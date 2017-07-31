structure BigOSolver = struct
open Equal
open ToStringRaw
open UVar
open Expr
open Subst
open Simp
open VC
open Normalize
       
infixr 0 $
infix 0 !!

infix 9 %@
infix 7 %*
infix 6 %+
infix 4 %<=
infix 4 %>=
infix 4 %=
infixr 3 /\
infixr 2 \/
infixr 1 -->
infix 1 <->

infix 4 ==

fun TimeFun n =
  if n <= 0 then Base Time
  else BSArrow (Base Nat, TimeFun (n-1))

fun TimeAbs (name, i, r) = IAbs (Base Nat, Bind (name, i), r)
                                
fun forget_i_vc x n (hs, p) = let
  fun f (h, (hs, x)) = 
    case h of 
        VarH _ => (h :: hs, x + 1) 
      | PropH p => (PropH (forget_i_p x 1 p) :: hs, x) handle ForgetError _ => (hs, x) (* just give up hypothesis if it involves [x] *)
  val (hs, x) = foldr f ([], 0) hs
in
  (hs, forget_i_p x 1 p)
end

fun match_bigO f hyps hyp =
  case hyp of
      PropH (BinPred (BigO, f', g)) =>
      if eq_i f' f then SOME g else NONE
    | _ => NONE
             
fun str_hyps_conclu gctx (hyps, p) =
  let 
    fun g (h, (hyps, ctx)) =
      case h of
          VarH ((name, _), (bs, _)) => (sprintf "$ : $" [name, str_bs bs] :: hyps, name :: ctx)
        | PropH p => (str_p gctx ctx p :: hyps, ctx)
    val (hyps, ctx) = foldr g ([], []) hyps
    val hyps = rev hyps
    val p = str_p gctx ctx p
  in
    hyps @
    ["==============="] @
    [p]
  end 

fun shiftx_hyp x n hyp =
  case hyp of
      VarH _ => hyp
    | PropH p => PropH (shiftx_i_p x n p)
                       
fun shiftx_hyps x n hyps =
  case hyps of
      [] => hyps
    | hyp :: hyps =>
      let
        val d = case hyp of
                    VarH _ => 1
                  | PropH _ => 0
      in
        shiftx_hyp x n hyp :: shiftx_hyps (x + d) n hyps
      end

(* find something about [x] in [hyps]. [x] is expressed as being in the innermost of [hyps] (so [x] can see all variables in [hyps]). *)
fun find_hyp forget shift pred x hyps =
  let
    exception Error
    fun runError m _ =
      SOME (m ())
      handle
      Error => NONE
      | ForgetError _ => NONE
    fun do_forget hyp x =
      case hyp of
          VarH _ => forget x
        | PropH _ => x
    fun do_shift hyp (p as (y, hyps)) =
      case hyp of
          VarH _ => (shift y, shiftx_hyps 0 1 hyps)
        | PropH _ => p
    fun loop x hyps () =
      let
        val (hyp, hyps) = case hyps of hyp :: hyps => (hyp, hyps) | [] => raise Error
        val x = do_forget hyp x
      in
        case pred x hyps hyp of
            SOME y => do_shift hyp (y, hyps)
          | NONE => do_shift hyp (loop x hyps ())
      end
  in
    runError (loop x hyps) ()
  end
    
fun find_bigO_hyp f_i hyps =
  find_hyp (forget_i_i 0 1) shift_i_i match_bigO f_i hyps
           
(* if [i] is [f m_1 ... m_k n] where [f m_1 ... m_i]'s bigO spec is known (i <= k), replace [f m1 ... m_i] with its bigO spec *)
fun use_bigO_hyp hs i =
  case is_IApp_UVarI i of
      SOME _ => i
    | NONE =>
      let
        val (f, args) = collect_IApp i
        fun iter (arg, f) =
          let
            val f = default f $ Option.map fst $ find_bigO_hyp f hs
            val f = simp_i (f %@ arg)
          in
            f
          end
        val f = foldl iter f args
      in
        f
      end

local
  open CollectVar
in
  fun contains i x = mem eq_var x $ collect_var_i_i i
end

local
  open CollectUVar
in
fun contains_uvar i x = mem eq_uvar_i x $ map #1 $ collect_uvar_i_i i
end

fun ask_smt_vc vc =
  not $ isSome $ SMTSolver.smt_solver_single "" false NONE vc
      
fun mult_class_entry ((c1, k1), (c2, k2)) = (c1 + c2, k1 + k2)
                                              
fun add_class_entry (a as (c1, k1), b as (c2, k2)) =
  if c1 = c2 then (c1, max k1 k2) else if c1 > c2 then a else b

val mult_class_entries = foldl' mult_class_entry (0, 0)
                                
val add_class_entries = foldl' add_class_entry (0, 0)

structure M = LongIdMap.LongIdBinaryMap
structure MU = MapUtilFn (M)
open MU
                
val mult_class = M.unionWith mult_class_entry
                             
val add_class = M.unionWith add_class_entry
                            
val mult_classes = foldl' mult_class M.empty
                          
val add_classes = foldl' add_class M.empty

fun trim_class cls = M.filter (fn (c, k) => not (c = 0 andalso k = 0)) cls
                              
fun str_cls cls = str_ls (fn (x, (c, k)) => sprintf "$=>($,$)" [str_raw_var x, str_int c, str_int k]) $ M.listItemsi $ cls
                         
(* summarize [i] in the form n_1^c_1 * (log n_1)^k_1 * ... * n_s^c_s * (log n_s)^k_s, and [n_1 => (c_1, k_1), ..., n_s => (c_s, k_s)] will be the [i]'s "asymptotic class". [n_1, ..., n_s] are the variable. *)
(* variables satisfy [is_outer] is considered constants from the outer environment *)
fun summarize (is_outer, on_error) i =
  let
    fun err i = on_error $ "summarize fails with " ^ str_i empty [] i
    fun loop i = 
      case i of
          IConst (ICTime _, _) =>
          M.empty
        | IConst (ICNat _, _) =>
          M.empty
        | VarI x =>
          if is_outer x then
            M.empty
          else
            M.insert (M.empty, x, (1, 0))
        | UnOpI (B2n, i, _) =>
          M.empty
        | UnOpI (ToReal, i, _) =>
          loop i
        | UnOpI (Ceil, i, _) =>
          loop i
        | UnOpI (Floor, i, _) =>
          loop i
        | UnOpI (IUDiv _, i, _) =>
          loop i
        | UnOpI (Log2, i, _) =>
          let
            (* val () = println "summarize/Log2" *)
            val is = collect_MultI i
            val classes = map loop is
            val cls = add_classes classes
            (* val () = println $ str_cls cls *)
            (* (0, 0) should never enter a class, so the following precaution shouldn't be necessary *)
            fun log_class (c, k) =
              (* approximate [log (log n)] by [log n] *)
              (0, if c = 0 andalso k = 0 then 0 else 1) 
            val cls = M.map log_class cls
            val cls = trim_class cls
                                 (* val () = println $ str_cls cls *)
          in
            cls
          end
        | BinOpI (MultI, a, b) =>
          mult_class (loop a, loop b)
        | BinOpI (AddI, a, b) =>
          add_class (loop a, loop b)
        | BinOpI (BoundedMinusI, a, b) =>
          loop a
        | BinOpI (MaxI, a, b) =>
          add_class (loop a, loop b)
        | _ => err i
  in
    loop i
  end

fun class_entry_le ((c, k), (c', k')) =
  if c < c' then
    true
  else if c = c' then k <= k'
  else false

fun class_le (m1, m2) =
  let
    fun f (k1, v1, still_ok) =
      if still_ok then
        let
          val v2 = default (0, 0) $ M.find (m2, k1)
        in
          class_entry_le (v1, v2)
        end
      else
        false
  in
    M.foldli f true m1
  end
    
fun timefun_le is_outer hs a b =
  let
    (* another version of [use_bigO_hyp] that substitute with all big-O premises *)
    fun match_bigO () hyps hyp =
      case hyp of
          PropH (BinPred (BigO, f', g)) =>
          SOME (f', g)
        | _ => NONE
    fun find_bigO_hyp f_i hyps =
      find_hyp id (fn (a, b) => (shift_i_i a, shift_i_i b)) match_bigO () hyps
    fun use_bigO_hyp hyps i =
      case find_bigO_hyp i hyps of
          SOME ((VarI (ID (f', _)), g), _) =>
          let
            val g = simp_i g
            val i' = simp_i $ ParaSubst.psubst_is_i [(ID (f', dummy))] [g] i
            val hs_ctx = hyps2ctx hs
                                  (* val () = println $ sprintf "timefun_le(): $ ~> $" [str_i [] ctx i, str_i [] ctx i'] *)
          in
            i'
          end
        | _ => i
    exception Error of string
    fun main () =
      let
        val a = normalize_i a
        val b = normalize_i b
        val (names1, _) = collect_IAbs a
        val (names2, _) = collect_IAbs b
        val arity = length names1
        val () = if arity = length names2 then () else raise Error "timefun_le: arity must equal"
        val a =
            (* if arity <= 2 then *)
              use_bigO_hyp hs a
            (* else *)
            (*   a *)
        val summarize = summarize (is_outer, fn s => raise Error s)
        val (_, i1) = collect_IAbs a
        val (_, i2) = collect_IAbs b
        val cls1 = summarize i1
        val cls2 = summarize i2
        (* val () = println $ sprintf "$ <=? $" [str_cls cls1, str_cls cls2] *)
      in
        class_le (cls1, cls2)
      end
  in
    main ()
    handle
    Error msg =>
    let
      (* val () = println $ sprintf "timefun_le failed because: $" [msg] *)
    in
      false
    end
  end

fun timefun_eq is_outer hs a b = timefun_le is_outer hs a b andalso timefun_le is_outer hs b a

fun is_VarI i =
  case i of
      VarI x => SOME x
    | _ => NONE

fun somes ls = List.mapPartial id ls

fun mapWithState f s ls = rev $ fst $ foldl (fn (x, (acc, s)) => let val (x, s) = f (x, s) in (x :: acc, s) end) ([], s) ls
                               
local
  (* for early return *)        
  exception Succeeded of idx
  exception Error of string
in
fun by_master_theorem uvar (hs, p) =
  let
    val (uvar_name, uvar_ctx, b) = get_uvar_info uvar !! (fn () => raise Error "not fresh uvar")
    (* val () = println $ sprintf "Running bigO inference for ?$" [str_int uvar_name] *)
    fun ask_smt p = ask_smt_vc (hs, p)
    fun V n = VarI (ID (n, dummy))
    fun to_real i = UnOpI (ToReal, i, dummy)
    val rV = to_real o V
    val use_bigO_hyp = use_bigO_hyp hs
    fun simp_i_max set i =
      let
        fun mark a = (set (); a)
        fun loop i =
          case i of
              BinOpI (opr, i1, i2) =>
              let
                fun def () = BinOpI (opr, loop i1, loop i2)
                fun remove_uvar i =
                  let
                    val is = collect_AddI $ simp_i i
                    val is = List.filter (isNone o is_IApp_UVarI) is
                  in
                    case is of
                        i :: is => combine_AddI_nonempty i is
                      | [] => i
                  end
              in
                case opr of
                    MaxI =>
                    if ask_smt (remove_uvar i1 %>= i2) then
                      mark i1
                    else if ask_smt (i1 %<= remove_uvar i2) then
                      mark i2
                    else def ()
                  | MultI =>
                    let
                      val i2s = collect_AddI i2
                      val () = if length i2s >= 2 then set () else ()
                    in
                      combine_AddI_Time (*i2s won't be empty*) $ map (fn i2 => i1 %* i2) i2s
                    end
                  | _ => def ()
              end
            | UnOpI (opr, i, r) => UnOpI (opr, loop i, r)
            | IConst _ => i
            | Ite (i1, i2, i3, r) => Ite (loop i1, loop i2, loop i3, r)
            | IAbs _ => i
            | VarI _ => i
            | UVarI _ => i
      in
        loop i
      end
    fun simp_p_max set p =
      let
        fun loop p =
          case p of
              BinPred (opr, i1, i2) => BinPred (opr, simp_i_max set i1, simp_i_max set i2)
            | BinConn (opr, p1, p2) => BinConn (opr, loop p1, loop p2)
            | Not (p, r) => Not (loop p, r)
            | PTrueFalse _ => p
            | Quan _ => p
      in
        loop p
      end
    val hs_ctx = hyps2ctx hs
    val p = normalize_p p
    (* val () = println $ "before simp_p_max: " ^ str_p [] hs_ctx p *)
    val p = simp_p_with_plugin simp_p_max p
    (* val () = println $ "after simp_p_max: " ^ str_p [] hs_ctx p *)
    (* [main_arg] is the main argument; [args] are the passive arguments *)
    val (lhs, main_fun, main_arg) =
        case p of
            BinPred (LeP, i1, BinOpI (IApp, g, n_i)) => (i1, g, n_i)
          | _ => raise Error "wrong pattern for by_master_theorem"
    val ((uvar', _), args) = is_IApp_UVarI main_fun !! (fn () => raise Error "RHS not [uvar arg1 ...]")
    val () = if uvar = uvar' then () else raise Error "uvar <> uvar'"
    val b = update_bs b
    val arity = is_time_fun b !! (fn () => raise Error $ sprintf "bsort $ not time fun" [str_raw_bs b])
    fun time_fun_var_name n =
      "__x" ^ str_int n
      (* if n = 0 then "n" *)
      (* else if n = 1 then "m" *)
      (* else *)
      (*   "m" ^ str_int n *)
    val ext_ctx = Range.map (fn n => (time_fun_var_name n, Base Nat)) $ Range.zero_to arity
    val uvar_ctx = ext_ctx @ uvar_ctx
    (* val () = println "  to solve this: " *)
    (* val () = app println $ str_vc false "" (hs, p) *)
    val () = if length args + 1 = length uvar_ctx then () else raise Error "length args + 1 <> length uvar_ctx"
    val args_v = map is_VarI args
    fun filter_arg_v ((v, b), vset) =
      case v of
          SOME x =>
          if not (eq_bs (update_bs b) (Base Nat)) orelse contains main_arg x orelse mem eq_var x vset then
            (NONE, vset)
          else
            (v, x :: vset)
        | NONE =>
          (NONE, vset)
    val args_bsorts = take (length args) $ rev $ map snd uvar_ctx
    (* later arguments have priority *)
    val args_v = rev $ mapWithState filter_arg_v [] $ rev $ zip (args_v, args_bsorts)
    val n_ = to_real main_arg
    val is = collect_AddI lhs
    fun get_class m k = default (0, 0) $ M.find (m, k)
    fun get_class_or_0 m k = default (0, 0) $ Option.map (get_class m) k
    fun exp n i = combine_MultI (repeat n i)
    fun class2term (c, k) n =
      exp c n %* exp k (UnOpI (Log2, n, dummy))
    (* is a variable appears as an argument to [uvar] but not among the last [arity] arguments, then it is seen as an "outer" parameter  *)
    fun is_outer x =
      case findi (eq_i (VarI x)) (main_arg :: rev args) of
          SOME (n, _) => n >= arity andalso not (contains main_arg x)
        | NONE => false
    val summarize = summarize (is_outer, fn s => raise Error s)
    (* we check that all variables on the LHS that are not covered by the passive arguments on the RHS will be <= the main argument so can be soundly treated as the main argument *)
    fun get_main_arg_class classes =
      let
        val uncovered = diff eq_var (domain classes) $ somes args_v
        val () = app (fn x => if ask_smt (VarI x %<= main_arg) then () else raise Error $ sprintf "not_covered > main_arg, not_covered=$, main_arg=$, is_outer(not_covered)=$" [str_i empty hs_ctx (VarI x), str_i empty hs_ctx main_arg, str_bool (is_outer x)]) uncovered
        val main_arg_class = mult_class_entries $ map (get_class classes) uncovered
      in
        main_arg_class
      end
    val () = println "Start to try different cases"
    val () =
        let
          val () = println "Trying [a * T (n/b) + f n <= T n] case ..."
          fun master_theorem n (a, b) (c, k) =
            let
              val int_add = op+
              open Real
              val log_b_a = Math.ln (fromInt a) / Math.ln (fromInt b)
              val T =
                  if fromInt c < log_b_a then
                    ExpI (n, (toString log_b_a, dummy))
                  else if fromInt c == log_b_a then
                    class2term (c, int_add (k, 1)) n
                  else if fromInt c > log_b_a then
                    class2term (c, k) n
                  else raise Error "can't compare c and (log_b a)"
            in
              T
            end
          fun get_params is_sub_problem is =
            let
              (* find terms of the form [T m (ceil (n/b))] (or respectively for [floor]) *)
              val (bs, others) = partitionOption is_sub_problem is
              val a = length bs
              val b = if null bs then raise Error "bs is null" else hd bs
              val () = if List.all (curry op= (b : int)) (tl bs) then () else raise Error "all bs eq"
            in
              (a, b, others)
            end
          fun infer_b n_ n' =
            let
              fun infer_b_i i =
                case i of
                    UnOpI (opr, i, _) =>
                    (case opr of
                         IUDiv b => [b]
                       | IUExp _ => []
                       | _ => infer_b_i i
                    )
                  | _ => []
              fun infer_b_p p =
                case p of
                    BinPred (EqP, i1, i2) => infer_b_i i1 @ infer_b_i i2
                  | _ => []
              fun infer_b_hyp h =
                case h of
                    PropH p => infer_b_p p
                  | VarH _ => []
              val bs = infer_b_i n' @ concatMap infer_b_hyp hs
              fun good_b b =
                ((* println (str_int b); *)
                if ask_smt (n' %<= UnOpI (Ceil, DivI (n_, (b, dummy)), dummy)) then
                  SOME b
                else NONE)
            in
              firstSuccess good_b bs
            end
          fun is_sub_problem i =
            ((* println (str_raw_i i); *)
            case i of
                BinOpI (IApp, g, n') =>
                if eq_i g main_fun then
                  ((* println (str_i [] hs_ctx n');  *)infer_b n_ n')
                else NONE
              | _ => NONE
            )
          val (a, b, others) = get_params is_sub_problem is
          val () = if b > 1 then () else raise Error "b > 1"
          val others = map use_bigO_hyp others
          val classes_of_terms = map summarize others
          val main_arg_classes = map get_main_arg_class classes_of_terms
          val classes = add_classes classes_of_terms
          val main_arg_class = add_class_entries main_arg_classes
          val classes = map (get_class_or_0 classes) args_v
          val i = master_theorem (rV 0) (a, b) main_arg_class
          val i = foldli (fn (n, cls, i) => class2term cls (rV (n + 1)) %* i) i $ rev classes
          val i = simp_i i
          val i = IAbs_Many (rev uvar_ctx, i, dummy)
        in
          raise Succeeded i
        end
        handle
        Error msg =>
        let
          (* val () = println $ sprintf "Case failed because: $" [msg] *)
        in
          ()
        end
    val () =
        let
          val () = println "Trying [T n + f n <= T (n + 1)] case ..."
          (* val () = println $ sprintf "main_fun=$   g=$" [str_int main_fun, str_int g] *)
          fun par i =
            case i of
                BinOpI (IApp, g, n') =>
                let
                  (* val () = println $ sprintf "main_fun=$   g=$  g'=$" [str_int main_fun, str_int g, str_int g'] *)

                in
                  if eq_i g main_fun then
                    SOME n'
                  else NONE
                end
              | _ => NONE
          val (n's, others) = partitionOption par is
          val () = if null n's then raise Error "n's is null" else ()
          (* val () = println $ sprintf "length n's = $" [str_int $ length n's] *)
          val n' = combine_AddI_Nat n's
          val N1 = ConstIN (1, dummy)
          val () = if ask_smt (n' %+ N1 %<= main_arg) then () else raise Error $ sprintf "n' + 1 > n_i, n'=$, main_arg=$" [str_i empty hs_ctx n', str_i empty hs_ctx main_arg]
          val others = concatMap (collect_AddI o simp_i_with_plugin simp_i_max) $ map use_bigO_hyp others
          val classes_of_terms = map summarize others
          (* val () = app (fn (i, cls) => (println (str_i empty hs_ctx i); println (str_cls cls))) $ zip (others, classes_of_terms) *)
          val main_arg_classes = map get_main_arg_class classes_of_terms
          (* val () = println "" *)
          (* val () = app (println o str_pair (str_int, str_int)) main_arg_classes *)
          val classes = add_classes classes_of_terms
          val (c, k) = add_class_entries main_arg_classes
          val classes = map (get_class_or_0 classes) args_v
          val i = class2term (c + 1, k) (rV 0)
          val i = foldli (fn (n, cls, i) => class2term cls (rV (n + 1)) %* i) i $ rev classes
          val i = simp_i i
          val i = IAbs_Many (rev uvar_ctx, i, dummy)
        in
          raise Succeeded i
        end
        handle Error msg =>
        let
          (* val () = println $ sprintf "Case failed because: $" [msg] *)
        in
          ()
        end
    val () =
        let
          val () = println "Trying [f n <= T n] case ..."
          val () = if not $ contains_uvar lhs uvar then () else raise Error "[lhs] contains [uvar]"
          val is = concatMap collect_AddI $ map use_bigO_hyp is
          val classes_of_terms = map summarize is
          val main_arg_classes = map get_main_arg_class classes_of_terms
          val classes = add_classes classes_of_terms
          val main_arg_classes = map get_main_arg_class classes_of_terms
          val main_arg_class = add_class_entries main_arg_classes
          val classes = map (get_class_or_0 classes) args_v
          val i = class2term main_arg_class (rV 0)
          val i = foldli (fn (n, cls, i) => class2term cls (rV (n + 1)) %* i) i $ rev classes
          val i = simp_i i
          val i = IAbs_Many (rev uvar_ctx, i, dummy)
        in
          raise Succeeded i
        end
        handle Error msg =>
        let
          (* val () = println $ sprintf "Case failed because: $" [msg] *)
        in
          ()
        end
    (* val () = println "Big-O inference failed because none of the cases applies" *)
  in
    NONE    
  end
  handle Succeeded i =>
         let
           val (uvar_name, _, _) = get_uvar_info uvar !! (fn () => raise Impossible "not fresh uvar")
           val () = println $ sprintf "Inferred this big-O class for ?$: $\n" [str_int uvar_name, str_i empty [] i]
         in
           SOME i
         end
       | Error msg =>
         let
           (* val () = println $ sprintf "Big-O inference failed because: $" [msg] *)
         in
           NONE
         end
end
    
fun go_through f ls =
  case ls of
      [] => []
    | x :: xs =>
      let
        val (output, remain) = f (x, xs)
        val remain = map normalize_vc remain
        val output2 = go_through f remain
      in
        output @ output2
      end

fun inside_arity arity id =
  case id of
      ID (x, _) => x < arity
    | QID _ => false
fun outside_arity arity id =
  not $ inside_arity arity id
                                                            
exception MasterTheoremCheckFail of region * string list

local
exception Succeeded of vc list * vc list
in
fun solve_exists (vc as (hs, p), vcs) =
  let
    (* val () = println "solve_exists()" *)
    (* val () = println "solve_exists() to solve this: " *)
    (* val () = app println $ str_vc false "" vc *)
    val hs_ctx = hyps2ctx hs
    val p = normalize_p p
    exception Error of string
    val () =
        let
          val () = println "Trying case [_ <== spec] ..."
          val (f, spec) =
              case p of
                  BinPred (BigO, f, spec) =>
                  (f, spec)
                | _ => raise Error "wrong pattern"
          val ((uvar, _), args) = is_IApp_UVarI f !! (fn () => raise Error "not [uvar arg1 ...]")
          val (_, uvar_ctx, b) = get_uvar_info uvar !! (fn () => raise Error "not fresh uvar")
          val b = update_bs b
          val arity = is_time_fun b !! (fn () => raise Error $ sprintf "bsort $ not time fun" [str_raw_bs b])
          val () = if arity >= 1 then () else raise Error "not (arity >= 1)"
          val () = if length args = length uvar_ctx then () else raise Error "length args <> length uvar_ctx"
                                  
          (* val () = if null args then () else raise Error "args not null" *)
          (* val () = if null ctx then () else raise Error "ctx not null" *)
                                                
          val () = println "Infer and check ..."
          fun on_fail_all () =
            let
              val () = println "by_master_theorem() failed on all remaining VCs. We accept this VC assuming that all big-O classes are inhabitted. But if there is a VC later constraining [f], it won't be proved."
            in                                                                                                     Succeeded ([], vcs)
            end
          val (many_inferred, vcs) = partitionOption (by_master_theorem uvar) vcs
          val (inferred, many_infered) =
              case many_inferred of
                  x :: xs => (x, xs)
                | [] => raise on_fail_all ()
          (* val () = println $ "arity=" ^ str_int arity *)
          fun is_outer x = outside_arity arity x
          fun combine_fun (a, b) =
            let
              (* val (ctx1, _) = collect_IAbs a *)
              (* val (ctx2, _) = collect_IAbs b *)
              (* val () = if length ctx1 = length ctx2 then () else raise Error "combine_fun(): arities don't match" *)
              (* val () = if length ctx1 = arity then () else raise Error "combine_fun(): wrong arity" *)
              val ret = if timefun_le is_outer hs a b then b
                        else if timefun_le is_outer hs b a then a
                        else raise Error(* Impossible *) $ sprintf "combine_fun(): neither a <= b nor b <= a\n  a=$\n  b=$" [str_i empty hs_ctx a, str_i empty hs_ctx b]
            in
              ret
            end
          val inferred = foldl combine_fun inferred many_inferred
          val inferred = IApps inferred args
          val inferred = normalize_i inferred
          val () = println $ sprintf "Inferred. Now check inferred complexity $ against specified complexity $" [str_i empty hs_ctx inferred, str_i empty hs_ctx spec]
          val () = 
              if timefun_le is_outer hs inferred spec then ()
              else Unify.unify_IApp dummy spec inferred
                   handle
                   Unify.UnifyAppUVarFailed _ => 
                   raise curry MasterTheoremCheckFail (get_region_i spec) $ [sprintf "Can't prove that the inferred big-O class $ is bounded by the given big-O class $" [str_i empty hs_ctx inferred, str_i empty hs_ctx spec]]
          val () = println "Complexity check OK!"
        in
          raise Succeeded ([], vcs)
        end
        handle Error msg =>
        let
          (* val () = println $ sprintf "Case failed because: $" [msg] *)
        in
          ()
        end
    fun unify (uvar_side, value_side) =
      let
        val () = println $ sprintf "try to unify $ with $" [str_i empty hs_ctx uvar_side, str_i empty hs_ctx value_side]
        val ((x, _), args) = is_IApp_UVarI uvar_side !! (fn () => raise Error "not [uvar arg1 ...]")
        val (name, _, _) = get_uvar_info x !! (fn () => raise Error "uvar not fresh")
        val value_side = normalize_i value_side
        val () = if mem op= x (map #1 $ CollectUVar.collect_uvar_i_i value_side) then raise Error "uvar appears in value_side" else ()

                           
        val args = map normalize_i args
        open CollectVar
        val vars = dedup eq_var $ collect_var_i_i value_side
        val uncovered = List.filter (fn var => not (List.exists (fn arg => eq_i (VarI var) arg) args)) vars
        fun forget_nonconsuming (var : var) b =
          let
            val x = case var of
                         ID (x, _) => x
                       | QID _ =>
                         raise Error "can't forget decorated variable"
            open UVarForget
            val () = println $ sprintf "forgeting $ in $" [str_i empty hs_ctx (VarI var), str_i empty hs_ctx b]
            val b = forget_i_i x 1 b
            val b = shiftx_i_i x 1 b
          in
            b
          end
        val value_side = foldl (fn (x, acc) => forget_nonconsuming x acc) value_side uncovered
                  handle ForgetError _ => raise Error "forgetting failed"
        val value_side = normalize_i value_side
        val uvar_side = normalize_i uvar_side

                              
        val () = println $ sprintf "Forgetting succeeded. Now try to unify $ with $" [str_i empty hs_ctx uvar_side, str_i empty hs_ctx value_side]
        val () =  Unify.unify_IApp dummy uvar_side value_side
                  handle
                  Unify.UnifyAppUVarFailed _ => raise Error "unify_IApp() failed"
        val () = println $ sprintf "?$ is instantiated to $" [str_int name, str_i empty [] (UVarI (x, dummy))]
      in
        ()
      end
    val () =
        let
          val () = println "Try case [_ <= uvar arg1 ...] (just to infer a Time)"
          val (lhs, rhs) =
              case p of
                  BinPred (Le, lhs, rhs) => (lhs, rhs)
                | _ => raise Error "wrong pattern"
          val () = unify (rhs, lhs)
        in
          raise Succeeded ([], vcs)
        end
        handle Error msg =>
        let
          (* val () = println $ sprintf "Case failed because: $" [msg] *)
        in
          ()
        end
(*                          
    val () =
        let
          fun infer_exists hs (name_arity1 as (name1, arity1)) p =
            let
              (* val () = println "infer_exists() to solve this: " *)
              (* val () = app println $ (str_vc false "" (VarH (name1, TimeFun arity1) :: hs, p) @ [""]) *)
            in
              if arity1 = 0 then
                (* just to infer a Time *)
                (case p of
                     BinPred (Le, i1 as (ConstIT _), VarI (_, (x, _))) =>
                     if x = 0 then SOME (i1, []) else NONE
                   | _ => NONE
                )
              else
                case p of
                  | BinPred (BigO, VarI (_, (x, _)), f) =>
                    if x = 0 then
                      let
                        val () = println "No other constraint on function"
                      in
                        SOME (f, [])
                      end
                    else NONE
                  | _ => NONE
            end
          val (i, ret) = infer_exists hs (name, arity) p !! fn () => Error
          val () = println "Inferred by infer_exists():"
          val () = println $ sprintf "$ = $" [name, str_i empty [] i]
          val () = case ins of
                       SOME ins => ins i
                     | NONE => ()
        in
          raise Succeeded (ret, vcs)
        end
        handle Error => ()
    val () = 
        let
          (* ToDo: a bit unsound inference strategy: infer [i] from [p1] and substitute for [i] in [p2] (assuming that [p2] doesn't contribute to inferring [i]) *)
          val (p1, p2) = split_and p
          val () = println "This inference may be unsound. "
                           (* val () = println $ sprintf "It assumes this proposition doesn't contribute to inference of $:" [name] *)
                           (* val () = app println $ (str_vc false "" (VarH (name, TimeFun arity) :: hs, p2) @ [""]) *)
                           (* val () = println "and it only uses this proposition to do the inference:" *)
                           (* val () = app println $ (str_vc false "" (VarH (name, TimeFun arity) :: hs, p1) @ [""]) *)
                           (* val () = println "solve_exists() to solve this: " *)
                           (* val () = app println $ (str_vc false "" vc @ [""]) *)
          val (i, vcs1) = infer_exists hs (name, arity) p1 !! fn () => Error
          val () = println "Inferred by infer_exists():"
          val () = println $ sprintf "$ = $" [name, str_i empty [] i]
          val () = case ins of
                       SOME ins => ins i
                     | NONE => ()
          val p2 = subst_i_p i p2
          val vcs = prop2vcs p2
          val vcs = append_hyps hs vcs
          val vcs = concatMap solve_exists vcs
          val vcs = vcs1 @ vcs
        in
          raise Succeeded vcs
        end
        handle Error => ()
  *)
  in
    ([vc], vcs)
  end
  handle Succeeded a => a
end

fun solve_bigO_compare (vc as (hs, p)) =
  case normalize_p p of
      BinPred (BigO, i1, i2) =>
      let
        (* val () = println "BigO-compare-solver to solve this: " *)
        val () = app println $ str_vc false "" vc @ [""]
        fun get_arity i = length $ fst $ collect_IAbs i
        val arity = get_arity i2
        val result = timefun_le (outside_arity arity) hs i1 i2
        (* val () = println $ sprintf "bigO-compare result: $" [str_bool result] *)
      in
        if result then
          []
        else
          [vc]
      end
    | _ => [vc]

(* relying on monoticity of functions *)             
fun solve_fun_compare (vc as (hs, p)) =
  case p of
      BinPred (Le, i1, i2) =>
      let
        fun find_apps i =
          let
            val is = collect_AddI i
            fun par i =
              case i of
                  BinOpI (IApp, VarI (ID (f, _)), n) =>
                  SOME (f, n)
                | _ => NONE
            val (apps, rest) = partitionOption par is
            val rest = combine_AddI_Time rest
          in
            (apps, rest)
          end
        val (apps1, rest1) = find_apps i1
        val (apps2, rest2) = find_apps i2
      in
        case (apps1, apps2) of
            ([(f1, n1)], [(f2, n2)]) =>
            if f1 = f2 then
              [(hs, n1 %<= n2), (hs, rest1 %<= rest2)]
            else
              [vc]
          | _ => [vc]
      end
    | _ => [vc]

fun solve_vcs (vcs : vc list) : vc list =
  let 
    (* val () = println "solve_vcs()" *)

    
    (* open CollectUVar *)
    (* open FreshUVar *)
    (* val uvars = dedup (fn (a, b) => #1 a = #1 b) $ concatMap collect_uvar_i_vc vcs *)
    (* val () = assert (fn () => List.all is_fresh $ map #1 uvars) "all fresh" *)
    (* fun is_fun (x as (_, (_, _, b), _)) = *)
    (*   case update_bs b of *)
    (*       BSArrow _ => true *)
    (*     | _ => false *)
    (* val uvars = List.filter is_fun uvars *)
    (* val () = app uvar_i_ignore_args uvars *)
    (* val vcs = map normalize_vc vcs *)

                  
    val vcs = go_through solve_exists vcs
    val vcs = concatMap solve_bigO_compare vcs
    val vcs = concatMap solve_fun_compare vcs
  in
    vcs
  end

fun infer_numbers vcs0 =
  let
    open CollectUVar
    open FreshUVar
    val vcs = map fst vcs0
    val () = println "infer_numbers() to solver these problems:"
    val () = app println $ concatMap (fn vc => str_vc false "" vc @ [""]) vcs
    val uvars = dedup (fn (a, b) => #1 a = #1 b) $ concatMap collect_uvar_i_vc vcs
    (* val () = app uvar_i_ignore_args uvars *)
    (* val vcs = map normalize_vc vcs *)
    (* val uvars = dedup (fn (a, b) => #1 a = #1 b) $ concatMap collect_uvar_i_vc vcs *)
    fun is_number (x as (_, (_, _, b), _)) =
      case update_bs b of
          Base Nat => SOME (x, true)
        | Base Time => SOME (x, false)
        | _ => NONE
    val uvars = List.mapPartial is_number uvars
    (* val () = println $ str_int $ length uvars *)
    val maximum_number = 10
    fun enumerate_until max_sum len f =
      if len <= 0 then f []
      else
        let
          fun loop n =
            if n > max_sum then false
            else if enumerate_until (max_sum - n) (len - 1) (fn vals => f (n :: vals)) then true
            else loop (n + 1)
        in
          loop 0
        end
    fun try vals =
      let
        fun set_value (((x, (_, ctx, _), r), is_nat), value) =
          let
            fun to_real i = UnOpI (ToReal, i, r)
            val value = ConstIN (value, r)
            val value = if is_nat then value else to_real value
            val value = IAbs_Many (rev ctx, value, r)
          in
            x := Refined value
          end
        val () = app set_value $ zip (uvars, vals)
        val vcs = map normalize_vc vcs
        val vcs = List.mapPartial id $ SMTSolver.smt_solver "" false NONE vcs
        val ret = null vcs
        (* val () = println $ str_bool ret *)
      in
        ret
      end
    fun restore uvars = app (fn ((x, info, _), _) => x := Fresh info) uvars
    val succeeded = enumerate_until maximum_number (length uvars) try
    (* val succeeded = enumerate_until 5 3 (fn vals => (println (str_ls str_int vals); vals = [1,3,1])) *)
    (* val () = println $ str_bool succeeded *)
    val () = if succeeded then println $ "Numbers inferred:\n" ^ (join_lines $ map (fn ((x, (name, _, _), r), _) => sprintf "?$ := $" [str_int name, str_i empty [] (UVarI (x, r))]) uvars)
             else () 
    val ret = if succeeded then []
              else (restore uvars; vcs0)
  in
    ret
  end
end
