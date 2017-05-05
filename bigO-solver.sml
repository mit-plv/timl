structure BigOSolver = struct
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
             
fun find_bigO_hyp f_i hyps =
  find_hyp (forget_i_i 0 1) shift_i_i match_bigO f_i hyps

(* if [i] is [f m_1 ... m_k n] where [f m_1 ... m_i]'s bigO spec is known (i <= k), replace [f m1 ... m_i] with its bigO spec *)
fun use_bigO_hyp long_hyps i =
  let
    val f :: args = collect_IApp i
    fun iter (arg, f) =
      let
        val f = default f $ Option.map fst $ find_bigO_hyp f long_hyps
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
  fun contains i x = mem eq_long_id x $ collect_var_i_i i
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

fun compare_option cmp (a, a') =
  case a of
      NONE =>
      (case a' of
           NONE => EQUAL
         | SOME _ => LESS
      )
    | SOME a =>
      (case a' of
           NONE => GREATER
         | SOME a' => cmp (a, a')
      )

fun compare_pair (cmp1, cmp2) ((a, b), (a', b')) =
  case cmp1 (a, a') of
      EQUAL => cmp2 (b, b')
    | ret => ret
      

fun compare_int (n, n') =
  if n < n' then LESS
  else if n = n' then EQUAL
  else GREATER
         
fun compare_id (x, x') = compare_int (fst x, fst x')
                                     
structure LongIdOrdKey = struct
type ord_key = long_id
fun compare (a : long_id * long_id) = compare_pair (compare_option compare_id, compare_id) a
end

structure LongIdBinaryMap = BinaryMapFn (LongIdOrdKey)

structure M = LongIdBinaryMap

fun get_domain m = map fst $ M.listItemsi m                
                
val mult_class = M.unionWith mult_class_entry
                             
val add_class = M.unionWith add_class_entry
                            
val mult_classes = foldl' mult_class M.empty
                          
val add_classes = foldl' add_class M.empty

fun trim_class cls = M.filter (fn (c, k) => not (c = 0 andalso k = 0)) cls
                              
(* fun str_cls cls = str_ls (fn (x, (c, k)) => sprintf "$=>($,$)" [str_int x, str_int c, str_int k]) $ M.listItemsi $ cls *)
                         
(* summarize [i] in the form n_1^c_1 * (log n_1)^k_1 * ... * n_s^c_s * (log n_s)^k_s, and [n_1 => (c_1, k_1), ..., n_s => (c_s, k_s)] will be the [i]'s "asymptotic class". [n_1, ..., n_s] are the variable. *)
fun summarize on_error i =
  let
    fun loop i = 
      case i of
          ConstIT _ =>
          M.empty
        | ConstIN _ =>
          M.empty
        | VarI x =>
          M.insert (M.empty, x, (1, 0))
        | UnOpI (B2n, i, _) =>
          M.empty
        | UnOpI (ToReal, i, _) =>
          loop i
        | UnOpI (Ceil, i, _) =>
          loop i
        | UnOpI (Floor, i, _) =>
          loop i
        | DivI (i, _) =>
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
        | _ => on_error $ "summarize fails with " ^ str_i [] [] i
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
    
fun timefun_le hs arity a b =
  let
    fun match_bigO () hyps hyp =
      case hyp of
          PropH (BinPred (BigO, f', g)) =>
          SOME (f', g)
        | _ => NONE
    fun find_bigO_hyp f_i hyps =
      find_hyp id (fn (a, b) => (shift_i_i a, shift_i_i b)) match_bigO () hyps
    fun use_bigO_hyp long_hyps i =
      case find_bigO_hyp i long_hyps of
          SOME ((VarI (_, (f', _)), g), _) =>
          let
            val g = simp_i g
            val i' = simp_i $ substx_i_i f' g i
                            (* val ctx = hyps2ctx hs *)
                            (* val () = println $ sprintf "timefun_le(): $ ~> $" [str_i [] ctx i, str_i [] ctx i'] *)
          in
            i'
          end
        | _ => i
    exception Error of string
    fun main () =
      let
        val a = if arity <= 2 then
                  use_bigO_hyp hs a
                else
                  a
        val (names1, i1) = collect_IAbs a
        val (names2, i2) = collect_IAbs b
        val () = if length names1 = length names2 then () else raise Error "timefun_le: arity must equal"
        val summarize = summarize (fn s => raise Error s)
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
      val () = println $ sprintf "timefun_le failed because: $" [msg]
    in
      false
    end
  end

fun timefun_eq hs arity a b = timefun_le hs arity a b andalso timefun_le hs arity b a

fun isPrefix eq xs ys =
  case (xs, ys) of
      ([], _) => true
    | (x :: xs, y :: ys) => eq (x, y) andalso isPrefix eq xs ys
    | _ => false

fun foldli f = foldlWithIdx (fn (x, acc, n) => f (n, x, acc))

fun is_VarI i =
  case i of
      VarI x => SOME x
    | _ => NONE

local
  (* for early return *)        
  exception Succeeded of idx
  exception Error of string
in
fun by_master_theorem (uvar, uvar_ctx, arity) (hs, p) =
  let
    val () = println "Running bigO inference"
    val () = println "  to solve this: "
    val () = app println $ str_vc false "" (hs, p)
    fun ask_smt p = ask_smt_vc (hs, p)
    fun V n = VarI (NONE, (n, dummy))
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
              in
                case opr of
                    MaxI =>
                    if ask_smt (i1 %>= i2) then
                      mark i1
                    else if ask_smt (i1 %<= i2) then
                      mark i2
                    else def ()
                  | _ => def ()
              end
            | UnOpI (opr, i, r) => UnOpI (opr, loop i, r)
            | DivI (i, b) => DivI (loop i, b)
            | ExpI (i, e) => ExpI (loop i, e)
            | Ite (i1, i2, i3, r) => Ite (loop i1, loop i2, loop i3, r)
            | IAbs _ => i
	    | TrueI _ => i
	    | FalseI _ => i
	    | TTI _ => i
            | ConstIN _ => i
            | ConstIT _ => i
            | VarI _ => i
            | AdmitI _ => i
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
            | True _ => p
            | False _ => p
            | Quan _ => p
      in
        loop p
      end
    val p = simp_p_with_plugin simp_p_max p
    val (lhs, g, main_arg) =
        case p of
            BinPred (LeP, i1, BinOpI (IApp, g, n_i)) => (i1, g, n_i)
          | _ => raise Error "wrong pattern for by_master_theorem"
    val (uvar', args') = is_IApp_UVarI g !! (fn () => Error "")
    val () = if uvar = uvar' then () else raise Error "uvar <> uvar'"
    val (main_fun, args) = (g, args')
    (* [main_arg] is the main argument; [args] are the passive arguments *)
    val args_v = map (fn i => is_VarI i !! (fn () => Error "")) args
    val () = app (fn x => if contains main_arg x then raise Error "" else ()) args_v
    val n_ = to_real main_arg
    fun decide_main_variable i =
      case i of
          VarI x => x
        | BinOpI (AddI, VarI x, ConstIN _) => x
        | BinOpI (AddI, ConstIN _, VarI x) => x
        | _ => raise Error ""
    val n = decide_main_variable main_arg
    val is = collect_AddI lhs
    fun get_class m k = default (0, 0) $ M.find (m, k)
    fun var_name n =
      if n = 0 then "n"
      else if n = 1 then "m"
      else "m" ^ str_int n
    val ext_ctx = Range.map (fn n => (var_name n, Base Nat)) $ Range.zero_to arity
    val uvar_ctx = ext_ctx @ uvar_ctx
    fun exp n i = combine_MultI (repeat n i)
    fun class2term (c, k) n =
      exp c n %* exp k (UnOpI (Log2, n, dummy))
    val summarize = summarize (fn s => raise Error s)
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
                    UnOpI (_, i, _) => infer_b_i i 
                  | DivI (_, (b, _)) => [b]
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
                if ask_smt (n' %<= UnOpI (Ceil, DivI (n_, (b, dummy)), dummy)) then
                  SOME b
                else NONE
            in
              firstSuccess good_b bs
            end
          fun is_sub_problem i =
            case i of
                BinOpI (IApp, g, n') =>
                if eq_i g main_fun then
                  infer_b n_ n'
                else NONE
              | _ => NONE
          val (a, b, others) = get_params is_sub_problem is
          val () = if b > 1 then () else raise Error "b > 1"
          val others = map use_bigO_hyp others
          val classes = map summarize others
          val classes = add_classes classes
          val () = if subset eq_long_id (get_domain classes) (n :: args_v) then () else raise Error ""
          val cls_n = get_class classes n
          val classes = map (get_class classes) args_v
          val i = master_theorem (rV 0) (a, b) cls_n
          val i = foldli (fn (n, cls, i) => class2term cls (rV (n + 1)) %* i) i $ rev classes
          val i = simp_i i
          val i = IAbsMany (uvar_ctx, i, dummy)
        in
          raise Succeeded i
        end
        handle
        Error msg => println $ sprintf "Case failed because: $" [msg]
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
          val () = if ask_smt (n' %+ N1 %<= main_arg) then () else raise Error "n' %+ N1 %<= n_i"
          val others = map use_bigO_hyp others
          val classes = map summarize others
          val classes = add_classes classes
          val () = if subset eq_long_id (get_domain classes) (n :: args_v) then () else raise Error ""
          val (c, k) = get_class classes n
          val classes = map (get_class classes) args_v
          val i = class2term (c + 1, k) (rV 0)
          val i = foldli (fn (n, cls, i) => class2term cls (rV (n + 1)) %* i) i $ rev classes
          val i = simp_i i
          val i = IAbsMany (uvar_ctx, i, dummy)
        in
          raise Succeeded i
        end
        handle Error msg => println $ sprintf "Case failed because: $" [msg]
    val () =
        let
          val () = println "Trying [f n <= T n] case ..."
          val () = if not $ contains_uvar lhs uvar then () else raise Error ""
          val is = map use_bigO_hyp is
          val classes = map summarize is
          val classes = add_classes classes
          val () = if subset eq_long_id (get_domain classes) (n :: args_v) then () else raise Error ""
          val cls_n = get_class classes n
          val classes = map (get_class classes) args_v
          val i = class2term cls_n (rV 0)
          val i = foldli (fn (n, cls, i) => class2term cls (rV (n + 1)) %* i) i $ rev classes
          val i = simp_i i
          val i = IAbsMany (uvar_ctx, i, dummy)
        in
          raise Succeeded i
        end
        handle Error msg => println $ sprintf "Case failed because: $" [msg]
    val () = println "Big-O inference failed because none of the cases applies"
  in
    NONE    
  end
  handle Succeeded i =>
         let
           val () = println $ sprintf "Inferred this big-O class: $\n" [str_i [] [] i]
         in
           SOME i
         end
       | Error msg =>
         let
           val () = println $ sprintf "Big-O inference failed because: $" [msg]
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
        val output2 = go_through f remain
      in
        output @ output2
      end

exception MasterTheoremCheckFail of region * string list

local
exception Succeeded of vc list * vc list
in
fun solve_exists (vc as (hs, p), vcs) =
  let
    (* val () = println "solve_exists()" *)
    val () = println "solve_exists() to solve this: "
    val () = app println $ str_vc false "" vc
    exception Error of string
    val () =
        let
          val () = println "Trying case [_ <== spec] ..."
          val (f, spec) =
              case normalize_p p of
                  BinPred (BigO, f, spec) =>
                  (f, spec)
                | _ => raise Error "wrong pattern"
          val (uvar, args) = is_IApp_UVarI f !! (fn () => Error "not [uvar arg1 ...]")
          val () = if null args then () else raise Error "args not null"
          val (_, ctx, b) = get_uvar_info uvar (fn () => raise Error "not fresh uvar")
          val arity = is_time_fun (update_bs b) !! (fn () => raise Error $ sprintf "bsort $ not time fun" [str_raw_bs b])
          val () = if arity >= 0 then () else raise Error "not (arity >= 0)"
          (* fun in_hyps p hs = *)
          (* val () = if in_hyps p hs2 then () else raise Error *)
          val () = println "Infer and check ..."
          val (inferred, vcs) = partitionOptionFirst (by_master_theorem (uvar, ctx, arity)) vcs  !! (fn () => Error "by_master_theorem() failed on all remaining VCs")
          val () = println $ sprintf "Inferred. Now check inferred complexity $ against specified complexity $" [str_i [] [] inferred, str_i [] [] spec]
          val () = 
              if timefun_le hs arity inferred spec then ()
              else raise curry MasterTheoremCheckFail (get_region_i spec) $ [sprintf "Can't prove that the inferred big-O class $ is bounded by the given big-O class $" [str_i [] (hyps2ctx hs) inferred, str_i [] (hyps2ctx hs) spec]]
          val () = println "Complexity check OK!"
        in
          raise Succeeded ([], vcs)
        end
        handle Error msg => println $ "Case failed because: " ^ msg
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
          val () = println $ sprintf "$ = $" [name, str_i [] [] i]
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
          val () = println $ sprintf "$ = $" [name, str_i [] [] i]
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
  case p of
      BinPred (BigO, i1, i2) =>
      let
        (* val () = println "BigO-compare-solver to solve this: " *)
        (* val () = app println $ str_vc false "" vc @ [""] *)
        fun get_arity i = length $ fst $ collect_IAbs i
        val arity = get_arity i2
        val result = timefun_le hs arity i1 i2
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
                  BinOpI (IApp, VarI (f, _), n) =>
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
    val () = println "solve_vcs()"
    open CollectUVar
    open FreshUVar
    val uvars = dedup (fn (a, b) => #1 a = #1 b) $ concatMap collect_uvar_i_vc vcs
    val () = assert (fn () => List.all is_fresh $ map #1 uvars) "all fresh"
    val () = app uvar_i_ignore_args uvars
    val vcs = map normalize_vc vcs
    val vcs = go_through solve_exists vcs
    val vcs = concatMap solve_bigO_compare vcs
    val vcs = concatMap solve_fun_compare vcs
  in
    vcs
  end

fun infer_numbers vcs0 =
  let
    val () = println "infer_numbers()"
    open CollectUVar
    open FreshUVar
    val vcs = map fst vcs0
    val uvars = dedup (fn (a, b) => #1 a = #1 b) $ concatMap collect_uvar_i_vc vcs
    val () = app uvar_i_ignore_args uvars
    val vcs = map normalize_vc vcs
    val uvars = dedup (fn (a, b) => #1 a = #1 b) $ concatMap collect_uvar_i_vc vcs
    fun is_number (x as (_, (_, ctx, b), _)) =
      case (ctx, update_bs b) of
          ([], Base Nat) => SOME (x, true)
        | ([], Base Time) => SOME (x, false)
        | _ => NONE
    val uvars = List.mapPartial is_number uvars
    val () = println $ str_int $ length uvars
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
        fun set_value (((x, _, r), is_nat), value) =
          let
            fun to_real i = UnOpI (ToReal, i, r)
            val value = ConstIN (value, r)
            val value = if is_nat then value else to_real value
          in
            x := Refined value
          end
        val () = app set_value $ zip (uvars, vals)
        val vcs = map normalize_vc vcs
        val vcs = List.mapPartial id $ SMTSolver.smt_solver "" false NONE vcs
        val ret = null vcs
        (* val () = println $ str_bool ret                *)
      in
        ret
      end
    fun restore uvars = app (fn ((x, info, _), _) => x := Fresh info) uvars
    val succeeded = enumerate_until maximum_number (length uvars) try
    (* val succeeded = enumerate_until 5 3 (fn vals => (println (str_ls str_int vals); vals = [1,3,1])) *)
    val () = println $ str_bool succeeded
    val () = if succeeded then println $ "Number inferred: " ^ (join_lines $ map (fn ((x, (name, _, _), r), _) => sprintf "?$ := $" [str_int name, str_i [] [] (UVarI (x, r))]) uvars)
             else () 
    val ret = if succeeded then []
              else (restore uvars; vcs0)
  in
    ret
  end
end
