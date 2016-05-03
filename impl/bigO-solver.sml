structure BigOSolver = struct
open UVarUtil
open NoUVarExpr
open VC
open NoUVarSubst
       
infixr 0 $

infix 9 %@
infix 7 %*
infix 6 %+
infix 4 %<=
infix 4 %=
infix 3 /\
infix 1 -->
infix 1 <->

infix 4 ==

fun forget_i_vc x n (hs, p) = let
  fun f (h, (hs, x)) = 
      case h of 
          VarH _ => (h :: hs, x + 1) 
        | PropH p => (PropH (forget_i_p x 1 p) :: hs, x) handle ForgetError _ => (hs, x) (* just give up hypothesis if it involves [x] *)
  val (hs, x) = foldr f ([], 0) hs
in
  (hs, forget_i_p x 1 p)
end

fun vc2prop (hs, p) =
    foldl (fn (h, p) => case h of VarH (name, b) => Quan (Forall, Base b, (name, dummy), p) | PropH p1 => p1 --> p) p hs
          
fun match_bigO f hyps hyp =
    case hyp of
        PropH (BinPred (BigO, f', g)) =>
        if eq_i f' f then SOME g else NONE
      | _ => NONE
               
fun find_bigO_hyp f_i hyps =
    find_hyp (forget_i_i 0 1) shift_i_i match_bigO f_i hyps

fun contains big small = not $ isSome $ try_forget (forget_i_i small 1) big
                             
fun ask_smt_vc vc =
    (null $ List.mapPartial id $ SMTSolver.smt_solver "" [vc])
    handle SMTSolver.SMTError _ => false
         
fun mult_class_entry ((c1, k1), (c2, k2)) = (c1 + c2, k1 + k2)
                                        
fun add_class_entry (a as (c1, k1), b as (c2, k2)) =
    if c1 = c2 then (c1, max k1 k2) else if c1 > c2 then a else b

val mult_class_entries = foldl' mult_class_entry (0, 0)
                         
val add_class_entries = foldl' add_class_entry (0, 0)

structure M = IntBinaryMap
                                                                         
val mult_class = M.unionWith mult_class_entry
                                
val add_class = M.unionWith add_class_entry
                                
val mult_classes = foldl' mult_class M.empty
                         
val add_classes = foldl' add_class M.empty

fun trim_class cls = M.filter (fn (c, k) => not $ c = 0 andalso k = 0) cls
                              
(* summarize [i] in the form n_1^c_1 * (log n_1)^k_1 * ... * n_s^c_s * (log n_s)^k_s, and [n_1 => (c_1, k_1), ..., n_s => (c_s, k_s)] will be the [i]'s "asymptotic class". [n_1, ..., n_s] are the variable. *)
fun summarize on_error i =
    case i of
        ConstIT _ =>
        M.empty
      | ConstIN _ =>
        M.empty
      | VarI (x, _) =>
        M.insert (M.empty, x, (1, 0))
      | UnOpI (ToReal, i, _) =>
        summarize on_error i
      | UnOpI (Ceil, i, _) =>
        summarize on_error i
      | UnOpI (Floor, i, _) =>
        summarize on_error i
      | DivI (i, _) =>
        summarize on_error i
      | UnOpI (Log2, i, _) =>
        let
          val is = collect_MultI i
          val classes = map (summarize on_error) is
          val cls = add_classes classes
          (* (0, 0) should never enter a class, so the following precaution shouldn't be necessary *)
          fun log_class (c, k) =
              (* approximate [log (log n)] by [log n] *)
              (0, if c = 0 andalso k = 0 then 0 else 1) 
          val cls = M.map log_class cls
          val cls = trim_class cls
        in
          cls
        end
      | BinOpI (MultI, a, b) =>
        mult_class (summarize on_error a, summarize on_error b)
      | BinOpI (AddI, a, b) =>
        add_class (summarize on_error a, summarize on_error b)
      | _ => on_error $ "summarize fails with " ^ str_i [] i

fun extract_only_variable error cls =
    let
      val cls = M.listItemsi $ trim_class cls
      (* val () = println $ str_ls (fn (x, (c, k)) => sprintf "$=>($,$)" [str_int x, str_int c, str_int k]) $ cls *)
      val x = if length cls <> 1 orelse snd (hd cls) <> (1, 0) then raise error
              else fst (hd cls)
    in
      x
    end
      
(* a version of [summarize] where n = O(x) is linear with the only variable x. *)
fun summarize_1 error n i =
  let
    fun on_error s = raise error s
    val cls_n = summarize on_error n
    val x = extract_only_variable (error "summarize_1: class of n must be (1, 0) for only one variable") cls_n
    val cls_i = M.listItemsi $ trim_class $ summarize on_error i
    val ret = if length cls_i = 0 then
                (0, 0)
              else if length cls_i = 1 andalso fst (hd cls_i) = x then
                snd (hd cls_i)
              else
                on_error "summarize_1: class of i must only contain n's variable"
  in
    ret
  end
    
(* a version of [summarize] where n = O(x) and m = O(y), x <> y, and i = y * f(x) or f(x) *)
fun summarize_2 error m n i =
    let
      fun on_error s = raise error s
      val cls_n = summarize on_error n
      val x = extract_only_variable (error $ "summarize_2: class of n must be (1, 0) for only one variable " ^ str_i [] n) cls_n
      val cls_m = summarize on_error m
      val y = extract_only_variable (error "summarize_2: class of n must be (1, 0) for only one variable") cls_m
      val () = if x = y then on_error "summarize_2: x = y" else ()
      val cls_i = M.listItemsi $ trim_class $ summarize on_error i
      fun err () = on_error $ "summarize_2: i should be y*f(x) or f(x) " ^ str_i [] i
      val ret = if length cls_i = 0 then
                  (0, 0)
                else if length cls_i = 1 then
                 if fst (hd cls_i) <> x then err ()
                 else snd (hd cls_i)
                else if length cls_i = 2 then
                  let
                    val ((v1, c1), (v2, c2)) =
                        case cls_i of
                            a :: b :: _ => (a, b)
                          | _ => raise Impossible "length cls_i = 2"
                    val (cx, cy) = if v1 = x andalso v2 = y then (c1, c2)
                                   else if v2 = x andalso v1 = y then (c2, c1)
                                   else err ()
                    val () = if cy = (1, 0) then () else err ()
                  in
                    cx
                  end
                else err ()
    in
      ret
    end
                           
fun by_master_theorem hs (name1, arity1) (name0, arity0) vcs =
    let
      val vcs' = append_hyps ([VarH (name0, TimeFun arity0), VarH (name1, TimeFun arity1)] @ hs) vcs
      (* val () = app println $ concatMap (fn vc => str_vc false "" vc @ [""]) vcs' *)
      (* val () = println "Master-Theorem-solver to apply SMT solver to discharge some VCs. " *)
      val (vcs, vcs') = unzip $ List.mapPartial (fn (vc, out) => case out of SOME (vc', _) => SOME (vc, vc') | NONE => NONE) $ zip (vcs, SMTSolver.smt_solver "" vcs')
      (* val () = println "Master-Theorem-solver to solve this: " *)
      (* val () = app println $ concatMap (fn vc => str_vc false "" vc @ [""]) vcs' *)
      exception Error of string
      fun runError m _ =
          let
            val ret as (f, _) = m ()
            val ctx = List.mapPartial (fn h => case h of VarH (name, _) => SOME name | _ => NONE) hs
            val () = println $ sprintf "Yes! I solved this: $" [str_i ctx f]
          in
            SOME ret
          end
          handle
          Error msg =>
          let
            val () = printf "Oh no! I can't solve this because: $\n" [msg]
          in
            NONE
          end
      fun main () =
          case vcs of
              [vc as (hs', p)] =>
              let
                (* number of variables in context *)
                val nx = length $ List.filter (fn h => case h of VarH _ => true | _ => false) hs'
                val vc' as (hyps, _) = hd vcs'
                fun ask_smt p = ask_smt_vc (hyps, p)
                val N1 = ConstIN (1, dummy)
                fun V n = VarI (n, dummy)
                fun to_real i = UnOpI (ToReal, i, dummy)
                fun exp n i = combine_MultI (repeat n i)
                fun class2term (c, k) n =
                    exp c n %* exp k (UnOpI (Log2, n, dummy))
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
                      val b = if null bs then raise Error "null bs" else hd bs
                      val () = if List.all (curry op= (b : int)) (tl bs) then () else raise Error "all bs eq"
                    in
                      (a, b, others)
                    end
              in
                case p of
                    BinPred (LeP, i1, BinOpI (TimeApp, BinOpI (TimeApp, VarI (g, _), VarI (m, _)), n_i)) =>
                    let
                      val () = if g = nx then () else raise Error "g = nx fails"
                      val () = if m < nx then () else raise Error "m < nx fails"
                      (* ToDo: check that [n_i] are well-scoped in [hs'] *)
                      (* ToDo: check that [m] doesn't appear in [n_i] *)
                      val m_i = V m
                      val m_ = to_real m_i
                      val n_ = to_real n_i
                    in
                      (* test the case: a * T m (n/b) + f m n <= T m n  *)
                      let
                        val is = collect_AddI i1
                        fun is_sub_problem i =
                            case i of
                                BinOpI (TimeApp, BinOpI (TimeApp, VarI (g', _), VarI (m', _)), UnOpI (opr, DivI (n', (b, _)), _)) =>
                                if g' = g andalso m' = m andalso (opr = Ceil orelse opr = Floor) andalso ask_smt (n' %= n_) then
                                  SOME b
                                else NONE
                              | _ => NONE
                        val (a, b, others) = get_params is_sub_problem is
                        (* if [i] is [f m n] where [f]'s bigO spec is known, replace [f] with its bigO spec *)
                        fun use_bigO_hyp i =
                            case i of
                                BinOpI (TimeApp, BinOpI (TimeApp, f_i as VarI (f, _), m'), n') =>
                                if f > nx andalso ask_smt (m' %= m_ /\ n' %= n_) then
                                  case find_bigO_hyp f_i hyps of
                                      SOME (g, _) => simp_i (g %@ m_ %@ n_)
                                    | NONE => i
                                else i
                              | _ => i
                        val others = map use_bigO_hyp others
                        val classes = map (summarize_2 Error m_ n_) others
                        val (c, k) = add_class_entries classes
                        val T = master_theorem (to_real (V 0)) (a, b) (c, k)
                        val T = TimeAbs (("m", dummy), TimeAbs (("n", dummy), simp_i (to_real (V 1) %* T), dummy), dummy)
                        val ret = (T, [])
                      in
                        ret
                      end
                      handle
                      Error msg =>
                      (* test the case: T m n + m + C <= T m (n + 1) *)
                      let
                        val () = printf "Failed the [T m (n/b)] case because: $\nTry [T m (n-1)] case ...\n" [msg]
                        val is = collect_AddI i1
                        fun par i =
                            case i of
                                BinOpI (TimeApp, BinOpI (TimeApp, VarI (g', _), VarI (m', _)), n') =>
                                if g' = g andalso m' = m then
                                  SOME n'
                                else NONE
                              | _ => NONE
                        val (n', rest) = case partitionOptionFirst par is of
                                             SOME a => a
                                           | NONE => raise Error "par() found nothing"
                        val () = if ask_smt (n' %+ N1 %= n_i) then () else raise Error "n' %+ N1 %= n_i"
                        fun only_const_or_m i =
                            case i of
                                ConstIT _ => ()
                              | UnOpI (ToReal, i, _) =>
                                (case i of
                                     ConstIN _ => ()
                                   | VarI (m', _) => if m' = m then () else raise Error "m' = m in only_const_or_m()"
                                   | _ => raise Error "to_real in only_const_or_m()"
                                )
                              | _ => raise Error "only_const_or_m fails"
                        val () = app only_const_or_m rest
                        val ret = (TimeAbs (("m", dummy), TimeAbs (("n", dummy), to_real (V 1) %* to_real (V 0), dummy), dummy), [])
                      in
                        ret
                      end
                    end
                  | BinPred (LeP, i1, BinOpI (TimeApp, VarI (g, _), n_i)) =>
                    if not $ contains i1 g then
                      let
                        val () = if g = nx then () else raise Error "g = nx fails"
                        val n_ = to_real n_i
                        fun use_bigO_hyp i =
                            case i of
                                BinOpI (TimeApp, f_i as VarI (f, _), n') =>
                                if f > nx andalso ask_smt (n' %= n_) then
                                  case find_bigO_hyp f_i hyps of
                                      SOME (f', _) => simp_i $ f' %@ n_
                                    | NONE => i
                                else i
                              | _ => i
                        val is = collect_AddI i1
                        val is = map use_bigO_hyp is
                        val classes = map (summarize_1 Error n_) is
                        val cls = add_class_entries classes
                        val T = TimeAbs (("n", dummy), simp_i $ class2term cls (to_real (V 0)), dummy)
                      in
                        (T, [])
                      end
                    else
                      let
                        val () = if g = nx then () else raise Error "g = nx fails"
                        (* ToDo: check that [n_i] are well-scoped in [hs'] *)
                        val n_ = to_real n_i
                      in
                        (* test the case: a * T (n/b) + f n <= T n  *)
                        let
                          val is = collect_AddI i1
                          fun is_sub_problem i =
                              case i of
                                  BinOpI (TimeApp, VarI (g', _), UnOpI (opr, DivI (n', (b, _)), _)) =>
                                  if g' = g andalso (opr = Ceil orelse opr = Floor) andalso ask_smt (n' %= n_) then
                                    SOME b
                                  else NONE
                                | _ => NONE
                          val (a, b, others) = get_params is_sub_problem is
                          (* if [i] is [f n] where [f]'s bigO spec is known, replace [f] with its bigO spec *)
                          fun use_bigO_hyp i =
                              case i of
                                  BinOpI (TimeApp, f_i as VarI (f, _), n') =>
                                  if f > nx andalso ask_smt (n' %= n_) then
                                    case find_bigO_hyp f_i hyps of
                                        SOME (g, _) => simp_i (g %@ n_)
                                      | NONE => i
                                  else i
                                | _ => i
                          val others = map use_bigO_hyp others
                          val classes = map (summarize_1 Error n_) others
                          val (c, k) = add_class_entries classes
                          val T = master_theorem (to_real (V 0)) (a, b) (c, k)
                          val T = TimeAbs (("n", dummy), simp_i T, dummy)
                          val ret = (T, [])
                        in
                          ret
                        end
                        handle
                        Error msg =>
                        (* test the case: T n + C <= T (n + 1) *)
                        let
                          val () = printf "Failed the [T (n/b)] case because: $\nTry [T (n-1)] case ...\n" [msg]
                          val is = collect_AddI i1
                          fun par i =
                              case i of
                                  BinOpI (TimeApp, VarI (g', _), n') =>
                                  if g' = g then
                                    SOME n'
                                  else NONE
                                | _ => NONE
                          val (n', rest) = case partitionOptionFirst par is of
                                               SOME a => a
                                             | NONE => raise Error "par() found nothing"
                          val () = if ask_smt (n' %+ N1 %= n_i) then () else raise Error "n' %+ N1 %= n_i"
                          fun only_const i =
                              case i of
                                  ConstIT _ => ()
                                | UnOpI (ToReal, ConstIN _, _) => ()
                                | _ => raise Error "only_const fails"
                          val () = app only_const rest
                          val ret = (TimeAbs (("n", dummy), to_real (V 0), dummy), [])
                        in
                          ret
                        end
                      end
                  | _ => raise Error "wrong pattern for by_master_theorem"
              end
            | _ => raise Error "by_master_theorem allows only 1 conjunct left"
    in
      runError main ()
    end

fun use_master_theorem hs name_arity1 (name0, arity0) p =
    (* opportunity to apply the Master Theorem to infer the bigO class *)
    let
      val () = println "use_master_theorem ()"
      (* hoist the conjuncts that don't involve the time functions *)
      val vcs = split_prop p
      val (rest, vcs) = partitionOption (Option.composePartial (try_forget (forget_i_vc 0 1), try_forget (forget_i_vc 0 1))) vcs
      val vcs = concatMap split_prop $ map (simp_p o vc2prop) vcs
      val ret = by_master_theorem hs name_arity1 (name0, arity0) vcs
    in
      case ret of
          SOME (i, vcs) => SOME (i, append_hyps hs rest @ vcs)
        | NONE => NONE
    end
    
fun split_and p =
    case p of
        BinConn (And, p1, p2) => (p1, p2)
      | _ => (p, True dummy)
               
fun infer_exists hs (name_arity1 as (_, arity1)) p =
    if arity1 = 0 then
      (* just to infer a Time *)
      (case p of
           BinPred (Le, i1 as (ConstIT _), VarI (x, _)) =>
           if x = 0 then SOME (i1, []) else NONE
         | _ => NONE
      )
    else
      case p of
          Quan (Exists _, Base (TimeFun arity0), (name0, _), BinConn (And, bigO as BinPred (BigO, VarI (n0, _), VarI (n1, _)), BinConn (Imply, bigO', p))) =>
          if n0 = 0 andalso n1 = 1 andalso eq_p bigO bigO' then
            use_master_theorem hs name_arity1 (name0, arity0) p
          else NONE
        | BinPred (BigO, VarI (x, _), f) =>
          if x = 0 then
            (* no other constraint *)
            SOME (f, [])
          else NONE
        | _ => NONE

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
      exception Error of string
      val summarize = summarize (fn s => raise Error s)
      fun main () =
          let
            val (names1, i1) = collect_TimeAbs a
            val (names2, i2) = collect_TimeAbs a
            val () = if length names1 = length names2 then () else raise Error "timefun_le: arity must equal"
          in
            class_le (summarize i1, summarize i2)
          end
    in
      main () handle Error _ => false
    end
      
fun hyps2ctx hs = List.mapPartial (fn h => case h of VarH (name, _) => SOME name | _ => NONE) hs

exception MasterTheoremCheckFail of region * string list
                                      
fun solve_exists (vc as (hs, p)) =
    case p of
        Quan (Exists ins, Base (TimeFun arity), (name, _), p) =>
        
        let
          val ret =
              case p of
                  BinConn (And, bigO as BinPred (BigO, VarI (n0, _), spec), BinConn (Imply, bigO', p)) =>
                  if n0 = 0 andalso eq_p bigO bigO' then
                    (* infer and then check *)
                    case use_master_theorem hs (name, arity) ("inferred", arity) (shiftx_i_p 1 1 p) of
                        SOME (inferred, vcs) =>
                        (let
                          val inferred = forget_i_i 1 1 inferred
                          val vcs = map (forget_i_vc 1 1) vcs
                          val inferred = forget_i_i 0 1 inferred
                          val spec = forget_i_i 0 1 spec
                        in
                          if timefun_le hs arity inferred spec then
                            SOME vcs
                          else
                            raise curry MasterTheoremCheckFail (get_region_i spec) $ [sprintf "Can't prove that the inferred big-O class $ is bounded by the given big-O class $" [str_i (hyps2ctx hs) inferred, str_i (hyps2ctx hs) spec]]
                        end handle ForgetError _ => NONE)
                      | NONE => NONE
                  else NONE
                | _ => NONE
        in
          case ret of
              SOME vcs => vcs
            | NONE =>
              
              let
                (* val () = println "hit1" *)
                (* val () = println "Exists-solver to solve this: " *)
                (* val () = app println $ (str_vc false "" vc @ [""]) *)
                val (p1, p2) = split_and p
              in
                case infer_exists hs (name, arity) p1 of
                    SOME (i, vcs1) =>
                    let
                      val () = case ins of
                                   SOME ins => ins i
                                 | NONE => ()
                      val p2 = subst_i_p i p2
                      val vcs = split_prop p2
                      val vcs = append_hyps hs vcs
                      val vcs = concatMap solve_exists vcs
                      val vcs = vcs1 @ vcs
                    in
                      vcs
                    end
                  | NONE => [vc]
              end

        end
      | _ => [vc]

fun solve_bigO_compare (vc as (hs, p)) =
    case p of
        BinPred (BigO, i1, i2) =>
        let
          (* val () = println "BigO-compare-solver to solve this: " *)
          (* val () = app println $ str_vc false "" vc @ [""] *)
          fun get_arity i = length $ fst $ collect_TimeAbs i
          val arity = get_arity i1
          val result = timefun_le hs arity i1 i2
          (* val () = println $ str_bool result *)
        in
          if result then
            []
          else
            [vc]
        end
      | _ => [vc]
    
fun solve_vcs (vcs : vc list) : vc list =
    let 
      (* val () = print "Applying Big-O solver ...\n" *)
      val vcs = concatMap solve_exists vcs
      val vcs = concatMap solve_bigO_compare vcs
    in
      vcs
    end

end
