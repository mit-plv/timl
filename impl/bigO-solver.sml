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
         
fun combine_class ((c1, k1), (c2, k2)) = (c1 + c2, k1 + k2)
                                        
fun join_class (a as (c1, k1), b as (c2, k2)) =
    if c1 = c2 then (c1, max k1 k2) else if c1 > c2 then a else b

(* summarize [i] in the form n^c*(log n)^k, and (c, k) will be the [i]'s "asymptotic class". [n] is the only variable. *)
fun summarize_1 (args as (ask_smt, on_error, n)) i =
    case i of
        ConstIT _ =>
        (0, 0)
      | UnOpI (ToReal, ConstIN _, _) =>
        (0, 0)
      | DivI (i, _) =>
        summarize_1 args i
      | UnOpI (Log2, i, _) =>
        let
          val (c, k) = summarize_1 args i
        in
          if k = 0 then
            (0, c)
          else
            (0, c + 1) (* approximate [log (log^k n)] by [log n] *)
        end
      | BinOpI (MultI, a, b) =>
        combine_class (summarize_1 args a, summarize_1 args b)
      | BinOpI (AddI, a, b) =>
        join_class (summarize_1 args a, summarize_1 args b)
      | _ =>
        if ask_smt (i %<= n) then
          (1, 0)
        else
          on_error "summarize_1 fails"
                           
(* summarize_2 into asym class, where [n_] and [m_] are variables *)
fun summarize_2 (ask_smt, on_error, m_, n_) i =
    let
      (* test for [ ... * m * ... ] *)
      val is = collect_MultI i
    in
      case partitionOptionFirst (fn i => b2o $ ask_smt (i %= m_)) is of
          SOME (_, rest) => (1, summarize_1 (ask_smt, on_error, n_) (combine_MultI rest))
        | NONE => (0, summarize_1 (ask_smt, on_error, n_) i)
    end
                             
fun by_master_theorem hs (name1, arity1) (name0, arity0) vcs =
    let
      val vcs' = append_hyps ([VarH (name0, TimeFun arity0), VarH (name1, TimeFun arity1)] @ hs) vcs
      (* val () = app println $ concatMap (fn vc => str_vc false "" vc @ [""]) vcs' *)
      (* val () = println "Master-Theorem-solver to apply SMT solver to discharge some VCs. " *)
      val (vcs, vcs') = unzip $ List.mapPartial (fn (vc, out) => case out of SOME (vc', _) => SOME (vc, vc') | NONE => NONE) $ zip (vcs, SMTSolver.smt_solver "" vcs')
      val () = println "Master-Theorem-solver to solve this: "
      val () = app println $ concatMap (fn vc => str_vc false "" vc @ [""]) vcs'
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
                fun join_classes classes = foldl' join_class ((0, 0)) classes
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
                        val classes = map (snd o summarize_2 (ask_smt, fn s => raise Error s, m_, n_)) others
                        val (c, k) = join_classes classes
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
                        val classes = map (summarize_1 (ask_smt, fn s => raise Error s, n_)) is
                        val cls = join_classes classes
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
                          val classes = map (summarize_1 (ask_smt, fn s => raise Error s, n_)) others
                          val (c, k) = join_classes classes
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

fun class_le ((c, k), (c', k')) =
    if c < c' then
      true
    else if c = c' then k <= k'
    else false
           
fun timefun_le hs arity a b =
    let
      exception Error of string
      fun V n = VarI (n, dummy)
      fun to_real i = UnOpI (ToReal, i, dummy)
      fun ask_smt hs' p = ask_smt_vc (map (fn name => VarH (name, Nat)) hs' @ hs, p)
      val summarize_1 = summarize_1 (ask_smt ["n"], fn s => raise Error s, to_real (V 0))
      val summarize_2 = summarize_2 (ask_smt ["n", "m"], fn s => raise Error s, to_real (V 1), to_real (V 0))
      fun ret () =
          case (arity, a, b) of
              (1, TimeAbs (_, a, _), TimeAbs (_, b, _)) =>
              class_le (summarize_1 a, summarize_1 b)
            | (2, TimeAbs (_, TimeAbs (_, a, _), _), TimeAbs (_, TimeAbs (_, b, _), _)) =>
              let
                val (m1, cls1) = summarize_2 a
                val (m2, cls2) = summarize_2 b
              in
                m1 <= m2 andalso class_le (cls1, cls2)
              end
            | _ => false 
    in
      ret () handle Error _ => false
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
                val () = println "Exists-solver to solve this: "
                val () = app println $ (str_vc false "" vc @ [""])
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
          val () = println "BigO-compare-solver to solve this: "
          val () = app println $ str_vc false "" vc @ [""]
          fun get_arity i =
              case i of
                  TimeAbs (_, i, _) => 1 + get_arity i
                | _ => 0
          val arity = get_arity i1
          val result = timefun_le hs arity i1 i2
          val () = println $ str_bool result
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
