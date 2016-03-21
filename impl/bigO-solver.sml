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
    foldl (fn (h, p) => case h of VarH (name, b) => Quan (Forall, Base b, NONE, (name, dummy), p) | PropH p1 => p1 --> p) p hs
          
fun hyps2ctx hs = List.mapPartial (fn h => case h of VarH (name, _) => SOME name | _ => NONE) hs

fun by_master_theorem hs (name1, arity1) (name0, arity0) vcs = let
  val vcs' = append_hyps ([VarH (name0, TimeFun arity0), VarH (name1, TimeFun arity1)] @ hs) vcs
  (* val () = app println $ concatMap (fn vc => str_vc false "" vc @ [""]) vcs' *)
  (* val () = println "Master-Theorem-solver to apply SMT solver to discharge some VCs. " *)
  val (vcs, vcs') = unzip $ List.mapPartial (fn (vc, out) => case out of SOME (vc', _) => SOME (vc, vc') | NONE => NONE) $ zip (vcs, SMTSolver.smt_solver "" vcs')
  val () = println "Master-Theorem-solver to solve this: "
  val () = app println $ concatMap (fn vc => str_vc false "" vc @ [""]) vcs'
  exception Error of string
  fun runError m _ = let
    val ret as (f, _) = m ()
    val ctx = List.mapPartial (fn h => case h of VarH (name, _) => SOME name | _ => NONE) hs
    val () = println $ sprintf "Yes! I solved this: $" [str_i ctx f]
  in
    SOME ret
  end
                     handle Error msg =>
                            let
                              val () = printf "Oh no! I can't solve this because: $\n" [msg]
                            in
                              NONE
                            end
  fun main () =
      case vcs of
          [vc as (hs', p)] =>
          (case p of
               BinPred (LeP, i1, BinOpI (TimeApp, BinOpI (TimeApp, VarI (g, _), VarI (m, _)), n_i)) => let
              (* number of variables in context *)
              val nx = length $ List.filter (fn h => case h of VarH _ => true | _ => false) hs'
              val () = if g = nx andalso m < nx then () else raise Error "g = nx andalso m < nx"
              (* ToDo: check that [n_i] are well-scoped in [hs'] *)
              (* ToDo: check that [m] doesn't appear in [n_i] *)
              val vc' as (hyps, _) = hd vcs'
              fun ask_smt_vc vc =
                  null $ List.mapPartial id $ SMTSolver.smt_solver "" [vc]
              fun ask_smt p = ask_smt_vc (hyps, p)
              val N1 = ConstIN (1, dummy)
              fun V n = VarI (n, dummy)
              fun to_real i = UnOpI (ToReal, i, dummy)
              val m_i = V m
              val m_ = to_real m_i
              val n_ = to_real n_i
            in
              (* test the case: a * T m (n/b) + f m n <= T m n  *)
              let
                val is = collect_AddI i1
                fun get_params is = let
                  (* find terms of the form [T m (ceil (n/b))] (or respectively for [floor]) *)
                  fun is_sub_problem i =
                      case i of
                          BinOpI (TimeApp, BinOpI (TimeApp, VarI (g', _), VarI (m', _)), UnOpI (opr, DivI (n', (b, _)), _)) =>
                          if g' = g andalso m' = m andalso (opr = Ceil orelse opr = Floor) andalso ask_smt (n' %= n_) then
                            SOME b
                          else NONE
                        | _ => NONE
                  val (bs, f) = partitionOption is_sub_problem is
                  val a = length bs
                  val b = if null bs then raise Error "null bs" else hd bs
                  (* val () = if ask_smt (combine_And $ map (fn b' => b' %= b) (tl bs)) then () else raise Error *)
                  (* fun i_to_int i = *)
                  (*     case simp_i i of *)
                  (*         ConstIN (n, _) => SOME n *)
                  (*       | _ => NONE *)
                  (* val b = case findOption i_to_int bs of SOME b => b | NONE => raise Error *)
                  val () = if List.all (curry op= b) (tl bs) then () else raise Error "all bs eq"
                in
                  (a, b, f)
                end
                val (a, b, fs) = get_params is
                (* try to describe each term in one of the following three cases *)
                datatype asym_case =
                         (* O (n^c) *)
                         O_c of int
                         (* \Theta (n^c * (lg n)^k) *)
                         | Theta_c_k of int * int
                         (* \Omega (n^c) *)
                         | Omega_c of int 
                local
                  open Cont
                in
                fun call f = callcc (fn k => f (fn v => throw k v))
                fun callfun f = call o f
                end
                fun do_summarize_n i return = let
                  val () = case i of ConstIT _ => return $ Theta_c_k (0, 0) | _ => () 
                  val () = case i of UnOpI (ToReal, ConstIN _, _) => return $ Theta_c_k (0, 0) | _ => () 
                  val () = if ask_smt (i %= n_) then return $ Theta_c_k (1, 0) else ()
                  val () = if ask_smt (i %= m_) then raise Error "m in summarize_n" else ()
                in
                  raise Error "summarize_n fails"
                end
                val summarize_n = callfun do_summarize_n
                fun do_summarize i return = let
                  (* test for [f m n] where [f]'s bigO class is known *)
                  val () =
                      case i of
                          BinOpI (TimeApp, BinOpI (TimeApp, f_i as VarI (f, _), m'), n') =>
                          let
                            val () = if ask_smt (m' %= m_ /\ n' %= n_) then () else raise Error "[m' = m_ /\\ n' = n_] in summarize()"
                            fun match_bigO f hyps hyp =
                                case hyp of
                                    PropH (BinPred (BigO, f', g)) =>
                                    if eq_i f' f then SOME g else NONE
                                  | _ => NONE
                            val g =
                                case find_hyp (forget_i_i 0 1) shift_i_i match_bigO f_i hyps of
                                    SOME (g, _) => g
                                  | NONE => raise Error "find_hyp fails"
                          in
                            return $ call $ do_summarize $ simp_i (g %@ m_ %@ n_)
                          end
                        | _ => ()
                  (* test for [ ... * m * ... ] *)
                  val () =
                      case i of
                          BinOpI (MultI, i1, i2) =>
                          let
                            val is = collect_MultI i
                          in
                            case partitionOptionFirst (fn i => b2o $ ask_smt (i %= m_)) is of
                                SOME (_, rest) => return $ summarize_n $ combine_MultI rest
                              | NONE => ()
                          end
                        | _ => ()
                  val () = if ask_smt (i %<= m_) then return $ Theta_c_k (0, 0) else ()
                in
                  summarize_n i
                end
                val summarize = callfun do_summarize
                val classes = map summarize fs
                fun max_class (a, b) =
                    case a of
                        O_c c1 =>
                        (case b of
                             O_c c2 => O_c (max c1 c2)
                           | Theta_c_k (c2, _) => if c1 <= c2 then b else O_c c1
                           | Omega_c c2 => if c1 = c2 then Theta_c_k (c1, 0) else Omega_c c2
                        )
                      | Theta_c_k (c1, k1) =>
                        (case b of
                             O_c c2 => max_class (b, a)
                           | Theta_c_k (c2, k2) => if c1 = c2 then Theta_c_k (c1, max k1 k2) else if c1 > c2 then a else b
                           | Omega_c c2 => Omega_c (max c1 c2)
                        )
                      | Omega_c _ => max_class (b, a)
                val cls = foldl' max_class (Theta_c_k (0, 0)) classes
                fun exp n i = combine_MultI (repeat n i)
                val int_add = op+
                open Real
                val log_b_a = Math.ln (fromInt a) / Math.ln (fromInt b)
                val T =
                    case cls of
                        O_c c =>
                        if fromInt c < log_b_a then
                          ExpI (to_real (V 0), (toString log_b_a, dummy))
                        else raise Error "O(n^c), c >= log_b a"
                      | Theta_c_k (c, k) =>
                        if fromInt c == log_b_a then
                          exp c (to_real (V 0)) %* exp (int_add (k, 1)) (UnOpI (Log2, to_real (V 0), dummy))
                        else raise Error "Theta(n^c * log^k (n)), c = log_b a"
                      | Omega_c c =>
                        if fromInt c > log_b_a then
                          if eq_i n_i (V 0) then
                            combine_MultI fs
                          else raise Error "Omega(n^c), c = log_b a, n_i not (V 0)"
                        else raise Error "Omega(n^c), c <= log_b a"
                val T = TimeAbs (("m", dummy), TimeAbs (("n", dummy), simp_i (to_real (V 1) %* T), dummy), dummy)
                (* val ret = (TimeAbs (("", dummy), TimeAbs (("", dummy), T0 dummy, dummy), dummy), []) *)
                (* val () = raise Error *)
                val ret = (T, [])
              in
                ret
              end
              handle
              Error msg =>
              (* test the case: T m n + m + C <= T m (n + 1) *)
              let
                (* val () = printf "Failed the 1st case because: $\nTry 2nd case ...\n" [msg] *)
                val is = collect_AddI i1
                fun par i =
                    case i of
                        BinOpI (TimeApp, BinOpI (TimeApp, VarI (g', _), VarI (m', _)), n') =>
                        if g' = g andalso m' = m then
                          SOME n'
                        else NONE
                      | _ => NONE
                val (focus, rest) = partitionOption par is
                val n' = if length focus > 0 then hd focus else raise Error "null focus"
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
             | _ => raise Error "wrong pattern for by_master_theorem"
          )
        | _ => raise Error "by_master_theorem allows only 1 conjunct left"
in
  runError main ()
end
                                                                 
fun infer_exists hs (name1 as (_, arity1)) p =
    if arity1 = 0 then
      (* just to infer a Time *)
      (case p of
           BinPred (Le, i1 as (ConstIT _), VarI (x, _)) =>
           if x = 0 then SOME (i1, []) else NONE
         | _ => NONE
      )
    else
      case p of
          Quan (Exists, Base (TimeFun arity0), _, (name0, _), BinConn (And, bigO as BinPred (BigO, VarI (n0, _), VarI (n1, _)), BinConn (Imply, bigO', p))) =>
          if n0 = 0 andalso n1 = 1 andalso eq_p bigO bigO' then
            (* opportunity to apply the Master Theorem *)
            let
              (* val () = println "hit2" *)
              (* hoist the conjuncts that don't involve the time functions *)
              val vcs = split_prop p
              val (rest, vcs) = partitionOption (Option.composePartial (try_forget (forget_i_vc 0 1), try_forget (forget_i_vc 0 1))) vcs
              val vcs = concatMap split_prop $ map (simp_p o vc2prop) vcs
              val ret = by_master_theorem hs name1 (name0, arity0) vcs
            in
              case ret of
                  SOME (i, vcs) => SOME (i, append_hyps hs rest @ vcs)
                | NONE => NONE
            end
          else NONE
        | _ => NONE
               
fun solve_exists (vc as (hs, p)) =
    case p of
        Quan (Exists, Base (TimeFun arity), ins, (name, _), p) =>
        let
          (* val () = println "hit1" *)
          fun test_ptrn p =
              case p of
                  BinConn (And, p1, p2) => SOME (p1, p2)
                | _ => SOME (p, True dummy)
        in
          case test_ptrn p of
              SOME (p1, p2) =>
              (case infer_exists hs (name, arity) p1 of
                   SOME (i, vcs1) =>
                   let
                     (* ToDo: update the link in [Quan] with [i] *)
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
              )
            | NONE => [vc]
        end
      | _ => [vc]
               
fun filter_solve vcs = concatMap solve_exists vcs

fun solve_vcs (vcs : vc list) : vc list =
    let 
      (* val () = print "Applying Big-O solver ...\n" *)
      val vcs = filter_solve vcs
    in
      vcs
    end

end
