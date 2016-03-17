structure BigOSolver = struct
open UVarUtil
open NoUVarExpr
open VC
open NoUVarSubst
         
infixr 0 $
infix 3 /\
infix 1 -->

fun forget_i_vc x n (hs, p) = 
    let
        fun f (h, (hs, x)) = 
            case h of 
                VarH _ => (h :: hs, x + 1) 
              | PropH p => (PropH (forget_i_p x 1 p) :: hs, x) handle ForgetError _ => (hs, x) (* just give up hypothesis if it involves [x] *)
        val (hs, x) = foldr f ([], 0) hs
    in
        (hs, forget_i_p x 1 p)
    end

fun and_all ps = foldl' (fn (p, acc) => acc /\ p) (True dummy) ps

fun vc2prop (hs, p) =
    foldl (fn (h, p) => case h of VarH (name, b) => Quan (Forall, Base b, (name, dummy), p) | PropH p1 => p1 --> p) p hs

fun by_master_theorem hs (name1, arity1) (name0, arity0) vcs =
    let
        val vcs' = append_hyps ([VarH (name0, TimeFun arity0), VarH (name1, TimeFun arity1)] @ hs) vcs
        (* val () = app println $ concatMap (fn vc => str_vc false "" vc @ [""]) vcs' *)
        val () = println "by_master_theorem to apply SMT solver to discharge some VCs: "
        val (vcs, vcs') = unzip $ List.mapPartial (fn (vc, out) => case out of SOME (vc', _) => SOME (vc, vc') | NONE => NONE) $ zip (vcs, SMTSolver.smt_solver "" vcs')
        val () = println "by_master_theorem to solve this myself: "
        val () = app println $ concatMap (fn vc => str_vc false "" vc @ [""]) vcs'
    in
        case vcs of
            [vc as (hs', p)] =>
            let
                (* (* number of variables in context *) *)
                val nx = length $ List.filter (fn h => case h of VarH _ => true | _ => false) hs'
            in
                case p of
                    BinPred (LeP, i1, BinOpI (TimeApp, BinOpI (TimeApp, VarI (g, _), VarI (m, _)), i2)) =>
                    if g = nx andalso m < nx then
                        case i2 of
                            VarI (n, _) =>
                            if n < nx andalso m <> n then
                                let
                                    (* val addends = collect_AddI i1 *)
                                    (* fun get_params is = *)
                                    (*     case is of *)
                                    (*         [] => NONE *)
                                    (*       | i :: is => *)
                                    
                                    (* open Real *)
                                    (* val T = *)
                                    (*     case get_params addends of *)
                                    (*         NONE => NONE *)
                                    (*       | SOME (a, b, f) => *)
                                    (*         case compare_params (a, b, f) of *)
                                    (*             AB_Dom => SOME (ExpI (VarI (0, dummy), Math.ln (fromInt a) / Math.ln (fromInt b))) *)
                                    (*           | Both_Dom => NONE *)
                                    (*           | F_Dom => NONE *)
                                    (*           | NotSure => NONE *)
                                in
                                    (* NONE *)
                                    SOME (TimeAbs (("", dummy), TimeAbs (("", dummy), T0 dummy, dummy), dummy), [])
                                         (* SOME T *)
                                end
                            else
                                NONE
                          | _ =>
                            let
                                val is = collect_AddI i1
                                fun test i =
                                    case i of
                                        BinOpI (TimeApp, BinOpI (TimeApp, VarI (g', _), VarI (m', _)), i2') =>
                                        if g' = g andalso m' = m then
                                            SOME i2'
                                        else NONE
                                      | _ => NONE
                                val (focus, rest) = partitionOption test is
                            in
                                (* NONE *)
                                SOME (TimeAbs (("", dummy), TimeAbs (("", dummy), T0 dummy, dummy), dummy), [])
                                     (* SOME T *)
                            end
                    else NONE
                  | _ =>
                    NONE
            end
          | _ => NONE
    end
            
fun infer_exists hs name1 p =
    case p of
        Quan (Exists, Base (TimeFun arity0), (name0, _), BinConn (And, bigO as BinPred (BigO, VarI (n0, _), VarI (n1, _)), BinConn (Imply, bigO', p))) =>
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
        Quan (Exists, Base (TimeFun arity), (name, _), p) =>
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
