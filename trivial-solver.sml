structure TrivialSolver = struct
open UVar
open NoUVarExpr
open VC
         
fun solve (hyps, p) =
  List.exists (fn h => case h of PropH p' => eq_p p p' | _ => false) hyps orelse
  case p of
      BinConn (Imply, p1, p2) => solve (PropH p1 :: hyps, p2)
    | BinConn (Iff, p1, p2) => solve (hyps, BinConn (Imply, p1, p2)) andalso solve (hyps, BinConn (Imply, p2, p1))
    | BinConn (And, p1, p2) => solve (hyps, p1) andalso solve (hyps, p1)
    | BinConn (Or, p1, p2) => solve (hyps, p1) orelse solve (hyps, p1)
    | True _ => true
    | BinPred (EqP, i1, i2) => eq_i i1 i2
    | BinPred (LeP, i1, i2) => eq_i i1 i2
    | _ => false

fun filter_solve vcs = List.filter (fn vc => solve vc = false) vcs

fun simp_and_solve_vcs (vcs : vc list) : vc list =
    let 
	(* val () = print "Simplifying and applying trivial solver ...\n" *)
	val vcs = filter_solve vcs
	val vcs = map simp_vc vcs
	val vcs = filter_solve vcs
    in
        vcs
    end

end
