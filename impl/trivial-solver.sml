structure TrivialSolver = struct
open UVarUtil
(* open OnlyIdxUVarExpr *)
open Expr
         
fun solve (ctx, ps, p) =
  isSome (List.find (eq_p op= p) ps) orelse
  case p of
      BinConn (Imply, p1, p2) => solve (ctx, p1 :: ps, p2)
    | BinConn (Iff, p1, p2) => solve (ctx, p1 :: ps, p2) andalso solve (ctx, p2 :: ps, p1)
    | BinConn (And, p1, p2) => solve (ctx, ps, p1) andalso solve (ctx, ps, p1)
    | BinConn (Or, p1, p2) => solve (ctx, ps, p1) orelse solve (ctx, ps, p1)
    | True _ => true
    | BinPred (EqP, i1, i2) => eq_i op= i1 i2
    | BinPred (LeP, i1, i2) => eq_i op= i1 i2
    | _ => false

fun solve_vc (ctx, ps, p, _) = solve (ctx, ps, p)

fun filter_solve vcs = List.filter (fn vc => solve_vc vc = false) vcs

open VC

fun simp_and_solve_vcs (vcs : vc list) : vc list =
    let 
	(* val () = print "Simplifying and applying trivial solver ...\n" *)
	val vcs = filter_solve vcs
	val vcs = map (simp_vc op=) vcs
	val vcs = filter_solve vcs
    in
        vcs
    end

end
