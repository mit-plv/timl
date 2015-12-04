structure BigOSolver = struct
open UVarUtil
open NoUVarExpr
open VC
         
fun solve (hyps, p) =
  case p of
      Quan (Exists, Base Profile, _, (Quan (Forall, Base Nat, _, BinPred (LeP, i1, i2)))) =>
      let
          fun is_le i1 i2 =
              case (i1, i2) of
                  (BinOpI (AddI, i1a, i1b), _) => is_le i1a i2 andalso is_le i1b i2
                | (_, BinOpI (AddI, i2a, i2b)) => is_le i1 i2a orelse is_le i1 i2b
                | (ConstIT _, BinOpI (BigO, VarI (c, _), i2)) =>
                  if c = 1 then
                      case i2 of
                          ConstIT (s, _) => 
                          (case Real.fromString s of
                               SOME r => r > 0.0
                             | _ => false
                          )
                        | UnOpI (ToReal, ConstIN (n, _), _) => n > 0
                        | UnOpI (ToReal, VarI (x, _), _) => x = 0
                        | _ => false
                  else
                      false
                | (BinOpI (BigO, c1, i1), BinOpI (BigO, VarI (c2, _), i2)) =>
                  if c2 = 1 andalso not (eq_i c1 (VarI (1, dummy))) then
                      case (i1, i2) of
                          (UnOpI (ToReal, ConstIN (n, _), _), UnOpI (ToReal, VarI (x2, _), _)) =>
                          x2 = 0
                        | (UnOpI (ToReal, VarI (x1, _), _), UnOpI (ToReal, VarI (x2, _), _)) =>
                          x1 = 0 andalso x2 = 0
                        | _ => false
                  else
                      false
                | _ => false
      in
          is_le i1 i2
      end
    | _ => false

fun filter_solve vcs = List.filter (fn vc => solve vc = false) vcs

fun solve_vcs (vcs : vc list) : vc list =
    let 
	(* val () = print "Simplifying and applying trivial solver ...\n" *)
	val vcs = filter_solve vcs
    in
        vcs
    end

end
