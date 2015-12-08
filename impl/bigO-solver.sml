structure BigOSolver = struct
open UVarUtil
open NoUVarExpr
open VC
open NoUVarSubst
         
infixr 0 $
infix 3 /\
infix 1 -->

fun solve_one vc =
  case vc of
      ([VarH (_, Nat)], BinPred (LeP, i1, i2)) =>
      let
          fun is_le i1 i2 =
              case (i1, i2) of
                  (BinOpI (AddI, i1a, i1b), BinOpI (BigO, VarI (c, _), _)) => 
                  (case try_forget (forget_i_i c 1) i1 of
                       SOME _ => is_le i1a i2 andalso is_le i1b i2
                     | _ => false
                  )
                (* | (_, BinOpI (AddI, i2a, i2b)) => is_le i1 i2a orelse is_le i1 i2b *)
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
          eq_i i1 i2 orelse is_le i1 i2
      end
    | _ => false

fun partitionOption f xs =
    case xs of
        [] => ([], [])
      | x :: xs =>
        let
            val (ys, zs) = partitionOption f xs
        in
            case f x of
                SOME y => (y :: ys, zs)
              | _ => (ys, x :: zs)
        end

fun forget_i_vc x n (hs, p) = 
    let
        fun f (h, (hs, x)) = 
            case h of 
                VarH _ => (h :: hs, x + 1) 
              | PropH p => (PropH (forget_i_p x 1 p) :: hs, x)
        val (hs, x) = foldr f ([], 0) hs
    in
        (hs, forget_i_p x 1 p)
    end

fun and_all ps = foldl' (fn (p, acc) => acc /\ p) (True dummy) ps

fun vc2prop (hs, p) =
    simp_p $ foldl (fn (h, p) => case h of VarH (name, b) => Quan (Forall, Base b, (name, dummy), p) | PropH p1 => p1 --> p) p hs

fun solve vc =
  case vc of
      (hs, Quan (Exists, Base Profile, name, p)) =>
      let
          val vcs = split_prop p
          val (rest, vcs) = partitionOption (fn vc => try_forget (forget_i_vc 0 1) vc) vcs
          val done = List.all id $ map solve_one vcs
          (* val done = true *)
      in
          map (fn (hs', p) => (hs' @ hs, p)) rest @
          (if done then []
           else [(hs, Quan (Exists, Base Profile, name, and_all (map vc2prop vcs)))])
      end
    | _ => [vc]

fun filter_solve vcs = concatMap solve vcs

fun solve_vcs (vcs : vc list) : vc list =
    let 
	(* val () = print "Simplifying and applying trivial solver ...\n" *)
	val vcs = filter_solve vcs
    in
        vcs
    end

end
