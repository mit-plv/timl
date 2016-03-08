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

fun and_all ps = foldl' (fn (p, acc) => acc /\ p) (True dummy) ps

fun vc2prop (hs, p) =
    foldl (fn (h, p) => case h of VarH (name, b) => Quan (Forall, Base b, (name, dummy), p) | PropH p1 => p1 --> p) p hs

        (*
fun solve_one (hs, p) =
    let
        (* number of variables in context *)
        val nx = length $ List.filter (fn h => case h of VarH _ => true | _ => false) hs
    in
        case p of
            BinPred (LeP, i1, i2) =>
            let
                fun is_le idx1 idx2 =
                    case idx2 of
                        BinOpI (BigO, VarI (c2, _), i2) =>
                        (case try_forget (forget_i_i c2 1) idx1 of
                             SOME _ =>
                             (* non-recursive cases *)
                             (case idx1 of
                                  BinOpI (AddI, i1a, i1b) =>
                                  is_le i1a idx2 andalso is_le i1b idx2
                                (* | (_, BinOpI (AddI, i2a, i2b)) => is_le i1 i2a orelse is_le i1 i2b *)
                                | ConstIT _ =>
                                  if c2 = nx then
                                      case i2 of
                                          ConstIT (s, _) =>
                                          (case Real.fromString s of
                                               SOME r => r > 0.0
                                             | _ => false
                                          )
                                        | UnOpI (ToReal, ConstIN (n, _), _) => n > 0
                                        | UnOpI (ToReal, VarI (x, _), _) => x < nx
                                        | _ => false
                                  else
                                      false
                                | BinOpI (BigO, c1, i1) =>
                                  if c2 = nx andalso not (eq_i c1 (VarI (1, dummy))) then
                                      case (i1, i2) of
                                          (UnOpI (ToReal, ConstIN (n, _), _), UnOpI (ToReal, VarI (x2, _), _)) =>
                                          x2 < nx
                                        | (UnOpI (ToReal, VarI (x1, _), _), UnOpI (ToReal, VarI (x2, _), _)) =>
                                          x1 = x2 andalso x1 < nx
                                        | _ => false
                                  else
                                      false
                                | _ => false
                             )
                           | NONE =>
                             (* recursive cases *)
                             false
                             (* (println "hit"; true) *)
                        )
                      | _ => false
            in
                eq_i i1 i2 orelse is_le i1 i2
            end
          | _ => false
    end
        *)

fun by_master_theorem vc as (hs, p) =
(* [vc] *)
    let
        (* number of variables in context *)
        val nx = length $ List.filter (fn h => case h of VarH _ => true | _ => false) hs
    in
        case p of
            BinPred (LeP, i1, BinOpI (MultI, VarI (m, _), BinOpI (App1, VarI (g, _), VarI (n, _)))) =>
            if g = nx andalso n < nx andalso m < nx andalso m <> n then
                let
                    val addends = 
                in
                end
            else [vc]
          | _ =>
            [vc]
    end
            
fun solve vc =
    case vc of
        (* test for opportunity to apply the Master Theorem *)
        (hs, Quan (Exists, Base Fun1, name1, Quan (Exists, Base Fun1, name2, BinConn (And, bigO as BinPred (BigO, VarI (n0, _), VarI (n1, _)), BinConn (Imply, bigO', p))))) =>
        if n0 = 0 andalso n1 = 1 andalso eq_p bigO bigO' then
            let
                (* hoist the conjuncts that don't involve the time functions *)
                val vcs = split_prop p
                val (rest, vcs) = partitionOption (Option.composePartial (try_forget (forget_i_vc 0 1), try_forget (forget_i_vc 0 1))) vcs
                val vcs = concatMap split_prop $ map (simp_p o vc2prop) vcs
            in
                case vcs of
                    (* only allow one conjunct *)
                    [vc] =>
                    let
                        val vcs = by_master_theorem vc
                    in
                        (* val vcs = [] *)
                        map (fn (hs', p) => (hs' @ hs, p)) rest @
                        (case vcs of
                             [] => []
                           | _ => [(hs, Quan (Exists, Base Fun1, name1, Quan (Exists, Base Fun1, name2, BinConn (And, bigO, BinConn (Imply, bigO', and_all (map vc2prop vcs))))))]
                        )
                    end
                  | _ => [vc]
            end
        else [vc]
      | _ => [vc]

fun filter_solve vcs = concatMap solve vcs

fun solve_vcs (vcs : vc list) : vc list =
    let 
	(* val () = print "Applying Big-O solver ...\n" *)
	val vcs = filter_solve vcs
    in
        vcs
    end

end
