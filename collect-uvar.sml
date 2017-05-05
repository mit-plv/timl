(* collect fresh uvars *)

structure CollectUVar = struct
open UVar
open Expr

fun collect_uvar_i_i i =
  case i of
      VarI _ => []
    | ConstIT _ => []
    | ConstIN _ => []
    | UnOpI (_, i, _) => collect_uvar_i_i i
    | DivI (i, _) => collect_uvar_i_i i
    | ExpI (i, _) => collect_uvar_i_i i
    | BinOpI (_, i1, i2) => collect_uvar_i_i i1 @ collect_uvar_i_i i2
    | Ite (i1, i2, i3, _) => collect_uvar_i_i i1 @ collect_uvar_i_i i2 @ collect_uvar_i_i i3
    | TrueI _ => []
    | FalseI _ => []
    | TTI _ => []
    | IAbs (_, Bind (_, i), _) => collect_uvar_i_i i
    | AdmitI _ => []
    | UVarI (x, r) =>
      case !x of
          Refined a => collect_uvar_i_i a
        | Fresh info => [(x, info, r)]
                                
fun collect_uvar_i_p p =
  case p of
      True _ => []
    | False _ => []
    | BinConn (_, p1, p2) => collect_uvar_i_p p1 @ collect_uvar_i_p p2
    | Not (p, _) => collect_uvar_i_p p
    | BinPred (_, i1, i2) => collect_uvar_i_i i1 @ collect_uvar_i_i i2
    | Quan (_, _, Bind (_, p), _) => collect_uvar_i_p p 
                                          
fun collect_uvar_t_mt t =
    case t of
        Unit _ => []
      | Arrow (t1, _, t2) => collect_uvar_t_mt t1 @ collect_uvar_t_mt t2
      | TyArray (t, _) => collect_uvar_t_mt t
      | TyNat _ => []
      | Prod (t1, t2) => collect_uvar_t_mt t1 @ collect_uvar_t_mt t2
      | UniI (s, Bind (name, t1), _) => collect_uvar_t_mt t1
      | MtVar x => []
      | MtAbs (_, Bind (_, t), _) => collect_uvar_t_mt t
      | MtApp (t1, t2) => collect_uvar_t_mt t1 @ collect_uvar_t_mt t2
      | MtAbsI (_, Bind (_, t), _) => collect_uvar_t_mt t
      | MtAppI (t, i) => collect_uvar_t_mt t
      | BaseType _ => []
      | UVar (x, r) =>
        case !x of
            Refined a => collect_uvar_t_mt a
          | Fresh info => [(x, info, r)]
    
fun collect_uvar_t_t t =
  case t of
      Mono t => collect_uvar_t_mt t
    | Uni _ => [] (* fresh uvars in Uni should either have been generalized or in previous ctx *)

open VC
                 
fun collect_uvar_i_hyp h =
    case h of
        VarH (name, b) => []
      | PropH p => collect_uvar_i_p p

fun collect_uvar_i_vc ((hyps, p) : vc) =
    let
      val hyps = concatMap collect_uvar_i_hyp hyps
      val p = collect_uvar_i_p p
    in
      hyps @ p
    end

end
