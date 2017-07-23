(* collect fresh uvars *)

structure CollectUVar = struct
open Bind
open UVar
open Expr
open Bind
       
infixr 0 $
         
fun collect_uvar_i_i i =
  case i of
      VarI _ => []
    | IConst _ => []
    | UnOpI (_, i, _) => collect_uvar_i_i i
    | BinOpI (_, i1, i2) => collect_uvar_i_i i1 @ collect_uvar_i_i i2
    | Ite (i1, i2, i3, _) => collect_uvar_i_i i1 @ collect_uvar_i_i i2 @ collect_uvar_i_i i3
    | IAbs (_, Bind (_, i), _) => collect_uvar_i_i i
    | UVarI (x, r) =>
      case !x of
          Refined a => collect_uvar_i_i a
        | Fresh info => [(x, info, r)]
                                
fun collect_uvar_i_p p =
  case p of
      PTrueFalse _ => []
    | BinConn (_, p1, p2) => collect_uvar_i_p p1 @ collect_uvar_i_p p2
    | Not (p, _) => collect_uvar_i_p p
    | BinPred (_, i1, i2) => collect_uvar_i_i i1 @ collect_uvar_i_i i2
    | Quan (_, _, Bind (_, p), _) => collect_uvar_i_p p

fun collect_uvar_s_s s =
  case s of 
      Basic s => []
    | Subset (b, Bind (_, p), r) => []
    | SAbs (b, Bind (_, s), r) => collect_uvar_s_s s
    | SApp (s, i) => collect_uvar_s_s s
    | UVarS (x, r) =>
      case !x of
          Refined a => collect_uvar_s_s a
        | Fresh info => [(x, info, r)]
                                          
structure TypeVisitor = TypeVisitorFn (structure S = Expr
                                         structure T = Expr)
open TypeVisitor

(* type 'this collect_uvar_t_vtable = *)
(*      ('this, ((uvar_name *  *)
(*                ((string * bsort) list *  *)
(*                 (string * kind) list),mtype) uvar ref *)
(*               *  *)
(*               (uvar_name *  *)
(*                ((string * bsort) list *  *)
(*                 (string * kind) list)) * region) list  *)
(*                                                  ref) type_visitor_vtable      *)
       
fun collect_uvar_t_type_visitor_vtable cast () (* : 'this collect_uvar_t_vtable *) =
  let
    fun visit_UVar this env (x, r) =
      let
        val vtable = cast this
        val () = 
            case !x of
                Refined t => ignore $ #visit_mtype vtable this env t
              | Fresh info => push_ref env (x, info, r)
      in
        UVar (x, r)
      end
    val vtable =
        default_type_visitor_vtable
          cast
          extend_noop
          extend_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
          visit_noop
          (visit_imposs "visit_uvar")
    val vtable = override_visit_UVar vtable visit_UVar
  in
    vtable
  end

fun new_collect_uvar_t_type_visitor params = new_type_visitor collect_uvar_t_type_visitor_vtable params
    
fun collect_uvar_t_mt t =
  let
    val visitor as (TypeVisitor vtable) = new_collect_uvar_t_type_visitor ()
    val result = ref []
    val t = #visit_mtype vtable visitor result t
  in
    !result
  end

open Bind
       
(* fun collect_uvar_t_mt t = *)
(*     case t of *)
(*         Unit _ => [] *)
(*       | Arrow (t1, _, t2) => collect_uvar_t_mt t1 @ collect_uvar_t_mt t2 *)
(*       | TyArray (t, _) => collect_uvar_t_mt t *)
(*       | TyNat _ => [] *)
(*       | Prod (t1, t2) => collect_uvar_t_mt t1 @ collect_uvar_t_mt t2 *)
(*       | UniI (s, Bind (name, t1), _) => collect_uvar_t_mt t1 *)
(*       | MtVar x => [] *)
(*       | MtAbs (_, Bind (_, t), _) => collect_uvar_t_mt t *)
(*       | MtApp (t1, t2) => collect_uvar_t_mt t1 @ collect_uvar_t_mt t2 *)
(*       | MtAbsI (_, Bind (_, t), _) => collect_uvar_t_mt t *)
(*       | MtAppI (t, i) => collect_uvar_t_mt t *)
(*       | BaseType _ => [] *)
(*       | TDatatype _ => raise Unimpl "collect_uvar_t_mt()/TDatatype" *)
(*       | UVar (x, r) => *)
(*         case !x of *)
(*             Refined a => collect_uvar_t_mt a *)
(*           | Fresh info => [(x, info, r)] *)
    
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
