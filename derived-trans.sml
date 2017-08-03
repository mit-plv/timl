(* transformations on datatypes, declarations, etc. that can be derived from those on types, exprs, etc. *)

structure DerivedTrans = struct

open Util
open Expr
open Unbound
       
infixr 0 $
         
fun for_dt f dt =
  case f $ TDatatype (dt, dummy) of
      TDatatype (dt, _) => dt
    | _ => raise Impossible "for_dt"
                 
fun for_decls f decls =
  case f $ ELet ((NONE, NONE), Bind (Teles decls, ETT dummy), dummy) of
      ELet (_, bind, _) => unTeles $ fst $ unBind bind
    | _ => raise Impossible "for_decls"
                 
fun for_decls_e f (decls, e) =
  case f $ ELet ((NONE, NONE), Bind (Teles decls, e), dummy) of
      ELet (_, bind, _) => mapFst unTeles $ unBind bind
    | _ => raise Impossible "for_decls_e"
                 
fun for_rule f (pn, e) =
  case f $ EAbs $ Bind (pn, e) of
      EAbs bind => unBind bind
    | _ => raise Impossible "for_rule"
                 
end
