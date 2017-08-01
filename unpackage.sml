structure Unpackage = struct

open Expr
open Util
open Subst
open Bind

infixr 0 $

fun unpackage_long_id m n id =
  case id of
      ID _ => id
    | QID ((m', mr), (x, r)) =>
      if m' = m then
        ID (x + n, r)
      else
        QID ((m', mr), (x, r))
             
fun adapt f x env = f (x + env)

fun params_var m = adapt $ unpackage_long_id m
                            
fun unpackage_i m x = IdxShiftVisitor.on_i_i $ params_var m x
fun unpackage_p m x = IdxShiftVisitor.on_i_p $ params_var m x

    
(* fun unpackage_ibind f n (Bind (name, b)) = *)
(*   Bind (name, f (n + 1) b) *)

(* fun unpackage_i m n i = *)
(*   let *)
(*     val unpackage_i = unpackage_i m *)
(*   in *)
(*     case i of *)
(*         VarI id => *)
(*         (case id of *)
(* nn             ID _ => i (* forall-module must all be on the outermost *) *)
(*            | QID ((m', mr), (x, r)) => *)
(*              if m' = m then *)
(*                VarI (ID (x + n, r)) *)
(*              else *)
(*                VarI $ QID ((m', mr), (x, r)) *)
(*         ) *)
(*       | IConst _ => i *)
(*       | UnOpI (opr, i, r) => UnOpI (opr, unpackage_i n i, r) *)
(*       | BinOpI (opr, i1, i2) => BinOpI (opr, unpackage_i n i1, unpackage_i n i2) *)
(*       | Ite (i1, i2, i3, r) => Ite (unpackage_i n i1, unpackage_i n i2, unpackage_i n i3, r) *)
(*       | IAbs (bs, bind, r) => IAbs (bs, unpackage_ibind unpackage_i n bind, r) *)
(*       | UVarI _ => i (* forall-module must all be on the outermost *) *)
(*   end *)
                   
(* fun unpackage_p m n p = *)
(*   let *)
(*     val unpackage_p = unpackage_p m *)
(*   in *)
(*     case p of *)
(*         BinConn (opr, p1, p2) => BinConn (opr, unpackage_p n p1, unpackage_p n p2) *)
(*       | Not (p, r) => Not (unpackage_p n p, r) *)
(*       | BinPred (opr, i1, i2) => BinPred (opr, unpackage_i m n i1, unpackage_i m n i2) *)
(*       | Quan (q, bs, bind, r) => Quan (q, bs, unpackage_ibind unpackage_p n bind, r) *)
(*       | PTrueFalse _ => p *)
(*   end *)
                   
end
