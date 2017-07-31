functor ExprUtilFn (Expr : EXPR) = struct

open Pattern
open Expr
open Operators
open Util
open Bind

infixr 0 $
         
fun ETT r = EConst (ECTT, r)
fun EConstInt (n, r) = EConst (ECInt n, r)
fun EConstNat (n, r) = EConst (ECNat n, r)
fun EFst (e, r) = EUnOp (EUFst, e, r)
fun ESnd (e, r) = EUnOp (EUSnd, e, r)
fun EApp (e1, e2) = EBinOp (EBApp, e1, e2)
fun EPair (e1, e2) = EBinOp (EBPair, e1, e2)
fun EAppI (e, i) = EEI (EEIAppI, e, i)
fun EAppIs (f, args) = foldl (swap EAppI) f args
fun EAppT (e, i) = EET (EETAppT, e, i)
fun EAppTs (f, args) = foldl (swap EAppT) f args
fun EAsc (e, t) = EET (EETAsc, e, t)
fun EAscTime (e, i) = EEI (EEIAscTime, e, i)
fun ENever (t, r) = ET (ETNever, t, r)
fun EBuiltin (t, r) = ET (ETBuiltin, t, r)
  
fun collect_Pair e =
  case e of
      EBinOp (EBPair, e1, e2) =>
      collect_Pair e1 @ [e2]
    | _ => [e]
             
fun collect_EAppI e =
  case e of
      EEI (opr, e, i) =>
      (case opr of
           EEIAppI =>
             let 
               val (e, is) = collect_EAppI e
             in
               (e, is @ [i])
             end
         | _ => (e, [])
      )
    | _ => (e, [])

fun collect_EAppT e =
  case e of
      EET (opr, e, i) =>
      (case opr of
           EETAppT =>
           let 
             val (e, is) = collect_EAppT e
           in
             (e, is @ [i])
           end
         | _ => (e, [])
      )
    | _ => (e, [])

fun is_value (e : expr) : bool =
  case e of
      EVar _ => true
    | EConst (c, _) =>
      (case c of
           ECTT => true
         | ECNat _ => true
         | ECInt _ => true
      )
    | EUnOp (opr, e, _) =>
      (case opr of
           EUFst => false
         | EUSnd => false
      )
    | EBinOp (opr, e1, e2) =>
      (case opr of
           EBApp => false
         | EBPair => is_value e1 andalso is_value e2
         | EBNew => false
         | EBRead => false
         | EBAdd => false
      )
    | ETriOp _ => false
    | EEI (opr, e, i) =>
      (case opr of
           EEIAppI => false
         | EEIAscTime => false
      )
    | EET (opr, e, t) =>
      (case opr of
           EETAppT => false
         | EETAsc => false
      )
    | ET (opr, t, _) =>
      (case opr of
           ETNever => true
         | ETBuiltin => true
      )
    | EAbs _ => true
    | EAbsI _ => true
    | ELet _ => false
    | EAppConstr (_, _, _, e, _) => is_value e
    | ECase _ => false

fun MakeAnnoP (pn, t) = AnnoP (pn, Outer t)
fun MakeEAbs (pn, e) = EAbs $ Binders.Bind (pn, e)
fun MakeEAbsI (name, s, e, r) = EAbsI (IBindAnno ((name, s), e), r)
      
end
