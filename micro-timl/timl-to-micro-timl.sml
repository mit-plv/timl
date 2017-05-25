structure TiML2microTiML = struct

structure LongIdVar = struct
type var = string option * int
end
structure Var = LongIdVar
open BaseSorts
structure Idx = IdxFn (struct
                        structure UVarI = UVar
                        type base_sort = base_sort
                        type var = Var.var
                        type name = unit
                        type region = unit
                        end)
structure TiMLType = TypeFn (struct
                              structure Idx = Idx
                              structure UVarT = NoUVar
                              type base_type = BaseTypes.base_type
                              type var = Var.var
                              type name = unit
                              type region = unit
                              end)
structure TiML = TAst (structure Idx = Idx structure Type = TiMLType)
structure MicroTiML = MicroTiMLFn (Idx)
structure S = TiML
structure T = MicroTiML
open T
structure Op = Operators
open Util
open Bind
       
infixr 0 $

exception Error of string

fun on_expr_un_op opr =
  case opr of
      EUFst => EUProj ProjFst
    | EUSnd => EUProj ProjSnd

fun on_bin_op opr =
  case opr of
      Op.EBApp => EBApp
    | Op.EBPair => EBPair
    | Op.Add => EBPrim PEBIntAdd
    | Op.New => EBNew
    | Op.Read => EBRead

fun on_base_type t =
  case t of
      Int => TCInt

fun KArrows bs k = foldr KArrow k bs
fun KArrowTs ks k = foldr KArrowT k ks
                          
fun on_k ((n, bs) : S.kind) : kind = KArrowTs (repeat n KType) $ KArrows bs KType

fun on_mt (t : S.mtype) : ty =
  case t of
      S.Arrow (t1, i, t2) => TArrow (on_mt t1, i, on_mt t2)
    | S.TyNat (i, _) => TNat i
    | S.TyArray (t, i) => TArr (on_mt t, i)
    | S.Unit _ => TConst TCUnit
    | S.Prod (t1, t2) => TBinOp (TBProd, on_mt t1, on_mt t2)
    | S.UniI (s, Bind (_, t), r) => TQuanI (Forall, s, on_mt t)
    | S.MtVar x => TVar x
    | S.MtApp (t1, t2) => TAppT (on_mt t1, on_mt t2)
    | S.MtAbs (k, Bind (_, t), _) => TAbsT (on_k k, on_mt t)
    | S.MtAppI (t, i) => TAppI (on_mt t, i)
    | S.MtAbsI (b, Bind (_, t), _) => TAbsI (b, on_mt t)
    | S.BaseType t => TConst (on_base_type t)
    | S.UVar (x, _) => exfalso x
      
fun on_e (e : S.expr) : expr =
  case e of
      S.Var x => EVar x
    | S.EConst b => EConst b
    | S.EUnOp (opr, e) => EUnOp (on_expr_un_op opr, on_e e)
    | S.BinOp (opr, e1, e2) => EBinOp (on_bin_op opr, on_e e1, on_e e2)
    | S.TriOp (Op.Write, e1, e2, e3) => EWrite (on_e e1, on_e e2, on_e e3)
    | S.EEI (opr, e, i) =>
      (case opr of
           Op.EEIAppI => EAppI (on_e e, i)
         | Op.EEIAscriptionTime => EAscTime (on_e e, i)
      )
    | S.ET (opr, t, r) =>
      (case opr of
           Op.ETNever => ENever (on_mt t)
         | Op.ETBuiltin => raise Error "can't translate builtin expression"
      )
    (* | Abs (pn, e) => *)
    (*   Abs (pn, f (x + (length $ snd $ ptrn_names pn)) n e) *)
    (* | AbsI (s, bind, r) => AbsI (s, on_e_ibind f x n bind, r) *)
    (* | Let (return, decs, e, r) => *)
    (*   let  *)
    (*     val (decs, m) = f_decls x n decs *)
    (*   in *)
    (*     Let (return, decs, f (x + m) n e, r) *)
    (*   end *)
    (* | Ascription (e, t) => Ascription (f x n e, t) *)
    (* | AppConstr (cx, is, e) => AppConstr (cx, is, f x n e) *)
    (* | Case (e, return, rules, r) => Case (f x n e, return, map (f_rule x n) rules, r) *)
      
end
