structure TiML2microTiML = struct

structure LongIdVar = struct
type var = (string * unit) option * (int * unit)
end
structure Var = LongIdVar
open BaseSorts
structure Idx = IdxFn (structure UVarI = UVar
                       type base_sort = base_sort
                       type var = Var.var
                       type name = unit
                       type region = unit)
(* structure TiMLType = TypeFn (structure Idx = Idx *)
(*                              structure UVarT = NoUVar *)
(*                              type base_type = BaseTypes.base_type *)
(*                              type var = Var.var *)
(*                              type name = unit *)
(*                              type region = unit) *)
structure TiML = TAst (structure Idx = Idx
                       structure UVarT = NoUVar
                       type base_type = BaseTypes.base_type)
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
fun KArrowTypes n k = KArrowTs (repeat n KType) k
                          
fun on_k ((n, bs) : S.kind) : kind = KArrowTypes n $ KArrows bs KType

val TUnit = TConst TCUnit
val TEmpty = TConst TCEmpty
fun TSum (t1, t2) = TBinOp (TBSum, t1, t2)
fun TProd (t1, t2) = TBinOp (TBProd, t1, t2)

fun foldr' f init xs = foldl' f init $ rev xs

fun combine_TSum ts = foldr' TSum TEmpty ts

fun int2var x = (NONE, (x, ()))
                  
fun on_mt (t : S.mtype) : ty =
  case t of
      S.Arrow (t1, i, t2) => TArrow (on_mt t1, i, on_mt t2)
    | S.TyNat (i, _) => TNat i
    | S.TyArray (t, i) => TArr (on_mt t, i)
    | S.Unit _ => TUnit
    | S.Prod (t1, t2) => TProd (on_mt t1, on_mt t2)
    | S.UniI (s, Bind (_, t), r) => TQuanI (Forall, s, on_mt t)
    | S.MtVar x => TVar x
    | S.MtApp (t1, t2) => TAppT (on_mt t1, on_mt t2)
    | S.MtAbs (k, Bind (_, t), _) => TAbsT (on_k k, on_mt t)
    | S.MtAppI (t, b, i) => TAppI (on_mt t, b, i)
    | S.MtAbsI (b, Bind (_, t), _) => TAbsI (b, on_mt t)
    | S.BaseType t => TConst (on_base_type t)
    | S.UVar (x, _) => exfalso x
    | S.TDatatype (dt as (_, tnames, bsorts, constrs, _)) =>
      let
        fun on_constr ibinds =
          let
            val len_bsorts = length bsorts
            val ibinds = on_ibinds shiftx_i_s (on_pair (on_noop, on_pair (shiftx_i_mt, on_list shiftx_i_i))) 0 len_bsorts
            val (name_sorts, (t, is)) = unfold_binds ibinds
            val () = assert (fn () => length is = len_bsorts) "length is = len_bsorts"
            val formal_iargs = map (fn x => VarI (int2var x)) $ rev $ range $ len_bsorts
            val t = shiftx_i_mt 0 1 t
            val is = map (shiftx_i_i 0 1) is
            val formal_iargs = map (shift_i_i 0 (length name_sorts + 1)) formal_iargs
            val prop = PEqs (is, formal_iargs)
            val extra_sort_name = "__datatype_constraint"
            val extra_sort = Subset ((BSUnit, ()), Bind ((extra_sort_name, ()), prop), ())
            val t = TExistsIMany (extra_sort :: map snd (rev name_sorts), t)
          in
            t
          end
        val n = length tnames
        val k = KArrowTypes n $ KArrows bsorts KType
        val ts = map (fn (_, c, _) => on_constr c) constrs
        val t = combine_TSum ts
        val t = TAbsIMany (rev bsorts, t)
        val t = TAbsTMany (repeat n KType, t)
      in
        TRec (k, t)
      end

fun on_ptrn pn e =
    case pn of
        S.TTP _ => e
      | S.AliasP (_, pn, _) => e
      | S.ConstrP ((x, eia), inames, pn, r) => e
      | S.VarP name => e
      | S.PairP (pn1, pn2) => e
      | S.AnnoP (pn, t) => e
      
fun on_e (e : S.expr) : expr =
  case e of
      S.Var (x, _) => EVar x
    | S.EConst (c, _) => EConst c
    | S.EUnOp (opr, e, _) => EUnOp (on_expr_un_op opr, on_e e)
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
    (* | S.Case (e, return, rules, _) => *)
    (*   Case (e, return, map (f_rule x n) rules) *)
    (* | S.Abs (pn, e) => *)
    (*   Abs (pn, e) *)
    | S.AbsI (s, Bind (_, e), _) => EAbsI (s, on_e e)
    (* | Let (return, decs, e, r) => *)
    (*   let  *)
    (*     val (decs, m) = f_decls x n decs *)
    (*   in *)
    (*     Let (return, decs, f (x + m) n e, r) *)
    (*   end *)
    | S.Ascription (e, t) => EAscType (on_e e, on_mt t)
    (* | AppConstr (cx, is, e) => AppConstr (cx, is, f x n e) *)
      
end
