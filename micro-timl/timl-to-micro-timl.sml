functor IdxTransFn (structure Src : IDX
                  structure Tgt : IDX
                  val on_base_sort : Src.base_sort -> Tgt.base_sort
                  val on_var : Src.var -> Tgt.var
                  val on_name : Src.name -> Tgt.name
                  val on_r : Src.region -> Tgt.region
                  val on_exists_anno : (Src.idx -> Tgt.idx) -> Src.idx Src.exists_anno-> Tgt.idx Tgt.exists_anno
                  val on_uvar_bs : (Src.bsort -> Tgt.bsort) -> Src.bsort Src.UVarI.uvar_bs -> Tgt.bsort Tgt.UVarI.uvar_bs
                  val on_uvar_s : (Src.bsort -> Tgt.bsort) -> (Src.sort -> Tgt.sort) -> (Src.bsort, Src.sort) Src.UVarI.uvar_s -> (Tgt.bsort, Tgt.sort) Tgt.UVarI.uvar_s
                  val on_uvar_i : (Src.bsort -> Tgt.bsort) -> (Src.idx -> Tgt.idx) -> (Src.bsort, Src.idx) Src.UVarI.uvar_i -> (Tgt.bsort, Tgt.idx) Tgt.UVarI.uvar_i
                 ) =
struct

structure Src = Src
structure Tgt = Tgt
val on_var = on_var
val on_name = on_name
val on_r = on_r
                  
open Util
open Bind
open Operators
structure S = Src
open Tgt

infixr 0 $

fun on_b b =
    case b of
        S.Base b => Base $ on_base_sort b
      | S.BSArrow (a, b) => BSArrow (on_b a, on_b b)
      | S.UVarBS x => UVarBS $ on_uvar_bs on_b x

fun on_i i =
  case i of 
      S.VarI x => VarI $ on_var x
    | S.IConst (c, r) => IConst (c, on_r r)
    | S.UnOpI (opr, i, r) => UnOpI (opr, on_i i, on_r r)
    | S.BinOpI (opr, i1, i2) => BinOpI (opr, on_i i1, on_i i2)
    | S.Ite (i1, i2, i3, r) => Ite (on_i i1, on_i i2, on_i i3, on_r r)
    | S.IAbs (b, Bind (name, i), r) => IAbs (on_b b, Bind (on_name name, on_i i), on_r r)
    | S.UVarI (x, r) => UVarI (on_uvar_i on_b on_i x, on_r r)

fun on_quan q =
  case q of
      Forall => Forall
    | Exists a => Exists $ on_exists_anno on_i a

fun on_p p =
  case p of
      S.PTrueFalse (b, r) => PTrueFalse (b, on_r r)
    | S.Not (p, r) => Not (on_p p, on_r r)
    | S.BinConn (opr, p1, p2) => BinConn (opr, on_p p1, on_p p2)
    | S.BinPred (opr, i1, i2) => BinPred (opr, on_i i1, on_i i2)
    | S.Quan (q, b, Bind (name, p), r) => Quan (on_quan q, on_b b, Bind (on_name name, on_p p), on_r r)

fun on_s s =
  case s of
      S.Basic (b, r) => Basic (on_b b, on_r r)
    | S.Subset ((b, r1), Bind (name, p), r) => Subset ((on_b b, on_r r1), Bind (on_name name, on_p p), on_r r)
    | S.SAbs (b, Bind (name, s), r) => SAbs (on_b b, Bind (on_name name, on_s s), on_r r)
    | S.SApp (s, i) => SApp (on_s s, on_i i)
    | S.UVarS (x, r) => UVarS (on_uvar_s on_b on_s x, on_r r)

end

signature IDX_TRANS = sig
  structure Src : IDX
  structure Tgt : IDX
  val on_b : Src.bsort -> Tgt.bsort
  val on_i : Src.idx -> Tgt.idx
  val on_s : Src.sort -> Tgt.sort
  val on_var : Src.var -> Tgt.var
  val on_name : Src.name -> Tgt.name
  val on_r : Src.region -> Tgt.region
end
                        
functor TypeTransFn (structure Src : TYPE
                   structure Tgt : TYPE
                   structure IdxTrans : IDX_TRANS
                   val on_base_type : Src.base_type -> Tgt.base_type
                   val on_k : Src.kind -> Tgt.kind
                   val on_uvar_mt : (Src.Idx.bsort -> Tgt.Idx.bsort) -> (Src.kind -> Tgt.kind) -> (Src.mtype -> Tgt.mtype) -> (Src.Idx.bsort, Src.kind, Src.mtype) Src.UVarT.uvar_mt -> (Tgt.Idx.bsort, Tgt.kind, Tgt.mtype) Tgt.UVarT.uvar_mt
                   sharing IdxTrans.Src = Src.Idx
                   sharing IdxTrans.Tgt = Tgt.Idx
                   sharing type  Src.var = Src.Idx.var
                   sharing type  Src.name = Src.Idx.name
                   sharing type  Src.region = Src.Idx.region
                   sharing type  Tgt.var = Tgt.Idx.var
                   sharing type  Tgt.name = Tgt.Idx.name
                   sharing type  Tgt.region = Tgt.Idx.region
                  ) =
struct

open Util
open Bind
structure S = Src
open Tgt
open IdxTrans
       
infixr 0 $
         
fun on_mt t =
  case t of
      S.Arrow (t1, i, t2) => Arrow (on_mt t1, on_i i, on_mt t2)
    | S.TyNat (i, r) => TyNat (on_i i, on_r r)
    | S.TyArray (t, i) => TyArray (on_mt t, on_i i)
    | S.Unit r => Unit $ on_r r
    | S.Prod (t1, t2) => Prod (on_mt t1, on_mt t2)
    | S.UniI (s, Bind (name, t), r) => UniI (on_s s, Bind (on_name name, on_mt t), on_r r)
    | S.MtVar x => MtVar $ on_var x
    | S.MtApp (t1, t2) => MtApp (on_mt t1, on_mt t2)
    | S.MtAbs (k, Bind (name, t), r) => MtAbs (on_k k, Bind (on_name name, on_mt t), on_r r)
    | S.MtAppI (t, i) => MtAppI (on_mt t, on_i i)
    | S.MtAbsI (b, Bind (name, t), r) => MtAbsI (on_b b, Bind (on_name name, on_mt t), on_r r)
    | S.BaseType (t, r) => BaseType (on_base_type t, on_r r)
    | S.UVar (x, r) => UVar (on_uvar_mt on_b on_k on_mt x, on_r r)
    | S.TDatatype (dt, r) => TDatatype (on_dt dt, on_r r)

and on_dt (Bind (name, tbinds)) =
    let
      val (tname_kinds, (bsorts, constrs)) = unfold_binds tbinds
      val bsorts = map on_b bsorts
      fun on_constr_core ibinds =
        let
          val (name_sorts, (t, is)) = unfold_binds ibinds
          val name_sorts = map (mapSnd on_s) name_sorts
          val t = on_mt t
          val is = map on_i is
          val ibinds = fold_binds (name_sorts, (t, is))
        in
          ibinds
        end
      val constrs = map (fn (name, c, r) => (name, on_constr_core c, on_r r)) constrs
      val tbinds = fold_binds (tname_kinds, (bsorts, constrs))
    in
      Bind (name, tbinds)
    end

end

structure TiML2microTiML = struct

type long_id = (string * unit) option * (int * unit)
structure LongIdVar = struct
type var = long_id
end
structure Var = LongIdVar
open BaseSorts
structure Idx = IdxFn (structure UVarI = UVar
                       type base_sort = base_sort
                       type var = Var.var
                       type name = unit
                       type region = unit
                       type 'a exists_anno = unit
                      )
structure TiMLType = TypeFn (structure Idx = Idx
                             structure UVarT = NoUVar
                             type base_type = BaseTypes.base_type
                            )
structure TiML = TAst (structure Idx = Idx
                       structure Type = TiMLType
                       structure UVarT = NoUVar
                      )
structure MicroTiML = MicroTiMLFn (Idx)

structure LongIdShift = struct
open ShiftUtil
open LongIdUtil
type var = long_id
val shiftx_v = shiftx_int
fun shiftx_long_id x n b = on_v_long_id shiftx_v x n b
val forget_v = forget_int ForgetError
fun forget_long_id x n b = on_v_long_id forget_v x n b
val shiftx_var = shiftx_long_id
val forget_var = forget_long_id
end

structure IdxShift = IdxShiftFn (structure Idx = Idx
                                 structure ShiftableVar = LongIdShift)
open IdxShift       
structure TypeShift = TypeShiftFn (structure Type = TiMLType
                                  structure ShiftableVar = LongIdShift
                                  structure ShiftableIdx = IdxShift
                                 )
open TypeShift
       
structure IdxUtil = IdxUtilFn (structure Idx = Idx
                               val dummy = ()
                              )
open IdxUtil
                                  
structure S = TiML
structure T = MicroTiML
open T
structure Op = Operators
open Util
open Bind
open ShiftUtil
       
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

fun PEqs pairs = combine_And $ map PEq pairs
  
val BSUnit = Base UnitSort

fun TExistsI (s, t) = TQuanI (Exists (), (s, t))
fun TExistsIMany (ctx, t) = foldl TExistsI t ctx
fun TAbsIMany (ctx, t) = foldl TAbsI t ctx
fun TAbsTMany (ctx, t) = foldl TAbsT t ctx
                  
fun on_mt (t : S.mtype) : ty =
  case t of
      S.Arrow (t1, i, t2) => TArrow (on_mt t1, i, on_mt t2)
    | S.TyNat (i, _) => TNat i
    | S.TyArray (t, i) => TArr (on_mt t, i)
    | S.Unit _ => TUnit
    | S.Prod (t1, t2) => TProd (on_mt t1, on_mt t2)
    | S.UniI (s, Bind (_, t), r) => TQuanI (Forall, (s, on_mt t))
    | S.MtVar x => TVar x
    | S.MtApp (t1, t2) => TAppT (on_mt t1, on_mt t2)
    | S.MtAbs (k, Bind (_, t), _) => TAbsT (on_k k, on_mt t)
    | S.MtAppI (t, i) => TAppI (on_mt t, i)
    | S.MtAbsI (b, Bind (_, t), _) => TAbsI (b, on_mt t)
    | S.BaseType t => TConst (on_base_type t)
    | S.UVar (x, _) => exfalso x
    | S.TDatatype (Bind (_, tbinds), _) =>
      let
        val (tname_kinds, (bsorts, constrs)) = unfold_binds tbinds
        val tnames = map fst tname_kinds
        fun on_constr (ibinds : S.mtype S.constr_core) =
          let
            val len_bsorts = length bsorts
            val ibinds = on_i_ibinds shiftx_i_s (on_pair (shiftx_i_mt, on_list shiftx_i_i)) 0 len_bsorts ibinds
            val (name_sorts, (t, is)) = unfold_binds ibinds
            val () = assert (fn () => length is = len_bsorts) "length is = len_bsorts"
            val formal_iargs = map (fn x => VarI (int2var x)) $ rev $ range $ len_bsorts
            val t = shiftx_i_mt 0 1 t
            val is = map (shiftx_i_i 0 1) is
            val formal_iargs = map (shiftx_i_i 0 (length name_sorts + 1)) formal_iargs
            val prop = PEqs $ zip (is, formal_iargs)
            (* val extra_sort_name = "__datatype_constraint" *)
            val extra_sort = Subset ((BSUnit, ()), Bind ((), prop), ())
            val t = on_mt t
            val t = TExistsIMany (extra_sort :: map snd (rev name_sorts), t)
          in
            t
          end
        val len_tnames = length tnames
        val k = KArrowTypes len_tnames $ KArrows bsorts KType
        val ts = map (fn (_, c, _) => on_constr c) constrs
        val t = combine_TSum ts
        val t = TAbsIMany (rev bsorts, t)
        val t = TAbsTMany (repeat len_tnames KType, t)
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

structure UnitTest = struct

structure U = UnderscoredExpr
fun trans_long_id (m, x) = (Option.map (mapSnd (const_fun ())) m, mapSnd (const_fun ()) x)
structure IdxTrans = IdxTransFn (structure Src = U
                                 structure Tgt = Idx
                                 val on_base_sort = id
                                 val on_var = trans_long_id
                                 fun on_name _ = ()
                                 fun on_r _ = ()
                                 fun on_exists_anno _ _ = ()
                                 fun on_uvar_bs _ _ = raise Impossible "IdxTrans/on_uvar_bs()"
                                 fun on_uvar_s _ _ _ = raise Impossible "IdxTrans/on_uvar_s()"
                                 fun on_uvar_i _ _ _ = raise Impossible "IdxTrans/on_uvar_i()"
                                )
structure TypeTrans = TypeTransFn (structure Src = U
                                   structure Tgt = TiMLType
                                   structure IdxTrans = IdxTrans
                                   val on_base_type = id
                                   fun on_k k = mapSnd (map IdxTrans.on_b) k
                                   fun on_uvar_mt _ _ _ _ = raise Impossible "TypeTrans/on_uvar_mt()"
                                  )

open Parser
open Elaborate
open NameResolve
       
(* val SNat = Basic (Base Nat, ()) *)
(* val nil = fold_ibinds ([], (S.Unit (), [N0])) *)
(* val cons = fold_ibinds ([("n", SNat)], (S.Prod (), [V0 %+ N1])) *)
(* val src = TDatatype (, ()) *)

fun test () =
  let
    val prog = parse_file "list.timl"
    val prog = elaborate_prog prog
    val (prog, _, _) = resolve_prog empty prog
    val (_, TopModBind (ModComponents (decls, _))) = hd prog
    val Datatype (dt, _) = hd decls
    val dt = TypeTrans.on_dt dt
    val t = TiMLType.TDatatype (dt, ())
    val t = on_mt t
(* val () = println $ str_t ([], []) t *)
  in
    t
  end
                          
end
                             
end
