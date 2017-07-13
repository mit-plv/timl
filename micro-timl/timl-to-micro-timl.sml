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
                   sharing type Src.name = Tgt.name
                  ) =
struct

open Util
open Unbound
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
    | S.TDatatype (Abs dt, r) => TDatatype (Abs $ on_dt dt, on_r r)

and on_dt dt =
    let
      open TypeUtil
      val (name, tbinds) = from_Unbound dt
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
      to_Unbound (name, tbinds)
    end

end

structure TiML2MicroTiML = struct

(* open BaseSorts *)
(* open Region *)
(* type name = string * region *)
(* type long_id = (string * region) option * (int * region) *)
(* structure LongIdVar = struct *)
(* type var = long_id *)
(* end *)
(* structure Var = LongIdVar *)
(* open Var *)
(* structure Idx = IdxFn (structure UVarI = UVar *)
(*                        type base_sort = base_sort *)
(*                        type var = var *)
(*                        type name = name *)
(*                        type region = region *)
(*                        type 'a exists_anno = unit *)
(*                       ) *)
(* structure TiMLType = TypeFn (structure Idx = Idx *)
(*                              structure UVarT = NoUVar *)
(*                              type base_type = BaseTypes.base_type *)
(*                             ) *)
(* structure TiML = TAst (structure Idx = Idx *)
(*                        structure Type = TiMLType *)
(*                        structure UVarT = NoUVar *)
(*                       ) *)

(* structure LongIdShift = struct *)
(* open ShiftUtil *)
(* open LongIdUtil *)
(* type var = long_id *)
(* val shift_v = shiftx_int *)
(* fun shift_long_id x n b = on_v_long_id shift_v x n b *)
(* val forget_v = forget_int ForgetError *)
(* fun forget_long_id x n b = on_v_long_id forget_v x n b *)
(* val shiftx_var = shift_long_id *)
(* val forget_var = forget_long_id *)
(* end *)

(* structure IdxShift = IdxShiftFn (structure Idx = Idx *)
(*                                  structure ShiftableVar = LongIdShift) *)
(* open IdxShift        *)
(* structure TypeShift = TypeShiftFn (structure Type = TiMLType *)
(*                                   structure ShiftableVar = LongIdShift *)
(*                                   structure ShiftableIdx = IdxShift *)
(*                                  ) *)
(* open TypeShift *)
       
(* structure IdxUtil = IdxUtilFn (structure Idx = Idx *)
(*                                val dummy = dummy *)
(*                               ) *)
(* open IdxUtil *)

structure TiML = Expr
structure S = TiML
open S
open Subst
open MicroTiML
open MicroTiMLVisitor
open MicroTiMLEx
structure Op = Operators
open Util
open Bind
open ShiftUtil
open Unbound
       
infixr 0 $
infixr 0 !!

exception T2MTError of string

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
                          
fun on_k ((n, bs) : S.kind) : bsort kind = KArrowTypes n $ KArrows bs KType

val TUnit = TConst TCUnit
val TEmpty = TConst TCEmpty
fun TSum (t1, t2) = TBinOp (TBSum, t1, t2)
fun TProd (t1, t2) = TBinOp (TBProd, t1, t2)
fun TAppIs (t, is) = foldl (swap TAppI) t is
fun TAppTs (t, ts) = foldl (swap TAppT) t ts
      
fun EInlInr (opr, t, e) = EUnOp (EUInj (opr, t), e)
fun EInl (t, e) = EInlInr (InjInl, t, e)
fun EInr (t, e) = EInlInr (InjInr, t, e)
fun EFold (t, e) = EUnOp (EUFold t, e)

fun foldr' f init xs = foldl' f init $ rev xs

fun TSums ts = foldr' TSum TEmpty ts
fun unTSums t =
  case t of
      TBinOp (TBSum, t1, t2) => t1 :: unTSums t2
    | _ => [t]
fun EInj (ts, n, e) =
  case ts of
      [] => raise Impossible "EInj []"
    | [t] =>
      let
        val () = assert (fn () => n = 0) "EInj(): n = 0"
      in
        e
      end
    | t :: ts =>
      if n <= 0 then
        EInl (TSums ts, e)
      else
        EInr (t, EInj (ts, n-1, e))

fun int2var x = (NONE, (x, dummy))

fun PEqs pairs = combine_And $ map PEq pairs
  
val BSUnit = Base UnitSort

fun TExistsI bind = TQuanI (Exists (), bind)
fun TExistsIMany (ctx, t) = foldl (TExistsI o BindAnno) t ctx
fun TAbsIMany (ctx, t) = foldl (TAbsI o BindAnno) t ctx
fun TAbsTMany (ctx, t) = foldl (TAbsT o BindAnno) t ctx
                  
fun on_mt (t : S.mtype) =
  case t of
      S.Arrow (t1, i, t2) => TArrow (on_mt t1, i, on_mt t2)
    | S.TyNat (i, _) => TNat i
    | S.TyArray (t, i) => TArr (on_mt t, i)
    | S.Unit _ => TUnit
    | S.Prod (t1, t2) => TProd (on_mt t1, on_mt t2)
    | S.UniI (s, S.Bind (name, t), r) => TQuanI (Forall, BindAnno ((IName name, s), on_mt t))
    | S.MtVar x => TVar x
    | S.MtApp (t1, t2) => TAppT (on_mt t1, on_mt t2)
    | S.MtAbs (k, S.Bind (name, t), _) => TAbsT $ BindAnno ((TName name, on_k k), on_mt t)
    | S.MtAppI (t, i) => TAppI (on_mt t, i)
    | S.MtAbsI (b, S.Bind (name, t), _) => TAbsI $ BindAnno ((IName name, b), on_mt t)
    | S.BaseType (t, r) => TConst (on_base_type t)
    | S.UVar (x, _) =>
    (* exfalso x *)
      raise Impossible "UVar"
    | S.TDatatype (Abs bind, _) =>
      let
        open TypeUtil
        val (dt_name, tbinds) = from_Unbound bind
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
            val extra_sort_name = "__VC"
            val extra_sort = Subset ((BSUnit, dummy), S.Bind ((extra_sort_name, dummy), prop), dummy)
            val t = on_mt t
            val t = TExistsIMany (map (mapFst IName) $ ((extra_sort_name, dummy), extra_sort) :: rev name_sorts, t)
          in
            t
          end
        val len_tnames = length tnames
        val k = KArrowTypes len_tnames $ KArrows bsorts KType
        val ts = map (fn (_, c, _) => on_constr c) constrs
        val t = TSums ts
        fun attach_names namespace f ls = mapi (fn (n, b) => (namespace (f n, dummy), b)) ls
        val t = TAbsIMany (attach_names IName (fn n => "_i" ^ str_int n) $ rev bsorts, t)
        val t = TAbsTMany (attach_names TName (fn n => "_t" ^ str_int n) $ repeat len_tnames KType, t)
      in
        TRec $ BindAnno ((TName dt_name, k), t)
      end

val trans_mt = on_mt
                 
val shift_var = LongIdShift.shiftx_var
    
fun compare_var (m, (y, r)) x =
  case m of
      SOME _ => CmpOther
    | NONE =>
      if y = x then CmpEq
      else if y > x then
        CmpGreater (m, (y - 1, r))
      else CmpOther
    
fun shift_i_t a = shift_i_t_fn (shiftx_i_i, shiftx_i_s) a
fun shift_t_t a = shift_t_t_fn shift_var a
fun subst_t_t a = subst_t_t_fn (compare_var, shift_var, shiftx_i_i, shiftx_i_s) a
fun subst0_t_t a = subst_t_t (IDepth 0, TDepth 0) 0 a
fun subst_i_t a = subst_i_t_fn (substx_i_i, substx_i_s) a
fun subst0_i_t a = subst_i_t 0 0 a
fun normalize_t a = normalize_t_fn (subst0_i_t, subst0_t_t) a
fun shift_i_e a = shift_i_e_fn (shiftx_i_i, shiftx_i_s, shift_i_t) a
fun shift_e_e a = shift_e_e_fn shift_var a
fun subst_e_e a = subst_e_e_fn (compare_var, shift_var, shiftx_i_i, shiftx_i_s, shift_i_t, shift_t_t) a
fun EV n = EVar (NONE, (n, dummy))
                
open PatternEx
fun shift_e_pn a = shift_e_pn_fn shift_e_e a
                                 
fun on_e (e : S.expr) =
  case e of
      S.EVar (x, _) => EVar x
    | S.EConst (c, _) => EConst c
    | S.EUnOp (opr, e, _) => EUnOp (on_expr_un_op opr, on_e e)
    | S.EBinOp (opr, e1, e2) => EBinOp (on_bin_op opr, on_e e1, on_e e2)
    | S.ETriOp (Op.Write, e1, e2, e3) => EWrite (on_e e1, on_e e2, on_e e3)
    | S.EEI (opr, e, i) =>
      (case opr of
           Op.EEIAppI => EAppI (on_e e, i)
         | Op.EEIAscTime => EAscTime (on_e e, i)
      )
    | S.ET (opr, t, r) =>
      (case opr of
           Op.ETNever => ENever (on_mt t)
         | Op.ETBuiltin => raise T2MTError "can't translate builtin expression"
      )
    | S.EAbs bind =>
      let
        val (pn, e) = unBind bind
        val (pn, Outer t) = case pn of S.AnnoP a => a | _ => raise Impossible "must be AnnoP"
        val t = on_mt t
        val e = on_e e
        val pn = from_TiML_ptrn pn
        val name = default (EName ("__x", dummy)) $ get_pn_alias pn
        val pn = PnBind (pn, e)
        val pn = shift_e_pn 0 1 pn
        val e = to_expr (shift_i_e, shift_e_e, subst_e_e, EV) (EV 0) [pn]
      in
        EAbs $ BindAnno ((name, t), e)
      end
    | S.ECase (e, return, rules, r) =>
      let
        val e = on_e e
        val rules = map (mapPair (from_TiML_ptrn, on_e) o unBind) rules
        val name = default (EName ("__x", dummy)) $ firstSuccess get_pn_alias $ map fst rules
        val pns = map PnBind rules
        val pns = map (shift_e_pn 0 1) pns
        val e2 = to_expr (shift_i_e, shift_e_e, subst_e_e, EV) (EV 0) pns
      in
        ELet (e, BindSimp (name, e2))
      end
    | S.EAbsI (bind, _) =>
      let
        val ((name, s), e) = unBindAnno bind
      in
        EAbsI $ BindAnno ((name, s), on_e e)
      end
    (* | Let (return, decs, e, r) => *)
    (*   let  *)
    (*     val (decs, m) = f_decls x n decs *)
    (*   in *)
    (*     Let (return, decs, f (x + m) n e, r) *)
    (*   end *)
    | S.EAsc (e, t) => EAscType (on_e e, on_mt t)
    | S.EAppConstr ((_, eia), ts, is, e, ot) =>
      let
        fun str_var (_, (x, _)) = str_int x
        val pp_t = MicroTiMLPP.pp_t_fn (str_var, str_bs, str_raw_i, str_raw_s, const_fun "<kind>")
        val (pos, t) = ot !! (fn () => raise Impossible "to-micro-timl/AppConstr/ot")
        val dt = case t of TDatatype (Abs dt, _) => dt | _ => raise Impossible "to-micro-timl/AppConstr/TDatatype"
        val () = if eia then () else raise Impossible "to-micro-timl/AppConstr/eia"
        val t_rec = on_mt t
        (* val () = pp_t t_rec *)
        val (name, tbinds) = TypeUtil.from_Unbound dt
        val (tname_kinds, (bsorts, constr_decls)) = unfold_binds tbinds
        val constr_decl as (_, core, _) = nth_error constr_decls pos !! (fn () => raise Impossible "to-micro-timl/AppConstr: nth_error constr_decls")
        val (name_sorts, (_, result_is)) = unfold_binds core
        val () = assert (fn () => length is = length name_sorts) "length is = length name_sorts"
        val result_is = foldl (fn (v, b) => map (subst_i_i v) b) result_is is
        val fold_anno = TAppIs (TAppTs (t_rec, map on_mt ts), result_is)
        fun unroll t_rec =
          let
            fun collect_until_TRec t =
              case t of
                  TAppI (t, i) =>
                  let
                    val (t, args) = collect_until_TRec t
                  in
                    (t, args @ [inl i])
                  end
                | TAppT (t, t') =>
                  let
                    val (t, args) = collect_until_TRec t
                  in
                    (t, args @ [inr t'])
                  end
                | TRec bind =>
                  let
                    val (_, t) = unBindAnno bind
                  in
                    (t, [])
                  end
                | _ => raise Impossible "collect_until_TRec"
            val (t_body, args) = collect_until_TRec t_rec
            val t = subst0_t_t t_rec t_body
            fun TApp (t, arg) =
              case arg of
                  inl i => TAppI (t, i)
                | inr t' => TAppT (t, t')
            val t = foldl (swap TApp) t args
            val t = normalize_t t
          in
            t
          end
        val unrolled = unroll fold_anno
        (* val () = pp_t unrolled *)
        val inj_anno = unTSums unrolled
        (* val () = println $ sprintf "$, $" [str_int $ length inj_anno, str_int pos] *)
        val pack_anno = nth_error inj_anno pos !! (fn () => raise Impossible $ sprintf "to-micro-timl/AppConstr: nth_error inj_anno: $, $" [str_int $ length inj_anno, str_int pos])
        (* val exists = peel_exists (length is + 1) pack_anno *)
        val is = is @ [TTI dummy]
        val e = on_e e
        val e = EPackIs (pack_anno, is, e)
        val e = EInj (inj_anno, pos, e)
        val e = EFold (fold_anno, e)
      in
        e
      end
    | _ => raise Unimpl ""

val trans_e = on_e

structure UnitTest = struct

structure U = UnderscoredExpr
                
(* val trans_long_id = id *)
(* structure IdxTrans = IdxTransFn (structure Src = U *)
(*                                  structure Tgt = Idx *)
(*                                  val on_base_sort = id *)
(*                                  val on_var = trans_long_id *)
(*                                  val on_name = id *)
(*                                  val on_r = id *)
(*                                  fun on_exists_anno _ _ = () *)
(*                                  fun on_uvar_bs _ _ = raise Impossible "IdxTrans/on_uvar_bs()" *)
(*                                  fun on_uvar_s _ _ _ = raise Impossible "IdxTrans/on_uvar_s()" *)
(*                                  fun on_uvar_i _ _ _ = raise Impossible "IdxTrans/on_uvar_i()" *)
(*                                 ) *)
(* structure TypeTrans = TypeTransFn (structure Src = U *)
(*                                    structure Tgt = TiMLType *)
(*                                    structure IdxTrans = IdxTrans *)
(*                                    val on_base_type = id *)
(*                                    fun on_k k = mapSnd (map IdxTrans.on_b) k *)
(*                                    fun on_uvar_mt _ _ _ _ = raise Impossible "TypeTrans/on_uvar_mt()" *)
(*                                   ) *)

(* val SNat = Basic (Base Nat, ()) *)
(* val nil = fold_ibinds ([], (S.Unit (), [N0])) *)
(* val cons = fold_ibinds ([("n", SNat)], (S.Prod (), [V0 %+ N1])) *)
(* val src = TDatatype (, ()) *)

fun test filename =
  let
    open Parser
    val prog = parse_file filename
    open Elaborate
    val prog = elaborate_prog prog
    open NameResolve
    val (prog, _, _) = resolve_prog empty prog
    val decls = case hd prog of
                    (_, TopModBind (ModComponents (decls, _))) => decls
                  | _ => raise Impossible ""
    open TypeCheck
    val ((decls, _, _, _), _) = typecheck_decls empty empty_ctx decls
    val dt = case hd decls of
                 DTypeDef (_, Outer (TDatatype (Abs dt, _))) => dt
               | _ => raise Impossible ""
    val bind = case nth (decls, 1) of
                   DVal (_, Outer bind, _) => bind
                 | _ => raise Impossible ""
    val (_, e) = unBind bind
    (* val dt = TypeTrans.on_dt dt *)
    val t_list = TiML.TDatatype (Abs dt, dummy)
    val t = trans_mt t_list
    (* val () = println $ str_e empty ([], ["'a", "list"], ["Cons", "Nil"], []) e *)
    val BSNat = Base Nat
    val e = SimpExpr.simp_e [("'a", KeKind Type), ("list", KeKind (1, [BSNat]))] e
    val () = println $ str_e empty ([], ["'a", "list"], ["Cons", "Nil"], []) e
    val () = println ""
    (* fun visit_subst_t_pn a = PatternVisitor.visit_subst_t_pn_fn (use_idepth_tdepth substx_t_mt) a *)
    fun subst_t_e a = SubstTE.subst_t_e_fn (use_idepth_tdepth substx_t_mt) a
    val e = subst_t_e (IDepth 0, TDepth 1) 1 t_list e
    val e = trans_e e
    fun short_to_long_id x = (NONE, (x, dummy))
    fun visit_var (_, _, tctx) (_, (x, _)) = short_to_long_id $ nth_error (map Name2str tctx) x !! (fn () => "__unbound_" ^ str_int x)
    val export = export_fn (visit_var, return2, return2, return2)
    val e = export ([], [], []) e
    fun str_var (_, (x, _)) = (* str_int  *)x
    val pp_e = MicroTiMLExPP.pp_e_fn (str_var, str_raw_i, str_raw_s, const_fun "<kind>", const_fun "<ty>")
    val () = pp_e e
  in
    ((* t, e *))
  end
  (* handle NameResolve.Error (_, msg) => (println $ "NR.Error: " ^ msg; raise Impossible "End") *)
  (*      | TypeCheck.Error (_, msgs) => (app println $ "TC.Error: " :: msgs; raise Impossible "End") *)
  (*      | T2MTError msg => (println $ "T2MT.Error: " ^ msg; raise Impossible "End") *)
  (*      | Impossible msg => (println $ "Impossible: " ^ msg; raise Impossible "End") *)
                          
end
                             
end
