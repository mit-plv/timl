structure PreTypeCheck = struct
structure U = UnderscoredExpr
open Region
open Expr
open Simp
       
infixr 0 $

infix 9 %@
infix 8 %^
infix 7 %*
infix 6 %+ 
infix 4 %<=
infix 4 %>=
infix 4 %=
infixr 3 /\
infixr 2 \/
infixr 1 -->
infix 1 <->
        
open Subst

val is_builtin_enabled = ref false
fun turn_on_builtin () = (is_builtin_enabled := true)
fun turn_off_builtin () = (is_builtin_enabled := false)
                            
fun idx_un_op_type opr =
  case opr of
      ToReal => (Nat, Time)
    | Log2 => (Time, Time)
    | Ceil => (Time, Nat)
    | Floor => (Time, Nat)
    | B2n => (BoolSort, Nat)
    | Neg => (BoolSort, BoolSort)

fun idx_bin_op_type opr =
  case opr of
      AndI => (BoolSort, BoolSort, BoolSort)
    | ExpNI => (Nat, Nat, Nat)
    | MaxI => raise Impossible "idx_bin_op_type ()"
    | MinI => raise Impossible "idx_bin_op_type ()"
    | IApp => raise Impossible "idx_bin_op_type ()"
    | EqI => raise Impossible "idx_bin_op_type ()"
    | LtI => raise Impossible "idx_bin_op_type ()"
    | GeI => raise Impossible "idx_bin_op_type ()"
    | AddI => raise Impossible "idx_bin_op_type ()"
    | MultI => raise Impossible "idx_bin_op_type ()"
    | BoundedMinusI => raise Impossible "idx_bin_op_type ()"

(* a special kind of substitution, where a variable y such that y >= x will be replaced with m.(y-x) *)
(* This is used for packagin things in the top-level context into a module *)
fun package_long_id x m (long_id as (m', (y, r))) =
  case m' of
      NONE =>
      if y >= x then
        (SOME m, (y - x, r))
      else
        long_id
    | SOME _ =>
      (* if it has module reference, don't substitute *)
      long_id
        
fun package_i_ibind f x v (Bind (name, inner) : ('a * 'b) ibind) =
  Bind (name, f (x + 1) v inner)

fun package_i_tbind f x v (Bind (name, inner)) =
  Bind (name, f x v inner)

local
  fun f x v b =
    case b of
	VarI y => VarI $ package_long_id x v y
      | ConstIN n => ConstIN n
      | ConstIT x => ConstIT x
      | UnOpI (opr, i, r) => UnOpI (opr, f x v i, r)
      | DivI (i1, n2) => DivI (f x v i1, n2)
      | ExpI (i1, n2) => ExpI (f x v i1, n2)
      | BinOpI (opr, d1, d2) => BinOpI (opr, f x v d1, f x v d2)
      | Ite (i1, i2, i3, r) => Ite (f x v i1, f x v i2, f x v i3, r)
      | TrueI r => TrueI r
      | FalseI r => FalseI r
      | TTI r => TTI r
      | IAbs (b, bind, r) => IAbs (b, package_i_ibind f x v bind, r)
      | AdmitI r => AdmitI r
      | UVarI a => b
in
fun package_i_i x v (b : idx) : idx = f x v b
end
fun package0_i v = package_i_i 0 v

local
  fun f x v b =
    case b of
	True r => True r
      | False r => False r
      | Not (p, r) => Not (f x v p, r)
      | BinConn (opr,p1, p2) => BinConn (opr, f x v p1, f x v p2)
      | BinPred (opr, d1, d2) => BinPred (opr, package_i_i x v d1, package_i_i x v d2)
      | Quan (q, bs, bind, r) => Quan (q, bs, package_i_ibind f x v bind, r)
in
fun package_i_p x v b = f x v b
end

fun SortBigO_to_Subset (bs, i, r) =
  Subset (bs, Bind (("__f", r), BinPred (BigO, VarI (NONE, (0, r)), shift_i_i i)), r)

local
  fun f x v b =
    case b of
	Basic s => Basic s
      | Subset (s, bind, r) => Subset (s, package_i_ibind package_i_p x v bind, r)
      | UVarS a => b
      | SortBigO s => f x v (SortBigO_to_Subset s)
      | SAbs (s1, bind, r) => SAbs (f x v s1, package_i_ibind f x v bind, r)
      | SApp (s, i) => SApp (f x v s, package_i_i x v i)
in
fun package_i_s x v (b : sort) : sort = f x v b
end
fun package0_s v = package_i_s 0 v

fun package_i_k x v k = mapSnd (map (package_i_s x v)) k

local
  fun f x v b =
    case b of
	Arrow (t1, d, t2) => Arrow (f x v t1, package_i_i x v d, f x v t2)
      | TyArray (t, i) => TyArray (f x v t, package_i_i x v i)
      | TyNat (i, r) => TyNat (package_i_i x v i, r)
      | Unit r => Unit r
      | Prod (t1, t2) => Prod (f x v t1, f x v t2)
      | UniI (s, bind, r) => UniI (package_i_s x v s, package_i_ibind f x v bind, r)
      | AppV (y, ts, is, r) => AppV (y, map (f x v) ts, map (package_i_i x v) is, r)
      | MtVar y => MtVar y
      | MtAbs (k, bind, r) => MtAbs (package_i_k x v k, package_i_tbind f x v bind, r)
      | MtApp (t1, t2) => MtApp (f x v t1, f x v t2)
      | MtAbsI (s, bind, r) => MtAbsI (package_i_s x v s, package_i_ibind f x v bind, r)
      | MtAppI (t, i) => MtAppI (f x v t, package_i_i x v i)
      | BaseType a => BaseType a
      | UVar a => b
in
fun package_i_mt x v (b : mtype) : mtype = f x v b
end

local
  fun f x v b =
    case b of
	Mono t => Mono (package_i_mt x v t)
      | Uni (bind, r) => Uni (package_i_tbind f x v bind, r)
in
fun package_i_t x v (b : ty) : ty = f x v b
end

fun package_t_ibind f x v (Bind (name, inner) : ('a * 'b) ibind) =
  Bind (name, f x v inner)

fun package_t_tbind f x v (Bind (name, inner) : ('a * 'b) tbind) =
  Bind (name, f (x + 1) v inner)

local
  fun f x v (b : mtype) : mtype =
    case b of
	Arrow (t1, d, t2) => Arrow (f x v t1, d, f x v t2)
      | TyArray (t, i) => TyArray (f x v t, i)
      | TyNat (i, r) => TyNat (i, r)
      | Unit r => Unit r
      | Prod (t1, t2) => Prod (f x v t1, f x v t2)
      | UniI (s, bind, r) => UniI (s, package_t_ibind f x v bind, r)
      | AppV (y, ts, is, r) =>
        AppV (package_long_id x v y, map (f x v) ts, is, r)
      | MtVar y => MtVar $ package_long_id x v y
      | MtAbs (k, bind, r) => MtAbs (k, package_t_tbind f x v bind, r)
      | MtApp (t1, t2) => MtApp (f x v t1, f x v t2)
      | MtAbsI (s, bind, r) => MtAbsI (s, package_t_ibind f x v bind, r)
      | MtAppI (t, i) => MtAppI (f x v t, i)
      | BaseType a => BaseType a
      | UVar a => b
in
fun package_t_mt x v (b : mtype) : mtype = f x v b
end
fun package0_mt v b = package_t_mt 0 v $ package_i_mt 0 v b

fun package_t_t x v (b : ty) : ty =
  case b of
      Mono t => Mono (package_t_mt x v t)
    | Uni (bind, r) => Uni (package_t_tbind package_t_t x v bind, r)
fun package0_t v b = package_t_t 0 v $ package_i_t 0 v b

fun package_i_kind x v b = mapSnd (map (package_i_s x v)) b
                                  
fun package0_kind v = package_i_kind 0 v
                                     
fun package_i_ibinds f_cls f_inner x v ibinds =
  let
    val package_i_ibinds = package_i_ibinds f_cls f_inner
  in
    case ibinds of
        BindNil inner => BindNil $ f_inner x v inner
      | BindCons (cls, bind) => BindCons (f_cls x v cls, package_i_ibind package_i_ibinds x v bind)
  end
    
fun package_t_ibinds f_cls f_inner x v ibinds =
  let
    val package_t_ibinds = package_t_ibinds f_cls f_inner
  in
    case ibinds of
        BindNil inner => BindNil $ f_inner x v inner
      | BindCons (cls, bind) => BindCons (f_cls x v cls, package_t_ibind package_t_ibinds x v bind)
  end
    
fun package_i_c x m (family, tnames, core) =
  let
    fun package_i_body x v (t, is) = (package_i_mt x v t, map (package_i_i x v) is)
    val core = package_i_ibinds package_i_s package_i_body x m core
  in
    (family, tnames, core)
  end

fun package_t_c x m (family, tnames, core) =
  let
    fun package_t_body x v (t, is) = (package_t_mt x v t, is)
    fun package_t_s x v b = b
    val family = package_long_id x m family
    val core = package_t_ibinds package_t_s package_t_body (x + length tnames) m core
  in
    (family, tnames, core)
  end

fun package0_c v b =
  package_t_c 0 v $ package_i_c 0 v b
              
(*                               
fun package_long_id m (m', x) =
    (SOME $ default m m', x)
      
fun package_i m b =
    let
      fun f b =
	  case b of
	      VarI x => VarI $ package_long_id m x
	    | ConstIN n => ConstIN n
	    | ConstIT x => ConstIT x
            | UnOpI (opr, i, r) => UnOpI (opr, f i, r)
            | DivI (i1, n2) => DivI (f i1, n2)
            | ExpI (i1, n2) => ExpI (f i1, n2)
	    | BinOpI (opr, i1, i2) => BinOpI (opr, f i1, f i2)
            | Ite (i1, i2, i3, r) => Ite (f i1, f i2, f i3, r)
	    | TTI r => TTI r
	    | TrueI r => TrueI r
	    | FalseI r => FalseI r
            | IAbs (name, i, r) => IAbs (name, f i, r)
            | AdmitI r => AdmitI r
            | UVarI a => raise ModuleUVar "package_i ()"
    in
      f b
    end

fun package_ibind f m bind =
    case bind of
        Bind (name, inner) => Bind (name, f m inner)

fun package_tbind f m bind =
    case bind of
        Bind (name, inner) => Bind (name, f m inner)

fun package_p m b =
    let
      fun f m b =
          case b of
	      True r => True r
	    | False r => False r
            | Not (p, r) => Not (f m p, r)
	    | BinConn (opr, p1, p2) => BinConn (opr, f m p1, f m p2)
	    | BinPred (opr, d1, d2) => BinPred (opr, package_i m d1, package_i m d2)
            | Quan (q, bs, bind, r) => Quan (q, bs, package_ibind f m bind, r)
    in
      f m b
    end

fun package_s m b =
    let
      fun f m b =
	  case b of
	      Basic s => Basic s
	    | Subset (s, bind, r) => Subset (s, package_ibind package_p m bind, r)
            | UVarS a => raise ModuleUVar "package_s ()"
    in
      f m b
    end

fun package_mt m b =
    let
      fun f m b =
	  case b of
	      Arrow (t1, d, t2) => Arrow (f m t1, package_i m d, f m t2)
            | Unit r => Unit r
	    | Prod (t1, t2) => Prod (f m t1, f m t2)
	    | UniI (s, bind, r) => UniI (package_s m s, package_ibind f m bind, r)
            | MtVar x => MtVar $ package_long_id m x
            (* | MtApp (t1, t2) => MtApp (f m t1, f m t2) *)
            (* | MtAbs (bind, r) => MtAbs (package_tbind f m bind, r) *)
            (* | MtAppI (t, i) => MtAppI (f m t, package_i m i) *)
            (* | MtAbsI (s, bind, r) => MtAbsI (package_s m s, package_ibind f m bind, r) *)
	    | AppV (x, ts, is, r) => AppV (package_long_id m x, map (f m) ts, map (package_i m) is, r)
	    | BaseType a => BaseType a
            | UVar a => raise ModuleUVar "package_mt ()"
    in
      f m b
    end

fun package_t m b =
    let
      fun f m b =
	  case b of
	      Mono t => Mono (package_mt m t)
	    | Uni (bind, r) => Uni (package_tbind f m bind, r)
    in
      f m b
    end

fun package_kind m b =
    case b of
	ArrowK (is_datatype, n, sorts) => ArrowK (is_datatype, n, map (package_s m) sorts)

fun package_c m (family, tnames, core) =
    let
      val family = package_long_id m family
      val (name_sorts, (t, is)) = unfold_binds core
      val t = package_mt m t
      val is = map (package_i m) is
      val name_sorts = map (mapSnd $ package_s m) name_sorts
      val core = fold_binds (name_sorts, (t, is))
    in
      (family, tnames, core)
    end
*)
              
type kind_ext = bool (*is datatype*) * kind * mtype option (*aliasing*)

fun str_ke gctx (ctx as (sctx, kctx)) (dt, k, t) =
  sprintf "($$$)" [str_k gctx sctx k, if dt then " [datatype]" else "", str_opt (fn t => sprintf " (= $)" [str_mt gctx ctx t]) t]
                                 
fun shiftx_i_ke x n (dt, k, t) = (dt, shiftx_i_k x n k, Option.map (shiftx_i_mt x n) t)
                                  
fun shiftx_t_ke x n (dt, k, t) = (dt, k, Option.map (shiftx_t_mt x n) t)
                                  
fun shiftx_m_ke x n (dt, k, t) = (dt, shiftx_m_k x n k, Option.map (shiftx_m_mt x n) t)

fun package_i_ke x v (dt, k, t) = (dt, package_i_kind x v k, Option.map (package_i_mt x v) t)
                                  
fun package_t_ke x v (dt, k, t) = (dt, k, Option.map (package_t_mt x v) t)

fun package0_ke v b =
  package_t_ke 0 v $ package_i_ke 0 v b
               
(* sorting context *)
type scontext = (string (* option *) * sort) list
(* kinding context *)
type kcontext = (string * kind_ext) list 
(* constructor context *)
type ccontext = (string * constr) list
(* typing context *)
type tcontext = (string * ty) list
type context = scontext * kcontext * ccontext * tcontext

(* structure StringOrdKey = struct *)
(* type ord_key = string *)
(* val compare = String.compare *)
(* end *)
(* structure StringBinaryMap = BinaryMapFn (structure Key = StringOrdKey) *)
(* structure M = StringBinaryMap *)
                                                  
(* another representation of signature, as contexts *)
datatype sgntr =
         (* module signaturing *)
         Sig of (* sigcontext *  *)context
         (* signature aliases *)
         (* | SigBind of string * sgntr *)
         | FunctorBind of (string * context) (* list *) * context
(* signaturing context *)
(* withtype sigcontext = (string * sgntr) list *)
(* withtype sigcontext = unit *)

type sigcontext = (string * sgntr) list
                                   
fun names ctx = map fst ctx

fun shiftx_i_ps n ps = 
  map (shiftx_i_p 0 n) ps
fun shiftx_i_kctx n ctx = 
  map (mapSnd (shiftx_i_ke 0 n)) ctx
fun shiftx_i_cs n ctx = 
  map (mapSnd (shiftx_i_c 0 n)) ctx
fun shiftx_t_cs n ctx = 
  map (mapSnd (shiftx_t_c 0 n)) ctx
fun shiftx_i_ts n ctx = 
  map (mapSnd (shiftx_i_t 0 n)) ctx
      
fun shiftx_t_ts n ctx = 
  map (mapSnd (shiftx_t_t 0 n)) ctx

fun shiftx_snd f x n (a, b) = (a, f x n b)
fun shiftx_list_snd f x n ls = map (mapSnd (f x n)) ls
                                   
fun shiftx_m_ctx x n (sctx, kctx, cctx, tctx) : context =
  (shiftx_list_snd shiftx_m_s x n sctx,
   shiftx_list_snd shiftx_m_ke x n kctx,
   shiftx_list_snd shiftx_m_c x n cctx,
   shiftx_list_snd shiftx_m_t x n tctx
  )

fun pacakge_is_mt vs b =
  fst (foldl (fn (v, (b, x)) => (package_i_mt x v b, x - 1)) (b, length vs - 1) vs)
fun package_ts_mt vs b =
  fst (foldl (fn (v, (b, x)) => (package_t_mt x v b, x - 1)) (b, length vs - 1) vs)
      
fun package0_ctx m (sctx, kctx, cctx, tctx) =
  let
    val sctx = foldrWithIdx 0 (fn ((name, s), acc, x) => (name, package_i_s x m s) :: acc) [] sctx
    val sctx_len = length sctx
    val kctx = foldrWithIdx 0 (fn ((name, k), acc, x) => (name, package_i_ke sctx_len m $ package_t_ke x m k) :: acc) [] kctx
    val kctx_len = length kctx
    val cctx = map (fn (name, c) => (name, package_t_c kctx_len m $ package_i_c sctx_len m c)) cctx
    val tctx = map (fn (name, t) => (name, package_t_t kctx_len m $ package_i_t sctx_len m t)) tctx
  in
    (sctx, kctx, cctx, tctx)
  end
    
fun shiftx_m_sigs x n sigs =
  foldrWithIdx x (fn (sg, acc, x) => shiftx_snd shiftx_m_ctx x n sg :: acc) [] sigs

fun add_sorting (name, s) pairs = (name, s) :: pairs
fun add_sorting_sk pair (sctx, kctx) = 
  (add_sorting pair sctx, 
   shiftx_i_kctx 1 kctx)
fun add_sorting_skc pair (sctx, kctx, cctx) = 
  (add_sorting pair sctx, 
   shiftx_i_kctx 1 kctx,
   shiftx_i_cs 1 cctx)
fun add_sorting_skct pair (sctx, kctx, cctx, tctx) = 
  (add_sorting pair sctx, 
   shiftx_i_kctx 1 kctx, 
   shiftx_i_cs 1 cctx, 
   shiftx_i_ts 1 tctx)
(* Within 'pairs', sort depends on previous sort *)
fun add_sortings_skct pairs' (pairs, kctx, cctx, tctx) : context = 
  let
    val n = length pairs' 
  in
    ((* map (mapFst SOME) *) pairs' @ pairs, 
     shiftx_i_kctx n kctx, 
     shiftx_i_cs n cctx, 
     shiftx_i_ts n tctx)
  end
(*      
(* Within 'pairs', sort doesn't depend on previous sort. All of them point to 'sctx'. So the front elements of 'pairs' must be shifted to skip 'pairs' and point to 'sctx' *)
fun add_nondep_sortings pairs sctx = 
    #1 (foldr (fn ((name, s), (ctx, n)) => (add_sorting (name, (shiftx_i_s 0 n s)) ctx, n + 1)) (sctx, 0) pairs)
fun add_nondep_sortings_sk pairs (sctx, kctx) = 
    let val n = length pairs
    in
      (add_nondep_sortings pairs sctx,
       shiftx_i_kctx n kctx)
    end
fun add_nondep_sortings_skc pairs (sctx, kctx, cctx) = 
    let val n = length pairs
    in
      (add_nondep_sortings pairs sctx,
       shiftx_i_kctx n kctx,
       shiftx_i_kctx n cctx)
    end
*)
fun sctx_names (ctx : scontext) = (* List.mapPartial id $ *) map fst ctx
fun sctx_length (ctx : scontext) = length $ sctx_names ctx

fun KeKind k = (false, k, NONE)
fun KeTypeEq (k, t) = (false, k, SOME t)

fun add_kindingext pair (kctx : kcontext) = pair :: kctx
fun add_kinding pair = add_kindingext $ mapSnd KeKind pair
fun add_type_eq pair = add_kindingext $ mapSnd KeTypeEq pair
fun add_kinding_kc pair (kctx, cctx) = 
  (add_kinding pair kctx, 
   shiftx_t_cs 1 cctx)
fun add_kinding_kct pair (kctx, cctx, tctx) = 
  (add_kinding pair kctx,
   shiftx_t_cs 1 cctx,
   shiftx_t_ts 1 tctx)
fun add_kindingext_skct pair (sctx, kctx, cctx, tctx) = 
  (sctx,
   add_kindingext pair kctx,
   shiftx_t_cs 1 cctx,
   shiftx_t_ts 1 tctx)
fun add_kinding_skct pair = add_kindingext_skct $ mapSnd KeKind pair
fun add_type_eq_skct pair = add_kindingext_skct $ mapSnd KeTypeEq pair
fun add_kinding_sk pair (sctx, kctx) = 
  (sctx, 
   add_kinding pair kctx)
fun add_kindingexts_skct pairs (sctx, kctx, cctx, tctx) =
  let val n = length pairs in
    (sctx,
     pairs @ kctx,
     shiftx_t_cs n cctx,
     shiftx_t_ts n tctx)
  end

fun add_kindings_skct pairs =
  add_kindingexts_skct $ map (mapSnd KeKind) pairs

fun add_constrs_skct pairs (sctx, kctx, cctx, tctx) = 
  (sctx, 
   kctx, 
   pairs @ cctx,
   tctx)

fun add_typing pair tctx = pair :: tctx
fun add_typing_skct pair ((sctx, kctx, cctx, tctx) : context) : context = 
  (sctx, 
   kctx, 
   cctx,
   add_typing pair tctx)
fun add_typings_skct pairs (sctx, kctx, cctx, tctx) = 
  (sctx, 
   kctx, 
   cctx,
   pairs @ tctx)

fun add_sigging (name, s) pairs = (name, Sig s) :: pairs
                                                     
fun ctx_names (sctx, kctx, cctx, tctx) =
  (sctx_names sctx, names kctx, names cctx, names tctx) 

fun add_ctx (sctx, kctx, cctx, tctx) ctx =
  let val ctx = add_sortings_skct sctx ctx
      val ctx = add_kindingexts_skct kctx ctx
      val ctx = add_constrs_skct cctx ctx
      val ctx = add_typings_skct tctx ctx
  in
    ctx
  end

fun add_ctx_skc ctx (sctx, kctx, cctx) =
  let val (sctx, kctx, cctx, _) = add_ctx ctx (sctx, kctx, cctx, []) in
    (sctx, kctx, cctx)
  end

fun shift_ctx_i (sctx, _, _, _) i =
  shiftx_i_i 0 (sctx_length sctx) i

fun shift_ctx_mt (sctx, kctx, _, _) t =
  (shiftx_t_mt 0 (length kctx) o shiftx_i_mt 0 (sctx_length sctx)) t

val empty_ctx = ([], [], [], [])
fun ctx_from_sorting pair : context = (add_sorting pair [], [], [], [])
fun ctx_from_sortings pairs : context = add_sortings_skct pairs empty_ctx
fun ctx_from_full_sortings pairs : context = (pairs, [], [], [])
fun ctx_from_kindingext pair : context = add_kindingext_skct pair empty_ctx
fun ctx_from_kinding pair : context = add_kinding_skct pair empty_ctx
fun ctx_from_typing pair : context = ([], [], [], [pair])

open UVar
       
fun update_bs bs =
  case bs of
      UVarBS x =>
      (case !x of
           Refined bs => 
           let 
             val bs = update_bs bs
             val () = x := Refined bs
           in
             bs
           end
         | Fresh _ => bs
      )
    | BSArrow (a, b) => BSArrow (update_bs a, update_bs b)
    | Base _ => bs

fun load_uvar update origin x = 
  case !x of
      Refined a => 
      let 
        val a = update a
        val () = x := Refined a
      in
        a
      end
    | Fresh _ => origin
                   
fun update_i i =
  case i of
      UVarI (x, r) => load_uvar update_i i x
    | UnOpI (opr, i, r) => UnOpI (opr, update_i i, r)
    | DivI (i1, n2) => DivI (update_i i1, n2)
    | ExpI (i1, n2) => ExpI (update_i i1, n2)
    | BinOpI (opr, i1, i2) => BinOpI (opr, update_i i1, update_i i2)
    | Ite (i1, i2, i3, r) => Ite (update_i i1, update_i i2, update_i i3, r)
    | VarI _ => i
    | ConstIN _ => i
    | ConstIT _ => i
    | TTI _ => i
    | TrueI _ => i
    | FalseI _ => i
    | AdmitI _ => i
    | IAbs (b, Bind (name, i), r) => IAbs (update_bs b, Bind (name, update_i i), r)

fun update_p p =
  case p of
      Quan (q, bs, Bind (name, p), r) => Quan (q, update_bs bs, Bind (name, update_p p), r)
    | BinConn (opr, p1, p2) => BinConn (opr, update_p p1, update_p p2)
    | BinPred (opr, i1, i2) => BinPred (opr, update_i i1, update_i i2)
    | Not (p, r) => Not (update_p p, r)
    | True _ => p
    | False _ => p

fun update_s s =
  case s of
      UVarS (x, r) => load_uvar update_s s x
    | Basic _ => s
    | Subset ((b, r1), Bind (name, p), r) => Subset ((update_bs b, r1), Bind (name, update_p p), r)
    | SortBigO ((b, r1), i, r) => SortBigO ((update_bs b, r1), update_i i, r)
    | SAbs (s1, Bind (name, s), r) => SAbs (update_s s1, Bind (name, update_s s), r)
    | SApp (s, i) => SApp (update_s s, update_i i)

exception Error of region * string list

(* fetching from context *)
                                   
fun lookup_sort (n : int) (ctx : scontext) : sort option =
  case nth_error ctx n of
      NONE => NONE
    | SOME (_, s) => 
      SOME (shiftx_i_s 0 (n + 1) s)

fun lookup_sort_by_name (ctx : scontext) (name : string) =
  case find_idx_value name ctx of
      NONE => NONE
    | SOME (n, s) => 
      SOME (n, shiftx_i_s 0 (n + 1) s)

fun lookup_kindext (n : int) kctx = 
  case nth_error kctx n of
      NONE => NONE
    | SOME (_, k) => SOME $ shiftx_t_ke 0 (n + 1) k

fun lookup_kindext_by_name kctx name = 
  case find_idx_value name kctx of
      NONE => NONE
    | SOME (n, k) => SOME (n, shiftx_t_ke 0 (n + 1) k)

fun get_ke_kind (_, k, _) = k
                           
fun lookup_kind (n : int) kctx = 
  case nth_error kctx n of
      NONE => NONE
    | SOME (_, k) => SOME $ get_ke_kind k
                          
fun lookup_snd n ctx =
  Option.map snd $ nth_error ctx n
             
val lookup_constr = lookup_snd
val lookup_type = lookup_snd

val get_outmost_module = id

fun filter_module gctx = List.mapPartial (fn (name, sg) => case sg of Sig sg => SOME (name, sg) | _ => NONE) gctx
                                         
fun gctx_names (gctx : sigcontext) =
  let
    val gctx = filter_module gctx
    val gctx = map (mapSnd ctx_names) gctx
  in
    gctx
  end
    
fun lookup_module gctx m =
  Option.map snd $ nth_error (filter_module gctx) m

fun fetch_module gctx (m, r) =
  case lookup_module gctx m of
      SOME sg => sg
    | NONE => raise Error (r, ["Unbounded module"])
                    
fun fetch_from_module (params as (shift, package, do_fetch)) (* sigs *) gctx ((m, mr), x) =
  let
    (* val fetch_from_module = fetch_from_module params (* sigs *) *)
    (* fun fetch_from_module_or_ctx gctx ctx (m, x) = *)
    (*     case m of *)
    (*         NONE => do_fetch (ctx, x) *)
    (*       | SOME m => fetch_from_module gctx (m, x) *)
    (* val ((m, r), x) = get_outmost_module (m, x) *)
    val ((* gctx,  *)ctx) = fetch_module gctx (m, mr)
    (* val v = fetch_from_module_or_ctx gctx ctx x *)
    val v = do_fetch (ctx, x)
    (* val v = package 0 (length gctx) v *)
    val v = shift 0 (m + 1) v
    val v = package (m, mr) v
  in
    v
  end
    
fun add_error_msg (r, old_msg) new_msg =
  (r, new_msg @ ["Cause:"] @ indent old_msg)
    
fun generic_fetch shift package do_fetch sel (ggctx as ((* sigs,  *)gctx : sigcontext)) (fctx, (m, x)) =
  case m of
      NONE => do_fetch (fctx, x)
    | SOME m => fetch_from_module (shift, package, do_fetch o mapFst sel) (* sigs *) gctx (m, x)

fun do_fetch_sort (ctx, (x, r)) =
  case lookup_sort x ctx of
      SOME s => s
    | NONE => raise Error (r, ["Unbound index variable: " ^ str_v (sctx_names ctx) x])

fun fetch_sort a = generic_fetch shiftx_m_s package0_s do_fetch_sort #1 a
                                 
fun do_fetch_sort_by_name (ctx, (name, r)) =
  case lookup_sort_by_name ctx name of
      SOME (i, s) => ((i, r), s)
    | NONE => raise Error (r, [sprintf "Can't find index variable '$' in context $" [name, str_ls fst ctx]])

fun package0_snd f m (a, b) = (a, f m b)
fun package0_list f m ls = map (f m) ls
                               
fun fetch_sort_by_name gctx ctx (m, name) =
  let
    val (x, s) = generic_fetch (shiftx_snd shiftx_m_s) (package0_snd package0_s) do_fetch_sort_by_name #1 gctx (ctx, (m, name))
  in
    ((m, x), s)
  end
    
fun do_fetch_kindext (kctx, (a, r)) =
  case lookup_kindext a kctx of
      SOME k => k
    | NONE => raise Error (r, [sprintf "Unbound type variable $ in context $" [str_v (names kctx) a, str_ls id $ names kctx]])

fun fetch_kindext gctx (kctx, x) =
  generic_fetch shiftx_m_ke package0_ke do_fetch_kindext #2 gctx (kctx, x)
  handle Error e => raise Error $ add_error_msg e [sprintf "Unbound name '$' in context $ $" [str_long_id #2 (gctx_names gctx) (names kctx) x, str_ls fst kctx, str_ls fst gctx ]]

(* fun do_fetch_kind (kctx, (a, r)) = *)
(*     case lookup_kind a kctx of *)
(*       	SOME k => k *)
(*       | NONE => raise Error (r, [sprintf "Unbound type variable $ in context $" [str_v (names kctx) a, str_ls id $ names kctx]]) *)

(* fun fetch_kind a = generic_fetch shiftx_m_k package0_kind do_fetch_kind #2 a *)
fun fetch_kind gctx (kctx, x) = get_ke_kind $ fetch_kindext gctx (kctx, x)
fun fetch_kind_and_is_datatype gctx (kctx, x) =
  let
    val (dt, (n, sorts), _) = fetch_kindext gctx (kctx, x)
  in
    (dt, n, sorts)
  end

fun do_fetch_kindext_by_name (kctx, (name, r)) =
  case lookup_kindext_by_name kctx name of
      SOME (i, k) => ((i, r), k)
    | NONE => raise Error (r, ["Can't find type variable: " ^ name])

fun fetch_kindext_by_name gctx ctx (m, name) =
  let
    val (x, k) = generic_fetch (shiftx_snd shiftx_m_ke) (package0_snd package0_ke) do_fetch_kindext_by_name #2 gctx (ctx, (m, name))
  in
    ((m, x), k)
  end
    
fun do_fetch_constr (ctx, (x, r)) =
  case lookup_constr x ctx of
      SOME c => c
    | NONE => raise Error (r, [sprintf "Unbound constructor $ in context $" [str_v (names ctx) x, str_ls fst ctx]])

fun fetch_constr a = generic_fetch shiftx_m_c package0_c do_fetch_constr #3 a
                                   
fun fetch_constr_type gctx (ctx : ccontext, x) =
  constr_type VarT shiftx_long_id $ fetch_constr gctx (ctx, x)

fun do_fetch_constr_by_name (ctx, (name, r)) =
  case find_idx_value name ctx of
      SOME (i, c) => ((i, r), c)
    | NONE => raise Error (r, ["Can't find constructor: " ^ name])

fun fetch_constr_by_name gctx ctx (m, name) =
  let
    val (x, c) = generic_fetch (shiftx_snd shiftx_m_c) (package0_snd package0_c) do_fetch_constr_by_name #3 gctx (ctx, (m, name))
  in
    ((m, x), c)
  end
    
fun fetch_constr_type_by_name gctx ctx name =
  mapSnd (constr_type VarT shiftx_long_id) $ fetch_constr_by_name gctx ctx name

fun do_fetch_type (tctx, (x, r)) =
  case lookup_type x tctx of
      SOME t => t
    | NONE => raise Error (r, ["Unbound variable: " ^ str_v (names tctx) x])

fun fetch_type a = generic_fetch shiftx_m_t package0_t do_fetch_type #4 a

fun do_fetch_type_by_name (ctx, (name, r)) =
  case find_idx_value name ctx of
      SOME (i, t) => ((i, r), t)
    | NONE => raise Error (r, ["Can't find variable: " ^ name])

fun fetch_type_by_name gctx ctx (m, name) =
  let
    val (x, t) = generic_fetch (shiftx_snd shiftx_m_t) (package0_snd package0_t) do_fetch_type_by_name #4 gctx (ctx, (m, name))
  in
    ((m, x), t)
  end
    
fun try_retrieve_MtVar f gctx kctx x =
  let
    val k = fetch_kindext gctx (kctx, x)
  in
    default (MtVar x) $ Option.map f (#3 k)
  end

fun is_type_variable r y =
  (* ToDo: can do better *)
  case y of
      AppV (x, [], [], _) => x
    (* | MtVar x => x *)
    | _ => raise Error (r, ["Head of type operator application must be a datatype name"])
                 
fun eval_AppV y (ts, is, r) =
  if null ts andalso null is then
    y
  else
    AppV (is_type_variable r y, ts, is, r)
         
fun load_without_update_uvar f (a as (x, r)) =
  case !x of
      Refined t => f t
    | Fresh _ => UVar a

fun update_k k = mapSnd (map update_s) k
                      
fun update_mt t =
  case t of
      UVar (x, r) => load_uvar update_mt t x
    | Unit r => Unit r
    | Arrow (t1, d, t2) => Arrow (update_mt t1, update_i d, update_mt t2)
    | TyArray (t, i) => TyArray (update_mt t, update_i i)
    | TyNat (i, r) => TyNat (update_i i, r)
    | Prod (t1, t2) => Prod (update_mt t1, update_mt t2)
    | UniI (s, Bind (name, t1), r) => UniI (update_s s, Bind (name, update_mt t1), r)
    | MtVar x => MtVar x
    | MtAbs (k, Bind (name, t), r) => MtAbs (update_k k, Bind (name, update_mt t), r)
    | MtApp (t1, t2) => MtApp (update_mt t1, update_mt t2)
    | MtAbsI (s, Bind (name, t), r) => MtAbsI (update_s s, Bind (name, update_mt t), r)
    | MtAppI (t, i) => MtAppI (update_mt t, update_i i)
    | AppV (y, ts, is, r) => AppV (y, map update_mt ts, map update_i is, r)
    | BaseType a => BaseType a

(* verification conditions written incrementally during typechecking *)
                                     
(* type anchor = (bsort, idx) uvar_ref_i *)

datatype 'sort forall_type =
         FtSorting of 'sort
         | FtModule of scontext
                         
datatype vc_entry =
         VcForall of string * sort forall_type
         | ImplyVC of prop
         | PropVC of prop * region
         | AdmitVC of prop * region
         (* remember where unification index variable is introduced, since those left over will be converted into existential variables in VC formulas *)
         (* | AnchorVC of anchor *)
         | OpenParen
         | CloseParen

fun VcSorting (name, s) = VcForall (name, FtSorting s)
fun VcModule (name, m) = VcForall (name, FtModule m)
                                  
val acc = ref ([] : vc_entry list)

fun write x = push_ref acc x

fun open_paren () = write OpenParen
fun open_sorting ns = write $ VcSorting ns
fun open_module (name, ctx : context) = write $ VcModule (name, #1 ctx)
                                              
fun close_paren () = write CloseParen
fun close_n n = repeat_app close_paren n
fun open_premises ps = app write $ map ImplyVC ps
fun open_sortings sortings = app open_sorting $ rev sortings
fun open_ctx (ctx as (sctx, kctx, _, _)) =
  let
    val () = open_sortings sctx
  in
    ()
  end
fun close_ctx (ctx as (sctx, _, _, _)) = close_n $ length sctx

(* fun write_anchor anchor = write (AnchorVC anchor) *)

fun write_prop (p, r) =
  let
    (* val () = println $ "Writing Prop: " ^ str_p [] p *)
  in
    write (PropVC (p, r))
  end

fun write_admit (p, r) =
  write (AdmitVC (p, r))

fun write_le (d : idx, d' : idx, r) =
  write_prop (d %<= d', r)
	     
fun check_length_n r (ls, n) =
  if length ls = n then
    ()
  else
    raise Error (r, ["List length mismatch"])

fun check_length r (a, b) =
  if length a = length b then
    ()
  else
    raise Error (r, ["List length mismatch"])

fun check_eq r eq (a, b) =
  if eq (a, b) then
    ()
  else
    raise Error (r, ["Check equality fails"])

fun open_and add ns ctx =
  let
    val () = open_sorting ns
  in
    add ns ctx
  end

fun open_close add ns ctx f =
  let
    val ctx = open_and add ns ctx
    val ret = f ctx
    val () = close_n 1
  in
    ret
  end

(* unification *)
    
fun unify_error r (s, s') =             
  Error (r, ["Can't unify"] @ indent [s] @ ["and"] @ indent [s'])

(* assumes arguments are already checked for well-formedness *)
fun unify_bs r (bs, bs') =
  case (update_bs bs, update_bs bs') of
      (UVarBS x, _) =>
      refine x bs'
    | (_, UVarBS _) =>
      unify_bs r (bs', bs)
    | (BSArrow (a, b), BSArrow (a', b')) => (unify_bs r (a, a'); unify_bs r (b, b'))
    | (Base b, Base b') =>
      if b = b' then
	()
      else
	raise Error (r, [sprintf "Base sort mismatch: $ and $" [str_b b, str_b b']])
    | _ => raise unify_error r (str_bs bs, str_bs bs')
	         
fun whnf_i i =
  case i of
      UVarI (x, r) => load_uvar whnf_i i x
    | BinOpI (opr, i1, i2) =>
      let
        val i1 = whnf_i i1
        val i2 = whnf_i i2
      in
        case (opr, i1) of
            (IApp, IAbs (_, Bind (_, i1), _)) => whnf_i (subst_i_i i2 i1)
          | _ => BinOpI (opr, i1, i2)
      end
    | Ite (i1, i2, i3, r) =>
      let
        val i1 = whnf_i i1
        val i2 = whnf_i i2
        val i3 = whnf_i i3
      in
        case i1 of
            TrueI _ => i2
          | FalseI _ => i3
          | _ => Ite (i1, i2, i3, r)
      end
    | _ => i

fun normalize_i i =
  case i of
      UVarI (x, r) => load_uvar normalize_i i x
    | UnOpI (opr, i, r) => UnOpI (opr, normalize_i i, r)
    | DivI (i1, n2) => DivI (normalize_i i1, n2)
    | ExpI (i1, n2) => ExpI (normalize_i i1, n2)
    | BinOpI (opr, i1, i2) =>
      let
        val i1 = normalize_i i1
        val i2 = normalize_i i2
      in
        case (opr, i1) of
            (IApp, IAbs (_, Bind (_, i1), _)) => normalize_i (subst_i_i i2 i1)
          | _ => BinOpI (opr, i1, i2)
      end
    | Ite (i1, i2, i3, r) =>
      let
        val i1 = normalize_i i1
        val i2 = normalize_i i2
        val i3 = normalize_i i3
      in
        case i1 of
            TrueI _ => i2
          | FalseI _ => i3
          | _ => Ite (i1, i2, i3, r)
      end
    | VarI _ => i
    | ConstIN _ => i
    | ConstIT _ => i
    | TTI _ => i
    | TrueI _ => i
    | FalseI _ => i
    | AdmitI _ => i
    | IAbs (b, Bind (name, i), r) => IAbs (update_bs b, Bind (name, normalize_i i), r)

fun SOME_or_fail opt err = 
  case opt of
      SOME a => a
    | NONE => raise err ()
infix 0 !!
fun opt !! err = SOME_or_fail opt err
                                      
fun collect_var_aux_i_ibind f d acc (Bind (_, b) : ('a * 'b) ibind) = f (d + 1) acc b

fun collect_var_long_id d (m, (x, r)) =
  case m of
      SOME _ => [(m, (x, r))]
    | NONE =>
      if x >= d then [(NONE, (x - d, r))]
      else []
  
local
  fun f d(*depth*) acc b =
    case b of
	VarI x => collect_var_long_id d x @ acc
      | ConstIN n => acc
      | ConstIT x => acc
      | UnOpI (opr, i, r) => f d acc i
      | DivI (i, n) => f d acc i
      | ExpI (i, n) => f d acc i
      | BinOpI (opr, i1, i2) => 
        let
          val acc = f d acc i1
          val acc = f d acc i2
        in
          acc
        end
      | Ite (i1, i2, i3, r) =>
        let
          val acc = f d acc i1
          val acc = f d acc i2
          val acc = f d acc i3
        in
          acc
        end
      | TrueI r => acc
      | FalseI r => acc
      | TTI r => acc
      | IAbs (b, bind, r) =>
        collect_var_aux_i_ibind f d acc bind
      | AdmitI r => acc
      | UVarI a => acc
in
val collect_var_aux_i_i = f
fun collect_var_i_i b = f 0 [] b
end

fun findi f xs = findWithIdx (fn (_, x) => f x) xs
                             
fun find_injection (eq : 'a -> 'a -> bool) (xs : 'a list) (ys : 'a list) : int list option =
  let
    exception Error
    fun f x =
      case findi (fn y => eq x y) ys of
          SOME (n, _) => n
        | NONE => raise Error
  in
    SOME (map f xs)
    handle Error => NONE
  end
          
fun ncsubst_aux_is_ibind f d x v (Bind (name, b) : ('a * 'b) ibind) =
  Bind (name, f (d + 1) x v b)
       
fun apply_depth d (m, (x, r)) =
  case m of
      SOME _ => (m, (x, r))
    | NONE => (NONE, (x + d, r))

fun ncsubst_long_id d x get_v default y =
  case findi (curry eq_long_id y) (map (apply_depth d) x) of
      SOME (n, _) => get_v n
    | NONE => default
          
local
  fun f d x v b =
    case b of
	VarI y => ncsubst_long_id d x (fn n => shiftx_i_i 0 d (List.nth (v, n))) b y
      | ConstIN n => ConstIN n
      | ConstIT x => ConstIT x
      | UnOpI (opr, i, r) => UnOpI (opr, f d x v i, r)
      | DivI (i1, n2) => DivI (f d x v i1, n2)
      | ExpI (i1, n2) => ExpI (f d x v i1, n2)
      | BinOpI (opr, d1, d2) => BinOpI (opr, f d x v d1, f d x v d2)
      | Ite (i1, i2, i3, r) => Ite (f d x v i1, f d x v i2, f d x v i3, r)
      | TrueI r => TrueI r
      | FalseI r => FalseI r
      | TTI r => TTI r
      | IAbs (b, bind, r) => IAbs (b, ncsubst_aux_is_ibind f d x v bind, r)
      | AdmitI r => AdmitI r
      | UVarI a => b
in
val ncsubst_aux_is_i = f 
fun ncsubst_is_i x v b = f 0 x v b
end
        
fun V r n = VarI (NONE, (n, r))
fun TV r n = MtVar (NONE, (n, r))
               
fun get_uvar_info x err =
  case !x of
      Fresh info => info
    | Refined _ => err ()
                       
fun unify_i r gctxn ctxn (i, i') =
  let
    val unify_i = unify_i r gctxn
    exception UnifyIAppFailed
    (* Try to see whether [i']'s variables are covered by the arguments applied to [x]. If so, then refine [x] with [i'], with the latter's variables replaced by the former's arguments. This may not be the most general instantiation, because [i']'s constants will be fixed for [x], although those constants may be arguments in a more instantiation. For example, unifying [x y 5] with [y+5] will refine [x] to be [fun y z => y+5], but a more general instantiation is [fun y z => y+z]. This less-general instantiation may cause later unifications to fail. *)
    fun unify_IApp i i' =
      let
        fun is_IApp_UVarI i =
          let
            val f :: args = collect_IApp i
          in
            case f of
                UVarI (x, _) => SOME (x, args)
              | _ => NONE
          end
        val (x, args) = is_IApp_UVarI i !! (fn () => UnifyIAppFailed)
        val args = map normalize_i args
        val i' = normalize_i i'
        val vars' = collect_var_i_i i'
        val inj = find_injection eq_i (map VarI vars') (rev args) !! (fn () => UnifyIAppFailed)
        (* non-consuming substitution *)
        val i' = ncsubst_is_i vars' (map (V r) inj) i'
        val (_, ctx, _) = get_uvar_info x (fn () => raise Impossible "unify_i()/IApp: shouldn't be [Refined]")
        fun IAbsMany (ctx, i, r) = foldl (fn ((name, b), i) => IAbs (b, Bind ((name, r), i), r)) i ctx
        val i' = IAbsMany (ctx, i', r)
        val () = refine x i'
      in
        ()
      end
    fun structural_compare (i, i') =
      let
        fun default () = 
          if eq_i i i' then ()
          else write_prop (BinPred (EqP, i, i'), r)
      in
        case (i, i') of
            (* ToReal is injective *)
            (UnOpI (ToReal, i, _), UnOpI (ToReal, i', _)) =>
            unify_i ctxn (i', i)
          | _ => default ()
      end
    val i = whnf_i i (* todo: whnf_i is enough *)
    val i' = whnf_i i'
    (* val () = println $ sprintf "Unifying indices $ and $" [str_i gctxn ctxn i, str_i gctxn ctxn i'] *)
  in
    if eq_i i i' then ()
    else
      (* first try unifying applications of uvars with the other index; if unsuccessful in both directions, then try ordinary structural unification *)
      unify_IApp i i'
      handle
      UnifyIAppFailed =>
      (unify_IApp i' i
       handle
       UnifyIAppFailed =>
       structural_compare (i, i'))
  end

fun normalize_p p =
  case p of
      Quan (q, bs, Bind (name, p), r) => Quan (q, update_bs bs, Bind (name, normalize_p p), r)
    | BinConn (opr, p1, p2) => BinConn (opr, normalize_p p1, normalize_p p2)
    | BinPred (opr, i1, i2) => BinPred (opr, normalize_i i1, normalize_i i2)
    | Not (p, r) => Not (normalize_p p, r)
    | True _ => p
    | False _ => p
                   
fun whnf_s s =
  case s of
      UVarS (x, r) => load_uvar whnf_s s x
    | SApp (s, i) =>
      let
        val s = whnf_s s
        val i = whnf_i i
      in
        case s of
            SAbs (_, Bind (_, s), _) => whnf_s (subst_i_s i s)
          | _ => SApp (s, i)
      end
    | _ => s
             
fun normalize_s s =
  case s of
      UVarS (x, r) => load_uvar normalize_s s x
    | Basic _ => s
    | Subset ((b, r1), Bind (name, p), r) => Subset ((update_bs b, r1), Bind (name, normalize_p p), r)
    | SortBigO ((b, r1), i, r) => SortBigO ((update_bs b, r1), normalize_i i, r)
    | SAbs (s_arg, Bind (name, s), r) => SAbs (normalize_s s_arg, Bind (name, normalize_s s), r)
    | SApp (s, i) =>
      let
        val s = normalize_s s
        val i = normalize_i i
      in
        case s of
            SAbs (_, Bind (_, s), _) => normalize_s (subst_i_s i s)
          | _ => SApp (s, i)
      end
        
local
  fun f d acc b =
    case b of
	True r => acc
      | False r => acc
      | Not (p, r) => f d acc p
      | BinConn (opr,p1, p2) =>
        let
          val acc = f d acc p1
          val acc = f d acc p2
        in
          acc
        end
      | BinPred (opr, i1, i2) => 
        let
          val acc = collect_var_aux_i_i d acc i1
          val acc = collect_var_aux_i_i d acc i2
        in
          acc
        end
      | Quan (q, bs, bind, r) => collect_var_aux_i_ibind f d acc bind
in
val collect_var_aux_i_p = f
fun collect_var_i_p b = f 0 [] b
end

local
  fun f d acc b =
    case b of
	Basic s => acc
      | Subset (b, bind, r) => collect_var_aux_i_ibind collect_var_aux_i_p d acc bind
      | UVarS a => acc
      | SortBigO (b, i, r) => collect_var_aux_i_i d acc i
      | SAbs (s, bind, r) => collect_var_aux_i_ibind f d acc bind
      | SApp (s, i) =>
        let
          val acc = f d acc s
          val acc = collect_var_aux_i_i d acc i
        in
          acc
        end
in
val collect_var_aux_i_s = f
fun collect_var_i_s b = f 0 [] b
end

local
  fun f d x v b =
    case b of
	True r => True r
      | False r => False r
      | Not (p, r) => Not (f d x v p, r)
      | BinConn (opr,p1, p2) => BinConn (opr, f d x v p1, f d x v p2)
      | BinPred (opr, i1, i2) => BinPred (opr, ncsubst_aux_is_i d x v i1, ncsubst_aux_is_i d x v i2)
      | Quan (q, bs, bind, r) => Quan (q, bs, ncsubst_aux_is_ibind f d x v bind, r)
in
val ncsubst_aux_is_p = f
fun ncsubst_is_p x v b = f 0 x v b
end

local
  fun f d x v b =
    case b of
	Basic s => Basic s
      | Subset (b, bind, r) => Subset (b, ncsubst_aux_is_ibind ncsubst_aux_is_p d x v bind, r)
      | UVarS a => b
      | SortBigO (b, i, r) => SortBigO (b, ncsubst_aux_is_i d x v i, r)
      | SAbs (s, bind, r) => SAbs (f d x v s, ncsubst_aux_is_ibind f d x v bind, r)
      | SApp (s, i) => SApp (f d x v s, ncsubst_aux_is_i d x v i)
in
val ncsubst_aux_is_s = f
fun ncsubst_is_s x v b = f 0 x v b
end

fun eq_s s s' =
  case s of
      Basic (b, _) =>
      (case s' of
           Basic (b', _) => eq_bs b b'
         | _ => false
      )
    | Subset ((b, _), Bind (_, p), _) =>
      (case s' of
           Subset ((b', _), Bind (_, p'), _) => eq_bs b b' andalso eq_p p p'
         | _ => false
      )
    | UVarS (x, _) =>
      (case s' of
           UVarS (x', _) => x = x'
         | _ => false
      )
    | SortBigO ((b, _), i, _) =>
      (case s' of
           SortBigO ((b', _), i', _) => eq_bs b b' andalso eq_i i i'
         | _ => false
      )
    | SAbs (s1, Bind (_, s), _) =>
      (case s' of
           SAbs (s1', Bind (_, s'), _) => eq_s s1 s1' andalso eq_s s s'
         | _ => false
      )
    | SApp (s, i) =>
      (case s' of
           SApp (s', i') => eq_s s s' andalso eq_i i i'
         | _ => false
      )
                                                             
fun collect_SApp s =
  case s of
      SApp (s, i) =>
      let 
        val (s, is) = collect_SApp s
      in
        (s, is @ [i])
      end
    | _ => (s, [])
             
fun is_SApp_UVarS s =
  let
    val (f, args) = collect_SApp s
  in
    case f of
        UVarS (x, _) => SOME (x, args)
      | _ => NONE
  end
    
fun SAbsMany (ctx, s, r) = foldl (fn ((name, s_arg), s) => SAbs (s_arg, Bind ((name, r), s), r)) s ctx
                                 
fun is_sub_sort r gctxn ctxn (s, s') =
  let
    val is_sub_sort = is_sub_sort r gctxn
    val is_eqv_sort = is_eqv_sort r gctxn
    exception UnifySAppFailed
    fun unify_SApp i i' =
      let
        val (x, args) = is_SApp_UVarS s !! (fn () => UnifySAppFailed)
        val args = map normalize_i args
        val s' = normalize_s s'
        val vars' = collect_var_i_s s'
        val inj = find_injection eq_i (map VarI vars') (rev args) !! (fn () => UnifySAppFailed)
        val s' = ncsubst_is_s vars' (map (V r) inj) s'
        val (_, ctx) = get_uvar_info x (fn () => raise Impossible "unify_s()/SApp: shouldn't be [Refined]")
        val i' = SAbsMany (ctx, i', r)
        val () = refine x i'
      in
        ()
      end
    fun structural_compare (s, s') =
      let
        fun default () = raise Error (r, ["Sort"] @ indent [str_s gctxn ctxn s] @ ["is not a subsort of"] @ indent [str_s gctxn ctxn s'])
      in
        case (s, s') of
            (Basic (bs, _), Basic (bs', _)) =>
            unify_bs r (bs, bs')
          | (Subset ((bs, r1), Bind ((name, _), p), _), Subset ((bs', _), Bind (_, p'), _)) =>
            let
	      val () = unify_bs r (bs, bs')
              val ctxd = ctx_from_sorting (name, Basic (bs, r1))
              val () = open_ctx ctxd
	      (* val () = write_prop (p <-> p', r) *)
	      val () = write_prop (p --> p', r)
	      (* val () = write_prop (p' --> p, r) *)
              val () = close_ctx ctxd
            in
              ()
            end
          | (Subset ((bs, r1), Bind ((name, _), p), _), Basic (bs', _)) =>
            let
	      val () = unify_bs r (bs, bs')
              val ctxd = ctx_from_sorting (name, Basic (bs, r1))
              val () = open_ctx ctxd
	      (* val () = write_prop (p, r) *)
              val () = close_ctx ctxd
            in
              ()
            end
          | (Basic (bs, r1), Subset ((bs', _), Bind ((name, _), p), _)) =>
            let
	      val () = unify_bs r (bs, bs')
              val ctxd = ctx_from_sorting (name, Basic (bs, r1))
              val () = open_ctx ctxd
	      val () = write_prop (p, r)
              val () = close_ctx ctxd
            in
              ()
            end
          | (SortBigO s, s') => is_sub_sort ctxn (SortBigO_to_Subset s, s')
          | (s, SortBigO s') => is_sub_sort ctxn (s, SortBigO_to_Subset s')
          | (SAbs (s1, Bind ((name, _), s), _), SAbs (s1', Bind (_, s'), _)) =>
            let
              val () = is_eqv_sort ctxn (s1, s1')
              val () = is_sub_sort (name :: ctxn) (s, s')
            in
              ()
            end
          | (SApp (s, i), SApp (s', i')) =>
            let
              val () = is_sub_sort ctxn (s, s')
              val () = unify_i r gctxn ctxn (i, i')
            in
              ()
            end
          | _ => default ()
      end
    val s = whnf_s s
    val s' = whnf_s s'
  in
    if eq_s s s' then ()
    else
      unify_SApp s s'
      handle
      UnifySAppFailed =>
      (unify_SApp s' s
       handle
       UnifySAppFailed =>
       structural_compare (s, s'))
  end

and is_eqv_sort r gctxn ctxn (s, s') =
  let
    val () = is_sub_sort r gctxn ctxn (s, s')
    val () = is_sub_sort r gctxn ctxn (s', s)
  in
    ()
  end
    
fun is_sub_sorts r gctx ctx (sorts, sorts') =
  (check_length r (sorts, sorts');
   ListPair.app (is_sub_sort r gctx ctx) (sorts, sorts'))

fun is_eqv_sorts r gctx ctx (sorts, sorts') =
  let
    val () = is_sub_sorts r gctx ctx (sorts, sorts')
    val () = is_sub_sorts r gctx ctx (sorts', sorts)
  in
    ()
  end

fun whnf_mt gctx kctx (t : mtype) : mtype =
  let
    val whnf_mt = whnf_mt gctx
  in
    case t of
        UVar (x, r) => load_uvar (whnf_mt kctx) t x
      | AppV (y, ts, is, r) =>
        let
          val y = try_retrieve_MtVar (whnf_mt kctx) gctx kctx y
        in
          eval_AppV y (ts, is, r)
        end
      | MtVar x => try_retrieve_MtVar (whnf_mt kctx) gctx kctx x
      | MtAppI (t, i) =>
        let
          val t = whnf_mt kctx t
          val i = whnf_i i
        in
          case t of
              MtAbsI (_, Bind (_, t), _) => whnf_mt kctx (subst_i_mt i t)
            | _ => MtAppI (t, i)
        end
      | MtApp (t1, t2) =>
        let
          val t1 = whnf_mt kctx t1
          val t2 = whnf_mt kctx t2
        in
          case t1 of
              MtAbs (_, Bind (_, t1), _) => whnf_mt kctx (subst_t_mt t2 t1)
            | _ => MtApp (t1, t2)
        end
      | _ => t
  end

fun normalize_k k = mapSnd (map normalize_s) k
                                      
fun normalize_mt gctx kctx t =
  let
    val normalize_mt = normalize_mt gctx
  in
    case t of
        UVar (x, r) => load_uvar (normalize_mt kctx) t x
      | Unit r => Unit r
      | Arrow (t1, d, t2) => Arrow (normalize_mt kctx t1, update_i d, normalize_mt kctx t2)
      | TyArray (t, i) => TyArray (normalize_mt kctx t, update_i i)
      | TyNat (i, r) => TyNat (update_i i, r)
      | Prod (t1, t2) => Prod (normalize_mt kctx t1, normalize_mt kctx t2)
      | UniI (s, Bind (name, t1), r) => UniI (update_s s, Bind (name, normalize_mt (shiftx_i_kctx 1 kctx) t1), r)
      | AppV (y, ts, is, r) =>
        let
          val y = try_retrieve_MtVar (normalize_mt kctx) gctx kctx y
          val ts = map (normalize_mt kctx) ts
          val is = map update_i is
        in
          eval_AppV y (ts, is, r)
        end
      | MtVar x => try_retrieve_MtVar (normalize_mt kctx) gctx kctx x
      | MtAbsI (s, Bind (name, t), r) => MtAbsI (normalize_s s, Bind (name, normalize_mt kctx t), r)
      | MtAppI (t, i) =>
        let
          val t = normalize_mt kctx t
          val i = normalize_i i
        in
          case t of
              MtAbsI (_, Bind (_, t), _) => normalize_mt kctx (subst_i_mt i t)
            | _ => MtAppI (t, i)
        end
      | MtAbs (k, Bind (name, t), r) => MtAbs (normalize_k k, Bind (name, normalize_mt kctx t), r)
      | MtApp (t1, t2) =>
        let
          val t1 = normalize_mt kctx t1
          val t2 = normalize_mt kctx t2
        in
          case t1 of
              MtAbs (_, Bind (_, t1), _) => normalize_mt kctx (subst_t_mt t2 t1)
            | _ => MtApp (t1, t2)
        end
      | BaseType a => BaseType a
  end

fun normalize_t gctx kctx t =
  case t of
      Mono t => Mono (normalize_mt gctx kctx t)
    | Uni (Bind (name, t), r) => Uni (Bind (name, normalize_t gctx (add_kinding (fst name, Type) kctx) t), r)

fun collect_var_aux_t_ibind f d acc (Bind (_, b) : ('a * 'b) ibind) = f d acc b
fun collect_var_aux_i_tbind f d acc (Bind (_, b) : ('a * 'b) tbind) = f d acc b
fun collect_var_aux_t_tbind f d acc (Bind (_, b) : ('a * 'b) tbind) = f (d + 1) acc b

fun collect_var_aux_i_k d acc (_, sorts) =
  foldl (fn (s, acc) => collect_var_aux_i_s d acc s) acc sorts
                                                                        
local
  fun f d acc b =
    case b of
	Arrow (t1, i, t2) =>
        let
          val acc = f d acc t1
          val acc = collect_var_aux_i_i d acc i
          val acc = f d acc t2
        in
          acc
        end
      | TyNat (i, _) => collect_var_aux_i_i d acc i
      | TyArray (t, i) =>
        let
          val acc = f d acc t
          val acc = collect_var_aux_i_i d acc i
        in
          acc
        end
      | Unit _ => acc
      | Prod (t1, t2) =>
        let
          val acc = f d acc t1
          val acc = f d acc t2
        in
          acc
        end
      | UniI (s, bind, _) =>
        let
          val acc = collect_var_aux_i_s d acc s
          val acc = collect_var_aux_i_ibind f d acc bind
        in
          acc
        end
      | MtVar _ => acc
      | MtApp (t1, t2) =>
        let
          val acc = f d acc t1
          val acc = f d acc t2
        in
          acc
        end
      | MtAbs (k, bind, _) =>
        let
          val acc = collect_var_aux_i_k d acc k
          val acc = collect_var_aux_i_tbind f d acc bind
        in
          acc
        end
      | MtAppI (t, i) =>
        let
          val acc = f d acc t
          val acc = collect_var_aux_i_i d acc i
        in
          acc
        end
      | MtAbsI (s, bind, r) =>
        let
          val acc = collect_var_aux_i_s d acc s
          val acc = collect_var_aux_i_ibind f d acc bind
        in
          acc
        end
      | AppV (y, ts, is, r) => [] (* todo: AppV is to be removed *)
      | BaseType _ => acc
      | UVar _ => acc
in
val collect_var_aux_i_mt = f
fun collect_var_i_mt b = f 0 [] b
end

local
  fun f d acc b =
    case b of
	Arrow (t1, i, t2) =>
        let
          val acc = f d acc t1
          val acc = f d acc t2
        in
          acc
        end
      | TyNat (i, _) => acc
      | TyArray (t, i) => f d acc t
      | Unit _ => acc
      | Prod (t1, t2) =>
        let
          val acc = f d acc t1
          val acc = f d acc t2
        in
          acc
        end
      | UniI (s, bind, _) => collect_var_aux_t_ibind f d acc bind
      | MtVar x => collect_var_long_id d x @ acc
      | MtApp (t1, t2) =>
        let
          val acc = f d acc t1
          val acc = f d acc t2
        in
          acc
        end
      | MtAbs (k, bind, _) => collect_var_aux_t_tbind f d acc bind
      | MtAppI (t, i) => f d acc t
      | MtAbsI (s, bind, r) => collect_var_aux_t_ibind f d acc bind
      | AppV (y, ts, is, r) => [] (* todo: AppV is to be removed *)
      | BaseType _ => acc
      | UVar _ => acc
in
val collect_var_aux_t_mt = f
fun collect_var_t_mt b = f 0 [] b
end

fun ncsubst_aux_is_k d x v b = mapSnd (map (ncsubst_aux_is_s d x v)) b
        
fun ncsubst_aux_is_tbind f d x v (Bind (name, b) : ('a * 'b) tbind) =
  Bind (name, f d x v b)
local
  fun f d x v b =
    case b of
	Arrow (t1, i, t2) => Arrow (f d x v t1, ncsubst_aux_is_i d x v i, f d x v t2)
      | TyNat (i, r) => TyNat (ncsubst_aux_is_i d x v i, r)
      | TyArray (t, i) => TyArray (f d x v t, ncsubst_aux_is_i d x v i)
      | Unit r => Unit r
      | Prod (t1, t2) => Prod (f d x v t1, f d x v t2)
      | UniI (s, bind, r) => UniI (ncsubst_aux_is_s d x v s, ncsubst_aux_is_ibind f d x v bind, r)
      | AppV (y, ts, is, r) => b
      | MtVar y => MtVar y
      | MtApp (t1, t2) => MtApp (f d x v t1, f d x v t2)
      | MtAbs (k, bind, r) => MtAbs (ncsubst_aux_is_k d x v k, ncsubst_aux_is_tbind f d x v bind, r)
      | MtAppI (t, i) => MtAppI (f d x v t, ncsubst_aux_is_i d x v i)
      | MtAbsI (s, bind, r) => MtAbsI (ncsubst_aux_is_s d x v s, ncsubst_aux_is_ibind f d x v bind, r)
      | BaseType a => BaseType a
      | UVar a => b
in
val ncsubst_aux_is_mt = f
fun ncsubst_is_mt x v b = f 0 x v b
end

fun ncsubst_aux_ts_ibind f (di, dt) x v (Bind (name, b) : ('a * 'b) ibind) =
  Bind (name, f (di + 1, dt) x v b)
fun ncsubst_aux_ts_tbind f (di, dt) x v (Bind (name, b) : ('a * 'b) tbind) =
  Bind (name, f (di, dt + 1) x v b)
local
  fun f d x v b =
    case b of
	Arrow (t1, i, t2) => Arrow (f d x v t1, i, f d x v t2)
      | TyNat (i, r) => TyNat (i, r)
      | TyArray (t, i) => TyArray (f d x v t, i)
      | Unit r => Unit r
      | Prod (t1, t2) => Prod (f d x v t1, f d x v t2)
      | UniI (s, bind, r) => UniI (s, ncsubst_aux_ts_ibind f d x v bind, r)
      | AppV (y, ts, is, r) => b
      | MtVar y => ncsubst_long_id (snd d) x (fn n => shiftx_i_mt 0 (fst d) (shiftx_t_mt 0 (snd d) (List.nth (v, n)))) b y
      | MtAbs (k, bind, r) => MtAbs (k, ncsubst_aux_ts_tbind f d x v bind, r)
      | MtApp (t1, t2) => MtApp (f d x v t1, f d x v t2)
      | MtAbsI (s, bind, r) => MtAbsI (s, ncsubst_aux_ts_ibind f d x v bind, r)
      | MtAppI (t, i) => MtAppI (f d x v t, i)
      | BaseType a => BaseType a
      | UVar a => b
in
val ncsubst_aux_ts_mt = f
fun ncsubst_ts_mt x v b = f (0, 0) x v b
end

fun eq_ls eq (ls1, ls2) = length ls1 = length ls2 andalso List.all eq $ zip (ls1, ls2)
                                                              
fun eq_k ((n, sorts) : kind) (n', sorts') =
  n = n' andalso eq_ls (uncurry eq_s) (sorts, sorts')
  
fun eq_mt t t' = 
    case t of
	Arrow (t1, i, t2) =>
        (case t' of
	     Arrow (t1', i', t2') => eq_mt t1 t1' andalso eq_i i i' andalso eq_mt t2 t2'
           | _ => false
        )
      | TyNat (i, r) =>
        (case t' of
             TyNat (i', _) => eq_i i i'
           | _ => false
        )
      | TyArray (t, i) =>
        (case t' of
             TyArray (t', i') => eq_mt t t' andalso eq_i i i'
           | _ => false
        )
      | Unit r =>
        (case t' of
             Unit _ => true
           | _ => false
        )
      | Prod (t1, t2) =>
        (case t' of
             Prod (t1', t2') => eq_mt t1 t1' andalso eq_mt t2 t2'
           | _ => false
        )
      | UniI (s, Bind (_, t), r) =>
        (case t' of
             UniI (s', Bind (_, t'), _) => eq_s s s' andalso eq_mt t t'
           | _ => false
        )
      | AppV (y, ts, is, r) => false
      | MtVar x =>
        (case t' of
             MtVar x' => eq_long_id (x, x')
           | _ => false
        )
      | MtAbs (k, Bind (_, t), r) =>
        (case t' of
             MtAbs (k', Bind (_, t'), _) => eq_k k k' andalso eq_mt t t'
           | _ => false
        )
      | MtApp (t1, t2) =>
        (case t' of
             MtApp (t1', t2') => eq_mt t1 t1' andalso eq_mt t2 t2'
           | _ => false
        )
      | MtAbsI (s, Bind (_, t), r) =>
        (case t' of
             MtAbsI (s', Bind (_, t'), _) => eq_s s s' andalso eq_mt t t'
           | _ => false
        )
      | MtAppI (t, i) =>
        (case t' of
             MtAppI (t', i') => eq_mt t t' andalso eq_i i i'
           | _ => false
        )
      | BaseType (a : base_type, r) =>
        (case t' of
             BaseType (a' : base_type, _)  => eq_base_type (a, a')
           | _ => false
        )
      | UVar (x, _) =>
        (case t' of
             UVar (x', _) => x = x'
           | _ => false
        )

fun MtAbsMany (ctx, t, r) = foldl (fn ((name, k), t) => MtAbs (k, Bind ((name, r), t), r)) t ctx
fun MtAbsIMany (ctx, t, r) = foldl (fn ((name, s), t) => MtAbsI (s, Bind ((name, r), t), r)) t ctx
                                           
fun unify_mt r gctx ctx (t, t') =
  let
    val unify_mt = unify_mt r gctx
    val sctx = #1 ctx
    val kctx = #2 ctx
    val gctxn = gctx_names gctx
    val ctxn = (sctx_names $ #1 ctx, names $ #2 ctx)
    val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
    fun error ctxn (t, t') = unify_error r (str_mt gctxn ctxn t, str_mt gctxn ctxn t')
    (* val () = println $ sprintf "Unifying types $ and $" [str_mt gctxn ctxn t, str_mt gctxn ctxn t'] *)
    exception UnifyMtAppFailed
    fun unify_MtApp t t' =
      let
        fun collect_MtApp t =
          case t of
              MtApp (t1, t2) =>
              let 
                val (f, args) = collect_MtApp t1
              in
                (f, args @ [t2])
              end
            | _ => (t, [])
        fun collect_MtAppI t =
          case t of
              MtAppI (t, i) =>
              let 
                val (f, args) = collect_MtAppI t
              in
                (f, args @ [i])
              end
            | _ => (t, [])
        fun is_MtApp_UVar t =
          let
            val (t, t_args) = collect_MtApp t
            val (f, i_args) = collect_MtAppI t
          in
            case f of
                UVar (x, _) => SOME (x, i_args, t_args)
              | _ => NONE
          end
        val (x, i_args, t_args) = is_MtApp_UVar t !! (fn () => UnifyMtAppFailed)
        val i_args = map normalize_i i_args
        val t_args = map (normalize_mt gctx kctx) t_args
        val t' = normalize_mt gctx kctx t'
        val i_vars' = collect_var_i_mt t'
        val i_inj = find_injection eq_i (map VarI i_vars') (rev i_args) !! (fn () => UnifyMtAppFailed)
        val t_vars' = collect_var_t_mt t'
        val t_inj = find_injection eq_mt (map MtVar i_vars') (rev t_args) !! (fn () => UnifyMtAppFailed)
        val t' = ncsubst_ts_mt t_vars' (map (TV r) t_inj) t'
        val t' = ncsubst_is_mt i_vars' (map (V r) i_inj) t'
        val (_, (sctx, kctx)) = get_uvar_info x (fn () => raise Impossible "unify_t()/MtApp: shouldn't be [Refined]")
        val t' = MtAbsMany (kctx, t', r)
        val t' = MtAbsIMany (sctx, t', r)
        val () = refine x t'
      in
        ()
      end
    fun structural_compare (t, t') =
      case (t, t') of
          (Arrow (t1, d, t2), Arrow (t1', d', t2')) =>
          (unify_mt ctx (t1, t1');
           unify_i r gctxn sctxn (d, d');
           unify_mt ctx (t2, t2'))
        | (TyArray (t, i), TyArray (t', i')) =>
          (unify_mt ctx (t, t');
           unify_i r gctxn sctxn (i, i')
          )
        | (TyNat (i, _), TyNat (i', _)) =>
          unify_i r gctxn sctxn (i, i')
        | (Prod (t1, t2), Prod (t1', t2')) =>
          (unify_mt ctx (t1, t1');
           unify_mt ctx (t2, t2'))
        | (UniI (s, Bind ((name, _), t1), _), UniI (s', Bind (_, t1'), _)) =>
          (is_eqv_sort r gctxn sctxn (s, s');
           open_close add_sorting_sk (name, s) ctx (fn ctx => unify_mt ctx (t1, t1'))
          )
        | (Unit _, Unit _) => ()
	| (BaseType (Int, _), BaseType (Int, _)) => ()
	(* | (MtVar x, MtVar x') =>  *)
	(*   if eq_long_id (x, x') then *)
        (*     () *)
	(*   else *)
	(*     raise error ctxn (t, t') *)
	| (AppV (x, ts, is, _), AppV (x', ts', is', _)) => 
	  if eq_long_id (x, x') then
	    (ListPair.app (unify_mt ctx) (ts, ts');
             ListPair.app (unify_i r gctxn sctxn) (is, is'))
	  else
	    raise error ctxn (t, t')
	| _ => raise error ctxn (t, t')
    val t = whnf_mt gctx kctx t
    val t' = whnf_mt gctx kctx t'
  in
    if eq_mt t t' then ()
    else
      unify_MtApp t t'
      handle
      UnifyMtAppFailed =>
      (unify_MtApp t' t
       handle
       UnifyMtAppFailed =>
       structural_compare (t, t'))
  end

fun unify_t r gctx ctx (t, t') =
  case (t, t') of
      (Mono t, Mono t') => unify_mt r gctx ctx (t, t')
    | (Uni (Bind ((name, _), t), _), Uni (Bind (_, t'), _)) => unify_t r gctx (add_kinding_sk (name, Type) ctx) (t, t')
    | _ =>
      let
        val gctxn = gctx_names gctx
        val ctxn = (sctx_names $ #1 ctx, names $ #2 ctx)
      in
        raise unify_error r (str_t gctxn ctxn t, str_t gctxn ctxn t')
      end
        
fun kind_mismatch expect str_got got = sprintf "Kind mismatch: expect $ got $" [expect, str_got got]
fun kind_mismatch_in_type expected str_got got thing =
  [sprintf "Kind mismatch:" [thing]] @ indent [sprintf "expected:\t $" [expected], sprintf "got:\t $" [str_got got], sprintf "in type:\t $" [thing]]

fun is_sub_kind r gctxn sctxn (k as (ntargs, sorts), k' as (ntargs', sorts')) =
  let
    val () = check_eq r op= (ntargs, ntargs')
    (* contravariant *)
    val () = is_sub_sorts r gctxn sctxn (sorts', sorts)
  in
    ()
  end
  handle Error _ => raise Error (r, [kind_mismatch (str_k gctxn sctxn k') (str_k gctxn sctxn) k])
                              
fun is_eqv_kind r gctxn sctxn (k, k') =
  let
    val () = is_sub_kind r gctxn sctxn (k, k')
    val () = is_sub_kind r gctxn sctxn (k', k)
  in
    ()
  end

(*      
fun unify_kind r gctxn sctxn (k, k') =
    case (k, k') of
        (ArrowK (is_dt, ntargs, sorts), ArrowK (is_dt', ntargs', sorts')) =>
        let
          val () = check_eq r op= (is_dt, is_dt')
          val () = check_eq r op= (ntargs, ntargs')
          val () = unify_sorts r gctxn sctxn (sorts, sorts')
        in
          ()
        end
        handle Error _ => raise Error (r, [kind_mismatch gctxn sctxn (str_k gctxn sctxn k) k'])
*)
    
fun is_sub_kindext r gctx ctx (ke as (dt, k, t), ke' as (dt', k', t')) =
  let
    val gctxn = gctx_names gctx
    val sctxn = sctx_names $ #1 ctx
    val kctxn = names $ #2 ctx
    val () = check_eq r op= (dt, dt')
    val () = is_sub_kind r gctxn sctxn (k, k')
  in
    case (t, t') of
        (NONE, NONE) => ()
      | (SOME t, SOME t') => unify_mt r gctx ctx (t, t')
      | (SOME _, NONE) => ()
      | (_, _) => raise Error (r, [sprintf "Kind $ is not a sub kind of $" [str_ke gctxn (sctxn, kctxn) ke, str_ke gctxn (sctxn, kctxn) ke']])
  end

val counter = ref 0

fun inc () = 
  let 
    val n = !counter
    val () = counter := n + 1
  in
    n
  end

fun get_base (* r gctx ctx *) on_UVarS s =
  let
    val r = get_region_s s
    val s = normalize_s s
    exception OnSAppFailed
    fun on_SApp_UVarS s =
      let
        val (x, args) = is_SApp_UVarS s !! (fn () => OnSAppFailed)
        val info = get_uvar_info x (fn () => raise Impossible "check_sort()/unify_SApp_UVar(): x should be Fresh")
      in
        on_UVarS (x, r, info, args)
      end
    fun main s =
      case s of
          Basic (s, _) => s
        | Subset ((s, _), _, _) => s
        | SortBigO ((s, _), _, _) => s
        | UVarS _ => raise Impossible "get_base()/main(): shouldn't be UVarS"
        | SAbs _ => raise Impossible "get_base()/main(): shouldn't be SAbs"
        | SApp _ => raise Impossible "get_base()/main(): shouldn't be SApp"
  in
    on_SApp_UVarS s
    handle
    OnSAppFailed =>
    main s
  end

fun IApps f args = foldl (fn (arg, f) => BinOpI (IApp, f, arg)) f args
fun SApps f args = foldl (fn (arg, f) => SApp (f, arg)) f args
fun MtAppIs f args = foldl (fn (arg, f) => MtAppI (f, arg)) f args
fun MtApps f args = foldl (fn (arg, f) => MtApp (f, arg)) f args
                         
fun fresh_bsort () = UVarBS (ref (Fresh (inc ())))

fun refine_UVarS_to_Basic (x, r, info, args) =
  let
    val b = fresh_bsort ()
    val s = Basic (b, r)
    val (_, ctx) = info
    val s = SAbsMany (ctx, s, r)
    val () = refine x s
  in
    b
  end
    
fun fresh_i ctx bsort r = 
  let
    val ctx = map (mapSnd (get_base refine_UVarS_to_Basic)) ctx
    val x = ref (Fresh (inc (), ctx, bsort))
    val i = UVarI (x, r)
    val i = IApps i (map (V r) $ rev $ range (length ctx))
  in
    i
  end

fun fresh_sort ctx r : sort =
  let
    val x = ref (Fresh (inc (), ctx))
    val s = UVarS (x, r)
    val s = SApps s (map (V r) $ rev $ range (length ctx))
  in
    s
  end
                                             
fun fresh_mt (ctx as (sctx, kctx)) r : mtype =
  let
    val x = ref (Fresh (inc (), mapSnd (map (mapSnd get_ke_kind)) ctx))
    val t = UVar (x, r)
    val t = MtAppIs t (map (V r) $ rev $ range (length sctx))
    val t = MtApps t (map (TV r) $ rev $ range (length kctx))
  in
    t
  end

fun sort_mismatch gctx ctx i expect have =  "Sort mismatch for " ^ str_i gctx ctx i ^ ": expect " ^ expect ^ " have " ^ str_s gctx ctx have

fun is_wf_bsort (bs : U.bsort) : bsort =
  case bs of
      U.Base bs => Base bs
    | U.BSArrow (a, b) => BSArrow (is_wf_bsort a, is_wf_bsort b)
    | U.UVarBS () => fresh_bsort ()

(* a classifier for [sort], since [sort] has [SAbs] and [SApp] *)        
type sort_type = sort list
val Sort : sort_type = []
fun is_Sort (t : sort_type) = null t
                      
fun get_sort_type gctx (ctx : scontext, s : U.sort) : sort * sort_type =
  let
    val get_sort_type = get_sort_type gctx
    val is_wf_sort = is_wf_sort gctx
    val is_wf_prop = is_wf_prop gctx
    val get_bsort = get_bsort gctx
    val check_bsort = check_bsort gctx
  in
    case s of
	U.Basic (bs, r) => (Basic (is_wf_bsort bs, r), Sort)
      | U.Subset ((bs, r), Bind ((name, r2), p), r_all) =>
        let 
          val bs = is_wf_bsort bs
          val p = open_close add_sorting (name, Basic (bs, r)) ctx (fn ctx => is_wf_prop (ctx, p))
        in
          (Subset ((bs, r), Bind ((name, r2), p), r_all), Sort)
        end
      | U.SortBigO ((bs, r), i, r_all) =>
        let
          val bs = is_wf_bsort bs
          val i = check_bsort (ctx, i, bs)
        in
          (SortBigO_to_Subset ((bs, r), i, r_all), Sort)
        end
      | U.UVarS ((), r) =>
        (* sort underscore will always mean a sort of type Sort *)
        (fresh_sort ctx r, Sort)
      | U.SAbs (s1, Bind ((name, r1), s), r) =>
        let
          val s1 = is_wf_sort (ctx, s1)
          val (s, t) = get_sort_type (add_sorting (name, s1) ctx, s)
        in
          (SAbs (s1, Bind ((name, r1), s), r), s1 :: t)
        end
      | U.SApp (s, i) =>
        let
          val (s, t) = get_sort_type (ctx, s)
          val (s1, t) =
              case t of
                  s1 :: t => (s1, t)
                | [] => raise Error (get_region_s s, [sprintf "sort $ should be an abstract" [str_s (gctx_names gctx) (sctx_names ctx) s]])
          val i = check_bsort (ctx, i, get_base refine_UVarS_to_Basic s1)
        in
          (SApp (s, i), t)
        end
        
  end

and is_wf_sort gctx (ctx : scontext, s : U.sort) : sort =
  let
    val (s, t) = get_sort_type gctx (ctx, s)
    val r = get_region_s s
    val () =
        if is_Sort t then
          ()
        else
          raise Error (r, [sprintf "sort $ is ill-formed (not fully applied)" [str_s (gctx_names gctx) (sctx_names ctx) s]])
  in
    s
  end

and is_wf_prop gctx (ctx : scontext, p : U.prop) : prop =
    let
      val is_wf_sort = is_wf_sort gctx
      val is_wf_prop = is_wf_prop gctx
      val get_bsort = get_bsort gctx
      val check_bsort = check_bsort gctx
    in
      case p of
	  U.True r => True r
        | U.False r => False r
        | U.Not (p, r) => 
          Not (is_wf_prop (ctx, p), r)
        | U.BinConn (opr, p1, p2) =>
	  BinConn (opr,
                   is_wf_prop (ctx, p1),
	           is_wf_prop (ctx, p2))
        | U.BinPred (EqP, i1, i2) =>
	  let 
            val (i1, bs1) = get_bsort (ctx, i1)
	    val (i2, bs2) = get_bsort (ctx, i2)
            val () = unify_bs (U.get_region_p p) (bs1, bs2)
	  in
            BinPred (EqP, i1, i2)
	  end
        | U.BinPred (opr, i1, i2) =>
	  let 
            val (i1, bs1) = get_bsort (ctx, i1)
	    val (i2, bs2) = get_bsort (ctx, i2)
            val () = unify_bs (U.get_region_p p) (bs1, bs2)
            val bs = update_bs bs1
            fun error expected = Error (U.get_region_p p, sprintf "Sorts of operands of $ must be both $:" [str_bin_pred opr, expected] :: indent ["left: " ^ str_bs bs1, "right: " ^ str_bs bs2])
            val () =
                case opr of
                    BigO =>
                    let
                      val (args, ret) = collect_BSArrow bs
                      val r = U.get_region_p p
                      val () = unify_bs r (ret, Base Time)
                      val () = app (fn arg => unify_bs r (arg, Base Nat)) args
                    in
                      ()
                    end
                  | _ =>
                    (case bs of
                         Base Nat => ()
                       | Base Time => ()
                       | _ => raise error "Nat or Time"
                    )
	  in
            BinPred (opr, i1, i2)
	  end
        | U.Quan (q, bs, Bind ((name, r), p), r_all) =>
          let
            val q = case q of
                        Forall => Forall
                      | Exists _ => Exists NONE
            val bs = is_wf_bsort bs
            val p = open_close add_sorting (name, Basic (bs, r)) ctx (fn ctx => is_wf_prop (ctx, p))
          in
            Quan (q, bs, Bind ((name, r), p), r_all)
          end
    end
      
and get_bsort (gctx : sigcontext) (ctx : scontext, i : U.idx) : idx * bsort =
    let
      val is_wf_sort = is_wf_sort gctx
      val is_wf_prop = is_wf_prop gctx
      val get_bsort = get_bsort gctx
      val check_bsort = check_bsort gctx
      fun main () =
        case i of
	    U.VarI x =>
            let
              val s = fetch_sort gctx (ctx, x)
              fun error r gctx ctx () = Error (r, [sprintf "Can't figure out base sort of $" [str_s gctx ctx s]])
            in
              (VarI x, get_base (fn _ => raise error (U.get_region_i i) (gctx_names gctx) (sctx_names ctx) ()) s)
            end
          | U.UnOpI (opr, i, r) =>
            let
              val (atype, rettype) = idx_un_op_type opr
            in
              (UnOpI (opr,
                      check_bsort (ctx, i, Base atype),
                      r),
               Base rettype)
            end
          | U.DivI (i1, (n2, r2)) =>
            let 
              val i1 = check_bsort (ctx, i1, Base Time)
	      val () = if n2 > 0 then ()
	               else raise Error (r2, ["Can only divide by positive integer"])
            in
              (DivI (i1, (n2, r2)), Base Time)
            end
          | U.ExpI (i1, (n2, r2)) =>
            let 
              val i1 = check_bsort (ctx, i1, Base Time)
            in
              (ExpI (i1, (n2, r2)), Base Time)
            end
	  | U.BinOpI (opr, i1, i2) =>
            let
              (* overloaded binary operations *)
              fun overloaded bases rettype =
                let 
                  val (i1, bs1) = get_bsort (ctx, i1)
                  val (i2, bs2) = get_bsort (ctx, i2)
                  val () = unify_bs (U.get_region_i i) (bs1, bs2)
                  val bs = update_bs bs1
                  fun error () = Error (U.get_region_i i, sprintf "Sorts of operands of $ must be the same and from $:" [str_idx_bin_op opr, str_ls str_b bases] :: indent ["left: " ^ str_bs bs1, "right: " ^ str_bs bs2])
                  val rettype =
                      case bs of
                          Base b =>
                          if mem op= b bases then
                            case rettype of
                                SOME b => Base b
                              | NONE => bs
                          else raise error ()
                        | _ => raise error ()
                in
                  (BinOpI (opr, i1, i2), rettype)
                end
            in
              case opr of
                  IApp =>
                  let
                    (* val () = println $ U.str_i (names ctx) i *)
                    val (i1, bs1) = get_bsort (ctx, i1)
                    val bs2 = fresh_bsort ()
                    val bs = fresh_bsort ()
                    val () = unify_bs (get_region_i i1) (bs1, BSArrow (bs2, bs))
                    val i2 = check_bsort (ctx, i2, bs2)
                  in
                    (BinOpI (opr, i1, i2), bs)
                  end
                | AddI => overloaded [Nat, Time] NONE
                | BoundedMinusI => overloaded [Nat, Time] NONE
                | MultI => overloaded [Nat, Time] NONE
                | MaxI => overloaded [Nat, Time] NONE
                | MinI => overloaded [Nat, Time] NONE
                | EqI => overloaded [Nat, BoolSort, UnitSort] (SOME BoolSort)
                | LtI => overloaded [Nat, Time, BoolSort, UnitSort] (SOME BoolSort)
                | GeI => overloaded [Nat, Time, BoolSort, UnitSort] (SOME BoolSort)
                | _ =>
                  let
                    val (arg1type, arg2type, rettype) = idx_bin_op_type opr
                  in
                    (BinOpI (opr,
                             check_bsort (ctx, i1, Base arg1type),
                             check_bsort (ctx, i2, Base arg2type)),
                     Base rettype)
                  end
            end
          | i_all as U.Ite (i, i1, i2, r) =>
            let
              val i = check_bsort (ctx, i, Base BoolSort)
              val (i1, bs1) = get_bsort (ctx, i1)
              val (i2, bs2) = get_bsort (ctx, i2)
              val () = unify_bs (U.get_region_i i_all) (bs1, bs2)
            in
              (Ite (i, i1, i2, r), bs1)
            end
	  | U.ConstIT (x, r) => 
	    (ConstIT (x, r), Base Time)
	  | U.ConstIN (n, r) => 
	    if n >= 0 then
	      (ConstIN (n, r), Base Nat)
	    else
	      raise Error (r, ["Natural number constant must be non-negative"])
	  | U.TrueI r => 
            (TrueI r, Base BoolSort)
	  | U.FalseI r => 
            (FalseI r, Base BoolSort)
	  | U.TTI r => 
            (TTI r, Base UnitSort)
          | U.IAbs (bs1, Bind ((name, r1), i), r) =>
            let
              val bs1 = is_wf_bsort bs1
              val (i, bs) = open_close add_sorting (name, Basic (bs1, r1)) ctx (fn ctx => get_bsort (ctx, i))
            in
              (IAbs (bs1, Bind ((name, r1), i), r), BSArrow (bs1, bs))
                (* case bs of *)
                (*     Base (TimeFun arity) => *)
                (*     (IAbs ((name, r1), i, r), Base (TimeFun (arity + 1))) *)
                (*   | _ => raise Error (get_region_i i, "Sort of time funtion body should be time function" :: indent ["want: time function", "got: " ^ str_bs bs]) *)
            end
	  | U.AdmitI r => 
            (AdmitI r, Base UnitSort)
          | U.UVarI ((), r) =>
            let
              val bs = fresh_bsort ()
            in
              (fresh_i ctx bs r, bs)
            end
      val ret = main ()
                handle
                Error (r, msg) => raise Error (r, msg @ ["when sort-checking index "] @ indent [U.str_i (gctx_names gctx) (sctx_names ctx) i])
    in
      ret
    end

and check_bsort gctx (ctx, i : U.idx, bs : bsort) : idx =
    let 
      val (i, bs') = get_bsort gctx (ctx, i)
      val () = unify_bs (get_region_i i) (bs', bs)
    in
      i
    end

fun is_wf_sorts gctx (ctx, sorts : U.sort list) : sort list = 
  map (fn s => is_wf_sort gctx (ctx, s)) sorts
      
fun subst_uvar_error r body i ((fresh, fresh_ctx), x) =
  Error (r,
         sprintf "Can't substitute for $ in unification variable $ in $" [str_v fresh_ctx x, fresh, body] ::
         indent [
           sprintf "because the context of $ is [$] which contains $" [fresh, join ", " $ fresh_ctx, str_v fresh_ctx x]
        ])

fun check_sort gctx (ctx, i : U.idx, s : sort) : idx =
  let 
    val (i, bs') = get_bsort gctx (ctx, i)
    val r = get_region_i i
    val s = normalize_s s
    exception UnifySAppFailed
    fun unify_SApp_UVarS s =
      let
        val (x, _) = is_SApp_UVarS s !! (fn () => UnifySAppFailed)
        val (_, ctx) = get_uvar_info x (fn () => raise Impossible "check_sort()/unify_SApp_UVar(): x should be Fresh")
        val s = Basic (bs', r)
        val s = SAbsMany (ctx, s, r)
        val () = refine x s
      in
        ()
      end
    fun main s =
      case s of
	  Subset ((bs, _), Bind ((name, _), p), _) =>
          let
	    val () = unify_bs r (bs', bs)
            val r = get_region_i i
            val (i, is_admit) =
                case i of
                    AdmitI r => (TTI r, true)
                  | _ => (i, false)
            val p = subst_i_p i p
            (* val () = println $ sprintf "Writing prop $ $" [str_p (sctx_names ctx) p, str_region "" "" r] *)
	    val () =
                if is_admit then
                  write_admit (p, r)
                else
                  write_prop (p, r)
          in
            ()
          end
        | SortBigO s => main (SortBigO_to_Subset s)
	| Basic (bs, _) => 
	  unify_bs r (bs', bs)
        | UVarS _ => raise Impossible "check_sort()/main(): s should be UVarS"
        | SAbs _ => raise Impossible "check_sort()/main(): s shouldn't be SAbs"
        | SApp _ => raise Impossible "check_sort()/main(): s shouldn't be SApp"
    val () =
        unify_SApp_UVarS s
        handle
        UnifySAppFailed =>
        (main s
         handle Error (_, msg) =>
                let
                  val ctxn = sctx_names ctx
                  val gctxn = gctx_names gctx
                in
                  raise Error (r,
                               sprintf "index $ (of base sort $) is not of sort $" [str_i gctxn ctxn i, str_bs bs', str_s gctxn ctxn s] ::
                               "Cause:" ::
                               indent msg)
                end
        )
  in
    i
  end

fun check_sorts gctx (ctx, is : U.idx list, sorts, r) : idx list =
  (check_length r (is, sorts);
   ListPair.map (fn (i, s) => check_sort gctx (ctx, i, s)) (is, sorts))

fun is_wf_kind gctx (sctx, k) = mapSnd (curry (is_wf_sorts gctx) sctx) k

(* k => Type *)
fun recur_kind k = (0, k)

(* higher-kind *)
datatype hkind =
         HKType
         | HKArrow of hkind * hkind
         | HKArrowI of sort * hkind

fun str_hk gctx ctx k =
  case k of
      HKType => "*"
    | HKArrow (k1, k2) => sprintf "($ => $)" [str_hk gctx ctx k1, str_hk gctx ctx k2]
    | HKArrowI (s, k) => sprintf "($ => $)" [str_s gctx ctx s, str_hk gctx ctx k]

val HType = HKType

fun kind_to_higher_kind (n, sorts) =
  let
    val k = foldr (fn (s, k) => HKArrowI (s, k)) HKType sorts
    val k = Range.for (fn (_, k) => HKArrow (HKType, k)) k (Range.zero_to n)
  in
    k
  end

fun is_sub_higher_kind r gctxn sctxn (k, k') =
  case (k, k') of
      (HKType, HKType) => ()
    | (HKArrow (k1, k2), HKArrow (k1', k2')) =>
      let
        val () = is_sub_higher_kind r gctxn sctxn (k1', k1)
        val () = is_sub_higher_kind r gctxn sctxn (k2, k2')
      in
        ()
      end
    | (HKArrowI (s, k), HKArrowI (s', k')) =>
      let
        val () = is_sub_sort r gctxn sctxn (s', s)
        val () = is_sub_higher_kind r gctxn sctxn (k, k')
      in
        ()
      end
    | _  => raise Error (r, [kind_mismatch (str_hk gctxn sctxn k) (str_hk gctxn sctxn) k'])

fun get_higher_kind gctx (ctx as (sctx : scontext, kctx : kcontext), c : U.mtype) : mtype * hkind = 
  let
    val get_higher_kind = get_higher_kind gctx
    val check_higher_kind = check_higher_kind gctx
    val check_higher_kind_Type = check_higher_kind_Type gctx
    val gctxn = gctx_names gctx
    val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
    fun error (r, thing, expected, str_got, got) =
      raise Error (r, kind_mismatch_in_type expected str_got got thing)
    (* val () = print (sprintf "Kinding $\n" [U.str_mt gctxn ctxn c]) *)
    fun main () =
      case c of
	  U.Arrow (c1, d, c2) => 
	  (Arrow (check_higher_kind_Type (ctx, c1),
	          check_bsort gctx (sctx, d, Base Time),
	          check_higher_kind_Type (ctx, c2)),
           HType)
        | U.TyArray (t, i) =>
	  (TyArray (check_higher_kind_Type (ctx, t),
	            check_bsort gctx (sctx, i, Base Nat)),
           HType)
        | U.TyNat (i, r) =>
	  (TyNat (check_bsort gctx (sctx, i, Base Nat), r),
           HType)
        | U.Unit r => (Unit r, HType)
	| U.Prod (c1, c2) => 
	  (Prod (check_higher_kind_Type (ctx, c1),
	         check_higher_kind_Type (ctx, c2)),
           HType)
	| U.UniI (s, Bind ((name, r), c), r_all) => 
          let
            val s = is_wf_sort gctx (sctx, s)
            val c = open_close add_sorting_sk (name, s) ctx (fn ctx => check_higher_kind_Type (ctx, c))
          in
	    (UniI (s, Bind ((name, r), c), r_all),
             HType)
          end
	| U.AppV (x, ts, is, r) => 
          let
            val (n, sorts) = fetch_kind gctx (kctx, x)
	    val () = check_length_n r (ts, n)
          in
	    (AppV (x, 
                   map (fn t => check_higher_kind_Type (ctx, t)) ts, 
                   check_sorts gctx (sctx, is, sorts, r), 
                   r),
             HType)
          end
	| U.BaseType a => (BaseType a, HType)
        | U.UVar ((), r) =>
          (* type underscore will always mean a type of kind Type *)
          (fresh_mt (sctx, kctx) r, HType)
        | U.MtVar x =>
          (MtVar x, kind_to_higher_kind $ fetch_kind gctx (kctx, x))
        | U.MtAbs (k1, Bind ((name, r1), t), r) =>
          let
            val k1 = is_wf_kind gctx (sctx, k1)
            val (t, k) = get_higher_kind (add_kinding_sk (name, k1) ctx, t)
            val k1' = kind_to_higher_kind k1
            val k = HKArrow (k1', k)
          in
            (MtAbs (k1, Bind ((name, r1), t), r), k)
          end
        | U.MtApp (t1, t2) =>
          let
            val (t1, k) = get_higher_kind (ctx, t1)
          in
            case k of
                HKArrow (k1, k2) =>
                let
                  val t2 = check_higher_kind (ctx, t2, k1)
                in
                  (MtApp (t1, t2), k2)
                end
              | _ => error (get_region_mt t1, str_mt gctxn ctxn t1, "<kind> => <kind>", str_hk gctxn sctxn, k)
          end
        | U.MtAbsI (s, Bind ((name, r1), t), r) =>
          let
            val s = is_wf_sort gctx (sctx, s)
            val (t, k) = get_higher_kind (add_sorting_sk (name, s) ctx, t)
            val k = HKArrowI (s, k)
          in
            (MtAbsI (s, Bind ((name, r1), t), r), k)
          end
        | U.MtAppI (t, i) =>
          let
            val (t, k) = get_higher_kind (ctx, t)
          in
            case k of
                HKArrowI (s, k) =>
                let
                  val i = check_sort gctx (sctx, i, s)
                in
                  (MtAppI (t, i), k)
                end
              | _ => error (get_region_mt t, str_mt gctxn ctxn t, "<sort> => <kind>", str_hk gctxn sctxn, k)
          end
    val ret =
        main ()
        handle
        Error (r, msg) => raise Error (r, msg @ ["when kind-checking of type "] @ indent [U.str_mt gctxn ctxn c])
  in
    ret
  end

and check_higher_kind gctx (ctx, t, k) =
    let
      val (t, k') = get_higher_kind gctx (ctx, t)
      val () = is_sub_higher_kind (get_region_mt t) (gctx_names gctx) (sctx_names $ #1 ctx) (k', k)
    in
      t
    end

and check_higher_kind_Type gctx (ctx, t) =
    check_higher_kind gctx (ctx, t, HType)

fun b2opt b = if b then SOME () else NONE

fun is_HKType k =
  case k of
      HKType => true
    | _ => false

fun higher_kind_to_kind k =
  case k of
      HKType => SOME Type
    | HKArrow (k1, k2) => opt_bind (b2opt $ is_HKType k1) (fn () => opt_bind (higher_kind_to_kind k2) (fn (n, sorts) => SOME (n + 1, sorts)))
    | HKArrowI (s, k) => opt_bind (higher_kind_to_kind k) (fn (n, sorts) => if n = 0 then SOME (0, s :: sorts) else NONE)

fun get_kind gctx (ctx as (sctx : scontext, kctx : kcontext), t : U.mtype) : mtype * kind =
  let
    val (t, k) = get_higher_kind gctx (ctx, t)
    val k = lazy_default (fn () => raise Error (get_region_mt t, kind_mismatch_in_type "first-order kind (i.e. * => ... <sort> => ... => *)" (str_hk (gctx_names gctx) (sctx_names sctx)) k (str_mt (gctx_names gctx) (sctx_names sctx, names kctx) t))) $ higher_kind_to_kind k
  in
    (t, k)
  end

fun check_kind gctx (ctx, t, k) =
    let
      val (t, k') = get_kind gctx (ctx, t)
      val () = is_sub_kind (get_region_mt t) (gctx_names gctx) (sctx_names $ #1 ctx) (k', k)
    in
      t
    end

fun check_kind_Type gctx (ctx, t) =
    check_kind gctx (ctx, t, Type)

fun is_wf_type gctx (ctx as (sctx : scontext, kctx : kcontext), c : U.ty) : ty = 
  let 
    val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	                           (* val () = print (sprintf "Type wellformedness checking: $\n" [str_t ctxn c]) *)
  in
    case c of
        U.Mono t =>
        Mono (check_kind_Type gctx (ctx, t))
      | U.Uni (Bind ((name, r), c), r_all) => 
	Uni (Bind ((name, r), is_wf_type gctx (add_kinding_sk (name, Type) ctx, c)), r_all)
  end

fun smart_max a b =
  if eq_i a (T0 dummy) then
    b
  else if eq_i b (T0 dummy) then
    a
  else
    BinOpI (MaxI, a, b)

fun smart_max_list ds = foldl' (fn (d, ds) => smart_max ds d) (T0 dummy) ds

(* redundancy and exhaustiveness checking *)
(* all the following cover operations assume that the cover has type t *)

datatype cover =
         TrueC
         | FalseC
         | AndC of cover * cover
         | OrC of cover * cover
         | ConstrC of long_id * cover
         | PairC of cover * cover
         | TTC

fun combine_covers covers = foldl' (swap OrC) FalseC covers

datatype habitant =
         TrueH
         | ConstrH of long_id * habitant
         | PairH of habitant * habitant
         | TTH

local
  
  fun str_cover gctx cctx c =
    let
      val str_cover = str_cover gctx
    in
      case c of
          TrueC => "_"
        | FalseC => "False"
        | AndC (c1, c2) => sprintf "($ /\\ $)" [str_cover cctx c1, str_cover cctx c2]
        | OrC (c1, c2) => sprintf "($ \\/ $)" [str_cover cctx c1, str_cover cctx c2]
        | ConstrC (x, c) => sprintf "($ $)" [str_long_id #3 gctx cctx x, str_cover cctx c]
        | PairC (c1, c2) => sprintf "($, $)" [str_cover cctx c1, str_cover cctx c2]
        | TTC => "()"
    end

  fun str_habitant gctx cctx c =
    let
      val str_habitant = str_habitant gctx
    in
      case c of
          TrueH => "_"
        | ConstrH (x, c) => sprintf "($ $)" [str_long_id #3 gctx cctx x, str_habitant cctx c]
        | PairH (c1, c2) => sprintf "($, $)" [str_habitant cctx c1, str_habitant cctx c2]
        | TTH => "()"
    end

  infixr 3 /\
  infixr 2 \/
  val op/\ = AndC
  val op\/ = OrC

  fun impossible s = Impossible $ "cover has the wrong type: " ^ s

  fun get_family (c : constr) = #1 c
                                   
  fun cover_neg gctx (ctx as (sctx, kctx, cctx)) (t : mtype) c =
    let
      val neg = cover_neg gctx ctx
      (* val t = normalize_mt t *)
      val t = whnf_mt gctx kctx t
    in
      case c of
          TrueC => FalseC
        | FalseC => TrueC
        | AndC (a, b) => neg t a \/ neg t b
        | OrC (a, b) => neg t a /\ neg t b
        | TTC => FalseC
        | PairC (c1, c2) =>
          (case t of
               Prod (t1, t2) =>
               PairC (neg t1 c1, c2) \/
               PairC (c1, neg t2 c2) \/
               PairC (neg t1 c1, neg t2 c2)
             | _ => raise impossible "cover_neg()/PairC")
        | c_all as ConstrC (x, c) =>
	  (case t of
	       AppV (family, ts, _, _) =>
	       let
                 fun get_family_siblings gctx cctx cx =
                   let
                     val family = get_family $ fetch_constr gctx (cctx, cx)
                     fun do_fetch_family (cctx, (_, r)) =
                       rev $ map snd $ mapPartialWithIdx (fn (n, (_, c)) => if eq_long_id (get_family c, family) then SOME (NONE, (n, r)) else NONE) cctx
                     fun fetch_family a = generic_fetch (shiftx_list shiftx_long_id) (package0_list (package_long_id 0)) do_fetch_family #3 a
                   in
                     fetch_family gctx (cctx, cx)
                   end
                 val all = get_family_siblings gctx cctx x
		 val others = diff eq_long_id all [x]
                 (* val () = println $ sprintf "Family siblings of $: $" [str_long_id #3 (gctx_names gctx) (names cctx) x, str_ls (str_long_id #3 (gctx_names gctx) (names cctx)) others] *)
                 val (_, _, ibinds) = fetch_constr gctx (cctx, x)
                 val (_, (t', _)) = unfold_binds ibinds
		 val t' = subst_ts_mt ts t'
                 val covers = ConstrC (x, neg t' c) :: map (fn y => ConstrC (y, TrueC)) others
	       in
                 combine_covers covers
	       end
	     | _ => raise impossible $ sprintf "cover_neg()/ConstrC:  cover is $ but type is " [str_cover (gctx_names gctx) (names cctx) c_all, str_mt (gctx_names gctx) (sctx_names sctx, names kctx) t])
    end

  (* fun cover_imply cctx t (a, b) : cover = *)
  (*     cover_neg cctx t a \/ b *)

  (* find habitant
       deep: when turned on, [find_hab] try to find a [ConstrH] for a datatype when constraints are empty (treat empty datatype as uninhabited); otherwise only return [TrueH] in such case (treat empty datatype as inhabited) *)
  fun find_hab deep gctx (ctx as (sctx, kctx, cctx)) (t : mtype) cs =
    let
      (* val () = println "find_hab() begin" *)
      (* fun sum ls = foldl' op+ 0 ls *)
      (* fun cover_size c = *)
      (*     case c of *)
      (*         TrueC => 1 *)
      (*       | FalseC => 1 *)
      (*       | AndC (c1, c2) => cover_size c1 + 1 + cover_size c2 *)
      (*       | OrC (c1, c2) => cover_size c1 + 1 + cover_size c2 *)
      (*       | ConstrC (x, c) => 1 + cover_size c *)
      (*       | PairC (c1, c2) => cover_size c1 + 1 + cover_size c2 *)
      (*       | TTC => 1 *)
      (* fun covers_size cs = sum $ map cover_size cs *)
      (* fun mt_size t = *)
      (*     case whnf_mt t of *)
      (*         Prod (t1, t2) => mt_size t1 + 1 + mt_size t2 *)
      (*       | _ => 1 *)
      fun collect_AndC acc c =
        case c of
            AndC (c1, c2) =>
            let
              val acc = collect_AndC acc c1
              val acc = collect_AndC acc c2
            in
              acc
            end
          | TrueC => acc
          | _ => c :: acc
      val collect_AndC = fn c => collect_AndC [] c
      (* fun combine_AndC cs = foldl' AndC TrueC cs *)
      local
        exception IsFalse
        fun runUntilFalse m =
          m () handle IsFalse => FalseC
        fun simp c =
          case c of
              AndC (c1, c2) =>
              (case (simp c1, simp c2) of
                   (TrueC, c) => c
                 | (c, TrueC) => c
                 | (c1, c2) => AndC (c1, c2)
              )
            | OrC (c1, c2) =>
              (case (runUntilFalse (fn () => simp c1), runUntilFalse (fn () => simp c2)) of
                   (FalseC, FalseC) => raise IsFalse
                 | (FalseC, c) => c
                 | (c, FalseC) => c
                 | (c1, c2) => OrC (c1, c2)
              )
            | TTC => TTC
            | PairC (c1, c2) => PairC (simp c1, simp c2)
            | ConstrC (x, c) => ConstrC (x, simp c)
            | TrueC => TrueC
            | FalseC => raise IsFalse
      in
      fun simp_cover cover =
        runUntilFalse (fn () => simp cover)
      fun simp_covers cs =
        let
          fun main () = List.filter (fn c => case c of TrueC => false | _ => true) $ map simp cs
        in
          main () handle IsFalse => [FalseC]
        end
      end              
      (* val () = println $ "before simp_cover(): size=" ^ (str_int $ covers_size cs) *)
      (* val c = combine_AndC cs *)
      (* val c = simp_cover c *)
      (* val cs = collect_AndC c *)
      val cs = concatMap collect_AndC $ simp_covers $ cs
      (* val () = println $ "after simp_cover(): size=" ^ (str_int $ covers_size cs) *)
                         
      exception Incon of string
      (* the last argument is for checking that recursive calls to [loop] are always on smaller arguments, to ensure termination *)
      fun loop (t : mtype, cs_all, ()) : habitant =
        let
          (* val () = println (sprintf "find_hab on type $" [str_mt (gctx_names gctx) (sctx_names sctx, names kctx) t]) *)
          (* val t = normalize_mt t *)
          val t = whnf_mt gctx kctx t
          (* val size = covers_size cs_all *)
          (* fun check_size (t', cs) = *)
          (*     let *)
          (*       val smaller = covers_size cs *)
          (*       val () = if smaller < size orelse smaller = size andalso mt_size t' < mt_size t then () *)
          (*                else raise Impossible "not smaller size" *)
          (*     in *)
          (*       (t', cs, ()) *)
          (*     end *)
          fun check_size (t', cs) = (t', cs, ())
                                      (* val cs_all = simp_covers $ concatMap collect_AndC cs_all *)
                                      (* val () = print $ sprintf "$\t\t$\n" [str_int $ covers_size cs_all, str_int $ length cs_all] *)
                                      (* fun has_false c = *)
                                      (*     case c of *)
                                      (*         FalseC => true *)
                                      (*       | TrueC => false *)
                                      (*       | TTC => false *)
                                      (*       | PairC (c1, c2) => has_false c1 orelse has_false c2 *)
                                      (*       | AndC (c1, c2) => has_false c1 orelse has_false c2 *)
                                      (*       | OrC (c1, c2) => has_false c1 andalso has_false c2 *)
                                      (*       | ConstrC (_, c) => has_false c *)
                                      (* val () = app (fn c' => if has_false c' then ((* println "has false";  *)raise Incon "has false") else ()) cs_all *)
                                      (* fun split3 i l = (List.nth (l, i), take i l, drop (i + 1) l) *)
                                      (* fun i_tl_to_hd c i cs = to_hd (i + 1) (c :: cs) *)
        in
          case cs_all of
              [] =>
              if not deep then
                TrueH
              else
                let
                  (* val () = println (sprintf "Empty constraints now. Now try to find any inhabitant of type $" [str_mt (gctx_names gctx) (sctx_names sctx, names kctx) t]) *)
                  val ret =
                      case t of
                          AppV (family, _, _, _) =>
                          (case fetch_kind_and_is_datatype gctx (kctx, family) of
                               (true, _, _) =>
	                       let
                                 fun do_fetch_constrs (cctx, family) =
                                   rev $ map snd $ mapPartialWithIdx (fn (n, (_, c)) => if eq_long_id (get_family c, (NONE, family)) then SOME (NONE, (n, snd family)) else NONE) cctx
                                 fun fetch_constrs a = generic_fetch (shiftx_list shiftx_long_id) (package0_list (package_long_id 0)) do_fetch_constrs #3 a
                                 val all = fetch_constrs gctx (cctx, family)
                                                         (* val () = println $ sprintf "Constructors of $: $" [str_long_id #2 (gctx_names gctx) (names kctx) family, str_ls (str_long_id #3 (gctx_names gctx) (names cctx)) all] *)
                               in
                                 case all of x :: _ => ConstrH (x, TrueH) | [] => raise Incon "empty datatype"
                               end
                             | _ => TrueH (* an abstract type is treated as an inhabited type *)
                          )
                        | Unit _ => TTH
                        | Prod (t1, t2) => PairH (loop $ check_size (t1, []), loop $ check_size (t2, []))
                        | _ => TrueH
                                 (* val () = println "Found" *)
                in
                  ret
                end
            | c :: cs =>
              let
                (* val () = Debug.println (sprintf "try to satisfy $" [(join ", " o map (str_cover (names cctx))) (c :: cs)]) *)
                (* val () = println $ sprintf "try to satisfy $" [str_cover (names cctx) c] *)
                fun conflict_half a b =
                  case (a, b) of
                      (PairC _, ConstrC _) => true
                    | (PairC _, TTC) => true
                    | (ConstrC _, TTC) => true
                    | _ => false
                fun conflict a b = conflict_half a b orelse conflict_half b a
                val () = app (fn c' => if conflict c c' then ((* println "conflict";  *)raise Incon "conflict") else ()) cs
                (* firstly try to test for concrete cases *)
                val result =
                    case (c, t) of
                        (TTC, Unit _) =>
                        (case allSome (fn c => case c of TTC => SOME () | _ => NONE) cs of
                             OK _ => inl TTH
                           | Failed (i, dissident) =>
                             if conflict c dissident then
                               raise Incon "conflicts on tt"
                             else
                               inr (dissident, c :: remove i cs, t)
                        )
                      | (PairC (c1, c2), Prod (t1, t2)) =>
                        (case allSome (fn c => case c of PairC p => SOME p | _ => NONE ) cs of
                             OK cs =>
                             let
                               val (cs1, cs2) = unzip cs
                               val c1 = loop $ check_size (t1, c1 :: cs1)
                               val c2 = loop $ check_size (t2, c2 :: cs2)
                             in
                               inl $ PairH (c1, c2)
                             end
                           | Failed (i, dissident) =>
                             if conflict c dissident then
                               raise Incon "conflicts on pair"
                             else
                               inr (dissident, c :: remove i cs, t)
                        )
                      | (ConstrC (x, c'), AppV (_, ts, _, _)) =>
                        let
                          fun same_constr c =
                            case c of
                                ConstrC (y, c) =>
                                if eq_long_id (y, x) then
                                  SOME c
                                else
                                  raise Incon "diff-constr"
                              | _ => NONE
                        in
                          case allSome same_constr cs of
                              OK cs' =>
                              let
                                val (_, _, ibinds) = fetch_constr gctx (cctx, x)
                                val (_, (t', _)) = unfold_binds ibinds
		                val t' = subst_ts_mt ts t'
                                (* val () = (* Debug. *)println (sprintf "All are $, now try to satisfy $" [str_v (names cctx) x, (join ", " o map (str_cover (names cctx))) (c' :: cs')]) *)
                                val c' = loop $ check_size (t', c' :: cs')
                                              (* val () = Debug.println (sprintf "Plugging $ into $" [str_habitant (names cctx) c', str_v (names cctx) x]) *)
                              in
                                inl $ ConstrH (x, c')
                              end
                            | Failed (i, dissident) =>
                              if conflict c dissident then
                                raise Incon $ "conflicts on constructor " ^ str_int (fst $ snd x)
                              else
                                inr (dissident, c :: remove i cs, t)
                        end
                      | _ => inr (c, cs, t)
                val ret =
                    case result of
                        inl hab => hab
                      | inr (c, cs, t) =>
                        case (c, t) of
                            (TrueC, _) => loop $ check_size (t, cs)
                          | (FalseC, _) => raise Incon "false"
                          | (AndC (c1, c2), _) => loop $ check_size (t, c1 :: c2 :: cs)
                          | (OrC (c1, c2), _) =>
                            (loop $ check_size (t, c1 :: cs) handle Incon _ => loop $ check_size (t, c2 :: cs))
                          | _ => raise impossible "find_hab()"
                                       (* val () = println (sprintf "Done find_hab on type $" [str_mt (gctx_names gctx) (sctx_names sctx, names kctx) t]) *)
              in
                ret
              end
        end
      val ret = 
          SOME (loop (t, cs, ()))
          handle
          Incon debug =>
          let
            (* val () = println $ "Can't find a habitant because: " ^ debug *)
          in
            NONE
          end
            (* val () = println "find_hab() end" *)
    in
      ret
    end

in              

fun any_missing deep gctx ctx t c =
  let
    (* val t = normalize_mt t *)
    val nc = cover_neg gctx ctx t c
    (* val () = println "after cover_neg()" *)
    (* val () = (* Debug. *)println (str_cover (names (#3 ctx)) nc) *)
    (* val () = println "before find_hab()" *)
    val ret = find_hab deep gctx ctx t [nc]
                       (* val () = println "after find_hab()" *)
  in
    ret
  end

fun is_redundant gctx (ctx, t, prevs, this) =
  let
    (* fun is_covered ctx t small big = *)
    (*     (isNull o (* (trace "after any_missing()") o *) any_missing true(*treat empty datatype as uninhabited*) ctx t o (* (trace "after cover_imply()") o *) cover_imply ctx t) (small, big) *)
    (* val t = normalize_mt t *)
    val prev = combine_covers prevs
    (* val () = println "after combine_covers()" *)
    (* val something_new = not (is_covered ctx t this prev) *)
    val something_new = isSome $ find_hab true(*treat empty datatype as uninhabited*) gctx ctx t $ [this, cover_neg gctx ctx t prev]                                  
                               (* val () = println "after find_hab()" *)
  in
    something_new
  end
    
fun check_redundancy gctx (ctx as (_, _, cctx), t, prevs, this, r) =
  let
  in
    if is_redundant gctx (ctx, t, prevs, this) then ()
    else
      raise Error (r, sprintf "Redundant rule: $" [str_cover (gctx_names gctx) (names cctx) this] :: indent [sprintf "Has already been covered by previous rules: $" [(join ", " o map (str_cover (gctx_names gctx) (names cctx))) prevs]])
  end
    
fun is_exhaustive gctx (ctx as (_, _, cctx), t : mtype, covers) =
  let
    (* val t = normalize_mt t *)
    val cover = combine_covers covers
                               (* val () = Debug.println (str_cover (names cctx) cover) *)
  in
    any_missing true(*treat empty datatype as uninhabited*) gctx ctx t cover
  end
    
fun check_exhaustion gctx (ctx as (_, _, cctx), t : mtype, covers, r) =
  let
  in
    case is_exhaustive gctx (ctx, t, covers) of
        NONE => ()
      | SOME missed =>
	raise Error (r, [sprintf "Not exhaustive, at least missing this case: $" [str_habitant (gctx_names gctx) (names cctx) missed]])
  end

end

fun get_ds (_, _, _, tctxd) = map (snd o snd) tctxd

fun escapes nametype name domaintype domain cause =
  [sprintf "$ $ escapes local scope in $ $" [nametype, name, domaintype, domain]] @ indent (if cause = "" then [] else ["cause: it is (potentially) used by " ^ cause])
	                                                                                   
fun forget_mt r gctxn (skctxn as (sctxn, kctxn)) (sctxl, kctxl) t = 
  let val t = forget_t_mt 0 kctxl t
	      handle ForgetError (x, cause) => raise Error (r, escapes "type variable" (str_v kctxn x) "type" (str_mt gctxn skctxn t) cause)
      val t = forget_i_mt 0 sctxl t
	      handle ForgetError (x, cause) => raise Error (r, escapes "index variable" (str_v sctxn x) "type" (str_mt gctxn skctxn t) cause)
  in
    t
  end

fun forget_ctx_mt r gctx (sctx, kctx, _, _) (sctxd, kctxd, _, _) t =
  let val (sctxn, kctxn) = (sctx_names sctx, names kctx)
      val sctxl = sctx_length sctxd
  in
    forget_mt r (gctx_names gctx) (sctxn, kctxn) (sctxl, length kctxd) t
  end
    
fun forget_t r gctxn (skctxn as (sctxn, kctxn)) (sctxl, kctxl) t = 
  let val t = forget_t_t 0 kctxl t
	      handle ForgetError (x, cause) => raise Error (r, escapes "type variable" (str_v kctxn x) "type" (str_t gctxn skctxn t) cause)
      val t = forget_i_t 0 sctxl t
	      handle ForgetError (x, cause) => raise Error (r, escapes "index variable" (str_v sctxn x) "type" (str_t gctxn skctxn t) cause)
  in
    t
  end

fun forget_ctx_t r gctx (sctx, kctx, _, _) (sctxd, kctxd, _, _) t =
  let val (sctxn, kctxn) = (sctx_names sctx, names kctx)
      val sctxl = sctx_length sctxd
  in
    forget_t r (gctx_names gctx) (sctxn, kctxn) (sctxl, length kctxd) t
  end
    
fun forget_d r gctxn sctxn sctxl d =
  forget_i_i 0 sctxl d
  handle ForgetError (x, cause) => raise Error (r, escapes "index variable" (str_v sctxn x) "time" (str_i gctxn sctxn d) cause)

(* val anno_less = ref true *)
val anno_less = ref false

fun substx_i_i_nonconsuming x v b =
  let
    val v = forget_i_i x 1 v
  in
    shiftx_i_i x 1 $ substx_i_i x v b
  end
    
fun substx_i_p_nonconsuming x v b =
  let
    val v = forget_i_i x 1 v
  in
    shiftx_i_p x 1 $ substx_i_p x v b
  end
    
fun forget_ctx_d r gctx (sctx, _, _, _) (sctxd, _, _, _) d =
  let
    val sctxn = sctx_names sctx
    val sctxl = sctx_length sctxd
    val d = 
        case (!anno_less, sctxd) of
            (true, (_, Subset (bs, Bind (name, BinConn (And, p1, p2)), r)) :: sorts') =>
            let
              val ps = collect_And p1
              fun change (p, (d, p2)) =
                case p of
                    BinPred (EqP, VarI (NONE, (x, _)), i) =>
                    (substx_i_i_nonconsuming x i d,
                     substx_i_p_nonconsuming x i p2)
                  | _ => (d, p2)
              val (d, p2) = foldl change (d, p2) ps
              exception Prop2IdxError
              fun prop2idx p =
                case p of
                    BinPred (opr, i1, i2) =>
                    let
                      val opr =
                          case opr of
                              EqP => EqI
                            | LtP => LtI
                            | GeP => GeI
                            | _ => raise Prop2IdxError                       
                    in
                      BinOpI (opr, i1, i2)
                    end
                  | BinConn (opr, p1, p2) =>
                    let
                      val opr =
                          case opr of
                              And => AndI
                            | _ => raise Prop2IdxError                       
                    in
                      BinOpI (opr, prop2idx p1, prop2idx p2)
                    end
                  | _ => raise Prop2IdxError                       
            in
              Ite (prop2idx p2, d, T0 dummy, dummy)
              handle Prop2IdxError => d
            end
          | _ => d
  in
    forget_d r (gctx_names gctx) sctxn sctxl d
  end

fun mismatch gctx (ctx as (sctx, kctx, _, _)) e expect got =  
  (get_region_e e,
   "Type mismatch:" ::
   indent ["expect: " ^ expect, 
           "got: " ^ str_t gctx (sctx, kctx) got,
           "in: " ^ str_e gctx ctx e])

fun mismatch_anno gctx ctx expect got =  
  (get_region_t got,
   "Type annotation mismatch:" ::
   indent ["expect: " ^ expect,
           "got: " ^ str_t gctx ctx got])

fun is_wf_return gctx (skctx as (sctx, _), return) =
  case return of
      (SOME t, SOME d) =>
      (SOME (check_kind_Type gctx (skctx, t)),
       SOME (check_bsort gctx (sctx, d, Base Time)))
    | (SOME t, NONE) =>
      (SOME (check_kind_Type gctx (skctx, t)),
       NONE)
    | (NONE, SOME d) =>
      (NONE,
       SOME (check_bsort gctx (sctx, d, Base Time)))
    | (NONE, NONE) => (NONE, NONE)

fun str_sctx gctx sctx =
  snd $ foldr (fn ((name, sort), (sctxn, acc)) => (name :: sctxn, (name, str_s (gctx_names gctx) sctxn sort) :: acc)) ([], []) sctx
      
(* t is already checked for wellformedness *)
fun match_ptrn gctx (ctx as (sctx : scontext, kctx : kcontext, cctx : ccontext), (* pcovers, *) pn : U.ptrn, t : mtype) : ptrn * cover * context * int =
  let
    val match_ptrn = match_ptrn gctx
    val gctxn = gctx_names gctx
    val skctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
  in
    case pn of
	U.ConstrP ((cx, eia), inames, opn, r) =>
        (case whnf_mt gctx kctx t of
             AppV (family, ts, is, _) =>
 	     let 
               val c as (family', tnames, ibinds) = fetch_constr gctx (cctx, cx)
               val (name_sorts, (t1, is')) = unfold_binds ibinds
               val () = if eia then () else raise Impossible "eia shouldn't be false"
	       val () = unify_mt r gctx (sctx, kctx) (MtVar family', MtVar family)
                        handle
                        Error _ =>
                        let
                          val expect = str_long_id #2 gctxn kctxn family
                          val got = str_long_id #2 gctxn kctxn family'
                        in
                          raise Error
                                (r, sprintf "Type of constructor $ doesn't match datatype " [str_long_id #3 gctxn (names cctx) cx] ::
                                    indent ["expect: " ^ expect,
                                            "got: " ^ got])
                        end
	       val () = if length tnames = length ts then ()
                        else
                          raise Error 
                                (r, sprintf "Type of constructor $ doesn't match datatype " [str_long_id #3 gctxn (names cctx) cx] :: 
                                    indent ["expect number of type arguments: " ^ (str_int $ length ts),
                                            "got: " ^ (str_int $ length tnames)])
	       val () = if length is' = length is then ()
                        else
                          raise Error 
                                (r, sprintf "Type of constructor $ doesn't match datatype " [str_long_id #3 gctxn (names cctx) cx] :: 
                                    indent ["expect number of index arguments: " ^ (str_int $ length is),
                                            "got: " ^ (str_int $ length is')])
               val () =
                   if length inames = length name_sorts then ()
                   else raise Error (r, [sprintf "This constructor requires $ index argument(s), not $" [str_int (length name_sorts), str_int (length inames)]])
	       val t1 = subst_ts_mt ts t1
	       val is = map (shiftx_i_i 0 (length name_sorts)) is
	       val ps = ListPair.map (fn (a, b) => BinPred (EqP, a, b)) (is', is)
               (* val () = println "try piggyback:" *)
               (* val () = println $ str_ls (fn (name, sort) => sprintf "$: $" [name, sort]) $ str_sctx gctx $ rev name_sorts *)
               val sorts = rev $ map snd name_sorts
               val sorts =
                   case (!anno_less, sorts) of
                       (true, Subset (bs, Bind (name, p), r) :: sorts') =>
                       (* piggyback the equalities on a Subset sort *)
                       let
                         (* val () = println "piggyback!" *)
                       in
                         Subset (bs, Bind (name, combine_And ps /\ p), r) :: sorts'
                       end
                     | _ => sorts
               val ctxd = ctx_from_full_sortings o ListPair.zip $ (rev inames, sorts)
               val () = open_ctx ctxd
               val () = open_premises ps
               val ctx = add_ctx_skc ctxd ctx
               val pn1 = default (U.TTP dummy) opn
               val (pn1, cover, ctxd', nps) = match_ptrn (ctx, pn1, t1)
               val ctxd = add_ctx ctxd' ctxd
               val cover = ConstrC (cx, cover)
             in
	       (ConstrP ((cx, eia), inames, SOME pn1, r), cover, ctxd, length ps + nps)
	     end
           | _ => raise Error (r, [sprintf "Pattern $ doesn't match type $" [U.str_pn gctxn (sctx_names sctx, names kctx, names cctx) pn, str_mt gctxn skctxn t]])
        )
      | U.VarP (name, r) =>
        (* let *)
        (*   val pcover = combine_covers pcovers *)
        (*   val cover = cover_neg cctx t pcover *)
        (* in *)
        (* end *)
        (VarP (name, r), TrueC, ctx_from_typing (name, Mono t), 0)
      | U.PairP (pn1, pn2) =>
        let 
          val r = U.get_region_pn pn
          val t1 = fresh_mt (sctx, kctx) r
          val t2 = fresh_mt (sctx, kctx) r
          (* val () = println $ sprintf "before: $ : $" [U.str_pn (sctxn, kctxn, names cctx) pn, str_mt skctxn t] *)
          val () = unify_mt r gctx (sctx, kctx) (t, Prod (t1, t2))
          (* val () = println "after" *)
          val (pn1, cover1, ctxd, nps1) = match_ptrn (ctx, pn1, t1)
          val ctx = add_ctx_skc ctxd ctx
          val (pn2, cover2, ctxd', nps2) = match_ptrn (ctx, pn2, shift_ctx_mt ctxd t2)
          val ctxd = add_ctx ctxd' ctxd
        in
          (PairP (pn1, pn2), PairC (cover1, cover2), ctxd, nps1 + nps2)
        end
      | U.TTP r =>
        let
          val () = unify_mt r gctx (sctx, kctx) (t, Unit dummy)
        in
          (TTP r, TTC, empty_ctx, 0)
        end
      | U.AliasP ((pname, r1), pn, r) =>
        let val ctxd = ctx_from_typing (pname, Mono t)
            val (pn, cover, ctxd', nps) = match_ptrn (ctx, pn, t)
            val ctxd = add_ctx ctxd' ctxd
        in
          (AliasP ((pname, r1), pn, r), cover, ctxd, nps)
        end
      | U.AnnoP (pn1, t') =>
        let
          val t' = check_kind_Type gctx ((sctx, kctx), t')
          val () = unify_mt (U.get_region_pn pn) gctx (sctx, kctx) (t, t')
          val (pn1, cover, ctxd, nps) = match_ptrn (ctx, pn1, t')
        in
          (AnnoP (pn1, t'), cover, ctxd, nps)
        end
  end

fun update_t t =
  case t of
      Mono t => Mono (update_mt t)
    | Uni (Bind (name, t), r) => Uni (Bind (name, update_t t), r)

fun update_k k = mapSnd (map update_s) k

fun update_ke (dt, k, t) = (dt, update_k k, Option.map update_mt t)

fun update_c (x, tnames, ibinds) =
  let
    val (ns, (t, is)) = unfold_binds ibinds
    val ns = map (mapSnd update_s) ns
    val t = update_mt t
    val is = map update_i is
    val ibinds = fold_binds (ns, (t, is))
  in
    (x, tnames, ibinds)
  end

fun update_ctx (sctx, kctx, cctx, tctx) =
  let
    val sctx = map (mapSnd update_s) sctx
    val kctx = map (mapSnd update_ke) kctx
    val cctx = map (mapSnd update_c) cctx
    val tctx = map (mapSnd update_t) tctx
  in
    (sctx, kctx, cctx, tctx)
  end

fun update_sgntr sg =
  case sg of
      Sig ctx => Sig $ update_ctx ctx
    | FunctorBind ((arg_name, arg), body) =>
      FunctorBind ((arg_name, update_ctx arg), update_ctx body)

fun update_gctx gctx =
  map (mapSnd update_sgntr) gctx
      
fun fresh_uvar_mt t =
  let
  in      
    case update_mt t of
        UVar (uvar_ref, _) => [uvar_ref]
      | Unit _ => []
      | Arrow (t1, _, t2) => fresh_uvar_mt t1 @ fresh_uvar_mt t2
      | TyArray (t, _) => fresh_uvar_mt t
      | TyNat _ => []
      | Prod (t1, t2) => fresh_uvar_mt t1 @ fresh_uvar_mt t2
      | UniI (s, Bind (name, t1), _) => fresh_uvar_mt t1
      | MtVar x => []
      | MtAbs (_, Bind (_, t), _) => fresh_uvar_mt t
      | MtApp (t1, t2) => fresh_uvar_mt t1 @ fresh_uvar_mt t2
      | MtAbsI (_, Bind (_, t), _) => fresh_uvar_mt t
      | MtAppI (t, i) => fresh_uvar_mt t
      | AppV (y, ts, is, r) => concatMap fresh_uvar_mt ts
      | BaseType _ => []
  end
    
fun fresh_uvar_t t =
  case t of
      Mono t => fresh_uvar_mt t
    | Uni _ => [] (* fresh uvars in Uni should either have been generalized or in previous ctx *)

(* If i1 or i2 is fresh, do unification instead of VC generation. Could be unsound. *)
fun smart_write_le gctx ctx (i1, i2, r) =
  let
    (* val () = println $ sprintf "Check Le : $ <= $" [str_i ctx i1, str_i ctx i2] *)
    fun is_fresh_i i =
      case i of
          UVarI (x, _) =>
          (case !x of
               Fresh _ => true
             | Refined _ => false
          )
        | _ => false
  in
    if is_fresh_i i1 orelse is_fresh_i i2 then unify_i r gctx ctx (i1, i2)
    else write_le (i1, i2, r)
  end
    
fun expand_rules gctx (ctx as (sctx, kctx, cctx), rules, t, r) =
  let
    fun expand_rule (rule as (pn, e), (pcovers, rules)) =
      let
        (* val () = println "before match_ptrn()" *)
	val (pn, cover, ctxd, nps) = match_ptrn gctx (ctx, (* pcovers, *) pn, t)
        (* val () = println "after match_ptrn()" *)
        val () = close_n nps
        val () = close_ctx ctxd
        (* val cover = ptrn_to_cover pn *)
        (* val () = println "before check_redundancy()" *)
        val () = check_redundancy gctx (ctx, t, pcovers, cover, get_region_pn pn)
        (* val () = println "after check_redundancy()" *)
        val (pcovers, new_rules) =
            case (pn, e) of
                (VarP _, U.Never (U.UVar ((), _), _)) =>
                let
                  fun hab_to_ptrn cctx (* cutoff *) t hab =
                    let
                      (* open UnderscoredExpr *)
                      (* exception Error of string *)
                      (* fun runError m () = *)
                      (*   SOME (m ()) handle Error _ => NONE *)
                      fun loop (* cutoff *) t hab =
                        let
                          (* val t = normalize_mt t *)
                          val t = whnf_mt gctx kctx t
                        in
                          case (hab, t) of
                              (ConstrH (x, h'), AppV (family, ts, _, _)) =>
                              let
                                val (_, _, ibinds) = fetch_constr gctx (cctx, x)
                                val (name_sorts, (t', _)) = unfold_binds ibinds
	                        val t' = subst_ts_mt ts t'
                                (* cut-off so that [expand_rules] won't try deeper and deeper proposals *) 
                                val pn' =
                                    loop (* (cutoff - 1) *) t' h'
                                         (* if cutoff > 0 then *)
                                         (*   loop (cutoff - 1) t' h' *)
                                         (* else *)
                                         (*   VarP ("_", dummy) *)
                              in
                                ConstrP ((x, true), repeat (length name_sorts) "_", SOME pn', dummy)
                              end
                            | (TTH, Unit _) =>
                              TTP dummy
                            | (PairH (h1, h2), Prod (t1, t2)) =>
                              PairP (loop (* cutoff *) t1 h1, loop (* cutoff *) t2 h2)
                            | (TrueH, _) => VarP ("_", dummy)
                            | _ => raise Impossible "hab_to_ptrn"
                        end
                    in
                      (* runError (fn () => loop t hab) () *)
                      loop (* cutoff *) t hab
                    end
                  fun ptrn_to_cover pn =
                    let
                      (* open UnderscoredExpr *)
                    in
                      case pn of
                          ConstrP ((x, _), _, pn, _) => ConstrC (x, default TrueC $ Option.map ptrn_to_cover pn)
                        | VarP _ => TrueC
                        | PairP (pn1, pn2) => PairC (ptrn_to_cover pn1, ptrn_to_cover pn2)
                        | TTP _ => TTC
                        | AliasP (_, pn, _) => ptrn_to_cover pn
                        | AnnoP (pn, _) => ptrn_to_cover pn
                    end
                  fun convert_pn pn =
                    case pn of
                        TTP a => U.TTP a
                      | PairP (pn1, pn2) => U.PairP (convert_pn pn1, convert_pn pn2)
                      | ConstrP (x, inames, opn, r) => U.ConstrP (x, inames, Option.map convert_pn opn, r) 
                      | VarP a => U.VarP a
                      | AliasP (name, pn, r) => U.AliasP (name, convert_pn pn, r)
                      | AnnoP _ => raise Impossible "convert_pn can't convert AnnoP"
                  fun loop pcovers =
                    case any_missing false(*treat empty datatype as inhabited, so as to get a shorter proposal*) gctx ctx t $ combine_covers pcovers of
                        SOME hab =>
                        let
                          val pn = hab_to_ptrn cctx (* 10 *) t hab
                          (* val () = println $ sprintf "New pattern: $" [str_pn (names sctx, names kctx, names cctx) pn] *)
                          val (pcovers, rules) = loop $ pcovers @ [ptrn_to_cover pn]
                        in
                          (pcovers, [(convert_pn pn, e)] @ rules)
                        end
                      | NONE => (pcovers, [])
                  val (pcovers, rules) = loop pcovers
                in
                  (pcovers, rules)
                end
              | _ => (pcovers @ [cover], [rule])
      in
        (pcovers, rules @ new_rules)
      end
    val (pcovers, rules) = foldl expand_rule ([], []) $ rules
    val () = check_exhaustion gctx (ctx, t, pcovers, r);
  in
    rules
  end

fun forget_or_check_return r gctx ctx ctxd (t', d') (t, d) =
  let
    val gctxn = gctx_names gctx
    val (sctx, kctx, _, _) = ctx
    val (sctxn, kctxn, _, _) = ctx_names ctx
    val t =
        case t of
            SOME t =>
            let
              val () = unify_mt r gctx (sctx, kctx) (t', shift_ctx_mt ctxd t)
            in
              t
            end
          | NONE =>
            let
	      val t' = forget_ctx_mt r gctx ctx ctxd t' 
            in
              t'
            end
    val d = 
        case d of
            SOME d =>
            let
              val () = smart_write_le gctxn sctxn (d', shift_ctx_i ctxd d, r)
            in
              d
            end
          | NONE =>
            let 
	      val d' = forget_ctx_d r gctx ctx ctxd d'
            in
              d'
            end
  in
    (t, d)
  end

(* change sort [s] to a [Subset (s.bsort, p)] *)
fun set_prop r s p =
  case normalize_s s of
      Basic (bs as (_, r)) => Subset (bs, Bind (("__set_prop", r), p), r)
    | Subset (bs, Bind (name, _), r) => Subset (bs, Bind (name, p), r)
    | SortBigO s => set_prop r (SortBigO_to_Subset s) p
    | UVarS _ => raise Error (r, ["unsolved unification variable in module"])
    | SAbs _ => raise Impossible "set_prop()/SAbs: shouldn't be prop"
    | SApp _ => raise Error (r, ["unsolved unification variable in module (unnormalized application)"])
                      
fun add_prop r s p =
  case normalize_s s of
      Basic (bs as (_, r)) => Subset (bs, Bind (("__added_prop", r), p), r)
    | Subset (bs, Bind (name, p'), r) => Subset (bs, Bind (name, p' /\ p), r)
    | SortBigO s => add_prop r (SortBigO_to_Subset s) p
    | UVarS _ => raise Error (r, ["unsolved unification variable in module"])
    | SAbs _ => raise Impossible "add_prop()/SAbs: shouldn't be prop"
    | SApp _ => raise Error (r, ["unsolved unification variable in module (unnormalized application)"])
                             
fun sort_add_idx_eq r s' i =
  add_prop r s' (VarI (NONE, (0, r)) %= shift_i_i i)
           
type typing_info = decl list * context * idx list * context

fun str_typing_info gctxn (sctxn, kctxn) (ctxd : context, ds) =
  let
    fun on_ns ((name, s), (acc, sctxn)) =
      ([sprintf "$ ::: $" [name, str_s gctxn sctxn s](* , "" *)] :: acc, name :: sctxn)
    val (idx_lines, sctxn) = foldr on_ns ([], sctxn) $ #1 $ ctxd
    val idx_lines = List.concat $ rev idx_lines
    fun on_nk ((name, k), (acc, kctxn)) =
      ([sprintf "$ :: $" [name, str_ke gctxn (sctxn, kctxn) k](* , "" *)] :: acc, name :: kctxn)
    val (type_lines, kctxn) = foldr on_nk ([], kctxn) $ #2 $ ctxd
    val type_lines = List.concat $ rev type_lines
    val expr_lines =
        (concatMap (fn (name, t) => [sprintf "$ : $" [name, str_t gctxn (sctxn, kctxn) t](* , "" *)]) o rev o #4) ctxd
    val time_lines =
        "Times:" :: "" ::
        (concatMap (fn d => [sprintf "|> $" [str_i gctxn sctxn d](* , "" *)])) ds
    val lines = 
        idx_lines
        @ type_lines
        @ expr_lines
            (* @ time_lines  *)
  in
    lines
  end
    
fun str_sig gctxn ctx =
  ["sig"] @
  indent (str_typing_info gctxn ([], []) (ctx, [])) @
  ["end"]
    
fun str_gctx old_gctxn gctx =
  let 
    fun str_sigging ((name, sg), (acc, gctxn)) =
      let
        val (ls, gctxnd) =
            case sg of
                Sig ctx =>
                ([sprintf "structure $ : " [name] ] @
                 indent (str_sig gctxn ctx),
                 [(name, ctx_names ctx)])
              | FunctorBind ((arg_name, arg), body) =>
                ([sprintf "functor $ (structure $ : " [name, arg_name] ] @
                 indent (str_sig gctxn arg) @
                 [") : "] @
                 indent (str_sig ((arg_name, ctx_names arg) :: gctxn) body),
                 [])
      in
        (ls :: acc, gctxnd @ gctxn)
      end
    val typing_lines = List.concat $ rev $ fst $ foldr str_sigging ([], old_gctxn) gctx
    val lines = 
        typing_lines @
        [""]
  in
    lines
  end

fun get_mtype gctx (ctx as (sctx : scontext, kctx : kcontext, cctx : ccontext, tctx : tcontext), e_all : U.expr) : expr * mtype * idx =
  let
    val get_mtype = get_mtype gctx
    val check_mtype = check_mtype gctx
    val check_time = check_time gctx
    val check_mtype_time = check_mtype_time gctx
    val check_decl = check_decl gctx
    val check_decls = check_decls gctx
    val check_rule = check_rule gctx
    val check_rules = check_rules gctx
    val skctx = (sctx, kctx)
    val gctxn = gctx_names gctx
    val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
    val skctxn = (sctxn, kctxn)
    fun print_ctx gctx (ctx as (sctx, kctx, _, tctx)) =
      let
        val () = println $ str_ls (fn (name, sort) => sprintf "$: $" [name, sort]) $ str_sctx gctx sctx
                         (* val () = println $ str_ls fst kctx *)
                         (* val () = str_ls (fn (nm, t) => println $ sprintf "$: $" [nm, str_t (gctx_names gctx) (sctx_names sctx, names kctx) t]) tctx *)
      in
        ()
      end
    (* val () = print $ sprintf "Typing $\n" [U.str_e gctxn ctxn e_all] *)
    (* val () = print_ctx gctx ctx *)
    fun main () =
      case e_all of
	  U.Var (info as (x, eia)) =>
          let
            val r = U.get_region_long_id x
            fun insert_type_args t =
              case t of
                  Mono t => t
                | Uni (Bind (_, t), _) =>
                  let
                    (* val t_arg = fresh_mt (sctx, kctx) r *)
                    (* val () = println $ str_mt skctxn t_arg *)
                    val t_arg = U.UVar ((), r)
                    val t_arg = check_kind_Type gctx (skctx, t_arg)
                    val t = subst_t_t t_arg t
                    (* val () = println $ str_t skctxn t *)
                    val t = insert_type_args t
                  in
                    t
                  end
            val t = fetch_type gctx (tctx, x)
            (* val () = println $ str_t skctxn t *)
            val t = insert_type_args t
            (* val () = println $ str_mt skctxn t *)
            fun insert_idx_args t_all =
              case t_all of
                  UniI (s, Bind ((name, _), t), _) =>
                  let
                    (* val bs = fresh_bsort () *)
                    (* val i = fresh_i sctx bs r *)
                    (* val bs =  get_base r sctxn s *)
                    val i = U.UVarI ((), r)
                    val i = check_sort gctx (sctx, i, s)
                    val t = subst_i_mt i t
                  in
                    insert_idx_args t
                  end
                | _ => t_all
            val t = if not eia then
                      insert_idx_args t
                    else
                      t
          in
            (Var info, t, T0 dummy)
          end
	| U.App (e1, e2) =>
	  let
            val (e2, t2, d2) = get_mtype (ctx, e2)
            val r = U.get_region_e e1
            val d = fresh_i sctx (Base Time) r
            val t = fresh_mt (sctx, kctx) r
            val (e1, _, d1) = check_mtype (ctx, e1, Arrow (t2, d, t))
            val ret = (App (e1, e2), t, d1 %+ d2 %+ T1 dummy %+ d) 
          in
            ret
	  end
	| U.BinOp (New, e1, e2) =>
          let
            val r = U.get_region_e e_all
            val i = fresh_i sctx (Base Time) r
            val (e1, _, d1) = check_mtype (ctx, e1, TyNat (i, r))
            val (e2, t, d2) = get_mtype (ctx, e2)
          in
            (BinOp (New, e1, e2), TyArray (t, i), d1 %+ d2)
          end
	| U.BinOp (Read, e1, e2) =>
          let
            val r = U.get_region_e e_all
            val t = fresh_mt (sctx, kctx) r
            val i1 = fresh_i sctx (Base Time) r
            val i2 = fresh_i sctx (Base Time) r
            val (e1, _, d1) = check_mtype (ctx, e1, TyArray (t, i1))
            val (e2, _, d2) = check_mtype (ctx, e2, TyNat (i2, r))
            val () = write_le (i2, i1, r)
          in
            (BinOp (Read, e1, e2), t, d1 %+ d2)
          end
	| U.TriOp (Write, e1, e2, e3) =>
          let
            val r = U.get_region_e e_all
            val t = fresh_mt (sctx, kctx) r
            val i1 = fresh_i sctx (Base Time) r
            val i2 = fresh_i sctx (Base Time) r
            val (e1, _, d1) = check_mtype (ctx, e1, TyArray (t, i1))
            val (e2, _, d2) = check_mtype (ctx, e2, TyNat (i2, r))
            val () = write_le (i2, i1, r)
            val (e3, _, d3) = check_mtype (ctx, e3, t)
          in
            (TriOp (Write, e1, e2, e3), Unit r, d1 %+ d2 %+ d3)
          end
	| U.Abs (pn, e) => 
	  let
            val r = U.get_region_pn pn
            val t = fresh_mt (sctx, kctx) r
            val skcctx = (sctx, kctx, cctx) 
            val (pn, cover, ctxd, nps (* number of premises *)) = match_ptrn gctx (skcctx, pn, t)
	    val () = check_exhaustion gctx (skcctx, t, [cover], get_region_pn pn)
            val ctx = add_ctx ctxd ctx
	    val (e, t1, d) = get_mtype (ctx, e)
	    val t1 = forget_ctx_mt (get_region_e e) gctx ctx ctxd t1 
            val d = forget_ctx_d (get_region_e e) gctx ctx ctxd d
            val () = close_n nps
            val () = close_ctx ctxd
          in
	    (Abs (pn, e), Arrow (t, d, t1), T0 dummy)
	  end
	| U.Let (return, decls, e, r) => 
	  let
            val return = is_wf_return gctx (skctx, return)
            val (decls, ctxd as (sctxd, kctxd, _, _), nps, ds, ctx) = check_decls (ctx, decls)
	    val (e, t, d) = get_mtype (ctx, e)
            val ds = rev (d :: ds)
            val d = combine_AddI_Time ds
            (* val d = foldl' (fn (d, acc) => acc %+ d) (T0 dummy) ds *)
	    (* val t = forget_ctx_mt r ctx ctxd t  *)
            (* val ds = map (forget_ctx_d r ctx ctxd) ds *)
	    val (t, d) = forget_or_check_return (get_region_e e) gctx ctx ctxd (t, d) return 
            val () = close_n nps
            val () = close_ctx ctxd
          in
	    (Let (return, decls, e, r), t, d)
	  end
	| U.AbsI (s, (name, r), e, r_all) => 
	  let 
	    val () = if U.is_value e then ()
		     else raise Error (U.get_region_e e, ["The body of a universal abstraction must be a value"])
            val s = is_wf_sort gctx (sctx, s)
            val ctxd = ctx_from_sorting (name, s)
            val ctx = add_ctx ctxd ctx
            val () = open_ctx ctxd
	    val (e, t, _) = get_mtype (ctx, e) 
            val () = close_ctx ctxd
          in
	    (AbsI (s, (name, r), e, r_all), UniI (s, Bind ((name, r), t), r_all), T0 r_all)
	  end 
	| U.AppI (e, i) =>
	  let 
            val r = U.get_region_e e
            val s = fresh_sort sctx r
            val t1 = fresh_mt (sctx, kctx) r
            val (e, t, d) = check_mtype (ctx, e, UniI (s, Bind (("_", r), t1), r)) 
            val i = check_sort gctx (sctx, i, s) 
          in
	    (AppI (e, i), subst_i_mt i t1, d)
	  end
	| U.TT r => 
          (TT r, Unit dummy, T0 dummy)
	| U.Pair (e1, e2) => 
	  let 
            val (e1, t1, d1) = get_mtype (ctx, e1) 
	    val (e2, t2, d2) = get_mtype (ctx, e2) 
          in
	    (Pair (e1, e2), Prod (t1, t2), d1 %+ d2)
	  end
	| U.Fst e => 
	  let 
            val r = U.get_region_e e
            val t1 = fresh_mt (sctx, kctx) r
            val t2 = fresh_mt (sctx, kctx) r
            val (e, _, d) = check_mtype (ctx, e, Prod (t1, t2)) 
          in 
            (Fst e, t1, d)
	  end
	| U.Snd e => 
	  let 
            val r = U.get_region_e e
            val t1 = fresh_mt (sctx, kctx) r
            val t2 = fresh_mt (sctx, kctx) r
            val (e, _, d) = check_mtype (ctx, e, Prod (t1, t2)) 
          in 
            (Snd e, t2, d)
	  end
	| U.Ascription (e, t) => 
	  let val t = check_kind_Type gctx (skctx, t)
	      val (e, _, d) = check_mtype (ctx, e, t)
          in
	    (Ascription (e, t), t, d)
	  end
	| U.AscriptionTime (e, d) => 
	  let val d = check_bsort gctx (sctx, d, Base Time)
	      val (e, t) = check_time (ctx, e, d)
          in
	    (AscriptionTime (e, d), t, d)
	  end
	| U.BinOp (Add, e1, e2) =>
	  let val (e1, _, d1) = check_mtype (ctx, e1, BaseType (Int, dummy))
	      val (e2, _, d2) = check_mtype (ctx, e2, BaseType (Int, dummy)) in
	    (BinOp (Add, e1, e2), BaseType (Int, dummy), d1 %+ d2 %+ T1 dummy)
	  end
	| U.ConstInt (n, r) => 
	  (ConstInt (n, r), BaseType (Int, dummy), T0 dummy)
	| U.ConstNat (n, r) => 
	  if n >= 0 then
	    (ConstNat (n, r), TyNat (ConstIN (n, r), r), T0 r)
	  else
	    raise Error (r, ["Natural number constant must be non-negative"])
	| U.AppConstr ((x, eia), is, e) => 
	  let 
            val tc = fetch_constr_type gctx (cctx, x)
	    (* delegate to checking [x {is} e] *)
	    val f = U.Var ((NONE, (0, U.get_region_long_id x)), eia)
	    val f = foldl (fn (i, e) => U.AppI (e, i)) f is
	    val e = U.App (f, U.Subst.shift_e_e e)
            (* val f_name = "__synthesized_constructor" *)
            val f_name = str_long_id #3 (gctx_names gctx) (names cctx) x
	    val (e, t, d) = get_mtype (add_typing_skct (f_name, tc) ctx, e) 
            (* val () = println $ str_i sctxn d *)
            val d = update_i d
            val d = simp_i d
            (* val () = println $ str_i sctxn d *)
            val wrong_d = Impossible "get_mtype (): U.AppConstr: d in wrong form"
	    (* constructor application doesn't incur count *)
            val d =
                case d of
                    ConstIT (_, r) => 
                    if eq_i d (T1 r) then T0 r 
                    else raise wrong_d
                  | (BinOpI (AddI, d1, d2)) => 
                    if eq_i d1 (T1 dummy) then d2
                    else if eq_i d2 (T1 dummy) then d1
                    else raise wrong_d
                  | _ => raise wrong_d
            val (is, e) =
                case e of
                    App (f, e) =>
                    let
                      val (_, is) = collect_AppI f
                    in
                      (is, e)
                    end
                  | _ => raise Impossible "get_mtype (): U.AppConstr: e in wrong form"
            val e = forget_e_e 0 1 e
            val e = AppConstr ((x, eia), is, e)
	  in
	    (e, t, d)
	  end
	| U.Case (e, return, rules, r) => 
	  let
            val return = if !anno_less then (fst return, NONE) else return
            val (e, t1, d1) = get_mtype (ctx, e)
            val return = is_wf_return gctx (skctx, return)
            val rules = expand_rules gctx ((sctx, kctx, cctx), rules, t1, r)
            val (rules, tds) = check_rules (ctx, rules, (t1, return), r)
            fun computed_t () : mtype =
              case map fst tds of
                  [] => raise Error (r, ["Empty case-matching must have a return type clause"])
                | t :: ts => 
                  (map (fn t' => unify_mt r gctx (sctx, kctx) (t, t')) ts; 
                   t)
            fun computed_d () =
              (smart_max_list o map snd) tds
            val (t, d) = mapPair (lazy_default computed_t, lazy_default computed_d) return
	    val ret = (Case (e, return, rules, r), t, d1 %+ d)
          in
            ret
          end
	| U.Never (t, r) => 
          let
	    val t = check_kind_Type gctx (skctx, t)
	    val () = write_prop (False dummy, U.get_region_e e_all)
          in
	    (Never (t, r), t, T0 r)
          end
	| U.Builtin (t, r) => 
          let
	    val t = check_kind_Type gctx (skctx, t)
	    val () = if !is_builtin_enabled then ()
                     else raise Error (r, ["builtin keyword is only available in standard library"])
          in
	    (Builtin (t, r), t, T0 r)
          end
    fun extra_msg () = ["when type-checking"] @ indent [U.str_e gctxn ctxn e_all]
    val (e, t, d) = main ()
    (* handle *)
    (* Error (r, msg) => raise Error (r, msg @ extra_msg ()) *)
    (* | Impossible msg => raise Impossible $ join_lines $ msg :: extra_msg () *)
    val t = simp_mt $ update_mt t
    val d = simp_i $ update_i d
                   (* val () = println $ str_ls id $ #4 ctxn *)
                   (* val () = print (sprintf " Typed $: \n        $\n" [str_e gctxn ctxn e, str_mt gctxn skctxn t]) *)
                   (* val () = print (sprintf "   Time : $: \n" [str_i sctxn d]) *)
                   (* val () = print (sprintf "  type: $ [for $]\n  time: $\n" [str_mt skctxn t, str_e ctxn e, str_i sctxn d]) *)
  in
    (e, t, d)
  end

and check_decl gctx (ctx as (sctx, kctx, cctx, _), decl) =
    let
      val check_decl = check_decl gctx
      val check_decls = check_decls gctx
      val get_mtype = get_mtype gctx
      val check_mtype_time = check_mtype_time gctx
      fun generalize t = 
        let
          fun fv_ctx (_, _, _, tctx) = (concatMap fresh_uvar_t o map snd) tctx (* cctx can't contain uvars *)
          (* substitute uvar with var *)
          fun substu_ibind f x v (Bind (name, b) : ('a * 'b) ibind) = Bind (name, f x v b)
          fun substu_tbind f x v (Bind (name, b) : ('a * 'b) tbind) = Bind (name, f x (v + 1) b)
          fun substu x v (b : mtype) : mtype =
	    case b of
                UVar (y, _) =>
                if y = x then
                  case !y of
                      Fresh (_, (sctx, kctx)) => MtAbsIMany (sctx, MtAbsMany (kctx, TV dummy (v + length kctx), dummy), dummy)
                    | Refined _ => raise Impossible "substu()/UVar: shouldn't be Refined"
                else 
                  b
              | Unit r => Unit r
	      | Arrow (t1, d, t2) => Arrow (substu x v t1, d, substu x v t2)
              | TyNat (i, r) => TyNat (i, r)
              | TyArray (t, i) => TyArray (substu x v t, i)
	      | Prod (t1, t2) => Prod (substu x v t1, substu x v t2)
	      | UniI (s, bind, r) => UniI (s, substu_ibind substu x v bind, r)
              (* don't need to consult type variable's definition *)
              | MtVar x => MtVar x
              | MtAbs (k, bind, r) => MtAbs (k, substu_tbind substu x v bind, r)
              | MtApp (t1, t2) => MtApp (substu x v t1, substu x v t2)
              | MtAbsI (k, bind, r) => MtAbsI (k, substu_ibind substu x v bind, r)
              | MtAppI (t, i) => MtAppI (substu x v t, i)
	      | AppV (y, ts, is, r) => 
		AppV (y, map (substu x v) ts, is, r)
	      | BaseType a => BaseType a
          fun evar_name n =
            if n < 26 then
              "'_" ^ (str o chr) (ord #"a" + n)
            else
              "'_" ^ str_int n
          val t = update_mt t
          val fv = dedup op= $ diff op= (fresh_uvar_mt t) (fv_ctx ctx)
          val t = shiftx_t_mt 0 (length fv) t
          val (t, _) = foldl (fn (uvar_ref, (t, v)) => (substu uvar_ref v t, v + 1)) (t, 0) fv
          val t = Range.for (fn (i, t) => (Uni (Bind ((evar_name i, dummy), t), dummy))) (Mono t) (0, (length fv))
        in
          t
        end
      (* val () = println $ sprintf "Typing Decl $" [fst $ U.str_decl (gctx_names gctx) (ctx_names ctx) decl] *)
      fun main () = 
        case decl of
            U.Val (tnames, U.VarP (name, r1), e, r) =>
            let 
              val (e, t, d) = get_mtype (add_kindings_skct (zip ((rev o map fst) tnames, repeat (length tnames) Type)) ctx, e)
              val t = if is_value e then 
                        let
                          val t = generalize t
                          val t = foldr (fn (nm, t) => Uni (Bind (nm, t), r)) t tnames
                        in
                          t
                        end
                      else if length tnames = 0 then
                        Mono t
                      else
                        raise Error (r, ["explicit type variable cannot be generalized because of value restriction"])
            in
              (Val (tnames, VarP (name, r1), e, r), ctx_from_typing (name, t), 0, [d])
            end
          | U.Val (tnames, pn, e, r) =>
            let 
              val () = if length tnames = 0 then ()
                       else raise Error (r, ["compound pattern can't be generalized, so can't have explicit type variables"])
              val skcctx = (sctx, kctx, cctx) 
              val (e, t, d) = get_mtype (ctx, e)
              val (pn, cover, ctxd, nps) = match_ptrn gctx (skcctx, pn, t)
              val d = shift_ctx_i ctxd d
	      val () = check_exhaustion gctx (skcctx, t, [cover], get_region_pn pn)
            in
              (Val (tnames, pn, e, r), ctxd, nps, [d])
            end
	  | U.Rec (tnames, (name, r1), (binds, ((t, d), e)), r) => 
	    let 
              val ctx as (sctx, kctx, cctx, tctx) = add_kindings_skct (zip ((rev o map fst) tnames, repeat (length tnames) Type)) ctx
              fun f (bind, (binds, ctxd, nps)) =
                case bind of
                    U.SortingST (name, s) => 
                    let 
                      val ctx = add_ctx ctxd ctx
                      val s = is_wf_sort gctx (#1 ctx, s)
                      val ctxd' = ctx_from_sorting (fst name, s)
                      val () = open_ctx ctxd'
                      val ctxd = add_ctx ctxd' ctxd
                    in
                      (inl (name, s) :: binds, ctxd, nps)
                    end
                  | U.TypingST pn =>
                    let
                      val ctx as (sctx, kctx, cctx, tctx) = add_ctx ctxd ctx
                      val r = U.get_region_pn pn
                      val t = fresh_mt (sctx, kctx) r
                      val skcctx = (sctx, kctx, cctx) 
                      val (pn, cover, ctxd', nps') = match_ptrn gctx (skcctx, pn, t)
	              val () = check_exhaustion gctx (skcctx, t, [cover], get_region_pn pn)
                      val ctxd = add_ctx ctxd' ctxd
                      val nps = nps' + nps
                    in
                      (inr (pn, t) :: binds, ctxd, nps)
                    end
              val (binds, ctxd, nps) = foldl f ([], empty_ctx, 0) binds
              val binds = rev binds
              val (sctx, kctx, cctx, tctx) = add_ctx ctxd ctx
	      val t = check_kind_Type gctx ((sctx, kctx), t)
	      val d = check_bsort gctx (sctx, d, Base Time)
              fun g (bind, t) =
                case bind of
		    inl (name, s) => UniI (s, Bind (name, t), get_region_mt t)
		  | inr (_, t1) => Arrow (t1, T0 dummy, t)
              val te = 
                  case rev binds of
                      inr (_, t1) :: binds =>
                      foldl g (Arrow (t1, d, t)) binds
                    | _ => raise Error (r, ["Recursion must have a typing bind as the last bind"])
              val ctx = add_typing_skct (name, Mono te) ctx
              val ctx = add_ctx ctxd ctx
	      val e = check_mtype_time (ctx, e, t, d)
              val () = close_n nps
              val () = close_ctx ctxd
              val te = generalize te
              val te = foldr (fn (nm, t) => Uni (Bind (nm, t), r)) te tnames
              fun h bind =
                case bind of
                    inl a => SortingST a
                  | inr (pn, _) => TypingST pn
              val binds = map h binds
            in
              (Rec (tnames, (name, r1), (binds, ((t, d), e)), r), ctx_from_typing (name, te), 0, [T0 dummy])
	    end
	  | U.Datatype a =>
            let
              val (a, ctxd) = is_wf_datatype gctx ctx a
            in
              (Datatype a, ctxd, 0, [])
            end
          | U.IdxDef ((name, r), s, i) =>
            let
              val s = is_wf_sort gctx (sctx, s)
              val i = check_sort gctx (sctx, i, s)
              val s = sort_add_idx_eq r s i
              val ctxd = ctx_from_sorting (name, s)
              val () = open_ctx ctxd
                                (* val ps = [BinPred (EqP, VarI (NONE, (0, r)), shift_ctx_i ctxd i)] *)
                                (* val () = open_premises ps *)
            in
              (IdxDef ((name, r), s, i), ctxd, 0, [])
            end
          | U.AbsIdx2 ((name, r), s, i) =>
            let
              val s = is_wf_sort gctx (sctx, s)
              val i = check_sort gctx (sctx, i, s)
              val ctxd = ctx_from_sorting (name, s)
              val () = open_ctx ctxd
              val ps = [BinPred (EqP, VarI (NONE, (0, r)), shift_ctx_i ctxd i)]
              val () = open_premises ps
            in
              (AbsIdx2 ((name, r), s, i), ctxd, length ps, [])
            end
          | U.TypeDef ((name, r), t) =>
            let
              val (t, k) = get_kind gctx ((sctx, kctx), t)
              val kinding = (name, KeTypeEq (k, t))
            in
              (TypeDef ((name, r), t), ctx_from_kindingext kinding, 0, [])
            end
          | U.AbsIdx (((name, r1), s, i), decls, r) =>
            let
              val s = is_wf_sort gctx (sctx, s)
              (* localized the scope of the evars introduced in type-checking absidx's definition *)
              val () = open_paren ()
              val i = check_sort gctx (sctx, i, s)
              val ctxd = ctx_from_sorting (name, s)
              val () = open_ctx ctxd
              val ps = [BinPred (EqP, VarI (NONE, (0, r)), shift_ctx_i ctxd i)]
              val () = open_premises ps
              val (decls, ctxd2, nps, ds, _) = check_decls (add_ctx ctxd ctx, decls)
              val () = if nps = 0 then ()
                       else raise Error (r, ["Can't have premise-generating pattern in abstype"])
              (* close and reopen *)
              val () = close_ctx ctxd2
              val () = close_n (length ps)
              val () = close_ctx ctxd
              val () = close_paren ()
              val ctxd = add_ctx ctxd2 ctxd
              val () = open_ctx ctxd
            in
              (AbsIdx (((name, r1), s, i), decls, r), ctxd, 0, ds)
            end
          | U.Open (m, r) =>
            let
              fun link_module (m, r) (sctx, kctx, cctx, tctx) =
                let
                  fun sort_set_idx_eq s' i =
                    set_prop r s' (VarI (NONE, (0, r)) %= shift_i_i i)
                  val sctx = mapWithIdx (fn (i, (name, s)) => (name, sort_set_idx_eq s $ VarI (SOME (m, r), (i, r)))) sctx
                  fun kind_set_type_eq (dt, k, _) t = (dt, k, SOME t)
                  val kctx = mapWithIdx (fn (i, (name, k)) => (name, kind_set_type_eq k $ MtVar (SOME (m, r), (i, r)))) kctx
                in
                  (sctx, kctx, cctx, tctx)
                end
              fun clone_module gctx (m, r) =
                let
                  val ctx = shiftx_m_ctx 0 (m + 1) $ fetch_module gctx (m, r)
                  (* val ctxd = package_ctx (m, r) ctxd  *)
                  val ctx = link_module (m, r) ctx
                in
                  ctx
                end
              val ctxd = clone_module gctx (m, r)
              val () = open_ctx ctxd
            in
              (Open (m, r), ctxd, 0, [])
            end
      fun extra_msg () = ["when type-checking declaration "] @ indent [fst $ U.str_decl (gctx_names gctx) (ctx_names ctx) decl]
      val ret as (decl, ctxd, nps, ds) =
          main ()
               (* handle *)
               (* Error (r, msg) => raise Error (r, msg @ extra_msg ()) *)
               (* | Impossible msg => raise Impossible $ join_lines $ msg :: extra_msg () *)
               (* val () = println $ sprintf " Typed Decl $ " [fst $ str_decl (gctx_names gctx) (ctx_names ctx) decl] *)
	       (* val () = print $ sprintf "   Time : $: \n" [str_i sctxn d] *)
    in
      ret
    end

and check_decls gctx (ctx, decls) : decl list * context * int * idx list * context = 
    let 
      val skctxn_old = (sctx_names $ #1 ctx, names $ #2 ctx)
      fun f (decl, (decls, ctxd, nps, ds, ctx)) =
        let 
          val (decl, ctxd', nps', ds') = check_decl gctx (ctx, decl)
          val decls = decl :: decls
          val ctxd = add_ctx ctxd' ctxd
          val nps = nps + nps'
          val ds = ds' @ map (shift_ctx_i ctxd') ds
          val ctx = add_ctx ctxd' ctx
        in
          (decls, ctxd, nps, ds, ctx)
        end
      val (decls, ctxd, nps, ds, ctx) = foldl f ([], empty_ctx, 0, [], ctx) decls
      val decls = rev decls
      val ctxd = (upd4 o map o mapSnd) (simp_t o update_t) ctxd
      val ds = map simp_i $ map update_i $ rev ds
                   (* val () = println "Typed Decls:" *)
                   (* val () = app println $ str_typing_info (gctx_names gctx) skctxn_old (ctxd, ds) *)
    in
      (decls, ctxd, nps, ds, ctx)
    end

and is_wf_datatype gctx ctx (name, tnames, sorts, constr_decls, r) : datatype_def * context =
    let 
      val sorts = is_wf_sorts gctx (#1 ctx, sorts)
      val nk = (name, (true, (length tnames, sorts), NONE))
      val ctx as (sctx, kctx, _, _) = add_kindingext_skct nk ctx
      fun make_constr ((name, ibinds, r) : U.constr_decl) : constr_decl * (string * constr) =
	let
          val family = (NONE, (0, r))
          val c = (family, tnames, ibinds)
	  val t = U.constr_type U.VarT shiftx_long_id c
	  val t = is_wf_type gctx ((sctx, kctx), t)
		  handle Error (_, msg) =>
			 raise Error (r, 
				      "Constructor is ill-formed" :: 
				      "Cause:" :: 
				      indent msg)
          val () = if length (fresh_uvar_t t) > 0 then
                     raise Error (r, ["Constructor has unresolved unification type variable(s)"])
                   else ()
          val (_, ibinds) = constr_from_type t
	in
	  ((name, ibinds, r), (name, (family, tnames, ibinds)))
	end
      val (constr_decls, constrs) = (unzip o map make_constr) constr_decls
    in
      ((name, tnames, sorts, constr_decls, r), ([], add_kindingext nk [], rev constrs, []))
    end
      
and check_rules gctx (ctx as (sctx, kctx, cctx, tctx), rules, t as (t1, return), r) =
    let 
      val skcctx = (sctx, kctx, cctx) 
      fun f (rule, acc) =
	let
          (* val previous_covers = map (snd o snd) $ rev acc *)
          val ans as (rule, (td, cover)) = check_rule gctx (ctx, (* previous_covers, *) rule, t)
          val covers = (rev o map (snd o snd)) acc
                                               (* val () = println "before check_redundancy()" *)
	                                       (* val () = check_redundancy (skcctx, t1, covers, cover, get_region_rule rule) *)
                                               (* val () = println "after check_redundancy()" *)
	in
	  ans :: acc
	end 
      val (rules, (tds, covers)) = (mapSnd unzip o unzip o rev o foldl f []) rules
	                                                                     (* val () = check_exhaustion (skcctx, t1, covers, r) *)
    in
      (rules, tds)
    end

and check_rule gctx (ctx as (sctx, kctx, cctx, tctx), (* pcovers, *) (pn, e), t as (t1, return)) =
    let 
      val skcctx = (sctx, kctx, cctx) 
      val (pn, cover, ctxd as (sctxd, kctxd, _, _), nps) = match_ptrn gctx (skcctx, (* pcovers, *) pn, t1)
      val ctx0 = ctx
      val ctx = add_ctx ctxd ctx
      val (e, t, d) = get_mtype gctx (ctx, e)
      val (t, d) = forget_or_check_return (get_region_e e) gctx ctx ctxd (t, d) return 
      (*
        val (e, t, d) = 
            case return of
                (SOME t, SOME d) =>
                let
	          val e = check_mtype_time (ctx, e, shift_ctx_mt ctxd t, shift_ctx_i ctxd d)
                in
                  (e, t, d)
                end
              | (SOME t, NONE) =>
                let 
                  val (e, _, d) = check_mtype (ctx, e, shift_ctx_mt ctxd t)
                  (* val () = println $ str_i (names (#1 ctx)) d *)
		  val d = forget_ctx_d (get_region_e e) ctx ctxd d
                                       (* val () = println $ str_i (names (#1 ctx0)) d *)
                in
                  (e, t, d)
                end
              | (NONE, SOME d) =>
                let 
                  val (e, t) = check_time (ctx, e, shift_ctx_i ctxd d)
		  val t = forget_ctx_mt (get_region_e e) ctx ctxd t 
                in
                  (e, t, d)
                end
              | (NONE, NONE) =>
                let 
                  val (e, t, d) = get_mtype (ctx, e)
		  val t = forget_ctx_mt (get_region_e e) ctx ctxd t 
		  val d = forget_ctx_d (get_region_e e) ctx ctxd d
                in
                  (e, t, d)
                end
      *)
      val () = close_n nps
      val () = close_ctx ctxd
    in
      ((pn, e), ((t, d), cover))
    end

and check_mtype gctx (ctx as (sctx, kctx, cctx, tctx), e, t) =
    let
      val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
      val (e, t', d) = get_mtype gctx (ctx, e)
      val () = unify_mt (get_region_e e) gctx (sctx, kctx) (t', t)
                        (* val () = println "check type" *)
                        (* val () = println $ str_region "" "ilist.timl" $ get_region_e e *)
    in
      (e, t', d)
    end

and check_time gctx (ctx as (sctx, kctx, cctx, tctx), e, d) : expr * mtype =
    let 
      val (e, t, d') = get_mtype gctx (ctx, e)
      val () = smart_write_le (gctx_names gctx) (names sctx) (d', d, get_region_e e)
    in
      (e, t)
    end

and check_mtype_time gctx (ctx as (sctx, kctx, cctx, tctx), e, t, d) =
    let 
      val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
      (* val () = print (sprintf "Type checking $ against $ and $\n" [U.str_e ctxn e, str_mt (sctxn, kctxn) t, str_i sctxn d]) *)
      val (e, _, d') = check_mtype gctx (ctx, e, t)
      (* val () = println "check type & time" *)
      (* val () = println $ str_region "" "ilist.timl" $ get_region_e e *)
      val () = smart_write_le (gctx_names gctx) (names sctx) (d', d, get_region_e e)
    in
      e
    end

fun link_sig r gctx m (ctx' as (sctx', kctx', cctx', tctx') : context) =
  let
    val gctxn = gctx_names gctx
    (* val () = println $ sprintf "Linking module $ (%$) against signature" [str_v (names gctxn) $ fst m, str_int $ fst m] *)
    fun match_sort ((name, s'), sctx') =
      let
        (* val () = println $ sprintf "before fetch_sort_by_name $.$" [str_v (names gctxn) $ fst m, name] *)
        val (x, s) = fetch_sort_by_name gctx [] (SOME m, (name, r))
        val () = is_sub_sort r gctxn (sctx_names sctx') (s, s')
        val s' = sort_add_idx_eq r s' (VarI x)
        val sctx' = open_and add_sorting (name, s') sctx'
      in
        sctx'
      end
    val sctx' = foldr match_sort [] sctx'
    fun match_kind ((name, k'), kctx') =
      let
        val (x, k) = fetch_kindext_by_name gctx [] (SOME m, (name, r))
        val () = is_sub_kindext r gctx (sctx', kctx') (k, k')
        fun kind_add_type_eq (dt, k, t') t =
          case t' of
              NONE => (dt, k, SOME t)
           |  SOME t' =>
              let
                val () = unify_mt r gctx (sctx', kctx') (t', t)
              in
                (dt, k, SOME t')
              end
        val k' = kind_add_type_eq k' (MtVar x)
      in
        add_kindingext (name, k') kctx'
      end
    val kctx' = foldr match_kind [] kctx'
    fun match_constr_type (name, c) =
      let
        val (_, t) = fetch_constr_type_by_name gctx [] (SOME m, (name, r))
        val t' = constr_type VarT shiftx_long_id c
      in
        unify_t r gctx (sctx', kctx') (t', t)
      end
    val () = app match_constr_type cctx'
    fun match_type (name, t') =
      let
        val (_, t) = fetch_type_by_name gctx [] (SOME m, (name, r))
      in
        unify_t r gctx (sctx', kctx') (t, t')
      end
    val () = app match_type tctx'
    val () = close_ctx ctx'
  in
    (sctx', kctx', cctx', tctx')
  end

(* and link_sig_pack (* sigs *) gctx_base sg sg' = *)
(*     case (sg, sg') of *)
(*         (Sig sg, Sig sg') => Sig $ link_sig (* sigs *) gctx_base sg sg' *)
(*       | _ => raise Impossible "link_sig_pack (): only Sig should appear here" *)

fun is_sub_sig r gctx ctx ctx' =
  let
    val mod_name = "__link_sig_module" 
    val gctx = add_sigging (mod_name, ctx) gctx
    val () = open_module (mod_name, ctx)
    val _ = link_sig r gctx (0, r) ctx'
    val () = close_n 1
  in
    ()
  end
    
fun is_wf_sig gctx sg =
  case sg of
      U.SigComponents (comps, r) =>
      let
        fun is_wf_spec (ctx as (sctx, kctx, _, _)) spec =
          case spec of
              U.SpecVal ((name, r), t) =>
              let
                val t = is_wf_type gctx ((sctx, kctx), t)
              in
                (SpecVal ((name, r), t), add_typing_skct (name, t) ctx)
              end
            | U.SpecIdx ((name, r), s) =>
              let
                val s = is_wf_sort gctx (sctx, s)
              in
                (SpecIdx ((name, r), s), open_and add_sorting_skct (name, s) ctx)
              end
            | U.SpecType ((name, r), k) =>
              let
                val k = is_wf_kind gctx (sctx, k)
              in
                (SpecType ((name, r), k), add_kinding_skct (name, k) ctx)
              end
            | U.SpecTypeDef ((name, r), t) =>
              let
                val (t, k) = get_kind gctx ((sctx, kctx), t)
              in
                (SpecTypeDef ((name, r), t), add_type_eq_skct (name, (k, t)) ctx)
              end
            | U.SpecDatatype a =>
              let
                val (a, ctxd) = is_wf_datatype gctx ctx a
              in
                (SpecDatatype a, add_ctx ctxd ctx)
              end
        fun iter (spec, (specs, ctx)) =
          let
            val (spec, ctx) = is_wf_spec ctx spec
          in
            (spec :: specs, ctx)
          end
        val ctxd = snd $ foldl iter ([], empty_ctx) comps
        val () = close_ctx ctxd
      in
        ctxd
      end
(* | U.SigVar (x, r) => *)
(*   (case lookup_sig gctx x of *)
(*        SOME sg => sg *)
(*      | NONE => raise Error (r, ["Unbound signature"]) *)
(*   ) *)
(* | U.SigWhere (sg, ((x, r), t)) => *)
(*   let *)
(*     val sg = is_wf_sig gctx sg *)
(*     val k =  *)
(*   in *)
(*   end *)
        
fun get_sig gctx m : context =
  case m of
      U.ModComponents (comps, r) =>
      let
        val (_, ctxd, nps, ds, _) = check_decls gctx (empty_ctx, comps)
        val () = close_n nps
        val () = close_ctx ctxd
      in
        ctxd
      end
    | U.ModSeal (m, sg) =>
      let
        val sg = is_wf_sig gctx sg
        val sg' = get_sig gctx m
        val () = is_sub_sig (U.get_region_m m) gctx sg' sg
      in
        sg
      end
    | U.ModTransparentAscription (m, sg) =>
      let
        val sg = is_wf_sig gctx sg
        val sg' = get_sig gctx m
        val () = is_sub_sig (U.get_region_m m) gctx sg' sg
      in
        sg'
      end

fun check_top_bind gctx bind =
  let
    val gctxd = 
        case bind of
            U.TopModBind ((name, _), m) =>
            let
              val sg = get_sig gctx m
            in
              [(name, Sig sg)]
            end
          | U.TopFunctorBind ((name, _), ((arg_name, _), arg), m) =>
            (* functor applications will be implemented fiberedly instead of parametrizedly *)
            let
              val arg = is_wf_sig gctx arg
              val gctx = add_sigging (arg_name, arg) gctx
              val () = open_module (arg_name, arg)
              val sg = get_sig gctx m
              val () = close_n 1
            in
              [(name, FunctorBind ((arg_name, arg), sg))]
            end
          | U.TopFunctorApp ((name, _), f, m) =>
            let
              fun lookup_functor gctx m =
                let
                  fun iter ((name, sg), (nsig, target)) =
                    case sg of
                        Sig _ => Continue (nsig + 1, target)
                      | FunctorBind a =>
                        if target <= 0 then
                          ShortCircuit (nsig, name, a)
                        else
                          Continue (nsig, target - 1)
                  fun find_first m = is_ShortCircuit $ foldlM_Error iter (0, m) gctx
                in
                  case find_first m of
                      SOME (n, name, (arg, body : context)) => SOME (name, (shiftx_snd shiftx_m_ctx 0 n arg, shiftx_m_ctx 1 n body))
                    | NONE => NONE
                end
              fun fetch_functor gctx (m, r) =
                case lookup_functor gctx m of
                    SOME a => a
                  | NONE => raise Error (r, ["Unbound functor " ^ str_v [] m])
              val (_, ((_, formal_arg), body)) = fetch_functor gctx f
              val formal_arg = link_sig (snd m) gctx m formal_arg
              val formal_arg_name = "__mod_arg"
              val gctxd = [(formal_arg_name, Sig formal_arg)]
            in
              (name, Sig body) :: gctxd
            end
              (* val () = println "Typechecked program:" *)
              (* val () = app println $ str_gctx (gctx_names gctx) gctxd *)
  in
    gctxd
  end
    
and check_prog gctx binds =
    let
      (* val () = println "Begin check_prog()" *)
      fun open_gctx gctx =
        app open_module $ rev $ filter_module gctx
      fun close_gctx gctx =
        close_n $ length $ filter_module gctx
      fun iter (bind, (acc, gctx)) =
        let
          val () = open_gctx gctx
          val gctxd = check_top_bind gctx bind
          val () = close_gctx gctx
        in
          (gctxd @ acc, gctxd @ gctx)
        end
      val ret as (gctxd, gctx) = foldl iter ([], gctx) binds
                                       (* val () = println "End check_prog()" *)
    in
      ret
    end

end
