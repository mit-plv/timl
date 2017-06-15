structure DoTypeCheck = struct
structure U = UnderscoredExpr
open CollectUVar
open RedundantExhaust
open Region
open Expr
open Simp
open Subst
open Package
open TypecheckUtil
open UVar
open Unify
open FreshUVar
open UVarForget
open Util

infixr 0 $
infix 0 !!

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
        
val is_builtin_enabled = ref false
fun turn_on_builtin () = (is_builtin_enabled := true)
fun turn_off_builtin () = (is_builtin_enabled := false)
                            
fun str_sctx gctx sctx =
  snd $ foldr (fn ((name, sort), (sctxn, acc)) => (name :: sctxn, (name, str_s gctx sctxn sort) :: acc)) ([], []) sctx
      
fun idx_un_op_type opr =
  case opr of
      ToReal => (Nat, Time)
    | Log2 => (Time, Time)
    | Ceil => (Time, Nat)
    | Floor => (Time, Nat)
    | B2n => (BoolSort, Nat)
    | Neg => (BoolSort, BoolSort)
    | IUDiv _ => raise Impossible "idx_un_op_type ()"
    | IUExp _ => raise Impossible "idx_un_op_type ()"

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

fun sort_mismatch gctx ctx i expect have =  "Sort mismatch for " ^ str_i gctx ctx i ^ ": expect " ^ expect ^ " have " ^ str_s gctx ctx have

fun is_wf_bsort (bs : U.bsort) : bsort =
  case bs of
      U.Base bs => Base bs
    | U.BSArrow (a, b) => BSArrow (is_wf_bsort a, is_wf_bsort b)
    | U.UVarBS () => fresh_bsort ()

(* a classifier for [sort], since [sort] has [SAbs] and [SApp] *)        
type sort_type = bsort list
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
      | U.UVarS ((), r) =>
        (* sort underscore will always mean a sort of type Sort *)
        (fresh_sort gctx ctx r, Sort)
      | U.SAbs (b, Bind ((name, r1), s), r) =>
        let
          val b = is_wf_bsort b
          val (s, t) = get_sort_type (add_sorting (name, Basic (b, r1)) ctx, s)
        in
          (SAbs (b, Bind ((name, r1), s), r), b :: t)
        end
      | U.SApp (s, i) =>
        let
          val (s, t) = get_sort_type (ctx, s)
          val (b, t) =
              case t of
                  b :: t => (b, t)
                | [] => raise Error (get_region_s s, [sprintf "sort $ should be an abstract" [str_s (gctx_names gctx) (sctx_names ctx) s]])
          val i = check_bsort (ctx, i, b)
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
	  U.PTrueFalse (b, r) => PTrueFalse (b, r)
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
            fun error expected =
              Error (U.get_region_p p, sprintf "Sorts of operands of $ must be both $:" [str_bin_pred opr, expected] :: indent ["left: " ^ str_bs bs1, "right: " ^ str_bs bs2])
            val () =
                case opr of
                    BigO =>
                    let
                      val (args, ret) = collect_BSArrow bs
                      val r = U.get_region_p p
                      val () =
                          case ret of
                              UVarBS _ => ()  (* if it's uvar, it may be BSArrow *)
                            | _ => unify_bs r (ret, Base Time)
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
          | U.IConst (c, r) =>
            (case c of
	         ICBool _ => 
                 (IConst (c, r), Base BoolSort)
	       | ICTT => 
                 (TTI r, Base UnitSort)
	       | ICTime x => 
	         (ConstIT (x, r), Base Time)
	       | ICNat n => 
	         if n >= 0 then
	           (ConstIN (n, r), Base Nat)
	         else
	           raise Error (r, ["Natural number constant must be non-negative"])
	       | ICAdmit => 
                 (AdmitI r, Base UnitSort)
            )
          | U.UnOpI (opr, i, r) =>
            (case opr of
                 IUDiv n =>
                 let 
                   val i = check_bsort (ctx, i, Base Time)
	           val () = if n > 0 then ()
	                    else raise Error (r, ["Can only divide by positive integer"])
                 in
                   (DivI (i, (n, r)), Base Time)
                 end
               | IUExp n =>
                 let 
                   val i = check_bsort (ctx, i, Base Time)
                 in
                   (ExpI (i, (n, r)), Base Time)
                 end
               | _ =>
                 let
                   val (atype, rettype) = idx_un_op_type opr
                 in
                   (UnOpI (opr,
                           check_bsort (ctx, i, Base atype),
                           r),
                    Base rettype)
                 end
            )
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
          | U.UVarI ((), r) =>
            let
              val bs = fresh_bsort ()
            in
              (fresh_i gctx ctx bs r, bs)
            end
      val ret = main ()
                handle
                Error (r, msg) =>
                raise Error (r, msg @ ["when sort-checking index "] @ indent [U.str_i (gctx_names gctx) (sctx_names ctx) i])
                (* raise Error (r, msg @ [sprintf "when sort-checking index $ in context $" [U.str_i (gctx_names gctx) (sctx_names ctx) i, str_ls (fn (name, sort) => sprintf "\n$: $" [name, sort]) $ str_sctx (gctx_names gctx) ctx]]) *)
      (* val () = println $ sprintf "get_bsort() result: $ : $" [str_i (gctx_names gctx) (sctx_names ctx) (fst ret), str_bs (snd ret)] *)
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
    (* val () = println $ sprintf "sortchecking $ against $" [U.str_i (gctx_names gctx) (sctx_names ctx) i, str_s (gctx_names gctx) (sctx_names ctx) s] *)
    val (i, bs') = get_bsort gctx (ctx, i)
    val r = get_region_i i
    val s = normalize_s s
    exception UnifySAppFailed
    fun unify_SApp_UVarS s =
      let
        val ((x, _), _) = is_SApp_UVarS s !! (fn () => raise UnifySAppFailed)
        val (_, ctx) = get_uvar_info x !! (fn () => raise Impossible "check_sort()/unify_SApp_UVar(): x should be Fresh")
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
                    IConst (ICAdmit, r) => (TTI r, true)
                  | _ => (i, false)
            (* val () = println $ "is_admit=" ^ str_bool is_admit *)
            val p = subst_i_p i p
            (* val () = println $ sprintf "Writing prop $ $" [str_p (gctx_names gctx) (sctx_names ctx) p, str_region "" "" r] *)
	    val () =
                if is_admit then
                  write_admit (p, r)
                else
                  write_prop (p, r)
          in
            ()
          end
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

fun is_wf_kind (k : U.kind) = mapSnd (map is_wf_bsort) k

(* k => Type *)
fun recur_kind k = (0, k)

(* higher-kind *)
datatype hkind =
         HKType
         | HKArrow of hkind * hkind
         | HKArrowI of bsort * hkind

fun str_hk k =
  case k of
      HKType => "*"
    | HKArrow (k1, k2) => sprintf "($ => $)" [str_hk k1, str_hk k2]
    | HKArrowI (s, k) => sprintf "($ => $)" [str_bs s, str_hk k]

val HType = HKType

fun kind_to_higher_kind (n, sorts) =
  let
    val k = foldr (fn (s, k) => HKArrowI (s, k)) HKType sorts
    val k = Range.for (fn (_, k) => HKArrow (HKType, k)) k (Range.zero_to n)
  in
    k
  end

fun unify_higher_kind r (k, k') =
  case (k, k') of
      (HKType, HKType) => ()
    | (HKArrow (k1, k2), HKArrow (k1', k2')) =>
      let
        val () = unify_higher_kind r (k1, k1')
        val () = unify_higher_kind r (k2, k2')
      in
        ()
      end
    | (HKArrowI (s, k), HKArrowI (s', k')) =>
      let
        val () = unify_bs r (s, s')
        val () = unify_higher_kind r (k, k')
      in
        ()
      end
    | _  => raise Error (r, [kind_mismatch (str_hk k) str_hk k'])

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
	| U.BaseType a => (BaseType a, HType)
        | U.UVar ((), r) =>
          (* type underscore will always mean a type of kind Type *)
          (fresh_mt gctx (sctx, kctx) r, HType)
        | U.MtVar x =>
          (MtVar x, kind_to_higher_kind $ fetch_kind gctx (kctx, x))
        | U.MtAbs (k1, Bind ((name, r1), t), r) =>
          let
            val k1 = is_wf_kind k1
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
              | _ => error (get_region_mt t1, str_mt gctxn ctxn t1, "<kind> => <kind>", str_hk, k)
          end
        | U.MtAbsI (b, Bind ((name, r1), t), r) =>
          let
            val b = is_wf_bsort b
            val (t, k) = get_higher_kind (add_sorting_sk (name, Basic (b, r1)) ctx, t)
            val k = HKArrowI (b, k)
          in
            (MtAbsI (b, Bind ((name, r1), t), r), k)
          end
        | U.MtAppI (t, i) =>
          let
            val (t, k) = get_higher_kind (ctx, t)
          in
            case k of
                HKArrowI (b, k) =>
                let
                  val i = check_bsort gctx (sctx, i, b)
                in
                  (MtAppI (t, i), k)
                end
              | _ => error (get_region_mt t, str_mt gctxn ctxn t, "<sort> => <kind>", str_hk, k)
          end
        | U.TDatatype _ => raise Unimpl "get_higher_kind()/TDatatype"
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
      val () = unify_higher_kind (get_region_mt t) (k', k)
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
    val k = lazy_default (fn () => raise Error (get_region_mt t, kind_mismatch_in_type "first-order kind (i.e. * => ... <sort> => ... => *)" str_hk k (str_mt (gctx_names gctx) (sctx_names sctx, names kctx) t))) $ higher_kind_to_kind k
  in
    (t, k)
  end

fun check_kind gctx (ctx, t, k) =
    let
      val (t, k') = get_kind gctx (ctx, t)
      val () = unify_k (get_region_mt t) (k', k)
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

fun check_redundancy gctx (ctx as (_, _, cctx), t, prevs, this, r) =
  let
  in
    if is_redundant gctx (ctx, t, prevs, this) then ()
    else
      raise Error (r, sprintf "Redundant rule: $" [str_cover (gctx_names gctx) (names cctx) this] :: indent [sprintf "Has already been covered by previous rules: $" [(join ", " o map (str_cover (gctx_names gctx) (names cctx))) prevs]])
  end
    
fun check_exhaustion gctx (ctx as (_, _, cctx), t : mtype, covers, r) =
  let
  in
    case is_exhaustive gctx (ctx, t, covers) of
        NONE => ()
      | SOME missed =>
	raise Error (r, [sprintf "Not exhaustive, at least missing this case: $" [str_habitant (gctx_names gctx) (names cctx) missed]])
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
    shiftx_i_i x 1 $ substx_i_i 0 x v b
  end
    
fun substx_i_p_nonconsuming x v b =
  let
    val v = forget_i_i x 1 v
  in
    shiftx_i_p x 1 $ substx_i_p 0 x v b
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

fun match_ptrn gctx (ctx as (sctx : scontext, kctx : kcontext, cctx : ccontext), (* pcovers, *) pn : U.ptrn, t : mtype) : ptrn * cover * context * int =
  let
    val match_ptrn = match_ptrn gctx
    val gctxn = gctx_names gctx
    val skctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
    (* val () = println $ sprintf "Checking pattern $ for type $" [U.str_pn gctxn (sctxn, kctxn, names cctx) pn, str_mt gctxn (sctxn, kctxn) t] *)
    (* val () = println $ "sctxn=" ^ (str_ls id sctxn) *)
  in
    case pn of
	U.ConstrP (((cx, ()), eia), inames, opn, r) =>
 	let 
          val c as (family, tbinds) = snd $ fetch_constr gctx (cctx, cx)
          val siblings = get_family_siblings gctx cctx cx
          val pos_in_family = index (curry eq_long_id cx) siblings !! (fn () => raise Impossible "family_pos")
          val (tname_kinds, ibinds) = unfold_binds tbinds
          val tnames = map fst tname_kinds
          val (name_sorts, (t1, is')) = unfold_binds ibinds
          val () = if eia then () else raise Impossible "eia shouldn't be false"
          val ts = map (fn _ => fresh_mt gctx (sctx, kctx) r) tnames
          val is = map (fn _ => fresh_i gctx sctx (fresh_bsort ()) r) is'
          val t_constr = MtAppIs (MtApps (MtVar family) ts) is
	  val () = unify_mt r gctx (sctx, kctx) (t, t_constr)
                   handle
                   Error _ =>
                   let
                     val expect = str_mt gctxn skctxn t
                     val got = str_mt gctxn skctxn t_constr
                   in
                     raise Error
                           (r, sprintf "Type of constructor $ doesn't match datatype " [str_long_id #3 gctxn (names cctx) cx] ::
                               indent ["expect: " ^ expect,
                                       "got: " ^ got])
                   end
          val length_name_sorts = length name_sorts
          val () =
              if length inames = length_name_sorts then ()
              else raise Error (r, [sprintf "This constructor requires $ index argument(s), not $" [str_int (length_name_sorts), str_int (length inames)]])
          val ts = map (normalize_mt gctx kctx) ts
          val is = map normalize_i is
	  val ts = map (shiftx_i_mt 0 (length_name_sorts)) ts
	  val is = map (shiftx_i_i 0 (length_name_sorts)) is
	  val t1 = subst_ts_mt ts t1
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
          val pn1 = opn
          val (pn1, cover, ctxd', nps) = match_ptrn (ctx, pn1, t1)
          val ctxd = add_ctx ctxd' ctxd
          val cover = ConstrC (cx, cover)
        in
	  (ConstrP (((cx, (length siblings, pos_in_family)), eia), inames, pn1, r), cover, ctxd, length ps + nps)
	end
      | U.VarP (name, r) =>
        let
          (* val pcover = combine_covers pcovers *)
          (* val cover = cover_neg cctx t pcover *)
          fun is_first_capital s =
            String.size s >= 1 andalso Char.isUpper (String.sub (s, 0))
          val () = if is_first_capital name then println $ sprintf "Warning: pattern $ is treated as a wildcard (did you misspell a constructor name?)" [name]
                   else ()
        in
          (VarP (name, r), TrueC, ctx_from_typing (name, Mono t), 0)
        end
      | U.PairP (pn1, pn2) =>
        let 
          val r = U.get_region_pn pn
          val t1 = fresh_mt gctx (sctx, kctx) r
          val t2 = fresh_mt gctx (sctx, kctx) r
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

(* If i1 or i2 is fresh, do unification instead of VC generation. Could be unsound. *)
fun smart_write_le gctx ctx (i1, i2, r) =
  let
    (* val () = println $ sprintf "Check Le : $ <= $" [str_i ctx i1, str_i ctx i2] *)
    (* fun is_fresh_i i = *)
    (*   case i of *)
    (*       UVarI (x, _) => is_fresh x *)
    (*     | _ => false *)
    fun is_fresh_i i = isSome $ is_IApp_UVarI i
  in
    if is_fresh_i i1 orelse is_fresh_i i2 then unify_i r gctx ctx (i1, i2)
    else
      write_le (i1, i2, r)
  end

(* expand wildcard rules to reveal premises *)    
fun expand_rules gctx (ctx as (sctx, kctx, cctx), rules, t, r) =
  let
    fun expand_rule (rule as (pn, e), (pcovers, rules)) =
      let
	val (pn, cover, ctxd, nps) = match_ptrn gctx (ctx, (* pcovers, *) pn, t)
        val () = close_n nps
        val () = close_ctx ctxd
        (* val cover = ptrn_to_cover pn *)
        (* val () = println "before check_redundancy()" *)
        val () = check_redundancy gctx (ctx, t, pcovers, cover, get_region_pn pn)
        (* val () = println "after check_redundancy()" *)
        val (pcovers, new_rules) =
            case (pn, e) of
                (VarP _, U.ET (ETNever, U.UVar ((), _), _)) =>
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
                          fun default () = raise Impossible "hab_to_ptrn"
                        in
                          case hab of
                              ConstrH (x, h') =>
                              (case is_AppV t of
                                   SOME (family, ts, _) =>
                                   let
                                     val (_, tbinds) = snd $ fetch_constr gctx (cctx, x)
                                     val (_, ibinds) = unfold_binds tbinds
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
                                     ConstrP (((x, ()), true), repeat (length name_sorts) "_", pn', dummy)
                                   end
                                 | NONE => default ()
                              )
                            | TTH =>
                              (case t of
                                   Unit _ =>
                                   TTP dummy
                                 | _ => default ()
                              )
                            | PairH (h1, h2) =>
                              (case t of
                                   Prod (t1, t2) =>
                                   PairP (loop (* cutoff *) t1 h1, loop (* cutoff *) t2 h2)
                                 | _ => default ()
                              )
                            | TrueH => VarP ("_", dummy)
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
                          ConstrP (((x, ()), _), _, pn, _) => ConstrC (x, ptrn_to_cover pn)
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
                      | ConstrP (x, inames, opn, r) => U.ConstrP (x, inames, convert_pn opn, r) 
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
    | UVarS _ => raise Error (r, ["unsolved unification variable in module"])
    | SAbs _ => raise Impossible "set_prop()/SAbs: shouldn't be prop"
    | SApp _ => raise Error (r, ["unsolved unification variable in module (unnormalized application)"])
                      
fun add_prop r s p =
  case normalize_s s of
      Basic (bs as (_, r)) => Subset (bs, Bind (("__added_prop", r), p), r)
    | Subset (bs, Bind (name, p'), r) => Subset (bs, Bind (name, p' /\ p), r)
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
                 indent (str_sig (add (arg_name, ctx_names arg) gctxn) body),
                 [])
      in
        (ls :: acc, addList (gctxn, gctxnd))
      end
    val typing_lines = List.concat $ rev $ fst $ foldr str_sigging ([], old_gctxn) gctx
    val lines = 
        typing_lines @
        [""]
  in
    lines
  end

(* fun str_gctx gctxn gctx = *)
(*   let *)
(*     val gctxn = union (gctxn, gctx_names $ to_map gctx) *)
(*     fun str_sigging (name, sg) = *)
(*       case sg of *)
(*           Sig ctx => *)
(*           [sprintf "structure $ : " [name] ] @ *)
(*           indent (str_sig gctxn ctx) *)
(*         | FunctorBind ((arg_name, arg), body) => *)
(*           [sprintf "functor $ (structure $ : " [name, arg_name] ] @ *)
(*           indent (str_sig gctxn arg) @ *)
(*           [") : "] @ *)
(*           indent (str_sig (curry Gctx.insert' (arg_name, ctx_names arg) gctxn) body) *)
(*     val typing_lines = concatMap str_sigging gctx *)
(*     val lines =  *)
(*         typing_lines @ *)
(*         [""] *)
(*   in *)
(*     lines *)
(*   end *)

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
    (* val () = print $ sprintf "  Typing $\n" [U.str_raw_e e_all] *)
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
            (* val () = println $ str_t gctxn skctxn t *)
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
        | U.EConst (c, r) =>
          (case c of
	       ECTT => 
               (TT r, Unit dummy, T0 dummy)
	     | ECInt n => 
	       (ConstInt (n, r), BaseType (Int, dummy), T0 dummy)
	     | ECNat n => 
	       if n >= 0 then
	         (ConstNat (n, r), TyNat (ConstIN (n, r), r), T0 r)
	       else
	         raise Error (r, ["Natural number constant must be non-negative"])
          )
        | U.EUnOp (opr, e, r) =>
          (case opr of
	       EUFst => 
	       let 
                 val r = U.get_region_e e
                 val t1 = fresh_mt gctx (sctx, kctx) r
                 val t2 = fresh_mt gctx (sctx, kctx) r
                 val (e, _, d) = check_mtype (ctx, e, Prod (t1, t2)) 
               in 
                 (Fst (e, r), t1, d)
	       end
	     | EUSnd => 
	       let 
                 val r = U.get_region_e e
                 val t1 = fresh_mt gctx (sctx, kctx) r
                 val t2 = fresh_mt gctx (sctx, kctx) r
                 val (e, _, d) = check_mtype (ctx, e, Prod (t1, t2)) 
               in 
                 (Snd (e, r), t2, d)
	       end
          )
	| U.BinOp (opr, e1, e2) =>
          (case opr of
	       EBPair => 
	       let 
                 val (e1, t1, d1) = get_mtype (ctx, e1) 
	         val (e2, t2, d2) = get_mtype (ctx, e2) 
               in
	         (Pair (e1, e2), Prod (t1, t2), d1 %+ d2)
	       end
	     | EBApp =>
	       let
                 val (e2, t2, d2) = get_mtype (ctx, e2)
                 val r = U.get_region_e e1
                 val d = fresh_i gctx sctx (Base Time) r
                 val t = fresh_mt gctx (sctx, kctx) r
                 val (e1, _, d1) = check_mtype (ctx, e1, Arrow (t2, d, t))
                 val ret = (App (e1, e2), t, d1 %+ d2 %+ T1 dummy %+ d) 
               in
                 ret
	       end
	     | New =>
               let
                 val r = U.get_region_e e_all
                 val i = fresh_i gctx sctx (Base Time) r
                 val (e1, _, d1) = check_mtype (ctx, e1, TyNat (i, r))
                 val (e2, t, d2) = get_mtype (ctx, e2)
               in
                 (BinOp (New, e1, e2), TyArray (t, i), d1 %+ d2)
               end
	     | Read =>
               let
                 val r = U.get_region_e e_all
                 val t = fresh_mt gctx (sctx, kctx) r
                 val i1 = fresh_i gctx sctx (Base Time) r
                 val i2 = fresh_i gctx sctx (Base Time) r
                 val (e1, _, d1) = check_mtype (ctx, e1, TyArray (t, i1))
                 val (e2, _, d2) = check_mtype (ctx, e2, TyNat (i2, r))
                 val () = write_le (i2, i1, r)
               in
                 (BinOp (Read, e1, e2), t, d1 %+ d2)
               end
	     | Add =>
	       let val (e1, _, d1) = check_mtype (ctx, e1, BaseType (Int, dummy))
	           val (e2, _, d2) = check_mtype (ctx, e2, BaseType (Int, dummy)) in
	         (BinOp (Add, e1, e2), BaseType (Int, dummy), d1 %+ d2 %+ T1 dummy)
	       end
          )
	| U.TriOp (Write, e1, e2, e3) =>
          let
            val r = U.get_region_e e_all
            val t = fresh_mt gctx (sctx, kctx) r
            val i1 = fresh_i gctx sctx (Base Time) r
            val i2 = fresh_i gctx sctx (Base Time) r
            val (e1, _, d1) = check_mtype (ctx, e1, TyArray (t, i1))
            val (e2, _, d2) = check_mtype (ctx, e2, TyNat (i2, r))
            val () = write_le (i2, i1, r)
            val (e3, _, d3) = check_mtype (ctx, e3, t)
          in
            (TriOp (Write, e1, e2, e3), Unit r, d1 %+ d2 %+ d3)
          end
	| U.EEI (opr, e, i) =>
          (case opr of
	       EEIAppI =>
	       let 
                 val (e, t, d) = get_mtype (ctx, e) 
               in
                 case t of
                     UniI (s, Bind ((arg_name, _), t1), r) =>
                     let
                       val i = check_sort gctx (sctx, i, s) 
                     in
	               (AppI (e, i), subst_i_mt i t1, d)
                     end
                   | _ =>
                     (* If the type is not in the expected form (maybe due to uvar), we try to unify it with the expected template. This may lose generality because the the inferred argument sort will always be a base sort. *)
	             let 
                       val r = get_region_e e
                       val s = fresh_sort gctx sctx r
                       val arg_name = "_"
                       val t1 = fresh_mt gctx (add_sorting (arg_name, s) sctx, kctx) r
                       val t_e = UniI (s, Bind ((arg_name, r), t1), r)
                       (* val () = println $ "t1 = " ^ str_mt gctxn (sctx_names sctx, names kctx) t1 *)
                       (* val () = println $ "t1 = " ^ str_raw_mt t1 *)
                       (* val () = println $ "t_e = " ^ str_mt gctxn (sctx_names sctx, names kctx) t_e *)
                       (* val () = println "before" *)
                       val () = unify_mt r gctx (sctx, kctx) (t, t_e)
                       (* val () = println $ "t = " ^ str_mt gctxn (sctx_names sctx, names kctx) t *)
                       (* val () = println $ "t_e = " ^ (str_mt gctxn (sctx_names sctx, names kctx) $ normalize_mt gctx kctx t_e) *)
                       (* val () = println "after" *)
                       val i = check_sort gctx (sctx, i, s) 
                     in
	               (AppI (e, i), subst_i_mt i t1, d)
	             end
               end
	     | EEIAscriptionTime => 
	       let val i = check_bsort gctx (sctx, i, Base Time)
	           val (e, t) = check_time (ctx, e, i)
               in
	         (AscriptionTime (e, i), t, i)
	       end
          )
	| U.ET (opr, t, r) =>
          (case opr of
	       ETNever => 
               let
	         val t = check_kind_Type gctx (skctx, t)
	         val () = write_prop (False dummy, U.get_region_e e_all)
               in
	         (Never (t, r), t, T0 r)
               end
	     | ETBuiltin => 
               let
	         val t = check_kind_Type gctx (skctx, t)
	         val () = if !is_builtin_enabled then ()
                          else raise Error (r, ["builtin keyword is only available in standard library"])
               in
	         (Builtin (t, r), t, T0 r)
               end
          )
	| U.Abs (pn, e) => 
	  let
            val r = U.get_region_pn pn
            val t = fresh_mt gctx (sctx, kctx) r
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
	    (Abs (AnnoP (pn, t), e), Arrow (t, d, t1), T0 dummy)
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
	| U.AbsI (s, Bind ((name, r), e), r_all) => 
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
	    (AbsI (s, Bind ((name, r), e), r_all), UniI (s, Bind ((name, r), t), r_all), T0 r_all)
	  end 
	| U.Ascription (e, t) => 
	  let val t = check_kind_Type gctx (skctx, t)
	      val (e, _, d) = check_mtype (ctx, e, t)
          in
	    (Ascription (e, t), t, d)
	  end
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
                    IConst (ICTime _, r) => 
                    if eq_i d (T1 r) then T0 r 
                    else raise wrong_d
                  | (BinOpI (AddI, d1, d2)) => 
                    if eq_i d1 (T1 dummy) then d2
                    else if eq_i d2 (T1 dummy) then d1
                    else raise wrong_d
                  | _ => raise wrong_d
            val (is, e) =
                case e of
                    BinOp (EBApp, f, e) =>
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
    fun extra_msg () = ["when type-checking"] @ indent [U.str_e gctxn ctxn e_all]
    val (e, t, d) = main ()
    handle
    Error (r, msg) => raise Error (r, msg @ extra_msg ())
    | Impossible msg => raise Impossible $ join_lines $ msg :: extra_msg ()
    val t = simp_mt $ normalize_mt gctx kctx t
    val d = simp_i $ normalize_i d
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
          fun collect_uvar_t_ctx (_, _, _, tctx) = (concatMap collect_uvar_t_t o map snd) tctx (* cctx can't contain uvars *)
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
	      | BaseType a => BaseType a
              | TDatatype _ => raise Unimpl "check_decl()/substu()/TDatatype"
          fun evar_name n =
            if n < 26 then
              "'_" ^ (str o chr) (ord #"a" + n)
            else
              "'_" ^ str_int n
          val t = update_mt t
          val fv = dedup op= $ diff op= (map #1 $ collect_uvar_t_mt t) (map #1 $ collect_uvar_t_ctx ctx)
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
                      val t = fresh_mt gctx (sctx, kctx) r
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
              (* val () = println $ sprintf "sort and value of absidx $: \n$\n$" [name, str_s (gctx_names gctx) (sctx_names sctx) s, str_i (gctx_names gctx) (sctx_names sctx) i] *)
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
          | U.Open ((m, r), octx) =>
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
                  val ctx = fetch_module gctx (m, r)
                  (* val ctxd = package_ctx (m, r) ctxd  *)
                  val ctx = link_module (m, r) ctx
                in
                  ctx
                end
              val ctxd = clone_module gctx (m, r)
              val () = open_ctx ctxd
            in
              (Open ((m, r), octx), ctxd, 0, [])
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
      val ctxd = (map4 o map o mapSnd) (simp_t o update_t) ctxd
      val ds = map simp_i $ map update_i $ rev ds
                   (* val () = println "Typed Decls:" *)
                   (* val () = app println $ str_typing_info (gctx_names gctx) skctxn_old (ctxd, ds) *)
    in
      (decls, ctxd, nps, ds, ctx)
    end

and is_wf_datatype gctx ctx (Bind (name : string, tbinds) : U.mtype U.datatype_def, r) : (mtype datatype_def * region) * context =
    let
      val (tname_kinds, (sorts, constr_decls)) = unfold_binds tbinds
      val tnames = map fst tname_kinds
      val sorts = map is_wf_bsort sorts
      val nk = (name, (true, (length tnames, sorts), NONE))
      val ctx as (sctx, kctx, _, _) = add_kindingext_skct nk ctx
      fun make_constr ((name, ibinds, r) : U.mtype U.constr_decl) : mtype constr_decl * (string * mtype constr) =
	let
          val family = (NONE, (0, r))
          val c = (family, fold_binds (tname_kinds, ibinds))
	  val t = U.constr_type U.VarT shiftx_long_id c
	  val t = is_wf_type gctx ((sctx, kctx), t)
		  handle Error (_, msg) =>
			 raise Error (r, 
				      "Constructor is ill-formed" :: 
				      "Cause:" :: 
				      indent msg)
          val () = if length (collect_uvar_t_t t) > 0 then
                     raise Error (r, ["Constructor has unresolved unification type variable(s)"])
                   else ()
          val t = normalize_t gctx kctx t
          fun constr_from_type t =
            let
              val (tnames, t) = collect_Uni t
              val tnames = map fst tnames
              val (ns, t) = collect_UniI t
              fun err t = raise Impossible $ sprintf "constr_from_type (): type ($) not the right form" [str_raw_mt t]
              val (t, is) =
                  case t of
                      Arrow (t, _, t2) =>
                      (case is_AppV t2 of
                           SOME (_, _, is) => (t, is)
                         | NONE => err t2
                      )
                    | _ => err t
            in
              (tnames, fold_binds (ns, (t, is)))
            end
          val (_, ibinds) = constr_from_type t
	in
	  ((name, ibinds, r), (name, (family, fold_binds (tname_kinds, ibinds))))
	end
      val (constr_decls, constrs) = (unzip o map make_constr) constr_decls
    in
      ((Bind (name, fold_binds (tname_kinds, (sorts, constr_decls))), r), ([], add_kindingext nk [], rev constrs, []))
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
    val mod_name = find_unique (domain gctx) "__link_sig_module" 
    val gctx = add_sigging (mod_name, ctx) gctx
    val () = open_module (mod_name, ctx)
    val _ = link_sig r gctx (mod_name, r) ctx'
    val () = close_n 1
  in
    ()
  end
    
fun is_wf_sig gctx (comps, r) =
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
            val k = is_wf_kind k
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

fun check_top_bind gctx (name, bind) =
  let
    val gctxd = 
        case bind of
            U.TopModBind m =>
            let
              val sg = get_sig gctx m
            in
              [(name, Sig sg)]
            end
          | U.TopFunctorBind (((arg_name, _), arg), m) =>
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
          | U.TopFunctorApp (f, m) =>
            let
              fun lookup_functor gctx m =
                opt_bind (Gctx.find (gctx, m)) is_FunctorBind
              fun fetch_functor gctx ((m, r) : mod_projectible) =
                case lookup_functor gctx m of
                    SOME a => a
                  | NONE => raise Error (r, ["Unbound functor " ^ m])
              val ((formal_arg_name, formal_arg), body) = fetch_functor gctx f
              val formal_arg = link_sig (snd m) gctx m formal_arg
            in
              [(name, Sig body), (formal_arg_name, Sig formal_arg)]
            end
    (* val () = println $ sprintf "Typechecked program:" [] *)
    (* val () = app println $ map fst gctxd *)
    (* val () = app println $ str_gctx (gctx_names gctx) gctxd *)
  in
    gctxd
  end
    
open CollectMod
       
fun collect_mod_ke (dt, k, t) = default [] (Option.map collect_mod_mt t)
                                        
fun collect_mod_ctx ((sctx, kctx, cctx, tctx) : context) =
  let
    val acc = []
    val acc = (concatMap collect_mod_s $ map snd sctx) @ acc
    val acc = (concatMap collect_mod_ke $ map snd kctx) @ acc
    val acc = (concatMap collect_mod_constr $ map snd cctx) @ acc
    val acc = (concatMap collect_mod_t $ map snd tctx) @ acc
  in
    acc
  end
    
fun collect_mod_sgntr b =
  case b of
      Sig ctx => collect_mod_ctx ctx
    | FunctorBind ((name, arg), ctx) => diff op = (collect_mod_ctx ctx) [name]
                                             
structure SU = SetUtilFn (StringBinarySet)
structure S = StringBinarySet
                         
fun get_dependency_graph gctx = Gctx.map (SU.to_set o collect_mod_sgntr) gctx

exception TopoSortFailed
fun topo_sort in_graph =
  let
    fun find_empty_nodes g = Gctx.foldli (fn (k, v, acc) => if S.isEmpty v then S.add (acc, k) else acc) S.empty g
    fun loop (in_graph, done) =
      if Gctx.length in_graph <= 0 then
        done
      else
        let
          val nodes = find_empty_nodes in_graph
          val () = if S.isEmpty nodes then raise TopoSortFailed else ()
          val in_graph : S.set Gctx.map = remove_many in_graph $ SU.enumerate nodes
          val in_graph = Gctx.map (fn s => S.difference (s, nodes)) in_graph
        in
          loop (in_graph, SU.to_list nodes @ done)
        end
    val ret = rev $ loop (in_graph, [])
    val () = assert (fn () => length ret = Gctx.length in_graph) "length ret = Gctx.length in_graph"
  in
    ret
  end

fun check_prog gctx (binds : U.prog) =
    let
      (* val () = println "Begin check_prog()" *)
      fun open_gctx gctx =
        let
          val gctx = filter_module gctx
        in
          app open_module $ find_many gctx $ topo_sort $ Gctx.map (SU.to_set o collect_mod_ctx) $ gctx
          handle TopoSortFailed =>
                 raise Error (dummy, [sprintf "There is circular dependency in models $" [str_ls id $ domain gctx]])
        end
      fun close_gctx gctx =
        close_n $ Gctx.length $ filter_module gctx
      fun iter (((name, r), bind), (acc, gctx)) =
        let
          val () = open_gctx gctx
          val gctxd = check_top_bind gctx (name, bind)
          val () = close_gctx gctx
        in
          (gctxd @ acc, addList (gctx, gctxd))
        end
      val ret as (gctxd, gctx) = foldl iter ([], gctx) binds
                                       (* val () = println "End check_prog()" *)
    in
      ret
    end

end
