structure PreTypeCheck = struct
structure U = UnderscoredExpr
open Region
open Expr
open Simp
       
infixr 0 $

infix 7 %*
infix 6 %+
infix 4 %<=
infixr 3 /\
infixr 2 \/
infixr 1 -->
infix 1 <->

open Subst

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
      | TimeApp => raise Impossible "idx_bin_op_type ()"
      | EqI => raise Impossible "idx_bin_op_type ()"
      | LtI => raise Impossible "idx_bin_op_type ()"
      | GeI => raise Impossible "idx_bin_op_type ()"
      | AddI => raise Impossible "idx_bin_op_type ()"
      | MultI => raise Impossible "idx_bin_op_type ()"
      | BoundedMinusI => raise Impossible "idx_bin_op_type ()"

(* sorting context *)
type scontext = (string (* option *) * sort) list
(* kinding context *)
datatype kind_ext =
         KeKind of kind
         | KeTypeEq of kind * ty
(* type kinding = kind *)
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
         | FactorBind of (string * sgntr) list * sgntr
                                                   (* signaturing context *)
                                                   (* withtype sigcontext = (string * sgntr) list *)
                                                   (* withtype sigcontext = unit *)

type sigcontext = (string * sgntr) list
                                   
fun names ctx = map fst ctx

fun shiftx_i_ke x n k =
    case k of
        KeKind k => KeKind $ shiftx_i_k x n k
      | KeTypeEq (k, t) => KeTypeEq (shiftx_i_k x n k, shiftx_i_t x n t)
                    
fun shiftx_t_ke x n k =
    case k of
        KeKind k => KeKind k
      | KeTypeEq (k, t) => KeTypeEq (k, shiftx_t_t x n t)
                    
fun shiftx_m_ke x n k =
    case k of
        KeKind k => KeKind $ shiftx_m_k x n k
      | KeTypeEq (k, t) => KeTypeEq (shiftx_m_k x n k, shiftx_m_t x n t)
                    
fun shiftx_i_ps n ps = 
    map (shiftx_i_p 0 n) ps
fun shiftx_i_ks n ctx = 
    map (mapSnd (shiftx_i_ke 0 n)) ctx
fun shiftx_i_cs n ctx = 
    map (mapSnd (shiftx_i_c 0 n)) ctx
fun shiftx_t_cs n ctx = 
    map (mapSnd (shiftx_t_c 0 n)) ctx
fun shiftx_i_ts n ctx = 
    map (mapSnd (shiftx_i_t 0 n)) ctx
fun shiftx_t_ts n ctx = 
    map (mapSnd (shiftx_t_t 0 n)) ctx

fun add_sorting (name, s) pairs = ((* SOME  *)name, s) :: pairs
fun add_sorting_sk pair (sctx, kctx) = 
    (add_sorting pair sctx, 
     shiftx_i_ks 1 kctx)
fun add_sorting_skc pair (sctx, kctx, cctx) = 
    (add_sorting pair sctx, 
     shiftx_i_ks 1 kctx,
     shiftx_i_cs 1 cctx)
fun add_sorting_skct pair (sctx, kctx, cctx, tctx) = 
    (add_sorting pair sctx, 
     shiftx_i_ks 1 kctx, 
     shiftx_i_cs 1 cctx, 
     shiftx_i_ts 1 tctx)
(* Within 'pairs', sort depends on previous sort *)
fun add_sortings_skct pairs' (pairs, kctx, cctx, tctx) : context = 
    let
      val n = length pairs' 
    in
      ((* map (mapFst SOME) *) pairs' @ pairs, 
                               shiftx_i_ks n kctx, 
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
       shiftx_i_ks n kctx)
    end
fun add_nondep_sortings_skc pairs (sctx, kctx, cctx) = 
    let val n = length pairs
    in
      (add_nondep_sortings pairs sctx,
       shiftx_i_ks n kctx,
       shiftx_i_ks n cctx)
    end
*)
fun sctx_names (ctx : scontext) = (* List.mapPartial id $ *) map fst ctx
fun sctx_length (ctx : scontext) = length $ sctx_names ctx

(* fun is_named (name, s) = case name of SOME name => SOME (name, s) | NONE => NONE *)
fun lookup_sort (n : int) (ctx : scontext) : sort option =
    case nth_error ((* List.mapPartial is_named *) ctx) n of
        NONE => NONE
      | SOME (_, s) => 
        SOME (shiftx_i_s 0 (n + 1) s)

fun lookup_kind_ext (n : int) kctx = 
    case nth_error kctx n of
        NONE => NONE
      | SOME (_, k) => SOME $ shiftx_t_ke 0 (n + 1) k

fun get_ke_kind k =
    case k of
        KeKind k => k
      | KeTypeEq (k, _) => k
                             
fun lookup_kind (n : int) kctx = 
    case nth_error kctx n of
        NONE => NONE
      | SOME (_, k) => SOME $ get_ke_kind k

fun add_kinding pair (kctx : kcontext) = mapSnd KeKind pair :: kctx
fun add_kinding_kc pair (kctx, cctx) = 
    (add_kinding pair kctx, 
     shiftx_t_cs 1 cctx)
fun add_kinding_kct pair (kctx, cctx, tctx) = 
    (add_kinding pair kctx,
     shiftx_t_cs 1 cctx,
     shiftx_t_ts 1 tctx)
fun add_kinding_skct pair (sctx, kctx, cctx, tctx) = 
    (sctx,
     add_kinding pair kctx,
     shiftx_t_cs 1 cctx,
     shiftx_t_ts 1 tctx)
fun add_kinding_sk pair (sctx, kctx) = 
    (sctx, 
     add_kinding pair kctx)
fun add_kindings_skct pairs (sctx, kctx, cctx, tctx) =
    let val n = length pairs in
      (sctx,
       pairs @ kctx,
       shiftx_t_cs n cctx,
       shiftx_t_ts n tctx)
    end

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

fun lookup_type (n : int) (ctx : tcontext) : ty option = 
    case nth_error ctx n of
        NONE => NONE
      | SOME (_, t) => SOME t

fun ctx_names (sctx, kctx, cctx, tctx) =
    (sctx_names sctx, names kctx, names cctx, names tctx) 

fun add_ctx (sctx, kctx, cctx, tctx) ctx =
    let val ctx = add_sortings_skct sctx ctx
        val ctx = add_kindings_skct kctx ctx
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
fun ctx_from_typing pair : context = ([], [], [], [pair])

open UVar
val expand_i = expand_i shiftx_i_i
val expand_s = expand_s shiftx_i_s
val expand_mt = expand_mt shiftx_i_mt shiftx_t_mt
                          
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
      | Base _ => bs

fun update_i i =
    case i of
        UVarI ((invis, x), r) => 
        (case !x of
             Refined i => 
             let 
               val i = update_i i
               val () = x := Refined i
             in
               expand_i invis i
             end
           | Fresh _ => i
        )
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
      | TimeAbs (name, i, r) => TimeAbs (name, update_i i, r)

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
        UVarS ((invis, x), r) =>
        (case !x of
             Refined s => 
             let 
               val s = update_s s
               val () = x := Refined s
             in
               expand_s invis s
             end
           | Fresh _ => s
        )
      | Basic _ => s
      | Subset _ => s

fun update_mt t =
    case t of
        UVar ((invis, x), r) => 
        (case !x of
             Refined t => 
             let 
               val t = update_mt t
               val () = x := Refined t
             in
               expand_mt invis t
             end
           | Fresh _ => t
        )
      | Unit r => Unit r
      | Arrow (t1, d, t2) => Arrow (update_mt t1, update_i d, update_mt t2)
      | Prod (t1, t2) => Prod (update_mt t1, update_mt t2)
      | UniI (s, Bind (name, t1), r) => UniI (update_s s, Bind (name, update_mt t1), r)
      | AppV (y, ts, is, r) => AppV (y, map update_mt ts, map update_i is, r)
      | BaseType a => BaseType a

fun hnf_mt t =
    case t of
        UVar ((invis, x), r) => 
        (case !x of
             Refined t => 
             let 
               val t = hnf_mt t
               val () = x := Refined t
             in
               expand_mt invis t
             end
           | Fresh _ => t
        )
      | _ => t

fun update_t t =
    case t of
        Mono t => Mono (update_mt t)
      | Uni (Bind (name, t), r) => Uni (Bind (name, update_t t), r)

exception Error of region * string list

fun runError m _ =
    OK (m ())
    handle
    Error e => Failed e

type anchor = (bsort, idx) uvar_ref_i
                           
datatype vc_entry =
         ForallVC of string (* option  *)* sort
         | ImplyVC of prop
         | PropVC of prop * region
         | AdmitVC of prop * region
         (* remember where unification index variable is introduced, since those left over will be converted into existential variables in VC formulas *)
         | AnchorVC of anchor
         | OpenVC
         | CloseVC

val acc = ref ([] : vc_entry list)

fun write x = push_ref acc x

fun open_ctx (ctx as (sctx, _, _, _)) = (app write o map ForallVC o rev) sctx

fun close_ctx (ctx as (sctx, _, _, _)) = app (fn _ => write CloseVC) sctx

fun open_sorting ns = write o ForallVC $ (* mapFst SOME *) ns

fun open_premises ps = (app write o map ImplyVC) ps

fun open_vc () = write OpenVC

fun close_vc () = write CloseVC

fun close_vcs n = repeat_app close_vc n

fun write_anchor anchor = write (AnchorVC anchor)

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

fun unify_error r (s, s') =             
    Error (r, ["Can't unify"] @ indent [s] @ ["and"] @ indent [s'])

(* fun handle_ue ctx e =              *)
(*     raise Error (get_region_e e,  *)
(*                  #2 (mismatch ctxn e (str_t (sctxn, kctxn) t) t') @ *)
(*                  "Cause:" :: *)
(*                  indent msg) *)

(* datatype UnifyErrorData = *)
(*          UEI of idx * idx *)
(*          | UES of sort * sort *)
(*          | UET of mtype * mtype *)

(* exception UnifyError of UnifyErrorData *)

(* assumes arguments are already checked for well-formedness *)

fun unify_bs r (bs, bs') =
    case (bs, bs') of
        (UVarBS x, _) =>
        refine x bs'
      | (_, UVarBS _) =>
        unify_bs r (bs', bs)
      | (Base b, Base b') =>
        if b = b' then
	  ()
        else
	  raise Error (r, [sprintf "Base sort mismatch: $ and $" [str_b b, str_b b']])
		
fun shrink_i invis b = shrink forget_i_i invis b
fun shrink_s invis b = shrink forget_i_s invis b
fun shrink_mt (invisi, invist) b = (shrink forget_i_mt invisi o shrink forget_t_mt invist) b

fun unify_i r gctx ctx (i, i') =
    let
      val unify_i = unify_i r gctx
      fun error (i, i') = unify_error r (str_i gctx ctx i, str_i gctx ctx i')
      val i = update_i i
      val i' = update_i i'
    in
      case (i, i') of
          (UVarI ((invis, x), _), UVarI ((invis', x'), _)) =>
          if x = x' then ()
          else
            (refine x (shrink_i invis i')
	     handle 
             ForgetError _ => 
             refine x' (shrink_i invis' i)
             handle ForgetError _ => raise error (i, i')
            )
        | (UVarI ((invis, x), _), _) =>
          (refine x (shrink_i invis i')
	   handle ForgetError _ => raise error (i, i')
          )
        | (_, UVarI _) =>
          unify_i ctx (i', i)
        (* ToReal is injective *)
        | (UnOpI (ToReal, i, _), UnOpI (ToReal, i', _)) =>
          unify_i ctx (i', i)
	| _ => 
          if eq_i i i' then ()
          else write_prop (BinPred (EqP, i, i'), r)
    end

fun unify_s r gctx ctx (s, s') =
    let
      val unify_s = unify_s r gctx
      fun error (s, s') = unify_error r (str_s gctx ctx s, str_s gctx ctx s')
      val s = update_s s
      val s' = update_s s'
    in
      (* UVarS can only be fresh *)
      case (s, s') of
          (UVarS ((invis, x), _), UVarS ((invis', x'), _)) =>
          if x = x' then ()
          else
            (refine x (shrink_s invis s')
	     handle 
             ForgetError _ => 
             refine x' (shrink_s invis' s)
             handle ForgetError _ => raise error (s, s')
            )
        | (UVarS ((invis, x), _), _) =>
          (refine x (shrink_s invis s')
	   handle ForgetError _ => raise error (s, s')
          )
        | (_, UVarS _) => 
          unify_s ctx (s', s)
	| (Basic (bs, _), Basic (bs', _)) =>
	  unify_bs r (bs, bs')
	| (Subset ((bs, r1), Bind ((name, _), p), _), Subset ((bs', _), Bind (_, p'), _)) =>
          let
	    val () = unify_bs r (bs, bs')
            val ctxd = ctx_from_sorting (name, Basic (bs, r1))
            val () = open_ctx ctxd
	    val () = write_prop (p <-> p', r)
            val () = close_ctx ctxd
          in
            ()
          end
	| (Subset ((bs, r1), Bind ((name, _), p), _), Basic (bs', _)) =>
          let
	    val () = unify_bs r (bs, bs')
            val ctxd = ctx_from_sorting (name, Basic (bs, r1))
            val () = open_ctx ctxd
	    val () = write_prop (p, r)
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
    end

fun unify_sorts r gctx ctx (sorts, sorts') =
    (check_length r (sorts, sorts');
     ListPair.app (unify_s r gctx ctx) (sorts, sorts'))

fun unify r gctx =
    let
      fun error ctx (t, t') = unify_error r (str_mt gctx ctx t, str_mt gctx ctx t')
      fun loop (ctx as (sctx, kctx)) (t, t') =
          let 
            val t = update_mt t
            val t' = update_mt t'
          in
            (* UVar can only be fresh *)
            case (t, t') of
                (UVar ((invis, x), _), UVar ((invis', x'), _)) =>
                if x = x' then ()
                else
                  (* ToDo: potentially dangerous because [shrink_mt invis t'] may not be transactional so may not be safe to roll back *)
                  (refine x (shrink_mt invis t')
		   handle
                   ForgetError _ =>
                   refine x' (shrink_mt invis' t)
                   handle ForgetError _ => raise error ctx (t, t')
                  )
              | (UVar ((invis, x), _), _) =>
                (refine x (shrink_mt invis t')
	         handle ForgetError _ => raise error ctx (t, t')
                )
              | (_, UVar _) => loop ctx (t', t)
              | (Arrow (t1, d, t2), Arrow (t1', d', t2')) =>
                (loop ctx (t1, t1');
                 unify_i r gctx sctx (d, d');
                 loop ctx (t2, t2'))
              | (Prod (t1, t2), Prod (t1', t2')) =>
                (loop ctx (t1, t1');
                 loop ctx (t2, t2'))
              | (UniI (s, Bind ((name, _), t1), _), UniI (s', Bind (_, t1'), _)) =>
                (unify_s r gctx sctx (s, s');
                 open_sorting (name, s);
                 loop (name :: sctx, kctx) (t1, t1');
                 close_vc ())
              | (Unit _, Unit _) => ()
	      | (BaseType (Int, _), BaseType (Int, _)) => ()
	      | (AppV ((a, _), ts, is, _), AppV ((a', _), ts', is', _)) => 
	        if a = a' then
		  (ListPair.app (loop ctx) (ts, ts');
                   ListPair.app (unify_i r gctx sctx) (is, is'))
	        else
		  raise error ctx (t, t')
	      | _ => raise error ctx (t, t')
          end
    in
      loop
    end

val counter = ref 0

fun inc () = 
    let 
      val n = !counter
      val () = counter := n + 1
    in
      n
    end

fun fresh_bsort () = UVarBS (ref (Fresh (inc ())))

fun fresh_i names bsort r = 
    let
      val uvar_ref = ref (Fresh (inc (), names, bsort))
      val () = write_anchor uvar_ref
    in
      UVarI (([], uvar_ref), r)
    end

fun fresh_nonidx f empty_invis names r = 
    f ((empty_invis, ref (Fresh (inc (), names))), r)

fun fresh_sort names r : sort = fresh_nonidx UVarS [] names r
fun fresh_mt names r : mtype = fresh_nonidx UVar ([], []) names r

fun sort_mismatch gctx ctx i expect have =  "Sort mismatch for " ^ str_i gctx ctx i ^ ": expect " ^ expect ^ " have " ^ str_s gctx ctx have

fun is_wf_bsort (bs : U.bsort) : bsort =
    case bs of
        U.Base bs => Base bs
      | U.UVarBS () => fresh_bsort ()

fun get_base r gctx ctx s =
    case update_s s of
        Basic (s, _) => s
      | Subset ((s, _), _, _) => s
      | UVarS _ => raise Error (r, [sprintf "Can't figure out base sort of $" [str_s gctx ctx s]])

val get_outmost_module = id

fun lookup_module gctx m = nth_error (List.mapPartial (fn (_, sg) => case sg of Sig sg => SOME sg | _ => NONE) gctx) m
                                     
fun fetch_from_module (params as (shift, do_fetch)) (* sigs *) gctx ((m, mr), x) =
    let
      (* val fetch_from_module = fetch_from_module params (* sigs *) *)
      (* fun fetch_from_module_or_ctx gctx ctx (m, x) = *)
      (*     case m of *)
      (*         NONE => do_fetch (ctx, x) *)
      (*       | SOME m => fetch_from_module gctx (m, x) *)
      (* val ((m, r), x) = get_outmost_module (m, x) *)
      val ((* gctx,  *)ctx) = case lookup_module gctx m of
                                SOME sg => sg
                              | NONE => raise Error (mr, ["Unbounded module"])
      (* val v = fetch_from_module_or_ctx gctx ctx x *)
      val v = do_fetch (ctx, x)
      (* val v = package 0 (length gctx) v *)
      val v = shift 0 (m + 1) v
    in
      v
    end
      
fun generic_fetch shift do_fetch sel (ggctx as ((* sigs,  *)gctx)) (fctx, (m, x)) =
    case m of
        NONE => do_fetch (fctx, x)
      | SOME m => fetch_from_module (shift, do_fetch o mapFst sel) (* sigs *) gctx (m, x)

fun do_fetch_sort (ctx, (x, r)) =
    case lookup_sort x ctx of
      	SOME s => s
      | NONE => raise Error (r, ["Unbound index variable: " ^ str_v (sctx_names ctx) x])

fun fetch_sort a = generic_fetch shiftx_m_s do_fetch_sort #1 a
                               
fun is_wf_sort gctx (ctx : scontext, s : U.sort) : sort =
    let
      val is_wf_sort = is_wf_sort gctx
      val is_wf_prop = is_wf_prop gctx
      val get_bsort = get_bsort gctx
      val check_bsort = check_bsort gctx
    in
    case s of
	U.Basic (bs, r) => Basic (is_wf_bsort bs, r)
      | U.Subset ((bs, r), Bind ((name, r2), p), r_all) =>
        let 
          val bs = is_wf_bsort bs
        in
          (* ToDo: need to [open_sorting] *)
          Subset ((bs, r),
                  Bind ((name, r2), 
                         is_wf_prop (add_sorting (name, Basic (bs, r)) ctx, p)), r_all)
        end
      | U.UVarS ((), r) => fresh_sort (sctx_names ctx) r
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
                  (case bs of
                       Base (TimeFun _) => ()
                     | _ => raise error "TimeFun"
                  )
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
          val p = is_wf_prop (add_sorting (name, Basic (bs, r)) ctx, p)
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
              in
                (VarI x, get_base (U.get_region_i i) (names gctx) (sctx_names ctx) s)
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
                    TimeApp =>
                    let
                      (* val () = println $ U.str_i (names ctx) i *)
                    in
                      case get_bsort (ctx, i1) of
                          (i1, Base (TimeFun arity)) =>
                          if arity > 0 then
                            let 
                              val i2 = check_bsort (ctx, i2, Base Nat)
                            in
                              (BinOpI (opr, i1, i2), Base (TimeFun (arity - 1)))
                            end
                          else
                            raise Error (get_region_i i1, "Arity of time function must be larger than 0" :: indent ["got arity: " ^ str_int arity, "in: " ^ str_i (names gctx) (sctx_names ctx) i1])
                        | (i1, bs1) => raise Error (get_region_i i1, "Sort of first operand of time function application must be time function" :: indent ["want: time function", "got: " ^ str_bs bs1, "in: " ^ str_i (names gctx) (sctx_names ctx) i1])
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
            | U.TimeAbs ((name, r1), i, r) =>
              (case get_bsort (add_sorting (name, Basic (Base Nat, r1)) ctx, i) of
                   (i, Base (TimeFun arity)) =>
                   (TimeAbs ((name, r1), i, r), Base (TimeFun (arity + 1)))
                 | (_, bs) => raise Error (U.get_region_i i, "Sort of time funtion body should be time function" :: indent ["want: time function", "got: " ^ str_bs bs])
              )
	    | U.AdmitI r => 
              (AdmitI r, Base UnitSort)
            | U.UVarI ((), r) =>
              let
                val bs = fresh_bsort ()
              in
                (fresh_i (sctx_names ctx) bs r, bs)
              end
      val ret = main ()
                handle
                Error (r, msg) => raise Error (r, msg @ ["when sort-checking index "] @ indent [U.str_i (names gctx) (sctx_names ctx) i])
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
      val s = update_s s
      val () =
	  (case s of
	       Subset ((bs, _), Bind ((name, _), p), _) =>
               let
	         val () = unify_bs r (bs', bs)
                 val r = get_region_i i
                 val (i, is_admit) = case i of
                                         AdmitI r => (TTI r, true)
                                       | _ => (i, false)
                 val p = subst_i_p i p
                         handle
                         SubstUVar info =>
                         raise subst_uvar_error (get_region_p p) ("proposition " ^ str_p (names gctx) (name :: sctx_names ctx) p) i info
                 (* val () = println $ sprintf "Writing prop $ $" [str_p (sctx_names ctx) p, str_region "" "" r] *)
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
             | UVarS ((_, x), _) =>
               (case !x of
                    Refined _ => raise Impossible "check_sort (): s should be Fresh"
                  | Fresh _ => 
                    refine x (Basic (bs', dummy))
               )
          )
          handle Error (_, msg) =>
                 let
                   val ctxn = sctx_names ctx
                   val gctxn = names gctx
                 in
                   raise Error (r,
                                sprintf "index $ (of base sort $) is not of sort $" [str_i gctxn ctxn i, str_bs bs', str_s gctxn ctxn s] ::
                                "Cause:" ::
                                indent msg)
                 end
    in
      i
    end

fun check_sorts gctx (ctx, is : U.idx list, sorts, r) : idx list =
    (check_length r (is, sorts);
     ListPair.map (fn (i, s) => check_sort gctx (ctx, i, s)) (is, sorts))

(* k => Type *)
fun recur_kind k = ArrowK (false, 0, k)

fun kind_mismatch gctx (ctx as (sctx, kctx)) c expect have = "Kind mismatch for " ^ str_t gctx ctx c ^ ": expect " ^ expect ^ " have " ^ str_k gctx sctx have

fun do_fetch_kind (kctx, (a, r)) =
    case lookup_kind a kctx of
      	SOME k => k
      | NONE => raise Error (r, ["Unbound type variable: " ^ str_v (names kctx) a])

fun fetch_kind a = generic_fetch shiftx_m_k do_fetch_kind #2 a

(* could also be named 'check_kind_Type' *)
fun is_wf_mtype gctx (ctx as (sctx : scontext, kctx : kcontext), c : U.mtype) : mtype = 
    let
      val is_wf_mtype = is_wf_mtype gctx
      val gctxn = names gctx
      val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
      (* val () = print (sprintf "Type wellformedness checking: $\n" [str_t ctxn c]) *)
      fun main () =
          case c of
	      U.Arrow (c1, d, c2) => 
	      Arrow (is_wf_mtype (ctx, c1),
	             check_bsort gctx (sctx, d, Base Time),
	             is_wf_mtype (ctx, c2))
            | U.Unit r => Unit r
	    | U.Prod (c1, c2) => 
	      Prod (is_wf_mtype (ctx, c1),
	            is_wf_mtype (ctx, c2))
	    | U.UniI (s, Bind ((name, r), c), r_all) => 
              let
                val s = is_wf_sort gctx (sctx, s)
              in
                (* ToDo: need to [open_sorting] *)
	        UniI (s,
	              Bind ((name, r), 
                             is_wf_mtype (add_sorting_sk (name, s) ctx, c)), r_all)
              end
	    | U.AppV (x, ts, is, r) => 
              let
                val ArrowK (_, n, sorts) = fetch_kind gctx (kctx, x)
	        val () = check_length_n r (ts, n)
              in
	        AppV (x, 
                      map (fn t => is_wf_mtype (ctx, t)) ts, 
                      check_sorts gctx (sctx, is, sorts, r), 
                      r)
              end
	    | U.BaseType a => BaseType a
            | U.UVar ((), r) => fresh_mt (sctxn @ kctxn) r
      val ret =
          main ()
          handle
          Error (r, msg) => raise Error (r, msg @ ["when checking well-formed-ness of type "] @ indent [U.str_mt gctxn ctxn c])
    in
      ret
    end

fun is_wf_type gctx (ctx as (sctx : scontext, kctx : kcontext), c : U.ty) : ty = 
    let 
      val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	                             (* val () = print (sprintf "Type wellformedness checking: $\n" [str_t ctxn c]) *)
    in
      case c of
          U.Mono t =>
          Mono (is_wf_mtype gctx (ctx, t))
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

fun fetch_constr (ctx, (x, r)) =
    case nth_error ctx x of
	SOME (name, c) => (name, c)
      | NONE => raise Error (r, [sprintf "Unbound constructor: $" [str_v (names ctx) x]])

fun fetch_constr_type (ctx : ccontext, cx) =
    let val (cname, c) = fetch_constr (ctx, cx)
	val t = constr_type VarT shiftx_v c
    in
      (cname, t)
    end

(* redundancy and exhaustiveness checking *)
(* all the following cover operations assume that the cover has type t *)

datatype cover =
         TrueC
         | FalseC
         | AndC of cover * cover
         | OrC of cover * cover
         | ConstrC of var * cover
         | PairC of cover * cover
         | TTC

fun combine_covers covers = foldl' (swap OrC) FalseC covers

datatype habitant =
         TrueH
         | ConstrH of var * habitant
         | PairH of habitant * habitant
         | TTH

local
  
  fun str_cover cctx c =
      case c of
          TrueC => "true"
        | FalseC => "false"
        | AndC (c1, c2) => sprintf "($ /\\ $)" [str_cover cctx c1, str_cover cctx c2]
        | OrC (c1, c2) => sprintf "($ \\/ $)" [str_cover cctx c1, str_cover cctx c2]
        | ConstrC (x, c) => sprintf "($ $)" [str_v cctx x, str_cover cctx c]
        | PairC (c1, c2) => sprintf "($, $)" [str_cover cctx c1, str_cover cctx c2]
        | TTC => "()"

  fun str_habitant cctx c =
      case c of
          TrueH => "_"
        | ConstrH (x, c) => sprintf "($ $)" [str_v cctx x, str_habitant cctx c]
        | PairH (c1, c2) => sprintf "($, $)" [str_habitant cctx c1, str_habitant cctx c2]
        | TTH => "()"

  infixr 3 /\
  infixr 2 \/
  val op/\ = AndC
  val op\/ = OrC

  fun impossible s = Impossible $ "cover has the wrong type: " ^ s

  fun get_family (x : constr) = #1 x

  (* fun get_family_members cctx x = *)
  (*   (rev o List.mapPartial (fn (n, (_, c)) => if get_family c = x then SOME n else NONE) o add_idx) cctx *)
  fun get_family_members cctx x =
      (rev o map fst o mapPartialWithIdx (fn (n, (_, c)) => if get_family c = x then SOME () else NONE)) cctx

  fun cover_neg (ctx as (_, kctx, cctx)) (t : mtype) c =
      let
        fun neg t c = cover_neg ctx t c
        (* val t = update_mt t *)
        val t = hnf_mt t
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
	         AppV ((family, _), ts, _, _) =>
	         let
                   val all = get_family_members cctx family
		   val others = diff op= all [x]
                   val (_, (_, _, ibinds)) = fetch_constr (cctx, (x, dummy))
                   val (_, (t', _)) = unfold_ibinds ibinds
		   val t' = subst_ts_mt ts t'
                   val covers = ConstrC (x, neg t' c) :: map (fn y => ConstrC (y, TrueC)) others
	         in
                   combine_covers covers
	         end
	       | _ => raise impossible $ sprintf "cover_neg()/ConstrC:  cover is $ but type is " [str_cover (names cctx) c_all, str_mt ([], names kctx) t])
      end

  (* fun cover_imply cctx t (a, b) : cover = *)
  (*     cover_neg cctx t a \/ b *)

  (* find habitant
       deep: when turned on, [find_hab] try to find a [ConstrH] for a datatype when constraints are empty (treat empty datatype as uninhabited); otherwise only return [TrueH] in such case (treat empty datatype as inhabited) *)
  fun find_hab deep (ctx as (sctx, kctx, cctx)) (t : mtype) cs =
      let
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
        (*     case hnf_mt t of *)
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
              (* val t = update_mt t *)
              val t = hnf_mt t
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
                      (* val () = Debug.println (sprintf "Empty constraints now. Now try to find any inhabitant of type $" [str_mt (sctx_names sctx, names kctx) t]) *)
                    in
                      case t of
                          AppV (tx as (family, _), _, _, _) =>
                          (case fetch_kind (kctx, tx) of
                               ArrowK (true, _, _) =>
	                       let
                                 val all = get_family_members cctx family
                               in
                                 case all of x :: _ => ConstrH (x, TrueH) | [] => raise Incon "empty datatype"
                               end
                             | _ => TrueH (* an abstract type is treated as an inhabited type *)
                          )
                        | Unit _ => TTH
                        | Prod (t1, t2) => PairH (loop $ check_size (t1, []), loop $ check_size (t2, []))
                        | _ => TrueH
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
                          | (ConstrC (x, c'), AppV ((family, _), ts, _, _)) =>
                            let
                              fun same_constr c =
                                  case c of
                                      ConstrC (y, c) =>
                                      if y = x then
                                        SOME c
                                      else
                                        raise Incon "diff-constr"
                                    | _ => NONE
                            in
                              case allSome same_constr cs of
                                  OK cs' =>
                                  let
                                    val (_, (_, _, ibinds)) = fetch_constr (cctx, (x, dummy))
                                    val (_, (t', _)) = unfold_ibinds ibinds
		                    val t' = subst_ts_mt ts t'
                                    (* val () = (* Debug. *)println (sprintf "All are $, now try to satisfy $" [str_v (names cctx) x, (join ", " o map (str_cover (names cctx))) (c' :: cs')]) *)
                                    val c' = loop $ check_size (t', c' :: cs')
                                                  (* val () = Debug.println (sprintf "Plugging $ into $" [str_habitant (names cctx) c', str_v (names cctx) x]) *)
                                  in
                                    inl $ ConstrH (x, c')
                                  end
                                | Failed (i, dissident) =>
                                  if conflict c dissident then
                                    raise Incon $ "conflicts on constructor " ^ str_int x
                                  else
                                    inr (dissident, c :: remove i cs, t)
                            end
                          | _ => inr (c, cs, t)
                  in
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
                  end
            end
      in
        SOME (loop (t, cs, ())) handle Incon debug => NONE
      end

in              

fun any_missing deep ctx t c =
    let
      (* val t = update_mt t *)
      val nc = cover_neg ctx t c
      (* val () = println "after cover_neg()" *)
      (* val () = (* Debug. *)println (str_cover (names (#3 ctx)) nc) *)
      (* val () = println "before find_hab()" *)
      val ret = find_hab deep ctx t [nc]
                         (* val () = println "after find_hab()" *)
    in
      ret
    end

fun is_redundant (ctx, t, prevs, this) =
    let
      (* fun is_covered ctx t small big = *)
      (*     (isNull o (* (trace "after any_missing()") o *) any_missing true(*treat empty datatype as uninhabited*) ctx t o (* (trace "after cover_imply()") o *) cover_imply ctx t) (small, big) *)
      (* val t = update_mt t *)
      val prev = combine_covers prevs
      (* val () = println "after combine_covers()" *)
      (* val something_new = not (is_covered ctx t this prev) *)
      val something_new = isSome $ find_hab true(*treat empty datatype as uninhabited*) ctx t $ [this, cover_neg ctx t prev]                                  
                                 (* val () = println "after is_covered()" *)
    in
      something_new
    end
      
fun check_redundancy (ctx as (_, _, cctx), t, prevs, this, r) =
    let
    in
      if is_redundant (ctx, t, prevs, this) then ()
      else
        raise Error (r, sprintf "Redundant rule: $" [str_cover (names cctx) this] :: indent [sprintf "Has already been covered by previous rules: $" [(join ", " o map (str_cover (names cctx))) prevs]])
    end
      
fun is_exhaustive (ctx as (_, _, cctx), t : mtype, covers) =
    let
      (* val t = update_mt t *)
      val cover = combine_covers covers
                                 (* val () = Debug.println (str_cover (names cctx) cover) *)
    in
      any_missing true(*treat empty datatype as uninhabited*) ctx t cover
    end
      
fun check_exhaustion (ctx as (_, _, cctx), t : mtype, covers, r) =
    let
    in
      case is_exhaustive (ctx, t, covers) of
          NONE => ()
        | SOME missed =>
	  raise Error (r, [sprintf "Not exhaustive, at least missing this case: $" [str_habitant (names cctx) missed]])
    end

end

fun get_ds (_, _, _, tctxd) = map (snd o snd) tctxd

fun escapes nametype name domaintype domain cause =
    [sprintf "$ $ escapes local scope in $ $" [nametype, name, domaintype, domain]] @ indent (if cause = "" then [] else ["cause: it is (potentially) used by " ^ cause])
	                                                                                     
fun forget_mt r (skctxn as (sctxn, kctxn)) (sctxl, kctxl) t = 
    let val t = forget_t_mt 0 kctxl t
		handle ForgetError (x, cause) => raise Error (r, escapes "type variable" (str_v kctxn x) "type" (str_mt skctxn t) cause)
	val t = forget_i_mt 0 sctxl t
		handle ForgetError (x, cause) => raise Error (r, escapes "index variable" (str_v sctxn x) "type" (str_mt skctxn t) cause)
    in
      t
    end

fun forget_ctx_mt r (sctx, kctx, _, _) (sctxd, kctxd, _, _) t =
    let val (sctxn, kctxn) = (sctx_names sctx, names kctx)
        val sctxl = sctx_length sctxd
    in
      forget_mt r (sctxn, kctxn) (sctxl, length kctxd) t
    end
      
fun forget_t r (skctxn as (sctxn, kctxn)) (sctxl, kctxl) t = 
    let val t = forget_t_t 0 kctxl t
		handle ForgetError (x, cause) => raise Error (r, escapes "type variable" (str_v kctxn x) "type" (str_t skctxn t) cause)
	val t = forget_i_t 0 sctxl t
		handle ForgetError (x, cause) => raise Error (r, escapes "index variable" (str_v sctxn x) "type" (str_t skctxn t) cause)
    in
      t
    end

fun forget_ctx_t r (sctx, kctx, _, _) (sctxd, kctxd, _, _) t =
    let val (sctxn, kctxn) = (sctx_names sctx, names kctx)
        val sctxl = sctx_length sctxd
    in
      forget_t r (sctxn, kctxn) (sctxl, length kctxd) t
    end
      
fun forget_d r sctxn sctxl d =
    forget_i_i 0 sctxl d
    handle ForgetError (x, cause) => raise Error (r, escapes "index variable" (str_v sctxn x) "time" (str_i sctxn d) cause)

fun forget_ctx_d r (sctx, _, _, _) (sctxd, _, _, _) d =
    let val sctxn = sctx_names sctx
        val sctxl = sctx_length sctxd
    in
      forget_d r sctxn sctxl d
    end

fun mismatch (ctx as (sctx, kctx, _, _)) e expect got =  
    (get_region_e e,
     "Type mismatch:" ::
     indent ["expect: " ^ expect, 
             "got: " ^ str_t (sctx, kctx) got,
             "in: " ^ str_e ctx e])

fun mismatch_anno ctx expect got =  
    (get_region_t got,
     "Type annotation mismatch:" ::
     indent ["expect: " ^ expect,
             "got: " ^ str_t ctx got])

fun is_wf_return (skctx as (sctx, _), return) =
    case return of
        (SOME t, SOME d) =>
	(SOME (is_wf_mtype (skctx, t)),
	 SOME (check_bsort (sctx, d, Base Time)))
      | (SOME t, NONE) =>
	(SOME (is_wf_mtype (skctx, t)),
         NONE)
      | (NONE, SOME d) =>
	(NONE,
         SOME (check_bsort (sctx, d, Base Time)))
      | (NONE, NONE) => (NONE, NONE)

fun do_fetch_type (tctx, (x, r)) =
    case lookup_type x tctx of
      	SOME t => t
      | NONE => raise Error (r, ["Unbound variable: " ^ str_v (names tctx) x])

val fetch_type = generic_fetch shiftx_m_t do_fetch_type #4

(* t is already checked for wellformedness *)
fun match_ptrn (ctx as (sctx : scontext, kctx : kcontext, cctx : ccontext), (* pcovers, *) pn : U.ptrn, t : mtype) : ptrn * cover * context * int =
    let 
      val skctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
      val t = update_mt t
    in
      case pn of
	  U.ConstrP (((cx, cr), eia), inames, opn, r) =>
          (case t of
               AppV ((family, _), ts, is, _) =>
 	       let 
                 val (_, c as (family', tnames, ibinds)) = fetch_constr (cctx, (cx, cr))
                 val (name_sorts, (t1, is')) = unfold_ibinds ibinds
                 val () = if eia then () else raise Impossible "eia shouldn't be false"
		 val () =
                     if family' = family andalso length tnames = length ts andalso length is' = length is then ()
                     else raise Error 
                                (r, sprintf "Type of constructor $ doesn't match datatype " [str_v (names cctx) cx] :: 
                                    indent ["expect: " ^ str_v kctxn family, 
                                            "got: " ^ str_v kctxn family'])
                 val () =
                     if length inames = length name_sorts then ()
                     else raise Error (r, [sprintf "This constructor requires $ index argument(s), not $" [str_int (length name_sorts), str_int (length inames)]])
		 val t1 = subst_ts_mt ts t1
		 val is = map (shiftx_i_i 0 (length name_sorts)) is
		 val ps = ListPair.map (fn (a, b) => BinPred (EqP, a, b)) (is', is)
                 val ctxd = ctx_from_full_sortings o rev o ListPair.zip $ (inames, snd (ListPair.unzip name_sorts))
                 val () = open_ctx ctxd
                 val () = open_premises ps
                 val ctx = add_ctx_skc ctxd ctx
                 val pn1 = default (U.TTP dummy) opn
                 val (pn1, cover, ctxd', nps) = match_ptrn (ctx, pn1, t1)
                 val ctxd = add_ctx ctxd' ctxd
                 val cover = ConstrC (cx, cover)
               in
		 (ConstrP (((cx, cr), eia), inames, SOME pn1, r), cover, ctxd, length ps + nps)
	       end
             | _ => raise Error (r, [sprintf "Pattern $ doesn't match type $" [U.str_pn (sctx_names sctx, names kctx, names cctx) pn, str_mt skctxn t]])
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
            val t1 = fresh_mt (kctxn @ sctxn) r
            val t2 = fresh_mt (kctxn @ sctxn) r
            (* val () = println $ sprintf "before: $ : $" [U.str_pn (sctxn, kctxn, names cctx) pn, str_mt skctxn t] *)
            val () = unify r skctxn (t, Prod (t1, t2))
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
            val () = unify r skctxn (t, Unit dummy)
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
            val t' = is_wf_mtype ((sctx, kctx), t')
            val () = unify (U.get_region_pn pn) skctxn (t, t')
            val (pn1, cover, ctxd, nps) = match_ptrn (ctx, pn1, t')
          in
            (AnnoP (pn1, t'), cover, ctxd, nps)
          end
    end

fun get_mtype (* ggctx *) (ctx as (sctx : scontext, kctx : kcontext, cctx : ccontext, tctx : tcontext), e_all : U.expr) : expr * mtype * idx =
    let
      (* val get_mtype = get_mtype ggctx *)
      val skctx = (sctx, kctx) 
      val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
      val skctxn = (sctxn, kctxn)
      (* val () = print (sprintf "Typing $\n" [U.str_e ((* upd4 (const [])  *)ctxn) e_all]) *)
      fun print_ctx (ctx as (sctx, kctx, _, tctx)) = app (fn (nm, t) => println $ sprintf "$: $" [nm, str_t (sctx_names sctx, names kctx) t]) tctx
      fun main () =
	  case e_all of
	      U.Var (info as ((x, r), is_explicit_idx_args)) =>
              let
                fun insert_type_args t =
                    case t of
                        Mono t => t
                      | Uni (_, t, _) =>
                        let
                          (* val t_arg = fresh_mt (kctxn @ sctxn) r *)
                          (* val () = println $ str_mt skctxn t_arg *)
                          val t_arg = U.UVar ((), r)
                          val t_arg = is_wf_mtype (skctx, t_arg)
                          val t = subst_t_t t_arg t
                          (* val () = println $ str_t skctxn t *)
                          val t = insert_type_args t
                        in
                          t
                        end
                val t = fetch_type (* ggctx  *)(tctx, (x, r))
                (* val () = println $ str_t skctxn t *)
                val t = insert_type_args t
                (* val () = println $ str_mt skctxn t *)
                fun insert_idx_args t_all =
                    case t_all of
                        UniI (s, Bind ((name, _), t), _) =>
                        let
                          (* val bs = fresh_bsort () *)
                          (* val i = fresh_i sctxn bs r *)
                          (* val bs =  get_base r sctxn s *)
                          val i = U.UVarI ((), r)
                          val i = check_sort (sctx, i, s)
                          val t = subst_i_mt i t
                                  handle
                                  SubstUVar info =>
                                  raise subst_uvar_error (U.get_region_e e_all) ("type " ^ str_mt skctxn t_all) i info
                        in
                          insert_idx_args t
                        end
                      | _ => t_all
                val t = if not is_explicit_idx_args then
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
                val d = fresh_i sctxn (Base Time) r
                val t = fresh_mt (kctxn @ sctxn) r
                val (e1, _, d1) = check_mtype (ctx, e1, Arrow (t2, d, t)) 
              in
                (App (e1, e2), t, d1 %+ d2 %+ T1 dummy %+ d) 
	      end
	    | U.Abs (pn, e) => 
	      let
                val r = U.get_region_pn pn
                val t = fresh_mt (kctxn @ sctxn) r
                val skcctx = (sctx, kctx, cctx) 
                val (pn, cover, ctxd, nps (* number of premises *)) = match_ptrn (skcctx, pn, t)
	        val () = check_exhaustion (skcctx, t, [cover], get_region_pn pn)
                val ctx = add_ctx ctxd ctx
		val (e, t1, d) = get_mtype (ctx, e)
		val t1 = forget_ctx_mt (get_region_e e) ctx ctxd t1 
                val d = forget_ctx_d (get_region_e e) ctx ctxd d
                val () = close_vcs nps
                val () = close_ctx ctxd
              in
		(Abs (pn, e), Arrow (t, d, t1), T0 dummy)
	      end
	    | U.Let (return, decls, e, r) => 
	      let
                val return = is_wf_return (skctx, return)
                val (decls, ctxd as (sctxd, kctxd, _, _), nps, ds, ctx) = check_decls (ctx, decls)
		val (e, t, d) = get_mtype (ctx, e)
                val ds = rev (d :: ds)
                val d = combine_AddI_Time ds
                (* val d = foldl' (fn (d, acc) => acc %+ d) (T0 dummy) ds *)
		(* val t = forget_ctx_mt r ctx ctxd t  *)
                (* val ds = map (forget_ctx_d r ctx ctxd) ds *)
	        val (t, d) = forget_or_check_return (get_region_e e) ctx ctxd (t, d) return 
                val () = close_vcs nps
                val () = close_ctx ctxd
              in
		(Let (return, decls, e, r), t, d)
	      end
	    | U.AbsI (s, (name, r), e, r_all) => 
	      let 
		val () = if U.is_value e then ()
		         else raise Error (U.get_region_e e, ["The body of a universal abstraction must be a value"])
                val s = is_wf_sort (sctx, s)
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
                val s = fresh_sort sctxn r
                val t1 = fresh_mt (kctxn @ sctxn) r
                val (e, t, d) = check_mtype (ctx, e, UniI (s, Bind (("_", r), t1), r)) 
                val i = check_sort (sctx, i, s) 
              in
		(AppI (e, i), subst_i_mt i t1, d)
                handle SubstUVar info =>
                       raise subst_uvar_error (U.get_region_e e_all) ("type " ^ str_mt skctxn t) i info
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
                val t1 = fresh_mt (kctxn @ sctxn) r
                val t2 = fresh_mt (kctxn @ sctxn) r
                val (e, _, d) = check_mtype (ctx, e, Prod (t1, t2)) 
              in 
                (Fst e, t1, d)
	      end
	    | U.Snd e => 
	      let 
                val r = U.get_region_e e
                val t1 = fresh_mt (kctxn @ sctxn) r
                val t2 = fresh_mt (kctxn @ sctxn) r
                val (e, _, d) = check_mtype (ctx, e, Prod (t1, t2)) 
              in 
                (Snd e, t2, d)
	      end
	    | U.Ascription (e, t) => 
	      let val t = is_wf_mtype (skctx, t)
		  val (e, _, d) = check_mtype (ctx, e, t)
              in
		(Ascription (e, t), t, d)
	      end
	    | U.AscriptionTime (e, d) => 
	      let val d = check_bsort (sctx, d, Base Time)
		  val (e, t) = check_time (ctx, e, d)
              in
		(AscriptionTime (e, d), t, d)
	      end
	    | U.BinOp (Add, e1, e2) =>
	      let val (e1, _, d1) = check_mtype (ctx, e1, BaseType (Int, dummy))
		  val (e2, _, d2) = check_mtype (ctx, e2, BaseType (Int, dummy)) in
		(BinOp (Add, e1, e2), BaseType (Int, dummy), d1 %+ d2 %+ T1 dummy)
	      end
	    | U.ConstInt n => 
	      (ConstInt n, BaseType (Int, dummy), T0 dummy)
	    | U.AppConstr ((cx as (_, rc), eia), is, e) => 
	      let 
                val (cname, tc) = fetch_constr_type (cctx, cx)
		(* delegate to checking [cx {is} e] *)
		val f = U.Var ((0, rc), eia)
		val f = foldl (fn (i, e) => U.AppI (e, i)) f is
		val e = U.App (f, U.Subst.shift_e_e e)
		val (e, t, d) = get_mtype (add_typing_skct (cname, tc) ctx, e) 
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
                val e = AppConstr ((cx, eia), is, e)
	      in
		(e, t, d)
	      end
	    | U.Case (e, return, rules, r) => 
	      let val (e, t1, d1) = get_mtype (ctx, e)
                  val return = is_wf_return (skctx, return)
                  val rules = expand_rules ((sctx, kctx, cctx), rules, t1, r)
                  val (rules, tds) = check_rules (ctx, rules, (t1, return), r)
                  fun computed_t () : mtype =
                      case map fst tds of
                          [] => raise Error (r, ["Empty case-matching must have a return type clause"])
                        | t :: ts => 
                          (map (fn t' => unify r skctxn (t, t')) ts; 
                           t)
                  fun computed_d () =
                      (smart_max_list o map snd) tds
                  val (t, d) = mapPair (lazy_default computed_t, lazy_default computed_d) return
              in
		(Case (e, return, rules, r), t, d1 %+ d)
              end
	    | U.Never (t, r) => 
              let
		val t = is_wf_mtype (skctx, t)
		val () = write_prop (False dummy, U.get_region_e e_all)
              in
		(Never (t, r), t, T0 r)
              end
      val (e, t, d) = main ()
                      handle
                      Error (r, msg) => raise Error (r, msg @ ["when type-checking"] @ indent [U.str_e ctxn e_all])
                                              (* val () = println $ str_ls id $ #4 ctxn *)
	                                      (* val () = print (sprintf "  Typed : $: \n          $\n" [str_e ((* upd4 (const [])  *)ctxn) e, str_mt skctxn t]) *)
	                                      (* val () = print (sprintf "   Time : $: \n" [str_i sctxn d]) *)
	                                      (* val () = print (sprintf "  type: $ [for $]\n  time: $\n" [str_mt skctxn t, str_e ctxn e, str_i sctxn d]) *)
    in
      (e, t, d)
    end

and check_decls (ctx, decls) : decl list * context * int * idx list * context = 
    let 
      fun f (decl, (decls, ctxd, nps, ds, ctx)) =
          let 
            val (decl, ctxd', nps', ds') = check_decl (ctx, decl)
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
    in
      (decls, ctxd, nps, ds, ctx)
    end

and check_decl (ctx as (sctx, kctx, cctx, _), decl) =
    let
      fun fv_mt t =
	  case hnf_mt t of
              UVar ((_, uvar_ref), _) => [uvar_ref]
            | Unit _ => []
	    | Arrow (t1, _, t2) => fv_mt t1 @ fv_mt t2
	    | Prod (t1, t2) => fv_mt t1 @ fv_mt t2
	    | UniI (s, Bind (name, t1), _) => fv_mt t1
	    | BaseType _ => []
	    | AppV (y, ts, is, r) => concatMap fv_mt ts
      fun fv_t t =
          case t of
              Mono t => fv_mt t
            | Uni _ => [] (* fresh uvars in Uni should either have been generalized or in previous ctx *)
      fun generalize t = 
          let
            fun fv_ctx (_, _, _, tctx) = (concatMap fv_t o map snd) tctx (* cctx can't contain uvars *)
            fun substu x v (b : mtype) : mtype =
	        case b of
                    UVar ((_, y), _) =>
                    if y = x then
                      AppV ((v, dummy), [], [], dummy)
                    else 
                      b
                  | Unit r => Unit r
	          | Arrow (t1, d, t2) => Arrow (substu x v t1, d, substu x v t2)
	          | Prod (t1, t2) => Prod (substu x v t1, substu x v t2)
	          | UniI (s, Bind (name, t1), r) => UniI (s, Bind (name, substu x v t1), r)
	          | BaseType a => BaseType a
	          | AppV (y, ts, is, r) => 
		    AppV (y, map (substu x v) ts, is, r)
            fun evar_name n =
                if n < 26 then
                  "'_" ^ (str o chr) (ord #"a" + n)
                else
                  "'_" ^ str_int n
            val fv = dedup op= $ diff op= (fv_mt t) (fv_ctx ctx)
            val t = shiftx_t_mt 0 (length fv) t
            val (t, _) = foldl (fn (uvar_ref, (t, v)) => (substu uvar_ref v t, v + 1)) (t, 0) fv
            val t = Range.for (fn (i, t) => (Uni ((evar_name i, dummy), t, dummy))) (Mono t) (0, (length fv))
          in
            t
          end
      (* val () = println $ sprintf "Typing $" [fst $ U.str_decl (ctx_names ctx) decl] *)
      fun main () = 
          case decl of
              U.Val (tnames, U.VarP (x, r1), e, r) =>
              let 
                val (e, t, d) = get_mtype (add_kindings_skct (zip ((rev o map fst) tnames, repeat (length tnames) Type)) ctx, e)
                val t = if is_value e then 
                          let
                            val t = generalize t
                            val t = foldr (fn (nm, t) => Uni (nm, t, r)) t tnames
                          in
                            t
                          end
                        else if length tnames = 0 then
                          Mono t
                        else
                          raise Error (r, ["explicit type variable cannot be generalized because of value restriction"])
              in
                (Val (tnames, VarP (x, r1), e, r), ctx_from_typing (x, t), 0, [d])
              end
            | U.Val (tnames, pn, e, r) =>
              let 
                val () = if length tnames = 0 then ()
                         else raise Error (r, ["compound pattern can't be generalized, so can't have explicit type variables"])
                val skcctx = (sctx, kctx, cctx) 
                val (e, t, d) = get_mtype (ctx, e)
                val (pn, cover, ctxd, nps) = match_ptrn (skcctx, pn, t)
                val d = shift_ctx_i ctxd d
	        val () = check_exhaustion (skcctx, t, [cover], get_region_pn pn)
              in
                (Val (tnames, pn, e, r), ctxd, nps, [d])
              end
	    | U.Rec (tnames, (name, r1), (binds, ((t, d), e)), r) => 
	      let 
                val ctx = add_kindings_skct (zip ((rev o map fst) tnames, repeat (length tnames) Type)) ctx
                fun f (bind, (binds, ctxd, nps)) =
                    case bind of
                        U.SortingST (name, s) => 
                        let 
                          val ctx = add_ctx ctxd ctx
                          val s = is_wf_sort (#1 ctx, s)
                          val ctxd' = ctx_from_sorting (fst name, s)
                          val () = open_ctx ctxd'
                          val ctxd = add_ctx ctxd' ctxd
                        in
                          (inl (name, s) :: binds, ctxd, nps)
                        end
                      | U.TypingST pn =>
                        let
                          val ctx as (sctx, kctx, _, _) = add_ctx ctxd ctx
                          val r = U.get_region_pn pn
                          val t = fresh_mt (names kctx @ names sctx) r
                          val skcctx = (sctx, kctx, cctx) 
                          val (pn, cover, ctxd', nps') = match_ptrn (skcctx, pn, t)
	                  val () = check_exhaustion (skcctx, t, [cover], get_region_pn pn)
                          val ctxd = add_ctx ctxd' ctxd
                          val nps = nps' + nps
                        in
                          (inr (pn, t) :: binds, ctxd, nps)
                        end
                val (binds, ctxd, nps) = foldl f ([], empty_ctx, 0) binds
                val binds = rev binds
                val (sctx, kctx, _, _) = add_ctx ctxd ctx
	        val t = is_wf_mtype ((sctx, kctx), t)
	        val d = check_bsort (sctx, d, Base Time)
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
                val () = close_vcs nps
                val () = close_ctx ctxd
                val te = generalize te
                val te = foldr (fn (nm, t) => Uni (nm, t, r)) te tnames
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
                val (a, ctxd) = is_wf_datatype ctx a
              in
                (Datatype a, ctxd, 0, [])
              end
            | U.IdxDef ((name, r), s, i) =>
              let
                val s = is_wf_sort (sctx, s)
                val i = check_sort (sctx, i, s)
                val ctxd = ctx_from_sorting (name, s)
                val () = open_ctx ctxd
                val ps = [BinPred (EqP, VarI (0, r), shift_ctx_i ctxd i)]
                val () = open_premises ps
              in
                (IdxDef ((name, r), s, i), ctxd, length ps, [])
              end
            | U.AbsIdx (((name, r1), s, i), decls, r) =>
              let
                val s = is_wf_sort (sctx, s)
                (* localized the scope of the evars introduced in type-checking absidx's definition *)
                val () = open_vc ()
                val i = check_sort (sctx, i, s)
                val ctxd = ctx_from_sorting (name, s)
                val () = open_ctx ctxd
                val ps = [BinPred (EqP, VarI (0, r), shift_ctx_i ctxd i)]
                val () = open_premises ps
                val (decls, ctxd2, nps, ds, _) = check_decls (add_ctx ctxd ctx, decls)
                val () = if nps = 0 then ()
                         else raise Error (r, ["Can't have premise-generating pattern in abstype"])
                (* close and reopen *)
                val () = close_ctx ctxd2
                val () = close_vcs (length ps)
                val () = close_ctx ctxd
                val () = close_vc ()
                val ctxd = add_ctx ctxd2 ctxd
                val () = open_ctx ctxd
              in
                (AbsIdx (((name, r1), s, i), decls, r), ctxd, 0, ds)
              end
      val ret as (decl, ctxd, nps, ds) =
          main ()
          handle
          Error (r, msg) => raise Error (r, msg @ ["when type-checking declaration "] @ indent [fst $ U.str_decl (ctx_names ctx) decl])
	                          (* val () = println $ sprintf "  Typed : $ " [fst $ str_decl (ctx_names ctx) decl] *)
	                          (* val () = print $ sprintf "   Time : $: \n" [str_i sctxn d] *)
    in
      ret
    end

and is_wf_datatype ctx (name, tnames, sorts, constr_decls, r) =
    let 
      val sorts = is_wf_sorts (sctx, sorts)
      val nk = (name, ArrowK (true, length tnames, sorts))
      val ctx as (sctx, kctx, _, _) = add_kinding_skct nk ctx
      fun make_constr ((name, ibinds, r) : U.constr_decl) =
	  let 
            val c = (0, tnames, ibinds)
	    val t = U.constr_type U.VarT shiftx_v c
	    val t = is_wf_type ((sctx, kctx), t)
		    handle Error (_, msg) =>
			   raise Error (r, 
					"Constructor is ill-formed" :: 
					"Cause:" :: 
					indent msg)
            val () = if length (fv_t t) > 0 then
                       raise Error (r, ["Constructor has unresolved unification type variable(s)"])
                     else ()
            val (_, ibinds) = constr_from_type t
	  in
	    ((name, ibinds, r), (name, (0, tnames, ibinds)))
	  end
      val (constr_decls, constrs) = (unzip o map make_constr) constr_decls
    in
      ((name, tnames, sorts, constr_decls, r), ([], [nk], rev constrs, []))
    end
      
and expand_rules (ctx as (sctx, kctx, cctx), rules, t, r) =
    let
      fun expand_rule (rule as (pn, e), (pcovers, rules)) =
          let
	    val (pn, cover, ctxd, nps) = match_ptrn (ctx, (* pcovers, *) pn, t)
            val () = close_vcs nps
            val () = close_ctx ctxd
            (* val cover = ptrn_to_cover pn *)
            (* val () = println "before check_redundancy()" *)
            val () = check_redundancy (ctx, t, pcovers, cover, get_region_pn pn)
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
                                  (* val t = update_mt t *)
                                  val t = hnf_mt t
                                in
                                  case (hab, t) of
                                      (ConstrH (x, h'), AppV ((family, _), ts, _, _)) =>
                                      let
                                        val (_, (_, _, ibinds)) = fetch_constr (cctx, (x, dummy))
                                        val (name_sorts, (t', _)) = unfold_ibinds ibinds
	                                val t' = subst_ts_mt ts t'
                                        (* cut-off so that [expand_rules] won't try deeper and deeper proposals *) 
                                        val pn' =
                                            loop (* (cutoff - 1) *) t' h'
                                                                    (* if cutoff > 0 then *)
                                                                    (*   loop (cutoff - 1) t' h' *)
                                                                    (* else *)
                                                                    (*   VarP ("_", dummy) *)
                                      in
                                        ConstrP (((x, dummy), true), repeat (length name_sorts) "_", SOME pn', dummy)
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
                                ConstrP (((x, _), _), _, pn, _) => ConstrC (x, default TrueC $ Option.map ptrn_to_cover pn)
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
                          case any_missing false(*treat empty datatype as inhabited, so as to get a shorter proposal*) ctx t $ combine_covers pcovers of
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
      val () = check_exhaustion (ctx, t, pcovers, r);
    in
      rules
    end

and check_rules (ctx as (sctx, kctx, cctx, tctx), rules, t as (t1, return), r) =
    let 
      val skcctx = (sctx, kctx, cctx) 
      fun f (rule, acc) =
	  let
            (* val previous_covers = map (snd o snd) $ rev acc *)
            val ans as (rule, (td, cover)) = check_rule (ctx, (* previous_covers, *) rule, t)
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

and check_rule (ctx as (sctx, kctx, cctx, tctx), (* pcovers, *) (pn, e), t as (t1, return)) =
    let 
      val skcctx = (sctx, kctx, cctx) 
      val (pn, cover, ctxd as (sctxd, kctxd, _, _), nps) = match_ptrn (skcctx, (* pcovers, *) pn, t1)
      val ctx0 = ctx
      val ctx = add_ctx ctxd ctx
      val (e, t, d) = get_mtype (ctx, e)
      val (t, d) = forget_or_check_return (get_region_e e) ctx ctxd (t, d) return 
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
      val () = close_vcs nps
      val () = close_ctx ctxd
    in
      ((pn, e), ((t, d), cover))
    end

and forget_or_check_return r ctx ctxd (t', d') (t, d) =
    let
      val (sctxn, kctxn, _, _) = ctx_names ctx
      val t =
          case t of
              SOME t =>
              let
                val () = unify r (sctxn, kctxn) (t', shift_ctx_mt ctxd t)
              in
                t
              end
            | NONE =>
              let
	        val t' = forget_ctx_mt r ctx ctxd t' 
              in
                t'
              end
      val d = 
          case d of
              SOME d =>
              let
                val () = smart_write_le sctxn (d', shift_ctx_i ctxd d, r)
              in
                d
              end
            | NONE =>
              let 
	        val d' = forget_ctx_d r ctx ctxd d'
              in
                d'
              end
    in
      (t, d)
    end

and check_mtype (ctx as (sctx, kctx, cctx, tctx), e, t) =
    let 
      val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
      val (e, t', d) = get_mtype (ctx, e)
      val () = unify (get_region_e e) (sctxn, kctxn) (t', t)
                     (* val () = println "check type" *)
                     (* val () = println $ str_region "" "ilist.timl" $ get_region_e e *)
    in
      (e, t', d)
    end

and smart_write_le ctx (i1, i2, r) =
    let
      (* val () = println $ sprintf "Check Le : $ <= $" [str_i ctx i1, str_i ctx i2] *)
      fun is_fresh_i i =
          case i of
              UVarI ((_, x), _) =>
              (case !x of
                   Fresh _ => true
                 | Refined _ => false
              )
            | _ => false
    in
      if is_fresh_i i1 orelse is_fresh_i i2 then unify_i r ctx (i1, i2)
      else write_le (i1, i2, r)
    end
      
and check_time (ctx as (sctx, kctx, cctx, tctx), e, d) : expr * mtype =
    let 
      val (e, t, d') = get_mtype (ctx, e)
      val () = smart_write_le (names sctx) (d', d, get_region_e e)
    in
      (e, t)
    end

and check_mtype_time (ctx as (sctx, kctx, cctx, tctx), e, t, d) =
    let 
      val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
      (* val () = print (sprintf "Type checking $ against $ and $\n" [U.str_e ctxn e, str_mt (sctxn, kctxn) t, str_i sctxn d]) *)
      val (e, _, d') = check_mtype (ctx, e, t)
      (* val () = println "check type & time" *)
      (* val () = println $ str_region "" "ilist.timl" $ get_region_e e *)
      val () = smart_write_le (names sctx) (d', d, get_region_e e)
    in
      e
    end

fun link_sig (* sigs  *)gctx_base ((* gctx,  *)ctx as (sctx, kctx, cctx, tctx)) ((* gctx',  *)ctx' as (sctx', kctx', cctx', tctx')) =
    let
      (* val len_gctx = length gctx *)
      (* val len_gctx' = length gctx' *)
      (* val gctx' = shiftx_m_gctx 0 len_gctx gctx' *)
      (* fun match_sig ((name, sg'), (gctx_base, gctx'), n) = *)
      (*     let *)
      (*       val sg = fetch_sig_by_name gctx name *)
      (*       val sg = shiftx_m_sig 0 n sg *)
      (*       val sg' = link_sig_pack (* sigs *) gctx_base sg sg' *)
      (*     in *)
      (*       (sg' :: gctx_base, sg' :: gctx') *)
      (*     end *)
      (* val (gctx_base, gctx') = foldlWithIdx match_sig (gctx @ gctx_base, gctx) gctx' *)
      (* val ctx = shiftx_m_ctx 0 len_gctx' ctx *)
      (* val ctx' = shiftx_m_ctx len_gctx' len_gctx ctx' *)
      val len_sctx = length sctx
      val len_sctx' = length sctx'
      (* val sctx' = shiftx_i_sctx 0 (len_sctx) sctx' *)
      val () = open_sortings sctx
      fun match_sort ((name, s'), sctx', n) =
          let
            val (s, x) = fetch_sort_by_name sctx name
            val s = shfitx_i_s 0 n s
            val x = x + n
            val () = unify_s s s'
            val r = get_region_s s
            fun sort_add_idx_eq s' i =
                add_prop s' (VarI (0, r) %= shift_i_i i)
            val s' = sort_add_idx_eq s' (VarI (x, r))
            val sctx' = add_sorting (name, s') sctx'
            val () = open_sorting (name, s')
          in
            sctx'
          end
      val sctx' = foldlWithIdx match_sort sctx sctx'
      val len_kctx = length kctx
      val len_kctx' = length kctx'
      val kctx = shiftx_i_kctx 0 len_sctx' kctx
      (* val kctx' = shiftx_t_kctx 0 len_kctx kctx' *)
      fun match_kind ((name, k'), kctx', n) =
          let
            val (k, x) = fetch_kind_by_name kctx name
            val k = shfitx_t_k 0 n k
            val x = x + n
            val () = unify_kind (* sigs *) gctx_base (sctx', kctx') k k'
            val r = get_region_k k
            val k' = kind_add_type_eq k' (MtVar (x, r))
          in
            add_kinding (name, k') kctx'
          end
      val kctx' = foldlWithIdx match_kind kctx kctx'
      val cctx = shiftx_i_cctx 0 len_sctx' cctx
      val cctx = shiftx_t_cctx 0 len_kctx' cctx
      fun match_constr_type ((name, t'), n) =
          let
            val (t, x) = fetch_constr_type_by_name cctx name
          in
            unify_t (* sigs *) gctx_base (sctx', kctx') t t'
          end
      val () = appWithIdx match_type cctx'
      val tctx = shiftx_i_tctx 0 len_sctx' tctx
      val tctx = shiftx_t_tctx 0 len_kctx' tctx
      fun match_type ((name, t'), n) =
          let
            val (t, x) = fetch_type_by_name tctx name
          in
            unify_t (* sigs *) gctx_base (sctx', kctx') t t'
          end
      val () = appWithIdx match_type tctx'
    in
      ((* gctx',  *)(sctx', kctx', cctx', tctx'))
    end

(* and link_sig_pack (* sigs *) gctx_base sg sg' = *)
(*     case (sg, sg') of *)
(*         (Sig sg, Sig sg') => Sig $ link_sig (* sigs *) gctx_base sg sg' *)
(*       | _ => raise Impossible "link_sig_pack (): only Sig should appear here" *)

fun is_sub_sig gctx ctx ctx' =
    let
      val _ = link_sig gctx ctx ctx'
      val () = close_premises (length (#1 ctx) + length (#1 ctx'))
    in
      ()
    end
                   
fun is_wf_sig gctx sg =
    case sg of
        U.SigComponents (comps, r) =>
        let
          fun is_wf_spec ctx spec =
              case spec of
                  U.SpecVal ((name, r), t) =>
                  let
                    val t = is_wf_type (#1 ctx, #2 ctx) t
                  in
                    (SpecVal ((name, r), t), add_typing (name, t) ctx)
                  end
                | U.SpecIdx ((name, r), s) =>
                  let
                    val s = is_wf_sort (#1 ctx) s
                  in
                    (SpecIdx ((name, r), s), add_sorting (name, s) ctx)
                  end
                | U.SpecType ((name, r), k) =>
                  let
                    val k = is_wf_kind (#1 ctx, #2 ctx) k
                  in
                    (U.SpecType ((name, r), k), add_kinding (name, k) ctx)
                  end
                | U.SpecTypeDef ((name, r), t) =>
                  let
                    val t = is_wf_type (#1 ctx, #2 ctx) t
                  in
                    (SpecTypeDef ((name, r), t), add_type_eq (name, t) ctx)
                  end
                | U.SpecDatatype a =>
                  let
                    val (a, ctxd) = is_wf_datatype ctx a
                  in
                    (SpecDatatype a, add_ctx ctxd ctx)
                  end
          fun iter (spec, (specs, ctx)) =
              let
                val (spec, ctx) = is_wf_spec ctx spec
              in
                (spec :: specs, ctx)
              end
          val ctxd = snd $ foldl iter ([], []) comps
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
          
fun get_sig gctx m =
    case m of
        U.ModComponents (comps, r) =>
        let
          val (_, ctxd, nps, ds, _) = check_decls ([], comps)
          val () = close_vcs nps
          val () = close_ctx ctxd
        in
          ctxd
        end
      | U.ModSeal (m, sg) =>
        let
          val sg = is_wf_sig gctx sg
          val sg' = get_sig gctx m
          val () = is_sub_sig gctx sg' sg
        in
          sg
        end
      | U.ModTransparentAscription (m, sg) =>
        let
          val sg = is_wf_sig gctx sg
          val sg' = get_sig gctx m
          val () = is_sub_sig gctx sg' sg
        in
          sg'
        end

fun check_top_bind gctx bind = 
    case bind of
        TopModBind ((name, _), m) =>
        let
          val sg = get_sig gctx m
          val () = open_module sg
        in
          [(name, Sig sg)]
        end
      | TopModSpec ((name, _), sg) =>
        let
          val sg = is_wf_sig gctx sg
          val () = open_module sg
        in
          [(name, Sig sg)]
        end
      (* | TopBindSig ((name, _), sg) => *)
      (*   let *)
      (*     val sg = is_wf_sig gctx sg *)
      (*   in *)
      (*     (name, SigBind sg) *)
      (*   end *)
      | TopFunctorBind ((name, _), args, m) =>
        (* functor applications will be implemented fiberedly instead of parametrizedly *)
        let
          val (args, gctx') = check_top_binds gctx $ map TopModSpec [args]
          val sg = get_sig gctx' m
          val () = close_premises $ length args
        in
          [(name, FactorBind (args, sg))]
        end
      | U.TopFunctorApp ((name, _), f, m) =>
        let
          val (arg, body) = fetch_functor gctx f
          val sg = get_sig gctx m
          val arg = link_sig gctx sg arg
          val gctxd = [("__actual_mod_arg", Sig sg), ("__formal_mod_arg", Sig arg)]
          val gctx = gctxd @ gctx
          val body = shiftx_m_m 1 1 body
          val body_sig = get_sig gctx body
        in
          (name, Sig body_sig) :: gctxd
        end
          
fun check_top_binds gctx binds =
    let
      fun iter (bind, (acc, gctx)) =
          let
            val sgs = check_top_bind gctx bind
          in
            (sgs @ acc, sgs @ gctx)
          end
    in
      foldl iter ([], gctx) binds
    end

end
