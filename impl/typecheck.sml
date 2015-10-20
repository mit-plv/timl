structure TypeCheck = struct
open ExprRegion
open Region
open Expr
open VC

infixr 0 $

infix 6 %+
infix 6 %*
infix 4 %<=
infix 3 /\
infix 1 -->
infix 1 <->

fun is_value (e : expr) : bool =
    case e of
        Var _ => true
      | App _ => false
      | Abs _ => true
      | TT _ => true
      | Pair (e1, e2) => is_value e1 andalso is_value e2
      | Fst _ => false
      | Snd _ => false
      | Inl (_, e) => is_value e
      | Inr (_, e) => is_value e
      | SumCase _ => false
      | Fold (_, e) => is_value e
      | Unfold _ => false
      | AbsT _ => true
      | AppT _ => true
      | AbsI _ => true
      | AppI _ => false
      | Pack (_, _, e) => is_value e
      | Unpack _ => false
      | Fix _ => false
      | Let _ => false
      | Ascription _ => false
      | AscriptionTime _ => false
      | BinOp _ => false
      | Const _ => true
      | AppConstr (_, _, _, e) => is_value e
      | Case _ => false
      | Never _ => false

fun is_fixpoint e =
    case e of
        Fix _ => true
      | _ => false

open Subst

(* sorting context *)
type scontext = (string * sort) list * prop list
(* kinding context *)
type kcontext = (string * kind) list 
(* constructor context *)
type ccontext = (string * constr) list
(* typing context *)
type tcontext = (string * ty) list
type context = scontext * kcontext * ccontext * tcontext

fun names (ctx : ('a * 'b) list) = map #1 ctx

fun shiftx_i_ps n ps = 
    map (shiftx_i_p 0 n) ps
fun shiftx_i_ks n ctx = 
    map (mapSnd (shiftx_i_k 0 n)) ctx
fun shiftx_i_cs n ctx = 
    map (mapSnd (shiftx_i_c 0 n)) ctx
fun shiftx_t_cs n ctx = 
    map (mapSnd (shiftx_t_c 0 n)) ctx
fun shiftx_i_ts n ctx = 
    map (mapSnd (shiftx_i_t 0 n)) ctx
fun shiftx_t_ts n ctx = 
    map (mapSnd (shiftx_t_t 0 n)) ctx

fun add_sorting pair (pairs, ps) = (pair :: pairs, shiftx_i_ps 1 ps)
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
fun add_sortings_skct (pairs', ps') ((pairs, ps), kctx, cctx, tctx) : context = 
    let val n = length pairs' 
    in
        ((pairs' @ pairs, ps' @ shiftx_i_ps n ps), 
         shiftx_i_ks n kctx, 
         shiftx_i_cs n cctx, 
         shiftx_i_ts n tctx)
    end
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

fun sctx_length (pairs, _) = length pairs
fun sctx_names ((pairs, _) : scontext) = map #1 pairs

fun lookup_sort (n : int) (pairs, _) : sort option = 
    case nth_error pairs n of
        NONE => NONE
      | SOME (_, s) => 
        SOME (shiftx_i_s 0 (n + 1) s)

fun add_kinding pair (kctx : kcontext) = pair :: kctx
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

fun lookup_kind (n : int) kctx : kind option = 
    case nth_error kctx n of
        NONE => NONE
      | SOME (_, k) => SOME k

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

fun lookup (n : int) (ctx : tcontext) : ty option = 
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

fun get_base s =
    case s of
        Basic (s, _) => s
      | Subset ((s, _), _) => s

fun collect (pairs, ps) : bscontext * prop list = 
    let fun get_p s n ps =
	    case s of
	        Basic _ => ps
	      | Subset (_, BindI (_, p)) => shiftx_i_p 0 n p :: ps
        val bctx = map (mapSnd get_base) pairs
        val (ps', _) = foldl (fn ((name, s), (ps, n)) => (get_p s n ps, n + 1)) ([], 0) pairs
    in
        (bctx, ps @ ps')
    end

(* exception Unimpl *)

exception Error of region * string list

fun runError m _ =
    OK (m ())
    handle
    Error e => Failed e

(* use cell to mimic the Writer monad *)
local								    

    val acc = ref ([] : vc list)

    fun tell vc =
        (
	  (* print (sprintf "Output VC:\n$" [str_vc vc]); *)
	  acc := vc :: !acc)

    fun runWriter m _ =
        (acc := []; let val r = m () in (r, rev (!acc)) end)

    fun check_length_n (n, ls, r) =
        if length ls = n then
	    ()
        else
	    raise Error (r, ["List length mismatch"])

    fun check_length (a, b, r) =
        if length a = length b then
	    ()
        else
	    raise Error (r, ["List length mismatch"])

    fun is_le (ctx : scontext, d : idx, d' : idx, r) =
        let val (bctx, ps) = collect ctx in
	    tell (bctx, ps, d %<= d', r)
        end
	    
    fun is_eq (ctx : scontext, i : idx, i' : idx, r) = 
        let val (bctx, ps) = collect ctx in
	    tell (bctx, ps, BinPred (EqP, i, i'), r)
        end

    fun is_eqs (ctx, is, is', r) =
        (check_length (is, is', r);
         app (fn (i, i') => is_eq (ctx, i, i', r)) (ListPair.zip (is, is')))
	    
    fun is_true (ctx : scontext, p : prop, r) = 
        let val (bctx, ps) = collect ctx in
	    tell (bctx, ps, p, r)
        end

    fun is_iff (ctx : scontext, p1 : prop, p2 : prop) = 
        let val (bctx, ps) = collect ctx in
	    tell (bctx, ps, p1 <-> p2, get_region_p p1)
        end

    fun is_eqvbsort_b s s' =
        case (s, s') of
	    (Time, Time) => true
	  | (Nat, Nat) => true
	  | (Bool, Bool) => true
	  | (BSUnit, BSUnit) => true
	  | _ => false

    fun is_eqvbsort ((s, r), (s', _)) =
        if is_eqvbsort_b s s' then
	    ()
        else
	    raise Error (r, [sprintf "Basic sort mismatch: $ and $" [str_b s, str_b s']])
		  
    fun is_eqvsort (ctx, s, s') =
        case (s, s') of
	    (Basic s1, Basic s1') =>
	    is_eqvbsort (s1, s1')
	  | (Subset (s1, BindI ((name, _), p)), Subset (s1', BindI (_, p'))) =>
	    (is_eqvbsort (s1, s1');
	     is_iff (add_sorting (name, Basic s1) ctx, p, p'))
	  | (Subset (s1, BindI ((name, _), p)), Basic s1') =>
	    (is_eqvbsort (s1, s1');
	     is_true (add_sorting (name, Basic s1) ctx, p, get_region_p p))
	  | (Basic s1, Subset (s1', BindI ((name, _), p))) =>
	    (is_eqvbsort (s1, s1');
	     is_true (add_sorting (name, Basic s1) ctx, p, get_region_p p))

    fun is_eqvsorts (ctx, sorts, sorts', r) =
        (check_length (sorts, sorts', r);
         ListPair.app (fn (s, s') => is_eqvsort (ctx, s, s')) (sorts, sorts'))
	    
    fun sort_mismatch ctx i expect have =  "Sort mismatch for " ^ str_i ctx i ^ ": expect " ^ expect ^ " have " ^ str_s ctx have

    fun is_wfsort (ctx : scontext, s : sort) =
        case s of
	    Basic _ => ()
	  | Subset (s, BindI ((name, _), p)) =>
	    is_wfprop (add_sorting (name, Basic s) ctx, p)

    and is_wfprop (ctx : scontext, p : prop) =
	case p of
	    True _ => ()
	  | False _ => ()
          | Not (p, _) => 
            is_wfprop (ctx, p)
	  | BinConn (_, p1, p2) =>
	    (is_wfprop (ctx, p1);
	     is_wfprop (ctx, p2))
	  | BinPred (EqP, i1, i2) =>
	    let val s1 = get_bsort (ctx, i1)
		val s2 = get_bsort (ctx, i2)
	    in
		if s1 = s2 then ()
		else raise Error (get_region_p p, [sprintf "Base-sorts not equal: $ and $" [str_b s1, str_b s2]])
	    end
	  | BinPred (opr, i1, i2) =>
	    let val s1 = get_bsort (ctx, i1)
		val s2 = get_bsort (ctx, i2)
	    in
                case (s1, s2) of
                      (Nat, Nat) => ()
                    | (Time, Time) => ()
                    | _ => raise Error (get_region_p p, sprintf "Sorts of operands of $ can only be both Nat or Time:" [str_bin_pred opr] :: indent ["left: " ^ str_b s1, "right: " ^ str_b s2])
	    end


    and check_sort (ctx, i, s) : unit =
	let val s' = get_bsort (ctx, i)
            val s'' = (s', get_region_i i)
        in
	    (case s of
		 Subset (s1, BindI (_, p)) =>
		 (is_eqvbsort (s'', s1);
		  is_true (ctx, subst_i_p i p, get_region_i i))
	       | Basic s1 => 
		 is_eqvbsort (s'', s1))
            handle Error (_, msg) => 
                   let val ctxn = sctx_names ctx in
                       raise Error (get_region_i i, 
                                    sprintf "index $ (of base sort $) is not of sort $" [str_i ctxn i, str_b s', str_s ctxn s] :: 
                                    "Cause:" :: 
                                    indent msg)
                   end
	end

    (* binary operations on idx are overloaded for Nat and Time *)
    and get_bsort (ctx, i) =
	case i of
	    VarI (x, r) =>
	    (case lookup_sort x ctx of
      		 SOME s => get_base s
      	       | NONE => raise Error (r, ["Unbound index variable: " ^ str_v (sctx_names ctx) x]))
          | UnOpI (ToReal, i, _) =>
            (check_bsort (ctx, i, Nat);
             Time)
          | UnOpI (Log2, i, _) =>
            (check_bsort (ctx, i, Time);
             Time)
	  | BinOpI (opr, i1, i2) =>
            let val s1 = get_bsort (ctx, i1)
                val s2 = get_bsort (ctx, i2)
            in
                case (s1, s2) of
                    (Nat, Nat) => Nat
                  | (Time, Time) => Time
                  | _ => raise Error (get_region_i i, sprintf "Sorts of operands of $ don't match:" [str_idx_bin_op opr] :: indent ["left: " ^ str_b s1, "right: " ^ str_b s2])
            end
	  | ConstIT (x, _) => 
	    Time
	  | ConstIN (n, r) => 
	    if n >= 0 then
		Nat
	    else
		raise Error (r, ["Natural number constant must be non-negative"])
	  | TrueI _ => Bool
	  | FalseI _ => Bool
	  | TTI _ => BSUnit

    and check_bsort (ctx, i, s) : unit =
	is_eqvbsort ((get_bsort (ctx, i), get_region_i i), (s, dummy))

    fun is_wfsorts (ctx, s) = List.app (fn s => is_wfsort (ctx, s)) s

    fun check_sorts (ctx, is, sorts, r) =
        (check_length (is, sorts, r);
         ListPair.app (fn (i, s) => check_sort (ctx, i, s)) (is, sorts))

    (* k => Type *)
    fun recur_kind k = ArrowK (false, 0, k)

    fun kind_mismatch (ctx as (sctx, kctx)) c expect have =  "Kind mismatch for " ^ str_t ctx c ^ ": expect " ^ expect ^ " have " ^ str_k sctx have

    fun fetch_kind (kctx, (a, r)) =
        case lookup_kind a kctx of
      	    SOME k => k
      	  | NONE => raise Error (r, ["Unbound type variable: " ^ str_v (names kctx) a])

    fun is_wf_mty (ctx as (sctx : scontext, kctx : kcontext), c : mty) : unit = 
        let val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	(* val () = print (sprintf "Type wellformedness checking: $\n" [str_t ctxn c]) *)
        in
	    case c of
	        Arrow (c1, d, c2) => 
	        (is_wf_mty (ctx, c1);
	         check_sort (sctx, d, STime);
	         is_wf_mty (ctx, c2))
	      | Unit _ => ()
	      | Prod (c1, c2) => 
	        (is_wf_mty (ctx, c1);
	         is_wf_mty (ctx, c2))
	      | Sum (c1, c2) => 
	        (is_wf_mty (ctx, c1);
	         is_wf_mty (ctx, c2))
	      | UniI (s, BindI ((name, _), c)) => 
	        (is_wfsort (sctx, s);
	         is_wf_mty (add_sorting_sk (name, s) ctx, c))
	      | ExI (s, BindI ((name, _), c)) => 
	        (is_wfsort (sctx, s);
	         is_wf_mty (add_sorting_sk (name, s) ctx, c))
	      | AppRecur (nameself, ns, t, is, r) =>
	        let val sorts = List.map #2 ns in
		    is_wfsorts (sctx, sorts);
		    is_wf_mty (add_nondep_sortings_sk (rev ns) (add_kinding_sk (nameself, recur_kind sorts) ctx), t);
		    check_sorts (sctx, is, sorts, r)
	        end
	      | AppV (x, ts, is, r) => 
	        (case fetch_kind (kctx, x) of
		     ArrowK (_, n, sorts) => 
		     (check_length_n (n, ts, r);
		      check_sorts (sctx, is, sorts, r)))
	      | Int _ => ()
        end

    fun is_wftype (ctx as (sctx : scontext, kctx : kcontext), c : ty) : unit = 
        let val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	(* val () = print (sprintf "Type wellformedness checking: $\n" [str_t ctxn c]) *)
        in
	    case c of
                Mono t =>
                is_wf_mty (ctx, t)
	      | Uni ((name, _), c) => 
	        is_wftype (add_kinding_sk (name, Type) ctx, c)
        end

    fun not_subtype ctx c c' = str_t ctx c ^ " is not subtype of " ^ str_t ctx c'

    (* is_submtype assumes that the types are already checked against the given kind, so it doesn't need to worry about their well-formedness *)
    fun is_submtype (ctx as (sctx : scontext, kctx : kcontext), c : mty, c' : mty, r) =
        let val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	    (* val () = print (sprintf "Subtyping checking: \n$\n<:\n$\n" [str_t ctxn c, str_t ctxn c']) *)
            (* val () = println $ str_region "" "ilist.timl" r *)
        in
	    case (c, c') of
	        (Arrow (c1, d, c2), Arrow (c1', d', c2')) =>
	        (is_submtype (ctx, c1', c1, r);
	         is_le (sctx, d, d', r);
	         is_submtype (ctx, c2, c2', r))
	      | (Unit _, Unit _) => ()
	      | (Prod (c1, c2), Prod (c1', c2')) =>
	        (is_submtype (ctx, c1, c1', r);
	         is_submtype (ctx, c2, c2', r))
	      | (Sum (c1, c2), Sum (c1', c2')) => 
	        (is_submtype (ctx, c1, c1', r);
	         is_submtype (ctx, c2, c2', r))
	      | (UniI (s, BindI ((name, _), c)), UniI (s', BindI (_, c'))) => 
	        (is_eqvsort (sctx, s, s');
	         is_submtype (add_sorting_sk (name, s) ctx, c, c', r))
	      | (ExI (s, BindI ((name, _), c)), ExI (s', BindI (_, c'))) => 
	        (is_eqvsort (sctx, s, s');
	         is_submtype (add_sorting_sk (name, s) ctx, c, c', r))
	      (* currently don't support subtyping for recursive types, so they must be equivalent *)
	      | (AppRecur (nameself, ns, t, is, _), AppRecur (_, ns', t', is', _)) => 
	        let val sorts = List.map #2 ns
		    val sorts' = List.map #2 ns'
		    val () = is_eqvsorts (sctx, sorts, sorts', r)
		    val () = is_eqs (sctx, is, is', r)
		    val ctx' = add_nondep_sortings_sk (rev ns) (add_kinding_sk (nameself, recur_kind sorts) ctx) in
		    is_eqvmtype (ctx', t, t', r)
	        end
	      | (AppV ((a, _), ts, is, _), AppV ((a', _), ts', is', _)) => 
	        if a = a' then
		    (app (fn (t, t') => is_eqvmtype (ctx, t, t', r)) (ListPair.zip (ts, ts'));
		     is_eqs (sctx, is, is', r))
	        else
		    raise Error (get_region_mt c, [not_subtype ctxn (Mono c) (Mono c')])
	      | (Int _, Int _) => ()
	      | _ => raise Error (get_region_mt c, [not_subtype ctxn (Mono c) (Mono c')])
        end

    and is_eqvmtype (kctx, c, c', r) =
	(is_submtype (kctx, c, c', r);
	 is_submtype (kctx, c', c, r))

    fun is_subtype (ctx as (sctx : scontext, kctx : kcontext), c : ty, c' : ty, r) =
        let val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	    (* val () = print (sprintf "Subtyping checking: \n$\n<:\n$\n" [str_t ctxn c, str_t ctxn c']) *)
            (* val () = println $ str_region "" "ilist.timl" r *)
        in
	    case (c, c') of
	        (Mono t, Mono t') =>
	        is_submtype (ctx, t', t, r)
	      | (Uni ((name, _), c), Uni (_, c')) => 
	        is_subtype (add_kinding_sk (name, Type) ctx, c, c', r)
	      | _ => raise Error (get_region_t c, [not_subtype ctxn c c'])
        end

    and is_eqvtype (kctx, c, c', r) =
	(is_subtype (kctx, c, c', r);
	 is_subtype (kctx, c', c, r))

    fun no_join ctx c c' = "Cannot find a join (minimal supertype) of " ^ str_mt ctx c ^ " and " ^ str_mt ctx c'
    fun no_meet ctx c c' = "Cannot find a meet (maximal subtype) of " ^ str_mt ctx c ^ " and " ^ str_mt ctx c'

    open IdxEqual
             
    fun smart_max a b =
      if eq_i a (T0 dummy) then
          b
      else if eq_i b (T0 dummy) then
          a
      else
          BinOpI (MaxI, a, b)

    (* c and c' are already checked for wellformedness *)
    fun join_type (ctx as (sctx : scontext, kctx : kcontext), c : mty, c' : mty, r) : mty = 
        let val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	    (* val () = print (sprintf "Joining $ and $\n" [str_t ctxn c, str_t ctxn c']) *)
            (* val () = println $ str_region "" "ilist.timl" r *)
        in
	    case (c, c') of
	        (Arrow (c1, d, c2), Arrow (c1', d', c2')) => 
	        let val c1'' = meet (ctx, c1, c1', r) 
		    val d'' = smart_max d d' 
		    val c2'' = join_type (ctx, c2, c2', r) in
		    Arrow (c1'', d'', c2'')
	        end
	      | (Unit r0, Unit _) => Unit r0
	      | (Prod (c1, c2), Prod (c1', c2')) => 
	        let val c1'' = join_type (ctx, c1, c1', r) 
		    val c2'' = join_type (ctx, c2, c2', r) in
		    Prod (c1'', c2'')
	        end
	      | (Sum (c1, c2), Sum (c1', c2')) => 
	        let val c1'' = join_type (ctx, c1, c1', r) 
		    val c2'' = join_type (ctx, c2, c2', r) in
		    Sum (c1'', c2'')
	        end
	      | (UniI (s, BindI ((name, r0), t)), UniI (s', BindI (_, t'))) => 
	        let val () = is_eqvsort (sctx, s, s')
		    val t'' = join_type (add_sorting_sk (name, s) ctx, t, t', r) in
		    UniI (s, BindI ((name, r0), t''))
	        end
	      | (ExI (s, BindI ((name, r0), t)), ExI (s', BindI (_, t'))) => 
	        let val () = is_eqvsort (#1 ctx, s, s')
		    val t'' = join_type (add_sorting_sk (name, s) ctx, t, t', r) in
		    ExI (s, BindI ((name, r0), t''))
	        end
	      (* currently don't support join for recursive types, so they must be equivalent *)
	      | (AppRecur _, AppRecur _) => 
	        (is_eqvmtype (ctx, c, c', r);
	         c)
	      | (AppV _, AppV _) => 
	        (is_eqvmtype (ctx, c, c', r);
	         c)
	      | (Int r0, Int _) => Int r0
	      | _ => raise Error (get_region_mt c, [no_join ctxn c c'])
        end

    and meet (ctx as (sctx : scontext, kctx : kcontext), c : mty, c' : mty, r) : mty = 
	let val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	in
	    case (c, c') of
		(Arrow (c1, d, c2), Arrow (c1', d', c2')) => 
		let val c1'' = join_type (ctx, c1, c1', r) 
		    val d'' = BinOpI (MinI, d, d')
		    val c2'' = meet (ctx, c2, c2', r) in
		    Arrow (c1'', d'', c2'')
		end
	      | (Unit r0, Unit _) => Unit r0
	      | (Prod (c1, c2), Prod (c1', c2')) => 
		let val c1'' = meet (ctx, c1, c1', r) 
		    val c2'' = meet (ctx, c2, c2', r) in
		    Prod (c1'', c2'')
		end
	      | (Sum (c1, c2), Sum (c1', c2')) => 
		let val c1'' = meet (ctx, c1, c1', r) 
		    val c2'' = meet (ctx, c2, c2', r) in
		    Sum (c1'', c2'')
		end
	      | (UniI (s, BindI ((name, r0), t)), UniI (s', BindI (_, t'))) => 
		let val () = is_eqvsort (sctx, s, s')
		    val t'' = meet (add_sorting_sk (name, s) ctx, t, t', r) in
		    UniI (s, BindI ((name, r0), t''))
		end
	      | (ExI (s, BindI ((name, r0), t)), ExI (s', BindI (_, t'))) => 
		let val () = is_eqvsort (#1 ctx, s, s')
		    val t'' = meet (add_sorting_sk (name, s) ctx, t, t', r) in
		    ExI (s, BindI ((name, r0), t''))
		end
	      (* currently don't support meet for recursive types, so they must be equivalent *)
	      | (AppRecur _, AppRecur _) => 
		(is_eqvmtype (ctx, c, c', r);
		 c)
	      | (AppV _, AppV _) => 
		(is_eqvmtype (ctx, c, c', r);
		 c)
	      | (Int r0, Int _) => Int r0
	      | _ => raise Error (get_region_mt c, [no_meet ctxn c c'])
	end

    fun fetch_constr (ctx, (x, r)) =
        case nth_error ctx x of
	    SOME (name, c) => (name, c)
	  | NONE => raise Error (r, [sprintf "Unbound constructor: $" [str_v (names ctx) x]])

    fun constr_type ((family, tnames, ibinds) : constr) = 
        let val (ns, (t, is)) = unfold_ibinds ibinds
            val ts = (map (fn x => VarT (x, dummy)) o rev o range o length) tnames
	    val t2 = AppV ((shiftx_v 0 (length tnames) family, dummy), ts, is, dummy)
	    val t = Arrow (t, T0 dummy, t2)
	    val t = foldr (fn ((name, s), t) => UniI (s, BindI ((name, dummy), t))) t ns
            val t = Mono t
	    val t = foldr (fn (name, t) => Uni ((name, dummy), t)) t tnames
        in
	    t
        end

    fun fetch_constr_type (ctx : ccontext, cx) =
        let val (cname, c) = fetch_constr (ctx, cx)
	    val t = constr_type c
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

    local
        
        datatype inhab =
                 TrueH
                 | ConstrH of var * inhab
                 | PairH of inhab * inhab
                 | TTH

        fun str_cover cctx c =
            case c of
                TrueC => "_"
              | FalseC => "nothing"
              | AndC (c1, c2) => sprintf "($ /\\ $)" [str_cover cctx c1, str_cover cctx c2]
              | OrC (c1, c2) => sprintf "($ \\/ $)" [str_cover cctx c1, str_cover cctx c2]
              | ConstrC (x, c) => sprintf "($ $)" [str_v cctx x, str_cover cctx c]
              | PairC (c1, c2) => sprintf "($, $)" [str_cover cctx c1, str_cover cctx c2]
              | TTC => "()"

        fun str_inhab cctx c =
            case c of
                TrueH => "_"
              | ConstrH (x, c) => sprintf "($ $)" [str_v cctx x, str_inhab cctx c]
              | PairH (c1, c2) => sprintf "($, $)" [str_inhab cctx c1, str_inhab cctx c2]
              | TTH => "()"

        infix 2 \/
        val op/\ = AndC
        val op\/ = OrC

        fun combine_covers covers = foldl' (swap OrC) FalseC covers

        val impossible = Impossible "cover has the wrong type"

        fun get_family (x : constr) = #1 x
        fun get_family_members cctx x =
            (rev o List.mapPartial (fn (n, (_, c)) => if get_family c = x then SOME n else NONE) o add_idx) cctx

        fun cover_neg cctx (t : ty) c =
            let fun neg c = cover_neg cctx t c
                fun neg' t c = cover_neg cctx t c
            in
                case c of
                    TrueC => FalseC
                  | FalseC => TrueC
                  | AndC (a, b) => neg a \/ neg b
                  | OrC (a, b) => neg a /\ neg b
                  | TTC => FalseC
                  | PairC (c1, c2) =>
                    (case t of
                         Mono (Prod (t1, t2)) =>
                         PairC (neg' (Mono t1) c1, c2) \/
                         PairC (c1, neg' (Mono t2) c2) \/
                         PairC (neg' (Mono t1) c1, neg' (Mono t2) c2)
                       | _ => raise impossible)
                  | ConstrC (x, c) =>
	            (case t of
	                 Mono (AppV ((family, _), ts, _, _)) =>
	                 let val all = get_family_members cctx family
		             val others = diff op= all [x]
                             val (_, (_, _, ibinds)) = fetch_constr (cctx, (x, dummy))
                             val (_, (t', _)) = unfold_ibinds ibinds
		             val t' = subst_ts_mt ts t'
                             val covers = ConstrC (x, cover_neg cctx (Mono t') c) :: map (fn y => ConstrC (y, TrueC)) others
	                 in
                             combine_covers covers
	                 end
	               | _ => raise impossible)
            end

                
        fun find_inhabitant (ctx as (sctx, kctx, cctx)) (t : ty) cs =
            let (* use exception to mimic Error monad *)
                exception Incon of string
                fun f (t : ty) cs : inhab =
                    case cs of
                        [] =>
                        let
                            val () = Debug.println (sprintf "Empty constraints now. Now try to find any inhabitant of type $" [str_t (sctx_names sctx, names kctx) t])
                        in
                            case t of
                                Mono (AppV (tx as (family, _), ts, _, _)) =>
                                (case fetch_kind (kctx, tx) of
                                     ArrowK (true, _, _) =>
	                             let val all = get_family_members cctx family
                                     in
                                         case all of x :: _ => ConstrH (x, TrueH) | [] => raise Incon "empty datatype"
                                     end
                                   | _ => TrueH (* an abstract type is treated as an inhabited type *)
                                )
                              | Mono (Unit _) => TTH
                              | Mono (Prod (t1, t2)) => PairH (f (Mono t1) [], f (Mono t2) [])
                              | _ => TrueH
                        end
                      | c :: cs =>
                        let
                            val () = Debug.println (sprintf "try to satisfy $" [(join ", " o map (str_cover (names cctx))) (c :: cs)])
                        in
                            case (c, t) of
                                (TrueC, _) => f t cs
                              | (FalseC, _) => raise Incon "false"
                              | (AndC (c1, c2), _) => f t (c1 :: c2 :: cs)
                              | (OrC (c1, c2), _) =>
                                (f t (c1 :: cs) handle Incon _ => f t (c2 :: cs))
                              | (TTC, Mono (Unit _)) =>
                                (case allSome (fn c => case c of TTC => SOME () | _ => NONE) cs of
                                     OK _ => TTH
                                   | Failed i => f t (to_hd i cs @ [c])
                                )
                              | (PairC (c1, c2), Mono (Prod (t1, t2))) =>
                                (case allSome (fn c => case c of PairC p => SOME p | _ => NONE ) cs of
                                     OK cs =>
                                     let val (cs1, cs2) = unzip cs
                                         val c1 = f (Mono t1) (c1 :: cs1)
                                         val c2 = f (Mono t2) (c2 :: cs2)
                                     in
                                         PairH (c1, c2)
                                     end
                                   | Failed i => f t (to_hd i cs @ [c])
                                )
                              | (ConstrC (x, c'), Mono (AppV ((family, _), ts, _, _))) =>
                                let fun g c =
                                        case c of
                                            ConstrC (y, c) =>
                                            if y = x then
                                                SOME c
                                            else
                                                raise Incon "diff-constr"
                                          | _ => NONE
                                in
                                    case allSome g cs of
                                        OK cs' =>
                                        let val (_, (_, _, ibinds)) = fetch_constr (cctx, (x, dummy))
                                            val (_, (t', _)) = unfold_ibinds ibinds
		                            val t' = subst_ts_mt ts t'
                                            val () = Debug.println (sprintf "All are $, now try to satisfy $" [str_v (names cctx) x, (join ", " o map (str_cover (names cctx))) (c' :: cs')])
                                            val c' = f (Mono t') (c' :: cs')
                                            val () = Debug.println (sprintf "Plugging $ into $" [str_inhab (names cctx) c', str_v (names cctx) x])
                                        in
                                            ConstrH (x, c')
                                        end
                                      | Failed i => f t (to_hd i cs @ [c])
                                end
                              | _ => raise impossible
                        end
            in
                SOME (f t cs) handle Incon debug => NONE
            end

        fun cover_imply cctx t (a, b) : cover =
            cover_neg cctx t a \/ b
                                      
        fun any_missing ctx t c =
            let val nc = cover_neg (#3 ctx) t c
                val () = Debug.println (str_cover (names (#3 ctx)) nc)
            in
                find_inhabitant ctx t [nc]
            end

        fun is_covered ctx t small big =
            (isNull o any_missing ctx t o cover_imply (#3 ctx) t) (small, big)

    in              

    fun check_redundancy (ctx as (_, _, cctx), t, prevs, this, r) =
        let val prev = combine_covers prevs
        in
	    if not (is_covered ctx t this prev) then ()
	    else raise Error (r, sprintf "Redundant rule: $" [str_cover (names cctx) this] :: indent [sprintf "Has already been covered by previous rules: $" [(join ", " o map (str_cover (names cctx))) prevs]])
        end
            
    fun check_exhaustive (ctx as (_, _, cctx), t : ty, covers, r) =
        let val cover = combine_covers covers
            val () = Debug.println (str_cover (names cctx) cover)
        in
            case any_missing ctx t cover of
                NONE => ()
              | SOME missed =>
	        raise Error (r, [sprintf "Not exhaustive, at least missing this case: $" [str_inhab (names cctx) missed]])
        end

    end

    (* t is already checked for wellformedness *)
    fun match_ptrn (ctx as (sctx : scontext, kctx : kcontext, cctx : ccontext), pn : ptrn, t : mty) : cover * context =
        let val skctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
            fun match_error () = raise Error (get_region_pn pn, [sprintf "Pattern $ doesn't match type $" [str_pn (names cctx) pn, str_t skctxn t]])
        in
	    case pn of
	        ConstrP ((cx, cr), inames, pn, r) =>
                (case t of
                     Mono (AppV ((family, _), ts, is, _)) =>
 	             let val (_, c as (family', tnames, ibinds)) = fetch_constr (cctx, (cx, cr))
                         val (name_sorts, (t1, is')) = unfold_ibinds ibinds
                     in
		         if family' = family andalso length tnames = length ts andalso length is' = length is then
                             if length inames = length name_sorts then
		                 let val t1 = subst_ts_mt ts t1
			             val is = map (shiftx_i_i 0 (length name_sorts)) is
			             val ps = map (fn (a, b) => BinPred (EqP, a, b)) (ListPair.zip (is', is))
                                     val ctxd = ((rev (ListPair.zip (inames, snd (ListPair.unzip name_sorts))), ps), [], [], [])
                                     val ctx = add_ctx_skc ctxd ctx
                                     val (cover, ctxd') = match_ptrn (ctx, default (TTP dummy) pn, Mono t1)
                                     val ctxd = add_ctx ctxd' ctxd
                                     val cover = ConstrC (cx, cover)
		                 in
			             (cover, ctxd)
		                 end
                             else
                                 raise Error (r, [sprintf "This constructor requires $ index argument(s), not $" [str_int (length name_sorts), str_int (length inames)]])
		         else
		             raise Error 
                                   (r, sprintf "Type of constructor $ doesn't match datatype " [str_v (names cctx) cx] :: 
                                       indent ["expect: " ^ str_v kctxn family, 
                                               "got: " ^ str_v kctxn family'])
                     end
                   | _ => match_error ())
              | VarP (name, _) =>
                (TrueC, (([], []), [], [], [(name, t)]))
              | PairP (pn1, pn2) =>
                (case t of
                     Mono (Prod (t1, t2)) =>                          
                     let
                         val (cover1, ctxd) = match_ptrn (ctx, pn1, Mono t1)
                         val ctx = add_ctx_skc ctxd ctx
                         val (cover2, ctxd') = match_ptrn (ctx, pn2, Mono (shift_ctx_mt ctxd t2))
                         val ctxd = add_ctx ctxd' ctxd
                     in
                         (PairC (cover1, cover2), ctxd)
                     end
                   | _ => match_error ())
              | TTP _ =>
                (case t of
                     Mono (Unit _) =>
                     (TTC, (([], []), [], [], []))
                   | _ => match_error ())
              | AliasP ((pname, _), pn, _) =>
                let val ctxd = (([], []), [], [], [(pname, t)])
                    val (cover, ctxd') = match_ptrn (ctx, pn, t)
                    val ctxd = add_ctx ctxd' ctxd
                in
                    (cover, ctxd)
                end
        end

    fun get_ds (_, _, _, tctxd) = map (snd o snd) tctxd

    fun escapes nametype name domaintype domain =
        [sprintf "$ $ escapes local scope in $ $" [nametype, name, domaintype, domain]]
	    
    fun forget_mt r (skctxn as (sctxn, kctxn)) (sctxl, kctxl) t = 
        let val t = forget_t_mt 0 kctxl t
		    handle ForgetError x => raise Error (r, escapes "type variable" (str_v kctxn x) "type" (str_mt skctxn t))
	    val t = forget_i_mt 0 sctxl t
		    handle ForgetError x => raise Error (r, escapes "index variable" (str_v sctxn x) "type" (str_mt skctxn t))
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
		    handle ForgetError x => raise Error (r, escapes "type variable" (str_v kctxn x) "type" (str_t skctxn t))
	    val t = forget_i_t 0 sctxl t
		    handle ForgetError x => raise Error (r, escapes "index variable" (str_v sctxn x) "type" (str_t skctxn t))
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
        handle ForgetError x => raise Error (r, escapes "index variable" (str_v sctxn x) "time" (str_i sctxn d))

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

    fun check_fix_body e =
        case e of
    	    AbsI (_, _, e') => check_fix_body e'
    	  | Abs _ => ()
    	  | _ => raise Error (get_region_e e, ["The body of fixpoint must have the form ({_ : _} ... {_ : _} (_ : _) => _)"])

    fun is_wf_return (skctx as (sctx, _), return) =
      case return of
          (SOME t, SOME d) =>
	  (is_wf_mty (skctx, t);
	   check_sort (sctx, d, STime))
        | (SOME t, NONE) =>
	  is_wf_mty (skctx, t)
        | (NONE, SOME d) =>
	  check_sort (sctx, d, STime)
	| (NONE, NONE) => ()

    fun fetch_var (tctx, (x, r)) =
	case lookup x tctx of
      	    SOME t => t
      	  | NONE => raise Error (r, ["Unbound variable: " ^ str_v (names tctx) x])

    fun insert t =
        case t of
            Base t => t
          | Uni (_, t) => insert (subst_t_t (fresh_t ()) t)

    fun get_mtype (ctx as (sctx : scontext, kctx : kcontext, cctx : ccontext, tctx : tcontext), e : expr) : ty * idx =
        let val skctx = (sctx, kctx) 
	    val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
	    val skctxn = (sctxn, kctxn)
	    (* val () = print (sprintf "Typing $\n" [str_e ctxn e]) *)
	    val (t, d) =
	        case e of
		    Var x =>
                    (empty_assign, insert (fetch_var (tctx, x)), T0 dummy)
		  | App (e1, e2) =>
		    let 
                        val (assign, uni_idxs, vc, t1, d1) = get_mtype (ctx, e1) 
                        val ctx = assign_ctx assign ctx
                        val ctx = add_uni_idxs uni_idxs ctx
                        val (assign', uni_idxs', vc', t2, d2) = get_mtype (ctx, e2) 
                        val t1 = assign_mt assign' t1
                        val assign = assign_assign assign' assign
                        val uni_idxs = uni_idxs' @ uni_idxs
                        val vc = vc_and vc vc'
                        val d = fresh_i ()
                        val uni_idxs = d :: uni_idxs
                        val t = fresh_t ()
                        val (assign', vc') = unify (t1, Arrow (t2, d, t))
                        val t = assign_mt assign' t
                        val assign = assign_assign assign' assign
                        val vc = vc_and vc vc'
                    in
                        (assign, uni_idxs, vc, t, d1 %+ d2 %+ T1 dummy %+ d) 
		    end
		  | Abs (pn, e) => 
		    let val t = fresh_t ()
                        val skcctx = (sctx, kctx, cctx) 
                        val (assign', cover, ctxd) = match_ptrn (skcctx, pn, Mono t)
                        val t = assign_mt assign' t
                        val assign = assign'
	                val () = check_exhaustive (skcctx, Mono t, [cover], get_region_pn pn)
                        val ctx = assign_ctx assign ctx
                        val ctx = add_ctx ctxd ctx
		        val (assign', t1, d) = get_mtype (ctx, e)
                        val t = assign_mt assign' t
                        val assign = assign_assign assign' assign
		        val t1 = forget_ctx_mt (get_region_e e) ctx ctxd t1 
                        val d = forget_ctx_d (get_region_e e) ctx ctxd d
                    in
		        (assign, Arrow (t, d, t1), T0 dummy)
		    end
		  | TT _ => 
                    (empty_assign, Unit dummy, T0 dummy)
		  | Pair (e1, e2) => 
		    let 
                        val (assign', t1, d1) = get_mtype (ctx, e1) 
                        val ctx = assign_ctx assign' ctx
                        val assign = assign'
		        val (t2, d2) = get_mtype (ctx, e2) 
                        val t1 = assign_mt assign' t1
                        val assign = assign_assign assign' assign
                    in
		        (assign, Prod (t1, t2), d1 %+ d2)
		    end
		  | Fst e => 
		    let 
                        val (assign', t, d) = get_mtype (ctx, e) 
                        val ctx = assign_ctx assign' ctx
                        val assign = assign'
                        val t1 = fresh_t ()
                        val t2 = fresh_t ()
                        val assign' = unify (t1, Prod (t1, t2))
                        val t1 = assign_mt assign' t1
                        val assign = assign_assign assign' assign
                    in 
                        (assign, t1, d)
		    end
		  | Snd e => 
		    let 
                        val (assign', t, d) = get_mtype (ctx, e) 
                        val ctx = assign_ctx assign' ctx
                        val assign = assign'
                        val t1 = fresh_t ()
                        val t2 = fresh_t ()
                        val assign' = unify (t1, Prod (t1, t2))
                        val t2 = assign_mt assign' t2
                        val assign = assign_assign assign' assign
                    in 
                        (assign, t2, d)
		    end
		  | Inl (t2, e) => 
		    let 
		        val () = is_wf_mty (skctx, t2) 
                        val (assign, t1, d) = get_mtype (ctx, e)
                    in
		        (assign, Sum (t1, t2), d)
		    end
		  | Inr (t1, e) => 
		    let 
		        val () = is_wf_mty (skctx, t1) 
                        val (assign, t2, d) = get_mtype (ctx, e)
                    in
		        (assign, Sum (t1, t2), d)
		    end
		  | SumCase (e0, name1, e1, name2, e2) => 
		    let 
                        val (assign', t, d) = get_mtype (ctx, e0) 
                        val ctx = assign_ctx assign' ctx
                        val assign = assign'
                        val t1 = fresh_t ()
                        val t2 = fresh_t ()
                        val assign' = unify (t1, Prod (t1, t2))
                        val ctx = assign_ctx assign' ctx
                        val t1 = assign_mt assign' t1
                        val t2 = assign_mt assign' t2
                        val assign = assign_assign assign' assign
                        val (assign', t1', d1) = get_mtype (add_typing_skct (name1, Mono t1) ctx, e1)
                        val ctx = assign_ctx assign' ctx
                        val t2 = assign_mt assign' t2
                        val assign = assign_assign assign' assign
			val (t2', d2) = get_mtype (add_typing_skct (name2, Mono t2) ctx, e2)
                        val ctx = assign_ctx assign' ctx
                        val t1' = assign_mt assign' t1'
                        val assign = assign_assign assign' assign
                        val assign' = unify (t1', t2')
                        val t1' = assign_mt assign' t1'
                        val assign = assign_assign assign' assign
                        val d = d %+ smart_max d1 d2
                    in
			(assign, t1', d)
		    end
		  | AbsI (s, (name, r), e) => 
		    if is_value e then
		        let val () = is_wfsort (sctx, s)
                            val () = push_forall (name, s)
			    val (assign, t, _) = get_mtype ((add_sorting_skct (name, s) ctx), e) 
                            val () = pop_forall ()
                        in
			    (assign, UniI (s, BindI ((name, dummy), t)), T0 dummy)
		        end 
		    else
		        raise Error (get_region_e e, ["The body of a universal abstraction must be a value"])
		  | AppI (e, i) =>
		    let 
                        val (assign, t, d) = get_mtype (ctx, e) 
                    (* t must have enough information. We don't attempt to guess t *)
                    in
		        case t of
			    UniI (s, BindI(_, t1)) => 
			    let val () = check_sort (sctx, i, s) in
			        (assign, subst_i_mt i t1, d)
                                handle SubstUniVar x =>
                                       raise Error (get_region_e e, [sprintf "Can't infer the unification variable $ in type $ of expression $" [str_uni x, str_t skctxn t, str_e ctxn e]])
			    end
			  | t' => raise Error (mismatch ctxn e "(forall {_ : _}, _)" (Mono t'))
		    end
		  | Fold (t, e) => 
		    (case t of
		         AppRecur t1 =>
		         let val () = is_wf_mty (skctx, t)
			     val d = check_type (ctx, e, Mono (unroll t1))
                         in
			     (Mono t, d)
		         end
		       | t' => raise Error (mismatch_anno skctxn "((recur (_ :: _) (_ : _), _) _)" (Mono t')))
		  | Unfold e =>
		    let val (t, d) = get_mtype (ctx, e) in
		        case t of
	      		    AppRecur t1 =>
			    (Mono (unroll t1), d)
			  | t' => raise Error (mismatch ctxn e "((recur (_ :: _) (_ : _), _) _)" (Mono t'))
		    end
		  | Pack (t, i, e) =>
		    (case t of
		         ExI (s, BindI (_, t1)) =>
		         let val () = is_wf_mty (skctx, t)
			     val () = check_sort (sctx, i, s)
			     val d = check_type (ctx, e, Mono (subst_i_mt i t1))
                         in
			     (Mono t, d)
		         end
		       | t' => raise Error (mismatch_anno skctxn "(ex _ : _, _)" (Mono t')))
		  | Unpack (e1, return, idx_var, expr_var, e2) =>
                    let val (t1, d1) = get_mtype (ctx, e1)
                        val (t, d) =
                            case t1 of
			        ExI (s, BindI (_, t1')) =>
                                let val ctx' = add_sorting_skct (idx_var, s) ctx
		                    val ctx' = add_typing_skct (expr_var, Mono t1') ctx'
                                    val sctxn' = idx_var :: sctxn
                                    val skctxn' = (sctxn', kctxn)
                                    val () = is_wf_return (skctx, return)
                                    val (t, d) =
                                        case return of
                                            (SOME t, SOME d) =>
		                            let
                                                val () = check_type_time (ctx', e2, Mono (shift_i_mt t), shift_i_i d)
			                    in
				                (t, d)
			                    end
                                          | (SOME t, NONE) =>
		                            let 
				                val d = check_type (ctx', e2, Mono (shift_i_mt t))
                                                val d = forget_d (get_region_e e2) sctxn' 1 d
			                    in
				                (t, d)
			                    end
                                          | (NONE, SOME d) =>
		                            let 
				                val t = check_time_return_mty (ctx', e2, shift_i_i d)
                                                val t = forget_mt (get_region_e e2) skctxn' (1, 0) t
			                    in
				                (t, d)
			                    end
		                          | (NONE, NONE) =>
		                            let val (t, d) = get_mtype (ctx', e2)
                                                val t = forget_mt (get_region_e e2) skctxn' (1, 0) t
                                                val d = forget_d (get_region_e e2) sctxn' 1 d
			                    in
				                (t, d)
			                    end
                                in
                                    (Mono t, d)
                                end
		              | t1' => raise Error (mismatch ctxn e1 "(ex _ : _, _)" (Mono t1'))
                    in
		        (t, d1 %+ d)
                    end
		  | Ascription (e, t) => 
		    let val () = is_wftype (skctx, t)
		        val d = check_type (ctx, e, t)
                    in
		        (t, d)
		    end
		  | AscriptionTime (e, d) => 
		    let val () = check_sort (sctx, d, STime)
		        val t = check_time (ctx, e, d)
                    in
		        (t, d)
		    end
		  | BinOp (Add, e1, e2) =>
		    let val d1 = check_type (ctx, e1, Mono (Int dummy))
		        val d2 = check_type (ctx, e2, Mono (Int dummy)) in
		        (Mono (Int dummy), d1 %+ d2 %+ T1 dummy)
		    end
		  | Const _ => 
		    (Mono (Int dummy), T0 dummy)
		  | AppConstr (cx as (_, rc), is, e) => 
		    let val (cname, tc) = fetch_constr_type (cctx, cx)
		        val () = is_wftype (skctx, tc)
		        val (_, d) = get_mtype (ctx, e)
		        (* delegate to checking e' *)
		        val f = Var (0, rc)
		        val f = foldl (fn (i, e) => AppI (e, i)) f is
		        val e' = App (f, shift_e_e e)
		        val (t, _) = get_mtype (add_typing_skct (cname, tc) ctx, e') 
		    in
		        (* constructor application doesn't incur count *)
		        (t, d)
		    end
		  | Case (e, return, rules, r) => 
		    let val (t1, d1) = get_mtype (ctx, e)
                        val () = is_wf_return (skctx, return)
                        val (t, d) =
                            case return of
                                (SOME t, SOME d) =>
                                let 
                                    val _ = check_rules (ctx, rules, (t1, return), r)
		                in
		                    (t, d)
		                end
                              | (SOME t, NONE) =>
                                let 
                                    val tds = check_rules (ctx, rules, (t1, return), r)
                                in
                                    (t, (foldl' (fn (d, ds) => smart_max ds d) (T0 dummy) o map snd) tds)
                                end
                              | (NONE, SOME d) =>
                                let 
                                    val tds = check_rules (ctx, rules, (t1, return), r)
                                in
                                    case map fst tds of
                                        [] => raise Error (r, ["Empty case-matching must have a return type clause"])
                                      | t :: ts => 
                                        (foldl (fn (t, ts) => join_type (skctx, ts, t, r)) t ts, d)
                                end
                              | (NONE, NONE) =>
                                let val tds = check_rules (ctx, rules, (t1, return), r)
                                in
                                    case tds of
                                        [] => raise Error (r, ["Empty case-matching must have a return type clause"])
                                      | td :: tds => 
                                        foldl (fn ((t, d), (ts, ds)) => (join_type (skctx, ts, t, r), smart_max ds d)) td tds
                                end
                    in
		        (Mono t, d1 %+ d)
                    end
		  | Never t => 
		    (is_wftype (skctx, t);
		     is_true (sctx, False dummy, get_region_e e);
		     (t, T0 dummy))
		  | Let (decls, e, r) => 
		    let val (assign, ctxd as (sctxd, kctxd, _, _), ds, ctx) = check_decls (ctx, decls)
		        val (assign', t, d) = get_type (ctx, e)
                        val ctxd = assign_ctx assign' ctxd
                        val ctx = assign_ctx assign' ctx
                        val assign = assign_assign assign' assign
                        val ds = rev (d :: ds)
		        val t = forget_ctx_t r ctx ctxd t 
                        val ds = map (forget_ctx_d r ctx ctxd) ds
                        val d = foldl' (fn (d, acc) => acc %+ d) (T0 dummy) ds
                    in
		        (assign, t, d)
		    end
	(* val () = print (sprintf "  type: $ [for $]\n  time: $\n" [str_t skctxn t, str_e ctxn e, str_i sctxn d]) *)
        in
	    (t, d)
        end

    and get_mtype (ctx, e) =
        let 
	    val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
            val (t, d) = get_type (ctx, e)
        in
            case t of
                Mono t => (t, d)
              | t => raise Error (mismatch ctxn e "monotype" t)
        end
            
    and check_type (ctx as (sctx, kctx, cctx, tctx), e, t) =
	let 
	    val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
	    val (t', d') = get_type (ctx, e)
            val () = is_subtype ((sctx, kctx), t', t, get_region_e e)
                     handle Error (_, msg) =>
                            raise Error (get_region_e e, 
                                         #2 (mismatch ctxn e (str_t (sctxn, kctxn) t) t') @
                                         "Cause:" ::
                                         indent msg)
            (* val () = println "check type" *)
            (* val () = println $ str_region "" "ilist.timl" $ get_region_e e *)
	in
            d'
	end

    and check_time (ctx as (sctx, kctx, cctx, tctx), e, d) : ty =
	let 
	    val (t', d') = get_type (ctx, e)
            val () = is_le (sctx, d', d, get_region_e e)
            (* val () = println "check time" *)
            (* val () = println $ str_region "" "ilist.timl" $ get_region_e e *)
	in
            t'
	end

    and check_time_return_mty (ctx as (sctx, kctx, cctx, tctx), e, d) : mty =
	let 
	    val (t', d') = get_mtype (ctx, e)
            val () = is_le (sctx, d', d, get_region_e e)
	in
            t'
	end

    and check_type_time (ctx as (sctx, kctx, cctx, tctx), e, t, d) =
	let 
	    val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
	    (* val () = print (sprintf "Type checking $ against $ and $\n" [str_e ctxn e, str_t (sctxn, kctxn) t, str_i sctxn d]) *)
	    val d' = check_type (ctx, e, t)
            (* val () = println "check type & time" *)
            (* val () = println $ str_region "" "ilist.timl" $ get_region_e e *)
	in
	    is_le (sctx, d', d, get_region_e e)
	end

    and check_decls (ctx, decls) : context * idx list * context = 
        let fun f (decl, (assign, ctxd, ds, ctx)) =
                let val (assign', ctxd', ds') = check_decl (ctx, decl)
                    val ctxd = assign_ctx assign' ctxd
                    val ctx = assign_ctx assign' ctx
                    val assign = assign_assign assign' assign
                    val ctxd = add_ctx ctxd' ctxd
                    val ds = ds' @ map (shift_ctx_i ctxd') ds
                    val ctx = add_ctx ctxd' ctx
                in
                    (assign, ctxd, ds, ctx)
                end
        in
            foldl f (empty_assign, (([], []), [], [], []), [], ctx) decls
        end

    and check_decl (ctx as (sctx, kctx, cctx, _), decl) =
        case decl of
            Val (VarP (x, _), e) =>
            let 
                val skcctx = (sctx, kctx, cctx) 
                val (assign', t, d) = get_mtype (ctx, e)
                val ctx = assign_ctx assign' ctx
                val assign = assign_assign assign' assign
                val t = generalize (ctx, t, is_value e)
            in
                (assign, (([], []), [], [], [(x, t)]), [d])
            end
          | Val (pn, e) =>
            let 
                val skcctx = (sctx, kctx, cctx) 
                val (assign', t, d) = get_mtype (ctx, e)
                val ctx = assign_ctx assign' ctx
                val assign = assign_assign assign' assign
                val (assign', cover, ctxd) = match_ptrn (skcctx, pn, t)
                val t = assign_t assing' t
                val ctxd = assign_ctx assign' ctxd
                val ctx = assign_ctx assign' ctx
                val assign = assign_assign assign' assign
                val d = shift_ctx_i ctxd d
	        val () = check_exhaustive (skcctx, t, [cover], get_region_pn pn)
            in
                (assign, ctxd, [d])
            end
	  | Rec (t, (name, r), e) => 
	    let 
		val () = is_wf_mty (skctx, t)
                val () = check_fix_body e
		val (assign', t1, _) = get_mtype (add_typing_skct (name, Mono t) ctx, e)
                val t = assign_mt assign' t
                val assign = assign'
                val assign' = unify (t1, t)
                val t = assign_mt assign' t
                val assign = assign_assign assign' assign
                val t = generalize (ctx, t, true)
                val d = T0 dummy
            in
                (assign, (([], []), [], [], [(x, t)]), [d])
	    end
	  | Datatype (name, tnames, sorts, constr_decls, _) =>
	    let val () = is_wfsorts (sctx, sorts)
		val nk = (name, ArrowK (true, length tnames, sorts))
		val ctx as (sctx, kctx, _, _) = add_kinding_skct nk ctx
		fun make_constr ((name, ibinds, r) : constr_decl) =
		    let val c = (0, tnames, ibinds)
		        val t = constr_type c
		        val () = is_wftype ((sctx, kctx), t)
			         handle Error (_, msg) =>
				        raise Error (r, 
						     "Constructor is ill-formed" :: 
						     "Cause:" :: 
						     indent msg)
		    in
		        (name, c)
		    end
		val constrs = map make_constr constr_decls
	    in
		(empty_assign, (([], []), [nk], rev constrs, []), [])
	    end

    and check_rules (ctx as (sctx, kctx, cctx, tctx), rules, t as (t1, return), r) =
	let val skcctx = (sctx, kctx, cctx) 
	    fun f (rule, acc) =
	        let val ans as (td, cover) = check_rule (ctx, rule, t)
		    val () = check_redundancy (skcctx, Mono t1, (rev o map snd) acc, cover, get_region_rule rule)
	        in
		    (ans :: acc)
	        end 
	    val ans as (tds, covers) = (unzip o rev o foldl f []) rules
	in
	    check_exhaustive (skcctx, Mono t1, covers, r);
            tds
	end

    and check_rule (ctx as (sctx, kctx, cctx, tctx), (pn, e), t as (t1, return)) =
	let val skcctx = (sctx, kctx, cctx) 
	    val (cover, ctxd as (sctxd, kctxd, _, _)) = match_ptrn (skcctx, pn, Mono t1)
	    val ctx = add_ctx ctxd ctx
            val td = case return of
                         (SOME t, SOME d) =>
	                 (check_type_time (ctx, e, Mono (shift_ctx_mt ctxd t), shift_ctx_i ctxd d);
                          (t, d))
                       | (SOME t, NONE) =>
                         let val d = check_type (ctx, e, Mono (shift_ctx_mt ctxd t))
			     val d = forget_ctx_d (get_region_e e) ctx ctxd d
                         in
                             (t, d)
                         end
                       | (NONE, SOME d) =>
                         let val t = check_time_return_mty (ctx, e, shift_ctx_i ctxd d)
			     val t = forget_ctx_mt (get_region_e e) ctx ctxd t 
                         in
                             (t, d)
                         end
                       | (NONE, NONE) =>
                         let val (t, d) = get_mtype (ctx, e)
			     val t = forget_ctx_mt (get_region_e e) ctx ctxd t 
			     val d = forget_ctx_d (get_region_e e) ctx ctxd d
                         in
                             (t, d)
                         end
	in
	    (td, cover)
	end

in								     

fun vcgen_expr ctx e : (ty * idx) * vc list =
    runWriter (fn () => get_type (ctx, e)) ()
	      
fun vcgen_expr_opt ctx e =
    runError (fn () => vcgen_expr ctx e) ()
	     
fun vcgen_decls ctx decls =
    runWriter (fn () => check_decls (ctx, decls)) ()
	      
fun vcgen_expr_opt ctx decls =
    runError (fn () => vcgen_decls ctx decls) ()
	     
end

open TrivialSolver

fun typecheck_expr (ctx as (sctx, kctx, cctx, tctx) : context) e : (ty * idx) * vc list =
    let 
        val ((t, d), vcs) = vcgen_expr ctx e
        val t = simp_t t
        val d = simp_i d
        val vcs = map (uniquefy_names) vcs
        val vcs = simp_and_solve_vcs vcs
    in
        ((t, d), vcs)
    end

fun typecheck_expr_opt ctx e =
    runError (fn () => typecheck_expr ctx e) ()

type tc_result = (context * idx list * context) * vc list

fun typecheck_decls (ctx as (sctx, kctx, cctx, tctx) : context) decls : tc_result =
    let 
        val ((ctxd, ds, ctx), vcs) = vcgen_decls ctx decls
        val ctxd = (upd4 o map o mapSnd) simp_t ctxd
        val ds = rev ds
        val ds = map simp_i ds
        val vcs = map (uniquefy_names) vcs
        val vcs = simp_and_solve_vcs vcs
    in
        ((ctxd, ds, ctx), vcs)
    end

fun typecheck_decls_opt ctx e =
    runError (fn () => typecheck_decls ctx e) ()

end
			  
