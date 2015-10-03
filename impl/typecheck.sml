structure TypeCheck = struct
open ExprRegion
open Region
open Type
open Expr

infix 7 $
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
      | AppT _ => false
      | AbsI _ => true
      | AppI _ => false
      | Pack (_, _, e) => is_value e
      | Unpack _ => false
      | Fix _ => false
      | Let _ => false
      | Ascription _ => false
      | AscriptionTime _ => false
      | Plus _ => false
      | Const _ => true
      | AppConstr (_, _, _, e) => is_value e
      | Case _ => false
      | Never _ => false

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

(* a slightly different version where tctx is of ((string * (ty * idx)) list) *)
fun shiftx_i_tds n ctx = 
    map (mapSnd (fn (t, d) => (shiftx_i_t 0 n t, shiftx_i_i 0 n d))) ctx
fun shiftx_t_tds n ctx = 
    map (mapSnd (mapFst (shiftx_t_t 0 n))) ctx
fun add_sortings_skctd (pairs', ps') ((pairs, ps), kctx, cctx, tctx) = 
    let val n = length pairs' 
    in
	((pairs' @ pairs, ps' @ shiftx_i_ps n ps), 
	 shiftx_i_ks n kctx, 
	 shiftx_i_cs n cctx, 
	 shiftx_i_tds n tctx)
    end
fun add_kindings_skctd pairs (sctx, kctx, cctx, tctx) =
  let val n = length pairs in
      (sctx,
       pairs @ kctx,
       shiftx_t_cs n cctx,
       shiftx_t_tds n tctx)
  end
val add_constrs_skctd = add_constrs_skct
val add_typings_skctd = add_typings_skct

fun get_base s =
    case s of
	Basic (s, _) => s
      | Subset ((s, _), _, _) => s

type bscontext = (string * bsort) list

fun collect (pairs, ps) : bscontext * prop list = 
    let fun get_p s n ps =
	    case s of
		Basic _ => ps
	      | Subset (_, _, p) => shiftx_i_p 0 n p :: ps
	val bctx = map (mapSnd get_base) pairs
	val (ps', _) = foldl (fn ((name, s), (ps, n)) => (get_p s n ps, n + 1)) ([], 0) pairs
    in
	(bctx, ps @ ps')
    end

type vc = bscontext * prop list * prop

fun mem eq x ls = List.exists (fn y => eq (y, x)) ls
fun subset eq a b =
    List.all (fn x => mem eq x b) a
fun diff eq a b = List.filter (fn x => not (mem eq x b)) a

local
    fun find_unique name ls =
	if not (mem op= name ls) then
	    name
	else
	    let fun loop n =
		    let val name' = name ^ str_int n in
			if not (mem op= name' ls) then name' else loop (n + 1)
		    end in
		loop 0
	    end
in
fun unique names = foldr (fn (name, acc) => find_unique name acc :: acc) [] names
end

fun str_vc (ctx : bscontext, ps, p) =
    let val ctx = ListPair.zip (mapFst unique (ListPair.unzip ctx))
	val ctxn = map #1 ctx in
	sprintf "$$===============\n$\n" 
		[join "" (map (fn (name, s) => sprintf "$ : $\n" [name, str_b s]) (rev ctx)), 
		 join "" (map (fn p => str_p ctxn p ^ "\n") ps), 
		 str_p ctxn p]
    end 

(* exception Unimpl *)
exception Impossible of string

exception Error of region * string list
fun indent msg = map (fn s => "  " ^ s) msg

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
	(acc := []; let val r = m () in (r, !acc) end)

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

    fun is_le (ctx : scontext, d : idx, d' : idx) =
	let val (bctx, ps) = collect ctx in
	    tell (bctx, ps, d %<= d')
	end
	    
    fun is_eq (ctx : scontext, i : idx, i' : idx) = 
	let val (bctx, ps) = collect ctx in
	    tell (bctx, ps, Eq (i, i'))
	end

    fun is_eqs (ctx, is, is', r) =
	(check_length (is, is', r);
         app (fn (i, i') => is_eq (ctx, i, i')) (ListPair.zip (is, is')))
	    
    fun is_true (ctx : scontext, p : prop) = 
	let val (bctx, ps) = collect ctx in
	    tell (bctx, ps, p)
	end

    fun is_iff (ctx : scontext, p1 : prop, p2 : prop) = 
	let val (bctx, ps) = collect ctx in
	    tell (bctx, ps, p1 <-> p2)
	end

    fun is_eqvbsort_b s s' =
	case (s, s') of
	    (Time, Time) => true
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
	  | (Subset (s1, (name, _), p), Subset (s1', _, p')) =>
	    (is_eqvbsort (s1, s1');
	     is_iff (add_sorting (name, Basic s1) ctx, p, p'))
	  | (Subset (s1, (name, _), p), Basic s1') =>
	    (is_eqvbsort (s1, s1');
	     is_true (add_sorting (name, Basic s1) ctx, p))
	  | (Basic s1, Subset (s1', (name, _), p)) =>
	    (is_eqvbsort (s1, s1');
	     is_true (add_sorting (name, Basic s1) ctx, p))

    fun is_eqvsorts (ctx, sorts, sorts', r) =
	(check_length (sorts, sorts', r);
	 ListPair.app (fn (s, s') => is_eqvsort (ctx, s, s')) (sorts, sorts'))
	    
    fun sort_mismatch ctx i expect have =  "Sort mismatch for " ^ str_i ctx i ^ ": expect " ^ expect ^ " have " ^ str_s ctx have

    fun is_wfsort (ctx : scontext, s : sort) =
	case s of
	    Basic _ => ()
	  | Subset (s, (name, _), p) =>
	    is_wfprop (add_sorting (name, Basic s) ctx, p)

    and is_wfprop (ctx : scontext, p : prop) =
	case p of
	    True _ => ()
	  | False _ => ()
	  | And (p1, p2) =>
	    (is_wfprop (ctx, p1);
	     is_wfprop (ctx, p2))
	  | Or (p1, p2) =>
	    (is_wfprop (ctx, p1);
	     is_wfprop (ctx, p2))
	  | Imply (p1, p2) =>
	    (is_wfprop (ctx, p1);
	     is_wfprop (ctx, p2))
	  | Iff (p1, p2) =>
	    (is_wfprop (ctx, p1);
	     is_wfprop (ctx, p2))
	  | TimeLe (d1, d2) =>
	    (check_sort (ctx, d1, STime);
	     check_sort (ctx, d2, STime))
	  | Eq (i1, i2) =>
	    let val s1 = get_bsort (ctx, i1)
		val s2 = get_bsort (ctx, i2)
	    in
		if s1 = s2 then ()
		else raise Error (get_region_p p, [sprintf "Base-sorts not equal: $ and $" [str_b s1, str_b s2]])
	    end


    and check_sort (ctx, i, s) : unit =
	let val s' = get_bsort (ctx, i)
            val s' = (s', get_region_i i)
        in
	    case s of
		Subset (s1, _, p) =>
		(is_eqvbsort (s', s1);
		 is_true (ctx, subst_i_p i p))
	      | Basic s1 => 
		is_eqvbsort (s', s1)
	end
        handle Error (_, msg) => 
               let val ctxn = sctx_names ctx in
                   raise Error (get_region_i i, 
                                sprintf "index $ is not of sort $" [str_i ctxn i, str_s ctxn s] :: 
                                "Cause:" :: 
                                indent msg)
               end

    and get_bsort (ctx, i) =
	case i of
	    VarI (x, r) =>
	    (case lookup_sort x ctx of
      		 SOME s => get_base s
      	       | NONE => raise Error (r, ["Unbound index variable: " ^ str_v (sctx_names ctx) x]))
      	  | T0 _ => Time
	  | T1 _ => Time
	  | Tadd (d1, d2) => 
	    (check_bsort (ctx, d1, Time);
	     check_bsort (ctx, d2, Time);
	     Time)
	  | Tmult (d1, d2) => 
	    (check_bsort (ctx, d1, Time);
	     check_bsort (ctx, d2, Time);
	     Time)
	  | Tmax (d1, d2) => 
	    (check_bsort (ctx, d1, Time);
	     check_bsort (ctx, d2, Time);
	     Time)
	  | Tmin (d1, d2) => 
	    (check_bsort (ctx, d1, Time);
	     check_bsort (ctx, d2, Time);
	     Time)
	  | TrueI _ => Bool
	  | FalseI _ => Bool
	  | TTI _ => BSUnit
	  | Tconst (n, r) => 
	    if n >= 0 then
		Time
	    else
		raise Error (r, ["Time constant must be non-negative"])

    and check_bsort (ctx, i, s) : unit =
	is_eqvbsort ((get_bsort (ctx, i), get_region_i i), (s, dummy))

    fun is_wfsorts (ctx, s) = List.app (fn s => is_wfsort (ctx, s)) s

    fun check_sorts (ctx, is, sorts, r) =
	(check_length (is, sorts, r);
	 ListPair.app (fn (i, s) => check_sort (ctx, i, s)) (is, sorts))

    (* k => Type *)
    fun recur_kind k = ArrowK (0, k)

    fun kind_mismatch (ctx as (sctx, kctx)) c expect have =  "Kind mismatch for " ^ str_t ctx c ^ ": expect " ^ expect ^ " have " ^ str_k sctx have

    fun fetch_kind (kctx, (a, r)) =
	case lookup_kind a kctx of
      	    SOME k => k
      	  | NONE => raise Error (r, ["Unbound type variable: " ^ str_v (names kctx) a])

    fun is_wftype (ctx as (sctx : scontext, kctx : kcontext), c : ty) : unit = 
	let val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	(* val () = print (sprintf "Type wellformedness checking: $\n" [str_t ctxn c]) *)
	in
	    case c of
		Arrow (c1, d, c2) => 
		(is_wftype (ctx, c1);
		 check_sort (sctx, d, STime);
		 is_wftype (ctx, c2))
	      | Unit _ => ()
	      | Prod (c1, c2) => 
		(is_wftype (ctx, c1);
		 is_wftype (ctx, c2))
	      | Sum (c1, c2) => 
		(is_wftype (ctx, c1);
		 is_wftype (ctx, c2))
	      | Uni ((name, _), c) => 
		is_wftype (add_kinding_sk (name, Type) ctx, c)
	      | UniI (s, (name, _), c) => 
		(is_wfsort (sctx, s);
		 is_wftype (add_sorting_sk (name, s) ctx, c))
	      | ExI (s, (name, _), c) => 
		(is_wfsort (sctx, s);
		 is_wftype (add_sorting_sk (name, s) ctx, c))
	      | AppRecur (nameself, ns, t, is, r) =>
		let val sorts = List.map #2 ns in
		    is_wfsorts (sctx, sorts);
		    is_wftype (add_nondep_sortings_sk (rev ns) (add_kinding_sk (nameself, recur_kind sorts) ctx), t);
		    check_sorts (sctx, is, sorts, r)
		end
	      | AppV (x, ts, is, r) => 
		(case fetch_kind (kctx, x) of
		     ArrowK (n, sorts) => 
		     (check_length_n (n, ts, r);
		      check_sorts (sctx, is, sorts, r)))
	      | Int _ => ()
	end

    fun not_subtype ctx c c' = str_t ctx c ^ " is not subtype of " ^ str_t ctx c'

    (* is_subtype assumes that the types are already checked against the given kind, so it doesn't need to worry about their well-formedness *)
    fun is_subtype (ctx as (sctx : scontext, kctx : kcontext), c : ty, c' : ty) =
	let val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	(* val () = print (sprintf "Subtyping checking: \n$\n<:\n$\n" [str_t ctxn c, str_t ctxn c'])  *)
	in
	    case (c, c') of
		(Arrow (c1, d, c2), Arrow (c1', d', c2')) =>
		(is_subtype (ctx, c1', c1);
		 is_le (sctx, d, d');
		 is_subtype (ctx, c2, c2'))
	      | (Unit _, Unit _) => ()
	      | (Prod (c1, c2), Prod (c1', c2')) =>
		(is_subtype (ctx, c1, c1');
		 is_subtype (ctx, c2, c2'))
	      | (Sum (c1, c2), Sum (c1', c2')) => 
		(is_subtype (ctx, c1, c1');
		 is_subtype (ctx, c2, c2'))
	      | (Uni ((name, _), c), Uni (_, c')) => 
		is_subtype (add_kinding_sk (name, Type) ctx, c, c')
	      | (UniI (s, (name, _), c), UniI (s', _, c')) => 
		(is_eqvsort (sctx, s, s');
		 is_subtype (add_sorting_sk (name, s) ctx, c, c'))
	      | (ExI (s, (name, _), c), ExI (s', _, c')) => 
		(is_eqvsort (sctx, s, s');
		 is_subtype (add_sorting_sk (name, s) ctx, c, c'))
	      (* currently don't support subtyping for recursive types, so they must be equivalent *)
	      | (AppRecur (nameself, ns, t, is, r), AppRecur (_, ns', t', is', _)) => 
		let val sorts = List.map #2 ns
		    val sorts' = List.map #2 ns'
		    val () = is_eqvsorts (sctx, sorts, sorts', r)
		    val () = is_eqs (sctx, is, is', r)
		    val ctx' = add_nondep_sortings_sk (rev ns) (add_kinding_sk (nameself, recur_kind sorts) ctx) in
		    is_eqvtype (ctx', t, t')
		end
	      | (AppV ((a, r), ts, is, r2), AppV ((a', _), ts', is', _)) => 
		if a = a' then
		    (app (fn (t, t') => is_eqvtype (ctx, t, t')) (ListPair.zip (ts, ts'));
		     is_eqs (sctx, is, is', r2))
		else
		    raise Error (get_region_t c, [not_subtype ctxn c c'])
	      | (Int _, Int _) => ()
	      | _ => raise Error (get_region_t c, [not_subtype ctxn c c'])
	end

    and is_eqvtype (kctx, c, c') =
	(is_subtype (kctx, c, c');
	 is_subtype (kctx, c', c))

    fun no_join ctx c c' = "Cannot find a join (minimal supertype) of " ^ str_t ctx c ^ " and " ^ str_t ctx c'
    fun no_meet ctx c c' = "Cannot find a meet (maximal subtype) of " ^ str_t ctx c ^ " and " ^ str_t ctx c'

    (* c and c' are already checked for wellformedness *)
    fun join_type (ctx as (sctx : scontext, kctx : kcontext), c : ty, c' : ty) : ty = 
	let val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	in
	    case (c, c') of
		(Arrow (c1, d, c2), Arrow (c1', d', c2')) => 
		let val c1'' = meet (ctx, c1, c1') 
		    val d'' = d $ d' 
		    val c2'' = join_type (ctx, c2, c2') in
		    Arrow (c1'', d'', c2'')
		end
	      | (Unit r, Unit _) => Unit r
	      | (Prod (c1, c2), Prod (c1', c2')) => 
		let val c1'' = join_type (ctx, c1, c1') 
		    val c2'' = join_type (ctx, c2, c2') in
		    Prod (c1'', c2'')
		end
	      | (Sum (c1, c2), Sum (c1', c2')) => 
		let val c1'' = join_type (ctx, c1, c1') 
		    val c2'' = join_type (ctx, c2, c2') in
		    Sum (c1'', c2'')
		end
	      | (Uni ((name, r), t), Uni (_, t')) => 
		let val t'' = join_type (add_kinding_sk (name, Type) ctx, t, t') in
		    Uni ((name, r), t'')
		end
	      | (UniI (s, (name, r), t), UniI (s', _, t')) => 
		let val () = is_eqvsort (sctx, s, s')
		    val t'' = join_type (add_sorting_sk (name, s) ctx, t, t') in
		    UniI (s, (name, r), t'')
		end
	      | (ExI (s, (name, r), t), ExI (s', _, t')) => 
		let val () = is_eqvsort (#1 ctx, s, s')
		    val t'' = join_type (add_sorting_sk (name, s) ctx, t, t') in
		    ExI (s, (name, r), t'')
		end
	      (* currently don't support join for recursive types, so they must be equivalent *)
	      | (AppRecur _, AppRecur _) => 
		(is_eqvtype (ctx, c, c');
		 c)
	      | (AppV _, AppV _) => 
		(is_eqvtype (ctx, c, c');
		 c)
	      | (Int r, Int _) => Int r
	      | _ => raise Error (get_region_t c, [no_join ctxn c c'])
	end

    and meet (ctx as (sctx : scontext, kctx : kcontext), c : ty, c' : ty) : ty = 
	let val ctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	in
	    case (c, c') of
		(Arrow (c1, d, c2), Arrow (c1', d', c2')) => 
		let val c1'' = join_type (ctx, c1, c1') 
		    val d'' = Tmin (d, d')
		    val c2'' = meet (ctx, c2, c2') in
		    Arrow (c1'', d'', c2'')
		end
	      | (Unit r, Unit _) => Unit r
	      | (Prod (c1, c2), Prod (c1', c2')) => 
		let val c1'' = meet (ctx, c1, c1') 
		    val c2'' = meet (ctx, c2, c2') in
		    Prod (c1'', c2'')
		end
	      | (Sum (c1, c2), Sum (c1', c2')) => 
		let val c1'' = meet (ctx, c1, c1') 
		    val c2'' = meet (ctx, c2, c2') in
		    Sum (c1'', c2'')
		end
	      | (Uni ((name, r), t), Uni (_, t')) => 
		let val t'' = meet (add_kinding_sk (name, Type) ctx, t, t') in
		    Uni ((name, r), t'')
		end
	      | (UniI (s, (name, r), t), UniI (s', _, t')) => 
		let val () = is_eqvsort (sctx, s, s')
		    val t'' = meet (add_sorting_sk (name, s) ctx, t, t') in
		    UniI (s, (name, r), t'')
		end
	      | (ExI (s, (name, r), t), ExI (s', _, t')) => 
		let val () = is_eqvsort (#1 ctx, s, s')
		    val t'' = meet (add_sorting_sk (name, s) ctx, t, t') in
		    ExI (s, (name, r), t'')
		end
	      (* currently don't support meet for recursive types, so they must be equivalent *)
	      | (AppRecur _, AppRecur _) => 
		(is_eqvtype (ctx, c, c');
		 c)
	      | (AppV _, AppV _) => 
		(is_eqvtype (ctx, c, c');
		 c)
	      | (Int r, Int _) => Int r
	      | _ => raise Error (get_region_t c, [no_meet ctxn c c'])
	end

    type cover = var list
    val Cover_False = []
    fun Cover_Or (a, b) = a @ b
    fun Cover_Constr e = [e]

    fun get_family ((x, _, _, _, _) : constr) = x

    fun get_family_members cctx x =
	List.mapPartial (fn (n, (_, c)) => if get_family c = x then SOME n else NONE) (add_idx cctx)

    (* covers should already have type t *)
    fun check_redundancy ((_, _, cctx), t, prev, this, r) =
	if not (subset op= this prev) then ()
	else raise Error (r, [sprintf "Redundant pattern $ after [$]" [join ", " (map (str_v (names cctx)) this), join ", " (map (str_v (names cctx)) prev)]])

    fun check_exhaustive ((_, _, cctx), t, cover, r) =
	case t of
	    AppV ((family, _), _, _, _) =>
	    let val all = get_family_members cctx family
		val missed = diff op= all cover
	    in
		if missed = [] then ()
		else raise Error (r, [sprintf "Not exhaustive, missing these constructors: $" [join ", " (map (str_v (names cctx)) missed)]])
	    end
	  | _ => raise Impossible "shouldn't check exhaustiveness under this type"

    fun fetch_constr (ctx, (x, r)) =
	case nth_error ctx x of
	    SOME (name, c) => (name, c)
	  | NONE => raise Error (r, [sprintf "Unbound constructor: $" [str_v (names ctx) x]])

    fun constr_type ((family, tnames, ns, t, is) : constr) = 
      let val ts = (map (fn x => VarT (x, dummy)) o rev o range o length) tnames
	  val t2 = AppV ((shiftx_v 0 (length tnames) family, dummy), ts, is, dummy)
	  val t = Arrow (t, T0 dummy, t2)
	  val t = foldr (fn ((name, s), t) => UniI (s, (name, dummy), t)) t ns
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

    (* t is already checked for wellformedness *)
    fun match_ptrn (ctx as (sctx : scontext, kctx : kcontext, cctx : ccontext), pn : ptrn, t) : scontext * (string * ty) * cover =
	let val skctxn as (sctxn, kctxn) = (sctx_names sctx, names kctx)
	in
	    case (pn, t) of
		(Constr ((cx, r), inames, (ename, _)), AppV ((x, _), ts, is, _)) =>
		let val (_, c as (x', tnames, ns, t1, is')) = fetch_constr (cctx, (cx, r))
		in
		    if x' = x then
			let val () = check_length (tnames, ts, r)
			    val t1 = subst_ts_t ts t1
			    val is = map (shiftx_i_i 0 (length ns)) is
			    val () = check_length (is', is, r)
			    val ps = map Eq (ListPair.zip (is', is))
			    val () = check_length (inames, ns, get_region_pn pn)
			in
			    ((rev (ListPair.zip (inames, #2 (ListPair.unzip ns))), ps), (ename, t1), Cover_Constr cx)
			end
		    else
			raise Error 
                              (r, sprintf "Type of constructor $ doesn't match datatype:" [str_v (names cctx) cx] :: 
                                  indent ["expect: " ^ str_v kctxn x, 
                                          "got: " ^ str_v kctxn x'])
		end
	      | _ => raise Error (get_region_pn pn, [sprintf "Pattern $ doesn't match type $" [str_pn (names cctx) pn, str_t skctxn t]])
	end

    fun mismatch (ctx as (sctx, kctx, _, _)) e expect got =  
        (get_region_e e,
	 "Type-mismatch:" ::
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

    fun get_type (ctx as (sctx : scontext, kctx : kcontext, cctx : ccontext, tctx : tcontext), e : expr) : ty * idx =
	let val skctx = (sctx, kctx) 
	    val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
	    val skctxn = (sctxn, kctxn)
	    (* val () = print (sprintf "Typing $\n" [str_e ctxn e]) *)
	    val (t, d) =
		case e of
		    Var (x, r) =>
		    (case lookup x tctx of
      			 SOME t => (t, T0 dummy)
      		       | NONE => raise Error (r, ["Unbound variable: " ^ str_v tctxn x]))
		  | App (e1, e2) =>
		    let val (t1, d1) = get_type (ctx, e1) in
    			case t1 of
    			    Arrow (t2, d, t) =>
    			    let val d2 = check_type (ctx, e2, t2) 
                            in
    				(t, d1 %+ d2 %+ T1 dummy %+ d) 
			    end
    			  | t1' =>  raise Error (mismatch ctxn e1 "(_ -- _ -> _)" t1')
		    end
		  | Abs (t, (varname, _), e) => 
		    let val () = is_wftype (skctx, t)
			val (t1, d) = get_type (add_typing_skct (varname, t) ctx, e) in
			(Arrow (t, d, t1), T0 dummy)
		    end
		  | TT _ => (Unit dummy, T0 dummy)
		  | Pair (e1, e2) => 
		    let val (t1, d1) = get_type (ctx, e1) 
			val (t2, d2) = get_type (ctx, e2) in
			(Prod (t1, t2), d1 %+ d2)
		    end
		  | Fst e => 
		    let val (t, d) = get_type (ctx, e) in 
			case t of
			    Prod (t1, t2) => (t1, d)
			  | t' => raise Error (mismatch ctxn e "(_ * _)" t')
		    end
		  | Snd e => 
		    let val (t, d) = get_type (ctx, e) in 
			case t of
			    Prod (t1, t2) => (t2, d)
			  | t' => raise Error (mismatch ctxn e "(_ * _)" t')
		    end
		  | Inl (t2, e) => 
		    let val (t1, d) = get_type (ctx, e)
			val () = is_wftype (skctx, t2) in
			(Sum (t1, t2), d)
		    end
		  | Inr (t1, e) => 
		    let val (t2, d) = get_type (ctx, e)
			val () = is_wftype (skctx, t1) in
			(Sum (t1, t2), d)
		    end
		  | SumCase (e, name1, e1, name2, e2) => 
		    let val (t, d) = get_type (ctx, e) in
			case t of
			    Sum (t1, t2) => 
			    let val (tr1, d1) = get_type (add_typing_skct (name1, t1) ctx, e1)
				val (tr2, d2) = get_type (add_typing_skct (name2, t2) ctx, e2)
				val tr = join_type (skctx, tr1, tr2) in
				(tr, d %+ d1 $ d2)
			    end
			  | t' => raise Error (mismatch ctxn e "(_ + _)" t')
		    end
		  | AbsT ((name, _), e) => 
		    if is_value e then
			let val (t, _) = get_type (add_kinding_skct (name, Type) ctx, e) in
			    (Uni ((name, dummy), t), T0 dummy)
			end 
		    else
			raise Error (get_region_e e, ["The body of a universal abstraction must be a value"])
		  | AppT (e, c) =>
		    let val (t, d) = get_type (ctx, e) in
			case t of
			    Uni (_, t1) => 
			    let val () = is_wftype (skctx, c) in
				(subst_t_t c t1, d)
			    end
			  | t' => raise Error (mismatch ctxn e "(forall _ : _, _)" t')
		    end
		  | AbsI (s, (name, r), e) => 
		    if is_value e then
			let val () = is_wfsort (sctx, s)
			    val (t, _) = get_type ((add_sorting_skct (name, s) ctx), e) in
			    (UniI (s, (name, dummy), t), T0 dummy)
			end 
		    else
			raise Error (get_region_e e, ["The body of a universal abstraction must be a value"])
		  | AppI (e, i) =>
		    let val (t, d) = get_type (ctx, e) in
			case t of
			    UniI (s, _, t1) => 
			    let val () = check_sort (sctx, i, s) in
				(subst_i_t i t1, d)
			    end
			  | t' => raise Error (mismatch ctxn e "(forallI _ : _, _)" t')
		    end
		  | Fold (t, e) => 
		    (case t of
			 AppRecur t1 =>
			 let val () = is_wftype (skctx, t)
			     val (t', d) = get_type (ctx, e)
			     val () = is_subtype (skctx, t', unroll t1) in
			     (t, d)
			 end
		       | t' => raise Error (mismatch_anno skctxn "((recur (_ :: _) (_ : _), _) _)" t'))
		  | Unfold e =>
		    let val (t, d) = get_type (ctx, e) in
			case t of
	      		    AppRecur t1 =>
			    (unroll t1, d)
			  | t' => raise Error (mismatch ctxn e "((recur (_ :: _) (_ : _), _) _)" t')
		    end
		  | Pack (t, i, e) =>
		    (case t of
			 ExI (s, _, t1) =>
			 let val () = is_wftype (skctx, t)
			     val () = check_sort (sctx, i, s)
			     val (t2, d) = get_type (ctx, e)
			     val () = is_subtype (skctx, t2, (subst_i_t i t1)) in
			     (t, d)
			 end
		       | t' => raise Error (mismatch_anno skctxn "(ex _ : _, _)" t'))
		  | Unpack (e1, t, d, idx_var, expr_var, e2) => 
		    let val () = is_wftype (skctx, t)
			val () = check_sort (sctx, d, STime)
			val (t1, d1) = get_type (ctx, e1) in
			case t1 of
			    ExI (s, _, t1') => 
			    let val ctx' = add_typing_skct (expr_var, t1') (add_sorting_skct (idx_var, s) ctx)
				val () = check_type_time (ctx', e2, shift_i_t t, shift_i_i d)
			    in
				(t, d1 %+ d)
			    end
			  | t1' => raise Error (mismatch ctxn e1 "(ex _ : _, _)" t1')
		    end
		  | Fix (t, (name, r), e) => 
		    let val () = check_fix_body e
			val () = is_wftype (skctx, t)
			val (t1, _) = get_type (add_typing_skct (name, t) ctx, e)
			val () = is_subtype (skctx, t1, t) in
			(t, T0 dummy)
		    end
		  | Ascription (e, t) => 
		    let val () = is_wftype (skctx, t)
			val (t1, d) = get_type (ctx, e)
			val () = is_subtype (skctx, t1, t) in
			(t, d)
		    end
		  | AscriptionTime (e, d) => 
		    let val () = check_sort (sctx, d, STime)
			val (t, d1) = get_type (ctx, e)
			val () = is_le (sctx, d1, d) in
			(t, d)
		    end
		  | Plus (e1, e2) =>
		    let val (t1, d1) = get_type (ctx, e1)
			val (t2, d2) = get_type (ctx, e2) in
			is_subtype (skctx, t1, Int dummy);
			is_subtype (skctx, t2, Int dummy);
			(Int dummy, d1 %+ d2 %+ T1 dummy)
		    end
		  | Const _ => 
		    (Int dummy, T0 dummy)
		  | AppConstr (cx, ts, is, e) => 
		    let val (cname, tc) = fetch_constr_type (cctx, cx)
			val () = is_wftype (skctx, tc)
			val (_, d) = get_type (ctx, e)
			(* delegate to checking e' *)
			val f = Var (0, dummy)
			val f = foldl (fn (t, e) => AppT (e, t)) f ts
			val f = foldl (fn (i, e) => AppI (e, i)) f is
			val e' = App (f, shift_e_e e)
			val (t, _) = get_type (add_typing_skct (cname, tc) ctx, e') 
		    in
			(* constructor application doesn't incur count *)
			(t, d)
		    end
		  | Case (e, t, d, rules, _) => 
		    let val () = is_wftype (skctx, t)
			val () = check_sort (sctx, d, STime)
			val (t1, d1) = get_type (ctx, e)
		    in
			check_rules (ctx, rules, (t1, d, t));
			(t, d1 %+ d)
		    end
		  | Never t => 
		    (is_wftype (skctx, t);
		     is_true (sctx, False dummy);
		     (t, T0 dummy))
		  (* | Let (e1, name, e2, _) =>  *)
		  (*   let val (t1, d1) = get_type (ctx, e1) *)
		  (*       val (t2, d2) = get_type (add_typing_skct (name, t1) ctx, e2) in *)
		  (*       (t2, d1 %+ d2) *)
		  (*   end *)
		  | Let (decs, e, r) => 
		    let val (ctxd, ctx) = check_decs (ctx, decs)
	                val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
			val (t, d) = get_type (ctx, e)
			val t = forget_t r (sctxn, kctxn) ctxd t 
                        val ds = get_ds ctxd
                        val ds = map (forget_d r sctxn ctxd) ds
			val d = forget_d r sctxn ctxd d
                    in
			(t, foldl (fn (d, acc) => acc %+ d) (T0 dummy) ds %+ d)
		    end
	(* val () = print (sprintf "  type: $ [for $]\n  time: $\n" [str_t skctxn t, str_e ctxn e, str_i sctxn d]) *)
	in
	    (t, d)
	end

    and check_dec (ctx as (sctx, kctx, _, _), dec) =
        case dec of
            Val ((name, _), e) =>
            let val (t, d) = get_type (ctx, e)
            in
                (([], []), [], [], [(name, (t, d))])
            end
	  | Datatype (name, tnames, sorts, constr_decs, _) =>
	    let val () = is_wfsorts (sctx, sorts)
		val nk = (name, ArrowK (length tnames, sorts))
		val ctx = add_kinding_skct nk ctx
		fun make_constr (name, name_sorts, t, ids, r) =
		  let val c = (0, tnames, name_sorts, t, ids)
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
		val constrs = map make_constr constr_decs
	    in
		(([], []), [nk], rev constrs, [])
	    end

    and check_decs (ctx, decs) = 
        let fun f (dec, (ctxd, ctx)) =
                let val ctxd' = check_dec (ctx, dec)
                    val ctx = add_ctxd_ctx ctxd' ctx
                    val ctxd = add_ctxd ctxd' ctxd
                in
                    (ctxd, ctx)
                end
        in
            foldl f ((([], []), [], [], []), ctx) decs
        end

    and get_ds (_, _, _, tctxd) = map (#2 o #2) tctxd

    (* placeholders *)
    and add_ctx (sctx, kctx, cctx, tctx) ctx =
	let val ctx = add_sortings_skct sctx ctx
	    val ctx = add_kindings_skct kctx ctx
	    val ctx = add_constrs_skct cctx ctx
	    val ctx = add_typings_skct tctx ctx
	in
	    ctx
	end

    and add_ctxd (sctx, kctx, cctx, tctx) ctx =
	let val ctx = add_sortings_skctd sctx ctx
	    val ctx = add_kindings_skctd kctx ctx
	    val ctx = add_constrs_skctd cctx ctx
	    val ctx = add_typings_skctd tctx ctx
	in
	    ctx
	end

    and add_ctxd_ctx (sctx, kctx, cctx, tctx) ctx =
	add_ctx (sctx, kctx, cctx, map (mapSnd #1) tctx) ctx

    and escapes nametype name domaintype domain =
	[sprintf "$ $ escapes local scope in $ $" [nametype, name, domaintype, domain]]
	    
    and forget_t r (skctxn as (sctxn, kctxn)) (sctxd, kctxd, _, _) t = 
        let val t = forget_t_t 0 (length kctxd) t
		    handle ForgetError x => raise Error (r, escapes "type variable" (str_v kctxn x) "type" (str_t skctxn t))
	    val t = forget_i_t 0 (length sctxd) t
		    handle ForgetError x => raise Error (r, escapes "index variable" (str_v sctxn x) "type" (str_t skctxn t))
	in
	    t
	end

    and forget_d r sctxn (sctxd, _, _, _) d =
	forget_i_i 0 (length sctxd) d
        handle ForgetError x => raise Error (r, escapes "index variable" (str_v sctxn x) "time" (str_i sctxn d))

    and check_type (ctx as (sctx, kctx, cctx, tctx), e, t) =
	let 
	    val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
	    (* val () = print (sprintf "Type checking $ against $ and $\n" [str_e ctxn e, str_t (sctxn, kctxn) t, str_i sctxn d]) *)
	    val (t', d') = get_type (ctx, e)
	in
	    is_subtype ((sctx, kctx), t', t)
            handle Error (_, msg) =>
                   raise Error (get_region_e e, 
                                #2 (mismatch ctxn e (str_t (sctxn, kctxn) t) t') @
                                "Cause:" ::
                                indent msg);
            d'
	end

    and check_type_time (ctx as (sctx, kctx, cctx, tctx), e, t, d) =
	let 
	    val d' = check_type (ctx, e, t)
	in
	    is_le (sctx, d', d)
	end

    and check_rules (ctx as (sctx, kctx, cctx, tctx), rules, t as (t1, _, _)) =
	let val skcctx = (sctx, kctx, cctx) 
	    fun f (rule, acc) =
		let val cover = check_rule (ctx, rule, t)
		    val () = check_redundancy (skcctx, t1, acc, cover, get_region_rule rule)
		in
		    Cover_Or (cover, acc)
		end 
	    val cover = foldl f Cover_False rules
	in
	    check_exhaustive (skcctx, t1, cover, get_region_t t1)
	end

    and check_rule (ctx as (sctx, kctx, cctx, tctx), (pn, e), t as (t1, d, t2)) =
	let val skcctx = (sctx, kctx, cctx) 
	    val (sctx', nt, cover) = match_ptrn (skcctx, pn, t1)
	    val ctx' = add_typing_skct nt (add_sortings_skct sctx' ctx)
	in
	    check_type_time (ctx', e, shift_pn_t pn t2, shift_pn_i pn d);
	    cover
	end

in								     

fun vcgen ctx e : (ty * idx) * vc list =
    runWriter (fn () => get_type (ctx, e)) ()
	     
fun vcgen_opt ctx e =
    runError (fn () => vcgen ctx e) ()
	     
end

open TrivialSolver

fun typecheck (ctx as (sctx, kctx, cctx, tctx) : context) e : (ty * idx) * vc list =
    let 
	val ctxn as (sctxn, kctxn, cctxn, tctxn) = ctx_names ctx
	val ((t, d), vcs) = vcgen ctx e
	(* val () = print "Simplifying and applying trivial solver ...\n" *)
	val vcs = trivial_solver vcs
	val vcs = map simplify vcs
	val vcs = trivial_solver vcs
	val t = simp_t t
	val d = simp_i d
    in
        ((t, d), vcs)
    end

fun typecheck_opt ctx e =
    runError (fn () => typecheck ctx e) ()

end
			  
