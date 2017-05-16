(* common utilities for typechecking *)

structure TypecheckUtil = struct
open Gctx
open Region
open Util
open Expr
open Subst
open Package
open List
       
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
        
exception Error of region * string list

type kind_ext = bool (*is datatype*) * kind * mtype option (*aliasing*)

fun str_ke gctx (ctx as (sctx, kctx)) (dt, k, t) =
  if not dt andalso isNone t then str_k k
  else
    sprintf "($$$)" [str_k k, if dt then " [datatype]" else "", str_opt (fn t => sprintf " (= $)" [str_mt gctx ctx t]) t]
                                 
(* sorting context *)
type scontext = (string (* option *) * sort) list
(* kinding context *)
type kcontext = (string * kind_ext) list 
(* constructor context *)
type ccontext = (string * constr) list
(* typing context *)
type tcontext = (string * ty) list
type context = scontext * kcontext * ccontext * tcontext

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

fun is_FunctorBind s =
  case s of
      FunctorBind a => SOME a
    | _ => NONE

(* type sigcontext = (string * sgntr) list *)
type sigcontext = sgntr Gctx.map
                                   
fun names ctx = map fst ctx

fun shiftx_i_ke x n (dt, k, t) = (dt, k, Option.map (shiftx_i_mt x n) t)
                                  
fun shiftx_t_ke x n (dt, k, t) = (dt, k, Option.map (shiftx_t_mt x n) t)
                                  
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

fun add_sgn (name, s) gctx =
  let
    val () = if isNone $ Gctx.find (gctx, name) then ()
             else raise Error (dummy, [sprintf "module name $ already exists in module context $" [name, str_ls id $ domain gctx]])
  in
    insert' ((name, s), gctx)
  end
    
fun add_sigging (name, s) pairs = add_sgn (name, Sig s) pairs
                                                     
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

(* fetching from context *)
                                   
fun package_i_ke x v (dt, k, t) = (dt, k, Option.map (package_i_mt x v) t)
                                  
fun package_t_ke x v (dt, k, t) = (dt, k, Option.map (package_t_mt x v) t)

fun package0_ke v (b : kind_ext) =
  package_t_ke 0 v $ package_i_ke 0 v b
               
fun pacakge_is_mt vs b =
  fst (foldl (fn (v, (b, x)) => (package_i_mt x v b, x - 1)) (b, length vs - 1) vs)
fun package_ts_mt vs b =
  fst (foldl (fn (v, (b, x)) => (package_t_mt x v b, x - 1)) (b, length vs - 1) vs)

fun package0_sctx m sctx =
  foldrWithIdx 0 (fn ((name, s), acc, x) => (name, package_i_s x m s) :: acc) [] sctx

fun package0_kctx m sctx_len kctx =
  foldrWithIdx 0 (fn ((name, k), acc, x) => (name, package_i_ke sctx_len m $ package_t_ke x m k) :: acc) [] kctx
               
fun package0_ctx m (sctx, kctx, cctx, tctx) =
  let
    val sctx = package0_sctx m sctx
    val sctx_len = length sctx
    val kctx = package0_kctx m sctx_len kctx
    val kctx_len = length kctx
    val cctx = map (fn (name, c) => (name, package_t_c kctx_len m $ package_i_c sctx_len m c)) cctx
    val tctx = map (fn (name, t) => (name, package_t_t kctx_len m $ package_i_t sctx_len m t)) tctx
  in
    (sctx, kctx, cctx, tctx)
  end
    
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
             
(* val lookup_constr = lookup_snd *)
fun lookup_constr n ctx = nth_error ctx n
val lookup_type = lookup_snd

val get_outmost_module = id

fun filter_module gctx = Gctx.mapPartial (fn sg => case sg of Sig sg => SOME sg | _ => NONE) gctx
                                         
fun gctx_names (gctx : sigcontext) =
  let
    val gctx = filter_module gctx
    val gctx = Gctx.map ctx_names gctx
  in
    gctx
  end

fun lookup_module gctx m =
  Option.map snd $ nth_error2 (filter_module gctx) m

fun fetch_module gctx (m, r) =
  case lookup_module gctx m of
      SOME sg => sg
    | NONE => raise Error (r, ["Unbounded module"])
                    
fun fetch_from_module (params as (package, do_fetch)) (* sigs *) gctx ((m, mr) : mod_projectible, x) =
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
    val v = package (m, mr) v
  in
    v
  end
    
fun add_error_msg (r, old_msg) new_msg =
  (r, new_msg @ ["Cause:"] @ indent old_msg)
    
fun generic_fetch package do_fetch sel (ggctx as ((* sigs,  *)gctx : sigcontext)) (fctx, (m, x)) =
  case m of
      NONE => do_fetch (fctx, x)
    | SOME m => fetch_from_module (package, do_fetch o mapFst sel) (* sigs *) gctx (m, x)

fun do_fetch_sort (ctx, (x, r)) =
  case lookup_sort x ctx of
      SOME s => s
    | NONE => raise Error (r, ["Unbound index variable: " ^ str_v (sctx_names ctx) x])

fun fetch_sort a = generic_fetch package0_s do_fetch_sort #1 a
                                 
fun do_fetch_sort_by_name (ctx, (name, r)) =
  case lookup_sort_by_name ctx name of
      SOME (i, s) => ((i, r), s)
    | NONE => raise Error (r, [sprintf "Can't find index variable '$' in context $" [name, str_ls fst ctx]])

fun package0_snd f m (a, b) = (a, f m b)
fun package0_list f m ls = map (f m) ls
                               
fun fetch_sort_by_name gctx ctx (m, name) =
  let
    val (x, s) = generic_fetch (package0_snd package0_s) do_fetch_sort_by_name #1 gctx (ctx, (m, name))
  in
    ((m, x), s)
  end
    
fun do_fetch_kindext (kctx, (a, r)) =
  case lookup_kindext a kctx of
      SOME k => k
    | NONE => raise Error (r, [sprintf "Unbound type variable $ in context $" [str_v (names kctx) a, str_ls id $ names kctx]])

fun fetch_kindext gctx (kctx, x) =
  generic_fetch package0_ke do_fetch_kindext #2 gctx (kctx, x)
  handle Error e => raise Error $ add_error_msg e [sprintf "Unbound name '$' in type context $ and module context $" [str_long_id #2 (gctx_names gctx) (names kctx) x, str_ls fst kctx, str_ls id $ domain gctx]]

(* fun do_fetch_kind (kctx, (a, r)) = *)
(*     case lookup_kind a kctx of *)
(*       	SOME k => k *)
(*       | NONE => raise Error (r, [sprintf "Unbound type variable $ in context $" [str_v (names kctx) a, str_ls id $ names kctx]]) *)

(* fun fetch_kind a = generic_fetch shiftx_m_k package0_kind do_fetch_kind #2 a *)
fun fetch_kind gctx (kctx, x) = get_ke_kind $ fetch_kindext gctx (kctx, x)
                                            
fun fetch_is_datatype gctx (kctx, x) =
  let
    val (dt, _, _) = fetch_kindext gctx (kctx, x)
  in
    dt
  end

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
    val (x, k) = generic_fetch (package0_snd package0_ke) do_fetch_kindext_by_name #2 gctx (ctx, (m, name))
  in
    ((m, x), k)
  end
    
fun do_fetch_constr (ctx, (x, r)) =
  case lookup_constr x ctx of
      SOME c => c
    | NONE => raise Error (r, [sprintf "Unbound constructor $ in context $" [str_v (names ctx) x, str_ls fst ctx]])

fun fetch_constr a = generic_fetch (package0_snd package0_c) do_fetch_constr #3 a
                                   
fun fetch_constr_type gctx (ctx : ccontext, x) =
  constr_type VarT shiftx_long_id $ snd $ fetch_constr gctx (ctx, x)

fun do_fetch_constr_by_name (ctx, (name, r)) =
  case find_idx_value name ctx of
      SOME (i, c) => ((i, r), c)
    | NONE => raise Error (r, ["Can't find constructor: " ^ name])

fun fetch_constr_by_name gctx ctx (m, name) =
  let
    val (x, c) = generic_fetch (package0_snd package0_c) do_fetch_constr_by_name #3 gctx (ctx, (m, name))
  in
    ((m, x), c)
  end
    
fun fetch_constr_type_by_name gctx ctx name =
  mapSnd (constr_type VarT shiftx_long_id) $ fetch_constr_by_name gctx ctx name

fun do_fetch_type (tctx, (x, r)) =
  case lookup_type x tctx of
      SOME t => t
    | NONE => raise Error (r, ["Unbound variable: " ^ str_v (names tctx) x])

fun fetch_type a = generic_fetch package0_t do_fetch_type #4 a

fun do_fetch_type_by_name (ctx, (name, r)) =
  case find_idx_value name ctx of
      SOME (i, t) => ((i, r), t)
    | NONE => raise Error (r, ["Can't find variable: " ^ name])

fun fetch_type_by_name gctx ctx (m, name) =
  let
    val (x, t) = generic_fetch (package0_snd package0_t) do_fetch_type_by_name #4 gctx (ctx, (m, name))
  in
    ((m, x), t)
  end
    
fun try_retrieve_MtVar f gctx kctx x =
  let
    val k = fetch_kindext gctx (kctx, x)
  in
    default (MtVar x) $ Option.map f (#3 k)
  end

(* verification conditions written incrementally during typechecking *)
                                     
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
    (* val () = println $ "Writing Prop: " ^ str_p empty [] p *)
  in
    write (PropVC (p, r))
  end

infixr 0 @@
         
fun write_admit (p, r) =
  (* (println $ "writing admit") @@ *)
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

end
