structure UVarUtil = struct
open Util
       
datatype ('a, 'b) uvar = 
         Fresh of 'a
         | Refined of 'b

(* invisible segments *)
type invisibles = (int * int) list

type 'bsort uname_i = int * string list (*ctx*) * 'bsort
type ('bsort, 'idx) uvar_ref_i = (('bsort uname_i, 'idx) uvar) ref
type ('bsort, 'idx) uvar_i = invisibles * ('bsort, 'idx) uvar_ref_i

type uname_bs = int
type 'bsort uvar_bs = ((uname_bs, 'bsort) uvar) ref
                                                
type uname_nonidx = int * string list (*ctx*)
type 't uvar_ref_nonidx = ((uname_nonidx, 't) uvar) ref
                                                    
type 'sort uvar_s = invisibles * 'sort uvar_ref_nonidx

type 'mtype uvar_mt = (invisibles (* sortings *) * invisibles (* kindings *)) * 'mtype uvar_ref_nonidx

fun expand shift invis b = 
  (fst o foldl (fn ((off, len), (b, base)) => (shift (base + off) len b, base + off + len)) (b, 0)) invis
fun shrink forget invis b = 
  (fst o foldl (fn ((off, len), (b, base)) => (forget (base + off) len b, base + off)) (b, 0)) invis
fun shrink_ctx invis ctx = shrink skip invis ctx

fun refine (x : (('a, 'b) uvar) ref) (v : 'b) = 
  case !x of
      Refined _ => raise Impossible "refine(): should only refine Fresh uvar"
    | Fresh _ =>
      x := Refined v

fun str_uvar n = "?" ^ str_int n

fun str_uname_i (n, ctx, _) = str_uvar n
fun str_uname_bs n = str_uvar n
fun str_uname_nonidx (n, ctx) = str_uvar n
                                         
fun str_uname_bs n = str_uvar n
(* fun str_uname_i (n, ctx, _) = sprintf "($ $)" [str_uvar n, str_ls id (rev ctx)] *)
(* fun str_uname_nonidx (n, ctx) = sprintf "($ $)" [str_uvar n, str_ls id (rev ctx)] *)
fun str_uname_i (n, ctx, _) = str_uvar n
fun str_uname_nonidx (n, ctx) = str_uvar n
                                         
fun str_uvar_i str_i ctx ((invis, u) : ('bsort, 'idx) uvar_i) =
  case !u of
      Refined i => str_i (shrink_ctx invis ctx) i
    (* | Fresh name => str_uname_i name *)
    | Fresh name => sprintf "($ $)" [str_uname_i name, str_ls (str_pair (str_int, str_int)) invis]

fun str_uvar_s str_s ctx ((invis, u) : 'sort uvar_s) =
  case !u of
      Refined s => str_s (shrink_ctx invis ctx) s
    (* | Fresh name => str_uname_i name *)
    | Fresh name => sprintf "($ $)" [str_uname_nonidx name, str_ls (str_pair (str_int, str_int)) invis]

fun str_uvar_bs str_bs (u : 'bsort uvar_bs) =
  case !u of
      Refined bs => str_bs bs
    | Fresh name => str_uname_bs name
                                 
fun str_uvar_mt str_mt (ctx as (sctx, kctx)) ((invis as (invisi, invist), u) : 'mtype uvar_mt) =
  case !u of
      Refined t => str_mt (shrink_ctx invisi sctx, shrink_ctx invist kctx) t
    (* | Fresh name => str_uname_nonidx name *)
    | Fresh name => sprintf "($ $ $)" [str_uname_nonidx name, str_ls (str_pair (str_int, str_int)) invisi, str_ls (str_pair (str_int, str_int)) invist]
                            
fun eq_uvar_i ((_, u) : ('bsort, 'idx) uvar_i, (_, u') : ('bsort, 'idx) uvar_i) = u = u'
                                                                                        
end
                       
structure UVar = struct
open UVarUtil
open Util
       
infixr 0 $
         
(* for reporting error *)
datatype ('bsort, 'idx, 'sort, 'mtype) fresh_uvar_ref =
         FrIdx of ('bsort, 'idx) uvar_ref_i * 'bsort uname_i
         | FrBsort of 'bsort uvar_bs * uname_bs
         | FrSort of 'sort uvar_ref_nonidx * uname_nonidx
         | FrMtype of 'mtype uvar_ref_nonidx * uname_nonidx

fun on_UVarI on_invis expand_i UVarI f x n ((invis, uvar_ref), r) =
  case !uvar_ref of
      Refined i => 
      f x n (expand_i invis i)
    | Fresh uname => 
      UVarI ((on_invis (FrIdx (uvar_ref, uname)) x n invis, uvar_ref), r)

fun on_UVarS on_invis expand_s UVarS f x n ((invis, uvar_ref), r) =
  case !uvar_ref of
      Refined i => 
      f x n (expand_s invis i)
    | Fresh uname => 
      UVarS ((on_invis (FrSort (uvar_ref, uname)) x n invis, uvar_ref), r)
            
fun on_i_UVar on_invis expand_mt UVar f x n ((invis as (invisi, invist), uvar_ref), r) =
  case !uvar_ref of
      Refined t => 
      f x n (expand_mt invis t)
    | Fresh uname => 
      UVar (((on_invis (FrMtype (uvar_ref, uname)) x n invisi, invist), uvar_ref), r)
           
fun on_t_UVar on_invis expand_mt UVar f x n ((invis as (invisi, invist), uvar_ref), r) =
  case !uvar_ref of
      Refined t => 
      f x n (expand_mt invis t)
    | Fresh uname => 
      UVar (((invisi, on_invis (FrMtype (uvar_ref, uname)) x n invist), uvar_ref), r)
           
fun shiftx_invis _ x n invis = 
  let 
    fun f ((off, len), (acc, (x, n))) =
      if n = 0 then
        ((off, len) :: acc, (0, 0))
      else if x < off then
        ((off - x, len) :: (x, n) :: acc, (0, 0))
      else if x <= off + len then
        ((off, len + n) :: acc, (0, 0))
      else 
        ((off, len) :: acc, (x - off - len, n))
    val (invis, (x, n)) = foldl f ([], (x, n)) invis
    val residue = if n = 0 then [] else [(x, n)]
    val invis = residue @ invis
    val invis = rev invis
  in
    invis
  end

fun expand_i shiftx_i_i invis b = expand shiftx_i_i invis b
fun expand_s shiftx_i_s invis b = expand shiftx_i_s invis b
fun expand_mt shiftx_i_mt shiftx_t_mt (invisi, invist) b = (expand shiftx_i_mt invisi o expand shiftx_t_mt invist) b
                                                                                                                   
fun shiftx_i_UVarI UVarI shiftx_i_i = on_UVarI shiftx_invis (expand_i shiftx_i_i) UVarI shiftx_i_i
fun shiftx_i_UVarS UVarS shiftx_i_s = on_UVarS shiftx_invis (expand_s shiftx_i_s) UVarS shiftx_i_s
fun shiftx_i_UVar shiftx_t_mt UVar shiftx_i_mt = on_i_UVar shiftx_invis (expand_mt shiftx_i_mt shiftx_t_mt) UVar shiftx_i_mt
fun shiftx_t_UVar shiftx_i_mt UVar shiftx_t_mt = on_t_UVar shiftx_invis (expand_mt shiftx_i_mt shiftx_t_mt) UVar shiftx_t_mt


(* Adjust a fresh unification variable [u]'s invisible sections when removing [x, x+1, ..., x+n-1] in [u]. If [x+i] is invisible to [u] (i.e. [x+i] is in [u]'s invisible sections), we only needs to shrink the relevant invisible section accordingly; if [x+i] is invisible to [u], this generic implementation allows [on_visible] to deal with the situation given [x+i]'s position in [u]'s visible context and [u]'s total context. *)
fun forget_invis_generic on_visible x n invis = 
  let 
    fun f ((off, len), (acc, (x, n, offsum, offlensum))) =
      let
        val (acc_new, (x, n)) =
            if n <= 0 then
              ([(off, len)], (0, 0))
            else if x < off then
              if x + n <= off then
                (on_visible (offsum + x, offlensum + x, n);
                 ([(off - n, len)], (0, 0)))
              else 
                (on_visible (offsum + x, offlensum + x, off - x);
                 if x + n <= off + len then
                   ([(x, len - (x + n - off))], (0, 0))
                 else
                   ([], (0, x + n - off - len))
                )
            else if x < off + len then
              if x + n <= off + len then
                ([(off, len - n)], (0, 0))
              else
                ([(off, x - off)], (0, x + n - off - len))
            else 
              ([(off, len)], (x - off - len, n))
      in
        (acc_new @ acc, (x, n, offsum + off, offlensum + off + len))
      end
    val (invis, (x, n, offsum, offlensum)) = foldl f ([], (x, n, 0, 0)) invis
    val () = if n <= 0 then () else on_visible (offsum + x, offlensum + x, n)
    val invis = rev invis
  in
    invis
  end

fun str_fresh_uvar_ref fresh =
  case fresh of
      FrIdx (_, uname) =>
      str_uname_i uname
    | FrBsort (_, uname) =>
      str_uname_bs uname
    | FrSort (_, uname) =>
      str_uname_nonidx uname
    | FrMtype (_, uname) =>
      str_uname_nonidx uname

fun remove_fresh_uvar_ctx fresh_uvar x n =
  let
    fun do_it ctx = skip x n ctx
  in
    case fresh_uvar of
        FrIdx (r, (n, ctx, bs)) =>
        r := Fresh (n, do_it ctx, bs)
      | FrBsort _ =>
        ()
      | FrSort (r, (n, ctx)) =>
        r := Fresh (n, do_it ctx)
      | FrMtype (r, (n, ctx)) =>
        r := Fresh (n, do_it ctx)
  end
    
(* This is a version where [x+i] must be invisible to [fresh_uvar]. If [x+i] is visible, throw [ForgetError]. *)
fun forget_invis ForgetError fresh_uvar =
  forget_invis_generic (fn (_, pos_total, _) => raise ForgetError (pos_total, str_fresh_uvar_ref fresh_uvar))

(* This is a version that allows forgetting for [x+i] that is visible to [fresh_uvar]. When this happens, remove [x+i] from [fresh_uvar]'s visible context. *)
(* fun forget_invis_no_throw fresh_uvar = *)
(*     forget_invis_generic (fn (pos_visible, _, n) => remove_fresh_uvar_ctx fresh_uvar pos_visible n) *)

fun forget_i_UVarI shiftx_i_i ForgetError = on_UVarI (forget_invis ForgetError) (expand_i shiftx_i_i)
fun forget_i_UVarS shiftx_i_s ForgetError = on_UVarS (forget_invis ForgetError) (expand_s shiftx_i_s)
fun forget_i_UVar shiftx_i_mt shiftx_t_mt ForgetError = on_i_UVar (forget_invis ForgetError) (expand_mt shiftx_i_mt shiftx_t_mt)
fun forget_t_UVar shiftx_i_mt shiftx_t_mt ForgetError = on_t_UVar (forget_invis ForgetError) (expand_mt shiftx_i_mt shiftx_t_mt)
                                                                  
fun fresh_uvar_info fresh =
  let
    fun get_fresh_uvar_ref_ctx fresh =
      case fresh of
          FrIdx (_, (_, ctx, _)) => ctx
        | FrBsort _ => []
        | FrSort (_, (_, ctx)) => ctx
        | FrMtype (_, (_, ctx)) => ctx
  in
    (str_fresh_uvar_ref fresh, get_fresh_uvar_ref_ctx fresh)
  end
    
exception SubstUVar of (string * string list) * int

fun substx_invis_generic on_visible x = forget_invis_generic (fn (pos_visible, _, _) => on_visible pos_visible) x 1

(* This is a version where [x] must be invisible to [fresh_uvar]. If [x] is visible, throw [SubstUVar]. *)
fun substx_invis fresh_uvar =
  substx_invis_generic (fn x => raise SubstUVar (fresh_uvar_info fresh_uvar, x))
                       
(* This is a version that allows substition for [x] that is visible to [fresh_uvar]. When this happens, remove [x] from [fresh_uvar]'s visible context. *)
(* fun substx_invis_no_throw fresh_uvar = *)
(*   substx_invis_generic (fn x => remove_fresh_uvar_ctx fresh_uvar x 1) *)

fun substx_i_UVarI shiftx_i_i UVarI f x v ((invis, uvar_ref), r) =
  case !uvar_ref of
      Refined i => f x v (expand_i shiftx_i_i invis i)
    | Fresh uname => 
      UVarI ((substx_invis(* _no_throw *) (FrIdx (uvar_ref, uname)) x invis, uvar_ref), r)
            
fun substx_i_UVarS shiftx_i_s UVarS f x v ((invis, uvar_ref), r) =
  case !uvar_ref of
      Refined s => f x v (expand_s shiftx_i_s invis s)
    | Fresh uname => 
      UVarS ((substx_invis(* _no_throw *) (FrSort (uvar_ref, uname)) x invis, uvar_ref), r)

fun substx_i_UVar shiftx_i_mt shiftx_t_mt UVar f x v ((invis as (invisi, invist), uvar_ref), r) =
  case !uvar_ref of
      Refined t => f x v (expand_mt shiftx_i_mt shiftx_t_mt invis t)
    | Fresh uname => 
      UVar (((substx_invis(* _no_throw *) (FrMtype (uvar_ref, uname)) x invisi, invist), uvar_ref), r)
           
fun substx_t_UVar shiftx_i_mt shiftx_t_mt UVar f x v ((invis as (invisi, invist), uvar_ref), r) =
  case !uvar_ref of
      Refined t => f x v (expand_mt shiftx_i_mt shiftx_t_mt invis t)
    | Fresh uname => 
      UVar (((invisi, substx_invis(* _no_throw *) (FrMtype (uvar_ref, uname)) x invist), uvar_ref), r)
           
end

structure Expr = ExprFun (structure Var = IntVar structure UVar = UVar)
