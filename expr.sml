structure UVar = struct
open Util

infixr 0 $
       
datatype ('a, 'b) uvar = 
         Fresh of 'a
         | Refined of 'b

type uvar_name = int

type ('a, 'b) uvar_ref = (('a, 'b) uvar) ref
                             
fun is_fresh x =
  case !x of
      Fresh _ => true
    | Refined _ => false
                        
(* uvar for bsort *)                  
type 'bsort uvar_bs = (uvar_name, 'bsort) uvar_ref

(* uvar for index *)                  
type ('bsort, 'idx) uvar_i = (uvar_name * (string * 'bsort) list(*context*) * 'bsort(*result*), 'idx) uvar_ref

(* uvar for sort *)                  
type ('bsort, 'sort) uvar_s = (uvar_name * (string * 'bsort) list(*context*), 'sort) uvar_ref

(* uvar for (mono-)type *)                  
type ('bsort, 'kind, 'mtype) uvar_mt = (uvar_name * ((string * 'bsort) list(*index context*) * (string * 'kind) list(*type context*)), 'mtype) uvar_ref

fun refine (x : ('a, 'b) uvar_ref) (v : 'b) = 
  case !x of
      Refined _ => raise Impossible "refine(): should only refine Fresh uvar"
    | Fresh _ =>
      x := Refined v

fun str_uvar n = "?" ^ str_int n

fun str_uinfo_bs n = str_uvar n
(* fun str_uinfo_i str_bs (n, ctx, b) = str_uvar n *)
fun str_uinfo_s (n, ctx) = str_uvar n
fun str_uinfo_mt _ (n, ctx) = str_uvar n
                                         
fun str_uinfo_i str_bs (n, ctx, b) = sprintf "$[$$]" [str_uvar n, join_suffix " => " $ map (str_bs o snd) $ rev ctx, str_bs b]
(* fun str_uinfo_mt (str_s, str_k) (n, (sctx, kctx)) = sprintf "$[$$$]" [str_uvar n, join_suffix " => " $ map (fn (name, s) => sprintf "$:$" [name, str_s s]) $ rev sctx, join_suffix " => " $ map (str_k o snd) $ rev kctx, "*"] *)
                                         
fun str_uvar_bs str_bs (u : 'bsort uvar_bs) =
  case !u of
      Refined bs => str_bs bs
    | Fresh info => str_uinfo_bs info
                                 
fun str_uvar_i (str_bs, str_i) (u : ('bsort, 'idx) uvar_i) =
  case !u of
      Refined i => str_i i
    | Fresh info => str_uinfo_i str_bs info

fun str_uvar_s str_s (u : ('bsort, 'sort) uvar_s) =
  case !u of
      Refined s => str_s s
    | Fresh info => str_uinfo_s info

fun str_uvar_mt (str_s, str_k, str_mt) (u : ('sort, 'kind, 'mtype) uvar_mt) =
  case !u of
      Refined t => str_mt t
    | Fresh info => str_uinfo_mt (str_s, str_k) info
                            
val eq_uvar_bs = op=
val eq_uvar_i = op=
val eq_uvar_s = op=
val eq_uvar_mt = op=
                                                                                        
fun get_uvar_info x =
  case !x of
      Fresh info => SOME info
    | Refined _ => NONE
                       
end
                       
structure Expr = ExprFn (structure Var = IntVar
                         structure UVarI = UVar
                         structure UVarT = UVar
                         type ptrn_constr_tag = int * int
                        )

structure CanToString = struct
(* fun str_raw_id (x, _) = str_raw_v x *)
(* val str_raw_long_id = fn a => str_raw_long_id str_raw_v a *)
open Expr
fun str_raw_var a = str_raw_long_id str_raw_v a
                                    
fun str_id ctx (x, _) =
  str_v ctx x
        
fun str_var sel gctx ctx id =
  case id of
      QID ((m, _), x) =>
      let
        val (name, ctx) = lookup_module gctx m
        val ctx = sel ctx
      in
        name ^ "." ^ str_id ctx x
      end
    | ID x => str_id ctx x
    
end
                       
structure ToString = ToStringFn (structure Expr = Expr
                                 structure CanToString = CanToString
                                )
                                
structure Subst = SubstFn (structure Idx = Expr.Idx
                           structure Type = Expr.Type
                           structure SubstableVar = LongIdSubst
)
                          
structure ExprVisitor = ExprVisitorFn (structure S = Expr
                                       structure T = Expr)

structure ShiftEE = ShiftEEFn (structure S = Expr
                               structure T = Expr)
                                      
structure SubstTE = SubstTEFn (structure S = Expr
                               structure T = Expr)
                                      
structure Simp = SimpFn (structure Idx = Expr
                         val get_region_i = Expr.get_region_i
                         val get_region_p = Expr.get_region_p
                         val eq_i = Expr.eq_i
                         val eq_p = Expr.eq_p
                         val shift_i_i = Subst.shift_i_i
                         val forget_i_i = Subst.forget_i_i
                         val forget_i_p = Subst.forget_i_p
                         val subst_i_i = Subst.subst_i_i
                         val subst_i_s = Subst.subst_i_s
                         val substx_i_p = Subst.substx_i_p
                        )
                        
structure VC = VCFn (structure Idx = Expr
                     val get_region_p = Expr.get_region_p
                     val str_bs = ToString.str_bs
                     val str_p = ToString.str_p
                     val simp_p = Simp.simp_p
                    )
                    
