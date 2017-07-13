structure StringVar = struct
open Util
type var = string
type name_context = string list * string list * string list * string list
type global_name_context = name_context Gctx.map
                                        
fun str_v ctx x : string = x
fun str_raw_v x = x
      
fun lookup_module gctx m = (m, ([], [], [], []))
                             
fun str_long_id sel gctx ctx (m, x) =
  let
    val m = default "" (Option.map (suffix "." o fst) m)
    val x = str_v ctx (fst x)
  in
    m ^ x
  end
    
fun eq_v (x : var, y) = x = y
                              
fun shiftx_v x n y = y
fun forget_v ForgetError x n y =  y
fun substx_v Var x v y = raise Impossible "Can't do StringVar.substx_v()"

fun int2var x = raise Impossible "StringVar.int2var()"
fun var2int x = raise Impossible "StringVar.var2int()"
end

structure IntVar = struct
open Util
open ShiftUtil
open Gctx
type var = int
type name_context = string list * string list * string list * string list
type global_name_context = name_context Gctx.map
                                        
fun str_v ctx x : string =
  (* sprintf "%$" [str_int x] *)
  case nth_error ctx x of
      SOME name => name
    | NONE => "unbound_" ^ str_int x
                                   
fun str_raw_v x = str_int x
                    
fun str_id ctx (x, _) =
  str_v ctx x
        
fun lookup_module gctx m =
  case nth_error2 gctx m of
      SOME (name, ctx) => (name, ctx)
    | NONE => ("unbound_module_" ^ m, ([], [], [], []))
                
fun str_long_id sel gctx ctx (m, x) =
  let
    val (mod_name, ctx) =
        case m of
            SOME (m, _) =>
            let
              val (name, ctx) = lookup_module gctx m
              val name = name ^ "."
              val ctx = sel ctx
            in
              (name, ctx)
            end
          | NONE => ("", ctx)
    val x = str_id ctx x
  in
    mod_name ^ x
  end
    
fun eq_v (x : var, y) = x = y

val shiftx_v = shiftx_int
val forget_v = forget_int
                 
fun substx_v Var x v y =
  if y = x then
    v ()
  else if y > x then
    Var (y - 1)
  else
    Var y

fun int2var x = x
fun var2int x = x
                  
end
                     
structure Underscore = struct
type 'bsort uvar_bs = unit
type ('bsort, 'idx) uvar_i = unit
type ('bsort, 'sort) uvar_s = unit
type ('sort, 'kind, 'mtype) uvar_mt = unit
fun str_uvar_bs _ _ = "_"
fun str_uvar_s _ _ = "_"
fun str_uvar_i _ _ = "_"
fun str_uvar_mt _ _ = "_"
fun eq_uvar_i (_, _) = false
fun eq_uvar_bs (_, _) = false
fun eq_uvar_s (_, _) = false
fun eq_uvar_mt (_, _) = false
end

structure NamefulExpr = ExprFn (structure Var = StringVar
                                structure UVarI = Underscore
                                structure UVarT = Underscore
                                type ptrn_constr_tag = unit
                               )
                               
structure UnderscoredExpr = ExprFn (structure Var = IntVar
                                    structure UVarI = Underscore
                                    structure UVarT = Underscore
                                    type ptrn_constr_tag = unit
                                   )

structure UnderscoredExprVisitor = ExprVisitorFn (structure S = UnderscoredExpr
                                                  structure T = UnderscoredExpr)
