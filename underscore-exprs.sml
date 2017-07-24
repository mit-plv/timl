structure StringVar = struct
open Util
open LongId
type var = string
type name_context = string list * string list * string list * string list
type global_name_context = name_context Gctx.map
                                        
fun str_v ctx x : string = x
fun str_raw_v x = x
      
fun lookup_module gctx m = (m, ([], [], [], []))
                             
fun str_long_id sel gctx ctx id =
  case id of
      ID (x, _) => str_v ctx x
    | QID ((m, _), (x, _)) => m ^ "." ^ str_v ctx x
    
fun eq_v (x : var, y) = x = y
                              
fun shiftx_v x n y = y
fun forget_v ForgetError x n y =  y
fun substx_v Var x v y = raise Impossible "Can't do StringVar.substx_v()"

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

structure UnderscoredShiftEE = ShiftEEFn (structure S = UnderscoredExpr
                                          structure T = UnderscoredExpr)
                                                 
