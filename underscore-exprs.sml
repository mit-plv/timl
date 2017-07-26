structure Underscore = struct
open Util
type 'bsort uvar_bs = unit
type ('bsort, 'idx) uvar_i = unit
type ('bsort, 'sort) uvar_s = unit
type ('sort, 'kind, 'mtype) uvar_mt = unit
fun eq_uvar_bs _ = false
fun eq_uvar_i _ = false
fun eq_uvar_s _ = false
fun eq_uvar_mt _ = false
fun map_uvar_bs _ = id
fun map_uvar_i _ = id
fun map_uvar_s _ = id
fun str_uvar_bs _ _ = "_"
fun str_uvar_i _ _ = "_"
fun str_uvar_s _ _ = "_"
fun str_uvar_mt _ _ = "_"
end

structure NamefulExpr = IdxTypeExprFn (type v = string
                                structure UVarI = Underscore
                                structure UVarT = Underscore
                                type ptrn_constr_tag = unit
                               )
                               
structure NamefulHasEqual = struct
open Underscore
open NamefulExpr
open LongIdHasEqual
end
                       
structure NamefulEqual = EqualFn (type bsort = NamefulExpr.Type.bsort
                                  structure IdxType = struct
                                  structure Idx = NamefulExpr.Idx
                                  structure Type = NamefulExpr.Type
                                  end
                                  structure HasEqual = NamefulHasEqual
                                 )
                          
structure StringLongIdCanToString = struct

open LongId
open Gctx
       
fun str_raw_v x = x
fun str_raw_var a = str_raw_long_id str_raw_v a
                                    
fun str_v ctx x : string = x
                                    
fun lookup_module gctx m = (m, ([], [], [], []))
                
fun str_var sel gctx ctx id =
  case id of
      ID (x, _) => str_v ctx x
    | QID ((m, _), (x, _)) => m ^ "." ^ str_v ctx x
    
end
                                   
structure NamefulCanToString = struct
open Underscore
open NamefulExpr
open StringLongIdCanToString
end
                       
structure NamefulToString = ToStringFn (type bsort = NamefulExpr.Type.bsort
                                        structure Expr = NamefulExpr
                                        structure CanToString = NamefulCanToString
                                )
                                
structure UnderscoredExpr = IdxTypeExprFn (type v = int
                                    structure UVarI = Underscore
                                    structure UVarT = Underscore
                                    type ptrn_constr_tag = unit
                                   )

structure UnderscoredHasEqual = struct
open Underscore
open UnderscoredExpr
open LongIdHasEqual
end
                       
structure UnderscoredEqual = EqualFn (type bsort = UnderscoredExpr.Type.bsort
                                      structure IdxType = struct
                                      structure Idx = UnderscoredExpr.Idx
                                      structure Type = UnderscoredExpr.Type
                                      end
                                      structure HasEqual = UnderscoredHasEqual
                          )
                          
structure UnderscoredCanToString = struct
open Underscore
open UnderscoredExpr
open IntLongIdCanToString
end
                       
structure UnderscoredToString = ToStringFn (type bsort = UnderscoredExpr.Type.bsort
                                            structure Expr = UnderscoredExpr
                                            structure CanToString = UnderscoredCanToString
                                )
                                
structure UnderscoredSubst = SubstFn (structure IdxType = struct
                                      structure Idx = UnderscoredExpr.Idx
                                      structure Type = UnderscoredExpr.Type
                                      end
                                      structure SubstableVar = LongIdSubst
)
                          
structure UnderscoredExprVisitor = ExprVisitorFn (structure S = UnderscoredExpr
                                                  structure T = UnderscoredExpr)

structure UnderscoredShiftEE = ShiftEEFn (structure S = UnderscoredExpr
                                          structure T = UnderscoredExpr)
                                                 
