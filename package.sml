(* a special kind of substitution, where a variable y such that y >= x will be replaced with m.(y-x) *)
(* This is used for packaging things in the top-level context into a module *)

structure Package = struct
open Expr
open Util
open Subst
open Bind

infixr 0 $

fun package_long_id x m (id : long_id) =
  case id of
      ID (y, r) =>
      if y >= x then
        QID (m, (y - x, r))
      else
        id
    | QID _ => id (* if it has module reference, don't substitute *)
        
fun adapt f x n env = f (x + env) n

fun params_var a = adapt package_long_id a
                            
fun package_i_i x n = IdxShiftVisitor.on_i_i $ params_var x n
fun package_i_s x n  = IdxShiftVisitor.on_i_s $ params_var x n

fun package0_i_i a = package_i_i 0 a
fun package0_i_s a = package_i_s 0 a
                               
val package0_i = package0_i_i
val package0_s = package0_i_s
                               
fun adapt f x n env = f (x + env) n
fun params_i_t x m = (adapt package_i_i x m, adapt package_i_s x m)
      
fun package_i_mt x m = TypeShiftVisitor.on_i_mt (params_i_t x m)
fun package_i_t x m = TypeShiftVisitor.on_i_t (params_i_t x m)
fun package_i_constr_core x m = TypeShiftVisitor.on_i_constr_core (params_i_t x m)
fun package_i_c x m = TypeShiftVisitor.on_i_c (params_i_t x m)

fun package0_i_mt a = package_i_mt 0 a
fun package0_i_t a = package_i_t 0 a
fun package0_i_constr_core a = package_i_constr_core 0 a
fun package0_i_c a = package_i_c 0 a

fun package_t_mt x m = TypeShiftVisitor.on_t_mt $ params_var x m
fun package_t_t x m = TypeShiftVisitor.on_t_t $ params_var x m
fun package_t_constr_core x m = TypeShiftVisitor.on_t_constr_core $ params_var x m
fun package_t_c x m = TypeShiftVisitor.on_t_c $ params_var x m

fun package0_t_mt a = package_t_mt 0 a
fun package0_t_t a = package_t_t 0 a
fun package0_t_constr_core a = package_t_constr_core 0 a
fun package0_t_c a = package_t_c 0 a

fun package0_mt m = package0_t_mt m o package0_i_mt m
fun package0_t m = package0_t_t m o package0_i_t m
fun package0_c m = package0_t_c m o package0_i_c m

open ExprShift

fun package_i_e x m = ExprShiftVisitor.on_i_e (adapt package_i_i x m, adapt package_i_s x m, adapt package_i_mt x m, adapt package_i_t x m)
fun package_t_e x m = ExprShiftVisitor.on_t_e (adapt package_t_mt x m, adapt package_t_t x m)
fun package_c_e x m = ExprShiftVisitor.on_c_e $ params_var x m
fun package_e_e x m = ExprShiftVisitor.on_e_e $ params_var x m

fun package0_i_e a = package_i_e 0 a
fun package0_t_e a = package_t_e 0 a
fun package0_c_e a = package_c_e 0 a
fun package0_e_e a = package_e_e 0 a

end
