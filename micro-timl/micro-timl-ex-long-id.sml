structure MicroTiMLExLongId = struct

open LongId
open VisitorUtil
open Util
open Subst
open MicroTiMLVisitor
open MicroTiMLEx
       
infixr 0 $
         
val shift_var = LongIdSubst.shiftx_var
fun compare_var id x =
  case id of
      QID _ => CmpOther
    | ID (y, r) =>
      if y = x then CmpEq
      else if y > x then
        CmpGreater $ ID (y - 1, r)
      else CmpOther
fun shift_i_t a = shift_i_t_fn (shiftx_i_i, shiftx_i_s) a
fun shift_t_t a = shift_t_t_fn shift_var a
fun subst_i_t a = subst_i_t_fn (substx_i_i, substx_i_s) a
fun subst0_i_t a = subst_i_t 0 0 a
fun subst_t_t a = subst_t_t_fn (compare_var, shift_var, shiftx_i_i, shiftx_i_s) a
fun subst0_t_t a = subst_t_t (IDepth 0, TDepth 0) 0 a
fun normalize_t a = normalize_t_fn (subst0_i_t, subst0_t_t) a
fun shift_i_e a = shift_i_e_fn (shiftx_i_i, shiftx_i_s, shift_i_t) a
fun shift_e_e a = shift_e_e_fn shift_var a
fun shift01_e_e a = shift_e_e 0 1 a
fun adapt f d x v env = f (d + env) (x + env) v
fun subst_i_e d x v = subst_i_e_fn (adapt substx_i_i d x v, adapt substx_i_s d x v, adapt subst_i_t d x v)
fun subst0_i_e a = subst_i_e 0 0 a
fun subst_e_e a = subst_e_e_fn (compare_var, shift_var, shiftx_i_i, shiftx_i_s, shift_i_t, shift_t_t) a
fun subst0_e_e a = subst_e_e (IDepth 0, TDepth 0, CDepth 0, EDepth 0) 0 a
                             
end
