structure VisitorUtil = struct
open Util
       
fun extend_noop this env x1 = env
val visit_noop = return3
fun visit_imposs msg _ _ _ = raise Impossible msg
fun visit_pair visit_fst visit_snd env (a, b) = (visit_fst env a, visit_snd env b)
fun visit_triple visit1 visit2 visit3 env (a1, a2, a3) = (visit1 env a1, visit2 env a2, visit3 env a3)
fun visit_list visit env = map (visit env)
fun visit_option visit env = Option.map (visit env)
                               
fun ignore_this_env f this env t = f t
fun ignore_this f this env t = f env t

datatype 'a cmp_var =
         CmpEq
         | CmpGreater of 'a
         | CmpOther

end
                          
