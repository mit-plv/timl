(* collect open variables *)

structure CollectVar = struct

open LongId
open Subst

infixr 0 $
         
(* fun collect_var_aux_i_ibind f d acc (Bind (_, b) : ('a * 'b) ibind) = f (d + 1) acc b *)

(* fun collect_var_long_id d (id : long_id) : long_id list = *)
(*   case id of *)
(*       QID _ => [id] *)
(*     | ID (x, r) => *)
(*       if x >= d then [ID (x - d, r)] *)
(*       else [] *)

(* local *)
(*   fun f d(*depth*) acc b = *)
(*     case b of *)
(* 	VarI x => collect_var_long_id d x @ acc *)
(*       | IConst _ => acc *)
(*       | UnOpI (opr, i, r) => f d acc i *)
(*       | BinOpI (opr, i1, i2) =>  *)
(*         let *)
(*           val acc = f d acc i1 *)
(*           val acc = f d acc i2 *)
(*         in *)
(*           acc *)
(*         end *)
(*       | Ite (i1, i2, i3, r) => *)
(*         let *)
(*           val acc = f d acc i1 *)
(*           val acc = f d acc i2 *)
(*           val acc = f d acc i3 *)
(*         in *)
(*           acc *)
(*         end *)
(*       | IAbs (b, bind, r) => *)
(*         collect_var_aux_i_ibind f d acc bind *)
(*       | UVarI a => acc *)
(* in *)
(* val collect_var_aux_i_i = f *)
(* fun collect_var_i_i b = f 0 [] b *)
(* end *)

(* local *)
(*   fun f d acc b = *)
(*     case b of *)
(* 	PTrueFalse _ => acc *)
(*       | Not (p, r) => f d acc p *)
(*       | BinConn (opr,p1, p2) => *)
(*         let *)
(*           val acc = f d acc p1 *)
(*           val acc = f d acc p2 *)
(*         in *)
(*           acc *)
(*         end *)
(*       | BinPred (opr, i1, i2) =>  *)
(*         let *)
(*           val acc = collect_var_aux_i_i d acc i1 *)
(*           val acc = collect_var_aux_i_i d acc i2 *)
(*         in *)
(*           acc *)
(*         end *)
(*       | Quan (q, bs, bind, r) => collect_var_aux_i_ibind f d acc bind *)
(* in *)
(* val collect_var_aux_i_p = f *)
(* fun collect_var_i_p b = f 0 [] b *)
(* end *)

(* local *)
(*   fun f d acc b = *)
(*     case b of *)
(* 	Basic s => acc *)
(*       | Subset (b, bind, r) => collect_var_aux_i_ibind collect_var_aux_i_p d acc bind *)
(*       | UVarS a => acc *)
(*       | SAbs (s, bind, r) => collect_var_aux_i_ibind f d acc bind *)
(*       | SApp (s, i) => *)
(*         let *)
(*           val acc = f d acc s *)
(*           val acc = collect_var_aux_i_i d acc i *)
(*         in *)
(*           acc *)
(*         end *)
(* in *)
(* val collect_var_aux_i_s = f *)
(* fun collect_var_i_s b = f 0 [] b *)
(* end *)

(* fun collect_var_aux_i_k d acc (_, sorts) = *)
(*   foldl (fn (s, acc) => collect_var_aux_i_s d acc s) acc sorts *)
                                                                        
(* fun collect_var_aux_t_ibind f d acc (Bind (_, b) : ('a * 'b) ibind) = f d acc b *)
(* fun collect_var_aux_i_tbind f d acc (Bind (_, b) : ('a * 'b) tbind) = f d acc b *)
(* fun collect_var_aux_t_tbind f d acc (Bind (_, b) : ('a * 'b) tbind) = f (d + 1) acc b *)

(* local *)
(*   fun f d acc b = *)
(*     case b of *)
(* 	Arrow (t1, i, t2) => *)
(*         let *)
(*           val acc = f d acc t1 *)
(*           val acc = collect_var_aux_i_i d acc i *)
(*           val acc = f d acc t2 *)
(*         in *)
(*           acc *)
(*         end *)
(*       | TyNat (i, _) => collect_var_aux_i_i d acc i *)
(*       | TyArray (t, i) => *)
(*         let *)
(*           val acc = f d acc t *)
(*           val acc = collect_var_aux_i_i d acc i *)
(*         in *)
(*           acc *)
(*         end *)
(*       | Unit _ => acc *)
(*       | Prod (t1, t2) => *)
(*         let *)
(*           val acc = f d acc t1 *)
(*           val acc = f d acc t2 *)
(*         in *)
(*           acc *)
(*         end *)
(*       | UniI (s, bind, _) => *)
(*         let *)
(*           val acc = collect_var_aux_i_s d acc s *)
(*           val acc = collect_var_aux_i_ibind f d acc bind *)
(*         in *)
(*           acc *)
(*         end *)
(*       | MtVar _ => acc *)
(*       | MtApp (t1, t2) => *)
(*         let *)
(*           val acc = f d acc t1 *)
(*           val acc = f d acc t2 *)
(*         in *)
(*           acc *)
(*         end *)
(*       | MtAbs (k, bind, _) => collect_var_aux_i_tbind f d acc bind *)
(*       | MtAppI (t, i) => *)
(*         let *)
(*           val acc = f d acc t *)
(*           val acc = collect_var_aux_i_i d acc i *)
(*         in *)
(*           acc *)
(*         end *)
(*       | MtAbsI (b, bind, r) => collect_var_aux_i_ibind f d acc bind *)
(*       | BaseType _ => acc *)
(*       | UVar _ => acc *)
(*       | TDatatype _ => raise Unimpl "collect_var_i_mt()/TDatatype" *)
(* in *)
(* val collect_var_aux_i_mt = f *)
(* fun collect_var_i_mt b = f 0 [] b *)
(* end *)

(* local *)
(*   fun f d acc b = *)
(*     case b of *)
(* 	Arrow (t1, i, t2) => *)
(*         let *)
(*           val acc = f d acc t1 *)
(*           val acc = f d acc t2 *)
(*         in *)
(*           acc *)
(*         end *)
(*       | TyNat (i, _) => acc *)
(*       | TyArray (t, i) => f d acc t *)
(*       | Unit _ => acc *)
(*       | Prod (t1, t2) => *)
(*         let *)
(*           val acc = f d acc t1 *)
(*           val acc = f d acc t2 *)
(*         in *)
(*           acc *)
(*         end *)
(*       | UniI (s, bind, _) => collect_var_aux_t_ibind f d acc bind *)
(*       | MtVar x => collect_var_long_id d x @ acc *)
(*       | MtApp (t1, t2) => *)
(*         let *)
(*           val acc = f d acc t1 *)
(*           val acc = f d acc t2 *)
(*         in *)
(*           acc *)
(*         end *)
(*       | MtAbs (k, bind, _) => collect_var_aux_t_tbind f d acc bind *)
(*       | MtAppI (t, i) => f d acc t *)
(*       | MtAbsI (s, bind, r) => collect_var_aux_t_ibind f d acc bind *)
(*       | BaseType _ => acc *)
(*       | UVar _ => acc *)
(*       | TDatatype _ => raise Unimpl "collect_var_t_mt()/TDatatype" *)
(* in *)
(* val collect_var_aux_t_mt = f *)
(* fun collect_var_t_mt b = f 0 [] b *)
(* end *)

fun adapt f x _ b = f x b
                      
fun unadapt f d b = f d 0 b
                      
fun collect_var_0 f b =
  let
    val r = ref []
    fun output id = push_ref r id
    val _ = f output 0 b
  in
    !r
  end
             
fun collect_var_aux_long_id output x id =
  let
    val () = 
        case id of
            QID _ => output id
          | ID (y, r) =>
            if y >= x then output $ ID (y - x, r)
            else ()
  in
    id
  end

fun params_i output x env = collect_var_aux_long_id output (x + env)
                            
fun collect_var_aux_i_i output x =
  IdxShift.on_i_i $ params_i output x
fun collect_var_aux_i_s output x =
  IdxShift.on_i_s $ params_i output x
             
fun collect_var_i_i b = collect_var_0 collect_var_aux_i_i b
fun collect_var_i_s b = collect_var_0 collect_var_aux_i_s b
             
fun collect_var_aux_i_mt output = unadapt $ TypeShift.on_i_mt (adapt $ collect_var_aux_i_i output, adapt $ collect_var_aux_i_s output)
fun collect_var_aux_t_mt output = unadapt $ TypeShift.on_t_mt (adapt $ collect_var_aux_long_id output)
                                       
fun collect_var_i_mt b = collect_var_0 collect_var_aux_i_mt b
fun collect_var_t_mt b = collect_var_0 collect_var_aux_t_mt b
             
end
