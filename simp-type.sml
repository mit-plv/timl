functor SimpTypeFn (structure Type : TYPE
                    val simp_i : Type.idx -> Type.idx
                    val simp_s : Type.sort -> Type.sort
                    val subst_i_mt : Type.idx -> Type.mtype -> Type.mtype
                   ) = struct

open Type
open SimpUtil
         
fun simp_mt t =
  case t of
      Arrow (t1, d, t2) => Arrow (simp_mt t1, simp_i d, simp_mt t2)
    | TyNat (i, r) => TyNat (simp_i i, r)
    | TyArray (t, i) => TyArray (simp_mt t, simp_i i)
    | Unit r => Unit r
    | Prod (t1, t2) => Prod (simp_mt t1, simp_mt t2)
    | UniI (s, bind, r) => UniI (simp_s s, simp_bind simp_mt bind, r)
    | BaseType a => BaseType a
    | UVar u => UVar u
    | MtVar x => MtVar x
    | MtAbs (k, bind, r) => MtAbs (k, simp_bind simp_mt bind, r)
    | MtApp (t1, t2) => MtApp (simp_mt t1, simp_mt t2)
    | MtAbsI (b, bind, r) => MtAbsI (b, simp_bind simp_mt bind, r)
    | MtAppI (t, i) =>
      let
        val t = simp_mt t
        val i = simp_i i
      in
        case t of
            MtAbsI (_, Bind (_, t), _) => simp_mt (subst_i_mt i t)
          | _ => MtAppI (t, i)
      end
    | TDatatype (dt, r) =>
      let
        fun simp_constr c = simp_binds simp_s (mapPair (simp_mt, map simp_i)) c
        fun simp_constr_decl ((name, c, r) : mtype constr_decl) : mtype constr_decl = (name, simp_constr c, r)
        val dt = simp_bind (simp_binds id (mapPair (id, map simp_constr_decl))) dt
      in
        TDatatype (dt, r)
      end

fun simp_t t =
  case t of
      Mono t => Mono (simp_mt t)
    | Uni (Bind (name, t), r) => Uni (Bind (name, simp_t t), r)

end
