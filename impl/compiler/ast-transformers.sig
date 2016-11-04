signature SIG_AST_TRANSFORMERS =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    structure PlainPrinter :
              sig
                  val str_cstr : MicroTiMLDef.cstr -> string
                  val str_kind : MicroTiMLDef.kind -> string
                  val str_prop : MicroTiMLDef.prop -> string
                  val str_expr : MicroTiMLDef.expr -> string
              end

    structure ShiftCstr :
              sig
                  val shift_c_c : int -> int -> MicroTiMLDef.cstr -> MicroTiMLDef.cstr
                  val shift_c_k : int -> int -> MicroTiMLDef.kind -> MicroTiMLDef.kind
                  val shift_c_p : int -> int -> MicroTiMLDef.prop -> MicroTiMLDef.prop
                  val shift_c_e : int -> int -> MicroTiMLDef.expr -> MicroTiMLDef.expr

                  val shift0_c_c : MicroTiMLDef.cstr -> MicroTiMLDef.cstr
                  val shift0_c_k : MicroTiMLDef.kind -> MicroTiMLDef.kind
                  val shift0_c_p : MicroTiMLDef.prop -> MicroTiMLDef.prop
                  val shift0_c_e : MicroTiMLDef.expr -> MicroTiMLDef.expr
              end

    structure ShiftExpr :
              sig
                  val shift_e_e : int -> int -> MicroTiMLDef.expr -> MicroTiMLDef.expr

                  val shift0_e_e : MicroTiMLDef.expr -> MicroTiMLDef.expr
              end

    structure SubstCstr :
              sig
                  val subst_c_c : MicroTiMLDef.cstr -> int -> MicroTiMLDef.cstr -> MicroTiMLDef.cstr
                  val subst_c_k : MicroTiMLDef.cstr -> int -> MicroTiMLDef.kind -> MicroTiMLDef.kind
                  val subst_c_p : MicroTiMLDef.cstr -> int -> MicroTiMLDef.prop -> MicroTiMLDef.prop
                  val subst_c_e : MicroTiMLDef.cstr -> int -> MicroTiMLDef.expr -> MicroTiMLDef.expr

                  val subst0_c_c : MicroTiMLDef.cstr -> MicroTiMLDef.cstr -> MicroTiMLDef.cstr
                  val subst0_c_k : MicroTiMLDef.cstr -> MicroTiMLDef.kind -> MicroTiMLDef.kind
                  val subst0_c_p : MicroTiMLDef.cstr -> MicroTiMLDef.prop -> MicroTiMLDef.prop
                  val subst0_c_e : MicroTiMLDef.cstr -> MicroTiMLDef.expr -> MicroTiMLDef.expr
              end

    structure SubstExpr :
              sig
                  val subst_e_e : MicroTiMLDef.expr -> int -> MicroTiMLDef.expr -> MicroTiMLDef.expr

                  val subst0_e_e : MicroTiMLDef.expr -> MicroTiMLDef.expr -> MicroTiMLDef.expr
              end

    structure DirectSubstCstr :
              sig
                  val dsubst_c_c : MicroTiMLDef.cstr -> int -> MicroTiMLDef.cstr -> MicroTiMLDef.cstr
                  val dsubst_c_k : MicroTiMLDef.cstr -> int -> MicroTiMLDef.kind -> MicroTiMLDef.kind
                  val dsubst_c_p : MicroTiMLDef.cstr -> int -> MicroTiMLDef.prop -> MicroTiMLDef.prop
                  val dsubst_c_e : MicroTiMLDef.cstr -> int -> MicroTiMLDef.expr -> MicroTiMLDef.expr

                  val dsubst0_c_c : MicroTiMLDef.cstr -> MicroTiMLDef.cstr -> MicroTiMLDef.cstr
                  val dsubst0_c_k : MicroTiMLDef.cstr -> MicroTiMLDef.kind -> MicroTiMLDef.kind
                  val dsubst0_c_p : MicroTiMLDef.cstr -> MicroTiMLDef.prop -> MicroTiMLDef.prop
                  val dsubst0_c_e : MicroTiMLDef.cstr -> MicroTiMLDef.expr -> MicroTiMLDef.expr
              end

    structure DirectSubstExpr :
              sig
                  val dsubst_e_e : MicroTiMLDef.expr -> int -> MicroTiMLDef.expr -> MicroTiMLDef.expr

                  val dsubst0_e_e : MicroTiMLDef.expr -> MicroTiMLDef.expr -> MicroTiMLDef.expr
              end

    structure FVUtil :
              sig
                  val unique_merge : int list * int list -> int list
              end

    structure FVCstr :
              sig
                  val free_vars_c_c : int -> MicroTiMLDef.cstr -> int list
                  val free_vars_c_k : int -> MicroTiMLDef.kind -> int list
                  val free_vars_c_p : int -> MicroTiMLDef.prop -> int list
                  val free_vars_c_e : int -> MicroTiMLDef.expr -> int list

                  val free_vars0_c_c : MicroTiMLDef.cstr -> int list
                  val free_vars0_c_k : MicroTiMLDef.kind -> int list
                  val free_vars0_c_p : MicroTiMLDef.prop -> int list
                  val free_vars0_c_e : MicroTiMLDef.expr -> int list
              end

    structure FVExpr :
              sig
                  val free_vars_e_e : int -> MicroTiMLDef.expr -> int list

                  val free_vars0_e_e : MicroTiMLDef.expr -> int list
              end
end
