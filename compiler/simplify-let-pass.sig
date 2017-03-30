signature SIG_SIMPLIFY_LET_PASS =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    val simplify_let_deriv : MicroTiMLDef.typing -> MicroTiMLDef.typing
end
