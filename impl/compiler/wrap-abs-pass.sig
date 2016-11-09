signature SIG_WRAP_ABS_PASS =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    val wrap_abs_deriv : MicroTiMLDef.typing -> MicroTiMLDef.typing
end
