signature SIG_CLO_CONV_PASS =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    val clo_conv_deriv : MicroTiMLDef.typing -> MicroTiMLDef.typing
end
