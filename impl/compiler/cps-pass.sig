signature SIG_CPS_PASS =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    val cps_cfg : MicroTiMLDef.configing -> MicroTiMLDef.configing
end
