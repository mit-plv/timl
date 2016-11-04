signature SIG_DERIV_CHECKER =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    exception CheckFail
    val assert : bool -> unit

    val check_proping : MicroTiMLDef.proping -> unit
    val check_tyeq : MicroTiMLDef.tyeq -> unit
    val check_kinding : MicroTiMLDef.kinding -> unit
    val check_typing : MicroTiMLDef.typing -> unit
end
