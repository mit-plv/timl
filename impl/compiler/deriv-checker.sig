signature SIG_DERIV_CHECKER =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    val check_kinding : MicroTiMLDef.kinding -> unit
    val check_typing : MicroTiMLDef.typing -> unit
end
