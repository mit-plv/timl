signature SIG_DERIV_CHECKER =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    val check_typing : MicroTiMLDef.typing -> unit
end
