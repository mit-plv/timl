signature SIG_HOISTED_DERIV_CHECKER =
sig
    structure MicroTiMLHoistedDef : SIG_MICRO_TIML_HOISTED_DEF

    val check_program : MicroTiMLHoistedDef.program_typing -> unit
end
