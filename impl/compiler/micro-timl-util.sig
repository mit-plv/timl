signature SIG_MICRO_TIML_UTIL =
sig
    structure MicroTiMLDef : SIG_MICRO_TIML_DEF

    val extract_judge_kdeq : MicroTiMLDef.kdeq -> MicroTiMLDef.kdeq_judgement
    val extract_judge_proping : MicroTiMLDef.proping -> MicroTiMLDef.proping_judgement
    val extract_judge_kinding : MicroTiMLDef.kinding -> MicroTiMLDef.kinding_judgement
    val extract_judge_wfkind : MicroTiMLDef.wfkind -> MicroTiMLDef.wfkind_judgement
    val extract_judge_wfprop : MicroTiMLDef.wfprop -> MicroTiMLDef.wfprop_judgement
    val extract_judge_tyeq : MicroTiMLDef.tyeq -> MicroTiMLDef.tyeq_judgement
    val extract_expr_value : MicroTiMLDef.value -> MicroTiMLDef.expr
    val extract_judge_typing : MicroTiMLDef.typing -> MicroTiMLDef.typing_judgement
    val extract_p_bin_conn : MicroTiMLDef.prop -> MicroTiMLDef.prop_bin_conn * MicroTiMLDef.prop * MicroTiMLDef.prop
    val extract_p_quan : MicroTiMLDef.prop -> MicroTiMLDef.quan * MicroTiMLDef.sort * MicroTiMLDef.prop
    val extract_p_bin_pred : MicroTiMLDef.prop -> MicroTiMLDef.prop_bin_pred * MicroTiMLDef.cstr * MicroTiMLDef.cstr
    val extract_c_quan : MicroTiMLDef.cstr -> MicroTiMLDef.quan * MicroTiMLDef.kind * MicroTiMLDef.cstr
    val extract_c_bin_op : MicroTiMLDef.cstr -> MicroTiMLDef.cstr_bin_op * MicroTiMLDef.cstr * MicroTiMLDef.cstr
    val extract_c_un_op : MicroTiMLDef.cstr -> MicroTiMLDef.cstr_un_op * MicroTiMLDef.cstr
    val extract_c_time_app : MicroTiMLDef.cstr -> int * MicroTiMLDef.cstr * MicroTiMLDef.cstr
    val extract_c_arrow : MicroTiMLDef.cstr -> MicroTiMLDef.cstr * MicroTiMLDef.cstr * MicroTiMLDef.cstr
    val extract_c_sum : MicroTiMLDef.cstr -> MicroTiMLDef.cstr * MicroTiMLDef.cstr
    val extract_c_prod : MicroTiMLDef.cstr -> MicroTiMLDef.cstr * MicroTiMLDef.cstr
    val extract_c_rec : MicroTiMLDef.cstr -> MicroTiMLDef.kind * MicroTiMLDef.cstr
    val extract_c_abs : MicroTiMLDef.cstr -> MicroTiMLDef.cstr
    val extract_c_type_nat : MicroTiMLDef.cstr -> MicroTiMLDef.cstr
    val extract_c_type_arr : MicroTiMLDef.cstr -> MicroTiMLDef.cstr * MicroTiMLDef.cstr
    val extract_k_time_fun : MicroTiMLDef.kind -> int
    val extract_k_arrow : MicroTiMLDef.kind -> MicroTiMLDef.kind * MicroTiMLDef.kind
    val extract_e_inj : MicroTiMLDef.expr -> MicroTiMLDef.injector * MicroTiMLDef.expr
    val extract_e_proj : MicroTiMLDef.expr -> MicroTiMLDef.projector * MicroTiMLDef.expr
    val extract_e_abs : MicroTiMLDef.expr -> MicroTiMLDef.expr
    val extract_e_abs_c : MicroTiMLDef.expr -> MicroTiMLDef.expr
    val extract_e_prim_bin_op : MicroTiMLDef.expr -> MicroTiMLDef.prim_expr_bin_op * MicroTiMLDef.expr * MicroTiMLDef.expr
    val extract_e_pack : MicroTiMLDef.expr -> MicroTiMLDef.cstr * MicroTiMLDef.expr

    val str_cstr_const : MicroTiMLDef.cstr_const -> string
    val str_cstr_bin_op : MicroTiMLDef.cstr_bin_op -> string
    val str_cstr_un_op : MicroTiMLDef.cstr_un_op -> string
    val str_quan : MicroTiMLDef.quan -> string
    val str_sort : MicroTiMLDef.sort -> string
    val str_prop_bin_conn : MicroTiMLDef.prop_bin_conn -> string
    val str_prop_bin_pred : MicroTiMLDef.prop_bin_pred -> string
    val str_expr_const : MicroTiMLDef.expr_const -> string
    val str_projector : MicroTiMLDef.projector -> string
    val str_injector : MicroTiMLDef.injector -> string
    val str_expr_un_op : MicroTiMLDef.expr_un_op -> string
    val str_prim_expr_bin_op : MicroTiMLDef.prim_expr_bin_op -> string
    val str_expr_bin_op : MicroTiMLDef.expr_bin_op -> string
    val str_expr_tri_op : MicroTiMLDef.expr_tri_op -> string
end
