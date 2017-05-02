structure CheckNoUVar = struct

structure N = NoUVarExpr

fun nouvar2uvar_bs bs =
  case bs of
      N.Base b => Base b
    | N.BSArrow (a, b) => BSArrow (nouvar2uvar_bs a, nouvar2uvar_bs b)
    | N.UVarBS u => exfalso u
                                
fun nouvar2uvar_i i =
  let
    fun f i =
      case i of
          N.VarI x => VarI x
        | N.ConstIT c => ConstIT c
        | N.ConstIN c => ConstIN c
        | N.UnOpI (opr, i, r) => UnOpI (opr, f i, r)
        | N.DivI (i1, n2) => DivI (f i1, n2)
        | N.ExpI (i1, n2) => ExpI (f i1, n2)
        | N.BinOpI (opr, i1, i2) => BinOpI (opr, f i1, f i2)
        | N.Ite (i1, i2, i3, r) => Ite (f i1, f i2, f i3, r)
        | N.TrueI r => TrueI r
        | N.FalseI r => FalseI r
        | N.TTI r => TTI r
        | N.IAbs (bs, Bind (name, i), r) => IAbs (nouvar2uvar_bs bs, Bind (name, f i), r)
        | N.AdmitI r => AdmitI r
        | N.UVarI (u, _) => exfalso u
  in
    f i
  end

fun no_uvar_bsort bs =
  case update_bs bs of
      Base b => N.Base b
    | BSArrow (a, b) => N.BSArrow (no_uvar_bsort a, no_uvar_bsort b)
    | UVarBS uvar_ref =>
      (* raise Impossible "no_uvar_bsort(): UVarBS" *)
      (unify_bs dummy (bs, Base UnitSort);
       N.Base N.UnitSort)

fun no_uvar_i i =
  let
    val i = update_i i
    fun impossible i' = Impossible $ sprintf "\n$\nno_uvar_i (): $ shouldn't be UVarI in $" [str_region "" (* "examples/rbt.timl" *)"" (get_region_i i'), str_i [] [] i', str_i [] [] i]
    fun f i =
      case i of
          VarI x => N.VarI x
        | ConstIT c => N.ConstIT c
        | ConstIN c => N.ConstIN c
        | UnOpI (opr, i, r) => N.UnOpI (opr, f i, r)
        | DivI (i1, n2) => N.DivI (f i1, n2)
        | ExpI (i1, n2) => N.ExpI (f i1, n2)
        | BinOpI (opr, i1, i2) => N.BinOpI (opr, f i1, f i2)
        | Ite (i1, i2, i3, r) => N.Ite (f i1, f i2, f i3, r)
        | TrueI r => N.TrueI r
        | FalseI r => N.FalseI r
        | TTI r => N.TTI r
        | IAbs (bs, Bind (name, i), r) => N.IAbs (no_uvar_bsort bs, Bind (name, f i), r)
        | AdmitI r =>
          raise Impossible "no_uvar_i () : shouldn't be AdmitI"
        | UVarI (_, r) =>
          raise impossible i
  in
    f i
  end

fun no_uvar_quan q =
  case q of
      Forall => Forall
    | Exists ins => Exists (Option.map (fn ins => fn i => ins $ nouvar2uvar_i i) ins)
                           
fun no_uvar_p p =
  case p of
      True r => N.True r
    | False r => N.False r
    | BinConn (opr, p1, p2) => N.BinConn (opr, no_uvar_p p1, no_uvar_p p2)
    | BinPred (opr, i1, i2) => N.BinPred (opr, no_uvar_i i1, no_uvar_i i2)
    | Not (p, r) => N.Not (no_uvar_p p, r)
    | Quan (q, bs, Bind (name, p), r) => N.Quan (no_uvar_quan q, no_uvar_bsort bs, Bind (name, no_uvar_p p), r)

end
