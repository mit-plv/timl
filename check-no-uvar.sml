structure CheckNoUVar = struct
structure N = NoUVarExpr
open Util
open Expr
open UVar
open VC

infixr 0 $
         
exception NoUVarError of string
                           
fun no_uvar_bsort bs =
  case bs of
      Base b => N.Base b
    | BSArrow (a, b) => N.BSArrow (no_uvar_bsort a, no_uvar_bsort b)
    | UVarBS x =>
      case !x of
          Refined a => no_uvar_bsort a
        | Fresh _ => raise NoUVarError $ str_bs bs

fun no_uvar_i i =
  let
    fun message i' = sprintf "\n$\nno_uvar_i (): $ shouldn't be UVarI in $" [str_region "" "" (get_region_i i'), str_i empty [] i', str_i empty [] i]
    fun f i =
      case i of
          VarI x => N.VarI x
        | IConst c => N.IConst c
        | UnOpI (opr, i, r) => N.UnOpI (opr, f i, r)
        | BinOpI (opr, i1, i2) => N.BinOpI (opr, f i1, f i2)
        | Ite (i1, i2, i3, r) => N.Ite (f i1, f i2, f i3, r)
        | IAbs (bs, Bind (name, i), r) => N.IAbs (no_uvar_bsort bs, Bind (name, f i), r)
        | UVarI (x, r) =>
          case !x of
              Refined a => no_uvar_i a
            | Fresh _ => raise NoUVarError $ message i
  in
    f i
  end

fun no_uvar_quan q =
  let
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
            | N.IConst c => IConst c
            | N.UnOpI (opr, i, r) => UnOpI (opr, f i, r)
            | N.BinOpI (opr, i1, i2) => BinOpI (opr, f i1, f i2)
            | N.Ite (i1, i2, i3, r) => Ite (f i1, f i2, f i3, r)
            | N.IAbs (bs, Bind (name, i), r) => IAbs (nouvar2uvar_bs bs, Bind (name, f i), r)
            | N.UVarI (u, _) => exfalso u
      in
        f i
      end
  in
    case q of
        Forall => Forall
      | Exists ins => Exists (Option.map (fn ins => fn i => ins $ nouvar2uvar_i i) ins)
  end
    
fun no_uvar_p p =
  case p of
      PTrueFalse b => N.PTrueFalse b
    | BinConn (opr, p1, p2) => N.BinConn (opr, no_uvar_p p1, no_uvar_p p2)
    | BinPred (opr, i1, i2) => N.BinPred (opr, no_uvar_i i1, no_uvar_i i2)
    | Not (p, r) => N.Not (no_uvar_p p, r)
    | Quan (q, bs, Bind (name, p), r) => N.Quan (no_uvar_quan q, no_uvar_bsort bs, Bind (name, no_uvar_p p), r)

fun no_uvar_hyp h =
  case h of
      VarH (name, b) => N.VarH (name, no_uvar_bsort b)
    | PropH p => N.PropH (no_uvar_p p)

fun no_uvar_vc ((hyps, p) : vc) : N.VC.vc =
  let
    val hyps = map no_uvar_hyp hyps
    val p = no_uvar_p p
  in
    (hyps, p)
  end

end
