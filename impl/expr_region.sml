structure ExprRegion = struct
open Region
open Type
open Expr

fun get_region_i i =
    case i of
        VarI (_, r) => r
      | Tconst (_, r) => r
      | T0 r => r
      | T1 r => r
      | TrueI r => r
      | FalseI r => r
      | TTI r => r
      | Tadd (i1, i2) => combine_region (get_region_i i1) (get_region_i i2)
      | Tmult (i1, i2) => combine_region (get_region_i i1) (get_region_i i2)
      | Tmax (i1, i2) => combine_region (get_region_i i1) (get_region_i i2)
      | Tmin (i1, i2) => combine_region (get_region_i i1) (get_region_i i2)

fun get_region_p p = 
    case p of
        True r => r
      | False r => r
      | And (p1, p2) => combine_region (get_region_p p1) (get_region_p p2)
      | Or (p1, p2) => combine_region (get_region_p p1) (get_region_p p2)
      | Imply (p1, p2) => combine_region (get_region_p p1) (get_region_p p2)
      | Iff (p1, p2) => combine_region (get_region_p p1) (get_region_p p2)
      | Eq (i1, i2) => combine_region (get_region_i i1) (get_region_i i2)
      | TimeLe (i1, i2) => combine_region (get_region_i i1) (get_region_i i2)

fun get_region_s s = 
    case s of
        Basic (_, r) => r
      | Subset (_, (_, r), p) => combine_region r (get_region_p p)

fun get_region_t t = 
    case t of
        Arrow (t1, d, t2) => combine_region (get_region_t t1) (get_region_t t2)
      | Prod (t1, t2) => combine_region (get_region_t t1) (get_region_t t2)
      | Sum (t1, t2) => combine_region (get_region_t t1) (get_region_t t2)
      | Unit r => r
      | Uni ((_, r), t) => combine_region r (get_region_t t)
      | UniI (_, (_, r), t) => combine_region r (get_region_t t)
      | ExI (_, (_, r), t) => combine_region r (get_region_t t)
      | AppRecur (_, _, t, _, r) => r
      | AppV (_, _, _, r) => r
      | Int r => r

fun get_region_pn pn = 
    case pn of
        ConstrP (_, _, _, r) => r
      | VarP (_, r) => r
      | PairP (pn1, pn2) => combine_region (get_region_pn pn1) (get_region_pn pn2)
      | TTP r => r
      | AliasP (_, _, r) => r

fun get_region_e e = 
    case e of
        Var (_, r) => r
      | Abs (_, (_, r), e) => combine_region r (get_region_e e)
      | App (e1, e2) => combine_region (get_region_e e1) (get_region_e e2)
      | TT r => r
      | Pair (e1, e2) => combine_region (get_region_e e1) (get_region_e e2)
      | Fst e => get_region_e e
      | Snd e => get_region_e e
      | Inl (t, e) => combine_region (get_region_t t) (get_region_e e)
      | Inr (t, e) => combine_region (get_region_t t) (get_region_e e)
      | SumCase (e, _, _, _, e2) => combine_region (get_region_e e) (get_region_e e2)
      | AbsT ((_, r), e) => combine_region r (get_region_e e)
      | AppT (e, t) => combine_region (get_region_e e) (get_region_t t)
      | AbsI (_, (_, r), e) => combine_region r (get_region_e e)
      | AppI (e, i) => combine_region (get_region_e e) (get_region_i i)
      | Pack (t, _, e) => combine_region (get_region_t t) (get_region_e e)
      | Unpack (e1, _, _, _, e2) => combine_region (get_region_e e1) (get_region_e e2)
      | Fold (t, e) => combine_region (get_region_t t) (get_region_e e)
      | Unfold e => get_region_e e
      | Plus (e1, e2) => combine_region (get_region_e e1) (get_region_e e2)
      | Const (_, r) => r
      | AppConstr ((_, r), _, _, e) => combine_region r (get_region_e e)
      | Case (_, _, _, r) => r
      | Never t => get_region_t t
      | Let (_, _, r) => r
      | Fix (_, (_, r), e) => combine_region r (get_region_e e)
      | Ascription (e, t) => combine_region (get_region_e e) (get_region_t t)
      | AscriptionTime (e, i) => combine_region (get_region_e e) (get_region_i i)
 
fun get_region_rule (pn, e) = combine_region (get_region_pn pn) (get_region_e e)

fun get_region_dec dec =
    case dec of
        Val ((_, r), e) => combine_region r (get_region_e e)
      | Datatype (_, _, _, _, r) => r

end
