functor IdxGetRegionFn (structure Idx : IDX where type region = Region.region
                      val get_region_var : Idx.var -> Region.region
                      val set_region_var : Idx.var -> Region.region -> Idx.var
                     ) = struct

open Idx
open Region
open Util

infixr 0 $
         
fun get_region_i i =
  case i of
      VarI x => get_region_var x
    | IConst (_, r) => r
    | UnOpI (_, _, r) => r
    | BinOpI (_, i1, i2) => combine_region (get_region_i i1) (get_region_i i2)
    | Ite (_, _, _, r) => r
    | IAbs (_, _, r) => r
    | UVarI (_, r) => r

fun set_region_i i r =
  case i of
      VarI x => VarI $ set_region_var x r
    | IConst (a, _) => IConst (a, r)
    | UnOpI (opr, i, _) => UnOpI (opr, i, r)
    | BinOpI (opr, i1, i2) => BinOpI (opr, set_region_i i1 r, set_region_i i2 r)
    | Ite (i1, i2, i3, _) => Ite (i1, i2, i3, r)
    | IAbs (name, i, _) => IAbs (name, i, r)
    | UVarI (a, _) => UVarI (a, r)

fun get_region_p p = 
  case p of
      PTrueFalse (_, r) => r
    | Not (_, r) => r
    | BinConn (_, p1, p2) => combine_region (get_region_p p1) (get_region_p p2)
    | BinPred (_, i1, i2) => combine_region (get_region_i i1) (get_region_i i2)
    | Quan (_, _, _, r) => r

fun set_region_p p r = 
  case p of
      PTrueFalse (b, _) => PTrueFalse (b, r)
    | Not (p, _) => Not (p, r)
    | BinConn (opr, p1, p2) => BinConn (opr, set_region_p p1 r, set_region_p p2 r)
    | BinPred (opr, i1, i2) => BinPred (opr, set_region_i i1 r, set_region_i i2 r)
    | Quan (q, bs, bind, _) => Quan (q, bs, bind, r)

fun get_region_s s = 
  case s of
      Basic (_, r) => r
    | Subset (_, _, r) => r
    | UVarS (_, r) => r
    | SAbs (_, _, r) => r
    | SApp (s, i) => combine_region (get_region_s s) (get_region_i i)

end

functor TypeGetRegionFn (structure Type : TYPE where type region = Region.region
                       val get_region_var : Type.var -> Region.region
                       val get_region_i : Type.idx -> Region.region
                      ) = struct

open Type
open Region
open Util

infixr 0 $
         
fun get_region_mt t = 
  case t of
      Arrow (t1, d, t2) => combine_region (get_region_mt t1) (get_region_mt t2)
    | TyNat (_, r) => r
    | TyArray (t, i) => combine_region (get_region_mt t) (get_region_i i)
    | Unit r => r
    | Prod (t1, t2) => combine_region (get_region_mt t1) (get_region_mt t2)
    | UniI (_, _, r) => r
    | MtVar y => get_region_var y
    | MtApp (t1, t2) => combine_region (get_region_mt t1) (get_region_mt t2)
    | MtAbs (_, _, r) => r
    | MtAppI (t, i) => combine_region (get_region_mt t) (get_region_i i)
    | MtAbsI (_, _, r) => r
    | BaseType (_, r) => r
    | UVar (_, r) => r
    | TDatatype (_, r) => r

fun get_region_t t = 
  case t of
      Mono t => get_region_mt t
    | Uni (_, r) => r

end
