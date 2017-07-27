structure MicroTiMLExUtil = struct

open Util
open Binders
open MicroTiMLEx

infixr 0 $

fun KArrows bs k = foldr KArrow k bs
fun KArrowTs ks k = foldr KArrowT k ks
fun KArrowTypes n k = KArrowTs (repeat n KType) k
                          
fun TExistsI bind = TQuanI (Exists (), bind)
fun TExistsIMany (ctx, t) = foldl (TExistsI o BindAnno) t ctx
fun TAbsIMany (ctx, t) = foldl (TAbsI o BindAnno) t ctx
fun TAbsTMany (ctx, t) = foldl (TAbsT o BindAnno) t ctx
fun TUni bind = TQuan (Forall, bind)
fun MakeTUni (name, k, t) = TUni $ BindAnno ((TName name, k), t)
fun TUniKind (name, t) = MakeTUni (name, KType, t)
fun TUniKindMany (names, t) = foldr TUniKind names t
                  
val TUnit = TConst TCUnit
val TEmpty = TConst TCEmpty
fun TSum (t1, t2) = TBinOp (TBSum, t1, t2)
fun TProd (t1, t2) = TBinOp (TBProd, t1, t2)
fun TAppIs (t, is) = foldl (swap TAppI) t is
fun TAppTs (t, ts) = foldl (swap TAppT) t ts
         
fun MakeEAbsT (name, k, e) = EAbsT $ BindAnno ((TName name, k), e)
fun MakeERec (name, t, e) = ERec $ BindAnno ((EName name, t), e)
fun EAbsTKind (name, e) = MakeEAbsT (name, KType, e) 
fun EAbsTKindMany (names, e) = foldr EAbsTKind e names

fun EInlInr (opr, t, e) = EUnOp (EUInj (opr, t), e)
fun EInl (t, e) = EInlInr (InjInl, t, e)
fun EInr (t, e) = EInlInr (InjInr, t, e)
fun EFold (t, e) = EUnOp (EUFold t, e)

end
                                 
