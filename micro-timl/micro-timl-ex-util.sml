structure MicroTiMLExUtil = struct

open Util
open Binders
open MicroTiMLEx

infixr 0 $

fun KArrows bs k = foldr KArrow k bs
fun KArrowTs ks k = foldr KArrowT k ks
fun KArrowTypes n k = KArrowTs (repeat n KType) k
                          
fun TExistsI bind = TQuanI (Exists (), bind)
fun TExistsI_Many (ctx, t) = foldr (TExistsI o BindAnno) t ctx
fun MakeTExistsI (name, s, t) = TExistsI $ IBindAnno ((name, s), t)
fun TAbsI_Many (ctx, t) = foldr (TAbsI o BindAnno) t ctx
fun TAbsT_Many (ctx, t) = foldr (TAbsT o BindAnno) t ctx
fun TUni bind = TQuan (Forall, bind)
fun MakeTUni (name, k, t) = TUni $ TBindAnno ((name, k), t)
fun TUniKind (name, t) = MakeTUni (name, KType, t)
fun TUniKind_Many (names, t) = foldr TUniKind t names
                  
val TUnit = TConst TCUnit
val TEmpty = TConst TCEmpty
fun TSum (t1, t2) = TBinOp (TBSum, t1, t2)
fun TProd (t1, t2) = TBinOp (TBProd, t1, t2)
fun TAppIs (t, is) = foldl (swap TAppI) t is
fun TAppTs (t, ts) = foldl (swap TAppT) t ts
         
fun EFst e = EUnOp (EUProj ProjFst, e)
fun ESnd e = EUnOp (EUProj ProjSnd, e)
fun EInlInr (opr, t, e) = EUnOp (EUInj (opr, t), e)
fun EInl (t, e) = EInlInr (InjInl, t, e)
fun EInr (t, e) = EInlInr (InjInr, t, e)
fun EFold (t, e) = EUnOp (EUFold t, e)
fun EUnfold e = EUnOp (EUUnfold, e)

fun MakeEAbsT (name, k, e) = EAbsT $ TBindAnno ((name, k), e)
fun MakeERec (name, t, e) = ERec $ EBindAnno ((name, t), e)
fun EAbsTKind (name, e) = MakeEAbsT (name, KType, e) 
fun EAbsTKind_Many (names, e) = foldr EAbsTKind e names
fun MakeEUnpackI (e1, iname, ename, e2) = EUnpackI (e1, IBind (iname, EBind (ename, e2)))
fun MakeELet (e1, name, e2) = ELet (e1, EBind (name, e2))
fun MakeELetIdx (i, name, e) = ELetIdx (i, IBind (name, e))
fun MakeELetType (t, name, e) = ELetType (t, TBind (name, e))
fun MakeELetConstr (e1, name, e2) = ELetConstr (e1, CBind (name, e2))
fun MakeEAbsConstr (tnames, inames, ename, e) = EAbsConstr $ Bind ((map TBinder tnames, map IBinder inames, EBinder ename), e)

end
                                 
