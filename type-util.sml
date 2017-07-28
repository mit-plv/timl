functor TypeUtilFn (Type : TYPE where type name = string * Region.region
                                           and type region = Region.region) = struct

open Type
open Bind
       
infixr 0 $

fun collect_UniI t =
  case t of
      UniI (s, Bind (name, t), _) =>
      let val (binds, t) = collect_UniI t
      in
        ((name, s) :: binds, t)
      end
    | _ => ([], t)

fun collect_Uni t =
  case t of
      Uni (Bind (name, t), _) =>
      let val (names, t) = collect_Uni t
      in
        (name :: names, t)
      end
    | Mono t => ([], t)

fun collect_MtAppI t =
  case t of
      MtAppI (t, i) =>
      let 
        val (f, args) = collect_MtAppI t
      in
        (f, args @ [i])
      end
    | _ => (t, [])
             
fun collect_MtApp t =
  case t of
      MtApp (t1, t2) =>
      let 
        val (f, args) = collect_MtApp t1
      in
        (f, args @ [t2])
      end
    | _ => (t, [])
             
fun is_MtApp_UVar t =
  let
    val (t, t_args) = collect_MtApp t
    val (t, i_args) = collect_MtAppI t
  in
    case t of
        UVar (x, r) => SOME ((x, r), i_args, t_args)
      | _ => NONE
  end
    
fun is_AppV t =
  let
    val (t, i_args) = collect_MtAppI t
    val (t, t_args) = collect_MtApp t
  in
    case t of
        MtVar x => SOME (x, t_args, i_args)
      | _ => NONE
  end
    
fun MtAppIs f args = foldl (fn (arg, f) => MtAppI (f, arg)) f args
fun MtApps f args = foldl (fn (arg, f) => MtApp (f, arg)) f args
                          
fun MtAbsMany (ctx, t, r) = foldl (fn ((name, k), t) => MtAbs (k, Bind ((name, r), t), r)) t ctx
fun MtAbsIMany (ctx, t, r) = foldl (fn ((name, s), t) => MtAbsI (s, Bind ((name, r), t), r)) t ctx
                                 
fun AppVar (x, is) = MtAppIs (MtVar x) is
fun AppV (x, ts, is, r) = MtAppIs (MtApps (MtVar x) ts) is

fun get_constr_inames (core : mtype constr_core) =
  let
    val (name_sorts, _) = unfold_binds core
  in
    map fst $ map fst name_sorts
  end
                                 
fun get_constr_names t =
  case t of
      TDatatype (Bind.Bind (name, tbinds), _) =>
      let
        val (_, (_, constr_decls)) = unfold_binds tbinds
        val cnames = map #1 constr_decls
      in
        cnames
      end
    | _ => []
      
end

