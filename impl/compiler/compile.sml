structure Compile =
struct
  open OS.Process
  open OS.Path
  open Util
  structure O = Option
  structure PTC = PreTypeCheck
  structure UE = UnderscoredExpr
  structure E = Expr

  infixr 0 $

  fun shift_mod_projectible_in_long_id d c (m, id) =
    (case m of
       SOME (i, r) => SOME (if i >= c then i + d else i, r)
     | NONE => NONE, id)

  fun shift_mod_projectible_in_idx_above d c i =
    let
      fun inner i =
        case i of
          UE.VarI lid => UE.VarI (shift_mod_projectible_in_long_id d c lid)
        | UE.UnOpI (uop, i1, r) => UE.UnOpI (uop, inner i1, r)
        | UE.DivI (i1, a) => UE.DivI (inner i1, a)
        | UE.ExpI (i1, a) => UE.ExpI (inner i1, a)
        | UE.BinOpI (bop, i1, i2) => UE.BinOpI (bop, inner i1, inner i2)
        | UE.Ite (i1, i2, i3, r) => UE.Ite (inner i1, inner i2, inner i3, r)
        | UE.TimeAbs (n, i1, r) => UE.TimeAbs (n, inner i1, r)
        | _ => i
    in
      inner i
    end

  fun shift_mod_projectible_in_prop_above d c p =
    let
      fun inner p =
        case p of
          UE.BinPred (pred, i1, i2) => UE.BinPred (pred, shift_mod_projectible_in_idx_above d c i1, shift_mod_projectible_in_idx_above d c i2)
          (* TODO: UE.Quan *)
        | _ => p
    in
      inner p
    end

  fun shift_mod_projectible_in_sort_above d c s =
    let
      fun inner s =
        case s of
          (* TODO: UE.Subset *)
          _ => s
    in
      inner s
    end

  fun shift_mod_projectible_in_kind_above d c k =
    let
      fun inner k =
        case k of
          UE.ArrowK (is_data, i, sl) => UE.ArrowK (is_data, i, map (shift_mod_projectible_in_sort_above d c) sl)
    in
      inner k
    end

  fun shift_mod_projectible_in_mtype_above d c mt =
    let
      fun inner mt =
        case mt of
          UE.Arrow (mt1, i, mt2) => UE.Arrow (inner mt1, shift_mod_projectible_in_idx_above d c i, inner mt2)
        | UE.TyNat (i, r) => UE.TyNat (shift_mod_projectible_in_idx_above d c i, r)
        | UE.TyArray (mt1, i) => UE.TyArray (inner mt1, shift_mod_projectible_in_idx_above d c i)
        | UE.Prod (mt1, mt2) => UE.Prod (inner mt1, inner mt2)
        (* TODO: UE.UniI *)
        | UE.AppV (lid, mtl, il, r) => UE.AppV (shift_mod_projectible_in_long_id d c lid, map inner mtl, map (shift_mod_projectible_in_idx_above d c) il, r)
        | _ => mt
    in
      inner mt
    end

  fun shift_mod_projectible_in_ty_above d c t =
    let
      fun inner t =
        case t of
          UE.Mono mt => UE.Mono (shift_mod_projectible_in_mtype_above d c mt)
          (* TODO: UE.Uni *)
        | _ => t
    in
      inner t
    end

  fun shift_mod_projectible_in_ptrn_above d c p =
    let
      fun inner p =
        case p of
          UE.ConstrP (((m, id), b), strs, op1, r) =>
            UE.ConstrP (((case m of SOME (i, r) => SOME (if i >= c then i + d else i, r) | NONE => NONE, id), b), strs, O.map inner op1, r)
        | UE.PairP (p1, p2) => UE.PairP (inner p1, inner p2)
        | UE.AliasP (n, p1, r) => UE.AliasP (n, inner p1, r)
        | UE.AnnoP (p1, mt) => UE.AnnoP (inner p1, shift_mod_projectible_in_mtype_above d c mt)
        | _ => p
    in
      inner p
    end

  fun shift_mod_projectible_in_expr_above d c e =
    let
      fun inner e =
        case e of
          UE.Var (lid, b) => UE.Var (shift_mod_projectible_in_long_id d c lid, b)
        | UE.App (e1, e2) => UE.App (inner e1, inner e2)
        | UE.Abs (p, e1) => UE.Abs (p, inner e1)
        | UE.Pair (e1, e2) => UE.Pair (inner e1, inner e2)
        | UE.Fst e1 => UE.Fst (inner e1)
        | UE.Snd e1 => UE.Snd (inner e1)
        | UE.AbsI (s, n, e1, r) => UE.AbsI (shift_mod_projectible_in_sort_above d c s, n, inner e1, r)
        | UE.AppI (e1, i) => UE.AppI (inner e1, shift_mod_projectible_in_idx_above d c i)
        | UE.BinOp (bop, e1, e2) => UE.BinOp (bop, inner e1, inner e2)
        | UE.TriOp (top, e1, e2, e3) => UE.TriOp (top, inner e1, inner e2, inner e3)
        | UE.AppConstr ((lid, b), il, e1) => UE.AppConstr ((shift_mod_projectible_in_long_id d c lid, b), map (shift_mod_projectible_in_idx_above d c) il, inner e1)
        (* TODO: UE.Case UE.Let *)
        | UE.Ascription (e1, mt) => UE.Ascription (inner e1, shift_mod_projectible_in_mtype_above d c mt)
        | UE.AscriptionTime (e1, i) => UE.AscriptionTime (inner e1, shift_mod_projectible_in_idx_above d c i)
        | UE.Never (mt, r) => UE.Never (shift_mod_projectible_in_mtype_above d c mt, r)
        | UE.Builtin (mt, r) => UE.Builtin (shift_mod_projectible_in_mtype_above d c mt, r)
        | _ => e
    in
      inner e
    end

  and shift_mod_projectible_in_decl_above d c dec =
    let
      fun inner dec =
        case dec of
          UE.Val (ns, p, e, r) => UE.Val (ns, shift_mod_projectible_in_ptrn_above d c p, shift_mod_projectible_in_expr_above d c e, r)
          (* TODO: UE.Rec UE.datatype *)
        | UE.IdxDef (n, s, i) => UE.IdxDef (n, shift_mod_projectible_in_sort_above d c s, shift_mod_projectible_in_idx_above d c i)
        | UE.AbsIdx2 (n, s, i) => UE.AbsIdx2 (n, shift_mod_projectible_in_sort_above d c s, shift_mod_projectible_in_idx_above d c i)
        | UE.AbsIdx ((n, s, i), decs, r) => UE.AbsIdx ((n, shift_mod_projectible_in_sort_above d c s, shift_mod_projectible_in_idx_above d c i), map inner decs, r)
        | UE.TypeDef (n, mt) => UE.TypeDef (n, shift_mod_projectible_in_mtype_above d c mt)
        | UE.Open (i, r) => UE.Open (if i >= c then i + d else i, r)
        | _ => dec
    in
      inner dec
    end

  fun elim_functors (prog : UE.prog) : UE.prog =
    let
      fun iter (top_bind : UE.top_bind, cur_prog : UE.prog) : UE.prog =
        on_top_bind cur_prog top_bind
    in
      foldr iter [] prog
    end

  and on_top_bind (cur_prog : UE.prog) (top_bind : UE.top_bind) : UE.prog  =
    case top_bind of
      UE.TopModBind _ => top_bind :: cur_prog
    | UE.TopFunctorBind _ => top_bind :: cur_prog
    | UE.TopFunctorApp ((name, _), f, m) =>
        let
          fun lookup_functor (cur_prog : UE.prog) (m : UE.var) =
            let
              fun iter (bind, (nsig, target)) =
                case bind of
                  UE.TopModBind _ => Continue (nsig + 1, target)
                | UE.TopFunctorBind a =>
                    if target <= 0 then
                      ShortCircuit (nsig, a)
                    else
                      Continue (nsig, target - 1)
                | _ => raise (Impossible "Compile.on_top_bind")
              fun find_first (m : UE.var) = is_ShortCircuit $ foldlM_Error iter (0, m) cur_prog
            in
              case find_first m of
                SOME (n, (fname, (mname, msign), fmodu)) => (* TODO SOME (name, (PTC.shiftx_snd PTC.shiftx_m_ctx 0 n arg, PTC.shiftx_m_ctx 1 n body))*) (println $ fst fname; println $ fst mname; NONE)
              | NONE => NONE
            end
          fun fetch_functor (cur_prog : UE.prog) ((m, r) : UE.id) =
            case lookup_functor cur_prog m of
              SOME a => a
            | NONE => raise (Impossible "Compile.on_top_bind")
          val _ = fetch_functor cur_prog f
          (*val (_, ((_, formal_arg), body)) = fetch_functor gctx f*)
        in
          (println name; println $ str_int $ fst f; println $ str_int $ fst m; top_bind :: cur_prog)
        end

  fun main (prog_name : string, args : string list) : int =
    let
      val result =
        if length args < 2 then
          (println "Usage: THIS main filename1 [filename2 ...]"; exit failure)
        else
          TiML.main $ tl args
      val prog : UE.prog = #1 result
      val gctx : PTC.sigcontext = #2 result
      val admits : (string * E.prop) list = #3 result
      val entry : string = hd args
      val (mod_name, func_name) =
        let
          val base_ext = splitBaseExt entry
          val base = #base base_ext
          val ext = #ext base_ext
        in
          case ext of
            SOME ext => (base, ext)
          | NONE => (println $ entry ^ " should be like Main.main"; exit failure)
        end
      val entry_is_legal = List.exists (fn (k, v) =>
        if k = mod_name then
          case v of
            PTC.Sig (_, _, _, tctx) => List.exists (fn (k, v) =>
              if k = func_name then
                case v of
                  E.Mono (E.Arrow (E.Unit _, _, E.BaseType (E.Int, _))) => true
                | _ => false
              else
                false) tctx
          | PTC.FunctorBind _ => false
        else
          false) gctx
      val () =
        case entry_is_legal of
          true => ()
        | false => (println $ entry ^ " does not exist or not have type unit -> int"; exit failure)
      val early_passes = elim_functors
      val prog = early_passes prog
    in
      0
    end
      handle TiML.Error msg => (println msg; 1)
           | IO.Io e => (println (sprintf "IO Error doing $ on $" [#function e, #name e]); 1)
           | Impossible msg => (println $ "Impossible: " ^ msg; 1)
           | E.ModuleUVar msg => (println $ "ModuleUVar: " ^ msg; 1)
           | _ => (println "Internal Error"; 1)
end
