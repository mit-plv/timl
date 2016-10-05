structure DerivationPasses =
struct
  open MicroTiML
  open Util

  structure TypingDerivationShift =
  struct
    structure TypingDerivationShiftHelper =
    struct
      type down = int * context
      type up = unit

      val upward_base = ()
      fun combiner ((), ()) = ()

      fun shift_context_above delta dep ctx =
        let
          val (left, right) = List.splitAt (ctx, dep)
        in
          List.concat [left, delta, right]
        end

      fun on_typing_relation ((ctx, tm, ty, ti), (dep, delta)) =
        let
          val ctx' = shift_context_above delta dep ctx
          val tm' = Passes.TermShift.shift_term_above (List.length delta) dep tm
          val ty' = Passes.TermShift.shift_constr_above (List.length delta) dep ty
          val ti' = Passes.TermShift.shift_constr_above (List.length delta) dep ti
        in
          (ctx', tm', ty', ti')
        end

      fun on_kinding_relation ((ctx, cstr, kd), (dep, delta)) =
        let
          val ctx' = shift_context_above delta dep ctx
          val cstr' = Passes.TermShift.shift_constr_above (List.length delta) dep cstr
          val kd' = Passes.TermShift.shift_kind_above (List.length delta) dep kd
        in
          (ctx', cstr', kd')
        end

      fun on_proping_relation ((ctx, pr), (dep, delta)) =
        let
          val ctx' = shift_context_above delta dep ctx
          val pr' = Passes.TermShift.shift_prop_above (List.length delta) dep pr
        in
          (ctx', pr')
        end

      fun on_kind_wellformness_relation ((ctx, kd), (dep, delta)) =
        let
          val ctx' = shift_context_above delta dep ctx
          val kd' = Passes.TermShift.shift_kind_above (List.length delta) dep kd
        in
          (ctx', kd')
        end

      fun on_prop_wellformness_relation ((ctx, pr), (dep, delta)) =
        let
          val ctx' = shift_context_above delta dep ctx
          val pr' = Passes.TermShift.shift_prop_above (List.length delta) dep pr
        in
          (ctx', pr')
        end

      fun transformer_typing_derivation (on_tyderiv, on_kdderiv, on_prderiv, on_kdwf) (tyderiv : typing_derivation, down as (dep, delta) : down) =
        let
          fun on_rel tyrel = on_typing_relation (tyrel, down)
        in
          case tyderiv of
            TyDerivAbs (tyrel, kdderiv1, tyderiv2) =>
              let
                val (kdderiv1, ()) = on_kdderiv (kdderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (dep + 1, delta))
              in
                SOME (TyDerivAbs (on_rel tyrel, kdderiv1, tyderiv2), ())
              end
          | TyDerivRec (tyrel, kdderiv1, tyderiv2) =>
              let
                val (kdderiv1, ()) = on_kdderiv (kdderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (dep + 1, delta))
              in
                SOME (TyDerivRec (on_rel tyrel, kdderiv1, tyderiv2), ())
              end
          | TyDerivCase (tyrel, tyderiv1, tyderiv2, tyderiv3) =>
              let
                val (tyderiv1, ()) = on_tyderiv (tyderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (dep + 1, delta))
                val (tyderiv3, ()) = on_tyderiv (tyderiv3, (dep + 1, delta))
              in
                SOME (TyDerivCase (on_rel tyrel, tyderiv1, tyderiv2, tyderiv3), ())
              end
          | TyDerivUnpack (tyrel, tyderiv1, tyderiv2) =>
              let
                val (tyderiv1, ()) = on_tyderiv (tyderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (dep + 2, delta))
              in
                 SOME (TyDerivUnpack (on_rel tyrel, tyderiv1, tyderiv2), ())
              end
          | TyDerivCstrAbs (tyrel, kdwf1, tyderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (dep + 1, delta))
              in
                SOME (TyDerivCstrAbs (on_rel tyrel, kdwf1, tyderiv2), ())
              end
          | TyDerivLet (tyrel, tyderiv1, tyderiv2) =>
              let
                val (tyderiv1, ()) = on_tyderiv (tyderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (dep + 1, delta))
              in
                SOME (TyDerivLet (on_rel tyrel, tyderiv1, tyderiv2), ())
              end
          | _ => NONE
        end

      fun transformer_kinding_derivation (on_kdderiv, on_prderiv, on_kdwf) (kdderiv : kinding_derivation, down as (dep, delta) : down) =
        let
          fun on_rel kdrel = on_kinding_relation (kdrel, down)
        in
          case kdderiv of
            KdDerivRefine (kdrel, kdderiv1, prderiv2) =>
              let
                val (kdderiv1, ()) = on_kdderiv (kdderiv1, down)
                val (prderiv2, ()) = on_prderiv (prderiv2, (dep + 1, delta))
              in
                SOME (KdDerivRefine (on_rel kdrel, kdderiv1, prderiv2), ())
              end
          | KdDerivTimeAbs (kdrel, kdderiv1) =>
              let
                val (kdderiv1, ()) = on_kdderiv (kdderiv1, (dep + 1, delta))
              in
                SOME (KdDerivTimeAbs (on_rel kdrel, kdderiv1), ())
              end
          | KdDerivAbs (kdrel, kdwf1, kdderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (kdderiv2, ()) = on_kdderiv (kdderiv2, (dep + 1, delta))
              in
                SOME (KdDerivAbs (on_rel kdrel, kdwf1, kdderiv2), ())
              end
          | KdDerivForall (kdrel, kdwf1, kdderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (kdderiv2, ()) = on_kdderiv (kdderiv2, (dep + 1, delta))
              in
                SOME (KdDerivForall (on_rel kdrel, kdwf1, kdderiv2), ())
              end
          | KdDerivExists (kdrel, kdwf1, kdderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (kdderiv2, ()) = on_kdderiv (kdderiv2, (dep + 1, delta))
              in
                SOME (KdDerivExists (on_rel kdrel, kdwf1, kdderiv2), ())
              end
          | KdDerivRec (kdrel, kdwf1, kdderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (kdderiv2, ()) = on_kdderiv (kdderiv2, (dep + 1, delta))
              in
                SOME (KdDerivRec (on_rel kdrel, kdwf1, kdderiv2), ())
              end
          | _ => NONE
        end

      fun transformer_proping_derivation _ = NONE

      fun transformer_kind_wellformness_derivation (on_kdwf, on_prwf) (kdwf : kind_wellformedness_derivation, down as (dep, delta) : down) =
        let
          fun on_rel kdrel = on_kind_wellformness_relation (kdrel, down)
        in
          case kdwf of
            KdWfDerivSubset (kdrel, kdwf1, prwf2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (prwf2, ()) = on_prwf (prwf2, (dep + 1, delta))
              in
                SOME (KdWfDerivSubset (on_rel kdrel, kdwf1, prwf2), ())
              end
          | _ => NONE
        end

      fun transformer_prop_wellformness_derivation (on_prwf, on_kdwf, on_kdderiv) (prwf : prop_wellformedness_derivation, down as (dep, delta) : down) =
        let
          fun on_rel prrel = on_prop_wellformness_relation (prrel, down)
        in
          case prwf of
            PrWfDerivForall (prrel, kdwf1, prwf2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (prwf2, ()) = on_prwf (prwf2, (dep + 1, delta))
              in
                SOME (PrWfDerivForall (on_rel prrel, kdwf1, prwf2), ())
              end
          | PrWfDerivExists (prrel, kdwf1, prwf2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (prwf2, ()) = on_prwf (prwf2, (dep + 1, delta))
              in
                SOME (PrWfDerivExists (on_rel prrel, kdwf1, prwf2), ())
              end
          | _ => NONE
        end
    end

    structure TypingDerivationShiftIns = TypingDerivationTransformPass(TypingDerivationShiftHelper)
    open TypingDerivationShiftIns

    fun shift_typing_derivation_above delta dep tyderiv = #1 (transform_typing_derivation (tyderiv, (dep, delta)))
  end

  structure ANF =
  struct
    open TypingDerivationShift
    exception Impossible

    fun extract_tyrel tyderiv =
      case tyderiv of
        TyDerivVar rel => rel
      | TyDerivInt rel => rel
      | TyDerivNat rel => rel
      | TyDerivUnit rel => rel
      | TyDerivApp (rel, _, _) => rel
      | TyDerivAbs (rel, _, _) => rel
      | TyDerivRec (rel, _, _) => rel
      | TyDerivPair (rel, _, _) => rel
      | TyDerivFst (rel, _) => rel
      | TyDerivSnd (rel, _) => rel
      | TyDerivInLeft (rel, _, _) => rel
      | TyDerivInRight (rel, _, _) => rel
      | TyDerivCase (rel, _, _, _) => rel
      | TyDerivFold (rel, _, _) => rel
      | TyDerivUnfold (rel, _) => rel
      | TyDerivPack (rel, _, _, _) => rel
      | TyDerivUnpack (rel, _, _) => rel
      | TyDerivCstrAbs (rel, _, _) => rel
      | TyDerivCstrApp (rel, _, _) => rel
      | TyDerivBinOp (rel, _, _) => rel
      | TyDerivArrayNew (rel, _, _) => rel
      | TyDerivArrayGet (rel, _, _, _) => rel
      | TyDerivArrayPut (rel, _, _, _, _) => rel
      | TyDerivLet (rel, _, _) => rel
      | TyDerivNever (rel, _) => rel

    fun extract_cstr_arrow (_, _, CstrArrow r, _) = r
      | extract_cstr_arrow _ = raise Impossible

    fun normalize_derivation tyderiv = normalize tyderiv (fn (x, d) => x)

    and normalize tyderiv k =
      case tyderiv of
        TyDerivVar _ => k (tyderiv, [])
      | TyDerivInt _ => k (tyderiv, [])
      | TyDerivNat _ => k (tyderiv, [])
      | TyDerivUnit _ => k (tyderiv, [])
      | TyDerivApp (tyrel, tyderiv1, tyderiv2) =>
          normalize_shift tyderiv1 (fn (tyderiv1, d1) =>
            normalize_shift (shift_typing_derivation_above d1 0 tyderiv2) (fn (tyderiv2, d2) =>
              let
                val tyderiv1 = shift_typing_derivation_above d2 0 tyderiv1
                val tyrel1 = extract_tyrel tyderiv1
                val tyrel2 = extract_tyrel tyderiv2
                val (ty1, ty2, ti) = extract_cstr_arrow tyrel
                val tyrel = (#1 tyrel2, TmApp (#2 tyrel1, #2 tyrel2), ty2, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, #4 tyrel1, #4 tyrel2), CstrNat 1), ti))
              in
                k (TyDerivApp (tyrel, tyderiv1, tyderiv2), List.concat [d2, d1])
              end))
      | _ => raise Impossible

    and normalize_shift tyderiv k =
      normalize tyderiv (fn (tyderiv, d) =>
        let
          val tyrel = extract_tyrel tyderiv
        in
          if Passes.ANF.is_value (#2 tyrel) then
            k (tyderiv, d)
          else
            let
              val ty = #3 tyrel
              val tyrel' = (BdType ty :: (#1 tyrel), TmVar 0, ty, CstrNat 0)
              val tyderiv' = TyDerivVar tyrel'
              val res = k (tyderiv', BdType ty :: d)
              val tyrel'' = extract_tyrel res
              val tm = TmLet (#2 tyrel, #2 tyrel'')
              val tyrel''' = (#1 tyrel, tm, #3 tyrel'', CstrBinOp (CstrBopAdd, #4 tyrel, #4 tyrel''))
              val tyderiv'' = TyDerivLet (tyrel''', tyderiv, res)
            in
              tyderiv''
            end
        end)
  end
end
