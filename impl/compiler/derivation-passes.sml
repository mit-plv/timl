structure DerivationPassesUtil =
struct
  open MicroTiML

  fun reconstruct_ty_deriv_abs tyrel kdderiv1 tyderiv2 =
    let
      val kdrel1 = extract_kdrel kdderiv1
      val tyrel2 = extract_tyrel tyderiv2
      val tyrel_new = (#1 kdrel1, TmAbs (#2 kdrel1, #2 tyrel2), CstrArrow (#2 kdrel1, Passes.TermShift.shift_constr ~1 (#3 tyrel2), Passes.TermShift.shift_constr ~1 (#4 tyrel2)), CstrTime "0.0")
    in
      TyDerivAbs (tyrel_new, kdderiv1, tyderiv2)
    end

  fun reconstruct_ty_deriv_rec tyrel kdderiv1 tyderiv2 =
    let
      val kdrel1 = extract_kdrel kdderiv1
      val tyrel2 = extract_tyrel tyderiv2
      val tyrel_new = (#1 kdrel1, TmRec (#2 kdrel1, #2 tyrel2), #2 kdrel1, CstrTime "0.0")
    in
      TyDerivRec (tyrel_new, kdderiv1, tyderiv2)
    end

  fun reconstruct_ty_deriv_case tyrel tyderiv1 tyderiv2 tyderiv3 =
    let
      val tyrel1 = extract_tyrel tyderiv1
      val tyrel2 = extract_tyrel tyderiv2
      val tyrel3 = extract_tyrel tyderiv3
      val tyrel_new = (#1 tyrel1, TmCase (#2 tyrel1, #2 tyrel2, #2 tyrel3), Passes.TermShift.shift_constr ~1 (#3 tyrel2), CstrBinOp (CstrBopAdd, #4 tyrel1, CstrBinOp (CstrBopMax, Passes.TermShift.shift_constr ~1 (#4 tyrel2), Passes.TermShift.shift_constr ~1 (#4 tyrel3))))
    in
      TyDerivCase (tyrel_new, tyderiv1, tyderiv2, tyderiv3)
    end

  fun reconstruct_ty_deriv_unpack tyrel tyderiv1 tyderiv2 =
    let
      val tyrel1 = extract_tyrel tyderiv1
      val tyrel2 = extract_tyrel tyderiv2
      val tyrel_new = (#1 tyrel1, TmUnpack (#2 tyrel1, #2 tyrel2), Passes.TermShift.shift_constr ~2 (#3 tyrel2), Passes.TermShift.shift_constr ~2 (#4 tyrel2))
    in
      TyDerivUnpack (tyrel_new, tyderiv1, tyderiv2)
    end

  fun reconstruct_ty_deriv_cstr_abs tyrel kdwf1 tyderiv2 =
    let
      val kdwfrel1 = extract_kdwfrel kdwf1
      val tyrel2 = extract_tyrel tyderiv2
      val tyrel_new = (#1 kdwfrel1, TmCstrAbs (#2 kdwfrel1, #2 tyrel2), CstrForall (#2 kdwfrel1, #3 tyrel2), CstrTime "0.0")
    in
      TyDerivCstrAbs (tyrel_new, kdwf1, tyderiv2)
    end

  fun reconstruct_ty_deriv_let tyrel tyderiv2 tyderiv3 =
    let
      val tyrel2 = extract_tyrel tyderiv2
      val tyrel3 = extract_tyrel tyderiv3
      val tyrel_new = (#1 tyrel2, TmLet (#2 tyrel2, #2 tyrel3), Passes.TermShift.shift_constr ~1 (#3 tyrel3), CstrBinOp (CstrBopAdd, #4 tyrel2, Passes.TermShift.shift_constr ~1 (#4 tyrel3)))
    in
      TyDerivLet (tyrel_new, tyderiv2, tyderiv3)
    end

  fun reconstruct_kd_deriv_refine kdrel kdderiv1 prderiv2 =
    let
      val kdrel1 = extract_kdrel kdderiv1
      val prrel2 = extract_prrel prderiv2
      val kdrel_new = (#1 kdrel1, #2 kdrel1, KdSubset (#3 kdrel1, #2 prrel2))
    in
      KdDerivRefine (kdrel_new, kdderiv1, prderiv2)
    end

  fun reconstruct_kd_deriv_time_abs kdrel kdderiv1 =
    let
      val kdrel1 = extract_kdrel kdderiv1
      val kdrel_new = (#1 kdrel1, CstrTimeAbs (#2 kdrel1), KdTimeFun (extract_kd_time_fun (#3 kdrel1) + 1))
    in
      KdDerivTimeAbs (kdrel_new, kdderiv1)
    end

  fun reconstruct_kd_deriv_abs kdrel kdwf1 kdderiv2 =
    let
      val kdwfrel1 = extract_kdwfrel kdwf1
      val kdrel2 = extract_kdrel kdderiv2
      val kdrel_new = (#1 kdwfrel1, CstrAbs (#2 kdwfrel1, #2 kdrel2), KdArrow (#2 kdwfrel1, Passes.TermShift.shift_kind ~1 (#3 kdrel2)))
    in
      KdDerivAbs (kdrel_new, kdwf1, kdderiv2)
    end

  fun reconstruct_kd_deriv_forall kdrel kdwf1 kdderiv2 =
    let
      val kdwfrel1 = extract_kdwfrel kdwf1
      val kdrel2 = extract_kdrel kdderiv2
      val kdrel_new = (#1 kdwfrel1, CstrForall (#2 kdwfrel1, #2 kdrel2), KdProper)
    in
      KdDerivForall (kdrel_new, kdwf1, kdderiv2)
    end

  fun reconstruct_kd_deriv_exists kdrel kdwf1 kdderiv2 =
    let
      val kdwfrel1 = extract_kdwfrel kdwf1
      val kdrel2 = extract_kdrel kdderiv2
      val kdrel_new = (#1 kdwfrel1, CstrExists (#2 kdwfrel1, #2 kdrel2), KdProper)
    in
      KdDerivExists (kdrel_new, kdwf1, kdderiv2)
    end

  fun reconstruct_kd_deriv_rec kdrel kdwf1 kdderiv2 =
    let
      val kdwfrel1 = extract_kdwfrel kdwf1
      val kdrel2 = extract_kdrel kdderiv2
      val kdrel_new = (#1 kdwfrel1, CstrRec (#2 kdwfrel1, #2 kdrel2), #2 kdwfrel1)
    in
      KdDerivRec (kdrel_new, kdwf1, kdderiv2)
    end

  fun reconstrct_kd_wf_deriv_subset kdrel kdwf1 prwf2 =
    let
      val kdwfrel1 = extract_kdwfrel kdwf1
      val prwfrel2 = extract_prwfrel prwf2
      val kdrel_new = (#1 kdwfrel1, KdSubset (#2 kdwfrel1, #2 prwfrel2))
    in
      KdWfDerivSubset (kdrel_new, kdwf1, prwf2)
    end

  fun reconstruct_pr_wf_deriv_forall prrel kdwf1 prwf2 =
    let
      val kdwfrel1 = extract_kdwfrel kdwf1
      val prwfrel2 = extract_prwfrel prwf2
      val prrel_new = (#1 kdwfrel1, PrForall (#2 kdwfrel1, #2 prwfrel2))
    in
      PrWfDerivForall (prrel_new, kdwf1, prwf2)
    end

  fun reconstruct_pr_wf_deriv_exists prrel kdwf1 prwf2 =
    let
      val kdwfrel1 = extract_kdwfrel kdwf1
      val prwfrel2 = extract_prwfrel prwf2
      val prrel_new = (#1 kdwfrel1, PrExists (#2 kdwfrel1, #2 prwfrel2))
    in
      PrWfDerivExists (prrel_new, kdwf1, prwf2)
    end

  fun reconstruct_ty_eq_deriv_forall tyrel kdeq1 tyeq2 =
    let
      val kdeqrel1 = extract_kdeqrel kdeq1
      val tyeqrel2 = extract_tyeqrel tyeq2
      val tyrel_new = (#1 kdeqrel1, CstrForall (#2 kdeqrel1, #2 tyeqrel2), CstrForall (#3 kdeqrel1, #3 tyeqrel2))
    in
      TyEqDerivForall (tyrel_new, kdeq1, tyeq2)
    end

  fun reconstruct_ty_eq_deriv_exists tyrel kdeq1 tyeq2 =
    let
      val kdeqrel1 = extract_kdeqrel kdeq1
      val tyeqrel2 = extract_tyeqrel tyeq2
      val tyrel_new = (#1 kdeqrel1, CstrExists (#2 kdeqrel1, #2 tyeqrel2), CstrExists (#3 kdeqrel1, #3 tyeqrel2))
    in
      TyEqDerivExists (tyrel_new, kdeq1, tyeq2)
    end

  fun reconstruct_ty_eq_deriv_abs tyrel kdeq1 tyeq2 =
    let
      val kdeqrel1 = extract_kdeqrel kdeq1
      val tyeqrel2 = extract_tyeqrel tyeq2
      val tyrel_new = (#1 kdeqrel1, CstrAbs (#2 kdeqrel1, #2 tyeqrel2), CstrAbs (#3 kdeqrel1, #3 tyeqrel2))
    in
      TyEqDerivAbs (tyrel_new, kdeq1, tyeq2)
    end

  fun reconstruct_ty_eq_deriv_rec tyrel kdeq1 tyeq2 =
    let
      val kdeqrel1 = extract_kdeqrel kdeq1
      val tyeqrel2 = extract_tyeqrel tyeq2
      val tyrel_new = (#1 kdeqrel1, CstrRec (#2 kdeqrel1, #2 tyeqrel2), CstrRec (#3 kdeqrel1, #3 tyeqrel2))
    in
      TyEqDerivRec (tyrel_new, kdeq1, tyeq2)
    end
end

structure DerivationPasses =
struct
  open MicroTiML
  open Util
  open DerivationPassesUtil

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
          val (left, right) = (List.take (ctx, dep), List.drop (ctx, dep))
          val left' = List.mapi (fn (i, bd) =>
            case bd of
              BdType ty => BdType (Passes.TermShift.shift_constr_above (List.length delta) (dep - 1 - i) ty)
            | BdKind kd => BdKind (Passes.TermShift.shift_kind_above (List.length delta) (dep - 1 - i) kd)) left
        in
          List.concat [left', delta, right]
        end

      fun on_typing_relation ((ctx, tm, ty, ti), (dep, delta)) =
        let
          val ctx' = shift_context_above delta dep ctx
          val tm' = Passes.TermShift.shift_term_above (List.length delta) dep tm
          val ty' = Passes.TermShift.shift_constr_above (List.length delta) dep ty
          val ti' = Passes.TermShift.shift_constr_above (List.length delta) dep ti
        in
          ((ctx', tm', ty', ti'), ())
        end

      fun on_kinding_relation ((ctx, cstr, kd), (dep, delta)) =
        let
          val ctx' = shift_context_above delta dep ctx
          val cstr' = Passes.TermShift.shift_constr_above (List.length delta) dep cstr
          val kd' = Passes.TermShift.shift_kind_above (List.length delta) dep kd
        in
          ((ctx', cstr', kd'), ())
        end

      fun on_proping_relation ((ctx, pr), (dep, delta)) =
        let
          val ctx' = shift_context_above delta dep ctx
          val pr' = Passes.TermShift.shift_prop_above (List.length delta) dep pr
        in
          ((ctx', pr'), ())
        end

      fun on_kind_wellformness_relation ((ctx, kd), (dep, delta)) =
        let
          val ctx' = shift_context_above delta dep ctx
          val kd' = Passes.TermShift.shift_kind_above (List.length delta) dep kd
        in
          ((ctx', kd'), ())
        end

      fun on_prop_wellformness_relation ((ctx, pr), (dep, delta)) =
        let
          val ctx' = shift_context_above delta dep ctx
          val pr' = Passes.TermShift.shift_prop_above (List.length delta) dep pr
        in
          ((ctx', pr'), ())
        end

      fun on_type_equivalence_relation ((ctx, ty1, ty2), (dep, delta)) =
        let
          val ctx' = shift_context_above delta dep ctx
          val ty1' = Passes.TermShift.shift_constr_above (List.length delta) dep ty1
          val ty2' = Passes.TermShift.shift_constr_above (List.length delta) dep ty2
        in
          ((ctx', ty1', ty2'), ())
        end

      (*fun on_kind_equivalence_relation ((ctx, kd1, kd2), (dep, delta)) =
        let
          val ctx' = shift_context_above delta dep ctx
          val kd1' = Passes.TermShift.shift_kind_above (List.length delta) dep kd1
          val kd2' = Passes.TermShift.shift_kind_above (List.length delta) dep kd2
        in
          ((ctx', kd1', kd2'), ())
        end

      fun on_kind_sub_relation ((ctx, kd1, kd2), (dep, delta)) =
        let
          val ctx' = shift_context_above delta dep ctx
          val kd1' = Passes.TermShift.shift_kind_above (List.length delta) dep kd1
          val kd2' = Passes.TermShift.shift_kind_above (List.length delta) dep kd2
        in
          ((ctx', kd1', kd2'), ())
        end*)

      fun transformer_typing_derivation (on_tyderiv, on_kdderiv, on_prderiv, on_kdwf, on_tyeq) (tyderiv : typing_derivation, down as (dep, delta) : down) =
        let
          (*fun on_rel tyrel = #1 (on_typing_relation (tyrel, down))*)
        in
          case tyderiv of
            TyDerivAbs (tyrel, kdderiv1, tyderiv2) =>
              let
                val (kdderiv1, ()) = on_kdderiv (kdderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (dep + 1, delta))
              in
                SOME (reconstruct_ty_deriv_abs tyrel kdderiv1 tyderiv2, ())
              end
          | TyDerivRec (tyrel, kdderiv1, tyderiv2) =>
              let
                val (kdderiv1, ()) = on_kdderiv (kdderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (dep + 1, delta))
              in
                SOME (reconstruct_ty_deriv_rec tyrel kdderiv1 tyderiv2, ())
              end
          | TyDerivCase (tyrel, tyderiv1, tyderiv2, tyderiv3) =>
              let
                val (tyderiv1, ()) = on_tyderiv (tyderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (dep + 1, delta))
                val (tyderiv3, ()) = on_tyderiv (tyderiv3, (dep + 1, delta))
              in
                SOME (reconstruct_ty_deriv_case tyrel tyderiv1 tyderiv2 tyderiv3, ())
              end
          | TyDerivUnpack (tyrel, tyderiv1, tyderiv2) =>
              let
                val (tyderiv1, ()) = on_tyderiv (tyderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (dep + 2, delta))
              in
                 SOME (reconstruct_ty_deriv_unpack tyrel tyderiv1 tyderiv2, ())
              end
          | TyDerivCstrAbs (tyrel, kdwf1, tyderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (dep + 1, delta))
              in
                SOME (reconstruct_ty_deriv_cstr_abs tyrel kdwf1 tyderiv2, ())
              end
          | TyDerivLet (tyrel, tyderiv2, tyderiv3) =>
              let
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, down)
                val (tyderiv3, ()) = on_tyderiv (tyderiv3, (dep + 1, delta))
              in
                SOME (reconstruct_ty_deriv_let tyrel tyderiv2 tyderiv3, ())
              end
          | _ => NONE
        end

      fun transformer_kinding_derivation (on_kdderiv, on_prderiv, on_kdwf) (kdderiv : kinding_derivation, down as (dep, delta) : down) =
        let
          (*fun on_rel kdrel = #1 (on_kinding_relation (kdrel, down))*)
        in
          case kdderiv of
            KdDerivRefine (kdrel, kdderiv1, prderiv2) =>
              let
                val (kdderiv1, ()) = on_kdderiv (kdderiv1, down)
                val (prderiv2, ()) = on_prderiv (prderiv2, (dep + 1, delta))
              in
                SOME (reconstruct_kd_deriv_refine kdrel kdderiv1 prderiv2, ())
              end
          | KdDerivTimeAbs (kdrel, kdderiv1) =>
              let
                val (kdderiv1, ()) = on_kdderiv (kdderiv1, (dep + 1, delta))
              in
                SOME (reconstruct_kd_deriv_time_abs kdrel kdderiv1, ())
              end
          | KdDerivAbs (kdrel, kdwf1, kdderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (kdderiv2, ()) = on_kdderiv (kdderiv2, (dep + 1, delta))
              in
                SOME (reconstruct_kd_deriv_abs kdrel kdwf1 kdderiv2, ())
              end
          | KdDerivForall (kdrel, kdwf1, kdderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (kdderiv2, ()) = on_kdderiv (kdderiv2, (dep + 1, delta))
              in
                SOME (reconstruct_kd_deriv_forall kdrel kdwf1 kdderiv2, ())
              end
          | KdDerivExists (kdrel, kdwf1, kdderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (kdderiv2, ()) = on_kdderiv (kdderiv2, (dep + 1, delta))
              in
                SOME (reconstruct_kd_deriv_exists kdrel kdwf1 kdderiv2, ())
              end
          | KdDerivRec (kdrel, kdwf1, kdderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (kdderiv2, ()) = on_kdderiv (kdderiv2, (dep + 1, delta))
              in
                SOME (reconstruct_kd_deriv_rec kdrel kdwf1 kdderiv2, ())
              end
          | _ => NONE
        end

      fun transformer_proping_derivation _ = NONE

      fun transformer_kind_wellformness_derivation (on_kdwf, on_prwf) (kdwf : kind_wellformedness_derivation, down as (dep, delta) : down) =
        let
          (*fun on_rel kdrel = #1 (on_kind_wellformness_relation (kdrel, down))*)
        in
          case kdwf of
            KdWfDerivSubset (kdrel, kdwf1, prwf2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (prwf2, ()) = on_prwf (prwf2, (dep + 1, delta))
              in
                SOME (reconstrct_kd_wf_deriv_subset kdrel kdwf1 prwf2, ())
              end
          | _ => NONE
        end

      fun transformer_prop_wellformness_derivation (on_prwf, on_kdwf, on_kdderiv) (prwf : prop_wellformedness_derivation, down as (dep, delta) : down) =
        let
          (*fun on_rel prrel = #1 (on_prop_wellformness_relation (prrel, down))*)
        in
          case prwf of
            PrWfDerivForall (prrel, kdwf1, prwf2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (prwf2, ()) = on_prwf (prwf2, (dep + 1, delta))
              in
                SOME (reconstruct_pr_wf_deriv_forall prrel kdwf1 prwf2, ())
              end
          | PrWfDerivExists (prrel, kdwf1, prwf2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (prwf2, ()) = on_prwf (prwf2, (dep + 1, delta))
              in
                SOME (reconstruct_pr_wf_deriv_exists prrel kdwf1 prwf2, ())
              end
          | _ => NONE
        end

      fun transformer_type_equivalence_derivation (on_tyeq, on_kdeq, on_prderiv) (tyeq : type_equivalence_derivation, down as (dep, delta) : down) =
        let
          (*fun on_rel tyrel = #1 (on_type_equivalence_relation (tyrel, down))*)
        in
          case tyeq of
            TyEqDerivForall (tyrel, kdeq1, tyeq2) =>
              let
                val (kdeq1, ()) = on_kdeq (kdeq1, down)
                val (tyeq2, ()) = on_tyeq (tyeq2, (dep + 1, delta))
              in
                SOME (reconstruct_ty_eq_deriv_forall tyrel kdeq1 tyeq2, ())
              end
          | TyEqDerivExists (tyrel, kdeq1, tyeq2) =>
              let
                val (kdeq1, ()) = on_kdeq (kdeq1, down)
                val (tyeq2, ()) = on_tyeq (tyeq2, (dep + 1, delta))
              in
                SOME (reconstruct_ty_eq_deriv_exists tyrel kdeq1 tyeq2, ())
              end
          | TyEqDerivRec (tyrel, kdeq1, tyeq2) =>
              let
                val (kdeq1, ()) = on_kdeq (kdeq1, down)
                val (tyeq2, ()) = on_tyeq (tyeq2, (dep + 1, delta))
              in
                SOME (reconstruct_ty_eq_deriv_rec tyrel kdeq1 tyeq2, ())
              end
          | TyEqDerivAbs (tyrel, kdeq1, tyeq2) =>
              let
                val (kdeq1, ()) = on_kdeq (kdeq1, down)
                val (tyeq2, ()) = on_tyeq (tyeq2, (dep + 1, delta))
              in
                SOME (reconstruct_ty_eq_deriv_abs tyrel kdeq1 tyeq2, ())
              end
          | _ => NONE
        end

      fun transformer_kind_equivalence_derivation on_kdsub (kdeq : kind_equivalence_derivation, down as (dep, delta) : down) = NONE

      fun transformer_kind_sub_derivation on_kdderiv (kdsub : kind_sub_derivation, down as (dep, delta) : down) = NONE
    end

    structure TypingDerivationShiftIns = TypingDerivationTransformPass(TypingDerivationShiftHelper)
    open TypingDerivationShiftIns

    fun shift_typing_derivation_above delta dep tyderiv = #1 (transform_typing_derivation (tyderiv, (dep, delta)))
    fun shift_kinding_derivation_above delta dep kdderiv = #1 (transform_kinding_derivation (kdderiv, (dep, delta)))
    fun shift_proping_derivation_above delta dep prderiv = #1 (transform_proping_derivation (prderiv, (dep, delta)))
  end

  structure TypingDerivationChangeContext =
  struct
    structure TypingDerivationChangeContextHelper =
    struct
      type down = context
      type up = unit

      val upward_base = ()
      fun combiner ((), ()) = ()

      fun on_typing_relation ((ctx, tm, ty, ti), down) = ((down, tm, ty, ti), ())

      fun on_kinding_relation ((ctx, cstr, kd), down) = ((down, cstr, kd), ())

      fun on_proping_relation ((ctx, pr), down) = ((down, pr), ())

      fun on_kind_wellformness_relation ((ctx, kd), down) = ((down, kd), ())

      fun on_prop_wellformness_relation ((ctx, pr), down) = ((down, pr), ())

      fun on_type_equivalence_relation ((ctx, ty1, ty2), down) = ((down, ty1, ty2), ())

      (*fun on_kind_equivalence_relation ((ctx, kd1, kd2), down) = ((down, kd1, kd2), ())

      fun on_kind_sub_relation ((ctx, kd1, kd2), down) = ((down, kd1, kd2), ())*)

      fun transformer_typing_derivation (on_tyderiv, on_kdderiv, on_prderiv, on_kdwf, on_tyeq) (tyderiv : typing_derivation, down : down) =
        let
          (*fun on_rel tyrel = #1 (on_typing_relation (tyrel, down))*)
        in
          case tyderiv of
            TyDerivAbs (tyrel, kdderiv1, tyderiv2) =>
              let
                val (kdderiv1, ()) = on_kdderiv (kdderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, BdType (#2 (extract_kdrel kdderiv1)) :: down)
              in
                SOME (reconstruct_ty_deriv_abs tyrel kdderiv1 tyderiv2, ())
              end
          | TyDerivRec (tyrel, kdderiv1, tyderiv2) =>
              let
                val (kdderiv1, ()) = on_kdderiv (kdderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, BdType (#2 (extract_kdrel kdderiv1)) :: down)
              in
                SOME (reconstruct_ty_deriv_rec tyrel kdderiv1 tyderiv2, ())
              end
          | TyDerivCase (tyrel, tyderiv1, tyderiv2, tyderiv3) =>
              let
                val (tyderiv1, ()) = on_tyderiv (tyderiv1, down)
                val (ty_l, ty_r) = extract_cstr_sum (#3 (extract_tyrel tyderiv1))
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, BdType ty_l :: down)
                val (tyderiv3, ()) = on_tyderiv (tyderiv3, BdType ty_r :: down)
              in
                SOME (reconstruct_ty_deriv_case tyrel tyderiv1 tyderiv2 tyderiv3, ())
              end
          | TyDerivUnpack (tyrel, tyderiv1, tyderiv2) =>
              let
                val (tyderiv1, ()) = on_tyderiv (tyderiv1, down)
                val (kd1, ty2) = extract_cstr_exists (#3 (extract_tyrel tyderiv1))
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, BdType ty2 :: BdKind kd1 :: down)
              in
                SOME (reconstruct_ty_deriv_unpack tyrel tyderiv1 tyderiv2, ())
              end
          | TyDerivCstrAbs (tyrel, kdwf1, tyderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, BdKind (#2 (extract_kdwfrel kdwf1)) :: down)
              in
                SOME (reconstruct_ty_deriv_cstr_abs tyrel kdwf1 tyderiv2, ())
              end
          | TyDerivLet (tyrel, tyderiv2, tyderiv3) =>
              let
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, down)
                val (tyderiv3, ()) = on_tyderiv (tyderiv3, BdType (#3 (extract_tyrel tyderiv2)) :: down)
              in
                SOME (reconstruct_ty_deriv_let tyrel tyderiv2 tyderiv3, ())
              end
          | _ => NONE
        end

      fun transformer_kinding_derivation (on_kdderiv, on_prderiv, on_kdwf) (kdderiv : kinding_derivation, down : down) =
        let
          (*fun on_rel kdrel = #1 (on_kinding_relation (kdrel, down))*)
        in
          case kdderiv of
            KdDerivRefine (kdrel, kdderiv1, prderiv2) =>
              let
                val (kdderiv1, ()) = on_kdderiv (kdderiv1, down)
                val (prderiv2, ()) = on_prderiv (prderiv2, BdKind (#3 (extract_kdrel kdderiv1)) :: down)
              in
                SOME (reconstruct_kd_deriv_refine kdrel kdderiv1 prderiv2, ())
              end
          | KdDerivTimeAbs (kdrel, kdderiv1) =>
              let
                val (kdderiv1, ()) = on_kdderiv (kdderiv1, BdKind (KdTimeFun 0) :: down)
              in
                SOME (reconstruct_kd_deriv_time_abs kdrel kdderiv1, ())
              end
          | KdDerivAbs (kdrel, kdwf1, kdderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (kdderiv2, ()) = on_kdderiv (kdderiv2, BdKind (#2 (extract_kdwfrel kdwf1)) :: down)
              in
                SOME (reconstruct_kd_deriv_abs kdrel kdwf1 kdderiv2, ())
              end
          | KdDerivForall (kdrel, kdwf1, kdderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (kdderiv2, ()) = on_kdderiv (kdderiv2, BdKind (#2 (extract_kdwfrel kdwf1)) :: down)
              in
                SOME (reconstruct_kd_deriv_forall kdrel kdwf1 kdderiv2, ())
              end
          | KdDerivExists (kdrel, kdwf1, kdderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (kdderiv2, ()) = on_kdderiv (kdderiv2, BdKind (#2 (extract_kdwfrel kdwf1)) :: down)
              in
                SOME (reconstruct_kd_deriv_exists kdrel kdwf1 kdderiv2, ())
              end
          | KdDerivRec (kdrel, kdwf1, kdderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (kdderiv2, ()) = on_kdderiv (kdderiv2, BdKind (#2 (extract_kdwfrel kdwf1)) :: down)
              in
                SOME (reconstruct_kd_deriv_rec kdrel kdwf1 kdderiv2, ())
              end
          | _ => NONE
        end

      fun transformer_proping_derivation _ = NONE

      fun transformer_kind_wellformness_derivation (on_kdwf, on_prwf) (kdwf : kind_wellformedness_derivation, down : down) =
        let
          (*fun on_rel kdrel = #1 (on_kind_wellformness_relation (kdrel, down))*)
        in
          case kdwf of
            KdWfDerivSubset (kdrel, kdwf1, prwf2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (prwf2, ()) = on_prwf (prwf2, BdKind (#2 (extract_kdwfrel kdwf1)) :: down)
              in
                SOME (reconstrct_kd_wf_deriv_subset kdrel kdwf1 prwf2, ())
              end
          | _ => NONE
        end

      fun transformer_prop_wellformness_derivation (on_prwf, on_kdwf, on_kdderiv) (prwf : prop_wellformedness_derivation, down : down) =
        let
          (*fun on_rel prrel = #1 (on_prop_wellformness_relation (prrel, down))*)
        in
          case prwf of
            PrWfDerivForall (prrel, kdwf1, prwf2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (prwf2, ()) = on_prwf (prwf2, BdKind (#2 (extract_kdwfrel kdwf1)) :: down)
              in
                SOME (reconstruct_pr_wf_deriv_forall prrel kdwf1 prwf2, ())
              end
          | PrWfDerivExists (prrel, kdwf1, prwf2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (prwf2, ()) = on_prwf (prwf2, BdKind (#2 (extract_kdwfrel kdwf1)) :: down)
              in
                SOME (reconstruct_pr_wf_deriv_exists prrel kdwf1 prwf2, ())
              end
          | _ => NONE
        end

      fun transformer_type_equivalence_derivation (on_tyeq, on_kdeq, on_prderiv) (tyeq : type_equivalence_derivation, down : down) =
        let
          (*fun on_rel tyrel = #1 (on_type_equivalence_relation (tyrel, down))*)
        in
          case tyeq of
            TyEqDerivForall (tyrel, kdeq1, tyeq2) =>
              let
                val (kdeq1, ()) = on_kdeq (kdeq1, down)
                val (tyeq2, ()) = on_tyeq (tyeq2, BdKind (#2 (extract_kdeqrel kdeq1)) :: down)
              in
                SOME (reconstruct_ty_eq_deriv_forall tyrel kdeq1 tyeq2, ())
              end
          | TyEqDerivExists (tyrel, kdeq1, tyeq2) =>
              let
                val (kdeq1, ()) = on_kdeq (kdeq1, down)
                val (tyeq2, ()) = on_tyeq (tyeq2, BdKind (#2 (extract_kdeqrel kdeq1)) :: down)
              in
                SOME (reconstruct_ty_eq_deriv_exists tyrel kdeq1 tyeq2, ())
              end
          | TyEqDerivRec (tyrel, kdeq1, tyeq2) =>
              let
                val (kdeq1, ()) = on_kdeq (kdeq1, down)
                val (tyeq2, ()) = on_tyeq (tyeq2, BdKind (#2 (extract_kdeqrel kdeq1)) :: down)
              in
                SOME (reconstruct_ty_eq_deriv_rec tyrel kdeq1 tyeq2, ())
              end
          | TyEqDerivAbs (tyrel, kdeq1, tyeq2) =>
              let
                val (kdeq1, ()) = on_kdeq (kdeq1, down)
                val (tyeq2, ()) = on_tyeq (tyeq2, BdKind (#2 (extract_kdeqrel kdeq1)) :: down)
              in
                SOME (reconstruct_ty_eq_deriv_abs tyrel kdeq1 tyeq2, ())
              end
          | _ => NONE
        end

      fun transformer_kind_equivalence_derivation on_kdsub (kdeq : kind_equivalence_derivation, down : down) = NONE

      fun transformer_kind_sub_derivation on_kdderiv (kdsub : kind_sub_derivation, down : down) = NONE
    end

    structure TypingDerivationChangeContextIns = TypingDerivationTransformPass(TypingDerivationChangeContextHelper)
    open TypingDerivationChangeContextIns

    fun change_context_typing_derivation tyderiv ctx = #1 (transform_typing_derivation (tyderiv, ctx))
    fun change_context_kinding_derivation kdderiv ctx = #1 (transform_kinding_derivation (kdderiv, ctx))
    fun change_context_proping_derivation prderiv ctx = #1 (transform_proping_derivation (prderiv, ctx))
    fun change_context_kind_wellformness_derivation kdwf ctx = #1 (transform_kind_wellformness_derivation (kdwf, ctx))
    fun change_context_prop_wellformness_derivation prwf ctx = #1 (transform_prop_wellformness_derivation (prwf, ctx))
  end

  structure TypingDerivationSubstConstr =
  struct
    structure TypingDerivationSubstConstrHelper =
    struct
      type down = int * constr
      type up = unit

      val upward_base = ()
      fun combiner ((), ()) = ()

      fun on_typing_relation ((ctx, tm, ty, ti), (who, to)) =
        let
          val tm' = #1 (Passes.TermSubstConstr.transform_term (tm, (who, to)))
          val ty' = #1 (Passes.TermSubstConstr.transform_constr (ty, (who, to)))
          val ti' = #1 (Passes.TermSubstConstr.transform_constr (ti, (who, to)))
        in
          ((ctx, tm', ty', ti'), ())
        end

      fun on_kinding_relation ((ctx, cstr, kd), (who, to)) =
        let
          val cstr' = #1 (Passes.TermSubstConstr.transform_constr (cstr, (who, to)))
          val kd' = #1 (Passes.TermSubstConstr.transform_kind (kd, (who, to)))
        in
          ((ctx, cstr', kd'), ())
        end

      fun on_proping_relation ((ctx, pr), (who, to)) =
        let
          val pr' = #1 (Passes.TermSubstConstr.transform_prop (pr, (who, to)))
        in
          ((ctx, pr'), ())
        end

      fun on_kind_wellformness_relation ((ctx, kd), (who, to)) =
        let
          val kd' = #1 (Passes.TermSubstConstr.transform_kind (kd, (who, to)))
        in
          ((ctx, kd'), ())
        end

      fun on_prop_wellformness_relation ((ctx, pr), (who, to)) =
        let
          val pr' = #1 (Passes.TermSubstConstr.transform_prop (pr, (who, to)))
        in
          ((ctx, pr'), ())
        end

      fun on_type_equivalence_relation ((ctx, ty1, ty2), (who, to)) =
        let
          val ty1' = #1 (Passes.TermSubstConstr.transform_constr (ty1, (who, to)))
          val ty2' = #1 (Passes.TermSubstConstr.transform_constr (ty2, (who, to)))
        in
          ((ctx, ty1', ty2'), ())
        end

      (*fun on_kind_equivalence_relation ((ctx, kd1, kd2), (who, to)) =
        let
          val kd1' = #1 (Passes.TermSubstConstr.transform_kind (kd1, (who, to)))
          val kd2' = #1 (Passes.TermSubstConstr.transform_kind (kd2, (who, to)))
        in
          ((ctx, kd1', kd2'), ())
        end

      fun on_kind_sub_relation ((ctx, kd1, kd2), (who, to)) =
        let
          val kd1' = #1 (Passes.TermSubstConstr.transform_kind (kd1, (who, to)))
          val kd2' = #1 (Passes.TermSubstConstr.transform_kind (kd2, (who, to)))
        in
          ((ctx, kd1', kd2'), ())
        end*)

      fun transformer_typing_derivation (on_tyderiv, on_kdderiv, on_prderiv, on_kdwf, on_tyeq) (tyderiv : typing_derivation, down as (who, to) : down) =
        let
          (*fun on_rel tyrel = #1 (on_typing_relation (tyrel, down))*)
        in
          case tyderiv of
            TyDerivAbs (tyrel, kdderiv1, tyderiv2) =>
              let
                val (kdderiv1, ()) = on_kdderiv (kdderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (who + 1, to))
              in
                SOME (reconstruct_ty_deriv_abs tyrel kdderiv1 tyderiv2, ())
              end
          | TyDerivRec (tyrel, kdderiv1, tyderiv2) =>
              let
                val (kdderiv1, ()) = on_kdderiv (kdderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (who + 1, to))
              in
                SOME (reconstruct_ty_deriv_rec tyrel kdderiv1 tyderiv2, ())
              end
          | TyDerivCase (tyrel, tyderiv1, tyderiv2, tyderiv3) =>
              let
                val (tyderiv1, ()) = on_tyderiv (tyderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (who + 1, to))
                val (tyderiv3, ()) = on_tyderiv (tyderiv3, (who + 1, to))
              in
                SOME (reconstruct_ty_deriv_case tyrel tyderiv1 tyderiv2 tyderiv3, ())
              end
          | TyDerivUnpack (tyrel, tyderiv1, tyderiv2) =>
              let
                val (tyderiv1, ()) = on_tyderiv (tyderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (who + 2, to))
              in
                SOME (reconstruct_ty_deriv_unpack tyrel tyderiv1 tyderiv2, ())
              end
          | TyDerivCstrAbs (tyrel, kdwf1, tyderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (who + 1, to))
              in
                SOME (reconstruct_ty_deriv_cstr_abs tyrel kdwf1 tyderiv2, ())
              end
          | TyDerivLet (tyrel, tyderiv2, tyderiv3) =>
              let
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, down)
                val (tyderiv3, ()) = on_tyderiv (tyderiv3, (who + 1, to))
              in
                SOME (reconstruct_ty_deriv_let tyrel tyderiv2 tyderiv3, ())
              end
          | _ => NONE
        end

      fun transformer_kinding_derivation (on_kdderiv, on_prderiv, on_kdwf) (kdderiv : kinding_derivation, down as (who, to) : down) =
        let
          (*fun on_rel kdrel = #1 (on_kinding_relation (kdrel, down))*)
        in
          case kdderiv of
            KdDerivRefine (kdrel, kdderiv1, prderiv2) =>
              let
                val (kdderiv1, ()) = on_kdderiv (kdderiv1, down)
                val (prderiv2, ()) = on_prderiv (prderiv2, (who + 1, to))
              in
                SOME (reconstruct_kd_deriv_refine kdrel kdderiv1 prderiv2, ())
              end
          | KdDerivTimeAbs (kdrel, kdderiv1) =>
              let
                val (kdderiv1, ()) = on_kdderiv (kdderiv1, (who + 1, to))
              in
                SOME (reconstruct_kd_deriv_time_abs kdrel kdderiv1, ())
              end
          | KdDerivAbs (kdrel, kdwf1, kdderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (kdderiv2, ()) = on_kdderiv (kdderiv2, (who + 1, to))
              in
                SOME (reconstruct_kd_deriv_abs kdrel kdwf1 kdderiv2, ())
              end
          | KdDerivForall (kdrel, kdwf1, kdderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (kdderiv2, ()) = on_kdderiv (kdderiv2, (who + 1, to))
              in
                SOME (reconstruct_kd_deriv_forall kdrel kdwf1 kdderiv2, ())
              end
          | KdDerivExists (kdrel, kdwf1, kdderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (kdderiv2, ()) = on_kdderiv (kdderiv2, (who + 1, to))
              in
                SOME (reconstruct_kd_deriv_exists kdrel kdwf1 kdderiv2, ())
              end
          | KdDerivRec (kdrel, kdwf1, kdderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (kdderiv2, ()) = on_kdderiv (kdderiv2, (who + 1, to))
              in
                SOME (reconstruct_kd_deriv_rec kdrel kdwf1 kdderiv2, ())
              end
          | _ => NONE
        end

      fun transformer_proping_derivation _ = NONE

      fun transformer_kind_wellformness_derivation (on_kdwf, on_prwf) (kdwf : kind_wellformedness_derivation, down as (who, to) : down) =
        let
          (*fun on_rel kdrel = #1 (on_kind_wellformness_relation (kdrel, down))*)
        in
          case kdwf of
            KdWfDerivSubset (kdrel, kdwf1, prwf2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (prwf2, ()) = on_prwf (prwf2, (who + 1, to))
              in
                SOME (reconstrct_kd_wf_deriv_subset kdrel kdwf1 prwf2, ())
              end
          | _ => NONE
        end

      fun transformer_prop_wellformness_derivation (on_prwf, on_kdwf, on_kdderiv) (prwf : prop_wellformedness_derivation, down as (who, to) : down) =
        let
          (*fun on_rel prrel = #1 (on_prop_wellformness_relation (prrel, down))*)
        in
          case prwf of
            PrWfDerivForall (prrel, kdwf1, prwf2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (prwf2, ()) = on_prwf (prwf2, (who + 1, to))
              in
                SOME (reconstruct_pr_wf_deriv_forall prrel kdwf1 prwf2, ())
              end
          | PrWfDerivExists (prrel, kdwf1, prwf2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (prwf2, ()) = on_prwf (prwf2, (who + 1, to))
              in
                SOME (reconstruct_pr_wf_deriv_exists prrel kdwf1 prwf2, ())
              end
          | _ => NONE
        end

      fun transformer_type_equivalence_derivation (on_tyeq, on_kdeq, on_prderiv) (tyeq : type_equivalence_derivation, down as (who, to) : down) =
        let
          (*fun on_rel tyrel = #1 (on_type_equivalence_relation (tyrel, down))*)
        in
          case tyeq of
            TyEqDerivForall (tyrel, kdeq1, tyeq2) =>
              let
                val (kdeq1, ()) = on_kdeq (kdeq1, down)
                val (tyeq2, ()) = on_tyeq (tyeq2, (who + 1, to))
              in
                SOME (reconstruct_ty_eq_deriv_forall tyrel kdeq1 tyeq2, ())
              end
          | TyEqDerivExists (tyrel, kdeq1, tyeq2) =>
              let
                val (kdeq1, ()) = on_kdeq (kdeq1, down)
                val (tyeq2, ()) = on_tyeq (tyeq2, (who + 1, to))
              in
                SOME (reconstruct_ty_eq_deriv_exists tyrel kdeq1 tyeq2, ())
              end
          | TyEqDerivRec (tyrel, kdeq1, tyeq2) =>
              let
                val (kdeq1, ()) = on_kdeq (kdeq1, down)
                val (tyeq2, ()) = on_tyeq (tyeq2, (who + 1, to))
              in
                SOME (reconstruct_ty_eq_deriv_rec tyrel kdeq1 tyeq2, ())
              end
          | TyEqDerivAbs (tyrel, kdeq1, tyeq2) =>
              let
                val (kdeq1, ()) = on_kdeq (kdeq1, down)
                val (tyeq2, ()) = on_tyeq (tyeq2, (who + 1, to))
              in
                SOME (reconstruct_ty_eq_deriv_abs tyrel kdeq1 tyeq2, ())
              end
          | _ => NONE
        end

      fun transformer_kind_equivalence_derivation on_kdsub (kdeq : kind_equivalence_derivation, down : down) = NONE

      fun transformer_kind_sub_derivation on_kdderiv (kdsub : kind_sub_derivation, down : down) = NONE
    end

    structure TypingDerivationSubstConstrIns = TypingDerivationTransformPass(TypingDerivationSubstConstrHelper)
    open TypingDerivationSubstConstrIns
  end

  structure TypingDerivationSubstTerm =
  struct
    structure TypingDerivationSubstTermHelper =
    struct
      type down = int * term
      type up = unit

      val upward_base = ()
      fun combiner ((), ()) = ()

      fun on_typing_relation ((ctx, tm, ty, ti), (who, to)) =
        let
          val tm' = #1 (Passes.TermSubstTerm.transform_term (tm, (who, to)))
        in
          ((ctx, tm', ty, ti), ())
        end

      fun on_kinding_relation (rel as (ctx, cstr, kd), (who, to)) = (rel, ())

      fun on_proping_relation (rel as (ctx, pr), (who, to)) = (rel, ())

      fun on_kind_wellformness_relation (rel as (ctx, kd), (who, to)) = (rel, ())

      fun on_prop_wellformness_relation (rel as (ctx, pr), (who, to)) = (rel, ())

      fun on_type_equivalence_relation (rel, down) = (rel, ())

      (*fun on_kind_equivalence_relation (rel, down) = (rel, ())

      fun on_kind_sub_relation (rel, down) = (rel, ())*)

      fun transformer_typing_derivation (on_tyderiv, on_kdderiv, on_prderiv, on_kdwf, on_tyeq) (tyderiv : typing_derivation, down as (who, to) : down) =
        let
          (*fun on_rel tyrel = #1 (on_typing_relation (tyrel, down))*)
        in
          case tyderiv of
            TyDerivAbs (tyrel, kdderiv1, tyderiv2) =>
              let
                val (kdderiv1, ()) = on_kdderiv (kdderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (who + 1, to))
              in
                SOME (reconstruct_ty_deriv_abs tyrel kdderiv1 tyderiv2, ())
              end
          | TyDerivRec (tyrel, kdderiv1, tyderiv2) =>
              let
                val (kdderiv1, ()) = on_kdderiv (kdderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (who + 1, to))
              in
                SOME (reconstruct_ty_deriv_rec tyrel kdderiv1 tyderiv2, ())
              end
          | TyDerivCase (tyrel, tyderiv1, tyderiv2, tyderiv3) =>
              let
                val (tyderiv1, ()) = on_tyderiv (tyderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (who + 1, to))
                val (tyderiv3, ()) = on_tyderiv (tyderiv3, (who + 1, to))
              in
                SOME (reconstruct_ty_deriv_case tyrel tyderiv1 tyderiv2 tyderiv3, ())
              end
          | TyDerivUnpack (tyrel, tyderiv1, tyderiv2) =>
              let
                val (tyderiv1, ()) = on_tyderiv (tyderiv1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (who + 2, to))
              in
                SOME (reconstruct_ty_deriv_unpack tyrel tyderiv1 tyderiv2, ())
              end
          | TyDerivCstrAbs (tyrel, kdwf1, tyderiv2) =>
              let
                val (kdwf1, ()) = on_kdwf (kdwf1, down)
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, (who + 1, to))
              in
                SOME (reconstruct_ty_deriv_cstr_abs tyrel kdwf1 tyderiv2, ())
              end
          | TyDerivLet (tyrel, tyderiv2, tyderiv3) =>
              let
                val (tyderiv2, ()) = on_tyderiv (tyderiv2, down)
                val (tyderiv3, ()) = on_tyderiv (tyderiv3, (who + 1, to))
              in
                SOME (reconstruct_ty_deriv_let tyrel tyderiv2 tyderiv3, ())
              end
          | _ => NONE
        end

      fun transformer_kinding_derivation (on_kdderiv, on_prderiv, on_kdwf) (kdderiv : kinding_derivation, down as (who, to) : down) = NONE

      fun transformer_proping_derivation _ = NONE

      fun transformer_kind_wellformness_derivation (on_kdwf, on_prwf) (kdwf : kind_wellformedness_derivation, down as (who, to) : down) = NONE

      fun transformer_prop_wellformness_derivation (on_prwf, on_kdwf, on_kdderiv) (prwf : prop_wellformedness_derivation, down as (who, to) : down) = NONE

      fun transformer_type_equivalence_derivation _ _ = NONE

      fun transformer_kind_equivalence_derivation _ _ = NONE

      fun transformer_kind_sub_derivation _ _ = NONE
    end

    structure TypingDerivationSubstTermIns = TypingDerivationTransformPass(TypingDerivationSubstTermHelper)
    open TypingDerivationSubstTermIns
  end

  structure ANF =
  struct
    open TypingDerivationShift

    fun normalize_derivation tyderiv = normalize tyderiv (fn (x, d) => x)

    and normalize tyderiv k =
      case tyderiv of
        TyDerivSub (tyrel, tyderiv1, tyeq2, prderiv3) => normalize tyderiv1 k
      | TyDerivVar _ => k (tyderiv, [])
      | TyDerivInt _ => k (tyderiv, [])
      | TyDerivNat _ => k (tyderiv, [])
      | TyDerivUnit _ => k (tyderiv, [])
      | TyDerivApp (tyrel, tyderiv1, tyderiv2) =>
          normalize_shift tyderiv1 (fn (tyderiv1_new, d1) =>
            normalize_shift (shift_typing_derivation_above d1 0 tyderiv2) (fn (tyderiv2_new, d2) =>
              let
                val tyderiv1_new = shift_typing_derivation_above d2 0 tyderiv1_new
                val tyrel1_new = extract_tyrel tyderiv1_new
                val tyrel2_new = extract_tyrel tyderiv2_new
                val (ty1, ty2, ti) = extract_cstr_arrow (#3 tyrel1_new)
                val tyrel_new = (#1 tyrel2_new, TmApp (#2 tyrel1_new, #2 tyrel2_new), ty2, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, #4 tyrel1_new, #4 tyrel2_new), CstrTime "1.0"), ti))
              in
                k (TyDerivApp (tyrel_new, tyderiv1_new, tyderiv2_new), List.concat [d2, d1])
              end))
      | TyDerivAbs (tyrel, kdderiv1, tyderiv2) =>
          let
            val (kd1, tm2) = extract_tm_abs (#2 tyrel)
            val tyderiv2_new = normalize_derivation tyderiv2
            val tyrel2_new = extract_tyrel tyderiv2_new
            val tyrel_new = (#1 tyrel, TmAbs (kd1, #2 tyrel2_new), #3 tyrel, CstrTime "0.0")
            val (ty1, ty2, ti) = extract_cstr_arrow (#3 tyrel)
            val tyderiv2_sub = TyDerivSub ((#1 tyrel2_new, #2 tyrel2_new, #3 tyrel2_new, Passes.TermShift.shift_constr 1 ti), tyderiv2_new, TyEqDerivAssume (#1 tyrel2_new, Passes.TermShift.shift_constr 1 ty2, #3 tyrel2_new), PrDerivAdmit (#1 tyrel2_new, PrBinRel (PrRelLe, #4 tyrel2_new, Passes.TermShift.shift_constr 1 ti)))
          in
            k (TyDerivAbs (tyrel_new, kdderiv1, tyderiv2_sub), [])
          end
      | TyDerivRec (tyrel, kdderiv1, tyderiv2) =>
          let
            val (kd1, tm2) = extract_tm_rec (#2 tyrel)
            val tyderiv2_new = normalize_derivation tyderiv2
            val tyrel2_new = extract_tyrel tyderiv2_new
            val tyrel_new = (#1 tyrel, TmRec (kd1, #2 tyrel2_new), #3 tyrel, CstrTime "0.0")
          in
            k (TyDerivRec (tyrel_new, kdderiv1, tyderiv2_new), [])
          end
      | TyDerivPair (tyrel, tyderiv1, tyderiv2) =>
          normalize_shift tyderiv1 (fn (tyderiv1_new, d1) =>
            normalize_shift (shift_typing_derivation_above d1 0 tyderiv2) (fn (tyderiv2_new, d2) =>
            let
              val tyderiv1_new = shift_typing_derivation_above d2 0 tyderiv1_new
              val tyrel1_new = extract_tyrel tyderiv1_new
              val tyrel2_new = extract_tyrel tyderiv2_new
              val tyrel_new = (#1 tyrel2_new, TmPair (#2 tyrel1_new, #2 tyrel2_new), CstrProd (#3 tyrel1_new, #3 tyrel2_new), CstrBinOp (CstrBopAdd, #4 tyrel1_new, #4 tyrel2_new))
            in
              k (TyDerivPair (tyrel_new, tyderiv1_new, tyderiv2_new), List.concat [d2, d1])
            end))
      | TyDerivFst (tyrel, tyderiv1) =>
          normalize_shift tyderiv1 (fn (tyderiv1_new, d1) =>
            let
              val tyrel1_new = extract_tyrel tyderiv1_new
              val (ty1, ty2) = extract_cstr_prod (#3 tyrel1_new)
              val tyrel_new = (#1 tyrel1_new, TmFst (#2 tyrel1_new), ty1, #4 tyrel1_new)
            in
              k (TyDerivFst (tyrel_new, tyderiv1_new), d1)
            end)
      | TyDerivSnd (tyrel, tyderiv1) =>
          normalize_shift tyderiv1 (fn (tyderiv1_new, d1) =>
            let
              val tyrel1_new = extract_tyrel tyderiv1_new
              val (ty1, ty2) = extract_cstr_prod (#3 tyrel1_new)
              val tyrel_new = (#1 tyrel1_new, TmSnd (#2 tyrel1_new), ty2, #4 tyrel1_new)
            in
              k (TyDerivSnd (tyrel_new, tyderiv1_new), d1)
            end)
      | TyDerivInLeft (tyrel, kdderiv1, tyderiv2) =>
          normalize_shift tyderiv2 (fn (tyderiv2_new, d2) =>
            let
              val kdderiv1_new = shift_kinding_derivation_above d2 0 kdderiv1
              val kdrel1_new = extract_kdrel kdderiv1_new
              val tyrel2_new = extract_tyrel tyderiv2_new
              val tyrel_new = (#1 tyrel2_new, TmInLeft (#2 tyrel2_new), CstrSum (#3 tyrel2_new, #2 kdrel1_new), #4 tyrel2_new)
            in
              k (TyDerivInLeft (tyrel_new, kdderiv1_new, tyderiv2_new), d2)
            end)
      | TyDerivInRight (tyrel, kdderiv1, tyderiv2) =>
          normalize_shift tyderiv2 (fn (tyderiv2_new, d2) =>
            let
              val kdderiv1_new = shift_kinding_derivation_above d2 0 kdderiv1
              val kdrel1_new = extract_kdrel kdderiv1_new
              val tyrel2_new = extract_tyrel tyderiv2_new
              val tyrel_new = (#1 tyrel2_new, TmInRight (#2 tyrel2_new), CstrSum (#2 kdrel1_new, #3 tyrel2_new), #4 tyrel2_new)
            in
              k (TyDerivInRight (tyrel_new, kdderiv1_new, tyderiv2_new), d2)
            end)
      | TyDerivCase (tyrel, tyderiv1, tyderiv2, tyderiv3) =>
          normalize_shift tyderiv1 (fn (tyderiv1_new, d1) =>
            let
              val tyderiv2_new = shift_typing_derivation_above d1 1 tyderiv2
              val tyderiv3_new = shift_typing_derivation_above d1 1 tyderiv3
              val tyderiv2_new = normalize_derivation tyderiv2_new
              val tyderiv3_new = normalize_derivation tyderiv3_new
              val tyrel2_new = extract_tyrel tyderiv2_new
              val tyrel3_new = extract_tyrel tyderiv3_new
              val tyrel1_new = extract_tyrel tyderiv1_new
              val ty_wrap = Passes.TermShift.shift_constr (List.length d1) (#3 tyrel)
              val tyderiv2_wrap = TyDerivSub ((#1 tyrel2_new, #2 tyrel2_new, Passes.TermShift.shift_constr 1 ty_wrap, #4 tyrel2_new), tyderiv2_new, TyEqDerivAssume (#1 tyrel2_new, #3 tyrel2_new, Passes.TermShift.shift_constr 1 ty_wrap), PrDerivAdmit (#1 tyrel2_new, PrBinRel (PrRelLe, #4 tyrel2_new, #4 tyrel2_new)))
              val tyderiv3_wrap = TyDerivSub ((#1 tyrel3_new, #2 tyrel3_new, Passes.TermShift.shift_constr 1 ty_wrap, #4 tyrel3_new), tyderiv3_new, TyEqDerivAssume (#1 tyrel3_new, #3 tyrel3_new, Passes.TermShift.shift_constr 1 ty_wrap), PrDerivAdmit (#1 tyrel3_new, PrBinRel (PrRelLe, #4 tyrel3_new, #4 tyrel3_new)))
              val tyrel_new = (#1 tyrel1_new, TmCase (#2 tyrel1_new, #2 tyrel2_new, #2 tyrel3_new), ty_wrap, CstrBinOp (CstrBopAdd, #4 tyrel1_new, CstrBinOp (CstrBopMax, Passes.TermShift.shift_constr ~1 (#4 tyrel2_new), Passes.TermShift.shift_constr ~1 (#4 tyrel3_new))))
            in
              k (TyDerivCase (tyrel_new, tyderiv1_new, tyderiv2_wrap, tyderiv3_wrap), d1)
            end)
      | TyDerivFold (tyrel, kdderiv1, tyderiv2) =>
          normalize_shift tyderiv2 (fn (tyderiv2_new, d2) =>
            let
              val kdderiv1_new = shift_kinding_derivation_above d2 0 kdderiv1
              val kdrel1_new = extract_kdrel kdderiv1_new
              val tyrel2_new = extract_tyrel tyderiv2_new
              val tyrel_new = (#1 tyrel2_new, TmFold (#2 tyrel2_new), #2 kdrel1_new, #4 tyrel2_new)
            in
              k (TyDerivFold (tyrel_new, kdderiv1_new, tyderiv2_new), d2)
            end)
      | TyDerivUnfold (tyrel, tyderiv1) =>
          normalize_shift tyderiv1 (fn (tyderiv1_new, d1) =>
            let
              val tyrel1_new = extract_tyrel tyderiv1_new
              val ty1_new = #3 tyrel1_new
              val tyrel_new = (#1 tyrel1_new, TmUnfold (#2 tyrel1_new), Passes.TermShift.shift_constr (List.length d1) (#3 tyrel), #4 tyrel1_new)
            in
              k (TyDerivUnfold (tyrel_new, tyderiv1_new), d1)
            end)
      | TyDerivPack (tyrel, kdderiv1, kdderiv2, tyderiv3) =>
          normalize_shift tyderiv3 (fn (tyderiv3_new, d3) =>
            let
              val kdderiv1_new = shift_kinding_derivation_above d3 0 kdderiv1
              val kdderiv2_new = shift_kinding_derivation_above d3 0 kdderiv2
              val kdrel1_new = extract_kdrel kdderiv1_new
              val kdrel2_new = extract_kdrel kdderiv2_new
              val tyrel3_new = extract_tyrel tyderiv3_new
              val tyrel_new = (#1 tyrel3_new, TmPack (#2 kdrel2_new, #2 tyrel3_new), #2 kdrel1_new, #4 tyrel3_new)
            in
              k (TyDerivPack (tyrel_new, kdderiv1_new, kdderiv2_new, tyderiv3_new), d3)
            end)
      | TyDerivUnpack (tyrel, tyderiv1, tyderiv2) =>
          normalize tyderiv1 (fn (tyderiv1_new, d1) =>
            let
              val tyderiv2_new = shift_typing_derivation_above d1 2 tyderiv2
              val tyrel2_new = extract_tyrel tyderiv2_new
              val tyderiv2_new = normalize tyderiv2_new (fn (tyderiv2_new, d2) => k (tyderiv2_new, List.concat [d2, List.take (#1 tyrel2_new, 2), d1]))
              val tyrel2_new = extract_tyrel tyderiv2_new
              val tyrel1_new = extract_tyrel tyderiv1_new
              val ty2_wrap = Passes.TermShift.shift_constr (List.length d1 + 2) (#3 tyrel)
              val ti2_wrap = Passes.TermShift.shift_constr (List.length d1 + 2) (#4 tyrel)
              val ti2_inner_wrap = CstrBinOp (CstrBopDiff, ti2_wrap, Passes.TermShift.shift_constr 2 (#4 tyrel1_new))
              val tyderiv2_wrap = TyDerivSub ((#1 tyrel2_new, #2 tyrel2_new, ty2_wrap, ti2_inner_wrap), tyderiv2_new, TyEqDerivAssume (#1 tyrel2_new, #3 tyrel2_new, ty2_wrap), PrDerivAdmit (#1 tyrel2_new, PrBinRel (PrRelLe, #4 tyrel2_new, ti2_inner_wrap)))
              val tyrel_new = (#1 tyrel1_new, TmUnpack (#2 tyrel1_new, #2 tyrel2_new), Passes.TermShift.shift_constr ~2 ty2_wrap, CstrBinOp (CstrBopAdd, #4 tyrel1_new, Passes.TermShift.shift_constr ~2 ti2_inner_wrap))
            in
              TyDerivUnpack (tyrel_new, tyderiv1_new, tyderiv2_wrap)
            end)
      | TyDerivCstrAbs (tyrel, kdwf1, tyderiv2) =>
          let
            val (kd1, tm2) = extract_tm_cstr_abs (#2 tyrel)
            val tyderiv2_new = normalize_derivation tyderiv2
            val tyrel2_new = extract_tyrel tyderiv2_new
            val tyrel_new = (#1 tyrel, TmCstrAbs (kd1, #2 tyrel2_new), #3 tyrel, CstrTime "0.0")
          in
            k (TyDerivCstrAbs (tyrel_new, kdwf1, tyderiv2_new), [])
          end
      | TyDerivCstrApp (tyrel, tyderiv1, kdderiv2) =>
          normalize_shift tyderiv1 (fn (tyderiv1_new, d1) =>
            let
              val kdderiv2_new = shift_kinding_derivation_above d1 0 kdderiv2
              val kdrel2_new = extract_kdrel kdderiv2_new
              val tyrel1_new = extract_tyrel tyderiv1_new
              val (ty_kind, ty_constr) = extract_cstr_forall (#3 tyrel1_new)
              val ty_new = Passes.TermSubstConstr.subst_constr_in_constr_top (#2 kdrel2_new) ty_constr
              val tyrel_new = (#1 tyrel1_new, TmCstrApp (#2 tyrel1_new, #2 kdrel2_new), ty_new, #4 tyrel1_new)
            in
              k (TyDerivCstrApp (tyrel_new, tyderiv1_new, kdderiv2_new), d1)
            end)
      | TyDerivBinOp (tyrel, tyderiv1, tyderiv2) =>
          normalize_shift tyderiv1 (fn (tyderiv1_new, d1) =>
            normalize_shift (shift_typing_derivation_above d1 0 tyderiv2) (fn (tyderiv2_new, d2) =>
              let
                val (bop, tm1, tm2) = extract_tm_bin_op (#2 tyrel)
                val tyderiv1_new = shift_typing_derivation_above d2 0 tyderiv1_new
                val tyrel1_new = extract_tyrel tyderiv1_new
                val tyrel2_new = extract_tyrel tyderiv2_new
                val tyrel_new = (#1 tyrel2_new, TmBinOp (bop, #2 tyrel1_new, #2 tyrel2_new), #1 (term_bin_op_to_constr bop), CstrBinOp (CstrBopAdd, #4 tyrel1_new, #4 tyrel2_new))
              in
                k (TyDerivBinOp (tyrel_new, tyderiv1_new, tyderiv2_new), List.concat [d2, d1])
              end))
      | TyDerivArrayNew (tyrel, tyderiv1, tyderiv2) =>
          normalize_shift tyderiv1 (fn (tyderiv1_new, d1) =>
            normalize_shift (shift_typing_derivation_above d1 0 tyderiv2) (fn (tyderiv2_new, d2) =>
              let
                val tyderiv1_new = shift_typing_derivation_above d2 0 tyderiv1_new
                val tyrel1_new = extract_tyrel tyderiv1_new
                val tyrel2_new = extract_tyrel tyderiv2_new
                val tyrel_new = (#1 tyrel2_new, TmArrayNew (#2 tyrel1_new, #2 tyrel2_new), CstrTypeArray (#3 tyrel2_new, extract_cstr_type_nat (#3 tyrel1_new)), CstrBinOp (CstrBopAdd, #4 tyrel1_new, #4 tyrel2_new))
              in
                k (TyDerivArrayNew (tyrel_new, tyderiv1_new, tyderiv2_new), List.concat [d2, d1])
              end))
      | TyDerivArrayGet (tyrel, tyderiv1, tyderiv2, prderiv3) =>
          normalize_shift tyderiv1 (fn (tyderiv1_new, d1) =>
            normalize_shift (shift_typing_derivation_above d1 0 tyderiv2) (fn (tyderiv2_new, d2) =>
              let
                val tyderiv1_new = shift_typing_derivation_above d2 0 tyderiv1_new
                val prderiv3_new = shift_proping_derivation_above (List.concat [d2, d1]) 0 prderiv3
                val tyrel1_new = extract_tyrel tyderiv1_new
                val tyrel2_new = extract_tyrel tyderiv2_new
                val tyrel_new = (#1 tyrel2_new, TmArrayGet (#2 tyrel1_new, #2 tyrel2_new), #1 (extract_cstr_type_array (#3 tyrel1_new)), CstrBinOp (CstrBopAdd, #4 tyrel1_new, #4 tyrel2_new))
              in
                k (TyDerivArrayGet (tyrel_new, tyderiv1_new, tyderiv2_new, prderiv3_new), List.concat [d2, d1])
              end))
      | TyDerivArrayPut (tyrel, tyderiv1, tyderiv2, prderiv3, tyderiv4) =>
          normalize_shift tyderiv1 (fn (tyderiv1_new, d1) =>
            normalize_shift (shift_typing_derivation_above d1 0 tyderiv2) (fn (tyderiv2_new, d2) =>
              normalize_shift (shift_typing_derivation_above (List.concat [d2, d1]) 0 tyderiv4) (fn (tyderiv4_new, d4) =>
                let
                  val tyderiv1_new = shift_typing_derivation_above (List.concat [d4, d2]) 0 tyderiv1_new
                  val tyderiv2_new = shift_typing_derivation_above d4 0 tyderiv2_new
                  val prderiv3_new = shift_proping_derivation_above (List.concat [d4, d2, d1]) 0 prderiv3
                  val tyrel1_new = extract_tyrel tyderiv1_new
                  val tyrel2_new = extract_tyrel tyderiv2_new
                  val tyrel4_new = extract_tyrel tyderiv4_new
                  val inner_tyderiv_new = k (TyDerivUnit (BdType CstrUnit :: (#1 tyrel4_new), TmUnit, CstrUnit, CstrNat 0), BdType CstrUnit :: (List.concat [d4, d2, d1]))
                  val inner_tyrel_new = extract_tyrel inner_tyderiv_new
                  val rand_tyrel_new = (#1 tyrel4_new, TmArrayPut (#2 tyrel1_new, #2 tyrel2_new, #2 tyrel4_new), CstrUnit, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, #4 tyrel1_new, #4 tyrel2_new), #4 tyrel4_new))
                  val rand_tyderiv_new = TyDerivArrayPut (rand_tyrel_new, tyderiv1_new, tyderiv2_new, prderiv3_new, tyderiv4_new)
                  val tyrel_new = (#1 tyrel4_new, TmLet (TmArrayPut (#2 tyrel1_new, #2 tyrel2_new, #2 tyrel4_new), #2 inner_tyrel_new), Passes.TermShift.shift_constr ~1 (#3 inner_tyrel_new), CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, CstrBinOp (CstrBopAdd, #4 tyrel1_new, #4 tyrel2_new), #4 tyrel4_new), Passes.TermShift.shift_constr ~1 (#4 inner_tyrel_new)))
                in
                  TyDerivLet (tyrel_new, rand_tyderiv_new, inner_tyderiv_new)
                end)))
      | TyDerivLet (tyrel, tyderiv2, tyderiv3) =>
          normalize tyderiv2 (fn (tyderiv2_new, d1) =>
            let
              val tyderiv3_new = shift_typing_derivation_above d1 1 tyderiv3
              val tyrel3_new = extract_tyrel tyderiv3_new
              val tyderiv3_new = normalize tyderiv3_new (fn (tyderiv3_new, d2) => k (tyderiv3_new, List.concat [d2, List.take (#1 tyrel3_new, 1), d1]))
              val tyrel3_new = extract_tyrel tyderiv3_new
              val tyrel2_new = extract_tyrel tyderiv2_new
              val tyrel_new = (#1 tyrel2_new, TmLet (#2 tyrel2_new, #2 tyrel3_new), Passes.TermShift.shift_constr ~1 (#3 tyrel2_new), CstrBinOp (CstrBopAdd, #4 tyrel2_new, Passes.TermShift.shift_constr ~1 (#4 tyrel3_new)))
            in
              TyDerivLet (tyrel_new, tyderiv2_new, tyderiv3_new)
            end)
      | TyDerivNever _ => k (tyderiv, [])
      | TyDerivFixAbs _ => raise (Impossible "not in the source language")

    and normalize_shift tyderiv k =
      normalize tyderiv (fn (tyderiv, d) =>
        let
          val tyrel = extract_tyrel tyderiv
        in
          if is_value (#2 tyrel) then
            k (tyderiv, d)
          else
            let
              val ty = #3 tyrel
              val tyrel_intro_var = (BdType ty :: (#1 tyrel), TmVar 0, Passes.TermShift.shift_constr 1 ty, CstrTime "0.0")
              val tyderiv_intro_var = TyDerivVar tyrel_intro_var
              val res = k (tyderiv_intro_var, BdType ty :: d)
              val tyrel_res = extract_tyrel res
              val tm = TmLet (#2 tyrel, #2 tyrel_res)
              val tyrel_let = (#1 tyrel, tm, Passes.TermShift.shift_constr ~1 (#3 tyrel_res), CstrBinOp (CstrBopAdd, #4 tyrel, Passes.TermShift.shift_constr ~1 (#4 tyrel_res)))
              val tyderiv_let = TyDerivLet (tyrel_let, tyderiv, res)
            in
              tyderiv_let
            end
        end)
  end

  structure FV =
  struct
    (* FIXME: quadratic time complexity *)
    structure FVHelper =
    struct
      type down = int
      type up = int list * int list

      val upward_base = ([], [])
      fun merge s1 s2 = s1 @ (List.filter (fn x => List.all (fn (y : int) => x <> y) s1) s2)
      fun combiner ((ftv1, fcv1), (ftv2, fcv2)) = (merge ftv1 ftv2, merge fcv1 fcv2)

      fun on_typing_relation (rel as (ctx, tm, ty, ti), down) = (rel, combiner (combiner (Passes.FV.free_variables_term tm down, Passes.FV.free_variables_constr ty down), Passes.FV.free_variables_constr ti down))
      fun on_kinding_relation (rel as (ctx, cstr, kd), down) = (rel, combiner (Passes.FV.free_variables_constr cstr down, Passes.FV.free_variables_kind kd down))
      fun on_proping_relation (rel as (ctx, pr), down) = (rel, Passes.FV.free_variables_prop pr down)
      fun on_kind_wellformness_relation (rel as (ctx, kd), down) = (rel, Passes.FV.free_variables_kind kd down)
      fun on_prop_wellformness_relation (rel as (ctx, pr), down) = (rel, Passes.FV.free_variables_prop pr down)
      fun on_type_equivalence_relation (rel as (ctx, ty1, ty2), down) = (rel, combiner (Passes.FV.free_variables_constr ty1 down, Passes.FV.free_variables_constr ty2 down))
      (*fun on_kind_equivalence_relation (rel as (ctx, kd1, kd2), down) = (rel, combiner (Passes.FV.free_variables_kind kd1 down, Passes.FV.free_variables_kind kd2 down))
      fun on_kind_sub_relation (rel as (ctx, kd1, kd2), down) = (rel, combiner (Passes.FV.free_variables_kind kd1 down, Passes.FV.free_variables_kind kd2 down))*)

      fun transformer_typing_derivation (on_tyderiv, on_kdderiv, on_prderiv, on_kdwf, on_tyeq) (tyderiv : typing_derivation, ctx : down) =
        let
          (*fun on_rel tyrel = on_typing_relation (tyrel, ctx)*)
        in
          case tyderiv of
            TyDerivAbs (tyrel, kdderiv1, tyderiv2) =>
              let
                (*val (tyrel, up0) = on_rel tyrel*)
                val (kdderiv1, up1) = on_kdderiv (kdderiv1, ctx)
                val (tyderiv2, up2) = on_tyderiv (tyderiv2, ctx + 1)
              in
                SOME (tyderiv, combiner (up1, up2))
              end
          | TyDerivRec (tyrel, kdderiv1, tyderiv2) =>
              let
                (*val (tyrel, up0) = on_rel tyrel*)
                val (kdderiv1, up1) = on_kdderiv (kdderiv1, ctx)
                val (tyderiv2, up2) = on_tyderiv (tyderiv2, ctx + 1)
              in
                SOME (tyderiv, combiner (up1, up2))
              end
          | TyDerivCase (tyrel, tyderiv1, tyderiv2, tyderiv3) =>
              let
                (*val (tyrel, up0) = on_rel tyrel*)
                val (tyderiv1, up1) = on_tyderiv (tyderiv1, ctx)
                val (tyderiv2, up2) = on_tyderiv (tyderiv2, ctx + 1)
                val (tyderiv3, up3) = on_tyderiv (tyderiv3, ctx + 1)
              in
                SOME (tyderiv, combiner (combiner (up1, up2), up3))
              end
          | TyDerivUnpack (tyrel, tyderiv1, tyderiv2) =>
              let
                (*val (tyrel, up0) = on_rel tyrel*)
                val (tyderiv1, up1) = on_tyderiv (tyderiv1, ctx)
                val (tyderiv2, up2) = on_tyderiv (tyderiv2, ctx + 2)
              in
                SOME (tyderiv, combiner (up1, up2))
              end
          | TyDerivCstrAbs (tyrel, kdwf1, tyderiv2) =>
              let
                (*val (tyrel, up0) = on_rel tyrel*)
                val (kdwf1, up1) = on_kdwf (kdwf1, ctx)
                val (tyderiv2, up2) = on_tyderiv (tyderiv2, ctx + 1)
              in
                SOME (tyderiv, combiner (up1, up2))
              end
          | TyDerivLet (tyrel, tyderiv2, tyderiv3) =>
              let
                (*val (tyrel, up0) = on_rel tyrel*)
                val (tyderiv2, up2) = on_tyderiv (tyderiv2, ctx)
                val (tyderiv3, up3) = on_tyderiv (tyderiv3, ctx + 1)
              in
                SOME (tyderiv, combiner (up2, up3))
              end
          | _ => NONE
        end

      fun transformer_kinding_derivation (on_kdderiv, on_prderiv, on_kdwf) (kdderiv : kinding_derivation, ctx : down) =
        let
          (*fun on_rel kdrel = on_kinding_relation (kdrel, ctx)*)
        in
          case kdderiv of
            KdDerivRefine (kdrel, kdderiv1, prderiv2) =>
              let
                (*val (kdrel, up0) = on_rel kdrel*)
                val (kdderiv1, up1) = on_kdderiv (kdderiv1, ctx)
                val (prderiv2, up2) = on_prderiv (prderiv2, ctx + 1)
              in
                SOME (kdderiv, combiner (up1, up2))
              end
          | KdDerivTimeAbs (kdrel, kdderiv1) =>
              let
                (*val (kdrel, up0) = on_rel kdrel*)
                val (kdderiv1, up1) = on_kdderiv (kdderiv1, ctx + 1)
              in
                SOME (kdderiv, up1)
              end
          | KdDerivAbs (kdrel, kdwf1, kdderiv2) =>
              let
                (*val (kdrel, up0) = on_rel kdrel*)
                val (kdwf1, up1) = on_kdwf (kdwf1, ctx)
                val (kdderiv2, up2) = on_kdderiv (kdderiv2, ctx + 1)
              in
                SOME (kdderiv, combiner (up1, up2))
              end
          | KdDerivForall (kdrel, kdwf1, kdderiv2) =>
              let
                (*val (kdrel, up0) = on_rel kdrel*)
                val (kdwf1, up1) = on_kdwf (kdwf1, ctx)
                val (kdderiv2, up2) = on_kdderiv (kdderiv2, ctx + 1)
              in
                SOME (kdderiv, combiner (up1, up2))
              end
          | KdDerivExists (kdrel, kdwf1, kdderiv2) =>
              let
                (*val (kdrel, up0) = on_rel kdrel*)
                val (kdwf1, up1) = on_kdwf (kdwf1, ctx)
                val (kdderiv2, up2) = on_kdderiv (kdderiv2, ctx + 1)
              in
                SOME (kdderiv, combiner (up1, up2))
              end
          | KdDerivRec (kdrel, kdwf1, kdderiv2) =>
              let
                (*val (kdrel, up0) = on_rel kdrel*)
                val (kdwf1, up1) = on_kdwf (kdwf1, ctx)
                val (kdderiv2, up2) = on_kdderiv (kdderiv2, ctx + 1)
              in
                SOME (kdderiv, combiner (up1, up2))
              end
          | _ => NONE
        end

      fun transformer_proping_derivation _ = NONE

      fun transformer_kind_wellformness_derivation (on_kdwf, on_prwf) (kdwf : kind_wellformedness_derivation, ctx : down) =
        let
          (*fun on_rel kdrel = on_kind_wellformness_relation (kdrel, ctx)*)
        in
          case kdwf of
            KdWfDerivSubset (kdrel, kdwf1, prwf2) =>
              let
                (*val (kdrel, up0) = on_rel kdrel*)
                val (kdwf1, up1) = on_kdwf (kdwf1, ctx)
                val (prwf2, up2) = on_prwf (prwf2, ctx + 1)
              in
                SOME (kdwf, combiner (up1, up2))
              end
          | _ => NONE
        end

      fun transformer_prop_wellformness_derivation (on_prwf, on_kdwf, on_kdderiv) (prwf : prop_wellformedness_derivation, ctx : down) =
        let
          (*fun on_rel prrel = on_prop_wellformness_relation (prrel, ctx)*)
        in
          case prwf of
            PrWfDerivForall (prrel, kdwf1, prwf2) =>
              let
                (*val (prrel, up0) = on_rel prrel*)
                val (kdwf1, up1) = on_kdwf (kdwf1, ctx)
                val (prwf2, up2) = on_prwf (prwf2, ctx + 1)
              in
                SOME (prwf, combiner (up1, up2))
              end
          | PrWfDerivExists (prrel, kdwf1, prwf2) =>
              let
                (*val (prrel, up0) = on_rel prrel*)
                val (kdwf1, up1) = on_kdwf (kdwf1, ctx)
                val (prwf2, up2) = on_prwf (prwf2, ctx + 1)
              in
                SOME (prwf, combiner (up1, up2))
              end
          | _ => NONE
        end

      fun transformer_type_equivalence_derivation (on_tyeq, on_kdeq, on_prderiv) (tyeq : type_equivalence_derivation, ctx : down) =
        let
          (*fun on_rel tyrel = on_type_equivalence_relation (tyrel, ctx)*)
        in
          case tyeq of
            TyEqDerivForall (tyrel, kdeq1, tyeq2) =>
              let
                (*val (tyrel, up0) = on_rel tyrel*)
                val (kdeq1, up1) = on_kdeq (kdeq1, ctx)
                val (tyeq2, up2) = on_tyeq (tyeq2, ctx + 1)
              in
                SOME (tyeq, combiner (up1, up2))
              end
          | TyEqDerivExists (tyrel, kdeq1, tyeq2) =>
              let
                (*val (tyrel, up0) = on_rel tyrel*)
                val (kdeq1, up1) = on_kdeq (kdeq1, ctx)
                val (tyeq2, up2) = on_tyeq (tyeq2, ctx + 1)
              in
                SOME (tyeq, combiner (up1, up2))
              end
          | TyEqDerivRec (tyrel, kdeq1, tyeq2) =>
              let
                (*val (tyrel, up0) = on_rel tyrel*)
                val (kdeq1, up1) = on_kdeq (kdeq1, ctx)
                val (tyeq2, up2) = on_tyeq (tyeq2, ctx + 1)
              in
                SOME (tyeq, combiner (up1, up2))
              end
          | TyEqDerivAbs (tyrel, kdeq1, tyeq2) =>
              let
                (*val (tyrel, up0) = on_rel tyrel*)
                val (kdeq1, up1) = on_kdeq (kdeq1, ctx)
                val (tyeq2, up2) = on_tyeq (tyeq2, ctx + 1)
              in
                SOME (tyeq, combiner (up1, up2))
              end
          | _ => NONE
        end

      fun transformer_kind_equivalence_derivation _ _ = NONE

      fun transformer_kind_sub_derivation _ _ = NONE
    end

    structure FVIns = TypingDerivationTransformPass(FVHelper)
    open FVIns

    fun free_variables_typing_derivation tyderiv ctx = #2 (transform_typing_derivation (tyderiv, ctx))
    fun free_variables_kinding_derivation kdderiv ctx = #2 (transform_kinding_derivation (kdderiv, ctx))
    fun free_variables_proping_derivation prderiv ctx = #2 (transform_proping_derivation (prderiv, ctx))
    fun free_variables_kind_wellformness_derivation kdwf ctx = #2 (transform_kind_wellformness_derivation (kdwf, ctx))
    fun free_variables_prop_wellformness_derivation prwf ctx = #2 (transform_prop_wellformness_derivation (prwf, ctx))
  end

  structure CloConv =
  struct
    structure CloConvHelper =
    struct
      type down = unit
      type up = unit

      val upward_base = ()
      fun combiner ((), ()) = ()

      fun transform_type ty =
        case ty of
          CstrArrow (ty1, ty2, ti) =>
            let
              val ty1 = transform_type ty1
              val ty2 = transform_type ty2
            in
              CstrExists (KdProper, CstrProd (CstrArrow (CstrProd (CstrVar 0, Passes.TermShift.shift_constr 1 ty1), Passes.TermShift.shift_constr 1 ty2, Passes.TermShift.shift_constr 1 ti), CstrVar 0))
            end
        (*| CstrForall (kd1, ty2) =>
            let
              val ty2 = transform_type ty2
            in
              CstrExists (KdProper, CstrProd (CstrForall (Passes.TermShift.shift_kind 1 kd1, CstrArrow (CstrVar 1, Passes.TermShift.shift_constr_above 1 1 ty2, CstrTime "0.0")), CstrVar 0))
            end*)
        | _ => ty

      fun on_typing_relation (rel as (ctx, tm, ty, ti), ()) = ((ctx, tm, transform_type ty, ti), ())
      fun on_kinding_relation ((ctx, cstr, kd), ()) = ((ctx, transform_type cstr, kd), ())
      fun on_proping_relation (rel, ()) = (rel, ())
      fun on_kind_wellformness_relation (rel, ()) = (rel, ())
      fun on_prop_wellformness_relation (rel, ()) = (rel, ())
      fun on_type_equivalence_relation (rel as (ctx, ty1, ty2), ()) = ((ctx, transform_type ty1, transform_type ty2), ())
      (*fun on_kind_equivalence_relation (rel, ()) = (rel, ())
      fun on_kind_sub_relation (rel, ()) = (rel, ())*)

      fun get_bind (ctx : context, i : int) =
        let
          val bd = List.nth (ctx, i)
        in
          case bd of
            BdType ty => BdType (Passes.TermShift.shift_constr (i + 1) ty)
          | BdKind kd => BdKind (Passes.TermShift.shift_kind (i + 1) kd)
        end

      fun get_type (BdType ty) = ty
        | get_type _ = raise (Impossible "must be type")

      fun get_kind (BdKind kd) = kd
        | get_kind _ = raise (Impossible "must be kind")

      fun assoc (x : int) ls =
        case ls of
          [] => raise Subscript
        | (a, b) :: tl => if a = x then b else assoc x tl

      fun transformer_typing_derivation (on_tyderiv : typing_derivation * down -> typing_derivation * up, on_kdderiv, on_prderiv, on_kdwf, on_tyeq) (tyderiv : typing_derivation, ()) =
        case tyderiv of
          TyDerivAbs ((ctx, tm as TmAbs (ty1, tm2), ty_arrow, _), kdderiv1, tyderiv2) =>
            let
              val (ftv, fcv) = FV.free_variables_typing_derivation tyderiv 0
              val ftv = ListMergeSort.sort (op>) ftv
              val types = List.map (fn i => get_type (get_bind (ctx, i))) ftv
              (*val fcv = #2 (FV.combine (([], fcv) :: List.map (fn ty => #2 (Passes.FV.transform_constr (ty, 0))) types))
              fun trace cur_fcv new_fcv delta_fcv =
                case new_fcv of
                  [] =>
                    let
                      val new_cur_fcv = #2 (Passes.FV.combine [([], cur_fcv), ([], delta_fcv)])
                    in
                      if List.length cur_fcv = List.length new_cur_fcv then
                        cur_fcv
                      else
                        trace new_cur_fcv delta_fcv []
                    end
                | hd :: tl =>
                    trace (hd :: cur_fcv) tl (#2 (Passes.FV.combine [([], delta_fcv), #2 (Passes.FV.transform_kind (case get_bind (ctx, hd) of BdKind kd => kd | _ => raise (Impossible "must be kind"), 0))]))
              val fcv = trace [] fcv []*)
              val fcv = ListMergeSort.sort (op>) fcv
              val kinds = List.map (fn i => get_kind (get_bind (ctx, i))) fcv
              val env = List.foldr (fn ((kd, n), env) =>
                (List.foldli (fn (i, (_, m), kd) => #1 (Passes.TermSubstConstr.transform_kind (kd, (m, CstrVar (i - m))))) kd env, n) :: env) [] (ListPair.zip (kinds, fcv))
              val kinds = List.map (fn (kd, _) => kd) env
              val types = List.foldr (fn (ty, ls) => (List.foldli (fn (i, (_, m), ty) => #1 (Passes.TermSubstConstr.transform_constr (ty, (m, CstrVar (i - m))))) ty env) :: ls) [] types
              val ty_arg = List.foldli (fn (i, (_, m), ty) => #1 (Passes.TermSubstConstr.transform_constr (ty, (m, CstrVar (i - m))))) ty1 env
              val ty_arrow_new = List.foldli (fn (i, (_, m), ty) => #1 (Passes.TermSubstConstr.transform_constr (ty, (m, CstrVar (i - m))))) ty_arrow env
              val ty_env =
                case List.length types of
                  0 => CstrTypeUnit
                | 1 => hd types
                | _ => List.foldl (fn (a, b) => CstrProd (a, b)) (CstrProd (hd (tl types), hd types)) (tl (tl types))
              val ty1_new = CstrProd (ty_env, ty_arg)
              val ctx_new = List.foldr (fn (kd, ctx) => BdKind kd :: ctx) [] kinds
              val ctx_inner_new = BdType ty1_new :: ctx_new
              val ctx_inner_bind =
                case List.length types of
                  0 => BdType (Passes.TermShift.shift_constr 1 ty_env) :: ctx_inner_new
                | 1 => BdType (Passes.TermShift.shift_constr 1 ty_env) :: ctx_inner_new
                | _ =>
                    let
                      fun inner wrapped d ctx =
                        case wrapped of
                          CstrProd (a, b) =>
                            if d = 0 then
                              let
                                val dep = (List.length types - 1) * 2
                              in
                                BdType (Passes.TermShift.shift_constr (dep + 1) b) :: BdType (Passes.TermShift.shift_constr dep a) :: ctx
                              end
                            else
                              let
                                val dep = (List.length types - d - 1) * 2
                              in
                                inner b (d - 1) (BdType (Passes.TermShift.shift_constr (dep + 1) b) :: BdType (Passes.TermShift.shift_constr dep a) :: ctx)
                              end
                        | _ => raise (Impossible "must be product type")
                    in
                      inner ty_env (List.length types - 2) (BdType (Passes.TermShift.shift_constr 1 ty_env) :: ctx_inner_new)
                    end
              val bind_depth = if List.length types = 0 then 2 else 2 * List.length types
              val ctx_inner_final = BdType (Passes.TermShift.shift_constr bind_depth ty_arg) :: ctx_inner_bind
              val kdderiv1_arg = TypingDerivationChangeContext.change_context_kinding_derivation (List.foldli (fn (i, (_, m), kdderiv) => #1 (TypingDerivationSubstConstr.transform_kinding_derivation (kdderiv, (m, CstrVar (i - m))))) kdderiv1 env) ctx_new
              val kdderiv1_env = KdDerivAssume (ctx_new, ty_env, KdProper)
              val kdderiv1_new = KdDerivProd ((ctx_new, ty1_new, KdProper), kdderiv1_env, kdderiv1_arg)
              val tyderiv2_new = List.foldli (fn (i, (_, m), tyderiv) => #1 (TypingDerivationSubstConstr.transform_typing_derivation (tyderiv, (m + 1, CstrVar (i - m + bind_depth))))) tyderiv2 env
              val tyderiv2_new =
                case List.length types of
                  0 => tyderiv2_new
                | 1 => #1 (TypingDerivationSubstTerm.transform_typing_derivation (tyderiv2_new, (hd ftv + 1, TmVar (0 - (hd ftv)))))
                | _ => List.foldli (fn (i, m, tyderiv) => #1 (TypingDerivationSubstTerm.transform_typing_derivation (tyderiv, (m + 1, TmVar (i - m + (if i = 0 then 0 else i - 1)))))) tyderiv2_new ftv
              val tyderiv2_new = TypingDerivationChangeContext.change_context_typing_derivation tyderiv2_new ctx_inner_final
              val tyderiv2_new = #1 (on_tyderiv (tyderiv2_new, ()))
              val tyrel2_new = extract_tyrel tyderiv2_new
              val tyderiv2_new = TyDerivLet ((ctx_inner_bind, TmLet (TmSnd (TmVar (bind_depth - 1)) , #2 tyrel2_new), Passes.TermShift.shift_constr ~1 (#3 tyrel2_new), CstrBinOp (CstrBopAdd, CstrTime "0.0", Passes.TermShift.shift_constr ~1 (#4 tyrel2_new))), TyDerivSnd ((ctx_inner_bind, TmSnd (TmVar (bind_depth - 1)), Passes.TermShift.shift_constr bind_depth ty_arg, CstrTime "0.0"), TyDerivVar (ctx_inner_bind, TmVar (bind_depth - 1), Passes.TermShift.shift_constr bind_depth ty1_new, CstrTime "0.0")), tyderiv2_new)
              val tyderiv2_new =
                case List.length types of
                  0 => tyderiv2_new
                | 1 => tyderiv2_new
                | _ => List.foldli (fn (i, ty, tyderiv) =>
                    let
                      val tyrel = extract_tyrel tyderiv
                    in
                      if i = 0 then
                        TyDerivLet ((tl (#1 tyrel), TmLet (TmSnd (TmVar 1), #2 tyrel), Passes.TermShift.shift_constr ~1 (#3 tyrel), CstrBinOp (CstrBopAdd, CstrTime "0.0", Passes.TermShift.shift_constr ~1 (#4 tyrel))), TyDerivSnd ((tl (#1 tyrel), TmSnd (TmVar 1), Passes.TermShift.shift_constr (bind_depth - 1) ty, CstrTime "0.0"), TyDerivVar (tl (#1 tyrel), TmVar 1, get_type (get_bind (tl (#1 tyrel), 1)), CstrTime "0.0")), tyderiv)
                        else
                          if i = List.length types - 1 then
                            TyDerivLet ((tl (#1 tyrel), TmLet (TmFst (TmVar 0), #2 tyrel), Passes.TermShift.shift_constr ~1 (#3 tyrel), CstrBinOp (CstrBopAdd, CstrTime "0.0", Passes.TermShift.shift_constr ~1 (#4 tyrel))), TyDerivFst ((tl (#1 tyrel), TmFst (TmVar 0), Passes.TermShift.shift_constr 2 ty, CstrTime "0.0"), TyDerivVar (tl (#1 tyrel), TmVar 0, get_type (get_bind (tl (#1 tyrel), 0)), CstrTime "0.0")), tyderiv)
                          else
                            let
                              val one = TyDerivLet ((tl (#1 tyrel), TmLet (TmFst (TmVar 0), #2 tyrel), Passes.TermShift.shift_constr ~1 (#3 tyrel), CstrBinOp (CstrBopAdd, CstrTime "0.0", Passes.TermShift.shift_constr ~1 (#4 tyrel))), TyDerivFst ((tl (#1 tyrel), TmFst (TmVar 0), Passes.TermShift.shift_constr (bind_depth - 2 * i) ty, CstrTime "0.0"), TyDerivVar (tl (#1 tyrel), TmVar 0, get_type (get_bind (tl (#1 tyrel), 0)), CstrTime "0.0")), tyderiv)
                              val tyrel = extract_tyrel one
                              val two = TyDerivLet ((tl (#1 tyrel), TmLet (TmSnd (TmVar 1), #2 tyrel), Passes.TermShift.shift_constr ~1 (#3 tyrel), CstrBinOp (CstrBopAdd, CstrTime "0.0", Passes.TermShift.shift_constr ~1 (#4 tyrel))), TyDerivSnd ((tl (#1 tyrel), TmSnd (TmVar 1), get_type (hd (#1 tyrel)), CstrTime "0.0"), TyDerivVar (tl (#1 tyrel), TmVar 1, get_type (get_bind (tl (#1 tyrel), 1)), CstrTime "0.0")), one)
                            in
                              two
                            end
                    end) tyderiv2_new types
              val tyrel2_new = extract_tyrel tyderiv2_new
              val tyderiv2_new = TyDerivLet ((ctx_inner_new, TmLet (TmFst (TmVar 0), #2 tyrel2_new), Passes.TermShift.shift_constr ~1 (#3 tyrel2_new), CstrBinOp (CstrBopAdd, CstrTime "0.0", Passes.TermShift.shift_constr ~1 (#4 tyrel2_new))), TyDerivFst ((ctx_inner_new, TmFst (TmVar 0), Passes.TermShift.shift_constr 1 ty_env, CstrTime "0.0"), TyDerivVar (ctx_inner_new, TmVar 0, Passes.TermShift.shift_constr 1 ty1_new, CstrTime "0.0")), tyderiv2_new)
              val tyrel2_new = extract_tyrel tyderiv2_new
              val tyderiv_new = TyDerivAbs ((ctx_new, TmAbs (ty1, #2 tyrel2_new), ty_arrow_new, CstrTime "0.0"), kdderiv1_new, tyderiv2_new)
              val tyderiv_new = List.foldl (fn (kd, tyderiv) =>
                let
                  val tyrel = extract_tyrel tyderiv
                in
                  TyDerivCstrAbs ((tl (#1 tyrel), TmCstrAbs (kd, #2 tyrel), CstrForall (kd, #3 tyrel), Passes.TermShift.shift_constr ~1 (#4 tyrel)), KdWfDerivAssume (tl (#1 tyrel), kd), tyderiv)
                end) tyderiv_new kinds
              val tyderiv_new = List.foldr (fn (n, tyderiv) =>
                let
                  val tyrel = extract_tyrel tyderiv
                  val (kd1, ty_body) = extract_cstr_forall (#3 tyrel)
                in
                  TyDerivCstrApp ((#1 tyrel, TmCstrApp (#2 tyrel, CstrVar n), Passes.TermSubstConstr.subst_constr_in_constr_top (CstrVar n) ty_body, #4 tyrel), tyderiv, KdDerivVar (#1 tyrel, CstrVar n, get_kind (get_bind (#1 tyrel, n))))
                end) tyderiv_new fcv
            in
              SOME (tyderiv_new, ())
            end
        | TyDerivRec (tyrel, kdderiv1, tyderiv2) =>
            NONE
        | TyDerivCstrAbs (tyrel, kdwf1, tyderiv2) =>
            NONE
        | TyDerivApp (tyrel, tyderiv1, tyderiv2) =>
            NONE
        | TyDerivCstrApp (tyrel, tyderiv1, kdderiv2) =>
            NONE
        | _ => NONE

      fun transformer_kinding_derivation _ _ = NONE

      fun transformer_proping_derivation _ = NONE

      fun transformer_kind_wellformness_derivation _ _ = NONE

      fun transformer_prop_wellformness_derivation _ _ = NONE

      fun transformer_type_equivalence_derivation _ _ = NONE

      fun transformer_kind_equivalence_derivation _ _ = NONE

      fun transformer_kind_sub_derivation _ _ = NONE
    end

    structure CloConvIns = TypingDerivationTransformPass(CloConvHelper)
    open CloConvIns
  end
end
