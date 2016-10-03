structure Passes =
struct
  open MicroTiML

  structure TermShift =
  struct
    structure TermShiftHelper =
    struct
      type down = int * int
      type up = unit

      val upward_base = ()
      fun combiner ((), ()) = ()

      fun transformer_constr (transform_constr, transform_kind) (cstr : constr, (ctx, delta) : down) =
        case cstr of
          CstrVar a => SOME (CstrVar (if a >= ctx then a + delta else a), ())
        | CstrTimeAbs cstr1 =>
            let
              val (cstr1, ()) = transform_constr (cstr1, (ctx + 1, delta))
            in
              SOME (CstrTimeAbs cstr1, ())
            end
        | CstrAbs (kd1, cstr2) =>
            let
              val (kd1, ()) = transform_kind (kd1, (ctx, delta))
              val (cstr2, ()) = transform_constr (cstr2, (ctx + 1, delta))
            in
              SOME (CstrAbs (kd1, cstr2), ())
            end
        | CstrForall (kd1, cstr2) =>
            let
              val (kd1, ()) = transform_kind (kd1, (ctx, delta))
              val (cstr2, ()) = transform_constr (cstr2, (ctx + 1, delta))
            in
              SOME (CstrForall (kd1, cstr2), ())
            end
        | CstrExists (kd1, cstr2) =>
            let
              val (kd1, ()) = transform_kind (kd1, (ctx, delta))
              val (cstr2, ()) = transform_constr (cstr2, (ctx + 1, delta))
            in
              SOME (CstrExists (kd1, cstr2), ())
            end
        | CstrRec (kd1, cstr2) =>
            let
              val (kd1, ()) = transform_kind (kd1, (ctx, delta))
              val (cstr2, ()) = transform_constr (cstr2, (ctx + 1, delta))
            in
              SOME (CstrRec (kd1, cstr2), ())
            end
        | _ => NONE

      fun transformer_kind (transform_kind, transform_prop) (kd : kind, (ctx, delta) : down) =
        case kd of
          KdSubset (kd1, pr2) =>
            let
              val (kd1, ()) = transform_kind (kd1, (ctx, delta))
              val (pr2, ()) = transform_prop (pr2, (ctx + 1, delta))
            in
              SOME (KdSubset (kd1, pr2), ())
            end
        | _ => NONE

      fun transformer_prop (transform_constr, transform_kind, transform_prop) (pr : prop, (ctx, delta) : down) =
        case pr of
          PrForall (kd1, pr2) =>
            let
              val (kd1, ()) = transform_kind (kd1, (ctx, delta))
              val (pr2, ()) = transform_prop (pr2, (ctx + 1, delta))
            in
              SOME (PrForall (kd1, pr2), ())
            end
        | PrExists (kd1, pr2) =>
            let
              val (kd1, ()) = transform_kind (kd1, (ctx, delta))
              val (pr2, ()) = transform_prop (pr2, (ctx + 1, delta))
            in
              SOME (PrExists (kd1, pr2), ())
            end
        | _ => NONE

      fun transformer_term (transform_constr, transform_kind, transform_term) (tm : term, (ctx, delta) : down) =
        case tm of
          TmVar x => SOME (TmVar (if x >= ctx then x + delta else x), ())
        | TmAbs (cstr1, tm2) =>
            let
              val (cstr1, ()) = transform_constr (cstr1, (ctx, delta))
              val (tm2, ()) = transform_term (tm2, (ctx + 1, delta))
            in
              SOME (TmAbs (cstr1, tm2), ())
            end
        | TmRec (cstr1, tm2) =>
            let
              val (cstr1, ()) = transform_constr (cstr1, (ctx, delta))
              val (tm2, ()) = transform_term (tm2, (ctx + 1, delta))
            in
              SOME (TmRec (cstr1, tm2), ())
            end
        | TmCase (tm1, tm2, tm3) =>
            let
              val (tm1, ()) = transform_term (tm1, (ctx, delta))
              val (tm2, ()) = transform_term (tm2, (ctx + 1, delta))
              val (tm3, ()) = transform_term (tm3, (ctx + 1, delta))
            in
              SOME (TmCase (tm1, tm2, tm3), ())
            end
        | TmUnpack (tm1, tm2) =>
            let
              val (tm1, ()) = transform_term (tm1, (ctx, delta))
              val (tm2, ()) = transform_term (tm2, (ctx + 2, delta))
            in
              SOME (TmUnpack (tm1, tm2), ())
            end
        | TmCstrAbs (kd1, tm2) =>
            let
              val (kd1, ()) = transform_kind (kd1, (ctx, delta))
              val (tm2, ()) = transform_term (tm2, (ctx + 1, delta))
            in
              SOME (TmCstrAbs (kd1, tm2), ())
            end
        | TmLet (tm1, tm2) =>
            let
              val (tm1, ()) = transform_term (tm1, (ctx, delta))
              val (tm2, ()) = transform_term (tm2, (ctx + 1, delta))
            in
              SOME (TmLet (tm1, tm2), ())
            end
        | _ => NONE
    end

    structure TermShiftHelper = TermTransformPass(TermShiftHelper)
    open TermShiftHelper

    fun shift_constr_above d c cstr = transform_constr (cstr, (c, d))
    fun shift_constr d cstr = shift_constr_above d 0 cstr

    fun shift_kind_above d c kd = transform_kind (kd, (c, d))
    fun shift_kind d kd = shift_kind_above d 0 kd

    fun shift_prop_above d c pr = transform_prop (pr, (c, d))
    fun shift_prop d pr = shift_prop_above d 0 pr

    fun shift_term_above d c tm = transform_term (tm, (c, d))
    fun shift_term d tm = shift_term_above d 0 tm
  end
end
