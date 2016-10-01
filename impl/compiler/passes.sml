structure Passes =
struct
  open MicroTiML

  structure TermShiftHelper =
  struct
    type down = int * int
    type up = unit

    val upward_base = ()
    fun combiner ((), ()) = ()
    fun at_transform_end (tm, ()) = (tm, ())

    fun transformer transform (tm : term, (ctx, delta) : down) =
      case tm of
        TmVar x => SOME (TmVar (if x >= ctx then x + delta else x), ())
      | TmAbs (constr, tm1) =>
          let
            val (tm1, ()) = transform (tm1, (ctx + 1, delta))
          in
            SOME (TmAbs (constr, tm1), ())
          end
      | TmRec (constr, tm1) =>
          let
            val (tm1, ()) = transform (tm1, (ctx + 1, delta))
          in
            SOME (TmRec (constr, tm1), ())
          end
      | TmCase (tm1, tm2, tm3) =>
          let
            val (tm1, ()) = transform (tm1, (ctx, delta))
            val (tm2, ()) = transform (tm2, (ctx + 1, delta))
            val (tm3, ()) = transform (tm3, (ctx + 1, delta))
          in
            SOME (TmCase (tm1, tm2, tm3), ())
          end
      | TmUnpack (tm1, tm2) =>
          let
            val (tm1, ()) = transform (tm1, (ctx, delta))
            val (tm2, ()) = transform (tm2, (ctx + 2, delta))
          in
            SOME (TmUnpack (tm1, tm2), ())
          end
      | TmCstrAbs (kd, tm1) =>
          let
            val (tm1, ()) = transform (tm1, (ctx + 1, delta))
          in
            SOME (TmCstrAbs (kd, tm1), ())
          end
      | _ => NONE
  end

  structure TermShift =
  struct
    structure TermShiftHelper = TermTransformPass(TermShiftHelper)
    open TermShiftHelper

    fun shift_term_above d c tm = apply (c, d) tm
    fun shift_term d tm = shift_term_above d 0 tm
  end
end
