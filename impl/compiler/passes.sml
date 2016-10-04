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

    structure TermShiftIns = TermTransformPass(TermShiftHelper)
    open TermShiftIns

    fun shift_constr_above d c cstr = #1 (transform_constr (cstr, (c, d)))
    fun shift_constr d cstr = shift_constr_above d 0 cstr

    fun shift_kind_above d c kd = #1 (transform_kind (kd, (c, d)))
    fun shift_kind d kd = shift_kind_above d 0 kd

    fun shift_prop_above d c pr = #1 (transform_prop (pr, (c, d)))
    fun shift_prop d pr = shift_prop_above d 0 pr

    fun shift_term_above d c tm = #1 (transform_term (tm, (c, d)))
    fun shift_term d tm = shift_term_above d 0 tm
  end

  structure Printer =
  struct
    structure PrinterHelper =
    struct
      type down = string list
      type up = string

      val upward_base = ""
      fun combiner (_, _) = ""

      fun transformer_constr _ (cstr, _) = SOME (cstr, "<constr>")

      fun transformer_kind _ (kd, _) = SOME (kd, "<kind>")

      fun transformer_prop _ (pr, _) = SOME (pr, "<prop>")

      open Util

      val gensym =
        let
          val counter = ref 0
        in
          fn () =>
            let
              val res = "%var" ^ (str_int (!counter))
              val _ = inc counter
            in
              res
            end
        end

      fun transformer_term (transform_constr : constr * down -> constr * up, transform_kind : kind * down -> kind * up, transform_term : term * down -> term * up) (tm : term, ctx : down) =
        SOME (tm, Option.valOf (case tm of
          TmVar x => SOME (List.nth (ctx, x))
        | TmInt i => SOME (str_int i)
        | TmNat n => SOME ("#" ^ str_int n)
        | TmUnit => SOME "()"
        | TmApp (tm1, tm2) => SOME ("(" ^ #2 (transform_term (tm1, ctx)) ^ " " ^ #2 (transform_term (tm2, ctx)) ^ ")")
        | TmAbs (cstr1, tm2) =>
            let
              val fresh = gensym ()
            in
              SOME ("(lambda (" ^ fresh ^ " : " ^ #2 (transform_constr (cstr1, ctx)) ^ ") " ^ #2 (transform_term (tm2, fresh :: ctx)) ^ ")")
            end
        | TmRec (cstr1, tm2) => SOME ("(fix " ^ #2 (transform_constr (cstr1, ctx)) ^ " " ^ #2 (transform_term (tm2, gensym () :: ctx)) ^ ")")
        | TmPair (tm1, tm2) => SOME ("(cons " ^ #2 (transform_term (tm1, ctx)) ^ " " ^ #2 (transform_term (tm2, ctx)) ^ ")")
        | TmFst tm1 => SOME ("(fst " ^ #2 (transform_term (tm1, ctx)) ^ ")")
        | TmSnd tm2 => SOME ("(snd " ^ #2 (transform_term (tm2, ctx)) ^ ")")
        | TmInLeft tm1 => SOME ("(inl " ^ #2 (transform_term (tm1, ctx)) ^ ")")
        | TmInRight tm1 => SOME ("(inr " ^ #2 (transform_term (tm1, ctx)) ^ ")")
        | TmCase (tm1, tm2, tm3) =>
            let
              val fresh = gensym ()
            in
              SOME ("(case " ^ #2 (transform_term (tm1, ctx)) ^ " via " ^ fresh ^ " " ^ #2 (transform_term (tm2, fresh :: ctx)) ^ " " ^ #2 (transform_term (tm3, fresh :: ctx)) ^ ")")
            end
        | TmFold tm1 => SOME ("(fold " ^ #2 (transform_term (tm1, ctx)) ^ ")")
        | TmUnfold tm1 => SOME ("(unfold " ^ #2 (transform_term (tm1, ctx)) ^ ")")
        | TmPack (cstr1, tm2) => SOME ("<" ^ #2 (transform_constr (cstr1, ctx)) ^ " | " ^ #2 (transform_term (tm2, ctx)) ^ ">")
        | TmUnpack (tm1, tm2) =>
            let
              val fresh1 = gensym ()
              val fresh2 = gensym ()
            in
              SOME ("(unpack " ^ #2 (transform_term (tm1, ctx)) ^ " via <" ^ fresh1 ^ " | " ^ fresh2 ^ "> " ^ #2 (transform_term (tm2, fresh2 :: fresh1 :: ctx)) ^ ")")
            end
        | TmCstrAbs (kd1, tm2) =>
            let
              val fresh = gensym ()
            in
                SOME ("(Lambda (" ^ fresh ^ " : " ^ #2 (transform_kind (kd1, ctx)) ^ ") " ^ #2 (transform_term (tm2, fresh :: ctx)) ^ ")")
            end
        | TmCstrApp (tm1, cstr2) => SOME ("[" ^ #2 (transform_term (tm1, ctx)) ^ " " ^ #2 (transform_constr (cstr2, ctx)) ^ "]")
        | TmBinOp (bop, tm1, tm2) => SOME ("(" ^ #2 (transform_term (tm1, ctx)) ^ " <bop> " ^ #2 (transform_term (tm2, ctx)) ^ ")")
        | TmArrayNew (tm1, tm2) => SOME ("(newarray " ^ #2 (transform_term (tm1, ctx)) ^ " " ^ #2 (transform_term (tm2, ctx)) ^ ")")
        | TmArrayGet (tm1, tm2) => SOME ("(getarray " ^ #2 (transform_term (tm1, ctx)) ^ " " ^ #2 (transform_term (tm2, ctx)) ^ ")")
        | TmArrayPut (tm1, tm2, tm3) => SOME ("(putarray " ^ #2 (transform_term (tm1, ctx)) ^ " " ^ #2 (transform_term (tm2, ctx)) ^ " " ^ #2 (transform_term (tm3, ctx)) ^ ")")
        | TmLet (tm1, tm2) =>
            let
              val fresh = gensym ()
            in
              SOME ("(let ([" ^ fresh ^ " " ^ #2 (transform_term (tm1, ctx)) ^ "]) " ^ #2 (transform_term (tm2, fresh :: ctx)) ^ ")")
            end))
    end

    structure PrinterIns = TermTransformPass(PrinterHelper)
    open PrinterIns

    fun str_term tm = #2 (transform_term (tm, []))
  end

  structure ANF =
  struct
    fun is_value tm =
      case tm of
        TmVar _ => true
      | TmInt _ => true
      | TmNat _ => true
      | TmUnit => true
      | TmAbs _ => true
      | TmRec _ => true
      | TmCstrAbs _ => true
      | _ => false

    fun normalize_term tm = normalize tm (fn (x, d) => x)

    and normalize tm k =
      case tm of
        TmVar _ => k (tm, 0)
      | TmInt _ => k (tm, 0)
      | TmNat _ => k (tm, 0)
      | TmUnit => k (tm, 0)
      | TmApp (tm1, tm2) =>
          normalize_shift tm1 (fn (tm1, d1) =>
            normalize_shift (TermShift.shift_term_above d1 0 tm2) (fn (tm2, d2) =>
              k (TmApp (TermShift.shift_term_above d2 0 tm1, tm2), d1 + d2)))
      | TmAbs (cstr1, tm2) => k (TmAbs (cstr1, normalize_term tm2), 0)
      | TmRec (cstr1, tm2) => k (TmRec (cstr1, normalize_term tm2), 0)
      | TmPair (tm1, tm2) =>
          normalize_shift tm1 (fn (tm1, d1) =>
            normalize_shift (TermShift.shift_term_above d1 0 tm2) (fn (tm2, d2) =>
              k (TmPair (TermShift.shift_term_above d2 0 tm1, tm2), d1 + d2)))
      | TmFst tm1 => normalize_shift tm1 (fn (tm1, d1) => k (TmFst tm1, d1))
      | TmSnd tm1 => normalize_shift tm1 (fn (tm1, d1) => k (TmSnd tm1, d1))
      | TmInLeft tm1 => normalize_shift tm1 (fn (tm1, d1) => k (TmInLeft tm1, d1))
      | TmInRight tm1 => normalize_shift tm1 (fn (tm1, d1) => k (TmInRight tm1, d1))
      | TmCase (tm1, tm2, tm3) =>
          normalize_shift tm1 (fn (tm1, d1) =>
            k (TmCase (tm1, normalize_term (TermShift.shift_term_above d1 1 tm2), normalize_term (TermShift.shift_term_above d1 1 tm3)), d1))
      | TmFold tm1 => normalize_shift tm1 (fn (tm1, d1) => k (TmFold tm1, d1))
      | TmUnfold tm1 => normalize_shift tm1 (fn (tm1, d1) => k (TmUnfold tm1, d1))
      | TmPack (cstr1, tm2) => normalize_shift tm2 (fn (tm2, d2) => k (TmPack (TermShift.shift_constr_above d2 0 cstr1, tm2), d2))
      | TmUnpack (tm1, tm2) =>
          normalize_shift tm1 (fn (tm1, d1) =>
            k (TmUnpack (tm1, normalize_term (TermShift.shift_term_above d1 2 tm2)), d1))
      | TmCstrAbs (kd1, tm2) => k (TmCstrAbs (kd1, normalize_term tm2), 0)
      | TmCstrApp (tm1, cstr2) => normalize_shift tm1 (fn (tm1, d1) => k (TmCstrApp (tm1, TermShift.shift_constr_above d1 0 cstr2), d1))
      | TmBinOp (bop, tm1, tm2) =>
          normalize_shift tm1 (fn (tm1, d1) =>
            normalize_shift (TermShift.shift_term_above d1 0 tm2) (fn (tm2, d2) =>
              k (TmBinOp (bop, TermShift.shift_term_above d2 0 tm1, tm2), d1 + d2)))
      | TmArrayNew (tm1, tm2) =>
          normalize_shift tm1 (fn (tm1, d1) =>
            normalize_shift (TermShift.shift_term_above d1 0 tm2) (fn (tm2, d2) =>
              k (TmArrayNew (TermShift.shift_term_above d2 0 tm1, tm2), d1 + d2)))
      | TmArrayGet (tm1, tm2) =>
          normalize_shift tm1 (fn (tm1, d1) =>
            normalize_shift (TermShift.shift_term_above d1 0 tm2) (fn (tm2, d2) =>
              k (TmArrayGet (TermShift.shift_term_above d2 0 tm1, tm2), d1 + d2)))
      | TmArrayPut (tm1, tm2, tm3) =>
          normalize_shift tm1 (fn (tm1, d1) =>
            normalize_shift (TermShift.shift_term_above d1 0 tm2) (fn (tm2, d2) =>
              normalize_shift (TermShift.shift_term_above (d1 + d2) 0 tm3) (fn (tm3, d3) =>
                k (TmArrayPut (TermShift.shift_term_above (d2 + d3) 0 tm1, TermShift.shift_term_above d3 0 tm2, tm3), d1 + d2 + d3))))
      | TmLet (tm1, tm2) =>
          normalize tm1 (fn (tm1, d1) =>
            TmLet (tm1, normalize (TermShift.shift_term_above d1 1 tm2) (fn (tm2, d2) =>
              k (tm2, d1 + 1 + d2))))

    and normalize_shift tm k =
      normalize tm (fn (tm, d) => if is_value tm then k (tm, d) else TmLet (tm, k (TmVar 0, d + 1)))
  end
end
