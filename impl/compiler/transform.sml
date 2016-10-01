functor TermTransformPass(Arg:
sig
  type down
  type up

  val transformer : ((MicroTiML.term * down) -> (MicroTiML.term * up)) -> (MicroTiML.term * down) -> (MicroTiML.term * up) option

  val upward_base : up
  val combiner : (up * up) -> up

  val at_transform_end : (MicroTiML.term * up) -> (MicroTiML.term * up)
end) =
struct
  open MicroTiML

  fun combine (ups : Arg.up list) = List.foldl Arg.combiner Arg.upward_base ups

  fun default_transform (tm : term, down : Arg.down) =
    case tm of
      TmVar x => (TmVar x, Arg.upward_base)
    | TmInt i => (TmInt i, Arg.upward_base)
    | TmNat n => (TmNat n, Arg.upward_base)
    | TmUnit => (TmUnit, Arg.upward_base)
    | TmApp (tm1, tm2) =>
        let
          val (tm1, up1) = transform (tm1, down)
          val (tm2, up2) = transform (tm2, down)
        in
          (TmApp (tm1, tm2), combine [up1, up2])
        end
    | TmAbs (cstr, tm1) =>
        let
          val (tm1, up1) = transform (tm1, down)
        in
          (TmAbs (cstr, tm1), combine [up1])
        end
    | TmRec (cstr, tm1) =>
        let
          val (tm1, up1) = transform (tm1, down)
        in
          (TmRec (cstr, tm1), combine [up1])
        end
    | TmPair (tm1, tm2) =>
        let
          val (tm1, up1) = transform (tm1, down)
          val (tm2, up2) = transform (tm2, down)
        in
          (TmPair (tm1, tm2), combine [up1, up2])
        end
    | TmFst tm1 =>
        let
          val (tm1, up1) = transform (tm1, down)
        in
          (TmFst tm1, combine [up1])
        end
    | TmSnd tm1 =>
        let
          val (tm1, up1) = transform (tm1, down)
        in
          (TmSnd tm1, combine [up1])
        end
    | TmInLeft tm1 =>
        let
          val (tm1, up1) = transform (tm1, down)
        in
          (TmInLeft tm1, combine [up1])
        end
    | TmInRight tm1 =>
        let
          val (tm1, up1) = transform (tm1, down)
        in
          (TmInRight tm1, combine [up1])
        end
    | TmCase (tm1, tm2, tm3) =>
        let
          val (tm1, up1) = transform (tm1, down)
          val (tm2, up2) = transform (tm2, down)
          val (tm3, up3) = transform (tm3, down)
        in
          (TmCase (tm1, tm2, tm3), combine [up1, up2, up3])
        end
    | TmFold tm1 =>
        let
          val (tm1, up1) = transform (tm1, down)
        in
          (TmFold tm1, combine [up1])
        end
    | TmUnfold tm1 =>
        let
          val (tm1, up1) = transform (tm1, down)
        in
          (TmUnfold tm1, combine [up1])
        end
    | TmPack (cstr, tm1) =>
        let
          val (tm1, up1) = transform (tm1, down)
        in
          (TmPack (cstr, tm1), combine [up1])
        end
    | TmUnpack (tm1, tm2) =>
        let
          val (tm1, up1) = transform (tm1, down)
          val (tm2, up2) = transform (tm2, down)
        in
          (TmUnpack (tm1, tm2), combine [up1, up2])
        end
    | TmCstrAbs (kd, tm1) =>
        let
          val (tm1, up1) = transform (tm1, down)
        in
          (TmCstrAbs (kd, tm1), combine [up1])
        end
    | TmCstrApp (tm1, cstr) =>
        let
          val (tm1, up1) = transform (tm1, down)
        in
          (TmCstrApp (tm1, cstr), combine [up1])
        end
    | TmBinOp (bop, tm1, tm2) =>
        let
          val (tm1, up1) = transform (tm1, down)
          val (tm2, up2) = transform (tm2, down)
        in
          (TmBinOp (bop, tm1, tm2), combine [up1, up2])
        end
    | TmArrayNew (tm1, tm2) =>
        let
          val (tm1, up1) = transform (tm1, down)
          val (tm2, up2) = transform (tm2, down)
        in
          (TmArrayNew (tm1, tm2), combine [up1, up2])
        end
    | TmArrayGet (tm1, tm2) =>
        let
          val (tm1, up1) = transform (tm1, down)
          val (tm2, up2) = transform (tm2, down)
        in
          (TmArrayGet (tm1, tm2), combine [up1, up2])
        end
    | TmArrayPut (tm1, tm2, tm3) =>
        let
          val (tm1, up1) = transform (tm1, down)
          val (tm2, up2) = transform (tm2, down)
          val (tm3, up3) = transform (tm3, down)
        in
          (TmArrayPut (tm1, tm2, tm3), combine [up1, up2, up3])
        end

  and transform (tm : term, down : Arg.down) =
    case Arg.transformer transform (tm, down) of
      SOME res => res
    | NONE => default_transform (tm, down)

  fun apply_with_down (tm : term, down : Arg.down) =
    let
      val res = transform (tm, down)
    in
      Arg.at_transform_end res
    end

  fun apply (downward_base : Arg.down) (tm : term) = #1 (apply_with_down (tm, downward_base))
end

functor TermThreadedTransformPass(Arg:
sig
  type thread

  val transformer : ((MicroTiML.term * thread) -> (MicroTiML.term * thread)) -> (MicroTiML.term * thread) -> (MicroTiML.term * thread) option

  val at_transform_end : (MicroTiML.term * thread) -> (MicroTiML.term * thread)
end) =
struct
  open MicroTiML

  fun default_transform (tm : term, thread : Arg.thread) =
    case tm of
      TmVar x => (TmVar x, thread)
    | TmInt i => (TmInt i, thread)
    | TmNat n => (TmNat n, thread)
    | TmUnit => (TmUnit, thread)
    | TmApp (tm1, tm2) =>
        let
          val (tm1, thread) = transform (tm1, thread)
          val (tm2, thread) = transform (tm2, thread)
        in
          (TmApp (tm1, tm2), thread)
        end
    | TmAbs (cstr, tm1) =>
        let
          val (tm1, thread) = transform (tm1, thread)
        in
          (TmAbs (cstr, tm1), thread)
        end
    | TmRec (cstr, tm1) =>
        let
          val (tm1, thread) = transform (tm1, thread)
        in
          (TmRec (cstr, tm1), thread)
        end
    | TmPair (tm1, tm2) =>
        let
          val (tm1, thread) = transform (tm1, thread)
          val (tm2, thread) = transform (tm2, thread)
        in
          (TmPair (tm1, tm2), thread)
        end
    | TmFst tm1 =>
        let
          val (tm1, thread) = transform (tm1, thread)
        in
          (TmFst tm1, thread)
        end
    | TmSnd tm1 =>
        let
          val (tm1, thread) = transform (tm1, thread)
        in
          (TmSnd tm1, thread)
        end
    | TmInLeft tm1 =>
        let
          val (tm1, thread) = transform (tm1, thread)
        in
          (TmInLeft tm1, thread)
        end
    | TmInRight tm1 =>
        let
          val (tm1, thread) = transform (tm1, thread)
        in
          (TmInRight tm1, thread)
        end
    | TmCase (tm1, tm2, tm3) =>
        let
          val (tm1, thread) = transform (tm1, thread)
          val (tm2, thread) = transform (tm2, thread)
          val (tm3, thread) = transform (tm3, thread)
        in
          (TmCase (tm1, tm2, tm3), thread)
        end
    | TmFold tm1 =>
        let
          val (tm1, thread) = transform (tm1, thread)
        in
          (TmFold tm1, thread)
        end
    | TmUnfold tm1 =>
        let
          val (tm1, thread) = transform (tm1, thread)
        in
          (TmUnfold tm1, thread)
        end
    | TmPack (cstr, tm1) =>
        let
          val (tm1, thread) = transform (tm1, thread)
        in
          (TmPack (cstr, tm1), thread)
        end
    | TmUnpack (tm1, tm2) =>
        let
          val (tm1, thread) = transform (tm1, thread)
          val (tm2, thread) = transform (tm2, thread)
        in
          (TmUnpack (tm1, tm2), thread)
        end
    | TmCstrAbs (kd, tm1) =>
        let
          val (tm1, thread) = transform (tm1, thread)
        in
          (TmCstrAbs (kd, tm1), thread)
        end
    | TmCstrApp (tm1, cstr) =>
        let
          val (tm1, thread) = transform (tm1, thread)
        in
          (TmCstrApp (tm1, cstr), thread)
        end
    | TmBinOp (bop, tm1, tm2) =>
        let
          val (tm1, thread) = transform (tm1, thread)
          val (tm2, thread) = transform (tm2, thread)
        in
          (TmBinOp (bop, tm1, tm2), thread)
        end
    | TmArrayNew (tm1, tm2) =>
        let
          val (tm1, thread) = transform (tm1, thread)
          val (tm2, thread) = transform (tm2, thread)
        in
          (TmArrayNew (tm1, tm2), thread)
        end
    | TmArrayGet (tm1, tm2) =>
        let
          val (tm1, thread) = transform (tm1, thread)
          val (tm2, thread) = transform (tm2, thread)
        in
          (TmArrayGet (tm1, tm2), thread)
        end
    | TmArrayPut (tm1, tm2, tm3) =>
        let
          val (tm1, thread) = transform (tm1, thread)
          val (tm2, thread) = transform (tm2, thread)
          val (tm3, thread) = transform (tm3, thread)
        in
          (TmArrayPut (tm1, tm2, tm3), thread)
        end

  and transform (tm : term, thread : Arg.thread) =
    case Arg.transformer transform (tm, thread) of
      SOME res => res
    | NONE => default_transform (tm, thread)

  fun apply_with_thread (tm : term, thread : Arg.thread) =
    let
      val res = transform (tm, thread)
    in
      Arg.at_transform_end res
    end

  fun apply (thread_base : Arg.thread) (tm : term) = #1 (apply_with_thread (tm, thread_base))
end
