functor TermTransformPass(Arg:
sig
  type down
  type up

  val transformer_constr : ((MicroTiML.constr * down) -> (MicroTiML.constr * up)) * ((MicroTiML.kind * down) -> (MicroTiML.kind * up)) -> (MicroTiML.constr * down) -> (MicroTiML.constr * up) option
  val transformer_kind : ((MicroTiML.kind * down) -> (MicroTiML.kind * up)) * ((MicroTiML.prop * down) -> (MicroTiML.prop * up)) -> (MicroTiML.kind * down) -> (MicroTiML.kind * up) option
  val transformer_prop : ((MicroTiML.constr * down) -> (MicroTiML.constr * up)) * ((MicroTiML.kind * down) -> (MicroTiML.kind * up)) * ((MicroTiML.prop * down) -> (MicroTiML.prop * up)) -> (MicroTiML.prop * down) -> (MicroTiML.prop * up) option
  val transformer_term : ((MicroTiML.constr * down) -> (MicroTiML.constr * up)) * ((MicroTiML.kind * down) -> (MicroTiML.kind * up)) * ((MicroTiML.term * down) -> (MicroTiML.term * up)) -> (MicroTiML.term * down) -> (MicroTiML.term * up) option

  val upward_base : up
  val combiner : (up * up) -> up
end) =
struct
  open MicroTiML

  fun combine (ups : Arg.up list) = List.foldl Arg.combiner Arg.upward_base ups

  fun default_transform_constr (cstr : constr, down : Arg.down) =
    case cstr of
      CstrVar a => (CstrVar a, Arg.upward_base)
    | CstrNat n => (CstrNat n, Arg.upward_base)
    | CstrTime r => (CstrTime r, Arg.upward_base)
    | CstrUnit => (CstrUnit, Arg.upward_base)
    | CstrTrue => (CstrTrue, Arg.upward_base)
    | CstrFalse => (CstrFalse, Arg.upward_base)
    | CstrUnOp (uop, cstr1) =>
        let
          val (cstr1, up1) = transform_constr (cstr1, down)
        in
          (CstrUnOp (uop, cstr1), combine [up1])
        end
    | CstrBinOp (bop, cstr1, cstr2) =>
        let
          val (cstr1, up1) = transform_constr (cstr1, down)
          val (cstr2, up2) = transform_constr (cstr2, down)
        in
          (CstrBinOp (bop, cstr1, cstr2), combine [up1, up2])
        end
    | CstrIte (cstr1, cstr2, cstr3) =>
        let
          val (cstr1, up1) = transform_constr (cstr1, down)
          val (cstr2, up2) = transform_constr (cstr2, down)
          val (cstr3, up3) = transform_constr (cstr3, down)
        in
          (CstrIte (cstr1, cstr2, cstr3), combine [up1, up2, up3])
        end
    | CstrTimeAbs cstr1 =>
        let
          val (cstr1, up1) = transform_constr (cstr1, down)
        in
          (CstrTimeAbs cstr1, combine [up1])
        end
    | CstrProd (cstr1, cstr2) =>
        let
          val (cstr1, up1) = transform_constr (cstr1, down)
          val (cstr2, up2) = transform_constr (cstr2, down)
        in
          (CstrProd (cstr1, cstr2), combine [up1, up2])
        end
    | CstrSum (cstr1, cstr2) =>
        let
          val (cstr1, up1) = transform_constr (cstr1, down)
          val (cstr2, up2) = transform_constr (cstr2, down)
        in
          (CstrSum (cstr1, cstr2), combine [up1, up2])
        end
    | CstrArrow (cstr1, cstr2, cstr3) =>
        let
          val (cstr1, up1) = transform_constr (cstr1, down)
          val (cstr2, up2) = transform_constr (cstr2, down)
          val (cstr3, up3) = transform_constr (cstr3, down)
        in
          (CstrArrow (cstr1, cstr2, cstr3), combine [up1, up2, up3])
        end
    | CstrApp (cstr1, cstr2) =>
        let
          val (cstr1, up1) = transform_constr (cstr1, down)
          val (cstr2, up2) = transform_constr (cstr2, down)
        in
          (CstrApp (cstr1, cstr2), combine [up1, up2])
        end
    | CstrAbs (kd1, cstr2) =>
        let
          val (kd1, up1) = transform_kind (kd1, down)
          val (cstr2, up2) = transform_constr (cstr2, down)
        in
          (CstrAbs (kd1, cstr2), combine [up1, up2])
        end
    | CstrForall (kd1, cstr2) =>
        let
          val (kd1, up1) = transform_kind (kd1, down)
          val (cstr2, up2) = transform_constr (cstr2, down)
        in
          (CstrForall (kd1, cstr2), combine [up1, up2])
        end
    | CstrExists (kd1, cstr2) =>
        let
          val (kd1, up1) = transform_kind (kd1, down)
          val (cstr2, up2) = transform_constr (cstr2, down)
        in
          (CstrExists (kd1, cstr2), combine [up1, up2])
        end
    | CstrRec (kd1, cstr2) =>
        let
          val (kd1, up1) = transform_kind (kd1, down)
          val (cstr2, up2) = transform_constr (cstr2, down)
        in
          (CstrRec (kd1, cstr2), combine [up1, up2])
        end
    | CstrTypeUnit => (CstrTypeUnit, Arg.upward_base)
    | CstrTypeInt => (CstrTypeInt, Arg.upward_base)
    | CstrTypeNat cstr1 =>
        let
          val (cstr1, up1) = transform_constr (cstr1, down)
        in
          (CstrTypeNat cstr1, combine [up1])
        end
    | CstrTypeArray (cstr1, cstr2) =>
        let
          val (cstr1, up1) = transform_constr (cstr1, down)
          val (cstr2, up2) = transform_constr (cstr2, down)
        in
          (CstrTypeArray (cstr1, cstr2), combine [up1, up2])
        end

  and transform_constr (cstr : constr, down : Arg.down) =
    case Arg.transformer_constr (transform_constr, transform_kind) (cstr, down) of
      SOME res => res
    | NONE => default_transform_constr (cstr, down)

  and default_transform_kind (kd : kind, down : Arg.down) =
    case kd of
      KdNat => (KdNat, Arg.upward_base)
    | KdUnit => (KdUnit, Arg.upward_base)
    | KdBool => (KdBool, Arg.upward_base)
    | KdTimeFun n => (KdTimeFun n, Arg.upward_base)
    | KdSubset (kd1, pr2) =>
        let
          val (kd1, up1) = transform_kind (kd1, down)
          val (pr2, up2) = transform_prop (pr2, down)
        in
          (KdSubset (kd1, pr2), combine [up1, up2])
        end
    | KdProper => (KdProper, Arg.upward_base)
    | KdArrow (kd1, kd2) =>
        let
          val (kd1, up1) = transform_kind (kd1, down)
          val (kd2, up2) = transform_kind (kd2, down)
        in
          (KdArrow (kd1, kd2), combine [up1, up2])
        end

  and transform_kind (kd : kind, down : Arg.down) =
    case Arg.transformer_kind (transform_kind, transform_prop) (kd, down) of
      SOME res => res
    | NONE => default_transform_kind (kd, down)

  and default_transform_prop (pr : prop, down : Arg.down) =
    case pr of
      PrTop => (PrTop, Arg.upward_base)
    | PrBot => (PrBot, Arg.upward_base)
    | PrBinConn (conn, pr1, pr2) =>
        let
          val (pr1, up1) = transform_prop (pr1, down)
          val (pr2, up2) = transform_prop (pr2, down)
        in
          (PrBinConn (conn, pr1, pr2), combine [up1, up2])
        end
    | PrNot pr1 =>
        let
          val (pr1, up1) = transform_prop (pr1, down)
        in
          (PrNot pr1, combine [up1])
        end
    | PrBinRel (rel, cstr1, cstr2) =>
        let
          val (cstr1, up1) = transform_constr (cstr1, down)
          val (cstr2, up2) = transform_constr (cstr2, down)
        in
          (PrBinRel (rel, cstr1, cstr2), combine [up1, up2])
        end
    | PrForall (kd1, pr2) =>
        let
          val (kd1, up1) = transform_kind (kd1, down)
          val (pr2, up2) = transform_prop (pr2, down)
        in
          (PrForall (kd1, pr2), combine [up1, up2])
        end
    | PrExists (kd1, pr2) =>
        let
          val (kd1, up1) = transform_kind (kd1, down)
          val (pr2, up2) = transform_prop (pr2, down)
        in
          (PrExists (kd1, pr2), combine [up1, up2])
        end

  and transform_prop (pr : prop, down : Arg.down) =
    case Arg.transformer_prop (transform_constr, transform_kind, transform_prop) (pr, down) of
      SOME res => res
    | NONE => default_transform_prop (pr, down)

  fun default_transform_term (tm : term, down : Arg.down) =
    case tm of
      TmVar x => (TmVar x, Arg.upward_base)
    | TmInt i => (TmInt i, Arg.upward_base)
    | TmNat n => (TmNat n, Arg.upward_base)
    | TmUnit => (TmUnit, Arg.upward_base)
    | TmApp (tm1, tm2) =>
        let
          val (tm1, up1) = transform_term (tm1, down)
          val (tm2, up2) = transform_term (tm2, down)
        in
          (TmApp (tm1, tm2), combine [up1, up2])
        end
    | TmAbs (cstr1, tm2) =>
        let
          val (cstr1, up1) = transform_constr (cstr1, down)
          val (tm2, up2) = transform_term (tm2, down)
        in
          (TmAbs (cstr1, tm2), combine [up1, up2])
        end
    | TmRec (cstr1, tm2) =>
        let
          val (cstr1, up1) = transform_constr (cstr1, down)
          val (tm2, up2) = transform_term (tm2, down)
        in
          (TmRec (cstr1, tm2), combine [up1, up2])
        end
    | TmPair (tm1, tm2) =>
        let
          val (tm1, up1) = transform_term (tm1, down)
          val (tm2, up2) = transform_term (tm2, down)
        in
          (TmPair (tm1, tm2), combine [up1, up2])
        end
    | TmFst tm1 =>
        let
          val (tm1, up1) = transform_term (tm1, down)
        in
          (TmFst tm1, combine [up1])
        end
    | TmSnd tm1 =>
        let
          val (tm1, up1) = transform_term (tm1, down)
        in
          (TmSnd tm1, combine [up1])
        end
    | TmInLeft tm1 =>
        let
          val (tm1, up1) = transform_term (tm1, down)
        in
          (TmInLeft tm1, combine [up1])
        end
    | TmInRight tm1 =>
        let
          val (tm1, up1) = transform_term (tm1, down)
        in
          (TmInRight tm1, combine [up1])
        end
    | TmCase (tm1, tm2, tm3) =>
        let
          val (tm1, up1) = transform_term (tm1, down)
          val (tm2, up2) = transform_term (tm2, down)
          val (tm3, up3) = transform_term (tm3, down)
        in
          (TmCase (tm1, tm2, tm3), combine [up1, up2, up3])
        end
    | TmFold tm1 =>
        let
          val (tm1, up1) = transform_term (tm1, down)
        in
          (TmFold tm1, combine [up1])
        end
    | TmUnfold tm1 =>
        let
          val (tm1, up1) = transform_term (tm1, down)
        in
          (TmUnfold tm1, combine [up1])
        end
    | TmPack (cstr1, tm2) =>
        let
          val (cstr1, up1) = transform_constr (cstr1, down)
          val (tm2, up2) = transform_term (tm2, down)
        in
          (TmPack (cstr1, tm2), combine [up1, up2])
        end
    | TmUnpack (tm1, tm2) =>
        let
          val (tm1, up1) = transform_term (tm1, down)
          val (tm2, up2) = transform_term (tm2, down)
        in
          (TmUnpack (tm1, tm2), combine [up1, up2])
        end
    | TmCstrAbs (kd1, tm2) =>
        let
          val (kd1, up1) = transform_kind (kd1, down)
          val (tm2, up2) = transform_term (tm2, down)
        in
          (TmCstrAbs (kd1, tm2), combine [up1, up2])
        end
    | TmCstrApp (tm1, cstr2) =>
        let
          val (tm1, up1) = transform_term (tm1, down)
          val (cstr2, up2) = transform_constr (cstr2, down)
        in
          (TmCstrApp (tm1, cstr2), combine [up1, up2])
        end
    | TmBinOp (bop, tm1, tm2) =>
        let
          val (tm1, up1) = transform_term (tm1, down)
          val (tm2, up2) = transform_term (tm2, down)
        in
          (TmBinOp (bop, tm1, tm2), combine [up1, up2])
        end
    | TmArrayNew (tm1, tm2) =>
        let
          val (tm1, up1) = transform_term (tm1, down)
          val (tm2, up2) = transform_term (tm2, down)
        in
          (TmArrayNew (tm1, tm2), combine [up1, up2])
        end
    | TmArrayGet (tm1, tm2) =>
        let
          val (tm1, up1) = transform_term (tm1, down)
          val (tm2, up2) = transform_term (tm2, down)
        in
          (TmArrayGet (tm1, tm2), combine [up1, up2])
        end
    | TmArrayPut (tm1, tm2, tm3) =>
        let
          val (tm1, up1) = transform_term (tm1, down)
          val (tm2, up2) = transform_term (tm2, down)
          val (tm3, up3) = transform_term (tm3, down)
        in
          (TmArrayPut (tm1, tm2, tm3), combine [up1, up2, up3])
        end
    | TmLet (tm1, tm2) =>
        let
          val (tm1, up1) = transform_term (tm1, down)
          val (tm2, up2) = transform_term (tm2, down)
        in
          (TmLet (tm1, tm2), combine [up1, up2])
        end
    | TmNever => (TmNever, Arg.upward_base)
    | TmFixAbs (kinds, cstr1, tm2) =>
        let
          val (kinds, ups) = ListPair.unzip (List.map (fn kd => transform_kind (kd, down)) kinds)
          val (cstr1, up1) = transform_constr (cstr1, down)
          val (tm2, up2) = transform_term (tm2, down)
        in
          (TmFixAbs (kinds, cstr1, tm2), combine (ups @ [up1, up2]))
        end

  and transform_term (tm : term, down : Arg.down) =
    case Arg.transformer_term (transform_constr, transform_kind, transform_term) (tm, down) of
      SOME res => res
    | NONE => default_transform_term (tm, down)
end

functor TermThreadedTransformPass(Arg:
sig
  type thread

  val transformer_constr : ((MicroTiML.constr * thread) -> (MicroTiML.constr * thread)) * ((MicroTiML.kind * thread) -> (MicroTiML.kind * thread)) -> (MicroTiML.constr * thread) -> (MicroTiML.constr * thread) option
  val transformer_kind : ((MicroTiML.kind * thread) -> (MicroTiML.kind * thread)) * ((MicroTiML.prop * thread) -> (MicroTiML.prop * thread)) -> (MicroTiML.kind * thread) -> (MicroTiML.kind * thread) option
  val transformer_prop : ((MicroTiML.constr * thread) -> (MicroTiML.constr * thread)) * ((MicroTiML.kind * thread) -> (MicroTiML.kind * thread)) * ((MicroTiML.prop * thread) -> (MicroTiML.prop * thread)) -> (MicroTiML.prop * thread) -> (MicroTiML.prop * thread) option
  val transformer_term : ((MicroTiML.constr * thread) -> (MicroTiML.constr * thread)) * ((MicroTiML.kind * thread) -> (MicroTiML.kind * thread)) * ((MicroTiML.term * thread) -> (MicroTiML.term * thread)) -> (MicroTiML.term * thread) -> (MicroTiML.term * thread) option
end) =
struct
  open MicroTiML

  fun default_transform_constr (cstr : constr, thread : Arg.thread) =
    case cstr of
      CstrVar a => (CstrVar a, thread)
    | CstrNat n => (CstrNat n, thread)
    | CstrTime r => (CstrTime r, thread)
    | CstrUnit => (CstrUnit, thread)
    | CstrTrue => (CstrTrue, thread)
    | CstrFalse => (CstrFalse, thread)
    | CstrUnOp (uop, cstr1) =>
        let
          val (cstr1, thread) = transform_constr (cstr1, thread)
        in
          (CstrUnOp (uop, cstr1), thread)
        end
    | CstrBinOp (bop, cstr1, cstr2) =>
        let
          val (cstr1, thread) = transform_constr (cstr1, thread)
          val (cstr2, thread) = transform_constr (cstr2, thread)
        in
          (CstrBinOp (bop, cstr1, cstr2), thread)
        end
    | CstrIte (cstr1, cstr2, cstr3) =>
        let
          val (cstr1, thread) = transform_constr (cstr1, thread)
          val (cstr2, thread) = transform_constr (cstr2, thread)
          val (cstr3, thread) = transform_constr (cstr3, thread)
        in
          (CstrIte (cstr1, cstr2, cstr3), thread)
        end
    | CstrTimeAbs cstr1 =>
        let
          val (cstr1, thread) = transform_constr (cstr1, thread)
        in
          (CstrTimeAbs cstr1, thread)
        end
    | CstrProd (cstr1, cstr2) =>
        let
          val (cstr1, thread) = transform_constr (cstr1, thread)
          val (cstr2, thread) = transform_constr (cstr2, thread)
        in
          (CstrProd (cstr1, cstr2), thread)
        end
    | CstrSum (cstr1, cstr2) =>
        let
          val (cstr1, thread) = transform_constr (cstr1, thread)
          val (cstr2, thread) = transform_constr (cstr2, thread)
        in
          (CstrSum (cstr1, cstr2), thread)
        end
    | CstrArrow (cstr1, cstr2, cstr3) =>
        let
          val (cstr1, thread) = transform_constr (cstr1, thread)
          val (cstr2, thread) = transform_constr (cstr2, thread)
          val (cstr3, thread) = transform_constr (cstr3, thread)
        in
          (CstrArrow (cstr1, cstr2, cstr3), thread)
        end
    | CstrApp (cstr1, cstr2) =>
        let
          val (cstr1, thread) = transform_constr (cstr1, thread)
          val (cstr2, thread) = transform_constr (cstr2, thread)
        in
          (CstrApp (cstr1, cstr2), thread)
        end
    | CstrAbs (kd1, cstr2) =>
        let
          val (kd1, thread) = transform_kind (kd1, thread)
          val (cstr2, thread) = transform_constr (cstr2, thread)
        in
          (CstrAbs (kd1, cstr2), thread)
        end
    | CstrForall (kd1, cstr2) =>
        let
          val (kd1, thread) = transform_kind (kd1, thread)
          val (cstr2, thread) = transform_constr (cstr2, thread)
        in
          (CstrForall (kd1, cstr2), thread)
        end
    | CstrExists (kd1, cstr2) =>
        let
          val (kd1, thread) = transform_kind (kd1, thread)
          val (cstr2, thread) = transform_constr (cstr2, thread)
        in
          (CstrExists (kd1, cstr2), thread)
        end
    | CstrRec (kd1, cstr2) =>
        let
          val (kd1, thread) = transform_kind (kd1, thread)
          val (cstr2, thread) = transform_constr (cstr2, thread)
        in
          (CstrRec (kd1, cstr2), thread)
        end
    | CstrTypeUnit => (CstrTypeUnit, thread)
    | CstrTypeInt => (CstrTypeInt, thread)
    | CstrTypeNat cstr1 =>
        let
          val (cstr1, thread) = transform_constr (cstr1, thread)
        in
          (CstrTypeNat cstr1, thread)
        end
    | CstrTypeArray (cstr1, cstr2) =>
        let
          val (cstr1, thread) = transform_constr (cstr1, thread)
          val (cstr2, thread) = transform_constr (cstr2, thread)
        in
          (CstrTypeArray (cstr1, cstr2), thread)
        end

  and transform_constr (cstr : constr, thread : Arg.thread) =
    case Arg.transformer_constr (transform_constr, transform_kind) (cstr, thread) of
      SOME res => res
    | NONE => default_transform_constr (cstr, thread)

  and default_transform_kind (kd : kind, thread : Arg.thread) =
    case kd of
      KdNat => (KdNat, thread)
    | KdUnit => (KdUnit, thread)
    | KdBool => (KdBool, thread)
    | KdTimeFun n => (KdTimeFun n, thread)
    | KdSubset (kd1, pr2) =>
        let
          val (kd1, thread) = transform_kind (kd1, thread)
          val (pr2, thread) = transform_prop (pr2, thread)
        in
          (KdSubset (kd1, pr2), thread)
        end
    | KdProper => (KdProper, thread)
    | KdArrow (kd1, kd2) =>
        let
          val (kd1, thread) = transform_kind (kd1, thread)
          val (kd2, thread) = transform_kind (kd2, thread)
        in
          (KdArrow (kd1, kd2), thread)
        end

  and transform_kind (kd : kind, thread : Arg.thread) =
    case Arg.transformer_kind (transform_kind, transform_prop) (kd, thread) of
      SOME res => res
    | NONE => default_transform_kind (kd, thread)

  and default_transform_prop (pr : prop, thread : Arg.thread) =
    case pr of
      PrTop => (PrTop, thread)
    | PrBot => (PrBot, thread)
    | PrBinConn (conn, pr1, pr2) =>
        let
          val (pr1, thread) = transform_prop (pr1, thread)
          val (pr2, thread) = transform_prop (pr2, thread)
        in
          (PrBinConn (conn, pr1, pr2), thread)
        end
    | PrNot pr1 =>
        let
          val (pr1, thread) = transform_prop (pr1, thread)
        in
          (PrNot pr1, thread)
        end
    | PrBinRel (rel, cstr1, cstr2) =>
        let
          val (cstr1, thread) = transform_constr (cstr1, thread)
          val (cstr2, thread) = transform_constr (cstr2, thread)
        in
          (PrBinRel (rel, cstr1, cstr2), thread)
        end
    | PrForall (kd1, pr2) =>
        let
          val (kd1, thread) = transform_kind (kd1, thread)
          val (pr2, thread) = transform_prop (pr2, thread)
        in
          (PrForall (kd1, pr2), thread)
        end
    | PrExists (kd1, pr2) =>
        let
          val (kd1, thread) = transform_kind (kd1, thread)
          val (pr2, thread) = transform_prop (pr2, thread)
        in
          (PrExists (kd1, pr2), thread)
        end

  and transform_prop (pr : prop, thread : Arg.thread) =
    case Arg.transformer_prop (transform_constr, transform_kind, transform_prop) (pr, thread) of
      SOME res => res
    | NONE => default_transform_prop (pr, thread)

  fun default_transform_term (tm : term, thread : Arg.thread) =
    case tm of
      TmVar x => (TmVar x, thread)
    | TmInt i => (TmInt i, thread)
    | TmNat n => (TmNat n, thread)
    | TmUnit => (TmUnit, thread)
    | TmApp (tm1, tm2) =>
        let
          val (tm1, thread) = transform_term (tm1, thread)
          val (tm2, thread) = transform_term (tm2, thread)
        in
          (TmApp (tm1, tm2), thread)
        end
    | TmAbs (cstr1, tm2) =>
        let
          val (cstr1, thread) = transform_constr (cstr1, thread)
          val (tm2, thread) = transform_term (tm2, thread)
        in
          (TmAbs (cstr1, tm2), thread)
        end
    | TmRec (cstr1, tm2) =>
        let
          val (cstr1, thread) = transform_constr (cstr1, thread)
          val (tm2, thread) = transform_term (tm2, thread)
        in
          (TmRec (cstr1, tm2), thread)
        end
    | TmPair (tm1, tm2) =>
        let
          val (tm1, thread) = transform_term (tm1, thread)
          val (tm2, thread) = transform_term (tm2, thread)
        in
          (TmPair (tm1, tm2), thread)
        end
    | TmFst tm1 =>
        let
          val (tm1, thread) = transform_term (tm1, thread)
        in
          (TmFst tm1, thread)
        end
    | TmSnd tm1 =>
        let
          val (tm1, thread) = transform_term (tm1, thread)
        in
          (TmSnd tm1, thread)
        end
    | TmInLeft tm1 =>
        let
          val (tm1, thread) = transform_term (tm1, thread)
        in
          (TmInLeft tm1, thread)
        end
    | TmInRight tm1 =>
        let
          val (tm1, thread) = transform_term (tm1, thread)
        in
          (TmInRight tm1, thread)
        end
    | TmCase (tm1, tm2, tm3) =>
        let
          val (tm1, thread) = transform_term (tm1, thread)
          val (tm2, thread) = transform_term (tm2, thread)
          val (tm3, thread) = transform_term (tm3, thread)
        in
          (TmCase (tm1, tm2, tm3), thread)
        end
    | TmFold tm1 =>
        let
          val (tm1, thread) = transform_term (tm1, thread)
        in
          (TmFold tm1, thread)
        end
    | TmUnfold tm1 =>
        let
          val (tm1, thread) = transform_term (tm1, thread)
        in
          (TmUnfold tm1, thread)
        end
    | TmPack (cstr1, tm2) =>
        let
          val (cstr1, thread) = transform_constr (cstr1, thread)
          val (tm2, thread) = transform_term (tm2, thread)
        in
          (TmPack (cstr1, tm2), thread)
        end
    | TmUnpack (tm1, tm2) =>
        let
          val (tm1, thread) = transform_term (tm1, thread)
          val (tm2, thread) = transform_term (tm2, thread)
        in
          (TmUnpack (tm1, tm2), thread)
        end
    | TmCstrAbs (kd1, tm2) =>
        let
          val (kd1, thread) = transform_kind (kd1, thread)
          val (tm2, thread) = transform_term (tm2, thread)
        in
          (TmCstrAbs (kd1, tm2), thread)
        end
    | TmCstrApp (tm1, cstr2) =>
        let
          val (tm1, thread) = transform_term (tm1, thread)
          val (cstr2, thread) = transform_constr (cstr2, thread)
        in
          (TmCstrApp (tm1, cstr2), thread)
        end
    | TmBinOp (bop, tm1, tm2) =>
        let
          val (tm1, thread) = transform_term (tm1, thread)
          val (tm2, thread) = transform_term (tm2, thread)
        in
          (TmBinOp (bop, tm1, tm2), thread)
        end
    | TmArrayNew (tm1, tm2) =>
        let
          val (tm1, thread) = transform_term (tm1, thread)
          val (tm2, thread) = transform_term (tm2, thread)
        in
          (TmArrayNew (tm1, tm2), thread)
        end
    | TmArrayGet (tm1, tm2) =>
        let
          val (tm1, thread) = transform_term (tm1, thread)
          val (tm2, thread) = transform_term (tm2, thread)
        in
          (TmArrayGet (tm1, tm2), thread)
        end
    | TmArrayPut (tm1, tm2, tm3) =>
        let
          val (tm1, thread) = transform_term (tm1, thread)
          val (tm2, thread) = transform_term (tm2, thread)
          val (tm3, thread) = transform_term (tm3, thread)
        in
          (TmArrayPut (tm1, tm2, tm3), thread)
        end
    | TmLet (tm1, tm2) =>
        let
          val (tm1, thread) = transform_term (tm1, thread)
          val (tm2, thread) = transform_term (tm2, thread)
        in
          (TmLet (tm1, tm2), thread)
        end
    | TmNever => (TmNever, thread)
    | TmFixAbs (kinds, cstr1, tm2) =>
        let
          val (kinds, thread) = List.foldl (fn (kd, (kinds, thread)) => let val (kd, thread) = transform_kind (kd, thread) in (kd :: kinds, thread) end) ([], thread) kinds
          val kinds = List.rev kinds
          val (cstr1, thread) = transform_constr (cstr1, thread)
          val (tm2, thread) = transform_term (tm2, thread)
        in
          (TmFixAbs (kinds, cstr1, tm2), thread)
        end

  and transform_term (tm : term, thread : Arg.thread) =
    case Arg.transformer_term (transform_constr, transform_kind, transform_term) (tm, thread) of
      SOME res => res
    | NONE => default_transform_term (tm, thread)
end
