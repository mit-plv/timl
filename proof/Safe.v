Require Import Frap.

Set Implicit Arguments.

Require Rdefinitions.

Module Time.
  Module R := Rdefinitions.
  Definition real := R.R.
  (* Require RIneq. *)
  (* Definition nnreal := RIneq.nonnegreal. *)
  Definition time := real.
  Definition Time0 := R.R0.
  Definition Time1 := R.R1.
  Definition TimeAdd := R.Rplus.
  Definition TimeMinus := R.Rminus.
  Definition TimeLe := R.Rle.
  Delimit Scope time_scope with time.
  Notation "0" := Time0 : time_scope.
  Notation "1" := Time1 : time_scope.
  Infix "+" := TimeAdd : time_scope.
  Infix "-" := TimeMinus : time_scope.
  Infix "<=" := TimeLe : time_scope.

  Module OpenScope.
    Open Scope time_scope.
  End OpenScope.

  Module CloseScope.
    Close Scope time_scope.
  End CloseScope.

End Time.

Import Time.

Inductive cstr_const :=
| CCIdxTT
| CCIdxNat (n : nat)
| CCTime (r : time)
| CCTypeUnit
| CCTypeInt
.

Inductive cstr_un_op :=
.

Inductive cstr_bin_op :=
| CBTimeAdd
| CBTimeMinus
| CBTimeMax
| CBTypeProd
| CBTypeSum
.

Inductive quan :=
| QuanForall
| QuanExists
.

Definition var := nat.

Inductive cstr :=
| CVar (x : var)
| CConst (cn : cstr_const)
| CUnOp (opr : cstr_un_op) (c : cstr)
| CBinOp (opr : cstr_bin_op) (c1 c2 : cstr)
| CIte (i1 i2 i3 : cstr)
| CTimeAbs (i : cstr)
| CArrow (t1 i t2 : cstr)
| CAbs (t : cstr)
| CApp (t c : cstr)
| CQuan (q : quan) (c : cstr)
| CRec (t : cstr)
| CRef (t : cstr)
.

Definition Tconst r := CConst (CCTime r).
Definition T0 := Tconst Time0.
Definition T1 := Tconst Time1.
Definition Tadd := CBinOp CBTimeAdd.
Definition Tminus := CBinOp CBTimeMinus.

Delimit Scope idx_scope with idx.
Infix "+" := Tadd : idx_scope.
(* Notation "0" := T0 : idx_scope. *)
(* Notation "1" := T1 : idx_scope. *)

Definition Tmax := CBinOp CBTimeMax.

Definition CForall := CQuan QuanForall.
Definition CExists := CQuan QuanExists.

Definition CTypeUnit := CConst CCTypeUnit.

Definition CProd := CBinOp CBTypeProd.
Definition CSum := CBinOp CBTypeSum.

Inductive prop_bin_conn :=
.

Inductive prop_bin_pred :=
| PBLe
.

Inductive prop :=
| PTrue
| PFalse
| PBinConn (opr : prop_bin_conn) (p1 p2 : prop)
| PNot (p : prop)
| PBinPred (opr : prop_bin_pred) (i1 i2 : cstr)
| PEq (i1 i2 : cstr)
| PQuan (q : quan) (p : prop)
.

Definition PLe := PBinPred PBLe.
Infix "<=" := PLe : idx_scope.

Inductive base_sort :=
| BSNat
| BSUnit
| BSBool
| BSTimeFun (arity : nat)
.

Inductive kind :=
| KType
| KArrow (k1 k2 : kind)
| KBaseSort (b : base_sort)
| KSubset (k : kind) (p : prop)
.

Require BinIntDef.
Definition int := BinIntDef.Z.t.

Inductive expr_const :=
| ECTT
| ECInt (i : int)
.

Definition CInt := CConst CCTypeInt.

Definition const_type cn :=
  match cn with
  | ECTT => CTypeUnit
  | ECInt _ => CInt
  end
.

Inductive prim_expr_bin_op :=
| PEBIntAdd
.

Inductive projector :=
| ProjFst
| ProjSnd
.

Inductive sum_cstr :=
| SCInl
| SCInr
.

Definition loc := nat.

Inductive expr_un_op :=
| EUProj (p : projector)
| EUSumI (c : sum_cstr)
| EUAppC (c : cstr)
| EUPack (c : cstr)
| EUFold
| EUUnfold
| EUNew 
| EURead 
.

Inductive expr_bin_op :=
| EBPrim (opr : prim_expr_bin_op)
| EBApp
| EBPair
| EBWrite
.

Inductive expr :=
| EVar (x : var)
| EConst (cn : expr_const)
| ELoc (l : loc)
| EUnOp (opr : expr_un_op) (e : expr)
| EBinOp (opr : expr_bin_op) (e1 e2 : expr)
| ECase (e e1 e2 : expr)
| EAbs (e : expr)
| ERec (e : expr)
| EAbsC (e : expr)
| EUnpack (e1 e2 : expr)
(* | EAsc (e : expr) (t : cstr) *)
(* | EAstTime (e : expr) (i : cstr) *)
.


Definition EProj p e := EUnOp (EUProj p) e.
Definition ESumI c e := EUnOp (EUSumI c) e.
Definition EAppC e c := EUnOp (EUAppC c) e.
Definition EPack c e := EUnOp (EUPack c) e.
Definition EFold e := EUnOp EUFold e.
Definition EUnfold e := EUnOp EUUnfold e.
Definition ENew e := EUnOp EUNew e.
Definition ERead e := EUnOp EURead e.

Definition EApp := EBinOp EBApp.
Definition EPair := EBinOp EBPair.
Definition EWrite := EBinOp EBWrite.

Inductive value : expr -> Prop :=
| VVar x :
    value (EVar x)
| VConst cn :
    value (EConst cn)
| VPair v1 v2 :
    value v1 ->
    value v2 ->
    value (EPair v1 v2)
| VSumI c v :
    value v ->
    value (ESumI c v)
| VAbs e :
    value (EAbs e)
| VAbsC e :
    value (EAbsC e)
| VPack c v :
    value (EPack c v)
| VFold v :
    value (EFold v)
| VLoc l :
    value (ELoc l)
.

Inductive ectx :=
| ECHole
| ECUnOp (opr : expr_un_op) (E : ectx)
| ECBinOp1 (opr : expr_bin_op) (E : ectx) (e : expr)
| ECBinOp2 (opr : expr_bin_op) (v : expr) (E : ectx)
| ECCase (E : ectx) (e1 e2 : expr)
| ECUnpack (E : ectx) (e : expr)
.

Inductive plug : ectx -> expr -> expr -> Prop :=
| PlugHole e :
    plug ECHole e e
| PlugUnOp E e e' opr :
    plug E e e' ->
    plug (ECUnOp opr E) e (EUnOp opr e')
| PlugBinOp1 E e e' opr e2 :
    plug E e e' ->
    plug (ECBinOp1 opr E e2) e (EBinOp opr e' e2)
| PlugBinOp2 E e e' opr v :
    plug E e e' ->
    value v ->
    plug (ECBinOp2 opr v E) e (EBinOp opr v e')
| PlugCase E e e' e1 e2 :
    plug E e e' ->
    plug (ECCase E e1 e2) e (ECase e' e1 e2)
| PlugUnpack E e e' e2 :
    plug E e e' ->
    plug (ECUnpack E e2) e (EUnpack e' e2)
.

Definition EFst := EProj ProjFst.
Definition ESnd := EProj ProjSnd.
Definition EInl := ESumI SCInl.
Definition EInr := ESumI SCInr.

Definition ETT := EConst ECTT.

Definition kctx := list kind.
Definition hctx := fmap loc cstr.
Definition tctx := list cstr.
Definition ctx := (kctx * hctx * tctx)%type.

Definition shift_c_c (x : var) (n : nat) (b : cstr) : cstr.
  Admitted.
Definition shift01_c_c := shift_c_c 0 1.
           
Definition forget_c_c (x : var) (n : nat) (b : cstr) : option cstr.
  Admitted.
Definition forget01_c_c := forget_c_c 0 1.

Definition subst_c_c (x : var) (v : cstr) (b : cstr) : cstr.
Admitted.
Definition subst0_c_c := subst_c_c 0.

Inductive wfkind : kctx -> kind -> Prop :=
.

Inductive kinding : kctx -> cstr -> kind -> Prop :=
.

Inductive tyeq : kctx -> cstr -> cstr -> Prop :=
.

Definition interpP : kctx -> prop -> Prop.
Admitted.

Definition fmap_map {K A B} (f : A -> B) (m : fmap K A) : fmap K B.
Admitted.

Definition add_kinding_ctx k (C : ctx) :=
  match C with
    (L, H, G) => (k :: L, fmap_map shift01_c_c H, map shift01_c_c G)
  end
.

Definition add_typing_ctx t (C : ctx) :=
  match C with
    (L, H, G) => (L, H, t :: G)
  end
.

Definition get_kctx (C : ctx) : kctx := fst (fst C).
Definition get_hctx (C : ctx) : hctx := snd (fst C).
Definition get_tctx (C : ctx) : tctx := snd C.


Fixpoint CApps t cs :=
  match cs with
  | nil => t
  | c :: cs => CApps (CApp t c) cs
  end
.

Fixpoint AbsCs_Abs n e :=
  match n with
  | 0 => e
  | S n => EAbsC (AbsCs_Abs n e)
  end
.

Definition proj {A} (p : A * A) pr :=
  match pr with
  | ProjFst => fst p
  | ProjSnd => snd p
  end
.

Definition choose {A} (p : A * A) sc :=
  match sc with
  | SCInl => fst p
  | SCInr => snd p
  end
.

Local Open Scope idx_scope.

Inductive typing : ctx -> expr -> cstr -> cstr -> Prop :=
| TyVar L G x t :
    nth_error G x = Some t ->
    typing (L, G) (EVar x) t T0
| TyApp C e1 e2 t i1 i2 T1 i t2 :
    typing C e1 (CArrow t2 i t) i1 ->
    typing C e2 t2 i2 ->
    typing C (EApp e1 e2) t (i1 + i2 + T1 + i)
| TyAbs C e t1 i t :
    kinding (get_kctx C) t1 KType ->
    typing (add_typing_ctx t1 C) e t i ->
    typing C (EAbs e) (CArrow t1 i t) T0
| TyAppC C e c t i k :
    typing C e (CForall t) i ->
    kinding (get_kctx C) (CForall t) (KArrow k KType) ->
    kinding (get_kctx C) c k -> 
    typing C (EAppC e c) (subst0_c_c c t) i
| TyAbsC C e t k :
    value e ->
    wfkind (get_kctx C) k ->
    typing (add_kinding_ctx k C) e t T0 ->
    typing C (EAbsC e) (CAbs t) T0
| TyRec C e t n e1 :
    e = AbsCs_Abs n e1 ->
    kinding (get_kctx C) t KType ->
    typing (add_typing_ctx t C) e t T0 ->
    typing C (ERec e) t T0
| TyFold C e t i t1 cs t2 :
    t = CApps t1 cs ->
    t1 = CRec t2 ->
    kinding (get_kctx C) t KType ->
    typing C e (CApps (subst0_c_c t1 t2) cs) i ->
    typing C (EFold e) t i
| TyUnfold C e t t1 cs i :
    t = CRec t1 ->
    typing C e (CApps t cs) i ->
    typing C (EUnfold e) (CApps (subst0_c_c t t1) cs) i
| TySub C e t2 i2 t1 i1 :
    typing C e t1 i1 ->
    tyeq (get_kctx C) t1 t2 ->
    interpP (get_kctx C) (i1 <= i2) ->
    typing C e t2 i2 
(* | TyAsc L G e t i : *)
(*     kinding L t KType -> *)
(*     typing (L, G) e t i -> *)
(*     typing (L, G) (EAsc e t) t i *)
| TyPack C c e t i t1 k :
    t = CExists t1 ->
    kinding (get_kctx C) t1 (KArrow k KType) ->
    kinding (get_kctx C) c k ->
    typing C e (subst0_c_c c t1) i ->
    typing C (EPack c e) t i
| TyUnpack C e1 e2 t2' i1 i2' t k t2 i2 :
    typing C e1 (CExists t) i1 ->
    kinding (get_kctx C) t (KArrow k KType) ->
    typing (add_typing_ctx t (add_kinding_ctx k C)) e2 t2 i2 ->
    forget01_c_c t2 = Some t2' ->
    forget01_c_c i2 = Some i2' ->
    typing C (EUnpack e1 e2) t2' (i1 + i2')
| TyConst C cn :
    typing C (EConst cn) (const_type cn) T0
| TyPair C e1 e2 t1 t2 i1 i2 :
    typing C e1 t1 i1 ->
    typing C e2 t2 i2 ->
    typing C (EPair e1 e2) (CProd t1 t2) (i1 + i2)
| TyProj C pr e t1 t2 i :
    typing C e (CProd t1 t2) i ->
    typing C (EProj pr e) (proj (t1, t2) pr) i
| TySumI C sc e t t' i :
    typing C e t i ->
    kinding (get_kctx C) t' KType ->
    typing C (ESumI sc e) (choose (CSum t t', CSum t' t) sc) i
| TyCase C e e1 e2 t i i1 i2 t1 t2 :
    typing C e (CSum t1 t2) i ->
    typing (add_typing_ctx t1 C) e1 t i1 ->
    typing (add_typing_ctx t2 C) e2 t i2 ->
    typing C (ECase e e1 e2) t (i + Tmax i1 i2)
| TyNew C e t i :
    typing C e t i ->
    typing C (ENew e) (CRef t) i
| TyRead C e t i :
    typing C e (CRef t) i ->
    typing C (ERead e) t i
| TyWrite C e1 e2 i1 i2 t :
    typing C e1 (CRef t) i1 ->
    typing C e2 t i2 ->
    typing C (EWrite e1 e2) CTypeUnit (i1 + i2)
| TyLoc C l t :
    get_hctx C $? l = Some t ->
    typing C (ELoc l) t T0
.

Local Close Scope idx_scope.

Definition heap := fmap loc expr.
  
Definition subst_e_e (x : var) (v : expr) (b : expr) : expr.
Admitted.
Definition subst0_e_e := subst_e_e 0.

Definition subst_c_e (x : var) (v : cstr) (b : expr) : expr.
Admitted.
Definition subst0_c_e := subst_c_e 0.

Definition fuel := time.

Definition config := (heap * expr * fuel)%type.

(* Require Import Reals. *)

(* Local Open Scope R_scope. *)

(* Local Open Scope time_scope. *)

Import Time.OpenScope.

Inductive astep : config -> config -> Prop :=
| AUnfoldFold h v t :
    value v ->
    astep (h, EUnfold (EFold v), t) (h, v, t)
| ARec h e t :
    astep (h, ERec e, t) (h, subst0_e_e (ERec e) e, t)
| AUnpackPack h c v e t :
    astep (h, EUnpack (EPack c v) e, t) (h, subst0_e_e v (subst0_c_e c e), t)
| ARead h l t v :
    h $? l = Some v ->
    astep (h, ERead (ELoc l), t) (h, v, t)
| AWrite h l v t v' :
    value v ->
    h $? l = Some v' ->
    astep (h, EWrite (ELoc l) v, t) (h $+ (l, v), ETT, t)
| ANew h v t l :
    value v ->
    h $? l = None ->
    astep (h, ENew v, t) (h $+ (l, v), ELoc l, t)
| ABeta h e v t :
    value v ->
    astep (h, EApp (EAbs e) v, 1 + t) (h, subst0_e_e v e, t)
| ABetaC h e c t :
    astep (h, EAppC (EAbsC e) c, t) (h, subst0_c_e c e, t)
| AProj h pr v1 v2 t :
    value v1 ->
    value v2 ->
    astep (h, EProj pr (EPair v1 v2), t) (h, proj (v1, v2) pr, t)
| AMatch h sc v e1 e2 t :
    astep (h, ECase (ESumI sc v) e1 e2, t) (h, subst0_e_e v (choose (e1, e2) sc), t)
.

Inductive step : config -> config -> Prop :=
| Step h e1 t h' e1' t' e e' E :
    astep (h, e, t) (h', e', t') ->
    plug E e e1 ->
    plug E e' e1' ->
    step (h, e1, t) (h', e1', t')
.

Definition empty_ctx : ctx := ([], $0, []).
Notation "${}" := empty_ctx.

Definition htyping (h : heap) (H : hctx) :=
  forall l t,
    H $? l = Some t ->
    exists v,
      h $? l = Some v /\
      value v /\
      typing ${} v t T0.

Definition interpTime : cstr -> time.
Admitted.

Definition ctyping H (s : config) t i :=
  let '(h, e, f) := s in
  typing ([], H, []) e t i /\
  htyping h H /\
  interpTime i <= f
.

Definition get_expr (s : config) : expr := snd (fst s).
Definition get_fuel (s : config) : fuel := snd s.

Definition finished s := value (get_expr s).

Definition unstuck s :=
  finished s /\
  exists s', step s s'.

Definition safe s := forall s', step^* s s' -> unstuck s'.

Lemma progress H s t i :
  ctyping H s t i ->
  unstuck s.
Proof.
Admitted.

(* Local Close Scope time_scope. *)

Import Time.CloseScope.

Lemma preservation :
  forall s s',
    step s s' ->
  (* forall h e f h' e' f', *)
  (*   step (h, e, f) (h', e', f') -> *)
  (*   let s := (h, e, f) in *)
  (*   let s' := (h', e', f') in *)
    forall H t i,
      ctyping H s t i ->
      let df := (get_fuel s - get_fuel s')%time in
      (df <= interpTime i)%time ->
      exists H',
        ctyping H' s t (Tminus i (Tconst df)) /\
        (H $<= H').
Proof.
  invert 1.
  (* induct 1. *)
  (* induction 1. *)
  simplify.
  destruct H3 as (Hty & Hhty & Hle).
  (* destruct H3 as [Hty & Hhty & Hle]. *)
  (* generalize H3. *)
  (* intros (Hty & Hhty & Hle). *)
  (* intros (Hty, (Hhty, Hle)). *)
  (* intros (Hty, Hhty). *)
  Lemma generalize_plug : forall C e1 e1',
    plug C e1 e1' ->
    forall H t,
      hasty H $0 e1' t ->
      exists H1 Hctx t0,
        hasty H1 $0 e1 t0 /\
        split H H1 Hctx /\
        forall e2 e2' H1' H',
          hasty H1' $0 e2 t0 ->
          plug C e2 e2' ->
          split H' H1' Hctx ->
          hasty H' $0 e2' t.
    
  Lemma generalize_plug : forall H e1 C e1',
    plug C e1 e1'
    -> forall t, hasty H $0 e1' t
    -> exists t0, hasty H $0 e1 t0
                  /\ (forall e2 e2' H',
                         hasty H' $0 e2 t0
                         -> plug C e2 e2'
                         -> (forall l t, H $? l = Some t -> H' $? l = Some t)
                         -> hasty H' $0 e2' t).
    
    Lemma generalize_plug : forall e1 E e1',
      plug E e1 e1'
      -> forall e2 e2', plug C e2 e2'
                  -> (forall t, hasty $0 $0 e1 t -> hasty $0 $0 e2 t)
                  -> (forall t, hasty $0 $0 e1' t -> hasty $0 $0 e2' t).
    Proof.
      induct 1; t; eauto.
    Qed.

  Qed.





Lemma ttt : forall A (ls : list A) p, Forall p ls -> ls = List.nil.
  induct 1.
  
