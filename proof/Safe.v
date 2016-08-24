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

Inductive prop_bin_conn :=
.

Inductive prop_bin_pred :=
| PBTimeLe
.

Inductive base_sort :=
| BSNat
| BSUnit
| BSBool
| BSTimeFun (arity : nat)
.

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
| CQuan (q : quan) (k : kind) (c : cstr)
| CRec (t : cstr)
| CRef (t : cstr)

with prop :=
| PTrue
| PFalse
| PBinConn (opr : prop_bin_conn) (p1 p2 : prop)
| PNot (p : prop)
| PBinPred (opr : prop_bin_pred) (i1 i2 : cstr)
| PEq (i1 i2 : cstr)
| PQuan (q : quan) (p : prop)

with kind :=
| KType
| KArrow (k1 k2 : kind)
| KBaseSort (b : base_sort)
| KSubset (k : kind) (p : prop)
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

Definition Tle := PBinPred PBTimeLe.
Infix "<=" := Tle : idx_scope.

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

Inductive injector :=
| InjInl
| InjInr
.

Definition loc := nat.

Inductive expr_un_op :=
| EUProj (p : projector)
| EUInj (inj : injector)
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
Definition EInj c e := EUnOp (EUInj c) e.
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
| VInj c v :
    value v ->
    value (EInj c v)
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
Definition EInl := EInj InjInl.
Definition EInr := EInj InjInr.

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

Inductive kdeq : kctx -> kind -> kind -> Prop :=
.

Inductive kinding : kctx -> cstr -> kind -> Prop :=
| KdEq L c k k' :
    kinding L c k ->
    kdeq L k' k -> 
    kinding L c k'
.

Inductive tyeq : kctx -> kind -> cstr -> cstr -> Prop :=
.

Definition interpP : kctx -> prop -> Prop.
Admitted.

Definition fmap_map {K A B} (f : A -> B) (m : fmap K A) : fmap K B.
Admitted.

Definition add_kinding_ctx k (C : ctx) :=
  match C with
    (L, W, G) => (k :: L, fmap_map shift01_c_c W, map shift01_c_c G)
  end
.

Definition add_typing_ctx t (C : ctx) :=
  match C with
    (L, W, G) => (L, W, t :: G)
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

Fixpoint EAbsCs n e :=
  match n with
  | 0 => e
  | S n => EAbsC (EAbsCs n e)
  end
.

Definition proj {A} (p : A * A) pr :=
  match pr with
  | ProjFst => fst p
  | ProjSnd => snd p
  end
.

Definition choose {A} (p : A * A) inj :=
  match inj with
  | InjInl => fst p
  | InjInr => snd p
  end
.

Local Open Scope idx_scope.

Inductive typing : ctx -> expr -> cstr -> cstr -> Prop :=
| TyVar C x t :
    nth_error (get_tctx C) x = Some t ->
    typing C (EVar x) t T0
| TyApp C e1 e2 t i1 i2 T1 i t2 :
    typing C e1 (CArrow t2 i t) i1 ->
    typing C e2 t2 i2 ->
    typing C (EApp e1 e2) t (i1 + i2 + T1 + i)
| TyAbs C e t1 i t :
    kinding (get_kctx C) t1 KType ->
    typing (add_typing_ctx t1 C) e t i ->
    typing C (EAbs e) (CArrow t1 i t) T0
| TyAppC C e c t i k :
    typing C e (CForall k t) i ->
    kinding (get_kctx C) c k -> 
    typing C (EAppC e c) (subst0_c_c c t) i
| TyAbsC C e t k :
    value e ->
    wfkind (get_kctx C) k ->
    typing (add_kinding_ctx k C) e t T0 ->
    typing C (EAbsC e) (CForall k t) T0
| TyRec C e t n e1 :
    e = EAbsCs n (EAbs e1) ->
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
    tyeq (get_kctx C) KType t1 t2 ->
    interpP (get_kctx C) (i1 <= i2) ->
    typing C e t2 i2 
(* | TyAsc L G e t i : *)
(*     kinding L t KType -> *)
(*     typing (L, G) e t i -> *)
(*     typing (L, G) (EAsc e t) t i *)
| TyPack C c e i t1 k :
    kinding (get_kctx C) t1 (KArrow k KType) ->
    kinding (get_kctx C) c k ->
    typing C e (subst0_c_c c t1) i ->
    typing C (EPack c e) (CExists k t1) i
| TyUnpack C e1 e2 t2' i1 i2' t k t2 i2 :
    typing C e1 (CExists k t) i1 ->
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
| TyInj C inj e t t' i :
    typing C e t i ->
    kinding (get_kctx C) t' KType ->
    typing C (EInj inj e) (choose (CSum t t', CSum t' t) inj) i
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
    typing C (ELoc l) (CRef t) T0
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
| AMatch h inj v e1 e2 t :
    astep (h, ECase (EInj inj v) e1 e2, t) (h, subst0_e_e v (choose (e1, e2) inj), t)
.

Inductive step : config -> config -> Prop :=
| StepPlug h e1 t h' e1' t' e e' E :
    astep (h, e, t) (h', e', t') ->
    plug E e e1 ->
    plug E e' e1' ->
    step (h, e1, t) (h', e1', t')
.

Definition empty_ctx : ctx := ([], $0, []).
Notation "${}" := empty_ctx.

Definition htyping (h : heap) (W : hctx) :=
  forall l t,
    W $? l = Some t ->
    exists v,
      h $? l = Some v /\
      value v /\
      typing ([], W, []) v t T0.

Definition interpTime : cstr -> time.
Admitted.

Definition ctyping W (s : config) t i :=
  let '(h, e, f) := s in
  typing ([], W, []) e t i /\
  htyping h W /\
  interpTime i <= f
.

Definition get_expr (s : config) : expr := snd (fst s).
Definition get_fuel (s : config) : fuel := snd s.

Definition finished s := value (get_expr s).

Definition unstuck s :=
  finished s /\
  exists s', step s s'.

Definition safe s := forall s', step^* s s' -> unstuck s'.

(* Local Close Scope time_scope. *)

Import Time.CloseScope.

Lemma progress W s t i :
  ctyping W s t i ->
  unstuck s.
Proof.
Admitted.

Fixpoint KArrows args result :=
  match args with
  | [] => result
  | arg :: args => KArrow arg (KArrows args result)
  end.

Section Forall3.

  Variables A B C : Type.
  Variable R : A -> B -> C -> Prop.

  Inductive Forall3 : list A -> list B -> list C -> Prop :=
  | Forall3_nil : Forall3 [] [] []
  | Forall3_cons : forall x y z l l' l'',
      R x y z -> Forall3 l l' l'' -> Forall3 (x::l) (y::l') (z::l'').

  Hint Constructors Forall3.

End Forall3.

Lemma preservation0 s s' :
  astep s s' ->
  forall W t i,
    ctyping W s t i ->
    let df := (get_fuel s - get_fuel s')%time in
    (df <= interpTime i)%time /\
    exists W',
      ctyping W' s' t (Tminus i (Tconst df)) /\
      (W $<= W').
Proof.
  invert 1; simplify.
  {
    (* Case Unfold-Fold *)
    destruct H as (Hty & Hhty & Hle).
    rename t into f.
    rename t0 into t.
    Lemma invert_TyUnfold C e t2 i :
      typing C (EUnfold e) t2 i ->
      exists t t1 cs i',
      tyeq (get_kctx C) KType t2 (CApps (subst0_c_c t t1) cs) /\
      t = CRec t1 /\
      typing C e (CApps t cs) i' /\
      interpP (get_kctx C) (i' <= i)%idx.
    Proof.
    Admitted.
    eapply invert_TyUnfold in Hty.
    destruct Hty as (t1 & t2& cs& i'& Htyeq & ? & Hty & Hle2).
    subst.
    Arguments get_kctx _ / .
    simplify.
    Lemma invert_TyFold C e t' i :
      typing C (EFold e) t' i ->
      exists t t1 cs t2 i',
        tyeq (get_kctx C) KType t' t /\
        t = CApps t1 cs /\
        t1 = CRec t2 /\
        kinding (get_kctx C) t KType /\
        typing C e (CApps (subst0_c_c t1 t2) cs) i' /\
        interpP (get_kctx C) (i' <= i)%idx.
    Admitted.
    subst.
    eapply invert_TyFold in Hty.
    destruct Hty as (? & ? & cs' & t2' & i'' & Htyeq2 & ? & ? & Hkd & Hty & Hle3).
    subst.
    simplify.
    Lemma invert_tyeq_CApps k t cs t' cs' :
      tyeq [] k (CApps (CRec t) cs) (CApps (CRec t') cs') ->
      exists ks ,
      tyeq [] (KArrows ks k) t t' /\
      Forall3 (tyeq []) ks cs cs'.
    Admitted.
    eapply invert_tyeq_CApps in Htyeq2.
    destruct Htyeq2 as (ks & Htyeq2 & Htyeqcs).
    split.
    {
      (* (f - f <= interpTime i)%time *)
      admit.
    }
    exists W.
    repeat split.
    {
      eapply TySub.
      {
        eapply Hty.
      }
      {
        (* tyeq *)
        simplify.
        admit.
      }
      {
        simplify.
        (* le *)
        admit.
      }
    }
    {
      eapply Hhty.
    }
    {
      (* (interpTime (Tminus i (Tconst (f - f))) <= f)%time *)
      admit.
    }
    {
      eapply includes_intro.
      eauto.
    }
  }
  {
    (* Case Rec *)
    destruct H as (Hty & Hhty & Hle).
    rename t into f.
    rename t0 into t.
    Lemma invert_TyRec C e t i :
      typing C (ERec e) t i ->
      exists n e1 ,
        e = EAbsCs n (EAbs e1) /\
        kinding (get_kctx C) t KType /\
        typing (add_typing_ctx t C) e t T0.
    Admitted.
    generalize Hty; intro Hty0.
    eapply invert_TyRec in Hty.
    destruct Hty as (n & e1 & ? & Hkd & Hty).
    simplify.
    split.
    {
      (* (f - f <= interpTime i)%time *)
      admit.
    }
    exists W.
    repeat split.
    {
      Lemma ty_subst0_e_e L W t G e1 t1 i1 e2 i2 :
        typing (L, W, t :: G) e1 t1 i1 ->
        typing (L, W, G) e2 t i2 ->
        typing (L, W, G) (subst0_e_e e2 e1) t1 (i1 + i2)%idx.
      Admitted.
      eapply ty_subst0_e_e with (G := []) in Hty; eauto.
      eapply TySub.
      {
        eapply Hty.
      }
      {
        Lemma tyeq_refl L k t : tyeq L k t t.
        Admitted.
        eapply tyeq_refl.
      }
      {
        simplify.
        (* le *)
        admit.
      }
    }
    {
      eapply Hhty.
    }
    {
      (* (interpTime (Tminus i (Tconst (f - f))) <= f)%time *)
      admit.
    }
    {
      eapply includes_intro.
      eauto.
    }
  }
  {
    (* Case Unpack-Pack *)
    destruct H as (Hty & Hhty & Hle).
    rename t into f.
    rename t0 into t.
    Lemma invert_TyUnpack C e1 e2 t2'' i :
      typing C (EUnpack e1 e2) t2'' i ->
      exists t2' t i1 k t2 i2 i2' ,
      tyeq (get_kctx C) KType t2'' t2' /\
      typing C e1 (CExists k t) i1 /\
      typing (add_typing_ctx t (add_kinding_ctx k C)) e2 t2 i2 /\
      forget01_c_c t2 = Some t2' /\
      forget01_c_c i2 = Some i2' /\
      interpP (get_kctx C) (i1 + i2' <= i)%idx.
    Proof.
    Admitted.
    eapply invert_TyUnpack in Hty.
    destruct Hty as (t2' & t0 & i1 & k & t2 & i2 & i2' & Htyeq & Hty1 & Hty2 & Ht2 & Hi2 & Hle2).
    subst.
    simplify.
    Lemma invert_TyPack C c e t i :
      typing C (EPack c e) t i ->
      exists t1 k i' ,
        tyeq (get_kctx C) KType t (CExists k t1) /\
        kinding (get_kctx C) t1 (KArrow k KType) /\
        kinding (get_kctx C) c k /\
        typing C e (subst0_c_c c t1) i' /\
        interpP (get_kctx C) (i' <= i)%idx.
    Admitted.
    eapply invert_TyPack in Hty1.
    destruct Hty1 as (t1 & k' & i' & Htyeq2 & Hkd1 & Hkdc' & Htyv & Hle3).
    subst.
    simplify.
    Lemma invert_tyeq_CExists L k k1 t1 k2 t2 :
      tyeq L k (CExists k1 t1) (CExists k2 t2) ->
      tyeq L (KArrow k1 k) t1 t2 /\
      kdeq L k1 k2.
    Admitted.
    eapply invert_tyeq_CExists in Htyeq2.
    destruct Htyeq2 as (Htyeq2 & Hkdeq).
    assert (Hkdc : kinding [] c k).
    {
      eapply KdEq; eauto.
    }
    Lemma ty_subst0_c_e k L W G e t i c :
      typing (k :: L, W, G) e t i ->
      kinding L c k ->
      typing (L, fmap_map (subst0_c_c c) W, map (subst0_c_c c) G) (subst0_c_e c e) (subst0_c_c c t) (subst0_c_c c i).
    Admitted.
    eapply ty_subst0_c_e with (L := []) in Hty2; eauto.
    simplify.
    Lemma fmap_map_subst0_shift01 k c W : fmap_map (K := k) (subst0_c_c c) (fmap_map shift01_c_c W) = W.
    Admitted.
    rewrite fmap_map_subst0_shift01 in Hty2.
    Lemma forget01_c_c_Some_subst0 c c' c'' :
      forget01_c_c c = Some c' ->
      subst0_c_c c'' c = c'.
    Admitted.
    erewrite (@forget01_c_c_Some_subst0 t2) in Hty2; eauto.
    erewrite (@forget01_c_c_Some_subst0 i2) in Hty2; eauto.
    assert (Htyv' : typing ([], W, []) v (subst0_c_c c t0) i').
    {
      Lemma TyEq C e t2 i t1 :
        typing C e t1 i ->
        tyeq (get_kctx C) KType t1 t2 ->
        typing C e t2 i.
      Admitted.
      eapply TyEq; eauto.
      simplify.
      admit.
    }
    eapply ty_subst0_e_e with (G := []) in Hty2; eauto.
    split.
    {
      (* (f - f <= interpTime i)%time *)
      admit.
    }
    exists W.
    repeat split.
    {
      eapply TySub.
      {
        eapply Hty2.
      }
      {
        (* tyeq *)
        simplify.
        Lemma tyeq_sym L k t1 t2 : tyeq L k t1 t2 -> tyeq L k t2 t1.
        Admitted.
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        (* le *)
        admit.
      }
    }
    {
      eapply Hhty.
    }
    {
      (* (interpTime (Tminus i (Tconst (f - f))) <= f)%time *)
      admit.
    }
    {
      eapply includes_intro.
      eauto.
    }
  }
  {
    (* Case Read *)
    destruct H as (Hty & Hhty & Hle).
    rename t into f.
    rename t0 into t.
    Lemma invert_TyRead C e t i :
      typing C (ERead e) t i ->
      exists i' ,
        typing C e (CRef t) i' /\
        interpP (get_kctx C) (i' <= i)%idx.
    Admitted.
    eapply invert_TyRead in Hty.
    destruct Hty as (i' & Hty & Hle2).
    simplify.
    Lemma invert_TyLoc C l t i :
      typing C (ELoc l) t i ->
      exists t' ,
        tyeq (get_kctx C) KType t (CRef t') /\
        get_hctx C $? l = Some t'.
    Admitted.
    eapply invert_TyLoc in Hty.
    destruct Hty as (t' & Htyeq & Hl).
    Arguments get_hctx _ / .
    simplify.
    Lemma htyping_elim h W l v t :
      htyping h W ->
      h $? l = Some v ->
      W $? l = Some t ->
      value v /\
      typing ([], W, []) v t T0.
    Admitted.
    generalize Hhty; intro Hhty0.
    eapply htyping_elim in Hhty; eauto.
    destruct Hhty as (Hval & Htyv).
    Lemma invert_tyeq_CRef L k t t' :
      tyeq L k (CRef t) (CRef t') ->
      tyeq L KType t t'.
    Admitted.
    eapply invert_tyeq_CRef in Htyeq.
    split.
    {
      (* (f - f <= interpTime i)%time *)
      admit.
    }
    exists W.
    repeat split.
    {
      eapply TySub.
      {
        eapply Htyv.
      }
      {
        (* tyeq *)
        simplify.
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        (* le *)
        admit.
      }
    }
    {
      eapply Hhty0.
    }
    {
      (* (interpTime (Tminus i (Tconst (f - f))) <= f)%time *)
      admit.
    }
    {
      eapply includes_intro.
      eauto.
    }
  }
  {
    (* Case Write *)
    destruct H as (Hty & Hhty & Hle).
    rename t into f.
    rename t0 into t.
    Lemma invert_TyWrite C e1 e2 t i :
      typing C (EWrite e1 e2) t i ->
      exists t' i1 i2 ,
        tyeq (get_kctx C) KType t CTypeUnit /\
        typing C e1 (CRef t') i1 /\
        typing C e2 t' i2 /\
        interpP (get_kctx C) (i1 + i2 <= i)%idx.
    Admitted.
    eapply invert_TyWrite in Hty.
    destruct Hty as (t' & i1 & i2 & Htyeq & Hty1 & Hty2 & Hle2).
    eapply invert_TyLoc in Hty1.
    destruct Hty1 as (t'' & Htyeq2 & Hl).
    simplify.
    eapply invert_tyeq_CRef in Htyeq2.
    Ltac copy h h2 := generalize h; intro h2.
    copy Hhty Hhty0.
    eapply htyping_elim in Hhty; eauto.
    destruct Hhty as (Hval' & Htyv').
    split.
    {
      (* (f - f <= interpTime i)%time *)
      admit.
    }
    exists W.
    repeat split.
    {
      eapply TySub.
      {
        Lemma TyETT C : typing C ETT CTypeUnit T0.
        Proof.
          eapply TyConst.
        Qed.
        eapply TyETT.
      }
      {
        simplify.
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        (* le *)
        admit.
      }
    }
    {
      Lemma htyping_upd h W l t v i :
        htyping h W ->
        W $? l = Some t ->
        value v ->
        typing ([], W, []) v t i ->
        htyping (h $+ (l, v)) W.
      Admitted.
      eapply htyping_upd; eauto.
      eapply TyEq.
      {
        eapply Hty2.
      }
      {
        simplify.
        eauto.
      }
    }
    {
      (* (interpTime (Tminus i (Tconst (f - f))) <= f)%time *)
      admit.
    }
    {
      eapply includes_intro.
      eauto.
    }
  }
  {
    (* Case New *)
    destruct H as (Hty & Hhty & Hle).
    rename t into f.
    rename t0 into t.
    Lemma invert_TyNew C e t i :
      typing C (ENew e) t i ->
      exists t' i' ,
        tyeq (get_kctx C) KType t (CRef t') /\
        typing C e t' i' /\
        interpP (get_kctx C) (i' <= i)%idx.
    Admitted.
    eapply invert_TyNew in Hty.
    destruct Hty as (t' & i' & Htyeq & Hty & Hle2).
    simplify.
    split.
    {
      (* (f - f <= interpTime i)%time *)
      admit.
    }
    exists (W $+ (l, t')).
    repeat split.
    {
      eapply TySub.
      {
        eapply TyLoc.
        simplify.
        eauto.
      }
      {
        simplify.
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        (* le *)
        admit.
      }
    }
    {
      Lemma htyping_new h W l t v i :
        htyping h W ->
        h $? l = None ->
        value v ->
        typing ([], W, []) v t i ->
        htyping (h $+ (l, v)) (W $+ (l, t)).
      Admitted.
      eapply htyping_new in Hhty; eauto.
    }
    {
      (* (interpTime (Tminus i (Tconst (f - f))) <= f)%time *)
      admit.
    }
    {
      eapply includes_intro.
      intros k v' Hk.
      assert (HWk : W $? k = None).
      {
        admit.
      }
      cases (l ==n k); subst.
      {
        simplify.
        eauto.
      }
      rewrite Hk in HWk.
      invert HWk.
    }
  }
  {
    (* Case Beta *)
    destruct H as (Hty & Hhty & Hle).
    rename t into f.
    rename t0 into t.
    Lemma invert_TyApp C e1 e2 t i :
      typing C (EApp e1 e2) t i ->
      exists t' t2 i1 i2 i3 ,
        tyeq (get_kctx C) KType t t' /\
        typing C e1 (CArrow t2 i3 t') i1 /\
        typing C e2 t2 i2 /\
        interpP (get_kctx C) (i1 + i2 + T1 + i3 <= i)%idx.
    Admitted.
    eapply invert_TyApp in Hty.
    destruct Hty as (t' & t2 & i1 & i2 & i3 & Htyeq & Hty1 & Hty2 & Hle2).
    simplify.
    Lemma invert_TyAbs C e t i :
      typing C (EAbs e) t i ->
      exists t1 i' t2 ,
        tyeq (get_kctx C) KType t (CArrow t1 i' t2) /\
        kinding (get_kctx C) t1 KType /\
        typing (add_typing_ctx t1 C) e t2 i'.
    Admitted.
    eapply invert_TyAbs in Hty1.
    destruct Hty1 as (t1 & i' & t3 & Htyeq2 & Hkd & Hty1).
    simplify.
    Lemma invert_tyeq_CArrow L k t1 i t2 t1' i' t2' :
      tyeq L k (CArrow t1 i t2) (CArrow t1' i' t2') ->
      tyeq L KType t1 t1' /\
      interpP L (PEq i i') /\
      tyeq L KType t2 t2'.
    Admitted.
    eapply invert_tyeq_CArrow in Htyeq2.
    destruct Htyeq2 as (Htyeq2 & Hieq & Htyeq3).
    split.
    {
      (* (1 + f - f <= interpTime i)%time *)
      admit.
    }
    exists W.
    repeat split.
    {
      eapply TySub.
      {
        eapply ty_subst0_e_e with (G := []) in Hty1; eauto.
        eapply TyEq; eauto.
      }
      {
        simplify.
        eapply tyeq_sym.
        Lemma tyeq_trans L k a b c :
          tyeq L k a b ->
          tyeq L k b c ->
          tyeq L k a c.
        Admitted.
        eapply tyeq_trans; eauto.
      }
      {
        simplify.
        (* le *)
        admit.
      }
    }
    {
      eapply Hhty.
    }
    {
      (* (interpTime (Tminus i (Tconst (1 + f - f))) <= f)%time *)
      admit.
    }
    {
      eapply includes_intro.
      eauto.
    }
  }
  {
    (* Case AppC *)
    destruct H as (Hty & Hhty & Hle).
    rename t into f.
    rename t0 into t.
    Lemma invert_TyAppC C e c t i :
      typing C (EAppC e c) t i ->
      exists t' i' k ,
        tyeq (get_kctx C) KType t (subst0_c_c c t') /\
        typing C e (CForall k t') i' /\
        kinding (get_kctx C) c k /\
        interpP (get_kctx C) (i' <= i)%idx.
    Admitted.
    eapply invert_TyAppC in Hty.
    destruct Hty as (t' & i' & k' & Htyeq & Hty & Hkdc & Hle2).
    simplify.
    Lemma invert_TyAbsC C e t i :
      typing C (EAbsC e) t i ->
      exists t' k ,
        tyeq (get_kctx C) KType t (CForall k t') /\
        value e /\
        wfkind (get_kctx C) k /\
        typing (add_kinding_ctx k C) e t' T0.
    Admitted.
    eapply invert_TyAbsC in Hty.
    destruct Hty as (t'' & k & Htyeq2 & Hval & Hwfk & Hty).
    simplify.
    Lemma invert_tyeq_CForall L k k1 t1 k2 t2 :
      tyeq L k (CForall k1 t1) (CForall k2 t2) ->
      tyeq L (KArrow k1 k) t1 t2 /\
      kdeq L k1 k2.
    Admitted.
    eapply invert_tyeq_CForall in Htyeq2.
    destruct Htyeq2 as (Htyeq2 & Hkdeq).
    assert (Hkdck : kinding [] c k).
    {
      eapply KdEq; eauto.
      Lemma kdeq_sym L a b : kdeq L a b -> kdeq L b a.
      Admitted.
      eapply kdeq_sym; eauto.
    }
    split.
    {
      (* (f - f <= interpTime i)%time *)
      admit.
    }
    exists W.
    repeat split.
    {
      eapply TySub.
      {
        eapply ty_subst0_c_e with (G := []) in Hty; eauto.
        simplify.
        rewrite fmap_map_subst0_shift01 in Hty.
        eauto.
      }
      {
        simplify.
        (* tyeq *)
        eapply tyeq_sym.
        eapply tyeq_trans; eauto.
        admit.
      }
      {
        simplify.
        (* le *)
        admit.
      }
    }
    {
      eapply Hhty.
    }
    {
      (* (interpTime (Tminus i (Tconst (f - f))) <= f)%time *)
      admit.
    }
    {
      eapply includes_intro.
      eauto.
    }
  }
  {
    (* Case Proj-Pair *)
    destruct H as (Hty & Hhty & Hle).
    rename t into f.
    rename t0 into t.
    Lemma invert_TyProj C pr e t i :
      typing C (EProj pr e) t i ->
      exists t1 t2 i' ,
        tyeq (get_kctx C) KType t (proj (t1, t2) pr) /\
        typing C e (CProd t1 t2) i' /\
        interpP (get_kctx C) (i' <= i)%idx.
    Admitted.
    eapply invert_TyProj in Hty.
    destruct Hty as (t1 & t2 & i' & Htyeq & Hty & Hle2).
    simplify.
    Lemma invert_TyPair C e1 e2 t i :
      typing C (EPair e1 e2) t i ->
      exists t1 t2 i1 i2 ,
        tyeq (get_kctx C) KType t (CProd t1 t2) /\
        typing C e1 t1 i1 /\
        typing C e2 t2 i2 /\
        interpP (get_kctx C) (i1 + i2 <= i)%idx.
    Admitted.
    eapply invert_TyPair in Hty.
    destruct Hty as (t1' & t2' & i1 & i2 & Htyeq2 & Hty1 & Hty2 & Hle3).
    simplify.
    Lemma invert_tyeq_CProd L k t1 t2 t1' t2' :
      tyeq L k (CProd t1 t2) (CProd t1' t2') ->
      tyeq L KType t1 t1' /\
      tyeq L KType t2 t2'.
    Admitted.
    eapply invert_tyeq_CProd in Htyeq2.
    destruct Htyeq2 as (Htyeq2 & Htyeq3).
    split.
    {
      (* (f - f <= interpTime i)%time *)
      admit.
    }
    exists W.
    repeat split.
    {
      cases pr; simplify.
      {
        eapply TySub; eauto.
        {
          simplify.
          eapply tyeq_sym.
          eapply tyeq_trans; eauto.
        }
        {
          simplify.
          admit. (* interpP [] (i1 <= Tminus i (Tconst (f - f)%time))%idx *)
        }
      }
      {
        eapply TySub; eauto.
        {
          simplify.
          eapply tyeq_sym.
          eapply tyeq_trans; eauto.
        }
        {
          simplify.
          admit. (* interpP [] (i1 <= Tminus i (Tconst (f - f)%time))%idx *)
        }
      }
    }
    {
      eapply Hhty.
    }
    {
      (* (interpTime (Tminus i (Tconst (f - f))) <= f)%time *)
      admit.
    }
    {
      eapply includes_intro.
      eauto.
    }
  }
  {
    (* Case Case-Inj *)
    destruct H as (Hty & Hhty & Hle).
    rename t into f.
    rename t0 into t.
    Lemma invert_TyCase C e e1 e2 t i :
      typing C (ECase e e1 e2) t i ->
      exists t1 t2 i0 i1 i2 ,
        typing C e (CSum t1 t2) i0 /\
        typing (add_typing_ctx t1 C) e1 t i1 /\
        typing (add_typing_ctx t2 C) e2 t i2 /\
        interpP (get_kctx C) (i0 + Tmax i1 i2 <= i)%idx.
    Admitted.
    eapply invert_TyCase in Hty.
    destruct Hty as (t1 & t2 & i0 & i1 & i2 & Hty0 & Hty1 & Hty2 & Hle2).
    simplify.
    Lemma invert_TyInj C inj e t i :
      typing C (EInj inj e) t i ->
      exists t' t'' i' ,
        tyeq (get_kctx C) KType t (choose (CSum t' t'', CSum t'' t') inj) /\
        typing C e t' i' /\
        kinding (get_kctx C) t'' KType /\
        interpP (get_kctx C) (i' <= i)%idx.
    Admitted.
    eapply invert_TyInj in Hty0.
    destruct Hty0 as (t' & t'' & i' & Htyeq & Hty0 & Hkd & Hle3).
    simplify.
    split.
    {
      (* (f - f <= interpTime i)%time *)
      admit.
    }
    exists W.
    repeat split.
    {
      Lemma invert_tyeq_CSum L k t1 t2 t1' t2' :
        tyeq L k (CSum t1 t2) (CSum t1' t2') ->
        tyeq L KType t1 t1' /\
        tyeq L KType t2 t2'.
      Admitted.
      Lemma TyLe C e t i1 i2 :
        typing C e t i1 ->
        interpP (get_kctx C) (i1 <= i2)%idx ->
        typing C e t i2.
      Admitted.
      cases inj; simplify.
      {
        eapply invert_tyeq_CSum in Htyeq.
        destruct Htyeq as (Htyeq1 & Htyeq2).
        eapply TyLe; eauto.
        {
          eapply ty_subst0_e_e with (G := []) in Hty1; eauto.
          eapply TyEq; eauto.
          simplify.
          eapply tyeq_sym; eauto.
        }
        {
          simplify.
          admit. (* interpP [] (i1 + i' <= Tminus i (Tconst (f - f)%time))%idx *)
        }
      }
      {
        eapply invert_tyeq_CSum in Htyeq.
        destruct Htyeq as (Htyeq1 & Htyeq2).
        eapply TyLe; eauto.
        {
          eapply ty_subst0_e_e with (G := []) in Hty2; eauto.
          eapply TyEq; eauto.
          simplify.
          eapply tyeq_sym; eauto.
        }
        {
          simplify.
          admit. (* interpP [] (i2 + i' <= Tminus i (Tconst (f - f)%time))%idx *)
        }
      }
    }
    {
      eapply Hhty.
    }
    {
      (* (interpTime (Tminus i (Tconst (f - f))) <= f)%time *)
      admit.
    }
    {
      eapply includes_intro.
      eauto.
    }
  }
Qed.

Lemma generalize_plug : forall C e e_all,
    plug C e e_all ->
    forall W t i,
      typing ([], W, []) e_all t i ->
      exists t1 i1,
        typing ([], W, []) e t1 i1 /\
        interpP [] (i1 <= i)%idx /\
        forall e' e_all' W' i1',
          plug C e' e_all' ->
          typing ([], W', []) e' t1 i1' ->
          interpP [] (i1' <= i1)%idx ->
          W $<= W' ->
          typing ([], W', []) e_all' t (i1' + Tminus i i1)%idx.
Proof.
  induct 1; intros W t i Hty.
  {
    exists t, i.
    repeat split; eauto.
    {
      admit. (* interpP [] (i <= i)%idx *)
    }
    intros.
    invert H.
    eapply TyLe; eauto.
    admit. (* interpP (get_kctx ([], W', [])) (i1' <= i1' + Tminus i i)%idx *)
  }
  {
    cases opr.
    {
      (* Case Proj *)
      eapply invert_TyProj in Hty.
      destruct Hty as (t1 & t2 & i' & Htyeq & Hty & Hle).
      simplify.
      eapply IHplug in Hty; eauto.
      destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        admit. (* interpP [] (i0 <= i)%idx *)
      }
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
      invert Hplug.
      rename e'0 into e_all''.
      rename H4 into Hplug.
      eapply HE in Hplug; eauto.
      eapply TySub.
      {
        eapply TyProj; eauto.
      }
      {
        simplify.
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        admit. (* interpP [] (i1' + Tminus i1 i0 <= i1' + Tminus i i0)%idx *)
      }
    }
    {
      (* Case Inj *)
      eapply invert_TyInj in Hty.
      destruct Hty as (t1 & t2 & i' & Htyeq & Hty & Hkd & Hle).
      simplify.
      eapply IHplug in Hty; eauto.
      destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        admit. (* interpP [] (i0 <= i)%idx *)
      }
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
      invert Hplug.
      rename e'0 into e_all''.
      rename H4 into Hplug.
      eapply HE in Hplug; eauto.
      cases inj; simplify.
      {
        eapply TySub.
        {
          eapply TyInj with (t' := t2); eauto.
        }
        {
          simplify.
          eapply tyeq_sym; eauto.
        }
        {
          simplify.
          admit. (* interpP [] (i1' + Tminus i1 i0 <= i1' + Tminus i i0)%idx *)
        }
      }
      {
        eapply TySub.
        {
          eapply TyInj with (t' := t2); eauto.
        }
        {
          simplify.
          eapply tyeq_sym; eauto.
        }
        {
          simplify.
          admit. (* interpP [] (i1' + Tminus i1 i0 <= i1' + Tminus i i0)%idx *)
        }
      }
    }
    {
      (* Case AppC *)
      eapply invert_TyAppC in Hty.
      destruct Hty as (t' & i' & k & Htyeq & Hty & Hkd & Hle).
      simplify.
      eapply IHplug in Hty; eauto.
      destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        admit. (* interpP [] (i0 <= i)%idx *)
      }
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
      invert Hplug.
      rename e'0 into e_all''.
      rename H4 into Hplug.
      eapply HE in Hplug; eauto.
      eapply TySub.
      {
        eapply TyAppC; eauto.
      }
      {
        simplify.
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        admit. (* interpP [] (i1' + Tminus i1 i0 <= i1' + Tminus i i0)%idx *)
      }
    }
    {
      (* Case Pack *)
      eapply invert_TyPack in Hty.
      destruct Hty as (t1 & k & i' & Htyeq & Hkd & Hkdc & Hty & Hle).
      simplify.
      eapply IHplug in Hty; eauto.
      destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        admit. (* interpP [] (i0 <= i)%idx *)
      }
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
      invert Hplug.
      rename e'0 into e_all''.
      rename H4 into Hplug.
      eapply HE in Hplug; eauto.
      eapply TySub.
      {
        eapply TyPack; eauto.
      }
      {
        simplify.
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        admit. (* interpP [] (i1' + Tminus i1 i0 <= i1' + Tminus i i0)%idx *)
      }
    }
    {
      (* Case Fold *)
      eapply invert_TyFold in Hty.
      destruct Hty as (t0 & t1 & cs & t2 & i' & Htyeq & ? & ? & Hkd & Hty & Hle).
      subst.
      simplify.
      eapply IHplug in Hty; eauto.
      destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        admit. (* interpP [] (i0 <= i)%idx *)
      }
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
      invert Hplug.
      rename e'0 into e_all''.
      rename H4 into Hplug.
      eapply HE in Hplug; eauto.
      eapply TySub.
      {
        eapply TyFold; eauto.
      }
      {
        simplify.
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        admit. (* interpP [] (i1' + Tminus i1 i0 <= i1' + Tminus i i0)%idx *)
      }
    }
    {
      (* Case Unfold *)
      eapply invert_TyUnfold in Hty.
      destruct Hty as (t0 & t1 & cs & i' & Htyeq & ? & Hty & Hle).
      subst.
      simplify.
      eapply IHplug in Hty; eauto.
      destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        admit. (* interpP [] (i0 <= i)%idx *)
      }
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
      invert Hplug.
      rename e'0 into e_all''.
      rename H4 into Hplug.
      eapply HE in Hplug; eauto.
      eapply TySub.
      {
        eapply TyUnfold; eauto.
      }
      {
        simplify.
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        admit. (* interpP [] (i1' + Tminus i' i0 <= i1' + Tminus i i0)%idx *)
      }
    }
    {
      (* Case New *)
      eapply invert_TyNew in Hty.
      destruct Hty as (t' & i' & Htyeq & Hty & Hle).
      simplify.
      eapply IHplug in Hty; eauto.
      destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        admit. (* interpP [] (i0 <= i)%idx *)
      }
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
      invert Hplug.
      rename e'0 into e_all''.
      rename H4 into Hplug.
      eapply HE in Hplug; eauto.
      eapply TySub.
      {
        eapply TyNew; eauto.
      }
      {
        simplify.
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        admit. (* interpP [] (i1' + Tminus i' i0 <= i1' + Tminus i i0)%idx *)
      }
    }
    {
      (* Case Read *)
      eapply invert_TyRead in Hty.
      destruct Hty as (i' & Hty & Hle).
      simplify.
      eapply IHplug in Hty; eauto.
      destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        admit. (* interpP [] (i0 <= i)%idx *)
      }
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
      invert Hplug.
      rename e'0 into e_all''.
      rename H4 into Hplug.
      eapply HE in Hplug; eauto.
      eapply TyLe.
      {
        eapply TyRead; eauto.
      }
      {
        simplify.
        admit. (* interpP [] (i1' + Tminus i' i0 <= i1' + Tminus i i0)%idx *)
      }
    }
  }
  {
    cases opr.
    {
      (* Case BinOpPrim *)
      Lemma invert_TyBinOpPrim C opr e1 e2 t i : typing C (EBinOp (EBPrim opr) e1 e2) t i -> False.
      Admitted.
      eapply invert_TyBinOpPrim in Hty.
      destruct Hty.
    }
    {
      (* Case App *)
      eapply invert_TyApp in Hty.
      destruct Hty as (t' & t2 & i1 & i2 & i3 & Htyeq & Hty1 & Hty2 & Hle).
      simplify.
      eapply IHplug in Hty1; eauto.
      destruct Hty1 as (t1 & i0 & Hty1 & Hle2 & HE).
      exists t1, i0.
      repeat split; eauto.
      {
        admit. (* interpP [] (i0 <= i)%idx *)
      }
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
      invert Hplug.
      rename e'0 into e_all''.
      rename H5 into Hplug.
      eapply HE in Hplug; eauto.
      eapply TySub.
      {
        eapply TyApp; eauto.
        Lemma weaken_W L W G e t i W' :
          typing (L, W, G) e t i ->
          W $<= W' ->
          typing (L, W', G) e t i.
        Admitted.
        eapply weaken_W; eauto.
      }
      {
        eapply tyeq_sym; eauto.
      }
      {
        instantiate (1 := T1).
        admit. (* interpP (get_kctx ([], W', [])) (i1' + Tminus i1 i0 + i2 + T1 + i3 <= i1' + Tminus i i0)%idx *)
      }
    }
    {
      (* Case Pair *)
      eapply invert_TyPair in Hty.
      destruct Hty as (t1 & t2 & i1 & i2 & Htyeq & Hty1 & Hty2 & Hle).
      simplify.
      eapply IHplug in Hty1; eauto.
      destruct Hty1 as (t0 & i0 & Hty1 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        admit. (* interpP [] (i0 <= i)%idx *)
      }
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
      invert Hplug.
      rename e'0 into e_all''.
      rename H5 into Hplug.
      eapply HE in Hplug; eauto.
      eapply TySub.
      {
        eapply TyPair; eauto.
        eapply weaken_W; eauto.
      }
      {
        simplify.
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        admit. (* interpP [] (i1' + Tminus i1 i0 + i2 <= i1' + Tminus i i0)%idx *)
      }
    }
    {
      (* Case Write *)
      eapply invert_TyWrite in Hty.
      destruct Hty as (t' & i1 & i2 & Htyeq & Hty1 & Hty2 & Hle).
      simplify.
      eapply IHplug in Hty1; eauto.
      destruct Hty1 as (t0 & i0 & Hty1 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        admit. (* interpP [] (i0 <= i)%idx *)
      }
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
      invert Hplug.
      rename e'0 into e_all''.
      rename H5 into Hplug.
      eapply HE in Hplug; eauto.
      eapply TySub.
      {
        eapply TyWrite; eauto.
        eapply weaken_W; eauto.
      }
      {
        simplify.
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        admit. (* interpP [] (i1' + Tminus i1 i0 + i2 <= i1' + Tminus i i0)%idx *)
      }
    }
  }
  {
    (* Case BinOp2 *)
    cases opr.
    {
      (* Case BinOpPrim *)
      eapply invert_TyBinOpPrim in Hty.
      destruct Hty.
    }
    {
      (* Case App *)
      eapply invert_TyApp in Hty.
      destruct Hty as (t' & t2 & i1 & i2 & i3 & Htyeq & Hty1 & Hty2 & Hle).
      simplify.
      eapply IHplug in Hty2; eauto.
      destruct Hty2 as (t0 & i0 & Hty2 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        admit. (* interpP [] (i0 <= i)%idx *)
      }
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
      invert Hplug.
      rename e'0 into e_all''.
      rename H6 into Hplug.
      eapply HE in Hplug; eauto.
      eapply TySub.
      {
        eapply TyApp; eauto.
        eapply weaken_W; eauto.
      }
      {
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        instantiate (1 := T1).
        admit. (* interpP (get_kctx ([], W', [])) (i1' + Tminus i2 i0 + i1 + T1 + i3 <= i1' + Tminus i i0)%idx *)
      }
    }
    {
      (* Case Pair *)
      eapply invert_TyPair in Hty.
      destruct Hty as (t1 & t2 & i1 & i2 & Htyeq & Hty1 & Hty2 & Hle).
      simplify.
      eapply IHplug in Hty2; eauto.
      destruct Hty2 as (t0 & i0 & Hty2 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        admit. (* interpP [] (i0 <= i)%idx *)
      }
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
      invert Hplug.
      rename e'0 into e_all''.
      rename H6 into Hplug.
      eapply HE in Hplug; eauto.
      eapply TySub.
      {
        eapply TyPair; eauto.
        eapply weaken_W; eauto.
      }
      {
        simplify.
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        admit. (* interpP [] (i1' + Tminus i2 i0 + i1 <= i1' + Tminus i i0)%idx *)
      }
    }
    {
      (* Case Write *)
      eapply invert_TyWrite in Hty.
      destruct Hty as (t' & i1 & i2 & Htyeq & Hty1 & Hty2 & Hle).
      simplify.
      eapply IHplug in Hty2; eauto.
      destruct Hty2 as (t0 & i0 & Hty2 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        admit. (* interpP [] (i0 <= i)%idx *)
      }
      intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
      invert Hplug.
      rename e'0 into e_all''.
      rename H6 into Hplug.
      eapply HE in Hplug; eauto.
      eapply TySub.
      {
        eapply TyWrite; eauto.
        eapply weaken_W; eauto.
      }
      {
        simplify.
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        admit. (* interpP [] (i1' + Tminus i2 i0 + i1 <= i1' + Tminus i i0)%idx *)
      }
    }
  }
  {
    (* Case Case *)
    eapply invert_TyCase in Hty.
    destruct Hty as (t1 & t2 & i0' & i1 & i2 & Hty0 & Hty1 & Hty2 & Hle).
    simplify.
    eapply IHplug in Hty0; eauto.
    destruct Hty0 as (t0 & i0 & Hty0 & Hle2 & HE).
    exists t0, i0.
    repeat split; eauto.
    {
      admit. (* interpP [] (i0 <= i)%idx *)
    }
    intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
    invert Hplug.
    rename e'0 into e_all''.
    rename H5 into Hplug.
    eapply HE in Hplug; eauto.
    eapply TyLe.
    {
      eapply TyCase; eauto;
      eapply weaken_W; eauto.
    }
    {
      simplify.
      admit. (* interpP [] (i1' + Tminus i0' i0 + Tmax i1 i2 <= i1' + Tminus i i0)%idx *)
    }
  }
  {
    (* Case Unpack *)
    eapply invert_TyUnpack in Hty.
    destruct Hty as (t2' & t0' & i1 & k & t2 & i2 & i2' & Htyeq & Hty1 & Hty2 & Hfg1 & Hfg2 & Hle).
    simplify.
    eapply IHplug in Hty1; eauto.
    destruct Hty1 as (t0 & i0 & Hty1 & Hle2 & HE).
    exists t0, i0.
    repeat split; eauto.
    {
      admit. (* interpP [] (i0 <= i)%idx *)
    }
    intros e'' e_all' W' i1' Hplug Htye'' Hle3 Hincl.
    invert Hplug.
    rename e'0 into e_all''.
    rename H4 into Hplug.
    eapply HE in Hplug; eauto.
    eapply TySub with (t1 := t2').
    {
      eapply TyUnpack; eauto.
      simplify.
      assert (Hincl' : fmap_map shift01_c_c W $<= fmap_map shift01_c_c W').
      {
        admit.
      }
      eapply weaken_W; eauto.
    }
    {
      simplify.
      eapply tyeq_sym; eauto.
    }
    {
      simplify.
      admit. (* interpP [] (i1' + Tminus i1 i0 + i2' <= i1' + Tminus i i0)%idx *)
    }
  }
Qed.

Lemma preservation s s' :
  step s s' ->
  (* forall h e f h' e' f', *)
  (*   step (h, e, f) (h', e', f') -> *)
  (*   let s := (h, e, f) in *)
  (*   let s' := (h', e', f') in *)
  forall W t i,
    ctyping W s t i ->
    exists W' i',
      ctyping W' s' t i' /\
      (W $<= W').
Proof.
  invert 1.
  (* induct 1. *)
  (* induction 1. *)
  simplify.
  destruct H as (Hty & Hhty & Hle).
  (* destruct H3 as [Hty & Hhty & Hle]. *)
  (* generalize H3. *)
  (* intros (Hty & Hhty & Hle). *)
  (* intros (Hty, (Hhty, Hle)). *)
  (* intros (Hty, Hhty). *)
  rename t into f.
  rename t' into f'.
  rename e1 into e_all.
  rename e1' into e_all'.
  rename t0 into t_all.
  eapply generalize_plug in Hty; eauto.
  destruct Hty as (t1 & i1 & Hty & Hle2 & He').
  rename H0 into Hstep.
  eapply preservation0 in Hstep.
  Focus 2.
  {
    unfold ctyping; repeat split; eauto.
    admit. (* (interpTime i1 <= f)%time *)
  }
  Unfocus.
  simplify.
  destruct Hstep as (Hle3 & W' & Hty2 & Hincl).
  destruct Hty2 as (Hty2 & Hhty' & Hle4).
  eapply He' in H2; eauto.
  Focus 2.
  {
    admit. (* interpP [] (Tminus i1 (Tconst (f - f')%time) <= i1)%idx *)
  }
  Unfocus.
  exists W'.
  eexists.
  repeat split; eauto.
  admit. (* (interpTime (Tminus i1 (Tconst (f - f')) + Tminus i i1)%idx <= f')%time *)
Qed.

Hint Resolve progress preservation.

Definition trsys_of (s : config) :=
  {|
    Initial := {s};
    Step := step
  |}.

Theorem safety W s t i :
  ctyping W s t i ->
  invariantFor (trsys_of s) unstuck.
Proof.
  simplify.
  apply invariant_weaken with (invariant1 := fun s' => exists W' i', ctyping W' s' t i'); eauto.
  {
    apply invariant_induction; simplify; eauto.
    {
      propositional.
      subst; simplify.
      eauto.
    }
    {
      destruct H0 as (W' & i' & Hty).
      propositional.
      eapply preservation in H1; eauto.
      destruct H1 as (W'' & i'' & Hty' & Hle).
      eauto.
    }
  }
  {
    simplify.
    destruct H0 as (W' & i' & Hty).
    eauto.
  }
Qed.

(*
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
*)  
