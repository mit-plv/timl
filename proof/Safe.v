Require Import Frap.

Set Implicit Arguments.

Ltac copy h h2 := generalize h; intro h2.

Ltac try_eexists := try match goal with | |- exists _, _ => eexists end.

Ltac try_split := try match goal with | |- _ /\ _ => split end.

Ltac eexists_split :=
  try match goal with
      | |- exists _, _ => eexists
      | |- _ /\ _ => split
      end.

Module Type TIME.
  Parameter time_type : Type.
  Parameter Time0 : time_type.
  Parameter Time1 : time_type.
  Parameter TimeAdd : time_type -> time_type -> time_type.
  Parameter TimeMinus : time_type -> time_type -> time_type.
  Parameter TimeLe : time_type -> time_type -> Prop.
End TIME.

Module RealTime <: TIME.
  Require Rdefinitions.
  Module R := Rdefinitions.
  Definition real := R.R.
  (* Require RIneq. *)
  (* Definition nnreal := RIneq.nonnegreal. *)
  Definition time_type := real.
  (* Definition time_type := nnreal. *)
  Definition Time0 := R.R0.
  Definition Time1 := R.R1.
  Definition TimeAdd := R.Rplus.
  Definition TimeMinus := R.Rminus.
  Definition TimeLe := R.Rle.
End RealTime.

Module NNRealTime <: TIME.
  Require RIneq.
  Definition nnreal := RIneq.nonnegreal.
  Definition time_type := nnreal.
  Definition Time0 : time_type.
    Require Rdefinitions.
    Module R := Rdefinitions.
    refine (RIneq.mknonnegreal R.R0 _).
    eauto with rorders.
  Defined.
  Definition Time1 : time_type.
    refine (RIneq.mknonnegreal R.R1 _).
    eauto with rorders.
    admit.
  Admitted.
  Definition TimeAdd (a b : time_type) : time_type.
    Import RIneq.
    refine (mknonnegreal (R.Rplus (nonneg a) (nonneg b)) _).
    destruct a.
    destruct b.
    simplify.
    admit.
  Admitted.
  Definition TimeMinus (a b : time_type) : time_type.
  Admitted.
  Definition TimeLe (a b : time_type) : Prop.
    refine (R.Rle (nonneg a) (nonneg b)).
  Defined.
End NNRealTime.

Module NatTime <: TIME.
  Definition time_type := nat.
  Definition Time0 := 0.
  Definition Time1 := 1.
  Definition TimeAdd := plus.
  Definition TimeMinus := Peano.minus.
  Definition TimeLe := le.
End NatTime.

(* Module Time := RealTime. *)
(* Module Time := NatTime. *)

Module M (Time : TIME).
Import Time.

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

Inductive cstr_const :=
| CCIdxTT
| CCIdxNat (n : nat)
| CCTime (r : time_type)
| CCTypeUnit
| CCTypeInt
.

(* Inductive cstr_un_op := *)
(* . *)

Inductive cstr_bin_op :=
| CBTimeAdd
| CBTimeMinus
| CBTimeMax
| CBTypeProd
| CBTypeSum
(* | CBApp *)
.

Inductive quan :=
| QuanForall
| QuanExists
.

Definition var := nat.

Inductive prop_bin_conn :=
| PBCAnd
| PBCOr
| PBCImply
.

Inductive prop_bin_pred :=
| PBTimeLe
| PBBigO (arity : nat)
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
(* | CUnOp (opr : cstr_un_op) (c : cstr) *)
| CBinOp (opr : cstr_bin_op) (c1 c2 : cstr)
| CIte (i1 i2 i3 : cstr)
| CTimeAbs (i : cstr)
| CArrow (t1 i t2 : cstr)
| CAbs (* (k : kind) *) (t : cstr)
| CApp (c1 c2 : cstr)
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

Definition KUnit := KBaseSort BSUnit.
Definition KBool := KBaseSort BSBool.
Definition KNat := KBaseSort BSNat.
Definition KTimeFun arity := KBaseSort (BSTimeFun arity).
Definition KTime := KTimeFun 0.

Notation Tconst r := (CConst (CCTime r)).
Notation T0 := (Tconst Time0).
Notation T1 := (Tconst Time1).
Definition Tadd := CBinOp CBTimeAdd.
Definition Tminus := CBinOp CBTimeMinus.

Definition PAnd := PBinConn PBCAnd.
Definition POr := PBinConn PBCOr.
Definition PImply := PBinConn PBCImply.
Definition PIff a b := PAnd (PImply a b) (PImply b a).

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
(* Definition CApp := CBinOp CBApp. *)

Definition Tle := PBinPred PBTimeLe.
Infix "<=" := Tle : idx_scope.
Infix "==" := PEq (at level 70) : idx_scope.
Infix "-->" := PImply (at level 95) : idx_scope.
Infix "<-->" := PIff (at level 95) : idx_scope.

Require BinIntDef.
Definition int := BinIntDef.Z.t.

Inductive expr_const :=
| ECTT
| ECInt (i : int)
.

Definition CInt := CConst CCTypeInt.

Definition const_kind cn :=
  match cn with
  | CCIdxTT => KUnit
  | CCIdxNat _ => KNat
  | CCTime _ => KTime
  | CCTypeUnit => KType
  | CCTypeInt => KType
  end
.

Definition const_type cn :=
  match cn with
  | ECTT => CTypeUnit
  | ECInt _ => CInt
  end
.

Definition cbinop_arg1_kind opr :=
  match opr with
  | CBTimeAdd => KTime
  | CBTimeMinus => KTime
  | CBTimeMax => KTime
  | CBTypeProd => KType
  | CBTypeSum => KType
  end.

Definition cbinop_arg2_kind opr :=
  match opr with
  | CBTimeAdd => KTime
  | CBTimeMinus => KTime
  | CBTimeMax => KTime
  | CBTypeProd => KType
  | CBTypeSum => KType
  end.

Definition cbinop_result_kind opr :=
  match opr with
  | CBTimeAdd => KTime
  | CBTimeMinus => KTime
  | CBTimeMax => KTime
  | CBTypeProd => KType
  | CBTypeSum => KType
  end.

Definition binpred_arg1_kind opr :=
  match opr with
  | PBTimeLe => KTime
  | PBBigO n => KTimeFun n
  end
.

Definition binpred_arg2_kind opr :=
  match opr with
  | PBTimeLe => KTime
  | PBBigO n => KTimeFun n
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

Definition interpTime : cstr -> time_type.
Admitted.

Definition interpP : kctx -> prop -> Prop.
Admitted.

Lemma interpP_le_refl L i : interpP L (i <= i)%idx.
Admitted.
Lemma interpP_le_trans L a b c :
  interpP L (a <= b)%idx ->
  interpP L (b <= c)%idx ->
  interpP L (a <= c)%idx.
Admitted.

Lemma interpP_eq_refl L i : interpP L (i == i)%idx.
Admitted.
Lemma interpP_eq_trans L a b c :
  interpP L (a == b)%idx ->
  interpP L (b == c)%idx ->
  interpP L (a == c)%idx.
Admitted.
Lemma interpP_eq_sym L i i' :
  interpP L (i == i')%idx ->
  interpP L (i' == i)%idx.
Admitted.

Inductive kdeq : kctx -> kind -> kind -> Prop :=
| KdEqKType L :
    kdeq L KType KType
| KdEqKArrow L k1 k2 k1' k2' :
    kdeq L k1 k1' ->
    kdeq L k2 k2' ->
    kdeq L (KArrow k1 k2) (KArrow k1' k2')
| KdEqBaseSort L b :
    kdeq L (KBaseSort b) (KBaseSort b)
| KdEqSubset L k p k' p' :
    kdeq L k k' ->
    interpP (k :: L) (p <--> p')%idx ->
    kdeq L (KSubset k p) (KSubset k' p')
.

Hint Constructors kdeq.

Lemma interpP_iff_refl L p : interpP L (p <--> p)%idx.
Admitted.
Lemma interpP_iff_trans L a b c :
  interpP L (a <--> b)%idx ->
  interpP L (b <--> c)%idx ->
  interpP L (a <--> c)%idx.
Admitted.
Lemma interpP_iff_sym L p p' :
  interpP L (p <--> p')%idx ->
  interpP L (p' <--> p)%idx.
Admitted.

Lemma kdeq_interpP L k k' p :
  kdeq L k k' ->
  interpP (k :: L) p ->
  interpP (k' :: L) p.
Proof.
  (* induct 1; eauto. *)
Admitted.

Lemma kdeq_refl : forall L k, kdeq L k k.
Proof.
  induct k; eauto using interpP_iff_refl.
Qed.

Lemma kdeq_sym L a b : kdeq L a b -> kdeq L b a.
Proof.
  induct 1; eauto using kdeq_interpP, interpP_iff_sym.
Qed.

Lemma kdeq_trans' L a b :
  kdeq L a b ->
  forall c,
    kdeq L b c -> kdeq L a c.
Proof.
  induct 1; invert 1; eauto 6 using interpP_iff_trans, kdeq_interpP, kdeq_sym.
Qed.

Lemma kdeq_trans L a b c : kdeq L a b -> kdeq L b c -> kdeq L a c.
Proof.
  intros; eapply kdeq_trans'; eauto.
Qed.

Definition monotone : cstr -> Prop.
Admitted.

Inductive wfprop : kctx -> prop -> Prop :=
| WfPropTrue L :
    wfprop L PTrue
| WfPropFalse L :
    wfprop L PFalse
| WfPropBinConn L opr p1 p2 :
    wfprop L p1 ->
    wfprop L p2 ->
    wfprop L (PBinConn opr p1 p2)
| WfPropNot L p :
    wfprop L p ->
    wfprop L (PNot p)
| WfPropBinPred L opr i1 i2 :
    kinding L i1 (binpred_arg1_kind opr) ->
    kinding L i2 (binpred_arg2_kind opr) ->
    wfprop L (PBinPred opr i1 i2) 
| WfPropEq L i1 i2 k :
    kinding L i1 k ->
    kinding L i2 k ->
    wfprop L (PEq i1 i2) 
| WfPropQuan L q p k :
    wfkind L k ->
    wfprop (k :: L) p ->
    wfprop L (PQuan q p)
    
with wfkind : kctx -> kind -> Prop :=
| WfKdType L :
    wfkind L KType
| WfKdArrow L k1 k2 :
    wfkind L k1 ->
    wfkind L k2 ->
    wfkind L (KArrow k1 k2)
| WfKdBaseSort L b :
    wfkind L (KBaseSort b)
| WfKdSubset L k p :
    wfkind L k ->
    wfprop (k :: L) p ->
    wfkind L (KSubset k p)

with kinding : kctx -> cstr -> kind -> Prop :=
| KdVar L x k :
    nth_error L x = Some k ->
    kinding L (CVar x) k
| KdConst L cn :
    kinding L (CConst cn) (const_kind cn)
| KdBinOp L opr c1 c2 :
    kinding L c1 (cbinop_arg1_kind opr) ->
    kinding L c2 (cbinop_arg2_kind opr) ->
    kinding L (CBinOp opr c1 c2) (cbinop_result_kind opr)
| KdIte L c c1 c2 k :
    kinding L c KBool ->
    kinding L c1 k ->
    kinding L c2 k ->
    kinding L (CIte c c1 c2) k
| KdArrow L t1 i t2 :
    kinding L t1 KType ->
    kinding L i KTime ->
    kinding L t2 KType ->
    kinding L (CArrow t1 i t2) KType
| KdAbs L c k1 k2 :
    wfkind L k1 ->
    kinding (k1 :: L) c k2 ->
    kinding L (CAbs c) (KArrow k1 k2)
| KdApp L c1 c2 k1 k2 :
    kinding L c1 (KArrow k1 k2) ->
    kinding L c2 k1 ->
    kinding L (CApp c1 c2) k2
| KdEq L c k k' :
    kinding L c k ->
    kdeq L k' k -> 
    kinding L c k'
| KdTimeAbs L i n :
    kinding (KNat :: L) i (KTimeFun n) ->
    monotone i ->
    kinding L (CTimeAbs i) (KTimeFun (1 + n))
| KdQuan L quan k c :
    wfkind L k ->
    kinding (k :: L) c KType ->
    kinding L (CQuan quan k c) KType
| KdRec L c k :
    wfkind L k ->
    kinding (k :: L) c k ->
    kinding L (CRec c) k
| KdRef L t :
    kinding L t KType ->
    kinding L (CRef t) KType
.

Inductive tyeq : kctx -> cstr -> cstr -> Prop :=
(* | TyEqRefl L t : *)
(*     tyeq L t t *)
| TyEqVar L x :
    tyeq L (CVar x) (CVar x)
| TyEqConst L cn :
    tyeq L (CConst cn) (CConst cn)
(* | TyEqUnOp L opr t t' : *)
(*     tyeq L t t' -> *)
(*     tyeq L (CUnOp opr t) (CUnOp opr t') *)
| TyEqBinOp L opr t1 t2 t1' t2' :
    tyeq L t1 t1' ->
    tyeq L t2 t2' ->
    tyeq L (CBinOp opr t1 t2) (CBinOp opr t1' t2')
| TyEqIte L t1 t2 t3 t1' t2' t3':
    tyeq L t1 t1' ->
    tyeq L t2 t2' ->
    tyeq L t3 t3' ->
    tyeq L (CIte t1 t2 t3) (CIte t1' t2' t3')
| TyEqArrow L t1 i t2 t1' i' t2':
    tyeq L t1 t1' ->
    interpP L (PEq i i') ->
    tyeq L t2 t2' ->
    tyeq L (CArrow t1 i t2) (CArrow t1' i' t2')
| TyEqApp L c1 c2 c1' c2' :
    tyeq L c1 c1' ->
    tyeq L c2 c2' ->
    tyeq L (CApp c1 c2) (CApp c1' c2')
| TyEqBeta L (* t *) t1 t2 t1' t2' t' :
    (* tyeq L t (CApp t1 t2) -> *)
    tyeq L t1 (CAbs t1') ->
    tyeq L t2 t2' ->
    tyeq L (subst0_c_c t2' t1') t' ->
    tyeq L (CApp t1 t2) t'
(* | TyEqBetaRev L t1 t2 t1' t2' t' : *)
(*     tyeq L t1 (CAbs t1') -> *)
(*     tyeq L t2 t2' -> *)
(*     tyeq L (subst0_c_c t2' t1') t' -> *)
(*     tyeq L t' (CApp t1 t2) *)
| TyEqBetaRev L t1 t2 t1' t2' t' :
    tyeq L (CAbs t1') t1 ->
    tyeq L t2' t2 ->
    tyeq L t' (subst0_c_c t2' t1') ->
    tyeq L t' (CApp t1 t2)
| TyEqQuan L quan k t k' t' :
    kdeq L k k' ->
    tyeq (k :: L) t t' ->
    tyeq L (CQuan quan k t) (CQuan quan k' t')
(* only do deep equality test of two CRec's where the kind is KType *)
| TyEqRec L t t' :
    tyeq (KType :: L) t t' ->
    tyeq L (CRec t) (CRec t')
| TyEqRef L t t' :
   tyeq L t t' ->
   tyeq L (CRef t) (CRef t')
(* the following rules are just here to satisfy reflexivity *)
| TyEqTimeAbs L i :
    tyeq L (CTimeAbs i) (CTimeAbs i)
(* don't do deep equality test of two CAbs's *)
| TyEqAbs L t :
    tyeq L (CAbs t) (CAbs t)
.

Section tyeq_hint.
  
  Local Hint Constructors tyeq.

  Lemma tyeq_refl : forall t L, tyeq L t t.
  Proof.
    induct t; eauto using interpP_eq_refl, kdeq_refl.
  Qed.

  Lemma kdeq_tyeq L k k' t t' :
    kdeq L k k' ->
    tyeq (k :: L) t t' ->
    tyeq (k' :: L) t t'.
  Admitted.

  Lemma tyeq_sym L t1 t2 : tyeq L t1 t2 -> tyeq L t2 t1.
  Proof.
    induct 1; eauto using interpP_eq_sym, kdeq_sym.
    {
      econstructor; eauto using interpP_eq_sym, kdeq_sym.
      eapply kdeq_tyeq; eauto using kdeq_trans, kdeq_sym.
    }
  Qed.

  Lemma tyeq_trans' L a b :
    tyeq L a b ->
    forall c,
      tyeq L b c ->
      tyeq L a c.
  Proof.
    induct 1; try solve [intros c Hbc; invert Hbc; eauto 3 using interpP_eq_trans, tyeq_refl].
    (* induct 1; try solve [induct 1; eauto using interpP_eq_trans, tyeq_refl]. *)
    {
      induct 1; eauto using interpP_eq_trans, tyeq_refl.
    }
    {
      induct 1; eauto using interpP_eq_trans, tyeq_refl.
    }
    {
      induct 1; eauto using interpP_eq_trans, tyeq_refl.
    }
    {
      induct 1; eauto using interpP_eq_trans, tyeq_refl.
    }
    {
      induct 1; eauto using interpP_eq_trans, tyeq_refl.
    }
    {
      rename t' into a.
      induct 1.
      {
        eauto using interpP_eq_trans, tyeq_refl.
      }
      {
        rename t' into c.
        copy H2_ HH.
        eapply IHtyeq1 in HH.
        invert HH.
        copy H2_0 HH2.
        eapply IHtyeq2 in HH2.
        admit.
        (* may need logical relation here *)
        
        (* eapply IHtyeq3. *)
        (* Lemma subst0_c_c_tyeq : *)
        (*   forall t1 L t2 t2' t, *)
        (*     tyeq L t2' t2 -> *)
        (*     tyeq L (subst0_c_c t2 t1) t -> *)
        (*     tyeq L (subst0_c_c t2' t1) t. *)
        (* Admitted. *)
        (* eapply subst0_c_c_tyeq; eauto. *)
        (* admit. *)
      }
      {
        eauto using interpP_eq_trans, tyeq_refl.
      }
    }
    {
      induct 1; eauto using interpP_eq_trans, tyeq_refl.
      econstructor; eauto using kdeq_trans.
      eapply IHtyeq.
      eapply kdeq_tyeq; eauto using kdeq_trans, kdeq_sym.
    }
    {
      induct 1; eauto using interpP_eq_trans, tyeq_refl.
    }
    {
      induct 1; eauto using interpP_eq_trans, tyeq_refl.
    }
    (* intros c Hbc. *)
    (* invert Hbc. *)
    (* econstructor; eauto using kdeq_trans. *)
    (* eapply IHtyeq. *)
    (* eapply kdeq_tyeq; eauto using kdeq_trans, kdeq_sym. *)
    (* induct 1; eauto using interpP_eq_trans, tyeq_refl, kdeq_tyeq, kdeq_trans, kdeq_sym. *)
    
    (* solve [invert Hbc; eauto 4 using interpP_eq_trans, tyeq_refl]. *)
    (* induct 1; intros c Hbc; try solve [invert Hbc; eauto 4]. *)
    (* induct 1; intros c Hbc; try solve [invert Hbc; eauto using tyeq_refl]. *)
    (* induct 1; intros c Hbc; try solve [invert Hbc; eauto using interpP_eq_trans, tyeq_refl]. *)
    (* { *)
    (*   invert Hbc. *)
    (*   econstructor; eauto using kdeq_trans. *)
    (*   eapply IHtyeq. *)
    (*   eapply kdeq_tyeq; eauto using kdeq_trans, kdeq_sym. *)
    (* } *)
  Admitted.

  Lemma tyeq_trans L a b c :
    tyeq L a b ->
    tyeq L b c ->
    tyeq L a c.
  Proof.
    intros; eapply tyeq_trans'; eauto.
  Qed.

  Lemma CForall_CArrow_false k t t1 i t2 :
    tyeq [] (CForall k t) (CArrow t1 i t2) ->
    False.
  Proof.
    invert 1.
  Qed.

  Lemma invert_tyeq_CArrow L t1 i t2 t1' i' t2' :
    tyeq L (CArrow t1 i t2) (CArrow t1' i' t2') ->
    tyeq L t1 t1' /\
    interpP L (PEq i i') /\
    tyeq L t2 t2'.
  Proof.
    invert 1.
    repeat eexists_split; eauto.
  Qed.

  Lemma CExists_CArrow_false k t t1 i t2 :
    tyeq [] (CExists k t) (CArrow t1 i t2) ->
    False.
  Proof.
    invert 1.
  Qed.

  Lemma const_type_CArrow_false cn t1 i t2 :
    tyeq [] (const_type cn) (CArrow t1 i t2) ->
    False.
  Proof.
    cases cn; intros Htyeq; simplify;
      invert Htyeq.
  Qed.

  Lemma CProd_CArrow_false ta tb t1 i t2 :
    tyeq [] (CProd ta tb) (CArrow t1 i t2) ->
    False.
  Proof.
    invert 1.
  Qed.

  Lemma CSum_CArrow_false ta tb t1 i t2 :
    tyeq [] (CSum ta tb) (CArrow t1 i t2) ->
    False.
  Proof.
    invert 1.
  Qed.

  Lemma CRef_CArrow_false t t1 i t2 :
    tyeq [] (CRef t) (CArrow t1 i t2) ->
    False.
  Proof.
    invert 1.
  Qed.

  Lemma invert_tyeq_CExists L k1 t1 k2 t2 :
    tyeq L (CExists k1 t1) (CExists k2 t2) ->
    tyeq (k1 :: L) t1 t2 /\
    kdeq L k1 k2.
  Proof.
    invert 1.
    repeat eexists_split; eauto.
  Qed.

  Lemma invert_tyeq_CForall L k1 t1 k2 t2 :
    tyeq L (CForall k1 t1) (CForall k2 t2) ->
    tyeq (k1 :: L) t1 t2 /\
    kdeq L k1 k2.
  Proof.
    invert 1.
    repeat eexists_split; eauto.
  Qed.

  Lemma invert_tyeq_CRef L t t' :
    tyeq L (CRef t) (CRef t') ->
    tyeq L t t'.
  Proof.
    invert 1.
    repeat eexists_split; eauto.
  Qed.

  Lemma invert_tyeq_CProd L t1 t2 t1' t2' :
    tyeq L (CProd t1 t2) (CProd t1' t2') ->
    tyeq L t1 t1' /\
    tyeq L t2 t2'.
  Proof.
    invert 1.
    repeat eexists_split; eauto.
  Qed.

  Lemma invert_tyeq_CSum L t1 t2 t1' t2' :
    tyeq L (CSum t1 t2) (CSum t1' t2') ->
    tyeq L t1 t1' /\
    tyeq L t2 t2'.
  Proof.
    invert 1.
    repeat eexists_split; eauto.
  Qed.

End tyeq_hint.

(*
Inductive tyeq : kctx -> cstr -> cstr -> Prop :=
(* | TyEqRefl L t : *)
(*     tyeq L t t *)
| TyEqVar L x :
    tyeq L (CVar x) (CVar x)
| TyConst L cn :
    tyeq L (CConst cn) (CConst cn)
(* | TyEqUnOp L opr t t' : *)
(*     tyeq L t t' -> *)
(*     tyeq L (CUnOp opr t) (CUnOp opr t') *)
| TyEqBinOp L opr t1 t2 t1' t2' :
    tyeq L t1 t1' ->
    tyeq L t2 t2' ->
    tyeq L (CBinOp opr t1 t2) (CBinOp opr t1' t2')
| TyEqIte L t1 t2 t3 t1' t2' t3':
    tyeq L t1 t1' ->
    tyeq L t2 t2' ->
    tyeq L t3 t3' ->
    tyeq L (CIte t1 t2 t3) (CIte t1' t2' t3')
| TyEqArrow L t1 i t2 t1' i' t2':
    tyeq L t1 t1' ->
    interpP L (PEq i i') ->
    tyeq L t2 t2' ->
    tyeq L (CArrow t1 i t2) (CArrow t1' i' t2')
| TyEqApp L c1 c2 c1' c2' :
    tyeq L c1 c1' ->
    tyeq L c2 c2' ->
    tyeq L (CApp c1 c2) (CApp c1' c2')
| TyEqBeta L t1 t2  :
    tyeq L (CApp (CAbs t1) t2) (subst0_c_c t2 t1)
| TyEqBetaRev L t1 t2  :
    tyeq L (subst0_c_c t2 t1) (CApp (CAbs t1) t2)
| TyEqQuan L quan k t k' t' :
    kdeq L k k' ->
    tyeq (k :: L) t t' ->
    tyeq L (CQuan quan k t) (CQuan quan k' t')
(* only do deep equality test of two CRec's where the kind is KType *)
| TyEqRec L t t' :
    tyeq (KType :: L) t t' ->
    tyeq L (CRec t) (CRec t')
| TyEqRef L t t' :
   tyeq L t t' ->
   tyeq L (CRef t) (CRef t')
(* the following rules are just here to satisfy reflexivity *)
| TyEqTimeAbs L i :
    tyeq L (CTimeAbs i) (CTimeAbs i)
(* don't do deep equality test of two CAbs's *)
| TyEqAbs L t :
    tyeq L (CAbs t) (CAbs t)
| TyEqTrans L a b c :
    tyeq L a b ->
    tyeq L b c ->
    tyeq L a c
.

Hint Constructors tyeq.

Lemma tyeq_refl : forall t L, tyeq L t t.
Proof.
  induct t; eauto using interpP_eq_refl, kdeq_refl.
Qed.

Lemma kdeq_tyeq L k k' t t' :
  kdeq L k k' ->
  tyeq (k :: L) t t' ->
  tyeq (k' :: L) t t'.
Admitted.

Lemma tyeq_sym L t1 t2 : tyeq L t1 t2 -> tyeq L t2 t1.
Proof.
  induct 1; eauto using interpP_eq_sym, kdeq_sym.
  {
    econstructor; eauto using interpP_eq_sym, kdeq_sym.
    eapply kdeq_tyeq; eauto using kdeq_trans, kdeq_sym.
  }
Qed.

Lemma tyeq_trans L a b c :
  tyeq L a b ->
  tyeq L b c ->
  tyeq L a c.
Proof.
  intros; eauto.
Qed.

Lemma invert_tyeq_Arrow L ta tb : 
  tyeq L ta tb ->
  forall t1 i t2,
    tyeq L ta (CArrow t1 i t2) ->
    (exists t1' i' t2' ,
        tb = CArrow t1' i' t2' /\
        tyeq L t1 t1' /\
        interpP L (PEq i i') /\
        tyeq L t2 t2') \/
    (exists t1' t2' ,
        tb = CApp t1' t2').
Proof.
  induct 1; eauto.
  intros.
  invert H.
  {
    left; repeat eexists_split; eauto.
  }

Lemma invert_tyeq_Arrow L t1 i t2 tb : 
    tyeq L (CArrow t1 i t2) tb ->
      (exists t1' i' t2' ,
          tb = CArrow t1' i' t2' /\
          tyeq L t1 t1' /\
          interpP L (PEq i i') /\
          tyeq L t2 t2') \/
      (exists t1' t2' ,
          tb = CApp t1' t2').
Proof.
  induct 1; eauto.
  {
    left; repeat eexists_split; eauto.
  }
  {
    specialize (Hcneq (CAbs t0) t3).
    propositional.
  }
  induct 1; eauto.
  {
    repeat eexists_split; eauto.
  }
  {
    specialize (Hcneq (CAbs t0) t3).
    propositional.
  }
  eapply IHtyeq2; eauto using tyeq_sym.
  intros Htyeq.
  invert Htyeq.

Qed.

Lemma invert_tyeq_Arrow L t1 i t2 tb : 
  tyeq L (CArrow t1 i t2) tb ->
  (forall t1' t2' ,
      tb <> CApp t1' t2') ->
  (exists t1' i' t2' ,
      tb = CArrow t1' i' t2' /\
      tyeq L t1 t1' /\
      interpP L (PEq i i') /\
      tyeq L t2 t2').
Proof.
  induct 1; eauto; intros Hcneq.
  {
    repeat eexists_split; eauto.
  }
  {
    specialize (Hcneq (CAbs t0) t3).
    propositional.
  }
  admit.
  eapply IHtyeq2; eauto using tyeq_sym.
  intros Htyeq.
  invert Htyeq.
Qed.

Lemma CForall_CArrow_false' L ta tb : 
    tyeq L ta tb ->
    forall k t t1 i t2,
      tyeq L ta (CForall k t) ->
      tyeq L tb (CArrow t1 i t2) ->
      False.
Proof.
  induct 1; eauto.
  eapply IHtyeq2; eauto using tyeq_sym.
  intros Htyeq.
  invert Htyeq.
Qed.

Lemma CForall_CArrow_false' L k t t1 i t2 : 
    tyeq L (CForall k t) (CArrow t1 i t2) ->
    False.
Proof.
  induct 1.
Qed.
  
Lemma invert_tyeq_CArrow L t1 i t2 t1' i' t2' :
  tyeq L (CArrow t1 i t2) (CArrow t1' i' t2') ->
  tyeq L t1 t1' /\
  interpP L (PEq i i') /\
  tyeq L t2 t2'.
Admitted.
 *)

Hint Resolve tyeq_refl tyeq_sym tyeq_trans interpP_le_refl interpP_le_trans : invert_typing.

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
    value v ->
    value (EPack c v)
| VFold v :
    value v ->
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
| TyApp C e1 e2 t i1 i2 i t2 :
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
    tyeq (get_kctx C) t1 t2 ->
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

Definition fuel := time_type.

Definition config := (heap * expr * fuel)%type.

(* Require Import Reals. *)

(* Local Open Scope R_scope. *)

(* Local Open Scope time_scope. *)

Import OpenScope.

Inductive astep : config -> config -> Prop :=
| ABeta h e v t :
    value v ->
    1 <= t ->
    astep (h, EApp (EAbs e) v, t) (h, subst0_e_e v e, t - 1)
| AUnfoldFold h v t :
    value v ->
    astep (h, EUnfold (EFold v), t) (h, v, t)
| ARec h e t :
    astep (h, ERec e, t) (h, subst0_e_e (ERec e) e, t)
| AUnpackPack h c v e t :
    value v ->
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
| ABetaC h e c t :
    astep (h, EAppC (EAbsC e) c, t) (h, subst0_c_e c e, t)
| AProj h pr v1 v2 t :
    value v1 ->
    value v2 ->
    astep (h, EProj pr (EPair v1 v2), t) (h, proj (v1, v2) pr, t)
| AMatch h inj v e1 e2 t :
    value v ->
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
  (forall l t,
      W $? l = Some t ->
      exists v,
        h $? l = Some v /\
        value v /\
        typing ([], W, []) v t T0) /\
  (exists l, forall l', l' >= l -> h $? l = None).

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
  finished s \/
  exists s', step s s'.

Definition safe s := forall s', step^* s s' -> unstuck s'.

(* Local Close Scope time_scope. *)

Import CloseScope.

Arguments get_kctx _ / .
Arguments get_hctx _ / .

Hint Constructors step astep plug value.

Lemma nth_error_nil A n : @nth_error A [] n = None.
Admitted.

Arguments finished / .
Arguments get_expr / .

Lemma CApps_CRec_CArrow_false cs t3 t1 i t2 :
  tyeq [] (CApps (CRec t3) cs) (CArrow t1 i t2) ->
  False.
Proof.
  (* Lemma CArrow_CApps_false cs : *)
  (*   forall t1 i t2 t3, *)
  (*     CArrow t1 i t2 = CApps t3 cs -> *)
  (*     (forall t1' i' t2', t3 <> CArrow t1' i' t2') ->  *)
  (*     False. *)
  (* Proof. *)
  (*   induction cs; simpl; subst; try discriminate; intuition eauto. *)
  (*   eapply IHcs; eauto. *)
  (*   intros; discriminate. *)
  (* Qed. *)
  (* intros; eapply CArrow_CApps_false; eauto. *)
  (* intros; discriminate. *)
Admitted.

Lemma CApps_CRec_CForall_false cs t3 k t  :
  tyeq [] (CApps (CRec t3) cs) (CForall k t) ->
  False.
Proof.
Admitted.

Lemma CApps_CRec_CExists_false cs t3 k t  :
  tyeq [] (CApps (CRec t3) cs) (CExists k t) ->
  False.
Proof.
Admitted.

Lemma CApps_CRec_const_type_false cs t3 cn  :
  tyeq [] (CApps (CRec t3) cs) (const_type cn) ->
  False.
Proof.
Admitted.

Lemma CApps_CRec_CProd_false cs t3 t1 t2  :
  tyeq [] (CApps (CRec t3) cs) (CProd t1 t2) ->
  False.
Proof.
Admitted.

Lemma CApps_CRec_CSum_false cs t3 t1 t2  :
  tyeq [] (CApps (CRec t3) cs) (CSum t1 t2) ->
  False.
Proof.
Admitted.

Lemma CApps_CRec_CRef_false cs t3 t  :
  tyeq [] (CApps (CRec t3) cs) (CRef t) ->
  False.
Proof.
Admitted.

Lemma invert_tyeq_CApps t cs t' cs' :
  tyeq [] (CApps (CRec t) cs) (CApps (CRec t') cs') ->
  exists ks ,
    tyeq ks t t' /\
    Forall2 (tyeq []) cs cs'.
Admitted.

Lemma canon_CArrow' C v t i :
  typing C v t i ->
  get_kctx C = [] ->
  get_tctx C = [] ->
  forall t1 i' t2 ,
    tyeq [] t (CArrow t1 i' t2) ->
    value v ->
    exists e,
      v = EAbs e.
Proof.
  induct 1; intros Hknil Htnil ta i' tb Htyeq Hval; try solve [invert Hval | eexists; eauto]; subst.
  {
    rewrite Htnil in H.
    rewrite nth_error_nil in H.
    invert H.
  }
  {
    eapply CForall_CArrow_false in Htyeq; propositional.
  }
  {
    eapply CApps_CRec_CArrow_false in Htyeq; propositional.
  }
  {
    destruct C as ((L & W) & G); simplify; subst.
    eapply IHtyping; eauto with invert_typing.
  }
  {
    eapply CExists_CArrow_false in Htyeq; propositional.
  }
  {
    eapply const_type_CArrow_false in Htyeq; propositional.
  }
  {
    eapply CProd_CArrow_false in Htyeq; propositional.
  }
  {
    cases inj; simplify; eapply CSum_CArrow_false in Htyeq; propositional.
  }
  {
    eapply CRef_CArrow_false in Htyeq; propositional.
  }
Qed.

Lemma canon_CArrow W v t1 i' t2 i :
  typing ([], W, []) v (CArrow t1 i' t2) i ->
  value v ->
  exists e,
    v = EAbs e.
Proof.
  intros; eapply canon_CArrow'; eauto with invert_typing.
Qed.

Lemma canon_CForall' C v t i :
  typing C v t i ->
  get_kctx C = [] ->
  get_tctx C = [] ->
  forall k t' ,
    tyeq [] t (CForall k t') ->
    value v ->
    exists e,
      v = EAbsC e.
Proof.
  induct 1; intros Hknil Htnil k' t'' Htyeq Hval; try solve [invert Hval | eexists; eauto | invert Htyeq]; subst.
  {
    rewrite Htnil in H.
    rewrite nth_error_nil in H.
    invert H.
  }
  {
    eapply CApps_CRec_CForall_false in Htyeq; propositional.
  }
  {
    destruct C as ((L & W) & G); simplify; subst.
    eapply IHtyping; eauto with invert_typing.
  }
  {
    cases cn; simplify; invert Htyeq.
  }
  {
    cases inj; simplify; invert Htyeq.
  }
Qed.

Lemma canon_CForall W v k t i :
  typing ([], W, []) v (CForall k t) i ->
  value v ->
  exists e,
    v = EAbsC e.
Proof.
  intros; eapply canon_CForall'; eauto with invert_typing.
Qed.

Lemma canon_CRec' C v t i :
  typing C v t i ->
  get_kctx C = [] ->
  get_tctx C = [] ->
  forall t' cs ,
    tyeq [] t (CApps (CRec t') cs) ->
    value v ->
    exists e,
      v = EFold e /\
      value e.
Proof.
  induct 1; intros Hknil Htnil t'' cs' Htyeq Hval; try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst.
  {
    rewrite Htnil in H.
    rewrite nth_error_nil in H.
    invert H.
  }
  {
    eapply tyeq_sym in Htyeq.
    eapply CApps_CRec_CArrow_false in Htyeq; propositional.
  }
  {
    eapply tyeq_sym in Htyeq.
    eapply CApps_CRec_CForall_false in Htyeq; propositional.
  }
  {
    destruct C as ((L & W) & G); simplify; subst.
    eapply IHtyping; eauto with invert_typing.
  }
  {
    eapply tyeq_sym in Htyeq.
    eapply CApps_CRec_CExists_false in Htyeq; propositional.
  }
  {
    eapply tyeq_sym in Htyeq.
    eapply CApps_CRec_const_type_false in Htyeq; propositional.
  }
  {
    eapply tyeq_sym in Htyeq.
    eapply CApps_CRec_CProd_false in Htyeq; propositional.
  }
  {
    eapply tyeq_sym in Htyeq.
    cases inj; simplify;
      eapply CApps_CRec_CSum_false in Htyeq; propositional.
  }
  {
    eapply tyeq_sym in Htyeq.
    eapply CApps_CRec_CRef_false in Htyeq; propositional.
  }
Qed.

Lemma canon_CRec W v t cs i :
  typing ([], W, []) v (CApps (CRec t) cs) i ->
  value v ->
  exists e,
    v = EFold e /\
    value e.
Proof.
  intros; eapply canon_CRec'; eauto with invert_typing.
Qed.

Lemma canon_CExists' C v t i :
  typing C v t i ->
  get_kctx C = [] ->
  get_tctx C = [] ->
  forall k t' ,
    tyeq [] t (CExists k t') ->
    value v ->
    exists c e,
      v = EPack c e /\
      value e.
Proof.
  induct 1; intros Hknil Htnil k' t'' Htyeq Hval; try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst.
  {
    rewrite Htnil in H.
    rewrite nth_error_nil in H.
    invert H.
  }
  {
    eapply CApps_CRec_CExists_false in Htyeq; propositional.
  }
  {
    destruct C as ((L & W) & G); simplify; subst.
    eapply IHtyping; eauto with invert_typing.
  }
  {
    cases cn; simplify; invert Htyeq.
  }
  {
    cases inj; simplify; invert Htyeq.
  }
Qed.

Lemma canon_CExists W v k t i :
  typing ([], W, []) v (CExists k t) i ->
  value v ->
  exists c e,
    v = EPack c e /\
    value e.
Proof.
  intros; eapply canon_CExists'; eauto with invert_typing.
Qed.

Lemma canon_CProd' C v t i :
  typing C v t i ->
  get_kctx C = [] ->
  get_tctx C = [] ->
  forall t1 t2 ,
    tyeq [] t (CProd t1 t2) ->
    value v ->
    exists v1 v2,
      v = EPair v1 v2 /\
      value v1 /\
      value v2.
Proof.
  induct 1; intros Hknil Htnil t1'' t2'' Htyeq Hval; try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst.
  {
    rewrite Htnil in H.
    rewrite nth_error_nil in H.
    invert H.
  }
  {
    eapply CApps_CRec_CProd_false in Htyeq; propositional.
  }
  {
    destruct C as ((L & W) & G); simplify; subst.
    eapply IHtyping; eauto with invert_typing.
  }
  {
    cases cn; simplify; invert Htyeq.
  }
  {
    cases inj; simplify; invert Htyeq.
  }
Qed.

Lemma canon_CProd W v t1 t2 i :
  typing ([], W, []) v (CProd t1 t2) i ->
  value v ->
  exists v1 v2,
    v = EPair v1 v2 /\
    value v1 /\
    value v2.
Proof.
  intros; eapply canon_CProd'; eauto with invert_typing.
Qed.

Lemma canon_CSum' C v t i :
  typing C v t i ->
  get_kctx C = [] ->
  get_tctx C = [] ->
  forall t1 t2 ,
    tyeq [] t (CSum t1 t2) ->
    value v ->
    exists inj v',
      v = EInj inj v' /\
      value v'.
Proof.
  induct 1; intros Hknil Htnil t1'' t2'' Htyeq Hval; try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst.
  {
    rewrite Htnil in H.
    rewrite nth_error_nil in H.
    invert H.
  }
  {
    eapply CApps_CRec_CSum_false in Htyeq; propositional.
  }
  {
    destruct C as ((L & W) & G); simplify; subst.
    eapply IHtyping; eauto with invert_typing.
  }
  {
    cases cn; simplify; invert Htyeq.
  }
Qed.
  
Lemma canon_CSum W v t1 t2 i :
  typing ([], W, []) v (CSum t1 t2) i ->
  value v ->
  exists inj v',
    v = EInj inj v' /\
    value v'.
Proof.
  intros; eapply canon_CSum'; eauto with invert_typing.
Qed.

Lemma canon_CRef' C v t i :
  typing C v t i ->
  get_kctx C = [] ->
  get_tctx C = [] ->
  forall t' ,
    tyeq [] t (CRef t') ->
    value v ->
    exists l t',
      v = ELoc l /\
      get_hctx C $? l = Some t'.
Proof.
  induct 1; intros Hknil Htnil t'' Htyeq Hval; try solve [invert Hval | eexists; eauto | invert Hval; eexists; eauto | invert Htyeq]; subst.
  {
    rewrite Htnil in H.
    rewrite nth_error_nil in H.
    invert H.
  }
  {
    eapply CApps_CRec_CRef_false in Htyeq; propositional.
  }
  {
    destruct C as ((L & W) & G); simplify; subst.
    eapply IHtyping; eauto with invert_typing.
  }
  {
    cases cn; simplify; invert Htyeq.
  }
  {
    cases inj; simplify; invert Htyeq.
  }
Qed.
  
Lemma canon_CRef W v t i :
  typing ([], W, []) v (CRef t) i ->
  value v ->
  exists l t',
    v = ELoc l /\
    W $? l = Some t'.
Proof.
  intros Hty ?; eapply canon_CRef' in Hty; eauto with invert_typing.
Qed.

Lemma htyping_fresh h W :
  htyping h W ->
  exists l, h $? l = None.
Admitted.
Lemma htyping_elim h W l v t :
  htyping h W ->
  h $? l = Some v ->
  W $? l = Some t ->
  value v /\
  typing ([], W, []) v t T0.
Admitted.
Lemma htyping_elim_exists h W l t :
  htyping h W ->
  W $? l = Some t ->
  exists v,
    h $? l = Some v /\
    value v /\
    typing ([], W, []) v t T0.
Admitted.

Lemma progress' C e t i :
  typing C e t i ->
  get_kctx C = [] ->
  get_tctx C = [] ->
  forall h f ,
    htyping h (get_hctx C) ->
    (interpTime i <= f)%time ->
    unstuck (h, e, f).
Proof.
  induct 1.
  {
    (* Case Var *)
    intros ? ? h f Hhty Hle.
    destruct C as ((L & W) & G).
    simplify.
    subst.
    rewrite nth_error_nil in H.
    invert H.
  }
  {
    (* Case App *)
    intros ? ? h f Hhty Hle.
    destruct C as ((L & W) & G).
    simplify.
    subst.
    assert (Hi1 : (interpTime i1 <= f)%time).
    {
      Lemma interpTime_distr a b : interpTime (a + b)%idx = (interpTime a + interpTime b)%time.
      Admitted.
      repeat rewrite interpTime_distr in Hle.
      Lemma Time_add_le_elim a b c :
        (a + b <= c -> a <= c /\ b <= c)%time.
      Admitted.
      repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
      eauto.
    }
    assert (Hi2 : (interpTime i2 <= f)%time).
    {
      repeat rewrite interpTime_distr in Hle.
      repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
      eauto.
    }
    eapply IHtyping1 in Hi1; eauto.
    cases Hi1; simplify.
    {
      eapply canon_CArrow in H1; eauto.
      destruct H1 as (e & ?).
      subst.
      eapply IHtyping2 in Hi2; eauto.
      cases Hi2; simplify.
      {
        right.
        exists (h, subst0_e_e e2 e, (f - 1)%time).
        econstructor; eauto.
        econstructor; eauto.
        Lemma interpTime_1 : interpTime T1 = 1%time.
        Admitted.
        repeat rewrite interpTime_distr in Hle.
        repeat rewrite interpTime_1 in Hle.
        repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
        eauto.
      }
      {
        destruct H1 as (((h' & e2') & f') & Hstep).
        invert Hstep.
        rename e' into e0'.
        right.
        exists (h', EApp (EAbs e) e2', f').
        eapply StepPlug with (E := ECBinOp2 _ (EAbs e) E); repeat econstructor; eauto.
      }
    }
    {
      destruct H1 as (((h' & e1') & f') & Hstep).
      invert Hstep.
      right.
      exists (h', EApp e1' e2, f').
      eapply StepPlug with (E := ECBinOp1 _ E e2); repeat econstructor; eauto.
    }
  }
  {
    (* Case Abs *)
    intros.
    left.
    simplify; eauto.
  }
  {
    (* Case AppC *)
    intros ? ? h f Hhty Hle.
    destruct C as ((L & W) & G).
    simplify.
    subst.
    eapply IHtyping in Hle; eauto.
    cases Hle; simplify.
    {
      eapply canon_CForall in H1; eauto.
      destruct H1 as (e1 & ?).
      subst.
      right.
      exists (h, subst0_c_e c e1, f).
      eapply StepPlug with (E := ECHole); try eapply PlugHole.
      eauto.
    }
    {
      destruct H1 as (((h' & e1') & f') & Hstep).
      invert Hstep.
      rename e' into e0'.
      rename e1' into e'.
      right.
      exists (h', EAppC e' c, f').
      eapply StepPlug with (E := ECUnOp _ E); repeat econstructor; eauto.
    }
  }
  {
    (* Case AbsC *)
    intros.
    left.
    simplify; eauto.
  }
  {
    (* Case Rec *)
    intros.
    right.
    exists (h, subst0_e_e (ERec e) e, f).
    eapply StepPlug with (E := ECHole); try eapply PlugHole.
    eauto.
  }
  {
    (* Case Fold *)
    intros ? ? h f Hhty Hle.
    destruct C as ((L & W) & G).
    simplify.
    subst.
    eapply IHtyping in Hle; eauto.
    cases Hle; simplify.
    {
      left.
      simplify; eauto.
    }
    {
      destruct H as (((h' & e1') & f') & Hstep).
      invert Hstep.
      rename e' into e0'.
      rename e1' into e'.
      right.
      exists (h', EFold e', f').
      eapply StepPlug with (E := ECUnOp _ E); repeat econstructor; eauto.
    }
  }
  {
    (* Case Unfold *)
    intros ? ? h f Hhty Hle.
    destruct C as ((L & W) & G).
    simplify.
    subst.
    eapply IHtyping in Hle; eauto.
    cases Hle; simplify.
    {
      eapply canon_CRec in H; eauto.
      destruct H as (e1 & ? & Hv).
      subst.
      right.
      exists (h, e1, f).
      eapply StepPlug with (E := ECHole); try eapply PlugHole.
      eauto.
    }
    {
      destruct H as (((h' & e1') & f') & Hstep).
      invert Hstep.
      rename e' into e0'.
      rename e1' into e'.
      right.
      exists (h', EUnfold e', f').
      eapply StepPlug with (E := ECUnOp _ E); repeat econstructor; eauto.
    }
  }
  {
    (* Case Sub *)
    intros ? ? h f Hhty Hle.
    destruct C as ((L & W) & G).
    simplify.
    subst.
    eapply IHtyping; eauto.
    Lemma interpP_le_interpTime a b :
      interpP [] (a <= b)%idx ->
      (interpTime a <= interpTime b)%time.
    Admitted.
    eapply interpP_le_interpTime in H1.
    Lemma Time_le_trans a b c :
      (a <= b -> b <= c -> a <= c)%time.
    Admitted.
    Hint Resolve Time_le_trans : time_order.
    eauto with time_order.
  }
  {
    (* Case Pack *)
    intros ? ? h f Hhty Hle.
    destruct C as ((L & W) & G).
    simplify.
    subst.
    eapply IHtyping in Hle; eauto.
    cases Hle; simplify.
    {
      left.
      simplify; eauto.
    }
    {
      destruct H2 as (((h' & e1') & f') & Hstep).
      invert Hstep.
      rename e' into e0'.
      rename e1' into e'.
      right.
      exists (h', EPack c e', f').
      eapply StepPlug with (E := ECUnOp _ E); repeat econstructor; eauto.
    }
  }
  {
    (* Case Unpack *)
    intros ? ? h f Hhty Hle.
    destruct C as ((L & W) & G).
    simplify.
    subst.
    assert (Hi1 : (interpTime i1 <= f)%time).
    {
      repeat rewrite interpTime_distr in Hle.
      repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
      eauto.
    }
    eapply IHtyping1 in Hi1; eauto.
    cases Hi1; simplify.
    {
      eapply canon_CExists in H3; eauto.
      destruct H3 as (c & e & ? & Hv).
      subst.
      right.
      exists (h, subst0_e_e e (subst0_c_e c e2), f).
      eapply StepPlug with (E := ECHole); try eapply PlugHole.
      eauto.
    }
    {
      destruct H3 as (((h' & e1') & f') & Hstep).
      invert Hstep.
      right.
      exists (h', EUnpack e1' e2, f').
      eapply StepPlug with (E := ECUnpack E e2); repeat econstructor; eauto.
    }
  }
  {
    (* Case Const *)
    intros.
    left.
    simplify; eauto.
  }
  {
    (* Case Pair *)
    intros ? ? h f Hhty Hle.
    destruct C as ((L & W) & G).
    simplify.
    subst.
    assert (Hi1 : (interpTime i1 <= f)%time).
    {
      repeat rewrite interpTime_distr in Hle.
      repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
      eauto.
    }
    assert (Hi2 : (interpTime i2 <= f)%time).
    {
      repeat rewrite interpTime_distr in Hle.
      repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
      eauto.
    }
    eapply IHtyping1 in Hi1; eauto.
    cases Hi1; simplify.
    {
      eapply IHtyping2 in Hi2; eauto.
      cases Hi2; simplify.
      {
        left.
        simplify; eauto.
      }
      {
        destruct H2 as (((h' & e2') & f') & Hstep).
        invert Hstep.
        right.
        exists (h', EPair e1 e2', f').
        eapply StepPlug with (E := ECBinOp2 _ e1 E); repeat econstructor; eauto.
      }
    }
    {
      destruct H1 as (((h' & e1') & f') & Hstep).
      invert Hstep.
      right.
      exists (h', EPair e1' e2, f').
      eapply StepPlug with (E := ECBinOp1 _ E e2); repeat econstructor; eauto.
    }
  }
  {
    (* Case Proj *)
    intros ? ? h f Hhty Hle.
    destruct C as ((L & W) & G).
    simplify.
    subst.
    eapply IHtyping in Hle; eauto.
    destruct Hle as [He | He]; simplify.
    {
      eapply canon_CProd in He; eauto.
      destruct He as (v1 & v2 & ? & Hv1 & Hv2).
      subst.
      right.
      exists (h, proj (v1, v2) pr, f).
      eapply StepPlug with (E := ECHole); try eapply PlugHole.
      eauto.
    }
    {
      destruct He as (((h' & e') & f') & Hstep).
      invert Hstep.
      rename e'0 into e0'.
      right.
      exists (h', EProj pr e', f').
      eapply StepPlug with (E := ECUnOp _ E); repeat econstructor; eauto.
    }
  }
  {
    (* Case Inj *)
    intros ? ? h f Hhty Hle.
    destruct C as ((L & W) & G).
    simplify.
    subst.
    eapply IHtyping in Hle; eauto.
    destruct Hle as [He | He]; simplify.
    {
      left.
      simplify; eauto.
    }
    {
      destruct He as (((h' & e') & f') & Hstep).
      invert Hstep.
      rename e'0 into e0'.
      right.
      exists (h', EInj inj e', f').
      eapply StepPlug with (E := ECUnOp _ E); repeat econstructor; eauto.
    }
  }
  {
    (* Case Case *)
    intros ? ? h f Hhty Hle.
    destruct C as ((L & W) & G).
    simplify.
    subst.
    assert (Hile : (interpTime i <= f)%time).
    {
      repeat rewrite interpTime_distr in Hle.
      repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
      eauto.
    }
    eapply IHtyping1 in Hile; eauto.
    destruct Hile as [He | He]; simplify.
    {
      eapply canon_CSum in He; eauto.
      destruct He as (inj & v & ? & Hv).
      subst.
      right.
      exists (h, subst0_e_e v (choose (e1, e2) inj), f).
      eapply StepPlug with (E := ECHole); try eapply PlugHole.
      eauto.
    }
    {
      destruct He as (((h' & e') & f') & Hstep).
      invert Hstep.
      rename e3 into e0.
      rename e'0 into e0'.
      right.
      exists (h', ECase e' e1 e2, f').
      eapply StepPlug with (E := ECCase E e1 e2); repeat econstructor; eauto.
    }
  }
  {
    (* Case New *)
    intros ? ? h f Hhty Hle.
    destruct C as ((L & W) & G).
    simplify.
    subst.
    eapply IHtyping in Hle; eauto.
    destruct Hle as [He | He]; simplify.
    {
      right.
      eapply htyping_fresh in Hhty.
      destruct Hhty as (l & Hl).
      exists (h $+ (l, e), ELoc l, f).
      eapply StepPlug with (E := ECHole); try eapply PlugHole.
      eauto.
    }
    {
      destruct He as (((h' & e') & f') & Hstep).
      invert Hstep.
      rename e'0 into e0'.
      right.
      exists (h', ENew e', f').
      eapply StepPlug with (E := ECUnOp _ E); repeat econstructor; eauto.
    }
  }
  {
    (* Case Read *)
    intros ? ? h f Hhty Hle.
    destruct C as ((L & W) & G).
    simplify.
    subst.
    eapply IHtyping in Hle; eauto.
    destruct Hle as [He | He]; simplify.
    {
      eapply canon_CRef in He; eauto.
      destruct He as (l & t' & ? & Hl).
      subst.
      eapply htyping_elim_exists in Hl; eauto.
      destruct Hl as (v & Hl & Hv & Hty).
      right.
      exists (h, v, f).
      eapply StepPlug with (E := ECHole); try eapply PlugHole.
      eauto.
    }
    {
      destruct He as (((h' & e') & f') & Hstep).
      invert Hstep.
      rename e'0 into e0'.
      right.
      exists (h', ERead e', f').
      eapply StepPlug with (E := ECUnOp _ E); repeat econstructor; eauto.
    }
  }
  {
    (* Case Write *)
    intros ? ? h f Hhty Hle.
    destruct C as ((L & W) & G).
    simplify.
    subst.
    assert (Hi1 : (interpTime i1 <= f)%time).
    {
      repeat rewrite interpTime_distr in Hle.
      repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
      eauto.
    }
    assert (Hi2 : (interpTime i2 <= f)%time).
    {
      repeat rewrite interpTime_distr in Hle.
      repeat (eapply Time_add_le_elim in Hle; destruct Hle as (Hle & ?)).
      eauto.
    }
    eapply IHtyping1 in Hi1; eauto.
    destruct Hi1 as [He1 | He1]; simplify.
    {
      eapply IHtyping2 in Hi2; eauto.
      destruct Hi2 as [He2 | He2]; simplify.
      {
        eapply canon_CRef in He1; eauto.
        destruct He1 as (l & t' & ? & Hl).
        subst.
        eapply htyping_elim_exists in Hl; eauto.
        destruct Hl as (v & Hl & Hv & Hty).
        right.
        exists (h $+ (l, e2), ETT, f).
        eapply StepPlug with (E := ECHole); try eapply PlugHole.
        eauto.
      }
      {
        destruct He2 as (((h' & e2') & f') & Hstep).
        invert Hstep.
        right.
        exists (h', EWrite e1 e2', f').
        eapply StepPlug with (E := ECBinOp2 _ e1 E); repeat econstructor; eauto.
      }
    }
    {
      destruct He1 as (((h' & e1') & f') & Hstep).
      invert Hstep.
      right.
      exists (h', EWrite e1' e2, f').
      eapply StepPlug with (E := ECBinOp1 _ E e2); repeat econstructor; eauto.
    }
  }
  {
    (* Case Loc *)
    intros.
    left.
    simplify; eauto.
  }
Qed.

Lemma progress W s t i :
  ctyping W s t i ->
  unstuck s.
Proof.
  unfold ctyping in *.
  simplify.
  destruct s as ((h & e) & f).
  propositional.
  eapply progress'; eauto.
Qed.

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

Lemma TyEq C e t2 i t1 :
  typing C e t1 i ->
  tyeq (get_kctx C) t1 t2 ->
  typing C e t2 i.
Proof.
  intros.
  eapply TySub; eauto.
  admit. (* interpP (get_kctx C) (i <= i)%idx *)
Admitted.

Lemma TyLe C e t i1 i2 :
  typing C e t i1 ->
  interpP (get_kctx C) (i1 <= i2)%idx ->
  typing C e t i2.
Admitted.
Lemma TyETT C : typing C ETT CTypeUnit T0.
Proof.
  eapply TyConst.
Qed.

Ltac openhyp :=
  repeat match goal with
         | H : _ /\ _ |- _  => destruct H
         | H : _ \/ _ |- _ => destruct H
         | H : exists x, _ |- _ => destruct H
         | H : exists ! x, _ |- _ => destruct H
         | H : unique _ _ |- _ => destruct H
         end.

Lemma invert_typing_App C e1 e2 t i :
  typing C (EApp e1 e2) t i ->
  exists t' t2 i1 i2 i3 ,
    tyeq (get_kctx C) t t' /\
    typing C e1 (CArrow t2 i3 t') i1 /\
    typing C e2 t2 i2 /\
    interpP (get_kctx C) (i1 + i2 + T1 + i3 <= i)%idx.
Proof.
  induct 1; openhyp; repeat eexists_split;
    eauto;
    eauto with invert_typing.
Qed.  

Lemma invert_typing_Abs C e t i :
  typing C (EAbs e) t i ->
  exists t1 i' t2 ,
    tyeq (get_kctx C) t (CArrow t1 i' t2) /\
    kinding (get_kctx C) t1 KType /\
    typing (add_typing_ctx t1 C) e t2 i'.
Proof.
  induct 1; openhyp; repeat eexists_split; eauto; eauto with invert_typing.
Qed.  

Lemma invert_typing_Unfold C e t2 i :
  typing C (EUnfold e) t2 i ->
  exists t t1 cs i',
    tyeq (get_kctx C) t2 (CApps (subst0_c_c t t1) cs) /\
    t = CRec t1 /\
    typing C e (CApps t cs) i' /\
    interpP (get_kctx C) (i' <= i)%idx.
Proof.
  induct 1; openhyp; repeat eexists_split; eauto; eauto with invert_typing.
Qed.  

Lemma invert_typing_Fold C e t' i :
  typing C (EFold e) t' i ->
  exists t t1 cs t2 i',
    tyeq (get_kctx C) t' t /\
    t = CApps t1 cs /\
    t1 = CRec t2 /\
    kinding (get_kctx C) t KType /\
    typing C e (CApps (subst0_c_c t1 t2) cs) i' /\
    interpP (get_kctx C) (i' <= i)%idx.
Proof.
  induct 1; openhyp; repeat eexists_split; eauto; eauto with invert_typing.
Qed.  

Lemma kinding_tyeq L k t1 t2 :
  kinding L t1 k ->
  tyeq L t1 t2 ->
  kinding L t2 k.
Admitted.
Lemma add_typing_ctx_tyeq t1 t2 C e t i :
  typing (add_typing_ctx t1 C) e t i ->
  tyeq (get_kctx C) t1 t2 ->
  typing (add_typing_ctx t2 C) e t i.
Admitted.
Lemma get_kctx_add_typing_ctx t C : get_kctx (add_typing_ctx t C) = get_kctx C.
Admitted.

Lemma invert_typing_Rec C e t i :
  typing C (ERec e) t i ->
  exists n e1 ,
    e = EAbsCs n (EAbs e1) /\
    kinding (get_kctx C) t KType /\
    typing (add_typing_ctx t C) e t T0.
Proof.
  induct 1; openhyp; repeat eexists_split; eauto; eauto with invert_typing.
  {
    subst.
    eapply kinding_tyeq; eauto.
  }
  {
    subst.
    eapply add_typing_ctx_tyeq; eauto.
    eapply TyEq; eauto.
    rewrite get_kctx_add_typing_ctx.
    eauto.
  }
Qed.  

Lemma invert_typing_Unpack C e1 e2 t2'' i :
  typing C (EUnpack e1 e2) t2'' i ->
  exists t2' t i1 k t2 i2 i2' ,
    tyeq (get_kctx C) t2'' t2' /\
    typing C e1 (CExists k t) i1 /\
    typing (add_typing_ctx t (add_kinding_ctx k C)) e2 t2 i2 /\
    forget01_c_c t2 = Some t2' /\
    forget01_c_c i2 = Some i2' /\
    interpP (get_kctx C) (i1 + i2' <= i)%idx.
Proof.
  induct 1; openhyp; repeat eexists_split; eauto; eauto with invert_typing.
Qed.

Lemma invert_typing_Pack C c e t i :
  typing C (EPack c e) t i ->
  exists t1 k i' ,
    tyeq (get_kctx C) t (CExists k t1) /\
    kinding (get_kctx C) t1 (KArrow k KType) /\
    kinding (get_kctx C) c k /\
    typing C e (subst0_c_c c t1) i' /\
    interpP (get_kctx C) (i' <= i)%idx.
Proof.
  induct 1; openhyp; repeat eexists_split; eauto; eauto with invert_typing.
Qed.

Lemma invert_typing_Read C e t i :
  typing C (ERead e) t i ->
  exists i' ,
    typing C e (CRef t) i' /\
    interpP (get_kctx C) (i' <= i)%idx.
Proof.
  induct 1; openhyp; repeat eexists_split; eauto; eauto with invert_typing.
  eapply TySub; try eapply H2; try econstructor; eauto.
Qed.

Lemma invert_typing_Loc C l t i :
  typing C (ELoc l) t i ->
  exists t' ,
    tyeq (get_kctx C) t (CRef t') /\
    get_hctx C $? l = Some t'.
Proof.
  induct 1; openhyp; repeat eexists_split; eauto; eauto with invert_typing.
Qed.

Lemma invert_typing_Write C e1 e2 t i :
  typing C (EWrite e1 e2) t i ->
  exists t' i1 i2 ,
    tyeq (get_kctx C) t CTypeUnit /\
    typing C e1 (CRef t') i1 /\
    typing C e2 t' i2 /\
    interpP (get_kctx C) (i1 + i2 <= i)%idx.
Proof.
  induct 1; openhyp; repeat eexists_split; eauto; eauto with invert_typing.
Qed.

Lemma invert_typing_New C e t i :
  typing C (ENew e) t i ->
  exists t' i' ,
    tyeq (get_kctx C) t (CRef t') /\
    typing C e t' i' /\
    interpP (get_kctx C) (i' <= i)%idx.
Proof.
  induct 1; openhyp; repeat eexists_split; eauto; eauto with invert_typing.
Qed.

Lemma invert_typing_AppC C e c t i :
  typing C (EAppC e c) t i ->
  exists t' i' k ,
    tyeq (get_kctx C) t (subst0_c_c c t') /\
    typing C e (CForall k t') i' /\
    kinding (get_kctx C) c k /\
    interpP (get_kctx C) (i' <= i)%idx.
Proof.
  induct 1; openhyp; repeat eexists_split; eauto; eauto with invert_typing.
Qed.

Lemma invert_typing_AbsC C e t i :
  typing C (EAbsC e) t i ->
  exists t' k ,
    tyeq (get_kctx C) t (CForall k t') /\
    value e /\
    wfkind (get_kctx C) k /\
    typing (add_kinding_ctx k C) e t' T0.
Proof.
  induct 1; openhyp; repeat eexists_split; eauto; eauto with invert_typing.
Qed.

Lemma invert_typing_Proj C pr e t i :
  typing C (EProj pr e) t i ->
  exists t1 t2 i' ,
    tyeq (get_kctx C) t (proj (t1, t2) pr) /\
    typing C e (CProd t1 t2) i' /\
    interpP (get_kctx C) (i' <= i)%idx.
Proof.
  induct 1; openhyp; repeat eexists_split; eauto; eauto with invert_typing.
Qed.

Lemma invert_typing_Pair C e1 e2 t i :
  typing C (EPair e1 e2) t i ->
  exists t1 t2 i1 i2 ,
    tyeq (get_kctx C) t (CProd t1 t2) /\
    typing C e1 t1 i1 /\
    typing C e2 t2 i2 /\
    interpP (get_kctx C) (i1 + i2 <= i)%idx.
Proof.
  induct 1; openhyp; repeat eexists_split; eauto; eauto with invert_typing.
Qed.

Lemma invert_typing_Case C e e1 e2 t i :
  typing C (ECase e e1 e2) t i ->
  exists t1 t2 i0 i1 i2 ,
    typing C e (CSum t1 t2) i0 /\
    typing (add_typing_ctx t1 C) e1 t i1 /\
    typing (add_typing_ctx t2 C) e2 t i2 /\
    interpP (get_kctx C) (i0 + Tmax i1 i2 <= i)%idx.
Proof.
  induct 1; openhyp; repeat eexists_split; eauto; eauto with invert_typing.
  {
    eapply TyEq; eauto.
    rewrite get_kctx_add_typing_ctx.
    eauto.
  }
  {
    eapply TyEq; eauto.
    rewrite get_kctx_add_typing_ctx.
    eauto.
  }
Qed.

Lemma invert_typing_Inj C inj e t i :
  typing C (EInj inj e) t i ->
  exists t' t'' i' ,
    tyeq (get_kctx C) t (choose (CSum t' t'', CSum t'' t') inj) /\
    typing C e t' i' /\
    kinding (get_kctx C) t'' KType /\
    interpP (get_kctx C) (i' <= i)%idx.
Proof.
  induct 1; openhyp; repeat eexists_split; eauto; eauto with invert_typing.
Qed.

Lemma invert_typing_BinOpPrim C opr e1 e2 t i : typing C (EBinOp (EBPrim opr) e1 e2) t i -> False.
Proof.
  induct 1; openhyp; repeat eexists_split; eauto; eauto with invert_typing.
Qed.

Lemma fmap_map_subst0_shift01 k c W : fmap_map (K := k) (subst0_c_c c) (fmap_map shift01_c_c W) = W.
Admitted.
Lemma forget01_c_c_Some_subst0 c c' c'' :
  forget01_c_c c = Some c' ->
  subst0_c_c c'' c = c'.
Admitted.

Lemma ty_subst0_c_e k L W G e t i c :
  typing (k :: L, W, G) e t i ->
  kinding L c k ->
  typing (L, fmap_map (subst0_c_c c) W, map (subst0_c_c c) G) (subst0_c_e c e) (subst0_c_c c t) (subst0_c_c c i).
Admitted.

Lemma ty_subst0_e_e L W t G e1 t1 i1 e2 i2 :
  typing (L, W, t :: G) e1 t1 i1 ->
  typing (L, W, G) e2 t i2 ->
  typing (L, W, G) (subst0_e_e e2 e1) t1 (i1 + i2)%idx.
Admitted.

Lemma htyping_upd h W l t v i :
  htyping h W ->
  W $? l = Some t ->
  value v ->
  typing ([], W, []) v t i ->
  htyping (h $+ (l, v)) W.
Admitted.
Lemma htyping_new h W l t v i :
  htyping h W ->
  h $? l = None ->
  value v ->
  typing ([], W, []) v t i ->
  htyping (h $+ (l, v)) (W $+ (l, t)).
Admitted.

Lemma weaken_W L W G e t i W' :
  typing (L, W, G) e t i ->
  W $<= W' ->
  typing (L, W', G) e t i.
Admitted.

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
    (* Case Beta *)
    destruct H as (Hty & Hhty & Hle).
    rename t into f.
    rename t0 into t.
    eapply invert_typing_App in Hty.
    destruct Hty as (t' & t2 & i1 & i2 & i3 & Htyeq & Hty1 & Hty2 & Hle2).
    simplify.
    eapply invert_typing_Abs in Hty1.
    destruct Hty1 as (t1 & i' & t3 & Htyeq2 & Hkd & Hty1).
    simplify.
    eapply invert_tyeq_CArrow in Htyeq2.
    destruct Htyeq2 as (Htyeq2 & Hieq & Htyeq3).
    split.
    {
      Lemma xM_xM1' x : (1 <= x -> x - (x - 1) = 1)%time.
      Admitted.
      rewrite xM_xM1' by eauto.
      eapply interpP_le_interpTime in Hle2.
      repeat rewrite interpTime_distr in Hle2.
      repeat rewrite interpTime_1 in Hle2.
      repeat (eapply Time_add_le_elim in Hle2; destruct Hle2 as (Hle2 & ?)).
      eauto.
    }
    exists W.
    repeat try_split.
    {
      eapply TySub.
      {
        eapply ty_subst0_e_e with (G := []) in Hty1; eauto.
        eapply TyEq; eauto.
      }
      {
        simplify.
        eapply tyeq_sym.
        eapply tyeq_trans; eauto.
      }
      {
        Lemma interpTime_interpP_le a b :
          (interpTime a <= interpTime b)%time ->
          interpP [] (a <= b)%idx.
        Admitted.
        Lemma interpTime_minus_distr a b :
          interpTime (Tminus a b) = (interpTime a - interpTime b)%time.
        Admitted.
        Lemma Time_minus_move_left a b c :
          (c <= b ->
           a + c <= b ->
           a <= b - c)%time.
        Admitted.
        Lemma interpP_eq_interpTime a b :
          interpP [] (a == b)%idx -> interpTime a = interpTime b.
        Admitted.
        Lemma Time_add_assoc a b c : (a + (b + c) = a + b + c)%time.
        Admitted.
        Lemma lhs_rotate a b c :
          (b + a <= c ->
           a + b <= c)%time.
        Admitted.
        Lemma Time_add_cancel a b c :
          (a <= b ->
           a + c <= b + c)%time.
        Admitted.
        Lemma rhs_rotate a b c :
          (a <= c + b->
           a <= b + c)%time.
        Admitted.
        Ltac rotate_lhs := eapply lhs_rotate; repeat rewrite Time_add_assoc.
        Ltac rotate_rhs := eapply rhs_rotate; repeat rewrite Time_add_assoc.
        Ltac cancel := eapply Time_add_cancel.
        Lemma Time_a_le_ba a b : (a <= b + a)%time.
        Admitted.
        Ltac finish := eapply Time_a_le_ba.
        simplify.
        rewrite xM_xM1' by eauto.
        eapply interpP_le_interpTime in Hle2.
        repeat rewrite interpTime_distr in Hle2.
        repeat rewrite interpTime_1 in Hle2.
        copy Hle2 Hle2'.
        repeat (eapply Time_add_le_elim in Hle2; destruct Hle2 as (Hle2 & ?)).
        eapply interpTime_interpP_le.
        rewrite interpTime_distr.
        rewrite interpTime_minus_distr.
        rewrite interpTime_1.
        eapply Time_minus_move_left; eauto.
        eapply interpP_eq_interpTime in Hieq.
        rewrite <- Hieq in *.
        eapply Time_le_trans; [| eapply Hle2'].
        rotate_lhs.
        rotate_lhs.
        cancel.
        cancel.
        finish.
      }
    }
    {
      eapply Hhty.
    }
    {
      rewrite xM_xM1' by eauto.
      rewrite interpTime_minus_distr.
      rewrite interpTime_1.
      Lemma Time_minus_cancel a b c :
        (a <= b -> a - c <= b - c)%time.
      Admitted.
      eapply Time_minus_cancel.
      eauto.
    }
    {
      eapply includes_intro.
      eauto.
    }
  }
  {
    (* Case Unfold-Fold *)
    destruct H as (Hty & Hhty & Hle).
    rename t into f.
    rename t0 into t.
    eapply invert_typing_Unfold in Hty.
    destruct Hty as (t1 & t2& cs& i'& Htyeq & ? & Hty & Hle2).
    subst.
    simplify.
    subst.
    eapply invert_typing_Fold in Hty.
    destruct Hty as (? & ? & cs' & t2' & i'' & Htyeq2 & ? & ? & Hkd & Hty & Hle3).
    subst.
    simplify.
    eapply invert_tyeq_CApps in Htyeq2.
    destruct Htyeq2 as (ks & Htyeq2 & Htyeqcs).
    split.
    {
      Lemma Time_a_minus_a a : (a - a = 0)%time.
      Admitted.
      Lemma Time_0_le_x x : (0 <= x)%time.
      Admitted.
      rewrite Time_a_minus_a.
      eapply Time_0_le_x.
    }
    exists W.
    repeat try_split.
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
        Lemma interpTime_0 : interpTime T0 = 0%time.
        Admitted.
        Lemma Time_minus_0 x : (x - 0 = x)%time.
        Admitted.
        simplify.
        rewrite Time_a_minus_a.
        eapply interpTime_interpP_le.
        rewrite interpTime_minus_distr.
        rewrite interpTime_0.
        rewrite Time_minus_0.
        eapply interpP_le_interpTime in Hle2.
        eapply interpP_le_interpTime in Hle3.
        eauto with time_order.
      }
    }
    {
      eapply Hhty.
    }
    {
      simplify.
      rewrite Time_a_minus_a.
      rewrite interpTime_minus_distr.
      rewrite interpTime_0.
      rewrite Time_minus_0.
      eauto.
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
    generalize Hty; intro Hty0.
    eapply invert_typing_Rec in Hty.
    destruct Hty as (n & e1 & ? & Hkd & Hty).
    simplify.
    split.
    {
      rewrite Time_a_minus_a.
      eapply Time_0_le_x.
    }
    exists W.
    repeat try_split.
    {
      eapply ty_subst0_e_e with (G := []) in Hty; eauto.
      eapply TySub.
      {
        eapply Hty.
      }
      {
        eapply tyeq_refl.
      }
      {
        Lemma Time_0_add x : (0 + x = x)%time.
        Admitted.
        Lemma Time_le_refl x : (x <= x)%time.
        Admitted.
        Hint Resolve Time_le_refl : time_order.
        simplify.
        rewrite Time_a_minus_a.
        eapply interpTime_interpP_le.
        rewrite interpTime_minus_distr.
        rewrite interpTime_distr.
        rewrite interpTime_0.
        rewrite Time_minus_0.
        rewrite Time_0_add.
        eauto with time_order.
      }
    }
    {
      eapply Hhty.
    }
    {
      simplify.
      rewrite Time_a_minus_a.
      rewrite interpTime_minus_distr.
      rewrite interpTime_0.
      rewrite Time_minus_0.
      eauto.
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
    eapply invert_typing_Unpack in Hty.
    destruct Hty as (t2' & t0 & i1 & k & t2 & i2 & i2' & Htyeq & Hty1 & Hty2 & Ht2 & Hi2 & Hle2).
    subst.
    simplify.
    eapply invert_typing_Pack in Hty1.
    destruct Hty1 as (t1 & k' & i' & Htyeq2 & Hkd1 & Hkdc' & Htyv & Hle3).
    subst.
    simplify.
    eapply invert_tyeq_CExists in Htyeq2.
    destruct Htyeq2 as (Htyeq2 & Hkdeq).
    assert (Hkdc : kinding [] c k).
    {
      eapply KdEq; eauto.
    }
    eapply ty_subst0_c_e with (L := []) in Hty2; eauto.
    simplify.
    rewrite fmap_map_subst0_shift01 in Hty2.
    erewrite (@forget01_c_c_Some_subst0 t2) in Hty2; eauto.
    erewrite (@forget01_c_c_Some_subst0 i2) in Hty2; eauto.
    assert (Htyv' : typing ([], W, []) v (subst0_c_c c t0) i').
    {
      eapply TyEq; eauto.
      simplify.
      admit.
    }
    eapply ty_subst0_e_e with (G := []) in Hty2; eauto.
    split.
    {
      rewrite Time_a_minus_a.
      eapply Time_0_le_x.
    }
    exists W.
    repeat try_split.
    {
      eapply TySub.
      {
        eapply Hty2.
      }
      {
        (* tyeq *)
        simplify.
        eapply tyeq_sym; eauto.
      }
      {
        Ltac trans_rhs h := eapply Time_le_trans; [|eapply h].
        simplify.
        rewrite Time_a_minus_a.
        eapply interpTime_interpP_le.
        rewrite interpTime_minus_distr.
        rewrite interpTime_distr.
        rewrite interpTime_0.
        rewrite Time_minus_0.
        eapply interpP_le_interpTime in Hle2.
        eapply interpP_le_interpTime in Hle3.
        repeat rewrite interpTime_distr in Hle2.
        repeat rewrite interpTime_1 in Hle2.
        trans_rhs Hle2.
        rotate_lhs.
        cancel.
        eauto.
      }
    }
    {
      eapply Hhty.
    }
    {
      simplify.
      rewrite Time_a_minus_a.
      rewrite interpTime_minus_distr.
      rewrite interpTime_0.
      rewrite Time_minus_0.
      eauto.
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
    eapply invert_typing_Read in Hty.
    destruct Hty as (i' & Hty & Hle2).
    simplify.
    eapply invert_typing_Loc in Hty.
    destruct Hty as (t' & Htyeq & Hl).
    simplify.
    generalize Hhty; intro Hhty0.
    eapply htyping_elim in Hhty; eauto.
    destruct Hhty as (Hval & Htyv).
    eapply invert_tyeq_CRef in Htyeq.
    split.
    {
      rewrite Time_a_minus_a.
      eapply Time_0_le_x.
    }
    exists W.
    repeat try_split.
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
        Hint Resolve Time_0_le_x : time_order.
        simplify.
        rewrite Time_a_minus_a.
        eapply interpTime_interpP_le.
        rewrite interpTime_minus_distr.
        repeat rewrite interpTime_0.
        rewrite Time_minus_0.
        eauto with time_order.
      }
    }
    {
      eapply Hhty0.
    }
    {
      simplify.
      rewrite Time_a_minus_a.
      rewrite interpTime_minus_distr.
      repeat rewrite interpTime_0.
      rewrite Time_minus_0.
      eauto.
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
    eapply invert_typing_Write in Hty.
    destruct Hty as (t' & i1 & i2 & Htyeq & Hty1 & Hty2 & Hle2).
    eapply invert_typing_Loc in Hty1.
    destruct Hty1 as (t'' & Htyeq2 & Hl).
    simplify.
    eapply invert_tyeq_CRef in Htyeq2.
    copy Hhty Hhty0.
    eapply htyping_elim in Hhty; eauto.
    destruct Hhty as (Hval' & Htyv').
    split.
    {
      rewrite Time_a_minus_a.
      eauto with time_order.
    }
    exists W.
    repeat try_split.
    {
      eapply TySub.
      {
        eapply TyETT.
      }
      {
        simplify.
        eapply tyeq_sym; eauto.
      }
      {
        simplify.
        rewrite Time_a_minus_a.
        eapply interpTime_interpP_le.
        rewrite interpTime_minus_distr.
        repeat rewrite interpTime_0.
        rewrite Time_minus_0.
        eauto with time_order.
      }
    }
    {
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
      simplify.
      rewrite Time_a_minus_a.
      rewrite interpTime_minus_distr.
      repeat rewrite interpTime_0.
      rewrite Time_minus_0.
      eauto.
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
    eapply invert_typing_New in Hty.
    destruct Hty as (t' & i' & Htyeq & Hty & Hle2).
    simplify.
    split.
    {
      rewrite Time_a_minus_a.
      eauto with time_order.
    }
    exists (W $+ (l, t')).
    repeat try_split.
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
        rewrite Time_a_minus_a.
        eapply interpTime_interpP_le.
        rewrite interpTime_minus_distr.
        repeat rewrite interpTime_0.
        rewrite Time_minus_0.
        eauto with time_order.
      }
    }
    {
      eapply htyping_new in Hhty; eauto.
    }
    {
      simplify.
      rewrite Time_a_minus_a.
      rewrite interpTime_minus_distr.
      repeat rewrite interpTime_0.
      rewrite Time_minus_0.
      eauto.
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
    (* Case AppC *)
    destruct H as (Hty & Hhty & Hle).
    rename t into f.
    rename t0 into t.
    eapply invert_typing_AppC in Hty.
    destruct Hty as (t' & i' & k' & Htyeq & Hty & Hkdc & Hle2).
    simplify.
    eapply invert_typing_AbsC in Hty.
    destruct Hty as (t'' & k & Htyeq2 & Hval & Hwfk & Hty).
    simplify.
    eapply invert_tyeq_CForall in Htyeq2.
    destruct Htyeq2 as (Htyeq2 & Hkdeq).
    assert (Hkdck : kinding [] c k).
    {
      eapply KdEq; eauto.
      eapply kdeq_sym; eauto.
    }
    split.
    {
      rewrite Time_a_minus_a.
      eauto with time_order.
    }
    exists W.
    repeat try_split.
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
        Lemma subst0_c_c_Const v cn : subst0_c_c v (CConst cn) = CConst cn.
        Admitted.
        simplify.
        rewrite subst0_c_c_Const.
        rewrite Time_a_minus_a.
        eapply interpTime_interpP_le.
        rewrite interpTime_minus_distr.
        repeat rewrite interpTime_0.
        rewrite Time_minus_0.
        eauto with time_order.
      }
    }
    {
      eapply Hhty.
    }
    {
      simplify.
      rewrite Time_a_minus_a.
      rewrite interpTime_minus_distr.
      repeat rewrite interpTime_0.
      rewrite Time_minus_0.
      eauto.
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
    eapply invert_typing_Proj in Hty.
    destruct Hty as (t1 & t2 & i' & Htyeq & Hty & Hle2).
    simplify.
    eapply invert_typing_Pair in Hty.
    destruct Hty as (t1' & t2' & i1 & i2 & Htyeq2 & Hty1 & Hty2 & Hle3).
    simplify.
    eapply invert_tyeq_CProd in Htyeq2.
    destruct Htyeq2 as (Htyeq2 & Htyeq3).
    split.
    {
      rewrite Time_a_minus_a.
      eauto with time_order.
    }
    exists W.
    repeat try_split.
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
          rewrite Time_a_minus_a.
          eapply interpTime_interpP_le.
          rewrite interpTime_minus_distr.
          repeat rewrite interpTime_0.
          rewrite Time_minus_0.
          eapply interpP_le_interpTime in Hle2.
          eapply interpP_le_interpTime in Hle3.
          repeat rewrite interpTime_distr in Hle3.
          trans_rhs Hle2.
          trans_rhs Hle3.
          rotate_rhs.
          finish.
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
          rewrite Time_a_minus_a.
          eapply interpTime_interpP_le.
          rewrite interpTime_minus_distr.
          repeat rewrite interpTime_0.
          rewrite Time_minus_0.
          eapply interpP_le_interpTime in Hle2.
          eapply interpP_le_interpTime in Hle3.
          repeat rewrite interpTime_distr in Hle3.
          trans_rhs Hle2.
          trans_rhs Hle3.
          finish.
        }
      }
    }
    {
      eapply Hhty.
    }
    {
      simplify.
      rewrite Time_a_minus_a.
      rewrite interpTime_minus_distr.
      repeat rewrite interpTime_0.
      rewrite Time_minus_0.
      eauto.
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
    eapply invert_typing_Case in Hty.
    destruct Hty as (t1 & t2 & i0 & i1 & i2 & Hty0 & Hty1 & Hty2 & Hle2).
    simplify.
    eapply invert_typing_Inj in Hty0.
    destruct Hty0 as (t' & t'' & i' & Htyeq & Hty0 & Hkd & Hle3).
    simplify.
    split.
    {
      rewrite Time_a_minus_a.
      eauto with time_order.
    }
    exists W.
    repeat try_split.
    {
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
          Lemma Time_add_cancel2 a b c d :
            (c <= d ->
             a <= b ->
             a + c <= b + d)%time.
          Admitted.
          Ltac cancel2 := eapply Time_add_cancel2; [eauto with time_order | ..].
          Definition TimeMax : time_type -> time_type -> time_type.
          Admitted.
          Lemma interpTime_max a b : interpTime (Tmax a b) = TimeMax (interpTime a) (interpTime b).
          Admitted.
          Lemma Time_a_le_maxab a b : (a <= TimeMax a b)%time.
          Admitted.
          Lemma Time_b_le_maxab a b : (b <= TimeMax a b)%time.
          Admitted.
          Hint Resolve Time_a_le_maxab Time_b_le_maxab : time_order.
          simplify.
          rewrite Time_a_minus_a.
          eapply interpTime_interpP_le.
          rewrite interpTime_minus_distr.
          rewrite interpTime_distr.
          repeat rewrite interpTime_0.
          rewrite Time_minus_0.
          eapply interpP_le_interpTime in Hle2.
          trans_rhs Hle2.
          rewrite interpTime_distr.
          eapply interpP_le_interpTime in Hle3.
          rotate_rhs.
          cancel2.
          rewrite interpTime_max.
          eauto with time_order.
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
          rewrite Time_a_minus_a.
          eapply interpTime_interpP_le.
          rewrite interpTime_minus_distr.
          rewrite interpTime_distr.
          repeat rewrite interpTime_0.
          rewrite Time_minus_0.
          eapply interpP_le_interpTime in Hle2.
          trans_rhs Hle2.
          rewrite interpTime_distr.
          eapply interpP_le_interpTime in Hle3.
          rotate_rhs.
          cancel2.
          rewrite interpTime_max.
          eauto with time_order.
        }
      }
    }
    {
      eapply Hhty.
    }
    {
      simplify.
      rewrite Time_a_minus_a.
      rewrite interpTime_minus_distr.
      repeat rewrite interpTime_0.
      rewrite Time_minus_0.
      eauto.
    }
    {
      eapply includes_intro.
      eauto.
    }
  }
Admitted.

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
      eapply interpTime_interpP_le.
      eauto with time_order.
    }
    intros.
    invert H.
    eapply TyLe; eauto.
    simplify.
    eapply interpTime_interpP_le.
    rewrite interpTime_distr.
    rotate_rhs.
    finish.
  }
  {
    cases opr.
    {
      (* Case Proj *)
      eapply invert_typing_Proj in Hty.
      destruct Hty as (t1 & t2 & i' & Htyeq & Hty & Hle).
      simplify.
      eapply IHplug in Hty; eauto.
      destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        eapply interpTime_interpP_le.
        eapply interpP_le_interpTime in Hle.
        eapply interpP_le_interpTime in Hle2.
        eauto with time_order.
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
        eapply interpTime_interpP_le.
        repeat rewrite interpTime_distr.
        rotate_lhs.
        rotate_rhs.
        cancel.
        repeat rewrite interpTime_minus_distr.
        eapply Time_minus_cancel.
        eapply interpP_le_interpTime in Hle.
        eauto.
      }
    }
    {
      (* Case Inj *)
      eapply invert_typing_Inj in Hty.
      destruct Hty as (t1 & t2 & i' & Htyeq & Hty & Hkd & Hle).
      simplify.
      eapply IHplug in Hty; eauto.
      destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        eapply interpTime_interpP_le.
        eapply interpP_le_interpTime in Hle.
        eapply interpP_le_interpTime in Hle2.
        eauto with time_order.
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
          eapply interpTime_interpP_le.
          repeat rewrite interpTime_distr.
          rotate_lhs.
          rotate_rhs.
          cancel.
          repeat rewrite interpTime_minus_distr.
          eapply Time_minus_cancel.
          eapply interpP_le_interpTime in Hle.
          eauto.
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
          eapply interpTime_interpP_le.
          repeat rewrite interpTime_distr.
          rotate_lhs.
          rotate_rhs.
          cancel.
          repeat rewrite interpTime_minus_distr.
          eapply Time_minus_cancel.
          eapply interpP_le_interpTime in Hle.
          eauto.
        }
      }
    }
    {
      (* Case AppC *)
      eapply invert_typing_AppC in Hty.
      destruct Hty as (t' & i' & k & Htyeq & Hty & Hkd & Hle).
      simplify.
      eapply IHplug in Hty; eauto.
      destruct Hty as (t0 & i0 & Hty1 & Hle2 & HE).
      exists t0, i0.
      repeat split; eauto.
      {
        eapply interpTime_interpP_le.
        eapply interpP_le_interpTime in Hle.
        eapply interpP_le_interpTime in Hle2.
        eauto with time_order.
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
      eapply invert_typing_Pack in Hty.
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
      eapply invert_typing_Fold in Hty.
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
      eapply invert_typing_Unfold in Hty.
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
      eapply invert_typing_New in Hty.
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
      eapply invert_typing_Read in Hty.
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
      eapply invert_typing_BinOpPrim in Hty.
      destruct Hty.
    }
    {
      (* Case App *)
      eapply invert_typing_App in Hty.
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
        eapply weaken_W; eauto.
      }
      {
        eapply tyeq_sym; eauto.
      }
      {
        admit. (* interpP (get_kctx ([], W', [])) (i1' + Tminus i1 i0 + i2 + T1 + i3 <= i1' + Tminus i i0)%idx *)
      }
    }
    {
      (* Case Pair *)
      eapply invert_typing_Pair in Hty.
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
      eapply invert_typing_Write in Hty.
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
      eapply invert_typing_BinOpPrim in Hty.
      destruct Hty.
    }
    {
      (* Case App *)
      eapply invert_typing_App in Hty.
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
        admit. (* interpP (get_kctx ([], W', [])) (i1' + Tminus i2 i0 + i1 + T1 + i3 <= i1' + Tminus i i0)%idx *)
      }
    }
    {
      (* Case Pair *)
      eapply invert_typing_Pair in Hty.
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
      eapply invert_typing_Write in Hty.
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
    eapply invert_typing_Case in Hty.
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
    eapply invert_typing_Unpack in Hty.
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
    unfold ctyping; repeat try_split; eauto.
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
  repeat try_split; eauto.
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

End M.