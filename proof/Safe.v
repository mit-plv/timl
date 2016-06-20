Require Import Frap.

Set Implicit Arguments.

Definition var := nat.

Require Rdefinitions.
Module R := Rdefinitions.
Definition real := R.R.
Definition R0 := R.R0.
Definition R1 := R.R1.
(* Require RIneq. *)
(* Definition nnreal := RIneq.nonnegreal. *)
                     
Inductive cstr_const :=
| CCIdxTT
| CCIdxNat (n : nat)
| CCTime (r : real)
| CCTypeUnit
| CCTypeInt
.

Inductive cstr_un_op :=
.

Inductive cstr_bin_op :=
| CBTimeAdd
| CBTimeMax
| CBTypeProd
| CBTypeSum
.

Inductive quan :=
| QuanForall
| QuanExists
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
| CQuan (q : quan) (c : cstr)
| CRec (t : cstr)
| CRef (t : cstr)
.

Definition T0 := CConst (CCTime R0).
Definition T1 := CConst (CCTime R1).
Definition Tadd := CBinOp CBTimeAdd.
Infix "+" := Tadd : idx_scope.
Delimit Scope idx_scope with idx.

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

Inductive exp_const :=
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

Inductive exp_bin_op :=
| EBIntAdd
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

Inductive exp :=
| EVar (x : var)
| EConst (cn : exp_const)
| EBinOp (opr : exp_bin_op) (e1 e2 : exp)
| EPair (e1 e2 : exp)
| EProj (p : projector) (e : exp)
| ESumI (c : sum_cstr) (e : exp)
| ECase (e e1 e2 : exp)
| EAbs (e : exp)
| EApp (e1 e2 : exp)
| ERec (e : exp)
| EAbsC (e : exp)
| EAppC (e : exp) (c : cstr)
| EPack (c : cstr) (e : exp)
| EUnpack (e1 e2 : exp)
| EFold (e : exp)
| EUnfold (e : exp)
(* | EAsc (e : exp) (t : cstr) *)
(* | EAstTime (e : exp) (i : cstr) *)
| ENew (e : exp)
| ERead (e : exp)
| EWrite (e1 e2 : exp)
| ELoc (l : loc)
.

Definition EFst := EProj ProjFst.
Definition ESnd := EProj ProjSnd.
Definition EInl := ESumI SCInl.
Definition EInr := ESumI SCInr.

Definition kctx := list kind.
Definition hctx := fmap loc cstr.
Definition tctx := list cstr.
Definition ctx := (kctx * hctx * tctx)%type.

Definition shift_c_c (x : var) (n : nat) (b : cstr) : cstr.
  admit.
Defined.

Definition forget_c_c (x : var) (n : nat) (b : cstr) : option cstr.
  admit.
Defined.

Definition subst_c_c (x : var) (v : cstr) (b : cstr) : cstr.
  admit.
Defined.

Inductive value : exp -> Prop :=
.

Inductive wfkind : kctx -> kind -> Prop :=
.

Inductive kinding : kctx -> cstr -> kind -> Prop :=
.

Inductive tyeq : kctx -> cstr -> cstr -> Prop :=
.

Definition interpP : kctx -> prop -> Prop.
  admit.
Defined.

Definition fmap_map {K A B} (f : A -> B) (m : fmap K A) : fmap K B.
  admit.
Defined.

Definition add_kinding_ctx k (C : ctx) :=
  match C with
    (L, H, G) => (k :: L, fmap_map (shift_c_c 0 1) H, map (shift_c_c 0 1) G)
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

Local Open Scope idx_scope.

Inductive typing : ctx -> exp -> cstr -> cstr -> Prop :=
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
    typing C (EAppC e c) (subst_c_c 0 c t) i
| TyAbsC C e t k :
    value e ->
    wfkind (get_kctx C) k ->
    typing (add_kinding_ctx k C) e t T0 ->
    typing C (EAbsC e) (CAbs t) T0
| TyRec C e t n e1 :
    kinding (get_kctx C) t KType ->
    e = AbsCs_Abs n e1 ->
    typing (add_typing_ctx t C) e t T0 ->
    typing C (ERec e) t T0
| TyFold C e t i t1 cs t2 :
    t = CApps t1 cs ->
    t1 = CRec t2 ->
    kinding (get_kctx C) t KType ->
    typing C e (CApps (subst_c_c 0 t1 t2) cs) i ->
    typing C (EFold e) t i
| TyUnfold C e t t1 cs i :
    t = CRec t1 ->
    typing C e (CApps t cs) i ->
    typing C (EUnfold e) (CApps (subst_c_c 0 t t1) cs) i
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
    wfkind (get_kctx C) k -> 
    kinding (get_kctx C) t1 (KArrow k KType) ->
    kinding (get_kctx C) c k ->
    typing C e (subst_c_c 0 c t1) i ->
    typing C (EPack c e) t i
| TyUnpack C e1 e2 t2' i1 i2' t k t2 i2 :
    typing C e1 (CExists t) i1 ->
    kinding (get_kctx C) t (KArrow k KType) ->
    typing (add_typing_ctx t (add_kinding_ctx k C)) e2 t2 i2 ->
    forget_c_c 0 1 t2 = Some t2' ->
    forget_c_c 0 1 i2 = Some i2' ->
    typing C (EUnpack e1 e2) t2' (i1 + i2')
| TyConst C cn :
    typing C (EConst cn) (const_type cn) T0
| TyPair C e1 e2 t1 t2 i1 i2 :
    typing C e1 t1 i1 ->
    typing C e2 t2 i2 ->
    typing C (EPair e1 e2) (CProd t1 t2) (i1 + i2)
| TyFst C e t1 t2 i :
    typing C e (CProd t1 t2) i ->
    typing C (EFst e) t1 i
| TySnd C e t1 t2 i :
    typing C e (CProd t1 t2) i ->
    typing C (ESnd e) t2 i
| TyInl C e t t' i :
    typing C e t i ->
    kinding (get_kctx C) t' KType ->
    typing C (EInl e) (CSum t t') i
| TyInr C e t t' i :
    typing C e t i ->
    kinding (get_kctx C) t' KType ->
    typing C (EInr e) (CSum t' t) i
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
           