Require Import List.
Require Import Program.
Require Import Bedrock.Platform.Cito.GeneralTactics4.
Require Import Bedrock.Platform.Cito.ListFacts4.
Require Import TypingFacts.

Export Typing.

Import ListNotations.
Local Open Scope list_scope.

Definition Efixpoint tlhs t0 e := Eletrec [(tlhs, t0, e)] #0.

Arguments compose / . 
Arguments flip / . 

Lemma TPfixpoint T tlhs t0 e :
  typing (add_typing (tlhs, Some Stt) T) (Eabs t0 e) (shift tlhs) F0 Stt ->
  typing T (Efixpoint tlhs t0 e) tlhs F0 Stt.
Proof.
  intros H.
  eapply TPletrec.
  {
    intros until 0.
    intros Hin.
    eapply in_singleton_iff in Hin.
    inject Hin.
    simpl.
    eauto.
  }
  { eapply TPvar'; simpl; eauto. }
Qed.
