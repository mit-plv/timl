Ltac unfolder:= repeat match goal with
                        | H:= _ |- _ => unfold H in *; clear H
                      end.
Ltac rewriter :=
  repeat match goal with
           H : _ = _ |- _ => rewrite H
         end.

Ltac rewriter_r :=
  repeat match goal with
           H : _ = _ |- _ => rewrite <- H
         end.

Ltac rewriter' :=
  repeat match goal with
           H : _ = _ |- _ => rewrite H in *
         end.

Ltac rewriter_clear :=
  repeat match goal with
           H : _ = _ |- _ => rewrite H in *; clear H
         end.

Ltac openHyp :=
  match goal with
    | [H: _ /\ _ |- _ ] => destruct H
    | [H: exists x, _ |- _ ] => destruct H
  end.

Ltac openhyp :=
  repeat match goal with
           | H : _ /\ _ |- _  => destruct H
           | H : _ \/ _ |- _ => destruct H
           | H : exists x, _ |- _ => destruct H
         end.

Ltac not_eq H1 H2 :=
  match H1 with
    | H2 => fail 1
    | _ => idtac
  end.

Lemma pair_eq: forall A B (a b:A) (c d:B), (a, c) = (b, d) -> a = b /\ c = d.
  intuition;
  inversion H; auto.
Qed.

Ltac openPair:= match goal with
                  | H: ( _ , _ ) = ( _ , _ ) |- _ => eapply pair_eq in H; destruct H
                  | H: ?x = ( _ , _ ) |- _ => destruct x; eapply pair_eq in H; destruct H
                  | H: ( _ , _ ) = ?x |- _ => destruct x; eapply pair_eq in H; destruct H
                end.
