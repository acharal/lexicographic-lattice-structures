From LexLatStruct Require Import Basic.
From LexLatStruct.Order Require Import CPO.
From LexLatStruct.Order.Partial Require Import Arrow.
From LexLatStruct.Order.Partial Require Import Sub.
From LexLatStruct.Order.CPO Require Import Arrow.
From LexLatStruct.Order.CPO Require Import Monotone.
Require Import Coq.Program.Program.

Section continuous_maps.

Context {A B} `{CompletePartialOrder A} `{CompletePartialOrder B} (f: A-m>B).

Class LimitPreserving :=
  { limit_preserving: forall (s:nat-m>A), lub (fmon_comp f s) = f (lub s) }.

End continuous_maps.

#[local] Existing Instance sub_equiv.

Lemma limit_compose_preserving_is_preserving {A B C}
  `{CompletePartialOrder A} `{CompletePartialOrder B} `{CompletePartialOrder C}:
  forall (f: B-m>C) (g: A-m>B),
    LimitPreserving f ->
    LimitPreserving g ->
    LimitPreserving (fmon_comp f g).
Proof.
intros f g f_lp g_lp.
split. intro s.
unfold fmon_comp at 3.
unfold compose.
simpl.
destruct H0. destruct H2. destruct H4.
destruct cpo_po. destruct cpo_po0. destruct cpo_po1.
assert (SetoidMorphism f). { apply (proj2_sig f). }
rewrite <- limit_preserving.
rewrite <- limit_preserving.
assert (fmon_comp (fmon_comp f g) s = fmon_comp f (fmon_comp g s)). {
unfold fmon_comp.
unfold equiv. unfold sub_equiv. unfold sig_equiv. simpl.
unfold compose.  reflexivity.
}
rewrite H2.
reflexivity.
assumption.
assumption.
Qed.
