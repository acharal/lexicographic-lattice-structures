From LexLatStruct.Order Require Import CPO.
From LexLatStruct.Order.Partial Require Import Sub.
From LexLatStruct.Order Require Import PartialOrder.

Section Suborder.

Context {A:Type} {P : A ->Prop} `{Equiv A} `{leq : Le A} `{!CompletePartialOrder leq}.

Variable PSlub: forall (S : nat-m>A), (forall n, P (S n)) -> P (lub S).

Existing Instance subord_is_setoid.
Existing Instance sub_equiv.
Instance : Le { x : A | P x } := sub_leq leq.
#[local] Existing Instance subord_is_partialorder.

Definition Embed (t : A) (p : P t) : { x : A | P x }.
exists t . apply p.
Defined.

Definition Extend (S : nat-m>{ x : A | P x }) : nat-m>A.
destruct S.
exists (fun n => proj1_sig (x n)).
split.
split.
apply PartialOrder_instance_0.
apply CompletePartialOrder0.
split.
apply PartialOrder_instance_0.
apply CompletePartialOrder0.
apply o.
apply o.
Defined.

Lemma ExtendP : forall (S : nat-m>{x : A | P x}) t, P (Extend S t).
intros S t. destruct S. unfold Extend. simpl. apply (proj2_sig (x t)).
Defined.

Program Instance subord_is_cpo : CompletePartialOrder (@sub_leq A P leq) := {
  lub := fun (S: nat-m>{x:A | P x}) => Embed (lub (Extend S)) (PSlub (Extend S) (ExtendP S))
}.
Next Obligation.
(* intros F n. *)
unfold le. unfold sub_leq. unfold sig_le. unfold Embed. simpl.
assert (proj1_sig (F n) = Extend F n). {
  destruct F.
  unfold Extend.
  simpl.
  apply po_setoid.
}
destruct CompletePartialOrder0. destruct cpo_po.
rewrite H0.
apply cpo_lub_le.
Qed.

Next Obligation.
(* intros F x H1. *)
unfold Embed.
unfold le.
unfold sub_leq.
unfold sig_le.
simpl.
apply cpo_le_lub.
intro n.
assert (proj1_sig (F n) = Extend F n). {
  destruct F.
  unfold Extend.
  simpl.
  apply po_setoid.
}
destruct CompletePartialOrder0. destruct cpo_po.
rewrite <- H2.
apply H0.
Defined.

End Suborder.

