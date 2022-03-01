
From LexLatStruct.Order Require Import CPO.
From LexLatStruct.Order.Map Require Import Monotone.
From LexLatStruct.Order.Partial Require Import Arrow.
From LexLatStruct.Order.Partial Require Import Sub.
From LexLatStruct.Order.CPO Require Import Arrow.
From LexLatStruct.Order.CPO Require Import Sub.
From LexLatStruct.Order Require Import PartialOrder.

Section FmonCPO.

Context {A B} `{Equiv A} `{lea : Le A} `{!CompletePartialOrder lea}
        `{Equiv B} `{leb : Le B} `{!CompletePartialOrder leb}.

Existing Instance arrow_cpo.

Lemma lub_is_op:
  forall (S : nat-m>(A->B)),
    (forall n, OrderPreserving (S n)) ->
    OrderPreserving (lub S).
Proof.
intros S H1.
split.
split.
apply CompletePartialOrder0.
apply CompletePartialOrder1.
split.
apply CompletePartialOrder0.
apply CompletePartialOrder1.
reduce.
unfold lub.
(* unfold CompletePartialOrder_instance_0.
unfold lubF. *)
apply po_antisym.
  apply cpo_le_lub.
  intro.
  unfold funseq at 1.
  simpl.
  specialize H1 with n.
  destruct H1.
  destruct order_preserving_mor.
  destruct order_po_b.
  destruct po_setoid.
  rewrite H2.
  assert (S n y = (funseq S y) n). {
    unfold funseq.
    simpl.
    reflexivity. }
  rewrite H1.
  apply cpo_lub_le.
  apply cpo_le_lub.
  intro.
  unfold funseq at 1.
  simpl.
  specialize H1 with n.
  destruct H1.
  destruct order_preserving_mor.
  destruct order_po_b.
  destruct po_setoid.
  destruct ordermor.
  assert (S n y = (funseq S x) n). {
    unfold funseq.
    simpl.
    rewrite <- H2.
    reflexivity. }
  rewrite H1.
  apply cpo_lub_le.
intros x y x_le_y.
apply cpo_le_lub.
intro n.
unfold funseq.
simpl.
transitivity (S n y).
apply H1.
apply x_le_y.
unfold lubF.
assert (S n y = (funseq S y) n).
{ unfold funseq. simpl.
  destruct CompletePartialOrder1.
  destruct cpo_po.
  reflexivity. }
destruct CompletePartialOrder1.
destruct cpo_po.
rewrite H2.
apply cpo_lub_le.
Qed.

Existing Instance subord_is_cpo.
Existing Instance sub_equiv.

Instance fmon_cpo : CompletePartialOrder (@sub_leq (A->B) OrderPreserving arrow_leq) :=
subord_is_cpo lub_is_op.


End FmonCPO.
