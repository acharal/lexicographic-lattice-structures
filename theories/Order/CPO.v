From LexLatStruct Require Export Basic.
From LexLatStruct.Order.Map Require Export Monotone.
From LexLatStruct.Order.Partial Require Export Nat.
From LexLatStruct.Order.Partial Require Export Arrow.
From LexLatStruct.Order.Partial Require Export Sub.
From LexLatStruct.Order Require Export PartialOrder.

Require Import Coq.Program.Program.


Class CompletePartialOrder {A} `{Equiv A} (Ale : Le A) := {
    cpo_po :> PartialOrder (≤)
  ; lub : forall (F : nat-m>A), A
  ; cpo_lub_le: forall (F : nat-m>A) (n : nat), F n ≤ lub F
  ; cpo_le_lub: forall (F : nat-m>A) (x : A), (forall n, F n ≤ x) -> lub F ≤ x }.


Lemma lub_le_order_preserving {A} {B}
  `{CompletePartialOrder A}
  `{CompletePartialOrder B} :
  forall (f:A-m>B) (s : nat -m>A),
    lub (fmon_comp f s) ≤ f (lub s).
Proof.
  intros f s.
  apply cpo_le_lub.
  intros.
  unfold fmon_comp. unfold compose. simpl.
  apply order_preserving.
  apply (proj2_sig f).
  apply cpo_lub_le.
Qed.

Section LubLemmas.

Context {A} `{CompletePartialOrder A}.

Existing Instance arrow_equiv.
Existing Instance arrow_leq.
Existing Instance sub_equiv.
Existing Instance sub_leq.

Lemma lub_le_compat :
  forall (f g : nat-m>A),
    f ≤ g ->
    lub f ≤ lub g.
Proof.
  intros.
  apply cpo_le_lub.
  intros.
  transitivity (g n).
  apply H1.
  apply cpo_lub_le.
Qed.


Definition seq_lift_left :
  forall (f : nat-m>A) (n:nat), nat-m>A.
  intros.
  exists (fun k => f (n+k)%nat).
  split.
  - split. apply PartialOrder_instance_0. apply H0.
  split. apply po_setoid. apply po_setoid.
  reduce. destruct f. destruct o. destruct order_preserving_mor.
  destruct H0. destruct cpo_po0. destruct ordermor. simpl.
  rewrite H1. reflexivity.
  - intros x y x_le_y.
  apply order_preserving.
  apply (proj2_sig f).
  unfold le. unfold Le_instance_0. unfold le_nat.
  auto with arith.
Defined.

Lemma lub_lift_left :
forall (f : nat-m>A) (n:nat),
  lub f = lub (seq_lift_left f n).
Proof.
intros.
apply po_antisym.
apply lub_le_compat.
unfold seq_lift_left.
unfold le. unfold sub_leq. unfold sub_leq. unfold sig_le.
simpl. unfold le. unfold arrow_leq_inst. unfold arrow_leq.
intro. apply order_preserving. apply (proj2_sig f).
unfold le. unfold Le_instance_0. unfold le_nat. auto with arith.
apply cpo_le_lub. intro. unfold seq_lift_left. unfold fmon_as_fun.
simpl. apply cpo_lub_le.
Qed.

Definition cta (x : A) : nat-m>A.
exists (fun _ => x).
split.
- split.
apply PartialOrder_instance_0.
apply cpo_po.
split.
apply PartialOrder_instance_0.
apply cpo_po.
reduce. destruct H0. destruct cpo_po0. reflexivity.
- intros. reflexivity.
Defined.

End LubLemmas.


#[local] Existing Instance arrow_equiv.
#[local] Existing Instance arrow_leq.
#[local] Existing Instance sub_equiv.
#[local] Existing Instance sub_leq.

#[export] Instance lub_eq_wd {A} `{CompletePartialOrder A} : Proper (equiv ==> equiv) lub.
Proof.
reduce.
apply po_antisym.
- destruct H0. destruct cpo_po0. apply lub_le_compat.
  unfold le. unfold sub_leq. unfold sub_leq.
  unfold sig_le. unfold le. unfold arrow_leq_inst. unfold arrow_leq.
  intro. unfold equiv in H1. unfold sub_equiv in H1. unfold sig_equiv in H1.
  unfold equiv in H1. unfold arrow_equiv in H1. rewrite H1. reflexivity.
- destruct H0. destruct cpo_po0. apply lub_le_compat.
  unfold le. unfold sub_leq. unfold sub_leq.
  unfold sig_le. unfold le. unfold arrow_leq_inst. unfold arrow_leq.
  intro. unfold equiv in H1. unfold sub_equiv in H1. unfold sig_equiv in H1.
  unfold equiv in H1. unfold arrow_equiv in H1. rewrite H1. reflexivity.
Qed.
