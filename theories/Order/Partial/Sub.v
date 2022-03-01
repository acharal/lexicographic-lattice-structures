Require Export Coq.Relations.Relations.
Require Import Coq.Program.Program.
From LexLatStruct Require Export Basic.
From LexLatStruct.Order Require Import PartialOrder.

Section Suborder.

Context {A} {P: A->Prop}.

Definition sub_equiv `{Equiv A} : Equiv {x : A | P x} := sig_equiv P.

Definition sub_leq (le : Le A) : Le {x : A | P x} := sig_le P.

Existing Instance sub_equiv.
Existing Instance sub_leq.

Instance subord_is_setoid `{Setoid A} : Setoid { x : A | P x }.
Proof.
split.
- unfold Reflexive. intro. unfold equiv. unfold sub_equiv. unfold sig_equiv. reflexivity.
- unfold Symmetric. intros. unfold equiv. unfold sub_equiv. unfold sig_equiv. destruct H. unfold Symmetric in Equivalence_Symmetric. apply Equivalence_Symmetric.
  unfold equiv in H0. unfold sub_equiv in H0. trivial.
- unfold Transitive. intros. unfold equiv. unfold sub_equiv. unfold sig_equiv.
  unfold equiv in H0. unfold sub_equiv in H0. unfold equiv in H1. unfold sub_equiv in H1. unfold sig_equiv in H1. rewrite <- H1. trivial.
Qed.

Instance subord_is_preorder (leq : Le A) `{!PreOrder leq} : PreOrder (sub_leq leq).
Proof.
split.
- reduce. destruct PreOrder0. unfold Reflexive in PreOrder_Reflexive. apply PreOrder_Reflexive.
- unfold sub_leq. reduce. destruct PreOrder0. apply transitivity with (proj1_sig y).
  + apply H.
  + apply H0.
Qed.

Global Instance subord_is_partialorder `{Equiv A} (leq : Le A) `{!PartialOrder leq} : PartialOrder (sub_leq leq).
Proof.
destruct PartialOrder0. split.
- apply subord_is_setoid.
- reduce. unfold le. unfold sub_leq. unfold sig_le. unfold equiv in H0. unfold sub_equiv in H0. unfold sig_equiv in H0.
  unfold equiv in H1. unfold sub_equiv in H1. unfold sig_equiv in H1. rewrite H0. rewrite H1. reflexivity.
- apply subord_is_preorder. apply po_preorder.
- unfold AntiSymmetric. intros. unfold equiv. unfold sub_equiv.
  unfold AntiSymmetric in po_antisym. apply po_antisym.
  + reduce in H0. assumption.
  + reduce in H1. assumption.
Qed.

End Suborder.
