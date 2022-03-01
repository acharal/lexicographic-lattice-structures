From LexLatStruct.Order Require Import CPO.
From LexLatStruct.Order.Partial Require Import Arrow.


Section ArrowCPO.

Context {A:Type} {B} `{Equiv B} {leb : Le B} `{!CompletePartialOrder leb}.

Instance : Setoid B := po_setoid.

Definition funseq (s : nat-m>(A->B)) (a : A) : nat-m>B.
exists (fun (n : nat) => s n a).
split.
split.
apply PartialOrder_instance_0.
apply CompletePartialOrder0.
split.
apply PartialOrder_instance_0.
apply CompletePartialOrder0.
reduce.
rewrite H0.
apply po_setoid.
intros x y x_le_y.
apply (proj2_sig s).
apply x_le_y.
Defined.

Definition lubF := fun (f : nat-m> (A->B)) => fun (a : A) => lub (funseq f a).

Program Instance arrow_cpo : CompletePartialOrder (@arrow_leq A B leb) := {
  lub := lubF
}.
Next Obligation.
Proof.
  (* intros F n. *)
  unfold le.
  unfold arrow_leq.
  intro x.
  assert (F n x = funseq F x n).
  { unfold funseq. simpl. reflexivity. }
  rewrite H0.
  apply cpo_lub_le.
Qed.
Next Obligation.
  (* intros F x H1. *)
  unfold le in *.
  unfold arrow_leq in *.
  intro x0.
  apply cpo_le_lub.
  intro n.
  apply H0.
Defined.

End ArrowCPO.
