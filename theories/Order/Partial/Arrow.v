
Require Export Coq.Relations.Relations.
Require Import Coq.Program.Program.

From LexLatStruct Require Export Basic.
From LexLatStruct.Order Require Import PartialOrder.

Section ArrowPO.

Context {A B: Type}.

Global Instance arrow_equiv `{Equiv B} : Equiv (A->B) :=
  fun (f g : A->B) => forall x, f x = g x.

Definition arrow_leq `{Le B} : Le (A->B) :=
  fun (f g : A->B) => forall x, f(x) ≤ g(x).

Global Instance arrow_leq_inst `{Le B} : Le (A->B) := arrow_leq.

Lemma arrow_is_preorder {leb : Le B} `{!PreOrder leb} : PreOrder (@arrow_leq leb).
Proof.
  intros.
  split.
  - reduce. reflexivity.
  - unfold Transitive. intros f h g.
    unfold arrow_leq. intro f_less_than_h.
    firstorder.
    specialize (f_less_than_h x).
    apply transitivity with (y:=h x).
    assumption.
    apply H.
Qed.


Global Instance arrow_is_setoid `{Setoid B} : Setoid (A->B).
Proof.
split.
- unfold Reflexive. unfold equiv. unfold arrow_equiv. intros f x.
  destruct H. unfold Reflexive in Equivalence_Reflexive. apply Equivalence_Reflexive.
- unfold Symmetric. unfold equiv. unfold arrow_equiv. intros f g. firstorder.
- unfold Transitive. unfold equiv. unfold arrow_equiv. intros f h g. firstorder.
Qed.

Instance po_is_setoid `{PartialOrder B} : Setoid B := po_setoid.

Global Instance arrow_is_partialorder (leb: Le B) `{Equiv B} `{!PartialOrder leb}: PartialOrder (@arrow_leq leb).
Proof.
split.
- apply arrow_is_setoid.
- reduce. unfold le. unfold arrow_leq. unfold equiv in H0. unfold arrow_equiv in H0.
  unfold equiv in H1. unfold arrow_equiv in H1.
  split.
  + intro. intro w. rewrite <- H1. rewrite <- H0. apply H2.
  + intro. intro w. rewrite -> H1. rewrite -> H0. apply H2.
- apply arrow_is_preorder.
- unfold AntiSymmetric. unfold le. unfold arrow_leq. unfold equiv. unfold arrow_equiv.
  intros f g. intros. apply po_antisym.
  + apply H0.
  + apply H1.
Qed.

End ArrowPO.
