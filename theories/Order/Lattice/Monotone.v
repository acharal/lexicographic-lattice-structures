
From LexLatStruct.Order Require Import Lattice.
From LexLatStruct.Order.Monotone Require Import Map.
From LexLatStruct.Order.Partial Require Import Arrow.
From LexLatStruct.Order.Partial Require Import Sub.
From LexLatStruct.Order.Lattice Require Import Arrow.
From LexLatStruct.Order.Lattice Require Import Sub.
From LexLatStruct.Order Require Import PartialOrder.

Section OrderPreservingLattice.

Context {A B : Type} `{PartialOrder A} `{Equiv B} (leq : Le B) `{!CompleteLattice leq}.

Existing Instance sub_equiv.
Existing Instance arrow_equiv.
Existing Instance arrow_is_clat.

Lemma inf_is_order_preserving : forall (S : Ensemble (A->B)), (forall t : A->B, S t -> OrderPreserving t) -> OrderPreserving (inf (Ale:=arrow_leq) S).
intros S l.
assert (Hhh : forall (x:A) (f : A->B), S f -> (f x) ∈ (fun x0 : B => exists g : A->B, S g /\ g x = x0)). {
    intros. exists f. split. assumption. destruct CompleteLattice0. destruct ltord. reflexivity. }
split.
- split.
 + assumption.
 + destruct CompleteLattice0. assumption.
 +
  split.
    * destruct H0. apply po_setoid.
    * destruct CompleteLattice0. destruct ltord. apply po_setoid.
    * reduce.
      assert (forall f : A -> B, S f -> f x = f y). {
        intro. intro.  apply l in H3. destruct CompleteLattice0. destruct ltord. rewrite H2. reflexivity. }
      assert (forall x y, x ≤ y /\ y ≤ x <-> x = y). {
        intros. split. intro. destruct H4. destruct CompleteLattice0. destruct ltord.
        apply po_antisym. assumption. assumption.
        intro.  destruct CompleteLattice0. destruct ltord. split. rewrite H4.  reflexivity. rewrite H4. reflexivity. }
      apply H4. split.
      destruct CompleteLattice0. unfold arrow_is_clat. reduce.
      { apply PinfL. intro. intro. reduce in H5. case H5. intros. destruct H6. apply Pinf. reduce. exists x0. destruct ltord. rewrite <- H7. split.
        assumption. apply H3. apply H6. }
            destruct CompleteLattice0.
      { apply PinfL. intro. intro. reduce in H5. case H5. intros. destruct H6. apply Pinf. reduce. exists x0. destruct ltord. rewrite <- H7. split.
        assumption. symmetry. apply H3. apply H6. }
- intros. unfold inf. unfold arrow_is_clat. unfold contains. reduce.
  destruct CompleteLattice0.
  assert (mon: forall f : A->B, S f -> f x ≤ f y). { intros. apply l. assumption. assumption. }

  apply PinfL. unfold Lower_Bound. intros.  reduce in H3. case H3. intro. intro. destruct H4. assert (Hc : S x0). { assumption. }
  apply mon in H4. destruct ltord. rewrite <- H5.
  simple apply Hhh with (f:=x0) (x:=x) in Hc.
  apply Pinf in Hc.
  transitivity (x0 x). assumption. assumption.
Qed.


Instance orderpreserving_is_complete_lattice : CompleteLattice (sub_leq (P:=OrderPreserving) (@arrow_leq A B leq)).
apply (sub_is_clat (@arrow_leq A B leq) inf_is_order_preserving).
Qed.

End OrderPreservingLattice.
