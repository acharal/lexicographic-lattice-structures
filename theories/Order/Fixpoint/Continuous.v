Require Import LexLatStruct.Basic.
Require Import LexLatStruct.Order.Map.Continuous.
Require Import LexLatStruct.Order.Map.Monotone.
Require Import LexLatStruct.Order.Fixpoint.
Require Import LexLatStruct.Order.CPO.
Require Import LexLatStruct.Order.Pointed.
Require Import Arith.

Section ContinuousFixpoint.


Open Scope nat.

Context {A} `{Equiv A} {leq : Le A} `{!CompletePartialOrder leq} `{!Pointed leq}
        (f: A-m>A) `{!LimitPreserving f}.

Fixpoint iter_ (n : nat) : A :=
  match n with
    | 0 => bot
    | S m => f (iter_ m)
  end.

Instance : Setoid A := po_setoid.

Lemma iter_is_expanding :
    forall n, iter_ n ≤ f (iter_ n).
Proof.
  induction n.
  apply Pbot.
  unfold iter_ at 1.
  apply order_preserving.
  apply (proj2_sig f).
  apply IHn.
Qed.

Lemma iter_is_preserving : OrderPreserving iter_.
Proof.
  split.
    - split.
      apply PartialOrder_instance_0.
      apply CompletePartialOrder0.
      split.
      apply po_setoid.
      apply po_setoid.
      reduce.
      unfold equiv in H0. unfold Equiv_instance_0 in H0.
      induction H0.
      reflexivity.
    - intros x y x_le_y.
      induction x_le_y. reflexivity.
      transitivity (iter_ m).
      assumption.
      apply iter_is_expanding.
Qed.

Definition iter : nat-m>A := exist _ iter_ iter_is_preserving.

Definition lfp := lub iter.

Lemma lfp_is_postfixedpoint : PostFixedPoint f lfp.
Proof.
  unfold PostFixedPoint.
  unfold lfp.
  transitivity (lub (fmon_comp f iter)).
  - apply lub_le_compat. unfold fmon_comp.
    unfold le. unfold sub_leq. unfold sub_leq. unfold sig_le.
    simpl. unfold Basics.compose. unfold le. unfold arrow_leq_inst.
    unfold arrow_leq. intro. apply iter_is_expanding.
  - apply lub_le_order_preserving.
Qed.

Lemma lfp_is_prefixedpoint : PreFixedPoint f lfp.
Proof.
  unfold PreFixedPoint.
  unfold lfp.
  transitivity (lub (fmon_comp f iter)).
  - rewrite limit_preserving.
    reflexivity. assumption.
  - rewrite (lub_lift_left iter (S 0)).
    unfold seq_lift_left. simpl.
    apply lub_le_compat.
    unfold le. unfold sub_leq. unfold sub_leq. unfold sub_leq. unfold sig_le.
    simpl. reflexivity.
Qed.

Lemma lfp_is_fixedpoint : FixedPoint f lfp.
Proof.
  apply po_antisym.
  apply lfp_is_prefixedpoint.
  apply lfp_is_postfixedpoint.
Qed.

Lemma lfp_is_least_prefixedpoint :
  forall g,
    PreFixedPoint f g ->
    lfp ≤ g.
Proof.
  unfold lfp. intros g g_pf.
  apply cpo_le_lub.
  induction n.
  - apply Pbot.
  - simpl. transitivity (f g).
    apply order_preserving.
    apply (proj2_sig f).
    apply IHn.
    apply g_pf.
Qed.

End ContinuousFixpoint.
