From LexLatStruct Require Import Basic.
From LexLatStruct Require Import Order.
From LexLatStruct Require Import WfOrdinal.

Require Import Arith.


Open Scope wf_ord_scope.
Open Scope ord_scope.
Open Scope nat.

Definition PreFixedPoint {A} `{Le A} (f : A -> A) (d : A) : Prop := f d ≤ d.
Definition PostFixedPoint {A} `{Le A} (f : A -> A) (d : A) : Prop := d ≤ f d.
Definition FixedPoint {A} `{Equiv A} (f : A -> A) (d : A) : Prop := f d = d.

Class Expansive {A} `{Le A} (f:A->A) :=
  { expansive : forall x, x ≤ f x }.

Section ContinuousFixpoint.

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
      unfold le. unfold sub_leq_inst. unfold sub_leq. unfold sig_le.
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
      unfold le. unfold sub_leq_inst. unfold sub_leq. unfold sub_leq. unfold sig_le.
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

Section OrdinalOrder.

  Instance : Equiv wf_ord := wf_ord_eq.
  Instance : Equiv ord := ord_eq.
  Instance : Le wf_ord := wf_ord_le.

  Instance : Setoid wf_ord.
  Proof.
    split.
    - unfold Reflexive. intros. apply ord_eq_refl.
    - unfold Symmetric. intros. apply ord_eq_symm; assumption.
    - unfold Transitive. intros. apply ord_eq_trans with (y); assumption.
  Qed.

  Instance : PreOrder wf_ord_le.
  Proof.
    split.
     - unfold Reflexive. unfold wf_ord_le. intros. apply ord_le_refl.
     - unfold Transitive. intros. unfold wf_ord_le in *.
       apply ord_le_trans with (proj1_sig y) ; assumption.
  Qed.

  Instance : PartialOrder wf_ord_le.
  Proof.
  split.
    - apply Setoid_instance_1.
    - reduce. apply ord_le_wd; assumption.
    - apply PreOrder_instance_0.
    - unfold AntiSymmetric.  intros. apply ord_le_antisymm; assumption.
  Qed.

  Instance : TotalOrder wf_ord_le.
  Proof.
  split.
    - apply PartialOrder_instance_0.
    - unfold TotalRelation. intros. apply ord_le_ge_cases.
  Qed.

End OrdinalOrder.

Lemma mon_lt_implies_mon_le : forall f : nat -> ord,
  (forall n m, (n < m)%nat -> (f n < f m)%ord) ->
  (forall n m, (n <= m)%nat -> (f n <= f m)%ord).
Proof.
intros g Hw n m Hnm.
apply le_lt_or_eq in Hnm. destruct Hnm as [Hlt|Heq].
- apply ord_lt_ord_le. apply Hw. apply Hlt.
- rewrite Heq. apply ord_le_refl.
Qed.

(*
Section Fixpoints.

Context {A} `{Equiv A} `{le : Le A} `{!Pointed le}
       `{!CompletePartialOrder le}.

Variable f : A -m> A.

Program Fixpoint iter (n : wf_ord) {wf wf_ord_lt n} : A :=
  match n with
    | Zero    => bot
    | Succ m  => f (iter m)
    | Limit s => lub (fun (n:nat) => iter (s n))
  end.

(* m is wellformed ordinal *)
Next Obligation.
apply wf_ord_wf_succ_implies_wf.
destruct n.
rewrite Heq_n.
trivial.
Qed.

(* n is decreasing *)
Next Obligation.
unfold wf_ord_lt.
unfold proj1_sig at 1.
rewrite <- Heq_n.
exists (inl (pd_type m) tt).
apply ord_le_refl.
Qed.

(* (s n) is wellformed ordinal *)
Next Obligation.
apply wf_ord_wf_limit_implies_wf.
destruct n0.
rewrite Heq_n.
trivial.
Qed.

(* (s n) is decreasing *)
Next Obligation.
unfold wf_ord_lt in *.
unfold proj1_sig at 1.
rewrite <- Heq_n.
apply wf_ord_lt_limit_is_bound.
rewrite Heq_n.
destruct n0.
apply w.
Qed.

(* the sequence is increasing and the lub is well-defined *)
Next Obligation.
split.
admit.
admit.
Admitted.

Lemma le_word_le_ord :
  forall x y : wf_ord,
    (x <= y)%ord ->
    (proj1_sig x <= proj1_sig y)%ord.
Admitted.

Lemma iter_incr : forall n, iter n ≤ f (iter n).
Proof.
intro n. destruct n as [n Hwfn].
induction n.
- unfold iter; rewrite WfExtensionality.fix_sub_eq_ext ; simpl ; fold iter. apply Pbot.
- unfold iter; rewrite WfExtensionality.fix_sub_eq_ext; simpl; fold iter. destruct f. apply o . apply IHn.
- unfold iter; rewrite WfExtensionality.fix_sub_eq_ext; simpl; fold iter.
  apply cpo_le_lub. intros. simpl.
Admitted.


Instance iter_is_increasing : OrderPreserving iter.
Proof.
split.
- admit.
- intros. destruct x. destruct y. reduce in H0. apply le_word_le_ord in H0. simpl in H0. induction H0.
  * admit.
  * unfold iter at 2; rewrite WfExtensionality.fix_sub_eq_ext; simpl ; fold iter.
    transitivity (iter m).  assumption. apply iter_incr.
Admitted.

Definition fp := lub iter.

Lemma fp_le : fp ≤ f fp. (* PostFixedPoint fp *)
Proof.
unfold fp.
transitivity (lub (f iter))

Lemma fp_eq  : f fp = fp. (* FixedPoint fp *)

Lemma fp_inv : forall g, f g ≤ g -> fp ≤ g. (* fp is less than every prefixedpoint.*)


End Fixpoints.
*)
