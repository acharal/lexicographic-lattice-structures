From LexLatStruct Require Import Basic.
From LexLatStruct Require Import Order.
From LexLatStruct Require Import Lattices.
From LexLatStruct Require Export WfOrdinal.

Open Scope wf_ord_scope.

Instance ord_eq: Equiv ord := ord_eq.
Instance ord_le: Le ord    := ord_le.
Instance ord_lt: Lt ord    := ord_lt.

Instance ord_eq_wd: Equivalence ord_eq.
split.
  unfold Reflexive; apply ord_eq_refl.
  unfold Symmetric; apply ord_eq_symm.
  unfold Transitive; apply ord_eq_trans.
Defined.

Instance ord_po: PartialOrder ord_le.
  split.
  split; apply ord_eq_wd.
  apply ord_le_wd.
  split.
    unfold Reflexive; apply ord_le_refl.
    unfold Transitive; apply ord_le_trans.
  unfold AntiSymmetric; apply ord_le_antisymm.
Defined.

Instance ord_meet : Meet ord.
Admitted.

Instance ord_meet_lattice : MeetSemiLatticeOrder ord_le.
Admitted.

Instance wf_ord_eq: Equiv wf_ord := wf_ord_eq.
Instance wf_ord_le: Le wf_ord    := wf_ord_le.
Instance wf_ord_lt: Lt wf_ord    := wf_ord_lt.

Instance wf_ord_eq_wd: Equivalence wf_ord_eq.
Proof.
split.
  unfold Reflexive; intros; apply ord_eq_refl.
  unfold Symmetric; intros; apply ord_eq_symm; assumption.
  unfold Transitive; intros; apply ord_eq_trans with y; assumption.
Qed.

Instance wf_ord_le_wd : Proper ((=)==>(=)==>iff) wf_ord_le.
Admitted.

Instance wf_ord_po : PartialOrder wf_ord_le.
split.
  apply wf_ord_eq_wd.
  apply wf_ord_le_wd.
  split.
    unfold Reflexive; intros; apply ord_le_refl.
    unfold Transitive; intros; apply ord_le_trans with y; assumption.
  unfold AntiSymmetric; intros; apply ord_le_antisymm; assumption.
Defined.

Instance wf_ord_meet: Meet wf_ord.
Admitted.

Instance wf_ord_meet_lattice: MeetSemiLatticeOrder wf_ord_le.
Admitted.

(* all the ordinals that are less or equal to a certain ordinal alpha *)
Definition orddd (alpha : wf_ord) := sig (fun beta => beta ≤ alpha).

Definition orddd_to_wf_ord {alpha} (beta: orddd alpha): wf_ord := proj1_sig beta.

Coercion orddd_to_wf_ord : orddd >-> wf_ord.

Definition as_orddd (alpha : wf_ord) : orddd alpha.
  exists alpha. reflexivity.
Defined.

(* Coercion as_orddd : wf_ord >-> orddd. *)

(* all the ordinals that are stricty less than a certain ordinal alpha *)
Definition ordd  (alpha: wf_ord) := sig (fun beta => beta < alpha).

Definition ordd_to_orddd {alpha} (beta : ordd alpha) : orddd alpha.
  exists (proj1_sig beta).
  apply ord_lt_ord_le.
  apply (proj2_sig beta).
Defined.

Coercion ordd_to_orddd : ordd >-> orddd.

Definition lift_alpha_to_kappa_eq_lt:
  forall {kappa},
  forall alpha : orddd kappa,
  forall beta : ordd alpha, ordd kappa.
  intros.
  exists (proj1_sig beta).
  apply ord_lt_le_trans with alpha.
  apply (proj2_sig beta).
  apply (proj2_sig alpha).
Defined.

Definition lift_alpha_to_kappa_lt_eq:
  forall {kappa},
  forall alpha : ordd kappa,
  forall beta : orddd alpha, ordd kappa.
  intros.
  exists (proj1_sig beta).
  apply ord_le_lt_trans with alpha.
  apply (proj2_sig beta).
  apply (proj2_sig alpha).
Defined.

Definition lift_alpha_to_kappa_lt:
  forall {kappa},
  forall alpha : ordd kappa,
  forall beta : ordd alpha, ordd kappa.
  intros.
  exists (proj1_sig beta).
  apply ord_lt_trans with alpha.
  apply (proj2_sig beta).
  apply (proj2_sig alpha).
Defined.

Definition lift_alpha_to_beta {alpha beta} (x: ordd alpha):
    alpha <wf= beta -> ordd beta.
  intro.
  exists x.
  apply ord_lt_le_trans with alpha.
  apply (proj2_sig x).
  assumption.
Defined.

Definition ordd_eq (alpha: wf_ord) := sig_equiv (fun beta => beta < alpha).
Definition ordd_le (alpha: wf_ord) := sig_le (fun beta => beta < alpha).
Definition ordd_lt (alpha: wf_ord) := sig_lt (fun beta => beta < alpha).

Instance ordd_eq_: forall alpha, Equiv (ordd alpha) := ordd_eq.
Instance ordd_le_: forall alpha, Le (ordd alpha) := ordd_le.
Instance ordd_lt_: forall alpha, Lt (ordd alpha) := ordd_lt.

Instance ordd_eq_wd:
  forall alpha,
    Equivalence (ordd_eq alpha).
Admitted.

Instance ordd_lt_wd:
  forall alpha,
    Proper ((ordd_eq alpha)==>(ordd_eq alpha)==>iff) (ordd_le alpha).
Admitted.

Instance ordd_le_wd:
  forall alpha,
    Proper ((ordd_eq alpha)==>(ordd_eq alpha)==>iff) (ordd_le alpha).
Admitted.

Instance ordd_po {alpha}: PartialOrder (ordd_le alpha).
Proof.
  split.
  apply ordd_eq_wd.
  apply ordd_le_wd.
  split.
    unfold Reflexive; intros; apply ord_le_refl.
    unfold Transitive; intros; apply ord_le_trans with (proj1_sig y); assumption.
  unfold AntiSymmetric; intros; apply ord_le_antisymm; assumption.
Qed.

Lemma ordd_lt_wf {alpha}: well_founded (ordd_lt alpha).
  unfold well_founded.
  intro.
  destruct a.
  induction (wf_ord_lt_wf x).
  constructor.
  intros.
  destruct y.
  apply H0.
  apply H1.
Defined.

Instance ordd_meet {alpha}: Meet (ordd alpha).
Admitted.

Instance ordd_meet_lattice {alpha}: MeetSemiLatticeOrder (ordd_le alpha).
Admitted.

Definition ordd_to_ordk_0 : forall {kappa} {alpha: wf_ord}, alpha ≤ kappa -> ordd alpha -> ordd kappa.
  intros kappa alpha Hle beta.
  exists beta.
  apply ord_lt_le_trans with alpha.
  apply (proj2_sig beta).
  apply Hle.
Defined.

Definition ordd_to_ordk : forall {kappa} {alpha: orddd kappa}, ordd alpha -> ordd kappa.
  intros kappa alpha beta.
  refine (@ordd_to_ordk_0 kappa alpha _ beta).
  apply (proj2_sig alpha).
Defined.

Definition ordk_to_ordd {kappa} {beta : orddd kappa} (alpha : ordd kappa) (beta_eq_kappa: beta =wf= kappa) : ordd beta.
  exists (proj1_sig alpha).
  apply ord_lt_le_trans with kappa.
  apply (proj2_sig alpha).
  apply beta_eq_kappa.
Defined.

Definition ordkd_to_ordk {kappa} (alpha : orddd kappa) (alpha_lt_kappa : alpha <wf kappa) : ordd kappa.
  exists (proj1_sig alpha).
  exact alpha_lt_kappa.
Defined.

Lemma ordk_rewrite:
  forall {kappa} (alpha : ordd (as_orddd kappa)),
    alpha = ordd_to_ordk alpha.
Proof.
  intros; apply ord_le_antisymm; apply ord_le_refl.
Qed.

Require Import Coq.Logic.Classical_Prop.      (* classic *)

(* move elsewhere *)
Lemma ord_le_le_3:
  forall (A:Type) (P R Q : A->Prop),
    (forall n, P(n) -> R(n) \/ Q(n)) ->
    (forall n, P(n) -> R(n)) \/ (exists n, P(n) /\ Q(n)).
Proof.
  intros.
  assert (forall {P : A -> Prop} {Q : Prop}, (forall (n:A), P n \/ Q) -> (forall (n:A), P n) \/ Q).
    intros.
    classical_left.
    intros.
    destruct (H0 n).
      assumption.
      contradiction.
   apply H0.
   intros.
   classical_left.
   intro.
   destruct (H n H2).
   assumption.
   contradict H1.
   exists n.
   split; assumption.
Qed.
