From LexLatStruct Require Import Basic.
From LexLatStruct.Order Require Import Ordinal.
From LexLatStruct.Order Require Import PartialOrder.
From LexLatStruct.Order Require Import Lattice.
Require Import Coq.Logic.Classical_Prop.

Section Lexicographic.


Variable kappa : wf_ord.

Notation ordkd := (orddd kappa).
Notation kappa_as_orkd := (as_orddd kappa).
Notation ordk := (ordd kappa_as_orkd).

Hypothesis kappa_is_limit : is_limit kappa.

Lemma ordk_succ : forall alpha : ordk, succ alpha < kappa.
Admitted.

Lemma ordk_zero : zero < kappa.
Admitted.

Definition zerok := exist (fun beta => beta < kappa) zero ordk_zero.
Definition succk (alpha : ordk) := exist (fun beta => beta < kappa) (succ alpha) (ordk_succ alpha).
Definition limitk (f : nat -> ordk)
                  (h : forall x m : nat, (x < m)%nat -> (f x) < (f m))
                  (h2: limit f h < kappa) : ordk.
  exists (limit f h).
  exact h2.
Defined.

Lemma well_founded_ordk_lt_ind :
  forall (P:ordk -> Prop), (forall n, (forall m, (m < n) -> P m) -> P n) -> forall n, P n.
Proof.
  exact (well_founded_ind ordd_lt_wf).
Qed.


Lemma well_founded_ordk_lt_rec :
  forall (P:ordk -> Set), (forall n, (forall m, (m < n) -> P m) -> P n) -> forall n, P n.
Proof.
  exact (well_founded_induction ordd_lt_wf).
Qed.

Lemma well_founded_ordk_lt_rect :
  forall (P:ordk -> Type), (forall n, (forall m, (m < n) -> P m) -> P n) -> forall n, P n.
Proof.
  exact (well_founded_induction_type ordd_lt_wf).
Qed.

(* probably not correct *)
Lemma ordd_ind :
  forall P : ordk -> Prop,
        P zerok ->
        (forall o : ordk, P o -> P (succk o)) ->
        (forall f : nat -> ordk,
          forall (h1: forall x m : nat, (x < m)%nat -> proj1_sig (f x) < proj1_sig (f m))
                  (h2: limit f h1 < kappa),
          (forall n : nat, P (f n)) -> P (limitk f h1 h2)) ->
        forall o : ordk, P o.
Admitted.

(* probably not correct *)
Definition ordd_rect :
  forall P : ordk -> Type,
        P zerok ->
        (forall o : ordk, P o -> P (succk o)) ->
        (forall f : nat -> ordk,
          forall (h1: forall x m : nat, (x < m)%nat -> proj1_sig (f x) < proj1_sig (f m))
                  (h2: limit f h1 < kappa),
          (forall n : nat, P (f n)) -> P (limitk f h1 h2)) ->
        forall o : ordk, P o.
Admitted.

Context {A} `{equiv : Equiv A}.

Definition Least (le : Le A) (S: A->Prop) (x:A) : Prop :=
  forall y, S y -> le x y.

Context `{equiv_a : forall alpha : ordk, Equiv A}.

Section RelSq.
  Context { le_a : ordk -> Le A }.

  (* Definition 1.3 *)
  Definition lt_a (alpha : ordk) := fun (x y: A) =>
      le_a alpha x y /\ ~ equiv_a alpha x y.

  (* Definition 1.4 *)
  Definition lt_sq :=
    fun x y => exists alpha, lt_a alpha x y.

  (* Definition 1.5 *)
  Definition le_sq : Le A :=
    fun x y => lt_sq x y \/ x = y.

End RelSq.

Existing Instance le_sq.
Infix "⊏" := lt_sq (at level 50).
Notation "(⊏)" := lt_sq (only parsing).
Infix "⊑" := le_sq (at level 50).
Notation "(⊑)" := le_sq (only parsing).

(* Definition 1.6 *)
Definition interval_a (alpha : ordk) (x : A) : A -> Prop :=
  fun (y : A) => forall beta, beta < alpha -> equiv_a beta x y.

Notation "( x ] a" := (interval_a a x) (at level 0).

(* Definition 1.6 *)
Definition closed_interval_a (alpha : ordk) (x : A) : A ->Prop :=
fun (y:A) => equiv_a alpha x y.

Notation "[ x ] a" := (closed_interval_a a x) (at level 0).

Class StratifiedCompleteLattice (le_a : ordk -> Le A) :=
  { le_a_preorder :> forall alpha, PreOrder (le_a alpha)
  ; eq_a_equiv    :> forall alpha, Equivalence (equiv_a alpha)
  ; le_a_eq_a_antisym : forall alpha, @AntiSymmetric A `(equiv_a alpha) (le_a alpha) (* Def 1.2 *)
  ; le_a_eq_a_proper : forall alpha, Proper ((equiv_a alpha) ==> (equiv_a alpha) ==> iff) (le_a alpha)
  ; le_a_family: forall alpha beta, alpha = beta -> forall x y, le_a alpha x y <-> le_a beta x y

  ; axiom1: forall alpha beta, alpha < beta ->
              forall x y, le_a beta x y -> equiv_a alpha x y
  ; axiom2: forall x y, x = y <-> forall alpha, equiv_a alpha x y
  ; sq_lattice :> CompleteLattice (⊑) (* property 3 *)

  ; lub_a: ordk -> (A->Prop) -> A

  ; axiom3_lub : forall x, forall alpha, forall (S: A->Prop),
          (forall z, S z ->  interval_a alpha x z) ->
          interval_a alpha x (lub_a alpha S) (* prop4 *)

  ; axiom3_lub_a: forall x, forall alpha, forall (S : A->Prop),
        (forall z, S z ->  interval_a alpha x z) ->
        forall z, S z -> le_a alpha z (lub_a alpha S) (* prop4i *)

  ; axiom3_lub_least_1: forall x, forall alpha, forall (S : A->Prop),
        (forall z, S z -> interval_a alpha x z) ->
        forall z, interval_a alpha x z ->
                (forall y, S y -> le_a alpha y z) ->
                le_a alpha (lub_a alpha S) z  (* prop4ii *)
  ; axiom3_lub_least_2: forall x, forall alpha, forall (S : A->Prop),
        (forall z, S z -> interval_a alpha x z) ->
        forall z, interval_a alpha x z ->
                (forall y, S y -> le_a alpha y z) ->
                le_sq (lub_a alpha S) z  (* prop4ii *)
  ; prop4iii : forall x, forall alpha, forall (S : A->Prop),
        (forall z, S z -> interval_a alpha x z) ->
        equiv_a alpha (lub_a alpha S) (sup S)
  }.



Section Consequences.

Context {le_a : ordk -> Le A} `{!StratifiedCompleteLattice le_a}.

(* Instance : CompleteLattice le_sq := sq_lattice. *)

Lemma eq_a_iff_le_a:
  forall alpha, forall x y,
    le_a alpha x y /\ le_a alpha y x <-> equiv_a alpha x y.
Proof.
  intros.
  split.
  intro H.
  apply le_a_eq_a_antisym; apply H.
  intro H.
  split.
  pose proof le_a_eq_a_proper.
  pose proof le_a_preorder.
  rewrite H.
  reflexivity.
  pose proof le_a_eq_a_proper.
  pose proof le_a_preorder.
  rewrite H.
  reflexivity.
Qed.

(* lemma 3.4a *)
Lemma join_le_a_eq :
  forall x y,
  (forall alpha, le_a alpha x y) ->
   x = y.
Proof.
  intros x y x_lea_y.
  apply axiom2.
  intro alpha.
  apply axiom1 with (beta:=succk alpha).
  apply ord_lt_succ_alpha.
  apply x_lea_y.
Qed.

Lemma le_a_eq_a_trans :
  forall alpha,
  forall x y z,
    le_a alpha x y ->
    equiv_a alpha y z ->
    le_a alpha x z.
Proof.
  intros alpha x y z.
  intros le_x_y eq_y_z.
  assert (Transitive (le_a alpha)). apply (le_a_preorder alpha).
  transitivity y.
  apply le_x_y.
  apply eq_a_iff_le_a in eq_y_z.
  apply eq_y_z.
Qed.

Lemma eq_a_le_a_trans :
  forall alpha,
  forall x y z,
    equiv_a alpha x y ->
    le_a alpha y z ->
    le_a alpha x z.
Proof.
  intros alpha x y z.
  intros eq_x_y le_y_z.
  assert (Transitive (le_a alpha)). apply (le_a_preorder alpha).
  transitivity y.
  apply eq_a_iff_le_a in eq_x_y.
  apply eq_x_y.
  apply le_y_z.
Qed.


(* added *)
Lemma eq_a_lt_a_trans :
  forall alpha,
  forall x y z,
    equiv_a alpha x y ->
    lt_a alpha y z ->
    lt_a alpha x z.
Proof.
  intros.
  destruct H0.
  split.
  apply eq_a_le_a_trans with y; assumption.
  intro.
  apply H1.
  transitivity x.
  symmetry.
  assumption.
  assumption.
Qed.

(*
Lemma axiom3_lub_1: forall x, forall alpha, forall (S: A->Prop),
          (forall z, S z ->  interval_a alpha x z) ->
          interval_a alpha x (lub_a alpha S). (* prop4 *)
Proof.
  intros.
  intros beta beta_lt_alpha.
  assert (forall z, S z -> equiv_a beta x z -> equiv_a beta z (lub_a alpha S) -> equiv_a beta x (lub_a alpha S)).
    intros.
    transitivity z; assumption.
  eapply H0.
  apply (axiom1 beta alpha beta_lt_alpha).
  apply (axiom3_lub_a x).
  assumption.
  apply H. *)

Instance : Setoid A := po_setoid.

Instance le_a_proper : Proper ((=) ==> (=) ==> (=) ==> iff) (le_a).
pose proof le_a_preorder.
reduce.
split.
intro.
rewrite axiom2 in H1.
rewrite axiom2 in H2.
transitivity x0.
  apply eq_a_iff_le_a.
  apply H1.
transitivity x1.
  apply le_a_family with x.
  symmetry.
  assumption.
  assumption.
  apply eq_a_iff_le_a.
  symmetry; apply H2.
intro.
rewrite axiom2 in H1.
rewrite axiom2 in H2.
transitivity y0.
  apply eq_a_iff_le_a.
  symmetry; apply H1.
transitivity y1.
  apply le_a_family with y; assumption.
  apply eq_a_iff_le_a.
  apply H2.
Qed.

Instance eq_a_proper : Proper ((=) ==> (=) ==> (=) ==> iff) (equiv_a).
Proof.
  reduce.
  split.
  intro.
  apply eq_a_iff_le_a.
  rewrite <- H.
  rewrite <- H0.
  rewrite <- H1.
  apply eq_a_iff_le_a.
  apply H2.
  intro.
  apply eq_a_iff_le_a.
  rewrite H.
  rewrite H0.
  rewrite H1.
  apply eq_a_iff_le_a.
  apply H2.
Qed.

(* aux *)
Lemma eq_a_le_a:
  forall alpha,
  forall x y,
    equiv_a alpha x y ->
    le_a alpha x y.
Proof.
  intros alpha x y H.
  pose proof le_a_eq_a_proper.
  pose proof le_a_preorder.
  rewrite H.
  reflexivity.
Qed.

(* aux *)
Lemma eq_b_eq_a:
  forall alpha beta,
    beta < alpha ->
    forall x y, equiv_a alpha x y ->
    equiv_a beta x y.
Proof.
  intros alpha beta beta_le_alpha x y.
  intros x_eq_b_y.
  refine (axiom1 _ _ beta_le_alpha x y _).
  apply eq_a_le_a.
  assumption.
Qed.

(* aux *)
Lemma eq_b_eq_a_2:
  forall alpha,
  forall x y,
    equiv_a alpha x y ->
    (forall beta, beta ≤ alpha -> equiv_a beta x y).
Proof.
  intros alpha x y x_eq_a_y.
  intros beta beta_le_alpha.
  assert (beta_alpha_cases: beta < alpha \/ beta = alpha).
    apply wf_ord_lt_eq_cases. assumption.
  destruct beta_alpha_cases as [H | H].
    apply axiom1 with alpha. assumption. apply eq_a_iff_le_a. symmetry. apply x_eq_a_y.
    rewrite H. apply x_eq_a_y.
Qed.

Lemma le_b_le_a_2:
  forall alpha,
  forall x y,
    le_a alpha x y ->
    (forall beta, beta ≤ alpha -> le_a beta x y).
Proof.
  intros alpha x y x_eq_a_y.
  intros beta beta_le_alpha.
  assert ((beta < alpha)%ord \/ (beta = alpha)%ord).
    apply wf_ord_lt_eq_cases. assumption.
  assert (equiv_a beta x y -> le_a beta x y).
    apply eq_a_iff_le_a.
  case H.
    intro. apply H0. apply axiom1 with alpha; assumption.
    intro. rewrite H1. assumption.
Qed.

Lemma le_sq_equiv_le_a:
  forall alpha x y,
    x ⊑ y ->
    (forall gamma, gamma < alpha -> equiv_a gamma x y) ->
    le_a alpha x y.
Proof.
  intros alpha x y H H0.
  destruct H.
    destruct H as [gamma [H H1]].
    case (wf_ord_lt_ge_cases gamma alpha).
      intro.
      contradict H.
      intro.
      apply H1.
      apply H0.
      apply H2.
      intro.
      apply le_b_le_a_2 with gamma.
      apply H.
      apply H2.
    rewrite H; apply le_a_preorder.
Qed.

(* added *)
Lemma le_a_lt_eq_cases:
  forall alpha,
  forall x y,
    le_a alpha x y <->
    lt_a alpha x y \/ equiv_a alpha x y.
Proof.
  split.
    destruct (classic (equiv_a alpha x y)).
      right; assumption.
      left; split; assumption.
    intro H.
    destruct H.
      apply H.
      apply eq_a_le_a; assumption.
Qed.

Lemma axiom4:
  forall (S : A->Prop), forall alpha, forall y : A,
    nonempty S ->
    (forall x, S x -> equiv_a alpha y x) ->
    equiv_a alpha y (sup S).
Proof.
  intros S alpha y H H1.
  transitivity (lub_a alpha S).
    apply eq_a_iff_le_a.
    split.
    destruct H as [z H].
    transitivity z.
      apply eq_a_le_a.
      apply H1. apply H.
      apply axiom3_lub_a with y.
        intros.
        intros beta beta_lt_alpha.
        apply eq_b_eq_a with alpha.
        apply beta_lt_alpha.
        apply H1.
        apply H0.
      apply H.
    apply axiom3_lub_least_1 with y.
    intros.
    intros beta beta_lt_alpha.
    apply eq_b_eq_a with alpha.
    apply beta_lt_alpha.
    apply H1.
    apply H0.
    intros ? ?; reflexivity.
    intros.
    apply eq_a_le_a.
    symmetry.
    apply H1.
    apply H0.
  apply prop4iii with y.
  intros.
  intros beta H2.
  apply eq_b_eq_a with alpha.
    assumption.
    apply H1.
    assumption.
Qed.

Definition glb_a (alpha : ordk) (S: A->Prop) : A :=
  sup (fun x => equiv_a alpha x (lub_a alpha (@Lower_Set _ (le_a alpha) S))).

Lemma axiom3_glb:
  forall x, forall alpha, forall (S: A->Prop),
    (forall z, S z ->  interval_a alpha x z) ->
    interval_a alpha x (glb_a alpha S).
Proof.
  intros.
  intros beta beta_l_alpha.
  unfold glb_a.
  apply axiom4.
    exists (lub_a alpha (@Lower_Set _ (le_a alpha) S)); reflexivity.
    intros.
    transitivity (lub_a alpha (@Lower_Set _ (le_a alpha) S)).
    apply axiom3_lub.
      admit.
      assumption.
    apply eq_b_eq_a with alpha.
    assumption.
    symmetry; assumption.
Admitted.

Lemma axiom3_glb_a : forall x, forall alpha, forall (S : A->Prop),
        (forall z, S z ->  interval_a alpha x z) ->
        forall z, S z -> le_a alpha (glb_a alpha S) z.
Proof.
  intros.
  unfold glb_a.
  apply eq_a_le_a_trans with (lub_a alpha (@Lower_Set _ (le_a alpha) S)).
    symmetry.
    apply axiom4.
    exists (lub_a alpha (@Lower_Set _ (le_a alpha) S)); reflexivity.
    intros; symmetry; assumption.
  apply axiom3_lub_least_1 with x.
  admit.
  apply H; assumption.
  intros.
  apply H1.
  apply H0.
Admitted.

Lemma axiom3_glb_least_1 :
  forall x, forall alpha, forall (S : A->Prop),
    (forall z, S z -> interval_a alpha x z) ->
    forall z, interval_a alpha x z ->
           (forall y, S y -> le_a alpha z y) ->
            le_a alpha z (glb_a alpha S).
Proof.
  intros.
  apply le_a_eq_a_trans with (lub_a alpha (@Lower_Set _ (le_a alpha) S)).
  apply axiom3_lub_a with x.
  admit.
  unfold Lower_Set, Lower_Bound.
  intros.
  apply H1.
  apply H2.
  apply axiom4.
    exists (lub_a alpha (@Lower_Set _ (le_a alpha) S)); reflexivity.
    intros; symmetry; assumption.
Admitted.

Lemma axiom3_glb_least_2 :
  forall x, forall alpha, forall (S : A->Prop),
    (forall z, S z -> interval_a alpha x z) ->
    forall z, interval_a alpha x z ->
           (forall y, S y -> le_a alpha z y) ->
            le_sq z (glb_a alpha S).
Proof.
  intros.
  apply Psup.
  reduce.
  apply eq_a_iff_le_a.
  split.
    apply axiom3_lub_a with x.
    admit.
    intros ? ?; apply H1; apply H2.
    apply axiom3_lub_least_1 with x.
    admit.
    assumption.
    intros. apply H2.
Admitted.

Lemma prop4iii_glb :
  forall x, forall alpha, forall (S : A->Prop),
    (forall z, S z -> interval_a alpha x z) ->
    equiv_a alpha (glb_a alpha S) (inf S).
Proof.
  intros.
  rewrite inf_rewrite.
  transitivity (lub_a alpha (Lower_Set S)).
    admit.
  apply prop4iii with x.
  intros.
  admit.
Admitted.

(* Definition 1.6 *)
Lemma closed_interval_a_interval_succ_a:
  forall alpha,
  forall x y,
    closed_interval_a alpha x y <->
    interval_a (succk alpha) x y.
Proof.
  intros alpha x y.
  split.
  intro H.
  unfold interval_a in *.
  intros beta beta_le_succ_alpha.
  refine (eq_b_eq_a_2 alpha _ _ _ beta _).
  apply H.
  destruct beta_le_succ_alpha as [x0 H0].
  apply ord_le_succ_pd_right with x0.
  apply H0.
  intro.
  unfold interval_a in *.
  unfold closed_interval_a in *.
  apply H.
  apply ord_lt_succ_alpha.
Qed.

(* lemma 2.1 *)
Lemma lemma21:
   forall x, forall alpha, forall (S: A->Prop),
      (forall z, S z -> interval_a alpha x z) ->
      interval_a alpha x (sup S).
Proof.
  intros.
  intros beta beta_le_alpha.
  transitivity (lub_a alpha S).
  apply axiom3_lub; assumption.
  apply eq_b_eq_a with alpha.
  assumption.
  apply prop4iii with x.
  assumption.
Qed.

(* lemma 2.2 *)
Lemma lemma22:
  forall alpha x y,
    (forall beta, beta < alpha -> equiv_a beta x y) ->
    le_sq x y ->
    le_a alpha x y.
Proof.
  intros alpha x y H1 H2.
  destruct H2 as [ H | H].
  destruct H as [beta H].
  destruct (wf_ord_lt_trichotomy alpha beta) as [alpha_lt_beta | [ alpha_eq_beta | alpha_gt_beta ]].
  apply eq_a_le_a.
  apply axiom1 with beta.
    apply alpha_lt_beta.
    apply H.
    assert (Hp: alpha = beta). apply alpha_eq_beta.
    rewrite Hp.
    apply H.
    absurd (equiv_a beta x y).
      apply H.
      apply H1.
      apply alpha_gt_beta.
    rewrite H; reflexivity.
Qed.

(* lemma 2.3 *)
Lemma lemma23:
  forall x y,
     le_sq x y -> le_a zerok x y.
Proof.
  intros x y x_le_sq_y.
  apply lemma22.
    intros beta H.
    contradict H.
    apply ord_lt_not_zero.
    assumption.
Qed.

(* lemma 2.4 *)
Lemma lemma24:
  forall x, le_a zerok bot x.
Proof.
  intros x.
  apply lemma23.
  apply Pinf.
  reduce.
  trivial.
Qed.

Lemma lemma25:
  forall x, forall alpha, forall (S: A->Prop),
    (forall z, S z -> interval_a alpha x z) ->
    forall y, forall z,
      S z ->
      le_a alpha y z ->
      le_a alpha y (lub_a alpha S).
Proof.
  intros x alpha S H1 y z H2 H3.
  transitivity z.
  apply H3.
  apply axiom3_lub_a with x;
   assumption.
Qed.

Lemma lemma26a:
  forall x, forall alpha, forall (S: A->Prop),
    (forall z, S z -> interval_a alpha x z) ->
    Least (≤) (closed_interval_a alpha (lub_a alpha S)) (lub_a alpha S).
Proof.
  intros x alpha S H z H1.
  apply axiom3_lub_least_2 with x.
    assumption.
    intros beta beta_lt_alpha.
    transitivity (lub_a alpha S).
      transitivity (sup S).
      refine (lemma21 _ _ _ H _ beta_lt_alpha).
      apply eq_b_eq_a with alpha.
      assumption.
      symmetry.
      apply prop4iii with x; assumption.
      apply eq_b_eq_a with alpha.
      assumption.
      apply H1.
    transitivity (lub_a alpha S).
    apply axiom3_lub_a with x; assumption.
    apply eq_a_le_a.
    apply H1.
Qed.

Lemma lemma26b:
  forall x, forall alpha, forall (S: A->Prop),
    (forall z, S z -> interval_a alpha x z) ->
    Least (le_a (succk alpha)) (closed_interval_a alpha (lub_a alpha S)) (lub_a alpha S).
Proof.
  intros.
  intros z H1.
  apply lemma22.
    intros beta beta_lt_succ_alpha.
    apply eq_b_eq_a_2 with alpha.
    apply H1.
    destruct beta_lt_succ_alpha.
    apply ord_le_succ_pd_right in H0.
    apply H0.
    refine (lemma26a x _ S H _ H1).
Qed.

Section lemma27.

  Variable x_a : ordk -> A.
  Context `{!Seq x_a}.
  Variable alpha : ordk. (* this should be less-eq to kappa *)

  Hypothesis compseq1 : forall beta : ordk,
      beta < alpha ->
      Least (le_sq) (closed_interval_a beta (x_a beta)) (x_a beta).

  Hypothesis compseq2 : forall beta gamma,
      beta < alpha ->
      gamma < alpha ->
      beta < gamma ->
      equiv_a beta (x_a beta) (x_a gamma).

  Lemma x_sup_sup_3:
    forall beta,
      beta < alpha ->
      sup (fun y => exists gamma, gamma < alpha /\ y = x_a gamma) = sup (fun y => exists gamma, gamma < alpha /\ beta ≤ gamma /\ y = x_a gamma).
  Proof.
    intros beta beta_l_alpha.
    apply po_antisym.
    apply PsupL.
    unfold Upper_Bound.
    intros s H.
    reduce in H.
    destruct H as [x [g_l_alpha H]].
    rewrite H.
    destruct (wf_ord_le_gt_cases beta x).
      apply Psup.
      reduce.
      exists x.
      split.
      assumption.
      split.
        apply H0.
        reflexivity.
    transitivity (x_a beta).
    apply compseq1. assumption.
    apply compseq2; assumption.
    apply Psup.
    reduce.
    exists beta.
    split.
      assumption.
      split; reflexivity.
    apply PsupL.
    unfold Upper_Bound.
    intros s H1.
    apply Psup.
    reduce.
    reduce in H1.
    destruct H1.
    exists x.
    split; apply H.
  Qed.

  Lemma lemma27a:
    forall beta,
      beta < alpha ->
      equiv_a beta (x_a beta) (sup (fun y => exists gamma, gamma < alpha /\ y = x_a gamma)).
  Proof.
    intros beta beta_lt_alpha.
    rewrite (x_sup_sup_3 beta beta_lt_alpha).
    apply axiom4.
      exists (x_a beta).
      exists beta.
      split.
        apply beta_lt_alpha.
        split;
          reflexivity.
    intros x H.
    destruct H as [gamma [g_la [b_l_g H]]].
    rewrite H.
    destruct (proj1 (wf_ord_lt_eq_cases beta gamma) b_l_g).
      apply compseq2; assumption.
      assert (b_eq_g: beta = gamma). assumption.
      rewrite <- b_eq_g; reflexivity.
  Qed.

  Lemma lemma27b:
      Least (le_sq) (interval_a alpha (sup (fun y => exists gamma, gamma < alpha /\ y = x_a gamma))) (sup (fun y => exists gamma, gamma < alpha /\ y = x_a gamma)).
  Proof.
    intros.
    intros y H1.
    apply PsupL.
    intros z H2.
    reduce in H2.
    destruct H2 as [beta [beta_le_alpha H3]].
    rewrite H3.
    refine (compseq1 _ _ _ _). assumption.
    transitivity (sup (fun y : A =>
                         exists gamma : ordd kappa_as_orkd,
                           gamma < alpha /\ y = x_a gamma)).
    apply lemma27a.
      apply beta_le_alpha.
    apply H1.
    apply beta_le_alpha.
  Qed.

End lemma27.

End Consequences.


End Lexicographic.
