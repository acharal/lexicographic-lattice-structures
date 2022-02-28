Require Import Basic.
Require Import Order.
Require Import Lattices.
Require Import Fix.
Require Import Ord.

Require Import Coq.Init.Specif.
Require Import Coq.Init.Wf.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.Classical_Prop.

Close Scope nat.
Close Scope ord.

Section Stratified.

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

  Section amonotonic.

    Context {le_a : ordk -> Le A} `{!StratifiedCompleteLattice le_a} (alpha : ordk) (f : A -> A).

    (* Definition 6.1 *)
    Class AlphaOrderPreserving : Prop :=
     { alpha_order_morphism :> Proper ((=) ==> (=)) f
     ; alpha_order_preserving : forall x y, le_a alpha x y -> le_a alpha (f x) (f y) }.

    Lemma aorder_preserving_equiv_alpha `{AlphaOrderPreserving} :
      forall x y, 
        equiv_a alpha x y -> 
        equiv_a alpha (f x) (f y).
    Proof.
      intros x y H0.
      apply eq_a_iff_le_a.
      apply eq_a_iff_le_a in H0.
      split; apply alpha_order_preserving; apply H0.
    Qed.

  End amonotonic.

  Section FixedPointTheorem.

    Context {le_a : ordk -> Le A} `{!StratifiedCompleteLattice le_a}.

    Instance : Setoid A := po_setoid.

    (* the following does not hold *)
    Instance : forall alpha, CompleteLattice (ordd_le alpha).
    Admitted.

    Instance : CompleteLattice (wf_ord_le).
    Admitted.

    Existing Instance le_a_proper.
    Existing Instance eq_a_proper.

    Section lemma32.

      Context (f : A -> A).
      Context (alpha : ordk) (x: A).

      Definition fixy : wf_ord -> A :=
        wf_ord_rect (fun _ : wf_ord => A) 
          (x) 
          (fun n r => f r) 
          (fun h _ hr => lub_a alpha (fun y => exists n, y = (hr n))).

      (* must prove that the set is not empty since inf is defined only to non-empty sets *)
      Definition lambda := inf ( 
            fun delta : wf_ord => forall gamma, 
              delta ≤ gamma -> 
              is_limit delta ->
              equiv_a alpha (fixy delta) (fixy gamma)).

      Lemma lambda_is_limit : is_limit lambda.
      Admitted.

      Lemma fixpy_lemma: 
        forall delta,
          lambda ≤ delta -> 
          equiv_a alpha (fixy lambda) (fixy delta).
      Admitted.

      Definition fixpy := fixy lambda.

      Context `{!AlphaOrderPreserving alpha f}.

      Lemma fixy_zero_eq : fixy zero = x.
      Proof.
        intros; cbv; reflexivity.
      Qed.

      Lemma fixy_succ_eq :
        forall beta, 
          fixy (succ beta) = f (fixy beta).
      Proof.
        intros.
        unfold fixy at 1.
        simpl.
        unfold fixy.
        unfold wf_ord_rect.
        induction beta using wf_ord_ind.
        reduce.
        reflexivity.
        reduce.
        reflexivity.
        reduce.
        reflexivity.
      Qed.

      Lemma fixy_limit_eq :
        forall h hh,
          fixy (limit h hh) = lub_a alpha (fun y => exists n, y = (fixy (h n))).
      Proof.
        intros.
        unfold fixy at 1.
        simpl.
        unfold fixy.
        unfold wf_ord_rect.
        f_equiv.
        extensionality y0.
        f_equiv.
        extensionality n0.
        induction (h n0) using wf_ord_ind; reflexivity.
      Qed.

      Instance : Proper ((=)==>(=)) fixy.
      reduce.
      Admitted.

      Instance : Proper ((wf_ord_eq)==>(=)) fixy.
      Admitted.

      Context `(le_a alpha x (f x)).

      Lemma lemma32_0:
        forall gamma, le_a alpha x (fixy gamma).
      Proof.
        intros.
        pose proof le_a_preorder.
        induction gamma using wf_ord_ind.
        - rewrite fixy_zero_eq. reflexivity.
        - rewrite fixy_succ_eq.
          transitivity (f x).
          assumption.
          apply alpha_order_preserving.
          assumption.
          assumption.
        - rewrite fixy_limit_eq.
        evar (nn:nat).
        apply lemma25 with (x) (fixy (f0 nn)).
        intros z H1.
          destruct H1.
          intros beta beta_lt_alpha.
          apply axiom1 with alpha.
          apply beta_lt_alpha.
          rewrite H1.
          apply H0.
          exists nn; reflexivity.
          apply H0.
          Unshelve.
          exact 0%nat.
      Qed.

      (* Lemma 62, Claim 1 *)
      Lemma lemma32_1: 
        forall gamma, le_a alpha (fixy gamma) (f (fixy gamma)).
      Proof.
        intros.
        pose proof le_a_preorder.
        induction gamma using wf_ord_ind.
        - rewrite fixy_zero_eq at 1.
          transitivity (f x).
          assumption.
          apply alpha_order_preserving.
          assumption.
          rewrite fixy_zero_eq.
          reflexivity.
        - rewrite fixy_succ_eq at 1.
          apply alpha_order_preserving.
          assumption.
          rewrite fixy_succ_eq.
          apply IHgamma.
        - rewrite fixy_limit_eq at 1.
          apply axiom3_lub_least_1 with (x0:=x).
          intros z H2.
          unfold interval_a.
          intros.
          destruct H2.
          apply axiom1 with alpha.
          assumption.
          rewrite H2.
          apply lemma32_0; assumption.
          unfold interval_a.
          intros.
          apply axiom1 with alpha.
          assumption.
          transitivity (f x).
          assumption.
          apply alpha_order_preserving.
          assumption.
          apply lemma32_0; assumption.
          intros y H2.
          destruct H2 as [x0 H2].
          transitivity (f (fixy (f0 x0))).
          rewrite H2.
          apply H0.
          apply alpha_order_preserving.
          assumption.
          rewrite fixy_limit_eq.
          apply axiom3_lub_a with (x1:=x).
          intros.
          unfold interval_a.
          intros.
          apply axiom1 with alpha.
          assumption.
          destruct H1.
          rewrite H1.
          apply lemma32_0; assumption.
          exists x0; reflexivity.
      Qed.

      (* Lemma 62, Claim 2 *)
      Lemma lemma32_2: 
        forall beta gamma, 
           beta < gamma ->
           le_a alpha (fixy beta) (fixy gamma).
      Proof.
        intros.
        pose proof le_a_preorder.
        induction gamma using wf_ord_ind.
        - contradict H; apply ord_lt_not_zero.
        - 
        rewrite fixy_succ_eq.
        transitivity (fixy gamma).
        case (proj1 (wf_ord_lt_eq_cases beta gamma)).
          destruct H.
            apply ord_le_succ_pd_right with x0.
            assumption.
          exact IHgamma.
          intro beta_eq_gamma.
          rewrite beta_eq_gamma.
          reflexivity.
        apply lemma32_1; assumption.
        - rewrite fixy_limit_eq.
          destruct H.
          destruct x0.
          transitivity (fixy (f0 x0)).
          apply H1.
          exists p.
          apply H.
          apply axiom3_lub_a with x.
          intros.
          unfold interval_a.
          intros.
          apply axiom1 with alpha.
          assumption.
          destruct H2.
          rewrite H2.
          apply lemma32_0; assumption.
          exists x0; reflexivity.
      Qed.

      (* Lemma 62, Claim 3 *)
      Lemma lemma32_3:
        forall z, forall gamma,
          le_a alpha x z ->
          le_a alpha (f z) z ->
          le_a alpha (fixy gamma) z.
      Proof.
        intros.
        pose proof le_a_preorder.
        induction gamma using wf_ord_ind.
        - rewrite fixy_zero_eq; assumption.
        - rewrite fixy_succ_eq.
          transitivity (f z).
          apply alpha_order_preserving.
          assumption.
          assumption.
          assumption.
        - rewrite fixy_limit_eq.
        apply axiom3_lub_least_1 with x.
        intros.
        unfold interval_a.
        intros.
        apply axiom1 with alpha.
        assumption.
        destruct H3.
        rewrite H3.
        apply lemma32_0; assumption.
        unfold interval_a.
        intros.
        apply axiom1 with alpha; assumption.
        intros.
        destruct H3.
        rewrite H3.
        apply H2.
      Qed.

      Lemma lemma32_4: equiv_a alpha fixpy (f fixpy).
      Proof.
        intros.
        unfold fixpy.
        transitivity (fixy (succ lambda)).
        apply fixpy_lemma. apply ord_le_succ_right. apply ord_le_refl.
        rewrite fixy_succ_eq. reflexivity.
      Qed.


      Lemma lemma32_5: le_a alpha x fixpy.
      Proof.
        intros.
        pose proof le_a_preorder.
        case (proj1 (wf_ord_lt_eq_cases zero lambda)).
          constructor.
          intro.
          unfold fixpy.
          rewrite <- fixy_zero_eq at 1.
          apply lemma32_2.
          assumption.
          intro.
          unfold fixpy.
          rewrite <- fixy_zero_eq at 1.
          rewrite <- H0.
          reflexivity.
      Qed.

      Lemma lemma32_6:
        forall z, 
          le_a alpha x z ->
          le_a alpha (f z) z ->
          le_a alpha fixpy z.
      Proof.
        intros; apply lemma32_3; assumption.
      Qed.

      Lemma lemma32_6_1:
        fixpy = lub_a alpha (fun y => exists beta, beta < lambda /\ y = fixy beta).
      Proof.
        intros.
        unfold fixpy.
        (* follows directly from the fact that lambda is limit ordinal and the definition of fixy *)
      Admitted.


      Lemma lemma32_7:
        Least (le_sq) (closed_interval_a alpha fixpy) fixpy.
      Proof.
        intros y H.
        rewrite lemma32_6_1.
        refine (lemma26a fixpy _ _ _ _ _).
        intros z H1.
        destruct H1 as [beta [beta_lt_alpha H1]].
        unfold interval_a.
        intros ? ?.
        symmetry.
        apply axiom1 with alpha.
        assumption.
        rewrite H1.
        unfold fixpy.
        apply lemma32_2; assumption.
        rewrite <- lemma32_6_1.
        assumption.
      Qed.

      Lemma lemma32_8:
        Least (le_a (succk alpha)) (closed_interval_a alpha fixpy) fixpy.
      Proof.
        intros.
        reduce.
        rewrite lemma32_6_1.
        refine (lemma26b fixpy _ _ _ _ _).
        intros z H1.
        destruct H1 as [beta [beta_lt_alpha H1]].
        unfold interval_a.
        intros.
        symmetry.
        apply axiom1 with alpha.
        assumption.
        rewrite H1.
        unfold fixpy.
        apply lemma32_2; assumption.
        rewrite <- lemma32_6_1.
        assumption.
      Qed.

      Lemma remark33: le_a (succk alpha) fixpy (f fixpy).
      Proof.
        apply lemma32_8.
        apply lemma32_4.
      Qed.

    End lemma32.


    Section lemma34.

    Context (f : A -> A) `{AllAlphaOrd : forall alpha, AlphaOrderPreserving alpha f}.

    Instance : Setoid A := po_setoid.


    Definition seq_as_set {alpha : ordkd} (s : ordd alpha -> A) : A -> Prop := 
      fun y => exists beta, y = s beta.

    Definition ordd_to_ordk_0 : forall {alpha: wf_ord}, alpha ≤ kappa -> ordd alpha -> ordk.
      intros alpha Hle beta.
      exists beta.
      apply ord_lt_le_trans with alpha.
      apply (proj2_sig beta).
      apply Hle.
    Defined.

    Definition ordd_to_ordk : forall {alpha: ordkd}, ordd alpha -> ordk.
      intros alpha beta.
      refine (@ordd_to_ordk_0 alpha _ beta).
      apply (proj2_sig alpha).
    Defined.

    Lemma ordk_rewrite: 
      forall (alpha : ordk),
        alpha = ordd_to_ordk alpha.
    Proof.
      intros; apply ord_le_antisymm; apply ord_le_refl.
    Qed.

    Arguments fixpy : default implicits.

    Definition fixpyy := fixpy f.

    Definition x_a : ordk -> A.
      refine (Fix (ordd_lt_wf) (fun _ => A)
            (fun (a : ordk) x => fixpyy a (sup (seq_as_set (fun (b : ordd a) => (x (ordd_to_ordk b)) _))))).
      destruct b as [b hb].
      apply hb.
    Defined.

    Definition y_a (alpha : ordk) := 
       sup (seq_as_set (fun (beta : ordd alpha) => x_a (ordd_to_ordk beta))).
    (* sup (fun x => exists beta, beta < alpha /\ x = x_a beta). *)

    Lemma y_a_unfold:
      forall alpha, y_a alpha = sup (fun x => exists beta, beta < alpha /\ x = x_a beta).
    Proof.
      intros alpha.
      unfold y_a, seq_as_set.
      apply po_antisym.
      apply PsupL.
      intros ? ?.
      reduce in H.
      destruct H.
      apply Psup.
      reduce.
      exists (ordd_to_ordk x).
      split.
        unfold ordd_to_ordk, ordd_to_ordk_0.
        apply (proj2_sig x).
        apply H.
      apply PsupL.
      intros ? ?.
      reduce in H.
      destruct H.
      destruct H.
      apply Psup.
      reduce.
      admit.
    Admitted.

    Lemma x_a_unfold:
      forall alpha, x_a alpha = fixpyy alpha (y_a alpha).
    Proof.
      intros.
      unfold x_a.
      rewrite (Fix_eq ordd_lt_wf _).
      unfold y_a.
      reflexivity.
      intros.
      f_equal.
      f_equal.
      f_equal.
      extensionality x0; apply H.
    Qed.

    Instance : Proper ((=) ==> (=) ==> (=)) fixpyy.
      reduce.
      unfold fixpyy.
      unfold fixpy.
    Admitted.

    Instance x_a_is_seq : Seq x_a.
    Proof.
      split.
      unfold Proper.
      unfold respectful.
      induction x using well_founded_ordk_lt_ind.
      intros.
      rewrite x_a_unfold.
      rewrite x_a_unfold.
      unfold y_a.
      f_equiv.
      assumption.
        apply po_antisym.
        apply PsupL.
        unfold Upper_Bound.
        intros s H1.
        destruct H1.
        rewrite H1.
        apply Psup.
        reduce.
        destruct H0.
        assert (x <wf= y). assumption.
        exists (lift_alpha_to_beta x0 H3).
        apply H.
        apply (proj2_sig x0).
        unfold ordd_to_ordk.
        unfold lift_alpha_to_beta.
        unfold ordd_to_ordk_0.
        split; apply ord_le_refl.
        apply PsupL.
        unfold Upper_Bound.
        intros.
        destruct H1.
        rewrite H1.
        apply Psup.
        reduce.
        destruct H0.
        assert (y <wf= x). assumption.
        exists (lift_alpha_to_beta x0 H3).
        apply H.
        apply ord_lt_le_trans with y.
        apply (proj2_sig x0).
        apply H3.
        unfold ordd_to_ordk.
        unfold lift_alpha_to_beta.
        unfold ordd_to_ordk_0.
        split; apply ord_le_refl.
    Qed.


    Lemma y_a_zero:
      y_a zerok = ⊥.
    Proof.
      intros.
      unfold y_a.
      apply po_antisym.
      apply PsupL.
      intros s H0.
      reduce in H0.
      destruct H0.
      destruct x.
      absurd (x < zero).
        apply ord_lt_not_zero.
        apply l.
      apply Pinf.
      reduce.
      trivial.
    Qed.

    Lemma x_a_zero_case :
      x_a zerok = fixpyy zerok ⊥.
    Proof.
      rewrite x_a_unfold.
      f_equiv.
      apply y_a_zero.
    Qed.

    Lemma lemma34_0_aux:
      forall alpha beta,
        le_a beta (y_a beta) (f (y_a beta)) ->
        beta < alpha ->
        (equiv_a beta (x_a beta) (x_a alpha)) ->
        (x_a beta) ≤ (x_a alpha).
    Proof.
      intros.
      rewrite x_a_unfold.
      apply lemma32_7.
      apply AllAlphaOrd.
      assumption.
      unfold closed_interval_a.
      rewrite <- x_a_unfold.
      assumption.
    Qed.

    Definition ordk_to_succ_ordd: 
      forall alpha : ordk, 
        ordd (orddd_to_wf_ord (ordd_to_orddd (succk alpha))).
      intro.
      exists alpha.
      apply ord_lt_succ_alpha.
    Defined.

    (* very similar to x_a_succ_case *)
    Lemma y_a_succ_case_aux:
      forall alpha, 
        (forall beta, beta < alpha -> le_a beta (y_a beta) (f (y_a beta))) ->
        (forall beta, beta < alpha -> equiv_a beta (x_a beta) (x_a alpha)) ->
        y_a (succk alpha) = fixpyy alpha (y_a alpha).
    Proof.
      intros.
      unfold y_a at 1.
      rewrite <- x_a_unfold.
      apply po_antisym.
      apply PsupL.
      intros s H2.
      reduce in H2.
      destruct H2.
      rewrite H1.
      pose proof (proj2_sig x).
      simpl in H2.
      destruct H2.
      apply ord_le_succ_pd_right in H2.
      destruct (proj1 (wf_ord_lt_eq_cases _ _) H2).
        apply lemma34_0_aux.
          apply H.
          assumption.
        assumption.
        apply H0.
        assumption.
        assert ((ordd_to_ordk x) = alpha).
          unfold ordd_to_ordk. unfold ordd_to_ordk_0. assumption.
        rewrite H4.
        reflexivity.
      apply Psup.
      reduce.
      exists (ordk_to_succ_ordd alpha).
      assert (alpha = ordd_to_ordk (ordk_to_succ_ordd alpha)).
        unfold ordd_to_ordk. unfold ordd_to_ordk_0. reduce. simpl. split; apply ord_le_refl.
      rewrite <- H1.
      reflexivity.
    Qed.

    Lemma x_a_unfold_2_aux: 
      forall alpha, 
        (forall beta, beta < alpha -> le_a beta (y_a beta) (f (y_a beta))) ->
        (forall beta, beta < alpha -> equiv_a beta (x_a beta) (x_a alpha)) ->
        x_a alpha = y_a (succk alpha).
    Proof.
      intro.
      rewrite x_a_unfold.
      symmetry.
      apply y_a_succ_case_aux; assumption.
    Qed.

    Lemma x_a_succ_case_aux:
      forall alpha, 
        (forall beta, beta < alpha -> le_a beta (y_a beta) (f (y_a beta))) ->
        (forall beta, beta < alpha -> equiv_a beta (x_a beta) (x_a alpha)) ->
        x_a (succk alpha) = fixpyy (succk alpha) (x_a alpha).
    Proof.
      intros.
      rewrite x_a_unfold.
      f_equiv.
      symmetry.
      apply x_a_unfold_2_aux; assumption.
    Qed.

    Instance ordd_to_ordk_proper {alpha} : Proper ((=)==>(=)) (@ordd_to_ordk alpha).
      reduce.
      unfold ordd_to_ordk, ordd_to_ordk_0; split; apply H.
    Qed.

    (* not in the paper *)
    Lemma eq_a_le_b_eq_a_trans : 
      forall alpha beta,
        alpha < beta ->
        forall x y z, 
          equiv_a alpha x z -> 
          le_a beta z y -> 
          equiv_a alpha x y.
    Proof.
      intros alpha beta alpha_lt_beta x y z.
      intros.
      transitivity z.
      assumption.
      apply (axiom1 alpha beta alpha_lt_beta). assumption.
    Qed.

    Lemma lemma34_0:
      forall alpha, 
        le_a alpha (y_a alpha) (f (y_a alpha)) /\ 
        (forall beta, beta < alpha -> equiv_a beta (x_a beta) (x_a alpha)) /\
        Least (le_sq) (closed_interval_a alpha (x_a alpha)) (x_a alpha) /\
        equiv_a alpha (x_a alpha) (f (x_a alpha)).
    Proof.
      intros.
      induction alpha using well_founded_ordk_lt_ind.
      induction alpha using ordd_ind.
      - assert (HH: le_a zerok (y_a zerok) (f (y_a zerok))).
          rewrite y_a_zero at 1; apply lemma24.
        split.
          apply HH.
        split.
          intros beta beta_lt_zero.
          contradict beta_lt_zero.
            apply ord_lt_not_zero.
        split.
          intros beta H1.
          rewrite x_a_unfold.
          apply lemma32_7.
          apply AllAlphaOrd.
          apply HH.
          rewrite <- x_a_unfold.
          assumption.
          rewrite x_a_unfold.
          apply lemma32_4.
          exact zerok.
       - assert (y_a_succ_case : y_a (succk alpha) = fixpyy alpha (y_a alpha)).
            apply y_a_succ_case_aux.
              intros.
              apply H.
              apply ord_lt_succ_right; assumption.
              apply H.
              apply ord_lt_succ_alpha.
          assert (x_a_succ_case: x_a (succk alpha) = fixpyy (succk alpha) (x_a alpha)).
            apply x_a_succ_case_aux.
            intros; apply H; apply ord_lt_succ_right; assumption.
            intros; apply H; [ apply ord_lt_succ_alpha | assumption ].
          assert (x_a_unfold_2: x_a alpha = y_a (succk alpha)).
            apply x_a_unfold_2_aux.
            intros; apply H; apply ord_lt_succ_right; assumption.
            intros; apply H; [ apply ord_lt_succ_alpha | assumption ].
          assert (HH: le_a (succk alpha) (y_a (succk alpha)) (f (y_a (succk alpha)))).
            rewrite y_a_succ_case.
            apply remark33.
            apply AllAlphaOrd.
            apply IHalpha.
            intros; apply H.
            apply ord_lt_succ_right; apply H0.
            exact zerok.
          split.
            apply HH.
          split.
            intros.
            apply eq_a_le_b_eq_a_trans with (succk alpha) (x_a alpha).
            assumption.
            case (proj1 (wf_ord_lt_eq_cases beta alpha)).
              destruct H0.
              apply ord_le_succ_pd_right in H0.
              apply H0.
              intro.
              apply IHalpha.
              intros.
              apply H.
              apply ord_lt_succ_right.
              assumption.
              apply H1.
              intro.
              assert (beta = alpha). apply H1.
              rewrite H2 at 2.
              reflexivity.
              rewrite x_a_succ_case.
              apply lemma32_5.
              apply AllAlphaOrd.
              rewrite x_a_unfold_2.
              exact HH.
              exact (succk alpha).
          split.
            intros beta H1.
            rewrite x_a_unfold.
            apply lemma32_7.
            apply AllAlphaOrd.
            apply HH.
            rewrite <- x_a_unfold.
            apply H1.
            rewrite x_a_unfold.
            apply lemma32_4.
            exact alpha.
        - assert (Heq : forall beta, beta < limitk f0 h1 h2 -> equiv_a beta (x_a beta) (y_a (limitk f0 h1 h2))).
            intros beta beta_l_limit.
            rewrite y_a_unfold.
            apply lemma27a.
            apply x_a_is_seq.
            apply H.
            intros.
            apply H; assumption.
            assumption.
          assert (Hyeq: forall beta, beta < limitk f0 h1 h2 -> equiv_a beta (y_a (limitk f0 h1 h2)) (f (y_a (limitk f0 h1 h2)))).
            intros.
            transitivity (f (x_a beta)).
              transitivity (x_a beta).
                  symmetry.
                  apply Heq; apply H1.
              apply H; apply H1.
              apply aorder_preserving_equiv_alpha.
                apply AllAlphaOrd.
              apply Heq; apply H1.
          assert (HH: le_a (limitk f0 h1 h2) (y_a (limitk f0 h1 h2)) (f (y_a (limitk f0 h1 h2)))).
              apply lemma22.
              apply Hyeq.
              rewrite y_a_unfold at 1.
              apply lemma27b.
              apply x_a_is_seq.
              apply H.
              intros.
              apply H; assumption.
              intros beta beta_l_limit.
              rewrite <- y_a_unfold at 1.
              apply Hyeq; assumption.
          split.
            apply HH.
          split.
            intros.
            transitivity (y_a (limitk f0 h1 h2)).
            apply Heq; assumption.
            apply axiom1 with (limitk f0 h1 h2).
            assumption.
            rewrite x_a_unfold.
            apply lemma32_5.
            apply AllAlphaOrd.
            exact HH.
          split.
            intros beta H1.
            rewrite x_a_unfold.
            apply lemma32_7.
            apply AllAlphaOrd.
            apply HH.
            rewrite <- x_a_unfold.
            apply H1.
            rewrite x_a_unfold.
            apply lemma32_4.
            exact (f0 0%nat).
    Qed.

    Lemma lemma34_1 :
      forall alpha beta,
        beta < alpha -> 
        equiv_a beta (x_a beta) (y_a alpha).
    Proof.
      intros alpha beta beta_l_limit.
      rewrite y_a_unfold.
      apply lemma27a.
      apply x_a_is_seq.
      intros.
      apply lemma34_0.
      intros.
      apply lemma34_0; assumption.
      assumption.
    Qed.

    (* very similar to x_a_succ_case *)
    Lemma y_a_succ_case:
      forall alpha, y_a (succk alpha) = fixpyy alpha (y_a alpha).
    Proof.
      intros.
      apply y_a_succ_case_aux.
      intros; apply lemma34_0.
      intros; apply lemma34_0.
      assumption.
    Qed.

    Lemma x_a_unfold_2 : 
      forall alpha, x_a alpha = y_a (succk alpha).
    Proof.
      intros.
      apply x_a_unfold_2_aux.
      intros; apply lemma34_0.
      intros; apply lemma34_0.
      assumption.
    Qed.


    Lemma x_a_succ_case :
      forall beta, x_a (succk beta) = fixpyy (succk beta) (x_a beta).
    Proof.
      intros.
      apply x_a_succ_case_aux.
      intros; apply lemma34_0.
      intros; apply lemma34_0.
      assumption.
    Qed.

    Definition x_inf := sup (seq_as_set x_a). (* sup (fun x => exists beta : ordk, beta < kappa /\ x = x_a beta). *)

    Lemma x_inf_eq_x_a : 
      forall alpha, 
        equiv_a alpha x_inf (x_a alpha).
    Proof.
    Admitted.
(*
      intros.
      symmetry.
      Check lemma27a.
      symmetry.
      rewrite ordk_rewrite at 1.
      refine (lemma320 x_a _ _ _).
      apply lemma66_1.
      intros.
      apply lemma321_1.
      assumption.
      apply lemma66_1.
    Qed.
*)
    Lemma x_inf_fixedpoint: FixedPoint f x_inf.
    Proof.
      intros.
      unfold FixedPoint.
      apply axiom2.
      intro.
      transitivity (f (x_a alpha)).
      apply aorder_preserving_equiv_alpha.
      apply AllAlphaOrd.
      apply x_inf_eq_x_a.
      transitivity (x_a alpha).
      symmetry.
      rewrite x_a_unfold.
      apply lemma32_4.
      exact alpha.
      symmetry.
      apply x_inf_eq_x_a.
    Qed.

    Lemma x_inf_prefixedpoint: @PreFixedPoint A (le_sq) f x_inf.
    Proof.
      unfold PreFixedPoint.
      right.
      apply x_inf_fixedpoint.
    Qed.


    Lemma y_a_is_least:
      forall alpha,
        Least (le_a alpha) (interval_a alpha (y_a alpha)) (y_a alpha).
    Proof.
      intro.
      reduce.
      induction alpha using ordd_ind.
       + rewrite y_a_zero.
         apply lemma24.
       + rewrite y_a_succ_case.
        apply lemma32_8.
        apply AllAlphaOrd.
        apply lemma34_0.
        unfold closed_interval_a.
        rewrite <- y_a_succ_case.
        apply H.
        apply ord_lt_succ_alpha.
       + apply lemma22.
        intros.
        apply H; assumption.
        rewrite y_a_unfold.
        apply lemma27b.
        apply x_a_is_seq.
        intros; apply lemma34_0.
        intros; apply lemma34_0; assumption.
        intros beta ?;
        rewrite <- y_a_unfold.
        apply H.
        assumption.
    Qed.


    (* this is slightly different from the original proof in the paper. 
       uses well-founded induction and y_a_is_least lemma. *)
    Lemma lemma34_2:
      forall alpha : ordk, 
      forall y, 
        @PreFixedPoint A le_sq f y ->
        (forall gamma : ordk, gamma <wf= alpha -> le_a gamma (x_a gamma) y) \/ 
        (exists gamma : ordk, (gamma < alpha) /\ lt_a gamma (x_a gamma) y).
    Proof.
      intros alpha y Ppre.
      induction alpha using well_founded_ordk_lt_ind.
      apply ord_le_le_3 in H.
      destruct H.
        assert (forall n : ordd kappa_as_orkd, n < alpha -> 
            (forall gamma : ordk, gamma <wf= n -> equiv_a gamma (x_a gamma) y) \/ 
            (exists gamma : ordk, gamma <wf= n /\ lt_a gamma (x_a gamma) y)).
          intros.
          pose proof (H n H0).
          assert (forall gamma : ordk, gamma <wf= n -> equiv_a gamma (x_a gamma) y \/ lt_a gamma (x_a gamma) y).
            intros.
            apply or_comm.
            apply le_a_lt_eq_cases.
            apply H1.
            assumption.
          apply ord_le_le_3 in H2.
          assumption.
        apply ord_le_le_3 in H0.
        destruct H0.
          left.
          intros.

          assert (Hya_le : le_a alpha (y_a alpha) y).
            apply y_a_is_least.
            unfold interval_a.
            intros.
            transitivity (x_a beta).
            symmetry.
            apply lemma34_1.
            assumption.
            apply H0 with beta.
              assumption.
              apply ord_le_refl.

          apply eq_a_le_a_trans with (x_a alpha).
            destruct (proj1 (wf_ord_lt_eq_cases _ _) H1).
              apply lemma34_0.
              assumption.
              assert (gamma = alpha). assumption.
              rewrite H3; reflexivity.
            refine (le_b_le_a_2 alpha _ _ _ _ H1).
            (* le_a alpha (x_a alpha) y *)
            rewrite x_a_unfold.
            apply lemma32_3.
              apply AllAlphaOrd.
              apply lemma34_0.
              apply Hya_le.
              (* le_a alpha (f y) y *)
              apply le_sq_equiv_le_a.
                assumption.
                intros.
                destruct Ppre.
                  destruct H3 as [x H3].
                  case (wf_ord_lt_ge_cases gamma0 x).
                    intro.
                    apply axiom1 with x.
                      assumption.
                      apply H3.
                    intro.
                    absurd (lt_a x (f y) y).
                      intro.
                      destruct H5.
                      apply H6.
                      symmetry.
                      transitivity (y_a alpha).
                        symmetry.
                        apply axiom1 with alpha.
                           apply ord_le_lt_trans with gamma0; assumption.
                          apply Hya_le.
                          transitivity (f (y_a alpha)).
                             apply axiom1 with alpha.
                             apply ord_le_lt_trans with gamma0; assumption.
                             apply lemma34_0.
                          apply axiom1 with alpha.
                          apply ord_le_lt_trans with gamma0; assumption.
                          apply alpha_order_preserving.
                          apply AllAlphaOrd.
                          apply Hya_le.
                      assumption.
                  rewrite H3.
                  reflexivity.
          right.
            destruct H0 as [n [n_alpha [gamma [gamma_n lt_gamma]]]].
            exists gamma.
            split.
              apply ord_le_lt_trans with n; assumption.
              assumption.
        right.
          destruct H.
          destruct H.
          destruct H0.
          exists x0.
          split.
          apply ord_lt_trans with x.
          apply H0.
          apply H.
          apply H0.
    Qed.

    Theorem fixpoint_theorem:
      Least (le_sq) (@PreFixedPoint A (le_sq) f) x_inf.
    Proof.
      intro.
      unfold Least.
      intros.
      unfold le_sq.
      unfold lt_sq.
      unfold PreFixedPoint in *.
      unfold le in H.
      pose proof (fun alpha => lemma34_2 alpha y H).
      apply ord_le_le_2 in H0.
      destruct H0.
        right.
        apply join_le_a_eq.
        intro.
        apply eq_a_le_a_trans with (x_a alpha).
        apply (x_inf_eq_x_a alpha).
        apply H0 with alpha.
        apply ord_le_refl.
        left.
        destruct H0 as [alpha [gamma [gamma_lt H2]]].
        exists gamma.
        apply eq_a_lt_a_trans with (x_a gamma).
        apply (x_inf_eq_x_a gamma).
        apply H2.
    Qed.

    End lemma34.

  End FixedPointTheorem.

End Stratified.
