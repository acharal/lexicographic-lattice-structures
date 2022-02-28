(************************************************************************)
(* Copyright (c) 2010, Martijn Vermaat <martijn@vermaat.name>           *)
(*                                                                      *)
(* Licensed under the MIT license, see the LICENSE file or              *)
(* http://en.wikipedia.org/wiki/Mit_license                             *)
(************************************************************************)


(** This library defines the type [wf_ord] of well-formed tree ordinals.
   The well-formed tree ordinals are a subset of [ord] (defined in the
   [Ordinal] library) where we restrict the arguments of [Limit] constructors
   to be monotone. *)


Require Export Ordinal.


Set Implicit Arguments.


Delimit Scope wf_ord_scope with wf_ord.
Open Scope ord_scope.
Open Scope wf_ord_scope.


(** Well-formed ordinals are those whose the limit functions are monotone. *)
Fixpoint wf alpha : Prop :=
  match alpha with
  | Zero      => True
  | Succ beta => wf beta
  | Limit f   => (forall n, wf (f n)) /\ forall n m, (n < m)%nat -> f n < f m
  end.

(** Addition of well-formed ordinals yields a well-formed ordinal. *)
Lemma add_wf :
  forall alpha beta,
    wf alpha ->
    wf beta ->
    wf (add alpha beta).
Proof.
intros alpha beta.
revert beta.
induction beta as [| beta IH | f IH]; intros WFa WFb.
assumption.
apply IH; assumption.
split.
intro n.
apply IH.
assumption.
apply WFb.
intros n m H.
apply ord_lt_add.
apply WFb.
assumption.
Qed.

(** All natural numbers are well-formed. *)
Lemma nat_wf :
  forall (n : nat), wf n.
Proof.
induction n.
exact I.
assumption.
Qed.

(** We now define the well-formed ordinals [wf_ord] as a subset of the
   ordinals [ord] by the [wf] condition. *)

Definition wf_ord : Set := sig wf.

(** Image of well-formed ordinals in ordinals. *)

Definition wf_ord_as_ord (alpha : wf_ord) : ord :=
  proj1_sig alpha.

Coercion wf_ord_as_ord : wf_ord >-> ord.

(** For any well-formed alpha <= zero, alpha = zero.
   (We would like to leave out the explicit coercion in the statement of
   this lemma.) *)
Lemma wf_ord_le_zero_right :
  forall alpha : wf_ord,
    alpha <= Zero ->
    wf_ord_as_ord alpha = Zero.
Proof.
intros alpha H.
destruct alpha as [alpha' G].
simpl in H.
induction alpha' as [| | f IH].
reflexivity.
elim (ord_le_not_succ_zero H).
elimtype False.
apply ord_lt_zero_zero.
simpl in G.
destruct G as [Gh Gnm].
specialize Gnm with (n:=1).
pose proof (Gh 1) as G1.
pose proof (Gh 2) as G2.
inversion_clear H.
pattern Zero at 1.
rewrite <- (IH 1) with G1.
rewrite <- (IH 2) with G2.
apply Gnm.
constructor.
apply H0.
apply H0.
Qed.

Lemma wf_ord_lt_limit_is_bound : 
  forall (f: nat->ord) (n : nat), 
      wf (Limit f) -> 
      f n < Limit f.
Proof.
intros f n H.
apply ord_lt_limit_right with (n:=S n).
apply H.
auto.
Qed.


Lemma wf_ord_wf_succ_implies_wf : 
    forall w, wf (Succ w) -> wf w.
Proof. 
  intros. induction w ; trivial.
Qed.

Lemma wf_ord_wf_limit_implies_wf : 
    forall f, wf (Limit f) -> 
    forall n : nat, wf (f n).
Proof.
  intros f Hwf n.
  destruct Hwf as [Hwf _].
  specialize Hwf with (n). 
  exact Hwf.
Qed.

(** Definitions of well-formed ordinals. *)

Definition zero : wf_ord := exist wf Zero I.

(*
(* TODO: the let bindings don't play nice with alpha conversion *)
Definition succ (alpha : wf_ord) : ord :=
  let (alpha', H) := alpha in
    exist g'' (Succ alpha') H.
*)
Definition succ (alpha : wf_ord) : wf_ord :=
(*  let (alpha', H) := alpha in
    exist wf (Succ alpha') H.*)
  exist wf (Succ (proj1_sig alpha)) (proj2_sig alpha).

Definition limit (f : nat -> wf_ord) H : wf_ord :=
  exist wf
    (Limit (fun n => proj1_sig (f n)))
    (conj (fun n => proj2_sig (f n)) H).

Definition is_succ (o : wf_ord) : Prop :=
  match proj1_sig o with
  | Succ _ => True
  | _      => False
  end.

Definition is_limit (o : wf_ord) : Prop :=
  match proj1_sig o with
  | Limit _ => True
  | _       => False
  end.

(** We lift the [<=], [<], and [==] relations to [wf_ord]. *)

Definition wf_ord_le (alpha beta : wf_ord) : Prop :=
  proj1_sig alpha <= proj1_sig beta.
Infix " <wf= " := wf_ord_le (no associativity, at level 75) : wf_ord_scope.

Definition wf_ord_lt (alpha beta : wf_ord) : Prop :=
  proj1_sig alpha < proj1_sig beta.
Infix " <wf " := wf_ord_lt (no associativity, at level 75) : wf_ord_scope.

Definition wf_ord_eq (alpha beta : wf_ord) : Prop :=
  proj1_sig alpha == proj1_sig beta.
Infix " =wf= " := wf_ord_eq (no associativity, at level 75) : wf_ord_scope.


Lemma wf_ord_lt_wf_limit_is_bound:
  forall f n h,
    f n <wf limit f h.
Proof.
  intros.
  apply wf_ord_lt_limit_is_bound with (f:= fun (n:nat) => proj1_sig (f n)).
  apply (conj (fun n => proj2_sig (f n)) h).
Qed.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Instance wf_ord_eq_wd : Equivalence (wf_ord_eq).
unfold wf_ord_eq.
split.
unfold Reflexive; intros; apply ord_eq_refl.
unfold Symmetric; intros; apply ord_eq_symm; assumption.
unfold Transitive; intros; transitivity (proj1_sig y); assumption.
Qed.

Lemma wf_ord_lt_wf_ord_le :
  forall n m, n <wf m -> n <wf= m.
Proof.
  exact ord_lt_ord_le.
Qed.

Hint Resolve wf_ord_lt_wf_ord_le.

Lemma wf_ord_eq_ord_eq :
  forall (alpha beta : wf_ord),
    alpha = beta ->
    proj1_sig alpha = proj1_sig beta.
Proof.
intros alpha beta H.
rewrite H.
reflexivity.
Qed.

Lemma wf_ord_lt_wf : well_founded wf_ord_lt.
Proof.
  red in |- *.
  cut (forall (n a : wf_ord), wf_ord_lt a n -> Acc wf_ord_lt a).
  intros H1 a.  refine (H1 (succ a) _ _). unfold wf_ord_lt. simpl. exists (inl tt). apply ord_le_refl.
  intro n. destruct n. induction x.
  intros. absurd (a <wf exist wf Zero w). intro.  destruct H. revert H. 
  apply ord_le_not_pd_right. apply Ord_le_Zero. assumption.
  intros. apply Acc_intro.
  unfold wf_ord in |- *. intros b H1. apply IHx with (w:=wf_ord_wf_succ_implies_wf x w).
  unfold wf_ord_lt. simpl. 
  apply ord_lt_le_trans with (beta:=a). apply H1.
  destruct H. apply ord_le_succ_pd_right in H. apply H.
  intros. apply Acc_intro.
  unfold wf_ord_lt in |- *. intros b H2. 
  destruct H0. destruct x.
  refine (H x (wf_ord_wf_limit_implies_wf w x) _ _).
  apply ord_lt_le_trans with (beta:=a).
  apply H2.  simpl. simpl in H0. apply ord_le_pd_right in H0. apply H0.
Defined.

Hint Resolve wf_ord_lt_wf.

Lemma well_founded_wf_ord_lt_ind :
  forall (P:wf_ord -> Prop), (forall n, (forall m, (m <wf n) -> P m) -> P n) -> forall n, P n.
Proof.
  exact (well_founded_ind wf_ord_lt_wf).
Defined.

Lemma well_founded_wf_ord_lt_rec :
  forall (P:wf_ord -> Set), (forall n, (forall m, (m <wf n) -> P m) -> P n) -> forall n, P n.
Proof.
  exact (well_founded_induction wf_ord_lt_wf).
Defined.

Lemma well_founded_wf_ord_lt_rect :
  forall (P:wf_ord -> Type), (forall n, (forall m, (m <wf n) -> P m) -> P n) -> forall n, P n.
Proof.
  exact (well_founded_induction_type wf_ord_lt_wf).
Defined.


(** The image of the natural numbers in the ordinals can of course be
   lifted to well-formed ordinals. *)

Definition nat_as_wf_ord (n : nat) : wf_ord :=
  exist wf n (nat_wf n).

Coercion nat_as_wf_ord : nat >-> wf_ord.

(** A well-formed definition of omega with a proof that it is really greater
   than all natural numbers. *)

Definition wf_omega := limit nat_as_wf_ord lt_implies_ord_lt.

Lemma n_le_omega : forall (n : nat), n <wf= wf_omega.
Proof.
destruct n as [| n]; unfold wf_ord_le; simpl.
constructor.
apply Ord_le_Succ with (i := existT (fun (n:nat) => pd_type n) (S n) (inl (pd_type n) tt)).
apply ord_le_refl.
Qed.

Lemma n_lt_omega : forall (n : nat), n <wf wf_omega.
Proof.
intro n.
exists (existT (fun (n:nat) => pd_type n) (S n) (inl (pd_type n) tt)).
apply ord_le_refl.
Qed.

(** Some inversion lemma for alpha <= omega. *)
Lemma ord_le_omega_elim :
  forall alpha,
    alpha <wf= wf_omega ->
    alpha <wf wf_omega \/ alpha =wf= wf_omega.
Proof.
intros alpha H. unfold wf_ord_lt.
destruct alpha as [alpha wf_alpha].
induction alpha as [| alpha IH | f IH].
left.
exists (existT (fun (n:nat) => pd_type n) 1 (inl _ tt)).
constructor.
left.
destruct IH with wf_alpha as [[[n j] H1] | H1].
apply (ord_le_succ_left H).
simpl in H1.
exists (existT (fun (n:nat) => pd_type n) (S n) (inl _ tt)); simpl.
destruct n as [| n].
elim j.
destruct j as [[] | j]; simpl in H1; apply ord_le_succ_intro.
assumption.
apply ord_le_pd_right with j.
assumption.
contradiction ord_le_not_pd_right with (Succ alpha) omega (inl (pd_type alpha) tt).
apply H1.
right.
split.
assumption.
simpl.
constructor.
(* TODO: cleanup, below is a mess *)
induction n as [| n IHn]; simpl.
constructor.
destruct wf_alpha as [LL GG].
pose proof (GG n) as G.
destruct G with (S n) as [i J]; clear G.
auto.
apply Ord_le_Succ with (existT (fun (n:nat) => pd_type (f n)) (S n) i).
simpl.
apply ord_le_trans with (f n).
induction n as [| n IHnn]; simpl.
constructor.
pose proof (GG n) as G.
destruct G with (S n) as [k K]; clear G.
auto.
apply Ord_le_Succ with k.
apply ord_le_trans with (f n).
apply IHnn with k.
apply ord_le_succ_left.
assumption.
assumption.
assumption.
assumption.
Qed.


Lemma wf_ord_ind : 
  forall P : wf_ord -> Prop,
       P zero ->
       (forall o : wf_ord, P o -> P (succ o)) ->
       (forall f : nat -> wf_ord, 
          forall h: (forall x m : nat, (x < m)%nat -> proj1_sig (f x) < proj1_sig (f m)),
          (forall n : nat, P (f n)) -> P (limit f h)) ->
       forall o : wf_ord, P o.
Proof.
  intros.
  destruct o.
  induction x.
  unfold wf in w.
  destruct w.
  assumption.
  apply H0 with (o:=exist wf x w).
  apply IHx.
  simpl in w.
  destruct w as [ww wh].
  specialize H1 with (f:=fun n => exist wf (o n) (ww n)) (h:=wh).
  unfold limit in H1.
  simpl in H1.
  apply H1.
  intro.
  apply H2.
Defined.

Definition wf_ord_rect : 
  forall P : wf_ord -> Type,
       P zero ->
       (forall o : wf_ord, P o -> P (succ o)) ->
       (forall f : nat -> wf_ord, 
          forall h: (forall x m : nat, (x < m)%nat -> proj1_sig (f x) < proj1_sig (f m)),
          (forall n : nat, P (f n)) -> P (limit f h)) ->
       forall o : wf_ord, P o.
intros.
destruct o as [x oo].
refine (ord_rect (fun (o:ord) => forall h, P (exist wf o h)) _ _ _ _ _).
intro.
destruct h.
apply X.
intros.
refine (X0 _ (X2 h)).
intros.
destruct h as [ww wh].
apply (X1 (fun n => exist wf (o n) (ww n)) wh (fun n => X2 n (ww n))).
Defined.

Definition wf_ord_rec :
  forall P : wf_ord -> Set,
     P zero ->
     (forall o : wf_ord, P o -> P (succ o)) ->
     (forall f : nat -> wf_ord, 
        forall h: (forall x m : nat, (x < m)%nat -> proj1_sig (f x) < proj1_sig (f m)),
        (forall n : nat, P (f n)) -> P (limit f h)) ->
     forall o : wf_ord, P o.
intros.
exact (wf_ord_rect P H H0 H1 o).
Defined.

Require Import Coq.Logic.Classical_Prop.

Lemma ord_le_le_2 :
  forall (A:Type) (R Q : A->Prop),
    (forall n, R(n) \/ Q(n)) ->
    (forall n, R(n)) \/ exists n, Q(n).
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
    intro.
    destruct (H n).
      left. assumption.
      right.  exists n. assumption.
Qed.

Lemma ord_le_le_3 :
  forall (A:Type) (P R Q : A->Prop),
    (forall n, P(n) -> R(n) \/ Q(n)) -> 
    (forall n, P(n) -> R(n)) \/ exists n, (P(n) /\ Q(n)).
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

Lemma pd_is_wf: 
    forall (o : ord) (i: pd_type o), 
    wf o -> wf (pd o i). 
Proof.
  intros.
  induction o.
  destruct i.
  induction i.
  destruct a.
  apply H.
  apply IHo.
  apply H.
  induction i.
  apply H0.
  apply H.
Qed.

Lemma wf_ord_pd_is_wf:
    forall (o : wf_ord) (i: pd_type o), wf (pd o i).
Proof.
    intros.
    apply pd_is_wf.
    apply (proj2_sig o).
Qed.

Definition wf_pd (alpha : wf_ord) : pd_type alpha -> wf_ord.
intro.
exists (pd alpha H).
apply wf_ord_pd_is_wf.
Defined.

Require Import Coq.Logic.Classical_Pred_Type.


Lemma wf_ord_lt_eq_cases: 
  forall x y, 
    x <wf= y <-> 
    x <wf y \/ x =wf= y.
Proof.
intros x y.
  split.
  - revert y.
    induction x using wf_ord_ind.
    * (* x = zero *) intros y H.
    induction y using wf_ord_ind.
    ++ right. reflexivity.
    ++ left. exists (inl (pd_type y) tt). constructor.
    ++ assert (forall n : nat, zero =wf= f n \/ zero <wf f n).
          intro n.
          apply or_comm.
          apply H0.
          constructor.
        apply ord_le_le_2 in H1.
        destruct H1.
          right. constructor. constructor. constructor. apply H1.
          left. destruct H1 as [x [x0 H1]].
             exists (existT (fun (n:nat) => pd_type (f n)) x x0). assumption.
    * (* x = succ *) intros y H.
    inversion_clear H.
    destruct (IHx (wf_pd y i) H0).
    + left; exists i; apply ord_lt_le_succ_right; assumption.
    + induction y using wf_ord_ind.
      ++ (* y = zero *) destruct i.
      ++ (* y = succ *) induction i.
          +++ (* immediate predecessor, if x = pred y then should be equal succ x = y *) 
              right; constructor; 
              apply ord_le_succ_intro; 
              destruct a; 
              apply H.
          +++ (* not immediate *) 
              left; destruct (IHy b H0 H).
              apply ord_lt_trans with y. assumption. apply ord_lt_succ_alpha.
              destruct H1. apply ord_le_lt_trans with y. apply H1. apply ord_lt_succ_alpha.
      ++ (* y = limit *) destruct i.
          simpl in *.
          destruct (H1 x0 p H0 H).
            left; apply ord_lt_limit_right with x0; assumption.
            left. apply ord_le_lt_trans with (f x0).
            apply H2.
            apply ord_le_lt_trans with ((fun n : nat => proj1_sig (f n)) x0).
            apply ord_le_refl.
            apply wf_ord_lt_limit_is_bound with (f:=(fun n : nat => proj1_sig (f n))).
            apply (proj2_sig (limit f h)).
    * (* x = limit *) intros.
    assert (forall (n: nat), f n <wf y \/ f n =wf= y).
      intros.
      apply (H n).
      inversion_clear H0.
      apply H1.
    apply ord_le_le_2 in H1.
    destruct H1.
      (*
      assert (forall (n: nat), exists i, f n <= pd y i).
        intros.
        destruct (H1 n).
        exists x.
        assumption. *)
      assert (exists i, forall (n:nat), f n <= pd y i).
        induction y using wf_ord_ind.
        destruct (H1 0). destruct x.
        exists (inl tt).
          intro.
          destruct (H1 n).
          apply ord_le_succ_pd_right in H2.
          apply H2.
        specialize H2 with 0.
        admit.
      destruct H2.
      left; exists x; constructor; apply H2.
      right.
        constructor.
          constructor.
          intros.
          inversion_clear H0.
          apply H2.
          destruct H1.
          destruct H1.
          apply ord_le_trans with (f x).
          assumption.
          apply ord_le_limit_is_bound with (f:=(fun n: nat => proj1_sig (f n))).
  - intro H. case H.
    intro H1. apply ord_lt_ord_le. apply H1.
    intro H1. apply H1.
Admitted.

Lemma wf_ord_le_gt_cases : forall n m, n <wf= m \/ m <wf n.
Proof.
  intros n m.
  induction n using wf_ord_ind.
  left. constructor.
  case IHn.
  intro. apply wf_ord_lt_eq_cases in H.
  case H.
    intro H0. left. apply ord_lt_ord_le_succ. apply H0.
    intro H0. right. destruct H0. exists (inl (pd_type n) tt). apply H1.
  right. apply ord_lt_succ_right; assumption.
  apply ord_le_le_2 in H. case H.
  intros. left. constructor. apply H0.
  intros. destruct H0. right. apply ord_lt_limit_right with (n:=x).
  exact H0.
Qed.

Lemma wf_ord_lt_ge_cases : forall n m, n <wf m \/ m <wf= n.
Proof.
  intros n m. destruct (wf_ord_le_gt_cases m n); intuition.
Qed.

Lemma wf_ord_le_ge_cases : forall x y, x <wf= y \/ y <wf= x.
Proof.
  intros n m. destruct (wf_ord_le_gt_cases n m); intuition.
Qed.

Lemma wf_ord_lt_trichotomy : forall n m, 
    n <wf m \/ 
    n =wf= m \/ 
    m <wf n.
Proof.
  intros n m.
  generalize (wf_ord_le_gt_cases n m).
  rewrite wf_ord_lt_eq_cases.
  tauto.
Qed.


Close Scope wf_ord_scope.
Close Scope ord_scope.
