Require Export Ensembles.
Require Import Coq.Program.Program.
From LexLatStruct.Order Require Export PartialOrder.

Class Meet A := meet : A -> A -> A.
Class Join A := join : A -> A -> A.
Class Top A := top: A.
Class Bottom A := bottom: A.

Infix "⊓" := meet (at level 49, no associativity).
Infix "⊔" := join (at level 49, no associativity).

Notation "(⊓)" := meet (only parsing).
Notation "(⊔)" := join (only parsing).

Typeclasses Transparent Meet Join Top Bottom.

Class MeetSemiLatticeOrder {A:Type} `{Ae : Equiv A} (Ale: Le A) `{Meet A} : Prop :=
  { meet_lattice_ord :> PartialOrder (≤)
  ; meet_lb_l : forall x y, x ⊓ y ≤ x
  ; meet_lbl_r: forall x y, x ⊓ y ≤ y
  ; meet_glb  : forall x y z, z ≤ x -> z ≤ y -> z ≤ x ⊓ y }.


Class JoinSemiLatticeOrder {A:Type} `{Ae : Equiv A} (Ale: Le A) `{Join A} : Prop :=
  { join_lattice_ord :> PartialOrder (≤)
  ; join_lb_l : forall x y, x ≤ x ⊔ y
  ; join_lbl_r: forall x y, y ≤ x ⊔ y
  ; join_lub  : forall x y z, x ≤ z -> y ≤ z -> x ⊔ y ≤ z }.

Class LatticeOrder {A:Type} `{Ae : Equiv A} (Ale : Le A) `{Meet A} `{Join A} : Prop :=
  { lattice_order_meet :> MeetSemiLatticeOrder (≤)
  ; lattice_order_join :> JoinSemiLatticeOrder (≤) }.


Definition contains {U:Type} (S : Ensemble U) (x : U) : Prop := S x.

Infix "∈" := (flip contains) (at level 55, no associativity).

Definition subset {U:Type} (A B : Ensemble U) := forall x, x ∈ A -> x ∈ B.

Section Bounds.

Context {A : Type} `{Le A}.

Definition Upper_Bound (S: Ensemble A) (d:A) : Prop :=
  forall s, s ∈ S -> s ≤ d.

Definition Lower_Bound (S: Ensemble A) (d:A) : Prop :=
  forall s, s ∈ S -> d ≤ s.

Definition Upper_Set (S :  Ensemble A) : Ensemble A :=
  fun d => Upper_Bound S d.

Definition Lower_Set (S :  Ensemble A) : Ensemble A :=
  fun d => Lower_Bound S d.

End Bounds.

Class CompleteLattice {A: Type} `{Ae: Equiv A} (Ale: Le A) :=
  { ltord :> PartialOrder (≤)
  ; inf   : forall S : A -> Prop, A
  ; Pinf  : forall P : Ensemble A, Lower_Bound P (inf P)
  ; PinfL : forall P : Ensemble A, forall t, Lower_Bound P t -> t ≤ inf P }.

Section CompleteLattice.

Context {A} `{CompleteLattice A}.

Definition sup (S :  A -> Prop) : A := inf (Upper_Set S).

Lemma Psup : forall (S: A -> Prop), Upper_Bound S (sup S).
Proof.
intros Sl t C.
apply PinfL.
intros x Usl.
apply Usl.
apply C.
Qed.


Lemma PsupL : forall (S: A->Prop) t, Upper_Bound S t -> sup S ≤ t.
Proof.
intros S t Sl.
apply Pinf. red.
apply Sl.
Qed.

Lemma inf_rewrite : forall (S : A->Prop), inf S = sup (Lower_Set S).
Proof.
  intros.
  unfold sup.
  apply po_antisym.
  apply PinfL.
  reduce.
  reduce in H0.
  apply H0.
  apply Pinf.
  apply PinfL.
  reduce.
  apply Pinf.
  reduce.
  apply H1.
  apply H0.
Qed.

End CompleteLattice.

Definition bot {A} `{CompleteLattice A} := inf (fun _ => True).

Notation "⊥" := bot.
