
Require Import Ensembles.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Program.Program.
From LexLatStruct Require Import Order.
From LexLatStruct Require Import Fix.

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

Section CLattice.

Class CompleteLattice {A: Type} `{Ae: Equiv A} (Ale: Le A) :=
  { ltord :> PartialOrder (≤)
  ; inf   : forall S : A -> Prop, A
  ; Pinf  : forall P : Ensemble A, Lower_Bound P (inf P)
  ; PinfL : forall P : Ensemble A, forall t, Lower_Bound P t -> t ≤ inf P }.

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

Global Instance dual_is_clattice  : CompleteLattice (≥) := {
  inf := sup }.
apply dual_is_partialorder.
apply Psup.
apply PsupL.
Defined.

End CLattice.

Definition bot {A} `{CompleteLattice A} := inf (fun _ => True).

Notation "⊥" := bot.


Section SubLattices.

Context {A} {P : A->Prop} `{Equiv A} (leq : Le A)  `{!CompleteLattice leq}.

Variable PSinf: forall (S : Ensemble A), (forall t, S t -> P t) -> P (inf S).

Definition Embed (t : A) (p : P t) : { x : A | P x }.
exists t . apply p.
Defined.

Definition Extend (S : { x : A | P x } -> Prop) : A -> Prop.
intro l. apply (exists p:P l, S (Embed l p)).
Defined.

Lemma ExtendP : forall (S : {x : A | P x} -> Prop) t, Extend S t -> P t.
intros S t Ex. unfold Extend in Ex. unfold Embed in Ex. destruct Ex as [E _]. apply E.
Defined.

Global Instance subord_is_clattice : CompleteLattice (sub_leq (P:=P) leq).
  exists (fun (S : Ensemble { x : A | P x }) => Embed (inf (Extend S)) (PSinf (Extend S) (ExtendP S))).
  destruct CompleteLattice0. apply subord_is_partialorder. apply ltord0.
- intros P0 t C. unfold le. unfold sub_leq. unfold inf. refine (Pinf _ _ _).
  unfold contains. unfold Extend. unfold Embed. red. exists (proj2_sig t). destruct t. apply C.
- intros P0 t C. unfold le. unfold sub_leq. destruct CompleteLattice0. apply PinfL0. unfold le in C. unfold sub_leq in C. intros x Ex.
  unfold Extend in Ex. unfold Embed in Ex. destruct Ex as [Pt St]. specialize (C _ St). apply C.
Qed.


End SubLattices.

Section ArrowLattice.

Context {A B: Type} (leb: Le B) `{Equiv B} `{!CompleteLattice leb}.

Global Instance arrow_is_clattice : CompleteLattice (arrow_leq (A:=A)).
  exists (fun S => fun d :A => inf (fun x => exists f, f ∈ S /\ f d = x)).
  apply arrow_is_partialorder. apply ltord.
- destruct CompleteLattice0. unfold Lower_Bound in *. intros. unfold le in *. unfold arrow_leq in *. intros t.
  apply Pinf0. unfold contains. unfold flip. exists s. split.
  + assumption.
  + destruct ltord0. reflexivity.
- unfold le in *. unfold arrow_leq in *. destruct CompleteLattice0.
  intros. apply PinfL0. intro. unfold contains. unfold flip. intro.
  case H1. intro. intro. destruct H2. destruct ltord0. rewrite <- H3.
  apply H0. apply H2.
Defined.


End ArrowLattice.

Section ProdLattice.

Context {A} {B} {lea : Le A} {leb : Le B} `{Equiv A} `{!CompleteLattice lea} `{Equiv B}  `{!CompleteLattice leb}.

Instance : CompleteLattice (@prod_leq A B lea leb).
  exists (fun (S : Ensemble (A*B)) => (inf (fun (l1:A) => exists l2, S(l1,l2)), inf (fun (l2:B) => exists l1, S(l1,l2)))).
  apply prod_is_partialorder; apply ltord.
unfold Lower_Bound. unfold le. unfold prod_leq. simpl. intros P s Ps.
  split. apply Pinf. reduce. exists (snd s).
  assert (ss:= surjective_pairing). rewrite <- ss. apply Ps.
  apply Pinf. reduce. exists (fst s).
  assert (ss:= surjective_pairing). rewrite <- ss. apply Ps.
unfold Lower_Bound. unfold le. unfold prod_leq. simpl. intros P s Ps.
split. apply PinfL. unfold Lower_Bound. intros. reduce in H1. case H1. intros.
specialize Ps with (s0:=(pair s0 x)). apply Ps in H2. destruct H2. apply H2.
apply PinfL. unfold Lower_Bound. intros. reduce in H1. case H1. intros.
specialize Ps with (s0:=(pair x s0)). apply Ps in H2. destruct H2. apply H3.
Qed.

End ProdLattice.

Section KnapsterTarski.

Context {A} `{eq : Equiv A}  (leq : Le A) `{!CompleteLattice leq} (f: A->A) `{!OrderPreserving f}.

Lemma PreFixedInfs: forall S : Ensemble A,
        (forall t : A, S t -> PreFixedPoint f t) -> PreFixedPoint f (inf S).
Proof.
intros S C.
unfold PreFixedPoint in *.
destruct CompleteLattice0.
apply (PinfL0 S).
intros l Sl.
transitivity (f l).
destruct  OrderPreserving0.
apply order_preserving. apply Pinf. apply Sl.
apply (C _ Sl).
Qed.

Lemma PostFixedSups : forall S : Ensemble A,
        (forall t : A, S t -> PostFixedPoint f t) -> PostFixedPoint f (@inf A equiv (flip leq) dual_is_clattice S).
Proof.
unfold PostFixedPoint.
intros S C.
apply PsupL.
intros l Sl.
transitivity (f l).
apply (C _ Sl).
destruct  OrderPreserving0.
apply order_preserving. apply Psup. apply Sl.
Qed.

Instance PreFixedLattice : CompleteLattice (sub_leq (P:=PreFixedPoint f) leq).
apply (subord_is_clattice leq PreFixedInfs).
Defined.

Instance PostFixedLattice : CompleteLattice (sub_leq (P:=PostFixedPoint f) (flip leq)).
apply (subord_is_clattice (flip leq) PostFixedSups).
Defined.

Definition lfp := proj1_sig (@inf {x : A | PreFixedPoint f x} (sub_equiv) (sub_leq leq) PreFixedLattice (fun _ => True)).
Definition gfp := proj1_sig (@inf {x : A | PostFixedPoint f x} (sub_equiv) (sub_leq (flip leq)) PostFixedLattice (fun _  => True)).

Lemma lfp_is_PreFixedPoint : PreFixedPoint f lfp.
Proof.
unfold PreFixedPoint. unfold lfp.
assert (yy:=@Pinf {x : A | PreFixedPoint f x} (sub_equiv) (sub_leq leq) PreFixedLattice).
generalize yy;  clear yy.
case (@inf {x : A | PreFixedPoint f x} (sub_equiv) (sub_leq leq) PreFixedLattice (fun _ => True)).
intros x Px yy.
apply Px.
Qed.

Lemma gfp_is_PostFixedPoint : PostFixedPoint f gfp.
Proof.
unfold PostFixedPoint. unfold gfp.
assert (yy:=@Pinf {x : A | PostFixedPoint f x} (sub_equiv) (sub_leq (flip leq)) PostFixedLattice).
generalize yy;  clear yy.
case (@inf {x : A | PostFixedPoint f x} (sub_equiv) (sub_leq (flip leq)) PostFixedLattice (fun _ => True)).
intros x Px yy.
apply Px.
Qed.

(* least fixed point is the least of all pre-fixed points. *)
Lemma lfp_least : forall fp, PreFixedPoint f fp -> lfp ≤ fp.
Proof.
unfold PreFixedPoint. unfold lfp.
assert (yy:=@Pinf {x : A | PreFixedPoint f x} (sub_equiv) (sub_leq leq) PreFixedLattice (fun _ => True)).
generalize yy; clear yy.
case (@inf {x : A | PreFixedPoint f x} (sub_equiv) (sub_leq leq) PreFixedLattice (fun _ => True)).
unfold proj1_sig.
intros x Px yy.
assert (zz:=fun X PX => (yy (exist (fun t => PreFixedPoint f t) X PX))). clear yy.
case (@inf {x : A | PreFixedPoint f x} (sub_equiv) (sub_leq leq) PreFixedLattice (fun _ => True)).
intros.
refine (zz _ H _).
reduce.
trivial.
Qed.

(* greatest fixed point is the greatest among all post-fixed points *)
Lemma gfp_greatest : forall fp, PostFixedPoint f fp -> fp ≤ gfp.
Proof.
unfold PostFixedPoint. unfold gfp.
assert (yy:=@Pinf {x : A | PostFixedPoint f x} (sub_equiv) (sub_leq (flip leq)) PostFixedLattice (fun _ => True)).
generalize yy; clear yy.
case (@inf {x : A | PostFixedPoint f x} (sub_equiv) (sub_leq (flip leq)) PostFixedLattice (fun _ => True)).
unfold proj1_sig.
intros x Px yy.
assert (zz:=fun X PX => (yy (exist (fun t => PostFixedPoint f t) X PX))). clear yy.
case (@inf {x : A | PostFixedPoint f x} (sub_equiv) (sub_leq (flip leq)) PostFixedLattice (fun _ => True)).
intros.
refine (zz _ H _).
reduce.
trivial.
Qed.

Lemma lfp_fixedpoint : FixedPoint f lfp.
Proof.
unfold FixedPoint.
apply po_antisym.
- apply lfp_is_PreFixedPoint.
- assert (Hfx: PreFixedPoint f (f lfp)). {
    unfold PreFixedPoint. apply OrderPreserving0. apply lfp_is_PreFixedPoint. }
  apply lfp_least. apply Hfx.
Qed.

Lemma gfp_fixedpoint : FixedPoint f gfp.
Proof.
unfold FixedPoint.
apply po_antisym.
- assert (Hfx: PostFixedPoint f (f gfp)). {
    unfold PostFixedPoint. apply OrderPreserving0. apply gfp_is_PostFixedPoint. }
  apply gfp_greatest. apply Hfx.
- apply gfp_is_PostFixedPoint.
Qed.

End KnapsterTarski.


Section OrderPreservingLattice.

Context {A B : Type} `{PartialOrder A} `{Equiv B} (leq : Le B) `{!CompleteLattice leq}.

Lemma inf_is_order_preserving : forall (S : Ensemble (A->B)), (forall t : A->B, S t -> OrderPreserving t) -> OrderPreserving (inf (Ale:=arrow_leq) S).
intros S l.
assert (Hhh : forall (x:A) (f : A->B), S f -> (f x) ∈ (fun x0 : B => exists g : A->B, S g /\ g x = x0)). {
    intros. exists f. split. assumption. destruct CompleteLattice0. destruct ltord0. reflexivity. }
split.
- split.
 + assumption.
 + destruct CompleteLattice0. assumption.
 +
  split.
    * destruct H0. apply po_setoid.
    * destruct CompleteLattice0. destruct ltord0. apply po_setoid.
    * reduce.
      assert (forall f : A -> B, S f -> f x = f y). {
        intro. intro.  apply l in H3. destruct CompleteLattice0. destruct ltord0. rewrite H2. reflexivity. }
      assert (forall x y, x ≤ y /\ y ≤ x <-> x = y). {
        intros. split. intro. destruct H4. destruct CompleteLattice0. destruct ltord0.
        apply po_antisym. assumption. assumption.
        intro.  destruct CompleteLattice0. destruct ltord0. split. rewrite H4.  reflexivity. rewrite H4. reflexivity. }
      apply H4. split.
      destruct CompleteLattice0. unfold inf. unfold arrow_is_clattice. reduce.
      { apply PinfL0. intro. intro. reduce in H5. case H5. intros. destruct H6. apply Pinf0. reduce. exists x0. destruct ltord0. rewrite <- H7. split.
        assumption. apply H3. apply H6. }
            destruct CompleteLattice0.
      { apply PinfL0. intro. intro. reduce in H5. case H5. intros. destruct H6. apply Pinf0. reduce. exists x0. destruct ltord0. rewrite <- H7. split.
        assumption. symmetry. apply H3. apply H6. }
- intros. unfold inf. unfold arrow_is_clattice. unfold contains. unfold flip. reduce.
  destruct CompleteLattice0.
  assert (mon: forall f : A->B, S f -> f x ≤ f y). { intros. apply l. assumption. assumption. }

  apply PinfL0. unfold Lower_Bound. intros.  reduce in H3. case H3. intro. intro. destruct H4. assert (Hc : S x0). { assumption. }
  apply mon in H4. destruct ltord0. rewrite <- H5.
  simple apply Hhh with (f:=x0) (x:=x) in Hc.
  apply Pinf0 in Hc.
  transitivity (x0 x). assumption. assumption.
Qed.


Global Instance orderpreserving_is_complete_lattice : CompleteLattice (sub_leq (P:=OrderPreserving) (@arrow_leq A B leq)).
apply (subord_is_clattice (@arrow_leq A B leq) inf_is_order_preserving).
Qed.

End OrderPreservingLattice.
