Require Export LexLatStruct.Order.Fixpoint.
Require Export LexLatStruct.Basic.
Require Import LexLatStruct.Order.Lattice.
Require Import LexLatStruct.Order.Map.Monotone.
Require Import Coq.Program.Program.
Require Import LexLatStruct.Order.Lattice.Dual.
Require Import LexLatStruct.Order.Lattice.Sub.
Require Import LexLatStruct.Order.Partial.Sub.

Section KnapsterTarski.

Context {A} `{eq : Equiv A}  (leq : Le A) `{!CompleteLattice leq} (f: A->A) `{!OrderPreserving f}.

Existing Instance sub_equiv.

Lemma PreFixedInfs: forall S : Ensemble A,
        (forall t : A, S t -> PreFixedPoint f t) -> PreFixedPoint f (inf S).
Proof.
intros S C.
unfold PreFixedPoint in *.
destruct CompleteLattice0.
apply (PinfL S).
intros l Sl.
transitivity (f l).
destruct  OrderPreserving0.
apply order_preserving. apply Pinf. apply Sl.
apply (C _ Sl).
Qed.

Lemma PostFixedSups : forall S : Ensemble A,
        (forall t : A, S t -> PostFixedPoint f t) -> PostFixedPoint f (@inf A equiv (flip leq) dual_is_clat S).
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
apply (sub_is_clat leq PreFixedInfs).
Defined.

Instance PostFixedLattice : CompleteLattice (sub_leq (P:=PostFixedPoint f) (flip leq)).
apply (sub_is_clat (flip leq) PostFixedSups).
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
