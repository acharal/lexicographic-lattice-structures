From LexLatStruct.Order Require Import Lattice.
From LexLatStruct.Order.Partial Require Import Arrow.
From LexLatStruct Require Export Basic.
Require Import Coq.Program.Program.

Section ArrowLattice.

Context {A B: Type} (leb: Le B) `{Equiv B} `{!CompleteLattice leb}.

Instance arrow_is_clat : CompleteLattice (arrow_leq (A:=A)).
  exists (fun S => fun d :A => inf (fun x => exists f, f ∈ S /\ f d = x)).
  apply arrow_is_partialorder. apply ltord.
- destruct CompleteLattice0. unfold Lower_Bound in *. intros. unfold le in *. unfold arrow_leq in *. intros t.
  apply Pinf. unfold contains. unfold flip. exists s. split.
  + assumption.
  + destruct ltord. reflexivity.
- unfold le in *. unfold arrow_leq in *. destruct CompleteLattice0.
  intros. apply PinfL. intro. unfold contains. unfold flip. intro.
  case H1. intro. intro. destruct H2. destruct ltord. rewrite <- H3.
  apply H0. apply H2.
Defined.


End ArrowLattice.
