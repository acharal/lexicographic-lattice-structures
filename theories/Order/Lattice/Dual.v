From LexLatStruct.Order Require Import Lattice.
From LexLatStruct.Order.Partial Require Import Dual.
From LexLatStruct Require Export Basic.
Require Import Coq.Program.Program.
Require Import LexLatStruct.Order.PartialOrder.

Section Dual.

Context {A} `{CompleteLattice A}.

Program Instance dual_is_clat  : CompleteLattice (≥) := {
  inf := sup }.

Next Obligation.
  apply Psup.
Qed.

Next Obligation.
  apply PsupL.
  apply H0.
Defined.

End Dual.
