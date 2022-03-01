Require Export Coq.Relations.Relations.
Require Import Coq.Program.Program.

From LexLatStruct Require Export Basic.
From LexLatStruct.Order Require Import PartialOrder.

Require Import Arith.
Require Import Coq.Arith.PeanoNat.

Open Scope nat.

Instance : Equiv nat := Nat.eq.
Definition le_nat := fun (x y: nat) => (x <= y)%nat.
Instance : Le nat := le_nat.
Instance : PartialOrder (le_nat).
Admitted.

Close Scope nat.
