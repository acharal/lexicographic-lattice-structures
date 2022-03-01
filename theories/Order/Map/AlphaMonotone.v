From LexLatStruct Require Import Basic.
From LexLatStruct.Order Require Import Ordinal.
From LexLatStruct.Order.Lattice Require Import Lexicographic.

Section amonotonic.

Context {kappa: wf_ord} {A}
       `{equiv : Equiv A}
       `{equiv_a : forall alpha : (ordd (as_orddd kappa)), Equiv A}
       {le_a : (ordd (as_orddd kappa)) -> Le A}
       `{!StratifiedCompleteLattice kappa le_a}
       (alpha : (ordd (as_orddd kappa))) (f : A -> A).

(* Definition 6.1 *)
Class AlphaOrderPreserving : Prop :=
 { alpha_order_morphism :> Proper ((=) ==> (=)) f
 ; alpha_order_preserving : forall x y, le_a alpha x y -> le_a alpha (f x) (f y) }.

Print StratifiedCompleteLattice.

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
