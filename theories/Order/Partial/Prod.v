Require Export Coq.Relations.Relations.
Require Import Coq.Program.Program.

From LexLatStruct Require Export Basic.
From LexLatStruct Require Import PartialOrder.


Section Prodorder.

Context {A B : Type}.

Global Instance prod_equiv `{Equiv A} `{Equiv B} : Equiv (A*B) := {
   equiv (x y : A*B) := (fst x) = (fst y) /\ (snd x) = (snd y) }.

Global Instance prod_leq `{Le A} `{Le B} : Le (A*B) := {
  le (x y : A*B) := (fst x) ≤ (fst y) /\ (snd x) ≤ (snd y) }.

Lemma prod_is_preorder {lea : Le A} `{!PreOrder lea} {leb : Le B} `{!PreOrder leb} : PreOrder prod_leq.
Proof.
split.
- unfold Reflexive. unfold prod_leq. intro x. split. reflexivity. reflexivity.
- unfold Transitive. intros x y z. unfold prod_leq. intros [HFstxy HSndxy]. intros [HFstyz HSndyz].
  split. transitivity (fst y). assumption. assumption. transitivity (snd y). assumption. assumption.
Qed.

Global Instance prod_is_setoid `{Setoid A} `{Setoid B} : Setoid (A*B).
Proof.
split.
  - unfold Reflexive. intro. split. reflexivity. reflexivity.

  - unfold Symmetric. intros x y. unfold equiv. unfold prod_equiv.
    intros [HFxy HSxy]. split. symmetry. assumption. symmetry. assumption.
  - unfold Transitive. intros x y z. unfold equiv. unfold prod_equiv. intros [HFxy HSxy] [HFyz HSyz].    split. transitivity (fst y). assumption. assumption. transitivity (snd y).
  assumption. assumption.

Qed.

Global Instance prod_is_partialorder `{Equiv A} (lea : Le A) `{!PartialOrder lea}
           `{Equiv B} (leb : Le B) `{!PartialOrder leb} : PartialOrder (@prod_leq lea leb).
Proof.
split.
  - destruct PartialOrder0. destruct PartialOrder1. apply prod_is_setoid.
  - reduce. unfold le. unfold prod_leq. unfold equiv in *. unfold prod_equiv in *.
    destruct H1. destruct H2. destruct PartialOrder0. destruct PartialOrder1.
    rewrite <- H1. rewrite <- H3. rewrite <- H2. rewrite <- H4. split. trivial. trivial.
  - apply prod_is_preorder.
  - unfold AntiSymmetric. unfold le. unfold prod_leq. unfold equiv. unfold prod_equiv.
    intros x y. intros [HFxy HSxy] [HFyx HSyx]. destruct PartialOrder0. destruct PartialOrder1.
    split.
      apply po_antisym. assumption. assumption.
      apply po_antisym0. assumption. assumption.
Qed.


End Prodorder.
