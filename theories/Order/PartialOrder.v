
Require Export Coq.Relations.Relations.
From LexLatStruct Require Export Basic.

Class PartialOrder {A} `{Equiv A} (Ale : Le A) : Prop :=
{ po_setoid : Setoid A
; po_proper :> Proper ((=) ==> (=) ==> iff) (≤)
; po_preorder :> PreOrder (≤)
; po_antisym :> AntiSymmetric (≤) }.

Lemma eq_implies_leq {A} `{Po : PartialOrder A} :
  forall x y,
    x = y ->
    x ≤ y /\ y ≤ x.
Proof.
  intros x y C.
  destruct Po.
  rewrite C.
  split; reflexivity.
Qed.
