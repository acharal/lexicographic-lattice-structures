
Require Export Coq.Relations.Relations.
Require Import Coq.Program.Program.

From LexLatStruct Require Export Basic.
From LexLatStruct.Order Require Import PartialOrder.

Section Dualorder.

Context {A} `{Equiv A} `{Le A}.

Lemma geq_is_preo `{!PreOrder (≤)} : PreOrder (≥).
Proof.
  split.
    intros x; reflexivity.
    intros x y z x_le_y y_le_z; transitivity y; assumption.
Qed.

Lemma geq_is_po `{!PartialOrder (≤)} : PartialOrder (≥).
Proof.
  pose proof po_setoid.
  split.
    assumption.
    unfold le, flip.
      reduce.
      rewrite <- H2; rewrite <- H3; tauto.
    apply geq_is_preo.
    intros x y x_le_y y_le_x.
    apply po_antisym.
    apply y_le_x.
    apply x_le_y.
Qed.

End Dualorder.

Existing Instance geq_is_preo.
Existing Instance geq_is_po.
