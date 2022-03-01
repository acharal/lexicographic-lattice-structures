From LexLatStruct Require Import Basic.

Definition PreFixedPoint {A} `{Le A} (f : A -> A) (d : A) : Prop := f d ≤ d.
Definition PostFixedPoint {A} `{Le A} (f : A -> A) (d : A) : Prop := d ≤ f d.
Definition FixedPoint {A} `{Equiv A} (f : A -> A) (d : A) : Prop := f d = d.

Class Expansive {A} `{Le A} (f:A->A) :=
  { expansive : forall x, x ≤ f x }.
