From LexLatStruct Require Export Basic.

(*
Definition similar {O1 O2} `{PartialOrder O1} `{PartialOrder O2} :=
  exists f : O1 -> O2, OrderIsomorphism f.
*)

Class Pointed {A} (leq : Le A) :=
 { bot : A
 ; Pbot : forall x : A, bot ≤ x }.
