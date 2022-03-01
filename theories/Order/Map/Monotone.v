Require Export Coq.Relations.Relations.
Require Export Coq.Classes.RelationClasses.
Require Import Coq.Program.Program.

From LexLatStruct Require Export Basic.
From LexLatStruct.Order Require Import PartialOrder.

Section maps.

Context {A B : Type}
  {Ae: Equiv A} {Ale: Le A}
  {Be: Equiv B} {Ble: Le B}
  (f : A -> B).

Class OrderMorphism :=
{ order_po_a : PartialOrder Ale
; order_po_b : PartialOrder Ble
; ordermor :> SetoidMorphism f }.

Class OrderPreserving :=
{ order_preserving_mor :> OrderMorphism
; order_preserving : forall x y, x ≤ y -> f x ≤ f y }.

Class OrderReflecting :=
{ order_reflecting_mor :> OrderMorphism
; order_reflecting  : forall x y, f x ≤ f y -> x ≤ y }.

Class OrderEmbedding :=
{ order_embedding_preserving :> OrderPreserving
; order_embedding_reflecting :> OrderReflecting }.

Class OrderIsomorphism `{!Inverse f} :=
{ order_iso_embedding :> OrderEmbedding
; order_iso_surjective :> Surjective f }.

Class OrderReversing :=
{ order_reversing_mor :> OrderMorphism
; order_reversing  : forall x y, x ≤ y -> f y ≤ f x }.

End maps.

Hint Extern 4 (?f _ ≤ ?f _) => apply (order_preserving f).


Lemma compose_is_order_morphism {A B C}
  `{poA: PartialOrder A} `{poB : PartialOrder B} `{poC: PartialOrder C}:
  forall (f: B->C) (g: A->B),
    OrderMorphism f ->
    OrderMorphism g ->
    OrderMorphism (compose f g).
Proof.
intros f g fop gop.
split. assumption. assumption.
  split. apply po_setoid. apply po_setoid.
  reduce. destruct poA. destruct poB. destruct poC. destruct fop. destruct gop.
  rewrite H2. reflexivity.
Qed.

Lemma compose_preserving_is_preserving {A B C}
  `{poA: PartialOrder A} `{poB : PartialOrder B} `{poC: PartialOrder C}:
  forall (f: B->C) (g: A->B),
    OrderPreserving f ->
    OrderPreserving g ->
    OrderPreserving (compose f g).
Proof.
intros f g f_op g_op. split.
- apply compose_is_order_morphism. apply f_op. apply g_op.
- intros x y x_le_y. unfold compose. apply order_preserving. apply f_op.
  apply order_preserving. apply g_op. apply x_le_y.
Qed.

Lemma compose_reversing_is_preserving {A B C}
  `{poA: PartialOrder A} `{poB : PartialOrder B} `{poC: PartialOrder C}:
  forall (f: B->C) (g: A->B),
    OrderReversing f ->
    OrderReversing g ->
    OrderPreserving (compose f g).
Proof.
intros f g f_or g_or. split.
- apply compose_is_order_morphism. apply f_or. apply g_or.
- intros x y x_le_y. unfold compose. apply order_reversing. apply f_or.
  apply order_reversing. apply g_or. apply x_le_y.
Qed.

Definition fmon (A B : Type) `{PartialOrder A} `{PartialOrder B} :=
    { f : A->B | OrderPreserving f}.

Infix "-m>" := fmon (at level 30, right associativity).

Definition fmon_as_fun {A} {B}
  `{PartialOrder A} `{PartialOrder B} (f : A -m> B) : A -> B := proj1_sig f.

Coercion fmon_as_fun : fmon >-> Funclass.

(* Composition of monotone functions is monotone *)
Definition fmon_comp {O1 O2 O3 : Type}
  `{PartialOrder O1} `{PartialOrder O2} `{PartialOrder O3} :
    (O2 -m> O3) -> (O1 -m> O2) -> O1 -m> O3.
intros f g; exists (compose f g).
apply compose_preserving_is_preserving. apply (proj2_sig f). apply (proj2_sig g).
Defined.
