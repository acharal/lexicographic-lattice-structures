Require Export Coq.Relations.Relations.
Require Export Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid. (* DefaultRelation *)
Require Import Coq.Program.Program. (* compose *)

Definition id {A : Type} (a : A) := a.

Class Equiv A := equiv : relation A.

Infix "=" := equiv : type_scope.

Notation "(=)" := equiv (only parsing).

Typeclasses Transparent Equiv.
Typeclasses Transparent compose flip.

Instance equiv_default_relation {A} `{Equiv A} : DefaultRelation (=) | 3.

Definition ext_equiv {A B} `{Equiv A} `{Equiv B} : Equiv (A -> B) := ((=) ==> (=))%signature.
Hint Extern 10 (Equiv (_ -> _)) => apply @ext_equiv : typeclass_instances.
Hint Extern 10 (Equiv (relation _)) => apply @ext_equiv : typeclass_instances. (* Due to bug #2491 *)

Definition sig_equiv {A} `{Equiv A} (P: A -> Prop) : Equiv (sig P) := fun x y => `x = `y.

Class Setoid A `{Ae: Equiv A} : Prop :=
  setoid_eq :> Equivalence (@equiv A Ae).

Class SetoidMorphism {A B} `{Equiv A} `{Equiv B} (f:A->B) :=
  { setoidmor_a : Setoid A
  ; setoidmor_b : Setoid B
  ; sm_proper   :> Proper ((=) ==> (=)) f }.


Class Seq {A B} `{Equiv A} `{Equiv B} (s : A -> B) := {
  seq_proper :> Proper (equiv ==> equiv) s
}.


Class Le (A : Type) := le : relation A.

Class Lt (A : Type) := lt : relation A.

Infix "≤" := le (at level 50).

Notation "(≤)" := le (only parsing).

Infix "<" := lt (at level 70).

Notation "(<)" := lt (only parsing).

Typeclasses Transparent Le.

Definition sig_le {A} `{Le A} (P : A->Prop) : Le (sig P) := fun x y => `x ≤ `y.
Definition sig_lt {A} `{Lt A} (P : A->Prop) : Lt (sig P) := fun x y => `x < `y.

Infix "≥" := (flip le) (at level 50).

Notation "(≥)" := (flip le) (only parsing).

Infix ">" := (flip lt) (at level 70).
Notation "(>)" := (flip lt) (only parsing).

Class Inverse {A} {B} (f: A->B) := inverse : B->A.
Arguments inverse {A B} _ {Inverse} _.
Typeclasses Transparent Inverse.


Class AntiSymmetric {A} `{Equiv A} (R: relation A) : Prop := 
  antisymmetry : forall {x y}, R x y -> R y x -> x = y.

Class TotalRelation {A} `(R : relation A) : Prop := 
  total : forall x y : A, R x y \/ R y x.

Section jections.

  Context {A B} {Ae : Equiv A} {Be : Equiv B} (f : A->B) `{inv: !Inverse f}.

  Class Injective : Prop :=
   { injective : forall x y, f x = f y -> x = y
   ; injective_mor : SetoidMorphism f }.

  Class Surjective : Prop :=
   { surjective : compose f (inverse f) = id
   ; surjective_mor : SetoidMorphism f }.

  Class Bijective : Prop :=
   { bijective_injective :> Injective
   ; bijective_surjective :> Surjective }.

End jections.


Definition emptyset {A} := fun _ : A => False.

Definition nonempty {A} (P : A ->Prop) : Prop := exists x, P x.

Notation "∅" := emptyset.

