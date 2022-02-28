Require Export Coq.Relations.Relations.
Require Export Coq.Classes.RelationClasses.
Require Import Coq.Program.Program.
From LexLatStruct Require Export Basic.
Require Import Arith.
Require Import Coq.Arith.PeanoNat.


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

Class TotalOrder {A} `{Ae : Equiv A} (Ale : Le A) : Prop :=
  { total_order_po :> PartialOrder (≤)
  ; total_order_total :> TotalRelation (≤) }.

Section DualOrd.

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

End DualOrd.

Existing Instance geq_is_preo.
Existing Instance geq_is_po.

Section SubOrd.

  Context {A} {P: A->Prop}.

  Definition sub_equiv `{Equiv A} : Equiv {x : A | P x} := sig_equiv P.

  Definition sub_leq (le : Le A) : Le {x : A | P x} := sig_le P.


  Existing Instance sub_equiv.
  Existing Instance sub_leq.

  Instance subord_is_setoid `{Setoid A} : Setoid { x : A | P x }.
  Proof.
  split.
  - unfold Reflexive. intro. unfold equiv. unfold sub_equiv. unfold sig_equiv. reflexivity.
  - unfold Symmetric. intros. unfold equiv. unfold sub_equiv. unfold sig_equiv. destruct H. unfold Symmetric in Equivalence_Symmetric. apply Equivalence_Symmetric.
    unfold equiv in H0. unfold sub_equiv in H0. trivial.
  - unfold Transitive. intros. unfold equiv. unfold sub_equiv. unfold sig_equiv.
    unfold equiv in H0. unfold sub_equiv in H0. unfold equiv in H1. unfold sub_equiv in H1. unfold sig_equiv in H1. rewrite <- H1. trivial.
  Qed.

  Instance subord_is_preorder (leq : Le A) `{!PreOrder leq} : PreOrder (sub_leq leq).
  Proof.
  split.
  - reduce. destruct PreOrder0. unfold Reflexive in PreOrder_Reflexive. apply PreOrder_Reflexive.
  - unfold sub_leq. reduce. destruct PreOrder0. apply transitivity with (y0:=proj1_sig y).
    + apply H.
    + apply H0.
  Qed.

  Global Instance subord_is_partialorder `{Equiv A} (leq : Le A) `{!PartialOrder leq} : PartialOrder (sub_leq leq).
  Proof.
  destruct PartialOrder0. split.
  - apply subord_is_setoid.
  - reduce. unfold le. unfold sub_leq. unfold sig_le. unfold equiv in H0. unfold sub_equiv in H0. unfold sig_equiv in H0.
    unfold equiv in H1. unfold sub_equiv in H1. unfold sig_equiv in H1. rewrite H0. rewrite H1. reflexivity.
  - apply subord_is_preorder. apply po_preorder0.
  - unfold AntiSymmetric. intros. unfold equiv. unfold sub_equiv.
    unfold AntiSymmetric in po_antisym0. apply po_antisym0.
    + reduce in H0. assumption.
    + reduce in H1. assumption.
  Qed.

End SubOrd.

Section ArrowOrd.

  Context {A B: Type}.

  Global Instance arrow_equiv `{Equiv B} : Equiv (A->B) :=
    fun (f g : A->B) => forall x, f x = g x.

  Definition arrow_leq `{Le B} : Le (A->B) :=
    fun (f g : A->B) => forall x, f(x) ≤ g(x).

  Global Instance arrow_leq_inst `{Le B} : Le (A->B) := arrow_leq.

  Lemma arrow_is_preorder {leb : Le B} `{!PreOrder leb} : PreOrder (@arrow_leq leb).
  Proof.
    intros.
    split.
    - reduce. reflexivity.
    - unfold Transitive. intros f h g.
      unfold arrow_leq. intro f_less_than_h.
      firstorder.
      specialize (f_less_than_h x).
      apply transitivity with (y:=h x).
      assumption.
      apply H.
  Qed.


  Global Instance arrow_is_setoid `{Setoid B} : Setoid (A->B).
  Proof.
  split.
  - unfold Reflexive. unfold equiv. unfold arrow_equiv. intros f x.
    destruct H. unfold Reflexive in Equivalence_Reflexive. apply Equivalence_Reflexive.
  - unfold Symmetric. unfold equiv. unfold arrow_equiv. intros f g. firstorder.
  - unfold Transitive. unfold equiv. unfold arrow_equiv. intros f h g. firstorder.
  Qed.

  Instance po_is_setoid `{PartialOrder B} : Setoid B := po_setoid.

  Global Instance arrow_is_partialorder (leb: Le B) `{Equiv B} `{!PartialOrder leb}: PartialOrder (@arrow_leq leb).
  Proof.
  split.
  - apply arrow_is_setoid.
  - reduce. unfold le. unfold arrow_leq. unfold equiv in H0. unfold arrow_equiv in H0.
    unfold equiv in H1. unfold arrow_equiv in H1.
    split.
    + intro. intro w. rewrite <- H1. rewrite <- H0. apply H2.
    + intro. intro w. rewrite -> H1. rewrite -> H0. apply H2.
  - apply arrow_is_preorder.
  - unfold AntiSymmetric. unfold le. unfold arrow_leq. unfold equiv. unfold arrow_equiv.
    intros f g. intros. apply po_antisym.
    + apply H0.
    + apply H1.
  Qed.

End ArrowOrd.


Section order_maps.

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

End order_maps.

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

(*
Definition similar {O1 O2} `{PartialOrder O1} `{PartialOrder O2} :=
  exists f : O1 -> O2, OrderIsomorphism f.
*)

Section ProdOrd.

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
    - unfold Transitive. intros x y z. unfold equiv. unfold prod_equiv. intros [HFxy HSxy] [HFyz HSyz].
      split. transitivity (fst y). assumption. assumption. transitivity (snd y).
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
        apply po_antisym0. assumption. assumption.
        apply po_antisym1. assumption. assumption.
  Qed.

End ProdOrd.

Class Pointed {A} (leq : Le A) :=
 { bot : A
 ; Pbot : forall x : A, bot ≤ x }.


Open Scope nat.

Instance : Equiv nat := Nat.eq.
Definition le_nat := fun (x y: nat) => (x <= y)%nat.
Instance : Le nat := le_nat.
Instance : PartialOrder (le_nat).
Admitted.

Close Scope nat.

Class CompletePartialOrder {A} `{Equiv A} (Ale : Le A) := {
    cpo_po :> PartialOrder (≤)
  ; lub : forall (F : nat-m>A), A
  ; cpo_lub_le: forall (F : nat-m>A) (n : nat), F n ≤ lub F
  ; cpo_le_lub: forall (F : nat-m>A) (x : A), (forall n, F n ≤ x) -> lub F ≤ x }.

Lemma lub_le_order_preserving {A} {B}
  `{CompletePartialOrder A}
  `{CompletePartialOrder B} :
  forall (f:A-m>B) (s : nat -m>A),
    lub (fmon_comp f s) ≤ f (lub s).
Proof.
  intros f s.
  apply cpo_le_lub.
  intros.
  unfold fmon_comp. unfold compose. simpl.
  apply order_preserving.
  apply (proj2_sig f).
  apply cpo_lub_le.
Qed.

Section ArrowCPO.

  Context {A:Type} {B} `{Equiv B} {leb : Le B} `{!CompletePartialOrder leb}.

  Instance : Setoid B := po_setoid.

  Definition funseq (s : nat-m>(A->B)) (a : A) : nat-m>B.
  exists (fun (n : nat) => s n a).
  split.
  split.
  apply PartialOrder_instance_0.
  apply CompletePartialOrder0.
  split.
  apply PartialOrder_instance_0.
  apply CompletePartialOrder0.
  reduce.
  rewrite H0.
  apply po_setoid.
  intros x y x_le_y.
  apply (proj2_sig s).
  apply x_le_y.
  Defined.

  Definition lubF := fun (f : nat-m> (A->B)) => fun (a : A) => lub (funseq f a).

  Global Instance : CompletePartialOrder (@arrow_leq A B leb) := {
    lub := lubF
  }.
  Proof.
    intros F n.
    unfold le.
    unfold arrow_leq.
    intro x.
    assert (F n x = funseq F x n).
    { unfold funseq. simpl. reflexivity. }
    rewrite H0.
    apply cpo_lub_le.
    intros F x H1.
    unfold le in *.
    unfold arrow_leq in *.
    intro x0.
    apply cpo_le_lub.
    intro n.
    apply H1.
  Defined.

End ArrowCPO.

Section SubCPO.

  Context {A:Type} {P : A ->Prop} `{Equiv A} `{leq : Le A} `{!CompletePartialOrder leq}.

  Variable PSlub: forall (S : nat-m>A), (forall n, P (S n)) -> P (lub S).

  Definition Embed (t : A) (p : P t) : { x : A | P x }.
  exists t . apply p.
  Defined.

  Definition Extend (S : nat-m>{ x : A | P x }) : nat-m>A.
  destruct S.
  exists (fun n => proj1_sig (x n)).
  split.
  split.
  apply PartialOrder_instance_0.
  apply CompletePartialOrder0.
  split.
  apply PartialOrder_instance_0.
  apply CompletePartialOrder0.
  apply o.
  apply o.
  Defined.

  Lemma ExtendP : forall (S : nat-m>{x : A | P x}) t, P (Extend S t).
  intros S t. destruct S. unfold Extend. simpl. apply (proj2_sig (x t)).
  Defined.

  Global Instance subord_is_cpo : CompletePartialOrder (@sub_leq A P leq) := {
    lub := fun (S: nat-m>{x:A | P x}) => Embed (lub (Extend S)) (PSlub (Extend S) (ExtendP S))
  }.
  intros F n. unfold le. unfold sub_leq. unfold sig_le. unfold Embed. simpl.
  assert (proj1_sig (F n) = Extend F n). {
    destruct F.
    unfold Extend.
    simpl.
    apply po_setoid.
  }
  destruct CompletePartialOrder0. destruct cpo_po0.
  rewrite H0.
  apply cpo_lub_le.
  intros F x H1.
  unfold Embed.
  unfold le.
  unfold sub_leq.
  unfold sig_le.
  simpl.
  apply cpo_le_lub.
  intro n.
  assert (proj1_sig (F n) = Extend F n). {
    destruct F.
    unfold Extend.
    simpl.
    apply po_setoid.
  }
  destruct CompletePartialOrder0. destruct cpo_po0.
  rewrite <- H0.
  apply H1.
  Defined.

End SubCPO.

Section FmonCPO.

  Context {A B} `{Equiv A} `{lea : Le A} `{!CompletePartialOrder lea}
          `{Equiv B} `{leb : Le B} `{!CompletePartialOrder leb}.

Lemma lub_is_op :
  forall (S : nat-m>(A->B)),
    (forall n, OrderPreserving (S n)) ->
    OrderPreserving (lub S).
Proof.
  intros S H1.
  split.
  split.
  apply CompletePartialOrder0.
  apply CompletePartialOrder1.
  split.
  apply CompletePartialOrder0.
  apply CompletePartialOrder1.
  reduce.
  unfold lub.
  unfold CompletePartialOrder_instance_0.
  unfold lubF.
  apply po_antisym.
    apply cpo_le_lub.
    intro.
    unfold funseq at 1.
    simpl.
    specialize H1 with n.
    destruct H1.
    destruct order_preserving_mor0.
    destruct order_po_b0.
    destruct po_setoid0.
    rewrite H2.
    assert (S n y = (funseq S y) n). {
      unfold funseq.
      simpl.
      reflexivity. }
    rewrite H1.
    apply cpo_lub_le.
    apply cpo_le_lub.
    intro.
    unfold funseq at 1.
    simpl.
    specialize H1 with n.
    destruct H1.
    destruct order_preserving_mor0.
    destruct order_po_b0.
    destruct po_setoid0.
    destruct ordermor0.
    assert (S n y = (funseq S x) n). {
      unfold funseq.
      simpl.
      rewrite <- H2.
      reflexivity. }
    rewrite H1.
    apply cpo_lub_le.
  intros x y x_le_y.
  apply cpo_le_lub.
  intro n.
  unfold funseq.
  simpl.
  transitivity (S n y).
  apply H1.
  apply x_le_y.
  unfold lubF.
  assert (S n y = (funseq S y) n).
  { unfold funseq. simpl.
    destruct CompletePartialOrder1.
    destruct cpo_po0.
    reflexivity. }
  destruct CompletePartialOrder1.
  destruct cpo_po0.
  rewrite H2.
  apply cpo_lub_le.
Qed.

Global Instance : CompletePartialOrder (@sub_leq (A->B) OrderPreserving arrow_leq) :=
  subord_is_cpo lub_is_op.


End FmonCPO.

Section LubLemmas.

  Context {A} `{CompletePartialOrder A}.

Lemma lub_le_compat :
  forall (f g : nat-m>A),
    f ≤ g ->
    lub f ≤ lub g.
Proof.
  intros.
  apply cpo_le_lub.
  intros.
  transitivity (g n).
  apply H1.
  apply cpo_lub_le.
Qed.

Definition seq_lift_left :
    forall (f : nat-m>A) (n:nat), nat-m>A.
intros.
exists (fun k => f (n+k)%nat).
split.
- split. apply PartialOrder_instance_0. apply H0.
  split. apply po_setoid. apply po_setoid.
  reduce. destruct f. destruct o. destruct order_preserving_mor0.
  destruct H0. destruct cpo_po0. destruct ordermor0. simpl.
  rewrite H1. reflexivity.
- intros x y x_le_y.
  apply order_preserving.
  apply (proj2_sig f).
  unfold le. unfold Le_instance_0. unfold le_nat.
  auto with arith.
Defined.

Lemma lub_lift_left :
  forall (f : nat-m>A) (n:nat),
    lub f = lub (seq_lift_left f n).
Proof.
intros.
apply po_antisym.
apply lub_le_compat.
unfold seq_lift_left.
unfold le. unfold sub_leq_inst. unfold sub_leq. unfold sig_le.
simpl. unfold le. unfold arrow_leq_inst. unfold arrow_leq.
intro. apply order_preserving. apply (proj2_sig f).
unfold le. unfold Le_instance_0. unfold le_nat. auto with arith.
apply cpo_le_lub. intro. unfold seq_lift_left. unfold fmon_as_fun.
simpl. apply cpo_lub_le.
Qed.

Definition cta (x : A) : nat-m>A.
exists (fun _ => x).
split.
- split.
  apply PartialOrder_instance_0.
  apply cpo_po.
  split.
  apply PartialOrder_instance_0.
  apply cpo_po.
  reduce. destruct H0. destruct cpo_po0. reflexivity.
- intros. reflexivity.
Defined.

End LubLemmas.


Global Instance lub_eq_wd {A} `{CompletePartialOrder A} : Proper (equiv ==> equiv) lub.
Proof.
reduce.
apply po_antisym.
- destruct H0. destruct cpo_po0. apply lub_le_compat.
  unfold le. unfold sub_leq_inst. unfold sub_leq.
  unfold sig_le. unfold le. unfold arrow_leq_inst. unfold arrow_leq.
  intro. unfold equiv in H1. unfold sub_equiv in H1. unfold sig_equiv in H1.
  unfold equiv in H1. unfold arrow_equiv in H1. rewrite H1. reflexivity.
- destruct H0. destruct cpo_po0. apply lub_le_compat.
  unfold le. unfold sub_leq_inst. unfold sub_leq.
  unfold sig_le. unfold le. unfold arrow_leq_inst. unfold arrow_leq.
  intro. unfold equiv in H1. unfold sub_equiv in H1. unfold sig_equiv in H1.
  unfold equiv in H1. unfold arrow_equiv in H1. rewrite H1. reflexivity.
Qed.

Section continuous_maps.

Context {A B} `{CompletePartialOrder A} `{CompletePartialOrder B} (f: A-m>B).

Class LimitPreserving :=
  { limit_preserving: forall (s:nat-m>A), lub (fmon_comp f s) = f (lub s) }.

End continuous_maps.

Lemma limit_compose_preserving_is_preserving {A B C}
  `{CompletePartialOrder A} `{CompletePartialOrder B} `{CompletePartialOrder C}:
  forall (f: B-m>C) (g: A-m>B),
    LimitPreserving f ->
    LimitPreserving g ->
    LimitPreserving (fmon_comp f g).
Proof.
intros f g f_lp g_lp.
split. intro s.
unfold fmon_comp at 3.
unfold compose.
simpl.
destruct H0. destruct H2. destruct H4.
destruct cpo_po0. destruct cpo_po1. destruct cpo_po2.
assert (SetoidMorphism f). { apply (proj2_sig f). }
rewrite <- limit_preserving.
rewrite <- limit_preserving.
assert (fmon_comp (fmon_comp f g) s = fmon_comp f (fmon_comp g s)). {
unfold fmon_comp.
unfold equiv. unfold sub_equiv. unfold sig_equiv. simpl.
unfold compose.  reflexivity.
}
rewrite H2.
reflexivity.
assumption.
assumption.
Qed.
