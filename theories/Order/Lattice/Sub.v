From LexLatStruct.Order Require Import Lattice.
From LexLatStruct.Order.Partial Require Import Sub.
From LexLatStruct Require Export Basic.

Section SubLattices.

Context {A} {P : A->Prop} `{Equiv A} (leq : Le A)  `{!CompleteLattice leq}.

Variable PSinf: forall (S : Ensemble A), (forall t, S t -> P t) -> P (inf S).

Definition Embed (t : A) (p : P t) : { x : A | P x }.
exists t . apply p.
Defined.

Definition Extend (S : { x : A | P x } -> Prop) : A -> Prop.
intro l. apply (exists p:P l, S (Embed l p)).
Defined.

Lemma ExtendP : forall (S : {x : A | P x} -> Prop) t, Extend S t -> P t.
intros S t Ex. unfold Extend in Ex. unfold Embed in Ex. destruct Ex as [E _]. apply E.
Defined.

Existing Instance sub_equiv.

Global Instance sub_is_clat : CompleteLattice (sub_leq (P:=P) leq).
exists (fun (S : Ensemble { x : A | P x }) => Embed (inf (Extend S)) (PSinf (Extend S) (ExtendP S))).
destruct CompleteLattice0. apply subord_is_partialorder. apply ltord.
- intros P0 t C. unfold le. unfold sub_leq. unfold inf. refine (Pinf _ _ _).
unfold contains. unfold Extend. unfold Embed. red. exists (proj2_sig t). destruct t. apply C.
- intros P0 t C. unfold le. unfold sub_leq. destruct CompleteLattice0. apply PinfL. unfold le in C. unfold sub_leq in C. intros x Ex.
unfold Extend in Ex. unfold Embed in Ex. destruct Ex as [Pt St]. specialize (C _ St). apply C.
Qed.


End SubLattices.
