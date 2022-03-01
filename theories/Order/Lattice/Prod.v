From LexLatStruct.Order Require Import Lattice.
From LexLatStruct.Order.Partial Require Import Prod.
From LexLatStruct Require Export Basic.

Section ProdLattice.

Context {A} {B} {lea : Le A} {leb : Le B} `{Equiv A} `{!CompleteLattice lea} `{Equiv B}  `{!CompleteLattice leb}.

Instance prod_is_clat : CompleteLattice (@prod_leq A B lea leb).
  exists (fun (S : Ensemble (A*B)) => (inf (fun (l1:A) => exists l2, S(l1,l2)), inf (fun (l2:B) => exists l1, S(l1,l2)))).
  apply prod_is_partialorder; apply ltord.
unfold Lower_Bound. unfold le. unfold prod_leq. simpl. intros P s Ps.
  split. apply Pinf. reduce. exists (snd s).
  assert (ss:= surjective_pairing). rewrite <- ss. apply Ps.
  apply Pinf. reduce. exists (fst s).
  assert (ss:= surjective_pairing). rewrite <- ss. apply Ps.
unfold Lower_Bound. unfold le. unfold prod_leq. simpl. intros P s Ps.
split. apply PinfL. unfold Lower_Bound. intros. reduce in H1. case H1. intros.
specialize Ps with (s:=(pair s0 x)). apply Ps in H2. destruct H2. apply H2.
apply PinfL. unfold Lower_Bound. intros. reduce in H1. case H1. intros.
specialize Ps with (s:=(pair x s0)). apply Ps in H2. destruct H2. apply H3.
Qed.

End ProdLattice.
