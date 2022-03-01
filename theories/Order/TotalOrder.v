Require Export Coq.Relations.Relations.
Require Export Coq.Classes.RelationClasses.
From LexLatStruct Require Export Basic.
From LexLatStruct.Order Require Export PartialOrder.

Class TotalOrder {A} `{Ae : Equiv A} (Ale : Le A) : Prop :=
  { total_order_po :> PartialOrder (≤)
  ; total_order_total :> TotalRelation (≤) }.
