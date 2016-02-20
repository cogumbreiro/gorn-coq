Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.FSets.FMapAVL.
Require Coq.FSets.FMapFacts.
Require Coq.FSets.FSetProperties.
Require Coq.FSets.FSetBridge.
Require Import Aniceto.Map.

Module NAME := Nat_as_OT.
Module NAME_Facts := OrderedTypeFacts NAME.
Module Set_NAME := FSetAVL.Make NAME.
Module Set_NAME_Props := FSetProperties.Properties Set_NAME.
(*Module Set_NAME_Extra := SetUtil Set_NAME.*)
Module Set_NAME_Dep := FSetBridge.DepOfNodep Set_NAME.
Module MN := FMapAVL.Make NAME.
Module MN_Facts := FMapFacts.Facts MN.
Module MN_Props := FMapFacts.Properties MN.
Module MN_Extra := MapUtil MN.

Definition name := NAME.t.
Definition set_name := Set_NAME.t.

Lemma name_eq_rw:
  forall k k' : name, k = k' <-> k = k'.
Proof.
  intros.
  auto with *.
Qed.
