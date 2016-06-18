Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.Arith.Peano_dec.
Require Import Aniceto.Map.

Require Coq.FSets.FMapFacts.

Require Import Tid.

Structure node := {
  n_task: tid;
  n_id: nat
}.

Definition zero t := {| n_task := t; n_id:= 0 |}.


Module NODE <: OrderedType.
  Definition t := node.
  Definition eq := @eq node.
  Definition lt n1 n2 := n_id n1 < n_id n2 \/ (n_id n1 = n_id n2 /\ TID.lt (n_task n1) (n_task n2)).

  Lemma eq_refl:
    forall x,
    eq x x.
  Proof.
    unfold eq; trivial.
  Qed.

  Lemma eq_sym:
    forall x y,
    eq x y ->
    eq y x.
  Proof.
    unfold eq; auto.
  Qed.

  Lemma eq_trans :
    forall x y z,
    eq x y ->
    eq y z ->
    eq x z.
  Proof.
    unfold eq.
    intros; subst; trivial.
  Qed.

  Lemma lt_trans:
    forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    unfold lt.
    intros.
    destruct H as [?|(?,?)], H0 as [?|(?,?)]; eauto using TID.lt_trans with *.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold eq, lt.
    intros.
    destruct H as [?|(?,?)].
    - intuition; subst; auto with *.
    - intuition; subst.
      apply TID.lt_not_eq in H0.
      eauto using TID.lt_not_eq with *.
  Qed.

  Require Import Coq.Structures.OrderedTypeEx.
  Require Import Coq.Arith.Compare_dec.
  Lemma compare:
    forall x y, Compare lt eq x y.
  Proof.
    intros.
    unfold lt.
    destruct (Nat_as_OT.compare (n_id x) (n_id y));
    unfold Nat_as_OT.lt, Nat_as_OT.eq in *;
    auto using LT, GT.
    destruct (TID.compare (n_task x) (n_task y));
    auto using LT, GT. 
    destruct x, y.
    unfold TID.eq in *.
    simpl in *; subst.
    apply EQ.
    unfold eq; auto.
  Qed.

  Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros.
    unfold eq.
    destruct x as (x1,x2), y as (y1,y2).
    destruct (tid_eq_dec x1 y1), (eq_nat_dec x2 y2); subst; eauto;
      right;
      intuition;
      inversion H; subst;
      contradiction n; auto.
  Qed.

End NODE.

Lemma node_eq_rw:
  forall x y, NODE.eq x y <-> x = y.
Proof.
  unfold NODE.eq; intuition. 
Qed.

Lemma node_eq_dec:
  forall (x y:node),
  { x = y } + { x <> y }.
Proof.
  intros.
  destruct (NODE.eq_dec x y); rewrite node_eq_rw in *; auto.
Qed.

Module MN := FMapAVL.Make NODE.
Module MN_Facts := FMapFacts.Facts MN.
Module MN_Props := FMapFacts.Properties MN.
Module MN_Extra := MapUtil MN.

