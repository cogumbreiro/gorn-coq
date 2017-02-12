Require Coq.Arith.Compare_dec.

Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.Arith.Peano_dec.
Require Import Omega.

Require Import Aniceto.Map.

Require Coq.FSets.FMapFacts.

Inductive tid := taskid : nat -> tid.

Definition tid_nat r := match r with | taskid n => n end.

Definition tid_first := taskid 0.

Definition tid_next m := taskid (S (tid_nat m)).

Module TID <: UsualOrderedType.
  Definition t := tid.
  Definition eq := @eq tid.
  Definition lt x y := lt (tid_nat x) (tid_nat y).
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Lemma lt_trans: forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros.
    unfold lt in *.
    destruct x, y, z.
    simpl in *.
    omega.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold lt in *.
    intros.
    destruct x, y.
    simpl in *.
    unfold not; intros.
    inversion H0.
    subst.
    apply Lt.lt_irrefl in H.
    inversion H.
  Qed.

  Import Coq.Arith.Compare_dec.
  Lemma compare:
    forall x y, Compare lt eq x y.
  Proof.
    intros.
    destruct x, y.
    destruct (Nat_as_OT.compare n n0);
    eauto using LT, GT.
    apply EQ.
    unfold Nat_as_OT.eq in *.
    subst.
    intuition.
  Defined.

  Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros.
    unfold eq.
    destruct x, y.
    destruct (eq_nat_dec n n0).
    - subst; eauto.
    - right.
      unfold not.
      intros.
      contradiction n1.
      inversion H; auto.
  Defined.
End TID.


Module MT := FMapAVL.Make TID.
Module MT_Facts := FMapFacts.Facts MT.
Module MT_Props := FMapFacts.Properties MT.
Module MT_Extra := MapUtil MT.
Module ST := FSetAVL.Make TID.
Definition set_tid := ST.t.

Lemma tid_eq_rw:
  forall (k k':tid), TID.eq k k' <-> k = k'.
Proof.
  intros.
  auto with *.
Qed.

Lemma tid_eq_dec:
  forall x y : tid, {x = y} + {x <> y}.
Proof.
  auto using tid_eq_rw, TID.eq_dec.
Defined.

Section NotIn.
  Variable elt:Type.

  Let lt_irrefl:
    forall x : tid, ~ TID.lt x x.
  Proof.
    unfold not; intros.
    apply TID.lt_not_eq in H.
    contradiction H.
    apply TID.eq_refl.
  Qed.

  Let lt_next:
    forall x, TID.lt x (tid_next x).
  Proof.
    intros.
    destruct x.
    unfold tid_next, tid_nat, TID.lt.
    simpl.
    auto.
  Qed.

  Let tid_impl_eq:
    forall k k' : tid, k = k' -> k = k'.
  Proof.
    auto.
  Qed.

  Definition supremum {elt:Type} := @MT_Extra.supremum elt tid_first tid_next TID.lt TID.compare.

  Theorem find_not_in:
    forall (m: MT.t elt),
    ~ MT.In (supremum m) m.
  Proof.
    intros.
    eauto using MT_Extra.find_not_in, TID.lt_trans.
  Qed.

End NotIn.