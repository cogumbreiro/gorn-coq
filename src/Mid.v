Set Implicit Arguments.

Require Coq.Arith.Compare_dec.

Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.Arith.Peano_dec.
Require Import Omega.

Require Import Aniceto.Map.

Require Coq.FSets.FMapFacts.

Inductive mid := memid : nat -> mid.

Definition mid_nat r := match r with | memid n => n end.

Definition mid_first := memid 0.

Definition mid_next m := memid (S (mid_nat m)).

Module MID <: UsualOrderedType.
  Definition t := mid.
  Definition eq := @eq t.
  Definition lt x y := lt (mid_nat x) (mid_nat y).
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
  Qed.

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
  Qed.
End MID.

Lemma mid_eq_rw:
  forall x y, MID.eq x y <-> x = y.
Proof.
  intros.
  auto with *.
Qed.

Definition eqb (x y:mid) := if MID.eq_dec x y then true else false.

Module MM := FMapAVL.Make MID.
Module MM_Facts := FMapFacts.Facts MM.
Module MM_Extra := MapUtil MM.

Module SM := FSetAVL.Make MID.
Definition set_mid := SM.t.

Section NotIn.
  Variable elt:Type.

  Let lt_irrefl:
    forall x : mid, ~ MID.lt x x.
  Proof.
    unfold not; intros.
    apply MID.lt_not_eq in H.
    contradiction H.
    apply MID.eq_refl.
  Qed.

  Let lt_next:
    forall x : mid, MID.lt x (mid_next x).
  Proof.
    intros.
    destruct x.
    unfold mid_next, mid_nat, MID.lt.
    simpl.
    auto.
  Qed.

  Let mid_impl_eq:
    forall k k' : mid, k = k' -> k = k'.
  Proof.
    auto.
  Qed.

  Definition supremum {elt:Type} := @MM_Extra.supremum elt mid_first mid_next MID.lt MID.compare.

  Theorem find_not_in:
    forall (m: MM.t elt),
    ~ MM.In (supremum m) m.
  Proof.
    intros.
    eauto using MM_Extra.find_not_in, MID.lt_trans.
  Qed.

End NotIn.

Lemma mid_eq_dec:
  forall x y : mid, {x = y} + {x <> y}.
Proof.
  auto using mid_eq_rw, MID.eq_dec.
Qed.
