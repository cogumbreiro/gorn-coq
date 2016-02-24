Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FMapAVL.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.Arith.Peano_dec.
Require Import Aniceto.Map.

Require Coq.FSets.FMapFacts.

Require Import HJ.Mid.
Require Import HJ.Tid.

Notation dep := (mid + tid)%type.

Notation d_mid := (@inl mid tid).

Notation d_tid := (@inr mid tid).

Module SumOrderedType (O1 O2:OrderedType) <: OrderedType.
  Definition t := sum O1.t O2.t.
  Definition eq o1 o2 :=
    match o1 with
    | inl l =>
      match o2 with
      | inl r => O1.eq l r
      | inr r => False
      end
    | inr l =>
      match o2 with
      | inl r => False
      | inr r => O2.eq l r
      end
    end.
    
  Definition lt o1 o2 :=
    match o1 with
    | inl l =>
      match o2 with
      | inl r => O1.lt l r
      | inr r => True
      end
    | inr l =>
      match o2 with
      | inl r => False
      | inr r => O2.lt l r
      end
    end.

  Lemma eq_refl:
    forall x,
    eq x x.
  Proof.
    intros.
    destruct x; simpl; eauto using O1.eq_refl, O2.eq_refl.
  Qed.

  Lemma eq_sym:
    forall x y,
    eq x y ->
    eq y x.
  Proof.
    intros.
    destruct x, y; simpl in *; eauto using O1.eq_sym, O2.eq_sym.
  Qed.

  Lemma eq_trans :
    forall x y z,
    eq x y ->
    eq y z ->
    eq x z.
  Proof.
    intros.
    destruct x, y, z; simpl in *.
    - eauto using O1.eq_trans.
    - inversion H0.
    - inversion H0.
    - inversion H.
    - inversion H.
    - inversion H.
    - inversion H0.
    - eauto using O2.eq_trans.
  Qed.

  Lemma lt_trans:
    forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros.
    unfold lt in *.
    destruct x, y, z; auto.
    - eauto using O1.lt_trans.
    - inversion H0.
    - inversion H.
    - eauto using O2.lt_trans.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    intros.
    destruct x, y; simpl in *.
    - eauto using O1.lt_not_eq.
    - intuition; inversion H0.
    - inversion H.
    - eauto using O2.lt_not_eq.
  Qed.

  Require Import Coq.Arith.Compare_dec.
  Lemma compare:
    forall x y, Compare lt eq x y.
  Proof.
    intros.
    destruct x, y.
    - assert (C: Compare O1.lt O1.eq t0 t1) by eauto using O1.compare.
      destruct C; eauto using LT, EQ, GT.
    - apply LT.
      simpl.
      trivial.
    - apply GT.
      simpl.
      trivial.
    - assert (C: Compare O2.lt O2.eq t0 t1) by eauto using O2.compare.
      destruct C; eauto using LT, EQ, GT.
  Qed.

  Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros.
    destruct x, y; simpl; eauto using O1.eq_dec, O2.eq_dec.
  Qed.

  Lemma eq_rw
    (o1_eq_rw: forall x y, O1.eq x y <-> x = y)
    (o2_eq_rw: forall x y, O2.eq x y <-> x = y):
    forall x y, eq x y <-> x = y.
  Proof.
    intros.
    destruct x, y; simpl in *.
    - split.
      + intros.
        apply o1_eq_rw in H; subst.
        trivial.
      + intros.
        inversion H; subst.
        rewrite o1_eq_rw.
        trivial.
    - split; intros; inversion H.
    - split; intros; inversion H.
    - split.
      + intros.
        apply o2_eq_rw in H; subst.
        trivial.
      + intros.
        inversion H; subst.
        rewrite o2_eq_rw.
        trivial.
  Qed.

End SumOrderedType.

Module DEP := SumOrderedType MID TID.

Lemma dep_eq_rw:
  forall x y, DEP.eq x y <-> x = y.
Proof.
  intros.
  split;
  intros;
  apply DEP.eq_rw in H; auto using mid_eq_rw, tid_eq_rw.
Qed.

Module SD := FSetAVL.Make DEP.
Definition set_dep := SD.t.

