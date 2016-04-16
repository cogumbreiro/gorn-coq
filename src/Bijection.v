Set Implicit Arguments.

Require Import Coq.Lists.List.
Require Omega.

Section Defs.
  Variable A:Type.

  Inductive IndexOf (x:A) : nat -> list A -> Prop :=
  | index_of_eq:
    forall l,
    IndexOf x (length l) (x :: l)
  | index_of_cons:
    forall y n l,
    IndexOf x n l ->
    IndexOf x n (y :: l).

  Lemma index_of_to_in:
    forall x n l,
    IndexOf x n l ->
    In x l.
  Proof.
    intros.
    induction l. {
      inversion H.
    }
    inversion H; subst.
    - auto using in_eq.
    - auto using in_cons.
  Qed.

  Lemma index_of_fun:
    forall l x n n',
    NoDup l ->
    IndexOf x n l ->
    IndexOf x n' l ->
    n' = n.
  Proof.
    intros.
    induction l. {
      inversion H0.
    }
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    - inversion H1; subst; clear H1.
      + trivial.
      + contradiction H4; eauto using index_of_to_in.
    - inversion H1; subst; clear H1.
      + contradiction H4; eauto using index_of_to_in.
      + eauto.
  Qed.

  Lemma index_of_length_lt:
    forall x n l,
    IndexOf x n l ->
    n < length l.
  Proof.
    intros.
    induction l. {
      inversion H.
    }
    inversion H; subst.
    - auto.
    - simpl.
      assert (n < length l) by eauto.
      eauto.
  Qed.

  Lemma in_to_index_of:
    forall l x,
    In x l ->
    exists n, n < length l /\ IndexOf x n l.
  Proof.
    induction l; intros. {
      inversion H.
    }
    destruct H.
    - subst.
      exists (length l).
      simpl.
      eauto using index_of_eq.
    - apply IHl in H.
      destruct H as (n, (?,?)).
      exists n.
      simpl.
      eauto using index_of_cons.
  Qed.

  Lemma index_of_bij:
    forall l x x' n,
    NoDup l ->
    IndexOf x n l ->
    IndexOf x' n l ->
    x' = x.
  Proof.
    intros.
    induction l. {
      inversion H0.
    }
    inversion H; clear H; subst.
    inversion H0; subst; clear H0.
    - inversion H1; subst; clear H1.
      + trivial.
      + assert (length l < length l). {
          eauto using index_of_length_lt.
        }
        omega.
    - inversion H1; subst; clear H1.
      + assert (length l < length l). {
          eauto using index_of_length_lt.
        }
        omega.
      + eauto.
  Qed.

  Lemma index_of_neq:
    forall l x y n n',
    NoDup l ->
    IndexOf x n l ->
    IndexOf y n' l ->
    n <> n' ->
    x <> y.
  Proof.
    intros.
    induction l. {
      inversion H0.
    }
    inversion H; clear H; subst.
    inversion H0; subst; clear H0.
    - inversion H1; subst; clear H1.
      + omega.
      + unfold not; intros; subst.
        contradiction H5.
        eauto using index_of_to_in.
    - inversion H1; subst; clear H1.
      + unfold not; intros; subst.
        contradiction H5.
        eauto using index_of_to_in.
      + eauto.
  Qed.

  Inductive Lt (l:list A) (x:A) (y:A) : Prop :=
  | lt_def:
    forall xn yn,
    IndexOf x xn l ->
    IndexOf y yn l ->
    xn < yn ->
    Lt l x y.

  Lemma lt_trans (l:list A) (N:NoDup l):
    forall x y z,
    Lt l x y ->
    Lt l y z ->
    Lt l x z.
  Proof.
    intros.
    inversion H; clear H.
    inversion H0; clear H0.
    rename yn0 into zn.
    assert (xn0 = yn) by
    eauto using index_of_fun; subst.
    apply lt_def with (xn:=xn) (yn:=zn); auto.
    omega.
  Qed.

  Lemma lt_neq (l:list A) (N:NoDup l):
    forall x y,
    Lt l x y ->
    x <> y.
  Proof.
    intros.
    inversion H; clear H.
    assert (xn <> yn) by omega.
    eauto using index_of_neq.
  Qed.

  Lemma lt_absurd_nil:
    forall x y,
    ~ Lt nil x y.
  Proof.
    intuition.
    destruct H.
    inversion H.
  Qed.

  Lemma lt_cons:
    forall z l x y,
    Lt l x y ->
    Lt (z :: l) x y.
  Proof.
    intros.
    inversion H.
    eauto using lt_def, index_of_cons.
  Qed.

End Defs.


