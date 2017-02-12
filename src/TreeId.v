Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Psatz.

Import ListNotations.

Definition tree_id := (nat * list nat) % type.

Notation root := (0, []).

Module TreeId.
  Definition tick (p:tree_id) :=
  let (n, l) := p in (S n, l).

  Definition child (p:tree_id) : tree_id :=
  let (n, l) := p in (0, n :: l).

  Definition add (p:tree_id) m :=
  let (n, l) := p in (n + m, l).
End TreeId.

Module Interval.
  Section Spec.
  
  Import TreeId.

  Require Import Coq.QArith.QArith.

  Definition interval := (Q * Q) % type.

  Definition max (x y:Q) :=
  if Qlt_le_dec x y then y else x.

  Definition min (x y:Q) :=
  if Qlt_le_dec x y then x else y.

  Definition merge (i j:interval) : interval :=
  let (l1, h1) := i in
  let (l2, h2) := j in
  (min l1 l2, max h1 h2).

  Open Scope Q_scope.

  Definition iroot : interval := (0, 1).

  Definition halve (i:interval) := 
  let (l, h) := i in
  (h - l) * (1# 2).

  Definition itick (i:interval) :=
  let (l, h) := i in
  (l, h - halve i).

  Definition ichild (i:interval) :=
  let (l, h) := i in
  (h - halve i, h).

  Fixpoint iadd (i:interval) (n:nat) :=
  match n with
  | 0 % nat => i
  | S n => iadd (itick i) n
  end.

  Fixpoint itree (l:list nat) :=
  match l with
  | nil => iroot
  | n :: l => iadd (ichild (itree l)) n
  end.

  Definition from_tree (t:tree_id) :=
  let (n, l) := t in itree (n:: l).

  Lemma tick_add_0:
    forall i,
    itick i = iadd i 1.
  Proof.
    intros.
    auto.
  Qed.

  Lemma itick_iadd:
    forall n i,
    iadd (itick i) n = itick (iadd i n).
  Proof.
    induction n; intros. {
      simpl; auto.
    }
    simpl.
    rewrite IHn.
    auto.
  Qed.

  Lemma itick_iadd_1:
    forall n i,
    itick (iadd i n) = iadd i (S n).
  Proof.
    intros.
    simpl.
    rewrite itick_iadd.
    auto.
  Qed.

  Lemma tick_1:
    forall (t:tree_id),
    itick (from_tree t) = from_tree (tick t).
  Proof.
    intros.
    destruct t.
    simpl.
    rewrite itick_iadd.
    auto.
  Qed.

  Lemma iadd_iadd:
    forall n (i:interval) m,
    iadd (iadd i n) m = iadd i (n + m).
  Proof.
    induction n; intros. {
      simpl; auto.
    }
    simpl.
    rewrite IHn.
    auto.
  Qed.

  Lemma add_1:
    forall (t:tree_id) n,
    iadd (from_tree t) n = from_tree (add t n).
  Proof.
    intros.
    destruct t.
    simpl.
    rewrite iadd_iadd.
    auto.
  Qed.

  Lemma ichild_child:
    forall t,
    from_tree (child t) = ichild (from_tree t).
  Proof.
    intros.
    destruct t.
    simpl.
    auto.
  Qed.

  Goal iroot = (0, 1).
    auto.
  Qed.

  Goal itick iroot = (0, 1 # 2).
    simpl.
    compute.
    auto.
  Qed.

  Goal ichild iroot = (1 # 2, 1).
    auto.
  Qed.

  Goal itick (ichild iroot) = (1#2, 3#4).
    simpl.
    compute.
    auto.
  Qed.

  Goal ichild (ichild iroot) = (3#4, 1).
    compute.
    auto.
  Qed.

  Goal itree [2%nat] = itick (itick (ichild iroot)).
    compute.
    auto.
  Qed.

  Inductive Overlap: interval -> interval -> Prop :=
  | overlap_def:
    forall l1 h1 l2 h2,
    l1 <= h2 ->
    l2 < h1 ->
    Overlap (l1, h1) (l2, h2).

  Lemma overlap_dec i1 i2 :
    { Overlap i1 i2 } + { ~ Overlap i1 i2 }.
  Proof.
    destruct i1 as (l1,h1), i2 as (l2,h2).
    destruct (Qlt_le_dec h2 l1). {
      right.
      unfold not; intros.
      inversion H.
      lra.
    }
    destruct (Qlt_le_dec l2 h1). {
      auto using overlap_def.
    }
    right.
    unfold not; intros N.
    inversion N.
    lra.
  Defined.

  Inductive Follows: interval -> interval -> Prop :=
  | follows_def:
    forall l1 h1 l2 h2,
    h1 == l2 ->
    Follows (l1, h1) (l2, h2).

  Inductive Contiguous i1 i2 : Prop :=
  | contiguous_l:
    Follows i1 i2 ->
    Contiguous i1 i2
  | contiguous_2:
    Follows i2 i1 ->
    Contiguous i1 i2.

  Inductive Prec : interval -> interval -> Prop :=
  | prec_def:
    forall l1 h1 l2 h2,
    h1 < l2 ->
    Prec (l1, h1) (l2, h2).

  Inductive CanMerge i1 i2 : Prop :=
  | can_merge_overlap:
    Overlap i1 i2 ->
    CanMerge i1 i2
  | can_merge_contiguous:
    Contiguous i1 i2 ->
    CanMerge i1 i2.

End Spec.
End Interval.

Module Event.
  Import Interval.
  Definition event := (interval * nat) % type.

  Definition union (e1 e2:event) :=
  let (i1, n1) := e1 in
  let (i2, n2) := e2 in
  (merge i1 i2, Nat.max n1 n2).

  Inductive Lt : event -> event -> Prop :=
  | lt_def:
    forall i1 i2 n1 n2,
    Overlap i1 i2 ->
    n1 < n2->
    Lt (i1, n1) (i2, n2).

  Lemma lt_trans:
    forall e1 e2 e3,
    Overlap (fst e1) (fst e3) ->
    Lt e1 e2 ->
    Lt e2 e3 ->
    Lt e1 e3.
  Proof.
    intros (i1, n1) (i2, n2) (i3, n3); intros.
    inversion H0; inversion H1; subst; clear H0 H1; simpl in *; subst.
    auto using lt_def with *.
  Qed.

  Inductive CanUnion: event -> event -> Prop :=
  | can_union_def:
    forall i1 i2 n1 n2,
    CanMerge i1 i2 ->
    CanUnion (i1,n1) (i2,n2).

End Event.

Module Stamp.
  Import Event.
  Definition stamp := (event * list event) % type.

  Definition Le l1 l2 :=
    forall x y,
    List.In x l1 ->
    List.In y l2 ->
    Event.Le x y.

End Stamp.

Module Others.

  Inductive Observes : list nat -> list nat -> Prop :=
  | observes_def:
    forall x y l,
    x > y ->
    Observes (x::l) (y::l).

  Inductive Spawn: tree_id -> tree_id -> Prop :=
  | spawn_def:
    forall n l,
    Spawn (S n, l) (0, n::l).

  Inductive ParentOf : tree_id -> tree_id -> Prop :=
  | parent_of_def:
    forall a b c l,
    a > c ->
    ParentOf (a, l) (b, c :: l).

  Lemma spawn_to_parent_of:
    forall x y,
    Spawn x y ->
    ParentOf x y.
  Proof.
    intros.
    inversion H; subst; clear H.
    apply parent_of_def.
    auto.
  Qed.

Definition parent_of (l:list nat) (r:list nat) :=
match r with
| _ :: r => if (list_eq_dec PeanoNat.Nat.eq_dec l r) then true else false
| _ => false
end.

(*
Goal parent_of [0;0] [1;0;0]  = true.
  compute.
  trivial.
Qed.
*)
Definition lt_sibling (l r:list nat) :=
match l, r with
| x :: l, y :: r =>
  if (lt_dec x y) then
    if (list_eq_dec PeanoNat.Nat.eq_dec l r) then true else false
  else false
| _,_ => false
end.

Definition gt_sibling (l r:list nat) := lt_sibling r l.

Definition contains (i j:list nat) :=
let fix ancestor_gt_sibling i j :=
  match i with
  | _ :: i => gt_sibling i j || ancestor_gt_sibling i j
  | _ => false
  end
in
if parent_of i j then true else ancestor_gt_sibling i j.
(*
Goal contains [3;1;0] [0;0]  = true.
  compute; auto.
Qed.

Goal contains [3;1;0] [2;0]  = false.
  compute;auto.
Qed.

Goal contains [3;3;0] [2;0]  = true.
  compute;auto.
Qed.
*)
Section AsCG.
  Require Import SafeJoins.
  Import SJ_Notations.
  Require Import Tid.

  Inductive MapsTo : tree_id -> tid -> list op -> Prop :=
  | maps_to_tick_root:
    forall x y,
    MapsTo (tick root) x [F x y]
  | maps_to_child_root:
    forall x y,
    MapsTo (child root) y [F x y]
  | maps_to_fork_parent:
    forall x y t k,
    MapsTo t x k ->
    MapsTo (tick t) x (F x y::k)
  | maps_to_fork_child:
    forall x y t k,
    MapsTo t x k ->
    MapsTo (child t) y (F x y::k)
  | maps_to_fork_neq:
    forall x y z k t,
    z <> x ->
    MapsTo t z k ->
    MapsTo t z (F x y::k)
  | maps_to_join:
    forall x y z t k,
    MapsTo t z k ->
    MapsTo t z (J x y::k).

  Lemma maps_to_inv_0:
    forall t x y,
    x <> y ->
    MapsTo t x [F x y] ->
    t = tick root.
  Proof.
    intros.
    inversion H0; subst; clear H0; auto; intuition.
    inversion H4.
  Qed.

  Lemma maps_to_inv_1:
    forall t x y,
    x <> y ->
    MapsTo t y [F x y] ->
    t = child root.
  Proof.
    intros.
    inversion H0; subst; clear H0; subst; simpl; intuition.
    + inversion H4.
    + inversion H7.
  Qed.

  Lemma maps_to_inv_2:
    forall t x o,
    MapsTo t x [o] ->
    exists y,
    (o = F x y /\ t = tick root)
    \/
    (o = F y x /\ t = child root).
  Proof.
    intros.
    inversion H; subst; clear H; eauto; try inversion H3.
    inversion H5.
  Qed.

  Lemma trace_inv_0:
    forall o,
    Trace [o] ->
    exists x y, F x y = o.
  Proof.
    intros.
    inversion H; subst. {
      eauto.
    }
    inversion H; subst.
    inversion H3.
  Qed.

  Lemma maps_to_inv_3:
    forall k t x y,
    x <> y ->
    k <> nil ->
    Trace (F x y :: k) ->
    MapsTo t x (F x y :: k) ->
    exists s, t = tick s /\ MapsTo s x k.
  Proof.
    induction k; intros; auto. {
      intuition.
    }
    destruct k. {
      inversion H1; subst; clear H1.
      inversion H2; subst; clear H2; intuition.
      apply maps_to_inv_2 in H5.
      destruct H5 as (z, [(?,He)|(?,He)]); inversion He; subst. {
        eauto using maps_to_tick_root.
      }
      eauto using maps_to_child_root.
    }
    inversion H1; subst; clear H1.
    inversion H2; subst; clear H2; eauto; intuition.
  Qed.

  Lemma maps_to_to_in:
    forall t x k,
    MapsTo t x k ->
    Graph.In (Edge k) x.
  Proof.
    intros.
    induction H;
    eauto using
    Graph.in_left, Graph.in_right,
    edge_fork_eq, Graph.in_impl, edge_cons.
  Qed.

  Lemma maps_to_fun:
    forall k t s x,
    Trace k ->
    MapsTo t x k ->
    MapsTo s x k ->
    t = s.
  Proof.
    induction k; intros. {
      inversion H0.
    }
    destruct a as ([], a, b). {
      inversion H; subst.
      inversion H0; subst; clear H0.
      + apply maps_to_inv_0 in H1; auto.
      + apply maps_to_inv_1 in H1; auto.
      + destruct k. {
          inversion H8.
        }
        apply maps_to_inv_3 in H1; auto with *.
        destruct H1 as (s', (?, Hm)).
        subst.
        apply IHk with (t:=t0) in Hm; subst; auto.
      + inversion H1; subst; clear H1; intuition.
        * inversion H8.
        * assert (t0 = t) by eauto; subst; auto.
        * contradiction H6.
          eauto using maps_to_to_in.
      + inversion H1; subst; clear H1; intuition.
        * inversion H11.
        * contradiction H6.
          eauto using maps_to_to_in.
        * eauto.
    }
    inversion H0; subst; clear H0.
    inversion H1; subst; clear H1.
    inversion H; subst; eauto.
  Qed.

  Lemma maps_to_inv_4:
    forall x y s t k,
    Trace (F x y :: k) ->
    MapsTo s x (F x y :: k) ->
    MapsTo t x k ->
    s = tick t.
  Proof.
    intros.
    destruct k. {
      inversion H1.
    }
    inversion H; subst.
    apply maps_to_inv_3 in H0; auto with *.
    destruct H0 as (t', (He, Hm)); subst.
    assert (He: t = t') by eauto using maps_to_fun.
    subst; auto.
  Qed.

  Lemma maps_to_inv_5:
    forall x y z t,
    x <> y ->
    MapsTo t z [F x y] ->
    (t = tick root /\ z = x) \/
    (t = child root /\ z = y).
  Proof.
    intros.
    inversion H0; subst; auto; try inversion H4.
    inversion H7.
  Qed.

  Lemma maps_to_inv_6:
    forall x y z,
    MapsTo (tick root) x [F y z] ->
    y = x.
  Proof.
    intros.
    inversion H; subst; clear H; auto. {
      inversion H3.
    }
    inversion H6.
  Qed.

  Lemma maps_to_inv_7:
    forall x y z,
     MapsTo (child root) x [F y z] ->
     x = z.
   Proof.
    intros.
    inversion H; subst; clear H; auto. {
      inversion H3.
    }
    inversion H6.
   Qed.

  Lemma child_neq_tick:
    forall x y,
    child x <> tick y.
  Proof.
    intros.
    unfold not; intros.
    destruct x, y.
    simpl in *.
    inversion H.
  Qed.

  Lemma maps_to_absurd_0:
    forall k n m l x y,
    n <> m ->
    MapsTo (n, l) x k ->
    ~ MapsTo (m, l) y k.
  Proof.
    induction k; intros. {
      inversion H0.
    }
    unfold not; intros.
    inversion H0; subst; clear H0.
    - inversion H1; subst; clear H1.
      + contradiction H; auto.
      + inversion H4.
      + inversion H4.
      + inversion H7.
    - inversion H1; subst; clear H1.
      + contradiction H; auto.
      + inversion H4.
      + inversion H4.
      + inversion H7.
    - destruct t; subst.
      inversion H2; subst; clear H2.
      inversion H1; subst; clear H1.
      + inversion H5.
      + inversion H5.
      + destruct t.
        simpl in *.
        destruct m. {
          inversion H0.
        }
        inversion H0; subst; clear H0.
        assert (n0 <> m). {
          unfold not; intros; subst.
          contradiction H; auto.
        }
        eapply IHk in H4; eauto.
      + destruct t.
        simpl in *.
        destruct m. {
          inversion H0; subst; clear H0.
        }
        apply child_neq_tick in H; contradiction.
      + destruct t0.
        simpl in *.
        destruct n. {
          
        }
  Qed.

  Lemma maps_to_fun_2:
    forall k t x y,
    Trace k ->
    MapsTo t x k ->
    MapsTo t y k ->
    x = y.
  Proof.
    induction k; intros. {
      inversion H0.
    }
    inversion H; subst. {
      inversion H0; subst; clear H0.
      - apply maps_to_inv_6 in H1; subst; auto.
      - apply maps_to_inv_7 in H1; subst; auto.
      - inversion H1; subst; clear H1.
        + inversion H8.
        + inversion H8.
        + auto.
        + apply child_neq_tick in H0; contradiction.
        + apply IHk with (x:=x0) (y:=y) in H6.
    }
  Qed.


  Inductive In t k : Prop :=
  | in_def:
    forall x,
    MapsTo t x k ->
    In t k.

  Inductive TreeId t x : list op -> Prop :=
  | tree_id_eq:
    forall k,
    MapsTo t x k ->
    TreeId t x k
  | tree_id_cons:
    forall k e,
    TreeId t x k ->
    TreeId t x (e::k).

  Inductive ForkTree : tid * tid -> tree_id * tree_id -> list op -> Prop :=
  | fork_tree_eq:
    forall x y t1 t2 k,
    MapsTo t1 x (F x y::k) ->
    MapsTo t2 y (F x y::k) ->
    ForkTree (x,y) (t1, t2) (F x y::k)
  | fork_tree_cons:
    forall e1 e2 e3 k,
    ForkTree e1 e2 k ->
    ForkTree e1 e2 (e3::k).

  Lemma parent_of_child:
    forall t,
    ParentOf (tick t) (child t).
  Proof.
    intros (n, l).
    unfold tick, child; simpl.
    auto using parent_of_def, observes_def with *.
  Qed.

  Lemma fork_tree_to_parent_of:
    forall k x y s t,
    Trace k ->
    ForkTree (x, y) (s, t) k ->
    ParentOf s t.
  Proof.
    induction k; intros. {
      inversion H0.
    }
    inversion H0; subst; clear H0. {
      inversion H; subst.
      inversion H8; subst; clear H8; intuition.
      + apply maps_to_inv_0 in H4; auto; subst.
        auto using parent_of_child.
      + eapply maps_to_inv_4 in H7; eauto; subst.
        auto using parent_of_child.
      + contradiction H5.
        eauto using maps_to_to_in.
    }
    inversion H; subst; clear H; eauto.
  Qed.

  Let absurd_cons:
    forall {A} l (x:A), x :: l <> l.
  Proof.
    induction l; intros. {
      auto with *.
    }
    unfold not; intros N.
    inversion N.
    apply IHl in H1.
    contradiction.
  Qed.

  Let absurd_cons_cons:
    forall {A} l (x y:A), y :: x :: l <> l.
  Proof.
    induction l; intros. {
      auto with *.
    }
    unfold not; intros N.
    inversion N.
    apply IHl in H1.
    contradiction.
  Qed.

  Lemma observes_length:
    forall x y,
    Observes x y ->
    length x = length y.
  Proof.
    induction x; intros. {
      inversion H.
    }
    inversion H; subst.
    simpl; auto.
  Qed.

  Lemma observes_irrefl:
    forall x,
    ~ Observes x x.
  Proof.
    intros.
    unfold not; intros.
    inversion H; subst; clear H.
    intuition.
  Qed.

  Lemma observes_asymm:
    forall x y,
    Observes x y ->
    ~ Observes y x.
  Proof.
    intros.
    unfold not; intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    intuition.
  Qed.

  Lemma parent_of_asymm:
    forall x y,
    ParentOf x y ->
    ~ ParentOf y x.
  Proof.
    intros.
    unfold not; intros.
    inversion H; subst; clear H.
    inversion H0; clear H0.
    rewrite <- H3 in *.
    rewrite H3 in *.
    apply absurd_cons_cons in H5.
    contradiction.
  Qed.

  Lemma parent_of_irrefl:
    forall x,
    ~ ParentOf x x.
  Proof.
    intros.
    unfold not; intros.
    inversion H.
    apply absurd_cons in H3.
    contradiction.
  Qed.

  Lemma parent_of_tick_snd:
    forall x y,
    ParentOf x y ->
    ParentOf x (tick y).
  Proof.
    intros.
    inversion H; subst; clear H; simpl.
    apply parent_of_def; simpl; auto.
  Qed.

  Lemma parent_of_absurd_root:
    forall x,
    ~ ParentOf x root.
  Proof.
    intros.
    unfold not; intros.
    inversion H; subst.
  Qed.

  Lemma parent_of_absurd_tick_root:
    forall x,
    ~ ParentOf x (tick root).
  Proof.
    intros.
    unfold not; intros.
    inversion H; subst.
  Qed.

  Lemma spawn_absurd_tick_root:
    forall x,
    ~ Spawn x (tick root).
  Proof.
    unfold tick, not; intros.
    inversion H.
  Qed.

  Require Import Omega.

  Lemma parent_of_child_root:
    forall x,
    ParentOf x (child root) ->
    exists n, x = tick (n, []).
  Proof.
    intros.
    unfold tick.
    simpl.
    inversion H; subst; clear H.
    destruct a. {
      omega.
    }
    eauto.
  Qed.

  Let fork_tree_eq_0:
    forall x y,
    ForkTree (x, y) (tick root, child root) [F x y].
  Proof.
    intros.
    auto using fork_tree_eq, maps_to_tick_root, maps_to_child_root.
  Qed.

  Lemma parent_of_simpl_left:
    forall x y,
    ParentOf x (tick y) ->
    ParentOf x y.
  Proof.
    intros.
    destruct y as (n, l); simpl in *.
    inversion H; subst; clear H.
    auto using parent_of_def.
  Qed.

  Lemma fork_tree_eq_fork:
    forall x y k t,
    x <> y ->
    ~ Graph.In (Edge k) y ->
    MapsTo t x k ->
    ForkTree (x, y) (tick t, child t) (F x y :: k).
  Proof.
    intros.
    auto using fork_tree_eq, maps_to_fork_parent, maps_to_fork_child.
  Qed.

  Lemma spawn_irrefl:
    forall x,
    ~ Spawn x x.
  Proof.
    unfold not; intros.
    destruct x.
    inversion H.
  Qed.

  Lemma spawn_inv_tick_child:
    forall x y,
    Spawn (tick x) (child y) ->
    x = y.
  Proof.
    intros.
    destruct x, y.
    unfold child, tick in *.
    inversion H; subst.
    auto.
  Qed.

  Lemma spawn_absurd_tick_tick:
    forall x y,
    ~ Spawn (tick x) (tick y).
  Proof.
    intros; destruct x, y.
    simpl.
    unfold not; intros.
    inversion H.
  Qed.

  Lemma maps_to_inv_root:
    forall k x,
    ~ MapsTo root x k.
  Proof.
    induction k; unfold not; intros. {
      inversion H.
    }
    inversion H; subst; clear H.
    - destruct t.
      simpl in *.
      inversion H0.
    - destruct t.
      simpl in *.
      inversion H0.
    - apply IHk in H5.
      contradiction.
    - apply IHk in H3; contradiction.
  Qed.

  Lemma tick_absurd_0:
    forall x,
    tick x <> x.
  Proof.
    intros.
    destruct x.
    unfold not; intros.
    simpl in *.
    inversion H.
    omega.
  Qed.

  Ltac simpl_tree :=
  repeat match goal with
  | [ H : ParentOf ?x ?x |- _ ] =>
    apply parent_of_irrefl in H; contradiction
  | [ H : Spawn ?x ?x |- _ ] =>
    apply spawn_irrefl in H; contradiction
  | [ H: Spawn (child ?x) (tick ?x) |- _ ] =>
    inversion H
  | [ H: Spawn (tick ?x) (child ?x) |- _ ] =>
    clear H
  | [ H: ParentOf _ (tick root) |- _ ] =>
    apply parent_of_absurd_tick_root in H; contradiction
  | [ H: Spawn (tick _) (tick _) |- _ ] =>
    apply spawn_absurd_tick_tick in H; contradiction
  | [ H: Spawn (tick ?x) (child ?y) |- _ ] =>
    apply spawn_inv_tick_child in H; rewrite H in *; clear H
  | [ H: Spawn _ (tick root) |- _ ] =>
    apply spawn_absurd_tick_root in H; contradiction
  | [ H: MapsTo root _ _ |- _ ] =>
    apply maps_to_inv_root in H; contradiction
  | [ H: MapsTo _ _ nil |- _ ] =>
    inversion H
  | [ H: MapsTo ?t ?x ?k, H2: MapsTo ?s ?x ?k |- _ ] =>
    assert (t = s) by eauto using maps_to_fun; subst; clear H2
  end.

  Lemma parent_of_to_fork_tree:
    forall k x y s t,
    Trace k ->
    MapsTo t x k ->
    MapsTo s y k ->
    Spawn t s ->
    ForkTree (x, y) (t, s) k.
  Proof.
    induction k; intros; simpl_tree.
    inversion H; subst; clear H. {
      inversion H0; subst; clear H0.
      + apply maps_to_inv_5 in H1; auto.
        destruct H1 as [(?,?)|(?,?)]; subst; simpl_tree.
        auto using fork_tree_eq_fork.
      + apply maps_to_inv_5 in H1; auto.
        destruct H1 as [(?,?)|(?,?)]; subst; simpl_tree.
      + inversion H1; subst; clear H1; simpl_tree. {
          auto using fork_tree_eq_fork.
        }
        apply fork_tree_cons.
        inversion H11; subst; clear H11; simpl_tree.
        - inversion H8; subst; clear H8; simpl_tree. {
            
          }
        - destruct t0; simpl in *.
          unfold root, child in *.
          simpl in *.
          inversion H2; subst.
        inversion H2; subst; clear H2.
        destruct t0; simpl in *.
        inversion H0; subst; clear H0.
        inversion H11; subst; clear H11.
        - destruct t.
          simpl in *.
          inversion H; subst; clear H.
        - destruct t.
          simpl in *.
          subst.
          apply 
        destruct x, t0; simpl in *; subst; simpl in *; simpl_tree.
        apply fork_tree_cons.
        apply IHk; auto using spawn_def.
        unfold tick.
        simpl.
    }
    inversion H0; subst.
    - inversion H0.
    - inversion H0; subst; clear H0.
      + apply maps_to_inv_5 in H1; auto.
        destruct H1 as [(?,?)|(?,?)]; subst; simpl_tree; auto.
      + apply maps_to_inv_5 in H1; auto.
        destruct H1 as [(?,?)|(?,?)]; subst; simpl_tree.
      + inversion H1; subst; clear H1; simpl_tree.
        * auto using fork_tree_eq_fork.
        * apply fork_tree_cons.
  Qed.

  Inductive JoinTree : tree_id -> tree_id -> list op -> Prop :=
  | join_tree_eq:
    forall x y t1 t2 k,
    MapsTo t1 x k ->
    MapsTo t2 y k ->
    JoinTree t1 t2 (J x y::k)
  | join_tree_cons:
    forall t1 t2 k e,
    JoinTree t1 t2 k ->
    JoinTree t1 t2 (e :: k).

  Lemma fork_spec_1 k es (Hs: Safe k es):
    forall x y t s,
    MapsTo t x k ->
    MapsTo s y k ->
    ForkTree t s k ->
    List.In (F x y) k.
  Proof.
    induction k; intros. {
      inversion H; subst; clear H.
    }
    destruct a as ([], a,b). {
      destruct (tid_eq_dec x a). {
        subst.
        destruct (tid_eq_dec y b). {
          subst.
          auto using in_eq.
        }
        inversion Hs; subst; clear Hs.
        inversion H4; subst; clear H4.
      }
    }
  Qed.

  Inductive ForkEdge x y k : Prop :=
  | fork_edge_def:
    forall t s,
    ForkTree t s k ->
    TreeId t x k ->
    TreeId s y k ->
    ForkEdge x y k.

  Lemma fork_spec_1:
    forall k x y,
    ForkEdge x y k ->
    List.In (F x y) k.
  Proof.
    induction k; intros. {
      inversion H; subst; clear H.
      inversion H1; inversion H.
    }
    inversion H; subst; clear H. {
      inversion H0; subst; clear H0. {
        
      }
    }
  Qed.

End AsCG.
