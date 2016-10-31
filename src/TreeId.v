Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.

Import ListNotations.

Definition tree_id := (nat * list nat) % type.

Definition root : tree_id := (0, []).

Definition tick (p:tree_id) := (S (fst p), snd p).

Definition child (p:tree_id) : tree_id :=
    (0, (fst p) :: (snd p)).

  Inductive Observes : list nat -> list nat -> Prop :=
  | observes_def:
    forall x y l,
    x > y ->
    Observes (x::l) (y::l). 

  Inductive ParentOf : tree_id -> tree_id -> Prop :=
  | parent_of_def:
    forall x l m y,
    Observes (x::l) m ->
    ParentOf (x, l) (y, m).

Definition parent_of (l:list nat) (r:list nat) :=
match r with
| _ :: r => if (list_eq_dec PeanoNat.Nat.eq_dec l r) then true else false
| _ => false
end.

Goal parent_of [0;0] [1;0;0]  = true.
  compute.
  auto.
Qed.

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

Goal contains [3;1;0] [0;0]  = true.
  compute; auto.
Qed.

Goal contains [3;1;0] [2;0]  = false.
  compute;auto.
Qed.

Goal contains [3;3;0] [2;0]  = true.
  compute;auto.
Qed.

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
(*
  Lemma maps_to_inv:
    forall k t x e,
    Trace (e :: k) ->
    MapsTo t x (e :: k) ->
    (k = nil /\ exists y, (e = F x y /\ t = tick root) \/ (e = F y x /\ t = child root))
    \/
    (k <> nil /\(
      (exists y s, (
           (e = F x y /\ t = tick s /\ MapsTo s x k)
        \/ (e = F y x /\ t = child s /\ MapsTo s y k)
        )
      )
      \/ MapsTo t x k
    )).
  Proof.
    induction k; intros. {
      inversion H0; subst; clear H0;
      try inversion H4; try (left; eauto; fail).
      inversion H6.
    }
    right; split; auto with *.
    inversion H; subst. {
      inversion H0; subst; clear H0.
      - left.
        exists y.
        exists t0.
        auto.
      - left.
        exists x0.
        exists t0.
        auto.
      - auto.
    }
    inversion H0; subst; auto.
  Qed.
*)
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
    inversion H0; subst; clear H0.
    apply observes_length in H1.
    apply observes_length in H2.
    simpl in *.
    rewrite <- H1 in *.
    intuition.
  Qed.

  Lemma parent_of_irrefl:
    forall x,
    ~ ParentOf x x.
  Proof.
    intros.
    unfold not; intros.
    inversion H; subst.
    inversion H2.
    apply absurd_cons in H1.
    contradiction.
  Qed.

  Lemma parent_of_tick_snd:
    forall x y,
    ParentOf x y ->
    ParentOf x (tick y).
  Proof.
    intros.
    inversion H; subst.
    apply parent_of_def; auto.
  Qed.

  Lemma parent_of_absurd_root:
    forall x,
    ~ ParentOf x root.
  Proof.
    intros.
    unfold not; intros.
    inversion H; subst.
    inversion H2; subst.
  Qed.

  Lemma parent_of_absurd_tick_root:
    forall x,
    ~ ParentOf x (tick root).
  Proof.
    intros.
    unfold not; intros.
    inversion H; subst.
    inversion H2.
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
    inversion H2; subst.
    destruct x0. {
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
    inversion H; subst; clear H.
    destruct y; simpl in *.
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

  Ltac simpl_tree :=
  repeat match goal with
  | [ H : ParentOf ?x ?x |- _ ] =>
    apply parent_of_irrefl in H; contradiction
  | [ H: ParentOf _ (tick root) |- _ ] =>
    apply parent_of_absurd_tick_root in H; contradiction
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
    ParentOf t s ->
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
