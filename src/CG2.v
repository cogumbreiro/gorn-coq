Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Aniceto.Graphs.Graph.

Require Import Tid.
Require Import Mid.
Require Import Node.

Import ListNotations.

Set Implicit Arguments.

Module Expr.
Section Defs.
  Variable A:Type.

  Inductive t :=
  | init: A -> t
  | fork : A -> A -> A -> t
  | join : A -> A -> A -> t
  | seq: A -> A -> t.

  Inductive In: A -> t -> Prop :=
  | in_init:
    forall x,
    In x (init x)
  | in_fork:
    forall w x y z,
    (w = x \/ w = y \/ w = z) ->
    In w (fork x y z)
  | in_join:
    forall x y z w,
    (w = x \/ w = y \/ w = z) ->
    In w (join x y z)
  | in_seq:
    forall x y z,
    (z = x \/ z = y) ->
    In z (seq x y).

  Inductive CEdge: t -> (A * A) -> Prop :=
  | c_edge_fork:
    forall x y z,
    CEdge (fork x y z) (y, z)
  | c_edge_join:
    forall x y z,
    CEdge (join x y z) (x, y)
  | c_edge_seq:
    forall x y,
    CEdge (seq x y) (x, y).

  Definition c_edge (e:t) :=
  match e with
  | fork x y z => Some (y, z)
  | join x y z => Some (x, y)
  | seq x y => Some (x, y)
  | _ => None
  end.

  Lemma some_to_c_edge:
    forall p e,
    (c_edge e) = Some p ->
    CEdge e p.
  Proof.
    intros; destruct e; simpl in *; try inversion H;
    destruct H; try contradiction; subst;
    auto using c_edge_fork, c_edge_join, c_edge_seq.
  Qed.

  Lemma c_edge_to_some:
    forall e p,
    CEdge e p ->
    c_edge e = Some p.
  Proof.
    intros.
    inversion H; subst; simpl; auto.
  Qed.

  Lemma c_edge_fun:
    forall e p p',
    CEdge e p ->
    CEdge e p' ->
    p' = p.
  Proof.
    intros.
    destruct e; inversion H; subst; inversion H0; subst; auto.
  Qed.

  Inductive JEdge: t -> (A * A) -> Prop :=
  | j_edge_def:
    forall x y z,
    JEdge (join x y z) (z, y).

  Lemma j_edge_fun:
    forall e p p',
    JEdge e p ->
    JEdge e p' ->
    p' = p.
  Proof.
    intros.
    destruct e; inversion H; subst; inversion H0; subst; auto.
  Qed.

  Definition j_edge (e:t) :=
  match e with
  | join x y z => Some (z, y)
  | _ => None
  end.

  Lemma some_to_j_edge:
    forall p e,
    j_edge e = Some p ->
    JEdge e p.
  Proof.
    intros; destruct e; simpl in *; try inversion H; subst.
    auto using j_edge_def.
  Qed.

  Lemma j_edge_to_some:
    forall e p,
    JEdge e p ->
    j_edge e = Some p.
  Proof.
    intros.
    inversion H; subst; simpl; auto.
  Qed.

  Inductive FEdge: t -> (A * A) -> Prop :=
  | f_edge_def:
    forall x y z,
    FEdge (fork x y z) (x, y).

  Definition Edge e p := CEdge e p \/ FEdge e p \/ JEdge e p.

  Section Dec.
    Variable a_eq_dec: forall (x y:A), { x = y } + { x <> y }.

    Ltac handle_not :=
    let H := fresh "H" in
    right; unfold not; intros; inversion H; subst; contradiction.

    Definition eq_dec (x y:t):
      { x = y } + { x <> y }.
    Proof.
      destruct x.
      - destruct y; try handle_not.
        destruct (a_eq_dec a a0); subst; auto.
        right; unfold not; intros.
        inversion H; subst; clear H.
        contradiction.
      - destruct y; try handle_not.
        destruct (a_eq_dec a a2); try handle_not.
        subst.
        destruct (a_eq_dec a0 a3); try handle_not; subst.
        destruct (a_eq_dec a4 a1); try handle_not; subst.
        auto.
      - destruct y; try handle_not.
        destruct (a_eq_dec a2 a); try handle_not; subst.
        destruct (a_eq_dec a0 a3); try handle_not; subst.
        destruct (a_eq_dec a1 a4); try handle_not; subst.
        auto.
      - destruct y; try handle_not.
        destruct (a_eq_dec a1 a); try handle_not; subst.
        destruct (a_eq_dec a0 a2); try handle_not; subst.
        auto.
    Defined.

    Let eq_fst x (p:A*A) :=
    let (a,b) := p in if a_eq_dec a x then true else false.

    Let eq_fst_true:
      forall x y z,
      eq_fst x (y, z) = true ->
      y = x.
    Proof.
      unfold eq_fst; intros.
      destruct (a_eq_dec y x); auto.
      inversion H.
    Qed.

    Let eq_fst_false:
      forall x y z,
      eq_fst x (y, z) = false ->
      y <> x.
    Proof.
      unfold eq_fst; intros.
      destruct (a_eq_dec y x); auto.
      inversion H.
    Qed.

    Definition c_edge_out e x : bool :=
    match c_edge e with
    | Some (a, _) => if a_eq_dec x a then true else false
    | _ => false
    end.

    Lemma c_edge_out_true:
      forall e x,
      c_edge_out e x = true ->
      exists y, CEdge e (x, y).
    Proof.
      unfold c_edge_out; intros.
      remember (c_edge e); symmetry in Heqo.
      destruct o. {
        destruct p.
        destruct (a_eq_dec x a). {
          subst.
          eauto using some_to_c_edge.
        }
        inversion H.
      }
      inversion H.
    Qed.

    Lemma c_edge_out_false:
      forall e x,
      c_edge_out e x = false ->
      forall y, ~ CEdge e (x, y).
    Proof.
      unfold c_edge_out; intros.
      remember (c_edge e); symmetry in Heqo.
      destruct o. {
        destruct p.
        unfold not; intros N.
        apply c_edge_to_some in N.
        rewrite N in *.
        inversion Heqo; subst.
        destruct (a_eq_dec a a). {
          inversion H.
        }
        contradiction.
      }
      unfold not; intros N.
      apply c_edge_to_some in N.
      rewrite N in *.
      inversion Heqo.
    Qed.

    Definition c_edge_out_dec t x:
      { forall y, ~ CEdge t (x, y) } + { exists y, CEdge t (x, y) }.
    Proof.
      remember (c_edge_out t x); symmetry in Heqb; destruct b. {
        auto using c_edge_out_true.
      }
      auto using c_edge_out_false.
    Defined.

    Definition j_edge_out e x : bool :=
    match j_edge e with
    | Some (a, _) => if a_eq_dec x a then true else false
    | _ => false
    end.

    Lemma j_edge_out_true:
      forall e x,
      j_edge_out e x = true ->
      exists y, JEdge e (x, y).
    Proof.
      unfold j_edge_out; intros.
      remember (j_edge e); symmetry in Heqo.
      destruct o. {
        destruct p.
        destruct (a_eq_dec x a). {
          subst.
          eauto using some_to_j_edge.
        }
        inversion H.
      }
      inversion H.
    Qed.

    Lemma j_edge_out_false:
      forall e x,
      j_edge_out e x = false ->
      forall y, ~ JEdge e (x, y).
    Proof.
      unfold j_edge_out; intros.
      remember (j_edge e); symmetry in Heqo.
      destruct o. {
        destruct p.
        unfold not; intros N.
        apply j_edge_to_some in N.
        rewrite N in *.
        inversion Heqo; subst.
        destruct (a_eq_dec a a). {
          inversion H.
        }
        contradiction.
      }
      unfold not; intros N.
      apply j_edge_to_some in N.
      rewrite N in *.
      inversion Heqo.
    Qed.

    Definition j_edge_out_dec t x:
      { forall y, ~ JEdge t (x, y) } + { exists y, JEdge t (x, y) }.
    Proof.
      remember (j_edge_out t x); symmetry in Heqb; destruct b. {
        auto using j_edge_out_true.
      }
      auto using j_edge_out_false.
    Defined.

    Definition in_dec x e:
      { In x e } + { ~ In x e }.
    Proof.
      destruct e.
      - destruct (a_eq_dec x a); try handle_not; subst; auto using in_init.
      - destruct (a_eq_dec x a); subst; auto using in_fork.
        destruct (a_eq_dec x a0); subst; auto using in_fork.
        destruct (a_eq_dec x a1); subst; auto using in_fork.
        right; unfold not; intros.
        inversion H; subst.
        destruct H2 as [?|[?|?]]; subst; try contradiction.
      - destruct (a_eq_dec x a); subst; auto using in_join.
        destruct (a_eq_dec x a0); subst; auto using in_join.
        destruct (a_eq_dec x a1); subst; auto using in_join.
        right; unfold not; intros.
        inversion H; subst.
        destruct H2 as [?|[?|?]]; subst; try contradiction.
      - destruct (a_eq_dec x a); subst; auto using in_seq.
        destruct (a_eq_dec x a0); subst; auto using in_seq.
        right; unfold not; intros.
        inversion H; subst.
        destruct H2 as [?|?]; subst; try contradiction.
    Defined.
  End Dec.
End Defs.
End Expr.

Section Defs.
  Variable A:Type.

  Definition computation_graph := (list (Expr.t A)).

  Definition Edge (cg:computation_graph) p :=
  Exists (fun e => Expr.Edge e p) cg.

  Definition CEdge (l:computation_graph) p :=
  Exists (fun e => Expr.CEdge e p) l.

  Definition JEdge (l:computation_graph) p :=
  Exists (fun e => Expr.JEdge e p) l.

  Definition HB l := Reaches (Edge l).
  Definition CONTINUE l := Reaches (Edge l).

  Definition In x : computation_graph -> Prop := Exists (fun e=>Expr.In x e).

  Inductive Leaf (x:A) l :=
  | leaf_def:
    (forall y, ~ CEdge l (x, y)) ->
    In x l ->
    Leaf x l.

  Variable a_eq_dec: forall (x y:A), { x = y } + { x <> y }.

  Definition is_in x l :=
  existsb (fun e => if Expr.in_dec a_eq_dec x e then true else false) l.

  Lemma is_in_true:
    forall x l,
    is_in x l = true ->
    In x l.
  Proof.
    unfold is_in; intros.
    apply existsb_exists in H.
    destruct H as (e, (Hi, Hx)).
    destruct (Expr.in_dec a_eq_dec x e). {
      apply Exists_exists.
      eauto.
    }
    inversion Hx.
  Qed.

  Lemma is_in_false:
    forall x l,
    is_in x l = false ->
    ~ In x l.
  Proof.
    unfold is_in, not; intros.
    apply List.existsb_Forall in H.
    rewrite Forall_forall in H.
    unfold In in *.
    rewrite Exists_exists in *.
    destruct H0 as (e, (Hi, Hii)).
    apply H in Hi.
    destruct (Expr.in_dec a_eq_dec x e). {
      inversion Hi.
    }
    contradiction.
  Qed.

  Definition in_dec x l:
    { In x l } + { ~ In x l }.
  Proof.
    remember (is_in x l).
    symmetry in Heqb.
    destruct b. {
      auto using is_in_true.
    }
    auto using is_in_false.
  Defined.

  Definition c_edge_out x l :=
  existsb (fun e => Expr.c_edge_out a_eq_dec e x) l.

  Lemma c_edge_out_true:
    forall x l,
    c_edge_out x l = true ->
    exists y, CEdge l (x, y).
  Proof.
    unfold c_edge_out; intros.
    apply existsb_exists in H.
    destruct H as (e, (Hi, Hii)).
    apply Expr.c_edge_out_true in Hii.
    unfold CEdge.
    destruct Hii as (y, He).
    exists y.
    apply Exists_exists.
    eauto.
  Qed.

  Lemma c_edge_out_false:
    forall x l,
    c_edge_out x l = false ->
    forall y, ~ CEdge l (x, y).
  Proof.
    unfold c_edge_out, not; intros.
    apply List.existsb_Forall in H.
    rewrite Forall_forall in H.
    unfold CEdge in *.
    rewrite Exists_exists in H0.
    destruct H0 as (e, (Hi, Hii)).
    apply H in Hi.
    eapply Expr.c_edge_out_false in Hi.
    eauto.
  Qed.

  Definition c_edge_out_dec l x:
    { forall y, ~ CEdge l (x, y) } + { exists y, CEdge l (x, y) }.
  Proof.
    remember (c_edge_out x l).
    symmetry in Heqb; destruct b. {
      auto using c_edge_out_true.
    }
    auto using c_edge_out_false.
  Defined.

  Let is_leaf (x: A) l := is_in x l && negb (c_edge_out x l).

  Lemma is_leaf_true:
    forall x l,
    is_leaf x l = true ->
    Leaf x l.
  Proof.
    unfold is_leaf; intros.
    rewrite andb_true_iff in *.
    destruct H.
    rewrite negb_true_iff in *.
    apply is_in_true in H.
    apply leaf_def; eauto using c_edge_out_false.
  Qed.

  Lemma is_leaf_false:
    forall x l,
    is_leaf x l = false ->
    ~ Leaf x l.
  Proof.
    unfold is_leaf, not; intros.
    rewrite andb_false_iff in *.
    inversion H0; subst; clear H0.
    destruct H. {
      apply is_in_false in H.
      contradiction.
    }
    rewrite negb_false_iff in *.
    apply c_edge_out_true in H.
    destruct H.
    apply H1 in H.
    contradiction.
  Qed.

  Definition leaf_dec x l :
    { Leaf x l } + { ~ Leaf x l }.
  Proof.
    remember (is_leaf x l); symmetry in Heqb; destruct b. {
      auto using is_leaf_true.
    }
    auto using is_leaf_false.
  Defined.

  Definition j_edge_out x l :=
  existsb (fun e => Expr.j_edge_out a_eq_dec e x) l.

  Definition j_edge_out_dec l x:
    { forall y, ~ JEdge l (x, y) } + { exists y, JEdge l (x, y) }.
  Proof.
    remember (j_edge_out x l).
    symmetry in Heqb; destruct b; unfold j_edge_out in *. {
      apply existsb_exists in Heqb.
      right.
      destruct Heqb as (e, (Hi, Hii)).
      apply Expr.j_edge_out_true in Hii.
      unfold JEdge.
      destruct Hii as (y, He).
      exists y.
      apply Exists_exists.
      eauto.
    }
    left.
    unfold not; intros.
    apply List.existsb_Forall in Heqb.
    rewrite Forall_forall in Heqb.
    unfold JEdge in *.
    rewrite Exists_exists in H.
    destruct H as (e, (Hi, Hii)).
    apply Heqb in Hi.
    eapply Expr.j_edge_out_false in Hi.
    eauto.
  Defined.

  Inductive Running (x:A) l :=
  | running_def:
    (forall y, ~ JEdge l (x, y)) ->
    Leaf x l ->
    Running x l.

  Definition is_running x l: bool :=
  negb (j_edge_out x l) && is_leaf x l.

  Definition running_dec x l:
    { Running x l } + { ~ Running x l }.
  Proof.
    destruct (leaf_dec x l). {
      destruct (j_edge_out_dec l x). {
        auto using running_def.
      }
      right; unfold not; intros;
      inversion H.
      destruct e as (?, He).
      apply H0 in He; contradiction.
    }
    right; unfold not; intros;
    inversion H.
    contradiction.
  Defined.

  Inductive WF: computation_graph -> Prop :=
  | wf_nil:
    WF []
  | wf_init:
    forall x l,
    WF l ->
    ~ In x l ->
    WF ((Expr.init x)::l)
  | wf_fork:
    forall x y z l,
    WF l ->
    Running y l ->
    ~ In x l ->
    ~ In z l ->
    WF ((Expr.fork x y z)::l)
  | wf_join:
    forall x y z l,
    WF l ->
    Running x l ->
    Leaf z l ->
    ~ In y l ->
    WF ((Expr.join x y z)::l)
  | wf_seq:
    forall x y l,
    WF l ->
    Running x l ->
    ~ In y l ->
    WF ((Expr.seq x y)::l).

  Lemma wf_inv_cons:
    forall e l,
    WF (e :: l) ->
    WF l.
  Proof.
    intros.
    inversion H; subst; clear H; auto.
  Qed.

  Definition wf_dec l:
    { WF l } + { ~ WF l }.
  Proof.
    induction l. {
      auto using wf_nil.
    }
    destruct IHl. {
      destruct a.
      - destruct (in_dec a l). {
          right; unfold not; intros N; inversion N; subst; contradiction.
        }
        auto using wf_init.
      - destruct (running_dec a0 l). {
          destruct (in_dec a l). {
            right; unfold not; intros N; inversion N; subst; contradiction.
          }
          destruct (in_dec a1 l). {
            right; unfold not; intros N; inversion N; subst; contradiction.
          }
          auto using wf_fork.
        }
        right; unfold not; intros N; inversion N; subst; contradiction.
      - destruct (running_dec a l). {
          destruct (in_dec a0 l). {
            right; unfold not; intros N; inversion N; subst; contradiction.
          }
          destruct (leaf_dec a1 l). {
            auto using wf_join.
          }
          right; unfold not; intros N; inversion N; subst; contradiction.
        }
        right; unfold not; intros N; inversion N; subst; contradiction.
      - destruct (running_dec a l). {
          destruct (in_dec a0 l). {
            right; unfold not; intros N; inversion N; subst; contradiction.
          }
          auto using wf_seq.
        }
        right; unfold not; intros N; inversion N; subst; contradiction.
    }
    right; unfold not; intros N.
    inversion N; subst; try contradiction.
  Defined.

  Definition is_wf l :=
  if wf_dec l then true else false.

  Lemma is_wf_true:
    forall l,
    is_wf l = true ->
    WF l.
  Proof.
    unfold is_wf; intros.
    destruct (wf_dec l); auto.
    inversion H.
  Qed.
End Defs.

Module Examples.
  (*Import Expr.*)
(*
  Lemma top_in_6:
    Top.In 6 [join 2 6 4; fork 5 4 5; fork 3 1 2; init 1].
  Proof.
    unfold Top.In.
    auto using Exists_cons_hd, in_join.
  Qed.

  Lemma top_in_5:
    Top.In 5 [join 2 6 4; fork 5 4 5; fork 3 1 2; init 1].
  Proof.
    unfold Top.In.
    apply Exists_cons_tl.
    auto using Exists_cons_hd, Exists_cons_tl, in_join.
  Qed.

  Lemma leaf_6:
    Leaf 6 [join 2 6 4; fork 5 4 5; fork 3 1 2; init 1].
  Proof.
    apply leaf_def. {
      unfold Supremum, not; intros.
      inversion H; clear H.
      inversion H0; subst; clear H0.
      apply walk_to_forall in H2.
      rewrite Forall_forall in H2.
      destruct w. {
        apply starts_with_inv_nil in H.
        assumption.
      }
      destruct p as (a,b).
      apply starts_with_eq in H.
      subst.
      assert (Hi: List.In (6,b) ((6,b)::w)) by auto using in_eq.
      apply H2 in Hi.
      apply Exists_exists in Hi.
      destruct Hi as (?, (Hi, He)).
      inversion Hi; subst; clear Hi. {
        destruct He as [X|X]; inversion X.
      }
      inversion H; subst; clear H. {
        destruct He as [X|X]; inversion X.
      }
      inversion H0; subst; clear H0. {
        destruct He as [X|X]; inversion X.
      }
      inversion H; subst; clear H. {
        destruct He as [X|X]; inversion X.
      }
      inversion H0.
    }
    auto using top_in_6.
  Qed.

  Lemma leaf_5:
    Leaf 5 [join 2 6 4; fork 5 4 5; fork 3 1 2; init 1].
  Proof.
    apply leaf_def. {
      unfold Supremum, not; intros.
      inversion H; clear H.
      inversion H0; subst; clear H0.
      apply walk_to_forall in H2.
      rewrite Forall_forall in H2.
      destruct w. {
        apply starts_with_inv_nil in H.
        assumption.
      }
      destruct p as (a,b).
      apply starts_with_eq in H.
      subst.
      assert (Hi: List.In (5,b) ((5,b)::w)) by auto using in_eq.
      apply H2 in Hi.
      apply Exists_exists in Hi.
      destruct Hi as (?, (Hi, He)).
      inversion Hi; subst; clear Hi. {
        destruct He as [X|X]; inversion X.
      }
      inversion H; subst; clear H. {
        destruct He as [X|X]; inversion X.
      }
      inversion H0; subst; clear H0. {
        destruct He as [X|X]; inversion X.
      }
      inversion H; subst; clear H. {
        destruct He as [X|X]; inversion X.
      }
      inversion H0.
    }
    auto using top_in_5.
  Qed.

*)

  Let wf_0:
   WF [
    Expr.init 1
  ].
  Proof.
    assert (is_wf Peano_dec.eq_nat_dec [Expr.init 1] = true). {
      compute.
      trivial.
    }
    apply is_wf_true in H.
    assumption.
  Qed.

  Let wf_1:
   WF [
    Expr.fork 3 1 2;
    Expr.init 1
  ].
  Proof.
    assert (is_wf Peano_dec.eq_nat_dec [
      Expr.fork 3 1 2;
      Expr.init 1
   ] = true). {
      compute.
      trivial.
    }
    apply is_wf_true in H.
    auto.
  Qed.

  Goal WF [
    Expr.fork 6 3 4;
    Expr.fork 3 1 2;
    Expr.init 1
  ].
  Proof.
    assert (is_wf Peano_dec.eq_nat_dec [
      Expr.fork 6 3 4;
      Expr.fork 3 1 2;
      Expr.init 1
   ] = true). {
      compute.
      trivial.
    }
    apply is_wf_true in H.
    auto.
  Qed.

  Goal WF [
    Expr.join 6 7 5;
    Expr.join 2 6 4;
    Expr.fork 6 3 4;
    Expr.fork 3 1 2;
    Expr.init 1
  ].
  Proof.
    assert (is_wf Peano_dec.eq_nat_dec [
      Expr.join 2 6 4;
      Expr.fork 6 3 4;
      Expr.fork 3 1 2;
      Expr.init 1
   ] = true). {
      compute.
      trivial.
    }
    apply is_wf_true in H.
    auto.
  Qed.

End Examples.

Section Props.
  Inductive datum :=
  | d_task : tid -> datum
  | d_mem : mid -> datum
  | d_any : datum.

  Inductive mem_op :=
  | ALLOC: mem_op
  | READ: datum -> mem_op
  | WRITE: datum -> mem_op.

  Inductive op :=
  | INIT: op
  | MEM: mid -> mem_op -> op
  | FUTURE: tid -> op
  | FORCE: tid -> op.

  Definition action := (tid * op) % type.

  Definition trace := list action.

  Definition computation_graph := lang node.

  Inductive CG: trace -> computation_graph -> Prop :=
  | cg_nil:
    forall x,
    CG [(x, INIT)] (init (@fresh action []))
  | cg_mem:
    forall t cg x o n m r,
    CG t cg ->
    MapsTo (x, o) n t ->
    CG ((x, MEM r m)::t) (seq n (fresh t) cg)
  | cg_future:
    forall x y t cg n o,
    CG t cg ->
    MapsTo (x, o) n t ->
    CG ((y, INIT)::(x, FUTURE y)::t) (fork (fresh ((x, FUTURE y)::t)) n (fresh t) cg)
  | cg_join:
    forall 
  
End Props.