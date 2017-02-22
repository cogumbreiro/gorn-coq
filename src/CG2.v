Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Aniceto.Graphs.Graph.

Require Import Tid.
Require Import Mid.
Require Import Node.

Require Trace.

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

  Definition is_leaf (x: A) l := is_in x l && negb (c_edge_out x l).

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

  Inductive CG: computation_graph -> Prop :=
  | cg_nil:
    CG []
  | cg_init:
    forall x l,
    CG l ->
    ~ In x l ->
    CG ((Expr.init x)::l)
  | cg_fork:
    forall x y z l,
    CG l ->
    Running y l ->
    ~ In x l ->
    ~ In z l ->
    CG ((Expr.fork x y z)::l)
  | cg_join:
    forall x y z l,
    CG l ->
    Running x l ->
    Leaf z l ->
    ~ In y l ->
    CG ((Expr.join x y z)::l)
  | cg_seq:
    forall x y l,
    CG l ->
    Running x l ->
    ~ In y l ->
    CG ((Expr.seq x y)::l).

  Lemma cg_inv_cons:
    forall e l,
    CG (e :: l) ->
    CG l.
  Proof.
    intros.
    inversion H; subst; clear H; auto.
  Qed.

  Definition cg_dec l:
    { CG l } + { ~ CG l }.
  Proof.
    induction l. {
      auto using cg_nil.
    }
    destruct IHl. {
      destruct a.
      - destruct (in_dec a l). {
          right; unfold not; intros N; inversion N; subst; contradiction.
        }
        auto using cg_init.
      - destruct (running_dec a0 l). {
          destruct (in_dec a l). {
            right; unfold not; intros N; inversion N; subst; contradiction.
          }
          destruct (in_dec a1 l). {
            right; unfold not; intros N; inversion N; subst; contradiction.
          }
          auto using cg_fork.
        }
        right; unfold not; intros N; inversion N; subst; contradiction.
      - destruct (running_dec a l). {
          destruct (in_dec a0 l). {
            right; unfold not; intros N; inversion N; subst; contradiction.
          }
          destruct (leaf_dec a1 l). {
            auto using cg_join.
          }
          right; unfold not; intros N; inversion N; subst; contradiction.
        }
        right; unfold not; intros N; inversion N; subst; contradiction.
      - destruct (running_dec a l). {
          destruct (in_dec a0 l). {
            right; unfold not; intros N; inversion N; subst; contradiction.
          }
          auto using cg_seq.
        }
        right; unfold not; intros N; inversion N; subst; contradiction.
    }
    right; unfold not; intros N.
    inversion N; subst; try contradiction.
  Defined.

  Definition is_cg l :=
  if cg_dec l then true else false.

  Lemma is_cg_true:
    forall l,
    is_cg l = true ->
    CG l.
  Proof.
    unfold is_cg; intros.
    destruct (cg_dec l); auto.
    inversion H.
  Qed.
End Defs.

Module Examples.

  Goal CG [
    Expr.join 6 7 5;
    Expr.join 2 6 4;
    Expr.fork 5 3 4;
    Expr.fork 3 1 2;
    Expr.init 1
  ].
  Proof.
    assert (is_cg Peano_dec.eq_nat_dec [
      Expr.join 6 7 5;
      Expr.join 2 6 4;
      Expr.fork 5 3 4;
      Expr.fork 3 1 2;
      Expr.init 1
   ] = true). {
      compute.
      trivial.
    }
    apply is_cg_true in H.
    auto.
  Qed.

  Goal CG [
    Expr.seq 8 11;   (* (h, rd(a, g)) *)
    Expr.seq 5 10;   (* (g, rd(b, h)) *)
    Expr.seq 7 9;    (* (f, wr(b, h)) *)
    Expr.fork 8 6 7; (* (f, async h) *)
    Expr.seq 4 6;    (* (f, wr(a, g)) *)
    Expr.fork 5 3 4; (* (f, async g) *)
    Expr.seq 2 3;    (* (f, new y) *)
    Expr.seq 1 2;    (* (f, new x) *)
    Expr.init 1      (* (f, init) *)
  ].
  Proof.
    assert (is_cg Peano_dec.eq_nat_dec [
    Expr.seq 8 11;   (* (h, rd(a, g)) *)
    Expr.seq 5 10;   (* (g, rd(b, h)) *)
    Expr.seq 7 9;    (* (f, wr(b, h)) *)
    Expr.fork 8 6 7; (* (f, async h) *)
    Expr.seq 4 6;    (* (f, wr(a, g)) *)
    Expr.fork 5 3 4; (* (f, async g) *)
    Expr.seq 2 3;    (* (f, new y) *)
    Expr.seq 1 2;    (* (f, new x) *)
    Expr.init 1      (* (f, init) *)
   ] = true). {
      compute.
      trivial.
    }
    apply is_cg_true in H.
    auto.
  Qed.
End Examples.

Section Props.
  Import Trace.

  Definition action := (tid * op) % type.

  Definition trace := list action.

  Definition actions := MN.t action.

  Inductive TaskOf n x (a:actions) : Prop :=
  | task_of_def:
    forall o,
    MN.MapsTo n (x, o) a ->
    TaskOf n x a.

  Inductive Trace: trace -> computation_graph node -> actions -> Prop :=
  | trace_nil:
    Trace [] [] (MN.empty action)
  | trace_init:
    forall x n cg a t,
    Trace t cg a ->
    Trace ((x, INIT)::t) (Expr.init n :: cg) (MN.add n (x,INIT) a)
  | trace_mem:
    forall t cg x n n' m r a,
    Trace t cg a ->
    TaskOf n x a ->
    Trace ((x, MEM r m)::t) (Expr.seq n n' :: cg) (MN.add n (x, MEM r m) a)
  | cg_future:
    forall x y t cg nx nx' ny a,
    Trace t cg a ->
    TaskOf nx x a ->
    Trace ((x, FUTURE y)::t) (Expr.fork ny nx nx'::cg)
      (MN.add ny (y, INIT) (MN.add nx' (x, FUTURE y) a))
  | trace_join:
    forall nx ny nx' t cg a x y,
    Trace t cg a ->
    TaskOf nx x a ->
    TaskOf ny y a ->
    Trace ((x, FUTURE y)::t) (Expr.join nx nx' ny::cg)
      (MN.add nx' (x, FORCE y) a).

  Definition known_sets := MN.t (list tid).

  Section KnownSet.
    Variable a: actions.

    Inductive KnownSet: computation_graph node -> known_sets -> Prop :=
    | known_set_nil:
      KnownSet [] (MN.empty (list tid))
    | known_set_init:
      forall cg ks n,
      KnownSet cg ks ->
      KnownSet (Expr.init n :: cg) (MN.add n nil ks)
    | known_set_mem:
      forall cg ks n n',
      KnownSet cg ks ->
      KnownSet (Expr.seq n n' :: cg) ks
    | known_set_fork:
      forall cg ks y l nx ny nx',
      KnownSet cg ks ->
      TaskOf ny y a ->
      MN.MapsTo nx l ks ->
      KnownSet (Expr.fork ny nx nx' :: cg) (MN.add ny l (MN.add nx' (y::l) ks))
    | known_set_join:
      forall cg ks lx ly nx ny nx',
      KnownSet cg ks ->
      MN.MapsTo nx lx ks ->
      MN.MapsTo ny ly ks ->
      KnownSet (Expr.fork nx nx' ny :: cg) (MN.add nx' (ly ++ lx) ks).
  End KnownSet.
End Props.