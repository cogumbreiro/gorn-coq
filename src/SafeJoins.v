Require Import Coq.Lists.List.

Require Import Aniceto.List.
Require Import Aniceto.Graphs.Graph.
Require Import Aniceto.Graphs.FGraph.

Require Import CG.
Require Import Tid.

Import Trace.
Require Import Aniceto.Graphs.FGraph.

Section Defs.
  Notation known := (list (tid*tid)).

  Definition safe_join_of t (e:tid*tid) := let (x,y) := e in if TID.eq_dec x t then Some y else None.

  Definition get_safe_joins x := List.omap (safe_join_of x).

  Definition copy_from (x y:tid) k := map (fun z => (y, z)) (get_safe_joins x k).

  Definition fork (x y:tid) (k:known) : known :=
  copy_from x y k ++ (x,y) :: k.

  Definition join (x y:tid) (k:known) : known :=
  copy_from y x k ++ k.

  Definition eval (o:op) :=
  let f := match op_t o with
  | FORK => fork
  | JOIN => join 
  end
  in
  f (op_src o) (op_dst o).

  Inductive Check (k:known) : op -> Prop :=
  | check_fork:
    forall (x y:tid),
    x <> y ->
    ~ Graph.In (Edge k) y ->
    Check k {| op_t := FORK; op_src:= x; op_dst:= y|}
  | check_join:
    forall x y,
    Edge k (x,y) ->
    Check k {| op_t := JOIN; op_src := x; op_dst:= y|}.

  Inductive Safe : trace -> known -> Prop :=
  | safe_nil:
    Safe nil nil
  | safe_cons:
    forall o l k,
    Check k o ->
    Safe l k ->
    Safe (o::l) (eval o k).

  Import Aniceto.Graphs.DAG.

  Let copy_from_eq:
    forall x y z k,
    copy_from x y ((x,z) :: k) = (y,z) :: copy_from x y k.
  Proof.
    intros.
    unfold copy_from.
    simpl.
    destruct (TID.eq_dec x x). {
      auto.
    }
    contradiction n.
    apply TID.eq_refl.
  Qed.

  Let copy_from_neq:
    forall x y a b k,
    a <> x ->
    copy_from x y ((a,b) :: k) = copy_from x y k.
  Proof.
    intros.
    unfold copy_from.
    simpl.
    destruct (TID.eq_dec a x). {
      contradiction H.
    }
    auto.
  Qed.

  Let copy_from_spec_1:
    forall k x y z, List.In (x,z) k -> List.In (y,z) (copy_from x y k).
  Proof.
    induction k as [|(a,b)]; intros. {
      inversion H.
    }
    destruct (TID.eq_dec a x); rewrite tid_eq_rw in *. {
      subst.
      rewrite copy_from_eq.
      destruct H. {
        inversion H; subst.
        auto using in_eq.
      }
      apply in_cons.
      auto using in_cons.
    }
    rewrite copy_from_neq; auto.
    destruct H. {
      inversion H.
      contradiction.
    }
    auto.
  Qed.

  Let copy_from_spec_2:
    forall k x y z, List.In (y,z) (copy_from x y k) -> List.In (x,z) k.
  Proof.
    induction k as [|(a,b)]; intros. {
      inversion H.
    }
    destruct (TID.eq_dec a x); rewrite tid_eq_rw in *. {
      subst.
      rewrite copy_from_eq in *.
      destruct H. {
        inversion H; subst.
        auto using in_eq.
      }
      eauto using in_cons.
    }
    rewrite copy_from_neq in *; auto.
    eauto using in_cons.
  Qed.

  Let copy_from_inv_eq:
    forall a b x y k,
    List.In (a, b) (copy_from x y k) ->
    a = y.
  Proof.
    induction k as [|(v1,v2)]; intros. {
      inversion H.
    }
    destruct (TID.eq_dec v1 x); rewrite tid_eq_rw in *. {
      subst.
      rewrite copy_from_eq in *.
      destruct H. {
        inversion H; subst.
        trivial.
      }
      auto.
    }
    rewrite copy_from_neq in *; auto.
  Qed.

  Let reaches_edge_absurd_nil:
    forall {A:Type} (x:A),
    ~ Reaches (Edge nil) x x.
  Proof.
    intros.
    unfold not; intros.
    inversion H.
    inversion H0.
    destruct H1 as (?,(?,(?,?))).
    subst.
    inversion H3.
    inversion H6.
  Qed.

  Require Import Aniceto.Pair.

  Let dag_fork_aux_0:
    forall l k x y,
    DAG (Edge k) ->
    x <> y ->
    ~ Graph.In (Edge k) y ->
    incl l k ->
    DAG (Edge (copy_from x y l ++ (x,y)::k)).
  Proof.
    induction l; intros. {
      simpl in *.
      apply f_dag_cons; auto using TID.eq_dec.
      unfold not; intros X.
      contradiction H1; eauto using reaches_to_in_fst.
    }
    assert (DAG (Edge (copy_from x y l ++ (x,y) ::k))) by
          eauto using List.incl_strengthten; clear IHl.
    destruct a as (a,b).
    destruct (TID.eq_dec a x); rewrite tid_eq_rw in *.
    - subst.
      rewrite copy_from_eq. 
      simpl.
      assert (y <> b). {
        unfold not; intros; subst.
        assert (List.In (x,b) k) by (unfold incl in *; auto using in_eq).
        assert (Edge k (x,b)) by (unfold Edge; auto).
        contradiction H1.
        eauto using in_right.
      }
      apply f_dag_cons; auto using TID.eq_dec.
      remember (_ ++ _ :: k) as es.
      unfold not; intros.
      (* for b to reach y in ES, then it must pass through (x,y) *)
      inversion H5 as (w,Hw2).
      assert (w =  (x,y) :: nil). {
        inversion Hw2; subst.
        inversion H7 as ((v,?),(?,?)); simpl in *; subst.
        rename H9 into E.
        remember (_ ++ _) as es.
        assert (v = x). {
          assert (Hi := E).
          apply end_to_edge with (Edge:=Edge es) in Hi; auto.
          subst.
          unfold Edge in Hi.
          rewrite in_app_iff in Hi.
          destruct Hi.
          - assert (v = y) by eauto; subst.
            apply copy_from_spec_2 in H9.
            assert (List.In (x,y) k); (apply List.incl_strengthten in H2; auto).
            contradiction H1.
            assert (Edge k (x,y)) by (unfold Edge;auto).
            eauto using in_right.
          - destruct H9 as [X|X]. {
              inversion X; subst; auto.
            }
            contradiction H1.
            assert (Edge k (v,y)) by (unfold Edge;auto).
            eauto using in_right.
        }
        subst.
        assert (List.In (x,y) w) by auto using end_in.
        apply end_to_append in E.
        destruct E as (w', ?); subst.
        destruct w'. {
          auto.
        }
        apply walk2_split_app in Hw2.
        destruct Hw2.
        remember (_ ++ (_ :: k)) as es.
        assert (Reaches (Edge es) b x) by eauto using reaches_def.
        assert (Reaches (Edge es) x b). {
          assert (Edge es (x,b)). {
            unfold Edge, incl in *.
            subst.
            rewrite in_app_iff.
            eauto using in_eq, in_cons.
          }
          auto using edge_to_reaches.
        }
        assert (n: Reaches (Edge es) b b) by eauto using reaches_trans.
        apply H3 in n.
        contradiction.
      } (* w =  (x,y) :: nil *)
      subst.
      assert (b = x). {
        inversion Hw2; subst.
        apply starts_with_eq in H6.
        auto.
      }
      subst.
      remember (_ ++ (_ :: k)) as es.
      assert (n: Reaches (Edge es) x x). {
        assert (Edge es (x,x)). {
          unfold Edge.
          subst.
          rewrite in_app_iff.
          eauto using in_eq, in_cons.
        }
        auto using edge_to_reaches.
      }
      apply H3 in n; contradiction.
    - rewrite copy_from_neq; auto.
  Qed.

  Let dag_fork:
    forall k x y,
    DAG (Edge k) ->
    x <> y ->
    ~ Graph.In (Edge k) y ->
    DAG (Edge (fork x y k)).
  Proof.
    unfold fork.
    intros.
    apply dag_fork_aux_0; auto using incl_refl.
  Qed.

  Let dag_join_aux_0:
    forall l k x y,
    DAG (Edge k) ->
    x <> y ->
    Edge k (x,y) ->
    incl l k ->
    DAG (Edge (copy_from y x l ++ k)).
  Proof.
    induction l; intros. { auto. }
    assert (DAG (Edge (copy_from y x l ++ k))) by
          eauto using List.incl_strengthten; clear IHl.
    destruct a as (a,b).
    destruct (TID.eq_dec a y); rewrite tid_eq_rw in *.
    - subst.
      rewrite copy_from_eq. 
      simpl.
      assert (x <> b). {
        unfold not; intros; subst.
        assert (List.In (y,b) k) by (unfold incl in *; auto using in_eq).
        assert (Edge k (y,b)) by (unfold Edge; auto).
        assert (Reaches (Edge k) y b) by auto using edge_to_reaches.
        assert (Reaches (Edge k) b y) by auto using edge_to_reaches.
        assert (n: Reaches (Edge k) y y) by eauto using reaches_trans.
        apply H in n; contradiction.
      }
      apply f_dag_cons_reaches; auto using TID.eq_dec.
        remember ( _ ++ _ ) as es.
        assert (Reaches (Edge es) y b). {
          assert (Edge es (y,b)). {
            unfold Edge, incl in *.
            subst.
            rewrite in_app_iff.
            eauto using in_eq, in_cons.
          }
          auto using edge_to_reaches.
        }
        assert (Reaches (Edge es) x y). {
          assert (Edge es (x,y)). {
            unfold Edge, incl in *.
            subst.
            rewrite in_app_iff.
            eauto using in_eq, in_cons.
          }
          auto using edge_to_reaches.
        }
        eauto using reaches_trans.
    - rewrite copy_from_neq; auto.
  Qed.

  Let dag_join:
    forall k x y,
    DAG (Edge k) ->
    Edge k (x,y) ->
    DAG (Edge (join x y k)).
  Proof.
    intros.
    unfold join.
    assert (x <> y). {
      unfold not; intros; subst.
      assert (n: Reaches (Edge k) y y) by auto using edge_to_reaches.
      apply H in n.
      contradiction.
    }
    apply dag_join_aux_0; auto using incl_refl.
  Qed.

  Lemma eval_preserves_dag:
    forall k o,
    Check k o ->
    DAG (Edge k) ->
    DAG (Edge (eval o k)).
  Proof.
    intros.
    destruct o; auto.
    inversion H; subst; simpl; eauto.
  Qed.

  (**
    If the safe-joins graph that yields a trace is well-formed, then
    the safe-joins graph is a DAG.
    *)

  Theorem safe_to_dag:
    forall t k,
    Safe t k ->
    DAG (Edge k).
  Proof.
    intros.
    induction H. {
      auto using f_dag_nil.
    }
    auto using eval_preserves_dag.
  Qed.

  Notation R_Edge rs k := (Edge (restriction tid_eq_dec rs k)).

  Notation R_DAG rs k := (DAG (R_Edge rs k)).

  Import WellFormed.

  Let running_infimum:
    forall rs k,
    restriction tid_eq_dec rs k <> nil ->
    R_DAG rs k ->
    exists x, Graph.In (R_Edge rs k) x /\
      forall y, ~ Reaches (R_Edge rs k) x y.
  Proof.
    intros.
    apply dag_infimum; auto using TID.eq_dec.
  Qed.


  Let safe_to_r_dag:
    forall t k rs,
    Safe t k ->
    R_DAG rs k.
  Proof.
    intros.
    apply safe_to_dag in H.
    apply f_dag_incl with (es:=k); auto using restriction_incl.
  Qed.

  Let progress_0:
    forall t k rs,
    Safe t k ->
    (restriction tid_eq_dec rs k) <> nil ->
    exists x, List.In x rs /\ forall y, Edge k (x,y) -> ~ List.In y rs.
  Proof.
    intros.
    assert (Hx:
      exists x, Graph.In (R_Edge rs k) x /\
      forall y, ~ Reaches (R_Edge rs k) x y). {
        eapply running_infimum; eauto.
    }
    destruct Hx as (x, (Hin, Hy)).
    exists x.
    split; eauto using restriction_in_1.
    unfold not;
    intros y He Hx.
    assert (Hz := Hy y); clear Hy.
    contradiction Hz; clear Hz.
    assert (List.In x rs). {
      eauto using restriction_in_1.
    }
    assert (R_Edge rs k (x,y)). {
      unfold Edge.
      auto using restriction_in_2.
    }
    auto using edge_to_reaches.
  Qed.

  Theorem progress:
    forall t k rs,
    Safe t k ->
    rs <> nil ->
    exists x, List.In x rs /\ forall y, Edge k (x,y) -> ~ List.In y rs.
  Proof.
    intros.
    remember (restriction tid_eq_dec rs k) as l.
    destruct l. {
      subst.
      destruct rs. { contradiction H0; auto. }
      exists t0.
      assert (List.In t0 (t0::rs)) by auto using in_eq.
      split. { auto. }
      intros.
      unfold not; intros.
      assert (List.In (t0, y) (restriction tid_eq_dec (t0::rs) k)) by auto using restriction_in_2.
      rewrite <- Heql in *.
      inversion H4.
    }
    assert (restriction tid_eq_dec rs k <> nil). {
      intuition.
      rewrite H1 in *.
      inversion Heql.
    }
    eauto.
  Qed.
(*
  Let sj_hb:
    forall t x y z a k cg,
    Safe t k ->
    CG a t cg ->
    List.In (Node.node_task x, Node.node_task z) k ->
    HB_Edge cg (x, y) ->
    List.In (Node.node_task y, Node.node_task z) k.
  Proof.
    intros.
  Qed.

  Let sj_hb_fork:
    forall w a b x y z r k cg t,
    a <> b ->
    ~ Graph.In (Edge k) b ->
    Safe (Some {| op_t := FORK; op_src := a; op_dst := b |} :: t) k ->
    List.In (Node.node_task x, Node.node_task z) k ->
    CG r (Some {| op_t := FORK; op_src := a; op_dst := b |} :: t) cg ->
    Walk2 (HB_Edge cg) x y w ->
    List.In (Node.node_task y, Node.node_task z) k.
  Proof.
    induction w; intros. {
      apply walk2_nil_inv in H4; contradiction.
    }
    destruct a as (v1,v2).
    assert (v1 = x) by eauto using walk2_inv_eq_fst; subst.
    assert (HB_Edge cg (x,v2)). {
      eapply walk2_to_edge; eauto using in_eq.
    }
    remember (Node.node_task y) as t_y.
    remember (Node.node_task z) as t_z.
    remember (Node.node_task x) as t_x.
    unfold fork.
    rewrite in_app_iff.
    destruct (tid_eq_dec t_y a), (tid_eq_dec t_z b); subst.
    - rewrite e; rewrite e0 in *.
      eauto using in_eq.
    - rewrite e in *.
      right.
      apply in_cons.
      inversion H3; subst.
  Qed.


  Let sj_hb:
    forall t x y z a k cg,
    Safe t k ->
    CG a t cg ->
    List.In (Node.node_task x, Node.node_task z) k ->
    HB cg x y ->
    List.In (Node.node_task y, Node.node_task z) k.
  Proof.
    induction t; intros; simpl in *. {
      inversion H0; subst; simpl in *.
      apply hb_make_cg_absurd in H2; contradiction.
    }
    inversion H; subst.
    inversion H0; subst.
    inversion H5; subst; simpl in *.
    - rename x0 into a; rename y0 into b.
      rename cg0 into cg.
      rename k0 into k.
      clear H5.
      assert (List.In (Node.node_task y, Node.node_task z) (fork a b k)). {
        eapply IHt; eauto.
      }
subst.
    destruct a0 as [(ot,os,od)|?].
    - destruct ot; simpl in *.
      + remember (Node.node_task x) as tx.
        remember (Node.node_task y) as ty.
        remember (Node.node_task z) as tz.
      destruct (tid_eq_dec os x), (tid_eq_dec od z)
  Qed.
*)
End Defs.

Module Lang.

  Fixpoint from_trace ts := 
  match ts with
  | nil => nil
  | o :: ts => eval o (from_trace ts)
  end.

  Definition effects_to_sj ts := from_trace (CG.Lang.from_effects ts).

  Definition Safe ts := Safe (CG.Lang.from_effects ts) (effects_to_sj ts).
End Lang.
