Set Implicit Arguments.

Require Import Coq.Lists.List.

Require Import Aniceto.List.
Require Import Aniceto.Graphs.Graph.
Require Import Aniceto.Graphs.FGraph.

Require Import Tid.

Require Import Aniceto.Graphs.FGraph.

  Inductive op_type := FORK | JOIN.

  Structure op := {
    op_t: op_type;
    op_src: tid;
    op_dst: tid
  }.

Module SJ_Notations.
  Notation F x y := ({| op_t := FORK; op_src:=x; op_dst := y |}).
  Notation J x y := ({| op_t := JOIN; op_src:=x; op_dst := y |}).
End SJ_Notations.

Section Defs.

  Definition trace := list op.

  Notation known := (list (tid*tid)).

  Definition outgoing_of t (e:tid*tid) := let (x,y) := e in if tid_eq_dec x t then Some y else None.

  Definition filter_outgoing x := List.omap (outgoing_of x).

  Definition copy_from (x y:tid) k := map (fun z => (y, z)) (filter_outgoing x k).

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

  Let fork_incl:
    forall x y k,
    incl k (fork x y k).
  Proof.
    intros.
    unfold fork.
    auto using incl_refl, incl_appr, incl_tl.
  Qed.

  Lemma in_fork:
    forall e x y k,
    List.In e k ->
    List.In e (fork x y k).
  Proof.
    intros.
    assert (X:incl k (fork x y k)) by eauto using fork_incl.
    unfold incl in *; auto.
  Qed.

  Let join_incl:
    forall x y k,
    incl k (join x y k).
  Proof.
    intros.
    unfold join.
    auto using incl_refl, incl_appr.
  Qed.

  Lemma in_join:
    forall e x y k,
    List.In e k ->
    List.In e (join x y k).
  Proof.
    intros.
    assert (incl k (join x y k)) by eauto using join_incl.
    unfold incl in *; auto.
  Qed.

  Lemma eval_incl:
    forall k o,
    incl k (eval o k).
  Proof.
    intros.
    unfold eval.
    destruct (op_t o); auto using join_incl, fork_incl.
  Qed.

  Lemma in_eval:
    forall e k o,
    List.In e k ->
    List.In e (eval o k).
  Proof.
    intros.
    assert (Hi: incl k (eval o k)) by auto using eval_incl.
    auto.
  Qed.

  Inductive CanCheckOp (k:known) : op -> Prop :=
  | can_check_fork:
    forall (x y:tid),
    x <> y ->
    ~ Graph.In (Edge k) y ->
    CanCheckOp k {| op_t := FORK; op_src:= x; op_dst:= y|}
  | can_check_join:
    forall x y,
    Edge k (x,y) ->
    CanCheckOp k {| op_t := JOIN; op_src := x; op_dst:= y|}.

  Lemma can_check_op_dec k o:
    { CanCheckOp k o } + { ~ CanCheckOp k o }.
  Proof.
    destruct o as (t, x, y).
    destruct t.
    - destruct (in_edge_dec tid_eq_dec y k). {
        right.
        unfold not; intros Hx.
        inversion Hx; subst; simpl in *; clear Hx.
        contradiction.
      }
      destruct (tid_eq_dec x y). {
        right.
        unfold not; intros Hx.
        inversion Hx; subst; simpl in *; clear Hx.
        contradiction H1; trivial.
      }
      auto using can_check_fork.
    - destruct (is_edge_dec tid_eq_dec k (x,y)). {
        left; auto using can_check_join.
      }
      right.
      unfold not; intros.
      inversion H; subst.
      contradiction.
  Defined.

  Inductive CheckOp k : op -> known -> Prop :=
  | check_fork:
    forall (x y:tid),
    x <> y ->
    ~ Graph.In (Edge k) y ->
    CheckOp k {| op_t := FORK; op_src:= x; op_dst:= y|} (fork x y k)
  | check_join:
    forall x y,
    Edge k (x,y) ->
    CheckOp k {| op_t := JOIN; op_src := x; op_dst:= y|} (join x y k).

  Inductive Safe : trace -> known -> Prop :=
  | safe_nil:
    Safe nil nil
  | safe_cons:
    forall o l k,
    CanCheckOp k o ->
    Safe l k ->
    Safe (o::l) (eval o k).

  Fixpoint is_safe t :=
  match t with
  | nil => Some nil
  | o :: t =>
    match is_safe t with
    | Some k =>
      if can_check_op_dec k o
      then Some (eval o k)
      else None
    | _ => None
    end
  end.

  Lemma can_check_op_to_check_op:
    forall o k,
    CanCheckOp k o ->
    CheckOp k o (eval o k).
  Proof.
    intros.
    inversion H; subst; clear H; subst; unfold eval; simpl in *;
    auto using check_fork, check_join.
  Qed.

  Lemma check_op_to_can_check_op:
    forall o k,
    CheckOp k o (eval o k) ->
    CanCheckOp k o.
  Proof.
    intros.
    inversion H; subst; clear H; subst; unfold eval; simpl in *;
    auto using can_check_fork, can_check_join.
  Qed.

  Lemma is_safe_some:
    forall t k,
    is_safe t = Some k ->
    Safe t k.
  Proof.
    induction t; intros; simpl in *.
    - inversion H; subst; auto using safe_nil.
    - remember (is_safe t).
      symmetry in Heqo.
      destruct o. {
        destruct (can_check_op_dec l a). {
          inversion H; subst.
          auto using safe_cons.
        }
        inversion H.
      }
      inversion H.
  Qed.

  Lemma safe_to_is_safe:
    forall t k,
    Safe t k ->
    is_safe t = Some k.
  Proof.
    induction t; intros. {
      inversion H.
      subst.
      auto.
    }
    inversion H;subst;clear H.
    apply IHt in H4.
    simpl.
    rewrite H4.
    destruct (can_check_op_dec k0 a). {
      trivial.
    }
    contradiction.
  Qed.

  Lemma safe_fun:
    forall t k k',
    Safe t k ->
    Safe t k' ->
    k' = k.
  Proof.
    intros.
    apply safe_to_is_safe in H.
    apply safe_to_is_safe in H0.
    rewrite H in H0.
    inversion H0; trivial.
  Qed.

  Lemma is_safe_none:
    forall t k,
    is_safe t = None ->
    ~ Safe t k.
  Proof.
    intros.
    unfold not; intros.
    apply safe_to_is_safe in H0.
    rewrite H in H0.
    inversion H0.
  Qed.

  Lemma safe_reduces:
    forall o t k k',
    Safe t k ->
    CheckOp k o k' ->
    Safe (o::t) k'.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    - assert (R: fork x y k = eval {| op_t := FORK; op_src := x; op_dst := y |} k) by auto.
      rewrite R.
      eauto using can_check_fork, safe_cons.
    - assert (R: join x y k = eval {| op_t := JOIN; op_src := x; op_dst := y |} k) by auto.
      rewrite R.
      eauto using can_check_join, safe_cons.
  Qed.

  Lemma safe_inv:
    forall o t k,
    Safe (o::t) k ->
    exists k', Safe t k' /\ CheckOp k' o k.
  Proof.
    intros.
    inversion H; subst; clear H.
    unfold eval.
    inversion H2; subst; simpl in *; clear H2;
    eauto using check_fork, check_join.
  Qed.

  Require Import Aniceto.Graphs.DAG.

  Let copy_from_eq:
    forall x y z k,
    copy_from x y ((x,z) :: k) = (y,z) :: copy_from x y k.
  Proof.
    intros.
    unfold copy_from.
    simpl.
    destruct (tid_eq_dec x x). {
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
    destruct (tid_eq_dec a x). {
      contradiction H.
    }
    auto.
  Qed.

  Let outgoing_of_some:
    forall x y,
    outgoing_of x (x, y) = Some y.
  Proof.
    intros.
    unfold outgoing_of.
    destruct (tid_eq_dec x x).
    - auto.
    - contradiction n; auto.
  Qed.

  Let outgoing_of_some_rw:
    forall x e y,
    outgoing_of x e = Some y ->
    e = (x, y).
  Proof.
    unfold outgoing_of.
    intros.
    destruct e.
    destruct (tid_eq_dec t x); inversion H.
    subst; auto.
  Qed.

  Let in_filter_outgoing:
    forall x y k,
    List.In (x, y) k ->
    List.In y (filter_outgoing x k).
  Proof.
    intros.
    unfold filter_outgoing.
    eauto using in_omap_1, outgoing_of_some.
  Qed.

  Let in_copy_from_1:
    forall x y z k,
    List.In (x, z) k ->
    List.In (y, z) (copy_from x y k).
  Proof.
    intros.
    unfold copy_from.
    rewrite in_map_iff.
    eauto using in_filter_outgoing.
  Qed.

  Let in_copy_from_2:
    forall x y z k,
    List.In (y, z) (copy_from x y k) ->
    List.In (x, z) k.
  Proof.
    intros.
    unfold copy_from, filter_outgoing in *.
    rewrite in_map_iff in H.
    destruct H as (x', (?,Hi)).
    inversion H; subst.
    apply in_omap_2 in Hi.
    destruct Hi as (e,(Hi,R)).
    apply outgoing_of_some_rw in R; subst.
    assumption.
  Qed.

  Let copy_from_inv_in:
    forall x y a b k,
    List.In (x, y) (copy_from a b k) ->
    x = b /\ List.In (a, y) k.
  Proof.
    intros.
    destruct (tid_eq_dec x b). {
      split; auto.
      subst.
      eauto using in_copy_from_2.
    }
    unfold copy_from, filter_outgoing in *.
    rewrite in_map_iff in H.
    destruct H as (?, (He, ?)).
    inversion He; subst.
    contradiction n; trivial.
  Qed.

  Lemma in_fork_1:
    forall x y z k,
    x <> y ->
    ~ Graph.In (Edge k) y ->
    List.In (y, z) (fork x y k) ->
    List.In (x, z) k.
  Proof.
    intros.
    unfold fork in *.
    rewrite in_app_iff in H1.
    destruct H1.
    - eauto using in_copy_from_2.
    - destruct H1.
      + inversion H1; subst.
        contradiction H; auto.
      + contradiction H0.
        eauto using in_left, edge_spec.
  Qed.

  Lemma in_fork_2:
    forall x y k z,
    List.In (x,z) k ->
    List.In (y,z) (fork x y k).
  Proof.
    intros.
    unfold fork.
    rewrite in_app_iff.
    eauto using in_copy_from_2.
  Qed.

  Lemma in_fork_3:
    forall k x y z,
    y <> z ->
    List.In (x, z) (fork x y k) ->
    List.In (y, z) (fork x y k).
  Proof.
    intros.
    unfold fork in *.
    rewrite in_app_iff in *.
    destruct H0.
    - apply copy_from_inv_in in H0.
      destruct H0; subst.
      eauto using in_copy_from_2.
    - destruct H0.
      + inversion H0; subst.
        contradiction H; trivial.
      + eauto using in_copy_from_2.
  Qed.

  Lemma fork_inv_in:
    forall x y a b k,
    List.In (x, y) (fork a b k) ->
    (x = b /\ List.In (a, y) k) \/ (a = x /\ b = y) \/ List.In (x, y) k.
  Proof.
    intros.
    unfold fork in *.
    rewrite in_app_iff in *.
    destruct H.
    - apply copy_from_inv_in in H.
      intuition.
    - destruct H.
      + inversion H.
        intuition.
      + auto.
  Qed.

  Lemma join_inv_in:
    forall x y a b k,
    List.In (x, y) (join a b k) ->
    (x = a /\ List.In (b, y) k) \/ List.In (x, y) k.
  Proof.
    intros.
    unfold join in *.
    rewrite in_app_iff in *.
    destruct H.
    - apply copy_from_inv_in in H.
      intuition.
    - auto.
  Qed.

  Lemma in_fork_4:
    forall x y z k,
    ~ Graph.In (FGraph.Edge k) y ->
    List.In (z, y) (fork x y k) ->
    z = x.
  Proof.
    intros.
    apply fork_inv_in in H0.
    destruct H0 as [(?,?)|[(?,?)|?]].
    - subst.
      contradiction H.
      eauto using in_right.
    - subst.
      trivial.
    - contradiction H.
      eauto using in_right.
  Qed.

  Lemma in_fork_5:
    forall x y k,
    List.In (x, y) (fork x y k).
  Proof.
    intros.
    unfold fork.
    rewrite in_app_iff.
    right.
    auto using in_eq.
  Qed.

  Lemma in_join_2:
    forall x y k z,
    List.In (y,z) k ->
    List.In (x,z) (join x y k).
  Proof.
    intros.
    unfold join.
    rewrite in_app_iff.
    eauto using in_copy_from_2.
  Qed.

  Let copy_from_inv_eq:
    forall a b x y k,
    List.In (a, b) (copy_from x y k) ->
    a = y.
  Proof.
    induction k as [|(v1,v2)]; intros. {
      inversion H.
    }
    destruct (tid_eq_dec v1 x). {
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
            apply in_copy_from_2 in H9.
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
    CanCheckOp k o ->
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

(*  Import WellFormed.*)

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

  Require Import Aniceto.Graphs.FGraph.

  Corollary deadlock_avoidance:
    forall t k wfg,
    Safe t k ->
    (forall e, Edge wfg e -> Edge k e) ->
    DAG (Edge wfg).
  Proof.
    intros.
    assert (DAG (Edge k)) by eauto using safe_to_dag.
    apply dag_impl with (E:=Edge k); auto.
  Qed.

End Defs.

Section Trace.
  Import SJ_Notations.

  Inductive Edge : trace -> (tid*tid) ->  Prop :=
  | edge_fork_eq:
    forall x y k,
    Edge (F x y:: k) (x,y)
  | edge_fork_trans:
    forall x y z k,
    Edge k (x, z) ->
    Edge (F x y::k) (y, z)
  | edge_join:
    forall x y z k,
    Edge k (y, z) ->
    Edge (J x y::k) (x, z)
  | edge_cons:
    forall k e e',
    Edge k e ->
    Edge (e'::k) e.

  Inductive Trace: trace -> Prop :=
  | trace_nil:
    Trace nil
  | trace_fork:
    forall x y l,
    x <> y ->
    ~ Graph.In (Edge l) y  ->
    Trace l ->
    Trace (F x y:: l)
  | trace_join:
    forall x y l,
    Trace l ->
    Edge l (x, y) ->
    Trace (J x y :: l).

  Lemma edge_to_f_edge:
    forall l e k,
    Safe l k ->
    Edge l e ->
    FGraph.Edge k e.
  Proof.
    induction l; intros;
    unfold FGraph.Edge. {
      inversion H0.
    }
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    - unfold eval; simpl.
      auto using in_fork_5.
    - eapply IHl in H4; eauto.
      inversion H3; subst; clear H3.
      unfold eval; simpl.
      auto using in_fork_2.
    - unfold eval; simpl.
      eapply IHl in H4; eauto.
      eauto using in_join_2.
    - apply in_eval.
      apply IHl with (k:=k0) in H4; auto.
  Qed.

  Lemma f_edge_to_edge:
    forall l e k,
    Safe l k ->
    FGraph.Edge k e ->
    Edge l e.
  Proof.
    induction l; intros;
    unfold FGraph.Edge in *. {
      inversion H; subst.
      inversion H0.
    }
    inversion H; subst; clear H.
    destruct e as (x, y).
    destruct a as ([], a, b); unfold eval in *; simpl in *.
    - apply fork_inv_in in H0.
      destruct H0 as [(?,?)|[(?,?)|?]]; subst;
      eauto using edge_fork_trans, edge_fork_eq, edge_cons.
    - apply join_inv_in in H0.
      destruct H0 as [(?,?)|?]. {
        subst.
        eauto using edge_join.
      }
      eauto using edge_cons.
  Qed.

  Lemma trace_to_safe:
    forall l,
    Trace l ->
    exists k, Safe l k.
  Proof.
    intros.
    induction H.
    - eauto using safe_nil.
    - destruct IHTrace as (k, Hs).
      exists (eval (F x y) k).
      apply safe_cons; auto.
      apply can_check_fork; auto.
      unfold not; intros.
      destruct H2 as (e, (He, Hi)).
      contradiction H0.
      unfold In.
      eauto using f_edge_to_edge.
    - destruct IHTrace as (k, Hs).
      exists (eval (J x y) k).
      apply safe_cons; auto.
      apply can_check_join; auto.
      eauto using edge_to_f_edge.
  Qed.

  Lemma safe_to_trace:
    forall l k,
    Safe l k ->
    Trace l.
  Proof.
    intros.
    induction H. {
      auto using trace_nil.
    }
    destruct o as ([], a, b). {
      inversion H; subst; clear H.
      apply trace_fork; auto.
      unfold not; intros N.
      contradiction H4.
      destruct N as (e, (Hi, He)).
      unfold In.
      apply edge_to_f_edge with (k:=k) in Hi; eauto.
    }
    inversion H; subst.
    eauto using f_edge_to_edge, trace_join.
  Qed.

End Trace.

Section Examples.

  Let check_fork_nil:
    forall x y,
    x <> y ->
    CheckOp nil {| op_t := FORK; op_src := x; op_dst := y |} ((x, y) :: nil).
  Proof.
    intros.
    apply check_fork; auto.
    intuition.
    inversion H0.
    destruct H1 as (N, _).
    inversion N.
  Qed.

  Let x := taskid 0.
  Let y := taskid 1.
  Let z := taskid 2.
  Let e1 := {|op_t:=FORK;op_src:=x;op_dst:=y|}.
  Let e2 := {|op_t:=FORK;op_src:=y;op_dst:=z|}.
  Goal exists k, Safe (e2::e1::nil) k.
  Proof.
  assert (Safe (e1::nil) ((x,y)::nil)). {
    assert (R: (x,y)::nil= eval e1 nil) by eauto.
    rewrite R.
    assert (x<>y). {
      unfold not; intros.
      subst.
      inversion H.
    }
    apply safe_cons; eauto using check_fork_nil, safe_nil.
    apply check_op_to_can_check_op.
    unfold eval; simpl.
    apply check_fork_nil; auto.
  }
  exists (fork y z ((x,y)::nil)).
  assert (R: fork y z ((x, y) :: nil) = eval e2 ((x,y)::nil)) by auto.
  rewrite R.
  apply safe_cons; auto.
  apply can_check_fork.
  - unfold not; intros; subst.
    inversion H0.
  - unfold not; intros.
    destruct H0 as (e, (Hi,He)).
    destruct Hi.
    + subst.
      destruct He; simpl in *; inversion H0.
    + inversion H0.
  Qed.

  Goal is_safe (e2::e1::nil) = Some ((y,z)::(x, y) :: nil).
  Proof.
  compute; auto.
  Qed.
End Examples.

Extraction "ocaml/sj.ml" is_safe.
