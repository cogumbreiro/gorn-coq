Require Import Coq.Lists.List.

Require Import Aniceto.List.
Require Import Aniceto.Graphs.Graph.
Require Import Aniceto.Graphs.FGraph.

Require Import Tid.

Require Import Aniceto.Graphs.FGraph.

Section Defs.

  Inductive op_type := FORK | JOIN.

  Structure op := {
    op_t: op_type;
    op_src: tid;
    op_dst: tid
  }.

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

  Lemma eval_inl:
    forall k o,
    incl k (eval o k).
  Proof.
    intros.
    unfold eval.
    destruct (op_t o); auto using join_incl, fork_incl.
  Qed.

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

  Inductive Reduces k : op -> known -> Prop :=
  | reduces_fork:
    forall (x y:tid),
    x <> y ->
    ~ Graph.In (Edge k) y ->
    Reduces k {| op_t := FORK; op_src:= x; op_dst:= y|} (fork x y k)
  | reduces_join:
    forall x y,
    Edge k (x,y) ->
    Reduces k {| op_t := JOIN; op_src := x; op_dst:= y|} (join x y k).

  Inductive Safe : trace -> known -> Prop :=
  | safe_nil:
    Safe nil nil
  | safe_cons:
    forall o l k,
    Check k o ->
    Safe l k ->
    Safe (o::l) (eval o k).


  Lemma safe_reduces:
    forall o t k k',
    Safe t k ->
    Reduces k o k' ->
    Safe (o::t) k'.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    - assert (R: fork x y k = eval {| op_t := FORK; op_src := x; op_dst := y |} k) by auto.
      rewrite R.
      eauto using check_fork, safe_cons.
    - assert (R: join x y k = eval {| op_t := JOIN; op_src := x; op_dst := y |} k) by auto.
      rewrite R.
      eauto using check_join, safe_cons.
  Qed.

  Lemma safe_inv:
    forall o t k,
    Safe (o::t) k ->
    exists k', Safe t k' /\ Reduces k' o k.
  Proof.
    intros.
    inversion H; subst; clear H.
    unfold eval.
    inversion H2; subst; simpl in *; clear H2;
    eauto using reduces_fork, reduces_join.
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

End Defs.

Section Examples.

  Lemma reduces_fork_nil:
    forall x y,
    x <> y ->
    Reduces nil {| op_t := FORK; op_src := x; op_dst := y |} ((x, y) :: nil).
  Proof.
    intros.
    apply reduces_fork; auto.
    intuition.
    inversion H0.
    destruct H1 as (N, _).
    inversion N.
  Qed.
End Examples.