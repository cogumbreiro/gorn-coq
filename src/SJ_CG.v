Require Import Coq.Lists.List.
Require Import Aniceto.Graphs.Graph.
Require Import Aniceto.Graphs.FGraph.

Require Import CG.
Require Import SafeJoins.
Require Import Tid.

Require Import Coq.Structures.OrderedTypeEx.
Module MN := FMapAVL.Make Nat_as_OT.
Module MN_Facts := FMapFacts.Facts MN.
Module MN_Props := FMapFacts.Properties MN.
Require Import Aniceto.Map.
Module MN_Extra := MapUtil MN.

Module Events.

  (** Reduces the known-set interpreting events of type [CG.event]. *)

Section Defs.
  Notation known_set := (list (tid * tid)).

  Inductive Reduces: known_set -> CG.event -> known_set -> Prop :=
  | reduces_fork:
    forall k k' x y,
    SafeJoins.Reduces k {| op_t := FORK; op_src := x; op_dst := y |} k' ->
    Reduces k (x, CG.FORK y) k'
  | reduces_join:
    forall k k' x y,
    SafeJoins.Reduces k {| op_t := JOIN; op_src := x; op_dst := y |} k' ->
    Reduces k (x, CG.JOIN y) k'
  | reduces_continue:
    forall k x,
    Reduces k (x, CG.CONTINUE) k.

  Inductive Run : list event -> known_set -> Prop :=
  | run_nil:
    Run nil nil
  | run_cons:
    forall k k' t e,
    Run t k ->
    Reduces k e k' ->
    Run (e::t) k'.

End Defs.

End Events.

Section HB.

  Notation node := nat.

  Notation known_set := (list (tid * tid)).

  Inductive command :=
  | Cons: tid -> node -> command
  | Copy : node -> command
  | Append: node -> node -> command.

  Definition cg_safe_joins := list (node * command).

  Inductive In (x:tid) : node -> cg_safe_joins -> Prop :=
  | in_eq:
    forall n' l n,
    In x n ((n, Cons x n')::l)
  | in_neq:
    forall l n n' c,
    In x n l ->
    n <> n' ->
    In x n ((n', c) :: l)
  | in_cons:
    forall n' l y n,
    In x n' l ->
    x <> y ->
    In x n ((n, Cons y n') :: l)
  | in_copy:
    forall n' l n,
    In x n' l ->
    In x n ((n, Copy n') :: l)
  | in_append_left:
    forall n' l n n'',
    In x n' l ->
    In x n ((n, Append n' n'') :: l)
  | in_append_right:
    forall n' l n n'',
    In x n'' l ->
    In x n ((n, Append n' n'') :: l).

  Inductive Knows (cg:computation_graph) (sj:cg_safe_joins): tid * tid -> Prop :=
  | knows_def:
    forall x y nx,
    Nodes.MapsTo x nx (fst cg) ->
    In y nx sj ->
    Knows cg sj (x, y).

  Definition KnowsSpec cg sj k :=
    forall p,
    List.In p k ->
    Knows cg sj p.

  Section ESafeJoins.

  Inductive Reduces : cg_safe_joins -> computation_graph -> cg_safe_joins -> Prop :=
  | reduces_fork:
    forall x y x' ty l vs es,
    Nodes.MapsTo ty y vs ->
    Reduces l (vs, F (x,y)::C (x,x')::es) ((y, Copy x)::(x', Cons ty x)::l)

  | reduces_join:
    forall x y x' ty l vs es,
    Nodes.MapsTo ty y vs ->
    In ty x l -> (* check: ty \in x *)
    Reduces l (vs, J (y,x) :: C (x,x')::es) ((x', Append x y) :: l)

  | e_safe_joins_continue:
    forall x x' l es vs,
    Reduces l (vs, C (x,x')::es) ((x', Copy x) :: l).

  Let do_fork:
    forall x y z cg cg' sj sj',
    CG.Reduces cg (x, CG.FORK y) cg' ->
    Reduces sj cg' sj' ->
    Knows cg sj (x, z) ->
    Knows cg' sj' (y, z).
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H6; subst; clear H6.
    assert (prev = nx) by eauto using Nodes.maps_to_fun; subst; clear H12.
    apply knows_def with (nx:=ny); auto.
    inversion H0; subst; clear H0.
    apply in_copy.
    inversion H1; subst; simpl in *; clear H1.
  Qed.
  

  Lemma asdf:
    forall cg sj k k' cg' sj' e,
    KnowsSpec cg sj k ->
    Events.Reduces k e k' ->
    CG.Reduces cg e cg' ->
    Reduces sj cg' sj' ->
    KnowsSpec cg' sj' k'.
  Proof.
    intros.
    unfold KnowsSpec in *.
    intros.
    inversion H0; subst; clear H0.
    - inversion H4; subst; clear H4.
      destruct p as (a,b).
      apply fork_inv_in in H3.
      destruct H3 as [(?,?)|[(?,?)|?]]; subst.
      + apply H in H3; rename H3 into Hk.
        inversion H1; subst; clear H1.
        inversion H7; subst; clear H7.
        inversion H2; subst; clear H2.
        apply knows_def with (nx:=ny).
        * simpl.
          assumption.
        * apply in_copy.
          apply 
    inversion H1; subst; clear H1.
    - inversion H6; subst; clear H6.
      inversion H2; subst.
      inversion 
      apply knows_def.
  Qed.

  Let flat_sj := MN.t (list tid).

  Inductive Flatten : cg_safe_joins -> flat_sj -> Prop :=
  | flatten_nil:
    Flatten nil (MN.empty (list tid))
  | flatten_cons:
    forall l m x y z zs,
    Flatten l m ->
    MN.MapsTo z zs m ->
    Flatten ((x,Cons y z)::l) (MN.add x (y::zs) m)
  | flatten_copy:
    forall l m x y ys,
    Flatten l m ->
    MN.MapsTo y ys m ->
    Flatten ((x,Copy y)::l) (MN.add x ys m)
  | flatten_append:
    forall l m x y ys z zs,
    Flatten l m ->
    MN.MapsTo y ys m ->
    MN.MapsTo z zs m ->
    Flatten ((x,Append y z)::l) (MN.add x (ys ++ zs) m).

  Definition SafeJoins (cg:computation_graph) sj := ESafeJoins (fst cg) (snd cg) sj.



  Inductive MapsTo e :  (known_set * known_set) -> list cg_edge -> known_history -> Prop :=
  | maps_to_eq:
    forall e' es h,
    MapsTo e e' (e::es) (e'::h)
  | maps_to_cons:
    forall e' e'' es h p,
    MapsTo e e' es h ->
    MapsTo e e' (e''::es) (p::h).

  Definition Dom cg k:=
    forall x y t,
    TaskEdge cg t (x, y) ->
    In (FGraph.Edge k) x.

  Definition WFEdges (cg:computation_graph) (h:known_history) :=
  forall e x y z nx ny k k',
  List.In e (snd cg) ->
  e_edge e = (nx, ny) ->
  MapsTo e (k, k') (snd cg) h ->
  Nodes.MapsTo x nx (cg_nodes cg) ->
  Nodes.MapsTo y ny (cg_nodes cg) ->
  List.In (x, z) k ->
  List.In (y, z) k'.
(*
  Definition CGtoSJ cg k :=
  forall x,
  Graph.In (FGraph.Edge k) x ->
  Nodes.In x (cg_nodes cg).

  Definition ForkInKnown cg k :=
  forall x y,
  TaskEdge cg CG.FORK (x, y) ->
  List.In (x, y) k.
*)
  Let wf_safe_joins_continue:
    forall cg o cg' h,
    WFEdges cg h ->
    CG.op_t o = CG.CONTINUE ->
    CG.Reduces cg o cg' ->
    WFEdges cg' h.
  Proof.
    intros.
    unfold WFEdges in *.
    intros e a b c; intros.
    inversion H1; subst; clear H1; try (inversion H0; clear H0).
    simpl in *.
    destruct H2. {
      subst.
      simpl in *.
      inversion H3; subst; clear H3.
      inversion H4; subst; clear H4. {
        
      }
    }
    
  Qed.

  Let wf_safe_joins_continue:
    forall cg o cg' h,
    Inv cg h ->
    CG.op_t o = CG.CONTINUE ->
    CG.Reduces cg o cg' ->
    Inv cg' h.
  Proof.
    intros.
    rename H0 into Heq0.
    inversion H1; subst; clear H1; subst; inversion Heq0; clear Heq0.
    rename H0 into HL.
    rename H4 into mt_x.
    inversion H3; subst; simpl in *; clear H3.
    unfold c_edge, i_prev, i_curr; simpl.
    remember ( _ :: _ :: l)%list as lx'.
    unfold Inv.
    intros a b c; intros; simpl in *.
    inversion H0; subst; simpl in *; clear H0.
    inversion H9 as [He|He]; clear H9. {
      subst; simpl in *.
      inversion H10; subst; simpl in *; clear H10.
      apply H
      assert (kx = ky) by (unfold KnownOf in *; eauto using MN_Facts.MapsTo_fun).
      assumption.
    }
    assert (Edge (vs, es) (e_t e) (e_edge e)) by eauto using edge_def.
    destruct e; destruct e_edge; simpl in *.
    inversion H9; subst.
    assert (TaskEdge (vs, es) e_t (node_task na, b)). {
      assert (RW: b = node_task {| node_task := b; node_id := nbi |}) by auto.
      rewrite RW in *.
      auto using task_edge_def.
    }
    eauto.
  Qed.


  Let wf_safe_joins_continue:
    forall cg o cg' k,
    Inv cg k ->
    CG.op_t o = CG.CONTINUE ->
    CG.Reduces cg o cg' ->
    Inv cg' k.
  Proof.
    intros.
    rename H0 into Heq0.
    inversion H1; subst; clear H1; subst; inversion Heq0; clear Heq0.
    rename H0 into HL.
    rename H4 into mt_x.
    inversion H3; subst; simpl in *; clear H3.
    unfold c_edge, i_prev, i_curr; simpl.
    remember ( _ :: _ :: l)%list as lx'.
    unfold Inv.
    intros a b c; intros; simpl in *.
    inversion H3 as (na,(nb,nbi)); subst; clear H3.
    inversion H6; subst; clear H6.
    inversion H8 as [He|He]; clear H8. {
      subst; simpl in *.
      inversion H9; subst; simpl in *; clear H9.
      assumption.
    }
    assert (Edge (vs, es) (e_t e) (e_edge e)) by eauto using edge_def.
    destruct e; destruct e_edge; simpl in *.
    inversion H9; subst.
    assert (TaskEdge (vs, es) e_t (node_task na, b)). {
      assert (RW: b = node_task {| node_task := b; node_id := nbi |}) by auto.
      rewrite RW in *.
      auto using task_edge_def.
    }
    eauto.
  Qed.
(*
  Let wf_safe_joins_continue:
    forall cg o cg' k,
    WellFormedSafeJoins cg k ->
    CG.op_t o = CG.CONTINUE ->
    CG.Reduces cg o cg' ->
    WellFormedSafeJoins cg' k.
  Proof.
    intros.
    inversion H1; subst; clear H1; subst; inversion H0; clear H0.
    rename H2 into HL.
    rename H5 into mt_x.
    inversion H4; subst; simpl in *; clear H4.
    unfold WellFormedSafeJoins.
    intros a b c; intros; simpl in *.
    destruct H0. {
      inversion H0; subst; simpl in *; clear H0.
      assumption.
    }
    rename H4 into Hi.
    assert (Nodes.In c vs). {
      destruct Hi as (nc,(lc,mt)); simpl in *.
      rewrite MT_Facts.add_mapsto_iff in mt.
      destruct mt as [(?,?)|(?,?)];
      subst;
      eauto using Nodes.maps_to_def, Nodes.in_def.
    }
    eauto.
  Qed.
*)
  Variable cg: computation_graph.
  Variable cg': computation_graph.
  Variable k:  list (tid * tid).
  Variable k': list (tid * tid).
  Variable Hdag: DAG.DAG (FGraph.Edge k).
  Variable Hsj: Inv cg k.
  Variable Hdom: Dom cg k.
  Variable Hfk: ForkInKnown cg k.

  Lemma wf_safe_joins_fork:
    forall x y,
    CG.Reduces cg {| CG.op_t := CG.FORK; CG.op_src:=x; CG.op_dst:=y|} cg' ->
    Reduces k {| op_t := FORK; op_src:=x; op_dst:=y|} k' ->
    Inv cg' k'.
  Proof.
    intros.
    inversion H; subst; clear H; subst;
    inversion H2; subst; clear H2.
    rename H1 into HL.
    inversion H0; subst; clear H0.
    inversion H3; subst; clear H3.
    simpl in *.
    rename x0 into x; rename y0 into y.
    unfold Inv, c_edge, f_edge, i_prev, i_curr.
    intros a b c; intros; simpl in *.
    inversion H3 as (na,(nb,nbi)); subst; clear H3.
    inversion H9; subst; clear H9.
    inversion H11 as [He|He]; clear H11. {
      subst; simpl in *.
      inversion H12; subst; simpl in *; clear H12.
      assumption.
    }
    inversion He as [He'|He']; clear He. {
      subst.
      simpl in *.
      inversion H12; subst; clear H12.
      simpl in *.
      apply fork_inv_in in H0.
      destruct H0 as [(?,?)|[(?,?)|?]].
      - subst.
        auto using in_fork.
      - subst.
        contradiction H; trivial.
      - auto using in_fork_2.
    }
    destruct e; destruct e_edge; simpl in *.
    inversion H12; subst; clear H12.
    assert (HT: TaskEdge (vs, es) e_t (node_task na, b)). {
      destruct na; subst; simpl in *.
      eauto using task_edge_eq.
    }
    clear He'.
    remember (node_task na) as a; clear Heqa.
    apply fork_inv_in in H0.
    destruct H0 as [(Hx,Hy)|[(Hx,Hy)|Hx]].
    - subst; contradiction H7.
      apply Hdom in HT.
      assumption.
    - 
      destruct e_t.
      + 
        assert (List.In (node_task na, b) k) by eauto.
        apply in_fork_2 with (y:=c) in H0; eauto.
  Qed.

  Lemma wf_safe_joins_fork:
    forall x y,
    CG.Reduces cg {| CG.op_t := CG.FORK; CG.op_src:=x; CG.op_dst:=y|} cg' ->
    Reduces k {| op_t := FORK; op_src:=x; op_dst:=y|} k' ->
    WellFormedSafeJoins cg' k'.
  Proof.
    intros.
    inversion H; subst; clear H; subst;
    inversion H2; subst; clear H2.
    rename H1 into HL.
    inversion H0; subst; clear H0.
    inversion H3; subst; clear H3.
    simpl in *.
    rename x0 into x; rename y0 into y.
    unfold WellFormedSafeJoins.
    intros a b c; intros; simpl in *.
    destruct H as [He|He]. {
      inversion He; subst; simpl in *; clear He.
      assumption.
    }
    simpl in *.
    destruct He as [He|He']. {
      inversion He; subst; simpl in *; clear He.
      auto using in_fork_3.
    }
    assert (He: HB_Edge (vs,es) (a, b)) by auto; clear He'.
    destruct H3 as (nc,(lc,mt)); simpl in *.
    rewrite MT_Facts.add_mapsto_iff in mt.
    destruct mt as [(Hx,Hy)|(x_neq_c,mt)]. {
      inversion Hy; subst; clear Hy.
      assert (Nodes.In c vs) by
      eauto using Nodes.maps_to_def, Nodes.in_def.
      apply fork_inv_in in H0.
      destruct H0 as [(?,?)|[(?,?)|X]].
      - assert (X:= Hdag c).
        contradiction X.
        auto using edge_to_reaches.
      - subst.
        contradiction H2; auto.
      - eauto using in_fork.
    }
    rewrite MT_Facts.add_mapsto_iff in mt.
    destruct mt as [(Hx,Hy)|(y_neq_c,mt)]. {
      subst.
      inversion Hy; subst; clear Hy.
      apply in_fork_4 in H0; auto.
      subst.
      clear x_neq_c.
      destruct HL as (HL).
      rewrite hb_edge_spec in He.
      destruct He as (e, (Hi,Hp)).
      simpl in *.
      inversion Hp; subst; clear Hp.
      destruct t.
      - assert (Ht: TaskEdge (vs,es) CG.FORK (node_task a, node_task b))
        by eauto using task_edge_def, edge_def; clear Hi.
        apply Hfk in Ht.
        apply in_fork_2 with (y:=c) in Ht.
        apply in_fork.
        assert (List.In (c, node_task a) k) by eauto.
    }


    apply fork_inv_in in H0.
    destruct H0 as [(?,?)|[(?,?)|X]].
    - subst.
      assert (Hn : Nodes.In c vs). {
        assert (Hi: Graph.In (FGraph.Edge k) c) by eauto using in_right.
        auto.
      }
      unfold WellFormedSafeJoins in *.
      apply in_fork.
      rewrite MT_Facts.add_mapsto_iff in mt.
      destruct mt as [(Hx,Hy)|(y_neq_c,mt)]. {
        inversion Hy; subst; clear Hy.

      apply Hsj with (x:=x); auto.
      eauto.

    rewrite MT_Facts.add_mapsto_iff in mt.
    destruct mt as [(Hx,Hy)|(y_neq_c,mt)]. {
      subst.
      inversion Hy; subst; clear Hy.
      apply in_fork_4 in H0; auto.
      subst.
      clear x_neq_c.
    }
    
    - rewrite MT_Facts.add_mapsto_iff in mt.
      destruct mt as [(?,?)|(?,mt)].
      + subst.
          apply in_fork_4 in H2; auto.
          subst.
          eauto using Nodes.maps_to_def, Nodes.in_def.


    

    intros.
    unfold WellFormedSafeJoins; intros a b c; intros.
    inversion H2; subst; clear H2.
    inversion H1; clear H1.
    
    destruct o1; simpl in *.
    destruct o0; simpl in *.
    subst.
    simpl in *. {
      (* fork *)
      destruct H3 as [E|[E|?]];
      try (inversion E; subst; clear E; auto using in_fork_3); simpl in *.
      assert (He: HB_Edge (vs,es) (x, y)) by auto; clear H1.
      apply fork_inv_in in H4.
      destruct H4 as [(?,Hx)|[(?,?)|?]]; subst; simpl in *.
      - contradiction H13.
        assert (R:vs = cg_nodes (vs, es)) by auto; rewrite R in *.
        apply H in He.
        destruct He.
        auto using Nodes.contains_to_in.
      - destruct (tid_eq_dec (node_task x) (node_task y)). {
          rewrite e in *.
          unfold fork; rewrite in_app_iff; right.
          auto using in_eq.
        }
        unfold fork.
                clear H8 H9 H11.
        assert (R:vs = cg_nodes (vs, es)) by auto; rewrite R in *.
        apply H in He.
        destruct He.
        apply in_fork.
        auto using in_fork_3.
    }
  Qed.


  Let wf_safe_joins:
    forall cg k o cg' k',
    WellFormedEdges cg ->
    WellFormedSafeJoins cg k ->
    CG.Reduces cg o cg' ->
    Reduces k o k' ->
    WellFormedSafeJoins cg' k'.
  Proof.
    intros.
    unfold WellFormedSafeJoins; intros.
    inversion H2; subst; clear H2;
    inversion H1; subst; clear H1;
    inversion H2; subst; clear H2;
    simpl in *. {
      (* fork *)
      destruct H3 as [E|[E|?]];
      try (inversion E; subst; clear E; auto using in_fork_3); simpl in *.
      assert (He: HB_Edge (vs,es) (x, y)) by auto; clear H1.
      apply fork_inv_in in H4.
      destruct H4 as [(?,Hx)|[(?,?)|?]]; subst; simpl in *.
      - contradiction H13.
        assert (R:vs = cg_nodes (vs, es)) by auto; rewrite R in *.
        apply H in He.
        destruct He.
        auto using Nodes.contains_to_in.
      - destruct (tid_eq_dec (node_task x) (node_task y)). {
          rewrite e in *.
          unfold fork; rewrite in_app_iff; right.
          auto using in_eq.
        }
        unfold fork.
                clear H8 H9 H11.
        assert (R:vs = cg_nodes (vs, es)) by auto; rewrite R in *.
        apply H in He.
        destruct He.
        apply in_fork.
        auto using in_fork_3.
    }
    (* join *)
  Qed.

  Lemma sj_hb:
    forall t x y z k cg a,
    Safe t k ->
    CG a t cg -> 
    HB_Edge cg (x, y) ->
    List.In (node_task x, z) k ->
    z <> node_task y ->
    List.In (node_task y, z) k.
  Proof.
    induction t; intros. {
      inversion H.
      subst.
      inversion H2.
    }
    inversion H; subst; clear H; rename k0 into k.
    unfold eval in *.
    inversion H0; subst; simpl in *; clear H0.
    apply reduces_to_reduces_ex in H9.
    inversion H9; subst; clear H9.
    inversion H; subst; clear H; simpl in *.
    - destruct H1 as [?|[?|?]].
      + simpl in *.
        inversion H; subst; clear H; simpl in *.
        auto using in_fork_3.
      + simpl in *. 
        inversion H; subst; clear H; simpl in *.
        auto using in_fork_3.
      + assert (He: HB_Edge (vs,es) (x, y)) by auto; clear H.
        apply fork_inv_in in H2.
        destruct H2 as [(?,Hx)|[(?,?)|?]]; subst; simpl in *.
        * contradiction H9.
          assert (R:vs = cg_nodes (vs, es)) by auto; rewrite R.
          eapply node_in_cg; eauto using in_left.
        *  
  Qed.
End HB.

Module Lang.

  Fixpoint from_trace ts := 
  match ts with
  | nil => nil
  | o :: ts => eval o (from_trace ts)
  end.

  Definition effects_to_sj ts := from_trace (CG.Lang.from_effects ts).

  Definition Safe ts := Safe (CG.Lang.from_effects ts) (effects_to_sj ts).
End Lang.
