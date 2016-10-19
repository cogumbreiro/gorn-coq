Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Lists.ListSet.
Require Import Aniceto.ListSet.
Require Import Aniceto.Graphs.Graph.
Require Import Omega.

Require Import Tid.
Require Import Mid.
Require Import Cid.
Require Import Var.
Require Import Dep.
Require Import Node.
(* ----- end of boiler-plate code ---- *)

Set Implicit Arguments.

Require Import Aniceto.Graphs.DAG.
Require Import Coq.Relations.Relation_Operators.
Require Aniceto.Graphs.Graph.

Require Import Coq.Structures.OrderedTypeEx.

Section Defs.

  Inductive op :=
  | FORK : tid -> op
  | JOIN : tid -> op
  | CONTINUE : op.

  Definition event := (tid * op) % type.
  Definition trace := list event.    

  Inductive edge_type :=
  | E_FORK
  | E_JOIN
  | E_CONTINUE.

  Structure cg_edge := cg_e {
    e_t: edge_type;
    e_edge: (node * node)
  }.
End Defs.

Notation F := (cg_e E_FORK).
Notation J := (cg_e E_JOIN).
Notation C := (cg_e E_CONTINUE).

Notation cg_edges es := (map e_edge es).

Section Edges.

  (**
    When creating a tee, the inter edge is the only thing
    that changes depending on the type of the node.
    *)


  Notation edge := (node * node) % type.

  Definition computation_graph := (list tid * list cg_edge) % type.

  Inductive Edge : list cg_edge -> edge_type -> (node * node) -> Prop :=
  | edge_def:
    forall es e,
    List.In e es ->
    Edge es (e_t e) (e_edge e).

  Inductive HB_Edge es e : Prop :=
  | hb_edge_def:
    forall t,
    Edge es t e ->
    HB_Edge es e.

  Lemma edge_eq:
    forall es t x y,
     List.In {| e_t := t; e_edge := (x,y) |} es ->
     Edge es t (x, y).
  Proof.
    intros.
    remember {| e_t := t; e_edge := (x, y) |} as e.
    assert (R:(x, y) = e_edge e) by (subst; auto).
    rewrite R.
    assert (R2:t = e_t e) by (subst; auto).
    rewrite R2.
    auto using edge_def.
  Qed.

  Lemma hb_edge_in:
    forall e es,
    List.In e es ->
    HB_Edge es (e_edge e).
  Proof.
    eauto using hb_edge_def, edge_def.
  Qed.

  Inductive Reduces: computation_graph -> event -> computation_graph -> Prop :=
  | reduces_fork:
    forall vs es es' vs' y x nx ny,
    x <> y ->
    ~ List.In y vs -> 
    Reduces (vs,es) (x, CONTINUE) (vs', es') ->
    MapsTo x nx vs ->
    MapsTo y ny (y::vs') ->
    Reduces (vs,es) (x, FORK y) (y::vs', F (nx,ny) :: es')
  | reduces_join:
    forall vs es vs' es' x y nx ny,
    x <> y ->
    Reduces (vs,es) (x, CONTINUE) (vs', es') ->
    MapsTo x nx vs' ->
    MapsTo y ny vs' ->
    Reduces (vs,es) (x, JOIN y) (vs', J (ny, nx) :: es')
  | reduces_continue:
    forall vs (es:list cg_edge) x prev curr,
    MapsTo x prev vs ->
    MapsTo x curr (x::vs) ->
    Reduces (vs,es) (x, CONTINUE) (x::vs, C (prev, curr) :: es).

  (** The cannonical way to interpret the results of a reduction step in a CG. *)

  Inductive result :=
  | R_FORK: cg_edge -> cg_edge -> result
  | R_JOIN: cg_edge -> cg_edge -> result
  | R_CONTINUE: cg_edge -> result.

  Inductive ReductionResult : event ->  computation_graph -> result -> Prop :=
  | reduction_result_fork:
    forall y x vs es nx,
    MapsTo x nx vs ->
    ReductionResult (x, FORK y) (y::x::vs, F (nx,fresh (x::vs))::C (nx,fresh vs)::es) (R_FORK (F (nx,fresh (x::vs))) (C (nx,fresh vs)))
  | result_join:
    forall x y nx ny vs es,
    MapsTo y ny vs ->
    MapsTo x nx vs ->
    ReductionResult (x, JOIN y) (x::vs, J (ny,fresh vs) :: C (nx,fresh vs)::es) (R_JOIN (J (ny,fresh vs)) (C (nx,fresh vs)))
  | result_continue:
    forall x nx es vs,
    MapsTo x nx vs ->
    ReductionResult (x, CONTINUE) (x::vs, C (nx,fresh vs)::es) (R_CONTINUE (C (nx,fresh vs))).

  Definition make_cg x : computation_graph := (x::nil, nil).

  Inductive Run (x:tid): trace -> computation_graph -> Prop :=
  | run_nil:
    Run x nil (make_cg x)
  | run_cons:
    forall cg o t cg',
    Run x t cg ->
    Reduces cg o cg' ->
    Run x (o::t) cg'.

  (** Getting the trace from a computation, which works as the type of a CG. *)

  Inductive TraceOf : computation_graph -> tid -> trace -> Prop :=
  | trace_of_nil:
    forall x,
    TraceOf (make_cg x) x nil
  | trace_of_fork:
    forall vs es a t x y nx,
    x <> y ->
    ~ List.In y vs ->
    TraceOf (vs, es) a t ->
    MapsTo x nx vs ->
    TraceOf (y::x::vs, F (nx, fresh (x::vs)) :: C (nx, fresh vs) :: es)
       a ((x, FORK y)::t)
  | trace_of_join:
    forall vs es a t x y ny nx,
    x <> y ->
    TraceOf (vs, es) a t ->
    MapsTo x nx vs ->
    MapsTo y ny vs ->
    TraceOf (x::vs, J (ny, fresh vs) :: C (nx, fresh vs) :: es)
       a ((x, JOIN y)::t)
  | trace_of_continue:
    forall vs es a t x nx,
    TraceOf (vs, es) a t ->
    MapsTo x nx vs ->
    TraceOf (x::vs, C (nx, fresh vs) :: es) a ((x, CONTINUE)::t).

  Lemma trace_of_cons:
    forall cg a t e cg',
    TraceOf cg a t ->
    Reduces cg e cg' ->
    TraceOf cg' a (e::t).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    - inversion H3; subst; clear H3.
      assert (prev = nx) by eauto using maps_to_fun_2; subst.
      apply maps_to_inv_eq in H11; subst.
      apply maps_to_inv_eq in H5; subst.
      auto using trace_of_fork.
    - inversion H2; subst; clear H2.
      apply maps_to_inv_eq in H3; subst.
      apply maps_to_inv_eq in H10; subst.
      apply maps_to_neq in H4; auto.
      eauto using trace_of_join.
    - apply maps_to_inv_eq in H2; subst.
      auto using trace_of_continue.
  Qed.

  Lemma run_to_trace_of:
    forall cg a t,
    Run a t cg ->
    TraceOf cg a t.
  Proof.
    intros.
    induction H. {
      apply trace_of_nil.
    }
    eauto using trace_of_cons.
  Qed.

  Lemma trace_of_to_run:
    forall cg a t,
    TraceOf cg a t ->
    Run a t cg.
  Proof.
    intros.
    induction H.
    - apply run_nil.
    - eapply run_cons; eauto.
      apply reduces_fork; auto using maps_to_eq, reduces_continue.
    - eauto using run_cons, reduces_join, reduces_continue, maps_to_eq, maps_to_cons.
    - eauto using run_cons, reduces_continue, maps_to_eq, maps_to_cons.
  Qed.

  (**
     The main result is that the information in the trace is
     the same as the information in the CG.
     *)

  Lemma trace_of_spec:
    forall cg a t,
    Run a t cg <-> TraceOf cg a t.
  Proof.
    split; auto using trace_of_to_run, run_to_trace_of.
  Qed.

  Definition cg_nodes (cg:computation_graph) := fst cg.

  (** Every node of the CG is an index of the list of vertices. *)

  Definition EdgeToNode (cg:computation_graph) :=
    forall x y,
    HB_Edge (snd cg) (x, y) ->
    Node x (fst cg) /\ Node y (fst cg).


  Inductive SpawnPoint x n : computation_graph -> Prop :=
  | spawn_point_eq:
    forall vs es n' n'',
    SpawnPoint x n (x::vs, F (n', n'') :: C(n', n) :: es)
  | spawn_point_neq:
    forall vs es e y,
    x <> y ->
    SpawnPoint x n (vs, es) ->
    SpawnPoint x n (y::vs, (F e) :: es)
  | spawn_point_continue:
    forall vs es e y,
    SpawnPoint x n (vs, es) ->
    SpawnPoint x n (y::vs, (C e) :: es)
  | spawn_point_join:
    forall vs es e y,
    SpawnPoint x n (y::vs, es) ->
    SpawnPoint x n (y::vs, (J e) :: es).
End Edges.

Section Props.

  Lemma in_make:
    forall t,
    List.In t (cg_nodes (make_cg t)).
  Proof.
    intros.
    simpl; auto.
  Qed.

  Inductive Prec : (node * node) -> cg_edge -> Prop :=
  | prec_def:
    forall e,
    Prec (e_edge e) e.

  Variable es: list cg_edge.

  Let HB_Edge_alt e := List.Exists (Prec e) es.

  Definition HB := Reaches (HB_Edge es).

  Definition MHP x y : Prop := ~ HB x y /\ ~ HB y x.

  Definition Le x y := x = y \/ HB x y.

  Let in_edges_to_tees:
    forall e,
    List.In e (map e_edge es) ->
    exists x, List.In x es /\ Prec e x.
  Proof.
    intros.
    rewrite in_map_iff in *.
    destruct H as (x, (Hi, He)).
    exists x; split; auto.
    subst; eauto using prec_def.
  Qed.

  Let in_tees_to_edges:
    forall x e,
    List.In x es ->
    Prec e x ->
    List.In e (map e_edge es).
  Proof.
    intros.
    rewrite in_map_iff in *.
    inversion H0;
    subst;
    eauto.
  Qed.

  Lemma hb_trans:
    forall x y z,
    HB x y ->
    HB y z ->
    HB x z.
  Proof.
    intros.
    unfold HB in *.
    eauto using reaches_trans.
  Qed.

  (** Comparable with respect to the happens-before relation [n1 < n2 \/ n2 < n1] *)

  Inductive Comparable n1 n2 : Prop :=
  | comparable_left_right:
    HB n1 n2 ->
    Comparable n1 n2
  | comparable_right_left:
    HB n2 n1 ->
    Comparable n1 n2.

  Lemma comparable_symm:
    forall x y,
    Comparable x y ->
    Comparable y x.
  Proof.
    intros.
    inversion H; auto using comparable_left_right, comparable_right_left.
  Qed.

  Lemma comparable_to_not_mhp:
    forall x y,
    Comparable x y ->
    ~ MHP x y.
  Proof.
    intros.
    unfold not; intros.
    inversion H0.
    inversion H; contradiction.
  Qed.

  Inductive Relation x y : Prop :=
  | L_HB_R: HB x y -> Relation x y
  | R_HB_L: HB y x -> Relation x y
  | EQ: x = y -> Relation x y
  | PAR: MHP x y -> Relation x y.

  Lemma hb_dec:
    forall x y,
    Relation x y.
  Admitted. (* TODO: prove this at the graph-level *)

End Props.

Section HB.

  Lemma hb_edge_spec:
    forall e es,
    HB_Edge es e <-> List.In e (map e_edge es).
  Proof.
    split; intros.
    - destruct H.
      inversion H; subst; clear H.
      simpl.
      auto using in_map.
    - rewrite in_map_iff in *.
      destruct H as (?,(?,?)); subst.
      simpl in *.
      eauto using hb_edge_in.
  Qed.
(*
  Lemma hb_edge_spec:
    forall e cg,
    HB_Edge (snd cg) e <-> List.In e (cg_edges cg).
  Proof.
    split; intros.
    - destruct H.
      inversion H; subst; clear H.
      unfold cg_edges.
      simpl.
      auto using in_map.
    - unfold cg_edges in *; rewrite in_map_iff in *.
      destruct H as (?,(?,?)); subst.
      simpl in *.
      eauto using hb_edge_in.
  Qed.
*)
  Lemma node_lt_length_left:
    forall n1 n2 vs es,
    EdgeToNode (vs,es) ->
    List.In (n1, n2) (map e_edge es) ->
    NODE.lt n1 (fresh vs).
  Proof.
    intros.
    apply hb_edge_spec in H0.
    apply H in H0.
    destruct H0.
    auto using node_lt.
  Qed.

  Let walk2_edge_false:
    forall {A:Type} (x y:A) w,
    ~ Walk2 (fun _ => False) x y w.
  Proof.
    intuition.
    destruct H.
    destruct w.
    - eauto using starts_with_inv_nil.
    - eapply walk_to_edge; eauto using in_eq.
  Qed.

  Let reaches_edge_false:
    forall {A:Type} (x y:A),
    ~ Reaches (fun _ => False) x y.
  Proof.
    intuition.
    inversion H.
    apply walk2_edge_false in H0; auto.
  Qed.

  Lemma hb_make_cg_absurd:
    forall a x y,
    ~ HB (snd (make_cg a)) x y.
  Proof.
    intros.
    intuition.
    inversion H.
    inversion H0; subst.
    destruct w. {
      apply starts_with_inv_nil in H1; contradiction.
    }
    assert (HB_Edge (snd (make_cg a)) p). {
      eapply walk_to_edge; eauto using List.in_eq.
    }
    rewrite hb_edge_spec in H4.
    simpl in H4.
    contradiction.
  Qed.

  Lemma hb_to_fgraph:
    forall es x y,
    HB es x y ->
    Reaches (FGraph.Edge (map e_edge es)) x y.
  Proof.
    unfold HB.
    intros.
    apply reaches_impl with (E:=HB_Edge es); auto.
    intros.
    rewrite hb_edge_spec in *.
    simpl in *.
    auto.
  Qed.

  Lemma fgraph_to_hb:
    forall es x y,
    Reaches (FGraph.Edge (map e_edge es)) x y ->
    HB es x y.
  Proof.
    unfold  HB; intros.
    apply reaches_impl with (E:=FGraph.Edge (map e_edge es)); auto.
    intros.
    rewrite hb_edge_spec.
    auto.
  Qed.

  Lemma hb_fgraph_spec:
    forall es x y,
    HB es x y <->
    Reaches (FGraph.Edge (map e_edge es)) x y.
  Proof.
    split; eauto using hb_to_fgraph, fgraph_to_hb.
  Qed.

End HB.

  Ltac simpl_red :=
  repeat match goal with
  | [ H: Reduces _ (_, FORK _) _ |- _ ] =>
      inversion H; subst; clear H;
      match goal with
      | [ H: Reduces _ (_, CONTINUE) _ |- _ ] => inversion H; subst; clear H; simpl_node
      end
  | [ H: Reduces _ (_, JOIN _) _ |- _ ] =>
      inversion H; subst; clear H;
      match goal with
      | [ H: Reduces _ (_, CONTINUE) _ |- _ ] => inversion H; subst; clear H; simpl_node
      end
  | [ H: Reduces _ (_, CONTINUE) _ |- _ ] => inversion H; subst; clear H; simpl_node
  end.

Section PropsEx.
  Lemma make_edge_to_node:
    forall x,
    EdgeToNode (make_cg x).
  Proof.
    intros.
    unfold make_cg, EdgeToNode.
    intros.
    simpl in *.
    rewrite hb_edge_spec in H.
    simpl in *.
    contradiction.
  Qed.

  Let edge_to_node_in:
    forall vs es e a b,
    EdgeToNode (vs, es) ->
    List.In e es ->
    e_edge e = (a, b) ->
    Node a vs /\ Node b vs.
  Proof.
    intros.
    assert (He: HB_Edge es (e_edge e)) by auto using hb_edge_in.
    rewrite H1 in *.
    apply H in He.
    simpl in *.
    assumption.
  Qed.

  Let edge_to_node_in_fst:
    forall vs es e a b,
    EdgeToNode (vs, es) ->
    List.In e es ->
    e_edge e = (a, b) ->
    Node a vs.
  Proof.
    intros.
    assert (He : Node a vs /\ Node b vs) by eauto.
    destruct He; auto.
  Qed.

  Let edge_to_node_in_snd:
    forall vs es e a b,
    EdgeToNode (vs, es) ->
    List.In e es ->
    e_edge e = (a, b) ->
    Node b vs.
  Proof.
    intros.
    assert (He : Node a vs /\ Node b vs) by eauto.
    destruct He; auto.
  Qed.

  Lemma reduces_edge_to_node:
    forall cg e cg',
    EdgeToNode cg ->
    Reduces cg e cg' ->
    EdgeToNode cg'.
  Proof.
    intros.
    unfold EdgeToNode; intros a b; intros.
    destruct H1 as (et, He).
    destruct e as (?,[]); simpl_red; simpl in *;
    inversion He as (?,e,Hi,Hx,Hy,Heq); subst; clear He;
    destruct Hi as [Hx|Hx]; subst; simpl in *; inversion Heq; subst;
    eauto 8 using maps_to_lt, lt_to_node, node_cons, maps_to_eq;
    destruct Hx; subst; simpl in *; inversion Heq;subst;
      split; eauto using maps_to_lt, lt_to_node, node_cons, maps_to_eq.
  Qed.

  Lemma run_to_edge_to_node:
    forall t a cg,
    Run a t cg ->
    EdgeToNode cg.
  Proof.
    intros.
    induction H.
    - auto using make_edge_to_node.
    - eauto using run_cons, reduces_edge_to_node.
  Qed.

  Lemma reduction_results_spec:
    forall cg e cg',
    Reduces cg e cg' ->
    exists r, ReductionResult e cg' r.
  Proof.
    intros.
    destruct e as (?,[]); simpl_red; eauto using reduction_result_fork, result_join, result_continue.
  Qed.

  Lemma f_edge_to_hb_edge:
    forall es a b,
    FGraph.Edge (map e_edge es) (a, b) ->
    HB_Edge es (a, b).
  Proof.
    intros.
    rewrite hb_edge_spec.
    auto.
  Qed.

  Lemma edge_to_node_fresh_not_in:
    forall vs es,
    EdgeToNode (vs, es) ->
    ~ In (FGraph.Edge (map e_edge es)) (fresh vs).
  Proof.
    unfold not; intros.
    destruct H0 as ((v1,v2),(Hx,Hy)).
    assert (He: HB_Edge es (v1, v2)) by eauto using f_edge_to_hb_edge.
    apply H in He.
    destruct He as (Ha,Hb).
    simpl in *.
    destruct Hy; simpl in *; subst.
    - apply node_absurd_fresh in Ha; contradiction.
    - apply node_absurd_fresh in Hb; contradiction.
  Qed.

  Lemma edge_to_node_hb:
    forall vs es x y,
    EdgeToNode (vs, es) ->
    HB es x y ->
    Node x vs /\ Node y vs.
  Proof.
    intros.
    destruct H0.
    destruct w. {
      apply walk2_nil_inv in H0; contradiction.
    }
    destruct w. {
      apply walk2_inv_pair in H0.
      destruct H0.
      eauto.
    }
    apply walk2_inv in H0.
    destruct H0 as (z, (R, (Hx, Hy))).
    subst.
    apply H in Hx.
    destruct Hx as (Hx,_); split; auto; clear Hx.
    destruct Hy.
    destruct H1 as ((v3,v4), (Hx, Hy)).
    simpl in *; subst.
    eapply end_to_edge in Hx; eauto.
    apply H in Hx.
    destruct Hx; auto.
  Qed.

  Lemma edge_to_node_hb_fst:
    forall vs es x y,
    EdgeToNode (vs, es) ->
    HB es x y ->
    Node x vs.
  Proof.
    intros.
    eapply edge_to_node_hb in H0; eauto.
    destruct H0; auto.
  Qed.

  Lemma edge_to_node_hb_snd:
    forall vs es x y,
    EdgeToNode (vs, es) ->
    HB es x y ->
    Node y vs.
  Proof.
    intros.
    eapply edge_to_node_hb in H0; eauto.
    destruct H0; auto.
  Qed.

  Lemma hb_edge_cons:
    forall es e a b,
    HB_Edge es (a, b) ->
    HB_Edge (e :: es) (a, b).
  Proof.
    intros.
    rewrite hb_edge_spec in *.
    simpl in *.
    intuition.
  Qed.

  Lemma hb_impl_cons:
    forall es x y e,
    HB es x y ->
    HB (e::es) x y.
  Proof.
    intros.
    rewrite hb_fgraph_spec in *; simpl in *;
    eauto using FGraph.reaches_impl_cons.
  Qed.

  Lemma hb_impl:
    forall e cg cg',
    Reduces cg e cg' ->
    forall x y,
    HB (snd cg) x y ->
    HB (snd cg') x y.
  Proof.
    intros.
    inversion H; subst; simpl_red;
    eauto using hb_impl_cons.
  Qed.

End PropsEx.


Section DAG.
  Require Import Aniceto.Graphs.DAG.

  Let LtEdge e := NODE.lt (fst e) (snd e).
  Definition LtEdges es := List.Forall LtEdge es.
  Let Sup x (e:node*node) := NODE.lt (snd e) x.
  Definition HasSup cg := List.Forall (Sup (fresh (A:=tid) (fst cg))) (map e_edge (snd cg)).

  Let edge_to_lt:
    forall es x y,
    LtEdges es ->
    FGraph.Edge es (x, y) ->
    NODE.lt x y.
  Proof.
    intros.
    unfold FGraph.Edge in *.
    unfold LtEdges in *.
    rewrite List.Forall_forall in H.
    apply H in H0.
    auto.
  Qed.

  Let walk_2_to_lt:
    forall w x y es,
    LtEdges es ->
    Walk2 (FGraph.Edge es) x y w ->
    NODE.lt x y.
  Proof.
    induction w; intros. {
      apply walk2_nil_inv in H0.
      contradiction.
    }
    inversion H0; subst; clear H0.
    destruct a as (v1,v2).
    apply starts_with_eq in H1; subst.
    destruct w as [|(a,b)]. {
      apply ends_with_eq in H2.
      subst.
      assert (Hi: FGraph.Edge es (x,y)). {
        eapply walk_to_edge; eauto using List.in_eq.
      }
      eauto.
    }
    assert (Hlt: NODE.lt x v2). {
      assert (FGraph.Edge es (x, v2)) by (eapply walk_to_edge; eauto using List.in_eq).
      eauto.
    }
    inversion H3; subst; clear H3.
    apply linked_inv in H6; symmetry in H6; subst.
    apply ends_with_inv in H2.
    assert (NODE.lt a y) by eauto using walk2_def, starts_with_def.
    eauto using NODE.lt_trans.
  Qed.

  Let reaches_to_lt:
    forall x y es,
    LtEdges es ->
    Reaches (FGraph.Edge es) x y ->
    NODE.lt x y.
  Proof.
    intros.
    inversion H0.
    eauto.
  Qed.

  Lemma hb_to_lt:
    forall x y es,
    LtEdges (map e_edge es) ->
    HB es x y ->
    NODE.lt x y.
  Proof.
    intros.
    apply hb_to_fgraph in H0.
    eauto.
  Qed.

  Lemma cg_dag:
    forall (es:list (node*node)),
    LtEdges es ->
    DAG (FGraph.Edge es).
  Proof.
    intros.
    unfold DAG.
    intros.
    unfold not; intros.
    apply reaches_to_lt in H0; auto.
    unfold NODE.lt in *.
    omega.
  Qed.

  Let maps_to_lt_edge_cons:
    forall {A:Type} (x:A) n vs,
    MapsTo x n vs ->
    LtEdge (n, fresh (x :: vs)).
  Proof.
    intros.
    apply maps_to_lt in H.
    unfold NODE.lt, fresh in *.
    unfold LtEdge; simpl in *.
    omega.
  Qed.

  Let maps_to_lt_edge:
    forall {A:Type} (x:A) n vs,
    MapsTo x n vs ->
    LtEdge (n, fresh vs).
  Proof.
    intros.
    apply maps_to_lt in H.
    unfold NODE.lt, fresh in *.
    unfold LtEdge; simpl in *.
    omega.
  Qed.

  Lemma lt_edges_reduces:
    forall (cg cg':computation_graph) e,
    LtEdges (map e_edge (snd cg)) ->
    Reduces cg e cg' ->
    LtEdges (map e_edge (snd cg')).
  Proof.
    intros.
    destruct e as (?,[]); simpl_red; simpl in *;
    apply List.Forall_cons; eauto.
  Qed.

  Lemma hb_irrefl:
    forall x es,
    LtEdges (map e_edge es) ->
    ~ HB es x x.
  Proof.
    intros.
    apply cg_dag in H.
    unfold DAG in *.
    unfold not; intros.
    apply hb_fgraph_spec in H0.
    simpl in *.
    apply H in H0.
    contradiction.
  Qed.

  Let sub_fresh_cons_lhs:
    forall {A:Type} (x:A) vs n,
    Sup (fresh (x :: vs)) (n, fresh vs).
  Proof.
    intros.
    unfold Sup.
    simpl.
    unfold NODE.lt, fresh; simpl; omega.
  Qed.

  Let sub_fresh_cons_cons:
    forall {A:Type} (x y:A) vs n,
    MapsTo x n vs ->
    Sup (fresh (y :: x :: vs)) (n, fresh vs).
  Proof.
    intros.
    unfold Sup.
    simpl.
    unfold NODE.lt, fresh; simpl; omega.
  Qed.

  Let lt_fresh_cons:
    forall {A:Type} (x:A) vs,
    NODE.lt (fresh vs) (fresh (x::vs)).
  Proof.
    intros.
    unfold NODE.lt, fresh; simpl; auto.
  Qed.

  Lemma has_sup_reduces:
    forall cg cg' e,
    HasSup cg ->
    Reduces cg e cg' ->
    HasSup cg'.
  Proof.
    intros.
    destruct e as (?,[]); simpl_red;
      unfold HasSup in *; simpl in *;
      apply List.Forall_cons; eauto;
      try (apply List.Forall_cons; eauto);
      rewrite List.Forall_forall in *;
      intros (a,b); intros;
      apply H in H0;
      unfold Sup in *;
      simpl in *;
      eauto using NODE.lt_trans.
  Qed.

  Let walk2_to_hb:
    forall es a b w n1 n2 t,
    Walk2 (FGraph.Edge ((n1, n2) :: map e_edge es)) a b w ->
    HB ({| e_t := t; e_edge := (n1,n2) |} :: es) a b.
  Proof.
    intros.
    apply fgraph_to_hb.
    simpl.
    eauto using reaches_def.
  Qed.

  Notation in_edge_dec := (in_dec (Pair.pair_eq_dec node_eq_dec)).

  Lemma edge_to_node_cons_node:
    forall x vs es,
    EdgeToNode (vs, es) ->
    EdgeToNode (x::vs, es).
  Proof.
    intros.
    unfold EdgeToNode.
    intros a b; intros.
    simpl.
    assert (He: HB_Edge es (a,b)). {
      rewrite hb_edge_spec in *.
      simpl in *.
      assumption.
    }
    apply H in He.
    destruct He.
    simpl in *.
    auto using node_cons.
  Qed.

  Lemma hb_edge_eq:
    forall es x y t,
    HB_Edge ({| e_t := t; e_edge := (x, y) |} :: es) (x, y).
  Proof.
    intros.
    rewrite hb_edge_spec in *.
    simpl in *.
    auto.
  Qed.

  Lemma hb_edge_to_hb:
    forall es x y,
    HB_Edge es (x,y) ->
    HB es x y.
  Proof.
    intros.
    rewrite hb_fgraph_spec.
    rewrite hb_edge_spec in H.
    eauto using edge_to_reaches.
  Qed.

  Lemma edge_to_node_inv_cons_edge:
    forall vs es x y t,
    EdgeToNode (vs, {|e_t := t; e_edge:=(x,y)|}::es) ->
    EdgeToNode (vs, es) /\ Node x vs /\ Node y vs.
  Proof.
    intros.
    split;
    try unfold EdgeToNode; simpl; intros;
    eauto using hb_edge_eq, hb_edge_cons, hb_edge_to_hb, edge_to_node_hb_snd, edge_to_node_hb_fst.
  Qed.

  Lemma edge_to_node_cons_edge:
    forall vs es x y t,
    EdgeToNode (vs, es) ->
    Node x vs ->
    Node y vs ->
    EdgeToNode (vs, {|e_t := t; e_edge:=(x,y)|}::es).
  Proof.
    intros.
    unfold EdgeToNode; intros a b; intros.
    simpl.
    rewrite hb_edge_spec in *.
    simpl in *.
    destruct H2.
    - inversion H2; subst; auto.
    - apply H.
      rewrite hb_edge_spec in *.
      auto.
  Qed.

  Lemma lt_edges_inv_cons_edge:
    forall es x y t,
    LtEdges (map e_edge ({|e_t := t; e_edge:=(x,y)|}::es)) ->
    LtEdges (map e_edge es) /\ LtEdge (x,y).
  Proof.
    intros.
    unfold LtEdges in *.
    inversion H; subst.
    auto.
  Qed.

  Lemma lt_edges_cons_edge:
    forall es x y t,
    LtEdges (map e_edge es) ->
    LtEdge (x,y) ->
    LtEdges (map e_edge ({|e_t := t; e_edge:=(x,y)|}::es)).
  Proof.
    intros.
    unfold LtEdges in *.
    apply List.Forall_cons; auto.
  Qed.

  Lemma hb_inv_cons_c:
    forall a b vs x n es t,
    EdgeToNode (x::vs, {| e_t := t; e_edge := (n,fresh vs) |} :: es) ->
    LtEdges (map e_edge ({| e_t := t; e_edge := (n,fresh vs) |} :: es)) ->
    HB ({| e_t := t; e_edge := (n,fresh vs) |} :: es) a b ->
    HB es a b \/ b = fresh vs.
  Proof.
    intros.
    rewrite hb_fgraph_spec in *.
    simpl in *.
    destruct H1 as (w, Hw).
    (* -- *)
    destruct (in_edge_dec (n, fresh vs) w). {
      apply in_split in i.
      destruct i as (w1, (w2, R)); subst.
      destruct w1. {
        simpl in *.
        destruct w2. {
          apply walk2_inv_eq_snd in Hw.
          subst.
          auto.
        }
        apply walk2_inv in Hw.
        destruct Hw as (c, (R, (He, Hw))).
        inversion R; subst; clear R.
        eapply walk2_to_hb with (t:=t) in Hw; auto.
        assert (Hb: Node b (x::vs)) by eauto using edge_to_node_hb_snd.
        apply node_inv in Hb.
        destruct Hb as [?|Hb]; auto.
        apply node_lt in Hb.
        apply hb_to_lt in Hw; auto.
        unfold NODE.lt in *; simpl in *; omega.
      }
      apply walk2_split_app in Hw.
      destruct Hw as (_,Hw).
      destruct w2. {
        apply walk2_inv_eq_snd in Hw.
        subst.
        auto.
      }
      apply walk2_inv in Hw.
      destruct Hw as (c, (R, (He, Hw))).
      inversion R; subst; clear R.
      apply walk2_to_hb with (t:=t) in Hw; auto.
      assert (Hb: Node b (x::vs)) by eauto using edge_to_node_hb_snd.
      apply node_inv in Hb.
      destruct Hb as [?|Hb]; auto.
      apply node_lt in Hb.
      apply hb_to_lt in Hw; auto.
      unfold NODE.lt in *; simpl in *; omega.
    }
    left; 
    eauto using FGraph.walk2_inv_not_in_walk, reaches_def.
  Qed.

  Let fdag_walk2_inv_0 {A}:
    forall w (x:A) y z es,
    DAG (FGraph.Edge es) ->
    Walk2 (FGraph.Edge es) x y w ->
    List.In (x, z) w ->
    exists w', w = (x,z)::w' /\ ~ List.In (x,z) w'.
  Proof.
    induction w; intros. {
      inversion H1.
    }
    assert (Hw0 := H0).
    inversion H1; subst; clear H1. {
      destruct w as [|(a,b)]. {
        assert (z = y). {
          apply walk2_inv_eq_snd in H0.
          trivial.
        }
        subst.
        eauto.
      }
      apply walk2_inv in H0.
      destruct H0 as (v2, (Heq, (He,Hw))).
      inversion Heq; subst; clear Heq.
      unfold FGraph.Edge in He.
      assert (v2 = a). {
        apply walk2_inv_eq_fst in Hw.
        auto.
      }
      subst.
      apply IHw with (z:=b) in Hw; eauto using in_eq; clear IHw.
      destruct Hw as (w', (Heq, Hn)).
      inversion Heq; subst; clear Heq.
      exists ((a,b)::w').
      split; auto.
      unfold not; intros N.
      inversion N; subst; clear N. {
        inversion H0; subst; clear H0.
        assert (X: Reaches (FGraph.Edge es) x x). {
          auto using edge_to_reaches.
        }
        apply H in X.
        assumption.
      }
      destruct w' as [|(v1,v2)]. {
        inversion H0.
      }
      inversion H0; subst; clear H0. {
        inversion H1; subst; clear H1.
        assert (b = x). {
          apply walk2_inv_2 in Hw0.
          inversion Hw0; subst; clear Hw0.
          inversion H2; subst.
          apply linked_inv in H7.
          auto.
        }
        subst.
        assert (Hx: FGraph.Edge es (x, a) /\ FGraph.Edge es (a, x)). {
          inversion Hw0; subst.
          inversion H2; subst.
          inversion H5; subst.
          auto.
        }
        destruct Hx.
        assert (N: Reaches (FGraph.Edge es) x x). {
          eauto using reaches_trans, edge_to_reaches.
        }
        apply H in N.
        assumption.
      }
      apply walk2_inv_2 in Hw0.
      assert (He1 : FGraph.Edge es (a,b)). {
        inversion Hw0.
        inversion H3.
        auto.
      }
      assert (v1 = b). {
        inversion Hw0.
        inversion H3; subst.
        apply linked_inv in H11.
        auto.
      }
      subst.
      apply walk2_inv_2 in Hw0.
      destruct w'. {
        inversion H1.
      }
      apply walk2_inv in Hw0.
      destruct Hw0 as (v3, (Heq, (He', Hw))).
      inversion Heq; subst; clear Heq.
      assert (R: Reaches (FGraph.Edge es) v3 y) by eauto using reaches_def.
      apply walk2_split with (a0:=x) (b0:=a) in Hw; auto.
      apply edge_to_reaches in He1.
      apply edge_to_reaches in He'.
      apply edge_to_reaches in He.
      destruct Hw as [?|[?|(?,(?,(Heq,(Hw1,Hw2))))]].
      + subst.
        assert (N: Reaches (FGraph.Edge es) a a). {
          eauto using reaches_trans.
        }
        apply H in N.
        contradiction.
      + subst.
        assert (N: Reaches (FGraph.Edge es) y y). {
          eauto using reaches_trans.
        }
        apply H in N.
        contradiction.
      + destruct x0; subst; simpl in *. {
          apply walk2_nil_inv in Hw1.
          contradiction.
        }
        inversion Heq; subst; clear Heq.
        apply reaches_def in Hw1.
        apply reaches_def in Hw2.
        assert (N: Reaches (FGraph.Edge es) x x). {
          eauto using reaches_trans.
        }
        apply H in N.
        contradiction.
    }
  Admitted.

  Let fdag_walk2_inv_1 {A}:
    forall (x:A) y w z es,
    DAG (FGraph.Edge es) ->
    Walk2 (FGraph.Edge es) x y w ->
    List.In (z, y) w ->
    exists w', w = w' ++ ((z,y)::nil) /\ ~ List.In (z,y) w'.
  Proof.
  Admitted.

  Let fdag_walk2_inv_2 {A}:
    forall es x (y:A) wa wb e,
    DAG (FGraph.Edge es) ->
    Walk2 (FGraph.Edge es) x y (wa ++ e :: wb)  ->
    ~ List.In e wa /\ ~ List.In e wb.
  Proof.
  Admitted.

  Let reaches_inv_cons_0 {A} (eq_dec: forall (x y:A), { x = y } + { x <> y }):
    forall x n2 es w (y:A),
    DAG (FGraph.Edge ((x, n2) :: es)) ->
    Walk2 (FGraph.Edge ((x, n2) :: es)) x y w ->
    List.In (x, n2) w ->
    n2 = y \/ (n2 <> y /\ Reaches (FGraph.Edge es) n2 y).
  Proof.
    intros.
    destruct (eq_dec n2 y). {
      auto.
    }
    right; split; auto.
    assert (Hw :=H0).
    apply fdag_walk2_inv_0 with (z:=n2) in H0; auto; clear H1.
    destruct H0 as (w', (?, Hn)); subst.
    destruct w' as [|(a,b)]. {
      apply walk2_inv_eq_snd in Hw.
      contradiction.
    }
    apply walk2_inv in Hw.
    destruct Hw as (v2, (Heq, (_,Hw))).
    inversion Heq; subst; clear Heq.
    assert (v2=a). {
      apply walk2_inv_eq_fst in Hw.
      auto.
    }
    subst.
    apply FGraph.walk2_inv_not_in_walk in Hw; auto.
    eauto using reaches_def.
  Qed.

  Let reaches_inv_cons_1 {A} (eq_dec: forall (x y:A), { x = y } + { x <> y }):
    forall n1 y es w (x:A),
    DAG (FGraph.Edge ((n1, y) :: es)) ->
    List.In (n1, y) w ->
    Walk2 (FGraph.Edge ((n1, y) :: es)) x y w ->
    n1 = x \/ Reaches (FGraph.Edge es) x n1.
  Proof.
    intros.
    destruct (eq_dec n1 x). {
      auto.
    }
    right.
    assert (Hw :=H1).
    apply fdag_walk2_inv_1 with (z:=n1) in H1; auto.
    destruct H1 as (w', (?, Hn)).
    subst.
    destruct w' as [|(a,b)]. {
      simpl in *.
      apply walk2_inv_eq_fst in Hw.
      contradiction.
    }
    assert (a = x). {
      apply walk2_inv_eq_fst in Hw.
      auto.
    }
    subst.
    apply walk2_split_app in Hw.
    destruct Hw as (Hw, _).
    apply FGraph.walk2_inv_not_in_walk in Hw; eauto using reaches_def.
  Qed.

  Let reaches_inv_cons_2 {A} (eq_dec: forall (x y:A), { x = y } + { x <> y }):
    forall n1 n2 es (x:A) y wa wb,
    DAG (FGraph.Edge ((n1, n2) :: es)) ->
    Walk2 (FGraph.Edge ((n1, n2) :: es)) x n1 wa ->
    Walk2 (FGraph.Edge ((n1, n2) :: es)) n2 y wb ->
    Walk2 (FGraph.Edge ((n1, n2) :: es)) x y (wa ++ (n1, n2) :: wb) ->
    Reaches (FGraph.Edge es) x n1 /\ Reaches (FGraph.Edge es) n2 y.
  Proof.
    intros.
    assert (Hw:=H2).
    apply fdag_walk2_inv_2 in H2; auto.
    destruct H2 as (Hn1, Hn2).
    apply FGraph.walk2_inv_not_in_walk in H0; eauto using reaches_def.
    apply FGraph.walk2_inv_not_in_walk in H1; eauto using reaches_def.
  Qed.

  Let reaches_inv_cons {A} (eq_dec: forall (x y:A), { x = y } + { x <> y }):
    forall  es n1 n2 (x:A) y w,
    DAG (FGraph.Edge ((n1,n2)::es)) ->
    Walk2 (FGraph.Edge ((n1,n2)::es)) x y w ->
    List.In (n1,n2) w ->
    (n2 = y /\ (n1 = x \/ Reaches (FGraph.Edge es) x n1)) \/
    (n2 <> y /\ Reaches (FGraph.Edge es) n2 y) \/
    (Reaches (FGraph.Edge es) x n1 /\ Reaches (FGraph.Edge es) n2 y).
  Proof.
    intros.
    assert (Hw := H0).
    apply walk2_split with (a:=n1) (b:=n2) in H0; auto.
    destruct H0 as [?|[?|(wa, (wb, (He, (Hw1, Hw2))))]]; subst.
    + apply reaches_inv_cons_0 in Hw; auto.
      destruct Hw as [?|(?,Hr)]; subst; auto.
    + left.
      split; auto.
      apply reaches_inv_cons_1 in Hw; auto.
    + subst.
      apply reaches_inv_cons_2 in Hw; auto.
  Qed.

  Lemma hb_inv_cons:
    forall x y n1 n2 t es,
    DAG (FGraph.Edge (cg_edges ({| e_t:=t; e_edge:=(n1, n2) |}::es))) ->
    HB ({| e_t:=t; e_edge:=(n1, n2) |}::es) x y ->
    HB es x y \/
    (n2 = y /\ (n1 = x \/ HB es x n1)) \/
    (n2 <> y /\ HB es n2 y) \/
    (HB es x n1 /\ HB es n2 y).
  Proof.
    intros.
    repeat rewrite hb_fgraph_spec in *.
    simpl in H0.
    inversion H0; clear H0.
    destruct (List.in_dec (Pair.pair_eq_dec node_eq_dec) (n1,n2) w). {
      right.
      eauto using reaches_inv_cons, node_eq_dec.
    }
    apply FGraph.walk2_inv_not_in_walk in H1; eauto using reaches_def.
  Qed.

End DAG.

Module T.
  Require Trace.

  Definition op_to_cg (o:Trace.op) : op :=
  match o with
  | Trace.CONTINUE => CONTINUE
  | Trace.ALLOC _ _ => CONTINUE
  | Trace.WRITE _ _ => CONTINUE
  | Trace.READ _ _ => CONTINUE
  | Trace.FUTURE x _ => FORK x
  | Trace.FORCE x _ => JOIN x
  end.

  Definition event_to_cg (e:Trace.event) :=
  let (x,o) := e in (x, op_to_cg o).

  Notation TReduces cg e cg' := (Reduces cg (event_to_cg e) cg').
End T.