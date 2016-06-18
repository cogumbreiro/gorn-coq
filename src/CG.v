Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Lists.ListSet.
Require Import Aniceto.ListSet.
Require Import Aniceto.Graphs.Graph.

Require Import HJ.Tid.
Require Import HJ.Mid.
Require Import HJ.Cid.
Require Import HJ.Var.
Require Import HJ.Dep.
Require Import Node.

(* ----- end of boiler-plate code ---- *)

Set Implicit Arguments.

Require Import Aniceto.Graphs.DAG.
Require Import Coq.Relations.Relation_Operators.
Require Aniceto.Graphs.Graph.

Require Import Coq.Structures.OrderedTypeEx.

Section Trace.
  Inductive op_type := FORK | JOIN | CONTINUE.

  Structure op := {
    op_t: op_type;
    op_src: tid;
    op_dst: tid
  }.

  Definition trace := list op.    

End Trace.

Module Nodes.
Section Nodes.

  Structure node_ids := {
    cg_ids : MT.t (list nat);
    cg_last_id : nat
  }.

  Definition make (x:tid) : node_ids :=
  {|
    cg_ids :=  MT.add x (0 :: nil) (@MT.empty (list nat)) ;
    cg_last_id := 0
   |}.

  (** Looks up the latest id of a given task. *)

  Inductive MapsTo (x:tid) (n:nat) (ns:node_ids) : Prop :=
  | maps_to_def:
    forall l,
    MT.MapsTo x (n::l) (cg_ids ns) ->
    MapsTo x n ns.

  (** If this property holds then x was assigned to this id
    at one point in time. *)

  Inductive Contains (n:node) (ids:MT.t (list nat)) : Prop :=
  | contains_def:
    forall l,
    MT.MapsTo (n_task n) l ids ->
    List.In (n_id n) l ->
    Contains n ids.

  Lemma contains_add_1:
    forall n x l ids,
    x = n_task n ->
    List.In (n_id n) l ->
    Contains n (MT.add x l ids).
  Proof.
    eauto using contains_def, MT.add_1.
  Qed.

  Lemma contains_add_2:
    forall n x l ids,
    x <> n_task n ->
    Contains n ids ->
    Contains n (MT.add x l ids).
  Proof.
    intros.
    inversion H0.
    eauto using contains_def, MT.add_2.
  Qed.

  Lemma contains_add_3:
    forall n x l ids,
    x <> n_task n ->
    Contains n (MT.add x l ids) ->
    Contains n ids.
  Proof.
    intros.
    inversion H0.
    eauto using contains_def, MT.add_3.
  Qed.

  Lemma contains_add_iff:
    forall n x l ids,
    Contains n (MT.add x l ids) <->
    x = n_task n /\ List.In (n_id n) l
    \/
    x <> n_task n /\ Contains n ids.
  Proof.
    split; intros. {
      inversion H.
      apply MT_Facts.add_mapsto_iff in H0.
      destruct H0 as [(?,?)|(?,?)]; subst.
      - intuition.
      - eauto using contains_def.
    }
    destruct H as [(?,?)|(?,?)]. {
      auto using contains_add_1.
    }
    auto using contains_add_2.
  Qed.

  Inductive In (x:tid) ns : Prop :=
  | in_def:
    forall n,
    MapsTo x n ns ->
    In x ns.

  Lemma contains_to_in:
    forall x ns,
    Contains x (cg_ids ns) ->
    In (n_task x) ns.
  Proof.
    intros.
    inversion H.
    destruct l. {
      inversion H1.
    }
    eauto using in_def, maps_to_def.
  Qed.

  Let do_fork x l y ns :=
  {|
    cg_ids :=
      (MT.add x (S (cg_last_id ns) :: l))
      (MT.add y (S (S (cg_last_id ns)):: nil) (cg_ids ns));
    cg_last_id := S (S (cg_last_id ns))
  |}.

  Let do_continue x l ns :=
  {|
    cg_ids := MT.add x (S (cg_last_id ns) :: l) (cg_ids ns);
    cg_last_id := S (cg_last_id ns)
  |}.

  Definition cg_eval_nodes o (ns:node_ids) :=
  let t := op_t o in
  let x := op_src o in
  let y := op_dst o in
  let handle := match t with
  | FORK => do_fork
  | _ => fun x l y => do_continue x l
  end in
  match MT.find x (cg_ids ns)  with
  | Some l => handle x l y ns
  | _ =>  ns
  end.

  (** Reduces vertices *)

  Inductive Reduces (ns:node_ids): op -> node_ids -> Prop :=
  | reduces_fork:
    forall a b n l,
    MT.MapsTo a (n::l) (cg_ids ns) ->
    ~ In b ns ->
    Reduces ns {|op_t:=FORK;op_src:=a;op_dst:=b|} (do_fork a (n::l) b ns)
  | reduces_join:
    forall a b n l,
    MT.MapsTo a (n::l) (cg_ids ns) ->
    In b ns ->
    a <> b ->
    Reduces ns {|op_t:=JOIN;op_src:=a;op_dst:=b|} (do_continue a (n::l) ns)
  | reduces_continue:
    forall a n l,
    MT.MapsTo a (n::l) (cg_ids ns) ->
    Reduces ns {|op_t:=CONTINUE;op_src:=a;op_dst:=a|} (do_continue a (n::l) ns).

  (** Cleaned up semantics. *)

  Inductive Pre (ns:node_ids): op -> Prop :=
  | pre_fork:
    forall a b,
    In a ns ->
    ~ In b ns ->
    Pre ns {| op_t := FORK; op_src := a; op_dst := b |}
  | pre_join:
    forall a b,
    In a ns ->
    In b ns ->
    a <> b ->
    Pre ns {| op_t := JOIN; op_src := a; op_dst := b |}
  | pre_continue:
    forall a,
    In a ns ->
    Pre ns {| op_t := CONTINUE; op_src := a; op_dst := a |}.

  Inductive Eval (ns:node_ids) o: node_ids -> Prop :=
  | eval_step:
    Pre ns o ->
    Eval ns o (cg_eval_nodes o ns).

  Let in_to_in_ids:
    forall a ns,
    In a ns ->
    MT.In a (cg_ids ns).
  Proof.
    intros.
    destruct H as (n, (l, mt)).
    eauto using MT_Extra.mapsto_to_in.
  Qed.

  Lemma eval_to_reduces:
    forall ns o ns',
    Eval ns o ns' ->
    Reduces ns o ns'.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0;
    unfold cg_eval_nodes;
      destruct (MT_Extra.find_rw a (cg_ids ns)) as [(R,N)|(v,(R,X))];
      simpl in *;
      rewrite R in *; clear R; try (contradiction N; auto);
      destruct H as (n,(l, mt));
      assert (v=n :: l) by eauto using MT_Facts.MapsTo_fun; subst; clear X;
      eauto using reduces_fork, reduces_continue, reduces_join.
  Qed.

  Lemma reduces_to_eval:
    forall ns o ns',
    Reduces ns o ns' ->
    Eval ns o ns'.
  Proof.
    intros.
    assert (Hx: Pre ns o /\ ns' = cg_eval_nodes o ns). {
      split.
      - inversion H; subst; clear H;
        assert (In a ns) by eauto using in_def, maps_to_def;
        auto using pre_fork, pre_join, pre_continue.
      - inversion H; subst; clear H;
        remember {| op_t := _; op_src := a; op_dst := _ |} as o;
        unfold cg_eval_nodes;
          destruct (MT_Extra.find_rw (op_src o) (cg_ids ns)) as [(R,N)|(v,(R,X))];
          rewrite R in *; clear R;
          try (subst; contradiction N; eauto using MT_Extra.mapsto_to_in);
          subst; assert (v=n :: l) by eauto using MT_Facts.MapsTo_fun; subst; clear X;
          trivial.
    }
    destruct Hx as (?,R).
    rewrite R.
    auto using eval_step.
  Qed.

  Lemma eval_iff:
    forall ns o ns',
    Eval ns o ns' <-> Reduces ns o ns'.
  Proof.
    split; eauto using reduces_to_eval, eval_to_reduces.
  Qed.

  Lemma in_make:
    forall t,
    In t (make t).
  Proof.
    unfold make.
    eauto using in_def, maps_to_def, MT.add_1.
  Qed.

  Lemma contains_preservation:
    forall vs o vs' n,
    Reduces vs o vs' ->
    Contains n (cg_ids vs) ->
    Contains n (cg_ids vs').
  Proof.
    intros.
    inversion H; subst; clear H; simpl in *.
    - destruct (tid_eq_dec (n_task n) a). {
        subst.
        destruct H0.
        assert (l0 = n0:: l) by eauto using MT_Facts.MapsTo_fun; subst.
        eauto using MT.add_1, contains_def, List.in_cons.
      }
      destruct (tid_eq_dec (n_task n) b). {
        subst.
        contradiction H2.
        auto using contains_to_in.
      }
      eauto using contains_add_2.
    - destruct (tid_eq_dec (n_task n) a). {
        subst.
        destruct H0.
        assert (l0 = n0:: l) by eauto using MT_Facts.MapsTo_fun; subst.
        eauto using MT.add_1, contains_def, List.in_cons.
      }
      auto using contains_add_2.
    - destruct (tid_eq_dec (n_task n) a). {
        subst.
        destruct H0.
        assert (l0 = n0:: l) by eauto using MT_Facts.MapsTo_fun; subst.
        eauto using MT.add_1, contains_def, List.in_cons.
      }
      auto using contains_add_2.
  Qed.

End Nodes.
End Nodes.

Section Edges.

  Import Nodes.

  Notation edge := (node * node) % type.

  (** A tee consists of two edges:
    an intra-edge that represents the continue edge, and
    an inter-edge that represents either the spawn or the async edge.
    *)

  Structure intra := {
    i_task: tid;
    i_prev_id: nat;
    i_curr_id: nat
  }.

  Definition i_prev (i:intra) := {| n_task := i_task i; n_id := i_prev_id i |}.

  Definition i_curr (i:intra) := {| n_task := i_task i; n_id := i_curr_id i |}.

  Structure tee := {
    t_intra: intra;
    t_inter: node
  }.

  (**
    When creating a tee, the inter edge is the only thing
    that changes depending on the type of the node.
    *)

  Structure cg_edge := {
    e_t: op_type;
    e_edge: (node * node)
  }.

  Definition c_edge (i:intra) :=
  {| e_t := CONTINUE; e_edge:= (i_prev i, i_curr i) |}.

  Definition f_edge (t:tee) :=
  {| e_t := FORK; e_edge := (i_prev (t_intra t), t_inter t) |}.

  Definition j_edge (t:tee) :=
  {| e_t := JOIN; e_edge := (t_inter t, i_curr (t_intra t)) |}.

  Definition computation_graph := (node_ids * list cg_edge) % type.

  Let do_inter f x nx_prev nx_curr y ny es :=
    let intra := {|i_task:=x; i_prev_id := nx_prev; i_curr_id := nx_curr |} in
    c_edge intra :: f {|t_intra:=intra; t_inter:={|n_task:=y;n_id:=ny|} |} :: es.

  Inductive Edge : computation_graph -> op_type -> (node * node) -> Prop :=
  | edge_def:
    forall vs es e t,
    List.In e es ->
    Edge (vs, es) t (e_edge e).

  Inductive HB_Edge cg e : Prop :=
  | hb_edge_def:
    forall t,
    Edge cg t e ->
    HB_Edge cg e.

  Lemma edge_eq:
    forall vs es t x y,
     List.In {| e_t := t; e_edge := (x,y) |} es ->
     Edge (vs, es) t (x, y).
  Proof.
    intros.
    remember {| e_t := t; e_edge := (x, y) |} as e.
    assert (R:(x, y) = e_edge e) by (subst; auto).
    rewrite R.
    auto using edge_def.
  Qed.

  Inductive TaskEdge cg t : (tid * tid) -> Prop :=
  | task_edge_def:
    forall x y,
    Edge cg t (x, y) ->
    TaskEdge cg t (n_task x, n_task y).

  Lemma task_edge_eq:
    forall vs es t x y nx ny,
     List.In {| e_t := t; e_edge := ({| n_task:=x; n_id := nx |}, {| n_task := y; n_id := ny |}) |} es ->
     TaskEdge (vs, es) t (x, y).
  Proof.
    intros.
    remember {| n_task := x; n_id := nx |} as a.
    remember {| n_task := y; n_id := ny |} as b.
    assert (Edge (vs,es) t (a, b)) by auto using edge_eq.
    assert (R1: x = n_task a) by (subst; trivial); rewrite R1; clear R1.
    assert (R2: y = n_task b) by (subst; trivial); rewrite R2.
    auto using task_edge_def.
  Qed.

  Inductive Live cg x : Prop :=
  | live_def:
    (forall y, ~ TaskEdge cg JOIN (x, y)) ->
    Live cg x.

  Inductive Reduces: computation_graph -> op -> computation_graph -> Prop :=
  | reduces_fork:
    forall (vs:node_ids) (es:list cg_edge) vs' x y nx_curr nx_prev ny lx ly o,
    Live (vs,es) x ->
    o = {| op_t := FORK; op_src:=x; op_dst:=y|} ->
    Nodes.Reduces vs o vs' ->
    MT.MapsTo x (nx_curr::nx_prev::lx) (cg_ids vs') ->
    MT.MapsTo y (ny::ly) (cg_ids vs') ->
    Reduces (vs,es) o (vs', do_inter f_edge x nx_prev nx_curr y ny es)
  | reduces_join:
    forall (vs:node_ids) (es:list cg_edge) vs' x y nx_prev nx_curr ny lx ly o,
    Live (vs,es) x ->
    o = {| op_t := JOIN; op_src:=x; op_dst:=y|} ->
    Nodes.Reduces vs o vs' ->
    MT.MapsTo x (nx_curr::nx_prev::lx) (cg_ids vs') ->
    MT.MapsTo y (ny::ly) (cg_ids vs') ->
    Reduces (vs,es) o (vs', do_inter j_edge x nx_prev nx_curr y ny es)
  | reduces_continue:
    forall (vs:node_ids) (es:list cg_edge) vs' x nx_prev nx_curr lx o,
    Live (vs,es) x ->
    o = {| op_t := CONTINUE; op_src:=x; op_dst:=x|} ->
    Nodes.Reduces vs o vs' ->
    MT.MapsTo x (nx_curr::nx_prev::lx) (cg_ids vs') ->
    Reduces (vs,es) o (vs', c_edge (Build_intra x nx_prev nx_curr) :: es).

  Definition make_cg x : computation_graph := (make x, nil).

  Inductive CG (x:tid): trace -> computation_graph -> Prop :=
  | cg_nil:
    CG x nil (make_cg x)
  | cg_cons:
    forall cg o t cg',
    CG x t cg ->
    Reduces cg o cg' ->
    CG x (o::t) cg'.

  Definition cg_nodes (cg:computation_graph) := fst cg.

  Definition cg_edges (cg:computation_graph) := map e_edge (snd cg).

  Definition cg_lookup x cg :=
  match MT.find x (cg_ids (cg_nodes cg)) with
  | Some (n::_) => Some {| n_task := x; n_id := n |}
  | _ => None
  end.

  (** Any node in the CG graph must be in the nodes. *)

  Definition WellFormedEdges (cg:computation_graph) :=
  forall n1 n2,
  FGraph.Edge (cg_edges cg) (n1, n2) ->
  Contains n1 (cg_ids (cg_nodes cg)) /\ Contains n2 (cg_ids (cg_nodes cg)).

  Let wf_edges_reduces_fork:
    forall x vs vs' es nx_prev nx_curr y ny lx ly,
    Nodes.Reduces vs {| op_t := FORK; op_src := x; op_dst := y |} vs' ->
    MT.MapsTo x (nx_curr :: nx_prev :: lx) (cg_ids vs') ->
    MT.MapsTo y (ny :: ly) (cg_ids vs') ->
    WellFormedEdges (vs, es) ->
    WellFormedEdges (vs', do_inter f_edge x nx_prev nx_curr y ny es).
  Proof.
    intros.
    unfold WellFormedEdges.
    intros.
    split;
      destruct H3 as [E|[E|?]]; simpl in *;
      try (
        inversion E; subst; clear E;
        unfold i_prev; simpl;
        eauto using contains_def, List.in_eq, List.in_cons
      );
      apply H2 in H3;
      simpl in *;
      destruct H3; eauto using contains_preservation.
  Qed.

  Let wf_edges_join:
    forall vs vs' x y ny ly es nx_curr nx_prev lx,
    Nodes.Reduces vs {| op_t := JOIN; op_src := x; op_dst := y |} vs' ->
    MT.MapsTo x (nx_curr :: nx_prev :: lx) (cg_ids vs') ->
    MT.MapsTo y (ny :: ly) (cg_ids vs') ->
    WellFormedEdges (vs, es) ->
    WellFormedEdges (vs', do_inter j_edge x nx_prev nx_curr y ny es).
  Proof.
    intros.
    unfold WellFormedEdges.
    intros.
    split;
      destruct H3 as [E|[E|?]]; simpl in *;
      try (
        inversion E; subst; clear E;
        unfold i_prev; simpl;
        eauto using contains_def, List.in_eq, List.in_cons
      );
      apply H2 in H3;
      simpl in *;
      destruct H3; eauto using contains_preservation.
  Qed.

  Let wf_edges_continue:
    forall x nx_curr nx_prev lx vs' vs es,
    Nodes.Reduces vs {| op_t := CONTINUE; op_src := x; op_dst := x |} vs' ->
    MT.MapsTo x (nx_curr :: nx_prev :: lx) (cg_ids vs') ->
    WellFormedEdges (vs, es) ->
    WellFormedEdges (vs', c_edge {| i_task := x; i_prev_id := nx_prev; i_curr_id := nx_curr |} :: es).
  Proof.
    intros.
    unfold WellFormedEdges.
    intros.
    split;
      destruct H2 as [E|?]; simpl in *;
      try (
        inversion E; subst; clear E;
        unfold i_prev; simpl;
        eauto using contains_def, List.in_eq, List.in_cons
      );
      apply H1 in H2;
      simpl in *;
      destruct H2; eauto using contains_preservation.
  Qed.

  Lemma wf_edges_reduces:
    forall cg o cg',
    WellFormedEdges cg ->
    Reduces cg o cg' ->
    WellFormedEdges cg'.
  Proof.
    intros.
    inversion H0; subst; clear H0; subst; simpl in *; eauto.
  Qed.

  Let WellFormedNodes (cg:computation_graph) :=
  forall n,
  Graph.In (FGraph.Edge (cg_edges cg)) n ->
  Contains n (cg_ids (cg_nodes cg)).

  Let well_formed_nodes_to_edges:
    forall cg,
    WellFormedNodes cg ->
    WellFormedEdges cg.
  Proof.
    unfold WellFormedNodes, WellFormedEdges.
    eauto 6 using in_left, in_right.
  Qed.

  Let well_formed_edges_to_nodes:
    forall cg,
    WellFormedEdges cg ->
    WellFormedNodes cg.
  Proof.
    unfold WellFormedNodes, WellFormedEdges.
    intros.
    destruct H0 as ((v1,v2),(Hx,[?|?])); simpl in *; subst;
      apply H in Hx;
      destruct Hx;
      auto.
  Qed.

  Let well_formed_edges_iff:
    forall cg,
    WellFormedNodes cg <->
    WellFormedEdges cg.
  Proof.
    split; eauto.
  Qed.

  Let wf_nodes_preservation:
    forall cg o cg',
    WellFormedNodes cg ->
    Reduces cg o cg' ->
    WellFormedNodes cg'.
  Proof.
    intros.
    rewrite well_formed_edges_iff in *; auto.
    eauto using wf_edges_reduces.
  Qed.

  Let cg_edges_make:
    forall x,
    cg_edges (make_cg x) = nil.
  Proof.
    intros.
    unfold cg_edges, make_cg.
    auto.
  Qed.

  Let wf_nodes_make:
    forall x,
    WellFormedNodes (make_cg x).
  Proof.
    unfold WellFormedNodes.
    intros.
    rewrite cg_edges_make in *.
    simpl in *.
    destruct H as (e, (Hx, Hy)).
    inversion Hx.
  Qed.

  Let wf_nodes_0:
    forall x t cg,
    CG x t cg ->
    WellFormedNodes cg.
  Proof.
    induction t; intros. {
      inversion H.
      auto using wf_nodes_make.
    }
    inversion H; subst.
    eauto.
  Qed.

  Lemma node_in_ids:
    forall x t cg n,
    CG x t cg ->
    Graph.In (FGraph.Edge (cg_edges cg)) n ->
    Contains n (cg_ids (cg_nodes cg)).
  Proof.
    intros.
    apply wf_nodes_0 in H.
    unfold WellFormedNodes in *.
    auto.
  Qed.

  Lemma node_in_cg:
    forall x t cg n,
    CG x t cg ->
    Graph.In (FGraph.Edge (cg_edges cg)) n ->
    In (n_task n) (cg_nodes cg).
  Proof.
    intros.
    eapply node_in_ids in H0; eauto
    using contains_to_in.
  Qed.

End Edges.

Section Defs.

  Lemma in_make:
    forall t,
    Nodes.In t (cg_nodes (make_cg t)).
  Proof.
    intros.
    simpl.
    auto using Nodes.in_make.
  Qed.

  Inductive Prec : (node * node) -> cg_edge -> Prop :=
  | prec_def:
    forall e,
    Prec (e_edge e) e.

  Variable cg: computation_graph.

  Let HB_Edge_alt e := List.Exists (Prec e) (snd cg).

  Definition HB := Reaches (HB_Edge cg).

  Definition MHP x y : Prop := ~ HB x y /\ ~ HB y x.

  Let in_edges_to_tees:
    forall e,
    List.In e (cg_edges cg) ->
    exists x, List.In x (snd cg) /\ Prec e x.
  Proof.
    unfold cg_edges.
    intros.
    rewrite in_map_iff in *.
    destruct H as (x, (Hi, He)).
    exists x; split; auto.
    subst; eauto using prec_def.
  Qed.

  Let in_tees_to_edges:
    forall x e,
    List.In x (snd cg) ->
    Prec e x ->
    List.In e (cg_edges cg).
  Proof.
    unfold cg_edges.
    intros.
    rewrite in_map_iff in *.
    inversion H0;
    subst;
    eauto.
  Qed.

  Lemma hb_edge_spec:
    forall e,
    HB_Edge cg e <-> List.In e (cg_edges cg).
  Proof.
    split; intros.
    - destruct H.
      inversion H; subst; clear H.
      unfold cg_edges.
      simpl.
      auto using in_map.
    - unfold cg_edges in *; rewrite in_map_iff in *.
      destruct H as (?,(?,?)); subst.
      destruct cg.
      simpl in *.
      destruct x as (t, x). 
      apply hb_edge_def with (t:=t); eauto using edge_def.
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

End Defs.

Section HB.

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
    ~ HB (make_cg a) x y.
  Proof.
    intros.
    intuition.
    inversion H.
    inversion H0; subst.
    destruct w. {
      apply starts_with_inv_nil in H1; contradiction.
    }
    assert (HB_Edge (make_cg a) p). {
      eapply walk_to_edge; eauto using List.in_eq.
    }
    rewrite hb_edge_spec in H4.
    simpl in H4.
    contradiction.
  Qed.

End HB.

Module WellFormed.
  Inductive Forks : trace -> tid -> list tid -> Prop :=
  | forks_nil:
    forall x,
    Forks nil x (x::nil)
  | forks_cons_fork:
    forall ts l z x y,
    (* x -> y *)
    List.In x l ->
    ~ List.In y l ->
    Forks ts z l ->
    Forks ({|op_t:=FORK; op_src:=x; op_dst:=y |}::ts) z (y::l)
  | forks_cons_join:
    forall ts l x y z,
    List.In x l ->
    List.In y l ->
    Forks ts z l ->
    Forks ({|op_t:=JOIN; op_src:=x; op_dst:=y |}::ts) z l.

  Inductive Joins: trace -> list tid -> Prop :=
  | joins_nil:
    Joins nil nil
  | joins_cons_fork:
    forall ts l x y,
    ~ List.In x l ->
    ~ List.In y l ->
    Joins ts l ->
    Joins ({|op_t:=FORK; op_src:=x; op_dst:=y |}::ts) l
  | joins_cons_join:
    forall ts l x y,
    ~ List.In x l ->
    Joins ts l ->
    Joins ({|op_t:=JOIN; op_src:=x; op_dst:=y |}::ts) l.

  Inductive Running : trace -> tid -> list tid -> Prop :=
  | running_nil:
    forall x,
    Running nil x (x::nil)
  | running_cons_fork:
    forall ts l x y z,
    (* x -> y *)
    List.In x l ->
    ~ List.In y l ->
    Running ts z l ->
    Running ({|op_t:=FORK; op_src:=x; op_dst:=y |}::ts) z (y::l)
  | running_cons_join:
    forall ts l x y z,
    List.In x l ->
    Running ts z l ->
    Running ({|op_t:=JOIN; op_src:=x; op_dst:=y |}::ts) z (remove TID.eq_dec y l).

  Section Defs.

  Require Import Aniceto.List.

  Lemma forks_no_dup:
    forall ts x l,
    Forks ts x l  ->
    NoDup l.
  Proof.
    induction ts; intros. {
      inversion H.
      subst.
      auto using NoDup_cons, NoDup_nil.
    }
    inversion H; subst; clear H; 
    eauto using NoDup_cons.
  Qed.

  Lemma running_incl_forked:
    forall ts ks rs x,
    Running ts x rs ->
    Forks ts x ks ->
    incl rs ks.
  Proof.
    induction ts; intros. {
      inversion H.
      inversion H0.
      auto using incl_refl.
    }
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    - eauto using incl_cons_cons.
    - inversion H0; subst.
      eauto using remove_incl, incl_tran.
  Qed.

  Lemma in_running_in_fork:
    forall ts vs rs x y,
    Running ts x rs ->
    Forks ts x vs ->
    List.In y rs ->
    List.In y vs.
  Proof.
    intros.
    assert (incl rs vs) by eauto using running_incl_forked.
    auto.
  Qed.

  Lemma running_not_in_joins:
    forall ts js rs x,
    Running ts x rs ->
    Joins ts js ->
    forall y, List.In y rs -> ~ List.In y js.
  Proof.
    induction ts; intros. {
      inversion H; inversion H0;
      intuition.
    }
    destruct a as (a,src,dst).
    destruct a; inversion H; inversion H0; subst; clear H H0.
    + destruct H1; subst; eauto.
    + eauto using remove_in.
  Qed.

  Lemma joins_not_in_running:
    forall ts js rs x,
    Running ts x rs ->
    Joins ts js ->
    forall y, List.In y js -> ~ List.In y rs.
  Proof.
    induction ts; intros. {
      inversion H; inversion H0; subst.
      inversion H1.
    }
    destruct a as (a,src,dst).
    destruct a; inversion H; inversion H0; subst; clear H H0.
    + unfold not; intros Hx.
      destruct Hx.
      * subst; contradiction.
      * assert (Hx := IHts _ _ _ H9 H16 _ H1); contradiction.
    + unfold not; intros Hx.
      apply remove_in in Hx.
      assert (Hy := IHts _ _ _ H8 H14 _ H1).
      contradiction.
  Qed.

  Lemma running_no_dup:
    forall ts rs x,
    Running ts x rs ->
    NoDup rs.
  Proof.
    induction ts; intros; inversion H; subst.
    - auto using no_dup_cons_nil.
    - eauto using NoDup_cons.
    - eauto using no_dup_remove.
  Qed.
(*
  Let forks_in_cg:
    forall l x t cg ts,
    CG x l cg ->
    Forks l x ts ->
    List.In t ts ->
    Nodes.In t (cg_nodes cg).
  Proof.
    induction l; intros. {
      inversion H0; subst.
      destruct H1. {
        subst.
        inversion H; subst.
        auto using Top.in_make.
      }
      inversion H1.
    }
    inversion H0; subst; clear H0.
    - destruct H1;
      inversion H; subst; clear H.
      + auto using in_fork_1.
      + eauto using in_fork_2.
    - inversion H; subst; clear H.
      eauto using in_join_2.
  Qed.
*)
(*
  (**
   Building a CG from a trace.
   *)
  Lemma cg_spec:
    forall x l ts,
    Forks l x ts ->
    CG x l (trace_to_cg x l).
  Proof.
    induction l; intros. {
      unfold trace_to_cg.
      simpl.
      auto using cg_nil.
    }
    destruct a as (t);
    try destruct t; simpl in *;
    inversion H; subst.
    - assert (op_src0 <> op_dst0). {
        intuition; subst; contradiction.
      }
      eauto using cg_cons_fork, forks_in_cg.
    - apply cg_cons_join; eauto using forks_in_cg.
  Qed.
*)
(*
  Lemma cg_n_task:
    forall x l cg t n,
    CG x l cg ->
    MT.MapsTo t n (cg_nodes cg) ->
    n_task n = t.
  Proof.
    induction l; intros. {
      inversion H.
      subst.
      unfold make_cg in *.
      simpl in *.
      rewrite MT_Facts.add_mapsto_iff in H0.
      destruct H0 as [(?,?)|(?,?)].
      + subst; auto.
      + rewrite MT_Facts.empty_mapsto_iff in H1; contradiction.
    }
    inversion H; simpl in *; subst.
    + rename a0 into a; rename cg0 into cg.
      assert (mt : exists na, MT.MapsTo a na (cg_nodes cg)). {
          unfold In in *.
          apply MT_Extra.in_to_mapsto in H4.
          assumption.
        }
      destruct mt as (na, mt).
      assert (n_task na = a) by eauto.
      destruct (tid_eq_dec t a); subst.
      * assert (Hx:=mt).
        apply maps_to_fork_1 with (b:=b) in Hx; auto.
        assert (n = next_intra (n_task na) (cg_last_id cg))
        by eauto using MT_Facts.MapsTo_fun;subst.
        unfold next_intra; auto.
      * destruct (tid_eq_dec t b). {
          subst.
          apply maps_to_fork_2 with (na:=na) in H0; auto.
          subst.
          auto.
        }
        apply maps_to_fork_3 with (x:=n_task na) (y:=b) (z:=t) (n:=n) (nx:=na) in H0; auto.
        eauto.
    + rename a0 into a; rename cg0 into cg.
      assert (mt : exists na, MT.MapsTo a na (cg_nodes cg)). {
        unfold In in *.
        apply MT_Extra.in_to_mapsto in H4.
        assumption.
      } destruct mt as (na, mta).
      assert (mtb : exists nb, MT.MapsTo b nb (cg_nodes cg)). {
        unfold In in *.
        apply MT_Extra.in_to_mapsto in H4.
        assumption.
      } destruct mtb as (nb, mtb).
      destruct (tid_eq_dec t a); subst. {
        assert (Hx := mta).
        apply maps_to_join_1 with (b:=b) in mta; auto. {
          assert (n = next_intra (n_task na) (cg_last_id cg))
          by eauto using MT_Facts.MapsTo_fun;subst.
          unfold next_intra.
          simpl.
          eauto.
        }
        eauto.
      }
      destruct (tid_eq_dec t b); subst. {
        apply maps_to_join_2 with (na:=na) (b:=b) (nb:=n) in H0; eauto.
      }
      apply maps_to_join_3 with (x:=a) (y:=b) (z:=t) (nx:=na) in H0; eauto.
  Qed.*)
(*
  Lemma maps_to_fork_1:
    forall x y n cg a l,
    CG a l cg ->
    MT.MapsTo x n (cg_nodes cg) ->
    MT.MapsTo x (next_intra x (cg_last_id cg)) (cg_nodes (cg_fork x y cg)).
  Proof.
    intros.
    assert (R: next_intra x (cg_last_id cg) = next_intra (n_task n) (cg_last_id cg)). {
      assert (R: n_task n = x) by
      eauto using cg_n_task.
      rewrite R.
      trivial.
    }
    rewrite R.
    eauto using maps_to_fork_1, cg_n_task.
  Qed.

  Lemma maps_to_fork_2:
    forall x y n cg a l,
    CG a l cg ->
    x <> y ->
    In x cg ->
    MT.MapsTo y n (cg_nodes (cg_fork x y cg)) ->
    n = fork_inter y (cg_last_id cg).
  Proof.
    unfold In; intros.
    apply MT_Extra.in_to_mapsto in H1.
    destruct H1.
    eauto using maps_to_fork_2, cg_n_task.
  Qed.

  Lemma maps_to_fork_3:
    forall x y z n cg l a,
    CG a l cg ->
    z <> x ->
    z <> y ->
    In x cg ->
    MT.MapsTo z n (cg_nodes (cg_fork x y cg)) ->
    MT.MapsTo z n (cg_nodes cg).
  Proof.
    unfold In; intros.
    apply MT_Extra.in_to_mapsto in H2.
    destruct H2 as  (nx, ?).
    apply maps_to_fork_3 with (x:=x) (y:=y) (nx:=nx); eauto using cg_n_task.
  Qed.

  Lemma maps_to_join_1:
    forall x y n cg a l,
    CG a l cg ->
    In y cg ->
    MT.MapsTo x n (cg_nodes cg) ->
    MT.MapsTo x (next_intra x (cg_last_id cg)) (cg_nodes (cg_join x y cg)).
  Proof.
    intros.
    assert (R: next_intra x (cg_last_id cg) = next_intra (n_task n) (cg_last_id cg)). {
      assert (R: n_task n = x) by
      eauto using cg_n_task.
      rewrite R.
      trivial.
    }
    rewrite R.
    eauto using maps_to_join_1, cg_n_task.
  Qed.

  Lemma maps_to_join_2:
    forall x y n cg a l,
    CG a l cg ->
    x <> y ->
    In x cg ->
    MT.MapsTo y n (cg_nodes (cg_join x y cg)) ->
    MT.MapsTo y n (cg_nodes cg).
  Proof.
    unfold In.
    intros.
    apply MT_Extra.in_to_mapsto in H1.
    destruct H1.
    eauto using maps_to_join_2, cg_n_task.
  Qed.

  Lemma maps_to_join_3:
    forall x y z n cg a l,
    CG a l cg ->
    z <> x ->
    z <> y ->
    In x cg ->
    MT.MapsTo z n (cg_nodes (cg_join x y cg)) ->
    MT.MapsTo z n (cg_nodes cg).  
  Proof.
    unfold In.
    intros.
    apply MT_Extra.in_to_mapsto in H2.
    destruct H2 as (nx,?).
    apply maps_to_join_3 with (x:=x) (y:=y) (nx:=nx); eauto using cg_n_task.
  Qed.

  (** If we get a tee from a CG, the intra nodes are referring to
   the same task. *)

  Lemma tee_continue:
    forall l x y v cg a,
    CG a l cg ->
    List.In v (cg_tees cg) ->
    intra v = (x, y) ->
    n_task x = n_task y.
  Proof.
    induction l; intros. {
      inversion H.
      subst.
      simpl in *.
      contradiction.
    }
    inversion H; subst; clear H;
    rename cg0 into cg; rename a1 into a.
    - unfold In in *.
      apply MT_Extra.in_to_mapsto in H5.
      destruct H5 as (n, mt).
      assert (R: cg_tees (cg_fork a b cg) = make_fork (cg_last_id cg) n b :: cg_tees cg)
      by auto using tee_fork_rw.
      rewrite R in *.
      destruct H0. {
        subst.
        inversion H1; subst.
        simpl.
        trivial.
      }
      eauto.
    - unfold In in *.
      apply MT_Extra.in_to_mapsto in H5.
      destruct H5 as (na, mta).
      apply MT_Extra.in_to_mapsto in H7.
      destruct H7 as (nb, mtb).
      assert (R: cg_tees (cg_join a b cg) = make_join (cg_last_id cg) na nb :: cg_tees cg)
      by auto using tee_join_rw.
      rewrite R in *.
      destruct H0. {
        subst; inversion H1.
        auto.
      }
      eauto.
  Qed.

  Let cg_last_id_rw_fork:
    forall cg a b,
    MT.In a (cg_nodes cg) ->
    cg_last_id (cg_fork a b cg) = S (S (cg_last_id cg)).
  Proof.
    intros.
    unfold cg_fork.
    destruct (tee_fork_dec a b cg) as [(?,(?,(R,(?,?))))|(?,?)].
    - unfold tee_last_id.
      rewrite R in *; subst.
      auto.
    - contradiction. 
  Qed.*)
(*
  Lemma cg_to_nodes:
    forall a l cg ns n,
    CG a l cg ->
    CGNodes.CGNodes a l ns n ->
    MT.MapsTo a {| n_task := a; n_id := n |} (cg_nodes cg) ->
    CGNodes.MapsTo a n ns.
  Proof.
    intros.
    
  Qed.
    
*)
(*
  Lemma cg_to_nodes:
    forall a l cg,
    CG a l cg ->
    exists ns, CGNodes.CGNodes a l ns (cg_last_id cg).
  Proof.
    induction l; intros. {
      inversion H.
      simpl in *.
      eauto using CGNodes.cg_nodes_nil.
    }
    inversion H; subst.
    - apply IHl in H2.
      destruct H2 as (ns, Hn).
      rewrite cg_last_id_rw_fork; auto.
      exists ((a1, S (cg_last_id cg0)) :: (b, S (S (cg_last_id cg0))) :: ns).
      apply CGNodes.cg_nodes_cons_fork with (cg_last_id cg0); auto.
  Qed.
*)
(*
  Let tee_fork_rw:
    forall x y cg cg',
    tee_fork x y cg' = tee_fork x y cg ->
    cg' = cg.
  Proof.
    intros.
    destruct (tee_fork_dec x y cg'), (tee_fork_dec x y cg).
    - destruct e as (t, (n, (mt, (R,?)))). 
      destruct e0 as (t', (n', (mt', (R',?)))). 
    remember (te
    unfold tee_fork.
    intros.
    destruct
  Qed.
*)
(*
  Let cg_fork_rw:
    forall x y cg cg',
    In x cg' ->
    x <> y ->
    In x cg ->
    cg_fork x y cg' = cg_fork x y cg ->
    cg' = cg.
  Proof.
    intros.
    unfold cg_fork in *.
    destruct (tee_fork_dec x y cg'), (tee_fork_dec x y cg).
    - destruct e as (?, (?, (R1,(?,?)))).
      destruct e0 as (?, (?, (R2,(?,?)))).
      rewrite R1 in *; rewrite R2 in *.
      subst.
      simpl in *.
  Qed.
  *)

(*
  Let cg_make_inv:

    cg_fork x y (make_cg a) = cg_fork x y cg ->
    cg = 
*)
(*
  Lemma fork_is_gt:
    forall vs es x,
    WellFormedEdges (vs, es) ->
    ~ Nodes.In (node_task x) vs ->
    forall y, ~ HB_Edge (vs, es) (x, y).
  Proof.
    intros.
    unfold HB_Edge.
    unfold not; intros.
    apply H in H1.
    destruct H1.
    contradiction H0.
    auto using Nodes.contains_to_in.
  Qed.
*)
  End Defs.

End WellFormed.
