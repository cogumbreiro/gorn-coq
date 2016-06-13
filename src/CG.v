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


(* ----- end of boiler-plate code ---- *)

Set Implicit Arguments.

Require Import Aniceto.Graphs.DAG.
Require Import Coq.Relations.Relation_Operators.
Require Aniceto.Graphs.Graph.

Require Import Coq.Structures.OrderedTypeEx.

Require Import Lang.

Module NAT_PAIR := PairOrderedType Nat_as_OT Nat_as_OT.


Section Node.
  Structure node := {
    node_task: tid;
    node_id: nat
  }.

  Definition zero_node t := {| node_task := t; node_id:= 0 |}.
End Node.

Section Trace.
  Inductive op_type := FORK | JOIN.

  Structure op := {
    op_t: op_type;
    op_src: tid;
    op_dst: tid
  }.

  Definition trace := list op.

End Trace.

Section Defs.

  (** DAG id order *)

  Definition dag_lt x y := node_id x < node_id y.

  Definition edge := (node * node) % type.

  Structure tee := {
    ntype: op_type;
    intra : edge;
    inter : edge
  }.

  Inductive Check : tee -> Prop :=
  | check_fork:
    forall x y dx last_id,
    dx < last_id ->
    x <> y ->
    Check
    {|
      ntype := FORK;
      intra :=
      (
        {| node_task := x; node_id := dx |},
        {| node_task := x; node_id := last_id |}
      );
      inter :=
      (
        {| node_task := x; node_id := dx |},
        {| node_task := y; node_id := S last_id |}
      )
    |}
  | check_join:
    forall x y dx last_id dy,
    dx < last_id ->
    dy < last_id ->
    x <> y ->
    Check
    {|
      ntype := JOIN;
      intra :=
      (
        {| node_task := x; node_id := dx |},
        {| node_task := x; node_id := last_id |}
      );
      inter :=
      (
        {| node_task := y; node_id := dy |},
        {| node_task := x; node_id := last_id |}
      )
    |}.

  (** Creates a future node *)

  Definition tee_last_id (t:tee) :=
  node_id (snd (inter t)).

  Definition next_intra x nid :=
  {| node_task := x; node_id := S nid |}.

  Definition fork_inter y nid :=
  {| node_task := y; node_id := S (S nid) |}.

  Definition mk_fork last_id (x:node) y :=
  {|
    ntype := FORK;
    intra := (x, next_intra (node_task x) last_id);
    inter := (x, fork_inter y last_id)
  |}.

  Definition mk_join (last_id:nat) x y :=
  let x' := next_intra (node_task x) last_id
  in {| ntype := JOIN; intra := (x, x'); inter := (y,x') |}.

  Lemma check_intra_eq_task:
    forall v,
    Check v ->
    node_task (fst (intra v)) = node_task (snd (intra v)).
  Proof.
    intros.
    inversion H; simpl in *; auto.
  Qed.

  Lemma check_inter_neq_task:
    forall v,
    Check v ->
    node_task (fst (inter v)) <> node_task (snd (inter v)).
  Proof.
    intros.
    inversion H; simpl in *; auto.
  Qed.

  Lemma check_inter_dag_fork:
    forall v,
    Check v ->
    ntype v = FORK ->
    fst (intra v) = fst (inter v).
  Proof.
    intros.
    inversion H; simpl in *.
    - trivial.
    - rewrite <- H4 in *.
      inversion H0.
  Qed.

  Lemma check_intra_dag_join:
    forall v,
    Check v ->
    ntype v = JOIN ->
    snd (intra v) = snd (inter v).
  Proof.
    intros.
    inversion H; simpl in *; trivial.
    rewrite <- H3 in *.
    inversion H0.
  Qed.

  Lemma check_dag_lt_intra:
    forall v,
    Check v ->
    dag_lt (fst (intra v)) (snd (intra v)).
  Proof.
    intros.
    unfold dag_lt.
    inversion H; simpl in *; auto.
  Qed.

  Lemma check_dag_lt_inter:
    forall v,
    Check v ->
    dag_lt (fst (inter v)) (snd (inter v)).
  Proof.
    intros.
    unfold dag_lt.
    inversion H; simpl in *; auto.
  Qed.

  Lemma check_dag_lt_fork:
    forall v,
    Check v ->
    ntype v = FORK ->
    dag_lt (snd (intra v)) (snd (inter v)).
  Proof.
    intros.
    unfold dag_lt.
    inversion H; simpl in *; auto.
    rewrite <- H4 in *.
    inversion H0.
  Qed.

  Definition to_edges (v:tee) := inter v :: intra v :: nil.

  Definition tee_lookup t v := 
  match v with
  {| ntype := _; intra:=(_,v); inter:=(_,v') |} =>
    if TID.eq_dec (node_task v') t then Some v'
    else if TID.eq_dec (node_task v) t then Some v
    else None
  end.

  Definition tee_contains t v := match tee_lookup t v with Some _ => true | None => false end.

  Structure computation_graph := {
    cg_tees : list tee;
    cg_nodes : MT.t node;
    cg_last_id : nat
  }.

  Definition make_cg t := {|
    cg_tees := nil;
    cg_nodes := MT.add t (Build_node t 0) (@MT.empty node);
    cg_last_id := 0
  |}.

  Definition cg_edges cg :=
  flat_map to_edges (cg_tees cg).

  Definition cg_lookup t cg : option node :=
  MT.find t (cg_nodes cg).

  Definition initial_nodes t := MT.add t (zero_node t) (@MT.empty node).

  Definition cg_nodes_add (t:tee) (m: MT.t node) :=
  match t with
  | {| ntype := FORK; intra:=(_,x); inter:=(_,y) |} =>
    (MT.add (node_task x) x)
    (MT.add (node_task y) y m)
  | {| ntype := JOIN; intra:=(_,x); inter:=_ |} => 
    MT.add (node_task x) x m
  end.

  Definition tee_fork (x y:tid) (cg : computation_graph) : option tee :=
  match cg_lookup x cg with
  | Some nx => Some (mk_fork (cg_last_id cg) nx y)
  | _ => None
  end.

  Definition tee_join (x y:tid) (cg : computation_graph) : option tee :=
  match (cg_lookup x cg, cg_lookup y cg)  with
  | (Some nx, Some ny) => Some (mk_join (cg_last_id cg) nx ny)
  | _ => None
  end.

  Definition cg_add (o:option tee) (cg : computation_graph) : computation_graph :=
  match o with
  | Some v =>
    {| cg_tees := v :: cg_tees cg;
       cg_last_id := (tee_last_id v);
       cg_nodes := cg_nodes_add v (cg_nodes cg) |}
  | None => cg
  end.

  Definition cg_fork (x y:tid) (cg : computation_graph) : computation_graph :=
  cg_add (tee_fork x y cg) cg.

  Definition cg_join (x y:tid) (cg : computation_graph) : computation_graph :=
  cg_add (tee_join x y cg) cg.

  Definition cg_eval (o:op) cg :=
  match o with
  | {| op_t := e; op_src := x; op_dst := y |} =>
    let f := (match e with
      | FORK => cg_fork
      | JOIN => cg_join
      end)
    in
    f x y cg
  end.

  (** Compute a CG from a trace. *)

  Fixpoint trace_to_cg (x:tid) l := 
  match l with
  | (o::l) => cg_eval o (trace_to_cg x l)
  | nil => make_cg x
  end.

  Inductive Lookup t n cg: Prop :=
  | lookup_def: 
    MT.MapsTo t n (cg_nodes cg) ->
    Lookup t n cg.

  Definition In (t:tid) cg := MT.In t (cg_nodes cg).

  Lemma in_make:
    forall t,
    In t (make_cg t).
  Proof.
    intros.
    unfold make_cg, In.
    simpl.
    rewrite MT_Facts.add_in_iff.
    auto.
  Qed.

  Let tee_fork_inv_some:
    forall x y t cg,
    tee_fork x y cg = Some t ->
    exists n, MT.MapsTo x n (cg_nodes cg) /\ t = mk_fork (cg_last_id cg) n y.
  Proof.
    unfold tee_fork, cg_lookup.
    intros.
    destruct (MT_Extra.find_rw x (cg_nodes cg)) as [(R,?)|(n,(R,?))];
    rewrite R in *; clear R; inversion H.
    eauto.
  Qed.

  Let tee_fork_inv_none:
    forall x y cg,
    tee_fork x y cg = None ->
    ~ MT.In x (cg_nodes cg).
  Proof.
    unfold tee_fork, cg_lookup.
    intros.
    destruct (MT_Extra.find_rw x (cg_nodes cg)) as [(R,?)|(n,(R,?))];
    rewrite R in *; clear R; inversion H.
    eauto.
  Qed.

  Lemma tee_fork_dec:
    forall x y cg,
    { exists t n, tee_fork x y cg = Some t /\
      MT.MapsTo x n (cg_nodes cg) /\ t = mk_fork (cg_last_id cg) n y }
    +
    { tee_fork x y cg = None /\ ~ MT.In x (cg_nodes cg) }.
  Proof.
    intros.
    remember (tee_fork x y cg).
    symmetry in Heqo.
    destruct o.
    - left.
      apply tee_fork_inv_some in Heqo.
      destruct Heqo as (n,(?,?)).
      exists t.
      exists n.
      eauto.
    - apply tee_fork_inv_none in Heqo.
      eauto.
  Qed.

  Let tee_join_inv_some:
    forall x y t cg,
    tee_join x y cg = Some t ->
    exists nx ny, MT.MapsTo x nx (cg_nodes cg) /\
    MT.MapsTo y ny (cg_nodes cg) /\
    t = mk_join (cg_last_id cg) nx ny.
  Proof.
    unfold tee_join, cg_lookup.
    intros.
    destruct (MT_Extra.find_rw x (cg_nodes cg)) as [(R,?)|(nx,(R,?))];
    rewrite R in *; clear R; inversion H;
      destruct (MT_Extra.find_rw y (cg_nodes cg)) as [(R,?)|(ny,(R,?))];
      rewrite R in *; clear R;
      inversion H2.
    eauto.
  Qed.

  Let tee_join_inv_none:
    forall x y cg,
    tee_join x y cg = None ->
    ~ MT.In x (cg_nodes cg) \/ ~ MT.In y (cg_nodes cg).
  Proof.
    unfold tee_join, cg_lookup.
    intros.
    destruct (MT_Extra.find_rw x (cg_nodes cg)) as [(R,?)|(n,(R,?))]; auto.
    rewrite R in *; clear R; inversion H.
    destruct (MT_Extra.find_rw y (cg_nodes cg)) as [(R,?)|(?,(R,?))]; auto.
    rewrite R in *; clear R; inversion H.
  Qed.

  Lemma tee_join_dec:
    forall x y cg,
    { exists t nx ny, tee_join x y cg = Some t /\
      MT.MapsTo x nx (cg_nodes cg) /\
      MT.MapsTo y ny (cg_nodes cg) /\
      t = mk_join (cg_last_id cg) nx ny }
    +
    { tee_join x y cg = None /\ (~ MT.In x (cg_nodes cg) \/ ~ MT.In y (cg_nodes cg)) }.
  Proof.
    intros.
    remember (tee_join x y cg).
    symmetry in Heqo.
    destruct o.
    - left.
      apply tee_join_inv_some in Heqo.
      destruct Heqo as (?,(?,(?,(?,?)))).
      eauto 7. (* try harder *)
    - eauto using tee_join_inv_none.
  Qed.

  Lemma in_fork_1:
    forall x y cg,
    In x cg ->
    In y (cg_fork x y cg).
  Proof.
    intros.
    unfold cg_fork, In, cg_add.
    destruct cg.
    remember (tee_fork _ _ _).
    symmetry in Heqo.
    destruct o; simpl in *.
    - apply tee_fork_inv_some in Heqo.
      destruct Heqo as (n, (mt, R)).
      subst.
      simpl in *.
      rewrite MT_Facts.add_in_iff.
      right.
      rewrite MT_Facts.add_in_iff; auto.
    - apply tee_fork_inv_none in Heqo.
      contradiction.
  Qed.

  Let in_cg_add:
    forall z cg o,
    MT.In z (cg_nodes cg) ->
    MT.In z (cg_nodes (cg_add o cg)).
  Proof.
    unfold cg_add, cg_nodes_add.
    destruct cg, o; simpl in *; intros.
    - destruct t; destruct ntype0, intra0, inter0; simpl;
      repeat rewrite MT_Facts.add_in_iff; auto.
    - auto.
  Qed.

  Lemma in_fork_2:
    forall x y z cg,
    In z cg ->
    In z (cg_fork x y cg).
  Proof.
    unfold cg_fork, In.
    intros.
    auto.
  Qed.

  Lemma in_join_2:
    forall x y z cg,
    In z cg ->
    In z (cg_join x y cg).
  Proof.
    unfold cg_join, In.
    intros.
    auto.
  Qed.

  Inductive CG (x:tid): trace -> computation_graph -> Prop :=
  | cg_nil:
    CG x nil (make_cg x)
  | cg_cons_fork:
    forall a b l cg,
    CG x l cg ->
    In a cg ->
    a <> b ->
    CG x ({| op_t := FORK; op_src := a; op_dst := b |} :: l) (cg_fork a b cg)
  | cg_cons_join:
    forall a b l cg,
    CG x l cg ->
    In a cg ->
    In b cg ->
    CG x ({| op_t := JOIN; op_src := a; op_dst := b |} :: l) (cg_join a b cg).

  Lemma cg_fun:
    forall x l cg cg',
    CG x l cg ->
    CG x l cg' ->
    cg = cg'.
  Proof.
    induction l; intros. {
      inversion H; inversion H0; auto.
    }
    destruct a;
    destruct op_t0;
    inversion H;
    inversion H0;
    subst;
    assert (cg0 = cg1) by auto; subst; auto.
  Qed.

  (**
    Ensure the names are being used properly; no continue edges after a task
    has been termianted (target of a join).
    *)

  Inductive edge_type :=
  | CONTINUE_EDGE
  | FORK_EDGE
  | JOIN_EDGE.

  Inductive Edge : edge_type -> edge -> tee -> Prop :=
  | edge_continue:
    forall t,
    Edge CONTINUE_EDGE (intra t) t
  | edge_fork:
    forall t,
    Edge FORK_EDGE (inter t) t
  | edge_join:
    forall t,
    Edge JOIN_EDGE (inter t) t.

  Inductive Prec e t : Prop :=
  | prec_def:
    forall k,
    Edge k e t ->
    Prec e t.

  Variable cg: computation_graph.

  Definition HB_Edge_alt e := List.Exists (Prec e) (cg_tees cg).

  Definition HB_Edge := FGraph.Edge (cg_edges cg).

  Definition HB := Reaches HB_Edge.

  Definition MHP x y : Prop := ~ HB x y /\ ~ HB y x.

  Let in_edges_to_tees:
    forall e,
    List.In e (cg_edges cg) ->
    exists x, List.In x (cg_tees cg) /\ Prec e x.
  Proof.
    unfold cg_edges.
    intros.
    rewrite in_flat_map in *.
    destruct H as (x, (Hi, He)).
    exists x; split; auto.
    unfold to_edges in *.
    destruct He as [?|[?|?]]; subst.
    - destruct x.
      destruct ntype0;
      eauto using prec_def, edge_fork, edge_join.
    - eauto using prec_def, edge_continue.
    - inversion H.
  Qed.

  Let in_tees_to_edges:
    forall x e,
    List.In x (cg_tees cg) ->
    Prec e x ->
    List.In e (cg_edges cg).
  Proof.
    unfold cg_edges.
    intros.
    rewrite in_flat_map in *.
    exists x.
    split; auto.
    unfold to_edges.
    destruct H0; inversion H0; subst; auto using in_eq, in_cons.
  Qed.

  Lemma hb_edge_spec:
    forall e,
    HB_Edge e <-> HB_Edge_alt e.
  Proof.
    unfold HB_Edge, HB_Edge_alt, FGraph.Edge;
    split; intros.
    - rewrite Exists_exists.
      auto.
    - rewrite Exists_exists in *.
      destruct H as (?, (?,?)).
      eauto.
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

Section cg_nodes.

  Lemma maps_to_fork_1:
    forall a b n cg,
    MT.MapsTo a n (cg_nodes cg) ->
    node_task n = a ->
    MT.MapsTo a (next_intra (node_task n) (cg_last_id cg)) (cg_nodes (cg_fork a b cg)).
  Proof.
    intros.
    unfold cg_fork in *.
    destruct (tee_fork_dec a b cg) as [(t,(n'',(R,(Hx,?))))|(R,Hn)]; subst.
    - assert (n'' = n) by eauto using MT_Facts.MapsTo_fun; subst; clear Hx.
      rewrite R; simpl; clear R.
      rewrite MT_Facts.add_mapsto_iff in *.
      eauto.
    - contradiction Hn.
      eauto using MT_Extra.mapsto_to_in.
  Qed.

  Lemma maps_to_fork_2:
    forall a b na nb cg,
    MT.MapsTo a na (cg_nodes cg) ->
    node_task na = a ->
    a <> b ->
    MT.MapsTo b nb (cg_nodes (cg_fork a b cg)) ->
    nb = fork_inter b (cg_last_id cg).
  Proof.
    intros.
    unfold cg_fork in *.
    rename H2 into mt.
    destruct (tee_fork_dec a b cg) as [(t,(n'',(R,(Hx,?))))|(R,Hn)]; subst.
    - assert (n'' = na) by eauto using MT_Facts.MapsTo_fun; subst; clear Hx.
      rewrite R in *; simpl; clear R.
      simpl in *.
      rewrite MT_Facts.add_mapsto_iff in *.
      destruct mt as [(?,?)|(?,mt)].
      + contradiction.
      + rewrite MT_Facts.add_mapsto_iff in *.
        destruct mt as [(?,?)|(N,?)].
        * subst.
          auto.
        * contradiction N; auto.
    - contradiction Hn.
      eauto using MT_Extra.mapsto_to_in.
  Qed.

  Lemma maps_to_fork_3:
    forall x y z n nx cg,
    z <> x ->
    z <> y ->
    MT.MapsTo z n (cg_nodes (cg_fork x y cg)) ->
    MT.MapsTo x nx (cg_nodes cg) ->
    node_task nx = x ->
    MT.MapsTo z n (cg_nodes cg).
  Proof.
    intros.
    unfold cg_fork in *.
    rename H1 into mt.
    destruct (tee_fork_dec x y cg) as [(t,(n'',(R,(Hx,?))))|(R,Hn)]; subst.
    - rewrite R in *; simpl; clear R.
      simpl in *.
      rewrite MT_Facts.add_mapsto_iff in *.
      destruct mt as [(?,?)|(?,mt)].
      + assert (n''=nx) by eauto using MT_Facts.MapsTo_fun; subst.
        contradiction H; auto.
      + rewrite MT_Facts.add_mapsto_iff in *.
        destruct mt as [(?,?)|(?,mt)].
        * subst.
          contradiction H0; auto.
        * auto.
    - contradiction Hn.
      eauto using MT_Extra.mapsto_to_in.
  Qed.

  Lemma maps_to_join_1:
    forall a b n cg,
    MT.MapsTo a n (cg_nodes cg) ->
    node_task n = a ->
    MT.In b (cg_nodes cg) ->
    MT.MapsTo a (next_intra (node_task n) (cg_last_id cg)) (cg_nodes (cg_join a b cg)).
  Proof.
    intros.
    unfold cg_join in *.
    destruct (tee_join_dec a b cg) as [(t,(nx',(ny',(R,(Hx,(Hy,?))))))|(R,[Hn|Hn])]; subst.
    - assert (nx' = n) by eauto using MT_Facts.MapsTo_fun; subst; clear Hx.
      rewrite R; simpl; clear R.
      rewrite MT_Facts.add_mapsto_iff in *.
      eauto.
    - contradiction Hn.
      eauto using MT_Extra.mapsto_to_in.
    - contradiction Hn.
  Qed.

  Lemma maps_to_join_2:
    forall a b na nb cg,
    MT.MapsTo a na (cg_nodes cg) ->
    node_task na = a ->
    a <> b ->
    MT.MapsTo b nb (cg_nodes (cg_join a b cg)) ->
    MT.MapsTo b nb (cg_nodes cg).
  Proof.
    intros.
    unfold cg_join in *.
    rename H2 into mt.
    destruct (tee_join_dec a b cg) as [(t,(nx',(ny',(R,(Hx,(Hy,?))))))|(R,[Hn|Hn])]; subst.
    - assert (nx' = na) by eauto using MT_Facts.MapsTo_fun; subst; clear Hx.
      rewrite R in *; simpl in *; clear R.
      rewrite MT_Facts.add_mapsto_iff in *.
      destruct mt as [(?,?)|(?,mt)].
      + contradiction.
      + assert (ny' = nb) by eauto using MT_Facts.MapsTo_fun; subst; clear Hy.
        assumption.
    - contradiction Hn.
      eauto using MT_Extra.mapsto_to_in.
    - rewrite R in *; simpl in *; clear R.
      assumption.
  Qed.

  Lemma maps_to_join_3:
    forall x y z n nx cg,
    z <> x ->
    z <> y ->
    MT.MapsTo z n (cg_nodes (cg_join x y cg)) ->
    MT.MapsTo x nx (cg_nodes cg) ->
    node_task nx = x ->
    MT.MapsTo z n (cg_nodes cg).
  Proof.
    intros.
    unfold cg_join in *.
    rename H1 into mt.
    destruct (tee_join_dec x y cg) as [(t,(nx',(ny',(R,(Hx,(Hy,?))))))|(R,[Hn|Hn])];
    subst; rewrite R in *; simpl in *; clear R.
    - rewrite MT_Facts.add_mapsto_iff in *.
      destruct mt as [(?,?)|(?,mt)].
      + assert (nx'=nx) by eauto using MT_Facts.MapsTo_fun; subst.
        contradiction H; auto.
      + assumption.
    - contradiction Hn.
      eauto using MT_Extra.mapsto_to_in.
    - assumption.
  Qed.


End cg_nodes.

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
    compute.
    apply reaches_edge_false.
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

  Let forks_in_cg:
    forall l x t cg ts,
    CG x l cg ->
    Forks l x ts ->
    List.In t ts ->
    In t cg.
  Proof.
    induction l; intros. {
      inversion H0; subst.
      destruct H1. {
        subst.
        inversion H; subst.
        auto using in_make.
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

  Lemma cg_node_task:
    forall x l cg t n,
    CG x l cg ->
    MT.MapsTo t n (cg_nodes cg) ->
    node_task n = t.
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
      assert (node_task na = a) by eauto.
      destruct (tid_eq_dec t a); subst.
      * assert (Hx:=mt).
        apply maps_to_fork_1 with (b:=b) in Hx; auto.
        assert (n = next_intra (node_task na) (cg_last_id cg))
        by eauto using MT_Facts.MapsTo_fun;subst.
        unfold next_intra; auto.
      * destruct (tid_eq_dec t b). {
          subst.
          apply maps_to_fork_2 with (na:=na) in H0; auto.
          subst.
          auto.
        }
        apply maps_to_fork_3 with (x:=node_task na) (y:=b) (z:=t) (n:=n) (nx:=na) in H0; auto.
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
          assert (n = next_intra (node_task na) (cg_last_id cg))
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
  Qed.

  Lemma maps_to_fork_1:
    forall x y n cg a l,
    CG a l cg ->
    MT.MapsTo x n (cg_nodes cg) ->
    MT.MapsTo x (next_intra x (cg_last_id cg)) (cg_nodes (cg_fork x y cg)).
  Proof.
    intros.
    assert (R: next_intra x (cg_last_id cg) = next_intra (node_task n) (cg_last_id cg)). {
      assert (R: node_task n = x) by
      eauto using cg_node_task.
      rewrite R.
      trivial.
    }
    rewrite R.
    eauto using maps_to_fork_1, cg_node_task.
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
    eauto using maps_to_fork_2, cg_node_task.
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
    apply maps_to_fork_3 with (x:=x) (y:=y) (nx:=nx); eauto using cg_node_task.
  Qed.

  Lemma maps_to_join_1:
    forall x y n cg a l,
    CG a l cg ->
    In y cg ->
    MT.MapsTo x n (cg_nodes cg) ->
    MT.MapsTo x (next_intra x (cg_last_id cg)) (cg_nodes (cg_join x y cg)).
  Proof.
    intros.
    assert (R: next_intra x (cg_last_id cg) = next_intra (node_task n) (cg_last_id cg)). {
      assert (R: node_task n = x) by
      eauto using cg_node_task.
      rewrite R.
      trivial.
    }
    rewrite R.
    eauto using maps_to_join_1, cg_node_task.
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
    eauto using maps_to_join_2, cg_node_task.
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
    apply maps_to_join_3 with (x:=x) (y:=y) (nx:=nx); eauto using cg_node_task.
  Qed.

  End Defs.
End WellFormed.

Module Lang.

  Definition from_effect (e:Lang.effect) :=
  match e with
  | (x, Lang.FUTURE y) => Some {|op_t:=FORK; op_src:=x; op_dst:=y|}
  | (x, Lang.FORCE y) => Some {|op_t:=JOIN; op_src:=x; op_dst:=y|}
  | _ => None
  end.

  Definition from_effects := List.omap from_effect.

  (** Compute a CG from a trace of our language. *)

  Definition effects_to_cg (x:tid) ts := trace_to_cg x (from_effects ts).

End Lang.
