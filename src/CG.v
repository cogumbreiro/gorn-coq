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


Module Node.
  Structure node := {
    node_task: tid;
    node_dag_id: nat
  }.

  Definition zero_node t := {| node_task := t; node_dag_id:= 0 |}.
End Node.

Module Trace.
  Inductive op_type := FORK | JOIN.

  Structure op := {
    op_t: op_type;
    op_src: tid;
    op_dst: tid
  }.

  Definition trace := list op.

End Trace.

Section CG.


Section Defs.
  Import Trace.
  Import Node.

  (** DAG id order *)

  Definition dag_lt x y := node_dag_id x < node_dag_id y.

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
        {| node_task := x; node_dag_id := dx |},
        {| node_task := x; node_dag_id := last_id |}
      );
      inter :=
      (
        {| node_task := x; node_dag_id := dx |},
        {| node_task := y; node_dag_id := S last_id |}
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
        {| node_task := x; node_dag_id := dx |},
        {| node_task := x; node_dag_id := last_id |}
      );
      inter :=
      (
        {| node_task := y; node_dag_id := dy |},
        {| node_task := x; node_dag_id := last_id |}
      )
    |}.

  (** Creates a future node *)

  Definition tee_last_id (t:tee) :=
  node_dag_id (snd (inter t)).

  Definition mk_fork last_id (x:node) y :=
  {|
    ntype := FORK;
    intra := (x, {| node_task := (node_task x); node_dag_id := S last_id |} );
    inter := (x, {| node_task := y; node_dag_id := S (S last_id) |})
  |}.

  Definition mk_join (last_id:nat) x y :=
  let x' := {| node_task := (node_task x); node_dag_id := S last_id |}
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

End CG.

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
  Import Trace.

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
    - eauto using cg_cons_fork, forks_in_cg.
    - apply cg_cons_join; eauto using forks_in_cg.
  Qed.

End WellFormed.

Module Lang.
  Import Trace.

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
