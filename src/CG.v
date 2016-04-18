Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
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
  Inductive op_type := SPAWN | JOIN.

  Structure op := {
    op_t: op_type;
    op_src: tid;
    op_dst: tid
  }.

  Definition trace := list (option op).
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
  | check_spawn:
    forall x y dx last_id,
    dx < last_id ->
    x <> y ->
    Check
    {|
      ntype := SPAWN;
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

  Definition mk_spawn last_id (x:node) y :=
  {|
    ntype := SPAWN;
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

  Lemma check_inter_dag_spawn:
    forall v,
    Check v ->
    ntype v = SPAWN ->
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

  Lemma check_dag_lt_spawn:
    forall v,
    Check v ->
    ntype v = SPAWN ->
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
  | {| ntype := SPAWN; intra:=(_,x); inter:=(_,y) |} =>
    (MT.add (node_task x) x)
    (MT.add (node_task y) y m)
  | {| ntype := JOIN; intra:=(_,x); inter:=_ |} => 
    MT.add (node_task x) x m
  end.

  Definition tee_spawn (x y:tid) (cg : computation_graph) : option tee :=
  match cg_lookup x cg with
  | Some nx => Some (mk_spawn (cg_last_id cg) nx y)
  | _ => None
  end.

  Definition tee_join (x y:tid) (cg : computation_graph) : option tee :=
  match (cg_lookup x cg, cg_lookup y cg)  with
  | (Some nx, Some ny) => Some (mk_join (cg_last_id cg) nx ny)
  | _ => None
  end.

  Definition cg_add (v:tee) (cg : computation_graph) : computation_graph :=
    {| cg_tees := v :: cg_tees cg;
       cg_last_id := (tee_last_id v);
       cg_nodes := cg_nodes_add v (cg_nodes cg) |}.

  Definition tee_eval o : computation_graph -> option tee :=
  match o with
  | {| op_t := e; op_src := x; op_dst := y |} =>
    let f := (match e with
    | SPAWN => tee_spawn
    | JOIN => tee_join
    end) in
    f x y
  end.

  Definition cg_eval (o:option op) cg :=
  match o with
  | Some o =>
    match (tee_eval o cg) with
    | Some v => cg_add v cg
    | _ => cg
    end
  | None => cg
  end.

  Inductive Lookup t n cg: Prop :=
  | lookup_def: 
    MT.MapsTo t n (cg_nodes cg) ->
    Lookup t n cg.

  Inductive CG: trace -> computation_graph -> Prop :=
  | cg_nil:
    forall x,
    CG nil (make_cg x)
  | cg_cons:
    forall o l cg,
    CG l cg ->
    CG (o::l) (cg_eval o cg).

  Definition is_evt (o:Lang.op) :=
  match o with
  | Lang.FUTURE _ => true
  | Lang.FORCE _ => true
  | _ => false
  end.

  Definition from_evt e :=
  match e with
  | (x, Lang.FUTURE y) => Some {|op_t:=SPAWN; op_src:=x; op_dst:=y|}
  | (x, Lang.FORCE y) => Some {|op_t:=JOIN; op_src:=x; op_dst:=y|}
  | _ => None
  end.

  Inductive Reduces: computation_graph -> Lang.effect -> computation_graph -> Prop :=
  | reduces_def:
    forall cg e,
    Reduces cg e (cg_eval (from_evt e) cg).

  (**
    Ensure the names are being used properly; no continue edges after a task
    has been termianted (target of a join).
    *)

  Inductive Continue v : edge -> Prop :=
    continue_def:
      Continue v (intra v).

  Inductive Spawn: tee -> edge -> Prop :=
    spawn_def:
      forall v,
      ntype v = SPAWN ->
      Spawn v (inter v).

  Inductive Join: tee -> edge -> Prop :=
    join_def:
      forall v,
      ntype v = JOIN ->
      Join v (inter v).

  Inductive Prec t e : Prop :=
  | prec_continue:
    Continue t e ->
    Prec t e
  | prec_spawn:
    Spawn t e ->
    Prec t e
  | prec_join:
    Join t e ->
    Prec t e.

  Inductive ListEdge {A:Type} {B:Type} P l (e:B*B) : Prop :=
  | list_edge_def:
    forall (x:A),
    List.In x l ->
    P x e ->
    ListEdge P l e.

  Let LContinue := ListEdge Continue.
  Let LSpawn := ListEdge Spawn.
  Let LPrec := ListEdge Prec.

  Require Import Aniceto.Graphs.Graph.

  Variable cg: computation_graph.

  Definition ContinueRefl x := ClosTransRefl (LContinue (cg_tees cg)) x.

  Definition HB := Reaches (LPrec (cg_tees cg)).

  Definition MHP x y : Prop := ~ HB x y /\ ~ HB y x.

  Inductive Ordered n1 n2 : Prop :=
  | ordered_lr:
    HB n1 n2 ->
    Ordered n1 n2
  | ordered_rl:
    HB n2 n1 ->
    Ordered n1 n2.

  (**
    We have a safe-spawn when the body of the spawn may run in parallel
    with the continuation of the spawn.
    *)

  Inductive SafeSpawn : tee -> Prop :=
  | safe_spawn_eq:
    forall v,
    ntype v = SPAWN ->
    List.In v (cg_tees cg) ->
    (forall y, ContinueRefl (snd (inter v)) y -> MHP y (snd (intra v) )) ->
    SafeSpawn v
  | safe_spawn_skip:
    forall v,
    ntype v = JOIN ->
    List.In v (cg_tees cg) ->
    SafeSpawn v.

  Definition Safe := List.Forall SafeSpawn (cg_tees cg).

  (** Is predicate [Safe] equivalent to [CG.RaceFree]? Maybe [CG.RaceFree] implies [Safe] *)
  (** Is predicate [CG.RaceFree] equivalent to [Shadow.RaceFree]? *)

End Defs.

End CG.

Module WellFormed.
  Import Trace.

  Inductive Spawns : trace -> tid -> list tid -> Prop :=
  | spawns_nil:
    forall x,
    Spawns nil x (x::nil)
  | spawns_cons_spawn:
    forall ts l z x y,
    (* x -> y *)
    List.In x l ->
    ~ List.In y l ->
    Spawns ts z l ->
    Spawns (Some {|op_t:=SPAWN; op_src:=x; op_dst:=y |}::ts) z (y::l)
  | spawns_cons_join:
    forall ts l x y z,
    List.In x l ->
    List.In y l ->
    Spawns ts z l ->
    Spawns (Some {|op_t:=JOIN; op_src:=x; op_dst:=y |}::ts) z l
  | spawns_cons_none:
    forall ts l z,
    Spawns ts z l ->
    Spawns (None::ts) z l.

  Lemma spawns_no_dup:
    forall ts x l,
    Spawns ts x l  ->
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

  Inductive Joins: trace -> list tid -> Prop :=
  | joins_nil:
    Joins nil nil
  | joins_cons_spawn:
    forall ts l x y,
    ~ List.In x l ->
    ~ List.In y l ->
    Joins ts l ->
    Joins (Some {|op_t:=SPAWN; op_src:=x; op_dst:=y |}::ts) l
  | joins_cons_join:
    forall ts l x y,
    ~ List.In x l ->
    Joins ts l ->
    Joins (Some {|op_t:=JOIN; op_src:=x; op_dst:=y |}::ts) l
  | joins_cons_none:
    forall ts l,
    Joins ts l ->
    Joins (None::ts) l.

  Inductive Running : trace -> tid -> list tid -> Prop :=
  | running_nil:
    forall x,
    Running nil x (x::nil)
  | running_cons_spawn:
    forall ts l x y z,
    (* x -> y *)
    List.In x l ->
    ~ List.In y l ->
    Running ts z l ->
    Running (Some {|op_t:=SPAWN; op_src:=x; op_dst:=y |}::ts) z (y::l)
  | running_cons_join:
    forall ts l x y z,
    List.In x l ->
    Running ts z l ->
    Running (Some {|op_t:=JOIN; op_src:=x; op_dst:=y |}::ts) z (remove TID.eq_dec y l)
  | running_cons_none:
    forall ts l z,
    Running ts z l ->
    Running (None::ts) z l.

  Lemma in_remove_simpl:
    forall {A:Type} (x y:A) l eq_dec,
    List.In x (remove eq_dec y l) ->
    List.In x l.
  Proof.
    induction l; intros; auto.
    simpl in H.
    destruct (eq_dec y a).
    - subst.
      eauto using in_cons.
    - inversion H.
      + subst.
        auto using in_eq.
      + eauto using in_cons.
  Qed.

  Lemma no_dup_remove:
    forall {A:Type} (l:list A),
    NoDup l ->
    forall (x:A) eq_dec,
    NoDup (remove eq_dec x l).
  Proof.
    induction l; intros; auto.
    inversion H; subst; clear H.
    simpl.
    destruct (eq_dec x a).
    - eauto.
    - apply NoDup_cons.
      + unfold not; intros.
        contradiction H2.
        eauto using in_remove_simpl.
      + eauto.
  Qed.

  Lemma incl_cons_cons:
    forall {A:Type} l l',
    incl l l' ->
    forall (x:A),
    incl (x :: l) (x :: l').
  Proof.
    intros.
    eauto using incl_cons, in_eq, incl_tl.
  Qed.

  Lemma incl_remove:
    forall {A:Type} l l',
    incl l l' ->
    forall eq_dec (x:A),
    incl (remove eq_dec x l) l'.
  Proof.
    intros.
    unfold incl in *; intros.
    apply in_remove_simpl in H0.
    auto.
  Qed.

  Lemma running_incl_spawned:
    forall ts ks rs x,
    Running ts x rs ->
    Spawns ts x ks ->
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
    - inversion H0.
      eauto using incl_remove.
    - inversion H0.
      eauto.
  Qed.


  Lemma no_dup_cons_nil:
    forall {A:Type} (x:A),
    NoDup (x :: nil).
  Proof.
    intros.
    apply NoDup_cons.
    - intuition.
    - auto using NoDup_nil.
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
    - eauto.
  Qed.

  Lemma incl_rw_nil:
    forall {A:Type} (l:list A),
    incl l nil ->
    l = nil.
  Proof.
    unfold incl.
    intros.
    destruct l; auto.
    assert (X: List.In a (a::l)) by auto using in_eq.
    apply H in X.
    inversion X.
  Qed.

End WellFormed.

Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Structures.OrderedType.
Require Import Coq.FSets.FMapAVL.
Module M := FMapAVL.Make Nat_as_OT.

Module Known.
  Import Trace.
  Section Defs.
  Definition known := MT.t (list tid).
  Definition make_known (x:tid) : known := (MT.add x nil (@MT.empty (list tid))).

  Definition spawn (x y:tid) (k:known) : known :=
  match MT.find x k with
  | Some l => (MT.add x (y::l)) (MT.add y l k)
  | _ => k
  end.

  Definition join (x y:tid) (k:known) : known :=
  match (MT.find x k, MT.find y k) with
  | (Some lx,Some ly) =>
    MT.add x (ly ++ lx) k
  | _ => k
  end.

  Definition eval (o:op_type) :=
  match o with SPAWN => spawn | JOIN => join end.

  Inductive Check (k:known) : op -> Prop :=
  | check_spawn:
    forall x y,
    MT.In x k ->
    ~ MT.In y k ->
    Check k {| op_t := SPAWN; op_src:= x; op_dst:= y|}
  | check_join:
    forall x y lx ly,
    MT.MapsTo x lx k ->
    MT.MapsTo y ly k ->
    List.In y lx ->
    ~ List.In x ly ->
    Check k {| op_t := JOIN; op_src := x; op_dst:= y|}.

  Inductive Known : trace -> known -> Prop :=
  | known_nil:
    forall x,
    Known nil (make_known x)
  | known_cons_some:
    forall o x y l k,
    Check k {| op_t:=o; op_src:=x; op_dst:=y |} ->
    Known l k ->
    Known (Some {| op_t:=o; op_src:=x; op_dst:=y |}::l) ((eval o) x y k)
  | known_cons_none:
    forall l k,
    Known l k ->
    Known (None::l) k.

  Definition WellFormed (k:known) := forall t l, MT.MapsTo t l k -> ~ List.In t l.

  Inductive SpawnEdges : trace -> list (tid*tid) -> Prop :=
  | spawn_edges_nil:
    SpawnEdges nil nil
  | spawn_edges_cons_spawn:
    forall x y l e,
    SpawnEdges l e ->
    SpawnEdges (Some {| op_t:=SPAWN; op_src:=x; op_dst:=y|}::l) ((x,y)::e)
  | spawn_edges_cons_join:
    forall l e x y,
    SpawnEdges l e ->
    SpawnEdges (Some {| op_t:=JOIN; op_src:=x; op_dst:=y|}::l) e
  | spawn_edges_cons_none:
    forall l e,
    SpawnEdges l e ->
    SpawnEdges (None::l) e.

  Require Import Bijection.
  Import WellFormed.

  (** The spawn-tree is a DAG *)

  Lemma spawn_edges_dag:
    forall t a vs es,
    Spawns t a vs ->
    SpawnEdges t es ->
    DAG (Bijection.Lt vs) es.
  Proof.
    induction t; intros;
    inversion H0; subst; clear H0;
    inversion H; subst; clear H; eauto. {
     apply Forall_nil.
    }
    assert (dag: DAG (Lt l) e) by eauto.
    apply Forall_cons.
    - simpl.
      apply in_to_index_of in H3; destruct H3 as (n, (?,?)).
      assert (IndexOf y (length l) (y::l)) by eauto using index_of_eq.
      apply lt_def with (xn:=n) (yn:=length l); auto using index_of_cons.
    - unfold DAG in *.
      apply Forall_impl with (P:=LtEdge (Lt l)); auto.
      intros.
      destruct a as (v,w).
      simpl in *.
      auto using lt_cons.
  Qed.

End Defs.
End Known.
