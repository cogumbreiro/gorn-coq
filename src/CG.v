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

  Definition cg_eval (o:op) cg :=
  match (tee_eval o cg) with
  | Some v => cg_add v cg
  | _ => cg
  end.

  Definition cg_spawn x y := cg_eval {|op_t:=SPAWN; op_src:=x; op_dst:=y|}.
  Definition cg_join x y := cg_eval {|op_t:=JOIN; op_src:=x; op_dst:=y|}.

  Inductive Lookup t n cg: Prop :=
  | lookup_def: 
    MT.MapsTo t n (cg_nodes cg) ->
    Lookup t n cg.

  Inductive CG: trace -> computation_graph -> Prop :=
  | cg_nil:
    forall x,
    CG nil (make_cg x)
  | cg_cons_some:
    forall o l cg,
    CG l cg ->
    CG (Some o::l) (cg_eval o cg)
  | cg_cons_none:
    forall l cg,
    CG l cg ->
    CG (None::l) cg.

  Inductive Reduces: computation_graph -> Lang.effect -> computation_graph -> Prop :=
  | reduces_spawn:
    forall cg x y,
    Reduces cg (x, Lang.FUTURE y) (cg_spawn x y cg)
  | reduces_join:
    forall cg x y,
    Reduces cg (x, Lang.FORCE y) (cg_join x y cg).

  (**
    Ensure the names are being used properly; no continue edges after a task
    has been termianted (target of a join).
    *)

  Inductive Dangling : trace -> list tid -> Prop :=
  | dangling_nil:
    forall x,
    Dangling nil (x::nil)
  | dangling_cons_spawn:
    forall vs ts x y,
    (* x -> y *)
    List.In x ts ->
    ~ List.In y ts ->
    Dangling vs ts ->
    Dangling (Some {|op_t:=SPAWN; op_src:=x; op_dst:=y |}::vs) (y::ts)
  | dangling_cons_join:
    forall vs ts x y,
    List.In x ts ->
    Dangling vs ts ->
    Dangling (Some {|op_t:=JOIN; op_src:=x; op_dst:=y |}::vs) (remove TID.eq_dec y ts)
  | dangling_cons_tau:
    forall vs ts,
    Dangling vs ts ->
    Dangling (None::vs) ts.

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

Section Props.
  Import Node.
(*
  Lemma cg_one_inv_lookup:
    forall x n y,
    Lookup x n (CG_ONE y) ->
    x = y /\ n = zero_node x.
  Proof.
    intros.
    destruct H.
    simpl in H.
    unfold initial_nodes in *.
    apply MT_Facts.add_mapsto_iff in H.
    destruct H.
    - intuition.
      subst.
      trivial.
    - destruct H.
      apply MT_Facts.empty_mapsto_iff in H0.
      inversion H0.
  Qed.

  Lemma lookup_inv:
    forall x t l n n' m,
    Lookup x n (CG (t :: l) n' (add_tee t m)) ->
    (node_task (snd (intra t)) = x /\ (snd (intra t)) = n) \/
    (node_task (snd (intra t)) <> x /\ MT.MapsTo x n (MT.add (node_task (snd (inter t))) (snd (inter t)) m)) \/
    (MT.MapsTo x n (MT.add (node_task (snd (intra t))) (snd (intra t)) m)).
  Proof.
    intros.
    destruct H.
    simpl in H.
    unfold add_tee in *.
    destruct t.
    destruct intra0 as (a, a').
    destruct inter0 as (b, c).
    simpl in *.
    destruct ntype0.
    - apply MT_Facts.add_mapsto_iff in H.
      destruct H as [(?,?)|?].
      + subst.
        intuition.
      + intuition.
    - intuition.
  Qed.
*)

End Props.
End CG.


Module Known.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Structures.OrderedType.
Require Import Coq.FSets.FMapAVL.
Module M := FMapAVL.Make Nat_as_OT.
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

  Inductive KnownOf : trace -> known -> Prop :=
  | known_of_nil:
    forall x,
    KnownOf nil (make_known x)
  | known_of_cons_some:
    forall o x y l k,
    Check k {| op_t:=o; op_src:=x; op_dst:=y |} ->
    KnownOf l k ->
    KnownOf (Some {| op_t:=o; op_src:=x; op_dst:=y |}::l) ((eval o) x y k)
  | known_of_cons_none:
    forall l k,
    KnownOf l k ->
    KnownOf (None::l) k.

  Definition WellFormed (k:known) := forall t l, MT.MapsTo t l k -> ~ List.In t l.

(*
  Inductive Lt x y : Prop :=
  | lt_def:
    forall n,
    Lookup x n cg ->
    List.In y (node_known n) ->
    Lt x y.

  Let lt_trans_absurd_one:
    forall t x y,
    ~ Lt (CG_ONE t) x y.
  Proof.
    intros.
    unfold not; intros.
    inversion H.
    apply cg_one_inv_lookup in H0.
    destruct H0.
    subst.
    inversion H1.
  Qed.

  Let lt_trans_absurd_nil:
    forall n m x y,
    Nodes (CG nil n m) ->
    ~ Lt (CG nil n m) x y.
  Proof.
    intros.
    unfold not; intros.
    destruct H0.
    inversion H.
  Qed.

  Let check_absurd_snd_intra:
    forall t,
    CG.WellFormed t ->
    ~ List.In (node_task (snd (intra t))) (node_known (snd (intra t))).
  Proof.
    intros.
    unfold not; intros.
    inversion H.
    + subst.
      simpl in *.
      destruct H3; contradiction.
    + subst.
      simpl in *.
      destruct H3; contradiction.
  Qed.
(*
  Let check_absurd_snd_inter:
    forall t,
    CG.WellFormed t ->
    ~ List.In (node_task (snd (inter t))) (node_known (snd (intra t))).
  Proof.
    intros.
    unfold not; intros.
    inversion H.
    + subst.
      simpl in *.
      destruct H3.
      contradiction H3.
      auto using in_
      destruct H2; contradiction.
    + subst.
      simpl in *.
      destruct H3; contradiction.
  Qed.
*)
(*
  Let lt_trans_cg:
    forall l n m,
    CG_WellFormed (CG l n m) ->
    forall x y z,
    Lt (CG l n m) x y ->
    Lt (CG l n m) y z ->
    Lt (CG l n m) x z.
  Proof.
    induction l; intros. {
      inversion H.
    }
    inversion H; subst; clear H.
    - destruct H0.
      destruct H1.
      apply lookup_inv in H.
      destruct H as [(?,?)|[?|?]].
      + subst.
        apply lookup_inv in H1.
        destruct H1 as [(?,?)|[(?,?)|?]].
        * subst.
          apply check_absurd_snd_intra in H0; auto.
          inversion H0.
        * apply MT_Facts.add_mapsto_iff in H1.
          destruct H1 as [(?,?)|(?,?)]. {
            subst.
            apply check_absurd_snd_inter in H0; auto.
            inversion H0.
          }
          
  Qed.

  Lemma lt_trans cg:
    forall x y z,
    Lt cg x y ->
    Lt cg y z ->
    Lt cg x z.
  Proof.
    intros.
    destruct cg.
    - apply lt_trans_one_absurd in H.
      inversion H.
    - 
  Qed.
*)
*)
(*
  Inductive WellFormed n : Prop :=
  | well_formed_def:
    ~ List.In (node_task n) (node_known n) ->
    WellFormed n.
*)


End Defs.
End Known.
