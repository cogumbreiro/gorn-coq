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

  Definition from_effect (e:Lang.effect) :=
  match e with
  | (x, Lang.FUTURE y) => Some {|op_t:=SPAWN; op_src:=x; op_dst:=y|}
  | (x, Lang.FORCE y) => Some {|op_t:=JOIN; op_src:=x; op_dst:=y|}
  | _ => None
  end.

  Definition from_effects := map from_effect.
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

  (** Compute a CG from a trace. *)

  Definition trace_to_cg (x:tid) ts := fold_left (fun cg o => cg_eval o cg) ts (make_cg x).

  (** Compute a CG from a trace of our language. *)

  Definition effects_to_cg (x:tid) ts := trace_to_cg x (from_effects ts).

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


  Inductive Reduces: computation_graph -> Lang.effect -> computation_graph -> Prop :=
  | reduces_def:
    forall cg e,
    Reduces cg e (cg_eval (from_effect e) cg).

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

  Require Import Aniceto.List.

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
    - inversion H0; subst.
      eauto using remove_incl, incl_tran.
    - inversion H0.
      eauto.
  Qed.

  Lemma in_running_in_spawn:
    forall ts vs rs x y,
    Running ts x rs ->
    Spawns ts x vs ->
    List.In y rs ->
    List.In y vs.
  Proof.
    intros.
    assert (incl rs vs) by eauto using running_incl_spawned.
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
    destruct a as [(a,src,dst)|].
    - destruct a; inversion H; inversion H0; subst; clear H H0.
      + destruct H1; subst; eauto.
      + eauto using remove_in.
    - inversion H; inversion H0; subst; clear H H0.
      eauto.
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
    destruct a as [(a,src,dst)|].
    - destruct a; inversion H; inversion H0; subst; clear H H0.
      + unfold not; intros Hx.
        destruct Hx.
        * subst.
          contradiction.
        * assert (Hx := IHts _ _ _ H9 H16 _ H1).
          contradiction.
      + unfold not; intros Hx.
        apply remove_in in Hx.
        assert (Hy := IHts _ _ _ H8 H14 _ H1).
        contradiction.
    - inversion H; inversion H0.
      eauto.
  Qed.

  Require Import Coq.Lists.ListSet.
  Require Import Aniceto.ListSet.

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

End WellFormed.

Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Structures.OrderedType.
Require Import Coq.FSets.FMapAVL.
Module M := FMapAVL.Make Nat_as_OT.

Module Restriction.
  Require Import Aniceto.Graphs.FGraph.
  Section Defs.

  Let vertex_mem (vs:list tid) (x:tid) := ListSet.set_mem TID.eq_dec x vs.

  Let edge_mem vs (e:tid*tid) := let (x,y) := e in andb (vertex_mem vs x) (vertex_mem vs y).

  Definition edge_eq_dec := Pair.pair_eq_dec TID.eq_dec.

  Definition restriction vs es := filter (edge_mem vs) es.

  Lemma restriction_incl:
    forall vs es,
    incl (restriction vs es) es.
  Proof.
    intros.
    unfold restriction.
    auto using List.filter_incl.
  Qed.

  Let vertex_mem_true_to_prop:
    forall x l,
    vertex_mem l x = true ->
    List.In x l.
  Proof.
    unfold vertex_mem.
    intros.
    apply ListSet.set_mem_correct1 in H.
    auto.
  Qed.

  Let vertex_mem_false_to_prop:
    forall x l,
    vertex_mem l x = false ->
    ~ List.In x l.
  Proof.
    unfold vertex_mem.
    intros.
    apply ListSet.set_mem_complete1 in H.
    auto.
  Qed.

  Let edge_mem_true_to_prop:
    forall rs x1 x2,
    edge_mem rs (x1, x2) = true ->
    List.In x1 rs /\ List.In x2 rs.
  Proof.
    unfold edge_mem.
    intros.
    remember (vertex_mem _ x1) as b1.
    remember (vertex_mem _ x2) as b2.
    symmetry in Heqb1; symmetry in Heqb2.
    destruct b1, b2; subst; try inversion H.
    auto using vertex_mem_true_to_prop.
  Qed.

  Let edge_mem_false_to_prop:
    forall rs x1 x2,
    edge_mem rs (x1, x2) = false ->
    ~ List.In x1 rs \/ ~ List.In x2 rs.
  Proof.
    unfold edge_mem.
    intros.
    rewrite Bool.andb_false_iff in H.
    destruct H;
    eauto using vertex_mem_false_to_prop.
  Qed.

  Let edge_mem_true_from_prop:
    forall rs x1 x2,
    List.In x1 rs ->
    List.In x2 rs ->
    edge_mem rs (x1, x2) = true.
  Proof.
    intros.
    remember (edge_mem _ _).
    symmetry in Heqb.
    destruct b; auto.
    apply edge_mem_false_to_prop in Heqb.
    destruct Heqb; contradiction.
  Qed.

  Let restriction_inv_edge:
    forall x1 x2 rs es,
    List.In (x1, x2) (restriction rs es) ->
    List.In x1 rs /\ List.In x2 rs.
  Proof.
    unfold restriction.
    intros.
    apply filter_In in H.
    destruct H.
    auto.
  Qed.

  Lemma restriction_in_1:
    forall rs es x,
    Graph.In (Edge (restriction rs es)) x ->
    List.In x rs.
  Proof.
    unfold Edge.
    intros.
    destruct H as ((x1,x2),(He,inP)).
    apply restriction_inv_edge in He.
    destruct He.
    destruct inP; simpl in *; subst; auto.
  Qed.

  Lemma restriction_in_2:
    forall x1 x2 rs es,
    List.In (x1, x2) es ->
    List.In x1 rs ->
    List.In x2 rs ->
    List.In (x1, x2) (restriction rs es).
  Proof.
    unfold restriction.
    intros.
    apply List.filter_true_to_in; auto.
  Qed.

  End Defs.
End Restriction.

Module SafeJoins.
  Import Trace.
  Import Restriction.
  Require Import Aniceto.Graphs.FGraph.

  Section Defs.
  Notation known := (list (tid*tid)).

  Definition safe_join_of t (e:tid*tid) := let (x,y) := e in if TID.eq_dec x t then Some y else None.

  Definition get_safe_joins x := List.omap (safe_join_of x).

  Definition copy_from (x y:tid) k := map (fun z => (y, z)) (get_safe_joins x k).

  Definition spawn (x y:tid) (k:known) : known :=
  copy_from x y k ++ (x,y) :: k.

  Definition join (x y:tid) (k:known) : known :=
  copy_from y x k ++ k.

  Definition eval (o:option op) :=
  match o with
  | Some o =>
    let f := match op_t o with
      | SPAWN => spawn
      | JOIN => join 
      end
    in
    f (op_src o) (op_dst o)
  | _ => fun k => k
  end.

  Inductive Check (k:known) : option op -> Prop :=
  | check_spawn:
    forall x y,
    x <> y ->
    ~ In (Edge k) y ->
    Check k (Some {| op_t := SPAWN; op_src:= x; op_dst:= y|})
  | check_join:
    forall x y,
    Edge k (x,y) ->
    Check k (Some {| op_t := JOIN; op_src := x; op_dst:= y|})
  | check_none:
    Check k None.

  Fixpoint from_trace ts := 
  match ts with
  | nil => nil
  | o :: ts => eval o (from_trace ts)
  end.

  Definition effects_to_sj ts := from_trace (from_effects ts).

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

  Let dag_spawn_aux_0:
    forall l k x y,
    DAG (Edge k) ->
    x <> y ->
    ~ In (Edge k) y ->
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

  Let dag_spawn:
    forall k x y,
    DAG (Edge k) ->
    x <> y ->
    ~ In (Edge k) y ->
    DAG (Edge (spawn x y k)).
  Proof.
    unfold spawn.
    intros.
    apply dag_spawn_aux_0; auto using incl_refl.
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
    inversion H; subst; simpl; auto.
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

  Notation R_Edge rs k := (Edge (restriction rs k)).

  Notation R_DAG rs k := (DAG (R_Edge rs k)).

  Import WellFormed.

  Let running_infimum:
    forall rs k,
    restriction rs k <> nil ->
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
    (restriction rs k) <> nil ->
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
    remember (restriction rs k) as l.
    destruct l. {
      subst.
      destruct rs. { contradiction H0; auto. }
      exists t0.
      assert (List.In t0 (t0::rs)) by auto using in_eq.
      split. { auto. }
      intros.
      unfold not; intros.
      assert (List.In (t0, y) (restriction (t0::rs) k)) by auto using restriction_in_2.
      rewrite <- Heql in *.
      inversion H4.
    }
    assert (restriction rs k <> nil). {
      intuition.
      rewrite H1 in *.
      inversion Heql.
    }
    eauto.
  Qed.

  End Defs.
End SafeJoins.


Module Known.
  Import Trace.
  Import Restriction.
  Require Import Aniceto.Graphs.FGraph.

  Section Defs.
  Definition known := MT.t (list tid).
  Definition make (x:tid) : known := (MT.add x nil (@MT.empty (list tid))).

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

  Definition eval (o:option op) :=
  match o with
  | Some o =>
    let f := match op_t o with
      | SPAWN => spawn
      | JOIN => join 
      end
    in
    f (op_src o) (op_dst o)
  | _ => fun k => k
  end.

  Inductive Check (k:known) : option op -> Prop :=
  | check_spawn:
    forall x y,
    MT.In x k ->
    ~ MT.In y k ->
    Check k (Some {| op_t := SPAWN; op_src:= x; op_dst:= y|})
  | check_join:
    forall x y lx ly,
    MT.MapsTo x lx k ->
    MT.MapsTo y ly k ->
    List.In y lx ->
    ~ List.In x ly ->
    Check k (Some {| op_t := JOIN; op_src := x; op_dst:= y|})
  | check_none:
    Check k None.

  Fixpoint from_trace x ts :=
  match ts with
  | nil => make x
  | o :: ts => eval o (from_trace x ts)
  end.

  Inductive Safe : trace -> tid -> known -> Prop :=
  | safe_nil:
    forall x,
    Safe nil x (make x)
  | safe_cons:
    forall o l z k,
    Check k o ->
    Safe l z k ->
    Safe (o::l) z (eval o k).

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

  Definition to_spawn_edge e :=
  match e with
  | Some {| op_t:=SPAWN; op_src:=x; op_dst:=y|} => Some (x,y)
  | _ => None
  end.

  Definition spawn_edges (ts:trace) := List.omap to_spawn_edge ts.

  Inductive WellFormed (k:known) :=
  | well_formed_def:
    (forall t l, MT.MapsTo t l k -> ~ List.In t l) ->
    (forall x y l, MT.MapsTo x l k -> List.In y l -> MT.In y k) ->
    WellFormed k.

  Require Import Bijection.
  Import WellFormed.

  (** The spawn-tree is a DAG *)

  Let edge_in_absurd_nil:
    forall {A:Type} (x:A),
    ~ Graph.In (Edge nil) x.
  Proof.
    intuition.
    destruct H as (?,(n,?)).
    destruct n.
  Qed.

  Let spawn_edges_to_spawns:
    forall x t a vs es,
    Spawns t a vs ->
    SpawnEdges t es ->
    Graph.In (Edge es) x ->
    List.In x vs.
  Proof.
    induction t; intros. {
      inversion H0; subst.
      apply edge_in_absurd_nil in H1.
      inversion H1.
    }
    inversion H; subst; clear H; inversion H0; subst; clear H0; eauto.
    destruct H1 as (e',(He,Hi)).
    destruct He; subst.
    + destruct Hi as [Hi|Hi]; symmetry in Hi; simpl in *; subst; intuition.
    + assert (Graph.In (Edge e) x) by eauto using in_def.
      eauto using in_cons.
  Qed.

  Let make_mapsto:
    forall x,
    MT.MapsTo x nil (make x).
  Proof.
    intros.
    unfold make.
    auto using MT.add_1.
  Qed.

  Let make_inv_maps_to:
    forall x y l,
    MT.MapsTo x l (make y) ->
    x = y /\ l = nil.
  Proof.
    intros.
    unfold make in *.
    apply MT_Facts.add_mapsto_iff in H.
    destruct H as [(?,?)|(?,?)]; auto.
    apply MT_Facts.empty_mapsto_iff in H0.
    contradiction.
  Qed.

  Let spawn_inv_maps_to:
    forall x y z l k,
    MT.MapsTo z l (spawn x y k) ->
    MT.MapsTo z l k \/
    (z = x /\ exists l', l = y :: l' /\ MT.MapsTo x l' k) \/
    (x <> z /\ y = z /\ MT.MapsTo x l k).
  Proof.
    intros.
    unfold spawn in *.
    destruct (MT_Extra.find_rw x k) as [(He,n)|(?,(He,?))]; rewrite He in *.
    - auto.
    - apply MT_Facts.add_mapsto_iff in H.
      destruct H as [(?,?)|(?,?)].
      + right; left.
        intuition.
        exists x0.
        intuition.
      + apply MT_Facts.add_mapsto_iff in H1.
        destruct H1 as [(?,?)|(?,?)].
        * right; right.
          subst; auto.
        * intuition.
  Qed.

  Let join_inv_maps_to:
    forall x y z l k,
    MT.MapsTo z l (join x y k) ->
    MT.MapsTo z l k \/
    (exists lx ly, MT.MapsTo x lx k /\ MT.MapsTo y ly k /\ l = ly ++ lx /\ z = x).
  Proof.
    unfold join.
    intros.
    destruct (MT_Extra.find_rw x k) as [(He,n)|(?,(He,?))]; rewrite He in *. {
      intuition.
    }
    destruct (MT_Extra.find_rw y k) as [(He',n)|(?,(He',?))]; rewrite He' in *. {
      intuition.
    }
    clear He He'.
    apply MT_Facts.add_mapsto_iff in H.
    destruct H as [(?,?)|(?,?)].
    - subst.
      right.
      exists x0.
      eauto.
    - intuition.
  Qed.

  Let spawn_mapsto_neq:
    forall (x y:tid) l (k:known),
    y <> x ->
    MT.MapsTo x l k ->
    MT.MapsTo y l (spawn x y k).
  Proof.
    intros.
    unfold spawn.
    destruct (MT_Extra.find_rw x k) as [(He,n)|(?,(He,?))]; rewrite He.
    - contradiction n; eauto using MT_Extra.mapsto_to_in.
    - assert (x0 = l) by eauto using MT_Facts.MapsTo_fun; subst.
      eauto using MT.add_2, MT.add_1.
  Qed.

  Let spawn_mapsto_inv_1:
    forall x y l k,
    MT.In x k ->
    MT.MapsTo x l (spawn x y k) ->
    exists l', (l = y::l' /\ MT.MapsTo x l' k).
  Proof.
    unfold spawn.
    intros.
    destruct (MT_Extra.find_rw x k) as [(He,n)|(?,(He,?))]; rewrite He in *.
    - contradiction.
    - apply MT_Facts.add_mapsto_iff in H0.
      destruct H0 as [(?,?)|(?,?)].
      + subst.
        eauto.
      + contradiction H0; auto.
  Qed.

  Let spawn_mapsto_eq:
    forall x y k l,
    MT.MapsTo x l k ->
    MT.MapsTo x (y::l) (spawn x y k).
  Proof.
    intros.
    unfold spawn.
    destruct (MT_Extra.find_rw x k) as [(He,n)|(?,(He,?))]; rewrite He.
    - contradiction n; eauto using MT_Extra.mapsto_to_in.
    - assert (x0 = l) by eauto using MT_Facts.MapsTo_fun; subst.
      eauto using MT.add_1.
  Qed.

  Let spawn_mapsto_eq_spawned:
    forall x y k l,
    MT.MapsTo x l k ->
    x <> y ->
    MT.MapsTo y l (spawn x y k).
  Proof.
    intros.
    unfold spawn.
    destruct (MT_Extra.find_rw x k) as [(He,n)|(?,(He,?))]; rewrite He.
    - contradiction n; eauto using MT_Extra.mapsto_to_in.
    - assert (x0 = l) by eauto using MT_Facts.MapsTo_fun; subst.
      eauto using MT.add_2, MT.add_1.
  Qed.

  Let spawn_mapsto_eq_spawner:
    forall x y k l,
    MT.In x k ->
    x <> y ->
    MT.MapsTo y l (spawn x y k) ->
    MT.MapsTo x l k.
  Proof.
    intros.
    unfold spawn in *.
    destruct (MT_Extra.find_rw x k) as [(He,n)|(?,(He,?))]; rewrite He in *.
    - contradiction n; eauto using MT_Extra.mapsto_to_in.
    - clear He H.
      apply MT_Facts.add_mapsto_iff in H1.
      destruct H1 as [(?,?)|(?,?)].
      + contradiction.
      + apply MT_Facts.add_mapsto_iff in H1.
        destruct H1 as [(?,?)|(?,?)]; subst; auto.
        contradiction H1; trivial.
  Qed.

  Let spawn_mapsto_neq_neq:
    forall x y z l k,
    z <> x ->
    z <> y ->
    MT.MapsTo z l k ->
    MT.MapsTo z l (spawn x y k).
  Proof.
    intros.
    unfold spawn.
    destruct (MT_Extra.find_rw x k) as [(He,n)|(?,(He,?))]; rewrite He.
    - auto.
    - eauto using MT.add_2.
  Qed.

  Let spawn_mapsto_inv_neq_neq:
    forall x y z l k,
    z <> x ->
    z <> y ->
    MT.MapsTo z l (spawn x y k) ->
    MT.MapsTo z l k.
  Proof.
    unfold spawn.
    intros.
    destruct (MT_Extra.find_rw x k) as [(He,n)|(?,(He,?))]; rewrite He in *.
    - auto.
    - repeat (apply MT.add_3 in H1; auto).
  Qed.

  Let spawn_in:
    forall x y z k,
    MT.In z k ->
    MT.In z (spawn x y k).
  Proof.
    intros.
    unfold spawn.
    destruct (MT_Extra.find_rw x k) as [(He,n)|(?,(He,?))];
    rewrite He;
    auto using MT_Extra.add_in.
  Qed.

  Let spawn_in_spawned:
    forall x y k,
    MT.In x k ->
    MT.In y (spawn x y k).
  Proof.
    intros.
    unfold spawn.
    destruct (MT_Extra.find_rw x k) as [(He,n)|(?,(He,?))];
    rewrite He.
    - contradiction.
    - apply MT_Extra.add_in.
      rewrite MT_Facts.add_in_iff.
      auto.
  Qed.

  Let join_in:
    forall x y z k,
    MT.In z k ->
    MT.In z (join x y k).
  Proof.
    intros.
    unfold join.
    destruct (MT_Extra.find_rw x k) as [(He,n)|(?,(He,?))];
    rewrite He.
    - auto.
    - clear He.
      destruct (MT_Extra.find_rw y k) as [(He,n)|(?,(He,?))];
      rewrite He;
    auto using MT_Extra.add_in.
  Qed.

  Let edge_cons:
    forall {A:Type} es (e e':A*A),
    Edge es e ->
    Edge (e' :: es) e.
  Proof.
    unfold Edge.
    auto using in_cons.
  Qed.

  Let reaches_cons:
    forall {A:Type} (x y:A) e es,
    Reaches (Edge es) x y ->
    Reaches (Edge (e :: es)) x y.
  Proof.
    eauto using reaches_impl.
  Qed.

  Lemma safe_spec:
    forall ts x k,
    Safe ts x k ->
    k = from_trace x ts.
  Proof.
    induction ts; intros. {
      inversion H; simpl; auto.
    }
    inversion H; subst.
    simpl.
    assert (RW: k0 = from_trace x ts) by auto.
    rewrite RW.
    auto.
  Qed.

  Lemma safe_fun:
    forall ts x k1 k2,
    Safe ts x k1 ->
    Safe ts x k2 ->
    k1 = k2.
  Proof.
    intros.
    assert (R1 :  k1 = from_trace x ts) by auto using safe_spec.
    assert (R2 :  k2 = from_trace x ts) by auto using safe_spec.
    rewrite R1.
    rewrite R2.
    trivial.
  Qed.

  Lemma spawn_rw:
    forall x y l k,
    MT.MapsTo x l k ->
    ~ MT.In (elt:=list tid) y k ->
    spawn x y k = MT.add x (y :: l) (MT.add y l k).
  Proof.
    intros.
    unfold spawn.
    destruct (MT_Extra.find_rw x k) as [(?,?)|(l',(R,?))]. {
      contradiction H2; eauto using MT_Extra.mapsto_to_in.
    }
    rewrite R.
    assert (l' = l) by eauto using MT_Facts.MapsTo_fun; subst; auto.
  Qed.

  (** This is not true: it breaks in a spawn

  Let known_to_spawn_edge:
    forall t a es k l x y,
    SpawnEdges t es ->
    Safe t a k ->
    MT.MapsTo x l k ->
    List.In y l ->
    WellFormed k ->
    Reaches (Edge es) x y.
  Proof.
    induction t; intros. {
      inversion H0; subst.
      assert (X: x = a /\ l = nil) by eauto.
      destruct X; subst.
      inversion H2.
    }
    inversion H; subst; clear H.
    - inversion H0; subst; simpl in *; clear H0.
      inversion H10; subst; clear H10.
      simpl in *.
      (* --- *)
      assert (X:=H1).
      apply spawn_inv_maps_to in X.
      destruct X as [?|[(?,(?,(?,?)))|(?,(?,?))]]; repeat subst.
      + eauto.
      + destruct H2. {
          subst.
          apply edge_to_reaches.
          unfold  Edge; auto using in_eq.
        }
        apply spawn_mapsto_inv_1 in H1; auto.
        destruct H1 as (?,(He,?)).
        inversion He; clear He H6; subst.
        rename x into l.
        apply reaches_cons.
        eauto.
      + clear H4.
  Qed.
  *)

  (* The next thing we have to do is to define a relation R, such that
     if MT.MapsTo x l k /\ List.In y l -> x R y
     and then prove that this yields a <
   *)


  Lemma in_spawns_in_known:
    forall t x a vs k,
    Spawns t a vs ->
    Safe t a k ->
    List.In x vs ->
    MT.In x k.
  Proof.
    induction t; intros. {
      inversion H; subst.
      inversion H1.
      - subst.
        inversion H0; subst.
        eauto using make_mapsto, MT_Extra.mapsto_to_in.
      - inversion H2.
    }
    inversion H; subst; clear H; inversion H0; subst; clear H0; simpl; eauto.
    destruct H1.
    + subst.
      simpl.
      assert (x0 <> x). {
        intuition; subst.
        contradiction.
      }
      inversion H3; subst.
      apply MT_Extra.in_to_mapsto in H2.
      destruct H2 as (l', Hmt).
      assert (MT.MapsTo x l' (spawn x0 x k0)) by eauto using spawn_mapsto_neq.
      eauto using MT_Extra.mapsto_to_in.
    + simpl; eauto.
  Qed.

  Let make_is_well_formed:
    forall x,
    WellFormed (make x).
  Proof.
    intros.
    apply well_formed_def.
    - intros.
      apply make_inv_maps_to in H; destruct H; subst.
      auto.
    - intros.
      apply make_inv_maps_to in H; destruct H; subst.
      inversion H0.
  Qed.

  Let well_formed_not_refl:
    forall x l k,
    WellFormed k ->
    MT.MapsTo x l k ->
    ~ List.In x l.
  Proof.
    intros; inversion H; eauto.
  Qed.

  Lemma well_formed_range_in_dom:
    forall x y l k,
    WellFormed k ->
    MT.MapsTo x l k ->
    List.In y l ->
    MT.In y k.
  Proof.
    intros; inversion H; eauto.
  Qed.

  Let spawn_is_well_formed:
    forall x y k,
    WellFormed k ->
    ~ MT.In y k ->
    WellFormed (spawn x y k).
  Proof.
    intros.
    apply well_formed_def; intros. {
    intros.
    apply spawn_inv_maps_to in H1.
    destruct H1 as [?|[(?,(?,(?,?)))|(?,(?,?))]]; subst; auto.
    - eauto.
    - unfold not; intros.
      destruct H1.
      + subst.
        contradiction H0.
        eauto using MT_Extra.mapsto_to_in.
      + assert (~ List.In x x0) by eauto.
        contradiction.
    - unfold not; intros.
      contradiction H0.
      eauto using well_formed_range_in_dom.
    }
    apply spawn_inv_maps_to in H1.
    destruct H1 as [?|[(?,(?,(?,?)))|(?,(?,?))]]; subst; eauto using well_formed_range_in_dom.
    destruct H2; subst; eauto using MT_Extra.mapsto_to_in, well_formed_range_in_dom.
  Qed.
(*
  Let well_formed_inv_spawn:
    forall x y k,
    ~ MT.In y k ->
    WellFormed (spawn x y k) ->
    WellFormed k.
  Proof.
    intros.
    inversion H0.
    apply well_formed_def; intros.
    - destruct (TID.eq_dec t x), (TID.eq_dec t y); rewrite tid_eq_rw in *; auto; repeat subst.
      + apply spawn_mapsto_eq with (y:=y) in H3.
        apply well_formed_not_refl in H3; auto.
        contradiction H3; auto using in_eq.
      + apply spawn_mapsto_eq with (y:=y) in H3.
        apply well_formed_not_refl in H3; auto.
        unfold not; intros.
        contradiction H3; auto using in_cons.
      + assert (N: ~ MT.In y k) by eauto.
        contradiction N; eauto using MT_Extra.mapsto_to_in.
    - destruct (TID.eq_dec y0 x0); rewrite tid_eq_rw in *; auto; repeat subst.
      + eauto using MT_Extra.mapsto_to_in.
      + assert 
        assert (MT.In y (spawn x y k)). {
          apply H2 with (x:=x0) (l:=l).
        }

  Qed.
*)
  Let join_is_well_formed:
    forall x y l k,
    WellFormed k ->
    MT.MapsTo y l k ->
    ~ List.In x l ->
    WellFormed (join x y k).
  Proof.
    intros.
    apply well_formed_def.
    - intros.
      apply join_inv_maps_to in H2.
      destruct H2 as [?|(?,(?,(?,(?,(?,?)))))].
      + eauto.
      + subst.
        assert (x1 = l) by eauto using MT_Facts.MapsTo_fun; subst.
        unfold not; intros.
        apply in_app_iff in H4.
        destruct H4.
        * contradiction.
        * assert (~ List.In x x0) by eauto.
          contradiction.
    - intros.
      apply join_inv_maps_to in H2.
      destruct H2 as [?|(?,(?,(?,(?,(?,?)))))].
      + eauto using well_formed_range_in_dom.
      + subst.
        apply in_app_iff in H3; destruct H3; eauto using well_formed_range_in_dom.
  Qed.

  Lemma safe_to_well_formed:
    forall t x k,
    Safe t x k ->
    WellFormed k.
  Proof.
    induction t; intros. {
      inversion H; subst; auto.
    }
    inversion H; subst; clear H.
    destruct a;
    simpl;
    inversion H2; eauto.
  Qed.

  (* This does not hold: 
  Let known_to_spawn_edge:
    forall t a es k l x y,
    SpawnEdges t es ->
    Safe t a k ->
    MT.MapsTo x l k ->
    List.In y l ->
    Edge es (x, y).
  *)

End Defs.
End Known.

