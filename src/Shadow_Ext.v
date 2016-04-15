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

Require Lang.
Require CG.

Module Trace.
  Inductive mode := READ | WRITE.
  Structure access := {
    a_t : mode;
    a_src : CG.Node.node;
    a_dst : mid
  }.

  Definition e_to_a cg (e:Lang.effect) :=
  match e with
  | (t, Lang.WRITE m) =>
    match CG.cg_lookup t cg with
    | Some n => Some {| a_t:= WRITE; a_src:=n; a_dst:= m |}
    | _ => None
    end
  | (t, Lang.READ m) =>
    match CG.cg_lookup t cg with
    | Some n => Some {| a_t:= READ; a_src:=n; a_dst:= m |}
    | _ => None
    end
  | _ => None
  end.

End Trace.

Section Shadow_Ext.
  Import Trace.

  Definition access_history := list (option access).

  Definition mode_eq m1 m2 :=
  match (m1, m2) with
  | (READ, READ) => true
  | (WRITE, WRITE) => true
  | _ => false
  end.

  Definition a_match x m (a:option access) :=
  match a with
  | Some a =>
    andb (Mid.eqb x (a_dst a)) (mode_eq m (a_t a))
  | None => false
  end.

  Definition ah_filter (x:mid) (m:mode) (ah:access_history) := filter (a_match x m) ah.

  Definition ah_reads (x:mid) (ah:access_history) := ah_filter x READ ah.

  Definition ah_writes x ah := ah_filter x READ ah.

  Section Defs.

  Definition is_access (o:Lang.op) :=
  match o with
  | Lang.WRITE _ => true
  | Lang.READ _ => true
  | _ => false
  end.

  Inductive AccessPre cg : Lang.effect -> Prop :=
  | access_pre_true:
    forall x o,
    MT.In x (CG.cg_nodes cg) ->
    is_access o = true ->
    AccessPre cg (x, o)
  | access_pre_false:
    forall x o,
    is_access o = false ->
    AccessPre cg (x, o).

  Definition ah_add cg e ah := e_to_a cg e::ah.

  Inductive AccessHistory: list CG.computation_graph -> list Lang.effect -> access_history -> Prop :=
  | access_history_nil:
    forall cg,
    AccessHistory (cg::nil) nil nil
  | access_of_cons_read:
    forall t (ah:access_history) l cg e,
    AccessHistory l t ah ->
    AccessPre cg e ->
    AccessHistory (cg::l) (e::t) (ah_add cg e ah).

  Variable ah:access_history.

  Variable cg:CG.computation_graph.



  Inductive Reduces cg ah e: access_history -> Prop :=
  | reduces_write:
    AccessPre cg e ->
    Reduces cg ah e (ah_add cg e ah).

  Definition Access a t h := List.In (Some {| a_t:=a; a_src:=t; a_dst:=h|}) ah. 

  Definition Writes t h := Access WRITE t h.

  Definition Reads t h := Access READ t h.

  Inductive CoAccess (x y:CG.Node.node) (h:mid): Prop :=
  | co_access_def:
    forall a,
    Writes x h ->
    Access a y h ->
    CoAccess x y h.

  Inductive HasRace h : Prop :=
  | has_race_def:
    forall n1 n2,
    CoAccess n1 n2 h ->
    CG.MHP cg n1 n2 ->
    HasRace h.

  Inductive OrderedAccesses h: Prop :=
  | safe_reads_def:
    (forall x y,
      Reads x h ->
      Writes y h ->
      CG.Ordered cg x y) ->
    (forall x y,
      Writes x h ->
      Writes y h ->
      CG.Ordered cg x y) ->
    OrderedAccesses h.

  Inductive RaceFree : Prop :=
  | race_free_def:
    (forall h, OrderedAccesses h) ->
    RaceFree.

  Inductive Racy : Prop :=
    racy_def:
      forall h,
      HasRace h ->
      Racy.
  End Defs.

End Shadow_Ext.
