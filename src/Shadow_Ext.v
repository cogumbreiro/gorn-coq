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

  Inductive RaceFreeAccess cg : option access -> option access -> Prop :=
  | race_free_access_lhs_none:
    forall a,
    RaceFreeAccess cg a None
  | race_free_access_rhs_none:
    forall a,
    RaceFreeAccess cg None a
  | race_free_access_mismatch:
    forall a b,
    a_dst a <> a_dst b ->
    RaceFreeAccess cg (Some a) (Some b)
  | race_free_access_read_read:
    forall a b,
    a_dst a = a_dst b ->
    a_t a = READ ->
    a_t b = READ ->
    RaceFreeAccess cg (Some a) (Some b)
  | race_free_access_lhs_write:
    forall a b,
    a_dst a = a_dst b ->
    a_t a = WRITE ->
    CG.Ordered cg (a_src a) (a_src b) ->
    RaceFreeAccess cg (Some a) (Some b)
  | race_free_access_rhs_write:
    forall a b,
    a_dst a = a_dst b ->
    a_t b = WRITE ->
    CG.Ordered cg (a_src a) (a_src b) ->
    RaceFreeAccess cg (Some a) (Some b).

  Definition RaceFreeCons cg ah a  := Forall (RaceFreeAccess cg a) ah.

  Definition ah_add cg e ah := e_to_a cg e::ah.

  Inductive AccessHistory: list CG.computation_graph -> list Lang.effect -> access_history -> Prop :=
  | access_history_nil:
    forall cg,
    AccessHistory (cg::nil) nil nil
  | access_of_cons:
    forall t (ah:access_history) l cg e,
    AccessHistory l t ah ->
    AccessPre cg e ->
    AccessHistory (cg::l) (e::t) (ah_add cg e ah).

  Inductive RaceFreeAccessHistory: list CG.computation_graph -> list Lang.effect -> access_history -> Prop :=
  | race_free_access_history_nil:
    forall cg,
    RaceFreeAccessHistory (cg::nil) nil nil
  | race_free_access_of_cons:
    forall t (ah:access_history) l cg e,
    RaceFreeAccessHistory l t ah ->
    AccessPre cg e ->
    RaceFreeCons cg ah (e_to_a cg e) ->
    RaceFreeAccessHistory (cg::l) (e::t) (e_to_a cg e::ah).

  Inductive RaceFreeReduces cg ah e: access_history -> Prop :=
  | race_free_reduces_def:
    AccessPre cg e ->
    RaceFreeCons cg ah (e_to_a cg e) ->
    RaceFreeReduces cg ah e (e_to_a cg e::ah).

  Inductive Reduces cg ah e: access_history -> Prop :=
  | reduces_write:
    AccessPre cg e ->
    Reduces cg ah e (ah_add cg e ah).


  Variable cg:CG.computation_graph.

  Variable ah:access_history.

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
