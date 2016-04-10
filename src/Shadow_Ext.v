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

Section Shadow_Ext.

  Inductive mode := READ | WRITE.

  Structure access := {
    a_node : CG.node;
    a_mode : mode;
    a_mid: mid
  }.

  Definition access_history := list access.

  Definition is_write (a:access) :=
  match a_mode a with
  | WRITE => true
  | _ => false
  end.

  Definition is_read (a:access) :=
  match a_mode a with
  | READ => true
  | _ => false
  end.

  Definition ah_reads x ah := filter is_read (filter (fun a => Mid.eqb x (a_mid a)) ah).

  Definition ah_writes x ah := filter is_write (filter (fun a => Mid.eqb x (a_mid a)) ah).

  Section Defs.
  Variable ah:access_history.
  Variable cg:CG.computation_graph.

  Definition ah_add_access (r:mode) (t:tid) (m:mid) (ah:access_history) : access_history :=
  match CG.cg_lookup t cg with
  | Some n => {| a_mode := r; a_node := n; a_mid := m |} :: ah
  | _ => ah
  end.

  Definition ah_add_read := ah_add_access READ.
  Definition ah_add_write := ah_add_access WRITE.

  Inductive Reduces ah: Lang.effect -> access_history -> Prop :=
  | reduces_write:
    forall t m,
    Reduces ah (t, Lang.WRITE m) (ah_add_write t m ah)
  | reduces_read:
    forall t m,
    Reduces ah (t, Lang.READ m) (ah_add_read t m ah).

  Definition Access a t h := List.In {| a_mode:=a; a_node:=t; a_mid:=h|} ah. 

  Definition Writes t h := Access WRITE t h.

  Definition Reads t h := Access READ t h.

  Inductive CoAccess (x y:CG.node) (h:mid): Prop :=
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
