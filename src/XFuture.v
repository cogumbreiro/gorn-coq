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

Require Import Shadow_Ext.

Module Races.

  Structure state := {
    r_state: Lang.state;
    r_cg: CG.computation_graph;
    r_ah: access_history
  }.

  Inductive Reduces: state -> Lang.effect -> state -> Prop :=
  | reduces_def:
    forall s s' cg sh o cg' sh',
    Lang.Reduces s o s' ->
    CG.Reduces cg o cg' ->
    Shadow_Ext.Reduces cg sh o sh' ->
    Reduces {| r_state:=s; r_cg:=cg; r_ah:=sh|} o {|r_state:=s';r_cg:=cg'; r_ah:=sh'|}.

  Inductive RaceFreeReduces: state -> Lang.effect -> state -> Prop :=
  | race_free_reduces_def:
    forall s s' cg sh o cg' sh',
    Lang.Reduces s o s' ->
    CG.Reduces cg o cg' ->
    Shadow_Ext.Reduces cg sh o sh' ->
    RaceFreeReduces {| r_state:=s; r_cg:=cg; r_ah:=sh|} o {|r_state:=s';r_cg:=cg'; r_ah:=sh'|}.

  Inductive ReducesTrace: state -> list Lang.effect -> state -> Prop :=
  | reduces_trace_nil:
    forall s,
    ReducesTrace s nil s
  | reduces_trace_cons:
    forall s s' s'' e t,
    ReducesTrace s t s' ->
    RaceFreeReduces s' e s'' ->
    ReducesTrace s (e::t) s''.

End Races.
