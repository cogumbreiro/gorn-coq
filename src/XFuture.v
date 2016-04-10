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

  Inductive Reduces: state -> state -> Prop :=
  | reduces_def:
    forall s s' cg sh o cg' sh',
    Lang.Reduces s o s' ->
    CG.Reduces cg o cg' ->
    Shadow_Ext.Reduces cg sh o sh' ->
    Reduces {| r_state:=s; r_cg:=cg; r_ah:=sh|} {|r_state:=s';r_cg:=cg'; r_ah:=sh'|}.

  Inductive RF_Reduces: state -> state -> Prop :=
  | rf_reduces_def:
    forall s s',
    RaceFree (r_ah s) (r_cg s) ->
    RaceFree (r_ah s') (r_cg s') ->
    Reduces s s' ->
    RF_Reduces s s'.
    

End Races.
