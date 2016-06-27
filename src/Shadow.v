Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import HJ.Tid.
Require Import HJ.Mid.
Require Import HJ.Cid.
Require Import HJ.Var.
Require Import HJ.Dep.
Require Import Node.

(* ----- end of boiler-plate code ---- *)

Set Implicit Arguments.

Require Import Aniceto.Graphs.DAG.
Require Import Coq.Relations.Relation_Operators.
Require Aniceto.Graphs.Graph.

Require Import Coq.Structures.OrderedTypeEx.

Require CG.

Section Defs.
  (** There are two kinds of events we observe: reading and writing to shared memory. *)

  Variable A:Type.

  (**
    An represents the kind of access the node in the CG responsible for the access
    and the target variable.
   *)

  Inductive op := READ | WRITE : A -> op | ALLOC : A -> op.

  Structure access := {
    a_when : node;
    a_what : op
  }.

Notation WR n x := {| a_when := n; a_what := WRITE x|}.
Notation RD n := {| a_when := n; a_what := READ|}.
Notation AL n x := {| a_when := n; a_what := ALLOC x|}.

  Inductive IsRead a : Prop :=
  | read_def:
    a_what a = READ ->
    IsRead a.

  Inductive Write a (x:A) : Prop :=
  | write_write:
    a_what a = WRITE x ->
    Write a x
  | write_alloc:
    a_what a = ALLOC x ->
    Write a x.

  Inductive IsWrite a : Prop :=
  | write_def:
    forall x,
    Write a x ->
    IsWrite a.

  Definition access_history := MM.t (list access).

  (** Two accesses are racy *)

  Inductive RacyAccess cg : access -> access -> Prop :=
  | racy_access_def:
    forall a b,
    a_when a <> a_when b ->
    (IsWrite a \/ IsWrite b) ->
    CG.MHP cg (a_when a) (a_when b) ->
    RacyAccess cg a b.

  Definition RaceFreeAccess cg a b := ~ RacyAccess cg a b.

  Definition RaceFreeCons cg ah a  := Forall (RaceFreeAccess cg a) ah.

Section History.

  Require Import CG.

  Inductive Reduces (cg:computation_graph) ah: (mid * access) -> access_history -> Prop :=
  | reduces_write:
    forall n x y l,
    MM.MapsTo x l ah ->
    Reduces cg ah (x, WR n y) (MM.add x (WR n y::l) ah)
  | reduces_read:
    forall n x l,
    MM.MapsTo x l ah ->
    Reduces cg ah (x, {|a_when:=n;a_what:=READ|}) (MM.add x (RD n::l) ah)
  | reduces_alloc:
    forall x n y,
    ~ MM.In x ah ->
    Reduces cg ah (x, AL n y) (MM.add x (AL n y::nil) ah).

  Section Access.

    Variable h:mid.

    Inductive Access (a:access) (ah:access_history) : Prop :=
    | access_def:
      forall l,
      MM.MapsTo h l ah ->
      List.In a l ->
      Access a ah.

    Let Le cg (a:access) b := a = b \/ CG.HB cg (a_when a) (a_when b).

    Inductive LastWrite (n:node) (x:A) ah cg : Prop :=
    | last_write_def:
      forall (a:access),
      Access a ah ->
      a_when a = n ->
      Write a x ->
      (forall b, Access b ah -> IsWrite b -> Le cg b a) ->
      LastWrite n x ah cg.

    Inductive MapsTo (x:A) ah cg : Prop :=
    | maps_to_def:
      forall n,
      LastWrite n x ah cg ->
      MapsTo x ah cg.

    Inductive HasRace ah cg : Prop :=
    | has_race_def:
      forall a b,
      Access a ah ->
      Access b ah ->
      (IsWrite a \/ IsWrite b) ->
      CG.MHP cg (a_when a) (a_when b) ->
      HasRace ah cg.

    Inductive RaceFreeRef ah cg: Prop :=
    | race_free_ref_def:
      (forall x y,
        Access x ah ->
        Access y ah ->
        IsWrite y ->
        x <> y ->
        CG.Comparable cg (a_when x) (a_when y)) ->
      RaceFreeRef ah cg.
  End Access.

  Variable ah:access_history.

  Variable cg:CG.computation_graph.

  Inductive RaceFree : Prop :=
  | race_free_def:
    (forall h, RaceFreeRef h ah cg) ->
    RaceFree.

  Inductive Racy : Prop :=
    racy_def:
      forall h,
      HasRace h ah cg ->
      Racy.
  End History.

End Defs.

