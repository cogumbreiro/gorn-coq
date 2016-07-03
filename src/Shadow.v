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

    Inductive MaxWrite a (ah:access_history) cg : Prop :=
    | max_write_def:
      forall l,
      MM.MapsTo h l ah ->
      IsWrite a ->
      List.In a l->
      Forall (fun b => IsWrite b -> Le cg (a_when b) (a_when a)) l ->
      MaxWrite a ah cg.

    Inductive LastWrite (n:node) (x:A) ah cg : Prop :=
    | last_write_def:
      forall (a:access),
      a_when a = n ->
      Write a x ->
      MaxWrite a ah cg ->
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

Section Props.

  Require Import Aniceto.Graphs.Graph.
  Require Import Aniceto.Graphs.FGraph.
(*
  Lemma last_write_inv_cons:
    forall (A:Type) r (d:A) g x (vs:list tid) es n,
    Node.MapsTo x n vs ->
    LtEdges (cg_edges (x :: vs, C (n, fresh vs) :: es)) ->
    DAG (FGraph.Edge (cg_edges (x :: vs, C (n, fresh vs) :: es))) ->
    LastWrite r n d g (x :: vs, C (n, fresh vs) :: es) ->
    LastWrite r n d g (vs, es).
  Proof.
    intros.
    unfold cg_edges in *; simpl in *.
    inversion H2; subst.
    apply last_write_def with (a:=a); auto.
    intros.
    assert (Hx: b = a \/ HB (x :: vs, C (nx, nx') :: es) (a_when b) (a_when a)) by auto.
    destruct Hx as [?|Hx]; auto; clear H4.
    assert (NODE.lt (a_when b) (a_when a)) by eauto using hb_to_lt.
    apply hb_to_fgraph in Hx.
    inversion Hx as (w, Hw).
    simpl in *.
    destruct (in_dec (edge_eq_dec node_eq_dec) (nx,nx') w). {
      destruct w. {
        apply walk2_nil_inv in Hw.
        contradiction.
      }
      destruct p as (v1,v2).
      assert (v1 = a_when b) by eauto using walk2_inv_eq_fst; subst.
      destruct w. {
        assert (v2 = a_when a) by eauto using walk2_inv_eq_snd; subst.
        destruct (node_eq_dec nx (a_when b)), (node_eq_dec nx' (a_when a)).
        - subst.
          clear i.
      }
      - subst.
      apply Graph.walk2_split with (a0:=nx) (b0:=nx') in Hw; auto.
      destruct Hw as [Heq|[?|?]].
      - subst.
    }
    
  Qed.
*)
End Props.


  Ltac simpl_red :=
  match goal with
    | [ H1: Reduces _ _ (_, {| a_when := _; a_what := _|}) _ |- _ ] =>
      inversion H1; subst; clear H1
  end.
