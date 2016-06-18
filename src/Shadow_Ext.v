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

Module Trace.

  (** There are two kinds of events we observe: reading and writing to shared memory. *)

  Inductive mode := READ | WRITE.

  (**
    An represents the kind of access the node in the CG responsible for the access
    and the target variable.
   *)

  Structure access := {
    a_t : mode;           (* how *)
    a_src : node; (* when *)
    a_dst : mid           (* what *)
  }.

  Definition access_history := list access.

End Trace.

Section Shadow_Ext.
  Import Trace.

  (** An access history is just a sequence of optional accesses; none when 
    the event is neither a read nor a write. *)

  (** compares if two access modes. *)

  Definition mode_eq m1 m2 :=
  match (m1, m2) with
  | (READ, READ) => true
  | (WRITE, WRITE) => true
  | _ => false
  end.

  (** Matches what and how *)

  Definition a_match x m (a:access) :=
  andb (Mid.eqb x (a_dst a)) (mode_eq m (a_t a)).

  (** Returns any access that matches what and how. *)

  Definition ah_filter (x:mid) (m:mode) (ah:access_history) := filter (a_match x m) ah.

  (** Returns all reads on a certain variable. *)

  Definition ah_reads (x:mid) (ah:access_history) := ah_filter x READ ah.

  (** Returns all writes on a certain variable *)

  Definition ah_writes x ah := ah_filter x READ ah.

  Section Defs.

  Inductive LastWrite cg ah (a:access) (m:mid) : Prop :=
  | last_write_def:
    a_t a = WRITE ->
    a_dst a = m ->
    (forall a', a_t a' = WRITE -> List.In (Some a') ah -> CG.HB cg (a_src a') (a_src a)) ->
    LastWrite cg ah a m.

  (** Two accesses are racy *)

  Inductive RacyAccess cg : access -> access -> Prop :=
  | racy_access_def:
    forall a b,
    a_src a <> a_src b ->
    a_dst a = a_dst b ->
    (a_t a = WRITE \/ a_t b = WRITE) ->
    CG.MHP cg (a_src a) (a_src b) ->
    RacyAccess cg a b.

  (** Two accesses are race-free. *)

  Definition RaceFreeAccess cg a b := ~ RacyAccess cg a b.

  (** An access can be appended to the access-history, yielding a race-free history. *)

  Definition RaceFreeCons cg ah a  := Forall (RaceFreeAccess cg a) ah.

  Variable cg:CG.computation_graph.

  Variable ah:access_history.

  Definition Access a t h := List.In {| a_t:=a; a_src:=t; a_dst:=h|} ah. 

  Definition Writes t h := Access WRITE t h.

  Definition Reads t h := Access READ t h.

  Inductive CoAccess (x y:node) (h:mid): Prop :=
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

  Inductive RaceFreeRef h: Prop :=
  | race_free_ref_def:
    (forall x a y,
      Access a x h ->
      Writes y h ->
      x <> y ->
      CG.Comparable cg x y) ->
    RaceFreeRef h.

  Inductive RaceFree : Prop :=
  | race_free_def:
    (forall h, RaceFreeRef h) ->
    RaceFree.

  Inductive Racy : Prop :=
    racy_def:
      forall h,
      HasRace h ->
      Racy.
  End Defs.

  Let race_free_inv_1:
    forall cg x y t1 t2 h,
    RaceFreeAccess cg
      {| a_t := t1; a_src := x; a_dst := h |}
      {| a_t := t2; a_src := y; a_dst := h |} ->
    x <> y ->
    (t1 = WRITE \/ t2 = WRITE) ->
    CG.Comparable cg x y.
  Proof.
    unfold RaceFreeAccess.
    intros.
    destruct (CG.hb_dec cg x y).
    - auto using CG.comparable_left_right.
    - auto using CG.comparable_right_left.
    - contradiction.
    - contradiction H.
      auto using racy_access_def.
  Qed.

  Let race_free_ref_to_race_free_access:
    forall n1 n2 t1 t2 h cg ah,
    RaceFreeRef cg ah h ->
    In {| a_t := t1; a_src := n1; a_dst := h |} ah ->
    In {| a_t := t2; a_src := n2; a_dst := h |} ah ->
    RaceFreeAccess cg
      {| a_t := t1; a_src := n1; a_dst := h |}
      {| a_t := t2; a_src := n2; a_dst := h |}.
  Proof.
    intros.
    inversion H.
    unfold RaceFreeAccess.
    unfold not; intros.
    inversion H3; simpl in *; subst; clear H5.
    destruct H6; subst; assert (CG.Comparable cg n1 n2) by eauto using CG.comparable_symm;
    apply CG.comparable_to_not_mhp in H5; contradiction.
  Qed.

  Let race_free_access_ref_neq:
    forall t1 t2 n1 n2 h1 h2 cg,
    h1 <> h2 ->
    RaceFreeAccess cg
       {| a_t := t1; a_src := n1; a_dst := h1 |}
       {| a_t := t2; a_src := n2; a_dst := h2 |}.
  Proof.
    intros.
    unfold RaceFreeAccess; intuition.
    inversion H0; simpl in *; subst.
    contradiction H; auto.
  Qed.

  Let race_free_to_race_free_access:
    forall ah cg a1 a2,
    RaceFree cg ah ->
    In a1 ah ->
    In a2 ah ->
    RaceFreeAccess cg a1 a2.
  Proof.
    intros.
    inversion H.
    destruct a1, a2; auto.
    destruct (MID.eq_dec a_dst0 a_dst1); rewrite mid_eq_rw in *; auto.
    subst.
    eauto.
  Qed.

  Lemma race_free_cons:
    forall cg ah a,
    RaceFree cg ah ->
    RaceFreeCons cg ah a ->
    RaceFree cg (a::ah).
  Proof.
    intros.
    apply race_free_def.
    intros.
    apply race_free_ref_def.
    intros.
    unfold RaceFreeCons in *.
    destruct H1.
    - subst.
      inversion H2; clear H2.
      + inversion H1; subst; clear H1.
        contradiction H3; auto.
      + rewrite Forall_forall in *.
        apply H0 in H1.
        apply race_free_inv_1 in H1; auto.
    - inversion H2; clear H2.
      + subst.
        rewrite Forall_forall in *.
        apply H0 in H1.
        apply race_free_inv_1 in H1; auto using CG.comparable_symm.
      + assert (X: RaceFreeAccess cg
           {| a_t := a0; a_src := x; a_dst := h |}
           {| a_t := WRITE; a_src := y; a_dst := h |}) by eauto.
        apply race_free_inv_1 in X; auto.
  Qed.

End Shadow_Ext.
(*
Module Lang.
  Import Trace.

  (** Checks if a language event is either a read or a write. *)

  Definition is_access (o:Lang.op) :=
  match o with
  | Lang.WRITE _ => true
  | Lang.READ _ => true
  | _ => false
  end.

  (**
    Converts an event from the language to an event we can interpret.
    *)

  Definition e_to_a cg (e:Lang.effect) : option access :=
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

  Definition effects_to_ah_0 cg : list Lang.effect -> access_history := List.omap (e_to_a cg).

  Definition ah_add cg e ah := e_to_a cg e::ah.
End Lang.

*)