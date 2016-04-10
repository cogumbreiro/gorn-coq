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

Section Shadow.
  Structure access := {
    write_access: list CG.node;
    read_access: list CG.node
  }.

  Definition a_add_write n a := Build_access (n :: write_access a) (read_access a).

  Definition a_add_read n a := Build_access (write_access a) (n :: read_access a).

  Definition shadow := MM.t access.

  Definition sh_update (h:mid) (f: access->access) (sh:shadow) : shadow :=
  match MM.find h sh with
  | Some a => MM.add h (f a) sh
  | _ => sh
  end.

  Definition sh_read cg t h sh : shadow :=
  match CG.cg_lookup t cg with
  | Some n => sh_update h (a_add_read n) sh
  | _ => sh
  end.

  Definition sh_write cg t h sh : shadow :=
  match CG.cg_lookup t cg with
  | Some n => sh_update h (a_add_write n) sh
  | _ => sh
  end.

  Inductive Reduces cg: shadow -> Lang.effect -> shadow -> Prop :=
  | reduces_read:
    forall sh t h,
    Reduces cg sh (t,Lang.READ h) (sh_read cg t h sh)
  | sh_reduces_write:
    forall sh t h,
    Reduces cg sh (t,Lang.WRITE h) (sh_write cg t h sh)
  | reduces_skip:
    forall sh t o,
    Lang.is_m_op o = true ->
    Reduces cg sh (t,o) sh.

  Section Opts.
  Variable sh:shadow.

  Inductive Reads (n:CG.node) (h:mid) : Prop :=
  | reads_def:
    forall a,
    MM.MapsTo h a sh ->
    List.In n (read_access a) ->
    Reads n h.

  Inductive Writes (n:CG.node) (h:mid) : Prop :=
  | writes_def:
    forall a,
    MM.MapsTo h a sh ->
    List.In n (write_access a) ->
    Writes n h.

  Inductive Node n h : Prop :=
  | node_read:
    Reads n h ->
    Node n h
  | node_write:
    Writes n h ->
    Node n h.

  Inductive CoAccess (n1 n2:CG.node) (h:mid): Prop :=
  | co_access_def:
    Writes n1 h ->
    Node n2 h ->
    CoAccess n1 n2 h.

  Variable cg: CG.computation_graph.

  Inductive HasRace h : Prop :=
  | has_race_def:
    forall n1 n2,
    CoAccess n1 n2 h ->
    CG.MHP cg n1 n2 ->
    HasRace h.

  Inductive OrderedAccesses (lhs:list CG.node) (rhs:list CG.node): Prop :=
  | safe_reads_def:
    (forall x y, List.In x lhs -> List.In y rhs -> CG.Ordered cg x y) ->
    OrderedAccesses lhs rhs.

  Inductive RaceFree h : Prop :=
  | race_free_def:
      forall a,
      MM.MapsTo h a sh ->
      OrderedAccesses (read_access a) (write_access a) ->
      OrderedAccesses (write_access a) (write_access a) ->
      RaceFree h.

  Inductive RaceFreeMemory : Prop :=
  | race_free_memory_def:
    (forall h, MM.In h sh -> RaceFree h) ->
    RaceFreeMemory.

  Inductive Racy : Prop :=
    racy_def:
      forall h,
      HasRace h ->
      Racy.

  End Opts.

  Section Props.

  Let reads_to_in_read_access:
    forall sh n h a,
    Reads sh n h ->
    MM.MapsTo h a sh ->
    List.In n (read_access a).
  Proof.
    intros.
    inversion H; subst; clear H.
    assert (a0 = a) by eauto using MM_Facts.MapsTo_fun.
    subst; auto.
  Qed.

  Let writes_to_in_write_access:
    forall sh n h a,
    Writes sh n h ->
    MM.MapsTo h a sh ->
    List.In n (write_access a).
  Proof.
    intros.
    inversion H; subst; clear H.
    assert (a0 = a) by eauto using MM_Facts.MapsTo_fun.
    subst; auto.
  Qed.

  Let in_read_access_add_read:
    forall n a n',
    List.In n (read_access a) ->
    List.In n (read_access (a_add_read n' a)).
  Proof.
    intros.
    destruct a; simpl in *.
    auto.
  Qed.

  Let in_read_access_add_write:
    forall n a n',
    List.In n (read_access a) ->
    List.In n (read_access (a_add_write n' a)).
  Proof.
    intros.
    destruct a; simpl in *.
    auto.
  Qed.

  Let in_write_access_add_read:
    forall n a n',
    List.In n (write_access a) ->
    List.In n (write_access (a_add_read n' a)).
  Proof.
    intros.
    destruct a; simpl in *.
    auto.
  Qed.

  Let in_write_access_add_write:
    forall n a n',
    List.In n (write_access a) ->
    List.In n (write_access (a_add_write n' a)).
  Proof.
    intros.
    destruct a; simpl in *.
    auto.
  Qed.
(*
  Let reads_preservation_read:
    forall cg t sh n h h',
    Reads sh n h ->
    Reads (sh_read cg t h' sh) n h.
  Proof.
    intros.
    unfold sh_read.
    unfold CG.cg_lookup.
    destruct (MT_Extra.find_rw t (CG.cg_tasks cg)) as [(rw,?)|(e,(rw,?))].
    - rewrite rw.
      auto.
    - rewrite rw; clear rw.
      unfold sh_update.
      destruct (MM_Extra.find_rw h' sh) as [(rw,?)|(a,(rw,?))]; rewrite rw; clear rw.
      + assumption.
      + destruct (MID.eq_dec h' h).
        * rewrite mid_eq_rw in *; subst.
          eauto using reads_def, MM.add_1.
        * rewrite mid_eq_rw in *; subst.
          inversion H.
          eauto using reads_def, MM.add_2.
  Qed.

  Let reads_preservation_write:
    forall cg t sh n h h',
    Reads sh n h ->
    Reads (sh_write cg t h' sh) n h.
  Proof.
    intros.
    unfold sh_write.
    unfold CG.cg_lookup.
    destruct (MT_Extra.find_rw t (CG.cg_tasks cg)) as [(rw,?)|(e,(rw,?))].
    - rewrite rw.
      auto.
    - rewrite rw; clear rw.
      unfold sh_update.
      destruct (MM_Extra.find_rw h' sh) as [(rw,?)|(a,(rw,?))]; rewrite rw; clear rw.
      + assumption.
      + destruct (MID.eq_dec h' h).
        * rewrite mid_eq_rw in *; subst.
          eauto using reads_def, MM.add_1.
        * rewrite mid_eq_rw in *; subst.
          inversion H.
          eauto using reads_def, MM.add_2.
  Qed.

  Let writes_preservation_read:
    forall cg t sh n h h',
    Writes sh n h ->
    Writes (sh_read cg t h' sh) n h.
  Proof.
    intros.
    unfold sh_read.
    unfold CG.cg_lookup.
    destruct (MT_Extra.find_rw t (CG.cg_tasks cg)) as [(rw,?)|(e,(rw,?))].
    - rewrite rw.
      auto.
    - rewrite rw; clear rw.
      unfold sh_update.
      destruct (MM_Extra.find_rw h' sh) as [(rw,?)|(a,(rw,?))]; rewrite rw; clear rw.
      + assumption.
      + destruct (MID.eq_dec h' h).
        * rewrite mid_eq_rw in *; subst.
          eauto using writes_def, MM.add_1.
        * rewrite mid_eq_rw in *; subst.
          inversion H.
          eauto using writes_def, MM.add_2.
  Qed.

  Let writes_preservation_write:
    forall cg t sh n h h',
    Writes sh n h ->
    Writes (sh_write cg t h' sh) n h.
  Proof.
    intros.
    unfold sh_write.
    unfold CG.cg_lookup.
    destruct (MT_Extra.find_rw t (CG.cg_tasks cg)) as [(rw,?)|(e,(rw,?))].
    - rewrite rw.
      auto.
    - rewrite rw; clear rw.
      unfold sh_update.
      destruct (MM_Extra.find_rw h' sh) as [(rw,?)|(a,(rw,?))]; rewrite rw; clear rw.
      + assumption.
      + destruct (MID.eq_dec h' h).
        * rewrite mid_eq_rw in *; subst.
          eauto using writes_def, MM.add_1.
        * rewrite mid_eq_rw in *; subst.
          inversion H.
          eauto using writes_def, MM.add_2.
  Qed.

  Let co_access_preservation_read:
    forall cg t sh n1 n2 h h',
    CoAccess sh n1 n2 h ->
    CoAccess (sh_read cg t h' sh) n1 n2 h.
  Proof.
    intros.
    destruct H.
    inversion H0; eauto using co_access_def, node_read, node_write.
  Qed.

  Let co_access_preservation_write:
    forall cg t sh n1 n2 h h',
    CoAccess sh n1 n2 h ->
    CoAccess (sh_write cg t h' sh) n1 n2 h.
  Proof.
    intros.
    destruct H.
    inversion H0; eauto using co_access_def, node_read, node_write.
  Qed.

  Lemma co_access_preservation:
    forall sh o sh' n1 n2 h cg,
    CoAccess sh n1 n2 h ->
    Reduces cg sh o sh' ->
    CoAccess sh' n1 n2 h.
  Proof.
    intros.
    inversion H0; subst; clear H0; eauto.
  Qed.
*)
  End Props.
End Shadow.
