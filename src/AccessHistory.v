Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.Relations.Relation_Operators.

Require Import Aniceto.Graphs.DAG.
Require Import Aniceto.Graphs.Graph.
Require Import Aniceto.Graphs.FGraph.

Require Import HJ.Mid.


(* ----- end of boiler-plate code ---- *)

Set Implicit Arguments.

Section Defs.
  (** There are two kinds of events we observe: reading and writing to shared memory. *)

  Variable A:Type.
  Variable E:Type.
  Variable Lt: E -> E -> Prop.

  (**
    An represents the kind of access the node in the CG responsible for the access
    and the target variable.
   *)
  Inductive op_type := READ | WRITE | ALLOC.

  Definition op := (op_type * A) % type.

  Notation payload := (option A).

  Definition access := (E * payload) % type.

  Definition a_when := @fst E payload.
  Definition a_what := @snd E payload.

  Notation HB a b := (Lt (a_when a) (a_when b)).
  Notation MHP a b := (~ HB a b /\ ~ HB b a).
  Notation HBE a b := (HB a b \/ a = b).

  Inductive HasData : payload -> Prop :=
  | has_data_def:
    forall x,
    HasData (Some x).

  Definition Write a := HasData (a_what a).

  Definition Read a := ~ Write a.

  Definition access_history := MM.t (list access).

  (** Two accesses are racy *)

  Inductive RacyAccess : access -> access -> Prop :=
  | racy_access_def:
    forall a b,
    a_when a <> a_when b ->
    (Write a \/ Write b) ->
    MHP a b ->
    RacyAccess a b.

  Definition RaceFreeAccess a b := ~ RacyAccess a b.

  Definition ForallWrites (P : access -> Prop) l : Prop :=
    forall a,
    List.In a l ->
    Write a ->
    P a.

  Definition ForallReads (P: access -> Prop) l : Prop :=
    forall a,
    List.In a l ->
    Read a ->
    P a.

  Inductive LastWrite (a:access) (l:list access) : Prop :=
  | last_write_def:
    Write a ->
    List.In a l->
    ForallWrites (fun b=>HBE b a) l ->
    LastWrite a l.

  Inductive MapsTo r (x:A) ah : Prop :=
  | maps_to_def:
    forall a l,
    MM.MapsTo r l ah ->
    LastWrite a l ->
    a_what a = Some x ->
    MapsTo r x ah.

  Definition RaceFreeHistory ah :=
    forall r l a b,
    MM.MapsTo r l ah ->
    List.In a l ->
    List.In b l ->
    RaceFreeAccess a b.

  (** A write-safe access happens before all writes *)

  Inductive WriteSafe a l : Prop :=
  | write_safe_def:
    forall w,
    (* take the last-write *)
    LastWrite w l ->
    (* the access must succeed the last-write *)
    HB w a ->
    WriteSafe a l.

  (** A read-safe happens before all reads. *)

  Definition ReadSafe a l := ForallReads (fun b => HB b a) l.

  Inductive RaceFreeAdd: access_history -> (mid * E * op) -> access_history -> Prop :=
  | race_free_add_alloc:
    forall g r d n,
    (* update the shared memory to record the read *)
    ~ MM.In r g ->
    RaceFreeAdd g (r, n, (ALLOC, d)) (MM.add r ((n, Some d)::nil) g)

  | race_free_read:
    forall g l n r a d,
    (* update the shared memory to record the read *)
    MM.MapsTo r l g ->
    WriteSafe (n, None) l ->
    LastWrite a l ->
    a_what a = Some d ->
    RaceFreeAdd g (r, n, (READ, d)) (MM.add r ((n, None)::l) g)

  | race_free_write:
    forall g r d n l,
    (* update the shared memory to record the read *)
    MM.MapsTo r l g ->
    (* make sure the write is safe with other writes in l *)
    WriteSafe (n, Some d) l ->
    (* the write must also be safe wrt all reads *)
    ReadSafe (n, Some d) l ->
    RaceFreeAdd g (r, n, (WRITE, d)) (MM.add r ((n, Some d)::l) g).

  Ltac expand H := inversion H; subst; clear H.

  Variable lt_trans:
    forall x y z,
    Lt x y ->
    Lt y z ->
    Lt x z.

  Variable lt_irrefl:
    forall x,
    ~ Lt x x.

  Lemma racy_access_irrefl:
    forall (a:access),
    ~ RacyAccess a a.
  Proof.
    unfold not; intros.
    inversion H.
    subst.
    contradiction H0.
    trivial.
  Qed.

  Lemma race_free_access_refl:
    forall (a:access),
    RaceFreeAccess a a.
  Proof.
    unfold RaceFreeAccess.
    auto using racy_access_irrefl.
  Qed.

  Notation Ordered a b := (HB a b \/ HB b a).

  Lemma race_free_access_read:
    forall (a:access) b,
    Read a ->
    Read b ->
    RaceFreeAccess a b.
  Proof.
    intros.
    unfold RaceFreeAccess, not; intros.
    inversion H1.
    destruct H3; auto.
  Qed.

  Lemma race_free_access_hb:
    forall a b,
    HB a b ->
    RaceFreeAccess a b.
  Proof.
    unfold RaceFreeAccess, not; intros.
    inversion H0; subst; clear H0.
    destruct H3.
    contradiction.
  Qed.

  Lemma race_free_access_hbe:
    forall a b,
    HBE a b ->
    RaceFreeAccess a b.
  Proof.
    intros.
    destruct H.
    - auto using race_free_access_hb.
    - subst.
      auto using race_free_access_refl.
  Qed.

  Let mhp_symm:
    forall a b,
    MHP a b ->
    MHP b a.
  Proof.
    intros.
    destruct H.
    auto.
  Qed.

  Lemma racy_access_symm:
    forall a b,
    RacyAccess a b ->
    RacyAccess b a.
  Proof.
    intros.
    inversion H; subst.
    destruct H1;
    apply racy_access_def; auto.
  Qed.

  Lemma race_free_access_symm:
    forall a b,
    RaceFreeAccess a b ->
    RaceFreeAccess b a.
  Proof.
    unfold RaceFreeAccess, not in *; intros.
    apply racy_access_symm  in H0; contradiction.
  Qed.

  Inductive OrderedAdds : list access -> Prop :=
  | ordered_adds_nil:
    forall a,
    Write a ->
    OrderedAdds (a :: nil)
  | ordered_adds_read:
    forall a l,
    Read a ->
    OrderedAdds l ->
    WriteSafe a l ->
    OrderedAdds (a :: l)
  | ordered_adds_write:
    forall a l,
    Write a ->
    OrderedAdds l ->
    WriteSafe a l ->
    ReadSafe a l ->
    OrderedAdds (a :: l).

  Inductive Last (a:access) : list access -> Prop :=
  | last_nil:
    Write a ->
    Last a (a :: nil)
  | last_cons_read:
    forall b l,
    Last a l ->
    a_what b = None ->
    Last a (b :: l)
  | last_cons_write:
    forall l b,
    Last b l ->
    Write a ->
    Last a (a::l).

  Definition OrderedAccessHistory (ah:access_history) :=
    forall r l,
    MM.MapsTo r l ah ->
    OrderedAdds l.

  Let write_some:
    forall n d,
    Write (n, Some d).
  Proof.
    intros.
    apply has_data_def.
  Qed.

  Let read_none:
    forall n,
    Read (n, None).
  Proof.
    intros.
    unfold Read, not; intros.
    inversion H.
  Qed.

  Let ordered_access_history_add_alloc:
    forall r ah n d,
    OrderedAccessHistory ah ->
    OrderedAccessHistory (MM.add r ((n, Some d) :: nil) ah).
  Proof.
    intros.
    unfold OrderedAccessHistory.
    intros.
    rewrite MM_Facts.add_mapsto_iff in *.
    destruct H0 as [(?,?)|(?,?)]. {
      subst.
      eauto using ordered_adds_nil.
    }
    eauto.
  Qed.

  Let ordered_access_history_add_read:
    forall ah x l n,
    OrderedAccessHistory ah ->
    MM.MapsTo x l ah ->
    WriteSafe (n, None) l ->
    OrderedAccessHistory (MM.add x ((n,None) :: l) ah).
  Proof.
    intros.
    unfold OrderedAccessHistory.
    intros.
    rewrite MM_Facts.add_mapsto_iff in *.
    destruct H2 as [(?,Heq)|(?,?)]. {
      subst.
      eauto using ordered_adds_read, write_safe_def.
    }
    eauto.
  Qed.

  Let ordered_access_history_add_write:
    forall ah x l n d,
    OrderedAccessHistory ah ->
    MM.MapsTo x l ah ->
    WriteSafe (n, Some d) l ->
    ReadSafe (n, Some d) l ->
    OrderedAccessHistory (MM.add x ((n, Some d) :: l) ah).
  Proof.
    intros.
    unfold OrderedAccessHistory.
    intros.
    rewrite MM_Facts.add_mapsto_iff in *.
    destruct H3 as [(?,Heq)|(?,?)]. {
      subst.
      eauto using ordered_adds_write.
    }
    eauto.
  Qed.

  Lemma ordered_access_history_add:
    forall ah e ah',
    OrderedAccessHistory ah ->
    RaceFreeAdd ah e ah' ->
    OrderedAccessHistory ah'.
  Proof.
    intros.
    unfold RaceFreeHistory; intros.
    inversion H0; subst; clear H0; eauto.
  Qed.

  Let last_to_write:
    forall l a,
    Last a l ->
    Write a.
  Proof.
    induction l; intros. {
      inversion H.
    }
    inversion H; subst; clear H; auto.
  Qed.

  Let last_to_in:
    forall a l,
    Last a l ->
    List.In a l.
  Proof.
    induction l; intros. {
      inversion H.
    }
    inversion H; auto using in_eq.
    subst.
    auto using in_cons.
  Qed.


  Let last_write:
    forall (a:access) b l,
    LastWrite b l ->
    Write a ->
    List.In a l ->
    HBE a b.
  Proof.
    intros.
    inversion H.
    eauto.
  Qed.

  Let last_inv_cons_nil:
    forall a b,
    Last a (b :: nil) ->
    a = b /\ Write b.
  Proof.
    intros.
    inversion H; subst; clear H; eauto;
    inversion H2.
  Qed.

  Let last_inv_eq:
    forall a b,
    Last a (b :: nil) ->
    a = b.
  Proof.
    intros.
    apply last_inv_cons_nil in H.
    destruct H; assumption.
  Qed.

  Let last_write_absurd_nil:
    forall (a:access),
    ~ LastWrite a nil.
  Proof.
    unfold not; intros.
    inversion H.
    inversion H1.
  Qed.

  Let write_dec:
    forall a,
    { Write a } + { ~ Write a }.
  Proof.
    intros.
    destruct a as (?,[]).
    - auto.
    - right; unfold not; intros.
      inversion H.
  Qed.

  Let in_last_write:
    forall l a b,
    List.In a l ->
    LastWrite b l ->
    Read a \/ (Write a /\ HBE a b).
  Proof.
    intros.
    inversion H0; clear H0.
    unfold ForallWrites in *; simpl in *.
    destruct (write_dec a); auto.
  Qed.

  Let forall_writes_inv:
    forall P l a,
    ForallWrites P (a :: l) ->
    ForallWrites P l /\ (Write a -> P a).
  Proof.
    intros.
    unfold ForallWrites in *.
    rewrite <- Forall_forall in *.
    inversion H; subst; auto.
  Qed.

  Let forall_writes_inv_cons:
    forall P l a,
    ForallWrites P (a :: l) ->
    ForallWrites P l.
  Proof.
    intros.
    apply forall_writes_inv in H; destruct H.
    auto.
  Qed.

  Let forall_reads_inv:
    forall P l a,
    ForallReads P (a :: l) ->
    ForallReads P l /\ (Read a -> P a).
  Proof.
    intros.
    unfold ForallReads in *.
    rewrite <- Forall_forall in *.
    inversion H; subst; auto.
  Qed.

  Let forall_reads_inv_cons:
    forall P l a,
    ForallReads P (a :: l) ->
    ForallReads P l.
  Proof.
    intros.
    apply forall_reads_inv in H; destruct H.
    auto.
  Qed.

  Let last_write_inv_read:
    forall l a b,
    Read a ->
    LastWrite b (a :: l) ->
    LastWrite b l.
  Proof.
    induction l; intros. {
      inversion H0.
      inversion H2; subst; clear H2. {
        contradiction.
      }
      inversion H4.
    }
    inversion H0; subst; clear H0.
    inversion H2; subst; clear H2. {
      contradiction.
    }
    inversion H0; subst; clear H0. {
      eauto using last_write_def, in_eq.
    }
    apply forall_writes_inv_cons in H3.
    auto using last_write_def, in_cons.
  Qed.

  Let hb_neq:
    forall a b,
    HB a b ->
    a <> b.
  Proof.
    unfold not; intros.
    subst.
    apply lt_irrefl in H.
    assumption.
  Qed.

  Let last_write_hbe:
    forall x y l,
    LastWrite x l ->
    LastWrite y l ->
    HBE x y.
  Proof.
    intros.
    inversion H0.
    inversion H.
    apply last_write with (l:=l); auto.
  Qed.

  Let last_write_trans:
    forall x y z l,
    LastWrite x l ->
    LastWrite y l ->
    HB x z ->
    HB y z.
  Proof.
    intros.
    assert (Hx: HBE y x) by eauto.
    destruct Hx. {
      eauto.
    }
    subst.
    assumption.
  Qed.

  Let write_safe:
    forall a b l,
    LastWrite a l ->
    WriteSafe b l ->
    HB a b.
  Proof.
    intros.
    inversion H0; subst.
    eauto.
  Qed.

  Let last_write_inv:
    forall a b l,
    LastWrite a (b :: l) ->
    (b = a /\  ForallWrites (fun c => HBE c a) l) \/
    (LastWrite a l /\ (Write b -> HBE b a)).
  Proof.
    intros.
    inversion H; subst; clear H.
    destruct H1. {
      apply forall_writes_inv_cons in H2.
      auto.
    }
    right.
    apply forall_writes_inv in H2.
    destruct H2 as (Hf, Hi).
    eauto using last_write_def.
  Qed.

  Let in_last_write_write:
    forall l a b,
    List.In a l ->
    Write a ->
    LastWrite b l ->
    HBE a b.
  Proof.
    intros.
    eapply in_last_write in H1; eauto.
    destruct H1; try contradiction.
    destruct H1.
    assumption.
  Qed.

  Let hbe_hb_hb_trans:
    forall a b c,
    HBE a b ->
    HB b c ->
    HB a c.
  Proof.
    intros.
    destruct H; subst; eauto.
  Qed.

  Let write_safe_hb:
    forall a b l,
    List.In a l ->
    Write a ->
    WriteSafe b l ->
    HB a b.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    assert (Hp: HBE a w) by eauto.
    eauto.
  Qed.

  Let read_write_safe:
    forall a b l,
    List.In b l ->
    WriteSafe a l ->
    ReadSafe a l ->
    HB b a.
  Proof.
    intros.
    destruct (write_dec b); eauto.
  Qed.

  Let read_in_write_safe_race_free:
    forall a b l,
    List.In a l ->
    Read b ->
    WriteSafe b l ->
    RaceFreeAccess a b.
  Proof.
    intros.
    destruct (write_dec a). {
      eauto using race_free_access_hb, race_free_access_symm.
    }
    eauto using race_free_access_read.
  Qed.

  Let ordered_adds_race_free:
    forall l a b,
    OrderedAdds l ->
    List.In a l ->
    List.In b l ->
    RaceFreeAccess a b.
  Proof.
    induction l; intros. {
      inversion H0.
    }
    inversion H0; inversion H1; clear H0 H1; repeat subst;
    auto using race_free_access_refl;
    inversion H; subst; clear H;
    try inversion H3;
    try inversion H2;
    eauto using race_free_access_symm, race_free_access_hbe.
  Qed.

  Lemma ordered_access_history_to_race_free_history:
    forall ah,
    OrderedAccessHistory ah ->
    RaceFreeHistory ah.
  Proof.
    unfold RaceFreeHistory, OrderedAccessHistory.
    intros.
    apply H in H0; clear H.
    eauto.
  Qed.

  Lemma last_write_inv_cons_nil:
    forall a b,
    LastWrite a (b::nil) ->
    a = b.
  Proof.
    intros.
    inversion H.
    destruct H1. {
      auto.
    }
    inversion H1.
  Qed.

  Lemma last_write_inv_cons_read:
    forall a n l,
    LastWrite a ((n,None)::l) ->
    LastWrite a l.
  Proof.
    intros.
    inversion H; subst; clear H.
    destruct H1; subst. {
      inversion H0.
    }
    assert (ForallWrites (fun b : access => HBE b a) l). {
      unfold ForallWrites in *; eauto using in_cons.
    }
    eauto using last_write_def.
  Qed.

  Lemma write_eq:
    forall n d,
    Write (n, Some d).
  Proof.
    auto using has_data_def.
  Qed.

  Definition LastWriteFun ah :=
    forall a b r h,
    MM.MapsTo r h ah ->
    LastWrite a h ->
    LastWrite b h ->
    a = b.

  Let last_write_to_write:
    forall a l,
    LastWrite a l ->
    Write a.
  Proof.
    intros.
    inversion H; auto.
  Qed.

  Lemma last_write_to_some:
    forall a l,
    LastWrite a l ->
    exists d, a_what a = Some d.
  Proof.
    intros.
    apply last_write_to_write in H.
    inversion H; eauto.
  Qed.

End Defs.


Section Props.
  Variable A:Type.
  Variable E:Type.
  Variable P: E -> E -> Prop.
  Variable Q: E -> E -> Prop.

  Variable lt_impl:
    forall x y,
    P x y -> Q x y.

  Let forall_writes_impl:
    forall a h,
    ForallWrites (fun b => P (a_when b) (a_when (A:=A) a) \/ b = a) h ->
    ForallWrites (fun b => Q (a_when b) (a_when a) \/ b = a) h.
  Proof.
    unfold ForallWrites.
    intros.
    apply H in H0; auto.
    destruct H0; auto.
  Qed.

  Let last_write_impl:
    forall w h,
    LastWrite (A:=A) P w h ->
    LastWrite Q w h.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using last_write_def.
  Qed.

  Let write_safe_impl:
    forall a h,
    WriteSafe (A:=A) P a h ->
    WriteSafe Q a h.
  Proof.
    intros.
    inversion H.
    eauto using write_safe_def.
  Qed.

  Let read_safe_impl:
    forall a h,
    ReadSafe (A:=A) P a h ->
    ReadSafe Q a h.
  Proof.
    intros.
    unfold ReadSafe, ForallReads in *.
    eauto.
  Qed.

  Let ordered_adds_impl:
    forall h,
    OrderedAdds (A:=A) P h ->
    OrderedAdds Q h.
  Proof.
    intros.
    induction H.
    - auto using ordered_adds_nil.
    - eauto using ordered_adds_read.
    - eauto using ordered_adds_write.
  Qed.

  Lemma ordered_access_history_impl:
    forall (ah: access_history A E),
    OrderedAccessHistory P ah ->
    OrderedAccessHistory Q ah.
  Proof.
    unfold OrderedAccessHistory; intros; eauto.
  Qed.

  Lemma last_write_fun_impl:
    forall (ah: access_history A E),
    LastWriteFun Q ah ->
    LastWriteFun P ah.
  Proof.
    unfold LastWriteFun; intros; eauto.
  Qed.

End Props.