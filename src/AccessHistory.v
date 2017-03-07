Require Tid.
Require Trace.
Require Node.
Require CG.
Require SJ_CG.

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
  (** 
  Access history records for each memory id: all the accesses to memory.
  An access consists of the causality event that performed the access
  and the kind of address, which can be either a read or a write,
  and in the case of a write, the written data.
  
  Let [A] be the type of the data. *)

  Variable A:Type.
  
  (** And [E] be the type of the causality event. *)
  
  Variable E:Type.
  
  (** As usual, an event [E] is ordered by a causality relation [Lt]
    that is a pre-order, thus transitive and irreflexive. *)
  
  Variable Lt: E -> E -> Prop.
  Variable lt_trans:
    forall x y z,
    Lt x y ->
    Lt y z ->
    Lt x z.
  Variable lt_irrefl:
    forall x,
    ~ Lt x x.

  (** An [access] pairs an event of type [E] with a payload
  which is either [None] for a read or [Some d] for a store 
  *)

  Notation payload := (option A).

  Definition access := (E * payload) % type.

  (** Rename fst and snd to more understandable terms. *)

  Definition a_when := @fst E payload.
  Definition a_what := @snd E payload.

  (** Some notation to operate over accesses. *)

  Notation HB a b := (Lt (a_when a) (a_when b)).
  Notation MHP a b := (~ HB a b /\ ~ HB b a).
  Notation HBE a b := (HB a b \/ a_when a = a_when b).

  (** Again, a [Write] holds some data. *)

  Inductive Write: access -> Prop :=
  | write_some:
    forall n x,
    Write (n, Some x).

  (** Otherwise, we have a read. *)

  Definition Read a := ~ Write a.

  (** An access history records all the saccesses for each
  memory id. *)

  Definition access_history := MM.t (list access).

  (** An empty access history. *)

  Definition empty : access_history := MM.empty (list access).

  (** The standard definition of a race: the events are concurrent
  and there is at least one write. *)

  Inductive RacyAccess : access -> access -> Prop :=
  | racy_access_def:
    forall a b,
    a_when a <> a_when b ->
    (Write a \/ Write b) ->
    MHP a b ->
    RacyAccess a b.

  (** Race-free accesses are trivially defined. *)

  Definition RaceFreeAccess a b := ~ RacyAccess a b.

  (** Finally a race-free history is such that two accesses
  in the same memory location are race free. *)

  Definition RaceFreeHistory ah :=
    forall r l a b,
    MM.MapsTo r l ah ->
    List.In a l ->
    List.In b l ->
    RaceFreeAccess a b.

  Ltac expand H := inversion H; subst; clear H.

(* begin hide *)
  Lemma racy_access_irrefl_when:
    forall (a b:access),
    a_when a = a_when b ->
    ~ RacyAccess a b.
  Proof.
    unfold not; intros.
    inversion H0.
    contradiction.
  Qed.

  Lemma racy_access_irrefl:
    forall (a:access),
    ~ RacyAccess a a.
  Proof.
    intros.
    assert (a_when a = a_when a) by trivial; eauto using racy_access_irrefl_when.
  Qed.
(* end hide *)

  (** If the same event performs multiple reads or multiple writes,
  these are race-free (as there is no concurrency in this case). 
  The rest are usual properties of race-free accesses (reflexivity,
  symmetry, reads do not race with each order, and 
  ordered accesses do not race with each other. These properties
  are necessary since we defined a race-free access by negating
  a racy access. *)

  Lemma race_free_access_refl_when:
    forall (a b:access),
    a_when a = a_when b ->
    RaceFreeAccess a b.
  Proof.
    unfold RaceFreeAccess.
    auto using racy_access_irrefl_when.
  Qed.

  Lemma race_free_access_refl:
    forall (a:access),
    RaceFreeAccess a a.
  Proof.
    unfold RaceFreeAccess.
    auto using racy_access_irrefl.
  Qed.
(* begin hide *)
(*  Notation Ordered a b := (HB a b \/ HB b a). *)
(* end hide *)

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
      auto using race_free_access_refl_when.
  Qed.
(* begin hide *)
  Let mhp_symm:
    forall a b,
    MHP a b ->
    MHP b a.
  Proof.
    intros.
    destruct H.
    auto.
  Qed.
(* end hide *)
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

  Lemma read_none:
    forall n,
    Read (n, None).
  Proof.
    intros.
    unfold Read, not; intros.
    inversion H.
  Qed.

  Lemma write_dec:
    forall a,
    { Write a } + { Read a }.
  Proof.
    intros.
    destruct a as (?,[]).
    - auto using write_some.
    - right; unfold Read, not; intros.
      inversion H.
  Defined.

End Defs.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Section LastWrites.

  (**
    The theory of race-free-adds defines sufficient conditions to
    maintain a data race-free access-history.
   *)

  Variable A:Type.
  Variable E:Type.
  Variable Lt: E -> E -> Prop.
  Variable lt_trans:
    forall (x y z:E),
    Lt x y ->
    Lt y z ->
    Lt x z.
  Variable lt_irrefl:
    forall (x:E),
    ~ Lt x x.

  Notation HB a b := (Lt (@a_when A E a) (@a_when A E b)).
  Notation MHP a b := (~ HB a b /\ ~ HB b a).
  Notation HBE a b := (HB a b \/ @a_when A E a = @a_when A E b).

  (** As we need to state definition in terms of the reads and the writes,
   let us define a predicate for all reads/writes. *)

  Definition ForallWrites (P : access A E -> Prop) l : Prop :=
    forall a,
    List.In a l ->
    Write a ->
    P a.

  Definition ForallReads (P: access A E -> Prop) l : Prop :=
    forall a,
    List.In a l ->
    Read a ->
    P a.

  (** The last write *)

  Inductive LastWrite (a:access A E) (l:list (access A E)) : Prop :=
  | last_write_def:
    Write a ->
    List.In a l->
    ForallWrites (fun b => HBE b a) l ->
    LastWrite a l.

  Inductive MapsTo r (x:A) ah : Prop :=
  | maps_to_def:
    forall a l,
    MM.MapsTo r l ah ->
    LastWrite a l ->
    a_what a = Some x ->
    MapsTo r x ah.

  (** A write-safe access happens before all writes *)
(*
  Inductive WriteSafe (a:access A E) l : Prop :=
  | write_safe_def:
    forall w,
    (* take the last-write *)
    LastWrite w l ->
    (* the access must succeed the last-write *)
    HBE w a ->
    WriteSafe a l.
*)
  (** A read-safe happens before all reads. *)

  Definition WriteSafe (a:access A E) l := ForallWrites (fun b => HBE b a) l.

  Definition ReadSafe (a:access A E) l := ForallReads (fun b => HBE b a) l.

  (**
    We distinguish between createion, reading and writing.
   *)

  Inductive op_type := READ | WRITE.

  Definition op := (op_type * A) % type.

  (*
  W_x \subseteq n
  ----------------------
  (R, W) ==>rd(n, x) (R{x += n}, W)
  
  W_x \subseteq n
  R_x \subseteq n
  ----------------------
  (R, W) ==>wr(n, x) (R, W{x += n})
   *)

  Inductive Add: access_history A E -> (mid * E * op) -> access_history A E -> Prop :=
  | add_alloc:
    forall g r d n,
    ~ MM.In r g ->
    (* update the shared memory to record the allocation *)
    Add g (r, n, (WRITE, d)) (MM.add r ((n, Some d)::nil) g)

  | add_read:
    forall g l (n n':E) r d,
    MM.MapsTo r l g ->
    (* The read is ordered wrt the reads *)
    WriteSafe (n, None) l ->
    (* Get the value of the last write *)
    LastWrite (n', Some d) l ->
    (* update the shared memory to record the read *)
    Add g (r, n, (READ, d)) (MM.add r ((n, None)::l) g)

  | add_write:
    forall g r d n l,
    (* update the shared memory to record the read *)
    MM.MapsTo r l g ->
    WriteSafe (n, Some d) l ->
    ReadSafe (n, Some d) l ->
    Add g (r, n, (WRITE, d)) (MM.add r ((n, Some d)::l) g).

  Lemma hbe_trans:
    forall x y z,
    HBE x y ->
    HBE y z ->
    HBE x z.
  Proof.
    intros.
    destruct H, H0, x, y, z; simpl in *; subst;
    eauto.
  Qed.

  Let last_write_to_forall_writes:
    forall c a l,
    LastWrite c l ->
    HBE c a ->
    ForallWrites (fun b : access A E => HBE b a) l.
  Proof.
    intros.
    inversion H; subst; clear H.
    unfold ForallWrites; intros.
    apply H3 in H4; auto.
    eapply hbe_trans; eauto.
  Qed.

  Theorem add_read_alt:
    forall g l (n n':E) r d,
    MM.MapsTo r l g ->
    (* same as [WriteSafe] *)
    LastWrite (n', Some d) l ->
    Lt n' n ->
    (* update the shared memory to record the read *)
    Add g (r, n, (READ, d)) (MM.add r ((n, None)::l) g).
  Proof.
    intros.
    apply add_read with (n':=n'); auto.
    eapply last_write_to_forall_writes; eauto.
  Qed.
(*
  Lemma write_safe_alt:
    forall n d l n',
    ForallWrites (fun b : access A E => HBE b (n, None)) l ->
    LastWrite (n', Some d) l ->
    WriteSafe (n, None) l.
  Proof.
    intros.
    apply write_safe_def with (w:=(n', Some d)); auto.
    inversion H0; subst; clear H0.
    apply H in H1; auto.
  Qed.
*)
  Theorem add_write_alt:
    forall g r d n w l,
    (* update the shared memory to record the read *)
    MM.MapsTo r l g ->
    (* take the last-write *)
    LastWrite w l ->
    (* the access must succeed the last-write *)
    HBE w (n, Some d) ->
    (* the write must also be safe wrt all reads *)
    ReadSafe (n, Some d) l ->
    Add g (r, n, (WRITE, d)) (MM.add r ((n, Some d)::l) g).
  Proof.
    intros.
    apply add_write; auto.
    inversion H0.
    eapply last_write_to_forall_writes; eauto.
  Qed.

(* begin hide *)
(*
  Inductive RaceFreeAdd: access_history A E -> (mid * E * op) -> access_history A E -> Prop :=
  | race_free_add_alloc:
    forall g r d n,
    ~ MM.In r g ->
    (* update the shared memory to record the allocation *)
    RaceFreeAdd g (r, n, (WRITE, d)) (MM.add r ((n, Some d)::nil) g)

  | race_free_read:
    forall g l (n n':E) r d,
    MM.MapsTo r l g ->
    (* same as [WriteSafe] *)
    LastWrite (n', Some d) l ->
    Lt n' n ->
    (* update the shared memory to record the read *)
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
*)
  Let last_write:
    forall (a:access A E) b l,
    LastWrite b l ->
    Write a ->
    List.In a l ->
    HBE a b.
  Proof.
    intros.
    inversion H.
    eauto.
  Qed.

  Let last_write_absurd_nil:
    forall (a:access A E),
    ~ LastWrite a nil.
  Proof.
    unfold not; intros.
    inversion H.
    inversion H1.
  Qed.

  Let in_last_write:
    forall l a b,
    List.In a l ->
    LastWrite b l ->
    Read (A:=A) a \/ (Write a /\ HBE a b).
  Proof.
    intros.
    inversion H0; clear H0.
    unfold ForallWrites in *; simpl in *.
    destruct (write_dec a); auto.
  Qed.

  Lemma forall_writes_inv:
    forall P l (a:access A E),
    ForallWrites P (a :: l) ->
    ForallWrites P l /\ (Write a -> P a).
  Proof.
    intros.
    unfold ForallWrites in *.
    rewrite <- Forall_forall in *.
    inversion H; subst; auto.
  Qed.

  Lemma forall_writes_inv_cons:
    forall P l (a:access A E),
    ForallWrites P (a :: l) ->
    ForallWrites P l.
  Proof.
    intros.
    apply forall_writes_inv in H; destruct H.
    auto.
  Qed.

  Lemma forall_writes_cons_read:
    forall P l (a:access A E),
    Read a ->
    ForallWrites P l ->
    ForallWrites P (a :: l).
  Proof.
    intros.
    unfold ForallWrites; intros b; intros.
    inversion H1; subst; clear H1. {
      contradiction.
    }
    auto.
  Qed.

  Lemma forall_writes_cons_write:
    forall (P:access A E -> Prop) l (a:access A E),
    Write a ->
    P a ->
    ForallWrites P l ->
    ForallWrites P (a :: l).
  Proof.
    intros.
    unfold ForallWrites; intros b; intros.
    inversion H2; subst; clear H2. {
      assumption.
    }
    auto.
  Qed.

  Lemma forall_reads_inv:
    forall P l (a:access A E),
    ForallReads P (a :: l) ->
    ForallReads P l /\ (Read a -> P a).
  Proof.
    intros.
    unfold ForallReads in *.
    rewrite <- Forall_forall in *.
    inversion H; subst; auto.
  Qed.

  Lemma forall_reads_inv_cons:
    forall P l (a:access A E),
    ForallReads P (a :: l) ->
    ForallReads P l.
  Proof.
    intros.
    apply forall_reads_inv in H; destruct H.
    auto.
  Qed.

  Let last_write_inv_read:
    forall l (a:access A E) b,
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
      eauto using last_write_def, in_eq, forall_writes_inv_cons.
    }
    apply forall_writes_inv_cons in H3.
    auto using last_write_def, in_cons.
  Qed.

  Let last_write_hbe:
    forall (x:access A E) y l,
    LastWrite x l ->
    LastWrite y l ->
    HBE x y.
  Proof.
    intros.
    inversion H0.
    inversion H.
    apply last_write with (l:=l); auto.
  Qed.

  Let last_write_inv:
    forall a (b:access A E) l,
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
    forall l (a:access A E) b,
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
(* end hide *)

  (** EXPORTED *)

  Theorem last_write_inv_cons_nil:
    forall (a b:access A E),
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
    forall (a:access A E) n l,
    LastWrite a ((n,None)::l) ->
    LastWrite a l.
  Proof.
    intros.
    inversion H; subst; clear H.
    destruct H1; subst. {
      inversion H0.
    }
    assert (ForallWrites (fun b : access A E => HBE b a) l). {
      unfold ForallWrites in *; eauto using in_cons.
    }
    eauto using last_write_def.
  Qed.

(* begin hide *)

  Let hb_neq:
    forall (a:access A E) b,
    HB a b ->
    a <> b.
  Proof.
    unfold not; intros.
    subst.
    apply lt_irrefl in H.
    assumption.
  Qed.

  Let hbe_eq_when_left:
    forall (x y z:access A E),
    HBE x z ->
    a_when y = a_when x ->
    HBE y z.
  Proof.
    intros.
    rewrite H0.
    assumption.
  Qed.

  Let hb_eq_when_left:
    forall (x y z:access A E),
    HB x z ->
    a_when y = a_when x ->
    HB y z.
  Proof.
    intros.
    rewrite H0.
    assumption.
  Qed.

  Let hbe_hb_hb_trans:
    forall (a b c:access A E),
    HBE a b ->
    HB b c ->
    HB a c.
  Proof.
    intros.
    destruct H; subst; eauto.
  Qed.

  Let write_safe:
    forall (a:access A E) b l,
    LastWrite a l ->
    WriteSafe b l ->
    HBE a b.
  Proof.
    intros.
    inversion H; subst.
    apply hbe_trans with (y:=a); eauto.
  Qed.

  Let write_safe_hbe:
    forall (a b:access A E) l,
    List.In a l ->
    Write a ->
    WriteSafe b l ->
    HBE a b.
  Proof.
    intros.
    auto.
  Qed.

  Let read_write_safe:
    forall (a b:access A E) l,
    List.In b l ->
    WriteSafe a l ->
    ReadSafe a l ->
    HBE b a.
  Proof.
    intros.
    destruct (write_dec b); eauto.
  Qed.

  Let read_in_write_safe_race_free:
    forall (a b:access A E) l,
    List.In a l ->
    Read b ->
    WriteSafe b l ->
    RaceFreeAccess Lt a b.
  Proof.
    intros.
    destruct (write_dec a). {
      eauto using race_free_access_hbe, race_free_access_symm.
    }
    eauto using race_free_access_read.
  Qed.
(* end hide *)

  Lemma last_write_inv_cons_write:
    forall (a:access A E) n l d,
    WriteSafe (n,Some d) l ->
    LastWrite a ((n,Some d)::l) ->
    n = a_when a.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    destruct H2. {
      subst.
      auto.
    }
    apply forall_writes_inv in H3.
    destruct H3 as (_,Hi).
    assert (Hx : Write (n, Some d)) by auto using write_some.
    apply Hi in Hx.
    destruct Hx. {
      assert (HBE a (n, Some d)) by eauto using write_safe_hbe.
      assert (HB a a) by eauto.
      apply lt_irrefl in H4.
      contradiction.
    }
    auto.
  Qed.

  Lemma last_write_inv_cons:
    forall l (a b:access A E),
    LastWrite a (b::l) ->
    a = b \/ ((Write b -> HBE b a) /\ LastWrite a l).
  Proof.
    induction l; intros. {
      auto using last_write_inv_cons_nil.
    }
    apply last_write_inv in H.
    destruct H as [(?,?)|(?,?)]; auto.
  Qed.

  Lemma last_write_cons_read:
    forall (a:access A E) n l,
    LastWrite a l ->
    LastWrite a ((n,None)::l).
  Proof.
    intros.
    inversion H; subst.
    apply last_write_def; auto using in_cons.
    unfold ForallWrites in *.
    intros.
    destruct H3. {
      subst.
      inversion H4.
    }
    auto.
  Qed.

(* begin hide *)
  Let last_write_trans:
    forall (x y z:access A E) l,
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
    eauto.
  Qed.
(* end hide *)

  Lemma last_write_to_write:
    forall (a:access A E) h,
    LastWrite a h ->
    Write a.
  Proof.
    intros.
    inversion H; auto.
  Qed.

  (** *EXPORTED* *)

  Theorem last_write_to_in:
    forall (a:access A E) h,
    LastWrite a h ->
    List.In a h.
  Proof.
    intros; inversion H; auto.
  Qed.

  Lemma last_write_cons_write:
    forall e d h,
    WriteSafe (e, Some d) h ->
    LastWrite (e, Some d) ((e, Some d) :: h).
  Proof.
    auto using last_write_def, write_some, in_eq, forall_writes_cons_write.
  Qed.

  Lemma last_write_cons_write_2:
    forall a h,
    Write a ->
    WriteSafe a h ->
    LastWrite a (a :: h).
  Proof.
    intros.
    inversion H; subst.
    auto using last_write_cons_write.
  Qed.

  Lemma forall_writes_reads_to_last_write:
    forall h n d,
    ForallWrites (fun b => HBE b (n, Some d)) h ->
    ForallReads (fun b => HBE b (n, Some d)) h ->
    LastWrite (n, Some d) ((n, Some d)::h).
  Proof.
    intros.
    apply last_write_def; auto using in_eq, write_some.
    unfold ForallWrites; intros.
    inversion H1; subst; clear H1. {
      auto.
    }
    apply H in H2; auto.
  Qed.

  Lemma write_safe_inv_in:
    forall (a b:access A E) l,
    WriteSafe a l ->
    List.In b l ->
    Read b \/ HBE b a.
  Proof.
    intros.
    apply H in H0.
    destruct (write_dec b); auto.
  Qed.

  Lemma read_safe_inv_in:
    forall (a b:access A E) l,
    ReadSafe a l ->
    List.In b l ->
    Write b \/ HBE b a.
  Proof.
    intros.
    unfold ReadSafe in H.
    apply H in H0.
    destruct (write_dec b). {
      auto.
    }
    auto.
  Qed.

  Lemma read_write_safe_inv_in:
    forall (a b:access A E) l,
    ReadSafe a l ->
    WriteSafe a l ->
    List.In b l ->
    HBE b a.
  Proof.
    intros.
    assert (Hx := H1).
    apply read_safe_inv_in with (a:=a) in H1; auto.
    apply write_safe_inv_in with (a:=a) in Hx; auto.
    destruct H1, Hx; try contradiction; auto.
  Qed.

  Lemma write_safe_read_to_race_free:
    forall (a b:access A E) l,
    List.In b l ->
    Read a ->
    WriteSafe a l ->
    RaceFreeAccess Lt a b.
  Proof.
    intros.
    eapply write_safe_inv_in in H; eauto.
    destruct H.
    + auto using race_free_access_read.
    + auto using race_free_access_hbe, race_free_access_symm.
  Qed.

  Lemma add_fun:
    forall ah o ah1 ah2,
    Add ah o ah1 ->
    Add ah o ah2 ->
    ah1 = ah2.
  Proof.
    intros.
    inversion H; subst; clear H;
    inversion H0; subst; clear H0.
    + auto.
    + contradiction H1.
      eauto using MM_Extra.mapsto_to_in.
    + assert (l0 = l) by eauto using MM_Facts.MapsTo_fun; subst.
      trivial.
    + contradiction H8.
      eauto using MM_Extra.mapsto_to_in.
    + assert (l0 = l) by eauto using MM_Facts.MapsTo_fun; subst.
      trivial.
  Qed.
End LastWrites.


(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Section OrderedAdds.

  Variable A:Type.
  Variable E:Type.
  Variable Lt: E -> E -> Prop.

  Variable lt_irrefl:
    forall x,
    ~ Lt x x.
  Variable lt_trans:
    forall x y z,
    Lt x y ->
    Lt y z ->
    Lt x z.

  Inductive OrderedAdds : list (access A E) -> Prop :=
  | ordered_adds_nil:
    forall a,
    Write a ->
    OrderedAdds (a :: nil)
  | ordered_adds_read:
    forall a l,
    Read a ->
    OrderedAdds l ->
    WriteSafe Lt a l ->
    OrderedAdds (a :: l)
  | ordered_adds_write:
    forall a l,
    Write a ->
    OrderedAdds l ->
    WriteSafe Lt a l ->
    ReadSafe Lt a l ->
    OrderedAdds (a :: l).

  Inductive Last (a:access A E) : list (access A E) -> Prop :=
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

  Definition OrderedAccessHistory (ah:access_history A E) :=
    forall r l,
    MM.MapsTo r l ah ->
    OrderedAdds l.

  Notation HB a b := (Lt (@a_when A E a) (@a_when A E b)).
  Notation MHP a b := (~ HB a b /\ ~ HB b a).
  Notation HBE a b := (HB a b \/ @a_when A E a = @a_when A E b).

(* begin hide *)
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
      auto using ordered_adds_nil, write_some.
    }
    eauto.
  Qed.

  Let ordered_access_history_add_read:
    forall ah x l n n' d,
    OrderedAccessHistory ah ->
    MM.MapsTo x l ah ->
    ForallWrites (fun b => HBE b (n, None)) l ->
    LastWrite Lt (n', Some d) l ->
    OrderedAccessHistory (MM.add x ((n,None) :: l) ah).
  Proof.
    intros.
    unfold OrderedAccessHistory.
    intros.
    rewrite MM_Facts.add_mapsto_iff in *.
    destruct H3 as [(?,Heq)|(?,?)]. {
      subst.
      apply ordered_adds_read; eauto using read_none, ordered_adds_read.
    }
    eauto.
  Qed.

  Let ordered_access_history_add_write_0:
    forall l n d,
    OrderedAdds l ->
    WriteSafe Lt (n, Some d) l ->
    ReadSafe Lt (n, Some d) l ->
    OrderedAdds ((n, Some d) :: l).
  Proof.
    intros.
    inversion H; subst; clear H;
    auto using
      ordered_adds_nil,
      ordered_adds_read,
      ordered_adds_write,
      write_some.
  Qed.

  Let ordered_access_history_add_write:
    forall ah x l n d,
    OrderedAccessHistory ah ->
    MM.MapsTo x l ah ->
    ForallWrites (fun b => HBE b (n, Some d)) l ->
    ForallReads (fun b => HBE b (n, Some d)) l ->
    OrderedAccessHistory (MM.add x ((n, Some d) :: l) ah).
  Proof.
    intros.
    unfold OrderedAccessHistory.
    intros.
    rewrite MM_Facts.add_mapsto_iff in *.
    destruct H3 as [(?,Heq)|(?,?)]; eauto.
    subst.
    apply ordered_access_history_add_write_0; auto.
    apply H in H0; assumption.
  Qed.
(* end hide *)

  Lemma ordered_access_history_add:
    forall ah e ah',
    OrderedAccessHistory ah ->
    Add Lt ah e ah' ->
    OrderedAccessHistory ah'.
  Proof.
    intros.
    unfold RaceFreeHistory; intros.
    inversion H0; subst; clear H0; eauto.
  Qed.

(* begin hide *)
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
(* end hide *)

(* begin hide *)
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

  Let read_write_safe_race_free:
    forall (a b:access A E) l,
    ReadSafe Lt a l ->
    WriteSafe Lt a l ->
    List.In b l ->
    RaceFreeAccess Lt a b.
  Proof.
    intros.
    apply race_free_access_symm,
          race_free_access_hbe,
          read_write_safe_inv_in with (l:=l); auto.
  Qed.

  Let ordered_adds_race_free:
    forall l a b,
    OrderedAdds l ->
    List.In a l ->
    List.In b l ->
    RaceFreeAccess Lt a b.
  Proof.
    induction l; intros. {
      inversion H0.
    }
    inversion H0; inversion H1; clear H0 H1; repeat subst;
    auto using race_free_access_refl;
    inversion H; subst; clear H;
    try inversion H3;
    try inversion H2;
    subst;
    eauto using race_free_access_symm, race_free_access_hbe,
    write_safe_read_to_race_free.
  Qed.
(* end hide *)

  Lemma ordered_access_history_to_race_free_history:
    forall ah,
    OrderedAccessHistory ah ->
    RaceFreeHistory Lt ah.
  Proof.
    unfold RaceFreeHistory, OrderedAccessHistory.
    intros.
    apply H in H0; clear H.
    eauto.
  Qed.

  Definition LastWriteFun ah :=
    forall (a b:access A E) r h,
    MM.MapsTo r h ah ->
    LastWrite Lt a h ->
    LastWrite Lt b h ->
    a = b.

  Definition AccessFun ah :=
    forall (a b:access A E) r h,
    MM.MapsTo r h ah ->
    List.In a h ->
    List.In b h ->
    a_when a = a_when b ->
    a = b.

  Definition LastWriteDef ah :=
    forall r h,
    MM.MapsTo r h ah ->
    exists (a:access A E), LastWrite Lt a h.

  Lemma access_to_last_write_fun:
    forall ah,
    AccessFun ah ->
    LastWriteFun ah.
  Proof.
    unfold AccessFun, LastWriteFun.
    intros.
    inversion H1; subst; clear H1.
    inversion H2; subst; clear H2.
    unfold ForallWrites in *.
    assert (Ha : HBE b a) by auto.
    assert (Hb : HBE a b) by auto.
    destruct Ha as [Ha|?], Hb as [Hb|?]; eauto.
    assert (N: HB a a) by eauto.
    apply lt_irrefl in N.
    contradiction.
  Qed.

End OrderedAdds.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Section Props.
  Variable A:Type.
  Variable E:Type.
  Variable P: E -> E -> Prop.
  Variable Q: E -> E -> Prop.

  Variable lt_impl:
    forall x y,
    P x y -> Q x y.

  Let forall_writes_impl:
    forall (a:access A E) (h:list (access A E)),
    ForallWrites (fun b => P (a_when b) (a_when a) \/ a_when b = a_when a) h ->
    ForallWrites (fun b => Q (a_when b) (a_when a) \/ a_when b = a_when a) h.
  Proof.
    unfold ForallWrites.
    intros.
    apply H in H0; auto.
    destruct H0; auto.
  Qed.

  Variable lt_impl_ex:
    forall h n (b:access A E),
    List.In b h ->
    P (a_when b) n ->
    Q (a_when b) n.

  Lemma last_write_impl_ex:
    forall (a:access A E) h,
    (forall b, List.In b h -> P (a_when b) (a_when a) -> Q (a_when b) (a_when a)) ->
    LastWrite (A:=A) P a h ->
    LastWrite Q a h.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    apply last_write_def; try assumption.
    unfold ForallWrites in *.
    intros.
    apply H3 in H4; auto.
    destruct H4.
    - apply H in H4; auto.
    - auto.
  Qed.

  Lemma last_write_impl:
    forall w h,
    LastWrite (A:=A) P w h ->
    LastWrite Q w h.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using last_write_def.
  Qed.

  Let hbe_impl_ex:
    forall h (w a:access A E),
    List.In w h ->
    P (a_when w) (a_when a) \/ a_when w = a_when a ->
    Q (a_when w) (a_when a) \/ a_when w = a_when a.
  Proof.
    intros.
    destruct H0. {
      eapply lt_impl_ex in H0; eauto.
    }
    rewrite H0.
    auto.
  Qed.

  Let write_safe_impl:
    forall a h,
    WriteSafe (A:=A) P a h ->
    WriteSafe Q a h.
  Proof.
    unfold WriteSafe in *.
    auto using forall_writes_impl.
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

  Lemma last_write_def_impl:
    forall (ah: access_history A E),
    LastWriteDef P ah ->
    LastWriteDef Q ah.
  Proof.
    unfold LastWriteDef; intros.
    apply H in H0.
    destruct H0 as (a, Hx).
    eauto using last_write_impl.
  Qed.

End Props.

Module T.
  Import Tid.
  Import Node.

  Notation cg_access_history := (access_history Trace.datum node).
  Notation cg_access_history_op := (op Trace.datum).

  Import CG.
  Import CG.T.

  Section Defs.

  Inductive DRF_Reduces es (ah:cg_access_history) : (mid * cg_access_history_op) -> cg_access_history -> Prop :=
  | drf_reduces:
    forall n n' o ah' r es',
    es = CG.C (n, n') :: es' ->
    Add (CG.HB es) ah (r, n', o) ah' ->
    DRF_Reduces es ah (r, o) ah'.

  Definition op_to_ah (o:Trace.op) : option (mid*cg_access_history_op) :=
  match o with
  | Trace.MEM r (Trace.READ d) => Some (r, (READ, d))
  | Trace.MEM r (Trace.WRITE d) => Some (r, (WRITE, d))
  | _ => None
  end.

  Inductive DRF: Trace.trace -> CG.computation_graph -> cg_access_history -> Prop :=
  | drf_nil:
    DRF nil (nil, nil) (empty Trace.datum node)
  | drf_some:
    forall o o' ah' vs es cg x t ah,
    DRF t cg ah ->
    CG.T.CG ((x,o)::t) (vs, es) ->
    op_to_ah o = Some o' ->
    DRF_Reduces es ah o' ah' ->
    DRF ((x,o)::t) (vs,es) ah'
  | drf_none:
    forall o vs es cg x t ah,
    DRF t cg ah ->
    CG.T.CG ((x,o)::t) (vs, es) ->
    op_to_ah o = None ->
    DRF ((x,o)::t) (vs,es) ah.

  Definition NodeDef (vs:list tid) (g:cg_access_history) :=
    forall a r h,
    MM.MapsTo r h g ->
    List.In a h ->
    Node (a_when a) vs.
End Defs.

Section Props.

  Let drf_to_cg0:
    forall t cg ah,
    DRF t cg ah ->
    CG.CG (map event_to_cg t) cg.
  Proof.
    induction t; intros. {
      inversion H; subst; clear H.
      auto using CG.cg_nil.
    }
    inversion H; subst; clear H. {
      apply IHt in H2.
      simpl.
      destruct o; simpl in *;
      try (inversion H4; fail).
      inversion H3; subst; clear H3.
      assert ((vs0,es0) = cg0) by eauto using cg_fun.
      subst.
      auto using CG.cg_continue.
    }
    destruct o; inversion H6; simpl in *;
    inversion H3; subst; clear H3;
    try (rename es0 into es);
    try (rename vs0 into vs);
    assert ((vs,es) = cg0) by eauto using cg_fun; subst;
    auto using CG.cg_init, CG.cg_continue, CG.cg_fork, CG.cg_join.
  Qed.

  Lemma drf_to_cg:
    forall t cg ah,
    DRF t cg ah ->
    CG t cg.
  Proof.
    intros.
    eapply drf_to_cg0; eauto.
  Qed.

  Lemma drf_to_ordered_access_history:
    forall t cg (ah:cg_access_history),
    DRF t cg ah ->
    OrderedAccessHistory (HB (snd cg)) ah.
  Proof.
    induction t; intros. {
      inversion H; subst; clear H; simpl.
      unfold OrderedAccessHistory; intros.
      unfold empty in *.
      apply MM_Facts.empty_mapsto_iff in H.
      contradiction.
    }
    inversion H; subst; clear H. {
      assert (Hcg:=H3).
      destruct o; simpl in *;
      try (inversion H4; fail);
      destruct m0; inversion H4; subst; clear H4;
      inversion H3; subst; clear H3; simpl_node;
      assert (Hx:=H2); apply IHt in Hx;
        assert ((vs0, es0) = cg0) by (
          apply drf_to_cg0 in H2;
          eauto using cg_fun);
        subst;
        inversion H7; subst; clear H7;
        inversion H1; subst; clear H1;
        apply ordered_access_history_add in H4;
        simpl in *;
        eauto using ordered_access_history_impl, CG.hb_impl_0.
    }
    simpl in *;
    assert (Hx:=H2); apply IHt in Hx.
    apply drf_to_cg0 in H2.
    eapply ordered_access_history_impl with (P:=HB (snd cg0)); auto;
    assert (R: es = snd (vs,es)) by auto; rewrite R;
    eauto using CG.hb_impl.
  Qed.

  Lemma drf_to_race_free_history:
    forall t cg ah,
    DRF t cg ah ->
    RaceFreeHistory (HB (snd cg)) ah.
  Proof.
    eauto using
      ordered_access_history_to_race_free_history,
      drf_to_ordered_access_history.
  Qed.

  Let access_fun_alloc:
    forall (ah:cg_access_history) r (vs:list tid) d,
    AccessFun ah ->
    ~ MM.In r ah ->
    AccessFun (MM.add r ((fresh vs, Some d) :: nil) ah).
  Proof.
    unfold AccessFun.
    intros.
    rewrite MM_Facts.add_mapsto_iff in *.
    destruct H1 as [(?,?)|(?,mt)]. {
      subst.
      destruct H2, H3; subst; try inversion H2; try inversion H3; try inversion H1.
      auto.
    }
    eauto.
  Qed.

  Let access_fun_add:
    forall ah r vs h p,
    AccessFun ah ->
    NodeDef vs ah ->
    MM.MapsTo r h ah ->
    AccessFun (MM.add r ((fresh vs, p) :: h) ah).
  Proof.
    unfold AccessFun.
    intros.
    rewrite MM_Facts.add_mapsto_iff in *.
    destruct H2 as [(?,?)|(?,mt)]. {
      subst.
      destruct H3, H4; subst;
      try inversion H3;
      try inversion H4;
      simpl in *; subst; eauto.
      - assert (Node (fresh vs) vs) by (rewrite H5; eauto).
        simpl_node.
      - assert (Node (fresh vs) vs) by (rewrite <- H5; eauto).
        simpl_node.
    }
    eauto.
  Qed.
End Props.

Section NodeDef.
  Let node_def_cons:
    forall vs a ah,
    NodeDef vs ah ->
    NodeDef (a :: vs) ah.
  Proof.
    intros.
    unfold NodeDef in *.
    eauto using node_cons.
  Qed.

  Let node_def_alloc:
    forall vs a ah d r,
    NodeDef vs ah ->
    NodeDef (a :: vs) (MM.add r ((fresh vs, d) :: nil) ah).
  Proof.
    intros.
    unfold NodeDef in *.
    intros b q; intros.
    rewrite MM_Facts.add_mapsto_iff in *.
    destruct H0 as [(?,?)|(?,mt)]. {
      subst.
      destruct H1 as [?|N]. {
        subst.
        simpl.
        auto using node_eq.
      }
      inversion N.
    }
    eauto using node_cons.
  Qed.

  Let node_def_add:
    forall vs a ah d r h,
    NodeDef vs ah ->
    MM.MapsTo r h ah ->
    NodeDef (a :: vs) (MM.add r ((fresh vs, d) :: h) ah).
  Proof.
    intros.
    unfold NodeDef in *.
    intros b q; intros.
    rewrite MM_Facts.add_mapsto_iff in *.
    destruct H1 as [(?,?)|(?,mt)]. {
      subst.
      destruct H2 as [?|N]. {
        subst.
        simpl.
        auto using node_eq.
      }
      eauto using node_cons.
    }
    eauto using node_cons.
  Qed.

  Lemma drf_to_node_def:
    forall t cg ah,
    DRF t cg ah ->
    NodeDef (fst cg) ah.
  Proof.
    induction t; intros; inversion H; subst; clear H.
    - (* nil trace *)
      unfold NodeDef, empty in *; intros.
      apply MM_Facts.empty_mapsto_iff in H.
      contradiction.
    - (* read/write *)
      assert (Hx:=H2).
      apply drf_to_cg in Hx.
      apply IHt in H2; simpl in *;
      destruct o; simpl in *; try (inversion H4; clear H4);
      destruct m0; inversion H0; subst; clear H0;
      inversion H7; subst; clear H7;
      inversion H5; subst; clear H5; simpl in *;
      try (rename es' into es);
      inversion H3; subst; clear H3; subst; eauto; simpl_node;
        assert (cg0 = (vs0, es)) by eauto using CG.cg_fun; subst;
        eauto.
    - assert (Hx:=H2).
      apply IHt in H2.
      unfold NodeDef in *; intros; simpl in *.
      destruct o; inversion H6; subst; clear H6;
      inversion H3; subst; clear H3;
      try (rename es0 into es);
      assert (cg0 = (vs0, es)) by eauto using drf_to_cg, cg_fun; subst;
      eauto using node_cons.
  Qed.

  Lemma drf_to_node:
    forall t vs es ah r h a,
    DRF t (vs, es) ah ->
    MM.MapsTo r h ah ->
    List.In a h ->
    Node (a_when a) vs.
  Proof.
    intros.
    assert (R: vs = (fst (vs,es))) by auto; rewrite R.
    apply drf_to_node_def in H.
    eauto.
  Qed.

End NodeDef.

Section AccessFun.

  Let drf_reduces_access_fun:
    forall ah x ah' o vs n t es,
    AccessFun ah ->
    DRF_Reduces (C (n, fresh vs) :: es) ah o ah' ->
    DRF t (vs, es) ah ->
    MapsTo x n vs ->
    AccessFun ah'.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    inversion H3; subst; clear H3.
    inversion H4; subst; clear H4;
    unfold AccessFun in *; intros;
    rewrite MM_Facts.add_mapsto_iff in H0;
    destruct H0 as [(?,?)|(?,mt)]; eauto; subst;
    simpl in *.
    - destruct H4; try contradiction.
      destruct H3; try contradiction.
      subst.
      trivial.
    - destruct H4, H3; subst; eauto; simpl in *.
      + eapply drf_to_node in H3; eauto.
        rewrite H5 in *.
        simpl_node.
      + eapply drf_to_node in H0; eauto.
        rewrite <- H5 in *.
        simpl_node.
    - destruct H4, H3; subst; eauto; simpl in *.
      + eapply drf_to_node in H3; eauto.
        rewrite H5 in *.
        simpl_node.
      + eapply drf_to_node in H0; eauto.
        rewrite <- H5 in *.
        simpl_node.
  Qed.

  Lemma drf_access_fun:
    forall t cg ah,
    DRF t cg ah ->
    AccessFun ah.
  Proof.
    induction t; intros. {
      unfold AccessFun; intros.
      inversion H; subst; clear H.
      unfold empty in *.
      rewrite MM_Facts.empty_mapsto_iff in *.
      contradiction.
    }
    inversion H; subst; clear H; eauto.
    destruct o;
    simpl in *;
    inversion H4; subst; clear H4;
    inversion H3; subst; clear H3;
    try (rename vs0 into vs);
    try (rename es0 into es);
    assert (cg0 = (vs, es)) by eauto using drf_to_cg, cg_fun; subst;
    simpl_node; eauto.
  Qed.

  Let last_write_def_cons:
    forall es e ah,
    LastWriteDef (A:=Trace.datum) (HB es) ah ->
    LastWriteDef (HB (e :: es)) ah.
  Proof.
    eauto using last_write_def_impl, hb_impl_cons.
  Qed.

  Lemma last_write_cons:
    forall (vs:list tid) es a h n,
    LastWrite (A:=Trace.datum) (HB es) a h ->
    LastWrite (HB (C (n, fresh vs) :: es)) a h.
  Proof.
    eauto using last_write_impl, hb_impl_cons.
  Qed.

  Let last_write_def_alloc:
    forall vs es n r ah (d:Trace.datum),
    LastWriteDef (HB (es)) ah ->
    LastWriteDef (HB (C (n, fresh (A:=tid) vs) :: es))
      (MM.add r ((fresh vs, Some d) :: nil) ah).
  Proof.
    unfold LastWriteDef; intros.
    rewrite MM_Facts.add_mapsto_iff in *.
    destruct H0 as [(?,?)|(?,mt)]. {
      subst.
      exists (fresh vs, Some d).
      apply last_write_def; eauto using write_some, in_eq.
      unfold ForallWrites; intros.
      destruct H0. {
        subst; auto.
      }
      contradiction.
    }
    apply H in mt.
    destruct mt as (a,?).
    eauto using last_write_cons.
  Qed.

  Let last_write_def_read:
    forall r h ah vs es n a (d:Trace.datum),
    LastWriteDef (A:=Trace.datum) (HB es) ah ->
    MM.MapsTo r h ah ->
    LastWrite (HB (C (n, fresh (A:=tid) vs) :: es)) a h ->
    LastWriteDef (HB (C (n, fresh vs) :: es))
      (MM.add r ((fresh vs, None) :: h) ah).
  Proof.
    unfold LastWriteDef; intros.
    rewrite MM_Facts.add_mapsto_iff in *.
    destruct H2 as [(?,?)|(?,mt)]. {
      subst.
      eauto using last_write_cons_read.
    }
    apply H in mt.
    destruct mt as (a',?).
    eauto using last_write_cons.
  Qed.

  Let last_write_def_write:
    forall (vs:list tid) es ah (d:Trace.datum) h r n,
    LastWriteDef (HB es) ah ->
    MM.MapsTo r h ah ->
    ForallWrites
       (fun b =>
        HB (C (n, fresh vs) :: es) (a_when b) (fresh vs) \/
        a_when b = fresh vs) h ->
    ForallReads
       (fun b : access Trace.datum node =>
        HB (C (n, fresh vs) :: es) (a_when b) (fresh vs) \/
        a_when b = fresh vs) h ->
    LastWriteDef (HB (C (n, fresh vs) :: es))
      (MM.add r ((fresh vs, Some d) :: h) ah).
  Proof.
    unfold LastWriteDef; intros.
    rewrite MM_Facts.add_mapsto_iff in *.
    destruct H3 as [(?,?)|(?,mt)]. {
      subst.
      eauto using forall_writes_reads_to_last_write.
    }
    apply H in mt.
    destruct mt.
    eauto using last_write_cons.
  Qed.

  Let drf_reduces_write_def:
    forall ah ah' o n vs es x t,
    LastWriteDef (HB es) ah ->
    DRF_Reduces (C (n, fresh vs) :: es) ah o ah' ->
    DRF t (vs, es) ah ->
    MapsTo x n vs ->
    LastWriteDef (HB (C (n, fresh vs) :: es)) ah'.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    inversion H3; subst; clear H3.
    inversion H4; subst; clear H4; eauto.
  Qed.

  Lemma drf_to_last_write_def:
    forall t cg ah,
    DRF t cg ah ->
    LastWriteDef (HB (snd cg)) ah.
  Proof.
    induction t; intros. {
      inversion H; subst; clear H.
      unfold LastWriteDef, empty in *; intros.
      apply MM_Facts.empty_mapsto_iff in H.
      contradiction.
    }
    inversion H; subst; clear H. {
      destruct o; simpl in *; inversion H4; subst; clear H4.
      inversion H3; subst; clear H3.
      assert (cg0 = (vs0, es0)) by eauto using drf_to_cg, cg_fun; subst.
      simpl_node.
      assert (Hx:=H2).
      apply IHt in H2.
      simpl in *.
      eauto using drf_reduces_write_def.
    }
    apply last_write_def_impl with (P:=HB (snd cg0)).
    + simpl in H3.
      eapply hb_impl; eauto;
      eauto using drf_to_cg.
    + eauto.
  Qed.

  Lemma drf_ref_to_last_write:
    forall t cg ah,
    DRF t cg ah ->
    forall r h,
    MM.MapsTo r h ah ->
    exists a, LastWrite (HB (snd cg)) a h.
  Proof.
    intros.
    apply drf_to_last_write_def in H.
    unfold LastWriteDef in *.
    eauto.
  Qed.

  Lemma wf_race_free_access:
    forall a b r h t cg ah,
    DRF t cg ah ->
    MM.MapsTo r h ah ->
    List.In a h ->
    List.In b h ->
    RaceFreeAccess (HB (snd cg)) a b.
  Proof.
    intros.
    apply drf_to_race_free_history in H.
    unfold RaceFreeHistory in *.
    eauto.
  Qed.

  Lemma drf_last_write_fun:
    forall t cg ah h r a b,
    DRF t cg ah ->
    MM.MapsTo r h ah ->
    LastWrite (HB (snd cg)) a h ->
    LastWrite (HB (snd cg)) b h ->
    a = b.
  Proof.
    intros.
    assert (Hx:=H).
    apply drf_to_cg in Hx.
    apply drf_access_fun in H.
    eapply access_to_last_write_fun in H; eauto using
    hb_trans, cg_irrefl.
  Qed.

(*
  Lemma wf_access_fun:
    forall cg ah h r a b,
    WellFormed cg ah ->
    MM.MapsTo r h ah ->
    List.In a h ->
    List.In b h ->
    a_when a = a_when b ->
    a = b.
  Proof.
    intros.
    assert (AccessFun ah) by eauto using wf_access_fun_prop.
    eauto.
  Qed.
*)
(*
  Lemma wf_access_def:
    forall cg ah h r,
    WellFormed cg ah ->
    MM.MapsTo r h ah ->
    exists a, LastWrite (A:=Trace.datum) (HB (snd cg)) a h.
  Proof.
    intros.
    assert (LastWriteDef (HB (snd cg)) ah) by eauto using wf_last_write_def_prop.
    eauto.
  Qed.
*)
(*
  Let wf_hb_inv_cons_c:
    forall vs es t ah r h a b k n,
    DRF t (vs, es) ah ->
    MM.MapsTo r h ah ->
    Node n vs ->
    List.In a h ->
    List.In b h ->
    HB ((k, (n, fresh vs)) :: es) (a_when a) (a_when b) ->
    HB es (a_when a) (a_when b).
  Proof.
    intros.
    eapply wf_node in H2; eauto.
    eapply wf_node in H3; eauto.
(*    inversion H1.*)
    eapply hb_inv_cons_c in H4; eauto.
    - destruct H4; auto.
      rewrite H4 in *.
      simpl_node.
    - apply wf_edge_to_node_prop in H.
      auto using node_cons, node_eq, edge_to_node_cons_node, edge_to_node_cons_edge.
    - apply wf_lt_edges_prop in H.
      apply lt_edges_cons_edge.
      + auto.
      + simpl.
        auto using node_lt.
  Qed.
*)
(*
  Lemma wf_continue:
    forall x n vs es g t,
    MapsTo x n vs ->
    WellFormed (vs, es) g ->
    WellFormed (x :: vs, {|e_t:=t; e_edge:=(n, fresh vs)|} :: es) g.
  Proof.
    intros.
    apply Build_WellFormed.
    - apply lt_edges_cons_edge.
      + apply wf_lt_edges_prop in H0.
        auto.
      + simpl.
        eauto using maps_to_lt.
    - apply edge_to_node_cons_edge.
      + eauto using wf_edge_to_node_prop, edge_to_node_cons_node.
      + eauto using maps_to_to_node, node_cons.
      + auto using node_eq.
    - simpl.
      apply wf_node_def_prop in H0.
      auto using node_def_cons.
    - eauto using wf_access_fun_prop.
    - assert (Hwf := H0).
      apply wf_last_write_fun_prop in H0.
      unfold LastWriteFun in *.
      intros.
      assert (forall c,
        List.In c h ->
        HB ({| e_t := t; e_edge := (n, fresh vs) |} :: es) (a_when c) (a_when a) ->
        HB es (a_when c) (a_when a)). {
        intros.
        apply last_write_to_in in H2.
        eapply wf_hb_inv_cons_c with (n:=n) (t:=t); eauto using wf_node, maps_to_to_node.
      }
      assert (forall c,
        List.In c h ->
        HB ({| e_t := t; e_edge := (n, fresh vs) |} :: es) (a_when c) (a_when b) ->
        HB es (a_when c) (a_when b)). {
        intros.
        apply last_write_to_in in H3.
        eapply wf_hb_inv_cons_c with (n:=n) (t:=t); eauto using wf_node, maps_to_to_node.
      }
      apply last_write_impl_ex with (Q:=HB es) in H2; auto.
      apply last_write_impl_ex with (Q:=HB es) in H3; auto.
      eauto.
     - apply ordered_access_history_impl with (P:=HB es).
       + intros.
         eauto using hb_impl_cons.
       + apply wf_ordered_access_history_prop in H0; simpl; auto using hb_cons.
       + apply wf_ordered_access_history_prop in H0; simpl in *; auto.
     - unfold LastWriteDef.
       intros.
       assert (Hx := H0).
       apply wf_last_write_def_prop in Hx.
       apply Hx in H1.
       destruct H1 as (a, Hw).
       exists a.
       eauto using last_write_impl, hb_impl_cons.
  Qed.
*)
(*
  Let hb_inv_cons_c_0:
    forall vs es x n ah a b t k o,
    DRF ((x,o)::t) (x :: vs,(k, (n,fresh vs) ) :: es) ah ->
    HB ((k, (n,fresh vs)) :: es) (a_when (A:=Trace.datum) a) (a_when (A:=Trace.datum) b) ->
    HB es (a_when a) (a_when b) \/ a_when b = fresh vs.
  Proof.
    intros.
    apply hb_inv_cons_c with (x:=x) in H0; auto.
    - apply wf_edge_to_node_prop in H ; auto.
    - apply wf_lt_edges_prop in H; auto.
  Qed.
*)
  Lemma last_write_inv_c:
    forall x n vs ah ah' h es a r t k o,
    DRF t (vs,es) ah ->
    DRF ((x, o)::t) (x :: vs, (k, (n,fresh vs)) :: es) ah' ->
    MM.MapsTo r h ah ->
    LastWrite (A:=Trace.datum) (HB ((k, (n,fresh vs)) :: es)) a h ->
    LastWrite (HB es) a h.
  Proof.
    intros.
    destruct H2 as (X,Y,Hfw).
    apply last_write_def; eauto.
    unfold ForallWrites in *; intros b Hin Hwb.
    apply Hfw in Hin; auto.
    destruct Hin as [Hin|?]; auto.
    assert (Hx:=drf_to_cg H0).
    apply hb_inv_cons_c with (x:=x) (a:=a_when b) (b:= a_when a) in Hx; repeat auto.
    destruct Hx as [?|R]; auto.
    subst.
    assert (Hn: Node (a_when a) vs) by eauto using drf_to_node.
    rewrite R in *.
    simpl_node.
  Qed.

  Lemma last_write_inv_j:
    forall x n vs ah ah' h es a r t e k o,
    DRF t (vs,es) ah ->
    DRF ((x,o)::t) (x :: vs,(k, (n,fresh vs)) :: e :: es) ah' ->
    MM.MapsTo r h ah ->
    LastWrite (A:=Trace.datum) (HB ((k, (n,fresh vs) ) :: e :: es)) a h ->
    LastWrite (HB (e::es)) a h.
  Proof.
    intros.
    destruct H2 as (X,Y,Hfw).
    apply last_write_def; eauto.
    unfold ForallWrites in *; intros b Hin Hwb.
    apply Hfw in Hin; auto.
    destruct Hin as [Hin|?]; auto.
    assert (Hx:=drf_to_cg H0).
    apply hb_inv_cons_c with (x:=x) (a:=a_when b) (b:= a_when a) in Hx; repeat auto.
    destruct Hx as [?|R]; auto.
    subst.
    assert (Hn: Node (a_when a) vs) by eauto using drf_to_node.
    rewrite R in *.
    simpl_node.
  Qed.

  Lemma last_write_inv_hb:
    forall t vs es ah r h a n x e,
    CG.T.CG (e::t) (x::vs, C (n, fresh vs) :: es) ->
    DRF t (vs, es) ah ->
    MM.MapsTo r h ah ->
    LastWrite (HB (C (n, fresh vs) :: es)) a h ->
    LastWrite (HB es) a h.
  Proof.
    intros.
    inversion H2; subst; clear H2.
    apply last_write_def; auto.
    unfold ForallWrites in *.
    intros b; intros.
    apply H5 in H2; auto.
    destruct H2; auto.
    apply hb_inv_cons_c with (x:=x) (t:=map event_to_cg (e::t)) in H2; auto.
    destruct H2; auto.
    eapply drf_to_node with (t:=t) (vs:=vs) (es:=es) (ah:=ah) (r:=r) in H4; auto.
    rewrite H2 in *.
    simpl_node.
  Qed.

  Let drf_reduces_fun:
    forall es ah o ah1 ah2,
    DRF_Reduces es ah o ah1 ->
    DRF_Reduces es ah o ah2 ->
    ah1 = ah2.
  Proof.
    intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    symmetry in H3.
    inversion H3; subst; clear H3.
    eauto using add_fun.
  Qed.

  Lemma drf_cg_fun:
    forall t cg cg' ah ah',
    DRF t cg ah ->
    DRF t cg' ah' ->
    cg' = cg.
  Proof.
    intros.
    apply drf_to_cg in H.
    apply drf_to_cg in H0.
    eauto using cg_fun.
  Qed.

  Lemma drf_fun:
    forall t cg ah ah',
    DRF t cg ah ->
    DRF t cg ah' ->
    ah' = ah.
  Proof.
    induction t; intros. {
      inversion H; subst; clear H.
      inversion H0; subst; clear H0.
      trivial.
    }
    inversion H; subst; clear H. {
      inversion H0; subst; clear H0. {
        rewrite H12 in *.
        inversion H5; subst; clear H5.
        assert (cg0 = cg) by eauto using drf_cg_fun; subst.
        assert (ah0 = ah1) by eauto; subst.
        eauto.
      }
      rewrite H5 in *.
      inversion H12.
    }
    inversion H0; subst; clear H0. {
      rewrite H7 in *.
      inversion H11.
    }
    assert (cg0 = cg) by eauto using drf_cg_fun; subst.
    eauto.
  Qed.

  (**
   Given a race-free trace, if we have a read, then
   there is a last-write that precedes the read.
   *)

  Theorem drf_check_inv_read_last_write:
    forall x n vs ah ah' d es r t,
    DRF t (vs,es) ah ->
    DRF ((x, Trace.MEM r (Trace.READ d))::t) (x :: vs,C (n, fresh vs) :: es) ah' ->
    exists h a,
    MM.MapsTo r h ah /\ LastWrite (HB es) a h /\ a_what a = Some d
    /\ HB (C (n, fresh vs) :: es) (a_when a) (fresh vs).
  Proof.
    intros.
    rename H into Hwf.
    rename H0 into Hwf'.
    (* -- *)
    inversion Hwf'; subst. {
      assert (cg = (vs, es)) by eauto using drf_cg_fun; subst.
      assert (ah0 = ah) by eauto using drf_fun; subst; clear Hwf.
      inversion H8; subst; clear H8. (* DRF_Reduces *)
      symmetry in H; (* C _ :: es = C _ :: es' *)
      inversion H; subst; clear H.
      simpl in *; subst; inversion H7; subst; clear H7. (* op_to_ah _ = Some _ *)
      inversion H0; subst; clear H0. (* Add *)
      assert (Hlw := H9). (* LastWrite *)
      exists l; exists (n', Some d).
      split; auto.
      split; eauto using last_write_inv_c, last_write_to_in.
      simpl; split; auto.
      inversion H9; subst; clear H9. (* LastWrite *)
      apply H8 in H; subst; auto; simpl in *. (* H8: WriteSafe _, H: Write *)
      destruct H; simpl in *; auto. (* HB \/ eq *)
      subst.
      eapply drf_to_node in H0; eauto; simpl in *. (* In (fresh vs) *)
      simpl_node.
    }
    simpl in *.
    inversion H7.
  Qed.

(*
  Section LastWriteCanJoin.

    Let LastWriteCanJoin (cg:computation_graph) sj (ah:cg_access_history) :=
      forall x a h r,
      MM.MapsTo r h ah ->
      LastWrite (HB (snd cg)) a h ->
      a_what a = Some (Trace.d_task x) ->
      SJ_CG.CanJoin (a_when a) x sj.

    Lemma mem_last_write_can_join:
      forall t cg ah sj,
      DRF t cg ah ->
      SJ_CG.SJ (map CG.T.event_to_cg t) cg sj ->
      LastWriteCanJoin cg sj ah.
    Proof.
      induction t; intros. {
        inversion H0; subst; clear H0.
        inversion H; subst; clear H.
        unfold LastWriteCanJoin.
        intros.
        unfold empty in *.
        rewrite MM_Facts.empty_mapsto_iff in *.
        contradiction.
      }
      unfold LastWriteCanJoin; intros.
      rename H2 into Hlw.
      inversion H; subst; rename H into Hdrf. {
        (* op_to_ah _ = Some _ *)
        destruct o; simpl in *; inversion H7; subst; clear H7.
        inversion H6; subst; clear H6; simpl_node. (* CG *)
        assert (cg0 = (vs0, es0)) by
          eauto using drf_to_cg, cg_fun; subst.
        inversion H0; subst; clear H0. (* SJ *)
        clear H15 (* CG *).
        rename sj0 into sj.
        rename vs0 into vs.
        rename es0 into es.
        assert (cg = (vs,es)) by eauto using SJ_CG.sj_to_cg, cg_fun; subst.
        assert (Hlwcj: LastWriteCanJoin (vs,es) sj ah0) by eauto.
        unfold LastWriteCanJoin in Hlwcj.
        destruct m0; simpl in *; inversion H2; subst; clear H2. { (* match _ with *)
          inversion H10; subst; clear H10. (* DRF_Reduces *)
          inversion H2; subst; clear H2. (* C _ :: _ = C _ :: _ *)
          inversion H6; subst; clear H6. (* Add *)
          rewrite MM_Facts.add_mapsto_iff in *.
          destruct H1 as [(?,?)|(?,?)]. {
            subst.
            apply last_write_inv_cons_read in Hlw.
            eapply last_write_inv_c in Hlw; eauto.
            eapply Hlwcj with (x:=x) in Hlw; eauto.
            eauto using SJ_CG.can_join_cons.
          }
          eapply last_write_inv_c in Hlw; eauto.
          eapply Hlwcj with (x:=x) in Hlw; eauto.
          eauto using SJ_CG.can_join_cons.
        }
        inversion H10; subst; clear H10. (* DRF_Reduces *)
        inversion H2; subst; clear H2. (* C _ :: _ = C _ :: _ *)
        inversion H6; subst; clear H6; (* Add *)
        rewrite MM_Facts.add_mapsto_iff in *;
        destruct H1 as [(?,?)|(?,?)]; subst.
        - apply last_write_inv_cons_nil in Hlw.
          subst; simpl in *; subst.
          inversion H3; subst; clear H3.
          assert (R: fresh vs = fresh sj). {
            eauto using SJ_CG.sj_to_length_0, maps_to_length_rw.
          }
          rewrite R; clear R.
          clear H9.
          apply SJ_CG.can_join_copy.
          
        -
        

        eapply last_write_inv_c with (r:=r) in Hlw; eauto.
        eapply Hlwcj with (x:=x) in Hlw; eauto.
        eauto using SJ_CG.can_join_cons.
      }
    Qed.
  End LastWriteCanJoin.
*)
(*
  Lemma wf_last_write_inv_cons_write:
    forall cg ah cg' ah' r h a b,
    WellFormed cg ah ->
    WellFormed cg' ah' ->
    MM.MapsTo r h ah ->
    MM.MapsTo r (b::h) ah' ->
    Write b ->
    WriteSafe (HB (snd cg')) b h ->
    LastWrite (HB (snd cg')) a (b :: h) ->
    b = a.
  Proof.
    intros.
    inversion H3; subst; clear H3; simpl in *.
    assert (a_when (n, Some x) = a_when a). {
      eapply last_write_inv_cons_write; eauto using hb_irrefl, wf_lt_edges_prop.
      eauto using hb_trans.
    }
    apply wf_access_fun with (ah:=ah') (cg:=cg') (r:=r) (h:=(n,Some x)::h) in H3; auto using in_eq.
    eapply last_write_to_in; eauto. 
  Qed.
*)
End AccessFun.

  Lemma drf_inv_alloc:
    forall (vs:list tid) e es ah m t x,
    DRF ((x,Trace.MEM m Trace.ALLOC)::t) (x::vs, CG.C e :: es) ah  ->
    DRF t (vs,es) ah.
  Proof.
    intros.
    inversion H; subst; clear H;
    simpl in *; inversion H8.
    inversion H7; subst; clear H7.
    assert ((vs,es) = cg). {
      eapply drf_to_cg in H6.
      eauto using cg_fun.
    }
    subst.
    assumption.
  Qed.

  Lemma drf_inv_init:
    forall (vs:list tid) es ah t x,
    DRF ((x,Trace.INIT)::t) (x::vs, es) ah  ->
    DRF t (vs,es) ah.
  Proof.
    intros.
    inversion H; subst; clear H;
    simpl in *; inversion H8.
    inversion H7; subst; clear H7.
    assert ((vs,es) = cg). {
      eapply drf_to_cg in H6.
      eauto using cg_fun.
    }
    subst.
    assumption.
  Qed.

  Lemma drf_inv_future:
    forall (vs:list tid) es ah t x y e e',
    DRF ((x,Trace.FUTURE y)::t) (y::x::vs, F e:: C e' :: es) ah  ->
    DRF t (vs,es) ah.
  Proof.
    intros.
    inversion H; subst; clear H;
    simpl in *; inversion H8.
    inversion H7; subst; clear H7.
    assert ((vs,es) = cg). {
      eapply drf_to_cg in H6.
      eauto using cg_fun.
    }
    subst.
    assumption.
  Qed.

  Lemma drf_inv_force:
    forall (vs:list tid) es ah t x y e e',
    DRF ((x,Trace.FORCE y)::t) (x::vs, J e:: C e' :: es) ah  ->
    DRF t (vs,es) ah.
  Proof.
    intros.
    inversion H; subst; clear H;
    simpl in *; inversion H8.
    inversion H7; subst; clear H7.
    assert ((vs,es) = cg). {
      eapply drf_to_cg in H6.
      eauto using cg_fun.
    }
    subst.
    assumption.
  Qed.

  Lemma drf_inv_read:
    forall (vs:list tid) es ah t x r d n,
    DRF ((x,Trace.MEM r (Trace.READ d))::t) (x::vs, C (n, fresh vs) :: es) ah  ->
    exists ah',
    DRF t (vs,es) ah' /\ 
    Add (HB (C (n, fresh vs) :: es)) ah' (r, fresh vs, (READ, d)) ah.
  Proof.
    intros.
    inversion H; subst; clear H;
    simpl in *; inversion H8; subst; clear H8.
    assert ((vs,es) = cg). {
      eapply drf_to_cg in H5.
      inversion H7; subst; clear H7.
      eauto using cg_fun.
    }
    subst.
    exists ah0.
    inversion H9; subst; clear H9.
    inversion H1; subst; clear H1.
    auto.
  Qed.

  Lemma drf_inv_write:
    forall (vs:list tid) es ah t x r d n,
    DRF ((x,Trace.MEM r (Trace.WRITE d))::t) (x::vs, C (n, fresh vs) :: es) ah  ->
    exists ah',
    DRF t (vs,es) ah' /\ 
    Add (HB (C (n, fresh vs) :: es)) ah' (r, fresh vs, (WRITE, d)) ah.
  Proof.
    intros.
    inversion H; subst; clear H;
    simpl in *; inversion H8; subst; clear H8.
    assert ((vs,es) = cg). {
      eapply drf_to_cg in H5.
      inversion H7; subst; clear H7.
      eauto using cg_fun.
    }
    subst.
    exists ah0.
    inversion H9; subst; clear H9.
    inversion H1; subst; clear H1.
    auto.
  Qed.

  Lemma last_write_inv_future:
    forall x n vs ah h es a r t e k y,
    DRF ((x,Trace.FUTURE y)::t) (y::x::vs,(k, (n,fresh (x::vs))) :: e :: es) ah ->
    MM.MapsTo r h ah ->
    LastWrite (A:=Trace.datum) (HB ((k, (n,fresh (x::vs)) ) :: e :: es)) a h ->
    LastWrite (HB es) a h.
  Proof.
    intros.
    destruct H1 as (X,Y,Hfw). (* LastWrite *)
    apply last_write_def; eauto.
    unfold ForallWrites in *; intros b Hin Hwb.
    apply Hfw in Hin; auto.
    destruct Hin as [Hin|?]; auto.
    assert (Hx:=drf_to_cg H). (* DRF *)
    inversion Hx; subst; simpl_node.
    eapply hb_inv_cons_fork in Hin; eauto.
    apply drf_inv_future in H. (* DRF *)
    destruct Hin as [?|[(R1,R2)|[(R1,?)|[(R1,?)|[(R1,?)|[(R1,?)|(?,(R1,?))]]]]]];
    auto; subst; try (
      assert (Node (a_when a) vs) by eauto using drf_to_node;
      rewrite <- R1 in *;
      simpl_node
    ).
  Qed.

  Lemma last_write_inv_force:
    forall x vs ah h es a r t e1 e2 y,
    DRF ((x,Trace.FORCE y)::t) (x::vs, e1 :: e2 :: es) ah ->
    MM.MapsTo r h ah ->
    LastWrite (A:=Trace.datum) (HB (e1 :: e2 :: es)) a h ->
    LastWrite (HB es) a h.
  Proof.
    intros.
    destruct H1 as (X,Y,Hfw). (* LastWrite *)
    apply last_write_def; eauto.
    unfold ForallWrites in *; intros b Hin Hwb.
    apply Hfw in Hin; auto.
    destruct Hin as [Hin|?]; auto.
    assert (Hx:=drf_to_cg H). (* DRF *)
    inversion Hx; subst; simpl_node.
    eapply hb_inv_cons_join in Hin; eauto.
    apply drf_inv_force in H. (* DRF *)
    destruct Hin as [?|[(R1,?)|[(R1,?)|[(R1,?)|(R1,?)]]]]; auto;
    try (
      assert (Node (a_when a) vs) by eauto using drf_to_node;
      rewrite <- R1 in *;
      simpl_node
    ).
  Qed.

  Lemma last_write_inv_alloc:
    forall x vs ah h es a r t e m,
    DRF ((x,Trace.MEM m Trace.ALLOC)::t) (x::vs, e :: es) ah ->
    MM.MapsTo r h ah ->
    LastWrite (A:=Trace.datum) (HB (e :: es)) a h ->
    LastWrite (HB es) a h.
  Proof.
    intros.
    assert (Hx:=drf_to_cg H). (* DRF *)
    inversion Hx; subst; simpl_node.
    apply drf_inv_alloc in H.
    eapply last_write_inv_hb in H1; eauto using drf_to_cg.
  Qed.


  Lemma last_write_inv_read:
    forall vs ah hr es a r t m d ah' n x,
    DRF t (vs, es) ah ->
    Add (HB (C (n, fresh vs) :: es)) ah (m, fresh vs, (READ, d)) ah' ->
    MM.MapsTo r hr ah' ->
    LastWrite (A:=Trace.datum) (HB (C (n, fresh vs) :: es)) a hr ->
    MapsTo x n vs ->
    (m = r /\ exists hm, hr = (fresh vs, None)::hm /\ MM.MapsTo r hm ah /\ LastWrite (HB es) a hm) \/
    (m <> r /\ MM.MapsTo r hr ah /\ LastWrite (HB es) a hr).
  Proof.
    intros.
    assert (Hdrf: DRF ((x,Trace.MEM m (Trace.READ d))::t) (x::vs, C (n, fresh vs):: es) ah'). {
      intros.
      eapply drf_some with (o':=(m, (READ, d))); eauto.
      - simpl.
        apply drf_to_cg in H.
        apply CG.cg_continue; auto using maps_to_eq.
      - simpl.
        inversion H0; subst.
        eapply drf_reduces; eauto.
    }
    assert (Hx:=drf_to_cg H). (* DRF *)
    inversion H0; subst; clear H0.
    assert (mt:=H1).
    rewrite MM_Facts.add_mapsto_iff in mt.
    destruct mt as [(?,?)|(?,?)]. {
      subst.
      apply last_write_inv_cons_read in H2.
      left.
      intuition.
      exists l.
      intuition.
      eapply last_write_inv_hb in H2; eauto using drf_to_cg.
    }
    right.
    intuition.
    eapply last_write_inv_hb in H2; eauto using drf_to_cg.
  Qed.

  Lemma last_write_inv_write:
    forall vs ah hr es a r t m d ah' n x,
    DRF t (vs, es) ah ->
    Add (HB (C (n, fresh vs) :: es)) ah (m, fresh vs, (WRITE, d)) ah' ->
    MM.MapsTo r hr ah' ->
    LastWrite (A:=Trace.datum) (HB (C (n, fresh vs) :: es)) a hr ->
    MapsTo x n vs ->
    (m = r /\ a = (fresh vs, Some d) /\ (fresh vs, Some d) :: nil = hr /\ ~ MM.In m ah) \/
    (m <> r /\ MM.MapsTo r hr ah /\ LastWrite (HB es) a hr) \/
    (m = r /\ a = (fresh vs, Some d) /\ exists l, (fresh vs, Some d) :: l = hr /\ MM.MapsTo m l ah).
  Proof.
    intros.
    assert (Hdrf: DRF ((x,Trace.MEM m (Trace.WRITE d))::t) (x::vs, C (n, fresh vs):: es) ah'). {
      intros.
      eapply drf_some with (o':=(m, (WRITE, d))); eauto.
      - simpl.
        apply drf_to_cg in H.
        apply CG.cg_continue; auto using maps_to_eq.
      - simpl.
        eapply drf_reduces; eauto.
    }
    assert (Hx:=drf_to_cg H). (* DRF *)
    assert (mt:=H1).
    inversion H0; subst; clear H0. { (* Add *)
      rewrite MM_Facts.add_mapsto_iff in mt.
      destruct mt as [(?,?)|(?,?)]. {
        left.
        subst.
        intuition.
        eauto using last_write_inv_cons_nil.
      }
      eapply last_write_inv_hb in H2; eauto using drf_to_cg.
    }
    rewrite MM_Facts.add_mapsto_iff in mt.
    destruct mt as [(?,?)|(?,?)]. {
      subst.
      apply last_write_inv_cons in H2.
      destruct H2 as [Hy|(Ha,Hb)]. {
        right.
        right.
        intuition.
        eauto 7.
      }
      eapply last_write_inv_hb in Hb; eauto using drf_to_cg.
      assert (Hw: Write (fresh vs, Some d)) by auto using write_some.
      apply Ha in Hw; clear Ha.
      destruct Hw as [Hw|Hw]. {
        simpl in *.
        apply drf_to_cg in Hdrf.
        eapply hb_inv_cons_continue in Hw; eauto.
        destruct Hw as [N|[(?,?)|(?,N)]].
        - eapply cg_hb_absurd_node_l in N; eauto; contradiction.
        - subst.
          simpl_node.
        - eapply cg_hb_absurd_node_l in N; eauto; contradiction.
      }
      simpl in *.
      apply last_write_to_in in Hb.
      assert (Hn: Node (a_when a) vs). {
        eauto using drf_to_node.
      }
      rewrite <- Hw in *.
      simpl_node.
    }
    eapply last_write_inv_hb in H2; eauto using drf_to_cg.
  Qed.

  Section forall_prec.
  Let forall_prec_cons:
    forall (a:access Trace.datum node) es (h:list (access Trace.datum node)) e,
    List.Forall
       (fun b =>
        Write b -> HB es (a_when b) (a_when a) \/ a = b) h ->
    List.Forall
      (fun b =>
        Write b -> HB (e :: es) (a_when b) (a_when a) \/ a = b) h.
  Proof.
    intros.
    rewrite Forall_forall in *; intros.
    apply H in H0; auto.
    destruct H0; auto using hb_cons.
  Qed.

  Lemma last_write_to_forall_prec:
    forall t vs es ah,
    DRF t (vs, es) ah ->
    forall r a h,
    MM.MapsTo r h ah ->
    LastWrite (HB es) a h ->
    List.Forall (fun b => Write b -> HB es (a_when b) (a_when a) \/ a = b) h.
  Proof.
    induction t; intros. {
      inversion H; subst; clear H.
      unfold empty in *.
      rewrite MM_Facts.empty_mapsto_iff in *.
      contradiction.
    }
    assert (Hx:=H).
    assert (Hdrf:=H).
    apply drf_to_cg in Hx;
    destruct a as (x,[]);
    inversion Hx; subst; clear Hx; simpl_node.
    - eauto using drf_inv_init.
    - destruct m0.
      + eauto using last_write_inv_alloc, drf_inv_alloc.
      + eapply drf_inv_read in H; eauto.
        destruct H as (ah', (?,?)).
        eapply last_write_inv_read in H1; eauto.
        destruct H1 as [(?,(l,(?,(?,Hw))))|(?,(?,?))].
        * subst.
          apply Forall_cons; intros. {
            inversion H1.
          }
          eauto.
        * eauto.
      + apply drf_inv_write in H.
        destruct H as (ah', (?, Hadd)).
        eapply last_write_inv_write in H1; eauto.
        destruct H1 as [(?,(?,(?,?)))|[(?,(?,?))|(?,(?,(l,(?,?))))]].
        * subst.
          apply Forall_cons. {
            intros.
            simpl.
            auto.
          }
          auto using Forall_nil.
        * eauto.
        * subst.
          apply Forall_cons; intros; auto.
          assert (Hlw: exists a, LastWrite (HB (snd (vs0,es0))) a l). {
            eauto using drf_ref_to_last_write.
          }
          simpl in *; destruct Hlw as (a, Hlw).
          eapply IHt in Hlw; eauto.
          rewrite Forall_forall in *.
          intros c; intros.
          assert (Hw := H2).
          apply Hlw in H2; auto.
          destruct H2. {
            inversion Hadd; subst; clear Hadd. {
              assert (l = nil). {
                rewrite MM_Facts.add_mapsto_iff in *.
                destruct H0 as [(?,Heq)|(?,_)].
                - inversion Heq; subst; auto.
                - contradiction.
              }
              subst.
              inversion H1.
            }
            assert (l0 = l) by eauto using MM_Facts.MapsTo_fun; subst.
            unfold WriteSafe,ForallWrites in *.
            apply H12 in H1; auto.
            destruct H1. {
              simpl in *.
              auto.
            }
            simpl in *.
            rewrite H1 in *.
            eapply cg_hb_absurd_node_l in H2; eauto; contradiction.
          }
          subst.
          inversion Hadd; subst; clear Hadd. {
            assert (l = nil). {
              rewrite MM_Facts.add_mapsto_iff in *.
              destruct H0 as [(?,Heq)|(?,_)].
              - inversion Heq; subst; auto.
              - contradiction.
            }
            subst.
            inversion H1.
          }
          assert (l0 = l) by eauto using MM_Facts.MapsTo_fun; subst.
          unfold WriteSafe,ForallWrites in *.
          assert (Hi:=H1). (* In c l *)
          apply H11 in H1; auto.
          destruct H1. {
            simpl in *.
            auto.
          }
          simpl in *.
          assert (Node (a_when c) vs0). {
            eauto using drf_to_node.
          }
          rewrite H1 in *.
          simpl_node.
        - apply drf_inv_future in Hdrf.
          eauto using last_write_inv_future.
        - apply drf_inv_force in Hdrf.
          eauto using last_write_inv_force.
  Qed.
  End forall_prec.
(*
  Lemma last_write_inv_write:
    forall ah x r d t vs es n a h,
    DRF ((x, Trace.MEM r (Trace.WRITE d))::t) (x :: vs,C (n, fresh vs) :: es) ah ->
    MM.MapsTo r ((fresh vs, Some d) :: h) ah ->
    LastWrite (HB (C (n, fresh vs) :: es)) a ((fresh vs, Some d) :: h) ->
    a = (fresh vs, Some d).
  Proof.
    intros.
    inversion H; subst; clear H;
    simpl in *; inversion H10; subst; clear H10.
    inversion H11; subst; clear H11.
    inversion H3; subst; clear H3.
    inversion H9; subst; clear H9.
    simpl_node.
    rename es' into es.
    assert (cg = (vs, es)). {
      eauto using drf_to_cg, cg_fun.
    }
    subst.
    inversion H1; subst; clear H1.
    simpl in *.
    destruct H2; auto.
    unfold ForallWrites in *.
    apply Forall_forall in H3.
    inversion H3; subst; clear H3.
    assert (Hw: Write (fresh vs, Some d)) by auto using write_some.
    apply H8 in Hw.
  Qed.
*)
(*
  Ltac simpl_drf :=
  match goal with
  | [ H1: DRF_Check _ _ (Trace.MEM _ Trace.ALLOC) _ |- _ ] =>
    apply drf_check_inv_alloc in H1; inversion H1; subst; clear H1
  | [ H1: DRF_Check _ _ (Trace.MEM _ (Trace.READ _)) _ |- _ ] =>
    apply drf_check_inv_read in H1; inversion H1; subst; clear H1
  | [ H1: DRF_Check _ _ (Trace.MEM _ (Trace.WRITE _ )) _ |- _ ] =>
    apply drf_check_inv_write in H1; inversion H1; subst; clear H1
  | [ H1: DRF_Check _ _ (Trace.MEM _ ?o) _ |- _ ] =>
    destruct o;
    match goal with
    | [ H1: DRF_Check _ _ (Trace.MEM _ Trace.ALLOC) _ |- _ ] =>
      apply drf_check_inv_alloc in H1; inversion H1; subst; clear H1
    | [ H1: DRF_Check _ _ (Trace.MEM _ (Trace.READ _)) _ |- _ ] =>
      apply drf_check_inv_read in H1; inversion H1; subst; clear H1
    | [ H1: DRF_Check _ _ (Trace.MEM _ (Trace.WRITE _ )) _ |- _ ] =>
      apply drf_check_inv_write in H1; inversion H1; subst; clear H1
    end
  | [ H1: DRF_Check _ _ (Trace.FUTURE _) _ |- _ ] =>
    apply drf_check_inv_future in H1; subst
  | [ H1: DRF_Check _ _ (Trace.FORCE _) _ |- _ ] =>
    apply drf_check_inv_force in H1; subst
  | [ H1: DRF_Check _ _ (Trace.INIT) _ |- _ ] =>
    apply drf_check_inv_init in H1; subst
  end.
*)

End T.