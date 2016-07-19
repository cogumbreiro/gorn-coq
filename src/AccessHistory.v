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
  Notation HBE a b := (HB a b \/ a_when a = a_when b).

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
    ~ MM.In r g ->
    (* update the shared memory to record the allocation *)
    RaceFreeAdd g (r, n, (ALLOC, d)) (MM.add r ((n, Some d)::nil) g)

  | race_free_read:
    forall g l n r a d,
    MM.MapsTo r l g ->
    (* same as [WriteSafe] *)
    LastWrite a l ->
    HB a (n, None) ->
    a_what a = Some d ->
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

  Ltac expand H := inversion H; subst; clear H.

  Variable lt_trans:
    forall x y z,
    Lt x y ->
    Lt y z ->
    Lt x z.

  Variable lt_irrefl:
    forall x,
    ~ Lt x x.

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
      auto using race_free_access_refl_when.
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
    inversion H0; subst; clear H0; eauto using write_safe_def.
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

  Let hb_eq_when_left:
    forall x y z,
    HB x z ->
    a_when y = a_when x ->
    HB y z.
  Proof.
    intros.
    rewrite H0.
    assumption.
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
    eauto.
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

  Lemma last_write_inv_cons_write:
    forall a n l d,
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
    assert (Hx : Write (n, Some d)) by auto using write_eq.
    apply Hi in Hx.
    destruct Hx. {
      assert (HB a (n, Some d)) by eauto using write_safe_hb.
      assert (HB a a) by eauto.
      apply lt_irrefl in H4.
      contradiction.
    }
    auto.
  Qed.

  Lemma last_write_cons_read:
    forall a n l,
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

  Lemma last_write_cons_write:
    forall e d h,
    WriteSafe (e, Some d) h ->
    LastWrite (e, Some d) ((e, Some d) :: h).
  Proof.
    intros.
    apply last_write_def; auto using in_eq.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    unfold ForallWrites in *; intros.
    destruct H0. {
      subst; auto.
    }
    eauto.
  Qed.

  Definition LastWriteFun ah :=
    forall a b r h,
    MM.MapsTo r h ah ->
    LastWrite a h ->
    LastWrite b h ->
    a = b.

  Definition AccessFun ah :=
    forall a b r h,
    MM.MapsTo r h ah ->
    List.In a h ->
    List.In b h ->
    a_when a = a_when b ->
    a = b.

  Definition LastWriteDef ah :=
    forall r h,
    MM.MapsTo r h ah ->
    exists a, LastWrite a h.

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

  Lemma last_write_to_write:
    forall a h,
    LastWrite a h ->
    Write a.
  Proof.
    intros.
    inversion H; auto.
  Qed.

  Lemma last_write_to_in:
    forall a h,
    LastWrite a h ->
    List.In a h.
  Proof.
    intros; inversion H; auto.
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

  Let write_safe_impl:
    forall a h,
    WriteSafe (A:=A) P a h ->
    WriteSafe Q a h.
  Proof.
    intros.
    inversion H.
    eauto using write_safe_def, last_write_impl.
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
  Require Import Tid.
  Require Trace.
  Require Import Node.
  Require CG.

  Notation cg_access_history := (access_history Trace.datum node).
  Notation cg_access_history_op := (op Trace.datum).

  Require Import CG.
  Import CG.T.

  Section Defs.

  Inductive DRF_Reduces es (ah:cg_access_history) : (mid * cg_access_history_op) -> cg_access_history -> Prop :=
  | drf_reduces:
    forall n n' o ah' r es',
    es = CG.C (n, n') :: es' ->
    RaceFreeAdd (CG.HB es) ah (r, n', o) ah' ->
    DRF_Reduces es ah (r, o) ah'.

  Definition op_to_ah (o:Trace.op) : option (mid*cg_access_history_op) :=
  match o with
  | Trace.ALLOC r d => Some (r, (ALLOC, d))
  | Trace.READ r d => Some (r, (READ, d))
  | Trace.WRITE r d => Some (r, (WRITE, d))
  | _ => None
  end.

  Inductive DRF_Check es (ah:cg_access_history) : Trace.op -> cg_access_history -> Prop :=
  | drf_check_some:
    forall o o' ah',
    op_to_ah o = Some o' ->
    DRF_Reduces es ah o' ah' ->
    DRF_Check es ah o ah'
  | drf_check_none:
    forall o,
    op_to_ah o = None ->
    DRF_Check es ah o ah.

  Definition NodeDef (vs:list tid) (g:cg_access_history) :=
    forall a r h,
    MM.MapsTo r h g ->
    List.In a h ->
    Node (a_when a) vs.

  Lemma drf_check_inv_alloc:
    forall (vs:list tid) n es ah m d ah',
    DRF_Check (CG.C (n, fresh vs) :: es) ah (Trace.ALLOC m d) ah' ->
    RaceFreeAdd (CG.HB (CG.C (n, fresh vs) :: es)) ah
       (m, fresh vs, (ALLOC, d)) ah'.
  Proof.
    intros.
    inversion H; subst; clear H; simpl in *; inversion H0; subst; clear H0.
    inversion H1; subst; clear H1.
    inversion H2; subst; clear H2.
    assumption.
  Qed.

  Lemma drf_check_inv_read:
    forall n (vs:list tid) es ah m d ah',
    DRF_Check (CG.C (n, fresh vs) :: es) ah (Trace.READ m d) ah' ->
    RaceFreeAdd (CG.HB (CG.C (n, fresh vs) :: es)) ah
       (m, fresh vs, (READ, d)) ah'.
  Proof.
    intros.
    inversion H; subst; clear H; simpl in *; inversion H0; subst; clear H0.
    inversion H1; subst; clear H1.
    simpl in *.
    inversion H2; subst.
    auto.
  Qed.

  Lemma drf_check_inv_continue:
    forall cg ah ah',
    DRF_Check cg ah Trace.CONTINUE ah' ->
    ah' = ah.
  Proof.
    intros.
    inversion H; subst; clear H; simpl in *; inversion H0.
    trivial.
  Qed.

  Lemma drf_check_inv_future:
   forall cg ah ah' t l,
    DRF_Check cg ah (Trace.FUTURE t l) ah' ->
    ah' = ah.
  Proof.
    intros.
    inversion H; subst; clear H; simpl in *; inversion H0; subst; clear H0.
    trivial.
  Qed.

  Lemma drf_check_inv_force:
   forall cg ah ah' t l,
    DRF_Check cg ah (Trace.FORCE t l) ah' ->
    ah' = ah.
  Proof.
    intros.
    inversion H; subst; clear H; simpl in *; inversion H0; subst; clear H0.
    trivial.
  Qed.

  Lemma drf_check_inv_write:
    forall ah ah' d r n (vs:list tid) es,
    DRF_Check (CG.C (n, fresh vs) :: es) ah (Trace.WRITE r d) ah' ->
    RaceFreeAdd (CG.HB (CG.C (n, fresh vs) :: es)) ah
       (r, fresh vs, (WRITE, d)) ah'.
  Proof.
    intros.
    inversion H; subst; clear H; simpl in *; inversion H0; subst; clear H0.
    inversion H1; subst; clear H1.
    simpl in *; inversion H2; subst.
    auto.
  Qed.
End Defs.

  Ltac simpl_drf_check :=
  match goal with
  | [ H1: DRF_Check _ _ (Trace.ALLOC _ _) _ |- _ ] =>
    apply drf_check_inv_alloc in H1; inversion H1; subst; clear H1
  | [ H1: DRF_Check _ _ Trace.CONTINUE _ |- _ ] =>
    apply drf_check_inv_continue in H1; subst
  | [ H1: DRF_Check _ _ (Trace.READ _ _) _ |- _ ] =>
    apply drf_check_inv_read in H1; inversion H1; subst; clear H1
  | [ H1: DRF_Check _ _ (Trace.WRITE _ _) _ |- _ ] =>
    apply drf_check_inv_write in H1; inversion H1; subst; clear H1
  | [ H1: DRF_Check _ _ (Trace.FUTURE _ _) _ |- _ ] =>
    apply drf_check_inv_future in H1; subst
  | [ H1: DRF_Check _ _ (Trace.FORCE _ _) _ |- _ ] =>
    apply drf_check_inv_force in H1; subst
  end.

Section Props.

  Let ordered_access_history_cg:
    forall cg e cg' (ah:cg_access_history),
    OrderedAccessHistory (HB (snd cg)) ah ->
    CG.Reduces cg e cg' ->
    OrderedAccessHistory (HB (snd cg')) ah.
  Proof.
    intros.
    apply ordered_access_history_impl with (P:=CG.HB (snd cg));
    eauto using CG.hb_impl.
  Qed.

  Let ordered_access_history_drf_check:
    forall cg a o cg' ah ah',
    OrderedAccessHistory (HB (snd cg)) ah ->
    TReduces cg (a,o) cg' ->
    DRF_Check (snd cg') ah o ah' ->
    OrderedAccessHistory (HB (snd cg')) ah'.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    - inversion H3; subst; clear H3.
      eauto using ordered_access_history_cg, ordered_access_history_add.
    - eauto using ordered_access_history_cg.
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

  Let access_fun_cg_reduces:
    forall cg ah a o cg' ah',
    NodeDef (fst cg) ah ->
    AccessFun ah ->
    TReduces cg (a,o) cg' ->
    DRF_Check (snd cg') ah o ah' ->
    AccessFun ah'.
  Proof.
    intros.
    destruct o; simpl in *; CG.simpl_red; simpl_drf_check; eauto.
  Qed.

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

  Let node_def_cg_reduces:
    forall cg ah a o cg' ah',
    NodeDef (fst cg) ah ->
    TReduces cg (a,o) cg' ->
    DRF_Check (snd cg') ah o ah' ->
    NodeDef (fst cg') ah'.
  Proof.
    intros.
    destruct o; simpl in *; CG.simpl_red; simpl_drf_check; simpl in *; eauto.
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
      apply last_write_def; eauto using write_eq, in_eq.
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
    forall vs es ah (d:Trace.datum) h r n,
    LastWriteDef (HB es) ah ->
    MM.MapsTo r h ah ->
    WriteSafe (HB (C (n, fresh (A:=tid) vs) :: es)) (fresh vs, Some d) h ->
    LastWriteDef (HB (C (n, fresh vs) :: es))
      (MM.add r ((fresh vs, Some d) :: h) ah).
  Proof.
    unfold LastWriteDef; intros.
    rewrite MM_Facts.add_mapsto_iff in *.
    destruct H2 as [(?,?)|(?,mt)]. {
      subst.
      eauto using last_write_cons_write, hb_trans.
    }
    apply H in mt.
    destruct mt.
    eauto using last_write_cons.
  Qed.

  Let last_write_def_check:
    forall ah ah' a o cg cg',
    LastWriteDef (HB (snd cg)) ah ->
    TReduces cg (a,o) cg' ->
    DRF_Check (snd cg') ah o ah' ->
    LastWriteDef (HB (snd cg')) ah'.
  Proof.
    intros.
    destruct o; simpl in *; CG.simpl_red; simpl_drf_check; simpl in *; eauto.
  Qed.

  Structure WellFormed cg ah := {
    wf_lt_edges_prop: LtEdges (map e_edge (snd cg));
    wf_edge_to_node_prop: EdgeToNode cg;
    wf_node_def_prop: NodeDef (fst cg) ah;
    wf_access_fun_prop: AccessFun ah;
    wf_last_write_fun_prop: LastWriteFun (HB (snd cg)) ah;
    wf_ordered_access_history_prop: OrderedAccessHistory (HB (snd cg)) ah;
    wf_last_write_def_prop: LastWriteDef (HB (snd cg)) ah
  }.

  Lemma wf_reduces:
    forall cg ah ah' a o cg',
    WellFormed cg ah ->
    TReduces cg (a,o) cg' ->
    DRF_Check (snd cg') ah o ah' ->
    WellFormed cg' ah'.
  Proof.
    intros.
    apply Build_WellFormed;
    eauto using wf_lt_edges_prop, wf_node_def_prop, wf_access_fun_prop, wf_last_write_fun_prop,
          lt_edges_reduces, wf_ordered_access_history_prop, wf_last_write_def_prop,
          wf_edge_to_node_prop, reduces_edge_to_node.
    apply access_to_last_write_fun; eauto using wf_node_def_prop, wf_access_fun_prop,
    hb_trans, hb_irrefl, lt_edges_reduces, wf_lt_edges_prop.
  Qed.

  Lemma wf_race_free_access:
    forall a b r h cg ah,
    WellFormed cg ah ->
    MM.MapsTo r h ah ->
    List.In a h ->
    List.In b h ->
    RaceFreeAccess (HB (snd cg)) a b.
  Proof.
    intros.
    assert (RaceFreeHistory (HB (snd cg)) ah) by 
    eauto using ordered_access_history_to_race_free_history, wf_ordered_access_history_prop, hb_trans.
    eauto.
  Qed.

  Lemma wf_last_write_fun:
    forall cg ah h r a b,
    WellFormed cg ah ->
    MM.MapsTo r h ah ->
    LastWrite (HB (snd cg)) a h ->
    LastWrite (HB (snd cg)) b h ->
    a = b.
  Proof.
    intros.
    assert (Hx := wf_last_write_fun_prop H).
    eauto.
  Qed.

  Lemma wf_node:
    forall vs es ah h r a,
    WellFormed (vs,es) ah ->
    MM.MapsTo r h ah ->
    List.In a h ->
    Node (a_when a) vs.
  Proof.
    intros.
    assert (NodeDef (fst (vs,es)) ah) by eauto using wf_node_def_prop.
    eauto.
  Qed.

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

  Let wf_hb_inv_cons_c:
    forall vs es g r h a b t n,
    WellFormed (vs, es) g ->
    MM.MapsTo r h g ->
    Node n vs ->
    List.In a h ->
    List.In b h ->
    HB ({| e_t := t; e_edge := (n, fresh vs) |} :: es) (a_when a) (a_when b) ->
    HB es (a_when a) (a_when b).
  Proof.
    intros.
    eapply wf_node in H2; eauto.
    eapply wf_node in H3; eauto.
    inversion H1.
    apply hb_inv_cons_c with (x:=x) in H4; eauto.
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
       + apply wf_ordered_access_history_prop in H0.
         auto.
     - unfold LastWriteDef.
       intros.
       assert (Hx := H0).
       apply wf_last_write_def_prop in Hx.
       apply Hx in H1.
       destruct H1 as (a, Hw).
       exists a.
       eauto using last_write_impl, hb_impl_cons.
  Qed.

  Let hb_inv_cons_c_0:
    forall vs es x n ah a b t,
    WellFormed (x :: vs,{| e_t := t; e_edge := (n,fresh vs) |} :: es) ah ->
    HB ({| e_t := t; e_edge := (n,fresh vs) |} :: es) (a_when (A:=Trace.datum) a) (a_when (A:=Trace.datum) b) ->
    HB es (a_when a) (a_when b) \/ a_when b = fresh vs.
  Proof.
    intros.
    apply hb_inv_cons_c with (x:=x) in H0; auto.
    - apply wf_edge_to_node_prop in H ; auto.
    - apply wf_lt_edges_prop in H; auto.
  Qed.

  Lemma last_write_inv_c:
    forall x n vs ah ah' h es a r t,
    WellFormed (vs,es) ah ->
    WellFormed (x :: vs,{| e_t := t; e_edge := (n,fresh vs) |} :: es) ah' ->
    MM.MapsTo r h ah ->
    LastWrite (A:=Trace.datum) (HB ({| e_t := t; e_edge := (n,fresh vs) |} :: es)) a h ->
    LastWrite (HB es) a h.
  Proof.
    intros.
    destruct H2 as (X,Y,Hfw).
    apply last_write_def; eauto.
    unfold ForallWrites in *; intros b Hin Hwb.
    apply Hfw in Hin; auto.
    destruct Hin as [Hin|?]; auto.
    apply hb_inv_cons_c_0 with (ah:=ah') (x:=x) in Hin; repeat auto.
    destruct Hin as [?|R]; auto.
    subst.
    assert (Hn: Node (a_when a) vs) by eauto using wf_node.
    rewrite R in *.
    simpl_node.
  Qed.

  Lemma last_write_inv_j:
    forall x n vs ah ah' h es a r t e,
    WellFormed (vs,es) ah ->
    WellFormed (x :: vs,{| e_t := t; e_edge := (n,fresh vs) |} :: e :: es) ah' ->
    MM.MapsTo r h ah ->
    LastWrite (A:=Trace.datum) (HB ({| e_t := t; e_edge := (n,fresh vs) |} :: e :: es)) a h ->
    LastWrite (HB (e::es)) a h.
  Proof.
    intros.
    destruct H2 as (X,Y,Hfw).
    apply last_write_def; eauto.
    unfold ForallWrites in *; intros b Hin Hwb.
    apply Hfw in Hin; auto.
    destruct Hin as [Hin|?]; auto.
    apply hb_inv_cons_c with (x:=x) in Hin.
    - destruct Hin as [?|R]; auto.
      subst.
      assert (Hn: Node (a_when a) vs) by eauto using wf_node.
      rewrite R in *.
      simpl_node.
    - eauto using wf_edge_to_node_prop.
    - apply wf_lt_edges_prop in H0.
      auto.
  Qed.
(*
  Lemma last_write_impl_nodes:
    forall vs vs' es a h,
    LastWrite (A:=Trace.datum) (HB es) a h ->
    LastWrite (HB (vs', es)) a h.
  Proof.
    eauto using hb_impl_nodes, last_write_impl.
  Qed.
*)
  Lemma drf_check_inv_read_last_write:
    forall x n vs ah ah' d es r,
    WellFormed (vs,es) ah ->
    WellFormed (x :: vs,C (n, fresh vs) :: es) ah' ->
    DRF_Check (C (n, fresh vs) :: es) ah (Trace.READ r d) ah' ->
    exists h a,
    MM.MapsTo r h ah /\ LastWrite (HB es) a h /\ a_what a = Some d
    /\ HB (C (n, fresh vs) :: es) (a_when a) (fresh vs).
  Proof.
    intros.
    rename H into Hwf.
    rename H0 into Hwf'.
    simpl_drf_check.
    assert (Hlw := H5).
    exists l; exists a.
    split; auto.
    split; eauto using last_write_inv_c, wf_node, last_write_to_in.
  Qed.

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
    inversion H3; subst; clear H3.
    destruct b; simpl in *.
    subst.
    assert (a_when (n, Some x) = a_when a). {
      eapply last_write_inv_cons_write; eauto using hb_irrefl, wf_lt_edges_prop.
      eauto using hb_trans.
    }
    apply wf_access_fun with (ah:=ah') (cg:=cg') (r:=r) (h:=(n,Some x)::h) in H3; auto using in_eq.
    eapply last_write_to_in; eauto. 
  Qed.

End Props.
End T.