Require Import HJ.Preamble.

Set Implicit Arguments.

Section DoDec.
  Variable A: Type.
  Variable P: A -> Prop.
  Notation Exists:= (exists x, P x).
  Notation NForall:= (forall x, ~ P x).

  Lemma not_exists_iff:
    ~ Exists <-> NForall.
  Proof.
    intuition.
    - assert (exists x, P x) by eauto.
      contradiction.
    - destruct H0 as (x, H0).
      eauto.
  Qed.

  Lemma exists_to_not_nforall:
    Exists -> ~ NForall.
  Proof.
    intros.
    intuition.
    destruct H as (x, H).
    assert (~ P x) by eauto.
    contradiction.
  Qed.

  (** In general, it is not possible to conclude the inverse,
      but if [Exists] is decidable, then we can. *)

  Lemma not_nforall_to_exists:
     { Exists } + { ~ Exists } ->
     ~ NForall -> Exists.
  Proof.
    intros.
    destruct H.
    - assumption.
    - rewrite not_exists_iff in *.
      contradiction.
  Qed.

  Lemma not_forall_iff:
     { Exists } + { ~ Exists } ->
     (~ NForall <-> Exists).
  Proof.
    intros.
    split;
    eauto using exists_to_not_nforall, not_nforall_to_exists.
  Qed.

  Lemma exists_nforall_dec:
    { Exists } + { ~ Exists } ->
    { Exists } + { NForall }.
  Proof.
    intros.
    inversion H.
    - left; auto.
    - rewrite not_exists_iff in *.
      eauto.
  Qed.
End DoDec.

Section DoDec2.
  Variable A: Type.
  Variable P: A -> Prop.
  Variable E: Prop.
  Variable N: Prop.

  Variable exists_alt:
    E <-> exists x, P x.

  Variable nforall_alt:
    N <-> (forall x, ~ P x).

  Lemma not_exists_iff_alt:
    ~ E <-> N.
  Proof.
    split;
    try rewrite exists_alt in *;
    try rewrite nforall_alt in *;
    try rewrite not_exists_iff in *;
    trivial.
  Qed.

  Lemma exists_to_not_nforall_alt:
    E -> ~ N.
  Proof.
    try rewrite nforall_alt in *;
    try rewrite exists_alt in *;
    eauto using exists_to_not_nforall.
  Qed.

  Let e_to_p:
    { E } + { ~ E } ->
    { exists x, P x } + { ~ exists x, P x }.
  Proof.
    intros.
    destruct H; 
    try rewrite exists_free_alt in *; intuition.
  Qed.

  Lemma not_nforall_to_exists_alt:
     { E } + { ~ E } ->
     ~ N -> E.
  Proof.
    intros.
    apply e_to_p in H.
    try rewrite exists_alt in *.
    apply not_nforall_to_exists; auto.
    intuition.
  Qed.

  Lemma not_nforall_iff_alt:
     { E } + { ~ E } ->
     (~ N <-> E).
  Proof.
    intros.
    split;
    auto using exists_to_not_nforall_alt, not_nforall_to_exists_alt.
  Qed.

  Let n_dec_to_e_n:
    { exists x, P x } + { forall x, ~ P x } ->
    {E} + {N}.
  Proof.
    intros.
    destruct H.
    - left; rewrite exists_alt; trivial.
    - right; rewrite nforall_alt; trivial.
  Qed.

  Lemma exists_nforall_dec_alt:
     { E } + { ~ E } ->
     { E } + { N }.
  Proof.
    intros.
    apply e_to_p in H.
    apply n_dec_to_e_n.
    eauto using exists_nforall_dec.
  Qed.

End DoDec2.

  (** * Races %\&% Dependencies *)

  Inductive tid :=
  | taskid: name -> tid.

  Definition from_tid t := match t with taskid x => x end.

  Inductive mid :=
  | memid: name -> mid.

  Definition from_mid t := match t with memid x => x end.

  (** Points-to dependency: a variable points to another variable in the store. *)

  (** Defines a dependency node, that can be either a task name or a memory location. *)

  Notation dep := (mid + tid)%type.

  Notation in_mid := (@inl mid tid).

  Notation in_tid := (@inr mid tid).

  Definition d_mid x := (in_mid (memid x)).

  Definition d_tid x := (in_tid (taskid x)).

  Definition from_dep d := match d with | inl l => from_mid l | inr t => from_tid t end.

Structure DependenciesSpec := {
  (** Holds when some task is reading from a heap reference. *) 

  Read: tid -> mid -> Prop;

  (** Holds when some task is writing to a heap reference. *)

  Write: tid -> mid -> Prop;

  (** Memory reference points to another reference *)

  PointsTo: mid -> dep -> Prop;

  (**
    A dependency that goes from a task to a memory location through the
    local memory of the task. *)

  LocalRef: tid -> mid -> Prop;


  (** Blocked dependency: a task is blocked on a future in the taskmap. *)

  Blocked: tid -> tid -> Prop
}.

Section Defs.
  Variable D:DependenciesSpec.

  Inductive Race x : Prop :=
  | race_def:
    forall t t',
    Read D t x ->
    Write D t' x ->
    Race x.

  Inductive Racy : Prop :=
  | racy_def:
    forall x,
    Race x ->
    Racy.

  Let racy_alt:
    Racy <-> exists x, Race x.
  Proof.
    split; intros.
    - inversion H; eauto.
    - destruct H; eauto using racy_def.
  Qed.

  Inductive RaceFree : Prop :=
  | race_free_def:
    (forall x, ~ Race x) ->
    RaceFree.

  Let race_free_alt:
    RaceFree <->
    (forall x, ~ Race x).
  Proof.
    split; intros.
    - inversion H; eauto.
    - auto using race_free_def.
  Qed.

  Lemma not_racy_iff:
    ~ Racy <-> RaceFree.
  Proof.
    apply not_exists_iff_alt with (P:=Race);
    auto using race_free_alt, racy_alt.
  Qed.

  Lemma not_race_free_iff:
     { Racy } + { ~ Racy } ->
     (~ RaceFree <-> Racy).
  Proof.
    apply not_nforall_iff_alt with (P:=Race);
    auto using race_free_alt, racy_alt.
  Qed.

  Lemma racy_race_free_dec:
     { Racy } + { ~ Racy } ->
     { Racy } + { RaceFree }.
  Proof.
    apply exists_nforall_dec_alt with (P:=Race);
    auto using race_free_alt, racy_alt.
  Qed.

  (** Dependencies between two names in a state wraps up blocked and points-to
     dependencies. *)

  Inductive Dep : dep -> dep -> Prop :=
    | dep_points_to:
      forall x y,
      PointsTo D x y ->
      Dep (inl x) y
    | dep_blocked:
      forall x y,
      Blocked D x y ->
      Dep (inr x) (inr y)
    | dep_read:
      forall x y,
      Read D x y ->
      Dep (inr x) (inl y)
    | dep_reg:
      forall x y,
      LocalRef D x y ->
      Dep (inr x) (inl y).

  (* begin hide *)
  Require Import Coq.Relations.Relation_Operators.
  (* end hide *)

  Definition Trans_Blocked := clos_trans _ (Blocked D).

  (** A deadlocked state has a cycle in the [Trans_Blocked] relation. *)

  Inductive Deadlocked : Prop :=
    deadlocked_def:
      forall x,
      Trans_Blocked x x ->
      Deadlocked.

  Let deadlocked_alt:
    Deadlocked <-> exists x, Trans_Blocked x x.
  Proof.
    split; intros.
    - inversion H; eauto.
    - destruct H; eauto using deadlocked_def.
  Qed.

  Inductive DeadlockFree : Prop :=
    deadlock_free_def:
      (forall x, ~ Trans_Blocked x x) ->
      DeadlockFree.

  Let deadlock_free_alt:
    DeadlockFree <-> (forall x, ~ Trans_Blocked x x).
  Proof.
    split; intros.
    - inversion H; eauto.
    - eauto using deadlock_free_def.
  Qed.

  Lemma not_deadlocked_iff:
    ~ Deadlocked <-> DeadlockFree.
  Proof.
    apply not_exists_iff_alt with (P:=fun x => Trans_Blocked x x);
    auto using deadlock_free_alt, deadlocked_alt.
  Qed.

  Lemma not_deadlockfree_iff:
     { Deadlocked } + { ~ Deadlocked } ->
     (~ DeadlockFree <-> Deadlocked).
  Proof.
    apply not_nforall_iff_alt with (P:=fun x => Trans_Blocked x x);
    auto using deadlock_free_alt, deadlocked_alt.
  Qed.

  Lemma deadlocked_deadlockfree_dec:
     { Deadlocked } + { ~ Deadlocked } ->
     { Deadlocked } + { DeadlockFree }.
  Proof.
    apply exists_nforall_dec_alt with (P:=fun x => Trans_Blocked x x);
    auto using deadlock_free_alt, deadlocked_alt.
  Qed.

  (** Defines the [Depends] relation as the transitive closure of [Dep]. *)

  Definition Depends := clos_trans _ Dep.

  (** A state is tainted if there is a cycle in the [Depends] relation.  *) 

  Inductive Tainted : Prop :=
    tainted_def:
      forall x,
      Depends (in_tid x) (in_tid x) ->
      Tainted.

  Let tainted_alt:
    Tainted <-> exists x, Depends (in_tid x) (in_tid x).
  Proof.
    split; intros.
    - inversion H; eauto.
    - destruct H; eauto using tainted_def.
  Qed.

  Inductive Untainted : Prop :=
    untainted_def:
      (forall x, ~ Depends (in_tid x) (in_tid x)) ->
      Untainted.

  Let untainted_alt:
    Untainted <-> (forall x, ~ (Depends (in_tid x) (in_tid x))).
  Proof.
    split; intros.
    - inversion H; eauto.
    - eauto using untainted_def.
  Qed.

  Let T x := Depends (in_tid x) (in_tid x).

  Lemma not_tainted_iff:
    ~ Tainted <-> Untainted.
  Proof.
    apply not_exists_iff_alt with (P:=T);
    auto using untainted_alt, tainted_alt.
  Qed.

  Lemma not_untainted_iff:
     { Tainted } + { ~ Tainted } ->
     (~ Untainted <-> Tainted).
  Proof.
    apply not_nforall_iff_alt with (P:=T);
    auto using tainted_alt, untainted_alt.
  Qed.

  Lemma tainted_untainted_dec:
     { Tainted } + { ~ Tainted } ->
     { Tainted } + { Untainted }.
  Proof.
    apply exists_nforall_dec_alt with (P:=T);
    auto using tainted_alt, untainted_alt.
  Qed.

  Import Operators_Properties.

  Lemma dep_to_depends:
    forall x y,
    Dep x y ->
    Depends x y.
  Proof.
    intros.
    unfold Depends.
    eauto using t_step.
  Qed.

  (* XXX: move to Aniceto *)
  Require Import Coq.Relations.Relation_Definitions.
  Require Import Aniceto.Graphs.Graph.

  (** A deadlocked state is a special case of a tainted state. *)

  Let trans_blocked_to_depends:
    forall x,
    Trans_Blocked x x ->
    Depends (in_tid x) (in_tid x).
  Proof.
    unfold Trans_Blocked, reflexive, Depends in *.
    eauto using clos_trans_impl_ex, dep_blocked.
  Qed.

  Lemma deadlocked_to_tainted:
    Deadlocked ->
    Tainted.
  Proof.
    intros.
    inversion H.
    eauto using tainted_def, trans_blocked_to_depends.
  Qed.

  Lemma untainted_to_deadlockfree:
    Untainted ->
    DeadlockFree.
  Proof.
    intros.
    apply not_deadlocked_iff.
    intuition.
    apply deadlocked_to_tainted in H0.
    apply not_tainted_iff in H.
    contradiction.
  Qed.


(* begin hide *)

End Defs.

Section Props.
  Lemma deadlocked_impl_ex:
    forall D E,
    (forall x y z, Blocked D y z -> Blocked D x y -> Blocked E x y) ->
    Deadlocked D -> Deadlocked E.
  Proof.
    intros ? ? Hi Hd.
    inversion Hd.
    apply deadlocked_def with (x:=x).
    unfold Trans_Blocked in *.
    apply clos_trans_cycle_succ_impl with (P:=Blocked D); eauto.
  Qed.

  Lemma deadlocked_impl:
    forall D E,
    (forall x y, Blocked D x y -> Blocked E x y) ->
    Deadlocked D -> Deadlocked E.
  Proof.
    intros ? ? Hi Hd.
    inversion Hd.
    apply deadlocked_def with (x:=x).
    unfold Trans_Blocked in *.
    eauto using clos_trans_impl.
  Qed.

  Lemma deadlockfree_impl:
    forall D E,
    (forall x y, Blocked E x y -> Blocked D x y) ->
    DeadlockFree D -> DeadlockFree E.
  Proof.
    intros ? ? Hi Hd.
    inversion Hd.
    apply deadlock_free_def.
    intros.
    unfold not; intros.
    unfold Trans_Blocked in *.
    assert (Hx := H x).
    contradiction Hx.
    eauto using clos_trans_impl.
  Qed.

End Props.

Section DefsFin.
  (** Finite definitions of deadlocked and of *)
  Variable D:DependenciesSpec.

  Inductive DeadlockedOf m : Prop :=
    deadlock_of:
      (forall x y, MN.MapsTo x y m <-> Blocked D (taskid x) (taskid y)) ->
      DeadlockedOf m.

End DefsFin.
