Require Import Coq.Setoids.Setoid.
Require Import Coq.Relations.Relation_Operators.

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

Require Import HJ.Mid.
Require Import HJ.Tid.
Require Import HJ.Dep.

  (** Points-to dependency: a variable points to another variable in the store. *)




Section Memory.

  Structure Memory := {
    (**
      A dependency that goes from a task to a memory location through the
      local memory of the task.
    *)
 
   LocalRef: tid -> dep -> Prop;
 
   (** Memory reference points to another reference *)

   GlobalRef: mid -> dep -> Prop
  }.


  Inductive task_op :=
  | BLOCKED: tid -> task_op
  | READ: mid -> task_op
  | WRITE: mid -> task_op.

  Definition as_dep (o:task_op) :=
  match o with
  | BLOCKED x => d_tid x
  | READ x => d_mid x
  | WRITE x => d_mid x
  end.

  Variable M:Memory.

  Inductive Dep : dep -> dep -> Prop :=
    | dep_global_ref:
      forall x y,
      GlobalRef M x y ->
      Dep (d_mid x) y
    | dep_local_ref:
      forall x y,
      LocalRef M x y ->
      Dep (d_tid x) y.

  Definition Depends := clos_trans _ Dep.

  (** A state is tainted if there is a cycle in the [Depends] relation.  *) 

  Inductive Tainted : Prop :=
    tainted_def:
      forall x,
      Depends (d_tid x) (d_tid x) ->
      Tainted.

  Let tainted_alt:
    Tainted <-> exists x, Depends (d_tid x) (d_tid x).
  Proof.
    split; intros.
    - inversion H; eauto.
    - destruct H; eauto using tainted_def.
  Qed.

  Inductive Untainted : Prop :=
    untainted_def:
      (forall x, ~ Depends (d_tid x) (d_tid x)) ->
      Untainted.

  Let untainted_alt:
    Untainted <-> (forall x, ~ (Depends (d_tid x) (d_tid x))).
  Proof.
    split; intros.
    - inversion H; eauto.
    - eauto using untainted_def.
  Qed.

  Let D x := Depends (d_tid x) (d_tid x).

  Lemma not_tainted_iff:
    ~ Tainted <-> Untainted.
  Proof.
    apply not_exists_iff_alt with (P:=D);
    auto using untainted_alt, tainted_alt.
  Qed.

  Lemma not_untainted_iff:
     { Tainted } + { ~ Tainted } ->
     (~ Untainted <-> Tainted).
  Proof.
    apply not_nforall_iff_alt with (P:=D);
    auto using tainted_alt, untainted_alt.
  Qed.

  Lemma tainted_untainted_dec:
     { Tainted } + { ~ Tainted } ->
     { Tainted } + { Untainted }.
  Proof.
    apply exists_nforall_dec_alt with (P:=D);
    auto using tainted_alt, untainted_alt.
  Qed.

  Lemma untainted_back_edges:
    (forall x y, { Depends x y } + { ~ Depends x y}) ->
    forall x y,
    Untainted ->
    Dep (d_tid x) y ->
    ~ Depends y (d_tid x).
  Proof.
    intros.
    destruct (H y (d_tid x)).
    - assert (Hx: ~ Depends (d_tid x) (d_tid x)) by (inversion H0; eauto).
      unfold Depends in *.
      contradiction Hx.
      eauto using t_trans, t_step.
    - assumption.
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
End Memory.


(** Memory defined as a finite data structure *)

Module MemoryState.

Section DefsFin.

  Notation local_refs := (MT.t set_dep).

  Notation global_refs := (MM.t dep).

  Inductive LocalRef (ms:local_refs) t (d:dep) : Prop :=
  | local_ref_def:
    forall s,
    MT.MapsTo t s ms ->
    SD.In d s ->
    LocalRef ms t d.

  Inductive GlobalRef (ms:global_refs) t d : Prop :=
  | global_ref_def:
    MM.MapsTo t d ms ->
    GlobalRef ms t d.

  Structure memory := {
    local_memory: local_refs;
    global_memory: global_refs
  }.

  Let update_local_memory f m :=
    Build_memory (f (local_memory m)) (global_memory m).

  Let update_global_memory f m :=
    Build_memory (local_memory m) (f (global_memory m)).

  Definition update_local_ref t f :=
    update_local_memory (fun lm => 
      match MT.find t lm with
      | Some s => MT.add t (f s) lm
      | _ => lm
      end
    ).

  Definition add_local_ref t d :=
    update_local_ref t (SD.add d).

  Definition remove_local_ref t d :=
    update_local_ref t (SD.remove d).

  Definition put_global_ref m d :=
    update_global_memory (fun gm => MM.add m d gm).

  Definition remove_global_ref m :=
    update_global_memory (fun gm => MM.remove m gm).

  Definition M ms :=
    Build_Memory
    (LocalRef (local_memory ms))
    (GlobalRef (global_memory ms)).

  Lemma local_ref_inv_add:
    forall x y t d s ms,
    LocalRef (MT.add t (SD.add d s) ms) x y ->
    (t = x /\ y = d) \/ (t = x /\ SD.In y s) \/ (t <> x /\ LocalRef ms x y).
  Proof.
    intros.
    inversion H.
    apply MT_Facts.add_mapsto_iff in H0.
    destruct H0 as [(?,?)|(?,?)].
    - subst.
      apply SD_Facts.add_iff in H1.
      destruct H1.
      + apply dep_eq_rw in H0.
        intuition.
      + intuition.
    - right.
      right.
      split; eauto using local_ref_def.
  Qed.

  Lemma dep_inv_add_local_ref:
    forall t d ms x y,
    Dep (M (add_local_ref t d ms)) x y ->
    (x = d_tid t /\ d = y) \/
    Dep (M ms) x y.
  Proof.
    intros.
    inversion H; subst; simpl in *.
    - right; auto using dep_global_ref.
    - destruct (MT_Extra.find_rw t (local_memory ms)) as [(Hf,?)|(s,(Hf,?))].
      + rewrite Hf in *; clear Hf.
        right; auto using dep_local_ref.
      + rewrite Hf in *; clear Hf.
        apply local_ref_inv_add in H0.
        destruct H0 as [(?,?)|[(?,?)|(?,?)]]; subst.
        * intuition.
        * right.
          apply dep_local_ref.
          simpl.
          eauto using local_ref_def.
        * right.
          apply dep_local_ref.
          simpl.
          eauto using local_ref_def.
  Qed.

  Lemma global_ref_inv_add:
    forall m d ms x y,
    GlobalRef (MM.add m d ms) x y ->
    ( m = x /\ d = y) \/ (m <> x /\ GlobalRef ms x y).
  Proof.
    intros.
    inversion H.
    apply MM_Facts.add_mapsto_iff in H0.
    destruct H0 as [(?,X)|(?,?)].
    - subst.
      intuition.
    - right.
      split; auto using global_ref_def.
  Qed.

  Lemma dep_inv_put_global_ref:
    forall m d ms x y,
    Dep (M (put_global_ref m d ms)) x y ->
    (x = d_mid m /\ d = y) \/
    Dep (M ms) x y.
  Proof.
    intros.
    inversion H; subst; simpl in *; auto.
    - apply global_ref_inv_add in H0.
      destruct H0 as [(?,?)|(?,?)].
      + subst.
        intuition.
      + right.
        auto using dep_global_ref.
    - right.
      auto using dep_local_ref.
  Qed.

  
End DefsFin.

End MemoryState.


Section Tasks.
(*
  Structure TaskState := {
   TaskMemory : Memory;
   Task: tid -> task_op -> Prop;
   task_spec: forall x y, Task x y -> LocalRef TaskMemory x (as_dep y)
  }.

  Variable T: TaskState.
*)
  Variable Task: tid -> task_op -> Prop.

  Inductive Race x : Prop :=
  | race_def:
    forall t t',
    Task t (READ x) ->
    Task t' (WRITE x) ->
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


  Definition Blocked x y := Task x (BLOCKED y).

  Definition Trans_Blocked := clos_trans _ Blocked.

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



  (* XXX: move to Aniceto *)
  Require Import Coq.Relations.Relation_Definitions.
  Require Import Aniceto.Graphs.Graph.

  (** A deadlocked state is a special case of a tainted state. *)

  Variable M : Memory.

  Variable task_spec:
    forall x y,
       Task x y -> LocalRef M x (as_dep y).

  Let trans_blocked_to_depends:
    forall x,
    Trans_Blocked x x ->
    Depends M (d_tid x) (d_tid x).
  Proof.
    unfold Trans_Blocked, reflexive, Depends in *.
    intros.
    apply clos_trans_impl_ex with (P:=Blocked); auto.
    intros.
    apply task_spec in H0.
    apply dep_local_ref.
    simpl in *.
    auto.
  Qed.

  Lemma deadlocked_to_tainted:
    Deadlocked ->
    Tainted M.
  Proof.
    intros.
    inversion H.
    eauto using tainted_def, trans_blocked_to_depends.
  Qed.

  Lemma untainted_to_deadlockfree:
    Untainted M ->
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

End Tasks.

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

  Lemma untainted_impl:
    forall D E,
    (forall x y, Dep E x y -> Dep D x y) ->
    Untainted D -> Untainted E.
  Proof.
    intros ? ? Hi Hd.
    inversion Hd.
    apply untainted_def.
    intros.
    unfold not; intros.
    unfold Depends in *.
    assert (Hx := H x).
    contradiction Hx.
    eauto using clos_trans_impl.
  Qed.

End Props.

(*
  

  (** A finite representation of memory state and task state *)

  Inductive task_state :=
  | BLOCKED: tid -> task_state
  | READ: mid -> task_state
  | WRITE: mid -> task_state.

  Inductive Read ts t m  :  Prop :=
  | read_def:
    MT.MapsTo t (READ m) ts ->
    Read ts t m.

  Inductive Write ts t m : Prop :=
  | write_def:
    MT.MapsTo t (WRITE m) ts ->
    Write ts t m.

  Inductive Blocked ts t t' : Prop :=
  | blocked_def:
    MT.MapsTo t (BLOCKED t') ts ->
    Blocked ts t t'.

  Notation local_memory := (MT.t set_dep).

  Notation global_memory := (MM.t dep).

  Structure dependency_state := {
    ds_local_memory: local_memory;
    ds_global_memory: global_memory;
    ds_task_state: MT.t task_state;
    ds_read_spec:
      forall x y,
      MT.MapsTo x (READ y) ds_task_state ->
      LocalRef ds_local_memory x (d_mid y);
    ds_write_spec:
      forall x y,
      MT.MapsTo x (WRITE y) ds_task_state ->
      LocalRef ds_local_memory x (d_mid y);
    ds_blocked_spec:
      forall x y,
      MT.MapsTo x (BLOCKED y) ds_task_state ->
      LocalRef ds_local_memory x (d_tid y)
  }.

  Lemma read_spec ds:
    forall x y,
    Read (ds_task_state ds) x y ->
    LocalRef (ds_local_memory ds) x (d_mid y).
  Proof.
    intros.
    inversion H.
    auto using ds_read_spec.
  Qed.

  Lemma write_spec ds:
    forall x y,
    Write (ds_task_state ds) x y ->
    LocalRef (ds_local_memory ds) x (d_mid y).
  Proof.
    intros.
    inversion H.
    auto using ds_write_spec.
  Qed.

  Lemma blocked_spec ds:
    forall x y,
    Blocked (ds_task_state ds) x y ->
    LocalRef (ds_local_memory ds) x (d_tid y).
  Proof.
    intros.
    inversion H.
    auto using ds_blocked_spec.
  Qed.

  Definition as_dependency_spec (ds:dependency_state) : DependenciesSpec :=
    Build_DependenciesSpec
      (Read (ds_task_state ds))
      (Write (ds_task_state ds))
      (Blocked (ds_task_state ds))
      (LocalRef (ds_local_memory ds))
      (GlobalRef (ds_global_memory ds))
      (read_spec ds)
      (write_spec ds)
      (blocked_spec ds).

  Let update_tasks (f:fun ts => (ds:dependency_state) : dependency_state.
    
    @Build_dependency_state
      (ds_local_memory ds)
      (ds_global_memory ds)
      (f (ds_task_state ds))
      (ds_read_spec ds)
      (ds_write_spec ds)
      (ds_blocked_spec ds).

  Definition put_read (t:tid) (m:mid) : dependency_state ->  dependency_state :=
    update_tasks (fun ts => MT.add t (READ m) ts).

  Definition put_write t m :=
    update_tasks (fun ts => MT.add t (WRITE m) ts).

  Definition put_blocked t t' :=
    update_tasks (fun ts => MT.add t (BLOCKED t') ts).

  Definition remove_task t :=
    update_tasks (fun ts => MT.remove t ts).

  Let update_local_memory f ds :=
    Build_dependency_state (f (ds_local_memory ds)) (ds_global_memory ds) (ds_task_state ds).

  Let update_global_memory f ds :=
    Build_dependency_state (ds_local_memory ds) (f (ds_global_memory ds)) (ds_task_state ds).

  Definition update_local_ref t f :=
    update_local_memory (fun lm => 
      match MT.find t lm with
      | Some s => MT.add t (f s) lm
      | _ => lm
      end
    ).

  Definition add_local_ref t d :=
    update_local_ref t (SD.add d).

  Definition remove_local_ref t d :=
    update_local_ref t (SD.remove d).

  Definition put_global_ref t d :=
    update_global_memory (fun gm => MM.add t d gm).

  Definition remove_global_ref t :=
    update_global_memory (fun gm => MM.remove t gm).

  Let D := as_dependency_spec.

  Let read_inv_add:
    forall x y ts e t,
    Read (MT.add t e ts) x y ->
    (t = x /\ e = READ y) \/ (t <> x /\Read ts x y).
  Proof.
    intros.
    inversion H.
    apply MT_Facts.add_mapsto_iff in H0.
    destruct H0 as [(?,X)|(?,?)].
    - subst.
      intuition.
    - right; auto using read_def.
  Qed.

  Let write_inv_add:
    forall x y ts e t,
    Write (MT.add t e ts) x y ->
    (t = x /\ e = WRITE y) \/ (t <> x /\ Write ts x y).
  Proof.
    intros.
    inversion H.
    apply MT_Facts.add_mapsto_iff in H0.
    destruct H0 as [(?,X)|(?,?)].
    - subst.
      intuition.
    - right; auto using write_def.
  Qed.

  Let blocked_inv_add:
    forall x y ts e t,
    Blocked (MT.add t e ts) x y ->
    (t = x /\ e = BLOCKED y) \/ (t <> x /\Blocked ts x y).
  Proof.
    intros.
    inversion H.
    apply MT_Facts.add_mapsto_iff in H0.
    destruct H0 as [(?,X)|(?,?)].
    - subst.
      intuition.
    - right; auto using blocked_def.
  Qed.

  Let dep_inv_add_tasks:
    forall x y ds e t,
    Dep (D (update_tasks (fun ts => MT.add t e ts) ds)) x y ->
    Dep (D ds) x y \/
    (d_tid t = x /\ exists t', e = BLOCKED t' /\ d_tid t' = y).
  Proof.
    intros.
    inversion H; subst; simpl in *.
    - apply blocked_inv_add in H0.
      destruct H0 as [(?,?)|(?,?)].
      + subst.
        right.
        eauto.
      + left.
        auto using dep_blocked.
    - left; auto using dep_global_ref.
    - left; auto using dep_local_ref.
  Qed.

  Lemma dep_inv_put_read:
    forall s t m x y,
    Dep (D (put_read t m s)) x y ->
    Dep (D s) x y.
  Proof.
    intros.
    unfold put_read in *.
    apply dep_inv_add_tasks in H.
    destruct H as [?|(?,(?,(Hx,?)))]; auto.
    inversion Hx.
  Qed.

  Lemma dep_inv_put_write:
    forall s t m x y,
    Dep (D (put_write t m s)) x y ->
    Dep (D s) x y.
  Proof.
    intros.
    unfold put_write in *.
    apply dep_inv_add_tasks in H.
    destruct H as [?|(?,(?,(Hx,?)))]; auto.
    inversion Hx.
  Qed.

  Lemma dep_inv_put_blocked:
    forall s t t' x y,
    Dep (D (put_blocked t t' s)) x y ->
    Dep (D s) x y \/ (x = d_tid t /\ y = d_tid t').
  Proof.
    intros.
    unfold put_blocked in *.
    apply dep_inv_add_tasks in H.
    destruct H as [?|(?,(?,(Hx,?)))]; auto.
    inversion Hx.
    subst.
    intuition.
  Qed.
*)

