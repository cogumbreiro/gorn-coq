(* begin hide *)

Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.FSets.FMapAVL.
Require Coq.FSets.FMapFacts.
Require Coq.FSets.FSetProperties.
Require Coq.FSets.FSetBridge.

Module NAME := Nat_as_OT.
Module NAME_Facts := OrderedTypeFacts NAME.
Module Set_NAME := FSetAVL.Make NAME.
Module Set_NAME_Props := FSetProperties.Properties Set_NAME.
(*Module Set_NAME_Extra := SetUtil Set_NAME.*)
Module Set_NAME_Dep := FSetBridge.DepOfNodep Set_NAME.
Module Map_NAME := FMapAVL.Make NAME.
Module Map_NAME_Facts := FMapFacts.Facts Map_NAME.
Module Map_NAME_Props := FMapFacts.Properties Map_NAME.
(*Module Map_ID_Extra := MapUtil Map_ID.*)

Definition name := NAME.t.
Definition set_name := Set_NAME.t.

Lemma name_eq_rw:
  forall k k' : name, k = k' <-> k = k'.
Proof.
  intros.
  auto with *.
Qed.

(* ----- end of boiler-plate code ---- *)

Set Implicit Arguments.

Module Lang.

(* end hide *)

(** * Language *)

  (**
    Our language is a simple Typed Assembly Language (TAL) with futures and shared memory.
  *)

Notation register := name.

  (** As for words we have numbers, and three kinds of handles: task identifiers,
    heap pointers, and function names. *)

  Inductive word :=
  | Num: nat -> word    (* number *)
  | TaskLabel : name -> word  (* task-id *)
  | HeapLabel : name -> word  (* heap-id *)
  | CodeLabel : name -> word. (* code-id *)

  (** A value, in TAL lingo, is either a register number or a word. It only has
    meaning in the context of a register-store. *)

  Inductive value :=
  | Reg: name -> value   (* register *)
  | Word: word -> value.

  Inductive inst :=

  (** TAL operations *)

  | MOV: register -> value -> inst          (* [r := v] *)
  | ADD: register -> register -> value -> inst            (* [r1 := r2 + v] *)
  | BNZ: register -> value -> inst (* [if r <> 0 jmp v] *)

  (**
    **Future operations.**
    Instruction [FUTURE] expects a target register and source value.
    The instruction creates a new task and assigns its task label to
    the target register.
    The new task runs the code in the source value, so it expects that
    there is a code label.
   *)

  | FUTURE: register -> value -> inst    (* [r := future v] *)


  (**
    Instruction [FORCE] expects a target register and a source value.
    The instruction blocks until the task (pointed by the source value) promises
    a value, that is copied to the target register.
   *)

  | FORCE: register -> value -> inst     (* [r := force v] *)

  (**
    [ALLOC] creates a memory cell and assigns
    the memory location to the register (in the operand).
   *)

  | ALLOC: register -> inst

  (** [LDR] the loaded data (in the left-hand side) is placed into the register. *)

  | LDR: register -> value -> inst          (* [r := &v] *)
  
  (** [STR] the data found in the left-hand side register is stored
    into memory. *)
  
  | STR: register -> value -> inst.          (* [ *r := v] *)

  Inductive code :=
  | SEQ : inst -> code -> code
  | BX: value -> code

  (**
     Tasks terminate their execution by fulfilling their promise of a future value.
     The promise is read by another tasks that executes [FORCE].
   *)

  | PROMISE : value -> code.

  (** A store maps from names/registers into values. *)

  Definition store := Map_NAME.t word.

  (** Let [mk_store] create an empty store. *)

  Definition mk_store := @Map_NAME.empty word.

  Definition heap := Map_NAME.t (option word).

  Definition mk_heap := @Map_NAME.empty (option word).

  (** A taskmap ranges from names into expressions. *)

  Inductive task := mk_task {get_registers: store; get_code: code}. 

  Definition set_registers (e:store) (t:task) := mk_task e (get_code t). 

  Definition put_register (r:name) (w:word) (t:task) :=
    set_registers (Map_NAME.add r w (get_registers t)) t.

  Definition set_code (c:code) (t:task) := mk_task (get_registers t) c. 

  Definition taskmap := Map_NAME.t task.

  (**
  Function [mk_taskmap] creates a taskmap with a singleton expression [e] labelled
  by name [h]. 
  *)

  Definition mk_taskmap := @Map_NAME.empty task.

  (** A state simply pairs a store and a taskmap. *)

  Structure state := mk_state {
    get_data: heap;
    get_tasks: taskmap
  }.

  (** The [load] function creates the initial state, running expression [e] with name [h]. *)

  Definition load (h:name) (e:code) := mk_state mk_heap (Map_NAME.add h (mk_task mk_store e) mk_taskmap).

  (** Functions [set_code] and  [set_data] work as expected. *)

  Definition set_tasks m (s:state) :=
    mk_state (get_data s) m.

  Definition put_task h t (s:state) :=
    set_tasks (Map_NAME.add h t (get_tasks s)) s.

  Definition set_data d (s:state) :=
    mk_state d (get_tasks s).

  Definition put_data h v (s:state) :=
    set_data (Map_NAME.add h v (get_data s)) s.

(* begin hide*)
End Lang.
(* end hide *)

(* begin hide  *)

Module Semantics.
  Import Lang.

(* end hide *)
  (** * Small-step operational semantics *)

  (** Converts a value to a word given a store. *)

  Inductive Load (t:task) : value -> word -> Prop :=
  | load_reg:
    forall r w,
    Map_NAME.MapsTo r w (get_registers t) ->
    Load t (Reg r) w
  | load_word:
    forall w,
    Load t (Word w) w.

  (**
    The code fragment is a parameter of the semantics that holds
    the code declarations.
   *)

  Variable code_fragment : Map_NAME.t code.

  (** For simplicity we abbreviate [Load] relative to a task's registers. *)

  (** We define a standard register-machine reduction *)

  Inductive IReduces (t:task) : task -> Prop :=
  | i_reduces_mov:
    forall dst v w c,
    get_code t = SEQ (MOV dst v) c ->
    (Load t) v w ->
    IReduces t (put_register dst w (set_code c t))
  | i_reduces_add:
    forall dst l r n1 n2 c,
    get_code t = SEQ (ADD dst l r) c ->
    Load t (Reg l) (Num n1) ->
    Load t r (Num n2) ->
    IReduces t (put_register dst (Num (n1 + n2)) (set_code c t))
  | i_reduces_bnz_skip:
    forall r v h c,
    get_code t = SEQ (BNZ r v) c ->
    Load t (Reg r) (CodeLabel h) ->
    Load t v (Num 0) ->
    IReduces t (set_code c t)
  | i_reduces_bnz_jmp:
    forall r v h c n c',
    get_code t = SEQ (BNZ r v) c ->
    Load t (Reg r) (CodeLabel h) ->
    Load t v (Num (S n)) ->
    Map_NAME.MapsTo h c' code_fragment ->
    IReduces t (set_code c' t)
  | i_reduces_jmp:
    forall c l v,
    get_code t = BX v ->
    Load t v (CodeLabel l) ->
    Map_NAME.MapsTo l c code_fragment ->
    IReduces t (set_code c t).

  (**
    The next reduction rules define register machine (a task)
    that has access to a main memory [s].
   *)

  Inductive TReduces (m:heap) (t:task) : heap -> task -> Prop :=
  | t_reduces_i:
    forall t',
    IReduces t t' ->
    TReduces m t m t'
  | t_reduces_alloc:
    forall c h r,
    get_code t = SEQ (ALLOC r) c ->
    ~ Map_NAME.In h m ->
    TReduces m t (Map_NAME.add h None m) (set_code c t)
  | t_reduces_store_reg:
    forall r v c h w,
    get_code t = SEQ (STR r v) c ->
    Load t (Reg r) w ->
    Load t v (HeapLabel h) ->
    Map_NAME.In h m ->
    TReduces m t (Map_NAME.add h (Some w) m) (set_code c t)
  | t_reduces_load_reg:
    forall w c h r v,
    get_code t = SEQ (LDR r v) c ->
    Load t v (HeapLabel h) ->
    Map_NAME.MapsTo h (Some w) m ->
    TReduces m t m (put_register r w (set_code c t)).

  (**
    We abbreviate when a task name maps to a task in a given state.
   *)

  Inductive GetTask (h:name) (t:task) (s:state) : Prop :=
  | get_task_def:
    Map_NAME.MapsTo h t (get_tasks s) ->
    GetTask h t s.

  (** Finally we define future manipulation *)

  Inductive Reduces (s:state) : state -> Prop :=
  | reduces_t:
    forall h t t' d',
    GetTask h t s ->
    TReduces (get_data s) t d' t' ->
    Reduces s (put_task h t' (set_data d' s))
  | reduces_future:
    forall dst c c' h h' t v l,
    GetTask h t s ->
    get_code t = SEQ (FUTURE dst v) c ->
    Load t v (CodeLabel l) ->
    Map_NAME.MapsTo l c' code_fragment ->
    ~ Map_NAME.In h' (get_tasks s) ->
    Reduces s
      (put_task h (put_register dst (TaskLabel h') (set_code c t))
        (put_task h' (set_code c' t) s))
  | reduces_get:
    forall r c h h' t t' v x y,
    GetTask h t s ->
    get_code t = SEQ (FORCE r x) c ->
    Load t x (TaskLabel h') ->
    GetTask h' t' s ->
    get_code t' = PROMISE y ->
    Load t' y v ->
    let new_t := put_register r v (set_code c t) in
    Reduces s (put_task h new_t s).

(* begin hide *)
End Semantics.

  Inductive tid :=
  | taskid: name -> tid.

  Definition from_tid t := match t with taskid x => x end.

  Inductive mid :=
  | memid: name -> mid.

  Definition from_mid t := match t with memid x => x end.


(** * Races & Dependencies *)

Module Races.
  Import Lang.
  Import Semantics.

(* end hide *)

  (** Holds when some task is reading from a heap reference. *) 

  Inductive Read s : tid -> mid -> Prop :=
    read_def:
    forall t h x v r c,
    GetTask h t s ->
    get_code t = SEQ (LDR r v) c ->
    Load t v (HeapLabel x) ->
    Map_NAME.In x (get_data s) ->
    Read s (taskid h) (memid x).

  (** Holds when some task is writing to a heap reference. *) 

  Inductive Write s : tid -> mid -> Prop :=
    write_def:
    forall t r v c x h,
    GetTask h t s ->
    get_code t = SEQ (STR r v) c ->
    Load t v (HeapLabel x) ->
    Map_NAME.In x (get_data s) ->
    Write s (taskid h) (memid x).

  Inductive Racy (s:state) : Prop :=
    racy_def:
    forall t t' x,
    Read s t x ->
    Write s t' x ->
    Racy s.

(* begin hide *)
End Races.

(*
Require Import Aniceto.Map.
Require Import Aniceto.Set.
*)

Module Dependencies.
  Import Map_NAME.
  Import Lang.
  Import Semantics.

(* end hide *)

  (** Defines a dependency node, that can be either a task name or a memory location. *)

  Notation dep := (mid + tid)%type.

  Definition from_dep d := match d with | inl l => from_mid l | inr t => from_tid t end.

  (** Points-to dependency: a variable points to another variable in the store. *)

  Inductive PointsTo (h:heap) : mid -> dep -> Prop :=
  | points_to_tid:
    forall x y,
    MapsTo x (Some (TaskLabel y)) h ->
    PointsTo h (memid x) (inr (taskid y))
  | points_to_mem:
    forall x y,
    MapsTo x (Some (HeapLabel y)) h ->
    PointsTo h (memid x) (inl (memid y)).

  (**
    A refers-to dependency is goes from a task to a memory location through the
    register of the task. *)

  Inductive RefersTo (s:state) : tid -> mid -> Prop :=
  | refers_to_def:
    forall r t x y,
    MapsTo x t (get_tasks s) ->
    MapsTo r (HeapLabel y) (get_registers t) ->
    RefersTo s (taskid x) (memid y).


  (** Blocked dependency: a task is blocked on a future in the taskmap. *)

  Inductive Blocked (s:state) : tid -> tid -> Prop :=
  | blocked_def:
    forall r t v c x y,
    MapsTo x t (get_tasks s) ->
    get_code t = SEQ (FORCE r v) c ->
    Load t v (TaskLabel y) ->
    Blocked s (taskid x) (taskid y).

  (** Dependencies between two names in a state wraps up blocked and points-to
     dependencies. *)

  Inductive Dep s : dep -> dep -> Prop :=
    | dep_points_to:
      forall x y,
      PointsTo (get_data s) x y ->
      Dep s (inl x) y
    | dep_blocked:
      forall x y,
      Blocked s x y ->
      Dep s (inr x) (inr y)
    | dep_read:
      forall x y,
      Races.Read s x y ->
      Dep s (inr x) (inl y)
    | dep_reg:
      forall x y,
      RefersTo s x y ->
      Dep s (inr x) (inl y).

  (* begin hide *)
  Require Import Coq.Relations.Relation_Operators.
  (* end hide *)

  Definition Trans_Blocked c := clos_trans _ (Blocked c).

  (** A deadlocked state has a cycle in the [Trans_Blocked] relation. *)

  Inductive Deadlocked s : Prop :=
    deadlocked_def:
      forall x,
      Trans_Blocked s x x ->
      Deadlocked s.

  (** Defines the [Depends] relation as the transitive closure of [Dep]. *)

  Definition Depends s := clos_trans _ (Dep s).

  Inductive DependsRel s m : Prop :=
  | depends_spec_def:
    (forall x y, Map_NAME.MapsTo (from_dep x) (from_dep y) m <-> Depends s x y) ->
    DependsRel s m.

  (** A state is tainted if there is a cycle in the [Depends] relation.  *) 

  Inductive Tainted s : Prop :=
    tainted_def:
      forall x,
      Depends s x x ->
      Tainted s.

  Inductive Taintless s : Prop :=
    taintless_def:
      (forall x, ~ Depends s x x) ->
      Taintless s.

  Lemma taintless_to_not_tainted:
    forall d s,
    DependsRel s d ->
    ~ Map_NAME.Empty d ->
    Taintless s ->
    ~ Tainted s.
  Proof.
    intros.
    destruct H.
    unfold not; intros.
    destruct H0.
  Admitted.
(*
  Lemma blocked_inv_add:
    forall h e c x y,
    Blocked (add h e c) x y ->
    (exists C, h = x /\
     e = C @ Get (Value (Var y))) \/ Blocked c x y.
  Proof.
    intros.
    inversion H.
    apply Map_NAME_Facts.add_mapsto_iff in H0.
    destruct H0 as [(?,?)|(?,?)].
    - subst.
      left; exists C.
      intuition.
    - right.
      eauto using blocked_def.
  Qed.

  Lemma dep_inv_put_code:
    forall s h e x y,
    Dep (put_code s h e) x y ->
    Dep s x y \/ (exists C, h = x /\ e = C @ Get (Value (Var y))).
  Proof.
    intros.
    inversion H.
    - left.
      auto using dep_points_to.
    - simpl in H0.
      apply blocked_inv_add in H0.
      destruct H0 as [(C,(?,?))|?].
      + right.
        exists C.
        intuition.
      + left.
        auto using dep_blocked.
  Qed.
*)
  Import Operators_Properties.

  Lemma dep_to_depends:
    forall s x y,
    Dep s x y ->
    Depends s x y.
  Proof.
    intros.
    unfold Depends.
    eauto using t_step.
  Qed.
(*
  Lemma tainted_inv:
    forall s h e,
    Tainted (put_code s h e) ->
    Tainted s \/ (exists C, e = C @ Get (Value (Var h))).
  Proof.
    intros.
    inversion H; clear H; rename H0 into H.
    unfold Depends in *.
    inversion H.
    - apply dep_inv_put_code in H0.
      destruct H0 as [?|(C,(?,?))].
      + left.
        eauto using tainted_def, dep_to_depends.
      + right.
        exists C.
        subst.
        trivial.
    - subst. 
  Qed.
*)

  (* XXX: move to Aniceto *)
  Lemma clos_trans_impl:
    forall {A:Type} (P Q: relation A),
    (forall x y, P x y -> Q x y) ->
    forall x y,
    clos_trans A P x y ->
    clos_trans A Q x y.
  Proof.
    intros.
    induction H0.
    - auto using t_step.
    - eauto using t_trans.
  Qed.

  (** A deadlocked state is a special case of a tainted state. *)

  Lemma deadlocked_to_tainted:
    forall s,
    Deadlocked s ->
    Tainted s.
  Proof.
    intros.
    inversion H.
    apply tainted_def with (x:=inl (tid x)).
    unfold Trans_Blocked, reflexive, Depends in *.
    eauto using clos_trans_impl, dep_blocked.
  Qed.

(* begin hide *)

End Dependencies.


Module Deadlocks.
  Import Lang.
  Import Semantics.
  Import Races.
  Import Dependencies.

(* end hide *)

  (** Tainted states are introduced by states. *)
(*
  Let ntainted_preserves_app:
    forall s1 s2,
    ~ Tainted s1 ->
    Reduces s1 APP s2 ->
    ~ Tainted s2.
  Proof.
    intros.
    inversion H0; clear H0; subst.
    unfold not.
    intros.
    inversion H0; clear H0; subst.
    inversion H2.
    - subst; apply dep_inv_put_code in H0.
      destruct H0.
      + contradiction H.
        eauto using tainted_def, dep_to_depends.
      + destruct H0 as (C, (?, Hx)).
        subst.
  Qed.
*)

  Lemma races_impl_tainted:
    forall s1 s2,
    ~ Tainted s1 ->
    Tainted s2 ->
    Reduces s1 s2 ->
    Racy s1.
  Proof.
    intros.
    inversion H1.
    - inversion H3; subst.
      + 
        
      Check (@racy_def s1 h).
  Qed.
*)
  Axiom reduces_preserves_tainted:
    forall s1 s2,
    Tainted s1 ->
    ~ Racy s1 ->
    Reduces s1 s2 ->
    ~ Racy s2.

(* begin hide *)

End Deadlocks.


Module Determinism.

  Require Import Coq.Relations.Relation_Operators.

  Import Semantics.
  Import Races.

(* end hide *)

(** * Determinism *)

  Definition StarReduces := clos_refl_trans _ Reduces.

  Inductive Racefree s : Prop :=
    racefree_def:
      (forall s', StarReduces s s' -> ~ Racy s) ->
      Racefree s.

  Inductive Deterministic s : Prop :=
    deterministic_def:
      (forall s1 s2,
        Reduces s s1 ->
        Reduces s s2 ->
        exists s', (StarReduces s1 s' /\ StarReduces s2 s')) ->
      Deterministic s.

(* begin  hide *)

End Determinism.
