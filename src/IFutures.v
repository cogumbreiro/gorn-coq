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
    Our language is a trivial extension of TAL, extended with futures and shared memory.
  *)

  Notation register := name.

  (** As for words we have numbers, and three kinds of handles: task identifiers,
    heap pointers, and function names. *)

  Inductive word :=
  | Num: nat -> word    (* number *)
  | Task : name -> word  (* task-id *)
  | Heap : name -> word  (* heap-id *)
  | Code : name -> word. (* code-id *)

  (** A value, in TAL lingo, is either a register number or a word. It only has
    meaning in the context of a register-store. *)

  Inductive value :=
  | Reg: name -> value   (* register *)
  | Word: word -> value.

  (**
    TAL exposes a rudimentary expression-based language, for illustration
    purposes we only define addition, but other operations (like multiplication)
    can easily be included in this definition.
    *)

  Inductive exp := 
  | Add : register -> value -> exp (* [r' + v] *)
  | Value: value -> exp.           (* [v] *)

  Inductive inst :=

  (** TAL operations *)

  | Move : register -> exp -> inst           (* [r := e] *)
  | BranchNotZero: register -> value -> inst (* [if r <> 0 jmp v] *)

  (**
    Future operations. lhs operand is the target register,
    rhs operand is the function name in the first case and the task id in
    the second case.
   *)

  | Future: register -> value -> inst    (* [r := future v] *)
  | Get: register -> value -> inst       (* [r := get v] *)

  (** Shared memory operations.
    [Mkref] expects the target register and the value to initialize the memory cell.
    [Assign] expects the memory cell reference on the rhs and the value to assign in the lhs.
    [Deref] expects the target register in the lhs and the memory cell on the lhs. *)

  | Mkref: register -> value -> inst     (* [r := ref v] *)
  | Assign: register -> value -> inst    (* [r := &v] *) 
  | Deref: register -> value -> inst. (* [r := *v] *)

  (**
   Standard TAL operations for instruction execution. [Ret v] defines the value
   that is communicated to a future.
   *)

  Inductive code :=
  | Seq : inst -> code -> code
  | Ret : value -> code
  | Jump: value -> code.

  (** A store maps from names/registers into values. *)

  Definition store := Map_NAME.t word.

  (** Let [mk_store] create an empty store. *)

  Definition mk_store := @Map_NAME.empty word.

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
    get_data: store;
    get_tasks: taskmap
  }.

  (** The [load] function creates the initial state, running expression [e] with name [h]. *)

  Definition load (h:name) (e:code) := mk_state mk_store (Map_NAME.add h (mk_task mk_store e) mk_taskmap).

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

  Inductive Load : value -> word -> store -> Prop :=
  | load_reg:
    forall r w s,
    Map_NAME.MapsTo r w s ->
    Load (Reg r) w s
  | load_word:
    forall w s,
    Load (Word w) w s.

  (** [Eval] takes an expression and yields a word. *)

  Inductive Eval : exp -> word -> store -> Prop :=
  | eval_add:
    forall r v n1 n2 s,
    Load (Reg r) (Num n1) s ->
    Load v (Num n2) s ->
    Eval (Add r v) (Num (n1 + n2)) s
  | eval_load:
    forall v w s,
    Load v w s ->
    Eval (Value v) w s.

  (**
    The code fragment is a parameter of the semantics that holds
    the code declarations.
   *)

  Variable code_fragment : Map_NAME.t code.

  (** For simplicity we abbreviate [Load] relative to a task's registers. *)

  Notation TLoad v w t := (Load v w (get_registers t)).

  (** We define a standard register-machine reduction *)

  Inductive IReduces (t:task) : task -> Prop :=
  | i_reduces_mov:
    forall dst e v c,
    get_code t = Seq (Move dst e) c ->
    Eval e v (get_registers t) ->
    IReduces t (put_register dst v (set_code c t))
  | i_reduces_bnz_skip:
    forall r v h c,
    get_code t = Seq (BranchNotZero r v) c ->
    TLoad (Reg r) (Code h) t ->
    TLoad v (Num 0) t ->
    IReduces t (set_code c t)
  | i_reduces_bnz_jmp:
    forall r v h c n c',
    get_code t = Seq (BranchNotZero r v) c ->
    TLoad (Reg r) (Code h) t ->
    TLoad v (Num (S n)) t ->
    Map_NAME.MapsTo h c' code_fragment ->
    IReduces t (set_code c' t)
  | i_reduces_jmp:
    forall c l v,
    get_code t = Jump v ->
    TLoad v (Code l) t ->
    Map_NAME.MapsTo l c code_fragment ->
    IReduces t (set_code c t).

  (**
    The next reduction rules define register machine (a task)
    that has access to a main memory [s].
   *)

  Inductive TReduces (s:store) (t:task) : store -> task -> Prop :=
  | t_reduces_i:
    forall t',
    IReduces t t' ->
    TReduces s t s t'
  | t_reduces_assign:
    forall v v' c h r,
    get_code t = Seq (Assign r v) c ->
    TLoad (Reg r) (Heap h) t ->
    Map_NAME.In h s ->
    TLoad v v' t ->
    TReduces s t (Map_NAME.add h v' s) (set_code c t)
  | t_reduces_deref:
    forall src dst c h v,
    get_code t = Seq (Deref dst src) c ->
    TLoad src (Heap h) t ->
    Map_NAME.MapsTo h v s ->
    TReduces s t s (put_register dst v (set_code c t)).

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
    get_code t = Seq (Future dst v) c ->
    TLoad v (Code l) t ->
    Map_NAME.MapsTo l c' code_fragment ->
    ~ Map_NAME.In h' (get_tasks s) ->
    Reduces s
      (put_task h (put_register dst (Task h') (set_code c t))
        (put_task h' (set_code c' t) s))
  | reduces_get:
    forall r c h h' t t' v x y,
    GetTask h t s ->
    get_code t = Seq (Get r x) c ->
    TLoad x (Task h') t ->
    GetTask h' t' s ->
    get_code t' = Ret y ->
    TLoad y v t' ->
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

  Inductive Read s h x : Prop :=
    read_def:
    forall t dst v c,
    GetTask (from_tid h) t s ->
    get_code t = Seq (Deref dst v) c ->
    TLoad v (Heap (from_mid x)) t ->
    Read s h x.

  (** Holds when some task is writing to a heap reference. *) 

  Inductive Write s h x : Prop :=
    write_def:
    forall t v r c,
    GetTask (from_tid h) t s ->
    get_code t = Seq (Assign r v) c ->
    TLoad (Reg r) (Heap (from_mid x)) t ->
    Write s h x.

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

  Inductive PointsTo d: mid -> dep -> Prop :=
  | points_to_tid:
    forall x y,
    MapsTo (from_mid x) (Task (from_tid y)) d ->
    PointsTo d x (inr y)
  | points_to_mem:
    forall x y,
    MapsTo (from_mid x) (Heap (from_mid y)) d ->
    PointsTo d x (inl y).
    
  (** Blocked dependency: a task is blocked on a future in the taskmap. *)

  Inductive Blocked m (x:tid) (y:tid) : Prop :=
    blocked_def:
      forall r t v c,
      MapsTo (from_tid x) t m ->
      get_code t = Seq (Get r v) c ->
      TLoad v (Task (from_tid y)) t ->
      Blocked m x y.

  (** Dependencies between two names in a state wraps up blocked and points-to
     dependencies. *)

  Inductive Dep s : dep -> dep -> Prop :=
    | dep_points_to:
      forall x y,
      PointsTo (get_data s) x y ->
      Dep s (inl x) y
    | dep_blocked:
      forall x y,
      Blocked (get_tasks s) x y ->
      Dep s (inr x) (inr y)
    | dep_read:
      forall x y,
      Races.Read s x y ->
      Dep s (inr x) (inl y).

  (* begin hide *)
  Require Import Coq.Relations.Relation_Operators.
  (* end hide *)

  Definition Trans_Blocked c := clos_trans _ (Blocked c).

  (** A deadlocked state has a cycle in the [Trans_Blocked] relation. *)

  Inductive Deadlocked s : Prop :=
    deadlocked_def:
      forall x,
      Trans_Blocked (get_tasks s) x x ->
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
