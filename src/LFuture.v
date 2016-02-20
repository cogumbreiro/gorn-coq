(* begin hide *)
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import HJ.Preamble.
Require Import HJ.Register.

(* ----- end of boiler-plate code ---- *)

Set Implicit Arguments.

Module Lang.

(* end hide *)

(** * Language *)

  (**
    Our language is a simple Typed Assembly Language (TAL) with futures and shared memory.
    The syntax and semantics follows the ARM instruction set.
    The language is devide into two main notions: data and code.
     
    %\textbf{Data}.%
    When it comes to data we have the contents of data and references to data (called registers).
    Words are the fundamental element of computation, which we separate according to its use:
    numbers, task identifiers, memory addresses, and function names.
  *)

  Inductive word :=
  | Num: nat -> word    (* number *)
  | TaskLabel : name -> word  (* task-id *)
  | HeapLabel : name -> word  (* heap-id *)
  | CodeLabel : name -> word. (* code-id *)

(* begin hide *)

  Notation "'#' i" := (Num i) (at level 60).

(* end hide *)

  (**
    A value is consumed by code and can be either a word or a register (a reference to a word).
    When typesetting and it is unambiguous that we are using values, we omit the [Reg]
    and [Word] prefixes.

    %\newcommand{\Reg}[1]{{#1}}
    \newcommand{\Word}[1]{{#1}}
    %

    *)

  Inductive value :=
  | Reg: register -> value   (* register *)
  | Word: word -> value.

  (** 
  
    Next we describe the instructions and instruction sequences.

    %\textbf{Standard instructions.}%
    [MOV] copies data into a register.
    [ADD] performs integer addition.
    [BNZ] jumps to a code fragment if the first operand (a register) is not zero.
    [LOAD] the loaded data (in the right-hand side) is placed into the register.
    [STORE] the data found in the value is stored
    into memory.
    [BX] jumps the target code and is the last instruction in an instruction sequence.

    %\textbf{Future-specific instructions.}%
    Instruction [FUTURE] expects a target register and source value.
    The instruction creates a new task and assigns its task label to
    the target register.
    The new task runs the code in the source value, so it expects that
    there is a code label.

    Instruction [FORCE] expects a target register and a source value.
    The instruction blocks until the task (pointed by the source value) promises
    a value, that is copied to the target register.
    [MALLOC] creates a memory cell and assigns the memory location to the
    register (in the operand).
    Tasks terminate their execution by fulfilling their promise of a future value.
    The promise is read by another tasks that executes [FORCE].
    
   *)


  (**
    A task consists of a store, where data of the local registers reside, and
    a program to execute.
    A store maps registers into words. Here [MR.t] a parametric type of a map
    where the keys are registers. *)

  Definition store := MR.t word.

  (** Let [mk_store] create an empty store. *)

  Definition mk_store := @MR.empty word.

  Inductive inst :=
  | CALL: register -> value -> list value -> inst
  | LOAD: register -> value -> inst          (* [r := &v] *)
  | STORE: value -> value -> inst          (* [ *r := v] *)
  | MALLOC: register -> inst                (* [r := alloc] *)
  | FUTURE: register -> value -> list value -> inst
  | FORCE: register -> value -> inst.        (* [r := force v] *)

  Inductive program :=
  | RET: value -> program
  | SEQ : inst -> program -> program.

  Infix ";;" := SEQ (at level 62, right associativity).

(* begin hide*)
End Lang.
(* end hide *)

(* begin hide  *)

Module Semantics.
  Import Lang.

  Notation frame := (store * program) % type. 

  (** ** Task-level reduction *)

  (** We are now ready to define a task. *)

  Notation task := (list frame).

(* end hide *)

  (** Proposition [Load] evaluates a value into a word. *)

  Inductive Load (m:store) : value -> word -> Prop :=
  | load_reg:
    forall r w,
    MR.MapsTo r w m ->
    Load m (Reg r) w
  | load_word:
    forall w,
    Load m (Word w) w.

  Variable args : MN.t (list register).

  Inductive BindArgs (m:store): list register -> list value -> store -> Prop :=
  | bind_args_nil:
    BindArgs m nil nil mk_store
  | bind_args_cons:
    forall rs vs r v w m',
    BindArgs m rs vs m' ->
    Load m v w ->
    BindArgs m (r::rs) (v::vs) (MR.add r w m').

  (**
    The code fragment is a parameter of the semantics and contains all
    the programs associated to each code label.
   *)

  Variable CF : MN.t program.

  Inductive LoadFrame (m:store) (v:value) (vs:list value) : frame -> Prop := 
  | call_frame_def:
    forall f m' p rs,
    Load m v (TaskLabel f) ->
    MN.MapsTo f rs args ->
    BindArgs m rs vs m' ->
    MN.MapsTo f p CF ->
    LoadFrame m v vs (m',p).

  (** Call-stack reduction has to do with the rules that control
    the call-stack, [CALL] and [RET. *)

  Inductive TReduces : task -> task -> Prop :=
  | t_reduces_call:
    forall r v vs p s t c,
    LoadFrame s v vs c ->
    TReduces ((s, CALL r v vs ;; p)::t) (c::(s, CALL r v vs ;; p)::t)
  | t_reduces_ret:
    forall r v p s s' vs w t v',
    Load s v w ->
    ~ MR.In r s' ->
    TReduces ((s, RET v) :: (s', CALL r v' vs ;; p) :: t) ((MR.add r w s', p)::t).


  (** ** Memory-level reduction *)

  (*
    The heap represents the main memory and is a map
    from names (memory addresses) into optional words. An undefined word is
      represented by [None]. *)

  Definition heap := MN.t (option word).

  Definition mk_heap := @MN.empty (option word).

  (**
    Next, are reduction rules for instructions that affect a heap [m].
   *)

  Inductive MReduces : (heap * frame) -> (heap * frame) -> Prop :=
  | m_reduces_alloc:
    forall m p h s r,
    ~ MN.In h m ->
    ~ MR.In r s ->
    MReduces (m, (s,MALLOC r ;; p)) ((MN.add h None m), (MR.add r (HeapLabel h) s, p))
  | m_reduces_store_reg:
    forall v1 v2 p h w s m,
    Load s v1 w ->
    Load s v2 (HeapLabel h) ->
    MN.In h m ->
    MReduces (m, (s, STORE v1 v2;; p))  ((MN.add h (Some w) m), (s, p))
  | m_reduces_load_reg:
    forall w s p h r v m,
    Load s v (HeapLabel h) ->
    MN.MapsTo h (Some w) m ->
    ~ MR.In r s ->
    MReduces (m, (s, LOAD r v;; p)) (m, (MR.add r w s, p)).

  (** ** State-level reduction *)

  (**
    The state of an abstract machine corresponds to a heap and a task map.
    Type [taskmap] is a map from names into tasks.
   *)
   
  Definition taskmap := MN.t task.
  
  (* begin hide *)
  
  Definition mk_taskmap := @MN.empty task.

  (* end hide *)


  Inductive FReduces: taskmap -> taskmap -> Prop :=
  | f_reduces_future:
    forall r h h' c v l tm s vs p,
    MN.MapsTo h ((s, FUTURE r v vs;; p)::l) tm ->
    LoadFrame s v vs c ->
    ~ MN.In h' tm ->
    ~ MR.In r s ->
    let t1 := (MR.add r (TaskLabel h') s, p)::l in
    let t2 := c::nil in
    FReduces tm (MN.add h' t2 (MN.add h t1 tm))
  | f_reduces_force:
    forall r p h h' l v v' w tm s s',
    MN.MapsTo h ((s, FORCE r v;;p)::l) tm ->
    Load s v (TaskLabel h') ->
    MN.MapsTo h' ((s', RET v')::nil) tm ->
    Load s' v' w ->
    let new_t := (MR.add r w s, p)::l in
    FReduces tm (MN.add h new_t tm).

  (** A state pairs a store and a taskmap. *)

  Definition state := (heap * taskmap) % type.

  (** The reduction rules at the state level are mainly for the manipulation of
    future-related instructions. *)

  Inductive Reduces : state -> state -> Prop :=
  | reduces_i:
    forall hm tm h t t',
    MN.MapsTo h t tm ->
    TReduces t t' ->
    Reduces (hm, tm) (hm, MN.add h t' tm)
  | reduces_t:
    forall hm hm' tm h e l e',
    MN.MapsTo h (e::l) tm ->
    MReduces (hm, e) (hm', e') ->
    Reduces (hm, tm) (hm, MN.add h (e::l) tm)
  | reduces_f:
    forall hm tm tm',
    FReduces tm tm' ->
    Reduces (hm, tm) (hm, tm').


End Semantics.


Module Races.
  Require Import HJ.Races.
  Import Lang.
  Import Semantics.

  (** Holds when some task is reading from a heap reference. *) 

  Inductive Read: state -> tid -> mid -> Prop :=
  | read_def:
    forall h s x v r p tm hm l,
    MN.MapsTo h ((s, LOAD r v;; p)::l) tm ->
    Load s v (HeapLabel x) ->
    MN.In x hm ->
    Read (hm,tm) (taskid h) (memid x).

  (** Holds when some task is writing to a heap reference. *)

  Inductive Write: state -> tid -> mid -> Prop :=
  | write_def:
    forall h s x v v' p tm hm l,
    MN.MapsTo h ((s, STORE v v';; p)::l) tm ->
    Load s v' (HeapLabel x) ->
    MN.In x hm ->
    Write (hm,tm) (taskid h) (memid x).

  Import Lang.
  Import Semantics.

  (** Points-to dependency: a variable points to another variable in the store. *)

  Inductive PointsTo (s:state) : mid -> dep -> Prop :=
  | points_to_tid:
    forall x y,
    MN.MapsTo x (Some (TaskLabel y)) (fst s) ->
    PointsTo s (memid x) (inr (taskid y))
  | points_to_mem:
    forall x y,
    MN.MapsTo x (Some (HeapLabel y)) (fst s) ->
    PointsTo s (memid x) (inl (memid y)).

  (**
    A refers-to dependency is goes from a task to a memory location through the
    register of the task. *)

  Inductive RefersTo: state -> tid -> mid -> Prop :=
  | refers_to_def:
    forall r x y hm tm s p l,
    MN.MapsTo x ((s,p)::l) tm ->
    MR.MapsTo r (HeapLabel y) s ->
    RefersTo (hm,tm) (taskid x) (memid y).

  Definition get_forced p :=
  match p with
  | FORCE r v;; p => Some v
  | _ => None
  end.

  (** Blocked dependency: a task is blocked on a future in the taskmap. *)
  Inductive Force : name -> frame -> Prop :=
  | force_def:
    forall y s r v p,
    Load s v (TaskLabel y) ->
    Force y (s, FORCE r v;; p).

  Inductive Blocked: taskmap -> tid -> tid -> Prop :=
  | blocked_def:
    forall x c l y m,
    MN.MapsTo x (c::l) m->
    Force y c ->
    Blocked m (taskid x) (taskid y).

  Let D s : DependenciesSpec :=
    Build_DependenciesSpec (Read s) (Write s)
      (PointsTo s) (RefersTo s) (Blocked (snd s)).

  Section Results.

    Let blocked_add_2:
      forall x y z t m,
      z <> x ->
      Blocked m (taskid x) y ->
      Blocked (MN.add z t m) (taskid x) y.
    Proof.
      intros.
      inversion H0; subst.
      eauto using blocked_def, MN.add_2.
    Qed.

    Let deadlocked_impl_t_reduces:
      forall h t t' hm tm,
      MN.MapsTo h t tm ->
      TReduces t t' ->
      Deadlocked (D (hm, tm)) ->
      Reduces (hm, tm) (hm, MN.add h t' tm) ->
      Deadlocked (D (hm, MN.add h t' tm)).
    Proof.
      intros.
      apply deadlocked_impl with (D:= D (hm,tm)); eauto.
      intros.
      destruct x as (x).
      apply blocked_add_2; auto.
      unfold not; intros;
      inversion H0; subst.
      - inversion H3; subst; clear H3.
        simpl in *.
        assert (c0 = (s, CALL r v vs;; p)). {
          assert (He: c0::l = (s, CALL r v vs;; p) :: t0). {
            eauto using MN_Facts.MapsTo_fun.
          }
          inversion He; subst.
          intuition.
        }
        subst.
        inversion H8; subst.
      - assert (Hx := H3).
        inversion H3; subst; clear H3.
        simpl in *.
        assert (X: c = (s, RET v)). {
          assert (c::l = ((s, RET v) :: (s', CALL r v' vs;; p) :: t0)). {
            eauto using MN_Facts.MapsTo_fun.
          }
          inversion H3; subst.
          intuition.
        }
        subst.
        inversion H9; subst.
    Qed.

    Let deadlocked_impl_m_reduces:
      forall h e l tm hm hm' e',
      MN.MapsTo h (e :: l) tm ->
      MReduces (hm, e) (hm', e') ->
      Deadlocked (D (hm, tm)) ->
      Reduces (hm, tm) (hm, MN.add h (e :: l) tm) ->
      Deadlocked (D (hm, MN.add h (e :: l) tm)).
    Proof.
      intros.
      apply deadlocked_impl with (D:= D (hm,tm)); eauto.
      intros.
      destruct x as (x).
      apply blocked_add_2; auto.
      unfold not; intros; subst.
      inversion H3; clear H3.
      inversion H0; subst; simpl in *.
      - assert (X: c = (s,  MALLOC r;; p)). {
          assert (c::l0 = ((s,  MALLOC r;; p) :: l)). {
            eauto using MN_Facts.MapsTo_fun.
          }
          inversion H3; subst.
          intuition.
        }
        subst.
        inversion H7.
      - assert (X: c = (s, STORE v1 v2;; p)). {
          assert (c::l0 = ((s, STORE v1 v2;; p) :: l)). {
            eauto using MN_Facts.MapsTo_fun.
          }
          inversion H3; subst.
          intuition.
        }
        subst.
        inversion H7.
      - assert (X: c = (s, LOAD r v;; p)). {
          assert (c::l0 = ((s, LOAD r v;; p) :: l)). {
            eauto using MN_Facts.MapsTo_fun.
          }
          inversion H3; subst.
          intuition.
        }
        subst.
        inversion H7.
    Qed.

    Lemma load_fun:
      forall s v w w',
      Load s v w ->
      Load s v w' ->
      w' = w.
    Proof.
      intros.
      inversion H; subst.
      - inversion H0; subst.
        eauto using MR_Facts.MapsTo_fun.
      - inversion H0; auto.
    Qed.

    Lemma blocked_inv_forced:
      forall x y c t m,
      MN.MapsTo x (c :: t) m ->
      Blocked m (taskid x) (taskid y) ->
      Force y c.
    Proof.
      intros.
      inversion H0.
      subst.
      assert (c0 = c). {
        assert (He: c0 :: l = c :: t)
        by eauto using MN_Facts.MapsTo_fun.
        inversion He; subst; trivial.
      }
      subst.
      trivial.
    Qed.

    Let deadlock_impl_f_reduces:
      forall tm tm' hm,
      FReduces tm tm' ->
      Deadlocked (D (hm, tm)) ->
      Reduces (hm, tm) (hm, tm') ->
      Deadlocked (D (hm, tm')).
    Proof.
      intros.
      inversion H; subst.
      - apply deadlocked_impl with (D:=D (hm,tm)); eauto.
        intros.
        destruct x as (x).
        apply blocked_add_2; auto.
        + unfold not; intros; rewrite H7 in *; clear H7.
          inversion H6; clear H6; subst.
          contradiction H4.
          eauto using MN_Extra.mapsto_to_in.
        + apply blocked_add_2; auto.
          unfold not; intros.
          rewrite H7 in *; clear H7.
          inversion H6; simpl in *; subst.
          assert (c0 = (s, FUTURE r v vs;; p)). {
            assert (He: (c0 :: l0) = ((s, FUTURE r v vs;; p) :: l))
            by eauto using MN_Facts.MapsTo_fun.
            inversion He; subst.
            trivial.
          }
          subst; inversion H10.
      - apply deadlocked_impl_ex with (D:= D (hm,tm)); eauto.
        intros.
        destruct x as (x).
        destruct y as (y).
        destruct (NAME.eq_dec h x). {
          subst.
          inversion H7; subst; simpl in *; clear H7.
          inversion H12; subst.
          assert (He: s0 = s /\ v0 = v). {
            assert (He: (s0, FORCE r0 v0;; p0) :: l0 = (s, FORCE r v;; p) :: l)
            by eauto using MN_Facts.MapsTo_fun.
            inversion He; subst.
            auto.
          }
          destruct He; subst.
          assert (h' = y). {
            assert (He : TaskLabel h' = TaskLabel y)
            by (eapply load_fun; eauto).
            inversion He; subst; trivial.
          }
          subst.
          destruct z as (z).
          assert (HF: Force z (s', RET v')) by eauto using blocked_inv_forced.
          inversion HF.
        }
        apply blocked_add_2; auto.
    Qed.

    Lemma deadlock_stable:
      forall s1 s2,
      Deadlocked (D s1) ->
      Reduces s1 s2 ->
      Deadlocked (D s2).
    Proof.
      intros.
      inversion H0; subst; eauto.
    Qed.

    Lemma race_free_preserves_untainted:
      forall (s1:state) (s2:state),
      RaceFree (D s1) ->
      Untainted (D s1) ->
      Reduces s1 s2 ->
      Untainted (D s2).
    Proof.
      intros.
      inversion H1; subst.
      - inversion H3.
        + 
    Qed.

    Lemma race_free_preserves:
      forall (s1:state) (s2:state),
      RaceFree (D s1) ->
      Untainted (D s1) ->
      Reduces s1 s2 ->
      DeadlockFree (D s2).
    Proof.
      intros.
      inversion H1; subst.
      - 
    Qed.
    
    

End Race.


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
(* begin hide *)
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
  Admitted.

  Axiom reduces_preserves_tainted:
    forall s1 s2,
    Tainted s1 ->
    ~ Racy s1 ->
    Reduces s1 s2 ->
    ~ Racy s2.


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
