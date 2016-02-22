(* begin hide *)
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import HJ.Tid.
Require Import HJ.Mid.
Require Import HJ.Cid.
Require Import HJ.Var.

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
  | TaskLabel : tid -> word  (* task-id *)
  | HeapLabel : mid -> word  (* heap-id *)
  | CodeLabel : cid -> word. (* code-id *)

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
  | Var: var -> value
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

  Definition store := MV.t word.

  (** Let [mk_store] create an empty store. *)

  Definition mk_store := @MV.empty word.

  Inductive inst :=
  | CALL: var -> value -> list value -> inst
  | LOAD: var -> value -> inst          (* [r := &v] *)
  | STORE: value -> value -> inst          (* [ *r := v] *)
  | MALLOC: var -> inst                (* [r := alloc] *)
  | FUTURE: var -> value -> list value -> inst
  | FORCE: var -> value -> inst.        (* [r := force v] *)

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
    forall x w,
    MV.MapsTo x w m ->
    Load m (Var x) w
  | load_word:
    forall w,
    Load m (Word w) w.

  Variable ARGS : MC.t (list var).

  Inductive BindArgs (m:store): list var -> list value -> store -> Prop :=
  | bind_args_nil:
    BindArgs m nil nil mk_store
  | bind_args_cons:
    forall xs vs x v w m',
    BindArgs m xs vs m' ->
    Load m v w ->
    BindArgs m (x::xs) (v::vs) (MV.add x w m').

  (**
    The code fragment is a parameter of the semantics and contains all
    the programs associated to each code label.
   *)

  Variable CF : MC.t program.

  Inductive LoadFrame (m:store) (v:value) (vs:list value) : frame -> Prop := 
  | call_frame_def:
    forall f m' p rs,
    Load m v (CodeLabel f) ->
    MC.MapsTo f rs ARGS ->
    BindArgs m rs vs m' ->
    MC.MapsTo f p CF ->
    LoadFrame m v vs (m',p).

  (** Call-stack reduction has to do with the rules that control
    the call-stack, [CALL] and [RET. *)

  Inductive TReduces : task -> task -> Prop :=
  | t_reduces_call:
    forall x f vs p s t c,
    LoadFrame s f vs c ->
    TReduces ((s, CALL x f vs ;; p)::t) (c::(s, CALL x f vs ;; p)::t)
  | t_reduces_ret:
    forall x v p s s' vs w t v',
    Load s v w ->
    ~ MV.In x s' ->
    TReduces ((s, RET v) :: (s', CALL x v' vs ;; p) :: t) ((MV.add x w s', p)::t).


  (** ** Memory-level reduction *)

  (*
    The heap represents the main memory and is a map
    from names (memory addresses) into optional words. An undefined word is
      represented by [None]. *)

  Definition heap := MM.t (option word).

  Definition mk_heap := @MM.empty (option word).

  (**
    Next, are reduction rules for instructions that affect a heap [m].
   *)

  Inductive MReduces : (heap * frame) -> (heap * frame) -> Prop :=
  | m_reduces_alloc:
    forall m p h s x,
    ~ MM.In h m ->
    ~ MV.In x s ->
    MReduces (m, (s,MALLOC x ;; p)) ((MM.add h None m), (MV.add x (HeapLabel h) s, p))
  | m_reduces_store_reg:
    forall v1 v2 p h w s m,
    Load s v1 w ->
    Load s v2 (HeapLabel h) ->
    MM.In h m ->
    MReduces (m, (s, STORE v1 v2;; p))  ((MM.add h (Some w) m), (s, p))
  | m_reduces_load_reg:
    forall w s p h x v m,
    Load s v (HeapLabel h) ->
    MM.MapsTo h (Some w) m ->
    ~ MV.In x s ->
    MReduces (m, (s, LOAD x v;; p)) (m, (MV.add x w s, p)).

  (** ** State-level reduction *)

  (**
    The state of an abstract machine corresponds to a heap and a task map.
    Type [taskmap] is a map from names into tasks.
   *)
   
  Definition taskmap := MT.t task.
  
  (* begin hide *)
  
  Definition mk_taskmap := @MT.empty task.

  (* end hide *)


  Inductive FReduces: taskmap -> taskmap -> Prop :=
  | f_reduces_future:
    forall x h h' c v l tm s vs p,
    MT.MapsTo h ((s, FUTURE x v vs;; p)::l) tm ->
    LoadFrame s v vs c ->
    ~ MT.In h' tm ->
    ~ MV.In x s ->
    let t1 := (MV.add x (TaskLabel h') s, p)::l in
    let t2 := c::nil in
    FReduces tm (MT.add h' t2 (MT.add h t1 tm))
  | f_reduces_force:
    forall x p h h' l v v' w tm s s',
    MT.MapsTo h ((s, FORCE x v;;p)::l) tm ->
    Load s v (TaskLabel h') ->
    MT.MapsTo h' ((s', RET v')::nil) tm ->
    Load s' v' w ->
    let new_t := (MV.add x w s, p)::l in
    FReduces tm (MT.add h new_t tm).

  (** A state pairs a store and a taskmap. *)

  Definition state := (heap * taskmap) % type.

  (** The reduction rules at the state level are mainly for the manipulation of
    future-related instructions. *)

  Inductive Reduces : state -> state -> Prop :=
  | reduces_i:
    forall hm tm h t t',
    MT.MapsTo h t tm ->
    TReduces t t' ->
    Reduces (hm, tm) (hm, MT.add h t' tm)
  | reduces_t:
    forall hm hm' tm h e l e',
    MT.MapsTo h (e::l) tm ->
    MReduces (hm, e) (hm', e') ->
    Reduces (hm, tm) (hm, MT.add h (e::l) tm)
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
    MT.MapsTo h ((s, LOAD r v;; p)::l) tm ->
    Load s v (HeapLabel x) ->
    MM.In x hm ->
    Read (hm,tm) h x.

  (** Holds when some task is writing to a heap reference. *)

  Inductive Write: state -> tid -> mid -> Prop :=
  | write_def:
    forall h s x v v' p tm hm l,
    MT.MapsTo h ((s, STORE v v';; p)::l) tm ->
    Load s v' (HeapLabel x) ->
    MM.In x hm ->
    Write (hm,tm) h x.

  Import Lang.
  Import Semantics.

  (** Points-to dependency: a variable points to another variable in the store. *)

  Inductive PointsTo (s:state) : mid -> dep -> Prop :=
  | points_to_tid:
    forall x y,
    MM.MapsTo x (Some (TaskLabel y)) (fst s) ->
    PointsTo s x (d_tid y)
  | points_to_mem:
    forall x y,
    MM.MapsTo x (Some (HeapLabel y)) (fst s) ->
    PointsTo s x (d_mid y).

  (**
    A refers-to dependency is goes from a task to a memory location through the
    register of the task. *)

  Inductive RefersTo: state -> tid -> mid -> Prop :=
  | refers_to_def:
    forall v x y hm tm s p l,
    MT.MapsTo x ((s,p)::l) tm ->
    MV.MapsTo v (HeapLabel y) s ->
    RefersTo (hm,tm) x y.

  Definition get_forced p :=
  match p with
  | FORCE r v;; p => Some v
  | _ => None
  end.

  (** Blocked dependency: a task is blocked on a future in the taskmap. *)
  Inductive Force : tid -> frame -> Prop :=
  | force_def:
    forall y s x v p,
    Load s v (TaskLabel y) ->
    Force y (s, FORCE x v;; p).

  Inductive Blocked: taskmap -> tid -> tid -> Prop :=
  | blocked_def:
    forall x c l y m,
    MT.MapsTo x (c::l) m->
    Force y c ->
    Blocked m x y.

  Let D s : DependenciesSpec :=
    Build_DependenciesSpec (Read s) (Write s)
      (Blocked (snd s))
      (RefersTo s)
      (PointsTo s).

  Section Results.

    Let blocked_add_2:
      forall x y z t m,
      z <> x ->
      Blocked m x y ->
      Blocked (MT.add z t m) x y.
    Proof.
      intros.
      inversion H0; subst.
      eauto using blocked_def, MT.add_2.
    Qed.

    Let deadlocked_impl_t_reduces:
      forall h t t' hm tm,
      MT.MapsTo h t tm ->
      TReduces t t' ->
      Deadlocked (D (hm, tm)) ->
      Reduces (hm, tm) (hm, MT.add h t' tm) ->
      Deadlocked (D (hm, MT.add h t' tm)).
    Proof.
      intros.
      apply deadlocked_impl with (D:= D (hm,tm)); eauto.
      intros.
      apply blocked_add_2; auto.
      unfold not; intros;
      inversion H0; subst.
      - inversion H3; subst; clear H3.
        simpl in *.
        assert (c0 = (s, CALL x0 f vs;; p)). {
          assert (He: c0::l = (s, CALL x0 f vs;; p) :: t0). {
            eauto using MT_Facts.MapsTo_fun.
          }
          inversion He; subst.
          intuition.
        }
        subst.
        inversion H6.
      - assert (Hx := H3).
        inversion H3; subst; clear H3.
        simpl in *.
        assert (X: c = (s, RET v)). {
          assert (c::l = ((s, RET v) :: (s', CALL x0 v' vs;; p) :: t0)). {
            eauto using MT_Facts.MapsTo_fun.
          }
          inversion H3; subst.
          intuition.
        }
        subst.
        inversion H7.
    Qed.

    Let deadlocked_impl_m_reduces:
      forall h e l tm hm hm' e',
      MT.MapsTo h (e :: l) tm ->
      MReduces (hm, e) (hm', e') ->
      Deadlocked (D (hm, tm)) ->
      Reduces (hm, tm) (hm, MT.add h (e :: l) tm) ->
      Deadlocked (D (hm, MT.add h (e :: l) tm)).
    Proof.
      intros.
      apply deadlocked_impl with (D:= D (hm,tm)); eauto.
      intros.
      destruct x as (x).
      apply blocked_add_2; auto.
      unfold not; intros; subst.
      inversion H3; clear H3.
      inversion H0; subst; simpl in *.
      - assert (X: c = (s,  MALLOC x1;; p)). {
          assert (c::l0 = ((s,  MALLOC x1;; p) :: l)). {
            eauto using MT_Facts.MapsTo_fun.
          }
          inversion H3; subst.
          intuition.
        }
        subst.
        inversion H5.
      - assert (X: c = (s, STORE v1 v2;; p)). {
          assert (c::l0 = ((s, STORE v1 v2;; p) :: l)). {
            eauto using MT_Facts.MapsTo_fun.
          }
          inversion H3; subst.
          intuition.
        }
        subst.
        inversion H5.
      - assert (X: c = (s, LOAD x1 v;; p)). {
          assert (c::l0 = ((s, LOAD x1 v;; p) :: l)). {
            eauto using MT_Facts.MapsTo_fun.
          }
          inversion H3; subst.
          intuition.
        }
        subst.
        inversion H5.
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
        eauto using MV_Facts.MapsTo_fun.
      - inversion H0; auto.
    Qed.

    Lemma blocked_inv_forced:
      forall x y c t m,
      MT.MapsTo x (c :: t) m ->
      Blocked m x y ->
      Force y c.
    Proof.
      intros.
      inversion H0.
      subst.
      assert (c0 = c). {
        assert (He: c0 :: l = c :: t)
        by eauto using MT_Facts.MapsTo_fun.
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
        apply blocked_add_2; auto.
        + unfold not; intros; rewrite H7 in *; clear H7.
          inversion H6; clear H6; subst.
          contradiction H4.
          eauto using MT_Extra.mapsto_to_in.
        + apply blocked_add_2; auto.
          unfold not; intros.
          rewrite H7 in *; clear H7.
          inversion H6; simpl in *; subst.
          assert (c0 = (s, FUTURE x v vs;; p)). {
            assert (He: (c0 :: l0) = ((s, FUTURE x v vs;; p) :: l))
            by eauto using MT_Facts.MapsTo_fun.
            inversion He; subst.
            trivial.
          }
          subst; inversion H8.
      - apply deadlocked_impl_ex with (D:= D (hm,tm)); eauto.
        intros.
        destruct (TID.eq_dec h x0). {
          rewrite tid_eq_rw in *; subst.
          inversion H7; subst; simpl in *; clear H7.
          inversion H9; subst.
          assert (He: s0 = s /\ v0 = v). {
            assert (He: (s0, FORCE x1 v0;; p0) :: l0 = (s, FORCE x v;; p) :: l)
            by eauto using MT_Facts.MapsTo_fun.
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

    Lemma untainted_to_tainted_impl_race:
      forall (s1:state) (s2:state),
      Untainted (D s1) ->
      Reduces s1 s2 ->
      Tainted (D s2) ->
      Racy (D s1).
    Proof.
      intros.
      
    Qed.

    Lemma race_free_preserves_untainted:
      forall (s1:state) (s2:state),
      RaceFree (D s1) ->
      Untainted (D s1) ->
      Reduces s1 s2 ->
      Untainted (D s2).
    Proof.
      intros.
      apply untainted_impl with (D:=D s1); auto.
      intros.
      inversion H1; subst.
      - 
      apply untainted_def.
      intros.
      intuition.
      inversion H1; subst.
      - 
      apply untainted_impl with (D:=D s1); auto.
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
