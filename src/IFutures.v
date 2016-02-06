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
Module MN := FMapAVL.Make NAME.
Module MN_Facts := FMapFacts.Facts MN.
Module MN_Props := FMapFacts.Properties MN.
(*Module Map_ID_Extra := MapUtil Map_ID.*)

Definition name := NAME.t.
Definition set_name := Set_NAME.t.

Lemma name_eq_rw:
  forall k k' : name, k = k' <-> k = k'.
Proof.
  intros.
  auto with *.
Qed.

Inductive register := reg : nat -> register.

Definition register_num r := match r with | reg n => n end.

Module REG <: UsualOrderedType.
  Definition t := register.
  Definition eq := @eq register.
  Definition lt x y := lt (register_num x) (register_num y).
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Lemma lt_trans: forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    intros.
    unfold lt in *.
    destruct x, y, z.
    simpl in *.
    eauto.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    unfold lt in *.
    intros.
    destruct x, y.
    simpl in *.
    unfold not; intros.
    inversion H0.
    subst.
    apply Lt.lt_irrefl in H.
    inversion H.
  Qed.

  Require Import Coq.Arith.Compare_dec.
  Lemma compare:
    forall x y, Compare lt eq x y.
  Proof.
    intros.
    destruct x, y.
    destruct (Nat_as_OT.compare n n0);
    eauto using LT, GT.
    apply EQ.
    unfold Nat_as_OT.eq in *.
    subst.
    intuition.
  Qed.

  Require Import Coq.Arith.Peano_dec.

  Lemma eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
  Proof.
    intros.
    unfold eq.
    destruct x, y.
    destruct (eq_nat_dec n n0).
    - subst; eauto.
    - right.
      unfold not.
      intros.
      contradiction n1.
      inversion H; auto.
  Qed.
End REG.

Module MR := FMapAVL.Make REG.

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
    [LDR] the loaded data (in the right-hand side) is placed into the register.
    [STR] the data found in the value is stored
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
    [ALLOC] creates a memory cell and assigns the memory location to the
    register (in the operand).
    Tasks terminate their execution by fulfilling their promise of a future value.
    The promise is read by another tasks that executes [FORCE].
    
   *)

  Inductive inst :=
  | MOV: register -> value -> inst          (* [r := v] *)
  | ADD: register -> register -> value -> inst  (* [r1 := r2 + v] *)
  | BNZ: register -> value -> inst          (* [if r <> 0 jmp v] *)
  | LDR: register -> value -> inst          (* [r := &v] *)
  | STR: register -> value -> inst          (* [ *r := v] *)
  | FUTURE: register -> value -> inst       (* [r := future v] *)
  | FORCE: register -> value -> inst        (* [r := force v] *)
  | ALLOC: register -> inst.                (* [r := alloc] *)

  Inductive program :=
  | BX: value -> program
  | SEQ : inst -> program -> program
  | PROMISE : value -> program.

  Infix ";;" := SEQ (at level 62, right associativity).

  (** ** Task-level reduction *)

  (**
    A task consists of a store, where data of the local registers reside, and
    a program to execute.
    A store maps registers into words. Here [MR.t] a parametric type of a map
    where the keys are registers. *)

  Definition store := MR.t word.

  (** Let [mk_store] create an empty store. *)

  Definition mk_store := @MR.empty word.

  (** We are now ready to define a task. *)

  Notation task := (store * program) % type. 


(* begin hide*)
  Definition get_registers := @fst store program.
  Definition get_code := @snd store program.

End Lang.
(* end hide *)

(* begin hide  *)

Module Semantics.
  Import Lang.

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


  (**
  Let  $\Gamma(v) \mapsto w$ be a notation for [Load] $\Gamma$ [v w].
  The inductive definition of [Load] is typeset below.
  %
  $$
  \frac{
    \Gamma(r) = w
  }{
    \Gamma(\Reg r) \mapsto w
  }
  \qquad
  \frac{
  }{
    \Gamma(\Word w) \mapsto w
  }
  $$
  %
  *)

  (**
    The code fragment is a parameter of the semantics and contains all
    the programs associated to each code label.
   *)

  Variable CF : MN.t program.

  (** We define a standard register-machine reduction *)

  Inductive IReduces : task -> task -> Prop :=
  | i_reduces_mov:
    forall s r v w p,
    Load s v w ->
    IReduces (s, MOV r v ;; p) (MR.add r w s, p)
  | i_reduces_add:
    forall r r' v n1 n2 p s,
    Load s (Reg r') (Num n1) ->
    Load s v (Num n2) ->
    IReduces (s, ADD r r' v ;; p) (MR.add r (Num (n1 + n2)) s, p)
  | i_reduces_bnz_skip:
    forall r v p s,
    Load s (Reg r) (Num 0) ->
    IReduces (s, BNZ r v ;; p) (s, p)
  | i_reduces_bnz_jmp:
    forall r v h p n p' s,
    Load s (Reg r) (CodeLabel h) ->
    Load s v (Num (S n)) ->
    MN.MapsTo h p' CF ->
    IReduces (s, BNZ r v ;; p) (s, p')
  | i_reduces_jmp:
    forall p h v s,
    Load s v (CodeLabel h) ->
    MN.MapsTo h p CF ->
    IReduces (s, BX v) (s, p).


  (**
   %
   \newcommand{\IReduces}{\rightarrow_{\mathtt{i}}}
   \newcommand{\MOV}[2]{\mathtt{MOV}\ {#1}\ {#2}}
   \newcommand{\ADD}[3]{\mathtt{ADD}\ {#1}\ {#2}\ {#3}}
   \newcommand{\BNZ}[2]{\mathtt{BNZ}\ {#1}\ {#2}}
   \newcommand{\BX}[1]{\mathtt{BX}\ {#1}}
   \newcommand{\ALLOC}[1]{\mathtt{ALLOC}\ {#1}}
   \newcommand{\STR}[2]{\mathtt{STR}\ {#1}\ {#2}}
   \newcommand{\LDR}[2]{\mathtt{LDR}\ {#1}\ {#2}}
   \newcommand{\FORCE}[2]{\mathtt{FORCE}\ {#1}\ {#2}}
   \newcommand{\FUTURE}[2]{\mathtt{FUTURE}\ {#1}\ {#2}}
   \newcommand{\PROMISE}[1]{\mathtt{PROMISE}\ {#1}}
   \newcommand{\Num}[1]{{#1}^\mathtt{n}}
   \newcommand{\Code}[1]{{#1}^\mathtt{c}}
   \newcommand{\Heap}[1]{{#1}^\mathtt{m}}
   \newcommand{\Task}[1]{{#1}^\mathtt{t}}
   $$
   \frac{
     \Gamma(v) \mapsto w 
   }{
     (\Gamma,\MOV r v;;p) \IReduces (\Gamma[r \mapsto w], p)
   }
   \qquad
   \frac{
     \Gamma(\Reg {r'}) \mapsto {n_1}
     \qquad
     \Gamma(v) \mapsto {n_2}
   }{
     (\Gamma,\ADD {r} {r'} v;;p) \IReduces (\Gamma[r \mapsto (n_1 + n_2)], p)
   }
   $$
   $$
   \frac{
     \Gamma(r) \mapsto 0
   }{
     (\Gamma,\BNZ {r} {v};;p) \IReduces (\Gamma, p)
   }
   \qquad
   \frac{
     \Gamma(\Reg r) \mapsto n
     \qquad
     n \neq 0
     \qquad
     \Gamma(v) \mapsto h
     \qquad
     C(h) = p'
   }{
     (\Gamma,\BNZ {r} {v};;p) \IReduces (\Gamma, p')
   }
   $$
   $$
   \frac{
     \Gamma(v) \mapsto h
     \qquad
     C(h) = p'
   }{
     (\Gamma,\BX {v}) \IReduces (\Gamma, p')
   }
   $$
   %
   *)

  (** ** Memory-level reduction *)

  (**
  %
    \newcommand{\Undef}{\mathtt{undef}}
  %
    The heap represents the main memory and is a map
    from names (memory addresses) into optional words. An undefined word is
      represented by [None], which is typeset as $\Undef$. *)

  Definition heap := MN.t (option word).

  Definition mk_heap := @MN.empty (option word).

  (**
    Next, are reduction rules for instructions that affect a heap [m].
   *)

  Inductive TReduces (m:heap) : task -> heap -> task -> Prop :=
  | t_reduces_i:
    forall t t',
    IReduces t t' ->
    TReduces m t m t'
  | t_reduces_alloc:
    forall p h s r,
    ~ MN.In h m ->
    TReduces m (s,ALLOC r ;; p) (MN.add h None m) (MR.add r (HeapLabel h) s, p)
  | t_reduces_store_reg:
    forall r v p h w s,
    Load s (Reg r) w ->
    Load s v (HeapLabel h) ->
    MN.In h m ->
    TReduces m (s, STR r v;; p)  (MN.add h (Some w) m) (s, p)
  | t_reduces_load_reg:
    forall w s p h r v,
    Load s v (HeapLabel h) ->
    MN.MapsTo h (Some w) m ->
    TReduces m (s, LDR r v;; p) m (MR.add r w s, p).

  (**
   %
    \newcommand{\TReduces}{\rightarrow_{\mathtt{t}}}
   Or in a more familiar typesetting.
   $$
   \frac{
     t \IReduces t'
   }{
     (M, t) \TReduces (M, t')
   }
   \qquad
   \frac{
     h \notin M
   }{
     (M, (\Gamma,\ALLOC r;; p)) \TReduces (M[h \mapsto \Undef], (\Gamma[r \mapsto h], p))
   }
   $$
   $$
   \frac{
     \Gamma(r) \mapsto w
     \qquad
     \Gamma(v) \mapsto h
     \qquad
     h \in M
   }{
     (M, (\Gamma,\STR r v;; p)) \TReduces (M[h \mapsto w], (\Gamma, p))
   }
   \qquad
   \frac{
     \Gamma(v) \mapsto h
     \qquad
     M(h) = w
   }{
     (M, (\Gamma,\LDR r v;; p)) \TReduces (M, (\Gamma[r \mapsto w], p))
   }
   $$
   %
  *)

  (** ** State-level reduction *)

  (**
    The state of an abstract machine corresponds to a heap and a task map.
    Type [taskmap] is a map from names into tasks.
   *)
   
  Definition taskmap := MN.t task.
  Definition mk_taskmap := @MN.empty task.

  (** A state pairs a store and a taskmap. *)

  Definition state := (heap * taskmap) % type.
  Definition get_data := @fst heap taskmap.
  Definition get_tasks := @snd heap taskmap.

  (** The reduction rules at the state level are mainly for the manipulation of
    future-related instructions. *)

  Inductive Reduces : state -> state -> Prop :=
  | reduces_t:
    forall hm hm' tm h t t',
    MN.MapsTo h t tm ->
    TReduces hm t hm' t' ->
    Reduces (hm, tm) (hm, MN.add h t' tm)
  | reduces_future:
    forall r h h' v l hm tm s p p',
    MN.MapsTo h (s, FUTURE r v;; p) tm ->
    Load s v (CodeLabel l) ->
    MN.MapsTo l p' CF ->
    ~ MN.In h' tm ->
    let t1 := (s, p') in
    let t2 := (MR.add r (TaskLabel h') s, p) in
    Reduces (hm, tm) (hm, MN.add h' t1 (MN.add h t2 tm))
  | reduces_force:
    forall r p h h' v v' w hm tm s s',
    MN.MapsTo h (s, FORCE r v;;p) tm ->
    Load s v (TaskLabel h') ->
    MN.MapsTo h' (s', PROMISE v') tm ->
    Load s' v' w ->
    let new_t := (MR.add r w s, p) in
    Reduces (hm, tm) (hm, MN.add h new_t tm).

  (**
   %
    \newcommand{\Reduces}{\rightarrow}
   $$
   \frac{
     T(h) = t
     \qquad
     (M,t) \TReduces (M', t')
   }{
     (M, T) \Reduces (M', T[h \mapsto t'])
   }
   $$
   $$
   \frac{
     T(h) = (\Gamma,\FUTURE r v;; i)
     \qquad
     \Gamma(v) \mapsto l
     \qquad
     C(l) = p'
     \qquad
     h' \notin T
   }{
     (M, T) \TReduces (M, T[h' \mapsto (\Gamma,p')][h \mapsto (\Gamma[r\mapsto {h'}],p)])
   }
   $$
   $$
   \frac{
     T(h) = (\Gamma,\FORCE r v;; p)
     \qquad
     \Gamma(v) \mapsto {h'}
     \qquad
     T(h') = (\Gamma', \PROMISE {v'})
     \qquad
     \Gamma'(v') \mapsto w
   }{
     (M, T) \TReduces (M, T[h \mapsto (\Gamma[r\mapsto w],i)])
   }
   $$
   %
  *)

End Semantics.


(** * Races & Dependencies *)

  Inductive tid :=
  | taskid: name -> tid.

  Definition from_tid t := match t with taskid x => x end.

  Inductive mid :=
  | memid: name -> mid.

  Definition from_mid t := match t with memid x => x end.



Module Races.
  Import Lang.
  Import Semantics.

  (** Holds when some task is reading from a heap reference. *) 

  Inductive Read: state -> tid -> mid -> Prop :=
  | read_def:
    forall h s x v r p tm hm,
    MN.MapsTo h (s, LDR r v;; p) tm ->
    Load s v (HeapLabel x) ->
    MN.In x hm ->
    Read (hm,tm) (taskid h) (memid x).

  (** Holds when some task is writing to a heap reference. *) 

  Inductive Write: state -> tid -> mid -> Prop :=
  | write_def:
    forall h s x v r p tm hm,
    MN.MapsTo h (s, STR r v;; p) tm ->
    Load s v (HeapLabel x) ->
    MN.In x hm ->
    Write (hm,tm) (taskid h) (memid x).

  Inductive Racy (s:state) : Prop :=
  | racy_def:
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
  Import MN.
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
    MR.MapsTo r (HeapLabel y) (get_registers t) ->
    RefersTo s (taskid x) (memid y).


  (** Blocked dependency: a task is blocked on a future in the taskmap. *)

  Inductive Blocked : state -> tid -> tid -> Prop :=
  | blocked_def:
    forall s hm tm r v p x y,
    MapsTo x (s, FORCE r v;; p) tm ->
    Load s v (TaskLabel y) ->
    Blocked (hm, tm) (taskid x) (taskid y).

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
    (forall x y, MN.MapsTo (from_dep x) (from_dep y) m <-> Depends s x y) ->
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
    ~ MN.Empty d ->
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
    apply MN_Facts.add_mapsto_iff in H0.
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
