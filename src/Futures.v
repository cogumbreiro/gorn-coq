(* begin hide *)

Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetAVL.
Require Import Coq.FSets.FMapAVL.
Require Coq.FSets.FMapFacts.
Require Coq.FSets.FSetProperties.
Require Coq.FSets.FSetBridge.
(*
Require Import Aniceto.Map.
Require Import Aniceto.Set.
*)

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
  Our language is a trivial extension of the $\lambda$-calculus, extended with memory cells
  (whose syntax is inspired by ML) and futures.
  *)

  Inductive f_value :=
  | Var: name -> f_value
  | Unit
  | Lambda: (name -> f_exp) -> f_value
  with f_exp :=
  | Value:  f_value -> f_exp
  | App: f_exp -> f_exp -> f_exp
  | Future: f_exp -> f_exp
  | Get: f_exp -> f_exp
  | Mkref: f_exp -> f_exp
  | Assign: f_exp -> f_exp -> f_exp
  | Deref: f_exp -> f_exp.
  
  (** A store maps from names into values. *)

  Definition store := Map_NAME.t f_value.
  
  (** Let [mk_store] create an empty store. *)

  Definition mk_store := @Map_NAME.empty f_value.

  (** A taskmap ranges from names into expressions. *)

  Definition taskmap := Map_NAME.t f_exp.

  (**
  Function [mk_taskmap] creates a taskmap with a singleton expression [e] labelled
  by name [h]. 
  *)

  Definition mk_taskmap h e := (Map_NAME.add h e (@Map_NAME.empty f_exp)).

  (** A state simply pairs a store and a taskmap. *)

  Structure state := mk_state {
    get_data: store;
    get_code: taskmap
  }.

  (** The [load] function creates the initial state, running expression [e] with name [h]. *)

  Definition load (h:name) (e:f_exp) := mk_state mk_store (mk_taskmap h e).

  (** Functions [set_code] and  [set_data] work as expected. *)

  Definition set_code (s:state) m :=
    mk_state (get_data s) m.

  Definition set_data (s:state) m :=
  mk_state m (get_code s).

(* begin hide*)
End Lang.
(* end hide *)

(* begin hide  *)

Module Semantics.
  Import Lang.

(* end hide *)
  (** * Small-step operational semantics *)

  (**
  We define expression contexts, where we note that
  we do not allow evaluating the body of futures and
  define call-by-value semantics.
  *)

  Inductive ctx :=
  | CtxAppLeft : ctx -> f_exp -> ctx
  | CtxAppRight: f_value -> ctx -> ctx
  | CtxGet: ctx -> ctx
  | CtxMkref: ctx -> ctx
  | CtxAssignLeft: ctx -> f_exp -> ctx
  | CtxAssignRight: f_value -> ctx -> ctx
  | CtxDeref: ctx -> ctx
  | CtxHole.

  (**
  Function [plug], notation $@$, replaces the whole in
  a context with the given expression.
  *)

  Fixpoint plug (c:ctx) (e:f_exp) : f_exp :=
  match c with
  | CtxAppLeft c e' => App (plug c e) e'
  | CtxAppRight v c => App (Value v) (plug c e)
  | CtxGet c => Get (plug c e)
  | CtxMkref c => Mkref (plug c e)
  | CtxAssignLeft c e' => Assign (plug c e) e'
  | CtxAssignRight v c => Assign (Value v) (plug c e)
  | CtxDeref c => Deref (plug c e)
  | CtxHole => e
  end.

  Infix "@" := plug (no associativity, at level 60).

  (* begin hide *)

  Import Map_NAME.

  (* end hide *)

  (** We define two predicates to inquire if a name is labelling some data or labelling some
  code. *)

  Definition DataIn h s : Prop := Map_NAME.In h (get_data s).

  Definition CodeIn h s : Prop := Map_NAME.In h (get_code s).

  (**
  We also define a predicate [In] that holds if the given name  is  labelling some
  code or some data.
  *)

  Inductive In h s : Prop :=
    | in_code:
      DataIn h s ->
      In h s
    | in_memory:
      CodeIn h s ->
      In h s.
  
  (**
  We define the predicate and function to get/put some pair label-expression in
  the given code/data of the state.
  *)

  Definition GetCode (h:name) (e:f_exp) (s:state) : Prop := (MapsTo h e (get_code s)).
  Definition put_code (s:state) (h:name) (e:f_exp) := set_code s (add h e (get_code s)).

  Definition GetData (h:name) (v:f_value) (s:state) : Prop := (MapsTo h v (get_data s)).
  Definition put_data (s:state) (h:name) (v:f_value) := set_data s (add h v (get_data s)).

  (**
  Next, we define the operational semantics of our language.
  *)

  Inductive Reduces (s:state) : state -> Prop :=
  | red_app:
    forall E h x f,
    GetCode h (E @ (App (Value (Lambda f)) (Value (Var x)))) s ->
    Reduces s (put_code s h (E @ (f x)))

  | red_future:
    forall E h e h',
    GetCode h (E @ (Future e)) s ->
    ~ In h' s ->
    Reduces s
    (put_code
    (put_code s h (E @ (Value (Var h'))))
                h' e)
  
  | red_get:
    forall E h h' v,
    GetCode h (E @ (Get (Value (Var h')))) s ->
    GetCode h' (Value v) s ->
    Reduces s (put_code s h (E @ (Value v)))
  
  | red_mkref:
    forall h h' E v,
    GetCode h (E @ (Mkref (Value v))) s ->
    ~ In h' s ->
    Reduces s
      (put_code
      (put_data s h' v)
      h (E @ (Value (Var h'))))

  | red_assign:
    forall h h' E v,
    GetCode h (E @ (Assign (Value (Var h')) (Value v))) s ->
    DataIn h' s -> 
    Reduces s
      (put_code
      (put_data s h' v)
      h (E @ (Value Unit)))

  | red_deref:
    forall h h' E v,
    GetCode h (E @ (Deref (Value (Var h')))) s ->
    GetData h' v s ->
    Reduces s (put_code s h (E @ (Value v))).

(* begin hide *)
End Semantics.

Module Typesystem.
  Import Lang.

(* end  hide *)
(** printing Gamma $\Gamma$ *)
(** *  Type system *)

  Inductive f_type :=
    | TUnit
    | TArrow : f_type -> f_type -> f_type
    | TRef : f_type -> f_type
    | TThr : f_type -> f_type.

  Definition typing := Map_NAME.t f_type.

  (** Typing rules for values: *)

  Inductive VCheck (Gamma:typing) : f_value -> f_type -> Prop :=
    | v_check_var:
      forall x t,
      Map_NAME.MapsTo x t Gamma ->
      VCheck Gamma (Var x) t

    | v_check_unit:
      VCheck Gamma Unit TUnit

    | v_check_lambda:
      forall x t1 t2 f,
      ECheck (Map_NAME.add x t1 Gamma) (f x) t2 ->
      VCheck Gamma (Lambda f) (TArrow t1 t2)

  (** Typing rules for expressions: *)

  with ECheck (Gamma:typing) : f_exp -> f_type -> Prop :=
    | e_check_value:
      forall v t,
      VCheck Gamma v t ->
      ECheck Gamma (Value v) t

    | e_check_app:
      forall e1 e2 t1 t2,
      ECheck Gamma e1 (TArrow t1 t2) ->
      ECheck Gamma e2 t1 ->
      ECheck Gamma (App e1 e2) t2
    
    | e_check_mkref:
      forall e t,
      ECheck Gamma e t ->
      ECheck Gamma (Mkref e) (TRef t)

    | e_check_deref:
      forall  e t,
      ECheck Gamma e (TRef t) ->
      ECheck Gamma (Deref e) t

    | e_check_assign:
      forall e1 e2 t,
      ECheck Gamma e1 (TRef t) ->
      ECheck Gamma e2 t ->
      ECheck Gamma (Assign e1 e2) TUnit

    | e_check_future:
      forall e t,
      ECheck Gamma e t ->
      ECheck Gamma (Future e) (TThr t)
   
    | e_check_get:
      forall e t,
      ECheck Gamma e (TRef t) ->
      ECheck Gamma e t.


  (** Typing rules for code: *)

  Inductive CCheck (Gamma:typing) (c:taskmap) : Prop :=
    c_check_def:
      (forall x e, Map_NAME.MapsTo x e c -> exists t, ECheck Gamma e (TThr t)) ->
      CCheck Gamma c.

  (** Typing rules for data: *)

  Inductive DCheck (Gamma:typing) (d:store) : Prop :=
    d_check_def:
      (forall x v, Map_NAME.MapsTo x v d -> exists t, VCheck Gamma v (TRef t)) ->
      DCheck Gamma d.

  (** Typing rules for states: *)

  Inductive SCheck (Gamma:typing) (s:state) : Prop :=
    s_check_def:
      CCheck Gamma (get_code s) ->
      DCheck Gamma (get_data s) ->
      SCheck Gamma s.

(** * Races & Dependencies *)

(* begin hide *)

End Typesystem.

Module Races.
  Import Lang.
  Import Semantics.

(* end hide *)

  Inductive Racy (s:state) : Prop :=
    racy_def:
      forall h c x e,
      GetCode h (c @ Deref (Value (Var x))) s ->
      GetCode h (c @ Assign (Value (Var x)) e) s ->
      Racy s.

(* begin hide *)
End Races.

Module Dependencies.
  Import Map_NAME.
  Import Lang.
  Import Semantics.

(* end hide *)

  (** Points-to dependency: a variable points to another variable in the store. *)

  Inductive PointsTo d x y : Prop :=
    points_to_def:
      MapsTo x (Var y) d ->
      PointsTo d x y.

  (** Blocked dependency: a task is blocked on a future in the taskmap. *)

  Inductive Blocked c x y : Prop :=
    blocked_def:
      forall C,
      MapsTo x (C @ Get (Value (Var y))) c ->
      Blocked c x y.

  (** Dependencies between two names in a state wraps up blocked and points-to
     dependencies. *)

  Inductive Dep s (x y:name) : Prop :=
    | dep_points_to:
      PointsTo (get_data s) x y ->
      Dep s x y
    | dep_blocked:
      Blocked (get_code s) x y ->
      Dep s x y.

  Require Import Coq.Relations.Relation_Operators.


  Definition Trans_Blocked c := clos_trans _ (Blocked c).

  (** A deadlocked state has a cycle in the [Trans_Blocked] relation. *)

  Definition Deadlocked s := reflexive _ (Trans_Blocked (get_code s)).

  (** Defines the [Depends] relation as the transitive closure of [Dep]. *)

  Definition Depends s := clos_trans _ (Dep s).

  (** The relation [Trans_Blocked] is the transitive closure of [Blocked]. *) 

  Definition Tainted s := reflexive _ (Depends s).

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
    unfold Deadlocked, Tainted, Trans_Blocked, reflexive, Depends in *.
    eauto using clos_trans_impl, dep_blocked.
  Qed.

(* begin hide *)

End Dependencies.


Module Deadlocks.
  Import Semantics.
  Import Races.
  Import Dependencies.

(* end hide *)

  (** Tainted states are introduced by states. *)

  Axiom races_impl_tainted:
    forall s1 s2,
    Reduces s1 s2 ->
    ~ Tainted s1 ->
    Tainted s2 ->
    Racy s1.
  (* TODO *)

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


(* --- examples ---- *)

Module FutNotations.
  Import Lang.
  Notation "^" := (Value) (at level 20).
  Notation "$" := (Var) (at level 20).
  Infix "@@" := App (at level 25, left associativity).
  Notation "\\" := (Lambda) (at level 35).
  Notation "!" := (Deref) (at level 20).
  Infix "<~" := Assign (at level 25, left associativity).
  Definition vlam (f:f_exp->f_exp) : f_value := \\ (fun x => f (^ ($ x))).
  Notation "\" := vlam (at level 30).
  Definition seq e e' := ((^ (\ (fun x => e'))) @@ e).
  Infix ";" := seq (at level 25, left associativity).
  Import Map_NAME.
  Notation "y %"  := (add y) (at level 45, left associativity). 
  Notation ":0" := (empty _).
End FutNotations.

Module Examples.
  Import Lang.
  Import Semantics.
  Import Map_NAME.
  Import FutNotations.
  Definition vlet e f := (^ (\ f)) @@ e.

  Example example1 :=
     vlet (Mkref (Future (^ Unit)))
     (fun x => x <~ (Future (Get (! x)))).

  Eval compute in example1.
  Let c2 := CtxAppRight (vlam (fun x =>
       x <~ (Future (Get (! x))))).
  Let c1 := c2 (CtxMkref CtxHole).
  Goal c1 @ (Future (^ Unit)) = example1.
    auto.
  Qed.
  Let h1 := 0.
  Let h2 := 1.
  Let s1 := load h1 example1.
  (* simplifies the definitions *)
  Ltac f_simpl := unfold GetCode, get_code, load, mk_taskmap, GetData, get_data, seq, vlet, vlam, DataIn, CodeIn in *.
  Goal
   Reduces s1 (put_code (put_code s1 h1 (c1 @ (^ ($ h2)))) h2 (^ Unit)).
  Proof.
    unfold s1.
    f_simpl.
    apply red_future; f_simpl.
    - auto using add_1.
    - unfold not.
      intros.
      inversion H; f_simpl.
      + apply Map_NAME_Facts.empty_in_iff in H0.
        assumption.
      + apply Map_NAME_Facts.add_in_iff in H0.
        destruct H0.
        * inversion H0.
        * apply Map_NAME_Facts.empty_in_iff in H0.
          assumption.
  Qed.

  Let y := 2.
  Let s2 := (put_code (load h1 (c2 CtxHole @ (Mkref (^ ($ h2))))) h2 (^ Unit)).
  Goal Reduces s2
    (put_code
      (put_data s2 y ($ h2))
      h1 (c2 CtxHole @ ^ ($ y))).
  Proof.
    unfold s2; f_simpl.
    apply red_mkref; f_simpl; simpl.
    - auto using add_1, add_2 with *.
    - intuition; f_simpl.
      + apply Map_NAME_Facts.empty_in_iff in H0.
        assumption.
      + simpl in *.
        apply Map_NAME_Facts.add_in_iff in H0.
        destruct H0.
        * inversion H.
        * apply Map_NAME_Facts.add_in_iff in H.
          destruct H.
          { inversion H. }
          apply Map_NAME_Facts.empty_in_iff in H.
          assumption.
  Qed.
  
  Goal c2 CtxHole @ (^ ($ y)) = ^ (\ (fun x : f_exp => x <~ Future (Get (! x)))) @@ ^ ($ y).
    auto.
  Qed.

  Let s3 :=
    mk_state
      (y % ($ h2) :0)
      (h1 % ((^)
     (\\ (fun x => ^ ($ x) <~ Future (Get (! (^ ($ x)))))) @@ ^ ($ y))
       (h2 % (^ Unit) :0)).

  (* Just to ensure we wrote the term correctly: we compare the data on the reduction above
     with state s3 *)
  Goal Map_NAME_Props.to_list (get_data (put_code
      (put_data s2 y ($ h2))
      h1 (c2 CtxHole @ ^ ($ y)))) = Map_NAME_Props.to_list (get_data s3).
    auto.
  Qed.
  (* We do the same for the code section *)
  Goal Map_NAME_Props.to_list (get_code (put_code
      (put_data s2 y ($ h2))
      h1 (c2 CtxHole @ ^ ($ y)))) = Map_NAME_Props.to_list (get_code s3).
    auto.
  Qed.

  Goal Reduces s3 (put_code s3 h1 (CtxHole @ (fun x => x <~ Future (Get (! x))) (^ ($ y)) )).
    unfold s3.
    simpl in *.
    apply (@red_app _ CtxHole _ _ (
      fun x => (
        (^ ($ x)) <~ (Future (Get (! (^ ($ x))))))
      )).
    f_simpl.
    simpl.
    apply add_1; auto.
  Qed.

  Let c3 := CtxAssignRight ($ y) CtxHole.
  Let s4 :=
    mk_state
      (y % ($ h2) :0)
      (h1 % (c3 @ Future (Get (! (^ ($ y)))))
       (h2 % (^ Unit) :0)).
  Let h3 := 3.

  Goal Reduces s4
    (put_code (put_code s4 h1 (c3 @ ^ ($ h3))) h3
       (Get (! (^ ($ y))))).
    simpl.
    apply (@red_future s4 c3 h1 (Get (! (^ ($ y)))) h3).
    - f_simpl.
      simpl.
      auto using add_1.
    - intuition.
      + unfold s4 in *.
        f_simpl.
        simpl in *.
        apply Map_NAME_Facts.add_in_iff in H0.
        destruct H0.
        inversion H.
        apply Map_NAME_Facts.empty_in_iff in H.
        assumption.
      + unfold s4 in *; f_simpl.
        simpl in *.
        apply Map_NAME_Facts.add_in_iff in H0.
        destruct H0.
        inversion H.
        apply Map_NAME_Facts.add_in_iff in H.
        destruct H.
        inversion H.
        apply Map_NAME_Facts.empty_in_iff in H.
        assumption.
  Qed.

  Let s5 :=
    mk_state (y  %  ($ h2) :0)
             (h1 % ((^ ($ y)) <~ (^ ($ h3)))
                (h2 % (^ Unit) 
                  (h3 % (Get (! (^ ($ y)))) :0)
                 )
              ).
End Examples.

(* end hide *)