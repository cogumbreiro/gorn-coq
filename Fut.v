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
  Inductive value :=
  | Var: name -> value
  | Unit
  | Lambda: (name -> exp) -> value
  with exp :=
  | Value:  value -> exp
  | App: exp -> exp -> exp
  | Future: exp -> exp
  | Get: exp -> exp
  | Mkref: exp -> exp
  | Assign: exp -> exp -> exp
  | Deref: exp -> exp.
  
  Definition store := Map_NAME.t value.
  Definition mk_store := @Map_NAME.empty value.
  Definition taskmap := Map_NAME.t exp.
  Definition mk_taskmap h e := (Map_NAME.add h e (@Map_NAME.empty exp)).

  Structure state := mk_state {
    get_data: store;
    get_code: taskmap
  }.

  Definition load (h:name) (e:exp) := mk_state mk_store (mk_taskmap h e).

  Definition set_code (s:state) m :=
    mk_state (get_data s) m.

  Definition set_data (s:state) m :=
  mk_state m (get_code s).
End Lang.

Module Semantics.
  Import Lang.

  Inductive ctx :=
  | CtxAppLeft : ctx -> exp -> ctx
  | CtxAppRight: value -> ctx -> ctx
  | CtxGet: ctx -> ctx
  | CtxMkref: ctx -> ctx
  | CtxAssignLeft: ctx -> exp -> ctx
  | CtxAssignRight: value -> ctx -> ctx
  | CtxDeref: ctx -> ctx
  | CtxHole.

  Fixpoint plug (c:ctx) (e:exp) : exp :=
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

  Import Map_NAME.

  Definition DataIn h s : Prop := Map_NAME.In h (get_data s).

  Definition CodeIn h s : Prop := Map_NAME.In h (get_code s).

  Inductive In h s : Prop :=
    | in_code:
      DataIn h s ->
      In h s
    | in_memory:
      CodeIn h s ->
      In h s.
  
  (** Simple abbreviations of map-related functions. *)

  Definition GetCode (h:name) (e:exp) (s:state) : Prop := (MapsTo h e (get_code s)).
  Definition GetData (h:name) (v:value) (s:state) : Prop := (MapsTo h v (get_data s)).
  Definition put_code (s:state) (h:name) (e:exp) := set_code s (add h e (get_code s)).
  Definition put_data (s:state) (h:name) (v:value) := set_data s (add h v (get_data s)).

  Inductive Reduction (s:state) : state -> Prop :=
  | red_app:
    forall E h x f,
    (* The only thing that can be passed to a lambda is a variable, we can still encode
       with the aid of a future+get. Actually our lambdas do not need variables. *)
    GetCode h (E @ (App (Value (Lambda f)) (Value (Var x)))) s ->
    Reduction s (put_code s h (E @ (f x)))

  | red_future:
    forall E h e h',
    GetCode h (E @ (Future e)) s ->
    ~ In h' s ->
    Reduction s
    (put_code
    (put_code s h (E @ (Value (Var h'))))
    h' e)
  
  | red_get:
    forall E h h' v,
    GetCode h (E @ (Get (Value (Var h')))) s ->
    GetCode h' (Value v) s ->
    Reduction s (put_code s h (E @ (Value v)))
  
  | red_mkref:
    forall h h' E v,
    GetCode h (E @ (Mkref (Value v))) s ->
    ~ In h' s ->
    Reduction s
      (put_code
      (put_data s h' v)
      h (E @ (Value (Var h'))))

  | red_assign:
    forall h h' E v,
    GetCode h (E @ (Assign (Value (Var h')) (Value v))) s ->
    DataIn h' s -> 
    Reduction s
      (put_code
      (put_data s h' v)
      h (E @ (Value Unit)))

  | red_deref:
    forall h h' E v,
    GetCode h (E @ (Deref (Value (Var h')))) s ->
    GetData h' v s ->
    Reduction s
      (put_code s h (E @ (Value v))).

End Semantics.

Module Races.
  Import Lang.
  Import Semantics.

  Inductive Racy (s:state) : Prop :=
    racy_def:
      forall h c x e,
      GetCode h (c @ Deref (Value (Var x))) s ->
      GetCode h (c @ Assign (Value (Var x)) e) s ->
      Racy s.

End Races.

Module FutNotations.
  Import Lang.
  Notation "^" := (Value) (at level 20).
  Notation "$" := (Var) (at level 20).
  Infix "@@" := App (at level 25, left associativity).
  Notation "\\" := (Lambda) (at level 35).
  Notation "!" := (Deref) (at level 20).
  Infix "<~" := Assign (at level 25, left associativity).
  Definition vlam (f:exp->exp) : value := \\ (fun x => f (^ ($ x))).
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
   Reduction s1 (put_code (put_code s1 h1 (c1 @ (^ ($ h2)))) h2 (^ Unit)).
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
  Goal Reduction s2
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
  
  Goal c2 CtxHole @ (^ ($ y)) = ^ (\ (fun x : exp => x <~ Future (Get (! x)))) @@ ^ ($ y).
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

  Goal Reduction s3 (put_code s3 h1 (CtxHole @ (fun x => x <~ Future (Get (! x))) (^ ($ y)) )).
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

  Goal Reduction s4
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
  Print s5.
End Examples.

