Require Import Coq.Lists.List.
Require Import Aniceto.Graphs.Graph.
Require Import Aniceto.Graphs.FGraph.
Require Import Aniceto.Graphs.DAG.
Require Import Omega.

Require CG.
Require Import SafeJoins.
Require Import Tid.
Require Import Node.

Require Import Coq.Structures.OrderedTypeEx.
Module MN := FMapAVL.Make Nat_as_OT.
Module MN_Facts := FMapFacts.Facts MN.
Module MN_Props := FMapFacts.Properties MN.
Require Import Aniceto.Map.
Module MN_Extra := MapUtil MN.

Module Events.

  (** Reduces the known-set interpreting events of type [CG.event]. *)

  Section Defs.
    Notation known_set := (list (tid * tid)).

    Inductive SJ: CG.trace -> known_set -> Prop :=
    | sj_nil:
      SJ nil nil
    | sj_init:
      forall k x t,
      SJ t k ->
      SJ ((x, CG.INIT)::t) k
    | sj_fork:
      forall k k' x y t,
      SJ t k ->
      SafeJoins.CheckOp k {| op_t := FORK; op_src := x; op_dst := y |} k' ->
      SJ ((x, CG.FORK y)::t) k'
    | sj_join:
      forall k k' x y t,
      SJ t k ->
      SafeJoins.CheckOp k {| op_t := JOIN; op_src := x; op_dst := y |} k' ->
      SJ ((x, CG.JOIN y)::t) k'
    | sj_continue:
      forall k x t,
      SJ t k ->
      SJ ((x, CG.CONTINUE)::t) k.

  End Defs.
(*
  Ltac simpl_red :=
  repeat match goal with
  | [ H : Reduces _ (_, CG.JOIN _) _ |- _ ] =>
     inversion H; subst; clear H;
     match goal with
     | [ H1 : SafeJoins.CheckOp _ {| op_t := JOIN; op_src := _; op_dst := _ |} _ |- _ ] =>
       inversion H1; subst; clear H1
     end
  | [ H: Reduces _ (_, CG.CONTINUE) _ |- _ ] =>
    inversion H; subst; clear H
  | [ H: Reduces _ (_, CG.INIT) _ |- _ ] =>
    inversion H; subst; clear H
  | [ H : Reduces _ (_, CG.FORK _) _ |- _ ] =>
     inversion H; subst; clear H;
     match goal with
     | [ H1 : SafeJoins.CheckOp _ {| op_t := FORK; op_src := _; op_dst := _ |} _ |- _ ] =>
       inversion H1; subst; clear H1
     end
  end.
*)
End Events.

Section Props.

  Notation known_set := (list (tid * tid)).

  Inductive command :=
  | Cons: tid -> node -> command
  | Copy : node -> command
  | Append: node -> node -> command
  | Nil: command.

  Definition cg_safe_joins := list command.

  Inductive CanJoin : node -> tid -> cg_safe_joins -> Prop :=
  | can_join_cons:
    forall l n c x,
    CanJoin n x l ->
    CanJoin n x (c :: l)
  | can_join_eq:
    forall l n x,
    CanJoin (fresh l) x (Cons x n::l)
  | can_join_neq:
    forall l y n x,
    CanJoin n x l ->
    x <> y ->
    CanJoin (fresh l) x (Cons y n :: l)
  | can_join_copy:
    forall n l x,
    CanJoin n x l ->
    CanJoin (fresh l) x (Copy n :: l)
  | can_join_append_left:
    forall x n' l n,
    CanJoin n x l ->
    CanJoin (fresh l) x (Append n n' :: l)
  | can_join_append_right:
    forall n' l n x,
    CanJoin n' x l ->
    CanJoin (fresh l) x (Append n n' :: l).

  Inductive Free x (l:cg_safe_joins) : Prop :=
  | free_def:
    forall n,
    List.In (Cons x n) l ->
    Free x l.

  Inductive Knows (vs:list tid) (sj:cg_safe_joins): tid * tid -> Prop :=
  | knows_def:
    forall x y nx,
    MapsTo x nx vs ->
    CanJoin nx y sj ->
    Knows vs sj (x, y).

  Definition EdgeToKnows vs sj k :=
    forall p,
    List.In p k ->
    Knows vs sj p.

  Definition KnowsToEdge vs sj k :=
    forall p,
    Knows vs sj p ->
    List.In p k.

  Definition FreeInGraph vs sj :=
    forall x,
    Free x sj ->
    List.In x vs.
End Props.

  Inductive SJ : CG.trace -> CG.computation_graph -> cg_safe_joins -> Prop :=

  | sj_nil:
    SJ nil (nil, nil) nil

  | sj_init:
    forall x cg cg' t sj,
    SJ t cg sj ->
    CG.CG ((x, CG.INIT)::t) cg' ->
    SJ ((x, CG.INIT)::t) cg' (Nil::sj)

  (**
    Case Fork:
    
    x -- fork --> y
     \
      `-- continue --> x'
  
    We know that `x` is connected to y through a `fork` edge
    and that `x` is connected to `x'` through a `continue` edge.
    Let `ty` be the name of task associated with node `y`.
    
    The result is:

     - x' is defined as `Cons ty x`, which means that the names of `x'` are defined as 
       the names from `x` and also `ty`.
      
     - y is defined as `Copy x` which means that it contains the same names as in `x`.
   *)

  | sj_fork:
    forall x y x' ty vs es a b t cg sj,
    SJ t cg sj ->
    CG.CG ((a, CG.FORK b)::t) (ty::vs, CG.F (x,y)::CG.C (x,x')::es) ->
    SJ ((a, CG.FORK b)::t) (ty::vs, CG.F (x,y)::CG.C (x,x')::es) (Copy x::Cons ty x::sj)

  | sj_join:
    forall x y x' ty vs es a b t sj cg,
    SJ t cg sj ->
    CG.CG ((a, CG.JOIN b)::t) (vs, CG.J (y,x') :: CG.C (x,x')::es) ->
    MapsTo ty y vs ->
    CanJoin x ty sj -> (* check: ty \in x *)
    SJ ((a, CG.JOIN b)::t) (vs, CG.J (y,x') :: CG.C (x,x')::es) (Append x y :: sj)

  | sj_continue:
    forall x x' a es vs sj t cg,
    SJ t cg sj ->
    CG.CG ((a, CG.CONTINUE)::t) (vs, CG.C (x,x')::es) ->
    SJ ((a, CG.CONTINUE)::t) (vs, CG.C (x,x')::es) (Copy x :: sj).
(*
  Ltac simpl_red :=
  repeat match goal with
  | [ H : Reduces _ _ ?cg _, H0 : CG.Reduces _ (_, CG.FORK _) ?cg |- _ ] =>
    CG.simpl_red; inversion H; subst; clear H
  | [ H : Reduces _ _ ?cg _, H0 : CG.Reduces _ (_, CG.JOIN _) ?cg |- _ ] =>
    inversion H0; subst; clear H0;
    match goal with
    | [ H1: CG.Reduces _ (_, CG.CONTINUE) _ |- _ ] => inversion H1; subst; clear H1
    end;
    inversion H; subst; clear H;
    simpl_node
  | [ H : Reduces _ _ ?cg _, H0 : CG.Reduces _ (_, CG.CONTINUE) ?cg |- _ ] =>
    CG.simpl_red; inversion H; subst; clear H
  | [ H : Reduces _ (_, CG.INIT) ?cg _, H0 : CG.Reduces _ (_, CG.INIT) ?cg |- _ ] =>
    CG.simpl_red; inversion H; subst; clear H
  end.
*)

Section SJ_TO_CG.
  Lemma sj_to_cg:
    forall t cg sj,
    SJ t cg sj ->
    CG.CG t cg.
  Proof.
    intros.
    inversion H; subst; auto using CG.cg_nil.
  Qed.

  Lemma sj_cg_fun:
    forall t cg1 cg2 sj,
    SJ t cg1 sj ->
    CG.CG t cg2 ->
    cg1 = cg2.
  Proof.
    eauto using sj_to_cg, CG.cg_fun.
  Qed.
End SJ_TO_CG.

  Ltac simpl_sj :=
  repeat match goal with
  | [ H1 : SJ ?t ?cg1 _, H2: CG.CG ?t ?cg2 |- _ ] =>
    assert (cg1 = cg2) by eauto using sj_cg_fun; subst;
    clear H2
  end.

  Ltac simpl_red :=
    CG.simpl_red;
    try simpl_sj.

Section LengthPreserves.

  (* -------------------------------------------------- *)

  Lemma sj_to_length:
    forall t cg sj,
    SJ t cg sj ->
    length (fst cg) = length sj.
  Proof.
    induction t; intros; inversion H; subst; clear H; simpl; auto;
    simpl_red;
    try (inversion H5; subst; simpl_node; clear H5);
    apply IHt in H2; simpl; auto with *.
  Qed.

  Lemma sj_to_length_0:
    forall t vs es sj,
    SJ t (vs, es) sj ->
    length vs = length sj.
  Proof.
    intros.
    assert (length (fst (vs, es)) = length sj) by eauto using sj_to_length.
    simpl in *.
    assumption.
  Qed.

End LengthPreserves.

Section FreeInGraph.

  (* -------------------------------------------------- *)

  Lemma sj_to_free_in_graph:
    forall t cg sj,
    SJ t cg sj ->
    FreeInGraph (fst cg) sj.
  Proof.
    induction t; intros. {
      inversion H; subst.
      unfold FreeInGraph; simpl; intros.
      inversion H0.
      inversion H1.
    }
    inversion H; subst; clear H; simpl_red; simpl in *;
    apply IHt in H2; simpl in *; unfold FreeInGraph in *; intros;
    inversion H; subst; clear H;
    inversion H0; subst; clear H0;
    eauto using in_cons, free_def;
    inversion H; subst; clear H.
    - inversion H0; subst; clear H0.
      auto using in_eq.
    - eauto using in_cons, free_def.
  Qed.

  Lemma sj_free_in_nodes:
    forall t vs es sj x,
    SJ t (vs, es) sj ->
    Free x sj ->
    List.In x vs.
  Proof.
    intros.
    assert (Hf: FreeInGraph (fst (vs, es)) sj) by
    eauto using sj_to_free_in_graph.
    auto.
  Qed.

End FreeInGraph.

Section ESafeJoins.

  Let free_cons:
    forall x sj c,
    Free x sj ->
    Free x (c::sj).
  Proof.
    intros.
    inversion H.
    eauto using List.in_cons, free_def.
  Qed.

  Let free_eq:
    forall x n sj,
    Free x (Cons x n :: sj).
  Proof.
    eauto using free_def, List.in_eq.
  Qed.

  Lemma can_join_to_free:
    forall sj x n ,
    CanJoin n x sj ->
    Free x sj.
  Proof.
    induction sj; intros. {
      inversion H.
    }
    inversion H; subst; clear H; eauto.
  Qed.

  Lemma can_join_absurd_lt:
    forall sj n b,
    NODE.lt (fresh sj) n ->
    ~ CanJoin n b sj.
  Proof.
    unfold NODE.lt, fresh, not; intros.
    induction H0; simpl in *; auto with *.
  Qed.

  Let can_join_lt_fresh:
    forall sj n b,
    CanJoin n b sj ->
    NODE.lt n (fresh sj).
  Proof.
    intros.
    unfold NODE.lt, fresh.
    induction H; simpl in *; auto with *.
  Qed.

  Lemma can_join_absurd_fresh:
    forall sj b,
    ~ CanJoin (fresh sj) b sj.
  Proof.
    intros.
    unfold not; intros.
    apply can_join_lt_fresh in H.
    unfold NODE.lt, fresh, not in *.
    omega.
  Qed.

  Lemma can_join_lt:
    forall x n sj c,
    NODE.lt n (fresh sj) ->
    CanJoin n x (c :: sj) ->
    CanJoin n x sj.
  Proof.
    intros.
    inversion H0; subst; try apply Lt.lt_irrefl in H; auto; contradiction.
  Qed.

  Lemma can_join_inv_cons_1:
    forall sj x y n,
    CanJoin (fresh sj) x (Cons y n :: sj) ->
    x = y \/ (CanJoin n x sj /\ x <> y).
  Proof.
    intros.
    inversion H; clear H.
    - subst; apply can_join_absurd_fresh in H3; contradiction.
    - intuition.
    - subst.
      intuition.
  Qed.

  Lemma can_join_inv_cons_2:
    forall n x y sj,
    CanJoin n x (Cons y n :: sj) ->
    (x = y /\ CanJoin n y sj) \/ (x <> y /\ CanJoin n x sj) \/ (x = y /\ n = fresh sj).
  Proof.
    intros.
    destruct (tid_eq_dec x y);
    inversion H; subst; clear H; auto.
  Qed.

  Lemma can_join_inv_append:
    forall x nx ny sj,
    CanJoin (fresh sj) x (Append nx ny :: sj) ->
    CanJoin nx x sj \/ CanJoin ny x sj.
  Proof.
    intros.
    inversion H; clear H.
    - subst; apply can_join_absurd_fresh in H3; contradiction.
    - intuition.
    - intuition.
  Qed.

  Lemma can_join_inv_copy_1:
    forall sj x n,
    CanJoin (fresh sj) x (Copy n :: sj) ->
    CanJoin n x sj.
  Proof.
    intros.
    inversion H; clear H.
    - subst; apply can_join_absurd_fresh in H3; contradiction.
    - auto.
  Qed.

  Lemma can_join_inv_copy_2:
    forall n x sj,
    CanJoin n x (Copy n :: sj) ->
    CanJoin n x sj.
  Proof.
    intros.
    inversion H; subst; clear H; assumption.
  Qed.

  Lemma knows_cons:
    forall vs sj a b c x,
    Knows vs sj (a, b) ->
    x <> a ->
    Knows (x :: vs) (c :: sj) (a, b).
  Proof.
    intros.
    inversion H; subst; clear H.
    simpl in *.
    eauto using knows_def, can_join_cons, maps_to_cons.
  Qed.

  Lemma knows_cons_neq:
    forall x y z n sj vs,
    x <> y ->
    y <> z ->
    MapsTo x n vs ->
    Knows vs sj (x, z) ->
    length vs = length sj ->
    Knows (x :: vs) (Cons y n :: sj) (x, z).
  Proof.
    intros.
    inversion_clear H2.
    simpl_node.
    apply knows_def with (nx:=fresh vs).
    - auto using maps_to_eq.
    - apply maps_to_length_rw in H3.
      rewrite H3.
      apply can_join_neq; auto.
  Qed.

  Lemma knows_neq:
    forall vs sj a b x c,
    Knows vs sj (a, b) ->
    a <> x ->
    Knows (x :: vs) (c :: sj) (a, b).
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using knows_def, maps_to_cons, can_join_cons.
  Qed.

  Lemma knows_eq:
    forall a vs b n sj,
    length vs = length sj ->
    Knows (a :: vs) (Cons b n :: sj) (a, b).
  Proof.
    intros.
    apply knows_def with (nx:=fresh vs).
    - auto using maps_to_eq.
    - apply maps_to_length_rw in H.
      rewrite H.
      apply can_join_eq.
  Qed.

  Lemma knows_copy:
    forall vs sj x y z n,
    length vs = length sj ->
    MapsTo x n vs ->
    Knows vs sj (x, y) ->
    Knows (z :: vs) (Copy n :: sj) (z, y).
  Proof.
    intros.
    inversion H1; subst; clear H1.
    apply knows_def with (nx:=fresh vs).
    - auto using maps_to_eq.
    - apply maps_to_length_rw in H.
      rewrite H.
      apply can_join_copy.
      assert (nx = n) by eauto using maps_to_fun_2; subst.
      assumption.
  Qed.

  Lemma knows_append_right:
    forall y ny nx x vs b sj,
    length vs = length sj ->
    MapsTo y ny vs ->
    Knows vs sj (y, b) ->
    Knows (x :: vs) (Append nx ny :: sj) (x, b).
  Proof.
    intros.
    inversion H1; subst; clear H1.
    assert (nx0 = ny) by eauto using maps_to_fun_2; subst.
    apply knows_def with (nx:=fresh vs).
    - auto using maps_to_eq.
    - apply maps_to_length_rw in H.
      rewrite H.
      apply can_join_append_right.
      assumption.
  Qed.

  Lemma knows_append_left:
    forall ny nx x vs b sj,
    length vs = length sj ->
    MapsTo x nx vs ->
    Knows vs sj (x, b) ->
    Knows (x :: vs) (Append nx ny :: sj) (x, b).
  Proof.
    intros.
    inversion H1; subst; clear H1.
    assert (nx0 = nx) by eauto using maps_to_fun_2; subst.
    apply knows_def with (nx:=fresh vs).
    - auto using maps_to_eq.
    - apply maps_to_length_rw in H.
      rewrite H.
      apply can_join_append_left.
      assumption.
  Qed.

  Lemma knows_to_free:
    forall sj vs x y,
    Knows vs sj (x, y) ->
    Free y sj.
  Proof.
    induction sj; intros; inversion_clear H. {
      inversion H1.
    }
    inversion_clear H1; eauto using free_cons, knows_def, can_join_to_free.
  Qed.

  Lemma knows_to_in_l:
    forall x y vs sj,
    Knows vs sj (x, y) ->
    List.In x vs.
  Proof.
    intros.
    inversion H; subst.
    eauto using maps_to_to_in.
  Qed.

  Lemma knows_to_in_r:
    forall x y vs sj t es,
    SJ t (vs, es) sj ->
    Knows vs sj (x, y) ->
    List.In y vs.
  Proof.
    intros.
    eapply sj_free_in_nodes; eauto using knows_to_free.
  Qed.

  Let knows_continue:
    forall sj vs a b x nx,
    MapsTo x nx vs ->
    Knows vs sj (a, b) ->
    length sj = length vs ->
    Knows (x :: vs) (Copy nx :: sj) (a, b).
  Proof.
    intros.
    destruct (tid_eq_dec a x). {
      subst.
      eauto using knows_copy.
    }
    auto using knows_neq.
  Qed.

  Lemma knows_fork_1:
    forall vs es sj x y z n t,
    SJ t (vs, es) sj ->
    ~ List.In y vs ->
    MapsTo x n vs ->
    Knows vs sj (x, z) ->
    x <> y ->
    Knows (x :: vs) (Cons y n :: sj) (x, z).
  Proof.
    intros.
    apply knows_cons_neq; auto; eauto using sj_to_length_0.
    unfold not; intros; subst.
    eapply knows_to_in_r in H2; eauto.
  Qed.

  Lemma knows_fork_2:
    forall x y z vs n sj t es,
    SJ t (vs, es) sj ->
    ~ List.In z vs ->
    MapsTo x n vs ->
    x <> z ->
    Knows vs sj (x, y) ->
    Knows (z :: x :: vs) (Copy n :: Cons z n :: sj) (z, y).
  Proof.
    intros.
    assert (Knows (x::vs) (Cons z n :: sj) (x, y)) by eauto using knows_fork_1.
    apply knows_def with (nx:=fresh (x::vs)); auto using maps_to_eq.
    assert (R: fresh (x::vs) = fresh (Cons z n :: sj)). {
      apply maps_to_length_rw.
      assert (R: length vs = length sj) by eauto using sj_to_length_0.
      simpl; rewrite R; trivial.
    }
    rewrite R.
    apply can_join_copy.
    apply can_join_cons.
    inversion H3; subst.
    simpl_node.
    assumption.
  Qed.

  Lemma knows_fork_3:
    forall x y vs es sj t n,
    SJ t (vs, es) sj ->
    x <> y ->
    Knows (y :: x :: vs) (Copy n :: Cons y n :: sj) (x, y).
  Proof.
    intros.
    apply knows_cons; auto.
    apply knows_eq; eauto using sj_to_length_0.
  Qed.

  Lemma knows_fork_4:
    forall t vs es sj a b n y x,
    SJ t (vs, es) sj ->
    ~ List.In y vs ->
    MapsTo x n vs ->
    Knows vs sj (a, b) ->
    Knows (y :: x :: vs) (Copy n :: Cons y n :: sj) (a, b).
  Proof.
    intros.
    assert (y <> a). {
      unfold not; intros; subst.
      apply knows_to_in_l in H2.
      contradiction.
    }
    apply knows_cons; auto.
    destruct (tid_eq_dec x a). {
      subst.
      assert (y <> b). {
        unfold not; intros; subst.
        eapply knows_to_in_r in H2; eauto.
      }
      apply knows_cons_neq; eauto using sj_to_length_0.
    }
    apply knows_cons; auto.
  Qed.

  Lemma knows_init:
    forall a b sj vs x,
    ~ List.In x vs ->
    Knows vs sj (a, b) ->
    Knows (x :: vs) (Nil :: sj) (a, b).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    apply knows_def with (nx:=nx).
    - apply maps_to_cons; auto.
      unfold not; intros; subst.
      apply maps_to_to_in in H3.
      contradiction.
    - auto using can_join_cons.
  Qed.

  Lemma knows_inv_init:
    forall x p vs sj,
    length vs = length sj ->
    Knows (x :: vs) (Nil :: sj) p ->
    Knows vs sj p.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    apply maps_to_inv in H1.
    destruct H1 as [(?,?)|(?,mt)].
    - subst.
      apply maps_to_length_rw in H.
      rewrite H in *.
      inversion H2; subst.
      apply can_join_absurd_fresh in H4.
      contradiction.
    - inversion H2; subst; clear H2.
      eauto using knows_def.
  Qed.

  Lemma knows_inv_fork:
    forall vs sj n x y a b,
    length vs = length sj ->
    Knows (y :: x :: vs) (Copy n :: Cons y n :: sj) (a, b) ->
    (a = y /\ CanJoin (fresh (x::vs)) b (Copy n :: Cons y n :: sj)) \/
    (a <> y /\ a = x /\ (CanJoin (fresh vs) b (Copy n :: Cons y n :: sj))) \/
    (a <> y /\ a <> x /\ Knows vs sj (a,b)).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    apply maps_to_inv in H3.
    assert (R: fresh (x::vs) = fresh (Cons y n :: sj)). {
      assert (R: length (x::vs) = length (Cons y n :: sj)). {
        simpl.
        rewrite H.
        trivial.
      }
      auto using maps_to_length_rw.
    }
    destruct H3 as [(?,?)|(?,mt)]. {
      left.
      subst.
      auto.
    }
    right.
    apply maps_to_inv in mt.
    destruct mt as [(?,?)|(?,mt)]. {
      subst.
      auto.
    }
    inversion H4; subst; clear H4. {
      inversion H6; subst; clear H6.
      - right.
        split; auto; split; eauto using knows_def.
      - apply maps_to_length_rw in H.
        rewrite <- H in *.
        simpl_node.
      - apply maps_to_length_rw in H.
        rewrite <- H in *.
        simpl_node.
    }
    rewrite <- R in *.
    rewrite fresh_cons_rw_next in *.
    simpl_node.
  Qed.

  Lemma can_join_to_in:
    forall vs es t sj x n,
    SJ t (vs,es) sj ->
    CanJoin n x sj ->
    List.In x vs.
  Proof.
    eauto using can_join_to_free, sj_free_in_nodes.
  Qed.

  Definition KnowsTrans vs sj :=
    forall x y z,
    Knows vs sj (x, y) ->
    Knows vs sj (y, z) ->
    Knows vs sj (x, z).

  Lemma can_join_inv_cons_3:
    forall n x y sj,
    n <> fresh sj ->
    CanJoin n x (Cons y n :: sj) ->
    CanJoin n x sj.
  Proof.
    intros.
    apply can_join_inv_cons_2 in H0.
    destruct H0 as [(?,?)|[(?,?)|(?,?)]].
    - subst; auto.
    - auto.
    - contradiction.
  Qed.

  Lemma can_join_inv_fork_1:
    forall x y n sj,
    CanJoin (fresh sj) x (Copy n :: Cons y n :: sj) ->
    x = y \/ CanJoin n x sj.
  Proof.
    intros.
    inversion H; subst; clear H. {
      apply can_join_inv_cons_1 in H3.
      destruct H3 as [?|(?,?)]; subst; auto.
    }
    simpl in *.
    omega.
  Qed.

  Lemma knows_append_2:
    forall a b nx ny sj vs x y,
    length vs = length sj ->
    MapsTo x nx vs ->
    Knows vs sj (a, b) ->
    Knows vs sj (x, y) ->
    Knows (x :: vs) (Append nx ny :: sj) (a, b).
  Proof.
    intros.
    destruct (tid_eq_dec x a). {
      subst.
      inversion H1; inversion H2; subst; clear H1 H2.
      simpl_node.
      apply knows_def with (nx:=fresh sj).
      + apply maps_to_length_rw in H.
        rewrite <- H.
        auto using maps_to_eq.
      + auto using can_join_append_left.
    }
    auto using knows_cons.
  Qed.

  Lemma sj_to_edge_to_knows:
    forall t k cg sj,
    Events.SJ t k ->
    SJ t cg sj ->
    EdgeToKnows (fst cg) sj k.
  Proof.
    induction t; intros. {
      inversion H0; subst; clear H0.
      inversion H; subst; clear H.
      unfold EdgeToKnows; simpl; intros.
      contradiction.
    }
    inversion H0; subst; clear H0; simpl_red;
    inversion H;subst; clear H; simpl in *;
    rename sj0 into sj;
    try (rename vs0 into vs);
    try (rename k0 into k_; rename k into k'; rename k_ into k);
    (assert (He: EdgeToKnows (fst (vs, es)) sj k) by auto; simpl in *);
    unfold EdgeToKnows in *; intros;try (apply He in H);
    destruct p as (c,d).
    - apply knows_cons; auto.
      unfold not; intros; subst.
      apply knows_to_in_l in H.
      contradiction.
    - inversion H6; subst; clear H6.
      apply fork_inv_in in H.
      destruct H as [(?,?)|[(?,?)|?]]; subst;
      eauto using knows_fork_2, knows_fork_3, knows_fork_4.
    - inversion H7; subst; clear H7.
      apply join_inv_in in H.
      unfold FGraph.Edge in *.
      apply He in H4.
      destruct H as [(?,Hi)|Hi]; subst;
      apply He in Hi; clear He IHt.
      + eapply knows_append_right; eauto using sj_to_length_0.
      + eauto using knows_append_2, sj_to_length_0.
    - destruct (tid_eq_dec a0 c). {
        subst.
        apply knows_def with (nx:=fresh vs); auto using maps_to_eq.
        assert (R: fresh vs = fresh sj). {
          eauto using maps_to_length_rw, sj_to_length_0.
        }
        rewrite R.
        apply can_join_copy.
        inversion H; subst; clear H.
        simpl_node.
        auto.
      }
      auto using knows_cons.
  Qed.

  Lemma sj_edge_to_knows_0:
    forall t k vs es sj p,
    Events.SJ t k ->
    SJ t (vs,es) sj ->
    List.In p k ->
    Knows vs sj p.
  Proof.
    assert (X:= sj_to_edge_to_knows).
    unfold EdgeToKnows in *.
    intros.
    eapply X in H1; eauto.
    simpl in *.
    assumption.
  Qed.

End ESafeJoins.

Section KnowsToEdge.
  (* -------------------------------------------------- *)

  Let nat_absurd_succ:
    forall n,
    n <> S n.
  Proof.
    intros.
    unfold not; intros.
    induction n.
    - inversion H.
    - inversion H; auto.
  Qed.

  Lemma knows_inv_append:
    forall x n1 n2 a b sj vs,
    length vs = length sj ->
    Knows (x :: vs) (Append n1 n2 :: sj) (a,b) ->
    (a = x /\ (CanJoin n1 b sj \/ CanJoin n2 b sj))
    \/
    (a <> x /\ Knows vs sj (a, b)).
  Proof.
    intros.
    apply maps_to_length_rw in H.
    inversion H0; subst; clear H0.
    apply maps_to_inv in H3.
    destruct H3 as [(?,?)|(?,?)]. {
      subst.
      rewrite H in *.
      apply can_join_inv_append in H4.
      intuition.
    }
    inversion H4; subst; clear H4.
    - eauto using knows_def.
    - rewrite <- H in *.
      simpl_node.
    - rewrite <- H in *.
      simpl_node.
  Qed.

  Lemma knows_inv_copy:
    forall x vs sj a b n,
    length vs = length sj ->
    Knows (x :: vs) (Copy n :: sj) (a,b) ->
    (a = x /\ CanJoin n b sj) \/
    (a <> x /\ Knows vs sj (a,b)).
  Proof.
    intros.
    apply maps_to_length_rw in H.
    inversion H0; subst; clear H0.
    apply maps_to_inv in H3.
    destruct H3 as [(?,?)|(?,?)].
    + subst.
      rewrite H in *.
      apply can_join_inv_copy_1 in H4.
      auto.
    + inversion H4; subst; clear H4. {
        eauto using knows_def.
      }
      rewrite <- H in *.
      simpl_node.
  Qed.

  Lemma sj_to_knows_to_edge:
    forall t cg k sj,
    Events.SJ t k ->
    SJ t cg sj ->
    KnowsToEdge (fst cg) sj k.
  Proof.
    induction t; intros. {
      inversion H; subst.
      inversion H0; subst.
      unfold KnowsToEdge; intros.
      inversion H1; subst; simpl in *.
      inversion H2.
    }
    inversion H0; subst; clear H0; simpl_red;
    inversion H;subst; clear H; simpl in *;
    rename sj0 into sj;
    try (rename vs0 into vs);
    try (rename k0 into k_; rename k into k'; rename k_ into k);
    unfold KnowsToEdge in *; intros.
    - apply knows_inv_init in H; eauto using sj_to_length_0.
    - destruct p as (a,b).
      inversion H6; subst; clear H6.
      assert (R: fresh (a0::vs) = fresh (Cons ty x :: sj)). {
        assert (length (a0::vs) = length (Cons ty x :: sj)). {
          simpl.
          erewrite sj_to_length_0; eauto.
        }
        auto using maps_to_length_rw.
      }
      assert (R2: fresh vs = fresh sj) by eauto using sj_to_length_0, maps_to_length_rw.
      apply knows_inv_fork in H; eauto using sj_to_length_0.
      destruct H as [(?,?)|[(?,(?,?))|(?,(?,?))]]; subst.
      + rewrite R in *.
        apply can_join_inv_copy_1 in H0.
        apply can_join_inv_cons_2 in H0.
        destruct H0 as [(?,?)|[(?,?)|(?,?)]]; subst.
        * eapply can_join_to_in in H0; eauto.
          contradiction.
        * eauto using in_fork_2, knows_def.
        * rewrite <- R2 in *.
          simpl_node.
      + rewrite R2 in *.
        apply can_join_inv_fork_1 in H1.
        destruct H1 as [?|?]. {
          subst.
          auto using in_fork_5.
        }
        eauto using in_fork, knows_def.
      + eauto using in_fork.
    - inversion H7; subst; clear H7.
      destruct p as (c,d).
      apply knows_inv_append in H; eauto using sj_to_length_0.
      destruct H as [(?,[?|?])|(?,?)];
      subst; eauto using knows_def, in_join_2, in_join.
    - destruct p as (a,b).
      apply knows_inv_copy in H; eauto using sj_to_length_0.
      destruct H as [(?,?)|(?,?)].
      + subst.
        eauto using knows_def.
      + eauto.
  Qed.

  Lemma sj_to_knows_to_edge_0:
    forall t vs es k sj p,
    Events.SJ t k ->
    SJ t (vs, es) sj ->
    Knows vs sj p ->
    List.In p k.
  Proof.
    intros.
    assert (Hk: KnowsToEdge (fst (vs,es)) sj k)
    by eauto using sj_to_knows_to_edge.
    auto.
  Qed.
End KnowsToEdge.

Section Incl.
  (* ------------------------------------------ *)

  Definition Incl cg sj :=
  forall n1 n2 x,
  List.In (n1, n2) (CG.cg_edges cg) ->
  CanJoin n1 x sj ->
  CanJoin n2 x sj.

  Let in_length_absurd:
    forall vs es n,
    CG.EdgeToNode (vs, es) ->
    ~ List.In (fresh vs, n) (map CG.e_edge es).
  Proof.
    intros.
    intuition.
    assert (Hx:List.In (fresh vs, n) (CG.cg_edges es)) by auto.
    eapply CG.node_lt_length_left in Hx; eauto.
    simpl in Hx.
    unfold NODE.lt in *.
    omega.
  Qed.
(*
  Let incl_fork:
    forall cg cg' sj sj' k k' x n1 n2 a b,
    Incl (snd cg) sj ->
    Events.Reduces k (a, CG.FORK b) k' ->
    CG.Reduces cg (a, CG.FORK b) cg' ->
    Reduces sj (a, CG.FORK b) cg' sj' ->
    List.In (n1, n2) (CG.cg_edges (snd cg')) ->
    CanJoin n1 x sj' ->
    length (fst cg) = length sj ->
    FreeInGraph (fst cg) sj ->
    CG.EdgeToNode cg ->
    CanJoin n2 x sj'.
  Proof.
    intros.
    rename H5 into Heq.
    rename H6 into Hdom.
    rename H7 into Hlt.
    Events.simpl_red; simpl_red; simpl in *.
    assert (Rw: fresh (a::vs) = fresh (Cons b n1 :: sj)). {
      apply maps_to_length_rw.
      simpl; auto.
    }
    apply maps_to_length_rw in Heq.
    destruct H3 as [R|[R|?]]; try (inversion R; subst; clear R).
    - rewrite Rw.
      apply can_join_inv_copy_2 in H4.
      apply can_join_inv_cons_2 in H4; destruct H4 as [(?,?)|[(?,?)|(?,?)]]; subst.
      + auto using can_join_copy, can_join_cons.
      + auto using can_join_copy, can_join_cons.
      + rewrite <- Heq in *.
        apply maps_to_absurd_fresh in H12; contradiction.
    - rewrite Heq.
      apply can_join_inv_copy_2 in H4.
      apply can_join_inv_cons_2 in H4.
      destruct H4 as [(?,?)|[(?,?)|(?,?)]]; subst.
      + auto using can_join_cons, can_join_eq.
      + auto using can_join_cons, can_join_neq.
      + rewrite <- Heq in *.
        apply maps_to_absurd_fresh in H12; contradiction.
    - inversion H4; subst; clear H4. {
        inversion H5; subst; clear H5.
        - eauto using can_join_cons.
        - rewrite <- Heq in *.
          apply in_length_absurd in H0; auto; contradiction.
        - rewrite <- Heq in *.
          apply in_length_absurd in H0; auto; contradiction.
      }
      simpl in *.
      assert (Hx:List.In (fresh (Cons b prev :: sj), n2) (CG.cg_edges es)) by auto.
      eapply CG.node_lt_length_left in Hx; eauto.
      simpl in Hx.
      unfold NODE.lt, fresh in *; simpl in *.
      inversion Heq.
      omega.
  Qed.

  Let incl_join:
    forall cg cg' sj sj' k k' x n1 n2 a b,
    Incl (snd cg) sj ->
    Events.Reduces k (a, CG.JOIN b) k' ->
    CG.Reduces cg (a, CG.JOIN b) cg' ->
    Reduces sj (a, CG.JOIN b) cg' sj' ->
    List.In (n1, n2) (CG.cg_edges (snd cg')) ->
    CanJoin n1 x sj' ->
    length (fst cg) = length sj ->
    FreeInGraph (fst cg) sj ->
    CG.EdgeToNode cg ->
    CanJoin n2 x sj'.
  Proof.
    intros.
    rename H5 into Heq.
    rename H6 into Hdom.
    rename H7 into Hlt.
    Events.simpl_red; simpl_red; simpl in *.
    rename prev into na.
    rename ny into nb.
    apply maps_to_length_rw in Heq.
    destruct H3 as [R|[R|?]]; try (inversion R; subst; clear R).
    - assert (CanJoin n1 x sj). {
        inversion H4; subst; clear H4.
        - assumption.
        - rewrite <- Heq in *.
          apply maps_to_absurd_fresh in H12; contradiction.
        - rewrite <- Heq in *.
          apply maps_to_absurd_fresh in H12; contradiction.
      } clear H4.
      rewrite Heq.
      auto using can_join_append_right.
    - assert (CanJoin n1 x sj). {
        inversion H4; subst; clear H4.
        - assumption.
        - rewrite <- Heq in *.
          apply maps_to_absurd_fresh in H11; contradiction.
        - rewrite <- Heq in *.
          apply maps_to_absurd_fresh in H11; contradiction.
      } clear H4.
      rewrite Heq.
      auto using can_join_append_left.
    - assert (CanJoin n1 x sj). {
        inversion H4; subst; clear H4.
        - assumption.
        - rewrite <- Heq in *.
          apply in_length_absurd in H0; auto; contradiction.
        - rewrite <- Heq in *.
          apply in_length_absurd in H0; auto; contradiction.
      } clear H4.
      eauto using can_join_cons.
  Qed.

  Let incl_continue:
    forall cg cg' sj sj' k k' x n1 n2 a,
    Incl (snd cg) sj ->
    Events.Reduces k (a, CG.CONTINUE) k' ->
    CG.Reduces cg (a, CG.CONTINUE) cg' ->
    Reduces sj (a, CG.CONTINUE) cg' sj' ->
    List.In (n1, n2) (CG.cg_edges (snd cg')) ->
    CanJoin n1 x sj' ->
    length (fst cg) = length sj ->
    FreeInGraph (fst cg) sj ->
    CG.EdgeToNode cg ->
    CanJoin n2 x sj'.
  Proof.
    intros.
    rename H5 into Heq.
    rename H6 into Hdom.
    rename H7 into Hlt.
    Events.simpl_red; simpl_red; simpl in *.
    apply maps_to_length_rw in Heq.
    destruct H3 as [Hx|Hx].
    - inversion Hx; subst; clear Hx.
      rewrite Heq.
      auto using can_join_copy, can_join_inv_copy_2.
    - inversion H4; subst; clear H4. {
        eauto using can_join_cons.
      }
      rewrite <- Heq in *.
      apply in_length_absurd in Hx; auto; contradiction.
  Qed.

  Let incl_init:
    forall cg cg' sj sj' k k' x n1 n2 a,
    Incl (snd cg) sj ->
    Events.Reduces k (a, CG.INIT) k' ->
    CG.Reduces cg (a, CG.INIT) cg' ->
    Reduces sj (a, CG.INIT) cg' sj' ->
    List.In (n1, n2) (CG.cg_edges (snd cg')) ->
    CanJoin n1 x sj' ->
    length (fst cg) = length sj ->
    FreeInGraph (fst cg) sj ->
    CG.EdgeToNode cg ->
    CanJoin n2 x sj'.
  Proof.
    intros.
    Events.simpl_red; simpl_red; simpl in *.
    inversion H4; subst; clear H4.
    eauto using can_join_cons.
  Qed.

  Lemma incl_reduces:
    forall sj cg k sj' cg' k' e,
    Incl (snd cg) sj ->
    Events.Reduces k e k' ->
    CG.Reduces cg e cg' ->
    Reduces sj e cg' sj' ->
    length (fst cg) = length sj ->
    FreeInGraph (fst cg) sj ->
    CG.EdgeToNode cg ->
    Incl (snd cg') sj'.
  Proof.
    intros.
    unfold Incl; intros.
    destruct e as (a, []).
    - eauto.
    - eauto.
    - eauto.
    - eauto.
  Qed.
*)

  Lemma sj_to_incl:
    forall t cg k sj,
    Events.SJ t k ->
    SJ t cg sj ->
    Incl (snd cg) sj.
  Proof.
    induction t; intros. {
      inversion H; subst; clear H.
      inversion H0; subst; clear H0.
      simpl; unfold Incl; intros.
      inversion H.
    }
    inversion H0; subst; clear H0; simpl_red;
    inversion H;subst; clear H; simpl in *;
    rename sj0 into sj;
    try (rename vs0 into vs);
    try (rename k0 into k_; rename k into k'; rename k_ into k);
    unfold Incl in *; intros.
    - inversion H0; subst; clear H0.
      eauto using can_join_cons.
    - inversion H6; subst; clear H6; simpl_node.
      simpl in *.
      assert (R: fresh (a0::vs) = fresh (Cons ty x :: sj)). {
        assert (length (a0::vs) = length (Cons ty x :: sj)). {
          simpl.
          erewrite sj_to_length_0; eauto.
        }
        auto using maps_to_length_rw.
      }
      assert (R2: fresh vs = fresh sj) by eauto using sj_to_length_0, maps_to_length_rw.
      destruct H as [Heq|[Heq|?]];
      try (inversion Heq; subst; clear Heq).
      + rewrite R. apply can_join_copy.
        apply can_join_inv_copy_2 in H0.
        apply can_join_inv_cons_2 in H0.
        destruct H0 as [(?,?)|[(?,?)|(?,?)]]; subst;
        auto using can_join_cons.
        rewrite <- R2 in *.
        simpl_node.
      + rewrite R2.
        apply can_join_cons.
        apply can_join_inv_copy_2 in H0.
        apply can_join_inv_cons_2 in H0.
        destruct H0 as [(?,?)|[(?,?)|(?,?)]]; subst;
        auto using can_join_eq, can_join_neq.
      + inversion H0; subst; clear H0. {
          inversion H7; subst; clear H7.
          - eapply IHt in H6; eauto.
            auto using can_join_cons.
          - rewrite <- R2 in *.
            eapply CG.cg_edge_to_node_l in H; eauto using sj_to_cg.
            simpl_node.
          - rewrite <- R2 in *.
            eapply CG.cg_edge_to_node_l in H; eauto using sj_to_cg.
            simpl_node.
        }
        rewrite <- R in *.
        eapply CG.cg_edge_to_node_l in H; eauto using sj_to_cg.
        simpl_node.
    - simpl in *.
      assert (R: fresh (a0::vs) = fresh (Append x y :: sj)). {
        assert (length (a0::vs) = length (Append x y :: sj)). {
          simpl.
          erewrite sj_to_length_0; eauto.
        }
        auto using maps_to_length_rw.
      }
      assert (R2: fresh vs = fresh sj) by eauto using sj_to_length_0, maps_to_length_rw.
      inversion H7; subst; clear H7.
      destruct H as [He|[He|Hi]];
      try (inversion He; subst; clear He);
      try (rewrite R2).
      + inversion H0; subst; clear H0;
        eauto using can_join_append_right, can_join_append_left.
      + inversion H0; subst; clear H0;
        eauto using can_join_append_right, can_join_append_left.
      + apply can_join_cons.
        inversion H0; subst; clear H0.
        * eauto.
        * rewrite <- R2 in *.
          eapply CG.cg_edge_to_node_l in Hi; eauto using sj_to_cg.
          simpl_node.
        * rewrite <- R2 in *.
          eapply CG.cg_edge_to_node_l in Hi; eauto using sj_to_cg.
          simpl_node.
    - simpl in *.
      assert (R: fresh (a0::vs) = fresh (Copy x :: sj)). {
        assert (length (a0::vs) = length (Copy x :: sj)). {
          simpl.
          erewrite sj_to_length_0; eauto.
        }
        auto using maps_to_length_rw.
      }
      assert (R2: fresh vs = fresh sj) by eauto using sj_to_length_0, maps_to_length_rw.
      destruct H as [He|Hi]. {
        inversion He; subst; clear He.
        rewrite R2.
        auto using can_join_copy, can_join_inv_copy_2.
      }
      inversion H0; subst; clear H0. {
        eauto using can_join_cons.
      }
      rewrite <- R2 in *.
      eapply CG.cg_edge_to_node_l in Hi; eauto using sj_to_cg.
      simpl_node.
  Qed.

  Let hb_edge_in:
    forall cg sj n1 n2 x,
    Incl cg sj ->
    CanJoin n1 x sj ->
    CG.HB_Edge cg (n1, n2) ->
    CanJoin n2 x sj.
  Proof.
    intros.
    rewrite CG.hb_edge_spec in *.
    eauto.
  Qed.

  Let InEdge sj x (e:node*node) := CanJoin (fst e) x sj /\ CanJoin (snd e) x sj.

  Let in_edge:
    forall sj cg a b x,
    Incl cg sj ->
    CG.HB_Edge cg (a, b) ->
    CanJoin a x sj ->
    InEdge sj x (a, b).
  Proof.
    intros.
    unfold InEdge.
    simpl.
    eauto.
  Qed.

  Let wb_in_0:
    forall cg  sj w x a b,
    Incl cg sj ->
    CanJoin a x sj ->
    Walk2 (CG.HB_Edge cg) a b w ->
    Walk2 (InEdge sj x) a b w.
  Proof.
    induction w; intros. {
      apply walk2_nil_inv in H1.
      contradiction.
    }
    inversion H1; subst; clear H1.
    inversion H4; subst; clear H4.
    destruct a as (a, c).
    apply starts_with_eq in H2; symmetry in H2; subst.
    destruct w as [|(c',d)].
    - apply ends_with_eq in H3.
      subst.
      eauto using edge_to_walk2.
    - apply ends_with_inv in H3.
      apply linked_inv in H8; subst.
      apply walk2_cons.
      + eauto using starts_with_def, walk2_def.
      + eauto.
  Qed.

  Lemma incl_hb:
    forall cg sj n1 n2 x,
    Incl cg sj ->
    CanJoin n1 x sj ->
    CG.HB cg n1 n2 ->
    CanJoin n2 x sj.
  Proof.
    intros.
    unfold CG.HB in *.
    inversion H1.
    apply wb_in_0 with (sj:=sj) (x:=x) in H2; auto.
    inversion H2; subst.
    destruct H4 as ((v1,v2),(Hx,Hy)); subst.
    apply end_to_edge with (Edge := InEdge sj x) in Hx; auto.
    simpl.
    destruct Hx.
    simpl in *.
    auto.
  Qed.

End Incl.

Section SJ.

  (** Main theorem part 1:
   Shows that we can build an annotated CG with SJ information
   from a SJ trace and a CG. *)

  Theorem events_sj_to_sj:
    forall t k cg,
    Events.SJ t k ->
    CG.CG t cg ->
    exists sj, SJ t cg sj.
  Proof.
    induction t; intros. {
      inversion H; subst; clear H.
      inversion H0; subst; clear H0.
      eauto using sj_nil.
    }
    inversion H0; subst; clear H0;
    inversion H; subst; clear H; simpl_red;
    try (
      assert (Hsj: exists sj, SJ t (vs,es) sj) by eauto;
      destruct Hsj as (sj, Hsj)
    ).
    - eapply CG.cg_init in H3; eauto.
      exists (Nil ::  sj).
      eauto using sj_init.
    - eapply CG.cg_fork in H3; eauto.
      exists (Copy nx :: Cons y nx :: sj).
      eauto using sj_fork.
    - eapply CG.cg_join in H3; eauto.
      exists (Append nx ny :: sj).
      eapply sj_join; eauto.
      inversion H10; subst.
      unfold FGraph.Edge in *.
      eapply sj_edge_to_knows_0 in H2; eauto.
      inversion H2; subst.
      simpl_node.
    - eapply CG.cg_continue in H3; eauto.
      exists (Copy prev :: sj).
      eauto using sj_continue.
  Qed.

  (** Main theorem part 2: from an annotated CG+SJ we can build a
  trace-valid SJ. *)

  Let sj_to_events_sj_0:
    forall t sj cg,
    CG.CG t cg ->
    SJ t cg sj ->
    exists k, Events.SJ t k.
  Proof.
    induction t; intros. {
      inversion H; subst; clear H.
      inversion H0; subst; clear H0.
      eauto using Events.sj_nil.
    }
    inversion H; subst; clear H;
    inversion H0; subst; clear H0; simpl_red.
    - apply IHt in H2; eauto using sj_to_cg; destruct H2 as (k, Hk).
      eauto using Events.sj_init.
    - assert (Hsj := H16).
      apply IHt in H16; eauto using sj_to_cg; destruct H16 as (k, Hk).
      assert (exists k', CheckOp k (SJ_Notations.F x y) k'). {
        exists (fork x y k).
        apply check_fork.
        - unfold not; intros; subst.
          apply maps_to_to_in in H5.
          contradiction.
        - unfold not; intros N.
          destruct N as (e, (?,He)).
          unfold FGraph.Edge in *.
          destruct e as (a,b).
          inversion He; simpl in *; subst.
          + eapply sj_edge_to_knows_0 in H0; eauto.
            apply knows_to_in_l in H0.
            contradiction.
          + eapply sj_edge_to_knows_0 in H0; eauto.
            eapply knows_to_in_r in H0; eauto.
      }
      destruct H0 as (k', ?).
      eauto using Events.sj_fork.
    - assert (Hsj := H15).
      apply IHt in Hsj; eauto using sj_to_cg.
      destruct Hsj as (k, ?); auto.
      assert (Hk: exists k', CheckOp k (SJ_Notations.J x ty) k'). {
        exists (join x ty k).
        apply check_join.
        assert (Hk: Knows vs sj0 (x, ty)) by eauto using knows_def.
        eapply sj_to_knows_to_edge_0 in Hk; eauto.
      }
      destruct Hk as (k', Hk).
      eauto using Events.sj_join.
    - apply IHt in H10; eauto using sj_to_cg; destruct H10 as (k, Hk).
      eauto using Events.sj_continue.
  Qed.

  Theorem sj_to_events_sj:
    forall t sj cg,
    SJ t cg sj ->
    exists k, Events.SJ t k.
  Proof.
    eauto using sj_to_cg.
  Qed.

  Theorem hb_spec:
    forall t cg n1 n2 x sj,
    SJ t cg sj ->
    CanJoin n1 x sj ->
    CG.HB (snd cg) n1 n2 ->
    CanJoin n2 x sj.
  Proof.
    intros.
    eapply incl_hb; eauto.
    assert (Hsj: exists k, Events.SJ t k). {
      eapply sj_to_events_sj; eauto.
    }
    destruct Hsj as (k, Hsj).
    eauto using sj_to_incl.
  Qed.
(*
  (* -------------------------------------- *)

  Let sj_fresh_rw:
    forall vs es k sj,
    SJ (vs, es) k sj ->
    fresh vs = fresh sj.
  Proof.
    intros.
    inversion H.
    simpl in *.
    auto using maps_to_length_rw.
  Qed.

  Let can_join_to_node:
    forall vs es sj x k n,
    SJ (vs,es) k sj ->
    CanJoin n x sj ->
    Node n vs.
  Proof.
    intros.
    apply can_join_to_node_0 in H0.
    inversion H.
    eauto using node_tr.
  Qed.


  Let can_join_to_node_0:
    forall n x sj,
    CanJoin n x sj ->
    Node n sj.
  Proof.
    intros.
    induction H; auto using node_cons, node_eq.
  Qed.

  Let fresh_absurd_eq:
    forall {A} vs (x:A),
     ~ fresh vs = fresh (x :: vs).
  Proof.
    induction vs; intros. {
      unfold not; intros N.
      inversion N.
    }
    unfold fresh in *.
    simpl in *.
    unfold not; intros N.
    inversion N.
    omega.
  Qed.

  Inductive HBCanJoin (cg:CG.computation_graph) : node -> tid -> Prop :=
  | hb_can_join_hb:
    forall y nx ny,
    CG.SpawnPoint y ny cg ->
    CG.HB (snd cg) ny nx ->
    HBCanJoin cg nx y
  | hb_can_join_eq:
    forall y n,
    CG.SpawnPoint y n cg ->
    HBCanJoin cg n y.

  Let hb_can_join_neq:
    forall vs es n x y e,
    x <> y ->
    HBCanJoin (vs, es) n x ->
    HBCanJoin (y :: vs, CG.F e :: es) n x.
  Proof.
    intros.
    inversion H0; subst; clear H0;
    simpl in *;
    eauto using hb_can_join_hb, hb_can_join_eq, CG.spawn_point_neq, CG.hb_impl_cons.
  Qed.

  Let hb_can_join_continue:
    forall vs es n z y e,
    HBCanJoin (vs, es) n z ->
    HBCanJoin (y :: vs, CG.C e :: es) n z.
  Proof.
    intros.
    inversion H; subst; clear H;
    simpl in *;
    eauto using hb_can_join_hb, hb_can_join_eq, CG.spawn_point_continue, CG.hb_impl_cons.
  Qed.

  Let hb_can_join_join:
    forall vs es n y z e,
    HBCanJoin (y :: vs, es) n z ->
    HBCanJoin (y :: vs, CG.J e :: es) n z.
  Proof.
    intros.
    inversion H; subst; clear H;
    simpl in *;
    eauto using hb_can_join_hb, hb_can_join_eq, CG.spawn_point_join, CG.hb_impl_cons.
  Qed.

  Let hb_can_join_spawn:
    forall n x y vs es,
    ~ List.In y vs ->
    MapsTo x n vs ->
    HBCanJoin (y :: x :: vs, CG.F (n, fresh (x :: vs)) :: CG.C (n, fresh vs) :: es) (fresh vs) y.
  Proof.
    auto using CG.spawn_point_eq, CG.spawn_point_eq, CG.spawn_point_continue, hb_can_join_eq.
  Qed.

  Let hb_can_join_trans:
    forall cg n n' x,
    HBCanJoin cg n x ->
    CG.HB (snd cg) n n' ->
    HBCanJoin cg n' x.
  Proof.
    intros.
    inversion H; subst; clear H;
    eauto using hb_can_join_hb, CG.hb_trans.
  Qed.

  Let spawn_point_absurd_nil:
    forall vs x n,
    ~ CG.SpawnPoint x n (vs, nil).
  Proof.
    induction vs; unfold not; intros. {
      inversion H.
    }
    inversion H; subst; clear H.
    apply IHvs in H4.
    contradiction.
  Qed.

  Let spawn_point_cons:
    forall x n vs es y e' e,
    CG.SpawnPoint x n (vs, es) ->
    CG.SpawnPoint x n (y :: vs, CG.J e' :: CG.C e :: es).
  Proof.
    auto using CG.spawn_point_join, CG.spawn_point_continue.
  Qed.

  Let hb_can_join_cons:
    forall vs es n x e' e y,
    HBCanJoin (vs, es) n x ->
    HBCanJoin (y :: vs, CG.J e' :: CG.C e :: es) n x.
  Proof.
    intros.
    inversion H; subst; clear H; simpl in *. {
      eauto using CG.hb_cons, hb_can_join_hb.
    }
    auto using hb_can_join_eq.
  Qed.

  Let hb_can_join_cons_c:
    forall vs es a b y x,
    HBCanJoin (vs, es) a x ->
    HBCanJoin (y :: vs, CG.C (a, b) :: es) b x.
  Proof.
    intros.
    inversion H; subst; clear H. {
      simpl in *.
      apply hb_can_join_hb with (ny:=ny).
      + eauto using CG.spawn_point_continue.
      + simpl in *.
        remember (_::es) as es'.
        assert (CG.HB es' ny a) by (subst; auto using CG.hb_cons).
        assert (CG.HB es' a b) by (subst;auto using CG.edge_to_hb).
        eauto using CG.hb_trans.
    }
    apply hb_can_join_hb with (ny:=a); simpl;
    auto using CG.spawn_point_continue, CG.edge_to_hb.
  Qed.

  Let hb_can_join_cons_j:
    forall vs es a b y x,
    HBCanJoin (y :: vs, es) a x ->
    HBCanJoin (y :: vs, CG.J (a, b) :: es) b x.
  Proof.
    intros.
    inversion H; subst; clear H. {
      simpl in *.
      apply hb_can_join_hb with (ny:=ny).
      + eauto using CG.spawn_point_join.
      + simpl in *.
        remember (_::es) as es'.
        assert (CG.HB es' ny a) by (subst; auto using CG.hb_cons).
        assert (CG.HB es' a b) by (subst;auto using CG.edge_to_hb).
        eauto using CG.hb_trans.
    }
    apply hb_can_join_hb with (ny:=a); simpl;
    auto using CG.spawn_point_join, CG.edge_to_hb.
  Qed.

  Let hb_can_join_cons_v:
    forall vs es n x z,
    ~ List.In x vs ->
    HBCanJoin (vs, es) n z ->
    HBCanJoin (x :: vs, es) n z.
  Proof.
    intros.
    inversion H0; subst; clear H0; simpl in *. {
      apply hb_can_join_hb with (ny:=ny); simpl; auto using CG.spawn_point_init.
    }
    auto using CG.spawn_point_init, hb_can_join_eq.
  Qed.

  Let spawn_point_to_edge:
    forall es x n vs,
    CG.SpawnPoint x n (vs, es) ->
    exists n', List.In (CG.C (n', n)) es.
  Proof.
    induction es; intros. {
      inversion H; subst.
      apply spawn_point_absurd_nil in H3; contradiction.
    }
    inversion H; subst; clear H.
    - 
    - exists n'.
      auto using in_eq, in_cons.
    - apply IHes in H4.
      destruct H4 as (nx, Hi).
      eauto using in_cons.
    - apply IHes in H1.
      destruct H1 as (nx, Hi).
      eauto using in_cons.
    - apply IHes in H1.
      destruct H1 as (nx, Hi).
      eauto using in_cons.
  Qed.

  Let spawn_point_to_node:
    forall es x n vs,
    EdgeToNode (vs, es) ->
    SpawnPoint x n (vs, es) ->
    Node n vs.
  Proof.
    intros.
    apply spawn_point_to_edge in H0.
    destruct H0 as  (n0, He).
    assert (Hx: HB_Edge es (n0, n)). {
      eauto using hb_edge_def, edge_eq.
    }
    apply H in Hx.
    destruct Hx.
    auto.
  Qed.

  Let hb_can_join_to_node:
    forall vs es n x,
    EdgeToNode (vs, es) ->
    HBCanJoin (vs, es) n x ->
    Node n vs.
  Proof.
    intros.
    inversion H0; subst; clear H0; simpl in *. {
      apply edge_to_node_hb_snd with (vs:=vs) in H2; auto.
    }
    eauto using spawn_point_to_node.
  Qed.

  Let hb_absurd_fresh_lhs:
    forall nx x (vs:list tid) es (n:node),
    DAG (FGraph.Edge (cg_edges (F (nx, node_next (fresh vs)) :: C (nx, fresh vs) :: es))) ->
    EdgeToNode (vs, es) ->
    MapsTo x nx vs ->
    ~ HB (F (nx, node_next (fresh vs)) :: C (nx, fresh vs) :: es) (fresh vs) n.
  Proof.
    intros.
    assert (Ha : DAG (FGraph.Edge (cg_edges (C (nx, fresh vs) :: es)))) by
    eauto using f_dag_inv_cons.
    assert (Hb : DAG (FGraph.Edge (cg_edges es))) by
    eauto using f_dag_inv_cons.
    unfold not; intros N.
    apply hb_inv_cons in N; auto.
    destruct N as [Hy|[(?,[?|Hy])|[(?,Hy)|(Hy,?)]]]; subst;
    simpl_node; auto;
    apply hb_inv_cons in Hy; auto;
    destruct Hy as [Hx|[(?,[?|Hx])|[(?,Hx)|(Hx,?)]]]; subst; simpl_node;
    hb_simpl.
  Qed.


  Let spawn_point_to_in:
    forall es vs x n,
    CG.SpawnPoint x n (vs, es) ->
    List.In x vs.
  Proof.
    induction es; intros. {
      apply spawn_point_absurd_nil in H.
      contradiction.
    }
    inversion H; subst; clear H; eauto using in_cons, in_eq.
  Qed.

  Let hb_can_join_to_in:
    forall vs es n x,
    HBCanJoin (vs, es) n x ->
    List.In x vs.
  Proof.
    intros.
    inversion H; subst; clear H; eauto.
  Qed.


  Notation KnowsEquiv1 sj cg :=
  (forall n x, CanJoin n x sj -> HBCanJoin cg n x).

  Let KnowsEquiv2 sj cg :=
  (forall n x, HBCanJoin cg n x -> CanJoin n x sj).

  Definition FirstHB (cg:CG.computation_graph) :=
    forall x n1 n2,
    First x n1 (fst cg) ->
    MapsTo x n2 (fst cg) ->
    n1 <> n2 ->
    CG.HB (snd cg) n1 n2.

  Let can_join_pres_fork:
    forall n cg sj z sj' cg' x y,
    length (fst cg) = length sj ->
    KnowsEquiv1 sj cg ->
    CG.Reduces cg (x, CG.FORK y) cg' ->
    Reduces sj (x, CG.FORK y) cg' sj' ->
    CanJoin n z sj' ->
    HBCanJoin cg' n z.
  Proof.
    intros.
    simpl_red.
    rename prev into nz.
    rename H0 into Hind.
    rename H into Heq.
    inversion H3; subst; clear H3; simpl in *. {
      inversion H2; subst; clear H2; simpl in *.
      - apply Hind in H3.
        assert (z <> y). {
          unfold not; intros N; subst.
          apply hb_can_join_to_in in H3.
          contradiction.
        }
        auto.
      - apply maps_to_length_rw in Heq.
        rewrite <- Heq in *.
        auto.
      - apply Hind in H4.
        apply maps_to_length_rw in Heq.
        rewrite <- Heq in *.
        apply hb_can_join_trans with (n:=nz); simpl; auto.
        eauto using hb_edge_to_hb, hb_edge_def, edge_eq, in_cons, in_eq.
    }
    apply can_join_inv_cons_2 in H2.
    assert (R: length (x :: vs) = length (Cons y nz :: sj)) by (simpl; auto).
    apply maps_to_length_rw in R.
    rewrite <- R.
    destruct H2 as [(?,Hc)|[(?,Hc)|(?,?)]]; subst.
    - apply Hind in Hc.
      apply hb_can_join_to_in in Hc.
      contradiction.
    - apply Hind in Hc.
      apply hb_can_join_trans with (n:=nz); simpl;
      eauto using hb_edge_to_hb, hb_edge_def, edge_eq, in_cons, in_eq.
    - apply maps_to_length_rw in Heq.
      rewrite <- Heq in *.
      simpl_node.
  Qed.

  Let can_join_pres_join:
    forall n cg sj z sj' cg' x y,
    length (fst cg) = length sj ->
    KnowsEquiv1 sj cg ->
    CG.Reduces cg (x, CG.JOIN y) cg' ->
    Reduces sj (x, CG.JOIN y) cg' sj' ->
    CanJoin n z sj' ->
    HBCanJoin cg' n z.
  Proof.
    intros.
    simpl_red.
    rename prev into nz.
    rename H0 into Hind.
    rename H into Heq.
    apply Hind in H19.
    apply maps_to_length_rw in Heq.
    inversion H3; subst; clear H3; simpl in *;
          try rewrite <- Heq; auto.
  Qed.

  Let can_join_pres_continue:
    forall n cg sj z sj' cg' x,
    length (fst cg) = length sj ->
    KnowsEquiv1 sj cg ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces sj (x, CG.CONTINUE) cg' sj' ->
    CanJoin n z sj' ->
    HBCanJoin cg' n z.
  Proof.
    intros.
    simpl_red.
    rename prev into nz.
    rename H0 into Hind.
    rename H into Heq.
    simpl in *.
    apply maps_to_length_rw in Heq.
    inversion H3; subst; clear H3; simpl in *;
    try rewrite Heq; auto.
  Qed.

  Let can_join_pres_init:
    forall n cg sj z sj' cg' x,
    length (fst cg) = length sj ->
    KnowsEquiv1 sj cg ->
    CG.Reduces cg (x, CG.INIT) cg' ->
    Reduces sj (x, CG.INIT) cg' sj' ->
    CanJoin n z sj' ->
    HBCanJoin cg' n z.
  Proof.
    intros.
    simpl_red.
    rename H0 into Hind.
    rename H into Heq.
    simpl in *.
    apply maps_to_length_rw in Heq.
    inversion H3; subst; clear H3; simpl in *.
    apply Hind in H2.
    try rewrite Heq; auto.
  Qed.

  Let can_join_pres_fork_2 cg k sj
    (Hsj: SJ cg k sj)
    (Heq: length (fst cg) = length sj)
    (Hke: KnowsEquiv2 sj cg)
    (Hen: EdgeToNode cg)
    sj' cg' x y
    (Hcr: CG.Reduces cg (x, CG.FORK y) cg')
    (Hr: Reduces sj (x, CG.FORK y) cg' sj')
    (Hd: DAG (FGraph.Edge (cg_edges (snd cg')))):
    forall n z,
    HBCanJoin cg' n z ->
    CanJoin n z sj'.
  Proof.
    intros.
    simpl_red.
    inversion H; subst; clear H;
    simpl in *. {
      rename ny0 into nz.
      rewrite fresh_cons_rw_next in *.
      clear nx; rename prev into nx.
      apply maps_to_length_rw in Heq.
      inversion H0; subst; clear H0. {
        eapply hb_absurd_fresh_lhs in H1; eauto.
        contradiction.
      }
      inversion H9; subst; clear H9. (* SpawnPoint *)
      assert (Hc: HBCanJoin (vs, es) nz z). {
        auto using hb_can_join_eq.
      }
      apply hb_inv_cons in H1; auto.
      apply f_dag_inv_cons in Hd.
      destruct H1 as [Hy|[(?,[?|Hy])|[(?,Hy)|(?,Hy)]]]; subst;
      try rewrite Heq.
      - apply Hke in Hc.
        apply hb_inv_cons in Hy; auto.
        destruct Hy as [Hx|[(?,[?|Hx])|[(?,Hx)|(Hx,?)]]]; subst; try (rewrite Heq);
        eauto using hb_spec, can_join_cons, can_join_neq; hb_simpl.
      - rewrite <- fresh_cons_rw_next with (x:=Cons y nz).
        assert (Hc0: HBCanJoin (vs, es) nz z). {
          auto using hb_can_join_eq .
        }
        auto using can_join_copy, can_join_cons.
      - apply hb_inv_cons in Hy; auto.
        rewrite <- fresh_cons_rw_next with (x:=Cons y nx).
        apply can_join_copy.
        destruct Hy as [Hx|[(?,[?|Hx])|[(?,Hx)|(Hx,?)]]]; subst;
        simpl_node; hb_simpl;
        eauto using hb_can_join_hb, can_join_cons.
      - apply hb_inv_cons in Hy; auto.
        destruct Hy as [Hx|[(?,[?|Hx])|[(?,Hx)|(Hx,?)]]]; subst; try (rewrite Heq);
        simpl_node; hb_simpl.
      - apply hb_inv_cons in Hy; auto.
        destruct Hy as [Hx|[(?,[?|Hx])|[(?,Hx)|(Hx,?)]]]; subst; try (rewrite Heq);
        simpl_node; hb_simpl.
    }
    apply maps_to_length_rw in Heq.
    inversion H0; subst; clear H0. {
      rewrite Heq.
      apply can_join_cons.
      apply can_join_eq.
    }
    inversion H8; subst; clear H8.
    assert (Hc: HBCanJoin (vs,es) n z). {
      auto using hb_can_join_eq.
    }
    apply Hke in Hc.
    auto using can_join_cons, can_join_neq.
  Qed.

  Let can_join_pres_join_2 cg k sj
    (Hsj: SJ cg k sj)
    (Heq: length (fst cg) = length sj)
    (Hke: KnowsEquiv2 sj cg)
    (Hen: EdgeToNode cg)
    sj' cg' x y
    (Hcr: CG.Reduces cg (x, CG.JOIN y) cg')
    (Hr: Reduces sj (x, CG.JOIN y) cg' sj')
    (Hd: DAG (FGraph.Edge (cg_edges (snd cg')))):
    forall n z,
    HBCanJoin cg' n z ->
    CanJoin n z sj'.
  Proof.
    intros.
    simpl_red.
    inversion H; subst; clear H;
    simpl in *. {
      rename ny0 into c.
      rename prev into a.
      rename ny into b.
      apply maps_to_length_rw in Heq.
      inversion H0; subst; clear H0.
      inversion H3; subst; clear H3.
      apply hb_inv_cons in H1; auto.
      apply f_dag_inv_cons in Hd.
      destruct H1 as [Hy|[(?,[?|Hy])|[(?,Hy)|(Hy,?)]]]; subst.
      + apply hb_inv_cons in Hy; auto.
        destruct Hy as [Hx|[(?,[?|Hx])|[(?,Hx)|(Hx,?)]]]; subst;
        try rewrite Heq;
        hb_simpl;
        eauto using
          can_join_append_right, can_join_append_left,
          hb_can_join_hb, can_join_cons, hb_can_join_eq.
      + rewrite Heq.
        eauto using
          can_join_append_right, can_join_append_left,
          hb_can_join_hb, can_join_cons, hb_can_join_eq.
      + apply hb_inv_cons in Hy; auto.
        destruct Hy as [Hx|[(?,[?|Hx])|[(?,Hx)|(Hx,?)]]]; subst;
        try rewrite Heq;
        hb_simpl;
        eauto using
          can_join_append_right, can_join_append_left,
          hb_can_join_hb, can_join_cons, hb_can_join_eq.
      + apply hb_inv_cons in Hy; auto.
        destruct Hy as [Hx|[(?,[?|Hx])|[(?,Hx)|(Hx,?)]]]; subst;
        try rewrite Heq;
        hb_simpl; simpl_node.
      + apply hb_inv_cons in H; auto.
        destruct H as [Hx|[(?,[?|Hx])|[(?,Hx)|(Hx,?)]]]; subst;
        try rewrite Heq;
        hb_simpl; simpl_node.
    }
    inversion H0; subst; clear H0.
    inversion H1; subst; clear H1.
    eauto using
      can_join_append_right, can_join_append_left,
      hb_can_join_hb, can_join_cons, hb_can_join_eq.
  Qed.

  Let can_join_pres_continue_2 cg k sj
    (Hsj: SJ cg k sj)
    (Heq: length (fst cg) = length sj)
    (Hke: KnowsEquiv2 sj cg)
    (Hen: EdgeToNode cg)
    sj' cg' x
    (Hcr: CG.Reduces cg (x, CG.CONTINUE) cg')
    (Hr: Reduces sj (x, CG.CONTINUE) cg' sj')
    (Hd: DAG (FGraph.Edge (cg_edges (snd cg')))):
    forall n z,
    HBCanJoin cg' n z ->
    CanJoin n z sj'.
  Proof.
    intros.
    simpl_red.
    inversion H; subst; clear H;
    simpl in *. {
      apply maps_to_length_rw in Heq.
      inversion H0; subst; clear H0.
      apply hb_inv_cons in H2; auto.
      destruct H2 as [Hy|[(?,[?|Hy])|[(?,Hy)|(Hy,?)]]]; subst;
      try rewrite Heq;
      hb_simpl;
      eauto using
          can_join_copy,
          hb_can_join_hb, can_join_cons, hb_can_join_eq.
    }
    inversion H0; subst; clear H0.
    eauto using
        can_join_copy,
        hb_can_join_hb, can_join_cons, hb_can_join_eq.
  Qed.

  Definition KnowsEquiv sj cg :=
  forall n x, CanJoin n x sj <-> HBCanJoin cg n x.

  Let knows_equiv_to_1:
    forall sj cg,
    KnowsEquiv sj cg ->
    KnowsEquiv1 sj cg.
  Proof.
    intros.
    apply H in H0.
    assumption.
  Qed.

  Let knows_equiv_to_2:
    forall sj cg,
    KnowsEquiv sj cg ->
    KnowsEquiv2 sj cg.
  Proof.
    unfold KnowsEquiv2.
    intros.
    apply H in H0.
    assumption.
  Qed.

  Theorem hb_can_join_preserves cg k sj
    (Hsj: SJ cg k sj)
    (Hke: KnowsEquiv sj cg)
    (Hlt: LtEdges (cg_edges (snd cg))):
    forall i sj' cg',
    CG.Reduces cg i cg' ->
    Reduces sj i cg' sj' ->
    KnowsEquiv sj' cg'.
  Proof.
    intros.
    unfold KnowsEquiv.
    intros.
    destruct i.
    assert (Hlt2: LtEdges (cg_edges (snd cg'))) by eauto using lt_edges_reduces.
    apply cg_dag in Hlt2.
    inversion Hsj.
    split; intros.
    + destruct o.
      * 
      * eapply can_join_pres_fork; eauto.
      * eapply can_join_pres_join; eauto.
      * eapply can_join_pres_continue; eauto.
    + destruct o.
      * eapply can_join_pres_fork_2; eauto.
      * eapply can_join_pres_join_2; eauto.
      * eapply can_join_pres_continue_2; eauto.
  Qed.

  Lemma sj_make_cg:
    forall a,
    SJ (make_cg a) nil (Nil :: nil).
  Proof.
    intros.
    apply sj_def; auto using make_edge_to_node; unfold make_cg; simpl; auto
    using free_in_graph_nil, knows_to_edge_nil, incl_nil, edge_to_knows_nil.
  Qed.

  Lemma knows_equiv_nil:
    forall a,
    KnowsEquiv (Nil :: nil) (make_cg a).
  Proof.
    intros.
    unfold KnowsEquiv.
    split; intros.
    - inversion H; subst; clear H.
      inversion H3; subst; clear H3.
    - inversion H; subst; clear H. {
        inversion H0.
      }
      inversion H0.
  Qed.

  (** Build a SJ from a CG *)

  Theorem sj_spec:
    forall a t cg k,
    CG.Run a t cg ->
    Events.Run t k ->
    exists sj, SJ cg k sj /\ KnowsEquiv sj cg.
  Proof.
    induction t; intros. {
      inversion H; subst; clear H.
      inversion H0; subst; clear H0.
      eauto using sj_make_cg, knows_equiv_nil.
    }
    inversion H; subst; clear H.
    assert (Hcg := H3).
    inversion H0; subst; clear H0.
    eapply IHt in H3; eauto.
    destruct H3 as (sj, (Hsj,Hk)).
    assert (Hr: exists sj', Reduces sj a0 cg sj'). {
      inversion Hsj.
      eauto.
    }
    destruct Hr as (sj', Hr).
    apply CG.run_to_lt_edges in Hcg.
    eauto using sj_reduces, hb_can_join_preserves.
  Qed.
  *)
End SJ.

(*
Section Extra.
  Lemma build_cg:
    forall t k,
    Events.Run t k ->
    exists a cg, CG.Run a t cg.
  Proof.
    induction t; intros. {
      exists (taskid 0).
      exists (make_cg (taskid 0)).
      auto using run_nil.
    }
    inversion H; subst; clear H.
    apply IHt in H2.
    destruct H2 as (x, (cg, Hr)).
    exists x.
    inversion H4; subst; clear H4.
    - inversion H; subst; clear H.
      CG.Reduces
    apply run_cons in Hr.
  Qed.
End Extra.
*)
