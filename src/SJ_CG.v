Require Import Coq.Lists.List.
Require Import Aniceto.Graphs.Graph.
Require Import Aniceto.Graphs.FGraph.

Require Import CG.
Require Import SafeJoins.
Require Import Tid.
Require Import Node.
(*Require Import Bijection.*)

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

  Inductive Reduces: known_set -> CG.event -> known_set -> Prop :=
  | reduces_fork:
    forall k k' x y,
    SafeJoins.Reduces k {| op_t := FORK; op_src := x; op_dst := y |} k' ->
    Reduces k (x, CG.FORK y) k'
  | reduces_join:
    forall k k' x y,
    SafeJoins.Reduces k {| op_t := JOIN; op_src := x; op_dst := y |} k' ->
    Reduces k (x, CG.JOIN y) k'
  | reduces_continue:
    forall k x,
    Reduces k (x, CG.CONTINUE) k.

  Inductive Run : list event -> known_set -> Prop :=
  | run_nil:
    Run nil nil
  | run_cons:
    forall k k' t e,
    Run t k ->
    Reduces k e k' ->
    Run (e::t) k'.

End Defs.

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

  Section ESafeJoins.

  Inductive Reduces : cg_safe_joins -> computation_graph -> cg_safe_joins -> Prop :=

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

  | reduces_fork:

    forall x y x' ty l vs es,
    Reduces l (ty::vs, F (x,y)::C (x,x')::es) (Copy x::Cons ty x::l)

  | reduces_join:
    forall x y x' ty l vs es,
    MapsTo ty y vs ->
    CanJoin x ty l -> (* check: ty \in x *)
    Reduces l (vs, J (y,x') :: C (x,x')::es) (Append x y :: l)

  | reduces_continue:
    forall x x' l es vs,
    Reduces l (vs, C (x,x')::es) (Copy x :: l).

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

  Let can_join_to_free:
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

  Let knows_cons:
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

  Let do_fork_1:
    forall x y z cg cg' sj sj',
    CG.Reduces cg (x, CG.FORK y) cg' ->
    Reduces sj cg' sj' ->
    Knows (fst cg) sj (x, z) ->
    length (fst cg) = length sj ->
    Knows (fst cg') sj' (y, z).
  Proof.
    intros.
    rename H2 into Heq.
    inversion H; subst; clear H.
    inversion H6; subst; clear H6.
    assert (prev = nx) by eauto using maps_to_fun_2; subst; clear H12.
    apply knows_def with (nx:=ny); auto.
    inversion H0; subst; clear H0.
    apply maps_to_inv_eq in H10; subst.
    simpl in *.
    assert (R: fresh (x :: vs) = fresh (Cons y nx :: sj))
    by (unfold fresh; simpl; auto); rewrite R.
    inversion H1; subst; simpl in *; clear H1.
    assert (nx0 = nx) by eauto using maps_to_fun_2; subst; clear H2.
    auto using can_join_copy, can_join_cons.
  Qed.

  Let do_fork_2:
    forall sj sj' cg cg' x y,
    Reduces sj cg' sj' ->
    CG.Reduces cg (x, CG.FORK y) cg' ->
    length (fst cg) = length sj ->
    Knows (fst cg') sj' (x, y).
  Proof.
    intros.
    rename H1 into Heq.
    inversion H0; subst; clear H0.
    inversion H5; subst; clear H5.
    inversion H; subst; clear H H7.
    apply maps_to_inv_eq in H11; subst.
    apply maps_to_inv_eq in H9; subst.
    simpl in *.
    apply knows_def with (nx:=fresh sj).
    - apply maps_to_length_rw in Heq.
      rewrite <- Heq.
      auto using maps_to_eq, maps_to_cons.
    - auto using can_join_cons, can_join_eq.
  Qed.

  Let do_fork_3:
    forall cg x y cg' sj sj' a b,
    Reduces sj cg' sj' ->
    CG.Reduces cg (x, CG.FORK y) cg' ->
    Knows (fst cg) sj (a, b) ->
    FreeInGraph (fst cg) sj ->
    length (fst cg) = length sj ->
    Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    rename H2 into Hdom.
    rename H3 into Heq.
    inversion H0; subst; clear H0.
    inversion H; subst; clear H.
    inversion H6; subst; clear H6.
    rename es0 into es; rename x' into nx'.
    inversion H1; subst; clear H1; simpl in *.
    rename nx0 into na.
    apply maps_to_inv_eq in H13; subst.
    apply maps_to_inv_eq in H10; subst.
    assert (b <> y). {
      unfold not; intros; subst.
      contradiction H5.
      eauto using Hdom, can_join_to_free.
    }
    destruct (tid_eq_dec a x). {
      subst.
      assert (na = nx) by eauto using maps_to_fun_2; subst; clear H8.
      apply knows_def with (nx:=fresh vs).
      - auto using maps_to_cons, maps_to_eq.
      - apply maps_to_length_rw in Heq.
        rewrite Heq.
        eauto using can_join_neq, can_join_cons.
    }
    assert (a <> y). {
      unfold not; intros; subst.
      contradiction H5.
      eauto using maps_to_to_in.
    }
    eauto using knows_def, maps_to_cons, can_join_cons, maps_to_lt.
  Qed.

  Let do_join_1:
    forall sj cg cg' sj' x y z,
    Reduces sj cg' sj' ->
    CG.Reduces cg (x, CG.JOIN y) cg' ->
    Knows (fst cg) sj (x, y) ->
    Knows (fst cg) sj (y, z) ->
    length (fst cg) = length sj ->
    Knows (fst cg') sj' (x, z).
  Proof.
    intros.
    rename H3 into Heq.
    inversion H0; subst; clear H0.
    inversion H6; subst; clear H6.
    inversion H; subst; clear H.
    inversion H1; subst; clear H1; simpl in *.
    apply maps_to_inv_eq in H8.
    assert (ty = y) by eauto using maps_to_fun_1; subst; clear H16.
    apply maps_to_neq in H10; auto.
    apply knows_def with (nx:=fresh vs); auto using maps_to_eq.
    apply maps_to_length_rw in Heq.
    rewrite Heq.
    inversion H2; subst; clear H2.
    assert (nx0 = ny) by eauto using maps_to_fun_2; subst.
    auto using can_join_append_right.
  Qed.

  Let do_join_2:
    forall sj cg' sj' x y a b cg,
    CG.Reduces cg (x, CG.JOIN y) cg' ->
    Reduces sj cg' sj' ->
    Knows (fst cg) sj (x, y) ->
    Knows (fst cg) sj (a, b) ->
    length (fst cg) = length sj ->
    Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    rename H3 into Heq.
    inversion H; subst; clear H.
    inversion H6; subst; clear H6.
    inversion H0; subst; clear H0.
    assert (ty = y) by eauto using maps_to_fun_1; subst.
    apply maps_to_inv_eq in H12; subst.
    apply maps_to_neq in H10; subst; auto; clear H15 H8.
    simpl in *.
    destruct (tid_eq_dec x a). {
      subst.
      apply knows_def with (nx:=fresh sj).
      - apply maps_to_length_rw in Heq; rewrite <- Heq.
        auto using maps_to_eq.
      - inversion H2; subst; clear H2.
        inversion H1; subst; clear H1.
        assert (nx0 = nx) by eauto using maps_to_fun_2; subst.
        assert (prev = nx) by eauto using maps_to_fun_2; subst.
        auto using can_join_append_left.
    }
    auto using knows_cons.
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
      inversion H0; subst; clear H0.
      subst.
      assert (nx0 = nx) by eauto using maps_to_fun_2; subst.
      apply knows_def with (nx:=fresh vs); auto using maps_to_eq.
      apply maps_to_length_rw in H1.
      rewrite <- H1.
      auto using can_join_copy.
    }
    auto.
  Qed.

  Let do_continue_1:
    forall sj sj' cg cg' a b x,
    Reduces sj cg' sj' ->
    length (fst cg) = length sj ->
    Knows (fst cg) sj (a, b) ->
    CG.Reduces cg (x, CONTINUE) cg' ->
    Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    inversion H2; subst; clear H2.
    simpl in *.
    inversion H; subst; clear H.
    auto.
  Qed.

  Lemma edge_to_knows_reduces:
    forall cg sj k k' cg' sj' e,
    EdgeToKnows (fst cg) sj k ->
    Events.Reduces k e k' ->
    CG.Reduces cg e cg' ->
    Reduces sj cg' sj' ->
    FreeInGraph (fst cg) sj ->
    length (fst cg) = length sj ->
    EdgeToKnows (fst cg') sj' k'.
  Proof.
    intros.
    rename H3 into Hdom.
    rename H4 into Heq.
    unfold EdgeToKnows in *.
    intros.
    inversion H0; subst; clear H0.
    - inversion H4; subst; clear H4.
      destruct p as (a,b).
      apply fork_inv_in in H3.
      destruct H3 as [(?,?)|[(?,?)|?]]; subst.
      + eauto.
      + eauto.
      + eapply do_fork_3 with (x:=x) (y:=y); eauto.
    - inversion H4; subst; clear H4.
      destruct p as (a,b).
      unfold FGraph.Edge in *.
      apply H in H7.
      apply join_inv_in in H3.
      destruct H3 as [(?,?)|?]; subst.
      + eapply do_join_1 with (sj:=sj); eauto.
      + eapply do_join_2 with (sj:=sj); eauto.
    - destruct p as (a,b).
      eapply do_continue_1; eauto.
  Qed.

  Lemma edge_to_knows_nil:
    forall a,
    EdgeToKnows (a :: nil) (Nil :: nil) nil.
  Proof.
    unfold EdgeToKnows.
    intros.
    inversion H.
  Qed.

End ESafeJoins.

Section LengthPreserves.

  (* -------------------------------------------------- *)

  Lemma length_reduces:
    forall cg sj cg' sj' e,
    length (fst cg) = length sj ->
    CG.Reduces cg e cg' ->
    Reduces sj cg' sj' ->
    length (fst cg') = length sj'.
  Proof.
    intros.
    inversion H0; subst; clear H0; simpl in *.
    - inversion H4; subst; clear H4.
      inversion H1; subst; clear H1.
      simpl.
      auto.
    - inversion H3; subst; clear H3.
      inversion H1; subst; clear H1.
      simpl.
      auto.
    - inversion H1; subst; clear H1.
      simpl.
      auto.
  Qed.

End LengthPreserves.


Section FreeInGraph.

  (* -------------------------------------------------- *)

  Let free_neq_copy:
    forall x n sj,
    Free x (Copy n :: sj) ->
    Free x sj.
  Proof.
    intros.
    inversion H.
    destruct H0.
    - inversion H0.
    - eauto using free_def.
  Qed.

  Let free_neq_append:
    forall x n n' sj,
    Free x (Append n n' :: sj) ->
    Free x sj.
  Proof.
    intros.
    inversion H.
    inversion H0.
    - inversion H1.
    - eauto using free_def.
  Qed.

  Lemma free_in_graph_reduces:
    forall cg sj cg' sj' e,
    FreeInGraph (fst cg) sj ->
    CG.Reduces cg e cg' ->
    Reduces sj cg' sj' ->
    FreeInGraph (fst cg') sj'.
  Proof.
    unfold FreeInGraph.
    intros.
    inversion H0; subst; clear H0; simpl in *.
    - inversion H5; subst; clear H5.
      inversion H1; subst; clear H1.
      apply free_neq_copy in H2.
      inversion H2.
      inversion H0. {
        inversion H1; subst; clear H1.
        auto.
      }
      eauto using free_def, List.in_cons.
    - inversion H4; subst; clear H4.
      inversion H1; subst; clear H1.
      eauto using List.in_cons, free_neq_append.
    - inversion H1; subst; clear H1.
      eauto.
  Qed.

  Lemma free_in_graph_nil:
    forall a,
    FreeInGraph (a :: nil) (Nil :: nil).
  Proof.
    unfold FreeInGraph.
    intros.
    inversion H; subst; clear H.
    destruct H0. {
      inversion H.
    }
    inversion H.
  Qed.

End FreeInGraph.


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

  Let can_join_fork:
    forall cg cg' sj sj' k k' a b x y,
    KnowsToEdge (fst cg) sj k ->
    Events.Reduces k (x, CG.FORK y) k' ->
    CG.Reduces cg (x, CG.FORK y) cg' ->
    Reduces sj cg' sj' ->
    Knows (fst cg') sj' (a, b) ->
    length (fst cg) = length sj ->
    List.In (a, b) k'.
  Proof.
    intros.
    rename H4 into Heq.
    inversion H0; subst; clear H0.
    inversion H8; subst; clear H8.
    inversion H1; subst; clear H1.
    inversion H9; subst; clear H9.
    simpl in *.
    apply maps_to_inv_eq in H15; subst.
    apply maps_to_inv_eq in H13; subst.
    inversion H2; subst; clear H2.
    inversion H3; subst; clear H3.
    clear H11.
    rename nx into na.
    rename prev into nx.
    assert (R: fresh (x :: vs) = fresh (Cons y nx :: sj))
    by (unfold fresh in *; simpl; auto).
    inversion H4; subst; clear H4. {
      apply maps_to_inv in H2; destruct H2 as [(?,?)|(?,mt)]. {
        subst.
        rewrite R in *.
        apply can_join_absurd_fresh in H9; contradiction.
      }
      apply maps_to_length_rw in Heq.
      apply maps_to_inv in mt; destruct mt as [(?,?)|(?,mt)]. {
        subst.
        rewrite Heq in *.
        apply can_join_inv_cons_1 in H9.
        destruct H9 as [?|(?,?)]; subst.
        - auto using in_fork_5.
        - eauto using knows_def, in_fork.
      }
      inversion H9; subst; clear H9.
      - eauto using knows_def, in_fork.
      - rewrite <- Heq in *.
        apply maps_to_absurd_fresh in mt; contradiction.
      - rewrite <- Heq in *.
        apply maps_to_absurd_fresh in mt; contradiction.
    }
    assert (NODE.lt nx (fresh vs)) by eauto using maps_to_lt.
    apply maps_to_length_rw in Heq.
    rewrite Heq in *.
    apply can_join_lt in H9; auto.
    inversion H2; subst; clear H2. {
      eauto using in_fork_2, knows_def.
    }
    apply maps_to_lt in H11.
    simpl in *.
    unfold fresh, NODE.lt in *.
    simpl in *.
    inversion Heq as (Hx).
    rewrite Hx in *.
    apply Lt.lt_irrefl in H11.
    contradiction.
  Qed.

  Let can_join_join:
    forall cg cg' sj sj' k k' a b x y,
    KnowsToEdge (fst cg) sj k ->
    Events.Reduces k (x, CG.JOIN y) k' ->
    CG.Reduces cg (x, CG.JOIN y) cg' ->
    Reduces sj cg' sj' ->
    Knows (fst cg') sj' (a, b) ->
    length (fst cg) = length sj ->
    List.In (a, b) k'.
  Proof.
    intros.
    rename H4 into Heq.
    inversion H0; subst; clear H0.
    inversion H8; subst; clear H8.
    inversion H1; subst; clear H1.
    inversion H7; subst; clear H7.
    simpl in *.
    inversion H2; subst; clear H2.
    inversion H3; subst; clear H3.
    assert (ty = y) by eauto using maps_to_fun_1; subst; clear H17.
    apply maps_to_inv_eq in H9; subst.
    apply maps_to_neq in H11; auto.
    rename nx into nb.
    rename prev into nx.
    apply maps_to_length_rw in Heq.
    apply maps_to_inv in H2; destruct H2 as [(?,?)|(?,mt)]. {
      subst.
      rewrite Heq in *.
      apply can_join_inv_append in H4.
      destruct H4; 
      eauto using knows_def, in_join, in_join_2.
    }
    inversion H4; subst; clear H4.
    - eauto using knows_def, in_join.
    - rewrite <- Heq in *.
      apply maps_to_absurd_fresh in mt; contradiction.
    - rewrite <- Heq in *.
      apply maps_to_absurd_fresh in mt; contradiction.
  Qed.

  Let can_join_continue:
    forall cg cg' sj sj' k k' a b x,
    KnowsToEdge (fst cg) sj k ->
    Events.Reduces k (x, CG.CONTINUE) k' ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces sj cg' sj' ->
    Knows (fst cg') sj' (a, b) ->
    length (fst cg) = length sj ->
    List.In (a, b) k'.
  Proof.
    intros.
    rename H4 into Heq.
    inversion H0; subst; clear H0.
    inversion H1; subst; clear H1.
    inversion H2; subst; clear H2.
    simpl in *.
    rename k' into k.
    rename prev into nx.
    apply maps_to_inv_eq in H6; subst.
    inversion H3; subst; clear H3.
    apply maps_to_length_rw in Heq.
    apply maps_to_inv in H2; destruct H2 as [(?,?)|(?,mt)]. {
      subst.
      rewrite Heq in *.
      apply can_join_inv_copy_1 in H5.
      eauto using knows_def.
    }
    rename nx0 into nb.
    assert (Hx:=mt).
    apply maps_to_lt in mt.
    rewrite Heq in *.
    eauto using knows_def, can_join_lt, maps_to_lt.
  Qed.

  Lemma knows_to_edge_reduces:
    forall cg sj cg' sj' e k' k,
    length (fst cg) = length sj ->
    KnowsToEdge (fst cg) sj k ->
    Events.Reduces k e k' ->
    CG.Reduces cg e cg' ->
    Reduces sj cg' sj' ->
    KnowsToEdge (fst cg') sj' k'.
  Proof.
    intros.
    unfold KnowsToEdge; intros; destruct p as (a,b).
    destruct e as (x, [y|y|]).
    - eapply can_join_fork; eauto.
    - eauto.
    - eauto.
  Qed.

  Lemma knows_to_edge_nil:
    forall a,
    KnowsToEdge (a :: nil) (Nil :: nil) nil.
  Proof.
    unfold KnowsToEdge; intros.
    inversion H; subst; clear H.
    inversion H0; subst; clear H0. {
      simpl in *.
      destruct nx; simpl in *; subst.
      inversion H1; subst; clear H1.
      inversion H3.
    }
    inversion H5.
  Qed.
End KnowsToEdge.

Section Incl.
  (* ------------------------------------------ *)

  Definition Incl cg sj :=
  forall n1 n2 x,
  List.In (n1, n2) (cg_edges cg) ->
  CanJoin n1 x sj ->
  CanJoin n2 x sj.

  Let in_length_absurd:
    forall vs es n,
    EdgeToIndex (vs, es) ->
    ~ List.In (fresh vs, n) (map e_edge es).
  Proof.
    intros.
    intuition.
    assert (Hx:List.In (fresh vs, n) (cg_edges (vs, es))) by auto.
    apply node_lt_length_left in Hx; auto.
    simpl in Hx.
    unfold NODE.lt in *.
    omega.
  Qed.

  Let incl_fork:
    forall cg cg' sj sj' k k' x n1 n2 a b,
    Incl cg sj ->
    Events.Reduces k (a, CG.FORK b) k' ->
    CG.Reduces cg (a, CG.FORK b) cg' ->
    Reduces sj cg' sj' ->
    List.In (n1, n2) (cg_edges cg') ->
    CanJoin n1 x sj' ->
    length (fst cg) = length sj ->
    FreeInGraph (fst cg) sj ->
    EdgeToIndex cg ->
    CanJoin n2 x sj'.
  Proof.
    intros.
    rename H5 into Heq.
    rename H6 into Hdom.
    rename H7 into Hlt.
    inversion H0; subst; clear H0.
    inversion H9; subst; clear H9.
    inversion H1; subst; clear H1.
    inversion H10; subst; clear H10.
    inversion H2; subst; clear H2.
    apply maps_to_inv_eq in H16; subst.
    apply maps_to_inv_eq in H14; subst.
    simpl in *.
    rename prev into na.
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
      assert (Hx:List.In (fresh (Cons b na :: sj), n2) (cg_edges (vs, es))) by auto.
      apply node_lt_length_left in Hx; auto.
      simpl in Hx.
      unfold NODE.lt, fresh in *; simpl in *.
      inversion Heq.
      omega.
  Qed.

  Let incl_join:
    forall cg cg' sj sj' k k' x n1 n2 a b,
    Incl cg sj ->
    Events.Reduces k (a, CG.JOIN b) k' ->
    CG.Reduces cg (a, CG.JOIN b) cg' ->
    Reduces sj cg' sj' ->
    List.In (n1, n2) (cg_edges cg') ->
    CanJoin n1 x sj' ->
    length (fst cg) = length sj ->
    FreeInGraph (fst cg) sj ->
    EdgeToIndex cg ->
    CanJoin n2 x sj'.
  Proof.
    intros.
    rename H5 into Heq.
    rename H6 into Hdom.
    rename H7 into Hlt.
    inversion H0; subst; clear H0.
    inversion H9; subst; clear H9.
    inversion H1; subst; clear H1.
    inversion H8; subst; clear H8.
    inversion H2; subst; clear H2.
    apply maps_to_inv_eq in H14; subst.
    apply maps_to_inv_eq in H10; subst.
    assert (ty = b) by eauto using maps_to_fun_1; subst; clear H18.
    apply maps_to_neq in H12; auto.
    simpl in *.
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
    Incl cg sj ->
    Events.Reduces k (a, CG.CONTINUE) k' ->
    CG.Reduces cg (a, CG.CONTINUE) cg' ->
    Reduces sj cg' sj' ->
    List.In (n1, n2) (cg_edges cg') ->
    CanJoin n1 x sj' ->
    length (fst cg) = length sj ->
    FreeInGraph (fst cg) sj ->
    EdgeToIndex cg ->
    CanJoin n2 x sj'.
  Proof.
    intros.
    rename H5 into Heq.
    rename H6 into Hdom.
    rename H7 into Hlt.
    inversion H0; subst; clear H0.
    inversion H1; subst; clear H1.
    inversion H2; subst; clear H2.
    apply maps_to_inv_eq in H7; subst.
    simpl in *.
    rename prev into na.
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

  Lemma incl_reduces:
    forall sj cg k sj' cg' k' e,
    Incl cg sj ->
    Events.Reduces k e k' ->
    CG.Reduces cg e cg' ->
    Reduces sj cg' sj' ->
    length (fst cg) = length sj ->
    FreeInGraph (fst cg) sj ->
    EdgeToIndex cg ->
    Incl cg' sj'.
  Proof.
    intros.
    unfold Incl; intros.
    destruct e as (a, [b|b|]).
    - eauto.
    - eauto.
    - eauto.
  Qed.

  Let hb_edge_in:
    forall cg sj n1 n2 x,
    Incl cg sj ->
    CanJoin n1 x sj ->
    HB_Edge cg (n1, n2) ->
    CanJoin n2 x sj.
  Proof.
    intros.
    rewrite hb_edge_spec in *.
    eauto.
  Qed.

  Let InEdge sj x (e:node*node) := CanJoin (fst e) x sj /\ CanJoin (snd e) x sj.

  Let in_edge:
    forall sj cg a b x,
    Incl cg sj ->
    HB_Edge cg (a, b) ->
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
    Walk2 (HB_Edge cg) a b w ->
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
    HB cg n1 n2 ->
    CanJoin n2 x sj.
  Proof.
    intros.
    unfold HB in *.
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

  Lemma incl_nil:
    forall a,
    Incl (a :: nil, nil) (Nil :: nil).
  Proof.
    intros.
    unfold Incl.
    intros.
    simpl in *.
    contradiction.
  Qed.

End Incl.

Section SJ.

  Let cg_reduces_to_reduces:
    forall k k' cg e cg' sj,
    Events.Reduces k e k' ->
    CG.Reduces cg e cg' ->
    EdgeToKnows (fst cg) sj k ->
    exists sj', Reduces sj cg' sj'.
  Proof.
    intros.
    rename H1 into He.
    inversion H0; subst; clear H0.
    - inversion H3; subst; clear H3.
      inversion H; subst; clear H.
      inversion H8; subst; clear H8.
      assert (prev = nx) by eauto using maps_to_fun_2; subst.
      eauto using reduces_fork.
    - inversion H2; subst; clear H2.
      inversion H; subst; clear H.
      inversion H7; subst; clear H7.
      assert (curr = nx) by eauto using maps_to_fun_2; subst.
      assert (Hk: Knows vs sj (x, y)) by eauto.
      inversion Hk; subst; clear Hk.
      assert (nx0 = prev) by eauto using maps_to_fun_2; subst.
      eauto using reduces_join.
    - inversion H; subst; clear H.
      simpl in *.
      eauto using reduces_continue.
  Qed.

  Inductive SJ cg k sj: Prop :=
  | sj_def:
    length (fst cg) = length sj ->
    FreeInGraph (fst cg) sj ->
    KnowsToEdge (fst cg) sj k ->
    EdgeToKnows (fst cg) sj k ->
    Incl cg sj ->
    EdgeToIndex cg ->
    SJ cg k sj.

  (** Main theorem of SJ *)

  Lemma sj_reduces:
    forall sj cg k sj' cg' k' e,
    SJ cg k sj ->
    Events.Reduces k e k' ->
    CG.Reduces cg e cg' ->
    Reduces sj cg' sj' ->
    SJ cg' k' sj'.
  Proof.
    intros.
    inversion H.
    apply sj_def; eauto 2 using reduces_edge_to_index, length_reduces,
    free_in_graph_reduces, knows_to_edge_reduces, edge_to_knows_reduces, incl_reduces.
  Qed.

  Lemma sj_make_cg:
    forall a,
    SJ (make_cg a) nil (Nil :: nil).
  Proof.
    intros.
    apply sj_def; auto using make_edge_to_index; unfold make_cg; simpl; auto
    using free_in_graph_nil, knows_to_edge_nil, incl_nil, edge_to_knows_nil.
  Qed.

  Lemma sj_spec:
    forall a t cg k,
    CG.Run a t cg ->
    Events.Run t k ->
    exists sj, SJ cg k sj.
  Proof.
    induction t; intros. {
      inversion H; subst; clear H.
      inversion H0; subst; clear H0.
      eauto using sj_make_cg.
    }
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    eapply IHt in H3; eauto.
    destruct H3 as (sj, Hsj).
    assert (Hr: exists sj', Reduces sj cg sj'). {
      inversion Hsj.
      eauto.
    }
    destruct Hr as (sj', Hr).
    eauto using sj_reduces.
  Qed.

  Theorem hb_spec:
    forall cg k n1 n2 x sj,
    SJ cg k sj ->
    CanJoin n1 x sj ->
    HB cg n1 n2 ->
    CanJoin n2 x sj.
  Proof.
    intros.
    inversion H; eauto using incl_hb.
  Qed.

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
End SJ.

