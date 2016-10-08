Require Import Coq.Lists.List.
Require Import Aniceto.Graphs.Graph.
Require Import Aniceto.Graphs.FGraph.
Require Import Omega.

Require Import CG.
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

  Inductive Reduces: known_set -> CG.event -> known_set -> Prop :=
  | reduces_fork:
    forall k k' x y,
    SafeJoins.CheckOp k {| op_t := FORK; op_src := x; op_dst := y |} k' ->
    Reduces k (x, CG.FORK y) k'
  | reduces_join:
    forall k k' x y,
    SafeJoins.CheckOp k {| op_t := JOIN; op_src := x; op_dst := y |} k' ->
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

  Ltac simpl_red :=
  repeat match goal with
  | [ H : Reduces _ (_, CG.JOIN _) _ |- _ ] =>
     inversion H; subst; clear H;
     match goal with
     | [ H1 : SafeJoins.CheckOp _ {| op_t := JOIN; op_src := _; op_dst := _ |} _ |- _ ] =>
       inversion H1; subst; clear H1
     end
  | [ H: Reduces _ (_, CONTINUE) _ |- _ ] =>
    inversion H; subst; clear H
  | [ H : Reduces _ (_, CG.FORK _) _ |- _ ] =>
     inversion H; subst; clear H;
     match goal with
     | [ H1 : SafeJoins.CheckOp _ {| op_t := FORK; op_src := _; op_dst := _ |} _ |- _ ] =>
       inversion H1; subst; clear H1
     end
  end.

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

  Ltac simpl_red :=
  repeat match goal with
  | [ H : Reduces _ ?cg _, H0 : CG.Reduces _ (_, CG.FORK _) ?cg |- _ ] =>
    CG.simpl_red; inversion H; subst; clear H
  | [ H : Reduces _ ?cg _, H0 : CG.Reduces _ (_, CG.JOIN _) ?cg |- _ ] =>
    inversion H0; subst; clear H0;
    match goal with
    | [ H1: CG.Reduces _ (_, CG.CONTINUE) _ |- _ ] => inversion H1; subst; clear H1
    end;
    inversion H; subst; clear H;
    simpl_node
  | [ H : Reduces _ ?cg _, H0 : CG.Reduces _ (_, CG.CONTINUE) ?cg |- _ ] =>
    CG.simpl_red; inversion H; subst; clear H
  end.

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
    CG.simpl_red.
    inversion_clear H0.
    simpl in *.
    apply knows_def with (nx:=fresh (x::vs)); auto using maps_to_eq.
    inversion_clear H1.
    clear nx; rename nx0 into nx.
    simpl_node.
    assert (R: fresh (x :: vs) = fresh (Cons y nx :: sj))
    by (unfold fresh; simpl; auto); rewrite R.
    eauto using can_join_copy, can_join_cons.
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
    simpl_red.
    simpl in *.
    apply knows_def with (nx:=fresh sj).
    - apply maps_to_length_rw in Heq.
      rewrite <- Heq.
      auto using maps_to_eq, maps_to_cons.
    - auto using can_join_cons, can_join_eq.
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

  Lemma knows_to_in:
    forall x y vs sj,
    Knows vs sj (x, y) ->
    List.In x vs.
  Proof.
    intros.
    inversion H; subst.
    eauto using maps_to_to_in.
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
    simpl_red.
    simpl in *.
    assert (b <> y). {
      unfold not; intros; subst.
      contradiction H5.
      eauto using knows_to_free.
    }
    destruct (tid_eq_dec a x). {
      subst.
      auto using knows_cons_neq, knows_neq.
    }
    assert (a <> y). {
      unfold not; intros; subst.
      contradiction H5.
      eauto using knows_to_in.
    }
    auto using knows_neq.
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
    simpl_red.
    simpl in *.
    eauto using knows_append_right.
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
    simpl_red.
    simpl in *.
    destruct (tid_eq_dec x a). {
      subst.
      auto using knows_append_left.
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
      subst.
      eauto using knows_copy.
    }
    auto using knows_neq.
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
    simpl_red.
    simpl in *.
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
    destruct e as (?,[]); simpl_red; simpl in *; auto.
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
    simpl_red.
    inversion H3; subst; clear H3.
    simpl in *; clear nx.
    rename nx0 into na.
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
    apply maps_to_lt in H12.
    simpl in *.
    unfold fresh, NODE.lt in *.
    simpl in *.
    inversion Heq as (Hx).
    rewrite Hx in *.
    omega.
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
    simpl_red; simpl in *.
    Events.simpl_red.
    apply maps_to_length_rw in Heq.
    inversion H3; subst; clear H3.
    apply maps_to_inv in H2; destruct H2 as [(?,?)|(?,mt)]. {
      subst.
      rewrite Heq in *.
      apply can_join_inv_append in H5.
      destruct H5;
      eauto using knows_def, in_join, in_join_2.
    }
    inversion H5; subst; clear H5.
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
    Events.simpl_red.
    simpl_red.
    simpl in *.
    rename k' into k.
    rename prev into nx.
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
    EdgeToNode (vs, es) ->
    ~ List.In (fresh vs, n) (map e_edge es).
  Proof.
    intros.
    intuition.
    assert (Hx:List.In (fresh vs, n) (cg_edges es)) by auto.
    eapply node_lt_length_left in Hx; eauto.
    simpl in Hx.
    unfold NODE.lt in *.
    omega.
  Qed.

  Let incl_fork:
    forall (cg:computation_graph) cg' sj sj' k k' x n1 n2 a b,
    Incl (snd cg) sj ->
    Events.Reduces k (a, CG.FORK b) k' ->
    CG.Reduces cg (a, CG.FORK b) cg' ->
    Reduces sj cg' sj' ->
    List.In (n1, n2) (cg_edges (snd cg')) ->
    CanJoin n1 x sj' ->
    length (fst cg) = length sj ->
    FreeInGraph (fst cg) sj ->
    EdgeToNode cg ->
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
      assert (Hx:List.In (fresh (Cons b prev :: sj), n2) (cg_edges es)) by auto.
      eapply node_lt_length_left in Hx; eauto.
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
    Reduces sj cg' sj' ->
    List.In (n1, n2) (cg_edges (snd cg')) ->
    CanJoin n1 x sj' ->
    length (fst cg) = length sj ->
    FreeInGraph (fst cg) sj ->
    EdgeToNode cg ->
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
    Reduces sj cg' sj' ->
    List.In (n1, n2) (cg_edges (snd cg')) ->
    CanJoin n1 x sj' ->
    length (fst cg) = length sj ->
    FreeInGraph (fst cg) sj ->
    EdgeToNode cg ->
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

  Lemma incl_reduces:
    forall sj cg k sj' cg' k' e,
    Incl (snd cg) sj ->
    Events.Reduces k e k' ->
    CG.Reduces cg e cg' ->
    Reduces sj cg' sj' ->
    length (fst cg) = length sj ->
    FreeInGraph (fst cg) sj ->
    EdgeToNode cg ->
    Incl (snd cg') sj'.
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
    Incl nil (Nil :: nil).
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
    inversion H0; subst; clear H0; Events.simpl_red; CG.simpl_red.
    - eauto using reduces_fork.
    - assert (Hk: Knows vs sj (x, y)) by eauto.
      inversion Hk; subst; clear Hk.
      simpl_node.
      eauto using reduces_join, maps_to_cons.
    - eauto using reduces_continue.
  Qed.

  Inductive SJ cg k sj: Prop :=
  | sj_def:
    length (fst cg) = length sj ->
    FreeInGraph (fst cg) sj ->
    KnowsToEdge (fst cg) sj k ->
    EdgeToKnows (fst cg) sj k ->
    Incl (snd cg) sj ->
    EdgeToNode cg ->
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
    apply sj_def; eauto 2 using reduces_edge_to_node, length_reduces,
    free_in_graph_reduces, knows_to_edge_reduces, edge_to_knows_reduces, incl_reduces.
  Qed.

  Lemma cg_sj_reduces_to_sj_reduces:
    forall sj cg k sj' cg' e,
    SJ cg k sj ->
    CG.Reduces cg e cg' ->
    Reduces sj cg' sj' ->
    exists k', Events.Reduces k e k'.
  Proof.
    intros.
    destruct e as (x,[]).
    - rename t into y.
      exists (fork x y k).
      simpl_red.
      apply Events.reduces_fork.
      apply SafeJoins.check_fork; auto.
      unfold not; intros.
      contradiction H5.
      destruct H0 as ((v1,v2), (He,Hp)).
      inversion H.
      apply H3 in He.
      simpl in *.
      destruct Hp; subst; simpl in *.
      + eauto using knows_to_in.
      + apply knows_to_free in He.
        auto.
    - simpl_red.
      exists (join x t k).
      apply Events.reduces_join.
      apply SafeJoins.check_join; auto.
      inversion H; simpl in *.
      apply H2.
      eauto using knows_def.
    - simpl_red.
      eauto using Events.reduces_continue.
  Qed.

  Lemma sj_reduces_alt:
    forall sj cg k sj' cg' e,
    SJ cg k sj ->
    CG.Reduces cg e cg' ->
    Reduces sj cg' sj' ->
    exists k', SJ cg' k' sj'.
  Proof.
    intros.
    assert (Hx: exists k', Events.Reduces k e k'). {
      eauto using cg_sj_reduces_to_sj_reduces.
    }
    destruct Hx as (k', Hx).
    exists k'.
    eauto using sj_reduces.
  Qed.

  Lemma sj_make_cg:
    forall a,
    SJ (make_cg a) nil (Nil :: nil).
  Proof.
    intros.
    apply sj_def; auto using make_edge_to_node; unfold make_cg; simpl; auto
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
    HB (snd cg) n1 n2 ->
    CanJoin n2 x sj.
  Proof.
    intros.
    inversion H; eauto using incl_hb.
  Qed.

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

  Let can_join_to_node_0:
    forall n x sj,
    CanJoin n x sj ->
    Node n sj.
  Proof.
    intros.
    induction H; auto using node_cons, node_eq.
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

  Let can_join_to_in:
    forall vs es k sj x n,
    SJ (vs,es) k sj ->
    CanJoin n x sj ->
    List.In x vs.
  Proof.
    intros.
    inversion H.
    simpl in *.
    eauto using can_join_to_free.
  Qed.

  Inductive HBCanJoin (cg:computation_graph) : node -> tid -> Prop :=
  | hb_can_join_def:
    forall y nx ny,
    SpawnPoint y ny cg ->
    HB (snd cg) ny nx ->
    HBCanJoin cg nx y.

  Definition KnowsEquiv sj cg :=
  forall n x, CanJoin n x sj <-> HBCanJoin cg n x.

  Let hb_can_join_fork:
    forall vs es n z y e,
    HBCanJoin (vs, es) n z ->
    HBCanJoin (y :: vs, F e :: es) n z.
  Proof.
    intros.
    inversion H; subst; clear H;
    simpl in *;
    eauto using hb_can_join_def, spawn_point_fork, hb_impl_cons.
  Qed.

  Let hb_can_join_continue:
    forall vs es n z y e,
    HBCanJoin (vs, es) n z ->
    HBCanJoin (y :: vs, C e :: es) n z.
  Proof.
    intros.
    inversion H; subst; clear H;
    simpl in *;
    eauto using hb_can_join_def, spawn_point_continue, hb_impl_cons.
  Qed.

  Let hb_can_join_join:
    forall vs es n y z e,
    HBCanJoin (y :: vs, es) n z ->
    HBCanJoin (y :: vs, J e :: es) n z.
  Proof.
    intros.
    inversion H; subst; clear H;
    simpl in *.
    eauto using hb_can_join_def, spawn_point_join, hb_impl_cons.
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

  Definition FirstHB (cg:computation_graph) :=
    forall x n1 n2,
    First x n1 (fst cg) ->
    MapsTo x n2 (fst cg) ->
    n1 <> n2 ->
    HB (snd cg) n1 n2.

  Let hb_can_join_spawn:
    forall n x y vs es,
    ~ List.In y vs ->
    MapsTo x n vs ->
    HBCanJoin (y :: x :: vs, F (n, fresh (x :: vs)) :: C (n, fresh vs) :: es) (fresh vs) y.
  Proof.
    intros.
    apply hb_can_join_def with (ny:=n). {
      auto using spawn_point_eq, spawn_point_fork, spawn_point_continue.
    }
    simpl.
    eauto using hb_edge_to_hb, hb_edge_def, edge_eq, in_cons, in_eq.
  Qed.

  Let hb_can_join_trans:
    forall cg n n' x,
    HBCanJoin cg n x ->
    HB (snd cg) n n' ->
    HBCanJoin cg n' x.
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using hb_can_join_def, hb_trans.
  Qed.

  Let can_join_pres_fork:
    forall n cg sj z sj' cg' x y,
    length (fst cg) = length sj ->
    KnowsEquiv sj cg ->
    CG.Reduces cg (x, CG.FORK y) cg' ->
    Reduces sj cg' sj' ->
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
    destruct H2 as [(?,Hc)|[(?,Hc)|(?,?)]]; subst; try (apply Hind in Hc;
      apply hb_can_join_trans with (n:=nz); simpl;
      eauto using hb_edge_to_hb, hb_edge_def, edge_eq, in_cons, in_eq).
    apply maps_to_length_rw in Heq.
    rewrite <- Heq in *.
    simpl_node.
  Qed.

  Let can_join_pres_fork_2:
    forall n cg sj z sj' cg' x y,
    length (fst cg) = length sj ->
    KnowsEquiv sj cg ->
    CG.Reduces cg (x, CG.FORK y) cg' ->
    Reduces sj cg' sj' ->
    HBCanJoin cg' n z ->
    CanJoin n z sj'.
  Proof.
    intros.
    simpl_red.
    inversion H3; subst; clear H3.
    simpl in *.
    rename ny0 into nz.
    rewrite fresh_cons_rw_next in *.
    destruct (node_eq_dec n (node_next (fresh sj))). {
      subst.
      apply maps_to_length_rw in H.
      rewrite <- H in H2.
      rewrite <- fresh_cons_rw_next with (x:=Cons y prev).
      apply can_join_copy.
      destruct (tid_eq_dec z y). {
        subst.
        apply can_join_cons.
      }
    }
    apply can_join_cons.
    apply can_join_copy.
  Qed.

  Let can_join_pres_1:
    forall sj cg sj' cg' e n x,
    length (fst cg) = length sj ->
    FirstHB cg ->
    KnowsEquiv sj cg ->
    CG.Reduces cg e cg' ->
    Reduces sj cg' sj' ->
    CanJoin n x sj' ->
    HBCanJoin cg' n x.
  Proof.
    intros ? ? ? ? ? ? ?.
    intros Heq Hfhb; intros.
    destruct e as (z,[]).
    - rename t into y.
      simpl_red; simpl in *.
      }
  Qed.

  Let can_join_hb_preservation:
    forall sj cg sj' cg' e,
    CanJoinSJ_CG sj cg ->
    CG.Reduces cg e cg' ->
    Reduces sj cg' sj' ->
    CanJoinSJ_CG sj' cg'.
  Proof.
    intros.
    unfold CanJoinSJ_CG.
    intros.
    split; intros. {
    }
    destruct e as (z,[]).
    - rename t into y.
      simpl_red; simpl in *.
      inversion H3; subst; clear H3. {
        assert (nx = fresh (z :: vs)). {
          destruct nx.
          unfold fresh.
          simpl in *.
          subst.
          trivial.
        }
        subst.
        assert (ny = fresh (z::vs)). {
          inversion H2; subst; clear H2. {
            unfold fresh in *.
            simpl in *.
            contradiction H7.
            eapply can_join_to_in in H8; eauto.
          }
        }
        inversion H2; subst.
        apply can_join_inv_copy_1 in H2.
      }
      unfold CanJoinToHB; intros; simpl in *.
      inversion H2; subst; clear H2. {
        inversion H5; subst; clear H5. {
          inversion H
        }
      }
    inversion H
  Qed.

  Let sj_first_can_join:
    forall sj vs es x k ny nx,
    SJ (vs,es) k sj ->
    CanJoin ny x sj ->
    First x nx vs ->
    HB es nx ny.
  Proof.
    induction sj; intros. {
      inversion H0.
    }
    inversion H0; subst; clear H0.
    - 
    induction H0.
    assert (Node ny vs) by eauto.
    eapply can_join_to_node_cg in H0; eauto.
    inversion H.
    apply node_tr with (b:=vs) in H0; auto.
  Qed.
  *)
End SJ.



