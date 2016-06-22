Require Import Coq.Lists.List.
Require Import Aniceto.Graphs.Graph.
Require Import Aniceto.Graphs.FGraph.

Require Import CG.
Require Import SafeJoins.
Require Import Tid.
Require Import Bijection.

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

Section HB.

  Notation node := nat.

  Notation known_set := (list (tid * tid)).

  Inductive command :=
  | Cons: tid -> node -> command
  | Copy : node -> command
  | Append: node -> node -> command.

  Definition cg_safe_joins := list command.

  Inductive CanJoin : node -> tid -> cg_safe_joins -> Prop :=
  | can_join_cons:
    forall l n c x,
    CanJoin n x l ->
    CanJoin n x (c :: l)
  | can_join_eq:
    forall l n x,
    CanJoin (length l) x (Cons x n::l)
  | can_join_neq:
    forall l y n x,
    CanJoin n x l ->
    x <> y ->
    CanJoin (length l) x (Cons y n :: l)
  | can_join_copy:
    forall n l x,
    CanJoin n x l ->
    CanJoin (length l) x (Copy n :: l)
  | can_join_append_left:
    forall x n' l n,
    CanJoin n x l ->
    CanJoin (length l) x (Append n n' :: l)
  | can_join_append_right:
    forall n' l n x,
    CanJoin n' x l ->
    CanJoin (length l) x (Append n n' :: l).

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

  | e_safe_joins_continue:
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

  Let can_join_absurd_le:
    forall sj n b,
    length sj <= n ->
    ~ CanJoin n b sj.
  Proof.
    unfold not; intros.
    induction H0; simpl in *; auto with *.
  Qed.

  Let can_join_le:
    forall x n sj c,
    n < length sj ->
    CanJoin n x (c :: sj) ->
    CanJoin n x sj.
  Proof.
    intros.
    inversion H0; subst; try apply Lt.lt_irrefl in H; auto; contradiction.
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
    inversion H1; subst; simpl in *; clear H1.
    assert (nx <> curr). {
      unfold not; intros; subst.
      assert (curr = length vs) by eauto using maps_to_inv_eq.
      subst.
      apply maps_to_absurd_length in H8.
      contradiction.
    }
    assert (nx0 = nx) by eauto using maps_to_fun_2; subst.
    assert (ny = length (x::vs)) by eauto using maps_to_inv_eq; subst.
    simpl in *.
    rewrite Heq in *.
    assert (R: S (length sj) = length (Cons y nx :: sj)) by auto; rewrite R.
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
    apply knows_def with (nx:=curr).
    - simpl.
      auto using maps_to_cons.
    - assert (ny <> curr). {
        intuition; subst.
        eapply maps_to_absurd_cons with (y:=y) in H12; auto.
      }
      assert (curr = length sj). {
        simpl in *.
        rewrite <- Heq.
        eauto using maps_to_inv_eq.
      }
      subst.
      auto using can_join_cons, can_join_eq.
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
    assert (nx' = length vs) by eauto using maps_to_inv_eq; subst.
    assert (ny = length (x::vs)) by eauto using maps_to_inv_eq; subst.
    assert (b <> y). {
      unfold not; intros; subst.
      contradiction H5.
      eauto using Hdom, can_join_to_free.
    }
    destruct (tid_eq_dec a x). {
      subst.
      assert (na = nx) by eauto using maps_to_fun_2; subst; clear H8.
      apply knows_def with (nx:=length vs).
      - simpl.
        eauto using maps_to_cons.
      - rewrite Heq.
        eauto using can_join_neq, can_join_cons.
    }
    assert (a <> y). {
      unfold not; intros; subst.
      contradiction H5.
      eauto using maps_to_to_in.
    }
    assert (CanJoin na b (Copy nx :: Cons y nx :: sj)). {
      eauto using can_join_cons, maps_to_lt.
    }
    eauto using knows_def, maps_to_cons.
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
    assert (prev = nx) by eauto using maps_to_fun_2; subst; clear H12.
    inversion H2; subst; clear H2; simpl in *; rename nx0 into ny'.
    apply knows_def with (nx:=curr); simpl; auto.
    assert (curr = length sj) by
    eauto using maps_to_inv_eq; subst.
    apply maps_to_neq in H10; auto.
    assert (ny' = ny) by eauto using maps_to_fun_2; subst.
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
    clear H8. (* MapsTo x curr (x :: vs) *)
    assert (ty = y) by eauto using maps_to_fun_1; subst;
    clear H16. (* MapsTo ty ny (x :: vs) *)
    simpl in *.
    destruct (tid_eq_dec x a). {
      subst.
      apply maps_to_neq in H10; auto.
      assert (curr = length sj) by eauto using maps_to_inv_eq; subst.
      apply knows_def with (nx:=length sj); auto.
      inversion H2; subst; clear H2.
      inversion H1; subst; clear H1.
      assert (nx0 = nx) by eauto using maps_to_fun_2; subst.
      clear H3. (* MapsTo a nx vs *)
      assert (prev = nx) by eauto using maps_to_fun_2; subst.
      clear H17. (* In y nx sj *)
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
      apply knows_def with (nx:=length vs); auto using maps_to_eq.
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

  Let edge_to_knows_preserves:
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

  (* -------------------------------------------------- *)

  Let length_preserves:
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

  Let free_in_graph_preserves:
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
    apply maps_to_inv_eq in H16; subst.
    apply maps_to_inv_eq in H13; subst.
    inversion H2; subst; clear H2.
    inversion H3; subst; clear H3.
    clear H11.
    rename nx into na.
    rename prev into nx.
    inversion H4; subst; clear H4. {
      inversion H2; subst; clear H2. {
        assert (rw: length (x :: vs) = length (Cons y nx :: sj)) by (simpl in *; auto).
        rewrite rw in *.
        inversion H9; subst; clear H9.
        - apply can_join_absurd_le in H3; simpl; auto; contradiction.
        - apply nat_absurd_succ in H1; contradiction.
        - apply nat_absurd_succ in H0; contradiction.
      }
      inversion H10; subst; clear H10. {
        rewrite Heq in *.
        inversion H9; subst; clear H9.
        - apply can_join_absurd_le in H3; simpl; auto; contradiction.
        - auto using in_fork_5.
        - eauto using knows_def, in_fork.
      }
      inversion H9; subst; clear H9.
      - eauto using knows_def, in_fork.
      - rewrite <- Heq in *.
        apply maps_to_absurd_length in H11.
        contradiction.
      - rewrite <- Heq in *.
        apply maps_to_absurd_length in H11.
        contradiction.
    }
    assert (nx < length vs) by eauto using maps_to_lt.
    rewrite Heq in *.
    apply can_join_le in H9; auto.
    inversion H2; subst; clear H2. {
      eauto using in_fork_2, knows_def.
    }
    apply maps_to_lt in H11.
    simpl in *.
    rewrite Heq in *.
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
    clear H14.
    assert (ty = y) by eauto using maps_to_fun_1; subst; clear H17.
    rename nx into nb.
    rename prev into nx.
    inversion H4; subst; clear H4.
    - inversion H2; subst; clear H2. {
        rewrite Heq in *.
        apply can_join_absurd_le in H7; auto.
        contradiction.
      }
      eauto using in_join, knows_def.
    - assert (curr = length vs) by eauto using maps_to_inv_eq; subst.
      assert (x = a). {
        rewrite Heq in *.
        eauto using maps_to_fun_1.
      }
      subst; clear H9.
      eauto using knows_def, in_join.
    - assert (curr = length vs) by eauto using maps_to_inv_eq; subst.
      assert (x = a). {
        rewrite Heq in *.
        eauto using maps_to_fun_1.
      }
      subst; clear H9.
      inversion H11; subst; clear H11. {
        contradiction H5.
        trivial.
      }
      eauto using knows_def, in_join_2.
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
    assert (curr = length vs) by eauto using maps_to_inv_eq; subst; clear H7.
    inversion H3; subst; clear H3.
    inversion H2; subst; clear H2. {
      rewrite Heq in *.
      inversion H6; subst; clear H6. {
        apply can_join_absurd_le in H3; auto.
        contradiction.
      }
      eauto using knows_def.
    }
    rename nx0 into nb.
    assert (nb < length vs) by eauto using maps_to_lt.
    eauto using knows_def.
  Qed.

  Let knows_to_edge_preserves:
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

  Inductive SJ vs k sj: Prop :=
  | sj_def:
    length vs = length sj ->
    FreeInGraph vs sj ->
    KnowsToEdge vs sj k ->
    EdgeToKnows vs sj k ->
    SJ vs k sj.

  (** Main theorem of SJ *)

  Lemma sj_preserves:
    forall sj cg k sj' cg' k' e,
    SJ (fst cg) k sj ->
    Events.Reduces k e k' ->
    CG.Reduces cg e cg' ->
    Reduces sj cg' sj' ->
    SJ (fst cg') k' sj'.
  Proof.
    intros.
    inversion H.
    apply sj_def; eauto.
  Qed.

  (* ------------------------------------------ *)

  Definition Incl cg sj :=
  forall n1 n2 x,
  List.In (n1, n2) (cg_edges cg) ->
  CanJoin n1 x sj ->
  CanJoin n2 x sj.

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
    apply maps_to_inv_eq in H17; subst.
    apply maps_to_inv_eq in H14; subst.
    simpl in *.
    rename prev into na; clear H16 H7.
    destruct H3 as [R|[R|?]]; try (inversion R; subst; clear R).
    - assert (R: S (length vs) = length (Cons b n1 :: sj)) by
      (simpl; rewrite Heq in *; auto).
      rewrite R.
      inversion H4; clear H4. {
        subst.
        assert (n1 < length vs) by eauto using maps_to_lt.
        rewrite Heq in *.
        apply can_join_le in H3; auto.
        apply can_join_copy.
        subst.
        destruct (tid_eq_dec x b). {
          subst.
          auto using can_join_cons.
        }
        auto using can_join_cons.
      }
      simpl in *.
      rewrite <- H0 in *.
      subst.
      simpl in *.
      subst.
      rewrite <- Heq in *.
      apply maps_to_lt in H12.
      apply Lt.lt_asym in H12.
      contradiction H12; auto.
    - rewrite Heq.
      apply can_join_cons.
      assert (CanJoin n1 x sj). {
        inversion H4; clear H4.
        - subst.
          inversion H3; subst; clear H3; auto.
          rewrite <- Heq in *.
          apply maps_to_lt in H12.
          apply Lt.lt_irrefl in H12.
          contradiction.
        - rewrite H1 in *; clear H1.
          subst.
          apply can_join_absurd_le in H3; auto.
          contradiction.
      }
      clear H4.
      assert (b <> x). {
        unfold not; intros; subst.
        contradiction H9.
        eauto.
      }
      auto using can_join_neq.
    - inversion H4; subst; clear H4. {
        inversion H5; subst; clear H5.
        - eauto using can_join_cons.
        - rewrite <- Heq in *.
          assert (Hx:List.In (length vs, n2) (cg_edges (vs, es))) by auto.
          apply node_lt_length_left in Hx; auto.
          simpl in Hx.
          apply Lt.lt_irrefl in Hx; contradiction.
        - rewrite <- Heq in *.
          assert (Hx:List.In (length vs, n2) (cg_edges (vs, es))) by auto.
          apply node_lt_length_left in Hx; auto.
          simpl in Hx.
          apply Lt.lt_irrefl in Hx; contradiction.
      }
      simpl in *.
      rewrite <- Heq in *.
      assert (Hx:List.In (S (length vs), n2) (cg_edges (vs, es))) by auto.
      apply node_lt_length_left in Hx; auto.
      simpl in Hx.
      omega.
  Qed.

  Let incl_preserve:
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
    - 
  Qed.


  (* ----------------------------------- *)

  Let flat_sj := MN.t (list tid).

  Inductive Flatten : cg_safe_joins -> flat_sj -> Prop :=
  | flatten_nil:
    Flatten nil (MN.empty (list tid))
  | flatten_cons:
    forall l m x y z zs,
    Flatten l m ->
    MN.MapsTo z zs m ->
    Flatten ((x,Cons y z)::l) (MN.add x (y::zs) m)
  | flatten_copy:
    forall l m x y ys,
    Flatten l m ->
    MN.MapsTo y ys m ->
    Flatten ((x,Copy y)::l) (MN.add x ys m)
  | flatten_append:
    forall l m x y ys z zs,
    Flatten l m ->
    MN.MapsTo y ys m ->
    MN.MapsTo z zs m ->
    Flatten ((x,Append y z)::l) (MN.add x (ys ++ zs) m).

  Definition SafeJoins (cg:computation_graph) sj := ESafeJoins (fst cg) (snd cg) sj.



  Inductive MapsTo e :  (known_set * known_set) -> list cg_edge -> known_history -> Prop :=
  | maps_to_eq:
    forall e' es h,
    MapsTo e e' (e::es) (e'::h)
  | maps_to_cons:
    forall e' e'' es h p,
    MapsTo e e' es h ->
    MapsTo e e' (e''::es) (p::h).

  Definition Dom cg k:=
    forall x y t,
    TaskEdge cg t (x, y) ->
    In (FGraph.Edge k) x.

  Definition WFEdges (cg:computation_graph) (h:known_history) :=
  forall e x y z nx ny k k',
  List.In e (snd cg) ->
  e_edge e = (nx, ny) ->
  MapsTo e (k, k') (snd cg) h ->
  Nodes.MapsTo x nx (cg_nodes cg) ->
  Nodes.MapsTo y ny (cg_nodes cg) ->
  List.In (x, z) k ->
  List.In (y, z) k'.
(*
  Definition CGtoSJ cg k :=
  forall x,
  Graph.In (FGraph.Edge k) x ->
  Nodes.In x (cg_nodes cg).

  Definition ForkInKnown cg k :=
  forall x y,
  TaskEdge cg CG.FORK (x, y) ->
  List.In (x, y) k.
*)
  Let wf_safe_joins_continue:
    forall cg o cg' h,
    WFEdges cg h ->
    CG.op_t o = CG.CONTINUE ->
    CG.Reduces cg o cg' ->
    WFEdges cg' h.
  Proof.
    intros.
    unfold WFEdges in *.
    intros e a b c; intros.
    inversion H1; subst; clear H1; try (inversion H0; clear H0).
    simpl in *.
    destruct H2. {
      subst.
      simpl in *.
      inversion H3; subst; clear H3.
      inversion H4; subst; clear H4. {
        
      }
    }
    
  Qed.

  Let wf_safe_joins_continue:
    forall cg o cg' h,
    Inv cg h ->
    CG.op_t o = CG.CONTINUE ->
    CG.Reduces cg o cg' ->
    Inv cg' h.
  Proof.
    intros.
    rename H0 into Heq0.
    inversion H1; subst; clear H1; subst; inversion Heq0; clear Heq0.
    rename H0 into HL.
    rename H4 into mt_x.
    inversion H3; subst; simpl in *; clear H3.
    unfold c_edge, i_prev, i_curr; simpl.
    remember ( _ :: _ :: l)%list as lx'.
    unfold Inv.
    intros a b c; intros; simpl in *.
    inversion H0; subst; simpl in *; clear H0.
    inversion H9 as [He|He]; clear H9. {
      subst; simpl in *.
      inversion H10; subst; simpl in *; clear H10.
      apply H
      assert (kx = ky) by (unfold KnownOf in *; eauto using MN_Facts.MapsTo_fun).
      assumption.
    }
    assert (Edge (vs, es) (e_t e) (e_edge e)) by eauto using edge_def.
    destruct e; destruct e_edge; simpl in *.
    inversion H9; subst.
    assert (TaskEdge (vs, es) e_t (node_task na, b)). {
      assert (RW: b = node_task {| node_task := b; node_id := nbi |}) by auto.
      rewrite RW in *.
      auto using task_edge_def.
    }
    eauto.
  Qed.


  Let wf_safe_joins_continue:
    forall cg o cg' k,
    Inv cg k ->
    CG.op_t o = CG.CONTINUE ->
    CG.Reduces cg o cg' ->
    Inv cg' k.
  Proof.
    intros.
    rename H0 into Heq0.
    inversion H1; subst; clear H1; subst; inversion Heq0; clear Heq0.
    rename H0 into HL.
    rename H4 into mt_x.
    inversion H3; subst; simpl in *; clear H3.
    unfold c_edge, i_prev, i_curr; simpl.
    remember ( _ :: _ :: l)%list as lx'.
    unfold Inv.
    intros a b c; intros; simpl in *.
    inversion H3 as (na,(nb,nbi)); subst; clear H3.
    inversion H6; subst; clear H6.
    inversion H8 as [He|He]; clear H8. {
      subst; simpl in *.
      inversion H9; subst; simpl in *; clear H9.
      assumption.
    }
    assert (Edge (vs, es) (e_t e) (e_edge e)) by eauto using edge_def.
    destruct e; destruct e_edge; simpl in *.
    inversion H9; subst.
    assert (TaskEdge (vs, es) e_t (node_task na, b)). {
      assert (RW: b = node_task {| node_task := b; node_id := nbi |}) by auto.
      rewrite RW in *.
      auto using task_edge_def.
    }
    eauto.
  Qed.
(*
  Let wf_safe_joins_continue:
    forall cg o cg' k,
    WellFormedSafeJoins cg k ->
    CG.op_t o = CG.CONTINUE ->
    CG.Reduces cg o cg' ->
    WellFormedSafeJoins cg' k.
  Proof.
    intros.
    inversion H1; subst; clear H1; subst; inversion H0; clear H0.
    rename H2 into HL.
    rename H5 into mt_x.
    inversion H4; subst; simpl in *; clear H4.
    unfold WellFormedSafeJoins.
    intros a b c; intros; simpl in *.
    destruct H0. {
      inversion H0; subst; simpl in *; clear H0.
      assumption.
    }
    rename H4 into Hi.
    assert (Nodes.In c vs). {
      destruct Hi as (nc,(lc,mt)); simpl in *.
      rewrite MT_Facts.add_mapsto_iff in mt.
      destruct mt as [(?,?)|(?,?)];
      subst;
      eauto using Nodes.maps_to_def, Nodes.in_def.
    }
    eauto.
  Qed.
*)
  Variable cg: computation_graph.
  Variable cg': computation_graph.
  Variable k:  list (tid * tid).
  Variable k': list (tid * tid).
  Variable Hdag: DAG.DAG (FGraph.Edge k).
  Variable Hsj: Inv cg k.
  Variable Hdom: Dom cg k.
  Variable Hfk: ForkInKnown cg k.

  Lemma wf_safe_joins_fork:
    forall x y,
    CG.Reduces cg {| CG.op_t := CG.FORK; CG.op_src:=x; CG.op_dst:=y|} cg' ->
    Reduces k {| op_t := FORK; op_src:=x; op_dst:=y|} k' ->
    Inv cg' k'.
  Proof.
    intros.
    inversion H; subst; clear H; subst;
    inversion H2; subst; clear H2.
    rename H1 into HL.
    inversion H0; subst; clear H0.
    inversion H3; subst; clear H3.
    simpl in *.
    rename x0 into x; rename y0 into y.
    unfold Inv, c_edge, f_edge, i_prev, i_curr.
    intros a b c; intros; simpl in *.
    inversion H3 as (na,(nb,nbi)); subst; clear H3.
    inversion H9; subst; clear H9.
    inversion H11 as [He|He]; clear H11. {
      subst; simpl in *.
      inversion H12; subst; simpl in *; clear H12.
      assumption.
    }
    inversion He as [He'|He']; clear He. {
      subst.
      simpl in *.
      inversion H12; subst; clear H12.
      simpl in *.
      apply fork_inv_in in H0.
      destruct H0 as [(?,?)|[(?,?)|?]].
      - subst.
        auto using in_fork.
      - subst.
        contradiction H; trivial.
      - auto using in_fork_2.
    }
    destruct e; destruct e_edge; simpl in *.
    inversion H12; subst; clear H12.
    assert (HT: TaskEdge (vs, es) e_t (node_task na, b)). {
      destruct na; subst; simpl in *.
      eauto using task_edge_eq.
    }
    clear He'.
    remember (node_task na) as a; clear Heqa.
    apply fork_inv_in in H0.
    destruct H0 as [(Hx,Hy)|[(Hx,Hy)|Hx]].
    - subst; contradiction H7.
      apply Hdom in HT.
      assumption.
    - 
      destruct e_t.
      + 
        assert (List.In (node_task na, b) k) by eauto.
        apply in_fork_2 with (y:=c) in H0; eauto.
  Qed.

  Lemma wf_safe_joins_fork:
    forall x y,
    CG.Reduces cg {| CG.op_t := CG.FORK; CG.op_src:=x; CG.op_dst:=y|} cg' ->
    Reduces k {| op_t := FORK; op_src:=x; op_dst:=y|} k' ->
    WellFormedSafeJoins cg' k'.
  Proof.
    intros.
    inversion H; subst; clear H; subst;
    inversion H2; subst; clear H2.
    rename H1 into HL.
    inversion H0; subst; clear H0.
    inversion H3; subst; clear H3.
    simpl in *.
    rename x0 into x; rename y0 into y.
    unfold WellFormedSafeJoins.
    intros a b c; intros; simpl in *.
    destruct H as [He|He]. {
      inversion He; subst; simpl in *; clear He.
      assumption.
    }
    simpl in *.
    destruct He as [He|He']. {
      inversion He; subst; simpl in *; clear He.
      auto using in_fork_3.
    }
    assert (He: HB_Edge (vs,es) (a, b)) by auto; clear He'.
    destruct H3 as (nc,(lc,mt)); simpl in *.
    rewrite MT_Facts.add_mapsto_iff in mt.
    destruct mt as [(Hx,Hy)|(x_neq_c,mt)]. {
      inversion Hy; subst; clear Hy.
      assert (Nodes.In c vs) by
      eauto using Nodes.maps_to_def, Nodes.in_def.
      apply fork_inv_in in H0.
      destruct H0 as [(?,?)|[(?,?)|X]].
      - assert (X:= Hdag c).
        contradiction X.
        auto using edge_to_reaches.
      - subst.
        contradiction H2; auto.
      - eauto using in_fork.
    }
    rewrite MT_Facts.add_mapsto_iff in mt.
    destruct mt as [(Hx,Hy)|(y_neq_c,mt)]. {
      subst.
      inversion Hy; subst; clear Hy.
      apply in_fork_4 in H0; auto.
      subst.
      clear x_neq_c.
      destruct HL as (HL).
      rewrite hb_edge_spec in He.
      destruct He as (e, (Hi,Hp)).
      simpl in *.
      inversion Hp; subst; clear Hp.
      destruct t.
      - assert (Ht: TaskEdge (vs,es) CG.FORK (node_task a, node_task b))
        by eauto using task_edge_def, edge_def; clear Hi.
        apply Hfk in Ht.
        apply in_fork_2 with (y:=c) in Ht.
        apply in_fork.
        assert (List.In (c, node_task a) k) by eauto.
    }


    apply fork_inv_in in H0.
    destruct H0 as [(?,?)|[(?,?)|X]].
    - subst.
      assert (Hn : Nodes.In c vs). {
        assert (Hi: Graph.In (FGraph.Edge k) c) by eauto using in_right.
        auto.
      }
      unfold WellFormedSafeJoins in *.
      apply in_fork.
      rewrite MT_Facts.add_mapsto_iff in mt.
      destruct mt as [(Hx,Hy)|(y_neq_c,mt)]. {
        inversion Hy; subst; clear Hy.

      apply Hsj with (x:=x); auto.
      eauto.

    rewrite MT_Facts.add_mapsto_iff in mt.
    destruct mt as [(Hx,Hy)|(y_neq_c,mt)]. {
      subst.
      inversion Hy; subst; clear Hy.
      apply in_fork_4 in H0; auto.
      subst.
      clear x_neq_c.
    }
    
    - rewrite MT_Facts.add_mapsto_iff in mt.
      destruct mt as [(?,?)|(?,mt)].
      + subst.
          apply in_fork_4 in H2; auto.
          subst.
          eauto using Nodes.maps_to_def, Nodes.in_def.


    

    intros.
    unfold WellFormedSafeJoins; intros a b c; intros.
    inversion H2; subst; clear H2.
    inversion H1; clear H1.
    
    destruct o1; simpl in *.
    destruct o0; simpl in *.
    subst.
    simpl in *. {
      (* fork *)
      destruct H3 as [E|[E|?]];
      try (inversion E; subst; clear E; auto using in_fork_3); simpl in *.
      assert (He: HB_Edge (vs,es) (x, y)) by auto; clear H1.
      apply fork_inv_in in H4.
      destruct H4 as [(?,Hx)|[(?,?)|?]]; subst; simpl in *.
      - contradiction H13.
        assert (R:vs = cg_nodes (vs, es)) by auto; rewrite R in *.
        apply H in He.
        destruct He.
        auto using Nodes.contains_to_in.
      - destruct (tid_eq_dec (node_task x) (node_task y)). {
          rewrite e in *.
          unfold fork; rewrite in_app_iff; right.
          auto using can_join_eq.
        }
        unfold fork.
                clear H8 H9 H11.
        assert (R:vs = cg_nodes (vs, es)) by auto; rewrite R in *.
        apply H in He.
        destruct He.
        apply in_fork.
        auto using in_fork_3.
    }
  Qed.


  Let wf_safe_joins:
    forall cg k o cg' k',
    WellFormedEdges cg ->
    WellFormedSafeJoins cg k ->
    CG.Reduces cg o cg' ->
    Reduces k o k' ->
    WellFormedSafeJoins cg' k'.
  Proof.
    intros.
    unfold WellFormedSafeJoins; intros.
    inversion H2; subst; clear H2;
    inversion H1; subst; clear H1;
    inversion H2; subst; clear H2;
    simpl in *. {
      (* fork *)
      destruct H3 as [E|[E|?]];
      try (inversion E; subst; clear E; auto using in_fork_3); simpl in *.
      assert (He: HB_Edge (vs,es) (x, y)) by auto; clear H1.
      apply fork_inv_in in H4.
      destruct H4 as [(?,Hx)|[(?,?)|?]]; subst; simpl in *.
      - contradiction H13.
        assert (R:vs = cg_nodes (vs, es)) by auto; rewrite R in *.
        apply H in He.
        destruct He.
        auto using Nodes.contains_to_in.
      - destruct (tid_eq_dec (node_task x) (node_task y)). {
          rewrite e in *.
          unfold fork; rewrite in_app_iff; right.
          auto using can_join_eq.
        }
        unfold fork.
                clear H8 H9 H11.
        assert (R:vs = cg_nodes (vs, es)) by auto; rewrite R in *.
        apply H in He.
        destruct He.
        apply in_fork.
        auto using in_fork_3.
    }
    (* join *)
  Qed.

  Lemma sj_hb:
    forall t x y z k cg a,
    Safe t k ->
    CG a t cg -> 
    HB_Edge cg (x, y) ->
    List.In (node_task x, z) k ->
    z <> node_task y ->
    List.In (node_task y, z) k.
  Proof.
    induction t; intros. {
      inversion H.
      subst.
      inversion H2.
    }
    inversion H; subst; clear H; rename k0 into k.
    unfold eval in *.
    inversion H0; subst; simpl in *; clear H0.
    apply reduces_to_reduces_ex in H9.
    inversion H9; subst; clear H9.
    inversion H; subst; clear H; simpl in *.
    - destruct H1 as [?|[?|?]].
      + simpl in *.
        inversion H; subst; clear H; simpl in *.
        auto using in_fork_3.
      + simpl in *. 
        inversion H; subst; clear H; simpl in *.
        auto using in_fork_3.
      + assert (He: HB_Edge (vs,es) (x, y)) by auto; clear H.
        apply fork_inv_in in H2.
        destruct H2 as [(?,Hx)|[(?,?)|?]]; subst; simpl in *.
        * contradiction H9.
          assert (R:vs = cg_nodes (vs, es)) by auto; rewrite R.
          eapply node_in_cg; eauto using in_left.
        *  
  Qed.
End HB.

Module Lang.

  Fixpoint from_trace ts := 
  match ts with
  | nil => nil
  | o :: ts => eval o (from_trace ts)
  end.

  Definition effects_to_sj ts := from_trace (CG.Lang.from_effects ts).

  Definition Safe ts := Safe (CG.Lang.from_effects ts) (effects_to_sj ts).
End Lang.
