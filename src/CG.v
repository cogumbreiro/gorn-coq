Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Lists.ListSet.
Require Import Aniceto.ListSet.
Require Import Aniceto.Graphs.Graph.

Require Import Tid.
Require Import Mid.
Require Import Cid.
Require Import Var.
Require Import Dep.
Require Import Bijection.

(* ----- end of boiler-plate code ---- *)

Set Implicit Arguments.

Require Import Aniceto.Graphs.DAG.
Require Import Coq.Relations.Relation_Operators.
Require Aniceto.Graphs.Graph.

Require Import Coq.Structures.OrderedTypeEx.

Section Defs.

  Inductive op :=
  | FORK : tid -> op
  | JOIN : tid -> op
  | CONTINUE : op.

  Definition event := (tid * op) % type.
  Definition trace := list event.    

  Inductive edge_type :=
  | E_FORK
  | E_JOIN
  | E_CONTINUE.

  Structure cg_edge := cg_e {
    e_t: edge_type;
    e_edge: (nat * nat)
  }.
End Defs.

Notation F := (cg_e E_FORK).
Notation J := (cg_e E_JOIN).
Notation C := (cg_e E_CONTINUE).

Section Edges.

  (**
    When creating a tee, the inter edge is the only thing
    that changes depending on the type of the node.
    *)


  Notation node := nat.
  Notation edge := (node * node) % type.

  Definition computation_graph := (list tid * list cg_edge) % type.

  Inductive Edge : computation_graph -> edge_type -> (node * node) -> Prop :=
  | edge_def:
    forall vs es e,
    List.In e es ->
    Edge (vs, es) (e_t e) (e_edge e).

  Inductive HB_Edge cg e : Prop :=
  | hb_edge_def:
    forall t,
    Edge cg t e ->
    HB_Edge cg e.

  Lemma edge_eq:
    forall vs es t x y,
     List.In {| e_t := t; e_edge := (x,y) |} es ->
     Edge (vs, es) t (x, y).
  Proof.
    intros.
    remember {| e_t := t; e_edge := (x, y) |} as e.
    assert (R:(x, y) = e_edge e) by (subst; auto).
    rewrite R.
    assert (R2:t = e_t e) by (subst; auto).
    rewrite R2.
    auto using edge_def.
  Qed.

  Lemma hb_edge_in:
    forall e vs es,
    List.In e es ->
    HB_Edge (vs,es) (e_edge e).
  Proof.
    eauto using hb_edge_def, edge_def.
  Qed.

  Inductive TaskEdge cg t : (tid * tid) -> Prop :=
  | task_edge_def:
    forall x y nx ny,
    Edge cg t (nx, ny) ->
    MapsTo x nx (fst cg) ->
    MapsTo y ny (fst cg) ->
    TaskEdge cg t (x, y).

  Inductive Live cg x : Prop :=
  | live_def:
    (forall y t, ~ TaskEdge cg t (x, y)) ->
    Live cg x.

  Inductive Reduces: computation_graph -> event -> computation_graph -> Prop :=
  | reduces_fork:
    forall vs es es' vs' y x nx ny,
    x <> y ->
    ~ List.In y vs -> 
    Reduces (vs,es) (x, CONTINUE) (vs', es') ->
    MapsTo x nx vs ->
    MapsTo y ny (y::vs') ->
    Reduces (vs,es) (x, FORK y) (y::vs', F (nx,ny) :: es')
  | reduces_join:
    forall vs es vs' es' x y nx ny,
    x <> y ->
    Reduces (vs,es) (x, CONTINUE) (vs', es') ->
    MapsTo x nx vs' ->
    MapsTo y ny vs' ->
    Reduces (vs,es) (x, JOIN y) (vs', J (ny, nx) :: es')
  | reduces_continue:
    forall vs (es:list cg_edge) x prev curr,
    Live (vs,es) x ->
    MapsTo x prev vs ->
    MapsTo x curr (x::vs) ->
    Reduces (vs,es) (x, CONTINUE) (x::vs, C (prev, curr) :: es).

  Definition make_cg x : computation_graph := (x::nil, nil).

  Inductive Run (x:tid): trace -> computation_graph -> Prop :=
  | run_nil:
    Run x nil (make_cg x)
  | run_cons:
    forall cg o t cg',
    Run x t cg ->
    Reduces cg o cg' ->
    Run x (o::t) cg'.

  (** Getting the trace from a computation, which works as the type of a CG. *)

  Inductive TraceOf : computation_graph -> tid -> trace -> Prop :=
  | trace_of_nil:
    forall x,
    TraceOf (make_cg x) x nil
  | trace_of_fork:
    forall vs es a t x y nx,
    x <> y ->
    Live (vs, es) x ->
    ~ List.In y vs ->
    TraceOf (vs, es) a t ->
    MapsTo x nx vs ->
    TraceOf (y::x::vs, F (nx, S (length vs)) :: C (nx, length vs) :: es)
       a ((x, FORK y)::t)
  | trace_of_join:
    forall vs es a t x y ny nx,
    x <> y ->
    Live (vs, es) x ->
    TraceOf (vs, es) a t ->
    MapsTo x nx vs ->
    MapsTo y ny vs ->
    TraceOf (x::vs, J (ny, length vs) :: C (nx, length vs) :: es)
       a ((x, JOIN y)::t)
  | trace_of_continue:
    forall vs es a t x nx,
    Live (vs, es) x ->
    TraceOf (vs, es) a t ->
    MapsTo x nx vs ->
    TraceOf (x::vs, C (nx, length vs) :: es) a ((x, CONTINUE)::t).

  Lemma trace_of_cons:
    forall cg a t e cg',
    TraceOf cg a t ->
    Reduces cg e cg' ->
    TraceOf cg' a (e::t).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    - inversion H3; subst; clear H3.
      assert (prev = nx) by eauto using maps_to_fun_2; subst.
      assert (curr = length vs)
      by eauto using maps_to_inv_eq; subst.
      assert (ny = length (x::vs))
      by eauto using maps_to_inv_eq; subst.
      simpl.
      auto using trace_of_fork.
    - inversion H2; subst; clear H2.
      assert (curr = length vs)
      by eauto using maps_to_inv_eq; subst.
      assert (nx = length vs)
      by eauto using maps_to_inv_eq; subst.
      eauto using trace_of_join, maps_to_neq.
    - assert (curr = length vs)
      by eauto using maps_to_inv_eq; subst.
      auto using trace_of_continue.
  Qed.

  Lemma run_to_trace_of:
    forall cg a t,
    Run a t cg ->
    TraceOf cg a t.
  Proof.
    intros.
    induction H. {
      apply trace_of_nil.
    }
    eauto using trace_of_cons.
  Qed.

  Lemma trace_of_to_run:
    forall cg a t,
    TraceOf cg a t ->
    Run a t cg.
  Proof.
    intros.
    induction H.
    - apply run_nil.
    - eapply run_cons; eauto.
      apply reduces_fork; auto using maps_to_eq, reduces_continue.
      assert (MapsTo y (length (x::vs)) (y :: x :: vs)) 
      by auto using maps_to_eq.
      simpl in *; assumption.
    - eauto using run_cons, reduces_join, reduces_continue, maps_to_eq, maps_to_cons.
    - eauto using run_cons, reduces_continue, maps_to_eq, maps_to_cons.
  Qed.

  (**
     The main result is that the information in the trace is
     the same as the information in the CG.
     *)

  Lemma trace_of_spec:
    forall cg a t,
    Run a t cg <-> TraceOf cg a t.
  Proof.
    split; auto using trace_of_to_run, run_to_trace_of.
  Qed.

  Definition cg_nodes (cg:computation_graph) := fst cg.

  Definition cg_edges (cg:computation_graph) := map e_edge (snd cg).

  (** Every node of the CG is an index of the list of vertices. *)

  Definition EdgeToIndex cg :=
    forall x y,
    HB_Edge cg (x, y) ->
    Index x (fst cg) /\ Index y (fst cg).
End Edges.

Section Props.

  Lemma in_make:
    forall t,
    List.In t (cg_nodes (make_cg t)).
  Proof.
    intros.
    simpl; auto.
  Qed.

  Inductive Prec : (nat * nat) -> cg_edge -> Prop :=
  | prec_def:
    forall e,
    Prec (e_edge e) e.

  Variable cg: computation_graph.

  Let HB_Edge_alt e := List.Exists (Prec e) (snd cg).

  Definition HB := Reaches (HB_Edge cg).

  Definition MHP x y : Prop := ~ HB x y /\ ~ HB y x.

  Let in_edges_to_tees:
    forall e,
    List.In e (cg_edges cg) ->
    exists x, List.In x (snd cg) /\ Prec e x.
  Proof.
    unfold cg_edges.
    intros.
    rewrite in_map_iff in *.
    destruct H as (x, (Hi, He)).
    exists x; split; auto.
    subst; eauto using prec_def.
  Qed.

  Let in_tees_to_edges:
    forall x e,
    List.In x (snd cg) ->
    Prec e x ->
    List.In e (cg_edges cg).
  Proof.
    unfold cg_edges.
    intros.
    rewrite in_map_iff in *.
    inversion H0;
    subst;
    eauto.
  Qed.

  Lemma hb_edge_spec:
    forall e,
    HB_Edge cg e <-> List.In e (cg_edges cg).
  Proof.
    split; intros.
    - destruct H.
      inversion H; subst; clear H.
      unfold cg_edges.
      simpl.
      auto using in_map.
    - unfold cg_edges in *; rewrite in_map_iff in *.
      destruct H as (?,(?,?)); subst.
      destruct cg.
      simpl in *.
      eauto using hb_edge_in.
  Qed.

  Lemma node_lt_length_left:
    forall n1 n2,
    EdgeToIndex cg ->
    List.In (n1, n2) (cg_edges cg) ->
    n1 < length (fst cg).
  Proof.
    intros.
    apply hb_edge_spec in H0.
    apply H in H0.
    destruct H0.
    auto using index_to_lt.
  Qed.

  (** Comparable with respect to the happens-before relation [n1 < n2 \/ n2 < n1] *)

  Inductive Comparable n1 n2 : Prop :=
  | comparable_left_right:
    HB n1 n2 ->
    Comparable n1 n2
  | comparable_right_left:
    HB n2 n1 ->
    Comparable n1 n2.

  Lemma comparable_symm:
    forall x y,
    Comparable x y ->
    Comparable y x.
  Proof.
    intros.
    inversion H; auto using comparable_left_right, comparable_right_left.
  Qed.

  Lemma comparable_to_not_mhp:
    forall x y,
    Comparable x y ->
    ~ MHP x y.
  Proof.
    intros.
    unfold not; intros.
    inversion H0.
    inversion H; contradiction.
  Qed.

  Inductive Relation x y : Prop :=
  | L_HB_R: HB x y -> Relation x y
  | R_HB_L: HB y x -> Relation x y
  | EQ: x = y -> Relation x y
  | PAR: MHP x y -> Relation x y.

  Lemma hb_dec:
    forall x y,
    Relation x y.
  Admitted. (* TODO: prove this at the graph-level *)

End Props.

Section HB.

  Let walk2_edge_false:
    forall {A:Type} (x y:A) w,
    ~ Walk2 (fun _ => False) x y w.
  Proof.
    intuition.
    destruct H.
    destruct w.
    - eauto using starts_with_inv_nil.
    - eapply walk_to_edge; eauto using in_eq.
  Qed.

  Let reaches_edge_false:
    forall {A:Type} (x y:A),
    ~ Reaches (fun _ => False) x y.
  Proof.
    intuition.
    inversion H.
    apply walk2_edge_false in H0; auto.
  Qed.

  Lemma hb_make_cg_absurd:
    forall a x y,
    ~ HB (make_cg a) x y.
  Proof.
    intros.
    intuition.
    inversion H.
    inversion H0; subst.
    destruct w. {
      apply starts_with_inv_nil in H1; contradiction.
    }
    assert (HB_Edge (make_cg a) p). {
      eapply walk_to_edge; eauto using List.in_eq.
    }
    rewrite hb_edge_spec in H4.
    simpl in H4.
    contradiction.
  Qed.

End HB.

Section PropsEx.
  Lemma make_edge_to_index:
    forall x,
    EdgeToIndex (make_cg x).
  Proof.
    intros.
    unfold make_cg, EdgeToIndex.
    intros.
    simpl in *.
    rewrite hb_edge_spec in H.
    simpl in *.
    contradiction.
  Qed.

  Lemma reduces_edge_to_index:
    forall cg e cg',
    EdgeToIndex cg ->
    Reduces cg e cg' ->
    EdgeToIndex cg'.
  Proof.
    intros.
    unfold EdgeToIndex; intros a b; intros.
    inversion H0; subst; clear H0.
    - inversion H4; subst; clear H4.
      apply maps_to_inv_eq in H13; subst.
      apply maps_to_inv_eq in H6; subst.
      assert (prev = nx) by eauto using maps_to_fun_2; subst; clear H12.
      simpl in *.
      inversion H1; subst; clear H1.
      inversion H0; subst; clear H0.
      destruct H7 as [?|[?|?]].
      + subst; inversion H8; subst; clear H8.
        split; eauto using maps_to_lt, lt_to_index, index_cons.
      + subst; simpl in *; inversion H8; subst; clear H8.
        split; eauto using maps_to_lt, lt_to_index, index_cons.
      + subst.
        assert (He: HB_Edge (vs, es) (e_edge e)) by auto using hb_edge_in.
        rewrite H8 in *.
        apply H in He.
        simpl in *.
        destruct He.
        split; auto using index_cons.
    - simpl in *.
      inversion H3; subst; clear H3.
      apply maps_to_inv_eq in H4; subst.
      apply maps_to_inv_eq in H12; subst.
      apply maps_to_neq in H5; auto.
      inversion H1; subst; clear H1.
      inversion H0; subst; clear H0.
      destruct H6 as [Hx|[Hx|Hx]].
      + subst.
        inversion H7; subst; clear H7.
        apply maps_to_lt in H5.
        auto using lt_to_index, index_cons.
      + subst.
        inversion H7; subst; clear H7.
        apply maps_to_lt in H11.
        auto using lt_to_index, index_cons.
      + assert (He: HB_Edge (vs, es) (e_edge e)) by auto using hb_edge_in.
        rewrite H7 in *.
        apply H in He.
        simpl in *.
        destruct He.
        split; auto using index_cons.
    - simpl in *.
      apply maps_to_inv_eq in H4; subst.
      inversion H1; subst; clear H1.
      inversion H0; subst; clear H0.
      destruct H6 as [Hx|Hx].
      + subst.
        inversion H7; subst; clear H7.
        apply maps_to_lt in H3.
        auto using lt_to_index, index_cons.
     + assert (He: HB_Edge (vs, es) (e_edge e)) by auto using hb_edge_in.
       rewrite H7 in *.
       apply H in He.
       simpl in *.
       destruct He.
       split; auto using index_cons.
  Qed.

  Lemma run_to_edge_to_index:
    forall t a cg,
    Run a t cg ->
    EdgeToIndex cg.
  Proof.
    intros.
    induction H.
    - auto using make_edge_to_index.
    - eauto using run_cons, reduces_edge_to_index.
  Qed.

End PropsEx.