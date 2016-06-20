Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Lists.ListSet.
Require Import Aniceto.ListSet.
Require Import Aniceto.Graphs.Graph.

Require Import HJ.Tid.
Require Import HJ.Mid.
Require Import HJ.Cid.
Require Import HJ.Var.
Require Import HJ.Dep.

(* ----- end of boiler-plate code ---- *)

Set Implicit Arguments.

Require Import Aniceto.Graphs.DAG.
Require Import Coq.Relations.Relation_Operators.
Require Aniceto.Graphs.Graph.

Require Import Coq.Structures.OrderedTypeEx.

Section Trace.

  Inductive op :=
  | FORK : tid -> op
  | JOIN : tid -> op
  | CONTINUE : op.

  Definition event := (tid * op) % type.
  Definition trace := list event.    

End Trace.

Module Nodes.
Section Nodes.

  Notation node_ids := (list tid).

  Definition make (x:tid) : list tid := (x::nil).

  Definition next_id := @length tid.
  (** Looks up the latest id of a given task. *)

  Inductive MapsTo (x:tid) : nat -> node_ids -> Prop :=
  | maps_to_eq:
    forall l,
    MapsTo x (next_id l) (x::l)
  | maps_to_cons:
    forall l y n,
    x <> y ->
    MapsTo x n l -> 
    MapsTo x n (y :: l). 

  Inductive IndexOf (x:tid) : nat -> node_ids -> Prop :=
  | index_of_eq:
    forall l,
    IndexOf x (next_id l) (x::l)
  | index_of_cons:
    forall l y n,
    IndexOf x n l -> 
    IndexOf x n (y :: l). 

  (** If this property holds then x was assigned to this id
    at one point in time. *)

  Inductive Contains (n:nat) (l:list tid) : Prop :=
  | contains_def:
    n < length l ->
    Contains n l.

  Lemma maps_to_inv_eq:
    forall x nx vs,
    MapsTo x nx (x :: vs) ->
    nx = next_id vs.
  Proof.
    intros.
    inversion H; subst; auto.
    contradiction H3; trivial.
  Qed.

  Lemma maps_to_neq:
    forall x y vs n,
    x <> y ->
    MapsTo y n (x :: vs) ->
    MapsTo y n vs.
  Proof.
    intros.
    inversion H0.
    - subst; contradiction H; trivial.
    - assumption.
  Qed.

  Lemma maps_to_fun:
    forall vs x nx nx',
    MapsTo x nx vs ->
    MapsTo x nx' vs ->
    nx' = nx.
  Proof.
    induction vs; intros. {
      inversion H.
    }
    inversion H; subst; clear H;
    inversion H0; subst; clear H0; auto.
    - contradiction H3; trivial.
    - contradiction H4; trivial.
    - eauto.
  Qed.

End Nodes.
End Nodes.

Section Edges.

  Notation node := nat.
  Notation edge := (node * node) % type.

  (**
    When creating a tee, the inter edge is the only thing
    that changes depending on the type of the node.
    *)

  Inductive edge_type :=
  | E_FORK
  | E_JOIN
  | E_CONTINUE.

  Structure cg_edge := cg_e {
    e_t: edge_type;
    e_edge: (node * node)
  }.

  Definition computation_graph := (list tid * list cg_edge) % type.

  Inductive Edge : computation_graph -> edge_type -> (node * node) -> Prop :=
  | edge_def:
    forall vs es e t,
    List.In e es ->
    Edge (vs, es) t (e_edge e).

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
    auto using edge_def.
  Qed.

  Inductive TaskEdge cg t : (tid * tid) -> Prop :=
  | task_edge_def:
    forall x y nx ny,
    Edge cg t (nx, ny) ->
    Nodes.MapsTo x nx (fst cg) ->
    Nodes.MapsTo y ny (fst cg) ->
    TaskEdge cg t (x, y).

  Inductive Live cg x : Prop :=
  | live_def:
    (forall y, ~ TaskEdge cg E_JOIN (x, y)) ->
    Live cg x.

  Notation F := (cg_e E_FORK).
  Notation J := (cg_e E_JOIN).
  Notation C := (cg_e E_CONTINUE).

  Inductive Reduces: computation_graph -> event -> computation_graph -> Prop :=
  | reduces_fork:
    forall vs es es' vs' y x nx ny,
    x <> y ->
    ~ List.In y vs -> 
    Reduces (vs,es) (x, CONTINUE) (vs', es') ->
    Nodes.MapsTo x nx vs ->
    Nodes.MapsTo y ny (y::vs') ->
    Reduces (vs,es) (x, FORK y) (y::vs', F (nx,ny) :: es')
  | reduces_join:
    forall vs es vs' es' x y nx ny,
    x <> y ->
    Reduces (vs,es) (x, CONTINUE) (vs', es') ->
    Nodes.MapsTo x nx vs' ->
    Nodes.MapsTo y ny vs' ->
    Reduces (vs,es) (x, JOIN y) (vs', J (ny, nx) :: es')
  | reduces_continue:
    forall vs (es:list cg_edge) x prev curr,
    Live (vs,es) x ->
    Nodes.MapsTo x prev vs ->
    Nodes.MapsTo x curr (x::vs) ->
    Reduces (vs,es) (x, CONTINUE) (x::vs, C (prev, curr) :: es).

  Definition make_cg x : computation_graph := (Nodes.make x, nil).

  Inductive TraceOf : computation_graph -> tid -> trace -> Prop :=
  | trace_of_nil:
    forall x,
    TraceOf (make_cg x) x nil
  | trace_of_fork:
    forall vs es a t x y nx,
    TraceOf (vs, es) a t ->
    Nodes.MapsTo x nx vs ->
    TraceOf (y::x::vs, F (nx, S (Nodes.next_id vs)) :: C (nx, Nodes.next_id vs) :: es)
       a ((x, FORK y)::t)
  | trace_of_join:
    forall vs es a t x y ny nx,
    TraceOf (vs, es) a t ->
    Nodes.MapsTo x nx vs ->
    Nodes.MapsTo y ny vs ->
    TraceOf (x::vs, J (ny, Nodes.next_id vs) :: C (nx, Nodes.next_id vs) :: es)
       a ((x, JOIN y)::t)
  | trace_of_continue:
    forall vs es a t x nx,
    TraceOf (vs, es) a t ->
    Nodes.MapsTo x nx vs ->
    TraceOf (x::vs, C (nx, Nodes.next_id vs) :: es) a ((x, CONTINUE)::t).

  Lemma trace_of_cons:
    forall cg a t e cg',
    TraceOf cg a t ->
    Reduces cg e cg' ->
    TraceOf cg' a (e::t).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    - inversion H3; subst; clear H3.
      assert (prev = nx) by eauto using Nodes.maps_to_fun; subst.
      assert (curr = Nodes.next_id vs)
      by eauto using Nodes.maps_to_inv_eq; subst.
      assert (ny = Nodes.next_id (x::vs))
      by eauto using Nodes.maps_to_inv_eq; subst.
      simpl.
      auto using trace_of_fork.
    - inversion H2; subst; clear H2.
      assert (curr = Nodes.next_id vs)
      by eauto using Nodes.maps_to_inv_eq; subst.
      assert (nx = Nodes.next_id vs)
      by eauto using Nodes.maps_to_inv_eq; subst.
      eauto using trace_of_join, Nodes.maps_to_neq.
    - assert (curr = Nodes.next_id vs)
      by eauto using Nodes.maps_to_inv_eq; subst.
      auto using trace_of_continue.
  Qed.

  Inductive CG (x:tid): trace -> computation_graph -> Prop :=
  | cg_nil:
    CG x nil (make_cg x)
  | cg_cons:
    forall cg o t cg',
    CG x t cg ->
    Reduces cg o cg' ->
    CG x (o::t) cg'.

  Lemma cg_to_trace_of:
    forall cg a t,
    CG a t cg ->
    TraceOf cg a t.
  Proof.
    intros.
    induction H. {
      apply trace_of_nil.
    }
    eauto using trace_of_cons.
  Qed.
    

  Definition cg_nodes (cg:computation_graph) := fst cg.

  Definition cg_edges (cg:computation_graph) := map e_edge (snd cg).
End Edges.

Section Defs.

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
      destruct x as (t, x). 
      apply hb_edge_def with (t:=t); eauto using edge_def.
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

End Defs.

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

