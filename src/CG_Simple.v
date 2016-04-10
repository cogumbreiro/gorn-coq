Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
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

Require Lang.

Section CG_Simple.
  Section Defs.

  Definition node := (tid*nat) % type.

  Definition edge := (node * node) % type.

  Definition edges := list edge.

  Structure computation_graph := cg_make {
    cg_size : nat;
    cg_tasks: MT.t nat;
    cg_edges: list (node * node)
  }.

  Definition cg_lookup (t:tid) cg : option node :=
  match MT.find t (cg_tasks cg) with
  | Some n => Some (t,n)
  | _ => None
  end.

  Definition cg_future (x y:tid) (cg : computation_graph) : computation_graph :=
  let nx' := cg_size cg in
  let ny := S nx' in
  let total := S ny in
  let tasks := (MT.add x nx') ((MT.add y ny) (cg_tasks cg)) in
  match MT.find x (cg_tasks cg) with
  | Some nx =>
    cg_make total tasks (((x,nx),(x,nx'))::((x,nx),(y,ny))::(cg_edges cg))
  | _ => cg
  end.

  Definition cg_force (x y:tid) (cg : computation_graph) : computation_graph :=
  let nx' := cg_size cg in
  let total := S nx' in
  let tasks := (MT.add x nx') (cg_tasks cg) in
  match MT.find x (cg_tasks cg) with
  | Some nx =>
    match MT.find y (cg_tasks cg) with
    | Some ny =>
      cg_make total tasks (((x,nx),(x,nx'))::((y,ny), (x,nx'))::(cg_edges cg))
    | _ => cg
    end
  | _ => cg
  end.

  (** Properties *)

  Let Lt (n1 n2:node) := (snd n1) < (snd n2).

  Let cg_upper_bound cg :node := ((taskid 0), cg_size cg).

  Definition HasBound cg := DAG.UpperBound Lt (cg_upper_bound cg) (cg_edges cg).

  Let LtEdge (e:edge) := let (x,y) := e in Lt x y.

  Definition Size (cg:computation_graph) :=
    forall x n,
    MT.MapsTo x n (cg_tasks cg) ->
    n < cg_size cg.

  Lemma cg_future_size:
    forall cg x y,
    Size cg ->
    Size (cg_future x y cg).
  Proof.
    intros.
    unfold cg_future.
    destruct (MT_Extra.find_rw x (cg_tasks cg)) as [(rw,?)|(e,(rw,?))]; rewrite rw; clear rw. {
      auto.
    }
    unfold Size in *; intros; simpl in *.
    apply MT_Facts.add_mapsto_iff in H1.
    destruct H1 as [(?,?)|(?,?)]. {
      subst.
      auto.
    }
    apply MT_Facts.add_mapsto_iff in H2.
    destruct H2 as [(?,?)|(?,?)]. {
      subst.
      auto.
    }
    apply H in H3.
    eauto.
  Qed.

  Lemma cg_force_size:
    forall cg x y,
    Size cg ->
    Size (cg_force x y cg).
  Proof.
    intros.
    unfold cg_force.
    destruct (MT_Extra.find_rw x (cg_tasks cg)) as [(rw,?)|(nx,(rw,?))]; rewrite rw; clear rw. {
      auto.
    }
    destruct (MT_Extra.find_rw y (cg_tasks cg)) as [(rw,?)|(ny,(rw,?))]; rewrite rw; clear rw. {
      auto.
    }
    unfold Size in *; intros; simpl in *.
    apply MT_Facts.add_mapsto_iff in H2.
    destruct H2 as [(?,?)|(?,?)]. {
      subst.
      auto.
    }
    apply H in H3.
    eauto.
  Qed.

  Lemma cg_size_maps_to:
    forall cg x n,
    Size cg ->
    MT.MapsTo x n (cg_tasks cg) ->
    n < cg_size cg.
  Proof.
    unfold Size; intros; eauto.
  Qed.

  Definition NodesLt (cg:computation_graph) := Forall LtEdge (cg_edges cg).

  Lemma cg_nodes_lt:
    forall cg x y,
    NodesLt cg ->
    List.In (x,y) (cg_edges cg) ->
    Lt x y.
  Proof.
    intros.
    unfold NodesLt in *.
    rewrite Forall_forall in H.
    unfold LtEdge in *.
    apply H in H0.
    assumption.
  Qed.


  Lemma cg_future_nodes_lt:
    forall cg x y,
    Size cg ->
    NodesLt cg ->
    NodesLt (cg_future x y cg).
  Proof.
    intros.
    unfold cg_future.
    destruct (MT_Extra.find_rw x (cg_tasks cg)) as [(rw,?)|(e,(rw,?))];
    rewrite rw; clear rw. {
      auto.
    }
    unfold NodesLt in *; intros; simpl in *.
    apply Forall_cons. {
      unfold LtEdge, Lt.
      simpl.
      eauto using cg_size_maps_to.
    }
    apply Forall_cons. {
      unfold LtEdge, Lt.
      simpl.
      apply cg_size_maps_to in H1; auto.
    }
    auto.
  Qed.

  Lemma cg_force_nodes_lt:
    forall cg x y,
    Size cg ->
    NodesLt cg ->
    NodesLt (cg_force x y cg).
  Proof.
    intros.
    unfold cg_force.
    destruct (MT_Extra.find_rw x (cg_tasks cg)) as [(rw,?)|(e,(rw,?))];
    rewrite rw; clear rw; auto.
    unfold NodesLt in *; intros; simpl in *.
    destruct (MT_Extra.find_rw y (cg_tasks cg)) as [(rw,?)|(n',(rw,?))];
    rewrite rw; clear rw; auto.
    simpl in *.
    apply Forall_cons. {
      unfold LtEdge, Lt.
      simpl.
      eauto using cg_size_maps_to.
    }
    apply Forall_cons. {
      unfold LtEdge, Lt.
      simpl.
      apply cg_size_maps_to in H2; auto.
    }
    auto.
  Qed.

  Inductive Reduces: computation_graph -> Lang.effect -> computation_graph -> Prop :=
  | cg_reduces_future:
    forall x y cg,
    MT.In x (cg_tasks cg) ->
    ~ MT.In y (cg_tasks cg) ->
    Reduces cg (x,Lang.FUTURE y) (cg_future x y cg)
  | cg_reduces_force:
    forall x y cg,
    MT.In x (cg_tasks cg) ->
    MT.In y (cg_tasks cg) ->
    Reduces cg (x,Lang.FORCE y) (cg_force x y cg)
  | cg_reduces_skip:
    forall cg t o,
    Lang.is_f_op o = false ->
    Reduces cg (t,o) cg.

  Definition Prec (cg:computation_graph) n1 n2 := List.In (n1,n2) (cg_edges cg).

  Definition HB cg := clos_trans node (Prec cg).

  Inductive Ordered cg n1 n2 : Prop :=
  | ordered_lr:
    HB cg n1 n2 ->
    Ordered cg n1 n2
  | ordered_rl:
    HB cg n2 n1 ->
    Ordered cg n1 n2.

  Lemma hb_trans:
    forall cg n1 n2 n3,
    HB cg n1 n2 ->
    HB cg n2 n3 ->
    HB cg n1 n3.
  Proof.
    intros.
    unfold HB in *; eauto using t_trans.
  Qed.

  Let cg_is_dag:
    forall cg,
    NodesLt cg ->
    DAG Lt (cg_edges cg).
  Proof.
    intros.
    apply DAG.make_dag.
    intros.
    apply cg_nodes_lt in H0; auto.
  Qed.

  Let Edge cg e := (List.In e (cg_edges cg)).

  Let hb_to_walk2:
    forall cg n1 n2,
    HB cg n1 n2 ->
    exists w, Graph.Walk2 (Edge cg) n1 n2 w.
  Proof.
    unfold not, HB; intros.
    apply Graph.clos_trans_to_walk2 with (R:=Prec cg); auto.
    intros.
    unfold Prec, Edge.
    tauto.
  Qed.

  Let lt_trans:
    forall x y z : node,
    Lt x y ->
    Lt y z ->
    Lt x z.
  Proof.
    unfold Lt; intros.
    auto with *.
  Qed.

  Lemma hb_irrefl (cg:computation_graph) (G:NodesLt cg):
    forall n,
    ~ HB cg n n.
  Proof.
    intros.
    unfold not; intros.
    apply hb_to_walk2 in H.
    destruct H as (w, H).
    apply DAG.dag_walk_to_lt with (Lt:=Lt) in H.
    - unfold Lt in *.
      omega.
    - apply lt_trans.
    - auto.
  Qed.

  Lemma hb_asymm (cg:computation_graph) (G:NodesLt cg):
    forall n1 n2,
    HB cg n1 n2 ->
    ~ HB cg n2 n1.
  Proof.
    intros.
    unfold not; intros.
    assert (HB cg n1 n1) by eauto using hb_trans.
    apply hb_irrefl in H1; auto.
  Qed.

  Require Import Aniceto.Graphs.Graph.

  Let cg_future_preserves_prec:
    forall cg a b x y,
    Prec cg a b ->
    Prec (cg_future x y cg) a b.
  Proof.
    intros.
    unfold Prec in *.
    unfold cg_future; simpl.
    destruct (MT_Extra.find_rw x (cg_tasks cg)) as [(rw,?)|(nx,(rw,?))];
    rewrite rw; clear rw; auto.
    simpl.
    auto.
  Qed.

  Let cg_force_preserves_prec:
    forall cg a b x y,
    Prec cg a b ->
    Prec (cg_force x y cg) a b.
  Proof.
    intros.
    unfold Prec in *.
    unfold cg_force; simpl.
    destruct (MT_Extra.find_rw x (cg_tasks cg)) as [(rw,?)|(nx,(rw,?))];
    rewrite rw; clear rw; auto.
    simpl.
    destruct (MT_Extra.find_rw y (cg_tasks cg)) as [(rw,?)|(ny,(rw,?))];
    rewrite rw; clear rw; auto.
    simpl.
    auto.
  Qed.

  Lemma cg_future_preserves_hb:
    forall cg n1 n2 x y,
    HB cg n1 n2 ->
    HB (cg_future x y cg) n1 n2.
  Proof.
    intros.
    unfold HB in *.
    apply clos_trans_impl with (P:=Prec cg); auto.
  Qed.

  Lemma cg_force_preserves_hb:
    forall cg n1 n2 x y,
    HB cg n1 n2 ->
    HB (cg_force x y cg) n1 n2.
  Proof.
    intros.
    unfold HB in *.
    apply clos_trans_impl with (P:=Prec cg); auto.
  Qed.

  Let hb_neq_fi cg:
    forall n1 n2,
    ~ HB cg n1 n2 ->
    forall n,
    HB cg n1 n ->
    n <> n2.
  Proof.
    intros.
    unfold not; intros.
    subst.
    contradiction H0.
  Qed.

  Let hb_neq_if cg:
    forall n1 n2,
    (forall n, HB cg n1 n -> n <> n2) ->
    ~ HB cg n1 n2.
  Proof.
    intros.
    unfold not; intros.
    apply H in H0.
    contradiction H0; auto.
  Qed.

  Let heq_neq_iff cg:
    forall n1 n2,
    (forall n, HB cg n1 n -> n <> n2) <-> ~ HB cg n1 n2.
  Proof.
    intros; split; try intros; eauto.
  Qed.

  Definition MHP cg n1 n2 := ~ HB cg n1 n2 /\ ~ HB cg n2 n1.
End Defs.
End CG_Simple.