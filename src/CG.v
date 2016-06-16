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

Require Import Lang.

Module NAT_PAIR := PairOrderedType Nat_as_OT Nat_as_OT.


Section Node.
  Structure node := {
    node_task: tid;
    node_id: nat
  }.

  Definition zero_node t := {| node_task := t; node_id:= 0 |}.
End Node.

Section Trace.
  Inductive op_type := FORK | JOIN.

  Structure op := {
    op_t: op_type;
    op_src: tid;
    op_dst: tid
  }.

  Definition trace := list op.    

End Trace.

Module Nodes.

Section Nodes.

  Structure node_ids := {
    cg_ids : MT.t (list nat);
    cg_last_id : nat
  }.

  Definition make (x:tid) : node_ids :=
  {|
    cg_ids :=  MT.add x (0 :: nil) (@MT.empty (list nat)) ;
    cg_last_id := 0
   |}.

  (** Looks up the latest id of a given task. *)

  Inductive MapsTo (x:tid) (n:nat) (ns:node_ids) : Prop :=
  | maps_to_def:
    forall l,
    MT.MapsTo x (n::l) (cg_ids ns) ->
    MapsTo x n ns.

  (** If this property holds then x was assigned to this id
    at one point in time. *)

  Inductive Contains (n:node) (ids:MT.t (list nat)) : Prop :=
  | contains_def:
    forall l,
    MT.MapsTo (node_task n) l ids ->
    List.In (node_id n) l ->
    Contains n ids.

  Lemma contains_add_1:
    forall n x l ids,
    x = node_task n ->
    List.In (node_id n) l ->
    Contains n (MT.add x l ids).
  Proof.
    eauto using contains_def, MT.add_1.
  Qed.

  Lemma contains_add_2:
    forall n x l ids,
    x <> node_task n ->
    Contains n ids ->
    Contains n (MT.add x l ids).
  Proof.
    intros.
    inversion H0.
    eauto using contains_def, MT.add_2.
  Qed.

  Lemma contains_add_3:
    forall n x l ids,
    x <> node_task n ->
    Contains n (MT.add x l ids) ->
    Contains n ids.
  Proof.
    intros.
    inversion H0.
    eauto using contains_def, MT.add_3.
  Qed.

  Lemma contains_add_iff:
    forall n x l ids,
    Contains n (MT.add x l ids) <->
    x = node_task n /\ List.In (node_id n) l
    \/
    x <> node_task n /\ Contains n ids.
  Proof.
    split; intros. {
      inversion H.
      apply MT_Facts.add_mapsto_iff in H0.
      destruct H0 as [(?,?)|(?,?)]; subst.
      - intuition.
      - eauto using contains_def.
    }
    destruct H as [(?,?)|(?,?)]. {
      auto using contains_add_1.
    }
    auto using contains_add_2.
  Qed.

  Inductive In (x:tid) ns : Prop :=
  | in_def:
    forall n,
    MapsTo x n ns ->
    In x ns.

  Lemma contains_to_in:
    forall x ns,
    Contains x (cg_ids ns) ->
    In (node_task x) ns.
  Proof.
    intros.
    inversion H.
    destruct l. {
      inversion H1.
    }
    eauto using in_def, maps_to_def.
  Qed.

  Let do_fork x l y ns :=
  {|
    cg_ids :=
      (MT.add x (S (cg_last_id ns) :: l))
      (MT.add y (S (S (cg_last_id ns)):: nil) (cg_ids ns));
    cg_last_id := S (S (cg_last_id ns))
  |}.

  Definition cg_nodes_fork x y (ns:node_ids) :=
  match MT.find x (cg_ids ns) with
  | Some l => do_fork x l y ns
  | _ =>  ns
  end.

  Let do_join x l ns :=
  {|
    cg_ids := MT.add x (S (cg_last_id ns) :: l) (cg_ids ns);
    cg_last_id := S (cg_last_id ns)
  |}.

  Definition cg_nodes_join x (ns:node_ids) :=
  match MT.find x (cg_ids ns) with
  | Some l => do_join x l ns
  | _ =>  ns
  end.

  (** Reduces vertices *)

  Inductive ReducesEx (ns:node_ids): op -> node_ids -> Prop :=
  | reduces_ex_fork:
    forall a b n l,
    MT.MapsTo a (n::l) (cg_ids ns) ->
    ~ In b ns ->
    ReducesEx ns {|op_t:=FORK;op_src:=a;op_dst:=b|} (do_fork a (n::l) b ns)
  | reduces_ex_join:
    forall a b n l,
    MT.MapsTo a (n::l) (cg_ids ns) ->
    In b ns ->
    a <> b ->
    ReducesEx ns {|op_t:=JOIN;op_src:=a;op_dst:=b|} (do_join a (n::l) ns).

  Inductive Reduces (ns:node_ids): op -> node_ids -> Prop :=
  | reduces_fork:
    forall a b,
    In a ns ->
    ~ In b ns ->
    Reduces ns {|op_t:=FORK;op_src:=a;op_dst:=b|} (cg_nodes_fork a b ns)
  | reduces_join:
    forall a b,
    In a ns ->
    In b ns ->
    a <> b ->
    Reduces ns {|op_t:=JOIN;op_src:=a;op_dst:=b|} (cg_nodes_join a ns).

  Lemma reduces_to_reduces_ex:
    forall ns o ns',
    Reduces ns o ns' ->
    ReducesEx ns o ns'.
  Proof.
    intros.
    inversion H; subst; clear H.
    - destruct H0 as (n, (l, mt)).
      unfold cg_nodes_fork.
      destruct (MT_Extra.find_rw a (cg_ids ns)) as [(R,N)|(v,(R,X))];
      rewrite R in *; clear R. {
        contradiction N; eauto using MT_Extra.mapsto_to_in.
      }
      assert (v=n :: l) by eauto using MT_Facts.MapsTo_fun; subst; clear X.
      eauto using reduces_ex_fork.
    - destruct H0 as (n, (l, mt)).
      unfold cg_nodes_join.
      destruct (MT_Extra.find_rw a (cg_ids ns)) as [(R,N)|(v,(R,X))];
      rewrite R in *; clear R. {
        contradiction N; eauto using MT_Extra.mapsto_to_in.
      }
      assert (v=n :: l) by eauto using MT_Facts.MapsTo_fun; subst; clear X.
      eauto using reduces_ex_join.
  Qed.

  Lemma reduces_ex_to_reduces:
    forall ns o ns',
    ReducesEx ns o ns' ->
    Reduces ns o ns'.
  Proof.
    intros.
    inversion H; subst; clear H.
    - assert (In a ns) by eauto using in_def, maps_to_def.
      assert (RW: do_fork a (n :: l) b ns = cg_nodes_fork a b ns). {
        unfold cg_nodes_fork.
        destruct (MT_Extra.find_rw a (cg_ids ns)) as [(R,N)|(v,(R,X))];
        rewrite R in *; clear R. {
          contradiction N; eauto using MT_Extra.mapsto_to_in.
        }
        assert (v=n :: l) by eauto using MT_Facts.MapsTo_fun; subst; clear X.
        trivial.
      }
      rewrite RW.
      auto using reduces_fork.
    - assert (In a ns) by eauto using in_def, maps_to_def.
      assert (RW: do_join a (n :: l) ns = cg_nodes_join a ns). {
        unfold cg_nodes_join.
        destruct (MT_Extra.find_rw a (cg_ids ns)) as [(R,N)|(v,(R,X))];
        rewrite R in *; clear R. {
          contradiction N; eauto using MT_Extra.mapsto_to_in.
        }
        assert (v=n :: l) by eauto using MT_Facts.MapsTo_fun; subst; clear X.
        trivial.
      }
      rewrite RW.
      auto using reduces_join.
  Qed.

  Lemma reduces_ex_iff:
    forall ns o ns',
    Reduces ns o ns' <->
    ReducesEx ns o ns'.
  Proof.
    split; eauto using reduces_ex_to_reduces, reduces_to_reduces_ex.
  Qed.

  Lemma reduces_src_neq_dst:
    forall vs o vs',
    Reduces vs o vs' ->
    op_src o <> op_dst o.
  Proof.
    intros.
    inversion H; subst; clear H; simpl.
    - intuition;
      subst;
      contradiction.
    - assumption. 
  Qed.

  (** After reduction we always get three nodes *)

  Lemma reduces_maps_to_op:
    forall vs o vs',
    Reduces vs o vs' ->
    exists na na' nb la lb,
    MT.MapsTo (op_src o) (na' :: na:: la) (cg_ids vs') /\
    MT.MapsTo (op_dst o) (nb:: lb) (cg_ids vs').
  Proof.
    intros.
    assert (Hneq: op_src o <> op_dst o) by eauto using reduces_src_neq_dst.
    apply reduces_to_reduces_ex in H.
    inversion H; subst; clear H; simpl in *.
    - eauto 10 using MT.add_1, MT.add_2.
    - destruct H1 as (nb, (lb, mt)).
      eauto 9 using MT.add_1, MT.add_2.
  Qed.

  Lemma reduces_continue_node:
    forall vs o vs',
    Reduces vs o vs' ->
    exists n l, MT.MapsTo (op_src o) (n::l) (cg_ids vs) /\
    MT.MapsTo (op_src o) (S (cg_last_id vs) :: n:: l) (cg_ids vs').
  Proof.
    intros.
    apply reduces_to_reduces_ex in H.
    inversion H; simpl in *; subst; clear H;
    eauto using MT.add_1.
  Qed.

  Lemma in_make:
    forall t,
    In t (make t).
  Proof.
    unfold make.
    eauto using in_def, maps_to_def, MT.add_1.
  Qed.

End Nodes.
End Nodes.

Section Edges.

  Import Nodes.

  Notation edge := (node * node) % type.

  (** A tee consists of two edges:
    an intra-edge that represents the continue edge, and
    an inter-edge that represents either the spawn or the async edge.
    *)

  Structure tee := {
    ntype: op_type;
    intra : edge;
    inter : edge
  }.

  (**
    When creating a tee, the inter edge is the only thing
    that changes depending on the type of the node.
    *)

  Definition make_inter nt (x x' y:node) :=
  match nt with
  | FORK => (x, y)
  | JOIN => (y, x')
  end.

  Definition make_tee o nx nx' ny :=
  let nt := op_t o in
  let x := op_src o in
  let y := op_dst o in
  let a  := {| node_task := x; node_id := nx |} in
  let a' := {| node_task := x; node_id := nx'|} in
  let b  := {| node_task := y; node_id := ny |} in
  {| ntype := nt; intra := (a, a'); inter := make_inter nt a a' b |}.

  Definition cg_add_tee vs o es : list tee :=
  match MT.find (op_src o) (cg_ids vs), MT.find (op_dst o) (cg_ids vs) with
  | Some (nx'::nx::_), Some (ny::_) =>
    make_tee o nx nx' ny :: es
  | _,_ => es
  end.

  Definition computation_graph := (node_ids * list tee) % type.

  Inductive Reduces: computation_graph -> op -> computation_graph -> Prop :=
  | reduces_step:
    forall vs (es:list tee) vs' o,
    Nodes.Reduces vs o vs' ->
    Reduces (vs,es) o (vs', cg_add_tee vs' o es).

  Inductive ReducesEx: computation_graph -> op -> computation_graph -> Prop :=
  | reduces_ex_step:
    forall vs (es:list tee) vs' o nx nx' ny lx ly,
    Nodes.ReducesEx vs o vs' ->
    MT.MapsTo (op_src o) (nx'::nx::lx) (cg_ids vs') ->
    MT.MapsTo (op_dst o) (ny::ly) (cg_ids vs') ->
    ReducesEx (vs,es) o (vs', make_tee o nx nx' ny :: es).

  Let cg_add_tee_rw:
    forall o la lb vs es na na' nb,
    MT.MapsTo (op_src o) (na' :: na :: la) (cg_ids vs) ->
    MT.MapsTo (op_dst o) (nb :: lb) (cg_ids vs) ->
    cg_add_tee vs o es = make_tee o na na' nb :: es.
  Proof.
    intros.
    unfold cg_add_tee.
    destruct (MT_Extra.find_rw (op_src o) (cg_ids vs)) as [(R,N)|(l,(R,X))];
    rewrite R in *; clear R. {
      contradiction N; eauto using MT_Extra.mapsto_to_in.
    }
    assert (l = na' :: na :: la) by eauto using MT_Facts.MapsTo_fun; subst; clear X.
    destruct (MT_Extra.find_rw (op_dst o) (cg_ids vs)) as [(R,N)|(l,(R,X))];
    rewrite R in *; clear R. {
      contradiction N; eauto using MT_Extra.mapsto_to_in.
    }
    assert (l = nb :: lb) by eauto using MT_Facts.MapsTo_fun; subst; clear X.
    trivial.
  Qed.

  Lemma reduces_to_reduces_ex:
    forall cg o cg',
    Reduces cg o cg' ->
    ReducesEx cg o cg'.
  Proof.
    intros.
    inversion H; subst.
    assert (R: exists na na' nb la lb, MT.MapsTo (op_src o) (na' :: na:: la) (cg_ids vs') /\
            MT.MapsTo (op_dst o) (nb:: lb) (cg_ids vs'))
    by eauto using reduces_maps_to_op;
    destruct R as (na, (na', (nb, (la, (lb, (mta, mtb)))))).
    assert (RW: cg_add_tee vs' o es = make_tee o na na' nb :: es) by eauto using cg_add_tee_rw;
    rewrite RW; clear RW.
    eauto using reduces_ex_step, reduces_to_reduces_ex.
  Qed.

  Lemma reduces_ex_to_reduces:
    forall cg o cg',
    ReducesEx cg o cg' ->
    Reduces cg o cg'.
  Proof.
    intros.
    inversion H; subst; clear H.
    assert (R: cg_add_tee vs' o es = make_tee o nx nx' ny :: es) by eauto.
    rewrite <- R.
    auto using reduces_step, reduces_ex_to_reduces.
  Qed.

  Lemma reduces_ex_iff:
    forall cg o cg',
    Reduces cg o cg' <->
    ReducesEx cg o cg'.
  Proof.
    split; eauto using reduces_to_reduces_ex, reduces_ex_to_reduces.
  Qed.

  Definition make_cg x : computation_graph := (make x, nil).

  Inductive CG (x:tid): trace -> computation_graph -> Prop :=
  | cg_nil:
    CG x nil (make_cg x)
  | cg_cons:
    forall cg o t cg',
    CG x t cg ->
    Reduces cg o cg' ->
    CG x (o::t) cg'.

  Definition cg_tees (cg:computation_graph) := snd cg.

  Definition cg_nodes (cg:computation_graph) := fst cg.

  Definition to_edges (v:tee) := inter v :: intra v :: nil.

  Definition cg_edges cg :=
  flat_map to_edges (cg_tees cg).

  Definition cg_lookup x cg :=
  match MT.find x (cg_ids (cg_nodes cg)) with
  | Some (n::_) => Some {| node_task := x; node_id := n |}
  | _ => None
  end.

  (** Any node in the CG graph must be in the nodes. *)

  Definition WellFormedEdges (cg:computation_graph) :=
  forall n1 n2,
  FGraph.Edge (cg_edges cg) (n1, n2) ->
  Contains n1 (cg_ids (cg_nodes cg)) /\ Contains n2 (cg_ids (cg_nodes cg)).

  Lemma wf_edges_reduces:
    forall cg o cg',
    WellFormedEdges cg ->
    Reduces cg o cg' ->
    WellFormedEdges cg'.
  Proof.
    intros.
    apply reduces_to_reduces_ex in H0.
    inversion H0; subst; clear H0.
    assert (Hneq: op_src o <> op_dst o) by eauto using reduces_src_neq_dst, Nodes.reduces_ex_to_reduces.
    unfold WellFormedEdges; intros.
    inversion H1; subst; clear H1; simpl in *.
    - apply MT.add_3 in H3; auto.
      assert (R: nx' :: nx :: lx = S (cg_last_id vs) :: n :: l). {
        rewrite MT_Facts.add_mapsto_iff in H2.
        destruct H2 as [(?,?)|(N,?)]; auto.
        contradiction N; trivial.
      }
      inversion R; subst; clear R.
      assert (R: ny :: ly = S (S (cg_last_id vs)) :: nil). {
        rewrite MT_Facts.add_mapsto_iff in H3.
        destruct H3 as [(?,?)|(N,?)]; auto.
        contradiction N; trivial.
      }
      inversion R; subst; clear R.
      destruct H0 as [E|[E|?]]; try (inversion E; subst; clear E).
      + auto using contains_add_1, contains_add_2 with *.
      + auto using contains_add_1, contains_add_2 with *.
      + apply H in H0.
        destruct H0.
        simpl in *.
        split.
        * destruct (tid_eq_dec (node_task n1) a). {
            inversion H0; subst.
            assert (l0 = n :: l) by eauto using MT_Facts.MapsTo_fun; subst.
            auto using contains_add_1, contains_add_2 with *.
          }
          destruct (tid_eq_dec (node_task n1) b). {
            inversion H0; subst.
            destruct l0. {
              inversion H7.
            }
            contradiction H5;
            eauto using in_def, maps_to_def.
          }
          eauto using contains_add_1, contains_add_2, contains_add_3 with *.
        * destruct (tid_eq_dec (node_task n2) a). {
            inversion H1; subst.
            assert (l0 = n :: l) by eauto using MT_Facts.MapsTo_fun; subst.
            auto using contains_add_1, contains_add_2 with *.
          }
          destruct (tid_eq_dec (node_task n2) b). {
            inversion H1; subst.
            destruct l0. {
              inversion H7.
            }
            contradiction H5;
            eauto using in_def, maps_to_def.
          }
          eauto using contains_add_1, contains_add_2, contains_add_3 with *.
    - apply MT.add_3 in H3; auto.
      assert (R: nx' :: nx :: lx = S (cg_last_id vs) :: n :: l). {
        rewrite MT_Facts.add_mapsto_iff in H2.
        destruct H2 as [(?,?)|(N,?)]; auto.
        contradiction N; trivial.
      }
      inversion R; subst; clear R.
      destruct H0 as [E|[E|?]]; try (inversion E; subst; clear E).
      + eauto using contains_add_2, maps_to_def, contains_def, List.in_eq.
      + eauto using contains_add_1, maps_to_def, contains_def, List.in_eq, List.in_cons.
      + apply H in H0.
        destruct H0.
        simpl in *.
        split.
        * destruct (tid_eq_dec (node_task n1) a). {
            inversion H0; subst.
            assert (l0 = n :: l) by eauto using MT_Facts.MapsTo_fun; subst.
            auto using contains_add_1, contains_add_2 with *.
          }
          apply contains_add_2; auto.
        * destruct (tid_eq_dec (node_task n2) a). {
            inversion H1; subst.
            assert (l0 = n :: l) by eauto using MT_Facts.MapsTo_fun; subst.
            auto using contains_add_1, contains_add_2 with *.
          }
          apply contains_add_2; auto.
  Qed.

  Let WellFormedNodes (cg:computation_graph) :=
  forall n,
  Graph.In (FGraph.Edge (cg_edges cg)) n ->
  Contains n (cg_ids (cg_nodes cg)).

  Let well_formed_nodes_to_edges:
    forall cg,
    WellFormedNodes cg ->
    WellFormedEdges cg.
  Proof.
    unfold WellFormedNodes, WellFormedEdges.
    eauto 6 using in_left, in_right.
  Qed.

  Let well_formed_edges_to_nodes:
    forall cg,
    WellFormedEdges cg ->
    WellFormedNodes cg.
  Proof.
    unfold WellFormedNodes, WellFormedEdges.
    intros.
    destruct H0 as ((v1,v2),(Hx,[?|?])); simpl in *; subst;
      apply H in Hx;
      destruct Hx;
      auto.
  Qed.

  Let well_formed_edges_iff:
    forall cg,
    WellFormedNodes cg <->
    WellFormedEdges cg.
  Proof.
    split; eauto.
  Qed.

  Let wf_nodes_preservation:
    forall cg o cg',
    WellFormedNodes cg ->
    Reduces cg o cg' ->
    WellFormedNodes cg'.
  Proof.
    intros.
    rewrite well_formed_edges_iff in *; auto.
    eauto using wf_edges_reduces.
  Qed.

  Let cg_edges_make:
    forall x,
    cg_edges (make_cg x) = nil.
  Proof.
    intros.
    unfold cg_edges, make_cg.
    auto.
  Qed.

  Let wf_nodes_make:
    forall x,
    WellFormedNodes (make_cg x).
  Proof.
    unfold WellFormedNodes.
    intros.
    rewrite cg_edges_make in *.
    simpl in *.
    destruct H as (e, (Hx, Hy)).
    inversion Hx.
  Qed.

  Let wf_nodes_0:
    forall x t cg,
    CG x t cg ->
    WellFormedNodes cg.
  Proof.
    induction t; intros. {
      inversion H.
      auto using wf_nodes_make.
    }
    inversion H; subst.
    eauto.
  Qed.

  Lemma node_in_ids:
    forall x t cg n,
    CG x t cg ->
    Graph.In (FGraph.Edge (cg_edges cg)) n ->
    Contains n (cg_ids (cg_nodes cg)).
  Proof.
    intros.
    apply wf_nodes_0 in H.
    unfold WellFormedNodes in *.
    auto.
  Qed.

  Lemma node_in_cg:
    forall x t cg n,
    CG x t cg ->
    Graph.In (FGraph.Edge (cg_edges cg)) n ->
    In (node_task n) (cg_nodes cg).
  Proof.
    intros.
    eapply node_in_ids in H0; eauto
    using contains_to_in.
  Qed.

End Edges.

Section Defs.

  Lemma in_make:
    forall t,
    Nodes.In t (cg_nodes (make_cg t)).
  Proof.
    intros.
    simpl.
    auto using Nodes.in_make.
  Qed.

  (**
    Ensure the names are being used properly; no continue edges after a task
    has been termianted (target of a join).
    *)

  Inductive edge_type :=
  | CONTINUE_EDGE
  | FORK_EDGE
  | JOIN_EDGE.

  Inductive Edge : edge_type -> (node * node) -> tee -> Prop :=
  | edge_continue:
    forall t,
    Edge CONTINUE_EDGE (intra t) t
  | edge_fork:
    forall t,
    Edge FORK_EDGE (inter t) t
  | edge_join:
    forall t,
    Edge JOIN_EDGE (inter t) t.

  Inductive Prec e t : Prop :=
  | prec_def:
    forall k,
    Edge k e t ->
    Prec e t.

  Variable cg: computation_graph.

  Let HB_Edge_alt e := List.Exists (Prec e) (cg_tees cg).

  Definition HB_Edge := FGraph.Edge (cg_edges cg).

  Definition HB := Reaches HB_Edge.

  Definition MHP x y : Prop := ~ HB x y /\ ~ HB y x.

  Let in_edges_to_tees:
    forall e,
    List.In e (cg_edges cg) ->
    exists x, List.In x (cg_tees cg) /\ Prec e x.
  Proof.
    unfold cg_edges.
    intros.
    rewrite in_flat_map in *.
    destruct H as (x, (Hi, He)).
    exists x; split; auto.
    unfold to_edges in *.
    destruct He as [?|[?|?]]; subst.
    - destruct x.
      destruct ntype0;
      eauto using prec_def, edge_fork, edge_join.
    - eauto using prec_def, edge_continue.
    - inversion H.
  Qed.

  Let in_tees_to_edges:
    forall x e,
    List.In x (cg_tees cg) ->
    Prec e x ->
    List.In e (cg_edges cg).
  Proof.
    unfold cg_edges.
    intros.
    rewrite in_flat_map in *.
    exists x.
    split; auto.
    unfold to_edges.
    destruct H0; inversion H0; subst; auto using in_eq, in_cons.
  Qed.

  Lemma hb_edge_spec:
    forall e,
    HB_Edge e <-> exists x, List.In x (cg_tees cg) /\ Prec e x.
  Proof.
    unfold HB_Edge, HB_Edge_alt, FGraph.Edge;
    split; intros.
    - auto.
    - destruct H as (?,(?,?)); eauto.
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
    compute.
    apply reaches_edge_false.
  Qed.

End HB.

Module WellFormed.
  Inductive Forks : trace -> tid -> list tid -> Prop :=
  | forks_nil:
    forall x,
    Forks nil x (x::nil)
  | forks_cons_fork:
    forall ts l z x y,
    (* x -> y *)
    List.In x l ->
    ~ List.In y l ->
    Forks ts z l ->
    Forks ({|op_t:=FORK; op_src:=x; op_dst:=y |}::ts) z (y::l)
  | forks_cons_join:
    forall ts l x y z,
    List.In x l ->
    List.In y l ->
    Forks ts z l ->
    Forks ({|op_t:=JOIN; op_src:=x; op_dst:=y |}::ts) z l.

  Inductive Joins: trace -> list tid -> Prop :=
  | joins_nil:
    Joins nil nil
  | joins_cons_fork:
    forall ts l x y,
    ~ List.In x l ->
    ~ List.In y l ->
    Joins ts l ->
    Joins ({|op_t:=FORK; op_src:=x; op_dst:=y |}::ts) l
  | joins_cons_join:
    forall ts l x y,
    ~ List.In x l ->
    Joins ts l ->
    Joins ({|op_t:=JOIN; op_src:=x; op_dst:=y |}::ts) l.

  Inductive Running : trace -> tid -> list tid -> Prop :=
  | running_nil:
    forall x,
    Running nil x (x::nil)
  | running_cons_fork:
    forall ts l x y z,
    (* x -> y *)
    List.In x l ->
    ~ List.In y l ->
    Running ts z l ->
    Running ({|op_t:=FORK; op_src:=x; op_dst:=y |}::ts) z (y::l)
  | running_cons_join:
    forall ts l x y z,
    List.In x l ->
    Running ts z l ->
    Running ({|op_t:=JOIN; op_src:=x; op_dst:=y |}::ts) z (remove TID.eq_dec y l).

  Section Defs.

  Require Import Aniceto.List.

  Lemma forks_no_dup:
    forall ts x l,
    Forks ts x l  ->
    NoDup l.
  Proof.
    induction ts; intros. {
      inversion H.
      subst.
      auto using NoDup_cons, NoDup_nil.
    }
    inversion H; subst; clear H; 
    eauto using NoDup_cons.
  Qed.

  Lemma running_incl_forked:
    forall ts ks rs x,
    Running ts x rs ->
    Forks ts x ks ->
    incl rs ks.
  Proof.
    induction ts; intros. {
      inversion H.
      inversion H0.
      auto using incl_refl.
    }
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    - eauto using incl_cons_cons.
    - inversion H0; subst.
      eauto using remove_incl, incl_tran.
  Qed.

  Lemma in_running_in_fork:
    forall ts vs rs x y,
    Running ts x rs ->
    Forks ts x vs ->
    List.In y rs ->
    List.In y vs.
  Proof.
    intros.
    assert (incl rs vs) by eauto using running_incl_forked.
    auto.
  Qed.

  Lemma running_not_in_joins:
    forall ts js rs x,
    Running ts x rs ->
    Joins ts js ->
    forall y, List.In y rs -> ~ List.In y js.
  Proof.
    induction ts; intros. {
      inversion H; inversion H0;
      intuition.
    }
    destruct a as (a,src,dst).
    destruct a; inversion H; inversion H0; subst; clear H H0.
    + destruct H1; subst; eauto.
    + eauto using remove_in.
  Qed.

  Lemma joins_not_in_running:
    forall ts js rs x,
    Running ts x rs ->
    Joins ts js ->
    forall y, List.In y js -> ~ List.In y rs.
  Proof.
    induction ts; intros. {
      inversion H; inversion H0; subst.
      inversion H1.
    }
    destruct a as (a,src,dst).
    destruct a; inversion H; inversion H0; subst; clear H H0.
    + unfold not; intros Hx.
      destruct Hx.
      * subst; contradiction.
      * assert (Hx := IHts _ _ _ H9 H16 _ H1); contradiction.
    + unfold not; intros Hx.
      apply remove_in in Hx.
      assert (Hy := IHts _ _ _ H8 H14 _ H1).
      contradiction.
  Qed.

  Lemma running_no_dup:
    forall ts rs x,
    Running ts x rs ->
    NoDup rs.
  Proof.
    induction ts; intros; inversion H; subst.
    - auto using no_dup_cons_nil.
    - eauto using NoDup_cons.
    - eauto using no_dup_remove.
  Qed.
(*
  Let forks_in_cg:
    forall l x t cg ts,
    CG x l cg ->
    Forks l x ts ->
    List.In t ts ->
    Nodes.In t (cg_nodes cg).
  Proof.
    induction l; intros. {
      inversion H0; subst.
      destruct H1. {
        subst.
        inversion H; subst.
        auto using Top.in_make.
      }
      inversion H1.
    }
    inversion H0; subst; clear H0.
    - destruct H1;
      inversion H; subst; clear H.
      + auto using in_fork_1.
      + eauto using in_fork_2.
    - inversion H; subst; clear H.
      eauto using in_join_2.
  Qed.
*)
(*
  (**
   Building a CG from a trace.
   *)
  Lemma cg_spec:
    forall x l ts,
    Forks l x ts ->
    CG x l (trace_to_cg x l).
  Proof.
    induction l; intros. {
      unfold trace_to_cg.
      simpl.
      auto using cg_nil.
    }
    destruct a as (t);
    try destruct t; simpl in *;
    inversion H; subst.
    - assert (op_src0 <> op_dst0). {
        intuition; subst; contradiction.
      }
      eauto using cg_cons_fork, forks_in_cg.
    - apply cg_cons_join; eauto using forks_in_cg.
  Qed.
*)
(*
  Lemma cg_node_task:
    forall x l cg t n,
    CG x l cg ->
    MT.MapsTo t n (cg_nodes cg) ->
    node_task n = t.
  Proof.
    induction l; intros. {
      inversion H.
      subst.
      unfold make_cg in *.
      simpl in *.
      rewrite MT_Facts.add_mapsto_iff in H0.
      destruct H0 as [(?,?)|(?,?)].
      + subst; auto.
      + rewrite MT_Facts.empty_mapsto_iff in H1; contradiction.
    }
    inversion H; simpl in *; subst.
    + rename a0 into a; rename cg0 into cg.
      assert (mt : exists na, MT.MapsTo a na (cg_nodes cg)). {
          unfold In in *.
          apply MT_Extra.in_to_mapsto in H4.
          assumption.
        }
      destruct mt as (na, mt).
      assert (node_task na = a) by eauto.
      destruct (tid_eq_dec t a); subst.
      * assert (Hx:=mt).
        apply maps_to_fork_1 with (b:=b) in Hx; auto.
        assert (n = next_intra (node_task na) (cg_last_id cg))
        by eauto using MT_Facts.MapsTo_fun;subst.
        unfold next_intra; auto.
      * destruct (tid_eq_dec t b). {
          subst.
          apply maps_to_fork_2 with (na:=na) in H0; auto.
          subst.
          auto.
        }
        apply maps_to_fork_3 with (x:=node_task na) (y:=b) (z:=t) (n:=n) (nx:=na) in H0; auto.
        eauto.
    + rename a0 into a; rename cg0 into cg.
      assert (mt : exists na, MT.MapsTo a na (cg_nodes cg)). {
        unfold In in *.
        apply MT_Extra.in_to_mapsto in H4.
        assumption.
      } destruct mt as (na, mta).
      assert (mtb : exists nb, MT.MapsTo b nb (cg_nodes cg)). {
        unfold In in *.
        apply MT_Extra.in_to_mapsto in H4.
        assumption.
      } destruct mtb as (nb, mtb).
      destruct (tid_eq_dec t a); subst. {
        assert (Hx := mta).
        apply maps_to_join_1 with (b:=b) in mta; auto. {
          assert (n = next_intra (node_task na) (cg_last_id cg))
          by eauto using MT_Facts.MapsTo_fun;subst.
          unfold next_intra.
          simpl.
          eauto.
        }
        eauto.
      }
      destruct (tid_eq_dec t b); subst. {
        apply maps_to_join_2 with (na:=na) (b:=b) (nb:=n) in H0; eauto.
      }
      apply maps_to_join_3 with (x:=a) (y:=b) (z:=t) (nx:=na) in H0; eauto.
  Qed.*)
(*
  Lemma maps_to_fork_1:
    forall x y n cg a l,
    CG a l cg ->
    MT.MapsTo x n (cg_nodes cg) ->
    MT.MapsTo x (next_intra x (cg_last_id cg)) (cg_nodes (cg_fork x y cg)).
  Proof.
    intros.
    assert (R: next_intra x (cg_last_id cg) = next_intra (node_task n) (cg_last_id cg)). {
      assert (R: node_task n = x) by
      eauto using cg_node_task.
      rewrite R.
      trivial.
    }
    rewrite R.
    eauto using maps_to_fork_1, cg_node_task.
  Qed.

  Lemma maps_to_fork_2:
    forall x y n cg a l,
    CG a l cg ->
    x <> y ->
    In x cg ->
    MT.MapsTo y n (cg_nodes (cg_fork x y cg)) ->
    n = fork_inter y (cg_last_id cg).
  Proof.
    unfold In; intros.
    apply MT_Extra.in_to_mapsto in H1.
    destruct H1.
    eauto using maps_to_fork_2, cg_node_task.
  Qed.

  Lemma maps_to_fork_3:
    forall x y z n cg l a,
    CG a l cg ->
    z <> x ->
    z <> y ->
    In x cg ->
    MT.MapsTo z n (cg_nodes (cg_fork x y cg)) ->
    MT.MapsTo z n (cg_nodes cg).
  Proof.
    unfold In; intros.
    apply MT_Extra.in_to_mapsto in H2.
    destruct H2 as  (nx, ?).
    apply maps_to_fork_3 with (x:=x) (y:=y) (nx:=nx); eauto using cg_node_task.
  Qed.

  Lemma maps_to_join_1:
    forall x y n cg a l,
    CG a l cg ->
    In y cg ->
    MT.MapsTo x n (cg_nodes cg) ->
    MT.MapsTo x (next_intra x (cg_last_id cg)) (cg_nodes (cg_join x y cg)).
  Proof.
    intros.
    assert (R: next_intra x (cg_last_id cg) = next_intra (node_task n) (cg_last_id cg)). {
      assert (R: node_task n = x) by
      eauto using cg_node_task.
      rewrite R.
      trivial.
    }
    rewrite R.
    eauto using maps_to_join_1, cg_node_task.
  Qed.

  Lemma maps_to_join_2:
    forall x y n cg a l,
    CG a l cg ->
    x <> y ->
    In x cg ->
    MT.MapsTo y n (cg_nodes (cg_join x y cg)) ->
    MT.MapsTo y n (cg_nodes cg).
  Proof.
    unfold In.
    intros.
    apply MT_Extra.in_to_mapsto in H1.
    destruct H1.
    eauto using maps_to_join_2, cg_node_task.
  Qed.

  Lemma maps_to_join_3:
    forall x y z n cg a l,
    CG a l cg ->
    z <> x ->
    z <> y ->
    In x cg ->
    MT.MapsTo z n (cg_nodes (cg_join x y cg)) ->
    MT.MapsTo z n (cg_nodes cg).  
  Proof.
    unfold In.
    intros.
    apply MT_Extra.in_to_mapsto in H2.
    destruct H2 as (nx,?).
    apply maps_to_join_3 with (x:=x) (y:=y) (nx:=nx); eauto using cg_node_task.
  Qed.

  (** If we get a tee from a CG, the intra nodes are referring to
   the same task. *)

  Lemma tee_continue:
    forall l x y v cg a,
    CG a l cg ->
    List.In v (cg_tees cg) ->
    intra v = (x, y) ->
    node_task x = node_task y.
  Proof.
    induction l; intros. {
      inversion H.
      subst.
      simpl in *.
      contradiction.
    }
    inversion H; subst; clear H;
    rename cg0 into cg; rename a1 into a.
    - unfold In in *.
      apply MT_Extra.in_to_mapsto in H5.
      destruct H5 as (n, mt).
      assert (R: cg_tees (cg_fork a b cg) = make_fork (cg_last_id cg) n b :: cg_tees cg)
      by auto using tee_fork_rw.
      rewrite R in *.
      destruct H0. {
        subst.
        inversion H1; subst.
        simpl.
        trivial.
      }
      eauto.
    - unfold In in *.
      apply MT_Extra.in_to_mapsto in H5.
      destruct H5 as (na, mta).
      apply MT_Extra.in_to_mapsto in H7.
      destruct H7 as (nb, mtb).
      assert (R: cg_tees (cg_join a b cg) = make_join (cg_last_id cg) na nb :: cg_tees cg)
      by auto using tee_join_rw.
      rewrite R in *.
      destruct H0. {
        subst; inversion H1.
        auto.
      }
      eauto.
  Qed.

  Let cg_last_id_rw_fork:
    forall cg a b,
    MT.In a (cg_nodes cg) ->
    cg_last_id (cg_fork a b cg) = S (S (cg_last_id cg)).
  Proof.
    intros.
    unfold cg_fork.
    destruct (tee_fork_dec a b cg) as [(?,(?,(R,(?,?))))|(?,?)].
    - unfold tee_last_id.
      rewrite R in *; subst.
      auto.
    - contradiction. 
  Qed.*)
(*
  Lemma cg_to_nodes:
    forall a l cg ns n,
    CG a l cg ->
    CGNodes.CGNodes a l ns n ->
    MT.MapsTo a {| node_task := a; node_id := n |} (cg_nodes cg) ->
    CGNodes.MapsTo a n ns.
  Proof.
    intros.
    
  Qed.
    
*)
(*
  Lemma cg_to_nodes:
    forall a l cg,
    CG a l cg ->
    exists ns, CGNodes.CGNodes a l ns (cg_last_id cg).
  Proof.
    induction l; intros. {
      inversion H.
      simpl in *.
      eauto using CGNodes.cg_nodes_nil.
    }
    inversion H; subst.
    - apply IHl in H2.
      destruct H2 as (ns, Hn).
      rewrite cg_last_id_rw_fork; auto.
      exists ((a1, S (cg_last_id cg0)) :: (b, S (S (cg_last_id cg0))) :: ns).
      apply CGNodes.cg_nodes_cons_fork with (cg_last_id cg0); auto.
  Qed.
*)
(*
  Let tee_fork_rw:
    forall x y cg cg',
    tee_fork x y cg' = tee_fork x y cg ->
    cg' = cg.
  Proof.
    intros.
    destruct (tee_fork_dec x y cg'), (tee_fork_dec x y cg).
    - destruct e as (t, (n, (mt, (R,?)))). 
      destruct e0 as (t', (n', (mt', (R',?)))). 
    remember (te
    unfold tee_fork.
    intros.
    destruct
  Qed.
*)
(*
  Let cg_fork_rw:
    forall x y cg cg',
    In x cg' ->
    x <> y ->
    In x cg ->
    cg_fork x y cg' = cg_fork x y cg ->
    cg' = cg.
  Proof.
    intros.
    unfold cg_fork in *.
    destruct (tee_fork_dec x y cg'), (tee_fork_dec x y cg).
    - destruct e as (?, (?, (R1,(?,?)))).
      destruct e0 as (?, (?, (R2,(?,?)))).
      rewrite R1 in *; rewrite R2 in *.
      subst.
      simpl in *.
  Qed.
  *)

(*
  Let cg_make_inv:

    cg_fork x y (make_cg a) = cg_fork x y cg ->
    cg = 
*)
(*
  Lemma fork_is_gt:
    forall vs es x,
    WellFormedEdges (vs, es) ->
    ~ Nodes.In (node_task x) vs ->
    forall y, ~ HB_Edge (vs, es) (x, y).
  Proof.
    intros.
    unfold HB_Edge.
    unfold not; intros.
    apply H in H1.
    destruct H1.
    contradiction H0.
    auto using Nodes.contains_to_in.
  Qed.
*)
  End Defs.

End WellFormed.

Module Lang.

  Definition from_effect (e:Lang.effect) :=
  match e with
  | (x, Lang.FUTURE y) => Some {|op_t:=FORK; op_src:=x; op_dst:=y|}
  | (x, Lang.FORCE y) => Some {|op_t:=JOIN; op_src:=x; op_dst:=y|}
  | _ => None
  end.

  Definition from_effects := List.omap from_effect.

  (** Compute a CG from a trace of our language. *)
(*
  Definition effects_to_cg (x:tid) ts := trace_to_cg x (from_effects ts).*)

End Lang.
