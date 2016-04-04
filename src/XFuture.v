Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import HJ.Tid.
Require Import HJ.Mid.
Require Import HJ.Cid.
Require Import HJ.Var.
Require Import HJ.Dep.

(* ----- end of boiler-plate code ---- *)

Set Implicit Arguments.


Module Lang.

  Inductive word :=
  | Num: nat -> word    (* number *)
  | TaskLabel : tid -> word  (* task-id *)
  | HeapLabel : mid -> word.  (* heap-id *)

  Inductive value :=
  | Var: var -> value
  | Word: word -> value.

  Inductive expression :=
  | Value: value -> expression
  | Deref: value -> expression
  | Malloc: expression
  | Future: list value -> list var -> program -> expression
  | Force: value -> expression
  with instruction :=
  | Assign: var -> expression -> instruction
  | Store: value -> expression -> instruction
  with program :=
  | Ret: value -> program
  | Seq: instruction -> program -> program
  | If: value -> program -> program -> program.

  Infix ";;" := Seq (at level 62, right associativity).

  Definition store := MV.t word.
  Definition mk_store := @MV.empty word.

  Definition task := (store * program) % type.

  Definition task_update_program f (t:task) : task :=
  match t with
  | (s, p) => (s, f p)
  end.

  Definition task_set_program (p:program) (t:task) : task :=
  task_update_program (fun _ => p) t.

  Definition task_update_instruction f (t:task) : task :=
  task_update_program
  (fun p=>
    match p with
    | Seq i p => Seq (f i) p
    | _ => p
    end
  )
  t.

  Definition eval w (i:instruction) : instruction :=
  let v := Value (Word w) in
  match i with
  | Assign x e => Assign x v
  | Store x e => Store x v
  end.

  Definition task_put_var (x:var) (w:word) (t:task) : task :=
  match t with
  | (s, p) => (MV.add x w s, p)
  end.

  Definition taskmap := MT.t task.
  Definition mk_taskmap := @MT.empty task.

  Definition tm_update x f tm : taskmap :=
  match MT.find x tm with
  | Some t => MT.add x (f t) tm
  | _ => tm
  end.

  Definition tm_set_program t p tm :=
  tm_update t (task_set_program p) tm.

  Definition tm_put_var t x v tm :=
  tm_update t (task_put_var x v) tm.

  Definition heap := MM.t (option word).

  Definition heap_put (x:mid) (v:option word) (hs:heap) : heap :=
  MM.add x v hs.

  Definition mk_heap := @MM.empty (option word).

  Definition state := (heap * taskmap) % type.

  Definition s_tasks (s:state) : taskmap :=
  match s with
  | (_, tm) => tm
  end.

  Definition s_heap (s:state) : heap :=
  match s with
  | (hm, _) => hm
  end.

  Definition s_tm_update f (s:state) : state :=
  match s with
  | (hm, tm) => (hm, f tm)
  end.

  Definition s_heap_update f (s:state) : state :=
  match s with
  | (hm, tm) => (f hm, tm)
  end.

  Definition s_set_program t p s :=
  s_tm_update (tm_set_program t p) s.

  Definition s_local_put t x v tm :=
  s_tm_update (tm_put_var t x v) tm.

  Definition s_global_put x v s :=
  s_heap_update (fun hs => MM.add x v hs) s.

  Definition s_spawn t l p s :=
  s_tm_update (fun tm => MT.add t (l, p) tm) s. 

  Inductive op := 
  | READ: mid -> op
  | WRITE: mid -> op
  | FUTURE: tid -> op
  | FORCE: tid -> op
  | TAU: op.

  Definition effect := (tid * op) % type.

  Inductive Local (s:state) t : store -> Prop :=
  | store_def:
    forall p l,
    MT.MapsTo t (l, p) (s_tasks s) ->
    Local s t l.

  Inductive Program s t (p:program) : Prop :=
  | program_def:
    forall l,
    MT.MapsTo t (l, p) (s_tasks s) ->
    Program s t p.

  Inductive Expression : instruction -> expression -> Prop :=
  | expression_assign:
    forall x e,
    Expression (Assign x e) e
  | expression_store:
    forall v e,
    Expression (Store v e) e.

  Inductive VReduces (s:state) (t:tid) : value -> word -> Prop :=
  | v_reduces_var:
    forall x w m,
    Local s t m ->
    MV.MapsTo x w m ->
    VReduces s t (Var x) w
  | v_reduces_word:
    forall w,
    VReduces s t (Word w) w.

  (** Reduction rules *)

  Inductive Bind (s:state) (t:tid): list var -> list value -> store -> Prop :=
  | bind_nil:
    Bind s t nil nil mk_store
  | bind_cons:
    forall xs vs x v w m',
    Bind s t xs vs m' ->
    VReduces s t v w ->
    Bind s t (x::xs) (v::vs) (MV.add x w m').

  Inductive Stopped (s:state) (t:tid) (w:word) : Prop :=
  | stopped_def:
    forall v,
    Program s t (Ret v) ->
    VReduces s t v w ->
    Stopped s t w.

  Inductive EReduces : (state * expression) -> effect -> (state * word) -> Prop :=
  | e_reduces_malloc:
    forall h t s,
    ~ MM.In h (s_heap s) ->
    EReduces (s, Malloc) (t,TAU) (s_global_put h None s, HeapLabel h)
  | e_reduces_load:
    forall s t v w h,
    VReduces s t v (HeapLabel h) ->
    MM.MapsTo h (Some w) (s_heap s) ->
    EReduces (s, Deref v) (t, READ h) (s, w)
  | e_reduces_future:
    forall xs vs t s p t' (l':store),
    Bind s t xs vs l' ->
    ~ MT.In t' (s_tasks s) ->
    EReduces (s, Future vs xs p) (t, FUTURE t') ((s_spawn t' l' p) s, TaskLabel t')
  | e_reduces_force:
    forall v t' w t s,
    VReduces s t v (TaskLabel t') ->
    Stopped s t' w ->
    EReduces (s,Force v) (t,FORCE t') (s, w).


  Inductive IReduces: (state * instruction) -> effect -> state -> Prop :=
  | i_reduces_assign:
    forall s t w x v,
    VReduces s t v w ->
    IReduces (s, Assign x (Value v)) (t,TAU) (s_local_put t x w s)
  | i_reduces_store:
    forall s s' t w h v v',
    VReduces s t v (HeapLabel h) ->
    VReduces s t v' w ->
    IReduces (s, Store v (Value v')) (t, WRITE h) (s_global_put h (Some w) s').

  Inductive PReduces: (state * program) -> effect -> (state * program) -> Prop :=
  | p_reduces_eval:
    forall s s' i e w p o,
    Expression i e ->
    EReduces (s,e) o (s',w) ->
    PReduces (s, Seq i p) o (s', Seq (eval w i) p)
  | p_reduces_seq:
    forall s i p s' o,
    IReduces (s,i) o s' ->
    PReduces (s, Seq i p) o (s', p)
  | i_reduces_if_zero:
    forall s t v p1 p2,
    VReduces s t v (Num 0) ->
    PReduces (s, If v p1 p2) (t,TAU) (s, p2)
  | i_reduces_if_succ:
    forall s t v n p1 p2,
    VReduces s t v (Num (S n)) ->
    PReduces (s, If v p1 p2) (t,TAU) (s, p1).

  Inductive Reduces: state -> effect -> state -> Prop :=
  | reduces_run:
    forall s s' t p p' o,
    Program s t p ->
    PReduces (s,p) (t,o) (s', p') ->
    Reduces s (t,o) (s_set_program t p' s').


  Definition is_f_op o :=
  match o with
  | FUTURE _ => true
  | FORCE _ => true
  | _ => false
  end.

  Definition is_m_op o :=
  match o with
  | WRITE _ => true
  | READ _ => true
  | _ => false
  end.
End Lang.

Require Import Aniceto.Graphs.DAG.
Require Import Coq.Relations.Relation_Operators.
Require Aniceto.Graphs.Graph.

Require Import Coq.Structures.OrderedTypeEx.

Module NAT_PAIR := PairOrderedType Nat_as_OT Nat_as_OT.


Module CGExtra.


Section Defs.

  Structure node := {
    node_task: tid;
    node_dag_id: nat;
    node_spawn_id: nat;
    node_continue_id: nat
  }.

  Definition node_sc v := (node_spawn_id v, node_continue_id v).

  (** Spawn-Continue order *)

  Definition sc_lt x y := NAT_PAIR.lt (node_sc x) (node_sc y).

  (** DAG id order *)

  Definition dag_lt x y := node_dag_id x < node_dag_id y.

  Definition edge := (node * node) % type.

  Inductive node_type := SPAWN | JOIN.

  Structure triplet := {
    ntype: node_type;
    intra : edge;
    inter : edge
  }.

  Inductive Check : triplet -> Prop :=
  | check_spawn:
    forall x y dx sx cx dx',
    dx < dx' ->
    x <> y ->
    Check
    {|
      ntype := SPAWN;
      intra :=
      (
        {|
          node_task := x;
          node_dag_id := dx;
          node_spawn_id := sx;
          node_continue_id := cx
        |},
        {|
          node_task := x;
          node_dag_id := dx';
          node_spawn_id := sx;
          node_continue_id := S cx
        |}
      );
      inter :=
      (
        {|
          node_task := x;
          node_dag_id := dx;
          node_spawn_id := sx;
          node_continue_id := cx
        |},
        {|
          node_task := y;
          node_dag_id := S dx';
          node_spawn_id := S sx;
          node_continue_id := 0
        |}
      )
    |}
  | check_join:
    forall x y dx sx cx dx' cy sy dy,
    dx < dx' ->
    dy < dx' ->
    x <> y ->
    Check
    {|
      ntype := JOIN;
      intra :=
      (
        {|
          node_task := x;
          node_dag_id := dx;
          node_spawn_id := sx;
          node_continue_id := cx
        |},
        {|
          node_task := x;
          node_dag_id := dx';
          node_spawn_id := sx;
          node_continue_id := S cx
        |}
      );
      inter :=
      (
        {|
          node_task := y;
          node_dag_id := dy;
          node_spawn_id := sy;
          node_continue_id := cy
        |},
        {|
          node_task := x;
          node_dag_id := dx';
          node_spawn_id := sx;
          node_continue_id := S cx
        |}
      )
    |}.

  Lemma check_intra_eq_task:
    forall v,
    Check v ->
    node_task (fst (intra v)) = node_task (snd (intra v)).
  Proof.
    intros.
    inversion H; simpl in *; auto.
  Qed.

  Lemma check_inter_neq_task:
    forall v,
    Check v ->
    node_task (fst (inter v)) <> node_task (snd (inter v)).
  Proof.
    intros.
    inversion H; simpl in *; auto.
  Qed.

  Lemma check_inter_dag_spawn:
    forall v,
    Check v ->
    ntype v = SPAWN ->
    fst (intra v) = fst (inter v).
  Proof.
    intros.
    inversion H; simpl in *.
    - trivial.
    - rewrite <- H4 in *.
      inversion H0.
  Qed.

  Lemma check_intra_dag_join:
    forall v,
    Check v ->
    ntype v = JOIN ->
    snd (intra v) = snd (inter v).
  Proof.
    intros.
    inversion H; simpl in *; trivial.
    rewrite <- H3 in *.
    inversion H0.
  Qed.

  Lemma check_intra_sc_lt:
    forall v,
    Check v ->
    sc_lt (fst (intra v)) (snd (intra v)).
  Proof.
    intros.
    unfold sc_lt, node_sc, NAT_PAIR.lt.
    inversion H; simpl in *; eauto.
  Qed.

  Lemma check_inter_spawn_sc_lt:
    forall v,
    Check v ->
    ntype v = SPAWN ->
    sc_lt (fst (inter v)) (snd (inter v)).
  Proof.
    intros.
    unfold sc_lt, node_sc, NAT_PAIR.lt.
    inversion H; simpl in *; auto.
    rewrite <- H4 in *.
    inversion H0.
  Qed.

  Lemma check_dag_lt_intra:
    forall v,
    Check v ->
    dag_lt (fst (intra v)) (snd (intra v)).
  Proof.
    intros.
    unfold dag_lt.
    inversion H; simpl in *; auto.
  Qed.

  Lemma check_dag_lt_inter:
    forall v,
    Check v ->
    dag_lt (fst (inter v)) (snd (inter v)).
  Proof.
    intros.
    unfold dag_lt.
    inversion H; simpl in *; auto.
  Qed.

  Lemma check_dag_lt_spawn:
    forall v,
    Check v ->
    ntype v = SPAWN ->
    dag_lt (snd (intra v)) (snd (inter v)).
  Proof.
    intros.
    unfold dag_lt.
    inversion H; simpl in *; auto.
    rewrite <- H4 in *.
    inversion H0.
  Qed.

  Inductive Lookup t n: list triplet -> Prop :=
  | lookup_continue: 
    forall v l,
    snd (intra v) = n ->
    node_task n = t ->
    Lookup t n (v::l)
  | lookup_spawn:
    forall v l,
    ntype v = SPAWN ->
    snd (inter v) = n ->
    node_task n = t ->
    Lookup t n (v::l)
  | lookup_cons:
    forall v l,
    Lookup t n l ->
    Lookup t n (v::l).

  (**
    Ensure the names are being used properly; no continue edges after a task
    has been termianted (target of a join).
    *)

  Inductive Dangling : list triplet -> list tid -> Prop :=
  | dangling_nil:
    forall v,
    ntype v = SPAWN ->
    let x := node_task (fst (inter v)) in
    let y := node_task (snd (inter v)) in
    (* x -> y *)
    Dangling (v::nil) (y::x::nil)
  | dangling_cons_spawn:
    forall v vs ts,
    ntype v = SPAWN ->
    let x := node_task (fst (inter v)) in
    let y := node_task (snd (inter v)) in
    (* x -> y *)
    List.In x ts ->
    ~ List.In y ts ->
    Dangling vs ts ->
    Dangling (v::vs) (y::ts)
  | dangling_cons_join:
    forall v vs ts,
    ntype v = JOIN ->
    let x := node_task (fst (inter v)) in
    let y := node_task (snd (inter v)) in
    (* x <- y *)
    List.In x ts ->
    Dangling vs ts ->
    Dangling (v::vs) (remove TID.eq_dec y ts).

  (** Ensure that the CG is a DAG. *)

  Inductive DAG : list triplet -> nat -> Prop :=
  | dag_spawn:
    forall v,
    node_dag_id (fst (intra v)) = 0 ->
    DAG (v::nil) 2
  | dag_cons_spawn:
    forall vs n x nx v,
    DAG vs n ->
    Lookup x nx vs ->
    fst (inter v) = nx ->
    node_dag_id (snd (inter v)) = S n ->
    DAG (v::vs) (S (S n))
  | dag_cons_join:
    forall vs n x y nx ny v,
    DAG vs n ->
    Lookup x nx vs ->
    Lookup y ny vs ->
    DAG (v::vs) (S n).

  Definition SafeJoin v := prod_curry sc_lt (inter v).

  Definition RaceFree := Forall SafeJoin.


  Inductive Continue v : edge -> Prop :=
    continue_def:
      Continue v (intra v).

  Inductive Spawn: triplet -> edge -> Prop :=
    spawn_def:
      forall v,
      ntype v = SPAWN ->
      Spawn v (intra v).

  Inductive Join: triplet -> edge -> Prop :=
    join_def:
      forall v,
      ntype v = JOIN ->
      Join v (inter v).

  Inductive Prec t e : Prop :=
  | prec_continue:
    Continue t e ->
    Prec t e
  | prec_spawn:
    Spawn t e ->
    Prec t e
  | prec_join:
    Join t e ->
    Prec t e.

  Inductive ListEdge {A:Type} {B:Type} P l (e:B*B) : Prop :=
  | list_edge_def:
    forall (x:A),
    List.In x l ->
    P x e ->
    ListEdge P l e.

  Let LContinue := ListEdge Continue.
  Let LSpawn := ListEdge Spawn.
  Let LPrec := ListEdge Prec.

  Require Import Aniceto.Graphs.Graph.

  Inductive Reaches {A:Type} E (x y:A) : Prop :=
  | reaches_def:
    forall w,
    Walk2 E x y w ->
    Reaches E x y.

  Require Import Coq.Relations.Relation_Operators.

  (** Reflexive closure of continue. *)

  Definition ClosTransRefl {A:Type} E (x y:A) := Reaches E x y \/ x = y.

  Definition ContinueRefl ts x := ClosTransRefl (LContinue ts) x.

  Definition HB (ts:list triplet) := Reaches (LPrec ts).

  Definition PAR ts x y : Prop := ~ HB ts x y /\ ~ HB ts y x.

  (**
    We have a safe-spawn when the body of the spawn may run in parallel
    with the continuation of the spawn.
    *)

  Inductive SafeSpawn ts : triplet -> Prop :=
  | safe_spawn_eq:
    forall v,
    ntype v = SPAWN ->
    List.In v ts ->
    (forall y, ContinueRefl ts (snd (inter v)) y -> PAR ts y (snd (intra v) )) ->
    SafeSpawn ts v
  | safe_spawn_skip:
    forall v,
    ntype v = JOIN ->
    List.In v ts ->
    SafeSpawn ts v.

  Definition Safe ts := List.Forall (SafeSpawn ts) ts.
End Defs.
End CGExtra.

Module CG.
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
(*
  Let hb_add_edge_inv:
    forall x n cg n1 n2,
    MT.MapsTo x n (cg_tasks cg) ->
    HB
      {|
      cg_size := S (cg_size cg);
      cg_tasks := MT.add x (cg_size cg) (cg_tasks cg);
      cg_edges := ((x, n), (x, cg_size cg)) :: cg_edges cg |} n1 n2 ->
    False.
  Proof.
    intros.
    remember (cg_edges cg) as l.
    remember (((x, n), (x, cg_size cg))) as e.
    apply clos_trans_to_walk2 with (Edge:=fun e' => List.In e' (e::l)) in H0. {
      destruct H0 as (w, W2).
      assert (X:=W2).
      apply (DAG.dag_walk2_inv_cons_edge (hb_irrefl cg))) with (Lt:=Lt) in X. {
        destruct H1 as [?|[(w'',(?,(?,?)))|?]].
      
    }
  Qed.

  Let hb_inv_cg_future:
    forall x y cg n1 n2,
    HB (cg_future x y cg) n1 n2 ->
    HB cg n1 n2 \/
    (exists n, MT.MapsTo x n (cg_tasks cg) /\ n1 = (x,n) /\ n2 = (x, cg_size cg)) \/
    False.
  Proof.
    intros.
(*    unfold HB, cg_future, Prec in *.*)
    unfold cg_future in *.
    destruct (MT_Extra.find_rw x (cg_tasks cg)) as [(rw,?)|(e,(rw,?))];
    rewrite rw in *; clear rw; try intuition.
    remember (cg_edges {|
            cg_size := _;
            cg_tasks := _;
            cg_edges := _ |}) as l.
    simpl in *.
    apply clos_trans_to_walk2 with (Edge:=fun (e:edge) => List.In e l) in H. {
      destruct H as (w, W).
      assert (X:=W).
      subst.
      apply DAG.dag_walk2_inv_cons_edge with (Lt:=Lt) in X.
      - destruct X as [?|[(w',(?,(?,?)))|?]].
        + subst.
          inversion W; subst; clear W.
          right; left.
          exists e.
          split; auto.
          apply starts_with_eq in H.
          apply ends_with_eq in H1.
          auto.
        + subst.
          remember (y, S (cg_size cg)) as vy.
          remember (x, cg_size cg) as vx'.
          remember (x, e) as vx.
          apply DAG.dag_walk2_inv_cons_edge with (Lt:=Lt) in H1. {
            destruct H1 as [?|[(w'',(?,(?,?)))|?]].
            - rewrite H in *; clear H.
              simpl in W.
              assert (vc
              inversion W; subst.
              clear H1.
              apply starts_with_eq in H; subst.
              inversion H2. {
                subst.
                apply linked_inv in H5.
                inversion H5; subst; clear H5.
                clear H4.
                
          }
    }
    
*)

(*
  Let cg_future_preserves_not_hb:
    forall cg n1 n2 x y,
    ~ HB cg n1 n2 ->
    ~ HB (cg_future x y cg) n1 n2.
  Proof.
    intros.
    apply heq_neq_iff.
  Qed.
*)   

  Definition MHP cg n1 n2 := ~ HB cg n1 n2 /\ ~ HB cg n2 n1.
(*
  Let mhb_preserves_future:
    forall cg n1 n2 x y,
    MHP cg n1 n2 ->
    MHP (cg_future x y cg) n1 n2.
  Proof.
    intros.
    unfold cg_future.
    destruct (MT_Extra.find_rw x (cg_tasks cg)) as [(rw,?)|(e,(rw,?))];
    rewrite rw; auto; clear rw.
    unfold MHP.
    split.
    - unfold not; intros.
      destruct H.
  Qed.

  Lemma mhb_preservation:
    forall cg n1 n2 o cg',
    MHP cg n1 n2 ->
    Reduces cg o cg' ->
    MHP cg' n1 n2.
  Proof.
    intros.
    destruct H0.
    - 
  Qed.
*)
End Defs.
End CG.

Module Shadow.
  Structure access := {
    write_access: list CG.node;
    read_access: list CG.node
  }.

  Definition a_add_write n a := Build_access (n :: write_access a) (read_access a).

  Definition a_add_read n a := Build_access (write_access a) (n :: read_access a).

  Definition shadow := MM.t access.

  Definition sh_update (h:mid) (f: access->access) (sh:shadow) : shadow :=
  match MM.find h sh with
  | Some a => MM.add h (f a) sh
  | _ => sh
  end.

  Definition sh_read cg t h sh : shadow :=
  match CG.cg_lookup t cg with
  | Some n => sh_update h (a_add_read n) sh
  | _ => sh
  end.

  Definition sh_write cg t h sh : shadow :=
  match CG.cg_lookup t cg with
  | Some n => sh_update h (a_add_write n) sh
  | _ => sh
  end.

  Inductive Reduces cg: shadow -> Lang.effect -> shadow -> Prop :=
  | reduces_read:
    forall sh t h,
    Reduces cg sh (t,Lang.READ h) (sh_read cg t h sh)
  | sh_reduces_write:
    forall sh t h,
    Reduces cg sh (t,Lang.WRITE h) (sh_write cg t h sh)
  | reduces_skip:
    forall sh t o,
    Lang.is_m_op o = true ->
    Reduces cg sh (t,o) sh.

  Section Opts.
  Variable sh:shadow.

  Inductive Reads (n:CG.node) (h:mid) : Prop :=
  | reads_def:
    forall a,
    MM.MapsTo h a sh ->
    List.In n (read_access a) ->
    Reads n h.

  Inductive Writes (n:CG.node) (h:mid) : Prop :=
  | writes_def:
    forall a,
    MM.MapsTo h a sh ->
    List.In n (write_access a) ->
    Writes n h.

  Inductive Node n h : Prop :=
  | node_read:
    Reads n h ->
    Node n h
  | node_write:
    Writes n h ->
    Node n h.

  Inductive CoAccess (n1 n2:CG.node) (h:mid): Prop :=
  | co_access_def:
    Writes n1 h ->
    Node n2 h ->
    CoAccess n1 n2 h.

  Variable cg: CG.computation_graph.

  Inductive HasRace h : Prop :=
  | has_race_def:
    forall n1 n2,
    CoAccess n1 n2 h ->
    CG.MHP cg n1 n2 ->
    HasRace h.

  Inductive OrderedAccesses (lhs:list CG.node) (rhs:list CG.node): Prop :=
  | safe_reads_def:
    (forall x y, List.In x lhs -> List.In y rhs -> CG.Ordered cg x y) ->
    OrderedAccesses lhs rhs.

  Inductive RaceFree h : Prop :=
  | race_free_def:
      forall a,
      MM.MapsTo h a sh ->
      OrderedAccesses (read_access a) (write_access a) ->
      OrderedAccesses (write_access a) (write_access a) ->
      RaceFree h.

  Inductive Racy : Prop :=
    racy_def:
      forall h,
      HasRace h ->
      Racy.

  End Opts.

  Section Props.

  Let reads_to_in_read_access:
    forall sh n h a,
    Reads sh n h ->
    MM.MapsTo h a sh ->
    List.In n (read_access a).
  Proof.
    intros.
    inversion H; subst; clear H.
    assert (a0 = a) by eauto using MM_Facts.MapsTo_fun.
    subst; auto.
  Qed.

  Let writes_to_in_write_access:
    forall sh n h a,
    Writes sh n h ->
    MM.MapsTo h a sh ->
    List.In n (write_access a).
  Proof.
    intros.
    inversion H; subst; clear H.
    assert (a0 = a) by eauto using MM_Facts.MapsTo_fun.
    subst; auto.
  Qed.

  Let in_read_access_add_read:
    forall n a n',
    List.In n (read_access a) ->
    List.In n (read_access (a_add_read n' a)).
  Proof.
    intros.
    destruct a; simpl in *.
    auto.
  Qed.

  Let in_read_access_add_write:
    forall n a n',
    List.In n (read_access a) ->
    List.In n (read_access (a_add_write n' a)).
  Proof.
    intros.
    destruct a; simpl in *.
    auto.
  Qed.

  Let in_write_access_add_read:
    forall n a n',
    List.In n (write_access a) ->
    List.In n (write_access (a_add_read n' a)).
  Proof.
    intros.
    destruct a; simpl in *.
    auto.
  Qed.

  Let in_write_access_add_write:
    forall n a n',
    List.In n (write_access a) ->
    List.In n (write_access (a_add_write n' a)).
  Proof.
    intros.
    destruct a; simpl in *.
    auto.
  Qed.

  Let reads_preservation_read:
    forall cg t sh n h h',
    Reads sh n h ->
    Reads (sh_read cg t h' sh) n h.
  Proof.
    intros.
    unfold sh_read.
    unfold CG.cg_lookup.
    destruct (MT_Extra.find_rw t (CG.cg_tasks cg)) as [(rw,?)|(e,(rw,?))].
    - rewrite rw.
      auto.
    - rewrite rw; clear rw.
      unfold sh_update.
      destruct (MM_Extra.find_rw h' sh) as [(rw,?)|(a,(rw,?))]; rewrite rw; clear rw.
      + assumption.
      + destruct (MID.eq_dec h' h).
        * rewrite mid_eq_rw in *; subst.
          eauto using reads_def, MM.add_1.
        * rewrite mid_eq_rw in *; subst.
          inversion H.
          eauto using reads_def, MM.add_2.
  Qed.

  Let reads_preservation_write:
    forall cg t sh n h h',
    Reads sh n h ->
    Reads (sh_write cg t h' sh) n h.
  Proof.
    intros.
    unfold sh_write.
    unfold CG.cg_lookup.
    destruct (MT_Extra.find_rw t (CG.cg_tasks cg)) as [(rw,?)|(e,(rw,?))].
    - rewrite rw.
      auto.
    - rewrite rw; clear rw.
      unfold sh_update.
      destruct (MM_Extra.find_rw h' sh) as [(rw,?)|(a,(rw,?))]; rewrite rw; clear rw.
      + assumption.
      + destruct (MID.eq_dec h' h).
        * rewrite mid_eq_rw in *; subst.
          eauto using reads_def, MM.add_1.
        * rewrite mid_eq_rw in *; subst.
          inversion H.
          eauto using reads_def, MM.add_2.
  Qed.

  Let writes_preservation_read:
    forall cg t sh n h h',
    Writes sh n h ->
    Writes (sh_read cg t h' sh) n h.
  Proof.
    intros.
    unfold sh_read.
    unfold CG.cg_lookup.
    destruct (MT_Extra.find_rw t (CG.cg_tasks cg)) as [(rw,?)|(e,(rw,?))].
    - rewrite rw.
      auto.
    - rewrite rw; clear rw.
      unfold sh_update.
      destruct (MM_Extra.find_rw h' sh) as [(rw,?)|(a,(rw,?))]; rewrite rw; clear rw.
      + assumption.
      + destruct (MID.eq_dec h' h).
        * rewrite mid_eq_rw in *; subst.
          eauto using writes_def, MM.add_1.
        * rewrite mid_eq_rw in *; subst.
          inversion H.
          eauto using writes_def, MM.add_2.
  Qed.

  Let writes_preservation_write:
    forall cg t sh n h h',
    Writes sh n h ->
    Writes (sh_write cg t h' sh) n h.
  Proof.
    intros.
    unfold sh_write.
    unfold CG.cg_lookup.
    destruct (MT_Extra.find_rw t (CG.cg_tasks cg)) as [(rw,?)|(e,(rw,?))].
    - rewrite rw.
      auto.
    - rewrite rw; clear rw.
      unfold sh_update.
      destruct (MM_Extra.find_rw h' sh) as [(rw,?)|(a,(rw,?))]; rewrite rw; clear rw.
      + assumption.
      + destruct (MID.eq_dec h' h).
        * rewrite mid_eq_rw in *; subst.
          eauto using writes_def, MM.add_1.
        * rewrite mid_eq_rw in *; subst.
          inversion H.
          eauto using writes_def, MM.add_2.
  Qed.

  Let co_access_preservation_read:
    forall cg t sh n1 n2 h h',
    CoAccess sh n1 n2 h ->
    CoAccess (sh_read cg t h' sh) n1 n2 h.
  Proof.
    intros.
    destruct H.
    inversion H0; eauto using co_access_def, node_read, node_write.
  Qed.

  Let co_access_preservation_write:
    forall cg t sh n1 n2 h h',
    CoAccess sh n1 n2 h ->
    CoAccess (sh_write cg t h' sh) n1 n2 h.
  Proof.
    intros.
    destruct H.
    inversion H0; eauto using co_access_def, node_read, node_write.
  Qed.

  Lemma co_access_preservation:
    forall sh o sh' n1 n2 h cg,
    CoAccess sh n1 n2 h ->
    Reduces cg sh o sh' ->
    CoAccess sh' n1 n2 h.
  Proof.
    intros.
    inversion H0; subst; clear H0; eauto.
  Qed.

  End Props.
End Shadow.

Module Races.

  Definition race_state := (Lang.state * CG.computation_graph * Shadow.shadow) % type.

  Definition r_shadow (s:race_state) : Shadow.shadow :=
  match s with
  | (_, _, sh) => sh
  end.

  Definition r_dag (s:race_state) : CG.computation_graph :=
  match s with
  | (_, cg, _) => cg
  end.

  Inductive Reduces: race_state -> race_state -> Prop :=
  | reduces_def:
    forall s s' cg sh o cg' sh',
    Lang.Reduces s o s' ->
    CG.Reduces cg o cg' ->
    Shadow.Reduces cg sh o sh' ->
    Reduces (s, cg, sh) (s', cg', sh').

End Races.

Module Vector.
  Section Defs.
  Variable A:Type.

  Inductive IndexOf (x:A) : nat -> list A -> Prop :=
  | index_of_eq:
    forall l,
    IndexOf x (length l) (x :: l)
  | index_of_cons:
    forall y n l,
    IndexOf x n l ->
    IndexOf x n (y :: l).

  Lemma index_of_to_in:
    forall x n l,
    IndexOf x n l ->
    In x l.
  Proof.
    intros.
    induction l. {
      inversion H.
    }
    inversion H; subst.
    - auto using in_eq.
    - auto using in_cons.
  Qed.

  Lemma index_of_fun:
    forall l x n n',
    NoDup l ->
    IndexOf x n l ->
    IndexOf x n' l ->
    n' = n.
  Proof.
    intros.
    induction l. {
      inversion H0.
    }
    inversion H; subst; clear H.
    inversion H0; subst; clear H0.
    - inversion H1; subst; clear H1.
      + trivial.
      + contradiction H4; eauto using index_of_to_in.
    - inversion H1; subst; clear H1.
      + contradiction H4; eauto using index_of_to_in.
      + eauto.
  Qed.

  Lemma index_of_length_lt:
    forall x n l,
    IndexOf x n l ->
    n < length l.
  Proof.
    intros.
    induction l. {
      inversion H.
    }
    inversion H; subst.
    - auto.
    - simpl.
      assert (n < length l) by eauto.
      eauto.
  Qed.

  Lemma index_of_bij:
    forall l x x' n,
    NoDup l ->
    IndexOf x n l ->
    IndexOf x' n l ->
    x' = x.
  Proof.
    intros.
    induction l. {
      inversion H0.
    }
    inversion H; clear H; subst.
    inversion H0; subst; clear H0.
    - inversion H1; subst; clear H1.
      + trivial.
      + assert (length l < length l). {
          eauto using index_of_length_lt.
        }
        omega.
    - inversion H1; subst; clear H1.
      + assert (length l < length l). {
          eauto using index_of_length_lt.
        }
        omega.
      + eauto.
  Qed.

  Lemma index_of_neq:
    forall l x y n n',
    NoDup l ->
    IndexOf x n l ->
    IndexOf y n' l ->
    n <> n' ->
    x <> y.
  Proof.
    intros.
    induction l. {
      inversion H0.
    }
    inversion H; clear H; subst.
    inversion H0; subst; clear H0.
    - inversion H1; subst; clear H1.
      + omega.
      + unfold not; intros; subst.
        contradiction H5.
        eauto using index_of_to_in.
    - inversion H1; subst; clear H1.
      + unfold not; intros; subst.
        contradiction H5.
        eauto using index_of_to_in.
      + eauto.
  Qed.

  Inductive Lt (l:list A) (x:A) (y:A) : Prop :=
  | lt_def:
    forall xn yn,
    IndexOf x xn l ->
    IndexOf y yn l ->
    xn < yn ->
    Lt l x y.

  Lemma lt_trans (l:list A) (N:NoDup l):
    forall x y z,
    Lt l x y ->
    Lt l y z ->
    Lt l x z.
  Proof.
    intros.
    inversion H; clear H.
    inversion H0; clear H0.
    rename yn0 into zn.
    assert (xn0 = yn) by
    eauto using index_of_fun; subst.
    apply lt_def with (xn:=xn) (yn:=zn); auto.
    omega.
  Qed.

  Lemma lt_neq (l:list A) (N:NoDup l):
    forall x y,
    Lt l x y ->
    x <> y.
  Proof.
    intros.
    inversion H; clear H.
    assert (xn <> yn) by omega.
    eauto using index_of_neq.
  Qed.

  End Defs.
End Vector.


