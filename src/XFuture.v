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

Module Walk2Lt.
  Section Defs.
  Variable A:Type.

  Variable Lt: A -> A -> Prop.

  Variable lt_trans:
    forall (x y z: A),
    Lt x y ->
    Lt y z ->
    Lt x z.

  Notation Edge := (fun e => let (x,y) := e in Lt x y).

  Require Import Aniceto.Graphs.Graph.

  Lemma walk_to_lt:
    forall w x y,
    Walk2 Edge x y w ->
    Lt x y.
  Proof.
    induction w; intros. {
      apply walk2_nil_inv in H.
      inversion H.
    }
    destruct a as (x',z).
    destruct w. {
      apply walk2_inv_pair in H.
      destruct H.
      inversion H; subst; clear H.
      assumption.
    }
    apply walk2_inv in H.
    destruct H as (z', (He, (Hi, Hw))).
    inversion He; subst; clear He; rename z' into z.
    assert (Lt z y) by eauto.
    eauto.
  Qed.
  End Defs.
End Walk2Lt.

Module DAG.
  Section Defs.
  Variable A:Type.

  Variable Lt: A -> A -> Prop.

  Inductive DAG : list (A*A) -> Prop :=
  | dag_nil:
    DAG nil
  | dag_cons:
    forall x y es,
    DAG es ->
    Lt x y ->
    DAG ((x,y)::es).

  Lemma dag_in_to_lt:
    forall es,
    DAG es ->
    forall x y,
    List.In (x, y) es ->
    Lt x y.
  Proof.
    induction es; intros. {
      inversion H0.
    }
    inversion H; subst; clear H.
    destruct H0. {
      inversion H; subst; auto.
    }
    eauto.
  Qed.

  Lemma make_dag:
    forall es,
    (forall x y, List.In (x,y) es -> Lt x y) ->
    DAG es.
  Proof.
    intros.
    induction es. {
      auto using dag_nil.
    }
    destruct a as (x,y).
    apply dag_cons.
    - eauto using dag_in_to_lt, in_cons.
    - auto using in_eq.
  Qed.

  Notation Edge := (fun g e => @List.In (A*A) e g) %type.

  Require Import Aniceto.Graphs.Graph.

  Variable lt_trans:
    forall (x y z: A),
    Lt x y ->
    Lt y z ->
    Lt x z.

  Lemma dag_walk_to_lt:
    forall es,
    DAG es ->
    forall w x y,
    Walk2 (Edge es) x y w ->
    Lt x y.
  Proof.
    intros.
    apply Walk2Lt.walk_to_lt with (w:=w); eauto.
    apply walk2_impl with (E:=Edge es); auto.
    intros.
    destruct e as (a,b); simpl.
    eauto using dag_in_to_lt.
  Qed.
End Defs.
End DAG.

Module CG.
  Definition node := (tid*nat) % type.

  Definition edge := (node * node) % type.

  Definition edges := list edge.

  Structure computation_graph := cg_make {
    cg_size : nat;
    cg_tasks: MT.t nat;
    cg_edges: list (node * node);
    cg_tasks_spec:
      forall x n,
      MT.MapsTo x n cg_tasks ->
      n < cg_size;
    cg_edges_spec:
      forall x y,
      List.In (x,y) cg_edges -> (snd x) < (snd y)
  }.

  Definition cg_lookup (t:tid) cg : option node :=
  match MT.find t (cg_tasks cg) with
  | Some n => Some (t,n)
  | _ => None
  end.

  Program Definition cg_future (x y:tid) (cg : computation_graph) : computation_graph :=
  let nx' := cg_size cg in
  let ny := S nx' in
  let total := S ny in
  match MT.find x (cg_tasks cg) with
  | Some nx =>
    @cg_make total ((MT.add x nx') ((MT.add y ny) (cg_tasks cg))) (((x,nx),(x,nx'))::((x,nx),(y,ny))::(cg_edges cg)) _ _
  | _ => cg
  end.
  Next Obligation.
    symmetry in Heq_anonymous.
    apply MT_Facts.find_mapsto_iff in Heq_anonymous.
    apply cg_tasks_spec in Heq_anonymous.
    apply MT_Facts.add_mapsto_iff in H.
    destruct H as [(?,?)|(?,?)]. {
      subst.
      auto.
    }
    apply MT_Facts.add_mapsto_iff in H0.
    destruct H0 as [(?,?)|(?,?)]. {
      subst.
      auto.
    }
    apply cg_tasks_spec in H1.
    auto.
  Qed.
  Next Obligation.
    symmetry in Heq_anonymous.
    apply MT_Facts.find_mapsto_iff in Heq_anonymous.
    apply cg_tasks_spec in Heq_anonymous.
    destruct H as [?|[?|?]];
    try (inversion H; simpl in *; subst; clear H); eauto.
    simpl in *.
    apply cg_edges_spec in H; auto.
  Qed.

  Program Definition cg_force (x y:tid) (cg : computation_graph) : computation_graph :=
  let nx' := cg_size cg in
  let total := S nx' in
  match MT.find x (cg_tasks cg) with
  | Some nx =>
    match MT.find y (cg_tasks cg) with
    | Some ny =>
      @cg_make total ((MT.add x nx') (cg_tasks cg)) (((x,nx),(x,nx'))::((y,ny), (x,nx'))::(cg_edges cg)) _ _
    | _ => cg
    end
  | _ => cg
  end.
  Next Obligation.
    symmetry in Heq_anonymous.
    apply MT_Facts.find_mapsto_iff in Heq_anonymous.
    apply cg_tasks_spec in Heq_anonymous.
    symmetry in Heq_anonymous0.
    apply MT_Facts.find_mapsto_iff in Heq_anonymous0.
    apply cg_tasks_spec in Heq_anonymous0.
    apply MT_Facts.add_mapsto_iff in H.
    destruct H as [(?,?)|(?,?)]. {
      subst.
      auto.
    }
    apply cg_tasks_spec in H0.
    auto.
  Qed.
  Next Obligation.
    symmetry in Heq_anonymous.
    apply MT_Facts.find_mapsto_iff in Heq_anonymous.
    apply cg_tasks_spec in Heq_anonymous.
    symmetry in Heq_anonymous0.
    apply MT_Facts.find_mapsto_iff in Heq_anonymous0.
    apply cg_tasks_spec in Heq_anonymous0.
    destruct H as [?|[?|?]];
    try (inversion H; subst; clear H); eauto.
    apply cg_edges_spec in H; auto.
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

  Require Import Coq.Relations.Relation_Operators.

  Definition HB cg := clos_trans CG.node (Prec cg).

  Lemma hb_trans:
    forall cg n1 n2 n3,
    HB cg n1 n2 ->
    HB cg n2 n3 ->
    HB cg n1 n3.
  Proof.
    intros.
    unfold HB in *; eauto using t_trans.
  Qed.

  Require Aniceto.Graphs.Graph.

  Let Lt (n1 n2:node) := (snd n1) < (snd n2).

  Let cg_is_dag:
    forall cg,
    DAG.DAG Lt (cg_edges cg).
  Proof.
    intros.
    apply DAG.make_dag.
    intros.
    apply cg_edges_spec in H.
    auto.
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

  Lemma hb_irrefl:
    forall cg n,
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
    - auto using cg_is_dag.
  Qed.

  Lemma hb_asymm:
    forall cg n1 n2,
    HB cg n1 n2 ->
    ~ HB cg n2 n1.
  Proof.
    intros.
    unfold not; intros.
    assert (HB cg n1 n1) by eauto using hb_trans.
    apply hb_irrefl in H1.
    assumption.
  Qed.

  Definition MHP cg n1 n2 := ~ HB cg n1 n2 /\ ~ HB cg n2 n1.

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

  Inductive CoAccess (n1 n2:CG.node) (h:mid): Prop :=
  | co_access_rw:
    Reads n1 h ->
    Writes n2 h ->
    CoAccess n1 n2 h
  | co_access_ww:
    Writes n1 h ->
    Writes n2 h ->
    CoAccess n1 n2 h.

  End Opts.

  Section Props.

  Let reads_to_in_read_access:
    forall sh n h a,
    Reads sh n h ->
    MM.MapsTo h a sh ->
    In n (read_access a).
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
    In n (write_access a).
  Proof.
    intros.
    inversion H; subst; clear H.
    assert (a0 = a) by eauto using MM_Facts.MapsTo_fun.
    subst; auto.
  Qed.

  Let in_read_access_add_read:
    forall n a n',
    In n (read_access a) ->
    In n (read_access (a_add_read n' a)).
  Proof.
    intros.
    destruct a; simpl in *.
    auto.
  Qed.

  Let in_read_access_add_write:
    forall n a n',
    In n (read_access a) ->
    In n (read_access (a_add_write n' a)).
  Proof.
    intros.
    destruct a; simpl in *.
    auto.
  Qed.

  Let in_write_access_add_read:
    forall n a n',
    In n (write_access a) ->
    In n (write_access (a_add_read n' a)).
  Proof.
    intros.
    destruct a; simpl in *.
    auto.
  Qed.

  Let in_write_access_add_write:
    forall n a n',
    In n (write_access a) ->
    In n (write_access (a_add_write n' a)).
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
    destruct H; eauto using co_access_rw, co_access_ww.
  Qed.

  Let co_access_preservation_write:
    forall cg t sh n1 n2 h h',
    CoAccess sh n1 n2 h ->
    CoAccess (sh_write cg t h' sh) n1 n2 h.
  Proof.
    intros.
    destruct H; eauto using co_access_rw, co_access_ww.
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

  Inductive HasRace h s : Prop :=
  | has_race_def:
    forall n1 n2,
    Shadow.CoAccess (r_shadow s) n1 n2 h ->
    CG.MHP (r_dag s) n1 n2 ->
    HasRace h s.

  Inductive Race s : Prop :=
    race_def:
      (forall h, MM.In h (r_shadow s) -> HasRace h s) ->
      Race s.
    


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


