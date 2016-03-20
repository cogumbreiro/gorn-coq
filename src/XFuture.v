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

Module Races.
  Definition node := (tid*nat) % type.

  Definition make_node (t:tid) : node := (t, 0).

  Definition node_succ (n:node) : node :=
  let (x,y) := n in (x, S y).

  Definition time := MT.t node.

  Definition ts_tick t ts :=
  match MT.find t ts with
  | Some n => MT.add t (node_succ n) ts
  | _ => ts
  end.

  Definition ts_spawn t ts :=
  MT.add t (make_node t) ts.

  Definition ts_lookup (t:tid) (ts:time) : option node :=
  MT.find t ts.

  Definition ts_future x y ts : time := (ts_spawn y) (ts_tick x ts).

  Definition ts_force (x y:tid) ts : time := (ts_tick x ts).

  Definition ts_eval (x:tid) o : time -> time :=
  match o with
  | Lang.FUTURE y => ts_future x y
  | Lang.FORCE y => ts_force x y
  | _ => id
  end.

  Definition edge := (node * node) % type.

  Definition edges := list edge.

  Definition es_add tsx x tsy y es : edges :=
  match ts_lookup x tsx with
  | Some nx =>
    match ts_lookup y tsy with
      | Some ny => (nx, ny) :: es
      | _ => es
    end
  | _ => es
  end.

  Definition es_eval (ts:time) (x:tid) (y:tid) (ts':time) (es:edges) : edges :=
  (es_add ts x ts' y) (es_add ts x ts' x es).

  Definition computation_graph := (time * edges) % type.

  Definition cg_edges (cg:computation_graph) : edges :=
  match cg with
  | (_, es) => es
  end.

  Definition cg_lookup (t:tid) (cg:computation_graph) : option node :=
  match cg with
  | (ts, _) => ts_lookup t ts
  end.

  Inductive CGReduces: computation_graph -> Lang.effect -> computation_graph -> Prop :=
  | cg_reduces_future:
    forall x y ts es,
    MT.In x ts ->
    ~ MT.In y ts ->
    let ts' := ts_future x y ts in
    CGReduces (ts,es) (x,Lang.FUTURE y) (ts', (es_eval ts x y ts') es)
  | cg_reduces_force:
    forall x y (ts:time) ts es,
    MT.In x ts ->
    MT.In y ts ->
    let ts' := ts_force x y ts in
    CGReduces (ts,es) (x,Lang.FORCE y) (ts', (es_eval ts x y ts') es)
  | cg_reduces_skip:
    forall cg t o,
    Lang.is_f_op o = false ->
    CGReduces cg (t,o) cg.

  Structure access := {
    write_access: list node;
    read_access: list node
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
  match cg_lookup t cg with
  | Some n => sh_update h (a_add_read n) sh
  | _ => sh
  end.

  Definition sh_write cg t h sh : shadow :=
  match cg_lookup t cg with
  | Some n => sh_update h (a_add_write n) sh
  | _ => sh
  end.

  Definition sh_eval (cg:computation_graph) t o (sh:shadow) :=
  match o with
  | Lang.READ h => sh_write cg t h
  | Lang.WRITE h => sh_read cg t h
  | _ => id
  end.

  Definition race_state := (Lang.state * computation_graph * shadow) % type.

  Definition r_shadow (s:race_state) : shadow :=
  match s with
  | (_, _, sh) => sh
  end.

  Definition r_edges (s:race_state) : edges :=
  match s with
  | (_, cg, _) => cg_edges cg
  end.


  Inductive SHReduces cg: shadow -> Lang.effect -> shadow -> Prop :=
  | sh_reduces_read:
    forall sh t h,
    SHReduces cg sh (t,Lang.READ h) (sh_read cg t h sh)
  | sh_reduces_write:
    forall sh t h,
    SHReduces cg sh (t,Lang.WRITE h) (sh_write cg t h sh)
  | sh_reduces_skip:
    forall sh t o,
    Lang.is_m_op o = true ->
    SHReduces cg sh (t,o) sh.

  Inductive Reduces: race_state -> race_state -> Prop :=
  | reduces_def:
    forall s s' cg sh o cg' sh',
    Lang.Reduces s o s' ->
    CGReduces cg o cg' ->
    SHReduces cg sh o sh' ->
    Reduces (s, cg, sh) (s', cg', sh').

  Require Import Coq.Relations.Relation_Operators.

  Inductive Prec (s:race_state) n1 n2 : Prop :=
  | prec_def:
    List.In (n1,n2) (r_edges s) ->
    Prec s n1 n2.

  Definition HB s := clos_trans node (Prec s).

  Definition MHP s n1 n2 := ~ HB s n1 n2 /\ ~ HB s n2 n1.

  Inductive Conflict (s:race_state) (a:access): Prop :=
  | conflict_rw:
    forall n1 n2,
    List.In n1 (read_access a) ->
    List.In n2 (write_access a) -> 
    MHP s n1 n2 ->
    Conflict s a
  | conflict_ww:
    forall n1 n2,
    List.In n1 (write_access a) ->
    List.In n2 (write_access a) -> 
    MHP s n1 n2 ->
    Conflict s a.

  Inductive HasRace h s : Prop :=
  | has_race_def:
    forall a,
    MM.MapsTo h a (r_shadow s) ->
    Conflict s a ->
    HasRace h s.

  Inductive Race s : Prop :=
    race_def:
      (forall h, MM.In h (r_shadow s) -> HasRace h s) ->
      Race s.

  Axiom race_preserves:
    forall s s',
    Race s ->
    Reduces s s' ->
    Race s'.

End Races.
Set Implict Arguments.

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
  | dag_cons_edge:
    forall x y es,
    DAG es ->
    Lt x y ->
    ~ List.In (x,y) es ->
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


Module CG.
  Structure computation_graph := cg_make {
    cg_size : nat;
    cg_tasks: MT.t nat;
    cg_edges: list (nat * nat);
    cg_tasks_spec:
      forall x n,
      MT.MapsTo x n cg_tasks ->
      n < cg_size;
    cg_edges_spec:
      forall x y,
      List.In (x,y) cg_edges -> x < y
  }.

  Program Definition cg_future (x y:tid) (cg : computation_graph) : computation_graph :=
  let nx' := cg_size cg in
  let ny := S nx' in
  let total := S ny in
  match MT.find x (cg_tasks cg) with
  | Some nx =>
    @cg_make total ((MT.add x nx') ((MT.add y ny) (cg_tasks cg))) ((nx,nx')::(nx,ny)::(cg_edges cg)) _ _
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
    try (inversion H; subst; clear H); eauto.
    apply cg_edges_spec in H; auto.
  Qed.

  Program Definition cg_force (x y:tid) (cg : computation_graph) : computation_graph :=
  let nx' := cg_size cg in
  let total := S nx' in
  match MT.find x (cg_tasks cg) with
  | Some nx =>
    match MT.find y (cg_tasks cg) with
    | Some ny =>
      @cg_make total ((MT.add x nx') (cg_tasks cg)) ((nx,nx')::(ny, nx')::(cg_edges cg)) _ _
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

End CG.

