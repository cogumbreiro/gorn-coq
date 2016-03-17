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

  Definition time := MT.t nat.

  Definition ts_tick t ts :=
  match MT.find t ts with
  | Some n => MT.add t (S n) ts
  | _ => ts
  end.

  Definition ts_spawn t ts :=
  MT.add t 0 ts.

  Definition ts_lookup (t:tid) (ts:time) : option node :=
  match MT.find t ts with
  | Some n => Some (t, n)
  | None => None
  end.

  Definition ts_future x y ts : time := (ts_spawn y) (ts_tick x ts).

  Definition ts_force (x y:tid) ts : time := (ts_tick x ts).

  Definition ts_eval (x:tid) o : time -> time :=
  match o with
  | Lang.FUTURE y => ts_future x y
  | Lang.FORCE y => ts_force x y
  | _ => id
  end.

  Definition ts_new_node (t:tid) : node := (t, 0).

  Definition edge := (node * node) % type.

  Definition edges := list edge.

  Definition es_future (ts:time) x y es : edges :=
  match ts_lookup x ts with
  | Some n => (n,ts_new_node y)::es
  | _ => es
  end.

  Definition es_force (ts:time) x y es : edges :=
  match ts_lookup x ts with
  | Some nx =>
    match ts_lookup y ts with
    | Some ny => (nx,ny)::es
    | _ => es
    end
  | _ => es
  end.

  Definition es_eval (ts:time) (x y:tid) o :=
  match o with
  | Lang.FUTURE y => es_future ts x y
  | Lang.FORCE y => es_force ts x y
  | _ => id
  end.

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
    CGReduces (ts,es) (x,Lang.FUTURE y) (ts_future x y ts, es_future ts x y es)
  | cg_reduces_force:
    forall x y (ts:time) ts es,
    MT.In x ts ->
    MT.In y ts ->
    CGReduces (ts,es) (x,Lang.FORCE y) (ts_force x y ts, es_force ts x y es)
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
Module X.
  Section X.
  Variable A:Type.
  Variable eq_dec: forall (x y:A), { x = y } + { x <> y }.


  Inductive Fin:  list A -> Type :=
  | F1:
    forall x l,
    Fin (x::l) 
  | FS:
    forall x l,
    Fin l ->
    Fin (x::l).

  Inductive Vector (E : Type) : list A -> Type :=
  | Vnil :
    Vector E nil
  | Vcons :
    E ->
    forall l x,
    Vector E l ->
    Vector E (x :: l).

  Fixpoint vector_impl (E F:Type) (f:E->F) (l:list A) (v:Vector E l) : Vector F l := 
  match v with 
  | Vnil => @Vnil F
  | Vcons e l' x v' => @Vcons F (f e) l' x (vector_impl f v')
  end.

End X.

Check (FS 1 (F1 2 nil)).

Check (F1 1 (2::nil)).

Section Y.
  Variable A:Type.

  Inductive DAG : list A -> list (A * A) -> Prop :=
  | dag_nil:
    DAG nil nil
  | dag_cons_edge:
    forall x y vs es,
    DAG (x::vs) es ->
    List.In y vs ->
    ~ List.In (x,y) es ->
    DAG (x::vs) ((x,y)::es)
  | dag_cons_vertex:
    forall x vs es,
    DAG vs es ->
    ~ List.In x vs ->
    DAG (x::vs) es.

  Lemma dag_no_dup:
    forall vs es,
    DAG vs es ->
    NoDup vs.
  Proof.
    intros.
    induction H.
    - auto using NoDup_nil.
    - assumption.
    - auto using NoDup_cons.
  Qed.

  Lemma dag_in_edge_right:
    forall vs es,
    DAG vs es ->
    forall x y,
    List.In (x, y) es ->
    List.In y vs.
  Proof.
    intros vs es H.
    induction H; intros.
    - inversion H.
    - inversion H2.
      + inversion H3; subst; clear H3.
        auto using in_cons.
      + eauto.
    - eauto using in_cons.
  Qed.

  Lemma dag_in_edge_left:
    forall vs es,
    DAG vs es ->
    forall x y,
    List.In (x, y) es ->
    List.In x vs.
  Proof.
    intros vs es H.
    induction H; intros.
    - inversion H.
    - inversion H2.
      + inversion H3; subst; clear H3.
        auto using in_eq.
      + eauto using in_cons.
    - eauto using in_cons.
  Qed.

  Lemma dag_inv_cons_nil:
    forall es x,
    DAG (x :: nil) es ->
    es = nil.
  Proof.
    intros es.
    induction es.
    - auto.
    - intros.
      inversion H.
      + subst.
        inversion H5.
      + subst.
        inversion H2.
  Qed.

  Lemma dag_snd_vertex_not_cons:
    forall es vs x e,
    DAG (x :: vs) es ->
    List.In e es ->
    snd e <> x.
  Proof.
    intros es.
    induction es; intros. {
      inversion H0.
    }
    inversion H0.
    - subst.
      inversion H.
      + subst.
        simpl.
        unfold not; intros.
        subst.
        assert (~ In x vs). {
          assert (n: NoDup (x::vs)) by eauto using dag_no_dup.
          inversion n; eauto.
        }
        contradiction.
      + subst.
        destruct e as (a,b).
        simpl in *.
        assert (In b vs) by eauto using dag_in_edge_right.
        unfold not; intros.
        subst.
        contradiction.
    - inversion H; subst.
      + simpl in *.
        destruct H0.
        * inversion H0.
          subst.
          contradiction.
        * apply IHes with (e:=e) in H6; auto.
      + destruct e as (x1,y1).
        simpl in *.
        unfold not; intros; subst.
        contradiction H6.
        eauto using dag_in_edge_right.
  Qed.

  Lemma dag_snd_vertex_not_cons_alt:
    forall es vs x y z,
    DAG (x :: vs) es ->
    List.In (y, z) es ->
    z <> x.
  Proof.
    intros.
    assert (snd (y, z) <> x)
    by eauto using dag_snd_vertex_not_cons.
    auto.
  Qed.

  Lemma dag_inv_neq_cons_vertex:
    forall x y z vs es,
    DAG (x :: vs) ((y, z) :: es) ->
    x <> y ->
    DAG vs ((y, z) :: es).
  Proof.
    intros.
    inversion H; subst.
    - contradiction H0; trivial.
    - assumption.
  Qed.

  Lemma dag_inv_cons_edge:
    forall x y vs es,
    DAG (x :: vs) ((x, y) :: es) ->
    DAG (x :: vs) es.
  Proof.
    intros.
    inversion H; subst.
    - assumption.
    - contradiction H4.
      eauto using dag_in_edge_left, in_eq.
  Qed.

  Lemma dag_inv_not_in_vetex:
    forall x vs es,
    DAG (x :: vs) es ->
    ~ In x vs.
  Proof.
    intros.
    assert (n: NoDup (x::vs)) by eauto using dag_no_dup.
    inversion n.
    auto.
  Qed.

  Lemma dag_inv_neq_vertex:
    forall x y vs es,
    DAG (x :: vs) ((x, y) :: es) ->
    x <> y.
  Proof.
    intros.
    inversion H; subst.
    - assert (~ In x vs) by eauto using dag_inv_not_in_vetex.
      unfold not; intros; subst;
      contradiction.
    - contradiction H4.
      eauto using dag_in_edge_left, in_eq.
  Qed.

  Lemma dag_edge_neq_vertex:
    forall es vs,
    DAG vs es ->
    forall x y,
    In (x, y) es ->
    x <> y.
  Proof.
    intros es.
    induction es; intros. {
      inversion H0.
    }
    inversion H; subst.
    - inversion H0; eauto.
      inversion H1; subst; clear H1.
      assert (y <> x) by
      eauto using dag_snd_vertex_not_cons_alt.
      auto.
    - inversion H0.
      + subst.
        induction vs0. {
          inversion H1.
        }
        assert (Hin: In x (a :: vs0))
        by eauto using dag_in_edge_left.
        destruct Hin. {
          subst.
          eauto using dag_inv_neq_vertex.
        }
        assert (x <> a). {
          apply dag_inv_not_in_vetex in H1.
          unfold not; intros; subst.
          contradiction.
        }
        apply IHvs0; auto.
        * unfold not; intros.
          contradiction H2.
          auto using in_cons.
        * apply dag_inv_neq_cons_vertex with (x:=a); auto.
        * apply dag_inv_neq_cons_vertex in H1; auto.
          apply dag_cons_vertex; auto.
          unfold not; intros; subst.
          contradiction H2.
          auto using in_cons.
      + destruct a as (a, b).
        induction vs0. {
          apply dag_inv_cons_nil in H.
          inversion H.
        }
        assert (Hin: In a (a0::vs0)). {
          eauto using dag_in_edge_left, in_eq.
        }
        destruct Hin. {
          subst.
          apply dag_inv_cons_edge in H1.
          eauto.
        }
        assert (a <> a0). {
          unfold not; intros; subst.
          apply dag_inv_not_in_vetex in H1.
          contradiction.
        }
        apply IHvs0; auto.
        * eauto using dag_inv_neq_cons_vertex.
        * unfold not; intros.
          contradiction H2.
          auto using in_cons.
        * assert (x0 <> a). {
            unfold not; intros; subst.
            contradiction H2.
            auto using in_cons.
          }
          apply dag_inv_neq_cons_vertex in H1; auto.
          apply dag_cons_vertex; auto.
          unfold not; intros; subst.
          contradiction H2.
          auto using in_cons.
  Qed.
        

  Require Import Coq.Relations.Relation_Definitions.

  Variable vs:list A.
  Variable es:list (A*A).
  Variable g:DAG vs es.



  Definition prec x y := List.In (x,y) es.

  Lemma prec_irreflex:
    forall x y,
    prec x y ->
    x <> y.
  Proof.
    intros.
    unfold prec in *.
    eauto using dag_edge_neq_vertex.
  Qed.

  Require Import Coq.Relations.Relation_Operators.
  Definition reaches := clos_trans A prec.

  Lemma reaches_trans:
    forall x y z,
    reaches x y ->
    reaches y z ->
    reaches x z.
  Proof.
    intros.
    unfold reaches in *.
    eauto using t_trans.
  Qed.

  Lemma reaches_irreflex:
    forall x y,
    reaches x y ->
    x <> y.
  Proof.
    intros.
    unfold reaches in *.
    apply Operators_Properties.clos_trans_t1n in H.
    induction H.
    - eauto using dag_edge_neq_vertex.
    - unfold not; intros; subst. 
  Qed.

  Let dag

Section Y.
  Variable A:Type.

  Definition Node := @Fin A.

  Definition Ancestors (l:list A) := list (Node l).

  Fixpoint ancestors_cons x {l} (fins:list (Fin l)) : Ancestors (x::l) :=
  match fins with
  | nil => nil
  | (f::fins) => (FS x f) :: (ancestors_cons x fins)
  end.

  Definition DAG (l:list A) := Vector (Ancestors l) l.

  Definition dag_nil : DAG nil := @Vnil A (Ancestors nil).

  Definition dag_cons (l:list A) (G:DAG l) (x:A) (es:Ancestors (x::l)) : DAG (x::l) :=
    @Vcons A (Ancestors (x::l)) es l x (vector_impl (ancestors_cons x) G).
End Y.
Let x := Vnil (@Node nat nil) (@Node nat nil).
Let y := Vcons 

Check @node nat nil.
Check @node nat (1::2::nil) ((FS 1 (F1 2 nil)) :: (F1 1 (2::nil)) :: nil).

(*
  Inductive t (A : Type) : nat -> Type :=
    nil : t A 0 | cons : A -> forall n : nat, t A n -> t A (S n)
*)



  

    

End X.

