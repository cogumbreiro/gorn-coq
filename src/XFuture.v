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

  Inductive effect := 
  | READ: tid -> mid -> effect
  | WRITE: tid -> mid -> effect
  | FUTURE: tid -> tid -> effect
  | FORCE: tid -> tid -> effect
  | TAU: effect.

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

  Inductive MReduces : (state * tid * expression) -> effect -> (state * word) -> Prop :=
  | m_reduces_malloc:
    forall h t s,
    ~ MM.In h (s_heap s) ->
    MReduces (s, t, Malloc) TAU (s_global_put h None s, HeapLabel h)
  | m_reduces_load:
    forall s t v w h,
    VReduces s t v (HeapLabel h) ->
    MM.MapsTo h (Some w) (s_heap s) ->
    MReduces (s, t, Deref v) (READ t h) (s, w).

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

  Inductive FReduces: (state*tid*expression) -> effect -> (state*word) -> Prop :=
  | f_reduces_future:
    forall xs vs t s p t' (l':store),
    Bind s t xs vs l' ->
    ~ MT.In t' (s_tasks s) ->
    FReduces (s,t,Future vs xs p) (FUTURE t t')
      ((s_spawn t' l' p) s,
        TaskLabel t')
  | f_reduces_force:
    forall v t' w t s,
    VReduces s t v (TaskLabel t') ->
    Stopped s t' w ->
    FReduces (s,t,Force v) (FORCE t t') (s, w).

  Inductive EReduces: (state*tid*expression) -> effect -> (state*word) -> Prop :=
  | e_reduces_f:
    forall s s' t e w o,
    FReduces (s, t, e) o (s', w) ->
    EReduces (s, t, e) o (s', w)
  | e_reduces_m:
    forall s s' t e w o,
    MReduces (s, t, e) o (s', w) ->
    EReduces (s, t, e) o (s', w).

  Inductive IReduces: (state * tid * instruction) -> effect -> state -> Prop :=
  | i_reduces_assign:
    forall s t w x,
    IReduces (s,t,Assign x (Value (Word w))) TAU (s_local_put t x w s)
  | i_reduces_store:
    forall s s' t w h v,
    VReduces s t v (HeapLabel h) ->
    IReduces (s,t,Store v (Value (Word w))) (WRITE t h)
      (s_global_put h (Some w) s').

  Inductive PReduces: (state * tid * program) -> effect -> (state * program) -> Prop :=
  | p_reduces_eval:
    forall s s' i t e w p o,
    Expression i e ->
    EReduces (s,t,e) o (s',w) ->
    PReduces (s,t, Seq i p) o (s', Seq (eval w i) p)
  | p_reduces_seq:
    forall s t i p s' o,
    IReduces (s,t,i) o s' ->
    PReduces (s,t, Seq i p) o (s', p)
  | i_reduces_if_zero:
    forall s t v p1 p2,
    VReduces s t v (Num 0) ->
    PReduces (s,t,If v p1 p2) TAU (s, p2)
  | i_reduces_if_succ:
    forall s t v n p1 p2,
    VReduces s t v (Num (S n)) ->
    PReduces (s,t,If v p1 p2) TAU (s, p1).

  Inductive Reduces: state -> effect -> state -> Prop :=
  | reduces_run:
    forall s s' t p p' o,
    Program s t p ->
    PReduces (s,t,p) o (s', p') ->
    Reduces s o (s_set_program t p' s').
End Lang.

Module Races.
  Definition node := (tid*nat) % type.

  Definition edge := (node * node) % type.

  Definition edges := list edge.

  Definition time := MT.t nat.

  Definition ts_tick t ts :=
  match MT.find t ts with
  | Some n => MT.add t (S n) ts
  | _ => ts
  end.

  Definition ts_spawn t ts :=
  MT.add t 0 ts.

  Definition ts_node t ts : option node :=
  match MT.find t ts with
  | Some n => Some (t, n)
  | None => None
  end.

  Definition ts_new_node (t:tid) : node := (t, 0).

  Definition computation_graph := (time * edges) % type.

  Definition cg_time (cg:computation_graph) : time :=
  match cg with
  | (ts, _) => ts
  end.

  Definition cg_edges (cg:computation_graph) : edges :=
  match cg with
  | (_,es) => es
  end.

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

  Definition sh_add_read h n sh : shadow :=
  sh_update h (a_add_read n) sh.

  Definition sh_add_write h n sh : shadow :=
  sh_update h (a_add_write n) sh.

  Definition race_state := (Lang.state * computation_graph * shadow) % type.

  Definition r_shadow (s:race_state) : shadow :=
  match s with
  | (_, _, sh) => sh
  end.

  Definition r_edges (s:race_state) : edges :=
  match s with
  | (_, cg, _) => cg_edges cg
  end.

  Definition cg_eval o (cg:computation_graph) :=
  let (ts, es) := cg in
  match o with
  | Lang.FUTURE x y =>
    match ts_node x ts with
    | Some n => ((ts_spawn y) (ts_tick x ts), (n,ts_new_node y)::es)
    | _ => cg
    end
  | Lang.FORCE x y =>
    match ts_node x ts with
    | Some nx =>
      match ts_node y ts with
      | Some ny =>
        (ts_tick x ts, (nx,ny)::es)
      | _ => cg
      end
    | _ => cg
    end
  | _ => cg
  end.

  Definition sh_eval o (cg:computation_graph) (sh:shadow) :=
  let ts := cg_time cg in
  match o with
  | Lang.READ t h =>
    match ts_node t ts with
    | Some n => sh_add_write h n sh
    | _ => sh
    end
  | Lang.WRITE t h =>
    match ts_node t ts with
    | Some n => sh_add_read h n sh
    | _ => sh
    end
  | _ => sh
  end.

  Inductive Reduces: race_state -> race_state -> Prop :=
  | reduces_def:
    forall s s' cg sh o,
    Lang.Reduces s o s' ->
    Reduces (s, cg, sh) (s', cg_eval o cg, sh_eval o cg sh). 


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
