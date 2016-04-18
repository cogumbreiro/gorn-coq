Set Implicit Arguments.

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import HJ.Tid.
Require Import HJ.Mid.
Require Import HJ.Cid.
Require Import HJ.Var.
Require Import HJ.Dep.

Section Lang.

  Inductive type :=
  | t_ref: type -> type
  | t_task: type -> type
  | t_number: type.

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
  | Malloc: value -> expression
  | Future: cid -> list value -> expression
  | Force: value -> expression.

  Inductive instruction :=
  | Assign: var -> expression -> instruction
  | Store: value -> expression -> instruction.

  Inductive program :=
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

  Definition heap := MM.t word.

  Definition heap_put (x:mid) (v:word) (hs:heap) : heap :=
  MM.add x v hs.

  Definition mk_heap := @MM.empty word.

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

  Inductive Eval (s:store) : value -> word -> Prop :=
  | eval_var:
    forall x w,
    MV.MapsTo x w s ->
    Eval s (Var x) w
  | eval_word:
    forall w,
    Eval s (Word w) w.

  Inductive VReduces (s:state) (t:tid) (v:value) (w:word): Prop :=
  | v_reduces_def:
    forall m,
    Local s t m ->
    Eval m v w ->
    VReduces s t v w.

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

  Structure code_fragment := {
    c_vars: list var;
    c_code: program
  }.

  (** Defines the available code-fragments of the language *)

  Variable CF: MC.t code_fragment.

  Inductive EReduces : (state * expression) -> effect -> (state * word) -> Prop :=
  | e_reduces_malloc:
    forall h t s v w,
    ~ MM.In h (s_heap s) ->
    VReduces s t v w ->
    EReduces (s, Malloc v) (t,WRITE h) (s_global_put h w s, HeapLabel h)
  | e_reduces_load:
    forall s t v w h,
    VReduces s t v (HeapLabel h) ->
    MM.MapsTo h w (s_heap s) ->
    EReduces (s, Deref v) (t, READ h) (s, w)
  | e_reduces_future:
    forall f cf vs t s t' (l':store),
    MC.MapsTo f cf CF ->
    Bind s t (c_vars cf) vs l' ->
    ~ MT.In t' (s_tasks s) ->
    EReduces (s, Future f vs) (t, FUTURE t') ((s_spawn t' l' (c_code cf)) s, TaskLabel t')
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
    IReduces (s, Store v (Value v')) (t, WRITE h) (s_global_put h w s').

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

Module Typesystem.
  Section Defs.

  Definition t_store := MV.t type.
  Definition t_taskmap := MT.t type.
  Definition t_heap := MM.t type.

  Section Checks.

  (** Type of tasks *)
  Variable TS: t_taskmap.

  (** Type of heap *)
  Variable HS: t_heap.

  Inductive WCheck: word -> type -> Prop :=
  | w_check_num:
    forall n,
    WCheck (Num n) t_number
  | w_check_task:
    forall x t,
    MT.MapsTo x t TS ->
    WCheck (TaskLabel x) (t_task t)
  | w_check_heap:
    forall x t,
    MM.MapsTo x t HS ->
    WCheck (HeapLabel x) (t_ref t).


  Structure signature := {
    s_ret: type;
    s_params: list type
  }.

  Definition s_task s := t_task (s_ret s).
  Definition signaturemap := MC.t signature.
  (** Type of the code fragments *)
  Variable CS: signaturemap.

  Section Values.
    (** Type of store *)
    Variable LS: t_store.

    Inductive VCheck: value -> type -> Prop :=
    | v_check_var:
      forall x t,
      MV.MapsTo x t LS ->
      VCheck (Var x) t
    | v_check_word:
      forall w t,
      WCheck w t ->
      VCheck (Word w) t.

    Inductive VSCheck : list value -> list type -> Prop :=
    | vs_check_nil:
      VSCheck nil nil
    | vs_check_cons:
      forall v t vs ts,
      VCheck v t ->
      VSCheck vs ts ->
      VSCheck (v::vs) (t::ts).

  Inductive ECheck: expression -> type -> Prop :=
  | e_check_value:
    forall v t,
    VCheck v t ->
    ECheck (Value v) t
  | e_check_deref:
    forall v t,
    VCheck v (t_ref t) ->
    ECheck (Deref v) t
  | e_check_malloc:
    forall v t,
    VCheck v t ->
    ECheck (Malloc v) (t_ref t)
  | e_check_future:
    forall f vs s,
    MC.MapsTo f s CS ->
    VSCheck vs (s_params s) ->
    ECheck (Future f vs) (s_task s)
  | e_check_force:
    forall v t,
    VCheck v (t_task t) ->
    ECheck (Force v) t.

  Inductive ICheck: instruction -> t_store -> Prop :=
  | i_check_assign:
    forall x e t,
    ECheck e t ->
    ICheck (Assign x e) (MV.add x t LS)
  | i_check_store:
    forall v e t,
    VCheck v (t_ref t) ->
    ECheck e t ->
    ICheck (Store v e) LS.

  End Values.

  Inductive PCheck: t_store -> program -> type -> Prop :=
  | p_check_ret:
    forall s v t,
    VCheck s v t ->
    PCheck s (Ret v) t
  | p_check_seq:
    forall s i p s' t,
    ICheck s i s' ->
    PCheck s' p t ->
    PCheck s (Seq i p) t
  | p_check_if:
    forall s v p1 p2 t,
    VCheck s v t_number ->
    PCheck s p1 t ->
    PCheck s p2 t ->
    PCheck s (If v p1 p2) t.

  End Checks.

  Structure t_state := {
    t_s_heap: t_heap;
    t_s_taskmap: t_taskmap;
    t_s_stores: MT.t t_store;
    t_s_signatures: signaturemap
  }.

  Variable s: t_state.
  Let WCheck := WCheck (t_s_taskmap s) (t_s_heap s).

  Inductive MidCheck hs m : Prop :=
  | mid_check_def:
    forall w t,
    MM.MapsTo m w hs ->
    WCheck w t ->
    WCheck (HeapLabel m) (t_ref t) ->
    MidCheck hs m.

  Definition HeapLabelCheck hs := forall m, MM.In m hs -> MidCheck hs m.
  Definition HeapDomCheck (hs:heap) := forall m, MM.In m hs <-> MM.In m (t_s_heap s).

  Inductive HCheck hs : Prop :=
  | h_check_def:
    HeapLabelCheck hs ->
    HeapDomCheck hs ->
    HCheck hs.

  (** Check the local store *)

  Inductive VarCheck (m:store) (mt:t_store) (x:var) : Prop :=
  | var_check_def:
    forall w t,
    MV.MapsTo x w m ->
    MV.MapsTo x t mt ->
    WCheck w t ->
    VarCheck m mt x.

  Definition StoreVarCheck (m:store) mt := forall x, MV.In x m -> VarCheck m mt x.
  Definition StoreDomCheck (m:store) (mt:t_store) := forall x, MV.In x m <-> MV.In x mt.
  Let PCheck := PCheck (t_s_taskmap s) (t_s_heap s) (t_s_signatures s).

  Inductive TCheck (ts:taskmap) x : Prop :=
  | t_check_def:
    forall p t m mt,
    MT.MapsTo x (m,p) ts -> (* get store and code *)
    MT.MapsTo x mt (t_s_stores s) -> (* get type of store *)
    MT.MapsTo x t (t_s_taskmap s) -> (* get type of code *)
    StoreVarCheck m mt -> (* check if store matches its type *)
    PCheck mt p t -> (* check if the code matches its type *)
    TCheck ts x.

  Definition TaskLabelCheck (ts:taskmap) := forall x, MT.In x ts -> TCheck ts x.
  Definition TaskmapDomCheck (ts:taskmap) := forall x, MT.In x ts <-> MT.In x (t_s_taskmap s).
  Definition StoresDomCheck (ts:taskmap) := forall x, MT.In x ts <-> MT.In x (t_s_stores s).

  Inductive TMCheck tm : Prop :=
  | tm_check_def:
    TaskLabelCheck tm ->
    TaskmapDomCheck tm ->
    StoresDomCheck tm ->
    TMCheck tm.

  Inductive SCheck : state -> Prop :=
  | s_check_def:
    forall hs tm,
    TMCheck tm ->
    HCheck hs ->
    SCheck (hs,tm).

  End Defs.
End Typesystem.

Module Progress.
  Section Task.
  Variable s: state.

  Inductive ERun (h:mid) (t:tid) m : expression -> op -> Prop :=
  | e_run_deref:
    forall x v,
    Eval m v (HeapLabel x) ->
    ERun h t m (Deref v) (READ x)
  | e_run_malloc:
    forall v,
    ERun h t m (Malloc v) (WRITE h)
  | e_run_future:
    forall f vs,
    ERun h t m (Future f vs) (FUTURE t)
  | e_run_force:
    forall v x,
    Eval m v (TaskLabel x) ->
    ERun h t m (Force v) (FORCE x).

  Inductive IRun s : instruction -> op -> Prop :=
  | i_run_assign:
    forall x v,
    IRun s (Assign x (Value v)) TAU
  | i_run_store:
    forall v v' h,
    Eval s v (HeapLabel h) ->
    IRun s (Store v (Value v')) (WRITE h).

  Inductive Run h t : task -> op -> Prop :=
  | run_e:
    forall s i p e o,
    Expression i e ->
    ERun h t s e o ->
    Run h t (s,Seq i p) o
  | run_i:
    forall s i p o,
    IRun s i o ->
    Run h t (s,Seq i p) o
  | run_if:
    forall s v p1 p2,
    Run h t (s, (If v p1 p2)) TAU.
  End Task.

  Definition is_running (t:task) :=
  let (s,p) := t in
  match p with
  | Ret _ => false
  | Seq _ _ => true
  | If _ _ _ => true
  end.

  Definition is_blocking o :=
  match o with
  | FUTURE _ => true
  | _ => false
  end.



End Progress.
