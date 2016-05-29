Require Import Cid.
Require Import Tid.
Require Import Mid.
Require Import Var.
Require Import Lang.

Definition t_store := MV.t type.
Definition t_taskmap := MT.t type.
Definition t_heap := MM.t type.

Section Checks.

  (** Type of tasks *)
  Variable TS: t_taskmap.

  (** Type of heap *)
  Variable HS: t_heap.

  (** Typecheck words. *)

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

  (** Define the type of a code block (an arrow type). *)

  Structure t_code := {
    s_params: list type;
    s_ret: type
  }.

  (**
    Invoking a future of this code type, yields a
    type, which is a future of the return type.
    *)

  Definition t_future s := t_task (s_ret s).

  (** Defines the code segment type of a program. *)

  Definition t_code_segment := MC.t t_code.

  (** Type of the code fragments *)
  Variable CS: t_code_segment.

  Section Values.

    (** Type of store *)

    Variable LS: t_store.

   (** Typecheck a value *)

    Inductive VCheck: value -> type -> Prop :=
    | v_check_var:
      forall x t,
      MV.MapsTo x t LS ->
      VCheck (Var x) t
    | v_check_word:
      forall w t,
      WCheck w t ->
      VCheck (Word w) t.

    (** Type check a vector of values. *)

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
    | e_check_malloc:
      forall v t,
      VCheck v t ->
      ECheck (Malloc v) (t_ref t)
    | e_check_deref:
      forall v t,
      VCheck v (t_ref t) ->
      ECheck (Deref v) t
(*    | e_check_future:
      forall f vs s,
      MC.MapsTo f s CS ->
      VSCheck vs (s_params s) ->
      ECheck (Future f vs) (t_future s)*)
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


Section State.
  Structure t_state := {
    t_s_heap: t_heap;
    t_s_tasks: t_taskmap;
    t_s_stores: MT.t t_store;
    t_s_signatures: t_code_segment
  }.

  Variable s: t_state.

  Let WCheck := WCheck (t_s_tasks s) (t_s_heap s).

  (* Check if a reference in the heap matches the expected type in t_heap. *)

  Inductive MidCheck (hs:heap) x : Prop :=
  | mid_check_def:
    forall w t,
    MM.MapsTo x w hs ->           (* H(x) = w) *)
    MM.MapsTo x t (t_s_heap s) -> (* \Gamma(x) = t *)
    WCheck w t ->                 (* |- w : t *)
    MidCheck hs x.

  (** Checks if all heaps in the heap are well typed. *)

  Definition HeapLabelCheck hs := forall m, MM.In m hs -> MidCheck hs m.

  (** Checks if all heap-type is in the heap *)

  Definition HeapLabelRange (hs:heap) := forall m, MM.In m (t_s_heap s) -> MM.In m hs.

  Inductive HeapCheck hs : Prop :=
  | heap_check_def:
    HeapLabelCheck hs ->
    HeapLabelRange hs ->
    HeapCheck hs.

  (** Check the local store *)

  Inductive VarCheck (m:store) (mt:t_store) (x:var) : Prop :=
  | var_check_def:
    forall w t,
    MV.MapsTo x w m ->  (* \sigma(x) = w *)
    MV.MapsTo x t mt -> (* \Gamma(x) = t *)
    WCheck w t ->       (* |- w : t *)
    VarCheck m mt x.

  Definition StoreVarCheck (m:store) mt := forall x, MV.In x m -> VarCheck m mt x.

  Definition StoreVarRange (m:store) (mt:t_store) := forall x, MV.In x mt -> MV.In x m.

  Inductive StoreCheck (m:store) (mt:t_store) : Prop :=
  | store_check_def:
    StoreVarCheck m mt ->
    StoreVarRange m mt ->
    StoreCheck m mt.

  Let PCheck := PCheck (t_s_tasks s) (t_s_heap s) (*t_s_signatures s*).

  (** Check a task *)

  Inductive ProgramCheck (x:tid) (mt:t_store) (p:program) : Prop :=
  | code_check_def:
    forall t,
    MT.MapsTo x t (t_s_tasks s) -> (* get type of code *)
    PCheck mt p t -> (* check if the code matches its type *)
    ProgramCheck x mt p.

  Inductive TaskCheck (x:tid) : task -> Prop :=
  | t_check_def:
    forall m p mt,
    MT.MapsTo x mt (t_s_stores s) -> (* get type of store *)
    StoreCheck m mt -> (* check if store matches its type *)
    ProgramCheck x mt p -> (* check the program *)
    TaskCheck x (m, p).

  Definition TaskLabelCheck (ts:taskmap) := forall x e, MT.MapsTo x e ts -> TaskCheck x e.

  Definition TaskLabelRange (ts:taskmap) := forall x, MT.In x (t_s_tasks s) -> MT.In x ts.

  Inductive TMCheck tm : Prop :=
  | tm_check_def:
    TaskLabelCheck tm ->
    TaskLabelRange tm ->
    TMCheck tm.

  Inductive SCheck : state -> Prop :=
  | s_check_def:
    forall hs tm,
    TMCheck tm ->
    HeapCheck hs ->
    SCheck (hs,tm).

End State.
