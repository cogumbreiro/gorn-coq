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
