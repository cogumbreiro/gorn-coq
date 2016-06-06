Require Import Tid.
Require Import Lang.
Require Import Dep.
Require Import Mid.

Section Defs.
  Definition local := MT.t (list dep).
  Definition global := MM.t dep.

  Definition state := (global * local) % type.

  Inductive op :=
  | LOCAL_ADD: dep -> op
  | LOCAL_REM: dep -> op
  | GLOBAL_PUT: mid -> dep -> op
  | GLOBAL_DEL: mid -> op
  | FUTURE: tid -> list dep -> op
  | FORCE: tid -> option dep -> op.

  Definition to_lang_op (o:op) : Lang.op :=
  match o with
  | LOCAL_ADD _ => Lang.TAU
  | LOCAL_REM _ => Lang.TAU
  | GLOBAL_PUT x _ => Lang.WRITE x
  | GLOBAL_DEL x => Lang.WRITE x
  | FUTURE x _ => Lang.FUTURE x
  | FORCE x _ => Lang.FORCE x
  end.

  Definition as_trace := List.map to_lang_op.

  Definition local_update f (t:tid) (l:local) : local :=
  match MT.find t l with
  | Some ds => MT.add t (f ds)%list l
  | _ => l
  end.

  Definition local_add t d := local_update (cons d) % list t.

  Definition local_remove (t:tid) (d:dep) := local_update (List.remove dep_eq_dec d) t.

  Definition local_create (t:tid) (ds:list dep) (l:local) : local := MT.add t ds l.

  Definition effect := (tid * op) % type.

  Inductive Reduces : state -> effect -> state -> Prop :=
  | reduces_l_add:
    forall l g t d,
    MT.In t l ->
    Reduces (g, l) (t, LOCAL_ADD d) (g, local_add t d l)
  | reduces_l_rem:
    forall l g t d,
    MT.In t l ->
    Reduces (g, l) (t, LOCAL_REM d) (g, local_remove t d l)
  | reduces_g_put:
    forall g l m d t,
    Reduces (g, l) (t, GLOBAL_PUT m d) (MM.add m d g, l)
  | reduces_g_del:
    forall g l m t,
    Reduces (g, l) (t, GLOBAL_DEL m) (MM.remove m g, l)
  | reduces_future:
    forall t t' ds ds' l g,
    List.incl ds' ds ->
    ~ MT.In t' l ->
    MT.MapsTo t ds l ->
    Reduces (g, l) (t, FUTURE t' ds') (g, MT.add t' ds' l)
  | reduce_force_none:
    forall t g l,
    Reduces (g, l) (t, FORCE t None)  (g, l)
  | reduce_force_some:
    forall g l t t' d ds,
    MT.MapsTo t' ds l ->
    List.In d ds ->
    Reduces (g, l) (t, FORCE t' (Some d)) (g, local_add t d l).

End Defs.

