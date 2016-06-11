Require Import Tid.
Require Import Lang.
Require Import Dep.
Require Import Mid.

Section Defs.
  Definition local := list (tid * dep). (*MT.t (list dep).*)
  Definition global := MM.t (option dep).

  Definition memory := (global * local) % type.

  Definition m_global (m:memory) := fst m.

  Definition m_local (m:memory) := snd m.

  Inductive op :=
(*  | LOCAL_REM: dep -> op*)
  | GLOBAL_CREATE: mid -> option dep -> op
  | GLOBAL_PUT: mid -> option dep -> op
  | GLOBAL_GET: mid -> op
  | FUTURE: tid -> list dep -> op
  | FORCE: tid -> list dep -> op.
(*
  Definition local_update f (t:tid) (l:local) : local :=
  match MT.find t l with
  | Some ds => MT.add t (f ds)%list l
  | _ => l
  end.
*)
  Notation local_entry := (tid * dep) % type.

  Definition local_add t d (l:local) : local := cons (t,d) l. (*local_update (cons d) % list t.*)

  Fixpoint local_add_all t ds (l:local) : local :=
  match ds with
  | cons d ds => local_add t d (local_add_all t ds l)
  | nil => l
  end.

  Let local_entry_eq_dec :
    forall (x y : local_entry),
    { x = y } + { x <> y }.
  Proof.
    intros.
    destruct x as (x1,x2), y as (y1, y2).
    destruct (tid_eq_dec x1 y1), (dep_eq_dec x2 y2);
    subst;
    auto;
    right;
    intuition;
    inversion H;
    subst;
    contradiction n;
    auto.
  Qed.

  Definition local_remove (t:tid) (d:dep) (l:local) := List.remove local_entry_eq_dec (t,d) l. (*local_update (List.remove dep_eq_dec d) t.*)

(*  Definition local_create (t:tid) (ds:list dep) (l:local) : local := MT.add t ds l.*)

  Definition effect := (tid * op) % type.

  Inductive In (t:tid) (l:local) : Prop :=
  | in_def:
    forall d,
    List.In (t, d) l ->
    In t l.

  Inductive Local (l:local) x (d:dep) : Prop :=
  | local_def:
    List.In (x,d) l ->
    Local l x d.

  Inductive Reduces : memory -> effect -> memory -> Prop :=
  | reduces_g_get: (* read *)
    forall g l x t d,
    Local l t (d_mid x) ->
    MM.MapsTo x (Some d) g ->
    Reduces (g, l) (t, GLOBAL_GET x) (g, local_add t d l)
  | reduces_g_put: (* write *)
    forall g l x t o,
    Local l t (d_mid x) ->
    Reduces (g, l) (t, GLOBAL_PUT x o) (MM.add x o g, l)
(*  | reduces_l_rem: (* local store of a constant *)
    forall l g t o,
    In t l ->
    Reduces (g, l) (t, LOCAL_REM o) (g, local_remove t o l)*)
  | reduces_g_create: (* malloc *)
    forall g l x t o,
    ~ MM.In x g ->
    Local l t (d_mid x) ->
    Reduces (g, l) (t, GLOBAL_CREATE x o) (MM.add x o g, l)
  | reduces_future: (* future *)
    forall t t' ds l g,
    List.Forall (Local l t) ds ->
    ~ In t' l ->
    Reduces (g, l) (t, FUTURE t' ds) (g, local_add_all t' ds (local_add t (d_tid t') l))
  | reduce_force: (* force *)
    forall g l t t' d ds,
    List.Forall (Local l t) ds ->
    Reduces (g, l) (t, FORCE t' ds) (g, local_add t d l).

End Defs.

Module Lang.

  Definition to_lang_op (o:op) : Lang.op :=
  match o with
(*  | LOCAL_REM _ => Lang.TAU*)
  | GLOBAL_CREATE x _ => Lang.WRITE x
  | GLOBAL_PUT x _ => Lang.WRITE x
  | GLOBAL_GET x => Lang.READ x
  | FUTURE x _ => Lang.FUTURE x
  | FORCE x _ => Lang.FORCE x
  end.

  Definition to_lang_effects : list effect -> list Lang.effect := List.map (fun (e:effect) => (fst e, to_lang_op (snd e))).

End Lang.