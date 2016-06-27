Set Implicit Arguments.

Require Import Coq.Lists.List.
Require Import Tid.
Require Import Lang.
Require Import Mid.
Require Import Shadow.
Require Import Node.

Module Locals.
Section Defs.
  Variable A:Type.

  Inductive op :=
  | CONS : A -> node -> op
  | NEW : list A -> op.

  Definition task_local := list A.

  Definition local_memory := MN.t task_local.

  Inductive Reduces (m:local_memory): (node * op) -> local_memory -> Prop :=
  | reduces_add:
    forall l x n n',
    MN.MapsTo n l m ->
    ~ MN.In n' m ->
    Reduces m (n', CONS x n) (MN.add n' (x::l) m)
  | reduces_new:
    forall l n,
    ~ MN.In n m ->
    Reduces m (n, NEW l) (MN.add n l m).

  Inductive MapsTo (n:node) (x:A) (ls:local_memory) : Prop :=
  | local_def:
    forall l,
    MN.MapsTo n l ls ->
    List.In x l ->
    MapsTo n x ls.

End Defs.
End Locals.

Section Defs.

  Import Locals.

  Inductive datum :=
  | d_task : tid -> datum
  | d_mem : mid -> datum
  | d_any : datum.


  Definition global_memory := access_history datum.

  Definition memory := (global_memory * (local_memory datum)) % type.

  Definition m_global (m:memory) := fst m.

  Definition m_local (m:memory) := snd m.

  Inductive op :=
  | CONTINUE: op
  | GLOBAL_ALLOC: mid -> datum -> op
  | GLOBAL_WRITE: mid -> datum -> op
  | GLOBAL_READ: mid -> op
  | FUTURE: node -> list datum -> op
  | FORCE: node -> datum -> op.

  Definition effect := (node * node * op) % type.

  Require Import CG.

  Variable cg: computation_graph.

  Inductive Reduces : memory -> effect -> memory -> Prop :=
  | reduces_g_read:
    forall g l d n n' x l' g',
    Locals.MapsTo n (d_mem x) l ->
    Shadow.MapsTo x d g cg ->
    Locals.Reduces l (n', CONS d n) l' ->
    Shadow.Reduces cg g (x, {| a_when := n; a_what:=@READ datum |}) g' ->
    Reduces (g, l) (x, GLOBAL_READ x) (g', l')

  | reduces_g_write:
    forall g (l:local_memory datum) x d n n' g',
    Locals.MapsTo n d l ->
    Locals.MapsTo n (d_mem x) l ->
    Shadow.Reduces cg g (x, {| a_when:=n; a_what:=WRITE d|}) g' ->
    Reduces (g, l) (n, n', GLOBAL_WRITE x d) (g', l)

  | reduces_g_alloc:
    forall g l x n n' d l' g',
    Locals.MapsTo n d l ->
    Shadow.Reduces cg g (x, {|a_when:=n;a_what:=ALLOC d|}) g' ->
    Locals.Reduces l (n', CONS (d_mem x) n) l' ->
    Reduces (g, l) (n, n', GLOBAL_ALLOC x d) (g', l')

  | reduces_future:
    forall nx nx' ny ds l g y l' l'',
    List.Forall (fun d => Locals.MapsTo nx d l) ds ->
    Node.MapsTo y ny (fst cg) ->
    Locals.Reduces l (nx', CONS (d_task y) nx) l' ->
    Locals.Reduces l' (ny, NEW ds) l'' ->
    Reduces (g, l) (nx, nx', FUTURE ny ds) (g, l)

  | reduce_force:
    forall g l nx nx' ny d l',
    Locals.MapsTo ny d l ->
    Locals.Reduces l (nx, CONS d nx') l' ->
    Reduces (g, l) (nx, nx', FORCE ny d) (g, l').


  Inductive Knows (l:local_memory datum) : tid * tid -> Prop :=
  | knows_def:
    forall n x y,
    Node.MapsTo x n (fst cg) ->
    Locals.MapsTo n (d_task y) l ->
    Knows l (x, y).

End Defs.


Section SR.
  Require SJ_CG.

  Definition LocalToKnows (l:Locals.local_memory datum) cg sj :=
    forall l p,
    Knows cg l p ->
    SJ_CG.Knows (fst cg) sj p.

  Lemma local_to_knows_reduces:
    forall a t cg k,
    Events.Reduces k e k' ->
    CG.Reduces cg e cg' ->
    SJ cg k sj ->
    

End SR.