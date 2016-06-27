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
  | FUTURE: tid -> list datum -> op
  | FORCE: tid -> datum -> op.

  Definition effect := (tid * op) % type.

  Require Import CG.

  Variable cg: computation_graph.

  Inductive Reduces : memory -> effect -> memory -> Prop :=
  | reduces_g_read:
    forall g l d n n' (x:tid) y l' g',
    (* a global read is a continue in the CG *)
    ReductionResult (x, CG.CONTINUE) cg (R_CONTINUE (C (n,n'))) ->
    (* the reference y is in the locals of task x *)
    Locals.MapsTo n (d_mem y) l ->
    (* the contents of reference y is datum d *)
    Shadow.MapsTo y d g cg ->
    (* add datum d to the locals of x *)
    Locals.Reduces l (n', CONS d n) l' ->
    (* update the shared memory to record the read *)
    Shadow.Reduces cg g (y, {| a_when := n'; a_what:=@READ datum |}) g' ->
    Reduces (g, l) (x, GLOBAL_READ y) (g', l')

  | reduces_g_write:
    forall g (l:local_memory datum) (x:tid) (y:mid) d n n' g',
    (* a global write is a continue in the CG *)
    ReductionResult (x, CG.CONTINUE) cg (R_CONTINUE (C (n,n'))) ->
    (* datum d being written is in the locals of task x *)
    Locals.MapsTo n d l ->
    (* the target reference is also in the locals of task x *)
    Locals.MapsTo n (d_mem y) l ->
    (* update the shared memory to record the write of datum d at reference y *)
    Shadow.Reduces cg g (y, {| a_when:=n'; a_what:=WRITE d|}) g' ->
    Reduces (g, l) (x, GLOBAL_WRITE y d) (g', l)

  | reduces_g_alloc:
    forall g l (x:tid) n n' d l' g' y,
    (* a global alloc is a continue edge in the CG *)
    ReductionResult (x, CG.CONTINUE) cg (R_CONTINUE (C (n,n'))) ->
    (* the datum being alloc'ed is a local *)
    Locals.MapsTo n d l ->
    (* update the shared memory with an alloc *)
    Shadow.Reduces cg g (y, {|a_when:=n;a_what:=ALLOC d|}) g' ->
    (* add reference y to the locals of task x *)
    Locals.Reduces l (n', CONS (d_mem y) n) l' ->
    Reduces (g, l) (x, GLOBAL_ALLOC y d) (g', l')

  | reduces_future:
    forall x nx nx' ny ds l g y l' l'',
    ReductionResult (x, CG.FORK y) cg (R_FORK (F (nx,ny)) (C (nx,nx'))) ->
    (* the locals of the new task are copied from the locals of the current task *)
    List.Forall (fun d => Locals.MapsTo nx d l) ds ->
    (* add task y to the locals of x *)
    Locals.Reduces l (nx', CONS (d_task y) nx) l' ->
    (* set the locals of y to be ds *)
    Locals.Reduces l' (ny, NEW ds) l'' ->
    Reduces (g, l) (x, FUTURE y ds) (g, l)

  | reduce_force:
    forall g l nx nx' ny d l' x y,
    (* CG reduced with a join *)
    ReductionResult (x, CG.JOIN y) cg (R_JOIN (J (ny,nx')) (C (nx,nx'))) ->
    (* Datum d is in the locals of y *)
    Locals.MapsTo ny d l ->
    (* Add d to the locals of x *)
    Locals.Reduces l (nx, CONS d nx') l' ->
    Reduces (g, l) (x, FORCE y d) (g, l').


  Inductive Knows (l:local_memory datum) : tid * tid -> Prop :=
  | knows_def:
    forall n x y,
    Node.MapsTo x n (fst cg) ->
    Locals.MapsTo n (d_task y) l ->
    Knows l (x, y).

End Defs.
