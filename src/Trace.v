Set Implicit Arguments.

Require Import Tid.
Require Import Mid.

Section Defs.
  Inductive datum :=
  | d_task : tid -> datum
  | d_mem : mid -> datum
  | d_any : datum.

  Inductive op :=
  | INIT: op
  | ALLOC: mid -> op
  | READ: mid -> datum -> op
  | WRITE: mid -> datum -> op
  | FUTURE: tid -> op
  | FORCE: tid -> op.

  Definition event := (tid * op) % type.

  Definition trace := list event.

End Defs.
