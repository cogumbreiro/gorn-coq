Set Implicit Arguments.

Require Import Tid.
Require Import Mid.

Section Defs.
  Inductive datum :=
  | d_task : tid -> datum
  | d_mem : mid -> datum
  | d_any : datum.

  Inductive op :=
  | CONTINUE: op
  | ALLOC: mid -> op
  | READ: mid -> datum -> op
  | WRITE: mid -> datum -> op
  | FUTURE: tid -> list datum -> op
  | FORCE: tid -> datum -> op.

  Definition event := (tid * op) % type.


End Defs.
