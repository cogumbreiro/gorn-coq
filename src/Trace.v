Set Implicit Arguments.

Require Import Tid.
Require Import Mid.

Section Defs.
  Inductive datum :=
  | d_task : tid -> datum
  | d_mem : mid -> datum
  | d_any : datum.

  Inductive mem_op :=
  | ALLOC: mem_op
  | READ: datum -> mem_op
  | WRITE: datum -> mem_op.

  Inductive op :=
  | INIT: op
  | MEM: mid -> mem_op -> op
  | FUTURE: tid -> op
  | FORCE: tid -> op.

  Definition event := (tid * op) % type.

  Definition trace := list event.

End Defs.
