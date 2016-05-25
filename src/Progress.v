Require Import Lang.
Require Import Tid.
Require Import Cid.

Section Progress.
  Section Task.
  Variable s: state.

  Inductive ERun (t:tid) m : expression -> op -> Prop :=
(*  | e_run_deref:
    forall x v,
    Eval m v (HeapLabel x) ->
    ERun h t m (Deref v) (READ x)
  | e_run_malloc:
    forall v,
    ERun h t m (Malloc v) (WRITE h)
  | e_run_future:
    forall f vs,
    ERun h t m (Future f vs) (FUTURE t)*)
  | e_run_force:
    forall v x,
    MT.In x (snd s) ->
    Eval m v (TaskLabel x) ->
    ERun t m (Force v) (FORCE x).

(*
  Inductive IRun s : instruction -> op -> Prop :=
  | i_run_assign:
    forall x v,
    IRun s (Assign x (Value v)) TAU
  | i_run_store:
    forall v v' h,
    Eval s v (HeapLabel h) ->
    IRun s (Store v (Value v')) (WRITE h).
*)
  Inductive TRun t : task -> op -> Prop :=
  | t_run_e:
    forall s i p e o,
    Expression i e ->
    ERun t s e o ->
    TRun t (s,Seq i p) o.
(*  | t_run_i:
    forall s i p o,
    IRun s i o ->
    TRun t (s,Seq i p) o
  | t_run_if:
    forall s v p1 p2,
    TRun t (s, (If v p1 p2)) TAU. *)

  Inductive Run : Prop :=
  | run_def:
    (forall x t, MT.MapsTo x t (snd s) -> exists o, TRun x t o) ->
    Run.
  
  End Task.

  Require CG.

  Variable s:state.
  Variable R: Run s.
  Variable t: CG.Trace.trace.
  Variable k: list (tid*tid).
  Variable S: CG.SafeJoins.Safe t k.
  Variable CF: MC.t code_fragment.

  Variable mt1: MT.t task.
  Variable mt2: MT.t task.
  Variable P: MT_Props.Partition (snd s) mt1 mt2.
  Variable mt1_spec_1: forall k e, MT.MapsTo k e mt1 -> exists o, TRun s k e o.
  Variable mt2_spec_1: forall x, MT.In x mt2 -> IsStopped s x.
  Variable N: MT_Extra.keys mt1 <> nil.
  Variable edge_to_task_fst:
    forall x y,
    FGraph.Edge k (x, y) ->
    MT.In x (snd s).
  Variable edge_to_task_snd:
    forall x y,
    FGraph.Edge k (x, y) ->
    MT.In y (snd s).

  Variable run_to_edge:
    forall x tsk y,
    TRun s x tsk (FORCE y) ->
    FGraph.Edge k (x,y).

  Let t_run_progress:
    forall x tsk o,
    TRun s x tsk o ->
    MT.MapsTo x tsk (snd s) ->
    (exists y, o = FORCE y -> MT.In y mt2) ->
    exists e s', Reduces CF s e s'.
  Proof.
    intros.
    inversion H; subst; clear H.
    rename s0 into st.
    destruct o.
    - 
  Qed.

  Theorem progress:
    exists e s', Reduces CF s e s'.
  Proof.
    destruct (CG.SafeJoins.progress S N) as (x, (Hi,?)).
    apply MT_Extra.keys_spec_1 in Hi.
    apply MT_Extra.in_to_mapsto in Hi.
    destruct Hi as (tsk,Hmt).
    assert (Hmt_s: MT.MapsTo x tsk (snd s)). {
      destruct P as (_,P2).
      rewrite P2.
      eauto.
    }
    apply mt1_spec_1 in Hmt.
    destruct Hmt as (o, TR).
    assert (X: exists y, o = FORCE y -> MT.In y mt2). {
      inversion TR; subst.
      inversion H1; subst.
      rename x0 into y.
      exists y; intros.
      assert (n: ~ MT.In y mt1). {
        apply run_to_edge in TR.
        apply H in TR.
        unfold not; intros.
        contradiction TR.
        rewrite <- MT_Extra.keys_spec; auto using tid_eq_rw.
      }
      apply run_to_edge in TR.
      apply edge_to_task_snd in TR.
      apply MT_Props.Partition_In with (m1:=mt1) (m2:= mt2) in TR; auto.
      destruct TR; auto.
      contradiction.
    } clear H.
    eauto.
  Qed.
    

End Progress.
