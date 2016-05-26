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


(*
  Inductive PRun: (state * program) -> effect -> Prop :=
  | p_reduces_eval:
    forall s s' i e w p o,
    Expression i e ->
    ERun (s,e) o (s',w) ->
    PRun (s, Seq i p) o (s', Seq (eval w i) p)
  | p_reduces_seq:
    forall s i p s' o,
    IRun (s,i) o s' ->
    PRun (s, Seq i p) o (s', p)
  | i_reduces_if_zero:
    forall s t v p1 p2,
    VRun s t v (Num 0) ->
    PRun (s, If v p1 p2) (t,TAU) (s, p2)
  | i_reduces_if_succ:
    forall s t v n p1 p2,
    VRun s t v (Num (S n)) ->
    PRun (s, If v p1 p2) (t,TAU) (s, p1).
*)

  Inductive TRun t : task -> op -> Prop :=
  | t_run_e:
    forall m i p e o,
    Expression i e ->
    ERun t m e o ->
    TRun t (m, Seq i p) o
(*  | t_run_i:
    forall s i p o,
    IRun s i o ->
    TRun t (s,Seq i p) o *)
  | t_run_if:
    forall m v p1 p2 n,
    Eval m v (Num n) ->
    TRun t (m, (If v p1 p2)) TAU.

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

  Let v_reduces_alt:
    forall x v w st p,
    MT.MapsTo x (st,p) (snd s) ->
    Eval st v w ->
    VReduces s x v w.
  Proof.
    intros.
    eauto using v_reduces_def, store_def.
  Qed.

  Let e_progress_force:
    forall x st p v y,
    MT.MapsTo x (st,p) (snd s) ->
    MT.In y mt2 ->
    ERun s x st (Force v) (FORCE y) ->
    exists w, EReduces CF (s, Force v) (x, FORCE y) (s, w).
  Proof.
    intros.
    inversion H1.
    clear H3 H2.
    apply mt2_spec_1 in H0.
    destruct H0.
    exists w.
    eauto using e_reduces_force.
  Qed.

  Let e_progress:
    forall x st p o e,
    MT.MapsTo x (st,p) (snd s) ->
    (forall y, o = FORCE y -> MT.In y mt2) ->
    ERun s x st e o ->
    exists w s', EReduces CF (s, e) (x, o) (s', w).
  Proof.
    intros.
    inversion H1.
    subst.
    eapply e_progress_force in H1; eauto.
    destruct H1.
    eauto.
  Qed.

  Let p_prog_seq:
    forall x m p i e o,
    MT.MapsTo x (m,Seq i p) (snd s) ->
    Expression i e ->
    ERun s x m e o ->
    (forall y, o = FORCE y -> MT.In y mt2) ->
    exists s' p', PReduces CF (s, Seq i p) (x,o) (s', p').
  Proof.
    intros.
    eapply e_progress in H1; eauto.
    destruct H1 as (w, (s', ER)).
    eauto using p_reduces_eval.
  Qed.

  Let p_prog_if:
    forall st v n x p1 p2,
    Eval st v (Num n) ->
    MT.MapsTo x (st, If v p1 p2) (snd s) ->
    exists s' p', PReduces CF (s, If v p1 p2) (x,TAU) (s', p').
  Proof.
    intros.
    destruct n.
    - eauto using i_reduces_if_zero.
    - eauto using i_reduces_if_succ.
  Qed.

  Let t_run_progress:
    forall x st p o,
    TRun s x (st,p) o ->
    MT.MapsTo x (st, p) (snd s) ->
    (forall y, o = FORCE y -> MT.In y mt2) ->
    exists s' p', PReduces CF (s, p) (x,o) (s', p').
  Proof.
    intros.
    inversion H; subst.
    - eauto.
    - eauto. 
  Proof.

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
    assert (X: forall y, o = FORCE y -> MT.In y mt2). {
      intros; subst.
      inversion TR; subst.
      inversion H1; subst.
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
