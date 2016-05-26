Require Import Lang.
Require Import Tid.
Require Import Cid.
Require Import Mid.

Section Progress.
  Section Task.
  Variable s: state.

  Inductive ERun (t:tid) m : expression -> op -> Prop :=
(*  | e_run_malloc:
    forall v,
    ERun h t m (Malloc v) (WRITE h) *)
  | e_run_deref:
    forall x v,
    Eval m v (HeapLabel x) ->
    MM.In x (fst s) ->
    ERun t m (Deref v) (READ x)
(*  | e_run_future:
    forall f vs,
    (forall v, List.In vs -> exists w, Eval m v w) ->
    ~ MT.In y ->
    ERun x m (Future f vs) (FUTURE y)*)
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
    TRun t (m, (If v p1 p2)) TAU
  | t_run_ret:
    forall m v w,
    Eval m v w ->
    TRun t (m, Ret v) TAU.

  Inductive Run : Prop :=
  | run_def:
    (forall x t, MT.MapsTo x t (snd s) -> exists o, TRun x t o) ->
    Run.
  
  End Task.

  Require CG.

  Variable s:state.
  Variable t: CG.Trace.trace.
  Variable k: list (tid*tid).
  Variable S: CG.SafeJoins.Safe t k.

  Variable edge_to_task_fst:
    forall x y,
    FGraph.Edge k (x, y) ->
    MT.In x (s_tasks s).

  Variable edge_to_task_snd:
    forall x y,
    FGraph.Edge k (x, y) ->
    MT.In y (s_tasks s).

  Let get_ret (t:tid) (tsk:task) : option value :=
  let (m,p) := tsk in
  match p with
  | Ret v => Some v
  | _ => None
  end.

  Let get_ret_some:
    forall x m p v,
    get_ret x (m, p) = Some v ->
    exists w, p = Ret w.
  Proof.
    intros.
    destruct p; simpl in H; inversion H; subst; eauto.
  Qed.

  Definition is_running t tsk : bool :=
  match get_ret t tsk with
  | Some _ => false
  | _ => true
  end. 

  Let stopped_tasks := MT_Props.partition is_running (s_tasks s).

  Let mt1 := fst (stopped_tasks). (* running *)
  Let mt2 := snd (stopped_tasks). (* stopped *)

  Let is_running_morph:
    Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) is_running.
  Proof.
    auto with *.
  Qed.

  Let P: MT_Props.Partition (s_tasks s) mt1 mt2.
  Proof.
    eauto using MT_Props.partition_Partition.
  Qed.

  Variable R: Run s.

  Let mt1_spec_1: forall k e, MT.MapsTo k e mt1 -> exists o, TRun s k e o.
  Proof.
    intros.
    inversion R.
    destruct P as (_,P').
    assert (MT.MapsTo k0 e (s_tasks s)). {
      apply P'.
      auto.
    }
    auto.
  Qed.

  Let v_reduces_alt:
    forall x v w st p,
    MT.MapsTo x (st,p) (s_tasks s) ->
    Eval st v w ->
    VReduces s x v w.
  Proof.
    intros.
    eauto using v_reduces_def, store_def.
  Qed.

  Let is_stopped_alt:
    forall x st v w,
    MT.MapsTo x (st, Ret v) (s_tasks s) ->
    Eval st v w ->
    IsStopped s x.
  Proof.
    intros.
    eauto using program_def, stopped_def, is_stopped_def.
  Qed.

  Let mt2_spec_1: forall x, MT.In x mt2 -> IsStopped s x.
  Proof.
    intros.
    apply MT_Extra.in_to_mapsto in H.
    destruct H as (e,mt).
    eapply MT_Props.partition_iff_2 with (m:=s_tasks s) in mt; eauto.
    destruct mt.
    unfold is_running in *.
    remember (get_ret x e) as o.
    symmetry in Heqo.
    destruct o. {
      destruct e.
      apply get_ret_some in Heqo.
      destruct Heqo; subst.
      inversion R as [R1].
      assert (mt := H).
      apply R1 in H.
      destruct H as (o,HT).
      inversion HT; subst.
      eauto.
    }
    inversion H0.
  Qed.

  Let mt1_not_stopped: forall x, MT.In x mt1 -> ~ IsStopped s x.
  Proof.
    intros.
    unfold not; intros.
    apply MT_Extra.in_to_mapsto in H.
    destruct H as (e,mt).
    eapply MT_Props.partition_iff_1 with (m:=s_tasks s) in mt; eauto.
    destruct mt.
    unfold is_running in *.
    remember (get_ret x e) as o.
    symmetry in Heqo.
    destruct o. {
      inversion H1.
    }
    destruct H0.
    destruct H0.
    destruct H0.
    assert (e=(l, Ret v)) by eauto using MT_Facts.MapsTo_fun; subst.
    simpl in *.
    inversion Heqo.
  Qed.

  Variable run_to_edge:
    forall x tsk y,
    TRun s x tsk (FORCE y) ->
    FGraph.Edge k (x,y).

  Variable CF: MC.t code_fragment.

  Let e_progress_force:
    forall x st p v y,
    MT.MapsTo x (st,p) (s_tasks s) ->
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

  Let e_progress_read:
    forall x st p v y,
    MT.MapsTo x (st,p) (s_tasks s) ->
    Eval st v (HeapLabel y) ->
    MM.In y (fst s) ->
    ERun s x st (Deref v) (READ y) ->
    exists w, EReduces CF (s, Deref v) (x, READ y) (s, w).
  Proof.
    intros.
    apply MM_Extra.in_to_mapsto in H1.
    destruct H1.
    eauto using e_reduces_load.
  Qed.

  Let e_progress:
    forall x st p o e,
    MT.MapsTo x (st,p) (s_tasks s) ->
    (forall y, o = FORCE y -> MT.In y mt2) ->
    ERun s x st e o ->
    exists w s', EReduces CF (s, e) (x, o) (s', w).
  Proof.
    intros.
    inversion H1; subst.
    - eapply e_progress_read in H1; eauto.
      destruct H1; eauto.
    - eapply e_progress_force in H1; eauto.
      destruct H1.
      eauto.
  Qed.

  Let p_prog_seq:
    forall x m p i e o,
    MT.MapsTo x (m,Seq i p) (s_tasks s) ->
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
    MT.MapsTo x (st, If v p1 p2) (s_tasks s) ->
    exists s' p', PReduces CF (s, If v p1 p2) (x,TAU) (s', p').
  Proof.
    intros.
    destruct n.
    - eauto using i_reduces_if_zero.
    - eauto using i_reduces_if_succ.
  Qed.

  Let p_progress:
    forall x st p o,
    MT.MapsTo x (st, p) (s_tasks s) ->
    MT.MapsTo x (st, p) mt1 -> (* for the ret case *)
    (forall y, o = FORCE y -> MT.In y mt2) ->
    TRun s x (st,p) o ->
    exists s' p', PReduces CF (s, p) (x,o) (s', p').
  Proof.
    intros.
    inversion H2; subst.
    - eauto.
    - eauto.
    - apply MT_Extra.mapsto_to_in in H0.
      apply mt1_not_stopped in H0.
      contradiction H0.
      eauto.
  Qed.

  Variable N': ~ MT.Empty mt1.

  Let N: MT_Extra.keys mt1 <> nil.
  Proof.
    remember (MT_Extra.keys mt1).
    destruct l.
    - apply MT_Extra.nonempty_in in N'.
      destruct N'.
      apply MT_Extra.keys_spec_2 in H.
      destruct H as (k', (?,Hi)).
      subst.
      rewrite <- Heql in *.
      inversion Hi.
    - auto with *.
  Qed.

  Theorem progress:
    exists e s', Reduces CF s e s'.
  Proof.
    destruct (CG.SafeJoins.progress S N) as (x, (Hi,?)).
    apply MT_Extra.keys_spec_1 in Hi.
    apply MT_Extra.in_to_mapsto in Hi.
    destruct Hi as (tsk,Hmt).
    assert (Hmt_s: MT.MapsTo x tsk (s_tasks s)). {
      destruct P as (_,P2).
      rewrite P2.
      eauto.
    }
    assert (Hmt1:= Hmt).
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
    destruct tsk as (m,p).
    eapply p_progress in TR; eauto.
    destruct TR as (s',(p',PR)).
    exists (x,o).
    eauto using reduces_def, program_def.
  Qed.

End Progress.
