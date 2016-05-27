Require Import Lang.
Require Import Tid.
Require Import Cid.
Require Import Mid.
Require Import Var.

Section Progress.
  Section Task.
  Variable CF: MC.t code_fragment.
  Variable s: state.

  Inductive ERun (t:tid) m : expression -> op -> Prop :=
  | e_run_malloc:
    forall v w x,
    ~ MM.In x (s_heap s) ->
    Eval m v w ->
    ERun t m (Malloc v) (WRITE x)
  | e_run_deref:
    forall x v,
    Eval m v (HeapLabel x) ->
    MM.In x (s_heap s) ->
    ERun t m (Deref v) (READ x)
  | e_run_future:
    forall f c vs y,
    MC.MapsTo f c CF ->
    length (c_vars c) = length vs ->
    List.Forall (fun v => exists w, Eval m v w) vs ->
    ~ MT.In y (s_tasks s) ->
    ERun t m (Future f vs) (FUTURE y)
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

  Variable CF: MC.t code_fragment.
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

  Variable R: Run CF s.

  Let mt1_spec_1: forall k e, MT.MapsTo k e mt1 -> exists o, TRun CF s k e o.
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
    TRun CF s x tsk (FORCE y) ->
    FGraph.Edge k (x,y).

  Let e_progress_malloc:
    forall x y st v w p,
    ~ MM.In y (s_heap s) ->
    Eval st v w ->
    MT.MapsTo x (st,p) (s_tasks s) ->
    ERun CF s x st (Malloc v) (WRITE y) ->
    EReduces CF (s, Malloc v) (x, WRITE y) (s_global_put y w s, HeapLabel y).
  Proof.
    intros.
    eauto using e_reduces_malloc, v_reduces_alt.
  Qed.

  Let v_reduces_vec:
    forall x st p vs,
    MT.MapsTo x (st,p) (s_tasks s) ->
    List.Forall (fun v => exists w, Eval st v w) vs ->
    List.Forall (fun v => exists w, VReduces s x v w) vs.
  Proof.
    intros.
    rewrite List.Forall_forall in *.
    intros.
    apply H0 in H1.
    destruct H1; eauto.
  Qed.

  Let v_reduces_vec_combine:
    forall x vs,
    List.Forall (fun v => exists w, VReduces s x v w) vs ->
    forall xs,
    List.Forall (fun (p:var*value) => let (y,v) := p in exists w, VReduces s x v w) (List.combine xs vs).
  Proof.
    intros.
    rewrite List.Forall_forall in *.
    intros.
    destruct x0 as (y,v).
    apply List.in_combine_r in H0.
    auto.
  Qed.

  (* XXX: MOVE ME OUT *)

  Lemma combine_inv_nil:
    forall {A:Type} {B:Type} (l1:list A) (l2:list B),
    List.combine l1 l2 = nil ->
    l1 = nil \/ l2 = nil.
  Proof.
    intros.
    destruct l1, l2; auto.
    inversion H.
  Qed.

  Lemma combine_inv_cons:
    forall {A:Type} {B:Type} (l1:list A) (l2:list B) x y l,
    List.combine l1 l2 = ((x, y) :: l)%list ->
    exists l1' l2', (l1 = x::l1' /\ l2 = y :: l2' /\ List.combine l1' l2' = l) % list.
  Proof.
    intros.
    destruct l1, l2; inversion H.
    eauto.
  Qed.

  Lemma length_inv_nil:
    forall {A:Type} (l:list A),
    length l = 0 ->
    l = nil.
  Proof.
    intros.
    destruct l; auto.
    inversion H.
  Qed.

  Let v_reduces_vec_to_bind:
    forall l x vs xs,
    List.combine xs vs = l ->
    length xs = length vs ->
    List.Forall (fun (p:var*value) => let (y,v) := p in exists w, VReduces s x v w) l ->
    exists m, Bind s x xs vs m.
  Proof.
    induction l; intros. {
      apply combine_inv_nil in H.
      destruct H; subst; simpl in *;
        try apply length_inv_nil in H0;
        symmetry in H0;
        try apply length_inv_nil in H0;
        subst;
        eauto using bind_nil.
    }
    destruct a as (x1,v1).
    apply combine_inv_cons in H.
    destruct H as (l1, (l2, (?,(?,Hc)))); subst.
    assert (B: exists m, Bind s  x l1 l2 m). {
      inversion H0.
      inversion H1.
      auto.
    }
    destruct B as (m, B).
    inversion H1; subst.
    destruct H3.
    eauto using bind_cons.
  Qed.

  Let e_progress_future:
    forall x st p y vs f c,
    MC.MapsTo f c CF ->
    length (c_vars c) = length vs ->
    List.Forall (fun v => exists w, Eval st v w) vs ->
    ~ MT.In y (s_tasks s) ->
    MT.MapsTo x (st,p) (s_tasks s) ->
    ERun CF s x st (Future f vs) (FUTURE y) ->
    exists s' w, EReduces CF (s, Future f vs) (x, FUTURE y) (s', w).
  Proof.
    intros.
    assert (B: exists m, Bind s x (c_vars c) vs m) by eauto; destruct B as (m, B).
    eauto using e_reduces_future.
  Qed.

  Let e_progress_force:
    forall x st p v y,
    MT.MapsTo x (st,p) (s_tasks s) ->
    MT.In y mt2 ->
    ERun CF s x st (Force v) (FORCE y) ->
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
    ERun CF s x st (Deref v) (READ y) ->
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
    ERun CF s x st e o ->
    exists w s', EReduces CF (s, e) (x, o) (s', w).
  Proof.
    intros.
    inversion H1; subst.
    - eauto using e_progress_malloc.
    - eapply e_progress_read in H1; eauto.
      destruct H1; eauto.
    - eapply e_progress_future in H1; eauto.
      destruct H1 as (?,(?,?)).
      eauto.
    - eapply e_progress_force in H1; eauto.
      destruct H1.
      eauto.
  Qed.

  Let p_prog_seq:
    forall x m p i e o,
    MT.MapsTo x (m,Seq i p) (s_tasks s) ->
    Expression i e ->
    ERun CF s x m e o ->
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
    TRun CF s x (st,p) o ->
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
