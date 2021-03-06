Set Implicit Arguments.

Require Import SafeJoins.
Require Import Lang.
Require Import Tid.
Require Import Cid.
Require Import Mid.
Require Import Var.
Require Import Typesystem.

Section Progress.
  Section Task.
  Variable CF: code_segment.
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
    MT.In x (s_tasks s) ->
    Eval m v (TaskLabel x) ->
    ERun t m (Force v) (FORCE x).

  Inductive IRun (s:state) m : instruction -> op -> Prop :=
  | i_run_assign:
    forall x v w,
    Eval m v w ->
    IRun s m (Assign x (Value v)) TAU
  | i_run_store:
    forall v v' w h,
    Eval m v (HeapLabel h) ->
    Eval m v' w ->
    MM.In h (s_heap s) ->
    IRun s m (Store v (Value v')) (WRITE h).

  Inductive PRun t : task -> op -> Prop :=
  | p_run_e:
    forall m i p e o,
    Expression i e ->
    ERun t m e o ->
    PRun t (m, Seq i p) o
  | p_run_i:
    forall m i p o,
    IRun s m i o ->
    PRun t (m,Seq i p) o
  | p_run_if:
    forall m v p1 p2 n,
    Eval m v (Num n) ->
    PRun t (m, (If v p1 p2)) TAU
  | p_run_ret:
    forall m v w,
    Eval m v w ->
    PRun t (m, Ret v) TAU.

  Inductive Run : Prop :=
  | run_def:
    (forall x t, MT.MapsTo x t (snd s) -> exists o, PRun x t o) ->
    Run.
  
  End Task.

  Require CG.

  Variable CF: code_segment.
  Variable s:state.
  Require SafeJoins.
  Variable trc: SafeJoins.trace.
  Variable k: list (tid*tid).
  Variable S: SafeJoins.Safe trc k.

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

  Variable s_t: t_state.
  Variable c_t: t_code_segment.

  Variable ST: SCheck c_t s_t s.
  Variable CT: CSCheck s_t c_t CF.

  Let store_check_in_rev:
    forall x st mt,
    StoreCheck s_t st mt ->
    MV.In x mt ->
    MV.In x st.
  Proof.
    intros.
    inversion H.
    auto.
  Qed.

  Let v_check_to_eval:
    forall mt v t_t st,
    StoreCheck s_t st mt ->
    VCheck (t_s_tasks s_t) (t_s_heap s_t) mt v t_t ->
    exists w, Eval st v w.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    - assert (i: MV.In x st) by eauto using MV_Extra.mapsto_to_in.
      apply MV_Extra.in_to_mapsto in i.
      destruct i as (w,?).
      eauto using eval_var.
    - eauto using eval_word.
  Qed.

  Let v_check_to_w_check:
    forall st mt x w t,
    StoreCheck s_t st mt ->
    VCheck (t_s_tasks s_t) (t_s_heap s_t) mt (Var x) t ->
    MV.MapsTo x w st ->
    MV.MapsTo x t mt ->
    WCheck (t_s_tasks s_t) (t_s_heap s_t) w t.
  Proof.
    intros.
    destruct H as (?,_).
    assert (i:MV.In x st) by eauto using MV_Extra.mapsto_to_in.
    apply H in i.
    inversion i.
    assert (w0 = w) by eauto using MV_Facts.MapsTo_fun; subst.
    assert (t0 = t) by eauto using MV_Facts.MapsTo_fun; subst.
    assumption.
  Qed.


  Let v_check_to_w_check_alt:
    forall mt v t st,
    StoreCheck s_t st mt ->
    VCheck (t_s_tasks s_t) (t_s_heap s_t) mt v t ->
    exists w, 
    Eval st v w /\ (
    (exists x, v = Var x /\ MV.MapsTo x w st /\ WCheck (t_s_tasks s_t) (t_s_heap s_t) w t)
    \/
    (v = Word w /\ WCheck (t_s_tasks s_t) (t_s_heap s_t) w t)).
  Proof.
    intros.
    assert (E: exists w, Eval st v w) by eauto.
    destruct E as (w,E).
    exists w; split; auto.
    inversion E; subst; inversion H0; subst.
    - left.
      assert (WCheck (t_s_tasks s_t) (t_s_heap s_t) w t) by eauto.
      eauto.
    - eauto.
  Qed.

  Let w_check_in_heap:
    forall x t,
    WCheck (t_s_tasks s_t) (t_s_heap s_t) (HeapLabel x) (t_ref t) ->
    MM.In x (s_heap s).
  Proof.
    intros.
    inversion ST.
    inversion H1.
    inversion H.
    assert (MM.In x (t_s_heap s_t)) by eauto using MM_Extra.mapsto_to_in.
    eauto.
  Qed.

  Let w_check_in_tasks:
    forall x t,
    WCheck (t_s_tasks s_t) (t_s_heap s_t) (TaskLabel x) (t_task t) ->
    MT.In x (s_tasks s).
  Proof.
    intros.
    inversion ST.
    inversion H0; clear H0.
    inversion H; clear H.
    assert (MT.In x (t_s_tasks s_t)) by eauto using MT_Extra.mapsto_to_in.
    eauto.
  Qed.

  Let e_prog_malloc:
    forall v t mt st x,
    StoreCheck s_t st mt ->
    VCheck (t_s_tasks s_t) (t_s_heap s_t) mt v t ->
    exists o, ERun CF s x st (Malloc v) o.
  Proof.
    intros.
    eapply v_check_to_eval in H0; eauto.
    destruct H0 as (w, E); subst.
    eauto using e_run_malloc, Mid.find_not_in.
  Qed.

  Let e_prog_deref:
    forall x st p v t mt,
    MT.MapsTo x (st, p) (s_tasks s) ->
    StoreCheck s_t st mt ->
    VCheck (t_s_tasks s_t) (t_s_heap s_t) mt v (t_ref t) ->
    exists o, ERun CF s x st (Deref v) o.
  Proof.
    intros.
    eapply v_check_to_w_check_alt in H1; eauto.
    destruct H1 as (?, (?, Y)); subst.
    destruct Y as [(?,(?,(?,W)))|(?,W)]; subst;
    inversion W; subst;
    eauto using e_run_deref.
  Qed.

  Let vs_check_to_eval:
    forall mt vs l st,
    StoreCheck s_t st mt ->
    VSCheck (t_s_tasks s_t) (t_s_heap s_t) mt vs l ->
    List.Forall (fun v : value => exists w : word, Eval st v w) vs.
  Proof.
    induction vs; intros. {
     apply List.Forall_nil.
    }
    inversion H0; subst; clear H0.
    eauto using List.Forall_cons.
  Qed.

  Let vs_check_length:
    forall mt vs l st,
    StoreCheck s_t st mt ->
    VSCheck (t_s_tasks s_t) (t_s_heap s_t) mt vs l ->
    length l = length vs.
  Proof.
    induction vs; intros. {
      inversion H0; subst; auto.
    }
    inversion H0; subst; clear H0.
    assert (length ts = length vs) by eauto.
    simpl.
    rewrite H0.
    auto.
  Qed.

  Let e_prog_future:
    forall x st p mt t vs f,
    MT.MapsTo x (st, p) (s_tasks s) ->
    StoreCheck s_t st mt ->
    MC.MapsTo f t c_t ->
    VSCheck (t_s_tasks s_t) (t_s_heap s_t) mt vs (s_params t) ->
    exists o, ERun CF s x st (Future f vs) o.
  Proof.
    intros.
    assert (i: MC.In f CF). {
      apply MC_Extra.mapsto_to_in in H1.
      inversion CT.
      auto.
    }
    apply MC_Extra.in_to_mapsto in i; destruct i as (c, mt_cf).
    assert (length (c_vars c) = length vs). {
      assert (length (s_params t) = length vs) by eauto.
      inversion CT.
      apply H4 in mt_cf.
      inversion mt_cf.
      assert (t0 = t) by eauto using MC_Facts.MapsTo_fun; subst.
      intuition.
    }
    eauto using e_run_future, Tid.find_not_in.
  Qed.

  Let e_check_to_e_run:
    forall mt e t st p x,
    MT.MapsTo x (st, p) (s_tasks s) ->
    ECheck (t_s_tasks s_t) (t_s_heap s_t) c_t mt e t ->
    StoreCheck s_t st mt ->
    (exists v, e = Value v /\ exists w, Eval st v w) \/ (exists o, ERun CF s x st e o).
  Proof.
    intros.
    inversion H0; subst; clear H0.
    - eauto.
    - eauto using e_prog_malloc.
    - eauto using e_prog_deref.
    - eauto using e_prog_future.
    - right.
      assert (X:=H2).
      eapply v_check_to_w_check_alt in H2; eauto.
      destruct H2 as (w, (E, Y)); subst.
      destruct Y as [(y,(?,(?,W)))|(?,W)]; subst;
      inversion W; subst; eauto using e_run_force.
  Qed.

  Let i_check_to_i_run:
    forall mt x i s' st p,
    StoreCheck s_t st mt ->
    MT.MapsTo x (st, p) (s_tasks s) ->
    ICheck (t_s_tasks s_t) (t_s_heap s_t) c_t mt i s' ->
    exists o, IRun s st i o \/
    exists e, (Expression i e /\ ERun CF s x st e o).
  Proof.
    intros.
    inversion H1; subst; clear H1.
    - eapply e_check_to_e_run in H2; eauto.
      destruct H2 as [(v,(w,(?,?)))|(o,E)]; subst.
      + eauto using i_run_assign.
      + eauto using expression_assign.
    - assert (E:=H3).
      eapply e_check_to_e_run in H3; eauto.
      destruct H3 as [(v',(w,(?,?)))|(o,E')]; subst.
      + inversion E; subst.
        rename H4 into V.
        eapply v_check_to_w_check_alt in H2; eauto.
        destruct H2 as (w', (Ev, X)).
        destruct X as [(y,(?,(?,W)))|(?,W)]; subst;
        inversion W; subst;
        eauto using i_run_store.
      + eauto using expression_store.
  Qed.


  Let p_prog_to_p_run:
    forall x t_t mt st p,
    StoreCheck s_t st mt ->
    MT.MapsTo x (st, p) (s_tasks s) ->
    PCheck (t_s_tasks s_t) (t_s_heap s_t) c_t mt p t_t ->
    exists o, PRun CF s x (st, p) o.
  Proof.
    intros.
    inversion H1; subst; clear H1.
    - assert (w: exists w, Eval st v w) by eauto.
      destruct w.
      eauto using p_run_ret.
    - eapply i_check_to_i_run in H2; eauto.
      destruct H2 as (o, X).
      destruct X as [?|(e,(?,?))].
      + eauto using p_run_i.
      + eauto using p_run_e.
    - assert (X:=H2).
      eapply v_check_to_w_check_alt in X; eauto.
      destruct X as (w, (E,X)).
      destruct X as [(y,(?,(?,W)))|(?,W)]; subst;
      inversion W; subst;
      eauto using p_run_if.
  Qed.

  Let t_taks_to_run:
    forall x st p,
    MT.MapsTo x (st, p) (s_tasks s) ->
    TaskLabelCheck c_t s_t (s_tasks s) ->
    TaskCheck c_t s_t x (st, p) ->
    exists o, PRun CF s x (st, p) o.
  Proof.
    intros.
    inversion H1; subst.
    inversion H6.
    eapply p_prog_to_p_run; eauto.
  Qed.

  Let R: Run CF s.
  Proof.
    intros.
    inversion ST.
    rewrite <- H1 in *; clear H1.
    apply run_def.
    intros.
    inversion H.
    simpl in *.
    destruct t as (st, p).
    eauto.
  Qed.

  Let mt1_spec_1: forall k e, MT.MapsTo k e mt1 -> exists o, PRun CF s k e o.
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
    PRun CF s x tsk (FORCE y) ->
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

  (* XXX: MOVE ME OUT *)

  Lemma combine_inv_cons:
    forall {A:Type} {B:Type} (l1:list A) (l2:list B) x y l,
    List.combine l1 l2 = ((x, y) :: l)%list ->
    exists l1' l2', (l1 = x::l1' /\ l2 = y :: l2' /\ List.combine l1' l2' = l) % list.
  Proof.
    intros.
    destruct l1, l2; inversion H.
    eauto.
  Qed.

  (* XXX: MOVE ME OUT *)

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

  Let i_progress_assign:
    forall x y w m p v,
    Eval m v w ->
    MT.MapsTo x (m, Seq (Assign y (Value v)) p) (s_tasks s) ->
    IReduces (s, Assign y (Value v)) (x, TAU) (s_local_put x y w s).
  Proof.
    eauto using i_reduces_assign.
  Qed.

  Let i_progress_store:
    forall m v v' h x w p,
    Eval m v (HeapLabel h) ->
    Eval m v' w ->
    MM.In h (s_heap s) ->
    MT.MapsTo x (m, Seq (Store v (Value v')) p) (s_tasks s) ->
    IReduces (s, Store v (Value v')) (x, WRITE h) (s_global_put h w s).
  Proof.
    eauto using i_reduces_store.
  Qed.

  Let i_progress:
    forall x m p i o,
    MT.MapsTo x (m,Seq i p) (s_tasks s) ->
    IRun s m i o ->
    exists s', IReduces (s, i) (x,o) s'.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    - eauto.
    - eauto.
  Qed.

  Let p_progress:
    forall x st p o,
    MT.MapsTo x (st, p) (s_tasks s) ->
    MT.MapsTo x (st, p) mt1 -> (* for the ret case *)
    (forall y, o = FORCE y -> MT.In y mt2) ->
    PRun CF s x (st,p) o ->
    exists s' p', PReduces CF (s, p) (x,o) (s', p').
  Proof.
    intros.
    inversion H2; subst.
    - eauto.
    - eapply i_progress in H6;eauto.
      destruct H6.
      eauto using p_reduces_seq.
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
    destruct (SafeJoins.progress S N) as (x, (Hi,?)).
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
      - inversion H1; subst.
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
      - inversion H0.
    } clear H.
    destruct tsk as (m,p).
    eapply p_progress in TR; eauto.
    destruct TR as (s',(p',PR)).
    exists (x,o).
    eauto using reduces_def, program_def.
  Qed.

End Progress.


Section KnowledgeOf.
  Definition KnowledgeOf s k :=
    forall x y,
    FGraph.Edge k (x, y) ->
    MT.In x (s_tasks s) /\ MT.In y (s_tasks s).

  Inductive Translate (k:list (tid*tid)) : effect -> list (tid*tid) -> Prop :=
  | translate_fork:
    forall k' x y,
    SafeJoins.Reduces k {| SafeJoins.op_t := SafeJoins.FORK; SafeJoins.op_src:=x; SafeJoins.op_dst := y |} k' ->
    Translate k (x, FUTURE y) k'
  | translate_join:
    forall k' x y,
    SafeJoins.Reduces k {| SafeJoins.op_t := SafeJoins.JOIN; SafeJoins.op_src:=x; SafeJoins.op_dst := y |} k' ->
    Translate k (x, FORCE y) k'
  | translate_write:
    forall x y,
    Translate k (x, WRITE y) k
  | translate_read:
    forall x y,
    Translate k (x, READ y) k
  | translate_tau:
    forall x,
    Translate k (x, TAU) k.

  Let set_program_in:
    forall x ts t p,
    MT.In x ts ->
    MT.In x (tm_set_program t p ts).
  Proof.
    intros.
    unfold tm_set_program, tm_update.
    destruct (MT_Extra.find_rw t ts) as [(R,?)|(?,(R,?))]. {
      rewrite R in *.
      assumption.
    }
    rewrite R.
    rewrite MT_Facts.add_in_iff.
    auto.
  Qed.

  Let tm_put_var_in:
    forall x ts h y w,
    MT.In x ts ->
    MT.In x (tm_put_var h y w ts).
  Proof.
    intros.
    unfold tm_put_var, tm_update.
    destruct (MT_Extra.find_rw h ts) as [(R,?)|(?,(R,?))]. {
      rewrite R in *.
      assumption.
    }
    rewrite R.
    rewrite MT_Facts.add_in_iff.
    auto.
  Qed.

  Let tasks_set_program_in:
    forall x s t p,
    MT.In x (s_tasks s) ->
    MT.In x (s_tasks (s_set_program t p s)).
  Proof.
    intros.
    destruct s as (ms, ts).
    simpl in *.
    auto.
  Qed.

  Let knowledge_of_set_program:
    forall s t p k,
    KnowledgeOf s k ->
    KnowledgeOf (s_set_program t p s) k.
  Proof.
    intros.
    unfold KnowledgeOf in *.
    intros.
    apply H in H0.
    destruct H0.
    auto.
  Qed.

  Let knowledge_of_global_put:
    forall s k w h,
    KnowledgeOf s k ->
    KnowledgeOf (s_global_put h w s) k.
  Proof.
    intros.
    unfold KnowledgeOf in *.
    intros.
    destruct s.
    simpl in *.
    auto.
  Qed.

  Let knowledge_of_local_put:
    forall k w h s x,
    KnowledgeOf s k ->
    KnowledgeOf (s_local_put h x w s) k.
  Proof.
    unfold KnowledgeOf.
    intros.
    destruct s as (hs, ts).
    simpl in *.
    apply H in H0.
    destruct H0.
    auto.
  Qed.

  Let program_to_in:
    forall s x p,
    Program s x p ->
    MT.In x (s_tasks s).
  Proof.
    intros.
    inversion H; subst; clear H.
    eauto using MT_Extra.mapsto_to_in.
  Qed.

  Let knowledge_of_fork:
    forall s k x y k' p' l' p,
    KnowledgeOf s k ->
    SafeJoins.Reduces k
       {| op_t := FORK; op_src := x; op_dst := y |} k' ->
    MT.In x (s_tasks s) ->
    KnowledgeOf
      (s_set_program x p
        (s_spawn y l' p' s)) k'.
  Proof.
    intros.
    apply knowledge_of_set_program.
    unfold KnowledgeOf; intros a b; intros.
    destruct s as (ms, ts).
    simpl.
    repeat rewrite MT_Facts.add_in_iff.
    inversion H0; subst; clear H0.
    unfold FGraph.Edge in *.
    apply fork_inv_in in H2.
    destruct H2 as [(?,Hi)|[(?,?)|Hi]]; subst.
    - apply H in Hi.
      destruct Hi.
      auto.
    - auto.
    - apply H in Hi.
      destruct Hi.
      auto.
  Qed.

  Let knowledge_of_join:
    forall s k x y k' p,
    KnowledgeOf s k ->
    SafeJoins.Reduces k
       {| op_t := JOIN; op_src := x; op_dst := y |} k' ->
    KnowledgeOf (s_set_program x p s) k'.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    unfold KnowledgeOf.
    intros a b; intros.
    apply join_inv_in in H0.
    destruct H0 as [(?,Hi)|Hi].
    - subst.
      apply H in H4.
      apply H in Hi.
      destruct H4, Hi.
      auto.
    - apply H in Hi.
      destruct Hi.
      auto.
  Qed.

  Lemma knowledge_of_i_reduces:
    forall k k' t s i s' p o,
    KnowledgeOf s k ->
    Translate k (t, o) k' ->
    IReduces (s, i) (t, o) s' ->
    KnowledgeOf (s_set_program t p s') k'.
  Proof.
    intros.
    inversion H1; subst; clear H1;
    inversion H0; subst; clear H0; auto.
  Qed.

  Lemma knowledge_of_reduces:
    forall s s' e CF k k',
    KnowledgeOf s k ->
    Reduces CF s e s' ->
    Translate k e k' ->
    KnowledgeOf s' k'.
  Proof.
    intros.
    inversion H0; subst; clear H0.
    inversion H3; subst; clear H3.
    - rename p0 into p.
      rename s'0 into s'.
      inversion H9; subst; clear H9; inversion H1; subst; auto.
      + eauto.
      + eauto.
    - eapply knowledge_of_i_reduces; eauto.
    - inversion H1; subst.
      auto.
    - inversion H1; subst; auto.
  Qed.
End KnowledgeOf.