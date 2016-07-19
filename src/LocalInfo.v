Set Implicit Arguments.

Require Import Coq.Lists.List.

Require Import Tid.
Require Import Lang.
Require Import Mid.
Require Import AccessHistory.
Require Import Node.
Require Import CG.
Require SJ_CG.
Require Import Trace.

Import AccessHistory.T.

Module Locals.
Section Defs.
  Variable A:Type.

  Inductive op :=
  | COPY : node -> op
  | CONS : A -> node -> op
  | NEW : list A -> op.

  Definition task_local := list A.

  Definition local_memory := MN.t task_local.

  Inductive Reduces (m:local_memory): (node * op) -> local_memory -> Prop :=
  | reduces_copy:
    forall l n n',
    MN.MapsTo n l m ->
    ~ MN.In n' m ->
    Reduces m (n', COPY n) (MN.add n' l m)
  | reduces_cons:
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


  Lemma maps_to_to_in:
    forall n x l,
    MapsTo n x l ->
    MN.In n l.
  Proof.
    intros.
    inversion H.
    eauto using MN_Extra.mapsto_to_in.
  Qed.
End Defs.

  Ltac simpl_red :=
    repeat match goal with
    | [ H1: Reduces _ (_, COPY _ _) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces _ (_, CONS _ _) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces _ (_, NEW _) _ |- _ ] =>
      inversion H1; subst; clear H1
    end.

End Locals.

Section Defs.
  Require Import Trace.

  Import Locals.

  Variable cg : computation_graph.

  Inductive Reduces : local_memory datum -> Trace.op -> local_memory datum -> Prop :=

  | reduces_alloc:
    forall l n n' d l' r es,
    (* a global alloc is a continue edge in the CG *)
    snd cg = C (n, n') :: es ->
    (* the datum being alloc'ed is a local *)
    Locals.MapsTo n d l ->
    (* add reference y to the locals of task x *)
    Locals.Reduces l (n', CONS (d_mem r) n) l' ->
    Reduces l (ALLOC r d) l'

  | reduces_read:
    forall l d n n' r l' es,
    snd cg = C (n, n') :: es ->
    (* the reference y is in the locals of task x *)
    Locals.MapsTo n (d_mem r) l ->
    (* add datum d to the locals of x *)
    Locals.Reduces l (n', CONS d n) l' ->
    Reduces l (READ r d) l'

  | reduces_write:
    forall l r d n n' es l',
    (* a global write is a continue in the CG *)
    snd cg = C (n, n') :: es ->
    (* datum d being written is in the locals of task x *)
    Locals.MapsTo n d l ->
    (* the target reference is also in the locals of task x *)
    Locals.MapsTo n (d_mem r) l ->
    Locals.Reduces l (n', COPY datum n) l' ->
    Reduces l (WRITE r d) l'

  | reduces_future:
    forall x nx nx' ny ds l y l' l'' es,
    snd cg = F (nx, ny) :: C (nx, nx') :: es ->
    (* the locals of the new task are copied from the locals of the current task *)
    List.Forall (fun d => Locals.MapsTo nx d l) ds ->
    (* add task y to the locals of x *)
    Locals.Reduces l (nx', CONS (d_task y) nx) l' ->
    (* set the locals of y to be ds *)
    Locals.Reduces l' (ny, NEW ds) l'' ->
    Reduces l (FUTURE x ds) l

  | reduce_force:
    forall l nx nx' ny d l' y es,
    (* CG reduced with a join *)
    snd cg = J (ny,nx') :: C (nx,nx') :: es ->
    (* Datum d is in the locals of y *)
    Locals.MapsTo ny d l ->
    (* Task y is in the local memory of nx *)
    Locals.MapsTo nx (d_task y) l ->
    (* Add d to the locals of x *)
    Locals.Reduces l (nx', CONS d nx) l' ->
    Reduces l (FORCE y d) l'

  | reduce_continue:
    forall l n n' l' es,
    snd cg = C (n, n') :: es ->
    Locals.Reduces l (n', COPY datum n) l' ->
    Reduces l CONTINUE l'.

  Inductive LocalKnows (l:local_memory datum) : tid * tid -> Prop :=
  | local_knows_def:
    forall n x y,
    TaskOf n x (fst cg) ->
    Locals.MapsTo n (d_task y) l ->
    LocalKnows l (x, y).

End Defs.

  Ltac simpl_structs :=
  repeat simpl in *; match goal with
  | [ H2: _ :: _ = _ :: _ |- _ ] => inversion H2; subst; clear H2
  | [ H2:(_,_) = (_,_) |- _ ] => inversion H2; subst; clear H2
  | [ H2: Some _ = Some _ |- _ ] => inversion H2; subst; clear H2
  end.

  Ltac simpl_red :=
  match goal with
    | [ H1: Reduces (_::_,_::_) _ CONTINUE _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces (_::_,_::_) _ (ALLOC _ _) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces (_::_,_::_) _ (WRITE _ _) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces (_::_,_::_) _ (READ _ _) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces (_::_::_,_::_::_) _ (FUTURE _ _) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces (_::_,_::_::_) _ (FORCE _ _) _ |- _ ] =>
      inversion H1; subst; clear H1
  end;
  simpl_structs.

  Ltac handle_all :=
  try SJ_CG.simpl_red;
  try CG.simpl_red;
  try simpl_red;
  try Locals.simpl_red;
(*  try Shadow.simpl_red;*)
  try simpl_structs;
  simpl in *.


Section SR.

  Definition op_to_cg (o:op) : CG.op :=
  match o with
  | CONTINUE => CG.CONTINUE
  | ALLOC _ _ => CG.CONTINUE
  | WRITE _ _ => CG.CONTINUE
  | READ _ _ => CG.CONTINUE
  | FUTURE x _ => CG.FORK x
  | FORCE x _ => CG.JOIN x
  end.

  Definition event_to_cg (e:event) : CG.event :=
  let (x,o) := e in (x, op_to_cg o).

  Definition LocalToKnows (l:Locals.local_memory datum) cg sj :=
    forall p,
    LocalKnows cg l p ->
    SJ_CG.Knows (fst cg) sj p.

  Definition DomIncl (l:Locals.local_memory datum) (vs:list tid) :=
    forall n,
    MN.In n l ->
    Node n vs.

  Definition LastWriteCanJoin (g:cg_access_history) cg sj :=
    forall x a h r,
    MM.MapsTo r h g ->
    LastWrite (HB cg) a h ->
    a_what a = Some (d_task x) ->
    SJ_CG.CanJoin (a_when a) x sj.

  Definition LastWriteKnows (cg:computation_graph) (g:cg_access_history) l :=
    forall x y a h r,
    MM.MapsTo r h g ->
    LastWrite (HB (snd cg)) a h ->
    a_what a = Some (d_task y) ->
    TaskOf (a_when a) x (fst cg) ->
    LocalKnows cg l (x, y).

  Ltac expand H := inversion H; subst; clear H.

  Let knows_eq:
    forall l ls (x y:tid) n vs es,
    MN.MapsTo n l ls ->
    In (d_task y) l ->
    MapsTo x n vs ->
    LocalKnows (vs, es) ls (x, y).
  Proof.
    eauto using local_knows_def, Locals.local_def, maps_to_to_task_of.
  Qed.

  Let sj_knows_copy:
    forall vs es k sj x y n,
    SJ_CG.SJ (vs, es) k sj ->
    MapsTo x n vs ->
    SJ_CG.Knows vs sj (x, y) ->
    SJ_CG.Knows (x :: vs) (SJ_CG.Copy n :: sj) (x, y).
  Proof.
    intros.
    inversion H.
    simpl in *.
    eauto using SJ_CG.knows_copy.
  Qed.

  Let sj_knows_copy_0:
    forall vs sj l es a b x n la na,
    length vs = length sj ->
    LocalToKnows l (vs, es) sj ->
    MapsTo x n vs ->
    TaskOf na a vs ->
    MN.MapsTo na la l ->
    In (d_task b) la ->
    SJ_CG.Knows (x :: vs) (SJ_CG.Copy n :: sj) (a, b).
  Proof.
    intros.
    assert (SJ_CG.Knows vs sj (a,b)) by eauto using Locals.local_def, local_knows_def.
    destruct (tid_eq_dec x a). {
      subst.
      eapply SJ_CG.knows_copy; eauto.
    }
    apply SJ_CG.knows_neq; auto.
  Qed.

  Let local_to_knows_continue:
    forall cg sj sj' cg' l l' a b x k,
    LocalToKnows l cg sj ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces cg' l CONTINUE l' ->
    LocalKnows cg' l' (a, b) ->
    SJ_CG.Reduces sj cg' sj' ->
    SJ_CG.SJ cg k sj ->
    DomIncl l (fst cg) ->
    length (fst cg) = length sj ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    SJ_CG.simpl_red.
    simpl_red; Locals.simpl_red; simpl in *.
    expand H2; simpl in *. (* Knows *)
    apply task_of_inv in H3.
    destruct H3 as [(?,?)|?]. {
      subst.
      inversion H9; subst.
      rewrite MN_Facts.add_mapsto_iff in *.
      destruct H0 as [(_,?)|(N,_)]. {
        subst.
        eapply SJ_CG.knows_copy; eauto.
      }
      contradiction N; trivial.
    }
    expand H9.
    rewrite MN_Facts.add_mapsto_iff in *.
    destruct H1 as [(?,?)|(?,?)]. {
      subst.
      simpl_node.
    }
    eauto.
  Qed.

  Let local_to_knows_alloc:
    forall cg sj sj' cg' l l' a b x k y d,
    LocalToKnows l cg sj ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces cg' l (ALLOC y d) l' ->
    LocalKnows cg' l' (a, b) ->
    SJ_CG.Reduces sj cg' sj' ->
    SJ_CG.SJ cg k sj ->
    length (fst cg) = length sj ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    rename H5 into Heq.
    handle_all.
    expand H2.
    simpl in *.
    expand H5.
    apply task_of_inv in H3.
    rewrite MN_Facts.add_mapsto_iff in *.
    destruct H3 as [(?,?)|mt]. {
      subst.
      destruct H0 as [(_,?)|(N,_)]. {
        subst.
        destruct H1 as [Hx|?]. { inversion Hx. }
        eauto.
      }
      contradiction N; trivial.
    }
    destruct H0 as [(?,?)|(?,mt')]. {
      subst.
      simpl_node.
    }
    eauto.
  Qed.

  Let local_to_knows_write:
    forall cg sj sj' cg' l l' a b x k y d,
    LocalToKnows l cg sj ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces cg' l (WRITE y d) l' ->
    LocalKnows cg' l' (a, b) ->
    SJ_CG.Reduces sj cg' sj' ->
    SJ_CG.SJ cg k sj ->
    DomIncl l (fst cg) ->
    length (fst cg) = length sj ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    rename H5 into Hdom.
    handle_all.
    expand H2.
    simpl in *.
    expand H11.
    apply task_of_inv in H5.
    rewrite MN_Facts.add_mapsto_iff in *.
    destruct H5 as [(?,?)|?]. {
      subst.
      destruct H0 as [(_,?)|(N,_)]. {
        subst.
        eauto.
      }
      contradiction N; auto.
    }
    destruct H0 as [(?,?)|(?,?)]. {
      subst.
      simpl_node.
    }
    eauto.
  Qed.

  Let local_to_knows_read:
    forall cg sj sj' cg' l l' a b x k y k' d g g',
    LocalToKnows l cg sj ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces cg' l (READ y d) l' ->
    LocalKnows cg' l' (a, b) ->
    SJ_CG.Reduces sj cg' sj' ->
    SJ_CG.SJ cg k sj ->
    DomIncl l (fst cg) ->
    LastWriteCanJoin g (snd cg) sj ->
    SJ_CG.SJ cg' k' sj' ->
    DRF_Check (snd cg') g (READ y d) g' ->
    WellFormed cg g ->
    WellFormed cg' g' ->
    length (fst cg) = length sj ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    rename H5 into Hdom.
    rename H6 into Hwrite.
    rename H7 into Hsj'.
    rename H8 into Hdrf.
    rename H9 into Hwf.
    rename H10 into Hwf'.
    rename H11 into Heq.
    handle_all.
    expand H2.
    simpl in *.
    apply task_of_inv in H3.
    expand H5.
    rewrite MN_Facts.add_mapsto_iff in *.
    destruct H3 as [(?,?)|?]; subst. {
      subst.
      destruct H0 as [(_,Hx)|(N,_)]; subst. {
        destruct H1 as [?|Hi]. {
          subst.
          apply drf_check_inv_read_last_write with (x:=x) in Hdrf; auto.
          destruct Hdrf as (h, (a, (mt, (Hw, (?,?))))).
          eauto using SJ_CG.knows_def, maps_to_eq, SJ_CG.hb_spec, SJ_CG.can_join_cons.
        }
        simpl in *.
        eapply sj_knows_copy; eauto.
      }
      contradiction N; trivial.
    }
    destruct H0 as [(?,?)|(?,mt')]. {
      subst.
      simpl_node.
    }
    eauto.
  Qed.

  Let local_to_knows_future:
    forall cg sj sj' cg' l l' a b x y k ds,
    LocalToKnows l cg sj ->
    CG.Reduces cg (x, CG.FORK y) cg' ->
    Reduces cg' l (FUTURE y ds) l' ->
    LocalKnows cg' l' (a, b) ->
    SJ_CG.Reduces sj cg' sj' ->
    SJ_CG.SJ cg k sj ->
    DomIncl l (fst cg) ->
    length (fst cg) = length sj ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    rename H5 into Hdom.
    rename H6 into Heq.
    handle_all.
    expand H2; simpl in *.
    apply task_of_inv in H3.
    destruct H3 as [(?,?)|mt]. {
      subst.
      apply Locals.maps_to_to_in in H10.
      apply Hdom in H10.
      apply node_lt in H10.
      unfold NODE.lt, fresh in *.
      simpl in *.
      omega.
    }
    apply task_of_inv in mt.
    destruct mt as [(?,?)|mt]. {
      subst.
      apply Locals.maps_to_to_in in H10.
      apply Hdom in H10.
      apply node_lt in H10.
      unfold NODE.lt, fresh in *.
      simpl in *.
      omega.
    }
    assert (SJ_CG.Knows vs sj (a,b)) by eauto using Locals.local_def, local_knows_def.
    destruct (tid_eq_dec y a). {
      subst.
      contradiction H8.
      eauto using task_of_to_in.
    }
    apply SJ_CG.knows_neq; auto.
    destruct (tid_eq_dec x a). {
      subst.
      destruct (tid_eq_dec y b). {
        subst.
        eapply SJ_CG.knows_eq; auto.
      }
      eapply SJ_CG.knows_cons_neq; auto.
    }
    apply SJ_CG.knows_neq; auto.
  Qed.

  Let local_to_knows_force:
    forall cg sj sj' cg' l l' a b x k y d,
    LocalToKnows l cg sj ->
    CG.Reduces cg (x, CG.JOIN y) cg' ->
    Reduces cg' l (FORCE y d) l' ->
    LocalKnows cg' l' (a, b) ->
    SJ_CG.Reduces sj cg' sj' ->
    SJ_CG.SJ cg k sj ->
    length (fst cg) = length sj ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    rename H5 into Heq.
    handle_all.
    expand H2.
    simpl in *.
    expand H5.
    rename es0 into es.
    rename ny0 into ny.
    rewrite MN_Facts.add_mapsto_iff in *.
    apply task_of_inv in H3.
    destruct H3 as [(?,?)|mt]. {
      subst.
      destruct H0 as [(_,?)|(N,_)]. {
        subst.
        destruct H1 as [|Hi]. {
          subst.
          inversion H4; subst.
          eauto using local_knows_def, Locals.local_def, maps_to_to_task_of, SJ_CG.knows_append_right.
        }
        inversion H4; subst.
        eauto using SJ_CG.knows_append_left, local_knows_def, Locals.local_def, maps_to_to_task_of.
      }
      contradiction N; trivial.
    }
    destruct H0 as [(?,?)|(?, mt')]. {
      subst.
      simpl_node.
    }
    assert (SJ_CG.Knows vs sj (a,b)) by eauto using Locals.local_def, local_knows_def.
    destruct (tid_eq_dec x a). {
      subst.
      eauto using SJ_CG.knows_append_left.
    }
    apply SJ_CG.knows_neq; auto.
  Qed.

  Notation local_info := (Locals.local_memory datum).

  Definition memory := (cg_access_history * local_info) % type.

  Let local_to_knows_reduces:
    forall cg k sj sj' g g' cg' l l' x o k',
    LocalToKnows l cg sj ->

    T.TReduces cg (x,o) cg' ->
    SJ_CG.SJ cg k sj ->
    SJ_CG.SJ cg' k' sj' ->

    Reduces cg' l o l' ->
    DRF_Check (snd cg') g o g' ->
    SJ_CG.Reduces sj cg' sj' -> (* show that this is implied *)

    length (fst cg) = length sj ->
    DomIncl l (fst cg) ->
    LastWriteCanJoin g (snd cg) sj ->
    WellFormed cg g ->
    WellFormed cg' g' ->
    LocalToKnows l' cg' sj'.
  Proof.
    intros.
    unfold LocalToKnows.
    intros (a,b); intros.
    destruct o; simpl in *; eauto.
  Qed.

  Let dom_incl_reduces:
    forall l l' cg cg' x o,
    DomIncl l (fst cg) ->
    T.TReduces cg (x,o) cg' ->
    Reduces cg' l o l' ->
    DomIncl l' (fst cg').
  Proof.
    intros.
    unfold DomIncl.
    intros.
    destruct o; simpl in *; handle_all.
    - rewrite MN_Facts.add_in_iff in *.
      destruct H2. {
        subst.
        auto using node_eq.
      }
      eauto using node_cons, maps_to_to_node.
    - rewrite MN_Facts.add_in_iff in *.
      destruct H2. {
        subst.
        auto using node_eq.
      }
      eauto using node_cons, maps_to_to_node.
    - simpl in *.
      rewrite MN_Facts.add_in_iff in *.
      destruct H2. {
        subst.
        auto using node_eq.
      }
      eauto using node_cons, maps_to_to_node.
    - rewrite MN_Facts.add_in_iff in *.
      destruct H2. {
        subst.
        auto using node_eq.
      }
      eauto using node_cons, maps_to_to_node.
    - eauto using node_cons, maps_to_to_node.
    - rewrite MN_Facts.add_in_iff in *.
      destruct H2. {
        subst.
        auto using node_eq.
      }
      eauto using node_cons, maps_to_to_node.
  Qed.

  Let local_knows_cons:
    forall l ls n a b cg,
    LocalKnows cg l (a, b) ->
    ~ MN.In n l ->
    LocalKnows cg (MN.add n ls l) (a, b).
  Proof.
    intros.
    expand H.
    expand H4.
    assert (n <> n0). {
      unfold not; intros; subst.
      contradiction H0.
      eauto using MN_Extra.mapsto_to_in.
    }
    eauto using local_knows_def, Locals.local_def, MN.add_2.
  Qed.

  Let local_knows_cons_c:
    forall l b x vs es a e,
    LocalKnows (vs, es) l (a, b) ->
    LocalKnows (x :: vs, e :: es) l (a, b).
  Proof.
    intros.
    expand H.
    eauto using local_knows_def, task_of_cons.
  Qed.

  Let local_knows_cons_j:
    forall l b x vs es a e,
    LocalKnows (x :: vs, es) l (a, b) ->
    LocalKnows (x :: vs, e :: es) l (a, b).
  Proof.
    intros.
    expand H.
    eauto using local_knows_def, task_of_cons.
  Qed.

  Let task_of_simpl:
    forall vs r es h z a n g l x t,
    LastWriteKnows (vs, es) g l ->
    WellFormed (vs, es) g ->
    WellFormed (z :: vs, {| e_t := t; e_edge := (n,fresh vs) |} :: es) g ->
    LastWrite (HB ({| e_t := t; e_edge := (n,fresh vs) |} :: es)) a h ->
    MM.MapsTo r h g ->
    TaskOf (a_when a) x (z :: vs) ->
    TaskOf (a_when a) x vs.
  Proof.
    intros.
    apply task_of_inv in H4.
    destruct H4 as [(?,?)|?]. {
      subst.
      destruct a; simpl in *.
      subst.
      eapply last_write_inv_c in H2; eauto.
      apply last_write_to_in in H2.
      eapply wf_node with (vs:=vs) (es:=es) in H2; eauto.
      simpl in *.
      simpl_node.
    }
    assumption.
  Qed.

  Let last_write_can_join_continue:
    forall a x r g h vs es sj z c t n,
    WellFormed (vs, es) g ->
    LastWriteCanJoin g es sj ->
    LastWrite (HB ({| e_t:=t; e_edge:=(n, fresh vs)|} :: es)) a h ->
    MM.MapsTo r h g ->
    a_what a = Some (d_task x) ->
    MapsTo z n vs ->
    SJ_CG.CanJoin (a_when a) x (c :: sj).
  Proof.
    intros.
    eapply last_write_inv_c in H1; eauto using wf_continue.
    eapply H0 in H3; eauto.
    auto using SJ_CG.can_join_cons.
  Qed.

  Let local_to_can_join:
    forall z vs es sj n x l,
    LocalToKnows l (vs, es) sj ->
    MapsTo z n vs ->
    Locals.MapsTo n (d_task x) l ->
    SJ_CG.CanJoin n x sj.
  Proof.
    intros.
    assert (Hk: SJ_CG.Knows vs sj (z,x)). {
      eauto using local_knows_def, maps_to_to_task_of.
    }
    inversion Hk.
    simpl_node.
    assumption.
  Qed.

  Let can_join_copy:
    forall vs sj es z n l x,
    length vs = length sj ->
    LocalToKnows l (vs, es) sj ->
    MapsTo z n vs ->
    Locals.MapsTo n (d_task x) l ->
    SJ_CG.CanJoin (fresh vs) x (SJ_CG.Copy n :: sj).
  Proof.
    intros.
    apply maps_to_length_rw in H.
    rewrite H.
    apply SJ_CG.can_join_copy.
    eauto.
  Qed.

  Let last_write_can_join_reduces:
    forall g cg cg' sj l o l' sj' g' z,
    LastWriteCanJoin g (snd cg) sj ->

    WellFormed cg g ->
    WellFormed cg' g' ->

    Reduces cg' l o l' ->
    T.TReduces cg (z,o) cg' ->
    DRF_Check (snd cg') g o g' ->
    SJ_CG.Reduces sj cg' sj' -> (* show that this is implied *)

    length (fst cg) = length sj ->
    LocalToKnows l cg sj ->

    LastWriteCanJoin g' (snd cg') sj'.
  Proof.
    intros.
    unfold LastWriteCanJoin.
    intros.
    destruct o; simpl in *; handle_all; simpl_drf_check; eauto;
    rename H9 into Hlw;
    rename H10 into Heq;
    try (
      assert (Hmt := H8);
      rewrite MM_Facts.add_mapsto_iff in Hmt;
      destruct Hmt as [(?,?)|(?,?)]; eauto;
      subst
    ).
    - apply last_write_inv_cons_nil in Hlw; subst.
      simpl_structs.
      eauto.
    - apply last_write_inv_cons_read in Hlw.
      eauto.
    - assert ((fresh vs, Some d) = a). {
        eapply wf_last_write_inv_cons_write with (ah:=g); eauto using write_eq.
      }
      subst; simpl in *; simpl_node; simpl_structs.
      eauto.
    - eapply last_write_inv_c in Hlw; eauto using wf_continue.
      eapply last_write_inv_c in Hlw; eauto using wf_continue.
      eapply H in Heq; eauto.
      auto using SJ_CG.can_join_cons.
    - eapply last_write_inv_j in Hlw; eauto using wf_continue.
  Qed.

  Structure WellFormed cg k sj g l := {
    wf_ah_well_formed : AccessHistory.T.WellFormed cg g;
    wf_sj_well_formed: SJ_CG.SJ cg k sj;
    wf_dom_incl_prop: DomIncl l (fst cg);
    wf_last_write_can_join_prop: LastWriteCanJoin g (snd cg) sj;
    wf_local_to_knows_prop: LocalToKnows l cg sj
  }.

  Lemma wf_reduces:
    forall cg cg' sj sj' g g' l l' k x o,
    WellFormed cg k sj g l ->
    T.TReduces cg (x,o) cg' ->
    Reduces cg' l o l' ->
    DRF_Check (snd cg') g o g' ->
    SJ_CG.Reduces sj cg' sj' -> (* show that this is implied *)
    exists k', WellFormed cg' k' sj' g' l'.
  Proof.
    intros.
    inversion H.
    assert (Hx:=H3).
    eapply SJ_CG.sj_reduces_alt in H3; eauto.
    assert (Hwf: T.WellFormed cg' g') by eauto using wf_reduces.
    destruct H3 as (k',Hsj).
    exists k'.
    inversion wf_sj_well_formed0.
    apply Build_WellFormed; eauto.
  Qed.

  Lemma wf_sj_cg_reduces:
    forall cg cg' sj g g' l l' k x o,
    WellFormed cg k sj g l ->
    T.TReduces cg (x,o) cg' ->
    Reduces cg' l o l' ->
    DRF_Check (snd cg') g o g' ->
    exists sj', 
    SJ_CG.Reduces sj cg' sj'.
  Proof.
    intros.
    destruct o; simpl in *; handle_all; simpl_drf_check;
    eauto using SJ_CG.reduces_continue, SJ_CG.reduces_fork.
    exists (SJ_CG.Append nx0 ny0::sj).
    eapply SJ_CG.reduces_join;eauto using maps_to_cons.
    assert (Hk: LocalKnows (vs,es0) l (x,t)). {
      eapply local_knows_def; eauto using maps_to_to_task_of.
    }
    apply wf_local_to_knows_prop in H.
    apply H in Hk.
    inversion Hk.
    subst.
    simpl_node.
    assumption.
  Qed.

  Lemma wf_reduces_alt:
    forall cg cg' sj g g' l l' k x o,
    WellFormed cg k sj g l ->
    T.TReduces cg (x,o) cg' ->
    Reduces cg' l o l' ->
    DRF_Check (snd cg') g o g' ->
    exists sj' k', WellFormed cg' k' sj' g' l'.
  Proof.
    intros.
    assert (Hsj: exists sj', SJ_CG.Reduces sj cg' sj') by
    eauto using wf_sj_cg_reduces.
    destruct Hsj as (sj', Hsj).
    eauto using wf_reduces.
  Qed.

End SR.