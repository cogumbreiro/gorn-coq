Set Implicit Arguments.

Require Import Coq.Lists.List.

Require Import Tid.
Require Import Lang.
Require Import Mid.
Require Import AccessHistory.
Require Import Node.
Require Import CG.
Require SJ_CG.

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

  Import Locals.

  Inductive datum :=
  | d_task : tid -> datum
  | d_mem : mid -> datum
  | d_any : datum.

(*
  Definition global_memory := access_history datum.

  Definition memory := (global_memory * (local_memory datum)) % type.

  Definition m_global (m:memory) := fst m.

  Definition m_local (m:memory) := snd m.
*)

  Inductive op :=
  | CONTINUE: op
  | ALLOC: mid -> datum -> op
  | READ: mid -> datum -> op
  | WRITE: mid -> datum -> op
  | FUTURE: tid -> list datum -> op
  | FORCE: tid -> datum -> op.

  Definition event := (tid * op) % type.


  Variable cg : computation_graph.

  Inductive Reduces : local_memory datum -> op -> local_memory datum -> Prop :=

  | reduces_alloc:
    forall l n n' d l' r es,
    (* a global alloc is a continue edge in the CG *)
    snd cg = C (n, n') :: es ->
    (* the datum being alloc'ed is a local *)
    Locals.MapsTo n d l ->
    (* add reference y to the locals of task x *)
    Locals.Reduces l (n', CONS (d_mem r) n) l' ->
    Reduces l (ALLOC r d) l'

  | reduces_g_read:
    forall l d n n' r l' es,
    snd cg = C (n, n') :: es ->
    (* the reference y is in the locals of task x *)
    Locals.MapsTo n (d_mem r) l ->
    (* add datum d to the locals of x *)
    Locals.Reduces l (n', CONS d n) l' ->
    Reduces l (READ r d) l'

  | reduces_g_write:
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
    (* Add d to the locals of x *)
    Locals.Reduces l (nx', CONS d nx) l' ->
    Reduces l (FORCE y d) l'

  | reduce_continue:
    forall l n n' l' es,
    snd cg = C (n, n') :: es ->
    Locals.Reduces l (n', COPY datum n) l' ->
    Reduces l CONTINUE l'.

  Inductive Knows (l:local_memory datum) : tid * tid -> Prop :=
  | knows_def:
    forall n x y,
    Node.MapsTo x n (fst cg) ->
    Locals.MapsTo n (d_task y) l ->
    Knows l (x, y).

End Defs.

  Require AccessHistory.

  Notation access_history := (AccessHistory.access_history datum node).
  Notation access_history_op := (AccessHistory.op datum).

  Inductive DRF_Reduces (cg:computation_graph) (ah:access_history) : (mid * access_history_op) -> access_history -> Prop :=
  | drf_reduces:
    forall n n' es o ah' r,
    snd cg = C (n, n') :: es ->
    AccessHistory.RaceFreeAdd (HB cg) ah (r, n', o) ah' ->
    DRF_Reduces cg ah (r, o) ah'.

  Definition op_to_ah (o:op) : option (mid*access_history_op) :=
  match o with
  | ALLOC r d => Some (r, (AccessHistory.ALLOC, d))
  | READ r d => Some (r, (AccessHistory.READ, d))
  | WRITE r d => Some (r, (AccessHistory.WRITE, d))
  | _ => None
  end.

  Inductive DRF_Check (cg:computation_graph) (ah:access_history) : op -> access_history -> Prop :=
  | drf_check_some:
    forall o o' ah',
    op_to_ah o = Some o' ->
    DRF_Reduces cg ah o' ah' ->
    DRF_Check cg ah o ah'
  | drf_check_none:
    forall o,
    op_to_ah o = None ->
    DRF_Check cg ah o ah.

  Ltac simpl_structs :=
  repeat simpl in *; match goal with
  | [ H2: _ :: _ = _ :: _ |- _ ] => inversion H2; subst; clear H2
  | [ H2:(_,_) = (_,_) |- _ ] => inversion H2; subst; clear H2
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
    Knows cg l p ->
    SJ_CG.Knows (fst cg) sj p.

  Definition DomIncl (l:Locals.local_memory datum) (vs:list tid) :=
    forall n,
    MN.In n l ->
    Node n vs.

  Let LastWrite cg := (@LastWrite datum node (HB cg)).

  Definition LastWriteCanJoin (g:access_history) cg sj :=
    forall x a h r,
    MM.MapsTo r h g ->
    LastWrite cg a h ->
    a_what a = Some (d_task x) ->
    SJ_CG.CanJoin (a_when a) x sj.
(*
  Definition LastWriteKnows (g:access_history) cg sj :=
    forall m n a b,
    MM.MapsTo r h g ->
    LastWrite cg a h ->
    a_what = d_task x ->
    NodeOf a n (fst cg) ->
    SJ_CG.Knows (fst cg) sj (a, b).
*)
  Ltac expand H := inversion H; subst; clear H.

  Let knows_eq:
    forall l ls (x y:tid) n vs es,
    MN.MapsTo n l ls ->
    In (d_task y) l ->
    MapsTo x n vs ->
    Knows (vs, es) ls (x, y).
  Proof.
    eauto using knows_def, Locals.local_def.
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

  Let local_to_knows_continue_0:
    forall ls vs es x n l a an b sj k,
    LocalToKnows ls (vs, es) sj ->
    MapsTo x n vs ->
    MN.MapsTo n l ls ->
    ~ MN.In (fresh vs) ls ->
    MapsTo a an (x :: vs) ->
    Locals.MapsTo an (d_task b) (MN.add (fresh vs) l ls) ->
    SJ_CG.SJ (vs,es) k sj ->
    SJ_CG.Knows (x :: vs) (SJ_CG.Copy n :: sj) (a, b).
  Proof.
    intros.
    inversion H4; subst; clear H4.
    rename l0 into al.
    apply maps_to_inv in H3.
    destruct H3 as [(?,?)|(?,mt)]; subst. {
      rewrite MN_Facts.add_mapsto_iff in *.
      destruct H6 as [(_,?)|(N,_)]. {
        subst.
        eauto using knows_eq, sj_knows_copy.
      }
      contradiction N; trivial.
    }
    rewrite MN_Facts.add_mapsto_iff in *.
    destruct H6 as [(?,?)|(?,mt')]. {
      subst.
      simpl_map.
    }
    eauto using SJ_CG.knows_neq. 
  Qed.

  Let local_to_knows_continue:
    forall cg sj sj' cg' l l' a b x k,
    LocalToKnows l cg sj ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces cg' l CONTINUE l' ->
    Knows cg' l' (a, b) ->
    SJ_CG.Reduces sj cg' sj' ->
    SJ_CG.SJ cg k sj ->
    DomIncl l (fst cg) ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    SJ_CG.simpl_red.
    simpl_red; Locals.simpl_red; simpl in *.
    expand H2; simpl in *. (* Knows *)
    eauto using SJ_CG.knows_neq, knows_def.
  Qed.

  Let local_to_knows_alloc:
    forall cg sj sj' cg' l l' a b x k y d,
    LocalToKnows l cg sj ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces cg' l (ALLOC y d) l' ->
    Knows cg' l' (a, b) ->
    SJ_CG.Reduces sj cg' sj' ->
    SJ_CG.SJ cg k sj ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    handle_all.
    expand H2.
    simpl in *.
    expand H5.
    apply maps_to_inv in H3.
    rewrite MN_Facts.add_mapsto_iff in *.
    destruct H3 as [(?,?)|(?,mt)]. {
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
      simpl_map.
    }
    eauto using SJ_CG.knows_neq.
  Qed.

  Let local_to_knows_write:
    forall cg sj sj' cg' l l' a b x k y d,
    LocalToKnows l cg sj ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces cg' l (WRITE y d) l' ->
    Knows cg' l' (a, b) ->
    SJ_CG.Reduces sj cg' sj' ->
    SJ_CG.SJ cg k sj ->
    DomIncl l (fst cg) ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    rename H5 into Hdom.
    handle_all.
    expand H2.
    simpl in *.
    eauto using SJ_CG.knows_neq, knows_def.
  Qed.

  Let local_to_knows_read:
    forall cg sj sj' cg' l l' a b x k y k' d g g',
    LocalToKnows l cg sj ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces cg' l (READ y d) l' ->
    Knows cg' l' (a, b) ->
    SJ_CG.Reduces sj cg' sj' ->
    SJ_CG.SJ cg k sj ->
    DomIncl l (fst cg) ->
    LastWriteCanJoin g cg sj ->
    SJ_CG.SJ cg' k' sj' ->
    DRF_Check cg' g (READ y d) g' ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    rename H5 into Hdom.
    rename H6 into Hwrite.
    rename H7 into Hsj'.
    rename H8 into Hdrf.
    handle_all.
    expand H2.
    simpl in *.
    apply maps_to_inv in H3.
    expand H5.
    rewrite MN_Facts.add_mapsto_iff in *.
    destruct H3 as [(?,?)|(?,mt)]; subst. {
      subst.
      destruct H0 as [(_,Hx)|(N,_)]; subst. {
        destruct H1 as [?|Hi]. {
          subst.
          expand Hdrf. {
            simpl in *.
            expand H0.
            expand H1.
            simpl_structs.
            expand H10.
            expand H11.
            simpl in *.
            eauto using SJ_CG.knows_def, maps_to_eq, SJ_CG.hb_spec, SJ_CG.can_join_cons.
          }
          (* absurd *)
        }
        simpl in *.
        eapply sj_knows_copy; eauto.
      }
      contradiction N; trivial.
    }
    destruct H0 as [(?,?)|(?,mt')]. {
      subst.
      simpl_map.
    }
    eauto using SJ_CG.knows_neq, knows_def, Locals.local_def.
  Qed.
*)
  Let local_to_knows_future:
    forall cg sj sj' cg' l l' a b x y k ds,
    LocalToKnows l cg sj ->
    CG.Reduces cg (x, CG.FORK y) cg' ->
    Reduces cg' l (FUTURE y ds) l' ->
    Knows cg' l' (a, b) ->
    SJ_CG.Reduces sj cg' sj' ->
    SJ_CG.SJ cg k sj ->
    DomIncl l (fst cg) ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    rename H5 into Hdom.
    handle_all.
    expand H2; simpl in *.
    apply maps_to_inv in H3.
    destruct H3 as [(?,?)|(?,mt)]. {
      subst.
      apply Locals.maps_to_to_in in H10.
      apply Hdom in H10.
      apply node_lt in H10.
      unfold NODE.lt, fresh in *.
      simpl in *.
      omega.
    }
    apply maps_to_inv in mt.
    destruct mt as [(?,?)|(?,mt)]. {
      subst.
      apply Locals.maps_to_to_in in H10.
      apply Hdom in H10.
      apply node_lt in H10.
      unfold NODE.lt, fresh in *.
      simpl in *.
      omega.
    }
    eauto 6 using SJ_CG.knows_neq, knows_def, Locals.local_def.
  Qed.

  Let local_to_knows_force:
    forall cg sj sj' cg' l l' a b x k y d,
    LocalToKnows l cg sj ->
    CG.Reduces cg (x, CG.JOIN y) cg' ->
    Reduces cg' l (FORCE y d) l' ->
    Knows cg' l' (a, b) ->
    SJ_CG.Reduces sj cg' sj' ->
    SJ_CG.SJ cg k sj ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    handle_all.
    expand H2.
    simpl in *.
    expand H5.
    rewrite MN_Facts.add_mapsto_iff in *.
    apply maps_to_inv in H3.
    destruct H3 as [(?,?)|(?,mt)]. {
      subst.
      destruct H0 as [(_,?)|(N,_)]. {
        subst.
        destruct H1 as [|Hi]. {
          subst.
          inversion H4; subst.
          eauto using SJ_CG.knows_append_right, knows_def, Locals.local_def.
        }
        inversion H4; subst.
        eauto using SJ_CG.knows_append_left, knows_def, Locals.local_def.
      }
      contradiction N; trivial.
    }
    destruct H0 as [(?,?)|(?, mt')]. {
      subst.
      apply maps_to_absurd_fresh in mt; contradiction.
    }
    eauto 6 using SJ_CG.knows_neq, knows_def, Locals.local_def.
  Qed.

  Notation local_info := (Locals.local_memory datum).

  Definition memory := (access_history * local_info) % type.

  Lemma local_to_knows_reduces:
    forall cg k sj sj' g g' cg' l l' x o k',
    LocalToKnows l cg sj ->
    SJ_CG.SJ cg k sj ->
    SJ_CG.SJ cg' k' sj' ->
    CG.Reduces cg (event_to_cg (x,o)) cg' ->
    Reduces cg' l o l' ->
    DRF_Check cg' g o g' ->
    SJ_CG.Reduces sj cg' sj' ->
    DomIncl l (fst cg) ->
    LastWriteCanJoin g cg sj ->
    LocalToKnows l' cg' sj'.
  Proof.
    intros.
    unfold LocalToKnows.
    intros (a,b); intros.
    destruct o; simpl in *; eauto.
  Qed.

  Lemma dom_incl_reduces:
    forall m m' cg cg' e,
    DomIncl (snd m) (fst cg) ->
    CG.Reduces cg (event_to_cg e) cg' ->
    Reduces cg' m e m' ->
    DomIncl (snd m') (fst cg').
  Proof.
    intros.
    unfold DomIncl.
    intros.
    destruct e as (x, []); simpl in *; handle_all.
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

  Variable max_write_continue:
    forall {A:Type} x n n' vs es g (v:A) r,
    MapsTo x n vs ->
    LastWrite r n' v g (x :: vs, C (n, fresh vs) :: es) ->
    LastWrite r n' v g (vs, es).

  Let last_write_can_join_continue:
    forall cg sj cg' sj' m m' x r n a,
    LastWriteCanJoin (fst m) cg sj ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces cg' m (x, CONTINUE) m' ->
    SJ_CG.Reduces sj cg' sj' ->
    LastWrite r n (d_task a) (fst m') cg' ->
    SJ_CG.CanJoin n a sj'.
  Proof.
    intros.
    CG.simpl_red.
    expand H1.
    expand H4.
    expand H2.
    simpl in *.
    rename n0 into nx.
    apply SJ_CG.can_join_cons.
    rename es0 into es.
    eauto using max_write_continue.
  Qed.

  Variable hb_irrefl:
    forall cg x,
    ~ HB cg x x.


  Let last_write_knows_continue:
    forall a n t nl vs es sj g b nt (l:Locals.local_memory datum) r,
    NodeOf a n (t :: vs) ->
    LastWriteKnows g (vs, es) sj ->
    MapsTo t nt vs ->
    LastWrite r n (d_task b) g (t :: vs, C (nt, fresh vs) :: es) ->
    MN.MapsTo nt nl l ->
    ~ MN.In (fresh vs) l ->
    SJ_CG.Knows (t :: vs) (SJ_CG.Copy nt :: sj) (a, b).
  Proof.
    intros.
  Admitted.

  (** MOVE OUT *)

  Lemma max_write_to_access:
    forall {A} r (a:access A) ah cg,
    MaxWrite r a ah cg ->
    Access r a ah.
  Proof.
    intros.
    inversion H.
    eauto using access_def.
  Qed.

  (** MOVE OUT *)

  Lemma last_write_to_access:
    forall {A:Type} r (x:A) ah vs es n,
    LastWrite r n x ah (vs, es) ->
    exists a, Access r a ah /\ a_when a = n /\ Write a x.
  Proof.
    intros.
    inversion H.
    eauto using max_write_to_access.
  Qed.

  Definition DomInclAccess {A} (ah:access_history A) (vs:list tid) :=
    forall r a,
    Access r a ah ->
    Node (a_when a) vs.

  Lemma last_write_to_node:
    forall r n {A} (x:A) ah vs es,
    DomInclAccess ah vs ->
    LastWrite r n x ah (vs, es) ->
    Node n vs.
  Proof.
    intros.
    apply last_write_to_access in H0.
    destruct H0 as (a, (?,(?,?))).
    apply H in H0.
    subst; assumption.
  Qed.

  Let last_write_knows_else:
    forall g vs es sj t a tn b n r' k,
    DomInclAccess g vs ->
    SJ_CG.SJ (vs, es) k sj ->
    LastWriteKnows g (vs, es) sj ->
    NodeOf a n (t :: vs) ->
    MapsTo t tn vs ->
    LastWrite r' n (d_task b) g (t :: vs, C (tn, fresh vs) :: es) ->
    SJ_CG.Knows (t :: vs) (SJ_CG.Copy tn :: sj) (a, b).
  Proof.
    intros.
    apply max_write_continue in H4; auto.
    apply node_of_inv in H2.
    destruct H2 as [(?,?)|Hin]. {
      subst.
      apply last_write_to_node in H4; auto.
      simpl_map.
    }
    assert (SJ_CG.Knows vs sj (a, b)) by eauto.
    destruct (tid_eq_dec t a). {
      subst.
      inversion H0.
      eauto using SJ_CG.knows_copy.
    }
    eauto using SJ_CG.knows_cons.
  Qed.

  Let last_write_knows_alloc:
    forall a n t vs es sj d tn l b g r r' tl k,
    LocalToKnows l (vs,es) sj ->
    NodeOf a n (t :: vs) ->
    Locals.MapsTo tn d l ->
    LastWriteKnows g (vs, es) sj ->
    MapsTo t tn vs ->
    MN.MapsTo tn tl l ->
    ~ MN.In (fresh vs) l ->
    ~ MM.In r g ->
    LastWrite r' n (d_task b) 
     (MM.add r ({| a_when := fresh vs; a_what := ALLOC d |} :: nil) g) 
     (t :: vs, C (tn, fresh vs) :: es) ->
    DomInclAccess g vs ->
    SJ_CG.SJ (vs,es) k sj ->
    SJ_CG.Knows (t :: vs) (SJ_CG.Copy tn :: sj) (a, b).
  Proof.
    intros.
    rename H8 into Hdom.
    rename H9 into Hsj.
    apply last_write_inv_alloc in H7.
    destruct H7 as [(?,(?,?))|(?,mt)]. {
      subst.
      apply node_of_inv_key in H0; subst.
      inversion Hsj.
      eauto using SJ_CG.knows_copy, knows_def.
    }
    eauto.
  Qed.

  Let last_write_knows_write:
    forall a n t n' b l sj vs es g d lr r r' k,
    NodeOf a n (t :: vs) ->
    Locals.MapsTo n' d l ->
    Locals.MapsTo n' (d_mem r) l ->
    MapsTo t n' vs ->
    MM.MapsTo r lr g ->
    LastWrite r' n (d_task b)
       (MM.add r ({| a_when := fresh vs; a_what := WRITE d |} :: lr) g)
       (t :: vs, C (n', fresh vs) :: es) ->

    LastWriteKnows g (vs, es) sj ->
    LocalToKnows l (vs, es) sj ->
    DomInclAccess g vs ->
    SJ_CG.SJ (vs, es) k sj ->

    SJ_CG.Knows (t :: vs) (SJ_CG.Copy n' :: sj) (a, b).
  Proof.
    intros.
    rename H5 into Hw.
    rename H6 into Hl.
    rename H7 into Hdom.
    rename H8 into Hsj.
    apply last_write_inv_write in H4; auto.
    destruct H4 as [(?,(?,?))|mt]. {
      subst.
      apply node_of_inv_key in H; subst.
      inversion Hsj.
      eauto using SJ_CG.knows_copy, knows_def.
    }
    eauto.
  Qed.

  Let last_write_knows_read:
    forall r' r'l l a b x nx sj es vs g an r nw k lx d,
    Locals.MapsTo nx (d_mem r') l ->
    LastWrite r' nw d g (vs, es) ->
    NodeOf a an (x :: vs) ->
    DomInclAccess g vs ->
    MN.MapsTo nx lx l ->
    MM.MapsTo r' r'l g ->
    SJ_CG.SJ (vs, es) k sj ->
    LastWriteKnows g (vs, es) sj ->
    LocalToKnows l (vs, es) sj ->
    MapsTo x nx vs ->
    LastWrite r an (d_task b)
       (MM.add r' ({| a_when := fresh vs; a_what := READ datum |} :: r'l) g)
       (x :: vs, C (nx, fresh vs) :: es) ->
    SJ_CG.Knows (x :: vs) (SJ_CG.Copy nx :: sj) (a, b).
  Proof.
    intros.
    apply last_write_inv_read in H9; eauto.
  Qed.

  Let last_write_knows_fork:
    forall l a b x nx sj es vs g an r k lx y args,
    DomInclAccess g vs ->
    SJ_CG.SJ (vs, es) k sj ->
    LastWriteKnows g (vs, es) sj ->
    LocalToKnows l (vs, es) sj ->
    MapsTo x nx vs ->
    MN.MapsTo nx lx l ->
    LastWrite r an (d_task b) g
       (y :: x :: vs, F (nx, fresh (x :: vs)) :: C (nx, fresh vs) :: es) ->
    NodeOf a an (y :: x :: vs) ->
    x <> y ->
    ~ In y vs ->
    Forall (fun d : datum => Locals.MapsTo nx d l) args ->
    ~ MN.In (fresh vs) l ->
    ~ MN.In (fresh (x :: vs)) (MN.add (fresh vs) (d_task y :: lx) l) ->
    SJ_CG.Knows (y :: x :: vs) (SJ_CG.Copy nx :: SJ_CG.Cons y nx :: sj) (a, b).
  Proof.
    intros.
    apply node_of_inv in H6.
    destruct H6 as [(?,?)|Hn]. {
      subst.
  Admitted.

  Lemma last_write_knows:
    forall m cg sj cg' m' sj' e k,
    LastWriteKnows (fst m) cg sj ->
    CG.Reduces cg (event_to_cg e) cg' ->
    Reduces cg' m e m' ->
    SJ_CG.Reduces sj cg' sj' ->

    SJ_CG.SJ cg k sj ->
    LocalToKnows (snd m) cg sj ->
    DomInclAccess (fst m) (fst cg) ->

    LastWriteKnows (fst m') cg' sj'.
  Proof.
    intros.
    unfold LastWriteKnows; intros.
    destruct e as (?,[]); simpl in *; handle_all.
    - eapply last_write_knows_continue with (l:=l); eauto.
    - eapply last_write_knows_alloc; eauto.
    - eauto.
    - eauto.
    - eapply last_write_knows_fork; eauto.
    - clear H9.
      rename es0 into es.
      rename m0 into r.
      rename t into x.
      rename t0 into y.
      rename ny0 into ny.
      rename l0 into lx.
      rename n into an.
      clear nx.
      rename nx0 into nx.
      rename l into args.
      rename l0 into l.
      clear H16.
      clear H8.
  Qed.


  Let last_write_can_join_alloc:
    forall cg sj cg' sj' m m' x r n a d z k,
    LastWriteCanJoin (fst m) cg sj ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces cg' m (x, GLOBAL_ALLOC z d) m' ->
    SJ_CG.Reduces sj cg' sj' ->
    LastWrite r n (d_task a) (fst m') cg' ->
    LocalToKnows (snd m) cg sj ->
    SJ_CG.SJ cg k sj ->
    SJ_CG.CanJoin n a sj'.
  Proof.
    intros.
    rename H4 into Hk.
    rename H5 into Hs.
    handle_all.
    rename n0 into nx.
    rename l0 into lx.
    rename es0 into es.
    destruct (mid_eq_dec r z). {
      subst.
      apply last_write_inv_add in H3.
      destruct H3; subst.
      assert (R: fresh vs = fresh sj). {
        inversion Hs.
        auto using maps_to_length_rw.
      }
      rewrite R.
      apply SJ_CG.can_join_copy.
      assert (Hx : Knows (vs, es) l (x,a)). {
       eauto using knows_def, Locals.local_def.
      }
      eauto.
    }
    apply max_write_continue in H3; auto.
    apply H in H3.
    apply SJ_CG.can_join_cons.
    assumption.
  Qed.

  Lemma last_write_can_join:
    forall m cg sj cg' m' sj' e,
    LastWriteCanJoin (fst m) cg sj ->
    CG.Reduces cg (event_to_cg e) cg' ->
    Reduces cg' m e m' ->
    SJ_CG.Reduces sj cg' sj' ->
    LastWriteCanJoin (fst m') cg' sj'.
  Proof.
    intros.
    unfold LastWriteCanJoin.
    intros r n a; intros.
    destruct e as (x, []); simpl in *.
    - eauto.
    - eauto.
    - 
    - rename m0 into z.
  Qed.
*)

End SR.