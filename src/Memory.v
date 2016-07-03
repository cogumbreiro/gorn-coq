Set Implicit Arguments.

Require Import Coq.Lists.List.

Require Import Tid.
Require Import Lang.
Require Import Mid.
Require Import Shadow.
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


  Definition global_memory := access_history datum.

  Definition memory := (global_memory * (local_memory datum)) % type.

  Definition m_global (m:memory) := fst m.

  Definition m_local (m:memory) := snd m.

  Inductive op :=
  | CONTINUE: op
  | GLOBAL_ALLOC: mid -> datum -> op
  | GLOBAL_WRITE: mid -> datum -> op
  | GLOBAL_READ: mid -> op
  | FUTURE: tid -> list datum -> op
  | FORCE: tid -> datum -> op.

  Definition event := (tid * op) % type.


  Variable cg : computation_graph.

  Inductive Reduces : memory -> event -> memory -> Prop :=
  | reduces_g_read:
    forall g l d n n' (x:tid) y l' g' es nw vs,
    snd cg = C (n, n') :: es ->
    fst cg = x :: vs ->
    (* the reference y is in the locals of task x *)
    Locals.MapsTo n (d_mem y) l ->
    (* the contents of reference y is datum d *)
    Shadow.LastWrite y nw d g (vs,es) ->
    (* and the read is safe (race-free) *)
    HB cg nw n' ->
    (* add datum d to the locals of x *)
    Locals.Reduces l (n', CONS d n) l' ->
    (* update the shared memory to record the read *)
    Shadow.Reduces cg g (y, {| a_when := n'; a_what:=READ datum |}) g' ->
    Reduces (g, l) (x, GLOBAL_READ y) (g', l')

  | reduces_g_write:
    forall g (l:local_memory datum) (x:tid) (y:mid) d n n' g' es,
    (* a global write is a continue in the CG *)
    snd cg = C (n, n') :: es ->
    (* datum d being written is in the locals of task x *)
    Locals.MapsTo n d l ->
    (* the target reference is also in the locals of task x *)
    Locals.MapsTo n (d_mem y) l ->
    (* update the shared memory to record the write of datum d at reference y *)
    Shadow.Reduces cg g (y, {| a_when:=n'; a_what:=WRITE d|}) g' ->
    Reduces (g, l) (x, GLOBAL_WRITE y d) (g', l)

  | reduces_g_alloc:
    forall g l (x:tid) n n' d l' g' y es,
    (* a global alloc is a continue edge in the CG *)
    snd cg = C (n, n') :: es ->
    (* the datum being alloc'ed is a local *)
    Locals.MapsTo n d l ->
    (* update the shared memory with an alloc *)
    Shadow.Reduces cg g (y, {|a_when:=n';a_what:=ALLOC d|}) g' ->
    (* add reference y to the locals of task x *)
    Locals.Reduces l (n', CONS (d_mem y) n) l' ->
    Reduces (g, l) (x, GLOBAL_ALLOC y d) (g', l')

  | reduces_future:
    forall x nx nx' ny ds l g y l' l'' es,
    snd cg = F (nx, ny) :: C (nx, nx') :: es ->
    (* the locals of the new task are copied from the locals of the current task *)
    List.Forall (fun d => Locals.MapsTo nx d l) ds ->
    (* add task y to the locals of x *)
    Locals.Reduces l (nx', CONS (d_task y) nx) l' ->
    (* set the locals of y to be ds *)
    Locals.Reduces l' (ny, NEW ds) l'' ->
    Reduces (g, l) (x, FUTURE y ds) (g, l)

  | reduce_force:
    forall g l nx nx' ny d l' x y es,
    (* CG reduced with a join *)
    snd cg = J (ny,nx') :: C (nx,nx') :: es ->
    (* Datum d is in the locals of y *)
    Locals.MapsTo ny d l ->
    (* Add d to the locals of x *)
    Locals.Reduces l (nx', CONS d nx) l' ->
    Reduces (g, l) (x, FORCE y d) (g, l')

  | reduce_continue:
    forall g l x n n' l' es,
    snd cg = C (n, n') :: es ->
    Locals.Reduces l (n', COPY datum n) l' ->
    Reduces (g, l) (x, CONTINUE) (g, l').

  Inductive Knows (l:local_memory datum) : tid * tid -> Prop :=
  | knows_def:
    forall n x y,
    Node.MapsTo x n (fst cg) ->
    Locals.MapsTo n (d_task y) l ->
    Knows l (x, y).

End Defs.

  Ltac simpl_structs :=
  repeat simpl in *; match goal with
  | [ H2: _ :: _ = _ :: _ |- _ ] => inversion H2; subst; clear H2
  | [ H2:(_,_) = (_,_) |- _ ] => inversion H2; subst; clear H2
  end.

  Ltac simpl_red :=
  match goal with
    | [ H1: Reduces (_::_,_::_) _ (_, CONTINUE) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces (_::_,_::_) _ (_, GLOBAL_ALLOC _ _) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces (_::_,_::_) _ (_, GLOBAL_WRITE _ _) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces (_::_,_::_) _ (_, GLOBAL_READ _) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces (_::_::_,_::_::_) _ (_, FUTURE _ _) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces (_::_,_::_::_) _ (_, FORCE _ _) _ |- _ ] =>
      inversion H1; subst; clear H1
  end;
  simpl_structs.

  Ltac handle_all :=
  try SJ_CG.simpl_red;
  try CG.simpl_red;
  try simpl_red;
  try Locals.simpl_red;
  try Shadow.simpl_red;
  try simpl_structs;
  simpl in *.


Section SR.

  Definition op_to_cg (o:op) : CG.op :=
  match o with
  | CONTINUE => CG.CONTINUE
  | GLOBAL_ALLOC _ _ => CG.CONTINUE
  | GLOBAL_WRITE _ _ => CG.CONTINUE
  | GLOBAL_READ _ => CG.CONTINUE
  | FUTURE x _ => CG.FORK x
  | FORCE x _ => CG.JOIN x
  end.

  Definition event_to_cg (e:event) : CG.event :=
  let (x,o) := e in (x, op_to_cg o).

  Definition LocalToKnows (l:Locals.local_memory datum) cg sj :=
    forall p,
    Knows cg l p ->
    SJ_CG.Knows (fst cg) sj p.

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
    forall cg sj sj' cg' m m' a b x k,
    LocalToKnows (snd m) cg sj ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces cg' m (x, CONTINUE) m' ->
    Knows cg' (snd m') (a, b) ->
    SJ_CG.Reduces sj cg' sj' ->
    SJ_CG.SJ cg k sj ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    SJ_CG.simpl_red.
    simpl_red; Locals.simpl_red; simpl in *.
    expand H2; simpl in *. (* Knows *)
    eauto.
  Qed.

  Let local_to_knows_alloc:
    forall cg sj sj' cg' m m' a b x k y d,
    LocalToKnows (snd m) cg sj ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces cg' m (x, GLOBAL_ALLOC y d) m' ->
    Knows cg' (snd m') (a, b) ->
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

  Definition DomIncl (l:Locals.local_memory datum) (vs:list tid) :=
    forall n,
    MN.In n l ->
    Node n vs.

  Let local_to_knows_write:
    forall cg sj sj' cg' m m' a b x k y d,
    LocalToKnows (snd m) cg sj ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces cg' m (x, GLOBAL_WRITE y d) m' ->
    Knows cg' (snd m') (a, b) ->
    SJ_CG.Reduces sj cg' sj' ->
    SJ_CG.SJ cg k sj ->
    DomIncl (snd m) (fst cg) ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    rename H5 into Hdom.
    handle_all.
    expand H2.
    simpl in *.
    apply maps_to_inv in H3.
    destruct H3 as [(?,?)|(?,mt)]. {
      subst.
      apply Locals.maps_to_to_in in H5.
      apply Hdom in H5.
      simpl_map.
    }
    eauto using SJ_CG.knows_neq, knows_def.
  Qed.

  Definition LastWriteCanJoin (g:access_history datum) cg sj :=
    forall m n x,
    LastWrite m n (d_task x) g cg ->
    SJ_CG.CanJoin n x sj.

  Let local_to_knows_read:
    forall cg sj sj' cg' m m' a b x k y k',
    LocalToKnows (snd m) cg sj ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces cg' m (x, GLOBAL_READ y) m' ->
    Knows cg' (snd m') (a, b) ->
    SJ_CG.Reduces sj cg' sj' ->
    SJ_CG.SJ cg k sj ->
    DomIncl (snd m) (fst cg) ->
    LastWriteCanJoin (fst m) cg sj ->
    SJ_CG.SJ cg' k' sj' ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    rename H5 into Hdom.
    rename H6 into Hwrite.
    rename H7 into Hsj'.
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
          eauto using SJ_CG.knows_def, maps_to_eq, SJ_CG.hb_spec, SJ_CG.can_join_cons.
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

  Let local_to_knows_future:
    forall cg sj sj' cg' m m' a b x y k ds,
    LocalToKnows (snd m) cg sj ->
    CG.Reduces cg (x, CG.FORK y) cg' ->
    Reduces cg' m (x, FUTURE y ds) m' ->
    Knows cg' (snd m') (a, b) ->
    SJ_CG.Reduces sj cg' sj' ->
    SJ_CG.SJ cg k sj ->
    DomIncl (snd m) (fst cg) ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    rename H5 into Hdom.
    handle_all.
    expand H2; simpl in *.
    apply maps_to_inv in H3.
    destruct H3 as [(?,?)|(?,mt)]. {
      subst.
      apply Locals.maps_to_to_in in H14.
      apply Hdom in H14.
      apply node_lt in H14.
      unfold NODE.lt, fresh in *.
      simpl in *.
      omega.
    }
    apply maps_to_inv in mt.
    destruct mt as [(?,?)|(?,mt)]. {
      subst.
      apply Locals.maps_to_to_in in H14.
      apply Hdom in H14.
      apply node_lt in H14.
      unfold NODE.lt, fresh in *.
      simpl in *.
      omega.
    }
    eauto 6 using SJ_CG.knows_neq, knows_def, Locals.local_def.
  Qed.

  Let local_to_knows_force:
    forall cg sj sj' cg' m m' a b x k y d,
    LocalToKnows (snd m) cg sj ->
    CG.Reduces cg (x, CG.JOIN y) cg' ->
    Reduces cg' m (x, FORCE y d) m' ->
    Knows cg' (snd m') (a, b) ->
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

  Lemma local_to_knows_reduces:
    forall cg k sj sj' cg' m m' e k',
    LocalToKnows (snd m) cg sj ->
    SJ_CG.SJ cg k sj ->
    SJ_CG.SJ cg' k' sj' ->
    CG.Reduces cg (event_to_cg e) cg' ->
    Reduces cg' m e m' ->
    SJ_CG.Reduces sj cg' sj' ->
    DomIncl (snd m) (fst cg) ->
    LastWriteCanJoin (fst m) cg sj ->
    LocalToKnows (snd m') cg' sj'.
  Proof.
    intros.
    unfold LocalToKnows.
    intros (a,b); intros.
    destruct e as (x, []); simpl in *.
    - eapply local_to_knows_continue; eauto.
    - eauto.
    - eauto.
    - eauto.
    - eauto.
    - eauto.
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

  Let max_write_add_3:
    forall {A} r (a:access A) r' x g cg,
    MaxWrite r a (MM.add r' x g) cg ->
    r <> r' ->
    MaxWrite r a g cg.
  Proof.
    intros.
    expand H.
    apply MM.add_3 in H1; eauto using max_write_def.
  Qed.

  Let last_write_add_3:  
    forall r n r' {A} (d:A) x g cg,
    LastWrite r n d (MM.add r' x g) cg ->
    r <> r' ->
    LastWrite r n d g cg.
  Proof.
    intros.
    expand H.
    eauto using max_write_add_3, last_write_def.
  Qed.

  Let last_write_inv_add:
    forall {A} r n n' (x y:A) g cg,
    LastWrite r n' y
       (MM.add r ({| a_when := n; a_what := ALLOC x |} :: nil) g) cg ->
     n' = n /\ y = x.
  Proof.
    intros.
    expand H.
    expand H2.
    rewrite MM_Facts.add_mapsto_iff in *.
    destruct H as [(_,?)|(N,_)]. {
      subst.
      destruct H3. {
        subst.
        expand H4.
        clear H5.
        apply H3 in H0; clear H3.
        destruct H0. {
          clear H.
          inversion H1; simpl in *; inversion H.
          auto.
        }
        apply hb_irrefl in H.
        contradiction.
      }
      inversion H.
    }
    contradiction N.
    trivial.
  Qed.

  Definition LastWriteKnows g cg sj :=
    forall m n a b,
    LastWrite m n (d_task b) g cg ->
    NodeOf a n (fst cg) ->
    SJ_CG.Knows (fst cg) sj (a, b).

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

  Lemma max_write_to_access:
    forall {A} r (a:access A) ah cg,
    MaxWrite r a ah cg ->
    Access r a ah.
  Proof.
    intros.
    inversion H.
    eauto using access_def.
  Qed.

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

  Lemma last_write_to_node:
    forall r n {A} (a:A) ah vs es,
    LastWrite r n a ah (vs, es) ->
    exists a, Access r a ah /\ a_when a = n.

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
    LastWrite r n (d_task b) 
     (MM.add r' ({| a_when := fresh vs; a_what := ALLOC d |} :: nil) g) 
     (t :: vs, C (tn, fresh vs) :: es) ->
    SJ_CG.SJ (vs,es) k sj ->
    SJ_CG.Knows (t :: vs) (SJ_CG.Copy tn :: sj) (a, b).
  Proof.
    intros.
    rename H8 into Hsj.
    destruct (mid_eq_dec r r'). {
      subst.
      apply last_write_inv_add in H7.
      destruct H7.
      subst.
      apply node_of_inv_key in H0; subst.
      inversion Hsj.
      eauto using SJ_CG.knows_copy, knows_def.
    }
    apply last_write_add_3 in H7; auto.
    apply max_write_continue in H7; auto.
    apply node_of_inv in H0.
    destruct H0 as [(?,?)|Hin]. {
      subst.
      inversion Hsj.
      eauto using SJ_CG.knows_copy, knows_def.
    }
      inversion Hsj.
      eauto using SJ_CG.knows_cons, knows_def.

      inversion Hsj.
      eauto using SJ_CG.knows_copy.
    auto using SJ_CG.knows_cons.
  Qed.

  Lemma last_write_knows:
    forall m cg sj cg' m' sj' e k,
    LastWriteKnows (fst m) cg sj ->
    CG.Reduces cg (event_to_cg e) cg' ->
    Reduces cg' m e m' ->
    SJ_CG.Reduces sj cg' sj' ->

    SJ_CG.SJ cg k sj ->
    LocalToKnows (snd m) cg sj ->

    LastWriteKnows (fst m') cg' sj'.
  Proof.
    intros.
    unfold LastWriteKnows; intros.
    destruct e as (?,[]); simpl in *; handle_all.
    - eapply last_write_knows_continue with (l:=l); eauto.
    - eapply last_write_knows_alloc; eauto.
     rename m0 into r.
      rename es0 into es.
      rename n0 into tn.
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