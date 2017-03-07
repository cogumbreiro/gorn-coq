Set Implicit Arguments.

Require Import Coq.Lists.List.
Require Import Coq.Program.Tactics.

Require Import Tid.
Require Import Lang.
Require Import Mid.
Require AccessHistory.
Require Import Node.
Require Import CG.
Require SJ_CG.
Require Import Trace.
Require Import Omega.

Module Locals.
Section Defs.
  Variable A:Type.

  Inductive op :=
  | NEW: op
  | COPY : node -> op
  | CONS : A -> node -> op
  | UNION : node -> node -> op.

  Definition task_local := list A.

  Definition local_memory := MN.t task_local.

  Definition empty : local_memory := MN.empty task_local.

  Inductive Reduces (m:local_memory): (node * op) -> local_memory -> Prop :=
  | reduces_new:
    forall n,
    ~ MN.In n m ->
    Reduces m (n, NEW) (MN.add n nil m)
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
  | reduces_union:
    forall n n1 n2 l1 l2,
    MN.MapsTo n1 l1 m ->
    MN.MapsTo n2 l2 m ->
    Reduces m (n, UNION n1 n2) (MN.add n (l1++l2) m).

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

  Lemma maps_to_inv_add:
    forall n n' d (l:local_memory) h,
    MapsTo n d (MN.add n' h l) ->
    (n' = n /\ In d h) \/ (n' <> n /\ MapsTo n d l).
  Proof.
    intros.
    inversion H; subst; clear H.
    rewrite MN_Facts.add_mapsto_iff in *.
    destruct H0 as [(?,?)|(?,?)]. {
      subst.
      auto.
    }
    eauto using local_def.
  Qed.
End Defs.

  Ltac simpl_red :=
    repeat match goal with
    | [ H1: Reduces _ (_, NEW _) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces _ (_, COPY _ _) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces _ (_, CONS _ _) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces _ (_, UNION _ _ _) _ |- _ ] =>
      inversion H1; subst; clear H1
    end.

End Locals.

Section Defs.
  Require Import Trace.

  Import Locals.

  Inductive Mem : Trace.trace -> computation_graph ->  local_memory datum -> Prop :=

  | mem_nil:
    Mem nil (nil, nil) (Locals.empty datum)

  | mem_init:
    forall l l' x vs es t,
    Mem t (vs, es) l ->
    CG.T.CG ((x,INIT)::t) (x::vs,es) ->
    (* Add d to the locals of x *)
    Locals.Reduces l (fresh vs, NEW datum) l' ->
    Mem ((x, INIT)::t) (x::vs, es) l'

  | mem_alloc:
    forall l n n' d l' r es t x vs,
    Mem t (vs, es) l ->
    (* a global alloc is a continue edge in the CG *)
    CG.T.CG ((x,(MEM r ALLOC))::t) (x::vs, C (n, n') :: es) ->
    (* the datum being alloc'ed is a local *)
    Locals.MapsTo n d l ->
    (* add reference y to the locals of task x *)
    Locals.Reduces l (n', CONS (d_mem r) n) l' ->
    Mem ((x,(MEM r ALLOC))::t) (x::vs, C (n, n') :: es) l'

  | reduces_read:
    forall l d n n' r l' es vs t x,
    Mem t (vs,es) l ->
    (* a read is a continue edge in the CG *)
    CG.T.CG ((x,(MEM r (READ d)))::t) (x::vs, C (n, n') :: es) ->
    (* the reference y is in the locals of task x *)
    Locals.MapsTo n (d_mem r) l ->
    (* add datum d to the locals of x *)
    Locals.Reduces l (n', CONS d n) l' ->
    Mem ((x,(MEM r (READ d)))::t) (x::vs, C (n, n') :: es) l'

  | mem_write:
    forall l r d n n' es l' vs t x,
    Mem t (vs,es) l ->
    (* a global write is a continue in the CG *)
    CG.T.CG ((x,(MEM r (WRITE d)))::t) (x::vs, C (n, n') :: es) ->
    (* datum d being written is in the locals of task x *)
    Locals.MapsTo n d l ->
    (* the target reference is also in the locals of task x *)
    Locals.MapsTo n (d_mem r) l ->
    Locals.Reduces l (n', COPY datum n) l' ->
    Mem ((x,(MEM r (WRITE d)))::t) (x::vs, C (n, n') :: es) l'

  | mem_future:
    forall x nx nx' ny ds l y l' l'' es t vs,
    Mem t (vs,es) l ->
    CG.T.CG ((x,FUTURE y)::t) (y::x::vs, F (nx, ny) :: C (nx, nx') :: es) ->
    (* the locals of the new task are copied from the locals of the current task *)
    List.Forall (fun d => Locals.MapsTo nx d l) ds ->
    (* add task y to the locals of x *)
    Locals.Reduces l (nx', CONS (d_task y) nx) l' ->
    (* set the locals of y to be ds *)
    Locals.Reduces l' (ny, COPY datum nx) l'' ->
    Mem ((x,FUTURE y)::t) (y::x::vs, F (nx, ny) :: C (nx, nx') :: es) l''

  | mem_force:
    forall l nx nx' ny d l' vs es t x y,
    Mem t (vs,es) l ->
    (* CG reduced with a join *)
    CG.T.CG ((x,FORCE y)::t) (x::vs, J (ny,nx') :: C (nx,nx') :: es) ->
    (* Datum d is in the locals of y *)
    Locals.MapsTo ny d l ->
    (* Task y is in the local memory of nx *)
    Locals.MapsTo nx (d_task y) l ->
    (* Add d to the locals of x *)
    Locals.Reduces l (nx', UNION datum nx ny) l' ->
    Mem ((x,FORCE y)::t) (x::vs, J (ny,nx') :: C (nx,nx') :: es) l'.

  Inductive LocalKnows (cg:computation_graph) (l:local_memory datum) : tid * tid -> Prop :=
  | local_knows_def:
    forall n x y,
    TaskOf n x (fst cg) ->
    Locals.MapsTo n (d_task y) l ->
    LocalKnows cg l (x, y).

End Defs.

  Ltac simpl_structs :=
  repeat simpl in *; match goal with
  | [ H2: ?x = ?x |- _ ] => clear H2
  | [ H2: _ :: _ = _ :: _ |- _ ] => inversion H2; subst; clear H2
  | [ H2:(_,_) = (_,_) |- _ ] => inversion H2; subst; clear H2
  | [ H2: Some _ = Some _ |- _ ] => inversion H2; subst; clear H2
  | [ H1: ?P, H2: ?P |- _ ] => clear P
  end.
(*
  Ltac simpl_red :=
  match goal with
    | [ H1: Reduces (_::_,_::_) _ CONTINUE _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces (_::_,_::_) _ (MEM _ ALLOC) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces (_::_,_::_) _ (MEM _ (WRITE _)) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces (_::_,_::_) _ (MEM _ (READ _)) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces (_::_::_,_::_::_) _ (FUTURE _) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces (_::_,_::_::_) _ (FORCE _) _ |- _ ] =>
      inversion H1; subst; clear H1
    | [ H1: Reduces (_::_,_) _ INIT _ |- _ ] =>
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

*)
Section SR.
(*
  Definition op_to_cg (o:op) : CG.op :=
  match o with
  | INIT => CG.INIT
  | MEM _ _ => CG.CONTINUE
  | FUTURE x => CG.FORK x
  | FORCE x => CG.JOIN x
  end.

  Definition event_to_cg (e:event) : CG.event :=
  let (x,o) := e in (x, op_to_cg o).
*)
  Definition LocalToKnows (l:Locals.local_memory datum) cg sj :=
    forall p,
    LocalKnows cg l p ->
    SJ_CG.Knows (fst cg) sj p.

  Definition LastWriteKnows (cg:computation_graph) (g:AccessHistory.T.cg_access_history) l :=
    forall x y n h r,
    MM.MapsTo r h g ->
    AccessHistory.LastWrite (HB (snd cg)) (n, Some (d_task y)) h ->
    TaskOf n x (fst cg) ->
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

  Section DomIncl.

    Let DomIncl (l:Locals.local_memory datum) (vs:list tid) :=
      forall n,
      MN.In n l ->
      Node n vs.

    Let mem_to_dom_incl:
      forall t l cg,
      Mem t cg l ->
      DomIncl l (fst cg).
    Proof.
      induction t; intros. {
        inversion H; subst; clear H.
        unfold DomIncl; intros.
        rewrite MN_Facts.empty_in_iff in *.
        contradiction.
      }
      unfold DomIncl in *; inversion H; subst; clear H; intros;
      match goal with
      [ H: (T.CG _) _ |- _] => inversion H; subst; clear H
      end;
      Locals.simpl_red; simpl_node;
      assert (Hx := IHt _ _ H2);
      try (rewrite MN_Facts.add_in_iff in *);
      try (
        destruct H; try (
          subst; simpl;
          auto using node_eq
        );
        simpl; auto using node_cons
      ).
      rewrite MN_Facts.add_mapsto_iff in H3.
      destruct H3 as [(?,?)|(?,mt)]. {
        subst.
        simpl_node.
      }
      assert (l1 = l) by eauto using MN_Facts.MapsTo_fun; subst.
      rewrite MN_Facts.add_in_iff in *.
      destruct H. {
        subst.
        auto using node_eq, node_cons.
      }
      eauto using node_cons.
    Qed.

    Lemma mem_in_to_node:
      forall t l vs es n,
      Mem t (vs,es) l ->
      MN.In n l ->
      Node n vs.
    Proof.
      intros.
      apply mem_to_dom_incl in H.
      apply H in H0.
      auto.
    Qed.
  End DomIncl.
(*
  Section LastWriteCanJoin.
    Import AccessHistory.
    Import AccessHistory.T.

    Let LastWriteCanJoin (cg:computation_graph) sj (ah:cg_access_history) :=
      forall x a h r,
      MM.MapsTo r h ah ->
      LastWrite (HB (snd cg)) a h ->
      a_what a = Some (Trace.d_task x) ->
      SJ_CG.CanJoin (a_when a) x sj.

    Ltac do_simpl :=
    match goal with
    | [ H: DRF_Reduces ((_, (_, _)) :: _) _ (_, (READ, _)) _ |- _ ] =>
      inversion H; subst; clear H;
      match goal with
      [ H: ((_, (_, _)) :: _) = ((_, (_, _)) :: _) |- _ ] =>
      inversion H; subst; clear H
      end
    | [ H: DRF_Reduces ((_, (_, _)) :: _) _ (_, (WRITE, _)) _ |- _ ] =>
      inversion H; subst; clear H;
      match goal with
      [ H: ((_, (_, _)) :: _) = ((_, (_, _)) :: _) |- _ ] =>
      inversion H; subst; clear H
      end
    | [ H: Add (HB ((_,(_, _)) :: _)) _ (_, _, (READ, _)) _ |- _ ] =>
      inversion H; subst; clear H
    | [ H: Add (HB ((_,(_, _)) :: _)) _ (_, _, (WRITE, _)) _ |- _ ] =>
      inversion H; subst; clear H
    end.

    Ltac simpl_red := repeat do_simpl.

    Let mem_last_write_can_join_read:
      forall r h ah ah' a n sj x vs es m d t y,
      MM.MapsTo r h ah' ->
      LastWrite (HB (C (n, fresh vs) :: es)) a h ->
      a_what a = Some (d_task x) ->
      DRF_Reduces (C (n, fresh vs) :: es) ah (m, (READ, d)) ah' ->
      LastWriteCanJoin (vs, es) sj ah ->
      DRF t (vs, es) ah ->
      DRF ((y, MEM m (Trace.READ d)) :: t) (y :: vs, C (n, fresh vs) :: es)
         ah' ->
       SJ_CG.CanJoin (a_when a) x (SJ_CG.Copy n :: sj).
    Proof.
      intros.
      unfold LastWriteCanJoin in *.
      simpl_red.
      rewrite MM_Facts.add_mapsto_iff in *.
      destruct H as [(?,?)|(?,?)]; subst;
      eauto using
        SJ_CG.can_join_cons,
        last_write_inv_cons_read,
        last_write_inv_c.
    Qed.

    Lemma mem_last_write_can_join:
      forall t cg ah sj l,
      DRF t cg ah ->
      SJ_CG.SJ (map CG.T.event_to_cg t) cg sj ->
      Mem t cg l ->
      LastWriteCanJoin cg sj ah.
    Proof.
      induction t; intros. {
        inversion H0; subst; clear H0.
        inversion H; subst; clear H.
        unfold LastWriteCanJoin.
        intros.
        unfold empty in *.
        rewrite MM_Facts.empty_mapsto_iff in *.
        contradiction.
      }
      rename H1 into Hmem.
      unfold LastWriteCanJoin; intros.
      rename H2 into Hlw.
      inversion H; subst; rename H into Hdrf. {
        (* op_to_ah _ = Some _ *)
        destruct o; simpl in *; inversion H7; subst; clear H7.
        inversion H6; subst; clear H6; simpl_node. (* CG *)
        assert (cg0 = (vs0, es0)) by
          eauto using drf_to_cg, cg_fun; subst.
        inversion H0; subst; clear H0. (* SJ *)
        clear H15 (* CG *).
        rename sj0 into sj.
        rename vs0 into vs.
        rename es0 into es.
        assert (cg = (vs,es)) by eauto using SJ_CG.sj_to_cg, cg_fun; subst.
        rename ah into ah'.
        rename ah0 into ah.
        rename a0 into a.
        rename prev into n.
        rename x0 into y.
        destruct m0; simpl in *; inversion H2; subst; clear H2;
        inversion Hmem; subst; clear Hmem;
        assert (Hlwcj: LastWriteCanJoin (vs,es) sj ah) by eauto. { (* match _ with *)
          eauto.
        }
        clear H16 H9.
        simpl_red;
        rewrite MM_Facts.add_mapsto_iff in *;
        destruct H1 as [(?,?)|(?,?)]; subst.
        - clear H16.
          apply last_write_inv_cons_nil in Hlw.
          subst; simpl in *; subst.
          inversion H3; subst; clear H3.
          assert (R: fresh vs = fresh sj). {
            eauto using SJ_CG.sj_to_length_0, maps_to_length_rw.
          }
          rewrite R; clear R.
          apply SJ_CG.can_join_copy.
          
        -
        

        eapply last_write_inv_c with (r:=r) in Hlw; eauto.
        eapply Hlwcj with (x:=x) in Hlw; eauto.
        eauto using SJ_CG.can_join_cons.
      }
    Qed.
  End LastWriteCanJoin.
*)
  Section MemCG.
    Lemma mem_to_cg:
      forall t cg l,
      Mem t cg l ->
      CG.T.CG t cg.
    Proof.
      induction t; intros. {
        inversion H; subst; clear H.
        auto using CG.cg_nil.
      }
      inversion H; subst; clear H;
      auto using CG.cg_init, CG.cg_continue, CG.cg_fork, CG.cg_join.
    Qed.
  End MemCG.

  Section LocalToKnows.
    Ltac handle_all := 
      simpl in *;
      SJ_CG.do_simpl;
      Locals.simpl_red;
      CG.simpl_red.

    Lemma local_knows_inv_add:
      forall x vs n es h l a b,
      LocalKnows (x :: vs, C (n, fresh vs) :: es) (MN.add (fresh vs) h l) (a, b) ->
      (a = x /\ In (d_task b) h) \/
      MN.In (fresh vs) l \/
      LocalKnows (vs, es) l (a,b).
    Proof.
      intros.
      inversion H; subst; clear H; simpl in *.
      apply task_of_inv in H2.
      apply Locals.maps_to_inv_add in H3.
      destruct H2 as [(?,?)|?]. {
        destruct H3 as [(?,?)|(?,?)]; subst; eauto using Locals.maps_to_to_in.
      }
      destruct H3 as [(?,?)|(?,?)]. {
        subst.
        simpl_node.
      }
      eauto using local_knows_def.
    Qed.

    Lemma local_knows_inv_init:
      forall x vs es l p,
      LocalKnows (x :: vs, es) (MN.add (fresh vs) nil l) p ->
      MN.In (fresh vs) l \/ LocalKnows (vs, es) l p.
    Proof.
      intros.
      inversion H; subst; clear H.
      apply Locals.maps_to_inv_add in H1.
      apply task_of_inv in H0.
      simpl in *.
      destruct H1 as [(?,?)|(?,?)]. {
        contradiction.
      }
      destruct H0 as [(?,?)|?]. {
        subst.
        apply Locals.maps_to_to_in in H1.
        auto.
      }
      eauto using local_knows_def.
    Qed.

    Lemma local_knows_inv_alloc:
      forall x vs n es h a b l r,
      LocalKnows
        (x :: vs, C (n, fresh vs) :: es)
        (MN.add (fresh vs) (d_mem r :: h) l)
        (a,b) ->
      MN.MapsTo n h l ->
      MapsTo x n vs ->
      (a = x /\ LocalKnows (vs, es) l (a,b))
      \/ 
      MN.In (fresh vs) l
      \/
      LocalKnows (vs, es) l (a,b).
    Proof.
      intros.
      inversion H; subst; clear H.
      simpl in *.
      apply task_of_inv in H4.
      apply Locals.maps_to_inv_add in H5.
      destruct H5 as [(?,?)|(?,?)]. {
        destruct H4 as [(?,?)|?]. {
          subst.
          inversion H2. {
            inversion H3.
          }
          apply maps_to_to_task_of in H1.
          left.
          split; auto.
          apply local_knows_def with (n:=n); simpl;
          eauto using maps_to_to_task_of, Locals.local_def.
        }
        subst.
        simpl_node.
      }
      destruct H4 as [(?,?)|?]. {
        subst.
        eauto using Locals.maps_to_to_in.
      }
      eauto using local_knows_def.
    Qed.

    Lemma local_knows_inv_read:
      forall x vs n es d h l a b,
      LocalKnows (x :: vs, C (n, fresh vs) :: es)
        (MN.add (fresh vs) (d :: h) l) (a,b) ->
      (a = x /\ In (d_task b) (d :: h)) \/
      MN.In (fresh vs) l \/
      LocalKnows (vs, es) l (a,b).
    Proof.
      intros.
      inversion H; subst; clear H; simpl in *.
      apply task_of_inv in H2.
      apply Locals.maps_to_inv_add in H3.
      destruct H2 as [(?,?)|?]. {
        destruct H3 as [(?,?)|(?,?)]; subst; eauto using Locals.maps_to_to_in.
      }
      destruct H3 as [(?,?)|(?,?)]. {
        subst.
        simpl_node.
      }
      eauto using local_knows_def.
    Qed.

    Let local_to_knows_init:
      forall x vs es sj l l' t,
      SJ_CG.SJ (map T.event_to_cg ((x, INIT) :: t)) (x :: vs, es) (SJ_CG.Nil :: sj) ->
      Mem t (vs, es) l ->
      LocalToKnows l (vs, es) sj ->
      Locals.Reduces l (fresh vs, Locals.NEW datum) l' ->
      LocalToKnows l' (x :: vs, es) (SJ_CG.Nil :: sj).
    Proof.
      intros.
      handle_all.
      assert (cg = (vs,es)) by eauto using SJ_CG.sj_cg_fun; subst;
      clear H5.
      unfold LocalToKnows; intros.
      apply local_knows_inv_init in H.
      destruct H as [H|H]. {
        eapply mem_in_to_node in H; eauto.
        simpl_node.
      }
      apply H1 in H.
      simpl in *.
      destruct p.
      auto using SJ_CG.knows_init.
    Qed.

    Let mem_sj_to_cg_fun:
      forall t cg l cg' sj,
      Mem t cg l ->
      SJ_CG.SJ (map T.event_to_cg t) cg' sj ->
      cg = cg'.
    Proof.
      intros.
      apply mem_to_cg in H;
      apply SJ_CG.sj_to_cg in H0;
      eauto using cg_fun.
    Qed.


    Let LastWriteCanJoin (cg:computation_graph) sj (ah:AccessHistory.T.cg_access_history) :=
      forall x a h r,
      MM.MapsTo r h ah ->
      AccessHistory.LastWrite (HB (snd cg)) a h ->
      AccessHistory.a_what a = Some (Trace.d_task x) ->
      SJ_CG.CanJoin (AccessHistory.a_when a) x sj.

    Let local_to_knows_alloc:
      forall x vs es sj l l' t n n' d r,
      SJ_CG.SJ (map T.event_to_cg ((x, MEM r ALLOC) :: t))
       (x :: vs, C (n, n') :: es) (SJ_CG.Copy n :: sj) ->
      Mem t (vs, es) l ->
      LocalToKnows l (vs, es) sj ->
      Locals.Reduces l (n', Locals.CONS (d_mem r) n) l' ->
      Locals.MapsTo n d l ->
      LocalToKnows l' (x :: vs, C (n, n') :: es) (SJ_CG.Copy n :: sj).
    Proof.
      intros.
      handle_all.
      assert (cg=(vs,es)). {
        apply SJ_CG.sj_to_cg in H7.
        eauto using cg_fun.
      }
      subst.
      rename l0 into h.
      clear H6. (* CG *)
      unfold LocalToKnows in *; intros.
      destruct p as (a,b).
      apply local_knows_inv_alloc in H; auto.
      destruct H as [(?,?)|[?|?]].
      - subst.
        eapply SJ_CG.knows_copy; eauto using SJ_CG.sj_to_length_0.
      - eapply mem_in_to_node in H; eauto.
        simpl_node.
      - destruct (tid_eq_dec x a). {
          subst.
          eapply SJ_CG.knows_copy; eauto using SJ_CG.sj_to_length_0.
        }
        eauto using SJ_CG.knows_cons.
    Qed.

    Let local_to_knows_read:
      forall x r d t sj es vs n n' l l' ah ah',
      AccessHistory.T.DRF ((x, MEM r (READ d)) :: t)
             (x :: vs, C (n, n') :: es) ah ->
      SJ_CG.SJ (map T.event_to_cg ((x, MEM r (READ d)) :: t))
             (x :: vs, C (n, n') :: es) (SJ_CG.Copy n :: sj) ->
      Mem t (vs, es) l ->
      Locals.MapsTo n (d_mem r) l ->
      Locals.Reduces l (n', Locals.CONS d n) l' ->
      LastWriteCanJoin (vs, es) sj ah' ->
      AccessHistory.T.DRF t (vs, es) ah' ->
      LocalToKnows l (vs, es) sj ->
      LocalToKnows l' (x :: vs, C (n, n') :: es) (SJ_CG.Copy n :: sj).
    Proof.
      intros.
      rename H4 into Hcj.
      rename H5 into Hdrf0.
      rename H6 into Hltk.
      inversion H; subst; rename H into Hdrf;
      simpl in *; inversion H12 (* op_to_ah _ = Some _ *);
      subst; clear H12 H11 (* CG *).
      handle_all.
      assert (cg0=(vs,es)). {
        apply SJ_CG.sj_to_cg in H6.
        eauto using cg_fun.
      }
      assert (cg = (vs,es)). {
        apply AccessHistory.T.drf_to_cg in H9.
        eauto using cg_fun.
      }
      subst.
      clear H5. (* CG *)
      rename l0 into h.
      unfold LocalToKnows in *; intros.
      destruct p as (a,b).
      apply local_knows_inv_read in H.
      assert (ah0 = ah') by eauto using AccessHistory.T.drf_fun; subst.
      destruct H as [(?,Hi)|[N|Hlk]].
      - subst.
        destruct Hi. {
          (** this is the crucial step of the proof *)
          (* d_task b = d *)
          subst.
          assert (Hdrf1 := Hdrf).
          eapply AccessHistory.T.drf_check_inv_read_last_write with (x:=x) in Hdrf; eauto.
          destruct Hdrf as (h', (a, (mt, (Hw, (?,?))))).
          eapply SJ_CG.knows_def; eauto using maps_to_eq.
          assert (R: fresh vs = fresh sj). {
            eauto using SJ_CG.sj_to_length_0, maps_to_length_rw.
          }
          rewrite R.
          apply SJ_CG.can_join_copy.
          eapply CG.hb_inv_continue_1 in H0; eauto. {
            destruct H0; subst;
            unfold LastWriteCanJoin in *;
            eapply Hcj with (r:=r) in Hw; eauto using SJ_CG.hb_spec.
          }
          apply AccessHistory.T.drf_to_cg in Hdrf1; simpl in *.
          eauto.
        }
        eapply SJ_CG.knows_copy; eauto using SJ_CG.sj_to_length_0.
    - contradiction.
    - destruct (tid_eq_dec x a). {
        subst.
        eapply SJ_CG.knows_copy; eauto using SJ_CG.sj_to_length_0.
      }
      eauto using SJ_CG.knows_cons.
    Qed.

    Let last_write_can_join_init:
      forall vs es ah x sj,
      LastWriteCanJoin (vs, es) sj ah ->
      LastWriteCanJoin (x :: vs, es) (SJ_CG.Nil :: sj) ah.
    Proof.
      unfold LastWriteCanJoin; intros.
      simpl in *.
      eauto using SJ_CG.can_join_cons.
    Qed.

    Let last_write_can_join_continue:
      forall vs es sj ah n x t o,
      AccessHistory.T.DRF t (vs, es) ah ->
      AccessHistory.T.DRF ((x, o) :: t) (x :: vs, C (n, fresh vs) :: es) ah ->
      LastWriteCanJoin (vs, es) sj ah ->
      LastWriteCanJoin (x :: vs, C (n, fresh vs) :: es) (SJ_CG.Copy n :: sj) ah.
    Proof.
      unfold LastWriteCanJoin; intros.
      simpl in *.
      eapply AccessHistory.T.last_write_inv_c in H3; eauto.
      eauto using SJ_CG.can_join_cons.
    Qed.

    Let last_write_can_join_read:
      forall vs es sj ah ah' x n r d t,
      AccessHistory.T.DRF t (vs,es) ah ->
      AccessHistory.T.DRF ((x,Trace.MEM r (Trace.READ d))::t) (x::vs,C (n, fresh vs) :: es) ah' ->
      LastWriteCanJoin (vs, es) sj ah ->
      AccessHistory.Add (HB (C (n, fresh vs) :: es)) ah
             (r, fresh vs, (AccessHistory.READ, d)) ah' ->
      LastWriteCanJoin (x :: vs, C (n, fresh vs) :: es) (SJ_CG.Copy n :: sj) ah'.
    Proof.
      intros.
      inversion H2; subst; clear H2.
      simpl in *.
      unfold LastWriteCanJoin; intros.
      rewrite MM_Facts.add_mapsto_iff in *.
      destruct H2 as [(?,Hi)|(?,?)];
      unfold LastWriteCanJoin in *.
      - simpl in *.
        subst.
        apply AccessHistory.last_write_inv_cons_read in H3.
        apply AccessHistory.T.drf_to_cg in H0.
        eapply AccessHistory.T.last_write_inv_hb in H10; eauto.
        eapply AccessHistory.T.last_write_inv_hb in H3; eauto.
        assert (a = (n', Some d))
        by eauto using AccessHistory.T.drf_last_write_fun; subst; simpl in *.
        inversion H4; subst; clear H4.
        eapply H1 with (x:=x0) in H3; simpl; eauto.
        auto using SJ_CG.can_join_cons.
      - simpl in*.
        apply AccessHistory.T.drf_to_cg in H0.
        eapply AccessHistory.T.last_write_inv_hb in H3; eauto.
        eauto using SJ_CG.can_join_cons.
    Qed.

    Let local_to_knows_write:
      forall x vs es sj l l' t n d r,
      SJ_CG.SJ (map T.event_to_cg ((x, MEM r (WRITE d)) :: t))
        (x :: vs, C (n, fresh vs) :: es) (SJ_CG.Copy n :: sj) ->
      Mem t (vs, es) l ->
      LocalToKnows l (vs, es) sj ->
      Locals.Reduces l (fresh vs, Locals.COPY datum n) l' ->
      LocalToKnows l' (x :: vs, C (n, fresh vs) :: es) (SJ_CG.Copy n :: sj).
    Proof.
      intros.
      handle_all.
      assert (cg = (vs,es)) by eauto using SJ_CG.sj_cg_fun; subst;
      clear H8 (* CG *).
      unfold LocalToKnows; intros.
      rename l0 into h.
      destruct p as (a,b).
      apply local_knows_inv_add in H.
      destruct H as [(?,H)|[H|H]].
      - subst.
        simpl.
        eapply SJ_CG.knows_copy; eauto using SJ_CG.sj_to_length_0.
      - contradiction.
      - destruct (tid_eq_dec a x). {
          subst.
          eapply SJ_CG.knows_copy; eauto using SJ_CG.sj_to_length_0.
        }
        apply SJ_CG.knows_cons; auto.
    Qed.

    Let last_write_can_join_write:
      forall vs es sj ah ah' x n r d t l,
      AccessHistory.T.DRF t (vs,es) ah ->
      AccessHistory.T.DRF ((x,Trace.MEM r (Trace.WRITE d))::t) (x::vs,C (n, fresh vs) :: es) ah' ->
      LastWriteCanJoin (vs, es) sj ah ->
      AccessHistory.Add (HB (C (n, fresh vs) :: es)) ah
             (r, fresh vs, (AccessHistory.WRITE, d)) ah' ->
      SJ_CG.SJ (map T.event_to_cg ((x, MEM r (WRITE d)) :: t))
        (x :: vs, C (n, fresh vs) :: es) (SJ_CG.Copy n :: sj) ->
      LocalToKnows l (vs, es) sj ->
      Locals.MapsTo n d l ->
      MapsTo x n vs ->
      LastWriteCanJoin (x :: vs, C (n, fresh vs) :: es) (SJ_CG.Copy n :: sj) ah'.
    Proof.
      intros.
      rename H3 into Hsj.
      rename H4 into Hlk.
      rename H5 into Hr.
      rename H6 into Hmt.
      unfold LastWriteCanJoin; intros.
      eapply AccessHistory.T.last_write_inv_write in H4; eauto.
      destruct H4 as [(?,(?,(?,?)))|[(?,(?,?))|(?,(?,(l',(?,?))))]];
      subst; simpl in *;
      eauto using SJ_CG.can_join_cons. (* take care of the inductive case *)
      - (* first write *)
        inversion H5; subst; clear H5. (* Some _ = Some (d_task _ ) *)
        assert (R: fresh vs = fresh sj). {
          inversion Hsj; subst.
          inversion H13; subst; clear H13. (* CG *)
          assert (cg = (vs, es)) by eauto using SJ_CG.sj_to_cg, cg_fun.
          subst.
          eauto using SJ_CG.sj_to_length_0, maps_to_length_rw.
        }
        rewrite R.
        (* Task x is writing x0, and we know from this rule that x0 is in
           the local info. But from the local-to-knows property, then
           x knows x0. *)
        apply SJ_CG.can_join_copy.
        unfold LocalToKnows in *.
        assert (Hlk': LocalKnows (vs,es) l (x, x0)). {
          apply local_knows_def with (n:=n); auto using maps_to_to_task_of.
        }
        apply Hlk in Hlk'.
        (* If x knows x0 and x mapsto n, then n can join with x0. *)
        inversion Hlk'; subst; simpl in *; simpl_node.
        assumption.
      - (* update write *)
        subst.
        simpl in *.
        (* a_what _ = Some (d_task _) *)
        inversion H5; subst; clear H5.
        assert (R: fresh vs = fresh sj). {
          inversion Hsj; subst.
          inversion H13; subst; clear H13. (* CG *)
          assert (cg = (vs, es)) by eauto using SJ_CG.sj_to_cg, cg_fun.
          subst.
          eauto using SJ_CG.sj_to_length_0, maps_to_length_rw.
        }
        rewrite R.
        (* Task x is writing x0, and we know from this rule that x0 is in
           the local info. But from the local-to-knows property, then
           x knows x0. *)
        apply SJ_CG.can_join_copy.
        unfold LocalToKnows in *.
        assert (Hlk': LocalKnows (vs,es) l (x, x0)). {
          apply local_knows_def with (n:=n); auto using maps_to_to_task_of.
        }
        apply Hlk in Hlk'.
        (* If x knows x0 and x mapsto n, then n can join with x0. *)
        inversion Hlk'; subst; simpl in *; simpl_node.
        assumption.
    Qed.

    Let mem_local_to_knows:
      forall t l cg sj ah,
      Mem t cg l ->
      AccessHistory.T.DRF t cg ah ->
      SJ_CG.SJ (map CG.T.event_to_cg t) cg sj ->
      LocalToKnows l cg sj /\ LastWriteCanJoin cg sj ah.
    Proof.
      induction t; intros. {
        inversion H; subst; clear H.
        split. {
          unfold LocalToKnows; intros.
          inversion H; simpl in *.
          inversion H2.
        }
        unfold LastWriteCanJoin; intros.
        inversion H0; subst.
        unfold AccessHistory.empty in *.
        rewrite MM_Facts.empty_mapsto_iff in *.
        contradiction.
      }
      inversion H; subst; clear H; inversion H1; subst;
      try (assert ((vs,es) = cg) by eauto using mem_sj_to_cg_fun;subst);
      try (rename sj0 into sj);
      try (rename l into l');
      try (rename l0 into l);
      repeat match goal with
      | [ H: CG _ _ |- _ ] => clear H
      end;
      assert (Hcg := H1);
      assert (Hdrf := H0);
      apply SJ_CG.sj_to_cg in H1; inversion H1; subst; simpl_node.
      - apply AccessHistory.T.drf_inv_init in H0.
        assert (Hx:=IHt _ _ _ _ H4 H0 H3).
        destruct Hx as (?,?).
        split; auto. {
          eapply local_to_knows_init; eauto.
        }
      - apply AccessHistory.T.drf_inv_alloc in H0.
        assert (Hx:=IHt _ _ _ _ H4 H0 H12).
        destruct Hx as (?,?).
        split; auto. {
          eapply local_to_knows_alloc; eauto.
        }
        eapply last_write_can_join_continue; eauto.
      - apply AccessHistory.T.drf_inv_read in H0.
        destruct H0 as (ah', (Hdrf',Ha)).
        assert (Hx:=IHt _ _ _ _ H4 Hdrf' H12).
        destruct Hx as (?,?).
        eauto.
      - apply AccessHistory.T.drf_inv_write in H0.
        destruct H0 as (ah', (Hdrf',Ha)).
        assert (Hx:=IHt _ _ _ _ H4 Hdrf' H13 (* SJ_CG.SJ (vs,es) *)).
        destruct Hx as (?,?).
        split;
          eauto using local_to_knows_write.
      - 
    Qed.
(*

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
*)

  (**
    Show that the local-knowledge contains
    SIF (ALLOC).
    *)

  Let local_to_knows_alloc:
    forall cg sj sj' cg' l l' a b x k y,
    LocalToKnows l cg sj ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces cg' l (MEM y ALLOC) l' ->
    LocalKnows cg' l' (a, b) ->
    SJ_CG.Reduces sj (x, CG.CONTINUE) cg' sj' ->
    SJ_CG.SJ cg k sj ->
    length (fst cg) = length sj ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    rename H5 into Heq.
    handle_all.
    expand H2.
    simpl in *.
    expand H7.
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

  (**
    Show that the local-knowledge contains
    SIF (WRITE).
    *)

  Let local_to_knows_write:
    forall cg sj sj' cg' l l' a b x k y d,
    LocalToKnows l cg sj ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces cg' l (MEM y (WRITE d)) l' ->
    LocalKnows cg' l' (a, b) ->
    SJ_CG.Reduces sj (x, CG.CONTINUE) cg' sj' ->
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

  (**
    Show that the local-knowledge contains
    SIF (READ).
    *)

  Let local_to_knows_read:
    forall cg sj sj' cg' l l' a b x k y k' d g g',
    LocalToKnows l cg sj ->
    CG.Reduces cg (x, CG.CONTINUE) cg' ->
    Reduces cg' l (MEM y (READ d)) l' ->
    LocalKnows cg' l' (a, b) ->
    SJ_CG.Reduces sj (x, CG.CONTINUE) cg' sj' ->
    SJ_CG.SJ cg k sj ->
    DomIncl l (fst cg) ->
    LastWriteCanJoin g (snd cg) sj ->
    SJ_CG.SJ cg' k' sj' ->
    AccessHistory.T.DRF_Check (snd cg') g (MEM y (READ d)) g' ->
    AccessHistory.T.WellFormed cg g ->
    AccessHistory.T.WellFormed cg' g' ->
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
          (** this is the crucial step of the proof *)
          apply AccessHistory.T.drf_check_inv_read_last_write with (x:=x) in Hdrf; auto.
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

  (**
    Show that the local-knowledge contains
    SIF (FUTURE).
    *)

  Let local_to_knows_future:
    forall cg sj sj' cg' l l' a b x y k,
    LocalToKnows l cg sj ->
    CG.Reduces cg (x, CG.FORK y) cg' ->
    Reduces cg' l (FUTURE y) l' ->
    LocalKnows cg' l' (a, b) ->
    SJ_CG.Reduces sj (x, CG.FORK y) cg' sj' ->
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
    destruct H3 as [(?,?)|mt]; simpl_structs. {
      subst.
      apply Locals.maps_to_to_in,Hdom in H6.
      simpl_node. (* absurd *)
    }
    apply task_of_inv in mt.
    destruct mt as [(?,?)|mt]. {
      subst.
      apply Locals.maps_to_to_in, Hdom in H6.
      simpl_node.
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

  (**
    Show that the local-knowledge contains
    SIF (FORCE).
    *)

  Let local_to_knows_force:
    forall cg sj sj' cg' l l' a b x k y,
    LocalToKnows l cg sj ->
    CG.Reduces cg (x, CG.JOIN y) cg' ->
    Reduces cg' l (FORCE y) l' ->
    LocalKnows cg' l' (a, b) ->
    SJ_CG.Reduces sj (x, CG.JOIN y) cg' sj' ->
    SJ_CG.SJ cg k sj ->
    length (fst cg) = length sj ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    rename H5 into Heq.
    handle_all.
    expand H2.
    simpl in *.
    expand H8. (* Locals.MapsTo *)
    rename es0 into es.
    rename ny0 into ny.
    apply task_of_inv in H3.
    rewrite MN_Facts.add_mapsto_iff in *.
    destruct H3 as [(?,?)|mt]. {
      subst.
      destruct H0 as [(_,?)|(N,_)]. {
        subst.
        apply in_app_or in H1; destruct H1 as [Hi|Hi];
        inversion H4; subst;
        eauto using local_knows_def, Locals.local_def, maps_to_to_task_of,
          SJ_CG.knows_append_left, SJ_CG.knows_append_right.
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

  Let local_to_knows_init cg sj sj' cg' l l' a b x k
    (Hcg': LocalKnows cg' l' (a, b))
    (Hdom: DomIncl l (fst cg)) :
    LocalToKnows l cg sj ->
    CG.Reduces cg (x, CG.INIT) cg' ->
    Reduces cg' l INIT l' ->
    SJ_CG.Reduces sj (x, CG.INIT) cg' sj' ->
    SJ_CG.SJ cg k sj ->
    length (fst cg) = length sj ->
    SJ_CG.Knows (fst cg') sj' (a, b).
  Proof.
    intros.
    handle_all.
    expand Hcg'; simpl in *. (* Locals.MapsTo *)
    apply task_of_inv in H6.
    destruct H6 as [(?,?)|?]. {
      (* absurd *)
      subst.
      apply Locals.maps_to_to_in, MN_Facts.add_in_iff in H8.
      destruct H8 as [?|Hi]. {
        subst.
        simpl_node.
      }
      apply Hdom in Hi.
      simpl_node.
    }
    expand H8. (* Locals.MapsTo *)
    rewrite MN_Facts.add_mapsto_iff in *.
    destruct H5 as [(?,?)|(?,mt)]. {
      subst.
      inversion H6.
    }
    eauto using local_knows_def, Locals.local_def, maps_to_to_task_of, SJ_CG.knows_init.
  Qed.

  Notation local_info := (Locals.local_memory datum).

  Definition memory := (AccessHistory.T.cg_access_history * local_info) % type.

  (** If reduces, then local-knowledge-inclusion is preserved. *)

  Let local_to_knows_reduces:
    forall cg k sj sj' g g' cg' l l' x o k',
    LocalToKnows l cg sj ->

    T.TReduces cg (x,o) cg' ->
    SJ_CG.SJ cg k sj ->
    SJ_CG.SJ cg' k' sj' ->

    Reduces cg' l o l' ->
    AccessHistory.T.DRF_Check (snd cg') g o g' ->
    SJ_CG.Reduces sj (x, op_to_cg o) cg' sj' -> (* show that this is implied *)

    length (fst cg) = length sj ->
    DomIncl l (fst cg) ->
    LastWriteCanJoin g (snd cg) sj ->
    AccessHistory.T.WellFormed cg g ->
    AccessHistory.T.WellFormed cg' g' ->
    LocalToKnows l' cg' sj'.
  Proof.
    intros.
    unfold LocalToKnows.
    intros (a,b); intros.
    destruct o as [?|? []|?|?]; simpl in *; eauto.
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
    AccessHistory.T.WellFormed (vs, es) g ->
    AccessHistory.T.WellFormed (z :: vs, {| e_t := t; e_edge := (n,fresh vs) |} :: es) g ->
    AccessHistory.LastWrite (HB ({| e_t := t; e_edge := (n,fresh vs) |} :: es)) a h ->
    MM.MapsTo r h g ->
    TaskOf (AccessHistory.a_when a) x (z :: vs) ->
    TaskOf (AccessHistory.a_when a) x vs.
  Proof.
    intros.
    apply task_of_inv in H4.
    destruct H4 as [(?,?)|?]. {
      subst.
      destruct a; simpl in *.
      subst.
      assert (Hi: In (fresh vs, o) h). {
        eapply AccessHistory.last_write_to_in; eauto.
      }
      eapply AccessHistory.T.wf_node with (vs:=vs) (es:=es) in Hi; eauto.
      simpl in *.
      simpl_node.
    }
    assumption.
  Qed.

  Let last_write_can_join_continue:
    forall a x r g h vs es sj z c t n,
    AccessHistory.T.WellFormed (vs, es) g ->
    LastWriteCanJoin g es sj ->
    AccessHistory.LastWrite (HB ({| e_t:=t; e_edge:=(n, fresh vs)|} :: es)) a h ->
    MM.MapsTo r h g ->
    AccessHistory.a_what a = Some (d_task x) ->
    MapsTo z n vs ->
    SJ_CG.CanJoin (AccessHistory.a_when a) x (c :: sj).
  Proof.
    intros.
    eapply AccessHistory.T.last_write_inv_c in H1; eauto using AccessHistory.T.wf_continue.
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

    AccessHistory.T.WellFormed cg g ->
    AccessHistory.T.WellFormed cg' g' ->

    Reduces cg' l o l' ->
    T.TReduces cg (z,o) cg' ->
    AccessHistory.T.DRF_Check (snd cg') g o g' ->
    SJ_CG.Reduces sj (z, op_to_cg o) cg' sj' -> (* show that this is implied *)

    length (fst cg) = length sj ->
    LocalToKnows l cg sj ->

    LastWriteCanJoin g' (snd cg') sj'.
  Proof.
    intros.
    unfold LastWriteCanJoin.
    intros.
    destruct o as [?|? []|?|?]; simpl in *; handle_all; AccessHistory.T.simpl_drf_check; eauto;
    rename H9 into Hlw;
    rename H10 into Heq;
    try (
      assert (Hmt := H8);
      rewrite MM_Facts.add_mapsto_iff in Hmt;
      destruct Hmt as [(?,?)|(?,?)]; eauto;
      subst
    ).
    - eauto using SJ_CG.can_join_cons.
    - apply AccessHistory.last_write_inv_cons_read in Hlw.
      eauto.
    - apply AccessHistory.last_write_inv_cons_nil in Hlw; subst.
      simpl_structs.
      eauto.
    - assert ((fresh vs, Some d) = a). {
        eapply AccessHistory.T.wf_last_write_inv_cons_write with (ah:=g); eauto using AccessHistory.write_some.
      }
      subst; simpl in *; simpl_node; simpl_structs.
      eauto.
    - eapply AccessHistory.T.last_write_inv_c in Hlw; eauto using AccessHistory.T.wf_continue.
      eapply AccessHistory.T.last_write_inv_c in Hlw; eauto using AccessHistory.T.wf_continue.
      eapply H in Heq; eauto.
      auto using SJ_CG.can_join_cons.
    - eapply AccessHistory.T.last_write_inv_j in Hlw; eauto using AccessHistory.T.wf_continue.
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
    AccessHistory.T.DRF_Check (snd cg') g o g' ->
    SJ_CG.Reduces sj (x, op_to_cg o) cg' sj' -> (* show that this is implied *)
    exists k', WellFormed cg' k' sj' g' l'.
  Proof.
    intros.
    inversion H.
    assert (Hx:=H3).
    eapply SJ_CG.sj_reduces_alt in H3; eauto.
    assert (Hwf: AccessHistory.T.WellFormed cg' g') by eauto using AccessHistory.T.wf_reduces.
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
    AccessHistory.T.DRF_Check (snd cg') g o g' ->
    exists sj', 
    SJ_CG.Reduces sj (x, op_to_cg o) cg' sj'.
  Proof.
    intros.
    destruct o as [?|? []|?|?]; simpl in *; handle_all; AccessHistory.T.simpl_drf_check;
    eauto using SJ_CG.reduces_continue, SJ_CG.reduces_fork, SJ_CG.reduces_init.
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

  (** Main lemma *)

  Lemma wf_reduces_alt:
    forall cg cg' sj g g' l l' k x o,
    WellFormed cg k sj g l ->
    T.TReduces cg (x,o) cg' ->
    Reduces cg' l o l' ->
    AccessHistory.T.DRF_Check (snd cg') g o g' ->
    exists sj' k', WellFormed cg' k' sj' g' l'.
  Proof.
    intros.
    assert (Hsj: exists sj', SJ_CG.Reduces sj (x, op_to_cg o) cg' sj') by
    eauto using wf_sj_cg_reduces.
    destruct Hsj as (sj', Hsj).
    eauto using AccessHistory.T.wf_reduces, wf_reduces.
  Qed.

End SR.
