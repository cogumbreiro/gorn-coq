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
    forall x nx nx' ny l y l' l'' es t vs,
    Mem t (vs,es) l ->
    CG.T.CG ((x,FUTURE y)::t) (y::x::vs, F (nx, ny) :: C (nx, nx') :: es) ->
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

    Lemma local_knows_inv_future:
      forall n h1 h2 l1 vs x a b y es,
      MN.MapsTo n h2 (MN.add (fresh vs) (d_task y :: h1) l1) ->
      MN.MapsTo n h1 l1 ->
      MapsTo x n vs ->
      ~ MN.In (fresh vs) l1 ->
      LocalKnows
        (y :: x :: vs, F (n, fresh (x :: vs)) :: C (n, fresh vs) :: es)
       (MN.add (fresh (x :: vs)) h2 (MN.add (fresh vs) (d_task y :: h1) l1))
        (a, b) ->
      h1 = h2 /\
      (
        (a = y /\ LocalKnows (vs, es) l1 (x,b)) \/
        (a = x /\ y = b) \/
        (a = x /\ LocalKnows (vs, es) l1 (a,b)) \/
        LocalKnows (vs, es) l1 (a,b)
      ).
    Proof.
      intros.
      assert (h2 = h1). {
        rewrite MN_Facts.add_mapsto_iff in *.
        destruct H as [(?,?)|(?,mt)].
        - subst.
          contradiction H2.
          eauto using MN_Extra.mapsto_to_in.
        - eauto using MN_Facts.MapsTo_fun.
      }
      subst; clear H.
      inversion H3; subst; clear H3.
      simpl in *.
      apply task_of_inv in H5. (* TaskOf _ _ _ *)
      apply Locals.maps_to_inv_add in H6. (* Locals.MapsTo _ _ _ *)
      destruct H5 as [(?,?)|Ht]. {
        destruct H6 as [(?,?)|(?,?)]. {
          eauto.
        }
        subst.
        contradiction.
      }
      apply task_of_inv in Ht. (* TaskOf _ _ _ *)
      destruct Ht as [(?,?)|Ht]. {
        destruct H6 as [(?,?)|(?,Hl)]. {
          subst.
          unfold fresh in *.
          inversion H4 (* make _ = make _ *).
          omega. (* absurd *)
        }
        apply Locals.maps_to_inv_add in Hl. (* Locals.MapsTo _ _ _ *)
        destruct Hl as [(?,Hi)|(?, Hl)]. {
          simpl in Hi.
          destruct Hi. {
            inversion H6; clear H6. (* d_task _ = d_task _ *)
            auto.
          }
          subst.
          split; auto.
          right.
          right.
          left.
          eauto.
        }
        subst.
        contradiction.
      }
      destruct H6 as [(?,Hi)|(?,Hl)]. {
        subst.
        rewrite fresh_cons_rw_next in *.
        apply task_of_to_node in Ht.
        simpl_node.
      }
      apply Locals.maps_to_inv_add in Hl. (* Locals.MapsTo _ _ _ *)
      destruct Hl as [(?,Hi)|(?,Hl)]. {
        subst.
        simpl_node.
      }
      intuition.
      right; right; right.
      eapply local_knows_def; eauto.
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
      (** Crucial part of the proof *)
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

    Let last_write_can_join_future:
      forall vs es sj ah x y n t,
      AccessHistory.T.DRF ((x, FUTURE y) :: t)
        (y :: x :: vs, F (n, fresh (x :: vs)) :: C (n, fresh vs) :: es) ah ->
      LastWriteCanJoin (vs, es) sj ah ->
      LastWriteCanJoin
        (y :: x :: vs, F (n, fresh (x :: vs)) :: C (n, fresh vs) :: es)
          (SJ_CG.Copy n :: SJ_CG.Cons y n :: sj) ah.
    Proof.
      unfold LastWriteCanJoin; intros.
      simpl in *.
      assert (mt := H1).
      eapply AccessHistory.T.last_write_inv_future in H1; eauto
      using SJ_CG.can_join_cons.
    Qed.

    Lemma fresh_eq_cons:
      forall A B (a:A) (b:B) (l1:list A) (l2:list B),
      fresh l1 = fresh l2 ->
      fresh (a :: l1) = fresh (b :: l2).
    Proof.
      intros.
      unfold fresh in *.
      inversion H.
      simpl.
      rewrite H1.
      auto.
    Qed.

    Let local_to_knows_future:
      forall y x vs es sj l1 l2 l3 t n,
      SJ_CG.SJ (map T.event_to_cg ((x, FUTURE y) :: t))
        (y :: x :: vs, F (n, fresh (x :: vs)) :: C (n, fresh vs) :: es)
        (SJ_CG.Copy n :: SJ_CG.Cons y n :: sj) ->

      Mem t (vs, es) l1 ->
      LocalToKnows l1 (vs, es) sj ->
      Locals.Reduces l1 (fresh vs, Locals.CONS (d_task y) n) l2 ->
      Locals.Reduces l2 (fresh (x :: vs), Locals.COPY datum n) l3 ->
      LocalToKnows l3
        (y :: x :: vs, F (n, fresh (x :: vs)) :: C (n, fresh vs) :: es)
        (SJ_CG.Copy n :: SJ_CG.Cons y n :: sj).
    Proof.
      intros.
      handle_all.
      assert (cg=(vs,es)). {
        apply SJ_CG.sj_to_cg in H6. (* SJ_CG.SJ *)
        eauto using cg_fun.
      }
      subst.
      rename l into h2.
      rename l0 into h1.
      unfold LocalToKnows in *; intros.
      destruct p as (a,b).
      apply local_knows_inv_future in H; auto.
      destruct H as (?,[(?,Hl)|[(?,?)|[(?,Hl)|Hl]]]); subst; simpl.
      - apply H1 in Hl.
        inversion Hl; subst; clear Hl.
        simpl in *; simpl_node.
        apply SJ_CG.knows_def with (nx:=fresh (x::vs)); auto using maps_to_eq.
        assert (R: fresh (x::vs) = fresh (SJ_CG.Cons y nx :: sj)). {
          eauto using fresh_eq_cons, SJ_CG.sj_to_length_0, maps_to_length_rw.
        }
        rewrite R.
        auto using SJ_CG.can_join_copy, SJ_CG.can_join_cons.
      - apply SJ_CG.knows_def with (nx:=fresh vs). {
          apply maps_to_cons. {
            unfold not; intros; subst.
            apply maps_to_to_in in H19.
            contradiction.
          }
          simpl.
          apply maps_to_eq.
        }
        assert (R: fresh vs = fresh sj). {
          eauto using SJ_CG.sj_to_length_0, maps_to_length_rw.
        }
        rewrite R.
        auto using SJ_CG.can_join_cons, SJ_CG.can_join_eq.
      - apply H1 in Hl.
        inversion Hl; subst; clear Hl.
        simpl in *; simpl_node.
        apply SJ_CG.knows_def with (nx:=fresh vs). {
          apply maps_to_cons. {
            unfold not; intros; subst.
            apply maps_to_to_in in H19.
            contradiction.
          }
          simpl.
          apply maps_to_eq.
        }
        assert (R: fresh vs = fresh sj). {
          eauto using SJ_CG.sj_to_length_0, maps_to_length_rw.
        }
        rewrite R.
        assert (b <> y). {
          unfold not; intros; subst.
          eapply SJ_CG.can_join_to_in in H4; eauto.
        }
        auto using SJ_CG.can_join_cons, SJ_CG.can_join_neq.
      - apply H1 in Hl.
        inversion Hl; subst; clear Hl.
        simpl in *; simpl_node.
        destruct (tid_eq_dec x a). {
          subst.
          simpl_node.
          apply SJ_CG.knows_def with (nx:=fresh vs). {
            apply maps_to_cons. {
              unfold not; intros; subst.
              apply maps_to_to_in in H19.
              contradiction.
            }
            simpl.
            apply maps_to_eq.
          }
          assert (R: fresh vs = fresh sj). {
            eauto using SJ_CG.sj_to_length_0, maps_to_length_rw.
          }
          rewrite R.
          assert (b <> y). {
            unfold not; intros; subst.
            eapply SJ_CG.can_join_to_in in H4; eauto.
          }
          auto using SJ_CG.can_join_cons, SJ_CG.can_join_neq.
        }
        assert (y <> a). {
          unfold not; intros; subst.
          apply maps_to_to_in in H3.
          contradiction.
        }
        apply SJ_CG.knows_def with (nx:=nx); auto using maps_to_cons.
        auto using SJ_CG.can_join_cons, SJ_CG.can_join_neq.
    Qed.

    Let last_write_can_join_force:
      forall vs es sj ah x y nx ny t,
      AccessHistory.T.DRF ((x, FORCE y) :: t)
          (x :: vs, J (ny, fresh vs) :: C (nx, fresh vs) :: es) ah ->
      LastWriteCanJoin (vs, es) sj ah ->
      LastWriteCanJoin (x :: vs, J (ny, fresh vs) :: C (nx, fresh vs) :: es)
        (SJ_CG.Append nx ny :: sj) ah.
    Proof.
      unfold LastWriteCanJoin; intros.
      simpl in *.
      assert (mt := H1).
      eapply AccessHistory.T.last_write_inv_force in H1; eauto
      using SJ_CG.can_join_cons.
    Qed.

    Lemma local_knows_inv_force:
      forall x vs nx es l1 l2 ls a b ny y,
      LocalKnows (x :: vs, J (ny, fresh vs) :: C (nx, fresh vs) :: es)
      (MN.add (fresh vs) (l1 ++ l2) ls) (a, b) ->
      MN.MapsTo nx l1 ls ->
      MN.MapsTo ny l2 ls ->
      MapsTo y ny vs ->
      MapsTo x nx vs ->
      x <> y ->
      (a = x /\ LocalKnows (vs, es) ls (x, b)) \/
      (a = x /\ LocalKnows (vs, es) ls (y, b)) \/
      LocalKnows (vs, es) ls (a, b).
    Proof.
      intros.
      inversion H; subst; clear H.
      simpl in *.
      apply task_of_inv in H7.
      apply Locals.maps_to_inv_add in H8.
      destruct H7 as [(?,?)|Ht]. {
        destruct H8 as [(_,Hi)|(N,_)]. {
          rewrite in_app_iff in *.
          destruct Hi; eauto.
        }
        subst; contradiction.
      }
      destruct H8 as [(?,_)|(?,Hl)]. {
        subst.
        simpl_node.
      }
      eauto using local_knows_def.
    Qed.

    Let local_to_knows_force:
      forall x d t sj es vs l l' ah nx ny y,
      SJ_CG.SJ ((x, JOIN y) :: map T.event_to_cg t)
          (x :: vs, J (ny, fresh vs) :: C (nx, fresh vs) :: es)
          (SJ_CG.Append nx ny :: sj) ->
      Mem t (vs, es) l ->
      Locals.MapsTo ny d l ->
      Locals.MapsTo nx (d_task y) l ->
      Locals.Reduces l (fresh vs, Locals.UNION datum nx ny) l' ->
      AccessHistory.T.DRF t (vs, es) ah ->
      LocalToKnows l (vs, es) sj ->
      MapsTo y ny vs ->
      MapsTo x nx vs ->
      x <> y ->
      LocalToKnows l' (x :: vs, J (ny, fresh vs) :: C (nx, fresh vs) :: es)
          (SJ_CG.Append nx ny :: sj).
    Proof.
      intros.
      handle_all.
      assert (cg=(vs,es)). {
        apply SJ_CG.sj_to_cg in H14. (* SJ_CG.SJ *)
        eauto using cg_fun.
      }
      subst.
      unfold LocalToKnows in *; intros.
      destruct p as (a,b).
      rename ty into z.
      simpl in *.
      eapply local_knows_inv_force in H; eauto.
      destruct H as [(?,Hl)|[(?,Hl)|Hl]]; subst; simpl;
      apply H5 in Hl;
      simpl in *;
      inversion Hl; subst; clear Hl;
      simpl_node.
      - apply SJ_CG.knows_def with (nx:=fresh vs); auto using maps_to_eq.
        assert (R: fresh vs = fresh sj). {
          eauto using SJ_CG.sj_to_length_0, maps_to_length_rw.
        }
        rewrite R.
        auto using SJ_CG.can_join_append_left.
      - apply SJ_CG.knows_def with (nx:=fresh vs); auto using maps_to_eq.
        assert (R: fresh vs = fresh sj). {
          eauto using SJ_CG.sj_to_length_0, maps_to_length_rw.
        }
        rewrite R.
        auto using SJ_CG.can_join_append_right.
      - destruct (tid_eq_dec a x). {
          subst.
          apply SJ_CG.knows_def with (nx:=fresh vs); auto using maps_to_eq.
          assert (R: fresh vs = fresh sj). {
            eauto using SJ_CG.sj_to_length_0, maps_to_length_rw.
          }
          rewrite R.
          simpl_node.
          auto using SJ_CG.can_join_append_left.
        }
        apply SJ_CG.knows_def with (nx:=nx0); eauto using maps_to_cons, maps_to_eq, maps_to_neq.
        auto using SJ_CG.can_join_cons.
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
        assert (Hx:=IHt _ _ _ _ H4 H0 H3 (* SJ_CG.SJ _ _ sj *)).
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
      - apply AccessHistory.T.drf_inv_future in H0.
        assert (Hx:=IHt _ _ _ _ H4 H0 H16(* SJ_CG.SJ _ _ sj *)).
        destruct Hx as (?,?).
        split; eauto using last_write_can_join_future.
      - apply AccessHistory.T.drf_inv_force in H0.
        assert (Hx:=IHt _ _ _ _ H4 H0 H16(* SJ_CG.SJ _ _ sj *)).
        destruct Hx as (?,?).
        clear y.
        rename ty into y.
        split; eauto using last_write_can_join_force, local_to_knows_force.
    Qed.

    Lemma local_knows_to_sj_knows:
      forall t l cg sj ah p,
      Mem t cg l ->
      AccessHistory.T.DRF t cg ah ->
      SJ_CG.SJ (map CG.T.event_to_cg t) cg sj ->
      LocalKnows cg l p ->
      SJ_CG.Knows (fst cg) sj p.
    Proof.
      intros.
      eapply mem_local_to_knows in H1; eauto.
      destruct H1; auto.
    Qed.

    Lemma mem_local_to_sj:
      forall t l cg ah,
      Mem t cg l ->
      AccessHistory.T.DRF t cg ah ->
      exists sj, SJ_CG.SJ (map CG.T.event_to_cg t) cg sj.
    Proof.
      induction t; intros. {
        inversion H; subst; clear H.
        simpl.
        eauto using SJ_CG.sj_nil.
      }
      assert (Hcg : T.CG (a::t) cg) by eauto using AccessHistory.T.drf_to_cg.
      destruct a as (x,[]); inversion Hcg; subst; clear Hcg; simpl_node.
      - apply AccessHistory.T.drf_inv_init in H0.
        inversion H; subst; clear H.
        assert (Hsj: exists sj, SJ_CG.SJ (map T.event_to_cg t) (vs,es) sj) by eauto;
        destruct Hsj as (sj, Hsj);
        simpl.
        exists (SJ_CG.Nil :: sj).
        eauto using SJ_CG.sj_init.
      - inversion H; subst; clear H.
        + apply AccessHistory.T.drf_inv_alloc in H0.
          assert (Hsj: exists sj, SJ_CG.SJ (map T.event_to_cg t) (vs,es) sj) by eauto;
          destruct Hsj as (sj, Hsj);
          simpl.
          exists (SJ_CG.Copy prev :: sj).
          eauto using SJ_CG.sj_continue.
        + simpl_node.
          apply AccessHistory.T.drf_inv_read in H0.
          destruct H0 as (ah', (?,?)).
          assert (Hsj: exists sj, SJ_CG.SJ (map T.event_to_cg t) (vs,es) sj) by eauto;
          destruct Hsj as (sj, Hsj);
          simpl.
          exists (SJ_CG.Copy prev :: sj).
          eauto using SJ_CG.sj_continue.
        + simpl_node.
          apply AccessHistory.T.drf_inv_write in H0.
          destruct H0 as (ah', (?,?)).
          assert (Hsj: exists sj, SJ_CG.SJ (map T.event_to_cg t) (vs,es) sj) by eauto;
          destruct Hsj as (sj, Hsj);
          simpl.
          exists (SJ_CG.Copy prev :: sj).
          eauto using SJ_CG.sj_continue.
      - inversion H; subst; clear H.
        apply AccessHistory.T.drf_inv_future in H0.
        assert (Hsj: exists sj, SJ_CG.SJ (map T.event_to_cg t) (vs,es) sj) by eauto;
        destruct Hsj as (sj, Hsj);
        simpl.
        exists (SJ_CG.Copy nx :: SJ_CG.Cons t0 nx :: sj).
        eauto using SJ_CG.sj_fork.
      - inversion H; subst; clear H.
        apply AccessHistory.T.drf_inv_force in H0.
        assert (Hsj: exists sj, SJ_CG.SJ (map T.event_to_cg t) (vs,es) sj) by eauto;
        destruct Hsj as (sj, Hsj);
        simpl.
        exists (SJ_CG.Append nx ny :: sj).
        (** crucial part of the proof. *)
        apply SJ_CG.sj_join with (ty:=t0) (cg:=(vs,es)); eauto using maps_to_cons.
        assert (Hlk: LocalKnows (vs,es) l0 (x,t0)). {
          eauto using local_knows_def, maps_to_to_task_of.
        }
        eapply local_knows_to_sj_knows in Hlk; eauto.
        inversion Hlk; subst; clear Hlk; simpl_node.
        assumption.
    Qed.
  End LocalToKnows.
End SR.
