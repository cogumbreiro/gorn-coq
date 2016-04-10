Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import HJ.Tid.
Require Import HJ.Mid.
Require Import HJ.Cid.
Require Import HJ.Var.
Require Import HJ.Dep.

(* ----- end of boiler-plate code ---- *)

Set Implicit Arguments.

Require Import Aniceto.Graphs.DAG.
Require Import Coq.Relations.Relation_Operators.
Require Aniceto.Graphs.Graph.

Require Import Coq.Structures.OrderedTypeEx.

Require Import Lang.

Module NAT_PAIR := PairOrderedType Nat_as_OT Nat_as_OT.


Section CG.


Section Defs.

  Structure node := {
    node_task: tid;
    node_dag_id: nat;
    node_known: list tid
  }.

  Definition zero_node t := {| node_task := t; node_dag_id:= 0; node_known := nil |}.

  (** DAG id order *)

  Definition dag_lt x y := node_dag_id x < node_dag_id y.

  Definition edge := (node * node) % type.

  Inductive node_type := SPAWN | JOIN.

  Structure triplet := {
    ntype: node_type;
    intra : edge;
    inter : edge
  }.

  Inductive Check : triplet -> Prop :=
  | check_spawn:
    forall x y dx dx' l,
    dx < dx' ->
    x <> y ->
    Check
    {|
      ntype := SPAWN;
      intra :=
      (
        {|
          node_task := x;
          node_dag_id := dx;
          node_known := l
        |},
        {|
          node_task := x;
          node_dag_id := dx';
          node_known := y::l
        |}
      );
      inter :=
      (
        {|
          node_task := x;
          node_dag_id := dx;
          node_known := l
        |},
        {|
          node_task := y;
          node_dag_id := S dx';
          node_known := l
        |}
      )
    |}
  | check_join:
    forall x y dx dx' dy lx ly,
    dx < dx' ->
    dy < dx' ->
    x <> y ->
    Check
    {|
      ntype := JOIN;
      intra :=
      (
        {|
          node_task := x;
          node_dag_id := dx;
          node_known := lx
        |},
        {|
          node_task := x;
          node_dag_id := dx';
          node_known := ly ++ lx
        |}
      );
      inter :=
      (
        {|
          node_task := y;
          node_dag_id := dy;
          node_known := ly
        |},
        {|
          node_task := x;
          node_dag_id := dx';
          node_known := ly ++ lx
        |}
      )
    |}.

  (** Creates a future node *)

  Definition mk_future last_id (x:node) y :=
    (S (S last_id),
      {|
      ntype := SPAWN;
      intra := (x,
      {|
        node_task := (node_task x);
        node_dag_id := S last_id;
        node_known := y::(node_known x)
      |});
      inter :=
      (x,
        {|
          node_task := y;
          node_dag_id := S (S last_id);
          node_known := (node_known x)
        |}
      )
    |}).

  (** Creates a join node *)

  Definition mk_join (last_id:nat) x y :=
  let x' := {|
    node_task := (node_task x);
    node_dag_id := S last_id;
    node_known := (node_known y) ++ (node_known x)
    |}
  in
    (S last_id,
    {|
      ntype := JOIN;
      intra := (x, x');
      inter := (y,x')
    |}
    ).

  Lemma check_intra_eq_task:
    forall v,
    Check v ->
    node_task (fst (intra v)) = node_task (snd (intra v)).
  Proof.
    intros.
    inversion H; simpl in *; auto.
  Qed.

  Lemma check_inter_neq_task:
    forall v,
    Check v ->
    node_task (fst (inter v)) <> node_task (snd (inter v)).
  Proof.
    intros.
    inversion H; simpl in *; auto.
  Qed.

  Lemma check_inter_dag_spawn:
    forall v,
    Check v ->
    ntype v = SPAWN ->
    fst (intra v) = fst (inter v).
  Proof.
    intros.
    inversion H; simpl in *.
    - trivial.
    - rewrite <- H4 in *.
      inversion H0.
  Qed.

  Lemma check_intra_dag_join:
    forall v,
    Check v ->
    ntype v = JOIN ->
    snd (intra v) = snd (inter v).
  Proof.
    intros.
    inversion H; simpl in *; trivial.
    rewrite <- H3 in *.
    inversion H0.
  Qed.

  Lemma check_dag_lt_intra:
    forall v,
    Check v ->
    dag_lt (fst (intra v)) (snd (intra v)).
  Proof.
    intros.
    unfold dag_lt.
    inversion H; simpl in *; auto.
  Qed.

  Lemma check_dag_lt_inter:
    forall v,
    Check v ->
    dag_lt (fst (inter v)) (snd (inter v)).
  Proof.
    intros.
    unfold dag_lt.
    inversion H; simpl in *; auto.
  Qed.

  Lemma check_dag_lt_spawn:
    forall v,
    Check v ->
    ntype v = SPAWN ->
    dag_lt (snd (intra v)) (snd (inter v)).
  Proof.
    intros.
    unfold dag_lt.
    inversion H; simpl in *; auto.
    rewrite <- H4 in *.
    inversion H0.
  Qed.

  Definition to_edges (v:triplet) := inter v :: intra v :: nil.

  Definition triplet_lookup t v := 
  match v with
  {| ntype := _; intra:=(_,v); inter:=(_,v') |} =>
    if TID.eq_dec (node_task v') t then Some v'
    else if TID.eq_dec (node_task v) t then Some v
    else None
  end.

  Definition triplet_contains t v := match triplet_lookup t v with Some _ => true | None => false end.

  Definition trips_lookup (t:tid) (l:list triplet) : option node :=
  match find (triplet_contains t) l with
  | Some v => triplet_lookup t v
  | None => None
  end.

  Inductive computation_graph :=
  | CG_ONE : tid -> computation_graph
  | CG: list triplet -> nat -> computation_graph.

  Definition cg_triplets cg : list triplet :=
  match cg with
  | CG_ONE t => nil
  | CG l _ => l
  end.

  Definition cg_last_id cg :=
  match cg with
  | CG_ONE _ => 0
  | CG _ n => n
  end.

  Definition cg_edges cg :=
  match cg with
  | CG_ONE _ => nil
  | CG l _ => flat_map to_edges l
  end.

  Definition cg_lookup t cg :=
  match cg with
  | CG_ONE x => if TID.eq_dec x t then Some (zero_node x) else None
  | CG l _ => trips_lookup t l
  end.

  Definition cg_future (x y:tid) (cg : computation_graph) : computation_graph :=
  match cg_lookup x cg with
  | Some nx =>
    let (last_id, v) := mk_future (cg_last_id cg) nx y in
    CG (v :: cg_triplets cg) last_id
  | _ => cg
  end.


  Definition cg_force (x y:tid) (cg : computation_graph) : computation_graph :=
  match cg_lookup x cg with
  | Some nx =>
    match cg_lookup y cg with
    | Some ny =>
      let (last_id, v) := mk_join (cg_last_id cg) nx ny in
      CG (v :: cg_triplets cg) last_id
    | _ => cg
    end
  | _ => cg
  end.

  Inductive Reduces: computation_graph -> Lang.effect -> computation_graph -> Prop :=
  | reduces_spawn:
    forall cg x y,
    Reduces cg (x, Lang.FUTURE y) (cg_future x y cg)
  | reduces_join:
    forall cg x y,
    Reduces cg (x, Lang.FORCE y) (cg_force x y cg).

  Inductive Lookup t n: list triplet -> Prop :=
  | lookup_continue: 
    forall v l,
    snd (intra v) = n ->
    node_task n = t ->
    Lookup t n (v::l)
  | lookup_spawn:
    forall v l,
    ntype v = SPAWN ->
    snd (inter v) = n ->
    node_task n = t ->
    Lookup t n (v::l)
  | lookup_cons:
    forall v l,
    Lookup t n l ->
    Lookup t n (v::l).

  (**
    Ensure the names are being used properly; no continue edges after a task
    has been termianted (target of a join).
    *)

  Inductive Dangling : list triplet -> list tid -> Prop :=
  | dangling_nil:
    forall v,
    ntype v = SPAWN ->
    let x := node_task (fst (inter v)) in
    let y := node_task (snd (inter v)) in
    (* x -> y *)
    Dangling (v::nil) (y::x::nil)
  | dangling_cons_spawn:
    forall v vs ts,
    ntype v = SPAWN ->
    let x := node_task (fst (inter v)) in
    let y := node_task (snd (inter v)) in
    (* x -> y *)
    List.In x ts ->
    ~ List.In y ts ->
    Dangling vs ts ->
    Dangling (v::vs) (y::ts)
  | dangling_cons_join:
    forall v vs ts,
    ntype v = JOIN ->
    let x := node_task (fst (inter v)) in
    let y := node_task (snd (inter v)) in
    (* x <- y *)
    List.In x ts ->
    Dangling vs ts ->
    Dangling (v::vs) (remove TID.eq_dec y ts).

  (** Ensure that the triplets are connected. *)

  Inductive Connected : list triplet -> nat -> Prop :=
  | connected_spawn:
    forall v,
    node_dag_id (fst (intra v)) = 0 ->
    Connected (v::nil) 2
  | connected_cons_spawn:
    forall vs n x nx v,
    ntype v = SPAWN ->
    Connected vs n ->
    Lookup x nx vs ->
    fst (inter v) = nx ->
    node_dag_id (snd (inter v)) = S n ->
    Connected (v::vs) (S (S n))
  | connected_cons_join:
    forall vs n x y nx ny v,
    ntype v = JOIN ->
    Connected vs n ->
    Lookup x nx vs ->
    Lookup y ny vs ->
    fst (inter v) = ny ->
    snd (intra v) = nx ->
    Connected (v::vs) (S n).

  Inductive SafeJoin v : Prop :=
  | safe_join_spawn:
    ntype v = SPAWN ->
    SafeJoin v
  | safe_join_join:
    ntype v = JOIN ->
    let l := node_known (fst (intra v)) in
    let y := node_task (fst (inter v)) in
    List.In y l ->
    SafeJoin v.

  Definition AllSafeJoins cg := Forall SafeJoin (cg_triplets cg).

  Inductive Continue v : edge -> Prop :=
    continue_def:
      Continue v (intra v).

  Inductive Spawn: triplet -> edge -> Prop :=
    spawn_def:
      forall v,
      ntype v = SPAWN ->
      Spawn v (inter v).

  Inductive Join: triplet -> edge -> Prop :=
    join_def:
      forall v,
      ntype v = JOIN ->
      Join v (inter v).

  Inductive Prec t e : Prop :=
  | prec_continue:
    Continue t e ->
    Prec t e
  | prec_spawn:
    Spawn t e ->
    Prec t e
  | prec_join:
    Join t e ->
    Prec t e.

  Inductive ListEdge {A:Type} {B:Type} P l (e:B*B) : Prop :=
  | list_edge_def:
    forall (x:A),
    List.In x l ->
    P x e ->
    ListEdge P l e.

  Let LContinue := ListEdge Continue.
  Let LSpawn := ListEdge Spawn.
  Let LPrec := ListEdge Prec.

  Require Import Aniceto.Graphs.Graph.

  Inductive Reaches {A:Type} E (x y:A) : Prop :=
  | reaches_def:
    forall w,
    Walk2 E x y w ->
    Reaches E x y.

  Require Import Coq.Relations.Relation_Operators.

  (** Reflexive closure of continue. *)

  Definition ClosTransRefl {A:Type} E (x y:A) := Reaches E x y \/ x = y.

  Definition ContinueRefl (cg:computation_graph) x := ClosTransRefl (LContinue (cg_triplets cg)) x.

  Definition HB (cg:computation_graph) := Reaches (LPrec (cg_triplets cg)).

  Definition MHP cg x y : Prop := ~ HB cg x y /\ ~ HB cg y x.

  Inductive Ordered cg n1 n2 : Prop :=
  | ordered_lr:
    HB cg n1 n2 ->
    Ordered cg n1 n2
  | ordered_rl:
    HB cg n2 n1 ->
    Ordered cg n1 n2.

  (**
    We have a safe-spawn when the body of the spawn may run in parallel
    with the continuation of the spawn.
    *)

  Inductive SafeSpawn cg : triplet -> Prop :=
  | safe_spawn_eq:
    forall v,
    ntype v = SPAWN ->
    List.In v (cg_triplets cg) ->
    (forall y, ContinueRefl cg (snd (inter v)) y -> MHP cg y (snd (intra v) )) ->
    SafeSpawn cg v
  | safe_spawn_skip:
    forall v,
    ntype v = JOIN ->
    List.In v (cg_triplets cg) ->
    SafeSpawn cg v.

  Definition Safe cg := List.Forall (SafeSpawn cg) (cg_triplets cg).

  (** Is predicate [Safe] equivalent to [CG.RaceFree]? Maybe [CG.RaceFree] implies [Safe] *)
  (** Is predicate [CG.RaceFree] equivalent to [Shadow.RaceFree]? *)

    
End Defs.
End CG.