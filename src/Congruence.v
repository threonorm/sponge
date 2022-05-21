Local Set Universe Polymorphism.
Unset Universe Minimization ToSet.

Require Import PArith.
Require EGraphList.
Import EGraphList.
Import EGraphList.ListNotations.


Section DeepType.
  Inductive type :=
   | TBase : forall (t : positive), type
   | TArrow: type -> type -> type.

  Fixpoint t_denote
    (typemap : list Type)
    (d : type) :=
    match d with
    | TBase e => EGraphList.nth (Pos.to_nat e - 1) typemap unit
    | TArrow A B => (t_denote typemap A) -> (t_denote typemap B)
    end.
End DeepType.

Notation "A '~>' B" := (TArrow A B) (right associativity, at level 20).
Notation "'`' A " := (TBase A) (at level 1, format "'`' A").

Eval simpl in (t_denote [nat] `1).
Eval simpl in (t_denote [nat : Type; Prop] (`1 ~> `2)).

Inductive term : type -> Type :=
    | TApp: forall {t td},
      term (t ~> td) ->
      term t ->
      term td
    | TVar : forall (n : positive) (t: type),
      term t
    | TConst : forall (n : positive) (t: type),
      term t.


Definition interp_term (typemap : list Type) (constmap : list )  (varmap : list ) 
{t : type} (a : term t)
: t_denote typemap t.
 induction f.
  -
  cbn in *.
  eauto.
  - destruct t0.
    cbn.
    exact state0.
Defined.

Require Import Arith.
Require Import Enodes.
Require Import Lia.
Section egraphs.

  Context {typemap : list Type}.
  Context {ctx : asgn typemap}.

  Definition uf_t := PTree.t eclass_id.
  (*  eclass_id -> eclass_id *)

  Definition init_uf : uf_t := PTree.empty _.
  Definition find (uf : uf_t) (x : eclass_id) := match PTree.get x uf with | Some y => y | None => x end.

  Lemma nat_eq_refl : forall x, exists p, Nat.eq_dec x x = left p.
    intros x.
    destruct (Nat.eq_dec x x).
    eexists. reflexivity.
    unfold "<>" in n. exfalso. apply n. reflexivity.
  Qed.

  Fixpoint dt_eq (t1 t2 : type) : bool :=
  match t1, t2 with
  | TBase n, TBase n' =>
    Nat.eqb n n'
  | TArrow a b, TArrow a' b' =>
    dt_eq a a'&& dt_eq b b'
  | _,_ => false
  end.

  Definition dt_eq_correct : forall (t1 t2 : type ),
    dt_eq t1 t2 = true -> t1 = t2.
    induction t1.
    - cbn.
      destruct t2.
      rewrite Nat.eqb_eq.
      intros; eauto.
      intros; inversion H.
    -
        cbn.
        intros.
        destruct t2;
        try inversion H; clear H.
        cbn in *.
        eapply Bool.andb_true_iff in H1.
        destruct H1.
        specialize IHt1_1 with (1:= H).
        specialize IHt1_2 with (1:= H0).
        rewrite IHt1_1.
        rewrite IHt1_2.
        eauto.
  Qed.


  Fixpoint dt_eq' (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
  refine (match t1, t2 with
  | TBase n, TBase n' =>
    _ (Nat.eq_dec n n')
  | TArrow a b, TArrow a' b' =>
    _
  | _,_ => _
  end).
  intros.
  destruct x.
  left. subst; eauto.
  right.
  intro.
  inversion H.
  subst.
  eapply n0; eauto.
  right.
  intro.
  inversion H.
  right.
  intro.
  inversion H.
      pose proof dt_eq'.
      specialize (dt_eq' a a').
      specialize (H b b').
      destruct H.
      destruct dt_eq'.
      subst.
      left; eauto.
      subst.
      right.
      intro.
      inversion H.
      eauto.
      right.
      intro.
      inversion H.
      eauto.
      Defined.

  Lemma dteq_refl : forall t,
  dt_eq t t = true .
  induction t.
  cbn.
  eapply Nat.eqb_refl.
  cbn.
  rewrite IHt1, IHt2.
  cbn; eauto.
  Qed.

  Lemma dteq_refl' : forall t ,
  exists p, dt_eq' t t = left p.
  induction t.
  cbn.
  destruct (Nat.eq_dec t t).
  destruct e.
  eexists.
  eauto.
  contradiction n.
  reflexivity.
  destruct IHt1.
  destruct IHt2.
  destruct x.
  destruct x0.
  cbn.
  eexists.
  rewrite H0.
  rewrite H.
  cbv.
  cbn; eauto.
  Qed.

  Definition union (g : uf_t) (x y : eclass_id ) : uf_t :=
    let px := find g x in
    let py := find g y in
    PTree.set y px (PTree.map_filter (fun el => if Pos.eq_dec el py then Some px else Some el) g).

  Notation Formula x := (Formula (ctx := ctx) (typemap := typemap) x).

  Fixpoint eqf {t1 t2} (f1 : Formula t1) (f2 : Formula t2) :=
  match f1, f2 with
  | App1 a b, App1 a' b' =>
    eqf a a' && eqf b b'
  | @Atom1 _ _ n tn eq, @Atom1 _ _ n' tn' eq' =>
  match dt_eq' (T tn) (T tn') with
  | left _ =>
    Pos.eqb n n'
  | right _ => false
  end
  | _, _ => false
  end.

  Lemma eqf_refl : forall {t} (f : Formula t), eqf f f = true.
    induction f.
    - cbn.
      rewrite IHf1, IHf2.
      eauto.
    - cbn.
      pose proof (@dteq_refl' (T t0)).
      destruct H.
      rewrite H.
      rewrite Pos.eqb_eq.
      eauto.
  Qed.

  Lemma eq_preserve_type : forall {t1} (f1 : Formula t1) {t2} (f2 : Formula  t2),
  eqf f1 f2 = true -> t1 = t2.
  induction f1.
  2:{
    intros; eauto.
    cbn in H.
    destruct f2 eqn:?; try inversion H; clear H.
    destruct (dt_eq' (T t0) (T t1)); eauto.
    inversion H1.
  }
  {
    cbn.
    intros.
    destruct f2 eqn:?; try inversion H; clear H.
    eapply andb_prop in H1.
    destruct H1.
    specialize (IHf1_1 _ _ H).
    inversion IHf1_1.
    eauto.
  }
  Defined.


  Ltac inverseS e0 :=
    let name := fresh e0 in
    inversion e0 as [name];
    cbn in name;
    apply inj_pair2 in name; clear e0;
    rename name into e0.

  Lemma eq_correct : forall {t} (f1 f2 : Formula t),
    eqf f1 f2 = true -> interp_formula ctx f1 = interp_formula ctx f2.
    induction f1.
    2:{
        cbn.
        intros.
        destruct t0.
        simpl in *.
        destruct f2; try inversion H; clear H.
        destruct (dt_eq' (T t0) (T t0)); inversion H1; clear H1.
        Search ((_ =? _)%positive = true).
        eapply Peqb_true_eq in H0.
        cbn.
        subst.
        destruct t0.
        cbn in *.
        rewrite e in e0.
        inverseS e0.
        eauto.
    }
    {
      intros; eauto.
      destruct f2; try inversion H; clear H.
      eapply andb_prop in H1.
      destruct H1.
      pose proof H.
      pose proof H0.
      eapply eq_preserve_type in H.
      eapply eq_preserve_type in H0.
      subst.
      specialize (IHf1_2 _ H2).
      specialize (IHf1_1 _ H1).
      simpl.
      rewrite IHf1_1.
      rewrite IHf1_2.
      reflexivity.
    }
  Defined.

  (* Definition set_enodes := PTree.t unit. *)
  Definition map_id_enode :=
    PTree.t (eclass_id * type * set_enodes).

  Record egraph := {
    max_allocated : positive;
    uf : uf_t; 
    (* eclass_id -> eclass_id *)
    n2id : map_enode_id;
    (* enode -> eclass_id *)
    (*  enode := EAtom (ptr vers la liste) | EApp eclass_id eclass_id *)
    id2s : map_id_enode
    (* eclass_id -> Set enode *)
  }.

  Definition canonicalize (e : egraph) (node : enode) : enode
  :=
    match node with
    | EApp1 f a =>
      let f := find (uf e) f in
      let a := find (uf e) a in
      EApp1 f a
    | a => a
    (* | EAtom1 n => let can := lookup (n2id e) (EAtom1 n) in *)
    end.

  Definition lookup (e : egraph) (node : enode) : option eclass_id :=
    match lookup (n2id e) (canonicalize e node) with 
    | Some to_canon => Some (find (uf e) to_canon)
    | None => None 
    end.

  (* Invariant, we always merge stuff that are already present in the egraph *)
  Definition merge_id2s (e1 e2 : eclass_id) (m : map_id_enode) : map_id_enode :=
    match (PTree.get e1 m), (PTree.get e2 m) with 
    | Some (eid1, tl, (set_eatoms_l, set_eapp_l)), Some (eid2, tr, (set_eatoms_r, set_eapp_r)) =>
      if dt_eq' tl tr then
        let newatoms :=
          PTree.merge_l set_eatoms_l set_eatoms_r in
        let newapps :=
          PTree.merge_with set_eapp_l set_eapp_r PTree.merge_l in
        PTree.set e2 (eid2, tl, (newatoms, newapps)) m
      else
        m
    (* Following case should never occur, we would leave the map unchanged
    TODO think about how I could define it? *)
    | _, _  => m
    end.

  Definition merge_n2id (e1 e2 : eclass_id) (m:map_enode_id) : map_enode_id :=
    let '(atms, fs) := m in 
    (* let atms_gather_to_change := 
      PTree.map_filter (fun '(enode,e) => if Pos.eq_dec e e1 then Some enode else None) atms
    in
    let atms := PTree.tree_fold_preorder (fun acc val  =>  
                match val with 
                | EAtom1 enode => 
                    PTree.set enode (EAtom1 enode, e2) acc
                | _ => acc
                end) atms_gather_to_change atms 
    (* let atms := PTree.tree_rec atms (fun _lhs acc1 val _rhs acc2 =>  
                match val with 
                | Some (EAtom1 enode) => 
                    PTree.merge_l (PTree.set enode (EAtom1 enode, e2) acc1) acc2 
                | _ => PTree.merge_l acc1 acc2 
                end) atms_gather_to_change *)
    in *)
    let eapp_gather_to_change := PTree.tree_fold_preorder (fun acc val  =>  
    PTree.tree_fold_preorder (fun acci '(enode,eid) =>
                                    match enode with
                                    | EApp1 a b => 
                                      let one_e1 := orb (Pos.eqb a e1) (Pos.eqb b e1) in
                                      if one_e1 then 
                                      let newa := if Pos.eqb a e1 then e2 else a in 
                                      let newb := if Pos.eqb b e1 then e2 else a in 
                                      (EApp1 newa newb, eid)::acc
                                      else acc
                                    | _ => acc 
                                    end) val acc) fs nil in
    EGraphList.fold_left (fun acc '(enode,eid) => 
    add_enode acc enode eid
    ) eapp_gather_to_change m 
    .

  Definition merge (e : egraph) (e1 e2 : eclass_id) := {|
    max_allocated := max_allocated e;
    uf := union (uf e) e1 e2;
    n2id :=
      merge_n2id e1 e2 (n2id e);
    id2s := merge_id2s e1 e2 (id2s e) |}.

  Fixpoint lookupF {t} (f : Formula t) (e : egraph) : option (eclass_id) :=
    match f with
    | App1 e1 e2 =>
      match lookupF e1 e, lookupF e2 e with
      | Some e1, Some e2 =>
        let fnode := EApp1 e1 e2 in
        lookup e fnode
      | _, _ => None
      end
    | Atom1 n t eq =>
      lookup e (EAtom1 n)
    end.

  Definition empty_egraph := {|
    max_allocated := 1;
    uf := init_uf;
    n2id := (PTree.empty _, PTree.empty _);
    id2s := PTree.empty _
    |}.

  Fixpoint add_formula (e : egraph) {t}
    (f : Formula t)
    : (egraph * eclass_id) :=
      match f with
      | App1 f1 f2 =>
        let '(e, fid) := add_formula e f1 in
        let '(e, arg1id) := add_formula e f2 in
        match lookup e (EApp1 fid arg1id) with
        | Some a => (e, a)
        | None =>
        let idx_formula := max_allocated e in
        ({|
        max_allocated := max_allocated e + 1;
        uf := uf e;
        n2id := add_enode (n2id e) (canonicalize e (EApp1 fid arg1id)) idx_formula;
        id2s := PTree.set idx_formula (idx_formula, t, (add_enode_set (PTree.empty _, PTree.empty _)  (canonicalize e (EApp1 fid arg1id)))) (id2s e)|}, idx_formula)
        end
      | Atom1 n _t e0 =>
         match lookupF f e with
        | Some a => (e, a)
        | None =>
        let idx_formula := max_allocated e in
        ({|
        max_allocated := max_allocated e + 1;
        uf := uf e;
        n2id := add_enode (n2id e) (EAtom1 n) idx_formula;
        id2s := PTree.set idx_formula (idx_formula, t, (add_enode_set (PTree.empty _, PTree.empty _) (EAtom1 n))) (id2s e)|}, idx_formula)
        end
      end.

  Definition mergeF {t} (e : egraph) (f : Formula t) (g : Formula t) : egraph * eclass_id * eclass_id :=
    let '(newe, fid) := add_formula e f in
    let '(newe', gid) := add_formula newe g in
    (merge newe' fid gid, fid, gid).

  Definition classIsCanonical e (n : eclass_id) :=
    find (uf e) n = n.

  Definition n2idCanonical e  := forall f (c : eclass_id),
    lookup e f = Some c ->
    classIsCanonical e c.

         (* if t = Prop then *)
          (* interp_formula ctx f <-> interp_formula ctx g; *)
        (* else  *)
  Record invariant_egraph e : Prop := {
      correct: forall t (f g : formula t) (eid : eclass_id),
        lookupf f e = some eid ->
        lookupf g e = some eid ->

          interp_formula ctx f = interp_formula ctx g;
      nobody_outside :
       forall a (eid : eclass_id),
          lookup e a = Some eid ->
           (eid < max_allocated e)%positive;
      no_args_eapp1_outside :
        forall (eid : eclass_id)
                (e1 : eclass_id)
                (e2 : eclass_id)
                ,
          lookup e (EApp1 e1 e2) = Some eid ->
          (find (uf e) e1 < max_allocated e)%positive /\
          (find (uf e) e2 < max_allocated e)%positive;
      sanely_assigned_lookup :
            n2idCanonical e;
      uf_id_outside :
        forall (a: eclass_id), (a >= max_allocated e)%positive ->
          classIsCanonical e a;
      wt_egraph:
        forall {t1 t2} (f1 : Formula t1) (f2 : Formula t2) (c : eclass_id),
        lookupF f1 e = Some c ->
        lookupF f2 e = Some c ->
        t1 = t2;
      wf_uf:
        forall (c : eclass_id),
          (c < max_allocated e)%positive ->
          (find (uf e) c < max_allocated e)%positive;
      }.
Ltac auto_specialize :=
  match goal with
  | H : ?a,  H' : ?a -> _  |- _ =>
    let t := type of a in
    constr_eq t Prop;
    specialize( H' H)
  | H : ?a,  H' :  _  |- _ =>
    let t := type of a in
    constr_eq t Prop;
    specialize H' with (1:= H)
  |  H' :  _  |- _ =>
    specialize H' with (1:= eq_refl)
  end.

  Ltac cleanup' := intros;
  repeat match goal with
  | H: _ /\ _ |- _ => destruct H
  | H: _ <-> _ |- _ => destruct H
  | H: exists _, _  |- _ => destruct H
  | H: True  |- _ => clear H
  | H : ?a = ?b, H' : ?a = ?b |- _ => clear H'
  | H : ?P, H' : ?P |- _ =>
    let t := type of P in
    assert_succeeds(constr_eq t Prop);
    clear H'
  end.
  Open Scope positive.

Theorem nobody_lookupF_outside e :
  invariant_egraph e ->
  forall t (a : Formula t) (eid : eclass_id),
    lookupF a e = Some eid ->
    eid < max_allocated e.
  intro.
  induction a.
  (* -
    cbn.
    intros.
    destruct (lookupF _ _) eqn:? in H0.
    2:{ inversion H0. }
    destruct (lookupF _ _) eqn:? in H0.
    2:{ inversion H0. }
    destruct (lookupF _ _) eqn:? in H0.
    2:{ inversion H0. }
    destruct H.
    eapply nobody_outside0; eauto. *)
  -
    cbn.
    intros.
    destruct (lookupF _ _) eqn:? in H0.
    2:{ inversion H0. }
    destruct (lookupF _ _) eqn:? in H0.
    2:{ inversion H0. }
    destruct H.
    eapply nobody_outside0; eauto.
  -
    cbn.
    intros.
    unfold lookup in H0.
    destruct H.
    eapply nobody_outside0; eauto.
  Qed.


Theorem lookupF_canonical e  :
  invariant_egraph e ->
  forall {t} (f : Formula t) (c : eclass_id),
   lookupF f e = Some c ->
   classIsCanonical e c.
   intro.
   induction f.
  -
    intros; cbn in H0.
    destruct (lookupF _ _) eqn:? in H0.
    2:{ inversion H0. }
    destruct (lookupF _ _) eqn:? in H0.
    2:{ inversion H0. }
    repeat auto_specialize.
    destruct H.
    unfold n2idCanonical in sanely_assigned_lookup0.
    cleanup'.
    repeat auto_specialize.
    eauto.
  -
    intros.
    cbn in H0.
    unfold lookup in H0.
    cbn in H0.
    destruct H.
    unfold n2idCanonical in sanely_assigned_lookup0.
    cleanup'.
    eapply sanely_assigned_lookup0 with (f:=EAtom1 n).
    eauto.
  Qed.

  Lemma dt_eq'_refl : forall {t},
  exists p, dt_eq' t t = left p.
  induction t.
  - cbn.
    pose (nat_eq_refl t).
    destruct e.
    rewrite H.
    destruct x.
    cbn.
    eexists; eauto.
  -
    destruct IHt1.
    destruct IHt2.
    destruct x.
    destruct x0.
    cbn.
    rewrite H0.
    rewrite H.
    cbn.
    eexists; eauto.
  Qed.




  (* TODO this lemma will be a good exercise for exams in the future *)
  Lemma dt_sane : forall td t1, dt_eq (t1 ~> td) td = false.
  induction td.
  -
    cbn; eauto.
  -
    cbn in *.
    intros.
    destruct td2.
    2:{
      specialize (IHtd2 td2_1).
      eapply Bool.andb_false_iff in IHtd2.
      destruct IHtd2.
      erewrite dteq_refl in H.
      inversion H.
      rewrite H.
      eapply Bool.andb_false_iff .
      right.
      eapply Bool.andb_false_iff .
      right; eauto.
    }
      eapply Bool.andb_false_iff .
      right; eauto.
      Qed.
  Lemma dt_sanef : forall t1 td , dt_eq (t1 ~> td) t1 = false.
  induction t1.
  -
    cbn; eauto.
  -
    cbn in *.
    intros.
    destruct t1_1.
    eauto.
    {
      specialize (IHt1_1 t1_2).
      eapply Bool.andb_false_iff in IHt1_1 .
      destruct IHt1_1.
      rewrite H; eauto.
      rewrite H.
      rewrite Bool.andb_comm.
      rewrite Bool.andb_assoc.
      rewrite Bool.andb_comm.
      cbn. eauto.
    }
    Qed.
  (* TODO this lemma will be a good exercise for exam in the future *)
  Lemma dt_sane2 : forall td t1 t2, dt_eq (t1 ~> t2 ~> td) td = false.
  induction td.
  -
    cbn; eauto.
  -
    cbn in *.
    intros.
    destruct td2.
    2:{
      specialize (IHtd2 td2_1).
      eapply Bool.andb_false_iff in IHtd2.
      destruct IHtd2.
      erewrite dteq_refl in H.
      inversion H.
      rewrite H.
      eapply Bool.andb_false_iff .
      right.
      eapply Bool.andb_false_iff .
      right; eauto.
    }
      eapply Bool.andb_false_iff .
      right; eauto.
   Qed.

  Lemma dt_sane2f : forall t1 t2 td, dt_eq (t1 ~> t2 ~> td) t1 = false.
  induction t1.
  -
    cbn; eauto.
  -
    cbn in *.
    intros.
    case t1_1 eqn:?.
    simpl;eauto.
    case t1_2 eqn:?.
    rewrite Bool.andb_comm.
    cbn; eauto.
    {
      destruct d2.
      {
      eapply Bool.andb_false_iff in IHt1_1.
      destruct IHt1_1.
      rewrite H; eauto.
      rewrite Bool.andb_comm.
      rewrite Bool.andb_assoc.
      rewrite Bool.andb_comm.
      cbn. eauto.
      exact t2.
      exact t2.
      }
      {
        specialize (IHt1_1 d2_1 d2_2).
      eapply Bool.andb_false_iff in IHt1_1.
      destruct IHt1_1.
      rewrite H; eauto.
      rewrite dteq_refl in H.
      rewrite dteq_refl in H.
      cbn in *; inversion H.
      }
    }
   Qed.

  Fixpoint node_size (t : type ) :=
    match t with
    | TBase n => 1
    | TArrow a b => 1 + node_size a + node_size b
    end.

  Lemma size_eq_dt : forall t1 t2, dt_eq t1 t2 = true -> node_size t1 = node_size t2.
    induction t1.
    -
      cbn.
      destruct t2.
      intros.
      eauto.
      intros. inversion H.
    -
      intros.
      cbn in *.
      destruct t2.
      inversion H.
      cbn.
      eapply Bool.andb_true_iff in H.
      cleanup'.
      erewrite IHt1_1; eauto.
      erewrite IHt1_2; eauto.
    Qed.

  Require Import Lia.
  (* Even more interesting induction for this one! *)
  Lemma dt_sane2s : forall t2 t1 td, dt_eq (t1 ~> t2 ~> td) t2 = false.
  intros.
  destruct (dt_eq _ _) eqn:?; eauto.
  pose proof (size_eq_dt _ _ Heqb).
  cbn [node_size] in H.
  lia.
  Qed.

  Lemma dteq_neq_dteq'  : forall t1 t2, dt_eq t1 t2 = false -> exists p, dt_eq' (t1 ) t2 = right p.
    induction t1.
    -
      destruct t2; eauto.
      cbn; intros.
      eapply beq_nat_false in H.
      destruct (Nat.eq_dec t t0).
      contradiction H; eauto.
      intros; eexists; eauto.
      cbn.
      intros; eexists; eauto.
    -
      intros.
      cbn in *.
      destruct t2; [eexists; eauto|].
      eapply Bool.andb_false_iff in H.
      destruct H.
      specialize (IHt1_1 _ H).
      destruct IHt1_1.
      rewrite H0.
      destruct (dt_eq' t1_2 t2_2).
      destruct e.
      cbn; eexists; eauto.
      eexists; eauto.
      specialize (IHt1_2 _ H).
      destruct IHt1_2.
      rewrite H0.
      eexists; eauto.
  Qed.

  Lemma dt_sane'  : forall td t1, exists p, dt_eq' (t1 ~> td) td = right p.
    intros.
    eapply dteq_neq_dteq'.
    eapply dt_sane.
  Qed.
  Lemma dt_sane2'  : forall td t1 t2, exists p, dt_eq' (t1 ~> t2 ~> td) td = right p.
    intros.
    eapply dteq_neq_dteq'.
    eapply dt_sane2.
  Qed.
 Lemma dt_sane2f'  : forall td t1 t2, exists p, dt_eq' (t1 ~> t2 ~> td) t1 = right p.
    intros.
    eapply dteq_neq_dteq'.
    eapply dt_sane2f.
  Qed.
 Lemma dt_sane2s'  : forall td t1 t2, exists p, dt_eq' (t1 ~> t2 ~> td) t2 = right p.
    intros.
    eapply dteq_neq_dteq'.
    eapply dt_sane2s.
  Qed.
  Lemma dt_comm_right  : forall t1 t2 p, dt_eq' t1 t2 = right p -> exists p', dt_eq' t2 t1 = right p' .
    induction t1.
    - intros.
    destruct t2.
    cbn in *.
    destruct (Nat.eq_dec t t0).
    rewrite e.
    destruct (Nat.eq_dec _ _).
    inversion H.
    contradiction n; eauto.
    destruct (Nat.eq_dec _ _).
    contradiction n; eauto.
    eexists; eauto.
    cbn in *.
    eexists; eauto.
    -
      intros.
      cbn in *.
      destruct t2.
      cbn.
      eexists; eauto.
      cbn.
      destruct (dt_eq' t1_2 t2_2) eqn:?;
      destruct (dt_eq' t1_1 t2_1) eqn:?.
      subst.
      cbn in H.
      inversion H.
      destruct e.
      cbn in H.
      specialize (IHt1_1 _ _ Heqs0).
      destruct IHt1_1.
      rewrite H0.
      pose (@dt_eq'_refl t1_2).
      destruct e.
      rewrite H1.
      destruct x0.
      cbn.
      eexists; eauto.
      specialize (IHt1_2 _ _ Heqs).
      destruct IHt1_2.
      rewrite H0.
      eexists; eauto.
      specialize (IHt1_2 _ _ Heqs).
      destruct IHt1_2.
      rewrite H0.
      eexists; eauto.
  Qed.


  Lemma atom_correct : forall {t t' st} (f1 : Formula t) n eq,
    eqf f1 (Atom1 n {|T:= t'; state := st|} eq) = true ->
    exists st' eq', f1 = Atom1 n {| T:= t; state := st'|} eq'.
    induction f1; intros; cbn in H; try inversion H.
    destruct t0.
    cbn in *.
    destruct (dt_eq' T0 t').
    eapply Pos.eqb_eq in H; eauto.
    rewrite <- H.
    eexists; eexists; eauto.
    inversion H.
  Qed.

  Lemma lookup_update {t} (f : Formula t) {old_id2s} :
  forall e n (eid0 : eclass_id),
      invariant_egraph e ->
      lookup e (EAtom1 n) = None ->
      lookupF f {| max_allocated := max_allocated e + 1;
                   uf := uf e;
                   n2id := add_enode (n2id e) (EAtom1 n) (max_allocated e);
                   id2s := old_id2s |} = Some eid0 ->
      lookupF f e = Some eid0 \/
      exists st eq, eqf f (Atom1 n {| T:= t; state := st |} eq) = true.
    induction f; cbn.
       2:{
         intros.
         cbn.
         unfold add_enode.
         cbn.
         destruct t0.
         cbn in *.
         pose proof (@dt_eq'_refl T0).
         destruct H2.
         intros.
         (* rewrite H2. *)
         unfold lookup in H1.
         simpl in H1.
         destruct H.
         unfold lookup, Enodes.lookup, lookup' in H0, nobody_outside0, H1.
         unfold add_enode, Enodes.lookup, lookup' in H1.
         destruct (n2id e0) eqn:?.
         simpl in H0.
         destruct ((n =?  n0)%positive) eqn:?.
         {
           pose (@Pos.eqb_eq n n0).
           destruct i.
           specialize (H Heqb).
           rewrite H in *.
           destruct (PTree.get _ _ ) eqn:? in H0.
           inversion H0.
           rewrite Heqo in H1.
           rewrite PTree.gss in H1.
           rewrite H2.
           eauto.
         }
         {
         pose (@Pos.eqb_neq n n0).
         destruct i.
         specialize (H Heqb).
         destruct (PTree.get _ _ ) eqn:? in H0.
         inversion H0.
         rewrite Heqo in H1.
         rewrite PTree.gso in H1; eauto.
         specialize (nobody_outside0 (EAtom1 n) eid0 ).
         cbn in nobody_outside0.
         specialize (nobody_outside0 H1).
         destruct (PTree.get n t) eqn:?.
         2:{ inversion H1. }
         inversion H1.
         left.
         unfold lookup, Enodes.lookup, lookup'.
         rewrite Heqm.
         simpl.
         rewrite Heqo0.
         eauto. 
       }
       }
       {
          intros.
          destruct (lookupF f1 _) eqn:? in H1.
          destruct (lookupF f2 _)  eqn :? in H1.
          specialize (IHf1 _ _ _ H H0 Heqo).
          specialize (IHf2 _ _ _ H H0 Heqo0).
          destruct IHf1.
        
          2:{
            cleanup'.
            pose proof (eq_preserve_type _ _ H2).
            subst.
            pose proof (@atom_correct).
            specialize (H4) with (1:= H2).
            cleanup'.
            subst.
            cbn in Heqo.
            unfold lookup, Enodes.lookup, lookup' in Heqo.
            cbn in Heqo.
            cbn .
            rewrite H0.
            simpl in *.
            unfold add_enode in *.
            destruct (n2id e) eqn:?.

            unfold lookup, Enodes.lookup, lookup' in *.
            destruct (PTree.get _ _) eqn:? in Heqo.
            rewrite Heqo1 in *.
            simpl in H1.
            rewrite Heqm in H0.
            simpl in H0.
            rewrite Heqo1 in H0.
            inversion H0.
            simpl in*.
            rewrite Heqo1 in *.
            simpl in*.
            rewrite PTree.gss in Heqo.
            simpl in Heqo.
            inversion Heqo.
            destruct H.
     
            unfold lookup in no_args_eapp1_outside0.
            simpl in no_args_eapp1_outside0.
            specialize (no_args_eapp1_outside0 eid0 e0 e1).
            unfold Enodes.lookup, lookup' in H1, no_args_eapp1_outside0.
            rewrite Heqm in no_args_eapp1_outside0.
            specialize (no_args_eapp1_outside0 H1).
            subst.
            cleanup'.
            unfold find in H.
            cbn in H.
            unfold classIsCanonical, find in uf_id_outside0.
            erewrite (uf_id_outside0 (max_allocated e)) in H.
            erewrite uf_id_outside0 in H.
            cbn in *.
            lia.
            lia.
            lia.
          }
          rewrite H2.
          destruct IHf2.
          2:{
            cleanup'.
            pose proof (eq_preserve_type _ _ H3).
            subst.
            pose proof (@atom_correct).
            specialize (H5) with (1:= H3).
            cleanup'.
            subst.
            cbn in Heqo.
            cbn in *.
            unfold lookup, Enodes.lookup, lookup' in *.
            cbn in Heqo.
            cbn .
            simpl in *.
            clear H3.
            unfold add_enode in *.
            destruct (n2id e) eqn:?.

            unfold lookup, Enodes.lookup, lookup' in *.
            destruct (PTree.get _ _) eqn:? in H0.
            rewrite Heqo1 in *.
            simpl in *.
            inversion H0.
       
            simpl in*.
            rewrite Heqo1 in *.
            simpl in*.

            rewrite PTree.gss in Heqo0.
            simpl in Heqo0.
            inversion Heqo0.
            destruct H.
            unfold lookup in no_args_eapp1_outside0.
            simpl in no_args_eapp1_outside0.
            specialize (no_args_eapp1_outside0 eid0 e0 e1).
            unfold Enodes.lookup, lookup' in H1, no_args_eapp1_outside0.
            rewrite Heqm in no_args_eapp1_outside0.
            specialize (no_args_eapp1_outside0 H1).
            subst.
            cleanup'.
            unfold find in H3.
            cbn in H3.
            unfold classIsCanonical, find in uf_id_outside0.
            erewrite (uf_id_outside0 (max_allocated e)) in H3.
            erewrite uf_id_outside0 in H3.
            cbn in *.
            lia.
            lia.
            lia.
          }
          rewrite H3.
          left.
          unfold add_enode,lookup, Enodes.lookup, lookup' in *.
          cbn in *.
          destruct (n2id e).
            unfold lookup, Enodes.lookup, lookup' in *.
            destruct (PTree.get _ _) eqn:? in H0.
            rewrite Heqo1 in *.
            simpl in *.
            inversion H0.
          rewrite Heqo1 in *.
          eauto.
          inversion H1.
          inversion H1.
       }
       Qed. 

  Lemma lookup_add_not_there : forall {t} (g : Formula t) e node i {new_id2s},
    invariant_egraph e ->
    lookup e node = None ->
    lookupF g e = Some i ->
    lookupF g {| max_allocated := max_allocated e + 1;
                 uf := uf e;
                 n2id := add_enode (n2id e) (canonicalize e node) (max_allocated e);
                 id2s := new_id2s |} =
    Some i.
    induction g.
    {
      intros.
      cbn in *.
      repeat auto_specialize.
      destruct (lookupF _ _) eqn:? in H1.
      2:{ inversion H1. }
      destruct (lookupF _ _) eqn:? in H1.
      2:{ inversion H1. }
      repeat auto_specialize.
      rewrite IHg1.
      rewrite IHg2.

      unfold lookup, Enodes.lookup, lookup'  in *.
      simpl.
      destruct node;eauto.
      (* destruct (_&&_)eqn:?; eauto. *)
      (* eapply Bool.andb_true_iff in Heqb. *)
      cleanup'.
      pose proof (@lookupF_canonical _ H _ _ _ Heqo).
      pose proof (@lookupF_canonical _ H _ _ _ Heqo0).
      unfold add_enode.
      simpl in *.
      destruct (n2id e) eqn:?.
      rewrite H2 in H1.
      simpl in *.
      rewrite H3 in H1.
      rewrite H2.
      rewrite H3.

        unfold lookup, Enodes.lookup, lookup' in *.
      simpl in *.
        destruct (PTree.get _ _) eqn:? in H1  .
        2:{ inversion H1. }
        destruct (PTree.get _ _) eqn:? in H1  .
        2:{ inversion H1. }
      assert (e0 = find (uf e) e2 \/ e0 <> find (uf e) e2) by lia.
      destruct H4. 
      2:{
        simpl in *.
        unfold lookup, Enodes.lookup, lookup' in *.

        destruct (PTree.get _ _) eqn:? in H0  .
        rewrite Heqo3.
        destruct (PTree.get _ _) eqn:? in H0  .
        rewrite Heqo4.
        rewrite Heqo1.
        rewrite Heqo2.
        eauto.
        rewrite Heqo4.
      erewrite PTree.gso;
      eauto.
      simpl in *.
      setoid_rewrite Heqo1.
      setoid_rewrite Heqo2.
      eauto.
      rewrite Heqo3.
      erewrite PTree.gso;
      eauto.
      setoid_rewrite Heqo1.
      setoid_rewrite Heqo2.
      eauto.
      }

      subst.
      rewrite Heqo1 in *.
      destruct (PTree.get _ _) eqn:? in H0  .
      inversion H0.
      rewrite Heqo3.

      erewrite PTree.gss.
      simpl in *.
      (* rewrite H2 iddn H0. *)
      assert (e1 = find (uf e) e3 \/ e1 <> find (uf e) e3) by lia.
      destruct H4.
      2:{
        erewrite PTree.gso; eauto.
        rewrite Heqo2.
        eauto.
      }
      subst.
      rewrite PTree.gss.
      simpl.
      inversion H1.
      2:{  simpl in *.
      destruct (n2id e) eqn:?.
      unfold add_enode.
      unfold Enodes.lookup, lookup'.
      destruct (PTree.get _ _) eqn:? in H0  .
      inversion H0.
      rewrite Heqo1 in *.
      eauto.  
      }
      (* Contradiction *)
      congruence.
    }
    {
      intros.
      cbn in *.
      unfold add_enode.
      unfold lookup, Enodes.lookup, lookup'  in *.
      cbn in *.
      destruct (n2id e0) eqn:?.
      destruct node; eauto.
      cbn in *.
      destruct (PTree.get _ _) eqn:? in H0.
      rewrite Heqo.
      destruct (PTree.get _ _) eqn:? in H0.
      inversion H0.
      rewrite Heqo0.
      eauto.
      rewrite Heqo.
      eauto.
      simpl.
      destruct (n0 =? n) eqn:?; eauto.
      eapply Pos.eqb_eq in Heqb.
      subst.

      destruct (PTree.get _ _) eqn:? in H1.
      2:{ inversion H1. }
      setoid_rewrite Heqo.
      setoid_rewrite Heqo.
      eauto.
    
      eapply Pos.eqb_neq in Heqb.
      destruct (PTree.get n0 _) eqn:? .
      destruct (PTree.get _ _) eqn:? .
      eauto.
      inversion H1.
      rewrite PTree.gso.
      eauto.
      eauto.
    }
    Qed. 

  (* On veut dire que si lookup = max_allocated, alors f2 est EAtom1 *)
  Lemma found_high_in_updated : forall {t} (g : Formula t) e node i {new_id2s},
    invariant_egraph e ->
    lookupF g {| max_allocated := max_allocated e + 1;
                 uf := uf e;
                 n2id := add_enode (n2id e) (canonicalize e node) (max_allocated e);
                 id2s := new_id2s |} =
    Some i ->
    (i < max_allocated e /\ lookupF g e = Some i ) \/
    (i = max_allocated e /\
    match g with
    | Atom1 n t eq => EAtom1 n = canonicalize e node
    | App1 f1 f2  =>
      exists e1 e2,
        lookupF  f1 e= Some e1 /\
        lookupF  f2 e= Some e2 /\
        EApp1 e1 e2 = canonicalize e node
    end).
    induction g.
    {
      intros e node i new_id2s inv.
      simpl.
      intros.
      destruct (lookupF _ _) eqn:? in H.
      2:{ inversion H. }
      destruct (lookupF _ _) eqn:? in H.
      2:{ inversion H. }
      unfold add_enode in H.
      repeat auto_specialize.
      destruct IHg1.
      destruct IHg2.
      {
        cleanup'.
        rewrite H3, H2.
        unfold lookup, Enodes.lookup, lookup' in *.
        simpl in *.
        destruct (n2id e) eqn:?.
        pose proof (@lookupF_canonical _ inv _ _ _ H3) as can_n1.
        pose proof (@lookupF_canonical _ inv _ _ _ H2) as can_n0.
        rewrite can_n0, can_n1 in *.
        cleanup'.
        destruct node eqn:?.
        2:{ left. split; eauto. simpl in *. destruct inv. 
        
        unfold lookup, Enodes.lookup, lookup' in nobody_outside0.
        erewrite Heqm in nobody_outside0.
        specialize (nobody_outside0 (EApp1 e0 e1) i).
        simpl in nobody_outside0.
        rewrite can_n0 in nobody_outside0.
        rewrite can_n1 in nobody_outside0.
        destruct (PTree.get _ _) in H.
        specialize (nobody_outside0 H).
        eauto.
        eauto.
        simpl in *.
        destruct (PTree.get _ _) in H.
        eauto.
        eauto.
        }
        simpl in *.
        destruct (PTree.get) eqn:? in H.
        destruct (PTree.get) eqn:? in H.
        destruct (PTree.get) eqn:? in H.
        rewrite Heqo3.
        destruct (PTree.get) eqn:? in H.
        2:{ inversion H. }
        2:{ inversion H. }
        rewrite Heqo4.
        { left.
        split;eauto.
        destruct inv.
        unfold lookup, Enodes.lookup, lookup' in nobody_outside0.
        rewrite Heqm in nobody_outside0.
        specialize (nobody_outside0  (EApp1 e0 e1) i).
        eapply nobody_outside0.
        simpl.
        rewrite can_n1.
        rewrite can_n0.
        rewrite Heqo3.
        rewrite Heqo4.
        congruence.
        }
        {
        assert (e0 = find (uf e) e2 \/ e0 <> find (uf e) e2) by lia.
        destruct H4.
        {
          rewrite H4 in *.
          rewrite PTree.gss in H.
        assert (e1 = find (uf e) e3 \/ e1 <> find (uf e) e3) by lia.
        destruct H5.
        {
          rewrite <- H5 in *.
          rewrite PTree.gss in H.
          simpl in *.
          rewrite Heqo1.
          rewrite Heqo2.
          right.
          split;eauto.
          destruct inv.
          erewrite uf_id_outside0 in H; try lia.
          congruence.
        }
        {
          pose (nobody_outside e inv).
          unfold lookup, Enodes.lookup, lookup' in l.
          rewrite Heqm in l.
          specialize (l (EApp1 e2 e1) i).
          simpl in l.
          rewrite PTree.gso in H; eauto.
          simpl in *.
          rewrite Heqo1; eauto.
          destruct (PTree.get) eqn:? in H.
          rewrite Heqo3.
          left; split; eauto.
          subst.
          inversion H.
          subst.
          clear H.
          rewrite Heqo1 in l.
          rewrite can_n0 in l.
          rewrite Heqo3 in l.
          intuition lia.
          inversion H.
        }
        }
        {
          rewrite PTree.gso in H; eauto.
          destruct (PTree.get) eqn:? in H.
          2:{ inversion H. }
          setoid_rewrite Heqo3.
          rewrite H.
          left.
          split ;eauto.
          pose (nobody_outside e inv).
          unfold lookup, Enodes.lookup, lookup' in l.
          rewrite Heqm in l.
          specialize (l (EApp1 e0 e1) i).
          simpl in l.
          rewrite can_n1 in l.
          setoid_rewrite Heqo3 in l.
          rewrite can_n0 in l.
          specialize (l H).
          eauto.
        }
        }
        {
        assert (e0 = find (uf e) e2 \/ e0 <> find (uf e) e2) by lia.
        destruct H4.
        {
          rewrite H4 in *.
          rewrite PTree.gss in H.
        assert (e1 = find (uf e) e3 \/ e1 <> find (uf e) e3) by lia.
        destruct H5.
        {
          rewrite <- H5 in *.
          rewrite PTree.gss in H.
          simpl in *.
          rewrite Heqo1.
          right.
          split;eauto.
          destruct inv.
          erewrite uf_id_outside0 in H; try lia.
          congruence.
        }
        {
          rewrite PTree.gso in H; eauto.
          simpl in *.
          rewrite Heqo1; eauto.
          inversion H.
        }
        }
        {
          rewrite PTree.gso in H; eauto.
          destruct (PTree.get) eqn:? in H.
          setoid_rewrite Heqo2.
          rewrite H.
          left.
          split; eauto.
          pose (nobody_outside e inv).
          unfold lookup, Enodes.lookup, lookup' in l.
          rewrite Heqm in l.
          specialize (l (EApp1 e0 e1) i).
          simpl in l.
          rewrite can_n1 in l.
          setoid_rewrite Heqo2 in l.
          rewrite can_n0 in l.
          specialize (l H).
          eauto.
          inversion H.
        }
      }
    }
    {
      cleanup'.
      subst.
      destruct node; simpl in *.
      2:{
        pose (no_args_eapp1_outside e inv i e0 (max_allocated e)).
        unfold lookup, Enodes.lookup, lookup' in *.
        simpl in *.
        destruct (n2id e) eqn:? in H.
        rewrite Heqm in a.
        destruct (PTree.get) eqn:? in H.
        specialize (a H).
        cleanup'.
        erewrite (uf_id_outside) in H4; try intuition lia.
        specialize (a H).
        cleanup'.
        erewrite (uf_id_outside) in H4; try intuition lia.
      }
      {
        pose (no_args_eapp1_outside e inv i e0 (max_allocated e)).
        unfold lookup, Enodes.lookup, lookup' in *.
        simpl in *.
        destruct (n2id e) eqn:? in H.
        rewrite Heqm in a.
        destruct (PTree.get) eqn:? in H.
        destruct (PTree.get) eqn:? in H.
        specialize (a H).
        cleanup'.
        erewrite (uf_id_outside) in H4; try intuition lia.
        assert (find (uf e) e0 = find (uf e) e1 \/ find (uf e) e0 <> find (uf e) e1) by lia.
        destruct H1.
        {
          rewrite H1 in *; clear H1.
          rewrite PTree.gss in H.
          rewrite Heqo1 in a.
          assert (find (uf e) (max_allocated e) = find (uf e) e2 \/ find (uf e) (max_allocated e) <> find (uf e) e2) by lia.
          destruct H1.
          {
            (* inconsistent *)
            exfalso.
            rewrite H1 in H.
            rewrite PTree.gss in H.
            inversion H.
            clear a.
            subst.
            rewrite <- H1 in *.
            rewrite Heqm in Heqo0.
            clear H1.
            unfold add_enode,Enodes.lookup, lookup' in Heqo0.
            rewrite Heqo1 in Heqo0.
            rewrite Heqo2 in Heqo0.
            clear H.
            destruct g2; cleanup'; simpl in *.
            admit.
            admit.
        }
        {
          rewrite PTree.gso in H.
          specialize (a H).
          cleanup'.
          erewrite (uf_id_outside) in H5; try intuition lia.
          eauto.
        }
        (* assert (find (uf e) e0 = find (uf e) e1 \/ find (uf e) e0 <> find (uf e) e1) by lia.
        destruct H1.
        {
          rewrite H1 in *; clear H1.
          rewrite PTree.gss in H.
          admit.
        }
        {
          rewrite PTree.gso in H.
          specialize (a H).
          cleanup'.
          erewrite (uf_id_outside) in H5; try intuition lia.
          eauto.
        } *)
       }
       admit.
       admit.
    }
  }
  admit.
    Admitted.

  Require Import Eqdep.
  Lemma add_atom_safe : forall {t} n eq e ,
    invariant_egraph e ->
    let '(newe, _) := add_formula e (@Atom1 _ _ n t eq) in
    invariant_egraph newe.
    cbn.
    intros.
    destruct (lookup e (EAtom1 n )) eqn:?; eauto.
    econstructor.
    intros.
    pose proof @lookup_update as updf.
    specialize updf with (1:= H).
    specialize updf with (1:= Heqo).
    specialize updf with (1:= H0).
    pose proof @lookup_update as updg.
    specialize updg with (1:= H).
    specialize updg with (1:= Heqo).
    specialize updg with (1:= H1).
    destruct updf.
    {
      destruct updg.
      eapply H; eauto.
      cleanup'.
      pose H3.
      eapply eq_preserve_type in e0.
      subst.
      pose proof (@atom_correct) as atomg.
      specialize atomg with (1:= H3).
      cleanup'.
      subst.
      cbn in *.
      (* That should be absurd: eid = max allocated *)
      {
        unfold lookup,  Enodes.lookup, lookup' in H1, Heqo.
        simpl in H1,Heqo.
        unfold add_enode in H1.
        unfold lookup,  Enodes.lookup, lookup' in H1.
        destruct (n2id e) eqn:?.
        destruct (PTree.get n t1) eqn:? in H1.
        inversion Heqo.
        congruence.
        rewrite PTree.gss in H1.
        inversion H1.
        pose proof (nobody_lookupF_outside e H _ _ _ H2).
        destruct H.
        erewrite uf_id_outside0 in H5; try lia.
      }
    }
    {
      cleanup'.
      pose H2.
      eapply eq_preserve_type in e0.
      subst.
      pose proof (@atom_correct) as atomf.
      specialize atomf with (1:= H2).
      cleanup'.
      (* destruct atomf. *)
      subst.
      cbn in H0.
      unfold add_enode in H0.
      unfold lookup, Enodes.lookup, lookup' in H0, Heqo.
      cbn in H0, Heqo.
      destruct (n2id e) eqn:?.
      destruct (PTree.get n t1) eqn:? in H0.
      {
        rewrite Heqo0 in *.
        inversion H0.
        destruct updg.
        pose proof (nobody_lookupF_outside e H).
        specialize H5 with (1:= H3).
        subst.
        cbn in *.
        inversion Heqo.
        cleanup'.
        pose proof (@atom_correct) as atomg.
        specialize atomg with (1:= H3).
        cleanup'.
        subst.
        simpl.
        cbn in *.
        rewrite x2 in x6.
        inverseS x6.
        eauto.
      }
      {
        rewrite Heqo0 in *.
        rewrite PTree.gss in H0.
        inversion H0.
        destruct updg.
        pose proof (nobody_lookupF_outside e H).
        specialize H5 with (1:= H3).
        erewrite uf_id_outside in H4; eauto; lia.
        cleanup'.
        pose proof (@atom_correct) as atomg.
        specialize atomg with (1:= H3).
        cleanup'.
        subst.
        simpl.
        cbn in *.
        rewrite x2 in x6.
        inverseS x6.
        eauto.
      }
    }
    {
      cbn.
      intros.
      pose proof (nobody_outside e H).
      unfold add_enode, lookup, Enodes.lookup, lookup' in H0,H1, Heqo.
      simpl in H0.
      subst.
      destruct (n2id e) eqn:?.
      destruct (PTree.get _ _) eqn:? in H0.
      { 
        simpl in *.
        cbn in H0.
        specialize (H1 a eid).
        destruct a; simpl in *.
        specialize H1 with (1:=H0).
        lia.
        specialize H1 with (1:=H0).
        lia.
      }
      {
        simpl in *.
        cbn in H0.
        specialize (H1 a eid).
        destruct a; simpl in *.
        specialize H1 with (1:=H0).
        lia.
        rewrite Heqo0 in *.
        assert (n0 = n \/ n0 <> n) by lia .
        destruct H2.
        {
          subst.
          rewrite PTree.gss in H0.
          inversion H0.
          erewrite uf_id_outside; eauto;lia.
        }
        {
          rewrite PTree.gso in H0;
          intuition lia.
        }
      }
    }
    {
      cbn.
      intros.
      pose proof (no_args_eapp1_outside e H).
      unfold add_enode, lookup, Enodes.lookup, lookup' in H0,H1, Heqo.
      simpl in H0.
      subst.
      destruct (n2id e) eqn:?.
      simpl in *.
      destruct (PTree.get _ _) eqn:? in H0.
      { 
        simpl in *.
        cbn in H0.
        specialize (H1 eid e1 e2).
        specialize H1 with (1:=H0).
        lia.
      }
      {
        simpl in *.
        cbn in H0.
        specialize (H1 eid e1 e2).
        specialize H1 with (1:=H0).
        lia.
      }
    }
    {
      unfold n2idCanonical.
      cbn.
      unfold lookup, add_enode, Enodes.lookup, lookup' in *.
      destruct H.
        unfold n2idCanonical in sanely_assigned_lookup0.
      unfold lookup, add_enode, Enodes.lookup, lookup' in sanely_assigned_lookup0.
      intros.
      unfold classIsCanonical.
      cbn.
      {
        subst.
        cleanup'.
        destruct (n2id e) eqn:?.
        destruct f eqn:?;
        try auto_specialize;
        unfold classIsCanonical in sanely_assigned_lookup0;
        eauto.
        {
          simpl in *.
          specialize (sanely_assigned_lookup0 f c).
          subst f.
          simpl in *.
          destruct (PTree.get _ _) eqn:? in H.
          {
            rewrite Heqo0 in *.
            inversion Heqo.
          }
          clear Heqo.
          destruct (PTree.get _ _) eqn:? in H.
          {
          destruct (PTree.get _ _) eqn:? in H.
          rewrite Heqo in *.
          rewrite Heqo1 in *.
          specialize (sanely_assigned_lookup0 H).
          eauto.
          inversion H.
          }
          inversion H.
        }
        {
          simpl in *.
          specialize (sanely_assigned_lookup0 f c).
          subst f.
          simpl in *.
          destruct (PTree.get _ _) eqn:? in H.
          {
            rewrite Heqo0 in *.
            inversion Heqo.
          }
          clear Heqo.
          assert (n = n0 \/  n<>n0) by lia.
          destruct H0.
          {
            subst.
            rewrite PTree.gss in H.
            simpl in *.
            inversion H.
            erewrite uf_id_outside0; try lia.
            erewrite uf_id_outside0; try lia.
          }
          {
            erewrite PTree.gso in H; eauto.
          }
        }
      }
    }
    {
      cbn.
      intros.
      destruct H.
      eapply uf_id_outside0.
      lia.
    }
    {
      intros.
      cbn in *.
      change (lookupF f1
                {|
                  max_allocated := max_allocated e + 1;
                  uf := uf e;
                  n2id := add_enode (n2id e) (canonicalize e (EAtom1 n)) (max_allocated e);
                  id2s :=
                    PTree.set (max_allocated e)
                      (max_allocated e, T t,
                      (PTree.Nodes (PTree.set0 n n),
                      PTree.empty (PTree.t (eclass_id * eclass_id)))) 
                      (id2s e)
                |} = Some c
               ) in H0.
      change ( lookupF f2
       {|
         max_allocated := max_allocated e + 1;
         uf := uf e;
         n2id := add_enode (n2id e) (canonicalize e (EAtom1 n)) (max_allocated e);
         id2s :=
           PTree.set (max_allocated e)
             (max_allocated e, T t,
             (PTree.Nodes (PTree.set0 n n),
             PTree.empty (PTree.t (eclass_id * eclass_id)))) 
             (id2s e)
       |} = Some c) in H1.
      pose proof (@found_high_in_updated _ _ _ _ _ _ H H0).
      pose proof (@found_high_in_updated _ _ _ _ _ _ H H1).
      destruct H2; destruct H3; cleanup'; try lia.
      eapply wt_egraph; eauto.
      {
        destruct f1; destruct f2; cleanup';
        cbn in *.
        inversion H6.
        inversion H6.
        inversion H6.
        inversion H5; inversion H4.
        subst.
        congruence.
      } 
    }
    {
        intros.
        destruct H.
        simpl in *.
        assert ( c < max_allocated e \/ c = max_allocated e) by  lia.
        destruct H.
        erewrite wf_uf0; lia.
        specialize (uf_id_outside0 c).
        rewrite uf_id_outside0.
        lia.
        lia.
    }
    Qed.

 (* Require Import Coq.Program.Equality. *)

  Ltac cleanup := cbn in *;intros;
  repeat match goal with
  | H: _ /\ _ |- _ => destruct H
  | H: _ <-> _ |- _ => destruct H
  | H: exists _, _  |- _ => destruct H
  | H: True  |- _ => clear H
  | H : ?a = ?b, H' : ?a = ?b |- _ => clear H'
  | H : ?P, H' : ?P |- _ =>
    let t := type of P in
    assert_succeeds(constr_eq t Prop);
    clear H'
  end.

  Lemma lookupF_eqf : forall {t} (f g : Formula t) e i,
    eqf f g = true ->
    lookupF f e = Some i ->
    lookupF g e = Some i.
    induction f.
    -
     destruct g; cbn.
      {
        intros.
        destruct (lookupF _ _) eqn:? in H0.
        2:{ inversion H0. }
        destruct (lookupF _ _) eqn:? in H0.
        2:{ inversion H0. }
        eapply Bool.andb_true_iff in H.
        cleanup.
        pose H.
        eapply eq_preserve_type in e2.
        inversion e2.
        subst.
        repeat auto_specialize.
        rewrite IHf1.
        rewrite IHf2.
        eauto.
      }
      { intros.  inversion H.  }
    -
     destruct g; cbn.
      (* { intros.  inversion H. } *)
      { intros.  inversion H.  }
      {
        intros.
        destruct t0.
        destruct t1.
        cbn in *.
        destruct (dt_eq' T0 T1) eqn:?; subst.
        eapply Pos.eqb_eq in H.
        subst.
        eauto.
        inversion H.
      }
  Qed.

  Lemma lookup_update_app1 :
  forall {t'} (f'  : Formula t') {t1 t3}
   newe
   (f1 : Formula t3) (f2 : Formula t1)
   e1 e3
   eid0 {new_id2s},
    (* lookupF (App2 f1 f2 f3) newe = None ->  *)
    lookupF f1 newe = Some e1 ->
    lookupF f2 newe = Some e3 ->
    invariant_egraph newe ->
    lookupF f' {| max_allocated := max_allocated newe + 1;
                 uf := uf newe;
                 n2id :=  add_enode (n2id newe) (EApp1 e1 e3) (max_allocated newe);
                 id2s := new_id2s |}
    = Some eid0 ->
    lookupF f' newe = Some eid0 \/
    (exists  (f'1 : Formula (t1 ~> t')) (f'2 : Formula t1)  ,
      lookupF f'1 newe = Some e1 /\
      lookupF f'2 newe = Some e3 /\
      eqf f' (App1 f'1 f'2) = true /\
      eid0 = max_allocated newe).
      Admitted.
      (* induction f'.
      2:{
        intros.
        cbn in *.
        left.
        unfold lookup.
        unfold add_enode in H2.
        cbn in *; eauto.
      }
      {
        intros.
        cbn in H2.
        specialize (IHf'1) with (1:= H).
        specialize (IHf'1) with (1:= H0).
        specialize (IHf'1) with (1:= H1).
        (* specialize (IHf'1) with (1:= H2). *)
        specialize (IHf'2) with (1:= H).
        specialize (IHf'2) with (1:= H0).
        specialize (IHf'2) with (1:= H1).
        (* specialize (IHf'2) with (1:= H2). *)
        repeat auto_specialize.
        cbn.
        destruct (lookupF f'1 _) eqn:? in H2.
        2:{
          inversion H2.
        }
        destruct (lookupF f'2 _) eqn:? in H2.
        2:{
          inversion H2.
        }
        repeat auto_specialize.
        destruct IHf'1.
        rewrite H3.
        destruct IHf'2.
        rewrite H4.
        {
          unfold update_map in H2.
          cbn in H2.
          subst.
          destruct (_&&_) eqn:? in H2.
          cbn in H2.
          pose proof (lookupF_canonical newe ) as canonicalLookup.
          auto_specialize.
          destruct H1.
          eapply Bool.andb_true_iff in Heqb.
          cleanup'.
          eapply Nat.eqb_eq in H1.
          eapply Nat.eqb_eq in H5.
          pose (canonicalLookup _ f1 e1) as e1_c.
          pose (canonicalLookup _ f2 e3) as e3_c.
          pose (canonicalLookup _ f'1 n) as e_c.
          pose (canonicalLookup _ f'2 n0) as e0_c.
          do 4 auto_specialize.
          rewrite e1_c in H1.
          rewrite e_c in H1.
          rewrite e3_c in H5.
          rewrite e0_c in H5.
          subst.
          pose proof (wt_egraph0 _ _ _ _ _ H H3) as luf1.
          pose proof (wt_egraph0 _ _ _ _ _ H0 H4) as luf2.
          cleanup'.
          subst.
          right.
          eexists; eexists.
          split.
          exact H3.
          split.
          exact H4.
          split.
          rewrite !eqf_refl.
          eauto.
          inversion H2.
          eauto.
          eauto.
        }
        {
          cleanup.
          rename H7 into reskj.
          unfold update_map in H2.
          subst.
          match type of Heqo0 with
          | lookupF ?a ?b = Some ?c =>
            assert (lookupF (App1 x x0) b = Some c)
          end.
          eapply lookupF_eqf; eauto.
          destruct (_ && _) eqn:? in H2.
          (* Destruction of H4 leads to one similar case for the false branch.  *)
          2:{
            destruct H1.
            specialize no_args_eapp1_outside0 with (1:= H2).
            cleanup'.
            unfold classIsCanonical in uf_id_outside0.
            unfold find in H8, uf_id_outside0; subst; cbn in *.
            erewrite uf_id_outside0 with (a := max_allocated newe) in H8; lia.
          }
          pose proof (lookupF_canonical newe ) as canonicalLookup.
          specialize (canonicalLookup H1).
          eapply Bool.andb_true_iff in Heqb.
          destruct Heqb.
          eapply Nat.eqb_eq in H8, H9.
          pose (canonicalLookup _ f2 e3) as e3_c.
          auto_specialize.
          rewrite e3_c in H9.
          pose proof (nobody_lookupF_outside newe H1 _ _ _ H0).
          destruct H1.
          unfold classIsCanonical in uf_id_outside0.
          unfold find in H9, uf_id_outside0.
          erewrite uf_id_outside0 in H9; cbn; try lia.
        }
        {
          cleanup.
          rename H6 into reskj.
          subst.
          match type of Heqo with
          | lookupF ?a ?b = Some ?c =>
            assert (lookupF (App1 x x0) b = Some c)
          end.
          eapply lookupF_eqf; eauto.
          destruct (_ && _) eqn:? in H2.
          (* Destruction of H4 leads to one similar case for the false branch.  *)
          2:{
            destruct H1.
            specialize no_args_eapp1_outside0 with (1:= H2).
            cleanup'.
            unfold classIsCanonical in uf_id_outside0.
            unfold find in H1, uf_id_outside0; subst; cbn in *.
            erewrite uf_id_outside0 with (a := max_allocated newe) in H1; lia.
          }
          pose proof (lookupF_canonical newe ) as canonicalLookup.
          specialize (canonicalLookup H1).
          eapply Bool.andb_true_iff in Heqb.
          destruct Heqb.
          eapply Nat.eqb_eq in H7, H8.
          pose (canonicalLookup _ f1 e1) as e1_c.
          auto_specialize.
          rewrite e1_c in H7.
          pose proof (nobody_lookupF_outside newe H1 _ _ _ H3).
          destruct H1.
          unfold classIsCanonical in uf_id_outside0.
          unfold find in H7, uf_id_outside0.
          erewrite uf_id_outside0 in H7; cbn; try lia.
        }
      }
      Qed. *)


  Lemma add_app1_safe: forall {t t1} e
  (f1 : Formula (t1 ~> t))
   (f2 : Formula t1)
    e1 e3 {new_id2s},
    invariant_egraph e ->
    lookupF f1 e = Some e1 ->
    lookupF f2 e = Some e3 ->
    invariant_egraph
      {| max_allocated := max_allocated e + 1;
         uf := uf e;
         n2id := add_enode (n2id e) (EApp1 e1 e3) (max_allocated e);
         id2s := new_id2s |}.
    Admitted.
    (* intros.
    econstructor.
    intros.
    pose proof @lookup_update_app1 as updf.
    (* specialize updf with (1:= H3). *)
    specialize updf with (1:= H0).
    specialize updf with (1:= H1).
    (* specialize updf with (1:= H2). *)
    specialize updf with (1:= H).
    specialize updf with (1:= H2).
    pose proof @lookup_update_app1 as updg.
    (* specialize updg with (1:= H3). *)
    specialize updg with (1:= H0).
    specialize updg with (1:= H1).
    (* specialize updg with (1:= H2). *)
    specialize updg with (1:= H).
    specialize updg with (1:= H3).
    destruct updf.
    {
      destruct updg.
      eapply H; eauto.
      cleanup'.
      pose proof (nobody_lookupF_outside _ H) as nobody_outside0.
      specialize (nobody_outside0) with (1:= H4).
      lia.
    }
    {
      cleanup'.
      pose H6.
      eapply eq_preserve_type in e0.
      subst.
      destruct updg.
      {
         pose proof (nobody_lookupF_outside _ H) as nobody_outside0.
         specialize (nobody_outside0) with (1:= H7).
         lia.
      }
      {
        cleanup.
        transitivity (interp_formula ctx (App1 x x0)).
        eapply eq_correct.
        eauto.
        transitivity (interp_formula ctx (App1 x1 x2 )).
        2:{
          symmetry.
          eapply eq_correct.
          eauto.
        }
        simpl.
        assert (interp_formula ctx x = interp_formula ctx x1).
        eapply H; eauto.
        assert (interp_formula ctx x0 = interp_formula ctx x2).
        eapply H; eauto.
        rewrite H11.
        rewrite H12.
        eauto.
      }
    }
    {
      cbn.
      intros.
      destruct a.
      cbn in *.
      destruct (_ && _) eqn:? in H2.
      inversion H2; subst; lia.
      destruct H.
      repeat auto_specialize.
      unfold find in no_args_eapp1_outside0.
      cleanup'.
      lia.
      destruct H.
      repeat auto_specialize.
      lia.
    }
    {
      unfold n2idCanonical.
      cbn.
      intros.

      destruct (_ && _) eqn:?.
      {
        eapply Bool.andb_true_iff in Heqb.
        cleanup'.
        eapply Nat.eqb_eq in H4.
        eapply Nat.eqb_eq in H3.
        unfold find in *.
        pose proof (@lookupF_canonical _ H  _ _ _ H0).
        pose proof (@lookupF_canonical _ H  _ _ _ H1).
        rewrite H5 in H3.
        rewrite H6 in H4.
        rewrite <- H3.
        rewrite <- H4.
        pose proof (nobody_lookupF_outside _ H).
        split; erewrite H7; eauto; lia.
      }
      subst.
      destruct H.
      unfold n2idCanonical in sanely_assigned_lookup0.
      cleanup'.
      try auto_specialize;
      unfold classIsCanonical in sanely_assigned_lookup0;
      eauto.
      specialize (no_args_eapp1_outside0 _ _ _ H2).
      cleanup'.
      rewrite H.
      rewrite H3.
      cbn; lia.
    }
    {
      unfold n2idCanonical.
      cbn.
      intros.
      destruct f.
      destruct (_ && _) eqn:?.
      {
        inversion H2.
        subst.
        cbn.
        destruct H.
        specialize (uf_id_outside0 (max_allocated e)).
        unfold classIsCanonical in *.
        cbn in *.
        unfold find in uf_id_outside0.
        erewrite uf_id_outside0; try lia.
      }
      {
        unfold classIsCanonical in *.
        cbn in *.
        destruct H.
        unfold n2idCanonical in *.
        specialize (sanely_assigned_lookup0 _ _ H2).
        eauto.
      }
      {
        unfold classIsCanonical in *.
        cbn in *.
        destruct H.
        unfold n2idCanonical in *.
        specialize (sanely_assigned_lookup0 _ _ H2).
        eauto.
      }
    }
    {
      cbn.
      intros.
      destruct H.
      eapply uf_id_outside0.
      lia.
    }
    {
      intros.
      cbn in *.
      pose proof (@found_high_in_updated _ _ _ _ _ _ H H2).
      pose proof (@found_high_in_updated _ _ _ _ _ _ H H3).
      destruct H4; destruct H5; cleanup'; try lia.
      eapply wt_egraph; eauto.
      {
        destruct f0; destruct f3; cleanup';
        cbn in *.
        2:{ inversion H6. }
        2:{ inversion H7. }
        2:{ inversion H7. }
        inversion H8; inversion H10.
        subst.
        destruct H.
        pose proof (@wt_egraph0 _ _ _ _ _ H7 H5).
        inversion H.
        eauto.
      }
    }
{
        intros.
        destruct H.
        simpl in *.
        assert ( c < max_allocated e \/ c = max_allocated e) by  lia.
        destruct H.
        erewrite wf_uf0; lia.
        specialize (uf_id_outside0 c).
        rewrite uf_id_outside0.
        lia.
        lia.
    }
    Qed. *)

    (* Another exam exercise:
     In this case we need to be careful to not make a statement too general
     that's something to have the student look for as well. *)
  Theorem lookup_already_there' :
    forall t  (f : Formula t) (e : egraph)  (e2 : eclass_id),
    lookupF f e = Some e2 ->
    add_formula e f = (e, e2).
    induction f.
    {
      intros.
      cbn in H.
      destruct (lookupF _ _) eqn:? in H.
      2:{ inversion H.  }
      destruct (lookupF _ _) eqn:? in H.
      2:{ inversion H.  }
      cbn.
      destruct (add_formula _ _) eqn:?.
      pose proof (IHf1 _ _ Heqo).
      assert (e0 = e4) by congruence.
      assert (e = e3) by congruence.
      subst.
      destruct (add_formula e3 f2) eqn:?.
      pose proof (IHf2 _ _ Heqo0).
      cleanup'.
      assert (e0 = e1) by congruence.
      assert (e = e3) by congruence.
      subst.
      subst.
      rewrite H.
      eauto.
    }
    {
      intros.
      cbn in *.
      rewrite H.
      eauto.
    }
    Qed.


  Lemma add_formula_safe : forall {t} (f : Formula t) e ,
    invariant_egraph e ->
    let '(newe, newal) := add_formula e f in
    invariant_egraph newe /\
    lookupF f newe = Some newal /\
    (forall t' (g : Formula t') old,
      (lookupF g e = Some old ->
       lookupF g newe = Some old) ).
       (* Admitted. *)
    induction f.
    2:{
      intros.
      pose proof @add_atom_safe.
      destruct (add_formula e0 _) eqn:?.
      repeat auto_specialize.
      specialize (H0 _ n e).
      rewrite Heqp in H0.
      eauto.
      remember (Atom1 n t0 e).
      cbn in *.
      assert (lookupF f e1 = Some e2).
      subst f.
      cbn in *.
      destruct (lookup e0 _) eqn:? in Heqp.
      {
      inversion Heqp.
      subst.
      eauto.
      }
      {
      inversion Heqp.
      subst.
      cbn.
      unfold lookup, Enodes.lookup, lookup' in Heqo |-*. 
      simpl in *.
      clear Heqp.
      unfold add_enode. 
      unfold lookup, Enodes.lookup, lookup'. 
      destruct (n2id e0).
      destruct (PTree.get _ _) eqn:? in Heqo.
      inversion Heqo.
      rewrite Heqo0.
      rewrite PTree.gss.
      simpl.
      destruct H.
      erewrite uf_id_outside0   by lia.
      eauto.
      }
      split; eauto.
      split; eauto.
      intros.
      subst.
      simpl in *.
      destruct (lookup e0 _) eqn:? in Heqp.
      {
        inversion Heqp.
        subst; eauto.
      }
      {
        inversion Heqp.
        subst.
        cbn in H1.
        pose proof @lookup_add_not_there.
        assert (lookup e0 (EAtom1 n ) = None).
        unfold lookup.
        cbn in *; eauto.
        epose proof (H3 _ _ _ _ _ _ H H4 H2 ).
        eauto.
      }
    }
    {
      intros.
      pose proof (IHf1 _ H ).
      destruct (add_formula e f1) eqn:?.
      cleanup'.
      pose proof (IHf2 _ H0).
      destruct (add_formula e0 f2) eqn:?.
      cleanup'.
      cleanup'.
      cbn - [eqf lookupF].
      rewrite Heqp.
      rewrite Heqp0.
      (* destruct (lookupF (App1 f1 f2) _) eqn:?; eauto. *)
      destruct (lookup e2 (EApp1 e1 e3)) eqn:?; eauto.
      2:{
        split.
        {
          pose lookupF_canonical.
          specialize c with (2:= H4). 
          specialize (c H3).
          rewrite c.
          specialize H5 with (1:= H1). 
          pose lookupF_canonical.
          specialize c0 with (2:= H5). 
          specialize (c0 H3).
          rewrite c0.
          pose proof @add_app1_safe; eauto.
        }
        split.
        {
          cbn.
          simpl in *.
          epose proof (@lookup_add_not_there _ f2 e2 (EApp1 e1 e3 ) e3 _ H3 Heqo H4).
          epose proof (@lookup_add_not_there _ f1 e2 (EApp1 e1 e3 ) e1 _ H3 Heqo (H5 _ _ _ H1)).
          rewrite H7.
          rewrite H6.
          unfold lookup, Enodes.lookup, lookup', add_enode in Heqo |-*.
          simpl.
          destruct (n2id e2) eqn:?.
          pose proof (H5 _ _ _ H1).
          pose proof (@lookupF_canonical _ H3 _ _ _ H8) as n_cano.
          pose proof (@lookupF_canonical _ H3 _ _ _ H4) as n0_cano.
          rewrite n_cano, n0_cano; eauto.
          simpl in *.
          unfold lookup, Enodes.lookup, lookup', add_enode in Heqo |-*.
          erewrite n_cano in Heqo.
          destruct (PTree.get _ _) eqn:? in Heqo.
          rewrite Heqo0 in *.
          erewrite n0_cano in Heqo.
          destruct (PTree.get _ _) eqn:? in Heqo.
          inversion Heqo.
          rewrite Heqo1.
          rewrite PTree.gss.
          rewrite PTree.gss.
          simpl.
          destruct H3.
          erewrite uf_id_outside0   by lia.
          intuition lia. 
          rewrite Heqo0.
          rewrite PTree.gss.
          rewrite PTree.gss.
          simpl.
          destruct H3.
          erewrite uf_id_outside0   by lia.
          intuition lia. 
        }
        {
          intros.
          pose proof  (H2 _ _ _ H6) as gint1.
          pose proof  (H5 _ _ _ gint1) as gint2.
          epose proof (@lookup_add_not_there _ g e2 (EApp1 e1 e3 ) old _ H3 Heqo gint2).
          eauto.
        } 
      }
      {
        split.
        {
          pose proof @add_app1_safe; eauto.
        }
        split.
        {
          cbn.
          rewrite H4.
          pose proof (H5 _ _ _ H1).
          rewrite H6.
          eauto.
        }
        {
          intros.
          eapply H5.
          eapply H2.
          eauto.
        }
      }
    }
    Qed. 


    Fixpoint substF {t t'} (e : egraph) (f : Formula t)
    (from : eclass_id)
    (to : Formula t') : Formula t.
    unshelve refine (let sub := _ in _).
    2:{
      destruct f.
      {
        pose (substF _ _ e f1 from to) as f'1 .
        pose (substF _ _ e f2 from to) as f'2 .
        exact (App1 f'1 f'2).
      }
      {
        exact (Atom1 n t0 e0).
      }
    }
    cbn in sub.
    destruct (dt_eq' t' t).
        {
          subst.
          destruct (lookupF sub e) .
          {
            destruct (Pos.eqb e0 from).
            {
              exact to.
            }
            exact sub.
          }
          {
            exact sub.
          }
        }
        {
          exact sub.
        }
    Defined.

    Lemma merge_helper : forall e,
    invariant_egraph e ->
    forall newe {t} (f1 : Formula t) (f2 : Formula t)
    (e1 e2 : eclass_id),
    lookupF f1 e = Some e1 ->
    lookupF f2 e = Some e2 ->
    merge e e1 e2 = newe ->
    forall  {t'} (f : Formula t') (e3 : eclass_id),
    lookupF f newe = Some e3 ->
    lookupF (substF e f e1 f2) e = Some e3.
    Admitted.
    (* intros.
    revert dependent f2.
    revert dependent f1.
    revert dependent e1.
    revert dependent e2.
    revert dependent e3.
    revert dependent f.
    induction f.
    {
      intros.
      (* pose proof H3 as init. *)
      simpl in H3.
      destruct (lookupF _ _) eqn:? in H3.
      2:{ inversion H3. }
      destruct (lookupF _ _) eqn:? in H3.
      2:{ inversion H3. }

      repeat auto_specialize.
      subst.

      (* H3 represente la classe dans l'egraph merge *)
      cbn in *.
      destruct (dt_eq' t td).
      2:{
        simpl.
        rewrite IHf1.
        rewrite IHf2.
        pose proof (@lookupF_canonical e H ) as H2.
        unfold merge,lookup, merge_n2id, Enodes.lookup, lookup' in H3 .
        simpl in H3.
        destruct (n2id e) eqn:? in H3.
        (* rewrite Heqm.
        simpl.
       
        (* erewrite (H2 _ _ _ IHf2) in H3;eauto. *)
        (* 2:{ inversion H3.  } *)
        pose proof (@lookupF_canonical _ H _ _ _ IHf1) as n_cano.
        pose proof (@lookupF_canonical _ H _ _ _ IHf2) as n2_cano.
        pose proof (@lookupF_canonical _ H _ _ _ H0) as n3_cano.
        pose proof (@lookupF_canonical _ H _ _ _ H1) as n4_cano.
        rewrite n3_cano in H3 .
        rewrite n4_cano in H3.
        rewrite n3_cano in H3.
        rewrite n2_cano.
        rewrite n_cano.
         *)
        (* destruct (Nat.eq_dec _ _); inversion H3; subst; eauto. *)
        assert (lookupF (App1 (substF e f1 e1 f3) (substF e f2 e1 f3)) e = Some e1).
        cbn.
        rewrite IHf1.
        rewrite IHf2.

        unfold merge,lookup, merge_n2id, Enodes.lookup, lookup' in H3 |-*.
        rewrite Heqm.
        simpl.
        destruct (PTree.get _ _) eqn:? in H3.
        2:{ inversion H3. }
        destruct (PTree.get _ _) eqn:? in H3.
        2:{ inversion H3. }
        simpl. unfold union,find in *|-.
        admit.
         (* rewrite n_cano.
        rewrite n2_cano.
        eauto. *)
        destruct H.
        specialize (wt_egraph0 _ _ _ _ _ H4 H0).
        contradiction n; eauto.
      }
      {
        destruct e5.
        cbn in *.
        rewrite IHf1, IHf2.
        pose proof (@lookupF_canonical e H ) as H2.
        epose (H2 _ _  _ IHf2).
        admit.
         (* in H3;eauto.
        destruct (n2id _ _) eqn:? in H3.
        2:{ inversion H3.  }
        {
          pose proof (@lookupF_canonical _ H _ _ _ IHf1) as n_cano.
          rewrite n_cano in Heqo1.
          destruct (Nat.eq_dec _ _) eqn:? in H3.
          subst.
          rewrite Heqo1.
          rewrite Heqs.
          inversion H3; subst; eauto.
          inversion H3; subst; eauto.
          rewrite Heqo1.
          rewrite Heqs.
          simpl.
          rewrite IHf1.
          rewrite IHf2.
          eauto.
        } *)
      }
    }
  {
      intros.
      (* pose proof H3 as init. *)
      simpl in H3.
      simpl.
      subst.

      (* H3 represente la classe dans l'egraph merge *)
      simpl in *.
      destruct t0.
      cbn.
      destruct (dt_eq' t T0).
      2:{
        simpl.
        (* unfold lookup, Enodes.lookup, lookup', merge, merge_n2id in *. *)
        simpl in *.
        eauto.
        destruct (n2id e ) eqn:? in H3;
        unfold lookup;
        cbn.
        rewrite Heqm.
        (* 2:{ inversion H3.  }
        destruct (Nat.eq_dec _ _ );
        inversion H3; subst; eauto. *)
        assert (lookupF (Atom1 n {| T:=T0; state:=state0 |} e0) e = Some e1) .
        cbn; unfold lookup; cbn; eauto.
        unfold Enodes.lookup, lookup'.
        rewrite Heqm.
        admit.
        destruct H.
        specialize (wt_egraph0 _ _ _ _ _  H2 H0).
        contradiction n0; eauto.
      }
      {
        destruct e4.
        cbn in *.
        unfold lookup,Enodes.lookup, lookup',merge  in *.
        simpl in*.
        destruct (n2id e) eqn:?.
        unfold lookup in *.

        unfold merge_n2id, lookup,Enodes.lookup, lookup',merge  in *.
        admit.
        (* 2:{ inversion H3.  }
        {
          cbn in *.
          rewrite Heqo.
          destruct (Nat.eq_dec _ _) eqn:? in H3.
          rewrite Heqs.
          inversion H3; subst; eauto.
          rewrite Heqs.
          simpl.
          inversion H3; subst; eauto.
        } *)
      }
    } *)
       (* Qed. *)

    Lemma subst_helper :
    forall {t'} (f : Formula t'),
    forall {t} (f1 : Formula t) (f2 : Formula t) e (e1 : eclass_id),
    invariant_egraph e ->
    interp_formula ctx f1 = interp_formula ctx f2 ->
    lookupF f1 e = Some e1 ->
    interp_formula ctx f = interp_formula ctx (substF e f e1 f2).
    Ltac t := subst; simpl; eauto.
    Admitted.
    (* induction f.
    - intros.
      repeat auto_specialize.
      simpl.
      rewrite  IHf1, IHf2.
      simpl.
      destruct (dt_eq' t0 td) eqn:?.
      2:{
        simpl.
        eauto.
      }
      destruct e0.
      simpl.
      remember (eq_rect_r  _ _ _ ).
      cbn in Heqy.
      remember (y f3).
      subst y.
      destruct (lookupF _ _) eqn:? in Heqf; try solve[ t ].
      destruct (lookupF _ _) eqn:? in Heqf; try solve[ t ].
      destruct (n2id _ _) eqn:? in Heqf; try solve [ t ].
      destruct (Nat.eq_dec _ _) eqn:? in Heqf; try solve [ t ].
      subst.
      rewrite <- H0.
      destruct H.
      erewrite (correct0 _ f0 (App1 (substF e f1 e1 f3) (substF e f2 e1 f3))).
      eauto.
      eauto.
      simpl.
      rewrite Heqo, Heqo0.
      eauto.
    -
      intros.
      simpl.
      destruct t0.
      cbn in *.
      destruct (dt_eq' t T0) eqn:?.
      2:{
        simpl.
        eauto.
      }
      destruct e2.
      remember (eq_rect_r _  _ _).
      remember (y f2).
      subst y.
      cbn in *.
      unfold lookup in *.
      cbn in *.
      destruct (n2id _ _) eqn:? in Heqf; try solve [ t ].
      destruct (Nat.eq_dec _ _) eqn:? in Heqf; try solve [ t ].
      subst.
      rewrite <- H0.
      destruct H.
      erewrite (correct0 _ f1 (Atom1 n {| T:= t; state := state0 |} e)).
      eauto.
      eauto.
      simpl.
      unfold lookup; cbn.
      eauto.
    Qed. *)

    Lemma type_preserved : forall {t1}  (f1 : Formula t1) {t2 t} (f g : Formula t)
          (f2 : Formula t2) e n0 n1 n2,
        invariant_egraph e ->
        lookupF f1 (merge e n0 n1) = Some n2 ->
        lookupF f2 (merge e n0 n1) = Some n2 ->
        lookupF f e = Some n0 ->
        lookupF g e = Some n1 ->
        t1 = t2.
          pose proof merge_helper as H.
          pose proof merge_helper as H434.
          intros.
          specialize H with (1:= H0).
          specialize H with (1:= H3).
          specialize H with (1:= H4).
          specialize H with (1:= eq_refl).
          specialize H with (1:= H1).
          specialize H434 with (1:= H0).
          specialize H434 with (1:= H3).
          specialize H434 with (1:= H4).
          specialize H434 with (1:= eq_refl).
          specialize H434 with (1:= H2).
          destruct H0.
          eapply wt_egraph0.
          eapply H.
          eapply H434.
    Qed.


  Theorem merge_preserve : forall {t} (e : egraph) (f g : Formula t),
    invariant_egraph e ->
    interp_formula ctx f = interp_formula ctx g ->
    let '(newe, before_merge_f, before_merge_g) := mergeF e f g in
    invariant_egraph newe.
    Admitted.
    (* intros.
    destruct (mergeF e f g) eqn:?.
    destruct p.
    econstructor.
    {
      intros.
      unfold mergeF in Heqp.
      (* unfold merge in Heqp. *)
      destruct (add_formula _ _) eqn:?.
      destruct (add_formula _ _) eqn:? in Heqp.
      inversion Heqp.
      pose proof @add_formula_safe.
      auto_specialize.
      specialize (H3 _ f).
      rewrite Heqp0 in H3.
      pose proof @add_formula_safe.
      cleanup'.
      auto_specialize.
      specialize (H7 _ g).
      rewrite Heqp1 in H7.
      cleanup'.
      pose proof merge_helper .
      pose proof @subst_helper.
      (* repeat auto_specialize. *)
      specialize (H12) with (1:= H7).
      specialize (H13) with (1:= H7).
      pose proof H13 as interpf .
      rename H13 into interpg .
      specialize (interpf) with (1:= H0).
      (* symmetry in H0. *)
      (* specialize (interpg) with (1:= H0). *)
      specialize (H12) with (3:= H4).
      assert (lookupF f e2 = Some n1) by eauto.
      assert (lookupF g e2 = Some n2) by eauto.
      (* specialize (H8 _ _ H9 H10). *)
      pose proof (H12 _ _ _ H13 H14 _ _ _ H1).
      pose proof (H12 _ _ _ H13 H14 _ _ _ H2).
      erewrite interpf.
      2:{ eauto.  }
      erewrite (interpf _ g0).
      2:{ eauto.  }
      eapply H7.
      eauto.
      eauto.
    }
    {
       intros.
      unfold mergeF in Heqp.
      (* unfold merge in Heqp. *)
      destruct (add_formula _ _) eqn:?.
      destruct (add_formula _ _) eqn:? in Heqp.
      inversion Heqp.
      pose proof @add_formula_safe.
      auto_specialize.
      specialize (H2 _ f).
      rewrite Heqp0 in H2.
      pose proof @add_formula_safe.
      cleanup'.
      auto_specialize.
      specialize (H6 _ g).
      rewrite Heqp1 in H6.
      cleanup'.
      subst.
      cbn in H1.
      destruct (n2id _ _ ) eqn:?.
      2:{ inversion H1. }
      destruct (Nat.eq_dec _ _) eqn:?.
      {
        inversion H1.
        subst.
        assert (lookupF g e2 = Some eid) by eauto.
        pose proof (@nobody_lookupF_outside  _ H6 _ _ _ H3).
        cbn.
        eauto.
      }
      cbn in *.
      destruct H6.
      inversion H1.
      subst.
      eapply nobody_outside0.
      eauto.
    }
    {
      intros.
      unfold mergeF in Heqp.
      (* unfold merge in Heqp. *)
      destruct (add_formula _ _) eqn:?.
      destruct (add_formula _ _) eqn:? in Heqp.
      inversion Heqp.
      pose proof @add_formula_safe.
      auto_specialize.
      specialize (H2 _ f).
      rewrite Heqp0 in H2.
      cleanup'.
      pose proof @add_formula_safe.
      auto_specialize.
      specialize (H8 _ g).
      rewrite Heqp1 in H8.
      subst.
      cbn.
      cleanup'.
      unfold union.
      repeat split.
      destruct (Nat.eq_dec _ _).
      {pose proof (nobody_lookupF_outside _ H3 _ _ _ H4).
      pose proof (@lookupF_canonical _ H3 _ _ _ H4).
      rewrite H9; lia.
      }
      {
      cbn in H1.
      destruct (n2id _ _ ) eqn:?.
      2:{ inversion H1. }
      destruct H3.
      specialize (no_args_eapp1_outside0 _ _ _ Heqo).
      cleanup'; eauto.
      pose proof (ge_dec e1 (max_allocated e4)).
      destruct H9.
      repeat auto_specialize.
      rewrite uf_id_outside0 in H3.
      rewrite uf_id_outside0 in H3.
      lia.
      assert (e1< max_allocated e4).
      lia.
      eapply wf_uf0; eauto.
      }
     destruct (Nat.eq_dec _ _).
     {
      pose proof (nobody_lookupF_outside _ H3 _ _ _ H4).
      pose proof (@lookupF_canonical _ H3 _ _ _ H4).
      rewrite H9; lia.
     }
     {
      cbn in H1.
      destruct (n2id _ _ ) eqn:?.
      2:{ inversion H1. }
      destruct H3.
      specialize (no_args_eapp1_outside0 _ _ _ Heqo).
      cleanup'; eauto.
      pose proof (ge_dec e2 (max_allocated e4)).
      destruct H9.
      repeat auto_specialize.
      rewrite uf_id_outside0 in H8.
      rewrite uf_id_outside0 in H8.
      lia.
      assert (e2< max_allocated e4).
      lia.
      eapply wf_uf0; eauto.
      }
    }
    {
      unfold mergeF in Heqp.
      (* unfold merge in Heqp. *)
      destruct (add_formula _ _) eqn:?.
      destruct (add_formula _ _) eqn:? in Heqp.
      inversion Heqp.
      pose proof @add_formula_safe.
      auto_specialize.
      specialize (H1 _ f).
      rewrite Heqp0 in H1.
      pose proof @add_formula_safe.
      cleanup'.
      auto_specialize.
      specialize (H5 _ g).
      rewrite Heqp1 in H5.
      cleanup'.
      subst.
      cbn.
      unfold n2idCanonical.
      simpl.
      intros.
      unfold classIsCanonical.
      simpl.
        destruct e1.
        pose proof (@lookupF_canonical _ H5).
        pose proof (nobody_lookupF_outside _ H5) as nobodyOutside.
        destruct H5.
        unfold n2idCanonical in sanely_assigned_lookup0.
        unfold union.
        cbn.
        unfold find.
        cbn.
        destruct (n2id _ _) eqn:? in H2.
        cbn in H2.
        2:{ inversion H2. }
        destruct (Nat.eq_dec (uf e2 n0) _) eqn:?.
        {
          destruct (Nat.eq_dec _ _) eqn:?.
          inversion H2.
          subst.
          assert (lookupF g e2 = Some c) by eauto.
          eapply H3; eauto.
          inversion H2.
          subst.
          unfold n2idCanonical in *.
          specialize (sanely_assigned_lookup0  _ _ Heqo).
          unfold classIsCanonical in sanely_assigned_lookup0.
          unfold find in sanely_assigned_lookup0.
          clear Heqs.
          rewrite sanely_assigned_lookup0 in e0.
          assert (lookupF f e2 = Some n0) by eauto.
          specialize (H3 _ _ _ H4).
          rewrite H3 in e0.
          congruence.
          (* unfold n2idCanonical in  *)
        }
        {
          destruct (Nat.eq_dec _ _) eqn:?.
          inversion H2.
          subst.
          assert (lookupF g e2 = Some c) by eauto.
          eapply H3; eauto.
          inversion H2.
          subst.
          eapply sanely_assigned_lookup0.
          eauto.
        }
    }
    {
      unfold mergeF in Heqp.
      (* unfold merge in Heqp. *)
      destruct (add_formula _ _) eqn:?.
      destruct (add_formula _ _) eqn:? in Heqp.
      inversion Heqp.
      pose proof @add_formula_safe.
      auto_specialize.
      specialize (H1 _ f).
      rewrite Heqp0 in H1.
      pose proof @add_formula_safe.
      cleanup'.
      auto_specialize.
      specialize (H5 _ g).
      rewrite Heqp1 in H5.
      cleanup'.
      subst.
      cbn.
      pose proof (@lookupF_canonical _ H5) as canonicalLookup.
      pose proof (nobody_lookupF_outside _ H5) as nobodyOutside.
      destruct H5.
      unfold union.
      intros.
      specialize (uf_id_outside0  _ H6).
      {
        unfold classIsCanonical.
        cbn.
        unfold union.
        destruct (Nat.eq_dec _ _) eqn:?.
        2:{
          unfold find.
          eauto.
        }
        unfold find in e0.
        clear Heqs.
        rewrite uf_id_outside0 in e0.
        assert (lookupF f e2  = Some n0) by eauto.
        specialize (canonicalLookup _ _ _ H2).
        rewrite canonicalLookup in e0.
        specialize (nobodyOutside _ _ _ H2).
        rewrite <- e0 in H6.
        cbn in H6.
        lia.
      }
    }
    {
      unfold mergeF in Heqp.
      (* unfold merge in Heqp. *)
      destruct (add_formula _ _) eqn:?.
      destruct (add_formula _ _) eqn:? in Heqp.
      inversion Heqp.
      pose proof @add_formula_safe.
      auto_specialize.
      specialize (H1 _ f).
      rewrite Heqp0 in H1.
      pose proof @add_formula_safe.
      cleanup'.
      auto_specialize.
      specialize (H5 _ g).
      rewrite Heqp1 in H5.
      cleanup'.
      subst.
      cbn.
      pose proof @type_preserved.
      eapply H2; eauto.
    }
    {
      unfold mergeF in Heqp.
      (* unfold merge in Heqp. *)
      destruct (add_formula _ _) eqn:?.
      destruct (add_formula _ _) eqn:? in Heqp.
      inversion Heqp.
      pose proof @add_formula_safe.
      auto_specialize.
      specialize (H1 _ f).
      rewrite Heqp0 in H1.
      pose proof @add_formula_safe.
      cleanup'.
      auto_specialize.
      specialize (H5 _ g).
      rewrite Heqp1 in H5.
      cleanup'.
      subst.
      cbn.
      unfold union.
      destruct (Nat.eq_dec _ _).
      (* destruct H5. *)
      eapply wf_uf; eauto.
      eapply (nobody_lookupF_outside); eauto.
      eapply wf_uf; eauto.
    }
    *)
  (* Qed. *)

Lemma apply_add_formula : forall {t} (f : Formula t) e newe,
    invariant_egraph e ->
    (fst (add_formula e f)) = newe ->
    invariant_egraph newe.
    pose proof @add_formula_safe.
    intros.
    repeat auto_specialize.
    specialize (H _ f).
    destruct (add_formula e f) eqn:?;
    cleanup'; eauto.
    cbn in H1; subst; eauto.
Qed.
Theorem apply_merge : forall {t} (e newe: egraph) (f g : Formula t),
    invariant_egraph e ->
    interp_formula ctx f = interp_formula ctx g ->
    (fst (fst (mergeF e f g)) = newe) ->
    invariant_egraph newe.
    pose proof @merge_preserve.
    intros.
    repeat auto_specialize.
    destruct (mergeF _ _ _) eqn:?;
    cleanup'; eauto.
    cbn in H2; subst; eauto.
    destruct p.
    eauto.
Qed.

End egraphs.

(* Note we need to make sure that types are uniquely put in the list, no duplicate! *)
(* Tests local:
En partant d'un egraph vide, ajouter quelques noeuds, et query le graph.
Voir si on peut reduire les ensembles d'une manière qui soit utilisable.

Voir si on peut reconstruire une Formula depuis un enode.
Grace au type deeply embedded, et la recursion sur les TArrows,
je crois qu'une telle recursion devcrait etre possible structurellement. *)
Lemma empty_invariant {typemap varmap}: invariant_egraph (typemap:=typemap) (ctx:=varmap) empty_egraph.
econstructor; firstorder.
{
  cbn in *.
  unfold empty_egraph in *.
  destruct f. cbn in H.
  destruct (lookupF _ _) eqn:? in H;
  try destruct (lookupF _ _) eqn:? in H.
  inversion H.
  inversion H.
  inversion H.
  cbn in H.
  inversion H.
}
Admitted.

Ltac cleanup' := intros;
  repeat match goal with
  | H: _ /\ _ |- _ => destruct H
  | H: _ <-> _ |- _ => destruct H
  | H: exists _, _  |- _ => destruct H
  | H: True  |- _ => clear H
  | H : ?a = ?b, H' : ?a = ?b |- _ => clear H'
  | H : ?P, H' : ?P |- _ =>
    let t := type of P in
    assert_succeeds(constr_eq t Prop);
    clear H'
  end.

Fixpoint propose_formula {typemap} {t}
   (ctx : asgn typemap) (e : egraph) (fuel : nat)
     (current_class : eclass_id) : option (Formula (ctx:=ctx) t).
  unshelve refine(match fuel with
  | 0 => None
  | S fuel =>
     match PTree.get current_class (id2s e) with
     | None => None
     | Some (eid, t', (atoms_candidates, eapp_candidates)) =>
      (* On essaie de trouver *)
      _
      
     end
  end).
  unshelve refine (let found_atoms := PTree.tree_fold_preorder(fun acc el => 
                          (_ : list (Formula (ctx:=ctx) t))) atoms_candidates nil in 
                          _).
  rename el into i.
  destruct (nth_error ctx ((Pos.to_nat i) - 1)) eqn:?.
  2:{ exact acc. }
  destruct s0 eqn:?.
  destruct (dt_eq' t T0).
  2:{ exact acc. }
  {
    rewrite <- Heqs1 in Heqo.
    rewrite e0 in *.
    replace T0 with (T s0).
    refine (cons _ nil).
    eapply (Atom1 i).
    eauto.
    rewrite Heqs1.
    reflexivity.
  }
  refine (match found_atoms with 
  | t ::q => Some t
  | _ => _ 
  end).
  unshelve refine (let found_eapp := PTree.tree_fold_preorder (fun acc el  => 
                          (_ : list (Formula (ctx:=ctx) t))) eapp_candidates nil  in 
                          _).
  refine (_ ++ acc).
  unshelve refine ( PTree.tree_fold_preorder (fun acc el => 
                          (_ : list (Formula (ctx:=ctx) t))) el nil
                          ).
  destruct el.
  refine ( match PTree.get e0 (id2s e), PTree.get e1 (id2s e) with
     | Some(eid1, TArrow arg _ret , _), Some (eid2, arg', _) => _
     | _, _ => nil
     end
  ).
  pose (propose_formula typemap (TArrow arg t) ctx e fuel e0).
  pose (propose_formula typemap arg ctx e fuel e1).
  destruct o.
  destruct o0.
  exact (cons (App1 f f0) nil).
  exact nil.
  exact nil.
  refine (match found_eapp with 
  | t ::q => Some t
  | _ => None
  end).
  Defined.


Notation "s" := (Atom1 _ {| T:= _; state := s|} _) (only printing, at level 5).
Notation "f g" := (App1 f g) (only printing, at level 10).
Ltac nodeAndTypeOfClass e n name :=
    let t := eval cbv in (id2s e n) in
    match t with
    | Some ?a => pose a as name
    end.
Ltac typeOfClass e n name :=
  let t := eval cbv in (id2s e n) in
  match t with
  | Some (_,?a) => pose a as name
  end.
Ltac formula_from_node ctx depth e n a :=
  let ta := fresh "type_" a in
  typeOfClass e n ta;
  match eval unfold ta in ta with
  | ?dt =>
    epose (propose_formula (t:= dt) ctx e depth n) as a;
    cbv in a; clear ta
  end.

Section Pattern.
  Context {typemap : list Type}.
  Context {quantifiermap : list (type )}.
  Inductive Pattern {ctx: asgn typemap} : type  -> Type :=
      | PApp1: forall {t td},
        Pattern (t ~> td) ->
        Pattern t ->
        Pattern td
      | PVar : forall (n : nat) {t0},
        EGraphList.nth_error quantifiermap n = Some t0 ->
        Pattern t0
      | PAtom1 : forall (n : positive) t0,
        EGraphList.nth_error ctx  ((Pos.to_nat n) - 1) = Some t0 ->
        Pattern (T t0).

  Context {ctx: asgn typemap}.

  (* The DeepList represents an instantiation of quantifiers, from the context,
     the values are Formulas from the context? *)
  Inductive DeepList : list (type ) -> Type :=
    | DCons : forall (t : type )
              (v : t_denote (typemap := typemap) t)
              {tcdr : list (type )} (cdr : DeepList tcdr),
      DeepList (t :: tcdr)
    | DNil : DeepList nil.

  Definition add_end {quantifiermap' :list (type )} (l : DeepList quantifiermap') {t : type }
  (* (v : Formula (ctx:= ctx) t)  *)
  (v : t_denote (typemap := typemap)t)
: DeepList (quantifiermap' ++ (cons t nil)).
  induction l.
  2:{
    simpl.
    econstructor.
    eauto.
    econstructor.
  }
  -
    econstructor.
    eauto.
    eauto.
    Defined.

  Definition app_d {quantifiermap1 :list (type )}
  (l1 : DeepList quantifiermap1) 

  {quantifiermap2 :list (type )}
  (l2 : DeepList quantifiermap2) 
: DeepList (quantifiermap1 ++ quantifiermap2).
  induction l1.
  2:{
    simpl.
    eauto.
  }
  {
    simpl.
    econstructor.
    eauto.
    eauto.
  }
  Defined.

  Definition deep_rev {quantifiermap' :list (type )} (l : DeepList quantifiermap')
: DeepList (rev quantifiermap').
  induction l.
  2:{
    simpl.
    econstructor.
  }
  -
    simpl.
    eapply add_end.
    eauto.
    eauto.
    Defined.


  Definition nth_deep {quantifiermap'} n t (pf : nth_error quantifiermap' n = Some t) 
      (l : DeepList quantifiermap') : t_denote (typemap := typemap)t.
  generalize dependent quantifiermap'.
  induction n.
  -
    intros.
    destruct quantifiermap'.
    inversion pf.
    simpl in *.
    inversion pf.
    subst.
    inversion l.
    exact v.
  -
    intros.
    destruct quantifiermap'.
    inversion pf.
    cbn in  pf.
    eapply IHn.
    exact pf.
    inversion l. exact cdr.
  Defined.

  Definition interp_pattern {t : type }
  (quantifiers: DeepList quantifiermap) (f : Pattern (ctx:= ctx) t) : t_denote (typemap := typemap)t.
  induction f.
  -
    cbn in *.
    eauto.
  -
    pose (nth_deep n t0 e quantifiers).
    exact t.
  - destruct t0.
    cbn.
    exact state0.
  Defined.


End Pattern.

Section TheoremGenerator.
  Context {typemap : list Type}.
  Context {ctx: asgn typemap}.

  (* Directly brought from Coq to avoid opacity issues *)
  Definition app_assoc' (A : Type) (l m n : list A):  l ++ m ++ n = (l ++ m) ++ n :=
  list_ind (fun l0 : list A => l0 ++ m ++ n = (l0 ++ m) ++ n)
    (let H : n = n := eq_refl in
     (let H0 : m = m := eq_refl in
    (let H1 : A = A := eq_refl in
       (fun (_ : A = A) (_ : m = m) (_ : n = n) => eq_refl) H1) H0) H)
    (fun (a : A) (l0 : list A) (IHl : l0 ++ m ++ n = (l0 ++ m) ++ n) =>
     let H : l0 ++ m ++ n = (l0 ++ m) ++ n := IHl in
     (let H0 : a = a := eq_refl in
      (let H1 : A = A := eq_refl in
       (fun (_ : A = A) (_ : a = a) (H4 : l0 ++ m ++ n = (l0 ++ m) ++ n) =>
        eq_trans
          (f_equal (fun f : list A -> list A => f (l0 ++ m ++ n)) eq_refl)
          (f_equal (cons a) H4)) H1) H0) H) l.

  Definition app_nil_r' :=
    fun (A : Type) (l : list A) =>
    list_ind (fun l0 : list A => l0 ++ nil = l0)
     (let H : A = A := eq_refl in (fun _ : A = A => eq_refl) H)
  (fun (a : A) (l0 : list A) (IHl : l0 ++ nil = l0) =>
   let H : l0 ++ nil = l0 := IHl in
   (let H0 : a = a := eq_refl in
        (let H1 : A = A := eq_refl in
     (fun (_ : A = A) (_ : a = a) (H4 : l0 ++ nil = l0) =>
      eq_trans (f_equal (fun f : list A -> list A => f (l0 ++ nil)) eq_refl)
        (f_equal (cons a) H4)) H1) H0) H) l.

  Fixpoint generate_theorem
    et
    (quantifiermap : list (type ))
    (quantifiermapdone : list (type ))
    (quantifiers : DeepList (typemap := typemap) quantifiermapdone)
    (clc1 : Pattern (quantifiermap := app (quantifiermapdone) quantifiermap) (ctx := ctx) et)
    (clc2 : Pattern (quantifiermap := app (quantifiermapdone) quantifiermap) (ctx := ctx) et)
    :
   Type
    .
    destruct quantifiermap.
    -
      rewrite <- app_nil_r' in quantifiers.
      exact (interp_pattern quantifiers clc1 = interp_pattern quantifiers clc2).
    -
      refine (forall (x : t_denote (typemap := typemap) d), _).
      simpl in clc1, clc2.
      change (d :: quantifiermap) with ((cons d nil) ++ quantifiermap) in clc1, clc2.
      rewrite app_assoc' in clc1, clc2.
      (* pose (generate_theorem et quantifiermap (d :: quantifiermapdone) (DCons d x quantifiers) clc1 clc2). *)
      pose (generate_theorem _ quantifiermap (quantifiermapdone ++ (cons d nil)) (add_end quantifiers x) clc1 clc2).
      exact T0.
    Defined.

 Definition generate_thm
     et
    (quantifiermap : list (type ))
    (clc1 : Pattern (quantifiermap := quantifiermap) (ctx := ctx) et)
    (clc2 : Pattern (quantifiermap := quantifiermap) (ctx := ctx) et) : Type .
    pose proof (generate_theorem et quantifiermap nil DNil clc1 clc2).
    exact X.
    Defined.

End TheoremGenerator.
Definition id_mark {T} (x : nat) (y :T) := y.

Ltac reify_forall n :=
   match goal with
  | [ |- forall (x : ?tx) , ?a] =>
    let x := fresh x in
    intro x;
    (* idtac "ok"; *)
    change x with (id_mark n x);
    reify_forall (S n)
    | _ => idtac
  end.

Ltac generate_cst u := lazymatch u with
| ?a -> ?b =>
  let v := generate_cst b in
  constr:(fun (x:a) => v)
| ?a => True
end.

Ltac get_quantifiers_t' t :=
  lazymatch t with
  | ?A -> ?B => constr:(True)
  | forall (x: ?T), @?body x =>
      constr:(forall (x: T), ltac:(
        let body' := eval cbv beta in (body x) in
        let r := get_quantifiers_t' body' in
        exact r))
  | _ => constr:(True)
  end.

Ltac get_quantifiers_aux t :=
  let __ := match O with | _ => idtac t end in
   lazymatch t with
  | ?tx -> ?a =>
  let __ := match O with | _ => idtac tx a "match" end in
    let rest := get_quantifiers_aux a in
    uconstr:((tx : Type)::rest)
    | _ => uconstr:(nil)
  end.
Ltac get_quantifiers H :=
  let H := type of H in

  (* idtac H; *)
  let t := get_quantifiers_t' H in
  let t := eval simpl in t in
  let __ := match O with | _ => idtac "Quantifiers" t end in
  let t := get_quantifiers_aux t in
  let __ := match O with | _ => idtac "PostQuantifiers" t end in
  t.


Notation "s" := (PAtom1 _ {| T:= _; state := s|} _) (only printing, at level 5).
Notation "f g" := (PApp1 f g) (only printing, at level 10).
Ltac ltac_map f tm l :=
  match l with
  | ?t :: ?q =>
    let newt := f tm t in
    let rest := ltac_map f tm q in
    uconstr:(newt::rest)
  | nil => uconstr:(nil)
  end.

Fixpoint max_t (t : type) :=
  match t with
  | `n => n
  | a ~> b => max (max_t a) (max_t b)
  end.
(* Lemma upcast_ok : forall t (varmap : type (typemap := t)), *)
    (* upcast_deeptype t [] varmap = varmap. *)
Definition app_nth1
  (A : Type) (l : list A) :
forall       (l' : list A) (d : A) (n : nat),
       n < length l -> nth n (l ++ l') d = nth n l d
  :=
list_ind
  (fun l0 : list A =>
   forall (l' : list A) (d : A) (n : nat),
   n < length l0 -> nth n (l0 ++ l') d = nth n l0 d)
  (fun (l' : list A) (d : A) (n : nat) (H : n < length nil) =>
   let H0 : length nil = length nil -> nth n (nil ++ l') d = nth n nil d :=
         match
       H in (_ <= n0)
       return (n0 = length nil -> nth n (nil ++ l') d = nth n nil d)
     with
     | le_n _ =>
         fun H0 : S n = length nil =>
         (fun H1 : S n = length nil =>
          let H2 : False :=
            eq_ind (S n)
              (fun e : nat => match e with
                              | 0 => False
                              | S _ => True
                              end) I (length nil) H1 in
          False_ind (nth n (nil ++ l') d = nth n nil d) H2) H0
     | le_S _ m H0 =>
         fun H1 : S m = length nil =>
         (fun H2 : S m = length nil =>
          let H3 : False :=
            eq_ind (S m)
              (fun e : nat => match e with
                              | 0 => False
                              | S _ => True
                              end) I (length nil) H2 in
          False_ind (S n <= m -> nth n (nil ++ l') d = nth n nil d) H3) H1 H0
     end in
   H0 eq_refl)
  (fun (a : A) (l0 : list A)
     (IHl : forall (l' : list A) (d : A) (n : nat),
            n < length l0 -> nth n (l0 ++ l') d = nth n l0 d)
     (l' : list A) (d : A) (n0 : nat) =>
   match
     n0 as n
     return
       (n < length (a :: l0) -> nth n ((a :: l0) ++ l') d = nth n (a :: l0) d)
   with
   | 0 => fun _ : 0 < S (length l0) => eq_refl
   | S n =>
       fun H : S n < S (length l0) =>
       IHl l' d n (gt_le_S n (length l0) (lt_S_n n (length l0) H))
   end) l
 .

Inductive Prod : Type -> Type -> Type :=
  | prod : forall {T T'} (x:T) (y : T'), Prod T T'.
Definition fstP {A B:Type} (x : Prod A B) := match x with
| prod f s => f
end.
Definition sndP {A B:Type} (x : Prod A B) := match x with
| prod f s => s
end.

Require Import Lia.
Definition travel_value :
forall (typemap : list Type) (t : type )
 typemap_extension,
 (max_t t) <? (length typemap) = true ->
 Prod ( t_denote (typemap := typemap ++ typemap_extension) t -> t_denote (typemap := typemap )t)
 (  t_denote (typemap := typemap )t -> t_denote (typemap := typemap ++ typemap_extension) t)
 .
 induction t.
 -
  simpl.
  intros;
  split.
  eapply Nat.ltb_lt in H.
  intros.
  pose proof app_nth1.
  specialize (H0) with (1:= H).
  specialize (H0 typemap_extension unit).
  rewrite H0 in X.
  eapply X.
  intros.
  eapply Nat.ltb_lt in H.

  pose proof app_nth1.
  specialize (H0) with (1:= H).
  specialize (H0 typemap_extension unit).
  rewrite H0.
  eapply X.
 -
  simpl.
  intros.
  eapply Nat.ltb_lt in H.
  assert (max_t t2 <? length typemap = true).
  eapply Nat.ltb_lt .
  lia.
  assert (max_t t1 <? length typemap = true).
  eapply Nat.ltb_lt .
  lia.
  pose proof (IHt2 typemap_extension H0).
  pose proof (IHt1 typemap_extension H1).
  inversion X.
  inversion X0.
  split.
  intros.
  eapply x.
  eapply X1.
  eapply y0.
  eapply X2.
  intros.
  eapply y.
  eapply X1.
  eapply x0.
  eapply X2 .
Defined.

Definition upcast_value :
forall (typemap : list Type) (t : type)
 typemap_extension,
 (max_t t) <? (length typemap) = true ->
 (t_denote (typemap := typemap )t -> t_denote (typemap := typemap ++ typemap_extension) t).
  intros.
  pose travel_value.
  specialize (p typemap t typemap_extension H).
  inversion p. eapply y. eapply X.
  Defined.

(* Definition upcast_varmap typemap typemap_extension
(varmap : list {f : SModule (typemap := typemap) & max_t (T f) <? length typemap = true})
 : list (SModule (typemap := typemap ++ typemap_extension)).
    refine (map (fun a => _ ) varmap).
    destruct a.
    pose( travel_value typemap (T x) typemap_extension e).
    inversion p.
    exact ({| T := _; state := y (state x) |}).
Defined. *)

Require Import Coq.Program.Equality.

Definition upcast_varmap typemap typemap_extension (varmap : list (SModule (typemap := typemap))) : list (SModule (typemap := typemap ++ typemap_extension)).
  induction varmap.
  -
    exact nil.
  -
    dependent destruction a.
    pose ((max_t T0 <? (length typemap))) .
    pose(travel_value typemap T0 typemap_extension).
    destruct b eqn:?.
    2:{ exact IHvarmap. }
    exact ({| T := _; state := (sndP (p Heqb0)) state0 |}::IHvarmap).
  Defined.

Ltac ltac_diff lbig lsmall :=
  (* let __ := match O with | _ => idtac "diffcompute" lbig lsmall end in *)
  match lbig with
  | ?t :: ?q =>
  match lsmall with
  | t :: ?r =>
  (* let __ := match O with | _ => idtac "find" t q r end in *)
        ltac_diff q r
  | nil => constr:(lbig)
  | _ => fail
  end
  | nil =>
  match lsmall with
  | nil => constr:(lsmall)
  | _ => fail
  end
  end.

Ltac listFromProp' tmap acc input_prop :=
  match input_prop with
  | id_mark ?n ?x =>
    acc
  | ?a ?b  =>
    lazymatch type of b with 
    | Prop => 
    let acc := listFromProp' tmap acc a in
    let acc := listFromProp' tmap acc b in
    acc
        | Type => fail
        | _ => 
    let acc := listFromProp' tmap acc a in
    let acc := listFromProp' tmap acc b in
    acc
    end
  | ?a =>
    let t := type of a in
    let deeply_represented := funToTArrow tmap t in
    let newa :=  eval cbv  [ Pos.add Pos.of_nat Pos.sub app_nth1 Init.Nat.max Nat.ltb Nat.leb length max_t upcast_value upcast_varmap travel_value generate_theorem interp_pattern eq_rect_r eq_rect eq_sym app_assoc' f_equal eq_trans list_ind nth_error nth_deep Pattern_rect nat_rect app rev list_rect type_rect type_rec] in (upcast_value tmap deeply_represented nil eq_refl a) in
    addList {| T := deeply_represented ; state := newa : (t_denote (typemap:= tmap) deeply_represented)|} acc
  end.
Ltac reify_prop' quantifiermap typemap varmap prop :=
match prop with
 | id_mark ?n ?x =>
 let s :=
 constr:(PVar (ctx:= varmap) (typemap:=typemap) (quantifiermap := quantifiermap) n eq_refl) in
 let __ := match O with | _ => idtac "newyo" end in
 s
 | ?a ?b =>
    lazymatch type of b with 
        | Prop => 
  let acc1 := reify_prop' quantifiermap typemap varmap a in
 (* let __ := match O with | _ => idtac "APPreify_prop'" acc1 b end in *)
  let acc2 := reify_prop' quantifiermap typemap varmap b in
 (* let __ := match O with | _ => idtac "APPreify_prop'" acc2 end in *)
  let res:= constr:(PApp1 (quantifiermap := quantifiermap) (typemap := typemap) acc1 acc2) in
 (* let __ := match O with | _ => idtac "APPreify_prop'" res end in *)
 res
        | Type => fail
        | _ => 
  let acc1 := reify_prop' quantifiermap typemap varmap a in
 (* let __ := match O with | _ => idtac "APPreify_prop'" acc1 b end in *)
  let acc2 := reify_prop' quantifiermap typemap varmap b in
 (* let __ := match O with | _ => idtac "APPreify_prop'" acc2 end in *)
  let res:= constr:(PApp1 (quantifiermap := quantifiermap) (typemap := typemap) acc1 acc2) in
 (* let __ := match O with | _ => idtac "APPreify_prop'" res end in *)
 res
 end
| ?a =>
  let t := type of a in
  (* let __ := match O with | _ => idtac "ATOMStartreify_prop'" a t end in *)
  let deeply_represented := funToTArrow typemap t in
  (* let __ := match O with | _ => idtac "ATOMStartreify_prop'" deeply_represented end in *)
  let newa :=  eval cbv  [  Pos.add Pos.of_nat Pos.sub app_nth1 Init.Nat.max Nat.ltb Nat.leb length max_t upcast_value upcast_varmap travel_value generate_theorem interp_pattern eq_rect_r eq_rect eq_sym app_assoc' f_equal eq_trans list_ind nth_error nth_deep Pattern_rect nat_rect app rev list_rect type_rect type_rec] in (upcast_value typemap deeply_represented nil eq_refl a) in
  (* idtac deeply_represented a varmap; *)
  let idx := indexList {| T := deeply_represented ; state := newa :(t_denote (typemap:= typemap) deeply_represented) |} varmap in
  (* let __ := match O with | _ => idtac "ATOMStartreify_prop'" idx end in *)
  let res :=   constr:(@PAtom1 typemap quantifiermap varmap (Pos.of_nat idx + 1) _ eq_refl) in
 (* let __ := match O with | _ => idtac "ATOMEndreify_prop'" idx res end in *)
 res

end.
(* 
Ltac reify_hyp H oldtypemap oldvarmap x :=
  idtac "start reify hyp";
  let oldtm := fresh "oldtm" in
  let oldvm := fresh "oldvm" in
  rename oldtypemap into oldtm;
  rename oldvarmap into oldvm;
  evar (oldtypemap : list Type);
  evar (oldvarmap : list (@SModule oldtypemap));
  let oldtm1 := eval unfold oldtm in oldtm in
  idtac "yo" oldtm1;
  evar (x : Type);
  let newassert := fresh "newassert" in
  let quan := get_quantifiers H in
  let quan := type_term quan in
  idtac quan;
  let t := type of H in assert t as newassert;
  reify_forall 0;
   [
  match goal with
  | [ |- ?a = ?b] =>
  idtac "start listTypes";
  let typemap := listTypesFromProp oldtm1 (a,b) in
  idtac "newtypemap" typemap;
  let diff := ltac_diff typemap oldtm1 in
  idtac "diff" diff;
  let oldtm' := eval unfold oldtypemap in oldtypemap in
  unify oldtm' typemap;
  pose typemap;
  idtac typemap;
  let deepify_quant := ltac_map funToTArrow typemap quan in
  let deepify_quant := type_term deepify_quant in
  let oldvm := eval unfold oldvm in oldvm in
  idtac "deepquant" deepify_quant oldtm1 diff oldvm;
  let oldvarmap' := constr:(upcast_varmap oldtm1 diff oldvm) in
  idtac "partial" oldvarmap';
  let oldvarmap' := eval cbv  [Pos.of_nat Pos.sub Pos.add app_nth1 Init.Nat.max Nat.ltb Nat.leb length max_t upcast_varmap travel_value generate_theorem interp_pattern eq_rect_r eq_rect eq_sym app_assoc' f_equal eq_trans list_ind nth_error nth_deep Pattern_rect nat_rect app rev list_rect type_rect type_rec] in oldvarmap' in
  idtac "reduced" oldvarmap';
  let varmap := listFromProp' typemap oldvarmap' (a, b) in
  idtac "newvarmap" varmap;
  let oldvm' := eval unfold oldvarmap in oldvarmap in
  unify oldvm' varmap;
  pose varmap;
  idtac "varmap" varmap;
  let reifedA := reify_prop' deepify_quant typemap varmap a in
  pose reifedA as A;
  let reifedB := reify_prop' deepify_quant typemap varmap b in
  pose reifedB as B;
  idtac "reifed" reifedA reifedB;
  let A':= eval unfold A in A in
  let B':= eval unfold B in B in
  let c := type of A in
  match c with
  | Pattern ?rett =>
  let T := fresh "newlemma" in
  let rett := eval simpl in rett in
    pose (generate_theorem (ctx:= varmap) (typemap := typemap) rett deepify_quant nil DNil
                                A' B') as T;
  let x' := eval unfold x in x in
  unify x' T ;
  eapply H
  end
  end
 |]; clear newassert
 ;
 subst oldtm;
 subst oldvm
 . *)
Ltac eta_collapse t :=
  match t with
  | context f[fun x => ?m x] =>
    context f[m]
  end.

Axiom (MYA : Type).
Axiom (pmya : MYA -> nat).
Goal ((forall x y ,  x + pmya y = pmya y + x)  -> (forall x y, x * y = y * x) -> True ).
  intros.
  pose (nil : list Type).
  pose (nil : list (SModule (typemap := l))).
  (* reify_hyp H l l0 myth. *)
  (* assert (myth ). *)
  (* exact H. *)
    admit.
  (* reify_hyp H0 l l0 y. *)
  (* Currently works but reverses the order in which it writes the quantifiers. *)
  (* clear y. *)
    Abort.

Section Potentials.
  Context {typemap : list Type}.
  Context {ctx: asgn typemap}.
  (* This structure represent a set of possible instantiation for the quantifiers,
  they might not have the right type? Is that a problem? Maybe I should add this constraint that all the element of the list represent nodes with the right type t *)
  (* Inductive DeepListPotentials : list (type ) -> Type :=
    | DConsF : forall (t : type )
              (v : list eclass_id)
              {tcdr : list (type )} (cdr : DeepListPotentials tcdr),
      DeepListPotentials (t :: tcdr)
    | DNilF : DeepListPotentials nil. *)
  Fixpoint dropNone {A:Type} (l : list (option A))  : list A :=
    match l with
    | Some a :: b => a :: dropNone b
    | _::b => dropNone b
    | _ => nil
    end.

  Inductive DeepList2 : list (type ) -> Type :=
    | DCons2 : forall (t : type )
              (v : Formula (ctx:= ctx) (typemap := typemap)t)
              {tcdr : list (type )} (cdr : DeepList2 tcdr),
      DeepList2 (t :: tcdr)
    | DNil2 : DeepList2 nil.

  Inductive DeepListEclass : list type -> Type :=
    | DConsE : forall (t:type) (v : option eclass_id) 
              {tcdr : list type} (cdr : DeepListEclass tcdr),
              DeepListEclass (t::tcdr)
    | DNilE : DeepListEclass nil .

  Definition FUEL := 30.
  Definition deeplist2_from_deeplisteclass (quant : list type)
    (instantiate_quant : DeepListEclass quant) (e : egraph) : option (DeepList2 quant).
  induction quant.
  {
    exact (Some DNil2).
  }
  {
    inversion instantiate_quant.
    specialize (IHquant cdr).
    unshelve refine (let potential :=
              match v with
              | Some id => (propose_formula (t:=t) ctx e FUEL id ) 
              | None => head (dropNone 
                  (map
                     (fun id => propose_formula (t:=t) ctx e FUEL (Pos.of_nat id))
                     (seq 0 (Pos.to_nat (max_allocated e)))))
              end in _).
    destruct IHquant.
    2:{ exact None. }
    destruct potential.
    econstructor.
    econstructor.
    rewrite H0 in f.
    exact f.
    exact d.
    exact None. 
  }
  Defined.

  (* Definition deeplist2_from_deeplistPotentials (quant : list (type ))
    (instantiate_quant : DeepListPotentials quant) (e : egraph) : list (DeepList2 quant).
  induction quant.
  {
    exact ([DNil2]).
  }
  {
    inversion instantiate_quant.
    specialize (IHquant cdr).
    unshelve refine (let potential := concat (map (fun x =>
                                    _ ) (dropNone (map (fun id => propose_formula (t:=t) ctx e FUEL id ) v )))in _).
    2:{
    unshelve refine (let newlist := map (fun x => _ : DeepList2 (a::quant)) IHquant in _).
    econstructor.
    rewrite H0 in x0.
    exact x0.
    exact x.
    exact newlist.
    }
    exact potential.
  }
  Defined. *)

  Definition deeplist_from_deeplist2 (quant : list (type ))
    (instantiate_quant : DeepList2 quant)  : (DeepList (typemap := typemap) quant).
  induction quant.
  {
    econstructor.
  }
  {
    inversion instantiate_quant.
    econstructor.
    eapply interp_formula; eauto.
    eauto.
  }
  Defined.


  Definition nth_deep' {quantifiermap' } n t (pf : nth_error quantifiermap' n = Some t) (l : DeepList2 quantifiermap')
   : Formula (ctx:=ctx) t.
  generalize dependent quantifiermap'.
  induction n.
  -
    intros.
    destruct quantifiermap'.
    inversion pf.
    simpl in *.
    inversion pf.
    subst.
    inversion l.
    exact v.
    (* exact (interp_formula ctx v). *)
  -
    intros.
    destruct quantifiermap'.
    inversion pf.
    cbn in  pf.
    eapply IHn.
    exact pf.
    inversion l. exact cdr.
  Defined.


End Potentials.

Require Import Coq.Program.Equality.

Lemma nth_deep2nth_deep' : forall  {typemap : list Type} quanttype ctx n t0 e0(X : DeepList2 quanttype) ,
      nth_deep n t0 e0 (deeplist_from_deeplist2 (ctx:=ctx) quanttype X )
       =
      interp_formula ctx (nth_deep' (typemap:=typemap) n t0 e0 X).
  induction quanttype.
  {
    simpl.
    intros.
    destruct n; inversion e0.
  }
  {
    induction n.
      intros.
    inversion e0.
    destruct H0.
    subst.
    destruct X eqn:?.
    2:{
      inversion e0.
    }
    simpl in e0.
    inversion X.
    inversion e0.
    subst.
    (* Here I could use my decidable equality to do that instead of Program Equality *)
    {
      dependent destruction e0.
      reflexivity.
    }
    intros.
    simpl in e0.
    (* Here it seems I would also need to lift a decidable equality... *)
    dependent destruction X.
    simpl (nth_deep' _ _ _ _).
    simpl (deeplist_from_deeplist2 _ _).
    unfold eq_rect_r, eq_rect.
    cbv [eq_sym].
    erewrite <- IHquanttype.
    reflexivity.
  }
  Defined.

  Fixpoint deep2_eqb {typemap : list Type} quanttype ctx (X Y: DeepList2 (typemap:=typemap) (ctx:= ctx) quanttype) : bool.
  dependent destruction X; dependent destruction Y.
  {
    pose (eqf v0 v).
    pose (deep2_eqb _ _ _ X Y).
    exact (b && b0).
  }
  { exact true. }
  Defined.

  Definition andb_true_iff  :=
(fun b1 b2 : bool =>
if b2 as b return (b1 && b = true <-> b1 = true /\ b = true)
then
 if b1 as b return (b && true = true <-> b = true /\ true = true)
 then
  conj (fun _ : true = true => conj eq_refl eq_refl)
    (fun H : true = true /\ true = true =>
     and_ind (fun _ _ : true = true => eq_refl) H)
 else
  conj (fun H : false = true => conj H eq_refl)
    (fun H : false = true /\ true = true =>
     and_ind (fun (H0 : false = true) (_ : true = true) => H0) H)
else
 if b1 as b return (b && false = true <-> b = true /\ false = true)
 then
  conj (fun H : false = true => conj eq_refl H)
    (fun H : true = true /\ false = true =>
     and_ind (fun (_ : true = true) (H1 : false = true) => H1) H)
 else
  conj (fun H : false = true => conj H H)
    (fun H : false = true /\ false = true =>
     and_ind (fun _ H1 : false = true => H1) H))
     : forall b1 b2 : bool, b1 && b2 = true <-> b1 = true /\ b2 = true.

  Lemma deep2_eqb_deeplist_from {typemap : list Type} quanttype ctx (X Y: DeepList2 (typemap:=typemap) (ctx:= ctx) quanttype) :
  deep2_eqb quanttype ctx X Y = true -> deeplist_from_deeplist2 quanttype X =  deeplist_from_deeplist2 quanttype Y.
    induction X.
    {
      dependent destruction Y.
      cbn [deep2_eqb].
      unfold solution_left, eq_rect_r, eq_rect, eq_sym, f_equal.
      intros.
      eapply andb_true_iff in H.
      destruct H.
      simpl.
      unfold solution_left, eq_rect_r, eq_rect, eq_sym, f_equal.
      pose @eq_correct .
      specialize (e) with (1:= H).
      rewrite e.
      f_equal.
      eapply IHX.
      eauto.
    }
    eauto.
  Defined.
  Definition nth_deep'' {quantifiermap' } (n : nat) (l : DeepListEclass quantifiermap')
   : option eclass_id.
  generalize dependent quantifiermap'.
  induction n.
  -
    intros.
    destruct quantifiermap'.
    exact None.
    inversion l.
    exact v.
  -
    intros.
    destruct quantifiermap'.
    exact None.
    inversion l. 
    eapply IHn.
    exact cdr.
  Defined.

  Definition change_nth_deep'' {quantifiermap' } (n : nat) (l : DeepListEclass quantifiermap') (e : eclass_id)
   : DeepListEclass quantifiermap'.
  generalize dependent quantifiermap'.
  induction n.
  -
    intros.
    destruct quantifiermap'.
    exact l.
    inversion l.
    econstructor.
    exact (Some e).
    eauto.
  -
    intros.
    destruct quantifiermap'.
    exact l.
    {
    inversion l. 
    econstructor.
    exact v.
    eapply IHn.
    exact cdr.
    }
  Defined.

(* I will do translation validation for hte match pattern, that will be the easiest.
Validator will simply return a boolean if the candidate matches the pattern and hence if the fn is correct *)
Definition no_constraints (quanttype : list type) : DeepListEclass quanttype.
  induction quanttype.
  econstructor.
  econstructor.
  exact None.
  exact IHquanttype.
Defined.
(* forall x y z, f (g ?x ?y) ?x *)
(* (0 ( _))
   (42 (_ _)) *)
(* (_ (_ _ _ _)) *)
Definition init_consider (quanttype : list type) (e:egraph): list (Prod eclass_id (DeepListEclass quanttype)).
(* TODO seq on el *)
  exact (map (fun el => prod (Pos.of_nat el) (no_constraints quanttype)) (seq 0 (Pos.to_nat (max_allocated e)))).
Defined.
Section MiniTEsts.
Import EGraphList.ListNotations.

Open Scope list_scope.
Definition test0 := [`0; `0].
Definition in0 := no_constraints test0.

Compute (change_nth_deep'' 0 in0 2%positive).
Compute (change_nth_deep'' 0 (change_nth_deep'' 0 in0 2%positive) 3%positive).
Compute (change_nth_deep'' 1 (change_nth_deep'' 0 in0 2%positive) 3%positive).
Compute (nth_deep'' 0 (change_nth_deep'' 1 (change_nth_deep'' 0 in0 2%positive) 3%positive)).
Compute (nth_deep'' 1 (change_nth_deep'' 1 (change_nth_deep'' 0 in0 2%positive) 3%positive)).
End MiniTEsts.

Fixpoint match_pattern_aux' {typemap : list Type} (fuel : nat) ctx (quanttype : list type)
(e : egraph )
(to_consider : list (Prod eclass_id (DeepListEclass quanttype)))
t (p : Pattern (typemap:=typemap) (ctx:=ctx) (quantifiermap:=quanttype) t) :
list (Prod eclass_id (DeepListEclass quanttype)).
  refine (match p with 
  | PApp1 p1 p2 => _
  | PVar n eq => _
  | PAtom1 n t eq => _
  end).
  {
    (* Filter the enodes such that they are of the form EApp1 ... *)
    unshelve refine (let new_consider := concat (map (fun el => _ : list (Prod eclass_id (DeepListEclass quanttype))) to_consider) in _).
    2:{
      exact new_consider.
    }
    pose (PTree.get (fstP el) (id2s e)).
    destruct o.
    2:{
      exact nil.
    }
    destruct p0.
    destruct s.
    pose (PTree.tree_fold_preorder (fun acc mid  => 
            PTree.tree_fold_preorder (fun acci '(fnbody, arg) => 
                    match_pattern_aux' typemap fuel ctx quanttype e (cons (prod fnbody (sndP el)) nil) _ p1
                    ++ acci
                  ) mid acc
            ) t1 nil ) as post_fn_body.
            rename el into el_old.
    unshelve refine (let post_arg := 
              map (fun elret =>  _: list (Prod eclass_id (DeepListEclass quanttype))) post_fn_body in _). 
    2:{ exact (concat post_arg) . }
    pose (PTree.get (fstP elret) t1).
    destruct o.
    2:{ exact nil. }
    exact (PTree.tree_fold_preorder (fun acci '(fnbody,arg)=> 
                    (map (fun el => 
                       prod (fstP el_old) (sndP el)) 
                        (match_pattern_aux' typemap fuel ctx quanttype e (cons (prod arg (sndP elret)) nil) _ p2)) ++ acci
                  ) t2 nil
            ).
  }
  2:{
    refine(dropNone (map (fun X => _) to_consider)).
    unshelve refine (let id_atom2 := lookup e (EAtom1 n) in _).
    destruct id_atom2.
    destruct ((e0 =? find (uf e) (fstP X))%positive).
    exact (Some X).
    exact None.
    exact None.
  }
  {
    refine (dropNone (map (fun X => _) to_consider)).
    (* There we have one concrete enode, we want to look it up,
    and then either it is the same as the one in the assignemnt map,  we can keep the assignemnt and then entry,
    or it is not in the assignment map, then we add it and we keep this entry, or it is inconsistent with the current assignment, then we die.  *)
    pose (nth_deep'' n (sndP X)).
    destruct o.
    2:{ exact (Some (prod (fstP X) (change_nth_deep'' n (sndP X) (fstP X)))). }
    destruct ((find (uf e) e0 =? find (uf e) (fstP X))%positive) eqn:?.
    exact (Some X).
    exact None.
  }
  Defined.

Definition match_pattern_aux {typemap : list Type} (fuel : nat) ctx (quanttype : list type)
(e : egraph )
t (p : Pattern (typemap:=typemap) (ctx:=ctx) (quantifiermap:=quanttype) t) :
list (Prod eclass_id (DeepListEclass quanttype)).
exact (match_pattern_aux' fuel ctx quanttype e (init_consider quanttype e) t p).
Defined.

Definition match_pattern {typemap : list Type} (fuel : nat) ctx (quanttype : list type)
(* Need to improve this function ... *)
(e : egraph)
t (p : Pattern (ctx:=ctx) (quantifiermap:=quanttype) t) :
list 
   (Prod (Formula (ctx:=ctx) t) (DeepList2 (typemap:=typemap) (ctx:=ctx) quanttype)):=
  dropNone (map (fun x => match propose_formula (t := t) ctx e fuel (fstP x) , (deeplist2_from_deeplisteclass quanttype (sndP x) e) with
                        | Some f, Some l => Some (prod f l)
                        | _, _=> None
                      end) (match_pattern_aux fuel ctx quanttype e t p)).
(* 
Fixpoint matc{typemap : list Type} (fuel : nat) ctx (quanttype : list type)
(* Need to improve this function ... *)
(e : egraph ) 
(to_consider : DeepListPotentials quanttype) t (p : Pattern (ctx:=ctx) (quantifiermap:=quanttype) t) :
list 
   (Prod (Formula (ctx:=ctx) t) (DeepList2 (typemap:=typemap) (ctx:=ctx) quanttype)).
  refine (match p with 
  | PApp1 p1 p2 => _
  | PVar n eq => _
  | PAtom1 n t eq => _
  end).
  {
    simpl.
    refine (let partial := concat (map (fun arg => dropNone (map (fun fn =>
                ?[internal]) (match_pattern typemap fuel ctx quanttype e to_consider _ p1))) 
               (match_pattern typemap fuel ctx quanttype e to_consider _ p2) 
                ) in partial).
    unshelve instantiate (internal:=_).
    pose (App1 (fstP fn) (fstP arg)).
    (* pose (lookupF f e).
    destruct o.
    2:{
      exact None.
    } *)
    destruct (deep2_eqb _ _ (sndP fn) (sndP arg)) eqn:?.
    2:{
      exact None.
    }
    refine (Some _).
    refine (prod f _).
    exact (sndP arg).
  }
  {
    pose (deeplist2_from_deeplistPotentials (ctx:=ctx) _ to_consider e) as partial_result.
    refine(map (fun X => _) partial_result).
    pose (nth_deep' n d eq X).
    exact (prod f X).
  }
  {
    pose (deeplist2_from_deeplistPotentials (ctx:=ctx) _ to_consider e) as partial_result.
    refine(map (fun X => _) partial_result).
    refine (prod (Atom1 _ _ _) X).
    simpl.
    eauto.
  }
  Defined. *)

Lemma in_dropNone:
  forall [A : Type] (l : list (option A)) (y : A),
  In y (dropNone l) <-> ( In (Some y) l ).
    induction l.
    {
      simpl.
      firstorder.
    } 
    {
      simpl.
      intros.
      destruct a.
      split.
      {
        intros.
        inversion H.
        left.
        rewrite H0.
        reflexivity.
        right.
        eapply IHl.
        eauto.
      }
      {
        intros.
        destruct H.
        inversion H.
        econstructor; eauto.
        simpl.
        right; eauto.
        eapply IHl; eauto.
      }
      split.
      {
        intros.
        right.
        eapply IHl.
        eauto.
      }
      {
        intros.
        destruct H.
        inversion H.
        eapply IHl; eauto.
      }
    }
    Defined.


(* The goal of this function is to make sure that the eclass returned follows the pattern prescribed.
If yues it should be the case that 
Lemma validator_matcher_correct {typemap : list Type} (fuel : nat) ctx (quanttype : list type)
(e : egraph) 
t (p : Pattern (ctx:=ctx) (quantifiermap:=quanttype) t) 
(input : Prod eclass_id (DeepListEclass quanttype)) 
(pf : validator_matcher fuel ctx quanttype e t p input = true) :
match propose_formula ctx e fuel (fstP input), deeplist2_from_deeplisteclass quanttype (sndP input) e with
| Some f, Some quantifiers => 
  interp_pattern (ctx:= ctx) (typemap := typemap) (deeplist_from_deeplist2 (ctx:=ctx) quanttype quantifiers) p
  =
  interp_formula ctx f
| _, _ => True
end.
induction p. *)
 


(* Ideally, The following function is generating a list of matches for the pattern in the egraph. *)
(* For now,
  The following function is generating potentially of matches for the pattern in the egraph. *)
Lemma match_pattern_correct :
  forall {typemap : list Type} (fuel : nat) ctx (quanttype : list type)
  (e : egraph )  t (p : Pattern t),
  Forall 
    (fun f =>
          interp_pattern (ctx:= ctx) (typemap := typemap)
              (deeplist_from_deeplist2 (ctx:=ctx) quanttype (sndP f)) p
          =
          interp_formula ctx (fstP f))
    (match_pattern fuel ctx quanttype e t p). 
  (* induction p.
  {
    eapply Forall_forall.
    intros.
    unfold match_pattern_aux in H.
    unfold match_pattern_aux' in H.
    unfold match_pattern in H.
    eapply in_dropNone in H.
    eapply in_map_iff in H.
    destruct H.
    destruct H.
    destruct propose_formula eqn:? in H.
    2:{ inversion H. }
    destruct deeplist2_from_deeplisteclass eqn:? in H.
    2:{ inversion H. }
    inversion H.
    subst.
    clear H.
    cbn in H0.
     (* destruct (PTree.get _ _) eqn:? in H.
    2:{ subst x0. inversion H0. }
    destruct p. destruct s.
    subst x0. *)
    eapply in_concat in H0.
    destruct H0.
    destruct H.
    eapply in_map_iff in H.
    destruct H.
    destruct (PTree.get _ _) eqn:? in H.
    2:{ destruct H. subst x. inversion H0. }
    destruct H.
    subst x.
    destruct p.
    destruct s.
    (* eapply in_dropNone in H.
    (* destruct H. *)
    (* destruct H. *)
    destruct H.
    destruct H.
    unfold match_pattern_aux in H0.
    simpl in H0. *)
    eapply in_concat in H0.
    destruct H0.
    destruct H.
    eapply in_map_iff in H.
    destruct H.
    destruct H.
    rewrite <- H in *.
    clear H.
    admit.
    (* destruct H0.
    destruct H.
    destruct (lookupF _ _) eqn:?.
    2:{ inversion H. }
    destruct (lookupF (fstP x1) _) eqn:?.
    2:{ inversion H. }
    destruct (n2id e _) eqn:?.
    2:{ inversion H. }
    destruct (deep2_eqb _ _ _ _) eqn:?.
    2:{ inversion H. }
    inversion H.
    simpl in *. *)
    (* eapply Forall_forall in IHp2.
    2:{ eauto. }
    eapply Forall_forall in IHp1.
    2:{ eapply H0. }
    rewrite IHp2.
    eapply deep2_eqb_deeplist_from  in Heqb.
    rewrite <- Heqb.
    rewrite IHp1.
    eauto.  *)
  }
  {
    cbn - [propose_formula].
    eapply Forall_forall.
    intros.
    eapply in_dropNone in H.
    eapply in_map_iff in H.
    destruct H.
    destruct H.
    eapply in_dropNone in H0.
    eapply in_map_iff in H0.
    destruct H0.
    destruct H0.
    destruct (nth_deep'' _ _) eqn:? in H0.
    destruct (_ =? _)%positive eqn:? in H0.
    2:{ inversion H0. }
    inversion H0.
    subst.
    clear H0.
    destruct (propose_formula _ _ _ _) eqn:? in H.
    2:{inversion H. }
    destruct (deeplist2_from_deeplisteclass _ _ _) eqn:? in H.
    2:{ inversion H. }
    inversion H.
    subst.
    clear H.
    simpl.
    admit.
    
  }
  {
    simpl.
    eapply Forall_forall.
    intros.
    unfold match_pattern in H.
    eapply in_dropNone in H.
    eapply in_map_iff in H.
    destruct H.
    destruct H.
    destruct (propose_formula _ _ _ _) eqn:? in H.
    2:{inversion H. }
    destruct (deeplist2_from_deeplisteclass _ _ _) eqn:? in H.
    2:{ inversion H. }
    inversion H.
    subst; clear H.
    destruct t0.
    simpl.
    admit.
   
  } *)
    Admitted.
(* Lemma match_pattern_correct :
  forall {typemap : list Type} (fuel : nat) ctx (quanttype : list type)
  (e : egraph ) (to_consider : list(DeepList2 quanttype)) t (p : Pattern t),
  Forall 
    (fun f =>
          interp_pattern (ctx:= ctx) (typemap := typemap)
              (deeplist_from_deeplist2 (ctx:=ctx) quanttype (sndP f)) p
          =
          interp_formula ctx (fstP f))
    (match_pattern fuel ctx quanttype e to_consider t p).
    Admitted. *)
  (* induction p.
  {
    simpl.
    eapply Forall_forall.
    intros.
    eapply in_concat in H.
    destruct H.
    destruct H.
    eapply in_map_iff in H.
    destruct H.
    destruct H.
    rewrite <- H in *.
    clear H.
    eapply in_dropNone in H0.
    eapply in_map_iff in H0.
    destruct H0.
    destruct H.
    destruct (lookupF _ _) eqn:?.
    2:{ inversion H. }
    destruct (lookupF (fstP x1) _) eqn:?.
    2:{ inversion H. }
    destruct (n2id e _) eqn:?.
    2:{ inversion H. }
    destruct (deep2_eqb _ _ _ _) eqn:?.
    2:{ inversion H. }
    inversion H.
    simpl in *.
    eapply Forall_forall in IHp2.
    2:{ eauto. }
    eapply Forall_forall in IHp1.
    2:{ eapply H0. }
    rewrite IHp2.
    eapply deep2_eqb_deeplist_from  in Heqb.
    rewrite <- Heqb.
    rewrite IHp1.
    eauto.
  }
  {
    simpl.
    eapply Forall_forall.
    intros.
    eapply in_map_iff in H.
    destruct H.
    destruct H.
    rewrite <- H in *.
    simpl in *.
    eapply nth_deep2nth_deep'.
  }
  {
    simpl.
    eapply Forall_forall.
    intros.
    eapply in_map_iff in H.
    destruct H.
    destruct H.
    rewrite <- H in *.
    simpl in *.
    eauto.
  }
  Qed. *)
  

  Definition pattern_to_formula {typemap ctx quantifiermap} {t : type }
  (quantifiers: DeepList2 (ctx:=ctx) (typemap := typemap)quantifiermap) (f : Pattern (quantifiermap:=quantifiermap) (ctx:= ctx) t) : Formula (ctx:=ctx) t.
  induction f.
  -
    eapply App1; eauto.
  -

    pose (nth_deep' n t0 e quantifiers).
    exact f.
  - 
    eapply (Atom1 n ).
    eauto.
  Defined.


Definition lift_ctx (tm tm_ext : list Type)
  (ctx : asgn tm) (ctx_ext: asgn (tm ++ tm_ext)) : asgn (tm ++ tm_ext).
      pose (upcast_varmap tm tm_ext ctx).
      unfold asgn in *.
      exact (l ++ ctx_ext).
Defined.

Lemma use_bool_true  : forall {RET : Type}
  (y : bool)
  (t1 : y = true -> RET)
  (t2 : y = false -> RET)
  (pf : y = true),
  (if y as b return y = b -> RET
      then (fun Ht => t1 Ht)
      else (fun Hf => t2 Hf)) eq_refl
  = t1 pf.
  intros.
  destruct y.
  {
    dependent destruction pf.
    reflexivity.
  }
  inversion pf.
Defined.

Lemma use_bool_false  : forall {RET : Type}
  (y : bool)
  (t1 : y = true -> RET)
  (t2 : y = false -> RET)
  (pf : y = false),
  (if y as b return y = b -> RET
      then (fun Ht => t1 Ht)
      else (fun Hf => t2 Hf)) eq_refl
  = t2 pf.
  intros.
  destruct y.
  inversion pf.
  {
    dependent destruction pf.
    reflexivity.
  }
Defined.

Lemma lift_nth_error : forall n tm tmext ctx newctx t0
    (pf : forallb (fun el => max_t (T el) <? length tm) ctx  = true)
    (pf_inside : max_t (T t0) <? length tm = true),
  nth_error ctx n = Some t0 ->
  nth_error
      (@lift_ctx tm tmext ctx newctx) n =
    Some
      {| T:= _; state := sndP (travel_value tm (T t0) tmext pf_inside) (state t0) |}.
      induction n .
      {
        intros; destruct ctx; simpl in *; inversion H.
        unfold lift_ctx.
        unfold upcast_varmap.
        destruct t0.
        simpl in *.
        subst.
        unshelve erewrite use_bool_true ; eauto.
      }
      {
        simpl.
        intros.
        destruct ctx eqn:?.
        inversion H.
        simpl in pf.
        eapply andb_true_iff in pf.
        destruct pf.
        erewrite <- IHn.
        3:{ exact H. }
        unfold lift_ctx at 1.
        unfold upcast_varmap.
        simpl in *.
        destruct s.
        unshelve erewrite use_bool_true. exact H0.
        simpl.
        reflexivity.
        eauto.
      }
    Defined.

(* Fixpoint supermap (A B : Type) (l : list A) (f: forall (x:A), In x l -> B) : list B. *)
Definition forallb_forall
 {A : Type} (f : A -> bool) (l : list A):=
list_ind
  (fun l0 : list A =>
   forallb f l0 = true <-> (forall x : A, In x l0 -> f x = true))
  (conj (fun (_ : true = true) (x : A) (H0 : False) => False_ind (f x = true) H0)
     (fun _ : forall x : A, False -> f x = true => eq_refl))
  (fun (a : A) (l0 : list A)
     (IHl : forallb f l0 = true <-> (forall x : A, In x l0 -> f x = true)) =>
   conj
     (fun H : f a && forallb f l0 = true =>
      let a0 : f a = true /\ forallb f l0 = true :=
        andb_prop (f a) (forallb f l0) H in
      match a0 with
      | conj H0 H1 =>
          fun (a' : A) (H2 : a = a' \/ In a' l0) =>
          match H2 with
          | or_introl H3 =>
              eq_trans
                (eq_trans (f_equal (fun f0 : A -> bool => f0 a') eq_refl)
                   (f_equal f (eq_sym H3)))
                (eq_trans H0 (eq_trans (eq_sym H1) H1))
          | or_intror H3 =>
              let H4 :
                forallb f l0 = true -> forall x : A, In x l0 -> f x = true :=
                match IHl with
                | conj x _ => x
                end in
              H4 H1 a' H3
          end
      end)
     (fun H : forall x : A, a = x \/ In x l0 -> f x = true =>
      andb_true_intro
        (conj (H a (or_introl eq_refl))
           (let H0 :
              (forall x : A, In x l0 -> f x = true) -> forallb f l0 = true :=
              match IHl with
              | conj _ x0 => x0
              end in
            H0 (fun (x : A) (H1 : In x l0) => H x (or_intror H1)))))) l
     :
       forallb f l = true <-> (forall x : A, In x l -> f x = true).


Fixpoint pattern_from_formula 
  {typemap t_quantifiermap ctx t}
  (f : Formula (typemap := typemap) (ctx := ctx) t)
  : @Pattern typemap t_quantifiermap ctx t.
  destruct f.
  {
    eapply (PApp1 (pattern_from_formula _ _ _ _ f1) (pattern_from_formula _ _ _ _ f2)).
  }
  {
    eapply PAtom1.
    eauto.
  }
Defined.

Fixpoint app_pattern {typemap t_quantifiermap ctx et t0} 
  (replacement_term : Formula (ctx:=ctx) t0) 
  (p : @Pattern typemap (t0::t_quantifiermap) ctx et) :
  @Pattern typemap t_quantifiermap ctx et.
  induction p.
  {
    eapply (PApp1 
        (app_pattern _ _ _ _ _ replacement_term p1) 
        (app_pattern _ _ _ _ _ replacement_term p2)).
  }
  {
    destruct n.
    {
      simpl in *.
      inversion e.
      clear e.
      subst.
      eapply pattern_from_formula.
      auto.
    }
    {
      simpl in e.
      eapply PVar.
      eapply e.
    }
  }
  {
    eapply PAtom1.
    eapply e.
  }
  Defined.

Lemma interp_pattern_from_formula :  
forall {typemap ctx t0 }
(v : Formula (typemap := typemap) (ctx:=ctx) t0),
interp_formula ctx v = interp_pattern DNil (pattern_from_formula v).
  induction v.
  {
    simpl.
    rewrite IHv1.
    rewrite IHv2.
    reflexivity.
  }
  {
    simpl.
    reflexivity.
  }
  Qed.

Lemma elim_quant_interp_pattern :  
forall {typemap t_quantifiermap ctx t0 rett}
(ql : DeepList t_quantifiermap)
(v : Formula (typemap := typemap) (ctx:=ctx) t0) 
(p : Pattern rett),
interp_pattern 
  (DCons t0 (interp_formula ctx v) ql) p =
  interp_pattern ql (app_pattern v p).
  induction p .
  {
    simpl.
    erewrite IHp2.
    erewrite IHp1.
    reflexivity.
  }
  2:{
    simpl.
    reflexivity.
  }
  {
    destruct n.
    {

      simpl (app_pattern _ _).
      simpl in e.
      inversion e.
      dependent destruction e.
      unfold eq_rect_r, eq_rect, eq_sym, f_equal.
      unfold interp_pattern at 1.
      unfold Pattern_rect.
      simpl nth_deep.
      unfold eq_rect_r, eq_rect, eq_sym, f_equal.
      induction v.
      {
        simpl.
        erewrite IHv2; eauto.
        erewrite IHv1; eauto.
      }
      {
        eauto.
      }
    }
    {
      simpl in *.
      reflexivity.
    } 
  }
  Qed.


Lemma eqPropType : forall {P P0 : Prop}, @eq Prop P P0 -> @eq Type P P0.
  intros.
  rewrite H.
  reflexivity.
Defined.
Require Import Coq.Logic.EqdepFacts.

Lemma elim_quant_generate_theorem : 
forall {typemap quant_to_do t_quantifiermap}
(ql : DeepList t_quantifiermap)
{ctx t0 rett}
(v : Formula (typemap := typemap) (ctx:=ctx) t0) 
(p pnew: Pattern rett),
  generate_theorem 
    rett quant_to_do (t0 :: t_quantifiermap) 
    (DCons t0 (interp_formula ctx v) ql) p pnew =
  generate_theorem 
    rett quant_to_do t_quantifiermap
    ql (app_pattern v p) (app_pattern v pnew).
    intros typemap quant_to_do t_quantifiermap. 
    change ((fix app (l m : list (type )) {struct l} :
           list (type ) :=
         match l with
         | nil => m
         | a :: l1 => a :: app l1 m
         end) t_quantifiermap quant_to_do) with ( t_quantifiermap ++ quant_to_do).
         revert t_quantifiermap.
    induction quant_to_do.
    2:{
      intros.
      specialize (IHquant_to_do (t_quantifiermap ++ (cons a nil))).
      specialize IHquant_to_do with (ctx:=ctx) (t0 := t0) (rett:= rett).
      specialize (IHquant_to_do) with (v:= v).
      simpl.
      Require Import Coq.Logic.FunctionalExtensionality.
      pose @forall_extensionality.
      set (eq_rect _ _ _ _ _) as p_transported.
      set (eq_rect _ _ _ _ _) as pnew_transported.
      set (eq_rect _ _ _ _ _) as app_p_transported.
      set (eq_rect _ _ _ _ _) as app_pnew_transported.
      assert ( forall (x : t_denote a),
                (fun x => generate_theorem rett quant_to_do (t0 :: t_quantifiermap ++ (cons a nil)) (DCons t0 (interp_formula ctx v) (add_end ql x)) p_transported
                  pnew_transported ) x=
                (fun x => generate_theorem rett quant_to_do (t_quantifiermap ++ (cons a nil)) (add_end ql x) (app_p_transported) (app_pnew_transported)) x).
      intros.
      erewrite IHquant_to_do.
      f_equal.
      {
        intros.
        rewrite H5.
        rewrite H6.
        reflexivity.
      }
      {
        subst app_p_transported.
        subst p_transported.
        unfold app_assoc'.
        unfold eq_rect, eq_trans, f_equal.
        remember (list_ind _ _ _ _ ).
        clear.
        revert v.
        revert p.
        revert rett.
        revert t0.
        simpl in y.
        generalize y.
        clear y.
        pose app_assoc'.
        specialize (e _ t_quantifiermap (cons a nil) quant_to_do).
        simpl in e.
        rewrite <- e.
        intros.
        dependent destruction y.
        reflexivity.
      }
      {
        subst app_pnew_transported.
        subst pnew_transported.
        unfold app_assoc'.
        unfold eq_rect, eq_trans, f_equal.
        remember (list_ind _ _ _ _ ).
        clear.
        revert v.
        revert pnew.
        revert rett.
        revert t0.
        simpl in y.
        generalize y.
        clear y.
        pose app_assoc'.
        
        specialize (e _ t_quantifiermap (cons a nil) quant_to_do).
        simpl in e.
        rewrite <- e.
        intros.
        dependent destruction y.
        reflexivity.
      }
      specialize (e _ _  _ H).
      apply e.
    }
    {
      intros.
      cbn [generate_theorem].
      erewrite <- elim_quant_interp_pattern.
      erewrite <- elim_quant_interp_pattern.
      eapply eqPropType.
      Require Import Coq.Logic.PropExtensionality.
      pose propositional_extensionality.
      match goal with 
      | [ |- ?a = ?b] => set a; set b end.
      specialize (e P P0).
      (* Upcaster from P = P0 in Prop, to P = P0 in type*)
      eapply e.
      subst P P0.
      clear e.
      split.
      {
        intros.
        (* This was surprisingly tricky the first time *)
        assert (interp_pattern (DCons t0 (interp_formula ctx v) (eq_rect_r DeepList ql (app_nil_r' type t_quantifiermap))) p
                = 
                interp_pattern (eq_rect_r DeepList (DCons t0 (interp_formula ctx v) ql) (app_nil_r' type (t0 :: t_quantifiermap))) p) .
        clear H.
        {
          f_equal.
          remember (interp_formula ctx v).
          unfold app_nil_r'.
          simpl.
          unfold eq_trans, f_equal.
          remember (list_ind _ _ _ _ ).
          generalize y.
          clear Heqy.
          clear y.
          rewrite app_nil_r'.
          intros.
          dependent destruction y.
          reflexivity.
        }
        assert (interp_pattern (DCons t0 (interp_formula ctx v) (eq_rect_r DeepList ql (app_nil_r' type t_quantifiermap))) pnew
                = 
                interp_pattern (eq_rect_r DeepList (DCons t0 (interp_formula ctx v) ql) (app_nil_r' type (t0 :: t_quantifiermap))) pnew).
        {
          f_equal.
          remember (interp_formula ctx v).
          unfold app_nil_r'.
          simpl.
          unfold eq_trans, f_equal.
          remember (list_ind _ _ _ _ ).
          generalize y.
          rewrite app_nil_r'.
          intros.
          dependent destruction y0.
          reflexivity.
        }
        etransitivity .
        exact H0.
        etransitivity .
        exact H.
        eauto.
      }
      {
        intros.
        assert (interp_pattern (DCons t0 (interp_formula ctx v) (eq_rect_r DeepList ql (app_nil_r' type t_quantifiermap))) p
                = 
                interp_pattern (eq_rect_r DeepList (DCons t0 (interp_formula ctx v) ql) (app_nil_r' type (t0 :: t_quantifiermap))) p) .
        clear H.
        {
          f_equal.
          remember (interp_formula ctx v).
          unfold app_nil_r'.
          simpl.
          unfold eq_trans, f_equal.
          remember (list_ind _ _ _ _ ).
          generalize y.
          clear Heqy.
          clear y.
          rewrite app_nil_r'.
          intros.
          dependent destruction y.
          reflexivity.
        }
        assert (interp_pattern (DCons t0 (interp_formula ctx v) (eq_rect_r DeepList ql (app_nil_r' type t_quantifiermap))) pnew
                = 
                interp_pattern (eq_rect_r DeepList (DCons t0 (interp_formula ctx v) ql) (app_nil_r' type (t0 :: t_quantifiermap))) pnew).
        {
          f_equal.
          remember (interp_formula ctx v).
          unfold app_nil_r'.
          simpl.
          unfold eq_trans, f_equal.
          remember (list_ind _ _ _ _ ).
          generalize y.
          rewrite app_nil_r'.
          intros.
          dependent destruction y0.
          reflexivity.
        }
        etransitivity.
        symmetry;
        exact H0.
        etransitivity.
        exact H.
        eauto.
      } 
    }
    Qed.

Definition saturate_1LtoR_aux : forall
  {typemap} ctx quantifiermap t' (p pnew : Pattern (typemap:=typemap) (ctx:=ctx) (quantifiermap:=quantifiermap) t')
  (e : egraph)
  (matchingL : (Prod eclass_id (DeepListEclass quantifiermap)))
  ,
  egraph
  .
  induction quantifiermap.
  {
      intros.
      simpl in *.
      pose @pattern_to_formula.
      pose (deeplist2_from_deeplisteclass (ctx:=ctx) nil (sndP matchingL) e).
      destruct o.
      2:{ exact e. }
      specialize f with (1:= d).
      specialize f with (1:=pnew).
      pose (propose_formula (t:= t') ctx e FUEL (fstP matchingL)).
      destruct o.
      pose (mergeF e f0 f).
      destruct p0.
      destruct p0.
      exact e1.
      exact e.
  }
  {
    simpl.
    intros.
    rename matchingL into x.
    set (fstP x) in *.
    remember (sndP x) in *.
    (* We need a way to say  *)
    simpl in *.
    specialize (IHquantifiermap) with (3 := e).
    inversion d.
    specialize (IHquantifiermap) with (3 := (prod e0 cdr)).
    destruct v.
    2:{ exact e. }
    pose (propose_formula (t:= a) ctx e FUEL e1).
    destruct o.
    2:{ exact e. }
    pose (app_pattern f p).
    pose (app_pattern f pnew).
    eapply IHquantifiermap.
    exact p0.
    exact p1.
  }
  Defined.
(* 
Definition saturate_1LtoR_aux : forall
  {typemap} ctx quantifiermap t' (p pnew : Pattern (ctx:=ctx) (quantifiermap:=quantifiermap) t')
  (e : egraph)
  (matchingL : Prod (Formula (ctx:=ctx) t') (DeepList2 (typemap:=typemap) (ctx:=ctx) quantifiermap))
  ,
  (egraph )
  .
  induction quantifiermap.
  {
      intros.
      simpl in *.
      pose @pattern_to_formula.
      specialize f with (1:=sndP matchingL).
      specialize f with (1:=pnew).
      pose (mergeF e (fstP matchingL) f).
      destruct p0.
      destruct p0.
      exact e1.
  }
  {
    simpl.
    intros.
    rename matchingL into x.
    set (fstP x) in *.
    remember (sndP x) in *.
    (* We need a way to say  *)
    simpl in *.
    specialize (IHquantifiermap) with (3 := e).
    inversion d.
    specialize (IHquantifiermap) with (3 := (prod f cdr)).
    pose (app_pattern v p).
    pose (app_pattern v pnew).
    eapply IHquantifiermap.
    exact p0.
    exact p1.
  }
  Defined. *)

Definition pattern_to_formula_correct {typemap ctx } {t : type }
  (quantifiers: DeepList2 (typemap := typemap)(ctx:=ctx) nil) (f : Pattern (quantifiermap:=nil) (ctx:= ctx) t)
   : 
   interp_pattern DNil f = interp_formula ctx (pattern_to_formula quantifiers f).
  induction f.
  -
    simpl.
    rewrite IHf2.
    rewrite IHf1.
    reflexivity.
  -
    destruct n; inversion e.
  - 
    reflexivity.
  Qed. 

Definition saturate_1LtoR_correct : forall
  {typemap} ctx quantifiermap t' p pnew
  (e : egraph)
  (e_pf: invariant_egraph (ctx:= ctx) e)
  (input : Prod eclass_id (DeepListEclass quantifiermap))
  (pf : match propose_formula ctx e FUEL (fstP input), deeplist2_from_deeplisteclass quantifiermap(sndP input) e with
  | Some f, Some quantifiers => 
    interp_pattern (ctx:= ctx) (typemap := typemap) (deeplist_from_deeplist2 (ctx:=ctx) quantifiermap quantifiers) p
    =
    interp_formula ctx f
  | _, _ => True
  end)
  (th_true : generate_theorem t' quantifiermap nil DNil p pnew),
  invariant_egraph (ctx:=ctx) (saturate_1LtoR_aux ctx quantifiermap t' p pnew e input).
  induction quantifiermap.
  {
      intros.
      simpl in th_true.
      unfold eq_rect_r, eq_rect,eq_sym in th_true.
      unfold saturate_1LtoR_aux, list_rect .
      cbn - [propose_formula].
      destruct (propose_formula _ _ _ _ ) eqn:? in pf.
      rewrite Heqo.
      remember (deeplist2_from_deeplisteclass _ _ _).
      destruct o.
      simpl in Heqo0.
      inversion Heqo0.
      pose (@pattern_to_formula_correct typemap ctx t' DNil2 pnew).
      simpl in Heqo0.
      cbn in pf.
      rewrite th_true in pf.
      pose @merge_preserve.
      specialize (y) with (1:=e_pf).
      rewrite e0 in pf.
      symmetry in pf.
      specialize y with (1:= pf).
      destruct (mergeF _ _ _) eqn:?.
      destruct p0.
      eauto.
      cbn in Heqo0.
      inversion Heqo0.
      rewrite Heqo; eauto.
  }
  {
    intros.
    dependent destruction input.
    dependent destruction y.
    cbv [fstP] in pf.
    destruct v.
    2:{ eauto.  }
    specialize (IHquantifiermap) with (1:= e_pf).

    destruct (propose_formula (t:=a) ctx e FUEL e0) eqn:?.
    2:{ cbn - [propose_formula]. rewrite Heqo. eauto. }

    specialize (th_true (interp_formula ctx f)). 
    cbn -[generate_theorem] in th_true.
    assert (generate_theorem t' quantifiermap (cons a nil) (DCons a (interp_formula ctx f) DNil) p pnew).
    exact th_true.
    clear th_true.
    rename X into th_true.
    erewrite elim_quant_generate_theorem in th_true.
    specialize (IHquantifiermap) with (input:=(prod x y)).
    cbn -[ propose_formula] in IHquantifiermap.
    simpl (sndP _) in pf.
    remember (deeplist2_from_deeplisteclass _ _ _) in pf. 
    cbn -[propose_formula] in Heqo0.
    unfold deeplist2_from_deeplisteclass, list_rect, eq_rect_r, eq_rect, f_equal, eq_sym in Heqo0.
    
    assert (o = match  deeplist2_from_deeplisteclass quantifiermap y e with | Some a0 =>  match propose_formula ctx e FUEL e0 with
            | Some a1 => Some (DCons2 a a1 a0)
            | None => None
            end
        | None => None
        end).
    exact Heqo0.
    clear Heqo0.
    subst o.
    rewrite Heqo in pf.
    destruct (deeplist2_from_deeplisteclass quantifiermap y e) eqn:?.
    2:{ 
      specialize (IHquantifiermap) with (1 := pf).
      specialize (IHquantifiermap) with (1 := th_true).
      unfold saturate_1LtoR_aux, eq_rect_r, eq_rect, eq_sym, list_rect, f_equal, sndP .
      rewrite Heqo.
      eapply IHquantifiermap.
    }
    {
      destruct (propose_formula ctx e FUEL x) eqn:?.
      {
        specialize (IHquantifiermap) with (2 := th_true).
        rewrite Heqo1 in IHquantifiermap.
        cbn in pf.
        erewrite elim_quant_interp_pattern in pf.
        unfold eq_rect_r, eq_rect, eq_sym, list_rect, f_equal, sndP in pf.
        specialize (IHquantifiermap pf).
        unfold saturate_1LtoR_aux, eq_rect_r, eq_rect, eq_sym, list_rect, f_equal, sndP .
        rewrite Heqo.
        eapply IHquantifiermap.
      }
      {
        specialize (IHquantifiermap) with (2 := th_true).
        rewrite Heqo1 in IHquantifiermap.
        specialize (IHquantifiermap I).
        unfold saturate_1LtoR_aux, eq_rect_r, eq_rect, eq_sym, list_rect, f_equal, sndP .
        rewrite Heqo.
        eapply IHquantifiermap.
      }
    }
  }
  Qed.

Definition saturate_LtoR_aux : forall
  {typemap} ctx quantifiermap t' (p pnew : Pattern (typemap:= typemap) (ctx:=ctx) (quantifiermap:=quantifiermap) t')
  (e : egraph )
  ,
  (egraph )
  .
  intros.
  pose (match_pattern_aux (typemap := typemap) FUEL ctx quantifiermap  e  _ p).
  (* refine (fold_left (fun acc m1 => _ ) (firstn 1 l) e). *)
  refine (fold_left (fun acc m1 => _ ) ( l) e).
  (* refine (fold_right (fun m1 acc => _ )  e l). *)
  (* We don't want to saturate if the pattern does not make sense anymore? *)
  eapply saturate_1LtoR_aux.
  exact p.
  exact pnew.
  exact acc.
  exact m1.
Defined.
(* 
Lemma preserve : forall   {typemap} ctx quanttype t' input e p pnew,
match propose_formula ctx e FUEL (fstP input), deeplist2_from_deeplisteclass quanttype (sndP input) e with
| Some f, Some quantifiers => 
  interp_pattern (ctx:= ctx) (typemap := typemap) (deeplist_from_deeplist2 (ctx:=ctx) quanttype quantifiers) p
  =
  interp_formula ctx f
| _, _ => True
end ->
match propose_formula ctx (saturate_LtoR_aux ctx quanttype t' p pnew e) FUEL (fstP input), deeplist2_from_deeplisteclass quanttype (sndP input) (saturate_LtoR_aux ctx quanttype t' p pnew e) with
| Some f, Some quantifiers => 
  interp_pattern (ctx:= ctx) (typemap := typemap) (deeplist_from_deeplist2 (ctx:=ctx) quanttype quantifiers) p
  =
  interp_formula ctx f
| _, _ => True
end. *)



Definition saturate_L2R_correct : forall
  {typemap} ctx quantifiermap t' p pnew
  (e : egraph)
  (e_pf: invariant_egraph (ctx:= ctx) e)
  (th_true : generate_theorem (typemap:= typemap) t' quantifiermap nil DNil p pnew),
   invariant_egraph (ctx:=ctx) (saturate_LtoR_aux ctx quantifiermap t' p pnew e ).
   Admitted.
   (* intros.
   intros.
   unfold saturate_LtoR_aux.
   pose @saturate_1LtoR_correct.
   specialize (i) with (3:=th_true).
   pose proof (@match_pattern_correct typemap FUEL ctx quantifiermap e t' p).
   (* pose proof (@match_pattern_correct typemap FUEL ctx quantifiermap e t' p). *)
   remember (match_pattern_aux _ _ _ _ _ _).
   clear Heql.
   generalize dependent e.

  induction l; eauto.
  {
     intros.
     simpl.
     eapply IHl.
     eapply saturate_1LtoR_correct;
     eauto.
     inversion H.
     eauto.
     inversion H.
   
   }
   Qed. *)
  
Definition lift_pattern :
  forall (tm tmext : list Type)
    (t : type)
    (qm : list (type ))
    (ctx : asgn tm)
    (* Maybe add a proof that every term of the context is within tm *)
    (pf : forallb (fun el => max_t (T el) <? length tm) ctx  = true)
    (newctx : asgn (tm ++ tmext)),
      @Pattern tm qm ctx t ->
      @Pattern
        (tm++tmext)
        qm
        (lift_ctx tm tmext ctx newctx)
        t.
        intros.
        induction X.
        {
          eapply (PApp1 IHX1 IHX2).
        }
        {
          eapply (PVar n (t0:= t0) ).
          eauto.
        }
        {
          set ((T t0)).
          pose (state t0).
          pose (@PAtom1 (tm++tmext) (qm) (lift_ctx tm tmext ctx newctx)).
          pose lift_nth_error.
          specialize e0 with (1:=pf).
          specialize e0 with (1:=e).
          specialize (e0 tmext newctx).
          pose proof (forallb_forall (fun el => max_t (T el) <? length tm) ctx).
          destruct H.
          specialize (H pf). clear H0.
          eapply nth_error_In in e.
          specialize (H _ e).
          specialize (e0 H).
          specialize (p _ _ e0).
          exact p.
        }
  Defined.

Inductive reifed_obj {typemap : list Type} {ctx : asgn typemap} :=
| SingleFact (a : type) (f : Formula (typemap:=typemap) (ctx:=ctx) a)
| EqualFacts (a : type) 
  (l : Formula (typemap:=typemap) (ctx:=ctx) a)
  (r : Formula (typemap:=typemap) (ctx:=ctx) a)
  (th : Type)
  (th_pf : th)
| Build_reifed_theorem  : forall
  (deept : type)
  (quant : list type)
  (lhsP : @Pattern typemap quant ctx deept)
  (rhsP : @Pattern typemap quant ctx deept) 
  (th : Type)
  (th_pf : th)
, reifed_obj .

Definition lift_formula :
  forall (tm tmext : list Type)
    (t : type)
    (ctx : asgn tm)
    (* Maybe add a proof that every term of the context is within tm *)
    (pf : forallb (fun el => max_t (T el) <? length tm) ctx  = true)
    (newctx : asgn (tm ++ tmext)),
      @Formula tm ctx t ->
      @Formula
        (tm++tmext)
        (lift_ctx tm tmext ctx newctx)
        t.
        intros.
        induction X.
        {
          eapply (App1 IHX1 IHX2).
        }
        {
          set ((T t0)).
          pose (state t0).
          pose (@Atom1 (tm++tmext)  (lift_ctx tm tmext ctx newctx)).
          pose lift_nth_error.
          specialize e0 with (1:=pf).
          specialize e0 with (1:=e).
          specialize (e0 tmext newctx).
          pose proof (forallb_forall (fun el => max_t (T el) <? length tm) ctx).
          destruct H.
          specialize (H pf). clear H0.
          eapply nth_error_In in e.
          specialize (H _ e).
          specialize (e0 H).
          specialize (f _ _ e0).
          exact f.
        }
  Defined.


Definition lift_reifed_theorem {typemap : list Type} {ctx : asgn typemap}
    {diff_tm : list Type} {diff_vm : asgn (typemap ++ diff_tm)}
  (r : @reifed_obj typemap ctx) 
  (pf :forallb (fun el : SModule => max_t (T el) <? length typemap) ctx = true )
  : 
 @reifed_obj (typemap ++ diff_tm) (lift_ctx typemap diff_tm ctx diff_vm). 
  destruct r.
  {
    eapply SingleFact.
    eapply lift_formula.  eauto.  eauto.
  }
  {
    eapply EqualFacts.
    eapply lift_formula. eauto. exact l.
    eapply lift_formula. eauto. exact r.
    exact th_pf.
  }
  {
    pose @Build_reifed_theorem.
    specialize (r) with (1:= (lift_pattern typemap diff_tm deept quant ctx pf diff_vm lhsP)).
    specialize (r) with (1:= (lift_pattern typemap diff_tm deept quant ctx pf diff_vm rhsP)).
    specialize (r) with (1:= th_pf).
    exact r.
  }
  Defined.

Definition lift_reifed_theorems {typemap : list Type} {ctx : asgn typemap} 
    {diff_tm : list Type} {diff_vm : asgn (typemap ++ diff_tm)}
  (r : list (@reifed_obj typemap ctx)) 
  (pf :forallb (fun el : SModule => max_t (T el) <? length typemap) ctx = true )
  : 
 list (@reifed_obj (typemap ++ diff_tm) (lift_ctx typemap diff_tm ctx diff_vm)). 
 eapply (map (fun x => @lift_reifed_theorem _ _ _ _ x pf) r).
  Defined.

Definition get_tm {typemap : list Type} {ctx : asgn typemap} (r : @reifed_obj typemap ctx) := typemap.
Definition get_ctx {typemap : list Type} {ctx : asgn typemap} (r : @reifed_obj typemap ctx) := ctx.

Definition empty_theorem (typemap : list Type) (ctx : asgn typemap) : list (@reifed_obj typemap ctx) := nil.
Ltac add_theorem identtm identvm list_th new_th :=
  let temp := fresh "temp" in
  rename list_th into temp;
  let oldtm := match type of temp with 
                | list (@reifed_obj ?tm _) => tm 
                | _ => fail 
                end in
  let oldvm := match type of temp with 
                | list (@reifed_obj _ ?vm ) => vm 
                | _ => fail 
                end in
  let newtm := eval cbv [get_tm] in (get_tm new_th) in
  let newvm := eval cbv [get_ctx] in (get_ctx new_th) in
  let difft := eval cbv [skipn length] in (skipn (length oldtm) newtm) in
  let diffv := eval cbv [skipn length] in (skipn (length oldvm) newvm) in
  (* let term := eval cbv [new_th map empty_theorem identtm identvm lift_reifed_theorems lift_reifed_theorem deept quant lhsP rhsP th th_pf] in (new_th :: (@lift_reifed_theorems oldtm oldvm difft diffv temp eq_refl)) in *)
  (* let term := eval cbv [identtm identvm lift_reifed_theorems map]  in (new_th :: (@lift_reifed_theorems oldtm oldvm difft diffv temp eq_refl)) in *)
  let rest_list := eval hnf in (@lift_reifed_theorems oldtm oldvm difft diffv temp eq_refl) in
  let term := constr:(new_th :: rest_list) in
  pose term as list_th;
  subst temp;
  subst new_th.

Ltac reify_hyp1 H oldtypemap oldvarmap :=
  idtac "start reify hyp";
  let oldtm := fresh "oldtm" in
  let oldvm := fresh "oldvm" in
  let etm := fresh "quantifiers" in
  let nquant := fresh "quantifiers" in
  let patternlhs := fresh "lhsPat" in
  let patternrhs := fresh "rhsPat" in
  let deept := fresh "t_" in
  rename oldtypemap into oldtm;
  rename oldvarmap into oldvm;
  evar (oldtypemap : list Type);
  evar (oldvarmap : list (@SModule oldtypemap));
  evar (deept : type );
  evar (nquant : list (type ));
  evar (patternlhs : Pattern (quantifiermap:=nquant) (ctx:= oldvarmap) deept);
  evar (patternrhs : Pattern (quantifiermap:=nquant) (ctx:=oldvarmap) deept);
  let oldtm1 := eval unfold oldtm in oldtm in
  idtac "yo" oldtm1;
  let newassert := fresh "newassert" in
  let quan := get_quantifiers H in
  let quan := type_term quan in
  idtac quan;
  let t := type of H in assert t as newassert;
  reify_forall 0;
   [
  match goal with
  | [ |- ?a = ?b] =>
  idtac "start listTypes" oldtm1;
  let typemap := listTypesFromProp oldtm1 (prod a b) in
  idtac "newtypemap" typemap;
  let diff := ltac_diff typemap oldtm1 in
  idtac "diff" diff;
  let oldtm' := eval unfold oldtypemap in oldtypemap in
  unify oldtm' typemap;
  pose typemap;
  idtac typemap;
  let deepify_quant := ltac_map funToTArrow typemap quan in
  let deepify_quant := type_term deepify_quant in
  let oldvm := eval unfold oldvm in oldvm in
  let x' := eval unfold nquant in nquant in
  unify  deepify_quant x';
  idtac "deepquant" deepify_quant oldtm1 diff oldvm;
  let oldvarmap' := constr:(upcast_varmap oldtm1 diff oldvm) in
  idtac "partial" oldvarmap';
  let oldvarmap' := eval cbv [sndP app_nth1 Init.Nat.max Nat.ltb Nat.leb length max_t upcast_varmap travel_value generate_theorem interp_pattern eq_rect_r eq_rect eq_sym app_assoc' f_equal eq_trans list_ind nth_error nth_deep Pattern_rect nat_rect app rev list_rect type_rect type_rec] in oldvarmap' in
  idtac "reduced" oldvarmap';
  let varmap := listFromProp' typemap oldvarmap' (prod a b) in
  idtac "newvarmap" varmap;
  let oldvm' := eval unfold oldvarmap in oldvarmap in
  unify oldvm' varmap;
  pose varmap;
  idtac "varmap" varmap deepify_quant typemap ;
  let reifedA := reify_prop' deepify_quant typemap varmap a in
  pose reifedA as A;
  let reifedB := reify_prop' deepify_quant typemap varmap b in
  pose reifedB as B;
  idtac "reifed" reifedA reifedB;
  let A':= eval unfold A in A in
  let B':= eval unfold B in B in
  let x' := eval unfold patternlhs in patternlhs in
  let y' := eval unfold patternrhs in patternrhs in
  let t := type of a in
  idtac "type of a" a t;
  let tm := eval unfold oldtypemap in oldtypemap in
  let deeply_represented := funToTArrow tm t in
  let t' := eval unfold deept in deept in
  unify t' deeply_represented;
  unify x' reifedA ;
  unify y' reifedB ;
  (* unify y' reifedB ; *)
  (* let c := type of A in
  match c with
  | Pattern ?rett =>
  let T := fresh "newlemma" in
  let rett := eval simpl in rett in
    pose (generate_theorem (ctx:= varmap) (typemap := typemap) rett deepify_quant [] DNil
                                A' B') as T;
  let x' := eval unfold x in x in
  unify x' T ;
  end *)
  eapply H
  end
 |]; clear newassert
 ;
 subst oldtm;
 subst oldvm.



Ltac reify_prop1 typemap varmap prop :=
  match prop with
   | ?a ?b =>
    lazymatch type of b with 
        | Prop => let acc1 := reify_prop1 typemap varmap a in
           let acc2 := reify_prop1 typemap varmap b in
          (* let __ := match O with | _ => idtac "Node" a b acc1 acc2 end in *)
           let res :=
           constr:(App1 (typemap := typemap) acc1 acc2) in
          (* let __ := match O with | _ => idtac "Nodeok" res end in *)
          res
        | Type => fail
        | _ => 
           let acc1 := reify_prop1 typemap varmap a in
           let acc2 := reify_prop1 typemap varmap b in
          (* let __ := match O with | _ => idtac "Node" a b acc1 acc2 end in *)
           let res :=
           constr:(App1 (typemap := typemap) acc1 acc2) in
          (* let __ := match O with | _ => idtac "Nodeok" res end in *)
          res
   end
   | ?a =>
    let t := type of a in
    (* let typemap' := eval unfold typemap in typemap in *)
   (* let __ := match O with | _ => idtac "leaf" t a  typemap end in *)
    let deeply_represented := funToTArrow typemap t in
   (* let __ := match O with | _ => idtac "funTArrow" deeply_represented end in *)
    let deeply_represented := eval cbv in deeply_represented in
    let newa :=  eval cbv  [Pos.to_nat app_nth1 Pos.of_nat sndP app_nth1 Init.Nat.max Nat.ltb Nat.leb length max_t upcast_value upcast_varmap travel_value generate_theorem interp_pattern eq_rect_r eq_rect eq_sym app_assoc' f_equal eq_trans list_ind nth_error nth_deep Pattern_rect nat_rect app rev list_rect type_rect type_rec] in (upcast_value typemap deeply_represented nil eq_refl a) in
    (* let __ := match O with | _ => idtac "lookingfor" a varmap end in *)
    (* idtac deeply_represented a varmap; *)
    let idx := indexList {| T := deeply_represented ; state := newa : (t_denote (typemap:= typemap) deeply_represented)|} varmap in
    let idx := eval cbv in (Pos.of_nat (1+idx)) in 
    (* let __ := match O with | _ => idtac "idx" idx end in *)
    let res := constr:(@Atom1 typemap varmap idx _ eq_refl) in
      let tres := type of res in
    (* let __ := match O with | _ => idtac "ok " res tres end in *)
    constr:(@Atom1 typemap varmap idx _ eq_refl)
end.

Ltac init_maps tm vm :=
  pose ((cons Prop nil) : list Type) as tm;
  pose (nil : list (SModule (typemap := tm))) as vm.

Ltac reify_goal_equality oldtypemap oldvarmap :=
  let oldtm := fresh "oldtm" in
  let oldvm := fresh "oldvm" in
  rename oldtypemap into oldtm;
  rename oldvarmap into oldvm;
  evar (oldtypemap : list Type);
  evar (oldvarmap : list (@SModule oldtypemap));
  let oldtm1 := eval unfold oldtm in oldtm in
  idtac "yo" oldtm1;
  match goal with
  | [ |- ?a = ?b] =>
  idtac "start listTypes";
  let typemap := listTypesFromProp oldtm1 (prod a b) in
  idtac "newtypemap" typemap;
  let diff := ltac_diff typemap oldtm1 in
  idtac "diff" diff;
  let oldtm' := eval unfold oldtypemap in oldtypemap in
  unify oldtm' typemap;
  let oldvm1 := eval unfold oldvm in oldvm in
  let oldvarmap' := constr:(upcast_varmap oldtm1 diff oldvm1) in
  idtac "partial" oldvarmap';
  let oldvarmap' := eval cbv [sndP app_nth1 Init.Nat.max Nat.ltb Nat.leb length max_t upcast_varmap travel_value generate_theorem interp_pattern eq_rect_r eq_rect eq_sym app_assoc' f_equal eq_trans list_ind nth_error nth_deep Pattern_rect nat_rect app rev list_rect type_rect type_rec] in oldvarmap' in
  idtac "reduced" oldvarmap';
  let varmap := listFromProp' typemap oldvarmap' (prod a b) in
  idtac "newvarmap" varmap;
  let oldvm' := eval unfold oldvarmap in oldvarmap in
  unify oldvm' varmap;
  subst oldvm;
  subst oldtm;
  match goal with
  | [|- ?a  = ?b] =>
    let oldtm := eval unfold oldtypemap in oldtypemap in
    let oldvm := eval unfold oldvarmap in oldvarmap in
    let reifedLHS := reify_prop1 oldtm oldvm a in
    let reifedRHS := reify_prop1 oldtm oldvm b in
    let lhs := fresh "goalLHS" in
    let rhs := fresh "goalRHS" in
    pose reifedLHS as lhs;
    pose reifedRHS as rhs
  end
  end.

Ltac reify_theorem_eq H oldtypemap oldvarmap list_th :=
  idtac "start reify hyp";
  let oldtm := fresh "oldtm" in
  let oldvm := fresh "oldvm" in
  let etm := fresh "quantifiers" in
  let nquant := fresh "quantifiers" in
  let patternlhs := fresh "lhsPat" in
  let patternrhs := fresh "rhsPat" in
  let edeept := fresh "t_" in
  rename oldtypemap into oldtm;
  rename oldvarmap into oldvm;
  evar (oldtypemap : list Type);
  evar (oldvarmap : list (@SModule oldtypemap));
  evar (edeept : type );
  evar (nquant : list (type ));
  evar (patternlhs : Pattern (quantifiermap:=nquant) (ctx:= oldvarmap) edeept);
  evar (patternrhs : Pattern (quantifiermap:=nquant) (ctx:=oldvarmap) edeept);
  let oldtm1 := eval unfold oldtm in oldtm in
  idtac "yo" oldtm1;
  let newassert := fresh "newassert" in
  let quan := get_quantifiers H in
  let quan := type_term quan in
  idtac quan;
  let t := type of H in assert t as newassert;
  reify_forall 0;
   [
  match goal with
  | [ |- ?a = ?b] =>
  idtac "start listTypes" oldtm1;
  let typemap := listTypesFromProp oldtm1 (prod a b) in
  idtac "newtypemap" typemap;
  let diff := ltac_diff typemap oldtm1 in
  idtac "diff" diff;
  let oldtm' := eval unfold oldtypemap in oldtypemap in
  unify oldtm' typemap;
  pose typemap;
  idtac typemap;
  let deepify_quant := ltac_map funToTArrow typemap quan in
  let deepify_quant := type_term deepify_quant in
  let oldvm := eval unfold oldvm in oldvm in
  let x' := eval unfold nquant in nquant in
  unify  deepify_quant x';
  idtac "deepquant" deepify_quant oldtm1 diff oldvm;
  let oldvarmap' := constr:(upcast_varmap oldtm1 diff oldvm) in
  idtac "partial" oldvarmap';
  let oldvarmap' := eval cbv [ sndP app_nth1 Init.Nat.max Nat.ltb Nat.leb length max_t upcast_varmap travel_value generate_theorem interp_pattern eq_rect_r eq_rect eq_sym app_assoc' f_equal eq_trans list_ind nth_error nth_deep Pattern_rect nat_rect app rev list_rect type_rect type_rec] in oldvarmap' in
  idtac "reduced" oldvarmap';
  let varmap := listFromProp' typemap oldvarmap' (prod a b) in
  idtac "newvarmap" varmap;
  let oldvm' := eval unfold oldvarmap in oldvarmap in
  unify oldvm' varmap;
  pose varmap;
  idtac "varmap" varmap deepify_quant typemap ;
  let reifedA := reify_prop' deepify_quant typemap varmap a in
  pose reifedA as A;
  let reifedB := reify_prop' deepify_quant typemap varmap b in
  pose reifedB as B;
  idtac "reifed" reifedA reifedB;
  let A':= eval unfold A in A in
  let B':= eval unfold B in B in
  let x' := eval unfold patternlhs in patternlhs in
  let y' := eval unfold patternrhs in patternrhs in
  let t := type of a in
  idtac "type of a" a t;
  let tm := eval unfold oldtypemap in oldtypemap in
  let deeply_represented := funToTArrow tm t in
  let t' := eval unfold edeept in edeept in
  unify t' deeply_represented;
  unify x' reifedA ;
  unify y' reifedB ;
  eapply H
  end
 |]; clear newassert
 ;
 subst oldtm;
 subst oldvm;
 let tH0 := type of H in
 let new_th := fresh "newth" in
 pose (Build_reifed_theorem edeept nquant patternlhs patternrhs tH0 H )as new_th;
 add_theorem oldtypemap oldvarmap list_th new_th;
 subst patternlhs; 
 subst patternrhs;
 subst nquant;
 subst edeept
 .

Ltac reify_quant_free oldtypemap oldvarmap H list_th :=
  let oldtm := fresh "oldtm" in
  let oldvm := fresh "oldvm" in
  idtac "start" ;
  rename oldtypemap into oldtm;
  rename oldvarmap into oldvm;
  evar (oldtypemap : list Type);
  evar (oldvarmap : list (@SModule oldtypemap));
  let oldtm1 := eval unfold oldtm in oldtm in
  idtac "yo" oldtm1;
  lazymatch type of H with
    | ?a = ?b => 
idtac "start listTypes" a b;
  let typemap := listTypesFromProp oldtm1 (prod a b) in
  idtac "newtypemap" typemap;
  let diff := ltac_diff typemap oldtm1 in
  idtac "diff" diff;
  let oldtm' := eval unfold oldtypemap in oldtypemap in
  unify oldtm' typemap;
  let oldvm1 := eval unfold oldvm in oldvm in
  let oldvarmap' := constr:(upcast_varmap oldtm1 diff oldvm1) in
  idtac "partial" oldvarmap';
  let oldvarmap' := eval cbv [sndP app_nth1 Init.Nat.max Nat.ltb Nat.leb length max_t upcast_varmap travel_value generate_theorem interp_pattern eq_rect_r eq_rect eq_sym app_assoc' f_equal eq_trans list_ind nth_error nth_deep Pattern_rect nat_rect app rev list_rect type_rect type_rec] in oldvarmap' in
  idtac "reduced" oldvarmap';
  let varmap := listFromProp' typemap oldvarmap' (prod a b)  in
  idtac "newvarmap" varmap ;
  let oldvm' := eval unfold oldvarmap in oldvarmap in
  unify oldvm' varmap;
  (* match goal with
  | [|- ?a  = ?b] => *)
    let reifedLHS := reify_prop1 typemap varmap a in
    let reifedRHS := reify_prop1 typemap varmap b in
    let lhs := fresh "hypL" H in
    let rhs := fresh "hypR" H in
    pose reifedLHS as lhs;
    pose reifedRHS as rhs;
  idtac "doneOld" ; 
    let edeept := match type of lhs with 
  | Formula ?a => a 
  | _ => fail
  end in
  idtac "doneOldDual" a b edeept; 
    let new_th := fresh "new_th" in
 pose (EqualFacts edeept lhs rhs _ H) as new_th;
  idtac "newtheorem" new_th; 
  (* let new_th' := eval unfold new_th in new_th in  *)
 add_theorem oldtypemap oldvarmap list_th new_th;
 (* subst new_th;  *)
 subst lhs; 
 subst rhs;
  subst oldvm;
  subst oldtm
 | ?a =>
  idtac "start listTypes";
  let typemap := listTypesFromProp oldtm1 a in
  idtac "newtypemap" typemap;
  let diff := ltac_diff typemap oldtm1 in
  idtac "diff" diff;
  let oldtm' := eval unfold oldtypemap in oldtypemap in
  unify oldtm' typemap;
  let oldvm1 := eval unfold oldvm in oldvm in
  let oldvarmap' := constr:(upcast_varmap oldtm1 diff oldvm1) in
  idtac "partial" oldvarmap';
  let oldvarmap' := eval cbv [sndP app_nth1 Init.Nat.max Nat.ltb Nat.leb length max_t upcast_varmap travel_value generate_theorem interp_pattern eq_rect_r eq_rect eq_sym app_assoc' f_equal eq_trans list_ind nth_error nth_deep Pattern_rect nat_rect app rev list_rect type_rect type_rec] in oldvarmap' in
  idtac "reduced" oldvarmap';
  let varmap := listFromProp' typemap oldvarmap' a  in
  idtac "newvarmap" varmap ;
  let oldvm' := eval unfold oldvarmap in oldvarmap in
  unify oldvm' varmap;
  let reifedLHS := reify_prop1 typemap varmap a in
  let lhs := fresh "hyp" H in
  pose reifedLHS as lhs;

  idtac "doneOld" ; 
  let edeept := match type of lhs with 
  | Formula ?a => a 
  | _ => fail
  end in
  idtac "doneOldSingle" a; 
  let new_th := fresh "new_th" in
  pose (SingleFact edeept lhs) as new_th;
  idtac "newtheorem" new_th; 
  add_theorem oldtypemap oldvarmap list_th new_th;
  subst lhs;
  subst oldvm;
  subst oldtm
  end.


Ltac prove_eq goalLHS goalRHS i1 :=
  (* let e := fresh "aux_correct" in
  pose (correct _ i1 _ goalLHS goalRHS) as e ;
  match type of e with 
  | forall q, ?l1 = _ -> ?l2 = _ -> _ => 
    set l1 in e; set l2 in e;
    let res := eval vm_compute in l1 in 
    match res with 
    | Some ?res => 
      eapply (e res)
    | _ => fail
    end
  end; clear e;
  vm_compute; exact eq_refl . *)
 let e := fresh "aux_correct" in
  pose (correct _ i1 _ goalLHS goalRHS) as e ;
  match type of e with 
  | forall q, ?l1 = _ -> ?l2 = _ -> _ => 
    (* set l1 in e; set l2 in e; *)
    let res := eval vm_compute in l1 in 
    match res with 
    | Some ?res => 
      apply (e res); vm_compute; reflexivity
    | _ => fail
    end
  end.



(*  *)
(* Time reify_hyp1 sep_comm tm vm. *)

Ltac lift_for_goal tm vm lhs rhs list_th :=
  let temp := fresh "temp" in
  rename list_th into temp;
  let oldtm := match type of temp with 
                | list (@reifed_obj ?tm _) => tm 
                | _ => fail 
                end in
  let oldvm := match type of temp with 
                | list (@reifed_obj _ ?vm ) => vm 
                | _ => fail 
                end in
  let newtm := match type of lhs with 
                | @Formula ?tm _ _ => tm 
                | _ => fail end in
  let newvm := match type of lhs with 
                | @Formula _ ?vm _ => vm 
                | _ => fail end in
  let difft := eval cbv [skipn length] in (skipn (length oldtm) newtm) in
  let diffv := eval cbv [skipn length] in (skipn (length oldvm) newvm) in
  (* let term := eval cbv [new_th map empty_theorem identtm identvm lift_reifed_theorems lift_reifed_theorem deept quant lhsP rhsP th th_pf] in (new_th :: (@lift_reifed_theorems oldtm oldvm difft diffv temp eq_refl)) in *)
  (* let term := eval cbv [identtm identvm lift_reifed_theorems map]  in (new_th :: (@lift_reifed_theorems oldtm oldvm difft diffv temp eq_refl)) in *)
  let rest_list := constr:(@lift_reifed_theorems oldtm oldvm difft diffv temp eq_refl) in
  let term := constr:( (SingleFact _ lhs) :: (SingleFact _ rhs):: rest_list) in
  pose term as list_th;
  subst temp
  .


Ltac saturate_rec current_sponge name_sponge list_th := 
  let list_th := eval hnf in list_th in 
  lazymatch list_th with 
  | ?t :: ?q => 
  let t' := eval hnf in t in 
  idtac t';
  lazymatch t' with 
  | @Build_reifed_theorem _ _ ?deept ?quant ?lhsP ?rhsP _ ?th_pf =>
    saturate_rec (@saturate_L2R_correct _ _ quant deept lhsP rhsP _ current_sponge th_pf) name_sponge q
  | SingleFact ?t ?f =>
    saturate_rec (@apply_add_formula _ _ _ f _ _ current_sponge eq_refl) name_sponge q
  | EqualFacts ?t ?l ?r _ ?th_pf =>
  (* Currently does nothing here *)
    let interm1 := constr:(@apply_add_formula _ _ _ l _ _ current_sponge eq_refl) in
    let interm2 := constr:(@apply_add_formula _ _ _ r _ _ interm1 eq_refl) in
    let interm3 := constr:(@apply_merge _ _ _ _ _ l r interm2 th_pf eq_refl) in
    saturate_rec interm3 name_sponge q
  end
  | _ => pose proof current_sponge as name_sponge
  end.

Ltac saturate current_sponge list_th :=
    let list_th := eval unfold list_th in list_th in
    idtac list_th;
    let sponge := eval unfold current_sponge in current_sponge in
    clear current_sponge;
    saturate_rec sponge current_sponge list_th.

Notation Lipstick_sponge := (invariant_egraph _). 

Goal (forall m n, (forall x y ,  x + pmya y = pmya y + x)  -> (forall x y, x * y = y * x) -> (m + m = m) = True -> m + pmya n = pmya n + m ).
  intros.
  init_maps tm vm.
  pose ( empty_theorem tm vm) as list_th.
  (* cbv [empty_theorem] in list_th. *)
  Time reify_theorem_eq H tm vm list_th.
  Time reify_theorem_eq H0 tm vm list_th.
  (* Scary. adding this hypothesis generate a universe inconsistency *)
  (* Time reify_quant_free tm vm H1 list_th. *)
  Time reify_goal_equality tm vm.
  Time lift_for_goal tm vm goalLHS goalRHS list_th.

  pose (@empty_invariant tm vm) as sponge.
  Time saturate sponge list_th.
  Time prove_eq goalLHS goalRHS sponge.
  Time Qed.


Goal (forall m n o, (forall x n ,  x + n = n + x) -> (forall x y z ,  (x + y) + z = x + (y + z)) ->
  m = 1 ->  
  (* -> o + m + (pmya n + m) = (pmya n + m + o) + m ). *)
  (o + pmya n + 1  = o + ( m + pmya n))).
  intros.
  init_maps tm vm.
  pose ( empty_theorem tm vm) as list_th.
  Time reify_theorem_eq H tm vm list_th.
  Time reify_theorem_eq H0 tm vm list_th.
  rename list_th into basic_saturation.
  pose (basic_saturation ++ basic_saturation) as list_th.
  (* subst basic_saturation. *)
  (* pose (basic_saturation ) as list_th. *)
  Time reify_quant_free tm vm H1 list_th.
  Time reify_goal_equality tm vm.
  Time lift_for_goal tm vm goalLHS goalRHS list_th.
  pose (@empty_invariant tm vm) as sponge.
  Time saturate sponge list_th.
  (* match type of sponge with 
  | invariant_egraph ?sponge =>
  pose (lookupF goalLHS sponge) as lhs;
  pose (lookupF goalRHS sponge) as rhs
  end. *)
  Time prove_eq goalLHS goalRHS sponge.
  Time Qed.

Goal (forall m n o, (forall x n ,  x + n = n + x) -> (forall x y z ,  (x + y) + z = x + (y + z))  
  -> o + m + (pmya n + m) = (pmya n + m + o) + m ).
  intros.
  init_maps tm vm.
  pose ( empty_theorem tm vm) as list_th.
  Time reify_theorem_eq H tm vm list_th.
  Time reify_theorem_eq H0 tm vm list_th.
  (* Time reify_quant_free tm vm H1 list_th. *)
  Time reify_goal_equality tm vm.
  Time lift_for_goal tm vm goalLHS goalRHS list_th.
  pose (@empty_invariant tm vm) as sponge.
  Time saturate sponge list_th.
  Time prove_eq goalLHS goalRHS sponge.
  Time Qed.

End NonSamsam.




Require Coq.Lists.List. Import List.ListNotations.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.PropExtensionality.

Ltac propintu := intros; apply propositional_extensionality; intuition idtac.
Module PropLemmas.
  Lemma eq_True: forall (P: Prop), P -> P = True. Proof. propintu. Qed.
  Lemma and_True_l: forall (P: Prop), (True /\ P) = P. Proof. propintu. Qed.
  Lemma and_True_r: forall (P: Prop), (P /\ True) = P. Proof. propintu. Qed.
  Lemma eq_eq_True: forall (A: Type) (a: A), (a = a) = True. Proof. propintu. Qed.
End PropLemmas.


Section WithLib.
  Context (word: Type)
          (ZToWord: Z -> word)
          (unsigned: word -> Z)
          (wsub: word -> word -> word)
          (wadd: word -> word -> word)
          (wopp: word -> word).

  Context (wadd_0_l: forall a, wadd (ZToWord 0) a = a)
          (wadd_0_r: forall a, wadd a (ZToWord 0) = a)
          (wadd_comm: forall a b, wadd a b = wadd b a)
          (wadd_assoc: forall a b c, wadd a (wadd b c) = wadd (wadd a b) c)
          (wadd_opp: forall a, wadd a (wopp a) = ZToWord 0).

  (* Preprocessing: *)
  Context (wsub_def: forall a b, wsub a b = wadd a (wopp b)).

  (* With sideconditions: *)
  Context (unsigned_of_Z: forall a, 0 <= a < 2 ^ 32 -> unsigned (ZToWord a) = a).

  Context (mem: Type)
          (word_array: word -> list word -> mem -> Prop)
          (sep: (mem -> Prop) -> (mem -> Prop) -> (mem -> Prop)).

  Context (sep_comm: forall P Q: mem -> Prop, sep P Q = sep Q P).

  Ltac pose_list_lemmas :=
    pose proof (@List.firstn_cons word) as firstn_cons;
    pose proof (@List.skipn_cons word) as skipn_cons;
    pose proof (@List.app_comm_cons word) as app_cons;
    pose proof (@List.firstn_O word) as firstn_O;
    pose proof (@List.skipn_O word) as skipn_O;
    pose proof (@List.app_nil_l word) as app_nil_l;
    pose proof (@List.app_nil_r word) as app_nil_r.

  Ltac pose_prop_lemmas :=
    pose proof PropLemmas.and_True_l as and_True_l;
    pose proof PropLemmas.and_True_r as and_True_r;
    pose proof PropLemmas.eq_eq_True as eq_eq_True.

  Import NonSamsam.
  Definition lipstick {A:Type} {a:A} := a.

  Lemma simplification1: forall (a: word) (w1_0 w2_0 w1 w2: word) (vs: list word)
                               (R: mem -> Prop) (m: mem) (cond0_0 cond0: bool)
        (f g: word -> word) (b: word)
        (HL: length vs = 3%nat)
        (H : sep (word_array a
          (List.firstn
             (Z.to_nat (unsigned (wsub (wadd a (ZToWord 8)) a) / 4))
             ((if cond0_0 then [w1_0] else if cond0 then [w2_0] else List.firstn 1 vs) ++
              [w1] ++ List.skipn 2 vs) ++
           [w2] ++
           List.skipn
             (S (Z.to_nat (unsigned (wsub (wadd a (ZToWord 8)) a) / 4)))
             ((if cond0_0 then [w1_0] else if cond0 then [w2_0] else List.firstn 1 vs) ++
              [w1] ++ List.skipn 2 vs))) R m),
      f (wadd b a) = g b /\
      sep R (word_array a [List.nth 0 vs (ZToWord 0); w1; w2]) m = True /\
      f (wadd b a) = f (wadd a b).
  Proof.
    pose_list_lemmas.
    pose_prop_lemmas.

    intros.
    specialize (eq_eq_True word).

    (* Make problems simpler by only considering one combination of the booleans,
       but it would be nice to treat all of them at once *)
    replace cond0_0 with false in * by admit.
    replace cond0 with false in * by admit.

    (* Make problem simpler by not requiring side conditions: since we know the
       concrete length of vs, we can destruct it, so firstn and skipn lemmas can
       be on cons without sideconditions rather than on app with side conditions
       on length *)
    destruct vs as [|v0 vs]. 1: discriminate HL.
    destruct vs as [|v1 vs]. 1: discriminate HL.
    destruct vs as [|v2 vs]. 1: discriminate HL.
    destruct vs as [|v3 vs]. 2: discriminate HL.
    clear HL.
    cbn.
    (* cbn in H. <-- We don't do this cbn because now that we've done the above
       destructs, cbn can do much more than it usually would be able to do. *)

    (* Preprocessing *)
    rewrite wsub_def in *.
    clear wsub_def.
    apply PropLemmas.eq_True in H.

    (* Rewrites with sideconditions, currently also part of separate preprocessing: *)
    pose proof (unsigned_of_Z 8 ltac:(lia)) as A1.

    (* Constant propagation rules, manually chosen to make things work,
       TODO how to automate? *)
    pose proof (eq_refl : (Z.to_nat (8 / 4)) = 2%nat) as C1.

  init_maps tm vm.
  pose (empty_theorem tm vm) as list_th.
  Time reify_theorem_eq and_True_l tm vm list_th.
  Time reify_theorem_eq skipn_cons tm vm list_th. 
  Time reify_theorem_eq and_True_r tm vm list_th.
  Time reify_theorem_eq eq_eq_True tm vm list_th.

  (* Time vm_compute in list_th. *)
  (* Time reify_theorem_eq app_nil_r tm vm list_th.
  Time reify_theorem_eq app_nil_l tm vm list_th.
  Time reify_theorem_eq app_cons tm vm list_th.
 *)
  (* rename list_th into basic_saturation. *)
  (* pose (basic_saturation ) as list_th. *)
  (* clear basic_saturation. *)
  (* pose (basic_saturation ++ basic_saturation) as list_th. *)
  (* Time reify_theorem_eq sep_comm tm vm list_th. *)
  Time reify_theorem_eq wadd_0_l   tm vm list_th.   
  Time reify_theorem_eq wadd_comm tm vm list_th. 
  Time reify_theorem_eq wadd_assoc tm vm list_th.
  Time reify_theorem_eq wadd_opp tm vm list_th.

  (* Time reify_quant_free tm vm H list_th. *)
  Time reify_quant_free tm vm A1 list_th.
  Time reify_quant_free tm vm C1 list_th.
   split.
  2:{
    split.

  Time reify_goal_equality tm vm.
  Time lift_for_goal tm vm goalLHS goalRHS list_th.
  pose (@empty_invariant tm vm) as sponge.
  Time saturate sponge list_th.
  match type of sponge with 
  | invariant_egraph ?sponge =>
  (* time(let v := eval native_compute in sponge in  *)
  pose (@lipstick _ sponge)  as sp
    (* let p := constr:(lookupF goalLHS sponge) in  *)
    (* pose p as lhs; *)
    (* let q := constr:(lookupF goalRHS sponge) in  *)
    (* pose q as rhs *)
  end.
  (* native_compute in sp. *)
  Time Eval native_compute in (max_allocated sp).
  Time Eval vm_compute in (max_allocated sp).

  (* Time vm_compute in lhs.
  Time vm_compute in rhs.
  Time prove_eq goalLHS goalRHS sponge.

  pose (@empty_invariant tm vm) as empty_e.
 

  Time reify_quant_free tm vm A1.
  pose ( empty_theorem tm vm) as list_th.
  cbv [empty_theorem] in list_th.
  
 
  Time saturate sponge1 list_th.
  pose (@apply_add_formula tm vm _ hypLA1 _ _ sponge1 eq_refl) as sponge2.
  Time reify_quant_free tm vm C1.

  reify_goal_equality tm vm.
  pose ( empty_theorem tm vm) as list_th.
  cbv [empty_theorem] in list_th.
  reify_theorem_eq H tm vm list_th.
  reify_theorem_eq H0 tm vm list_th.

  
  Time saturate i0 list_th.
  Time prove_eq goalLHS goalRHS i0.
    pose (@apply_add_formula tm vm _ goalLHS _ _ empty_e eq_refl).
    pose (@apply_add_formula tm vm _ goalRHS _ _ i eq_refl). *)

    (* If sep_comm first, it crashes *)
    


    (* Request for the sponge: Absorb all hypotheses, add the goal as a term,
       and then give me the smallest term that's equal to the goal.
       Below are manual steps consisting of only using equalities of the context
       (potentially forall-quantified, but without side conditions) and which
       result in the desired term in the goal *)
    rewrite (wadd_comm a (ZToWord 8)) in H.
    rewrite <- (wadd_assoc (ZToWord 8) a (wopp a)) in H.
    rewrite (wadd_opp a) in H.
    rewrite (wadd_0_r (ZToWord 8)) in H.
    rewrite A1 in H.
    rewrite C1 in H.
    repeat (rewrite ?firstn_cons, ?skipn_cons, <-?app_cons, ?firstn_O, ?skipn_O,
             ?app_nil_l, ?app_nil_r in H).
    rewrite sep_comm in H.
    rewrite H.
    rewrite and_True_l.
    rewrite (wadd_comm b a).
    rewrite eq_eq_True.
    rewrite and_True_r.

    (* This is the remaining conditions that can't be proven from the hypotheses,
       but having this reduced Prop is much simpler for the user than just to get
       the feedback "can't solve huge Prop automatically" *)
  Abort.

End WithLib.

Goal (forall m n o, (forall x n ,  x + n = n + x) -> (forall x y z ,  (x + y) + z = x + (y + z))  
  -> o + m + m + (pmya n + m) = (pmya n + m + o) + m + m ).
  (* -> (o + m) + pmya n  = o + ( m + pmya n)). *)
  Time intros.
  Time init_maps tm vm.
  Time reify_hyp1 H tm vm.
  Time pose vm as oldvm.
  Time pose tm as oldtm.
  Time reify_hyp1 H0 tm vm.
  Time simpl in vm.
  Time pose vm as oldvm1.
  Time pose tm as oldtm1.
  Time reify_goal_equality tm vm.
  Time pose (skipn (length oldvm) vm) as diffv.
  Time pose (skipn (length oldtm) tm) as difft.
  Time pose (lift_pattern oldtm difft t_ quantifiers0 oldvm eq_refl diffv lhsPat).
  Time pose (lift_pattern oldtm difft t_ quantifiers0 oldvm eq_refl diffv rhsPat).
  Time pose (lift_pattern oldtm1 (skipn (length oldtm1) tm) t_0 quantifiers1 oldvm1 eq_refl (skipn (length oldvm1) vm) lhsPat0).
  Time pose (lift_pattern oldtm1 (skipn (length oldtm1) tm) t_0 quantifiers1 oldvm1 eq_refl (skipn (length oldvm1) vm) rhsPat0).
  Time pose (@empty_invariant tm vm) as empty_e.
  Time pose (@apply_add_formula tm vm _ goalLHS _ _ empty_e eq_refl).
  Time pose (@apply_add_formula tm vm _ goalRHS _ _ i eq_refl).
  Time pose (@saturate_L2R_correct _ vm quantifiers1 _ p1 p2 _ i0 H0).
  Time pose (@saturate_L2R_correct _ vm quantifiers0 _ p p0 _ i1 H).
  Time pose (@saturate_L2R_correct _ vm quantifiers1 _ p1 p2 _ i2 H0).
  Time pose (@saturate_L2R_correct _ vm quantifiers0 _ p p0 _ i3 H).
  Time prove_eq goalLHS goalRHS i4.
Time Qed. 

(* CHENIL BROUGHT DOWN *)
  Inductive SModule {typemap : list Type} :=
    { T : type ; state : t_denote (typemap := typemap) T }.

  Definition generic_embed {typemap : list Type} (T': type ) (s:t_denote (typemap := typemap)T') :=
    {| T:= T'; state := s |}.

Notation "'<<' s '>>'" := (generic_embed s) (only parsing).

Ltac inList e l :=
  lazymatch l with
  | nil =>
  false
  | cons ?t ?l =>
    let res := match O with
    | _ =>
    CASE ltac:(
      first [constr_eq e t ]
      ) true
    | _ =>
    inList e l
    end in res
  end.

Ltac indexList e l :=
  match l with
  | nil => constr:(false)
  | cons e _ => constr:(O%nat)
  | cons _ ?l =>
    let n := indexList e l in
    constr:((S n)%nat)
  end.

Ltac addList e l :=
  let member := inList e l in
 (* let __ := match O with | _ => idtac "addlist" e l member end in *)
  match member with
  | true => l
  | false =>
  let newl := eval cbv [app] in (app l (cons e nil)) in
 (* let __ := match O with | _ => idtac "appendlist" end in *)
   newl
  end.
Definition index := nat.
Ltac CASE l ret :=
let __ := match O with
| _ => assert_succeeds l
end in ret.


Ltac funToTArrow tmap t :=
  match t with
  | ?a -> ?b =>
    let s1 := funToTArrow tmap a in
    let s2 := funToTArrow tmap b in
    constr:(s1 ~> s2)
  | _ =>
    let dt := indexList t tmap in
     constr:(TBase dt)
  end.

(* Le probleme c'set qu'il faut rajouter les TBase types aussi *)
Ltac listTypesFromProp acc input_prop :=
 (* let __ := match O with | _ => idtac "listnewitem" acc input_prop end in *)
  match input_prop with
  | ?a ?b  =>
    lazymatch type of b with 
    | Prop => 
    let acc' := listTypesFromProp acc a in
 (* let __ := match O with | _ => idtac "listnew1" acc' end in *)
    let acc'' := listTypesFromProp acc' b in
    let t := type of input_prop in
    match t with 
    | _ -> _ => 
      acc''
    | _ =>
     addList (t:Type) acc''
     end
        | Type => fail
        | _ => 
    let acc' := listTypesFromProp acc a in
 (* let __ := match O with | _ => idtac "listnew1" acc' end in *)
    let acc'' := listTypesFromProp acc' b in
 (* let __ := match O with | _ => idtac "listnew2" acc'' end in *)
    let t := type of input_prop in
    match t with 
    | _ -> _ => 
      acc''
    | _ =>
     addList (t:Type) acc''
     end
    end
  | ?a =>
    let t := type of a in
    match t with 
    | _ -> _ => 
      acc 
    | _ =>
    addList (t : Type) acc
    end
  end.


Ltac listFromProp tmap acc input_prop :=
  match input_prop with
  | ?a ?b  =>
     lazymatch type of b with 
     |Prop => 
  let acc := listFromProp tmap acc a in
    let acc := listFromProp tmap acc b in
    acc
        | Type => fail
        | _ => 
    let acc := listFromProp tmap acc a in
    let acc := listFromProp tmap acc b in
    acc
        end
  | ?a =>
    let t := type of a in
    let deeply_represented := funToTArrow tmap t in
    addList {| T := deeply_represented ; state := a : (t_denote (typemap:= tmap) deeply_represented)|} acc
  end.


Goal forall A C (D:Prop),
  A /\ A \/ C -> False.
  intros.
  let t := type of H in
  let tmap := listTypesFromProp (nil : list Type) t in
  let map := listFromProp tmap (nil : list (SModule (typemap := tmap))) t in
  idtac tmap;
  idtac map.
  Abort.

Section Term.
  Context {typemap : list Type}.
  Inductive Formula {ctx: asgn typemap} : type -> Type :=
      | App1: forall {t td},
        Formula (t ~> td) ->
        Formula t ->
        Formula td
      | Atom1 : forall (n : positive) t0,
        EGraphList.nth_error ctx ((Pos.to_nat n) - 1) = Some t0 ->
        Formula (T t0).


Require Import Eqdep.