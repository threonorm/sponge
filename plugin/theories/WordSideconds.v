Require Import egg.Loader.
Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.PropExtensionality.
Set Default Goal Selector "!".

Lemma rew_zoom_fw{T: Type} {lhs rhs : T}:
  lhs = rhs ->
  forall P : T -> Prop, P lhs -> P rhs.
Proof.
  intros. subst. assumption.
Qed.

Lemma rew_zoom_bw{T: Type}{rhs lhs: T}:
  lhs = rhs ->
  forall P : T -> Type, P rhs -> P lhs.
Proof.
  intros. subst. assumption.
Qed.

Lemma invert_eq_True: forall (P: Prop), P = True -> P.
Proof. intros; subst; auto. Qed.
Lemma prove_eq_True: forall (P: Prop), P -> P = True.
Proof.
  intros. apply propositional_extensionality. split; auto.
Qed.
Lemma invert_eq_False: forall (P: Prop), P = False -> ~ P.
Proof. intros. intro C. subst. assumption. Qed.
Lemma prove_eq_False: forall (P: Prop), ~ P -> P = False.
Proof.
  intros. apply propositional_extensionality. split; intuition idtac.
Qed.

Lemma eq_eq_sym: forall {A: Type} (x y: A), (x = y) = (y = x).
Proof.
  intros. apply propositional_extensionality. split; intros; congruence.
Qed.

Ltac deTrue :=
  repeat match goal with
         | H: _ = True |- _ => eapply invert_eq_True in H
         | H: _ = False |- _ => eapply invert_eq_False in H
         end;
  try apply prove_eq_True;
  try apply prove_eq_False.

Lemma eq_True_holds: forall (P: Prop), P = True <-> P.
Proof.
  split; intros; subst; auto.
  apply propositional_extensionality. split; auto.
Qed.

Module ZT.
  Lemma mul_le : forall e1 e2 : Z,
      (0 <= e1) = True -> (0 <= e2) = True -> (0 <= e1 * e2) = True.
  Proof.
    intros. deTrue. nia.
  Qed.

  Lemma div_mul_lt: forall x d1 d2,
      (0 < x = True)->
      (0 < d1 = True) ->
      (d1 < d2 = True)->
      (x / d2 * d1 < x = True).
  Proof.
    intros. deTrue. Z.to_euclidean_division_equations. nia.
  Qed.

  Lemma lt_from_le_and_neq: forall x y,
      x <= y = True -> (x = y) = False -> x < y = True.
  Proof. intros. deTrue. lia. Qed.

  Lemma le_lt_trans : forall m n p : Z, n <= m = True -> m < p = True -> n < p = True.
  Proof.
    intros. deTrue. lia.
  Qed.

  Lemma mod_le : forall a b : Z, 0 <= a = True -> 0 < b = True -> a mod b <= a = True.
  Proof.
    intros. deTrue. eapply Z.mod_le; assumption.
  Qed.

  Lemma forget_mod_in_lt_l : forall a b m : Z,
      0 <= a = True ->
      0 < m = True ->
      a < b = True ->
      a mod m < b = True.
  Proof.
    intros. deTrue. eapply Z.le_lt_trans. 1: eapply Z.mod_le. all: assumption.
  Qed.

  Lemma div_pos : forall a b : Z, 0 <= a = True -> 0 < b = True -> 0 <= a / b = True.
  Proof.
    intros. deTrue. eapply Z.div_pos; auto.
  Qed.

End ZT.

Lemma neq_sym{A: Type}: forall (x y: A), x <> y -> y <> x. congruence. Qed.

Ltac consts :=
  cbv; apply propositional_extensionality; split; intuition discriminate.

Section WithLib.
  Context (word: Type)
          (ZToWord: Z -> word)
          (unsigned: word -> Z)
          (wsub: word -> word -> word)
          (wadd: word -> word -> word)
          (wslu: word -> word -> word)
          (wsru: word -> word -> word)
          (wopp: word -> word).

  Context (wadd_0_l: forall a, wadd (ZToWord 0) a = a)
          (wadd_0_r: forall a, wadd a (ZToWord 0) = a)
          (wadd_comm: forall a b, wadd a b = wadd b a)
          (wadd_assoc: forall a b c, wadd a (wadd b c) = wadd (wadd a b) c)
          (wadd_opp: forall a, wadd a (wopp a) = ZToWord 0).

  Context (wsub_def: forall a b, wsub a b = wadd a (wopp b)).

  Context (unsigned_of_Z: forall a, 0 <= a < 2 ^ 32 = True -> unsigned (ZToWord a) = a).

  Context (unsigned_nonneg: forall x : word, 0 <= unsigned x = True)
          (unsigned_sru_to_div_pow2: forall (x : word) (a : Z),
              0 <= a < 32 = True ->
              (unsigned (wsru x (ZToWord a))) = (unsigned x) / 2 ^ a)
          (unsigned_slu_to_mul_pow2: forall (x : word) (a : Z),
              0 <= a < 32 = True ->
              (unsigned (wslu x (ZToWord a))) = ((unsigned x) * 2 ^ a) mod 2 ^ 32)
          (word_sub_add_l_same_l: forall x y : word, (wsub (wadd x y) x) = y).

  Ltac pose_const_sideconds :=
    assert (0 <= 8 < 2 ^ 32 = True) as C1 by consts;
    assert (0 <= 3 < 32 = True) as C2 by consts;
    assert (0 <= 4 < 32 = True) as C3 by consts;
    assert (0 <= 2 ^ 3 = True) as C4 by consts;
    assert (0 < 2 ^ 4 = True) as C5 by consts;
    assert (0 < 2 ^ 32 = True) as C6 by consts;
    assert (0 < 2 ^ 3 = True) as C7 by consts;
    assert (2 ^ 3 < 2 ^ 4 = True) as C8 by consts.

  Ltac pose_lib_lemmas :=
    pose proof ZT.forget_mod_in_lt_l as ZT_forget_mod_in_lt_l;
    pose proof ZT.mul_le as ZT_mul_le;
    pose proof ZT.div_pos as ZT_div_pos;
    pose proof ZT.div_mul_lt as ZT_div_mul_lt;
    pose proof ZT.lt_from_le_and_neq as ZT_lt_from_le_and_neq;
    pose proof @eq_eq_sym as H_eq_eq_sym.

  Definition bsearch_goal1 := forall (x : list word) (x1 x2 : word),
      unsigned (wsub x2 x1) = 8 * Z.of_nat (length x) ->
      (unsigned (wsub x2 x1) = 0) = False ->
      unsigned (wsub (wadd x1 (wslu (wsru (wsub x2 x1) (ZToWord 4)) (ZToWord 3))) x1) <
        unsigned (ZToWord 8) * Z.of_nat (length x)
      = True.

  Lemma bsearch_goal1_proof_without_transitivity: bsearch_goal1.
  Proof.
    unfold bsearch_goal1. intros. pose_const_sideconds. pose_lib_lemmas.

    pose (l := 1). move l after H0.
    assert (False -> True) as Impl1 by intuition.

    rewrite word_sub_add_l_same_l.
    rewrite unsigned_of_Z by exact C1.
    rewrite <- H.

    egg_simpl_goal.

    rewrite unsigned_slu_to_mul_pow2 by exact C2.
    rewrite unsigned_sru_to_div_pow2 by exact C3.

    pose proof (unsigned_nonneg (wsub x2 x1)) as p1.
    pose proof (ZT_div_pos (unsigned (wsub x2 x1)) (2 ^ 4) p1 C5) as p2.
    pose proof (ZT_mul_le (unsigned (wsub x2 x1) / 2 ^ 4) (2 ^ 3) p2 C4) as p3.
    pose proof (eq_eq_sym (unsigned (wsub x2 x1)) 0) as q1.
    rewrite q1 in H0.
    pose proof (ZT_lt_from_le_and_neq 0 (unsigned (wsub x2 x1)) p1 H0) as q2.
    pose proof (ZT_div_mul_lt (unsigned (wsub x2 x1)) (2 ^ 3) (2 ^ 4) q2 C7 C8) as q3.
    rewrite (ZT.forget_mod_in_lt_l _ _ _ p3 C6 q3).
    reflexivity.
  Qed.

  Lemma bsearch_goal1_proof_egg: bsearch_goal1.
  Proof.
    unfold bsearch_goal1. intros. pose_const_sideconds. pose_lib_lemmas.

(* proof generated by egg, but manually added correct number of underscores to lemma names
   and @ where needed *)
eapply (@rew_zoom_bw _ (wslu (wsru (wsub x2 x1) (ZToWord 4)) (ZToWord 3)) _  (word_sub_add_l_same_l _ _) (fun hole => (@eq Prop (Z.lt (unsigned hole) (Z.mul (unsigned (ZToWord 8)) (Z.of_nat (@length word x)))) True))).
eapply (@rew_zoom_bw _ (Z.modulo (Z.mul (unsigned (wsru (wsub x2 x1) (ZToWord 4))) (Z.pow 2 3)) (Z.pow 2 32)) _  (unsigned_slu_to_mul_pow2 _ _ _) (fun hole => (@eq Prop (Z.lt hole (Z.mul (unsigned (ZToWord 8)) (Z.of_nat (@length word x)))) True))).
eapply (@rew_zoom_bw _ 8 _  (unsigned_of_Z _ _) (fun hole => (@eq Prop (Z.lt (Z.modulo (Z.mul (unsigned (wsru (wsub x2 x1) (ZToWord 4))) (Z.pow 2 3)) (Z.pow 2 32)) (Z.mul hole (Z.of_nat (@length word x)))) True))).
eapply (@rew_zoom_fw _ (unsigned (wsub x2 x1)) _  H (fun hole => (@eq Prop (Z.lt (Z.modulo (Z.mul (unsigned (wsru (wsub x2 x1) (ZToWord 4))) (Z.pow 2 3)) (Z.pow 2 32)) hole) True)));
eapply (@rew_zoom_bw _ True _  (ZT_forget_mod_in_lt_l _ _ _ _ _ _) (fun hole => (@eq Prop hole True)));
idtac.

reflexivity.
Unshelve.
(* sideconditions: *)
    all: eauto.
    rewrite unsigned_sru_to_div_pow2 by exact C3.
    pose proof (unsigned_nonneg (wsub x2 x1)) as p1.
    pose proof (ZT_div_pos (unsigned (wsub x2 x1)) (2 ^ 4) p1 C5) as p2.
    pose proof (ZT_mul_le (unsigned (wsub x2 x1) / 2 ^ 4) (2 ^ 3) p2 C4) as p3.
    pose proof (eq_eq_sym (unsigned (wsub x2 x1)) 0) as q1.
    rewrite q1 in H0.
    pose proof (ZT_lt_from_le_and_neq 0 (unsigned (wsub x2 x1)) p1 H0) as q2.
    pose proof (ZT_div_mul_lt (unsigned (wsub x2 x1)) (2 ^ 3) (2 ^ 4) q2 C7 C8) as q3.
    eauto.
  Qed.

  Lemma bsearch_goal1_proof1: bsearch_goal1.
  Proof.
    unfold bsearch_goal1. intros. pose_const_sideconds.

    rewrite unsigned_of_Z by exact C1.
    rewrite <- H.
    rewrite word_sub_add_l_same_l.
    rewrite unsigned_slu_to_mul_pow2 by exact C2.
    rewrite unsigned_sru_to_div_pow2 by exact C3.
    rewrite (ZT.le_lt_trans (unsigned (wsub x2 x1) / 2 ^ 4 * 2 ^ 3)).
    { reflexivity. }
    { rewrite ZT.mod_le.
      { reflexivity. }
      { rewrite ZT.mul_le.
        { reflexivity. }
        { rewrite ZT.div_pos.
          { reflexivity. }
          { rewrite unsigned_nonneg. reflexivity. }
          { exact C5. } }
        { exact C4. } }
      { exact C7. } }
    rewrite ZT.div_mul_lt.
    { reflexivity. }
    { rewrite ZT.lt_from_le_and_neq.
      { reflexivity. }
      { apply unsigned_nonneg. }
      { rewrite (eq_eq_sym 0 (unsigned (wsub x2 x1))). exact H0. } }
    { exact C7. }
    { exact C8. }
  Qed.


End WithLib.