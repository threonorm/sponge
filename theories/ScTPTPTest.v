Require Import egg.Loader.
Require Import Coq.ZArith.ZArith.

Set Egg Backend "TPTPBackend". 
(* Uncomment the following line to keep the file to communicate with egg-sc-tptp *)
(* Set Egg Misc Logging. *)
Axiom d : nat -> nat -> nat.
Axiom m : nat -> nat -> nat.
Axiom un : nat.
Axiom deux : nat.
Axiom trois : nat.
Goal forall 
    (div_one: (forall x, d x un  =  x))
    (cancel_denominator : (forall x y, m (d x y) y =x ))
    (invert_div : forall x y, d x y  = d un (d y x)),
    d (m (d deux trois) (d trois deux)) un = un.
  Proof.
    intros.
    egg_tptp.
  Qed.


Goal forall 
    (div_one: (forall x, d x 1  =  x))
    (cancel_denominator : (forall x y, m (d x y) y =x ))
    (invert_div : forall x y, d x y  = d 1 (d y x)),
    d (m (d 2 3) (d 3 2)) 1 = 1.
  Proof.
    intros.
    egg_tptp.
  Qed.

Goal forall 
    (div_one: forall x, d x 1 = x)
    (cancel_denominator: forall x y, m (d x y) y = x)
    (invert_div: forall x y, d x y = d 1 (d y x)),
    d (m (d 4 6) (d 6 4)) 1 = 1.
Proof.
  intros.
  egg_tptp.
Qed.

Goal forall (A B : nat)
  (div_one: forall x, d x 1 = x)
  (cancel_denominator: forall x y, m (d x y) y = x)
  (invert_div: forall x y, d x y = d 1 (d y x)),
  d (m (d (m A B) B) (d B (m A B))) 1 = 1.
Proof.
  intros.
  egg_tptp.
Qed.


Axiom d_as_mult : forall x y, d x y = m x (d 1 y).
Axiom m_assoc : forall x y z, m x (m y z) = m (m x y) z.
Axiom m_comm : forall x y, m x y = m y x.
Axiom m_one : forall x, m x 1 = x.
Axiom d_self : forall x, d x x = 1.
Axiom inv_square : forall x, m (d 1 x) (d 1 x) = d 1 (m x x).


Goal forall (A B : nat)
    (div_one: (forall x, d x un  =  x))
    (cancel_denominator : (forall x y, m (d x y) y =x ))
    (invert_div : forall x y, d x y  = d un (d y x)),
  d (m (m A A) (d 1 (m B B))) 1 = m (d A B) (d A B).
Proof.
  intros.
  (* Lemma's name still need to be lower case for now *)
  pose proof d_as_mult as h1.
  pose proof m_assoc as h2.
  pose proof m_comm as h3.
  pose proof m_one as h4.
  pose proof inv_square as h5.
  pose proof d_self as h6.
  egg_tptp.
Qed.