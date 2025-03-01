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

(* Slightly more sophisticated, with S(S(S(...))) *)
Goal forall 
    (div_one: (forall x, d x 1  =  x))
    (cancel_denominator : (forall x y, m (d x y) y =x ))
    (invert_div : forall x y, d x y  = d 1 (d y x)),
    d (m (d 2 3) (d 3 2)) 1 = 1.
  Proof.
    intros.
    Time egg_tptp.
  Qed.

(* Larger *) 
Goal forall 
    (div_one: forall x, d x 1 = x)
    (cancel_denominator: forall x y, m (d x y) y = x)
    (invert_div: forall x y, d x y = d 1 (d y x)),
    d (m (d 40 60) (d 60 40)) 1 = 1.
Proof.
  intros.
  Time egg_tptp.
Qed.

(* Abstract variables *)
Goal forall (A B : nat)
  (div_one: forall x, d x 1 = x)
  (cancel_denominator: forall x y, m (d x y) y = x)
  (invert_div: forall x y, d x y = d 1 (d y x)),
  d (m (d (m A B) B) (d B (m A B))) 1 = 1.
Proof.
  intros.
  egg_tptp.
Qed.

(* More axioms *)
Goal forall (A B : nat)
    (d_as_mult : forall x y, d x y = m x (d 1 y))
    (m_assoc : forall x y z, m x (m y z) = m (m x y) z)
    (m_comm : forall x y, m x y = m y x)
    (m_one : forall x, m x 1 = x)
    (d_self : forall x, d x x = 1)
    (inv_square : forall x, m (d 1 x) (d 1 x) = d 1 (m x x))
    (div_one: (forall x, d x un  =  x))
    (cancel_denominator : (forall x y, m (d x y) y =x ))
    (invert_div : forall x y, d x y  = d un (d y x)),
  d (m (m A A) (d 1 (m B B))) 1 = m (d A B) (d A B).
Proof.
  intros.
  egg_tptp.
Qed.

(* Variation with square *)
Goal forall (A B : nat)
    (d_as_mult : forall x y, d x y = m x (d un y))
    (m_assoc     : forall x y z, m x (m y z) = m (m x y) z)
    (m_comm      : forall x y, m x y = m y x)
    (m_one       : forall x, m x un = x)
    (d_self      : forall x, d x x = un)
    (inv_square  : forall x, m (d un x) (d un x) = d un (m x x))
    (div_one     : forall x, d x un = x)
    (cancel_denominator : forall x y, m (d x y) y = x)
    (invert_div  : forall x y, d x y = d un (d y x))
    (d_comm      : forall x y, d x y = d y x),
  d (m (d A B) (d B A)) un = un.
Proof.
  intros.
  egg_tptp.
Qed.


Goal forall (A B : nat)
    (d_as_mult : forall x y, d x y = m x (d un y))
    (m_assoc     : forall x y z, m x (m y z) = m (m x y) z)
    (m_comm      : forall x y, m x y = m y x)
    (m_one       : forall x, m x un = x)
    (d_self      : forall x, d x x = un)
    (inv_square  : forall x, m (d un x) (d un x) = d un (m x x))
    (div_one     : forall x, d x un = x)
    (cancel_denominator : forall x y, m (d x y) y = x)
    (invert_div  : forall x y, d x y = d un (d y x))
    ,
  m (d A B) (d A B) = d (m A A) (m B B).
Proof.
  intros.
  egg_tptp.
Qed.

(* Very confusing error message: *)
Goal forall (A B : nat)
    (false_axiom: forall x y, d x y = d y x)
    (d_as_mult : forall x y, d x y = m x (d un y))
    (m_assoc     : forall x y z, m x (m y z) = m (m x y) z)
    (m_comm      : forall x y, m x y = m y x)
    (m_one       : forall x, m x un = x)
    (d_self      : forall x, d x x = un)
    (inv_square  : forall x, m (d un x) (d un x) = d un (m x x))
    (div_one     : forall x, d x un = x)
    (cancel_denominator : forall x y, m (d x y) y = x)
    (invert_div  : forall x y, d x y = d un (d y x))
    ,
  m (d A B) (d A B) = d (m A A) (m B B).
Proof.
  intros.
  Fail egg_tptp. (* Why is "The reference Y was not found in the current environment"  *)
Abort.



(* More of the same: *)