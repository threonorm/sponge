Require Import egg.Loader.
Require Import Coq.ZArith.ZArith.

Set Egg Backend "TPTPBackend". 
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
  Set Egg Misc Logging.
    intros.
    egg_tptp.
  Qed.

