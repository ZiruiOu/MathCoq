Require Import Reals.Reals.

Fixpoint rmz_positive(n: positive) : nat :=
    match n with 
    | xH => 0
    | xO n' => S (rmz_positive n')
    | xI n' => rmz_positive n'
    end.

Example check_rmz_6: rmz_positive 6 = 1.
Proof. reflexivity. Qed.

Example chcek_rmz_24: rmz_positive 24 = 3.
Proof. reflexivity. Qed.

Definition irrational(x: R): Prop :=
    ~exists p q: Z, (q > 0)%Z /\  (IZR p / IZR q)%R = x.

