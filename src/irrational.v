Require Import Reals.Reals.
Require Import Lia.

Fixpoint rmz_positive(n: positive) : nat :=
    match n with 
    | xH => 0
    | xO n' => S (rmz_positive n')
    | xI n' => 0
    end.

Definition rmz_z(n: Z) : nat := 
    match n with
    | Z0 => 0
    | Zpos n' => rmz_positive n'
    | Zneg n' => rmz_positive n'
    end.


Example check_rmz_6: rmz_positive 6 = 1.
Proof. reflexivity. Qed.

Example check_rmz_24: rmz_positive 24 = 3.
Proof. reflexivity. Qed.

Example check_rmz_neg24: rmz_z (-24)%Z = 3.
Proof. reflexivity. Qed.

Example check_rmz_pos24: rmz_z 24%Z = 3.
Proof. reflexivity. Qed.

Example check_rmz_pos5: rmz_z 5%Z = 0.
Proof. reflexivity. Qed.

Definition irrational(x: R): Prop :=
    ~exists p q: Z, (q > 0)%Z /\  (IZR p / IZR q)%R = x.

Lemma rmz_z_mult_2: forall n: Z, (n <> 0 %Z)->
    rmz_z (2 * n) = S (rmz_z n).
Proof.
    destruct n;
    intuition || intros;
    reflexivity.
    Qed.


Lemma n_Sn_even: forall n,
    Nat.even (S n) = negb (Nat.even n).
Proof.
    intros n.
    induction n.
    - simpl. reflexivity.
    - simpl (Nat.even (S (S n))). 
      rewrite IHn. rewrite Bool.negb_involutive. reflexivity.
    Qed.

Lemma rmz_z_square: forall z: Z,
    Nat.even(rmz_z(z * z)) = true.
Proof.
    assert (rmz_positive_square: forall p: positive, Nat.even(rmz_positive (p * p)) = true).
    {
        induction p.
        - reflexivity.
        - simpl; rewrite Pos.mul_comm. simpl. apply IHp.
        - reflexivity. 
    }
    destruct z;
    reflexivity || simpl; apply rmz_positive_square.
    Qed.

Search ((IZR ?x > 0)%R).

Theorem sqrt_2_irrational:
    irrational (sqrt 2%R)%R.
Proof.
    unfold irrational.
    intros [p [q [q_Z_gt_0 p_q_Z_sqrt_2]]].
    (** The main goal is to prove (p * p)%Z = (2 * q * q)%Z **)

    (** (IZR q > 0)**)
    assert (Hq_gt_0_R: (IZR q > 0)%R).
    { 
        replace 0%R with (IZR 0).
        apply Rlt_gt. apply IZR_lt.
        auto with zarith.
        reflexivity.
    }

    (** (IZR p) = (sqrt 2) * (IZR q) **)
    assert (Hp_eq_q_sqrt2_R: ((IZR p) = (sqrt 2) * (IZR q))%R).
    {
        rewrite <- p_q_Z_sqrt_2;
        field.
        apply Rgt_not_eq.
        apply Hq_gt_0_R.
    }

    (** (IZR p) * (IZR p) = (2 * (IZR q) *(IZR q))%R **)
    assert (Hpp_eq_2qq_R: ((IZR p) * (IZR p) = (2 * (IZR q) * (IZR q)))%R).
    {
        replace (IZR p)%R with ((sqrt 2) * (IZR q))%R.
        replace (sqrt 2 * IZR q * (sqrt 2 * IZR q))%R with 
            ((sqrt 2 * sqrt 2) * (IZR q) * (IZR q))%R by ring.
        replace (sqrt 2 * sqrt 2)%R with 2%R.
        reflexivity.
        symmetry.
        apply sqrt_def.
        replace 0%R with (IZR 0).
        replace 2%R with (IZR 2).
        Search ((IZR ?x) <= (IZR ?y)).
        apply IZR_le.
        auto with zarith.
        - reflexivity.
        - reflexivity. 
    }

    (** p * p = 2 * q * q **)
    assert (Hpp_eq_2qq_Z: (p * p = 2 * q * q)%Z).
    {
       apply eq_IZR.
       repeat rewrite <- mult_IZR in Hpp_eq_2qq_R.
       apply Hpp_eq_2qq_R.
    }

    assert (H_rmz_z_pp_even: Nat.even (rmz_z(p * p)) = true).
    apply rmz_z_square.


    assert (H_rmz_z_qq_even: Nat.even (rmz_z(2 * q * q)) = false).
    {
        replace (2 * q * q)%Z with (2 * (q * q))%Z by ring.
        rewrite rmz_z_mult_2.
        - rewrite n_Sn_even; rewrite rmz_z_square; reflexivity.
        - auto with zarith.
    }

    assert (H_rmz_z_pp_eq_2qq_Z: Nat.even(rmz_z(p * p)) = 
                                    Nat.even(rmz_z(2 * q * q))).
    { rewrite Hpp_eq_2qq_Z. reflexivity. }


    rewrite H_rmz_z_pp_even in H_rmz_z_pp_eq_2qq_Z.
    rewrite H_rmz_z_qq_even in H_rmz_z_pp_eq_2qq_Z.
    inversion H_rmz_z_pp_eq_2qq_Z.
    Qed.