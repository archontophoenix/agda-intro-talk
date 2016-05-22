Inductive even: nat -> Prop :=
  | even0: even 0
  | evenSS: forall n: nat, even n -> even (S (S n)).

Inductive odd: nat -> Prop :=
  | oddS: forall n: nat, even n -> odd (S n).

Theorem even_after_odd: forall n: nat, even (S n) -> odd n.
Proof.
  intros. inversion H; subst. constructor. assumption.
Qed.

Theorem odd_then_even: forall n: nat, odd n -> even (S n).
Proof.
  intros. inversion H; subst. constructor. assumption.
Qed.

Theorem even_then_not_even: forall n: nat, even n -> ~ (even (S n)).
Proof.
  intros n H Contra. induction n; inversion Contra; subst.
    apply IHn. assumption. assumption.
Qed.

Theorem even_not_odd: forall n: nat, even n -> ~ (odd n).
Proof.
  intros n H Contra.
  inversion Contra; inversion H; subst;
    apply even_then_not_even in H0; apply H0 in H; assumption.
Qed.

Theorem odd_not_even: forall n: nat, odd n -> ~ (even n).
Proof.
  intros n H Contra.
  inversion Contra; inversion H; subst.
    inversion H.
    apply even_not_odd in Contra.
    apply Contra in H. assumption.
Qed.

Theorem even_or_odd: forall n: nat, even n \/ odd n.
Proof.
  intros. induction n.
    left. constructor.
    inversion IHn.
      right. constructor. assumption.
      left. apply odd_then_even. assumption.
Qed.

Theorem even_dec: forall n: nat, even n \/ ~ (even n).
Proof.
  intros. assert (even n \/ odd n).
    apply even_or_odd.
  inversion H.
    left. assumption.
    right. apply odd_not_even. assumption.
Qed.
