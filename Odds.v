Require Export Nats.

Inductive Odd: Nat -> Prop :=
  | Odd1: Odd (S Z)
  | OddSS:
      forall n: Nat,
        Odd n -> Odd (S (S n)).

Theorem Odd_5:
  Odd (S (S (S (S (S Z))))).
Proof.
  constructor. constructor.
  constructor.
Qed.