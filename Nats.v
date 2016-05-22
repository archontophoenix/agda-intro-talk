Inductive Nat: Type :=
  | Z: Nat
  | S: Nat -> Nat.

Fixpoint plus (m n: Nat) :=
  match m with
  | Z => n
  | S m' => S (plus m' n)
  end.

Notation "x + y" :=
  (plus x y)
  (at level 50,
    left associativity).
