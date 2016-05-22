open import Nats

data Odd : Nat → Set where
  Odd1 : Odd (S Z)
  OddSS :
    {n : Nat} → Odd n →
      Odd (S (S n))

Odd5 :
  Odd (S (S (S (S (S Z)))))
Odd5 = OddSS (OddSS Odd1)
