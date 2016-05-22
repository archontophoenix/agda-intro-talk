module Nats where

data Nat : Set where
  Z : Nat
  S : Nat → Nat

_+_ : Nat → Nat → Nat
Z + n = n
(S m) + n = S (m + n)
