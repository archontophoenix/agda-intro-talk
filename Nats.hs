module Nats where

data Nat = Z | S Nat

(+):: Nat -> Nat -> Nat
(+) Z n = n
-- Haskell is confused about
-- whether I mean Prelude.+
(+) (S m) n = S ((Nats.+) m n)