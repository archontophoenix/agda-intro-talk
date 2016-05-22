module Nats

%access public export
%default total

-- The name "Nat" conflicts
-- with built-in Nat

data Nat' = Z' | S' Nat'

(+): Nat' -> Nat' -> Nat'
(+) Z' n = n
(+) (S' m) n = S' (m + n)