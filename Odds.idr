module Odds

import Nats

data Odd: Nat' -> Type where
  Odd1: Odd (S' Z')
  OddSS:
    Odd n -> Odd (S' (S' n))

Odd5:
  Odd (S' (S' (S' (S' (S' Z')))))
Odd5 = OddSS (OddSS Odd1)
