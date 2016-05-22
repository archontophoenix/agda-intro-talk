module EvensAndOdds

%default total

data Even: Nat -> Type where
  EvenZ: Even Z
  EvenSS: Even n -> Even (S (S n))

data Odd: Nat -> Type where
  OddS: Even n -> Odd (S n)

evenAfterOdd: Even (S n) -> Odd n
evenAfterOdd (EvenSS evenPredN) = OddS evenPredN

oddThenEven: Odd n -> Even (S n)
oddThenEven (OddS evenPredN) = EvenSS evenPredN

evenThenNotEven: Even n -> Even (S n) -> Void
evenThenNotEven (EvenSS evenPPN) (EvenSS evenPN) =
  evenThenNotEven evenPPN evenPN

evenNotOdd: Even n -> Odd n -> Void
evenNotOdd (EvenSS evenPPN) (OddS evenPN) =
  evenNotOdd evenPN (OddS evenPPN)

oddNotEven: Odd n -> (Even n) -> Void
oddNotEven (OddS evenPN) (EvenSS evenPPn) =
  oddNotEven (OddS evenPPn) evenPN

evenOrOdd: (n: Nat) -> Either (Even n) (Odd n)
evenOrOdd Z = Left EvenZ
evenOrOdd (S pN) with (evenOrOdd pN)
  | Left evenPN = Right (OddS evenPN)
  | Right oddPN  = Left (oddThenEven oddPN)

evenDecidable:
  (n: Nat) -> Either (Even n) (Even n -> Void)
evenDecidable n with (evenOrOdd n)
  | Left evenN = Left evenN
  | Right oddN  = Right (oddNotEven oddN)
