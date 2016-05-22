open import Data.Nat
open import Data.Sum
open import Relation.Binary.Core
open import Relation.Nullary

module EvensAndOdds where

data even : ℕ → Set where
  even0 : even 0
  evenSS : {n : ℕ} → even n → even (suc (suc n))

data odd : ℕ → Set where
  oddS : {n : ℕ} → even n → odd (suc n)

evenAfterOdd : {n : ℕ} → even (suc n) → odd n
evenAfterOdd (evenSS evenPredN) =
  oddS evenPredN

oddThenEven : {n : ℕ} → odd n → even (suc n)
oddThenEven (oddS evenPredN) =
  evenSS evenPredN

evenNotOdd : {n : ℕ} → even n → ¬ (odd n)
evenNotOdd (evenSS evenPPN) (oddS evenPN) =
  evenNotOdd evenPN (oddS evenPPN)

oddNotEven : {n : ℕ} → odd n → ¬ (even n)
oddNotEven (oddS evenPN) (evenSS evenPPn) =
  oddNotEven (oddS evenPPn) evenPN

evenOrOdd : (n : ℕ) → even n ⊎ odd n
evenOrOdd 0 = inj₁ even0
evenOrOdd (suc pN) with evenOrOdd pN
evenOrOdd (suc pN)
  | inj₁ evenPN = inj₂ (oddS evenPN)
evenOrOdd (suc pN)
  | inj₂ oddPN  = inj₁ (oddThenEven oddPN)

evenDecidable : (n : ℕ) → even n ⊎ ¬ (even n)
evenDecidable n with evenOrOdd n
evenDecidable n
  | inj₁ evenN = inj₁ evenN
evenDecidable n
  | inj₂ oddN  = inj₂ (oddNotEven oddN)
