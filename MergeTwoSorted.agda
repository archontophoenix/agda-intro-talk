open import Data.List
open import Data.Nat
open import Data.Sum
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

module MergeTwoSorted {ℓ ℓ₁ ℓ₂} (
  ord : DecTotalOrder ℓ ℓ₁ ℓ₂) where

open import MergeSort(ord)

total≤A : Total _≤A_
total≤A =
  IsTotalOrder.total
    (IsDecTotalOrder.isTotalOrder (DecTotalOrder.isDecTotalOrder ord))

oppositeOfLeq : (a b : A) → ¬ (a ≤A b) → (b ≤A a)
oppositeOfLeq a b contra with total≤A a b
oppositeOfLeq a b contra | inj₁ a≤b with contra a≤b
oppositeOfLeq a b contra | inj₁ a≤b | ()
oppositeOfLeq a b contra | inj₂ b≤a = b≤a

mergeOneSortedLeft :
  (a : A) → (lr : List A) → Sorted lr →
  Sorted (merge (a ∷ []) lr)
mergeOneSortedLeft a [] sortedNil = sortedOne
mergeOneSortedLeft a (hr ∷ []) sortedOne with a ≤A? hr
... | yes a≤hr = sortedLeq a≤hr sortedOne
... | no a>hr = sortedLeq (oppositeOfLeq a hr a>hr) sortedOne
mergeOneSortedLeft a (hr ∷ htr ∷ ttr) (sortedLeq hr≤htr sortedTr) with a ≤A? hr
... | yes a≤hr = sortedLeq a≤hr (sortedLeq hr≤htr sortedTr)
... | no a>hr with oppositeOfLeq a hr a>hr
... | hr≤a = {!!}

mergeTwoSorted : (ll lr : List A) →
  Sorted ll → Sorted lr →
  Sorted (merge ll lr)
mergeTwoSorted [] _ sortedNil sortedR = sortedR
mergeTwoSorted (hl ∷ []) lr sortedOne sortedR = {!!}
mergeTwoSorted (hl ∷ htl ∷ ttl) [] (sortedLeq hl≤htl sortedTl) sortedNil = {!!}
mergeTwoSorted (hl ∷ htl ∷ ttl) (hr ∷ []) (sortedLeq hl≤htl sortedTl) sortedOne = {!!}
mergeTwoSorted (hl ∷ htl ∷ ttl) (hr ∷ htr ∷ ttr) (sortedLeq hl≤htl sortedTl) (sortedLeq hr≤htr sortedTr) = {!!}

