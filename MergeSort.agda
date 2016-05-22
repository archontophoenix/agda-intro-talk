open import Data.List
open import Data.Nat hiding (_⊔_)
open import Data.Nat.Properties
open import Data.Product
open import Level hiding (suc)
open import Relation.Binary
open import Relation.Nullary

module MergeSort {ℓ ℓ₁ ℓ₂} (
  ord : DecTotalOrder ℓ ℓ₁ ℓ₂) where

A : Set ℓ
A = DecTotalOrder.Carrier ord

_=A_ : Rel A ℓ₁
_=A_ = DecTotalOrder._≈_ ord

_≤A_ : Rel A ℓ₂
_≤A_ = DecTotalOrder._≤_ ord

_=A?_ : Decidable _=A_
_=A?_ =
 IsDecTotalOrder._≟_
  (DecTotalOrder.isDecTotalOrder ord)

_≤A?_ : Decidable _≤A_
_≤A?_ =
  IsDecTotalOrder._≤?_
   (DecTotalOrder.isDecTotalOrder ord)

-- Part 1: the sorting algorithm proper -------------

split : List A → List A × List A
split [] = [] , []
split (a ∷ []) = (a ∷ []) , []
split (a0 ∷ a1 ∷ t) with split t
... | tl , tr = (a0 ∷ tl) , (a1 ∷ tr)

merge : List A → List A → List A
merge [] right = right
merge left [] = left
merge (hl ∷ tl) (hr ∷ tr) with hl ≤A? hr
... | yes _ = hl ∷ (merge tl (hr ∷ tr))
... | no _ = hr ∷ (merge (hl ∷ tl) tr)

{- Traditional definition of mergeSort
-- Does not pass termination checker
mergeSort : List A → List A
mergeSort [] = []
mergeSort (a ∷ []) = a ∷ []
mergeSort (a0 ∷ a1 ∷ t) with split t
... | tl , tr =
  merge (mergeSort (a0 ∷ tl)) (mergeSort (a1 ∷ tr))
-}

-- Lemma: length limit on left of split
splitLenLeft :
  {lim : ℕ} → (a0 a1 : A) →
  (t : List A) →
  (p : suc (length (a0 ∷ a1 ∷ t)) ≤ suc lim) →
  (suc (length (a0 ∷ (proj₁ (split t)))) ≤ lim)
splitLenLeft a0 a1 [] (s≤s p) = p
splitLenLeft a0 a1 (_ ∷ []) (s≤s p) = p
splitLenLeft
    a0 a1 (a2 ∷ a3 ∷ t) (s≤s (s≤s (s≤s p))) =
  ≤-step (s≤s (splitLenLeft a2 a3 t (s≤s p)))

-- Lemma: length limit on right of split
splitLenRight :
  {lim : ℕ} → (a0 a1 : A) →
  (t : List A) →
  (p : suc (length (a0 ∷ a1 ∷ t)) ≤ suc lim) →
  (suc (length (a1 ∷ (proj₂ (split t)))) ≤ lim)
splitLenRight a0 a1 [] (s≤s p) = p
splitLenRight a0 a1 (_ ∷ []) (s≤s (s≤s p)) =
  ≤-step p
splitLenRight
    a0 a1 (a2 ∷ a3 ∷ t) (s≤s (s≤s (s≤s p))) =
  ≤-step (s≤s (splitLenRight a2 a3 t (s≤s p)))

-- Decreasing limit placates the termination checker
mergeSortLimited :
  (lim : ℕ) → (l : List A) →
  (p : suc (length l) ≤ lim) →
  List A
mergeSortLimited 0 _ ()
mergeSortLimited (suc n) [] _ = []
mergeSortLimited (suc n) (a ∷ []) _ = a ∷ []
{- This doesn't work:
-- Agda doesn't seem to know that
--   split t = proj₁ (split t) , proj₂ (split t)
mergeSortLimited (suc n) (a0 ∷ a1 ∷ t) p with split t
... | tl , tr =
  merge
   (mergeSortLimited n (a0 ∷ tl)
     (splitLenLeft a0 a1 t p))
   (mergeSortLimited n (a1 ∷ tr)
     (splitLenRight a0 a1 t p)) -}
mergeSortLimited (suc n) (a0 ∷ a1 ∷ t) p =
  merge
   (mergeSortLimited n (a0 ∷ (proj₁ (split t)))
     (splitLenLeft a0 a1 t p))
   (mergeSortLimited n (a1 ∷ (proj₂ (split t)))
     (splitLenRight a0 a1 t p))

-- Reflexivity of ≤ is predefined, but it's buried
-- so deep in Nat.decTotalOrder that it's more
-- concise just to prove it again from scratch:
n≤n : (n : ℕ) → n ≤ n
n≤n 0 = z≤n
n≤n (suc n) = s≤s (n≤n n)

mergeSort : List A → List A
mergeSort l =
  mergeSortLimited
    (suc (length l)) l (n≤n (suc (length l)))

-- Part 2: Definitions of properties to be proved ---

-- a +> as => as′:
-- a inserted into as yields as′
data _+>_=>_ (a : A) : List A → List A → Set ℓ where
  here : {as : List A} → (a +> as => (a ∷ as))
  there : {aa : A}{as as′ : List A} →
    (a +> as => as′) → (a +> (aa ∷ as) => (aa ∷ as′))

-- Perm as as′:
-- as is a permutation of as′
data Perm : List A → List A → Set ℓ where
  permNil : Perm [] []
  permIns : {as as′ as′′ : List A}{a : A} →
    Perm as as′ → (a +> as′ => as′′) →
    Perm (a ∷ as) as′′

-- Sorted as:
-- as is sorted
data Sorted : List A → Set (ℓ ⊔ ℓ₂) where
  sortedNil : Sorted []
  sortedOne : {a : A} → Sorted (a ∷ [])
  sortedLeq : {a aa : A }{tail : List A} →
    (a ≤A aa) → Sorted (aa ∷ tail) →
    Sorted (a ∷ aa ∷ tail)

-- SortedPerm as as′:
-- as′ is a sorted permutation of as
data SortedPerm (as : List A) :
    List A → Set (ℓ ⊔ ℓ₂) where
  both : {as′ : List A} →
    Perm as as′ → Sorted as′ →
    SortedPerm as as′

-- Part 3: Proofs of properties of the algorithm ----

-- Lemma
sortedListHasSortedTail :
  (h : A) → (t : List A) → Sorted (h ∷ t) → Sorted t
sortedListHasSortedTail h [] sortedOne = sortedNil
sortedListHasSortedTail
  h (h′ ∷ t′) (sortedLeq _ sTail) =
    sTail

{- Where we'd like to get to:
mergeSortWorks :
  (l : List A) → SortedPerm l (mergeSort l)
mergeSortWorks l = {!!}
-}
