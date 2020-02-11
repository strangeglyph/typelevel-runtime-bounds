module Vec where

open import Level using (Level)
open import Data.Vec hiding (insert)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product using (_,_; _×_)
open import Data.Sum.Base
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Sigma
open import DecTree

private
    variable
        a : Level
        A : Set a

-- -- Vector-based specializations of DecTree -- --

append : {n : ℕ} -> A -> Vec A n -> Σ ℕ (Vec A)
append x xs = σ (x ∷ xs)

-- Decision tree which constructs a new vector from base elements
VecTree : (A : Set a) -> (height : ℕ) -> Set a
VecTree A height = DecTree A ℕ A (Vec A) append height



data VecPair (A : Set a) : (ℕ × ℕ) -> Set a where
    _,,_ : {l₁ l₂ : ℕ} -> Vec A l₁ -> Vec A l₂ -> VecPair A (l₁ , l₂)

append2 : {l : ℕ × ℕ} -> (A ⊎ A) -> VecPair A l -> Σ (ℕ × ℕ) (VecPair A)
append2 {l = l₁ , l₂} (inj₁ x) (left ,, right) = σ { key = 1 + l₁ , l₂ } ((x ∷ left) ,, right)
append2 {l = l₁ , l₂} (inj₂ y) (left ,, right) = σ { key = l₁ , 1 + l₂ } (left ,, (y ∷ right))


-- Decision tree which constructs a pair of vectors. Which vector is added to each step depends on
-- whether the base elemen is inj₁ or inj₂
VecPairTree : (A : Set a) -> (height : ℕ) -> Set a
VecPairTree A height = DecTree A (ℕ × ℕ) (A ⊎ A) (VecPair A) append2 height



-- -- Algorithms -- --


-- Insert a value into a sorted vector
insert : {n : ℕ} -> A -> Vec A n -> VecTree A n
insert k [] = Leaf [ k ]
insert k (x ∷ xs) = compare k , x
                    yes> k , Leaf (x ∷ xs)
                    no>  x , insert k xs





⊔-idem-under-≡ : {x y : ℕ} -> (x ≡ y) -> x ⊔ y ≡ x
⊔-idem-under-≡ {x} {y} equ = trans (cong (x ⊔_) (sym equ)) (⊔-idem x)

⊔-idem-suc-xy : {x y : ℕ} -> (x + (1 + y)) ⊔ (1 + (x + y)) ≡ (x + (1 + y))
⊔-idem-suc-xy {x} {y} = ⊔-idem-under-≡ (+-suc x y)

-- Merge two sorted vectors
merge : {m n : ℕ} -> Vec A n -> Vec A m -> VecTree A (n + m)
merge [] ys = OverLeaf ys
merge (x ∷ xs) [] = OverLeaf (x ∷ xs)
merge {A = A} (x ∷ xs) (y ∷ ys) = subst (VecTree A) (cong suc ⊔-idem-suc-xy) (
                           compare x , y
                           yes> x , merge xs (y ∷ ys)
                           no>  y , merge (x ∷ xs) ys)


-- Split a vector into values smaller and larger than a pivot element
split-pivot : {l : ℕ} -> A -> Vec A l -> VecPairTree A l
split-pivot _ [] = Leaf ([] ,, [])
split-pivot {A = A} {l = l} k (x ∷ xs) = subst (VecPairTree A) (⊔-idem l) (
                            compare x , k
                            yes> inj₁ x , split-pivot k xs
                            no>  inj₂ x , split-pivot k xs)



-- Sort a vector using merge sort
merge-sort : {l : ℕ} -> Vec A l -> VecTree A l
merge-sort [] = Leaf []
merge-sort xs@(x ∷ _) = {! Embed split-pivot x xs !}
