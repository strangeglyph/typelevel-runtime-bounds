module Vec where

open import Level using (Level ; Lift ; lift) renaming (suc to lsuc)
open import Data.Vec hiding (insert; _>>=_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product using (_,_; _×_)
open import Data.Sum.Base
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Induction.WellFounded using (Acc)
open import Data.Nat.Induction using (<-wellFounded)

open import Sigma
open import DecTree
open import NatProp

private
    variable
        a : Level
        A : Set a

-- -- Vector-based specializations of DecTree -- --

append : {n : ℕ} -> A -> Vec A n -> Σ ℕ (Vec A)
append x xs = σ (x ∷ xs)

-- Decision tree which constructs a new vector from base elements
VecTree : (A : Set a) -> (height : ℕ) -> Set (lsuc a)
VecTree A height = DecTree A ℕ (Vec A) height



data VecPair (A : Set a) : (ℕ × ℕ) -> Set a where
    _,,_ : {l₁ l₂ : ℕ} -> Vec A l₁ -> Vec A l₂ -> VecPair A (l₁ , l₂)

append-l : {(l₁ , l₂) : ℕ × ℕ} -> A -> VecPair A (l₁ , l₂) -> VecPair A (1 + l₁ , l₂)
append-l x (xs ,, ys) = (x ∷ xs) ,, ys

append-r : {(l₁ , l₂) : ℕ × ℕ} -> A -> VecPair A (l₁ , l₂) -> VecPair A (l₁ , 1 + l₂)
append-r y (xs ,, ys) = xs ,, (y ∷ ys)

-- Decision tree which constructs a pair of vectors.
VecPairTree : (A : Set a) -> (height : ℕ) -> Set (lsuc a)
VecPairTree A height = DecTree A (ℕ × ℕ) (VecPair A) height


BoundedVecTree : (A : Set a) -> (Constr : {n : ℕ} -> Vec A n -> Set) -> (height : ℕ) -> Set (lsuc a)
BoundedVecTree A Constr h = DecTree A ℕ (Constrained (Vec A) Constr) h

BoundedVecPairTree : (A : Set a) -> (Constr : {n : ℕ × ℕ} -> VecPair A n -> Set) -> (height : ℕ) -> Set (lsuc a)
BoundedVecPairTree A Constr h = DecTree A (ℕ × ℕ) (Constrained (VecPair A) Constr) h

-- -- Algorithms -- --


-- Insert a value into a sorted vector
insert : {n : ℕ} -> A -> Vec A n -> VecTree A n
insert k [] = Leaf [ k ]
insert k (x ∷ xs) = compare k , x
                    yes> Leaf (k ∷ x ∷ xs)
                    no>  (append x <$> insert k xs)



-- Merge two sorted vectors
merge : {m n : ℕ} -> Vec A n -> Vec A m -> VecTree A (n + m)
merge [] ys = delay (Leaf ys)
merge (x ∷ xs) [] = delay (Leaf (x ∷ xs))
merge {A = A} (x ∷ xs) (y ∷ ys) = subst (VecTree A) (cong suc ⊔-idem-suc-xy) (
                           compare x , y
                           yes> (append x <$> merge xs (y ∷ ys))
                           no>  (append y <$> merge (x ∷ xs) ys))




pivot-constr : ℕ -> {n : ℕ × ℕ} -> VecPair A n -> Set
pivot-constr l {n = l₁ , l₂} _ = l₁ + l₂ ≡ l


PivotTree : (A : Set a) -> (l h : ℕ) -> Set (lsuc a)
PivotTree A l h = BoundedVecPairTree A (pivot-constr l) h


pivot-append-l : {l : ℕ} -> A -> {n : ℕ × ℕ} -> Constrained (VecPair A) (pivot-constr l) n -> Σ (ℕ × ℕ) (Constrained (VecPair A) (λ {(l₁ , l₂)} _ -> l₁ + l₂ ≡ (suc l)))
pivot-append-l x (constr vecs pf) = σ (constr (append-l x vecs) (cong suc pf))

pivot-append-r : {l : ℕ} -> {n : ℕ × ℕ} -> A -> Constrained (VecPair A) (pivot-constr l) n -> Σ (ℕ × ℕ) (Constrained (VecPair A) (pivot-constr (suc l)))
pivot-append-r {n = l₁ , l₂} x (constr vecs pf) = σ (constr (append-r x vecs) (trans (+-suc l₁ l₂) (cong suc pf)))


-- Split a vector into values smaller and larger than a pivot element
split-pivot : {l : ℕ}-> A -> Vec A l -> PivotTree A l l
split-pivot _ [] = Leaf (constr ([] ,, []) refl)
split-pivot {A = A} {l = suc l'} k (x ∷ xs) =  subst (PivotTree A (suc l')) (⊔-idem (suc l')) (
                             compare x , k
                             yes> (pivot-append-l x <$> split-pivot k xs)
                             no>  (pivot-append-r x <$> split-pivot k xs))


-- Sort a vector using merge sort
quick-sort : {l : ℕ} -> Vec A l -> VecTree A (l * l)
quick-sort {l = l} xs = quick-sort-step xs (<-wellFounded l)
    where
      quick-sort-step : {l : ℕ} -> Vec A l -> Acc _<_ l -> VecTree A (l * l)
      quick-sort-step [] _ = Leaf []
      quick-sort-step (x ∷ []) _ = delay (Leaf [ x ])
      quick-sort-step {A = A} {l = suc l} (x ∷ xs@(y ∷ _)) (Acc.acc rs) = delay' {d = 1} (split-pivot x xs >>= recurse)
        where
            recurse : {l' : ℕ × ℕ} -> Constrained (VecPair A) (pivot-constr l) l' -> VecTree A (l * suc l)
            recurse (constr {n₁ , n₂} (left ,, right) pf) =
                subst (VecTree A) (cong (λ x -> x * suc x) pf) $
                subst (VecTree A) (sym (*-suc (n₁ + n₂) (n₁ + n₂))) $
                delay' {d = n₁ + n₂} $
                    subst (VecTree A) (sym (binom-identity n₁ n₂)) $
                    delay {d = 2 * n₁ * n₂ } $
                    fork (quick-sort-step left (rs n₁ (s≤s (m≤m+n≡k pf)))) , (quick-sort-step right (rs n₂ (s≤s (n≤m+n≡k pf))))
                    combine-with λ l r -> σ (l ++ x ∷ r)

