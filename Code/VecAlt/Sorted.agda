module VecAlt.Sorted where

open import Level using (Level ; Lift ; lift) renaming (suc to lsuc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec hiding (insert ; _>>=_)
open import Data.Product

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Induction.WellFounded using (Acc)
open import Data.Nat.Induction using (<-wellFounded)
open import Function

open import Util
open import DecTreeAlt
open import Nat.Props
open import Nat.Log
open import VecAlt.Base

private
    variable
        a : Level
        A : Set a


-- Vector-based specializations of DecTree --
VecTree : Set a -> ℕ -> ℕ -> Set (lsuc a)
VecTree A l h = DecTree A (Vec A l) h


-- Insert a value into a sorted vector
insert : {n : ℕ} -> A -> Vec A n -> VecTree A (suc n) n
insert k [] = return [ k ]
insert k (x ∷ xs) = if k ≤? x
                    then[ s≤s z≤n ] return (k ∷ x ∷ xs)
                    else[ ≤-refl ] (x ∷_ <$> insert k xs)



-- Merge two sorted vectors
merge-by : {X A : Set a} -> {m n : ℕ} -> (X -> A) -> Vec X n -> Vec X m -> DecTree A (Vec X (n + m)) (n + m)
merge-by _ [] ys = return {k = len ys} ys
merge-by {X = X} {n = suc n} _ (x ∷ xs) [] = return {k = suc n + 0} $ x ∷ (subst (Vec X) (sym $ +-identityʳ n) xs)
merge-by {X = X} {A = A} {m'} {n'} f (x ∷ xs) (y ∷ ys) =
                                if' f x ≤? f y
                                then (x ∷_ <$> merge-by f xs (y ∷ ys))
                                else (y ∷_ <$> (double-subst (sym $ +-suc (pred n') (pred m')) $ merge-by f (x ∷ xs) ys))
   where
       m = suc m'
       n = suc n'
       double-subst : {n m : ℕ} -> n ≡ m -> DecTree A (Vec X n) n -> DecTree A (Vec X m) m
       double-subst pf t = subst (λ n → DecTree A (Vec X n) n) pf t

merge : {m n : ℕ} -> Vec A n -> Vec A m -> VecTree A (n + m) (n + m)
merge = merge-by id


-- Sort a vector using quick sort
quick-sort : {l : ℕ} -> Vec A l -> VecTree A l (l * l)
quick-sort {l = l} xs = quick-sort-step xs (<-wellFounded l)
    where
      quick-sort-step : {l : ℕ} -> Vec A l -> Acc _<_ l -> VecTree A l (l * l)
      quick-sort-step [] _ = return []
      quick-sort-step (x ∷ []) _ = return {k = 1} [ x ]
      quick-sort-step {A = A} {l = suc l} (x ∷ xs@(y ∷ _)) (Acc.acc rs) = chain (split-pivot x xs) recurse (n≤1+n _)
        where
            recurse : SplitVec A l -> VecTree A (suc l) (l * suc l)
            recurse split@(left , right by pf) =
                        chain (quick-sort-step left (rs l₁ (s≤s (m≤m+n≡k pf))))
                              (λ (l : Vec A l₁) -> quick-sort-step right (rs l₂ (s≤s (n≤m+n≡k pf)))
                                                   <&> λ (r : Vec A l₂) -> subst (Vec A) (trans (+-suc l₁ l₂) (cong suc pf)) $ l ++ x ∷ r)
                        (≤-trans binom-bound split-len-bound)
                where
                    open ≤-Reasoning
                    l₁ : ℕ
                    l₁ = SplitVec.l₁ split
                    l₂ : ℕ
                    l₂ = SplitVec.l₂ split
                    binom-bound : l₁ * l₁ + l₂ * l₂ ≤ (l₁ + l₂) * (l₁ + l₂)
                    binom-bound = ≤-trans (m≤m+n (l₁ * l₁ + l₂ * l₂) _) (≤-reflexive $ sym $ binom-identity l₁ l₂)
                    split-len-bound : (l₁ + l₂) * (l₁ + l₂) ≤ l * suc l
                    split-len-bound = begin
                            (l₁ + l₂) * (l₁ + l₂)      ≡⟨ cong₂ (_*_) pf pf ⟩
                            l * l                      ≤⟨ m≤n+m (l * l) l ⟩
                            suc l * l                  ≡⟨ sym $ *-suc l l ⟩
                            l * suc l                  ∎



-- Sort a vector using selection sort
selection-sort : {n : ℕ} -> Vec A n -> VecTree A n (n * n)
selection-sort [] = return []
selection-sort {n = n@(suc n')} (x ∷ xs) = chain (take-min x xs)
                                                 (λ (e , rs) -> e ∷_ <$> selection-sort rs)
                                           (≤-trans (≤-reflexive $ sym $ *-suc n' n') (m≤n+m (n' * n) n))


-- Sort a vector using merge sort
private
    merge-sort-step : {X A : Set a} -> {l : ℕ} -> (X -> A) -> Vec X l -> Acc _<_ l -> DecTree A (Vec X l) (l * ⌈log₂ l ⌉)
    merge-sort-step _ [] _ = return []
    merge-sort-step _ (x ∷ []) _ = return [ x ]
    merge-sort-step {X = X} {A = A} {l = l} f xs@(_ ∷ _ ∷ _) (Acc.acc more) =
            chain (merge-sort-step f left (more ⌈ l /2⌉ (n>1⇒⌈n/2⌉<n _)))
                  (λ sort-left → merge-sort-step f right (more ⌊ l /2⌋ (n>0⇒⌊n/2⌋<n _))
                                 >>= (λ sort-right → subst (Vec X) (⌈n/2⌉+⌊n/2⌋≡n l) <$> merge-by f sort-left sort-right))
            (log₂n/2-bound _)
        where
            left = proj₁ $ split xs
            right = proj₂ $ split xs


merge-sort : {l : ℕ} -> Vec A l -> VecTree A l (l * ⌈log₂ l ⌉)
merge-sort {l = l} xs = merge-sort-step id xs $ <-wellFounded l

merge-sort-by : {X A : Set a} -> {l : ℕ} -> (X -> A) -> Vec X l -> DecTree A (Vec X l) (l * ⌈log₂ l ⌉)
merge-sort-by {l = l} f xs = merge-sort-step f xs $ <-wellFounded l

