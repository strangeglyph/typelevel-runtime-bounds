module Vec.Sorted where

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
open import DecTree
open import Nat.Props
open import Nat.Log
open import Vec.Base

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
                    then return (k ∷ x ∷ xs)
                    else (x ∷_ <$> insert k xs)


-- Merge two sorted vectors
merge-by : {X A : Set a} -> {m n : ℕ} -> (X -> A) -> Vec X n -> Vec X m -> DecTree A (Vec X (n + m)) (n + m)
merge-by _ [] ys = delay (len ys) (return ys)
merge-by {X = X} {A = A} {n = suc n} _ (x ∷ xs) [] = delay' (suc n) (return (x ∷ (subst (Vec X) (sym $ +-identityʳ n) xs)))
merge-by {X = X} {A = A} {m = suc m'} {n = suc n'} f (x ∷ xs) (y ∷ ys) =
                            subst (DecTree A (Vec X (n + m))) (cong suc ⊔-idem-suc-xy) $
                                if[ Vec X ] f x ≤? f y
                                then (x ∷_ <$> merge-by f xs (y ∷ ys))
                                else (y ∷_ <$> merge-by f (x ∷ xs) ys) by (cong suc $ sym $ +-suc n' m')
   where
       m : ℕ
       m = suc m'
       n : ℕ
       n = suc n'

merge : {m n : ℕ} -> Vec A n -> Vec A m -> VecTree A (n + m) (n + m)
merge = merge-by id


-- Sort a vector using quick sort
quick-sort : {l : ℕ} -> Vec A l -> VecTree A l (l * l)
quick-sort {l = l} xs = quick-sort-step xs (<-wellFounded l)
    where
      quick-sort-step : {l : ℕ} -> Vec A l -> Acc _<_ l -> VecTree A l (l * l)
      quick-sort-step [] _ = return []
      quick-sort-step (x ∷ []) _ = delay 1 (return [ x ])
      quick-sort-step {A = A} {l = suc l} (x ∷ xs@(y ∷ _)) (Acc.acc rs) = delay' 1 (split-pivot x xs >>=' recurse)
        where
            recurse : SplitVec A l -> VecTree A (suc l) (l * suc l)
            recurse split@(left , right by pf) =
                height-≡ (cong (λ x -> x * suc x) pf) $
                height-≡ (sym (*-suc (l₁ + l₂) (l₁ + l₂))) $
                delay' (l₁ + l₂) $
                    height-≡ (sym (binom-identity l₁ l₂)) $
                    delay (2 * l₁ * l₂) $
                            quick-sort-step right (rs l₂ (s≤s (n≤m+n≡k pf)))
                        >>= λ (r : Vec A l₂) -> quick-sort-step left (rs l₁ (s≤s (m≤m+n≡k pf)))
                        <&> λ (l : Vec A l₁) -> subst (Vec A) (trans (+-suc l₁ l₂) (cong suc pf)) $ l ++ x ∷ r
                where
                    l₁ : ℕ
                    l₁ = SplitVec.l₁ split
                    l₂ : ℕ
                    l₂ = SplitVec.l₂ split


-- Sort a vector using selection sort
selection-sort : {n : ℕ} -> Vec A n -> VecTree A n (n * n)
selection-sort [] = return []
selection-sort (x ∷ xs) = delay' 1 $ take-min x xs >>=' λ (e , rs) -> e ∷_ <$> recurse rs
    where
        recurse : {n : ℕ} -> Vec A n -> VecTree A n (n * suc n)
        recurse {A = A} {n = n} xs = subst (VecTree A n) (sym $ *-suc n n) $ delay' n $ selection-sort xs


-- Sort a vector using merge sort
private
    merge-sort-step : {X A : Set a} -> {l : ℕ} -> (X -> A) -> Vec X l -> Acc _<_ l -> DecTree A (Vec X l) (l * ⌈log₂ l ⌉)
    merge-sort-step _ [] _ = return []
    merge-sort-step _ (x ∷ []) _ = return [ x ]
    merge-sort-step {X = X} {A = A} {l = l} f xs@(_ ∷ _ ∷ _) (Acc.acc more) =
        delay-≤ (log₂n/2-bound _) $ do
            let (left , right) = split xs
            sort-left <- merge-sort-step f left (more ⌈ l /2⌉ (n>1⇒⌈n/2⌉<n _))
            sort-right <- merge-sort-step f right (more ⌊ l /2⌋ (n>0⇒⌊n/2⌋<n _))
            subst (Vec X) (⌈n/2⌉+⌊n/2⌋≡n l) <$> merge-by f sort-left sort-right

merge-sort : {l : ℕ} -> Vec A l -> VecTree A l (l * ⌈log₂ l ⌉)
merge-sort {l = l} xs = merge-sort-step id xs $ <-wellFounded l

merge-sort-by : {X A : Set a} -> {l : ℕ} -> (X -> A) -> Vec X l -> DecTree A (Vec X l) (l * ⌈log₂ l ⌉)
merge-sort-by {l = l} f xs = merge-sort-step f xs $ <-wellFounded l
