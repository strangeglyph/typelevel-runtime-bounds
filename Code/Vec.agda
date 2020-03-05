module Vec where

open import Level using (Level ; Lift ; lift) renaming (suc to lsuc)
open import Data.Vec hiding (insert; _>>=_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Data.Product using (_,_; _×_)
open import Data.Sum.Base
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Induction.WellFounded using (Acc)
open import Data.Nat.Induction using (<-wellFounded)

open import DecTree
open import NatProp
open import Util
open import Nat.Log

private
    variable
        a : Level
        A : Set a

-- -- Vector-based specializations of DecTree -- --

VecTree : Set a -> ℕ -> ℕ -> Set (lsuc a)
VecTree A l h = DecTree A (Vec A l) h

-- -- Algorithms -- --


-- Insert a value into a sorted vector
insert : {n : ℕ} -> A -> Vec A n -> VecTree A (suc n) n
insert k [] = Leaf [ k ]
insert k (x ∷ xs) = compare k , x
                    yes> Leaf (k ∷ x ∷ xs)
                    no>  (x ∷_ <$> insert k xs)



-- Merge two sorted vectors
merge : {m n : ℕ} -> Vec A n -> Vec A m -> VecTree A (n + m) (n + m)
merge [] ys = delay (len ys)(Leaf ys)
merge {A = A} {n = suc n} (x ∷ xs) [] = delay' (suc n) (Leaf (x ∷ (subst (Vec A) (sym $ +-identityʳ n) xs)))
merge {A = A} {m = suc m'} {n = suc n'} (x ∷ xs) (y ∷ ys) = subst (VecTree A (n + m)) (cong suc ⊔-idem-suc-xy) (
                           if[ Vec A ] x ≤? y
                           then (x ∷_ <$> merge xs (y ∷ ys))
                           else (y ∷_ <$> merge (x ∷ xs) ys) by (cong suc $ sym $ +-suc n' m'))
   where
     m : ℕ
     m = suc m'
     n : ℕ
     n = suc n'




pivot-constr : ℕ -> {l₁ l₂ : ℕ} -> Vec A l₁ × Vec A l₂ -> Set
pivot-constr l {l₁} {l₂} _ = l₁ + l₂ ≡ l

record SplitVec (A : Set a) (l : ℕ) : Set a where
    constructor _,_by_
    field
        {l₁ l₂} : ℕ
        left : Vec A l₁
        right : Vec A l₂
        proof : l₁ + l₂ ≡ l


PivotTree : (A : Set a) -> (l h : ℕ) -> Set (lsuc a)
PivotTree A l h = DecTree A (SplitVec A l) h

pivot-append-l : {l : ℕ} -> A -> SplitVec A l -> SplitVec A (suc l)
pivot-append-l x (left , right by pf) = (x ∷ left) , right by cong suc pf

pivot-append-r : {l : ℕ} -> A -> SplitVec A l -> SplitVec A (suc l)
pivot-append-r x (left , right by pf) = left , x ∷ right by trans (+-suc (len left) (len right)) (cong suc pf)


-- Split a vector into values smaller and larger than a pivot element
split-pivot : {l : ℕ}-> A -> Vec A l -> PivotTree A l l
split-pivot _ [] = Leaf $ [] , [] by refl
split-pivot {A = A} {l = suc l'} k (x ∷ xs) =  subst (PivotTree A (suc l')) (⊔-idem (suc l')) (
                             compare x , k
                             yes> (pivot-append-l x <$> split-pivot k xs)
                             no>  (pivot-append-r x <$> split-pivot k xs))


-- Sort a vector using merge sort
quick-sort : {l : ℕ} -> Vec A l -> VecTree A l (l * l)
quick-sort {l = l} xs = quick-sort-step xs (<-wellFounded l)
    where
      quick-sort-step : {l : ℕ} -> Vec A l -> Acc _<_ l -> VecTree A l (l * l)
      quick-sort-step [] _ = Leaf []
      quick-sort-step (x ∷ []) _ = delay 1 (Leaf [ x ])
      quick-sort-step {A = A} {l = suc l} (x ∷ xs@(y ∷ _)) (Acc.acc rs) = delay' 1 (split-pivot x xs >>= recurse)
        where
            recurse : SplitVec A l -> VecTree A (suc l) (l * suc l)
            recurse split@(left , right by pf) =
                height-≡ (cong (λ x -> x * suc x) pf) $
                height-≡ (sym (*-suc (l₁ + l₂) (l₁ + l₂))) $
                delay' (l₁ + l₂) $
                    height-≡ (sym (binom-identity l₁ l₂)) $
                    delay (2 * l₁ * l₂) $
                            quick-sort-step left (rs l₁ (s≤s (m≤m+n≡k pf)))
                        >>= λ (l : Vec A l₁) -> quick-sort-step right (rs l₂ (s≤s (n≤m+n≡k pf)))
                        <&> λ (r : Vec A l₂) -> subst (Vec A) (trans (+-suc l₁ l₂) (cong suc pf)) $ l ++ x ∷ r
                where
                    l₁ : ℕ
                    l₁ = SplitVec.l₁ split
                    l₂ : ℕ
                    l₂ = SplitVec.l₂ split



take-min : {n : ℕ} -> A -> Vec A n -> DecTree A (A × Vec A n) n
take-min x [] = Leaf $ x , []
take-min x (y ∷ ys) = if' x ≤? y
                 then (take-min x ys <&> λ (e , rs) -> e , y ∷ rs)
                 else (take-min y ys <&> λ (e , rs) -> e , x ∷ rs)


selection-sort : {n : ℕ} -> Vec A n -> VecTree A n (n * n)
selection-sort [] = Leaf []
selection-sort (x ∷ xs) = delay' 1 $ take-min x xs >>= λ (e , rs) -> e ∷_ <$> recurse rs
  where
    recurse : {n : ℕ} -> Vec A n -> VecTree A n (n * suc n)
    recurse {A = A} {n = n} xs = subst (VecTree A n) (sym $ *-suc n n) $ delay' n $ selection-sort xs




merge-sort-step : {l : ℕ} -> Vec A l -> Acc _<_ l -> VecTree A l (l * ⌈log₂ l ⌉)
merge-sort-step [] _ = Leaf []
merge-sort-step (x ∷ []) _ = Leaf [ x ]
merge-sort-step {A = A} {l = l} xs@(_ ∷ _ ∷ _) (Acc.acc more) = Data.Product.uncurry recurse $ split xs
     where
         recurse : Vec A ⌈ l /2⌉ -> Vec A ⌊ l /2⌋ -> VecTree A l (l * ⌈log₂ l ⌉)
         recurse left right =
                   subst (λ x -> VecTree A x (l * ⌈log₂ l ⌉)) (⌈n/2⌉+⌊n/2⌋≡n l) $
                   delay-≤ (log₂n/2-bound _) $
                           merge-sort-step left (more ⌈ l /2⌉ (n>1⇒⌈n/2⌉<n _)) >>=
                   λ lr -> merge-sort-step right (more ⌊ l /2⌋ (n>0⇒⌊n/2⌋<n _))>>=
                   λ rr -> merge lr rr

merge-sort : {l : ℕ} -> Vec A l -> VecTree A l (l * ⌈log₂ l ⌉)
merge-sort {l = l} xs = merge-sort-step xs $ <-wellFounded l

