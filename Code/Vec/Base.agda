module Vec.Base where

open import Level using (Level ; Lift ; lift) renaming (suc to lsuc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Vec
open import Data.Product
open import Data.Maybe
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality
open import Function

open import DecTree
open import Util

private
    variable
        a : Level
        A : Set a

record SplitVec (A : Set a) (l : ℕ) : Set a where
    constructor _,_by_
    field
        {l₁ l₂} : ℕ
        left : Vec A l₁
        right : Vec A l₂
        proof : l₁ + l₂ ≡ l


private
    pivot-append-l : {l : ℕ} -> A -> SplitVec A l -> SplitVec A (suc l)
    pivot-append-l x (left , right by pf) = (x ∷ left) , right by cong suc pf

    pivot-append-r : {l : ℕ} -> A -> SplitVec A l -> SplitVec A (suc l)
    pivot-append-r x (left , right by pf) = left , x ∷ right by trans (+-suc (len left) (len right)) (cong suc pf)


-- Split a vector into values smaller and larger than a pivot element
split-pivot-by : {X A : Set a} -> {l : ℕ} -> (X -> A) -> X -> Vec X l -> DecTree A (SplitVec X l) l
split-pivot-by _ _ [] = return $ [] , [] by refl
split-pivot-by {A = A} {l = suc l'} f k (x ∷ xs) = if' f x ≤? f k
                                                   then (pivot-append-l x <$> split-pivot-by f k xs)
                                                   else (pivot-append-r x <$> split-pivot-by f k xs)

split-pivot : {l : ℕ} -> A -> Vec A l -> DecTree A (SplitVec A l) l
split-pivot = split-pivot-by id




take-min : {n : ℕ} -> A -> Vec A n -> DecTree A (A × Vec A n) n
take-min x [] = return $ x , []
take-min x (y ∷ ys) = if' x ≤? y
                 then (take-min x ys <&> λ (e , rs) -> e , y ∷ rs)
                 else (take-min y ys <&> λ (e , rs) -> e , x ∷ rs)



find : {l : ℕ} -> Vec A l -> A -> DecTree A (Maybe $ Fin l) (2 * l)
find [] _ = return nothing
find {l = suc l-1} (x ∷ xs) e =
                  height-≡ (sym $ +-suc  (suc l-1) (l-1 + 0)) $
                  if' x ≤? e
                  then if e ≤? x
                       then return (just $ Fin.zero)
                       else (find xs e <&> λ res -> Data.Maybe.map (Fin.suc) res)
                  else (delay' 1 $ find xs e <&> λ res -> Data.Maybe.map (Fin.suc) res)


removeElem : {l : ℕ} -> Vec A l -> A -> DecTree A (Vec A ⟨ l ⟩-1?) (2 * l)
removeElem [] _ = return $ neutral []
removeElem {l = suc l-1} (x ∷ xs) e =
                  height-≡ (sym $ +-suc (suc l-1) (l-1 + 0)) $
                  if' x ≤? e
                  then if e ≤? x
                       then return $ decrement xs
                       else (x ∷'_ <$> removeElem xs e)
                  else (delay' 1 $ x ∷'_ <$> removeElem xs e)
    where
        _∷'_ : {l : ℕ} ->  A -> Vec A ⟨ l ⟩-1? -> Vec A ⟨ suc l ⟩-1?
        x ∷' (neutral xs) = neutral $ x ∷ xs
        x ∷' (decrement xs) = decrement $ x ∷ xs
