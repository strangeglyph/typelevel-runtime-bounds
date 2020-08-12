module Nat.Props.Mul where

open import Nat.Mul

open import Data.Nat as ℕ renaming (_*_ to _ℕ*_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Function
open import Level renaming (suc to lsuc)

private
    variable
        a : Level

*≡* : ∀ x y -> x ℕ* y ≡ x * y
*≡* zero y = refl
*≡* (suc zero) y = +-identityʳ y
*≡* (suc (suc x)) y = cong (y +_) $ *≡* (suc x) y

lift-* : ∀ {x y} -> (P : ℕ -> Set a) -> P (x ℕ* y) -> P (x * y)
lift-* {x = x} {y = y} P pf = subst P (*≡* x y) pf
