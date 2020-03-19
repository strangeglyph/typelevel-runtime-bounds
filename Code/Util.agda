module Util where

open import Level using (Level)
open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality

private
    variable
        a b c : Level
        A : Set a
        B : Set b

len : {n : ℕ} -> Vec A n -> ℕ
len {n = n} _ = n


subst2 : (P : A -> B -> Set c) {a₁ a₂ : A} {b₁ b₂ : B} -> a₁ ≡ a₂ -> b₁ ≡ b₂ -> P a₁ b₁ -> P a₂ b₂
subst2 P refl refl p = p


data _1?+⟨_⟩ (A : ℕ -> Set a) (n : ℕ) : Set a where
    +0 : A n       -> A 1?+⟨ n ⟩
    +1 : A (suc n) -> A 1?+⟨ n ⟩

data _⟨_⟩-1? (A : ℕ -> Set a) : (n : ℕ) -> Set a where
    neutral   : {n : ℕ} -> A n -> A ⟨ n ⟩-1?
    decrement : {n : ℕ} -> A n -> A ⟨ suc n ⟩-1?
