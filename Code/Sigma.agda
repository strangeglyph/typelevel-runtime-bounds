module Sigma where

open import Level using (_⊔_; Level)

private
    variable
        a : Level
        b : Level

-- Dep sum with implicit first argument
record Σ (A : Set a) (B : A -> Set b) : Set (a ⊔ b) where
    constructor σ
    field
        {key} : A
        val : B key
