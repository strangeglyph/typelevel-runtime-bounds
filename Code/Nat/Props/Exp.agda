module Nat.Props.Exp where

open import Data.Nat as ℕ hiding (_*_ ; _^_)
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Function

open import Nat.Mul
open import Nat.Props.Mul

a^n≥1 : ∀ a-1 n -> (suc a-1) ^ n ≥ 1
a^n≥1 a-1 zero = s≤s z≤n
a^n≥1 a-1 n@(suc n-1) = let a = suc a-1 in begin
        1              ≤⟨ s≤s z≤n ⟩
        a              ≡⟨ sym $ *-identityʳ a ⟩
        a ℕ.* 1        ≤⟨ *-monoʳ-≤ a $ a^n≥1 a-1 n-1 ⟩
        a ℕ.* a ^ n-1  ≡⟨ *≡* a (a ^ n-1) ⟩
        a * a ^ n-1    ≡⟨⟩
        a ^ n          ∎
    where
        open ≤-Reasoning
