module Nat.Props.Times where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Function

open import Nat.Props.Plus


2*m≡m+m : ∀ m -> 2 * m ≡ m + m
2*m≡m+m m = cong (m +_) $ +-identityʳ m



binom-identity : (a b : ℕ) -> (a + b) * (a + b) ≡ (a * a) + (b * b) + (2 * a * b)
binom-identity zero b = sym (+-identityʳ (b * b))
binom-identity (suc a) b = cong suc (begin
    a + b            +    (a + b) * (1 + a + b)      ≡⟨ cong (a + b +_) (*-suc (a + b) (a + b)) ⟩
    a + b + ((a + b) +    ((a + b) * (a + b)))       ≡⟨ sym (+-assoc (a + b) (a + b) ((a + b) * (a + b))) ⟩
    a + b + (a + b)  +    (a + b) * (a + b)          ≡⟨ cong (_+ ((a + b) * (a + b))) (+-double-comm a b) ⟩
    a + a + (b + b)  +    (a + b) * (a + b)          ≡⟨ cong ((a + a) + (b + b) +_) (binom-identity a b) ⟩
    a + a + (b + b)  + (a * a + b * b + 2 * a * b)   ≡⟨ cong ((a + a) + (b + b) +_) (+-assoc (a * a) (b * b) (2 * a * b)) ⟩
    a + a + (b + b)  + (a * a + (b * b + 2 * a * b)) ≡⟨ sym (+-assoc (a + a + (b + b)) (a * a) (b * b + 2 * a * b)) ⟩
    a + a + (b + b)  + (a * a) + (b * b + 2 * a * b) ≡⟨ cong (_+ (b * b + 2 * a * b)) (+-assoc (a + a) (b + b) (a * a)) ⟩
    a + a + ((b + b) + a * a) + (b * b + 2 * a * b)  ≡⟨ cong (_+ (b * b + 2 * a * b)) (cong (a + a +_) (+-comm (b + b) (a * a))) ⟩
    a + a + (a * a + (b + b)) + (b * b + 2 * a * b)  ≡⟨ cong (_+ (b * b + 2 * a * b)) (sym (+-assoc (a + a) (a * a) (b + b))) ⟩
    a + a + a * a + (b + b) + (b * b + 2 * a * b)    ≡⟨ cong (_+ (b * b + 2 * a * b)) (cong (_+ (b + b)) (+-assoc a a (a * a))) ⟩
    a + (a + a * a) + (b + b) + (b * b + 2 * a * b)  ≡⟨ cong (_+ (b * b + 2 * a * b)) (cong (_+ (b + b)) (cong (a +_) (sym (*-suc a a)))) ⟩
    a + a * suc a + (b + b) + (b * b + 2 * a * b)    ≡⟨ +-assoc (a + a * suc a) (b + b) (b * b + 2 * a * b) ⟩
    a + a * suc a + (b + b + (b * b + 2 * a * b))    ≡⟨ cong (a + a * suc a +_) (sym (+-assoc (b + b) (b * b) (2 * a * b))) ⟩
    a + a * suc a + ((b + b + b * b) + 2 * a * b)    ≡⟨ cong (a + a * suc a +_) (cong (_+ (2 * a * b)) (+-comm (b + b) (b * b))) ⟩
    a + a * suc a + (b * b + (b + b) + 2 * a * b)    ≡⟨ cong (a + a * suc a +_) (+-assoc (b * b) (b + b) (2 * a * b)) ⟩
    a + a * suc a + (b * b + ((b + b) + 2 * a * b))  ≡⟨ sym (+-assoc (a + a * suc a) (b * b) (b + b + 2 * a * b)) ⟩
    a + a * suc a + b * b + (b + b + 2 * a * b)      ≡⟨ cong (a + a * suc a + b * b +_) (+-assoc b b (2 * a * b)) ⟩
    a + a * suc a + b * b + (b + (b + 2 * a * b))    ≡⟨ cong (a + a * suc a + b * b +_) (cong (b +_) (cong (_* b) (sym (+-suc a (a + 0))))) ⟩
    a + a * suc a + b * b + (2 * (1 + a) * b)        ∎)
    where
        open ≡-Reasoning

