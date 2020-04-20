module Nat.Props.Minus where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Function


a+b≡c⇒b≡c-a : ∀ a b c -> a + b ≡ c -> b ≡ c ∸ a
a+b≡c⇒b≡c-a zero b c a+b≡c = a+b≡c
a+b≡c⇒b≡c-a a@(suc a-1) b c@(suc c-1) a+b≡c = a+b≡c⇒b≡c-a a-1 b c-1 $ suc-injective a+b≡c

a+b+c≡n∧a≡k∧b≡n-k⇒c≡0 : ∀ {a b c n k} -> a + b + c ≡ n -> a ≡ k -> b ≡ n ∸ k -> k ≤ n -> c ≡ 0
a+b+c≡n∧a≡k∧b≡n-k⇒c≡0 {a} {b} {c} {n} {k} a+b+c≡n a≡k b≡n-k k≤n = begin
        c                  ≡⟨ a+b≡c⇒b≡c-a (a + b) c n a+b+c≡n ⟩
        n ∸ (a + b)        ≡⟨ cong (λ x → n ∸ (x + b)) a≡k ⟩
        n ∸ (k + b)        ≡⟨ cong (λ x → n ∸ (k + x)) b≡n-k ⟩
        n ∸ (k + (n ∸ k))  ≡⟨ cong (n ∸_) $ +-comm k (n ∸ k) ⟩
        n ∸ (n ∸ k + k)    ≡⟨ cong (n ∸_) $ m∸n+n≡m k≤n ⟩
        n ∸ n              ≡⟨ n∸n≡0 n ⟩
        0                  ∎
    where
        open ≡-Reasoning

a∸[b∸c]≡a+c∸b : ∀ a {b c} -> c ≤ b -> a ∸ (b ∸ c) ≡ a + c ∸ b
a∸[b∸c]≡a+c∸b a {b} {.0} z≤n = cong (_∸ b) $ sym $ +-identityʳ a
a∸[b∸c]≡a+c∸b a {.(suc b)} {.(suc c)} (s≤s {m = c} {n = b} c≤b) = begin
        a ∸ (b ∸ c)        ≡⟨ a∸[b∸c]≡a+c∸b a c≤b ⟩
        a + c ∸ b          ≡⟨⟩
        suc a + c ∸ suc b  ≡⟨ cong (_∸ suc b) $ sym $ +-suc a c ⟩
        a + suc c ∸ suc b  ∎
    where
        open ≡-Reasoning