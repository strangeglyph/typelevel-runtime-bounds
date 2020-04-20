module Nat.Props.Plus where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Function

+-double-comm' : ∀ a b c d -> (a + b) + (c + d) ≡ (a + c) + (b + d)
+-double-comm' a b c d = begin
        a +     b    + (c + d)  ≡⟨ +-assoc a b (c + d) ⟩
        a + (   b    + (c + d)) ≡⟨ cong (a +_) (+-comm b (c + d)) ⟩
        a + ((c + d) +    b   ) ≡⟨ cong (a +_) (+-assoc c d b) ⟩
        a + (   c    + (d + b)) ≡⟨ sym (+-assoc a c (d + b)) ⟩
        a +     c    + (d + b)  ≡⟨ cong ((a + c) +_) $ +-comm d b ⟩
        a +     c    + (b + d)  ∎
    where
        open ≡-Reasoning

+-double-comm : ∀ a b -> (a + b) + (a + b) ≡ (a + a) + (b + b)
+-double-comm a b = +-double-comm' a b a b


+-assoc-commˡ : ∀ a b c -> a + (b + c) ≡ b + (a + c)
+-assoc-commˡ = +-double-comm' 0

a+1+b+c+d≡a+b+1+c+d : ∀ a b c d -> a + suc (b + c + d) ≡ a + b + suc (c + d)
a+1+b+c+d≡a+b+1+c+d a b c d = begin
        a + suc (b + c + d)     ≡⟨ cong (a +_) $ cong suc $ +-assoc b c d ⟩
        a + suc (b + (c + d))   ≡⟨ cong (a +_) $ sym $ +-suc b (c + d) ⟩
        a + (b + suc (c + d))   ≡⟨ sym $ +-assoc a b (suc (c + d)) ⟩
        a + b + suc (c + d)     ∎
    where
        open ≡-Reasoning

m≤m+n≡k : {m n k : ℕ} -> m + n ≡ k -> m ≤ k
m≤m+n≡k {m} {n} {k} pf = subst (m ≤_) pf (m≤m+n m n)

n≤m+n≡k : {m n k : ℕ} -> m + n ≡ k -> n ≤ k
n≤m+n≡k {m} {n} {k} pf = subst (n ≤_) pf (m≤n+m n m)