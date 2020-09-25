module Nat.Props.Min where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Function

⊓-min-≤ : ∀ {m n} -> m ≤ n -> m ⊓ suc n ≡ m ⊓ n
⊓-min-≤ m≤n = trans (m≤n⇒m⊓n≡m $ ≤-step m≤n) (sym $ m≤n⇒m⊓n≡m m≤n)

⊓-min-≤ᵣ : ∀ {m n} -> n ≤ m -> suc m ⊓ n ≡ m ⊓ n
⊓-min-≤ᵣ n≤m = trans (m≤n⇒n⊓m≡m $ ≤-step n≤m) (sym $ m≤n⇒n⊓m≡m n≤m)
