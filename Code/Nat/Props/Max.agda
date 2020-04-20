module Nat.Props.Max where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Function

open import Nat.Props.Plus

comm-⊔≤+ : ∀ m n -> suc (m + m) ⊔ (n + n) ≤ m + n + suc (m + n)
comm-⊔≤+ m n = begin
        suc (m + m) ⊔ (n + n)                  ≤⟨ m⊔n≤m+n (suc $ m + m) (n + n) ⟩
        suc (m + m) + (n + n)                  ≡⟨⟩
        suc (m + m + (n + n))                  ≡⟨ sym $ cong suc $ +-double-comm m n ⟩
        suc (m + n + (m + n))                  ≡⟨ sym $ +-suc _ _ ⟩
        m + n + suc (m + n)                    ∎
    where
       open ≤-Reasoning

⊔-+-switch : ∀ m n -> 1 + (m + m) ⊔ (n + n) ≤ m ⊔ n + suc (m ⊔ n)
⊔-+-switch m n = begin
        1 + (m + m) ⊔ (n + n)                  ≤⟨ ⊔-monoʳ-≤ (suc $ m + m) (≤-step $ +-mono-≤ (n≤m⊔n m n) (n≤m⊔n m n)) ⟩
        1 + (m + m) ⊔ (1 + (m ⊔ n + (m ⊔ n)))  ≤⟨ ⊔-monoˡ-≤ (suc $ m ⊔ n + (m ⊔ n)) (s≤s $ +-mono-≤ (m≤m⊔n m n) (m≤m⊔n m n)) ⟩
        1 + (m ⊔ n + (m ⊔ n)) ⊔ (1 + (m ⊔ n + (m ⊔ n))) ≡⟨ ⊔-idem _ ⟩
        (suc $ (m ⊔ n) + (m ⊔ n))              ≡⟨ sym $ +-suc _ _ ⟩
        m ⊔ n + suc (m ⊔ n)                    ∎
    where
        open ≤-Reasoning

⊔-idem-under-≡ : {x y : ℕ} -> (x ≡ y) -> x ⊔ y ≡ x
⊔-idem-under-≡ {x} {y} equ = trans (cong (x ⊔_) (sym equ)) (⊔-idem x)

⊔-idem-suc-xy : {x y : ℕ} -> (x + (1 + y)) ⊔ (1 + (x + y)) ≡ (x + (1 + y))
⊔-idem-suc-xy {x} {y} = ⊔-idem-under-≡ (+-suc x y)

⊔-max-< : ∀ {m n} -> m < n -> m ⊔ n ≡ suc m ⊔ n
⊔-max-< pf = trans (m≤n⇒m⊔n≡n $ ≤⇒pred≤ pf) (sym $ m≤n⇒m⊔n≡n pf)

⊔-max-<ᵣ : ∀ {m n} -> n < m -> m ⊔ n ≡ m ⊔ suc n
⊔-max-<ᵣ pf = trans (m≤n⇒n⊔m≡n $ ≤⇒pred≤ pf) (sym $ m≤n⇒n⊔m≡n pf)

⊔-max-≡ : ∀ {m n} -> suc m ≡ n -> m ⊔ n ≡ suc m ⊔ n
⊔-max-≡ pf = ⊔-max-< $ ≤-reflexive pf

⊔-max-≡ᵣ : ∀ {m n} -> m ≡ suc n -> m ⊔ n ≡ m ⊔ suc n
⊔-max-≡ᵣ pf = ⊔-max-<ᵣ (≤-reflexive $ sym pf)

⊔-max-> : ∀ {m n} -> n ≤ m -> suc (m ⊔ n) ≡ suc m ⊔ n
⊔-max-> pf = trans (cong suc $ m≤n⇒n⊔m≡n $ pf) (sym $ m≤n⇒n⊔m≡n $ ≤-step pf)

⊔-max->ᵣ : ∀ {m n} -> m ≤ n -> suc (m ⊔ n) ≡ m ⊔ suc n
⊔-max->ᵣ pf = trans (cong suc $ m≤n⇒m⊔n≡n pf) (sym $ m≤n⇒m⊔n≡n $ ≤-step pf)
