module Nat.Props.Div.Const where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Function

open import Nat.Base

⌈n/2⌉+⌊n/2⌋≡n : ∀ n -> ⌈ n /2⌉ + ⌊ n /2⌋ ≡ n
⌈n/2⌉+⌊n/2⌋≡n zero = refl
⌈n/2⌉+⌊n/2⌋≡n (suc n) = begin
        ⌈ suc n /2⌉ + ⌊ suc n /2⌋      ≡⟨⟩
        suc (⌊ n /2⌋ + ⌊ suc n /2⌋)    ≡⟨ cong suc (+-comm ⌊ n /2⌋ ⌊ suc n /2⌋) ⟩
        suc (⌊ suc n /2⌋ + ⌊ n /2⌋)    ≡⟨⟩
        suc (⌈ n /2⌉ + ⌊ n /2⌋)        ≡⟨ cong suc (⌈n/2⌉+⌊n/2⌋≡n n) ⟩
        suc n                          ∎
    where
        open ≡-Reasoning


⌊n/2⌋+⌈n/2⌉≡n : ∀ n -> ⌊ n /2⌋ + ⌈ n /2⌉ ≡ n
⌊n/2⌋+⌈n/2⌉≡n n = trans (+-comm ⌊ n /2⌋ ⌈ n /2⌉) $ ⌈n/2⌉+⌊n/2⌋≡n n

n>0⇒⌊n/2⌋<n : ∀ n-1 -> let n = 1 + n-1 in ⌊ n /2⌋ < n
n>0⇒⌊n/2⌋<n zero = s≤s z≤n
n>0⇒⌊n/2⌋<n (suc zero) = s≤s (s≤s z≤n)
n>0⇒⌊n/2⌋<n (suc (suc k)) = ≤-step $ s≤s $ n>0⇒⌊n/2⌋<n k

n>1⇒⌈n/2⌉<n : ∀ n-2 -> let n = 2 + n-2 in ⌈ n /2⌉ < n
n>1⇒⌈n/2⌉<n k = s≤s $ n>0⇒⌊n/2⌋<n $ k

⌈1+n/5⌉>0 : ∀ n -> Σ ℕ (λ m -> ⌈ (suc n) /5⌉ ≡ suc m)
⌈1+n/5⌉>0 zero = 0 , refl
⌈1+n/5⌉>0 (suc zero) = 0 , refl
⌈1+n/5⌉>0 (suc (suc zero)) = 0 , refl
⌈1+n/5⌉>0 (suc (suc (suc zero))) = 0 , refl
⌈1+n/5⌉>0 (suc (suc (suc (suc zero)))) = 0 , refl
⌈1+n/5⌉>0 (suc (suc (suc (suc (suc n))))) = let m , pf = ⌈1+n/5⌉>0 n in suc m , cong suc pf


⌊n5/5⌋≡n : ∀ n -> ⌊ n * 5 /5⌋ ≡ n
⌊n5/5⌋≡n zero = refl
⌊n5/5⌋≡n (suc n) = cong suc $ ⌊n5/5⌋≡n n

⌊5n/n⌋≡n : ∀ n -> ⌊ 5 * n /5⌋ ≡ n
⌊5n/n⌋≡n n = trans (cong ⌊_/5⌋ $ *-comm 5 n) (⌊n5/5⌋≡n n)



n-⌊n/2⌋≡⌈n/2⌉ : ∀ n -> n ∸ ⌊ n /2⌋ ≡ ⌈ n /2⌉
n-⌊n/2⌋≡⌈n/2⌉ n = begin
        n ∸ ⌊ n /2⌋                  ≡⟨ cong (_∸ ⌊ n /2⌋) $ sym $ ⌊n/2⌋+⌈n/2⌉≡n n ⟩
        ⌊ n /2⌋ + ⌈ n /2⌉ ∸ ⌊ n /2⌋  ≡⟨ m+n∸m≡n ⌊ n /2⌋ _ ⟩
        ⌈ n /2⌉                      ∎
    where
        open ≡-Reasoning

n>0⇒n-suc⌊n/2⌋≡⌊n-1/2⌋ : ∀ n-1 -> let n = suc n-1 in n ∸ suc ⌊ n /2⌋ ≡ ⌊ n-1 /2⌋
n>0⇒n-suc⌊n/2⌋≡⌊n-1/2⌋ n-1 = let n = suc n-1 in begin
        n ∸ suc ⌊ n /2⌋                          ≡⟨ cong (_∸ suc ⌊ n /2⌋) $ sym $ ⌊n/2⌋+⌈n/2⌉≡n n ⟩
        ⌊ n /2⌋ + ⌈ n /2⌉ ∸ suc ⌊ n /2⌋          ≡⟨⟩
        ⌊ n /2⌋ + suc ⌊ n-1 /2⌋ ∸ suc ⌊ n /2⌋    ≡⟨ cong (_∸ suc ⌊ n /2⌋) $ +-suc ⌊ n /2⌋ ⌊ n-1 /2⌋ ⟩
        suc (⌊ n /2⌋ + ⌊ n-1 /2⌋) ∸ suc ⌊ n /2⌋  ≡⟨⟩
        ⌊ n /2⌋ + ⌊ n-1 /2⌋ ∸ ⌊ n /2⌋            ≡⟨ m+n∸m≡n ⌊ n /2⌋ _ ⟩
        ⌊ n-1 /2⌋       ∎
    where
        open ≡-Reasoning


a⌊n/2⌋+a⌈n/2⌉≡a*n : ∀ a n -> a * ⌊ n /2⌋ + a * ⌈ n /2⌉ ≡ a * n
a⌊n/2⌋+a⌈n/2⌉≡a*n a n = begin
        a * ⌊ n /2⌋ + a * ⌈ n /2⌉   ≡⟨ sym $ *-distribˡ-+ a ⌊ n /2⌋ ⌈ n /2⌉ ⟩
        a * (⌊ n /2⌋ + ⌈ n /2⌉)     ≡⟨ cong (a *_) $ ⌊n/2⌋+⌈n/2⌉≡n n ⟩
        a * n                       ∎
    where
        open ≡-Reasoning


5⌊n/5⌋≤n : ∀ n -> 5 * ⌊ n /5⌋ ≤ n
5⌊n/5⌋≤n zero = z≤n
5⌊n/5⌋≤n (suc zero) = z≤n
5⌊n/5⌋≤n (suc (suc zero)) = z≤n
5⌊n/5⌋≤n (suc (suc (suc zero))) = z≤n
5⌊n/5⌋≤n (suc (suc (suc (suc zero)))) = z≤n
5⌊n/5⌋≤n (suc (suc (suc (suc (suc n-5))))) = let n = 5 + n-5 in begin
        5 * ⌊ n /5⌋          ≡⟨⟩
        5 * suc ⌊ n-5 /5⌋    ≡⟨ *-suc 5 ⌊ n-5 /5⌋ ⟩
        5 + 5 * ⌊ n-5 /5⌋    ≤⟨ +-monoʳ-≤ 5 $ 5⌊n/5⌋≤n n-5 ⟩
        5 + n-5              ≡⟨⟩
        n                    ∎
    where
        open ≤-Reasoning

a*5*⌊n/5⌋≤a*n : ∀ a n -> a * 5 * ⌊ n /5⌋ ≤ a * n
a*5*⌊n/5⌋≤a*n a n = begin
        a * 5 * ⌊ n /5⌋       ≡⟨ *-assoc a 5 ⌊ n /5⌋ ⟩
        a * (5 * ⌊ n /5⌋)     ≤⟨ *-monoʳ-≤ a $ 5⌊n/5⌋≤n n ⟩
        a * n                 ∎
    where
        open ≤-Reasoning

⌊l/5⌋<l : ∀ l-1 -> ⌊ suc l-1 /5⌋ < suc l-1
⌊l/5⌋<l zero = s≤s z≤n
⌊l/5⌋<l (suc zero) = s≤s z≤n
⌊l/5⌋<l (suc (suc zero)) = s≤s z≤n
⌊l/5⌋<l (suc (suc (suc zero))) = s≤s z≤n
⌊l/5⌋<l (suc (suc (suc (suc zero)))) = s≤s (s≤s z≤n)
⌊l/5⌋<l (suc (suc (suc (suc (suc l-6))))) = ≤-step $ ≤-step $ ≤-step $ ≤-step $ s≤s (⌊l/5⌋<l l-6)
