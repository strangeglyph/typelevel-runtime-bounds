module Nat.Props.Log where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Induction using (<-wellFounded)
open import Relation.Binary.PropositionalEquality
open import Function
open import Induction.WellFounded using (Acc)

open import Nat.Log
open import Nat.Props.Div

⌈log₂⌉-suc : ∀ n-2 -> let n = 2 + n-2 in ⌈log₂ n ⌉ ≡ suc ⌈log₂ ⌈ n /2⌉ ⌉
⌈log₂⌉-suc n-2 = cong (suc ∘ logPartial) $ logAccUnique _ _

1+⌊log₂⌋-suc : ∀ n-1 -> let n = suc n-1 in 1+⌊log₂ n ⌋ ≡ suc 1+⌊log₂ ⌊ n /2⌋ ⌋
1+⌊log₂⌋-suc n-1 = cong (suc ∘ logPartial) $ logAccUnique _ _

⌈log₂⌉-mono : ∀ {m n} -> m ≤ n -> ⌈log₂ m ⌉ ≤ ⌈log₂ n ⌉
⌈log₂⌉-mono {m} pf = ⌈log₂⌉-mono-step pf $ <-wellFounded m
    where
        ⌈log₂⌉-mono-step : ∀ {m n} -> m ≤ n -> Acc _<_ m -> ⌈log₂ m ⌉ ≤ ⌈log₂ n ⌉
        ⌈log₂⌉-mono-step z≤n _ = z≤n
        ⌈log₂⌉-mono-step (s≤s z≤n) _ = z≤n
        ⌈log₂⌉-mono-step {m} {n} pf@(s≤s (s≤s _)) (Acc.acc more) = begin
                ⌈log₂ m ⌉             ≡⟨ ⌈log₂⌉-suc _ ⟩
                suc ⌈log₂ ⌈ m /2⌉ ⌉   ≤⟨ s≤s $ ⌈log₂⌉-mono-step (⌈n/2⌉-mono pf) $ more ⌈ m /2⌉ (n>1⇒⌈n/2⌉<n _) ⟩
                suc ⌈log₂ ⌈ n /2⌉ ⌉   ≡⟨ sym $ ⌈log₂⌉-suc _ ⟩
                ⌈log₂ n ⌉ ∎
            where
                open ≤-Reasoning

1+⌊log₂⌋-mono : ∀ {m n} -> m ≤ n -> 1+⌊log₂ m ⌋ ≤ 1+⌊log₂ n ⌋
1+⌊log₂⌋-mono {m} pf = 1+⌊log₂⌋-mono-step pf $ <-wellFounded m
    where
        1+⌊log₂⌋-mono-step : ∀ {m n} -> m ≤ n -> Acc _<_ m -> 1+⌊log₂ m ⌋ ≤ 1+⌊log₂ n ⌋
        1+⌊log₂⌋-mono-step z≤n _ = z≤n
        1+⌊log₂⌋-mono-step {m} {n} pf@(s≤s _) (Acc.acc more) = begin
                1+⌊log₂ m ⌋            ≡⟨ 1+⌊log₂⌋-suc _ ⟩
                suc 1+⌊log₂ ⌊ m /2⌋ ⌋  ≤⟨ s≤s $ 1+⌊log₂⌋-mono-step (⌊n/2⌋-mono pf) $ more ⌊ m /2⌋ (n>0⇒⌊n/2⌋<n _) ⟩
                suc 1+⌊log₂ ⌊ n /2⌋ ⌋  ≡⟨ sym $ 1+⌊log₂⌋-suc _ ⟩
                1+⌊log₂ n ⌋            ∎
            where
                open ≤-Reasoning

1+⌊log₂⌋≥1 : ∀ m -> 1+⌊log₂ suc m ⌋ ≥ 1
1+⌊log₂⌋≥1 m = s≤s z≤n


merge-time : ℕ -> ℕ
merge-time n = (⌈ n /2⌉ + ⌊ n /2⌋) + ⌊ n /2⌋ * ⌈log₂ ⌊ n /2⌋ ⌉ + ⌈ n /2⌉ * ⌈log₂ ⌈ n /2⌉ ⌉

log₂n/2-bound : ∀ n-2 -> let n = 2 + n-2 in merge-time n ≤ n * ⌈log₂ n ⌉
log₂n/2-bound n-2 = let n = 2 + n-2 in begin
        merge-time n
                                       ≡⟨ cong (λ x → x + ⌊ n /2⌋ * ⌈log₂ ⌊ n /2⌋ ⌉ + ⌈ n /2⌉ * ⌈log₂ ⌈ n /2⌉ ⌉) $ ⌈n/2⌉+⌊n/2⌋≡n n ⟩
        n + ⌊ n /2⌋ * ⌈log₂ ⌊ n /2⌋ ⌉ + ⌈ n /2⌉ * ⌈log₂ ⌈ n /2⌉ ⌉
                                       ≤⟨ +-monoˡ-≤ (⌈ n /2⌉ * ⌈log₂ ⌈ n /2⌉ ⌉) $ +-monoʳ-≤ n $ *-monoʳ-≤ ⌊ n /2⌋ $ ⌈log₂⌉-mono $ ⌊n/2⌋-mono $ n≤1+n n ⟩
        n + ⌊ n /2⌋ * ⌈log₂ ⌈ n /2⌉ ⌉ + ⌈ n /2⌉ * ⌈log₂ ⌈ n /2⌉ ⌉
                                       ≡⟨ +-assoc n (⌊ n /2⌋ * ⌈log₂ ⌈ n /2⌉ ⌉) _ ⟩
        n + (⌊ n /2⌋ * ⌈log₂ ⌈ n /2⌉ ⌉ + ⌈ n /2⌉ * ⌈log₂ ⌈ n /2⌉ ⌉)
                                       ≡⟨ cong (n +_) $ sym $ *-distribʳ-+ ⌈log₂ ⌈ n /2⌉ ⌉ ⌊ n /2⌋ _ ⟩
        n + ((⌊ n /2⌋ + ⌈ n /2⌉) * ⌈log₂ ⌈ n /2⌉ ⌉)
                                       ≡⟨ cong (n +_) $ cong (_* ⌈log₂ ⌈ n /2⌉ ⌉) $ trans (+-comm ⌊ n /2⌋ ⌈ n /2⌉) (⌈n/2⌉+⌊n/2⌋≡n _) ⟩
        n + n * ⌈log₂ ⌈ n /2⌉ ⌉
                                       ≡⟨ sym $ *-suc n _ ⟩
        n * suc ⌈log₂ ⌈ n /2⌉ ⌉
                                       ≡⟨ cong (n *_) $ sym $ ⌈log₂⌉-suc n-2 ⟩
        n * ⌈log₂ n ⌉ ∎



{-
                                  ≡⟨ sym $ +-assoc (⌈ n /2⌉ * ⌈log₂ ⌈ n /2⌉ ⌉) (⌊ n /2⌋ * ⌈log₂ ⌊ n /2⌋ ⌉) (⌈ n /2⌉ + ⌊ n /2⌋) ⟩
        ⌈ n /2⌉ * ⌈log₂ ⌈ n /2⌉ ⌉ + ⌊ n /2⌋ * ⌈log₂ ⌊ n /2⌋ ⌉ + (⌈ n /2⌉ + ⌊ n /2⌋)
                                         ≡⟨ cong (⌈ n /2⌉ * ⌈log₂ ⌈ n /2⌉ ⌉ + ⌊ n /2⌋ * ⌈log₂ ⌊ n /2⌋ ⌉ +_) (⌈n/2⌉+⌊n/2⌋≡n n) ⟩
        ⌈ n /2⌉ * ⌈log₂ ⌈ n /2⌉ ⌉ + ⌊ n /2⌋ * ⌈log₂ ⌊ n /2⌋ ⌉ + n
                                         ≤⟨ +-monoˡ-≤ n (+-monoʳ-≤ (⌈ n /2⌉ * ⌈log₂ ⌈ n /2⌉ ⌉) (*-monoʳ-≤ ⌊ n /2⌋ (⌈log₂⌉-mono (⌊n/2⌋-mono (n≤1+n n))))) ⟩
        ⌈ n /2⌉ * ⌈log₂ ⌈ n /2⌉ ⌉ + ⌊ n /2⌋ * ⌈log₂ ⌈ n /2⌉ ⌉ + n
                                         ≡⟨ cong (_+ n) $ sym $ *-distribʳ-+ ⌈log₂ ⌈ n /2⌉ ⌉ ⌈ n /2⌉ ⌊ n /2⌋ ⟩
        (⌈ n /2⌉ + ⌊ n /2⌋) * ⌈log₂ ⌈ n /2⌉ ⌉ + n
                                         ≡⟨ cong (λ x -> x * ⌈log₂ ⌈ n /2⌉ ⌉ + n) $ ⌈n/2⌉+⌊n/2⌋≡n n ⟩
        n * ⌈log₂ ⌈ n /2⌉ ⌉ + n
                                         ≡⟨ +-comm (n * ⌈log₂ ⌈ n /2⌉ ⌉) n ⟩
        n + n * ⌈log₂ ⌈ n /2⌉ ⌉
                                         ≡⟨ sym $ *-suc n (⌈log₂ ⌈ n /2⌉ ⌉) ⟩
        n * suc ⌈log₂ ⌈ n /2⌉ ⌉
                                         ≡⟨ cong (n *_) $ sym $ ⌈log₂⌉-suc n-2 ⟩
        n * ⌈log₂ n ⌉ ∎
  -}
    where
        open ≤-Reasoning





n≤8000⇒⌈log₂n⌉≤35 : ∀ {n} -> n ≤ 8000 -> ⌈log₂ n ⌉ ≤ 35
n≤8000⇒⌈log₂n⌉≤35 {n} n≤8000 = begin
        ⌈log₂ n ⌉     ≤⟨ ⌈log₂⌉-mono n≤8000 ⟩
        ⌈log₂ 8000 ⌉  ≡⟨⟩
        13            ≤⟨ s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))))) ⟩
        35            ∎
    where
        open ≤-Reasoning


