module Nat.Log where

open import Data.Nat
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Function using (_$_ ; _∘_)
open import Induction.WellFounded using (Acc)

open import Nat.Props

-- Implementation taken from https://gist.github.com/gallais/5643718

private
    data logAcc : ℕ -> Set where
        log0 : logAcc 0
        logs : ∀ n -> logAcc ⌊ suc n /2⌋ -> logAcc (suc n)

    logAccUnique : ∀ {n} (p q : logAcc n) -> p ≡ q
    logAccUnique log0 log0              = refl
    logAccUnique (logs n p) (logs .n q) = cong (logs n) (logAccUnique p q)


    logAccTotal : ∀ n -> logAcc n
    logAccTotal = <′-rec logAcc logRec
        where
            logRec : ∀ n -> <′-Rec logAcc n -> logAcc n
            logRec zero rec    = log0
            logRec (suc n) rec = logs n (rec _ (s≤′s $ ⌈n/2⌉≤′n n))

    logPartial : ∀ {n} -> logAcc n -> ℕ
    logPartial log0 = 0
    logPartial (logs n pr) = suc (logPartial pr)

1+⌊log₂_⌋ : ℕ -> ℕ
1+⌊log₂_⌋ = logPartial ∘ logAccTotal

⌈log₂_⌉ : ℕ -> ℕ
⌈log₂ n ⌉ = 1+⌊log₂ pred n ⌋



⌈log₂⌉-suc : ∀ n-2 -> let n = 2 + n-2 in ⌈log₂ n ⌉ ≡ suc ⌈log₂ ⌈ n /2⌉ ⌉
⌈log₂⌉-suc n-2 = cong (suc ∘ logPartial) $ logAccUnique _ _

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


-- {! subst (_≤ suc ⌈log₂ ⌈ n /2⌉ ⌉) (⌈log₂ ) s≤s $  ⌈log₂⌉-mono (⌈n/2⌉-mono pf)!}


merge-time : ℕ -> ℕ
merge-time n = ⌈ n /2⌉ * ⌈log₂ ⌈ n /2⌉ ⌉ + (⌊ n /2⌋ * ⌈log₂ ⌊ n /2⌋ ⌉ + (⌈ n /2⌉ + ⌊ n /2⌋))

log₂n/2-bound : ∀ n-2 -> let n = 2 + n-2 in merge-time n ≤ n * ⌈log₂ n ⌉
log₂n/2-bound n-2 = let n = 2 + n-2 in begin
        merge-time n
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
    where
        open ≤-Reasoning
