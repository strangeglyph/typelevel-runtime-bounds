module Nat.Log where

open import Data.Nat
open import Data.Nat.Induction
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Function using (_$_ ; _∘_)
open import Induction.WellFounded using (Acc)

-- Implementation taken from https://gist.github.com/gallais/5643718


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
