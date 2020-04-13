module Fin.Props where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (_+_)
open import Data.Fin.Properties
open import Relation.Binary.PropositionalEquality
open import Function

open import Nat.Props

nℕ-ℕi≡n∸i : ∀ n i -> n ℕ-ℕ i ≡ n ∸ toℕ i
nℕ-ℕi≡n∸i n zero = refl
nℕ-ℕi≡n∸i (suc n) (suc i) = nℕ-ℕi≡n∸i n i

raise[x]i≡x+i : ∀ {m} x -> (i : Fin m) -> toℕ (raise x i) ≡ x + toℕ i
raise[x]i≡x+i zero i = refl
raise[x]i≡x+i (suc x) i = cong suc $ raise[x]i≡x+i x i

nℕ-ℕsuc⌊n/2⌋≡⌊n-1/2⌋ : ∀ n-1 -> let n = suc n-1 in n ℕ-ℕ (raise 1 $ fromℕ< $ n>0⇒⌊n/2⌋<n n-1) ≡ ⌊ n-1 /2⌋
nℕ-ℕsuc⌊n/2⌋≡⌊n-1/2⌋ n-1 = let n = suc n-1 in begin
        n ℕ-ℕ (raise 1 $ fromℕ< $ n>0⇒⌊n/2⌋<n n-1)    ≡⟨ nℕ-ℕi≡n∸i n (raise 1 $ fromℕ< $ n>0⇒⌊n/2⌋<n n-1) ⟩
        n ∸ toℕ (raise 1 $ fromℕ< $ n>0⇒⌊n/2⌋<n n-1)  ≡⟨ cong (n ∸_) $ raise[x]i≡x+i 1 (fromℕ< $ n>0⇒⌊n/2⌋<n n-1) ⟩
        n ∸ suc (toℕ $ fromℕ< $ n>0⇒⌊n/2⌋<n n-1)      ≡⟨ cong (n ∸_) $ cong suc $ toℕ-fromℕ< $ n>0⇒⌊n/2⌋<n n-1 ⟩
        n ∸ suc ⌊ n /2⌋                               ≡⟨ n>0⇒n-suc⌊n/2⌋≡⌊n-1/2⌋ n-1 ⟩
        ⌊ n-1 /2⌋                                     ∎
    where
        open ≡-Reasoning

a+b+c≡n∧a≡k∧b≡nℕ-ℕk⇒c≡0 : ∀ {a b c n} -> {k : Fin $ suc n} -> a + b + c ≡ n -> a ≡ toℕ k -> b ≡ n ℕ-ℕ k -> c ≡ 0
a+b+c≡n∧a≡k∧b≡nℕ-ℕk⇒c≡0 {n = n} {k = k} a+b+c≡n a≡k b≡nℕ-ℕk
        = a+b+c≡n∧a≡k∧b≡n-k⇒c≡0 a+b+c≡n a≡k (trans b≡nℕ-ℕk $ nℕ-ℕi≡n∸i n k) (≤-pred $ toℕ<n k)
