module Fin.Props where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (_+_ ; _≤_ ; _<_)
open import Data.Fin.Properties renaming (suc-injective to fsuc-injective)
open import Relation.Binary.PropositionalEquality
open import Function

open import Fin.Base
open import Nat.Props
open import Util

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

toℕ-subst : ∀ {x y} -> (eq : x ≡ y) -> (i : Fin x) -> toℕ (subst Fin eq i) ≡ toℕ i
toℕ-subst refl i = refl

+-ℕ-ℕ-assoc : ∀ a b -> (i : Fin $ suc b) -> a + (b ℕ-ℕ i) ≡ a + b ℕ-ℕ (inject≤ i $ s≤s $ m≤n+m b a)
+-ℕ-ℕ-assoc a b i = begin
        a + (b ℕ-ℕ i)                              ≡⟨ cong (a +_) $ nℕ-ℕi≡n∸i b i ⟩
        a + (b ∸ toℕ i)                            ≡⟨ sym $ +-∸-assoc a $ ≤-pred $ toℕ<n i ⟩
        a + b ∸ toℕ i                              ≡⟨ sym $ cong (a + b ∸_) $ toℕ-inject≤ i $ s≤s $ m≤n+m b a  ⟩
        a + b ∸ toℕ (inject≤ i $ s≤s $ m≤n+m b a)  ≡⟨ sym $ nℕ-ℕi≡n∸i (a + b) (inject≤ i $ s≤s $ m≤n+m b a) ⟩
        a + b ℕ-ℕ (inject≤ i $ s≤s $ m≤n+m b a)    ∎
    where
        open ≡-Reasoning

ℕ-ℕ-+-assoc : ∀ a b -> (i : Fin $ suc a) -> a ℕ-ℕ i + b ≡ a + b ℕ-ℕ (inject+ b i)
ℕ-ℕ-+-assoc a b i = begin
        a ℕ-ℕ i + b                ≡⟨ cong (_+ b) $ nℕ-ℕi≡n∸i a i ⟩
        a ∸ toℕ i + b              ≡⟨ sym $ +-∸-comm b $ toℕ<n i ⟩
        a + b ∸ toℕ i              ≡⟨ cong (a + b ∸_) $ toℕ-inject+ b i ⟩
        a + b ∸ toℕ (inject+ b i)  ≡⟨ sym $ nℕ-ℕi≡n∸i (a + b) (inject+ b i) ⟩
        a + b ℕ-ℕ (inject+ b i)    ∎
    where
        open ≡-Reasoning

toℕ-fromℕ≤' : ∀ {n k} -> (i : Fin n) -> (eq : k ≤ toℕ i) -> toℕ (fromℕ≤' i eq) ≡ k
toℕ-fromℕ≤' {_} {zero} _ _ = refl
toℕ-fromℕ≤' {_} {suc k} (suc i) (s≤s k≤i) = cong suc $ toℕ-fromℕ≤' i k≤i

toℕ[a-b] : ∀ {n} -> (a : Fin n) -> (b : Fin′ $ suc a) -> toℕ (a - b) ≡ toℕ a ∸ toℕ b
toℕ[a-b] zero zero = refl
toℕ[a-b] (suc a) zero = refl
toℕ[a-b] (suc a) (suc b) = toℕ[a-b] a b

Fin′≤Fin : ∀ {n} -> (i : Fin n) -> (j : Fin′ $ suc i) -> toℕ j ≤ toℕ i
Fin′≤Fin zero zero = z≤n
Fin′≤Fin (suc i) zero = z≤n
Fin′≤Fin (suc i) (suc j) = s≤s $ Fin′≤Fin i j


fin-identity : {n : ℕ} -> (i : Fin (suc n)) -> n ≡ toℕ i + (n ∸ toℕ i)
fin-identity i = sym $ suc-injective $ m+[n∸m]≡n $ toℕ<n i

inject₁-bound : {n : ℕ} -> (i : Fin n) -> toℕ (inject₁ i) < n
inject₁-bound zero = s≤s z≤n
inject₁-bound (suc i) = s≤s (inject₁-bound i)

ℕ-ℕinject₁-ℕ-ℕraise : {n : ℕ} -> (i : Fin n) -> n ℕ-ℕ (inject₁ i) ≡ suc (n ℕ-ℕ (raise 1 i))
ℕ-ℕinject₁-ℕ-ℕraise zero = refl
ℕ-ℕinject₁-ℕ-ℕraise {n} i@(suc i-1) = begin
        n ℕ-ℕ inject₁ i            ≡⟨ nℕ-ℕi≡n∸i n (inject₁ i) ⟩
        n ∸ toℕ (inject₁ i)        ≡⟨ cong (n ∸_) $ toℕ-inject₁ i ⟩
        n ∸ toℕ i                  ≡⟨⟩
        suc n ∸ suc (toℕ i)        ≡⟨ +-∸-assoc 1 $ toℕ<n i ⟩
        suc (n ∸ suc (toℕ i))      ≡⟨ cong suc $ cong (n ∸_) $ sym $ raise[x]i≡x+i 1 i  ⟩
        suc (n ∸ toℕ (raise 1 i))  ≡⟨ cong suc $ sym $ nℕ-ℕi≡n∸i n (raise 1 i) ⟩
        suc (n ℕ-ℕ raise 1 i)      ∎
    where
        open ≡-Reasoning
