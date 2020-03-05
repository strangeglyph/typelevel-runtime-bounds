module NatProp where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Induction.WellFounded
open import Function
open ≡-Reasoning

⊔-idem-under-≡ : {x y : ℕ} -> (x ≡ y) -> x ⊔ y ≡ x
⊔-idem-under-≡ {x} {y} equ = trans (cong (x ⊔_) (sym equ)) (⊔-idem x)

⊔-idem-suc-xy : {x y : ℕ} -> (x + (1 + y)) ⊔ (1 + (x + y)) ≡ (x + (1 + y))
⊔-idem-suc-xy {x} {y} = ⊔-idem-under-≡ (+-suc x y)

⌈n/2⌉+⌊n/2⌋≡n : ∀ n -> ⌈ n /2⌉ + ⌊ n /2⌋ ≡ n
⌈n/2⌉+⌊n/2⌋≡n zero = refl
⌈n/2⌉+⌊n/2⌋≡n (suc n) = begin
        ⌈ suc n /2⌉ + ⌊ suc n /2⌋      ≡⟨⟩
        suc (⌊ n /2⌋ + ⌊ suc n /2⌋)    ≡⟨ cong suc (+-comm ⌊ n /2⌋ ⌊ suc n /2⌋) ⟩
        suc (⌊ suc n /2⌋ + ⌊ n /2⌋)    ≡⟨⟩
        suc (⌈ n /2⌉ + ⌊ n /2⌋)        ≡⟨ cong suc (⌈n/2⌉+⌊n/2⌋≡n n) ⟩
        suc n                          ∎

⌊n/2⌋+⌈n/2⌉≡n : ∀ n -> ⌊ n /2⌋ + ⌈ n /2⌉ ≡ n
⌊n/2⌋+⌈n/2⌉≡n n = trans (+-comm ⌊ n /2⌋ ⌈ n /2⌉) $ ⌈n/2⌉+⌊n/2⌋≡n n

n>0⇒⌊n/2⌋<n : ∀ n-1 -> let n = 1 + n-1 in ⌊ n /2⌋ < n
n>0⇒⌊n/2⌋<n zero = s≤s z≤n
n>0⇒⌊n/2⌋<n (suc zero) = s≤s (s≤s z≤n)
n>0⇒⌊n/2⌋<n (suc (suc k)) = ≤-step $ s≤s $ n>0⇒⌊n/2⌋<n k

n>1⇒⌈n/2⌉<n : ∀ n-2 -> let n = 2 + n-2 in ⌈ n /2⌉ < n
n>1⇒⌈n/2⌉<n k = s≤s $ n>0⇒⌊n/2⌋<n $ k

+-double-comm : (a b : ℕ) -> (a + b) + (a + b) ≡ (a + a) + (b + b)
+-double-comm a b = begin
    a +     b    + (a + b)  ≡⟨ +-assoc a b (a + b) ⟩
    a + (   b    + (a + b)) ≡⟨ cong (a +_) (+-comm b (a + b)) ⟩
    a + ((a + b) +    b   ) ≡⟨ cong (a +_) (+-assoc a b b) ⟩
    a + (   a    + (b + b)) ≡⟨ sym (+-assoc a a (b + b)) ⟩
    a +     a    + (b + b)  ∎

binom-identity : (a b : ℕ) -> (a + b) * (a + b) ≡ (a * a) + (b * b) + (2 * a * b)
binom-identity zero b = sym (+-identityʳ (b * b))
binom-identity (suc a) b = cong suc (begin
    a + b            +    (a + b) * (1 + a + b)      ≡⟨ cong (a + b +_) (*-suc (a + b) (a + b)) ⟩
    a + b + ((a + b) +    ((a + b) * (a + b)))       ≡⟨ sym (+-assoc (a + b) (a + b) ((a + b) * (a + b))) ⟩
    a + b + (a + b)  +    (a + b) * (a + b)          ≡⟨ cong (_+ ((a + b) * (a + b))) (+-double-comm a b) ⟩
    a + a + (b + b)  +    (a + b) * (a + b)          ≡⟨ cong ((a + a) + (b + b) +_) (binom-identity a b) ⟩
    a + a + (b + b)  + (a * a + b * b + 2 * a * b)   ≡⟨ cong ((a + a) + (b + b) +_) (+-assoc (a * a) (b * b) (2 * a * b)) ⟩
    a + a + (b + b)  + (a * a + (b * b + 2 * a * b)) ≡⟨ sym (+-assoc (a + a + (b + b)) (a * a) (b * b + 2 * a * b)) ⟩
    a + a + (b + b)  + (a * a) + (b * b + 2 * a * b) ≡⟨ cong (_+ (b * b + 2 * a * b)) (+-assoc (a + a) (b + b) (a * a)) ⟩
    a + a + ((b + b) + a * a) + (b * b + 2 * a * b)  ≡⟨ cong (_+ (b * b + 2 * a * b)) (cong (a + a +_) (+-comm (b + b) (a * a))) ⟩
    a + a + (a * a + (b + b)) + (b * b + 2 * a * b)  ≡⟨ cong (_+ (b * b + 2 * a * b)) (sym (+-assoc (a + a) (a * a) (b + b))) ⟩
    a + a + a * a + (b + b) + (b * b + 2 * a * b)    ≡⟨ cong (_+ (b * b + 2 * a * b)) (cong (_+ (b + b)) (+-assoc a a (a * a))) ⟩
    a + (a + a * a) + (b + b) + (b * b + 2 * a * b)  ≡⟨ cong (_+ (b * b + 2 * a * b)) (cong (_+ (b + b)) (cong (a +_) (sym (*-suc a a)))) ⟩
    a + a * suc a + (b + b) + (b * b + 2 * a * b)    ≡⟨ +-assoc (a + a * suc a) (b + b) (b * b + 2 * a * b) ⟩
    a + a * suc a + (b + b + (b * b + 2 * a * b))    ≡⟨ cong (a + a * suc a +_) (sym (+-assoc (b + b) (b * b) (2 * a * b))) ⟩
    a + a * suc a + ((b + b + b * b) + 2 * a * b)    ≡⟨ cong (a + a * suc a +_) (cong (_+ (2 * a * b)) (+-comm (b + b) (b * b))) ⟩
    a + a * suc a + (b * b + (b + b) + 2 * a * b)    ≡⟨ cong (a + a * suc a +_) (+-assoc (b * b) (b + b) (2 * a * b)) ⟩
    a + a * suc a + (b * b + ((b + b) + 2 * a * b))  ≡⟨ sym (+-assoc (a + a * suc a) (b * b) (b + b + 2 * a * b)) ⟩
    a + a * suc a + b * b + (b + b + 2 * a * b)      ≡⟨ cong (a + a * suc a + b * b +_) (+-assoc b b (2 * a * b)) ⟩
    a + a * suc a + b * b + (b + (b + 2 * a * b))    ≡⟨ cong (a + a * suc a + b * b +_) (cong (b +_) (cong (_* b) (sym (+-suc a (a + 0))))) ⟩
    a + a * suc a + b * b + (2 * (1 + a) * b)        ∎)


m≤m+n≡k : {m n k : ℕ} -> m + n ≡ k -> m ≤ k
m≤m+n≡k {m} {n} {k} pf = subst (m ≤_) pf (m≤m+n m n)

n≤m+n≡k : {m n k : ℕ} -> m + n ≡ k -> n ≤ k
n≤m+n≡k {m} {n} {k} pf = subst (n ≤_) pf (m≤n+m n m)
