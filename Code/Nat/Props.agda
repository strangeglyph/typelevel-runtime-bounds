module Nat.Props where

open import Agda.Builtin.Nat using () renaming (div-helper to divₕ ; mod-helper to modₕ)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Nat.DivMod.Core
open import Data.Nat.Divisibility
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (False)
open import Function

open import Nat.Base

data Ord : ℕ -> ℕ -> Set where
    lt : {x y : ℕ} -> x < y -> Ord x y
    eq : {x y : ℕ} -> x ≡ y -> Ord x y
    gt : {x y : ℕ} -> y < x -> Ord x y


ord : (x y : ℕ) -> Ord x y
ord zero zero       = eq refl
ord zero (suc n)    = lt (s≤s $ z≤n)
ord (suc n) zero    = gt (s≤s $ z≤n)
ord (suc x) (suc y) with ord x y
...                 | lt pf = lt $ s≤s pf
...                 | eq pf = eq $ cong suc pf
...                 | gt pf = gt $ s≤s pf


record Diff (x y : ℕ) : Set where
    constructor Diff_by_
    field
        k : ℕ
        pf : (x + k) ≡ y

diff : {x y : ℕ} -> x ≤ y -> Diff x y
diff (z≤n {n}) = Diff n by refl
diff (s≤s m≤n) = case (diff m≤n) of λ (Diff n by pf) -> Diff n by cong suc pf


2*m≡m+m : ∀ m -> 2 * m ≡ m + m
2*m≡m+m m = cong (m +_) $ +-identityʳ m

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

n%n+m%n<n : ∀ m n-1 -> let n = suc n-1 in  modₕ 0 n-1 n n-1 + modₕ 0 n-1 m n-1 < n
n%n+m%n<n m n-1 = let n = suc n-1 in s≤s $ begin
        n % n + m % n     ≡⟨ cong (_+ m % n) $ n[modₕ]n≡0 0 n-1 ⟩
        m % n             ≤⟨ a[modₕ]n<n 0 m n-1 ⟩
        n-1               ∎
    where
        open ≤-Reasoning


[n+m]/n≡1+m/n : ∀ m n-1 -> let n = suc n-1 in (n + m) / n ≡ 1 + m / n
[n+m]/n≡1+m/n m n-1 = let n = suc n-1 in begin
        (n + m) / n      ≡⟨ +-distrib-divₕ 0 0 n m n-1 $ n%n+m%n<n m n-1 ⟩
        n / n + m / n    ≡⟨ cong (_+ m / n) $ n/n≡1 n ⟩
        1 + m / n        ∎
    where
        open ≡-Reasoning

-- public reimpl of DivMod.Core.divₕ-extractAcc
divₕ-extractAcc : ∀ acc d n j -> divₕ acc d n j ≡ acc + divₕ 0 d n j
divₕ-extractAcc acc d 0 j = sym (+-identityʳ acc)
divₕ-extractAcc acc d (suc n) (suc j) = divₕ-extractAcc acc d n j
divₕ-extractAcc acc d (suc n) 0 = begin
        divₕ (suc acc)    d n d  ≡⟨ divₕ-extractAcc (suc acc) d n d ⟩
        suc acc +  divₕ 0 d n d  ≡⟨ sym $ +-suc acc _ ⟩
        acc + suc (divₕ 0 d n d) ≡⟨ cong (acc +_) $ sym $ divₕ-extractAcc 1 d n d ⟩
        acc +      divₕ 1 d n d  ∎
    where
        open ≡-Reasoning

⌊n/5/2⌋≡n/10 : ∀ n -> ⌊ ⌊ n /5⌋ /2⌋ ≡ n / 10
⌊n/5/2⌋≡n/10 0 = refl
⌊n/5/2⌋≡n/10 (suc 0) = refl
⌊n/5/2⌋≡n/10 (suc (suc 0)) = refl
⌊n/5/2⌋≡n/10 (suc (suc (suc 0))) = refl
⌊n/5/2⌋≡n/10 (suc (suc (suc (suc 0)))) = refl
⌊n/5/2⌋≡n/10 (suc (suc (suc (suc (suc 0))))) = refl
⌊n/5/2⌋≡n/10 (suc (suc (suc (suc (suc (suc 0)))))) = refl
⌊n/5/2⌋≡n/10 (suc (suc (suc (suc (suc (suc (suc 0))))))) = refl
⌊n/5/2⌋≡n/10 (suc (suc (suc (suc (suc (suc (suc (suc 0)))))))) = refl
⌊n/5/2⌋≡n/10 (suc (suc (suc (suc (suc (suc (suc (suc (suc 0))))))))) = refl
⌊n/5/2⌋≡n/10 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n-10)))))))))) =
        let n = 10 + n-10 in begin
            ⌊ ⌊ n /5⌋ /2⌋        ≡⟨⟩
            suc ⌊ ⌊ n-10 /5⌋ /2⌋ ≡⟨ cong suc $ ⌊n/5/2⌋≡n/10 n-10 ⟩
            suc (n-10 / 10)      ≡⟨ sym $ [n+m]/n≡1+m/n (n-10) 9 ⟩
            n / 10               ∎
    where
        open ≡-Reasoning

⌈⌊n/5⌋/2⌉≡[5+n]/10 : ∀ n -> ⌈ ⌊ n /5⌋ /2⌉ ≡ (5 + n) / 10
⌈⌊n/5⌋/2⌉≡[5+n]/10 zero = refl
⌈⌊n/5⌋/2⌉≡[5+n]/10 (suc zero) = refl
⌈⌊n/5⌋/2⌉≡[5+n]/10 (suc (suc zero)) = refl
⌈⌊n/5⌋/2⌉≡[5+n]/10 (suc (suc (suc zero))) = refl
⌈⌊n/5⌋/2⌉≡[5+n]/10 (suc (suc (suc (suc zero)))) = refl
⌈⌊n/5⌋/2⌉≡[5+n]/10 (suc (suc (suc (suc (suc n))))) = trans (cong suc $ ⌊n/5/2⌋≡n/10 n) (sym $ divₕ-extractAcc 1 9 n 9)

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

5⌊n/5⌋+n%5≡n : ∀ n -> 5 * ⌊ n /5⌋ + n % 5 ≡ n
5⌊n/5⌋+n%5≡n zero = refl
5⌊n/5⌋+n%5≡n (suc zero) = refl
5⌊n/5⌋+n%5≡n (suc (suc zero)) = refl
5⌊n/5⌋+n%5≡n (suc (suc (suc zero))) = refl
5⌊n/5⌋+n%5≡n (suc (suc (suc (suc zero)))) = refl
5⌊n/5⌋+n%5≡n (suc (suc (suc (suc (suc n-5))))) = let n = 5 + n-5 in begin
        5 * ⌊ n /5⌋ + n % 5                 ≡⟨ cong (λ x → 5 * ⌊ n /5⌋ + x % 5) $ +-comm 5 n-5 ⟩
        5 * suc ⌊ n-5 /5⌋ + (n-5 + 5) % 5   ≡⟨ cong (5 * suc ⌊ n-5 /5⌋ +_) $ a+n[modₕ]n≡a[modₕ]n 0 n-5 4 ⟩
        5 * suc ⌊ n-5 /5⌋ + n-5 % 5         ≡⟨ cong (_+ n-5 % 5) $ *-suc 5 ⌊ n-5 /5⌋ ⟩
        5 + 5 * ⌊ n-5 /5⌋ + n-5 % 5         ≡⟨ +-assoc 5 (5 * ⌊ n-5 /5⌋) (n-5 % 5) ⟩
        5 + (5 * ⌊ n-5 /5⌋ + n-5 % 5)       ≡⟨ cong (5 +_) $ 5⌊n/5⌋+n%5≡n n-5 ⟩
        5 + n-5                             ≡⟨⟩
        n                                   ∎
    where
        open ≡-Reasoning

a+a*n/10≥a*[n+5]/10 : ∀ a n -> a + a * (n / 10) ≥ a * ((5 + n) / 10)
a+a*n/10≥a*[n+5]/10 a n = begin
        a * ((5 + n) / 10)      ≤⟨ *-monoʳ-≤ a (5+n/10≤10+n/10 n) ⟩
        a * ((10 + n) / 10)     ≡⟨ cong (a *_) $ [n+m]/n≡1+m/n n 9 ⟩
        a * suc (n / 10)        ≡⟨ *-suc a (n / 10) ⟩
        a + a * (n / 10)        ∎
    where
        5≤10 : 5 ≤ 10
        5≤10 = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
        5+n≤10+n : ∀ n -> 5 + n ≤ 10 + n
        5+n≤10+n n = +-monoˡ-≤ n 5≤10
        5+n/10≤10+n/10 : ∀ n -> (5 + n) / 10 ≤ (10 + n) / 10
        5+n/10≤10+n/10 k = /-monoˡ-≤ {m = 5 + k} {n = 10 + k} {o = 10} $ 5+n≤10+n k
        open ≤-Reasoning

10⌊n/5⌋≤2n : ∀ n -> 10 * ⌊ n /5⌋ ≤ 2 * n
10⌊n/5⌋≤2n zero = z≤n
10⌊n/5⌋≤2n (suc zero) = z≤n
10⌊n/5⌋≤2n (suc (suc zero)) = z≤n
10⌊n/5⌋≤2n (suc (suc (suc zero))) = z≤n
10⌊n/5⌋≤2n (suc (suc (suc (suc zero)))) = z≤n
10⌊n/5⌋≤2n (suc (suc (suc (suc (suc n-5))))) = let n = 5 + n-5 in begin
        10 * ⌊ n /5⌋         ≡⟨⟩
        10 * suc ⌊ n-5 /5⌋   ≡⟨ *-suc 10 ⌊ n-5 /5⌋ ⟩
        10 + 10 * ⌊ n-5 /5⌋  ≤⟨ +-monoʳ-≤ 10 (10⌊n/5⌋≤2n n-5) ⟩
        10 + 2 * n-5         ≡⟨⟩
        2 * 5 + 2 * n-5      ≡⟨ sym $ *-distribˡ-+ 2 5 n-5 ⟩
        2 * n                ∎
    where
        open ≤-Reasoning

a+1+b+c+d≡a+b+1+c+d : ∀ a b c d -> a + suc (b + c + d) ≡ a + b + suc (c + d)
a+1+b+c+d≡a+b+1+c+d a b c d = begin
        a + suc (b + c + d)     ≡⟨ cong (a +_) $ cong suc $ +-assoc b c d ⟩
        a + suc (b + (c + d))   ≡⟨ cong (a +_) $ sym $ +-suc b (c + d) ⟩
        a + (b + suc (c + d))   ≡⟨ sym $ +-assoc a b (suc (c + d)) ⟩
        a + b + suc (c + d)     ∎
    where
        open ≡-Reasoning


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
    where
        open ≡-Reasoning

m≤m+n≡k : {m n k : ℕ} -> m + n ≡ k -> m ≤ k
m≤m+n≡k {m} {n} {k} pf = subst (m ≤_) pf (m≤m+n m n)

n≤m+n≡k : {m n k : ℕ} -> m + n ≡ k -> n ≤ k
n≤m+n≡k {m} {n} {k} pf = subst (n ≤_) pf (m≤n+m n m)
