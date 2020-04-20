module Nat.Props.Div.Free where

open import Agda.Builtin.Nat using () renaming (div-helper to divₕ ; mod-helper to modₕ)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Nat.DivMod.Core
open import Data.Nat.Divisibility
open import Relation.Binary.PropositionalEquality
open import Function

open import Util
open import Nat.Base

open import Nat.Props.Plus
open import Nat.Props.Minus

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

-- public reimpl of DivMod.Core.divₕ-finish
divₕ-finish : ∀ d {m n-1} -> m < suc n-1 -> divₕ 0 d m n-1 ≡ 0
divₕ-finish _ {0} {_} _  = refl
divₕ-finish d {(suc m)} {(suc n-1)} (s≤s m<n) = divₕ-finish d m<n


divₕ-inc-offset : ∀ acc d n j k -> divₕ acc d n j ≡ divₕ acc d (k + n) (k + j)
divₕ-inc-offset acc d n j zero = refl
divₕ-inc-offset acc d n j (suc k) = divₕ-inc-offset acc d n j k



m<n⇒m/n≡0 : ∀ {m n-1} -> let n = suc n-1 in m < n -> m / n ≡ 0
m<n⇒m/n≡0 {m} {n-1} m<n = divₕ-finish n-1 m<n

/-distrib-+-mono : ∀ a b c-1 -> let c = suc c-1 in (a + b) / c ≤ 1 + a / c + b / c
/-distrib-+-mono a b c-1 = let c = suc c-1 in begin
        (a + b) / c

                               ≡⟨ cong (λ x → (x + b) / c) $ m≡m%n+[m/n]*n a c-1 ⟩

        ((a % c + a / c * c) + b) / c

                               ≡⟨ cong (λ x → ((a % c + a / c * c) + x) / c) $ m≡m%n+[m/n]*n b c-1 ⟩

        ((a % c + a / c * c) + (b % c + b / c * c)) / c

                               ≡⟨ cong (_/ c) $ +-double-comm' (a % c) (a / c * c) (b % c) (b / c * c) ⟩

        ((a % c + b % c) + (a / c * c + b / c * c)) / c

                               ≡⟨ cong (λ x -> ((a % c + b % c) + x) / c) $ sym $ *-distribʳ-+ c (a / c) (b / c) ⟩

        ((a % c + b % c) + (a / c + b / c) * c) / c

                               ≡⟨ +-distrib-/-∣ʳ {m = a % c + b % c} ((a / c + b / c) * c) $ n∣m*n (a / c + b / c) ⟩

        (a % c + b % c) / c + (a / c + b / c) * c / c

                         ≤⟨ +-monoˡ-≤ ((a / c + b / c) * c / c) $ /-monoˡ-≤ {o = c} $ +-monoʳ-≤ (a % c) $ <⇒≤ $ m%n<n b c-1 ⟩

        (a % c + c) / c + (a / c + b / c) * c / c

                               ≡⟨ cong (λ x → x + (a / c + b / c) * c / c) $ +-distrib-/-∣ʳ {m = a % c} c $ n∣n ⟩

        (a % c) / c + c / c + (a / c + b / c) * c / c

                               ≡⟨ cong (λ x → x + c / c + (a / c + b / c) * c / c) $ m<n⇒m/n≡0 $ m%n<n a c-1  ⟩

        0 + c / c + (a / c + b / c) * c / c

                               ≡⟨ cong (_+ (a / c + b / c) * c / c) $ n/n≡1 c ⟩

        1 + (a / c + b / c) * c / c

                               ≡⟨ cong suc $ m*n/n≡m (a / c + b / c) c ⟩

        1 + a / c + b / c      ∎
    where
        open ≤-Reasoning

a*b/c≤a*[b/c]+a : ∀ a b c-1 -> let c = suc c-1 in a * b / c ≤ a * (b / c) + a
a*b/c≤a*[b/c]+a 0 b c-1 = z≤n
a*b/c≤a*[b/c]+a a@(suc a-1) b c-1 = let c = suc c-1 in begin
        a * b / c                            ≡⟨⟩
        (b + a-1 * b) / c                    ≤⟨ /-distrib-+-mono b (a-1 * b) c-1 ⟩
        1 + (b / c) + (a-1 * b) / c          ≤⟨ +-monoʳ-≤ (1 + (b / c)) $ a*b/c≤a*[b/c]+a a-1 b c-1 ⟩
        1 + (b / c) + (a-1 * (b / c) + a-1)  ≡⟨ cong suc $ sym $ +-assoc (b / c) (a-1 * (b / c)) a-1 ⟩
        1 + (b / c) + a-1 * (b / c) + a-1    ≡⟨⟩
        1 + a * (b / c) + a-1                ≡⟨ sym $ +-suc (a * (b / c)) a-1 ⟩
        a * (b / c) + a                      ∎
    where
        open ≤-Reasoning



divₕ-*-cancel : ∀ a acc k n j -> let d = k + j in divₕ acc d n j ≡ divₕ acc (d + a * suc d) (n + a * n) (j + a * suc j)
divₕ-*-cancel zero acc k n j = sym $ cong₃ (divₕ acc) (+-identityʳ $ k + j) (+-identityʳ n) (+-identityʳ j)
divₕ-*-cancel a@(suc a-1) acc k zero j = let d = k + j in
                                         cong (λ x → divₕ acc (d + a * suc d) x (j + a * suc j)) $ sym $ *-zeroʳ a-1
divₕ-*-cancel a@(suc a-1) acc zero n@(suc n-1) zero = begin
        divₕ acc 0 n 0 ≡⟨⟩
        divₕ (suc acc) 0 n-1 0                         ≡⟨ divₕ-*-cancel a (suc acc) 0 n-1 0 ⟩
        divₕ (suc acc) (a * 1) (n-1 + a * n-1) (a * 1) ≡⟨ cong (λ x → divₕ (suc acc) x (suc a * n-1) x) $ *-identityʳ a ⟩
        divₕ (suc acc) a (n-1 + a * n-1) a             ≡⟨⟩
        divₕ acc a (n + a * n-1) 0                     ≡⟨ divₕ-inc-offset acc a (n + a * n-1) 0 a ⟩
        divₕ acc a (a + (n + a * n-1)) (a + 0)         ≡⟨ cong (divₕ acc a (a + (n + a * n-1))) $ +-identityʳ a ⟩
        divₕ acc a (a + (n + a * n-1)) a               ≡⟨ cong (λ x → divₕ acc a x a) $ +-assoc-commˡ a n (a * n-1) ⟩
        divₕ acc a (n + (a + a * n-1)) a               ≡⟨ cong (λ x → divₕ acc a x a) $ cong (n +_) $ sym $ *-suc a n-1 ⟩
        divₕ acc a (n + a * n) a                       ≡⟨ cong (λ x → divₕ acc x (n + a * n) x) $ sym $ *-identityʳ a ⟩
        divₕ acc (a * 1) (n + a * n) (a * 1)           ∎
    where
        open ≡-Reasoning
divₕ-*-cancel a@(suc a-1) acc zero n@(suc n-1) j@(suc j-1) = begin
        divₕ acc j n j

                            ≡⟨⟩

        divₕ acc j n-1 j-1

                            ≡⟨ divₕ-*-cancel a acc 1 n-1 j-1 ⟩

        divₕ acc (j + a * suc j) (n-1 + a * n-1) (j-1 + a * j)

                            ≡⟨⟩

        divₕ acc (j + a * suc j) (n + a * n-1) (j + a * j)

                            ≡⟨ divₕ-inc-offset acc (j + a * suc j) (n + a * n-1) (j + a * j) a ⟩

        divₕ acc (j + a * suc j) (a + (n + a * n-1)) (a + (j + a * j))

                            ≡⟨ cong₂ (divₕ acc (j + a * suc j)) (+-assoc-commˡ a n (a * n-1)) (+-assoc-commˡ a j (a * j)) ⟩

        divₕ acc (j + a * suc j) (n + (a + a * n-1)) (j + (a + a * j))

                            ≡⟨ sym $ cong₂ (λ x y → divₕ acc (j + a * suc j) (n + x) (j + y)) (*-suc a n-1) (*-suc a j) ⟩

        divₕ acc (j + a * suc j) (n + a * n) (j + a * suc j) ∎
    where
        open ≡-Reasoning
divₕ-*-cancel a@(suc a-1) acc k@(suc k-1) n@(suc n-1) zero = begin
        divₕ acc (k + 0) n 0

                             ≡⟨ cong (λ x → divₕ acc x n 0) $ +-identityʳ k ⟩

        divₕ (suc acc) k n-1 k

                            ≡⟨ divₕ-*-cancel a (suc acc) 0 n-1 k ⟩

        divₕ (suc acc) (k + a * suc k) (n-1 + a * n-1) (k + a * suc k)

                            ≡⟨⟩

        divₕ acc (k + a * suc k) (n + a * n-1) 0

                            ≡⟨ divₕ-inc-offset acc (k + a * suc k) (n + a * n-1) 0 a ⟩

        divₕ acc (k + a * suc k) (a + (n + a * n-1)) (a + 0)

                            ≡⟨ cong (divₕ acc (k + a * suc k) (a + (n + a * n-1))) $ +-identityʳ a ⟩

        divₕ acc (k + a * suc k) (a + (n + a * n-1)) a

                            ≡⟨ cong (λ x → divₕ acc (k + a * suc k) x a) $ +-assoc-commˡ a n (a * n-1) ⟩

        divₕ acc (k + a * suc k) (n + (a + a * n-1)) a

                            ≡⟨ cong (λ x → divₕ acc (k + a * suc k) (n + x) a) $ sym $ *-suc a n-1 ⟩

        divₕ acc (k + a * suc k) (n + a * n) a

                            ≡⟨ cong (divₕ acc (k + a * suc k) (n + a * n)) $ sym $ *-identityʳ a ⟩

        divₕ acc (k + a * suc k) (n + a * n) (a * 1)

                            ≡⟨ cong (λ x → divₕ acc (x + a * suc x) (n + a * n) (a * 1)) $ sym $ +-identityʳ k ⟩

        divₕ acc ((k + 0) + a * suc (k + 0)) (n + a * n) (a * 1) ∎
    where
        open ≡-Reasoning
divₕ-*-cancel a@(suc a-1) acc k@(suc k-1) n@(suc n-1) j@(suc j-1) = let d = k + j in let d' = suc k + j-1 in begin
        divₕ acc d n j

                           ≡⟨⟩
        divₕ acc d n-1 j-1

                           ≡⟨ cong (λ x → divₕ acc x n-1 j-1) $ +-suc k j-1 ⟩

        divₕ acc d' n-1 j-1

                           ≡⟨ divₕ-*-cancel a acc (suc k) n-1 j-1 ⟩

        divₕ acc (d' + a * suc d') (n-1 + a * n-1) (j-1 + a * j)

                           ≡⟨⟩

        divₕ acc (d' + a * suc d') (n + a * n-1) (j + a * j)

                           ≡⟨ divₕ-inc-offset acc (d' + a * suc d') (n + a * n-1) (j + a * j) a ⟩

        divₕ acc (d' + a * suc d') (a + (n + a * n-1)) (a + (j + a * j))

                           ≡⟨ cong₂ (divₕ acc (d' + a * suc d')) (+-assoc-commˡ a n (a * n-1)) (+-assoc-commˡ a j (a * j)) ⟩

        divₕ acc (d' + a * suc d') (n + (a + a * n-1)) (j + (a + a * j))

                           ≡⟨ sym $ cong₂ (λ x y → divₕ acc (d' + a * suc d') (n + x) (j + y)) (*-suc a n-1) (*-suc a j) ⟩

        divₕ acc (d' + a * suc d') (n + a * n) (j + a * suc j)

                           ≡⟨ cong (λ x → divₕ acc (x + a * suc x) (n + a * n) (j + a * suc j)) $ sym $ +-suc k j-1 ⟩

        divₕ acc (d + a * suc d) (n + a * n) (j + a * suc j) ∎
    where
        open ≡-Reasoning



am/an≡m/n : ∀ a-1 m n-1 -> let a = suc a-1 in let n = suc n-1 in (a * m) / (a * n) ≡ m / n
am/an≡m/n a-1 m n-1 = sym $ divₕ-*-cancel a-1 0 0 m n-1

m/n≤a[m/an]+a : ∀ a-1 m n-1 -> let a = suc a-1 in let n = suc n-1 in m / n ≤ a * (m / (a * n)) + a
m/n≤a[m/an]+a a-1 m n-1 = let a = suc a-1 in let n = suc n-1 in begin
        m / n                  ≡⟨ sym $ am/an≡m/n a-1 m n-1 ⟩
        (a * m) / (a * n)      ≤⟨ a*b/c≤a*[b/c]+a a m (n-1 + a-1 * n) ⟩
        a * (m / (a * n)) + a  ∎
    where
        open ≤-Reasoning




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



1+a+b+c≡n∧a,b≥3n/10⇒c≤4n/10 : ∀ {a b c n} -> suc (a + b + c) ≡ n -> suc a ≥ 3 * (n / 10) -> suc b ≥ 3 * (n / 10) -> c ≤ 4 * (n / 10) + 19
1+a+b+c≡n∧a,b≥3n/10⇒c≤4n/10 {a} {b} {c} {n} 1+a+b+c≡n a≥3n/10 b≥3n/10 = begin
        c                                                         ≡⟨ a+b≡c⇒b≡c-a (suc a + b) c n 1+a+b+c≡n ⟩
        n ∸ (1 + a + b)                                           ≤⟨ ∸-monoʳ-≤ n 1+a+b≥3n/10+b ⟩
        n ∸ (3 * (n / 10) + b)                                    ≡⟨⟩
        suc n ∸ suc (3 * (n / 10) + b)                            ≡⟨ cong (suc n ∸_) $ sym $ +-suc (3 * (n / 10)) b ⟩
        suc n ∸ (3 * (n / 10) + suc b)                            ≤⟨ ∸-monoʳ-≤ (suc n) 3n/10+1+b≥3n/10+3n/10 ⟩
        suc n ∸ (3 * (n / 10) + 3 * (n / 10))                     ≡⟨ cong (suc n ∸_) (sym $ *-distribʳ-+ (n / 10) 3 3) ⟩
        suc n ∸ 6 * (n / 10)                                      ≡⟨ cong (_∸ 6 * (n / 10)) $ m≡m%n+[m/n]*n (suc n) 9  ⟩
        suc n % 10 + (suc n / 10) * 10 ∸ 6 * (n / 10)             ≡⟨ cong (λ x → suc n % 10 + x ∸ 6 * (n / 10)) $ *-comm (suc n / 10) 10 ⟩
        suc n % 10 + 10 * (suc n / 10) ∸ 6 * (n / 10)             ≡⟨⟩
        6 + suc n % 10 + 10 * (suc n / 10) ∸ (6 + 6 * (n / 10))   ≡⟨ cong ((6 + suc n % 10 + 10 * (suc n / 10)) ∸_) $ sym $ *-suc 6 (n / 10) ⟩
        6 + suc n % 10 + 10 * (suc n / 10) ∸ 6 * suc (n / 10)     ≡⟨ cong (λ x → 6 + suc n % 10 + 10 * (suc n / 10) ∸ 6 * x) $ sym $ [n+m]/n≡1+m/n n 9 ⟩
        6 + suc n % 10 + 10 * (suc n / 10) ∸ 6 * ((10 + n) / 10)  ≤⟨ ∸-monoʳ-≤ (6 + suc n % 10 + 10 * (suc n / 10)) 6[10+n]/10≥6[1+n]/10 ⟩
        6 + suc n % 10 + 10 * (suc n / 10) ∸ 6 * (suc n / 10)     ≡⟨ +-∸-assoc (6 + suc n % 10) $ *-monoˡ-≤ (suc n / 10) 6≤10 ⟩
        6 + suc n % 10 + (10 * (suc n / 10) ∸ 6 * (suc n / 10))   ≡⟨ cong ((6 + suc n % 10) +_) $ sym $ *-distribʳ-∸ (suc n / 10) 10 6 ⟩
        6 + suc n % 10 + 4 * (suc n / 10)                         ≤⟨ +-monoˡ-≤ (4 * (suc n / 10)) (+-monoʳ-≤ 6 (a[modₕ]n<n 0 (suc n) 9)) ⟩
        15 + 4 * (suc n / 10)                                     ≤⟨ +-monoʳ-≤ 15 $ *-monoʳ-≤ 4 $ /-monoˡ-≤ {suc n} {10 + n} {10} $ +-monoˡ-≤ n $ s≤s z≤n ⟩
        15 + 4 * ((10 + n) / 10)                                  ≡⟨ cong (λ x -> 15 + 4 * x) $ [n+m]/n≡1+m/n n 9 ⟩
        15 + 4 * suc (n / 10)                                     ≡⟨ cong (15 +_) $ *-suc 4 (n / 10) ⟩
        15 + (4 + 4 * (n / 10))                                   ≡⟨ +-assoc 15 4 (4 * (n / 10)) ⟩
        19 + 4 * (n / 10)                                         ≡⟨ +-comm 19 (4 * (n / 10)) ⟩
        4 * (n / 10) + 19                                         ∎
    where
        open ≤-Reasoning
        1+a+b≥3n/10+b : 1 + a + b ≥ 3 * (n / 10) + b
        1+a+b≥3n/10+b = +-monoˡ-≤ b a≥3n/10
        3n/10+1+b≥3n/10+3n/10 : (3 * (n / 10)) + suc b ≥ 3 * (n / 10) + 3 * (n / 10)
        3n/10+1+b≥3n/10+3n/10 = +-monoʳ-≤ (3 * (n / 10)) b≥3n/10
        6[10+n]/10≥6[1+n]/10 : 6 * ((10 + n) / 10) ≥ 6 * (suc n / 10)
        6[10+n]/10≥6[1+n]/10 = *-monoʳ-≤ 6 $ /-monoˡ-≤ {suc n} {10 + n} {10} $ +-monoˡ-≤ n $ s≤s z≤n
        6≤10 : 6 ≤ 10
        6≤10 = ≤-step $ ≤-step $ ≤-step $ ≤-step ≤-refl
        [1+n]%10≤9 : suc n % 10 ≤ 9
        [1+n]%10≤9 = a[modₕ]n<n 0 (suc n) 9

1+a+b≡n∧b≥3n/10⇒a≤7n/10 : ∀ {a b n} -> 1 + a + b ≡ n -> suc b ≥ 3 * (n / 10) -> a ≤ 7 * (n / 10) + 9
1+a+b≡n∧b≥3n/10⇒a≤7n/10 {a} {b} {n} 1+a+b≡n b≥3n/10 = begin
        a                                        ≡⟨ a≡n∸[1+b] ⟩
        n ∸ suc b                                ≡⟨ cong (_∸ suc b) $ m≡m%n+[m/n]*n n 9 ⟩
        n % 10 + n / 10 * 10 ∸ suc b             ≡⟨ cong (λ x → n % 10 + x ∸ suc b) $ *-comm (n / 10) 10  ⟩
        n % 10 + 10 * (n / 10) ∸ suc b           ≤⟨ ∸-monoʳ-≤ (n % 10 + 10 * (n / 10)) b≥3n/10  ⟩
        n % 10 + 10 * (n / 10) ∸ 3 * (n / 10)    ≡⟨ +-∸-assoc (n % 10) $ *-monoˡ-≤ (n / 10) 3≤10 ⟩
        n % 10 + (10 * (n / 10) ∸ 3 * (n / 10))  ≡⟨ cong (n % 10 +_) $ sym $ *-distribʳ-∸ (n / 10) 10 3 ⟩
        n % 10 + 7 * (n / 10)                    ≡⟨ +-comm (n % 10) (7 * (n / 10)) ⟩
        7 * (n / 10) + n % 10                    ≤⟨ +-monoʳ-≤ (7 * (n / 10)) $  a[modₕ]n<n 0 n 9 ⟩
        7 * (n / 10) + 9                         ∎
    where
        open ≤-Reasoning
        a≡n∸[1+b] : a ≡ n ∸ suc b
        a≡n∸[1+b] = a+b≡c⇒b≡c-a (1 + b) a n $ sym $ trans (sym 1+a+b≡n) (cong suc $ +-comm a b)
        3≤10 : 3 ≤ 10
        3≤10 = s≤s $ s≤s $ s≤s z≤n
