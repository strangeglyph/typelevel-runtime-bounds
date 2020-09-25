module Int.Props.Misc where

open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕ-Props
open import Data.Integer as ℤ
open import Data.Integer.Properties as ℤ-Props

open import Relation.Binary.PropositionalEquality
open import Function

0-a+[k+a]≡k : (a k : ℕ) -> 0 ⊖ a ℤ.+ + (k ℕ.+ a) ≡ + k
0-a+[k+a]≡k zero k = cong (+_) $ ℕ-Props.+-identityʳ k
0-a+[k+a]≡k a@(ℕ.suc a-1) k = begin
        k ℕ.+ a ⊖ a          ≡⟨ sym $ [+m]-[+n]≡m⊖n (k ℕ.+ a) a ⟩
        + (k ℕ.+ a) ℤ.- aℤ   ≡⟨⟩
        + k ℤ.+ aℤ  ℤ.- aℤ   ≡⟨ ℤ-Props.+-assoc (+ k) aℤ (- aℤ)  ⟩
        + k ℤ.+ (aℤ ℤ.- aℤ)  ≡⟨ cong (λ x → + k ℤ.+ x) $ m≡n⇒m-n≡0 aℤ _ refl  ⟩
        + k ℤ.+ + 0          ≡⟨ ℤ-Props.+-identityʳ (+ k) ⟩
        + k                  ∎
    where
        open ≡-Reasoning
        aℤ = + a

0-a+suca≡1 : (a : ℕ) -> 0 ⊖ a ℤ.+ + ℕ.suc a ≡ + 1
0-a+suca≡1 a = 0-a+[k+a]≡k a 1


suca-b+c≡suc[a-b+c] : ∀ a b c -> ℕ.suc a ⊖ b ℤ.+ + c ≡ + 1 ℤ.+ (a ⊖ b ℤ.+ + c)
suca-b+c≡suc[a-b+c] a b c = begin
        ℕ.suc a ⊖ b ℤ.+ cℤ                ≡⟨ cong (λ x → x ℤ.+ cℤ) $ sym $ [+m]-[+n]≡m⊖n (ℕ.suc a) b ⟩
        (+ ℕ.suc a) ℤ.- bℤ ℤ.+ cℤ         ≡⟨⟩
        (+ 1 ℤ.+ aℤ) ℤ.- bℤ ℤ.+ cℤ        ≡⟨ ℤ-Props.+-assoc (+ 1 ℤ.+ aℤ) (- bℤ) cℤ ⟩
        (+ 1 ℤ.+ aℤ) ℤ.+ (- bℤ ℤ.+ cℤ)    ≡⟨ ℤ-Props.+-assoc (+ 1) aℤ ((- bℤ) ℤ.+ cℤ) ⟩
        + 1 ℤ.+ (aℤ ℤ.+ (- bℤ ℤ.+ cℤ))    ≡⟨ cong (λ x → + 1 ℤ.+ x) $ sym $ ℤ-Props.+-assoc aℤ (- bℤ) cℤ ⟩
        + 1 ℤ.+ (aℤ ℤ.- bℤ ℤ.+ cℤ)        ≡⟨ cong (λ x → + 1 ℤ.+ (x ℤ.+ cℤ)) $ [+m]-[+n]≡m⊖n a b ⟩
        + 1 ℤ.+ (a ⊖ b ℤ.+ cℤ)            ∎
    where
        open ≡-Reasoning
        aℤ = + a
        bℤ = + b
        cℤ = + c
