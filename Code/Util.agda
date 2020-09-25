module Util where

open import Level using (Level)
open import Data.Nat
open import Data.Nat.Properties using (m≤n+m)
open import Data.Vec
open import Data.Fin using (Fin ; raise ; inject≤) renaming (zero to fzero ; suc to fsuc)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality as H using (_≅_)
open import Function

private
    variable
        a b c d : Level
        A : Set a
        B : Set b

len : {n : ℕ} -> Vec A n -> ℕ
len {n = n} _ = n


subst2 : (P : A -> B -> Set c) {a₁ a₂ : A} {b₁ b₂ : B} -> a₁ ≡ a₂ -> b₁ ≡ b₂ -> P a₁ b₁ -> P a₂ b₂
subst2 P refl refl p = p


≅-cong' :  {B : A -> Set b} {C : Set c}
        -> {a1 a2 : A}
        -> a1 ≡ a2
        -> {x : B a1} -> {y : B a2}
        -> (f : {a : A} -> B a -> C)
        -> x ≅ y
        -> f x ≅ f y
≅-cong' refl f H.refl  = H.refl


subst-appl : {P : A -> Set a} -> (f : (a : A) -> P a -> B) -> {a b : A} -> (eq : a ≡ b) -> (x : P a) -> f a x ≡ f b (subst P eq x)
subst-appl f eq x rewrite eq = refl

subst-appl' : {P : A -> Set a} -> (f : {a : A} -> P a -> B) -> {a b : A} -> (eq : a ≡ b) -> (x : P a) -> f (subst P eq x) ≡ f x
subst-appl' f eq x rewrite eq = refl

cong₃ : {A : Set a} {B : Set b} {C : Set c} {D : Set d} -> (f : A -> B -> C -> D) -> {a1 a2 : A} -> a1 ≡ a2 -> {b1 b2 : B} -> b1 ≡ b2 -> {c1 c2 : C} -> c1 ≡ c2 -> f a1 b1 c1 ≡ f a2 b2 c2
cong₃ f refl refl refl = refl

data _1?+⟨_⟩ (A : ℕ -> Set a) (n : ℕ) : Set a where
    +0 : A n       -> A 1?+⟨ n ⟩
    +1 : A (suc n) -> A 1?+⟨ n ⟩

data _⟨_⟩-1? (A : ℕ -> Set a) : (n : ℕ) -> Set a where
    neutral   : {n : ℕ} -> A n -> A ⟨ n ⟩-1?
    decrement : {n : ℕ} -> A n -> A ⟨ suc n ⟩-1?

record Indexed (A : Set a) (l : ℕ) : Set a where
     constructor index
     field
         idx : Fin l
         value : A

raise-ix : ∀ {l} -> (k : ℕ) -> Indexed A l -> Indexed A (k + l)
raise-ix k (index i x) = index (raise k i) x

inject-ix : ∀ {l} -> (k : ℕ) -> Indexed A l -> Indexed A (k + l)
inject-ix k (index i x) = index (inject≤ i $ m≤n+m _ _) x

f0 : ∀ {n} -> Fin (suc n)
f0 = fzero
f1 : ∀ {n} -> Fin (suc $ suc n)
f1 = fsuc f0
f2 : ∀ {n} -> Fin (suc $ suc $ suc n)
f2 = fsuc f1
f3 : ∀ {n} -> Fin (suc $ suc $ suc $ suc n)
f3 = fsuc f2
f4 : ∀ {n} -> Fin (suc $ suc $ suc $ suc $ suc n)
f4 = fsuc f3
f5 : ∀ {n} -> Fin (suc $ suc $ suc $ suc $ suc $ suc n)
f5 = fsuc f4
