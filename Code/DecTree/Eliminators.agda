module DecTree.Eliminators where

open import Data.Bool hiding (_≤?_)
open import Data.Nat hiding (_≤?_)
open import Data.Nat.Properties hiding (_≤?_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.HeterogeneousEquality as H using (≡-subst-removable ; ≅-to-≡)
open import Function
open import Level using (Level)

open import DecTree.Core
open import DecTree.Base
open import Leq
open import Util

private
    variable
        a c : Level
        A B : Set a
        Compare : Set c


subst-elim :  {{_ : Leq Compare}}
               -> ∀ {l₁ l₂}
               -> (eq : l₁ ≡ l₂)
               -> (v : DecTree Compare A l₁)
               -> reduce (subst (DecTree Compare A) eq v) ≡ reduce v
subst-elim {Compare = C} {A = A} eq v = ≅-to-≡ $ ≅-cong' (sym eq) reduce $ ≡-subst-removable (DecTree C A) eq v


return-elim : {{_ : Leq Compare}} -> (a : A) -> reduce (return a) ≡ a
return-elim a = refl


branch-elim : {{_ : Leq Compare}} -> ∀ {x y} -> ∀ {l} -> (v : DecTree Compare A l) -> reduce (if x ≤? y then v else v) ≡ reduce v
branch-elim {x = x} {y = y} _ with x <= y
... | false = refl
... | true = refl

branch'-elim : {{_ : Leq Compare}} -> ∀ {x y} -> ∀ {l} -> (v : DecTree Compare A l) -> reduce (if' x ≤? y then v else v) ≡ reduce v
branch'-elim {Compare = C} {A = A} {x = x} {y} {l} v with x <= y
... | false = trans (subst-elim (cong suc $ ⊔-idem l) (if x ≤? y then v else v)) $ branch-elim v
... | true = trans (subst-elim (cong suc $ ⊔-idem l) (if x ≤? y then v else v)) $ branch-elim v


bind-elim :  {{_ : Leq Compare}}
              -> ∀ {l₁ l₂}
              -> (v : DecTree Compare A l₁)
              -> (f : A -> DecTree Compare B l₂)
              -> reduce (v >>= f) ≡ reduce (f (reduce v))
bind-elim v trans = refl


apply-elim : {{_ : Leq Compare}} -> ∀ {l} -> (f : A -> B) -> (v : DecTree Compare A l) -> reduce (f <$> v) ≡ f (reduce v)
apply-elim {l = l} f v = subst-elim (+-identityʳ l) (v >>= (λ r -> return (f r)))
