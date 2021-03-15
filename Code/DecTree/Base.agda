module DecTree.Base where

open import Data.Nat
open import Data.Nat.Properties hiding (_≤?_)
open import Relation.Binary.PropositionalEquality
open import Function
open import Level using (Level)

open import DecTree.Core
open import Nat.Props

private
    variable
        b c : Level
        Result : Set b
        Compare : Set c

infix 1 _<$>_

height-≡ : {h h' : ℕ} -> h ≡ h' -> DecTree Compare Result h -> DecTree Compare Result h'
height-≡ {Compare = Compare} {Result = Result} pf = subst (DecTree Compare Result) pf

_<$>_ : {R R' : Set b} -> {h : ℕ} -> (R' -> R) -> DecTree Compare R' h -> DecTree Compare R h
_<$>_ {h = h} f t = t >>= λ r -> return $ f r

_<&>_ : {R R' : Set b} -> {h : ℕ} -> DecTree Compare R' h -> (R' -> R) -> DecTree Compare R h
t <&> f = f <$> t

_>>='_ : {R R' : Set b} -> {h1 h2 : ℕ} -> DecTree Compare R' h1 -> (R' -> DecTree Compare R h2) -> DecTree Compare R (h1 + h2)
_>>='_ {h1 = h1} {h2 = h2} t trans = height-≡ (+-comm h2 h1) $ t >>= trans

delay' : {h : ℕ} -> (d : ℕ) -> DecTree Compare Result h -> DecTree Compare Result (d + h)
delay' zero tree = tree
delay' (suc d) tree = delay1 $ delay' d tree

delay : {h : ℕ} -> (d : ℕ) -> DecTree Compare Result h -> DecTree Compare Result (h + d)
delay d tree = height-≡ (+-comm d _) $ delay' d tree

delay-< : {d d' : ℕ} -> d < d' -> DecTree Compare Result d -> DecTree Compare Result d'
delay-< d<d' tree = case diff d<d' of λ (Diff n by pf) -> height-≡ pf $ delay1 $ delay n tree

delay-≤ : {d d' : ℕ} -> d ≤ d' -> DecTree Compare Result d -> DecTree Compare Result d'
delay-≤ {d = d} d≤d' tree = case diff d≤d' of λ where
                         (Diff 0 by pf)       -> height-≡ (trans (sym $ +-identityʳ d) pf) tree
                         (Diff (suc n) by pf) -> height-≡ pf $ delay (suc n) tree


if[_]_≤?_then_else_by_ : ∀ {l} {Idx : Set l} -> {i₁ i₂ : Idx} -> (Result : Idx -> Set b) -> {h₁ h₂ : ℕ} -> Compare -> Compare -> DecTree Compare (Result i₁) h₁ -> DecTree Compare (Result i₂) h₂ -> i₂ ≡ i₁ -> DecTree Compare (Result i₁) (1 + (h₁ ⊔ h₂))
if[_]_≤?_then_else_by_ {Compare = C} R {h₂ = h} a b left right proof =
                    if a ≤? b
                    then left
                    else subst (λ i -> DecTree C (R i) h) proof right


if'_≤?_then_else_ : {h : ℕ} -> (x y : Compare) -> (left right : DecTree Compare Result h) -> DecTree Compare Result (suc h)
if'_≤?_then_else_ {h = h} x y left right = height-≡ (cong suc $ ⊔-idem h) $ if x ≤? y then left else right
