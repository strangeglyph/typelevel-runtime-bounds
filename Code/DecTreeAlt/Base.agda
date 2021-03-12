module DecTreeAlt.Base where

open import Data.Nat
open import Data.Nat.Properties hiding (_≤?_)
open import Relation.Binary.PropositionalEquality
open import Function
open import Level using (Level)

open import DecTreeAlt.Core
open import Nat.Props

private
    variable
        b c : Level
        Result : Set b
        Compare : Set c

infix 1 _>>=_
infix 1 _<$>_

height-≡ : {h h' : ℕ} -> h ≡ h' -> DecTree Compare Result h -> DecTree Compare Result h'
height-≡ {Compare = Compare} {Result = Result} pf = subst (DecTree Compare Result) pf


_>>=_ : {R R' : Set b} -> {h1 h2 : ℕ} -> DecTree Compare R' h1 -> (R' -> DecTree Compare R h2) -> DecTree Compare R (h1 + h2)
tree >>= f = chain tree f ≤-refl

_<$>_ : {R R' : Set b} -> {h : ℕ} -> (R' -> R) -> DecTree Compare R' h -> DecTree Compare R h
_<$>_ {h = h} f t = height-≡ (+-identityʳ h) $ t >>= λ r -> return $ f r

_<&>_ : {R R' : Set b} -> {h : ℕ} -> DecTree Compare R' h -> (R' -> R) -> DecTree Compare R h
t <&> f = f <$> t



if'_≤?_then_else_ : {h : ℕ} -> (x y : Compare) -> (left right : DecTree Compare Result h) -> DecTree Compare Result (suc h)
if'_≤?_then_else_ {h = h} x y left right = if x ≤? y then[ ≤-refl ] left else[ ≤-refl ] right
