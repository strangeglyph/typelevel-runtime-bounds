module Nat.Props where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Function

open import Nat.Base
open import Util

open import Nat.Props.Plus public
open import Nat.Props.Times public
open import Nat.Props.Minus public
open import Nat.Props.Max public
open import Nat.Props.Div public


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






