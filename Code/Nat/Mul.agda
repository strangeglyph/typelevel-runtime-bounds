module Nat.Mul where

open import Data.Nat renaming (_*_ to _ℕ*_)

_*_ : ℕ -> ℕ -> ℕ
zero * y = 0
suc zero * y = y
suc (suc x) * y = y + suc x * y
