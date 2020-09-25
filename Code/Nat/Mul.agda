module Nat.Mul where

open import Data.Nat renaming (_*_ to _ℕ*_ ; _^_ to _ℕ^_)

infix 30 _^_

_*_ : ℕ -> ℕ -> ℕ
zero * y = 0
suc zero * y = y
suc (suc x) * y = y + suc x * y

_^_ : ℕ -> ℕ -> ℕ
x ^ 0 = 1
x ^ (suc l) = x * x ^ l
