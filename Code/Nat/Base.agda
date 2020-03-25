module Nat.Base where

open import Data.Nat
open import Function

⌈_/5⌉ : ℕ -> ℕ
⌈ 0 /5⌉ = 0
⌈ 1 /5⌉ = 1
⌈ 2 /5⌉ = 1
⌈ 3 /5⌉ = 1
⌈ 4 /5⌉ = 1
⌈ suc (suc (suc (suc (suc n)))) /5⌉ = 1 + ⌈ n /5⌉

