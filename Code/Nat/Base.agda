module Nat.Base where

open import Data.Nat
open import Function

⌊_/5⌋ : ℕ -> ℕ
⌊ 0 /5⌋ = 0
⌊ 1 /5⌋ = 0
⌊ 2 /5⌋ = 0
⌊ 3 /5⌋ = 0
⌊ 4 /5⌋ = 0
⌊ suc (suc (suc (suc (suc n)))) /5⌋ = 1 + ⌊ n /5⌋


⌈_/5⌉ : ℕ -> ℕ
⌈ n /5⌉ = ⌊ 4 + n /5⌋
