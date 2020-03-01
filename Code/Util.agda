module Util where

open import Level using (Level)
open import Data.Nat
open import Data.Vec

private
    variable
        a : Level
        A : Set a

len : {n : ℕ} -> Vec A n -> ℕ
len {n = n} _ = n
