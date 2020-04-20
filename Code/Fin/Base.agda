module Fin.Base where

open import Data.Nat
open import Data.Fin using (Fin ; Fin′ ; toℕ) renaming (zero to fzero ; suc to fsuc)
open import Function

fromℕ≤' : {n k : ℕ} -> (i : Fin n) -> k ≤ toℕ i -> Fin′ (fsuc i)
fromℕ≤' {_} {zero} _ _ = fzero
fromℕ≤' {_} {suc k} (fsuc i) (s≤s k≤i) = fsuc $ fromℕ≤' i k≤i
