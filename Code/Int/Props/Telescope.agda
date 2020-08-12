module Int.Props.Telescope where

open import Data.Integer
open import Data.Integer.Properties
open import Relation.Binary.PropositionalEquality
open import Function

+-telescope : ∀ x y z -> (x + z) + (y - z) ≡ x + y
+-telescope x y z = begin
        x + z + (y + - z)  ≡⟨ cong (λ v → x + z + v) $ +-comm y (- z) ⟩
        x + z + (- z + y)  ≡⟨ sym $ +-assoc (x + z) (- z) y ⟩
        x + z + - z + y    ≡⟨ cong (_+ y) $ +-assoc x z (- z) ⟩
        x + (z + - z) + y  ≡⟨ cong (λ v → x + v + y) $ m≡n⇒m-n≡0 z z refl ⟩
        x + 0ℤ + y         ≡⟨ cong (_+ y) $ +-identityʳ x ⟩
        x + y              ∎
    where
        open ≡-Reasoning
