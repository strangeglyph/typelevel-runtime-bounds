module Leq where

open import Level using (Level)
open import Data.Bool

private
    variable
        a : Level
        A : Set a

-- Less or equal then comparison type
record Leq (A : Set a) : Set a where
    field leq : A -> A -> Bool


_<=_ : {{_ : Leq A}} -> A -> A -> Bool
_<=_ {{leqA}} x y = Leq.leq leqA x y
