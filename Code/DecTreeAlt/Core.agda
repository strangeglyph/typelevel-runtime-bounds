module DecTreeAlt.Core where

open import Level using (Level)
open import Data.Nat hiding (_≤?_)
open import Data.Bool hiding (_≤_ ; _≤?_ ; _<_)

open import Leq

private
    variable
        a b : Level
        Compare : Set a
        Result : Set b


infix 5 if_≤?_then[_]_else[_]_


-- Decision tree parametrized by four types
-- * The type of variables being compared at each decision (-> Compare)
-- * The result type (-> B) indexed by
-- * The index type (-> Idx)
-- The tree is indexed by its height which allows reasoning about algorithmic runtime
data DecTree (Compare : Set a) (B : Set b) : (height : ℕ) -> Set (Level.suc (a Level.⊔ b)) where
    -- Leaf of the decision tree, forming the base element of the fold
    return : ∀ {k} -> B -> DecTree Compare B k
    -- Decision node - compare two values, then evaluate one of two trees
    -- Note that the runtime bounds here assume that datatype arguments are evaluated by need only to avoid unfolding the
    --   entire tree instead of only the necessary branch for evaluation. Otherwise change the subtrees to \top -> Tree
    if_≤?_then[_]_else[_]_ : {h1 h2 h : ℕ} -> (compLeft compRight : Compare) -> h1 < h -> DecTree Compare B h1 -> h2 < h -> DecTree Compare B h2 -> DecTree Compare B h
    -- Monad transform of a decision tree
    chain : {B' : Set b} -> {h1 h2 h : ℕ} -> DecTree Compare B' h1 -> (B' -> DecTree Compare B h2) -> h1 + h2 ≤ h -> DecTree Compare B h


-- Give a decision tree a concrete comparision function and evaluate it
reduce :  {h : ℕ}
       -> {{_ : Leq Compare}}
       -> DecTree Compare Result h
       -> Result
reduce (return x) = x
reduce (if x ≤? y then[ _ ] left else[ _ ] right) with x <= y
...                 | true = reduce left
...                 | false = reduce right
reduce (chain tree transform _) = reduce (transform (reduce tree))
