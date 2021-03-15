module DecTree.Core where

open import Level using (Level)
open import Data.Nat hiding (_≤?_)
open import Data.Bool hiding (_≤_ ; _≤?_)

open import Leq

private
    variable
        a b : Level
        Compare : Set a
        Result : Set b


infix 5 if_≤?_then_else_
infix 1 _>>=_


-- Decision tree parametrized by four types
-- * The type of variables being compared at each decision (-> Compare)
-- * The result type (-> B) indexed by
-- * The index type (-> Idx)
-- The tree is indexed by its height which allows reasoning about algorithmic runtime
data DecTree (Compare : Set a) (B : Set b) : (height : ℕ) -> Set (Level.suc (a Level.⊔ b)) where
    -- Leaf of the decision tree, forming the base element of the fold
    return : B -> DecTree Compare B 0
    -- Insert an one-step delay into the computation. This is okay since the height of the tree is only an upper bound
    delay1 : {h : ℕ} -> DecTree Compare B h -> DecTree Compare B (suc h)
    -- Decision node - compare two values, then evaluate one of two trees
    -- Note that the runtime bounds here assume that datatype arguments are evaluated by need only to avoid unfolding the
    --   entire tree instead of only the necessary branch for evaluation. Otherwise change the subtrees to \top -> Tree
    if_≤?_then_else_ : {h1 h2 : ℕ} -> (compLeft compRight : Compare) -> DecTree Compare B h1 -> DecTree Compare B h2 -> DecTree Compare B (1 + (h1 ⊔ h2))
    -- Monad transform of a decision tree
    _>>=_ : {B' : Set b} -> {h1 h2 : ℕ} -> DecTree Compare B' h1 -> (B' -> DecTree Compare B h2) -> DecTree Compare B (h2 + h1)


-- Give a decision tree a concrete comparision function and evaluate it
reduce :  {h : ℕ}
       -> {{_ : Leq Compare}}
       -> DecTree Compare Result h
       -> Result
reduce (return x) = x
reduce (delay1 x) = reduce x
reduce (if x ≤? y then left else right) with x <= y
...                 | true = reduce left
...                 | false = reduce right
reduce (tree >>= transform) = reduce (transform (reduce tree))
