module DecTree where

open import Level using (Level)
open import Data.Nat
open import Data.Bool

open import Sigma
open import Leq

private
    variable
        c i a r : Level
        Compare : Set c
        Idx : Set i
        Atomic : Set a
        Result : Atomic -> Set r


infix 5 compare_,_yes>_,_no>_,_

-- Decision tree parametrized by four types
-- * The type of variables being compared at each decision (-> Compare)
-- * The fold atomic type (-> A)
-- * The fold result type (-> B) indexed by
-- * The index type (-> Idx)
-- Additionally the fold function is also encoded in the tree
-- The tree is indexed by its height which allows reasoning about algorithmic runtime
data DecTree (Compare : Set c) (Idx : Set i) (A : Set a) (B : Idx -> Set r) (Fold : {n : Idx} -> A -> B n -> Σ Idx B) : (height : ℕ) -> Set (Level.suc (c Level.⊔ i Level.⊔ a Level.⊔ r)) where
    -- Leaf of the decision tree, forming the base element of the fold
    Leaf : {n : Idx} -> B n -> DecTree Compare Idx A B Fold 0
    -- As above, but with an arbitrary height. This is okay since the height of the tree is only an upper bound
    OverLeaf : {n : Idx} -> {h : ℕ} -> B n -> DecTree Compare Idx A B Fold h
    -- Decision node - compare two values, then give two paths to fold along
    -- Note that the runtime bounds here assume that datatype arguments are evaluated by need only to avoid unfolding the
    --   entire tree instead of only the necessary branch for evaluation. Otherwise change the subtrees to \top -> Tree
    compare_,_yes>_,_no>_,_ : {h1 h2 : ℕ} -> (compLeft compRight : Compare) -> (valLeft : A) -> DecTree Compare Idx A B Fold h1 -> (valRight : A) -> DecTree Compare Idx A B Fold h2 -> DecTree Compare Idx A B Fold (1 + (h1 ⊔ h2))
    Embed : {Idx' : Set i} -> {A' : Set a} -> {B' : Idx' -> Set r} -> (Fold' : {n : Idx'} -> A' -> B' n -> Σ Idx' B') -> {h1 h2 : ℕ} -> DecTree Compare Idx' A' B' Fold' h1 -> ({n : Idx'} -> B' n -> A) -> DecTree Compare Idx A B Fold h2 -> DecTree Compare Idx A B Fold (h1 + h2)



-- Give a decision tree a concrete comparision function and evaluate it
reduce :  {h : ℕ}
       -> {fold : {n : Idx} -> Atomic -> Result n -> Σ Idx Result}
       -> {{_ : Leq Compare}}
       -> DecTree Compare Idx Atomic Result fold h
       -> Σ Idx Result
reduce (Leaf x) = σ x
reduce (OverLeaf x) = σ x
reduce {fold = fold} (
        compare x , y
        yes> lVal , lTree
        no>  rVal , rTree) with x <= y
...                         | true = fold lVal (Σ.val (reduce lTree))
...                         | false = fold rVal (Σ.val (reduce rTree))
