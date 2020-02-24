module DecTree where

open import Level using (Level)
open import Data.Nat
open import Data.Bool
open import Category.Functor
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties

open import Sigma
open import Leq

private
    variable
        c i a r : Level
        Compare : Set c
        Idx : Set i
        Result : Idx -> Set r


infix 5 compare_,_yes>_no>_
infix 5 fork_,_combine-with_
infix 1 _<$>_
infix 1 _>>=_


-- Decision tree parametrized by four types
-- * The type of variables being compared at each decision (-> Compare)
-- * The result type (-> B) indexed by
-- * The index type (-> Idx)
-- The tree is indexed by its height which allows reasoning about algorithmic runtime
data DecTree (Compare : Set c) (Idx : Set i) (B : Idx -> Set r) : (height : ℕ) -> Set (Level.suc (c Level.⊔ i Level.⊔ r)) where
    -- Leaf of the decision tree, forming the base element of the fold
    Leaf : {n : Idx} -> B n -> DecTree Compare Idx B 0
    -- Insert an arbitrary delay into the computation. This is okay since the height of the tree is only an upper bound
    delay : {h d : ℕ} -> DecTree Compare Idx B h -> DecTree Compare Idx B (h + d)
    -- Decision node - compare two values, then evaluate one of two trees
    -- Note that the runtime bounds here assume that datatype arguments are evaluated by need only to avoid unfolding the
    --   entire tree instead of only the necessary branch for evaluation. Otherwise change the subtrees to \top -> Tree
    compare_,_yes>_no>_ : {h1 h2 : ℕ} -> (compLeft compRight : Compare) -> DecTree Compare Idx B h1 -> DecTree Compare Idx B h2 -> DecTree Compare Idx B (1 + (h1 ⊔ h2))
    -- Functor transform of a decision tree
    _<$>_ : {Idx' : Set i} -> {B' : Idx' -> Set r} -> {h1 : ℕ} -> ({n : Idx'} -> B' n -> Σ Idx B) -> DecTree Compare Idx' B' h1 -> DecTree Compare Idx B h1
    -- Monad transform of a decision tree
    _>>=_ : {Idx' : Set i} -> {B' : Idx' -> Set r} -> {h1 h2 : ℕ} -> DecTree Compare Idx' B' h1 -> ({n : Idx'} -> B' n -> DecTree Compare Idx B h2) -> DecTree Compare Idx B (h1 + h2)


_<&>_ :  {Compare : Set c} -> {Idx Idx' : Set i} -> {B : Idx -> Set r} -> {B' : Idx' -> Set r} -> {h1 : ℕ}
      -> DecTree Compare Idx' B' h1
      -> ({n : Idx'} -> B' n -> Σ Idx B)
      -> DecTree Compare Idx B h1
t <&> f = f <$> t

fork_,_combine-with_ : {h1 h2 : ℕ} -> DecTree Compare Idx Result h1 -> DecTree Compare Idx Result h2 -> ({n1 n2 : Idx} -> Result n1 -> Result n2 -> Σ Idx Result) -> DecTree Compare Idx Result (h1 + h2)
fork left , right combine-with f = left >>= λ lr -> right <&> λ { rr -> f lr rr }

delay' : {h d : ℕ} -> DecTree Compare Idx Result h -> DecTree Compare Idx Result (d + h)
delay' {Compare = Compare} {Idx = Idx} {Result = Result} {h = h} {d = d} tree =
       subst (DecTree Compare Idx Result) (+-comm h d) (delay tree)

-- Give a decision tree a concrete comparision function and evaluate it
reduce :  {h : ℕ}
       -> {{_ : Leq Compare}}
       -> DecTree Compare Idx Result h
       -> Σ Idx Result
reduce (Leaf x) = σ x
reduce (delay x) = reduce x
reduce (compare x , y
        yes> left
        no>  right) with x <= y
...                 | true = reduce left
...                 | false = reduce right
reduce (transform <$> tree) = transform (Σ.val (reduce tree))
reduce (tree >>= transform) = reduce (transform (Σ.val (reduce tree)))

{-
data Constrained {Idx : Set i} (Result : Idx -> Set r) (Constraint : {n : Idx} -> Result n -> Set r) : Idx -> Set (Level.suc (i Level.⊔ r)) where
    constr : {n : Idx} -> (value : Result n) -> Constraint value -> Constrained Result Constraint n
-}

data Constrained {Idx : Set i} (Result : Idx -> Set r) (Constraint : {n : Idx} -> Result n -> Set) : Idx -> Set (i Level.⊔ r) where
    constr : {n : Idx} -> (value : Result n) -> Constraint value -> Constrained Result Constraint n
