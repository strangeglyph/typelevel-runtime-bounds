module DecTree where

open import Level using (Level)
open import Data.Nat
open import Data.Bool
open import Category.Functor
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open import Function

open import Leq

private
    variable
        a b : Level
        Compare : Set a
        Result : Set b


infix 5 compare_,_yes>_no>_
infix 1 _<$>_
infix 1 _>>=_


-- Decision tree parametrized by four types
-- * The type of variables being compared at each decision (-> Compare)
-- * The result type (-> B) indexed by
-- * The index type (-> Idx)
-- The tree is indexed by its height which allows reasoning about algorithmic runtime
data DecTree (Compare : Set a) (B : Set b) : (height : ℕ) -> Set (Level.suc (a Level.⊔ b)) where
    -- Leaf of the decision tree, forming the base element of the fold
    Leaf : B -> DecTree Compare B 0
    -- Insert an arbitrary delay into the computation. This is okay since the height of the tree is only an upper bound
    delay : {h d : ℕ} -> DecTree Compare B h -> DecTree Compare B (h + d)
    -- Decision node - compare two values, then evaluate one of two trees
    -- Note that the runtime bounds here assume that datatype arguments are evaluated by need only to avoid unfolding the
    --   entire tree instead of only the necessary branch for evaluation. Otherwise change the subtrees to \top -> Tree
    compare_,_yes>_no>_ : {h1 h2 : ℕ} -> (compLeft compRight : Compare) -> DecTree Compare B h1 -> DecTree Compare B h2 -> DecTree Compare B (1 + (h1 ⊔ h2))
    -- Functor transform of a decision tree
--    _<$>_ : {B' : Set b} -> {h1 : ℕ} -> (B' -> B) -> DecTree Compare B' h1 -> DecTree Compare B h1
    -- Monad transform of a decision tree
    _>>=_ : {B' : Set b} -> {h1 h2 : ℕ} -> DecTree Compare B' h1 -> (B' -> DecTree Compare B h2) -> DecTree Compare B (h1 + h2)


_<$>_ : {R R' : Set b} -> {h : ℕ} -> (R' -> R) -> DecTree Compare R' h -> DecTree Compare R h
_<$>_ {Compare = C} {R = R} {h = h} f t = subst (DecTree C R) (+-identityʳ h) $ t >>= λ r -> Leaf $ f r

_<&>_ :  {Compare : Set a} -> {B B' : Set b} -> {h1 : ℕ}
      -> DecTree Compare B' h1
      -> (B' -> B)
      -> DecTree Compare B h1
t <&> f = f <$> t


delay' : {h d : ℕ} -> DecTree Compare Result h -> DecTree Compare Result (d + h)
delay' {Compare = Compare} {Result = Result} {h = h} {d = d} tree =
       subst (DecTree Compare Result) (+-comm h d) (delay tree)


if[_]_≤?_then_else_by_ : ∀ {l} {Idx : Set l} -> {i₁ i₂ : Idx} -> (Result : Idx -> Set b) -> {h₁ h₂ : ℕ} -> Compare -> Compare -> DecTree Compare (Result i₁) h₁ -> DecTree Compare (Result i₂) h₂ -> i₂ ≡ i₁ -> DecTree Compare (Result i₁) (1 + (h₁ ⊔ h₂))
if[_]_≤?_then_else_by_ {Compare = C} R {h₂ = h} a b left right proof =
                    compare a , b
                    yes> left
                    no>  subst (λ i -> DecTree C (R i) h) proof right


if'_≤?_then_else_ : {h : ℕ} -> (x y : Compare) -> (left right : DecTree Compare Result h) -> DecTree Compare Result (suc h)
if'_≤?_then_else_ {Compare = C} {Result = R} {h = h} x y left right = subst (DecTree C R) (cong suc $ ⊔-idem h) (compare x , y yes> left no> right)

-- Give a decision tree a concrete comparision function and evaluate it
reduce :  {h : ℕ}
       -> {{_ : Leq Compare}}
       -> DecTree Compare Result h
       -> Result
reduce (Leaf x) = x
reduce (delay x) = reduce x
reduce (compare x , y
        yes> left
        no>  right) with x <= y
...                 | true = reduce left
...                 | false = reduce right
--reduce (transform <$> tree) = transform (reduce tree)
reduce (tree >>= transform) = reduce (transform (reduce tree))


data Constrained (Result : Set b) (Constraint : Result -> Set) : Set b where
    constr : (value : Result) -> Constraint value -> Constrained Result Constraint
