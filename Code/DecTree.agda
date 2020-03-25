module DecTree where

open import Level using (Level)
open import Data.Nat hiding (_≤?_)
open import Data.Bool hiding (_≤_ ; _≤?_)
open import Category.Functor
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties hiding (_≤?_)
open import Function

open import Leq
open import Nat.Props

private
    variable
        a b : Level
        Compare : Set a
        Result : Set b


infix 5 if_≤?_then_else_
infix 1 _<$>_
infix 1 _>>=_


-- Decision tree parametrized by four types
-- * The type of variables being compared at each decision (-> Compare)
-- * The result type (-> B) indexed by
-- * The index type (-> Idx)
-- The tree is indexed by its height which allows reasoning about algorithmic runtime
data DecTree (Compare : Set a) (B : Set b) : (height : ℕ) -> Set (Level.suc (a Level.⊔ b)) where
    -- Leaf of the decision tree, forming the base element of the fold
    return : B -> DecTree Compare B 0
    -- Insert an arbitrary delay into the computation. This is okay since the height of the tree is only an upper bound
    delay : {h : ℕ} -> (d : ℕ) -> DecTree Compare B h -> DecTree Compare B (h + d)
    -- Decision node - compare two values, then evaluate one of two trees
    -- Note that the runtime bounds here assume that datatype arguments are evaluated by need only to avoid unfolding the
    --   entire tree instead of only the necessary branch for evaluation. Otherwise change the subtrees to \top -> Tree
    if_≤?_then_else_ : {h1 h2 : ℕ} -> (compLeft compRight : Compare) -> DecTree Compare B h1 -> DecTree Compare B h2 -> DecTree Compare B (1 + (h1 ⊔ h2))
    -- Monad transform of a decision tree
    _>>=_ : {B' : Set b} -> {h1 h2 : ℕ} -> DecTree Compare B' h1 -> (B' -> DecTree Compare B h2) -> DecTree Compare B (h1 + h2)


height-≡ : {h h' : ℕ} -> h ≡ h' -> DecTree Compare Result h -> DecTree Compare Result h'
height-≡ {Compare = Compare} {Result = Result} pf = subst (DecTree Compare Result) pf





_<$>_ : {R R' : Set b} -> {h : ℕ} -> (R' -> R) -> DecTree Compare R' h -> DecTree Compare R h
_<$>_ {h = h} f t = height-≡ (+-identityʳ h) $ t >>= λ r -> return $ f r

_<&>_ : {R R' : Set b} -> {h : ℕ} -> DecTree Compare R' h -> (R' -> R) -> DecTree Compare R h
t <&> f = f <$> t


delay' : {h : ℕ} -> (d : ℕ) -> DecTree Compare Result h -> DecTree Compare Result (d + h)
delay' {h = h} d tree = height-≡ (+-comm h d) $ delay d tree


delay-≤ : {d d' : ℕ} -> d ≤ d' -> DecTree Compare Result d -> DecTree Compare Result d'
delay-≤ d≤d' tree = case diff d≤d' of λ (Diff n by pf) -> height-≡ pf $ delay n tree


if[_]_≤?_then_else_by_ : ∀ {l} {Idx : Set l} -> {i₁ i₂ : Idx} -> (Result : Idx -> Set b) -> {h₁ h₂ : ℕ} -> Compare -> Compare -> DecTree Compare (Result i₁) h₁ -> DecTree Compare (Result i₂) h₂ -> i₂ ≡ i₁ -> DecTree Compare (Result i₁) (1 + (h₁ ⊔ h₂))
if[_]_≤?_then_else_by_ {Compare = C} R {h₂ = h} a b left right proof =
                    if a ≤? b
                    then left
                    else subst (λ i -> DecTree C (R i) h) proof right


if'_≤?_then_else_ : {h : ℕ} -> (x y : Compare) -> (left right : DecTree Compare Result h) -> DecTree Compare Result (suc h)
if'_≤?_then_else_ {h = h} x y left right = height-≡ (cong suc $ ⊔-idem h) $ if x ≤? y then left else right

-- Give a decision tree a concrete comparision function and evaluate it
reduce :  {h : ℕ}
       -> {{_ : Leq Compare}}
       -> DecTree Compare Result h
       -> Result
reduce (return x) = x
reduce (delay _ x) = reduce x
reduce (if x ≤? y then left else right) with x <= y
...                 | true = reduce left
...                 | false = reduce right
reduce (tree >>= transform) = reduce (transform (reduce tree))


data Constrained (Result : Set b) (Constraint : Result -> Set) : Set b where
    constr : (value : Result) -> Constraint value -> Constrained Result Constraint
