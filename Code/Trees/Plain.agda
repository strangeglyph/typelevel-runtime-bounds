module Trees.Plain where

open import Data.Nat hiding (_≤?_) renaming (_≡ᵇ_ to _==_)
open import Data.Nat.Properties hiding (_≤?_)
open import Data.Product
open import Data.Sum
open import Level using (Level) renaming (suc to lsuc)
open import Function
open import Relation.Binary.PropositionalEquality

open import DecTree
open import NatProp
open import Util


private
    variable
        a : Level
        A : Set a

data Tree (A : Set a) : ℕ -> ℕ -> Set a where
    Leaf : Tree A 0 0
    Fork : {s₁ s₂ h₁ h₂ : ℕ} -> Tree A s₁ h₁ -> A -> Tree A s₂ h₂ -> Tree A (1 + s₁ + s₂) (1 + (h₁ ⊔ h₂))


size : {s h : ℕ} -> Tree A s h -> ℕ
size {s = s} _ = s

height : {s h : ℕ} -> Tree A s h -> ℕ
height {h = h} _ = h

TreeTree : Set a -> ℕ -> ℕ -> Set (lsuc a)
TreeTree A s l = DecTree A (Σ ℕ $ Tree A s) l

insert : {s h : ℕ} -> Tree A s h -> A -> TreeTree A (1 + s) s
insert Leaf x = return $ -, Fork Leaf x Leaf
insert {A = A} (Fork l x r) y =
                    if' y ≤? x
                    then (delay-≤ (m≤m+n _ _) $ insert l y <&> λ σ -> let l' = Σ.proj₂ σ in -, Fork l' x r)
                    else (delay-≤ (m≤n+m _ _) $ insert r y <&> λ σ -> let r' = Σ.proj₂ σ in +-suc-t $ -, Fork l x r')
    where
        s₁ s₂ : ℕ
        s₁ = size l
        s₂ = size r
        +-suc-t : Σ ℕ (Tree A (1 + s₁ + (1 + s₂))) -> Σ ℕ (Tree A (2 + s₁ + s₂))
        +-suc-t = subst (λ s -> Σ ℕ (Tree A s)) (cong suc $ +-suc s₁ s₂)


tree-⊔-max-< : {s h₁ h₂ : ℕ} -> Tree A s (suc (h₁ ⊔ h₂)) -> suc h₁ < h₂ -> Tree A s (suc (suc h₁ ⊔ h₂))
tree-⊔-max-< t pf = subst (Tree _ _) (cong suc $ ⊔-max-< $ ≤⇒pred≤ pf) t

tree-⊔-max-≡ : {s h₁ h₂ : ℕ} -> Tree A s (suc (h₁ ⊔ h₂)) -> suc h₁ ≡ h₂ -> Tree A s (suc (suc h₁ ⊔ h₂))
tree-⊔-max-≡ t pf = subst (Tree _ _) (cong suc $ ⊔-max-≡ pf) t

tree-⊔-max-> : {s h₁ h₂ : ℕ} -> Tree A s (suc (h₁ ⊔ h₂)) -> h₂ < suc h₁ -> Tree A s (suc h₁ ⊔ h₂)
tree-⊔-max-> t pf = subst (Tree _ _) (⊔-max-> $ ≤-pred pf) t

tree-⊔-max-<ᵣ : ∀ {s h₁ h₂} -> Tree A s (suc (h₁ ⊔ h₂)) -> suc h₂ < h₁ -> Tree A s (suc (h₁ ⊔ suc h₂))
tree-⊔-max-<ᵣ t pf = subst (Tree _ _) (cong suc $ ⊔-max-<ᵣ $ ≤⇒pred≤ pf) t

tree₂-⊔-max-<ᵣ : ∀ {s₁ s₂ h₁ h₂} -> Tree A (suc (s₁ + s₂)) (suc (h₁ ⊔ h₂)) -> suc h₂ < h₁ -> Tree A (s₁ + suc s₂) (suc (h₁ ⊔ suc h₂))
tree₂-⊔-max-<ᵣ t pf = subst2 (Tree _) (sym $ +-suc _ _) (cong suc $ ⊔-max-<ᵣ $ ≤⇒pred≤ pf) t

tree-⊔-max-≡ᵣ : ∀ {s h₁ h₂} -> Tree A s (suc (h₁ ⊔ h₂)) -> h₁ ≡ suc h₂ -> Tree A s (suc (h₁ ⊔  suc h₂))
tree-⊔-max-≡ᵣ t pf = subst (Tree _ _) (cong suc $ ⊔-max-≡ᵣ pf) t

tree₂-⊔-max-≡ᵣ : ∀ {s₁ s₂ h₁ h₂} -> Tree A (suc (s₁ + s₂)) (suc (h₁ ⊔ h₂)) -> h₁ ≡ suc h₂ -> Tree A (s₁ + suc s₂) (suc (h₁ ⊔ suc h₂))
tree₂-⊔-max-≡ᵣ t pf = subst2 (Tree _) (sym $ +-suc _ _) (cong suc $ ⊔-max-≡ᵣ pf) t

tree-⊔-max->ᵣ : ∀ {s h₁ h₂} -> Tree A s (suc (h₁ ⊔ h₂)) -> h₁ < suc h₂ -> Tree A s (h₁ ⊔ suc h₂)
tree-⊔-max->ᵣ t pf = subst (Tree _ _) (⊔-max->ᵣ $ ≤-pred pf) t

tree₂-⊔-max->ᵣ : ∀ {s₁ s₂ h₁ h₂} -> Tree A (suc (s₁ + s₂)) (suc (h₁ ⊔ h₂)) -> h₁ < suc h₂ -> Tree A (s₁ + suc s₂) (h₁ ⊔ suc h₂)
tree₂-⊔-max->ᵣ t pf = subst2 (Tree _) (sym $ +-suc _ _) (⊔-max->ᵣ $ ≤-pred pf) t

remove-min : {s h : ℕ} -> Tree A (suc s) (suc h) -> A × Tree A s 1?+⟨ h ⟩
remove-min (Fork Leaf x r) = x , +0 r
remove-min {A = A} {s = s} (Fork l@(Fork _ _ _) x r) with remove-min l
...         | m , +1 l' = m , +1 (Fork l' x r)
...         | m , +0 l' with ord (height l) (height r)
...                 | lt pf = m , +1 (tree-⊔-max-< (Fork l' x r) pf)
...                 | eq pf = m , +1 (tree-⊔-max-≡ (Fork l' x r) pf)
...                 | gt pf = m , +0 (tree-⊔-max-> (Fork l' x r) pf)

remove-max : {s h : ℕ} -> Tree A (suc s) (suc h) -> A × Tree A s 1?+⟨ h ⟩
remove-max {A = A} {s = s} {h = h} (Fork l x Leaf) = x , +0 (subst2 (Tree A) (sym $ +-identityʳ _) (sym $ ⊔-identityʳ _) l)
remove-max {A = A} {s = s} {h = h} (Fork l x r@(Fork _ _ _)) with remove-max r
...         | m , +1 r' = m , +1 (subst (λ s -> Tree A s (suc h)) (sym $ +-suc _ _) $ Fork l x r')
...         | m , +0 r' with ord (height l) (height r)
...                 | lt pf = m , +0 (tree₂-⊔-max->ᵣ (Fork l x r') pf)
...                 | eq pf = m , +1 (tree₂-⊔-max-≡ᵣ (Fork l x r') pf)
...                 | gt pf = m , +1 (tree₂-⊔-max-<ᵣ (Fork l x r') pf)


merge : {s s' h h' : ℕ} -> Tree A s h -> Tree A s' h' -> Tree A (s + s') 1?+⟨ h ⊔ h' ⟩
merge Leaf r             = +0 r
merge l@(Fork ll x lr) r with remove-min l
...         | m , +1 l' = +1 $ Fork l' x r
...         | m , +0 l' with ord (height l) (height r)
...                 | lt pf = +1 $ tree-⊔-max-< (Fork l' x r) pf
...                 | eq pf = +1 $ tree-⊔-max-≡ (Fork l' x r) pf
...                 | gt pf = +0 $ tree-⊔-max-> (Fork l' x r) pf


RemovalTree : Set a -> ℕ -> ℕ -> Set a
RemovalTree A s h = _⟨_⟩-1? (λ s' -> Tree A s' ⟨ h ⟩-1?) s

remove : {s h : ℕ} -> Tree A s h -> A -> DecTree A (RemovalTree A s h) (2 * h)
remove Leaf val = return $ neutral $ neutral Leaf
remove {A = A} {s = s} {h = h} (Fork l x r) val =
                    height-≡ (sym $ 2*m≡m+m h) $
                    delay-≤ (s≤s $ ⊔-+-switch (height l) (height r)) $
                    if val ≤? x
                    then height-≡ (cong suc $ 2*m≡m+m $ height l) $
                         if' x ≤? val
                         then delay-≤ (z≤n) $ return $ remove-merge $ merge l r
                         else (remove l val <&> λ l' -> remove-join-l l' x r)
                    else (height-≡ (2*m≡m+m $ height r) $ remove r val <&> λ r' -> remove-join-r l x r')
    where
        h-1 : ℕ
        h-1 = height l ⊔ height r
        remove-merge : Tree A (size l + size r) 1?+⟨ height l ⊔ height r ⟩ -> RemovalTree A s h
        remove-merge (+0 t) = decrement $ decrement t
        remove-merge (+1 t) = decrement $ neutral t
        remove-join-l : RemovalTree A (size l) (height l) -> A -> Tree A (size r) (height r) -> RemovalTree A s h
        remove-join-l (neutral (neutral l')) x r = neutral $ neutral $ Fork l' x r
        remove-join-l (neutral (decrement l')) x r with ord (height l) (height r)
        ...         | lt pf = neutral $ neutral $ tree-⊔-max-< (Fork l' x r) pf
        ...         | eq pf = neutral $ neutral $ tree-⊔-max-≡ (Fork l' x r) pf
        ...         | gt pf = neutral $ decrement $ tree-⊔-max-> (Fork l' x r) pf
        remove-join-l (decrement (neutral l')) x r = decrement $ neutral $ Fork l' x r
        remove-join-l (decrement (decrement l')) x r with ord (height l) (height r)
        ...         | lt pf = decrement $ neutral $ tree-⊔-max-< (Fork l' x r) pf
        ...         | eq pf = decrement $ neutral $ tree-⊔-max-≡ (Fork l' x r) pf
        ...         | gt pf = decrement $ decrement $ tree-⊔-max-> (Fork l' x r) pf
        remove-join-r : Tree A (size l) (height l) -> A -> RemovalTree A (size r) (height r) -> RemovalTree A s h
        remove-join-r l x (neutral (neutral r')) = neutral $ neutral $ Fork l x r'
        remove-join-r l x (neutral (decrement r')) with ord (height l) (height r)
        ...         | lt pf = neutral $ decrement $ tree-⊔-max->ᵣ (Fork l x r') pf
        ...         | eq pf = neutral $ neutral $ tree-⊔-max-≡ᵣ (Fork l x r') pf
        ...         | gt pf = neutral $ neutral $ tree-⊔-max-<ᵣ (Fork l x r') pf
        remove-join-r l x (decrement (neutral r')) = decrement $ neutral $ subst (λ s -> Tree A s h) (sym $ +-suc _ _) $ Fork l x r'
        remove-join-r l x (decrement (decrement r')) with ord (height l) (height r)
        ...         | lt pf = decrement $ decrement $ tree₂-⊔-max->ᵣ (Fork l x r') pf
        ...         | eq pf = decrement $ neutral $ tree₂-⊔-max-≡ᵣ (Fork l x r') pf
        ...         | gt pf = decrement $ neutral $ tree₂-⊔-max-<ᵣ (Fork l x r') pf

{-
remove : {s h : ℕ} -> Tree A s h -> A -> DecTree A (Σ ℕ (λ s -> Σ ℕ (Tree A s))) {!!}
remove Leaf _ = return (-, (-, Leaf))
remove t@(Fork Leaf x Leaf) y =
                    height-≡ {!!} $
                    if' y ≤? x
                    then if' x ≤? y
                        then return (-, (-, Leaf))
                        else return (-, (-, t))
                    else (delay 1 $ return (-, (-, t)))
remove t@(Fork l@(Fork ll xₗ lr) x Leaf) y =
                    delay-≤ {!!} $
                    if y ≤? x
                    then if x ≤? y
                         then return (-, (-, l))
                         else (remove l y <&> λ l' -> -, (-, (Fork (Σ.proj₂ $ Σ.proj₂ l') x Leaf)))
                    else (return (-, (-, t)))
remove t@(Fork Leaf x r@(Fork rl xᵣ rr)) y =
                    delay-≤ {!!} $
                    if y ≤? x
                    then if' x ≤? y
                        then return (-, (-, r))
                        else return (-, (-, t))
                    else (remove r y <&> λ r' -> -, (-, (Fork Leaf x (Σ.proj₂ $ Σ.proj₂ r'))))
remove t@(Fork l@(Fork ll xₗ lr) x r@(Fork rl xᵣ rr)) y =
                    delay-≤ {!!} $
                    if' y ≤? x
                    then if' x ≤? y
                        then {!!}
                        else (remove l y <&> λ l' -> -, (-, (Fork (Σ.proj₂ $ Σ.proj₂ l') x r)))
                    else (remove r y <&> λ r' -> -, (-, (Fork l x (Σ.proj₂ $ Σ.proj₂ r'))))
-}
