module Trees.Plain where

open import Data.Nat hiding (_≤?_) renaming (_≡ᵇ_ to _==_)
open import Data.Nat.Properties hiding (_≤?_)
open import Data.Product
open import Level using (Level) renaming (suc to lsuc)
open import Function
open import Relation.Binary.PropositionalEquality

open import DecTree
open import NatProp


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

data _1?+⟨_⟩ (A : ℕ -> Set a) (n : ℕ) : Set a where
    +0 : (A n) -> A 1?+⟨ n ⟩
    +1 : (A (suc n)) -> A 1?+⟨ n ⟩

remove-min : {s h : ℕ} -> Tree A (suc s) (suc h) -> A × Tree A s 1?+⟨ h ⟩
remove-min (Fork Leaf x r) = x , +0 r
remove-min {h = h} (Fork l@(Fork _ _ _) x r) with remove-min l
...                                 | m , +1 l' = m , +1 (Fork l' x r)
...                                 | m , +0 l' with ≤-total (height l') (height r)
...                                            | inj₁ _     = m , {!!}
...                                            | inj₂ _     = m , ?

merge : {s s' h h' : ℕ} -> Tree A s h -> Tree A s' h' -> Tree A (s + s') (h ⊔ h')
merge Leaf Leaf                               = Leaf
merge Leaf r@(Fork _ _ _)                     = r
merge {A = A} {h = h} l@(Fork _ _ _) Leaf     = subst (\s -> Tree A s h) (cong suc (sym $ +-identityʳ _)) l
merge {A = A} {h = h} {h' = h'} l@(Fork ll xₗ lr) r@(Fork rl xᵣ rr) = subst (\s -> Tree A s {!h ⊔ h'!}) (cong suc (a+1+b+c+d≡a+b+1+c+d _ _ _ _)) $ Fork ll xₗ (Fork (merge lr rl) xᵣ rr)

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
