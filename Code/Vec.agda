module Vec where

open import Level using (Level ; Lift ; lift) renaming (suc to lsuc)
open import Data.Vec hiding (insert; _>>=_)
open import Data.Nat hiding (_≤?_)
open import Data.Nat.Properties hiding (_≤?_)
open import Data.Nat.Induction
open import Data.Product using (_,_; _×_)
open import Data.Sum.Base
open import Data.Fin using (Fin) renaming (zero to fzero ; suc to fsuc)
import Data.Fin.Properties
open import Data.Maybe hiding (_>>=_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Induction.WellFounded using (Acc)
open import Data.Nat.Induction using (<-wellFounded)

open import DecTree
open import Util
open import Nat.Log
open import Nat.Base
open import Nat.Props

private
    variable
        a : Level
        A : Set a

-- -- Vector-based specializations of DecTree -- --

VecTree : Set a -> ℕ -> ℕ -> Set (lsuc a)
VecTree A l h = DecTree A (Vec A l) h

-- -- Algorithms -- --


-- Insert a value into a sorted vector
insert : {n : ℕ} -> A -> Vec A n -> VecTree A (suc n) n
insert k [] = return [ k ]
insert k (x ∷ xs) = if k ≤? x
                    then return (k ∷ x ∷ xs)
                    else (x ∷_ <$> insert k xs)



-- Merge two sorted vectors
merge : {m n : ℕ} -> Vec A n -> Vec A m -> VecTree A (n + m) (n + m)
merge [] ys = delay (len ys) (return ys)
merge {A = A} {n = suc n} (x ∷ xs) [] = delay' (suc n) (return (x ∷ (subst (Vec A) (sym $ +-identityʳ n) xs)))
merge {A = A} {m = suc m'} {n = suc n'} (x ∷ xs) (y ∷ ys) = subst (VecTree A (n + m)) (cong suc ⊔-idem-suc-xy) (
                           if[ Vec A ] x ≤? y
                           then (x ∷_ <$> merge xs (y ∷ ys))
                           else (y ∷_ <$> merge (x ∷ xs) ys) by (cong suc $ sym $ +-suc n' m'))
   where
     m : ℕ
     m = suc m'
     n : ℕ
     n = suc n'




pivot-constr : ℕ -> {l₁ l₂ : ℕ} -> Vec A l₁ × Vec A l₂ -> Set
pivot-constr l {l₁} {l₂} _ = l₁ + l₂ ≡ l

record SplitVec (A : Set a) (l : ℕ) : Set a where
    constructor _,_by_
    field
        {l₁ l₂} : ℕ
        left : Vec A l₁
        right : Vec A l₂
        proof : l₁ + l₂ ≡ l


PivotTree : (A : Set a) -> (l h : ℕ) -> Set (lsuc a)
PivotTree A l h = DecTree A (SplitVec A l) h

pivot-append-l : {l : ℕ} -> A -> SplitVec A l -> SplitVec A (suc l)
pivot-append-l x (left , right by pf) = (x ∷ left) , right by cong suc pf

pivot-append-r : {l : ℕ} -> A -> SplitVec A l -> SplitVec A (suc l)
pivot-append-r x (left , right by pf) = left , x ∷ right by trans (+-suc (len left) (len right)) (cong suc pf)


-- Split a vector into values smaller and larger than a pivot element
split-pivot : {l : ℕ}-> A -> Vec A l -> PivotTree A l l
split-pivot _ [] = return $ [] , [] by refl
split-pivot {A = A} {l = suc l'} k (x ∷ xs) =  subst (PivotTree A (suc l')) (⊔-idem (suc l')) (
                             if x ≤? k
                             then (pivot-append-l x <$> split-pivot k xs)
                             else (pivot-append-r x <$> split-pivot k xs))


-- Sort a vector using merge sort
quick-sort : {l : ℕ} -> Vec A l -> VecTree A l (l * l)
quick-sort {l = l} xs = quick-sort-step xs (<-wellFounded l)
    where
      quick-sort-step : {l : ℕ} -> Vec A l -> Acc _<_ l -> VecTree A l (l * l)
      quick-sort-step [] _ = return []
      quick-sort-step (x ∷ []) _ = delay 1 (return [ x ])
      quick-sort-step {A = A} {l = suc l} (x ∷ xs@(y ∷ _)) (Acc.acc rs) = delay' 1 (split-pivot x xs >>= recurse)
        where
            recurse : SplitVec A l -> VecTree A (suc l) (l * suc l)
            recurse split@(left , right by pf) =
                height-≡ (cong (λ x -> x * suc x) pf) $
                height-≡ (sym (*-suc (l₁ + l₂) (l₁ + l₂))) $
                delay' (l₁ + l₂) $
                    height-≡ (sym (binom-identity l₁ l₂)) $
                    delay (2 * l₁ * l₂) $
                            quick-sort-step left (rs l₁ (s≤s (m≤m+n≡k pf)))
                        >>= λ (l : Vec A l₁) -> quick-sort-step right (rs l₂ (s≤s (n≤m+n≡k pf)))
                        <&> λ (r : Vec A l₂) -> subst (Vec A) (trans (+-suc l₁ l₂) (cong suc pf)) $ l ++ x ∷ r
                where
                    l₁ : ℕ
                    l₁ = SplitVec.l₁ split
                    l₂ : ℕ
                    l₂ = SplitVec.l₂ split



take-min : {n : ℕ} -> A -> Vec A n -> DecTree A (A × Vec A n) n
take-min x [] = return $ x , []
take-min x (y ∷ ys) = if' x ≤? y
                 then (take-min x ys <&> λ (e , rs) -> e , y ∷ rs)
                 else (take-min y ys <&> λ (e , rs) -> e , x ∷ rs)


selection-sort : {n : ℕ} -> Vec A n -> VecTree A n (n * n)
selection-sort [] = return []
selection-sort (x ∷ xs) = delay' 1 $ take-min x xs >>= λ (e , rs) -> e ∷_ <$> recurse rs
  where
    recurse : {n : ℕ} -> Vec A n -> VecTree A n (n * suc n)
    recurse {A = A} {n = n} xs = subst (VecTree A n) (sym $ *-suc n n) $ delay' n $ selection-sort xs




merge-sort-step : {l : ℕ} -> Vec A l -> Acc _<_ l -> VecTree A l (l * ⌈log₂ l ⌉)
merge-sort-step [] _ = return []
merge-sort-step (x ∷ []) _ = return [ x ]
merge-sort-step {A = A} {l = l} xs@(_ ∷ _ ∷ _) (Acc.acc more) = Data.Product.uncurry recurse $ split xs
     where
         recurse : Vec A ⌈ l /2⌉ -> Vec A ⌊ l /2⌋ -> VecTree A l (l * ⌈log₂ l ⌉)
         recurse left right =
                   subst (λ x -> VecTree A x (l * ⌈log₂ l ⌉)) (⌈n/2⌉+⌊n/2⌋≡n l) $
                   delay-≤ (log₂n/2-bound _) $
                           merge-sort-step left (more ⌈ l /2⌉ (n>1⇒⌈n/2⌉<n _)) >>=
                   λ lr -> merge-sort-step right (more ⌊ l /2⌋ (n>0⇒⌊n/2⌋<n _))>>=
                   λ rr -> merge lr rr

merge-sort : {l : ℕ} -> Vec A l -> VecTree A l (l * ⌈log₂ l ⌉)
merge-sort {l = l} xs = merge-sort-step xs $ <-wellFounded l



find : {l : ℕ} -> Vec A l -> A -> DecTree A (Maybe $ Fin l) (2 * l)
find [] _ = return nothing
find {l = suc l-1} (x ∷ xs) e =
                  height-≡ (sym $ +-suc  (suc l-1) (l-1 + 0)) $
                  if' x ≤? e
                  then if e ≤? x
                       then return (just $ Fin.zero)
                       else (find xs e <&> λ res -> Data.Maybe.map (Fin.suc) res)
                  else (delay' 1 $ find xs e <&> λ res -> Data.Maybe.map (Fin.suc) res)

removeElem : {l : ℕ} -> Vec A l -> A -> DecTree A (Vec A ⟨ l ⟩-1?) (2 * l)
removeElem [] _ = return $ neutral []
removeElem {l = suc l-1} (x ∷ xs) e =
                  height-≡ (sym $ +-suc (suc l-1) (l-1 + 0)) $
                  if' x ≤? e
                  then if e ≤? x
                       then return $ decrement xs
                       else (x ∷'_ <$> removeElem xs e)
                  else (delay' 1 $ x ∷'_ <$> removeElem xs e)
    where
        _∷'_ : {l : ℕ} ->  A -> Vec A ⟨ l ⟩-1? -> Vec A ⟨ suc l ⟩-1?
        x ∷' (neutral xs) = neutral $ x ∷ xs
        x ∷' (decrement xs) = decrement $ x ∷ xs



_,_⊔'_,_ : {n : ℕ} -> Fin n -> A -> Fin n -> A -> DecTree A (Fin n × A) 1
i₁ , a ⊔' i₂ , b = if a ≤? b then return (i₂ , b) else return (i₁ , a)

_,_⊓'_,_ : {n : ℕ} -> Fin n -> A -> Fin n -> A -> DecTree A (Fin n × A) 1
i₁ , a ⊓' i₂ , b = if a ≤? b then return (i₁ , a) else return (i₂ , b)

f0 : ∀ {n} -> Fin (suc n)
f0 = fzero
f1 : ∀ {n} -> Fin (suc $ suc n)
f1 = fsuc f0
f2 : ∀ {n} -> Fin (suc $ suc $ suc n)
f2 = fsuc f1
f3 : ∀ {n} -> Fin (suc $ suc $ suc $ suc n)
f3 = fsuc f2
f4 : ∀ {n} -> Fin (suc $ suc $ suc $ suc $ suc n)
f4 = fsuc f3
f5 : ∀ {n} -> Fin (suc $ suc $ suc $ suc $ suc $ suc n)
f5 = fsuc f4

median2 : A -> A -> DecTree A (Fin 2 × A) 1
median2 a b = f0 , a ⊓' f1 , b

median3 : A -> A -> A -> DecTree A (Fin 3 × A) 4
median3 a b c = do
        fₓ₁ , x₁ <- f1 , b ⊓' f2 , c
        fₓ₂ , x₂ <- f0 , a ⊔' fₓ₁ , x₁
        fₓ₃ , x₃ <- f1 , b ⊔' f2 , c
        fₓ₂ , x₂ ⊓' fₓ₃ , x₃

median4 : A -> A -> A -> A -> DecTree A (Fin 4 × A) 7
median4 a b c d = do
        f₁ , ab⊓ <- f0 , a ⊓' f1 , b
        f₂ , ab⊔ <- f0 , a ⊔' f1 , b
        f₃ , cd⊓ <- f2 , c ⊓' f3 , d
        f₄ , cd⊔ <- f2 , c ⊔' f3 , d
        f₅ , x₁ <- f₁ , ab⊓ ⊔' f₃ , cd⊓
        f₆ , x₂ <- f₂ , ab⊔ ⊓' f₄ , cd⊔
        f₅ , x₁ ⊓' f₆ , x₂

median5 : A -> A -> A -> A -> A -> DecTree A (Fin 5 × A) 10
median5 a b c d e = do
        f₁ , ab⊓ <- f0 , a ⊓' f1 , b
        f₂ , ab⊔ <- f0 , a ⊔' f1 , b
        f₃ , cd⊓ <- f2 , c ⊓' f3 , d
        f₄ , cd⊔ <- f2 , c ⊔' f3 , d
        f₅ , not-the-biggest <- f₁ , ab⊓ ⊔' f₃ , cd⊓
        f₆ , not-the-smallest <- f₂ , ab⊔ ⊓' f₄ , cd⊔
        r <- median3 not-the-biggest not-the-smallest e
        case r of λ where
            (fzero , x)             -> return $ f₅ , x
            (fsuc fzero , x)        -> return $ f₆ , x
            (fsuc (fsuc fzero) , x) -> return $ f4 , x

medians-of-5 : {l : ℕ} -> Vec A l -> DecTree A (Vec (Fin l × A) ⌈ l /5⌉) (2 * l)
medians-of-5 []                       = return []
medians-of-5 (a ∷ [])                 = delay 2 $ return [ (f0 , a) ]
medians-of-5 (a ∷ b ∷ [])             = delay 3 $ (median2 a b <&> [_])
medians-of-5 (a ∷ b ∷ c ∷ [])         = delay 2 $ (median3 a b c <&> [_])
medians-of-5 (a ∷ b ∷ c ∷ d ∷ [])     = delay 1 $ (median4 a b c d <&> [_])
medians-of-5 (a ∷ b ∷ c ∷ d ∷ e ∷ xs) = let n = len xs in
                                        height-≡ (sym $ *-distribˡ-+ 2 5 n) $
                                        height-≡ (cong (10 +_) $ +-identityʳ (n + (n + 0))) $ do
                                        i , m <- median5 a b c d e
                                        ms <- medians-of-5 xs
                                        return $ (Data.Fin.inject≤ i (5≤5+n _) , m) ∷ (Data.Vec.map inc-idx ms)
    where
        5≤5+n : ∀ n -> 5 ≤ 5 + n
        5≤5+n _ = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))
        inc-idx : ∀ {n} -> Fin n × A -> Fin (5 + n) × A
        inc-idx = Data.Product.map₁ (Data.Fin._+_ $ f5 {6})

ordselect : {l : ℕ} -> (i : Fin $ suc l) -> (xs : Vec A $ suc l) -> DecTree A (Fin (suc l) × A) (10 * suc l)
median-by : {l : ℕ} {X A : Set a} -> (X -> A) -> Vec X (suc l) -> DecTree A (Fin (suc l) × X) (10 * suc l)

median-by _ (a ∷ [])                       = delay 10 $ return $ f0 , a
median-by f xs@(a ∷ b ∷ [])                = delay 19 (do i , m <- median2 (f a) (f b) ; return $ i , lookup xs i)
median-by f xs@(a ∷ b ∷ c ∷ [])            = delay 26 (do i , m <- median3 (f a) (f b) (f c) ; return $ i , lookup xs i)
median-by f xs@(a ∷ b ∷ c ∷ d ∷ [])        = delay 33 (do i , m <- median4 (f a) (f b) (f c) (f d) ; return $ i , lookup xs i)
median-by f xs@(a ∷ b ∷ c ∷ d ∷ e ∷ [])    = delay 40 (do i , m <- median5 (f a) (f b) (f c) (f d) (f e) ; return $ i , lookup xs i)
median-by {l = l} {A = A} f xs@(_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _ ∷ _) = select-median <&> λ (i , _) -> _,_ i (lookup xs i)
    where
        ix : Fin (len xs)
        ix = Data.Fin.fromℕ< {m = ⌊ len xs /2⌋} (n>0⇒⌊n/2⌋<n _)
        select-median : DecTree A (Fin (suc l) × A) (10 * suc l)
        select-median = ordselect ix $ Data.Vec.map f xs

median : {l : ℕ} -> Vec A (suc l) -> DecTree A (Fin (suc l) × A) (10 * suc l)
median = median-by id

ordselect {l = l-1} i xs = height-≡ {!!} $ do
        ms <- medians-of-5 xs
        _ , (iₚ , pivot) <- median-by Data.Product.proj₂ (subst (Vec _) (Data.Product.proj₂ $ ⌈1+n/5⌉>0 l-1) ms)
        let xs' = remove xs iₚ
        smaller , larger by split-length-≡ <- split-pivot pivot xs'
        case ord (iℕ) (len smaller) of λ where
            (lt pf) -> do
                let Diff k by suc≡l₁ = diff pf
                let smaller' = subst (Vec _) (sym suc≡l₁) smaller
                i , r <- ordselect {!!} smaller'
                {!!}
            (eq pf) -> delay-≤ z≤n $ return $ iₚ , pivot
            (gt pf) -> {!!}
        {-}{!do
        ms <- medians-of-5 xs
        _ , (iₚ , pivot) <- median-by Data.Product.proj₂ xs
        let xs' = remove xs iₚ
        smaller , larger by split-length-≡ <- split-pivot pivot {!xs'!}
        case ord (iℕ) (len smaller) of λ where
            (lt pf) -> {!ordselect {!!} {!smaller!}!}
            (eq pf) -> delay-≤ z≤n $ return iₚ , pivot
            (gt pf) -> ordselect (idx> pf {!cong suc $ split-length-≡!}) {!larger!}!}-}
    where
        l : ℕ
        l = suc l-1
        iℕ : ℕ
        iℕ = Data.Fin.toℕ i
        idx> : ∀ {x y} -> x < iℕ -> suc (x + y) ≡ l -> Fin y
        idx> {x = x} gtX eqL = let i' = Data.Fin.cast (sym $ eqL) i in
                              let gtX' = subst (x <_) (sym $ Data.Fin.Properties.toℕ-cast (sym eqL) i) gtX in
                              Data.Fin.reduce≥ {m = suc x} i' gtX'
