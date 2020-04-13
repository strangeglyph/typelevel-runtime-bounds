module Vec where

open import Level using (Level ; Lift ; lift) renaming (suc to lsuc)
open import Data.Vec hiding (insert; _>>=_)
open import Data.Nat hiding (_≤?_)
open import Data.Nat.Properties hiding (_≤?_)
open import Data.Nat.Induction
open import Data.Nat.DivMod
open import Data.Nat.Divisibility
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
open import Fin.Props

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
split-pivot-by : {X A : Set a} -> {l : ℕ} -> (X -> A) -> X -> Vec X l -> DecTree A (SplitVec X l) l
split-pivot-by _ _ [] = return $ [] , [] by refl
split-pivot-by {A = A} {l = suc l'} f k (x ∷ xs) = if' f x ≤? f k
                                                   then (pivot-append-l x <$> split-pivot-by f k xs)
                                                   else (pivot-append-r x <$> split-pivot-by f k xs)

split-pivot : {l : ℕ} -> A -> Vec A l -> PivotTree A l l
split-pivot = split-pivot-by id

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


module Median where
    open import Data.Fin using (raise)
    private
        record Split (A : Set a) (l : ℕ) (b₁ b₂ : ℕ -> Set) : Set a where
            field
                median : Indexed A l
                {l₁ l₂ l₃} : ℕ
                smaller : Vec (Indexed A l) l₁
                larger : Vec (Indexed A l) l₂
                unknown : Vec (Indexed A l) l₃
                length-≡ : suc (l₁ + l₂ + l₃) ≡ l
                bound-smaller : b₁ l₁
                bound-larger : b₂ l₂

        M2 : Set a -> ℕ -> Set a
        M2 A l = Indexed A l × Indexed A l

        M3 : Set a -> ℕ -> Set a
        M3 A l = Indexed A l × Indexed A l × Indexed A l

        M4 : Set a -> ℕ -> Set a
        M4 A l = Indexed A l × Indexed A l × Indexed A l × Indexed A l

        M5 : Set a -> ℕ -> Set a
        M5 A l = Indexed A l × Indexed A l × Indexed A l × Indexed A l × Indexed A l

        data MX (A : Set a) (l : ℕ) : Set a where
            m1 : Indexed A l -> MX A l
            m2 : M2 A l -> MX A l
            m3 : M3 A l -> MX A l
            m4 : M4 A l -> MX A l


        median2-by : {X A : Set a} -> (X -> A) -> X -> X -> DecTree A (M2 X 2) 1
        median2-by {X = X} f x' y' =
                if f x' ≤? f y'
                then (return $ x , y)
                else (return $ y , x)
            where
                x y : Indexed X 2
                x = index f0 x'
                y = index f1 y'


        median3-by : {X A : Set a} -> (X -> A) -> X -> X -> X -> DecTree A (M3 X 3) 3
        median3-by {X = X} f x' y' z' =
                if f x' ≤? f y'
                then if f x' ≤? f z'
                    then if f y' ≤? f z'
                        then (return $ x , y , z)
                        else (return $ x , z , y)
                    else (return $ z , x , y)
                else if f y' ≤? f z'
                    then if f x' ≤? f z'
                        then (return $ y , x , z)
                        else (return $ y , z , x)
                    else (return $ z , y , x)
            where
                x y z : Indexed X 3
                x = index f0 x'
                y = index f1 y'
                z = index f2 z'

        median4-by : {X A : Set a} -> (X -> A) -> X -> X -> X -> X -> DecTree A (M4 X 4) 5
        median4-by {X = X} f w x y z =
                if f w ≤? f x
                then if f x ≤? f y
                    then if f x ≤? f z
                        then (return $ wI , xI , yI , zI)
                        else if f w ≤? f z
                            then (return $ wI , zI , xI , yI)
                            else (return $ zI , wI , xI , yI)
                    else if f w ≤? f y
                        then if f y ≤? f z
                            then (return $ wI , yI , zI , xI)
                            else if f w ≤? f z
                                    then (return $ wI , zI , yI , xI)
                                    else (return $ zI , wI , yI , xI)
                        else if f w ≤? f z
                            then (return $ yI , wI , zI , xI)
                            else if f y ≤? f z
                                    then (return $ yI , zI , wI , xI)
                                    else (return $ zI , yI , wI , xI)
                else if f w ≤? f y
                    then if f w ≤? f z
                        then (return $ xI , wI , zI , yI)
                        else if f x ≤? f z
                            then (return $ xI , zI , wI , yI)
                            else (return $ zI , xI , wI , yI)
                    else if f x ≤? f y
                        then if f y ≤? f z
                            then (return $ xI , yI , zI , wI)
                            else if f x ≤? f z
                                    then (return $ xI , zI , yI , wI)
                                    else (return $ zI , xI , yI , wI)
                        else if f x ≤? f z
                            then (return $ yI , xI , zI , wI)
                            else if f y ≤? f z
                                    then (return $ yI , zI , xI , wI)
                                    else (return $ zI , yI , xI , wI)

            where
                wI xI yI zI : Indexed X 4
                wI = index f0 w
                xI = index f1 x
                yI = index f2 y
                zI = index f3 y

        median5-by : {X A : Set a} -> (X -> A) -> X -> X -> X -> X -> X -> DecTree A (M5 X 5) 7
        median5-by {X = X} {A = A} f v w x y z =
                if f v ≤? f w
                then median5₁ (index f0 v) (index f1 w) (index f2 x) (index f3 y) (index f4 z)
                else median5₁ (index f1 w) (index f0 v) (index f2 x) (index f3 y) (index f4 z) -- swap v, w
            where
                median5₃ : Indexed X 5 -> Indexed X 5 -> Indexed X 5 -> Indexed X 5 -> Indexed X 5 -> DecTree A (M5 X 5) 4
                median5₃ vI@(index _ v) wI@(index _ w) xI@(index _ x) yI@(index _ y) zI@(index _ z) =
                    if f w ≤? f x
                    then if f w ≤? f z
                        then if f x ≤? f z
                            then (return $ vI , wI , xI , zI , yI)
                            else (return $ vI , wI , zI , xI , yI)
                        else (return $ vI , zI , wI , xI , yI)
                    else if f w ≤? f z
                        then (return $ vI , xI , wI , zI , yI)
                        else if f v ≤? f x
                            then if f x ≤? f z
                                then (return $ vI , xI , zI , wI , yI)
                                else (return $ vI , zI , xI , wI , yI)
                            else if f v ≤? f z
                                then (return $ xI , vI , zI , wI , yI)
                                else (return $ xI , zI , vI , wI , yI)
                median5₂ : Indexed X 5 -> Indexed X 5 -> Indexed X 5 -> Indexed X 5 -> Indexed X 5 -> DecTree A (M5 X 5) 5
                median5₂ vI wI@(index _ w) xI yI@(index _ y) zI =
                    if f w ≤? f y
                    then median5₃ vI wI xI yI zI
                    else median5₃ xI yI vI wI zI  -- swap (v w), (x y)
                median5₁ : Indexed X 5 -> Indexed X 5 -> Indexed X 5 -> Indexed X 5 -> Indexed X 5 -> DecTree A (M5 X 5) 6
                median5₁ vI wI xI@(index _ x) yI@(index _ y) zI =
                    if f x ≤? f y
                    then median5₂ vI wI xI yI zI
                    else median5₂ vI wI yI xI zI -- swap x, y


        inc-idx-m5 : ∀ {l} -> M5 A l -> M5 A (5 + l)
        inc-idx-m5 (a , b , c , d , e) = (raise-ix 5 a) , (raise-ix 5 b) , (raise-ix 5 c) , (raise-ix 5 d) , (raise-ix 5 e)

        inc-idx-mx : ∀ {l} -> MX A l -> MX A (5 + l)
        inc-idx-mx (m1 v)               = m1 $ raise-ix 5 v
        inc-idx-mx (m2 (a , b))         = m2 $ (raise-ix 5 a) , (raise-ix 5 b)
        inc-idx-mx (m3 (a , b , c))     = m3 $ (raise-ix 5 a) , (raise-ix 5 b) , (raise-ix 5 c)
        inc-idx-mx (m4 (a , b , c , d)) = m4 $ (raise-ix 5 a) , (raise-ix 5 b) , (raise-ix 5 c) , (raise-ix 5 d)

        lift-m5 : ∀ {l} -> M5 A 5 -> M5 A (5 + l)
        lift-m5 {l = l} (a , b , c , d , e) = subst (M5 _) (+-comm l 5) $ (inject-ix l a) , (inject-ix l b) , (inject-ix l c) , (inject-ix l d) , (inject-ix l e)


        data Medians-Of-5 (A : Set a) (l : ℕ) : Set a where
            medians : Vec (M5 A l) ⌊ l /5⌋ -> Vec (Indexed A l) (l % 5) -> Medians-Of-5 A l

        _:::_ : {l : ℕ} -> M5 A 5 -> Medians-Of-5 A l -> Medians-Of-5 A (5 + l)
        m5 ::: (medians ms overflow) = medians ((lift-m5 m5) ∷ (Data.Vec.map inc-idx-m5 ms)) (Data.Vec.map (raise-ix 5) overflow)


        medians-of-5-by : {X A : Set a} -> {l : ℕ} -> (X -> A) -> Vec X l -> DecTree A (Medians-Of-5 X l) (2 * l)
        medians-of-5-by _ []                       = return $ medians [] []
        medians-of-5-by _ (a ∷ [])              = delay 2 $ return $ medians [] [ index f0 a ]
        medians-of-5-by _ (a ∷ b ∷ [])          = delay 4 $ return $ medians [] $ (index f0 a) ∷ [ index f1 b ]
        medians-of-5-by _ (a ∷ b ∷ c ∷ [])      = delay 6 $ return $ medians [] $ (index f0 a) ∷ (index f1 b) ∷ [ index f2 c ]
        medians-of-5-by _ (a ∷ b ∷ c ∷ d ∷ [])  = delay 8 $ return $ medians [] $ (index f0 a) ∷ (index f1 b) ∷ (index f2 c) ∷ [ index f3 d ]
        medians-of-5-by f (a ∷ b ∷ c ∷ d ∷ e ∷ xs) = let n = len xs in
                                                height-≡ (sym $ *-distribˡ-+ 2 5 n) $
                                                height-≡ (cong (10 +_) $ +-identityʳ (n + (n + 0))) $ do
                                                m5 <- delay 3 $ median5-by f a b c d e
                                                ms <- medians-of-5-by f xs
                                                return $ m5 ::: ms


        quasi-median-length-≡ : ∀ n-5 -> let n = 5 + n-5 in 1 + (2 + 3 * (n / 10)) + (2 + 3 * (n-5 / 10)) + (2 * (n / 10) + 2 * (n-5 / 10) + n % 5) ≡ n
        quasi-median-length-≡ n-5 = let n = 5 + n-5 in let n/10 = n / 10 in let n-5/10 = n-5 / 10 in let n/5 = ⌊ n /5⌋ in begin
                1 + (2 + 3 * n/10) + (2 + 3 * n-5/10) + (2 * n/10 + 2 * n-5/10 + n % 5)
                                        ≡⟨ sym $ +-assoc (1 + (2 + 3 * n/10) + (2 + 3 * n-5/10)) (2 * n/10 + 2 * n-5/10) (n % 5) ⟩
                1 + (2 + 3 * n/10) + (2 + 3 * n-5/10) + (2 * n/10 + 2 * n-5/10) + n % 5
                                        ≡⟨⟩
                3 + 3 * n/10 + (2 + 3 * n-5/10) + (2 * n/10 + 2 * n-5/10) + n % 5
                                        ≡⟨ cong (λ x → x + (2 * n/10 + 2 * n-5/10) + n % 5) $ +-double-comm' 3 (3 * n/10) 2 (3 * n-5/10) ⟩
                5 + (3 * n/10 + 3 * n-5/10) + (2 * n/10 + 2 * n-5/10) + n % 5
                                        ≡⟨ cong (_+ n % 5) $ +-assoc 5 (3 * n/10 + 3 * n-5/10) (2 * n/10 + 2 * n-5/10) ⟩
                5 + ((3 * n/10 + 3 * n-5/10) + (2 * n/10 + 2 * n-5/10)) + n % 5
                                        ≡⟨ cong (λ x -> 5 + x + n % 5) $ +-double-comm' (3 * n/10) (3 * n-5/10) (2 * n/10) (2 * n-5/10) ⟩
                5 + ((3 * n/10 + 2 * n/10) + (3 * n-5/10 + 2 * n-5/10)) + n % 5
                                        ≡⟨ cong (λ x → 5 + (x + (3 * n-5/10 + 2 * n-5/10)) + n % 5) $ sym $ *-distribʳ-+ n/10 3 2 ⟩
                5 + (5 * n/10 + (3 * n-5/10 + 2 * n-5/10)) + n % 5
                                        ≡⟨ cong (λ x → 5 + (5 * n/10 + x) + n % 5) $ sym $ *-distribʳ-+ n-5/10 3 2 ⟩
                5 + (5 * n/10 + 5 * n-5/10) + n % 5
                                        ≡⟨ cong (λ x → 5 + x + n % 5) $ +-comm (5 * n/10) (5 * n-5/10) ⟩
                5 + (5 * n-5/10 + 5 * n/10) + n % 5
                                        ≡⟨ cong (_+ n % 5) $ +-assoc 5 (5 * n-5/10) (5 * n/10) ⟩
                5 + 5 * n-5/10 + 5 * n/10 + n % 5
                                        ≡⟨ cong (λ x → x + 5 * n/10 + n % 5) $ sym $ *-suc 5 n-5/10  ⟩
                5 * suc n-5/10 + 5 * n/10 + n % 5
                                        ≡⟨ cong (λ x → 5 * suc x + 5 * n/10 + n % 5) $ sym $ ⌊n/5/2⌋≡n/10 n-5 ⟩
                5 * suc ⌊ ⌊ n-5 /5⌋ /2⌋ + 5 * n/10 + n % 5
                                        ≡⟨⟩
                5 * ⌈ n/5 /2⌉ + 5 * n/10 + n % 5
                                        ≡⟨ cong (_+ n % 5) $ +-comm (5 * ⌈ n/5 /2⌉) (5 * n/10) ⟩
                5 * n/10 + 5 * ⌈ n/5 /2⌉ + n % 5
                                        ≡⟨ cong (λ x → 5 * x + 5 * ⌈ n/5 /2⌉ + n % 5) $ sym $ ⌊n/5/2⌋≡n/10 n ⟩
                5 * ⌊ n/5 /2⌋ + 5 * ⌈ n/5 /2⌉ + n % 5
                                        ≡⟨ cong (_+ n % 5) $ a⌊n/2⌋+a⌈n/2⌉≡a*n 5 n/5 ⟩
                5 * n/5 + n % 5         ≡⟨ 5⌊n/5⌋+n%5≡n n ⟩
                n                       ∎
            where
                open ≡-Reasoning

    Quasi-Median : Set a -> ℕ -> Set a
    Quasi-Median A l = Split A l (λ x → suc x ≥ 3 * (l / 10)) (λ x → suc x ≥ 3 * (l / 10))

    Ordselect : Set a -> (l : ℕ) -> (i : Fin l) -> Set a
    Ordselect A l i = Split A l (_≡ Data.Fin.toℕ i) (_≡ l Data.Fin.ℕ-ℕ (Data.Fin.raise 1 i))

    quasi-median-by : {A X : Set a} -> {l-1 : ℕ} -> let l = suc l-1 in (X -> A) -> Vec X l -> DecTree A (Quasi-Median X l) (4 * l)
    ordselect-by : {A X : Set a} {l-1 : ℕ} -> let l = suc l-1 in (X -> A) -> (i : Fin l) -> (xs : Vec X l) -> DecTree A (Ordselect X l i) (10 * l)

    quasi-median-by _ (a ∷ []) = delay 4 $ return $ record
                                    { median = index f0 a
                                    ; smaller = []
                                    ; larger = []
                                    ; unknown = []
                                    ; length-≡ = refl
                                    ; bound-smaller = z≤n
                                    ; bound-larger = z≤n
                                    }
    quasi-median-by f (a ∷ b ∷ []) = delay 7 $ median2-by f a b <&> λ (med , l) → record
                                    { median = med
                                    ; smaller = []
                                    ; larger = [ l ]
                                    ; unknown = []
                                    ; length-≡ = refl
                                    ; bound-smaller = z≤n
                                    ; bound-larger = z≤n
                                    }
    quasi-median-by f (a ∷ b ∷ c ∷ []) = delay 9 $ median3-by f a b c <&> λ (s , med , l) → record
                                    { median = med
                                    ; smaller = [ s ]
                                    ; larger = [ l ]
                                    ; unknown = []
                                    ; length-≡ = refl
                                    ; bound-smaller = z≤n
                                    ; bound-larger = z≤n
                                    }
    quasi-median-by f (a ∷ b ∷ c ∷ d ∷ []) = delay 11 $ median4-by f a b c d <&> λ (s , med , l₁ , l₂) → record
                                    { median = med
                                    ; smaller = [ s ]
                                    ; larger = l₁ ∷ [ l₂ ]
                                    ; unknown = []
                                    ; length-≡ = refl
                                    ; bound-smaller = z≤n
                                    ; bound-larger = z≤n
                                    }
    quasi-median-by {l-1 = l-1} f xs@(_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ xss) = let l = suc l-1 in
        height-≡ (sym $ *-distribʳ-+ l 2 2) $
        height-≡ (+-identityʳ (2 * l + 2 * l)) $
        height-≡ (sym $ +-assoc (2 * l) (2 * l) 0 ) $
        do
            medians ms overflow <- medians-of-5-by f xs
            let ix = ix-half ms
            med-of-meds' <- delay-≤ (10⌊n/5⌋≤2n l) $ ordselect-by (f ∘ m5-extract-value) ix ms
            let med-of-meds = simplify-med-split {v = ms} med-of-meds'
            return $ record
                   { median = m5-extract-indexed $ Indexed.value $ Split.median med-of-meds
                   ; smaller = small med-of-meds
                   ; larger = large med-of-meds
                   ; unknown = unk med-of-meds ++ overflow
                   ; length-≡ = quasi-median-length-≡ $ len xss
                   ; bound-smaller = ≤-step $ ≤-step $ ≤-step ≤-refl
                   ; bound-larger = a+a*n/10≥a*[n+5]/10 3 (len xss)
                   }
        where
            open Data.Fin hiding (_+_ ; _≤_)
            open Data.Fin.Properties hiding (≤-refl)
            open import Fin.Props
            m5-extract-value : ∀ {l} -> M5 A l -> A
            m5-extract-value (_ , _ , (index _ v) , _ , _) = v
            m5-extract-indexed : ∀ {l} -> M5 A l -> Indexed A l
            m5-extract-indexed (_ , _ , iv , _ , _) = iv
            m5-strictly-smaller : ∀ {l} -> M5 A l -> Vec (Indexed A l) 2
            m5-strictly-smaller (s₁ , s₂ , _ , _ , _) = s₁ ∷ [ s₂ ]
            m5-strictly-larger : ∀ {l} -> M5 A l -> Vec (Indexed A l) 2
            m5-strictly-larger (_ , _ , _ , l₁ , l₂) = l₁ ∷ [ l₂ ]
            m5-extract-l : ∀ {l l'} -> Vec (M5 A l') l -> Vec (Indexed A l') (3 * l)
            m5-extract-l {l = l} xs = subst (Vec _) (*-comm l 3) $ concat $ Data.Vec.map (λ (s₁ , s₂ , m , _ , _) → s₁ ∷ s₂ ∷ [ m ]) xs
            m5-extract-r : ∀ {l l'} -> Vec (M5 A l') l -> Vec (Indexed A l') (3 * l)
            m5-extract-r {l = l} xs = subst (Vec _) (*-comm l 3) $ concat $ Data.Vec.map (λ (_ , _ , m , l₁ , l₂) → l₁ ∷ l₂ ∷ [ m ]) xs
            m5-extract-strictly-smaller : ∀ {l l'} -> Vec (M5 A l') l -> Vec (Indexed A l') (2 * l)
            m5-extract-strictly-smaller {l = l} xs = subst (Vec _) (*-comm l 2) $ concat $ Data.Vec.map m5-strictly-smaller xs
            m5-extract-strictly-larger : ∀ {l l'} -> Vec (M5 A l') l -> Vec (Indexed A l') (2 * l)
            m5-extract-strictly-larger {l = l} xs = subst (Vec _) (*-comm l 2) $ concat $ Data.Vec.map m5-strictly-larger xs
            ix-half : ∀ {l-1} -> Vec A (suc l-1) -> Fin (suc l-1)
            ix-half {l-1 = l-1} _ = fromℕ< {m = ⌊ suc l-1 /2⌋} (n>0⇒⌊n/2⌋<n _)
            simplify-med-split : ∀ {l-5} -> let l = 5 + l-5 in {v : Vec (M5 A l) ⌊ l /5⌋} -> Split (M5 A l) ⌊ l /5⌋ (_≡ toℕ (ix-half v)) (_≡ ⌊ l-5 /5⌋ ℕ-ℕ ix-half v) -> Split (M5 A l) ⌊ l /5⌋ (_≡ ⌊ ⌊ l /5⌋ /2⌋) (_≡ ⌊ ⌊ l-5 /5⌋ /2⌋)
            simplify-med-split {A = A} {l-5 = l-5} s = let l = 5 + l-5 in
                subst2 (λ lower-bound upper-bound -> Split (M5 A l) ⌊ l /5⌋ (_≡ lower-bound) (_≡ upper-bound))
                    (toℕ-fromℕ< $ n>0⇒⌊n/2⌋<n ⌊ l-5 /5⌋)
                    (nℕ-ℕsuc⌊n/2⌋≡⌊n-1/2⌋ ⌊ l-5 /5⌋)
                s
            small : ∀ {l-5} -> let l = 5 + l-5 in Split (M5 A l) ⌊ l /5⌋ (_≡ ⌊ ⌊ l /5⌋ /2⌋) (_≡ ⌊ ⌊ l-5 /5⌋ /2⌋) -> Vec (Indexed A l) (2 + 3 * (l / 10))
            small {l-5 = l-5} s = subst (λ k -> Vec _ (2 + 3 * k)) (trans (Split.bound-smaller s) (⌊n/5/2⌋≡n/10 $ 5 + l-5)) $ (m5-strictly-smaller $ Indexed.value $ Split.median s) ++ (m5-extract-l $ Data.Vec.map Indexed.value $ Split.smaller s)
            large : ∀ {l-5} -> let l = 5 + l-5 in Split (M5 A l) ⌊ l /5⌋ (_≡ ⌊ ⌊ l /5⌋ /2⌋) (_≡ ⌊ ⌊ l-5 /5⌋ /2⌋) -> Vec (Indexed A l) (2 + 3 * (l-5 / 10))
            large {l-5 = l-5} s = subst (λ k -> Vec _ (2 + 3 * k)) (trans (Split.bound-larger s) (⌊n/5/2⌋≡n/10 l-5)) $ (m5-strictly-larger $ Indexed.value $ Split.median s) ++ (m5-extract-r $ Data.Vec.map Indexed.value $ Split.larger s)
            unk : ∀ {l-5} -> let l = 5 + l-5 in Split (M5 A l) ⌊ l /5⌋ (_≡ ⌊ ⌊ l /5⌋ /2⌋) (_≡ ⌊ ⌊ l-5 /5⌋ /2⌋) -> Vec (Indexed A l) (2 * (l / 10) + 2 * (l-5 / 10))
            unk {l-5 = l-5} s = let l = 5 + l-5 in
                    subst (λ x → Vec _ (2 * (l / 10) + 2 * x))
                        (trans (Split.bound-larger s) (⌊n/5/2⌋≡n/10 l-5)) $
                    subst (λ x → Vec _ (2 * x + 2 * len (Split.larger s)))
                        (trans (Split.bound-smaller s) (⌊n/5/2⌋≡n/10 l)) $
                    (m5-extract-strictly-larger $ Data.Vec.map Indexed.value $ Split.smaller s) ++ (m5-extract-strictly-smaller $ Data.Vec.map Indexed.value $ Split.larger s)



    ordselect-eq : {ls ll lu lus lul n : ℕ} -> (i : Fin n) -> Indexed A n -> Vec (Indexed A n) (ls + lus) -> Vec (Indexed A n) (ll + lul) -> lus + lul ≡ lu -> 1 + ls + ll + lu ≡ n -> Data.Fin.toℕ i ≡ ls + lus -> Ordselect A n i
    ordselect-eq {ls = ls} {ll = ll} {lu = lu} {lus = lus} {lul = lul} {n = suc n} i v smaller larger lus+lul≡lu 1+ls+ll+lu≡n i≡ls+lus =
            record
              { median = v
              ; smaller = smaller
              ; larger = larger
              ; unknown = []
              ; length-≡ = bound-≡
              ; bound-smaller = sym i≡ls+lus
              ; bound-larger = bound-l
              }
        where
            open ≡-Reasoning
            open import Data.Fin using (_ℕ-ℕ_ ; toℕ)
            bound-≡ : suc ls + lus + (ll + lul) + 0 ≡ suc n
            bound-≡ = begin
                    suc ls + lus + (ll + lul) + 0 ≡⟨ +-identityʳ _ ⟩
                    suc ls + lus + (ll + lul)     ≡⟨ +-assoc (suc ls) lus (ll + lul) ⟩
                    suc ls + (lus + (ll + lul))   ≡⟨ cong (suc ls +_) $ sym $ +-assoc lus ll lul  ⟩
                    suc ls + (lus + ll + lul)     ≡⟨ cong (suc ls +_) $ cong (_+ lul) $ +-comm lus ll ⟩
                    suc ls + (ll + lus + lul)     ≡⟨ cong (suc ls +_) $ +-assoc ll lus lul ⟩
                    suc ls + (ll + (lus + lul))   ≡⟨ sym $ +-assoc (suc ls) ll (lus + lul) ⟩
                    suc ls + ll + (lus + lul)     ≡⟨ cong (suc ls + ll +_) $ lus+lul≡lu ⟩
                    suc ls + ll + lu              ≡⟨ 1+ls+ll+lu≡n ⟩
                    suc n                         ∎
            bound-l : ll + lul ≡ n ℕ-ℕ i
            bound-l = begin
                    ll + lul            ≡⟨ a+b≡c⇒b≡c-a (suc ls + lus) (ll + lul) (suc n) $ trans (sym $ +-identityʳ _) bound-≡ ⟩
                    suc n ∸ (suc ls + lus)        ≡⟨⟩
                    n ∸ (ls + lus)                ≡⟨ cong (n ∸_) $ sym $ i≡ls+lus ⟩
                    n ∸ toℕ i                     ≡⟨ sym $ nℕ-ℕi≡n∸i n i ⟩
                    n ℕ-ℕ i                       ∎

    ordselect-lt : {X A : Set a} {ls ll lu lus lul n : ℕ} -> (X -> A) -> (i : Fin n) -> Indexed X n -> Vec (Indexed X n) (ls + lus) -> Vec (Indexed X n) (ll + lul) -> lus + lul ≡ lu -> 1 + ls + ll + lu ≡ n -> Data.Fin.toℕ i < ls + lus -> DecTree A (Ordselect X n i) (10 * (ls + lus))
    ordselect-lt {ls = ls} {ll = ll} {lu = lu} {lus = lus} {lul = lul} {n = n@(suc n-1)} f i v smaller larger lus+lul≡lu 1+ls+ll+lu≡n i<ls+lus = height-≡ {!!} $ do
            split <- recurse
            let Diff k by i+k≡s = diff-i-s
            return (record
                      { median = Indexed.value $ Split.median split
                      ; smaller = Data.Vec.map Indexed.value $ Split.smaller split
                      ; larger = v ∷ (Data.Vec.map Indexed.value $ Split.larger split) ++ larger
                      ; unknown = []
                      ; length-≡ = bound-≡ split
                      ; bound-smaller = {!!}
                      ; bound-larger = {!!}
                      })
        where
            open ≡-Reasoning
            open import Data.Fin using (fromℕ< ; toℕ)
            open import Data.Fin.Properties using (toℕ<n)
            diff-i-s = diff i<ls+lus
            i' : Fin (ls + lus)
            i' = fromℕ< {m = toℕ i} i<ls+lus
            recurse = let Diff k by i+k≡s = diff-i-s in
                      subst (DecTree _ _) (cong (10 *_) i+k≡s) $
                      ordselect-by (f ∘ Indexed.value) (subst Fin (sym i+k≡s) i') (subst (Vec _) (sym i+k≡s) smaller)
            bound-≡ : (split : Ordselect (Indexed A n) (1 + toℕ i + Diff.k diff-i-s) (subst Fin (sym (Diff.pf diff-i-s)) $ fromℕ< i<ls+lus)) -> 1 + Split.l₁ split + (1 + Split.l₂ split + (ll + lul)) + 0 ≡ n
            bound-≡ s = cong suc $ begin
                    Split.l₁ s + (1 + Split.l₂ s + (ll + lul)) + 0  ≡⟨ +-identityʳ _ ⟩
                    Split.l₁ s + (1 + Split.l₂ s + (ll + lul))      ≡⟨ sym $ +-assoc (Split.l₁ s) (1 + Split.l₂ s) (ll + lul)  ⟩
                    Split.l₁ s + (1 + Split.l₂ s) + (ll + lul)      ≡⟨ cong (_+ (ll + lul)) $ sym $ +-assoc (Split.l₁ s) 1 (Split.l₂ s) ⟩
                    Split.l₁ s + 1 + Split.l₂ s + (ll + lul)        ≡⟨ cong (λ x → x + Split.l₂ s + (ll + lul)) $ +-comm (Split.l₁ s) 1 ⟩
                    1 + Split.l₁ s + Split.l₂ s + (ll + lul)        ≡⟨ cong (_+ (ll + lul)) $ sym $ +-identityʳ (1 + Split.l₁ s + Split.l₂ s) ⟩
                    1 + Split.l₁ s + Split.l₂ s + 0 + (ll + lul)    ≡⟨ cong (λ x → 1 + Split.l₁ s + Split.l₂ s + x + (ll + lul)) $ sym $ a+b+c≡n∧a≡k∧b≡nℕ-ℕk⇒c≡0 (suc-injective $ Split.length-≡ s) (Split.bound-smaller s) (Split.bound-larger s) ⟩
                    1 + Split.l₁ s + Split.l₂ s + Split.l₃ s + (ll + lul) ≡⟨ cong (_+ (ll + lul)) $ Split.length-≡ s ⟩
                    1 + toℕ i + Diff.k diff-i-s + (ll + lul)        ≡⟨ cong (_+ (ll + lul)) $ Diff.pf diff-i-s ⟩
                    ls + lus + (ll + lul)                           ≡⟨ +-double-comm' ls lus ll lul ⟩
                    ls + ll + (lus + lul)                           ≡⟨ cong ((ls + ll) +_) lus+lul≡lu ⟩
                    ls + ll + lu                                    ≡⟨ suc-injective 1+ls+ll+lu≡n ⟩
                    n-1                                             ∎

    ordselect-by f i xs = let iℕ = toℕ i in
        height-≡ {!!} $ do
            split <- quasi-median-by f xs
            unk-smaller , unk-larger by us+ul≡l₃ <- delay-≤ (l₃≤4n/10+19 split) $ split-pivot-by (f ∘ Indexed.value) (Split.median split) $ Split.unknown split
            let smaller = Split.smaller split ++ unk-smaller
            let larger = Split.larger split ++ unk-larger
            rec <- case ord iℕ (len smaller) of λ where
                (lt pf) -> {!return $ ordselect-lt i (Split.median split) smaller larger us+ul≡l₃ (Split.length-≡ split) pf!}
                (eq pf) -> return $ ordselect-eq i (Split.median split) smaller larger us+ul≡l₃ (Split.length-≡ split) pf
                (gt pf) -> {!!}
            {!!}
        where
            open Data.Fin using (toℕ)
            l₃≤4n/10+19 : ∀ {l} -> (s : Quasi-Median A l) -> Split.l₃ s ≤ 4 * (l / 10) + 19
            l₃≤4n/10+19 s = 1+a+b+c≡n∧a,b≥3n/10⇒c≤4n/10 (Split.length-≡ s) (Split.bound-smaller s) (Split.bound-larger s)

{-}
    ordselect {A = A} {l = l-1} i xs = height-≡ {!!} $ do
            ms <- medians-of-5 xs
            _ , (iₚ , pivot) <- median-by Data.Product.proj₂ (subst (Vec _) (Data.Product.proj₂ $ ⌈1+n/5⌉>0 l-1) ms)
            let xs' = remove xs iₚ
            smaller , larger by split-length-≡ <- split-pivot pivot xs'
            height-≡ {!!} $ case ord (iℕ) (len smaller) of λ where
                (lt pf) -> delay-≤ {!!} $ do
                    let Diff k by suc≡l₁ = diff pf
                    let smaller' = subst (Vec _) (sym suc≡l₁) smaller
                    let idx = subst Fin (sym suc≡l₁) $ Data.Fin.fromℕ< pf
                    let recurse = ordselect idx smaller'
                    found_index , r <- subst (λ l -> DecTree _ (Fin l × A) (10 * l)) suc≡l₁ recurse
                    let lifted_index = Data.Fin.inject≤ {n = suc l-1} found_index (m+n≤o⇒m≤o (len smaller) $ ≤-step $ ≤-reflexive split-length-≡)
                    return $ lifted_index , r
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
    -}
