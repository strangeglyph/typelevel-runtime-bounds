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


module Median where
    open import Data.Fin using (raise)
    private
        record Split (A : Set a) (l : ℕ) (b₁ b₂ : ℕ -> Set) : Set a where
            field
                median : Indexed A l
                {l₁ l₂ l₃} : ℕ
                smaller : Vec A l₁
                larger : Vec A l₂
                unknown : Vec A l₃
                length-≡ : suc (l₁ + l₂ + l₃) ≡ l
                bound-smaller : b₁ l₁
                bound-larger : b₂ l₂

        M2 : Set a -> ℕ -> Set a
        M2 A l = Indexed A l × A

        M3 : Set a -> ℕ -> Set a
        M3 A l = A × Indexed A l × A

        M4 : Set a -> ℕ -> Set a
        M4 A l = A × Indexed A l × A × A

        M5 : Set a -> ℕ -> Set a
        M5 A l = A × A × Indexed A l × A × A

        data MX (A : Set a) (l : ℕ) : Set a where
            m1 : Indexed A l -> MX A l
            m2 : M2 A l -> MX A l
            m3 : M3 A l -> MX A l
            m4 : M4 A l -> MX A l


        median2 : A -> A -> DecTree A (M2 A 2) 1
        median2 {A = A} x' y' =
                if x' ≤? y'
                then (return $ x , y')
                else (return $ y , x')
            where
                x y : Indexed A 2
                x = index f0 x'
                y = index f1 y'


        median3 : A -> A -> A -> DecTree A (M3 A 3) 3
        median3 {A = A} x' y' z' =
                if x' ≤? y'
                then if x' ≤? z'
                    then if y' ≤? z'
                        then (return $ x' , y , z')
                        else (return $ x' , z , y')
                    else (return $ z' , x , y')
                else if y' ≤? z'
                    then if x' ≤? z'
                        then (return $ y' , x , z')
                        else (return $ y' , z , x')
                    else (return $ z' , y , x')
            where
                x y z : Indexed A 3
                x = index f0 x'
                y = index f1 y'
                z = index f2 z'

        median4 : A -> A -> A -> A -> DecTree A (M4 A 4) 5
        median4 {A = A} w x y z =
                if w ≤? x
                then if x ≤? y
                    then if x ≤? z
                        then (return $ w , xI , y , z)
                        else if w ≤? z
                            then (return $ w , zI , x , y)
                            else (return $ z , wI , x , y)
                    else if w ≤? y
                        then if y ≤? z
                            then (return $ w , yI , z , x)
                            else if w ≤? z
                                    then (return $ w , zI , y , x)
                                    else (return $ z , wI , y , x)
                        else if w ≤? z
                            then (return $ y , wI , z , x)
                            else if y ≤? z
                                    then (return $ y , zI , w , x)
                                    else (return $ z , yI , w , x)
                else if w ≤? y
                    then if w ≤? z
                        then (return $ x , wI , z , y)
                        else if x ≤? z
                            then (return $ x , zI , w , y)
                            else (return $ z , xI , w , y)
                    else if x ≤? y
                        then if y ≤? z
                            then (return $ x , yI , z , w)
                            else if x ≤? z
                                    then (return $ x , zI , y , w)
                                    else (return $ z , xI , y , w)
                        else if x ≤? z
                            then (return $ y , xI , z , w)
                            else if y ≤? z
                                    then (return $ y , zI , x , w)
                                    else (return $ z , yI , x , w)

            where
                wI xI yI zI : Indexed A 4
                wI = index f0 w
                xI = index f1 x
                yI = index f2 y
                zI = index f3 y

        median5 : A -> A -> A -> A -> A -> DecTree A (M5 A 5) 7
        median5 v w x y z =
                if v ≤? w
                then median5₁ (index f0 v) (index f1 w) (index f2 x) (index f3 y) (index f4 z)
                else median5₁ (index f1 w) (index f0 v) (index f2 x) (index f3 y) (index f4 z) -- swap v, w
            where
                median5₃ : Indexed A 5 -> Indexed A 5 -> Indexed A 5 -> Indexed A 5 -> Indexed A 5 -> DecTree A (M5 A 5) 4
                median5₃ vI@(index _ v) wI@(index _ w) xI@(index _ x) yI@(index _ y) zI@(index _ z) =
                    if w ≤? x
                    then if w ≤? z
                        then if x ≤? z
                            then (return $ v , w , xI , z , y)
                            else (return $ v , w , zI , x , y)
                        else (return $ v , z , wI , x , y)
                    else if w ≤? z
                        then (return $ v , x , wI , z , y)
                        else if v ≤? x
                            then if x ≤? z
                                then (return $ v , x , zI , w , y)
                                else (return $ v , z , xI , w , y)
                            else if v ≤? z
                                then (return $ x , v , zI , w , y)
                                else (return $ x , z , vI , w , y)
                median5₂ : Indexed A 5 -> Indexed A 5 -> Indexed A 5 -> Indexed A 5 -> Indexed A 5 -> DecTree A (M5 A 5) 5
                median5₂ vI wI@(index _ w) xI yI@(index _ y) zI =
                    if w ≤? y
                    then median5₃ vI wI xI yI zI
                    else median5₃ xI yI vI wI zI  -- swap (v w), (x y)
                median5₁ : Indexed A 5 -> Indexed A 5 -> Indexed A 5 -> Indexed A 5 -> Indexed A 5 -> DecTree A (M5 A 5) 6
                median5₁ vI wI xI@(index _ x) yI@(index _ y) zI =
                    if x ≤? y
                    then median5₂ vI wI xI yI zI
                    else median5₂ vI wI yI xI zI -- swap x, y


        inc-idx-m5 : ∀ {l} -> M5 A l -> M5 A (5 + l)
        inc-idx-m5 v = Data.Product.map₂ (Data.Product.map₂ (Data.Product.map₁ (raise-ix 5))) v

        inc-idx-mx : ∀ {l} -> MX A l -> MX A (5 + l)
        inc-idx-mx (m1 v) = m1 $ raise-ix 5 v
        inc-idx-mx (m2 v) = m2 $ Data.Product.map₁ (raise-ix 5) v
        inc-idx-mx (m3 v) = m3 $ Data.Product.map₂ (Data.Product.map₁ (raise-ix 5)) v
        inc-idx-mx (m4 v) = m4 $ Data.Product.map₂ (Data.Product.map₁ (raise-ix 5)) v

        lift-m5 : ∀ {l} -> M5 A 5 -> M5 A (5 + l)
        lift-m5 {l = l} (a , b , c , d , e) = subst (M5 _) (+-comm l 5) $ a , b , (raise-ix l c) , d , e


        data Medians-Of-5 (A : Set a) (l : ℕ) : Set a where
            medians : Vec (M5 A l) ⌊ l /5⌋ -> Vec A (l % 5) -> Medians-Of-5 A l

        _:::_ : {l : ℕ} -> M5 A 5 -> Medians-Of-5 A l -> Medians-Of-5 A (5 + l)
        m5 ::: (medians ms overflow) = medians ((lift-m5 m5) ∷ (Data.Vec.map inc-idx-m5 ms)) overflow


        medians-of-5 : {l : ℕ} -> Vec A l -> DecTree A (Medians-Of-5 A l) (2 * l)
        medians-of-5 []                       = return $ medians [] []
        medians-of-5 xs@(_ ∷ [])              = delay 2 $ return $ medians [] xs
        medians-of-5 xs@(a ∷ b ∷ [])          = delay 4 $ return $ medians [] xs
        medians-of-5 xs@(a ∷ b ∷ c ∷ [])      = delay 6 $ return $ medians [] xs
        medians-of-5 xs@(a ∷ b ∷ c ∷ d ∷ [])  = delay 8 $ return $ medians [] xs
        medians-of-5 (a ∷ b ∷ c ∷ d ∷ e ∷ xs) = let n = len xs in
                                                height-≡ (sym $ *-distribˡ-+ 2 5 n) $
                                                height-≡ (cong (10 +_) $ +-identityʳ (n + (n + 0))) $ do
                                                m5 <- delay 3 $ median5 a b c d e
                                                ms <- medians-of-5 xs
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

    quasi-median : {l-1 : ℕ} -> let l = suc l-1 in Vec A l -> DecTree A (Split A l (λ x → suc x ≥ 3 * (l / 10)) (λ x → suc x ≥ 3 * (l / 10))) (4 * l)
    ordselect-by : {A X : Set a} {l-1 : ℕ} -> let l = suc l-1 in (X -> A) -> (i : Fin l) -> (xs : Vec X l) -> DecTree A (Split X l (_≡ Data.Fin.toℕ i) (_≡ l Data.Fin.ℕ-ℕ (Data.Fin.raise 1 i))) (10 * l)

    quasi-median (a ∷ []) = delay 4 $ return $ record
                                    { median = index f0 a
                                    ; smaller = []
                                    ; larger = []
                                    ; unknown = []
                                    ; length-≡ = refl
                                    ; bound-smaller = z≤n
                                    ; bound-larger = z≤n
                                    }
    quasi-median (a ∷ b ∷ []) = delay 7 $ median2 a b <&> λ (med , l) → record
                                    { median = med
                                    ; smaller = []
                                    ; larger = [ l ]
                                    ; unknown = []
                                    ; length-≡ = refl
                                    ; bound-smaller = z≤n
                                    ; bound-larger = z≤n
                                    }
    quasi-median (a ∷ b ∷ c ∷ []) = delay 9 $ median3 a b c <&> λ (s , med , l) → record
                                    { median = med
                                    ; smaller = [ s ]
                                    ; larger = [ l ]
                                    ; unknown = []
                                    ; length-≡ = refl
                                    ; bound-smaller = z≤n
                                    ; bound-larger = z≤n
                                    }
    quasi-median (a ∷ b ∷ c ∷ d ∷ []) = delay 11 $ median4 a b c d <&> λ (s , med , l₁ , l₂) → record
                                    { median = med
                                    ; smaller = [ s ]
                                    ; larger = l₁ ∷ [ l₂ ]
                                    ; unknown = []
                                    ; length-≡ = refl
                                    ; bound-smaller = z≤n
                                    ; bound-larger = z≤n
                                    }
    quasi-median {l-1 = l-1} xs@(_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ xss) = let l = suc l-1 in
        height-≡ (sym $ *-distribʳ-+ l 2 2) $
        height-≡ (+-identityʳ (2 * l + 2 * l)) $
        height-≡ (sym $ +-assoc (2 * l) (2 * l) 0 ) $
        do
            medians ms overflow <- medians-of-5 xs
            let ix = ix-half ms
            med-of-meds' <- delay-≤ (10⌊n/5⌋≤2n l) $ ordselect-by m5-extract-value ix ms
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
            m5-strictly-smaller : ∀ {l} -> M5 A l -> Vec A 2
            m5-strictly-smaller (s₁ , s₂ , _ , _ , _) = s₁ ∷ [ s₂ ]
            m5-strictly-larger : ∀ {l} -> M5 A l -> Vec A 2
            m5-strictly-larger (_ , _ , _ , l₁ , l₂) = l₁ ∷ [ l₂ ]
            m5-extract-l : ∀ {l l'} -> Vec (M5 A l') l -> Vec A (3 * l)
            m5-extract-l {l = l} xs = subst (Vec _) (*-comm l 3) $ concat $ Data.Vec.map (λ (s₁ , s₂ , (index _ m) , _ , _) → s₁ ∷ s₂ ∷ [ m ]) xs
            m5-extract-r : ∀ {l l'} -> Vec (M5 A l') l -> Vec A (3 * l)
            m5-extract-r {l = l} xs = subst (Vec _) (*-comm l 3) $ concat $ Data.Vec.map (λ (_ , _ , (index _ m) , l₁ , l₂) → l₁ ∷ l₂ ∷ [ m ]) xs
            m5-extract-strictly-smaller : ∀ {l l'} -> Vec (M5 A l') l -> Vec A (2 * l)
            m5-extract-strictly-smaller {l = l} xs = subst (Vec _) (*-comm l 2) $ concat $ Data.Vec.map m5-strictly-smaller xs
            m5-extract-strictly-larger : ∀ {l l'} -> Vec (M5 A l') l -> Vec A (2 * l)
            m5-extract-strictly-larger {l = l} xs = subst (Vec _) (*-comm l 2) $ concat $ Data.Vec.map m5-strictly-larger xs
            ix-half : ∀ {l-1} -> Vec A (suc l-1) -> Fin (suc l-1)
            ix-half {l-1 = l-1} _ = fromℕ< {m = ⌊ suc l-1 /2⌋} (n>0⇒⌊n/2⌋<n _)
            simplify-med-split : ∀ {l-5} -> let l = 5 + l-5 in {v : Vec (M5 A l) ⌊ l /5⌋} -> Split (M5 A l) ⌊ l /5⌋ (_≡ toℕ (ix-half v)) (_≡ ⌊ l-5 /5⌋ ℕ-ℕ ix-half v) -> Split (M5 A l) ⌊ l /5⌋ (_≡ ⌊ ⌊ l /5⌋ /2⌋) (_≡ ⌊ ⌊ l-5 /5⌋ /2⌋)
            simplify-med-split {A = A} {l-5 = l-5} s = let l = 5 + l-5 in
                subst2 (λ lower-bound upper-bound -> Split (M5 A l) ⌊ l /5⌋ (_≡ lower-bound) (_≡ upper-bound))
                    (toℕ-fromℕ< $ n>0⇒⌊n/2⌋<n ⌊ l-5 /5⌋)
                    (nℕ-ℕsuc⌊n/2⌋≡⌊n-1/2⌋ ⌊ l-5 /5⌋)
                s
            small : ∀ {l-5} -> let l = 5 + l-5 in Split (M5 A l) ⌊ l /5⌋ (_≡ ⌊ ⌊ l /5⌋ /2⌋) (_≡ ⌊ ⌊ l-5 /5⌋ /2⌋) -> Vec A (2 + 3 * (l / 10))
            small {l-5 = l-5} s = subst (λ k -> Vec _ (2 + 3 * k)) (trans (Split.bound-smaller s) (⌊n/5/2⌋≡n/10 $ 5 + l-5)) $ (m5-strictly-smaller $ Indexed.value $ Split.median s) ++ (m5-extract-l $ Split.smaller s)
            large : ∀ {l-5} -> let l = 5 + l-5 in Split (M5 A l) ⌊ l /5⌋ (_≡ ⌊ ⌊ l /5⌋ /2⌋) (_≡ ⌊ ⌊ l-5 /5⌋ /2⌋) -> Vec A (2 + 3 * (l-5 / 10))
            large {l-5 = l-5} s = subst (λ k -> Vec _ (2 + 3 * k)) (trans (Split.bound-larger s) (⌊n/5/2⌋≡n/10 l-5)) $ (m5-strictly-larger $ Indexed.value $ Split.median s) ++ (m5-extract-r $ Split.larger s)
            unk : ∀ {l-5} -> let l = 5 + l-5 in Split (M5 A l) ⌊ l /5⌋ (_≡ ⌊ ⌊ l /5⌋ /2⌋) (_≡ ⌊ ⌊ l-5 /5⌋ /2⌋) -> Vec A (2 * (l / 10) + 2 * (l-5 / 10))
            unk {l-5 = l-5} s = let l = 5 + l-5 in
                    subst (λ x → Vec _ (2 * (l / 10) + 2 * x))
                        (trans (Split.bound-larger s) (⌊n/5/2⌋≡n/10 l-5)) $
                    subst (λ x → Vec _ (2 * x + 2 * len (Split.larger s)))
                        (trans (Split.bound-smaller s) (⌊n/5/2⌋≡n/10 l)) $
                    (m5-extract-strictly-larger $ Split.smaller s) ++ (m5-extract-strictly-smaller $ Split.larger s)




    ordselect-by f i xs = {!!}

    {-
    median-by : {l : ℕ} {X A : Set a} -> (X -> A) -> Vec X (suc l) -> DecTree A (Fin (suc l) × X) (10 * suc l)
    ordselect : {l : ℕ} -> (i : Fin $ suc l) -> (xs : Vec A $ suc l) -> DecTree A (Fin (suc l) × A) (10 * suc l)

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
