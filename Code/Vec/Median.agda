module Vec.Median where

open import Level using (Level) renaming (suc to lsuc)

open import Data.Vec hiding (_>>=_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product
open import Data.Sum
open import Data.Fin using (Fin)

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Induction.WellFounded using (Acc)

open import Util
open import DecTree
open import Nat.Base
open import Nat.Props
open import Fin.Props

open import Vec.Base
open import Vec.Sorted

private
    variable
        a : Level
        A : Set a

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

private
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




Quasi-Median : Set a -> ℕ -> Set a
Quasi-Median A l = Split A l (λ x → suc x ≥ 3 * (l / 10)) (λ x → suc x ≥ 3 * (l / 10))

quasi-median-by : {A X : Set a} -> {l-1 : ℕ} -> let l = suc l-1 in Acc _<_ l -> (X -> A) -> Vec X l -> DecTree A (Quasi-Median X l) (9 * l)


Ordselect : Set a -> (l : ℕ) -> (i : Fin l) -> Set a
Ordselect A l i = Split A l (_≡ Data.Fin.toℕ i) (_≡ l Data.Fin.ℕ-ℕ (Data.Fin.raise 1 i))

ordselect-by : {A X : Set a} {l-1 : ℕ} -> let l = suc l-1 in Acc _<_ l -> (X -> A) -> (i : Fin l) -> (xs : Vec X l) -> DecTree A (Ordselect X l i) (35 * l)


private
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

    quasi-median-by _ _ (a ∷ []) = delay 9 $ return $ record
                                    { median = index f0 a
                                    ; smaller = []
                                    ; larger = []
                                    ; unknown = []
                                    ; length-≡ = refl
                                    ; bound-smaller = z≤n
                                    ; bound-larger = z≤n
                                    }
    quasi-median-by _ f (a ∷ b ∷ []) = delay 17 $ median2-by f a b <&> λ (med , l) → record
                                    { median = med
                                    ; smaller = []
                                    ; larger = [ l ]
                                    ; unknown = []
                                    ; length-≡ = refl
                                    ; bound-smaller = z≤n
                                    ; bound-larger = z≤n
                                    }
    quasi-median-by _ f (a ∷ b ∷ c ∷ []) = delay 24 $ median3-by f a b c <&> λ (s , med , l) → record
                                    { median = med
                                    ; smaller = [ s ]
                                    ; larger = [ l ]
                                    ; unknown = []
                                    ; length-≡ = refl
                                    ; bound-smaller = z≤n
                                    ; bound-larger = z≤n
                                    }
    quasi-median-by _ f (a ∷ b ∷ c ∷ d ∷ []) = delay 31 $ median4-by f a b c d <&> λ (s , med , l₁ , l₂) → record
                                    { median = med
                                    ; smaller = [ s ]
                                    ; larger = l₁ ∷ [ l₂ ]
                                    ; unknown = []
                                    ; length-≡ = refl
                                    ; bound-smaller = z≤n
                                    ; bound-larger = z≤n
                                    }
    quasi-median-by {l-1 = l-1} (Acc.acc more) f xs@(_ ∷ _ ∷ _ ∷ _ ∷ _ ∷ xss) = let l = suc l-1 in
        height-≡ (sym $ *-distribʳ-+ l 2 7) $
        height-≡ (+-identityʳ (2 * l + 7 * l)) $
        height-≡ (sym $ +-assoc (2 * l) (7 * l) 0 ) $
        do
            medians ms overflow <- medians-of-5-by f xs
            let ix = ix-half ms
            med-of-meds' <- delay-≤ (a*5*⌊n/5⌋≤a*n 7 l) $ ordselect-by (more ⌊ l /5⌋ $ ⌊l/5⌋<l _) (f ∘ m5-extract-value) ix ms
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
            open import Data.Fin.Properties hiding (≤-refl)
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

private
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

    ordselect-lt : {X A : Set a} {ls ll lu lus lul n : ℕ} -> Acc _<_ n -> (X -> A) -> (i : Fin n) -> Indexed X n -> Vec (Indexed X n) (ls + lus) -> Vec (Indexed X n) (ll + lul) -> lus + lul ≡ lu -> 1 + ls + ll + lu ≡ n -> Data.Fin.toℕ i < ls + lus -> DecTree A (Ordselect X n i) (35 * (ls + lus))
    ordselect-lt {ls = ls} {ll = ll} {lu = lu} {lus = lus} {lul = lul} {n = n@(suc n-1)} (Acc.acc more) f i v smaller larger lus+lul≡lu 1+ls+ll+lu≡n i<ls+lus = height-≡ (+-identityʳ _) $ do
            split <- recurse
            let Diff k by i+k≡s = diff-i-s
            return (record
                    { median = Indexed.value $ Split.median split
                    ; smaller = Data.Vec.map Indexed.value $ Split.smaller split
                    ; larger = v ∷ (Data.Vec.map Indexed.value $ Split.larger split) ++ larger
                    ; unknown = []
                    ; length-≡ = bound-≡ split
                    ; bound-smaller = bound-s split
                    ; bound-larger = bound-l split
                    })
        where
            open ≡-Reasoning
            open import Data.Fin using (fromℕ< ; toℕ ; _ℕ-ℕ_ ; raise)
            open import Data.Fin.Properties using (toℕ<n ; toℕ-fromℕ<)
            diff-i-s = diff i<ls+lus
            i' : Fin (ls + lus)
            i' = fromℕ< {m = toℕ i} i<ls+lus

            1+i+k<n : 1 + toℕ i + Diff.k diff-i-s < n
            1+i+k<n = ≤-begin
                    2 + toℕ i + Diff.k diff-i-s   ≤-≡⟨ cong suc $ Diff.pf diff-i-s ⟩
                    suc ls + lus                    ≤⟨ m≤m+n (suc ls + lus) (ll + lul) ⟩
                    suc ls + lus + (ll + lul)     ≤-≡⟨ +-double-comm' (suc ls) lus ll lul ⟩
                    suc ls + ll + (lus + lul)     ≤-≡⟨ cong (suc ls + ll +_) lus+lul≡lu ⟩
                    1 + ls + ll + lu              ≤-≡⟨ 1+ls+ll+lu≡n ⟩
                    n                             ≤-∎
                where
                    open ≤-Reasoning renaming (begin_ to ≤-begin_ ; _≡⟨_⟩_ to _≤-≡⟨_⟩_ ; _∎ to _≤-∎)

            RecurseSelect : Set a ->  Set a
            RecurseSelect A = Ordselect (Indexed A n) (1 + toℕ i + Diff.k diff-i-s) (subst Fin (sym $ Diff.pf diff-i-s) i')
            recurse = let Diff k by i+k≡s = diff-i-s in
                    subst (DecTree _ _) (cong (35 *_) i+k≡s) $
                    ordselect-by (more (1 + toℕ i + k) 1+i+k<n) (f ∘ Indexed.value) (subst Fin (sym i+k≡s) i') (subst (Vec _) (sym i+k≡s) smaller)

            bound-l : (split : Ordselect (Indexed A n) (1 + toℕ i + Diff.k diff-i-s) (subst Fin (sym $ Diff.pf diff-i-s) i')) -> 1 + Split.l₂ split + (ll + lul) ≡ n-1 ℕ-ℕ i
            bound-l s = begin
                    1 + Split.l₂ s + (ll + lul)

                                    ≡⟨ cong (λ x → 1 + x + (ll + lul)) $ Split.bound-larger s ⟩

                    1 + (1 + toℕ i + Diff.k diff-i-s ℕ-ℕ (raise 1 $ subst Fin (sym $ Diff.pf diff-i-s) i')) + (ll + lul)

                                    ≡⟨ cong (λ x → 1 + x + (ll + lul)) $ sym $ subst-appl (λ k i → k ℕ-ℕ raise 1 i) (sym $ Diff.pf diff-i-s) i' ⟩
                    1 + ((ls + lus) ℕ-ℕ raise 1 i') + (ll + lul)

                                    ≡⟨ cong (λ x → 1 + x + (ll + lul)) $ nℕ-ℕi≡n∸i (ls + lus) (raise 1 i')  ⟩

                    1 + ((ls + lus) ∸ toℕ (raise 1 i')) + (ll + lul)

                                    ≡⟨ cong suc $ sym $ +-∸-comm (ll + lul) $ toℕ<n (raise 1 i') ⟩

                    1 + ((ls + lus) + (ll + lul) ∸ toℕ (raise 1 i'))

                                    ≡⟨ sym $ +-∸-assoc 1 $ ≤-trans (≤-pred $ toℕ<n $ raise 1 i') (m≤m+n (ls + lus) (ll + lul)) ⟩

                    1 + ((ls + lus) + (ll + lul)) ∸ toℕ (raise 1 i')

                                    ≡⟨ cong (λ x → 1 + x ∸ toℕ (raise 1 i')) $ +-double-comm' ls lus ll lul ⟩

                    1 + (ls + ll + (lus + lul)) ∸ toℕ (raise 1 i')

                                    ≡⟨ cong (λ x → 1 + (ls + ll + x) ∸ toℕ (raise 1 i')) lus+lul≡lu ⟩

                    1 + (ls + ll + lu) ∸ toℕ (raise 1 i')

                                    ≡⟨ cong (_∸ (toℕ $ raise 1 i')) 1+ls+ll+lu≡n ⟩

                    n ∸ toℕ (raise 1 i')

                                    ≡⟨ cong (n ∸_) $ raise[x]i≡x+i 1 i' ⟩

                    n-1 ∸ toℕ i'

                                    ≡⟨ cong (n-1 ∸_) $ toℕ-fromℕ< i<ls+lus ⟩

                    n-1 ∸ toℕ i

                                ≡⟨ sym $ nℕ-ℕi≡n∸i n-1 i ⟩

                    n-1 ℕ-ℕ i       ∎

            bound-s : (split : RecurseSelect A) -> Split.l₁ split ≡ toℕ i
            bound-s s = begin
                    Split.l₁ s                                    ≡⟨ Split.bound-smaller s ⟩
                    toℕ (subst Fin (sym (Diff.pf diff-i-s)) i')   ≡⟨ toℕ-subst (sym $ Diff.pf diff-i-s) (fromℕ< i<ls+lus) ⟩
                    toℕ i'                                        ≡⟨ toℕ-fromℕ< i<ls+lus ⟩
                    toℕ i                                         ∎

            bound-≡ : (split : RecurseSelect A) -> 1 + Split.l₁ split + (1 + Split.l₂ split + (ll + lul)) + 0 ≡ n
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

    ordselect-gt : {X A : Set a} {ls ll lu lus lul n : ℕ} -> Acc _<_ n -> (X -> A) -> (i : Fin n) -> Indexed X n -> Vec (Indexed X n) (ls + lus) -> Vec (Indexed X n) (ll + lul) -> lus + lul ≡ lu -> 1 + ls + ll + lu ≡ n -> ls + lus < Data.Fin.toℕ i -> DecTree A (Ordselect X n i) (35 * (ll + lul))
    ordselect-gt {X = X} {A = A} {ls = ls} {ll = ll} {lu = lu} {lus = lus} {lul = lul} {n = n} (Acc.acc more) f i v smaller larger lus+lul≡lu 1+ls+ll+lu≡n ls+lus<i = height-≡ (+-identityʳ _) $ do
            split <- recurse
            return (record
                        { median = Indexed.value $ Split.median split
                        ; smaller = v ∷ smaller ++ (Data.Vec.map Indexed.value $ Split.smaller split)
                        ; larger = Data.Vec.map Indexed.value $ Split.larger split
                        ; unknown = []
                        ; length-≡ = bound-≡ split
                        ; bound-smaller = bound-s split
                        ; bound-larger = bound-l split
                        })
        where
            open ≡-Reasoning
            open import Fin.Base
            open import Fin.Props
            open import Data.Fin using (toℕ ; fromℕ< ; strengthen ; _ℕ-ℕ_) renaming (_-_ to _-F_ ; suc to fsuc)
            open import Data.Fin.Properties using (toℕ<n)

            j = fromℕ≤' {k = suc ls + lus} i ls+lus<i
            i' = i -F j

            diff-i-n = diff $ toℕ<n i
            k = Diff.k diff-i-n
            i+k≡n = Diff.pf diff-i-n

            diff-ls+lus-i = diff $ ls+lus<i
            k' = Diff.k diff-ls+lus-i
            ls+lus+k'≡i = Diff.pf diff-ls+lus-i

            n-j≡1+k'+k : n ∸ toℕ j ≡ 1 + k' + k
            n-j≡1+k'+k = begin
                n ∸ toℕ j                              ≡⟨ cong (n ∸_) $ toℕ-fromℕ≤' i ls+lus<i ⟩
                n ∸ suc (ls + lus)                     ≡⟨ cong (_∸ suc (ls + lus)) $ sym $ i+k≡n ⟩
                toℕ i + k ∸ (ls + lus)                 ≡⟨ cong (λ x → x + k ∸ (ls + lus)) $ sym $ ls+lus+k'≡i ⟩
                suc ls + lus + k' + k ∸ (ls + lus)     ≡⟨ cong (_∸ (ls + lus)) $ +-assoc (suc ls + lus) k' k ⟩
                suc ls + lus + (k' + k) ∸ (ls + lus)   ≡⟨ cong (_∸ (ls + lus)) $ sym $ +-suc (ls + lus) (k' + k) ⟩
                ls + lus + suc (k' + k) ∸ (ls + lus)   ≡⟨ m+n∸m≡n (ls + lus) (suc k' + k) ⟩
                1 + k' + k                             ∎

            1+ls+lus+ll+lul≡n : 1 + ls + lus + (ll + lul) ≡ n
            1+ls+lus+ll+lul≡n = begin
                1 + ls + lus + (ll + lul) ≡⟨ cong suc $ +-double-comm' ls lus ll lul ⟩
                1 + ls + ll + (lus + lul) ≡⟨ cong (1 + ls + ll +_) $ lus+lul≡lu ⟩
                1 + ls + ll + lu          ≡⟨ 1+ls+ll+lu≡n ⟩
                n                         ∎

            ll+lul≡1+k'+k : ll + lul ≡ 1 + k' + k
            ll+lul≡1+k'+k = begin
                ll + lul             ≡⟨ a+b≡c⇒b≡c-a (1 + ls + lus) (ll + lul) n 1+ls+lus+ll+lul≡n ⟩
                n ∸ suc (ls + lus)   ≡⟨ cong (n ∸_) $ sym $ toℕ-fromℕ≤' i ls+lus<i ⟩
                n ∸ toℕ j            ≡⟨ n-j≡1+k'+k ⟩
                1 + k' + k           ∎

            i'≤k'+k : toℕ i' ≤ k' + k
            i'≤k'+k = ≤-pred $ ≤-trans (toℕ<n i') (≤-reflexive n-j≡1+k'+k)

            1+k'+k<n : 1 + k' + k < n
            1+k'+k<n = ≤-begin
                    2 + k' + k                 ≤-≡⟨ cong suc $ sym ll+lul≡1+k'+k ⟩
                    1 + ll + lul                 ≤⟨ +-monoʳ-≤ 1 $ m≤n+m (ll + lul) (ls + lus) ⟩
                    1 + ls + lus + (ll + lul)  ≤-≡⟨ 1+ls+lus+ll+lul≡n ⟩
                    n                          ≤-∎
                where
                    open ≤-Reasoning renaming (begin_ to ≤-begin_ ; _≡⟨_⟩_ to _≤-≡⟨_⟩_ ; _∎ to _≤-∎)

            recurse = height-≡ (cong (35 *_) $ sym ll+lul≡1+k'+k) $
                        ordselect-by (more (1 + k' + k) 1+k'+k<n) (f ∘ Indexed.value) (subst Fin n-j≡1+k'+k i') (subst (Vec _) ll+lul≡1+k'+k larger)

            bound-≡ : (split : Ordselect (Indexed X n) (1 + k' + k) (subst Fin n-j≡1+k'+k i')) -> 2 + ls + lus + Split.l₁ split + Split.l₂ split + 0 ≡ n
            bound-≡ s = begin
                2 + ls + lus + Split.l₁ s + Split.l₂ s + 0   ≡⟨ +-identityʳ _ ⟩
                2 + ls + lus + Split.l₁ s + Split.l₂ s       ≡⟨ cong (λ x -> 2 + ls + lus + x + Split.l₂ s) $ trans (Split.bound-smaller s) (toℕ-subst n-j≡1+k'+k i') ⟩
                2 + ls + lus + toℕ i' + Split.l₂ s           ≡⟨ cong (2 + ls + lus + toℕ i' +_) $ Split.bound-larger s ⟩
                2 + ls + lus + toℕ i' + (k' + k ℕ-ℕ subst Fin n-j≡1+k'+k i')

                                        ≡⟨ cong (2 + ls + lus + toℕ i' +_) $ nℕ-ℕi≡n∸i (k' + k) (subst Fin n-j≡1+k'+k i') ⟩

                2 + ls + lus + toℕ i' + (k' + k ∸ toℕ (subst Fin n-j≡1+k'+k i'))

                                        ≡⟨ cong (2 + ls + lus + toℕ i' +_ ) $ cong (k' + k ∸_) $ toℕ-subst n-j≡1+k'+k i' ⟩

                2 + ls + lus + toℕ i' + (k' + k ∸ toℕ i')    ≡⟨ +-assoc (2 + ls + lus) (toℕ i') (k' + k ∸ toℕ i') ⟩
                2 + ls + lus + (toℕ i' + (k' + k ∸ toℕ i'))  ≡⟨ cong (2 + ls + lus +_) $ m+[n∸m]≡n i'≤k'+k ⟩
                2 + ls + lus + (k' + k)                      ≡⟨ sym $ +-suc (1 + ls + lus) (k' + k) ⟩
                1 + ls + lus + (1 + k' + k)                  ≡⟨ cong (1 + ls + lus +_) $ sym $ ll+lul≡1+k'+k ⟩
                1 + ls + lus + (ll + lul)                    ≡⟨ 1+ls+lus+ll+lul≡n ⟩
                n                                            ∎

            bound-s : (split : Ordselect (Indexed X n) (1 + k' + k) (subst Fin n-j≡1+k'+k i')) -> 1 + ls + lus + Split.l₁ split ≡ toℕ i
            bound-s s = begin
                1 + ls + lus + Split.l₁ s                     ≡⟨ cong (1 + ls + lus +_) $ Split.bound-smaller s ⟩
                1 + ls + lus + toℕ (subst Fin n-j≡1+k'+k i')  ≡⟨ cong (1 + ls + lus +_) $ toℕ-subst n-j≡1+k'+k i' ⟩
                1 + ls + lus + toℕ i'                         ≡⟨⟩
                1 + ls + lus + toℕ (i -F j)                   ≡⟨ cong (1 + ls + lus +_) $ toℕ[a-b] i j ⟩
                1 + ls + lus + (toℕ i ∸ toℕ j)                ≡⟨ sym $ +-∸-assoc (1 + ls + lus) (Fin′≤Fin i j) ⟩
                1 + ls + lus + toℕ i ∸ toℕ j                  ≡⟨ cong (_∸ toℕ j) $ +-comm (1 + ls + lus) (toℕ i) ⟩
                toℕ i + (1 + ls + lus) ∸ toℕ j                ≡⟨ cong (toℕ i + (1 + ls + lus) ∸_) $ toℕ-fromℕ≤' i ls+lus<i ⟩
                toℕ i + (1 + ls + lus) ∸ (1 + ls + lus)       ≡⟨ m+n∸n≡m (toℕ i) (1 + ls + lus) ⟩
                toℕ i                                         ∎

            bound-l : (split : Ordselect (Indexed X n) (1 + k' + k) (subst Fin n-j≡1+k'+k i')) -> Split.l₂ split ≡ n ℕ-ℕ fsuc i
            bound-l s = begin
                Split.l₂ s                                ≡⟨ Split.bound-larger s ⟩
                k' + k ℕ-ℕ subst Fin n-j≡1+k'+k i'        ≡⟨ nℕ-ℕi≡n∸i (k' + k) (subst Fin n-j≡1+k'+k i') ⟩
                k' + k ∸ toℕ (subst Fin n-j≡1+k'+k i')    ≡⟨ cong (k' + k ∸_) $ toℕ-subst n-j≡1+k'+k i' ⟩
                k' + k ∸ toℕ i'                           ≡⟨⟩
                k' + k ∸ toℕ (i -F j)                     ≡⟨ cong (k' + k ∸_) $ toℕ[a-b] i j ⟩
                k' + k ∸ (toℕ i ∸ toℕ j)                  ≡⟨ a∸[b∸c]≡a+c∸b (k' + k) $ Fin′≤Fin i j ⟩
                k' + k + toℕ j ∸ toℕ i                    ≡⟨ cong (λ x → k' + k + x ∸ toℕ i) $ toℕ-fromℕ≤' i ls+lus<i ⟩
                k' + k + (1 + ls + lus) ∸ toℕ i           ≡⟨ cong (_∸ toℕ i) $ +-comm (k' + k) (1 + ls + lus) ⟩
                1 + ls + lus + (k' + k) ∸ toℕ i           ≡⟨ cong (_∸ toℕ i) $ sym $ +-suc (ls + lus) (k' + k)  ⟩
                ls + lus + (1 + k' + k) ∸ toℕ i           ≡⟨ cong (λ x → ls + lus + x ∸ toℕ i) $ sym $ ll+lul≡1+k'+k  ⟩
                ls + lus + (ll + lul) ∸ toℕ i             ≡⟨⟩
                1 + ls + lus + (ll + lul) ∸ toℕ (fsuc i)  ≡⟨ cong (_∸ (toℕ $ fsuc i)) $ 1+ls+lus+ll+lul≡n ⟩
                n ∸ toℕ (fsuc i)                          ≡⟨ sym $ nℕ-ℕi≡n∸i n (fsuc i) ⟩
                n ℕ-ℕ fsuc i                              ∎


    split-sorted : {n : ℕ} -> (i : Fin n) -> Vec (Indexed A n) n -> Ordselect A n i
    split-sorted {n = n} i xs = record
                            { median = lookup xs i
                            ; smaller = take (toℕ i) xs'
                            ; larger = tail $ drop (toℕ i) xs'
                            ; unknown = []
                            ; length-≡ = 1+toℕi+nℕ-ℕ1+i+0≡n
                            ; bound-smaller = refl
                            ; bound-larger = refl
                            }
        where
            open ≡-Reasoning
            open import Data.Fin using (inject₁ ; toℕ ; _ℕ-ℕ_ ; raise)
            open import Data.Fin.Properties using (toℕ-inject₁)
            n≡toℕi+1+nℕ-ℕ1+i : n ≡ toℕ i + suc (n ℕ-ℕ raise 1 i)
            n≡toℕi+1+nℕ-ℕ1+i = begin
                n                                         ≡⟨ fin-identity $ inject₁ i ⟩
                toℕ (inject₁ i) + (n ∸ toℕ (inject₁ i))   ≡⟨ cong (_+ (n ∸ toℕ (inject₁ i))) $ toℕ-inject₁ i ⟩
                toℕ i + (n ∸ toℕ (inject₁ i))             ≡⟨ cong (toℕ i +_) $ sym $ nℕ-ℕi≡n∸i n (inject₁ i) ⟩
                toℕ i + (n ℕ-ℕ inject₁ i)                 ≡⟨ cong (toℕ i +_) $ ℕ-ℕinject₁-ℕ-ℕraise i ⟩
                toℕ i + suc (n ℕ-ℕ raise 1 i)             ∎
            1+toℕi+nℕ-ℕ1+i+0≡n : 1 + toℕ i + (n ℕ-ℕ raise 1 i) + 0 ≡ n
            1+toℕi+nℕ-ℕ1+i+0≡n = begin
                1 + toℕ i + (n ℕ-ℕ raise 1 i) + 0         ≡⟨ +-identityʳ _ ⟩
                1 + toℕ i + (n ℕ-ℕ raise 1 i)             ≡⟨ sym $ +-suc (toℕ i) (n ℕ-ℕ raise 1 i) ⟩
                toℕ i + suc (n ℕ-ℕ raise 1 i)             ≡⟨ sym $ n≡toℕi+1+nℕ-ℕ1+i ⟩
                n                                         ∎
            xs' = subst (Vec _) (n≡toℕi+1+nℕ-ℕ1+i) xs


ordselect-by {l-1 = l-1} wf-acc f i xs with ≤-total (suc l-1) 8000
... | inj₁ l≤8000 = delay-≤ nlogn≤35n $ split-sorted i <$> sorted
    where
        open ≤-Reasoning
        open import Nat.Log
        l = suc l-1
        nlogn≤35n : l * ⌈log₂ l ⌉ ≤ 35 * l
        nlogn≤35n = begin
            l * ⌈log₂ l ⌉  ≤⟨ *-monoʳ-≤ l $ n≤8000⇒⌈log₂n⌉≤35 l≤8000 ⟩
            l * 35         ≡⟨ *-comm l 35 ⟩
            35 * l         ∎
        sorted = merge-sort-by (f ∘ Indexed.value) $ zipWith index (allFin l) xs

... | inj₂ l>8000 =
        let iℕ = toℕ i in
        height-≡ (sym $ *-distribʳ-+ l 9 26) $ do
            split <- quasi-median-by wf-acc f xs
            let l₃≤l = ≤-trans (m≤n+m (Split.l₃ split) (1 + Split.l₁ split + Split.l₂ split)) (≤-reflexive $ Split.length-≡ split)
            unk-smaller , unk-larger by us+ul≡l₃ <- delay-≤ l₃≤l $ split-pivot-by (f ∘ Indexed.value) (Split.median split) $ Split.unknown split
            let smaller = Split.smaller split ++ unk-smaller
            let larger = Split.larger split ++ unk-larger
            let us≤l₃ = ≤-trans (m≤m+n (len unk-smaller) (len unk-larger)) (≤-reflexive us+ul≡l₃)
            let ul≤l₃ = ≤-trans (m≤n+m (len unk-larger) (len unk-smaller)) (≤-reflexive us+ul≡l₃)

            case ord iℕ (len smaller) of λ where
                (lt pf) -> delay-≤ (smallerRuntimeBound split (len unk-smaller) us≤l₃) $ ordselect-lt {ls = Split.l₁ split} wf-acc f i (Split.median split) smaller larger us+ul≡l₃ (Split.length-≡ split) pf
                (eq pf) -> delay-≤ z≤n $ return $ ordselect-eq {ls = Split.l₁ split} i (Split.median split) smaller larger us+ul≡l₃ (Split.length-≡ split) pf
                (gt pf) -> delay-≤ (largerRuntimeBound split (len unk-larger) ul≤l₃) $ ordselect-gt {ls = Split.l₁ split} wf-acc f i (Split.median split) smaller larger us+ul≡l₃ (Split.length-≡ split) pf
    where
        open Data.Fin using (toℕ)
        l = suc l-1

        l₃≤4n/10+19 : ∀ {l} -> (s : Quasi-Median A l) -> Split.l₃ s ≤ 4 * (l / 10) + 19
        l₃≤4n/10+19 s = 1+a+b+c≡n∧a,b≥3n/10⇒c≤4n/10 (Split.length-≡ s) (Split.bound-smaller s) (Split.bound-larger s)

        1+l₁+l₃+l₂≡n : ∀ {l} -> (s : Quasi-Median A l) -> 1 + Split.l₁ s + Split.l₃ s + Split.l₂ s ≡ l
        1+l₁+l₃+l₂≡n {l = l} s =
                        let l₁ = Split.l₁ s in
                        let l₂ = Split.l₂ s in
                        let l₃ = Split.l₃ s in begin
                            1 + l₁ + l₃ + l₂     ≡⟨ cong suc $ +-assoc l₁ l₃ l₂ ⟩
                            1 + l₁ + (l₃ + l₂)   ≡⟨ cong (1 + l₁ +_) $ +-comm l₃ l₂ ⟩
                            1 + l₁ + (l₂ + l₃)   ≡⟨ cong suc $ sym $ +-assoc l₁ l₂ l₃ ⟩
                            1 + l₁ + l₂ + l₃     ≡⟨ Split.length-≡ s ⟩
                            l                    ∎
            where
                open ≡-Reasoning

        1+l₂+l₃+l₁≡n : ∀ {l} -> (s : Quasi-Median A l) -> 1 + Split.l₂ s + Split.l₃ s + Split.l₁ s ≡ l
        1+l₂+l₃+l₁≡n {l = l} s =
                        let l₁ = Split.l₁ s in
                        let l₂ = Split.l₂ s in
                        let l₃ = Split.l₃ s in begin
                            1 + l₂ + l₃ + l₁     ≡⟨ cong suc $ +-comm (l₂ + l₃) l₁ ⟩
                            1 + l₁ + (l₂ + l₃)   ≡⟨ cong suc $ sym $ +-assoc l₁ l₂ l₃ ⟩
                            1 + l₁ + l₂ + l₃     ≡⟨ Split.length-≡ s ⟩
                            l                    ∎
            where
                open ≡-Reasoning

        l₁+l₃≤7n/10+9 : ∀ {l} -> (s : Quasi-Median A l) -> Split.l₁ s + Split.l₃ s ≤ 7 * (l / 10) + 9
        l₁+l₃≤7n/10+9 s = 1+a+b≡n∧b≥3n/10⇒a≤7n/10 (1+l₁+l₃+l₂≡n s) (Split.bound-larger s)

        l₂+l₃≤7n/10+9 : ∀ {l} -> (s : Quasi-Median A l) -> Split.l₂ s + Split.l₃ s ≤ 7 * (l / 10) + 9
        l₂+l₃≤7n/10+9 s = 1+a+b≡n∧b≥3n/10⇒a≤7n/10 (1+l₂+l₃+l₁≡n s) (Split.bound-smaller s)

        7*l/10+9≤71*l/100 : 7 * (l / 10) + 9 ≤ 71 * (l / 100)
        7*l/10+9≤71*l/100 = begin
                7 * (l / 10) + 9                ≡⟨ cong (λ x → 7 * x + 9) $ sym $ am/an≡m/n 9 l 9 ⟩
                7 * (10 * l / 100) + 9          ≤⟨ +-monoˡ-≤ 9 $ *-monoʳ-≤ 7 $ a*b/c≤a*[b/c]+a 10 l 99 ⟩
                7 * (10 * (l / 100) + 10) + 9   ≡⟨ cong (_+ 9) $ *-distribˡ-+ 7 (10 * (l / 100)) 10 ⟩
                7 * (10 * (l / 100)) + 70 + 9   ≡⟨ cong (λ x → x + 70 + 9) $ sym $ *-assoc 7 10 (l / 100) ⟩
                70 * (l / 100) + 70 + 9         ≡⟨ +-assoc (70 * (l / 100)) 70 9 ⟩
                70 * (l / 100) + 79             ≤⟨ +-monoʳ-≤ (70 * (l / 100)) $ ≤-step ≤-refl ⟩
                70 * (l / 100) + 80             ≡⟨⟩
                70 * (l / 100) + 8000 / 100     ≤⟨ +-monoʳ-≤ (70 * (l / 100)) $ /-monoˡ-≤ {o = 100} l>8000 ⟩
                70 * (l / 100) + l / 100        ≡⟨ +-comm (70 * (l / 100)) (l / 100) ⟩
                l / 100 + 70 * (l / 100)        ≡⟨⟩
                71 * (l / 100)                  ∎
            where
                open ≤-Reasoning

        35*71*l/100≤25l : 35 * (71 * (l / 100)) ≤ 25 * l
        35*71*l/100≤25l = begin
                35 * (71 * (l / 100))           ≡⟨ sym $ *-assoc 35 71 (l / 100) ⟩
                2485 * (l / 100)                ≤⟨ *-monoˡ-≤ (l / 100) $ 2485≤2500 ⟩
                2500 * (l / 100)                ≡⟨ *-assoc 25 100 (l / 100) ⟩
                25 * (100 * (l / 100))          ≡⟨ cong (25 *_) $ *-comm 100 (l / 100) ⟩
                25 * (l / 100 * 100)            ≤⟨ *-monoʳ-≤ 25 $ m/n*n≤m l 100 ⟩
                25 * l                          ∎
            where
                open ≤-Reasoning
                2485≤2500 : 2485 ≤ 2500
                2485≤2500 = m≤m+n 2485 15


        smallerRuntimeBound : (s : Quasi-Median A l) -> (us : ℕ) -> us ≤ Split.l₃ s -> 35 * (Split.l₁ s + us) ≤ 25 * l
        smallerRuntimeBound s us us≤l₃ = begin
                35 * (Split.l₁ s + us)          ≤⟨ *-monoʳ-≤ 35 $ +-monoʳ-≤ (Split.l₁ s) us≤l₃ ⟩
                35 * (Split.l₁ s + Split.l₃ s)  ≤⟨ *-monoʳ-≤ 35 $ l₁+l₃≤7n/10+9 s ⟩
                35 * (7 * (l / 10) + 9)         ≤⟨ *-monoʳ-≤ 35 7*l/10+9≤71*l/100 ⟩
                35 * (71 * (l / 100))           ≤⟨ 35*71*l/100≤25l ⟩
                25 * l                          ∎
            where
                open ≤-Reasoning

        largerRuntimeBound : (s : Quasi-Median A l) -> (ul : ℕ) -> ul ≤ Split.l₃ s -> 35 * (Split.l₂ s + ul) ≤ 25 * l
        largerRuntimeBound s ul ul≤l₃ = begin
                35 * (Split.l₂ s + ul)          ≤⟨ *-monoʳ-≤ 35 $ +-monoʳ-≤ (Split.l₂ s) ul≤l₃ ⟩
                35 * (Split.l₂ s + Split.l₃ s)  ≤⟨ *-monoʳ-≤ 35 $ l₂+l₃≤7n/10+9 s ⟩
                35 * (7 * (l / 10) + 9)         ≤⟨ *-monoʳ-≤ 35 7*l/10+9≤71*l/100 ⟩
                35 * (71 * (l / 100))           ≤⟨ 35*71*l/100≤25l ⟩
                25 * l                          ∎
            where
                open ≤-Reasoning



ordselect : {l : ℕ} -> Vec A l -> (i : Fin l) -> DecTree A (Ordselect A l i) (35 * l)
ordselect {l = zero} _ ()
ordselect {l = l@(suc l-1)} xs i = ordselect-by (<-wellFounded l) id i xs

median : {l-1 : ℕ} -> let l = suc l-1 in Vec A l -> DecTree A (Indexed A l) (35 * l)
median {l-1 = l-1} xs = Split.median <$> ordselect xs (Data.Fin.fromℕ< $ n>0⇒⌊n/2⌋<n l-1)
