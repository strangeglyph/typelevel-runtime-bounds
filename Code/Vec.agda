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

        ordselect-lt : {X A : Set a} {ls ll lu lus lul n : ℕ} -> (X -> A) -> (i : Fin n) -> Indexed X n -> Vec (Indexed X n) (ls + lus) -> Vec (Indexed X n) (ll + lul) -> lus + lul ≡ lu -> 1 + ls + ll + lu ≡ n -> Data.Fin.toℕ i < ls + lus -> DecTree A (Ordselect X n i) (10 * (ls + lus))
        ordselect-lt {ls = ls} {ll = ll} {lu = lu} {lus = lus} {lul = lul} {n = n@(suc n-1)} f i v smaller larger lus+lul≡lu 1+ls+ll+lu≡n i<ls+lus = height-≡ (+-identityʳ _) $ do
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
                open import Data.Fin using (fromℕ< ; toℕ ; _ℕ-ℕ_)
                open import Data.Fin.Properties using (toℕ<n ; toℕ-fromℕ<)
                diff-i-s = diff i<ls+lus
                i' : Fin (ls + lus)
                i' = fromℕ< {m = toℕ i} i<ls+lus
                RecurseSelect : Set a ->  Set a
                RecurseSelect A = Ordselect (Indexed A n) (1 + toℕ i + Diff.k diff-i-s) (subst Fin (sym $ Diff.pf diff-i-s) i')
                recurse = let Diff k by i+k≡s = diff-i-s in
                        subst (DecTree _ _) (cong (10 *_) i+k≡s) $
                        ordselect-by (f ∘ Indexed.value) (subst Fin (sym i+k≡s) i') (subst (Vec _) (sym i+k≡s) smaller)

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

        ordselect-gt : {X A : Set a} {ls ll lu lus lul n : ℕ} -> (X -> A) -> (i : Fin n) -> Indexed X n -> Vec (Indexed X n) (ls + lus) -> Vec (Indexed X n) (ll + lul) -> lus + lul ≡ lu -> 1 + ls + ll + lu ≡ n -> ls + lus < Data.Fin.toℕ i -> DecTree A (Ordselect X n i) (10 * (ll + lul))
        ordselect-gt {X = X} {A = A} {ls = ls} {ll = ll} {lu = lu} {lus = lus} {lul = lul} {n = n} f i v smaller larger lus+lul≡lu 1+ls+ll+lu≡n ls+lus<i = height-≡ (+-identityʳ _) $ do
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
                open import Data.Fin using (toℕ ; fromℕ< ; strengthen ; _ℕ-ℕ_) renaming (_-_ to _-F_)
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

                recurse = height-≡ (cong (10 *_) $ sym ll+lul≡1+k'+k) $
                          ordselect-by (f ∘ Indexed.value) (subst Fin n-j≡1+k'+k i') (subst (Vec _) ll+lul≡1+k'+k larger)

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


        split-sorted : {l : ℕ} -> (i : Fin l) -> Vec (Indexed A l) l -> Ordselect A l i
        split-sorted i xs = record
                              { median = lookup xs i
                              ; smaller = {!take-f xs i!}
                              ; larger = {!drop $ drop-f xs i!}
                              ; unknown = {!!}
                              ; length-≡ = {!!}
                              ; bound-smaller = {!!}
                              ; bound-larger = {!!}
                              }


    ordselect-by {l-1 = l-1} f i xs with 90 | ord (suc l-1) 90
    ... | _ | lt l<90 = delay-≤ {!!} $ {!flip lookup i <$> merge-sort xs!}
    ... | _ | eq l≡90 = {!!}
    ... | _ | gt l>90 = {!!}

{-}
        let iℕ = toℕ i in
        height-≡ {!!} $ do
            split <- quasi-median-by f xs
            let l₃≤l = ≤-trans (m≤n+m (Split.l₃ split) (1 + Split.l₁ split + Split.l₂ split)) (≤-reflexive $ Split.length-≡ split)
            unk-smaller , unk-larger by us+ul≡l₃ <- delay-≤ l₃≤l $ split-pivot-by (f ∘ Indexed.value) (Split.median split) $ Split.unknown split
            let smaller = Split.smaller split ++ unk-smaller
            let larger = Split.larger split ++ unk-larger
            let us≤l₃ = ≤-trans (m≤m+n (len unk-smaller) (len unk-larger)) (≤-reflexive us+ul≡l₃)
            let ul≤l₃ = ≤-trans (m≤n+m (len unk-larger) (len unk-smaller)) (≤-reflexive us+ul≡l₃)

            case ord iℕ (len smaller) of λ where
                (lt pf) -> delay-≤ (*-monoʳ-≤ 10 $ ≤-trans (+-monoʳ-≤ (Split.l₁ split) us≤l₃) $ l₁+l₃≤7n/10+9 split) $ ordselect-lt {ls = Split.l₁ split} f i (Split.median split) smaller larger us+ul≡l₃ (Split.length-≡ split) pf
                (eq pf) -> delay-≤ z≤n $ return $ ordselect-eq {ls = Split.l₁ split} i (Split.median split) smaller larger us+ul≡l₃ (Split.length-≡ split) pf
                (gt pf) -> delay-≤ (*-monoʳ-≤ 10 $ ≤-trans (+-monoʳ-≤ (Split.l₂ split) ul≤l₃) $ l₂+l₃≤7n/10+9 split) $ ordselect-gt {ls = Split.l₁ split} f i (Split.median split) smaller larger us+ul≡l₃ (Split.length-≡ split) pf
        where
            open Data.Fin using (toℕ)
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
-}
