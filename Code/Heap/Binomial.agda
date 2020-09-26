module Heap.Binomial where

open import Data.Nat as ℕ hiding (_*_ ; _^_)
open import Data.Nat.Properties
open import Data.Integer as ℤ using (ℤ ; _⊖_ ; +_ ; -_)
import Data.Integer.Properties as ℤ-Props
open import Data.Bool as 𝔹 using (Bool ; true ; false)
open import Data.Maybe hiding (_>>=_)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Vec as Vec using (Vec ; _∷_)
open import Level using (Level)
open import Function
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.HeterogeneousEquality as H using (_≅_ ; ≡-subst-removable ; ≅-to-≡)

open import DecTree
open import Nat.Props
open import Nat.Mul
open import Nat.Log
open import Int.Props
open import Util
open import AmortizedTime
open import Leq

private
    variable
        a : Level
        A : Set a

data DescList (A : ℕ -> Set a) : ℕ -> Set a where
    D[_] : A 0 -> DescList A 0
    _D∷_ : {l : ℕ} -> A (suc l) -> DescList A l -> DescList A (suc l)


data BinomialTree (A : Set a) : ℕ -> Set a where
    Leaf : A -> BinomialTree A 0
    Node : {l : ℕ} -> A -> DescList (BinomialTree A) l -> BinomialTree A (suc l)

tSize : {l : ℕ} -> BinomialTree A l -> ℕ
tSize {l = l} _ = 2 ^ l

tVal : {l : ℕ} -> BinomialTree A l -> A
tVal (Leaf x) = x
tVal (Node x _) = x

link : {l : ℕ} -> BinomialTree A l -> BinomialTree A l -> DecTree A (BinomialTree A (suc l)) 1
link (Leaf l) (Leaf r) = if l ≤? r then return (Node l $ D[ Leaf r ]) else return (Node r $ D[ Leaf l ])
link l@(Node x xs) r@(Node y ys) = if x ≤? y then return (Node x $ r D∷ xs) else return (Node y $ l D∷ ys)


data SparseTreeList (A : Set a) : ℕ -> ℕ -> Set a where
    [] : {l : ℕ} -> SparseTreeList A l 0
    empty∷ : {l acc : ℕ} -> SparseTreeList A (suc l) acc -> SparseTreeList A l acc
    entry_∷_ :  {l acc acc' : ℕ}
             -> {acc'≡2^l+acc : acc' ≡ 2 ^ l + acc}
             -> BinomialTree A l
             -> SparseTreeList A (suc l) acc
             -> SparseTreeList A l acc'


data BinomialHeap (A : Set a) : ℕ -> Set a where
    heap : {l acc : ℕ} -> SparseTreeList A l acc -> BinomialHeap A acc

-- # entries
entries : {l acc : ℕ} -> SparseTreeList A l acc -> ℕ
entries [] = 0
entries (empty∷ ts) = entries ts
entries (entry _ ∷ ts) = 1 + entries ts

ts-acc : {l acc : ℕ} -> SparseTreeList A l acc -> ℕ
ts-acc {acc = acc} _ = acc


tlist-subst : {l l' acc : ℕ} -> l ≡ l' -> SparseTreeList A l acc -> SparseTreeList A l' acc
tlist-subst {A = A} {acc = acc} l≡l' ts = subst (λ x → SparseTreeList A x acc) l≡l' ts

tlist-subst-elim :  {b : Level}
                    {B : Set b}
                    {l l' acc : ℕ}
                 -> (f : {A : Set a} {l acc : ℕ} -> SparseTreeList A l acc -> B)
                 -> (l≡l' : l ≡ l')
                 -> (ts : SparseTreeList A l acc)
                 -> f ts ≡ f (subst (λ x → SparseTreeList A x acc) l≡l' ts)
tlist-subst-elim f refl ts = refl

tlist-subst-acc : {l acc acc' : ℕ} -> acc ≡ acc' -> SparseTreeList A l acc -> SparseTreeList A l acc'
tlist-subst-acc {A = A} {l = l} acc≡acc' ts = subst (SparseTreeList A l) acc≡acc' ts

tlist-dec-subst : {l l' acc t : ℕ} -> l ≡ l' -> DecTree A (SparseTreeList A l acc) t -> DecTree A (SparseTreeList A l' acc) t
tlist-dec-subst {A = A} {acc = acc} {t} l≡l' dec = subst (λ x → DecTree A (SparseTreeList A x acc) t) l≡l' dec

tlist-dec-subst-acc : {l acc acc' t : ℕ} -> acc ≡ acc' -> DecTree A (SparseTreeList A l acc) t -> DecTree A (SparseTreeList A l acc') t
tlist-dec-subst-acc {A = A} {l = l} {t = t} acc≡acc' dec =  subst (λ x → DecTree A (SparseTreeList A l x) t) acc≡acc' dec

tlist-dec-subst-acc-elim :  {b : Level}
                            {B : Set b}
                            {l acc acc' t : ℕ}
                         -> (f : {l acc t : ℕ} -> DecTree A (SparseTreeList A l acc) t -> B)
                         -> (acc≡acc' : acc ≡ acc')
                         -> (comp : DecTree A (SparseTreeList A l acc) t)
                         -> f comp ≡ f (tlist-dec-subst-acc acc≡acc' comp)
tlist-dec-subst-acc-elim f refl comp = refl


leadingEntries : {l n : ℕ} -> SparseTreeList A l n -> ℕ
leadingEntries [] = 0
leadingEntries (empty∷ _) = 0
leadingEntries (entry _ ∷ xs) = 1 + leadingEntries xs

leading≤len : {l n : ℕ} -> (ts : SparseTreeList A l n) -> leadingEntries ts ≤ entries ts
leading≤len [] = z≤n
leading≤len (empty∷ ts) = z≤n
leading≤len (entry x ∷ ts) = s≤s $ leading≤len ts


len-log-forward : {k n l acc : ℕ} -> k ≤ 1+⌊log₂ n ⌋ -> n < 2 ^ l -> (ts : SparseTreeList A l acc) -> (k + entries ts) ≤ 1+⌊log₂ n + acc ⌋
len-log-forward {k = k} {n} k≤1+logn n≤2^l [] =
        subst2 (_≤_)
            (sym $ +-identityʳ k)
            (cong 1+⌊log₂_⌋ $ sym $ +-identityʳ n)
        k≤1+logn
len-log-forward {l = l} k≤1+logn n≤2^l (empty∷ ts) = len-log-forward k≤1+logn (≤-trans n≤2^l (m≤m+n (2 ^ l) (2 ^ l))) ts
len-log-forward {k = k} {n} {l} {acc} k≤1+logn n≤2^l (entry_∷_ {acc = acc'} {acc'≡2^l+acc = pf} x ts) = begin
        k + suc (entries ts)           ≡⟨ +-suc k (entries ts) ⟩
        suc k + entries ts             ≤⟨ len-log-forward (1+k≤1+log[n+2^l] k n l k≤1+logn n≤2^l) (+-monoˡ-≤ (2 ^ l) n≤2^l) ts ⟩
        1+⌊log₂ (n + 2 ^ l) + acc' ⌋   ≡⟨ cong (1+⌊log₂_⌋) $ +-assoc n (2 ^ l) acc' ⟩
        1+⌊log₂ n + (2 ^ l + acc') ⌋   ≡⟨ cong (λ x → 1+⌊log₂ n + x ⌋) $ sym pf ⟩
        1+⌊log₂ n + acc ⌋              ∎
    where
        open ≤-Reasoning
        1+k≤1+log[n+2^l] : (k n l : ℕ) -> k ≤ 1+⌊log₂ n ⌋ -> n < 2 ^ l -> suc k ≤ 1+⌊log₂ n + 2 ^ l ⌋
        1+k≤1+log[n+2^l] .0 0 l z≤n n2^l = ≤-trans (s≤s z≤n) (1+⌊log₂⌋-mono $ a^n≥1 1 l)
        1+k≤1+log[n+2^l] k n@(suc n-1) l k≤1+logn n<2^l = begin
            suc k                        ≤⟨ +-monoʳ-≤ 1 k≤1+logn ⟩
            suc 1+⌊log₂ n ⌋              ≡⟨ cong (suc ∘ 1+⌊log₂_⌋) $ sym $ ⌊2n/2⌋≡n n ⟩
            suc 1+⌊log₂ ⌊ 2 ℕ.* n /2⌋ ⌋  ≡⟨ cong (suc ∘ 1+⌊log₂_⌋ ∘ ⌊_/2⌋) $ *≡* 2 n ⟩
            suc 1+⌊log₂ ⌊ 2 * n /2⌋ ⌋    ≡⟨ sym $ 1+⌊log₂⌋-suc (n-1 + n) ⟩
            1+⌊log₂ 2 * n ⌋              ≤⟨ 1+⌊log₂⌋-mono $ +-monoʳ-≤ n (<⇒≤ n<2^l) ⟩
            1+⌊log₂ n + 2 ^ l ⌋          ∎

len≤⌊log₂acc⌋ : {l acc : ℕ} -> (ts : SparseTreeList A l acc) -> entries ts ≤ 1+⌊log₂ acc ⌋
len≤⌊log₂acc⌋ {l = l} ts = len-log-forward z≤n (a^n≥1 1 l) ts

heapLeading : {l : ℕ} -> BinomialHeap A l -> ℕ
heapLeading (heap xs) = leadingEntries xs


tlist-amortized0 : (A : Set a) -> Amortized (SparseTreeList A 0)
Amortized.i₀        (tlist-amortized0 A) = 0
Amortized.initial   (tlist-amortized0 A) = []
Amortized.potential (tlist-amortized0 A) = entries
Amortized.init≡0    (tlist-amortized0 A) = refl

tlist-amortized' : (A : Set a) -> Amortized1 (SparseTreeList A)
Amortized1.i₀        (tlist-amortized' A)   = 0
Amortized1.initial   (tlist-amortized' A) l = []
Amortized1.potential (tlist-amortized' A)   = entries
Amortized1.init≡0    (tlist-amortized' A) l = ≤-antisym (len≤⌊log₂acc⌋ (Amortized1.initial (tlist-amortized' A) l)) z≤n


extendTList : {l l' acc : ℕ} -> l ≤ l' -> SparseTreeList A l' acc -> SparseTreeList A l acc
extendTList {l = l} {l'} l≤l' ts with l <? l'
... | yes (s≤s l≤l'-1) = extendTList l≤l'-1 (empty∷ ts)
... | no l≮l' = tlist-subst (≤-antisym (≮⇒≥ l≮l') l≤l') ts

extendTList-inv : ∀ {l l' acc} -> (l≤l' : l ≤ l') -> (ts : SparseTreeList A l' acc) -> entries (extendTList l≤l' ts) ≡ entries ts
extendTList-inv {l = l} {l'} l≤l' ts with l <? l'
... | yes (s≤s l≤l'-1) = extendTList-inv l≤l'-1 (empty∷ ts)
... | no l≮l'  = sym $ tlist-subst-elim entries (≤-antisym (≮⇒≥ l≮l') l≤l') ts

insertTList≡ : {l acc : ℕ} -> BinomialTree A l -> (ts : SparseTreeList A l acc) -> DecTree A (SparseTreeList A l (2 ^ l + acc)) (leadingEntries ts)
insertTList≡ {l = l} t [] = return $ entry_∷_ {acc' = 2 ^ l + 0} {acc'≡2^l+acc = refl} t []
insertTList≡ {l = l} {acc} t (empty∷ ts) = return $ entry_∷_ {acc' = 2 ^ l + acc} {acc'≡2^l+acc = refl} t ts
insertTList≡ {l = l} t (entry_∷_ {acc = acc'} {acc'≡2^l+acc = pf} t' ts) = do
        t-join <- link t t'
        tlist-dec-subst-acc (trans (+-assoc (2 ^ l) (2 ^ l) acc') $ cong (λ x → 2 ^ l + x) $ sym pf) $
            empty∷ <$> insertTList≡ t-join ts

tlist-n-inserts : (n : ℕ) -> Vec A n -> Am (tlist-amortized0 A) A
tlist-n-inserts zero Vec.[] = lift
tlist-n-inserts (suc n) (x ∷ xs) = Am.step (tlist-n-inserts n xs) (λ ts → insertTList≡ (Leaf x) ts)

tlist-insert-pot-invariant :  {{_ : Leq A}}
                           -> ∀ {l acc}
                           -> (t : BinomialTree A l)
                           -> (ts : SparseTreeList A l acc)
                           -> leadingEntries ts ⊖ entries ts ℤ.+ + entries (reduce $ insertTList≡ t ts) ≡ + 1
tlist-insert-pot-invariant {l = l} t [] = refl
tlist-insert-pot-invariant {l = l} t (empty∷ ts) = 0-a+suca≡1 (entries ts)
tlist-insert-pot-invariant {{≤A}} {l = l} t ts@(entry_∷_ {acc = acc'} {acc'≡2^l+acc = pf} x ts') = begin
        leadingEntries ts ⊖ entries ts ℤ.+ + entries (reduce $ insertTList≡ t ts)
                         ≡⟨ cong (λ x → leadingEntries ts ⊖ entries ts ℤ.+ + x) einsert ⟩
        leadingEntries ts' ⊖ entries ts' ℤ.+ + entries (reduce $ insertTList≡ (reduce $ link t x) ts')
                         ≡⟨ tlist-insert-pot-invariant (reduce $ link t x) ts' ⟩
        + 1              ∎
    where
        open ≡-Reasoning
        einsert : entries (reduce $ insertTList≡ t ts) ≡ entries (reduce $ insertTList≡ (reduce $ link t x) ts')
        einsert = begin
            entries (reduce (insertTList≡ t ts))

                        ≡⟨ cong entries $ bind-elim (link t x) (λ t-join → tlist-dec-subst-acc (trans (+-assoc (2 ^ l) (2 ^ l) acc') (cong (λ x → 2 ^ l + x) $ sym pf)) $ empty∷ <$> insertTList≡ t-join ts') ⟩

            entries (reduce (tlist-dec-subst-acc (trans (+-assoc (2 ^ l) (2 ^ l) acc') (cong (λ x → 2 ^ l + x) $ sym pf)) $ empty∷ <$> insertTList≡ (reduce (link t x)) ts'))
                        ≡⟨ sym $ tlist-dec-subst-acc-elim (entries ∘ reduce {{≤A}}) (trans (+-assoc (2 ^ l) (2 ^ l) acc') (cong (λ x → 2 ^ l + x) $ sym pf)) (empty∷ <$> insertTList≡ (reduce (link t x)) ts') ⟩

            entries (reduce (empty∷ <$> insertTList≡ (reduce (link t x)) ts'))

                        ≡⟨ cong entries $ apply-elim empty∷ (insertTList≡ (reduce $ link t x) ts') ⟩

            entries (reduce $ insertTList≡ (reduce $ link t x) ts')

                        ∎

tlist-insert-in-linear-time : {n : ℕ} -> (xs : Vec A n) -> {{_ : Leq A}} -> atime-full (tlist-n-inserts n xs) ≡ + n
tlist-insert-in-linear-time Vec.[] = refl
tlist-insert-in-linear-time {n = n@(suc n-1)} (x ∷ xs) = let n-1-inserts = tlist-n-inserts _ xs in
                                                         let n-inserts = tlist-n-inserts _ (x ∷ xs) in begin
        atime-full n-1-inserts
        ℤ.+ (leadingEntries (am-eval n-1-inserts)
             ⊖     am-potential n-1-inserts
             ℤ.+ + am-potential n-inserts)         ≡⟨ cong (ℤ._+ atime-step n-inserts) $ tlist-insert-in-linear-time xs ⟩

        + n-1 ℤ.+ (leadingEntries (am-eval n-1-inserts)
                   ⊖     am-potential n-1-inserts
                   ℤ.+ + am-potential n-inserts)   ≡⟨ cong (λ x → + n-1 ℤ.+ x) $ tlist-insert-pot-invariant (Leaf x) (am-eval n-1-inserts) ⟩

        + n-1 ℤ.+ + 1                              ≡⟨⟩

        + (n-1 + 1)                                ≡⟨ cong (+_) $ +-comm n-1 1 ⟩

        + n ∎
    where
        open ≡-Reasoning

tListMergeAm≡ :  {l acc acc' : ℕ}
             -> (left : SparseTreeList A l acc)
             -> (right : SparseTreeList A l acc')
             -> Am1 (tlist-amortized' A) A l
tListMergeAm≡ {l = l} {acc' = acc'} [] right = Am1.step {nextA = const l}
                                                        {nextI = const acc'}
                                                        {time = const 0}
                                                        (lift1 0) (λ _ → return right)
tListMergeAm≡ {l = l} {acc = acc} (empty∷ left) [] = Am1.step {nextA = const l}
                                                              {nextI = const acc}
                                                              {time = const 0}
                                                              (lift1 0) (λ _ → return $ empty∷ left)
tListMergeAm≡ (empty∷ left) (empty∷ right) = Am1.step {nextA = pred}
                                                      {nextI = ts-acc}
                                                      {time = const 0}
                                                      (tListMergeAm≡ left right) (λ ts → return $ empty∷ ts)
tListMergeAm≡ {l = l} (empty∷ left) (entry x ∷ right) = Am1.step {nextA = pred}
                                                                 {nextI = λ ts → 2 ^ l + ts-acc ts}
                                                                 {time = const 0}
                                                                 (tListMergeAm≡ left right) (λ ts → return $ entry_∷_ {acc' = 2 ^ l + ts-acc ts} {acc'≡2^l+acc = refl} x ts)
tListMergeAm≡ {l = l} {acc = acc} left@(entry _ ∷ _) [] = Am1.step {nextA = const l}
                                                                   {nextI = const acc}
                                                                   {time = const 0}
                                                                   (lift1 0) (λ _ → return left)
tListMergeAm≡ {l = l} (entry x ∷ left) (empty∷ right) = Am1.step {nextA = pred}
                                                                 {nextI = λ ts → 2 ^ l + ts-acc ts }
                                                                 {time = const 0}
                                                                 (tListMergeAm≡ left right) (λ ts → return $ entry_∷_ {acc' = 2 ^ l + ts-acc ts} {acc'≡2^l+acc = refl} x ts)
tListMergeAm≡ {l = l} (entry x ∷ left) (entry y ∷ right) = Am1.step {nextA = pred}
                                                                    {nextI = λ ts → 2 ^ (suc l) + ts-acc ts}
                                                                    {time = λ ts → suc $ leadingEntries ts}
                                                                    (tListMergeAm≡ left right)
                                                                    (λ ts → link x y >>= λ t-join → empty∷ <$> insertTList≡ t-join ts)

tListMergeAm≤ :  {l l' acc acc' : ℕ}
              -> l ≤ l'
              -> (left : SparseTreeList A l acc)
              -> (right : SparseTreeList A l' acc')
              -> Am1 (tlist-amortized' A) A l
tListMergeAm≤ {l = l} {l' = l'} l≤l' left right with l <? l'
... | yes (s≤s l≤l'-1) = tListMergeAm≤ l≤l'-1 left (empty∷ right)
... | no  l≮l' = tListMergeAm≡ left (tlist-subst (sym $ ≤-antisym l≤l' (≮⇒≥ l≮l')) right)

tListMergeAm :  {l l' acc acc' : ℕ}
             -> (left : SparseTreeList A l acc)
             -> (right : SparseTreeList A l' acc')
             -> Am1 (tlist-amortized' A) A (l ⊓ l')
tListMergeAm {A = A} {l = l} {l' = l'} left right with ≤-total l l'
... | inj₁ l≤l' = subst (Am1 (tlist-amortized' A) A) (sym $ m≤n⇒m⊓n≡m l≤l') $ tListMergeAm≤ l≤l' left right
... | inj₂ l'≤l = subst (Am1 (tlist-amortized' A) A) (sym $ m≤n⇒n⊓m≡m l'≤l) $ tListMergeAm≤ l'≤l right left

tlist-merge-in-linear-time≡ :  {{_ : Leq A}}
                               {l acc acc' : ℕ}
                            -> (left : SparseTreeList A l acc)
                            -> (right : SparseTreeList A l acc')
                            -> atime-full1 (tListMergeAm≡ left right) ℤ.≤ + (entries left + entries right)
tlist-merge-in-linear-time≡ [] right = ℤ-Props.≤-refl
tlist-merge-in-linear-time≡ (empty∷ left) [] = ℤ.+≤+ (m≤m+n (entries left) 0)
tlist-merge-in-linear-time≡ ll@(empty∷ left) rr@(empty∷ right) = begin
        atime-full1 (tListMergeAm≡ left right)
        ℤ.+ (0
             ⊖     am1-potential (tListMergeAm≡ left right)
             ℤ.+ + am1-potential (tListMergeAm≡ ll rr))          ≡⟨⟩

        atime-full1 (tListMergeAm≡ left right)
        ℤ.+ (0
             ⊖     am1-potential (tListMergeAm≡ left right)
             ℤ.+ + am1-potential (tListMergeAm≡ left right))     ≡⟨ cong (λ x → atime-full1 (tListMergeAm≡ left right) ℤ.+ x) $
                                                                    0-a+[k+a]≡k (am1-potential (tListMergeAm≡ left right)) 0 ⟩

        atime-full1 (tListMergeAm≡ left right) ℤ.+ + 0           ≡⟨ ℤ-Props.+-identityʳ _ ⟩

        atime-full1 (tListMergeAm≡ left right)                   ≤⟨ tlist-merge-in-linear-time≡ left right ⟩

        + (entries left + entries right) ∎
    where
        open ℤ-Props.≤-Reasoning
tlist-merge-in-linear-time≡ (empty∷ left) (entry x ∷ right) = begin
        atime-full1 (tListMergeAm≡ left right)
        ℤ.+ (0
             ⊖     am1-potential (tListMergeAm≡ left right)
             ℤ.+ + (suc $ am1-potential $ tListMergeAm≡ left right))  ≡⟨ cong (λ x → atime-full1 (tListMergeAm≡ left right) ℤ.+ x) $ 0-a+suca≡1 (am1-potential $ tListMergeAm≡ left right) ⟩

        atime-full1 (tListMergeAm≡ left right) ℤ.+ + 1                ≤⟨ ℤ-Props.+-monoˡ-≤ (+ 1) (tlist-merge-in-linear-time≡ left right) ⟩

        + (entries left + entries right) ℤ.+ + 1                      ≡⟨ cong (+_) $ +-comm _ 1 ⟩

        + suc (entries left + entries right)                          ≡⟨ cong (+_) $ sym $ +-suc _ _ ⟩

        + (entries left + suc (entries right))       ∎
    where
        open ℤ-Props.≤-Reasoning
tlist-merge-in-linear-time≡ (entry x ∷ left) [] = ℤ-Props.≤-reflexive $ cong (λ x → + suc x) $ sym $ +-identityʳ _
tlist-merge-in-linear-time≡ (entry x ∷ left) (empty∷ right) = begin
        atime-full1 (tListMergeAm≡ left right)
        ℤ.+ (0
             ⊖     am1-potential (tListMergeAm≡ left right)
             ℤ.+ + (suc $ am1-potential $ tListMergeAm≡ left right))  ≡⟨ cong (λ x → atime-full1 (tListMergeAm≡ left right) ℤ.+ x) $ 0-a+suca≡1 (am1-potential $ tListMergeAm≡ left right) ⟩

        atime-full1 (tListMergeAm≡ left right) ℤ.+ + 1                ≤⟨ ℤ-Props.+-monoˡ-≤ (+ 1) (tlist-merge-in-linear-time≡ left right) ⟩

        + (entries left + entries right) ℤ.+ + 1                      ≡⟨ cong (+_) $ +-comm _ 1 ⟩

        + suc (entries left + entries right)                          ∎
    where
        open ℤ-Props.≤-Reasoning
tlist-merge-in-linear-time≡ ll@(entry x ∷ left) rr@(entry y ∷ right) = begin
        atime-full1 rec-merge
        ℤ.+ (suc (leadingEntries $ am1-eval rec-merge)
             ⊖     am1-potential rec-merge
             ℤ.+ + am1-potential nxt-merge)               ≡⟨ cong (λ x → atime-full1 rec-merge ℤ.+ x) $
                                                             suca-b+c≡suc[a-b+c] (leadingEntries $ am1-eval rec-merge)
                                                                                 (am1-potential rec-merge)
                                                                                 (am1-potential nxt-merge) ⟩

        atime-full1 rec-merge
        ℤ.+ (+ 1 ℤ.+ (leadingEntries (am1-eval rec-merge)
                      ⊖     am1-potential rec-merge
                      ℤ.+ + am1-potential nxt-merge))

                                                          ≡⟨ cong (λ x → atime-full1 rec-merge ℤ.+ (+ 1 ℤ.+ x)) einsert ⟩

        atime-full1 rec-merge ℤ.+ (+ 2)                   ≤⟨ ℤ-Props.+-monoˡ-≤ (+ 2) $ tlist-merge-in-linear-time≡ left right ⟩

        + (entries left + entries right) ℤ.+ (+ 2)        ≡⟨ ℤ-Props.+-comm (+ (entries left + entries right)) (+ 2) ⟩

        + 2 ℤ.+ + (entries left + entries right)          ≡⟨ cong (+_) $ sym $ +-suc (suc $ entries left) (entries right) ⟩

        + suc (entries left + suc (entries right))        ∎
    where
        open ℤ-Props.≤-Reasoning
        open Relation.Binary.PropositionalEquality renaming (module ≡-Reasoning to E)
        rec-merge = tListMergeAm≡ left right
        nxt-merge = tListMergeAm≡ ll rr
        einsert : leadingEntries (am1-eval rec-merge) ⊖ am1-potential rec-merge ℤ.+ + am1-potential nxt-merge ≡ + 1
        einsert = E.begin
            leadingEntries (am1-eval rec-merge)
            ⊖     entries (am1-eval rec-merge)
            ℤ.+ + entries (am1-eval nxt-merge)        E.≡⟨ cong (λ x → leadingEntries (am1-eval rec-merge)
                                                                       ⊖     entries (am1-eval rec-merge)
                                                                       ℤ.+ + entries x) $
                                                           apply-elim empty∷ (insertTList≡ (reduce $ link x y)
                                                                                           (am1-eval rec-merge)) ⟩

            leadingEntries (am1-eval rec-merge)
            ⊖ entries (am1-eval rec-merge)
            ℤ.+ + entries (reduce $ insertTList≡ (reduce $ link x y) (am1-eval rec-merge))

                                                      E.≡⟨ tlist-insert-pot-invariant (reduce $ link x y) (am1-eval rec-merge) ⟩

            + 1                                                       E.∎

tlist-merge-in-linear-time≤ :  {{_ : Leq A}}
                               {l l' acc acc' : ℕ}
                            -> (l≤l' : l ≤ l')
                            -> (left : SparseTreeList A l acc)
                            -> (right : SparseTreeList A l' acc')
                            -> atime-full1 (tListMergeAm≤ l≤l' left right) ℤ.≤ + (entries left + entries right)
tlist-merge-in-linear-time≤ {l = l} {l' = l'} l≤l' left right with l <? l'
... | yes (s≤s l≤l'-1) = tlist-merge-in-linear-time≤ l≤l'-1 left (empty∷ right)
... | no l≮l'  = begin
        atime-full1 (tListMergeAm≡ left (tlist-subst (sym $ ≤-antisym l≤l' (≮⇒≥ l≮l')) right))

                                ≤⟨ tlist-merge-in-linear-time≡ left (tlist-subst (sym $ ≤-antisym l≤l' (≮⇒≥ l≮l')) right) ⟩

        + (entries left + entries (tlist-subst (sym $ ≤-antisym l≤l' (≮⇒≥ l≮l')) right))

                                ≡⟨ cong (λ x → + (entries left + x)) $ sym $ tlist-subst-elim entries (sym $ ≤-antisym l≤l' (≮⇒≥ l≮l')) right ⟩

        + (entries left + entries right) ∎
    where
        open ℤ-Props.≤-Reasoning

tlist-merge-in-linear-time :  {{_ : Leq A}}
                              {l l' acc acc' : ℕ}
                           -> (left : SparseTreeList A l acc)
                           -> (right : SparseTreeList A l' acc')
                           -> atime-full1 (tListMergeAm left right) ℤ.≤ + (entries left + entries right)
tlist-merge-in-linear-time {A = A} {l = l} {l' = l'} left right with ≤-total l l'
... | inj₁ l≤l' = begin
        atime-full1 (subst (Am1 (tlist-amortized' A) A) (sym $ m≤n⇒m⊓n≡m l≤l') $ tListMergeAm≤ l≤l' left right)

                                ≡⟨ subst-appl' atime-full1 (sym $ m≤n⇒m⊓n≡m l≤l') $ tListMergeAm≤ l≤l' left right ⟩

        atime-full1 (tListMergeAm≤ l≤l' left right)

                                ≤⟨ tlist-merge-in-linear-time≤ l≤l' left right ⟩

        + (entries left + entries right) ∎
    where
        open ℤ-Props.≤-Reasoning
... | inj₂ l'≤l = begin
        atime-full1 (subst (Am1 (tlist-amortized' A) A) (sym $ m≤n⇒n⊓m≡m l'≤l) $ tListMergeAm≤ l'≤l right left)

                                ≡⟨ subst-appl' atime-full1 (sym $ m≤n⇒n⊓m≡m l'≤l) $ tListMergeAm≤ l'≤l right left ⟩

        atime-full1 (tListMergeAm≤ l'≤l right left)

                                ≤⟨ tlist-merge-in-linear-time≤ l'≤l right left ⟩

        + (entries right + entries left)

                                ≡⟨ cong (+_) $ +-comm (entries right) (entries left) ⟩

        + (entries left + entries right) ∎
    where
        open ℤ-Props.≤-Reasoning

merge-in-log-time :  {{_ : Leq A}}
                     {l l' acc acc' : ℕ}
                  -> (left : SparseTreeList A l acc)
                  -> (right : SparseTreeList A l' acc')
                  -> atime-full1 (tListMergeAm left right) ℤ.≤ + 2 * 1+⌊log₂ acc ⊔ acc' ⌋
merge-in-log-time {acc = acc} {acc' = acc'} left right = ℤ≤.begin
        atime-full1 (tListMergeAm left right)    ℤ≤.≤⟨ tlist-merge-in-linear-time left right ⟩
        + (entries left + entries right)         ℤ≤.≤⟨ ℤ.+≤+ $ begin

            entries left + entries right                     ≤⟨ +-monoˡ-≤ _ $ len≤⌊log₂acc⌋ left ⟩
            1+⌊log₂ acc ⌋ + entries right                    ≤⟨ +-monoˡ-≤ _ $ 1+⌊log₂⌋-mono $ m≤m⊔n acc acc' ⟩
            1+⌊log₂ acc ⊔ acc' ⌋ + entries right             ≤⟨ +-monoʳ-≤ _ $ len≤⌊log₂acc⌋ right ⟩
            1+⌊log₂ acc ⊔ acc' ⌋ + 1+⌊log₂ acc' ⌋            ≤⟨ +-monoʳ-≤ _ $ 1+⌊log₂⌋-mono $ n≤m⊔n acc acc' ⟩
            1+⌊log₂ acc ⊔ acc' ⌋ + 1+⌊log₂ acc ⊔ acc' ⌋      ≡⟨⟩
            2 * 1+⌊log₂ acc ⊔ acc' ⌋                         ∎
                                                  ⟩
        + (2 * 1+⌊log₂ acc ⊔ acc' ⌋)              ℤ≤.∎
    where
        open ℤ-Props renaming (module ≤-Reasoning to ℤ≤) using ()
        open ≤-Reasoning

findMin : {l acc : ℕ} -> SparseTreeList A l (suc acc) -> DecTree A A 1+⌊log₂ (suc acc) ⌋
findMin ts = delay-≤ (len≤⌊log₂acc⌋ ts) $ findMin' ts
    where
        findMin'' : {l acc : ℕ} -> A -> (ts : SparseTreeList A l acc) -> DecTree A A (entries ts)
        findMin'' a [] = return a
        findMin'' a (empty∷ ts) = findMin'' a ts
        findMin'' a (entry node ∷ ts) = if' a ≤? (tVal node) then findMin'' a ts else findMin'' (tVal node) ts
        findMin' : {l acc : ℕ} -> (ts : SparseTreeList A l (suc acc)) -> DecTree A A (entries ts)
        findMin' (empty∷ ts) = findMin' ts
        findMin' (entry node ∷ ts) = delay' 1 $ findMin'' (tVal node) ts

cum-acc : {l : ℕ} -> DescList (BinomialTree A) l -> ℕ
cum-acc D[ _ ] = 1
cum-acc (_D∷_ {l = l} _ dl) = cum-acc dl + 2 ^ (suc l)

cum-acc≡2^l : {l : ℕ} -> (dl : DescList (BinomialTree A) l) -> suc (cum-acc dl) ≡ 2 ^ (suc l)
cum-acc≡2^l D[ _ ] = refl
cum-acc≡2^l {l = l} (_D∷_ {l = l-1} _ dl) = cong (_+ 2 ^ l) $ cum-acc≡2^l dl


inner-acc : {l : ℕ} -> BinomialTree A l -> ℕ
inner-acc (Leaf _) = 0
inner-acc (Node _ ts) = cum-acc ts

inner-acc≡2^l : {l : ℕ} -> (t : BinomialTree A l) -> suc (inner-acc t) ≡ 2 ^ l
inner-acc≡2^l (Leaf _) = refl
inner-acc≡2^l (Node _ ts) = cum-acc≡2^l ts

desclist-2-sparselist : {l : ℕ} -> (dl : DescList (BinomialTree A) l) -> SparseTreeList A 0 (cum-acc dl)
desclist-2-sparselist dl = tlist-subst-acc (+-identityʳ $ cum-acc dl) $ dl-2-sparse dl []
    where
        dl-2-sparse : {l acc : ℕ} -> (dl : DescList (BinomialTree A) l) -> SparseTreeList A (suc l) acc -> SparseTreeList A 0 (cum-acc dl + acc)
        dl-2-sparse {acc = acc} D[ x ] ts = entry_∷_ {acc'≡2^l+acc = refl} x ts
        dl-2-sparse {l = l} {acc = acc} (x D∷ dl) ts = tlist-subst-acc (sym $ +-assoc (cum-acc dl) (2 ^ l) acc) $ dl-2-sparse dl (entry_∷_ {acc'≡2^l+acc = refl} x ts)


inner-trees : {l : ℕ} -> (t : BinomialTree A l) -> SparseTreeList A 0 (inner-acc t)
inner-trees (Leaf _) = []
inner-trees (Node _ ts) = desclist-2-sparselist ts

record RemoveTree (A : Set a) (l : ℕ) (acc : ℕ) : Set a where
     field
         {l'} : ℕ
         {acc'} : ℕ
         min : A
         tree : BinomialTree A l'
         rem-heap : SparseTreeList A l acc'
         full-heap : SparseTreeList A l acc
         acc≡acc'+inner : acc ≡ acc' + suc (inner-acc tree)


find-and-remove-min-tree : {l acc : ℕ} -> (ts : SparseTreeList A l (suc acc)) -> DecTree A (RemoveTree A l (suc acc)) 1+⌊log₂ suc acc ⌋
find-and-remove-min-tree ts = delay-≤ (len≤⌊log₂acc⌋ ts) $ find-and-remove-min' ts
    where
        ext-rt-empty : {l acc : ℕ} -> RemoveTree A (suc l) acc -> RemoveTree A l acc
        ext-rt-empty record { min = min ; tree = tree ; rem-heap = rem-heap ; full-heap = full-heap ; acc≡acc'+inner = accinn}
                     = record { min = min ; tree = tree ; rem-heap = empty∷ rem-heap ; full-heap = empty∷ full-heap ; acc≡acc'+inner = accinn}
        ext-rt-entry : {l acc : ℕ} -> BinomialTree A l -> RemoveTree A (suc l) acc -> RemoveTree A l (2 ^ l + acc)
        ext-rt-entry {l = l} t record { min = min ; tree = tree ; rem-heap = rem-heap ; full-heap = full-heap ; acc≡acc'+inner = accinn }
                     = record {
                         min = min
                       ; tree = tree
                       ; rem-heap =  entry_∷_ {acc'≡2^l+acc = refl} t rem-heap
                       ; full-heap = entry_∷_ {acc'≡2^l+acc = refl} t full-heap
                       ; acc≡acc'+inner = trans (cong (λ x → 2 ^ l + x) accinn) (sym $ +-assoc (2 ^ l) _ _)
                     }
        swap-rt : {l acc : ℕ} -> BinomialTree A l -> RemoveTree A (suc l) acc -> RemoveTree A l (2 ^ l + acc)
        swap-rt {acc = acc} node record { full-heap = full-heap ; acc≡acc'+inner = acc+inn }
                = record {
                    min = (tVal node)
                  ; tree = node
                  ; rem-heap = empty∷ full-heap
                  ; full-heap = entry_∷_ {acc'≡2^l+acc = refl} node full-heap
                  ; acc≡acc'+inner = trans (cong (_+ acc) $ sym $ inner-acc≡2^l node) (+-comm _ acc)
                }
        find-and-remove-min' : {l acc : ℕ} -> (ts : SparseTreeList A l (suc acc)) -> DecTree A (RemoveTree A l (suc acc)) (entries ts)
        find-and-remove-min' (empty∷ ts) = find-and-remove-min' ts <&> λ rt -> ext-rt-empty rt
        find-and-remove-min' (entry_∷_ {acc = acc@(suc acc-1)} {acc'≡2^l+acc = pf} node ts) =
                                    height-≡ (+-comm _ 1) $ do
                                        rt <- find-and-remove-min' ts
                                        if' (RemoveTree.min rt) ≤? (tVal node)
                                            then return (subst (RemoveTree _ _) (sym pf) $ ext-rt-entry node rt)
                                            else return (subst (RemoveTree _ _) (sym pf) $ swap-rt node rt)
        find-and-remove-min' {l = l} (entry_∷_ {acc = zero} {acc'≡2^l+acc = pf} node ts) =
                                    delay-≤ z≤n $
                                    return $ subst (RemoveTree _ _) (sym pf) $
                                           record { min = (tVal node)
                                                  ; tree = node
                                                  ; rem-heap = []
                                                  ; full-heap = entry_∷_ {acc'≡2^l+acc = refl} node []
                                                  ; acc≡acc'+inner = trans (+-identityʳ $ 2 ^ l) (sym $ inner-acc≡2^l node)
                                           }

deleteMin : {l acc : ℕ} -> (ts : SparseTreeList A l (suc acc)) -> Am1 (tlist-amortized' A) A 0
deleteMin {A = A} {l = l} ts = Am1.init-comp {am = tlist-amortized' A} rem λ rt → tListMergeAm≤ z≤n (inner-trees $ RemoveTree.tree rt) (RemoveTree.rem-heap rt)
    where
        rem = find-and-remove-min-tree ts


deleteMin-in-log-time :  {{_ : Leq A}}
                         {l acc : ℕ}
                      -> (ts : SparseTreeList A l (suc acc))
                      -> atime-full1 (deleteMin ts) ℤ.≤ + 3 * 1+⌊log₂ suc acc ⌋
deleteMin-in-log-time {acc = acc} ts = ℤ-Props.+-monoʳ-≤ (+ 1+⌊log₂ suc acc ⌋) $ begin
        atime-full1 (tListMergeAm≤ z≤n (inner-trees $ RemoveTree.tree rem') (RemoveTree.rem-heap rem'))
                ≤⟨ tlist-merge-in-linear-time≤ z≤n (inner-trees $ RemoveTree.tree rem') (RemoveTree.rem-heap rem') ⟩
        + (entries (inner-trees $ RemoveTree.tree rem') + entries (RemoveTree.rem-heap rem'))
                ≤⟨ ℤ-Props.+-monoʳ-≤ (+ (entries $ inner-trees $ RemoveTree.tree rem')) $ ℤ.+≤+ $ len≤⌊log₂acc⌋ (RemoveTree.rem-heap rem') ⟩
        + (entries (inner-trees $ RemoveTree.tree rem') + 1+⌊log₂ RemoveTree.acc' rem' ⌋)
                ≤⟨ ℤ-Props.+-monoʳ-≤ (+ entries (inner-trees $ RemoveTree.tree rem')) $ ℤ.+≤+ $ 1+⌊log₂⌋-mono acc'≤acc ⟩
        + (entries (inner-trees $ RemoveTree.tree rem') + 1+⌊log₂ suc acc ⌋)
                ≤⟨ ℤ-Props.+-monoˡ-≤ (+ 1+⌊log₂ suc acc ⌋) $ ℤ.+≤+ $ len≤⌊log₂acc⌋ $ inner-trees $ RemoveTree.tree rem' ⟩
        + (1+⌊log₂ inner-acc $ RemoveTree.tree rem' ⌋ + 1+⌊log₂ suc acc ⌋)
                ≤⟨ ℤ-Props.+-monoˡ-≤ (+ 1+⌊log₂ suc acc ⌋) $ ℤ.+≤+ $ 1+⌊log₂⌋-mono $ n≤1+n _ ⟩
        + (1+⌊log₂ suc $ inner-acc $ RemoveTree.tree rem' ⌋ + 1+⌊log₂ suc acc ⌋)
                ≤⟨ ℤ-Props.+-monoˡ-≤ (+ 1+⌊log₂ suc acc ⌋) $ ℤ.+≤+ $ 1+⌊log₂⌋-mono accinner≤acc ⟩
        + 2 * 1+⌊log₂ suc acc ⌋ ∎
    where
        open ℤ-Props.≤-Reasoning
        rem = find-and-remove-min-tree ts
        rem' = reduce rem
        acc'≤acc = m+n≤o⇒m≤o (RemoveTree.acc' rem') (≤-reflexive $ sym $ RemoveTree.acc≡acc'+inner rem')
        accinner≤acc = m+n≤o⇒n≤o (RemoveTree.acc' rem') (≤-reflexive $ sym $ RemoveTree.acc≡acc'+inner rem')
