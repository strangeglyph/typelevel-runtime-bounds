module AmortizedTime where

open import Level using (Level) renaming (suc to lsuc ; _⊔_ to _l⊔_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Integer as ℤ using (ℤ ; _⊖_ ; +_ ; -_)
import Data.Integer.Properties as ℤ-Props
open import Data.Vec
open import Function

open import Relation.Binary.PropositionalEquality hiding ([_])

open import Int.Props.Telescope
open import DecTree
open import Leq

private
    variable
        a b c i m n x : Level
        Compare : Set b
        I : Set i
        M : Set m
        N : Set n
        X : Set x
        A : I -> Set a
        P1 : M -> I -> Set a
        P2 : M -> N -> I -> Set a



record Amortized {I : Set i} (A : I -> Set a) : Set (a l⊔ i) where
    field
        {i₀} : I
        initial : A i₀
        potential : {i : I} -> A i -> ℕ
        init≡0 : potential initial ≡ 0

record Amortized1 {A : Set a} {I : Set i} (P : A -> I -> Set b) : Set (a l⊔ b l⊔ i) where
    field
        {i₀} : I
        initial : (a : A) -> P a i₀
        potential : {a : A} {i : I} -> P a i -> ℕ
        init≡0 : (a : A) -> potential (initial a) ≡ 0


data Am {I : Set i} {A : I -> Set a} (am : Amortized A) (C : Set b) : Set (lsuc (a l⊔ i l⊔ b)) where
    base : (x : A (Amortized.i₀ am)) -> {x ≡ Amortized.initial am} -> Am am C
    init-comp :  {B : Set a}
                 {time : ℕ}
              -> DecTree C B time
              -> (B -> Am am C)
              -> Am am C
    step :  {next : {i : I} -> A i -> I}
            {time : {i : I} -> A i -> ℕ}
         -> Am am C
         -> ({i : I} -> (x : A i) -> DecTree C (A $ next x) (time x))
         -> Am am C
    am-bind :  {J : Set i}
               {B : J -> Set a}
               {am' : Amortized B}
            -> Am am' C
            -> ({j : J} -> (x : B j) -> Am am C)
            -> Am am C
    am-map :  {J : Set i}
              {B : J -> Set a}
              {am' : Amortized B}
              {imap : {j : J} -> B j -> I}
              (f : {j : J} -> (x : B j) -> A $ imap x)
              {map-is-pot-invariant : {j : J} -> (x : B j) -> Amortized.potential am' x ≡ Amortized.potential am (f x)}
           -> Am am' C
           -> Am am  C

data Am1 {A : Set a} {I : Set i} {P : A -> I -> Set b} (am : Amortized1 P) (C : Set c) : A -> Set (lsuc (a l⊔ i l⊔ b l⊔ c)) where
    base :  {a : A}
         -> (v : P a (Amortized1.i₀ am))
         -> {v ≡ Amortized1.initial am a}
         -> Am1 am C a
    init-comp :  {B : Set b}
                 {time : ℕ}
                 {a : A}
              -> DecTree C B time
              -> (B -> Am1 am C a)
              -> Am1 am C a
    step :  {nextA : A -> A}
            {nextI : {a : A} {i : I} -> P a i -> I}
            {time  : {a : A} {i : I} -> P a i -> ℕ}
            {a : A}
         -> Am1 am C a
         -> ({i : I} -> (x : P a i) -> DecTree C (P (nextA a) (nextI x)) (time x))
         -> Am1 am C (nextA a)

lift : {am : Amortized A} -> Am am Compare
lift {am = am} = base (Amortized.initial am) {refl}


lift1 : {P : M -> I -> Set a} {am : Amortized1 P} -> (m : M) -> Am1 am Compare m
lift1 {am = am} m = base (Amortized1.initial am m) {refl}


am-index : {I : Set i} -> {A : I -> Set a} -> {am : Amortized A} -> {{_ : Leq Compare}} -> Am am Compare -> I
am-eval : {am : Amortized A} -> {{_ : Leq Compare}} -> (v : Am am Compare) -> A (am-index v)

am-index {am = am} (base _) = Amortized.i₀ am
am-index (step {next} val _) = next (am-eval val)
am-index (am-map {imap = imap} _ val) = imap (am-eval val)
am-index (am-bind val trans) = am-index (trans (am-eval val))
am-index (init-comp comp trans) = am-index (trans $ reduce comp)

am-eval (base v) = v
am-eval (step val trans) = reduce $ trans $ am-eval val
am-eval (am-map f val) = f (am-eval val)
am-eval (am-bind val trans) = am-eval $ trans $ am-eval val
am-eval (init-comp comp trans) = am-eval $ trans $ reduce comp

am1-index : {P : M -> I -> Set a} {am : Amortized1 P} {{_ : Leq Compare}} {m : M} -> Am1 am Compare m -> I
am1-eval : {P : M -> I -> Set a} {am : Amortized1 P} {m : M} -> {{_ : Leq Compare}} -> (v : Am1 am Compare m) -> P m (am1-index v)

am1-index {am = am} (base _) = Amortized1.i₀ am
am1-index (step {nextI = nextI} val _) = nextI (am1-eval val)
am1-index (init-comp comp trans) = am1-index (trans $ reduce comp)

am1-eval (base v) = v
am1-eval (step val trans) = reduce $ trans $ am1-eval val
am1-eval (init-comp comp trans) = am1-eval $ trans $ reduce comp




am-potential : {am : Amortized A} -> {{_ : Leq Compare}} -> Am am Compare -> ℕ
am-potential {am = am} v = Amortized.potential am $ am-eval v

am1-potential : {P : M -> I -> Set a} {am : Amortized1 P} {m : M} {{_ : Leq Compare}} -> Am1 am Compare m -> ℕ
am1-potential {am = am} v = Amortized1.potential am $ am1-eval v


dtime-step : {am : Amortized A} -> {{_ : Leq Compare}} -> Am am Compare -> ℕ
dtime-step (base val) = 0
dtime-step (step {next} {time} val trans) = time $ am-eval val
dtime-step (am-map _ _) = 0
dtime-step (am-bind val trans) = 0
dtime-step (init-comp {_} {time} _ _) = time

dtime-full : {am : Amortized A} -> {{_ : Leq Compare}} -> Am am Compare -> ℕ
dtime-full (base val) = 0
dtime-full outer@(step inner _) = dtime-full inner + dtime-step outer
dtime-full (am-map _ val) = dtime-full val
dtime-full (am-bind val trans) = dtime-full val + dtime-full (trans $ am-eval val)
dtime-full (init-comp {_} {time} comp trans) = time + dtime-full (trans $ reduce comp)

dtime-step1 : {P : M -> I -> Set a} {am : Amortized1 P} {m : M} {{_ : Leq Compare}} -> Am1 am Compare m -> ℕ
dtime-step1 (base val) = 0
dtime-step1 (step {time = time} val trans) = time $ am1-eval val
dtime-step1 (init-comp {_} {time} _ _) = time

dtime-full1 : {P : M -> I -> Set a} {am : Amortized1 P} {m : M} {{_ : Leq Compare}} -> Am1 am Compare m -> ℕ
dtime-full1 (base val) = 0
dtime-full1 outer@(step inner _) = dtime-full1 inner + dtime-step1 outer
dtime-full1 (init-comp {_} {time} comp trans) = time + dtime-full1 (trans $ reduce comp)

atime-step : {am : Amortized A} -> {{_ : Leq Compare}} -> Am am Compare -> ℤ
atime-step (base val) = ℤ.0ℤ
atime-step (am-map _ _) = ℤ.0ℤ
atime-step (am-bind _ _) = ℤ.0ℤ
atime-step {am = am} (init-comp {_} {time} _ _) = + time
atime-step {am = am} v@(step val transform) = dtime-step v ⊖ pot-before ℤ.+ (+ pot-after)
    where
        val-before = am-eval val
        val-after = reduce $ transform $ val-before
        pot-before = Amortized.potential am $ val-before
        pot-after = Amortized.potential am val-after

atime-full : {am : Amortized A} -> {{_ : Leq Compare}} -> Am am Compare -> ℤ
atime-full (base val) = ℤ.0ℤ
atime-full v@(step val _) = atime-full val ℤ.+ atime-step v
atime-full (am-map _ val) = atime-full val
atime-full v@(init-comp comp trans) = atime-step v ℤ.+ atime-full (trans $ reduce comp)
atime-full (am-bind val trans) = atime-full val ℤ.+ atime-full (trans $ am-eval val)

atime-step1 : {P : M -> I -> Set a} {am : Amortized1 P} {m : M} {{_ : Leq Compare}} -> Am1 am Compare m -> ℤ
atime-step1 (base val) = ℤ.0ℤ
atime-step1 (init-comp {_} {time} _ _) = + time
atime-step1 {am = am} v@(step val transform) = dtime-step1 v ⊖ pot-before ℤ.+ (+ pot-after)
    where
        val-before = am1-eval val
        val-after = reduce $ transform $ val-before
        pot-before = Amortized1.potential am val-before
        pot-after = Amortized1.potential am val-after

atime-full1 : {P : M -> I -> Set a} {am : Amortized1 P} {m : M} {{_ : Leq Compare}} -> Am1 am Compare m -> ℤ
atime-full1 (base val) = ℤ.0ℤ
atime-full1 v@(init-comp comp trans) = atime-step1 v ℤ.+ atime-full1 (trans $ reduce comp)
atime-full1 v@(step val _) = atime-full1 val ℤ.+ atime-step1 v

-- atime is an upper bound on dtime
atime≥dtime : {am : Amortized A} -> {{_ : Leq Compare}} -> (v : Am am Compare) -> atime-full v ℤ.≥ + (dtime-full v + am-potential v)
atime≥dtime {am = am} (base v {v≡init}) = ℤ.+≤+ (≤-reflexive $ trans (cong (Amortized.potential am) v≡init) (Amortized.init≡0 am))
atime≥dtime v@(am-map f {map-pot-inv} val) = begin
        + (dtime-full val + am-potential v)          ≡⟨ cong (λ x → + (dtime-full val + x)) $ sym $ map-pot-inv (am-eval val)  ⟩
        + (dtime-full val + am-potential val)        ≤⟨ atime≥dtime val ⟩
        atime-full val                               ∎
    where
        open ℤ-Props.≤-Reasoning
atime≥dtime v@(init-comp {_} {time} comp trans) = begin
        + (time + dtime-full (trans $ reduce comp) + am-potential v)     ≡⟨ cong (+_) $ +-assoc time _ _ ⟩
        + (time + (dtime-full (trans $ reduce comp) + am-potential v))   ≤⟨ ℤ-Props.+-monoʳ-≤ (+ time) $ atime≥dtime (trans $ reduce comp) ⟩
        + time ℤ.+ atime-full (trans $ reduce comp)                      ∎
    where
        open ℤ-Props.≤-Reasoning
atime≥dtime (am-bind val trans) = begin
        + (dtime-full val + dtime-full (trans $ am-eval val) + am-potential (trans $ am-eval val))
                ≡⟨ cong (+_) $ +-assoc (dtime-full val) _ _ ⟩
        + (dtime-full val + (dtime-full (trans $ am-eval val) + am-potential (trans $ am-eval val)))
                ≤⟨ ℤ-Props.+-monoʳ-≤ (+ dtime-full val) $ atime≥dtime (trans $ am-eval val) ⟩
        + dtime-full val ℤ.+ atime-full (trans $ am-eval val)
                ≤⟨ ℤ-Props.+-monoˡ-≤ (atime-full $ trans $ am-eval val) $ ℤ.+≤+ $ m≤m+n (dtime-full val) (am-potential val) ⟩
        + (dtime-full val + am-potential val) ℤ.+ atime-full (trans $ am-eval val)
                ≤⟨ ℤ-Props.+-monoˡ-≤ _ $ atime≥dtime val ⟩
        atime-full val ℤ.+ atime-full (trans $ am-eval val)
                ∎
    where
        open ℤ-Props.≤-Reasoning
atime≥dtime v@(step val trans) = begin
        + (dtime-full val + dtime-step v + am-potential v)

                      ≡⟨ cong (ℤ._+ (+ am-potential v)) $ sym $ +-telescope (+ dtime-full val) (+ dtime-step v) (+ am-potential val) ⟩

        + (dtime-full val + am-potential val) ℤ.+ (+ dtime-step v ℤ.- + am-potential val) ℤ.+ + am-potential v

                      ≡⟨ cong (λ x → + (dtime-full val + am-potential val) ℤ.+ x ℤ.+ + am-potential v) $ ℤ-Props.[+m]-[+n]≡m⊖n (dtime-step v) (am-potential val) ⟩

        + (dtime-full val + am-potential val) ℤ.+ (dtime-step v ⊖ am-potential val) ℤ.+ + am-potential v

                      ≡⟨ ℤ-Props.+-assoc (+ (dtime-full val + am-potential val)) (dtime-step v ⊖ am-potential val) (+ am-potential v) ⟩

        + (dtime-full val + am-potential val) ℤ.+ (dtime-step v ⊖ am-potential val ℤ.+ + am-potential v)

                      ≡⟨⟩

        + (dtime-full val + am-potential val) ℤ.+ atime-step v

                      ≤⟨ ℤ-Props.+-monoˡ-≤ _ $ atime≥dtime val ⟩

        atime-full val ℤ.+ atime-step v   ∎
    where
        open ℤ-Props.≤-Reasoning




atime1≡dtime1+pot : {P : M -> I -> Set a} {am : Amortized1 P} {m : M} {{_ : Leq Compare}} -> (v : Am1 am Compare m) -> atime-full1 v ≡ + (dtime-full1 v + am1-potential v)
atime1≡dtime1+pot {am = am} (base {a} v {v≡init}) = sym $ begin
        + Amortized1.potential am v                           ≡⟨ cong (+_) $ cong (Amortized1.potential am) v≡init ⟩
        + Amortized1.potential am (Amortized1.initial am a)   ≡⟨ cong (+_) $ Amortized1.init≡0 am a ⟩
        ℤ.0ℤ                                                  ∎
    where
        open ≡-Reasoning
atime1≡dtime1+pot {am = am} v@(init-comp {_} {time} comp trans) = begin
        + time ℤ.+ atime-full1 (trans $ reduce comp)                       ≡⟨ cong (λ x → + time ℤ.+ x) $ atime1≡dtime1+pot (trans $ reduce comp) ⟩
        + (time + (dtime-full1 (trans $ reduce comp) + am1-potential v))   ≡⟨ cong (+_) $ sym $ +-assoc time _ _ ⟩
        + (time + dtime-full1 (trans $ reduce comp) + am1-potential v)     ∎
    where
        open ≡-Reasoning
atime1≡dtime1+pot v@(step val trans) = begin
        atime-full1 v
                                                        ≡⟨⟩
        atime-full1 val ℤ.+ atime-step1 v
                                                        ≡⟨ cong (ℤ._+ atime-step1 v) $ atime1≡dtime1+pot val ⟩
            + (dtime-full1 val + am1-potential val)
        ℤ.+ atime-step1 v
                                                       ≡⟨ cong (ℤ._+ atime-step1 v) $
                                                          ℤ-Props.pos-+-commute (dtime-full1 val) (am1-potential val) ⟩
            + dtime-full1 val
        ℤ.+ + am1-potential val
        ℤ.+ atime-step1 v
                                                       ≡⟨⟩
            + dtime-full1 val
        ℤ.+ + am1-potential val
        ℤ.+ (dtime-step1 v ⊖ am1-potential val
             ℤ.+ + am1-potential v)
                                                       ≡⟨ sym $ ℤ-Props.+-assoc
                                                                  (+ dtime-full1 val ℤ.+ + am1-potential val)
                                                                  (dtime-step1 v ⊖ am1-potential val)
                                                                  (+ am1-potential v) ⟩
            + dtime-full1 val
        ℤ.+ + am1-potential val
        ℤ.+ (dtime-step1 v ⊖ am1-potential val)
        ℤ.+ + am1-potential v
                                                       ≡⟨ cong (λ x →     + dtime-full1 val
                                                                      ℤ.+ + am1-potential val
                                                                      ℤ.+ x
                                                                      ℤ.+ + am1-potential v) $
                                                          sym $ ℤ-Props.[+m]-[+n]≡m⊖n (dtime-step1 v) (am1-potential val) ⟩
            + dtime-full1 val
        ℤ.+ + am1-potential val
        ℤ.+ (+ dtime-step1 v ℤ.- + am1-potential val)
        ℤ.+ + am1-potential v
                                                       ≡⟨ cong (ℤ._+ (+ am1-potential v)) $
                                                          +-telescope (+ dtime-full1 val) (+ dtime-step1 v) (+ am1-potential val) ⟩
            + dtime-full1 val
        ℤ.+ (+ dtime-step1 v)
        ℤ.+ (+ am1-potential v)
                                                       ≡⟨ cong (ℤ._+ (+ am1-potential v)) $
                                                          sym $ ℤ-Props.pos-+-commute (dtime-full1 val) (dtime-step1 v) ⟩
            + dtime-full1 v
        ℤ.+ + am1-potential v
                                                       ≡⟨ sym $ ℤ-Props.pos-+-commute (dtime-full1 v) (am1-potential v) ⟩
            + (dtime-full1 v + am1-potential v)          ∎
    where
        open ≡-Reasoning


