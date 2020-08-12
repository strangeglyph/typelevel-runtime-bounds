module AmortizedTime where

open import Level using (Level) renaming (suc to lsuc ; _⊔_ to _l⊔_)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Integer as ℤ using (ℤ ; _⊖_ ; +_ ; -_)
import Data.Integer.Properties as ℤ-Props
open import Function

open import Relation.Binary.PropositionalEquality hiding ([_])

open import Int.Props.Telescope
open import DecTree
open import Leq

private
    variable
        a b i : Level
        Compare : Set b
        I : Set i
        A : I -> Set a


record Amortized {I : Set i} (A : I -> Set a) : Set (a l⊔ i) where
    field
        {i₀} : I
        initial : A i₀
        potential : {i : I} -> A i -> ℕ
        init≡0 : potential initial ≡ 0


data Am {I : Set i} {A : I -> Set a} (am : Amortized A) (C : Set b) : Set (lsuc a l⊔ i l⊔ lsuc b) where
    base : (x : A (Amortized.i₀ am)) -> {x ≡ Amortized.initial am} -> Am am C
    step :  {next : {i : I} -> A i -> I}
            {time : {i : I} -> A i -> ℕ}
         -> Am am C
         -> ({i : I} -> (x : A i) -> DecTree C (A $ next x) (time x))
         -> Am am C


lift : {am : Amortized A} -> Am am Compare
lift {am = am} = base (Amortized.initial am) {refl}

am-index : {I : Set i} -> {A : I -> Set a} -> {am : Amortized A} -> {{_ : Leq Compare}} -> Am am Compare -> I
am-eval : {am : Amortized A} -> {{_ : Leq Compare}} -> (v : Am am Compare) -> A (am-index v)

am-index {am = am} (base _) = Amortized.i₀ am
am-index (step {next} val _) = next (am-eval val)

am-eval (base v) = v
am-eval (step val trans) = reduce $ trans $ am-eval val

am-potential : {am : Amortized A} -> {{_ : Leq Compare}} -> Am am Compare -> ℕ
am-potential {am = am} v = Amortized.potential am $ am-eval v

dtime-step : {am : Amortized A} -> {{_ : Leq Compare}} -> Am am Compare -> ℕ
dtime-step (base val) = 0
dtime-step (step {next} {time} val trans) = time $ am-eval val

dtime-full : {am : Amortized A} -> {{_ : Leq Compare}} -> Am am Compare -> ℕ
dtime-full (base val) = 0
dtime-full outer@(step inner _) = dtime-full inner + dtime-step outer

atime-step : {am : Amortized A} -> {{_ : Leq Compare}} -> Am am Compare -> ℤ
atime-step (base val) = ℤ.0ℤ
atime-step {am = am} v@(step val transform) = dtime-step v ⊖ pot-before ℤ.+ (+ pot-after)
    where
        val-before = am-eval val
        val-after = reduce $ transform $ val-before
        pot-before = Amortized.potential am $ val-before
        pot-after = Amortized.potential am val-after

atime-full : {am : Amortized A} -> {{_ : Leq Compare}} -> Am am Compare -> ℤ
atime-full (base val) = ℤ.0ℤ
atime-full v@(step val _) = atime-full val ℤ.+ atime-step v



-- atime is an upper bound on dtime
atime≡dtime+pot : {am : Amortized A} -> {{_ : Leq Compare}} -> (v : Am am Compare) -> atime-full v ≡ + (dtime-full v + am-potential v)
atime≡dtime+pot {am = am} (base v {v≡init}) = sym $ begin
        + Amortized.potential am v                        ≡⟨ cong (+_) $ cong (Amortized.potential am) v≡init ⟩
        + Amortized.potential am (Amortized.initial am)   ≡⟨ cong (+_) $ Amortized.init≡0 am ⟩
        ℤ.0ℤ                                              ∎
    where
        open ≡-Reasoning
atime≡dtime+pot {{am}} v@(step val trans) = begin
        atime-full v
                                                        ≡⟨⟩
        atime-full val ℤ.+ atime-step v
                                                        ≡⟨ cong (ℤ._+ atime-step v) $ atime≡dtime+pot val ⟩
            + (dtime-full val + am-potential val)
        ℤ.+ atime-step v
                                                       ≡⟨ cong (ℤ._+ atime-step v) $
                                                          ℤ-Props.pos-+-commute (dtime-full val) (am-potential val) ⟩
            + dtime-full val
        ℤ.+ + am-potential val
        ℤ.+ atime-step v
                                                       ≡⟨⟩
            + dtime-full val
        ℤ.+ + am-potential val
        ℤ.+ (dtime-step v ⊖ am-potential val
             ℤ.+ + am-potential v)
                                                       ≡⟨ sym $ ℤ-Props.+-assoc
                                                                  (+ dtime-full val ℤ.+ + am-potential val)
                                                                  (dtime-step v ⊖ am-potential val)
                                                                  (+ am-potential v) ⟩
            + dtime-full val
        ℤ.+ + am-potential val
        ℤ.+ (dtime-step v ⊖ am-potential val)
        ℤ.+ + am-potential v
                                                       ≡⟨ cong (λ x →     + dtime-full val
                                                                      ℤ.+ + am-potential val
                                                                      ℤ.+ x
                                                                      ℤ.+ + am-potential v) $
                                                          sym $ ℤ-Props.[+m]-[+n]≡m⊖n (dtime-step v) (am-potential val) ⟩
            + dtime-full val
        ℤ.+ + am-potential val
        ℤ.+ (+ dtime-step v ℤ.- + am-potential val)
        ℤ.+ + am-potential v
                                                       ≡⟨ cong (ℤ._+ (+ am-potential v)) $
                                                          +-telescope (+ dtime-full val) (+ dtime-step v) (+ am-potential val) ⟩
            + dtime-full val
        ℤ.+ (+ dtime-step v)
        ℤ.+ (+ am-potential v)
                                                       ≡⟨ cong (ℤ._+ (+ am-potential v)) $
                                                          sym $ ℤ-Props.pos-+-commute (dtime-full val) (dtime-step v) ⟩
            + dtime-full v
        ℤ.+ + am-potential v
                                                       ≡⟨ sym $ ℤ-Props.pos-+-commute (dtime-full v) (am-potential v) ⟩
            + (dtime-full v + am-potential v)          ∎
    where
        open ≡-Reasoning






