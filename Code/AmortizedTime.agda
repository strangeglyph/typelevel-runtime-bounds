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



data ParList (a : Level) : Set (lsuc a) where
    nil : ParList a
    _consa_ : Set a -> ParList a -> ParList a
    _cons0_ : Set   -> ParList a -> ParList a

_+++_ : ParList a -> ParList a -> ParList a
nil +++ ys = ys
(x consa xs) +++ ys = x consa (xs +++ ys)
(x cons0 xs) +++ ys = x cons0 (xs +++ ys)

infixr 40 _consa_
infixr 40 _cons0_


IxType : ParList (lsuc a) -> Set (lsuc a)
IxType {a} nil = Set a
IxType (x consa xs) = x -> IxType xs
IxType (x cons0 xs) = x -> IxType xs


sel-level : ParList (lsuc a) -> Level
sel-level {a} nil = a
sel-level (_ cons0 p) = sel-level p
sel-level {a} (_ consa p) = lsuc a l⊔ sel-level p

sel-level' : ParList (lsuc a) -> Level -> Level
sel-level' nil b = b
sel-level' {a} (_ consa xs) b = lsuc a l⊔ sel-level' xs b
sel-level' (_ cons0 xs) b = sel-level' xs b

IxType' : (pars : ParList (lsuc a)) -> (b : Level) -> Set (sel-level' pars $ lsuc b)
IxType' nil b = Set b
IxType' (x consa pars) b = x -> IxType' pars b
IxType' (x cons0 pars) b = x -> IxType' pars b

{-}
IxTypeConcat : {pars : ParList (lsuc a)} -> IxType' pars b -> Set c -> IxType' pars (b l⊔ c)
IxTypeConcat {pars = nil} P C = P -> C
IxTypeConcat {pars = X consa pars} P C = {!(x : X) -> IxTypeConcat (P x) C!}
IxTypeConcat {pars = X cons0 pars} P C = {!!}
-}

_==>_ : (pars : ParList (lsuc a)) -> Set b -> Set (sel-level' pars b)
nil ==> ty = ty
(x consa xs) ==> ty = x -> (xs ==> ty)
(x cons0 xs) ==> ty = x -> (xs ==> ty)

_I==>_ : (pars : ParList (lsuc a)) -> Set b -> Set (sel-level' pars b)
nil I==> ty = ty
(x consa xs) I==> ty = {x} -> (xs I==> ty)
(x cons0 xs) I==> ty = {x} -> (xs I==> ty)


Selector : {p : ParList (lsuc a)} -> IxType p  -> Set (sel-level p)
Selector {p = nil} P = P
Selector {p = X consa p} P = (x : X) -> Selector {p = p} (P x)
Selector {p = X cons0 p} P = (x : X) -> Selector {p = p} (P x)

Selector+Extra :  (type-pars : ParList (lsuc a))
               -> (extra-pars : ParList (lsuc a))
               -> IxType type-pars
               -> Set (sel-level type-pars l⊔ sel-level extra-pars)
Selector+Extra nil nil P = P
Selector+Extra nil (X consa extra-pars) P = X -> Selector+Extra nil extra-pars P
Selector+Extra nil (X cons0 extra-pars) P = X -> Selector+Extra nil extra-pars P
Selector+Extra (X consa type-pars) extra-pars P = (x : X) -> Selector+Extra type-pars extra-pars (P x)
Selector+Extra (X cons0 type-pars) extra-pars P = (x : X) -> Selector+Extra type-pars extra-pars (P x)

ImplicitSelector : {p : ParList (lsuc a)} -> IxType p -> Set (sel-level p)
ImplicitSelector {p = nil} P = P
ImplicitSelector {p = X consa p} P = {x : X} -> ImplicitSelector {p = p} (P x)
ImplicitSelector {p = X cons0 p} P = {x : X} -> ImplicitSelector {p = p} (P x)

ImplicitSelector+Fun : {p : ParList (lsuc a)} -> IxType p -> Set b -> Set (sel-level p l⊔ b)
ImplicitSelector+Fun {p = nil} P f = P -> f
ImplicitSelector+Fun {p = X consa p} P f = {x : X} -> ImplicitSelector+Fun {p = p} (P x) f
ImplicitSelector+Fun {p = X cons0 p} P f = {x : X} -> ImplicitSelector+Fun {p = p} (P x) f


ImplicitSelector+ParameterizedFun : {p : ParList (lsuc a)} -> (P : IxType p) -> (ImplicitSelector+Fun {p = p} P (Set b)) -> Set (sel-level p l⊔ b)
ImplicitSelector+ParameterizedFun {p = nil} P f = (x : P) -> f x
ImplicitSelector+ParameterizedFun {p = X consa p} P f = {x : X} -> ImplicitSelector+ParameterizedFun (P x) (f {x})
ImplicitSelector+ParameterizedFun {p = X cons0 p} P f = {x : X} -> ImplicitSelector+ParameterizedFun (P x) (f {x})




data Explicitness : Set where
    Explicit : Explicitness
    Implicit : Explicitness

data FunSpaceParams {a : Level} : ParList (lsuc a) -> Set (lsuc (lsuc a)) where
    Param : {pars : ParList (lsuc a)} -> (pars' : ParList (lsuc a)) -> Explicitness -> FunSpaceParams pars -> FunSpaceParams (pars' +++ pars)
    Param' : (pars : ParList (lsuc a)) -> Explicitness -> FunSpaceParams pars
    Extra : {pars : ParList (lsuc a)} -> ParList (lsuc a) -> Explicitness -> FunSpaceParams pars -> FunSpaceParams pars
    Extra' : ParList (lsuc a) -> Explicitness -> FunSpaceParams nil

fspace-level : {pars : ParList (lsuc a)} -> FunSpaceParams pars -> Level
fspace-level (Param pars _ more) = sel-level' pars (fspace-level more)
fspace-level {a} (Param' pars _) = sel-level' pars a
fspace-level (Extra pars _ more) = sel-level' pars (fspace-level more)
fspace-level {a} (Extra' pars _) = sel-level' pars a

FunSpace : {pars : ParList (lsuc a)} -> (head : FunSpaceParams pars) -> IxType pars -> Set (fspace-level head)
FunSpace (Param nil x more) P = FunSpace more P
FunSpace (Param (X consa pars) Explicit more) P = (x : X) -> FunSpace (Param pars Explicit more) (P x)
FunSpace (Param (X cons0 pars) Explicit more) P = (x : X) -> FunSpace (Param pars Explicit more) (P x)
FunSpace (Param (X consa pars) Implicit more) P = {x : X} -> FunSpace (Param pars Implicit more) (P x)
FunSpace (Param (X cons0 pars) Implicit more) P = {x : X} -> FunSpace (Param pars Implicit more) (P x)
FunSpace (Param' nil x) P = P
FunSpace (Param' (X consa pars) Explicit) P = (x : X) -> FunSpace (Param' pars Explicit) (P x)
FunSpace (Param' (X cons0 pars) Explicit) P = (x : X) -> FunSpace (Param' pars Explicit) (P x)
FunSpace (Param' (X consa pars) Implicit) P = {x : X} -> FunSpace (Param' pars Implicit) (P x)
FunSpace (Param' (X cons0 pars) Implicit) P = {x : X} -> FunSpace (Param' pars Implicit) (P x)
FunSpace (Extra pars Explicit more) P = pars ==> (FunSpace more P)
FunSpace (Extra pars Implicit more) P = pars I==> (FunSpace more P)
FunSpace (Extra' pars Explicit) P = pars ==> P
FunSpace (Extra' pars Implicit) P = pars I==> P

{-}
fspace-level' : ParList (lsuc a) -> ParList (lsuc a) -> Level
fspace-level' xs ys = sel-level' xs (sel-level ys)

FunSpace' :  Explicitness -> (pars : ParList (lsuc a))
          -> Explicitness -> (pars' : ParList (lsuc a))
          -> IxType pars
          -> Set (fspace-level' pars pars')
FunSpace' x pars y extra P = {!!}
-}

ISelect-Concat :  {p : ParList (lsuc a)}
                  {tyA : IxType p}
                  {tyB : Set b}
               -> ImplicitSelector+Fun tyA tyB
               -> {tyC : Set c}
               -> (tyB -> tyC)
               -> ImplicitSelector+Fun tyA tyC
ISelect-Concat {p = nil} iselect f = f ∘ iselect
ISelect-Concat {p = X consa p} iselect f {x} = ISelect-Concat {p = p} (iselect {x}) f
ISelect-Concat {p = X cons0 p} iselect f {x} = ISelect-Concat {p = p} (iselect {x}) f


record Amortized {I : Set i} (A : I -> Set a) : Set (a l⊔ i) where
    field
        {i₀} : I
        initial : A i₀
        potential : {i : I} -> A i -> ℕ
        init≡0 : potential initial ≡ 0
    
record Amortized' {I : Set i} (A : I -> Set a) (X : Set x) : Set (a l⊔ i l⊔ x) where
    field
        {i₀} : I
        initial : X -> A i₀
        potential : {i : I} -> A i -> ℕ
        init≡0 : (x : X) -> potential (initial x) ≡ 0

record Amortized1 {A : Set a} {I : Set i} (P : A -> I -> Set b) : Set (a l⊔ b l⊔ i) where
    field
        {i₀} : I
        initial : (a : A) -> P a i₀
        potential : {a : A} {i : I} -> P a i -> ℕ
        init≡0 : (a : A) -> potential (initial a) ≡ 0

record Amortized1' {A : Set a} {I : Set i} (P : A -> I -> Set b) (C : Set c) : Set (a l⊔ b l⊔ c l⊔ i) where
    field
        {i₀} : I
        initial : (a : A) -> C -> P a i₀
        potential : {a : A} {i : I} -> P a i -> ℕ
        init≡0 : (a : A) -> (c : C) -> potential (initial a c) ≡ 0

record Amortized2 {A : Set a} {B : Set b} {I : Set i} (P : A -> B -> I -> Set c) : Set (a l⊔ b l⊔ c l⊔ i) where
    field
        {i₀} : I
        initial : (a : A) -> (b : B) -> P a b i₀
        potential : {a : A} {b : B} {i : I} -> P a b i -> ℕ
        init≡0 : (a : A) -> (b : B) -> potential (initial a b) ≡ 0

{-}
record Amortized' {I : Set} {pars : ParList (lsuc a)} {init-extra-pars : ParList (lsuc a)} (A : IxType (I cons0 pars)) : Set (sel-level' pars (sel-level init-extra-pars)) where
    field
        {i₀} : I
        initial : FunSpace' Explicit pars Explicit init-extra-pars (A i₀)
        -- potential : FunSpace' Explicit (I cons0 pars) Explicit nil A ℕ
        init≡0 : ImplicitSelector+ParameterizedFun {p = pars} (A i₀) (ISelect-Concat potential (_≡ 0))
-}

data Am {I : Set i} {A : I -> Set a} (am : Amortized A) (C : Set b) : Set (lsuc (a l⊔ i l⊔ b)) where
    base : (x : A (Amortized.i₀ am)) -> {x ≡ Amortized.initial am} -> Am am C
    step :  {next : {i : I} -> A i -> I}
            {time : {i : I} -> A i -> ℕ}
         -> Am am C
         -> ({i : I} -> (x : A i) -> DecTree C (A $ next x) (time x))
         -> Am am C
    am-map :  {J : Set i}
              {B : J -> Set a}
              {am' : Amortized B}
              {imap : {j : J} -> B j -> I}
              (f : {j : J} -> (x : B j) -> A $ imap x)
              {map-is-pot-invariant : {j : J} -> (x : B j) -> Amortized.potential am' x ≡ Amortized.potential am (f x)}
           -> Am am' C
           -> Am am  C

data Am' {I : Set i} {A : I -> Set a} {X : Set x} (am : Amortized' A X) (C : Set b) : Set (lsuc (a l⊔ i l⊔ x l⊔ b)) where
    base :  (v : A (Amortized'.i₀ am))
         -> {x : X}
         -> {v ≡ Amortized'.initial am x}
         -> Am' am C
    step :  {next : {i : I} -> A i -> I}
            {time : {i : I} -> A i -> ℕ}
         -> Am' am C
         -> ({i : I} -> (x : A i) -> DecTree C (A $ next x) (time x))
         -> Am' am C

data Am1 {A : Set a} {I : Set i} {P : A -> I -> Set b} (am : Amortized1 P) (C : Set c) : A -> Set (lsuc (a l⊔ i l⊔ b l⊔ c)) where
    base :  {a : A}
         -> (v : P a (Amortized1.i₀ am))
         -> {v ≡ Amortized1.initial am a}
         -> Am1 am C a
    step :  {nextA : A -> A}
            {nextI : {a : A} {i : I} -> P a i -> I}
            {time  : {a : A} {i : I} -> P a i -> ℕ}
            {a : A}
         -> Am1 am C a
         -> ({i : I} -> (x : P a i) -> DecTree C (P (nextA a) (nextI x)) (time x))
         -> Am1 am C (nextA a)


data Am1' {ℓc : Level} {A : Set a} {C : Set c} {I : Set i} {P : A -> I -> Set b} (am : Amortized1' P C) (Comp : Set ℓc) : Set (lsuc (a l⊔ b l⊔ c l⊔ i l⊔ ℓc)) where
    base :  {a : A}
         -> (x : P a (Amortized1'.i₀ am))
         -> {c : C}
         -> {x ≡ Amortized1'.initial am a c}
         -> Am1' am Comp
    step :  {nextA : {a : A} {i : I} -> P a i -> A}
            {nextI : {a : A} {i : I} -> P a i -> I}
            {time  : {a : A} {i : I} -> P a i -> ℕ}
         -> Am1' am Comp
         -> ({a : A} {i : I} -> (x : P a i) -> DecTree Comp (P (nextA x) (nextI x)) (time x))
         -> Am1' am Comp

data Am2 {ℓc : Level} {A : Set a} {B : Set b} {I : Set i} {P : A -> B -> I -> Set c} (am : Amortized2 P) (C : Set ℓc) : Set (lsuc (a l⊔ b l⊔ c l⊔ i l⊔ ℓc)) where
    base :  {a : A}
            {b : B}
         -> (x : P a b (Amortized2.i₀ am))
         -> {x ≡ Amortized2.initial am a b}
         -> Am2 am C
    step :  {nextA : {a : A} {b : B} {i : I} -> P a b i -> A}
            {nextB : {a : A} {b : B} {i : I} -> P a b i -> B}
            {nextI : {a : A} {b : B} {i : I} -> P a b i -> I}
            {time  : {a : A} {b : B} {i : I} -> P a b i -> ℕ}
         -> Am2 am C
         -> ({a : A} {b : B} {i : I} -> (x : P a b i) -> DecTree C (P (nextA x) (nextB x) (nextI x)) (time x))
         -> Am2 am C


lift : {am : Amortized A} -> Am am Compare
lift {am = am} = base (Amortized.initial am) {refl}

lift' : {am : Amortized' A X} -> X -> Am' am Compare
lift' {am = am} x = base (Amortized'.initial am x) {x} {refl}

lift1 : {P : M -> I -> Set a} {am : Amortized1 P} -> (m : M) -> Am1 am Compare m
lift1 {am = am} m = base (Amortized1.initial am m) {refl}

lift1' : {P : M -> I -> Set a} {am : Amortized1' P X} -> M -> X -> Am1' am Compare
lift1' {am = am} m x = base (Amortized1'.initial am m x) {x} {refl}

lift2 : {P : M -> N -> I -> Set a} {am : Amortized2 P} -> M -> N -> Am2 am Compare
lift2 {am = am} m n = base (Amortized2.initial am m n) {refl}

am-index : {I : Set i} -> {A : I -> Set a} -> {am : Amortized A} -> {{_ : Leq Compare}} -> Am am Compare -> I
am-eval : {am : Amortized A} -> {{_ : Leq Compare}} -> (v : Am am Compare) -> A (am-index v)

am-index {am = am} (base _) = Amortized.i₀ am
am-index (step {next} val _) = next (am-eval val)
am-index (am-map {imap = imap} _ val) = imap (am-eval val)

am-eval (base v) = v
am-eval (step val trans) = reduce $ trans $ am-eval val
am-eval (am-map f val) = f (am-eval val)


am'-index : {I : Set i} {A : I -> Set a} {am : Amortized' A X} {{_ : Leq Compare}} -> Am' am Compare -> I
am'-eval : {am : Amortized' A X} -> {{_ : Leq Compare}} -> (v : Am' am Compare) -> A (am'-index v)

am'-index {am = am} (base _) = Amortized'.i₀ am
am'-index (step {next} val _) = next (am'-eval val)

am'-eval (base v) = v
am'-eval (step val trans) = reduce $ trans $ am'-eval val

am1-index : {P : M -> I -> Set a} {am : Amortized1 P} {{_ : Leq Compare}} {m : M} -> Am1 am Compare m -> I
am1-eval : {P : M -> I -> Set a} {am : Amortized1 P} {m : M} -> {{_ : Leq Compare}} -> (v : Am1 am Compare m) -> P m (am1-index v)

am1-index {am = am} (base _) = Amortized1.i₀ am
am1-index (step {nextI = nextI} val _) = nextI (am1-eval val)

am1-eval (base v) = v
am1-eval (step val trans) = reduce $ trans $ am1-eval val


am1'-index : {P : M -> I -> Set a} {am : Amortized1' P X} {{_ : Leq Compare}} -> Am1' am Compare -> I
am1'-m : {P : M -> I -> Set a} {am : Amortized1' P X} {{_ : Leq Compare}} -> Am1' am Compare -> M
am1'-eval : {am : Amortized1' P1 X} -> {{_ : Leq Compare}} -> (v : Am1' am Compare) -> P1 (am1'-m v) (am1'-index v)

am1'-index {am = am} (base _) = Amortized1'.i₀ am
am1'-index (step {nextI = next} val _) = next (am1'-eval val)

am1'-m (base {m} _) = m
am1'-m (step {nextA = next} val _) = next (am1'-eval val)

am1'-eval (base v) = v
am1'-eval (step val trans) = reduce $ trans $ am1'-eval val


am2-index : {P : M -> N -> I -> Set a} {am : Amortized2 P} {{_ : Leq Compare}} -> Am2 am Compare -> I
am2-m : {P : M -> N -> I -> Set a} {am : Amortized2 P} {{_ : Leq Compare}} -> Am2 am Compare -> M
am2-n : {P : M -> N -> I -> Set a} {am : Amortized2 P} {{_ : Leq Compare}} -> Am2 am Compare -> N
am2-eval : {am : Amortized2 P2} -> {{_ : Leq Compare}} -> (v : Am2 am Compare) -> P2 (am2-m v) (am2-n v) (am2-index v)

am2-index {am = am} (base _) = Amortized2.i₀ am
am2-index (step {nextI = next} val _) = next (am2-eval val)

am2-m (base {m} _) = m
am2-m (step {nextA = next} val _) = next (am2-eval val)

am2-n (base {_} {n} _) = n
am2-n (step {nextB = next} val _) = next (am2-eval val)

am2-eval (base v) = v
am2-eval (step val trans) = reduce $ trans $ am2-eval val



am-potential : {am : Amortized A} -> {{_ : Leq Compare}} -> Am am Compare -> ℕ
am-potential {am = am} v = Amortized.potential am $ am-eval v

am'-potential : {am : Amortized' A X} -> {{_ : Leq Compare}} -> Am' am Compare -> ℕ
am'-potential {am = am} v = Amortized'.potential am $ am'-eval v

am1-potential : {P : M -> I -> Set a} {am : Amortized1 P} {m : M} {{_ : Leq Compare}} -> Am1 am Compare m -> ℕ
am1-potential {am = am} v = Amortized1.potential am $ am1-eval v

am1'-potential : {am : Amortized1' P1 X} -> {{_ : Leq Compare}} -> Am1' am Compare -> ℕ
am1'-potential {am = am} v = Amortized1'.potential am $ am1'-eval v

am2-potential : {am : Amortized2 P2} -> {{_ : Leq Compare}} -> Am2 am Compare -> ℕ
am2-potential {am = am} v = Amortized2.potential am $ am2-eval v


dtime-step : {am : Amortized A} -> {{_ : Leq Compare}} -> Am am Compare -> ℕ
dtime-step (base val) = 0
dtime-step (step {next} {time} val trans) = time $ am-eval val
dtime-step (am-map _ _) = 0

dtime-full : {am : Amortized A} -> {{_ : Leq Compare}} -> Am am Compare -> ℕ
dtime-full (base val) = 0
dtime-full outer@(step inner _) = dtime-full inner + dtime-step outer
dtime-full (am-map _ val) = dtime-full val

dtime-step' : {am : Amortized' A X} -> {{_ : Leq Compare}} -> Am' am Compare -> ℕ
dtime-step' (base val) = 0
dtime-step' (step {next} {time} val trans) = time $ am'-eval val

dtime-full' : {am : Amortized' A X} -> {{_ : Leq Compare}} -> Am' am Compare -> ℕ
dtime-full' (base val) = 0
dtime-full' outer@(step inner _) = dtime-full' inner + dtime-step' outer

dtime-step1 : {P : M -> I -> Set a} {am : Amortized1 P} {m : M} {{_ : Leq Compare}} -> Am1 am Compare m -> ℕ
dtime-step1 (base val) = 0
dtime-step1 (step {time = time} val trans) = time $ am1-eval val

dtime-full1 : {P : M -> I -> Set a} {am : Amortized1 P} {m : M} {{_ : Leq Compare}} -> Am1 am Compare m -> ℕ
dtime-full1 (base val) = 0
dtime-full1 outer@(step inner _) = dtime-full1 inner + dtime-step1 outer

dtime-step1' : {am : Amortized1' P1 X} -> {{_ : Leq Compare}} -> Am1' am Compare -> ℕ
dtime-step1' (base val) = 0
dtime-step1' (step {time = time} val trans) = time $ am1'-eval val

dtime-full1' : {am : Amortized1' P1 X} -> {{_ : Leq Compare}} -> Am1' am Compare -> ℕ
dtime-full1' (base val) = 0
dtime-full1' outer@(step inner _) = dtime-full1' inner + dtime-step1' outer

dtime-step2 : {am : Amortized2 P2} -> {{_ : Leq Compare}} -> Am2 am Compare -> ℕ
dtime-step2 (base val) = 0
dtime-step2 (step {time = time} val trans) = time $ am2-eval val

dtime-full2 : {am : Amortized2 P2} -> {{_ : Leq Compare}} -> Am2 am Compare -> ℕ
dtime-full2 (base val) = 0
dtime-full2 outer@(step inner _) = dtime-full2 inner + dtime-step2 outer



atime-step : {am : Amortized A} -> {{_ : Leq Compare}} -> Am am Compare -> ℤ
atime-step (base val) = ℤ.0ℤ
atime-step (am-map _ _) = ℤ.0ℤ
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

atime-step' : {am : Amortized' A X} -> {{_ : Leq Compare}} -> Am' am Compare -> ℤ
atime-step' (base val) = ℤ.0ℤ
atime-step' {am = am} v@(step val transform) = dtime-step' v ⊖ pot-before ℤ.+ (+ pot-after)
    where
        val-before = am'-eval val
        val-after = reduce $ transform $ val-before
        pot-before = Amortized'.potential am val-before
        pot-after = Amortized'.potential am val-after

atime-full' : {am : Amortized' A X} -> {{_ : Leq Compare}} -> Am' am Compare -> ℤ
atime-full' (base val) = ℤ.0ℤ
atime-full' v@(step val _) = atime-full' val ℤ.+ atime-step' v

atime-step1 : {P : M -> I -> Set a} {am : Amortized1 P} {m : M} {{_ : Leq Compare}} -> Am1 am Compare m -> ℤ
atime-step1 (base val) = ℤ.0ℤ
atime-step1 {am = am} v@(step val transform) = dtime-step1 v ⊖ pot-before ℤ.+ (+ pot-after)
    where
        val-before = am1-eval val
        val-after = reduce $ transform $ val-before
        pot-before = Amortized1.potential am val-before
        pot-after = Amortized1.potential am val-after

atime-full1 : {P : M -> I -> Set a} {am : Amortized1 P} {m : M} {{_ : Leq Compare}} -> Am1 am Compare m -> ℤ
atime-full1 (base val) = ℤ.0ℤ
atime-full1 v@(step val _) = atime-full1 val ℤ.+ atime-step1 v

atime-step1' : {am : Amortized1' P1 X} -> {{_ : Leq Compare}} -> Am1' am Compare -> ℤ
atime-step1' (base val) = ℤ.0ℤ
atime-step1' {am = am} v@(step val transform) = dtime-step1' v ⊖ pot-before ℤ.+ (+ pot-after)
    where
        val-before = am1'-eval val
        val-after = reduce $ transform $ val-before
        pot-before = Amortized1'.potential am val-before
        pot-after = Amortized1'.potential am val-after

atime-full1' : {am : Amortized1' P1 X} -> {{_ : Leq Compare}} -> Am1' am Compare -> ℤ
atime-full1' (base val) = ℤ.0ℤ
atime-full1' v@(step val _) = atime-full1' val ℤ.+ atime-step1' v

atime-step2 : {am : Amortized2 P2} -> {{_ : Leq Compare}} -> Am2 am Compare -> ℤ
atime-step2 (base val) = ℤ.0ℤ
atime-step2 {am = am} v@(step val transform) = dtime-step2 v ⊖ pot-before ℤ.+ (+ pot-after)
    where
        val-before = am2-eval val
        val-after = reduce $ transform $ val-before
        pot-before = Amortized2.potential am val-before
        pot-after = Amortized2.potential am val-after

atime-full2 : {am : Amortized2 P2} -> {{_ : Leq Compare}} -> Am2 am Compare -> ℤ
atime-full2 (base val) = ℤ.0ℤ
atime-full2 v@(step val _) = atime-full2 val ℤ.+ atime-step2 v


-- atime is an upper bound on dtime
atime≡dtime+pot : {am : Amortized A} -> {{_ : Leq Compare}} -> (v : Am am Compare) -> atime-full v ≡ + (dtime-full v + am-potential v)
atime≡dtime+pot {am = am} (base v {v≡init}) = sym $ begin
        + Amortized.potential am v                        ≡⟨ cong (+_) $ cong (Amortized.potential am) v≡init ⟩
        + Amortized.potential am (Amortized.initial am)   ≡⟨ cong (+_) $ Amortized.init≡0 am ⟩
        ℤ.0ℤ                                              ∎
    where
        open ≡-Reasoning
atime≡dtime+pot {am = am} v@(am-map {am' = am'} f {map-is-pot-invariant} val) = begin
        atime-full v                                                   ≡⟨⟩
        atime-full val                                                 ≡⟨ atime≡dtime+pot val ⟩
        + (dtime-full val + Amortized.potential am' (am-eval val))     ≡⟨ cong (λ x → + (dtime-full val + x)) $ map-is-pot-invariant (am-eval val) ⟩
        + (dtime-full val + Amortized.potential am (f $ am-eval val))  ≡⟨⟩
        + (dtime-full val + Amortized.potential am (am-eval v))        ≡⟨⟩
        + (dtime-full v + am-potential v)                              ∎
    where
        open ≡-Reasoning
atime≡dtime+pot v@(step val trans) = begin
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

atime'≡dtime'+pot : {am : Amortized' A X} -> {{_ : Leq Compare}} -> (v : Am' am Compare) -> atime-full' v ≡ + (dtime-full' v + am'-potential v)
atime'≡dtime'+pot {am = am} (base v {x} {v≡init}) = sym $ begin
        + Amortized'.potential am v                           ≡⟨ cong (+_) $ cong (Amortized'.potential am) v≡init ⟩
        + Amortized'.potential am (Amortized'.initial am x)   ≡⟨ cong (+_) $ Amortized'.init≡0 am x ⟩
        ℤ.0ℤ                                                  ∎
    where
        open ≡-Reasoning
atime'≡dtime'+pot v@(step val trans) = begin
        atime-full' v
                                                        ≡⟨⟩
        atime-full' val ℤ.+ atime-step' v
                                                        ≡⟨ cong (ℤ._+ atime-step' v) $ atime'≡dtime'+pot val ⟩
            + (dtime-full' val + am'-potential val)
        ℤ.+ atime-step' v
                                                       ≡⟨ cong (ℤ._+ atime-step' v) $
                                                          ℤ-Props.pos-+-commute (dtime-full' val) (am'-potential val) ⟩
            + dtime-full' val
        ℤ.+ + am'-potential val
        ℤ.+ atime-step' v
                                                       ≡⟨⟩
            + dtime-full' val
        ℤ.+ + am'-potential val
        ℤ.+ (dtime-step' v ⊖ am'-potential val
             ℤ.+ + am'-potential v)
                                                       ≡⟨ sym $ ℤ-Props.+-assoc
                                                                  (+ dtime-full' val ℤ.+ + am'-potential val)
                                                                  (dtime-step' v ⊖ am'-potential val)
                                                                  (+ am'-potential v) ⟩
            + dtime-full' val
        ℤ.+ + am'-potential val
        ℤ.+ (dtime-step' v ⊖ am'-potential val)
        ℤ.+ + am'-potential v
                                                       ≡⟨ cong (λ x →     + dtime-full' val
                                                                      ℤ.+ + am'-potential val
                                                                      ℤ.+ x
                                                                      ℤ.+ + am'-potential v) $
                                                          sym $ ℤ-Props.[+m]-[+n]≡m⊖n (dtime-step' v) (am'-potential val) ⟩
            + dtime-full' val
        ℤ.+ + am'-potential val
        ℤ.+ (+ dtime-step' v ℤ.- + am'-potential val)
        ℤ.+ + am'-potential v
                                                       ≡⟨ cong (ℤ._+ (+ am'-potential v)) $
                                                          +-telescope (+ dtime-full' val) (+ dtime-step' v) (+ am'-potential val) ⟩
            + dtime-full' val
        ℤ.+ (+ dtime-step' v)
        ℤ.+ (+ am'-potential v)
                                                       ≡⟨ cong (ℤ._+ (+ am'-potential v)) $
                                                          sym $ ℤ-Props.pos-+-commute (dtime-full' val) (dtime-step' v) ⟩
            + dtime-full' v
        ℤ.+ + am'-potential v
                                                       ≡⟨ sym $ ℤ-Props.pos-+-commute (dtime-full' v) (am'-potential v) ⟩
            + (dtime-full' v + am'-potential v)          ∎
    where
        open ≡-Reasoning






atime1≡dtime1+pot : {P : M -> I -> Set a} {am : Amortized1 P} {m : M} {{_ : Leq Compare}} -> (v : Am1 am Compare m) -> atime-full1 v ≡ + (dtime-full1 v + am1-potential v)
atime1≡dtime1+pot {am = am} (base {a} v {v≡init}) = sym $ begin
        + Amortized1.potential am v                           ≡⟨ cong (+_) $ cong (Amortized1.potential am) v≡init ⟩
        + Amortized1.potential am (Amortized1.initial am a)   ≡⟨ cong (+_) $ Amortized1.init≡0 am a ⟩
        ℤ.0ℤ                                                  ∎
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


atime1'≡dtime1'+pot : {am : Amortized1' P1 X} -> {{_ : Leq Compare}} -> (v : Am1' am Compare) -> atime-full1' v ≡ + (dtime-full1' v + am1'-potential v)
atime1'≡dtime1'+pot {am = am} (base {a} v {x} {v≡init}) = sym $ begin
        + Amortized1'.potential am v                              ≡⟨ cong (+_) $ cong (Amortized1'.potential am) v≡init ⟩
        + Amortized1'.potential am (Amortized1'.initial am a x)   ≡⟨ cong (+_) $ Amortized1'.init≡0 am a x ⟩
        ℤ.0ℤ                                                      ∎
    where
        open ≡-Reasoning
atime1'≡dtime1'+pot v@(step val trans) = begin
        atime-full1' v
                                                        ≡⟨⟩
        atime-full1' val ℤ.+ atime-step1' v
                                                        ≡⟨ cong (ℤ._+ atime-step1' v) $ atime1'≡dtime1'+pot val ⟩
            + (dtime-full1' val + am1'-potential val)
        ℤ.+ atime-step1' v
                                                        ≡⟨ cong (ℤ._+ atime-step1' v) $
                                                          ℤ-Props.pos-+-commute (dtime-full1' val) (am1'-potential val) ⟩
            + dtime-full1' val
        ℤ.+ + am1'-potential val
        ℤ.+ atime-step1' v
                                                        ≡⟨⟩
            + dtime-full1' val
        ℤ.+ + am1'-potential val
        ℤ.+ (dtime-step1' v ⊖ am1'-potential val
             ℤ.+ + am1'-potential v)
                                                        ≡⟨ sym $ ℤ-Props.+-assoc
                                                                  (+ dtime-full1' val ℤ.+ + am1'-potential val)
                                                                  (dtime-step1' v ⊖ am1'-potential val)
                                                                  (+ am1'-potential v) ⟩
            + dtime-full1' val
        ℤ.+ + am1'-potential val
        ℤ.+ (dtime-step1' v ⊖ am1'-potential val)
        ℤ.+ + am1'-potential v
                                                        ≡⟨ cong (λ x →    + dtime-full1' val
                                                                      ℤ.+ + am1'-potential val
                                                                      ℤ.+ x
                                                                      ℤ.+ + am1'-potential v) $
                                                          sym $ ℤ-Props.[+m]-[+n]≡m⊖n (dtime-step1' v) (am1'-potential val) ⟩
            + dtime-full1' val
        ℤ.+ + am1'-potential val
        ℤ.+ (+ dtime-step1' v ℤ.- + am1'-potential val)
        ℤ.+ + am1'-potential v
                                                        ≡⟨ cong (ℤ._+ (+ am1'-potential v)) $
                                                           +-telescope (+ dtime-full1' val) (+ dtime-step1' v) (+ am1'-potential val) ⟩
            + dtime-full1' val
        ℤ.+ (+ dtime-step1' v)
        ℤ.+ (+ am1'-potential v)
                                                        ≡⟨ cong (ℤ._+ (+ am1'-potential v)) $
                                                           sym $ ℤ-Props.pos-+-commute (dtime-full1' val) (dtime-step1' v) ⟩
            + dtime-full1' v
        ℤ.+ + am1'-potential v
                                                        ≡⟨ sym $ ℤ-Props.pos-+-commute (dtime-full1' v) (am1'-potential v) ⟩
            + (dtime-full1' v + am1'-potential v)       ∎
    where
        open ≡-Reasoning






atime2≡dtime2+pot : {am : Amortized2 P2} -> {{_ : Leq Compare}} -> (v : Am2 am Compare) -> atime-full2 v ≡ + (dtime-full2 v + am2-potential v)
atime2≡dtime2+pot {am = am} (base {a} {b} v {v≡init}) = sym $ begin
        + Amortized2.potential am v                             ≡⟨ cong (+_) $ cong (Amortized2.potential am) v≡init ⟩
        + Amortized2.potential am (Amortized2.initial am a b)   ≡⟨ cong (+_) $ Amortized2.init≡0 am a b ⟩
        ℤ.0ℤ                                                    ∎
    where
        open ≡-Reasoning
atime2≡dtime2+pot v@(step val trans) = begin
        atime-full2 v
                                                        ≡⟨⟩
        atime-full2 val ℤ.+ atime-step2 v
                                                        ≡⟨ cong (ℤ._+ atime-step2 v) $ atime2≡dtime2+pot val ⟩
            + (dtime-full2 val + am2-potential val)
        ℤ.+ atime-step2 v
                                                       ≡⟨ cong (ℤ._+ atime-step2 v) $
                                                          ℤ-Props.pos-+-commute (dtime-full2 val) (am2-potential val) ⟩
            + dtime-full2 val
        ℤ.+ + am2-potential val
        ℤ.+ atime-step2 v
                                                       ≡⟨⟩
            + dtime-full2 val
        ℤ.+ + am2-potential val
        ℤ.+ (dtime-step2 v ⊖ am2-potential val
             ℤ.+ + am2-potential v)
                                                       ≡⟨ sym $ ℤ-Props.+-assoc
                                                                  (+ dtime-full2 val ℤ.+ + am2-potential val)
                                                                  (dtime-step2 v ⊖ am2-potential val)
                                                                  (+ am2-potential v) ⟩
            + dtime-full2 val
        ℤ.+ + am2-potential val
        ℤ.+ (dtime-step2 v ⊖ am2-potential val)
        ℤ.+ + am2-potential v
                                                       ≡⟨ cong (λ x →     + dtime-full2 val
                                                                      ℤ.+ + am2-potential val
                                                                      ℤ.+ x
                                                                      ℤ.+ + am2-potential v) $
                                                          sym $ ℤ-Props.[+m]-[+n]≡m⊖n (dtime-step2 v) (am2-potential val) ⟩
            + dtime-full2 val
        ℤ.+ + am2-potential val
        ℤ.+ (+ dtime-step2 v ℤ.- + am2-potential val)
        ℤ.+ + am2-potential v
                                                       ≡⟨ cong (ℤ._+ (+ am2-potential v)) $
                                                          +-telescope (+ dtime-full2 val) (+ dtime-step2 v) (+ am2-potential val) ⟩
            + dtime-full2 val
        ℤ.+ (+ dtime-step2 v)
        ℤ.+ (+ am2-potential v)
                                                       ≡⟨ cong (ℤ._+ (+ am2-potential v)) $
                                                          sym $ ℤ-Props.pos-+-commute (dtime-full2 val) (dtime-step2 v) ⟩
            + dtime-full2 v
        ℤ.+ + am2-potential v
                                                       ≡⟨ sym $ ℤ-Props.pos-+-commute (dtime-full2 v) (am2-potential v) ⟩
            + (dtime-full2 v + am2-potential v)          ∎
    where
        open ≡-Reasoning






