module Counter where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Integer as ℤ using (ℤ ; _⊖_ ; +_ ; -_)
import Data.Integer.Properties as ℤ-Props
open import Data.Bool
open import Data.Unit using (⊤ ; tt)
open import Relation.Binary.PropositionalEquality
open import Function

open import AmortizedTime
open import DecTree
open import Leq

-- counter in little endian binary representation
-- \top indexing is just for convenience for plugging stuff into Am for now
data Counter : ⊤ → Set where
    zero : Counter tt
    _#_ : ∀ {i} -> Bool -> Counter i -> Counter tt

infixr 20 _#_


toℕ : ∀ {i} -> Counter i -> ℕ
toℕ zero = 0
toℕ (false # xs) = 2 * toℕ xs
toℕ (true # xs) = 1 + 2 * toℕ xs


counterPotential : ∀ {i} -> Counter i -> ℕ
counterPotential zero = 0
counterPotential (true # xs) = 1 + counterPotential xs
counterPotential (false # xs) = counterPotential xs

leadingOnes : ∀ {i} -> Counter i -> ℕ
leadingOnes zero = 0
leadingOnes (false # _) = 0
leadingOnes (true # xs) = 1 + leadingOnes xs

increment : {i : ⊤} -> (c : Counter i) -> DecTree Bool (Counter tt) (leadingOnes c)
increment zero = return (true # zero)
increment (false # c) = return (true # c)
increment (true # c) = if' true ≤? true then false #_ <$> increment c else (false #_ <$> increment c)




counter-amortized : Amortized Counter
counter-amortized = record
                    { initial = Counter.zero
                    ; potential = counterPotential
                    ; init≡0 = refl
                    }

inc-n : ℕ -> Am (counter-amortized) Bool
inc-n zero = lift
inc-n (suc n) = step (inc-n n ) increment


counter-pot-invariant : {{_ : Leq Bool}} -> ∀ {i} -> (c : Counter i) -> leadingOnes c ⊖ counterPotential c ℤ.+ + counterPotential (reduce $ increment c) ≡ + 1
counter-pot-invariant zero = refl
counter-pot-invariant (false # c) = begin
        0 ⊖ pot ℤ.+ + suc pot         ≡⟨ cong (ℤ._+ (+ suc pot)) $ sym $ ℤ-Props.[+m]-[+n]≡m⊖n 0 pot  ⟩
        + 0 ℤ.- potℤ ℤ.+ + suc pot    ≡⟨ cong (ℤ._+ (+ suc pot)) $ ℤ-Props.+-identityˡ (- potℤ) ⟩
        - potℤ ℤ.+ + suc pot          ≡⟨ ℤ-Props.+-comm (- potℤ) (+ suc pot) ⟩
        + suc pot ℤ.- potℤ            ≡⟨ cong (ℤ._- potℤ) $ ℤ-Props.pos-+-commute 1 pot ⟩
        + 1 ℤ.+ potℤ ℤ.- potℤ         ≡⟨ ℤ-Props.+-assoc (+ 1) potℤ (- potℤ) ⟩
        + 1 ℤ.+ (potℤ ℤ.- potℤ)       ≡⟨ cong (λ x → + 1 ℤ.+ x) $ ℤ-Props.m≡n⇒m-n≡0 potℤ potℤ refl ⟩
        + 1 ℤ.+ + 0                   ≡⟨ ℤ-Props.+-identityʳ (+ 1) ⟩
        + 1                           ∎
    where
        open ≡-Reasoning
        pot = counterPotential c
        potℤ = + pot
counter-pot-invariant (true # c) = begin
        ones ⊖ pot ℤ.+ + counterPotential (reduce branch) ≡⟨ cong (λ x → ones ⊖ pot ℤ.+ + counterPotential x) $ branch'-elim t ⟩
        ones ⊖ pot ℤ.+ + counterPotential (reduce t)      ≡⟨ cong (λ x → ones ⊖ pot ℤ.+ + counterPotential x) $ apply-elim (false #_) (increment c) ⟩
        ones ⊖ pot ℤ.+ + counterPotential (reduce (increment c)) ≡⟨ counter-pot-invariant c ⟩
        + 1    ∎
    where
        open ≡-Reasoning
        ones = leadingOnes c
        pot = counterPotential c
        t = false #_ <$> increment c
        branch = if' true ≤? true then t else t

inc-in-linear-time : {{_ : Leq Bool}} -> ∀ n -> atime-full (inc-n n) ℤ.≤ + n
inc-in-linear-time zero = ℤ.+≤+ z≤n
inc-in-linear-time (suc n) = begin
        atime-full (inc-n n) ℤ.+ (leadingOnes (am-eval $ inc-n n) ⊖ am-potential (inc-n n) ℤ.+ + am-potential (inc-n $ suc n))
            ≤⟨ ℤ-Props.+-monoˡ-≤ _ $ inc-in-linear-time n ⟩
        + n ℤ.+ ((leadingOnes $ am-eval $ inc-n n) ⊖ (am-potential $ inc-n n) ℤ.+ (+ am-potential (inc-n $ suc n)))
            ≡⟨ cong (λ x → + n ℤ.+ x) $ counter-pot-invariant (am-eval $ inc-n n) ⟩
        + n ℤ.+ + 1
            ≡⟨⟩
        + (n + 1)
            ≡⟨ cong (+_) $ +-comm n 1  ⟩
        + suc n   ∎
    where
        open ℤ-Props.≤-Reasoning
