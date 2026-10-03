module Inception.Rewriting.Relation where

open import Data.Product using (Σ; Σ-syntax; _×_; _,_)

open import Induction.WellFounded using (Acc; acc)

--------------------------------------------------------------------------
-- converse

infix 30 _†

_† : {A B : Set} → (A → B → Set) → B → A → Set
(R †) b a = R a b

--------------------------------------------------------------------------
-- accessibility along a simulation

module _ {A B : Set} {_~>_ : A → A → Set} {_⇝_ : B → B → Set} (R : A → B → Set)
         (h : ∀ {a a₁ b} → R a b → a ~> a₁ → Σ[ b₁ ∈ B ] (b ⇝ b₁) × R a₁ b₁) where

  Acc-sim : ∀ {a b} → R a b → Acc (_⇝_ †) b → Acc (_~>_ †) a
  Acc-sim {a} r (acc f) = acc step
    where
    step : ∀ {a₁} → a ~> a₁ → Acc (_~>_ †) a₁
    step s with h r s
    ... | (b₁ , t , r₁) = Acc-sim r₁ (f t)
