module Inception.Rewriting.Acc where

open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Function using (flip)

open import Induction.WellFounded using (Acc; acc)

--------------------------------------------------------------------------
-- transport along a simulation

module _ {A B : Set} {_~>_ : A → A → Set} {_⇝_ : B → B → Set} (R : A → B → Set)
         (h : ∀ {a a₁ b} → R a b → a ~> a₁ → Σ[ b₁ ∈ B ] (b ⇝ b₁) × R a₁ b₁) where

  Acc-sim : ∀ {a b} → R a b → Acc (flip _⇝_) b → Acc (flip _~>_) a
  Acc-sim {a} r (acc f) = acc step
    where
    step : ∀ {a₁} → a ~> a₁ → Acc (flip _~>_) a₁
    step s with h r s
    ... | (b₁ , t , r₁) = Acc-sim r₁ (f t)
