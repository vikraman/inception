module Inception.Ctx.Base (Ty : Set) where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

infixl 15 _∙_
infix  10 _∋_

--------------------------------------------------------------------------
-- contexts

data Ctx : Set where
  ε   : Ctx
  _∙_ : Ctx → Ty → Ctx

variable
  X X₀ X₁ X₂ X₃ Y Y₀ Y₁ Y₂ Y₃ Z Z₀ Z₁ Z₂ Z₃ U U₀ U₁ U₂ U₃ S S₀ S₁ S₂ S₃ T T₀ T₁ T₂ T₃ : Ty
  Γ Δ Ψ Ξ Γ₁ Δ₁ Ψ₁ : Ctx

data _∋_ : Ctx → Ty → Set where
  here  : Γ ∙ X ∋ X
  there : Γ ∋ X → Γ ∙ Y ∋ X

there-injective : {i j : Γ ∋ X} → there {Y = Y} i ≡ there j → i ≡ j
there-injective refl = refl
