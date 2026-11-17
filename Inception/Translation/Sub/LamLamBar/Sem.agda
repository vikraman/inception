open import Inception.LamLamBar.Syntax

module Inception.Translation.Sub.LamLamBar.Sem (R : Set) where

open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality

import Inception.LamLamBar.CPS
open import Inception.Prelude
import Inception.Sub.Semantics
import Inception.Sub.Syntax as I
open import Inception.Translation.Sub.LamLamBar

private
  module LC = Inception.LamLamBar.CPS R
  module IC = Inception.Sub.Semantics R
  module LS = Sem LC.⟦_⟧
  module IS = I.Sem IC.⟦_⟧

--------------------------------------------------------------------------
-- types and contexts

⟦-⟧-coh : LC.⟦ ⟦ I.X ⟧ ⟧ ≡ IC.⟦ I.X ⟧
⟦-⟧-coh {I.`𝟙}     = refl
⟦-⟧-coh {X I.`× Y} = cong₂ _×_ (⟦-⟧-coh {X}) (⟦-⟧-coh {Y})
⟦-⟧-coh {X I.`⇒ Y} = cong₂ (λ A B → A → IC.K B) (⟦-⟧-coh {X}) (⟦-⟧-coh {Y})
⟦-⟧-coh {I.`ℓ}     = refl
{-# REWRITE ⟦-⟧-coh #-}

⟦-⟧ˣ-coh : LS.⟦ ⟦ I.Γ ⟧ˣ ⟧ˣ ≡ IS.⟦ I.Γ ⟧ˣ
⟦-⟧ˣ-coh {I.ε}     = refl
⟦-⟧ˣ-coh {Γ I.∙ X} = cong (_× IC.⟦ X ⟧) (⟦-⟧ˣ-coh {Γ})
{-# REWRITE ⟦-⟧ˣ-coh #-}

⟦-⟧ⁱ-coh : (i : I.Γ I.∋ I.X) → LS.⟦ ⟦ i ⟧ⁱ ⟧ᵐ ≡ IS.⟦ i ⟧ᵐ
⟦-⟧ⁱ-coh I.here = refl
⟦-⟧ⁱ-coh (I.there i) = cong (proj₁ ；_) (⟦-⟧ⁱ-coh i)
{-# REWRITE ⟦-⟧ⁱ-coh #-}

--------------------------------------------------------------------------
-- values and computations

mutual
  ⟦-⟧ᵛ-coh : (V : I.Γ I.⊢ᵛ I.X) → LC.⟦ ⟦ V ⟧ᵛ ⟧ᵛ ≡ IC.⟦ V ⟧ᵛ
  ⟦-⟧ᵛ-coh (I.var i)    = refl
  ⟦-⟧ᵛ-coh (I.lam M)    = cong curry (⟦-⟧ᶜ-coh M)
  ⟦-⟧ᵛ-coh (I.pair V W) = cong₂ <_,_> (⟦-⟧ᵛ-coh V) (⟦-⟧ᵛ-coh W)
  ⟦-⟧ᵛ-coh I.unit       = refl

  ⟦-⟧ᶜ-coh : (M : I.Γ I.⊢ᶜ I.X) → LC.⟦ ⟦ M ⟧ᶜ ⟧ᶜ ≡ IC.⟦ M ⟧ᶜ
  ⟦-⟧ᶜ-coh (I.return V) = cong (λ f γ k → k (f γ)) (⟦-⟧ᵛ-coh V)
  ⟦-⟧ᶜ-coh (I.pm V M)   = cong₂ (λ f g → < idf , f > ； assocl ； g) (⟦-⟧ᵛ-coh V) (⟦-⟧ᶜ-coh M)
  ⟦-⟧ᶜ-coh (I.push M N) = cong₂ (λ f g γ k → f γ (λ a → g (γ , a) k)) (⟦-⟧ᶜ-coh M) (⟦-⟧ᶜ-coh N)
  ⟦-⟧ᶜ-coh (I.app V W)  = cong₂ (λ f g γ → f γ (g γ)) (⟦-⟧ᵛ-coh V) (⟦-⟧ᵛ-coh W)
  ⟦-⟧ᶜ-coh (I.var V)    = cong (λ f γ k → f γ tt) (⟦-⟧ᵛ-coh V)
  ⟦-⟧ᶜ-coh (I.sub M N)  = cong₂ (λ f g γ k → f (γ , λ _ → g γ k) k) (⟦-⟧ᶜ-coh M) (⟦-⟧ᶜ-coh N)

{-# REWRITE ⟦-⟧ᵛ-coh ⟦-⟧ᶜ-coh #-}

--------------------------------------------------------------------------
-- soundness

sound : I.Γ I.⊢ᶜ I.M₁ ≈ I.M₂ ∶ I.X → LC.⟦ ⟦ I.M₁ ⟧ᶜ ⟧ᶜ ≡ LC.⟦ ⟦ I.M₂ ⟧ᶜ ⟧ᶜ
sound = IC.eqComp
