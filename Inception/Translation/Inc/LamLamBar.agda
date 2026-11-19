open import Inception.LamLamBar.Syntax

module Inception.Translation.Inc.LamLamBar (𝒫 : Ty) where

import Inception.Inc.CPS
import Inception.Inc.Syntax as I
import Inception.LamLamBar.CPS
open import Inception.Prelude

--------------------------------------------------------------------------
-- types and contexts

⟦_⟧ : I.Ty → Ty
⟦ I.`𝟙 ⟧     = `𝟙
⟦ X I.`× Y ⟧ = ⟦ X ⟧ `× ⟦ Y ⟧
⟦ X I.`⇒ Y ⟧ = ⟦ X ⟧ `⇒ ⟦ Y ⟧
⟦ I.`ℓ ⟧     = 𝒫 ̃
⟦ I.`𝓅 ⟧     = 𝒫

open import Inception.Ctx.Map ⟦_⟧ public

--------------------------------------------------------------------------
-- values and computations

mutual
  ⟦_⟧ᵛ : I.Γ I.⊢ᵛ I.X → ⟦ I.Γ ⟧ˣ ⊢ᵛ ⟦ I.X ⟧
  ⟦ I.var i ⟧ᵛ    = var ⟦ i ⟧ⁱ
  ⟦ I.lam M ⟧ᵛ    = lam ⟦ M ⟧ᶜ
  ⟦ I.pair V W ⟧ᵛ = pair ⟦ V ⟧ᵛ ⟦ W ⟧ᵛ
  ⟦ I.unit ⟧ᵛ     = unit

  ⟦_⟧ᶜ : I.Γ I.⊢ᶜ I.X → ⟦ I.Γ ⟧ˣ ⊢ᶜ ⟦ I.X ⟧
  ⟦ I.return V ⟧ᶜ = return ⟦ V ⟧ᵛ
  ⟦ I.pm V M ⟧ᶜ   = pm ⟦ V ⟧ᵛ ⟦ M ⟧ᶜ
  ⟦ I.push M N ⟧ᶜ = push ⟦ M ⟧ᶜ ⟦ N ⟧ᶜ
  ⟦ I.app V W ⟧ᶜ  = app ⟦ V ⟧ᵛ ⟦ W ⟧ᵛ
  ⟦ I.rec V W ⟧ᶜ  = throw ⟦ V ⟧ᵛ ⟦ W ⟧ᵛ
  ⟦ I.inc M N ⟧ᶜ  = catch ⟦ M ⟧ᶜ ⟦ N ⟧ᶜ

⟦_⟧ˢ : I.Γ I.⊢ I.Δ → ⟦ I.Γ ⟧ˣ ⊢ ⟦ I.Δ ⟧ˣ
⟦ I.sub-ε ⟧ˢ      = sub-ε
⟦ I.sub-ex θ V ⟧ˢ = sub-ex ⟦ θ ⟧ˢ ⟦ V ⟧ᵛ

--------------------------------------------------------------------------
-- semantics

module _ (R : Set) where

  private
    module LC = Inception.LamLamBar.CPS R
    module IC = Inception.Inc.CPS LC.⟦ 𝒫 ⟧ R
    module LS = Sem LC.⟦_⟧
    module IS = I.Sem IC.⟦_⟧

  ------------------------------------------------------------------------
  -- types and contexts

  ⟦-⟧-coh : LC.⟦ ⟦ I.X ⟧ ⟧ ≡ IC.⟦ I.X ⟧
  ⟦-⟧-coh {I.`𝟙}     = refl
  ⟦-⟧-coh {X I.`× Y} = cong₂ _×_ (⟦-⟧-coh {X}) (⟦-⟧-coh {Y})
  ⟦-⟧-coh {X I.`⇒ Y} = cong₂ (λ A B → A → IC.K B) (⟦-⟧-coh {X}) (⟦-⟧-coh {Y})
  ⟦-⟧-coh {I.`ℓ}     = refl
  ⟦-⟧-coh {I.`𝓅}     = refl
  {-# REWRITE ⟦-⟧-coh #-}

  ⟦-⟧ˣ-coh : LS.⟦ ⟦ I.Γ ⟧ˣ ⟧ˣ ≡ IS.⟦ I.Γ ⟧ˣ
  ⟦-⟧ˣ-coh {I.ε}     = refl
  ⟦-⟧ˣ-coh {Γ I.∙ X} = cong (_× IC.⟦ X ⟧) (⟦-⟧ˣ-coh {Γ})
  {-# REWRITE ⟦-⟧ˣ-coh #-}

  ⟦_⟧ⁱ-coh : (i : I.Γ I.∋ I.X) → LS.⟦ ⟦ i ⟧ⁱ ⟧ᵐ ≡ IS.⟦ i ⟧ᵐ
  ⟦ I.here ⟧ⁱ-coh = refl
  ⟦ I.there i ⟧ⁱ-coh = cong (proj₁ ；_) ⟦ i ⟧ⁱ-coh
  {-# REWRITE ⟦_⟧ⁱ-coh #-}

  ------------------------------------------------------------------------
  -- values and computations

  mutual
    ⟦_⟧ᵛ-coh : (V : I.Γ I.⊢ᵛ I.X) → LC.⟦ ⟦ V ⟧ᵛ ⟧ᵛ ≡ IC.⟦ V ⟧ᵛ
    ⟦ I.var i ⟧ᵛ-coh    = refl
    ⟦ I.lam M ⟧ᵛ-coh    = cong curry ⟦ M ⟧ᶜ-coh
    ⟦ I.pair V W ⟧ᵛ-coh = cong₂ <_,_> ⟦ V ⟧ᵛ-coh ⟦ W ⟧ᵛ-coh
    ⟦ I.unit ⟧ᵛ-coh     = refl

    ⟦_⟧ᶜ-coh : (M : I.Γ I.⊢ᶜ I.X) → LC.⟦ ⟦ M ⟧ᶜ ⟧ᶜ ≡ IC.⟦ M ⟧ᶜ
    ⟦ I.return V ⟧ᶜ-coh = cong (λ f γ k → k (f γ)) ⟦ V ⟧ᵛ-coh
    ⟦ I.pm V M ⟧ᶜ-coh   = cong₂ (λ f g → < idf , f > ； assocl ； g) ⟦ V ⟧ᵛ-coh ⟦ M ⟧ᶜ-coh
    ⟦ I.push M N ⟧ᶜ-coh = cong₂ (λ f g γ k → f γ (λ a → g (γ , a) k)) ⟦ M ⟧ᶜ-coh ⟦ N ⟧ᶜ-coh
    ⟦ I.app V W ⟧ᶜ-coh  = cong₂ (λ f g γ → f γ (g γ)) ⟦ V ⟧ᵛ-coh ⟦ W ⟧ᵛ-coh
    ⟦ I.rec V W ⟧ᶜ-coh  = cong₂ (λ f g γ _ → f γ (g γ)) ⟦ V ⟧ᵛ-coh ⟦ W ⟧ᵛ-coh
    ⟦ I.inc M N ⟧ᶜ-coh  = cong₂ (λ f g γ k → f (γ , λ p → g (γ , p) k) k) ⟦ M ⟧ᶜ-coh ⟦ N ⟧ᶜ-coh

  {-# REWRITE ⟦_⟧ᵛ-coh ⟦_⟧ᶜ-coh #-}

  ------------------------------------------------------------------------
  -- soundness

  sound : I.Γ I.⊢ᶜ I.M ≈ I.N ∶ I.X → LC.⟦ ⟦ I.M ⟧ᶜ ⟧ᶜ ≡ LC.⟦ ⟦ I.N ⟧ᶜ ⟧ᶜ
  sound = IC.eqComp
