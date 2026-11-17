module Inception.Ctx.Map {Ty₁ Ty₂ : Set} (⟦_⟧ : Ty₁ → Ty₂) where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)

import Inception.Ctx

private
  module Src = Inception.Ctx Ty₁
  module Tgt = Inception.Ctx Ty₂

--------------------------------------------------------------------------
-- contexts, variables and weakenings

⟦_⟧ˣ : Src.Ctx → Tgt.Ctx
⟦ Src.ε ⟧ˣ     = Tgt.ε
⟦ Γ Src.∙ X ⟧ˣ = ⟦ Γ ⟧ˣ Tgt.∙ ⟦ X ⟧

⟦_⟧ⁱ : Src.Γ Src.∋ Src.X → ⟦ Src.Γ ⟧ˣ Tgt.∋ ⟦ Src.X ⟧
⟦ Src.here ⟧ⁱ    = Tgt.here
⟦ Src.there i ⟧ⁱ = Tgt.there ⟦ i ⟧ⁱ

⟦_⟧ʷ : Src.Γ Src.⊇ Src.Δ → ⟦ Src.Γ ⟧ˣ Tgt.⊇ ⟦ Src.Δ ⟧ˣ
⟦ Src.wk-ε ⟧ʷ      = Tgt.wk-ε
⟦ Src.wk-cong π ⟧ʷ = Tgt.wk-cong ⟦ π ⟧ʷ
⟦ Src.wk-wk π ⟧ʷ   = Tgt.wk-wk ⟦ π ⟧ʷ

--------------------------------------------------------------------------
-- translation laws

⟦-⟧ʷ-id-β : ⟦ Src.wk-id {Src.Γ} ⟧ʷ ≡ Tgt.wk-id
⟦-⟧ʷ-id-β {Src.ε}     = refl
⟦-⟧ʷ-id-β {Γ Src.∙ X} = cong Tgt.wk-cong (⟦-⟧ʷ-id-β {Γ})
{-# REWRITE ⟦-⟧ʷ-id-β #-}

⟦-⟧ʷ-trans-η : (π : Src.Γ Src.⊇ Src.Δ) (δ : Src.Δ Src.⊇ Src.Ψ) → ⟦ Src.wk-trans π δ ⟧ʷ ≡ Tgt.wk-trans ⟦ π ⟧ʷ ⟦ δ ⟧ʷ
⟦-⟧ʷ-trans-η Src.wk-ε δ                    = refl
⟦-⟧ʷ-trans-η (Src.wk-cong π) (Src.wk-cong δ) = cong Tgt.wk-cong (⟦-⟧ʷ-trans-η π δ)
⟦-⟧ʷ-trans-η (Src.wk-cong π) (Src.wk-wk δ)   = cong Tgt.wk-wk (⟦-⟧ʷ-trans-η π δ)
⟦-⟧ʷ-trans-η (Src.wk-wk π) δ                 = cong Tgt.wk-wk (⟦-⟧ʷ-trans-η π δ)
{-# REWRITE ⟦-⟧ʷ-trans-η #-}

⟦-⟧ⁱ-wk-η : (π : Src.Γ Src.⊇ Src.Δ) (i : Src.Δ Src.∋ Src.X) → ⟦ Src.wk-mem π i ⟧ⁱ ≡ Tgt.wk-mem ⟦ π ⟧ʷ ⟦ i ⟧ⁱ
⟦-⟧ⁱ-wk-η (Src.wk-cong π) Src.here      = refl
⟦-⟧ⁱ-wk-η (Src.wk-wk π) Src.here        = cong Tgt.there (⟦-⟧ⁱ-wk-η π Src.here)
⟦-⟧ⁱ-wk-η (Src.wk-cong π) (Src.there i) = cong Tgt.there (⟦-⟧ⁱ-wk-η π i)
⟦-⟧ⁱ-wk-η (Src.wk-wk π) (Src.there i)   = cong Tgt.there (⟦-⟧ⁱ-wk-η π (Src.there i))
{-# REWRITE ⟦-⟧ⁱ-wk-η #-}
