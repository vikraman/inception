open import Inception.LamLamBar.Syntax

module Inception.Translation.Inc.LamLamBar (𝒫 : Ty) where

import Inception.Inc.Syntax as I

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
