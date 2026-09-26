module Inception.Inc.Translation where

open import Inception.Inc.Syntax as I hiding (ε; _∙_; here; there)
open import Inception.SystemL.Syntax as L

variable
  IΓ IΔ : I.Ctx
  IA : I.Ty

⟦_⟧ : I.Ty → L.Ty
⟦ `𝟙 ⟧     = `𝟙
⟦ X `× Y ⟧ = ⟦ X ⟧ `× ⟦ Y ⟧
⟦ X `⇒ Y ⟧ = ⟦ X ⟧ `⇒ ⟦ Y ⟧
⟦ `𝓅 ⟧     = `𝓅
⟦ `ℓ ⟧     = ⟦ `𝓅 ⟧ `⇒ `⊥

⟦_⟧ˣ : I.Ctx → L.Ctx
⟦ I.ε ⟧ˣ     = ε
⟦ Γ I.∙ X ⟧ˣ = ⟦ Γ ⟧ˣ ∙ ⟦ X ⟧

⟦_⟧ⁱ : IΓ I.∋ IA → ⟦ IΓ ⟧ˣ L.∋ ⟦ IA ⟧
⟦ I.here ⟧ⁱ   = here
⟦ I.there i ⟧ⁱ = there ⟦ i ⟧ⁱ

raiseP : L.Γ ⊢ᵛ (⟦ `𝓅 ⟧ `⇒ `⊥) ∣ L.Δ → L.Γ ⊢ᵛ ⟦ `𝓅 ⟧ ∣ L.Δ → L.Γ ⊢ᵗ L.X ∣ L.Δ
raiseP ref p = efq (applyL ref p)

installV : (L.Γ ∙ ⟦ `𝓅 ⟧) ⊢ᵗ L.X ∣ L.Δ → L.Γ ⊢ᵛ (⟦ `𝓅 ⟧ `⇒ `⊥) ∣ (L.Δ ∙ L.X)
installV {X = X} n = lam (μ (cut X (wk̃ᵗ (wk̃ᵗ n)) (covar (there here))))

⟦_⟧ᶜ : IΓ I.⊢ᶜ IA → ⟦ IΓ ⟧ˣ ⊢ᵗ ⟦ IA ⟧ ∣ L.Δ

⟦_⟧ᵛ : IΓ I.⊢ᵛ IA → ⟦ IΓ ⟧ˣ ⊢ᵛ ⟦ IA ⟧ ∣ L.Δ
⟦ I.var i ⟧ᵛ    = var ⟦ i ⟧ⁱ
⟦ I.lam M ⟧ᵛ    = lam ⟦ M ⟧ᶜ
⟦ I.pair V W ⟧ᵛ = pair ⟦ V ⟧ᵛ ⟦ W ⟧ᵛ
⟦ I.unit ⟧ᵛ     = unit

⟦_⟧ˢ : I.Sub IΓ IΔ → L.Sub ⟦ IΓ ⟧ˣ L.Δ ⟦ IΔ ⟧ˣ
⟦ I.sub-ε ⟧ˢ      = L.sub-ε
⟦ I.sub-ex θ V ⟧ˢ = L.sub-ex ⟦ θ ⟧ˢ ⟦ V ⟧ᵛ

⟦ I.return V ⟧ᶜ = ret ⟦ V ⟧ᵛ
⟦ I.pm V M ⟧ᶜ   = letpv ⟦ V ⟧ᵛ ⟦ M ⟧ᶜ
⟦ I.push M N ⟧ᶜ = lett ⟦ M ⟧ᶜ ⟦ N ⟧ᶜ
⟦ I.app V W ⟧ᶜ  = applyL ⟦ V ⟧ᵛ ⟦ W ⟧ᵛ
⟦ I.rec V W ⟧ᶜ  = raiseP ⟦ V ⟧ᵛ ⟦ W ⟧ᵛ
⟦ I.inc M N ⟧ᶜ  = μ (cut _ (L.letv (installV ⟦ N ⟧ᶜ) ⟦ M ⟧ᶜ) (covar here))
