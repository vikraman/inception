module Inception.Sub.Translation where

open import Inception.Sub.Syntax as S hiding (ε; _∙_; here; there)
open import Inception.SystemL.Syntax as L

variable
  SΓ SΔ : S.Ctx
  SA : S.Ty

⟦_⟧ : S.Ty -> L.Ty
⟦ `𝟙 ⟧  = `𝟙
⟦ A `× B ⟧ = ⟦ A ⟧ `× ⟦ B ⟧
⟦ A `⇒ B ⟧ = ⟦ A ⟧ `⇒ ⟦ B ⟧
⟦ `ℓ ⟧     = `𝟙 `⇒ `⊥

⟦_⟧ˣ : S.Ctx -> L.Ctx
⟦ S.ε ⟧ˣ     = ε
⟦ Γ S.∙ A ⟧ˣ = ⟦ Γ ⟧ˣ ∙ ⟦ A ⟧

⟦_⟧ⁱ : SΓ S.∋ SA -> ⟦ SΓ ⟧ˣ L.∋ ⟦ SA ⟧
⟦ S.here ⟧ⁱ   = here
⟦ S.there i ⟧ⁱ = there ⟦ i ⟧ⁱ

raise : L.Γ ⊢ᵛ (`𝟙 `⇒ `⊥) ∣ L.Δ -> L.Γ ⊢ᵗ L.A ∣ L.Δ
raise ref = efq (applyL ref unit)

handleVal : L.Γ ⊢ᵗ L.A ∣ L.Δ -> L.Γ ⊢ᵛ (`𝟙 `⇒ `⊥) ∣ (L.Δ ∙ L.A)
handleVal {A = A} n =
  lam (μ (cut A (wk-tm (L.wk-wk L.wk-id) (L.wk-wk (L.wk-wk L.wk-id)) n) (covar (there here))))

⟦_⟧ᶜ : SΓ S.⊢ᶜ SA -> ⟦ SΓ ⟧ˣ ⊢ᵗ ⟦ SA ⟧ ∣ L.Δ

⟦_⟧ᵛ : SΓ S.⊢ᵛ SA -> ⟦ SΓ ⟧ˣ ⊢ᵛ ⟦ SA ⟧ ∣ L.Δ
⟦ S.var i ⟧ᵛ    = var ⟦ i ⟧ⁱ
⟦ S.lam M ⟧ᵛ    = lam ⟦ M ⟧ᶜ
⟦ S.pair V W ⟧ᵛ = pair ⟦ V ⟧ᵛ ⟦ W ⟧ᵛ
⟦ S.unit ⟧ᵛ     = unit

⟦_⟧ˢ : S.Sub SΓ SΔ -> L.Sub ⟦ SΓ ⟧ˣ L.Δ ⟦ SΔ ⟧ˣ
⟦ S.sub-ε ⟧ˢ      = L.sub-ε
⟦ S.sub-ex θ V ⟧ˢ = L.sub-ex ⟦ θ ⟧ˢ ⟦ V ⟧ᵛ

⟦ S.return V ⟧ᶜ = ret ⟦ V ⟧ᵛ
⟦ S.pm V M ⟧ᶜ   = letpv ⟦ V ⟧ᵛ ⟦ M ⟧ᶜ
⟦ S.push M N ⟧ᶜ = lett ⟦ M ⟧ᶜ ⟦ N ⟧ᶜ
⟦ S.app V W ⟧ᶜ  = applyL ⟦ V ⟧ᵛ ⟦ W ⟧ᵛ
⟦ S.var V ⟧ᶜ    = raise ⟦ V ⟧ᵛ
⟦ S.sub M N ⟧ᶜ  = μ (cut _ (L.letv (handleVal ⟦ N ⟧ᶜ) ⟦ M ⟧ᶜ) (covar here))
