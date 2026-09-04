module Inception.Sub2.Translation where

open import Inception.Sub2.Syntax as S
open import Inception.LamBarMuMuTilde.Syntax as L

variable
  SΓ SΔ : S.Ctx
  SA SB SC : S.Ty

⟦_⟧ : S.Ty -> L.Ty
⟦ `Unit ⟧  = `Unit
⟦ A `× B ⟧ = ⟦ A ⟧ `× ⟦ B ⟧
⟦ A `⇒ B ⟧ = ⟦ A ⟧ `⇒ ⟦ B ⟧
⟦ `V ⟧     = `Unit `⇒ `⊥

⟦_⟧ˣ : S.Ctx -> L.Env
⟦ ε ⟧ˣ     = ε
⟦ Γ ∙ A ⟧ˣ = ⟦ Γ ⟧ˣ ∙ ⟦ A ⟧

⟦_⟧ⁱ : SΓ S.∋ SA -> ⟦ SΓ ⟧ˣ L.∋ ⟦ SA ⟧
⟦ S.h ⟧ⁱ   = z
⟦ S.t i ⟧ⁱ = s ⟦ i ⟧ⁱ

applyL : L.Γ ⊢ᵛ (L.A `⇒ L.B) ∣ L.Δ -> L.Γ ⊢ᵛ L.A ∣ L.Δ -> L.Γ ⊢ᵗ L.B ∣ L.Δ
applyL f a = μ (cut _ (ret (wk̃ᵛ f)) (app (wk̃ᵛ a) (covar z)))

projFst : L.Γ ⊢ᵛ (L.A `× L.B) ∣ L.Δ -> L.Γ ⊢ᵗ L.A ∣ L.Δ
projFst p = μ (cut _ (ret (wk̃ᵛ p)) (fst (covar z)))

projSnd : L.Γ ⊢ᵛ (L.A `× L.B) ∣ L.Δ -> L.Γ ⊢ᵗ L.B ∣ L.Δ
projSnd p = μ (cut _ (ret (wk̃ᵛ p)) (snd (covar z)))

letpv : L.Γ ⊢ᵛ L.A₁ `× L.A₂ ∣ L.Δ -> (L.Γ ∙ L.A₁ ∙ L.A₂) ⊢ᵗ L.B ∣ L.Δ -> L.Γ ⊢ᵗ L.B ∣ L.Δ
letpv V M = lett (projFst V) (lett (projSnd (wkᵛ V)) M)

efq : L.Γ ⊢ᵗ `⊥ ∣ L.Δ -> L.Γ ⊢ᵗ L.A ∣ L.Δ
efq u = μ (cut `⊥ (wk̃ᵗ u) tp)

raise : L.Γ ⊢ᵛ (`Unit `⇒ `⊥) ∣ L.Δ -> L.Γ ⊢ᵗ L.A ∣ L.Δ
raise ref = efq (applyL ref unit)

handleVal : L.Γ ⊢ᵗ L.A ∣ L.Δ -> L.Γ ⊢ᵛ (`Unit `⇒ `⊥) ∣ (L.Δ ∙ L.A)
handleVal {A = A} n =
  lam (μ (cut A (wk-tm (L.wk-wk L.wk-id) (L.wk-wk (L.wk-wk L.wk-id)) n) (covar (s z))))

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
⟦ S.sub M N ⟧ᶜ  = μ (cut _ (L.letv (handleVal ⟦ N ⟧ᶜ) ⟦ M ⟧ᶜ) (covar z))
