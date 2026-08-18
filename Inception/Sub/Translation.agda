module Inception.Sub.Translation where

open import Inception.Sub.Syntax as S
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

letpm : L.Γ ⊢ᵗ (L.A₁ `× L.A₂) ∣ L.Δ -> (L.Γ ∙ L.A₁ ∙ L.A₂) ⊢ᵗ L.B ∣ L.Δ -> L.Γ ⊢ᵗ L.B ∣ L.Δ
letpm p cont =
  lett p
    (lett (projFst (var z))
      (lett (projSnd (var (s z)))
        (sub-tm (L.sub-ex (L.sub-ex (L.sub-wk (L.wk-wk (L.wk-wk (L.wk-wk L.wk-id))) L.wk-id L.sub-id) (var (s z))) (var z)) cosub-id cont)))

letpv : L.Γ ⊢ᵛ L.A₁ `× L.A₂ ∣ L.Δ -> (L.Γ ∙ L.A₁ ∙ L.A₂) ⊢ᵛ L.B ∣ L.Δ -> L.Γ ⊢ᵗ L.B ∣ L.Δ
letpv V W = lett (projFst V) (lett (projSnd (wkᵛ V)) (ret W))

efq : L.Γ ⊢ᵗ `⊥ ∣ L.Δ -> L.Γ ⊢ᵗ L.A ∣ L.Δ
efq u = μ (cut `⊥ (wk̃ᵗ u) tp)

raise : L.Γ ⊢ᵛ (`Unit `⇒ `⊥) ∣ L.Δ -> L.Γ ⊢ᵗ L.A ∣ L.Δ
raise ref = efq (applyL ref unit)

handleVal : L.Γ ⊢ᵗ L.A ∣ L.Δ -> L.Γ ⊢ᵛ (`Unit `⇒ `⊥) ∣ (L.Δ ∙ L.A)
handleVal {A = A} n =
  lam (μ (cut A (wk-tm (L.wk-wk L.wk-id) (L.wk-wk (L.wk-wk L.wk-id)) n) (covar (s z))))

⟦_⟧ᶜ : SΓ S.⊢ᶜ SA -> ⟦ SΓ ⟧ˣ ⊢ᵗ ⟦ SA ⟧ ∣ L.Δ

varVal : SΓ S.∋ SA -> ⟦ SΓ ⟧ˣ ⊢ᵛ ⟦ SA ⟧ ∣ L.Δ
varVal i = var ⟦ i ⟧ⁱ

lamVal : (SΓ S.∙ SA) S.⊢ᶜ SB -> ⟦ SΓ ⟧ˣ ⊢ᵛ (⟦ SA ⟧ `⇒ ⟦ SB ⟧) ∣ L.Δ
lamVal M = lam ⟦ M ⟧ᶜ

⟦_⟧ᵗ : SΓ S.⊢ᵖ SA -> ⟦ SΓ ⟧ˣ ⊢ᵗ ⟦ SA ⟧ ∣ L.Δ
⟦ S.var i ⟧ᵗ    = ret (varVal i)
⟦ S.lam M ⟧ᵗ    = ret (lamVal M)
⟦ S.pair V W ⟧ᵗ = lett ⟦ V ⟧ᵗ (lett (wkᵗ ⟦ W ⟧ᵗ) (ret (pair (var (s z)) (var z))))
⟦ S.pm V W ⟧ᵗ   = letpm ⟦ V ⟧ᵗ ⟦ W ⟧ᵗ
⟦ S.unit ⟧ᵗ     = ret unit

⟦ S.return V ⟧ᶜ  = ⟦ V ⟧ᵗ
⟦ S.pm V M ⟧ᶜ    = letpm ⟦ V ⟧ᵗ ⟦ M ⟧ᶜ
⟦ S.push M N ⟧ᶜ  = lett ⟦ M ⟧ᶜ ⟦ N ⟧ᶜ
⟦ S.app V W ⟧ᶜ   = lett ⟦ V ⟧ᵗ (lett (wkᵗ ⟦ W ⟧ᵗ) (applyL (var (s z)) (var z)))
⟦ S.var V ⟧ᶜ     = lett ⟦ V ⟧ᵗ (raise (var z))
⟦ S.sub M N ⟧ᶜ   = μ (cut _ (L.letv (handleVal ⟦ N ⟧ᶜ) ⟦ M ⟧ᶜ) (covar z))
