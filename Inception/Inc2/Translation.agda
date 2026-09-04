module Inception.Inc2.Translation where

open import Inception.Inc2.Syntax as I
open import Inception.LamBarMuMuTilde.Syntax as L

variable
  IΓ IΔ : I.Ctx
  IA IB IC : I.Ty

⟦_⟧ : I.Ty -> L.Ty
⟦ `Unit ⟧  = `Unit
⟦ A `× B ⟧ = ⟦ A ⟧ `× ⟦ B ⟧
⟦ A `⇒ B ⟧ = ⟦ A ⟧ `⇒ ⟦ B ⟧
⟦ `P ⟧     = `Unit
⟦ `V ⟧     = ⟦ `P ⟧ `⇒ `⊥

⟦_⟧ˣ : I.Ctx -> L.Env
⟦ ε ⟧ˣ     = ε
⟦ Γ ∙ A ⟧ˣ = ⟦ Γ ⟧ˣ ∙ ⟦ A ⟧

⟦_⟧ⁱ : IΓ I.∋ IA -> ⟦ IΓ ⟧ˣ L.∋ ⟦ IA ⟧
⟦ I.h ⟧ⁱ   = z
⟦ I.t i ⟧ⁱ = s ⟦ i ⟧ⁱ

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

raiseP : L.Γ ⊢ᵛ (⟦ `P ⟧ `⇒ `⊥) ∣ L.Δ -> L.Γ ⊢ᵛ ⟦ `P ⟧ ∣ L.Δ -> L.Γ ⊢ᵗ L.A ∣ L.Δ
raiseP ref p = efq (applyL ref p)

installV : (L.Γ ∙ ⟦ `P ⟧) ⊢ᵗ L.A ∣ L.Δ -> L.Γ ⊢ᵛ (⟦ `P ⟧ `⇒ `⊥) ∣ (L.Δ ∙ L.A)
installV {A = A} n = lam (μ (cut A (wk̃ᵗ (wk̃ᵗ n)) (covar (s z))))

⟦_⟧ᶜ : IΓ I.⊢ᶜ IA -> ⟦ IΓ ⟧ˣ ⊢ᵗ ⟦ IA ⟧ ∣ L.Δ

⟦_⟧ᵛ : IΓ I.⊢ᵛ IA -> ⟦ IΓ ⟧ˣ ⊢ᵛ ⟦ IA ⟧ ∣ L.Δ
⟦ I.var i ⟧ᵛ    = var ⟦ i ⟧ⁱ
⟦ I.lam M ⟧ᵛ    = lam ⟦ M ⟧ᶜ
⟦ I.pair V W ⟧ᵛ = pair ⟦ V ⟧ᵛ ⟦ W ⟧ᵛ
⟦ I.unit ⟧ᵛ     = unit

⟦_⟧ˢ : I.Sub IΓ IΔ -> L.Sub ⟦ IΓ ⟧ˣ L.Δ ⟦ IΔ ⟧ˣ
⟦ I.sub-ε ⟧ˢ      = L.sub-ε
⟦ I.sub-ex θ V ⟧ˢ = L.sub-ex ⟦ θ ⟧ˢ ⟦ V ⟧ᵛ

⟦ I.return V ⟧ᶜ = ret ⟦ V ⟧ᵛ
⟦ I.pm V M ⟧ᶜ   = letpv ⟦ V ⟧ᵛ ⟦ M ⟧ᶜ
⟦ I.push M N ⟧ᶜ = lett ⟦ M ⟧ᶜ ⟦ N ⟧ᶜ
⟦ I.app V W ⟧ᶜ  = applyL ⟦ V ⟧ᵛ ⟦ W ⟧ᵛ
⟦ I.rec V W ⟧ᶜ  = raiseP ⟦ V ⟧ᵛ ⟦ W ⟧ᵛ
⟦ I.inc M N ⟧ᶜ  = μ (cut _ (L.letv (installV ⟦ N ⟧ᶜ) ⟦ M ⟧ᶜ) (covar z))
