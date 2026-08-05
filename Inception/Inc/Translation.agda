module Inception.Inc.Translation where

open import Inception.Inc.Syntax as I
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

letpm : L.Γ ⊢ᵗ (L.A₁ `× L.A₂) ∣ L.Δ -> (L.Γ ∙ L.A₁ ∙ L.A₂) ⊢ᵗ L.B ∣ L.Δ -> L.Γ ⊢ᵗ L.B ∣ L.Δ
letpm p cont =
  lett p
    (lett (projFst (var z))
      (lett (projSnd (var (s z)))
        (sub-tm (L.sub-ex (L.sub-ex (L.sub-wk (L.wk-wk (L.wk-wk (L.wk-wk L.wk-id))) L.wk-id L.sub-id) (var (s z))) (var z)) cosub-id cont)))

efq : L.Γ ⊢ᵗ `⊥ ∣ L.Δ -> L.Γ ⊢ᵗ L.A ∣ L.Δ
efq u = μ (cut `⊥ (wk̃ᵗ u) tp)

raiseP : L.Γ ⊢ᵛ (⟦ `P ⟧ `⇒ `⊥) ∣ L.Δ -> L.Γ ⊢ᵛ ⟦ `P ⟧ ∣ L.Δ -> L.Γ ⊢ᵗ L.A ∣ L.Δ
raiseP ref p = efq (applyL ref p)

installV : (L.Γ ∙ ⟦ `P ⟧) ⊢ᵗ L.A ∣ L.Δ -> L.Γ ⊢ᵛ (⟦ `P ⟧ `⇒ `⊥) ∣ (L.Δ ∙ L.A)
installV {A = A} n = lam (μ (cut A (wk̃ᵗ (wk̃ᵗ n)) (covar (s z))))

⟦_⟧ᶜ : IΓ I.⊢ᶜ IA -> ⟦ IΓ ⟧ˣ ⊢ᵗ ⟦ IA ⟧ ∣ L.Δ

varVal : IΓ I.∋ IA -> ⟦ IΓ ⟧ˣ ⊢ᵛ ⟦ IA ⟧ ∣ L.Δ
varVal i = var ⟦ i ⟧ⁱ

lamVal : (IΓ I.∙ IA) I.⊢ᶜ IB -> ⟦ IΓ ⟧ˣ ⊢ᵛ (⟦ IA ⟧ `⇒ ⟦ IB ⟧) ∣ L.Δ
lamVal M = lam ⟦ M ⟧ᶜ

⟦_⟧ᵗ : IΓ I.⊢ᵛ IA -> ⟦ IΓ ⟧ˣ ⊢ᵗ ⟦ IA ⟧ ∣ L.Δ
⟦ I.var i ⟧ᵗ    = ret (varVal i)
⟦ I.lam M ⟧ᵗ    = ret (lamVal M)
⟦ I.pair V W ⟧ᵗ = lett ⟦ V ⟧ᵗ (lett (wkᵗ ⟦ W ⟧ᵗ) (ret (pair (var (s z)) (var z))))
⟦ I.pm V W ⟧ᵗ   = letpm ⟦ V ⟧ᵗ ⟦ W ⟧ᵗ
⟦ I.unit ⟧ᵗ     = ret unit

⟦ I.return V ⟧ᶜ   = ⟦ V ⟧ᵗ
⟦ I.pm V M ⟧ᶜ     = letpm ⟦ V ⟧ᵗ ⟦ M ⟧ᶜ
⟦ I.push M N ⟧ᶜ   = lett ⟦ M ⟧ᶜ ⟦ N ⟧ᶜ
⟦ I.app V W ⟧ᶜ    = lett ⟦ V ⟧ᵗ (lett (wkᵗ ⟦ W ⟧ᵗ) (applyL (var (s z)) (var z)))
⟦ I.rec V W ⟧ᶜ    = lett ⟦ V ⟧ᵗ (lett (wkᵗ ⟦ W ⟧ᵗ) (raiseP (var (s z)) (var z)))
⟦ I.inc M N ⟧ᶜ    = μ (cut _ (L.letv (installV ⟦ N ⟧ᶜ) ⟦ M ⟧ᶜ) (covar z))
