{-# OPTIONS --no-postfix-projections #-}

open import Inception.Sub.Syntax using (Ty)

module Inception.Sub.TelescopeMachineLR (ℛ : Ty) where

open import Inception.Prelude
open import Inception.Sub.Syntax

open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Unit using (⊤; tt)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Inception.Sub.TelescopeMachine ℛ

open import Inception.Rewriting.Reduction _→ᶜ_

--data SN (σ : CState) : Set where
--  sn : (∀ {σ₁} → σ →ᶜ σ₁ → SN σ₁) → SN σ

Rᵛ : (X : Ty) → OMVal Γ X → MEnv Γ → Set
Rᵏ : (X : Ty) → CStack Γ X → Set
Rᴱ : MEnv Γ → Set

Rᵛ `𝟙 unit γ = ⊤
Rᵛ (X `× Y) (pair 𝐕 𝐖) γ = Rᵛ X 𝐕 γ × Rᵛ Y 𝐖 γ
Rᵛ {Γ = Γ} (X `⇒ Y) (lam M) γ =
            ∀ {Δ : Ctx} (π₁ : Δ ⊇ Γ)
              (𝐖 : OMVal Δ X) (δ : MEnv Δ)
              {Ψ : Ctx} (π₂ : Δ ⊇ Ψ)
            → Rᵛ X 𝐖 δ → {K : CStack Ψ Y} → Rᵏ Y K
            → SN ⟨ wk-comp (wk-cong π₁) M ╎ δ · 𝐖 ╎ wk-wk π₂ ╎ K ⟩
Rᵛ `ℓ (label x) γ = SN (lookup-label x γ)

Rᴱ {Γ = Γ} γ = ∀ {X : Ty} → (i : Γ ∋ X) → Rᵛ X (lookup i γ) γ

Rᵏ {Γ = Γ} X K = ∀ {Δ : Ctx} {𝐖 : OMVal Δ X} {δ : MEnv Δ} {π : Δ ⊇ Γ} → Rᵛ X 𝐖 δ → SN ⟨ 𝐖 ； δ ╎ π ╎ K ⟩

{-
Rᵛ-wk : {Δ : Ctx} {π : Wk Δ Γ} {γ : MEnv Γ} {𝐖 : OMVal Γ X}
        → (δ : MEnv Δ) → Rᵛ X 𝐖 γ → Rᵛ X (wk-omval π 𝐖) δ
Rᵛ-wk {𝐖 = unit} _ Rv = tt
Rᵛ-wk {π = π} {𝐖 = pair 𝐖 𝐕} δ (fst , snd) =
  let
    RW = Rᵛ-wk {π = π} δ fst
    RV = Rᵛ-wk {π = π} δ snd
  in
  RW , RV
Rᵛ-wk {𝐖 = lam M} δ Rv = λ π₁ 𝐖 δ₁ π₂ x x₁ → {!!}
Rᵛ-wk {𝐖 = label x} δ Rv =
  {!subst () !}

Rᴱ-ext : {γ : MEnv Γ} {𝐖 : OMVal Γ X} → Rᴱ γ → Rᵛ X 𝐖 γ → Rᴱ (γ · 𝐖)
Rᴱ-ext Rγ RW here = {!!}
Rᴱ-ext Rγ RW (there i) = {!!}
-}

{-
mutual

  fundamentalᵛ  : (W : Γ ⊢ᵛ X) → {Δ : Ctx} → {δ : MEnv Δ} → Rᴱ δ
                 → (π : Δ ⊇ Γ)
                 → Rᵛ X (eval (wk-val π W) δ) δ
  fundamentalᵛ (var i) Rδ π = Rδ (wk-mem π i)
  fundamentalᵛ (lam M) Rδ π π₁ 𝐖 δ₁ π₂ Rv Rk = fundamentalᶜ M {!!} (wk-trans (Wk.wk-cong π₁) (Wk.wk-cong π)) (wk-wk π₂) Rk
  fundamentalᵛ (pair V W) Rδ π = (fundamentalᵛ V Rδ π) , (fundamentalᵛ W Rδ π)
  fundamentalᵛ unit Rδ π = tt

  fundamentalᶜ : (M : Γ ⊢ᶜ X) → {Δ : Ctx} → {δ : MEnv Δ} → Rᴱ δ
                 → (π₁ : Δ ⊇ Γ)
                 → {Ψ : Ctx} → (π₂ : Δ ⊇ Ψ)
                 → {K : CStack Ψ X} → Rᵏ X K
                 → SN ⟨ wk-comp π₁ M ╎ δ ╎ π₂ ╎ K ⟩
  fundamentalᶜ (return W) Rδ π₁ π₂ Rk = sn (λ { eval→ → Rk (fundamentalᵛ W Rδ π₁) })
  fundamentalᶜ (pm W M) Rδ π₁ π₂ Rk = sn (λ { pmᶜ→ → {!!} })
  fundamentalᶜ (push M N) Rδ π₁ π₂ Rk = sn (λ { push→ →
                                                fundamentalᶜ M {!!} π₁ wk-id {!!} })
  fundamentalᶜ (app V W) Rδ π₁ π₂ Rk = sn (λ { app→ → {!!} })
  fundamentalᶜ (var W) Rδ π₁ π₂ Rk = sn (λ { var→ → {!!} })
  fundamentalᶜ (sub M N) Rδ π₁ π₂ Rk = sn (λ { sub→ → {!!} })
-}
