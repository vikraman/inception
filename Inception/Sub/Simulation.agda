{-# OPTIONS --no-postfix-projections #-}

open import Inception.Sub.Syntax using (Ty)

module Inception.Sub.Simulation (ℛ : Ty) where

open import Inception.Prelude
open import Inception.Rewriting
open import Inception.Sub.Syntax

open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; subst; cong; cong₂)
open Eq.≡-Reasoning using (step-≡-⟩; step-≡-∣; step-≡-⟨; _∎; step-≡)

import Inception.Sub.Machine ℛ as M
import Inception.Sub.TelescopeMachine ℛ as TM
open M using (⟨_╎_⟩; ⟨_╎_╎_⟩; _·_; ◻; <_；_>∷_; ⋄; jumpᵛ; unitᵛ; pairᵛ; cloᵛ; eval→; return→; push→; sub→; var→; pmᶜ→; app→; progress) renaming (_→ᶜ_ to _→ᴹ_)
open TM using (⟨_；_╎_╎_⟩; ⟨_╎_╎_╎_⟩; <_；_；_>∷_; _·_; _·﹝_╎_╎_﹞; ⋄; ◻; unit; pair; lam; label; eval→; return→; push→; sub→; var→; pmᶜ→; app→) renaming (_→ᶜ_ to _→ᵀᴹ_)

---------------------------------------------------------------------------------
-- Properties of Inception.Sub.Machine
---------------------------------------------------------------------------------

-- Weakening of Machine Values, Environments and Stacks
mutual

  data WkMVal : (𝐖₁ : M.MVal X) → (𝐖₂ : M.MVal X) → Set where

      wk-unitᵛ : WkMVal M.unitᵛ M.unitᵛ

      wk-pairᵛ : {𝐖₁₁ 𝐖₁₂ : M.MVal X₁} {𝐖₂₁ 𝐖₂₂ : M.MVal X₂} → WkMVal 𝐖₁₁ 𝐖₁₂ → WkMVal 𝐖₂₁ 𝐖₂₂ → WkMVal (M.pairᵛ 𝐖₁₁ 𝐖₂₁) (M.pairᵛ 𝐖₁₂ 𝐖₂₂)

      wk-cloᵛ : {Γ₁ Γ₂ : Ctx} {M₁ : Comp (Γ₁ ∙ X) Y} {M₂ : Comp (Γ₂ ∙ X) Y} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} → (π : Wk Γ₁ Γ₂) → M₁ ≡ wk-comp (wk-cong π) M₂ → (WkMEnvᴹ π γ₁ γ₂) → WkMVal (M.cloᵛ M₁ γ₁) (M.cloᵛ M₂ γ₂)

      wk-jumpᵛ : {Γ₁ Γ₂ : Ctx} {M₁ : Comp Γ₁ X} {M₂ : Comp Γ₂ X} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} {K₁ K₂ : M.CStack X} → (π : Wk Γ₁ Γ₂) → M₁ ≡ wk-comp π M₂ → (WkMEnvᴹ π γ₁ γ₂) → (WkCStackᴹ K₁ K₂) → WkMVal (M.jumpᵛ M₁ γ₁ K₁) (M.jumpᵛ M₂ γ₂ K₂)

  data WkMEnvᴹ : {Γ₁ Γ₂ : Ctx} → (π : Wk Γ₁ Γ₂) → (γ₁ : M.MEnv Γ₁) → (γ₂ : M.MEnv Γ₂) → Set where

      wk-menv-ε    : WkMEnvᴹ wk-ε M.⋄ M.⋄

      wk-menv-cong : {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} {𝐖₁ : M.MVal X} {𝐖₂ : M.MVal X} → WkMVal 𝐖₁ 𝐖₂ → WkMEnvᴹ π γ₁ γ₂ → WkMEnvᴹ (wk-cong π) (γ₁ · 𝐖₁) (γ₂ · 𝐖₂)

      wk-menv-wk : {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} → (𝐖 : M.MVal X) → WkMEnvᴹ π γ₁ γ₂ → WkMEnvᴹ (wk-wk π) (γ₁ · 𝐖) γ₂

  data WkCStackᴹ : (K₁ : M.CStack X) → (K₂ : M.CStack X) → Set where

    wk-cstack-empty : WkCStackᴹ ◻ ◻

    wk-cstack-push : {Γ₁ Γ₂ : Ctx} {M₁ : (Γ₁ ∙ Y) ⊢ᶜ X} {M₂ : (Γ₂ ∙ Y) ⊢ᶜ X} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} {K₁ K₂ : M.CStack X}
                    → (π : Wk Γ₁ Γ₂) → M₁ ≡ wk-comp (wk-cong π) M₂ → WkMEnvᴹ π γ₁ γ₂ → WkCStackᴹ K₁ K₂
                    → WkCStackᴹ (< M₁ ； γ₁ >∷ K₁) (< M₂ ； γ₂ >∷ K₂)

-- Weakening of Machine States
data WkCStateᴹ : M.CState → M.CState → Set where

  wk-cstate-result : {𝐖₁ 𝐖₂ : M.MVal X} {K₁ K₂ : M.CStack X}
                     → WkMVal 𝐖₁ 𝐖₂ → WkCStackᴹ K₁ K₂
                     → WkCStateᴹ ⟨ 𝐖₁ ╎ K₁ ⟩ ⟨ 𝐖₂ ╎ K₂ ⟩

  wk-cstate-comp : {Γ₁ Γ₂ : Ctx} {M₁ : Γ₁ ⊢ᶜ X} {M₂ : Γ₂ ⊢ᶜ X} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} {K₁ K₂ : M.CStack X}
                   → (π : Wk Γ₁ Γ₂) → M₁ ≡ wk-comp π M₂ → (WkMEnvᴹ π γ₁ γ₂) → WkCStackᴹ K₁ K₂
                   → WkCStateᴹ ⟨ M₁ ╎ γ₁ ╎ K₁ ⟩ ⟨ M₂ ╎ γ₂ ╎ K₂ ⟩

data _≈₀ᴹ_ : M.CState → M.CState → Set where

    ≈-wk₁ : {σ₁ σ₂ : M.CState} → WkCStateᴹ σ₁ σ₂ → σ₂ ≈₀ᴹ σ₁

    ≈-wk₂ : {σ₁ σ₂ : M.CState} → WkCStateᴹ σ₁ σ₂ → σ₁ ≈₀ᴹ σ₂

-- Equivalence of states
data _≈ᴹ_ : M.CState → M.CState → Set where

    ≈ᴹ-bc   : {σ₁ σ₂ : M.CState} → σ₁ ≈₀ᴹ σ₂ → σ₁ ≈ᴹ σ₂

    ≈-trans : {σ₁ σ₂ σ₃ : M.CState} → σ₁ ≈₀ᴹ σ₂ → σ₂ ≈ᴹ σ₃ → σ₁ ≈ᴹ σ₃

mutual

  wk-mval-id : {𝐖 : M.MVal X} → WkMVal 𝐖 𝐖
  wk-mval-id {𝐖 = M.unitᵛ} = wk-unitᵛ
  wk-mval-id {𝐖 = M.pairᵛ 𝐖 𝐖₁} = wk-pairᵛ wk-mval-id wk-mval-id
  wk-mval-id {𝐖 = M.cloᵛ M γ} = wk-cloᵛ wk-id refl wk-menv-id
  wk-mval-id {𝐖 = M.jumpᵛ M γ K} = wk-jumpᵛ wk-id refl wk-menv-id wk-cstack-id

  wk-menv-id : {γ : M.MEnv Γ} → WkMEnvᴹ wk-id γ γ
  wk-menv-id {γ = ⋄} = wk-menv-ε
  wk-menv-id {γ = γ · 𝐖} = wk-menv-cong wk-mval-id wk-menv-id

  wk-cstack-id : {K : M.CStack X} → WkCStackᴹ K K
  wk-cstack-id {K = ◻} = wk-cstack-empty
  wk-cstack-id {K = < x ； γ >∷ K} = wk-cstack-push wk-id refl wk-menv-id wk-cstack-id

wk-mclo-wk-η : {Γ : Ctx} {X : Ty} → (𝐖 : TM.MClo Γ X) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → TM.wk-mclo π (TM.wk-mclo δ 𝐖) ≡ TM.wk-mclo (wk-trans π δ) 𝐖
wk-mclo-wk-η TM.unit π δ = refl
wk-mclo-wk-η (TM.pair 𝐖₁ 𝐖₂) π δ = cong₂ TM.pair (wk-mclo-wk-η 𝐖₁ π δ) (wk-mclo-wk-η 𝐖₂ π δ)
wk-mclo-wk-η (TM.lam M) π δ = cong TM.lam (wk-comp-id-β (wk-comp (wk-trans (Wk.wk-cong π) (Wk.wk-cong δ)) M))
wk-mclo-wk-η (TM.label x) π δ = refl

mutual

  wk-MEnvᴹ-trans : {Γ₁ Γ₂ Γ₃ : Ctx} {π₁ : Wk Γ₁ Γ₂} {π₂ : Wk Γ₂ Γ₃} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} {γ₃ : M.MEnv Γ₃} → WkMEnvᴹ π₁ γ₁ γ₂ → WkMEnvᴹ π₂ γ₂ γ₃ → WkMEnvᴹ (wk-trans π₁ π₂) γ₁ γ₃
  wk-MEnvᴹ-trans wk-menv-ε wk-menv-ε = wk-menv-ε
  wk-MEnvᴹ-trans (wk-menv-cong x₁ ϖ₁) (wk-menv-cong x₂ ϖ₂) = wk-menv-cong (wk-mval-trans x₁ x₂) (wk-MEnvᴹ-trans ϖ₁ ϖ₂)
  wk-MEnvᴹ-trans (wk-menv-cong {𝐖₁ = 𝐖₁} x₁ ϖ₁) (wk-menv-wk 𝐖₂ ϖ₂) = wk-menv-wk 𝐖₁ (wk-MEnvᴹ-trans ϖ₁ ϖ₂)
  wk-MEnvᴹ-trans (wk-menv-wk 𝐖 ϖ) wk-menv-ε = wk-menv-wk 𝐖 ϖ
  wk-MEnvᴹ-trans (wk-menv-wk 𝐖₁ ϖ₁) (wk-menv-cong x₂ ϖ₂) = wk-menv-wk 𝐖₁ (wk-MEnvᴹ-trans ϖ₁ (wk-menv-cong x₂ ϖ₂))
  wk-MEnvᴹ-trans (wk-menv-wk 𝐖₁ ϖ₁) (wk-menv-wk 𝐖₂ ϖ₂) = wk-menv-wk 𝐖₁ (wk-MEnvᴹ-trans ϖ₁ (wk-menv-wk 𝐖₂ ϖ₂))

  wk-cstack-trans : {K₁ K₂ K₃ : M.CStack X} → WkCStackᴹ K₁ K₂ → WkCStackᴹ K₂ K₃ → WkCStackᴹ K₁ K₃
  wk-cstack-trans wk-cstack-empty wk-cstack-empty = wk-cstack-empty
  wk-cstack-trans (wk-cstack-push {M₁ = M₁₁} {M₂ = M₂₁} π₁ eq₁ ϖ₁ x₁) (wk-cstack-push {M₁ = M₁₂} {M₂ = M₂₂} π₂ eq₂ ϖ₂ x₂) =
                        wk-cstack-push
                          (wk-trans π₁ π₂)
                          (M₁₁ ≡⟨ eq₁ ⟩ wk-comp (wk-cong π₁) M₂₁ ≡⟨ cong (wk-comp (wk-cong π₁)) eq₂ ⟩ wk-comp (wk-cong (wk-trans π₁ π₂)) M₂₂ ∎)
                          (wk-MEnvᴹ-trans ϖ₁ ϖ₂)
                          (wk-cstack-trans x₁ x₂)

  wk-mval-trans : {𝐖₁ 𝐖₂ 𝐖₃ : M.MVal X} → WkMVal 𝐖₁ 𝐖₂ → WkMVal 𝐖₂ 𝐖₃ → WkMVal 𝐖₁ 𝐖₃
  wk-mval-trans wk-unitᵛ wk-unitᵛ = wk-unitᵛ
  wk-mval-trans (wk-pairᵛ w₁ w₂) (wk-pairᵛ w₃ w₄) = wk-pairᵛ (wk-mval-trans w₁ w₃) (wk-mval-trans w₂ w₄)
  wk-mval-trans (wk-cloᵛ {M₁ = M₁₁} {M₂ = M₂₁} π₁ eq₁ x₁) (wk-cloᵛ {M₁ = M₁₂} {M₂ = M₂₂} π₂ eq₂ x₂) =
                        wk-cloᵛ
                          (wk-trans π₁ π₂)
                          (M₁₁
                            ≡⟨ eq₁ ⟩
                            wk-comp (wk-cong π₁) M₂₁
                            ≡⟨ cong (wk-comp (wk-cong π₁)) eq₂ ⟩
                            wk-comp (wk-cong π₁) (wk-comp (wk-cong π₂) M₂₂)
                            ≡⟨ wk-comp-wk-η M₂₂ (wk-cong π₁) (wk-cong π₂) ⟩
                            wk-comp (wk-cong (wk-trans π₁ π₂)) M₂₂ ∎)
                          (wk-MEnvᴹ-trans x₁ x₂)
  wk-mval-trans (wk-jumpᵛ {M₁ = M₁₁} {M₂ = M₂₁} π₁ eq₁ x₁ y₁) (wk-jumpᵛ {M₁ = M₁₂} {M₂ = M₂₂} π₂ eq₂ x₂ y₂) =
                        wk-jumpᵛ
                          (wk-trans π₁ π₂)
                          (M₁₁ ≡⟨ eq₁ ⟩ wk-comp π₁ M₂₁ ≡⟨ cong (wk-comp π₁) eq₂ ⟩ wk-comp (wk-trans π₁ π₂) M₂₂ ∎)
                          (wk-MEnvᴹ-trans x₁ x₂)
                          (wk-cstack-trans y₁ y₂)

wk-cstate-trans : {σ₁ σ₂ σ₃ : M.CState} → WkCStateᴹ σ₁ σ₂ → WkCStateᴹ σ₂ σ₃ → WkCStateᴹ σ₁ σ₃
wk-cstate-trans (wk-cstate-result ϖ₁ x₁) (wk-cstate-result ϖ₂ x₂) = wk-cstate-result (wk-mval-trans ϖ₁ ϖ₂) (wk-cstack-trans x₁ x₂)
wk-cstate-trans (wk-cstate-comp {M₁ = M₁₁} {M₂ = M₂₁} π₁ eq₁ ϖ₁ x₁) (wk-cstate-comp {M₁ = M₁₂} {M₂ = M₂₂} π₂ eq₂ ϖ₂ x₂) =
                        wk-cstate-comp
                          (wk-trans π₁ π₂)
                          (M₁₁ ≡⟨ eq₁ ⟩ wk-comp π₁ M₂₁ ≡⟨ cong (wk-comp π₁) eq₂ ⟩ wk-comp (wk-trans π₁ π₂) M₂₂ ∎)
                          (wk-MEnvᴹ-trans ϖ₁ ϖ₂)
                          (wk-cstack-trans x₁ x₂)

≈ᴹ-refl : {σ : M.CState} → σ ≈ᴹ σ
≈ᴹ-refl {σ = ⟨ 𝐖 ╎ K ⟩} = ≈ᴹ-bc (≈-wk₂ (wk-cstate-result wk-mval-id wk-cstack-id))
≈ᴹ-refl {σ = ⟨ M ╎ γ ╎ K ⟩} = ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp wk-id refl wk-menv-id wk-cstack-id))

≈₀ᴹ-sym : {σ₁ σ₂ : M.CState} → σ₁ ≈₀ᴹ σ₂ → σ₂ ≈₀ᴹ σ₁
≈₀ᴹ-sym (≈-wk₁ x) = (≈-wk₂ x)
≈₀ᴹ-sym (≈-wk₂ x) = (≈-wk₁ x)

mutual
  ≈ᴹ-sym : {σ₁ σ₂ : M.CState} → σ₁ ≈ᴹ σ₂ → σ₂ ≈ᴹ σ₁
  ≈ᴹ-sym (≈ᴹ-bc (≈-wk₁ x)) = ≈ᴹ-bc (≈-wk₂ x)
  ≈ᴹ-sym (≈ᴹ-bc (≈-wk₂ x)) = ≈ᴹ-bc (≈-wk₁ x)
  ≈ᴹ-sym (≈-trans x y) = ≈ᴹ-trans (≈ᴹ-sym y) (≈ᴹ-bc (≈₀ᴹ-sym x))

  ≈ᴹ-trans : {σ₁ σ₂ σ₃ : M.CState} → σ₁ ≈ᴹ σ₂ → σ₂ ≈ᴹ σ₃ → σ₁ ≈ᴹ σ₃
  ≈ᴹ-trans (≈ᴹ-bc x) (≈ᴹ-bc x₁) = ≈-trans x (≈ᴹ-bc x₁)
  ≈ᴹ-trans (≈ᴹ-bc x) (≈-trans x₁ s₂) = ≈-trans x (≈-trans x₁ s₂)
  ≈ᴹ-trans (≈-trans x s₁) (≈ᴹ-bc x₁) = ≈-trans x (≈ᴹ-trans s₁ (≈ᴹ-bc x₁))
  ≈ᴹ-trans (≈-trans x s₁) (≈-trans x₁ s₂) = ≈-trans x (≈ᴹ-trans s₁ (≈-trans x₁ s₂))

proj₁-wk-mval : {𝐖 𝐕 : M.MVal (X₁ `× X₂)} → WkMVal 𝐖 𝐕 → WkMVal (M.proj₁-val 𝐖) (M.proj₁-val 𝐕)
proj₁-wk-mval (wk-pairᵛ wm₁ wm₂) = wm₁

proj₂-wk-mval : {𝐖 𝐕 : M.MVal (X₁ `× X₂)} → WkMVal 𝐖 𝐕 → WkMVal (M.proj₂-val 𝐖) (M.proj₂-val 𝐕)
proj₂-wk-mval (wk-pairᵛ wm₁ wm₂) = wm₂

jump-wk : {Γ₁ Γ₂ : Ctx} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} {π : Wk Γ₁ Γ₂} → (i : Γ₂ ∋ `ℓ) → (WkMEnvᴹ π γ₁ γ₂) → M.eval-jump (var (wk-mem π i)) γ₁ ≈ᴹ M.eval-jump (var i) γ₂
jump-wk here (wk-menv-cong (wk-jumpᵛ π x x₁ x₂) ϖ) = ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp π x x₁ x₂))
jump-wk here (wk-menv-wk 𝐖 ϖ) = jump-wk here ϖ
jump-wk (there i) (wk-menv-cong x ϖ) = jump-wk i ϖ
jump-wk (there i) (wk-menv-wk 𝐖 ϖ) = jump-wk (there i) ϖ

eval-mem-wk : {Γ₁ Γ₂ : Ctx} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} {π : Wk Γ₁ Γ₂} → (i : Γ₂ ∋ X) → (WkMEnvᴹ π γ₁ γ₂) → WkMVal (M.eval (var (wk-mem π i)) γ₁) (M.eval (var i) γ₂)
eval-mem-wk here (wk-menv-cong x ϖ) = x
eval-mem-wk here (wk-menv-wk 𝐖 ϖ) = eval-mem-wk here ϖ
eval-mem-wk (there i) (wk-menv-cong x ϖ) = eval-mem-wk i ϖ
eval-mem-wk (there i) (wk-menv-wk 𝐖 ϖ) = eval-mem-wk (there i) ϖ

eval-val-wk : {Γ₁ Γ₂ : Ctx} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} {π : Wk Γ₁ Γ₂} → (W : Val Γ₂ X) → (WkMEnvᴹ π γ₁ γ₂) → WkMVal (M.eval (wk-val π W) γ₁) (M.eval W γ₂)
eval-val-wk (var i) (wk-menv-cong x ϖ) = eval-mem-wk i (wk-menv-cong x ϖ)
eval-val-wk (var i) (wk-menv-wk 𝐖 ϖ) = eval-mem-wk i ϖ
eval-val-wk (lam M) wk-menv-ε = wk-cloᵛ wk-ε refl wk-menv-ε
eval-val-wk (lam M) (wk-menv-cong x₁ ϖ) = wk-cloᵛ (wk-cong _) refl (wk-menv-cong x₁ ϖ)
eval-val-wk (lam M) (wk-menv-wk 𝐖 ϖ) = wk-cloᵛ (wk-wk _) refl (wk-menv-wk 𝐖 ϖ)
eval-val-wk (pair W₁ W₂) wk-menv-ε = wk-pairᵛ (eval-val-wk W₁ wk-menv-ε) (eval-val-wk W₂ wk-menv-ε)
eval-val-wk (pair W₁ W₂) (wk-menv-cong x ϖ) = wk-pairᵛ (eval-val-wk W₁ (wk-menv-cong x ϖ)) (eval-val-wk W₂ (wk-menv-cong x ϖ))
eval-val-wk (pair W₁ W₂) (wk-menv-wk 𝐖 ϖ) = wk-pairᵛ (eval-val-wk W₁ (wk-menv-wk 𝐖 ϖ)) (eval-val-wk W₂ (wk-menv-wk 𝐖 ϖ))
eval-val-wk unit wk-menv-ε = wk-unitᵛ
eval-val-wk unit (wk-menv-cong x ϖ) = wk-unitᵛ
eval-val-wk unit (wk-menv-wk 𝐖 ϖ) = wk-unitᵛ

eval₁-mem-wk : {Γ₁ Γ₂ : Ctx} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} {π : Wk Γ₁ Γ₂} → (i : Γ₂ ∋ (X₁ `× X₂)) → (WkMEnvᴹ π γ₁ γ₂) → WkMVal (M.eval₁ (var (wk-mem π i)) γ₁) (M.eval₁ (var i) γ₂)
eval₁-mem-wk here (wk-menv-cong x ϖ) = proj₁-wk-mval x
eval₁-mem-wk here (wk-menv-wk 𝐖 ϖ) = eval₁-mem-wk here ϖ
eval₁-mem-wk (there i) (wk-menv-cong x ϖ) = eval₁-mem-wk i ϖ
eval₁-mem-wk (there i) (wk-menv-wk 𝐖 ϖ) = eval₁-mem-wk (there i) ϖ

eval₁-val-wk : {Γ₁ Γ₂ : Ctx} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} {π : Wk Γ₁ Γ₂} → (W : Val Γ₂ (X₁ `× X₂)) → (WkMEnvᴹ π γ₁ γ₂) → WkMVal (M.eval₁ (wk-val π W) γ₁) (M.eval₁ W γ₂)
eval₁-val-wk (var i) (wk-menv-cong x ϖ) = eval₁-mem-wk i (wk-menv-cong x ϖ)
eval₁-val-wk (var i) (wk-menv-wk 𝐖 ϖ) = eval₁-mem-wk i ϖ
eval₁-val-wk (pair W₁ W₂) wk-menv-ε = wk-mval-id
eval₁-val-wk {γ₁ = γ₁ · 𝐖₁} {γ₂ = γ₂ · 𝐖₂} {π = wk-cong π} (pair W₁ W₂) (wk-menv-cong x ϖ) =
  let
    goal : WkMVal (M.eval (wk-val (Wk.wk-cong π) W₁) (γ₁ · 𝐖₁)) (M.eval W₁ (γ₂ · 𝐖₂))
    goal = eval-val-wk W₁ (wk-menv-cong x ϖ)
  in
  goal
eval₁-val-wk (pair W₁ W₂) (wk-menv-wk 𝐖 ϖ) = eval-val-wk W₁ (wk-menv-wk 𝐖 ϖ)

eval₂-mem-wk : {Γ₁ Γ₂ : Ctx} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} {π : Wk Γ₁ Γ₂} → (i : Γ₂ ∋ (X₁ `× X₂)) → (WkMEnvᴹ π γ₁ γ₂) → WkMVal (M.eval₂ (var (wk-mem π i)) γ₁) (M.eval₂ (var i) γ₂)
eval₂-mem-wk here (wk-menv-cong x ϖ) = proj₂-wk-mval x
eval₂-mem-wk here (wk-menv-wk 𝐖 ϖ) = eval₂-mem-wk here ϖ
eval₂-mem-wk (there i) (wk-menv-cong x ϖ) = eval₂-mem-wk i ϖ
eval₂-mem-wk (there i) (wk-menv-wk 𝐖 ϖ) = eval₂-mem-wk (there i) ϖ

eval₂-val-wk : {Γ₁ Γ₂ : Ctx} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} {π : Wk Γ₁ Γ₂} → (W : Val Γ₂ (X₁ `× X₂)) → (WkMEnvᴹ π γ₁ γ₂) → WkMVal (M.eval₂ (wk-val π W) γ₁) (M.eval₂ W γ₂)
eval₂-val-wk (var i) (wk-menv-cong x ϖ) = eval₂-mem-wk i (wk-menv-cong x ϖ)
eval₂-val-wk (var i) (wk-menv-wk 𝐖 ϖ) = eval₂-mem-wk i ϖ
eval₂-val-wk (pair W₁ W₂) wk-menv-ε = wk-mval-id
eval₂-val-wk (pair W₁ W₂) (wk-menv-cong x ϖ) = eval-val-wk W₂ (wk-menv-cong x ϖ)
eval₂-val-wk (pair W₁ W₂) (wk-menv-wk 𝐖 ϖ) = eval-val-wk W₂ (wk-menv-wk 𝐖 ϖ)

clo-to-comp-wk-proj₁ : {𝐖₁ 𝐖₂ : M.MVal (X `⇒ Y)} → WkMVal 𝐖₁ 𝐖₂ → Wk (proj₁ (M.clo-to-comp 𝐖₁)) (proj₁ (M.clo-to-comp 𝐖₂))
clo-to-comp-wk-proj₁ (wk-cloᵛ π x x₁) = π

clo-to-comp-wk-mem-cong : {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} → (i : Γ₂ ∋ (X `⇒ Y)) → (ϖ : WkMEnvᴹ π γ₁ γ₂) → Wk (proj₁ (M.clo-to-comp (M.eval (var (wk-mem π i)) γ₁))) (proj₁ (M.clo-to-comp (M.eval (var i) γ₂)))
clo-to-comp-wk-mem-cong {π = wk-ε} {γ₁ = ⋄} {γ₂ = ⋄} () ϖ
clo-to-comp-wk-mem-cong {π = wk-cong π} {γ₁ = γ₁ · 𝐖₁} {γ₂ = γ₂ · 𝐖₂} here (wk-menv-cong x₂ ϖ) = clo-to-comp-wk-proj₁ x₂
clo-to-comp-wk-mem-cong {π = wk-cong π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} (there i) (wk-menv-cong x₂ ϖ) = clo-to-comp-wk-mem-cong i ϖ
clo-to-comp-wk-mem-cong {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = ⋄} () ϖ
clo-to-comp-wk-mem-cong {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} here (wk-menv-wk 𝐖 ϖ) = clo-to-comp-wk-mem-cong here ϖ
clo-to-comp-wk-mem-cong {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} (there i) (wk-menv-wk 𝐖 ϖ) = clo-to-comp-wk-mem-cong (there i) ϖ

clo-to-comp-wk-cong : {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} → (W : Val Γ₂ (X `⇒ Y)) → (ϖ : WkMEnvᴹ π γ₁ γ₂) → Wk (proj₁ (M.clo-to-comp (M.eval (wk-val π W) γ₁))) (proj₁ (M.clo-to-comp (M.eval W γ₂)))
clo-to-comp-wk-cong {π = wk-cong π} (var i) (wk-menv-cong x ϖ) = clo-to-comp-wk-mem-cong i (wk-menv-cong x ϖ)
clo-to-comp-wk-cong {π = wk-wk π} (var i) (wk-menv-wk 𝐖 ϖ) = clo-to-comp-wk-mem-cong i ϖ
clo-to-comp-wk-cong {π = wk-ε} (lam M) wk-menv-ε = Wk.wk-ε
clo-to-comp-wk-cong {π = wk-cong π} (lam M) (wk-menv-cong x₁ ϖ) = Wk.wk-cong π
clo-to-comp-wk-cong {π = wk-wk π} (lam M) (wk-menv-wk 𝐖 ϖ) = Wk.wk-wk π

clo-to-comp-wk-proj₁-proj₂ : {𝐖₁ 𝐖₂ : M.MVal (X `⇒ Y)} → (w : WkMVal 𝐖₁ 𝐖₂) → proj₁ (proj₂ (M.clo-to-comp 𝐖₁)) ≡ wk-comp (Wk.wk-cong (clo-to-comp-wk-proj₁ w)) (proj₁ (proj₂ (M.clo-to-comp 𝐖₂)))
clo-to-comp-wk-proj₁-proj₂ (wk-cloᵛ π x x₁) = x

clo-to-comp-wk-proj₂-proj₂ : {𝐖₁ 𝐖₂ : M.MVal (X `⇒ Y)} → (w : WkMVal 𝐖₁ 𝐖₂) → WkMEnvᴹ (clo-to-comp-wk-proj₁ w) (proj₂ (proj₂ (M.clo-to-comp 𝐖₁))) (proj₂ (proj₂ (M.clo-to-comp 𝐖₂)))
clo-to-comp-wk-proj₂-proj₂ (wk-cloᵛ π x x₁) = x₁

cc-wk-eq : {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} {𝐖 : M.MVal Z} → (i : Γ₂ ∋ (X `⇒ Y)) → (ϖ : WkMEnvᴹ π γ₁ γ₂) → clo-to-comp-wk-mem-cong i ϖ ≡ clo-to-comp-wk-mem-cong i (wk-menv-wk 𝐖 ϖ)
cc-wk-eq {π = wk-ε} {γ₁ = ⋄} {γ₂ = ⋄} () ϖ
cc-wk-eq {π = wk-cong π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} here (wk-menv-cong x₂ ϖ) = refl
cc-wk-eq {π = wk-cong π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} (there i) (wk-menv-cong x₂ ϖ) = refl
cc-wk-eq {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = ⋄} () ϖ
cc-wk-eq {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} here (wk-menv-wk 𝐖 ϖ) = refl
cc-wk-eq {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} (there i) (wk-menv-wk 𝐖 ϖ) = refl

cc-eq-eq : {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} → (i : Γ₂ ∋ (X `⇒ Y)) → (ϖ : WkMEnvᴹ π γ₁ γ₂) → clo-to-comp-wk-cong (var i) ϖ ≡ clo-to-comp-wk-mem-cong i ϖ
cc-eq-eq here (wk-menv-cong x ϖ) = refl
cc-eq-eq here (wk-menv-wk 𝐖 ϖ) = cc-wk-eq {𝐖 = 𝐖} here ϖ
cc-eq-eq (there i) (wk-menv-cong x ϖ) = refl
cc-eq-eq (there i) (wk-menv-wk 𝐖 ϖ) = cc-wk-eq {𝐖 = 𝐖} (there i) ϖ

clo-to-comp-wk-mem-eq : {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} → (i : Γ₂ ∋ (X `⇒ Y)) → (ϖ : WkMEnvᴹ π γ₁ γ₂) → proj₁ (proj₂ (M.clo-to-comp (M.eval (var (wk-mem π i)) γ₁))) ≡ wk-comp (wk-cong (clo-to-comp-wk-cong (var i) ϖ)) (proj₁ (proj₂ (M.clo-to-comp (M.eval (var i) γ₂))))
clo-to-comp-wk-mem-eq {π = wk-ε} {γ₁ = ⋄} {γ₂ = ⋄} () ϖ
clo-to-comp-wk-mem-eq {π = wk-cong π} {γ₁ = γ₁ · 𝐖₁} {γ₂ = γ₂ · 𝐖₂} here (wk-menv-cong w ϖ) = clo-to-comp-wk-proj₁-proj₂ w
clo-to-comp-wk-mem-eq {π = wk-cong π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} (there i) (wk-menv-cong x₂ ϖ) =
  let
    a0 : proj₁ (proj₂ (M.clo-to-comp (M.lookup (wk-mem π i) γ₁))) ≡ wk-comp (wk-cong (clo-to-comp-wk-cong (var i) ϖ)) (proj₁ (proj₂ (M.clo-to-comp (M.lookup i γ₂))))
    a0 = clo-to-comp-wk-mem-eq i ϖ

    goal : proj₁ (proj₂ (M.clo-to-comp (M.lookup (wk-mem π i) γ₁))) ≡ wk-comp (wk-cong (clo-to-comp-wk-mem-cong i ϖ)) (proj₁ (proj₂ (M.clo-to-comp (M.lookup i γ₂))))
    goal = subst (λ z → proj₁ (proj₂ (M.clo-to-comp (M.lookup (wk-mem π i) γ₁))) ≡ wk-comp (wk-cong z) (proj₁ (proj₂ (M.clo-to-comp (M.lookup i γ₂))))) (cc-eq-eq i ϖ) a0
  in
  goal
clo-to-comp-wk-mem-eq {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = ⋄} () ϖ
clo-to-comp-wk-mem-eq {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} here (wk-menv-wk 𝐖 ϖ) =
  let
    a0 : proj₁ (proj₂ (M.clo-to-comp (M.lookup (wk-mem π here) γ₁))) ≡ wk-comp (wk-cong (clo-to-comp-wk-cong (var here) ϖ)) (proj₁ (proj₂ (M.clo-to-comp x₁)))
    a0 = clo-to-comp-wk-mem-eq here ϖ

    goal : proj₁ (proj₂ (M.clo-to-comp (M.lookup (wk-mem π here) γ₁))) ≡ wk-comp (wk-cong (clo-to-comp-wk-mem-cong here ϖ)) (proj₁ (proj₂ (M.clo-to-comp x₁)))
    goal = subst (λ z → proj₁ (proj₂ (M.clo-to-comp (M.lookup (wk-mem π here) γ₁))) ≡ wk-comp (wk-cong z) (proj₁ (proj₂ (M.clo-to-comp x₁)))) (cc-eq-eq here ϖ) a0
  in
  goal
clo-to-comp-wk-mem-eq {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} (there i) (wk-menv-wk 𝐖 ϖ) =
  let
    a0 : proj₁ (proj₂ (M.clo-to-comp (M.eval (var (wk-mem π (there i))) γ₁))) ≡ wk-comp (wk-cong (clo-to-comp-wk-cong (var (there i)) ϖ)) (proj₁ (proj₂ (M.clo-to-comp (M.lookup i γ₂))))
    a0 = clo-to-comp-wk-mem-eq (there i) ϖ

    goal : proj₁ (proj₂ (M.clo-to-comp (M.lookup (wk-mem π (_∋_.there i)) γ₁))) ≡ wk-comp (Wk.wk-cong (clo-to-comp-wk-mem-cong (_∋_.there i) ϖ)) (proj₁ (proj₂ (M.clo-to-comp (M.lookup i γ₂))))
    goal = subst (λ z → proj₁ (proj₂ (M.clo-to-comp (M.lookup (wk-mem π (_∋_.there i)) γ₁))) ≡ wk-comp (Wk.wk-cong z) (proj₁ (proj₂ (M.clo-to-comp (M.lookup i γ₂))))) (cc-eq-eq (there i) ϖ) a0
  in
  goal

clo-to-comp-wk-eq : {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} → (W : Val Γ₂ (X `⇒ Y)) → (ϖ : WkMEnvᴹ π γ₁ γ₂) → proj₁ (proj₂ (M.clo-to-comp (M.eval (wk-val π W) γ₁))) ≡ wk-comp (wk-cong (clo-to-comp-wk-cong W ϖ)) (proj₁ (proj₂ (M.clo-to-comp (M.eval W γ₂))))
clo-to-comp-wk-eq {π = wk-cong π} (var i) (wk-menv-cong x ϖ) = clo-to-comp-wk-mem-eq i (wk-menv-cong x ϖ)
clo-to-comp-wk-eq {π = wk-wk π} (var i) (wk-menv-wk 𝐖 ϖ) = clo-to-comp-wk-mem-eq i (wk-menv-wk 𝐖 ϖ)
clo-to-comp-wk-eq {π = wk-ε} (lam M) wk-menv-ε = refl
clo-to-comp-wk-eq {π = wk-cong π} (lam M) (wk-menv-cong x₁ ϖ) = refl
clo-to-comp-wk-eq {π = wk-wk π} (lam M) (wk-menv-wk 𝐖 ϖ) = refl

clo-to-comp-mem-wk-menv : {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} → (i : Γ₂ ∋ (X `⇒ Y)) → (ϖ : WkMEnvᴹ π γ₁ γ₂) → WkMEnvᴹ (clo-to-comp-wk-cong (var i) ϖ) (proj₂ (proj₂ (M.clo-to-comp (M.eval (var (wk-mem π i)) γ₁)))) (proj₂ (proj₂ (M.clo-to-comp (M.eval (var i) γ₂))))
clo-to-comp-mem-wk-menv {π = wk-ε} {γ₁ = ⋄} {γ₂ = ⋄} () ϖ
clo-to-comp-mem-wk-menv {π = wk-cong π} {γ₁ = γ₁ · 𝐖₁} {γ₂ = γ₂ · 𝐖₂} here (wk-menv-cong w ϖ) =
  let
    goal : WkMEnvᴹ (clo-to-comp-wk-proj₁ w) (proj₂ (proj₂ (M.clo-to-comp 𝐖₁))) (proj₂ (proj₂ (M.clo-to-comp 𝐖₂)))
    goal = clo-to-comp-wk-proj₂-proj₂ w
  in
  goal
clo-to-comp-mem-wk-menv {π = wk-cong π} {γ₁ = γ₁ · 𝐖₁} {γ₂ = γ₂ · 𝐖₂} (there i) (wk-menv-cong x₂ ϖ) =
  let
    a0 : WkMEnvᴹ (clo-to-comp-wk-cong (var i) ϖ) (proj₂ (proj₂ (M.clo-to-comp (M.lookup (wk-mem π i) γ₁)))) (proj₂ (proj₂ (M.clo-to-comp (M.lookup i γ₂))))
    a0 = clo-to-comp-mem-wk-menv i ϖ

    goal : WkMEnvᴹ (clo-to-comp-wk-mem-cong i ϖ) (proj₂ (proj₂ (M.clo-to-comp (M.lookup (wk-mem π i) γ₁)))) (proj₂ (proj₂ (M.clo-to-comp (M.lookup i γ₂))))
    goal = subst (λ z → WkMEnvᴹ z (proj₂ (proj₂ (M.clo-to-comp (M.lookup (wk-mem π i) γ₁)))) (proj₂ (proj₂ (M.clo-to-comp (M.lookup i γ₂))))) (cc-eq-eq i ϖ) a0
  in
  goal
clo-to-comp-mem-wk-menv {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = ⋄} () ϖ
clo-to-comp-mem-wk-menv {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} here (wk-menv-wk 𝐖 ϖ) =
  let
    a0 : WkMEnvᴹ (clo-to-comp-wk-cong (var here) ϖ) (proj₂ (proj₂ (M.clo-to-comp (M.eval (var (wk-mem π here)) γ₁)))) (proj₂ (proj₂ (M.clo-to-comp (M.eval (var here) (γ₂ · x₁)))))
    a0 = clo-to-comp-mem-wk-menv here ϖ

    goal : WkMEnvᴹ (clo-to-comp-wk-mem-cong _∋_.here ϖ) (proj₂ (proj₂ (M.clo-to-comp (M.lookup (wk-mem π _∋_.here) γ₁)))) (proj₂ (proj₂ (M.clo-to-comp x₁)))
    goal = subst (λ z → WkMEnvᴹ z (proj₂ (proj₂ (M.clo-to-comp (M.eval (var (wk-mem π here)) γ₁)))) (proj₂ (proj₂ (M.clo-to-comp (M.eval (var here) (γ₂ · x₁)))))) (cc-eq-eq _∋_.here ϖ) a0
  in
  goal
clo-to-comp-mem-wk-menv {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} (there i) (wk-menv-wk 𝐖 ϖ) =
  let
    a0 : WkMEnvᴹ (clo-to-comp-wk-cong (var (there i)) ϖ) (proj₂ (proj₂ (M.clo-to-comp (M.eval (var (wk-mem π (there i))) γ₁)))) (proj₂ (proj₂ (M.clo-to-comp (M.eval (var (there i)) (γ₂ · x₁)))))
    a0 = clo-to-comp-mem-wk-menv (there i) ϖ

    goal : WkMEnvᴹ (clo-to-comp-wk-mem-cong (_∋_.there i) ϖ) (proj₂ (proj₂ (M.clo-to-comp (M.lookup (wk-mem π (_∋_.there i)) γ₁)))) (proj₂ (proj₂ (M.clo-to-comp (M.lookup i γ₂))))
    goal = subst (λ z → WkMEnvᴹ z (proj₂ (proj₂ (M.clo-to-comp (M.eval (var (wk-mem π (there i))) γ₁)))) (proj₂ (proj₂ (M.clo-to-comp (M.eval (var (there i)) (γ₂ · x₁)))))) (cc-eq-eq (there i) ϖ) a0
  in
  goal

clo-to-comp-wk-menv : {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} → (W : Val Γ₂ (X `⇒ Y)) → (ϖ : WkMEnvᴹ π γ₁ γ₂) → WkMEnvᴹ (clo-to-comp-wk-cong W ϖ) (proj₂ (proj₂ (M.clo-to-comp (M.eval (wk-val π W) γ₁)))) (proj₂ (proj₂ (M.clo-to-comp (M.eval W γ₂))))
clo-to-comp-wk-menv (var i) (wk-menv-cong x ϖ) = clo-to-comp-mem-wk-menv i (wk-menv-cong x ϖ)
clo-to-comp-wk-menv (var i) (wk-menv-wk 𝐖 ϖ) = clo-to-comp-mem-wk-menv i (wk-menv-wk 𝐖 ϖ)
clo-to-comp-wk-menv (lam M) wk-menv-ε = wk-menv-ε
clo-to-comp-wk-menv (lam M) (wk-menv-cong x₁ ϖ) = wk-menv-cong x₁ ϖ
clo-to-comp-wk-menv (lam M) (wk-menv-wk 𝐖 ϖ) = wk-menv-wk 𝐖 ϖ

mstep-eqv₁ : {σ₁₁ σ₂₁ σ₁₂ : M.CState} → (WkCStateᴹ σ₁₂ σ₁₁) → (σ₁₁ →ᴹ σ₂₁) → Σ[ σ₂₂ ∈ M.CState ] ((σ₁₂ →ᴹ σ₂₂) × σ₂₁ ≈ᴹ σ₂₂)
mstep-eqv₁ (wk-cstate-result {K₁ = < x₂ ； γ >∷ K₁} x (wk-cstack-push π x₁ x₃ x₄)) return→ = _ , return→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp (wk-cong π) x₁ (wk-menv-cong x x₃) x₄))
mstep-eqv₁ (wk-cstate-comp {M₁ = return W} {M₂ = return W₂} π refl x₁ x₂) eval→ = _ , eval→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-result (eval-val-wk W₂ x₁) x₂))
mstep-eqv₁ (wk-cstate-comp {M₁ = push M₁ M₂} π refl x₁ x₂) push→ = _ , push→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp π refl x₁ (wk-cstack-push π refl x₁ x₂)))
mstep-eqv₁ (wk-cstate-comp {M₁ = sub M₁ M₂} π refl x₁ x₂) sub→ = _ , sub→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp (Wk.wk-cong π) refl (wk-menv-cong (wk-jumpᵛ π refl x₁ x₂) x₁) x₂))
mstep-eqv₁ (wk-cstate-comp {M₁ = var (var i₁)} {M₂ = var (var i)} π refl x₁ x₂) var→ = _ , var→ , ≈ᴹ-sym (jump-wk i x₁)
mstep-eqv₁ (wk-cstate-comp {M₁ = pm x₃ M₁} {M₂ = pm W₂ M₂} π refl x₁ x₂) pmᶜ→ = _ , pmᶜ→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp (Wk.wk-cong (Wk.wk-cong π)) refl (wk-menv-cong (eval₂-val-wk W₂ x₁) (wk-menv-cong (eval₁-val-wk W₂ x₁) x₁)) x₂))
mstep-eqv₁ (wk-cstate-comp {M₁ = app x₃ x₄} {M₂ = app x₅ x₆} π refl x₁ x₂) app→ = _ , app→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp (wk-cong (clo-to-comp-wk-cong x₅ x₁)) (clo-to-comp-wk-eq x₅ x₁) (wk-menv-cong (eval-val-wk x₆ x₁) (clo-to-comp-wk-menv x₅ x₁)) x₂))

mstep-eqv₂ : {σ₁₁ σ₂₁ σ₁₂ : M.CState} → (WkCStateᴹ σ₁₁ σ₁₂) → (σ₁₁ →ᴹ σ₂₁) → Σ[ σ₂₂ ∈ M.CState ] ((σ₁₂ →ᴹ σ₂₂) × σ₂₁ ≈ᴹ σ₂₂)
mstep-eqv₂ (wk-cstate-result {K₂ = < x₂ ； γ >∷ K₂} x (wk-cstack-push π x₁ x₃ x₄)) return→ = _ , return→ , ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp (wk-cong π) x₁ (wk-menv-cong x x₃) x₄))
mstep-eqv₂ (wk-cstate-comp {M₂ = return W} π refl x₁ x₂) eval→ = _ , eval→ , ≈ᴹ-bc (≈-wk₂ (wk-cstate-result (eval-val-wk W x₁) x₂))
mstep-eqv₂ (wk-cstate-comp {M₂ = push M₂ M₃} π refl x₁ x₂) push→ = _ , push→ , ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp π refl x₁ (wk-cstack-push π refl x₁ x₂)))
mstep-eqv₂ (wk-cstate-comp {M₂ = sub M₂ M₃} π refl x₁ x₂) sub→ = _ , sub→ , ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp (wk-cong π) refl (wk-menv-cong (wk-jumpᵛ π refl x₁ x₂) x₁) x₂))
mstep-eqv₂ (wk-cstate-comp {M₂ = var (var i)} π refl x₁ x₂) var→ = _ , var→ , jump-wk i x₁
mstep-eqv₂ (wk-cstate-comp {M₂ = pm W M₂} {γ₁ = γ₁} {γ₂ = γ₂} π refl x₁ x₂) pmᶜ→ = _ , pmᶜ→ , ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp (Wk.wk-cong (Wk.wk-cong π)) refl (wk-menv-cong (eval₂-val-wk W x₁) (wk-menv-cong (eval₁-val-wk W x₁) x₁)) x₂))
mstep-eqv₂ (wk-cstate-comp {M₂ = app W₁ W₂} π refl ϖ x) app→ = _ , app→ , ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp (wk-cong (clo-to-comp-wk-cong W₁ ϖ)) (clo-to-comp-wk-eq W₁ ϖ) (wk-menv-cong (eval-val-wk W₂ ϖ) (clo-to-comp-wk-menv W₁ ϖ)) x))

mstep-eqv' : {σ₁₁ σ₂₁ σ₁₂ : M.CState} → (σ₁₁ ≈₀ᴹ σ₁₂) → (σ₁₁ →ᴹ σ₂₁) → Σ[ σ₂₂ ∈ M.CState ] ((σ₁₂ →ᴹ σ₂₂) × σ₂₁ ≈ᴹ σ₂₂)
mstep-eqv' (≈-wk₁ w) σ→σ' = mstep-eqv₁ w σ→σ'
mstep-eqv' (≈-wk₂ w) σ→σ' = mstep-eqv₂ w σ→σ'

mstep-eqv : {σ₁₁ σ₂₁ σ₁₂ : M.CState} → (σ₁₁ ≈ᴹ σ₁₂) → (σ₁₁ →ᴹ σ₂₁) → Σ[ σ₂₂ ∈ M.CState ] ((σ₁₂ →ᴹ σ₂₂) × σ₂₁ ≈ᴹ σ₂₂)
mstep-eqv (≈ᴹ-bc (≈-wk₁ w)) σ→σ' = mstep-eqv₁ w σ→σ'
mstep-eqv (≈ᴹ-bc (≈-wk₂ w)) σ→σ' = mstep-eqv₂ w σ→σ'
mstep-eqv (≈-trans eqv₁ eqv₂) σ→σ' =
  let
    IH₁ = mstep-eqv' eqv₁ σ→σ'
    eqvIH₁ = proj₂ (proj₂ IH₁)
    σ→σIH₁ = proj₁ (proj₂ IH₁)
    IH₂ = mstep-eqv eqv₂ σ→σIH₁
    eqvIH₂ = proj₂ (proj₂ IH₂)
  in
  proj₁ IH₂ , proj₁ (proj₂ IH₂) , ≈ᴹ-trans eqvIH₁ eqvIH₂

---------------------------------------------------------------------------------
-- Properties of Inception.Sub.TelescopeMachine
---------------------------------------------------------------------------------

-- Weakening of Telescopes
data WkMEnvᵀ : {Γ₁ Γ₂ : Ctx} → (π : Wk Γ₁ Γ₂) → (γ₁ : TM.MEnv Γ₁) → (γ₂ : TM.MEnv Γ₂) → Set where

    wk-tmenv-ε    : WkMEnvᵀ wk-ε TM.⋄ TM.⋄

    wk-tmenv-mclo-cong : {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {γ₁ : TM.MEnv Γ₁} {γ₂ : TM.MEnv Γ₂} → (𝐖 : TM.MClo Γ₂ X) → WkMEnvᵀ π γ₁ γ₂ → WkMEnvᵀ (wk-cong π) (γ₁ · TM.wk-mclo π 𝐖) (γ₂ · 𝐖)

    wk-tmenv-jump-cong : {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {γ₁ : TM.MEnv Γ₁} {γ₂ : TM.MEnv Γ₂}
                         → (M : Comp Γ₂ X) → (πᵀ : Wk Γ₂ Δ) → (K : TM.CStack Δ X) → WkMEnvᵀ π γ₁ γ₂
                         → WkMEnvᵀ (wk-cong π) (γ₁ TM.·﹝ wk-comp π M ╎ wk-trans π πᵀ ╎ K ﹞) (γ₂ TM.·﹝ M ╎ πᵀ ╎ K ﹞)

    wk-tmenv-mclo-wk : {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {γ₁ : TM.MEnv Γ₁} {γ₂ : TM.MEnv Γ₂} → (𝐖 : TM.MClo Γ₁ X) → WkMEnvᵀ π γ₁ γ₂ → WkMEnvᵀ (wk-wk π) (γ₁ · 𝐖) γ₂

    wk-tmenv-jump-wk :   {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {γ₁ : TM.MEnv Γ₁} {γ₂ : TM.MEnv Γ₂}
                         → (M : Comp Γ₁ X) → (πᵀ : Wk Γ₁ Δ) → (K : TM.CStack Δ X) → WkMEnvᵀ π γ₁ γ₂
                         → WkMEnvᵀ (wk-wk π) (γ₁ TM.·﹝ M ╎ πᵀ ╎ K ﹞) γ₂

-- Well-formedness of states
mutual

  data WellFormedTMCStack : TM.CStack Γ X → Set where

      ◻ : WellFormedTMCStack {Γ = ε} {X = ℛ} TM.◻

      wf-bottom : (M : (Γ ∙ Y) ⊢ᶜ ℛ) → (γ : TM.MEnv Γ) → (π : Wk Γ ε)
                  → WellFormedTMEnv γ
                  ------------------------------------
                  → WellFormedTMCStack (TM.< M ； γ ； π >∷ TM.◻)

      wf-next :  {Γ₁ Γ₂ Γ₃ : Ctx} → (M₁ : (Γ₁ ∙ Z) ⊢ᶜ Y) → {γ₁ : TM.MEnv Γ₁} → (M₂ : (Γ₂ ∙ Y) ⊢ᶜ X) → {γ₂ : TM.MEnv Γ₂}
                  → {π₁ : Wk Γ₁ Γ₂} → {π₂ : Wk Γ₂ Γ₃} → WkMEnvᵀ π₁ γ₁ γ₂
                  → {K : TM.CStack Γ₃ X} → WellFormedTMCStack (TM.< M₂ ； γ₂ ； π₂ >∷ K)
                  → WellFormedTMEnv γ₁
                  ------------------------------------
                  → WellFormedTMCStack (TM.< M₁ ； γ₁ ； π₁ >∷ TM.< M₂ ； γ₂ ； π₂ >∷ K)

  data WellFormedTMClo : TM.MEnv Γ → TM.MClo Γ X → Set where

      wf-mclo-unit : {γ : TM.MEnv Γ} → WellFormedTMClo γ TM.unit

      wf-mclo-lam : {γ : TM.MEnv Γ} {M : Comp (Γ ∙ X) Y} → WellFormedTMClo γ (TM.lam M)

      wf-mclo-pair : {γ : TM.MEnv Γ} {𝐖₁ : TM.MClo Γ X₁} {𝐖₂ : TM.MClo Γ X₂} → WellFormedTMClo γ 𝐖₁ → WellFormedTMClo γ 𝐖₂ → WellFormedTMClo γ (TM.pair 𝐖₁ 𝐖₂)

      wf-mclo-label-h : {γ : TM.MEnv Γ} {M : Comp Γ X} {π : Wk Γ Γ₁} {K : TM.CStack Γ₁ X} → WellFormedTMClo (γ TM.·﹝ M ╎ π ╎ K ﹞) (TM.label here)

      wf-mclo-label-t-mclo : {γ : TM.MEnv Γ} {i : Γ ∋ `ℓ} {𝐖 : TM.MClo Γ X} → WellFormedTMClo γ (TM.label i) → WellFormedTMClo (γ · 𝐖) (TM.label (there i))

      wf-mclo-label-t-jump : {γ : TM.MEnv Γ} {i : Γ ∋ `ℓ} {M : Comp Γ X} {π : Wk Γ Γ₁} {K : TM.CStack Γ₁ X} → WellFormedTMClo γ (TM.label i) → WellFormedTMClo (γ TM.·﹝ M ╎ π ╎ K ﹞) (TM.label (there i))

  data WellFormedTMEnv : TM.MEnv Γ → Set where

      wf-env-empty : WellFormedTMEnv TM.⋄

      wf-env-mclo : {γ : TM.MEnv Γ} {𝐖 : TM.MClo Γ X} → WellFormedTMEnv γ → WellFormedTMClo γ 𝐖 → WellFormedTMEnv (γ · 𝐖)

      wf-env-jump : {γ : TM.MEnv Γ} {M : Comp Γ X} {π : Wk Γ Γ₁} {K : TM.CStack Γ₁ X}
                    → WellFormedTMCState TM.⟨ M ╎ γ ╎ π ╎ K ⟩
                    → WellFormedTMEnv (γ TM.·﹝ M ╎ π ╎ K ﹞)

  data WellFormedTMCState : TM.CState → Set where

      wf-state-halt : (𝐖 : TM.MClo Γ ℛ) → (γ : TM.MEnv Γ) → (π : Wk Γ ε)
                  → WellFormedTMEnv γ
                  → WellFormedTMClo γ 𝐖
                  ------------------------------------
                  → WellFormedTMCState TM.⟨ 𝐖 ； γ ╎ π ╎ TM.◻ ⟩

      wf-state-result : {Γ₁ Γ₂ Γ₃ : Ctx} {γ₁ : TM.MEnv Γ₁}
                  {γ₂ : TM.MEnv Γ₂} {π₁ : Wk Γ₁ Γ₂} → {π₂ : Wk Γ₂ Γ₃}
                  {M : Comp (Γ₂ ∙ X) Y} {K : TM.CStack Γ₃ Y}
                  → (𝐖 : TM.MClo Γ₁ X)
                  → WkMEnvᵀ π₁ γ₁ γ₂
                  → WellFormedTMCStack (TM.< M ； γ₂ ； π₂ >∷ K)
                  → WellFormedTMEnv γ₁
                  → WellFormedTMClo γ₁ 𝐖
                  ------------------------------------
                  → WellFormedTMCState TM.⟨ 𝐖 ； γ₁ ╎ π₁ ╎ TM.< M ； γ₂ ； π₂ >∷ K ⟩

      wf-state-bottom : (M : Comp Γ ℛ) → (γ : TM.MEnv Γ) → (π : Wk Γ ε)
                  → WellFormedTMEnv γ
                  ------------------------------------
                  → WellFormedTMCState TM.⟨ M ╎ γ ╎ π ╎ TM.◻ ⟩

      wf-state-resume : {Γ₁ Γ₂ Γ₃ : Ctx} {γ₁ : TM.MEnv Γ₁}
                  {γ₂ : TM.MEnv Γ₂} {π₁ : Wk Γ₁ Γ₂} → {π₂ : Wk Γ₂ Γ₃}
                  {M₂ : Comp (Γ₂ ∙ X) Y} {K : TM.CStack Γ₃ Y}
                  → (M₁ : Comp Γ₁ X)
                  → WkMEnvᵀ π₁ γ₁ γ₂
                  → WellFormedTMCStack (TM.< M₂ ； γ₂ ； π₂ >∷ K)
                  → WellFormedTMEnv γ₁
                  ------------------------------------
                  → WellFormedTMCState TM.⟨ M₁ ╎ γ₁ ╎ π₁ ╎ TM.< M₂ ； γ₂ ； π₂ >∷ K ⟩

wk-MEnvᵀ-trans : {Γ₁ Γ₂ Γ₃ : Ctx} {π₁ : Wk Γ₁ Γ₂} {π₂ : Wk Γ₂ Γ₃} {γ₁ : TM.MEnv Γ₁} {γ₂ : TM.MEnv Γ₂} {γ₃ : TM.MEnv Γ₃} → WkMEnvᵀ π₁ γ₁ γ₂ → WkMEnvᵀ π₂ γ₂ γ₃ → WkMEnvᵀ (wk-trans π₁ π₂) γ₁ γ₃
wk-MEnvᵀ-trans wk-tmenv-ε wk-tmenv-ε = wk-tmenv-ε
wk-MEnvᵀ-trans {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {γ₁ = γ₁ · _} {γ₂ = γ₂ · _} {γ₃ = γ₃ · _} (wk-tmenv-mclo-cong 𝐖 ϖ₁) (wk-tmenv-mclo-cong 𝐖₁ ϖ₂) =
  let
    a0 = wk-MEnvᵀ-trans ϖ₁ ϖ₂
    a1 : WkMEnvᵀ (wk-cong (wk-trans π₁ π₂)) (γ₁ · TM.wk-mclo (wk-trans π₁ π₂) 𝐖₁) (γ₃ · 𝐖₁)
    a1 = wk-tmenv-mclo-cong 𝐖₁ a0
    a2 : WkMEnvᵀ (wk-trans (Wk.wk-cong π₁) (Wk.wk-cong π₂)) (γ₁ · TM.wk-mclo (wk-trans π₁ π₂) 𝐖₁) (γ₃ · 𝐖₁)
    a2 = subst (λ x → WkMEnvᵀ x (γ₁ · TM.wk-mclo (wk-trans π₁ π₂) 𝐖₁) (γ₃ · 𝐖₁)) (wk-trans-idr-β (Wk.wk-cong (wk-trans π₁ π₂))) a1
    a3 : WkMEnvᵀ (wk-trans (Wk.wk-cong π₁) (Wk.wk-cong π₂)) (γ₁ · TM.wk-mclo π₁ (TM.wk-mclo π₂ 𝐖₁)) (γ₃ · 𝐖₁)
    a3 = subst (λ x → WkMEnvᵀ (wk-trans (Wk.wk-cong π₁) (Wk.wk-cong π₂)) (γ₁ · x) (γ₃ · 𝐖₁)) (sym (wk-mclo-wk-η 𝐖₁ π₁ π₂)) a2
  in
  a3
wk-MEnvᵀ-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} (wk-tmenv-mclo-cong 𝐖 ϖ₁) (wk-tmenv-mclo-wk 𝐖₁ ϖ₂) = wk-tmenv-mclo-wk (TM.wk-mclo π₁ 𝐖) (wk-MEnvᵀ-trans ϖ₁ ϖ₂)
wk-MEnvᵀ-trans {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} (wk-tmenv-jump-cong M πᵀ K ϖ₁) (wk-tmenv-jump-cong M₁ πᵀ₁ K₁ ϖ₂) = wk-tmenv-jump-cong M₁ πᵀ₁ K₁ (wk-MEnvᵀ-trans ϖ₁ ϖ₂)
wk-MEnvᵀ-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂}(wk-tmenv-jump-cong M πᵀ K ϖ₁) (wk-tmenv-jump-wk M₁ πᵀ₁ K₁ ϖ₂) = wk-tmenv-jump-wk (wk-comp π₁ M) (wk-trans π₁ πᵀ) K (wk-MEnvᵀ-trans ϖ₁ ϖ₂)
wk-MEnvᵀ-trans (wk-tmenv-mclo-wk 𝐖 ϖ₁) wk-tmenv-ε = wk-tmenv-mclo-wk 𝐖 ϖ₁
wk-MEnvᵀ-trans (wk-tmenv-mclo-wk 𝐖 ϖ₁) (wk-tmenv-mclo-cong 𝐖₁ ϖ₂) = wk-tmenv-mclo-wk 𝐖 (wk-MEnvᵀ-trans ϖ₁ (wk-tmenv-mclo-cong 𝐖₁ ϖ₂))
wk-MEnvᵀ-trans (wk-tmenv-mclo-wk 𝐖 ϖ₁) (wk-tmenv-jump-cong M πᵀ K ϖ₂) = wk-tmenv-mclo-wk 𝐖 (wk-MEnvᵀ-trans ϖ₁ (wk-tmenv-jump-cong M πᵀ K ϖ₂))
wk-MEnvᵀ-trans (wk-tmenv-mclo-wk 𝐖 ϖ₁) (wk-tmenv-mclo-wk 𝐖₁ ϖ₂) = wk-tmenv-mclo-wk 𝐖 (wk-MEnvᵀ-trans ϖ₁ (wk-tmenv-mclo-wk 𝐖₁ ϖ₂))
wk-MEnvᵀ-trans (wk-tmenv-mclo-wk 𝐖 ϖ₁) (wk-tmenv-jump-wk M πᵀ K ϖ₂) = wk-tmenv-mclo-wk 𝐖 (wk-MEnvᵀ-trans ϖ₁ (wk-tmenv-jump-wk M πᵀ K ϖ₂))
wk-MEnvᵀ-trans (wk-tmenv-jump-wk M πᵀ K ϖ₁) wk-tmenv-ε = wk-tmenv-jump-wk M πᵀ K ϖ₁
wk-MEnvᵀ-trans (wk-tmenv-jump-wk M πᵀ K ϖ₁) (wk-tmenv-mclo-cong 𝐖 ϖ₂) = wk-tmenv-jump-wk M πᵀ K (wk-MEnvᵀ-trans ϖ₁ (wk-tmenv-mclo-cong 𝐖 ϖ₂))
wk-MEnvᵀ-trans (wk-tmenv-jump-wk M πᵀ K ϖ₁) (wk-tmenv-jump-cong M₁ πᵀ₁ K₁ ϖ₂) = wk-tmenv-jump-wk M πᵀ K (wk-MEnvᵀ-trans ϖ₁ (wk-tmenv-jump-cong M₁ πᵀ₁ K₁ ϖ₂))
wk-MEnvᵀ-trans (wk-tmenv-jump-wk M πᵀ K ϖ₁) (wk-tmenv-mclo-wk 𝐖 ϖ₂) = wk-tmenv-jump-wk M πᵀ K (wk-MEnvᵀ-trans ϖ₁ (wk-tmenv-mclo-wk 𝐖 ϖ₂))
wk-MEnvᵀ-trans (wk-tmenv-jump-wk M πᵀ K ϖ₁) (wk-tmenv-jump-wk M₁ πᵀ₁ K₁ ϖ₂) = wk-tmenv-jump-wk M πᵀ K (wk-MEnvᵀ-trans ϖ₁ (wk-tmenv-jump-wk M₁ πᵀ₁ K₁ ϖ₂))

wk-mclo-id-η : (𝐖 : TM.MClo Γ X) → TM.wk-mclo wk-id 𝐖 ≡ 𝐖
wk-mclo-id-η TM.unit = refl
wk-mclo-id-η (TM.pair 𝐖₁ 𝐖₂) = cong₂ TM.pair (wk-mclo-id-η 𝐖₁) (wk-mclo-id-η 𝐖₂)
wk-mclo-id-η (TM.lam M) = refl
wk-mclo-id-η (TM.label x) = refl

wk-MEnvᵀ-id : (γ : TM.MEnv Γ) → WkMEnvᵀ (wk-id) γ γ
wk-MEnvᵀ-id TM.⋄ = wk-tmenv-ε
wk-MEnvᵀ-id (γ · TM.unit) = wk-tmenv-mclo-cong TM.unit (wk-MEnvᵀ-id γ)
wk-MEnvᵀ-id (γ · TM.pair x₁ x₂) =
  let
    a0 = wk-tmenv-mclo-cong (TM.pair x₁ x₂) (wk-MEnvᵀ-id γ)
  in
  subst (λ x → WkMEnvᵀ (wk-cong wk-id) (γ · x) (γ · TM.pair x₁ x₂)) (wk-mclo-id-η (TM.pair x₁ x₂)) a0
wk-MEnvᵀ-id (γ · TM.lam M) = wk-tmenv-mclo-cong (TM.lam M) (wk-MEnvᵀ-id γ)
wk-MEnvᵀ-id (γ · TM.label x) = wk-tmenv-mclo-cong (TM.label x) (wk-MEnvᵀ-id γ)
wk-MEnvᵀ-id (γ TM.·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-tmenv-jump-cong x x₁ x₂ (wk-MEnvᵀ-id γ)

wf-mclo-wk-mclo : {γ : TM.MEnv Γ} {𝐖 : TM.MClo Γ X} {𝐖₁ : TM.MClo Γ Y} → WellFormedTMClo γ 𝐖 → WellFormedTMClo γ 𝐖₁ → WellFormedTMClo (γ · 𝐖₁) (TM.wk-mclo (wk-wk wk-id) 𝐖)
wf-mclo-wk-mclo wf-mclo-unit g₁ = wf-mclo-unit
wf-mclo-wk-mclo wf-mclo-lam g₁ = wf-mclo-lam
wf-mclo-wk-mclo (wf-mclo-pair g g₂) g₁ = wf-mclo-pair (wf-mclo-wk-mclo g g₁) (wf-mclo-wk-mclo g₂ g₁)
wf-mclo-wk-mclo wf-mclo-label-h g₁ = wf-mclo-label-t-mclo wf-mclo-label-h
wf-mclo-wk-mclo (wf-mclo-label-t-mclo g) g₁ = wf-mclo-label-t-mclo (wf-mclo-label-t-mclo g)
wf-mclo-wk-mclo (wf-mclo-label-t-jump g) g₁ = wf-mclo-label-t-mclo (wf-mclo-label-t-jump g)

wf-mclo-wk-jump : {γ : TM.MEnv Γ} {𝐖 : TM.MClo Γ X} {M : Comp Γ Y} {π : Wk Γ Γ₁} {K : TM.CStack Γ₁ Y} → WellFormedTMClo γ 𝐖 → WellFormedTMClo (γ TM.·﹝ M ╎ π ╎ K ﹞) (TM.wk-mclo (wk-wk wk-id) 𝐖)
wf-mclo-wk-jump wf-mclo-unit = wf-mclo-unit
wf-mclo-wk-jump wf-mclo-lam = wf-mclo-lam
wf-mclo-wk-jump (wf-mclo-pair g g₁) = wf-mclo-pair (wf-mclo-wk-jump g) (wf-mclo-wk-jump g₁)
wf-mclo-wk-jump wf-mclo-label-h = wf-mclo-label-t-jump wf-mclo-label-h
wf-mclo-wk-jump (wf-mclo-label-t-mclo g) = wf-mclo-label-t-jump (wf-mclo-label-t-mclo g)
wf-mclo-wk-jump (wf-mclo-label-t-jump g) = wf-mclo-label-t-jump (wf-mclo-label-t-jump g)

wf-lookup : {γ : TM.MEnv Γ} → (i : Γ ∋ X) → (g : WellFormedTMEnv γ) → WellFormedTMClo γ (TM.lookup i γ)
wf-lookup here (wf-env-mclo g wf-mclo-unit) = wf-mclo-unit
wf-lookup here (wf-env-mclo g wf-mclo-lam) = wf-mclo-lam
wf-lookup here (wf-env-mclo g (wf-mclo-pair x₁ x₂)) = wf-mclo-pair (wf-mclo-wk-mclo x₁ (wf-mclo-pair x₁ x₂)) (wf-mclo-wk-mclo x₂ (wf-mclo-pair x₁ x₂))
wf-lookup here (wf-env-mclo g wf-mclo-label-h) = wf-mclo-label-t-mclo wf-mclo-label-h
wf-lookup here (wf-env-mclo g (wf-mclo-label-t-mclo x)) = wf-mclo-label-t-mclo (wf-mclo-label-t-mclo x)
wf-lookup here (wf-env-mclo g (wf-mclo-label-t-jump x)) = wf-mclo-label-t-mclo (wf-mclo-label-t-jump x)
wf-lookup here (wf-env-jump x) = wf-mclo-label-h
wf-lookup (there i) (wf-env-mclo g x) = wf-mclo-wk-mclo (wf-lookup i g) x
wf-lookup (there i) (wf-env-jump (wf-state-bottom M γ π x)) = wf-mclo-wk-jump (wf-lookup i x)
wf-lookup (there i) (wf-env-jump (wf-state-resume M₁ x x₁ x₂)) = wf-mclo-wk-jump (wf-lookup i x₂)

wf-lookup-label : {γ : TM.MEnv Γ} → (i : Γ ∋ `ℓ) → (g : WellFormedTMEnv γ) → WellFormedTMCState (TM.lookup-label i γ)
wf-lookup-label {γ = γ · (TM.label x)} here (wf-env-mclo g x₁) = wf-lookup-label x g
wf-lookup-label here (wf-env-jump x) = x
wf-lookup-label (there i) (wf-env-mclo g x) = wf-lookup-label i g
wf-lookup-label (there i) (wf-env-jump (wf-state-bottom M γ π x)) = wf-lookup-label i x
wf-lookup-label (there i) (wf-env-jump (wf-state-resume M₁ x x₁ x₂)) = wf-lookup-label i x₂

wf-eval : {γ : TM.MEnv Γ} → (W : Val Γ X) → (g : WellFormedTMEnv γ) → WellFormedTMClo γ (TM.eval W γ)
wf-eval (var i) (wf-env-mclo g x) = wf-lookup i (wf-env-mclo g x)
wf-eval (var i) (wf-env-jump x) = wf-lookup i (wf-env-jump x)
wf-eval (lam x) wf-env-empty = wf-mclo-lam
wf-eval (lam x) (wf-env-mclo g x₁) = wf-mclo-lam
wf-eval (lam x) (wf-env-jump x₁) = wf-mclo-lam
wf-eval (pair W W₁) wf-env-empty = wf-mclo-pair (wf-eval W wf-env-empty) (wf-eval W₁ wf-env-empty)
wf-eval (pair W W₁) (wf-env-mclo g x) = wf-mclo-pair (wf-eval W (wf-env-mclo g x)) (wf-eval W₁ (wf-env-mclo g x))
wf-eval (pair W W₁) (wf-env-jump x) = wf-mclo-pair (wf-eval W (wf-env-jump x)) (wf-eval W₁ (wf-env-jump x))
wf-eval unit wf-env-empty = wf-mclo-unit
wf-eval unit (wf-env-mclo g x) = wf-mclo-unit
wf-eval unit (wf-env-jump x) = wf-mclo-unit

wf-proj₁ : {γ : TM.MEnv Γ} {𝐖 : TM.MClo Γ (X₁ `× X₂)} → WellFormedTMClo γ 𝐖 → WellFormedTMClo γ (TM.proj₁-mclo 𝐖)
wf-proj₁ (wf-mclo-pair w₁ w₂) = w₁

wf-proj₂ : {γ : TM.MEnv Γ} {𝐖 : TM.MClo Γ (X₁ `× X₂)} → WellFormedTMClo γ 𝐖 → WellFormedTMClo γ (TM.proj₂-mclo 𝐖)
wf-proj₂ (wf-mclo-pair w₁ w₂) = w₂

wf-eval₁ : {γ : TM.MEnv Γ} → (W : Val Γ (X₁ `× X₂)) → (g : WellFormedTMEnv γ) → WellFormedTMClo γ (TM.eval₁ W γ)
wf-eval₁ W g = wf-proj₁ (wf-eval W g)

wf-eval₂ : {γ : TM.MEnv Γ} → (W : Val Γ (X₁ `× X₂)) → (g : WellFormedTMEnv γ) → WellFormedTMClo γ (TM.eval₂ W γ)
wf-eval₂ W g = wf-proj₂ (wf-eval W g)

wf-jump : {γ : TM.MEnv Γ} → (i : Γ ∋ `ℓ) → (g : WellFormedTMEnv γ) → WellFormedTMCState (TM.eval-jump (var i) γ)
wf-jump i g = wf-lookup-label i g

wf-preservation : {σ σ' : TM.CState} → (σ →ᵀᴹ σ') → WellFormedTMCState σ → WellFormedTMCState σ'
wf-preservation eval→ (wf-state-bottom (return W) γ π g) = wf-state-halt _ γ π g (wf-eval W g)
wf-preservation eval→ (wf-state-resume (return W) x x₁ g) = wf-state-result _ x x₁ g (wf-eval W g)
wf-preservation (return→ {K = TM.◻}) (wf-state-result 𝐖 x (wf-bottom M γ π x₁) g w) = wf-state-bottom _ (_ · 𝐖) _ (wf-env-mclo g w)
wf-preservation (return→ {K = < x₂ ； γ ； π >∷ K}) (wf-state-result 𝐖 ϖ₁ (wf-next M₁ M₂ ϖ₂ x₃ g₁) g₂ w) = wf-state-resume _ (wk-tmenv-mclo-wk 𝐖 (wk-MEnvᵀ-trans ϖ₁ ϖ₂)) x₃ (wf-env-mclo g₂ w)
wf-preservation push→ (wf-state-bottom M γ π g) = wf-state-resume _ (wk-MEnvᵀ-id γ) (wf-bottom _ γ π g) g
wf-preservation push→ (wf-state-resume M₁ x x₁ g) = wf-state-resume _ (wk-MEnvᵀ-id _) (wf-next _ _ x x₁ g) g
wf-preservation sub→ (wf-state-bottom M γ π g) = wf-state-bottom _ (γ TM.·﹝ _ ╎ π ╎ TM.◻ ﹞) (wk-wk π) (wf-env-jump (wf-state-bottom _ γ π g))
wf-preservation sub→ (wf-state-resume M₁ x x₁ g) = wf-state-resume _ (wk-tmenv-jump-wk _ _ _ x) x₁ (wf-env-jump (wf-state-resume _ x x₁ g))
wf-preservation (var→ {W = var i}) (wf-state-bottom M γ π g) = wf-jump i g
wf-preservation (var→ {W = var i}) (wf-state-resume M₁ x x₁ g) = wf-jump i g
wf-preservation (pmᶜ→ {W = W}) (wf-state-bottom M γ π g) = wf-state-bottom _ (γ · _ · TM.wk-mclo (wk-wk wk-id) _) (Wk.wk-wk (Wk.wk-wk π)) (wf-env-mclo (wf-env-mclo g (wf-eval₁ W g)) (wf-mclo-wk-mclo (wf-eval₂ W g) (wf-eval₁ W g)))
wf-preservation (pmᶜ→ {W = W}) (wf-state-resume M₁ x x₁ g) = wf-state-resume _ (wk-tmenv-mclo-wk (TM.wk-mclo (wk-wk wk-id) _) (wk-tmenv-mclo-wk _ x)) x₁ (wf-env-mclo (wf-env-mclo g (wf-eval₁ W g)) (wf-mclo-wk-mclo (wf-eval₂ W g) (wf-eval₁ W g)))
wf-preservation app→ (wf-state-bottom (app W₁ W₂) γ π g) = wf-state-bottom _ (γ · _) (Wk.wk-wk π) (wf-env-mclo g (wf-eval W₂ g))
wf-preservation app→ (wf-state-resume (app W₁ W₂) x x₁ g) = wf-state-resume _ (wk-tmenv-mclo-wk _ x) x₁ (wf-env-mclo g (wf-eval W₂ g))

init-wf : (M : ε ⊢ᶜ ℛ) → WellFormedTMCState TM.⟨ M ╎ ⋄ ╎ wk-ε ╎ TM.◻ ⟩
init-wf M = wf-state-bottom M ⋄ wk-ε wf-env-empty

---------------------------------------------------------------------------------
-- Translation of Telescope Environments into List Environments
---------------------------------------------------------------------------------

mutual

  tmcstack-to-mcstack : TM.CStack Γ X → M.CStack X
  tmcstack-to-mcstack ◻ = ◻
  tmcstack-to-mcstack (< x ； γ ； π >∷ K) = < x ； tmenv-to-menv γ >∷ tmcstack-to-mcstack K

  tmenv-to-menv : TM.MEnv Γ → M.MEnv Γ
  tmenv-to-menv ⋄ = ⋄
  tmenv-to-menv (γ · 𝐖) = tmenv-to-menv γ · mclo-to-mval 𝐖 γ
  tmenv-to-menv (γ ·﹝ M ╎ π ╎ K ﹞) = tmenv-to-menv γ · jumpᵛ M (tmenv-to-menv γ) (tmcstack-to-mcstack K)

  mclo-to-mval : TM.MClo Γ X → TM.MEnv Γ → M.MVal X
  mclo-to-mval unit γ = unitᵛ
  mclo-to-mval (pair 𝐖₁ 𝐖₂) γ = pairᵛ (mclo-to-mval 𝐖₁ γ) (mclo-to-mval 𝐖₂ γ)
  mclo-to-mval (lam M) γ = cloᵛ M (tmenv-to-menv γ)
  mclo-to-mval (label here) (γ · label i) = mclo-to-mval (label i) γ
  mclo-to-mval (label here) (γ ·﹝ M ╎ π ╎ K ﹞) = jumpᵛ M (tmenv-to-menv γ) (tmcstack-to-mcstack K)
  mclo-to-mval (label (there i)) (γ · 𝐖) = mclo-to-mval (label i) γ
  mclo-to-mval (label (there i)) (γ ·﹝ M ╎ π ╎ K ﹞) = mclo-to-mval (label i) γ

mutual

  wkmval : {Γ₁ Γ₂ : Ctx} → (𝐖 : TM.MClo Γ₂ X) → (π : Wk Γ₁ Γ₂) → (γ₁ : TM.MEnv Γ₁) → (γ₂ : TM.MEnv Γ₂) → WkMEnvᵀ π γ₁ γ₂ → WkMVal (mclo-to-mval (TM.wk-mclo π 𝐖) γ₁) (mclo-to-mval 𝐖 γ₂)
  wkmval TM.unit π γ₁ γ₂ g = wk-unitᵛ
  wkmval (TM.pair 𝐖 𝐖₁) π γ₁ γ₂ g = wk-pairᵛ (wkmval 𝐖 π γ₁ γ₂ g) (wkmval 𝐖₁ π γ₁ γ₂ g)
  wkmval (TM.lam M) π γ₁ γ₂ g = wk-cloᵛ π refl (wk-MEnvᵀ-to-wk-MEnvᴹ g)
  wkmval (label here) π γ₁ (γ₂ · (label x)) (wk-tmenv-mclo-cong 𝐖 g) = wkmval (label x) _ _ _ g
  wkmval (label here) π γ₁ γ₂ (wk-tmenv-jump-cong {π = π₁} M πᵀ K g) = wk-jumpᵛ π₁ refl (wk-MEnvᵀ-to-wk-MEnvᴹ g) wk-cstack-id
  wkmval (label here) π γ₁ γ₂ (wk-tmenv-mclo-wk 𝐖 g) = wkmval (label here) _ _ _ g
  wkmval (label here) π γ₁ γ₂ (wk-tmenv-jump-wk M πᵀ K g) = wkmval (label here) _ _ _ g
  wkmval (label (there x)) π γ₁ γ₂ (wk-tmenv-mclo-cong 𝐖 g) = wkmval (label x) _ _ _ g
  wkmval (label (there x)) π γ₁ γ₂ (wk-tmenv-jump-cong M πᵀ K g) = wkmval (label x) _ _ _ g
  wkmval (label (there x)) π γ₁ γ₂ (wk-tmenv-mclo-wk 𝐖 g) = wkmval (label (there x)) _ _ _ g
  wkmval (label (there x)) π γ₁ γ₂ (wk-tmenv-jump-wk M πᵀ K g) = wkmval (label (there x)) _ _ _ g

  wk-MEnvᵀ-to-wk-MEnvᴹ : {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {γ₁ : TM.MEnv Γ₁} {γ₂ : TM.MEnv Γ₂} → WkMEnvᵀ π γ₁ γ₂ → WkMEnvᴹ π (tmenv-to-menv γ₁) (tmenv-to-menv γ₂)
  wk-MEnvᵀ-to-wk-MEnvᴹ wk-tmenv-ε = wk-menv-ε
  wk-MEnvᵀ-to-wk-MEnvᴹ (wk-tmenv-mclo-cong {π = π} {γ₁ = γ₁} {γ₂ = γ₂} 𝐖 g) =
    let
      a0 : WkMVal (mclo-to-mval (TM.wk-mclo π 𝐖) γ₁) (mclo-to-mval 𝐖 γ₂)
      a0 = wkmval 𝐖 π γ₁ γ₂ g
      a1 = wk-menv-cong a0 (wk-MEnvᵀ-to-wk-MEnvᴹ g)
    in
    a1
  wk-MEnvᵀ-to-wk-MEnvᴹ (wk-tmenv-jump-cong M πᵀ K g) =
    let
      a0 = wk-jumpᵛ _ refl (wk-MEnvᵀ-to-wk-MEnvᴹ g) wk-cstack-id
      a1 = wk-menv-cong a0 (wk-MEnvᵀ-to-wk-MEnvᴹ g)
    in
    a1
  wk-MEnvᵀ-to-wk-MEnvᴹ (wk-tmenv-mclo-wk 𝐖 g) = wk-menv-wk (mclo-to-mval 𝐖 _) (wk-MEnvᵀ-to-wk-MEnvᴹ g)
  wk-MEnvᵀ-to-wk-MEnvᴹ (wk-tmenv-jump-wk M πᵀ K g) = wk-menv-wk (M.jumpᵛ M (tmenv-to-menv _) (tmcstack-to-mcstack K)) (wk-MEnvᵀ-to-wk-MEnvᴹ g)

tmcstate-to-mcstate : TM.CState → M.CState
tmcstate-to-mcstate ⟨ 𝐖 ； γ ╎ π ╎ K ⟩ = ⟨ mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩
tmcstate-to-mcstate ⟨ M ╎ γ ╎ π ╎ K ⟩ = ⟨ M ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩

next-state : {σ : M.CState} → M.Step? σ → M.CState
next-state {σ = σ} (M.done _) = σ
next-state (M.next {b = σ₁} _) = σ₁

wk-mclo-wk-comm : {𝐕 : TM.MClo Γ X} → (𝐖 : TM.MClo Γ Y) → (γ : TM.MEnv Γ) → WkMVal (mclo-to-mval (TM.wk-mclo (Wk.wk-wk wk-id) 𝐖) (γ · 𝐕)) (mclo-to-mval 𝐖 γ)
wk-mclo-wk-comm unit ⋄ = wk-unitᵛ
wk-mclo-wk-comm unit (γ · x) = wk-unitᵛ
wk-mclo-wk-comm unit (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-unitᵛ
wk-mclo-wk-comm (pair 𝐖 𝐖₁) ⋄ = wk-pairᵛ (wk-mclo-wk-comm 𝐖 ⋄) (wk-mclo-wk-comm 𝐖₁ ⋄)
wk-mclo-wk-comm (pair 𝐖 𝐖₁) (γ · x) = wk-pairᵛ (wk-mclo-wk-comm 𝐖 (γ · x)) (wk-mclo-wk-comm 𝐖₁ (γ · x))
wk-mclo-wk-comm (pair 𝐖 𝐖₁) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-pairᵛ (wk-mclo-wk-comm 𝐖 (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) (wk-mclo-wk-comm 𝐖₁ (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞))
wk-mclo-wk-comm {𝐕 = 𝐕} (lam M) ⋄ = wk-cloᵛ (wk-wk wk-ε) refl (wk-menv-wk (mclo-to-mval 𝐕 ⋄) wk-menv-ε)
wk-mclo-wk-comm (lam M) (γ · x) = wk-cloᵛ (wk-wk wk-id) refl (wk-menv-wk _ wk-menv-id)
wk-mclo-wk-comm (lam M) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-cloᵛ (wk-wk wk-id) refl (wk-menv-wk _ wk-menv-id)
wk-mclo-wk-comm (label x) (γ · x₁) = wk-mval-id
wk-mclo-wk-comm (label x) (γ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) = wk-mval-id

wk-mclo-wk-jump-comm : {M : Comp Γ X} {π : Wk Γ Δ} {K : TM.CStack Δ X} → (𝐖 : TM.MClo Γ Y) → (γ : TM.MEnv Γ) → WkMVal (mclo-to-mval (TM.wk-mclo (Wk.wk-wk wk-id) 𝐖) (γ ·﹝ M ╎ π ╎ K ﹞)) (mclo-to-mval 𝐖 γ)
wk-mclo-wk-jump-comm unit ⋄ = wk-unitᵛ
wk-mclo-wk-jump-comm unit (γ · x) = wk-unitᵛ
wk-mclo-wk-jump-comm unit (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-unitᵛ
wk-mclo-wk-jump-comm (pair 𝐖₁ 𝐖₂) ⋄ = wk-pairᵛ (wk-mclo-wk-jump-comm 𝐖₁ ⋄) (wk-mclo-wk-jump-comm 𝐖₂ ⋄)
wk-mclo-wk-jump-comm (pair 𝐖₁ 𝐖₂) (γ · x) = wk-pairᵛ (wk-mclo-wk-jump-comm 𝐖₁ (γ · x)) (wk-mclo-wk-jump-comm 𝐖₂ (γ · x))
wk-mclo-wk-jump-comm (pair 𝐖₁ 𝐖₂) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-pairᵛ (wk-mclo-wk-jump-comm 𝐖₁ (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) (wk-mclo-wk-jump-comm 𝐖₂ (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞))
wk-mclo-wk-jump-comm (lam M) ⋄ = wk-cloᵛ (wk-wk wk-ε) refl (wk-menv-wk (M.jumpᵛ _ (tmenv-to-menv ⋄) (tmcstack-to-mcstack _)) wk-menv-ε)
wk-mclo-wk-jump-comm (lam M) (γ · x) = wk-cloᵛ (wk-wk wk-id) refl (wk-menv-wk _ wk-menv-id)
wk-mclo-wk-jump-comm (lam M) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-cloᵛ (wk-wk wk-id) refl (wk-menv-wk _ wk-menv-id)
wk-mclo-wk-jump-comm (label x) (γ · x₁) = wk-mval-id
wk-mclo-wk-jump-comm (label x) (γ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) = wk-mval-id

lookup-wk : (i : Γ ∋ X) → (γ : TM.MEnv Γ) → WkMVal (mclo-to-mval (TM.lookup i γ) γ) (M.lookup i (tmenv-to-menv γ))
lookup-wk here (γ · x) = wk-mclo-wk-comm x γ
lookup-wk here (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-mclo-wk-comm {𝐕 = label here} (label here) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)
lookup-wk {X = X} (there i) (γ · x) = wk-mval-trans (wk-mclo-wk-comm (TM.lookup i γ) γ) (lookup-wk i γ)
lookup-wk (there i) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-mval-trans (wk-mclo-wk-jump-comm (TM.lookup i γ) γ) (lookup-wk i γ)

eval-wk : (W : Val Γ X) → (γ : TM.MEnv Γ) → WkMVal (mclo-to-mval (TM.eval W γ) γ) (M.eval W (tmenv-to-menv γ))
eval-wk (var i) (γ · 𝐖) = lookup-wk i (γ · 𝐖)
eval-wk (var i) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = lookup-wk i (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)
eval-wk (lam x) ⋄ = wk-mval-id
eval-wk (lam x) (γ · x₁) = wk-mval-id
eval-wk (lam x) (γ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) = wk-mval-id
eval-wk (pair W₁ W₂) ⋄ = wk-pairᵛ (eval-wk W₁ ⋄) (eval-wk W₂ ⋄)
eval-wk (pair W₁ W₂) (γ · x) = wk-pairᵛ (eval-wk W₁ (γ · x)) (eval-wk W₂ (γ · x))
eval-wk (pair W₁ W₂) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-pairᵛ (eval-wk W₁ (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) (eval-wk W₂ (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞))
eval-wk unit ⋄ = wk-mval-id
eval-wk unit (γ · x) = wk-mval-id
eval-wk unit (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-mval-id

proj₁-wk-mval-eq : (𝐖 : TM.MClo Γ (X₁ `× X₂)) → (γ : TM.MEnv Γ) → (M.proj₁-val (mclo-to-mval 𝐖 γ)) ≡ (mclo-to-mval (TM.proj₁-mclo 𝐖) γ)
proj₁-wk-mval-eq (pair 𝐖₁ 𝐖₂) ⋄ = refl
proj₁-wk-mval-eq (pair 𝐖₁ 𝐖₂) (γ · x) = refl
proj₁-wk-mval-eq (pair 𝐖₁ 𝐖₂) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = refl

proj₂-wk-mval-eq : (𝐖 : TM.MClo Γ (X₁ `× X₂)) → (γ : TM.MEnv Γ) → (M.proj₂-val (mclo-to-mval 𝐖 γ)) ≡ (mclo-to-mval (TM.proj₂-mclo 𝐖) γ)
proj₂-wk-mval-eq (pair 𝐖₁ 𝐖₂) ⋄ = refl
proj₂-wk-mval-eq (pair 𝐖₁ 𝐖₂) (γ · x) = refl
proj₂-wk-mval-eq (pair 𝐖₁ 𝐖₂) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = refl

eval₁-wk : (W : Val Γ (X₁ `× X₂)) → (γ : TM.MEnv Γ) → WkMVal (mclo-to-mval (TM.proj₁-mclo (TM.eval W γ)) γ) (M.proj₁-val (M.eval W (tmenv-to-menv γ)))
eval₁-wk W γ =
  let
    goal' : WkMVal (M.proj₁-val (mclo-to-mval (TM.eval W γ) γ)) (M.proj₁-val (M.eval W (tmenv-to-menv γ)))
    goal' = proj₁-wk-mval (eval-wk W γ)

    goal : WkMVal (mclo-to-mval (TM.proj₁-mclo (TM.eval W γ)) γ) (M.proj₁-val (M.eval W (tmenv-to-menv γ)))
    goal = subst (λ x → WkMVal x (M.proj₁-val (M.eval W (tmenv-to-menv γ)))) (proj₁-wk-mval-eq (TM.eval W γ) γ) goal'
  in
  goal

eval₂-wk : (W : Val Γ (X₁ `× X₂)) → (γ : TM.MEnv Γ) → WkMVal (mclo-to-mval (TM.wk-mclo (Wk.wk-wk wk-id) (TM.proj₂-mclo (TM.eval W γ))) (γ · TM.proj₁-mclo (TM.eval W γ))) (M.proj₂-val (M.eval W (tmenv-to-menv γ)))
eval₂-wk W γ =
  let
    goal' : WkMVal (M.proj₂-val (mclo-to-mval (TM.eval W γ) γ)) (M.proj₂-val (M.eval W (tmenv-to-menv γ)))
    goal' = proj₂-wk-mval (eval-wk W γ)

    goal'' : WkMVal (mclo-to-mval (TM.proj₂-mclo (TM.eval W γ)) γ) (M.proj₂-val (M.eval W (tmenv-to-menv γ)))
    goal'' = subst (λ x → WkMVal x (M.proj₂-val (M.eval W (tmenv-to-menv γ)))) (proj₂-wk-mval-eq (TM.eval W γ) γ) goal'

    goal : WkMVal (mclo-to-mval (TM.wk-mclo (Wk.wk-wk wk-id) (TM.proj₂-mclo (TM.eval W γ))) (γ · TM.proj₁-mclo (TM.eval W γ))) (M.proj₂-val (M.eval W (tmenv-to-menv γ)))
    goal = wk-mval-trans (wk-mclo-wk-comm (TM.proj₂-mclo (TM.eval W γ)) γ) goal''
  in
  goal

ctx-clo-to-comp-wk : (W : Val Γ (X `⇒ Y)) → (γ : TM.MEnv Γ) → Wk Γ (proj₁ (M.clo-to-comp (M.eval W (tmenv-to-menv γ))))
ctx-clo-to-comp-wk {Γ = Γ ∙ (X `⇒ Y)} (var here) (γ · lam M) = wk-wk wk-id
ctx-clo-to-comp-wk (var (there i)) (γ · 𝐖) = wk-wk (ctx-clo-to-comp-wk (var i) γ)
ctx-clo-to-comp-wk (var (there i)) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-wk (ctx-clo-to-comp-wk (var i) γ)
ctx-clo-to-comp-wk (lam M) ⋄ = wk-id
ctx-clo-to-comp-wk (lam M) (γ · 𝐖) = wk-id
ctx-clo-to-comp-wk (lam M) (γ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) = wk-id

clo-to-comp-eq : (W : Val Γ (X `⇒ Y)) → (γ : TM.MEnv Γ) → TM.lam-to-comp (TM.eval W γ) ≡ wk-comp (wk-cong (ctx-clo-to-comp-wk W γ)) (proj₁ (proj₂ (M.clo-to-comp (M.eval W (tmenv-to-menv γ)))))
clo-to-comp-eq (var here) (γ · lam M) = refl
clo-to-comp-eq {Γ = Γ ∙ Z} (var (there i)) (γ · 𝐖) with (TM.lookup i γ) in eq
... | lam M =
  let
    a0 : TM.lookup i γ ≡ lam M
    a0 = eq

    a1 : TM.lam-to-comp (TM.lookup i γ) ≡ wk-comp (wk-cong (ctx-clo-to-comp-wk (var i) γ)) (proj₁ (proj₂ (M.clo-to-comp (M.eval (var i) (tmenv-to-menv γ)))))
    a1 = clo-to-comp-eq (var i) γ

    a1' : M ≡ wk-comp (wk-cong (ctx-clo-to-comp-wk (var i) γ)) (proj₁ (proj₂ (M.clo-to-comp (M.eval (var i) (tmenv-to-menv γ)))))
    a1' = subst (λ x → TM.lam-to-comp x ≡ wk-comp (wk-cong (ctx-clo-to-comp-wk (var i) γ)) (proj₁ (proj₂ (M.clo-to-comp (M.eval (var i) (tmenv-to-menv γ)))))) a0 a1

    a2 : wk-comp (wk-cong ((wk-wk {X = Z}) wk-id)) (TM.lam-to-comp (TM.lookup i γ)) ≡ (wk-comp (wk-cong (wk-wk (ctx-clo-to-comp-wk (var i) γ))) (proj₁ (proj₂ (M.clo-to-comp (M.eval (var i) (tmenv-to-menv γ))))))
    a2 = cong (wk-comp (wk-cong (wk-wk wk-id))) a1

    goal : wk-comp (Wk.wk-cong (Wk.wk-wk wk-id)) M ≡ wk-comp (Wk.wk-cong (Wk.wk-wk (ctx-clo-to-comp-wk (var i) γ))) (proj₁ (proj₂ (M.clo-to-comp (M.lookup i (tmenv-to-menv γ)))))
    goal = cong (wk-comp (Wk.wk-cong (Wk.wk-wk wk-id))) a1'
  in
  goal
clo-to-comp-eq (var (there i)) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)  with (TM.lookup i γ) in eq
... | lam M =
  let
    a0 : TM.lookup i γ ≡ lam M
    a0 = eq

    a1 : TM.lam-to-comp (TM.lookup i γ) ≡ wk-comp (wk-cong (ctx-clo-to-comp-wk (var i) γ)) (proj₁ (proj₂ (M.clo-to-comp (M.eval (var i) (tmenv-to-menv γ)))))
    a1 = clo-to-comp-eq (var i) γ

    a1' : M ≡ wk-comp (wk-cong (ctx-clo-to-comp-wk (var i) γ)) (proj₁ (proj₂ (M.clo-to-comp (M.eval (var i) (tmenv-to-menv γ)))))
    a1' = subst (λ x → TM.lam-to-comp x ≡ wk-comp (wk-cong (ctx-clo-to-comp-wk (var i) γ)) (proj₁ (proj₂ (M.clo-to-comp (M.eval (var i) (tmenv-to-menv γ)))))) a0 a1

    a2 : wk-comp (wk-cong ((wk-wk {X = Z}) wk-id)) (TM.lam-to-comp (TM.lookup i γ)) ≡ (wk-comp (wk-cong (wk-wk (ctx-clo-to-comp-wk (var i) γ))) (proj₁ (proj₂ (M.clo-to-comp (M.eval (var i) (tmenv-to-menv γ))))))
    a2 = cong (wk-comp (wk-cong (wk-wk wk-id))) a1

    goal : wk-comp (Wk.wk-cong (Wk.wk-wk wk-id)) M ≡ wk-comp (Wk.wk-cong (Wk.wk-wk (ctx-clo-to-comp-wk (var i) γ))) (proj₁ (proj₂ (M.clo-to-comp (M.lookup i (tmenv-to-menv γ)))))
    goal = cong (wk-comp (Wk.wk-cong (Wk.wk-wk wk-id))) a1'
  in
  goal
clo-to-comp-eq (lam M) ⋄ = refl
clo-to-comp-eq (lam M) (γ · x₁) = refl
clo-to-comp-eq (lam M) (γ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) = refl

clo-wk-menv : (W : Val Γ (X `⇒ Y)) → (γ : TM.MEnv Γ) → WkMEnvᴹ (ctx-clo-to-comp-wk W γ) (tmenv-to-menv γ) (proj₂ (proj₂ (M.clo-to-comp (M.eval W (tmenv-to-menv γ)))))
clo-wk-menv (var here) (γ · lam M) = wk-menv-wk (mclo-to-mval (lam M) γ) wk-menv-id
clo-wk-menv (var (there i)) (γ · 𝐖) = wk-menv-wk (mclo-to-mval 𝐖 γ) (clo-wk-menv (var i) γ)
clo-wk-menv (var (there i)) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-menv-wk (M.jumpᵛ x (tmenv-to-menv γ) (tmcstack-to-mcstack x₂)) (clo-wk-menv (var i) γ)
clo-wk-menv (lam M) ⋄ = wk-menv-ε
clo-wk-menv (lam M) (γ · x₁) = wk-menv-id
clo-wk-menv (lam M) (γ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) = wk-menv-id

eval-clo : (W₁ : Val Γ (X `⇒ Y)) → (W₂ : Val Γ X) → (γ : TM.MEnv Γ) → (K : M.CStack Y) → WkCStateᴹ ⟨ TM.lam-to-comp (TM.eval W₁ γ) ╎ tmenv-to-menv γ · mclo-to-mval (TM.eval W₂ γ) γ ╎ K ⟩ (M.eval-clo W₁ W₂ (tmenv-to-menv γ) K)
eval-clo W₁ W₂ γ K =
  let
    a0 = clo-to-comp-eq W₁ γ

    b3 : WkMEnvᴹ (wk-cong (ctx-clo-to-comp-wk W₁ γ)) (tmenv-to-menv γ · mclo-to-mval (TM.eval W₂ γ) γ) (proj₂ (proj₂ (M.clo-to-comp (M.eval W₁ (tmenv-to-menv γ)))) · M.eval W₂ (tmenv-to-menv γ))
    b3 = wk-menv-cong (eval-wk W₂ γ) (clo-wk-menv W₁ γ)
  in
  wk-cstate-comp (wk-cong (ctx-clo-to-comp-wk W₁ γ)) a0 b3 wk-cstack-id

lookup-eq : (x : Γ ∋ `ℓ) → (γ : TM.MEnv Γ) → (M.lookup x (tmenv-to-menv γ)) ≡ (mclo-to-mval (label x) γ)
lookup-eq here (γ · (label x)) = refl
lookup-eq here (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = refl
lookup-eq (there x) (γ · x₁) = lookup-eq x γ
lookup-eq (there x) (γ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) = lookup-eq x γ

lookup-label-wk : (i : Γ ∋ `ℓ) → (γ : TM.MEnv Γ) → WkCStateᴹ (M.jump-to-state (M.lookup i (tmenv-to-menv γ))) (tmcstate-to-mcstate (TM.lookup-label i γ))
lookup-label-wk here (γ · (label x)) =
  let
    a0 : WkCStateᴹ (M.jump-to-state (M.lookup x (tmenv-to-menv γ))) (tmcstate-to-mcstate (TM.lookup-label x γ))
    a0 = lookup-label-wk x γ
    goal : WkCStateᴹ (M.jump-to-state (mclo-to-mval (label x) γ)) (tmcstate-to-mcstate (TM.lookup-label x γ))
    goal = subst (λ z → WkCStateᴹ (M.jump-to-state z) (tmcstate-to-mcstate (TM.lookup-label x γ))) (lookup-eq x γ) a0
  in
  goal
lookup-label-wk here (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-cstate-comp wk-id refl wk-menv-id wk-cstack-id
lookup-label-wk (there i) (γ · 𝐖) = lookup-label-wk i γ
lookup-label-wk (there i) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = lookup-label-wk i γ

eval-jump-wk : (W : Val Γ `ℓ) → (γ : TM.MEnv Γ) → WkCStateᴹ (M.eval-jump W (tmenv-to-menv γ)) (tmcstate-to-mcstate (TM.eval-jump W γ))
eval-jump-wk (var i) γ = lookup-label-wk i γ

tmstep-to-mstep : {σ σ' : TM.CState} → (WellFormedTMCState σ) → (σ →ᵀᴹ σ') → Σ[ σᴹ ∈ M.CState ] (((tmcstate-to-mcstate σ) →ᴹ σᴹ) × σᴹ ≈ᴹ (tmcstate-to-mcstate σ'))
tmstep-to-mstep wf (eval→ {W = W} {γ = γ} {K = K}) =
  --Goal: ⟨ return W ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩ →ᴹ ⟨ mclo-to-mval (TM.eval W γ) γ ╎ tmcstack-to-mcstack K ⟩
  let
    -- a0 : M.Step? ⟨ return W ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩
    -- a0 = progress ⟨ return W ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩

    -- next : next-state a0 ≡ ⟨ M.eval W (tmenv-to-menv γ) ╎ tmcstack-to-mcstack K ⟩
    -- next = refl

    eqv : ⟨ M.eval W (tmenv-to-menv γ) ╎ tmcstack-to-mcstack K ⟩ ≈ᴹ ⟨ mclo-to-mval (TM.eval W γ) γ ╎ tmcstack-to-mcstack K ⟩
    eqv = ≈ᴹ-bc (≈-wk₁ (wk-cstate-result (eval-wk W γ) wk-cstack-id))
  in
  ⟨ M.eval W (tmenv-to-menv γ) ╎ tmcstack-to-mcstack K ⟩ , eval→ , eqv
tmstep-to-mstep (wf-state-result {π₁ = π₁} {π₂ = π₂} _ w _ _ _) (return→ {𝐖 = 𝐖} {M₁ = M₁} {γ = γ} {γ₁ = γ₁} {K = K} {π = π}) =
  -- Goal: ⟨ mclo-to-mval 𝐖 γ ╎ M.< M₁ ； tmenv-to-menv γ₁ >∷ tmcstack-to-mcstack K ⟩ →ᴹ ⟨ wk-comp (wk-cong π) M₁ ╎ tmenv-to-menv γ M.· mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩
  let
    -- a0 = progress ⟨ mclo-to-mval 𝐖 γ ╎ M.< M₁ ； tmenv-to-menv γ₁ >∷ tmcstack-to-mcstack K ⟩

    -- next : next-state a0 ≡ ⟨ M₁ ╎ tmenv-to-menv γ₁ · mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩
    -- next = refl

    eqv : ⟨ M₁ ╎ tmenv-to-menv γ₁ · mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩ ≈ᴹ ⟨ wk-comp (wk-cong π) M₁ ╎ tmenv-to-menv γ M.· mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩
    eqv = ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp (Wk.wk-cong π₁) refl (wk-menv-cong wk-mval-id (wk-MEnvᵀ-to-wk-MEnvᴹ w)) wk-cstack-id))
  in
  ⟨ M₁ ╎ tmenv-to-menv γ₁ · mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩ , return→ , eqv
tmstep-to-mstep wf push→ = _ , push→ , ≈ᴹ-refl
tmstep-to-mstep wf sub→ = _ , sub→ , ≈ᴹ-refl
tmstep-to-mstep wf (var→ {W = W} {γ = γ} {K = K}) =
  -- Goal: ⟨ var W ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩ →ᴹ tmcstate-to-mcstate (TM.eval-jump W γ)
  let
    -- a0 = progress ⟨ var W ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩

    -- next : next-state a0 ≡ M.eval-jump W (tmenv-to-menv γ)
    -- next = refl

    eqv : M.eval-jump W (tmenv-to-menv γ) ≈ᴹ tmcstate-to-mcstate (TM.eval-jump W γ)
    eqv = ≈ᴹ-bc (≈-wk₂ (eval-jump-wk W γ))
  in
  _ , var→ , eqv
tmstep-to-mstep wf (pmᶜ→ {W = W} {γ = γ} {M = M} {K = K}) =
  -- Goal: ⟨ pm W M ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩ →ᴹ ⟨ M ╎ tmenv-to-menv γ M.· mclo-to-mval (TM.eval₁ W γ) γ M.· mclo-to-mval (TM.wk-mclo (wk-wk wk-id) (TM.eval₂ W γ)) (γ TM.· TM.eval₁ W γ) ╎ tmcstack-to-mcstack K ⟩
  let
    -- a0 = progress ⟨ pm W M ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩

    -- next : next-state a0 ≡ ⟨ M ╎ tmenv-to-menv γ · M.eval₁ W (tmenv-to-menv γ) · M.eval₂ W (tmenv-to-menv γ) ╎ tmcstack-to-mcstack K ⟩
    -- next = refl

    wk1 : WkMEnvᴹ (Wk.wk-cong (Wk.wk-cong wk-id)) (tmenv-to-menv γ · mclo-to-mval (TM.proj₁-mclo (TM.eval W γ)) γ · mclo-to-mval (TM.wk-mclo (Wk.wk-wk wk-id) (TM.proj₂-mclo (TM.eval W γ))) (γ · TM.proj₁-mclo (TM.eval W γ))) (tmenv-to-menv γ · M.proj₁-val (M.eval W (tmenv-to-menv γ)) · M.proj₂-val (M.eval W (tmenv-to-menv γ)))
    wk1 = wk-menv-cong (eval₂-wk W γ) (wk-menv-cong (eval₁-wk W γ) wk-menv-id)

    eqv : ⟨ M ╎ tmenv-to-menv γ · M.eval₁ W (tmenv-to-menv γ) · M.eval₂ W (tmenv-to-menv γ) ╎ tmcstack-to-mcstack K ⟩ ≈ᴹ ⟨ M ╎ tmenv-to-menv γ M.· mclo-to-mval (TM.eval₁ W γ) γ M.· mclo-to-mval (TM.wk-mclo (wk-wk wk-id) (TM.eval₂ W γ)) (γ TM.· TM.eval₁ W γ) ╎ tmcstack-to-mcstack K ⟩
    eqv = ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp wk-id refl wk1 wk-cstack-id))
  in
  _ , pmᶜ→ , eqv
tmstep-to-mstep wf (app→ {W₁ = W₁} {W₂ = W₂} {γ = γ} {K = K}) =
  -- Goal: ⟨ app W₁ W₂ ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩ →ᴹ ⟨ TM.lam-to-comp (TM.eval W₁ γ) ╎ tmenv-to-menv γ M.· mclo-to-mval (TM.eval W₂ γ) γ ╎ tmcstack-to-mcstack K ⟩
  let
    -- a0 = progress ⟨ app W₁ W₂ ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩

    -- next : next-state a0 ≡ M.eval-clo W₁ W₂ (tmenv-to-menv γ) (tmcstack-to-mcstack K)
    -- next = refl

    wk1 : WkCStateᴹ ⟨ TM.lam-to-comp (TM.eval W₁ γ) ╎ tmenv-to-menv γ · mclo-to-mval (TM.eval W₂ γ) γ ╎ tmcstack-to-mcstack K ⟩ (M.eval-clo W₁ W₂ (tmenv-to-menv γ) (tmcstack-to-mcstack K))
    wk1 = eval-clo W₁ W₂ γ (tmcstack-to-mcstack K)

    eqv : M.eval-clo W₁ W₂ (tmenv-to-menv γ) (tmcstack-to-mcstack K) ≈ᴹ ⟨ TM.lam-to-comp (TM.eval W₁ γ) ╎ tmenv-to-menv γ M.· mclo-to-mval (TM.eval W₂ γ) γ ╎ tmcstack-to-mcstack K ⟩
    eqv = ≈ᴹ-bc (≈-wk₁ wk1)
  in
  _ , app→ , eqv

----------------------------------------------------------------------------------------

open Reduction _→ᴹ_ renaming (_~>*_ to _→ᴹ*_; Normal to Normalᴹ)
open Reduction _→ᵀᴹ_ renaming (_~>*_ to _→ᵀᴹ*_; Normal to Normalᵀᴹ)

progress-t₁ : {σ₀ : TM.CState} {σ₀ᴹ σᴹ : M.CState} → (WkCStateᴹ (tmcstate-to-mcstate σ₀) σ₀ᴹ) → (σ₀ᴹ →ᴹ σᴹ) → Σ[ σ ∈ TM.CState ] (σ₀ →ᵀᴹ σ)
progress-t₁ {σ₀ = ⟨ 𝐖 ； γ ╎ π ╎ ◻ ⟩} ((wk-cstate-result x ())) return→
progress-t₁ {σ₀ = ⟨ 𝐖 ； γ ╎ π ╎ TM.< x₂ ； γ₁ ； π₁ >∷ K ⟩} ((wk-cstate-result x x₁)) return→ = ⟨ wk-comp (wk-cong π) x₂ ╎ γ · 𝐖 ╎ wk-wk (wk-trans π π₁) ╎ K ⟩ , return→
progress-t₁ {σ₀ = ⟨ return x ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp π₁ refl x₁ x₂)) eval→ = _ , eval→
progress-t₁ {σ₀ = ⟨ pm x M ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp π₁ refl x₁ x₂)) pmᶜ→ = _ , pmᶜ→
progress-t₁ {σ₀ = ⟨ push M M₁ ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp π₁ refl x₁ x₂)) push→ = _ , push→
progress-t₁ {σ₀ = ⟨ app x x₃ ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp π₁ refl x₁ x₂)) app→ = _ , app→
progress-t₁ {σ₀ = ⟨ var x ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp π₁ refl x₁ x₂)) var→ = _ , var→
progress-t₁ {σ₀ = ⟨ sub M M₁ ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp π₁ refl x₁ x₂)) sub→ = _ , sub→

progress-t₂ : {σ₀ : TM.CState} {σ₀ᴹ σᴹ : M.CState} → (WkCStateᴹ σ₀ᴹ (tmcstate-to-mcstate σ₀)) → (σ₀ᴹ →ᴹ σᴹ) → Σ[ σ ∈ TM.CState ] (σ₀ →ᵀᴹ σ)
progress-t₂ {σ₀ = ⟨ 𝐖 ； γ ╎ π ╎ ◻ ⟩} ((wk-cstate-result x ())) return→
progress-t₂ {σ₀ = ⟨ 𝐖 ； γ ╎ π ╎ < x₂ ； γ₁ ； π₁ >∷ K ⟩} ((wk-cstate-result x x₁)) return→ = ⟨ wk-comp (wk-cong π) x₂ ╎ γ · 𝐖 ╎ wk-wk (wk-trans π π₁) ╎ K ⟩ , return→
progress-t₂ {σ₀ = ⟨ return x₃ ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp π₁ refl x₁ x₂)) eval→ = _ , eval→
progress-t₂ {σ₀ = ⟨ pm x₃ M ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp π₁ refl x₁ x₂)) pmᶜ→ = _ , pmᶜ→
progress-t₂ {σ₀ = ⟨ push M M₁ ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp π₁ refl x₁ x₂)) push→ = _ , push→
progress-t₂ {σ₀ = ⟨ app x₃ x₄ ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp π₁ refl x₁ x₂)) app→ = _ , app→
progress-t₂ {σ₀ = ⟨ var x₃ ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp π₁ refl x₁ x₂)) var→ = _ , var→
progress-t₂ {σ₀ = ⟨ sub M M₁ ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp π₁ refl x₁ x₂)) sub→ = _ , sub→

progress-t : {σ₀ : TM.CState} {σ₀ᴹ σᴹ : M.CState} → (σ₀ᴹ ≈ᴹ (tmcstate-to-mcstate σ₀)) → (σ₀ᴹ →ᴹ σᴹ) → Σ[ σ ∈ TM.CState ] (σ₀ →ᵀᴹ σ)
progress-t (≈ᴹ-bc (≈-wk₁ w)) s = progress-t₁ w s
progress-t (≈ᴹ-bc (≈-wk₂ w)) s = progress-t₂ w s
progress-t (≈-trans {σ₂ = σ₂} {σ₃ = σ₃} w eqv) s = progress-t {σ₀ᴹ = σ₂} eqv (proj₁ (proj₂ (mstep-eqv' w s)))

tmstep-to-mstep-eqv : {σ σ' : TM.CState} {σᴹ : M.CState} → (WellFormedTMCState σ) → (σ →ᵀᴹ σ') → ((tmcstate-to-mcstate σ) →ᴹ σᴹ) → σᴹ ≈ᴹ (tmcstate-to-mcstate σ')
tmstep-to-mstep-eqv {σ' = σ'} {σᴹ = σᴹ} wf σ→ᵀᴹσ' mσ→ᴹσᴹ =
  let
    t = tmstep-to-mstep wf σ→ᵀᴹσ'
    t' = proj₂ (proj₂ t)
    goal : σᴹ ≈ᴹ tmcstate-to-mcstate σ'
    goal = subst (λ x → x ≈ᴹ tmcstate-to-mcstate σ') (M.determinismꟲ' (proj₁ (proj₂ t)) mσ→ᴹσᴹ) t'
  in
  goal

exec-TM : {σ₀ : TM.CState} {σ₀ᴹ σᴹ : M.CState} → (WellFormedTMCState σ₀) → ((tmcstate-to-mcstate σ₀) ≈ᴹ σ₀ᴹ) → (σ₀ᴹ →ᴹ* σᴹ) → Σ[ σ ∈ TM.CState ] ((σ₀ →ᵀᴹ* σ) × ((tmcstate-to-mcstate σ) ≈ᴹ σᴹ) × WellFormedTMCState σ)
exec-TM {σ₀ = σ₀} wf eqv ε = σ₀ , ε , eqv , wf
exec-TM wf eqv (σ₀ᴹ→σ₁ᴹ ◅ σ₁ᴹ→*σᴹ) =
  let
    σ₀→ᵀᴹσ₁ = proj₂ (progress-t (≈ᴹ-sym eqv) σ₀ᴹ→σ₁ᴹ)
    me = mstep-eqv (≈ᴹ-sym eqv) σ₀ᴹ→σ₁ᴹ
    eqv = tmstep-to-mstep-eqv wf σ₀→ᵀᴹσ₁ (proj₁ (proj₂ me))
    wf' = wf-preservation σ₀→ᵀᴹσ₁ wf
    IH = exec-TM wf' (≈ᴹ-sym (≈ᴹ-trans (proj₂ (proj₂ me)) eqv))  σ₁ᴹ→*σᴹ
  in
  proj₁ IH , σ₀→ᵀᴹσ₁ ◅ proj₁ (proj₂ IH) , proj₁ (proj₂ (proj₂ IH)) , proj₂ (proj₂ (proj₂ IH))

normal-t : {σ : TM.CState} {σᴹ : M.CState} → WellFormedTMCState σ → Normalᴹ σᴹ → ((tmcstate-to-mcstate σ) ≈ᴹ σᴹ) → Normalᵀᴹ σ
normal-t {σ = σ} {σᴹ = σᴹ} wf n eqv s = n (proj₁ (proj₂ (mstep-eqv eqv (proj₁ (proj₂ (tmstep-to-mstep wf s))))))

exec :    (M : ε ⊢ᶜ ℛ)
        → Σ[ σ ∈ TM.CState ]
          Σ[ NF ∈ Normalᵀᴹ σ ]
          TM.⟨ M ╎ ⋄ ╎ wk-ε ╎ TM.◻ ⟩ →ᵀᴹ* σ
exec M =
  let
    wf = init-wf M
    mexec = M.exec M
    t = exec-TM wf (≈ᴹ-bc (≈-wk₂ (wk-cstate-comp wk-ε refl wk-menv-ε wk-cstack-empty))) (proj₁ (proj₂ (proj₂ (proj₂ mexec))))
  in
  proj₁ t , normal-t (proj₂ (proj₂ (proj₂ t))) (proj₁ (proj₂ (proj₂ mexec))) (proj₁ (proj₂ (proj₂ t))) , proj₁ (proj₂ t)
