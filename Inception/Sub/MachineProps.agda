{-# OPTIONS --no-postfix-projections #-}

open import Inception.Sub.Syntax using (Ty)

module Inception.Sub.MachineProps (ℛ : Ty) where

open import Inception.Prelude
open import Inception.Sub.Syntax

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; subst; cong; cong₂)
open Eq.≡-Reasoning using (step-≡-⟩; step-≡-∣; step-≡-⟨; _∎; step-≡)

open import Inception.Sub.Machine ℛ

-- Weakening of Machine Values, Environments and Stacks
mutual

  data WkMVal : (𝐖₁ : MVal X) → (𝐖₂ : MVal X) → Set where

      wk-unitᵛ : WkMVal unitᵛ unitᵛ

      wk-pairᵛ : {𝐖₁₁ 𝐖₁₂ : MVal X₁} {𝐖₂₁ 𝐖₂₂ : MVal X₂} → WkMVal 𝐖₁₁ 𝐖₁₂ → WkMVal 𝐖₂₁ 𝐖₂₂ → WkMVal (pairᵛ 𝐖₁₁ 𝐖₂₁) (pairᵛ 𝐖₁₂ 𝐖₂₂)

      wk-cloᵛ : {Γ₁ Γ₂ : Ctx} {M₁ : (Γ₁ ∙ X) ⊢ᶜ Y} {M₂ : (Γ₂ ∙ X) ⊢ᶜ Y} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} → (π : Γ₁ ⊇ Γ₂) → M₁ ≡ wk-comp (wk-cong π) M₂ → (WkMEnvᴹ π γ₁ γ₂) → WkMVal (cloᵛ M₁ γ₁) (cloᵛ M₂ γ₂)

      wk-jumpᵛ : {Γ₁ Γ₂ : Ctx} {M₁ : Γ₁ ⊢ᶜ X} {M₂ : Γ₂ ⊢ᶜ X} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} {K₁ K₂ : CStack X} → (π : Γ₁ ⊇ Γ₂) → M₁ ≡ wk-comp π M₂ → (WkMEnvᴹ π γ₁ γ₂) → (WkCStackᴹ K₁ K₂) → WkMVal (jumpᵛ M₁ γ₁ K₁) (jumpᵛ M₂ γ₂ K₂)

  data WkMEnvᴹ : {Γ₁ Γ₂ : Ctx} → (π : Wk Γ₁ Γ₂) → (γ₁ : MEnv Γ₁) → (γ₂ : MEnv Γ₂) → Set where

      wk-menv-ε    : WkMEnvᴹ wk-ε ⋄ ⋄

      wk-menv-cong : {Γ₁ Γ₂ : Ctx} {π : Γ₁ ⊇ Γ₂} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} {𝐖₁ : MVal X} {𝐖₂ : MVal X} → WkMVal 𝐖₁ 𝐖₂ → WkMEnvᴹ π γ₁ γ₂ → WkMEnvᴹ (wk-cong π) (γ₁ · 𝐖₁) (γ₂ · 𝐖₂)

      wk-menv-wk : {Γ₁ Γ₂ : Ctx} {π : Γ₁ ⊇ Γ₂} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} → (𝐖 : MVal X) → WkMEnvᴹ π γ₁ γ₂ → WkMEnvᴹ (wk-wk π) (γ₁ · 𝐖) γ₂

  data WkCStackᴹ : (K₁ : CStack X) → (K₂ : CStack X) → Set where

    wk-cstack-empty : WkCStackᴹ ◻ ◻

    wk-cstack-push : {Γ₁ Γ₂ : Ctx} {M₁ : (Γ₁ ∙ Y) ⊢ᶜ X} {M₂ : (Γ₂ ∙ Y) ⊢ᶜ X} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} {K₁ K₂ : CStack X}
                    → (π : Γ₁ ⊇ Γ₂) → M₁ ≡ wk-comp (wk-cong π) M₂ → WkMEnvᴹ π γ₁ γ₂ → WkCStackᴹ K₁ K₂
                    → WkCStackᴹ (< M₁ ； γ₁ >∷ K₁) (< M₂ ； γ₂ >∷ K₂)

-- Weakening of Machine States
data WkCStateᴹ : CState → CState → Set where

  wk-cstate-result : {𝐖₁ 𝐖₂ : MVal X} {K₁ K₂ : CStack X}
                     → WkMVal 𝐖₁ 𝐖₂ → WkCStackᴹ K₁ K₂
                     → WkCStateᴹ ⟨ 𝐖₁ ╎ K₁ ⟩ ⟨ 𝐖₂ ╎ K₂ ⟩

  wk-cstate-comp : {Γ₁ Γ₂ : Ctx} {M₁ : Γ₁ ⊢ᶜ X} {M₂ : Γ₂ ⊢ᶜ X} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} {K₁ K₂ : CStack X}
                   → (π : Γ₁ ⊇ Γ₂) → M₁ ≡ wk-comp π M₂ → (WkMEnvᴹ π γ₁ γ₂) → WkCStackᴹ K₁ K₂
                   → WkCStateᴹ ⟨ M₁ ╎ γ₁ ╎ K₁ ⟩ ⟨ M₂ ╎ γ₂ ╎ K₂ ⟩

data _≈₀ᴹ_ : CState → CState → Set where

    ≈-wk₁ : {σ₁ σ₂ : CState} → WkCStateᴹ σ₁ σ₂ → σ₂ ≈₀ᴹ σ₁

    ≈-wk₂ : {σ₁ σ₂ : CState} → WkCStateᴹ σ₁ σ₂ → σ₁ ≈₀ᴹ σ₂

-- Equivalence of states
data _≈ᴹ_ : CState → CState → Set where

    ≈ᴹ-bc   : {σ₁ σ₂ : CState} → σ₁ ≈₀ᴹ σ₂ → σ₁ ≈ᴹ σ₂

    ≈-trans : {σ₁ σ₂ σ₃ : CState} → σ₁ ≈₀ᴹ σ₂ → σ₂ ≈ᴹ σ₃ → σ₁ ≈ᴹ σ₃

mutual

  wk-mval-id : {𝐖 : MVal X} → WkMVal 𝐖 𝐖
  wk-mval-id {𝐖 = unitᵛ} = wk-unitᵛ
  wk-mval-id {𝐖 = pairᵛ 𝐖 𝐖₁} = wk-pairᵛ wk-mval-id wk-mval-id
  wk-mval-id {𝐖 = cloᵛ M γ} = wk-cloᵛ wk-id refl wk-menv-id
  wk-mval-id {𝐖 = jumpᵛ M γ K} = wk-jumpᵛ wk-id refl wk-menv-id wk-cstack-id

  wk-menv-id : {γ : MEnv Γ} → WkMEnvᴹ wk-id γ γ
  wk-menv-id {γ = ⋄} = wk-menv-ε
  wk-menv-id {γ = γ · 𝐖} = wk-menv-cong wk-mval-id wk-menv-id

  wk-cstack-id : {K : CStack X} → WkCStackᴹ K K
  wk-cstack-id {K = ◻} = wk-cstack-empty
  wk-cstack-id {K = < x ； γ >∷ K} = wk-cstack-push wk-id refl wk-menv-id wk-cstack-id

mutual

  wk-MEnvᴹ-trans : {Γ₁ Γ₂ Γ₃ : Ctx} {π₁ : Γ₁ ⊇ Γ₂} {π₂ : Γ₂ ⊇ Γ₃} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} {γ₃ : MEnv Γ₃} → WkMEnvᴹ π₁ γ₁ γ₂ → WkMEnvᴹ π₂ γ₂ γ₃ → WkMEnvᴹ (wk-trans π₁ π₂) γ₁ γ₃
  wk-MEnvᴹ-trans wk-menv-ε wk-menv-ε = wk-menv-ε
  wk-MEnvᴹ-trans (wk-menv-cong x₁ ϖ₁) (wk-menv-cong x₂ ϖ₂) = wk-menv-cong (wk-mval-trans x₁ x₂) (wk-MEnvᴹ-trans ϖ₁ ϖ₂)
  wk-MEnvᴹ-trans (wk-menv-cong {𝐖₁ = 𝐖₁} x₁ ϖ₁) (wk-menv-wk 𝐖₂ ϖ₂) = wk-menv-wk 𝐖₁ (wk-MEnvᴹ-trans ϖ₁ ϖ₂)
  wk-MEnvᴹ-trans (wk-menv-wk 𝐖 ϖ) wk-menv-ε = wk-menv-wk 𝐖 ϖ
  wk-MEnvᴹ-trans (wk-menv-wk 𝐖₁ ϖ₁) (wk-menv-cong x₂ ϖ₂) = wk-menv-wk 𝐖₁ (wk-MEnvᴹ-trans ϖ₁ (wk-menv-cong x₂ ϖ₂))
  wk-MEnvᴹ-trans (wk-menv-wk 𝐖₁ ϖ₁) (wk-menv-wk 𝐖₂ ϖ₂) = wk-menv-wk 𝐖₁ (wk-MEnvᴹ-trans ϖ₁ (wk-menv-wk 𝐖₂ ϖ₂))

  wk-cstack-trans : {K₁ K₂ K₃ : CStack X} → WkCStackᴹ K₁ K₂ → WkCStackᴹ K₂ K₃ → WkCStackᴹ K₁ K₃
  wk-cstack-trans wk-cstack-empty wk-cstack-empty = wk-cstack-empty
  wk-cstack-trans (wk-cstack-push {M₁ = M₁₁} {M₂ = M₂₁} π₁ eq₁ ϖ₁ x₁) (wk-cstack-push {M₁ = M₁₂} {M₂ = M₂₂} π₂ eq₂ ϖ₂ x₂) =
                        wk-cstack-push
                          (wk-trans π₁ π₂)
                          (M₁₁ ≡⟨ eq₁ ⟩ wk-comp (wk-cong π₁) M₂₁ ≡⟨ cong (wk-comp (wk-cong π₁)) eq₂ ⟩ wk-comp (wk-cong (wk-trans π₁ π₂)) M₂₂ ∎)
                          (wk-MEnvᴹ-trans ϖ₁ ϖ₂)
                          (wk-cstack-trans x₁ x₂)

  wk-mval-trans : {𝐖₁ 𝐖₂ 𝐖₃ : MVal X} → WkMVal 𝐖₁ 𝐖₂ → WkMVal 𝐖₂ 𝐖₃ → WkMVal 𝐖₁ 𝐖₃
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

wk-cstate-trans : {σ₁ σ₂ σ₃ : CState} → WkCStateᴹ σ₁ σ₂ → WkCStateᴹ σ₂ σ₃ → WkCStateᴹ σ₁ σ₃
wk-cstate-trans (wk-cstate-result ϖ₁ x₁) (wk-cstate-result ϖ₂ x₂) = wk-cstate-result (wk-mval-trans ϖ₁ ϖ₂) (wk-cstack-trans x₁ x₂)
wk-cstate-trans (wk-cstate-comp {M₁ = M₁₁} {M₂ = M₂₁} π₁ eq₁ ϖ₁ x₁) (wk-cstate-comp {M₁ = M₁₂} {M₂ = M₂₂} π₂ eq₂ ϖ₂ x₂) =
                        wk-cstate-comp
                          (wk-trans π₁ π₂)
                          (M₁₁ ≡⟨ eq₁ ⟩ wk-comp π₁ M₂₁ ≡⟨ cong (wk-comp π₁) eq₂ ⟩ wk-comp (wk-trans π₁ π₂) M₂₂ ∎)
                          (wk-MEnvᴹ-trans ϖ₁ ϖ₂)
                          (wk-cstack-trans x₁ x₂)

≈ᴹ-refl : {σ : CState} → σ ≈ᴹ σ
≈ᴹ-refl {σ = ⟨ 𝐖 ╎ K ⟩} = ≈ᴹ-bc (≈-wk₂ (wk-cstate-result wk-mval-id wk-cstack-id))
≈ᴹ-refl {σ = ⟨ M ╎ γ ╎ K ⟩} = ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp wk-id refl wk-menv-id wk-cstack-id))

≈₀ᴹ-sym : {σ₁ σ₂ : CState} → σ₁ ≈₀ᴹ σ₂ → σ₂ ≈₀ᴹ σ₁
≈₀ᴹ-sym (≈-wk₁ x) = (≈-wk₂ x)
≈₀ᴹ-sym (≈-wk₂ x) = (≈-wk₁ x)

mutual
  ≈ᴹ-sym : {σ₁ σ₂ : CState} → σ₁ ≈ᴹ σ₂ → σ₂ ≈ᴹ σ₁
  ≈ᴹ-sym (≈ᴹ-bc (≈-wk₁ x)) = ≈ᴹ-bc (≈-wk₂ x)
  ≈ᴹ-sym (≈ᴹ-bc (≈-wk₂ x)) = ≈ᴹ-bc (≈-wk₁ x)
  ≈ᴹ-sym (≈-trans x y) = ≈ᴹ-trans (≈ᴹ-sym y) (≈ᴹ-bc (≈₀ᴹ-sym x))

  ≈ᴹ-trans : {σ₁ σ₂ σ₃ : CState} → σ₁ ≈ᴹ σ₂ → σ₂ ≈ᴹ σ₃ → σ₁ ≈ᴹ σ₃
  ≈ᴹ-trans (≈ᴹ-bc x) (≈ᴹ-bc x₁) = ≈-trans x (≈ᴹ-bc x₁)
  ≈ᴹ-trans (≈ᴹ-bc x) (≈-trans x₁ s₂) = ≈-trans x (≈-trans x₁ s₂)
  ≈ᴹ-trans (≈-trans x s₁) (≈ᴹ-bc x₁) = ≈-trans x (≈ᴹ-trans s₁ (≈ᴹ-bc x₁))
  ≈ᴹ-trans (≈-trans x s₁) (≈-trans x₁ s₂) = ≈-trans x (≈ᴹ-trans s₁ (≈-trans x₁ s₂))

proj₁-wk-mval : {𝐖 𝐕 : MVal (X₁ `× X₂)} → WkMVal 𝐖 𝐕 → WkMVal (proj₁-val 𝐖) (proj₁-val 𝐕)
proj₁-wk-mval (wk-pairᵛ wm₁ wm₂) = wm₁

proj₂-wk-mval : {𝐖 𝐕 : MVal (X₁ `× X₂)} → WkMVal 𝐖 𝐕 → WkMVal (proj₂-val 𝐖) (proj₂-val 𝐕)
proj₂-wk-mval (wk-pairᵛ wm₁ wm₂) = wm₂

jump-wk : {Γ₁ Γ₂ : Ctx} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} {π : Γ₁ ⊇ Γ₂} → (i : Γ₂ ∋ `ℓ) → (WkMEnvᴹ π γ₁ γ₂) → eval-jump (var (wk-mem π i)) γ₁ ≈ᴹ eval-jump (var i) γ₂
jump-wk here (wk-menv-cong (wk-jumpᵛ π x x₁ x₂) ϖ) = ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp π x x₁ x₂))
jump-wk here (wk-menv-wk 𝐖 ϖ) = jump-wk here ϖ
jump-wk (there i) (wk-menv-cong x ϖ) = jump-wk i ϖ
jump-wk (there i) (wk-menv-wk 𝐖 ϖ) = jump-wk (there i) ϖ

eval-mem-wk : {Γ₁ Γ₂ : Ctx} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} {π : Γ₁ ⊇ Γ₂} → (i : Γ₂ ∋ X) → (WkMEnvᴹ π γ₁ γ₂) → WkMVal (eval (var (wk-mem π i)) γ₁) (eval (var i) γ₂)
eval-mem-wk here (wk-menv-cong x ϖ) = x
eval-mem-wk here (wk-menv-wk 𝐖 ϖ) = eval-mem-wk here ϖ
eval-mem-wk (there i) (wk-menv-cong x ϖ) = eval-mem-wk i ϖ
eval-mem-wk (there i) (wk-menv-wk 𝐖 ϖ) = eval-mem-wk (there i) ϖ

eval-val-wk : {Γ₁ Γ₂ : Ctx} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} {π : Γ₁ ⊇ Γ₂} → (W : Γ₂ ⊢ᵛ X) → (WkMEnvᴹ π γ₁ γ₂) → WkMVal (eval (wk-val π W) γ₁) (eval W γ₂)
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

eval₁-mem-wk : {Γ₁ Γ₂ : Ctx} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} {π : Γ₁ ⊇ Γ₂} → (i : Γ₂ ∋ (X₁ `× X₂)) → (WkMEnvᴹ π γ₁ γ₂) → WkMVal (eval₁ (var (wk-mem π i)) γ₁) (eval₁ (var i) γ₂)
eval₁-mem-wk here (wk-menv-cong x ϖ) = proj₁-wk-mval x
eval₁-mem-wk here (wk-menv-wk 𝐖 ϖ) = eval₁-mem-wk here ϖ
eval₁-mem-wk (there i) (wk-menv-cong x ϖ) = eval₁-mem-wk i ϖ
eval₁-mem-wk (there i) (wk-menv-wk 𝐖 ϖ) = eval₁-mem-wk (there i) ϖ

eval₁-val-wk : {Γ₁ Γ₂ : Ctx} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} {π : Γ₁ ⊇ Γ₂} → (W : Γ₂ ⊢ᵛ (X₁ `× X₂)) → (WkMEnvᴹ π γ₁ γ₂) → WkMVal (eval₁ (wk-val π W) γ₁) (eval₁ W γ₂)
eval₁-val-wk (var i) (wk-menv-cong x ϖ) = eval₁-mem-wk i (wk-menv-cong x ϖ)
eval₁-val-wk (var i) (wk-menv-wk 𝐖 ϖ) = eval₁-mem-wk i ϖ
eval₁-val-wk (pair W₁ W₂) wk-menv-ε = wk-mval-id
eval₁-val-wk {γ₁ = γ₁ · 𝐖₁} {γ₂ = γ₂ · 𝐖₂} {π = wk-cong π} (pair W₁ W₂) (wk-menv-cong x ϖ) =
  let
    goal : WkMVal (eval (wk-val (Wk.wk-cong π) W₁) (γ₁ · 𝐖₁)) (eval W₁ (γ₂ · 𝐖₂))
    goal = eval-val-wk W₁ (wk-menv-cong x ϖ)
  in
  goal
eval₁-val-wk (pair W₁ W₂) (wk-menv-wk 𝐖 ϖ) = eval-val-wk W₁ (wk-menv-wk 𝐖 ϖ)

eval₂-mem-wk : {Γ₁ Γ₂ : Ctx} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} {π : Γ₁ ⊇ Γ₂} → (i : Γ₂ ∋ (X₁ `× X₂)) → (WkMEnvᴹ π γ₁ γ₂) → WkMVal (eval₂ (var (wk-mem π i)) γ₁) (eval₂ (var i) γ₂)
eval₂-mem-wk here (wk-menv-cong x ϖ) = proj₂-wk-mval x
eval₂-mem-wk here (wk-menv-wk 𝐖 ϖ) = eval₂-mem-wk here ϖ
eval₂-mem-wk (there i) (wk-menv-cong x ϖ) = eval₂-mem-wk i ϖ
eval₂-mem-wk (there i) (wk-menv-wk 𝐖 ϖ) = eval₂-mem-wk (there i) ϖ

eval₂-val-wk : {Γ₁ Γ₂ : Ctx} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} {π : Γ₁ ⊇ Γ₂} → (W : Γ₂ ⊢ᵛ (X₁ `× X₂)) → (WkMEnvᴹ π γ₁ γ₂) → WkMVal (eval₂ (wk-val π W) γ₁) (eval₂ W γ₂)
eval₂-val-wk (var i) (wk-menv-cong x ϖ) = eval₂-mem-wk i (wk-menv-cong x ϖ)
eval₂-val-wk (var i) (wk-menv-wk 𝐖 ϖ) = eval₂-mem-wk i ϖ
eval₂-val-wk (pair W₁ W₂) wk-menv-ε = wk-mval-id
eval₂-val-wk (pair W₁ W₂) (wk-menv-cong x ϖ) = eval-val-wk W₂ (wk-menv-cong x ϖ)
eval₂-val-wk (pair W₁ W₂) (wk-menv-wk 𝐖 ϖ) = eval-val-wk W₂ (wk-menv-wk 𝐖 ϖ)

clo-to-comp-wk-proj₁ : {𝐖₁ 𝐖₂ : MVal (X `⇒ Y)} → WkMVal 𝐖₁ 𝐖₂ → (proj₁ (clo-to-comp 𝐖₁)) ⊇ (proj₁ (clo-to-comp 𝐖₂))
clo-to-comp-wk-proj₁ (wk-cloᵛ π x x₁) = π

clo-to-comp-wk-mem-cong : {Γ₁ Γ₂ : Ctx} {π : Γ₁ ⊇ Γ₂} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} → (i : Γ₂ ∋ (X `⇒ Y)) → (ϖ : WkMEnvᴹ π γ₁ γ₂) → (proj₁ (clo-to-comp (eval (var (wk-mem π i)) γ₁))) ⊇ (proj₁ (clo-to-comp (eval (var i) γ₂)))
clo-to-comp-wk-mem-cong {π = wk-ε} {γ₁ = ⋄} {γ₂ = ⋄} () ϖ
clo-to-comp-wk-mem-cong {π = wk-cong π} {γ₁ = γ₁ · 𝐖₁} {γ₂ = γ₂ · 𝐖₂} here (wk-menv-cong x₂ ϖ) = clo-to-comp-wk-proj₁ x₂
clo-to-comp-wk-mem-cong {π = wk-cong π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} (there i) (wk-menv-cong x₂ ϖ) = clo-to-comp-wk-mem-cong i ϖ
clo-to-comp-wk-mem-cong {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = ⋄} () ϖ
clo-to-comp-wk-mem-cong {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} here (wk-menv-wk 𝐖 ϖ) = clo-to-comp-wk-mem-cong here ϖ
clo-to-comp-wk-mem-cong {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} (there i) (wk-menv-wk 𝐖 ϖ) = clo-to-comp-wk-mem-cong (there i) ϖ

clo-to-comp-wk-cong : {Γ₁ Γ₂ : Ctx} {π : Γ₁ ⊇ Γ₂} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} → (W : Γ₂ ⊢ᵛ (X `⇒ Y)) → (ϖ : WkMEnvᴹ π γ₁ γ₂) → (proj₁ (clo-to-comp (eval (wk-val π W) γ₁))) ⊇ (proj₁ (clo-to-comp (eval W γ₂)))
clo-to-comp-wk-cong {π = wk-cong π} (var i) (wk-menv-cong x ϖ) = clo-to-comp-wk-mem-cong i (wk-menv-cong x ϖ)
clo-to-comp-wk-cong {π = wk-wk π} (var i) (wk-menv-wk 𝐖 ϖ) = clo-to-comp-wk-mem-cong i ϖ
clo-to-comp-wk-cong {π = wk-ε} (lam M) wk-menv-ε = Wk.wk-ε
clo-to-comp-wk-cong {π = wk-cong π} (lam M) (wk-menv-cong x₁ ϖ) = Wk.wk-cong π
clo-to-comp-wk-cong {π = wk-wk π} (lam M) (wk-menv-wk 𝐖 ϖ) = Wk.wk-wk π

clo-to-comp-wk-proj₁-proj₂ : {𝐖₁ 𝐖₂ : MVal (X `⇒ Y)} → (w : WkMVal 𝐖₁ 𝐖₂) → proj₁ (proj₂ (clo-to-comp 𝐖₁)) ≡ wk-comp (Wk.wk-cong (clo-to-comp-wk-proj₁ w)) (proj₁ (proj₂ (clo-to-comp 𝐖₂)))
clo-to-comp-wk-proj₁-proj₂ (wk-cloᵛ π x x₁) = x

clo-to-comp-wk-proj₂-proj₂ : {𝐖₁ 𝐖₂ : MVal (X `⇒ Y)} → (w : WkMVal 𝐖₁ 𝐖₂) → WkMEnvᴹ (clo-to-comp-wk-proj₁ w) (proj₂ (proj₂ (clo-to-comp 𝐖₁))) (proj₂ (proj₂ (clo-to-comp 𝐖₂)))
clo-to-comp-wk-proj₂-proj₂ (wk-cloᵛ π x x₁) = x₁

cc-wk-eq : {Γ₁ Γ₂ : Ctx} {π : Γ₁ ⊇ Γ₂} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} {𝐖 : MVal Z} → (i : Γ₂ ∋ (X `⇒ Y)) → (ϖ : WkMEnvᴹ π γ₁ γ₂) → clo-to-comp-wk-mem-cong i ϖ ≡ clo-to-comp-wk-mem-cong i (wk-menv-wk 𝐖 ϖ)
cc-wk-eq {π = wk-ε} {γ₁ = ⋄} {γ₂ = ⋄} () ϖ
cc-wk-eq {π = wk-cong π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} here (wk-menv-cong x₂ ϖ) = refl
cc-wk-eq {π = wk-cong π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} (there i) (wk-menv-cong x₂ ϖ) = refl
cc-wk-eq {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = ⋄} () ϖ
cc-wk-eq {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} here (wk-menv-wk 𝐖 ϖ) = refl
cc-wk-eq {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} (there i) (wk-menv-wk 𝐖 ϖ) = refl

cc-eq-eq : {Γ₁ Γ₂ : Ctx} {π : Γ₁ ⊇ Γ₂} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} → (i : Γ₂ ∋ (X `⇒ Y)) → (ϖ : WkMEnvᴹ π γ₁ γ₂) → clo-to-comp-wk-cong (var i) ϖ ≡ clo-to-comp-wk-mem-cong i ϖ
cc-eq-eq here (wk-menv-cong x ϖ) = refl
cc-eq-eq here (wk-menv-wk 𝐖 ϖ) = cc-wk-eq {𝐖 = 𝐖} here ϖ
cc-eq-eq (there i) (wk-menv-cong x ϖ) = refl
cc-eq-eq (there i) (wk-menv-wk 𝐖 ϖ) = cc-wk-eq {𝐖 = 𝐖} (there i) ϖ

clo-to-comp-wk-mem-eq : {Γ₁ Γ₂ : Ctx} {π : Γ₁ ⊇ Γ₂} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} → (i : Γ₂ ∋ (X `⇒ Y)) → (ϖ : WkMEnvᴹ π γ₁ γ₂) → proj₁ (proj₂ (clo-to-comp (eval (var (wk-mem π i)) γ₁))) ≡ wk-comp (wk-cong (clo-to-comp-wk-cong (var i) ϖ)) (proj₁ (proj₂ (clo-to-comp (eval (var i) γ₂))))
clo-to-comp-wk-mem-eq {π = wk-ε} {γ₁ = ⋄} {γ₂ = ⋄} () ϖ
clo-to-comp-wk-mem-eq {π = wk-cong π} {γ₁ = γ₁ · 𝐖₁} {γ₂ = γ₂ · 𝐖₂} here (wk-menv-cong w ϖ) = clo-to-comp-wk-proj₁-proj₂ w
clo-to-comp-wk-mem-eq {π = wk-cong π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} (there i) (wk-menv-cong x₂ ϖ) =
  let
    a₀ : proj₁ (proj₂ (clo-to-comp (lookup (wk-mem π i) γ₁))) ≡ wk-comp (wk-cong (clo-to-comp-wk-cong (var i) ϖ)) (proj₁ (proj₂ (clo-to-comp (lookup i γ₂))))
    a₀ = clo-to-comp-wk-mem-eq i ϖ

    goal : proj₁ (proj₂ (clo-to-comp (lookup (wk-mem π i) γ₁))) ≡ wk-comp (wk-cong (clo-to-comp-wk-mem-cong i ϖ)) (proj₁ (proj₂ (clo-to-comp (lookup i γ₂))))
    goal = subst (λ z → proj₁ (proj₂ (clo-to-comp (lookup (wk-mem π i) γ₁))) ≡ wk-comp (wk-cong z) (proj₁ (proj₂ (clo-to-comp (lookup i γ₂))))) (cc-eq-eq i ϖ) a₀
  in
  goal
clo-to-comp-wk-mem-eq {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = ⋄} () ϖ
clo-to-comp-wk-mem-eq {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} here (wk-menv-wk 𝐖 ϖ) =
  let
    a₀ : proj₁ (proj₂ (clo-to-comp (lookup (wk-mem π here) γ₁))) ≡ wk-comp (wk-cong (clo-to-comp-wk-cong (var here) ϖ)) (proj₁ (proj₂ (clo-to-comp x₁)))
    a₀ = clo-to-comp-wk-mem-eq here ϖ

    goal : proj₁ (proj₂ (clo-to-comp (lookup (wk-mem π here) γ₁))) ≡ wk-comp (wk-cong (clo-to-comp-wk-mem-cong here ϖ)) (proj₁ (proj₂ (clo-to-comp x₁)))
    goal = subst (λ z → proj₁ (proj₂ (clo-to-comp (lookup (wk-mem π here) γ₁))) ≡ wk-comp (wk-cong z) (proj₁ (proj₂ (clo-to-comp x₁)))) (cc-eq-eq here ϖ) a₀
  in
  goal
clo-to-comp-wk-mem-eq {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} (there i) (wk-menv-wk 𝐖 ϖ) =
  let
    a₀ : proj₁ (proj₂ (clo-to-comp (eval (var (wk-mem π (there i))) γ₁))) ≡ wk-comp (wk-cong (clo-to-comp-wk-cong (var (there i)) ϖ)) (proj₁ (proj₂ (clo-to-comp (lookup i γ₂))))
    a₀ = clo-to-comp-wk-mem-eq (there i) ϖ

    goal : proj₁ (proj₂ (clo-to-comp (lookup (wk-mem π (_∋_.there i)) γ₁))) ≡ wk-comp (Wk.wk-cong (clo-to-comp-wk-mem-cong (_∋_.there i) ϖ)) (proj₁ (proj₂ (clo-to-comp (lookup i γ₂))))
    goal = subst (λ z → proj₁ (proj₂ (clo-to-comp (lookup (wk-mem π (_∋_.there i)) γ₁))) ≡ wk-comp (Wk.wk-cong z) (proj₁ (proj₂ (clo-to-comp (lookup i γ₂))))) (cc-eq-eq (there i) ϖ) a₀
  in
  goal

clo-to-comp-wk-eq : {Γ₁ Γ₂ : Ctx} {π : Γ₁ ⊇ Γ₂} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} → (W : Γ₂ ⊢ᵛ (X `⇒ Y)) → (ϖ : WkMEnvᴹ π γ₁ γ₂) → proj₁ (proj₂ (clo-to-comp (eval (wk-val π W) γ₁))) ≡ wk-comp (wk-cong (clo-to-comp-wk-cong W ϖ)) (proj₁ (proj₂ (clo-to-comp (eval W γ₂))))
clo-to-comp-wk-eq {π = wk-cong π} (var i) (wk-menv-cong x ϖ) = clo-to-comp-wk-mem-eq i (wk-menv-cong x ϖ)
clo-to-comp-wk-eq {π = wk-wk π} (var i) (wk-menv-wk 𝐖 ϖ) = clo-to-comp-wk-mem-eq i (wk-menv-wk 𝐖 ϖ)
clo-to-comp-wk-eq {π = wk-ε} (lam M) wk-menv-ε = refl
clo-to-comp-wk-eq {π = wk-cong π} (lam M) (wk-menv-cong x₁ ϖ) = refl
clo-to-comp-wk-eq {π = wk-wk π} (lam M) (wk-menv-wk 𝐖 ϖ) = refl

clo-to-comp-mem-wk-menv : {Γ₁ Γ₂ : Ctx} {π : Γ₁ ⊇ Γ₂} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} → (i : Γ₂ ∋ (X `⇒ Y)) → (ϖ : WkMEnvᴹ π γ₁ γ₂) → WkMEnvᴹ (clo-to-comp-wk-cong (var i) ϖ) (proj₂ (proj₂ (clo-to-comp (eval (var (wk-mem π i)) γ₁)))) (proj₂ (proj₂ (clo-to-comp (eval (var i) γ₂))))
clo-to-comp-mem-wk-menv {π = wk-ε} {γ₁ = ⋄} {γ₂ = ⋄} () ϖ
clo-to-comp-mem-wk-menv {π = wk-cong π} {γ₁ = γ₁ · 𝐖₁} {γ₂ = γ₂ · 𝐖₂} here (wk-menv-cong w ϖ) =
  let
    goal : WkMEnvᴹ (clo-to-comp-wk-proj₁ w) (proj₂ (proj₂ (clo-to-comp 𝐖₁))) (proj₂ (proj₂ (clo-to-comp 𝐖₂)))
    goal = clo-to-comp-wk-proj₂-proj₂ w
  in
  goal
clo-to-comp-mem-wk-menv {π = wk-cong π} {γ₁ = γ₁ · 𝐖₁} {γ₂ = γ₂ · 𝐖₂} (there i) (wk-menv-cong x₂ ϖ) =
  let
    a₀ : WkMEnvᴹ (clo-to-comp-wk-cong (var i) ϖ) (proj₂ (proj₂ (clo-to-comp (lookup (wk-mem π i) γ₁)))) (proj₂ (proj₂ (clo-to-comp (lookup i γ₂))))
    a₀ = clo-to-comp-mem-wk-menv i ϖ

    goal : WkMEnvᴹ (clo-to-comp-wk-mem-cong i ϖ) (proj₂ (proj₂ (clo-to-comp (lookup (wk-mem π i) γ₁)))) (proj₂ (proj₂ (clo-to-comp (lookup i γ₂))))
    goal = subst (λ z → WkMEnvᴹ z (proj₂ (proj₂ (clo-to-comp (lookup (wk-mem π i) γ₁)))) (proj₂ (proj₂ (clo-to-comp (lookup i γ₂))))) (cc-eq-eq i ϖ) a₀
  in
  goal
clo-to-comp-mem-wk-menv {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = ⋄} () ϖ
clo-to-comp-mem-wk-menv {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} here (wk-menv-wk 𝐖 ϖ) =
  let
    a₀ : WkMEnvᴹ (clo-to-comp-wk-cong (var here) ϖ) (proj₂ (proj₂ (clo-to-comp (eval (var (wk-mem π here)) γ₁)))) (proj₂ (proj₂ (clo-to-comp (eval (var here) (γ₂ · x₁)))))
    a₀ = clo-to-comp-mem-wk-menv here ϖ

    goal : WkMEnvᴹ (clo-to-comp-wk-mem-cong _∋_.here ϖ) (proj₂ (proj₂ (clo-to-comp (lookup (wk-mem π _∋_.here) γ₁)))) (proj₂ (proj₂ (clo-to-comp x₁)))
    goal = subst (λ z → WkMEnvᴹ z (proj₂ (proj₂ (clo-to-comp (eval (var (wk-mem π here)) γ₁)))) (proj₂ (proj₂ (clo-to-comp (eval (var here) (γ₂ · x₁)))))) (cc-eq-eq _∋_.here ϖ) a₀
  in
  goal
clo-to-comp-mem-wk-menv {π = wk-wk π} {γ₁ = γ₁ · x} {γ₂ = γ₂ · x₁} (there i) (wk-menv-wk 𝐖 ϖ) =
  let
    a₀ : WkMEnvᴹ (clo-to-comp-wk-cong (var (there i)) ϖ) (proj₂ (proj₂ (clo-to-comp (eval (var (wk-mem π (there i))) γ₁)))) (proj₂ (proj₂ (clo-to-comp (eval (var (there i)) (γ₂ · x₁)))))
    a₀ = clo-to-comp-mem-wk-menv (there i) ϖ

    goal : WkMEnvᴹ (clo-to-comp-wk-mem-cong (_∋_.there i) ϖ) (proj₂ (proj₂ (clo-to-comp (lookup (wk-mem π (_∋_.there i)) γ₁)))) (proj₂ (proj₂ (clo-to-comp (lookup i γ₂))))
    goal = subst (λ z → WkMEnvᴹ z (proj₂ (proj₂ (clo-to-comp (eval (var (wk-mem π (there i))) γ₁)))) (proj₂ (proj₂ (clo-to-comp (eval (var (there i)) (γ₂ · x₁)))))) (cc-eq-eq (there i) ϖ) a₀
  in
  goal

clo-to-comp-wk-menv : {Γ₁ Γ₂ : Ctx} {π : Γ₁ ⊇ Γ₂} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} → (W : Γ₂ ⊢ᵛ (X `⇒ Y)) → (ϖ : WkMEnvᴹ π γ₁ γ₂) → WkMEnvᴹ (clo-to-comp-wk-cong W ϖ) (proj₂ (proj₂ (clo-to-comp (eval (wk-val π W) γ₁)))) (proj₂ (proj₂ (clo-to-comp (eval W γ₂))))
clo-to-comp-wk-menv (var i) (wk-menv-cong x ϖ) = clo-to-comp-mem-wk-menv i (wk-menv-cong x ϖ)
clo-to-comp-wk-menv (var i) (wk-menv-wk 𝐖 ϖ) = clo-to-comp-mem-wk-menv i (wk-menv-wk 𝐖 ϖ)
clo-to-comp-wk-menv (lam M) wk-menv-ε = wk-menv-ε
clo-to-comp-wk-menv (lam M) (wk-menv-cong x₁ ϖ) = wk-menv-cong x₁ ϖ
clo-to-comp-wk-menv (lam M) (wk-menv-wk 𝐖 ϖ) = wk-menv-wk 𝐖 ϖ

mstep-eqv₁ : {σ₁₁ σ₂₁ σ₁₂ : CState} → (WkCStateᴹ σ₁₂ σ₁₁) → (σ₁₁ →ᶜ σ₂₁) → Σ[ σ₂₂ ∈ CState ] ((σ₁₂ →ᶜ σ₂₂) × σ₂₁ ≈ᴹ σ₂₂)
mstep-eqv₁ (wk-cstate-result {K₁ = < x₂ ； γ >∷ K₁} x (wk-cstack-push π x₁ x₃ x₄)) return→ = _ , return→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp (wk-cong π) x₁ (wk-menv-cong x x₃) x₄))
mstep-eqv₁ (wk-cstate-comp {M₁ = return W} {M₂ = return W₂} π refl x₁ x₂) eval→ = _ , eval→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-result (eval-val-wk W₂ x₁) x₂))
mstep-eqv₁ (wk-cstate-comp {M₁ = push M₁ M₂} π refl x₁ x₂) push→ = _ , push→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp π refl x₁ (wk-cstack-push π refl x₁ x₂)))
mstep-eqv₁ (wk-cstate-comp {M₁ = sub M₁ M₂} π refl x₁ x₂) sub→ = _ , sub→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp (Wk.wk-cong π) refl (wk-menv-cong (wk-jumpᵛ π refl x₁ x₂) x₁) x₂))
mstep-eqv₁ (wk-cstate-comp {M₁ = var (var i₁)} {M₂ = var (var i)} π refl x₁ x₂) var→ = _ , var→ , ≈ᴹ-sym (jump-wk i x₁)
mstep-eqv₁ (wk-cstate-comp {M₁ = pm x₃ M₁} {M₂ = pm W₂ M₂} π refl x₁ x₂) pmᶜ→ = _ , pmᶜ→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp (Wk.wk-cong (Wk.wk-cong π)) refl (wk-menv-cong (eval₂-val-wk W₂ x₁) (wk-menv-cong (eval₁-val-wk W₂ x₁) x₁)) x₂))
mstep-eqv₁ (wk-cstate-comp {M₁ = app x₃ x₄} {M₂ = app x₅ x₆} π refl x₁ x₂) app→ = _ , app→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp (wk-cong (clo-to-comp-wk-cong x₅ x₁)) (clo-to-comp-wk-eq x₅ x₁) (wk-menv-cong (eval-val-wk x₆ x₁) (clo-to-comp-wk-menv x₅ x₁)) x₂))

mstep-eqv₂ : {σ₁₁ σ₂₁ σ₁₂ : CState} → (WkCStateᴹ σ₁₁ σ₁₂) → (σ₁₁ →ᶜ σ₂₁) → Σ[ σ₂₂ ∈ CState ] ((σ₁₂ →ᶜ σ₂₂) × σ₂₁ ≈ᴹ σ₂₂)
mstep-eqv₂ (wk-cstate-result {K₂ = < x₂ ； γ >∷ K₂} x (wk-cstack-push π x₁ x₃ x₄)) return→ = _ , return→ , ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp (wk-cong π) x₁ (wk-menv-cong x x₃) x₄))
mstep-eqv₂ (wk-cstate-comp {M₂ = return W} π refl x₁ x₂) eval→ = _ , eval→ , ≈ᴹ-bc (≈-wk₂ (wk-cstate-result (eval-val-wk W x₁) x₂))
mstep-eqv₂ (wk-cstate-comp {M₂ = push M₂ M₃} π refl x₁ x₂) push→ = _ , push→ , ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp π refl x₁ (wk-cstack-push π refl x₁ x₂)))
mstep-eqv₂ (wk-cstate-comp {M₂ = sub M₂ M₃} π refl x₁ x₂) sub→ = _ , sub→ , ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp (wk-cong π) refl (wk-menv-cong (wk-jumpᵛ π refl x₁ x₂) x₁) x₂))
mstep-eqv₂ (wk-cstate-comp {M₂ = var (var i)} π refl x₁ x₂) var→ = _ , var→ , jump-wk i x₁
mstep-eqv₂ (wk-cstate-comp {M₂ = pm W M₂} {γ₁ = γ₁} {γ₂ = γ₂} π refl x₁ x₂) pmᶜ→ = _ , pmᶜ→ , ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp (Wk.wk-cong (Wk.wk-cong π)) refl (wk-menv-cong (eval₂-val-wk W x₁) (wk-menv-cong (eval₁-val-wk W x₁) x₁)) x₂))
mstep-eqv₂ (wk-cstate-comp {M₂ = app W₁ W₂} π refl ϖ x) app→ = _ , app→ , ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp (wk-cong (clo-to-comp-wk-cong W₁ ϖ)) (clo-to-comp-wk-eq W₁ ϖ) (wk-menv-cong (eval-val-wk W₂ ϖ) (clo-to-comp-wk-menv W₁ ϖ)) x))

mstep-eqv′ : {σ₁₁ σ₂₁ σ₁₂ : CState} → (σ₁₁ ≈₀ᴹ σ₁₂) → (σ₁₁ →ᶜ σ₂₁) → Σ[ σ₂₂ ∈ CState ] ((σ₁₂ →ᶜ σ₂₂) × σ₂₁ ≈ᴹ σ₂₂)
mstep-eqv′ (≈-wk₁ w) σ→σ′ = mstep-eqv₁ w σ→σ′
mstep-eqv′ (≈-wk₂ w) σ→σ′ = mstep-eqv₂ w σ→σ′

mstep-eqv : {σ₁₁ σ₂₁ σ₁₂ : CState} → (σ₁₁ ≈ᴹ σ₁₂) → (σ₁₁ →ᶜ σ₂₁) → Σ[ σ₂₂ ∈ CState ] ((σ₁₂ →ᶜ σ₂₂) × σ₂₁ ≈ᴹ σ₂₂)
mstep-eqv (≈ᴹ-bc (≈-wk₁ w)) σ→σ′ = mstep-eqv₁ w σ→σ′
mstep-eqv (≈ᴹ-bc (≈-wk₂ w)) σ→σ′ = mstep-eqv₂ w σ→σ′
mstep-eqv (≈-trans eqv₁ eqv₂) σ→σ′ =
  let
    IH₁ = mstep-eqv′ eqv₁ σ→σ′
    eqvIH₁ = proj₂ (proj₂ IH₁)
    σ→σIH₁ = proj₁ (proj₂ IH₁)
    IH₂ = mstep-eqv eqv₂ σ→σIH₁
    eqvIH₂ = proj₂ (proj₂ IH₂)
  in
  proj₁ IH₂ , proj₁ (proj₂ IH₂) , ≈ᴹ-trans eqvIH₁ eqvIH₂
