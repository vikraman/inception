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

      wk-pairᵛ : {𝐖₁₁ 𝐖₁₂ : MVal X} {𝐖₂₁ 𝐖₂₂ : MVal Y} → WkMVal 𝐖₁₁ 𝐖₁₂ → WkMVal 𝐖₂₁ 𝐖₂₂ → WkMVal (pairᵛ 𝐖₁₁ 𝐖₂₁) (pairᵛ 𝐖₁₂ 𝐖₂₂)

      wk-cloᵛ : {Γ Δ : Ctx} {M₁ : (Γ ∙ X) ⊢ᶜ Y} {M₂ : (Δ ∙ X) ⊢ᶜ Y} {γ : MEnv Γ} {δ : MEnv Δ} → (π : Γ ⊇ Δ) → M₁ ≡ wk-comp (wk-cong π) M₂ → (WkMEnv π γ δ) → WkMVal (cloᵛ M₁ γ) (cloᵛ M₂ δ)

      wk-jumpᵛ : {Γ Δ : Ctx} {M₁ : Γ ⊢ᶜ X} {M₂ : Δ ⊢ᶜ X} {γ : MEnv Γ} {δ : MEnv Δ} {K₁ K₂ : CStack X} → (π : Γ ⊇ Δ) → M₁ ≡ wk-comp π M₂ → (WkMEnv π γ δ) → (WkCStack K₁ K₂) → WkMVal (jumpᵛ M₁ γ K₁) (jumpᵛ M₂ δ K₂)

  data WkMEnv : {Γ Δ : Ctx} → (π : Wk Γ Δ) → (γ : MEnv Γ) → (δ : MEnv Δ) → Set where

      wk-menv-ε    : WkMEnv wk-ε ⋄ ⋄

      wk-menv-cong : {Γ Δ : Ctx} {π : Γ ⊇ Δ} {γ : MEnv Γ} {δ : MEnv Δ} {𝐖₁ : MVal X} {𝐖₂ : MVal X} → WkMVal 𝐖₁ 𝐖₂ → WkMEnv π γ δ → WkMEnv (wk-cong π) (γ · 𝐖₁) (δ · 𝐖₂)

      wk-menv-wk : {Γ Δ : Ctx} {π : Γ ⊇ Δ} {γ : MEnv Γ} {δ : MEnv Δ} → (𝐖 : MVal X) → WkMEnv π γ δ → WkMEnv (wk-wk π) (γ · 𝐖) δ

  data WkCStack : (K₁ : CStack X) → (K₂ : CStack X) → Set where

    wk-cstack-empty : WkCStack ◻ ◻

    wk-cstack-push : {Γ Δ : Ctx} {M₁ : (Γ ∙ Y) ⊢ᶜ X} {M₂ : (Δ ∙ Y) ⊢ᶜ X} {γ : MEnv Γ} {δ : MEnv Δ} {K₁ K₂ : CStack X}
                    → (π : Γ ⊇ Δ) → M₁ ≡ wk-comp (wk-cong π) M₂ → WkMEnv π γ δ → WkCStack K₁ K₂
                    → WkCStack (< M₁ ； γ >∷ K₁) (< M₂ ； δ >∷ K₂)

-- Weakening of Machine States
data WkCState : CState → CState → Set where

  wk-cstate-result : {𝐖₁ 𝐖₂ : MVal X} {K₁ K₂ : CStack X}
                     → WkMVal 𝐖₁ 𝐖₂ → WkCStack K₁ K₂
                     → WkCState ⟨ 𝐖₁ ╎ K₁ ⟩ ⟨ 𝐖₂ ╎ K₂ ⟩

  wk-cstate-comp : {Γ Δ : Ctx} {M₁ : Γ ⊢ᶜ X} {M₂ : Δ ⊢ᶜ X} {γ : MEnv Γ} {δ : MEnv Δ} {K₁ K₂ : CStack X}
                   → (π : Γ ⊇ Δ) → M₁ ≡ wk-comp π M₂ → (WkMEnv π γ δ) → WkCStack K₁ K₂
                   → WkCState ⟨ M₁ ╎ γ ╎ K₁ ⟩ ⟨ M₂ ╎ δ ╎ K₂ ⟩

data _≈₀ᴹ_ : CState → CState → Set where

    ≈-wk₁ : {σ₁ σ₂ : CState} → WkCState σ₁ σ₂ → σ₂ ≈₀ᴹ σ₁

    ≈-wk₂ : {σ₁ σ₂ : CState} → WkCState σ₁ σ₂ → σ₁ ≈₀ᴹ σ₂

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

  wk-menv-id : {γ : MEnv Γ} → WkMEnv wk-id γ γ
  wk-menv-id {γ = ⋄} = wk-menv-ε
  wk-menv-id {γ = γ · 𝐖} = wk-menv-cong wk-mval-id wk-menv-id

  wk-cstack-id : {K : CStack X} → WkCStack K K
  wk-cstack-id {K = ◻} = wk-cstack-empty
  wk-cstack-id {K = < x ； γ >∷ K} = wk-cstack-push wk-id refl wk-menv-id wk-cstack-id

mutual

  wk-MEnvᴹ-trans : {Γ Δ Γ₃ : Ctx} {π₁ : Γ ⊇ Δ} {π₂ : Δ ⊇ Γ₃} {γ : MEnv Γ} {δ : MEnv Δ} {γ₃ : MEnv Γ₃} → WkMEnv π₁ γ δ → WkMEnv π₂ δ γ₃ → WkMEnv (wk-trans π₁ π₂) γ γ₃
  wk-MEnvᴹ-trans wk-menv-ε wk-menv-ε = wk-menv-ε
  wk-MEnvᴹ-trans (wk-menv-cong x₁ ϖ₁) (wk-menv-cong x₂ ϖ₂) = wk-menv-cong (wk-mval-trans x₁ x₂) (wk-MEnvᴹ-trans ϖ₁ ϖ₂)
  wk-MEnvᴹ-trans (wk-menv-cong {𝐖₁ = 𝐖₁} _ ϖ₁) (wk-menv-wk 𝐖₂ ϖ₂) = wk-menv-wk 𝐖₁ (wk-MEnvᴹ-trans ϖ₁ ϖ₂)
  wk-MEnvᴹ-trans (wk-menv-wk 𝐖 ϖ) wk-menv-ε = wk-menv-wk 𝐖 ϖ
  wk-MEnvᴹ-trans (wk-menv-wk 𝐖₁ ϖ₁) (wk-menv-cong x ϖ₂) = wk-menv-wk 𝐖₁ (wk-MEnvᴹ-trans ϖ₁ (wk-menv-cong x ϖ₂))
  wk-MEnvᴹ-trans (wk-menv-wk 𝐖₁ ϖ₁) (wk-menv-wk 𝐖₂ ϖ₂) = wk-menv-wk 𝐖₁ (wk-MEnvᴹ-trans ϖ₁ (wk-menv-wk 𝐖₂ ϖ₂))

  wk-cstack-trans : {K₁ K₂ K₃ : CStack X} → WkCStack K₁ K₂ → WkCStack K₂ K₃ → WkCStack K₁ K₃
  wk-cstack-trans wk-cstack-empty wk-cstack-empty = wk-cstack-empty
  wk-cstack-trans (wk-cstack-push {M₁ = M₁₁} {M₂ = M₂₁} π eq₁ ϖ₁ x₁) (wk-cstack-push {M₁ = M₁₂} {M₂ = M₂₂} ρ eq₂ ϖ₂ x₂) =
                        wk-cstack-push
                          (wk-trans π ρ)
                          (M₁₁ ≡⟨ eq₁ ⟩ wk-comp (wk-cong π) M₂₁ ≡⟨ cong (wk-comp (wk-cong π)) eq₂ ⟩ wk-comp (wk-cong (wk-trans π ρ)) M₂₂ ∎)
                          (wk-MEnvᴹ-trans ϖ₁ ϖ₂)
                          (wk-cstack-trans x₁ x₂)

  wk-mval-trans : {𝐖₁ 𝐖₂ 𝐖₃ : MVal X} → WkMVal 𝐖₁ 𝐖₂ → WkMVal 𝐖₂ 𝐖₃ → WkMVal 𝐖₁ 𝐖₃
  wk-mval-trans wk-unitᵛ wk-unitᵛ = wk-unitᵛ
  wk-mval-trans (wk-pairᵛ w₁ w₂) (wk-pairᵛ w₃ w₄) = wk-pairᵛ (wk-mval-trans w₁ w₃) (wk-mval-trans w₂ w₄)
  wk-mval-trans (wk-cloᵛ {M₁ = M₁₁} {M₂ = M₂₁} π eq₁ x₁) (wk-cloᵛ {M₁ = M₁₂} {M₂ = M₂₂} ρ eq₂ x₂) =
                        wk-cloᵛ
                          (wk-trans π ρ)
                          (M₁₁
                            ≡⟨ eq₁ ⟩
                            wk-comp (wk-cong π) M₂₁
                            ≡⟨ cong (wk-comp (wk-cong π)) eq₂ ⟩
                            wk-comp (wk-cong π) (wk-comp (wk-cong ρ) M₂₂)
                            ≡⟨ wk-comp-wk-η M₂₂ (wk-cong π) (wk-cong ρ) ⟩
                            wk-comp (wk-cong (wk-trans π ρ)) M₂₂ ∎)
                          (wk-MEnvᴹ-trans x₁ x₂)
  wk-mval-trans (wk-jumpᵛ {M₁ = M₁₁} {M₂ = M₂₁} π eq₁ x₁ y₁) (wk-jumpᵛ {M₁ = M₁₂} {M₂ = M₂₂} ρ eq₂ x₂ y₂) =
                        wk-jumpᵛ
                          (wk-trans π ρ)
                          (M₁₁ ≡⟨ eq₁ ⟩ wk-comp π M₂₁ ≡⟨ cong (wk-comp π) eq₂ ⟩ wk-comp (wk-trans π ρ) M₂₂ ∎)
                          (wk-MEnvᴹ-trans x₁ x₂)
                          (wk-cstack-trans y₁ y₂)

wk-cstate-trans : {σ₁ σ₂ σ₃ : CState} → WkCState σ₁ σ₂ → WkCState σ₂ σ₃ → WkCState σ₁ σ₃
wk-cstate-trans (wk-cstate-result ϖ₁ x₁) (wk-cstate-result ϖ₂ x₂) = wk-cstate-result (wk-mval-trans ϖ₁ ϖ₂) (wk-cstack-trans x₁ x₂)
wk-cstate-trans (wk-cstate-comp {M₁ = M₁₁} {M₂ = M₂₁} π eq₁ ϖ₁ x₁) (wk-cstate-comp {M₁ = M₁₂} {M₂ = M₂₂} ρ eq₂ ϖ₂ x₂) =
                        wk-cstate-comp
                          (wk-trans π ρ)
                          (M₁₁ ≡⟨ eq₁ ⟩ wk-comp π M₂₁ ≡⟨ cong (wk-comp π) eq₂ ⟩ wk-comp (wk-trans π ρ) M₂₂ ∎)
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
  ≈ᴹ-trans (≈ᴹ-bc x) (≈-trans x₁ s) = ≈-trans x (≈-trans x₁ s)
  ≈ᴹ-trans (≈-trans x s) (≈ᴹ-bc x₁) = ≈-trans x (≈ᴹ-trans s (≈ᴹ-bc x₁))
  ≈ᴹ-trans (≈-trans x s₁) (≈-trans x₁ s₂) = ≈-trans x (≈ᴹ-trans s₁ (≈-trans x₁ s₂))

proj₁-wk-mval : {𝐖 𝐕 : MVal (X `× Y)} → WkMVal 𝐖 𝐕 → WkMVal (proj₁-val 𝐖) (proj₁-val 𝐕)
proj₁-wk-mval (wk-pairᵛ wm₁ wm₂) = wm₁

proj₂-wk-mval : {𝐖 𝐕 : MVal (X `× Y)} → WkMVal 𝐖 𝐕 → WkMVal (proj₂-val 𝐖) (proj₂-val 𝐕)
proj₂-wk-mval (wk-pairᵛ wm₁ wm₂) = wm₂

jump-wk : {Γ Δ : Ctx} {γ : MEnv Γ} {δ : MEnv Δ} {π : Γ ⊇ Δ} → (i : Δ ∋ `ℓ) → (WkMEnv π γ δ) → eval-jump (var (wk-mem π i)) γ ≈ᴹ eval-jump (var i) δ
jump-wk here (wk-menv-cong (wk-jumpᵛ π x x₁ x₂) ϖ) = ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp π x x₁ x₂))
jump-wk here (wk-menv-wk 𝐖 ϖ) = jump-wk here ϖ
jump-wk (there i) (wk-menv-cong x ϖ) = jump-wk i ϖ
jump-wk (there i) (wk-menv-wk 𝐖 ϖ) = jump-wk (there i) ϖ

eval-mem-wk : {Γ Δ : Ctx} {γ : MEnv Γ} {δ : MEnv Δ} {π : Γ ⊇ Δ} → (i : Δ ∋ X) → (WkMEnv π γ δ) → WkMVal (eval (var (wk-mem π i)) γ) (eval (var i) δ)
eval-mem-wk here (wk-menv-cong x ϖ) = x
eval-mem-wk here (wk-menv-wk 𝐖 ϖ) = eval-mem-wk here ϖ
eval-mem-wk (there i) (wk-menv-cong x ϖ) = eval-mem-wk i ϖ
eval-mem-wk (there i) (wk-menv-wk 𝐖 ϖ) = eval-mem-wk (there i) ϖ

eval-val-wk : {Γ Δ : Ctx} {γ : MEnv Γ} {δ : MEnv Δ} {π : Γ ⊇ Δ} → (W : Δ ⊢ᵛ X) → (WkMEnv π γ δ) → WkMVal (eval (wk-val π W) γ) (eval W δ)
eval-val-wk (var i) (wk-menv-cong x ϖ) = eval-mem-wk i (wk-menv-cong x ϖ)
eval-val-wk (var i) (wk-menv-wk 𝐖 ϖ) = eval-mem-wk i ϖ
eval-val-wk (lam M) wk-menv-ε = wk-cloᵛ wk-ε refl wk-menv-ε
eval-val-wk (lam M) (wk-menv-cong x ϖ) = wk-cloᵛ (wk-cong _) refl (wk-menv-cong x ϖ)
eval-val-wk (lam M) (wk-menv-wk 𝐖 ϖ) = wk-cloᵛ (wk-wk _) refl (wk-menv-wk 𝐖 ϖ)
eval-val-wk (pair V W) wk-menv-ε = wk-pairᵛ (eval-val-wk V wk-menv-ε) (eval-val-wk W wk-menv-ε)
eval-val-wk (pair V W) (wk-menv-cong x ϖ) = wk-pairᵛ (eval-val-wk V (wk-menv-cong x ϖ)) (eval-val-wk W (wk-menv-cong x ϖ))
eval-val-wk (pair V W) (wk-menv-wk 𝐖 ϖ) = wk-pairᵛ (eval-val-wk V (wk-menv-wk 𝐖 ϖ)) (eval-val-wk W (wk-menv-wk 𝐖 ϖ))
eval-val-wk unit wk-menv-ε = wk-unitᵛ
eval-val-wk unit (wk-menv-cong x ϖ) = wk-unitᵛ
eval-val-wk unit (wk-menv-wk 𝐖 ϖ) = wk-unitᵛ

eval₁-mem-wk : {Γ Δ : Ctx} {γ : MEnv Γ} {δ : MEnv Δ} {π : Γ ⊇ Δ} → (i : Δ ∋ (X `× Y)) → (WkMEnv π γ δ) → WkMVal (eval₁ (var (wk-mem π i)) γ) (eval₁ (var i) δ)
eval₁-mem-wk here (wk-menv-cong x ϖ) = proj₁-wk-mval x
eval₁-mem-wk here (wk-menv-wk 𝐖 ϖ) = eval₁-mem-wk here ϖ
eval₁-mem-wk (there i) (wk-menv-cong x ϖ) = eval₁-mem-wk i ϖ
eval₁-mem-wk (there i) (wk-menv-wk 𝐖 ϖ) = eval₁-mem-wk (there i) ϖ

eval₁-val-wk : {Γ Δ : Ctx} {γ : MEnv Γ} {δ : MEnv Δ} {π : Γ ⊇ Δ} → (W : Δ ⊢ᵛ (X `× Y)) → (WkMEnv π γ δ) → WkMVal (eval₁ (wk-val π W) γ) (eval₁ W δ)
eval₁-val-wk (var i) (wk-menv-cong x ϖ) = eval₁-mem-wk i (wk-menv-cong x ϖ)
eval₁-val-wk (var i) (wk-menv-wk 𝐖 ϖ) = eval₁-mem-wk i ϖ
eval₁-val-wk (pair V W) wk-menv-ε = wk-mval-id
eval₁-val-wk {γ = γ · 𝐖₁} {δ = δ · 𝐖₂} {π = wk-cong π} (pair V W) (wk-menv-cong x ϖ) =
  let
    goal : WkMVal (eval (wk-val (Wk.wk-cong π) V) (γ · 𝐖₁)) (eval V (δ · 𝐖₂))
    goal = eval-val-wk V (wk-menv-cong x ϖ)
  in
  goal
eval₁-val-wk (pair V W) (wk-menv-wk 𝐖 ϖ) = eval-val-wk V (wk-menv-wk 𝐖 ϖ)

eval₂-mem-wk : {Γ Δ : Ctx} {γ : MEnv Γ} {δ : MEnv Δ} {π : Γ ⊇ Δ} → (i : Δ ∋ (X `× Y)) → (WkMEnv π γ δ) → WkMVal (eval₂ (var (wk-mem π i)) γ) (eval₂ (var i) δ)
eval₂-mem-wk here (wk-menv-cong x ϖ) = proj₂-wk-mval x
eval₂-mem-wk here (wk-menv-wk 𝐖 ϖ) = eval₂-mem-wk here ϖ
eval₂-mem-wk (there i) (wk-menv-cong x ϖ) = eval₂-mem-wk i ϖ
eval₂-mem-wk (there i) (wk-menv-wk 𝐖 ϖ) = eval₂-mem-wk (there i) ϖ

eval₂-val-wk : {Γ Δ : Ctx} {γ : MEnv Γ} {δ : MEnv Δ} {π : Γ ⊇ Δ} → (W : Δ ⊢ᵛ (X `× Y)) → (WkMEnv π γ δ) → WkMVal (eval₂ (wk-val π W) γ) (eval₂ W δ)
eval₂-val-wk (var i) (wk-menv-cong x ϖ) = eval₂-mem-wk i (wk-menv-cong x ϖ)
eval₂-val-wk (var i) (wk-menv-wk 𝐖 ϖ) = eval₂-mem-wk i ϖ
eval₂-val-wk (pair V W) wk-menv-ε = wk-mval-id
eval₂-val-wk (pair V W) (wk-menv-cong x ϖ) = eval-val-wk W (wk-menv-cong x ϖ)
eval₂-val-wk (pair V W) (wk-menv-wk 𝐖 ϖ) = eval-val-wk W (wk-menv-wk 𝐖 ϖ)

clo-to-comp-wk-proj₁ : {𝐖₁ 𝐖₂ : MVal (X `⇒ Y)} → WkMVal 𝐖₁ 𝐖₂ → (proj₁ (clo-to-comp 𝐖₁)) ⊇ (proj₁ (clo-to-comp 𝐖₂))
clo-to-comp-wk-proj₁ (wk-cloᵛ π x x₁) = π

clo-to-comp-wk-mem-cong : {Γ Δ : Ctx} {π : Γ ⊇ Δ} {γ : MEnv Γ} {δ : MEnv Δ} → (i : Δ ∋ (X `⇒ Y)) → (ϖ : WkMEnv π γ δ) → (proj₁ (clo-to-comp (eval (var (wk-mem π i)) γ))) ⊇ (proj₁ (clo-to-comp (eval (var i) δ)))
clo-to-comp-wk-mem-cong {π = wk-ε} {γ = ⋄} {δ = ⋄} () ϖ
clo-to-comp-wk-mem-cong {π = wk-cong π} {γ = γ · 𝐖₁} {δ = δ · 𝐖₂} here (wk-menv-cong x ϖ) = clo-to-comp-wk-proj₁ x
clo-to-comp-wk-mem-cong {π = wk-cong π} {γ = γ · x} {δ = δ · x₁} (there i) (wk-menv-cong x₂ ϖ) = clo-to-comp-wk-mem-cong i ϖ
clo-to-comp-wk-mem-cong {π = wk-wk π} {γ = γ · x} {δ = ⋄} () ϖ
clo-to-comp-wk-mem-cong {π = wk-wk π} {γ = γ · x} {δ = δ · x₁} here (wk-menv-wk 𝐖 ϖ) = clo-to-comp-wk-mem-cong here ϖ
clo-to-comp-wk-mem-cong {π = wk-wk π} {γ = γ · x} {δ = δ · x₁} (there i) (wk-menv-wk 𝐖 ϖ) = clo-to-comp-wk-mem-cong (there i) ϖ

clo-to-comp-wk-cong : {Γ Δ : Ctx} {π : Γ ⊇ Δ} {γ : MEnv Γ} {δ : MEnv Δ} → (W : Δ ⊢ᵛ (X `⇒ Y)) → (ϖ : WkMEnv π γ δ) → (proj₁ (clo-to-comp (eval (wk-val π W) γ))) ⊇ (proj₁ (clo-to-comp (eval W δ)))
clo-to-comp-wk-cong {π = wk-cong π} (var i) (wk-menv-cong x ϖ) = clo-to-comp-wk-mem-cong i (wk-menv-cong x ϖ)
clo-to-comp-wk-cong {π = wk-wk π} (var i) (wk-menv-wk 𝐖 ϖ) = clo-to-comp-wk-mem-cong i ϖ
clo-to-comp-wk-cong {π = wk-ε} (lam M) wk-menv-ε = Wk.wk-ε
clo-to-comp-wk-cong {π = wk-cong π} (lam M) (wk-menv-cong _ ϖ) = Wk.wk-cong π
clo-to-comp-wk-cong {π = wk-wk π} (lam M) (wk-menv-wk 𝐖 ϖ) = Wk.wk-wk π

clo-to-comp-wk-proj₁-proj₂ : {𝐖₁ 𝐖₂ : MVal (X `⇒ Y)} → (w : WkMVal 𝐖₁ 𝐖₂) → proj₁ (proj₂ (clo-to-comp 𝐖₁)) ≡ wk-comp (Wk.wk-cong (clo-to-comp-wk-proj₁ w)) (proj₁ (proj₂ (clo-to-comp 𝐖₂)))
clo-to-comp-wk-proj₁-proj₂ (wk-cloᵛ π x x₁) = x

clo-to-comp-wk-proj₂-proj₂ : {𝐖₁ 𝐖₂ : MVal (X `⇒ Y)} → (w : WkMVal 𝐖₁ 𝐖₂) → WkMEnv (clo-to-comp-wk-proj₁ w) (proj₂ (proj₂ (clo-to-comp 𝐖₁))) (proj₂ (proj₂ (clo-to-comp 𝐖₂)))
clo-to-comp-wk-proj₂-proj₂ (wk-cloᵛ π x x₁) = x₁

cc-wk-eq : {Γ Δ : Ctx} {π : Γ ⊇ Δ} {γ : MEnv Γ} {δ : MEnv Δ} {𝐖 : MVal Z} → (i : Δ ∋ (X `⇒ Y)) → (ϖ : WkMEnv π γ δ) → clo-to-comp-wk-mem-cong i ϖ ≡ clo-to-comp-wk-mem-cong i (wk-menv-wk 𝐖 ϖ)
cc-wk-eq {π = wk-ε} {γ = ⋄} {δ = ⋄} () ϖ
cc-wk-eq {π = wk-cong π} {γ = γ · x} {δ = δ · x₁} here (wk-menv-cong x₂ ϖ) = refl
cc-wk-eq {π = wk-cong π} {γ = γ · x} {δ = δ · x₁} (there i) (wk-menv-cong x₂ ϖ) = refl
cc-wk-eq {π = wk-wk π} {γ = γ · x} {δ = ⋄} () ϖ
cc-wk-eq {π = wk-wk π} {γ = γ · x} {δ = δ · x₁} here (wk-menv-wk 𝐖 ϖ) = refl
cc-wk-eq {π = wk-wk π} {γ = γ · x} {δ = δ · x₁} (there i) (wk-menv-wk 𝐖 ϖ) = refl

cc-eq-eq : {Γ Δ : Ctx} {π : Γ ⊇ Δ} {γ : MEnv Γ} {δ : MEnv Δ} → (i : Δ ∋ (X `⇒ Y)) → (ϖ : WkMEnv π γ δ) → clo-to-comp-wk-cong (var i) ϖ ≡ clo-to-comp-wk-mem-cong i ϖ
cc-eq-eq here (wk-menv-cong x ϖ) = refl
cc-eq-eq here (wk-menv-wk 𝐖 ϖ) = cc-wk-eq {𝐖 = 𝐖} here ϖ
cc-eq-eq (there i) (wk-menv-cong x ϖ) = refl
cc-eq-eq (there i) (wk-menv-wk 𝐖 ϖ) = cc-wk-eq {𝐖 = 𝐖} (there i) ϖ

clo-to-comp-wk-mem-eq : {Γ Δ : Ctx} {π : Γ ⊇ Δ} {γ : MEnv Γ} {δ : MEnv Δ} → (i : Δ ∋ (X `⇒ Y)) → (ϖ : WkMEnv π γ δ) → proj₁ (proj₂ (clo-to-comp (eval (var (wk-mem π i)) γ))) ≡ wk-comp (wk-cong (clo-to-comp-wk-cong (var i) ϖ)) (proj₁ (proj₂ (clo-to-comp (eval (var i) δ))))
clo-to-comp-wk-mem-eq {π = wk-ε} {γ = ⋄} {δ = ⋄} () ϖ
clo-to-comp-wk-mem-eq {π = wk-cong π} {γ = γ · 𝐖₁} {δ = δ · 𝐖₂} here (wk-menv-cong w ϖ) = clo-to-comp-wk-proj₁-proj₂ w
clo-to-comp-wk-mem-eq {π = wk-cong π} {γ = γ · x} {δ = δ · _} (there i) (wk-menv-cong _ ϖ) =
  let
    a : proj₁ (proj₂ (clo-to-comp (lookup (wk-mem π i) γ))) ≡ wk-comp (wk-cong (clo-to-comp-wk-cong (var i) ϖ)) (proj₁ (proj₂ (clo-to-comp (lookup i δ))))
    a = clo-to-comp-wk-mem-eq i ϖ

    goal : proj₁ (proj₂ (clo-to-comp (lookup (wk-mem π i) γ))) ≡ wk-comp (wk-cong (clo-to-comp-wk-mem-cong i ϖ)) (proj₁ (proj₂ (clo-to-comp (lookup i δ))))
    goal = subst (λ z → proj₁ (proj₂ (clo-to-comp (lookup (wk-mem π i) γ))) ≡ wk-comp (wk-cong z) (proj₁ (proj₂ (clo-to-comp (lookup i δ))))) (cc-eq-eq i ϖ) a
  in
  goal
clo-to-comp-wk-mem-eq {π = wk-wk π} {γ = γ · x} {δ = ⋄} () ϖ
clo-to-comp-wk-mem-eq {π = wk-wk π} {γ = γ · x} {δ = δ · x₁} here (wk-menv-wk 𝐖 ϖ) =
  let
    a : proj₁ (proj₂ (clo-to-comp (lookup (wk-mem π here) γ))) ≡ wk-comp (wk-cong (clo-to-comp-wk-cong (var here) ϖ)) (proj₁ (proj₂ (clo-to-comp x₁)))
    a = clo-to-comp-wk-mem-eq here ϖ

    goal : proj₁ (proj₂ (clo-to-comp (lookup (wk-mem π here) γ))) ≡ wk-comp (wk-cong (clo-to-comp-wk-mem-cong here ϖ)) (proj₁ (proj₂ (clo-to-comp x₁)))
    goal = subst (λ z → proj₁ (proj₂ (clo-to-comp (lookup (wk-mem π here) γ))) ≡ wk-comp (wk-cong z) (proj₁ (proj₂ (clo-to-comp x₁)))) (cc-eq-eq here ϖ) a
  in
  goal
clo-to-comp-wk-mem-eq {π = wk-wk π} {γ = γ · x} {δ = δ · x₁} (there i) (wk-menv-wk 𝐖 ϖ) =
  let
    a : proj₁ (proj₂ (clo-to-comp (eval (var (wk-mem π (there i))) γ))) ≡ wk-comp (wk-cong (clo-to-comp-wk-cong (var (there i)) ϖ)) (proj₁ (proj₂ (clo-to-comp (lookup i δ))))
    a = clo-to-comp-wk-mem-eq (there i) ϖ

    goal : proj₁ (proj₂ (clo-to-comp (lookup (wk-mem π (_∋_.there i)) γ))) ≡ wk-comp (Wk.wk-cong (clo-to-comp-wk-mem-cong (_∋_.there i) ϖ)) (proj₁ (proj₂ (clo-to-comp (lookup i δ))))
    goal = subst (λ z → proj₁ (proj₂ (clo-to-comp (lookup (wk-mem π (_∋_.there i)) γ))) ≡ wk-comp (Wk.wk-cong z) (proj₁ (proj₂ (clo-to-comp (lookup i δ))))) (cc-eq-eq (there i) ϖ) a
  in
  goal

clo-to-comp-wk-eq : {Γ Δ : Ctx} {π : Γ ⊇ Δ} {γ : MEnv Γ} {δ : MEnv Δ} → (W : Δ ⊢ᵛ (X `⇒ Y)) → (ϖ : WkMEnv π γ δ) → proj₁ (proj₂ (clo-to-comp (eval (wk-val π W) γ))) ≡ wk-comp (wk-cong (clo-to-comp-wk-cong W ϖ)) (proj₁ (proj₂ (clo-to-comp (eval W δ))))
clo-to-comp-wk-eq {π = wk-cong π} (var i) (wk-menv-cong x ϖ) = clo-to-comp-wk-mem-eq i (wk-menv-cong x ϖ)
clo-to-comp-wk-eq {π = wk-wk π} (var i) (wk-menv-wk 𝐖 ϖ) = clo-to-comp-wk-mem-eq i (wk-menv-wk 𝐖 ϖ)
clo-to-comp-wk-eq {π = wk-ε} (lam M) wk-menv-ε = refl
clo-to-comp-wk-eq {π = wk-cong π} (lam M) (wk-menv-cong _ ϖ) = refl
clo-to-comp-wk-eq {π = wk-wk π} (lam M) (wk-menv-wk 𝐖 ϖ) = refl

clo-to-comp-mem-wk-menv : {Γ Δ : Ctx} {π : Γ ⊇ Δ} {γ : MEnv Γ} {δ : MEnv Δ} → (i : Δ ∋ (X `⇒ Y)) → (ϖ : WkMEnv π γ δ) → WkMEnv (clo-to-comp-wk-cong (var i) ϖ) (proj₂ (proj₂ (clo-to-comp (eval (var (wk-mem π i)) γ)))) (proj₂ (proj₂ (clo-to-comp (eval (var i) δ))))
clo-to-comp-mem-wk-menv {π = wk-ε} {γ = ⋄} {δ = ⋄} () ϖ
clo-to-comp-mem-wk-menv {π = wk-cong π} {γ = γ · 𝐖₁} {δ = δ · 𝐖₂} here (wk-menv-cong w ϖ) =
  let
    goal : WkMEnv (clo-to-comp-wk-proj₁ w) (proj₂ (proj₂ (clo-to-comp 𝐖₁))) (proj₂ (proj₂ (clo-to-comp 𝐖₂)))
    goal = clo-to-comp-wk-proj₂-proj₂ w
  in
  goal
clo-to-comp-mem-wk-menv {π = wk-cong π} {γ = γ · 𝐖₁} {δ = δ · 𝐖₂} (there i) (wk-menv-cong _ ϖ) =
  let
    a : WkMEnv (clo-to-comp-wk-cong (var i) ϖ) (proj₂ (proj₂ (clo-to-comp (lookup (wk-mem π i) γ)))) (proj₂ (proj₂ (clo-to-comp (lookup i δ))))
    a = clo-to-comp-mem-wk-menv i ϖ

    goal : WkMEnv (clo-to-comp-wk-mem-cong i ϖ) (proj₂ (proj₂ (clo-to-comp (lookup (wk-mem π i) γ)))) (proj₂ (proj₂ (clo-to-comp (lookup i δ))))
    goal = subst (λ z → WkMEnv z (proj₂ (proj₂ (clo-to-comp (lookup (wk-mem π i) γ)))) (proj₂ (proj₂ (clo-to-comp (lookup i δ))))) (cc-eq-eq i ϖ) a
  in
  goal
clo-to-comp-mem-wk-menv {π = wk-wk π} {γ = γ · x} {δ = ⋄} () ϖ
clo-to-comp-mem-wk-menv {π = wk-wk π} {γ = γ · x} {δ = δ · x₁} here (wk-menv-wk 𝐖 ϖ) =
  let
    a : WkMEnv (clo-to-comp-wk-cong (var here) ϖ) (proj₂ (proj₂ (clo-to-comp (eval (var (wk-mem π here)) γ)))) (proj₂ (proj₂ (clo-to-comp (eval (var here) (δ · x₁)))))
    a = clo-to-comp-mem-wk-menv here ϖ

    goal : WkMEnv (clo-to-comp-wk-mem-cong _∋_.here ϖ) (proj₂ (proj₂ (clo-to-comp (lookup (wk-mem π _∋_.here) γ)))) (proj₂ (proj₂ (clo-to-comp x₁)))
    goal = subst (λ z → WkMEnv z (proj₂ (proj₂ (clo-to-comp (eval (var (wk-mem π here)) γ)))) (proj₂ (proj₂ (clo-to-comp (eval (var here) (δ · x₁)))))) (cc-eq-eq _∋_.here ϖ) a
  in
  goal
clo-to-comp-mem-wk-menv {π = wk-wk π} {γ = γ · x} {δ = δ · x₁} (there i) (wk-menv-wk 𝐖 ϖ) =
  let
    a : WkMEnv (clo-to-comp-wk-cong (var (there i)) ϖ) (proj₂ (proj₂ (clo-to-comp (eval (var (wk-mem π (there i))) γ)))) (proj₂ (proj₂ (clo-to-comp (eval (var (there i)) (δ · x₁)))))
    a = clo-to-comp-mem-wk-menv (there i) ϖ

    goal : WkMEnv (clo-to-comp-wk-mem-cong (_∋_.there i) ϖ) (proj₂ (proj₂ (clo-to-comp (lookup (wk-mem π (_∋_.there i)) γ)))) (proj₂ (proj₂ (clo-to-comp (lookup i δ))))
    goal = subst (λ z → WkMEnv z (proj₂ (proj₂ (clo-to-comp (eval (var (wk-mem π (there i))) γ)))) (proj₂ (proj₂ (clo-to-comp (eval (var (there i)) (δ · x₁)))))) (cc-eq-eq (there i) ϖ) a
  in
  goal

clo-to-comp-wk-menv : {Γ Δ : Ctx} {π : Γ ⊇ Δ} {γ : MEnv Γ} {δ : MEnv Δ} → (W : Δ ⊢ᵛ (X `⇒ Y)) → (ϖ : WkMEnv π γ δ) → WkMEnv (clo-to-comp-wk-cong W ϖ) (proj₂ (proj₂ (clo-to-comp (eval (wk-val π W) γ)))) (proj₂ (proj₂ (clo-to-comp (eval W δ))))
clo-to-comp-wk-menv (var i) (wk-menv-cong x ϖ) = clo-to-comp-mem-wk-menv i (wk-menv-cong x ϖ)
clo-to-comp-wk-menv (var i) (wk-menv-wk 𝐖 ϖ) = clo-to-comp-mem-wk-menv i (wk-menv-wk 𝐖 ϖ)
clo-to-comp-wk-menv (lam M) wk-menv-ε = wk-menv-ε
clo-to-comp-wk-menv (lam M) (wk-menv-cong x ϖ) = wk-menv-cong x ϖ
clo-to-comp-wk-menv (lam M) (wk-menv-wk 𝐖 ϖ) = wk-menv-wk 𝐖 ϖ

mstep-eqv₁ : {σ₁₁ σ₂₁ σ₁₂ : CState} → (WkCState σ₁₂ σ₁₁) → (σ₁₁ →ᶜ σ₂₁) → Σ[ σ₂₂ ∈ CState ] ((σ₁₂ →ᶜ σ₂₂) × σ₂₁ ≈ᴹ σ₂₂)
mstep-eqv₁ (wk-cstate-result {K₁ = < x₂ ； γ >∷ K₁} x (wk-cstack-push π x₁ x₃ x₄)) return→ = _ , return→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp (wk-cong π) x₁ (wk-menv-cong x x₃) x₄))
mstep-eqv₁ (wk-cstate-comp {M₁ = return V} {M₂ = return W} π refl x₁ x₂) eval→ = _ , eval→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-result (eval-val-wk W x₁) x₂))
mstep-eqv₁ (wk-cstate-comp {M₁ = push M₁ M₂} π refl x₁ x₂) push→ = _ , push→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp π refl x₁ (wk-cstack-push π refl x₁ x₂)))
mstep-eqv₁ (wk-cstate-comp {M₁ = sub M₁ M₂} π refl x₁ x₂) sub→ = _ , sub→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp (Wk.wk-cong π) refl (wk-menv-cong (wk-jumpᵛ π refl x₁ x₂) x₁) x₂))
mstep-eqv₁ (wk-cstate-comp {M₁ = var (var i₁)} {M₂ = var (var i)} π refl x₁ x₂) var→ = _ , var→ , ≈ᴹ-sym (jump-wk i x₁)
mstep-eqv₁ (wk-cstate-comp {M₁ = pm x₃ M₁} {M₂ = pm W M₂} π refl x₁ x₂) pmᶜ→ = _ , pmᶜ→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp (Wk.wk-cong (Wk.wk-cong π)) refl (wk-menv-cong (eval₂-val-wk W x₁) (wk-menv-cong (eval₁-val-wk W x₁) x₁)) x₂))
mstep-eqv₁ (wk-cstate-comp {M₁ = app x₃ x₄} {M₂ = app x₅ x₆} π refl x₁ x₂) app→ = _ , app→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp (wk-cong (clo-to-comp-wk-cong x₅ x₁)) (clo-to-comp-wk-eq x₅ x₁) (wk-menv-cong (eval-val-wk x₆ x₁) (clo-to-comp-wk-menv x₅ x₁)) x₂))

mstep-eqv₂ : {σ₁₁ σ₂₁ σ₁₂ : CState} → (WkCState σ₁₁ σ₁₂) → (σ₁₁ →ᶜ σ₂₁) → Σ[ σ₂₂ ∈ CState ] ((σ₁₂ →ᶜ σ₂₂) × σ₂₁ ≈ᴹ σ₂₂)
mstep-eqv₂ (wk-cstate-result {K₂ = < x₂ ； γ >∷ K₂} x (wk-cstack-push π x₁ x₃ x₄)) return→ = _ , return→ , ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp (wk-cong π) x₁ (wk-menv-cong x x₃) x₄))
mstep-eqv₂ (wk-cstate-comp {M₂ = return W} π refl x₁ x₂) eval→ = _ , eval→ , ≈ᴹ-bc (≈-wk₂ (wk-cstate-result (eval-val-wk W x₁) x₂))
mstep-eqv₂ (wk-cstate-comp {M₂ = push M₂ M₃} π refl x₁ x₂) push→ = _ , push→ , ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp π refl x₁ (wk-cstack-push π refl x₁ x₂)))
mstep-eqv₂ (wk-cstate-comp {M₂ = sub M₂ M₃} π refl x₁ x₂) sub→ = _ , sub→ , ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp (wk-cong π) refl (wk-menv-cong (wk-jumpᵛ π refl x₁ x₂) x₁) x₂))
mstep-eqv₂ (wk-cstate-comp {M₂ = var (var i)} π refl x₁ x₂) var→ = _ , var→ , jump-wk i x₁
mstep-eqv₂ (wk-cstate-comp {M₂ = pm W M₂} {γ = γ} {δ = δ} π refl x₁ x₂) pmᶜ→ = _ , pmᶜ→ , ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp (Wk.wk-cong (Wk.wk-cong π)) refl (wk-menv-cong (eval₂-val-wk W x₁) (wk-menv-cong (eval₁-val-wk W x₁) x₁)) x₂))
mstep-eqv₂ (wk-cstate-comp {M₂ = app V W} π refl ϖ x) app→ = _ , app→ , ≈ᴹ-bc (≈-wk₂ (wk-cstate-comp (wk-cong (clo-to-comp-wk-cong V ϖ)) (clo-to-comp-wk-eq V ϖ) (wk-menv-cong (eval-val-wk W ϖ) (clo-to-comp-wk-menv V ϖ)) x))

mstep-eqv₀ : {σ₁₁ σ₂₁ σ₁₂ : CState} → (σ₁₁ ≈₀ᴹ σ₁₂) → (σ₁₁ →ᶜ σ₂₁) → Σ[ σ₂₂ ∈ CState ] ((σ₁₂ →ᶜ σ₂₂) × σ₂₁ ≈ᴹ σ₂₂)
mstep-eqv₀ (≈-wk₁ w) σ→σ′ = mstep-eqv₁ w σ→σ′
mstep-eqv₀ (≈-wk₂ w) σ→σ′ = mstep-eqv₂ w σ→σ′

mstep-eqv : {σ₁₁ σ₂₁ σ₁₂ : CState} → (σ₁₁ ≈ᴹ σ₁₂) → (σ₁₁ →ᶜ σ₂₁) → Σ[ σ₂₂ ∈ CState ] ((σ₁₂ →ᶜ σ₂₂) × σ₂₁ ≈ᴹ σ₂₂)
mstep-eqv (≈ᴹ-bc (≈-wk₁ w)) σ→σ′ = mstep-eqv₁ w σ→σ′
mstep-eqv (≈ᴹ-bc (≈-wk₂ w)) σ→σ′ = mstep-eqv₂ w σ→σ′
mstep-eqv (≈-trans eqv₁ eqv₂) σ→σ′ =
  let
    IH₁ = mstep-eqv₀ eqv₁ σ→σ′
    eqvIH₁ = proj₂ (proj₂ IH₁)
    σ→σIH₁ = proj₁ (proj₂ IH₁)
    IH₂ = mstep-eqv eqv₂ σ→σIH₁
    eqvIH₂ = proj₂ (proj₂ IH₂)
  in
  proj₁ IH₂ , proj₁ (proj₂ IH₂) , ≈ᴹ-trans eqvIH₁ eqvIH₂
