{-# OPTIONS --no-postfix-projections #-}

open import Inception.Sub.Syntax using (Ty)

module Inception.Sub.Simulation (ℛ : Ty) where

open import Inception.Sub.Syntax
open import Inception.Prelude

open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; subst; cong; cong₂)
open Eq.≡-Reasoning using (step-≡-⟩; step-≡-∣; step-≡-⟨; _∎; step-≡)

import Inception.Sub.Machine ℛ as M
import Inception.Sub.TelescopeMachine ℛ as TM
open M using (⟨_╎_⟩; ⟨_╎_╎_⟩; _·_; ◻; <_；_>∷_; ⋄; eval→; return→; push→; sub→; var→; pmᶜ→; app→; progress) renaming (_→ᶜ_ to _→ᴹ_)
open TM using (⟨_；_╎_╎_⟩; ⟨_╎_╎_╎_⟩; <_；_；_>∷_; _·_; eval→; return→; push→; sub→; var→; pmᶜ→; app→; label) renaming (_→ᶜ_ to _→ᵀᴹ_)
--open TM using (⟨_；_╎_╎_⟩; ⟨_╎_╎_╎_⟩) renaming (_→ᶜ_ to _→ᵀᴹ_; eval→ to eval→ᵀᴹ; return→ to return→ᵀᴹ; push→ to push→ᵀᴹ; sub→ to sub→ᵀᴹ; var→ to var→ᵀᴹ; pmᶜ→ to pmᶜ→ᵀᴹ; app→ to app→ᵀᴹ)


mutual

  tmcstack-to-mcstack : TM.CStack Γ X → M.CStack X
  tmcstack-to-mcstack TM.◻ = M.◻
  tmcstack-to-mcstack (TM.< x ； γ ； π >∷ K) = M.< x ； tmenv-to-menv γ >∷ tmcstack-to-mcstack K

  tmenv-to-menv : TM.MEnv Γ → M.MEnv Γ
  tmenv-to-menv TM.⋄ = M.⋄
  tmenv-to-menv (γ TM.· 𝐖) = tmenv-to-menv γ M.· mclo-to-mval 𝐖 γ
  tmenv-to-menv (γ TM.·﹝ M ╎ π ╎ K ﹞) = tmenv-to-menv γ M.· M.jumpᵛ M (tmenv-to-menv γ) (tmcstack-to-mcstack K)

  mclo-to-mval : TM.MClo Γ X → TM.MEnv Γ → M.MVal X
  mclo-to-mval TM.unit γ = M.unitᵛ
  mclo-to-mval (TM.pair 𝐖₁ 𝐖₂) γ = M.pairᵛ (mclo-to-mval 𝐖₁ γ) (mclo-to-mval 𝐖₂ γ)
  mclo-to-mval (TM.lam M) γ = M.cloᵛ M (tmenv-to-menv γ)
  mclo-to-mval (TM.label here) (γ TM.· TM.label i) = mclo-to-mval (TM.label i) γ
  mclo-to-mval (TM.label here) (γ TM.·﹝ M ╎ π ╎ K ﹞) = M.jumpᵛ M (tmenv-to-menv γ) (tmcstack-to-mcstack K)
  mclo-to-mval (TM.label (there i)) (γ TM.· 𝐖) = mclo-to-mval (TM.label i) γ
  mclo-to-mval (TM.label (there i)) (γ TM.·﹝ M ╎ π ╎ K ﹞) = mclo-to-mval (TM.label i) γ

-------------------------------------------------------------------------------------

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

data WkCStateᴹ : M.CState → M.CState → Set where

  wk-cstate-result : {𝐖₁ 𝐖₂ : M.MVal X} {K₁ K₂ : M.CStack X}
                     → WkMVal 𝐖₁ 𝐖₂ → WkCStackᴹ K₁ K₂
                     → WkCStateᴹ ⟨ 𝐖₁ ╎ K₁ ⟩ ⟨ 𝐖₂ ╎ K₂ ⟩

  wk-cstate-comp : {Γ₁ Γ₂ : Ctx} {M₁ : Γ₁ ⊢ᶜ X} {M₂ : Γ₂ ⊢ᶜ X} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} {K₁ K₂ : M.CStack X}
                   → (π : Wk Γ₁ Γ₂) → M₁ ≡ wk-comp π M₂ → (WkMEnvᴹ π γ₁ γ₂) → WkCStackᴹ K₁ K₂
                   → WkCStateᴹ ⟨ M₁ ╎ γ₁ ╎ K₁ ⟩ ⟨ M₂ ╎ γ₂ ╎ K₂ ⟩

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

{-
data _≈ᴹ_ : M.CState → M.CState → Set where

    ≈-refl : {σ : M.CState} → σ ≈ᴹ σ

    ≈-sym : {σ₁ σ₂ : M.CState} → σ₁ ≈ᴹ σ₂ → σ₂ ≈ᴹ σ₁

    ≈-wk : {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} → (M : Comp Γ₂ X) → (WkMEnvᴹ π γ₁ γ₂) → (K : M.CStack X) → ⟨ M ╎ γ₂ ╎ K ⟩ ≈ᴹ ⟨ wk-comp π M ╎ γ₁ ╎ K ⟩

mutual

  ≈ᴹ-trans : {σ₁ σ₂ σ₃ : M.CState} → σ₁ ≈ᴹ σ₂ → σ₂ ≈ᴹ σ₃ → σ₁ ≈ᴹ σ₃
  ≈ᴹ-trans ≈-refl ≈-refl = ≈-refl
  ≈ᴹ-trans ≈-refl (≈-sym σ₂≈ᴹσ₃) = ≈-sym σ₂≈ᴹσ₃
  ≈ᴹ-trans ≈-refl (≈-wk M x K) = ≈-wk M x K
  ≈ᴹ-trans (≈-sym σ₁≈ᴹσ₂) ≈-refl = ≈-sym σ₁≈ᴹσ₂
  ≈ᴹ-trans (≈-sym σ₁≈ᴹσ₂) (≈-sym σ₂≈ᴹσ₃) = ≈-sym (≈ᴹ-trans σ₂≈ᴹσ₃ σ₁≈ᴹσ₂)
  ≈ᴹ-trans (≈-sym σ₁≈ᴹσ₂) (≈-wk M x K) =
    let
      a0 = ≈-wk M x K
      a1 = ≈-wk M x K
    in
    {!!}
  ≈ᴹ-trans (≈-wk M x K) ≈-refl = ≈-wk M x K
  ≈ᴹ-trans (≈-wk M x K) (≈-sym σ₂≈ᴹσ₃) = {!!}
  ≈ᴹ-trans (≈-wk M x K) (≈-wk M₁ x₁ K₁) = {!!}
-}

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

wk-mclo-wk-η : {Γ : Ctx} {X : Ty} → (𝐖 : TM.MClo Γ X) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → TM.wk-mclo π (TM.wk-mclo δ 𝐖) ≡ TM.wk-mclo (wk-trans π δ) 𝐖
wk-mclo-wk-η TM.unit π δ = refl
wk-mclo-wk-η (TM.pair 𝐖₁ 𝐖₂) π δ = cong₂ TM.pair (wk-mclo-wk-η 𝐖₁ π δ) (wk-mclo-wk-η 𝐖₂ π δ)
wk-mclo-wk-η (TM.lam M) π δ = cong TM.lam (wk-comp-id-β (wk-comp (wk-trans (Wk.wk-cong π) (Wk.wk-cong δ)) M))
wk-mclo-wk-η (TM.label x) π δ = refl

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

data _≈ᴹ_ : M.CState → M.CState → Set where

    ≈-wk₁ : {σ₁ σ₂ : M.CState} → WkCStateᴹ σ₁ σ₂ → σ₂ ≈ᴹ σ₁

    ≈-wk₂ : {σ₁ σ₂ : M.CState} → WkCStateᴹ σ₁ σ₂ → σ₁ ≈ᴹ σ₂

    ≈-trans : {σ₁ σ₂ σ₃ : M.CState} → σ₁ ≈ᴹ σ₂ → σ₂ ≈ᴹ σ₃ → σ₁ ≈ᴹ σ₃

≈ᴹ-refl : {σ : M.CState} → σ ≈ᴹ σ
≈ᴹ-refl {σ = ⟨ 𝐖 ╎ K ⟩} = ≈-wk₂ (wk-cstate-result wk-mval-id wk-cstack-id)
≈ᴹ-refl {σ = ⟨ M ╎ γ ╎ K ⟩} = ≈-wk₂ (wk-cstate-comp wk-id refl wk-menv-id wk-cstack-id)

≈ᴹ-sym : {σ₁ σ₂ : M.CState} → σ₁ ≈ᴹ σ₂ → σ₂ ≈ᴹ σ₁
≈ᴹ-sym (≈-wk₁ x) = ≈-wk₂ x
≈ᴹ-sym (≈-wk₂ x) = ≈-wk₁ x
≈ᴹ-sym (≈-trans x y) = ≈-trans (≈ᴹ-sym y) (≈ᴹ-sym x)

≈ᴹ-trans : {σ₁ σ₂ σ₃ : M.CState} → σ₁ ≈ᴹ σ₂ → σ₂ ≈ᴹ σ₃ → σ₁ ≈ᴹ σ₃
≈ᴹ-trans (≈-wk₁ x₁) (≈-wk₁ x₂) = ≈-wk₁ (wk-cstate-trans x₂ x₁)
≈ᴹ-trans (≈-wk₁ x) (≈-wk₂ x₁) = ≈-trans (≈-wk₁ x) (≈-wk₂ x₁)
≈ᴹ-trans (≈-wk₁ x) (≈-trans σ₂≈σ₃ σ₂≈σ₄) = ≈-trans (≈-wk₁ x) (≈-trans σ₂≈σ₃ σ₂≈σ₄)
≈ᴹ-trans (≈-wk₂ x) (≈-wk₁ x₁) = ≈-trans (≈-wk₂ x) (≈-wk₁ x₁)
≈ᴹ-trans (≈-wk₂ x₁) (≈-wk₂ x₂) = (≈-wk₂ (wk-cstate-trans x₁ x₂))
≈ᴹ-trans (≈-wk₂ x) (≈-trans σ₂≈σ₃ σ₂≈σ₄) = ≈-trans (≈ᴹ-trans (≈-wk₂ x) σ₂≈σ₃) σ₂≈σ₄
≈ᴹ-trans (≈-trans σ₁≈σ₂ σ₁≈σ₃) (≈-wk₁ x) = ≈ᴹ-trans σ₁≈σ₂ (≈ᴹ-trans σ₁≈σ₃ (≈-wk₁ x))
≈ᴹ-trans (≈-trans σ₁≈σ₂ σ₁≈σ₃) (≈-wk₂ x) = ≈ᴹ-trans σ₁≈σ₂ (≈ᴹ-trans σ₁≈σ₃ (≈-wk₂ x))
≈ᴹ-trans (≈-trans σ₁≈σ₂ σ₁≈σ₃) (≈-trans σ₂≈σ₃ σ₂≈σ₄) = ≈-trans σ₁≈σ₂ (≈-trans σ₁≈σ₃ (≈-trans σ₂≈σ₃ σ₂≈σ₄))

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

-------------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------------

tmcstate-to-mcstate : TM.CState → M.CState
tmcstate-to-mcstate ⟨ 𝐖 ； γ ╎ π ╎ K ⟩ = ⟨ mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩
tmcstate-to-mcstate ⟨ M ╎ γ ╎ π ╎ K ⟩ = ⟨ M ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩

next-state : {σ : M.CState} → M.Step? σ → M.CState
next-state {σ = σ} (M.done _) = σ
next-state (M.next {b = σ₁} _) = σ₁

tmstep-to-mstep : {σ σ' : TM.CState} → (WellFormedTMCState σ) → (σ →ᵀᴹ σ') → ((tmcstate-to-mcstate σ) →ᴹ (tmcstate-to-mcstate σ'))
tmstep-to-mstep wf (eval→ {W = W} {γ = γ} {K = K}) =
  --Goal: ⟨ return W ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩ →ᴹ ⟨ mclo-to-mval (TM.eval W γ) γ ╎ tmcstack-to-mcstack K ⟩
  let
    a0 : M.Step? ⟨ return W ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩
    a0 = progress ⟨ return W ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩
  in
  {!a0!}
tmstep-to-mstep (wf-state-result {π₁ = π₁} {π₂ = π₂} _ w _ _ _) (return→ {𝐖 = 𝐖} {M₁ = M₁} {γ = γ} {γ₁ = γ₁} {K = K} {π = π}) =
  -- Goal: ⟨ mclo-to-mval 𝐖 γ ╎ M.< M₁ ； tmenv-to-menv γ₁ >∷ tmcstack-to-mcstack K ⟩ →ᴹ ⟨ wk-comp (wk-cong π) M₁ ╎ tmenv-to-menv γ M.· mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩
  let
    a0 = progress ⟨ mclo-to-mval 𝐖 γ ╎ M.< M₁ ； tmenv-to-menv γ₁ >∷ tmcstack-to-mcstack K ⟩
    --next = next-state a0
    next = ⟨ M₁ ╎ tmenv-to-menv γ₁ · mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩

    eqv : ⟨ M₁ ╎ tmenv-to-menv γ₁ · mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩ ≈ᴹ ⟨ wk-comp (wk-cong π) M₁ ╎ tmenv-to-menv γ M.· mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩
    --eqv = ≈-wk M₁ (wk-menv-cong wk-mval-id (wk-MEnvᵀ-to-wk-MEnvᴹ w)) (tmcstack-to-mcstack K)
    eqv = ≈-wk₁ (wk-cstate-comp (Wk.wk-cong π₁) refl (wk-menv-cong wk-mval-id (wk-MEnvᵀ-to-wk-MEnvᴹ w)) wk-cstack-id)
  in
  {!!}
tmstep-to-mstep wf push→ = push→
tmstep-to-mstep wf sub→ = sub→
tmstep-to-mstep wf (var→ {W = W} {γ = γ} {K = K}) =
  -- Goal: ⟨ var W ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩ →ᴹ tmcstate-to-mcstate (TM.eval-jump W γ)
  let
    a0 = progress ⟨ var W ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩
  in
  {!a0!}
tmstep-to-mstep wf (pmᶜ→ {W = W} {γ = γ} {M = M} {K = K}) =
  -- Goal: ⟨ pm W M ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩ →ᴹ ⟨ M ╎ tmenv-to-menv γ M.· mclo-to-mval (TM.eval₁ W γ) γ M.· mclo-to-mval (TM.wk-mclo (wk-wk wk-id) (TM.eval₂ W γ)) (γ TM.· TM.eval₁ W γ) ╎ tmcstack-to-mcstack K ⟩
  let
    a0 = progress ⟨ pm W M ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩
  in
  {!a0!}
tmstep-to-mstep wf (app→ {W₁ = W₁} {W₂ = W₂} {γ = γ} {K = K}) =
  -- Goal: ⟨ app W₁ W₂ ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩ →ᴹ ⟨ TM.lam-to-comp (TM.eval W₁ γ) ╎ tmenv-to-menv γ M.· mclo-to-mval (TM.eval W₂ γ) γ ╎ tmcstack-to-mcstack K ⟩
  let
    a0 = progress ⟨ app W₁ W₂ ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩
  in
  {!a0!}
