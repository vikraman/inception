{-# OPTIONS --no-postfix-projections #-}

open import Inception.Sub.Syntax using (Ty)

module Inception.Sub.TelescopeMachineProps (ℛ : Ty) where

open import Inception.Sub.Syntax
open import Inception.Sub.TelescopeMachine ℛ

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; cong₂)

---------------------------------------------------------------------------------
-- Properties of Inception.Sub.TelescopeMachine
---------------------------------------------------------------------------------

-- Weakening of Telescopes
data WkMEnvᵀ : {Γ₁ Γ₂ : Ctx} → (π : Wk Γ₁ Γ₂) → (γ₁ : MEnv Γ₁) → (γ₂ : MEnv Γ₂) → Set where

    wk-tmenv-ε    : WkMEnvᵀ wk-ε ⋄ ⋄

    wk-tmenv-mclo-cong : {Γ₁ Γ₂ : Ctx} {π : Γ₁ ⊇ Γ₂} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} → (𝐖 : MClo Γ₂ X) → WkMEnvᵀ π γ₁ γ₂ → WkMEnvᵀ (wk-cong π) (γ₁ · wk-mclo π 𝐖) (γ₂ · 𝐖)

    wk-tmenv-jump-cong : {Γ₁ Γ₂ : Ctx} {π : Γ₁ ⊇ Γ₂} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂}
                         → (M : Γ₂ ⊢ᶜ X) → (πᵀ : Γ₂ ⊇ Δ) → (K : CStack Δ X) → WkMEnvᵀ π γ₁ γ₂
                         → WkMEnvᵀ (wk-cong π) (γ₁ ·﹝ wk-comp π M ╎ wk-trans π πᵀ ╎ K ﹞) (γ₂ ·﹝ M ╎ πᵀ ╎ K ﹞)

    wk-tmenv-mclo-wk : {Γ₁ Γ₂ : Ctx} {π : Γ₁ ⊇ Γ₂} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} → (𝐖 : MClo Γ₁ X) → WkMEnvᵀ π γ₁ γ₂ → WkMEnvᵀ (wk-wk π) (γ₁ · 𝐖) γ₂

    wk-tmenv-jump-wk :   {Γ₁ Γ₂ : Ctx} {π : Γ₁ ⊇ Γ₂} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂}
                         → (M : Γ₁ ⊢ᶜ X) → (πᵀ : Γ₁ ⊇ Δ) → (K : CStack Δ X) → WkMEnvᵀ π γ₁ γ₂
                         → WkMEnvᵀ (wk-wk π) (γ₁ ·﹝ M ╎ πᵀ ╎ K ﹞) γ₂

-- Well-formedness of states
mutual

  data WellFormedTMCStack : CStack Γ X → Set where

      ◻ : WellFormedTMCStack {Γ = ε} {X = ℛ} ◻

      wf-bottom : (M : (Γ ∙ Y) ⊢ᶜ ℛ) → (γ : MEnv Γ) → (π : Γ ⊇ ε)
                  → WellFormedTMEnv γ
                  ------------------------------------
                  → WellFormedTMCStack (< M ； γ ； π >∷ ◻)

      wf-next :  {Γ₁ Γ₂ Γ₃ : Ctx} → (M₁ : (Γ₁ ∙ Z) ⊢ᶜ Y) → {γ₁ : MEnv Γ₁} → (M₂ : (Γ₂ ∙ Y) ⊢ᶜ X) → {γ₂ : MEnv Γ₂}
                  → {π₁ : Γ₁ ⊇ Γ₂} → {π₂ : Γ₂ ⊇ Γ₃} → WkMEnvᵀ π₁ γ₁ γ₂
                  → {K : CStack Γ₃ X} → WellFormedTMCStack (< M₂ ； γ₂ ； π₂ >∷ K)
                  → WellFormedTMEnv γ₁
                  ------------------------------------
                  → WellFormedTMCStack (< M₁ ； γ₁ ； π₁ >∷ < M₂ ； γ₂ ； π₂ >∷ K)

  data WellFormedTMClo : MEnv Γ → MClo Γ X → Set where

      wf-mclo-unit : {γ : MEnv Γ} → WellFormedTMClo γ unit

      wf-mclo-lam : {γ : MEnv Γ} {M : (Γ ∙ X) ⊢ᶜ Y} → WellFormedTMClo γ (lam M)

      wf-mclo-pair : {γ : MEnv Γ} {𝐖₁ : MClo Γ X₁} {𝐖₂ : MClo Γ X₂} → WellFormedTMClo γ 𝐖₁ → WellFormedTMClo γ 𝐖₂ → WellFormedTMClo γ (pair 𝐖₁ 𝐖₂)

      wf-mclo-label-h : {γ : MEnv Γ} {M : Γ ⊢ᶜ X} {π : Γ ⊇ Γ₁} {K : CStack Γ₁ X} → WellFormedTMClo (γ ·﹝ M ╎ π ╎ K ﹞) (label here)

      wf-mclo-label-t-mclo : {γ : MEnv Γ} {i : Γ ∋ `ℓ} {𝐖 : MClo Γ X} → WellFormedTMClo γ (label i) → WellFormedTMClo (γ · 𝐖) (label (there i))

      wf-mclo-label-t-jump : {γ : MEnv Γ} {i : Γ ∋ `ℓ} {M : Γ ⊢ᶜ X} {π : Γ ⊇ Γ₁} {K : CStack Γ₁ X} → WellFormedTMClo γ (label i) → WellFormedTMClo (γ ·﹝ M ╎ π ╎ K ﹞) (label (there i))

  data WellFormedTMEnv : MEnv Γ → Set where

      wf-env-empty : WellFormedTMEnv ⋄

      wf-env-mclo : {γ : MEnv Γ} {𝐖 : MClo Γ X} → WellFormedTMEnv γ → WellFormedTMClo γ 𝐖 → WellFormedTMEnv (γ · 𝐖)

      wf-env-jump : {γ : MEnv Γ} {M : Γ ⊢ᶜ X} {π : Γ ⊇ Γ₁} {K : CStack Γ₁ X}
                    → WellFormedTMCState ⟨ M ╎ γ ╎ π ╎ K ⟩
                    → WellFormedTMEnv (γ ·﹝ M ╎ π ╎ K ﹞)

  data WellFormedTMCState : CState → Set where

      wf-state-halt : (𝐖 : MClo Γ ℛ) → (γ : MEnv Γ) → (π : Γ ⊇ ε)
                  → WellFormedTMEnv γ
                  → WellFormedTMClo γ 𝐖
                  ------------------------------------
                  → WellFormedTMCState ⟨ 𝐖 ； γ ╎ π ╎ ◻ ⟩

      wf-state-result : {Γ₁ Γ₂ Γ₃ : Ctx} {γ₁ : MEnv Γ₁}
                  {γ₂ : MEnv Γ₂} {π₁ : Γ₁ ⊇ Γ₂} → {π₂ : Γ₂ ⊇ Γ₃}
                  {M : (Γ₂ ∙ X) ⊢ᶜ Y} {K : CStack Γ₃ Y}
                  → (𝐖 : MClo Γ₁ X)
                  → WkMEnvᵀ π₁ γ₁ γ₂
                  → WellFormedTMCStack (< M ； γ₂ ； π₂ >∷ K)
                  → WellFormedTMEnv γ₁
                  → WellFormedTMClo γ₁ 𝐖
                  ------------------------------------
                  → WellFormedTMCState ⟨ 𝐖 ； γ₁ ╎ π₁ ╎ < M ； γ₂ ； π₂ >∷ K ⟩

      wf-state-bottom : (M : Γ ⊢ᶜ ℛ) → (γ : MEnv Γ) → (π : Γ ⊇ ε)
                  → WellFormedTMEnv γ
                  ------------------------------------
                  → WellFormedTMCState ⟨ M ╎ γ ╎ π ╎ ◻ ⟩

      wf-state-resume : {Γ₁ Γ₂ Γ₃ : Ctx} {γ₁ : MEnv Γ₁}
                  {γ₂ : MEnv Γ₂} {π₁ : Γ₁ ⊇ Γ₂} → {π₂ : Γ₂ ⊇ Γ₃}
                  {M₂ : (Γ₂ ∙ X) ⊢ᶜ Y} {K : CStack Γ₃ Y}
                  → (M₁ : Γ₁ ⊢ᶜ X)
                  → WkMEnvᵀ π₁ γ₁ γ₂
                  → WellFormedTMCStack (< M₂ ； γ₂ ； π₂ >∷ K)
                  → WellFormedTMEnv γ₁
                  ------------------------------------
                  → WellFormedTMCState ⟨ M₁ ╎ γ₁ ╎ π₁ ╎ < M₂ ； γ₂ ； π₂ >∷ K ⟩

wk-mclo-wk-η : {Γ : Ctx} {X : Ty} → (𝐖 : MClo Γ X) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → wk-mclo π (wk-mclo δ 𝐖) ≡ wk-mclo (wk-trans π δ) 𝐖
wk-mclo-wk-η unit π δ = refl
wk-mclo-wk-η (pair 𝐖₁ 𝐖₂) π δ = cong₂ pair (wk-mclo-wk-η 𝐖₁ π δ) (wk-mclo-wk-η 𝐖₂ π δ)
wk-mclo-wk-η (lam M) π δ = cong lam (wk-comp-id-β (wk-comp (wk-trans (Wk.wk-cong π) (Wk.wk-cong δ)) M))
wk-mclo-wk-η (label x) π δ = refl

wk-MEnvᵀ-trans : {Γ₁ Γ₂ Γ₃ : Ctx} {π₁ : Γ₁ ⊇ Γ₂} {π₂ : Γ₂ ⊇ Γ₃} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} {γ₃ : MEnv Γ₃} → WkMEnvᵀ π₁ γ₁ γ₂ → WkMEnvᵀ π₂ γ₂ γ₃ → WkMEnvᵀ (wk-trans π₁ π₂) γ₁ γ₃
wk-MEnvᵀ-trans wk-tmenv-ε wk-tmenv-ε = wk-tmenv-ε
wk-MEnvᵀ-trans {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {γ₁ = γ₁ · _} {γ₂ = γ₂ · _} {γ₃ = γ₃ · _} (wk-tmenv-mclo-cong 𝐖 ϖ₁) (wk-tmenv-mclo-cong 𝐖₁ ϖ₂) =
  let
    a₀ = wk-MEnvᵀ-trans ϖ₁ ϖ₂
    a₁ : WkMEnvᵀ (wk-cong (wk-trans π₁ π₂)) (γ₁ · wk-mclo (wk-trans π₁ π₂) 𝐖₁) (γ₃ · 𝐖₁)
    a₁ = wk-tmenv-mclo-cong 𝐖₁ a₀
    a₂ : WkMEnvᵀ (wk-trans (Wk.wk-cong π₁) (Wk.wk-cong π₂)) (γ₁ · wk-mclo (wk-trans π₁ π₂) 𝐖₁) (γ₃ · 𝐖₁)
    a₂ = subst (λ x → WkMEnvᵀ x (γ₁ · wk-mclo (wk-trans π₁ π₂) 𝐖₁) (γ₃ · 𝐖₁)) (wk-trans-idr-β (Wk.wk-cong (wk-trans π₁ π₂))) a₁
    a₃ : WkMEnvᵀ (wk-trans (Wk.wk-cong π₁) (Wk.wk-cong π₂)) (γ₁ · wk-mclo π₁ (wk-mclo π₂ 𝐖₁)) (γ₃ · 𝐖₁)
    a₃ = subst (λ x → WkMEnvᵀ (wk-trans (Wk.wk-cong π₁) (Wk.wk-cong π₂)) (γ₁ · x) (γ₃ · 𝐖₁)) (sym (wk-mclo-wk-η 𝐖₁ π₁ π₂)) a₂
  in
  a₃
wk-MEnvᵀ-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} (wk-tmenv-mclo-cong 𝐖 ϖ₁) (wk-tmenv-mclo-wk 𝐖₁ ϖ₂) = wk-tmenv-mclo-wk (wk-mclo π₁ 𝐖) (wk-MEnvᵀ-trans ϖ₁ ϖ₂)
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

wk-mclo-id-η : (𝐖 : MClo Γ X) → wk-mclo wk-id 𝐖 ≡ 𝐖
wk-mclo-id-η unit = refl
wk-mclo-id-η (pair 𝐖₁ 𝐖₂) = cong₂ pair (wk-mclo-id-η 𝐖₁) (wk-mclo-id-η 𝐖₂)
wk-mclo-id-η (lam M) = refl
wk-mclo-id-η (label x) = refl

wk-MEnvᵀ-id : (γ : MEnv Γ) → WkMEnvᵀ (wk-id) γ γ
wk-MEnvᵀ-id ⋄ = wk-tmenv-ε
wk-MEnvᵀ-id (γ · unit) = wk-tmenv-mclo-cong unit (wk-MEnvᵀ-id γ)
wk-MEnvᵀ-id (γ · pair x₁ x₂) =
  let
    a₀ = wk-tmenv-mclo-cong (pair x₁ x₂) (wk-MEnvᵀ-id γ)
  in
  subst (λ x → WkMEnvᵀ (wk-cong wk-id) (γ · x) (γ · pair x₁ x₂)) (wk-mclo-id-η (pair x₁ x₂)) a₀
wk-MEnvᵀ-id (γ · lam M) = wk-tmenv-mclo-cong (lam M) (wk-MEnvᵀ-id γ)
wk-MEnvᵀ-id (γ · label x) = wk-tmenv-mclo-cong (label x) (wk-MEnvᵀ-id γ)
wk-MEnvᵀ-id (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-tmenv-jump-cong x x₁ x₂ (wk-MEnvᵀ-id γ)

wf-mclo-wk-mclo : {γ : MEnv Γ} {𝐖 : MClo Γ X} {𝐖₁ : MClo Γ Y} → WellFormedTMClo γ 𝐖 → WellFormedTMClo γ 𝐖₁ → WellFormedTMClo (γ · 𝐖₁) (wk-mclo (wk-wk wk-id) 𝐖)
wf-mclo-wk-mclo wf-mclo-unit g₁ = wf-mclo-unit
wf-mclo-wk-mclo wf-mclo-lam g₁ = wf-mclo-lam
wf-mclo-wk-mclo (wf-mclo-pair g g₂) g₁ = wf-mclo-pair (wf-mclo-wk-mclo g g₁) (wf-mclo-wk-mclo g₂ g₁)
wf-mclo-wk-mclo wf-mclo-label-h g₁ = wf-mclo-label-t-mclo wf-mclo-label-h
wf-mclo-wk-mclo (wf-mclo-label-t-mclo g) g₁ = wf-mclo-label-t-mclo (wf-mclo-label-t-mclo g)
wf-mclo-wk-mclo (wf-mclo-label-t-jump g) g₁ = wf-mclo-label-t-mclo (wf-mclo-label-t-jump g)

wf-mclo-wk-jump : {γ : MEnv Γ} {𝐖 : MClo Γ X} {M : Γ ⊢ᶜ Y} {π : Γ ⊇ Γ₁} {K : CStack Γ₁ Y} → WellFormedTMClo γ 𝐖 → WellFormedTMClo (γ ·﹝ M ╎ π ╎ K ﹞) (wk-mclo (wk-wk wk-id) 𝐖)
wf-mclo-wk-jump wf-mclo-unit = wf-mclo-unit
wf-mclo-wk-jump wf-mclo-lam = wf-mclo-lam
wf-mclo-wk-jump (wf-mclo-pair g g₁) = wf-mclo-pair (wf-mclo-wk-jump g) (wf-mclo-wk-jump g₁)
wf-mclo-wk-jump wf-mclo-label-h = wf-mclo-label-t-jump wf-mclo-label-h
wf-mclo-wk-jump (wf-mclo-label-t-mclo g) = wf-mclo-label-t-jump (wf-mclo-label-t-mclo g)
wf-mclo-wk-jump (wf-mclo-label-t-jump g) = wf-mclo-label-t-jump (wf-mclo-label-t-jump g)

wf-lookup : {γ : MEnv Γ} → (i : Γ ∋ X) → (g : WellFormedTMEnv γ) → WellFormedTMClo γ (lookup i γ)
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

wf-lookup-label : {γ : MEnv Γ} → (i : Γ ∋ `ℓ) → (g : WellFormedTMEnv γ) → WellFormedTMCState (lookup-label i γ)
wf-lookup-label {γ = γ · (label x)} here (wf-env-mclo g x₁) = wf-lookup-label x g
wf-lookup-label here (wf-env-jump x) = x
wf-lookup-label (there i) (wf-env-mclo g x) = wf-lookup-label i g
wf-lookup-label (there i) (wf-env-jump (wf-state-bottom M γ π x)) = wf-lookup-label i x
wf-lookup-label (there i) (wf-env-jump (wf-state-resume M₁ x x₁ x₂)) = wf-lookup-label i x₂

wf-eval : {γ : MEnv Γ} → (W : Γ ⊢ᵛ X) → (g : WellFormedTMEnv γ) → WellFormedTMClo γ (eval W γ)
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

wf-proj₁ : {γ : MEnv Γ} {𝐖 : MClo Γ (X₁ `× X₂)} → WellFormedTMClo γ 𝐖 → WellFormedTMClo γ (proj₁-mclo 𝐖)
wf-proj₁ (wf-mclo-pair w₁ w₂) = w₁

wf-proj₂ : {γ : MEnv Γ} {𝐖 : MClo Γ (X₁ `× X₂)} → WellFormedTMClo γ 𝐖 → WellFormedTMClo γ (proj₂-mclo 𝐖)
wf-proj₂ (wf-mclo-pair w₁ w₂) = w₂

wf-eval₁ : {γ : MEnv Γ} → (W : Γ ⊢ᵛ (X₁ `× X₂)) → (g : WellFormedTMEnv γ) → WellFormedTMClo γ (eval₁ W γ)
wf-eval₁ W g = wf-proj₁ (wf-eval W g)

wf-eval₂ : {γ : MEnv Γ} → (W : Γ ⊢ᵛ (X₁ `× X₂)) → (g : WellFormedTMEnv γ) → WellFormedTMClo γ (eval₂ W γ)
wf-eval₂ W g = wf-proj₂ (wf-eval W g)

wf-jump : {γ : MEnv Γ} → (i : Γ ∋ `ℓ) → (g : WellFormedTMEnv γ) → WellFormedTMCState (eval-jump (var i) γ)
wf-jump i g = wf-lookup-label i g

wf-preservation : {σ σ₁ : CState} → (σ →ᶜ σ₁) → WellFormedTMCState σ → WellFormedTMCState σ₁
wf-preservation eval→ (wf-state-bottom (return W) γ π g) = wf-state-halt _ γ π g (wf-eval W g)
wf-preservation eval→ (wf-state-resume (return W) x x₁ g) = wf-state-result _ x x₁ g (wf-eval W g)
wf-preservation (return→ {K = ◻}) (wf-state-result 𝐖 x (wf-bottom M γ π x₁) g w) = wf-state-bottom _ (_ · 𝐖) _ (wf-env-mclo g w)
wf-preservation (return→ {K = < x₂ ； γ ； π >∷ K}) (wf-state-result 𝐖 ϖ₁ (wf-next M₁ M₂ ϖ₂ x₃ g₁) g₂ w) = wf-state-resume _ (wk-tmenv-mclo-wk 𝐖 (wk-MEnvᵀ-trans ϖ₁ ϖ₂)) x₃ (wf-env-mclo g₂ w)
wf-preservation push→ (wf-state-bottom M γ π g) = wf-state-resume _ (wk-MEnvᵀ-id γ) (wf-bottom _ γ π g) g
wf-preservation push→ (wf-state-resume M₁ x x₁ g) = wf-state-resume _ (wk-MEnvᵀ-id _) (wf-next _ _ x x₁ g) g
wf-preservation sub→ (wf-state-bottom M γ π g) = wf-state-bottom _ (γ ·﹝ _ ╎ π ╎ ◻ ﹞) (wk-wk π) (wf-env-jump (wf-state-bottom _ γ π g))
wf-preservation sub→ (wf-state-resume M₁ x x₁ g) = wf-state-resume _ (wk-tmenv-jump-wk _ _ _ x) x₁ (wf-env-jump (wf-state-resume _ x x₁ g))
wf-preservation (var→ {W = var i}) (wf-state-bottom M γ π g) = wf-jump i g
wf-preservation (var→ {W = var i}) (wf-state-resume M₁ x x₁ g) = wf-jump i g
wf-preservation (pmᶜ→ {W = W}) (wf-state-bottom M γ π g) = wf-state-bottom _ (γ · _ · wk-mclo (wk-wk wk-id) _) (Wk.wk-wk (Wk.wk-wk π)) (wf-env-mclo (wf-env-mclo g (wf-eval₁ W g)) (wf-mclo-wk-mclo (wf-eval₂ W g) (wf-eval₁ W g)))
wf-preservation (pmᶜ→ {W = W}) (wf-state-resume M₁ x x₁ g) = wf-state-resume _ (wk-tmenv-mclo-wk (wk-mclo (wk-wk wk-id) _) (wk-tmenv-mclo-wk _ x)) x₁ (wf-env-mclo (wf-env-mclo g (wf-eval₁ W g)) (wf-mclo-wk-mclo (wf-eval₂ W g) (wf-eval₁ W g)))
wf-preservation app→ (wf-state-bottom (app W₁ W₂) γ π g) = wf-state-bottom _ (γ · _) (Wk.wk-wk π) (wf-env-mclo g (wf-eval W₂ g))
wf-preservation app→ (wf-state-resume (app W₁ W₂) x x₁ g) = wf-state-resume _ (wk-tmenv-mclo-wk _ x) x₁ (wf-env-mclo g (wf-eval W₂ g))

init-wf : (M : ε ⊢ᶜ ℛ) → WellFormedTMCState ⟨ M ╎ ⋄ ╎ wk-ε ╎ ◻ ⟩
init-wf M = wf-state-bottom M ⋄ wk-ε wf-env-empty
