{-# OPTIONS --no-postfix-projections #-}

open import Inception.Sub.Syntax using (Ty)

module Inception.Sub.TelescopeMachineProps (ℛ : Ty) where

open import Inception.Sub.Syntax
open import Inception.Sub.TelescopeMachine ℛ

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; cong₂)

--------------------------------------------------------------------------
-- properties of telescope machine
--------------------------------------------------------------------------

-- weakening of telescopes
data WkMEnvᵀ : {Γ Δ : Ctx} → (π : Wk Γ Δ) → (γ : MEnv Γ) → (δ : MEnv Δ) → Set where

    wk-tmenv-ε    : WkMEnvᵀ wk-ε ⋄ ⋄

    wk-tmenv-omval-cong : {Γ Δ : Ctx} {π : Γ ⊇ Δ} {γ : MEnv Γ} {δ : MEnv Δ} → (𝐖 : OMVal Δ X) → WkMEnvᵀ π γ δ → WkMEnvᵀ (wk-cong π) (γ · wk-omval π 𝐖) (δ · 𝐖)

    wk-tmenv-jump-cong : {Γ Δ : Ctx} {π : Γ ⊇ Δ} {γ : MEnv Γ} {δ : MEnv Δ}
                         → (M : Δ ⊢ᶜ X) → (ρ : Δ ⊇ Ψ) → (K : CStack Ψ X) → WkMEnvᵀ π γ δ
                         → WkMEnvᵀ (wk-cong π) (γ ·﹝ wk-comp π M ╎ wk-trans π ρ ╎ K ﹞) (δ ·﹝ M ╎ ρ ╎ K ﹞)

    wk-tmenv-omval-wk : {Γ Δ : Ctx} {π : Γ ⊇ Δ} {γ : MEnv Γ} {δ : MEnv Δ} → (𝐖 : OMVal Γ X) → WkMEnvᵀ π γ δ → WkMEnvᵀ (wk-wk π) (γ · 𝐖) δ

    wk-tmenv-jump-wk :   {Γ Δ : Ctx} {π : Γ ⊇ Δ} {γ : MEnv Γ} {δ : MEnv Δ}
                         → (M : Γ ⊢ᶜ X) → (ρ : Γ ⊇ Ψ) → (K : CStack Ψ X) → WkMEnvᵀ π γ δ
                         → WkMEnvᵀ (wk-wk π) (γ ·﹝ M ╎ ρ ╎ K ﹞) δ

-- well-formedness of states
mutual

  data WellFormedTMCStack : CStack Γ X → Set where

      ◻ : WellFormedTMCStack {Γ = ε} {X = ℛ} ◻

      wf-bottom : (M : (Γ ∙ Y) ⊢ᶜ ℛ) → (γ : MEnv Γ) → (π : Γ ⊇ ε)
                  → WellFormedTMEnv γ
                  ------------------------------------
                  → WellFormedTMCStack (< M ； γ ； π >∷ ◻)

      wf-next :  {Γ₁ Γ₂ Γ₃ : Ctx} → (M : (Γ₁ ∙ Z) ⊢ᶜ Y) → {γ₁ : MEnv Γ₁} → (N : (Γ₂ ∙ Y) ⊢ᶜ X) → {γ₂ : MEnv Γ₂}
                  → {π₁ : Γ₁ ⊇ Γ₂} → {π₂ : Γ₂ ⊇ Γ₃} → WkMEnvᵀ π₁ γ₁ γ₂
                  → {K : CStack Γ₃ X} → WellFormedTMCStack (< N ； γ₂ ； π₂ >∷ K)
                  → WellFormedTMEnv γ₁
                  ------------------------------------
                  → WellFormedTMCStack (< M ； γ₁ ； π₁ >∷ < N ； γ₂ ； π₂ >∷ K)

  data WellFormedTOMVal : MEnv Γ → OMVal Γ X → Set where

      wf-omval-unit : {γ : MEnv Γ} → WellFormedTOMVal γ unit

      wf-omval-lam : {γ : MEnv Γ} {M : (Γ ∙ X) ⊢ᶜ Y} → WellFormedTOMVal γ (lam M)

      wf-omval-pair : {γ : MEnv Γ} {𝐕 : OMVal Γ X} {𝐖 : OMVal Γ Y} → WellFormedTOMVal γ 𝐕 → WellFormedTOMVal γ 𝐖 → WellFormedTOMVal γ (pair 𝐕 𝐖)

      wf-omval-label-h : {γ : MEnv Γ} {M : Γ ⊢ᶜ X} {π : Γ ⊇ Γ₁} {K : CStack Γ₁ X} → WellFormedTOMVal (γ ·﹝ M ╎ π ╎ K ﹞) (label here)

      wf-omval-label-t-omval : {γ : MEnv Γ} {i : Γ ∋ `ℓ} {𝐖 : OMVal Γ X} → WellFormedTOMVal γ (label i) → WellFormedTOMVal (γ · 𝐖) (label (there i))

      wf-omval-label-t-jump : {γ : MEnv Γ} {i : Γ ∋ `ℓ} {M : Γ ⊢ᶜ X} {π : Γ ⊇ Γ₁} {K : CStack Γ₁ X} → WellFormedTOMVal γ (label i) → WellFormedTOMVal (γ ·﹝ M ╎ π ╎ K ﹞) (label (there i))

  data WellFormedTMEnv : MEnv Γ → Set where

      wf-env-empty : WellFormedTMEnv ⋄

      wf-env-omval : {γ : MEnv Γ} {𝐖 : OMVal Γ X} → WellFormedTMEnv γ → WellFormedTOMVal γ 𝐖 → WellFormedTMEnv (γ · 𝐖)

      wf-env-jump : {γ : MEnv Γ} {M : Γ ⊢ᶜ X} {π : Γ ⊇ Γ₁} {K : CStack Γ₁ X}
                    → WellFormedTMCState ⟨ M ╎ γ ╎ π ╎ K ⟩
                    → WellFormedTMEnv (γ ·﹝ M ╎ π ╎ K ﹞)

  data WellFormedTMCState : CState → Set where

      wf-state-halt : (𝐖 : OMVal Γ ℛ) → (γ : MEnv Γ) → (π : Γ ⊇ ε)
                  → WellFormedTMEnv γ
                  → WellFormedTOMVal γ 𝐖
                  ------------------------------------
                  → WellFormedTMCState ⟨ 𝐖 ； γ ╎ π ╎ ◻ ⟩

      wf-state-result : {Γ₁ Γ₂ Γ₃ : Ctx} {γ₁ : MEnv Γ₁}
                  {γ₂ : MEnv Γ₂} {π₁ : Γ₁ ⊇ Γ₂} → {π₂ : Γ₂ ⊇ Γ₃}
                  {M : (Γ₂ ∙ X) ⊢ᶜ Y} {K : CStack Γ₃ Y}
                  → (𝐖 : OMVal Γ₁ X)
                  → WkMEnvᵀ π₁ γ₁ γ₂
                  → WellFormedTMCStack (< M ； γ₂ ； π₂ >∷ K)
                  → WellFormedTMEnv γ₁
                  → WellFormedTOMVal γ₁ 𝐖
                  ------------------------------------
                  → WellFormedTMCState ⟨ 𝐖 ； γ₁ ╎ π₁ ╎ < M ； γ₂ ； π₂ >∷ K ⟩

      wf-state-bottom : (M : Γ ⊢ᶜ ℛ) → (γ : MEnv Γ) → (π : Γ ⊇ ε)
                  → WellFormedTMEnv γ
                  ------------------------------------
                  → WellFormedTMCState ⟨ M ╎ γ ╎ π ╎ ◻ ⟩

      wf-state-resume : {Γ₁ Γ₂ Γ₃ : Ctx} {γ₁ : MEnv Γ₁}
                  {γ₂ : MEnv Γ₂} {π₁ : Γ₁ ⊇ Γ₂} → {π₂ : Γ₂ ⊇ Γ₃}
                  {N : (Γ₂ ∙ X) ⊢ᶜ Y} {K : CStack Γ₃ Y}
                  → (M : Γ₁ ⊢ᶜ X)
                  → WkMEnvᵀ π₁ γ₁ γ₂
                  → WellFormedTMCStack (< N ； γ₂ ； π₂ >∷ K)
                  → WellFormedTMEnv γ₁
                  ------------------------------------
                  → WellFormedTMCState ⟨ M ╎ γ₁ ╎ π₁ ╎ < N ； γ₂ ； π₂ >∷ K ⟩

wk-omval-wk-η : {Γ : Ctx} {X : Ty} → (𝐖 : OMVal Γ X) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → wk-omval π (wk-omval δ 𝐖) ≡ wk-omval (wk-trans π δ) 𝐖
wk-omval-wk-η unit π δ = refl
wk-omval-wk-η (pair 𝐕 𝐖) π δ = cong₂ pair (wk-omval-wk-η 𝐕 π δ) (wk-omval-wk-η 𝐖 π δ)
wk-omval-wk-η (lam M) π δ = cong lam (wk-comp-id-β (wk-comp (wk-trans (Wk.wk-cong π) (Wk.wk-cong δ)) M))
wk-omval-wk-η (label x) π δ = refl

wk-MEnvᵀ-trans : {Γ₁ Γ₂ Γ₃ : Ctx} {π₁ : Γ₁ ⊇ Γ₂} {π₂ : Γ₂ ⊇ Γ₃} {γ₁ : MEnv Γ₁} {γ₂ : MEnv Γ₂} {γ₃ : MEnv Γ₃} → WkMEnvᵀ π₁ γ₁ γ₂ → WkMEnvᵀ π₂ γ₂ γ₃ → WkMEnvᵀ (wk-trans π₁ π₂) γ₁ γ₃
wk-MEnvᵀ-trans wk-tmenv-ε wk-tmenv-ε = wk-tmenv-ε
wk-MEnvᵀ-trans {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {γ₁ = γ₁ · _} {γ₂ = γ₂ · _} {γ₃ = γ₃ · _} (wk-tmenv-omval-cong 𝐖 ϖ₁) (wk-tmenv-omval-cong 𝐖₁ ϖ₂) =
  let
    a₀ = wk-MEnvᵀ-trans ϖ₁ ϖ₂
    a₁ : WkMEnvᵀ (wk-cong (wk-trans π₁ π₂)) (γ₁ · wk-omval (wk-trans π₁ π₂) 𝐖₁) (γ₃ · 𝐖₁)
    a₁ = wk-tmenv-omval-cong 𝐖₁ a₀
    a₂ : WkMEnvᵀ (wk-trans (Wk.wk-cong π₁) (Wk.wk-cong π₂)) (γ₁ · wk-omval (wk-trans π₁ π₂) 𝐖₁) (γ₃ · 𝐖₁)
    a₂ = subst (λ x → WkMEnvᵀ x (γ₁ · wk-omval (wk-trans π₁ π₂) 𝐖₁) (γ₃ · 𝐖₁)) (wk-trans-idr-β (Wk.wk-cong (wk-trans π₁ π₂))) a₁
    a₃ : WkMEnvᵀ (wk-trans (Wk.wk-cong π₁) (Wk.wk-cong π₂)) (γ₁ · wk-omval π₁ (wk-omval π₂ 𝐖₁)) (γ₃ · 𝐖₁)
    a₃ = subst (λ x → WkMEnvᵀ (wk-trans (Wk.wk-cong π₁) (Wk.wk-cong π₂)) (γ₁ · x) (γ₃ · 𝐖₁)) (sym (wk-omval-wk-η 𝐖₁ π₁ π₂)) a₂
  in
  a₃
wk-MEnvᵀ-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} (wk-tmenv-omval-cong 𝐖 ϖ₁) (wk-tmenv-omval-wk 𝐖₁ ϖ₂) = wk-tmenv-omval-wk (wk-omval π₁ 𝐖) (wk-MEnvᵀ-trans ϖ₁ ϖ₂)
wk-MEnvᵀ-trans {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} (wk-tmenv-jump-cong M ρ K ϖ₁) (wk-tmenv-jump-cong N ρ₁ K₁ ϖ₂) = wk-tmenv-jump-cong N ρ₁ K₁ (wk-MEnvᵀ-trans ϖ₁ ϖ₂)
wk-MEnvᵀ-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂}(wk-tmenv-jump-cong M ρ K ϖ₁) (wk-tmenv-jump-wk N ρ₁ K₁ ϖ₂) = wk-tmenv-jump-wk (wk-comp π₁ M) (wk-trans π₁ ρ) K (wk-MEnvᵀ-trans ϖ₁ ϖ₂)
wk-MEnvᵀ-trans (wk-tmenv-omval-wk 𝐖 ϖ) wk-tmenv-ε = wk-tmenv-omval-wk 𝐖 ϖ
wk-MEnvᵀ-trans (wk-tmenv-omval-wk 𝐖 ϖ₁) (wk-tmenv-omval-cong 𝐖₁ ϖ₂) = wk-tmenv-omval-wk 𝐖 (wk-MEnvᵀ-trans ϖ₁ (wk-tmenv-omval-cong 𝐖₁ ϖ₂))
wk-MEnvᵀ-trans (wk-tmenv-omval-wk 𝐖 ϖ₁) (wk-tmenv-jump-cong M ρ K ϖ₂) = wk-tmenv-omval-wk 𝐖 (wk-MEnvᵀ-trans ϖ₁ (wk-tmenv-jump-cong M ρ K ϖ₂))
wk-MEnvᵀ-trans (wk-tmenv-omval-wk 𝐖 ϖ₁) (wk-tmenv-omval-wk 𝐖₁ ϖ₂) = wk-tmenv-omval-wk 𝐖 (wk-MEnvᵀ-trans ϖ₁ (wk-tmenv-omval-wk 𝐖₁ ϖ₂))
wk-MEnvᵀ-trans (wk-tmenv-omval-wk 𝐖 ϖ₁) (wk-tmenv-jump-wk M ρ K ϖ₂) = wk-tmenv-omval-wk 𝐖 (wk-MEnvᵀ-trans ϖ₁ (wk-tmenv-jump-wk M ρ K ϖ₂))
wk-MEnvᵀ-trans (wk-tmenv-jump-wk M ρ K ϖ) wk-tmenv-ε = wk-tmenv-jump-wk M ρ K ϖ
wk-MEnvᵀ-trans (wk-tmenv-jump-wk M ρ K ϖ₁) (wk-tmenv-omval-cong 𝐖 ϖ₂) = wk-tmenv-jump-wk M ρ K (wk-MEnvᵀ-trans ϖ₁ (wk-tmenv-omval-cong 𝐖 ϖ₂))
wk-MEnvᵀ-trans (wk-tmenv-jump-wk M ρ K ϖ₁) (wk-tmenv-jump-cong N ρ₁ K₁ ϖ₂) = wk-tmenv-jump-wk M ρ K (wk-MEnvᵀ-trans ϖ₁ (wk-tmenv-jump-cong N ρ₁ K₁ ϖ₂))
wk-MEnvᵀ-trans (wk-tmenv-jump-wk M ρ K ϖ₁) (wk-tmenv-omval-wk 𝐖 ϖ₂) = wk-tmenv-jump-wk M ρ K (wk-MEnvᵀ-trans ϖ₁ (wk-tmenv-omval-wk 𝐖 ϖ₂))
wk-MEnvᵀ-trans (wk-tmenv-jump-wk M ρ K ϖ₁) (wk-tmenv-jump-wk N ρ₁ K₁ ϖ₂) = wk-tmenv-jump-wk M ρ K (wk-MEnvᵀ-trans ϖ₁ (wk-tmenv-jump-wk N ρ₁ K₁ ϖ₂))

wk-omval-id-η : (𝐖 : OMVal Γ X) → wk-omval wk-id 𝐖 ≡ 𝐖
wk-omval-id-η unit = refl
wk-omval-id-η (pair 𝐕 𝐖) = cong₂ pair (wk-omval-id-η 𝐕) (wk-omval-id-η 𝐖)
wk-omval-id-η (lam M) = refl
wk-omval-id-η (label x) = refl

wk-MEnvᵀ-id : (γ : MEnv Γ) → WkMEnvᵀ (wk-id) γ γ
wk-MEnvᵀ-id ⋄ = wk-tmenv-ε
wk-MEnvᵀ-id (γ · unit) = wk-tmenv-omval-cong unit (wk-MEnvᵀ-id γ)
wk-MEnvᵀ-id (γ · pair x₁ x₂) =
  let
    a = wk-tmenv-omval-cong (pair x₁ x₂) (wk-MEnvᵀ-id γ)
  in
  subst (λ x → WkMEnvᵀ (wk-cong wk-id) (γ · x) (γ · pair x₁ x₂)) (wk-omval-id-η (pair x₁ x₂)) a
wk-MEnvᵀ-id (γ · lam M) = wk-tmenv-omval-cong (lam M) (wk-MEnvᵀ-id γ)
wk-MEnvᵀ-id (γ · label x) = wk-tmenv-omval-cong (label x) (wk-MEnvᵀ-id γ)
wk-MEnvᵀ-id (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-tmenv-jump-cong x x₁ x₂ (wk-MEnvᵀ-id γ)

wf-omval-wk-omval : {γ : MEnv Γ} {𝐖 : OMVal Γ X} {𝐖₁ : OMVal Γ Y} → WellFormedTOMVal γ 𝐖 → WellFormedTOMVal γ 𝐖₁ → WellFormedTOMVal (γ · 𝐖₁) (wk-omval (wk-wk wk-id) 𝐖)
wf-omval-wk-omval wf-omval-unit _ = wf-omval-unit
wf-omval-wk-omval wf-omval-lam _ = wf-omval-lam
wf-omval-wk-omval (wf-omval-pair g g₂) g₁ = wf-omval-pair (wf-omval-wk-omval g g₁) (wf-omval-wk-omval g₂ g₁)
wf-omval-wk-omval wf-omval-label-h _ = wf-omval-label-t-omval wf-omval-label-h
wf-omval-wk-omval (wf-omval-label-t-omval g) g₁ = wf-omval-label-t-omval (wf-omval-label-t-omval g)
wf-omval-wk-omval (wf-omval-label-t-jump g) g₁ = wf-omval-label-t-omval (wf-omval-label-t-jump g)

wf-omval-wk-jump : {γ : MEnv Γ} {𝐖 : OMVal Γ X} {M : Γ ⊢ᶜ Y} {π : Γ ⊇ Γ₁} {K : CStack Γ₁ Y} → WellFormedTOMVal γ 𝐖 → WellFormedTOMVal (γ ·﹝ M ╎ π ╎ K ﹞) (wk-omval (wk-wk wk-id) 𝐖)
wf-omval-wk-jump wf-omval-unit = wf-omval-unit
wf-omval-wk-jump wf-omval-lam = wf-omval-lam
wf-omval-wk-jump (wf-omval-pair g g₁) = wf-omval-pair (wf-omval-wk-jump g) (wf-omval-wk-jump g₁)
wf-omval-wk-jump wf-omval-label-h = wf-omval-label-t-jump wf-omval-label-h
wf-omval-wk-jump (wf-omval-label-t-omval g) = wf-omval-label-t-jump (wf-omval-label-t-omval g)
wf-omval-wk-jump (wf-omval-label-t-jump g) = wf-omval-label-t-jump (wf-omval-label-t-jump g)

wf-lookup : {γ : MEnv Γ} → (i : Γ ∋ X) → (g : WellFormedTMEnv γ) → WellFormedTOMVal γ (lookup i γ)
wf-lookup here (wf-env-omval g wf-omval-unit) = wf-omval-unit
wf-lookup here (wf-env-omval g wf-omval-lam) = wf-omval-lam
wf-lookup here (wf-env-omval g (wf-omval-pair x₁ x₂)) = wf-omval-pair (wf-omval-wk-omval x₁ (wf-omval-pair x₁ x₂)) (wf-omval-wk-omval x₂ (wf-omval-pair x₁ x₂))
wf-lookup here (wf-env-omval g wf-omval-label-h) = wf-omval-label-t-omval wf-omval-label-h
wf-lookup here (wf-env-omval g (wf-omval-label-t-omval x)) = wf-omval-label-t-omval (wf-omval-label-t-omval x)
wf-lookup here (wf-env-omval g (wf-omval-label-t-jump x)) = wf-omval-label-t-omval (wf-omval-label-t-jump x)
wf-lookup here (wf-env-jump x) = wf-omval-label-h
wf-lookup (there i) (wf-env-omval g x) = wf-omval-wk-omval (wf-lookup i g) x
wf-lookup (there i) (wf-env-jump (wf-state-bottom _ γ π x)) = wf-omval-wk-jump (wf-lookup i x)
wf-lookup (there i) (wf-env-jump (wf-state-resume _ x x₁ x₂)) = wf-omval-wk-jump (wf-lookup i x₂)

wf-lookup-label : {γ : MEnv Γ} → (i : Γ ∋ `ℓ) → (g : WellFormedTMEnv γ) → WellFormedTMCState (lookup-label i γ)
wf-lookup-label {γ = γ · (label x)} here (wf-env-omval g x₁) = wf-lookup-label x g
wf-lookup-label here (wf-env-jump x) = x
wf-lookup-label (there i) (wf-env-omval g x) = wf-lookup-label i g
wf-lookup-label (there i) (wf-env-jump (wf-state-bottom M γ π x)) = wf-lookup-label i x
wf-lookup-label (there i) (wf-env-jump (wf-state-resume _ x x₁ x₂)) = wf-lookup-label i x₂

wf-eval : {γ : MEnv Γ} → (W : Γ ⊢ᵛ X) → (g : WellFormedTMEnv γ) → WellFormedTOMVal γ (eval W γ)
wf-eval (var i) (wf-env-omval g x) = wf-lookup i (wf-env-omval g x)
wf-eval (var i) (wf-env-jump x) = wf-lookup i (wf-env-jump x)
wf-eval (lam x) wf-env-empty = wf-omval-lam
wf-eval (lam x) (wf-env-omval g x₁) = wf-omval-lam
wf-eval (lam x) (wf-env-jump x₁) = wf-omval-lam
wf-eval (pair W W₁) wf-env-empty = wf-omval-pair (wf-eval W wf-env-empty) (wf-eval W₁ wf-env-empty)
wf-eval (pair W W₁) (wf-env-omval g x) = wf-omval-pair (wf-eval W (wf-env-omval g x)) (wf-eval W₁ (wf-env-omval g x))
wf-eval (pair W W₁) (wf-env-jump x) = wf-omval-pair (wf-eval W (wf-env-jump x)) (wf-eval W₁ (wf-env-jump x))
wf-eval unit wf-env-empty = wf-omval-unit
wf-eval unit (wf-env-omval g x) = wf-omval-unit
wf-eval unit (wf-env-jump x) = wf-omval-unit

wf-proj₁ : {γ : MEnv Γ} {𝐖 : OMVal Γ (X `× Y)} → WellFormedTOMVal γ 𝐖 → WellFormedTOMVal γ (proj₁-omval 𝐖)
wf-proj₁ (wf-omval-pair w₁ w₂) = w₁

wf-proj₂ : {γ : MEnv Γ} {𝐖 : OMVal Γ (X `× Y)} → WellFormedTOMVal γ 𝐖 → WellFormedTOMVal γ (proj₂-omval 𝐖)
wf-proj₂ (wf-omval-pair w₁ w₂) = w₂

wf-eval₁ : {γ : MEnv Γ} → (W : Γ ⊢ᵛ (X `× Y)) → (g : WellFormedTMEnv γ) → WellFormedTOMVal γ (eval₁ W γ)
wf-eval₁ W g = wf-proj₁ (wf-eval W g)

wf-eval₂ : {γ : MEnv Γ} → (W : Γ ⊢ᵛ (X `× Y)) → (g : WellFormedTMEnv γ) → WellFormedTOMVal γ (eval₂ W γ)
wf-eval₂ W g = wf-proj₂ (wf-eval W g)

wf-jump : {γ : MEnv Γ} → (i : Γ ∋ `ℓ) → (g : WellFormedTMEnv γ) → WellFormedTMCState (eval-jump (var i) γ)
wf-jump i g = wf-lookup-label i g

wf-preservation : {σ σ₁ : CState} → (σ →ᶜ σ₁) → WellFormedTMCState σ → WellFormedTMCState σ₁
wf-preservation eval→ (wf-state-bottom (return W) γ π g) = wf-state-halt _ γ π g (wf-eval W g)
wf-preservation eval→ (wf-state-resume (return W) x x₁ g) = wf-state-result _ x x₁ g (wf-eval W g)
wf-preservation (return→ {K = ◻}) (wf-state-result 𝐖 x (wf-bottom M γ π x₁) g w) = wf-state-bottom _ (_ · 𝐖) _ (wf-env-omval g w)
wf-preservation (return→ {K = < x₂ ； γ ； π >∷ K}) (wf-state-result 𝐖 ϖ₁ (wf-next _ _ ϖ₂ x₃ g₁) g₂ w) = wf-state-resume _ (wk-tmenv-omval-wk 𝐖 (wk-MEnvᵀ-trans ϖ₁ ϖ₂)) x₃ (wf-env-omval g₂ w)
wf-preservation push→ (wf-state-bottom M γ π g) = wf-state-resume _ (wk-MEnvᵀ-id γ) (wf-bottom _ γ π g) g
wf-preservation push→ (wf-state-resume _ x x₁ g) = wf-state-resume _ (wk-MEnvᵀ-id _) (wf-next _ _ x x₁ g) g
wf-preservation sub→ (wf-state-bottom M γ π g) = wf-state-bottom _ (γ ·﹝ _ ╎ π ╎ ◻ ﹞) (wk-wk π) (wf-env-jump (wf-state-bottom _ γ π g))
wf-preservation sub→ (wf-state-resume _ x x₁ g) = wf-state-resume _ (wk-tmenv-jump-wk _ _ _ x) x₁ (wf-env-jump (wf-state-resume _ x x₁ g))
wf-preservation (var→ {W = var i}) (wf-state-bottom M γ π g) = wf-jump i g
wf-preservation (var→ {W = var i}) (wf-state-resume _ x x₁ g) = wf-jump i g
wf-preservation (pmᶜ→ {W = W}) (wf-state-bottom M γ π g) = wf-state-bottom _ (γ · _ · wk-omval (wk-wk wk-id) _) (Wk.wk-wk (Wk.wk-wk π)) (wf-env-omval (wf-env-omval g (wf-eval₁ W g)) (wf-omval-wk-omval (wf-eval₂ W g) (wf-eval₁ W g)))
wf-preservation (pmᶜ→ {W = W}) (wf-state-resume _ x x₁ g) = wf-state-resume _ (wk-tmenv-omval-wk (wk-omval (wk-wk wk-id) _) (wk-tmenv-omval-wk _ x)) x₁ (wf-env-omval (wf-env-omval g (wf-eval₁ W g)) (wf-omval-wk-omval (wf-eval₂ W g) (wf-eval₁ W g)))
wf-preservation app→ (wf-state-bottom (app V W) γ π g) = wf-state-bottom _ (γ · _) (Wk.wk-wk π) (wf-env-omval g (wf-eval W g))
wf-preservation app→ (wf-state-resume (app V W) x x₁ g) = wf-state-resume _ (wk-tmenv-omval-wk _ x) x₁ (wf-env-omval g (wf-eval W g))

init-wf : (M : ε ⊢ᶜ ℛ) → WellFormedTMCState ⟨ M ╎ ⋄ ╎ wk-ε ╎ ◻ ⟩
init-wf M = wf-state-bottom M ⋄ wk-ε wf-env-empty
