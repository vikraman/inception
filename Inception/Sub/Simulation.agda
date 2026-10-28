{-# OPTIONS --no-postfix-projections #-}

open import Inception.Sub.Syntax using (Ty)

module Inception.Sub.Simulation (ℛ : Ty) where

open import Inception.Prelude
open import Inception.Rewriting
open import Inception.Sub.Syntax

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)

open import Inception.Sub.Machine ℛ as M renaming (_→ᶜ_ to _→ᴹ_)
open import Inception.Sub.TelescopeMachine ℛ as TM renaming (_→ᶜ_ to _→ᵀᴹ_)

open import Inception.Sub.MachineProps ℛ
open import Inception.Sub.TelescopeMachineProps ℛ

open import Inception.Sub.TelescopeTranslation ℛ

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
progress-t (≈-trans {σ₂ = σ₂} {σ₃ = σ₃} w eqv) s = progress-t {σ₀ᴹ = σ₂} eqv (proj₁ (proj₂ (mstep-eqv′ w s)))

execᵀᴹ-rec : {σ₀ : TM.CState} {σ₀ᴹ σᴹ : M.CState} → (WellFormedTMCState σ₀) → ((tmcstate-to-mcstate σ₀) ≈ᴹ σ₀ᴹ) → (σ₀ᴹ →ᴹ* σᴹ) → Σ[ σ ∈ TM.CState ] ((σ₀ →ᵀᴹ* σ) × ((tmcstate-to-mcstate σ) ≈ᴹ σᴹ) × WellFormedTMCState σ)
execᵀᴹ-rec {σ₀ = σ₀} wf eqv ε = σ₀ , ε , eqv , wf
execᵀᴹ-rec wf eqv (σ₀ᴹ→σ₁ᴹ ◅ σ₁ᴹ→*σᴹ) =
  let
    σ₀→ᵀᴹσ₁ = proj₂ (progress-t (≈ᴹ-sym eqv) σ₀ᴹ→σ₁ᴹ)
    me = mstep-eqv (≈ᴹ-sym eqv) σ₀ᴹ→σ₁ᴹ
    eqv = tmstep-to-mstep-eqv wf σ₀→ᵀᴹσ₁ (proj₁ (proj₂ me))
    wf′ = wf-preservation σ₀→ᵀᴹσ₁ wf
    IH = execᵀᴹ-rec wf′ (≈ᴹ-sym (≈ᴹ-trans (proj₂ (proj₂ me)) eqv))  σ₁ᴹ→*σᴹ
  in
  proj₁ IH , σ₀→ᵀᴹσ₁ ◅ proj₁ (proj₂ IH) , proj₁ (proj₂ (proj₂ IH)) , proj₂ (proj₂ (proj₂ IH))

normal-t : {σ : TM.CState} {σᴹ : M.CState} → WellFormedTMCState σ → Normalᴹ σᴹ → ((tmcstate-to-mcstate σ) ≈ᴹ σᴹ) → Normalᵀᴹ σ
normal-t {σ = σ} {σᴹ = σᴹ} wf n eqv s = n (proj₁ (proj₂ (mstep-eqv eqv (proj₁ (proj₂ (tmstep-to-mstep wf s))))))

execᵀᴹ :    (M : ε ⊢ᶜ ℛ)
        → Σ[ σ ∈ TM.CState ]
          Σ[ NF ∈ Normalᵀᴹ σ ]
          TM.⟨ M ╎ ⋄ ╎ wk-ε ╎ TM.◻ ⟩ →ᵀᴹ* σ
execᵀᴹ M =
  let
    wf = init-wf M
    mexec = M.exec M
    t = execᵀᴹ-rec wf (≈ᴹ-bc (≈-wk₂ (wk-cstate-comp wk-ε refl wk-menv-ε wk-cstack-empty))) (proj₁ (proj₂ (proj₂ (proj₂ mexec))))
  in
  proj₁ t , normal-t (proj₂ (proj₂ (proj₂ t))) (proj₁ (proj₂ (proj₂ mexec))) (proj₁ (proj₂ (proj₂ t))) , proj₁ (proj₂ t)
