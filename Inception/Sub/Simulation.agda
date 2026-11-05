{-# OPTIONS --no-postfix-projections #-}

open import Inception.Sub.Syntax using (Ty)

module Inception.Sub.Simulation (ℛ : Ty) where

open import Inception.Prelude
open import Inception.Rewriting
open import Inception.Sub.Syntax

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; trans; sym)

open import Inception.Sub.Machine ℛ as M renaming (_→ᶜ_ to _→ᴹ_)
open import Inception.Sub.TelescopeMachine ℛ as TM renaming (_→ᶜ_ to _→ᵀᴹ_)
open import Inception.Sub.GCMachine ℛ as GCM renaming (_→ᶜ_ to _→ᴳ_)

open import Inception.Sub.MachineProps ℛ as MProps
open import Inception.Sub.TelescopeMachineProps ℛ as TMProps

open import Inception.Sub.TelescopeTranslation ℛ

open Reduction _→ᴹ_ renaming (_~>*_ to _→ᴹ*_; Normal to Normalᴹ; Step? to Step?ᴹ)
open Reduction _→ᵀᴹ_ renaming (_~>*_ to _→ᵀᴹ*_; Normal to Normalᵀᴹ; Step? to Step?ᵀᴹ)
open Reduction _→ᴳ_ renaming (_~>*_ to _→ᴳ*_; Normal to Normalᴳ; Step? to Step?ᴳ)

progress-t₁ : {σ₀ : TM.CState} {σ₀ᴹ σᴹ : M.CState} → (MProps.WkCState (tmcstate-to-mcstate σ₀) σ₀ᴹ) → (σ₀ᴹ →ᴹ σᴹ) → Σ[ σ ∈ TM.CState ] (σ₀ →ᵀᴹ σ)
progress-t₁ {σ₀ = ⟨ 𝐖 ； γ ╎ π ╎ ◻ ⟩} ((wk-cstate-result x ())) return→
progress-t₁ {σ₀ = ⟨ 𝐖 ； γ ╎ π ╎ TM.< x₂ ； δ ； ρ >∷ K ⟩} ((wk-cstate-result x x₁)) return→ = ⟨ wk-comp (wk-cong π) x₂ ╎ γ · 𝐖 ╎ wk-wk (wk-trans π ρ) ╎ K ⟩ , return→
progress-t₁ {σ₀ = ⟨ return x ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp ρ refl x₁ x₂)) eval→ = _ , eval→
progress-t₁ {σ₀ = ⟨ pm x M ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp ρ refl x₁ x₂)) pmᶜ→ = _ , pmᶜ→
progress-t₁ {σ₀ = ⟨ push M N ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp ρ refl x₁ x₂)) push→ = _ , push→
progress-t₁ {σ₀ = ⟨ app x x₃ ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp ρ refl x₁ x₂)) app→ = _ , app→
progress-t₁ {σ₀ = ⟨ var x ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp ρ refl x₁ x₂)) var→ = _ , var→
progress-t₁ {σ₀ = ⟨ sub M N ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp ρ refl x₁ x₂)) sub→ = _ , sub→

progress-t₂ : {σ₀ : TM.CState} {σ₀ᴹ σᴹ : M.CState} → (MProps.WkCState σ₀ᴹ (tmcstate-to-mcstate σ₀)) → (σ₀ᴹ →ᴹ σᴹ) → Σ[ σ ∈ TM.CState ] (σ₀ →ᵀᴹ σ)
progress-t₂ {σ₀ = ⟨ 𝐖 ； γ ╎ π ╎ ◻ ⟩} ((wk-cstate-result x ())) return→
progress-t₂ {σ₀ = ⟨ 𝐖 ； γ ╎ π ╎ < x₂ ； δ ； ρ >∷ K ⟩} ((wk-cstate-result x x₁)) return→ = ⟨ wk-comp (wk-cong π) x₂ ╎ γ · 𝐖 ╎ wk-wk (wk-trans π ρ) ╎ K ⟩ , return→
progress-t₂ {σ₀ = ⟨ return x₃ ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp ρ refl x₁ x₂)) eval→ = _ , eval→
progress-t₂ {σ₀ = ⟨ pm x₃ M ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp ρ refl x₁ x₂)) pmᶜ→ = _ , pmᶜ→
progress-t₂ {σ₀ = ⟨ push M N ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp ρ refl x₁ x₂)) push→ = _ , push→
progress-t₂ {σ₀ = ⟨ app x₃ x₄ ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp ρ refl x₁ x₂)) app→ = _ , app→
progress-t₂ {σ₀ = ⟨ var x₃ ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp ρ refl x₁ x₂)) var→ = _ , var→
progress-t₂ {σ₀ = ⟨ sub M N ╎ γ ╎ π ╎ K ⟩} ((wk-cstate-comp ρ refl x₁ x₂)) sub→ = _ , sub→

progress-t : {σ₀ : TM.CState} {σ₀ᴹ σᴹ : M.CState} → (σ₀ᴹ ≈ᴹ (tmcstate-to-mcstate σ₀)) → (σ₀ᴹ →ᴹ σᴹ) → Σ[ σ ∈ TM.CState ] (σ₀ →ᵀᴹ σ)
progress-t (≈ᴹ-bc (≈-wk₁ w)) s = progress-t₁ w s
progress-t (≈ᴹ-bc (≈-wk₂ w)) s = progress-t₂ w s
progress-t (≈-trans {σ₂ = σ₂} {σ₃ = σ₃} w eqv) s = progress-t {σ₀ᴹ = σ₂} eqv (proj₁ (proj₂ (mstep-eqv₀ w s)))

normal-t : {σ : TM.CState} {σᴹ : M.CState} → WellFormedCState σ → Normalᴹ σᴹ → ((tmcstate-to-mcstate σ) ≈ᴹ σᴹ) → Normalᵀᴹ σ
normal-t {σ = σ} {σᴹ = σᴹ} wf n eqv s = n (proj₁ (proj₂ (mstep-eqv eqv (proj₁ (proj₂ (tmstep-to-mstep wf s))))))

mutual
  execᵀᴹ-step : {σ₀ : TM.CState} → Step?ᵀᴹ σ₀ → {σ₀ᴹ σᴹ : M.CState} → (σ₀ᴹ →ᴹ* σᴹ) → Σ[ σ ∈ TM.CState ] (σ₀ →ᵀᴹ* σ)
  execᵀᴹ-step {σ₀ = σ₀} (done _) _ = σ₀ , ε
  execᵀᴹ-step (next {b = σ} t) ss = let u = execᵀᴹ-quick-rec σ ss in proj₁ u , t ◅ proj₂ u

  execᵀᴹ-quick-rec : (σ₀ : TM.CState) → {σ₀ᴹ σᴹ : M.CState} → (σ₀ᴹ →ᴹ* σᴹ) → Σ[ σ ∈ TM.CState ] (σ₀ →ᵀᴹ* σ)
  execᵀᴹ-quick-rec σ ε = σ , ε
  execᵀᴹ-quick-rec σ (s ◅ ss) = execᵀᴹ-step (TM.progress σ) ss

execᵀᴹ-quick : (M : ε ⊢ᶜ ℛ) → Σ[ σ ∈ TM.CState ] TM.⟨ M ╎ ⋄ ╎ wk-ε ╎ TM.◻ ⟩ →ᵀᴹ* σ
execᵀᴹ-quick M = execᵀᴹ-quick-rec TM.⟨ M ╎ ⋄ ╎ wk-ε ╎ TM.◻ ⟩ (proj₁ (proj₂ (proj₂ (proj₂ (M.exec M)))))


e-lem : {σ₀ σ₁ : TM.CState} → (σ₀ →ᵀᴹ σ₁) → {σ₀ᴹ σ₁ᴹ σᴹ : M.CState} → (sᴹ : σ₀ᴹ →ᴹ σ₁ᴹ) → (ssᴹ : σ₁ᴹ →ᴹ* σᴹ) → proj₁ (execᵀᴹ-quick-rec σ₀ (sᴹ ◅ ssᴹ)) ≡ proj₁ (execᵀᴹ-quick-rec σ₁ ssᴹ)
e-lem eval→ sᴹ ssᴹ = refl
e-lem return→ sᴹ ssᴹ = refl
e-lem push→ sᴹ ssᴹ = refl
e-lem sub→ sᴹ ssᴹ = refl
e-lem var→ sᴹ ssᴹ = refl
e-lem pmᶜ→ sᴹ ssᴹ = refl
e-lem app→ sᴹ ssᴹ = refl

execᵀᴹ-correct-rec : {σ₀ : TM.CState} {σ₀ᴹ σᴹ : M.CState} → (WellFormedCState σ₀) → ((tmcstate-to-mcstate σ₀) ≈ᴹ σ₀ᴹ) → (s : σ₀ᴹ →ᴹ* σᴹ) → Σ[ σ ∈ TM.CState ] (σ ≡ (proj₁ (execᵀᴹ-quick-rec σ₀ s)) × (σ₀ →ᵀᴹ* σ) × ((tmcstate-to-mcstate σ) ≈ᴹ σᴹ) × WellFormedCState σ)
execᵀᴹ-correct-rec {σ₀ = σ₀} wf eqv ε = σ₀ , refl , ε , eqv , wf
execᵀᴹ-correct-rec {σ₀ = σ₀} wf eqv (σ₀ᴹ→σ₁ᴹ ◅ σ₁ᴹ→*σᴹ) =
  let
    σ₀→ᵀᴹσ₁ = proj₂ (progress-t (≈ᴹ-sym eqv) σ₀ᴹ→σ₁ᴹ)
    me = mstep-eqv (≈ᴹ-sym eqv) σ₀ᴹ→σ₁ᴹ
    eqv₁ = tmstep-to-mstep-eqv wf σ₀→ᵀᴹσ₁ (proj₁ (proj₂ me))
    wf′ = wf-preservation σ₀→ᵀᴹσ₁ wf
    IH = execᵀᴹ-correct-rec wf′ (≈ᴹ-sym (≈ᴹ-trans (proj₂ (proj₂ me)) eqv₁))  σ₁ᴹ→*σᴹ
    a = proj₁ (proj₂ IH)
    eq : proj₁ (execᵀᴹ-quick-rec σ₀ (σ₀ᴹ→σ₁ᴹ ◅ σ₁ᴹ→*σᴹ)) ≡ proj₁ (execᵀᴹ-quick-rec (proj₁ (progress-t (≈ᴹ-sym eqv) σ₀ᴹ→σ₁ᴹ)) σ₁ᴹ→*σᴹ)
    eq = e-lem σ₀→ᵀᴹσ₁ σ₀ᴹ→σ₁ᴹ σ₁ᴹ→*σᴹ
  in
  proj₁ IH , trans a (sym eq) , σ₀→ᵀᴹσ₁ ◅ proj₁ (proj₂ (proj₂ IH)) , proj₁ (proj₂ (proj₂ (proj₂ IH))) , proj₂ (proj₂ (proj₂ (proj₂ IH)))

execᵀᴹ-correct :    (M : ε ⊢ᶜ ℛ)
        → Σ[ σ ∈ TM.CState ]
          Σ[ NF ∈ Normalᵀᴹ σ ]
          σ ≡ (proj₁ (execᵀᴹ-quick M)) ×
          TM.⟨ M ╎ ⋄ ╎ wk-ε ╎ TM.◻ ⟩ →ᵀᴹ* σ
execᵀᴹ-correct M =
  let
    wf = init-wf M
    mexec = M.exec M
    t = execᵀᴹ-correct-rec wf (≈ᴹ-bc (≈-wk₂ (wk-cstate-comp wk-ε refl wk-menv-ε wk-cstack-empty))) (proj₁ (proj₂ (proj₂ (proj₂ mexec))))
  in
  proj₁ t , normal-t (proj₂ (proj₂ (proj₂ (proj₂ t)))) (proj₁ (proj₂ (proj₂ mexec))) (proj₁ (proj₂ (proj₂ (proj₂ t)))) , proj₁ (proj₂ t) , proj₁ (proj₂ (proj₂ t))


execᵀᴹ :    (M : ε ⊢ᶜ ℛ)
        → Σ[ σ ∈ TM.CState ]
          Σ[ NF ∈ Normalᵀᴹ σ ]
          TM.⟨ M ╎ ⋄ ╎ wk-ε ╎ TM.◻ ⟩ →ᵀᴹ* σ
execᵀᴹ M =
  let
    exec₁ = execᵀᴹ-quick M
    exec₂ = execᵀᴹ-correct M
    n = proj₁ (proj₂ exec₂)
    eq = proj₁ (proj₂ (proj₂ exec₂))
  in
  proj₁ exec₁ , subst (λ x → Normalᵀᴹ x) eq n , proj₂ exec₁

--------------------------------------------------------------------------

mutual
  execᴳ-step : {σ₀ : GCM.CState} → Step?ᴳ σ₀ → {σ₀ᴹ σᴹ : M.CState} → (σ₀ᴹ →ᴹ* σᴹ) → Σ[ σ ∈ GCM.CState ] (σ₀ →ᴳ* σ)
  execᴳ-step {σ₀ = σ₀} (done _) _ = σ₀ , ε
  execᴳ-step (next {b = σ} t) ss = let u = execᴳ-quick-rec σ ss in proj₁ u , t ◅ proj₂ u

  execᴳ-quick-rec : (σ₀ : GCM.CState) → {σ₀ᴹ σᴹ : M.CState} → (σ₀ᴹ →ᴹ* σᴹ) → Σ[ σ ∈ GCM.CState ] (σ₀ →ᴳ* σ)
  execᴳ-quick-rec σ ε = σ , ε
  execᴳ-quick-rec σ (s ◅ ss) = execᴳ-step (GCM.progress σ) ss

wkext-ε : WkExt wk-ε
wkext-ε = wkext-id

execᴳ-quick : (M : ε ⊢ᶜ ℛ) → Σ[ σ ∈ GCM.CState ] GCM.⟨ ⋄ ╎ M ╎ wkext-ε ╎ GCM.◻ ⟩ →ᴳ* σ
execᴳ-quick M = execᴳ-quick-rec GCM.⟨ ⋄ ╎ M ╎ wkext-ε ╎ GCM.◻ ⟩ (proj₁ (proj₂ (proj₂ (proj₂ (M.exec M)))))
