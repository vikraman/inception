{-# OPTIONS --no-postfix-projections #-}

open import Inception.Sub.Syntax using (Ty)

module Inception.Sub.Simulation (ℛ : Ty) where

open import Inception.Sub.Syntax
open import Inception.Prelude

open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

import Inception.Sub.Machine ℛ as M
import Inception.Sub.TelescopeMachine ℛ as TM
open M using (⟨_╎_⟩; ⟨_╎_╎_⟩; _·_; ◻; <_；_>∷_; ⋄; eval→; return→; push→; sub→; var→; pmᶜ→; app→; progress) renaming (_→ᶜ_ to _→ᴹ_)
open TM using (⟨_；_╎_╎_⟩; ⟨_╎_╎_╎_⟩; <_；_；_>∷_; _·_; eval→; return→; push→; sub→; var→; pmᶜ→; app→) renaming (_→ᶜ_ to _→ᵀᴹ_)
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


data WkMEnvᴹ : {Γ₁ Γ₂ : Ctx} → (π : Wk Γ₁ Γ₂) → (γ₁ : M.MEnv Γ₁) → (γ₂ : M.MEnv Γ₂) → Set where

    wk-menv-ε    : WkMEnvᴹ wk-ε M.⋄ M.⋄

    wk-menv-cong : {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} → (M : M.MVal X) → WkMEnvᴹ π γ₁ γ₂ → WkMEnvᴹ (wk-cong π) (γ₁ · M) (γ₂ · M)

    wk-menv-wk : {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} → (M : M.MVal X) → WkMEnvᴹ π γ₁ γ₂ → WkMEnvᴹ (wk-wk π) (γ₁ · M) γ₂

wk-menv-id : {γ : M.MEnv Γ} → WkMEnvᴹ wk-id γ γ
wk-menv-id {γ = ⋄} = wk-menv-ε
wk-menv-id {γ = γ · 𝐖} = wk-menv-cong 𝐖 wk-menv-id

data _≈ᴹ_ : M.CState → M.CState → Set where

    ≈-refl : {σ : M.CState} → σ ≈ᴹ σ

    ≈-sym : {σ₁ σ₂ : M.CState} → σ₁ ≈ᴹ σ₂ → σ₂ ≈ᴹ σ₁

    ≈-wk : {Γ₁ Γ₂ : Ctx} {π : Wk Γ₁ Γ₂} {M : Comp Γ₂ X} {γ₁ : M.MEnv Γ₁} {γ₂ : M.MEnv Γ₂} {K : M.CStack X} → (WkMEnvᴹ π γ₁ γ₂) → ⟨ M ╎ γ₂ ╎ K ⟩ ≈ᴹ ⟨ wk-comp π M ╎ γ₁ ╎ K ⟩

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

data WellFormedTMCStack : TM.CStack Γ X → Set where

    ◻ : WellFormedTMCStack {Γ = ε} {X = ℛ} TM.◻

    wf-bottom : (M : (Γ ∙ Y) ⊢ᶜ ℛ) → (γ : TM.MEnv Γ) → (π : Wk Γ ε)
                ------------------------------------
                → WellFormedTMCStack (TM.< M ； γ ； π >∷ TM.◻)

    wf-next :  {Γ₁ Γ₂ Γ₃ : Ctx} → (M₁ : (Γ₁ ∙ Z) ⊢ᶜ Y) → {γ₁ : TM.MEnv Γ₁} → (M₂ : (Γ₂ ∙ Y) ⊢ᶜ X) → {γ₂ : TM.MEnv Γ₂}
                → {π₁ : Wk Γ₁ Γ₂} → {π₂ : Wk Γ₂ Γ₃} → WkMEnvᵀ π₁ γ₁ γ₂
                → {K : TM.CStack Γ₃ X} → WellFormedTMCStack (TM.< M₂ ； γ₂ ； π₂ >∷ K)
                ------------------------------------
                → WellFormedTMCStack (TM.< M₁ ； γ₁ ； π₁ >∷ TM.< M₂ ； γ₂ ； π₂ >∷ K)

data WellFormedTMCState : TM.CState → Set where

     wf-state-halt : (𝐖 : TM.MClo Γ ℛ) → (γ : TM.MEnv Γ) → (π : Wk Γ ε)
                ------------------------------------
                → WellFormedTMCState TM.⟨ 𝐖 ； γ ╎ π ╎ TM.◻ ⟩

     wf-state-result : {Γ₁ Γ₂ Γ₃ : Ctx} {γ₁ : TM.MEnv Γ₁}
                {γ₂ : TM.MEnv Γ₂} {π₁ : Wk Γ₁ Γ₂} → {π₂ : Wk Γ₂ Γ₃}
                {M : Comp (Γ₂ ∙ X) Y} {K : TM.CStack Γ₃ Y}
                → (𝐖 : TM.MClo Γ₁ X)
                → WkMEnvᵀ π₁ γ₁ γ₂
                → WellFormedTMCStack (TM.< M ； γ₂ ； π₂ >∷ K)
                ------------------------------------
                → WellFormedTMCState TM.⟨ 𝐖 ； γ₁ ╎ π₁ ╎ TM.< M ； γ₂ ； π₂ >∷ K ⟩

     wf-state-bottom : (M : Comp Γ ℛ) → (γ : TM.MEnv Γ) → (π : Wk Γ ε)
                ------------------------------------
                → WellFormedTMCState TM.⟨ M ╎ γ ╎ π ╎ TM.◻ ⟩

     wf-state-resume : {Γ₁ Γ₂ Γ₃ : Ctx} {γ₁ : TM.MEnv Γ₁}
                {γ₂ : TM.MEnv Γ₂} {π₁ : Wk Γ₁ Γ₂} → {π₂ : Wk Γ₂ Γ₃}
                {M₂ : Comp (Γ₂ ∙ X) Y} {K : TM.CStack Γ₃ Y}
                → (M₁ : Comp Γ₁ X)
                → WkMEnvᵀ π₁ γ₁ γ₂
                → WellFormedTMCStack (TM.< M₂ ； γ₂ ； π₂ >∷ K)
                ------------------------------------
                → WellFormedTMCState TM.⟨ M₁ ╎ γ₁ ╎ π₁ ╎ TM.< M₂ ； γ₂ ； π₂ >∷ K ⟩

-------------------------------------------------------------------------------------

tmcstate-to-mcstate : TM.CState → M.CState
tmcstate-to-mcstate ⟨ 𝐖 ； γ ╎ π ╎ K ⟩ = ⟨ mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩
tmcstate-to-mcstate ⟨ M ╎ γ ╎ π ╎ K ⟩ = ⟨ M ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩

next-state : {σ : M.CState} → M.Step? σ → M.CState
next-state {σ = σ} (M.done _) = σ
next-state (M.next {b = σ₁} _) = σ₁

tmstep-to-mstep : {σ σ' : TM.CState} → (σ →ᵀᴹ σ') → ((tmcstate-to-mcstate σ) →ᴹ (tmcstate-to-mcstate σ'))
tmstep-to-mstep (eval→ {W = W} {γ = γ} {K = K}) =
  --Goal: ⟨ return W ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩ →ᴹ ⟨ mclo-to-mval (TM.eval W γ) γ ╎ tmcstack-to-mcstack K ⟩
  let
    a0 : M.Step? ⟨ return W ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩
    a0 = progress ⟨ return W ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩
  in
  {!a0!}
tmstep-to-mstep (return→ {𝐖 = 𝐖} {M₁ = M₁} {γ = γ} {γ₁ = γ₁} {K = K} {π = π}) =
  -- Goal: ⟨ mclo-to-mval 𝐖 γ ╎ M.< M₁ ； tmenv-to-menv γ₁ >∷ tmcstack-to-mcstack K ⟩ →ᴹ ⟨ wk-comp (wk-cong π) M₁ ╎ tmenv-to-menv γ M.· mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩
  let
    a0 = progress ⟨ mclo-to-mval 𝐖 γ ╎ M.< M₁ ； tmenv-to-menv γ₁ >∷ tmcstack-to-mcstack K ⟩
    --next = next-state a0
    next = ⟨ M₁ ╎ tmenv-to-menv γ₁ · mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩

    eqv : ⟨ M₁ ╎ tmenv-to-menv γ₁ · mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩ ≈ᴹ ⟨ wk-comp (wk-cong π) M₁ ╎ tmenv-to-menv γ M.· mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩
    eqv = ≈-wk (wk-menv-cong (mclo-to-mval 𝐖 γ) {!!})
  in
  {!!}
tmstep-to-mstep push→ = push→
tmstep-to-mstep sub→ = sub→
tmstep-to-mstep (var→ {W = W} {γ = γ} {K = K}) =
  -- Goal: ⟨ var W ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩ →ᴹ tmcstate-to-mcstate (TM.eval-jump W γ)
  let
    a0 = progress ⟨ var W ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩
  in
  {!a0!}
tmstep-to-mstep (pmᶜ→ {W = W} {γ = γ} {M = M} {K = K}) =
  -- Goal: ⟨ pm W M ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩ →ᴹ ⟨ M ╎ tmenv-to-menv γ M.· mclo-to-mval (TM.eval₁ W γ) γ M.· mclo-to-mval (TM.wk-mclo (wk-wk wk-id) (TM.eval₂ W γ)) (γ TM.· TM.eval₁ W γ) ╎ tmcstack-to-mcstack K ⟩
  let
    a0 = progress ⟨ pm W M ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩
  in
  {!a0!}
tmstep-to-mstep (app→ {W₁ = W₁} {W₂ = W₂} {γ = γ} {K = K}) =
  -- Goal: ⟨ app W₁ W₂ ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩ →ᴹ ⟨ TM.lam-to-comp (TM.eval W₁ γ) ╎ tmenv-to-menv γ M.· mclo-to-mval (TM.eval W₂ γ) γ ╎ tmcstack-to-mcstack K ⟩
  let
    a0 = progress ⟨ app W₁ W₂ ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩
  in
  {!a0!}
