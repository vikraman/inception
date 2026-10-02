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
open M using (⟨_╎_⟩; ⟨_╎_╎_⟩; eval→; return→; push→; sub→; var→; pmᶜ→; app→; progress) renaming (_→ᶜ_ to _→ᴹ_)
open TM using (⟨_；_╎_╎_⟩; ⟨_╎_╎_╎_⟩; eval→; return→; push→; sub→; var→; pmᶜ→; app→) renaming (_→ᶜ_ to _→ᵀᴹ_)
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

tmcstate-to-mcstate : TM.CState → M.CState
tmcstate-to-mcstate ⟨ 𝐖 ； γ ╎ π ╎ K ⟩ = ⟨ mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩
tmcstate-to-mcstate ⟨ M ╎ γ ╎ π ╎ K ⟩ = ⟨ M ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩

tmstep-to-mstep : {σ σ' : TM.CState} → (σ →ᵀᴹ σ') → ((tmcstate-to-mcstate σ) →ᴹ (tmcstate-to-mcstate σ'))
tmstep-to-mstep (eval→ {W = W} {γ = γ} {K = K}) =
  --Goal: ⟨ return W ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩ →ᴹ ⟨ mclo-to-mval (TM.eval W γ) γ ╎ tmcstack-to-mcstack K ⟩
  let
    a0 : M.Progress ⟨ return W ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩
    a0 = progress ⟨ return W ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩
  in
  {!a0!}
tmstep-to-mstep (return→ {𝐖 = 𝐖} {M₁ = M₁} {γ = γ} {γ₁ = γ₁} {K = K}) =
  -- Goal: ⟨ mclo-to-mval 𝐖 γ ╎ M.< M₁ ； tmenv-to-menv γ₁ >∷ tmcstack-to-mcstack K ⟩ →ᴹ ⟨ wk-comp (wk-cong π) M₁ ╎ tmenv-to-menv γ M.· mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩
  let
    a0 = progress ⟨ mclo-to-mval 𝐖 γ ╎ M.< M₁ ； tmenv-to-menv γ₁ >∷ tmcstack-to-mcstack K ⟩
  in
  {!a0!}
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
