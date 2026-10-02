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
open M using (⟨_╎_⟩; ⟨_╎_╎_⟩)
open TM using (⟨_；_╎_╎_⟩; ⟨_╎_╎_╎_⟩)


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
