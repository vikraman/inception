\begin{code}
{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.TelescopeMachine where

open import Inception.Sub.Syntax
open import Inception.Prelude

open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

---------------------------------------------------------------------------------

infixl 27 _·_

---------------------------------------------------------------------------------
-- ENVIRONMENTS

\end{code}
%<*Env>
\begin{code}

mutual

  data CStack {ℛ : Ty} : (X : Ty) → Set where

    ◻ :        CStack ℛ

    <_；_>∷_ :  Comp (Γ ∙ Y) X → (γ : MEnvᵀ {ℛ = ℛ} Γ)
                → (pstack : CStack {ℛ = ℛ} X)
                ------------------------------------
                → CStack Y

  data MClo {ℛ : Ty} : Ctx → Ty → Set where

    unit :
              -------------------
              MClo {ℛ = ℛ} Γ `𝟙

    pair :    (𝐖₁ : MClo {ℛ = ℛ} Γ X₁) → (𝐖₂ : MClo {ℛ = ℛ} Γ X₂)
              -------------------------------------------------
              → MClo Γ (X₁ `× X₂)

    lam :     (M : Comp (Γ ∙ X) Y)
              ----------------------------------------------------
              → MClo Γ (X `⇒ Y)

    label :   (i : Γ ∋ `ℓ)
              ----------------------------------------------------
              → MClo Γ `ℓ


  data MEnvᵀ {ℛ : Ty} : Ctx → Set where

    ⋄ :
               --------------
               MEnvᵀ {ℛ = ℛ} ε

    _·_ :      MEnvᵀ {ℛ = ℛ} Γ → MClo {ℛ = ℛ} Γ X
               ----------------------------------
               → MEnvᵀ {ℛ = ℛ} (Γ ∙ X)

    _·﹝_╎_﹞ :  MEnvᵀ {ℛ = ℛ} Γ → Comp Γ X → CStack {ℛ = ℛ} X
               ----------------------------------------------
               → MEnvᵀ {ℛ = ℛ} (Γ ∙ `ℓ)

\end{code}
