\begin{code}

{-# OPTIONS --no-postfix-projections #-}

module Inception.IncV.Syntax where

open import Inception.Prelude

open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Empty using (⊥)

open import Data.Nat

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; cong₂)
open Eq.≡-Reasoning

---------------------------------------------------------------------------------

infixr 40 _`×_
infixr 25 _`⇒_

data Ty : Set where
  `𝟙 : Ty
  _`×_ _`⇒_ : Ty → Ty → Ty
  `ℓ `𝓅 : Ty

open import Inception.Ctx Ty public

syntax Val Γ X = Γ ⊢ᵛ X

data Val : Ctx → Ty → Set

syntax Comp Γ X = Γ ⊢ᶜ X

data Comp : Ctx → Ty → Set

\end{code}
%<*Val>
\begin{code}

data Val where

  var :   (x : Γ ∋ X)
          ----------
          → Γ ⊢ᵛ X

  lam :   (Γ ∙ X) ⊢ᶜ Y
          --------------
          → Γ ⊢ᵛ X `⇒ Y

  pair :  Γ ⊢ᵛ X₁ → Γ ⊢ᵛ X₂
          -----------------
          → Γ ⊢ᵛ X₁ `× X₂

  unit :
          -----------
          Γ ⊢ᵛ `𝟙


  dat :   (N : ℕ)
          -----------
          → Γ ⊢ᵛ `𝓅

\end{code}
%</Val>
\begin{code}

\end{code}
%<*Comp>
\begin{code}

data Comp where

  return :  Γ ⊢ᵛ X
            ---------
            → Γ ⊢ᶜ X

  pm :      Γ ⊢ᵛ X₁ `× X₂ → (Γ ∙ X₁ ∙ X₂) ⊢ᶜ Y
            -------------------------------
            → Γ ⊢ᶜ Y

  push :    Γ ⊢ᶜ X → (Γ ∙ X) ⊢ᶜ Y
            --------------------
            → Γ ⊢ᶜ Y

  app :     Γ ⊢ᵛ X `⇒ Y → Γ ⊢ᵛ X
            ---------------------
            → Γ ⊢ᶜ Y

  rec :     Γ ⊢ᵛ `ℓ → Γ ⊢ᵛ `𝓅
            ------------------
            → Γ ⊢ᶜ X

  inc :     (Γ ∙ `ℓ) ⊢ᶜ X → (Γ ∙ `𝓅) ⊢ᶜ X
            -------------------------------
            → Γ ⊢ᶜ X

\end{code}
%</Comp>
\begin{code}

mutual
  wk-val : Wk Γ Δ → Δ ⊢ᵛ X → Γ ⊢ᵛ X
  wk-val π (var x)    = var (wk-mem π x)
  wk-val π (lam M)    = lam (wk-comp (wk-cong π) M)
  wk-val π (pair V W) = pair (wk-val π V) (wk-val π W)
  wk-val π unit       = unit
  wk-val π (dat N)    = dat N

  wk-comp : Wk Γ Δ → Δ ⊢ᶜ X → Γ ⊢ᶜ X
  wk-comp π (return W) = return (wk-val π W)
  wk-comp π (pm W M)   = pm (wk-val π W) (wk-comp (wk-cong (wk-cong π)) M)
  wk-comp π (push M N) = push (wk-comp π M) (wk-comp (wk-cong π) N)
  wk-comp π (app V W)  = app (wk-val π V) (wk-val π W)
  wk-comp π (rec V W)  = rec (wk-val π V) (wk-val π W)
  wk-comp π (inc M N)  = inc (wk-comp (wk-cong π) M) (wk-comp (wk-cong π) N)

wk : Val Γ X → Val (Γ ∙ Y) X
wk = wk-val (wk-wk wk-id)

\end{code}
