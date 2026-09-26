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

  var :   (i : Γ ∋ X)
          ----------
          → Γ ⊢ᵛ X

  lam :   (Γ ∙ X) ⊢ᶜ Y
          --------------
          → Γ ⊢ᵛ X `⇒ Y

  pair :  Γ ⊢ᵛ X → Γ ⊢ᵛ Y
          -----------------
          → Γ ⊢ᵛ X `× Y

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

  pm :      Γ ⊢ᵛ X `× Z → (Γ ∙ X ∙ Z) ⊢ᶜ Y
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
  wk-val : Γ ⊇ Δ → Δ ⊢ᵛ X → Γ ⊢ᵛ X
  wk-val π (var i)    = var (wk-mem π i)
  wk-val π (lam M)    = lam (wk-comp (wk-cong π) M)
  wk-val π (pair V W) = pair (wk-val π V) (wk-val π W)
  wk-val π unit       = unit
  wk-val π (dat N)    = dat N

  wk-comp : Γ ⊇ Δ → Δ ⊢ᶜ X → Γ ⊢ᶜ X
  wk-comp π (return W) = return (wk-val π W)
  wk-comp π (pm W M)   = pm (wk-val π W) (wk-comp (wk-cong (wk-cong π)) M)
  wk-comp π (push M N) = push (wk-comp π M) (wk-comp (wk-cong π) N)
  wk-comp π (app V W)  = app (wk-val π V) (wk-val π W)
  wk-comp π (rec V W)  = rec (wk-val π V) (wk-val π W)
  wk-comp π (inc M N)  = inc (wk-comp (wk-cong π) M) (wk-comp (wk-cong π) N)

wk : Γ ⊢ᵛ X → (Γ ∙ Y) ⊢ᵛ X
wk = wk-val (wk-wk wk-id)

\end{code}
