\begin{code}

{-# OPTIONS --no-postfix-projections #-}

open import Inception.IncV.Data

module Inception.IncV.Syntax (𝒜 : Alg) where

open import Inception.Prelude

open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)

open import Data.List
open import Data.Vec

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; cong₂)
open Eq.≡-Reasoning

𝒟 = Alg.𝒟 𝒜
𝒪 = Alg.𝒪 𝒜
∣_∣ = Alg.∣_∣ 𝒜
apply = Alg.apply 𝒜

--------------------------------------------------------------------------

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


  dat :   (D : 𝒟)
          -----------
          → Γ ⊢ᵛ `𝓅

  op :    (o : 𝒪) → (args : Vec 𝒟 ∣ o ∣)
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
  wk-val π (op o a)    = op o a

  wk-comp : Γ ⊇ Δ → Δ ⊢ᶜ X → Γ ⊢ᶜ X
  wk-comp π (return W) = return (wk-val π W)
  wk-comp π (pm W M)   = pm (wk-val π W) (wk-comp (wk-cong (wk-cong π)) M)
  wk-comp π (push M N) = push (wk-comp π M) (wk-comp (wk-cong π) N)
  wk-comp π (app V W)  = app (wk-val π V) (wk-val π W)
  wk-comp π (rec V W)  = rec (wk-val π V) (wk-val π W)
  wk-comp π (inc M N)  = inc (wk-comp (wk-cong π) M) (wk-comp (wk-cong π) N)

wk : Γ ⊢ᵛ X → (Γ ∙ Y) ⊢ᵛ X
wk = wk-val (wk-wk wk-id)

mutual
  wk-val-id-β : (V : Γ ⊢ᵛ X) → wk-val wk-id V ≡ V
  wk-val-id-β (var i)    = refl
  wk-val-id-β (lam M)    = cong lam (wk-comp-id-β M)
  wk-val-id-β (pair V W) = cong₂ pair (wk-val-id-β V) (wk-val-id-β W)
  wk-val-id-β unit       = refl
  wk-val-id-β (dat D)    = refl
  wk-val-id-β (op o a)   = refl

  wk-comp-id-β : (M : Γ ⊢ᶜ X) → wk-comp wk-id M ≡ M
  wk-comp-id-β (return V) = cong return (wk-val-id-β V)
  wk-comp-id-β (pm V M)   = cong₂ pm (wk-val-id-β V) (wk-comp-id-β M)
  wk-comp-id-β (push M N) = cong₂ push (wk-comp-id-β M) (wk-comp-id-β N)
  wk-comp-id-β (app V W)  = cong₂ app (wk-val-id-β V) (wk-val-id-β W)
  wk-comp-id-β (rec V W)  = cong₂ rec (wk-val-id-β V) (wk-val-id-β W)
  wk-comp-id-β (inc M N)  = cong₂ inc (wk-comp-id-β M) (wk-comp-id-β N)

{-# REWRITE wk-val-id-β wk-comp-id-β #-}

mutual
  wk-val-wk-η : (V : Γ ⊢ᵛ X) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → wk-val π (wk-val δ V) ≡ wk-val (wk-trans π δ) V
  wk-val-wk-η (var i) π δ    = refl
  wk-val-wk-η (lam M) π δ    = cong lam (wk-comp-wk-η M (wk-cong π) (wk-cong δ))
  wk-val-wk-η (pair V W) π δ = cong₂ pair (wk-val-wk-η V π δ) (wk-val-wk-η W π δ)
  wk-val-wk-η unit π δ       = refl
  wk-val-wk-η (dat D) π δ    = refl
  wk-val-wk-η (op o a) π δ   = refl

  wk-comp-wk-η : (M : Γ ⊢ᶜ X) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → wk-comp π (wk-comp δ M) ≡ wk-comp (wk-trans π δ) M
  wk-comp-wk-η (return V) π δ = cong return (wk-val-wk-η V π δ)
  wk-comp-wk-η (pm V M) π δ   = cong₂ pm (wk-val-wk-η V π δ) (wk-comp-wk-η M (wk-cong (wk-cong π)) (wk-cong (wk-cong δ)))
  wk-comp-wk-η (push M N) π δ = cong₂ push (wk-comp-wk-η M π δ) (wk-comp-wk-η N (wk-cong π) (wk-cong δ))
  wk-comp-wk-η (app V W) π δ  = cong₂ app (wk-val-wk-η V π δ) (wk-val-wk-η W π δ)
  wk-comp-wk-η (rec V W) π δ  = cong₂ rec (wk-val-wk-η V π δ) (wk-val-wk-η W π δ)
  wk-comp-wk-η (inc M N) π δ  = cong₂ inc (wk-comp-wk-η M (wk-cong π) (wk-cong δ)) (wk-comp-wk-η N (Wk.wk-cong π) (wk-cong δ))

{-# REWRITE wk-val-wk-η wk-comp-wk-η #-}

mutual
  wk-val-ε-η : (V : ε ⊢ᵛ X) → wk-val wk-ε V ≡ V
  wk-val-ε-η V = wk-val-id-β V

  wk-comp-ε-η : (M : ε ⊢ᶜ X) → wk-comp wk-ε M ≡ M
  wk-comp-ε-η M = wk-comp-id-β M

{-# REWRITE wk-val-ε-η wk-comp-ε-η #-}

\end{code}
