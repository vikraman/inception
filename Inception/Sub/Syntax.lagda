\begin{code}
{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Syntax where

open import Inception.Prelude

open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; cong₂)
open Eq.≡-Reasoning

--------------------------------------------------------------------------

infixr 40 _`×_
infixr 25 _`⇒_

data Ty : Set where
  `𝟙 : Ty
  _`×_ _`⇒_ : Ty → Ty → Ty
  `ℓ : Ty

open import Inception.Ctx Ty public
open import Inception.Ctx.Sub Ty public


\end{code}
%<*Terms>
\begin{code}

syntax Val Γ X = Γ ⊢ᵛ X
syntax Comp Γ X = Γ ⊢ᶜ X

mutual

  data Val : Ctx → Ty → Set where

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

  data Comp : Ctx → Ty → Set where

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

    var :     Γ ⊢ᵛ `ℓ
              ---------
              → Γ ⊢ᶜ X

    sub :     (Γ ∙ `ℓ) ⊢ᶜ X → Γ ⊢ᶜ X
              --------------------
              → Γ ⊢ᶜ X

\end{code}
%</Terms>
\begin{code}

mutual
  wk-val : Γ ⊇ Δ → Δ ⊢ᵛ X → Γ ⊢ᵛ X
  wk-val π (var i) = var (wk-mem π i)
  wk-val π (lam M) = lam (wk-comp (wk-cong π) M)

  wk-val π (pair V W) = pair (wk-val π V) (wk-val π W)
  wk-val π unit       = unit

  wk-comp : Γ ⊇ Δ → Δ ⊢ᶜ X → Γ ⊢ᶜ X
  wk-comp π (return W)     = return (wk-val π W)
  wk-comp π (pm W M)       = pm (wk-val π W) (wk-comp (wk-cong (wk-cong π)) M)
  wk-comp π (push M N) = push (wk-comp π M) (wk-comp (wk-cong π) N)
  wk-comp π (app V W)  = app (wk-val π V) (wk-val π W)
  wk-comp π (var W)        = var (wk-val π W)
  wk-comp π (sub M N)      = sub (wk-comp (wk-cong π) M) (wk-comp π N)

wk : Γ ⊢ᵛ X → (Γ ∙ Y) ⊢ᵛ X
wk = wk-val (wk-wk wk-id)

syntax Subᵛ Γ Δ = Γ ⊢ Δ

Subᵛ : Ctx → Ctx → Set
Subᵛ Γ = Sub (Val Γ)

sub-wk : Γ ⊇ Δ → Δ ⊢ Ψ → Γ ⊢ Ψ
sub-wk π = sub-map (wk-val π)

sub-id : Γ ⊢ Γ
sub-id {Γ = ε} = sub-ε
sub-id {Γ = Γ ∙ X} = sub-ex (sub-wk (wk-wk wk-id) sub-id) (var here)

mutual
  sub-val : Γ ⊢ Δ → Δ ⊢ᵛ X → Γ ⊢ᵛ X
  sub-val θ (var i) = sub-mem θ i
  sub-val θ (lam M) = lam (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  sub-val θ (pair V W) = pair (sub-val θ V) (sub-val θ W)
  sub-val θ unit = unit

  sub-comp : Γ ⊢ Δ → Δ ⊢ᶜ X → Γ ⊢ᶜ X
  sub-comp θ (return W) = return (sub-val θ W)
  sub-comp θ (pm W M) = pm (sub-val θ W) (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M)
  sub-comp θ (push M N) = push (sub-comp θ M) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
  sub-comp θ (app V W) = app (sub-val θ V) (sub-val θ W)
  sub-comp θ (var W) = var (sub-val θ W)
  sub-comp θ (sub M N) = sub (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M) (sub-comp θ N)

-- syntactic sugar

letv : Γ ⊢ᵛ X → (Γ ∙ X) ⊢ᵛ Y
     ---------------------------
    → Γ ⊢ᵛ Y
letv V W = sub-val (sub-ex sub-id V) W

letc : Γ ⊢ᵛ X → (Γ ∙ X) ⊢ᶜ Y
     ---------------------------
     → Γ ⊢ᶜ Y
letc W M = sub-comp (sub-ex sub-id W) M

exchg : (Γ ∙ X ∙ Y) ⊢ (Γ ∙ Y ∙ X)
exchg = sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) sub-id) (var here)) (var (there here))

variable
  V V₁ V₂ V₃ W₁ W₂ : Γ ⊢ᵛ X
  M M₁ M₂ M₃ N₁ N₂ : Γ ⊢ᶜ X

syntax EqVal Γ X e₁ e₂ = Γ ⊢ᵛ e₁ ≈ e₂ ∶ X

syntax EqComp Γ X e₁ e₂ = Γ ⊢ᶜ e₁ ≈ e₂ ∶ X

data EqVal (Γ : Ctx) : (X : Ty) → Γ ⊢ᵛ X → Γ ⊢ᵛ X → Set

data EqComp (Γ : Ctx) : (X : Ty) → Γ ⊢ᶜ X → Γ ⊢ᶜ X → Set

data EqVal Γ where

  -- equivalence rules
  ≈-refl  :
          -------------
          Γ ⊢ᵛ V ≈ V ∶ X

  ≈-sym   : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X
          ------------------
          → Γ ⊢ᵛ V₂ ≈ V₁ ∶ X

  ≈-trans : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X → Γ ⊢ᵛ V₂ ≈ V₃ ∶ X
          -------------------------------------
          → Γ ⊢ᵛ V₁ ≈ V₃ ∶ X

  -- congruence rules
  lam-cong : (Γ ∙ X) ⊢ᶜ M₁ ≈ M₂ ∶ Y
           ---------------------------------
           → Γ ⊢ᵛ lam M₁ ≈ lam M₂ ∶ X `⇒ Y

  pair-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X → Γ ⊢ᵛ W₁ ≈ W₂ ∶ Y
            ----------------------------------------
            → Γ ⊢ᵛ pair V₁ W₁ ≈ pair V₂ W₂ ∶ X `× Y

  -- beta/eta rules

  unit-eta : (V : Γ ⊢ᵛ `𝟙)
           ------------------------
           → Γ ⊢ᵛ V ≈ unit ∶ `𝟙

  lam-eta : (V : Γ ⊢ᵛ X `⇒ Y)
          ---------------------------
          → Γ ⊢ᵛ V ≈ lam (app (wk V) (var here)) ∶ X `⇒ Y

data EqComp Γ where

  -- equivalence rules
  ≈-refl  :
          -------------
          Γ ⊢ᶜ M ≈ M ∶ X

  ≈-sym   : Γ ⊢ᶜ M₁ ≈ M₂ ∶ X
          -------------------
          → Γ ⊢ᶜ M₂ ≈ M₁ ∶ X

  ≈-trans : Γ ⊢ᶜ M₁ ≈ M₂ ∶ X → Γ ⊢ᶜ M₂ ≈ M₃ ∶ X
          -------------------------------------
          → Γ ⊢ᶜ M₁ ≈ M₃ ∶ X

  -- congruence rules
  return-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X
             -----------------------------
             → Γ ⊢ᶜ return V₁ ≈ return V₂ ∶ X

  pm-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X `× Z → (Γ ∙ X ∙ Z) ⊢ᶜ M₁ ≈ M₂ ∶ Y
            -------------------------------------------------------------------
            → Γ ⊢ᶜ pm V₁ M₁ ≈ pm V₂ M₂ ∶ Y

  push-cong : Γ ⊢ᶜ M₁ ≈ M₂ ∶ X → (Γ ∙ X) ⊢ᶜ N₁ ≈ N₂ ∶ Y
            ---------------------------------------------------
            → Γ ⊢ᶜ push M₁ N₁ ≈ push M₂ N₂ ∶ Y

  app-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X `⇒ Y → Γ ⊢ᵛ W₁ ≈ W₂ ∶ X
            ------------------------------------------------
            → Γ ⊢ᶜ app V₁ W₁ ≈ app V₂ W₂ ∶ Y

  var-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ `ℓ
            ----------------------------
            → Γ ⊢ᶜ var V₁ ≈ var V₂ ∶ X

  sub-cong : (Γ ∙ `ℓ) ⊢ᶜ M₁ ≈ M₂ ∶ X → Γ ⊢ᶜ N₁ ≈ N₂ ∶ X
            -------------------------------------------------------------------------------------------
            → Γ ⊢ᶜ sub M₁ N₁ ≈ sub M₂ N₂ ∶ X

  -- beta/eta rules

  pm-beta : (V : Γ ⊢ᵛ X) → (W : Γ ⊢ᵛ Z) → (M : (Γ ∙ X ∙ Z) ⊢ᶜ Y)
          ------------------------------------------------------------------------
          → Γ ⊢ᶜ pm (pair V W) M ≈ sub-comp (sub-ex (sub-ex sub-id V) W) M ∶ Y

  pm-eta : (V : Γ ⊢ᵛ X `× Z) → (M : (Γ ∙ (X `× Z)) ⊢ᶜ Y)
         -------------------------------------------------------------------------------------------
         → Γ ⊢ᶜ sub-comp (sub-ex sub-id V) M ≈ pm V (sub-comp (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) sub-id) (pair (var (there here)) (var here))) M) ∶ Y

  return-beta : (V : Γ ⊢ᵛ X) → (M : (Γ ∙ X) ⊢ᶜ Y)
               ---------------------------------------------------------------
               → Γ ⊢ᶜ push (return V) M ≈ sub-comp (sub-ex sub-id V) M ∶ Y

  return-eta : (M : Γ ⊢ᶜ X)
              -----------------------
              → Γ ⊢ᶜ M ≈ push M (return (var here)) ∶ X

  push-eta : (M : Γ ⊢ᶜ X) → (N : (Γ ∙ X) ⊢ᶜ Y) → (P : (Γ ∙ Y) ⊢ᶜ Z)
           ----------------------------------------------------------------
           → Γ ⊢ᶜ push (push M N) P ≈ push M (push N (wk-comp (wk-cong (wk-wk wk-id)) P)) ∶ Z

  lam-beta : (M : (Γ ∙ X) ⊢ᶜ Y) → (V : Γ ⊢ᵛ X)
           ------------------------------------------------
           → Γ ⊢ᶜ app (lam M) V ≈ sub-comp (sub-ex sub-id V) M ∶ Y

  -- var/sub rules

  sub-weak : (M : Γ ⊢ᶜ X) → (N : Γ ⊢ᶜ X)
           ------------------------------------------------
           → Γ ⊢ᶜ sub (wk-comp (wk-wk wk-id) M) N ≈ M ∶ X

  sub-subst : (M : Γ ⊢ᶜ X)
            -------------------------------------------
            → Γ ⊢ᶜ sub (var (var here)) M ≈ M ∶ X

  sub-ext : (M : (Γ ∙ `ℓ) ⊢ᶜ X) → (V : Γ ⊢ᵛ `ℓ)
          ---------------------------------------------------------------------------
          → Γ ⊢ᶜ sub (sub-comp sub-id M) (var V) ≈ sub-comp (sub-ex sub-id V) M ∶ X

  sub-assoc : (M : (Γ ∙ `ℓ ∙ `ℓ) ⊢ᶜ X) → (N : (Γ ∙ `ℓ) ⊢ᶜ X) → (P : Γ ⊢ᶜ X)
            -----------------------------------------------------------------------------------------------
            → Γ ⊢ᶜ sub (sub M N) P ≈ sub (sub (sub-comp exchg M) (wk-comp (wk-wk wk-id) P)) (sub N P) ∶ X

  -- algebraicity rules

  var-push : (V : Γ ⊢ᵛ `ℓ) → (M : (Γ ∙ X) ⊢ᶜ Y)
           ----------------------------------------
           → Γ ⊢ᶜ push (var V) M ≈ var V ∶ Y

  sub-push : (M : (Γ ∙ `ℓ) ⊢ᶜ X) → (N : Γ ⊢ᶜ X) → (P : (Γ ∙ X) ⊢ᶜ Y)
           -------------------------------------------------------------------------------------------
           → Γ ⊢ᶜ push (sub M N) P ≈ sub (push M (wk-comp (wk-cong (wk-wk wk-id)) P)) (push N P) ∶ Y


mutual
  wk-val-id-β : (V : Γ ⊢ᵛ X) → wk-val wk-id V ≡ V
  wk-val-id-β (var i)    = refl
  wk-val-id-β (lam M)    = cong lam (wk-comp-id-β M)
  wk-val-id-β (pair V W) = cong₂ pair (wk-val-id-β V) (wk-val-id-β W)
  wk-val-id-β unit       = refl

  wk-comp-id-β : (M : Γ ⊢ᶜ X) → wk-comp wk-id M ≡ M
  wk-comp-id-β (return V) = cong return (wk-val-id-β V)
  wk-comp-id-β (pm V M)   = cong₂ pm (wk-val-id-β V) (wk-comp-id-β M)
  wk-comp-id-β (push M N) = cong₂ push (wk-comp-id-β M) (wk-comp-id-β N)
  wk-comp-id-β (app V W)  = cong₂ app (wk-val-id-β V) (wk-val-id-β W)
  wk-comp-id-β (var V)    = cong var (wk-val-id-β V)
  wk-comp-id-β (sub M N)  = cong₂ sub (wk-comp-id-β M) (wk-comp-id-β N)

{-# REWRITE wk-val-id-β wk-comp-id-β #-}

wk-val-id-η : (π : Γ ⊇ Γ) (V : Γ ⊢ᵛ X) → wk-val π V ≡ V
wk-val-id-η π V = cong (λ δ → wk-val δ V) (wk-id-η π)

wk-comp-id-η : (π : Γ ⊇ Γ) (M : Γ ⊢ᶜ X) → wk-comp π M ≡ M
wk-comp-id-η π M = cong (λ δ → wk-comp δ M) (wk-id-η π)

{-# REWRITE wk-val-id-η wk-comp-id-η #-}

mutual
  wk-val-wk-η : (V : Γ ⊢ᵛ X) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → wk-val π (wk-val δ V) ≡ wk-val (wk-trans π δ) V
  wk-val-wk-η (var i) π δ    = refl
  wk-val-wk-η (lam M) π δ    = cong lam (wk-comp-wk-η M (wk-cong π) (wk-cong δ))
  wk-val-wk-η (pair V W) π δ = cong₂ pair (wk-val-wk-η V π δ) (wk-val-wk-η W π δ)
  wk-val-wk-η unit π δ       = refl

  wk-comp-wk-η : (M : Γ ⊢ᶜ X) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → wk-comp π (wk-comp δ M) ≡ wk-comp (wk-trans π δ) M
  wk-comp-wk-η (return V) π δ = cong return (wk-val-wk-η V π δ)
  wk-comp-wk-η (pm V M) π δ   = cong₂ pm (wk-val-wk-η V π δ) (wk-comp-wk-η M (wk-cong (wk-cong π)) (wk-cong (wk-cong δ)))
  wk-comp-wk-η (push M N) π δ = cong₂ push (wk-comp-wk-η M π δ) (wk-comp-wk-η N (wk-cong π) (wk-cong δ))
  wk-comp-wk-η (app V W) π δ  = cong₂ app (wk-val-wk-η V π δ) (wk-val-wk-η W π δ)
  wk-comp-wk-η (var V) π δ    = cong var (wk-val-wk-η V π δ)
  wk-comp-wk-η (sub M N) π δ  = cong₂ sub (wk-comp-wk-η M (wk-cong π) (wk-cong δ)) (wk-comp-wk-η N π δ)

{-# REWRITE wk-val-wk-η wk-comp-wk-η #-}

\end{code}
