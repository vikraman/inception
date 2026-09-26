\begin{code}
{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Syntax where

open import Inception.Prelude

open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Empty using (⊥)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; cong₂)
open Eq.≡-Reasoning

---------------------------------------------------------------------------------

infixr 40 _`×_
infixr 25 _`⇒_

data Ty : Set where
  `𝟙 : Ty
  _`×_ _`⇒_ : Ty → Ty → Ty
  `ℓ : Ty

open import Inception.Ctx Ty public


\end{code}
%<*Terms>
\begin{code}

syntax Val Γ X = Γ ⊢ᵛ X
syntax Comp Γ X = Γ ⊢ᶜ X

mutual

  data Val : Ctx → Ty → Set where

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

  data Comp : Ctx → Ty → Set where

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
  wk-val : Wk Γ Δ → Δ ⊢ᵛ X → Γ ⊢ᵛ X
  wk-val π (var x)         = var (wk-mem π x)
  wk-val π (lam M)         = lam (wk-comp (wk-cong π) M)

  wk-val π (pair V W) = pair (wk-val π V) (wk-val π W)
  wk-val π unit       = unit

  wk-comp : Wk Γ Δ → Δ ⊢ᶜ X → Γ ⊢ᶜ X
  wk-comp π (return W)     = return (wk-val π W)
  wk-comp π (pm W M)       = pm (wk-val π W) (wk-comp (wk-cong (wk-cong π)) M)
  wk-comp π (push M N) = push (wk-comp π M) (wk-comp (wk-cong π) N)
  wk-comp π (app V W)  = app (wk-val π V) (wk-val π W)
  wk-comp π (var W)        = var (wk-val π W)
  wk-comp π (sub M N)      = sub (wk-comp (wk-cong π) M) (wk-comp π N)

wk : Val Γ X → Val (Γ ∙ Y) X
wk = wk-val (wk-wk wk-id)

data Sub (Γ : Ctx) : (Δ : Ctx) → Set where
  sub-ε : Sub Γ ε
  sub-ex : (θ : Sub Γ Δ) → (W : Val Γ X) → Sub Γ (Δ ∙ X)

sub-mem : Sub Γ Δ → Δ ∋ X → Val Γ X
sub-mem (sub-ex θ W) here = W
sub-mem (sub-ex θ W) (there i) = sub-mem θ i

sub-wk : Wk Γ Δ → Sub Δ Ψ → Sub Γ Ψ
sub-wk π sub-ε = sub-ε
sub-wk π (sub-ex θ W) = sub-ex (sub-wk π θ) (wk-val π W)

sub-id : Sub Γ Γ
sub-id {Γ = ε} = sub-ε
sub-id {Γ = Γ ∙ X} = sub-ex (sub-wk (wk-wk wk-id) sub-id) (var here)

mutual
  sub-val : Sub Γ Δ → Δ ⊢ᵛ X → Γ ⊢ᵛ X
  sub-val θ (var x) = sub-mem θ x
  sub-val θ (lam M) = lam (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  sub-val θ (pair V W) = pair (sub-val θ V) (sub-val θ W)
  sub-val θ unit = unit

  sub-comp : Sub Γ Δ → Δ ⊢ᶜ X → Γ ⊢ᶜ X
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

exchg : Sub (Γ ∙ X ∙ Y)(Γ ∙ Y ∙ X)
exchg = sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) sub-id) (var here)) (var (there here))

variable
  x : Γ ∋ X
  V V₁ V₂ V₃ W W₁ W₂ W₃ : Γ ⊢ᵛ X
  M M₁ M₂ M₃ N N₁ N₂ N₃ P P₁ P₂ P₃ : Γ ⊢ᶜ X

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

  pair-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X₁ → Γ ⊢ᵛ W₁ ≈ W₂ ∶ X₂
            ----------------------------------------
            → Γ ⊢ᵛ pair V₁ W₁ ≈ pair V₂ W₂ ∶ X₁ `× X₂

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

  pm-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X₁ `× X₂ → (Γ ∙ X₁ ∙ X₂) ⊢ᶜ M₁ ≈ M₂ ∶ Y
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

  pm-beta : (V : Γ ⊢ᵛ X₁) → (W : Γ ⊢ᵛ X₂) → (M : (Γ ∙ X₁ ∙ X₂) ⊢ᶜ Y)
          ------------------------------------------------------------------------
          → Γ ⊢ᶜ pm (pair V W) M ≈ sub-comp (sub-ex (sub-ex sub-id V) W) M ∶ Y

  pm-eta : (V : Γ ⊢ᵛ X₁ `× X₂) → (M : (Γ ∙ (X₁ `× X₂)) ⊢ᶜ Y)
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

  wk-val-trans : (V : Γ ⊢ᵛ X) → (π₁ : Wk Ψ Δ) → (π₂ : Wk Δ Γ) → wk-val π₁ (wk-val π₂ V) ≡ wk-val (wk-trans π₁ π₂) V
  wk-val-trans (var i) π₁ π₂ = cong var (wk-mem-trans i π₁ π₂)
  wk-val-trans (lam M) π₁ π₂ = cong lam (wk-comp-trans M (wk-cong π₁) (wk-cong π₂))
  wk-val-trans (pair V W) π₁ π₂ = pair (wk-val π₁ (wk-val π₂ V)) (wk-val π₁ (wk-val π₂ W))
               ≡⟨ cong (λ x → pair (wk-val π₁ (wk-val π₂ V)) x) (wk-val-trans W π₁ π₂) ⟩
               pair (wk-val π₁ (wk-val π₂ V)) (wk-val (wk-trans π₁ π₂) W)
               ≡⟨ cong (λ x → pair x (wk-val (wk-trans π₁ π₂) W)) (wk-val-trans V π₁ π₂) ⟩
               pair (wk-val (wk-trans π₁ π₂) V) (wk-val (wk-trans π₁ π₂) W) ∎
  wk-val-trans unit π₁ π₂ = refl

  wk-comp-trans : (M : Γ ⊢ᶜ X) → (π₁ : Wk Ψ Δ) → (π₂ : Wk Δ Γ) → wk-comp π₁ (wk-comp π₂ M) ≡ wk-comp (wk-trans π₁ π₂) M
  wk-comp-trans (return V) π₁ π₂ = cong return (wk-val-trans V π₁ π₂)
  wk-comp-trans (pm V M) π₁ π₂ =
                pm (wk-val π₁ (wk-val π₂ V)) (wk-comp (wk-cong (wk-cong π₁)) (wk-comp (wk-cong (wk-cong π₂)) M))
                ≡⟨ cong (λ x → pm x (wk-comp (wk-cong (wk-cong π₁)) (wk-comp (wk-cong (wk-cong π₂)) M))) (wk-val-trans V π₁ π₂) ⟩
                pm (wk-val (wk-trans π₁ π₂) V) (wk-comp (wk-cong (wk-cong π₁)) (wk-comp (wk-cong (wk-cong π₂)) M))
                ≡⟨ cong (λ x → pm (wk-val (wk-trans π₁ π₂) V) x) (wk-comp-trans M (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π₂)) ) ⟩
                pm (wk-val (wk-trans π₁ π₂) V) (wk-comp (wk-cong (wk-cong (wk-trans π₁ π₂))) M) ∎
  wk-comp-trans (push M N) π₁ π₂ =
                push (wk-comp π₁ (wk-comp π₂ M)) (wk-comp (wk-cong π₁) (wk-comp (wk-cong π₂) N))
                ≡⟨ cong (λ x → push x (wk-comp (wk-cong π₁) (wk-comp (wk-cong π₂) N))) (wk-comp-trans M π₁ π₂) ⟩
                push (wk-comp (wk-trans π₁ π₂) M) (wk-comp (wk-cong π₁) (wk-comp (wk-cong π₂) N))
                ≡⟨ cong (λ x → push (wk-comp (wk-trans π₁ π₂) M) x) (wk-comp-trans N (wk-cong π₁) (wk-cong π₂)) ⟩
                push (wk-comp (wk-trans π₁ π₂) M) (wk-comp (wk-cong (wk-trans π₁ π₂)) N) ∎
  wk-comp-trans (app V W) π₁ π₂ =
                app (wk-val π₁ (wk-val π₂ V)) (wk-val π₁ (wk-val π₂ W))
                ≡⟨ cong (λ y → app y (wk-val π₁ (wk-val π₂ W))) (wk-val-trans V π₁ π₂) ⟩
                app (wk-val (wk-trans π₁ π₂) V) (wk-val π₁ (wk-val π₂ W))
                ≡⟨ cong (λ y → app (wk-val (wk-trans π₁ π₂) V) y) (wk-val-trans W π₁ π₂) ⟩
                app (wk-val (wk-trans π₁ π₂) V) (wk-val (wk-trans π₁ π₂) W) ∎
  wk-comp-trans (var V) π₁ π₂ = cong var (wk-val-trans V π₁ π₂)
  wk-comp-trans (sub M N) π₁ π₂ =
                sub (wk-comp (wk-cong π₁) (wk-comp (wk-cong π₂) M)) (wk-comp π₁ (wk-comp π₂ N))
                ≡⟨ cong (λ x → sub x (wk-comp π₁ (wk-comp π₂ N))) (wk-comp-trans M (wk-cong π₁) (wk-cong π₂)) ⟩
                sub (wk-comp (wk-cong (wk-trans π₁ π₂)) M) (wk-comp π₁ (wk-comp π₂ N))
                ≡⟨ cong (λ x → sub (wk-comp (wk-cong (wk-trans π₁ π₂)) M) x) (wk-comp-trans N π₁ π₂) ⟩
                sub (wk-comp (wk-cong (wk-trans π₁ π₂)) M) (wk-comp (wk-trans π₁ π₂) N) ∎

mutual

  wk-val-id : (V : Γ ⊢ᵛ X) → wk-val wk-id V ≡ V
  wk-val-id (var i) = cong var wk-mem-id
  wk-val-id (lam M) = cong lam (wk-comp-id M)
  wk-val-id (pair V W) = pair (wk-val wk-id V) (wk-val wk-id W) ≡⟨ cong (λ y → pair y (wk-val wk-id W)) (wk-val-id V) ⟩ pair V (wk-val wk-id W) ≡⟨ cong (λ y → pair V y) (wk-val-id W) ⟩ pair V W ∎
  wk-val-id unit = refl

  wk-comp-id : (M : Γ ⊢ᶜ X) → wk-comp wk-id M ≡ M
  wk-comp-id (return V) = cong return (wk-val-id V)
  wk-comp-id (pm V M) = pm (wk-val wk-id V) (wk-comp (wk-cong (wk-cong wk-id)) M) ≡⟨ refl ⟩ pm (wk-val wk-id V) (wk-comp wk-id M) ≡⟨ cong (λ y → pm y (wk-comp wk-id M)) (wk-val-id V) ⟩ pm V (wk-comp wk-id M) ≡⟨ cong (λ y → pm V y) (wk-comp-id M) ⟩ pm V M ∎
  wk-comp-id (push M N) = push (wk-comp wk-id M) (wk-comp (wk-cong wk-id) N) ≡⟨ cong (λ y → push (wk-comp wk-id M) y) (wk-comp-id N) ⟩ push (wk-comp wk-id M) N ≡⟨ cong (λ y → push y N) (wk-comp-id M) ⟩ push M N ∎
  wk-comp-id (app V W) = app (wk-val wk-id V) (wk-val wk-id W) ≡⟨ cong (λ y → app y (wk-val wk-id W)) (wk-val-id V) ⟩ app V (wk-val wk-id W) ≡⟨ cong (λ y → app V y) (wk-val-id W) ⟩ app V W ∎
  wk-comp-id (var V) = cong var (wk-val-id V)
  wk-comp-id (sub M N) = sub (wk-comp (wk-cong wk-id) M) (wk-comp wk-id N) ≡⟨ cong (λ y → sub y (wk-comp wk-id N)) (wk-comp-id M) ⟩ sub M (wk-comp wk-id N) ≡⟨ cong (λ y → sub M y) (wk-comp-id N) ⟩ sub M N ∎

\end{code}
