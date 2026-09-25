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
  _`×_ _`⇒_ : Ty -> Ty -> Ty
  `ℓ : Ty

open import Inception.Ctx Ty public


\end{code}
%<*Terms>
\begin{code}

syntax Pure Γ X = Γ ⊢ᵖ X
syntax Comp Γ X = Γ ⊢ᶜ X

mutual

  data Pure : Ctx -> Ty -> Set where

    var :   (x : Γ ∋ X)
            ----------
            -> Γ ⊢ᵖ X

    lam :   (Γ ∙ X) ⊢ᶜ Y
            --------------
            -> Γ ⊢ᵖ X `⇒ Y

    pair :  Γ ⊢ᵖ X₁ -> Γ ⊢ᵖ X₂
            -----------------
            -> Γ ⊢ᵖ X₁ `× X₂

    unit :
            -----------
            Γ ⊢ᵖ `𝟙

  data Comp : Ctx -> Ty -> Set where

    return :  Γ ⊢ᵖ X
              ---------
              -> Γ ⊢ᶜ X

    pm :      Γ ⊢ᵖ X₁ `× X₂ -> (Γ ∙ X₁ ∙ X₂) ⊢ᶜ Y
              -------------------------------
              -> Γ ⊢ᶜ Y

    push :    Γ ⊢ᶜ X -> (Γ ∙ X) ⊢ᶜ Y
              --------------------
              -> Γ ⊢ᶜ Y

    app :     Γ ⊢ᵖ X `⇒ Y -> Γ ⊢ᵖ X
              ---------------------
              -> Γ ⊢ᶜ Y

    var :     Γ ⊢ᵖ `ℓ
              ---------
              -> Γ ⊢ᶜ X

    sub :     (Γ ∙ `ℓ) ⊢ᶜ X -> Γ ⊢ᶜ X
              --------------------
              -> Γ ⊢ᶜ X

\end{code}
%</Terms>
\begin{code}

mutual
  wk-pure : Wk Γ Δ -> Δ ⊢ᵖ X -> Γ ⊢ᵖ X
  wk-pure π (var x)         = var (wk-mem π x)
  wk-pure π (lam M)         = lam (wk-comp (wk-cong π) M)

  wk-pure π (pair W₁ W₂)    = pair (wk-pure π W₁) (wk-pure π W₂)
  wk-pure π unit            = unit

  wk-comp : Wk Γ Δ -> Δ ⊢ᶜ X -> Γ ⊢ᶜ X
  wk-comp π (return W)     = return (wk-pure π W)
  wk-comp π (pm W M)       = pm (wk-pure π W) (wk-comp (wk-cong (wk-cong π)) M)
  wk-comp π (push M₁ M₂)     = push (wk-comp π M₁) (wk-comp (wk-cong π) M₂)
  wk-comp π (app W₁ W₂)      = app (wk-pure π W₁) (wk-pure π W₂)
  wk-comp π (var W)        = var (wk-pure π W)
  wk-comp π (sub M₁ M₂)      = sub (wk-comp (wk-cong π) M₁) (wk-comp π M₂)

wk : Pure Γ X -> Pure (Γ ∙ Y) X
wk = wk-pure (wk-wk wk-id)

data Sub (Γ : Ctx) : (Δ : Ctx) -> Set where
  sub-ε : Sub Γ ε
  sub-ex : (θ : Sub Γ Δ) -> (W : Pure Γ X) -> Sub Γ (Δ ∙ X)

sub-mem : Sub Γ Δ -> Δ ∋ X -> Pure Γ X
sub-mem (sub-ex θ W) here = W
sub-mem (sub-ex θ W) (there i) = sub-mem θ i

sub-wk : Wk Γ Δ -> Sub Δ Ψ -> Sub Γ Ψ
sub-wk π sub-ε = sub-ε
sub-wk π (sub-ex θ W) = sub-ex (sub-wk π θ) (wk-pure π W)

sub-id : Sub Γ Γ
sub-id {Γ = ε} = sub-ε
sub-id {Γ = Γ ∙ X} = sub-ex (sub-wk (wk-wk wk-id) sub-id) (var here)

mutual
  sub-pure : Sub Γ Δ -> Δ ⊢ᵖ X -> Γ ⊢ᵖ X
  sub-pure θ (var x) = sub-mem θ x
  sub-pure θ (lam M) = lam (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  sub-pure θ (pair W₁ W₂) = pair (sub-pure θ W₁) (sub-pure θ W₂)
  sub-pure θ unit = unit

  sub-comp : Sub Γ Δ -> Δ ⊢ᶜ X -> Γ ⊢ᶜ X
  sub-comp θ (return W) = return (sub-pure θ W)
  sub-comp θ (pm W M) = pm (sub-pure θ W) (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M)
  sub-comp θ (push M₁ M₂) = push (sub-comp θ M₁) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M₂)
  sub-comp θ (app W₁ W₂) = app (sub-pure θ W₁) (sub-pure θ W₂)
  sub-comp θ (var W) = var (sub-pure θ W)
  sub-comp θ (sub M₁ M₂) = sub (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M₁) (sub-comp θ M₂)

-- syntactic sugar

letv : Γ ⊢ᵖ X -> (Γ ∙ X) ⊢ᵖ Y
     ---------------------------
    -> Γ ⊢ᵖ Y
letv W₁ W₂ = sub-pure (sub-ex sub-id W₁) W₂

letc : Γ ⊢ᵖ X -> (Γ ∙ X) ⊢ᶜ Y
     ---------------------------
     -> Γ ⊢ᶜ Y
letc W M = sub-comp (sub-ex sub-id W) M

exchg : Sub (Γ ∙ X ∙ Y)(Γ ∙ Y ∙ X)
exchg = sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) sub-id) (var here)) (var (there here))

variable
  x : Γ ∋ X
  W W₁ W₂ W₃ W' W₁' W₂' W₃' : Γ ⊢ᵖ X
  M M₁ M₂ M₃ M₄ M' M₁' M₂' M₃' M₄' : Γ ⊢ᶜ X

syntax EqPure Γ X e1 e2 = Γ ⊢ᵖ e1 ≈ e2 ∶ X

syntax EqComp Γ X e1 e2 = Γ ⊢ᶜ e1 ≈ e2 ∶ X

data EqPure (Γ : Ctx) : (X : Ty) -> Γ ⊢ᵖ X -> Γ ⊢ᵖ X -> Set

data EqComp (Γ : Ctx) : (X : Ty) -> Γ ⊢ᶜ X -> Γ ⊢ᶜ X -> Set

data EqPure Γ where

  -- equivalence rules
  ≈-refl  :
          -------------
          Γ ⊢ᵖ W ≈ W ∶ X

  ≈-sym   : Γ ⊢ᵖ W₁ ≈ W₂ ∶ X
          ------------------
          -> Γ ⊢ᵖ W₂ ≈ W₁ ∶ X

  ≈-trans : Γ ⊢ᵖ W₁ ≈ W₂ ∶ X -> Γ ⊢ᵖ W₂ ≈ W₃ ∶ X
          -------------------------------------
          -> Γ ⊢ᵖ W₁ ≈ W₃ ∶ X

  -- congruence rules
  lam-cong : (Γ ∙ X) ⊢ᶜ M₁ ≈ M₂ ∶ Y
           ---------------------------------
           -> Γ ⊢ᵖ lam M₁ ≈ lam M₂ ∶ X `⇒ Y

  pair-cong : Γ ⊢ᵖ W₁ ≈ W₁' ∶ X₁ -> Γ ⊢ᵖ W₂ ≈ W₂' ∶ X₂
            ----------------------------------------
            -> Γ ⊢ᵖ pair W₁ W₂ ≈ pair W₁' W₂' ∶ X₁ `× X₂

  -- beta/eta rules

  unit-eta : (W : Γ ⊢ᵖ `𝟙)
           ------------------------
           -> Γ ⊢ᵖ W ≈ unit ∶ `𝟙

  lam-eta : (W : Γ ⊢ᵖ X `⇒ Y)
          ---------------------------
          -> Γ ⊢ᵖ W ≈ lam (app (wk W) (var here)) ∶ X `⇒ Y

data EqComp Γ where

  -- equivalence rules
  ≈-refl  :
          -------------
          Γ ⊢ᶜ M ≈ M ∶ X

  ≈-sym   : Γ ⊢ᶜ M₁ ≈ M₂ ∶ X
          -------------------
          -> Γ ⊢ᶜ M₂ ≈ M₁ ∶ X

  ≈-trans : Γ ⊢ᶜ M₁ ≈ M₂ ∶ X -> Γ ⊢ᶜ M₂ ≈ M₃ ∶ X
          -------------------------------------
          -> Γ ⊢ᶜ M₁ ≈ M₃ ∶ X

  -- congruence rules
  return-cong : Γ ⊢ᵖ W₁ ≈ W₂ ∶ X
             -----------------------------
             -> Γ ⊢ᶜ return W₁ ≈ return W₂ ∶ X

  pm-cong : Γ ⊢ᵖ W ≈ W' ∶ X₁ `× X₂ -> (Γ ∙ X₁ ∙ X₂) ⊢ᶜ M ≈ M' ∶ Y
            -------------------------------------------------------------------
            -> Γ ⊢ᶜ pm W M ≈ pm W' M' ∶ Y

  push-cong : Γ ⊢ᶜ M₁ ≈ M₁' ∶ X -> (Γ ∙ X) ⊢ᶜ M₂ ≈ M₂' ∶ Y
            ---------------------------------------------------
            -> Γ ⊢ᶜ push M₁ M₂ ≈ push M₁' M₂' ∶ Y

  app-cong : Γ ⊢ᵖ W₁ ≈ W₁' ∶ X `⇒ Y -> Γ ⊢ᵖ W₂ ≈ W₂' ∶ X
            ------------------------------------------------
            -> Γ ⊢ᶜ app W₁ W₂ ≈ app W₁' W₂' ∶ Y

  var-cong : Γ ⊢ᵖ W ≈ W' ∶ `ℓ
            ----------------------------
            -> Γ ⊢ᶜ var W ≈ var W' ∶ X

  sub-cong : (Γ ∙ `ℓ) ⊢ᶜ M₁ ≈ M₁' ∶ X -> Γ ⊢ᶜ M₂ ≈ M₂' ∶ X
            -------------------------------------------------------------------------------------------
            -> Γ ⊢ᶜ sub M₁ M₂ ≈ sub M₁' M₂' ∶ X

  -- beta/eta rules

  pm-beta : (W₁ : Γ ⊢ᵖ X₁) -> (W₂ : Γ ⊢ᵖ X₂) -> (M : (Γ ∙ X₁ ∙ X₂) ⊢ᶜ Y)
          ------------------------------------------------------------------------
          -> Γ ⊢ᶜ pm (pair W₁ W₂) M ≈ sub-comp (sub-ex (sub-ex sub-id W₁) W₂) M ∶ Y

  pm-eta : (W : Γ ⊢ᵖ X₁ `× X₂) -> (M : (Γ ∙ (X₁ `× X₂)) ⊢ᶜ Y)
         -------------------------------------------------------------------------------------------
         -> Γ ⊢ᶜ sub-comp (sub-ex sub-id W) M ≈ pm W (sub-comp (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) sub-id) (pair (var (there here)) (var here))) M) ∶ Y

  return-beta : (W : Γ ⊢ᵖ X) -> (M : (Γ ∙ X) ⊢ᶜ Y)
               ---------------------------------------------------------------
               -> Γ ⊢ᶜ push (return W) M ≈ sub-comp (sub-ex sub-id W) M ∶ Y

  return-eta : (M : Γ ⊢ᶜ X)
              -----------------------
              -> Γ ⊢ᶜ M ≈ push M (return (var here)) ∶ X

  push-eta : (M₁ : Γ ⊢ᶜ X) -> (M₂ : (Γ ∙ X) ⊢ᶜ Y) -> (M₃ : (Γ ∙ Y) ⊢ᶜ Z)
           ----------------------------------------------------------------
           -> Γ ⊢ᶜ push (push M₁ M₂) M₃ ≈ push M₁ (push M₂ (wk-comp (wk-cong (wk-wk wk-id)) M₃)) ∶ Z

  lam-beta : (M : (Γ ∙ X) ⊢ᶜ Y) -> (W : Γ ⊢ᵖ X)
           ------------------------------------------------
           -> Γ ⊢ᶜ app (lam M) W ≈ sub-comp (sub-ex sub-id W) M ∶ Y

  -- var/sub rules

  sub-weak : (M₁ : Γ ⊢ᶜ X) -> (M₂ : Γ ⊢ᶜ X)
           ------------------------------------------------
           -> Γ ⊢ᶜ sub (wk-comp (wk-wk wk-id) M₁) M₂ ≈ M₁ ∶ X

  sub-subst : (M : Γ ⊢ᶜ X)
            -------------------------------------------
            -> Γ ⊢ᶜ sub (var (var here)) M ≈ M ∶ X

  sub-ext : (M : (Γ ∙ `ℓ) ⊢ᶜ X) -> (W : Γ ⊢ᵖ `ℓ)
          ---------------------------------------------------------------------------
          -> Γ ⊢ᶜ sub (sub-comp sub-id M) (var W) ≈ sub-comp (sub-ex sub-id W) M ∶ X

  sub-assoc : (M₁ : (Γ ∙ `ℓ ∙ `ℓ) ⊢ᶜ X) -> (M₂ : (Γ ∙ `ℓ) ⊢ᶜ X) -> (M₃ : Γ ⊢ᶜ X)
            -----------------------------------------------------------------------------------------------
            -> Γ ⊢ᶜ sub (sub M₁ M₂) M₃ ≈ sub (sub (sub-comp exchg M₁) (wk-comp (wk-wk wk-id) M₃)) (sub M₂ M₃) ∶ X

  -- algebraicity rules

  var-push : (W : Γ ⊢ᵖ `ℓ) -> (M : (Γ ∙ X) ⊢ᶜ Y)
           ----------------------------------------
           -> Γ ⊢ᶜ push (var W) M ≈ var W ∶ Y

  sub-push : (M₁ : (Γ ∙ `ℓ) ⊢ᶜ X) -> (M₂ : Γ ⊢ᶜ X) -> (M₃ : (Γ ∙ X) ⊢ᶜ Y)
           -------------------------------------------------------------------------------------------
           -> Γ ⊢ᶜ push (sub M₁ M₂) M₃ ≈ sub (push M₁ (wk-comp (wk-cong (wk-wk wk-id)) M₃)) (push M₂ M₃) ∶ Y


mutual

  wk-pure-trans : (M : Γ ⊢ᵖ X) → (π₁ : Wk Ψ Δ) → (π₂ : Wk Δ Γ) → wk-pure π₁ (wk-pure π₂ M) ≡ wk-pure (wk-trans π₁ π₂) M
  wk-pure-trans (var i) π₁ π₂ = cong var (wk-mem-trans i π₁ π₂)
  wk-pure-trans (lam x) π₁ π₂ = cong lam (wk-comp-trans x (wk-cong π₁) (wk-cong π₂))
  wk-pure-trans (pair M₁ M₂) π₁ π₂ = pair (wk-pure π₁ (wk-pure π₂ M₁)) (wk-pure π₁ (wk-pure π₂ M₂))
               ≡⟨ cong (λ x → pair (wk-pure π₁ (wk-pure π₂ M₁)) x) (wk-pure-trans M₂ π₁ π₂) ⟩
               pair (wk-pure π₁ (wk-pure π₂ M₁)) (wk-pure (wk-trans π₁ π₂) M₂)
               ≡⟨ cong (λ x → pair x (wk-pure (wk-trans π₁ π₂) M₂)) (wk-pure-trans M₁ π₁ π₂) ⟩
               pair (wk-pure (wk-trans π₁ π₂) M₁) (wk-pure (wk-trans π₁ π₂) M₂) ∎
  wk-pure-trans unit π₁ π₂ = refl

  wk-comp-trans : (W : Γ ⊢ᶜ X) → (π₁ : Wk Ψ Δ) → (π₂ : Wk Δ Γ) → wk-comp π₁ (wk-comp π₂ W) ≡ wk-comp (wk-trans π₁ π₂) W
  wk-comp-trans (return M) π₁ π₂ = cong return (wk-pure-trans M π₁ π₂)
  wk-comp-trans (pm M₁ M₂) π₁ π₂ =
                pm (wk-pure π₁ (wk-pure π₂ M₁)) (wk-comp (wk-cong (wk-cong π₁)) (wk-comp (wk-cong (wk-cong π₂)) M₂))
                ≡⟨ cong (λ x → pm x (wk-comp (wk-cong (wk-cong π₁)) (wk-comp (wk-cong (wk-cong π₂)) M₂))) (wk-pure-trans M₁ π₁ π₂) ⟩
                pm (wk-pure (wk-trans π₁ π₂) M₁) (wk-comp (wk-cong (wk-cong π₁)) (wk-comp (wk-cong (wk-cong π₂)) M₂))
                ≡⟨ cong (λ x → pm (wk-pure (wk-trans π₁ π₂) M₁) x) (wk-comp-trans M₂ (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π₂)) ) ⟩
                pm (wk-pure (wk-trans π₁ π₂) M₁) (wk-comp (wk-cong (wk-cong (wk-trans π₁ π₂))) M₂) ∎
  wk-comp-trans (push W₁ W₂) π₁ π₂ =
                push (wk-comp π₁ (wk-comp π₂ W₁)) (wk-comp (wk-cong π₁) (wk-comp (wk-cong π₂) W₂))
                ≡⟨ cong (λ x → push x (wk-comp (wk-cong π₁) (wk-comp (wk-cong π₂) W₂))) (wk-comp-trans W₁ π₁ π₂) ⟩
                push (wk-comp (wk-trans π₁ π₂) W₁) (wk-comp (wk-cong π₁) (wk-comp (wk-cong π₂) W₂))
                ≡⟨ cong (λ x → push (wk-comp (wk-trans π₁ π₂) W₁) x) (wk-comp-trans W₂ (wk-cong π₁) (wk-cong π₂)) ⟩
                push (wk-comp (wk-trans π₁ π₂) W₁) (wk-comp (wk-cong (wk-trans π₁ π₂)) W₂) ∎
  wk-comp-trans (app W₁ W₂) π₁ π₂ =
                app (wk-pure π₁ (wk-pure π₂ W₁)) (wk-pure π₁ (wk-pure π₂ W₂))
                ≡⟨ cong (λ y → app y (wk-pure π₁ (wk-pure π₂ W₂))) (wk-pure-trans W₁ π₁ π₂) ⟩
                app (wk-pure (wk-trans π₁ π₂) W₁) (wk-pure π₁ (wk-pure π₂ W₂))
                ≡⟨ cong (λ y → app (wk-pure (wk-trans π₁ π₂) W₁) y) (wk-pure-trans W₂ π₁ π₂) ⟩
                app (wk-pure (wk-trans π₁ π₂) W₁) (wk-pure (wk-trans π₁ π₂) W₂) ∎
  wk-comp-trans (var W) π₁ π₂ = cong var (wk-pure-trans W π₁ π₂)
  wk-comp-trans (sub W₁ W₂) π₁ π₂ =
                sub (wk-comp (wk-cong π₁) (wk-comp (wk-cong π₂) W₁)) (wk-comp π₁ (wk-comp π₂ W₂))
                ≡⟨ cong (λ x → sub x (wk-comp π₁ (wk-comp π₂ W₂))) (wk-comp-trans W₁ (wk-cong π₁) (wk-cong π₂)) ⟩
                sub (wk-comp (wk-cong (wk-trans π₁ π₂)) W₁) (wk-comp π₁ (wk-comp π₂ W₂))
                ≡⟨ cong (λ x → sub (wk-comp (wk-cong (wk-trans π₁ π₂)) W₁) x) (wk-comp-trans W₂ π₁ π₂) ⟩
                sub (wk-comp (wk-cong (wk-trans π₁ π₂)) W₁) (wk-comp (wk-trans π₁ π₂) W₂) ∎

mutual

  wk-pure-id : (M : Γ ⊢ᵖ X) → wk-pure wk-id M ≡ M
  wk-pure-id (var i) = cong var wk-mem-id
  wk-pure-id (lam W) = cong lam (wk-comp-id W)
  wk-pure-id (pair W₁ W₂) = pair (wk-pure wk-id W₁) (wk-pure wk-id W₂) ≡⟨ cong (λ y → pair y (wk-pure wk-id W₂)) (wk-pure-id W₁) ⟩ pair W₁ (wk-pure wk-id W₂) ≡⟨ cong (λ y → pair W₁ y) (wk-pure-id W₂) ⟩ pair W₁ W₂ ∎
  wk-pure-id unit = refl

  wk-comp-id : (W : Γ ⊢ᶜ X) → wk-comp wk-id W ≡ W
  wk-comp-id (return x) = cong return (wk-pure-id x)
  wk-comp-id (pm W M) = pm (wk-pure wk-id W) (wk-comp (wk-cong (wk-cong wk-id)) M) ≡⟨ refl ⟩ pm (wk-pure wk-id W) (wk-comp wk-id M) ≡⟨ cong (λ y → pm y (wk-comp wk-id M)) (wk-pure-id W) ⟩ pm W (wk-comp wk-id M) ≡⟨ cong (λ y → pm W y) (wk-comp-id M) ⟩ pm W M ∎
  wk-comp-id (push M₁ M₂) = push (wk-comp wk-id M₁) (wk-comp (wk-cong wk-id) M₂) ≡⟨ cong (λ y → push (wk-comp wk-id M₁) y) (wk-comp-id M₂) ⟩ push (wk-comp wk-id M₁) M₂ ≡⟨ cong (λ y → push y M₂) (wk-comp-id M₁) ⟩ push M₁ M₂ ∎
  wk-comp-id (app W₁ W₂) = app (wk-pure wk-id W₁) (wk-pure wk-id W₂) ≡⟨ cong (λ y → app y (wk-pure wk-id W₂)) (wk-pure-id W₁) ⟩ app W₁ (wk-pure wk-id W₂) ≡⟨ cong (λ y → app W₁ y) (wk-pure-id W₂) ⟩ app W₁ W₂ ∎
  wk-comp-id (var W) = cong var (wk-pure-id W)
  wk-comp-id (sub W₁ W₂) = sub (wk-comp (wk-cong wk-id) W₁) (wk-comp wk-id W₂) ≡⟨ cong (λ y → sub y (wk-comp wk-id W₂)) (wk-comp-id W₁) ⟩ sub W₁ (wk-comp wk-id W₂) ≡⟨ cong (λ y → sub W₁ y) (wk-comp-id W₂) ⟩ sub W₁ W₂ ∎

\end{code}
