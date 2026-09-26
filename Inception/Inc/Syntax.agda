module Inception.Inc.Syntax where

open import Data.Nat

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

data Val where

  var : (i : Γ ∋ X)
      ---------
      → Γ ⊢ᵛ X

  lam : (Γ ∙ X) ⊢ᶜ Y
      -----------------
      → Γ ⊢ᵛ X `⇒ Y

  pair : Γ ⊢ᵛ X → Γ ⊢ᵛ Y
      -------------------
       → Γ ⊢ᵛ X `× Y

  unit :
       -----------
        Γ ⊢ᵛ `𝟙

data Comp where

  return : Γ ⊢ᵛ X
         -----------
         → Γ ⊢ᶜ X

  pm : Γ ⊢ᵛ X `× Y → (Γ ∙ X ∙ Y) ⊢ᶜ Z
     -----------------------------------
     → Γ ⊢ᶜ Z

  push : Γ ⊢ᶜ X → (Γ ∙ X) ⊢ᶜ Y
       ---------------------------
       → Γ ⊢ᶜ Y

  app : Γ ⊢ᵛ X `⇒ Y → Γ ⊢ᵛ X
      -------------------------
              → Γ ⊢ᶜ Y

  rec : Γ ⊢ᵛ `ℓ → Γ ⊢ᵛ `𝓅
      -----------------------
      → Γ ⊢ᶜ X

  inc : (Γ ∙ `ℓ) ⊢ᶜ X → (Γ ∙ `𝓅) ⊢ᶜ X
      -----------------------------------
      → Γ ⊢ᶜ X

mutual
  wk-val : Γ ⊇ Δ → Δ ⊢ᵛ X → Γ ⊢ᵛ X
  wk-val π (var i) = var (wk-mem π i)
  wk-val π (lam M) = lam (wk-comp (wk-cong π) M)

  wk-val π (pair V W) = pair (wk-val π V) (wk-val π W)
  wk-val π unit       = unit

  wk-comp : Γ ⊇ Δ → Δ ⊢ᶜ X → Γ ⊢ᶜ X
  wk-comp π (return V)     = return (wk-val π V)
  wk-comp π (pm V M)       = pm (wk-val π V) (wk-comp (wk-cong (wk-cong π)) M)
  wk-comp π (push M N)     = push (wk-comp π M) (wk-comp (wk-cong π) N)
  wk-comp π (app V W)      = app (wk-val π V) (wk-val π W)
  wk-comp π (rec V W)      = rec (wk-val π V) (wk-val π W)
  wk-comp π (inc M N)      = inc (wk-comp (wk-cong π) M) (wk-comp (wk-cong π) N)

wk : Γ ⊢ᵛ X → (Γ ∙ Y) ⊢ᵛ X
wk = wk-val (wk-wk wk-id)

syntax Sub Γ Δ = Γ ⊢ Δ

data Sub (Γ : Ctx) : (Δ : Ctx) → Set where
  sub-ε : Γ ⊢ ε
  sub-ex : (θ : Γ ⊢ Δ) → (V : Γ ⊢ᵛ X) → Γ ⊢ (Δ ∙ X)

sub-mem : Γ ⊢ Δ → Δ ∋ X → Γ ⊢ᵛ X
sub-mem (sub-ex θ V) here = V
sub-mem (sub-ex θ V) (there i) = sub-mem θ i

sub-wk : Γ ⊇ Δ → Δ ⊢ Ψ → Γ ⊢ Ψ
sub-wk π sub-ε = sub-ε
sub-wk π (sub-ex θ V) = sub-ex (sub-wk π θ) (wk-val π V)

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
  sub-comp θ (return V) = return (sub-val θ V)
  sub-comp θ (pm V M) = pm (sub-val θ V) (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M)
  sub-comp θ (push M N) = push (sub-comp θ M) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
  sub-comp θ (app V W) = app (sub-val θ V) (sub-val θ W)
  sub-comp θ (rec V W) = rec (sub-val θ V) (sub-val θ W)
  sub-comp θ (inc M N) = inc (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)

-- syntactic sugar

letv : Γ ⊢ᵛ X → (Γ ∙ X) ⊢ᵛ Y
     ---------------------------
    → Γ ⊢ᵛ Y
letv V W = sub-val (sub-ex sub-id V) W

letc : Γ ⊢ᵛ X → (Γ ∙ X) ⊢ᶜ Y
     ---------------------------
     → Γ ⊢ᶜ Y
letc V M = sub-comp (sub-ex sub-id V) M

exchg : (Γ ∙ X ∙ Y) ⊢ (Γ ∙ Y ∙ X)
exchg = sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) sub-id) (var here)) (var (there here))

variable
  V V₁ V₂ V₃ W W₁ W₂ : Γ ⊢ᵛ X
  M M₁ M₂ M₃ N N₁ N₂ : Γ ⊢ᶜ X

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

  pm-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X `× Y → (Γ ∙ X ∙ Y) ⊢ᶜ M₁ ≈ M₂ ∶ Z
            -------------------------------------------------------------------
            → Γ ⊢ᶜ pm V₁ M₁ ≈ pm V₂ M₂ ∶ Z

  push-cong : Γ ⊢ᶜ M₁ ≈ M₂ ∶ X → (Γ ∙ X) ⊢ᶜ N₁ ≈ N₂ ∶ Y
            ---------------------------------------------------
            → Γ ⊢ᶜ push M₁ N₁ ≈ push M₂ N₂ ∶ Y

  app-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X `⇒ Y → Γ ⊢ᵛ W₁ ≈ W₂ ∶ X
            ------------------------------------------------
            → Γ ⊢ᶜ app V₁ W₁ ≈ app V₂ W₂ ∶ Y

  rec-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ `ℓ → Γ ⊢ᵛ W₁ ≈ W₂ ∶ `𝓅
            ----------------------------------------
            → Γ ⊢ᶜ rec V₁ W₁ ≈ rec V₂ W₂ ∶ X

  inc-cong : (Γ ∙ `ℓ) ⊢ᶜ M₁ ≈ M₂ ∶ X → (Γ ∙ `𝓅) ⊢ᶜ N₁ ≈ N₂ ∶ X
            ----------------------------------------------------
            → Γ ⊢ᶜ inc M₁ N₁ ≈ inc M₂ N₂ ∶ X

  -- beta/eta rules

  pm-beta : (V : Γ ⊢ᵛ X) → (W : Γ ⊢ᵛ Y) → (M : (Γ ∙ X ∙ Y) ⊢ᶜ Z)
          ------------------------------------------------------------------------
          → Γ ⊢ᶜ pm (pair V₁ V₂) M ≈ sub-comp (sub-ex (sub-ex sub-id V₁) V₂) M ∶ Z

  pm-eta : (V : Γ ⊢ᵛ X `× Y) → (M : (Γ ∙ (X `× Y)) ⊢ᶜ Z)
         -------------------------------------------------------------------------------------------
         → Γ ⊢ᶜ sub-comp (sub-ex sub-id V) M ≈ pm V (sub-comp (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) sub-id) (pair (var (there here)) (var here))) M) ∶ Z

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

  -- rec/inc rules

  inc-weak : (M : Γ ⊢ᶜ X) → (N : (Γ ∙ `𝓅) ⊢ᶜ X)
           ------------------------------------------------
           → Γ ⊢ᶜ inc (wk-comp (wk-wk wk-id) M) N ≈ M ∶ X

  inc-subst : (M : (Γ ∙ `𝓅) ⊢ᶜ X) → (V : Γ ⊢ᵛ `𝓅)
            -----------------------------------------------------------------------
            → Γ ⊢ᶜ inc (rec (var here) (wk V)) M ≈ sub-comp (sub-ex sub-id V) M ∶ X

  inc-ext : (M : (Γ ∙ `ℓ) ⊢ᶜ X) → (V : Γ ⊢ᵛ `ℓ)
          ----------------------------------------------------------------------------------------
          → Γ ⊢ᶜ inc (sub-comp sub-id M) (rec (wk V) (var here)) ≈ sub-comp (sub-ex sub-id V) M ∶ X

  inc-assoc : (M : (Γ ∙ `ℓ ∙ `ℓ) ⊢ᶜ X) → (N : (Γ ∙ `ℓ ∙ `𝓅) ⊢ᶜ X) → (P : (Γ ∙ `𝓅) ⊢ᶜ X)
            ------------------------------------------------------------------------------------------------------------------------------------------------------------
            → Γ ⊢ᶜ inc (inc M N) P ≈ inc (inc (sub-comp exchg M) (wk-comp (wk-cong (wk-wk wk-id)) P)) (inc (sub-comp exchg N) (wk-comp (wk-cong (wk-wk wk-id)) P)) ∶ X

  -- algebraicity rules

  rec-push : (V : Γ ⊢ᵛ `ℓ) → (W : Γ ⊢ᵛ `𝓅) → (M : (Γ ∙ `ℓ) ⊢ᶜ X)
           --------------------------------------------------------
           → Γ ⊢ᶜ push (rec V W) M ≈ rec V W ∶ X

  inc-push : (M : (Γ ∙ `ℓ) ⊢ᶜ X) → (N : (Γ ∙ `𝓅) ⊢ᶜ X) → (P : (Γ ∙ X) ⊢ᶜ Y)
           -------------------------------------------------------------------------------------------------------------------------------
           → Γ ⊢ᶜ push (inc M N) P ≈ inc (push M (wk-comp (wk-cong (wk-wk wk-id)) P)) (push N (wk-comp (wk-cong (wk-wk wk-id)) P)) ∶ Y
