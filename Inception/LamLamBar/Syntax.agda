module Inception.LamLamBar.Syntax where

open import Inception.Prelude

--------------------------------------------------------------------------
-- types and contexts

infix  50 _̃
infixr 40 _`×_
infixr 35 _`+_
infixr 25 _`⇒_

data Ty : Set where
  `𝟙 : Ty
  _̃ : Ty → Ty
  _`×_ _`⇒_ _`+_ : Ty → Ty → Ty

`𝔹 : Ty
`𝔹 = `𝟙 `+ `𝟙

open import Inception.Ctx Ty public

--------------------------------------------------------------------------
-- values and computations

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

  inl : Γ ⊢ᵛ X
      ---------------
      → Γ ⊢ᵛ X `+ Y

  inr : Γ ⊢ᵛ Y
      ---------------
      → Γ ⊢ᵛ X `+ Y

  case : Γ ⊢ᵛ X `+ Y → (Γ ∙ X) ⊢ᵛ Z → (Γ ∙ Y) ⊢ᵛ Z
      ------------------------------------------------
      → Γ ⊢ᵛ Z

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

  colam : (Γ ∙ X ̃) ⊢ᶜ Y
        ----------------
        → Γ ⊢ᶜ X `+ Y

  coapp : Γ ⊢ᶜ X `+ Y → Γ ⊢ᵛ X ̃
        -------------------------
        → Γ ⊢ᶜ Y

--------------------------------------------------------------------------
-- weakenings

mutual
  wk-val : Γ ⊇ Δ → Δ ⊢ᵛ X → Γ ⊢ᵛ X
  wk-val π (var i)        = var (wk-mem π i)
  wk-val π (lam M)        = lam (wk-comp (wk-cong π) M)
  wk-val π (pair V W)     = pair (wk-val π V) (wk-val π W)
  wk-val π unit           = unit
  wk-val π (inl V)        = inl (wk-val π V)
  wk-val π (inr V)        = inr (wk-val π V)
  wk-val π (case V W₁ W₂) = case (wk-val π V) (wk-val (wk-cong π) W₁) (wk-val (wk-cong π) W₂)

  wk-comp : Γ ⊇ Δ → Δ ⊢ᶜ X → Γ ⊢ᶜ X
  wk-comp π (return V)  = return (wk-val π V)
  wk-comp π (pm V M)    = pm (wk-val π V) (wk-comp (wk-cong (wk-cong π)) M)
  wk-comp π (push M N)  = push (wk-comp π M) (wk-comp (wk-cong π) N)
  wk-comp π (app V W)   = app (wk-val π V) (wk-val π W)
  wk-comp π (colam M)   = colam (wk-comp (wk-cong π) M)
  wk-comp π (coapp M V) = coapp (wk-comp π M) (wk-val π V)

wk : Γ ⊢ᵛ X → (Γ ∙ Y) ⊢ᵛ X
wk = wk-val (wk-wk wk-id)

--------------------------------------------------------------------------
-- substitutions

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
  sub-val θ (var i)        = sub-mem θ i
  sub-val θ (lam M)        = lam (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  sub-val θ (pair V W)     = pair (sub-val θ V) (sub-val θ W)
  sub-val θ unit           = unit
  sub-val θ (inl V)        = inl (sub-val θ V)
  sub-val θ (inr V)        = inr (sub-val θ V)
  sub-val θ (case V W₁ W₂) = case (sub-val θ V) (sub-val (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) W₁) (sub-val (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) W₂)

  sub-comp : Γ ⊢ Δ → Δ ⊢ᶜ X → Γ ⊢ᶜ X
  sub-comp θ (return V)  = return (sub-val θ V)
  sub-comp θ (pm V M)    = pm (sub-val θ V) (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M)
  sub-comp θ (push M N)  = push (sub-comp θ M) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
  sub-comp θ (app V W)   = app (sub-val θ V) (sub-val θ W)
  sub-comp θ (colam M)   = colam (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  sub-comp θ (coapp M V) = coapp (sub-comp θ M) (sub-val θ V)

--------------------------------------------------------------------------
-- syntactic sugar

letv : Γ ⊢ᵛ X → (Γ ∙ X) ⊢ᵛ Y
     ---------------------------
     → Γ ⊢ᵛ Y
letv V W = sub-val (sub-ex sub-id V) W

letc : Γ ⊢ᵛ X → (Γ ∙ X) ⊢ᶜ Y
     ---------------------------
     → Γ ⊢ᶜ Y
letc V M = sub-comp (sub-ex sub-id V) M

inlc : Γ ⊢ᶜ X
     ---------------
     → Γ ⊢ᶜ X `+ Y
inlc M = push M (return (inl (var here)))

inrc : Γ ⊢ᶜ Y
     ---------------
     → Γ ⊢ᶜ X `+ Y
inrc M = push M (return (inr (var here)))

vcase : Γ ⊢ᵛ X `+ Y → (Γ ∙ X) ⊢ᶜ Z → (Γ ∙ Y) ⊢ᶜ Z
      ------------------------------------------------
      → Γ ⊢ᶜ Z
vcase V M N = app (case V (lam (wk-comp (wk-wk wk-id) M)) (lam (wk-comp (wk-wk wk-id) N))) unit

ccase : Γ ⊢ᶜ X `+ Y → (Γ ∙ X) ⊢ᶜ Z → (Γ ∙ Y) ⊢ᶜ Z
      ------------------------------------------------
      → Γ ⊢ᶜ Z
ccase M N P = push M (vcase (var here) (wk-comp (wk-cong (wk-wk wk-id)) N) (wk-comp (wk-cong (wk-wk wk-id)) P))

throw : Γ ⊢ᵛ X ̃ → Γ ⊢ᵛ X
      -------------------------
      → Γ ⊢ᶜ Y
throw V W = coapp (return (inl W)) V

catch : (Γ ∙ X ̃) ⊢ᶜ Y → (Γ ∙ X) ⊢ᶜ Y
      ------------------------------------
      → Γ ⊢ᶜ Y
catch M N = ccase (colam M) N (return (var here))

exchg : (Γ ∙ X ∙ Y) ⊢ (Γ ∙ Y ∙ X)
exchg = sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) sub-id) (var here)) (var (there here))

--------------------------------------------------------------------------
-- equational theory

variable
  V V₁ V₂ V₃ W W₁ W₂ W₃ W₄ : Γ ⊢ᵛ X
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

  inl-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X
           ---------------------------------
           → Γ ⊢ᵛ inl V₁ ≈ inl V₂ ∶ X `+ Y

  inr-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ Y
           ---------------------------------
           → Γ ⊢ᵛ inr V₁ ≈ inr V₂ ∶ X `+ Y

  case-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X `+ Y → (Γ ∙ X) ⊢ᵛ W₁ ≈ W₂ ∶ Z → (Γ ∙ Y) ⊢ᵛ W₃ ≈ W₄ ∶ Z
            ---------------------------------------------------------------------------
            → Γ ⊢ᵛ case V₁ W₁ W₃ ≈ case V₂ W₂ W₄ ∶ Z

  -- beta/eta rules

  unit-eta : (V : Γ ⊢ᵛ `𝟙)
           ------------------------
           → Γ ⊢ᵛ V ≈ unit ∶ `𝟙

  case-inl-beta : (V : Γ ⊢ᵛ X) → (W₁ : (Γ ∙ X) ⊢ᵛ Z) (W₂ : (Γ ∙ Y) ⊢ᵛ Z)
                ------------------------------------------------------------
                → Γ ⊢ᵛ case (inl V) W₁ W₂ ≈ sub-val (sub-ex sub-id V) W₁ ∶ Z

  case-inr-beta : (V : Γ ⊢ᵛ Y) → (W₁ : (Γ ∙ X) ⊢ᵛ Z) (W₂ : (Γ ∙ Y) ⊢ᵛ Z)
                ------------------------------------------------------------
                → Γ ⊢ᵛ case (inr V) W₁ W₂ ≈ sub-val (sub-ex sub-id V) W₂ ∶ Z

  case-eta : (V : Γ ⊢ᵛ X `+ Y) → (W : (Γ ∙ X `+ Y) ⊢ᵛ Z)
           ------------------------------------------------
           → Γ ⊢ᵛ sub-val (sub-ex sub-id V) W ≈ case V (sub-val (sub-ex (sub-wk (wk-wk wk-id) sub-id) (inl (var here))) W) (sub-val (sub-ex (sub-wk (wk-wk wk-id) sub-id) (inr (var here))) W) ∶ Z

  lam-eta : (V : Γ ⊢ᵛ X `⇒ Y)
          -----------------------------------------------
          → Γ ⊢ᵛ V ≈ lam (app (wk V) (var here)) ∶ X `⇒ Y

data EqComp Γ where

  -- equivalence rules
  ≈-refl  :
          -------------
          Γ ⊢ᶜ M ≈ M ∶ X

  ≈-sym   : Γ ⊢ᶜ M₁ ≈ M₂ ∶ X
          ------------------
          → Γ ⊢ᶜ M₂ ≈ M₁ ∶ X

  ≈-trans : Γ ⊢ᶜ M₁ ≈ M₂ ∶ X → Γ ⊢ᶜ M₂ ≈ M₃ ∶ X
          ---------------------------------------
          → Γ ⊢ᶜ M₁ ≈ M₃ ∶ X

  -- congruence rules
  return-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X
              ---------------------------------
              → Γ ⊢ᶜ return V₁ ≈ return V₂ ∶ X

  pm-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X `× Y → (Γ ∙ X ∙ Y) ⊢ᶜ M₁ ≈ M₂ ∶ Z
          -------------------------------------------------------
          → Γ ⊢ᶜ pm V₁ M₁ ≈ pm V₂ M₂ ∶ Z

  push-cong : Γ ⊢ᶜ M₁ ≈ M₂ ∶ X → (Γ ∙ X) ⊢ᶜ N₁ ≈ N₂ ∶ Y
            ---------------------------------------------------
            → Γ ⊢ᶜ push M₁ N₁ ≈ push M₂ N₂ ∶ Y

  app-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X `⇒ Y → Γ ⊢ᵛ W₁ ≈ W₂ ∶ X
           ------------------------------------------------
           → Γ ⊢ᶜ app V₁ W₁ ≈ app V₂ W₂ ∶ Y

  colam-cong : (Γ ∙ X ̃) ⊢ᶜ M₁ ≈ M₂ ∶ Y
             -------------------------------------
             → Γ ⊢ᶜ colam M₁ ≈ colam M₂ ∶ X `+ Y

  coapp-cong : Γ ⊢ᶜ M₁ ≈ M₂ ∶ X `+ Y → Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ̃
             ------------------------------------------------
             → Γ ⊢ᶜ coapp M₁ V₁ ≈ coapp M₂ V₂ ∶ Y

  -- beta/eta rules

  pm-beta : (V : Γ ⊢ᵛ X) → (W : Γ ⊢ᵛ Y) → (M : (Γ ∙ X ∙ Y) ⊢ᶜ Z)
          ------------------------------------------------------------------------
          → Γ ⊢ᶜ pm (pair V W) M ≈ sub-comp (sub-ex (sub-ex sub-id V) W) M ∶ Z

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
           --------------------------------------------------------
           → Γ ⊢ᶜ app (lam M) V ≈ sub-comp (sub-ex sub-id V) M ∶ Y

  -- colam/coapp rules

  colam-beta : (M : (Γ ∙ X ̃) ⊢ᶜ Y) → (V : Γ ⊢ᵛ X ̃)
             ------------------------------------------------------------
             → Γ ⊢ᶜ coapp (colam M) V ≈ sub-comp (sub-ex sub-id V) M ∶ Y

  colam-eta : (M : Γ ⊢ᶜ X `+ Y)
            --------------------------------------------------------------------
            → Γ ⊢ᶜ M ≈ colam (coapp (wk-comp (wk-wk wk-id) M) (var here)) ∶ X `+ Y

  -- control rules

  colam-const : (M : Γ ⊢ᶜ Y)
              ----------------------------------------------------
              → Γ ⊢ᶜ colam (wk-comp (wk-wk wk-id) M) ≈ inrc M ∶ X `+ Y

  colam-inr-pass : (M : Γ ⊢ᶜ Y) (N : (Γ ∙ Y) ⊢ᶜ Z)
                 ------------------------------------------------
                 → Γ ⊢ᶜ colam (push (coapp (inrc (wk-comp (wk-wk wk-id) M)) (var here)) (wk-comp (wk-cong (wk-wk wk-id)) N)) ≈ push M (inrc N) ∶ X `+ Z

  colam-inl-jump : (M : Γ ⊢ᶜ X) (N : (Γ ∙ Y) ⊢ᶜ Z)
                 ------------------------------------------------
                 → Γ ⊢ᶜ colam (push (coapp (inlc (wk-comp (wk-wk wk-id) M)) (var here)) (wk-comp (wk-cong (wk-wk wk-id)) N)) ≈ inlc M ∶ X `+ Z

  case-colam-beta : (V : (Γ ∙ X ̃) ⊢ᵛ Y) → (M : (Γ ∙ X) ⊢ᶜ Z) → (N : (Γ ∙ Y) ⊢ᶜ Z)
                  --------------------------------------------------------------------
                  → Γ ⊢ᶜ ccase (colam (return V)) M N ≈ ccase (colam (sub-comp (sub-ex (sub-wk (wk-wk wk-id) sub-id) V) N)) M (return (var here)) ∶ Z

  case-colam-push : (M : (Γ ∙ X ̃) ⊢ᶜ Y) → (N : (Γ ∙ X) ⊢ᶜ Z) → (P : (Γ ∙ Y) ⊢ᶜ Z)
                  --------------------------------------------------------------------
                  → Γ ⊢ᶜ ccase (colam M) N P ≈ ccase (colam (push M (wk-comp (wk-cong (wk-wk wk-id)) P))) N (return (var here)) ∶ Z

  coapp-eta : (M : Γ ⊢ᶜ X `+ Y) → (V : Γ ⊢ᵛ X ̃)
            ------------------------------------------------------------------------
            → Γ ⊢ᶜ coapp M V ≈ ccase M (throw (wk V) (var here)) (return (var here)) ∶ Y
