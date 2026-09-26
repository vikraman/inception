module Inception.Inc.Syntax where

open import Data.Nat

infixr 40 _`×_
infixr 25 _`⇒_

data Ty : Set where
  `𝟙 : Ty
  _`×_ _`⇒_ : Ty -> Ty -> Ty
  `ℓ `𝓅 : Ty

open import Inception.Ctx Ty public

syntax Val Γ A = Γ ⊢ᵛ A

data Val : Ctx -> Ty -> Set

syntax Comp Γ A = Γ ⊢ᶜ A

data Comp : Ctx -> Ty -> Set

data Val where

  var : (i : Γ ∋ A)
      ---------
      -> Γ ⊢ᵛ A

  lam : (Γ ∙ A) ⊢ᶜ B
      -----------------
      -> Γ ⊢ᵛ A `⇒ B

  pair : Γ ⊢ᵛ A -> Γ ⊢ᵛ B
      -------------------
       -> Γ ⊢ᵛ A `× B

  unit :
       -----------
        Γ ⊢ᵛ `𝟙

data Comp where

  return : Γ ⊢ᵛ A
         -----------
         -> Γ ⊢ᶜ A

  pm : Γ ⊢ᵛ A `× B -> (Γ ∙ A ∙ B) ⊢ᶜ C
     -----------------------------------
     -> Γ ⊢ᶜ C

  push : Γ ⊢ᶜ A -> (Γ ∙ A) ⊢ᶜ B
       ---------------------------
       -> Γ ⊢ᶜ B

  app : Γ ⊢ᵛ A `⇒ B -> Γ ⊢ᵛ A
      -------------------------
              -> Γ ⊢ᶜ B

  rec : Γ ⊢ᵛ `ℓ -> Γ ⊢ᵛ `𝓅
      -----------------------
      -> Γ ⊢ᶜ A

  inc : (Γ ∙ `ℓ) ⊢ᶜ A -> (Γ ∙ `𝓅) ⊢ᶜ A
      -----------------------------------
      -> Γ ⊢ᶜ A

mutual
  wk-val : Wk Γ Δ -> Δ ⊢ᵛ A -> Γ ⊢ᵛ A
  wk-val π (var x)         = var (wk-mem π x)
  wk-val π (lam M)         = lam (wk-comp (wk-cong π) M)

  wk-val π (pair V W) = pair (wk-val π V) (wk-val π W)
  wk-val π unit       = unit

  wk-comp : Wk Γ Δ -> Δ ⊢ᶜ A -> Γ ⊢ᶜ A
  wk-comp π (return V)     = return (wk-val π V)
  wk-comp π (pm V M)       = pm (wk-val π V) (wk-comp (wk-cong (wk-cong π)) M)
  wk-comp π (push M N)     = push (wk-comp π M) (wk-comp (wk-cong π) N)
  wk-comp π (app V W)      = app (wk-val π V) (wk-val π W)
  wk-comp π (rec V W)      = rec (wk-val π V) (wk-val π W)
  wk-comp π (inc M N)      = inc (wk-comp (wk-cong π) M) (wk-comp (wk-cong π) N)

wk : Val Γ A -> Val (Γ ∙ B) A
wk = wk-val (wk-wk wk-id)

data Sub (Γ : Ctx) : (Δ : Ctx) -> Set where
  sub-ε : Sub Γ ε
  sub-ex : (θ : Sub Γ Δ) -> (V : Val Γ A) -> Sub Γ (Δ ∙ A)

sub-mem : Sub Γ Δ -> Δ ∋ A -> Val Γ A
sub-mem (sub-ex θ V) here = V
sub-mem (sub-ex θ V) (there i) = sub-mem θ i

sub-wk : Wk Γ Δ -> Sub Δ Ψ -> Sub Γ Ψ
sub-wk π sub-ε = sub-ε
sub-wk π (sub-ex θ V) = sub-ex (sub-wk π θ) (wk-val π V)

sub-id : Sub Γ Γ
sub-id {Γ = ε} = sub-ε
sub-id {Γ = Γ ∙ A} = sub-ex (sub-wk (wk-wk wk-id) sub-id) (var here)

mutual
  sub-val : Sub Γ Δ -> Δ ⊢ᵛ A -> Γ ⊢ᵛ A
  sub-val θ (var x) = sub-mem θ x
  sub-val θ (lam M) = lam (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  sub-val θ (pair V W) = pair (sub-val θ V) (sub-val θ W)
  sub-val θ unit = unit

  sub-comp : Sub Γ Δ -> Δ ⊢ᶜ A -> Γ ⊢ᶜ A
  sub-comp θ (return V) = return (sub-val θ V)
  sub-comp θ (pm V M) = pm (sub-val θ V) (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M)
  sub-comp θ (push M N) = push (sub-comp θ M) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
  sub-comp θ (app V W) = app (sub-val θ V) (sub-val θ W)
  sub-comp θ (rec V W) = rec (sub-val θ V) (sub-val θ W)
  sub-comp θ (inc M N) = inc (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)

-- syntactic sugar

letv : Γ ⊢ᵛ A -> (Γ ∙ A) ⊢ᵛ B
     ---------------------------
    -> Γ ⊢ᵛ B
letv V W = sub-val (sub-ex sub-id V) W

letc : Γ ⊢ᵛ A -> (Γ ∙ A) ⊢ᶜ B
     ---------------------------
     -> Γ ⊢ᶜ B
letc V M = sub-comp (sub-ex sub-id V) M

exchg : Sub (Γ ∙ A ∙ B)(Γ ∙ B ∙ A)
exchg = sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) sub-id) (var here)) (var (there here))

variable
  V V₁ V₂ V₃ W W₁ W₂ : Γ ⊢ᵛ A
  M M₁ M₂ M₃ N N₁ N₂ : Γ ⊢ᶜ A

syntax EqVal Γ A e₁ e₂ = Γ ⊢ᵛ e₁ ≈ e₂ ∶ A

syntax EqComp Γ A e₁ e₂ = Γ ⊢ᶜ e₁ ≈ e₂ ∶ A

data EqVal (Γ : Ctx) : (A : Ty) -> Γ ⊢ᵛ A -> Γ ⊢ᵛ A -> Set

data EqComp (Γ : Ctx) : (A : Ty) -> Γ ⊢ᶜ A -> Γ ⊢ᶜ A -> Set

data EqVal Γ where

  -- equivalence rules
  ≈-refl  :
          -------------
          Γ ⊢ᵛ V ≈ V ∶ A

  ≈-sym   : Γ ⊢ᵛ V₁ ≈ V₂ ∶ A
          ------------------
          -> Γ ⊢ᵛ V₂ ≈ V₁ ∶ A

  ≈-trans : Γ ⊢ᵛ V₁ ≈ V₂ ∶ A -> Γ ⊢ᵛ V₂ ≈ V₃ ∶ A
          -------------------------------------
          -> Γ ⊢ᵛ V₁ ≈ V₃ ∶ A

  -- congruence rules
  lam-cong : (Γ ∙ A) ⊢ᶜ M₁ ≈ M₂ ∶ B
           ---------------------------------
           -> Γ ⊢ᵛ lam M₁ ≈ lam M₂ ∶ A `⇒ B

  pair-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ A -> Γ ⊢ᵛ W₁ ≈ W₂ ∶ B
            ----------------------------------------
            -> Γ ⊢ᵛ pair V₁ W₁ ≈ pair V₂ W₂ ∶ A `× B

  -- beta/eta rules

  unit-eta : (V : Γ ⊢ᵛ `𝟙)
           ------------------------
           -> Γ ⊢ᵛ V ≈ unit ∶ `𝟙

  lam-eta : (V : Γ ⊢ᵛ A `⇒ B)
          ---------------------------
          -> Γ ⊢ᵛ V ≈ lam (app (wk V) (var here)) ∶ A `⇒ B

data EqComp Γ where

  -- equivalence rules
  ≈-refl  :
          -------------
          Γ ⊢ᶜ M ≈ M ∶ A

  ≈-sym   : Γ ⊢ᶜ M₁ ≈ M₂ ∶ A
          -------------------
          -> Γ ⊢ᶜ M₂ ≈ M₁ ∶ A

  ≈-trans : Γ ⊢ᶜ M₁ ≈ M₂ ∶ A -> Γ ⊢ᶜ M₂ ≈ M₃ ∶ A
          -------------------------------------
          -> Γ ⊢ᶜ M₁ ≈ M₃ ∶ A

  -- congruence rules
  return-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ A
             -----------------------------
             -> Γ ⊢ᶜ return V₁ ≈ return V₂ ∶ A

  pm-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ A `× B -> (Γ ∙ A ∙ B) ⊢ᶜ M₁ ≈ M₂ ∶ C
            -------------------------------------------------------------------
            -> Γ ⊢ᶜ pm V₁ M₁ ≈ pm V₂ M₂ ∶ C

  push-cong : Γ ⊢ᶜ M₁ ≈ M₂ ∶ A -> (Γ ∙ A) ⊢ᶜ N₁ ≈ N₂ ∶ B
            ---------------------------------------------------
            -> Γ ⊢ᶜ push M₁ N₁ ≈ push M₂ N₂ ∶ B

  app-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ A `⇒ B -> Γ ⊢ᵛ W₁ ≈ W₂ ∶ A
            ------------------------------------------------
            -> Γ ⊢ᶜ app V₁ W₁ ≈ app V₂ W₂ ∶ B

  rec-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ `ℓ -> Γ ⊢ᵛ W₁ ≈ W₂ ∶ `𝓅
            ----------------------------------------
            -> Γ ⊢ᶜ rec V₁ W₁ ≈ rec V₂ W₂ ∶ A

  inc-cong : (Γ ∙ `ℓ) ⊢ᶜ M₁ ≈ M₂ ∶ A -> (Γ ∙ `𝓅) ⊢ᶜ N₁ ≈ N₂ ∶ A
            ----------------------------------------------------
            -> Γ ⊢ᶜ inc M₁ N₁ ≈ inc M₂ N₂ ∶ A

  -- beta/eta rules

  pm-beta : (V : Γ ⊢ᵛ A) -> (W : Γ ⊢ᵛ B) -> (M : (Γ ∙ A ∙ B) ⊢ᶜ C)
          ------------------------------------------------------------------------
          -> Γ ⊢ᶜ pm (pair V₁ V₂) M ≈ sub-comp (sub-ex (sub-ex sub-id V₁) V₂) M ∶ C

  pm-eta : (V : Γ ⊢ᵛ A `× B) -> (M : (Γ ∙ (A `× B)) ⊢ᶜ C)
         -------------------------------------------------------------------------------------------
         -> Γ ⊢ᶜ sub-comp (sub-ex sub-id V) M ≈ pm V (sub-comp (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) sub-id) (pair (var (there here)) (var here))) M) ∶ C

  return-beta : (V : Γ ⊢ᵛ A) -> (M : (Γ ∙ A) ⊢ᶜ B)
               ---------------------------------------------------------------
               -> Γ ⊢ᶜ push (return V) M ≈ sub-comp (sub-ex sub-id V) M ∶ B

  return-eta : (M : Γ ⊢ᶜ A)
              -----------------------
              -> Γ ⊢ᶜ M ≈ push M (return (var here)) ∶ A

  push-eta : (M : Γ ⊢ᶜ A) -> (N : (Γ ∙ A) ⊢ᶜ B) -> (P : (Γ ∙ B) ⊢ᶜ C)
           ----------------------------------------------------------------
           -> Γ ⊢ᶜ push (push M N) P ≈ push M (push N (wk-comp (wk-cong (wk-wk wk-id)) P)) ∶ C

  lam-beta : (M : (Γ ∙ A) ⊢ᶜ B) -> (V : Γ ⊢ᵛ A)
           ------------------------------------------------
           -> Γ ⊢ᶜ app (lam M) V ≈ sub-comp (sub-ex sub-id V) M ∶ B

  -- rec/inc rules

  inc-weak : (M : Γ ⊢ᶜ A) -> (N : (Γ ∙ `𝓅) ⊢ᶜ A)
           ------------------------------------------------
           -> Γ ⊢ᶜ inc (wk-comp (wk-wk wk-id) M) N ≈ M ∶ A

  inc-subst : (M : (Γ ∙ `𝓅) ⊢ᶜ A) -> (V : Γ ⊢ᵛ `𝓅)
            -----------------------------------------------------------------------
            -> Γ ⊢ᶜ inc (rec (var here) (wk V)) M ≈ sub-comp (sub-ex sub-id V) M ∶ A

  inc-ext : (M : (Γ ∙ `ℓ) ⊢ᶜ A) -> (V : Γ ⊢ᵛ `ℓ)
          ----------------------------------------------------------------------------------------
          -> Γ ⊢ᶜ inc (sub-comp sub-id M) (rec (wk V) (var here)) ≈ sub-comp (sub-ex sub-id V) M ∶ A

  inc-assoc : (M : (Γ ∙ `ℓ ∙ `ℓ) ⊢ᶜ A) -> (N : (Γ ∙ `ℓ ∙ `𝓅) ⊢ᶜ A) -> (P : (Γ ∙ `𝓅) ⊢ᶜ A)
            ------------------------------------------------------------------------------------------------------------------------------------------------------------
            -> Γ ⊢ᶜ inc (inc M N) P ≈ inc (inc (sub-comp exchg M) (wk-comp (wk-cong (wk-wk wk-id)) P)) (inc (sub-comp exchg N) (wk-comp (wk-cong (wk-wk wk-id)) P)) ∶ A

  -- algebraicity rules

  rec-push : (V : Γ ⊢ᵛ `ℓ) -> (W : Γ ⊢ᵛ `𝓅) -> (M : (Γ ∙ `ℓ) ⊢ᶜ A)
           --------------------------------------------------------
           -> Γ ⊢ᶜ push (rec V W) M ≈ rec V W ∶ A

  inc-push : (M : (Γ ∙ `ℓ) ⊢ᶜ A) -> (N : (Γ ∙ `𝓅) ⊢ᶜ A) -> (P : (Γ ∙ A) ⊢ᶜ B)
           -------------------------------------------------------------------------------------------------------------------------------
           -> Γ ⊢ᶜ push (inc M N) P ≈ inc (push M (wk-comp (wk-cong (wk-wk wk-id)) P)) (push N (wk-comp (wk-cong (wk-wk wk-id)) P)) ∶ B
