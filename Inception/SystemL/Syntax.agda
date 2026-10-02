module Inception.SystemL.Syntax where

open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym)
open Eq.≡-Reasoning

infixr 25 _`⇒_

data Ty : Set where
  `⊥ `𝟙 `𝓅 : Ty
  _`×_ _`⇒_ _`+_ : (X : Ty) → (Y : Ty) → Ty

infixr 30 ¬_
¬_ : Ty → Ty
¬ X = X `⇒ `⊥

open import Inception.Ctx Ty public

syntax Cmd Γ Δ = Γ ⊢ Δ

syntax Val Γ X Δ = Γ ⊢ᵛ X ∣ Δ

syntax Tm Γ X Δ = Γ ⊢ᵗ X ∣ Δ

syntax CoTm Γ X Δ = Γ ∣ X ⊢ᵏ Δ

data Cmd : Ctx → Ctx → Set

data Val : Ctx → Ty → Ctx → Set

data Tm : Ctx → Ty → Ctx → Set

data CoTm : Ctx → Ty → Ctx → Set

data Cmd where

  cut : (X : Ty) → (M : Γ ⊢ᵗ X ∣ Δ) → (K : Γ ∣ X ⊢ᵏ Δ)
      ----------------------------------------------------
      → Γ ⊢ Δ

data Val where

  var : (i : Γ ∋ X)
       ----------------
       → Γ ⊢ᵛ X ∣ Δ

  lam : (M : (Γ ∙ X) ⊢ᵗ Y ∣ Δ)
      ------------------------
      → Γ ⊢ᵛ X `⇒ Y ∣ Δ

  unit :
       -----------------
         Γ ⊢ᵛ `𝟙 ∣ Δ

  pair : Γ ⊢ᵛ X ∣ Δ → Γ ⊢ᵛ Y ∣ Δ
       ---------------------------
       → Γ ⊢ᵛ X `× Y ∣ Δ

  inl : Γ ⊢ᵛ X ∣ Δ
      -----------------
      → Γ ⊢ᵛ X `+ Y ∣ Δ

  inr : Γ ⊢ᵛ Y ∣ Δ
      -----------------
      → Γ ⊢ᵛ X `+ Y ∣ Δ

data Tm where

  ret : (V : Γ ⊢ᵛ X ∣ Δ)
      ---------------------
      → Γ ⊢ᵗ X ∣ Δ

  μ : (C : Γ ⊢ (Δ ∙ X))
    ------------------------
    → Γ ⊢ᵗ X ∣ Δ

data CoTm where

  covar : (i : Δ ∋ X)
        ---------------
        → Γ ∣ X ⊢ᵏ Δ

  app : (V : Γ ⊢ᵛ X ∣ Δ) → (K : Γ ∣ Y ⊢ᵏ Δ)
      ---------------------------------------
      → Γ ∣ X `⇒ Y ⊢ᵏ Δ

  fst : (K : Γ ∣ X ⊢ᵏ Δ)
      -------------------
      → Γ ∣ X `× Y ⊢ᵏ Δ

  snd : (K : Γ ∣ Y ⊢ᵏ Δ)
      -------------------
      → Γ ∣ X `× Y ⊢ᵏ Δ

  case : (K : Γ ∣ X ⊢ᵏ Δ) → (L : Γ ∣ Y ⊢ᵏ Δ)
       -------------------------------------------
       → Γ ∣ X `+ Y ⊢ᵏ Δ

  μ̃ : (M : (Γ ∙ X) ⊢ Δ)
    ------------------------
    → Γ ∣ X ⊢ᵏ Δ

  tp : -------------
       Γ ∣ `⊥ ⊢ᵏ Δ

mutual
  wk-cmd : Γ ⊇ Ψ → Δ ⊇ Ξ → Ψ ⊢ Ξ → Γ ⊢ Δ
  wk-cmd π ρ (cut X M K) = cut X (wk-tm π ρ M) (wk-cotm π ρ K)

  wk-val : Γ ⊇ Ψ → Δ ⊇ Ξ → Ψ ⊢ᵛ X ∣ Ξ → Γ ⊢ᵛ X ∣ Δ
  wk-val π ρ (var i)    = var (wk-mem π i)
  wk-val π ρ (lam M)    = lam (wk-tm (wk-cong π) ρ M)
  wk-val π ρ unit       = unit
  wk-val π ρ (pair V W) = pair (wk-val π ρ V) (wk-val π ρ W)
  wk-val π ρ (inl V)    = inl (wk-val π ρ V)
  wk-val π ρ (inr W)    = inr (wk-val π ρ W)

  wk-tm : Γ ⊇ Ψ → Δ ⊇ Ξ → Ψ ⊢ᵗ X ∣ Ξ → Γ ⊢ᵗ X ∣ Δ
  wk-tm π ρ (ret V) = ret (wk-val π ρ V)
  wk-tm π ρ (μ C)   = μ (wk-cmd π (wk-cong ρ) C)

  wk-cotm : Γ ⊇ Ψ → Δ ⊇ Ξ → Ψ ∣ X ⊢ᵏ Ξ → Γ ∣ X ⊢ᵏ Δ
  wk-cotm π ρ (covar i) = covar (wk-mem ρ i)
  wk-cotm π ρ (app V K) = app (wk-val π ρ V) (wk-cotm π ρ K)
  wk-cotm π ρ (fst K)   = fst (wk-cotm π ρ K)
  wk-cotm π ρ (snd K)   = snd (wk-cotm π ρ K)
  wk-cotm π ρ (case K L) = case (wk-cotm π ρ K) (wk-cotm π ρ L)
  wk-cotm π ρ (μ̃ C)     = μ̃ (wk-cmd (wk-cong π) ρ C)
  wk-cotm π ρ tp        = tp

wkᵛ : Γ ⊢ᵛ X ∣ Δ → (Γ ∙ Y) ⊢ᵛ X ∣ Δ
wkᵛ = wk-val (wk-wk wk-id) wk-id

wkᵗ : Γ ⊢ᵗ X ∣ Δ → (Γ ∙ Y) ⊢ᵗ X ∣ Δ
wkᵗ = wk-tm (wk-wk wk-id) wk-id

wkᵏ : Γ ∣ X ⊢ᵏ Δ → (Γ ∙ Y) ∣ X ⊢ᵏ Δ
wkᵏ = wk-cotm (wk-wk wk-id) wk-id

wk̃ᵛ : Γ ⊢ᵛ X ∣ Δ → Γ ⊢ᵛ X ∣ (Δ ∙ Y)
wk̃ᵛ = wk-val wk-id (wk-wk wk-id)

wk̃ᵗ : Γ ⊢ᵗ X ∣ Δ → Γ ⊢ᵗ X ∣ (Δ ∙ Y)
wk̃ᵗ = wk-tm wk-id (wk-wk wk-id)

wk̃ᵏ : Γ ∣ X ⊢ᵏ Δ → Γ ∣ X ⊢ᵏ (Δ ∙ Y)
wk̃ᵏ = wk-cotm wk-id (wk-wk wk-id)

syntax Subᵛ Γ Δ Ψ = Γ ⊢ Ψ ∣ Δ

Subᵛ : Ctx → Ctx → Ctx → Set
Subᵛ Γ Δ = Sub (λ X → Γ ⊢ᵛ X ∣ Δ)

syntax Subᵏ Γ Δ Ψ = Γ ∣ Ψ ⊢ Δ

Subᵏ : Ctx → Ctx → Ctx → Set
Subᵏ Γ Δ = Sub (λ X → Γ ∣ X ⊢ᵏ Δ)

sub-wk : Ψ ⊇ Γ → Ξ ⊇ Δ → Γ ⊢ Γ₁ ∣ Δ → Ψ ⊢ Γ₁ ∣ Ξ
sub-wk π ρ = sub-map (wk-val π ρ)

cosub-wk : Ψ ⊇ Γ → Ξ ⊇ Δ → Γ ∣ Δ₁ ⊢ Δ → Ψ ∣ Δ₁ ⊢ Ξ
cosub-wk π ρ = sub-map (wk-cotm π ρ)

sub-id : Γ ⊢ Γ ∣ Δ
sub-id {Γ = ε} = sub-ε
sub-id {Γ = Γ ∙ X} = sub-ex (sub-wk (wk-wk wk-id) wk-id sub-id) (var here)

cosub-id : Γ ∣ Δ ⊢ Δ
cosub-id {Δ = ε} = sub-ε
cosub-id {Δ = Δ ∙ X} = sub-ex (cosub-wk wk-id (wk-wk wk-id) cosub-id) (covar here)

mutual
  sub-cmd : Γ ⊢ Ψ ∣ Δ → Γ ∣ Ξ ⊢ Δ → Ψ ⊢ Ξ → Γ ⊢ Δ
  sub-cmd θ φ (cut X M K) = cut X (sub-tm θ φ M) (sub-cotm θ φ K)

  sub-val : Γ ⊢ Ψ ∣ Δ → Γ ∣ Ξ ⊢ Δ → Ψ ⊢ᵛ X ∣ Ξ → Γ ⊢ᵛ X ∣ Δ
  sub-val θ φ (var i)    = sub-mem θ i
  sub-val θ φ (lam M)    = lam (sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M)
  sub-val θ φ unit       = unit
  sub-val θ φ (pair V W) = pair (sub-val θ φ V) (sub-val θ φ W)
  sub-val θ φ (inl V)    = inl (sub-val θ φ V)
  sub-val θ φ (inr W)    = inr (sub-val θ φ W)

  sub-tm : Γ ⊢ Ψ ∣ Δ → Γ ∣ Ξ ⊢ Δ → Ψ ⊢ᵗ X ∣ Ξ → Γ ⊢ᵗ X ∣ Δ
  sub-tm θ φ (ret V) = ret (sub-val θ φ V)
  sub-tm θ φ (μ C)   = μ (sub-cmd (sub-wk wk-id (wk-wk wk-id) θ) (sub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) C)

  sub-cotm : Γ ⊢ Ψ ∣ Δ → Γ ∣ Ξ ⊢ Δ → Ψ ∣ X ⊢ᵏ Ξ → Γ ∣ X ⊢ᵏ Δ
  sub-cotm θ φ (covar i) = sub-mem φ i
  sub-cotm θ φ (app V K) = app (sub-val θ φ V) (sub-cotm θ φ K)
  sub-cotm θ φ (fst K)   = fst (sub-cotm θ φ K)
  sub-cotm θ φ (snd K)   = snd (sub-cotm θ φ K)
  sub-cotm θ φ (case K L) = case (sub-cotm θ φ K) (sub-cotm θ φ L)
  sub-cotm θ φ (μ̃ C)     = μ̃ (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) C)
  sub-cotm θ φ tp        = tp

-- syntactic sugar

letv : Γ ⊢ᵛ X ∣ Δ → (Γ ∙ X) ⊢ᵗ Y ∣ Δ → Γ ⊢ᵗ Y ∣ Δ
letv V M = sub-tm (sub-ex sub-id V) cosub-id M

lett : Γ ⊢ᵗ X ∣ Δ → (Γ ∙ X) ⊢ᵗ Y ∣ Δ → Γ ⊢ᵗ Y ∣ Δ
lett {X = X} {Y = Y} N M = μ (cut X (wk̃ᵗ N) (μ̃ (cut Y (wk̃ᵗ M) (covar here))))

letc : Γ ∣ X ⊢ᵏ Δ → Γ ⊢ (Δ ∙ X) → Γ ⊢ Δ
letc K C = sub-cmd sub-id (sub-ex cosub-id K) C

letvc : Γ ⊢ᵛ X ∣ Δ → (Γ ∙ X) ⊢ Δ → Γ ⊢ Δ
letvc V C = sub-cmd (sub-ex sub-id V) cosub-id C

applyL : Γ ⊢ᵛ (X `⇒ Y) ∣ Δ → Γ ⊢ᵛ X ∣ Δ → Γ ⊢ᵗ Y ∣ Δ
applyL f a = μ (cut _ (ret (wk̃ᵛ f)) (app (wk̃ᵛ a) (covar here)))

projFst : Γ ⊢ᵛ (X `× Y) ∣ Δ → Γ ⊢ᵗ X ∣ Δ
projFst p = μ (cut _ (ret (wk̃ᵛ p)) (fst (covar here)))

projSnd : Γ ⊢ᵛ (X `× Y) ∣ Δ → Γ ⊢ᵗ Y ∣ Δ
projSnd p = μ (cut _ (ret (wk̃ᵛ p)) (snd (covar here)))

letpv : Γ ⊢ᵛ X `× Z ∣ Δ → (Γ ∙ X ∙ Z) ⊢ᵗ Y ∣ Δ → Γ ⊢ᵗ Y ∣ Δ
letpv V M = lett (projFst V) (lett (projSnd (wkᵛ V)) M)

efq : Γ ⊢ᵗ `⊥ ∣ Δ → Γ ⊢ᵗ X ∣ Δ
efq u = μ (cut `⊥ (wk̃ᵗ u) tp)

variable
  V V₁ V₂ V₃ W₁ W₂ : Γ ⊢ᵛ X ∣ Δ
  M M₁ M₂ M₃ : Γ ⊢ᵗ X ∣ Δ
  K K₁ K₂ K₃ L₁ L₂ : Γ ∣ X ⊢ᵏ Δ
  C C₁ C₂ C₃ : Γ ⊢ Δ

syntax EqVal Γ Δ X V₁ V₂ = Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ∣ Δ

data EqVal (Γ Δ : Ctx) : (X : Ty) → Γ ⊢ᵛ X ∣ Δ → Γ ⊢ᵛ X ∣ Δ → Set

syntax EqTm Γ Δ X M₁ M₂ = Γ ⊢ᵗ M₁ ≈ M₂ ∶ X ∣ Δ

data EqTm (Γ Δ : Ctx) : (X : Ty) → Γ ⊢ᵗ X ∣ Δ → Γ ⊢ᵗ X ∣ Δ → Set

syntax EqCoTm Γ Δ X K₁ K₂ = Γ ∣ K₁ ≈ K₂ ∶ X ⊢ᵏ Δ

data EqCoTm (Γ Δ : Ctx) : (X : Ty) → Γ ∣ X ⊢ᵏ Δ → Γ ∣ X ⊢ᵏ Δ → Set

syntax EqCmd Γ Δ C₁ C₂ = Γ ⊢ C₁ ≈ C₂ ⊣ Δ

data EqCmd (Γ Δ : Ctx) : Γ ⊢ Δ → Γ ⊢ Δ → Set

data EqVal Γ Δ where

  -- equivalence rules
  ≈-refl  :
          -----------------
          Γ ⊢ᵛ V ≈ V ∶ X ∣ Δ

  ≈-sym   : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ∣ Δ
          ----------------------
          → Γ ⊢ᵛ V₂ ≈ V₁ ∶ X ∣ Δ

  ≈-trans : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ∣ Δ → Γ ⊢ᵛ V₂ ≈ V₃ ∶ X ∣ Δ
          -----------------------------------------------
          → Γ ⊢ᵛ V₁ ≈ V₃ ∶ X ∣ Δ

  -- congruence rules
  lam-cong : (Γ ∙ X) ⊢ᵗ M₁ ≈ M₂ ∶ Y ∣ Δ
           -----------------------------------
           → Γ ⊢ᵛ lam M₁ ≈ lam M₂ ∶ X `⇒ Y ∣ Δ

  pair-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ∣ Δ → Γ ⊢ᵛ W₁ ≈ W₂ ∶ Y ∣ Δ
            ---------------------------------------------------
            → Γ ⊢ᵛ pair V₁ W₁ ≈ pair V₂ W₂ ∶ X `× Y ∣ Δ

  inl-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ∣ Δ
           -----------------------------------
           → Γ ⊢ᵛ inl V₁ ≈ inl V₂ ∶ X `+ Y ∣ Δ

  inr-cong : Γ ⊢ᵛ W₁ ≈ W₂ ∶ Y ∣ Δ
           -----------------------------------
           → Γ ⊢ᵛ inr W₁ ≈ inr W₂ ∶ X `+ Y ∣ Δ

  -- eta rules

  unit-eta : (V : Γ ⊢ᵛ `𝟙 ∣ Δ)
           --------------------------
           → Γ ⊢ᵛ V ≈ unit ∶ `𝟙 ∣ Δ

  lam-eta : (V : Γ ⊢ᵛ X `⇒ Y ∣ Δ)
          -----------------------------------------------------------------------------------
          → Γ ⊢ᵛ V ≈ lam (μ (cut (X `⇒ Y) (ret (wk̃ᵛ (wkᵛ V))) (app (var here) (covar here)))) ∶ X `⇒ Y ∣ Δ

data EqTm Γ Δ where

  -- equivalence rules
  ≈-refl  :
          -----------------
          Γ ⊢ᵗ M ≈ M ∶ X ∣ Δ

  ≈-sym   : Γ ⊢ᵗ M₁ ≈ M₂ ∶ X ∣ Δ
          ----------------------
          → Γ ⊢ᵗ M₂ ≈ M₁ ∶ X ∣ Δ

  ≈-trans : Γ ⊢ᵗ M₁ ≈ M₂ ∶ X ∣ Δ → Γ ⊢ᵗ M₂ ≈ M₃ ∶ X ∣ Δ
          -----------------------------------------------
          → Γ ⊢ᵗ M₁ ≈ M₃ ∶ X ∣ Δ

  -- congruence rules
  ret-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ∣ Δ
           ---------------------------
           → Γ ⊢ᵗ ret V₁ ≈ ret V₂ ∶ X ∣ Δ

  μ-cong : Γ ⊢ C₁ ≈ C₂ ⊣ (Δ ∙ X)
         -------------------------
         → Γ ⊢ᵗ μ C₁ ≈ μ C₂ ∶ X ∣ Δ

  -- structural (eta) rule

  μ-eta : (M : Γ ⊢ᵗ X ∣ Δ)
        ------------------------------------------
        → Γ ⊢ᵗ M ≈ μ (cut X (wk̃ᵗ M) (covar here)) ∶ X ∣ Δ

  -- surjective pairing

  pair-eta : (V : Γ ⊢ᵛ X `× Y ∣ Δ)
           ---------------------------------------------------------------------------------
           → Γ ⊢ᵗ ret V
              ≈ lett (μ (cut (X `× Y) (ret (wk̃ᵛ V)) (fst (covar here))))
                     (lett (μ (cut (X `× Y) (ret (wk̃ᵛ (wkᵛ V))) (snd (covar here))))
                           (ret (pair (var (there here)) (var here))))
              ∶ X `× Y ∣ Δ

data EqCoTm Γ Δ where

  -- equivalence rules
  ≈-refl  :
          ---------------------
          Γ ∣ K ≈ K ∶ X ⊢ᵏ Δ

  ≈-sym   : Γ ∣ K₁ ≈ K₂ ∶ X ⊢ᵏ Δ
          ----------------------
          → Γ ∣ K₂ ≈ K₁ ∶ X ⊢ᵏ Δ

  ≈-trans : Γ ∣ K₁ ≈ K₂ ∶ X ⊢ᵏ Δ → Γ ∣ K₂ ≈ K₃ ∶ X ⊢ᵏ Δ
          -----------------------------------------------
          → Γ ∣ K₁ ≈ K₃ ∶ X ⊢ᵏ Δ

  -- congruence rules
  app-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ∣ Δ → Γ ∣ K₁ ≈ K₂ ∶ Y ⊢ᵏ Δ
           -----------------------------------------------------
           → Γ ∣ app V₁ K₁ ≈ app V₂ K₂ ∶ X `⇒ Y ⊢ᵏ Δ

  fst-cong : Γ ∣ K₁ ≈ K₂ ∶ X ⊢ᵏ Δ
           -----------------------------------
           → Γ ∣ fst K₁ ≈ fst K₂ ∶ X `× Y ⊢ᵏ Δ

  snd-cong : Γ ∣ K₁ ≈ K₂ ∶ Y ⊢ᵏ Δ
           -----------------------------------
           → Γ ∣ snd K₁ ≈ snd K₂ ∶ X `× Y ⊢ᵏ Δ

  case-cong : Γ ∣ K₁ ≈ K₂ ∶ X ⊢ᵏ Δ → Γ ∣ L₁ ≈ L₂ ∶ Y ⊢ᵏ Δ
            -------------------------------------------------------
            → Γ ∣ case K₁ L₁ ≈ case K₂ L₂ ∶ X `+ Y ⊢ᵏ Δ

  μ̃-cong : (Γ ∙ X) ⊢ C₁ ≈ C₂ ⊣ Δ
         ---------------------------
         → Γ ∣ μ̃ C₁ ≈ μ̃ C₂ ∶ X ⊢ᵏ Δ

  -- structural (eta) rule

  μ̃-eta : (K : Γ ∣ X ⊢ᵏ Δ)
        --------------------------------------------
        → Γ ∣ K ≈ μ̃ (cut X (ret (var here)) (wkᵏ K)) ∶ X ⊢ᵏ Δ

  case-eta : (K : Γ ∣ X `+ Y ⊢ᵏ Δ)
           -----------------------------------------------------------------------------
           → Γ ∣ K ≈ case (μ̃ (cut (X `+ Y) (ret (inl (var here))) (wkᵏ K)))
                           (μ̃ (cut (X `+ Y) (ret (inr (var here))) (wkᵏ K))) ∶ X `+ Y ⊢ᵏ Δ

data EqCmd Γ Δ where

  -- equivalence rules
  ≈-refl  :
          -----------
          Γ ⊢ C ≈ C ⊣ Δ

  ≈-sym   : Γ ⊢ C₁ ≈ C₂ ⊣ Δ
          -----------------
          → Γ ⊢ C₂ ≈ C₁ ⊣ Δ

  ≈-trans : Γ ⊢ C₁ ≈ C₂ ⊣ Δ → Γ ⊢ C₂ ≈ C₃ ⊣ Δ
          -----------------------------------
          → Γ ⊢ C₁ ≈ C₃ ⊣ Δ

  -- congruence rule
  cut-cong : Γ ⊢ᵗ M₁ ≈ M₂ ∶ X ∣ Δ → Γ ∣ K₁ ≈ K₂ ∶ X ⊢ᵏ Δ
           --------------------------------------------------------------
           → Γ ⊢ cut X M₁ K₁ ≈ cut X M₂ K₂ ⊣ Δ

  -- beta rules (cut elimination)

  μ-beta : (C : Γ ⊢ (Δ ∙ X)) → (K : Γ ∣ X ⊢ᵏ Δ)
         -----------------------------------------
         → Γ ⊢ cut X (μ C) K ≈ letc K C ⊣ Δ

  μ̃-beta : (V : Γ ⊢ᵛ X ∣ Δ) → (C : (Γ ∙ X) ⊢ Δ)
         -------------------------------------------
         → Γ ⊢ cut X (ret V) (μ̃ C) ≈ letvc V C ⊣ Δ

  app-beta : (M : (Γ ∙ X) ⊢ᵗ Y ∣ Δ) → (V : Γ ⊢ᵛ X ∣ Δ) → (K : Γ ∣ Y ⊢ᵏ Δ)
           ---------------------------------------------------------------------------
           → Γ ⊢ cut (X `⇒ Y) (ret (lam M)) (app V K) ≈ cut Y (letv V M) K ⊣ Δ

  fst-beta : (V : Γ ⊢ᵛ X ∣ Δ) → (W : Γ ⊢ᵛ Y ∣ Δ) → (K : Γ ∣ X ⊢ᵏ Δ)
           -----------------------------------------------------------------
           → Γ ⊢ cut (X `× Y) (ret (pair V W)) (fst K) ≈ cut X (ret V) K ⊣ Δ

  snd-beta : (V : Γ ⊢ᵛ X ∣ Δ) → (W : Γ ⊢ᵛ Y ∣ Δ) → (K : Γ ∣ Y ⊢ᵏ Δ)
           -----------------------------------------------------------------
           → Γ ⊢ cut (X `× Y) (ret (pair V W)) (snd K) ≈ cut Y (ret W) K ⊣ Δ

  inl-beta : (V : Γ ⊢ᵛ X ∣ Δ) → (K : Γ ∣ X ⊢ᵏ Δ) → (L : Γ ∣ Y ⊢ᵏ Δ)
           -----------------------------------------------------------------------
           → Γ ⊢ cut (X `+ Y) (ret (inl V)) (case K L) ≈ cut X (ret V) K ⊣ Δ

  inr-beta : (W : Γ ⊢ᵛ Y ∣ Δ) → (K : Γ ∣ X ⊢ᵏ Δ) → (L : Γ ∣ Y ⊢ᵏ Δ)
           -----------------------------------------------------------------------
           → Γ ⊢ cut (X `+ Y) (ret (inr W)) (case K L) ≈ cut Y (ret W) L ⊣ Δ

--------------------------------------------------------------------------
-- weakening lemmas

mutual
  wk-cmd-id-β : (C : Γ ⊢ Δ) → wk-cmd wk-id wk-id C ≡ C
  wk-cmd-id-β (cut X M K) = cong₂ (cut X) (wk-tm-id-β M) (wk-cotm-id-β K)

  wk-val-id-β : (V : Γ ⊢ᵛ X ∣ Δ) → wk-val wk-id wk-id V ≡ V
  wk-val-id-β (var i)    = refl
  wk-val-id-β (lam M)    = cong lam (wk-tm-id-β M)
  wk-val-id-β unit       = refl
  wk-val-id-β (pair V W) = cong₂ pair (wk-val-id-β V) (wk-val-id-β W)
  wk-val-id-β (inl V)    = cong inl (wk-val-id-β V)
  wk-val-id-β (inr W)    = cong inr (wk-val-id-β W)

  wk-tm-id-β : (M : Γ ⊢ᵗ X ∣ Δ) → wk-tm wk-id wk-id M ≡ M
  wk-tm-id-β (ret V) = cong ret (wk-val-id-β V)
  wk-tm-id-β (μ C)   = cong μ (wk-cmd-id-β C)

  wk-cotm-id-β : (K : Γ ∣ X ⊢ᵏ Δ) → wk-cotm wk-id wk-id K ≡ K
  wk-cotm-id-β (covar i)  = refl
  wk-cotm-id-β (app V K)  = cong₂ app (wk-val-id-β V) (wk-cotm-id-β K)
  wk-cotm-id-β (fst K)    = cong fst (wk-cotm-id-β K)
  wk-cotm-id-β (snd K)    = cong snd (wk-cotm-id-β K)
  wk-cotm-id-β (case K L) = cong₂ case (wk-cotm-id-β K) (wk-cotm-id-β L)
  wk-cotm-id-β (μ̃ C)      = cong μ̃ (wk-cmd-id-β C)
  wk-cotm-id-β tp         = refl

{-# REWRITE wk-cmd-id-β wk-val-id-β wk-tm-id-β wk-cotm-id-β #-}

wk-cmd-id-η : (π : Γ ⊇ Γ) (ρ : Δ ⊇ Δ) (C : Γ ⊢ Δ) → wk-cmd π ρ C ≡ C
wk-cmd-id-η π ρ C = cong₂ (λ δ σ → wk-cmd δ σ C) (wk-id-η π) (wk-id-η ρ)

wk-val-id-η : (π : Γ ⊇ Γ) (ρ : Δ ⊇ Δ) (V : Γ ⊢ᵛ X ∣ Δ) → wk-val π ρ V ≡ V
wk-val-id-η π ρ V = cong₂ (λ δ σ → wk-val δ σ V) (wk-id-η π) (wk-id-η ρ)

wk-tm-id-η : (π : Γ ⊇ Γ) (ρ : Δ ⊇ Δ) (M : Γ ⊢ᵗ X ∣ Δ) → wk-tm π ρ M ≡ M
wk-tm-id-η π ρ M = cong₂ (λ δ σ → wk-tm δ σ M) (wk-id-η π) (wk-id-η ρ)

wk-cotm-id-η : (π : Γ ⊇ Γ) (ρ : Δ ⊇ Δ) (K : Γ ∣ X ⊢ᵏ Δ) → wk-cotm π ρ K ≡ K
wk-cotm-id-η π ρ K = cong₂ (λ δ σ → wk-cotm δ σ K) (wk-id-η π) (wk-id-η ρ)

{-# REWRITE wk-cmd-id-η wk-val-id-η wk-tm-id-η wk-cotm-id-η #-}

mutual
  wk-cmd-wk-η : (C : Γ ⊢ Δ) (π : Ψ ⊇ Γ₁) (δ : Γ₁ ⊇ Γ) (ρ : Ψ₁ ⊇ Ξ) (σ : Ξ ⊇ Δ)
               → wk-cmd π ρ (wk-cmd δ σ C) ≡ wk-cmd (wk-trans π δ) (wk-trans ρ σ) C
  wk-cmd-wk-η (cut X M K) π δ ρ σ = cong₂ (cut X) (wk-tm-wk-η M π δ ρ σ) (wk-cotm-wk-η K π δ ρ σ)

  wk-val-wk-η : (V : Γ ⊢ᵛ X ∣ Δ) (π : Ψ ⊇ Γ₁) (δ : Γ₁ ⊇ Γ) (ρ : Ψ₁ ⊇ Ξ) (σ : Ξ ⊇ Δ)
               → wk-val π ρ (wk-val δ σ V) ≡ wk-val (wk-trans π δ) (wk-trans ρ σ) V
  wk-val-wk-η (var i) π δ ρ σ    = refl
  wk-val-wk-η (lam M) π δ ρ σ    = cong lam (wk-tm-wk-η M (wk-cong π) (wk-cong δ) ρ σ)
  wk-val-wk-η unit π δ ρ σ       = refl
  wk-val-wk-η (pair V W) π δ ρ σ = cong₂ pair (wk-val-wk-η V π δ ρ σ) (wk-val-wk-η W π δ ρ σ)
  wk-val-wk-η (inl V) π δ ρ σ    = cong inl (wk-val-wk-η V π δ ρ σ)
  wk-val-wk-η (inr W) π δ ρ σ    = cong inr (wk-val-wk-η W π δ ρ σ)

  wk-tm-wk-η : (M : Γ ⊢ᵗ X ∣ Δ) (π : Ψ ⊇ Γ₁) (δ : Γ₁ ⊇ Γ) (ρ : Ψ₁ ⊇ Ξ) (σ : Ξ ⊇ Δ)
              → wk-tm π ρ (wk-tm δ σ M) ≡ wk-tm (wk-trans π δ) (wk-trans ρ σ) M
  wk-tm-wk-η (ret V) π δ ρ σ = cong ret (wk-val-wk-η V π δ ρ σ)
  wk-tm-wk-η (μ C) π δ ρ σ   = cong μ (wk-cmd-wk-η C π δ (wk-cong ρ) (wk-cong σ))

  wk-cotm-wk-η : (K : Γ ∣ X ⊢ᵏ Δ) (π : Ψ ⊇ Γ₁) (δ : Γ₁ ⊇ Γ) (ρ : Ψ₁ ⊇ Ξ) (σ : Ξ ⊇ Δ)
               → wk-cotm π ρ (wk-cotm δ σ K) ≡ wk-cotm (wk-trans π δ) (wk-trans ρ σ) K
  wk-cotm-wk-η (covar i) π δ ρ σ  = refl
  wk-cotm-wk-η (app V K) π δ ρ σ  = cong₂ app (wk-val-wk-η V π δ ρ σ) (wk-cotm-wk-η K π δ ρ σ)
  wk-cotm-wk-η (fst K) π δ ρ σ    = cong fst (wk-cotm-wk-η K π δ ρ σ)
  wk-cotm-wk-η (snd K) π δ ρ σ    = cong snd (wk-cotm-wk-η K π δ ρ σ)
  wk-cotm-wk-η (case K L) π δ ρ σ = cong₂ case (wk-cotm-wk-η K π δ ρ σ) (wk-cotm-wk-η L π δ ρ σ)
  wk-cotm-wk-η (μ̃ C) π δ ρ σ      = cong μ̃ (wk-cmd-wk-η C (wk-cong π) (wk-cong δ) ρ σ)
  wk-cotm-wk-η tp π δ ρ σ         = refl

{-# REWRITE wk-cmd-wk-η wk-val-wk-η wk-tm-wk-η wk-cotm-wk-η #-}

--------------------------------------------------------------------------
-- weakening/substitution

sub-wk-id-Δ-β : (ρ : Ξ ⊇ Δ) → sub-map (wk-val wk-id ρ) (sub-id {Γ} {Δ}) ≡ sub-id {Γ} {Ξ}
sub-wk-id-Δ-β {Γ = ε}     ρ = refl
sub-wk-id-Δ-β {Γ = Γ ∙ X} ρ = cong (λ θ → sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (sub-wk-id-Δ-β ρ)
{-# REWRITE sub-wk-id-Δ-β #-}

sub-wk-id-Δ-η : (π : Γ ⊇ Γ) (ρ : Ξ ⊇ Δ) → sub-map (wk-val π ρ) (sub-id {Γ} {Δ}) ≡ sub-id {Γ} {Ξ}
sub-wk-id-Δ-η π ρ = cong (λ δ → sub-wk δ ρ sub-id) (wk-id-η π)
{-# REWRITE sub-wk-id-Δ-η #-}

cosub-wk-id-Γ-β : (π : Ψ ⊇ Γ) → sub-map (wk-cotm π wk-id) (cosub-id {Γ} {Δ}) ≡ cosub-id {Ψ} {Δ}
cosub-wk-id-Γ-β {Δ = ε}     π = refl
cosub-wk-id-Γ-β {Δ = Δ ∙ X} π = cong (λ φ → sub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) (cosub-wk-id-Γ-β π)
{-# REWRITE cosub-wk-id-Γ-β #-}

cosub-wk-id-Γ-η : (π : Ψ ⊇ Γ) (ρ : Δ ⊇ Δ) → sub-map (wk-cotm π ρ) (cosub-id {Γ} {Δ}) ≡ cosub-id {Ψ} {Δ}
cosub-wk-id-Γ-η π ρ = cong (λ σ → cosub-wk π σ cosub-id) (wk-id-η ρ)
{-# REWRITE cosub-wk-id-Γ-η #-}

mutual
  wk-cmd-sub-η : (π : Γ₁ ⊇ Γ) (ρ : Ξ ⊇ Δ) (θ : Γ ⊢ Ψ ∣ Δ) (φ : Γ ∣ Ψ₁ ⊢ Δ) (C : Ψ ⊢ Ψ₁)
             → wk-cmd π ρ (sub-cmd θ φ C) ≡ sub-cmd (sub-wk π ρ θ) (cosub-wk π ρ φ) C
  wk-cmd-sub-η π ρ θ φ (cut X M K) = cong₂ (cut X) (wk-tm-sub-η π ρ θ φ M) (wk-cotm-sub-η π ρ θ φ K)

  wk-val-sub-η : (π : Γ₁ ⊇ Γ) (ρ : Ξ ⊇ Δ) (θ : Γ ⊢ Ψ ∣ Δ) (φ : Γ ∣ Ψ₁ ⊢ Δ) (V : Ψ ⊢ᵛ X ∣ Ψ₁)
             → wk-val π ρ (sub-val θ φ V) ≡ sub-val (sub-wk π ρ θ) (cosub-wk π ρ φ) V
  wk-val-sub-η π ρ θ φ (var i)    = refl
  wk-val-sub-η π ρ θ φ (lam M)    =
    cong lam (wk-tm-sub-η (wk-cong π) ρ (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M)
  wk-val-sub-η π ρ θ φ unit       = refl
  wk-val-sub-η π ρ θ φ (pair V W) = cong₂ pair (wk-val-sub-η π ρ θ φ V) (wk-val-sub-η π ρ θ φ W)
  wk-val-sub-η π ρ θ φ (inl V)    = cong inl (wk-val-sub-η π ρ θ φ V)
  wk-val-sub-η π ρ θ φ (inr W)    = cong inr (wk-val-sub-η π ρ θ φ W)

  wk-tm-sub-η : (π : Γ₁ ⊇ Γ) (ρ : Ξ ⊇ Δ) (θ : Γ ⊢ Ψ ∣ Δ) (φ : Γ ∣ Ψ₁ ⊢ Δ) (M : Ψ ⊢ᵗ X ∣ Ψ₁)
            → wk-tm π ρ (sub-tm θ φ M) ≡ sub-tm (sub-wk π ρ θ) (cosub-wk π ρ φ) M
  wk-tm-sub-η π ρ θ φ (ret V) = cong ret (wk-val-sub-η π ρ θ φ V)
  wk-tm-sub-η π ρ θ φ (μ C)   =
    cong μ (wk-cmd-sub-η π (wk-cong ρ) (sub-wk wk-id (wk-wk wk-id) θ) (sub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) C)

  wk-cotm-sub-η : (π : Γ₁ ⊇ Γ) (ρ : Ξ ⊇ Δ) (θ : Γ ⊢ Ψ ∣ Δ) (φ : Γ ∣ Ψ₁ ⊢ Δ) (K : Ψ ∣ X ⊢ᵏ Ψ₁)
              → wk-cotm π ρ (sub-cotm θ φ K) ≡ sub-cotm (sub-wk π ρ θ) (cosub-wk π ρ φ) K
  wk-cotm-sub-η π ρ θ φ (covar i)  = refl
  wk-cotm-sub-η π ρ θ φ (app V K)  = cong₂ app (wk-val-sub-η π ρ θ φ V) (wk-cotm-sub-η π ρ θ φ K)
  wk-cotm-sub-η π ρ θ φ (fst K)    = cong fst (wk-cotm-sub-η π ρ θ φ K)
  wk-cotm-sub-η π ρ θ φ (snd K)    = cong snd (wk-cotm-sub-η π ρ θ φ K)
  wk-cotm-sub-η π ρ θ φ (case K L) = cong₂ case (wk-cotm-sub-η π ρ θ φ K) (wk-cotm-sub-η π ρ θ φ L)
  wk-cotm-sub-η π ρ θ φ (μ̃ C)      =
    cong μ̃ (wk-cmd-sub-η (wk-cong π) ρ (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) C)
  wk-cotm-sub-η π ρ θ φ tp         = refl

{-# REWRITE wk-cmd-sub-η wk-val-sub-η wk-tm-sub-η wk-cotm-sub-η #-}

--------------------------------------------------------------------------
-- substitution precomposed with weakening

sub-pre-idl-β : (π : Γ ⊇ Ψ) → sub-pre (sub-id {Γ} {Δ}) π ≡ sub-wk π wk-id (sub-id {Ψ} {Δ})
sub-pre-idl-β wk-ε        = refl
sub-pre-idl-β (wk-cong π) = cong (λ θ → sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (sub-pre-idl-β π)
sub-pre-idl-β (wk-wk π)   = cong (sub-wk (wk-wk wk-id) wk-id) (sub-pre-idl-β π)
{-# REWRITE sub-pre-idl-β #-}

cosub-pre-idl-β : (ρ : Δ ⊇ Ξ) → sub-pre (cosub-id {Γ} {Δ}) ρ ≡ cosub-wk wk-id ρ (cosub-id {Γ} {Ξ})
cosub-pre-idl-β wk-ε        = refl
cosub-pre-idl-β (wk-cong ρ) = cong (λ φ → sub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) (cosub-pre-idl-β ρ)
cosub-pre-idl-β (wk-wk ρ)   = cong (cosub-wk wk-id (wk-wk wk-id)) (cosub-pre-idl-β ρ)
{-# REWRITE cosub-pre-idl-β #-}

mutual
  sub-val-wk-η : (θ : Ψ ⊢ Γ ∣ Γ₁) (φ : Ψ ∣ Δ ⊢ Γ₁) (π : Γ ⊇ Ψ₁) (ρ : Δ ⊇ Ξ) (V : Ψ₁ ⊢ᵛ X ∣ Ξ)
                 → sub-val θ φ (wk-val π ρ V) ≡ sub-val (sub-pre θ π) (sub-pre φ ρ) V
  sub-val-wk-η θ φ π ρ (var i)    = refl
  sub-val-wk-η θ φ π ρ (lam M)    =
    cong lam (sub-tm-wk-η (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) (wk-cong π) ρ M)
  sub-val-wk-η θ φ π ρ unit       = refl
  sub-val-wk-η θ φ π ρ (pair V W) = cong₂ pair (sub-val-wk-η θ φ π ρ V) (sub-val-wk-η θ φ π ρ W)
  sub-val-wk-η θ φ π ρ (inl V)    = cong inl (sub-val-wk-η θ φ π ρ V)
  sub-val-wk-η θ φ π ρ (inr W)    = cong inr (sub-val-wk-η θ φ π ρ W)

  sub-tm-wk-η : (θ : Ψ ⊢ Γ ∣ Γ₁) (φ : Ψ ∣ Δ ⊢ Γ₁) (π : Γ ⊇ Ψ₁) (ρ : Δ ⊇ Ξ) (M : Ψ₁ ⊢ᵗ X ∣ Ξ)
                → sub-tm θ φ (wk-tm π ρ M) ≡ sub-tm (sub-pre θ π) (sub-pre φ ρ) M
  sub-tm-wk-η θ φ π ρ (ret V) = cong ret (sub-val-wk-η θ φ π ρ V)
  sub-tm-wk-η θ φ π ρ (μ C)   =
    cong μ (sub-cmd-wk-η (sub-wk wk-id (wk-wk wk-id) θ) (sub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) π (wk-cong ρ) C)

  sub-cotm-wk-η : (θ : Ψ ⊢ Γ ∣ Γ₁) (φ : Ψ ∣ Δ ⊢ Γ₁) (π : Γ ⊇ Ψ₁) (ρ : Δ ⊇ Ξ) (K : Ψ₁ ∣ X ⊢ᵏ Ξ)
                  → sub-cotm θ φ (wk-cotm π ρ K) ≡ sub-cotm (sub-pre θ π) (sub-pre φ ρ) K
  sub-cotm-wk-η θ φ π ρ (covar i)  = refl
  sub-cotm-wk-η θ φ π ρ (app V K)  = cong₂ app (sub-val-wk-η θ φ π ρ V) (sub-cotm-wk-η θ φ π ρ K)
  sub-cotm-wk-η θ φ π ρ (fst K)    = cong fst (sub-cotm-wk-η θ φ π ρ K)
  sub-cotm-wk-η θ φ π ρ (snd K)    = cong snd (sub-cotm-wk-η θ φ π ρ K)
  sub-cotm-wk-η θ φ π ρ (case K L) = cong₂ case (sub-cotm-wk-η θ φ π ρ K) (sub-cotm-wk-η θ φ π ρ L)
  sub-cotm-wk-η θ φ π ρ (μ̃ C)      =
    cong μ̃ (sub-cmd-wk-η (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) (wk-cong π) ρ C)
  sub-cotm-wk-η θ φ π ρ tp         = refl

  sub-cmd-wk-η : (θ : Ψ ⊢ Γ ∣ Γ₁) (φ : Ψ ∣ Δ ⊢ Γ₁) (π : Γ ⊇ Ψ₁) (ρ : Δ ⊇ Ξ) (C : Ψ₁ ⊢ Ξ)
                 → sub-cmd θ φ (wk-cmd π ρ C) ≡ sub-cmd (sub-pre θ π) (sub-pre φ ρ) C
  sub-cmd-wk-η θ φ π ρ (cut X M K) = cong₂ (cut X) (sub-tm-wk-η θ φ π ρ M) (sub-cotm-wk-η θ φ π ρ K)

{-# REWRITE sub-val-wk-η sub-tm-wk-η sub-cotm-wk-η sub-cmd-wk-η #-}

--------------------------------------------------------------------------
-- substitution composition

sub-∘ : Γ ⊢ Γ₁ ∣ Δ → Γ ∣ Ξ ⊢ Δ → Γ₁ ⊢ Ψ ∣ Ξ → Γ ⊢ Ψ ∣ Δ
sub-∘ θ φ = sub-map (sub-val θ φ)

cosub-∘ : Γ ⊢ Γ₁ ∣ Δ → Γ ∣ Ξ ⊢ Δ → Γ₁ ∣ Ψ ⊢ Ξ → Γ ∣ Ψ ⊢ Δ
cosub-∘ θ φ = sub-map (sub-cotm θ φ)

mutual
  sub-cmd-sub-η : (θ₁ : Γ ⊢ Γ₁ ∣ Δ) (φ₁ : Γ ∣ Ξ ⊢ Δ) (θ₂ : Γ₁ ⊢ Ψ ∣ Ξ) (φ₂ : Γ₁ ∣ Ψ₁ ⊢ Ξ) (C : Ψ ⊢ Ψ₁)
              → sub-cmd θ₁ φ₁ (sub-cmd θ₂ φ₂ C) ≡ sub-cmd (sub-∘ θ₁ φ₁ θ₂) (cosub-∘ θ₁ φ₁ φ₂) C
  sub-cmd-sub-η θ₁ φ₁ θ₂ φ₂ (cut X M K) = cong₂ (cut X) (sub-tm-sub-η θ₁ φ₁ θ₂ φ₂ M) (sub-cotm-sub-η θ₁ φ₁ θ₂ φ₂ K)

  sub-val-sub-η : (θ₁ : Γ ⊢ Γ₁ ∣ Δ) (φ₁ : Γ ∣ Ξ ⊢ Δ) (θ₂ : Γ₁ ⊢ Ψ ∣ Ξ) (φ₂ : Γ₁ ∣ Ψ₁ ⊢ Ξ) (V : Ψ ⊢ᵛ X ∣ Ψ₁)
              → sub-val θ₁ φ₁ (sub-val θ₂ φ₂ V) ≡ sub-val (sub-∘ θ₁ φ₁ θ₂) (cosub-∘ θ₁ φ₁ φ₂) V
  sub-val-sub-η θ₁ φ₁ θ₂ φ₂ (var i)    = refl
  sub-val-sub-η θ₁ φ₁ θ₂ φ₂ (lam M)    =
    cong lam (sub-tm-sub-η (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₁) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₁)
                         (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₂) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₂) M)
  sub-val-sub-η θ₁ φ₁ θ₂ φ₂ unit       = refl
  sub-val-sub-η θ₁ φ₁ θ₂ φ₂ (pair V W) = cong₂ pair (sub-val-sub-η θ₁ φ₁ θ₂ φ₂ V) (sub-val-sub-η θ₁ φ₁ θ₂ φ₂ W)
  sub-val-sub-η θ₁ φ₁ θ₂ φ₂ (inl V)    = cong inl (sub-val-sub-η θ₁ φ₁ θ₂ φ₂ V)
  sub-val-sub-η θ₁ φ₁ θ₂ φ₂ (inr W)    = cong inr (sub-val-sub-η θ₁ φ₁ θ₂ φ₂ W)

  sub-tm-sub-η : (θ₁ : Γ ⊢ Γ₁ ∣ Δ) (φ₁ : Γ ∣ Ξ ⊢ Δ) (θ₂ : Γ₁ ⊢ Ψ ∣ Ξ) (φ₂ : Γ₁ ∣ Ψ₁ ⊢ Ξ) (M : Ψ ⊢ᵗ X ∣ Ψ₁)
             → sub-tm θ₁ φ₁ (sub-tm θ₂ φ₂ M) ≡ sub-tm (sub-∘ θ₁ φ₁ θ₂) (cosub-∘ θ₁ φ₁ φ₂) M
  sub-tm-sub-η θ₁ φ₁ θ₂ φ₂ (ret V) = cong ret (sub-val-sub-η θ₁ φ₁ θ₂ φ₂ V)
  sub-tm-sub-η θ₁ φ₁ θ₂ φ₂ (μ C)   =
    cong μ (sub-cmd-sub-η (sub-wk wk-id (wk-wk wk-id) θ₁) (sub-ex (cosub-wk wk-id (wk-wk wk-id) φ₁) (covar here))
                        (sub-wk wk-id (wk-wk wk-id) θ₂) (sub-ex (cosub-wk wk-id (wk-wk wk-id) φ₂) (covar here)) C)

  sub-cotm-sub-η : (θ₁ : Γ ⊢ Γ₁ ∣ Δ) (φ₁ : Γ ∣ Ξ ⊢ Δ) (θ₂ : Γ₁ ⊢ Ψ ∣ Ξ) (φ₂ : Γ₁ ∣ Ψ₁ ⊢ Ξ) (K : Ψ ∣ X ⊢ᵏ Ψ₁)
               → sub-cotm θ₁ φ₁ (sub-cotm θ₂ φ₂ K) ≡ sub-cotm (sub-∘ θ₁ φ₁ θ₂) (cosub-∘ θ₁ φ₁ φ₂) K
  sub-cotm-sub-η θ₁ φ₁ θ₂ φ₂ (covar i)  = refl
  sub-cotm-sub-η θ₁ φ₁ θ₂ φ₂ (app V K)  = cong₂ app (sub-val-sub-η θ₁ φ₁ θ₂ φ₂ V) (sub-cotm-sub-η θ₁ φ₁ θ₂ φ₂ K)
  sub-cotm-sub-η θ₁ φ₁ θ₂ φ₂ (fst K)    = cong fst (sub-cotm-sub-η θ₁ φ₁ θ₂ φ₂ K)
  sub-cotm-sub-η θ₁ φ₁ θ₂ φ₂ (snd K)    = cong snd (sub-cotm-sub-η θ₁ φ₁ θ₂ φ₂ K)
  sub-cotm-sub-η θ₁ φ₁ θ₂ φ₂ (case K L) = cong₂ case (sub-cotm-sub-η θ₁ φ₁ θ₂ φ₂ K) (sub-cotm-sub-η θ₁ φ₁ θ₂ φ₂ L)
  sub-cotm-sub-η θ₁ φ₁ θ₂ φ₂ (μ̃ C)      =
    cong μ̃ (sub-cmd-sub-η (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₁) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₁)
                        (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₂) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₂) C)
  sub-cotm-sub-η θ₁ φ₁ θ₂ φ₂ tp         = refl

{-# REWRITE sub-cmd-sub-η sub-val-sub-η sub-tm-sub-η sub-cotm-sub-η #-}

--------------------------------------------------------------------------
-- identity substitution

sub-mem-id-β : (i : Γ ∋ X) → sub-mem (sub-id {Γ} {Δ}) i ≡ var i
sub-mem-id-β here      = refl
sub-mem-id-β (there i) = cong (wk-val (wk-wk wk-id) wk-id) (sub-mem-id-β i)
{-# REWRITE sub-mem-id-β #-}

cosub-mem-id-β : (i : Δ ∋ X) → sub-mem (cosub-id {Γ} {Δ}) i ≡ covar i
cosub-mem-id-β here      = refl
cosub-mem-id-β (there i) = cong (wk-cotm wk-id (wk-wk wk-id)) (cosub-mem-id-β i)
{-# REWRITE cosub-mem-id-β #-}

mutual
  sub-cmd-ren-β : (π : Γ ⊇ Ψ) {ρ₁ : Δ ⊇ Δ₁} {π₁ : Γ ⊇ Γ₁} (ρ : Δ ⊇ Ξ) (C : Ψ ⊢ Ξ)
              → sub-cmd (sub-wk π ρ₁ sub-id) (cosub-wk π₁ ρ cosub-id) C ≡ wk-cmd π ρ C
  sub-cmd-ren-β π {ρ₁} {π₁} ρ (cut X M K) = cong₂ (cut X) (sub-tm-ren-β π {ρ₁} {π₁} ρ M) (sub-cotm-ren-β π {ρ₁} {π₁} ρ K)

  sub-val-ren-β : (π : Γ ⊇ Ψ) {ρ₁ : Δ ⊇ Δ₁} {π₁ : Γ ⊇ Γ₁} (ρ : Δ ⊇ Ξ) (V : Ψ ⊢ᵛ X ∣ Ξ)
              → sub-val (sub-wk π ρ₁ sub-id) (cosub-wk π₁ ρ cosub-id) V ≡ wk-val π ρ V
  sub-val-ren-β π {ρ₁} {π₁} ρ (var i)    = refl
  sub-val-ren-β π {ρ₁} {π₁} ρ (lam M)    = cong lam (sub-tm-ren-β (wk-cong π) {ρ₁} {wk-wk π₁} ρ M)
  sub-val-ren-β π {ρ₁} {π₁} ρ unit       = refl
  sub-val-ren-β π {ρ₁} {π₁} ρ (pair V W) = cong₂ pair (sub-val-ren-β π {ρ₁} {π₁} ρ V) (sub-val-ren-β π {ρ₁} {π₁} ρ W)
  sub-val-ren-β π {ρ₁} {π₁} ρ (inl V)    = cong inl (sub-val-ren-β π {ρ₁} {π₁} ρ V)
  sub-val-ren-β π {ρ₁} {π₁} ρ (inr W)    = cong inr (sub-val-ren-β π {ρ₁} {π₁} ρ W)

  sub-tm-ren-β : (π : Γ ⊇ Ψ) {ρ₁ : Δ ⊇ Δ₁} {π₁ : Γ ⊇ Γ₁} (ρ : Δ ⊇ Ξ) (M : Ψ ⊢ᵗ X ∣ Ξ)
             → sub-tm (sub-wk π ρ₁ sub-id) (cosub-wk π₁ ρ cosub-id) M ≡ wk-tm π ρ M
  sub-tm-ren-β π {ρ₁} {π₁} ρ (ret V) = cong ret (sub-val-ren-β π {ρ₁} {π₁} ρ V)
  sub-tm-ren-β π {ρ₁} {π₁} ρ (μ C)   = cong μ (sub-cmd-ren-β π {wk-wk ρ₁} {π₁} (wk-cong ρ) C)

  sub-cotm-ren-β : (π : Γ ⊇ Ψ) {ρ₁ : Δ ⊇ Δ₁} {π₁ : Γ ⊇ Γ₁} (ρ : Δ ⊇ Ξ) (K : Ψ ∣ X ⊢ᵏ Ξ)
               → sub-cotm (sub-wk π ρ₁ sub-id) (cosub-wk π₁ ρ cosub-id) K ≡ wk-cotm π ρ K
  sub-cotm-ren-β π {ρ₁} {π₁} ρ (covar i)  = refl
  sub-cotm-ren-β π {ρ₁} {π₁} ρ (app V K)  = cong₂ app (sub-val-ren-β π {ρ₁} {π₁} ρ V) (sub-cotm-ren-β π {ρ₁} {π₁} ρ K)
  sub-cotm-ren-β π {ρ₁} {π₁} ρ (fst K)    = cong fst (sub-cotm-ren-β π {ρ₁} {π₁} ρ K)
  sub-cotm-ren-β π {ρ₁} {π₁} ρ (snd K)    = cong snd (sub-cotm-ren-β π {ρ₁} {π₁} ρ K)
  sub-cotm-ren-β π {ρ₁} {π₁} ρ (case K L) = cong₂ case (sub-cotm-ren-β π {ρ₁} {π₁} ρ K) (sub-cotm-ren-β π {ρ₁} {π₁} ρ L)
  sub-cotm-ren-β π {ρ₁} {π₁} ρ (μ̃ C)     = cong μ̃ (sub-cmd-ren-β (wk-cong π) {ρ₁} {wk-wk π₁} ρ C)
  sub-cotm-ren-β π {ρ₁} {π₁} ρ tp         = refl

{-# REWRITE sub-cmd-ren-β sub-val-ren-β sub-tm-ren-β sub-cotm-ren-β #-}

sub-cmd-ren-Γ-β : (π : Γ ⊇ Ψ) {ρ : Δ ⊇ Δ₁} (C : Ψ ⊢ Δ) → sub-cmd (sub-wk π ρ sub-id) cosub-id C ≡ wk-cmd π wk-id C
sub-cmd-ren-Γ-β π {ρ} = sub-cmd-ren-β π {ρ} {wk-id} wk-id

sub-val-ren-Γ-β : (π : Γ ⊇ Ψ) {ρ : Δ ⊇ Δ₁} (V : Ψ ⊢ᵛ X ∣ Δ) → sub-val (sub-wk π ρ sub-id) cosub-id V ≡ wk-val π wk-id V
sub-val-ren-Γ-β π {ρ} = sub-val-ren-β π {ρ} {wk-id} wk-id

sub-tm-ren-Γ-β : (π : Γ ⊇ Ψ) {ρ : Δ ⊇ Δ₁} (M : Ψ ⊢ᵗ X ∣ Δ) → sub-tm (sub-wk π ρ sub-id) cosub-id M ≡ wk-tm π wk-id M
sub-tm-ren-Γ-β π {ρ} = sub-tm-ren-β π {ρ} {wk-id} wk-id

sub-cotm-ren-Γ-β : (π : Γ ⊇ Ψ) {ρ : Δ ⊇ Δ₁} (K : Ψ ∣ X ⊢ᵏ Δ) → sub-cotm (sub-wk π ρ sub-id) cosub-id K ≡ wk-cotm π wk-id K
sub-cotm-ren-Γ-β π {ρ} = sub-cotm-ren-β π {ρ} {wk-id} wk-id

{-# REWRITE sub-cmd-ren-Γ-β sub-val-ren-Γ-β sub-tm-ren-Γ-β sub-cotm-ren-Γ-β #-}

sub-cmd-ren-Δ-β : {π : Γ ⊇ Γ₁} (ρ : Δ ⊇ Ξ) (C : Γ ⊢ Ξ) → sub-cmd sub-id (cosub-wk π ρ cosub-id) C ≡ wk-cmd wk-id ρ C
sub-cmd-ren-Δ-β {π = π} = sub-cmd-ren-β wk-id {wk-id} {π}

sub-val-ren-Δ-β : {π : Γ ⊇ Γ₁} (ρ : Δ ⊇ Ξ) (V : Γ ⊢ᵛ X ∣ Ξ) → sub-val sub-id (cosub-wk π ρ cosub-id) V ≡ wk-val wk-id ρ V
sub-val-ren-Δ-β {π = π} = sub-val-ren-β wk-id {wk-id} {π}

sub-tm-ren-Δ-β : {π : Γ ⊇ Γ₁} (ρ : Δ ⊇ Ξ) (M : Γ ⊢ᵗ X ∣ Ξ) → sub-tm sub-id (cosub-wk π ρ cosub-id) M ≡ wk-tm wk-id ρ M
sub-tm-ren-Δ-β {π = π} = sub-tm-ren-β wk-id {wk-id} {π}

sub-cotm-ren-Δ-β : {π : Γ ⊇ Γ₁} (ρ : Δ ⊇ Ξ) (K : Γ ∣ X ⊢ᵏ Ξ) → sub-cotm sub-id (cosub-wk π ρ cosub-id) K ≡ wk-cotm wk-id ρ K
sub-cotm-ren-Δ-β {π = π} = sub-cotm-ren-β wk-id {wk-id} {π}

{-# REWRITE sub-cmd-ren-Δ-β sub-val-ren-Δ-β sub-tm-ren-Δ-β sub-cotm-ren-Δ-β #-}

sub-cmd-id-β : (C : Γ ⊢ Δ) → sub-cmd sub-id cosub-id C ≡ C
sub-cmd-id-β = sub-cmd-ren-β wk-id {wk-id} {wk-id} wk-id

sub-val-id-β : (V : Γ ⊢ᵛ X ∣ Δ) → sub-val sub-id cosub-id V ≡ V
sub-val-id-β = sub-val-ren-β wk-id {wk-id} {wk-id} wk-id

sub-tm-id-β : (M : Γ ⊢ᵗ X ∣ Δ) → sub-tm sub-id cosub-id M ≡ M
sub-tm-id-β = sub-tm-ren-β wk-id {wk-id} {wk-id} wk-id

sub-cotm-id-β : (K : Γ ∣ X ⊢ᵏ Δ) → sub-cotm sub-id cosub-id K ≡ K
sub-cotm-id-β = sub-cotm-ren-β wk-id {wk-id} {wk-id} wk-id

{-# REWRITE sub-cmd-id-β sub-val-id-β sub-tm-id-β sub-cotm-id-β #-}


sub-∘-idr-β : (θ : Γ ⊢ Ψ ∣ Δ) (φ : Γ ∣ Ξ ⊢ Δ) → sub-map (sub-val θ φ) sub-id ≡ θ
sub-∘-idr-β sub-ε        φ = refl
sub-∘-idr-β (sub-ex θ V) φ = cong₂ sub-ex (sub-∘-idr-β θ φ) refl
{-# REWRITE sub-∘-idr-β #-}

cosub-∘-idr-β : (θ : Γ ⊢ Ψ ∣ Δ) (φ : Γ ∣ Ξ ⊢ Δ) → sub-map (sub-cotm θ φ) cosub-id ≡ φ
cosub-∘-idr-β θ sub-ε        = refl
cosub-∘-idr-β θ (sub-ex φ K) = cong₂ sub-ex (cosub-∘-idr-β θ φ) refl
{-# REWRITE cosub-∘-idr-β #-}
