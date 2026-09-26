module Inception.SystemL.Syntax where

open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym)
open Eq.≡-Reasoning

infixr 25 _`⇒_

data Ty : Set where
  `⊥ `Unit `P : Ty
  _`×_ _`⇒_ _`+_ : (X : Ty) -> (Y : Ty) -> Ty

infixr 30 ¬_
¬_ : Ty -> Ty
¬ X = X `⇒ `⊥

open import Inception.Ctx Ty public hiding (C)

syntax Cmd Γ Δ = Γ ⊢ Δ

syntax Val Γ X Δ = Γ ⊢ᵛ X ∣ Δ

syntax Tm Γ X Δ = Γ ⊢ᵗ X ∣ Δ

syntax CoTm Γ X Δ = Γ ∣ X ⊢ᵏ Δ

data Cmd : Ctx -> Ctx -> Set

data Val : Ctx -> Ty -> Ctx -> Set

data Tm : Ctx -> Ty -> Ctx -> Set

data CoTm : Ctx -> Ty -> Ctx -> Set

data Cmd where

  cut : (X : Ty) -> (M : Γ ⊢ᵗ X ∣ Δ) -> (K : Γ ∣ X ⊢ᵏ Δ)
      ----------------------------------------------------
      -> Γ ⊢ Δ

data Val where

  var : (i : Γ ∋ X)
       ----------------
       -> Γ ⊢ᵛ X ∣ Δ

  lam : (M : (Γ ∙ X) ⊢ᵗ Y ∣ Δ)
      ------------------------
      -> Γ ⊢ᵛ X `⇒ Y ∣ Δ

  unit :
       -----------------
         Γ ⊢ᵛ `Unit ∣ Δ

  pair : Γ ⊢ᵛ X ∣ Δ -> Γ ⊢ᵛ Y ∣ Δ
       ---------------------------
       -> Γ ⊢ᵛ X `× Y ∣ Δ

  inl : Γ ⊢ᵛ X ∣ Δ
      -----------------
      -> Γ ⊢ᵛ X `+ Y ∣ Δ

  inr : Γ ⊢ᵛ Y ∣ Δ
      -----------------
      -> Γ ⊢ᵛ X `+ Y ∣ Δ

data Tm where

  ret : (V : Γ ⊢ᵛ X ∣ Δ)
      ---------------------
      -> Γ ⊢ᵗ X ∣ Δ

  μ : (C : Γ ⊢ (Δ ∙ X))
    ------------------------
    -> Γ ⊢ᵗ X ∣ Δ

data CoTm where

  covar : (i : Δ ∋ X)
        ---------------
        -> Γ ∣ X ⊢ᵏ Δ

  app : (V : Γ ⊢ᵛ X ∣ Δ) -> (K : Γ ∣ Y ⊢ᵏ Δ)
      ---------------------------------------
      -> Γ ∣ X `⇒ Y ⊢ᵏ Δ

  fst : (K : Γ ∣ X ⊢ᵏ Δ)
      -------------------
      -> Γ ∣ X `× Y ⊢ᵏ Δ

  snd : (K : Γ ∣ Y ⊢ᵏ Δ)
      -------------------
      -> Γ ∣ X `× Y ⊢ᵏ Δ

  case : (K : Γ ∣ X ⊢ᵏ Δ) -> (L : Γ ∣ Y ⊢ᵏ Δ)
       -------------------------------------------
       -> Γ ∣ X `+ Y ⊢ᵏ Δ

  μ̃ : (M : (Γ ∙ X) ⊢ Δ)
    ------------------------
    -> Γ ∣ X ⊢ᵏ Δ

  tp : -------------
       Γ ∣ `⊥ ⊢ᵏ Δ

mutual
  wk-cmd : Wk Γ Γ₁ -> Wk Δ Δ₁ -> Γ₁ ⊢ Δ₁ -> Γ ⊢ Δ
  wk-cmd π ρ (cut X M K) = cut X (wk-tm π ρ M) (wk-cotm π ρ K)

  wk-val : Wk Γ Γ₁ -> Wk Δ Δ₁ -> Γ₁ ⊢ᵛ X ∣ Δ₁ -> Γ ⊢ᵛ X ∣ Δ
  wk-val π ρ (var i)    = var (wk-mem π i)
  wk-val π ρ (lam M)    = lam (wk-tm (wk-cong π) ρ M)
  wk-val π ρ unit       = unit
  wk-val π ρ (pair V W) = pair (wk-val π ρ V) (wk-val π ρ W)
  wk-val π ρ (inl V)    = inl (wk-val π ρ V)
  wk-val π ρ (inr W)    = inr (wk-val π ρ W)

  wk-tm : Wk Γ Γ₁ -> Wk Δ Δ₁ -> Γ₁ ⊢ᵗ X ∣ Δ₁ -> Γ ⊢ᵗ X ∣ Δ
  wk-tm π ρ (ret V) = ret (wk-val π ρ V)
  wk-tm π ρ (μ C)   = μ (wk-cmd π (wk-cong ρ) C)

  wk-cotm : Wk Γ Γ₁ -> Wk Δ Δ₁ -> Γ₁ ∣ X ⊢ᵏ Δ₁ -> Γ ∣ X ⊢ᵏ Δ
  wk-cotm π ρ (covar i) = covar (wk-mem ρ i)
  wk-cotm π ρ (app V K) = app (wk-val π ρ V) (wk-cotm π ρ K)
  wk-cotm π ρ (fst K)   = fst (wk-cotm π ρ K)
  wk-cotm π ρ (snd K)   = snd (wk-cotm π ρ K)
  wk-cotm π ρ (case K L) = case (wk-cotm π ρ K) (wk-cotm π ρ L)
  wk-cotm π ρ (μ̃ C)     = μ̃ (wk-cmd (wk-cong π) ρ C)
  wk-cotm π ρ tp        = tp

wkᵛ : Γ ⊢ᵛ X ∣ Δ -> (Γ ∙ Y) ⊢ᵛ X ∣ Δ
wkᵛ = wk-val (wk-wk wk-id) wk-id

wkᵗ : Γ ⊢ᵗ X ∣ Δ -> (Γ ∙ Y) ⊢ᵗ X ∣ Δ
wkᵗ = wk-tm (wk-wk wk-id) wk-id

wkᵏ : Γ ∣ X ⊢ᵏ Δ -> (Γ ∙ Y) ∣ X ⊢ᵏ Δ
wkᵏ = wk-cotm (wk-wk wk-id) wk-id

wk̃ᵛ : Γ ⊢ᵛ X ∣ Δ -> Γ ⊢ᵛ X ∣ (Δ ∙ Y)
wk̃ᵛ = wk-val wk-id (wk-wk wk-id)

wk̃ᵗ : Γ ⊢ᵗ X ∣ Δ -> Γ ⊢ᵗ X ∣ (Δ ∙ Y)
wk̃ᵗ = wk-tm wk-id (wk-wk wk-id)

wk̃ᵏ : Γ ∣ X ⊢ᵏ Δ -> Γ ∣ X ⊢ᵏ (Δ ∙ Y)
wk̃ᵏ = wk-cotm wk-id (wk-wk wk-id)

data Sub (Γ Δ : Ctx) : (Γ₁ : Ctx) -> Set where
  sub-ε : Sub Γ Δ ε
  sub-ex : (θ : Sub Γ Δ Γ₁) -> (V : Γ ⊢ᵛ X ∣ Δ) -> Sub Γ Δ (Γ₁ ∙ X)

data CoSub (Γ Δ : Ctx) : (Δ₁ : Ctx) -> Set where
  cosub-ε : CoSub Γ Δ ε
  cosub-ex : (φ : CoSub Γ Δ Δ₁) -> (K : Γ ∣ X ⊢ᵏ Δ) -> CoSub Γ Δ (Δ₁ ∙ X)

sub-mem : Sub Γ Δ Γ₁ -> Γ₁ ∋ X -> Γ ⊢ᵛ X ∣ Δ
sub-mem (sub-ex θ V) here = V
sub-mem (sub-ex θ V) (there i) = sub-mem θ i

cosub-mem : CoSub Γ Δ Δ₁ -> Δ₁ ∋ X -> Γ ∣ X ⊢ᵏ Δ
cosub-mem (cosub-ex φ K) here = K
cosub-mem (cosub-ex φ K) (there i) = cosub-mem φ i

sub-wk : Wk Γ₁ Γ -> Wk Δ₁ Δ -> Sub Γ Δ Γ₂ -> Sub Γ₁ Δ₁ Γ₂
sub-wk π ρ sub-ε = sub-ε
sub-wk π ρ (sub-ex θ V) = sub-ex (sub-wk π ρ θ) (wk-val π ρ V)

cosub-wk : Wk Γ₁ Γ -> Wk Δ₁ Δ -> CoSub Γ Δ Δ₂ -> CoSub Γ₁ Δ₁ Δ₂
cosub-wk π ρ cosub-ε = cosub-ε
cosub-wk π ρ (cosub-ex φ K) = cosub-ex (cosub-wk π ρ φ) (wk-cotm π ρ K)

sub-id : Sub Γ Δ Γ
sub-id {Γ = ε} = sub-ε
sub-id {Γ = Γ ∙ X} = sub-ex (sub-wk (wk-wk wk-id) wk-id sub-id) (var here)

cosub-id : CoSub Γ Δ Δ
cosub-id {Δ = ε} = cosub-ε
cosub-id {Δ = Δ ∙ X} = cosub-ex (cosub-wk wk-id (wk-wk wk-id) cosub-id) (covar here)

mutual
  sub-cmd : Sub Γ Δ Γ₁ -> CoSub Γ Δ Δ₁ -> Γ₁ ⊢ Δ₁ -> Γ ⊢ Δ
  sub-cmd θ φ (cut X M K) = cut X (sub-tm θ φ M) (sub-cotm θ φ K)

  sub-val : Sub Γ Δ Γ₁ -> CoSub Γ Δ Δ₁ -> Γ₁ ⊢ᵛ X ∣ Δ₁ -> Γ ⊢ᵛ X ∣ Δ
  sub-val θ φ (var i)    = sub-mem θ i
  sub-val θ φ (lam M)    = lam (sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M)
  sub-val θ φ unit       = unit
  sub-val θ φ (pair V W) = pair (sub-val θ φ V) (sub-val θ φ W)
  sub-val θ φ (inl V)    = inl (sub-val θ φ V)
  sub-val θ φ (inr W)    = inr (sub-val θ φ W)

  sub-tm : Sub Γ Δ Γ₁ -> CoSub Γ Δ Δ₁ -> Γ₁ ⊢ᵗ X ∣ Δ₁ -> Γ ⊢ᵗ X ∣ Δ
  sub-tm θ φ (ret V) = ret (sub-val θ φ V)
  sub-tm θ φ (μ C)   = μ (sub-cmd (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) C)

  sub-cotm : Sub Γ Δ Γ₁ -> CoSub Γ Δ Δ₁ -> Γ₁ ∣ X ⊢ᵏ Δ₁ -> Γ ∣ X ⊢ᵏ Δ
  sub-cotm θ φ (covar i) = cosub-mem φ i
  sub-cotm θ φ (app V K) = app (sub-val θ φ V) (sub-cotm θ φ K)
  sub-cotm θ φ (fst K)   = fst (sub-cotm θ φ K)
  sub-cotm θ φ (snd K)   = snd (sub-cotm θ φ K)
  sub-cotm θ φ (case K L) = case (sub-cotm θ φ K) (sub-cotm θ φ L)
  sub-cotm θ φ (μ̃ C)     = μ̃ (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) C)
  sub-cotm θ φ tp        = tp

-- syntactic sugar

letv : Γ ⊢ᵛ X ∣ Δ -> (Γ ∙ X) ⊢ᵗ Y ∣ Δ -> Γ ⊢ᵗ Y ∣ Δ
letv V M = sub-tm (sub-ex sub-id V) cosub-id M

lett : Γ ⊢ᵗ X ∣ Δ -> (Γ ∙ X) ⊢ᵗ Y ∣ Δ -> Γ ⊢ᵗ Y ∣ Δ
lett {X = X} {Y = Y} N M = μ (cut X (wk̃ᵗ N) (μ̃ (cut Y (wk̃ᵗ M) (covar here))))

letc : Γ ∣ X ⊢ᵏ Δ -> Γ ⊢ (Δ ∙ X) -> Γ ⊢ Δ
letc K C = sub-cmd sub-id (cosub-ex cosub-id K) C

letvc : Γ ⊢ᵛ X ∣ Δ -> (Γ ∙ X) ⊢ Δ -> Γ ⊢ Δ
letvc V C = sub-cmd (sub-ex sub-id V) cosub-id C

applyL : Γ ⊢ᵛ (X `⇒ Y) ∣ Δ -> Γ ⊢ᵛ X ∣ Δ -> Γ ⊢ᵗ Y ∣ Δ
applyL f a = μ (cut _ (ret (wk̃ᵛ f)) (app (wk̃ᵛ a) (covar here)))

projFst : Γ ⊢ᵛ (X `× Y) ∣ Δ -> Γ ⊢ᵗ X ∣ Δ
projFst p = μ (cut _ (ret (wk̃ᵛ p)) (fst (covar here)))

projSnd : Γ ⊢ᵛ (X `× Y) ∣ Δ -> Γ ⊢ᵗ Y ∣ Δ
projSnd p = μ (cut _ (ret (wk̃ᵛ p)) (snd (covar here)))

letpv : Γ ⊢ᵛ X₁ `× X₂ ∣ Δ -> (Γ ∙ X₁ ∙ X₂) ⊢ᵗ Y ∣ Δ -> Γ ⊢ᵗ Y ∣ Δ
letpv V M = lett (projFst V) (lett (projSnd (wkᵛ V)) M)

efq : Γ ⊢ᵗ `⊥ ∣ Δ -> Γ ⊢ᵗ X ∣ Δ
efq u = μ (cut `⊥ (wk̃ᵗ u) tp)

variable
  V V₁ V₂ V₃ W₁ W₂ : Γ ⊢ᵛ X ∣ Δ
  M M₁ M₂ M₃ : Γ ⊢ᵗ X ∣ Δ
  K K₁ K₂ K₃ L₁ L₂ : Γ ∣ X ⊢ᵏ Δ
  C C₁ C₂ C₃ : Γ ⊢ Δ

syntax EqVal Γ Δ X V₁ V₂ = Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ∣ Δ

data EqVal (Γ Δ : Ctx) : (X : Ty) -> Γ ⊢ᵛ X ∣ Δ -> Γ ⊢ᵛ X ∣ Δ -> Set

syntax EqTm Γ Δ X M₁ M₂ = Γ ⊢ᵗ M₁ ≈ M₂ ∶ X ∣ Δ

data EqTm (Γ Δ : Ctx) : (X : Ty) -> Γ ⊢ᵗ X ∣ Δ -> Γ ⊢ᵗ X ∣ Δ -> Set

syntax EqCoTm Γ Δ X K₁ K₂ = Γ ∣ K₁ ≈ K₂ ∶ X ⊢ᵏ Δ

data EqCoTm (Γ Δ : Ctx) : (X : Ty) -> Γ ∣ X ⊢ᵏ Δ -> Γ ∣ X ⊢ᵏ Δ -> Set

syntax EqCmd Γ Δ C₁ C₂ = Γ ⊢ C₁ ≈ C₂ ⊣ Δ

data EqCmd (Γ Δ : Ctx) : Γ ⊢ Δ -> Γ ⊢ Δ -> Set

data EqVal Γ Δ where

  -- equivalence rules
  ≈-refl  :
          -----------------
          Γ ⊢ᵛ V ≈ V ∶ X ∣ Δ

  ≈-sym   : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ∣ Δ
          ----------------------
          -> Γ ⊢ᵛ V₂ ≈ V₁ ∶ X ∣ Δ

  ≈-trans : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ∣ Δ -> Γ ⊢ᵛ V₂ ≈ V₃ ∶ X ∣ Δ
          -----------------------------------------------
          -> Γ ⊢ᵛ V₁ ≈ V₃ ∶ X ∣ Δ

  -- congruence rules
  lam-cong : (Γ ∙ X) ⊢ᵗ M₁ ≈ M₂ ∶ Y ∣ Δ
           -----------------------------------
           -> Γ ⊢ᵛ lam M₁ ≈ lam M₂ ∶ X `⇒ Y ∣ Δ

  pair-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ∣ Δ -> Γ ⊢ᵛ W₁ ≈ W₂ ∶ Y ∣ Δ
            ---------------------------------------------------
            -> Γ ⊢ᵛ pair V₁ W₁ ≈ pair V₂ W₂ ∶ X `× Y ∣ Δ

  inl-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ∣ Δ
           -----------------------------------
           -> Γ ⊢ᵛ inl V₁ ≈ inl V₂ ∶ X `+ Y ∣ Δ

  inr-cong : Γ ⊢ᵛ W₁ ≈ W₂ ∶ Y ∣ Δ
           -----------------------------------
           -> Γ ⊢ᵛ inr W₁ ≈ inr W₂ ∶ X `+ Y ∣ Δ

  -- eta rules

  unit-eta : (V : Γ ⊢ᵛ `Unit ∣ Δ)
           --------------------------
           -> Γ ⊢ᵛ V ≈ unit ∶ `Unit ∣ Δ

  lam-eta : (V : Γ ⊢ᵛ X `⇒ Y ∣ Δ)
          -----------------------------------------------------------------------------------
          -> Γ ⊢ᵛ V ≈ lam (μ (cut (X `⇒ Y) (ret (wk̃ᵛ (wkᵛ V))) (app (var here) (covar here)))) ∶ X `⇒ Y ∣ Δ

data EqTm Γ Δ where

  -- equivalence rules
  ≈-refl  :
          -----------------
          Γ ⊢ᵗ M ≈ M ∶ X ∣ Δ

  ≈-sym   : Γ ⊢ᵗ M₁ ≈ M₂ ∶ X ∣ Δ
          ----------------------
          -> Γ ⊢ᵗ M₂ ≈ M₁ ∶ X ∣ Δ

  ≈-trans : Γ ⊢ᵗ M₁ ≈ M₂ ∶ X ∣ Δ -> Γ ⊢ᵗ M₂ ≈ M₃ ∶ X ∣ Δ
          -----------------------------------------------
          -> Γ ⊢ᵗ M₁ ≈ M₃ ∶ X ∣ Δ

  -- congruence rules
  ret-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ∣ Δ
           ---------------------------
           -> Γ ⊢ᵗ ret V₁ ≈ ret V₂ ∶ X ∣ Δ

  μ-cong : Γ ⊢ C₁ ≈ C₂ ⊣ (Δ ∙ X)
         -------------------------
         -> Γ ⊢ᵗ μ C₁ ≈ μ C₂ ∶ X ∣ Δ

  -- structural (eta) rule

  μ-eta : (M : Γ ⊢ᵗ X ∣ Δ)
        ------------------------------------------
        -> Γ ⊢ᵗ M ≈ μ (cut X (wk̃ᵗ M) (covar here)) ∶ X ∣ Δ

  -- surjective pairing

  pair-eta : (V : Γ ⊢ᵛ X `× Y ∣ Δ)
           ---------------------------------------------------------------------------------
           -> Γ ⊢ᵗ ret V
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
          -> Γ ∣ K₂ ≈ K₁ ∶ X ⊢ᵏ Δ

  ≈-trans : Γ ∣ K₁ ≈ K₂ ∶ X ⊢ᵏ Δ -> Γ ∣ K₂ ≈ K₃ ∶ X ⊢ᵏ Δ
          -----------------------------------------------
          -> Γ ∣ K₁ ≈ K₃ ∶ X ⊢ᵏ Δ

  -- congruence rules
  app-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ∣ Δ -> Γ ∣ K₁ ≈ K₂ ∶ Y ⊢ᵏ Δ
           -----------------------------------------------------
           -> Γ ∣ app V₁ K₁ ≈ app V₂ K₂ ∶ X `⇒ Y ⊢ᵏ Δ

  fst-cong : Γ ∣ K₁ ≈ K₂ ∶ X ⊢ᵏ Δ
           -----------------------------------
           -> Γ ∣ fst K₁ ≈ fst K₂ ∶ X `× Y ⊢ᵏ Δ

  snd-cong : Γ ∣ K₁ ≈ K₂ ∶ Y ⊢ᵏ Δ
           -----------------------------------
           -> Γ ∣ snd K₁ ≈ snd K₂ ∶ X `× Y ⊢ᵏ Δ

  case-cong : Γ ∣ K₁ ≈ K₂ ∶ X ⊢ᵏ Δ -> Γ ∣ L₁ ≈ L₂ ∶ Y ⊢ᵏ Δ
            -------------------------------------------------------
            -> Γ ∣ case K₁ L₁ ≈ case K₂ L₂ ∶ X `+ Y ⊢ᵏ Δ

  μ̃-cong : (Γ ∙ X) ⊢ C₁ ≈ C₂ ⊣ Δ
         ---------------------------
         -> Γ ∣ μ̃ C₁ ≈ μ̃ C₂ ∶ X ⊢ᵏ Δ

  -- structural (eta) rule

  μ̃-eta : (K : Γ ∣ X ⊢ᵏ Δ)
        --------------------------------------------
        -> Γ ∣ K ≈ μ̃ (cut X (ret (var here)) (wkᵏ K)) ∶ X ⊢ᵏ Δ

  case-eta : (K : Γ ∣ X `+ Y ⊢ᵏ Δ)
           -----------------------------------------------------------------------------
           -> Γ ∣ K ≈ case (μ̃ (cut (X `+ Y) (ret (inl (var here))) (wkᵏ K)))
                           (μ̃ (cut (X `+ Y) (ret (inr (var here))) (wkᵏ K))) ∶ X `+ Y ⊢ᵏ Δ

data EqCmd Γ Δ where

  -- equivalence rules
  ≈-refl  :
          -----------
          Γ ⊢ C ≈ C ⊣ Δ

  ≈-sym   : Γ ⊢ C₁ ≈ C₂ ⊣ Δ
          -----------------
          -> Γ ⊢ C₂ ≈ C₁ ⊣ Δ

  ≈-trans : Γ ⊢ C₁ ≈ C₂ ⊣ Δ -> Γ ⊢ C₂ ≈ C₃ ⊣ Δ
          -----------------------------------
          -> Γ ⊢ C₁ ≈ C₃ ⊣ Δ

  -- congruence rule
  cut-cong : Γ ⊢ᵗ M₁ ≈ M₂ ∶ X ∣ Δ -> Γ ∣ K₁ ≈ K₂ ∶ X ⊢ᵏ Δ
           --------------------------------------------------------------
           -> Γ ⊢ cut X M₁ K₁ ≈ cut X M₂ K₂ ⊣ Δ

  -- beta rules (cut elimination)

  μ-beta : (C : Γ ⊢ (Δ ∙ X)) -> (K : Γ ∣ X ⊢ᵏ Δ)
         -----------------------------------------
         -> Γ ⊢ cut X (μ C) K ≈ letc K C ⊣ Δ

  μ̃-beta : (V : Γ ⊢ᵛ X ∣ Δ) -> (C : (Γ ∙ X) ⊢ Δ)
         -------------------------------------------
         -> Γ ⊢ cut X (ret V) (μ̃ C) ≈ letvc V C ⊣ Δ

  app-beta : (M : (Γ ∙ X) ⊢ᵗ Y ∣ Δ) -> (V : Γ ⊢ᵛ X ∣ Δ) -> (K : Γ ∣ Y ⊢ᵏ Δ)
           ---------------------------------------------------------------------------
           -> Γ ⊢ cut (X `⇒ Y) (ret (lam M)) (app V K) ≈ cut Y (letv V M) K ⊣ Δ

  fst-beta : (V : Γ ⊢ᵛ X ∣ Δ) -> (W : Γ ⊢ᵛ Y ∣ Δ) -> (K : Γ ∣ X ⊢ᵏ Δ)
           -----------------------------------------------------------------
           -> Γ ⊢ cut (X `× Y) (ret (pair V W)) (fst K) ≈ cut X (ret V) K ⊣ Δ

  snd-beta : (V : Γ ⊢ᵛ X ∣ Δ) -> (W : Γ ⊢ᵛ Y ∣ Δ) -> (K : Γ ∣ Y ⊢ᵏ Δ)
           -----------------------------------------------------------------
           -> Γ ⊢ cut (X `× Y) (ret (pair V W)) (snd K) ≈ cut Y (ret W) K ⊣ Δ

  inl-beta : (V : Γ ⊢ᵛ X ∣ Δ) -> (K : Γ ∣ X ⊢ᵏ Δ) -> (L : Γ ∣ Y ⊢ᵏ Δ)
           -----------------------------------------------------------------------
           -> Γ ⊢ cut (X `+ Y) (ret (inl V)) (case K L) ≈ cut X (ret V) K ⊣ Δ

  inr-beta : (W : Γ ⊢ᵛ Y ∣ Δ) -> (K : Γ ∣ X ⊢ᵏ Δ) -> (L : Γ ∣ Y ⊢ᵏ Δ)
           -----------------------------------------------------------------------
           -> Γ ⊢ cut (X `+ Y) (ret (inr W)) (case K L) ≈ cut Y (ret W) L ⊣ Δ

--------------------------------------------------------------------------
-- weakening lemmas

mutual
  wk-cmd-id : (C : Γ ⊢ Δ) -> wk-cmd wk-id wk-id C ≡ C
  wk-cmd-id (cut X M K) = cong₂ (cut X) (wk-tm-id M) (wk-cotm-id K)

  wk-val-id : (V : Γ ⊢ᵛ X ∣ Δ) -> wk-val wk-id wk-id V ≡ V
  wk-val-id (var i)    = cong var wk-mem-id
  wk-val-id (lam M)    = cong lam (wk-tm-id M)
  wk-val-id unit       = refl
  wk-val-id (pair V W) = cong₂ pair (wk-val-id V) (wk-val-id W)
  wk-val-id (inl V)    = cong inl (wk-val-id V)
  wk-val-id (inr W)    = cong inr (wk-val-id W)

  wk-tm-id : (M : Γ ⊢ᵗ X ∣ Δ) -> wk-tm wk-id wk-id M ≡ M
  wk-tm-id (ret V) = cong ret (wk-val-id V)
  wk-tm-id (μ C)   = cong μ (wk-cmd-id C)

  wk-cotm-id : (K : Γ ∣ X ⊢ᵏ Δ) -> wk-cotm wk-id wk-id K ≡ K
  wk-cotm-id (covar i) = cong covar wk-mem-id
  wk-cotm-id (app V K) = cong₂ app (wk-val-id V) (wk-cotm-id K)
  wk-cotm-id (fst K)   = cong fst (wk-cotm-id K)
  wk-cotm-id (snd K)   = cong snd (wk-cotm-id K)
  wk-cotm-id (case K L) = cong₂ case (wk-cotm-id K) (wk-cotm-id L)
  wk-cotm-id (μ̃ C)     = cong μ̃ (wk-cmd-id C)
  wk-cotm-id tp        = refl

mutual
  wk-cmd-trans : (C : Γ ⊢ Δ) (π : Ψ ⊇ Γ₁) (δ : Γ₁ ⊇ Γ) (ρ : Ψ₁ ⊇ Δ₁) (σ : Δ₁ ⊇ Δ)
               -> wk-cmd π ρ (wk-cmd δ σ C) ≡ wk-cmd (wk-trans π δ) (wk-trans ρ σ) C
  wk-cmd-trans (cut X M K) π δ ρ σ = cong₂ (cut X) (wk-tm-trans M π δ ρ σ) (wk-cotm-trans K π δ ρ σ)

  wk-val-trans : (V : Γ ⊢ᵛ X ∣ Δ) (π : Ψ ⊇ Γ₁) (δ : Γ₁ ⊇ Γ) (ρ : Ψ₁ ⊇ Δ₁) (σ : Δ₁ ⊇ Δ)
               -> wk-val π ρ (wk-val δ σ V) ≡ wk-val (wk-trans π δ) (wk-trans ρ σ) V
  wk-val-trans (var i) π δ ρ σ    = cong var (wk-mem-trans i π δ)
  wk-val-trans (lam M) π δ ρ σ    = cong lam (wk-tm-trans M (wk-cong π) (wk-cong δ) ρ σ)
  wk-val-trans unit π δ ρ σ       = refl
  wk-val-trans (pair V W) π δ ρ σ = cong₂ pair (wk-val-trans V π δ ρ σ) (wk-val-trans W π δ ρ σ)
  wk-val-trans (inl V) π δ ρ σ    = cong inl (wk-val-trans V π δ ρ σ)
  wk-val-trans (inr W) π δ ρ σ    = cong inr (wk-val-trans W π δ ρ σ)

  wk-tm-trans : (M : Γ ⊢ᵗ X ∣ Δ) (π : Ψ ⊇ Γ₁) (δ : Γ₁ ⊇ Γ) (ρ : Ψ₁ ⊇ Δ₁) (σ : Δ₁ ⊇ Δ)
              -> wk-tm π ρ (wk-tm δ σ M) ≡ wk-tm (wk-trans π δ) (wk-trans ρ σ) M
  wk-tm-trans (ret V) π δ ρ σ = cong ret (wk-val-trans V π δ ρ σ)
  wk-tm-trans (μ C) π δ ρ σ   = cong μ (wk-cmd-trans C π δ (wk-cong ρ) (wk-cong σ))

  wk-cotm-trans : (K : Γ ∣ X ⊢ᵏ Δ) (π : Ψ ⊇ Γ₁) (δ : Γ₁ ⊇ Γ) (ρ : Ψ₁ ⊇ Δ₁) (σ : Δ₁ ⊇ Δ)
               -> wk-cotm π ρ (wk-cotm δ σ K) ≡ wk-cotm (wk-trans π δ) (wk-trans ρ σ) K
  wk-cotm-trans (covar i) π δ ρ σ = cong covar (wk-mem-trans i ρ σ)
  wk-cotm-trans (app V K) π δ ρ σ = cong₂ app (wk-val-trans V π δ ρ σ) (wk-cotm-trans K π δ ρ σ)
  wk-cotm-trans (fst K) π δ ρ σ   = cong fst (wk-cotm-trans K π δ ρ σ)
  wk-cotm-trans (snd K) π δ ρ σ   = cong snd (wk-cotm-trans K π δ ρ σ)
  wk-cotm-trans (case K L) π δ ρ σ = cong₂ case (wk-cotm-trans K π δ ρ σ) (wk-cotm-trans L π δ ρ σ)
  wk-cotm-trans (μ̃ C) π δ ρ σ     = cong μ̃ (wk-cmd-trans C (wk-cong π) (wk-cong δ) ρ σ)
  wk-cotm-trans tp π δ ρ σ        = refl

--------------------------------------------------------------------------
-- weakening/substitution

sub-wk-trans : {Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ Ψ : Ctx} (π : Γ ⊇ Γ₁) (ρ : Δ ⊇ Δ₁) (δ : Γ₁ ⊇ Γ₂) (σ : Δ₁ ⊇ Δ₂) (θ : Sub Γ₂ Δ₂ Ψ)
             -> sub-wk π ρ (sub-wk δ σ θ) ≡ sub-wk (wk-trans π δ) (wk-trans ρ σ) θ
sub-wk-trans π ρ δ σ sub-ε        = refl
sub-wk-trans π ρ δ σ (sub-ex θ V) = cong₂ sub-ex (sub-wk-trans π ρ δ σ θ) (wk-val-trans V π δ ρ σ)

cosub-wk-trans : {Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ Ψ : Ctx} (π : Γ ⊇ Γ₁) (ρ : Δ ⊇ Δ₁) (δ : Γ₁ ⊇ Γ₂) (σ : Δ₁ ⊇ Δ₂) (φ : CoSub Γ₂ Δ₂ Ψ)
               -> cosub-wk π ρ (cosub-wk δ σ φ) ≡ cosub-wk (wk-trans π δ) (wk-trans ρ σ) φ
cosub-wk-trans π ρ δ σ cosub-ε        = refl
cosub-wk-trans π ρ δ σ (cosub-ex φ K) = cong₂ cosub-ex (cosub-wk-trans π ρ δ σ φ) (wk-cotm-trans K π δ ρ σ)

sub-mem-wk : (π : Γ ⊇ Γ₁) (ρ : Δ ⊇ Δ₁) (θ : Sub Γ₁ Δ₁ Ψ) (i : Ψ ∋ X) -> sub-mem (sub-wk π ρ θ) i ≡ wk-val π ρ (sub-mem θ i)
sub-mem-wk π ρ (sub-ex θ V) here     = refl
sub-mem-wk π ρ (sub-ex θ V) (there i) = sub-mem-wk π ρ θ i

cosub-mem-wk : (π : Γ ⊇ Γ₁) (ρ : Δ ⊇ Δ₁) (φ : CoSub Γ₁ Δ₁ Ψ) (i : Ψ ∋ X) -> cosub-mem (cosub-wk π ρ φ) i ≡ wk-cotm π ρ (cosub-mem φ i)
cosub-mem-wk π ρ (cosub-ex φ K) here     = refl
cosub-mem-wk π ρ (cosub-ex φ K) (there i) = cosub-mem-wk π ρ φ i

sub-wk-id : (θ : Sub Γ Δ Γ₁) -> sub-wk wk-id wk-id θ ≡ θ
sub-wk-id sub-ε        = refl
sub-wk-id (sub-ex θ V) = cong₂ sub-ex (sub-wk-id θ) (wk-val-id V)

cosub-wk-id : (φ : CoSub Γ Δ Δ₁) -> cosub-wk wk-id wk-id φ ≡ φ
cosub-wk-id cosub-ε        = refl
cosub-wk-id (cosub-ex φ K) = cong₂ cosub-ex (cosub-wk-id φ) (wk-cotm-id K)

sub-wk-cong-lemma : (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) (θ : Sub Γ Δ Ψ)
                  -> sub-wk (wk-cong {A = X} π) ρ (sub-wk (wk-wk wk-id) wk-id θ) ≡ sub-wk (wk-wk wk-id) wk-id (sub-wk π ρ θ)
sub-wk-cong-lemma π ρ θ = begin
  sub-wk (wk-cong π) ρ (sub-wk (wk-wk wk-id) wk-id θ)     ≡⟨ sub-wk-trans (wk-cong π) ρ (wk-wk wk-id) wk-id θ ⟩
  sub-wk (wk-wk (wk-trans π wk-id)) (wk-trans ρ wk-id) θ  ≡⟨ cong₂ (λ π ρ -> sub-wk (wk-wk π) ρ θ) (wk-trans-idr π) (wk-trans-idr ρ) ⟩
  sub-wk (wk-wk π) ρ θ                                    ≡˘⟨ cong₂ (λ π ρ -> sub-wk (wk-wk π) ρ θ) (wk-trans-idl π) (wk-trans-idl ρ) ⟩
  sub-wk (wk-wk (wk-trans wk-id π)) (wk-trans wk-id ρ) θ  ≡˘⟨ sub-wk-trans (wk-wk wk-id) wk-id π ρ θ ⟩
  sub-wk (wk-wk wk-id) wk-id (sub-wk π ρ θ)               ∎

cosub-wk-cong-lemma : (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) (φ : CoSub Γ Δ Ψ)
                    -> cosub-wk (wk-cong {A = X} π) ρ (cosub-wk (wk-wk wk-id) wk-id φ) ≡ cosub-wk (wk-wk wk-id) wk-id (cosub-wk π ρ φ)
cosub-wk-cong-lemma π ρ φ = begin
  cosub-wk (wk-cong π) ρ (cosub-wk (wk-wk wk-id) wk-id φ)     ≡⟨ cosub-wk-trans (wk-cong π) ρ (wk-wk wk-id) wk-id φ ⟩
  cosub-wk (wk-wk (wk-trans π wk-id)) (wk-trans ρ wk-id) φ    ≡⟨ cong₂ (λ π ρ -> cosub-wk (wk-wk π) ρ φ) (wk-trans-idr π) (wk-trans-idr ρ) ⟩
  cosub-wk (wk-wk π) ρ φ                                      ≡˘⟨ cong₂ (λ π ρ -> cosub-wk (wk-wk π) ρ φ) (wk-trans-idl π) (wk-trans-idl ρ) ⟩
  cosub-wk (wk-wk (wk-trans wk-id π)) (wk-trans wk-id ρ) φ    ≡˘⟨ cosub-wk-trans (wk-wk wk-id) wk-id π ρ φ ⟩
  cosub-wk (wk-wk wk-id) wk-id (cosub-wk π ρ φ)               ∎

sub-wk-cong-lemma-Δ : (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) (θ : Sub Γ Δ Ψ)
                     -> sub-wk π (wk-cong {A = X} ρ) (sub-wk wk-id (wk-wk wk-id) θ) ≡ sub-wk wk-id (wk-wk wk-id) (sub-wk π ρ θ)
sub-wk-cong-lemma-Δ π ρ θ = begin
  sub-wk π (wk-cong ρ) (sub-wk wk-id (wk-wk wk-id) θ)     ≡⟨ sub-wk-trans π (wk-cong ρ) wk-id (wk-wk wk-id) θ ⟩
  sub-wk (wk-trans π wk-id) (wk-wk (wk-trans ρ wk-id)) θ  ≡⟨ cong₂ (λ π ρ -> sub-wk π (wk-wk ρ) θ) (wk-trans-idr π) (wk-trans-idr ρ) ⟩
  sub-wk π (wk-wk ρ) θ                                    ≡˘⟨ cong₂ (λ π ρ -> sub-wk π (wk-wk ρ) θ) (wk-trans-idl π) (wk-trans-idl ρ) ⟩
  sub-wk (wk-trans wk-id π) (wk-wk (wk-trans wk-id ρ)) θ  ≡˘⟨ sub-wk-trans wk-id (wk-wk wk-id) π ρ θ ⟩
  sub-wk wk-id (wk-wk wk-id) (sub-wk π ρ θ)               ∎

cosub-wk-cong-lemma-Δ : (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) (φ : CoSub Γ Δ Ψ)
                      -> cosub-wk π (wk-cong {A = X} ρ) (cosub-wk wk-id (wk-wk wk-id) φ) ≡ cosub-wk wk-id (wk-wk wk-id) (cosub-wk π ρ φ)
cosub-wk-cong-lemma-Δ π ρ φ = begin
  cosub-wk π (wk-cong ρ) (cosub-wk wk-id (wk-wk wk-id) φ)     ≡⟨ cosub-wk-trans π (wk-cong ρ) wk-id (wk-wk wk-id) φ ⟩
  cosub-wk (wk-trans π wk-id) (wk-wk (wk-trans ρ wk-id)) φ    ≡⟨ cong₂ (λ π ρ -> cosub-wk π (wk-wk ρ) φ) (wk-trans-idr π) (wk-trans-idr ρ) ⟩
  cosub-wk π (wk-wk ρ) φ                                      ≡˘⟨ cong₂ (λ π ρ -> cosub-wk π (wk-wk ρ) φ) (wk-trans-idl π) (wk-trans-idl ρ) ⟩
  cosub-wk (wk-trans wk-id π) (wk-wk (wk-trans wk-id ρ)) φ    ≡˘⟨ cosub-wk-trans wk-id (wk-wk wk-id) π ρ φ ⟩
  cosub-wk wk-id (wk-wk wk-id) (cosub-wk π ρ φ)               ∎

sub-wk-wk-shift : (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) (θ : Sub Γ Δ Ψ)
                 -> sub-wk (wk-wk {A = Y} π) ρ θ ≡ sub-wk (wk-wk {A = Y} wk-id) wk-id (sub-wk π ρ θ)
sub-wk-wk-shift π ρ θ = begin
  sub-wk (wk-wk π) ρ θ                                    ≡˘⟨ cong₂ (λ x y -> sub-wk (wk-wk x) y θ) (wk-trans-idl π) (wk-trans-idl ρ) ⟩
  sub-wk (wk-wk (wk-trans wk-id π)) (wk-trans wk-id ρ) θ  ≡˘⟨ sub-wk-trans (wk-wk wk-id) wk-id π ρ θ ⟩
  sub-wk (wk-wk wk-id) wk-id (sub-wk π ρ θ)               ∎

cosub-wk-wk-shift : (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) (φ : CoSub Γ Δ Ψ)
                   -> cosub-wk π (wk-wk {A = Y} ρ) φ ≡ cosub-wk wk-id (wk-wk {A = Y} wk-id) (cosub-wk π ρ φ)
cosub-wk-wk-shift π ρ φ = begin
  cosub-wk π (wk-wk ρ) φ                                    ≡˘⟨ cong₂ (λ x y -> cosub-wk x (wk-wk y) φ) (wk-trans-idl π) (wk-trans-idl ρ) ⟩
  cosub-wk (wk-trans wk-id π) (wk-wk (wk-trans wk-id ρ)) φ  ≡˘⟨ cosub-wk-trans wk-id (wk-wk wk-id) π ρ φ ⟩
  cosub-wk wk-id (wk-wk wk-id) (cosub-wk π ρ φ)             ∎

sub-mem-id : (i : Γ ∋ X) -> sub-mem (sub-id {Γ} {Δ}) i ≡ var i
sub-mem-id here     = refl
sub-mem-id (there i) = begin
  sub-mem (sub-wk (wk-wk wk-id) wk-id sub-id) i       ≡⟨ sub-mem-wk (wk-wk wk-id) wk-id sub-id i ⟩
  wk-val (wk-wk wk-id) wk-id (sub-mem sub-id i)       ≡⟨ cong (wk-val (wk-wk wk-id) wk-id) (sub-mem-id i) ⟩
  wk-val (wk-wk wk-id) wk-id (var i)                  ≡⟨⟩
  var (wk-mem (wk-wk wk-id) i)                        ≡⟨ cong var (wk-mem-wk-wk wk-id i) ⟩
  var (there (wk-mem wk-id i))                            ≡⟨ cong (λ j -> var (there j)) wk-mem-id ⟩
  var (there i)                                           ∎

cosub-mem-id : (i : Δ ∋ X) -> cosub-mem (cosub-id {Γ} {Δ}) i ≡ covar i
cosub-mem-id here     = refl
cosub-mem-id (there i) = begin
  cosub-mem (cosub-wk wk-id (wk-wk wk-id) cosub-id) i       ≡⟨ cosub-mem-wk wk-id (wk-wk wk-id) cosub-id i ⟩
  wk-cotm wk-id (wk-wk wk-id) (cosub-mem cosub-id i)         ≡⟨ cong (wk-cotm wk-id (wk-wk wk-id)) (cosub-mem-id i) ⟩
  wk-cotm wk-id (wk-wk wk-id) (covar i)                      ≡⟨⟩
  covar (wk-mem (wk-wk wk-id) i)                            ≡⟨ cong covar (wk-mem-wk-wk wk-id i) ⟩
  covar (there (wk-mem wk-id i))                                ≡⟨ cong (λ j -> covar (there j)) wk-mem-id ⟩
  covar (there i)                                               ∎

sub-id-Δ-wk-gen : (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) -> sub-wk π ρ (sub-id {Γ} {Δ}) ≡ sub-wk π wk-id (sub-id {Γ} {Δ₁})
sub-id-Δ-wk-gen wk-ε ρ = refl
sub-id-Δ-wk-gen (wk-cong π) ρ =
  cong₂ sub-ex
    (begin
      sub-wk (wk-cong π) ρ (sub-wk (wk-wk wk-id) wk-id sub-id)  ≡⟨ sub-wk-cong-lemma π ρ sub-id ⟩
      sub-wk (wk-wk wk-id) wk-id (sub-wk π ρ sub-id)            ≡⟨ cong (sub-wk (wk-wk wk-id) wk-id) (sub-id-Δ-wk-gen π ρ) ⟩
      sub-wk (wk-wk wk-id) wk-id (sub-wk π wk-id sub-id)        ≡˘⟨ sub-wk-cong-lemma π wk-id sub-id ⟩
      sub-wk (wk-cong π) wk-id (sub-wk (wk-wk wk-id) wk-id sub-id)  ∎)
    refl
sub-id-Δ-wk-gen (wk-wk π) ρ = begin
  sub-wk (wk-wk π) ρ sub-id                            ≡⟨ sub-wk-wk-shift π ρ sub-id ⟩
  sub-wk (wk-wk wk-id) wk-id (sub-wk π ρ sub-id)        ≡⟨ cong (sub-wk (wk-wk wk-id) wk-id) (sub-id-Δ-wk-gen π ρ) ⟩
  sub-wk (wk-wk wk-id) wk-id (sub-wk π wk-id sub-id)    ≡˘⟨ sub-wk-wk-shift π wk-id sub-id ⟩
  sub-wk (wk-wk π) wk-id sub-id                         ∎

sub-id-Δ-wk : (ρ : Δ₁ ⊇ Δ) -> sub-wk wk-id ρ (sub-id {Γ} {Δ}) ≡ sub-id {Γ} {Δ₁}
sub-id-Δ-wk ρ = begin
  sub-wk wk-id ρ sub-id  ≡⟨ sub-id-Δ-wk-gen wk-id ρ ⟩
  sub-wk wk-id wk-id sub-id  ≡⟨ sub-wk-id sub-id ⟩
  sub-id                 ∎

cosub-id-Γ-wk-gen : (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) -> cosub-wk π ρ (cosub-id {Γ} {Δ}) ≡ cosub-wk wk-id ρ (cosub-id {Γ₁} {Δ})
cosub-id-Γ-wk-gen π wk-ε = refl
cosub-id-Γ-wk-gen π (wk-cong ρ) =
  cong₂ cosub-ex
    (begin
      cosub-wk π (wk-cong ρ) (cosub-wk wk-id (wk-wk wk-id) cosub-id)  ≡⟨ cosub-wk-cong-lemma-Δ π ρ cosub-id ⟩
      cosub-wk wk-id (wk-wk wk-id) (cosub-wk π ρ cosub-id)            ≡⟨ cong (cosub-wk wk-id (wk-wk wk-id)) (cosub-id-Γ-wk-gen π ρ) ⟩
      cosub-wk wk-id (wk-wk wk-id) (cosub-wk wk-id ρ cosub-id)        ≡˘⟨ cosub-wk-cong-lemma-Δ wk-id ρ cosub-id ⟩
      cosub-wk wk-id (wk-cong ρ) (cosub-wk wk-id (wk-wk wk-id) cosub-id)  ∎)
    refl
cosub-id-Γ-wk-gen π (wk-wk ρ) = begin
  cosub-wk π (wk-wk ρ) cosub-id                          ≡⟨ cosub-wk-wk-shift π ρ cosub-id ⟩
  cosub-wk wk-id (wk-wk wk-id) (cosub-wk π ρ cosub-id)   ≡⟨ cong (cosub-wk wk-id (wk-wk wk-id)) (cosub-id-Γ-wk-gen π ρ) ⟩
  cosub-wk wk-id (wk-wk wk-id) (cosub-wk wk-id ρ cosub-id)  ≡˘⟨ cosub-wk-wk-shift wk-id ρ cosub-id ⟩
  cosub-wk wk-id (wk-wk ρ) cosub-id                      ∎

cosub-id-Γ-wk : (π : Γ₁ ⊇ Γ) -> cosub-wk π wk-id (cosub-id {Γ} {Δ}) ≡ cosub-id {Γ₁} {Δ}
cosub-id-Γ-wk π = begin
  cosub-wk π wk-id cosub-id  ≡⟨ cosub-id-Γ-wk-gen π wk-id ⟩
  cosub-wk wk-id wk-id cosub-id  ≡⟨ cosub-wk-id cosub-id ⟩
  cosub-id                    ∎

--------------------------------------------------------------------------
-- identity substitution

mutual
  sub-cmd-id : (C : Γ ⊢ Δ) -> sub-cmd sub-id cosub-id C ≡ C
  sub-cmd-id (cut X M K) = cong₂ (cut X) (sub-tm-id M) (sub-cotm-id K)

  sub-val-id : (V : Γ ⊢ᵛ X ∣ Δ) -> sub-val sub-id cosub-id V ≡ V
  sub-val-id (var i)    = sub-mem-id i
  sub-val-id (lam M)    = cong lam (begin
    sub-tm sub-id (cosub-wk (wk-wk wk-id) wk-id cosub-id) M  ≡⟨ cong (λ x -> sub-tm sub-id x M) (cosub-id-Γ-wk (wk-wk wk-id)) ⟩
    sub-tm sub-id cosub-id M                                 ≡⟨ sub-tm-id M ⟩
    M                                                         ∎)
  sub-val-id unit       = refl
  sub-val-id (pair V W) = cong₂ pair (sub-val-id V) (sub-val-id W)
  sub-val-id (inl V)    = cong inl (sub-val-id V)
  sub-val-id (inr W)    = cong inr (sub-val-id W)

  sub-tm-id : (M : Γ ⊢ᵗ X ∣ Δ) -> sub-tm sub-id cosub-id M ≡ M
  sub-tm-id (ret V) = cong ret (sub-val-id V)
  sub-tm-id (μ C)   = cong μ (begin
    sub-cmd (sub-wk wk-id (wk-wk wk-id) sub-id) cosub-id C  ≡⟨ cong (λ x -> sub-cmd x cosub-id C) (sub-id-Δ-wk (wk-wk wk-id)) ⟩
    sub-cmd sub-id cosub-id C                               ≡⟨ sub-cmd-id C ⟩
    C                                                        ∎)

  sub-cotm-id : (K : Γ ∣ X ⊢ᵏ Δ) -> sub-cotm sub-id cosub-id K ≡ K
  sub-cotm-id (covar i)  = cosub-mem-id i
  sub-cotm-id (app V K)  = cong₂ app (sub-val-id V) (sub-cotm-id K)
  sub-cotm-id (fst K)    = cong fst (sub-cotm-id K)
  sub-cotm-id (snd K)    = cong snd (sub-cotm-id K)
  sub-cotm-id (case K L) = cong₂ case (sub-cotm-id K) (sub-cotm-id L)
  sub-cotm-id (μ̃ C)        = cong μ̃ (begin
    sub-cmd sub-id (cosub-wk (wk-wk wk-id) wk-id cosub-id) C  ≡⟨ cong (λ x -> sub-cmd sub-id x C) (cosub-id-Γ-wk (wk-wk wk-id)) ⟩
    sub-cmd sub-id cosub-id C                                 ≡⟨ sub-cmd-id C ⟩
    C                                                          ∎)
  sub-cotm-id tp           = refl

--------------------------------------------------------------------------
-- weakening commutes with substitution

mutual
  wk-sub-cmd : (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) (θ : Sub Γ Δ Ψ) (φ : CoSub Γ Δ Ψ₁) (C : Ψ ⊢ Ψ₁)
             -> wk-cmd π ρ (sub-cmd θ φ C) ≡ sub-cmd (sub-wk π ρ θ) (cosub-wk π ρ φ) C
  wk-sub-cmd π ρ θ φ (cut X M K) = cong₂ (cut X) (wk-sub-tm π ρ θ φ M) (wk-sub-cotm π ρ θ φ K)

  wk-sub-val : (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) (θ : Sub Γ Δ Ψ) (φ : CoSub Γ Δ Ψ₁) (V : Ψ ⊢ᵛ X ∣ Ψ₁)
             -> wk-val π ρ (sub-val θ φ V) ≡ sub-val (sub-wk π ρ θ) (cosub-wk π ρ φ) V
  wk-sub-val π ρ θ φ (var i) = sym (sub-mem-wk π ρ θ i)
  wk-sub-val π ρ θ φ (lam M) =
    cong lam (begin
      wk-tm (wk-cong π) ρ (sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M)
        ≡⟨ wk-sub-tm (wk-cong π) ρ (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M ⟩
      sub-tm (sub-ex (sub-wk (wk-cong π) ρ (sub-wk (wk-wk wk-id) wk-id θ)) (var here)) (cosub-wk (wk-cong π) ρ (cosub-wk (wk-wk wk-id) wk-id φ)) M
        ≡⟨ cong₂ (λ x y -> sub-tm (sub-ex x (var here)) y M) (sub-wk-cong-lemma π ρ θ) (cosub-wk-cong-lemma π ρ φ) ⟩
      sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-wk π ρ θ)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-wk π ρ φ)) M  ∎)
  wk-sub-val π ρ θ φ unit       = refl
  wk-sub-val π ρ θ φ (pair V W) = cong₂ pair (wk-sub-val π ρ θ φ V) (wk-sub-val π ρ θ φ W)
  wk-sub-val π ρ θ φ (inl V)    = cong inl (wk-sub-val π ρ θ φ V)
  wk-sub-val π ρ θ φ (inr W)    = cong inr (wk-sub-val π ρ θ φ W)

  wk-sub-tm : (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) (θ : Sub Γ Δ Ψ) (φ : CoSub Γ Δ Ψ₁) (M : Ψ ⊢ᵗ X ∣ Ψ₁)
            -> wk-tm π ρ (sub-tm θ φ M) ≡ sub-tm (sub-wk π ρ θ) (cosub-wk π ρ φ) M
  wk-sub-tm π ρ θ φ (ret V) = cong ret (wk-sub-val π ρ θ φ V)
  wk-sub-tm π ρ θ φ (μ C) =
    cong μ (begin
      wk-cmd π (wk-cong ρ) (sub-cmd (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) C)
        ≡⟨ wk-sub-cmd π (wk-cong ρ) (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) C ⟩
      sub-cmd (sub-wk π (wk-cong ρ) (sub-wk wk-id (wk-wk wk-id) θ)) (cosub-ex (cosub-wk π (wk-cong ρ) (cosub-wk wk-id (wk-wk wk-id) φ)) (covar here)) C
        ≡⟨ cong₂ (λ x y -> sub-cmd x (cosub-ex y (covar here)) C) (sub-wk-cong-lemma-Δ π ρ θ) (cosub-wk-cong-lemma-Δ π ρ φ) ⟩
      sub-cmd (sub-wk wk-id (wk-wk wk-id) (sub-wk π ρ θ)) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) (cosub-wk π ρ φ)) (covar here)) C  ∎)

  wk-sub-cotm : (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) (θ : Sub Γ Δ Ψ) (φ : CoSub Γ Δ Ψ₁) (K : Ψ ∣ X ⊢ᵏ Ψ₁)
             -> wk-cotm π ρ (sub-cotm θ φ K) ≡ sub-cotm (sub-wk π ρ θ) (cosub-wk π ρ φ) K
  wk-sub-cotm π ρ θ φ (covar i)  = sym (cosub-mem-wk π ρ φ i)
  wk-sub-cotm π ρ θ φ (app V K)  = cong₂ app (wk-sub-val π ρ θ φ V) (wk-sub-cotm π ρ θ φ K)
  wk-sub-cotm π ρ θ φ (fst K)    = cong fst (wk-sub-cotm π ρ θ φ K)
  wk-sub-cotm π ρ θ φ (snd K)    = cong snd (wk-sub-cotm π ρ θ φ K)
  wk-sub-cotm π ρ θ φ (case K L) = cong₂ case (wk-sub-cotm π ρ θ φ K) (wk-sub-cotm π ρ θ φ L)
  wk-sub-cotm π ρ θ φ (μ̃ C) =
    cong μ̃ (begin
      wk-cmd (wk-cong π) ρ (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) C)
        ≡⟨ wk-sub-cmd (wk-cong π) ρ (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) C ⟩
      sub-cmd (sub-ex (sub-wk (wk-cong π) ρ (sub-wk (wk-wk wk-id) wk-id θ)) (var here)) (cosub-wk (wk-cong π) ρ (cosub-wk (wk-wk wk-id) wk-id φ)) C
        ≡⟨ cong₂ (λ x y -> sub-cmd (sub-ex x (var here)) y C) (sub-wk-cong-lemma π ρ θ) (cosub-wk-cong-lemma π ρ φ) ⟩
      sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-wk π ρ θ)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-wk π ρ φ)) C  ∎)
  wk-sub-cotm π ρ θ φ tp = refl

--------------------------------------------------------------------------
-- substitution precomposed with weakening

sub-pre : Sub Γ Δ Γ₁ -> Γ₁ ⊇ Ψ -> Sub Γ Δ Ψ
sub-pre θ wk-ε              = sub-ε
sub-pre (sub-ex θ V) (wk-cong π) = sub-ex (sub-pre θ π) V
sub-pre (sub-ex θ V) (wk-wk π)   = sub-pre θ π

cosub-pre : CoSub Γ Δ Δ₁ -> Δ₁ ⊇ Ψ -> CoSub Γ Δ Ψ
cosub-pre φ wk-ε                 = cosub-ε
cosub-pre (cosub-ex φ K) (wk-cong π) = cosub-ex (cosub-pre φ π) K
cosub-pre (cosub-ex φ K) (wk-wk π)   = cosub-pre φ π

sub-mem-pre : (θ : Sub Γ Δ Γ₁) (π : Γ₁ ⊇ Ψ) (i : Ψ ∋ X) -> sub-mem (sub-pre θ π) i ≡ sub-mem θ (wk-mem π i)
sub-mem-pre (sub-ex θ V) (wk-cong π) here     = refl
sub-mem-pre (sub-ex θ V) (wk-cong π) (there i) = sub-mem-pre θ π i
sub-mem-pre (sub-ex θ V) (wk-wk π) i = begin
  sub-mem (sub-pre θ π) i               ≡⟨ sub-mem-pre θ π i ⟩
  sub-mem θ (wk-mem π i)                ≡˘⟨ cong (λ j -> sub-mem (sub-ex θ V) j) (wk-mem-wk-wk π i) ⟩
  sub-mem (sub-ex θ V) (wk-mem (wk-wk π) i)  ∎

cosub-mem-pre : (φ : CoSub Γ Δ Δ₁) (ρ : Δ₁ ⊇ Ψ) (i : Ψ ∋ X) -> cosub-mem (cosub-pre φ ρ) i ≡ cosub-mem φ (wk-mem ρ i)
cosub-mem-pre (cosub-ex φ K) (wk-cong ρ) here     = refl
cosub-mem-pre (cosub-ex φ K) (wk-cong ρ) (there i) = cosub-mem-pre φ ρ i
cosub-mem-pre (cosub-ex φ K) (wk-wk ρ) i = begin
  cosub-mem (cosub-pre φ ρ) i               ≡⟨ cosub-mem-pre φ ρ i ⟩
  cosub-mem φ (wk-mem ρ i)                  ≡˘⟨ cong (λ j -> cosub-mem (cosub-ex φ K) j) (wk-mem-wk-wk ρ i) ⟩
  cosub-mem (cosub-ex φ K) (wk-mem (wk-wk ρ) i)  ∎

sub-pre-wk-l : (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) (θ : Sub Γ Δ Γ₂) (δ : Γ₂ ⊇ Ψ) -> sub-pre (sub-wk π ρ θ) δ ≡ sub-wk π ρ (sub-pre θ δ)
sub-pre-wk-l π ρ θ wk-ε              = refl
sub-pre-wk-l π ρ (sub-ex θ V) (wk-cong δ) = cong₂ sub-ex (sub-pre-wk-l π ρ θ δ) refl
sub-pre-wk-l π ρ (sub-ex θ V) (wk-wk δ)   = sub-pre-wk-l π ρ θ δ

cosub-pre-wk-l : (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) (φ : CoSub Γ Δ Δ₂) (σ : Δ₂ ⊇ Ψ) -> cosub-pre (cosub-wk π ρ φ) σ ≡ cosub-wk π ρ (cosub-pre φ σ)
cosub-pre-wk-l π ρ φ wk-ε                  = refl
cosub-pre-wk-l π ρ (cosub-ex φ K) (wk-cong σ) = cong₂ cosub-ex (cosub-pre-wk-l π ρ φ σ) refl
cosub-pre-wk-l π ρ (cosub-ex φ K) (wk-wk σ)   = cosub-pre-wk-l π ρ φ σ

sub-pre-wk-id : (θ : Sub Γ Δ Γ₁) -> sub-pre θ (wk-id {Γ₁}) ≡ θ
sub-pre-wk-id sub-ε        = refl
sub-pre-wk-id (sub-ex θ V) = cong (λ W -> sub-ex W V) (sub-pre-wk-id θ)

cosub-pre-wk-id : (φ : CoSub Γ Δ Δ₁) -> cosub-pre φ (wk-id {Δ₁}) ≡ φ
cosub-pre-wk-id cosub-ε        = refl
cosub-pre-wk-id (cosub-ex φ K) = cong (λ W -> cosub-ex W K) (cosub-pre-wk-id φ)

--------------------------------------------------------------------------
-- substitution after weakening

mutual
  sub-val-wk-pre : (θ : Sub Ψ Ψ₁ Γ) (φ : CoSub Ψ Ψ₁ Δ) (π : Γ ⊇ Γ₁) (ρ : Δ ⊇ Δ₁) (V : Γ₁ ⊢ᵛ X ∣ Δ₁)
                 -> sub-val θ φ (wk-val π ρ V) ≡ sub-val (sub-pre θ π) (cosub-pre φ ρ) V
  sub-val-wk-pre θ φ π ρ (var i) = sym (sub-mem-pre θ π i)
  sub-val-wk-pre θ φ π ρ (lam M) =
    cong lam (begin
      sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) (wk-tm (wk-cong π) ρ M)
        ≡⟨ sub-tm-wk-pre (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) (wk-cong π) ρ M ⟩
      sub-tm (sub-ex (sub-pre (sub-wk (wk-wk wk-id) wk-id θ) π) (var here)) (cosub-pre (cosub-wk (wk-wk wk-id) wk-id φ) ρ) M
        ≡⟨ cong₂ (λ x y -> sub-tm (sub-ex x (var here)) y M) (sub-pre-wk-l (wk-wk wk-id) wk-id θ π) (cosub-pre-wk-l (wk-wk wk-id) wk-id φ ρ) ⟩
      sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-pre θ π)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-pre φ ρ)) M  ∎)
  sub-val-wk-pre θ φ π ρ unit       = refl
  sub-val-wk-pre θ φ π ρ (pair V W) = cong₂ pair (sub-val-wk-pre θ φ π ρ V) (sub-val-wk-pre θ φ π ρ W)
  sub-val-wk-pre θ φ π ρ (inl V)    = cong inl (sub-val-wk-pre θ φ π ρ V)
  sub-val-wk-pre θ φ π ρ (inr W)    = cong inr (sub-val-wk-pre θ φ π ρ W)

  sub-tm-wk-pre : (θ : Sub Ψ Ψ₁ Γ) (φ : CoSub Ψ Ψ₁ Δ) (π : Γ ⊇ Γ₁) (ρ : Δ ⊇ Δ₁) (M : Γ₁ ⊢ᵗ X ∣ Δ₁)
                -> sub-tm θ φ (wk-tm π ρ M) ≡ sub-tm (sub-pre θ π) (cosub-pre φ ρ) M
  sub-tm-wk-pre θ φ π ρ (ret V) = cong ret (sub-val-wk-pre θ φ π ρ V)
  sub-tm-wk-pre θ φ π ρ (μ C) =
    cong μ (begin
      sub-cmd (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) (wk-cmd π (wk-cong ρ) C)
        ≡⟨ sub-cmd-wk-pre (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) π (wk-cong ρ) C ⟩
      sub-cmd (sub-pre (sub-wk wk-id (wk-wk wk-id) θ) π) (cosub-ex (cosub-pre (cosub-wk wk-id (wk-wk wk-id) φ) ρ) (covar here)) C
        ≡⟨ cong₂ (λ x y -> sub-cmd x (cosub-ex y (covar here)) C) (sub-pre-wk-l wk-id (wk-wk wk-id) θ π) (cosub-pre-wk-l wk-id (wk-wk wk-id) φ ρ) ⟩
      sub-cmd (sub-wk wk-id (wk-wk wk-id) (sub-pre θ π)) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) (cosub-pre φ ρ)) (covar here)) C  ∎)

  sub-cotm-wk-pre : (θ : Sub Ψ Ψ₁ Γ) (φ : CoSub Ψ Ψ₁ Δ) (π : Γ ⊇ Γ₁) (ρ : Δ ⊇ Δ₁) (K : Γ₁ ∣ X ⊢ᵏ Δ₁)
                 -> sub-cotm θ φ (wk-cotm π ρ K) ≡ sub-cotm (sub-pre θ π) (cosub-pre φ ρ) K
  sub-cotm-wk-pre θ φ π ρ (covar i) = sym (cosub-mem-pre φ ρ i)
  sub-cotm-wk-pre θ φ π ρ (app V K) = cong₂ app (sub-val-wk-pre θ φ π ρ V) (sub-cotm-wk-pre θ φ π ρ K)
  sub-cotm-wk-pre θ φ π ρ (fst K)   = cong fst (sub-cotm-wk-pre θ φ π ρ K)
  sub-cotm-wk-pre θ φ π ρ (snd K)   = cong snd (sub-cotm-wk-pre θ φ π ρ K)
  sub-cotm-wk-pre θ φ π ρ (case K L) = cong₂ case (sub-cotm-wk-pre θ φ π ρ K) (sub-cotm-wk-pre θ φ π ρ L)
  sub-cotm-wk-pre θ φ π ρ (μ̃ C) =
    cong μ̃ (begin
      sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) (wk-cmd (wk-cong π) ρ C)
        ≡⟨ sub-cmd-wk-pre (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) (wk-cong π) ρ C ⟩
      sub-cmd (sub-ex (sub-pre (sub-wk (wk-wk wk-id) wk-id θ) π) (var here)) (cosub-pre (cosub-wk (wk-wk wk-id) wk-id φ) ρ) C
        ≡⟨ cong₂ (λ x y -> sub-cmd (sub-ex x (var here)) y C) (sub-pre-wk-l (wk-wk wk-id) wk-id θ π) (cosub-pre-wk-l (wk-wk wk-id) wk-id φ ρ) ⟩
      sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-pre θ π)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-pre φ ρ)) C  ∎)
  sub-cotm-wk-pre θ φ π ρ tp = refl

  sub-cmd-wk-pre : (θ : Sub Ψ Ψ₁ Γ) (φ : CoSub Ψ Ψ₁ Δ) (π : Γ ⊇ Γ₁) (ρ : Δ ⊇ Δ₁) (C : Γ₁ ⊢ Δ₁)
                 -> sub-cmd θ φ (wk-cmd π ρ C) ≡ sub-cmd (sub-pre θ π) (cosub-pre φ ρ) C
  sub-cmd-wk-pre θ φ π ρ (cut X M K) = cong₂ (cut X) (sub-tm-wk-pre θ φ π ρ M) (sub-cotm-wk-pre θ φ π ρ K)

--------------------------------------------------------------------------
-- substitution composition

sub-comp-sub : Sub Γ Δ Γ₁ -> CoSub Γ Δ Δ₁ -> Sub Γ₁ Δ₁ Ψ -> Sub Γ Δ Ψ
sub-comp-sub θ φ sub-ε          = sub-ε
sub-comp-sub θ₁ φ (sub-ex θ₂ V) = sub-ex (sub-comp-sub θ₁ φ θ₂) (sub-val θ₁ φ V)

cosub-comp-sub : Sub Γ Δ Γ₁ -> CoSub Γ Δ Δ₁ -> CoSub Γ₁ Δ₁ Ψ -> CoSub Γ Δ Ψ
cosub-comp-sub θ φ cosub-ε          = cosub-ε
cosub-comp-sub θ φ₁ (cosub-ex φ₂ K) = cosub-ex (cosub-comp-sub θ φ₁ φ₂) (sub-cotm θ φ₁ K)

sub-mem-comp-sub : (θ₁ : Sub Γ Δ Γ₁) (φ : CoSub Γ Δ Δ₁) (θ₂ : Sub Γ₁ Δ₁ Ψ) (i : Ψ ∋ X)
                  -> sub-mem (sub-comp-sub θ₁ φ θ₂) i ≡ sub-val θ₁ φ (sub-mem θ₂ i)
sub-mem-comp-sub θ₁ φ (sub-ex θ₂ V) here     = refl
sub-mem-comp-sub θ₁ φ (sub-ex θ₂ V) (there i) = sub-mem-comp-sub θ₁ φ θ₂ i

cosub-mem-comp-sub : (θ : Sub Γ Δ Γ₁) (φ₁ : CoSub Γ Δ Δ₁) (φ₂ : CoSub Γ₁ Δ₁ Ψ) (i : Ψ ∋ X)
                    -> cosub-mem (cosub-comp-sub θ φ₁ φ₂) i ≡ sub-cotm θ φ₁ (cosub-mem φ₂ i)
cosub-mem-comp-sub θ φ₁ (cosub-ex φ₂ K) here     = refl
cosub-mem-comp-sub θ φ₁ (cosub-ex φ₂ K) (there i) = cosub-mem-comp-sub θ φ₁ φ₂ i

sub-comp-sub-wk-r : (θ₁ : Sub Γ Δ Γ₁) (φ : CoSub Γ Δ Δ₁) (π : Γ₁ ⊇ Γ₂) (ρ : Δ₁ ⊇ Δ₂) (θ₂ : Sub Γ₂ Δ₂ Ψ)
                   -> sub-comp-sub θ₁ φ (sub-wk π ρ θ₂) ≡ sub-comp-sub (sub-pre θ₁ π) (cosub-pre φ ρ) θ₂
sub-comp-sub-wk-r θ φ π ρ sub-ε          = refl
sub-comp-sub-wk-r θ₁ φ π ρ (sub-ex θ₂ V) = cong₂ sub-ex (sub-comp-sub-wk-r θ₁ φ π ρ θ₂) (sub-val-wk-pre θ₁ φ π ρ V)

cosub-comp-sub-wk-r : (θ : Sub Γ Δ Γ₁) (φ₁ : CoSub Γ Δ Δ₁) (π : Γ₁ ⊇ Γ₂) (ρ : Δ₁ ⊇ Δ₂) (φ₂ : CoSub Γ₂ Δ₂ Ψ)
                     -> cosub-comp-sub θ φ₁ (cosub-wk π ρ φ₂) ≡ cosub-comp-sub (sub-pre θ π) (cosub-pre φ₁ ρ) φ₂
cosub-comp-sub-wk-r θ φ π ρ cosub-ε          = refl
cosub-comp-sub-wk-r θ φ₁ π ρ (cosub-ex φ₂ K) = cong₂ cosub-ex (cosub-comp-sub-wk-r θ φ₁ π ρ φ₂) (sub-cotm-wk-pre θ φ₁ π ρ K)

sub-comp-sub-wk-l : (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) (θ₁ : Sub Γ Δ Γ₂) (φ : CoSub Γ Δ Δ₂) (θ₂ : Sub Γ₂ Δ₂ Ψ)
                   -> sub-comp-sub (sub-wk π ρ θ₁) (cosub-wk π ρ φ) θ₂ ≡ sub-wk π ρ (sub-comp-sub θ₁ φ θ₂)
sub-comp-sub-wk-l π ρ θ φ sub-ε         = refl
sub-comp-sub-wk-l π ρ θ₁ φ (sub-ex θ₂ V) =
  cong₂ sub-ex (sub-comp-sub-wk-l π ρ θ₁ φ θ₂) (sym (wk-sub-val π ρ θ₁ φ V))

cosub-comp-sub-wk-l : (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) (θ : Sub Γ Δ Γ₂) (φ₁ : CoSub Γ Δ Δ₂) (φ₂ : CoSub Γ₂ Δ₂ Ψ)
                     -> cosub-comp-sub (sub-wk π ρ θ) (cosub-wk π ρ φ₁) φ₂ ≡ cosub-wk π ρ (cosub-comp-sub θ φ₁ φ₂)
cosub-comp-sub-wk-l π ρ θ φ cosub-ε         = refl
cosub-comp-sub-wk-l π ρ θ φ₁ (cosub-ex φ₂ K) =
  cong₂ cosub-ex (cosub-comp-sub-wk-l π ρ θ φ₁ φ₂) (sym (wk-sub-cotm π ρ θ φ₁ K))

-- pushing a fresh-variable lift through composition, on either the Γ or Δ side
sub-comp-sub-ext-Γ : (θ₁ : Sub Γ Δ Γ₁) (φ : CoSub Γ Δ Δ₁) (θ₂ : Sub Γ₁ Δ₁ Ψ)
                   -> sub-comp-sub (sub-ex (sub-wk (wk-wk {A = X} wk-id) wk-id θ₁) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₂) (var here))
                    ≡ sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-comp-sub θ₁ φ θ₂)) (var here)
sub-comp-sub-ext-Γ θ₁ φ θ₂ =
  cong₂ sub-ex
    (begin
      sub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₁) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) (sub-wk (wk-wk wk-id) wk-id θ₂)
        ≡⟨ sub-comp-sub-wk-r (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₁) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) (wk-wk wk-id) wk-id θ₂ ⟩
      sub-comp-sub (sub-pre (sub-wk (wk-wk wk-id) wk-id θ₁) wk-id) (cosub-pre (cosub-wk (wk-wk wk-id) wk-id φ) wk-id) θ₂
        ≡⟨ cong₂ (λ x y -> sub-comp-sub x y θ₂) (sub-pre-wk-id (sub-wk (wk-wk wk-id) wk-id θ₁)) (cosub-pre-wk-id (cosub-wk (wk-wk wk-id) wk-id φ)) ⟩
      sub-comp-sub (sub-wk (wk-wk wk-id) wk-id θ₁) (cosub-wk (wk-wk wk-id) wk-id φ) θ₂
        ≡⟨ sub-comp-sub-wk-l (wk-wk wk-id) wk-id θ₁ φ θ₂ ⟩
      sub-wk (wk-wk wk-id) wk-id (sub-comp-sub θ₁ φ θ₂)  ∎)
    refl

cosub-comp-sub-ext-Γ : (θ : Sub Γ Δ Γ₁) (φ₁ : CoSub Γ Δ Δ₁) (φ₂ : CoSub Γ₁ Δ₁ Ψ)
                      -> cosub-comp-sub (sub-ex (sub-wk (wk-wk {A = X} wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₁) (cosub-wk (wk-wk wk-id) wk-id φ₂)
                       ≡ cosub-wk (wk-wk wk-id) wk-id (cosub-comp-sub θ φ₁ φ₂)
cosub-comp-sub-ext-Γ θ φ₁ φ₂ = begin
  cosub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₁) (cosub-wk (wk-wk wk-id) wk-id φ₂)
    ≡⟨ cosub-comp-sub-wk-r (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₁) (wk-wk wk-id) wk-id φ₂ ⟩
  cosub-comp-sub (sub-pre (sub-wk (wk-wk wk-id) wk-id θ) wk-id) (cosub-pre (cosub-wk (wk-wk wk-id) wk-id φ₁) wk-id) φ₂
    ≡⟨ cong₂ (λ x y -> cosub-comp-sub x y φ₂) (sub-pre-wk-id (sub-wk (wk-wk wk-id) wk-id θ)) (cosub-pre-wk-id (cosub-wk (wk-wk wk-id) wk-id φ₁)) ⟩
  cosub-comp-sub (sub-wk (wk-wk wk-id) wk-id θ) (cosub-wk (wk-wk wk-id) wk-id φ₁) φ₂
    ≡⟨ cosub-comp-sub-wk-l (wk-wk wk-id) wk-id θ φ₁ φ₂ ⟩
  cosub-wk (wk-wk wk-id) wk-id (cosub-comp-sub θ φ₁ φ₂)  ∎

sub-comp-sub-ext-Δ : (θ₁ : Sub Γ Δ Γ₁) (φ : CoSub Γ Δ Δ₁) (θ₂ : Sub Γ₁ Δ₁ Ψ)
                   -> sub-comp-sub (sub-wk wk-id (wk-wk {A = X} wk-id) θ₁) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) (sub-wk wk-id (wk-wk wk-id) θ₂)
                    ≡ sub-wk wk-id (wk-wk wk-id) (sub-comp-sub θ₁ φ θ₂)
sub-comp-sub-ext-Δ θ₁ φ θ₂ = begin
  sub-comp-sub (sub-wk wk-id (wk-wk wk-id) θ₁) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) (sub-wk wk-id (wk-wk wk-id) θ₂)
    ≡⟨ sub-comp-sub-wk-r (sub-wk wk-id (wk-wk wk-id) θ₁) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) wk-id (wk-wk wk-id) θ₂ ⟩
  sub-comp-sub (sub-pre (sub-wk wk-id (wk-wk wk-id) θ₁) wk-id) (cosub-pre (cosub-wk wk-id (wk-wk wk-id) φ) wk-id) θ₂
    ≡⟨ cong₂ (λ x y -> sub-comp-sub x y θ₂) (sub-pre-wk-id (sub-wk wk-id (wk-wk wk-id) θ₁)) (cosub-pre-wk-id (cosub-wk wk-id (wk-wk wk-id) φ)) ⟩
  sub-comp-sub (sub-wk wk-id (wk-wk wk-id) θ₁) (cosub-wk wk-id (wk-wk wk-id) φ) θ₂
    ≡⟨ sub-comp-sub-wk-l wk-id (wk-wk wk-id) θ₁ φ θ₂ ⟩
  sub-wk wk-id (wk-wk wk-id) (sub-comp-sub θ₁ φ θ₂)  ∎

cosub-comp-sub-ext-Δ : (θ : Sub Γ Δ Γ₁) (φ₁ : CoSub Γ Δ Δ₁) (φ₂ : CoSub Γ₁ Δ₁ Ψ)
                      -> cosub-comp-sub (sub-wk wk-id (wk-wk {A = X} wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ₁) (covar here)) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ₂) (covar here))
                       ≡ cosub-ex (cosub-wk wk-id (wk-wk wk-id) (cosub-comp-sub θ φ₁ φ₂)) (covar here)
cosub-comp-sub-ext-Δ θ φ₁ φ₂ =
  cong₂ cosub-ex
    (begin
      cosub-comp-sub (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ₁) (covar here)) (cosub-wk wk-id (wk-wk wk-id) φ₂)
        ≡⟨ cosub-comp-sub-wk-r (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ₁) (covar here)) wk-id (wk-wk wk-id) φ₂ ⟩
      cosub-comp-sub (sub-pre (sub-wk wk-id (wk-wk wk-id) θ) wk-id) (cosub-pre (cosub-wk wk-id (wk-wk wk-id) φ₁) wk-id) φ₂
        ≡⟨ cong₂ (λ x y -> cosub-comp-sub x y φ₂) (sub-pre-wk-id (sub-wk wk-id (wk-wk wk-id) θ)) (cosub-pre-wk-id (cosub-wk wk-id (wk-wk wk-id) φ₁)) ⟩
      cosub-comp-sub (sub-wk wk-id (wk-wk wk-id) θ) (cosub-wk wk-id (wk-wk wk-id) φ₁) φ₂
        ≡⟨ cosub-comp-sub-wk-l wk-id (wk-wk wk-id) θ φ₁ φ₂ ⟩
      cosub-wk wk-id (wk-wk wk-id) (cosub-comp-sub θ φ₁ φ₂)  ∎)
    refl

mutual
  sub-sub-cmd : (θ₁ : Sub Γ Δ Γ₁) (φ₁ : CoSub Γ Δ Δ₁) (θ₂ : Sub Γ₁ Δ₁ Ψ) (φ₂ : CoSub Γ₁ Δ₁ Ψ₁) (C : Ψ ⊢ Ψ₁)
              -> sub-cmd θ₁ φ₁ (sub-cmd θ₂ φ₂ C) ≡ sub-cmd (sub-comp-sub θ₁ φ₁ θ₂) (cosub-comp-sub θ₁ φ₁ φ₂) C
  sub-sub-cmd θ₁ φ₁ θ₂ φ₂ (cut X M K) = cong₂ (cut X) (sub-sub-tm θ₁ φ₁ θ₂ φ₂ M) (sub-sub-cotm θ₁ φ₁ θ₂ φ₂ K)

  sub-sub-val : (θ₁ : Sub Γ Δ Γ₁) (φ₁ : CoSub Γ Δ Δ₁) (θ₂ : Sub Γ₁ Δ₁ Ψ) (φ₂ : CoSub Γ₁ Δ₁ Ψ₁) (V : Ψ ⊢ᵛ X ∣ Ψ₁)
              -> sub-val θ₁ φ₁ (sub-val θ₂ φ₂ V) ≡ sub-val (sub-comp-sub θ₁ φ₁ θ₂) (cosub-comp-sub θ₁ φ₁ φ₂) V
  sub-sub-val θ₁ φ₁ θ₂ φ₂ (var i) = sym (sub-mem-comp-sub θ₁ φ₁ θ₂ i)
  sub-sub-val θ₁ φ₁ θ₂ φ₂ (lam M) =
    cong lam (begin
      sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₁) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₁)
              (sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₂) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₂) M)
        ≡⟨ sub-sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₁) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₁)
                      (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₂) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₂) M ⟩
      sub-tm (sub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₁) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₁) (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₂) (var here)))
             (cosub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₁) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₁) (cosub-wk (wk-wk wk-id) wk-id φ₂)) M
        ≡⟨ cong₂ (λ x y -> sub-tm x y M) (sub-comp-sub-ext-Γ θ₁ φ₁ θ₂) (cosub-comp-sub-ext-Γ θ₁ φ₁ φ₂) ⟩
      sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-comp-sub θ₁ φ₁ θ₂)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-comp-sub θ₁ φ₁ φ₂)) M  ∎)
  sub-sub-val θ₁ φ₁ θ₂ φ₂ unit       = refl
  sub-sub-val θ₁ φ₁ θ₂ φ₂ (pair V W) = cong₂ pair (sub-sub-val θ₁ φ₁ θ₂ φ₂ V) (sub-sub-val θ₁ φ₁ θ₂ φ₂ W)
  sub-sub-val θ₁ φ₁ θ₂ φ₂ (inl V)    = cong inl (sub-sub-val θ₁ φ₁ θ₂ φ₂ V)
  sub-sub-val θ₁ φ₁ θ₂ φ₂ (inr W)    = cong inr (sub-sub-val θ₁ φ₁ θ₂ φ₂ W)

  sub-sub-tm : (θ₁ : Sub Γ Δ Γ₁) (φ₁ : CoSub Γ Δ Δ₁) (θ₂ : Sub Γ₁ Δ₁ Ψ) (φ₂ : CoSub Γ₁ Δ₁ Ψ₁) (M : Ψ ⊢ᵗ X ∣ Ψ₁)
             -> sub-tm θ₁ φ₁ (sub-tm θ₂ φ₂ M) ≡ sub-tm (sub-comp-sub θ₁ φ₁ θ₂) (cosub-comp-sub θ₁ φ₁ φ₂) M
  sub-sub-tm θ₁ φ₁ θ₂ φ₂ (ret V) = cong ret (sub-sub-val θ₁ φ₁ θ₂ φ₂ V)
  sub-sub-tm θ₁ φ₁ θ₂ φ₂ (μ C) =
    cong μ (begin
      sub-cmd (sub-wk wk-id (wk-wk wk-id) θ₁) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ₁) (covar here))
              (sub-cmd (sub-wk wk-id (wk-wk wk-id) θ₂) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ₂) (covar here)) C)
        ≡⟨ sub-sub-cmd (sub-wk wk-id (wk-wk wk-id) θ₁) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ₁) (covar here))
                       (sub-wk wk-id (wk-wk wk-id) θ₂) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ₂) (covar here)) C ⟩
      sub-cmd (sub-comp-sub (sub-wk wk-id (wk-wk wk-id) θ₁) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ₁) (covar here)) (sub-wk wk-id (wk-wk wk-id) θ₂))
              (cosub-comp-sub (sub-wk wk-id (wk-wk wk-id) θ₁) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ₁) (covar here)) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ₂) (covar here))) C
        ≡⟨ cong₂ (λ x y -> sub-cmd x y C) (sub-comp-sub-ext-Δ θ₁ φ₁ θ₂) (cosub-comp-sub-ext-Δ θ₁ φ₁ φ₂) ⟩
      sub-cmd (sub-wk wk-id (wk-wk wk-id) (sub-comp-sub θ₁ φ₁ θ₂)) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) (cosub-comp-sub θ₁ φ₁ φ₂)) (covar here)) C  ∎)

  sub-sub-cotm : (θ₁ : Sub Γ Δ Γ₁) (φ₁ : CoSub Γ Δ Δ₁) (θ₂ : Sub Γ₁ Δ₁ Ψ) (φ₂ : CoSub Γ₁ Δ₁ Ψ₁) (K : Ψ ∣ X ⊢ᵏ Ψ₁)
              -> sub-cotm θ₁ φ₁ (sub-cotm θ₂ φ₂ K) ≡ sub-cotm (sub-comp-sub θ₁ φ₁ θ₂) (cosub-comp-sub θ₁ φ₁ φ₂) K
  sub-sub-cotm θ₁ φ₁ θ₂ φ₂ (covar i)  = sym (cosub-mem-comp-sub θ₁ φ₁ φ₂ i)
  sub-sub-cotm θ₁ φ₁ θ₂ φ₂ (app V K)  = cong₂ app (sub-sub-val θ₁ φ₁ θ₂ φ₂ V) (sub-sub-cotm θ₁ φ₁ θ₂ φ₂ K)
  sub-sub-cotm θ₁ φ₁ θ₂ φ₂ (fst K)    = cong fst (sub-sub-cotm θ₁ φ₁ θ₂ φ₂ K)
  sub-sub-cotm θ₁ φ₁ θ₂ φ₂ (snd K)    = cong snd (sub-sub-cotm θ₁ φ₁ θ₂ φ₂ K)
  sub-sub-cotm θ₁ φ₁ θ₂ φ₂ (case K L) = cong₂ case (sub-sub-cotm θ₁ φ₁ θ₂ φ₂ K) (sub-sub-cotm θ₁ φ₁ θ₂ φ₂ L)
  sub-sub-cotm θ₁ φ₁ θ₂ φ₂ (μ̃ C) =
    cong μ̃ (begin
      sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₁) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₁)
              (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₂) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₂) C)
        ≡⟨ sub-sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₁) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₁)
                       (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₂) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₂) C ⟩
      sub-cmd (sub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₁) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₁) (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₂) (var here)))
              (cosub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) wk-id θ₁) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ₁) (cosub-wk (wk-wk wk-id) wk-id φ₂)) C
        ≡⟨ cong₂ (λ x y -> sub-cmd x y C) (sub-comp-sub-ext-Γ θ₁ φ₁ θ₂) (cosub-comp-sub-ext-Γ θ₁ φ₁ φ₂) ⟩
      sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-comp-sub θ₁ φ₁ θ₂)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-comp-sub θ₁ φ₁ φ₂)) C  ∎)
  sub-sub-cotm θ₁ φ₁ θ₂ φ₂ tp = refl

sub-comp-sub-idl : (θ : Sub Γ Δ Γ₁) -> sub-comp-sub (sub-id {Γ} {Δ}) (cosub-id {Γ} {Δ}) θ ≡ θ
sub-comp-sub-idl sub-ε        = refl
sub-comp-sub-idl (sub-ex θ V) = cong₂ sub-ex (sub-comp-sub-idl θ) (sub-val-id V)

cosub-comp-sub-idl : (φ : CoSub Γ Δ Δ₁) -> cosub-comp-sub (sub-id {Γ} {Δ}) (cosub-id {Γ} {Δ}) φ ≡ φ
cosub-comp-sub-idl cosub-ε        = refl
cosub-comp-sub-idl (cosub-ex φ K) = cong₂ cosub-ex (cosub-comp-sub-idl φ) (sub-cotm-id K)

--------------------------------------------------------------------------
-- lemmas for fundamental lemma

fund-lam-eq : (θ : Sub Γ Δ Γ₂) (φ : CoSub Γ Δ Δ₂) (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) (W : Γ₁ ⊢ᵛ X ∣ Δ₁) (M : (Γ₂ ∙ X) ⊢ᵗ Y ∣ Δ₂)
  -> sub-tm (sub-ex sub-id W) cosub-id (wk-tm (wk-cong π) ρ (sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M))
   ≡ sub-tm (sub-ex (sub-wk π ρ θ) W) (cosub-wk π ρ φ) M
fund-lam-eq θ φ π ρ W M = begin
  sub-tm (sub-ex sub-id W) cosub-id (wk-tm (wk-cong π) ρ (sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M))
    ≡⟨ cong (sub-tm (sub-ex sub-id W) cosub-id) (begin
         wk-tm (wk-cong π) ρ (sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M)
           ≡⟨ wk-sub-tm (wk-cong π) ρ (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M ⟩
         sub-tm (sub-ex (sub-wk (wk-cong π) ρ (sub-wk (wk-wk wk-id) wk-id θ)) (var here)) (cosub-wk (wk-cong π) ρ (cosub-wk (wk-wk wk-id) wk-id φ)) M
           ≡⟨ cong₂ (λ x y -> sub-tm (sub-ex x (var here)) y M) (sub-wk-cong-lemma π ρ θ) (cosub-wk-cong-lemma π ρ φ) ⟩
         sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-wk π ρ θ)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-wk π ρ φ)) M  ∎) ⟩
  sub-tm (sub-ex sub-id W) cosub-id (sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-wk π ρ θ)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-wk π ρ φ)) M)
    ≡⟨ sub-sub-tm (sub-ex sub-id W) cosub-id (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-wk π ρ θ)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-wk π ρ φ)) M ⟩
  sub-tm (sub-comp-sub (sub-ex sub-id W) cosub-id (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-wk π ρ θ)) (var here)))
         (cosub-comp-sub (sub-ex sub-id W) cosub-id (cosub-wk (wk-wk wk-id) wk-id (cosub-wk π ρ φ))) M
    ≡⟨ cong₂ (λ x y -> sub-tm x y M)
             (cong₂ sub-ex
               (begin
                 sub-comp-sub (sub-ex sub-id W) cosub-id (sub-wk (wk-wk wk-id) wk-id (sub-wk π ρ θ))
                   ≡⟨ sub-comp-sub-wk-r (sub-ex sub-id W) cosub-id (wk-wk wk-id) wk-id (sub-wk π ρ θ) ⟩
                 sub-comp-sub (sub-pre (sub-ex sub-id W) (wk-wk wk-id)) (cosub-pre cosub-id wk-id) (sub-wk π ρ θ)
                   ≡⟨ cong₂ (λ x y -> sub-comp-sub x y (sub-wk π ρ θ)) (sub-pre-wk-id sub-id) (cosub-pre-wk-id cosub-id) ⟩
                 sub-comp-sub sub-id cosub-id (sub-wk π ρ θ)
                   ≡⟨ sub-comp-sub-idl (sub-wk π ρ θ) ⟩
                 sub-wk π ρ θ  ∎)
               refl)
             (begin
               cosub-comp-sub (sub-ex sub-id W) cosub-id (cosub-wk (wk-wk wk-id) wk-id (cosub-wk π ρ φ))
                 ≡⟨ cosub-comp-sub-wk-r (sub-ex sub-id W) cosub-id (wk-wk wk-id) wk-id (cosub-wk π ρ φ) ⟩
               cosub-comp-sub (sub-pre (sub-ex sub-id W) (wk-wk wk-id)) (cosub-pre cosub-id wk-id) (cosub-wk π ρ φ)
                 ≡⟨ cong₂ (λ x y -> cosub-comp-sub x y (cosub-wk π ρ φ)) (sub-pre-wk-id sub-id) (cosub-pre-wk-id cosub-id) ⟩
               cosub-comp-sub sub-id cosub-id (cosub-wk π ρ φ)
                 ≡⟨ cosub-comp-sub-idl (cosub-wk π ρ φ) ⟩
               cosub-wk π ρ φ  ∎) ⟩
  sub-tm (sub-ex (sub-wk π ρ θ) W) (cosub-wk π ρ φ) M  ∎

fund-mu-eq : (θ : Sub Γ Δ Γ₁) (φ : CoSub Γ Δ Δ₁) (K : Γ ∣ X ⊢ᵏ Δ) (C : Γ₁ ⊢ (Δ₁ ∙ X))
  -> sub-cmd sub-id (cosub-ex cosub-id K) (sub-cmd (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) C)
   ≡ sub-cmd θ (cosub-ex φ K) C
fund-mu-eq θ φ K C = begin
  sub-cmd sub-id (cosub-ex cosub-id K) (sub-cmd (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) C)
    ≡⟨ sub-sub-cmd sub-id (cosub-ex cosub-id K) (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) C ⟩
  sub-cmd (sub-comp-sub sub-id (cosub-ex cosub-id K) (sub-wk wk-id (wk-wk wk-id) θ))
          (cosub-comp-sub sub-id (cosub-ex cosub-id K) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here))) C
    ≡⟨ cong₂ (λ x y -> sub-cmd x y C)
             (begin
               sub-comp-sub sub-id (cosub-ex cosub-id K) (sub-wk wk-id (wk-wk wk-id) θ)
                 ≡⟨ sub-comp-sub-wk-r sub-id (cosub-ex cosub-id K) wk-id (wk-wk wk-id) θ ⟩
               sub-comp-sub (sub-pre sub-id wk-id) (cosub-pre cosub-id wk-id) θ
                 ≡⟨ cong₂ (λ x y -> sub-comp-sub x y θ) (sub-pre-wk-id sub-id) (cosub-pre-wk-id cosub-id) ⟩
               sub-comp-sub sub-id cosub-id θ
                 ≡⟨ sub-comp-sub-idl θ ⟩
               θ  ∎)
             (cong₂ cosub-ex
               (begin
                 cosub-comp-sub sub-id (cosub-ex cosub-id K) (cosub-wk wk-id (wk-wk wk-id) φ)
                   ≡⟨ cosub-comp-sub-wk-r sub-id (cosub-ex cosub-id K) wk-id (wk-wk wk-id) φ ⟩
                 cosub-comp-sub (sub-pre sub-id wk-id) (cosub-pre cosub-id wk-id) φ
                   ≡⟨ cong₂ (λ x y -> cosub-comp-sub x y φ) (sub-pre-wk-id sub-id) (cosub-pre-wk-id cosub-id) ⟩
                 cosub-comp-sub sub-id cosub-id φ
                   ≡⟨ cosub-comp-sub-idl φ ⟩
                 φ  ∎)
               refl) ⟩
  sub-cmd θ (cosub-ex φ K) C  ∎

fund-mut-eq : (θ : Sub Γ Δ Γ₁) (φ : CoSub Γ Δ Δ₁) (V : Γ ⊢ᵛ X ∣ Δ) (C : (Γ₁ ∙ X) ⊢ Δ₁)
  -> sub-cmd (sub-ex sub-id V) cosub-id (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) C)
   ≡ sub-cmd (sub-ex θ V) φ C
fund-mut-eq θ φ V C = begin
  sub-cmd (sub-ex sub-id V) cosub-id (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) C)
    ≡⟨ sub-sub-cmd (sub-ex sub-id V) cosub-id (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) C ⟩
  sub-cmd (sub-comp-sub (sub-ex sub-id V) cosub-id (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)))
          (cosub-comp-sub (sub-ex sub-id V) cosub-id (cosub-wk (wk-wk wk-id) wk-id φ)) C
    ≡⟨ cong₂ (λ x y -> sub-cmd x y C)
             (cong₂ sub-ex
               (begin
                 sub-comp-sub (sub-ex sub-id V) cosub-id (sub-wk (wk-wk wk-id) wk-id θ)
                   ≡⟨ sub-comp-sub-wk-r (sub-ex sub-id V) cosub-id (wk-wk wk-id) wk-id θ ⟩
                 sub-comp-sub (sub-pre sub-id wk-id) (cosub-pre cosub-id wk-id) θ
                   ≡⟨ cong₂ (λ x y -> sub-comp-sub x y θ) (sub-pre-wk-id sub-id) (cosub-pre-wk-id cosub-id) ⟩
                 sub-comp-sub sub-id cosub-id θ
                   ≡⟨ sub-comp-sub-idl θ ⟩
                 θ  ∎)
               refl)
             (begin
               cosub-comp-sub (sub-ex sub-id V) cosub-id (cosub-wk (wk-wk wk-id) wk-id φ)
                 ≡⟨ cosub-comp-sub-wk-r (sub-ex sub-id V) cosub-id (wk-wk wk-id) wk-id φ ⟩
               cosub-comp-sub (sub-pre sub-id wk-id) (cosub-pre cosub-id wk-id) φ
                 ≡⟨ cong₂ (λ x y -> cosub-comp-sub x y φ) (sub-pre-wk-id sub-id) (cosub-pre-wk-id cosub-id) ⟩
               cosub-comp-sub sub-id cosub-id φ
                 ≡⟨ cosub-comp-sub-idl φ ⟩
               φ  ∎) ⟩
  sub-cmd (sub-ex θ V) φ C  ∎

fund-mut-wk-eq : (θ : Sub Γ Δ Γ₂) (φ : CoSub Γ Δ Δ₂) (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) (V : Γ₁ ⊢ᵛ X ∣ Δ₁) (C : (Γ₂ ∙ X) ⊢ Δ₂)
  -> sub-cmd (sub-ex sub-id V) cosub-id (wk-cmd (wk-cong π) ρ (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) C))
   ≡ sub-cmd (sub-ex (sub-wk π ρ θ) V) (cosub-wk π ρ φ) C
fund-mut-wk-eq θ φ π ρ V C = begin
  sub-cmd (sub-ex sub-id V) cosub-id (wk-cmd (wk-cong π) ρ (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) C))
    ≡⟨ cong (sub-cmd (sub-ex sub-id V) cosub-id) (begin
         wk-cmd (wk-cong π) ρ (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) C)
           ≡⟨ wk-sub-cmd (wk-cong π) ρ (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) C ⟩
         sub-cmd (sub-ex (sub-wk (wk-cong π) ρ (sub-wk (wk-wk wk-id) wk-id θ)) (var here)) (cosub-wk (wk-cong π) ρ (cosub-wk (wk-wk wk-id) wk-id φ)) C
           ≡⟨ cong₂ (λ x y -> sub-cmd (sub-ex x (var here)) y C) (sub-wk-cong-lemma π ρ θ) (cosub-wk-cong-lemma π ρ φ) ⟩
         sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-wk π ρ θ)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-wk π ρ φ)) C  ∎) ⟩
  sub-cmd (sub-ex sub-id V) cosub-id (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-wk π ρ θ)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-wk π ρ φ)) C)
    ≡⟨ fund-mut-eq (sub-wk π ρ θ) (cosub-wk π ρ φ) V C ⟩
  sub-cmd (sub-ex (sub-wk π ρ θ) V) (cosub-wk π ρ φ) C  ∎
