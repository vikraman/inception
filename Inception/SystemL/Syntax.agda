module Inception.SystemL.Syntax where

open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym)
open Eq.≡-Reasoning

infixr 25 _`⇒_

data Ty : Set where
  `⊥ `Unit `P : Ty
  _`×_ _`⇒_ _`+_ : (A : Ty) -> (B : Ty) -> Ty

infixr 30 ¬_
¬_ : Ty -> Ty
¬ A = A `⇒ `⊥

open import Inception.Ctx Ty public

syntax Cmd Γ Δ = Γ ⊢ Δ

syntax Val Γ A Δ = Γ ⊢ᵛ A ∣ Δ

syntax Tm Γ A Δ = Γ ⊢ᵗ A ∣ Δ

syntax CoTm Γ A Δ = Γ ∣ A ⊢ᵏ Δ

data Cmd : Ctx -> Ctx -> Set

data Val : Ctx -> Ty -> Ctx -> Set

data Tm : Ctx -> Ty -> Ctx -> Set

data CoTm : Ctx -> Ty -> Ctx -> Set

data Cmd where

  cut : (A : Ty) -> (M : Γ ⊢ᵗ A ∣ Δ) -> (K : Γ ∣ A ⊢ᵏ Δ)
      ----------------------------------------------------
      -> Γ ⊢ Δ

data Val where

  var : (i : Γ ∋ A)
       ----------------
       -> Γ ⊢ᵛ A ∣ Δ

  lam : (M : (Γ ∙ A) ⊢ᵗ B ∣ Δ)
      ------------------------
      -> Γ ⊢ᵛ A `⇒ B ∣ Δ

  unit :
       -----------------
         Γ ⊢ᵛ `Unit ∣ Δ

  pair : Γ ⊢ᵛ A ∣ Δ -> Γ ⊢ᵛ B ∣ Δ
       ---------------------------
       -> Γ ⊢ᵛ A `× B ∣ Δ

  inl : Γ ⊢ᵛ A ∣ Δ
      -----------------
      -> Γ ⊢ᵛ A `+ B ∣ Δ

  inr : Γ ⊢ᵛ B ∣ Δ
      -----------------
      -> Γ ⊢ᵛ A `+ B ∣ Δ

data Tm where

  ret : (V : Γ ⊢ᵛ A ∣ Δ)
      ---------------------
      -> Γ ⊢ᵗ A ∣ Δ

  μ : (M : Γ ⊢ (Δ ∙ A))
    ------------------------
    -> Γ ⊢ᵗ A ∣ Δ

data CoTm where

  covar : (i : Δ ∋ A)
        ---------------
        -> Γ ∣ A ⊢ᵏ Δ

  app : (V : Γ ⊢ᵛ A ∣ Δ) -> (K : Γ ∣ B ⊢ᵏ Δ)
      ---------------------------------------
      -> Γ ∣ A `⇒ B ⊢ᵏ Δ

  fst : (K : Γ ∣ A ⊢ᵏ Δ)
      -------------------
      -> Γ ∣ A `× B ⊢ᵏ Δ

  snd : (K : Γ ∣ B ⊢ᵏ Δ)
      -------------------
      -> Γ ∣ A `× B ⊢ᵏ Δ

  case : (K1 : Γ ∣ A ⊢ᵏ Δ) -> (K2 : Γ ∣ B ⊢ᵏ Δ)
       -------------------------------------------
       -> Γ ∣ A `+ B ⊢ᵏ Δ

  μ̃ : (M : (Γ ∙ A) ⊢ Δ)
    ------------------------
    -> Γ ∣ A ⊢ᵏ Δ

  tp : -------------
       Γ ∣ `⊥ ⊢ᵏ Δ

mutual
  wk-cmd : Wk Γ Γ' -> Wk Δ Δ' -> Γ' ⊢ Δ' -> Γ ⊢ Δ
  wk-cmd ρ σ (cut A M K) = cut A (wk-tm ρ σ M) (wk-cotm ρ σ K)

  wk-val : Wk Γ Γ' -> Wk Δ Δ' -> Γ' ⊢ᵛ A ∣ Δ' -> Γ ⊢ᵛ A ∣ Δ
  wk-val ρ σ (var i)    = var (wk-mem ρ i)
  wk-val ρ σ (lam M)    = lam (wk-tm (wk-cong ρ) σ M)
  wk-val ρ σ unit       = unit
  wk-val ρ σ (pair V W) = pair (wk-val ρ σ V) (wk-val ρ σ W)
  wk-val ρ σ (inl V)    = inl (wk-val ρ σ V)
  wk-val ρ σ (inr W)    = inr (wk-val ρ σ W)

  wk-tm : Wk Γ Γ' -> Wk Δ Δ' -> Γ' ⊢ᵗ A ∣ Δ' -> Γ ⊢ᵗ A ∣ Δ
  wk-tm ρ σ (ret V) = ret (wk-val ρ σ V)
  wk-tm ρ σ (μ M')   = μ (wk-cmd ρ (wk-cong σ) M')

  wk-cotm : Wk Γ Γ' -> Wk Δ Δ' -> Γ' ∣ A ⊢ᵏ Δ' -> Γ ∣ A ⊢ᵏ Δ
  wk-cotm ρ σ (covar i) = covar (wk-mem σ i)
  wk-cotm ρ σ (app V K) = app (wk-val ρ σ V) (wk-cotm ρ σ K)
  wk-cotm ρ σ (fst K)   = fst (wk-cotm ρ σ K)
  wk-cotm ρ σ (snd K)   = snd (wk-cotm ρ σ K)
  wk-cotm ρ σ (case K1 K2) = case (wk-cotm ρ σ K1) (wk-cotm ρ σ K2)
  wk-cotm ρ σ (μ̃ M')     = μ̃ (wk-cmd (wk-cong ρ) σ M')
  wk-cotm ρ σ tp        = tp

wkᵛ : Γ ⊢ᵛ A ∣ Δ -> (Γ ∙ B) ⊢ᵛ A ∣ Δ
wkᵛ = wk-val (wk-wk wk-id) wk-id

wkᵗ : Γ ⊢ᵗ A ∣ Δ -> (Γ ∙ B) ⊢ᵗ A ∣ Δ
wkᵗ = wk-tm (wk-wk wk-id) wk-id

wkᵏ : Γ ∣ A ⊢ᵏ Δ -> (Γ ∙ B) ∣ A ⊢ᵏ Δ
wkᵏ = wk-cotm (wk-wk wk-id) wk-id

wk̃ᵛ : Γ ⊢ᵛ A ∣ Δ -> Γ ⊢ᵛ A ∣ (Δ ∙ B)
wk̃ᵛ = wk-val wk-id (wk-wk wk-id)

wk̃ᵗ : Γ ⊢ᵗ A ∣ Δ -> Γ ⊢ᵗ A ∣ (Δ ∙ B)
wk̃ᵗ = wk-tm wk-id (wk-wk wk-id)

wk̃ᵏ : Γ ∣ A ⊢ᵏ Δ -> Γ ∣ A ⊢ᵏ (Δ ∙ B)
wk̃ᵏ = wk-cotm wk-id (wk-wk wk-id)

data Sub (Γ Δ : Ctx) : (Γ' : Ctx) -> Set where
  sub-ε : Sub Γ Δ ε
  sub-ex : (θ : Sub Γ Δ Γ') -> (V : Γ ⊢ᵛ A ∣ Δ) -> Sub Γ Δ (Γ' ∙ A)

data CoSub (Γ Δ : Ctx) : (Δ' : Ctx) -> Set where
  cosub-ε : CoSub Γ Δ ε
  cosub-ex : (φ : CoSub Γ Δ Δ') -> (K : Γ ∣ A ⊢ᵏ Δ) -> CoSub Γ Δ (Δ' ∙ A)

sub-mem : Sub Γ Δ Γ' -> Γ' ∋ A -> Γ ⊢ᵛ A ∣ Δ
sub-mem (sub-ex θ V) here = V
sub-mem (sub-ex θ V) (there i) = sub-mem θ i

cosub-mem : CoSub Γ Δ Δ' -> Δ' ∋ A -> Γ ∣ A ⊢ᵏ Δ
cosub-mem (cosub-ex φ K) here = K
cosub-mem (cosub-ex φ K) (there i) = cosub-mem φ i

sub-wk : Wk Γ₁ Γ -> Wk Δ₁ Δ -> Sub Γ Δ Γ' -> Sub Γ₁ Δ₁ Γ'
sub-wk ρ σ sub-ε = sub-ε
sub-wk ρ σ (sub-ex θ V) = sub-ex (sub-wk ρ σ θ) (wk-val ρ σ V)

cosub-wk : Wk Γ₁ Γ -> Wk Δ₁ Δ -> CoSub Γ Δ Δ' -> CoSub Γ₁ Δ₁ Δ'
cosub-wk ρ σ cosub-ε = cosub-ε
cosub-wk ρ σ (cosub-ex φ K) = cosub-ex (cosub-wk ρ σ φ) (wk-cotm ρ σ K)

sub-id : Sub Γ Δ Γ
sub-id {Γ = ε} = sub-ε
sub-id {Γ = Γ ∙ A} = sub-ex (sub-wk (wk-wk wk-id) wk-id sub-id) (var here)

cosub-id : CoSub Γ Δ Δ
cosub-id {Δ = ε} = cosub-ε
cosub-id {Δ = Δ ∙ A} = cosub-ex (cosub-wk wk-id (wk-wk wk-id) cosub-id) (covar here)

mutual
  sub-cmd : Sub Γ Δ Γ' -> CoSub Γ Δ Δ' -> Γ' ⊢ Δ' -> Γ ⊢ Δ
  sub-cmd θ φ (cut A M K) = cut A (sub-tm θ φ M) (sub-cotm θ φ K)

  sub-val : Sub Γ Δ Γ' -> CoSub Γ Δ Δ' -> Γ' ⊢ᵛ A ∣ Δ' -> Γ ⊢ᵛ A ∣ Δ
  sub-val θ φ (var i)    = sub-mem θ i
  sub-val θ φ (lam M)    = lam (sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M)
  sub-val θ φ unit       = unit
  sub-val θ φ (pair V W) = pair (sub-val θ φ V) (sub-val θ φ W)
  sub-val θ φ (inl V)    = inl (sub-val θ φ V)
  sub-val θ φ (inr W)    = inr (sub-val θ φ W)

  sub-tm : Sub Γ Δ Γ' -> CoSub Γ Δ Δ' -> Γ' ⊢ᵗ A ∣ Δ' -> Γ ⊢ᵗ A ∣ Δ
  sub-tm θ φ (ret V) = ret (sub-val θ φ V)
  sub-tm θ φ (μ M')   = μ (sub-cmd (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) M')

  sub-cotm : Sub Γ Δ Γ' -> CoSub Γ Δ Δ' -> Γ' ∣ A ⊢ᵏ Δ' -> Γ ∣ A ⊢ᵏ Δ
  sub-cotm θ φ (covar i) = cosub-mem φ i
  sub-cotm θ φ (app V K) = app (sub-val θ φ V) (sub-cotm θ φ K)
  sub-cotm θ φ (fst K)   = fst (sub-cotm θ φ K)
  sub-cotm θ φ (snd K)   = snd (sub-cotm θ φ K)
  sub-cotm θ φ (case K1 K2) = case (sub-cotm θ φ K1) (sub-cotm θ φ K2)
  sub-cotm θ φ (μ̃ M')     = μ̃ (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M')
  sub-cotm θ φ tp        = tp

-- syntactic sugar

letv : Γ ⊢ᵛ A ∣ Δ -> (Γ ∙ A) ⊢ᵗ B ∣ Δ -> Γ ⊢ᵗ B ∣ Δ
letv V M = sub-tm (sub-ex sub-id V) cosub-id M

lett : Γ ⊢ᵗ A ∣ Δ -> (Γ ∙ A) ⊢ᵗ B ∣ Δ -> Γ ⊢ᵗ B ∣ Δ
lett {A = A} {B = B} N M = μ (cut A (wk̃ᵗ N) (μ̃ (cut B (wk̃ᵗ M) (covar here))))

letc : Γ ∣ A ⊢ᵏ Δ -> Γ ⊢ (Δ ∙ A) -> Γ ⊢ Δ
letc K M = sub-cmd sub-id (cosub-ex cosub-id K) M

letvc : Γ ⊢ᵛ A ∣ Δ -> (Γ ∙ A) ⊢ Δ -> Γ ⊢ Δ
letvc V M' = sub-cmd (sub-ex sub-id V) cosub-id M'

applyL : Γ ⊢ᵛ (A `⇒ B) ∣ Δ -> Γ ⊢ᵛ A ∣ Δ -> Γ ⊢ᵗ B ∣ Δ
applyL f a = μ (cut _ (ret (wk̃ᵛ f)) (app (wk̃ᵛ a) (covar here)))

projFst : Γ ⊢ᵛ (A `× B) ∣ Δ -> Γ ⊢ᵗ A ∣ Δ
projFst p = μ (cut _ (ret (wk̃ᵛ p)) (fst (covar here)))

projSnd : Γ ⊢ᵛ (A `× B) ∣ Δ -> Γ ⊢ᵗ B ∣ Δ
projSnd p = μ (cut _ (ret (wk̃ᵛ p)) (snd (covar here)))

letpv : Γ ⊢ᵛ A₁ `× A₂ ∣ Δ -> (Γ ∙ A₁ ∙ A₂) ⊢ᵗ B ∣ Δ -> Γ ⊢ᵗ B ∣ Δ
letpv V M = lett (projFst V) (lett (projSnd (wkᵛ V)) M)

efq : Γ ⊢ᵗ `⊥ ∣ Δ -> Γ ⊢ᵗ A ∣ Δ
efq u = μ (cut `⊥ (wk̃ᵗ u) tp)

variable
  V V1 V2 V3 W W1 W2 : Γ ⊢ᵛ A ∣ Δ
  M M1 M2 M3 N N1 N2 : Γ ⊢ᵗ A ∣ Δ
  K K1 K2 K3 K4 : Γ ∣ A ⊢ᵏ Δ
  M' M1' M2' M3' : Γ ⊢ Δ

syntax EqVal Γ Δ A V1 V2 = Γ ⊢ᵛ V1 ≈ V2 ∶ A ∣ Δ

data EqVal (Γ Δ : Ctx) : (A : Ty) -> Γ ⊢ᵛ A ∣ Δ -> Γ ⊢ᵛ A ∣ Δ -> Set

syntax EqTm Γ Δ A M1 M2 = Γ ⊢ᵗ M1 ≈ M2 ∶ A ∣ Δ

data EqTm (Γ Δ : Ctx) : (A : Ty) -> Γ ⊢ᵗ A ∣ Δ -> Γ ⊢ᵗ A ∣ Δ -> Set

syntax EqCoTm Γ Δ A K1 K2 = Γ ∣ K1 ≈ K2 ∶ A ⊢ᵏ Δ

data EqCoTm (Γ Δ : Ctx) : (A : Ty) -> Γ ∣ A ⊢ᵏ Δ -> Γ ∣ A ⊢ᵏ Δ -> Set

syntax EqCmd Γ Δ M1' M2' = Γ ⊢ M1' ≈ M2' ⊣ Δ

data EqCmd (Γ Δ : Ctx) : Γ ⊢ Δ -> Γ ⊢ Δ -> Set

data EqVal Γ Δ where

  -- equivalence rules
  ≈-refl  :
          -----------------
          Γ ⊢ᵛ V ≈ V ∶ A ∣ Δ

  ≈-sym   : Γ ⊢ᵛ V1 ≈ V2 ∶ A ∣ Δ
          ----------------------
          -> Γ ⊢ᵛ V2 ≈ V1 ∶ A ∣ Δ

  ≈-trans : Γ ⊢ᵛ V1 ≈ V2 ∶ A ∣ Δ -> Γ ⊢ᵛ V2 ≈ V3 ∶ A ∣ Δ
          -----------------------------------------------
          -> Γ ⊢ᵛ V1 ≈ V3 ∶ A ∣ Δ

  -- congruence rules
  lam-cong : (Γ ∙ A) ⊢ᵗ M1 ≈ M2 ∶ B ∣ Δ
           -----------------------------------
           -> Γ ⊢ᵛ lam M1 ≈ lam M2 ∶ A `⇒ B ∣ Δ

  pair-cong : Γ ⊢ᵛ V1 ≈ V2 ∶ A ∣ Δ -> Γ ⊢ᵛ W1 ≈ W2 ∶ B ∣ Δ
            ---------------------------------------------------
            -> Γ ⊢ᵛ pair V1 W1 ≈ pair V2 W2 ∶ A `× B ∣ Δ

  inl-cong : Γ ⊢ᵛ V1 ≈ V2 ∶ A ∣ Δ
           -----------------------------------
           -> Γ ⊢ᵛ inl V1 ≈ inl V2 ∶ A `+ B ∣ Δ

  inr-cong : Γ ⊢ᵛ W1 ≈ W2 ∶ B ∣ Δ
           -----------------------------------
           -> Γ ⊢ᵛ inr W1 ≈ inr W2 ∶ A `+ B ∣ Δ

  -- eta rules

  unit-eta : (V : Γ ⊢ᵛ `Unit ∣ Δ)
           --------------------------
           -> Γ ⊢ᵛ V ≈ unit ∶ `Unit ∣ Δ

  lam-eta : (V : Γ ⊢ᵛ A `⇒ B ∣ Δ)
          -----------------------------------------------------------------------------------
          -> Γ ⊢ᵛ V ≈ lam (μ (cut (A `⇒ B) (ret (wk̃ᵛ (wkᵛ V))) (app (var here) (covar here)))) ∶ A `⇒ B ∣ Δ

data EqTm Γ Δ where

  -- equivalence rules
  ≈-refl  :
          -----------------
          Γ ⊢ᵗ M ≈ M ∶ A ∣ Δ

  ≈-sym   : Γ ⊢ᵗ M1 ≈ M2 ∶ A ∣ Δ
          ----------------------
          -> Γ ⊢ᵗ M2 ≈ M1 ∶ A ∣ Δ

  ≈-trans : Γ ⊢ᵗ M1 ≈ M2 ∶ A ∣ Δ -> Γ ⊢ᵗ M2 ≈ M3 ∶ A ∣ Δ
          -----------------------------------------------
          -> Γ ⊢ᵗ M1 ≈ M3 ∶ A ∣ Δ

  -- congruence rules
  ret-cong : Γ ⊢ᵛ V1 ≈ V2 ∶ A ∣ Δ
           ---------------------------
           -> Γ ⊢ᵗ ret V1 ≈ ret V2 ∶ A ∣ Δ

  μ-cong : Γ ⊢ M1' ≈ M2' ⊣ (Δ ∙ A)
         -------------------------
         -> Γ ⊢ᵗ μ M1' ≈ μ M2' ∶ A ∣ Δ

  -- structural (eta) rule

  μ-eta : (M : Γ ⊢ᵗ A ∣ Δ)
        ------------------------------------------
        -> Γ ⊢ᵗ M ≈ μ (cut A (wk̃ᵗ M) (covar here)) ∶ A ∣ Δ

  -- surjective pairing

  pair-eta : (V : Γ ⊢ᵛ A `× B ∣ Δ)
           ---------------------------------------------------------------------------------
           -> Γ ⊢ᵗ ret V
              ≈ lett (μ (cut (A `× B) (ret (wk̃ᵛ V)) (fst (covar here))))
                     (lett (μ (cut (A `× B) (ret (wk̃ᵛ (wkᵛ V))) (snd (covar here))))
                           (ret (pair (var (there here)) (var here))))
              ∶ A `× B ∣ Δ

data EqCoTm Γ Δ where

  -- equivalence rules
  ≈-refl  :
          ---------------------
          Γ ∣ K ≈ K ∶ A ⊢ᵏ Δ

  ≈-sym   : Γ ∣ K1 ≈ K2 ∶ A ⊢ᵏ Δ
          ----------------------
          -> Γ ∣ K2 ≈ K1 ∶ A ⊢ᵏ Δ

  ≈-trans : Γ ∣ K1 ≈ K2 ∶ A ⊢ᵏ Δ -> Γ ∣ K2 ≈ K3 ∶ A ⊢ᵏ Δ
          -----------------------------------------------
          -> Γ ∣ K1 ≈ K3 ∶ A ⊢ᵏ Δ

  -- congruence rules
  app-cong : Γ ⊢ᵛ V1 ≈ V2 ∶ A ∣ Δ -> Γ ∣ K1 ≈ K2 ∶ B ⊢ᵏ Δ
           -----------------------------------------------------
           -> Γ ∣ app V1 K1 ≈ app V2 K2 ∶ A `⇒ B ⊢ᵏ Δ

  fst-cong : Γ ∣ K1 ≈ K2 ∶ A ⊢ᵏ Δ
           -----------------------------------
           -> Γ ∣ fst K1 ≈ fst K2 ∶ A `× B ⊢ᵏ Δ

  snd-cong : Γ ∣ K1 ≈ K2 ∶ B ⊢ᵏ Δ
           -----------------------------------
           -> Γ ∣ snd K1 ≈ snd K2 ∶ A `× B ⊢ᵏ Δ

  case-cong : Γ ∣ K1 ≈ K2 ∶ A ⊢ᵏ Δ -> Γ ∣ K3 ≈ K4 ∶ B ⊢ᵏ Δ
            -------------------------------------------------------
            -> Γ ∣ case K1 K3 ≈ case K2 K4 ∶ A `+ B ⊢ᵏ Δ

  μ̃-cong : (Γ ∙ A) ⊢ M1' ≈ M2' ⊣ Δ
         ---------------------------
         -> Γ ∣ μ̃ M1' ≈ μ̃ M2' ∶ A ⊢ᵏ Δ

  -- structural (eta) rule

  μ̃-eta : (K : Γ ∣ A ⊢ᵏ Δ)
        --------------------------------------------
        -> Γ ∣ K ≈ μ̃ (cut A (ret (var here)) (wkᵏ K)) ∶ A ⊢ᵏ Δ

  case-eta : (K : Γ ∣ A `+ B ⊢ᵏ Δ)
           -----------------------------------------------------------------------------
           -> Γ ∣ K ≈ case (μ̃ (cut (A `+ B) (ret (inl (var here))) (wkᵏ K)))
                           (μ̃ (cut (A `+ B) (ret (inr (var here))) (wkᵏ K))) ∶ A `+ B ⊢ᵏ Δ

data EqCmd Γ Δ where

  -- equivalence rules
  ≈-refl  :
          -----------
          Γ ⊢ M' ≈ M' ⊣ Δ

  ≈-sym   : Γ ⊢ M1' ≈ M2' ⊣ Δ
          -----------------
          -> Γ ⊢ M2' ≈ M1' ⊣ Δ

  ≈-trans : Γ ⊢ M1' ≈ M2' ⊣ Δ -> Γ ⊢ M2' ≈ M3' ⊣ Δ
          -----------------------------------
          -> Γ ⊢ M1' ≈ M3' ⊣ Δ

  -- congruence rule
  cut-cong : Γ ⊢ᵗ M1 ≈ M2 ∶ A ∣ Δ -> Γ ∣ K1 ≈ K2 ∶ A ⊢ᵏ Δ
           --------------------------------------------------------------
           -> Γ ⊢ cut A M1 K1 ≈ cut A M2 K2 ⊣ Δ

  -- beta rules (cut elimination)

  μ-beta : (M' : Γ ⊢ (Δ ∙ A)) -> (K : Γ ∣ A ⊢ᵏ Δ)
         -----------------------------------------
         -> Γ ⊢ cut A (μ M') K ≈ letc K M' ⊣ Δ

  μ̃-beta : (V : Γ ⊢ᵛ A ∣ Δ) -> (M' : (Γ ∙ A) ⊢ Δ)
         -------------------------------------------
         -> Γ ⊢ cut A (ret V) (μ̃ M') ≈ letvc V M' ⊣ Δ

  app-beta : (M : (Γ ∙ A) ⊢ᵗ B ∣ Δ) -> (V : Γ ⊢ᵛ A ∣ Δ) -> (K : Γ ∣ B ⊢ᵏ Δ)
           ---------------------------------------------------------------------------
           -> Γ ⊢ cut (A `⇒ B) (ret (lam M)) (app V K) ≈ cut B (letv V M) K ⊣ Δ

  fst-beta : (V : Γ ⊢ᵛ A ∣ Δ) -> (W : Γ ⊢ᵛ B ∣ Δ) -> (K : Γ ∣ A ⊢ᵏ Δ)
           -----------------------------------------------------------------
           -> Γ ⊢ cut (A `× B) (ret (pair V W)) (fst K) ≈ cut A (ret V) K ⊣ Δ

  snd-beta : (V : Γ ⊢ᵛ A ∣ Δ) -> (W : Γ ⊢ᵛ B ∣ Δ) -> (K : Γ ∣ B ⊢ᵏ Δ)
           -----------------------------------------------------------------
           -> Γ ⊢ cut (A `× B) (ret (pair V W)) (snd K) ≈ cut B (ret W) K ⊣ Δ

  inl-beta : (V : Γ ⊢ᵛ A ∣ Δ) -> (K1 : Γ ∣ A ⊢ᵏ Δ) -> (K2 : Γ ∣ B ⊢ᵏ Δ)
           -----------------------------------------------------------------------
           -> Γ ⊢ cut (A `+ B) (ret (inl V)) (case K1 K2) ≈ cut A (ret V) K1 ⊣ Δ

  inr-beta : (W : Γ ⊢ᵛ B ∣ Δ) -> (K1 : Γ ∣ A ⊢ᵏ Δ) -> (K2 : Γ ∣ B ⊢ᵏ Δ)
           -----------------------------------------------------------------------
           -> Γ ⊢ cut (A `+ B) (ret (inr W)) (case K1 K2) ≈ cut B (ret W) K2 ⊣ Δ

--------------------------------------------------------------------------
-- weakening lemmas

mutual
  wk-cmd-id : (M' : Γ ⊢ Δ) -> wk-cmd wk-id wk-id M' ≡ M'
  wk-cmd-id (cut A M K) = cong₂ (cut A) (wk-tm-id M) (wk-cotm-id K)

  wk-val-id : (V : Γ ⊢ᵛ A ∣ Δ) -> wk-val wk-id wk-id V ≡ V
  wk-val-id (var i)    = cong var wk-mem-id
  wk-val-id (lam M)    = cong lam (wk-tm-id M)
  wk-val-id unit       = refl
  wk-val-id (pair V W) = cong₂ pair (wk-val-id V) (wk-val-id W)
  wk-val-id (inl V)    = cong inl (wk-val-id V)
  wk-val-id (inr W)    = cong inr (wk-val-id W)

  wk-tm-id : (M : Γ ⊢ᵗ A ∣ Δ) -> wk-tm wk-id wk-id M ≡ M
  wk-tm-id (ret V) = cong ret (wk-val-id V)
  wk-tm-id (μ M')   = cong μ (wk-cmd-id M')

  wk-cotm-id : (K : Γ ∣ A ⊢ᵏ Δ) -> wk-cotm wk-id wk-id K ≡ K
  wk-cotm-id (covar i) = cong covar wk-mem-id
  wk-cotm-id (app V K) = cong₂ app (wk-val-id V) (wk-cotm-id K)
  wk-cotm-id (fst K)   = cong fst (wk-cotm-id K)
  wk-cotm-id (snd K)   = cong snd (wk-cotm-id K)
  wk-cotm-id (case K1 K2) = cong₂ case (wk-cotm-id K1) (wk-cotm-id K2)
  wk-cotm-id (μ̃ M')     = cong μ̃ (wk-cmd-id M')
  wk-cotm-id tp        = refl

mutual
  wk-cmd-trans : (M' : Γ ⊢ Δ) (ρ1 : Ψ ⊇ Γ₁) (ρ2 : Γ₁ ⊇ Γ) (σ1 : Ψ' ⊇ Δ₁) (σ2 : Δ₁ ⊇ Δ)
               -> wk-cmd ρ1 σ1 (wk-cmd ρ2 σ2 M') ≡ wk-cmd (wk-trans ρ1 ρ2) (wk-trans σ1 σ2) M'
  wk-cmd-trans (cut A M K) ρ1 ρ2 σ1 σ2 = cong₂ (cut A) (wk-tm-trans M ρ1 ρ2 σ1 σ2) (wk-cotm-trans K ρ1 ρ2 σ1 σ2)

  wk-val-trans : (V : Γ ⊢ᵛ A ∣ Δ) (ρ1 : Ψ ⊇ Γ₁) (ρ2 : Γ₁ ⊇ Γ) (σ1 : Ψ' ⊇ Δ₁) (σ2 : Δ₁ ⊇ Δ)
               -> wk-val ρ1 σ1 (wk-val ρ2 σ2 V) ≡ wk-val (wk-trans ρ1 ρ2) (wk-trans σ1 σ2) V
  wk-val-trans (var i) ρ1 ρ2 σ1 σ2    = cong var (wk-mem-trans i ρ1 ρ2)
  wk-val-trans (lam M) ρ1 ρ2 σ1 σ2    = cong lam (wk-tm-trans M (wk-cong ρ1) (wk-cong ρ2) σ1 σ2)
  wk-val-trans unit ρ1 ρ2 σ1 σ2       = refl
  wk-val-trans (pair V W) ρ1 ρ2 σ1 σ2 = cong₂ pair (wk-val-trans V ρ1 ρ2 σ1 σ2) (wk-val-trans W ρ1 ρ2 σ1 σ2)
  wk-val-trans (inl V) ρ1 ρ2 σ1 σ2    = cong inl (wk-val-trans V ρ1 ρ2 σ1 σ2)
  wk-val-trans (inr W) ρ1 ρ2 σ1 σ2    = cong inr (wk-val-trans W ρ1 ρ2 σ1 σ2)

  wk-tm-trans : (M : Γ ⊢ᵗ A ∣ Δ) (ρ1 : Ψ ⊇ Γ₁) (ρ2 : Γ₁ ⊇ Γ) (σ1 : Ψ' ⊇ Δ₁) (σ2 : Δ₁ ⊇ Δ)
              -> wk-tm ρ1 σ1 (wk-tm ρ2 σ2 M) ≡ wk-tm (wk-trans ρ1 ρ2) (wk-trans σ1 σ2) M
  wk-tm-trans (ret V) ρ1 ρ2 σ1 σ2 = cong ret (wk-val-trans V ρ1 ρ2 σ1 σ2)
  wk-tm-trans (μ M') ρ1 ρ2 σ1 σ2   = cong μ (wk-cmd-trans M' ρ1 ρ2 (wk-cong σ1) (wk-cong σ2))

  wk-cotm-trans : (K : Γ ∣ A ⊢ᵏ Δ) (ρ1 : Ψ ⊇ Γ₁) (ρ2 : Γ₁ ⊇ Γ) (σ1 : Ψ' ⊇ Δ₁) (σ2 : Δ₁ ⊇ Δ)
               -> wk-cotm ρ1 σ1 (wk-cotm ρ2 σ2 K) ≡ wk-cotm (wk-trans ρ1 ρ2) (wk-trans σ1 σ2) K
  wk-cotm-trans (covar i) ρ1 ρ2 σ1 σ2 = cong covar (wk-mem-trans i σ1 σ2)
  wk-cotm-trans (app V K) ρ1 ρ2 σ1 σ2 = cong₂ app (wk-val-trans V ρ1 ρ2 σ1 σ2) (wk-cotm-trans K ρ1 ρ2 σ1 σ2)
  wk-cotm-trans (fst K) ρ1 ρ2 σ1 σ2   = cong fst (wk-cotm-trans K ρ1 ρ2 σ1 σ2)
  wk-cotm-trans (snd K) ρ1 ρ2 σ1 σ2   = cong snd (wk-cotm-trans K ρ1 ρ2 σ1 σ2)
  wk-cotm-trans (case K1 K2) ρ1 ρ2 σ1 σ2 = cong₂ case (wk-cotm-trans K1 ρ1 ρ2 σ1 σ2) (wk-cotm-trans K2 ρ1 ρ2 σ1 σ2)
  wk-cotm-trans (μ̃ M') ρ1 ρ2 σ1 σ2     = cong μ̃ (wk-cmd-trans M' (wk-cong ρ1) (wk-cong ρ2) σ1 σ2)
  wk-cotm-trans tp ρ1 ρ2 σ1 σ2        = refl

--------------------------------------------------------------------------
-- weakening/substitution

sub-wk-trans : {Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ Ψ : Ctx} (ρ1 : Γ ⊇ Γ₁) (σ1 : Δ ⊇ Δ₁) (ρ2 : Γ₁ ⊇ Γ₂) (σ2 : Δ₁ ⊇ Δ₂) (θ : Sub Γ₂ Δ₂ Ψ)
             -> sub-wk ρ1 σ1 (sub-wk ρ2 σ2 θ) ≡ sub-wk (wk-trans ρ1 ρ2) (wk-trans σ1 σ2) θ
sub-wk-trans ρ1 σ1 ρ2 σ2 sub-ε         = refl
sub-wk-trans ρ1 σ1 ρ2 σ2 (sub-ex θ V)  = cong₂ sub-ex (sub-wk-trans ρ1 σ1 ρ2 σ2 θ) (wk-val-trans V ρ1 ρ2 σ1 σ2)

cosub-wk-trans : {Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ Ψ : Ctx} (ρ1 : Γ ⊇ Γ₁) (σ1 : Δ ⊇ Δ₁) (ρ2 : Γ₁ ⊇ Γ₂) (σ2 : Δ₁ ⊇ Δ₂) (φ : CoSub Γ₂ Δ₂ Ψ)
               -> cosub-wk ρ1 σ1 (cosub-wk ρ2 σ2 φ) ≡ cosub-wk (wk-trans ρ1 ρ2) (wk-trans σ1 σ2) φ
cosub-wk-trans ρ1 σ1 ρ2 σ2 cosub-ε        = refl
cosub-wk-trans ρ1 σ1 ρ2 σ2 (cosub-ex φ K) = cong₂ cosub-ex (cosub-wk-trans ρ1 σ1 ρ2 σ2 φ) (wk-cotm-trans K ρ1 ρ2 σ1 σ2)

sub-mem-wk : (ρ : Γ ⊇ Γ') (σ : Δ ⊇ Δ') (θ : Sub Γ' Δ' Ψ) (i : Ψ ∋ A) -> sub-mem (sub-wk ρ σ θ) i ≡ wk-val ρ σ (sub-mem θ i)
sub-mem-wk ρ σ (sub-ex θ V) here     = refl
sub-mem-wk ρ σ (sub-ex θ V) (there i) = sub-mem-wk ρ σ θ i

cosub-mem-wk : (ρ : Γ ⊇ Γ') (σ : Δ ⊇ Δ') (φ : CoSub Γ' Δ' Ψ) (i : Ψ ∋ A) -> cosub-mem (cosub-wk ρ σ φ) i ≡ wk-cotm ρ σ (cosub-mem φ i)
cosub-mem-wk ρ σ (cosub-ex φ K) here     = refl
cosub-mem-wk ρ σ (cosub-ex φ K) (there i) = cosub-mem-wk ρ σ φ i

sub-wk-id : (θ : Sub Γ Δ Γ') -> sub-wk wk-id wk-id θ ≡ θ
sub-wk-id sub-ε        = refl
sub-wk-id (sub-ex θ V) = cong₂ sub-ex (sub-wk-id θ) (wk-val-id V)

cosub-wk-id : (φ : CoSub Γ Δ Δ') -> cosub-wk wk-id wk-id φ ≡ φ
cosub-wk-id cosub-ε        = refl
cosub-wk-id (cosub-ex φ K) = cong₂ cosub-ex (cosub-wk-id φ) (wk-cotm-id K)

sub-wk-cong-lemma : (ρ : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) (θ : Sub Γ Δ Ψ)
                  -> sub-wk (wk-cong {A = A} ρ) σ (sub-wk (wk-wk wk-id) wk-id θ) ≡ sub-wk (wk-wk wk-id) wk-id (sub-wk ρ σ θ)
sub-wk-cong-lemma ρ σ θ = begin
  sub-wk (wk-cong ρ) σ (sub-wk (wk-wk wk-id) wk-id θ)     ≡⟨ sub-wk-trans (wk-cong ρ) σ (wk-wk wk-id) wk-id θ ⟩
  sub-wk (wk-wk (wk-trans ρ wk-id)) (wk-trans σ wk-id) θ  ≡⟨ cong₂ (λ π τ -> sub-wk (wk-wk π) τ θ) (wk-trans-idr ρ) (wk-trans-idr σ) ⟩
  sub-wk (wk-wk ρ) σ θ                                    ≡˘⟨ cong₂ (λ π τ -> sub-wk (wk-wk π) τ θ) (wk-trans-idl ρ) (wk-trans-idl σ) ⟩
  sub-wk (wk-wk (wk-trans wk-id ρ)) (wk-trans wk-id σ) θ  ≡˘⟨ sub-wk-trans (wk-wk wk-id) wk-id ρ σ θ ⟩
  sub-wk (wk-wk wk-id) wk-id (sub-wk ρ σ θ)               ∎

cosub-wk-cong-lemma : (ρ : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) (φ : CoSub Γ Δ Ψ)
                    -> cosub-wk (wk-cong {A = A} ρ) σ (cosub-wk (wk-wk wk-id) wk-id φ) ≡ cosub-wk (wk-wk wk-id) wk-id (cosub-wk ρ σ φ)
cosub-wk-cong-lemma ρ σ φ = begin
  cosub-wk (wk-cong ρ) σ (cosub-wk (wk-wk wk-id) wk-id φ)     ≡⟨ cosub-wk-trans (wk-cong ρ) σ (wk-wk wk-id) wk-id φ ⟩
  cosub-wk (wk-wk (wk-trans ρ wk-id)) (wk-trans σ wk-id) φ    ≡⟨ cong₂ (λ π τ -> cosub-wk (wk-wk π) τ φ) (wk-trans-idr ρ) (wk-trans-idr σ) ⟩
  cosub-wk (wk-wk ρ) σ φ                                      ≡˘⟨ cong₂ (λ π τ -> cosub-wk (wk-wk π) τ φ) (wk-trans-idl ρ) (wk-trans-idl σ) ⟩
  cosub-wk (wk-wk (wk-trans wk-id ρ)) (wk-trans wk-id σ) φ    ≡˘⟨ cosub-wk-trans (wk-wk wk-id) wk-id ρ σ φ ⟩
  cosub-wk (wk-wk wk-id) wk-id (cosub-wk ρ σ φ)               ∎

sub-wk-cong-lemma-Δ : (ρ : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) (θ : Sub Γ Δ Ψ)
                     -> sub-wk ρ (wk-cong {A = A} σ) (sub-wk wk-id (wk-wk wk-id) θ) ≡ sub-wk wk-id (wk-wk wk-id) (sub-wk ρ σ θ)
sub-wk-cong-lemma-Δ ρ σ θ = begin
  sub-wk ρ (wk-cong σ) (sub-wk wk-id (wk-wk wk-id) θ)     ≡⟨ sub-wk-trans ρ (wk-cong σ) wk-id (wk-wk wk-id) θ ⟩
  sub-wk (wk-trans ρ wk-id) (wk-wk (wk-trans σ wk-id)) θ  ≡⟨ cong₂ (λ π τ -> sub-wk π (wk-wk τ) θ) (wk-trans-idr ρ) (wk-trans-idr σ) ⟩
  sub-wk ρ (wk-wk σ) θ                                    ≡˘⟨ cong₂ (λ π τ -> sub-wk π (wk-wk τ) θ) (wk-trans-idl ρ) (wk-trans-idl σ) ⟩
  sub-wk (wk-trans wk-id ρ) (wk-wk (wk-trans wk-id σ)) θ  ≡˘⟨ sub-wk-trans wk-id (wk-wk wk-id) ρ σ θ ⟩
  sub-wk wk-id (wk-wk wk-id) (sub-wk ρ σ θ)               ∎

cosub-wk-cong-lemma-Δ : (ρ : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) (φ : CoSub Γ Δ Ψ)
                      -> cosub-wk ρ (wk-cong {A = A} σ) (cosub-wk wk-id (wk-wk wk-id) φ) ≡ cosub-wk wk-id (wk-wk wk-id) (cosub-wk ρ σ φ)
cosub-wk-cong-lemma-Δ ρ σ φ = begin
  cosub-wk ρ (wk-cong σ) (cosub-wk wk-id (wk-wk wk-id) φ)     ≡⟨ cosub-wk-trans ρ (wk-cong σ) wk-id (wk-wk wk-id) φ ⟩
  cosub-wk (wk-trans ρ wk-id) (wk-wk (wk-trans σ wk-id)) φ    ≡⟨ cong₂ (λ π τ -> cosub-wk π (wk-wk τ) φ) (wk-trans-idr ρ) (wk-trans-idr σ) ⟩
  cosub-wk ρ (wk-wk σ) φ                                      ≡˘⟨ cong₂ (λ π τ -> cosub-wk π (wk-wk τ) φ) (wk-trans-idl ρ) (wk-trans-idl σ) ⟩
  cosub-wk (wk-trans wk-id ρ) (wk-wk (wk-trans wk-id σ)) φ    ≡˘⟨ cosub-wk-trans wk-id (wk-wk wk-id) ρ σ φ ⟩
  cosub-wk wk-id (wk-wk wk-id) (cosub-wk ρ σ φ)               ∎

sub-wk-wk-shift : (ρ : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) (θ : Sub Γ Δ Ψ)
                 -> sub-wk (wk-wk {A = B} ρ) σ θ ≡ sub-wk (wk-wk {A = B} wk-id) wk-id (sub-wk ρ σ θ)
sub-wk-wk-shift ρ σ θ = begin
  sub-wk (wk-wk ρ) σ θ                                    ≡˘⟨ cong₂ (λ x y -> sub-wk (wk-wk x) y θ) (wk-trans-idl ρ) (wk-trans-idl σ) ⟩
  sub-wk (wk-wk (wk-trans wk-id ρ)) (wk-trans wk-id σ) θ  ≡˘⟨ sub-wk-trans (wk-wk wk-id) wk-id ρ σ θ ⟩
  sub-wk (wk-wk wk-id) wk-id (sub-wk ρ σ θ)               ∎

cosub-wk-wk-shift : (ρ : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) (φ : CoSub Γ Δ Ψ)
                   -> cosub-wk ρ (wk-wk {A = B} σ) φ ≡ cosub-wk wk-id (wk-wk {A = B} wk-id) (cosub-wk ρ σ φ)
cosub-wk-wk-shift ρ σ φ = begin
  cosub-wk ρ (wk-wk σ) φ                                    ≡˘⟨ cong₂ (λ x y -> cosub-wk x (wk-wk y) φ) (wk-trans-idl ρ) (wk-trans-idl σ) ⟩
  cosub-wk (wk-trans wk-id ρ) (wk-wk (wk-trans wk-id σ)) φ  ≡˘⟨ cosub-wk-trans wk-id (wk-wk wk-id) ρ σ φ ⟩
  cosub-wk wk-id (wk-wk wk-id) (cosub-wk ρ σ φ)             ∎

sub-mem-id : (i : Γ ∋ A) -> sub-mem (sub-id {Γ} {Δ}) i ≡ var i
sub-mem-id here     = refl
sub-mem-id (there i) = begin
  sub-mem (sub-wk (wk-wk wk-id) wk-id sub-id) i       ≡⟨ sub-mem-wk (wk-wk wk-id) wk-id sub-id i ⟩
  wk-val (wk-wk wk-id) wk-id (sub-mem sub-id i)       ≡⟨ cong (wk-val (wk-wk wk-id) wk-id) (sub-mem-id i) ⟩
  wk-val (wk-wk wk-id) wk-id (var i)                  ≡⟨⟩
  var (wk-mem (wk-wk wk-id) i)                        ≡⟨ cong var (wk-mem-wk-wk wk-id i) ⟩
  var (there (wk-mem wk-id i))                            ≡⟨ cong (λ j -> var (there j)) wk-mem-id ⟩
  var (there i)                                           ∎

cosub-mem-id : (i : Δ ∋ A) -> cosub-mem (cosub-id {Γ} {Δ}) i ≡ covar i
cosub-mem-id here     = refl
cosub-mem-id (there i) = begin
  cosub-mem (cosub-wk wk-id (wk-wk wk-id) cosub-id) i       ≡⟨ cosub-mem-wk wk-id (wk-wk wk-id) cosub-id i ⟩
  wk-cotm wk-id (wk-wk wk-id) (cosub-mem cosub-id i)         ≡⟨ cong (wk-cotm wk-id (wk-wk wk-id)) (cosub-mem-id i) ⟩
  wk-cotm wk-id (wk-wk wk-id) (covar i)                      ≡⟨⟩
  covar (wk-mem (wk-wk wk-id) i)                            ≡⟨ cong covar (wk-mem-wk-wk wk-id i) ⟩
  covar (there (wk-mem wk-id i))                                ≡⟨ cong (λ j -> covar (there j)) wk-mem-id ⟩
  covar (there i)                                               ∎

sub-id-Δ-wk-gen : (ρ : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) -> sub-wk ρ σ (sub-id {Γ} {Δ}) ≡ sub-wk ρ wk-id (sub-id {Γ} {Δ'})
sub-id-Δ-wk-gen wk-ε σ = refl
sub-id-Δ-wk-gen (wk-cong ρ) σ =
  cong₂ sub-ex
    (begin
      sub-wk (wk-cong ρ) σ (sub-wk (wk-wk wk-id) wk-id sub-id)  ≡⟨ sub-wk-cong-lemma ρ σ sub-id ⟩
      sub-wk (wk-wk wk-id) wk-id (sub-wk ρ σ sub-id)            ≡⟨ cong (sub-wk (wk-wk wk-id) wk-id) (sub-id-Δ-wk-gen ρ σ) ⟩
      sub-wk (wk-wk wk-id) wk-id (sub-wk ρ wk-id sub-id)        ≡˘⟨ sub-wk-cong-lemma ρ wk-id sub-id ⟩
      sub-wk (wk-cong ρ) wk-id (sub-wk (wk-wk wk-id) wk-id sub-id)  ∎)
    refl
sub-id-Δ-wk-gen (wk-wk ρ) σ = begin
  sub-wk (wk-wk ρ) σ sub-id                            ≡⟨ sub-wk-wk-shift ρ σ sub-id ⟩
  sub-wk (wk-wk wk-id) wk-id (sub-wk ρ σ sub-id)        ≡⟨ cong (sub-wk (wk-wk wk-id) wk-id) (sub-id-Δ-wk-gen ρ σ) ⟩
  sub-wk (wk-wk wk-id) wk-id (sub-wk ρ wk-id sub-id)    ≡˘⟨ sub-wk-wk-shift ρ wk-id sub-id ⟩
  sub-wk (wk-wk ρ) wk-id sub-id                         ∎

sub-id-Δ-wk : (σ : Δ' ⊇ Δ) -> sub-wk wk-id σ (sub-id {Γ} {Δ}) ≡ sub-id {Γ} {Δ'}
sub-id-Δ-wk σ = begin
  sub-wk wk-id σ sub-id  ≡⟨ sub-id-Δ-wk-gen wk-id σ ⟩
  sub-wk wk-id wk-id sub-id  ≡⟨ sub-wk-id sub-id ⟩
  sub-id                 ∎

cosub-id-Γ-wk-gen : (ρ : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) -> cosub-wk ρ σ (cosub-id {Γ} {Δ}) ≡ cosub-wk wk-id σ (cosub-id {Γ'} {Δ})
cosub-id-Γ-wk-gen ρ wk-ε = refl
cosub-id-Γ-wk-gen ρ (wk-cong σ) =
  cong₂ cosub-ex
    (begin
      cosub-wk ρ (wk-cong σ) (cosub-wk wk-id (wk-wk wk-id) cosub-id)  ≡⟨ cosub-wk-cong-lemma-Δ ρ σ cosub-id ⟩
      cosub-wk wk-id (wk-wk wk-id) (cosub-wk ρ σ cosub-id)            ≡⟨ cong (cosub-wk wk-id (wk-wk wk-id)) (cosub-id-Γ-wk-gen ρ σ) ⟩
      cosub-wk wk-id (wk-wk wk-id) (cosub-wk wk-id σ cosub-id)        ≡˘⟨ cosub-wk-cong-lemma-Δ wk-id σ cosub-id ⟩
      cosub-wk wk-id (wk-cong σ) (cosub-wk wk-id (wk-wk wk-id) cosub-id)  ∎)
    refl
cosub-id-Γ-wk-gen ρ (wk-wk σ) = begin
  cosub-wk ρ (wk-wk σ) cosub-id                          ≡⟨ cosub-wk-wk-shift ρ σ cosub-id ⟩
  cosub-wk wk-id (wk-wk wk-id) (cosub-wk ρ σ cosub-id)   ≡⟨ cong (cosub-wk wk-id (wk-wk wk-id)) (cosub-id-Γ-wk-gen ρ σ) ⟩
  cosub-wk wk-id (wk-wk wk-id) (cosub-wk wk-id σ cosub-id)  ≡˘⟨ cosub-wk-wk-shift wk-id σ cosub-id ⟩
  cosub-wk wk-id (wk-wk σ) cosub-id                      ∎

cosub-id-Γ-wk : (ρ : Γ' ⊇ Γ) -> cosub-wk ρ wk-id (cosub-id {Γ} {Δ}) ≡ cosub-id {Γ'} {Δ}
cosub-id-Γ-wk ρ = begin
  cosub-wk ρ wk-id cosub-id  ≡⟨ cosub-id-Γ-wk-gen ρ wk-id ⟩
  cosub-wk wk-id wk-id cosub-id  ≡⟨ cosub-wk-id cosub-id ⟩
  cosub-id                    ∎

--------------------------------------------------------------------------
-- identity substitution

mutual
  sub-cmd-id : (M' : Γ ⊢ Δ) -> sub-cmd sub-id cosub-id M' ≡ M'
  sub-cmd-id (cut A M K) = cong₂ (cut A) (sub-tm-id M) (sub-cotm-id K)

  sub-val-id : (V : Γ ⊢ᵛ A ∣ Δ) -> sub-val sub-id cosub-id V ≡ V
  sub-val-id (var i)    = sub-mem-id i
  sub-val-id (lam M)    = cong lam (begin
    sub-tm sub-id (cosub-wk (wk-wk wk-id) wk-id cosub-id) M  ≡⟨ cong (λ x -> sub-tm sub-id x M) (cosub-id-Γ-wk (wk-wk wk-id)) ⟩
    sub-tm sub-id cosub-id M                                 ≡⟨ sub-tm-id M ⟩
    M                                                         ∎)
  sub-val-id unit       = refl
  sub-val-id (pair V W) = cong₂ pair (sub-val-id V) (sub-val-id W)
  sub-val-id (inl V)    = cong inl (sub-val-id V)
  sub-val-id (inr W)    = cong inr (sub-val-id W)

  sub-tm-id : (M : Γ ⊢ᵗ A ∣ Δ) -> sub-tm sub-id cosub-id M ≡ M
  sub-tm-id (ret V) = cong ret (sub-val-id V)
  sub-tm-id (μ M')   = cong μ (begin
    sub-cmd (sub-wk wk-id (wk-wk wk-id) sub-id) cosub-id M'  ≡⟨ cong (λ x -> sub-cmd x cosub-id M') (sub-id-Δ-wk (wk-wk wk-id)) ⟩
    sub-cmd sub-id cosub-id M'                               ≡⟨ sub-cmd-id M' ⟩
    M'                                                        ∎)

  sub-cotm-id : (K : Γ ∣ A ⊢ᵏ Δ) -> sub-cotm sub-id cosub-id K ≡ K
  sub-cotm-id (covar i)    = cosub-mem-id i
  sub-cotm-id (app V K)    = cong₂ app (sub-val-id V) (sub-cotm-id K)
  sub-cotm-id (fst K)      = cong fst (sub-cotm-id K)
  sub-cotm-id (snd K)      = cong snd (sub-cotm-id K)
  sub-cotm-id (case K1 K2) = cong₂ case (sub-cotm-id K1) (sub-cotm-id K2)
  sub-cotm-id (μ̃ M')        = cong μ̃ (begin
    sub-cmd sub-id (cosub-wk (wk-wk wk-id) wk-id cosub-id) M'  ≡⟨ cong (λ x -> sub-cmd sub-id x M') (cosub-id-Γ-wk (wk-wk wk-id)) ⟩
    sub-cmd sub-id cosub-id M'                                 ≡⟨ sub-cmd-id M' ⟩
    M'                                                          ∎)
  sub-cotm-id tp           = refl

--------------------------------------------------------------------------
-- weakening commutes with substitution

mutual
  wk-sub-cmd : (ρ : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) (θ : Sub Γ Δ Ψ) (φ : CoSub Γ Δ Ψ') (M' : Ψ ⊢ Ψ')
             -> wk-cmd ρ σ (sub-cmd θ φ M') ≡ sub-cmd (sub-wk ρ σ θ) (cosub-wk ρ σ φ) M'
  wk-sub-cmd ρ σ θ φ (cut A M K) = cong₂ (cut A) (wk-sub-tm ρ σ θ φ M) (wk-sub-cotm ρ σ θ φ K)

  wk-sub-val : (ρ : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) (θ : Sub Γ Δ Ψ) (φ : CoSub Γ Δ Ψ') (V : Ψ ⊢ᵛ A ∣ Ψ')
             -> wk-val ρ σ (sub-val θ φ V) ≡ sub-val (sub-wk ρ σ θ) (cosub-wk ρ σ φ) V
  wk-sub-val ρ σ θ φ (var i) = sym (sub-mem-wk ρ σ θ i)
  wk-sub-val ρ σ θ φ (lam M) =
    cong lam (begin
      wk-tm (wk-cong ρ) σ (sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M)
        ≡⟨ wk-sub-tm (wk-cong ρ) σ (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M ⟩
      sub-tm (sub-ex (sub-wk (wk-cong ρ) σ (sub-wk (wk-wk wk-id) wk-id θ)) (var here)) (cosub-wk (wk-cong ρ) σ (cosub-wk (wk-wk wk-id) wk-id φ)) M
        ≡⟨ cong₂ (λ x y -> sub-tm (sub-ex x (var here)) y M) (sub-wk-cong-lemma ρ σ θ) (cosub-wk-cong-lemma ρ σ φ) ⟩
      sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-wk ρ σ θ)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-wk ρ σ φ)) M  ∎)
  wk-sub-val ρ σ θ φ unit       = refl
  wk-sub-val ρ σ θ φ (pair V W) = cong₂ pair (wk-sub-val ρ σ θ φ V) (wk-sub-val ρ σ θ φ W)
  wk-sub-val ρ σ θ φ (inl V)    = cong inl (wk-sub-val ρ σ θ φ V)
  wk-sub-val ρ σ θ φ (inr W)    = cong inr (wk-sub-val ρ σ θ φ W)

  wk-sub-tm : (ρ : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) (θ : Sub Γ Δ Ψ) (φ : CoSub Γ Δ Ψ') (M : Ψ ⊢ᵗ A ∣ Ψ')
            -> wk-tm ρ σ (sub-tm θ φ M) ≡ sub-tm (sub-wk ρ σ θ) (cosub-wk ρ σ φ) M
  wk-sub-tm ρ σ θ φ (ret V) = cong ret (wk-sub-val ρ σ θ φ V)
  wk-sub-tm ρ σ θ φ (μ M') =
    cong μ (begin
      wk-cmd ρ (wk-cong σ) (sub-cmd (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) M')
        ≡⟨ wk-sub-cmd ρ (wk-cong σ) (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) M' ⟩
      sub-cmd (sub-wk ρ (wk-cong σ) (sub-wk wk-id (wk-wk wk-id) θ)) (cosub-ex (cosub-wk ρ (wk-cong σ) (cosub-wk wk-id (wk-wk wk-id) φ)) (covar here)) M'
        ≡⟨ cong₂ (λ x y -> sub-cmd x (cosub-ex y (covar here)) M') (sub-wk-cong-lemma-Δ ρ σ θ) (cosub-wk-cong-lemma-Δ ρ σ φ) ⟩
      sub-cmd (sub-wk wk-id (wk-wk wk-id) (sub-wk ρ σ θ)) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) (cosub-wk ρ σ φ)) (covar here)) M'  ∎)

  wk-sub-cotm : (ρ : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) (θ : Sub Γ Δ Ψ) (φ : CoSub Γ Δ Ψ') (K : Ψ ∣ A ⊢ᵏ Ψ')
             -> wk-cotm ρ σ (sub-cotm θ φ K) ≡ sub-cotm (sub-wk ρ σ θ) (cosub-wk ρ σ φ) K
  wk-sub-cotm ρ σ θ φ (covar i)    = sym (cosub-mem-wk ρ σ φ i)
  wk-sub-cotm ρ σ θ φ (app V K)    = cong₂ app (wk-sub-val ρ σ θ φ V) (wk-sub-cotm ρ σ θ φ K)
  wk-sub-cotm ρ σ θ φ (fst K)      = cong fst (wk-sub-cotm ρ σ θ φ K)
  wk-sub-cotm ρ σ θ φ (snd K)      = cong snd (wk-sub-cotm ρ σ θ φ K)
  wk-sub-cotm ρ σ θ φ (case K1 K2) = cong₂ case (wk-sub-cotm ρ σ θ φ K1) (wk-sub-cotm ρ σ θ φ K2)
  wk-sub-cotm ρ σ θ φ (μ̃ M') =
    cong μ̃ (begin
      wk-cmd (wk-cong ρ) σ (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M')
        ≡⟨ wk-sub-cmd (wk-cong ρ) σ (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M' ⟩
      sub-cmd (sub-ex (sub-wk (wk-cong ρ) σ (sub-wk (wk-wk wk-id) wk-id θ)) (var here)) (cosub-wk (wk-cong ρ) σ (cosub-wk (wk-wk wk-id) wk-id φ)) M'
        ≡⟨ cong₂ (λ x y -> sub-cmd (sub-ex x (var here)) y M') (sub-wk-cong-lemma ρ σ θ) (cosub-wk-cong-lemma ρ σ φ) ⟩
      sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-wk ρ σ θ)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-wk ρ σ φ)) M'  ∎)
  wk-sub-cotm ρ σ θ φ tp = refl

--------------------------------------------------------------------------
-- substitution precomposed with weakening

sub-pre : Sub Γ Δ Γ' -> Γ' ⊇ Ψ -> Sub Γ Δ Ψ
sub-pre θ wk-ε              = sub-ε
sub-pre (sub-ex θ V) (wk-cong π) = sub-ex (sub-pre θ π) V
sub-pre (sub-ex θ V) (wk-wk π)   = sub-pre θ π

cosub-pre : CoSub Γ Δ Δ' -> Δ' ⊇ Ψ -> CoSub Γ Δ Ψ
cosub-pre φ wk-ε                 = cosub-ε
cosub-pre (cosub-ex φ K) (wk-cong π) = cosub-ex (cosub-pre φ π) K
cosub-pre (cosub-ex φ K) (wk-wk π)   = cosub-pre φ π

sub-mem-pre : (θ : Sub Γ Δ Γ') (π : Γ' ⊇ Ψ) (i : Ψ ∋ A) -> sub-mem (sub-pre θ π) i ≡ sub-mem θ (wk-mem π i)
sub-mem-pre (sub-ex θ V) (wk-cong π) here     = refl
sub-mem-pre (sub-ex θ V) (wk-cong π) (there i) = sub-mem-pre θ π i
sub-mem-pre (sub-ex θ V) (wk-wk π) i = begin
  sub-mem (sub-pre θ π) i               ≡⟨ sub-mem-pre θ π i ⟩
  sub-mem θ (wk-mem π i)                ≡˘⟨ cong (λ j -> sub-mem (sub-ex θ V) j) (wk-mem-wk-wk π i) ⟩
  sub-mem (sub-ex θ V) (wk-mem (wk-wk π) i)  ∎

cosub-mem-pre : (φ : CoSub Γ Δ Δ') (π : Δ' ⊇ Ψ) (i : Ψ ∋ A) -> cosub-mem (cosub-pre φ π) i ≡ cosub-mem φ (wk-mem π i)
cosub-mem-pre (cosub-ex φ K) (wk-cong π) here     = refl
cosub-mem-pre (cosub-ex φ K) (wk-cong π) (there i) = cosub-mem-pre φ π i
cosub-mem-pre (cosub-ex φ K) (wk-wk π) i = begin
  cosub-mem (cosub-pre φ π) i               ≡⟨ cosub-mem-pre φ π i ⟩
  cosub-mem φ (wk-mem π i)                  ≡˘⟨ cong (λ j -> cosub-mem (cosub-ex φ K) j) (wk-mem-wk-wk π i) ⟩
  cosub-mem (cosub-ex φ K) (wk-mem (wk-wk π) i)  ∎

sub-pre-wk-l : (ρ : Γ₁ ⊇ Γ) (σ : Δ₁ ⊇ Δ) (θ : Sub Γ Δ Γ') (π : Γ' ⊇ Ψ) -> sub-pre (sub-wk ρ σ θ) π ≡ sub-wk ρ σ (sub-pre θ π)
sub-pre-wk-l ρ σ θ wk-ε              = refl
sub-pre-wk-l ρ σ (sub-ex θ V) (wk-cong π) = cong₂ sub-ex (sub-pre-wk-l ρ σ θ π) refl
sub-pre-wk-l ρ σ (sub-ex θ V) (wk-wk π)   = sub-pre-wk-l ρ σ θ π

cosub-pre-wk-l : (ρ : Γ₁ ⊇ Γ) (σ : Δ₁ ⊇ Δ) (φ : CoSub Γ Δ Δ') (π : Δ' ⊇ Ψ) -> cosub-pre (cosub-wk ρ σ φ) π ≡ cosub-wk ρ σ (cosub-pre φ π)
cosub-pre-wk-l ρ σ φ wk-ε                  = refl
cosub-pre-wk-l ρ σ (cosub-ex φ K) (wk-cong π) = cong₂ cosub-ex (cosub-pre-wk-l ρ σ φ π) refl
cosub-pre-wk-l ρ σ (cosub-ex φ K) (wk-wk π)   = cosub-pre-wk-l ρ σ φ π

sub-pre-wk-id : (θ : Sub Γ Δ Γ') -> sub-pre θ (wk-id {Γ'}) ≡ θ
sub-pre-wk-id sub-ε        = refl
sub-pre-wk-id (sub-ex θ V) = cong (λ W -> sub-ex W V) (sub-pre-wk-id θ)

cosub-pre-wk-id : (φ : CoSub Γ Δ Δ') -> cosub-pre φ (wk-id {Δ'}) ≡ φ
cosub-pre-wk-id cosub-ε        = refl
cosub-pre-wk-id (cosub-ex φ K) = cong (λ W -> cosub-ex W K) (cosub-pre-wk-id φ)

--------------------------------------------------------------------------
-- substitution after weakening

mutual
  sub-val-wk-pre : (θ : Sub Ψ Ψ' Γ) (φ : CoSub Ψ Ψ' Δ) (ρ : Γ ⊇ Γ') (σ : Δ ⊇ Δ') (V : Γ' ⊢ᵛ A ∣ Δ')
                 -> sub-val θ φ (wk-val ρ σ V) ≡ sub-val (sub-pre θ ρ) (cosub-pre φ σ) V
  sub-val-wk-pre θ φ ρ σ (var i) = sym (sub-mem-pre θ ρ i)
  sub-val-wk-pre θ φ ρ σ (lam M) =
    cong lam (begin
      sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) (wk-tm (wk-cong ρ) σ M)
        ≡⟨ sub-tm-wk-pre (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) (wk-cong ρ) σ M ⟩
      sub-tm (sub-ex (sub-pre (sub-wk (wk-wk wk-id) wk-id θ) ρ) (var here)) (cosub-pre (cosub-wk (wk-wk wk-id) wk-id φ) σ) M
        ≡⟨ cong₂ (λ x y -> sub-tm (sub-ex x (var here)) y M) (sub-pre-wk-l (wk-wk wk-id) wk-id θ ρ) (cosub-pre-wk-l (wk-wk wk-id) wk-id φ σ) ⟩
      sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-pre θ ρ)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-pre φ σ)) M  ∎)
  sub-val-wk-pre θ φ ρ σ unit       = refl
  sub-val-wk-pre θ φ ρ σ (pair V W) = cong₂ pair (sub-val-wk-pre θ φ ρ σ V) (sub-val-wk-pre θ φ ρ σ W)
  sub-val-wk-pre θ φ ρ σ (inl V)    = cong inl (sub-val-wk-pre θ φ ρ σ V)
  sub-val-wk-pre θ φ ρ σ (inr W)    = cong inr (sub-val-wk-pre θ φ ρ σ W)

  sub-tm-wk-pre : (θ : Sub Ψ Ψ' Γ) (φ : CoSub Ψ Ψ' Δ) (ρ : Γ ⊇ Γ') (σ : Δ ⊇ Δ') (M : Γ' ⊢ᵗ A ∣ Δ')
                -> sub-tm θ φ (wk-tm ρ σ M) ≡ sub-tm (sub-pre θ ρ) (cosub-pre φ σ) M
  sub-tm-wk-pre θ φ ρ σ (ret V) = cong ret (sub-val-wk-pre θ φ ρ σ V)
  sub-tm-wk-pre θ φ ρ σ (μ M') =
    cong μ (begin
      sub-cmd (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) (wk-cmd ρ (wk-cong σ) M')
        ≡⟨ sub-cmd-wk-pre (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) ρ (wk-cong σ) M' ⟩
      sub-cmd (sub-pre (sub-wk wk-id (wk-wk wk-id) θ) ρ) (cosub-ex (cosub-pre (cosub-wk wk-id (wk-wk wk-id) φ) σ) (covar here)) M'
        ≡⟨ cong₂ (λ x y -> sub-cmd x (cosub-ex y (covar here)) M') (sub-pre-wk-l wk-id (wk-wk wk-id) θ ρ) (cosub-pre-wk-l wk-id (wk-wk wk-id) φ σ) ⟩
      sub-cmd (sub-wk wk-id (wk-wk wk-id) (sub-pre θ ρ)) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) (cosub-pre φ σ)) (covar here)) M'  ∎)

  sub-cotm-wk-pre : (θ : Sub Ψ Ψ' Γ) (φ : CoSub Ψ Ψ' Δ) (ρ : Γ ⊇ Γ') (σ : Δ ⊇ Δ') (K : Γ' ∣ A ⊢ᵏ Δ')
                 -> sub-cotm θ φ (wk-cotm ρ σ K) ≡ sub-cotm (sub-pre θ ρ) (cosub-pre φ σ) K
  sub-cotm-wk-pre θ φ ρ σ (covar i) = sym (cosub-mem-pre φ σ i)
  sub-cotm-wk-pre θ φ ρ σ (app V K) = cong₂ app (sub-val-wk-pre θ φ ρ σ V) (sub-cotm-wk-pre θ φ ρ σ K)
  sub-cotm-wk-pre θ φ ρ σ (fst K)   = cong fst (sub-cotm-wk-pre θ φ ρ σ K)
  sub-cotm-wk-pre θ φ ρ σ (snd K)   = cong snd (sub-cotm-wk-pre θ φ ρ σ K)
  sub-cotm-wk-pre θ φ ρ σ (case K1 K2) = cong₂ case (sub-cotm-wk-pre θ φ ρ σ K1) (sub-cotm-wk-pre θ φ ρ σ K2)
  sub-cotm-wk-pre θ φ ρ σ (μ̃ M') =
    cong μ̃ (begin
      sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) (wk-cmd (wk-cong ρ) σ M')
        ≡⟨ sub-cmd-wk-pre (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) (wk-cong ρ) σ M' ⟩
      sub-cmd (sub-ex (sub-pre (sub-wk (wk-wk wk-id) wk-id θ) ρ) (var here)) (cosub-pre (cosub-wk (wk-wk wk-id) wk-id φ) σ) M'
        ≡⟨ cong₂ (λ x y -> sub-cmd (sub-ex x (var here)) y M') (sub-pre-wk-l (wk-wk wk-id) wk-id θ ρ) (cosub-pre-wk-l (wk-wk wk-id) wk-id φ σ) ⟩
      sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-pre θ ρ)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-pre φ σ)) M'  ∎)
  sub-cotm-wk-pre θ φ ρ σ tp = refl

  sub-cmd-wk-pre : (θ : Sub Ψ Ψ' Γ) (φ : CoSub Ψ Ψ' Δ) (ρ : Γ ⊇ Γ') (σ : Δ ⊇ Δ') (M' : Γ' ⊢ Δ')
                 -> sub-cmd θ φ (wk-cmd ρ σ M') ≡ sub-cmd (sub-pre θ ρ) (cosub-pre φ σ) M'
  sub-cmd-wk-pre θ φ ρ σ (cut A M K) = cong₂ (cut A) (sub-tm-wk-pre θ φ ρ σ M) (sub-cotm-wk-pre θ φ ρ σ K)

--------------------------------------------------------------------------
-- substitution composition

sub-comp-sub : Sub Γ Δ Γ' -> CoSub Γ Δ Δ' -> Sub Γ' Δ' Ψ -> Sub Γ Δ Ψ
sub-comp-sub θ1 φ1 sub-ε         = sub-ε
sub-comp-sub θ1 φ1 (sub-ex θ2 V) = sub-ex (sub-comp-sub θ1 φ1 θ2) (sub-val θ1 φ1 V)

cosub-comp-sub : Sub Γ Δ Γ' -> CoSub Γ Δ Δ' -> CoSub Γ' Δ' Ψ -> CoSub Γ Δ Ψ
cosub-comp-sub θ1 φ1 cosub-ε         = cosub-ε
cosub-comp-sub θ1 φ1 (cosub-ex φ2 K) = cosub-ex (cosub-comp-sub θ1 φ1 φ2) (sub-cotm θ1 φ1 K)

sub-mem-comp-sub : (θ1 : Sub Γ Δ Γ') (φ1 : CoSub Γ Δ Δ') (θ2 : Sub Γ' Δ' Ψ) (i : Ψ ∋ A)
                  -> sub-mem (sub-comp-sub θ1 φ1 θ2) i ≡ sub-val θ1 φ1 (sub-mem θ2 i)
sub-mem-comp-sub θ1 φ1 (sub-ex θ2 V) here     = refl
sub-mem-comp-sub θ1 φ1 (sub-ex θ2 V) (there i) = sub-mem-comp-sub θ1 φ1 θ2 i

cosub-mem-comp-sub : (θ1 : Sub Γ Δ Γ') (φ1 : CoSub Γ Δ Δ') (φ2 : CoSub Γ' Δ' Ψ) (i : Ψ ∋ A)
                    -> cosub-mem (cosub-comp-sub θ1 φ1 φ2) i ≡ sub-cotm θ1 φ1 (cosub-mem φ2 i)
cosub-mem-comp-sub θ1 φ1 (cosub-ex φ2 K) here     = refl
cosub-mem-comp-sub θ1 φ1 (cosub-ex φ2 K) (there i) = cosub-mem-comp-sub θ1 φ1 φ2 i

sub-comp-sub-wk-r : (θ1 : Sub Γ Δ Γ') (φ1 : CoSub Γ Δ Δ') (ρ : Γ' ⊇ Γ'') (σ : Δ' ⊇ Δ'') (θ2 : Sub Γ'' Δ'' Ψ)
                   -> sub-comp-sub θ1 φ1 (sub-wk ρ σ θ2) ≡ sub-comp-sub (sub-pre θ1 ρ) (cosub-pre φ1 σ) θ2
sub-comp-sub-wk-r θ1 φ1 ρ σ sub-ε         = refl
sub-comp-sub-wk-r θ1 φ1 ρ σ (sub-ex θ2 V) = cong₂ sub-ex (sub-comp-sub-wk-r θ1 φ1 ρ σ θ2) (sub-val-wk-pre θ1 φ1 ρ σ V)

cosub-comp-sub-wk-r : (θ1 : Sub Γ Δ Γ') (φ1 : CoSub Γ Δ Δ') (ρ : Γ' ⊇ Γ'') (σ : Δ' ⊇ Δ'') (φ2 : CoSub Γ'' Δ'' Ψ)
                     -> cosub-comp-sub θ1 φ1 (cosub-wk ρ σ φ2) ≡ cosub-comp-sub (sub-pre θ1 ρ) (cosub-pre φ1 σ) φ2
cosub-comp-sub-wk-r θ1 φ1 ρ σ cosub-ε         = refl
cosub-comp-sub-wk-r θ1 φ1 ρ σ (cosub-ex φ2 K) = cong₂ cosub-ex (cosub-comp-sub-wk-r θ1 φ1 ρ σ φ2) (sub-cotm-wk-pre θ1 φ1 ρ σ K)

sub-comp-sub-wk-l : (ρ : Γ₁ ⊇ Γ) (σ : Δ₁ ⊇ Δ) (θ1 : Sub Γ Δ Γ') (φ1 : CoSub Γ Δ Δ') (θ2 : Sub Γ' Δ' Ψ)
                   -> sub-comp-sub (sub-wk ρ σ θ1) (cosub-wk ρ σ φ1) θ2 ≡ sub-wk ρ σ (sub-comp-sub θ1 φ1 θ2)
sub-comp-sub-wk-l ρ σ θ1 φ1 sub-ε         = refl
sub-comp-sub-wk-l ρ σ θ1 φ1 (sub-ex θ2 V) =
  cong₂ sub-ex (sub-comp-sub-wk-l ρ σ θ1 φ1 θ2) (sym (wk-sub-val ρ σ θ1 φ1 V))

cosub-comp-sub-wk-l : (ρ : Γ₁ ⊇ Γ) (σ : Δ₁ ⊇ Δ) (θ1 : Sub Γ Δ Γ') (φ1 : CoSub Γ Δ Δ') (φ2 : CoSub Γ' Δ' Ψ)
                     -> cosub-comp-sub (sub-wk ρ σ θ1) (cosub-wk ρ σ φ1) φ2 ≡ cosub-wk ρ σ (cosub-comp-sub θ1 φ1 φ2)
cosub-comp-sub-wk-l ρ σ θ1 φ1 cosub-ε         = refl
cosub-comp-sub-wk-l ρ σ θ1 φ1 (cosub-ex φ2 K) =
  cong₂ cosub-ex (cosub-comp-sub-wk-l ρ σ θ1 φ1 φ2) (sym (wk-sub-cotm ρ σ θ1 φ1 K))

-- pushing a fresh-variable lift through composition, on either the Γ or Δ side
sub-comp-sub-ext-Γ : (θ1 : Sub Γ Δ Γ') (φ1 : CoSub Γ Δ Δ') (θ2 : Sub Γ' Δ' Ψ)
                   -> sub-comp-sub (sub-ex (sub-wk (wk-wk {A = A} wk-id) wk-id θ1) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ1) (sub-ex (sub-wk (wk-wk wk-id) wk-id θ2) (var here))
                    ≡ sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-comp-sub θ1 φ1 θ2)) (var here)
sub-comp-sub-ext-Γ θ1 φ1 θ2 =
  cong₂ sub-ex
    (begin
      sub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) wk-id θ1) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ1) (sub-wk (wk-wk wk-id) wk-id θ2)
        ≡⟨ sub-comp-sub-wk-r (sub-ex (sub-wk (wk-wk wk-id) wk-id θ1) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ1) (wk-wk wk-id) wk-id θ2 ⟩
      sub-comp-sub (sub-pre (sub-wk (wk-wk wk-id) wk-id θ1) wk-id) (cosub-pre (cosub-wk (wk-wk wk-id) wk-id φ1) wk-id) θ2
        ≡⟨ cong₂ (λ x y -> sub-comp-sub x y θ2) (sub-pre-wk-id (sub-wk (wk-wk wk-id) wk-id θ1)) (cosub-pre-wk-id (cosub-wk (wk-wk wk-id) wk-id φ1)) ⟩
      sub-comp-sub (sub-wk (wk-wk wk-id) wk-id θ1) (cosub-wk (wk-wk wk-id) wk-id φ1) θ2
        ≡⟨ sub-comp-sub-wk-l (wk-wk wk-id) wk-id θ1 φ1 θ2 ⟩
      sub-wk (wk-wk wk-id) wk-id (sub-comp-sub θ1 φ1 θ2)  ∎)
    refl

cosub-comp-sub-ext-Γ : (θ1 : Sub Γ Δ Γ') (φ1 : CoSub Γ Δ Δ') (φ2 : CoSub Γ' Δ' Ψ)
                      -> cosub-comp-sub (sub-ex (sub-wk (wk-wk {A = A} wk-id) wk-id θ1) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ1) (cosub-wk (wk-wk wk-id) wk-id φ2)
                       ≡ cosub-wk (wk-wk wk-id) wk-id (cosub-comp-sub θ1 φ1 φ2)
cosub-comp-sub-ext-Γ θ1 φ1 φ2 = begin
  cosub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) wk-id θ1) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ1) (cosub-wk (wk-wk wk-id) wk-id φ2)
    ≡⟨ cosub-comp-sub-wk-r (sub-ex (sub-wk (wk-wk wk-id) wk-id θ1) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ1) (wk-wk wk-id) wk-id φ2 ⟩
  cosub-comp-sub (sub-pre (sub-wk (wk-wk wk-id) wk-id θ1) wk-id) (cosub-pre (cosub-wk (wk-wk wk-id) wk-id φ1) wk-id) φ2
    ≡⟨ cong₂ (λ x y -> cosub-comp-sub x y φ2) (sub-pre-wk-id (sub-wk (wk-wk wk-id) wk-id θ1)) (cosub-pre-wk-id (cosub-wk (wk-wk wk-id) wk-id φ1)) ⟩
  cosub-comp-sub (sub-wk (wk-wk wk-id) wk-id θ1) (cosub-wk (wk-wk wk-id) wk-id φ1) φ2
    ≡⟨ cosub-comp-sub-wk-l (wk-wk wk-id) wk-id θ1 φ1 φ2 ⟩
  cosub-wk (wk-wk wk-id) wk-id (cosub-comp-sub θ1 φ1 φ2)  ∎

sub-comp-sub-ext-Δ : (θ1 : Sub Γ Δ Γ') (φ1 : CoSub Γ Δ Δ') (θ2 : Sub Γ' Δ' Ψ)
                   -> sub-comp-sub (sub-wk wk-id (wk-wk {A = A} wk-id) θ1) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ1) (covar here)) (sub-wk wk-id (wk-wk wk-id) θ2)
                    ≡ sub-wk wk-id (wk-wk wk-id) (sub-comp-sub θ1 φ1 θ2)
sub-comp-sub-ext-Δ θ1 φ1 θ2 = begin
  sub-comp-sub (sub-wk wk-id (wk-wk wk-id) θ1) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ1) (covar here)) (sub-wk wk-id (wk-wk wk-id) θ2)
    ≡⟨ sub-comp-sub-wk-r (sub-wk wk-id (wk-wk wk-id) θ1) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ1) (covar here)) wk-id (wk-wk wk-id) θ2 ⟩
  sub-comp-sub (sub-pre (sub-wk wk-id (wk-wk wk-id) θ1) wk-id) (cosub-pre (cosub-wk wk-id (wk-wk wk-id) φ1) wk-id) θ2
    ≡⟨ cong₂ (λ x y -> sub-comp-sub x y θ2) (sub-pre-wk-id (sub-wk wk-id (wk-wk wk-id) θ1)) (cosub-pre-wk-id (cosub-wk wk-id (wk-wk wk-id) φ1)) ⟩
  sub-comp-sub (sub-wk wk-id (wk-wk wk-id) θ1) (cosub-wk wk-id (wk-wk wk-id) φ1) θ2
    ≡⟨ sub-comp-sub-wk-l wk-id (wk-wk wk-id) θ1 φ1 θ2 ⟩
  sub-wk wk-id (wk-wk wk-id) (sub-comp-sub θ1 φ1 θ2)  ∎

cosub-comp-sub-ext-Δ : (θ1 : Sub Γ Δ Γ') (φ1 : CoSub Γ Δ Δ') (φ2 : CoSub Γ' Δ' Ψ)
                      -> cosub-comp-sub (sub-wk wk-id (wk-wk {A = A} wk-id) θ1) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ1) (covar here)) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ2) (covar here))
                       ≡ cosub-ex (cosub-wk wk-id (wk-wk wk-id) (cosub-comp-sub θ1 φ1 φ2)) (covar here)
cosub-comp-sub-ext-Δ θ1 φ1 φ2 =
  cong₂ cosub-ex
    (begin
      cosub-comp-sub (sub-wk wk-id (wk-wk wk-id) θ1) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ1) (covar here)) (cosub-wk wk-id (wk-wk wk-id) φ2)
        ≡⟨ cosub-comp-sub-wk-r (sub-wk wk-id (wk-wk wk-id) θ1) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ1) (covar here)) wk-id (wk-wk wk-id) φ2 ⟩
      cosub-comp-sub (sub-pre (sub-wk wk-id (wk-wk wk-id) θ1) wk-id) (cosub-pre (cosub-wk wk-id (wk-wk wk-id) φ1) wk-id) φ2
        ≡⟨ cong₂ (λ x y -> cosub-comp-sub x y φ2) (sub-pre-wk-id (sub-wk wk-id (wk-wk wk-id) θ1)) (cosub-pre-wk-id (cosub-wk wk-id (wk-wk wk-id) φ1)) ⟩
      cosub-comp-sub (sub-wk wk-id (wk-wk wk-id) θ1) (cosub-wk wk-id (wk-wk wk-id) φ1) φ2
        ≡⟨ cosub-comp-sub-wk-l wk-id (wk-wk wk-id) θ1 φ1 φ2 ⟩
      cosub-wk wk-id (wk-wk wk-id) (cosub-comp-sub θ1 φ1 φ2)  ∎)
    refl

mutual
  sub-sub-cmd : (θ1 : Sub Γ Δ Γ') (φ1 : CoSub Γ Δ Δ') (θ2 : Sub Γ' Δ' Ψ) (φ2 : CoSub Γ' Δ' Ψ') (M' : Ψ ⊢ Ψ')
              -> sub-cmd θ1 φ1 (sub-cmd θ2 φ2 M') ≡ sub-cmd (sub-comp-sub θ1 φ1 θ2) (cosub-comp-sub θ1 φ1 φ2) M'
  sub-sub-cmd θ1 φ1 θ2 φ2 (cut A M K) = cong₂ (cut A) (sub-sub-tm θ1 φ1 θ2 φ2 M) (sub-sub-cotm θ1 φ1 θ2 φ2 K)

  sub-sub-val : (θ1 : Sub Γ Δ Γ') (φ1 : CoSub Γ Δ Δ') (θ2 : Sub Γ' Δ' Ψ) (φ2 : CoSub Γ' Δ' Ψ') (V : Ψ ⊢ᵛ A ∣ Ψ')
              -> sub-val θ1 φ1 (sub-val θ2 φ2 V) ≡ sub-val (sub-comp-sub θ1 φ1 θ2) (cosub-comp-sub θ1 φ1 φ2) V
  sub-sub-val θ1 φ1 θ2 φ2 (var i) = sym (sub-mem-comp-sub θ1 φ1 θ2 i)
  sub-sub-val θ1 φ1 θ2 φ2 (lam M) =
    cong lam (begin
      sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ1) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ1)
              (sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ2) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ2) M)
        ≡⟨ sub-sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ1) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ1)
                      (sub-ex (sub-wk (wk-wk wk-id) wk-id θ2) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ2) M ⟩
      sub-tm (sub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) wk-id θ1) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ1) (sub-ex (sub-wk (wk-wk wk-id) wk-id θ2) (var here)))
             (cosub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) wk-id θ1) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ1) (cosub-wk (wk-wk wk-id) wk-id φ2)) M
        ≡⟨ cong₂ (λ x y -> sub-tm x y M) (sub-comp-sub-ext-Γ θ1 φ1 θ2) (cosub-comp-sub-ext-Γ θ1 φ1 φ2) ⟩
      sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-comp-sub θ1 φ1 θ2)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-comp-sub θ1 φ1 φ2)) M  ∎)
  sub-sub-val θ1 φ1 θ2 φ2 unit       = refl
  sub-sub-val θ1 φ1 θ2 φ2 (pair V W) = cong₂ pair (sub-sub-val θ1 φ1 θ2 φ2 V) (sub-sub-val θ1 φ1 θ2 φ2 W)
  sub-sub-val θ1 φ1 θ2 φ2 (inl V)    = cong inl (sub-sub-val θ1 φ1 θ2 φ2 V)
  sub-sub-val θ1 φ1 θ2 φ2 (inr W)    = cong inr (sub-sub-val θ1 φ1 θ2 φ2 W)

  sub-sub-tm : (θ1 : Sub Γ Δ Γ') (φ1 : CoSub Γ Δ Δ') (θ2 : Sub Γ' Δ' Ψ) (φ2 : CoSub Γ' Δ' Ψ') (M : Ψ ⊢ᵗ A ∣ Ψ')
             -> sub-tm θ1 φ1 (sub-tm θ2 φ2 M) ≡ sub-tm (sub-comp-sub θ1 φ1 θ2) (cosub-comp-sub θ1 φ1 φ2) M
  sub-sub-tm θ1 φ1 θ2 φ2 (ret V) = cong ret (sub-sub-val θ1 φ1 θ2 φ2 V)
  sub-sub-tm θ1 φ1 θ2 φ2 (μ M') =
    cong μ (begin
      sub-cmd (sub-wk wk-id (wk-wk wk-id) θ1) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ1) (covar here))
              (sub-cmd (sub-wk wk-id (wk-wk wk-id) θ2) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ2) (covar here)) M')
        ≡⟨ sub-sub-cmd (sub-wk wk-id (wk-wk wk-id) θ1) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ1) (covar here))
                       (sub-wk wk-id (wk-wk wk-id) θ2) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ2) (covar here)) M' ⟩
      sub-cmd (sub-comp-sub (sub-wk wk-id (wk-wk wk-id) θ1) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ1) (covar here)) (sub-wk wk-id (wk-wk wk-id) θ2))
              (cosub-comp-sub (sub-wk wk-id (wk-wk wk-id) θ1) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ1) (covar here)) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ2) (covar here))) M'
        ≡⟨ cong₂ (λ x y -> sub-cmd x y M') (sub-comp-sub-ext-Δ θ1 φ1 θ2) (cosub-comp-sub-ext-Δ θ1 φ1 φ2) ⟩
      sub-cmd (sub-wk wk-id (wk-wk wk-id) (sub-comp-sub θ1 φ1 θ2)) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) (cosub-comp-sub θ1 φ1 φ2)) (covar here)) M'  ∎)

  sub-sub-cotm : (θ1 : Sub Γ Δ Γ') (φ1 : CoSub Γ Δ Δ') (θ2 : Sub Γ' Δ' Ψ) (φ2 : CoSub Γ' Δ' Ψ') (K : Ψ ∣ A ⊢ᵏ Ψ')
              -> sub-cotm θ1 φ1 (sub-cotm θ2 φ2 K) ≡ sub-cotm (sub-comp-sub θ1 φ1 θ2) (cosub-comp-sub θ1 φ1 φ2) K
  sub-sub-cotm θ1 φ1 θ2 φ2 (covar i)    = sym (cosub-mem-comp-sub θ1 φ1 φ2 i)
  sub-sub-cotm θ1 φ1 θ2 φ2 (app V K)    = cong₂ app (sub-sub-val θ1 φ1 θ2 φ2 V) (sub-sub-cotm θ1 φ1 θ2 φ2 K)
  sub-sub-cotm θ1 φ1 θ2 φ2 (fst K)      = cong fst (sub-sub-cotm θ1 φ1 θ2 φ2 K)
  sub-sub-cotm θ1 φ1 θ2 φ2 (snd K)      = cong snd (sub-sub-cotm θ1 φ1 θ2 φ2 K)
  sub-sub-cotm θ1 φ1 θ2 φ2 (case K1 K2) = cong₂ case (sub-sub-cotm θ1 φ1 θ2 φ2 K1) (sub-sub-cotm θ1 φ1 θ2 φ2 K2)
  sub-sub-cotm θ1 φ1 θ2 φ2 (μ̃ M') =
    cong μ̃ (begin
      sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ1) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ1)
              (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ2) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ2) M')
        ≡⟨ sub-sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ1) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ1)
                       (sub-ex (sub-wk (wk-wk wk-id) wk-id θ2) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ2) M' ⟩
      sub-cmd (sub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) wk-id θ1) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ1) (sub-ex (sub-wk (wk-wk wk-id) wk-id θ2) (var here)))
              (cosub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) wk-id θ1) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ1) (cosub-wk (wk-wk wk-id) wk-id φ2)) M'
        ≡⟨ cong₂ (λ x y -> sub-cmd x y M') (sub-comp-sub-ext-Γ θ1 φ1 θ2) (cosub-comp-sub-ext-Γ θ1 φ1 φ2) ⟩
      sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-comp-sub θ1 φ1 θ2)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-comp-sub θ1 φ1 φ2)) M'  ∎)
  sub-sub-cotm θ1 φ1 θ2 φ2 tp = refl

sub-comp-sub-idl : (θ : Sub Γ Δ Γ') -> sub-comp-sub (sub-id {Γ} {Δ}) (cosub-id {Γ} {Δ}) θ ≡ θ
sub-comp-sub-idl sub-ε        = refl
sub-comp-sub-idl (sub-ex θ V) = cong₂ sub-ex (sub-comp-sub-idl θ) (sub-val-id V)

cosub-comp-sub-idl : (φ : CoSub Γ Δ Δ') -> cosub-comp-sub (sub-id {Γ} {Δ}) (cosub-id {Γ} {Δ}) φ ≡ φ
cosub-comp-sub-idl cosub-ε        = refl
cosub-comp-sub-idl (cosub-ex φ K) = cong₂ cosub-ex (cosub-comp-sub-idl φ) (sub-cotm-id K)

--------------------------------------------------------------------------
-- lemmas for fundamental lemma

fund-lam-eq : (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ') (π : Γ₁ ⊇ Γ) (σ : Δ₁ ⊇ Δ) (W : Γ₁ ⊢ᵛ A ∣ Δ₁) (M : (Γ' ∙ A) ⊢ᵗ B ∣ Δ')
  -> sub-tm (sub-ex sub-id W) cosub-id (wk-tm (wk-cong π) σ (sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M))
   ≡ sub-tm (sub-ex (sub-wk π σ θ) W) (cosub-wk π σ φ) M
fund-lam-eq θ φ π σ W M = begin
  sub-tm (sub-ex sub-id W) cosub-id (wk-tm (wk-cong π) σ (sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M))
    ≡⟨ cong (sub-tm (sub-ex sub-id W) cosub-id) (begin
         wk-tm (wk-cong π) σ (sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M)
           ≡⟨ wk-sub-tm (wk-cong π) σ (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M ⟩
         sub-tm (sub-ex (sub-wk (wk-cong π) σ (sub-wk (wk-wk wk-id) wk-id θ)) (var here)) (cosub-wk (wk-cong π) σ (cosub-wk (wk-wk wk-id) wk-id φ)) M
           ≡⟨ cong₂ (λ x y -> sub-tm (sub-ex x (var here)) y M) (sub-wk-cong-lemma π σ θ) (cosub-wk-cong-lemma π σ φ) ⟩
         sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-wk π σ θ)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-wk π σ φ)) M  ∎) ⟩
  sub-tm (sub-ex sub-id W) cosub-id (sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-wk π σ θ)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-wk π σ φ)) M)
    ≡⟨ sub-sub-tm (sub-ex sub-id W) cosub-id (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-wk π σ θ)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-wk π σ φ)) M ⟩
  sub-tm (sub-comp-sub (sub-ex sub-id W) cosub-id (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-wk π σ θ)) (var here)))
         (cosub-comp-sub (sub-ex sub-id W) cosub-id (cosub-wk (wk-wk wk-id) wk-id (cosub-wk π σ φ))) M
    ≡⟨ cong₂ (λ x y -> sub-tm x y M)
             (cong₂ sub-ex
               (begin
                 sub-comp-sub (sub-ex sub-id W) cosub-id (sub-wk (wk-wk wk-id) wk-id (sub-wk π σ θ))
                   ≡⟨ sub-comp-sub-wk-r (sub-ex sub-id W) cosub-id (wk-wk wk-id) wk-id (sub-wk π σ θ) ⟩
                 sub-comp-sub (sub-pre (sub-ex sub-id W) (wk-wk wk-id)) (cosub-pre cosub-id wk-id) (sub-wk π σ θ)
                   ≡⟨ cong₂ (λ x y -> sub-comp-sub x y (sub-wk π σ θ)) (sub-pre-wk-id sub-id) (cosub-pre-wk-id cosub-id) ⟩
                 sub-comp-sub sub-id cosub-id (sub-wk π σ θ)
                   ≡⟨ sub-comp-sub-idl (sub-wk π σ θ) ⟩
                 sub-wk π σ θ  ∎)
               refl)
             (begin
               cosub-comp-sub (sub-ex sub-id W) cosub-id (cosub-wk (wk-wk wk-id) wk-id (cosub-wk π σ φ))
                 ≡⟨ cosub-comp-sub-wk-r (sub-ex sub-id W) cosub-id (wk-wk wk-id) wk-id (cosub-wk π σ φ) ⟩
               cosub-comp-sub (sub-pre (sub-ex sub-id W) (wk-wk wk-id)) (cosub-pre cosub-id wk-id) (cosub-wk π σ φ)
                 ≡⟨ cong₂ (λ x y -> cosub-comp-sub x y (cosub-wk π σ φ)) (sub-pre-wk-id sub-id) (cosub-pre-wk-id cosub-id) ⟩
               cosub-comp-sub sub-id cosub-id (cosub-wk π σ φ)
                 ≡⟨ cosub-comp-sub-idl (cosub-wk π σ φ) ⟩
               cosub-wk π σ φ  ∎) ⟩
  sub-tm (sub-ex (sub-wk π σ θ) W) (cosub-wk π σ φ) M  ∎

fund-mu-eq : (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ') (K : Γ ∣ A ⊢ᵏ Δ) (M' : Γ' ⊢ (Δ' ∙ A))
  -> sub-cmd sub-id (cosub-ex cosub-id K) (sub-cmd (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) M')
   ≡ sub-cmd θ (cosub-ex φ K) M'
fund-mu-eq θ φ K M' = begin
  sub-cmd sub-id (cosub-ex cosub-id K) (sub-cmd (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) M')
    ≡⟨ sub-sub-cmd sub-id (cosub-ex cosub-id K) (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) M' ⟩
  sub-cmd (sub-comp-sub sub-id (cosub-ex cosub-id K) (sub-wk wk-id (wk-wk wk-id) θ))
          (cosub-comp-sub sub-id (cosub-ex cosub-id K) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here))) M'
    ≡⟨ cong₂ (λ x y -> sub-cmd x y M')
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
  sub-cmd θ (cosub-ex φ K) M'  ∎

fund-mut-eq : (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ') (V : Γ ⊢ᵛ A ∣ Δ) (M' : (Γ' ∙ A) ⊢ Δ')
  -> sub-cmd (sub-ex sub-id V) cosub-id (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M')
   ≡ sub-cmd (sub-ex θ V) φ M'
fund-mut-eq θ φ V M' = begin
  sub-cmd (sub-ex sub-id V) cosub-id (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M')
    ≡⟨ sub-sub-cmd (sub-ex sub-id V) cosub-id (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M' ⟩
  sub-cmd (sub-comp-sub (sub-ex sub-id V) cosub-id (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)))
          (cosub-comp-sub (sub-ex sub-id V) cosub-id (cosub-wk (wk-wk wk-id) wk-id φ)) M'
    ≡⟨ cong₂ (λ x y -> sub-cmd x y M')
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
  sub-cmd (sub-ex θ V) φ M'  ∎

fund-mut-wk-eq : (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ') (π : Γ₁ ⊇ Γ) (σ : Δ₁ ⊇ Δ) (V : Γ₁ ⊢ᵛ A ∣ Δ₁) (M' : (Γ' ∙ A) ⊢ Δ')
  -> sub-cmd (sub-ex sub-id V) cosub-id (wk-cmd (wk-cong π) σ (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M'))
   ≡ sub-cmd (sub-ex (sub-wk π σ θ) V) (cosub-wk π σ φ) M'
fund-mut-wk-eq θ φ π σ V M' = begin
  sub-cmd (sub-ex sub-id V) cosub-id (wk-cmd (wk-cong π) σ (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M'))
    ≡⟨ cong (sub-cmd (sub-ex sub-id V) cosub-id) (begin
         wk-cmd (wk-cong π) σ (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M')
           ≡⟨ wk-sub-cmd (wk-cong π) σ (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M' ⟩
         sub-cmd (sub-ex (sub-wk (wk-cong π) σ (sub-wk (wk-wk wk-id) wk-id θ)) (var here)) (cosub-wk (wk-cong π) σ (cosub-wk (wk-wk wk-id) wk-id φ)) M'
           ≡⟨ cong₂ (λ x y -> sub-cmd (sub-ex x (var here)) y M') (sub-wk-cong-lemma π σ θ) (cosub-wk-cong-lemma π σ φ) ⟩
         sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-wk π σ θ)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-wk π σ φ)) M'  ∎) ⟩
  sub-cmd (sub-ex sub-id V) cosub-id (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id (sub-wk π σ θ)) (var here)) (cosub-wk (wk-wk wk-id) wk-id (cosub-wk π σ φ)) M')
    ≡⟨ fund-mut-eq (sub-wk π σ θ) (cosub-wk π σ φ) V M' ⟩
  sub-cmd (sub-ex (sub-wk π σ θ) V) (cosub-wk π σ φ) M'  ∎
