module Inception.LamBarMuMuTilde.Syntax where

open import Data.Nat

infixr 25 _`⇒_

data Ty : Set where
  `⊥ `Unit : Ty
  _`×_ _`⇒_ _`+_ : Ty -> Ty -> Ty

infixr 30 ¬_
¬_ : Ty -> Ty
¬ A = A `⇒ `⊥

module Cx (Ty : Set) where

  infixl 15 _∙_
  infix 10 _∋_

  data Env : Set where
    ε : Env
    _∙_ : Env -> Ty -> Env

  private
    variable
      A B : Ty

  variable
      Γ Δ Ψ : Env

  data _∋_ : Env -> Ty -> Set where
    z :
      ---------
      Γ ∙ A ∋ A

    s : Γ ∋ A
      -------------
      -> Γ ∙ B ∋ A

open Cx Ty public

variable
  A B C : Ty

syntax Cmd Γ Δ = Γ ⊢ Δ

syntax Val Γ A Δ = Γ ⊢ᵛ A ∣ Δ

syntax Tm Γ A Δ = Γ ⊢ᵗ A ∣ Δ

syntax Ctx Γ A Δ = Γ ∣ A ⊢ᵉ Δ

data Cmd : Env -> Env -> Set

data Val : Env -> Ty -> Env -> Set

data Tm : Env -> Ty -> Env -> Set

data Ctx : Env -> Ty -> Env -> Set

data Cmd where

  cut : (A : Ty) -> (t : Γ ⊢ᵗ A ∣ Δ) -> (e : Γ ∣ A ⊢ᵉ Δ)
      ----------------------------------------------------
      -> Γ ⊢ Δ

data Val where

  var : (i : Γ ∋ A)
       ----------------
       -> Γ ⊢ᵛ A ∣ Δ

  lam : (t : (Γ ∙ A) ⊢ᵗ B ∣ Δ)
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

  ret : (v : Γ ⊢ᵛ A ∣ Δ)
      ---------------------
      -> Γ ⊢ᵗ A ∣ Δ

  μ : (c : Γ ⊢ (Δ ∙ A))
    ------------------------
    -> Γ ⊢ᵗ A ∣ Δ

data Ctx where

  covar : (i : Δ ∋ A)
        ---------------
        -> Γ ∣ A ⊢ᵉ Δ

  app : (v : Γ ⊢ᵛ A ∣ Δ) -> (e : Γ ∣ B ⊢ᵉ Δ)
      ---------------------------------------
      -> Γ ∣ A `⇒ B ⊢ᵉ Δ

  fst : (e : Γ ∣ A ⊢ᵉ Δ)
      -------------------
      -> Γ ∣ A `× B ⊢ᵉ Δ

  snd : (e : Γ ∣ B ⊢ᵉ Δ)
      -------------------
      -> Γ ∣ A `× B ⊢ᵉ Δ

  case : (e1 : Γ ∣ A ⊢ᵉ Δ) -> (e2 : Γ ∣ B ⊢ᵉ Δ)
       -------------------------------------------
       -> Γ ∣ A `+ B ⊢ᵉ Δ

  μ̃ : (c : (Γ ∙ A) ⊢ Δ)
    ------------------------
    -> Γ ∣ A ⊢ᵉ Δ

  tp : -------------
       Γ ∣ `⊥ ⊢ᵉ Δ

variable
  Γ' Δ' Γ₁ Δ₁ : Env

syntax Wk Γ Δ = Γ ⊇ Δ

data Wk : (Γ Δ : Env) -> Set where
  wk-ε : ε ⊇ ε
  wk-cong : (π : Wk Γ Δ) -> Wk (Γ ∙ A) (Δ ∙ A)
  wk-wk : (π : Wk Γ Δ) -> Wk (Γ ∙ A) Δ

wk-id : Wk Γ Γ
wk-id {Γ = ε} = wk-ε
wk-id {Γ = Γ ∙ A} = wk-cong wk-id

wk-mem : Wk Γ Δ -> Δ ∋ A -> Γ ∋ A
wk-mem (wk-cong π) z = z
wk-mem (wk-wk π) z = s (wk-mem π z)
wk-mem (wk-cong π) (s i) = s (wk-mem π i)
wk-mem (wk-wk π) (s i) = s (wk-mem π (s i))

mutual
  wk-cmd : Wk Γ Γ' -> Wk Δ Δ' -> Γ' ⊢ Δ' -> Γ ⊢ Δ
  wk-cmd ρ σ (cut A t e) = cut A (wk-tm ρ σ t) (wk-ctx ρ σ e)

  wk-val : Wk Γ Γ' -> Wk Δ Δ' -> Γ' ⊢ᵛ A ∣ Δ' -> Γ ⊢ᵛ A ∣ Δ
  wk-val ρ σ (var i)    = var (wk-mem ρ i)
  wk-val ρ σ (lam t)    = lam (wk-tm (wk-cong ρ) σ t)
  wk-val ρ σ unit       = unit
  wk-val ρ σ (pair v w) = pair (wk-val ρ σ v) (wk-val ρ σ w)
  wk-val ρ σ (inl v)    = inl (wk-val ρ σ v)
  wk-val ρ σ (inr w)    = inr (wk-val ρ σ w)

  wk-tm : Wk Γ Γ' -> Wk Δ Δ' -> Γ' ⊢ᵗ A ∣ Δ' -> Γ ⊢ᵗ A ∣ Δ
  wk-tm ρ σ (ret v) = ret (wk-val ρ σ v)
  wk-tm ρ σ (μ c)   = μ (wk-cmd ρ (wk-cong σ) c)

  wk-ctx : Wk Γ Γ' -> Wk Δ Δ' -> Γ' ∣ A ⊢ᵉ Δ' -> Γ ∣ A ⊢ᵉ Δ
  wk-ctx ρ σ (covar i) = covar (wk-mem σ i)
  wk-ctx ρ σ (app v e) = app (wk-val ρ σ v) (wk-ctx ρ σ e)
  wk-ctx ρ σ (fst e)   = fst (wk-ctx ρ σ e)
  wk-ctx ρ σ (snd e)   = snd (wk-ctx ρ σ e)
  wk-ctx ρ σ (case e1 e2) = case (wk-ctx ρ σ e1) (wk-ctx ρ σ e2)
  wk-ctx ρ σ (μ̃ c)     = μ̃ (wk-cmd (wk-cong ρ) σ c)
  wk-ctx ρ σ tp        = tp

wkᵛ : Γ ⊢ᵛ A ∣ Δ -> (Γ ∙ B) ⊢ᵛ A ∣ Δ
wkᵛ = wk-val (wk-wk wk-id) wk-id

wkᵗ : Γ ⊢ᵗ A ∣ Δ -> (Γ ∙ B) ⊢ᵗ A ∣ Δ
wkᵗ = wk-tm (wk-wk wk-id) wk-id

wkᵉ : Γ ∣ A ⊢ᵉ Δ -> (Γ ∙ B) ∣ A ⊢ᵉ Δ
wkᵉ = wk-ctx (wk-wk wk-id) wk-id

wk̃ᵛ : Γ ⊢ᵛ A ∣ Δ -> Γ ⊢ᵛ A ∣ (Δ ∙ B)
wk̃ᵛ = wk-val wk-id (wk-wk wk-id)

wk̃ᵗ : Γ ⊢ᵗ A ∣ Δ -> Γ ⊢ᵗ A ∣ (Δ ∙ B)
wk̃ᵗ = wk-tm wk-id (wk-wk wk-id)

wk̃ᵉ : Γ ∣ A ⊢ᵉ Δ -> Γ ∣ A ⊢ᵉ (Δ ∙ B)
wk̃ᵉ = wk-ctx wk-id (wk-wk wk-id)

wk-emp : Wk Γ ε
wk-emp {Γ = ε} = wk-ε
wk-emp {Γ = Γ ∙ A} = wk-wk wk-emp

data Sub (Γ Δ : Env) : (Γ' : Env) -> Set where
  sub-ε : Sub Γ Δ ε
  sub-ex : (θ : Sub Γ Δ Γ') -> (v : Γ ⊢ᵛ A ∣ Δ) -> Sub Γ Δ (Γ' ∙ A)

data CoSub (Γ Δ : Env) : (Δ' : Env) -> Set where
  cosub-ε : CoSub Γ Δ ε
  cosub-ex : (φ : CoSub Γ Δ Δ') -> (e : Γ ∣ A ⊢ᵉ Δ) -> CoSub Γ Δ (Δ' ∙ A)

sub-mem : Sub Γ Δ Γ' -> Γ' ∋ A -> Γ ⊢ᵛ A ∣ Δ
sub-mem (sub-ex θ v) z = v
sub-mem (sub-ex θ v) (s i) = sub-mem θ i

cosub-mem : CoSub Γ Δ Δ' -> Δ' ∋ A -> Γ ∣ A ⊢ᵉ Δ
cosub-mem (cosub-ex φ e) z = e
cosub-mem (cosub-ex φ e) (s i) = cosub-mem φ i

sub-wk : Wk Γ₁ Γ -> Wk Δ₁ Δ -> Sub Γ Δ Γ' -> Sub Γ₁ Δ₁ Γ'
sub-wk ρ σ sub-ε = sub-ε
sub-wk ρ σ (sub-ex θ v) = sub-ex (sub-wk ρ σ θ) (wk-val ρ σ v)

cosub-wk : Wk Γ₁ Γ -> Wk Δ₁ Δ -> CoSub Γ Δ Δ' -> CoSub Γ₁ Δ₁ Δ'
cosub-wk ρ σ cosub-ε = cosub-ε
cosub-wk ρ σ (cosub-ex φ e) = cosub-ex (cosub-wk ρ σ φ) (wk-ctx ρ σ e)

sub-id : Sub Γ Δ Γ
sub-id {Γ = ε} = sub-ε
sub-id {Γ = Γ ∙ A} = sub-ex (sub-wk (wk-wk wk-id) wk-id sub-id) (var z)

cosub-id : CoSub Γ Δ Δ
cosub-id {Δ = ε} = cosub-ε
cosub-id {Δ = Δ ∙ A} = cosub-ex (cosub-wk wk-id (wk-wk wk-id) cosub-id) (covar z)

mutual
  sub-cmd : Sub Γ Δ Γ' -> CoSub Γ Δ Δ' -> Γ' ⊢ Δ' -> Γ ⊢ Δ
  sub-cmd θ φ (cut A t e) = cut A (sub-tm θ φ t) (sub-ctx θ φ e)

  sub-val : Sub Γ Δ Γ' -> CoSub Γ Δ Δ' -> Γ' ⊢ᵛ A ∣ Δ' -> Γ ⊢ᵛ A ∣ Δ
  sub-val θ φ (var i)    = sub-mem θ i
  sub-val θ φ (lam t)    = lam (sub-tm (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var z)) (cosub-wk (wk-wk wk-id) wk-id φ) t)
  sub-val θ φ unit       = unit
  sub-val θ φ (pair v w) = pair (sub-val θ φ v) (sub-val θ φ w)
  sub-val θ φ (inl v)    = inl (sub-val θ φ v)
  sub-val θ φ (inr w)    = inr (sub-val θ φ w)

  sub-tm : Sub Γ Δ Γ' -> CoSub Γ Δ Δ' -> Γ' ⊢ᵗ A ∣ Δ' -> Γ ⊢ᵗ A ∣ Δ
  sub-tm θ φ (ret v) = ret (sub-val θ φ v)
  sub-tm θ φ (μ c)   = μ (sub-cmd (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar z)) c)

  sub-ctx : Sub Γ Δ Γ' -> CoSub Γ Δ Δ' -> Γ' ∣ A ⊢ᵉ Δ' -> Γ ∣ A ⊢ᵉ Δ
  sub-ctx θ φ (covar i) = cosub-mem φ i
  sub-ctx θ φ (app v e) = app (sub-val θ φ v) (sub-ctx θ φ e)
  sub-ctx θ φ (fst e)   = fst (sub-ctx θ φ e)
  sub-ctx θ φ (snd e)   = snd (sub-ctx θ φ e)
  sub-ctx θ φ (case e1 e2) = case (sub-ctx θ φ e1) (sub-ctx θ φ e2)
  sub-ctx θ φ (μ̃ c)     = μ̃ (sub-cmd (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var z)) (cosub-wk (wk-wk wk-id) wk-id φ) c)
  sub-ctx θ φ tp        = tp

-- syntactic sugar

letv : Γ ⊢ᵛ A ∣ Δ -> (Γ ∙ A) ⊢ᵗ B ∣ Δ -> Γ ⊢ᵗ B ∣ Δ
letv v t = sub-tm (sub-ex sub-id v) cosub-id t

lett : Γ ⊢ᵗ A ∣ Δ -> (Γ ∙ A) ⊢ᵗ B ∣ Δ -> Γ ⊢ᵗ B ∣ Δ
lett {A = A} {B = B} u t = μ (cut A (wk̃ᵗ u) (μ̃ (cut B (wk̃ᵗ t) (covar z))))

letc : Γ ∣ A ⊢ᵉ Δ -> Γ ⊢ (Δ ∙ A) -> Γ ⊢ Δ
letc e t = sub-cmd sub-id (cosub-ex cosub-id e) t

letvc : Γ ⊢ᵛ A ∣ Δ -> (Γ ∙ A) ⊢ Δ -> Γ ⊢ Δ
letvc v c = sub-cmd (sub-ex sub-id v) cosub-id c

variable
  v v1 v2 v3 w w1 w2 : Γ ⊢ᵛ A ∣ Δ
  t t1 t2 t3 u u1 u2 : Γ ⊢ᵗ A ∣ Δ
  e e1 e2 e3 e4 : Γ ∣ A ⊢ᵉ Δ
  c c1 c2 c3 : Γ ⊢ Δ

syntax EqVal Γ Δ A e1 e2 = Γ ⊢ᵛ e1 ≈ e2 ∶ A ∣ Δ

data EqVal (Γ Δ : Env) : (A : Ty) -> Γ ⊢ᵛ A ∣ Δ -> Γ ⊢ᵛ A ∣ Δ -> Set

syntax EqTm Γ Δ A e1 e2 = Γ ⊢ᵗ e1 ≈ e2 ∶ A ∣ Δ

data EqTm (Γ Δ : Env) : (A : Ty) -> Γ ⊢ᵗ A ∣ Δ -> Γ ⊢ᵗ A ∣ Δ -> Set

syntax EqCtx Γ Δ A e1 e2 = Γ ∣ e1 ≈ e2 ∶ A ⊢ᵉ Δ

data EqCtx (Γ Δ : Env) : (A : Ty) -> Γ ∣ A ⊢ᵉ Δ -> Γ ∣ A ⊢ᵉ Δ -> Set

syntax EqCmd Γ Δ c1 c2 = Γ ⊢ c1 ≈ c2 ⊣ Δ

data EqCmd (Γ Δ : Env) : Γ ⊢ Δ -> Γ ⊢ Δ -> Set

data EqVal Γ Δ where

  -- equivalence rules
  ≈-refl  :
          -----------------
          Γ ⊢ᵛ v ≈ v ∶ A ∣ Δ

  ≈-sym   : Γ ⊢ᵛ v1 ≈ v2 ∶ A ∣ Δ
          ----------------------
          -> Γ ⊢ᵛ v2 ≈ v1 ∶ A ∣ Δ

  ≈-trans : Γ ⊢ᵛ v1 ≈ v2 ∶ A ∣ Δ -> Γ ⊢ᵛ v2 ≈ v3 ∶ A ∣ Δ
          -----------------------------------------------
          -> Γ ⊢ᵛ v1 ≈ v3 ∶ A ∣ Δ

  -- congruence rules
  lam-cong : (Γ ∙ A) ⊢ᵗ t1 ≈ t2 ∶ B ∣ Δ
           -----------------------------------
           -> Γ ⊢ᵛ lam t1 ≈ lam t2 ∶ A `⇒ B ∣ Δ

  pair-cong : Γ ⊢ᵛ v1 ≈ v2 ∶ A ∣ Δ -> Γ ⊢ᵛ w1 ≈ w2 ∶ B ∣ Δ
            ---------------------------------------------------
            -> Γ ⊢ᵛ pair v1 w1 ≈ pair v2 w2 ∶ A `× B ∣ Δ

  inl-cong : Γ ⊢ᵛ v1 ≈ v2 ∶ A ∣ Δ
           -----------------------------------
           -> Γ ⊢ᵛ inl v1 ≈ inl v2 ∶ A `+ B ∣ Δ

  inr-cong : Γ ⊢ᵛ w1 ≈ w2 ∶ B ∣ Δ
           -----------------------------------
           -> Γ ⊢ᵛ inr w1 ≈ inr w2 ∶ A `+ B ∣ Δ

  -- eta rule

  unit-eta : (v : Γ ⊢ᵛ `Unit ∣ Δ)
           --------------------------
           -> Γ ⊢ᵛ v ≈ unit ∶ `Unit ∣ Δ

data EqTm Γ Δ where

  -- equivalence rules
  ≈-refl  :
          -----------------
          Γ ⊢ᵗ t ≈ t ∶ A ∣ Δ

  ≈-sym   : Γ ⊢ᵗ t1 ≈ t2 ∶ A ∣ Δ
          ----------------------
          -> Γ ⊢ᵗ t2 ≈ t1 ∶ A ∣ Δ

  ≈-trans : Γ ⊢ᵗ t1 ≈ t2 ∶ A ∣ Δ -> Γ ⊢ᵗ t2 ≈ t3 ∶ A ∣ Δ
          -----------------------------------------------
          -> Γ ⊢ᵗ t1 ≈ t3 ∶ A ∣ Δ

  -- congruence rules
  ret-cong : Γ ⊢ᵛ v1 ≈ v2 ∶ A ∣ Δ
           ---------------------------
           -> Γ ⊢ᵗ ret v1 ≈ ret v2 ∶ A ∣ Δ

  μ-cong : Γ ⊢ c1 ≈ c2 ⊣ (Δ ∙ A)
         -------------------------
         -> Γ ⊢ᵗ μ c1 ≈ μ c2 ∶ A ∣ Δ

  -- structural (eta) rule

  μ-eta : (t : Γ ⊢ᵗ A ∣ Δ)
        ------------------------------------------
        -> Γ ⊢ᵗ t ≈ μ (cut A (wk̃ᵗ t) (covar z)) ∶ A ∣ Δ

data EqCtx Γ Δ where

  -- equivalence rules
  ≈-refl  :
          ---------------------
          Γ ∣ e ≈ e ∶ A ⊢ᵉ Δ

  ≈-sym   : Γ ∣ e1 ≈ e2 ∶ A ⊢ᵉ Δ
          ----------------------
          -> Γ ∣ e2 ≈ e1 ∶ A ⊢ᵉ Δ

  ≈-trans : Γ ∣ e1 ≈ e2 ∶ A ⊢ᵉ Δ -> Γ ∣ e2 ≈ e3 ∶ A ⊢ᵉ Δ
          -----------------------------------------------
          -> Γ ∣ e1 ≈ e3 ∶ A ⊢ᵉ Δ

  -- congruence rules
  app-cong : Γ ⊢ᵛ v1 ≈ v2 ∶ A ∣ Δ -> Γ ∣ e1 ≈ e2 ∶ B ⊢ᵉ Δ
           -----------------------------------------------------
           -> Γ ∣ app v1 e1 ≈ app v2 e2 ∶ A `⇒ B ⊢ᵉ Δ

  fst-cong : Γ ∣ e1 ≈ e2 ∶ A ⊢ᵉ Δ
           -----------------------------------
           -> Γ ∣ fst e1 ≈ fst e2 ∶ A `× B ⊢ᵉ Δ

  snd-cong : Γ ∣ e1 ≈ e2 ∶ B ⊢ᵉ Δ
           -----------------------------------
           -> Γ ∣ snd e1 ≈ snd e2 ∶ A `× B ⊢ᵉ Δ

  case-cong : Γ ∣ e1 ≈ e2 ∶ A ⊢ᵉ Δ -> Γ ∣ e3 ≈ e4 ∶ B ⊢ᵉ Δ
            -------------------------------------------------------
            -> Γ ∣ case e1 e3 ≈ case e2 e4 ∶ A `+ B ⊢ᵉ Δ

  μ̃-cong : (Γ ∙ A) ⊢ c1 ≈ c2 ⊣ Δ
         ---------------------------
         -> Γ ∣ μ̃ c1 ≈ μ̃ c2 ∶ A ⊢ᵉ Δ

  -- structural (eta) rule

  μ̃-eta : (e : Γ ∣ A ⊢ᵉ Δ)
        --------------------------------------------
        -> Γ ∣ e ≈ μ̃ (cut A (ret (var z)) (wkᵉ e)) ∶ A ⊢ᵉ Δ

data EqCmd Γ Δ where

  -- equivalence rules
  ≈-refl  :
          -----------
          Γ ⊢ c ≈ c ⊣ Δ

  ≈-sym   : Γ ⊢ c1 ≈ c2 ⊣ Δ
          -----------------
          -> Γ ⊢ c2 ≈ c1 ⊣ Δ

  ≈-trans : Γ ⊢ c1 ≈ c2 ⊣ Δ -> Γ ⊢ c2 ≈ c3 ⊣ Δ
          -----------------------------------
          -> Γ ⊢ c1 ≈ c3 ⊣ Δ

  -- congruence rule
  cut-cong : Γ ⊢ᵗ t1 ≈ t2 ∶ A ∣ Δ -> Γ ∣ e1 ≈ e2 ∶ A ⊢ᵉ Δ
           --------------------------------------------------------------
           -> Γ ⊢ cut A t1 e1 ≈ cut A t2 e2 ⊣ Δ

  -- beta rules (cut elimination)

  μ-beta : (c : Γ ⊢ (Δ ∙ A)) -> (e : Γ ∣ A ⊢ᵉ Δ)
         -----------------------------------------
         -> Γ ⊢ cut A (μ c) e ≈ letc e c ⊣ Δ

  μ̃-beta : (v : Γ ⊢ᵛ A ∣ Δ) -> (c : (Γ ∙ A) ⊢ Δ)
         -------------------------------------------
         -> Γ ⊢ cut A (ret v) (μ̃ c) ≈ letvc v c ⊣ Δ

  app-beta : (t : (Γ ∙ A) ⊢ᵗ B ∣ Δ) -> (v : Γ ⊢ᵛ A ∣ Δ) -> (e : Γ ∣ B ⊢ᵉ Δ)
           ---------------------------------------------------------------------------
           -> Γ ⊢ cut (A `⇒ B) (ret (lam t)) (app v e) ≈ cut B (letv v t) e ⊣ Δ

  fst-beta : (v : Γ ⊢ᵛ A ∣ Δ) -> (w : Γ ⊢ᵛ B ∣ Δ) -> (e : Γ ∣ A ⊢ᵉ Δ)
           -----------------------------------------------------------------
           -> Γ ⊢ cut (A `× B) (ret (pair v w)) (fst e) ≈ cut A (ret v) e ⊣ Δ

  snd-beta : (v : Γ ⊢ᵛ A ∣ Δ) -> (w : Γ ⊢ᵛ B ∣ Δ) -> (e : Γ ∣ B ⊢ᵉ Δ)
           -----------------------------------------------------------------
           -> Γ ⊢ cut (A `× B) (ret (pair v w)) (snd e) ≈ cut B (ret w) e ⊣ Δ

  inl-beta : (v : Γ ⊢ᵛ A ∣ Δ) -> (e1 : Γ ∣ A ⊢ᵉ Δ) -> (e2 : Γ ∣ B ⊢ᵉ Δ)
           -----------------------------------------------------------------------
           -> Γ ⊢ cut (A `+ B) (ret (inl v)) (case e1 e2) ≈ cut A (ret v) e1 ⊣ Δ

  inr-beta : (w : Γ ⊢ᵛ B ∣ Δ) -> (e1 : Γ ∣ A ⊢ᵉ Δ) -> (e2 : Γ ∣ B ⊢ᵉ Δ)
           -----------------------------------------------------------------------
           -> Γ ⊢ cut (A `+ B) (ret (inr w)) (case e1 e2) ≈ cut B (ret w) e2 ⊣ Δ
