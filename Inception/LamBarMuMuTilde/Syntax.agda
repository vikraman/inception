module Inception.LamBarMuMuTilde.Syntax where

open import Data.Nat

infixr 25 _`⇒_

data Ty : Set where
  _`⇒_ : Ty -> Ty -> Ty

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

  cut : (e : Γ ∣ A ⊢ᵉ Δ) -> (t : Γ ⊢ᵗ A ∣ Δ)
      ---------------------------------------
      -> Γ ⊢ Δ

data Val where

  var : (i : Γ ∋ A)
       ----------------
       -> Γ ⊢ᵛ A ∣ Δ

  lam : (t : (Γ ∙ A) ⊢ᵗ B ∣ Δ)
      ------------------------
      -> Γ ⊢ᵛ A `⇒ B ∣ Δ

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

  μ̃ : (c : (Γ ∙ A) ⊢ Δ)
    ------------------------
    -> Γ ∣ A ⊢ᵉ Δ
