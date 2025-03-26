module Sub.Machine where

open import Data.List
open import Data.Product

open import Sub.Syntax

data Stack : Set where
  nil : Stack
  [_,_]_ : {Γ : Ctx} {A : Ty} -> Stack -> Γ ⊢ᶜ A -> Stack -> Stack

data Env : Set where
  ∅ : Env
  ⦅_,_⦆ : Env -> List (Stack × Env) -> Env

data State : Set where
  ⟪_,_,_⟫ : {Γ : Ctx} {A : Ty} -> Γ ⊢ᶜ A -> Env -> Stack -> State
