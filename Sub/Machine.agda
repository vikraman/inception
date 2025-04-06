module Sub.Machine where

open import Data.List
open import Data.Product

open import Sub.Syntax

data Stack : Set where
  nil : Stack
  [_,_]∷_ : {Γ : Ctx} {A : Ty} -> Stack -> Γ ⊢ᶜ A -> Stack -> Stack

-- I don't think we need this, if we want to stay close to the CK-machine.
-- data Env : Set where
--   ∅ : Env
--   ⦅_,_⦆ : Env -> List (Stack × Env) -> Env

-- data State : Set where
--   ⟪_,_,_⟫ : {Γ : Ctx} {A : Ty} -> Γ ⊢ᶜ A -> Env -> Stack -> State

data State : Set where
  ⟪_,_⟫ : {Γ : Ctx} {A : Ty} -> Γ ⊢ᶜ A -> Stack -> State

data _~>_ : State -> State -> Set where
  ~>-app :  {V : Γ ⊢ᵛ A `⇒ B} {W : Γ ⊢ᵛ A} {k : Stack}
         ------------------------------------------------------------------------
         -> ⟪ app V W , k ⟫ ~> ⟪ return V , [ k , (return W) ]∷ k ⟫
  ~>-letv : {V : Γ ⊢ᵛ A} {M : (Γ ∙ A) ⊢ᶜ B} {k : Stack}
         ------------------------------------------------------------------------
         -> ⟪ letv V M , k ⟫ ~> ⟪ (sub-comp (sub-ex sub-id V) M) , k ⟫
  ~>-return : {V : Γ ⊢ᵛ A} {N : (Γ ∙ A) ⊢ᶜ B} {k k' : Stack}
         ------------------------------------------------------------------------
         -> ⟪ return V , [ k' , N ]∷ k ⟫ ~> ⟪ (sub-comp (sub-ex sub-id V) N) , k' ⟫
