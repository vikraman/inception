module Sub.Machine where

open import Data.List
open import Data.Product

open import Sub.Syntax

data Stack : Set where
  nil : Stack
  [_,_]∷_ : {Γ : Ctx} {A : Ty} -> Stack -> Γ ⊢ᶜ A -> Stack -> Stack

data Env : Set where
  ∅ : Env
  ⦅_,_⦆ : Env -> List (Stack × Env) -> Env

data State : Set where
  ⟪_,_,_⟫ : {Γ : Ctx} {A : Ty} -> Γ ⊢ᶜ A -> Env -> Stack -> State

data _~>_ : State -> State -> Set where
  ~>-app :  {V : Γ ⊢ᵛ A `⇒ B} {W : Γ ⊢ᵛ A} {γ : Env} {k : Stack}
         ------------------------------------------------------------------------
         -> ⟪ app V W , γ , k ⟫ ~> ⟪ produce V , γ , [ k , (produce W) ]∷ k ⟫
  ~>-letv : {V : Γ ⊢ᵛ A} {M : (Γ ∙ A) ⊢ᶜ B} {γ : Env} {k : Stack}
         ------------------------------------------------------------------------
         -> ⟪ letv V M , γ , k ⟫ ~> ⟪ (sub-comp (sub-ex sub-id V) M) , γ , k ⟫
  ~>-produce : {V : Γ ⊢ᵛ A} {N : (Γ ∙ A) ⊢ᶜ B} {γ : Env} {k k' : Stack}
         ------------------------------------------------------------------------
         -> ⟪ produce V , γ , [ k' , N ]∷ k ⟫ ~> ⟪ (sub-comp (sub-ex sub-id V) N) , γ , k' ⟫
