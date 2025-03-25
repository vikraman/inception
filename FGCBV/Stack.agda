module FGCBV.Stack (R : Set) where

open import FGCBV.Syntax
open import FGCBV.CPS

-- data Machine (Γ : Ctx) : (A : Ty) (M : Γ ⊢ᶜ A) (K : Stk) -> Set where

-- record State : Set where
--   constructor st
--   field
--     env : Ctx
--     type : Ty
--     code : env ⊢ᶜ type
--     stack : Stk
   
-- State : Set
-- State = (Γ : Ctx) × (A : Ty) (M : Γ ⊢ᶜ A) (K : Stk)

-- step : State -> State
-- step (st Γ A (produce V) K) =
--   {!!}
-- step (st Γ A (letv V M) K) = 
--   st Γ A (sub-comp (sub-ex sub-id V) M) K
-- step (st Γ A (pm V M) K) =
--   {!!}
-- step (st Γ A (push M N) K) =
--   {!!}
-- step (st Γ A (app V W) K) =
--   {!!}

syntax Stk Γ B C = Γ ∣ B ⊢ᵏ C

data Stk (Γ : Ctx) : (B : Ty) (C : Ty) -> Set where

  nil :
      ------------
      Γ ∣ C ⊢ᵏ C


  _∷_ : (M : (Γ ∙ A) ⊢ᶜ B) -> (K : Γ ∣ B ⊢ᵏ C)
      ----------------------------------------
      -> Γ ∣ A ⊢ᵏ C 

  fst∷_ : (K : Γ ∣ A ⊢ᵏ C)
        --------------------
        -> Γ ∣ A `× B ⊢ᵏ C

  snd∷_ : (K : Γ ∣ B ⊢ᵏ C)
        --------------------
        -> Γ ∣ A `× B ⊢ᵏ C

  _val∷_ : (V : Γ ⊢ᵛ A) -> (Γ ∣ B ⊢ᵏ C)
         -------------------------------
         -> Γ ∣ (A `⇒ B) ⊢ᵏ C

open import Data.Product

-- step : {Γ : Ctx} {C : Ty} -> (Γ ⊢ᶜ B × Γ ∣ B ⊢ᵏ C) -> (Γ ⊢ᶜ B × Γ ∣ B ⊢ᵏ C)
-- step (produce V , N ∷ K) = {!!}
--   -- sub-comp (sub-ex sub-id V) {!!} , {!!}
-- step (letv V M , K) = 
--   sub-comp (sub-ex sub-id V) M , K
-- step (pm V M , K) = 
--   {!!}
-- step (push M N , K) = 
--   {!!}
-- step (app V W , K) = 
--   {!!}

