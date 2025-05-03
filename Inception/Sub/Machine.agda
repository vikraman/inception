-- {-# OPTIONS --show-implicit #-}

module Inception.Sub.Machine where

open import Data.List
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Inception.Sub.Syntax

data Elem {Γ : Ctx} {A B : Ty} : Set where
  cont : Γ ⊢ᶜ B → Elem
  comp : (Γ ∙ A) ⊢ᶜ B → Elem

data Stack : Set where
  nil : Stack
  _∷_ : {Γ : Ctx} {A B : Ty} -> (Elem {Γ} {A} {B}) -> Stack -> Stack


data State : Set where
  ⟪_,_,_⟫ : {Γ : Ctx} {A : Ty} -> Γ ⊢ᶜ A -> Ctx × Ctx -> Stack -> State

data _~>_ : State -> State -> Set where
  ~>-app : {M : (Γ ∙ A) ⊢ᶜ B} {V : Γ ⊢ᵛ A} {k : Stack}
         -----------------------------------------------------------------------------------------------------
         ->    ⟪ app (lam M) V                             , (ε , ε)                        , k                           ⟫
            ~> ⟪ sub-comp (sub-ex sub-id V) M              , (ε , ε)                        , k                           ⟫
  ~>-push : {M : Γ ⊢ᶜ A} {N : (Γ ∙ A) ⊢ᶜ B} {k : Stack}
         -----------------------------------------------------------------------------------------------------
         ->    ⟪ push M N                                  , (ε , ε)                        , k                           ⟫
            ~> ⟪ M                                         , (ε , ε)                        , ( comp N ) ∷ k              ⟫
  ~>-return-pop : {V : Γ ⊢ᵛ A} {Δ : Ctx} {K : Δ ⊢ᶜ D} {k : Stack}
         -----------------------------------------------------------------------------------------------------
         ->    ⟪ return V                                  , (ε , ε)                        , ( cont {Δ} {C} {D} K ) ∷ k  ⟫
            ~> ⟪ return V                                  , (ε , ε)                        , k                           ⟫
  ~>-return-step : {V : Γ ⊢ᵛ A} {M : (Γ ∙ A) ⊢ᶜ B} {k : Stack}
         -----------------------------------------------------------------------------------------------------
         ->    ⟪ return V                                  , (ε , ε)                        , ( comp M ) ∷ k              ⟫
            ~> ⟪ (sub-comp (sub-ex sub-id V) M)            , (ε , ε)                        , k                           ⟫
  ~>-sub : {M : (Γ ∙ `V) ⊢ᶜ A} {N : Γ ⊢ᶜ A} {k : Stack}
         -----------------------------------------------------------------------------------------------------
         ->    ⟪ sub M N                                   , (ε , ε)                        , k                           ⟫
            ~> ⟪ M                                         , (ε , ε)                        , ( cont {Γ} {`V} {A} N ) ∷ k ⟫
  ~>-var-pop : {V : Γ ⊢ᵛ `V} {K : (Δ ∙ C) ⊢ᶜ D} {k : Stack}
         -----------------------------------------------------------------------------------------------------
         ->    ⟪ var {A = A} V                             , (ε , ε)                        , (comp K) ∷ k                ⟫
            ~> ⟪ var {A = A} V                             , (ε , ε)                        , k                           ⟫
  ~>-var-lookup-init : {i : Γ ∋ `V} {N : Δ ⊢ᶜ D} {k : Stack}
         -----------------------------------------------------------------------------------------------------
         ->    ⟪ var {A = A} (var i)                       , (ε , ε)                        , (cont {Δ} {`V} {D} N) ∷ k   ⟫
            ~> ⟪ var {A = A} (var i)                       , (Γ , Δ)                        , (cont {Δ} {`V} {D} N) ∷ k   ⟫
  ~>-var-lookup-stop : {i : Γ ∋ `V} {N : Δ ⊢ᶜ D} {k : Stack}
         -----------------------------------------------------------------------------------------------------
         ->    ⟪ var {A = A} (var i)                       , (ε , Ψ ∙ C)                    , (cont {Δ} {`V} {D} N) ∷ k   ⟫
            ~> ⟪ var {A = A} (var i)                       , (ε , ε)                        , k                           ⟫
  ~>-var-lookup-decr : {i : Γ ∋ `V} {B' C' : Ty} {Ψ' : Ctx} {N : Δ ⊢ᶜ D} {k : Stack}
         -----------------------------------------------------------------------------------------------------
         ->    ⟪ var {A = A} (var i)                       , (Ψ' ∙ B' ∙ B , Ψ ∙ C' ∙ C)     , (cont {Δ} {`V} {D} N) ∷ k   ⟫
            ~> ⟪ var {A = A} (var i)                       , (Ψ' ∙ B' , Ψ ∙ C')             , k                           ⟫
  ~>-var-step : {i : Γ ∋ `V} {N : Δ ⊢ᶜ D} {k : Stack}
         -----------------------------------------------------------------------------------------------------
         ->    ⟪ var {A = A} (var i)                       , (ε ∙ B , ε)                    , (cont {Δ} {`V} {D} N) ∷ k   ⟫
            ~> ⟪ N                                         , (ε , ε)                        , k                           ⟫
  ~>-pm : {V1 : Γ ⊢ᵛ A} {V2 : Γ ⊢ᵛ B} {W : (Γ ∙ A ∙ B) ⊢ᶜ C} {k : Stack}
         -----------------------------------------------------------------------------------------------------
         ->    ⟪ pm (pair V1 V2) W                         , (ε , ε)                        , k                           ⟫
            ~> ⟪ sub-comp (sub-ex (sub-ex sub-id V1) V2) W , (ε , ε)                        , k                           ⟫


data _~>*_ : State -> State → Set where

  _∎ : ∀ (M : State)
      --------
    → M ~>* M

  _~>⟨_⟩_ : ∀ (L : State) {M N : State}
    → L ~> M
    → M ~>* N
      ---------
    → L ~>* N

~>*-trans : {M N P : State} -> M ~>* N -> N ~>* P -> M ~>* P
~>*-trans (_ ∎) N>P = N>P
~>*-trans (M ~>⟨ x ⟩ M>N) N>P =  M ~>⟨ x ⟩ ~>*-trans M>N N>P

-- "local termination"

lt : {M : Γ ⊢ᶜ A} {k : Stack}
     ->   ( ∃[ Δ ] ∃[ B ] ∃[ V ] (⟪ M , (ε , ε) , k ⟫ ~>* ⟪ var    {Γ = Δ} {A = B} V , (ε , ε) , k ⟫) )
        ⊎ ( ∃[ V ] (⟪ M , (ε , ε) , k ⟫ ~>* ⟪ return {Γ = Γ} {A = A} V , (ε , ε) , k ⟫) )

lt {Γ = Γ} {A = A} {M = return x} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = pm x M} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = app x x₁} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = var x} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = sub M M₁} {k = k} = {!!}

lt {Γ = Γ} {A = A} {M = push N (app P V)} {k = k} with lt {M = N} {k = comp (app P V) ∷ k}
... | inj₁ (Δ₁ , B₁ , V₁ , Q₁) = inj₁ ( Δ₁ , B₁ , V₁ , ~>*-trans (⟪ push N (app P V) , ( ε , ε ) , k ⟫ ~>⟨ ~>-push ⟩ Q₁)
                                                                 (⟪ var V₁ , ( ε , ε ) , comp (app P V) ∷ k ⟫ ~>⟨ ~>-var-pop ⟩ (⟪ var V₁ , ( ε , ε ) , k ⟫  ∎)))
... | inj₂ (V₁ , Q₁) with lt {M = app (sub-val (sub-ex sub-id V₁) P) (sub-val (sub-ex sub-id V₁) V)} {k = k}
...   | inj₁ (Δ₂ , B₂ , V₂ , Q₂) = inj₁ ( Δ₂ , B₂ , V₂ , ~>*-trans (⟪ push N (app P V) , ( ε , ε ) , k ⟫ ~>⟨ ~>-push ⟩ Q₁)
                                                                   (⟪ return V₁ , ( ε , ε ) , comp (app P V) ∷ k ⟫ ~>⟨ ~>-return-step ⟩ Q₂))
...   | inj₂ (V₂ , Q₂) = inj₂ (V₂ , ~>*-trans (⟪ push N (app P V) , ( ε , ε ) , k ⟫ ~>⟨ ~>-push ⟩ Q₁)
                                              (⟪ return V₁ , ( ε , ε ) , comp (app P V) ∷ k ⟫ ~>⟨ ~>-return-step ⟩ Q₂))

lt {Γ = Γ} {A = A} {M = push N (return x)} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = push N (pm x P)} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = push N (push P P₁)} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = push N (var x)} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = push N (sub P P₁)} {k = k} = {!!}
