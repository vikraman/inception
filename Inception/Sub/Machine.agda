-- {-# OPTIONS --show-implicit #-}

module Inception.Sub.Machine where

-- open import Data.List
-- open import Data.Product
-- open import Data.Sum using (_⊎_; inj₁; inj₂)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)

open import Inception.Sub.Syntax

_⊕_ : Ctx → Ctx → Ctx
Γ ⊕ ε = Γ
Γ ⊕ (Δ ∙ x) = (Γ ⊕ Δ) ∙ x

data Stack : (Γ : Ctx) → Set where
  nil : Stack ε
  _↦_∷_ : {Γ : Ctx} {A : Ty} -> (i : (Γ ⊕ Ψ) ∙ `V ∋ `V) -> (N : (Γ ⊕ Ψ) ⊢ᶜ A) -> Stack Γ -> Stack ((Γ ⊕ Ψ) ∙ `V)
  _∷_ : {Γ : Ctx} {A B : Ty} -> (N : ((Γ ⊕ Ψ) ∙ A) ⊢ᶜ B) -> Stack Γ -> Stack (Γ ⊕ Ψ)
  --_↦_∷_ : {Γ : Ctx} {A : Ty} -> (i : Γ ∙ `V ∋ `V) -> (N : Γ ⊢ᶜ A) -> Stack Γ -> Stack (Γ ∙ `V)
  --_∷_ : {Γ : Ctx} {A B : Ty} -> (N : (Γ ∙ A) ⊢ᶜ B) -> Stack Γ -> Stack Γ

data State : Set where
  ⟪_∥_∥_⟫ : {Γ : Ctx} -> (Δ : Ctx) -> (Γ ⊕ Δ) ⊢ᶜ A -> Stack Γ -> State

⊕-assoc : (Γ ⊕ Ψ) ⊕ Δ ≡ Γ ⊕ (Ψ ⊕ Δ)
⊕-assoc {Γ} {Ψ} {ε} = refl
⊕-assoc {Γ} {Ψ} {Δ ∙ x} rewrite ⊕-assoc {Γ} {Ψ} {Δ} = refl

⊕-left-id : (Γ : Ctx) → ε ⊕ Γ ≡ Γ
⊕-left-id ε = refl
⊕-left-id (Γ ∙ x) rewrite ⊕-left-id Γ = refl

ext-⊇-R : (Γ ⊕ Δ) ⊇ Δ
ext-⊇-R {ε} {ε} = wk-ε
ext-⊇-R {Γ ∙ x} {ε} = wk-wk (ext-⊇-R {Γ} {ε})
ext-⊇-R {ε} {Δ ∙ x} rewrite ⊕-left-id (Δ ∙ x) = wk-id
ext-⊇-R {Γ ∙ x₁} {Δ ∙ x} = wk-cong (ext-⊇-R {Γ ∙ x₁} {Δ})

ext-⊇-L : (Γ ⊕ Δ) ⊇ Γ
ext-⊇-L {Γ} {ε} = wk-id
ext-⊇-L {ε} {Δ ∙ x} = wk-wk ext-⊇-L
ext-⊇-L {Γ ∙ x₁} {Δ ∙ x} = wk-wk ext-⊇-L

i-wk : (i : Γ ∋ `V) → (Γ ⊕ Δ) ∋ `V
i-wk {Γ} {Δ} i = wk-mem {Γ ⊕ Δ} {Γ} ext-⊇-L i

i-assoc : (i : ((Γ ⊕ Ψ) ⊕ Δ) ∋ A) → (Γ ⊕ (Ψ ⊕ Δ)) ∋ A
i-assoc {Δ = ε} i = i
i-assoc {Δ = Δ ∙ x} h = h
i-assoc {Δ = Δ ∙ x} (t i) = t (i-assoc {Δ = Δ} i)

i-assoc' : (i : (Γ ⊕ (Ψ ⊕ Δ)) ∋ A) → ((Γ ⊕ Ψ) ⊕ Δ) ∋ A
i-assoc' {Δ = ε} i = i
i-assoc' {Δ = Δ ∙ x} h = h
i-assoc' {Δ = Δ ∙ x} (t i) = t (i-assoc' {Δ = Δ} i)

v-assoc : Val ((Γ ⊕ Ψ) ⊕ Δ) A → Val (Γ ⊕ (Ψ ⊕ Δ)) A

c-assoc : Comp ((Γ ⊕ Ψ) ⊕ Δ) A → Comp (Γ ⊕ (Ψ ⊕ Δ)) A

v-assoc {Γ} {Ψ} {Δ} (var i) = var (i-assoc {Γ} {Ψ} {Δ} i)
v-assoc {Γ} {Ψ} {Δ} (lam {A = A} x) = lam (c-assoc {Γ} {Ψ} {Δ ∙ A} x)
v-assoc {Γ} {Ψ} {Δ} (pair V V₁) = pair (v-assoc {Γ} {Ψ} {Δ} V) (v-assoc {Γ} {Ψ} {Δ} V₁)
v-assoc {Γ} {Ψ} {Δ} (pm {A = A} {B = B} V V₁) = pm (v-assoc {Γ} {Ψ} {Δ} V) (v-assoc {Γ} {Ψ} {Δ ∙ A ∙ B} V₁)
v-assoc {Γ} {Ψ} {Δ} unit = unit

c-assoc {Γ} {Ψ} {Δ} (return x) = return (v-assoc {Γ} {Ψ} {Δ} x)
c-assoc {Γ} {Ψ} {Δ} (pm {A = A} {B = B} x X) = pm (v-assoc {Γ} {Ψ} {Δ} x) (c-assoc {Γ} {Ψ} {Δ ∙ A ∙ B} X)
c-assoc {Γ} {Ψ} {Δ} (push {A = A} X X₁) = push (c-assoc {Γ} {Ψ} {Δ} X) (c-assoc {Γ} {Ψ} {Δ ∙ A} X₁)
c-assoc {Γ} {Ψ} {Δ} (app x x₁) = app (v-assoc {Γ} {Ψ} {Δ} x) (v-assoc {Γ} {Ψ} {Δ} x₁)
c-assoc {Γ} {Ψ} {Δ} (var x) = var (v-assoc {Γ} {Ψ} {Δ} x)
c-assoc {Γ} {Ψ} {Δ} (sub X X₁) = sub (c-assoc {Γ} {Ψ} {Δ ∙ `V} X) (c-assoc {Γ} {Ψ} {Δ} X₁)

data _~>_ : State -> State -> Set where

  ~>-app : {M : ((Γ ⊕ Δ) ∙ A) ⊢ᶜ B} {V : (Γ ⊕ Δ) ⊢ᵛ A} {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ            ∥ app (lam M) V                                                     ∥ k         ⟫
       ~> ⟪ Δ            ∥ sub-comp (sub-ex sub-id V) M                                      ∥ k         ⟫

  ~>-pm : {V1 : (Γ ⊕ Δ) ⊢ᵛ A} {V2 : (Γ ⊕ Δ) ⊢ᵛ B} {W : ((Γ ⊕ Δ) ∙ A ∙ B) ⊢ᶜ C} {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ            ∥ pm (pair V1 V2) W                                                 ∥ k         ⟫
       ~> ⟪ Δ            ∥ sub-comp (sub-ex (sub-ex sub-id V1) V2) W                         ∥ k         ⟫

  ~>-push : {M : (Γ ⊕ Δ) ⊢ᶜ A} {N : ((Γ ⊕ Δ) ∙ A) ⊢ᶜ B} {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ            ∥ push M N                                                          ∥ k         ⟫
       ~> ⟪ ε            ∥ M                                                                 ∥ N ∷ k     ⟫

  ~>-sub : {M : ((Γ ⊕ Δ) ∙ `V) ⊢ᶜ A} {N : (Γ ⊕ Δ) ⊢ᶜ A} {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ            ∥ sub M N                                                           ∥ k         ⟫
       ~> ⟪ ε            ∥ M                                                                 ∥ h ↦ N ∷ k ⟫

  ~>-var-pop-c : {i : Γ ∋ `V} {N : ((Γ ⊕ Ψ) ∙ A) ⊢ᶜ B}  {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ            ∥ var {A = A} (var (i-assoc' {Γ} {Ψ} {Δ} (i-wk i)))                 ∥ N ∷ k     ⟫
       ~> ⟪ Ψ ⊕ Δ        ∥ var {A = A} (var (i-wk i))                                        ∥ k         ⟫

  ~>-var-pop-k : {i : (Γ ⊕ Ψ) ∋ `V} {N : (Γ ⊕ Ψ) ⊢ᶜ B}  {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ            ∥ var {A = A} (var (i-wk (t i)))                                    ∥ h ↦ N ∷ k ⟫
       ~> ⟪ (Ψ ∙ `V) ⊕ Δ ∥ var {A = A} (var (i-assoc {Γ} {Ψ ∙ `V} {Δ} (i-wk {Δ = Δ} (t i)))) ∥ k         ⟫

  ~>-var-step : {N : (Γ ⊕ Ψ) ⊢ᶜ B}  {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ            ∥ var {A = A} (var (i-wk h))                                        ∥ h ↦ N ∷ k ⟫
       ~> ⟪ Ψ            ∥ N                                                                 ∥ k         ⟫

  ~>-return-pop : {V : (((Γ ⊕ Ψ) ∙ `V) ⊕ Δ) ⊢ᵛ A} {N : (Γ ⊕ Ψ) ⊢ᶜ B} {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ ∥ return V                                                                     ∥ h ↦ N ∷ k ⟫
       ~> ⟪ (Ψ ∙ `V) ⊕ Δ ∥ return (v-assoc {Γ} {Ψ ∙ `V} {Δ} V)                               ∥ k         ⟫

  ~>-return-step : {V : (Γ ⊕ Ψ) ⊢ᵛ A} {N : ((Γ ⊕ Ψ) ∙ A) ⊢ᶜ B} {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ            ∥ return (wk-val (ext-⊇-L {Γ ⊕ Ψ} {Δ}) V)                           ∥ N ∷ k     ⟫
       ~> ⟪ Ψ            ∥  (sub-comp (sub-ex sub-id V) N)                                   ∥ k         ⟫

{- OLD
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

-}
