-- {-# OPTIONS --show-implicit #-}

module Inception.Sub.Machine where

open import Data.List
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax

variable
  Γ' Δ' Ψ' : Ctx

_⊕_ : Ctx → Ctx → Ctx
Γ ⊕ ε = Γ
Γ ⊕ (Δ ∙ x) = (Γ ⊕ Δ) ∙ x

data Stack : (Γ : Ctx) → Set where
  nil : Stack ε
  _↦_∷_ : {Γ : Ctx} {A : Ty} -> (i : (Γ ⊕ Ψ) ∙ `V ∋ `V) -> (N : (Γ ⊕ Ψ) ⊢ᶜ A) -> Stack Γ -> Stack ((Γ ⊕ Ψ) ∙ `V)
  _∷_ : {Γ : Ctx} {A B : Ty} -> (N : ((Γ ⊕ Ψ) ∙ A) ⊢ᶜ B) -> Stack Γ -> Stack (Γ ⊕ Ψ)

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

i-assoc : (i : ((Γ ⊕ Ψ) ⊕ Δ) ∋ A) → (Γ ⊕ (Ψ ⊕ Δ)) ∋ A
i-assoc {Γ} {Ψ} {Δ} i rewrite ⊕-assoc {Γ} {Ψ} {Δ} = i

v-assoc : Val ((Γ ⊕ Ψ) ⊕ Δ) A → Val (Γ ⊕ (Ψ ⊕ Δ)) A
v-assoc {Γ} {Ψ} {Δ} v rewrite ⊕-assoc {Γ} {Ψ} {Δ} = v

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
    ----------------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ            ∥ var {A = A} (var (wk-mem (ext-⊇-L {Γ = Γ ⊕ Ψ} {Δ = Δ}) (wk-mem ext-⊇-L i))) ∥ N ∷ k     ⟫
       ~> ⟪ Ψ ⊕ Δ        ∥ var {A = A} (var (wk-mem ext-⊇-L i))                                        ∥ k         ⟫

  ~>-var-pop-k : {i : (Γ ⊕ Ψ) ∋ `V} {N : (Γ ⊕ Ψ) ⊢ᶜ B}  {k : Stack Γ}
    ----------------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ            ∥ var {A = A} (var (wk-mem ext-⊇-L (t i)))                                    ∥ h ↦ N ∷ k ⟫
       ~> ⟪ (Ψ ∙ `V) ⊕ Δ ∥ var {A = A} (var (i-assoc {Γ} {Ψ ∙ `V} {Δ} (wk-mem ext-⊇-L (t i))))         ∥ k         ⟫

  ~>-var-step : {N : (Γ ⊕ Ψ) ⊢ᶜ B}  {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ            ∥ var {A = A} (var (wk-mem ext-⊇-L h))                              ∥ h ↦ N ∷ k ⟫
       ~> ⟪ Ψ            ∥ N                                                                 ∥ k         ⟫

  ~>-return-pop : {V : (((Γ ⊕ Ψ) ∙ `V) ⊕ Δ) ⊢ᵛ A} {N : (Γ ⊕ Ψ) ⊢ᶜ B} {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ ∥ return V                                                                     ∥ h ↦ N ∷ k ⟫
       ~> ⟪ (Ψ ∙ `V) ⊕ Δ ∥ return (v-assoc {Γ} {Ψ ∙ `V} {Δ} V)                               ∥ k         ⟫

  ~>-return-step : {V : (Γ ⊕ Ψ) ⊢ᵛ A} {N : ((Γ ⊕ Ψ) ∙ A) ⊢ᶜ B} {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ            ∥ return (wk-val (ext-⊇-L {Γ ⊕ Ψ} {Δ}) V)                           ∥ N ∷ k     ⟫
       ~> ⟪ Ψ            ∥  (sub-comp (sub-ex sub-id V) N)                                   ∥ k         ⟫

data _~>*_ : State -> State → Set where
  _■ : ∀ (M : State) → M ~>* M
  _~>⟨_⟩_ : ∀ (L : State) {M N : State} → L ~> M → M ~>* N → L ~>* N

~>*-trans : {M N P : State} -> M ~>* N -> N ~>* P -> M ~>* P
~>*-trans (_ ■) N>P = N>P
~>*-trans (M ~>⟨ x ⟩ M>N) N>P =  M ~>⟨ x ⟩ ~>*-trans M>N N>P

~>*-refl : {M : State} -> M ~>* M
~>*-refl {M} = M ■

wk-mem-id : {i : Γ ∋ A} → (wk-mem wk-id i) ≡ i
wk-mem-id {i = h} = refl
wk-mem-id {i = t i} rewrite wk-mem-id {i = i} = refl

wk-comp-id : {x : Comp (Γ ∙ A) B} → (wk-comp wk-id x) ≡ x

wk-val-id : {x : Val Γ B} → (wk-val wk-id x) ≡ x

wk-comp-id {x = return x} rewrite wk-val-id {x = x} = refl
wk-comp-id {x = pm x x₁} rewrite wk-val-id {x = x} rewrite (wk-comp-id {x = x₁}) = refl
wk-comp-id {x = push x x₁} rewrite wk-comp-id {x = x} rewrite wk-comp-id {x = x₁} = refl
wk-comp-id {x = app x x₁} rewrite wk-val-id {x = x} rewrite wk-val-id {x = x₁} = refl
wk-comp-id {x = var x} rewrite wk-val-id {x = x} = refl
wk-comp-id {x = sub x x₁} rewrite wk-comp-id {x = x} rewrite wk-comp-id {x = x₁} = refl

wk-val-id {Γ = ε} {x = var i} rewrite wk-mem-id {i = i} = refl
wk-val-id {Γ = Γ ∙ A} {x = var i} rewrite wk-mem-id {i = i} = refl
wk-val-id {Γ = ε} {x = lam x} rewrite wk-comp-id {x = x} = refl
wk-val-id {Γ = Γ ∙ A} {x = lam x} rewrite (wk-comp-id {x = x}) = refl
wk-val-id {Γ = ε} {x = pair x x₁} rewrite wk-val-id {x = x} rewrite wk-val-id {x = x₁} = refl
wk-val-id {Γ = Γ ∙ x₂} {x = pair x x₁} rewrite wk-val-id {x = x} rewrite wk-val-id {x = x₁} = refl
wk-val-id {Γ = ε} {x = pm x x₁} rewrite wk-val-id {x = x} rewrite wk-val-id {x = x₁} = refl
wk-val-id {Γ = Γ ∙ x₂} {x = pm x x₁} rewrite wk-val-id {x = x} rewrite wk-val-id {x = x₁} = refl
wk-val-id {Γ = ε} {x = unit} = refl
wk-val-id {Γ = Γ ∙ x} {x = unit} = refl

-------------------------------------------------------------

i-wk : (i : Γ ∋ `V) → (Γ ⊕ Δ) ∋ `V
i-wk {Γ} {Δ} i = wk-mem {Γ ⊕ Δ} {Γ} ext-⊇-L i

eq-wk : {i i' : Γ ∋ `V} → i ≡ i' → (i-wk {Δ = ε ∙ A} i) ≡ (i-wk {Δ = ε ∙ A} i')
eq-wk {i = i} {i' = i'} i≡i' = cong i-wk i≡i'

i-assoc' : (i : (Γ ⊕ (Ψ ⊕ Δ)) ∋ A) → ((Γ ⊕ Ψ) ⊕ Δ) ∋ A
i-assoc' {Δ = ε} i = i
i-assoc' {Δ = Δ ∙ x} h = h
i-assoc' {Δ = Δ ∙ x} (t i) = t (i-assoc' {Δ = Δ} i)

v-assoc' : Val (Γ ⊕ (Ψ ⊕ Δ)) A → Val ((Γ ⊕ Ψ) ⊕ Δ) A
v-assoc' {Γ} {Ψ} {Δ} v rewrite ⊕-assoc {Γ} {Ψ} {Δ} = v

c-assoc : Comp ((Γ ⊕ Ψ) ⊕ Δ) A → Comp (Γ ⊕ (Ψ ⊕ Δ)) A
c-assoc {Γ} {Ψ} {Δ} c rewrite ⊕-assoc {Γ} {Ψ} {Δ} = c

c-assoc' : Comp (Γ ⊕ (Ψ ⊕ Δ)) A → Comp ((Γ ⊕ Ψ) ⊕ Δ) A
c-assoc' {Γ} {Ψ} {Δ} c rewrite ⊕-assoc {Γ} {Ψ} {Δ} = c

k-assoc : Stack ((Γ ⊕ Ψ) ⊕ Δ) → Stack (Γ ⊕ (Ψ ⊕ Δ))
k-assoc {Γ} {Ψ} {Δ} k rewrite ⊕-assoc {Γ} {Ψ} {Δ} = k

k-assoc' : Stack (Γ ⊕ (Ψ ⊕ Δ)) → Stack ((Γ ⊕ Ψ) ⊕ Δ)
k-assoc' {Γ} {Ψ} {Δ} k rewrite ⊕-assoc {Γ} {Ψ} {Δ} = k

c-assoc'' : Comp ((Γ ⊕ Ψ) ⊕ Δ) A ≡ Comp (Γ ⊕ (Ψ ⊕ Δ)) A
c-assoc'' {Γ} {Ψ} {Δ} {A} rewrite ⊕-assoc {Γ} {Ψ} {Δ} = refl

-------------------------------------------------------------

lt : {M : ((Γ ⊕ Ψ') ⊕ Ψ) ⊢ᶜ A} {k : Stack (Γ ⊕ Ψ')}
     ->   ( ∃[ Δ ] ∃[ i ] (⟪ Ψ ∥ M ∥ k ⟫ ~>* ⟪ Δ ∥ var {A = A} (var (wk-mem (ext-⊇-L {Δ = Δ}) (wk-mem (ext-⊇-L {Δ = Ψ'}) i))) ∥ k ⟫) )
        ⊎ ( ∃[ V ] (⟪ Ψ ∥ M ∥ k ⟫ ~>* ⟪ Ψ ∥ return {A = A} V ∥ k ⟫) )

lt {Γ = Γ} {A = A} {M = return x} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = pm x M} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = app x x₁} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = var x} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = sub M M₁} {k = k} = {!!}

lt {Γ = Γ} {A = A} {M = push N (return x)} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = push N (pm x P)} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = push N (push P P₁)} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = push N (var x)} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = push N (sub P P₁)} {k = k} = {!!}


lt {Γ = Γ} {Ψ' = Ψ'} {Ψ = Ψ} {A = A} {M = push {A = A₂} N (app {A = A₁} P V)} {k = k} with lt {Γ = Γ} {Ψ' = Ψ' ⊕ Ψ} {Ψ = ε} {M = {!!}} {k = {!!}}
... | inj₁ (Δ₁ , i₁ , Q₁) = {!!}
... | inj₂ (V₁ , Q₁)  = {!!}

-- SCRATCH:

-- -- This one is a special case of the above with Δ = ε, it might be the only one we need.
-- ~>-return-step' : {V : (Γ ⊕ Ψ) ⊢ᵛ A} {N : ((Γ ⊕ Ψ) ∙ A) ⊢ᶜ B} {k : Stack Γ}
--   ------------------------------------------------------------------------------------------------------
--   ->    ⟪ ε            ∥ return V                                                          ∥ N ∷ k     ⟫
--      ~> ⟪ Ψ            ∥  (sub-comp (sub-ex sub-id V) N)                                   ∥ k         ⟫

-- ... | inj₁ (Δ₁ , i₁ , Q₁) = inj₁ ( (Ψ ⊕ Δ₁) , {!i₁!} ,  ~>*-trans (⟪ Ψ ∥ push N (app P V) ∥ k ⟫ ~>⟨ ~>-push ⟩ Q₁) ( ⟪ Δ₁ ∥ var (var (wk-mem (ext-⊇-L {Δ = Δ₁}) (wk-mem (ext-⊇-L {Δ = Ψ}) i₁))) ∥ (_∷_ {Ψ = Ψ} (app P V) k) ⟫ ~>⟨ {!~>-var-pop-c!} ⟩ ( ⟪ {!!} ∥ var {A = A} (var {!!}) ∥ k ⟫ ■)) )
-- ... | inj₂ (V₁ , Q₁) with lt {Γ = Γ} {Ψ = Ψ} {M = app (sub-val (sub-ex sub-id V₁) P) (sub-val (sub-ex sub-id V₁) V)} {k = k}
-- ...   | inj₁ (Δ₂ , i₂ , Q₂) = inj₁ (Δ₂ , i₂ , (~>*-trans (⟪ Ψ ∥ push N (app P V) ∥ k ⟫ ~>⟨ ~>-push ⟩ Q₁) ( ⟪ ε ∥ return V₁ ∥ (_∷_ {Ψ = Ψ} (app P V) k) ⟫ ~>⟨ ~>-return-step' ⟩ Q₂)) )
-- ...   | inj₂ (V₂ , Q₂) = inj₂ (V₂ , (~>*-trans (⟪ Ψ ∥ push N (app P V) ∥ k ⟫ ~>⟨ ~>-push ⟩ Q₁) (⟪ ε ∥ return V₁ ∥ (_∷_ {Ψ = Ψ} (app P V) k) ⟫ ~>⟨ ~>-return-step' ⟩ Q₂)))
