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
  A' B' C' D' : Ty

_⊕_ : Ctx → Ctx → Ctx
Γ ⊕ ε = Γ
Γ ⊕ (Δ ∙ x) = (Γ ⊕ Δ) ∙ x

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


val-eval : Γ ⊢ᵛ A -> Γ ⊢ᵛ A
val-eval (var i) = var i
val-eval (lam x) = lam x
val-eval (pair V₁ V₂) = pair (val-eval V₁) (val-eval V₂)
val-eval (pm M W) with (val-eval M)
... | var i =  pm (var i) (val-eval W)
... | pair V₁ V₂ = sub-val (sub-ex (sub-ex sub-id V₁) V₂) (val-eval W)
... | pm M M₁ = pm (pm M M₁) (val-eval W)
val-eval unit = unit

data Stack : (Γ : Ctx) → Set where
  nil : Stack ε
  _↦_∷_ : {Γ : Ctx} {A : Ty} -> (i : Γ ∙ `V ∋ `V) -> (N : Γ ⊢ᶜ A) -> Stack Γ -> Stack (Γ ∙ `V)
  _∷_ : {Γ : Ctx} {A B : Ty} -> (N : (Γ ∙ A) ⊢ᶜ B) -> Stack Γ -> Stack Γ

data State : Set where
  ⟪_∥_∥_⟫ : {Γ : Ctx} -> (Δ : Ctx) -> (Γ ⊕ Δ) ⊢ᶜ A -> Stack Γ -> State
  stuck : State

data _~>_ : State -> State -> Set where

  ~>-app-lam : {M : (Γ ∙ A) ⊢ᶜ B} {V : Γ ⊢ᵛ A} {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ ε            ∥ app (lam M) V                                                     ∥ k         ⟫
       ~> ⟪ ε            ∥ sub-comp (sub-ex sub-id V) M                                      ∥ k         ⟫

  ~>-app-pm : (P : Γ ⊢ᵛ A `× B) -> (W : (Γ ∙ A ∙ B) ⊢ᵛ C `⇒ D) {V : Γ ⊢ᵛ C}  {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ ε            ∥ app (pm P W) V                                                    ∥ k         ⟫
       ~> ⟪ ε            ∥ app (val-eval (pm P W)) V                                         ∥ k         ⟫

  ~>-app-var : {i : Γ ∋ C `⇒ D} {V : Γ ⊢ᵛ C}  {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ ε            ∥ app (var i) V                                                     ∥ k         ⟫
       ~> stuck

  ~>-pm-pair : {V1 : Γ ⊢ᵛ A} {V2 : Γ ⊢ᵛ B} {W : (Γ ∙ A ∙ B) ⊢ᶜ C} {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ ε            ∥ pm (pair V1 V2) W                                                 ∥ k         ⟫
       ~> ⟪ ε            ∥ sub-comp (sub-ex (sub-ex sub-id V1) V2) W                         ∥ k         ⟫

  ~>-pm-pm : {P : Γ ⊢ᵛ A' `× B'} {M : (Γ ∙ A' ∙ B') ⊢ᵛ A `× B} {W : (Γ ∙ A ∙ B) ⊢ᶜ C} {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ ε            ∥ pm (pm P M) W                                                     ∥ k         ⟫
       ~> ⟪ ε            ∥ pm (val-eval (pm P M)) W                                          ∥ k         ⟫

  ~>-pm-var : {i : Γ ∋ A `× B} {W : (Γ ∙ A ∙ B) ⊢ᶜ C} {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ ε            ∥ pm (var i) W                                                      ∥ k         ⟫
       ~> stuck

  ~>-push : {M : Γ  ⊢ᶜ A} {N : (Γ ∙ A) ⊢ᶜ B} {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ ε            ∥ push M N                                                          ∥ k         ⟫
       ~> ⟪ ε            ∥ M                                                                 ∥ N ∷ k     ⟫

  ~>-sub : {M : (Γ ∙ `V) ⊢ᶜ A} {N : Γ ⊢ᶜ A} {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ ε            ∥ sub M N                                                           ∥ k         ⟫
       ~> ⟪ ε            ∥ M                                                                 ∥ h ↦ N ∷ k ⟫

  ~>-var-pop-c : {i : Γ ∋ `V} {N : (Γ ∙ C) ⊢ᶜ B}  {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ            ∥ var {A = A} (var (wk-mem (ext-⊇-L {Γ = Γ} {Δ = Δ}) i))            ∥ N ∷ k     ⟫
       ~> ⟪ Δ            ∥ var {A = A} (var (wk-mem ext-⊇-L i))                              ∥ k         ⟫

  ~>-var-pop-k : {i : Γ ∋ `V} {N : Γ ⊢ᶜ B}  {k : Stack Γ}
    ----------------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ            ∥ var {A = A} (var (wk-mem ext-⊇-L (t i)))                                ∥ h ↦ N ∷ k ⟫
       ~> ⟪ (ε ∙ `V) ⊕ Δ ∥ var {A = A} (var (i-assoc {Γ} {ε ∙ `V} {Δ} (wk-mem ext-⊇-L (t i))))     ∥ k         ⟫

  ~>-var-pm : (V1 : Γ ⊢ᵛ A) -> (V2 : Γ ⊢ᵛ B) -> (W : (Γ ∙ A ∙ B) ⊢ᵛ `V)  {k : Stack Γ}
    ----------------------------------------------------------------------------------------------------------------
    ->    ⟪ ε            ∥ var {A = C} (pm (pair V1 V2) W)                                   ∥ k         ⟫
       ~> ⟪ ε            ∥ var {A = C} (sub-val (sub-ex (sub-ex sub-id V1) V2) W)            ∥ k         ⟫

  ~>-var-step : {N : Γ ⊢ᶜ B}  {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ            ∥ var {A = A} (var (wk-mem ext-⊇-L h))                              ∥ h ↦ N ∷ k ⟫
       ~> ⟪ ε            ∥ N                                                                 ∥ k         ⟫

  ~>-return-pop : {V : Γ ⊢ᵛ A} {N : Γ ⊢ᶜ B} {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ ∥ return (wk-val {(Γ ∙ `V) ⊕ Δ} {Γ ∙ `V} {A} (ext-⊇-L {Γ ∙ `V} {Δ}) ((wk-val {Γ ∙ `V} {Γ} {A} (ext-⊇-L) V)))         ∥ h ↦ N ∷ k ⟫
       ~> ⟪ (ε ∙ `V) ⊕ Δ ∥ return (wk-val {Γ ⊕ ((ε ∙ `V) ⊕ Δ)} {Γ} {A} (ext-⊇-L {Γ} {(ε ∙ `V) ⊕ Δ}) V)       ∥ k         ⟫

  ~>-return-step : {V : Γ ⊢ᵛ A} {N : (Γ ∙ A) ⊢ᶜ B} {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ            ∥ return (wk-val (ext-⊇-L {Γ} {Δ}) V)                               ∥ N ∷ k     ⟫
       ~> ⟪ ε            ∥  (sub-comp (sub-ex sub-id V) N)                                   ∥ k         ⟫

  ~>-return-stuck : {k : Stack Γ}
    ------------------------------------------------------------------------------------------------------
    ->    ⟪ Δ ∥ return (wk-val {(Γ ∙ `V) ⊕ Δ} {Γ ∙ `V} {`V} (ext-⊇-L {Γ ∙ `V} {Δ}) (var h))  ∥ h ↦ N ∷ k ⟫
       ~> stuck

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
-- wk-ε-id : {V : Γ ⊢ᵛ A} → wk-val (ext-⊇-L {Γ} {ε}) V ≡ V
-- wk-ε-id = wk-val-id

-- l1 : {V : Γ ⊢ᵛ A} {N : (Γ ∙ A) ⊢ᶜ B} {k : Stack Γ}
--      → ⟪ ε ∥ return (wk-val (ext-⊇-L {Γ} {ε}) V) ∥ N ∷ k ⟫ ~> ⟪ ε ∥ (sub-comp (sub-ex sub-id V) N) ∥ k ⟫
-- l1 = ~>-return-step
-- 
-- l2 : {V : Γ ⊢ᵛ A} {N : (Γ ∙ A) ⊢ᶜ B} {k : Stack Γ}
--      → ⟪ ε ∥ return V ∥ N ∷ k ⟫ ~> ⟪ ε ∥ (sub-comp (sub-ex sub-id V) N) ∥ k ⟫ ≡ ⟪ ε ∥ return (wk-val (ext-⊇-L {Γ} {ε}) V) ∥ N ∷ k ⟫ ~> ⟪ ε ∥ (sub-comp (sub-ex sub-id V) N) ∥ k ⟫
-- l2 {V = V} rewrite (wk-val-id {x = V}) = refl
-- 
-- l3 : {V : Γ ⊢ᵛ A} {N : (Γ ∙ A) ⊢ᶜ B} {k : Stack Γ}
--      → ⟪ ε ∥ return V ∥ N ∷ k ⟫ ~> ⟪ ε ∥ (sub-comp (sub-ex sub-id V) N) ∥ k ⟫
-- l3 {V = V} {N = N} {k = k} with l1 {V = V} {N = N} {k = k}
-- ... | L1 rewrite l2 {V = V} {N = N} {k = k} = L1
-- 
-- 
-- i-wk : (i : Γ ∋ `V) → (Γ ⊕ Δ) ∋ `V
-- i-wk {Γ} {Δ} i = wk-mem {Γ ⊕ Δ} {Γ} ext-⊇-L i
-- 
-- eq-wk : {i i' : Γ ∋ `V} → i ≡ i' → (i-wk {Δ = ε ∙ A} i) ≡ (i-wk {Δ = ε ∙ A} i')
-- eq-wk {i = i} {i' = i'} i≡i' = cong i-wk i≡i'

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

lt : {M : Γ ⊢ᶜ A} {k : Stack Γ}
     ->   ( ∃[ Δ ] ∃[ B ] ∃[ V ] (⟪ ε ∥ M ∥ k ⟫ ~>* ⟪ Δ ∥ var {A = B} (wk-val (ext-⊇-L {Δ = Δ}) V) ∥ k ⟫) )
        ⊎ ( ∃[ Δ ] ∃[ V ] (⟪ ε ∥ M ∥ k ⟫ ~>* ⟪ Δ ∥ return {A = A} (wk-val (ext-⊇-L {Δ = Δ}) V) ∥ k ⟫)
            ⊎ ( ⟪ ε ∥ M ∥ k ⟫ ~>* stuck ) )

lt {Γ = Γ} {A = A} {M = return x} {k = k} with ~>*-refl {M = ⟪ ε ∥ return x ∥ k ⟫}
... | M rewrite (sym (wk-val-id {x = x})) =  inj₂ (inj₁ ( ε , x ,  M ))

lt {Γ = Γ} {A = A} {M = var V} {k = k}  with ~>*-refl {M = ⟪ ε ∥ var V ∥ k ⟫}
... | M rewrite (sym (wk-val-id {x = V})) =  inj₁ ( ε , A , V ,  M )

lt {Γ = Γ} {A = A} {M = app (var i) V} {k = k} =  inj₂ (inj₂ ( ⟪ ε ∥ app (var i) V ∥ k ⟫ ~>⟨ ~>-app-var ⟩ (stuck ■)))
lt {Γ = Γ} {A = A} {M = app (lam x) V} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = app (pm M M₁) V} {k = k} = {!!}

lt {Γ = Γ} {A = A} {M = pm x M} {k = k} = {!!}

lt {Γ = Γ} {A = A} {M = push M M₁} {k = k} = {!!}

lt {Γ = Γ} {A = A} {M = sub M M₁} {k = k} = {!!}

{- 
lt {Γ = Γ} {A = A} {M = return x} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = pm x M} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = app x x₁} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = var x} {k = k} = {!!}

lt {Γ = Γ} {A = A} {M = sub N P} {k = k} with lt {M = N} {k = h ↦ P ∷ k}
... | inj₁ (Δ , B , h , Q) = {!!}
... | inj₁ (Δ , B , t i , Q) = {!!}
--inj₁ ( {!!} , {!!} , {!!} ,  ~>*-trans ( ⟪ ε ∥ sub N P ∥ k ⟫ ~>⟨ ~>-sub ⟩ Q) (⟪ Δ ∥ var (var (wk-mem ext-⊇-L i)) ∥ h ↦ P ∷ k ⟫ ~>⟨ {! ~>-var-pop-k!} ⟩ {!!}) )

-- What if we return the variable bound by sub?
-- Need to split on V.
... | inj₂ (Δ , V , Q) = inj₂ ( (ε ∙ `V) ⊕ Δ , {!!} ,  ~>*-trans (⟪ ε ∥ sub N P ∥ k ⟫ ~>⟨ ~>-sub ⟩ Q) (⟪ Δ ∥ return (wk-val ext-⊇-L V) ∥ h ↦ P ∷ k ⟫ ~>⟨ {!~>-return-pop'!} ⟩ ( {!!} ■)) )

lt {Γ = Γ} {A = A} {M = push N (return x)} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = push N (pm x P)} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = push N (push P P₁)} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = push N (var x)} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = push N (sub P P₁)} {k = k} = {!!}

lt {Γ = Γ} {A = A} {M = push {A = A₂} {B = A} N (app {A = A₁} {B = A} P V)} {k = k} with lt {M = N} {k = (app P V) ∷ k}
... | inj₁ (Δ₁ , B₁ , i₁ , Q₁) =  inj₁ (Δ₁ , B₁ , i₁ , ~>*-trans (⟪ ε ∥ push N (app P V) ∥ k ⟫ ~>⟨ ~>-push ⟩ Q₁) (⟪ Δ₁ ∥ var (var (wk-mem ext-⊇-L i₁)) ∥ app P V ∷ k ⟫ ~>⟨ ~>-var-pop-c ⟩ ( ⟪ Δ₁ ∥ var (var (wk-mem ext-⊇-L i₁)) ∥ k ⟫ ■)) )
... | inj₂ (Δ₁ , V₁ , Q₁) with lt {Γ = Γ} {M = app (sub-val (sub-ex sub-id V₁) P) (sub-val (sub-ex sub-id V₁) V)} {k = k}
...   | inj₁ (Δ₂ , B₂ , i₂ , Q₂) = inj₁ (Δ₂ , B₂ , i₂ , (~>*-trans ( ⟪ ε ∥ push N (app P V) ∥ k ⟫ ~>⟨ ~>-push ⟩ Q₁) ( ⟪ Δ₁ ∥ return (wk-val ext-⊇-L V₁) ∥ (app P V) ∷ k ⟫ ~>⟨ ~>-return-step ⟩ Q₂)) )
...   | inj₂ (Δ₂ , V₂ , Q₂) = inj₂ (Δ₂ , V₂ , (~>*-trans (⟪ ε ∥ push N (app P V) ∥ k ⟫ ~>⟨ ~>-push ⟩ Q₁) (⟪ Δ₁ ∥ return (wk-val ext-⊇-L V₁) ∥ (app P V) ∷ k ⟫ ~>⟨ ~>-return-step ⟩ Q₂)))

-}


--  var : (i : Γ ∋ `V)
--      --------------
--      -> Γ ⊢ᵛ `V
--
--  unit : (i : Γ ∋ `Unit)
--       --------------
--       -> Γ ⊢ᵛ `Unit

------------------------------------------------------

test : (M : Γ ⊢ᶜ `V) → Γ ⊢ᶜ `V
test M = sub (return (var h)) M
