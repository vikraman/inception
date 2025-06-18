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

{-
val-eval : Γ ⊢ᵛ A -> Γ ⊢ᵛ A
val-eval (var i) = var i
val-eval (lam x) = lam x
val-eval (pair V₁ V₂) = pair (val-eval V₁) (val-eval V₂)
val-eval (pm M W) with (val-eval M)
... | var i =  pm (var i) (val-eval W)
... | pair V₁ V₂ = sub-val (sub-ex (sub-ex sub-id V₁) V₂) (val-eval W)
... | pm M M₁ = pm (pm M M₁) (val-eval W)
val-eval unit = unit
-}

data Stack : (Γ : Ctx) → Set where
  nil : Stack ε
  _∷ᵛ_ : {Γ : Ctx} {A : Ty} -> (N : Γ ⊢ᵛ A) -> Stack Γ -> Stack Γ
  _∷ˢ_ : {Γ : Ctx} {A : Ty} -> (N : Γ ⊢ᶜ A) -> Stack Γ -> Stack (Γ ∙ `V)
  _∷ᵖ_ : {Γ : Ctx} {A B : Ty} -> (N : (Γ ∙ A) ⊢ᶜ B) -> Stack Γ -> Stack Γ

data State : Set where
  ⟪_∥_∥_∥_⟫ : {Γ : Ctx} -> {Δᵛ : Ctx} -> (Δ : Ctx) -> (Γ ⊕ Δ) ⊢ᶜ A -> ((Γ ⊕ Δᵛ) ⊕ Δ) ⊢ᶜ A -> Stack Γ -> State
  stuck : State

{-
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
-}

-------------------------------------------------------------

{-
-- {-# TERMINATING #-}
lt : {M : Γ ⊢ᶜ A} {k : Stack Γ}
     ->   ( ∃[ Δ ] ∃[ B ] ∃[ V ] (⟪ ε ∥ M ∥ k ⟫ ~>* ⟪ Δ ∥ var {A = B} (wk-val (ext-⊇-L {Δ = Δ}) V) ∥ k ⟫) )
        ⊎ ( ∃[ Δ ] ∃[ V ] (⟪ ε ∥ M ∥ k ⟫ ~>* ⟪ Δ ∥ return {A = A} (wk-val (ext-⊇-L {Δ = Δ}) V) ∥ k ⟫)
            ⊎ ( ⟪ ε ∥ M ∥ k ⟫ ~>* stuck ) )

lt {Γ = Γ} {A = A} {M = return x} {k = k} with ~>*-refl {M = ⟪ ε ∥ return x ∥ k ⟫}
... | M rewrite (sym (wk-val-id {x = x})) =  inj₂ (inj₁ ( ε , x ,  M ))

lt {Γ = Γ} {A = A} {M = var V} {k = k}  with ~>*-refl {M = ⟪ ε ∥ var V ∥ k ⟫}
... | M rewrite (sym (wk-val-id {x = V})) =  inj₁ ( ε , A , V ,  M )

lt {Γ = Γ} {A = A} {M = app (var i) V} {k = k} =  inj₂ (inj₂ ( ⟪ ε ∥ app (var i) V ∥ k ⟫ ~>⟨ ~>-app-var ⟩ (stuck ■)))

lt {Γ = Γ} {A = A} {M = app {A = B} (lam (return x)) V} {k = k} with ~>-app-lam {M = return x} {V = V} {k = k}
... | Y rewrite (sym (wk-val-id {x = (sub-val (sub-ex sub-id V) x)})) =  inj₂ (inj₁ ( ε , ((sub-val (sub-ex sub-id V) x) , ( ⟪ ε ∥ app (lam (return x)) V ∥ k ⟫ ~>⟨ Y ⟩ (⟪ ε ∥ return (wk-val wk-id (sub-val (sub-ex sub-id V) x)) ∥ k ⟫ ■)))))

lt {Γ = Γ} {A = A} {M = app (lam (pm V M)) W} {k = k} with lt {M = pm (sub-val (sub-ex sub-id W) V) (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-ex sub-id W)) (var (t h))) (var h)) M)} {k = k}
... | inj₁ (Δ , B , V' , R) = inj₁ (Δ , B , V' , ( ⟪ ε ∥ app (lam (pm V M)) W ∥ k ⟫ ~>⟨ ~>-app-lam ⟩ R))
... | inj₂ (inj₁ (Δ , V' , R)) = inj₂ (inj₁ (Δ , V' , ( ⟪ ε ∥ app (lam (pm V M)) W ∥ k ⟫ ~>⟨ ~>-app-lam ⟩ R)))
... | inj₂ (inj₂ R) = inj₂ (inj₂ ( ⟪ ε ∥ app (lam (pm V M)) W ∥ k ⟫ ~>⟨ ~>-app-lam ⟩ R))

lt {Γ = Γ} {A = A} {M = app (lam (push M N)) V} {k = k} with lt {M = push (sub-comp (sub-ex sub-id V) M) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-ex sub-id V)) (var h)) N)} {k = k}
... | inj₁ (Δ , B , V' , R) =  inj₁ (Δ , B , V' , ( ⟪ ε ∥ app (lam (push M N)) V ∥ k ⟫ ~>⟨ ~>-app-lam ⟩ R))
... | inj₂ (inj₁ (Δ , V' , R)) =  inj₂ (inj₁ (Δ , V' , ( ⟪ ε ∥ app (lam (push M N)) V ∥ k ⟫ ~>⟨ ~>-app-lam ⟩ R)))
... | inj₂ (inj₂ R) =  inj₂ (inj₂ ( ⟪ ε ∥ app (lam (push M N)) V ∥ k ⟫ ~>⟨ ~>-app-lam ⟩ R))

lt {Γ = Γ} {A = A} {M = app (lam (app V W)) Q} {k = k} with lt {M = app (sub-val (sub-ex sub-id Q) V) (sub-val (sub-ex sub-id Q) W)} {k = k}
... | inj₁ (Δ , B , V' , R) =  inj₁ (Δ , B , V' , ( ⟪ ε ∥ app (lam (app V W)) Q ∥ k ⟫ ~>⟨ ~>-app-lam ⟩ R))
... | inj₂ (inj₁ (Δ , V' , R)) =  inj₂ (inj₁ (Δ , V' , ( ⟪ ε ∥ app (lam (app V W)) Q ∥ k ⟫ ~>⟨ ~>-app-lam ⟩ R)))
... | inj₂ (inj₂ R) =  inj₂ (inj₂ ( ⟪ ε ∥ app (lam (app V W)) Q ∥ k ⟫ ~>⟨ ~>-app-lam ⟩ R))

lt {Γ = Γ} {A = A} {M = app (lam (var x)) V} {k = k} = {!!}
lt {Γ = Γ} {A = A} {M = app (lam (sub M M₁)) V} {k = k} = {!!}

lt {Γ = Γ} {A = A} {M = app (pm M M₁) V} {k = k} = {!!}

lt {Γ = Γ} {A = A} {M = pm x M} {k = k} = {!!}

lt {Γ = Γ} {A = A} {M = push M M₁} {k = k} = {!!}

lt {Γ = Γ} {A = A} {M = sub M M₁} {k = k} = {!!}

------------------------------------------------------

test : (M : Γ ⊢ᶜ `V) → Γ ⊢ᶜ `V
test M = sub (return (var h)) M
-}
