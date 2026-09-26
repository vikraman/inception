{-# OPTIONS --no-postfix-projections #-}

module Inception.LamPm.CK where

open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym)
open Eq.≡-Reasoning

open import Inception.LamPm.Syntax
open import Inception.Prelude
open Inception.Prelude.RTC

--------------------------------------------------------------------------
-- stacks, configurations, transitions

infixr 20 _∷_
infixr 20 _pm∷_
infixr 20 _pmᵛ∷_

syntax Stk Γ A B = Γ ⊢ᵏ A ⇒ B

data Stk (Γ : Ctx) : Ty → Ty → Set where

  ε      : Γ ⊢ᵏ A ⇒ A

  _∷_    : (N : (Γ ∙ A) ⊢ᶜ B) → (K : Γ ⊢ᵏ B ⇒ C)
         → Γ ⊢ᵏ A ⇒ C

  _pm∷_  : (N : (Γ ∙ A ∙ B) ⊢ᶜ C) → (K : Γ ⊢ᵏ C ⇒ D)
         → Γ ⊢ᵏ (A `× B) ⇒ D

  _pmᵛ∷_ : (W : (Γ ∙ A ∙ B) ⊢ᵛ C) → (K : Γ ⊢ᵏ C ⇒ D)
         → Γ ⊢ᵏ (A `× B) ⇒ D

infix 5 ⟨_∥_⟩
infix 5 [_∥_]

data Cfg (Γ : Ctx) (B : Ty) : Set where

  ⟨_∥_⟩ : (M : Γ ⊢ᶜ A) → (K : Γ ⊢ᵏ A ⇒ B)
        → Cfg Γ B

  [_∥_] : (V : Γ ⊢ᵛ A) → (K : Γ ⊢ᵏ A ⇒ B)
        → Cfg Γ B

infix 5 _→ᵏ_

data _→ᵏ_ : Cfg Γ B → Cfg Γ B → Set where

  push-step      : {M : Γ ⊢ᶜ A} {N : (Γ ∙ A) ⊢ᶜ B} {K : Γ ⊢ᵏ B ⇒ C}
                 → ⟨ push M N ∥ K ⟩ →ᵏ ⟨ M ∥ N ∷ K ⟩

  return-step    : {V : Γ ⊢ᵛ A} {N : (Γ ∙ A) ⊢ᶜ B} {K : Γ ⊢ᵏ B ⇒ C}
                 → ⟨ return V ∥ N ∷ K ⟩ →ᵏ ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩

  pm-step        : {V : Γ ⊢ᵛ A `× B} {N : (Γ ∙ A ∙ B) ⊢ᶜ C} {K : Γ ⊢ᵏ C ⇒ D}
                 → ⟨ pm V N ∥ K ⟩ →ᵏ [ V ∥ N pm∷ K ]

  pm-pair-step   : {V : Γ ⊢ᵛ A} {W : Γ ⊢ᵛ B} {N : (Γ ∙ A ∙ B) ⊢ᶜ C} {K : Γ ⊢ᵏ C ⇒ D}
                 → [ pair V W ∥ N pm∷ K ] →ᵏ ⟨ sub-comp (sub-ex (sub-ex sub-id V) W) N ∥ K ⟩

  pm-val-step    : {V : Γ ⊢ᵛ A `× B} {W : (Γ ∙ A ∙ B) ⊢ᵛ C} {K : Γ ⊢ᵏ C ⇒ D}
                 → [ pm V W ∥ K ] →ᵏ [ V ∥ W pmᵛ∷ K ]

  pmᵛ-pair-step  : {V₁ : Γ ⊢ᵛ A} {V₂ : Γ ⊢ᵛ B} {W : (Γ ∙ A ∙ B) ⊢ᵛ C} {K : Γ ⊢ᵏ C ⇒ D}
                 → [ pair V₁ V₂ ∥ W pmᵛ∷ K ] →ᵏ [ sub-val (sub-ex (sub-ex sub-id V₁) V₂) W ∥ K ]

  app-lam-step   : {N : (Γ ∙ A) ⊢ᶜ B} {V : Γ ⊢ᵛ A} {K : Γ ⊢ᵏ B ⇒ C}
                 → ⟨ app (lam N) V ∥ K ⟩ →ᵏ ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩

  app-pm-step    : {V : Γ ⊢ᵛ X `× Y} {W : (Γ ∙ X ∙ Y) ⊢ᵛ A `⇒ B} {W₁ : Γ ⊢ᵛ A} {K : Γ ⊢ᵏ B ⇒ C}
                 → ⟨ app (pm V W) W₁ ∥ K ⟩ →ᵏ ⟨ pm V (app W (wk-val (wk-wk (wk-wk wk-id)) W₁)) ∥ K ⟩

--------------------------------------------------------------------------
-- accessibility

data SN {Γ B} (σ : Cfg Γ B) : Set where
  sn : (∀ {σ'} → σ →ᵏ σ' → SN σ') → SN σ

infix 5 _↠ᵏ_

_↠ᵏ_ : {Γ : Ctx} {B : Ty} → Cfg Γ B → Cfg Γ B → Set
_↠ᵏ_ {Γ} {B} = _~>*_ (_→ᵏ_ {Γ = Γ} {B = B})

--------------------------------------------------------------------------
-- weakening a configuration

wk-stk : {Γ' : Ctx} → Γ' ⊇ Γ → Γ ⊢ᵏ A ⇒ B → Γ' ⊢ᵏ A ⇒ B
wk-stk π ε          = ε
wk-stk π (N ∷ K)    = wk-comp (wk-cong π) N ∷ wk-stk π K
wk-stk π (N pm∷ K)  = wk-comp (wk-cong (wk-cong π)) N pm∷ wk-stk π K
wk-stk π (W pmᵛ∷ K) = wk-val (wk-cong (wk-cong π)) W pmᵛ∷ wk-stk π K

wk-cfg : {Γ' : Ctx} → Γ' ⊇ Γ → Cfg Γ B → Cfg Γ' B
wk-cfg π ⟨ M ∥ K ⟩ = ⟨ wk-comp π M ∥ wk-stk π K ⟩
wk-cfg π [ V ∥ K ] = [ wk-val π V ∥ wk-stk π K ]

wk-ins2 : {Γ Γ' : Ctx} {X Y A : Ty} (π : Γ' ⊇ Γ) (V : Γ ⊢ᵛ A) →
        wk-val (wk-wk {A = Y} (wk-wk {A = X} wk-id)) (wk-val π V) ≡ wk-val (wk-cong {A = Y} (wk-cong {A = X} π)) (wk-val (wk-wk {A = Y} (wk-wk {A = X} wk-id)) V)
wk-ins2 {X = X} {Y = Y} π V = begin
    wk-val (wk-wk {A = Y} (wk-wk {A = X} wk-id)) (wk-val π V)
  ≡⟨ wk-val-trans V (wk-wk {A = Y} (wk-wk {A = X} wk-id)) π ⟩
    wk-val (wk-wk {A = Y} (wk-wk {A = X} (wk-trans wk-id π))) V
  ≡⟨ cong (λ x → wk-val (wk-wk {A = Y} (wk-wk {A = X} x)) V) (wk-trans-idl π) ⟩
    wk-val (wk-wk {A = Y} (wk-wk {A = X} π)) V
  ≡˘⟨ cong (λ x → wk-val (wk-wk {A = Y} (wk-wk {A = X} x)) V) (wk-trans-idr π) ⟩
    wk-val (wk-wk {A = Y} (wk-wk {A = X} (wk-trans π wk-id))) V
  ≡˘⟨ wk-val-trans V (wk-cong {A = Y} (wk-cong {A = X} π)) (wk-wk {A = Y} (wk-wk {A = X} wk-id)) ⟩
    wk-val (wk-cong {A = Y} (wk-cong {A = X} π)) (wk-val (wk-wk {A = Y} (wk-wk {A = X} wk-id)) V) ∎

wk-step : {Γ' : Ctx} (π : Γ' ⊇ Γ) {σ σ' : Cfg Γ B} → σ →ᵏ σ' → wk-cfg π σ →ᵏ wk-cfg π σ'
wk-step π push-step = push-step
wk-step π (return-step {V = V} {N = N} {K = K}) =
  Eq.subst (λ x → ⟨ return (wk-val π V) ∥ wk-comp (wk-cong π) N ∷ wk-stk π K ⟩ →ᵏ ⟨ x ∥ wk-stk π K ⟩)
           (wk-beta-1 π V N) return-step
wk-step π pm-step = pm-step
wk-step π (pm-pair-step {V = V} {W = W} {N = N} {K = K}) =
  Eq.subst (λ x → [ pair (wk-val π V) (wk-val π W) ∥ wk-comp (wk-cong (wk-cong π)) N pm∷ wk-stk π K ] →ᵏ ⟨ x ∥ wk-stk π K ⟩)
           (wk-beta-pmᶜ π V W N) pm-pair-step
wk-step π pm-val-step = pm-val-step
wk-step π (pmᵛ-pair-step {V₁ = V₁} {V₂ = V₂} {W = W} {K = K}) =
  Eq.subst (λ x → [ pair (wk-val π V₁) (wk-val π V₂) ∥ wk-val (wk-cong (wk-cong π)) W pmᵛ∷ wk-stk π K ] →ᵏ [ x ∥ wk-stk π K ])
           (wk-beta-pmᵛ π V₁ V₂ W) pmᵛ-pair-step
wk-step π (app-lam-step {N = N} {V = V} {K = K}) =
  Eq.subst (λ x → ⟨ app (lam (wk-comp (wk-cong π) N)) (wk-val π V) ∥ wk-stk π K ⟩ →ᵏ ⟨ x ∥ wk-stk π K ⟩)
           (wk-beta-1 π V N) app-lam-step
wk-step π (app-pm-step {X = X} {Y = Y} {V = V} {W = W} {W₁ = W₁} {K = K}) =
  Eq.subst (λ x → ⟨ app (pm (wk-val π V) (wk-val (wk-cong (wk-cong π)) W)) (wk-val π W₁) ∥ wk-stk π K ⟩ →ᵏ ⟨ pm (wk-val π V) x ∥ wk-stk π K ⟩)
           (Eq.cong (app (wk-val (wk-cong (wk-cong π)) W)) (wk-ins2 {X = X} {Y = Y} π W₁))
           app-pm-step

wk-reflect : {Γ' : Ctx} (π : Γ' ⊇ Γ) {σ : Cfg Γ B} {σ₁ : Cfg Γ' B}
           → wk-cfg π σ →ᵏ σ₁ → Σ[ σ' ∈ Cfg Γ B ] (σ →ᵏ σ') × (σ₁ ≡ wk-cfg π σ')
wk-reflect π {σ = ⟨ push M N ∥ K ⟩} push-step = ⟨ M ∥ N ∷ K ⟩ , push-step , refl
wk-reflect π {σ = ⟨ return V ∥ ε ⟩} ()
wk-reflect π {σ = ⟨ return V ∥ N ∷ K ⟩} return-step =
  ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩ , return-step ,
  Eq.cong (λ x → ⟨ x ∥ wk-stk π K ⟩) (wk-beta-1 π V N)
wk-reflect π {σ = ⟨ return V ∥ N pm∷ K ⟩} ()
wk-reflect π {σ = ⟨ return V ∥ W pmᵛ∷ K ⟩} ()
wk-reflect π {σ = ⟨ pm V N ∥ K ⟩} pm-step = [ V ∥ N pm∷ K ] , pm-step , refl
wk-reflect π {σ = ⟨ app (var i) V ∥ K ⟩} ()
wk-reflect π {σ = ⟨ app (lam N) V ∥ K ⟩} app-lam-step =
  ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩ , app-lam-step ,
  Eq.cong (λ x → ⟨ x ∥ wk-stk π K ⟩) (wk-beta-1 π V N)
wk-reflect π {σ = ⟨ app (pm V₁ W) V ∥ K ⟩} app-pm-step =
  ⟨ pm V₁ (app W (wk-val (wk-wk (wk-wk wk-id)) V)) ∥ K ⟩ , app-pm-step ,
  Eq.cong (λ x → ⟨ pm (wk-val π V₁) x ∥ wk-stk π K ⟩)
          (Eq.cong (app (wk-val (wk-cong (wk-cong π)) W)) (wk-ins2 π V))
wk-reflect π {σ = [ pair V W ∥ ε ]} ()
wk-reflect π {σ = [ pair V W ∥ N ∷ K ]} ()
wk-reflect π {σ = [ pair V W ∥ N pm∷ K ]} pm-pair-step =
  ⟨ sub-comp (sub-ex (sub-ex sub-id V) W) N ∥ K ⟩ , pm-pair-step ,
  Eq.cong (λ x → ⟨ x ∥ wk-stk π K ⟩) (wk-beta-pmᶜ π V W N)
wk-reflect π {σ = [ pair V₁ V₂ ∥ W pmᵛ∷ K ]} pmᵛ-pair-step =
  [ sub-val (sub-ex (sub-ex sub-id V₁) V₂) W ∥ K ] , pmᵛ-pair-step ,
  Eq.cong (λ x → [ x ∥ wk-stk π K ]) (wk-beta-pmᵛ π V₁ V₂ W)
wk-reflect π {σ = [ pm V W ∥ K ]} pm-val-step = [ V ∥ W pmᵛ∷ K ] , pm-val-step , refl
wk-reflect π {σ = [ lam N ∥ K ]} ()
wk-reflect π {σ = [ unit ∥ K ]} ()
wk-reflect π {σ = [ var i ∥ K ]} ()

SN-wk : {Γ' : Ctx} (π : Γ' ⊇ Γ) {σ : Cfg Γ B} → SN σ → SN (wk-cfg π σ)
SN-wk π (sn f) = sn (λ step →
  let (σ' , σ-step , eq) = wk-reflect π step
  in Eq.subst SN (sym eq) (SN-wk π (f σ-step)))

--------------------------------------------------------------------------
-- reducibility candidates

graft : Γ ⊢ᵏ A ⇒ D → Γ ⊢ᵏ D ⇒ C → Γ ⊢ᵏ A ⇒ C
graft ε          K = K
graft (N ∷ L)   K  = N ∷ graft L K
graft (N pm∷ L)  K = N pm∷ graft L K
graft (W pmᵛ∷ L) K = W pmᵛ∷ graft L K

Redᵛ : (A : Ty) → Γ ⊢ᵛ A → Set
Redᶜ : (A : Ty) → Γ ⊢ᶜ A → Set

Redᵛ `Unit       V = SN [ V ∥ ε ]
Redᵛ (A `× B)    V = SN [ V ∥ ε ] × (∀ {V₁ V₂} → [ V ∥ ε ] ↠ᵏ [ pair V₁ V₂ ∥ ε ] → Redᵛ A V₁ × Redᵛ B V₂)
Redᵛ {Γ} (A `⇒ B) V = SN [ V ∥ ε ] × (∀ {Γ'} (π : Γ' ⊇ Γ) {W : Γ' ⊢ᵛ A} → Redᵛ A W → Redᶜ B (app (wk-val π V) W))

Redᶜ A M = SN ⟨ M ∥ ε ⟩ × (∀ {V} → ⟨ M ∥ ε ⟩ ↠ᵏ ⟨ return V ∥ ε ⟩ → Redᵛ A V)

Red→SNᵛ : (A : Ty) (V : Γ ⊢ᵛ A) → Redᵛ A V → SN [ V ∥ ε ]
Red→SNᵛ `Unit    V r = r
Red→SNᵛ (A `× B) V r = proj₁ r
Red→SNᵛ (A `⇒ B) V r = proj₁ r

Red→SNᶜ : (A : Ty) (M : Γ ⊢ᶜ A) → Redᶜ A M → SN ⟨ M ∥ ε ⟩
Red→SNᶜ A M (snM , ret) = snM

Red→RTNᶜ : (A : Ty) (M : Γ ⊢ᶜ A) → Redᶜ A M → (∀ {V} → ⟨ M ∥ ε ⟩ ↠ᵏ ⟨ return V ∥ ε ⟩ → Redᵛ A V)
Red→RTNᶜ A M (snM , ret) = ret

mutual
  SN-ext∷-C : {E : Ty} {M : Γ ⊢ᶜ A} {L : Γ ⊢ᵏ A ⇒ D} {N : (Γ ∙ D) ⊢ᶜ E} {K : Γ ⊢ᵏ E ⇒ C}
            → SN ⟨ M ∥ L ⟩
            → (∀ {V} → ⟨ M ∥ L ⟩ ↠ᵏ ⟨ return V ∥ ε ⟩ → Redᵛ D V)
            → (∀ {V} → Redᵛ D V → SN ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩)
            → SN ⟨ M ∥ graft L (N ∷ K) ⟩
  SN-ext∷-C {M = push M N} (sn f) rtn H =
    sn (λ { push-step → SN-ext∷-C (f push-step) (λ ch → rtn (_ ~>⟨ push-step ⟩ ch)) H })
  SN-ext∷-C {M = app (var i) V} (sn f) rtn H = sn (λ ())
  SN-ext∷-C {M = app (lam N) V} (sn f) rtn H =
    sn (λ { app-lam-step → SN-ext∷-C (f app-lam-step) (λ ch → rtn (_ ~>⟨ app-lam-step ⟩ ch)) H })
  SN-ext∷-C {M = app (pm V₀ W) V} (sn f) rtn H =
    sn (λ { app-pm-step → SN-ext∷-C (f app-pm-step) (λ ch → rtn (_ ~>⟨ app-pm-step ⟩ ch)) H })
  SN-ext∷-C {M = pm V N} (sn f) rtn H =
    sn (λ { pm-step → SN-ext∷-V (f pm-step) (λ ch → rtn (_ ~>⟨ pm-step ⟩ ch)) H })
  SN-ext∷-C {M = return V} {L = ε} (sn f) rtn H =
    sn (λ { return-step → H (rtn (_ ◼)) })
  SN-ext∷-C {M = return V} {L = N ∷ L} (sn f) rtn H =
    sn (λ { return-step → SN-ext∷-C (f return-step) (λ ch → rtn (_ ~>⟨ return-step ⟩ ch)) H })
  SN-ext∷-C {M = return V} {L = N pm∷ L} (sn f) rtn H = sn (λ ())
  SN-ext∷-C {M = return V} {L = W pmᵛ∷ L} (sn f) rtn H = sn (λ ())

  SN-ext∷-V : {E : Ty} {V : Γ ⊢ᵛ A} {L : Γ ⊢ᵏ A ⇒ D} {N : (Γ ∙ D) ⊢ᶜ E} {K : Γ ⊢ᵏ E ⇒ C}
            → SN [ V ∥ L ]
            → (∀ {W} → [ V ∥ L ] ↠ᵏ ⟨ return W ∥ ε ⟩ → Redᵛ D W)
            → (∀ {W} → Redᵛ D W → SN ⟨ sub-comp (sub-ex sub-id W) N ∥ K ⟩)
            → SN [ V ∥ graft L (N ∷ K) ]
  SN-ext∷-V {V = var i} (sn f) rtn H = sn (λ ())
  SN-ext∷-V {V = lam N} (sn f) rtn H = sn (λ ())
  SN-ext∷-V {V = unit} (sn f) rtn H = sn (λ ())
  SN-ext∷-V {V = pm V W} (sn f) rtn H =
    sn (λ { pm-val-step → SN-ext∷-V (f pm-val-step) (λ ch → rtn (_ ~>⟨ pm-val-step ⟩ ch)) H })
  SN-ext∷-V {V = pair V W} {L = ε} (sn f) rtn H = sn (λ ())
  SN-ext∷-V {V = pair V W} {L = N ∷ L} (sn f) rtn H = sn (λ ())
  SN-ext∷-V {V = pair V W} {L = N pm∷ L} (sn f) rtn H =
    sn (λ { pm-pair-step → SN-ext∷-C (f pm-pair-step) (λ ch → rtn (_ ~>⟨ pm-pair-step ⟩ ch)) H })
  SN-ext∷-V {V = pair V₁ V₂} {L = W pmᵛ∷ L} (sn f) rtn H =
    sn (λ { pmᵛ-pair-step → SN-ext∷-V (f pmᵛ-pair-step) (λ ch → rtn (_ ~>⟨ pmᵛ-pair-step ⟩ ch)) H })

mutual
  RTN-ext∷-C : {E : Ty} {M : Γ ⊢ᶜ A} {L : Γ ⊢ᵏ A ⇒ D} {N : (Γ ∙ D) ⊢ᶜ E} {K : Γ ⊢ᵏ E ⇒ C}
             → (∀ {V} → ⟨ M ∥ L ⟩ ↠ᵏ ⟨ return V ∥ ε ⟩ → Redᵛ D V)
             → (∀ {V} → Redᵛ D V → ∀ {W} → ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩ ↠ᵏ ⟨ return W ∥ ε ⟩ → Redᵛ C W)
             → {W : _} → ⟨ M ∥ graft L (N ∷ K) ⟩ ↠ᵏ ⟨ return W ∥ ε ⟩ → Redᵛ C W
  RTN-ext∷-C {M = push M N} rtn H (_ ~>⟨ push-step ⟩ rest) =
    RTN-ext∷-C (λ ch → rtn (_ ~>⟨ push-step ⟩ ch)) H rest
  RTN-ext∷-C {M = app (var i) V} rtn H (_ ~>⟨ () ⟩ rest)
  RTN-ext∷-C {M = app (lam N) V} rtn H (_ ~>⟨ app-lam-step ⟩ rest) =
    RTN-ext∷-C (λ ch → rtn (_ ~>⟨ app-lam-step ⟩ ch)) H rest
  RTN-ext∷-C {M = app (pm V₀ W) V} rtn H (_ ~>⟨ app-pm-step ⟩ rest) =
    RTN-ext∷-C (λ ch → rtn (_ ~>⟨ app-pm-step ⟩ ch)) H rest
  RTN-ext∷-C {M = pm V N} rtn H (_ ~>⟨ pm-step ⟩ rest) =
    RTN-ext∷-V (λ ch → rtn (_ ~>⟨ pm-step ⟩ ch)) H rest
  RTN-ext∷-C {M = return V} {L = ε} rtn H (_ ~>⟨ return-step ⟩ rest) = H (rtn (_ ◼)) rest
  RTN-ext∷-C {M = return V} {L = N ∷ L} rtn H (_ ~>⟨ return-step ⟩ rest) =
    RTN-ext∷-C (λ ch → rtn (_ ~>⟨ return-step ⟩ ch)) H rest
  RTN-ext∷-C {M = return V} {L = N pm∷ L} rtn H (_ ~>⟨ () ⟩ rest)
  RTN-ext∷-C {M = return V} {L = W pmᵛ∷ L} rtn H (_ ~>⟨ () ⟩ rest)

  RTN-ext∷-V : {E : Ty} {V : Γ ⊢ᵛ A} {L : Γ ⊢ᵏ A ⇒ D} {N : (Γ ∙ D) ⊢ᶜ E} {K : Γ ⊢ᵏ E ⇒ C}
             → (∀ {V₁} → [ V ∥ L ] ↠ᵏ ⟨ return V₁ ∥ ε ⟩ → Redᵛ D V₁)
             → (∀ {V₁} → Redᵛ D V₁ → ∀ {V₂} → ⟨ sub-comp (sub-ex sub-id V₁) N ∥ K ⟩ ↠ᵏ ⟨ return V₂ ∥ ε ⟩ → Redᵛ C V₂)
             → {V₂ : _} → [ V ∥ graft L (N ∷ K) ] ↠ᵏ ⟨ return V₂ ∥ ε ⟩ → Redᵛ C V₂
  RTN-ext∷-V {V = var i} rtn H (_ ~>⟨ () ⟩ rest)
  RTN-ext∷-V {V = lam N} rtn H (_ ~>⟨ () ⟩ rest)
  RTN-ext∷-V {V = unit} rtn H (_ ~>⟨ () ⟩ rest)
  RTN-ext∷-V {V = pm V W} rtn H (_ ~>⟨ pm-val-step ⟩ rest) =
    RTN-ext∷-V (λ ch → rtn (_ ~>⟨ pm-val-step ⟩ ch)) H rest
  RTN-ext∷-V {V = pair V W} {L = ε} rtn H (_ ~>⟨ () ⟩ rest)
  RTN-ext∷-V {V = pair V W} {L = N ∷ L} rtn H (_ ~>⟨ () ⟩ rest)
  RTN-ext∷-V {V = pair V W} {L = N pm∷ L} rtn H (_ ~>⟨ pm-pair-step ⟩ rest) =
    RTN-ext∷-C (λ ch → rtn (_ ~>⟨ pm-pair-step ⟩ ch)) H rest
  RTN-ext∷-V {V = pair V₁ V₂} {L = W pmᵛ∷ L} rtn H (_ ~>⟨ pmᵛ-pair-step ⟩ rest) =
    RTN-ext∷-V (λ ch → rtn (_ ~>⟨ pmᵛ-pair-step ⟩ ch)) H rest

exp-push : {M : Γ ⊢ᶜ A} {N : (Γ ∙ A) ⊢ᶜ B}
         → Redᶜ A M → (∀ {V} → Redᵛ A V → Redᶜ B (sub-comp (sub-ex sub-id V) N))
         → Redᶜ B (push M N)
exp-push {M = M} {N} rM H =
  sn (λ { push-step → SN-ext∷-C (Red→SNᶜ _ _ rM) (Red→RTNᶜ _ _ rM) (λ {V} rv → Red→SNᶜ _ _ (H rv)) }) ,
  λ { (_ ~>⟨ push-step ⟩ rest) → RTN-ext∷-C (Red→RTNᶜ _ _ rM) (λ {V} rv → Red→RTNᶜ _ _ (H rv)) rest }

mutual
  SN-ext-pm∷-C : {X Y E : Ty} {M : Γ ⊢ᶜ A} {L : Γ ⊢ᵏ A ⇒ (X `× Y)} {N : (Γ ∙ X ∙ Y) ⊢ᶜ E} {K : Γ ⊢ᵏ E ⇒ C}
               → SN ⟨ M ∥ L ⟩
               → (∀ {V W} → ⟨ M ∥ L ⟩ ↠ᵏ [ pair V W ∥ ε ] → Redᵛ X V × Redᵛ Y W)
               → (∀ {V W} → Redᵛ X V → Redᵛ Y W → SN ⟨ sub-comp (sub-ex (sub-ex sub-id V) W) N ∥ K ⟩)
               → SN ⟨ M ∥ graft L (N pm∷ K) ⟩
  SN-ext-pm∷-C {M = push M N} (sn f) rtn H =
    sn (λ { push-step → SN-ext-pm∷-C (f push-step) (λ ch → rtn (_ ~>⟨ push-step ⟩ ch)) H })
  SN-ext-pm∷-C {M = app (var i) V} (sn f) rtn H = sn (λ ())
  SN-ext-pm∷-C {M = app (lam N) V} (sn f) rtn H =
    sn (λ { app-lam-step → SN-ext-pm∷-C (f app-lam-step) (λ ch → rtn (_ ~>⟨ app-lam-step ⟩ ch)) H })
  SN-ext-pm∷-C {M = app (pm V₀ W) V} (sn f) rtn H =
    sn (λ { app-pm-step → SN-ext-pm∷-C (f app-pm-step) (λ ch → rtn (_ ~>⟨ app-pm-step ⟩ ch)) H })
  SN-ext-pm∷-C {M = pm V N} (sn f) rtn H =
    sn (λ { pm-step → SN-ext-pm∷-V (f pm-step) (λ ch → rtn (_ ~>⟨ pm-step ⟩ ch)) H })
  SN-ext-pm∷-C {M = return V} {L = ε} (sn f) rtn H = sn (λ ())
  SN-ext-pm∷-C {M = return V} {L = N ∷ L} (sn f) rtn H =
    sn (λ { return-step → SN-ext-pm∷-C (f return-step) (λ ch → rtn (_ ~>⟨ return-step ⟩ ch)) H })
  SN-ext-pm∷-C {M = return V} {L = N pm∷ L} (sn f) rtn H = sn (λ ())
  SN-ext-pm∷-C {M = return V} {L = W pmᵛ∷ L} (sn f) rtn H = sn (λ ())

  SN-ext-pm∷-V : {X Y E : Ty} {V : Γ ⊢ᵛ A} {L : Γ ⊢ᵏ A ⇒ (X `× Y)} {N : (Γ ∙ X ∙ Y) ⊢ᶜ E} {K : Γ ⊢ᵏ E ⇒ C}
               → SN [ V ∥ L ]
               → (∀ {V₁ V₂} → [ V ∥ L ] ↠ᵏ [ pair V₁ V₂ ∥ ε ] → Redᵛ X V₁ × Redᵛ Y V₂)
               → (∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → SN ⟨ sub-comp (sub-ex (sub-ex sub-id V₁) V₂) N ∥ K ⟩)
               → SN [ V ∥ graft L (N pm∷ K) ]
  SN-ext-pm∷-V {V = var i} (sn f) rtn H = sn (λ ())
  SN-ext-pm∷-V {V = lam N} (sn f) rtn H = sn (λ ())
  SN-ext-pm∷-V {V = unit} (sn f) rtn H = sn (λ ())
  SN-ext-pm∷-V {V = pm V W} (sn f) rtn H =
    sn (λ { pm-val-step → SN-ext-pm∷-V (f pm-val-step) (λ ch → rtn (_ ~>⟨ pm-val-step ⟩ ch)) H })
  SN-ext-pm∷-V {V = pair V W} {L = ε} (sn f) rtn H =
    sn (λ { pm-pair-step → H (proj₁ (rtn (_ ◼))) (proj₂ (rtn (_ ◼))) })
  SN-ext-pm∷-V {V = pair V W} {L = N ∷ L} (sn f) rtn H = sn (λ ())
  SN-ext-pm∷-V {V = pair V W} {L = N pm∷ L} (sn f) rtn H =
    sn (λ { pm-pair-step → SN-ext-pm∷-C (f pm-pair-step) (λ ch → rtn (_ ~>⟨ pm-pair-step ⟩ ch)) H })
  SN-ext-pm∷-V {V = pair V₁ V₂} {L = W pmᵛ∷ L} (sn f) rtn H =
    sn (λ { pmᵛ-pair-step → SN-ext-pm∷-V (f pmᵛ-pair-step) (λ ch → rtn (_ ~>⟨ pmᵛ-pair-step ⟩ ch)) H })

mutual
  RTN-ext-pm∷-C : {X Y E : Ty} {M : Γ ⊢ᶜ A} {L : Γ ⊢ᵏ A ⇒ (X `× Y)} {N : (Γ ∙ X ∙ Y) ⊢ᶜ E} {K : Γ ⊢ᵏ E ⇒ C}
                → (∀ {V₁ V₂} → ⟨ M ∥ L ⟩ ↠ᵏ [ pair V₁ V₂ ∥ ε ] → Redᵛ X V₁ × Redᵛ Y V₂)
                → (∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → ∀ {W} → ⟨ sub-comp (sub-ex (sub-ex sub-id V₁) V₂) N ∥ K ⟩ ↠ᵏ ⟨ return W ∥ ε ⟩ → Redᵛ C W)
                → {W : _} → ⟨ M ∥ graft L (N pm∷ K) ⟩ ↠ᵏ ⟨ return W ∥ ε ⟩ → Redᵛ C W
  RTN-ext-pm∷-C {M = push M N} rtn H (_ ~>⟨ push-step ⟩ rest) =
    RTN-ext-pm∷-C (λ ch → rtn (_ ~>⟨ push-step ⟩ ch)) H rest
  RTN-ext-pm∷-C {M = app (var i) V} rtn H (_ ~>⟨ () ⟩ rest)
  RTN-ext-pm∷-C {M = app (lam N) V} rtn H (_ ~>⟨ app-lam-step ⟩ rest) =
    RTN-ext-pm∷-C (λ ch → rtn (_ ~>⟨ app-lam-step ⟩ ch)) H rest
  RTN-ext-pm∷-C {M = app (pm V₀ W) V} rtn H (_ ~>⟨ app-pm-step ⟩ rest) =
    RTN-ext-pm∷-C (λ ch → rtn (_ ~>⟨ app-pm-step ⟩ ch)) H rest
  RTN-ext-pm∷-C {M = pm V N} rtn H (_ ~>⟨ pm-step ⟩ rest) =
    RTN-ext-pm∷-V (λ ch → rtn (_ ~>⟨ pm-step ⟩ ch)) H rest
  RTN-ext-pm∷-C {M = return V} {L = ε} rtn H (_ ~>⟨ () ⟩ rest)
  RTN-ext-pm∷-C {M = return V} {L = N ∷ L} rtn H (_ ~>⟨ return-step ⟩ rest) =
    RTN-ext-pm∷-C (λ ch → rtn (_ ~>⟨ return-step ⟩ ch)) H rest
  RTN-ext-pm∷-C {M = return V} {L = N pm∷ L} rtn H (_ ~>⟨ () ⟩ rest)
  RTN-ext-pm∷-C {M = return V} {L = W pmᵛ∷ L} rtn H (_ ~>⟨ () ⟩ rest)

  RTN-ext-pm∷-V : {X Y E : Ty} {V : Γ ⊢ᵛ A} {L : Γ ⊢ᵏ A ⇒ (X `× Y)} {N : (Γ ∙ X ∙ Y) ⊢ᶜ E} {K : Γ ⊢ᵏ E ⇒ C}
                → (∀ {V₁ V₂} → [ V ∥ L ] ↠ᵏ [ pair V₁ V₂ ∥ ε ] → Redᵛ X V₁ × Redᵛ Y V₂)
                → (∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → ∀ {W} → ⟨ sub-comp (sub-ex (sub-ex sub-id V₁) V₂) N ∥ K ⟩ ↠ᵏ ⟨ return W ∥ ε ⟩ → Redᵛ C W)
                → {W : _} → [ V ∥ graft L (N pm∷ K) ] ↠ᵏ ⟨ return W ∥ ε ⟩ → Redᵛ C W
  RTN-ext-pm∷-V {V = pm V W} rtn H (_ ~>⟨ pm-val-step ⟩ rest) =
    RTN-ext-pm∷-V (λ ch → rtn (_ ~>⟨ pm-val-step ⟩ ch)) H rest
  RTN-ext-pm∷-V {V = pair V W} {L = ε} rtn H (_ ~>⟨ pm-pair-step ⟩ rest) =
    H (proj₁ (rtn (_ ◼))) (proj₂ (rtn (_ ◼))) rest
  RTN-ext-pm∷-V {V = pair V W} {L = N pm∷ L} rtn H (_ ~>⟨ pm-pair-step ⟩ rest) =
    RTN-ext-pm∷-C (λ ch → rtn (_ ~>⟨ pm-pair-step ⟩ ch)) H rest
  RTN-ext-pm∷-V {V = pair V₁ V₂} {L = W pmᵛ∷ L} rtn H (_ ~>⟨ pmᵛ-pair-step ⟩ rest) =
    RTN-ext-pm∷-V (λ ch → rtn (_ ~>⟨ pmᵛ-pair-step ⟩ ch)) H rest

mutual
  SN-ext-pmᵛ∷-C : {X Y E : Ty} {M : Γ ⊢ᶜ A} {L : Γ ⊢ᵏ A ⇒ (X `× Y)} {W : (Γ ∙ X ∙ Y) ⊢ᵛ E} {K : Γ ⊢ᵏ E ⇒ C}
               → SN ⟨ M ∥ L ⟩
               → (∀ {V₁ V₂} → ⟨ M ∥ L ⟩ ↠ᵏ [ pair V₁ V₂ ∥ ε ] → Redᵛ X V₁ × Redᵛ Y V₂)
               → (∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → SN [ sub-val (sub-ex (sub-ex sub-id V₁) V₂) W ∥ K ])
               → SN ⟨ M ∥ graft L (W pmᵛ∷ K) ⟩
  SN-ext-pmᵛ∷-C {M = push M N} (sn f) rtn H =
    sn (λ { push-step → SN-ext-pmᵛ∷-C (f push-step) (λ ch → rtn (_ ~>⟨ push-step ⟩ ch)) H })
  SN-ext-pmᵛ∷-C {M = app (var i) V} (sn f) rtn H = sn (λ ())
  SN-ext-pmᵛ∷-C {M = app (lam N) V} (sn f) rtn H =
    sn (λ { app-lam-step → SN-ext-pmᵛ∷-C (f app-lam-step) (λ ch → rtn (_ ~>⟨ app-lam-step ⟩ ch)) H })
  SN-ext-pmᵛ∷-C {M = app (pm V₀ W) V} (sn f) rtn H =
    sn (λ { app-pm-step → SN-ext-pmᵛ∷-C (f app-pm-step) (λ ch → rtn (_ ~>⟨ app-pm-step ⟩ ch)) H })
  SN-ext-pmᵛ∷-C {M = pm V N} (sn f) rtn H =
    sn (λ { pm-step → SN-ext-pmᵛ∷-V (f pm-step) (λ ch → rtn (_ ~>⟨ pm-step ⟩ ch)) H })
  SN-ext-pmᵛ∷-C {M = return V} {L = ε} (sn f) rtn H = sn (λ ())
  SN-ext-pmᵛ∷-C {M = return V} {L = N ∷ L} (sn f) rtn H =
    sn (λ { return-step → SN-ext-pmᵛ∷-C (f return-step) (λ ch → rtn (_ ~>⟨ return-step ⟩ ch)) H })
  SN-ext-pmᵛ∷-C {M = return V} {L = N pm∷ L} (sn f) rtn H = sn (λ ())
  SN-ext-pmᵛ∷-C {M = return V} {L = W pmᵛ∷ L} (sn f) rtn H = sn (λ ())

  SN-ext-pmᵛ∷-V : {X Y E : Ty} {V : Γ ⊢ᵛ A} {L : Γ ⊢ᵏ A ⇒ (X `× Y)} {W : (Γ ∙ X ∙ Y) ⊢ᵛ E} {K : Γ ⊢ᵏ E ⇒ C}
               → SN [ V ∥ L ]
               → (∀ {V₁ V₂} → [ V ∥ L ] ↠ᵏ [ pair V₁ V₂ ∥ ε ] → Redᵛ X V₁ × Redᵛ Y V₂)
               → (∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → SN [ sub-val (sub-ex (sub-ex sub-id V₁) V₂) W ∥ K ])
               → SN [ V ∥ graft L (W pmᵛ∷ K) ]
  SN-ext-pmᵛ∷-V {V = var i} (sn f) rtn H = sn (λ ())
  SN-ext-pmᵛ∷-V {V = lam N} (sn f) rtn H = sn (λ ())
  SN-ext-pmᵛ∷-V {V = unit} (sn f) rtn H = sn (λ ())
  SN-ext-pmᵛ∷-V {V = pm V W} (sn f) rtn H =
    sn (λ { pm-val-step → SN-ext-pmᵛ∷-V (f pm-val-step) (λ ch → rtn (_ ~>⟨ pm-val-step ⟩ ch)) H })
  SN-ext-pmᵛ∷-V {V = pair V W} {L = ε} (sn f) rtn H =
    sn (λ { pmᵛ-pair-step → H (proj₁ (rtn (_ ◼))) (proj₂ (rtn (_ ◼))) })
  SN-ext-pmᵛ∷-V {V = pair V W} {L = N ∷ L} (sn f) rtn H = sn (λ ())
  SN-ext-pmᵛ∷-V {V = pair V W} {L = N pm∷ L} (sn f) rtn H =
    sn (λ { pm-pair-step → SN-ext-pmᵛ∷-C (f pm-pair-step) (λ ch → rtn (_ ~>⟨ pm-pair-step ⟩ ch)) H })
  SN-ext-pmᵛ∷-V {V = pair V₁ V₂} {L = W pmᵛ∷ L} (sn f) rtn H =
    sn (λ { pmᵛ-pair-step → SN-ext-pmᵛ∷-V (f pmᵛ-pair-step) (λ ch → rtn (_ ~>⟨ pmᵛ-pair-step ⟩ ch)) H })

mutual
  RTN-ext-pmᵛ∷ᴾ-C : {X Y E X' Y' : Ty} {M : Γ ⊢ᶜ A} {L : Γ ⊢ᵏ A ⇒ (X `× Y)} {W : (Γ ∙ X ∙ Y) ⊢ᵛ E} {K : Γ ⊢ᵏ E ⇒ (X' `× Y')}
                → (∀ {V₁ V₂} → ⟨ M ∥ L ⟩ ↠ᵏ [ pair V₁ V₂ ∥ ε ] → Redᵛ X V₁ × Redᵛ Y V₂)
                → (∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → ∀ {W₁ W₂} → [ sub-val (sub-ex (sub-ex sub-id V₁) V₂) W ∥ K ] ↠ᵏ [ pair W₁ W₂ ∥ ε ] → Redᵛ X' W₁ × Redᵛ Y' W₂)
                → {W₁ : Γ ⊢ᵛ X'} {W₂ : Γ ⊢ᵛ Y'} → ⟨ M ∥ graft L (W pmᵛ∷ K) ⟩ ↠ᵏ [ pair W₁ W₂ ∥ ε ] → Redᵛ X' W₁ × Redᵛ Y' W₂
  RTN-ext-pmᵛ∷ᴾ-C {M = push M N} rtn H (_ ~>⟨ push-step ⟩ rest) =
    RTN-ext-pmᵛ∷ᴾ-C (λ ch → rtn (_ ~>⟨ push-step ⟩ ch)) H rest
  RTN-ext-pmᵛ∷ᴾ-C {M = app (var i) V} rtn H (_ ~>⟨ () ⟩ rest)
  RTN-ext-pmᵛ∷ᴾ-C {M = app (lam N) V} rtn H (_ ~>⟨ app-lam-step ⟩ rest) =
    RTN-ext-pmᵛ∷ᴾ-C (λ ch → rtn (_ ~>⟨ app-lam-step ⟩ ch)) H rest
  RTN-ext-pmᵛ∷ᴾ-C {M = app (pm V₀ W) V} rtn H (_ ~>⟨ app-pm-step ⟩ rest) =
    RTN-ext-pmᵛ∷ᴾ-C (λ ch → rtn (_ ~>⟨ app-pm-step ⟩ ch)) H rest
  RTN-ext-pmᵛ∷ᴾ-C {M = pm V N} rtn H (_ ~>⟨ pm-step ⟩ rest) =
    RTN-ext-pmᵛ∷ᴾ-V (λ ch → rtn (_ ~>⟨ pm-step ⟩ ch)) H rest
  RTN-ext-pmᵛ∷ᴾ-C {M = return V} {L = ε} rtn H (_ ~>⟨ () ⟩ rest)
  RTN-ext-pmᵛ∷ᴾ-C {M = return V} {L = N ∷ L} rtn H (_ ~>⟨ return-step ⟩ rest) =
    RTN-ext-pmᵛ∷ᴾ-C (λ ch → rtn (_ ~>⟨ return-step ⟩ ch)) H rest
  RTN-ext-pmᵛ∷ᴾ-C {M = return V} {L = N pm∷ L} rtn H (_ ~>⟨ () ⟩ rest)
  RTN-ext-pmᵛ∷ᴾ-C {M = return V} {L = W pmᵛ∷ L} rtn H (_ ~>⟨ () ⟩ rest)

  RTN-ext-pmᵛ∷ᴾ-V : {X Y E X' Y' : Ty} {V : Γ ⊢ᵛ A} {L : Γ ⊢ᵏ A ⇒ (X `× Y)} {W : (Γ ∙ X ∙ Y) ⊢ᵛ E} {K : Γ ⊢ᵏ E ⇒ (X' `× Y')}
                → (∀ {V₁ V₂} → [ V ∥ L ] ↠ᵏ [ pair V₁ V₂ ∥ ε ] → Redᵛ X V₁ × Redᵛ Y V₂)
                → (∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → ∀ {W₁ W₂} → [ sub-val (sub-ex (sub-ex sub-id V₁) V₂) W ∥ K ] ↠ᵏ [ pair W₁ W₂ ∥ ε ] → Redᵛ X' W₁ × Redᵛ Y' W₂)
                → {W₁ : Γ ⊢ᵛ X'} {W₂ : Γ ⊢ᵛ Y'} → [ V ∥ graft L (W pmᵛ∷ K) ] ↠ᵏ [ pair W₁ W₂ ∥ ε ] → Redᵛ X' W₁ × Redᵛ Y' W₂
  RTN-ext-pmᵛ∷ᴾ-V {V = var i} rtn H (_ ~>⟨ () ⟩ rest)
  RTN-ext-pmᵛ∷ᴾ-V {V = lam N} rtn H (_ ~>⟨ () ⟩ rest)
  RTN-ext-pmᵛ∷ᴾ-V {V = unit} rtn H (_ ~>⟨ () ⟩ rest)
  RTN-ext-pmᵛ∷ᴾ-V {V = pm V W} rtn H (_ ~>⟨ pm-val-step ⟩ rest) =
    RTN-ext-pmᵛ∷ᴾ-V (λ ch → rtn (_ ~>⟨ pm-val-step ⟩ ch)) H rest
  RTN-ext-pmᵛ∷ᴾ-V {V = pair V W} {L = ε} rtn H (_ ~>⟨ pmᵛ-pair-step ⟩ rest) =
    H (proj₁ (rtn (_ ◼))) (proj₂ (rtn (_ ◼))) rest
  RTN-ext-pmᵛ∷ᴾ-V {V = pair V W} {L = N ∷ L} rtn H (_ ~>⟨ () ⟩ rest)
  RTN-ext-pmᵛ∷ᴾ-V {V = pair V W} {L = N pm∷ L} rtn H (_ ~>⟨ pm-pair-step ⟩ rest) =
    RTN-ext-pmᵛ∷ᴾ-C (λ ch → rtn (_ ~>⟨ pm-pair-step ⟩ ch)) H rest
  RTN-ext-pmᵛ∷ᴾ-V {V = pair V₁ V₂} {L = W pmᵛ∷ L} rtn H (_ ~>⟨ pmᵛ-pair-step ⟩ rest) =
    RTN-ext-pmᵛ∷ᴾ-V (λ ch → rtn (_ ~>⟨ pmᵛ-pair-step ⟩ ch)) H rest

exp-pm-comp : {V : Γ ⊢ᵛ X `× Y} {M : (Γ ∙ X ∙ Y) ⊢ᶜ C}
            → Redᵛ (X `× Y) V → (∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → Redᶜ C (sub-comp (sub-ex (sub-ex sub-id V₁) V₂) M))
            → Redᶜ C (pm V M)
exp-pm-comp {V = V} {M} redV H =
  sn (λ { pm-step → SN-ext-pm∷-V (Red→SNᵛ _ V redV) (proj₂ redV) (λ redV₁ redV₂ → Red→SNᶜ _ _ (H redV₁ redV₂)) }) ,
  λ { (_ ~>⟨ pm-step ⟩ rest) → RTN-ext-pm∷-V (proj₂ redV) (λ redV₁ redV₂ → Red→RTNᶜ _ _ (H redV₁ redV₂)) rest }

exp-app-lam : {N : (Γ ∙ A) ⊢ᶜ B} {V : Γ ⊢ᵛ A}
            → Redᶜ B (sub-comp (sub-ex sub-id V) N) → Redᶜ B (app (lam N) V)
exp-app-lam {N = N} {V} (snN , rtnN) =
  sn (λ { app-lam-step → snN }) ,
  λ { (_ ~>⟨ app-lam-step ⟩ rest) → rtnN rest }

exp-app-pm : {V : Γ ⊢ᵛ X `× Y} {W : (Γ ∙ X ∙ Y) ⊢ᵛ A `⇒ B} {W₁ : Γ ⊢ᵛ A}
           → Redᶜ B (pm V (app W (wk-val (wk-wk (wk-wk wk-id)) W₁))) → Redᶜ B (app (pm V W) W₁)
exp-app-pm {V = V} {W} {W₁} (snM , rtnM) =
  sn (λ { app-pm-step → snM }) ,
  λ { (_ ~>⟨ app-pm-step ⟩ rest) → rtnM rest }

Red-varᵛ : (A : Ty) (i : Γ ∋ A) → Redᵛ A (var i)
Red-varᵛ `Unit    i           = sn (λ ())
Red-varᵛ (A `× B) i           = sn (λ ()) , λ { (_ ~>⟨ () ⟩ _) }
Red-varᵛ (A `⇒ B) i           = sn (λ ()) , λ π {W} rw → sn (λ ()) , λ { (_ ~>⟨ () ⟩ _) }

--------------------------------------------------------------------------
-- weakening preserves reducibility

wk-reflect* : {Γ' : Ctx} (π : Γ' ⊇ Γ) {σ : Cfg Γ B} {σ₁ : Cfg Γ' B}
            → wk-cfg π σ ↠ᵏ σ₁ → Σ[ σ' ∈ Cfg Γ B ] (σ ↠ᵏ σ') × (σ₁ ≡ wk-cfg π σ')
wk-reflect* π (_ ◼) = _ , (_ ◼) , refl
wk-reflect* π (_ ~>⟨ step ⟩ rest) with wk-reflect π step
wk-reflect* π (_ ~>⟨ step ⟩ rest) | (σ , σ-step , refl) =
  let (σ' , σ₁-steps , eq₂) = wk-reflect* π rest
  in σ' , _ ~>⟨ σ-step ⟩ σ₁-steps , eq₂

pair-cfg-inv : {Γ' : Ctx} {A B : Ty} (π : Γ' ⊇ Γ) {σ' : Cfg Γ (A `× B)} {W₁ : Γ' ⊢ᵛ A} {W₂ : Γ' ⊢ᵛ B}
             → [ pair W₁ W₂ ∥ ε ] ≡ wk-cfg π σ'
             → Σ[ V₁ ∈ Γ ⊢ᵛ A ] Σ[ V₂ ∈ Γ ⊢ᵛ B ] (σ' ≡ [ pair V₁ V₂ ∥ ε ]) × (wk-val π V₁ ≡ W₁) × (wk-val π V₂ ≡ W₂)
pair-cfg-inv π {σ' = ⟨ M ∥ K ⟩}               ()
pair-cfg-inv π {σ' = [ var i ∥ K ]}           ()
pair-cfg-inv π {σ' = [ lam N ∥ K ]}           ()
pair-cfg-inv π {σ' = [ pair V W ∥ ε ]}        refl = V , W , refl , refl , refl
pair-cfg-inv π {σ' = [ pair V W ∥ N ∷ K ]}    ()
pair-cfg-inv π {σ' = [ pair V W ∥ N pm∷ K ]}  ()
pair-cfg-inv π {σ' = [ pair V₁ V₂ ∥ W pmᵛ∷ K ]} ()
pair-cfg-inv π {σ' = [ pm V W ∥ K ]}          ()
pair-cfg-inv π {σ' = [ unit ∥ K ]}            ()

Red-wk : (A : Ty) {Γ' : Ctx} (π : Γ' ⊇ Γ) {V : Γ ⊢ᵛ A} → Redᵛ A V → Redᵛ A (wk-val π V)
Red-wk `Unit    π r          = SN-wk π r
Red-wk (A `× B) π {V} (snV , f) = SN-wk π snV , g
  where
  g : ∀ {W₁ W₂} → [ wk-val π V ∥ ε ] ↠ᵏ [ pair W₁ W₂ ∥ ε ] → Redᵛ A W₁ × Redᵛ B W₂
  g p =
    let (σ' , σ-steps , eq)          = wk-reflect* π p
        (V₁ , V₂ , σ'-eq , eqV₁ , eqV₂) = pair-cfg-inv π eq
        (redV₁ , redV₂)                 = f (Eq.subst (λ x → [ V ∥ ε ] ↠ᵏ x) σ'-eq σ-steps)
    in Eq.subst (Redᵛ A) eqV₁ (Red-wk A π redV₁) , Eq.subst (Redᵛ B) eqV₂ (Red-wk B π redV₂)
Red-wk (A `⇒ B) π {V} (snV , f) = SN-wk π snV , harrow
  where
  harrow : ∀ {Γ''} (δ : Γ'' ⊇ _) {W : Γ'' ⊢ᵛ A} → Redᵛ A W → Redᶜ B (app (wk-val δ (wk-val π V)) W)
  harrow δ {W = W} redW =
    Eq.subst (Redᶜ B) (sym (cong (λ x → app x W) (wk-val-trans V δ π))) (f (wk-trans δ π) redW)

sub-val-ins2-cancel : (V₁ : Γ ⊢ᵛ X) (V₂ : Γ ⊢ᵛ Y) (W : Γ ⊢ᵛ A)
                     → sub-val (sub-ex (sub-ex sub-id V₁) V₂) (wk-val (wk-wk (wk-wk wk-id)) W) ≡ W
sub-val-ins2-cancel V₁ V₂ W = begin
  sub-val (sub-ex (sub-ex sub-id V₁) V₂) (wk-val (wk-wk (wk-wk wk-id)) W)  ≡⟨ sub-val-wk-pre (sub-ex (sub-ex sub-id V₁) V₂) (wk-wk (wk-wk wk-id)) W ⟩
  sub-val (sub-pre sub-id wk-id) W                                      ≡⟨ cong (λ θ → sub-val θ W) (sub-pre-wk-id sub-id) ⟩
  sub-val sub-id W                                                      ≡⟨ sub-val-id W ⟩
  W ∎

exp-pm-val : (C : Ty) {V : Γ ⊢ᵛ X `× Y} {W : (Γ ∙ X ∙ Y) ⊢ᵛ C}
           → Redᵛ (X `× Y) V
           → (∀ {Γ'} (π : Γ' ⊇ Γ) {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → Redᵛ C (sub-val (sub-ex (sub-ex sub-id V₁) V₂) (wk-val (wk-cong (wk-cong π)) W)))
           → Redᵛ C (pm V W)
exp-pm-val {Γ} {X} {Y} `Unit {V} {W} redV H =
  sn (λ { pm-val-step →
    SN-ext-pmᵛ∷-V (Red→SNᵛ _ V redV) (proj₂ redV)
      (λ redV₁ redV₂ → Red→SNᵛ `Unit _ (H₀ redV₁ redV₂)) })
  where
  H₀ : ∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → Redᵛ `Unit (sub-val (sub-ex (sub-ex sub-id V₁) V₂) W)
  H₀ {V₁} {V₂} redV₁ redV₂ = Eq.subst (Redᵛ `Unit) (cong (sub-val (sub-ex (sub-ex sub-id V₁) V₂)) (wk-val-id W)) (H wk-id redV₁ redV₂)
exp-pm-val {Γ} {X} {Y} (C₁ `× C₂) {V} {W} redV H =
  sn (λ { pm-val-step →
    SN-ext-pmᵛ∷-V (Red→SNᵛ _ V redV) (proj₂ redV)
      (λ redV₁ redV₂ → Red→SNᵛ (C₁ `× C₂) _ (H₀ redV₁ redV₂)) }) ,
  λ { (_ ~>⟨ pm-val-step ⟩ rest) → RTN-ext-pmᵛ∷ᴾ-V (proj₂ redV) (λ redV₁ redV₂ → proj₂ (H₀ redV₁ redV₂)) rest }
  where
  H₀ : ∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → Redᵛ (C₁ `× C₂) (sub-val (sub-ex (sub-ex sub-id V₁) V₂) W)
  H₀ {V₁} {V₂} redV₁ redV₂ = Eq.subst (Redᵛ (C₁ `× C₂)) (cong (sub-val (sub-ex (sub-ex sub-id V₁) V₂)) (wk-val-id W)) (H wk-id redV₁ redV₂)
exp-pm-val {Γ} {X} {Y} (C₁ `⇒ C₂) {V} {W} redV H =
  sn (λ { pm-val-step →
    SN-ext-pmᵛ∷-V (Red→SNᵛ _ V redV) (proj₂ redV)
      (λ redV₁ redV₂ → Red→SNᵛ (C₁ `⇒ C₂) _ (H₀ redV₁ redV₂)) }) ,
  harrow
  where
  H₀ : ∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → Redᵛ (C₁ `⇒ C₂) (sub-val (sub-ex (sub-ex sub-id V₁) V₂) W)
  H₀ {V₁} {V₂} redV₁ redV₂ = Eq.subst (Redᵛ (C₁ `⇒ C₂)) (cong (sub-val (sub-ex (sub-ex sub-id V₁) V₂)) (wk-val-id W)) (H wk-id redV₁ redV₂)

  harrow : ∀ {Γ''} (ρ : Γ'' ⊇ Γ) {W₁ : Γ'' ⊢ᵛ C₁} → Redᵛ C₁ W₁ → Redᶜ C₂ (app (wk-val ρ (pm V W)) W₁)
  harrow ρ {W₁} redW₁ =
    exp-app-pm
      (exp-pm-comp (Red-wk (X `× Y) ρ redV)
        (λ {V₁} {V₂} redV₁ redV₂ →
          let redW = H ρ redV₁ redV₂
              redW₁-wk = Eq.subst (Redᵛ C₁) (sym (sub-val-ins2-cancel V₁ V₂ W₁)) redW₁
          in Eq.subst (Redᶜ C₂)
                      (cong (λ w → app w (sub-val (sub-ex (sub-ex sub-id V₁) V₂) (wk-val (wk-wk (wk-wk wk-id)) W₁)))
                            (wk-val-id (sub-val (sub-ex (sub-ex sub-id V₁) V₂) (wk-val (wk-cong (wk-cong ρ)) W))))
                      (proj₂ redW wk-id redW₁-wk)))

record RedSub (θ : Γ ⊢ Δ) : Set where
  field red : (i : Δ ∋ A) → Redᵛ A (sub-mem θ i)
open RedSub

RedSub-wk : {Γ' : Ctx} (ρ : Γ' ⊇ Γ) {θ : Γ ⊢ Δ} → RedSub θ → RedSub (sub-wk ρ θ)
RedSub-wk ρ {θ} rθ = record
  { red = λ i → Eq.subst (Redᵛ _) (sym (sub-mem-wk ρ θ i)) (Red-wk _ ρ (rθ .red i)) }

RedSub-ext : {θ : Γ ⊢ Δ} {V : Γ ⊢ᵛ A} → RedSub θ → Redᵛ A V → RedSub (sub-ex θ V)
RedSub-ext rθ rv = record { red = λ { here → rv ; (there i) → rθ .red i } }

RedSub-id : RedSub (sub-id {Γ})
RedSub-id {Γ} = record { red = λ i → Eq.subst (Redᵛ _) (sym (sub-mem-id i)) (Red-varᵛ _ i) }

--------------------------------------------------------------------------
-- Fundamental Lemma

Fundamental-val : (θ : Γ ⊢ Δ) → RedSub θ → (V : Δ ⊢ᵛ A) → Redᵛ A (sub-val θ V)
Fundamental-comp : (θ : Γ ⊢ Δ) → RedSub θ → (M : Δ ⊢ᶜ A) → Redᶜ A (sub-comp θ M)

Fundamental-val θ rθ (var i) = rθ .red i
Fundamental-val θ rθ unit    = sn (λ ())
Fundamental-val θ rθ (lam M) =
  sn (λ ()) ,
  λ π {W} rw →
    exp-app-lam (Eq.subst (Redᶜ _) (sym (fund-lam-eq θ π W M))
                          (Fundamental-comp (sub-ex (sub-wk π θ) W) (RedSub-ext (RedSub-wk π rθ) rw) M))
Fundamental-val θ rθ (pair V W) =
  sn (λ ()) , λ { (_ ◼) → Fundamental-val θ rθ V , Fundamental-val θ rθ W ; (_ ~>⟨ () ⟩ _) }
Fundamental-val θ rθ (pm {A = X} {B = Y} V W) =
  exp-pm-val _ (Fundamental-val θ rθ V)
    (λ π {V₁} {V₂} redV₁ redV₂ →
      Eq.subst (Redᵛ _)
        (begin
           sub-val (sub-ex (sub-ex (sub-wk π θ) V₁) V₂) W
         ≡˘⟨ fund-pm-eqᵛ (sub-wk π θ) V₁ V₂ W ⟩
           sub-val (sub-ex (sub-ex sub-id V₁) V₂)
                   (sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-wk π θ)) (var (there here))) (var here)) W)
         ≡˘⟨ cong (sub-val (sub-ex (sub-ex sub-id V₁) V₂))
                  (begin
                     wk-val (wk-cong (wk-cong π))
                            (sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) W)
                   ≡⟨ wk-sub-val (wk-cong (wk-cong π)) (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) W ⟩
                     sub-val (sub-wk (wk-cong (wk-cong π)) (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here))) W
                   ≡⟨ cong (λ w → sub-val w W)
                           (cong (λ w → sub-ex w (var here))
                                 (cong (λ w → sub-ex w (var (there here))) (wk-cong2-sub-wk-lemma π θ))) ⟩
                     sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-wk π θ)) (var (there here))) (var here)) W ∎) ⟩
           sub-val (sub-ex (sub-ex sub-id V₁) V₂)
                   (wk-val (wk-cong (wk-cong π))
                           (sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) W)) ∎)
        (Fundamental-val (sub-ex (sub-ex (sub-wk π θ) V₁) V₂) (RedSub-ext (RedSub-ext (RedSub-wk π rθ) redV₁) redV₂) W))

Fundamental-comp θ rθ (return V) =
  sn (λ ()) , λ { (_ ◼) → Fundamental-val θ rθ V ; (_ ~>⟨ () ⟩ _) }
Fundamental-comp θ rθ (app V W) =
  Eq.subst (λ x → Redᶜ _ (app x (sub-val θ W))) (wk-val-id (sub-val θ V))
           (proj₂ (Fundamental-val θ rθ V) wk-id (Fundamental-val θ rθ W))
Fundamental-comp θ rθ (push M N) =
  exp-push (Fundamental-comp θ rθ M)
           (λ {V} rv → Eq.subst (Redᶜ _) (sym (fund-push-eq θ V N))
                          (Fundamental-comp (sub-ex θ V) (RedSub-ext rθ rv) N))
Fundamental-comp θ rθ (pm {A = X} {B = Y} V M) =
  exp-pm-comp (Fundamental-val θ rθ V)
              (λ {V₁} {V₂} redV₁ redV₂ →
                Eq.subst (Redᶜ _) (sym (fund-pm-eqᶜ θ V₁ V₂ M))
                         (Fundamental-comp (sub-ex (sub-ex θ V₁) V₂) (RedSub-ext (RedSub-ext rθ redV₁) redV₂) M))

SN-theorem : (M : Γ ⊢ᶜ A) → SN ⟨ M ∥ ε ⟩
SN-theorem {Γ} {A} M =
  Eq.subst (λ x → SN ⟨ x ∥ ε ⟩) (sub-comp-id M)
           (Red→SNᶜ A (sub-comp sub-id M) (Fundamental-comp sub-id RedSub-id M))

--------------------------------------------------------------------------
-- eval

Normal : Cfg Γ B → Set
Normal σ = ∀ {σ'} → σ →ᵏ σ' → ⊥

data Step? (σ : Cfg Γ B) : Set where
  done : Normal σ → Step? σ
  next : {σ' : Cfg Γ B} → σ →ᵏ σ' → Step? σ

step? : (σ : Cfg Γ B) → Step? σ
step? ⟨ push M N ∥ K ⟩          = next push-step
step? ⟨ return V ∥ ε ⟩          = done (λ ())
step? ⟨ return V ∥ N ∷ K ⟩      = next return-step
step? ⟨ return V ∥ N pm∷ K ⟩    = done (λ ())
step? ⟨ return V ∥ W pmᵛ∷ K ⟩   = done (λ ())
step? ⟨ app (var i) V ∥ K ⟩     = done (λ ())
step? ⟨ app (lam N) V ∥ K ⟩     = next app-lam-step
step? ⟨ app (pm V W) N ∥ K ⟩    = next app-pm-step
step? ⟨ pm V N ∥ K ⟩            = next pm-step
step? [ var i ∥ K ]             = done (λ ())
step? [ lam N ∥ K ]             = done (λ ())
step? [ unit ∥ K ]              = done (λ ())
step? [ pm V W ∥ K ]            = next pm-val-step
step? [ pair V W ∥ ε ]          = done (λ ())
step? [ pair V W ∥ N ∷ K ]      = done (λ ())
step? [ pair V W ∥ N pm∷ K ]    = next pm-pair-step
step? [ pair V₁ V₂ ∥ W pmᵛ∷ K ] = next pmᵛ-pair-step

eval-acc : {σ : Cfg Γ B} → SN σ → Σ[ σ' ∈ Cfg Γ B ] (σ ↠ᵏ σ') × Normal σ'
eval-acc {σ = σ} (sn f) with step? σ
... | done normal    = σ , σ ◼ , normal
... | next {σ'} step with eval-acc (f step)
...   | (σ'' , chain , normal) = σ'' , σ ~>⟨ step ⟩ chain , normal

eval : (M : Γ ⊢ᶜ A) → Σ[ σ' ∈ Cfg Γ A ] (⟨ M ∥ ε ⟩ ↠ᵏ σ') × Normal σ'
eval M = eval-acc (SN-theorem M)
