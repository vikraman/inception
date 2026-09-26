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

syntax Stk Γ X Y = Γ ⊢ᵏ X ⇒ Y

data Stk (Γ : Ctx) : Ty → Ty → Set where

  ε      : Γ ⊢ᵏ X ⇒ X

  _∷_    : (N : (Γ ∙ X) ⊢ᶜ Y) → (K : Γ ⊢ᵏ Y ⇒ Z)
         → Γ ⊢ᵏ X ⇒ Z

  _pm∷_  : (N : (Γ ∙ X ∙ Y) ⊢ᶜ Z) → (K : Γ ⊢ᵏ Z ⇒ X₁)
         → Γ ⊢ᵏ (X `× Y) ⇒ X₁

  _pmᵛ∷_ : (W : (Γ ∙ X ∙ Y) ⊢ᵛ Z) → (K : Γ ⊢ᵏ Z ⇒ X₁)
         → Γ ⊢ᵏ (X `× Y) ⇒ X₁

infix 5 ⟨_∥_⟩
infix 5 [_∥_]

data Cfg (Γ : Ctx) (X : Ty) : Set where

  ⟨_∥_⟩ : (M : Γ ⊢ᶜ Y) → (K : Γ ⊢ᵏ Y ⇒ X)
        → Cfg Γ X

  [_∥_] : (V : Γ ⊢ᵛ Y) → (K : Γ ⊢ᵏ Y ⇒ X)
        → Cfg Γ X

infix 5 _→ᵏ_

data _→ᵏ_ : Cfg Γ X → Cfg Γ X → Set where

  push-step      : {M : Γ ⊢ᶜ X} {N : (Γ ∙ X) ⊢ᶜ Y} {K : Γ ⊢ᵏ Y ⇒ Z}
                 → ⟨ push M N ∥ K ⟩ →ᵏ ⟨ M ∥ N ∷ K ⟩

  return-step    : {V : Γ ⊢ᵛ X} {N : (Γ ∙ X) ⊢ᶜ Y} {K : Γ ⊢ᵏ Y ⇒ Z}
                 → ⟨ return V ∥ N ∷ K ⟩ →ᵏ ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩

  pm-step        : {V : Γ ⊢ᵛ X `× Y} {N : (Γ ∙ X ∙ Y) ⊢ᶜ Z} {K : Γ ⊢ᵏ Z ⇒ X₁}
                 → ⟨ pm V N ∥ K ⟩ →ᵏ [ V ∥ N pm∷ K ]

  pm-pair-step   : {V : Γ ⊢ᵛ X} {W : Γ ⊢ᵛ Y} {N : (Γ ∙ X ∙ Y) ⊢ᶜ Z} {K : Γ ⊢ᵏ Z ⇒ X₁}
                 → [ pair V W ∥ N pm∷ K ] →ᵏ ⟨ sub-comp (sub-ex (sub-ex sub-id V) W) N ∥ K ⟩

  pm-val-step    : {V : Γ ⊢ᵛ X `× Y} {W : (Γ ∙ X ∙ Y) ⊢ᵛ Z} {K : Γ ⊢ᵏ Z ⇒ X₁}
                 → [ pm V W ∥ K ] →ᵏ [ V ∥ W pmᵛ∷ K ]

  pmᵛ-pair-step  : {V₁ : Γ ⊢ᵛ X} {V₂ : Γ ⊢ᵛ Y} {W : (Γ ∙ X ∙ Y) ⊢ᵛ Z} {K : Γ ⊢ᵏ Z ⇒ X₁}
                 → [ pair V₁ V₂ ∥ W pmᵛ∷ K ] →ᵏ [ sub-val (sub-ex (sub-ex sub-id V₁) V₂) W ∥ K ]

  app-lam-step   : {N : (Γ ∙ X) ⊢ᶜ Y} {V : Γ ⊢ᵛ X} {K : Γ ⊢ᵏ Y ⇒ Z}
                 → ⟨ app (lam N) V ∥ K ⟩ →ᵏ ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩

  app-pm-step    : {V : Γ ⊢ᵛ X `× Y} {W : (Γ ∙ X ∙ Y) ⊢ᵛ Z `⇒ X₁} {W₁ : Γ ⊢ᵛ Z} {K : Γ ⊢ᵏ X₁ ⇒ Y₁}
                 → ⟨ app (pm V W) W₁ ∥ K ⟩ →ᵏ ⟨ pm V (app W (wk-val (wk-wk (wk-wk wk-id)) W₁)) ∥ K ⟩

--------------------------------------------------------------------------
-- accessibility

data SN {Γ X} (σ : Cfg Γ X) : Set where
  sn : (∀ {σ₁} → σ →ᵏ σ₁ → SN σ₁) → SN σ

infix 5 _↠ᵏ_

_↠ᵏ_ : {Γ : Ctx} {X : Ty} → Cfg Γ X → Cfg Γ X → Set
_↠ᵏ_ {Γ} {X} = _~>*_ (_→ᵏ_ {Γ = Γ} {X = X})

--------------------------------------------------------------------------
-- weakening a configuration

wk-stk : {Δ : Ctx} → Δ ⊇ Γ → Γ ⊢ᵏ X ⇒ Y → Δ ⊢ᵏ X ⇒ Y
wk-stk π ε          = ε
wk-stk π (N ∷ K)    = wk-comp (wk-cong π) N ∷ wk-stk π K
wk-stk π (N pm∷ K)  = wk-comp (wk-cong (wk-cong π)) N pm∷ wk-stk π K
wk-stk π (W pmᵛ∷ K) = wk-val (wk-cong (wk-cong π)) W pmᵛ∷ wk-stk π K

wk-cfg : {Δ : Ctx} → Δ ⊇ Γ → Cfg Γ X → Cfg Δ X
wk-cfg π ⟨ M ∥ K ⟩ = ⟨ wk-comp π M ∥ wk-stk π K ⟩
wk-cfg π [ V ∥ K ] = [ wk-val π V ∥ wk-stk π K ]

wk-ins2 : {Γ Δ : Ctx} {X Y Z : Ty} (π : Δ ⊇ Γ) (V : Γ ⊢ᵛ Z) →
        wk-val (wk-wk {X = Y} (wk-wk {X = X} wk-id)) (wk-val π V) ≡ wk-val (wk-cong {X = Y} (wk-cong {X = X} π)) (wk-val (wk-wk {X = Y} (wk-wk {X = X} wk-id)) V)
wk-ins2 {X = X} {Y = Y} π V = begin
    wk-val (wk-wk {X = Y} (wk-wk {X = X} wk-id)) (wk-val π V)
  ≡⟨ wk-val-trans V (wk-wk {X = Y} (wk-wk {X = X} wk-id)) π ⟩
    wk-val (wk-wk {X = Y} (wk-wk {X = X} (wk-trans wk-id π))) V
  ≡⟨ cong (λ x → wk-val (wk-wk {X = Y} (wk-wk {X = X} x)) V) (wk-trans-idl π) ⟩
    wk-val (wk-wk {X = Y} (wk-wk {X = X} π)) V
  ≡˘⟨ cong (λ x → wk-val (wk-wk {X = Y} (wk-wk {X = X} x)) V) (wk-trans-idr π) ⟩
    wk-val (wk-wk {X = Y} (wk-wk {X = X} (wk-trans π wk-id))) V
  ≡˘⟨ wk-val-trans V (wk-cong {X = Y} (wk-cong {X = X} π)) (wk-wk {X = Y} (wk-wk {X = X} wk-id)) ⟩
    wk-val (wk-cong {X = Y} (wk-cong {X = X} π)) (wk-val (wk-wk {X = Y} (wk-wk {X = X} wk-id)) V) ∎

wk-step : {Δ : Ctx} (π : Δ ⊇ Γ) {σ σ₁ : Cfg Γ X} → σ →ᵏ σ₁ → wk-cfg π σ →ᵏ wk-cfg π σ₁
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

wk-reflect : {Δ : Ctx} (π : Δ ⊇ Γ) {σ : Cfg Γ X} {σ₁ : Cfg Δ X}
           → wk-cfg π σ →ᵏ σ₁ → Σ[ σ₂ ∈ Cfg Γ X ] (σ →ᵏ σ₂) × (σ₁ ≡ wk-cfg π σ₂)
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

SN-wk : {Δ : Ctx} (π : Δ ⊇ Γ) {σ : Cfg Γ X} → SN σ → SN (wk-cfg π σ)
SN-wk π {σ} (sn f) = sn step
  where
  step : ∀ {σ₁} → wk-cfg π σ →ᵏ σ₁ → SN σ₁
  step s with wk-reflect π s
  ... | (σ₂ , σ-step , eq) = Eq.subst SN (sym eq) (SN-wk π (f σ-step))

--------------------------------------------------------------------------
-- reducibility candidates

graft : Γ ⊢ᵏ X ⇒ Y → Γ ⊢ᵏ Y ⇒ Z → Γ ⊢ᵏ X ⇒ Z
graft ε          K = K
graft (N ∷ L)   K  = N ∷ graft L K
graft (N pm∷ L)  K = N pm∷ graft L K
graft (W pmᵛ∷ L) K = W pmᵛ∷ graft L K

Redᵛ : (X : Ty) → Γ ⊢ᵛ X → Set
Redᶜ : (X : Ty) → Γ ⊢ᶜ X → Set

Redᵛ `𝟙       V    = SN [ V ∥ ε ]
Redᵛ (X `× Y)    V = SN [ V ∥ ε ] × (∀ {V₁ V₂} → [ V ∥ ε ] ↠ᵏ [ pair V₁ V₂ ∥ ε ] → Redᵛ X V₁ × Redᵛ Y V₂)
Redᵛ {Γ} (X `⇒ Y) V = SN [ V ∥ ε ] × (∀ {Δ} (π : Δ ⊇ Γ) {W : Δ ⊢ᵛ X} → Redᵛ X W → Redᶜ Y (app (wk-val π V) W))

Redᶜ X M = SN ⟨ M ∥ ε ⟩ × (∀ {V} → ⟨ M ∥ ε ⟩ ↠ᵏ ⟨ return V ∥ ε ⟩ → Redᵛ X V)

Red→SNᵛ : (X : Ty) (V : Γ ⊢ᵛ X) → Redᵛ X V → SN [ V ∥ ε ]
Red→SNᵛ `𝟙    V r    = r
Red→SNᵛ (X `× Y) V r = proj₁ r
Red→SNᵛ (X `⇒ Y) V r = proj₁ r

Red→SNᶜ : (X : Ty) (M : Γ ⊢ᶜ X) → Redᶜ X M → SN ⟨ M ∥ ε ⟩
Red→SNᶜ X M (snM , ret) = snM

Red→RTNᶜ : (X : Ty) (M : Γ ⊢ᶜ X) → Redᶜ X M → (∀ {V} → ⟨ M ∥ ε ⟩ ↠ᵏ ⟨ return V ∥ ε ⟩ → Redᵛ X V)
Red→RTNᶜ X M (snM , ret) = ret

mutual
  SN-ext∷-C : {X : Ty} {M : Γ ⊢ᶜ Y} {L : Γ ⊢ᵏ Y ⇒ Z} {N : (Γ ∙ Z) ⊢ᶜ X} {K : Γ ⊢ᵏ X ⇒ X₁}
            → SN ⟨ M ∥ L ⟩
            → (∀ {V} → ⟨ M ∥ L ⟩ ↠ᵏ ⟨ return V ∥ ε ⟩ → Redᵛ Z V)
            → (∀ {V} → Redᵛ Z V → SN ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩)
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

  SN-ext∷-V : {X : Ty} {V : Γ ⊢ᵛ Y} {L : Γ ⊢ᵏ Y ⇒ Z} {N : (Γ ∙ Z) ⊢ᶜ X} {K : Γ ⊢ᵏ X ⇒ X₁}
            → SN [ V ∥ L ]
            → (∀ {W} → [ V ∥ L ] ↠ᵏ ⟨ return W ∥ ε ⟩ → Redᵛ Z W)
            → (∀ {W} → Redᵛ Z W → SN ⟨ sub-comp (sub-ex sub-id W) N ∥ K ⟩)
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
  RTN-ext∷-C : {X : Ty} {M : Γ ⊢ᶜ Y} {L : Γ ⊢ᵏ Y ⇒ Z} {N : (Γ ∙ Z) ⊢ᶜ X} {K : Γ ⊢ᵏ X ⇒ X₁}
             → (∀ {V} → ⟨ M ∥ L ⟩ ↠ᵏ ⟨ return V ∥ ε ⟩ → Redᵛ Z V)
             → (∀ {V} → Redᵛ Z V → ∀ {W} → ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩ ↠ᵏ ⟨ return W ∥ ε ⟩ → Redᵛ X₁ W)
             → {W : _} → ⟨ M ∥ graft L (N ∷ K) ⟩ ↠ᵏ ⟨ return W ∥ ε ⟩ → Redᵛ X₁ W
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

  RTN-ext∷-V : {X : Ty} {V : Γ ⊢ᵛ Y} {L : Γ ⊢ᵏ Y ⇒ Z} {N : (Γ ∙ Z) ⊢ᶜ X} {K : Γ ⊢ᵏ X ⇒ X₁}
             → (∀ {V₁} → [ V ∥ L ] ↠ᵏ ⟨ return V₁ ∥ ε ⟩ → Redᵛ Z V₁)
             → (∀ {V₁} → Redᵛ Z V₁ → ∀ {V₂} → ⟨ sub-comp (sub-ex sub-id V₁) N ∥ K ⟩ ↠ᵏ ⟨ return V₂ ∥ ε ⟩ → Redᵛ X₁ V₂)
             → {V₂ : _} → [ V ∥ graft L (N ∷ K) ] ↠ᵏ ⟨ return V₂ ∥ ε ⟩ → Redᵛ X₁ V₂
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

exp-push : {M : Γ ⊢ᶜ X} {N : (Γ ∙ X) ⊢ᶜ Y}
         → Redᶜ X M → (∀ {V} → Redᵛ X V → Redᶜ Y (sub-comp (sub-ex sub-id V) N))
         → Redᶜ Y (push M N)
exp-push {M = M} {N} rM H =
  sn (λ { push-step → SN-ext∷-C (Red→SNᶜ _ _ rM) (Red→RTNᶜ _ _ rM) (λ {V} rv → Red→SNᶜ _ _ (H rv)) }) ,
  λ { (_ ~>⟨ push-step ⟩ rest) → RTN-ext∷-C (Red→RTNᶜ _ _ rM) (λ {V} rv → Red→RTNᶜ _ _ (H rv)) rest }

mutual
  SN-ext-pm∷-C : {X Y Z : Ty} {M : Γ ⊢ᶜ X₁} {L : Γ ⊢ᵏ X₁ ⇒ (X `× Y)} {N : (Γ ∙ X ∙ Y) ⊢ᶜ Z} {K : Γ ⊢ᵏ Z ⇒ Y₁}
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

  SN-ext-pm∷-V : {X Y Z : Ty} {V : Γ ⊢ᵛ X₁} {L : Γ ⊢ᵏ X₁ ⇒ (X `× Y)} {N : (Γ ∙ X ∙ Y) ⊢ᶜ Z} {K : Γ ⊢ᵏ Z ⇒ Y₁}
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
  RTN-ext-pm∷-C : {X Y Z : Ty} {M : Γ ⊢ᶜ X₁} {L : Γ ⊢ᵏ X₁ ⇒ (X `× Y)} {N : (Γ ∙ X ∙ Y) ⊢ᶜ Z} {K : Γ ⊢ᵏ Z ⇒ Y₁}
                → (∀ {V₁ V₂} → ⟨ M ∥ L ⟩ ↠ᵏ [ pair V₁ V₂ ∥ ε ] → Redᵛ X V₁ × Redᵛ Y V₂)
                → (∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → ∀ {W} → ⟨ sub-comp (sub-ex (sub-ex sub-id V₁) V₂) N ∥ K ⟩ ↠ᵏ ⟨ return W ∥ ε ⟩ → Redᵛ Y₁ W)
                → {W : _} → ⟨ M ∥ graft L (N pm∷ K) ⟩ ↠ᵏ ⟨ return W ∥ ε ⟩ → Redᵛ Y₁ W
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

  RTN-ext-pm∷-V : {X Y Z : Ty} {V : Γ ⊢ᵛ X₁} {L : Γ ⊢ᵏ X₁ ⇒ (X `× Y)} {N : (Γ ∙ X ∙ Y) ⊢ᶜ Z} {K : Γ ⊢ᵏ Z ⇒ Y₁}
                → (∀ {V₁ V₂} → [ V ∥ L ] ↠ᵏ [ pair V₁ V₂ ∥ ε ] → Redᵛ X V₁ × Redᵛ Y V₂)
                → (∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → ∀ {W} → ⟨ sub-comp (sub-ex (sub-ex sub-id V₁) V₂) N ∥ K ⟩ ↠ᵏ ⟨ return W ∥ ε ⟩ → Redᵛ Y₁ W)
                → {W : _} → [ V ∥ graft L (N pm∷ K) ] ↠ᵏ ⟨ return W ∥ ε ⟩ → Redᵛ Y₁ W
  RTN-ext-pm∷-V {V = pm V W} rtn H (_ ~>⟨ pm-val-step ⟩ rest) =
    RTN-ext-pm∷-V (λ ch → rtn (_ ~>⟨ pm-val-step ⟩ ch)) H rest
  RTN-ext-pm∷-V {V = pair V W} {L = ε} rtn H (_ ~>⟨ pm-pair-step ⟩ rest) =
    H (proj₁ (rtn (_ ◼))) (proj₂ (rtn (_ ◼))) rest
  RTN-ext-pm∷-V {V = pair V W} {L = N pm∷ L} rtn H (_ ~>⟨ pm-pair-step ⟩ rest) =
    RTN-ext-pm∷-C (λ ch → rtn (_ ~>⟨ pm-pair-step ⟩ ch)) H rest
  RTN-ext-pm∷-V {V = pair V₁ V₂} {L = W pmᵛ∷ L} rtn H (_ ~>⟨ pmᵛ-pair-step ⟩ rest) =
    RTN-ext-pm∷-V (λ ch → rtn (_ ~>⟨ pmᵛ-pair-step ⟩ ch)) H rest

mutual
  SN-ext-pmᵛ∷-C : {X Y Z : Ty} {M : Γ ⊢ᶜ X₁} {L : Γ ⊢ᵏ X₁ ⇒ (X `× Y)} {W : (Γ ∙ X ∙ Y) ⊢ᵛ Z} {K : Γ ⊢ᵏ Z ⇒ Y₁}
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

  SN-ext-pmᵛ∷-V : {X Y Z : Ty} {V : Γ ⊢ᵛ X₁} {L : Γ ⊢ᵏ X₁ ⇒ (X `× Y)} {W : (Γ ∙ X ∙ Y) ⊢ᵛ Z} {K : Γ ⊢ᵏ Z ⇒ Y₁}
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
  RTN-ext-pmᵛ∷ᴾ-C : {X Y Z X₁ Y₁ : Ty} {M : Γ ⊢ᶜ Z₁} {L : Γ ⊢ᵏ Z₁ ⇒ (X `× Y)} {W : (Γ ∙ X ∙ Y) ⊢ᵛ Z} {K : Γ ⊢ᵏ Z ⇒ (X₁ `× Y₁)}
                → (∀ {V₁ V₂} → ⟨ M ∥ L ⟩ ↠ᵏ [ pair V₁ V₂ ∥ ε ] → Redᵛ X V₁ × Redᵛ Y V₂)
                → (∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → ∀ {W₁ W₂} → [ sub-val (sub-ex (sub-ex sub-id V₁) V₂) W ∥ K ] ↠ᵏ [ pair W₁ W₂ ∥ ε ] → Redᵛ X₁ W₁ × Redᵛ Y₁ W₂)
                → {W₁ : Γ ⊢ᵛ X₁} {W₂ : Γ ⊢ᵛ Y₁} → ⟨ M ∥ graft L (W pmᵛ∷ K) ⟩ ↠ᵏ [ pair W₁ W₂ ∥ ε ] → Redᵛ X₁ W₁ × Redᵛ Y₁ W₂
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

  RTN-ext-pmᵛ∷ᴾ-V : {X Y Z X₁ Y₁ : Ty} {V : Γ ⊢ᵛ Z₁} {L : Γ ⊢ᵏ Z₁ ⇒ (X `× Y)} {W : (Γ ∙ X ∙ Y) ⊢ᵛ Z} {K : Γ ⊢ᵏ Z ⇒ (X₁ `× Y₁)}
                → (∀ {V₁ V₂} → [ V ∥ L ] ↠ᵏ [ pair V₁ V₂ ∥ ε ] → Redᵛ X V₁ × Redᵛ Y V₂)
                → (∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → ∀ {W₁ W₂} → [ sub-val (sub-ex (sub-ex sub-id V₁) V₂) W ∥ K ] ↠ᵏ [ pair W₁ W₂ ∥ ε ] → Redᵛ X₁ W₁ × Redᵛ Y₁ W₂)
                → {W₁ : Γ ⊢ᵛ X₁} {W₂ : Γ ⊢ᵛ Y₁} → [ V ∥ graft L (W pmᵛ∷ K) ] ↠ᵏ [ pair W₁ W₂ ∥ ε ] → Redᵛ X₁ W₁ × Redᵛ Y₁ W₂
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

exp-pm-comp : {V : Γ ⊢ᵛ X `× Y} {M : (Γ ∙ X ∙ Y) ⊢ᶜ Z}
            → Redᵛ (X `× Y) V → (∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → Redᶜ Z (sub-comp (sub-ex (sub-ex sub-id V₁) V₂) M))
            → Redᶜ Z (pm V M)
exp-pm-comp {V = V} {M} redV H =
  sn (λ { pm-step → SN-ext-pm∷-V (Red→SNᵛ _ V redV) (proj₂ redV) (λ redV₁ redV₂ → Red→SNᶜ _ _ (H redV₁ redV₂)) }) ,
  λ { (_ ~>⟨ pm-step ⟩ rest) → RTN-ext-pm∷-V (proj₂ redV) (λ redV₁ redV₂ → Red→RTNᶜ _ _ (H redV₁ redV₂)) rest }

exp-app-lam : {N : (Γ ∙ X) ⊢ᶜ Y} {V : Γ ⊢ᵛ X}
            → Redᶜ Y (sub-comp (sub-ex sub-id V) N) → Redᶜ Y (app (lam N) V)
exp-app-lam {N = N} {V} (snN , rtnN) =
  sn (λ { app-lam-step → snN }) ,
  λ { (_ ~>⟨ app-lam-step ⟩ rest) → rtnN rest }

exp-app-pm : {V : Γ ⊢ᵛ X `× Y} {W : (Γ ∙ X ∙ Y) ⊢ᵛ Z `⇒ X₁} {W₁ : Γ ⊢ᵛ Z}
           → Redᶜ X₁ (pm V (app W (wk-val (wk-wk (wk-wk wk-id)) W₁))) → Redᶜ X₁ (app (pm V W) W₁)
exp-app-pm {V = V} {W} {W₁} (snM , rtnM) =
  sn (λ { app-pm-step → snM }) ,
  λ { (_ ~>⟨ app-pm-step ⟩ rest) → rtnM rest }

Red-varᵛ : (X : Ty) (i : Γ ∋ X) → Redᵛ X (var i)
Red-varᵛ `𝟙    i    = sn (λ ())
Red-varᵛ (X `× Y) i = sn (λ ()) , λ { (_ ~>⟨ () ⟩ _) }
Red-varᵛ (X `⇒ Y) i = sn (λ ()) , λ π {W} rw → sn (λ ()) , λ { (_ ~>⟨ () ⟩ _) }

--------------------------------------------------------------------------
-- weakening preserves reducibility

wk-reflect* : {Δ : Ctx} (π : Δ ⊇ Γ) {σ : Cfg Γ X} {σ₁ : Cfg Δ X}
            → wk-cfg π σ ↠ᵏ σ₁ → Σ[ σ₂ ∈ Cfg Γ X ] (σ ↠ᵏ σ₂) × (σ₁ ≡ wk-cfg π σ₂)
wk-reflect* π (_ ◼) = _ , (_ ◼) , refl
wk-reflect* π (_ ~>⟨ step ⟩ rest) with wk-reflect π step
wk-reflect* π (_ ~>⟨ step ⟩ rest) | (σ , σ-step , refl) with wk-reflect* π rest
... | (σ₁ , σ₁-steps , eq₂) = σ₁ , _ ~>⟨ σ-step ⟩ σ₁-steps , eq₂

pair-cfg-inv : {Δ : Ctx} {X Y : Ty} (π : Δ ⊇ Γ) {σ₁ : Cfg Γ (X `× Y)} {W₁ : Δ ⊢ᵛ X} {W₂ : Δ ⊢ᵛ Y}
             → [ pair W₁ W₂ ∥ ε ] ≡ wk-cfg π σ₁
             → Σ[ V₁ ∈ Γ ⊢ᵛ X ] Σ[ V₂ ∈ Γ ⊢ᵛ Y ] (σ₁ ≡ [ pair V₁ V₂ ∥ ε ]) × (wk-val π V₁ ≡ W₁) × (wk-val π V₂ ≡ W₂)
pair-cfg-inv π {σ₁ = ⟨ M ∥ K ⟩}               ()
pair-cfg-inv π {σ₁ = [ var i ∥ K ]}           ()
pair-cfg-inv π {σ₁ = [ lam N ∥ K ]}           ()
pair-cfg-inv π {σ₁ = [ pair V W ∥ ε ]}        refl = V , W , refl , refl , refl
pair-cfg-inv π {σ₁ = [ pair V W ∥ N ∷ K ]}    ()
pair-cfg-inv π {σ₁ = [ pair V W ∥ N pm∷ K ]}  ()
pair-cfg-inv π {σ₁ = [ pair V₁ V₂ ∥ W pmᵛ∷ K ]} ()
pair-cfg-inv π {σ₁ = [ pm V W ∥ K ]}          ()
pair-cfg-inv π {σ₁ = [ unit ∥ K ]}            ()

Red-wk : (X : Ty) {Δ : Ctx} (π : Δ ⊇ Γ) {V : Γ ⊢ᵛ X} → Redᵛ X V → Redᵛ X (wk-val π V)
Red-wk `𝟙    π r          = SN-wk π r
Red-wk (X `× Y) π {V} (snV , f) = SN-wk π snV , g
  where
  g : ∀ {W₁ W₂} → [ wk-val π V ∥ ε ] ↠ᵏ [ pair W₁ W₂ ∥ ε ] → Redᵛ X W₁ × Redᵛ Y W₂
  g p with wk-reflect* π p
  ... | (σ₁ , σ-steps , eq) with pair-cfg-inv π eq
  ... | (V₁ , V₂ , σ₁-eq , eqV₁ , eqV₂) with f (Eq.subst (λ x → [ V ∥ ε ] ↠ᵏ x) σ₁-eq σ-steps)
  ... | (redV₁ , redV₂) = Eq.subst (Redᵛ X) eqV₁ (Red-wk X π redV₁) , Eq.subst (Redᵛ Y) eqV₂ (Red-wk Y π redV₂)
Red-wk (X `⇒ Y) π {V} (snV , f) = SN-wk π snV , harrow
  where
  harrow : ∀ {Γ} (δ : Γ ⊇ _) {W : Γ ⊢ᵛ X} → Redᵛ X W → Redᶜ Y (app (wk-val δ (wk-val π V)) W)
  harrow δ {W = W} redW =
    Eq.subst (Redᶜ Y) (sym (cong (λ x → app x W) (wk-val-trans V δ π))) (f (wk-trans δ π) redW)

sub-val-ins2-cancel : (V₁ : Γ ⊢ᵛ X) (V₂ : Γ ⊢ᵛ Y) (W : Γ ⊢ᵛ Z)
                     → sub-val (sub-ex (sub-ex sub-id V₁) V₂) (wk-val (wk-wk (wk-wk wk-id)) W) ≡ W
sub-val-ins2-cancel V₁ V₂ W = begin
  sub-val (sub-ex (sub-ex sub-id V₁) V₂) (wk-val (wk-wk (wk-wk wk-id)) W)  ≡⟨ sub-val-wk-pre (sub-ex (sub-ex sub-id V₁) V₂) (wk-wk (wk-wk wk-id)) W ⟩
  sub-val (sub-pre sub-id wk-id) W                                      ≡⟨ cong (λ θ → sub-val θ W) (sub-pre-wk-id sub-id) ⟩
  sub-val sub-id W                                                      ≡⟨ sub-val-id W ⟩
  W ∎

exp-pm-val : (Z : Ty) {V : Γ ⊢ᵛ X `× Y} {W : (Γ ∙ X ∙ Y) ⊢ᵛ Z}
           → Redᵛ (X `× Y) V
           → (∀ {Δ} (π : Δ ⊇ Γ) {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → Redᵛ Z (sub-val (sub-ex (sub-ex sub-id V₁) V₂) (wk-val (wk-cong (wk-cong π)) W)))
           → Redᵛ Z (pm V W)
exp-pm-val {Γ} {X} {Y} `𝟙 {V} {W} redV H =
  sn (λ { pm-val-step →
    SN-ext-pmᵛ∷-V (Red→SNᵛ _ V redV) (proj₂ redV)
      (λ redV₁ redV₂ → Red→SNᵛ `𝟙 _ (H₀ redV₁ redV₂)) })
  where
  H₀ : ∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → Redᵛ `𝟙 (sub-val (sub-ex (sub-ex sub-id V₁) V₂) W)
  H₀ {V₁} {V₂} redV₁ redV₂ = Eq.subst (Redᵛ `𝟙) (cong (sub-val (sub-ex (sub-ex sub-id V₁) V₂)) (wk-val-id W)) (H wk-id redV₁ redV₂)
exp-pm-val {Γ} {X} {Y} (Z `× X₁) {V} {W} redV H =
  sn (λ { pm-val-step →
    SN-ext-pmᵛ∷-V (Red→SNᵛ _ V redV) (proj₂ redV)
      (λ redV₁ redV₂ → Red→SNᵛ (Z `× X₁) _ (H₀ redV₁ redV₂)) }) ,
  λ { (_ ~>⟨ pm-val-step ⟩ rest) → RTN-ext-pmᵛ∷ᴾ-V (proj₂ redV) (λ redV₁ redV₂ → proj₂ (H₀ redV₁ redV₂)) rest }
  where
  H₀ : ∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → Redᵛ (Z `× X₁) (sub-val (sub-ex (sub-ex sub-id V₁) V₂) W)
  H₀ {V₁} {V₂} redV₁ redV₂ = Eq.subst (Redᵛ (Z `× X₁)) (cong (sub-val (sub-ex (sub-ex sub-id V₁) V₂)) (wk-val-id W)) (H wk-id redV₁ redV₂)
exp-pm-val {Γ} {X} {Y} (Z `⇒ X₁) {V} {W} redV H =
  sn (λ { pm-val-step →
    SN-ext-pmᵛ∷-V (Red→SNᵛ _ V redV) (proj₂ redV)
      (λ redV₁ redV₂ → Red→SNᵛ (Z `⇒ X₁) _ (H₀ redV₁ redV₂)) }) ,
  harrow
  where
  H₀ : ∀ {V₁ V₂} → Redᵛ X V₁ → Redᵛ Y V₂ → Redᵛ (Z `⇒ X₁) (sub-val (sub-ex (sub-ex sub-id V₁) V₂) W)
  H₀ {V₁} {V₂} redV₁ redV₂ = Eq.subst (Redᵛ (Z `⇒ X₁)) (cong (sub-val (sub-ex (sub-ex sub-id V₁) V₂)) (wk-val-id W)) (H wk-id redV₁ redV₂)

  harrow : ∀ {Δ} (ρ : Δ ⊇ Γ) {W₁ : Δ ⊢ᵛ Z} → Redᵛ Z W₁ → Redᶜ X₁ (app (wk-val ρ (pm V W)) W₁)
  harrow ρ {W₁} redW₁ =
    exp-app-pm
      (exp-pm-comp (Red-wk (X `× Y) ρ redV)
        (λ {V₁} {V₂} redV₁ redV₂ →
          Eq.subst (Redᶜ X₁)
                   (cong (λ w → app w (sub-val (sub-ex (sub-ex sub-id V₁) V₂) (wk-val (wk-wk (wk-wk wk-id)) W₁)))
                         (wk-val-id (sub-val (sub-ex (sub-ex sub-id V₁) V₂) (wk-val (wk-cong (wk-cong ρ)) W))))
                   (proj₂ (H ρ redV₁ redV₂) wk-id (Eq.subst (Redᵛ Z) (sym (sub-val-ins2-cancel V₁ V₂ W₁)) redW₁))))

record RedSub (θ : Γ ⊢ Δ) : Set where
  field red : (i : Δ ∋ X) → Redᵛ X (sub-mem θ i)
open RedSub

RedSub-wk : {Ψ : Ctx} (ρ : Ψ ⊇ Γ) {θ : Γ ⊢ Δ} → RedSub θ → RedSub (sub-wk ρ θ)
RedSub-wk ρ {θ} rθ = record
  { red = λ i → Eq.subst (Redᵛ _) (sym (sub-mem-wk ρ θ i)) (Red-wk _ ρ (rθ .red i)) }

RedSub-ext : {θ : Γ ⊢ Δ} {V : Γ ⊢ᵛ X} → RedSub θ → Redᵛ X V → RedSub (sub-ex θ V)
RedSub-ext rθ rv = record { red = λ { here → rv ; (there i) → rθ .red i } }

RedSub-id : RedSub (sub-id {Γ})
RedSub-id {Γ} = record { red = λ i → Eq.subst (Redᵛ _) (sym (sub-mem-id i)) (Red-varᵛ _ i) }

--------------------------------------------------------------------------
-- fundamental lemma

Fundamental-val : (θ : Γ ⊢ Δ) → RedSub θ → (V : Δ ⊢ᵛ X) → Redᵛ X (sub-val θ V)
Fundamental-comp : (θ : Γ ⊢ Δ) → RedSub θ → (M : Δ ⊢ᶜ X) → Redᶜ X (sub-comp θ M)

Fundamental-val θ rθ (var i) = rθ .red i
Fundamental-val θ rθ unit    = sn (λ ())
Fundamental-val θ rθ (lam M) =
  sn (λ ()) ,
  λ π {W} rw →
    exp-app-lam (Eq.subst (Redᶜ _) (sym (fund-lam-eq θ π W M))
                          (Fundamental-comp (sub-ex (sub-wk π θ) W) (RedSub-ext (RedSub-wk π rθ) rw) M))
Fundamental-val θ rθ (pair V W) =
  sn (λ ()) , λ { (_ ◼) → Fundamental-val θ rθ V , Fundamental-val θ rθ W ; (_ ~>⟨ () ⟩ _) }
Fundamental-val θ rθ (pm {X = X} {Y = Y} V W) =
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
Fundamental-comp θ rθ (pm {X = X} {Y = Y} V M) =
  exp-pm-comp (Fundamental-val θ rθ V)
              (λ {V₁} {V₂} redV₁ redV₂ →
                Eq.subst (Redᶜ _) (sym (fund-pm-eqᶜ θ V₁ V₂ M))
                         (Fundamental-comp (sub-ex (sub-ex θ V₁) V₂) (RedSub-ext (RedSub-ext rθ redV₁) redV₂) M))

SN-theorem : (M : Γ ⊢ᶜ X) → SN ⟨ M ∥ ε ⟩
SN-theorem {Γ} {X} M =
  Eq.subst (λ x → SN ⟨ x ∥ ε ⟩) (sub-comp-id M)
           (Red→SNᶜ X (sub-comp sub-id M) (Fundamental-comp sub-id RedSub-id M))

--------------------------------------------------------------------------
-- eval

Normal : Cfg Γ X → Set
Normal σ = ∀ {σ₁} → σ →ᵏ σ₁ → ⊥

data Step? (σ : Cfg Γ X) : Set where
  done : Normal σ → Step? σ
  next : {σ₁ : Cfg Γ X} → σ →ᵏ σ₁ → Step? σ

step? : (σ : Cfg Γ X) → Step? σ
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

eval-acc : {σ : Cfg Γ X} → SN σ → Σ[ σ₁ ∈ Cfg Γ X ] (σ ↠ᵏ σ₁) × Normal σ₁
eval-acc {σ = σ} (sn f) with step? σ
... | done normal    = σ , σ ◼ , normal
... | next {σ₁} step with eval-acc (f step)
...   | (σ₂ , chain , normal) = σ₂ , σ ~>⟨ step ⟩ chain , normal

eval : (M : Γ ⊢ᶜ X) → Σ[ σ₁ ∈ Cfg Γ X ] (⟨ M ∥ ε ⟩ ↠ᵏ σ₁) × Normal σ₁
eval M = eval-acc (SN-theorem M)
