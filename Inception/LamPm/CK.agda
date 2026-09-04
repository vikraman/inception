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

  pm-pair-step   : {L : Γ ⊢ᵛ A} {R : Γ ⊢ᵛ B} {N : (Γ ∙ A ∙ B) ⊢ᶜ C} {K : Γ ⊢ᵏ C ⇒ D}
                 → [ pair L R ∥ N pm∷ K ] →ᵏ ⟨ sub-comp (sub-ex (sub-ex sub-id L) R) N ∥ K ⟩

  pm-val-step    : {V : Γ ⊢ᵛ A `× B} {W : (Γ ∙ A ∙ B) ⊢ᵛ C} {K : Γ ⊢ᵏ C ⇒ D}
                 → [ pm V W ∥ K ] →ᵏ [ V ∥ W pmᵛ∷ K ]

  pmᵛ-pair-step  : {L : Γ ⊢ᵛ A} {R : Γ ⊢ᵛ B} {W : (Γ ∙ A ∙ B) ⊢ᵛ C} {K : Γ ⊢ᵏ C ⇒ D}
                 → [ pair L R ∥ W pmᵛ∷ K ] →ᵏ [ sub-val (sub-ex (sub-ex sub-id L) R) W ∥ K ]

  app-lam-step   : {N : (Γ ∙ A) ⊢ᶜ B} {V : Γ ⊢ᵛ A} {K : Γ ⊢ᵏ B ⇒ C}
                 → ⟨ app (lam N) V ∥ K ⟩ →ᵏ ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩

  app-pm-step    : {V : Γ ⊢ᵛ X `× Y} {W : (Γ ∙ X ∙ Y) ⊢ᵛ A `⇒ B} {N : Γ ⊢ᵛ A} {K : Γ ⊢ᵏ B ⇒ C}
                 → ⟨ app (pm V W) N ∥ K ⟩ →ᵏ ⟨ pm V (app W (wk-val (wk-wk (wk-wk wk-id)) N)) ∥ K ⟩

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

wk-ins2 : {Γ Γ' : Ctx} {X Y A : Ty} (π : Γ' ⊇ Γ) (N : Γ ⊢ᵛ A) →
        wk-val (wk-wk {A = Y} (wk-wk {A = X} wk-id)) (wk-val π N) ≡ wk-val (wk-cong {A = Y} (wk-cong {A = X} π)) (wk-val (wk-wk {A = Y} (wk-wk {A = X} wk-id)) N)
wk-ins2 {X = X} {Y = Y} π N = begin
    wk-val (wk-wk {A = Y} (wk-wk {A = X} wk-id)) (wk-val π N)
  ≡⟨ wk-val-trans N (wk-wk {A = Y} (wk-wk {A = X} wk-id)) π ⟩
    wk-val (wk-wk {A = Y} (wk-wk {A = X} (wk-trans wk-id π))) N
  ≡⟨ cong (λ x → wk-val (wk-wk {A = Y} (wk-wk {A = X} x)) N) (wk-trans-idl π) ⟩
    wk-val (wk-wk {A = Y} (wk-wk {A = X} π)) N
  ≡˘⟨ cong (λ x → wk-val (wk-wk {A = Y} (wk-wk {A = X} x)) N) (wk-trans-idr π) ⟩
    wk-val (wk-wk {A = Y} (wk-wk {A = X} (wk-trans π wk-id))) N
  ≡˘⟨ wk-val-trans N (wk-cong {A = Y} (wk-cong {A = X} π)) (wk-wk {A = Y} (wk-wk {A = X} wk-id)) ⟩
    wk-val (wk-cong {A = Y} (wk-cong {A = X} π)) (wk-val (wk-wk {A = Y} (wk-wk {A = X} wk-id)) N) ∎

wk-step : {Γ' : Ctx} (π : Γ' ⊇ Γ) {σ σ' : Cfg Γ B} → σ →ᵏ σ' → wk-cfg π σ →ᵏ wk-cfg π σ'
wk-step π push-step = push-step
wk-step π (return-step {V = V} {N = N} {K = K}) =
  Eq.subst (λ x → ⟨ return (wk-val π V) ∥ wk-comp (wk-cong π) N ∷ wk-stk π K ⟩ →ᵏ ⟨ x ∥ wk-stk π K ⟩)
           (wk-beta-1 π V N) return-step
wk-step π pm-step = pm-step
wk-step π (pm-pair-step {L = L} {R = R} {N = N} {K = K}) =
  Eq.subst (λ x → [ pair (wk-val π L) (wk-val π R) ∥ wk-comp (wk-cong (wk-cong π)) N pm∷ wk-stk π K ] →ᵏ ⟨ x ∥ wk-stk π K ⟩)
           (wk-beta-pmᶜ π L R N) pm-pair-step
wk-step π pm-val-step = pm-val-step
wk-step π (pmᵛ-pair-step {L = L} {R = R} {W = W} {K = K}) =
  Eq.subst (λ x → [ pair (wk-val π L) (wk-val π R) ∥ wk-val (wk-cong (wk-cong π)) W pmᵛ∷ wk-stk π K ] →ᵏ [ x ∥ wk-stk π K ])
           (wk-beta-pmᵛ π L R W) pmᵛ-pair-step
wk-step π (app-lam-step {N = N} {V = V} {K = K}) =
  Eq.subst (λ x → ⟨ app (lam (wk-comp (wk-cong π) N)) (wk-val π V) ∥ wk-stk π K ⟩ →ᵏ ⟨ x ∥ wk-stk π K ⟩)
           (wk-beta-1 π V N) app-lam-step
wk-step π (app-pm-step {X = X} {Y = Y} {V = V} {W = W} {N = N} {K = K}) =
  Eq.subst (λ x → ⟨ app (pm (wk-val π V) (wk-val (wk-cong (wk-cong π)) W)) (wk-val π N) ∥ wk-stk π K ⟩ →ᵏ ⟨ pm (wk-val π V) x ∥ wk-stk π K ⟩)
           (Eq.cong (app (wk-val (wk-cong (wk-cong π)) W)) (wk-ins2 {X = X} {Y = Y} π N))
           app-pm-step

wk-reflect : {Γ' : Ctx} (π : Γ' ⊇ Γ) {σ : Cfg Γ B} {τ' : Cfg Γ' B}
           → wk-cfg π σ →ᵏ τ' → Σ[ σ' ∈ Cfg Γ B ] (σ →ᵏ σ') × (τ' ≡ wk-cfg π σ')
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
wk-reflect π {σ = [ pair L R ∥ ε ]} ()
wk-reflect π {σ = [ pair L R ∥ N ∷ K ]} ()
wk-reflect π {σ = [ pair L R ∥ N pm∷ K ]} pm-pair-step =
  ⟨ sub-comp (sub-ex (sub-ex sub-id L) R) N ∥ K ⟩ , pm-pair-step ,
  Eq.cong (λ x → ⟨ x ∥ wk-stk π K ⟩) (wk-beta-pmᶜ π L R N)
wk-reflect π {σ = [ pair L R ∥ W pmᵛ∷ K ]} pmᵛ-pair-step =
  [ sub-val (sub-ex (sub-ex sub-id L) R) W ∥ K ] , pmᵛ-pair-step ,
  Eq.cong (λ x → [ x ∥ wk-stk π K ]) (wk-beta-pmᵛ π L R W)
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
graft (N ∷ K₀)   K = N ∷ graft K₀ K
graft (N pm∷ K₀)  K = N pm∷ graft K₀ K
graft (W pmᵛ∷ K₀) K = W pmᵛ∷ graft K₀ K

Redᵛ : (A : Ty) → Γ ⊢ᵛ A → Set
Redᶜ : (A : Ty) → Γ ⊢ᶜ A → Set

Redᵛ `Unit       V = SN [ V ∥ ε ]
Redᵛ (A `× B)    V = SN [ V ∥ ε ] × (∀ {L R} → [ V ∥ ε ] ↠ᵏ [ pair L R ∥ ε ] → Redᵛ A L × Redᵛ B R)
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
  SN-ext∷-C : {E : Ty} {M : Γ ⊢ᶜ A} {K₀ : Γ ⊢ᵏ A ⇒ D} {N : (Γ ∙ D) ⊢ᶜ E} {K : Γ ⊢ᵏ E ⇒ C}
            → SN ⟨ M ∥ K₀ ⟩
            → (∀ {V} → ⟨ M ∥ K₀ ⟩ ↠ᵏ ⟨ return V ∥ ε ⟩ → Redᵛ D V)
            → (∀ {V} → Redᵛ D V → SN ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩)
            → SN ⟨ M ∥ graft K₀ (N ∷ K) ⟩
  SN-ext∷-C {M = push M₀ N₀} (sn f) rtn H =
    sn (λ { push-step → SN-ext∷-C (f push-step) (λ ch → rtn (_ ~>⟨ push-step ⟩ ch)) H })
  SN-ext∷-C {M = app (var i) V} (sn f) rtn H = sn (λ ())
  SN-ext∷-C {M = app (lam N₀) V} (sn f) rtn H =
    sn (λ { app-lam-step → SN-ext∷-C (f app-lam-step) (λ ch → rtn (_ ~>⟨ app-lam-step ⟩ ch)) H })
  SN-ext∷-C {M = app (pm V₀ W₀) V} (sn f) rtn H =
    sn (λ { app-pm-step → SN-ext∷-C (f app-pm-step) (λ ch → rtn (_ ~>⟨ app-pm-step ⟩ ch)) H })
  SN-ext∷-C {M = pm V₀ N₀} (sn f) rtn H =
    sn (λ { pm-step → SN-ext∷-V (f pm-step) (λ ch → rtn (_ ~>⟨ pm-step ⟩ ch)) H })
  SN-ext∷-C {M = return V} {K₀ = ε} (sn f) rtn H =
    sn (λ { return-step → H (rtn (_ ◼)) })
  SN-ext∷-C {M = return V} {K₀ = N₀ ∷ K₀} (sn f) rtn H =
    sn (λ { return-step → SN-ext∷-C (f return-step) (λ ch → rtn (_ ~>⟨ return-step ⟩ ch)) H })
  SN-ext∷-C {M = return V} {K₀ = N₀ pm∷ K₀} (sn f) rtn H = sn (λ ())
  SN-ext∷-C {M = return V} {K₀ = W₀ pmᵛ∷ K₀} (sn f) rtn H = sn (λ ())

  SN-ext∷-V : {E : Ty} {V : Γ ⊢ᵛ A} {K₀ : Γ ⊢ᵏ A ⇒ D} {N : (Γ ∙ D) ⊢ᶜ E} {K : Γ ⊢ᵏ E ⇒ C}
            → SN [ V ∥ K₀ ]
            → (∀ {V'} → [ V ∥ K₀ ] ↠ᵏ ⟨ return V' ∥ ε ⟩ → Redᵛ D V')
            → (∀ {V'} → Redᵛ D V' → SN ⟨ sub-comp (sub-ex sub-id V') N ∥ K ⟩)
            → SN [ V ∥ graft K₀ (N ∷ K) ]
  SN-ext∷-V {V = var i} (sn f) rtn H = sn (λ ())
  SN-ext∷-V {V = lam N₀} (sn f) rtn H = sn (λ ())
  SN-ext∷-V {V = unit} (sn f) rtn H = sn (λ ())
  SN-ext∷-V {V = pm V₀ W₀} (sn f) rtn H =
    sn (λ { pm-val-step → SN-ext∷-V (f pm-val-step) (λ ch → rtn (_ ~>⟨ pm-val-step ⟩ ch)) H })
  SN-ext∷-V {V = pair L R} {K₀ = ε} (sn f) rtn H = sn (λ ())
  SN-ext∷-V {V = pair L R} {K₀ = N₀ ∷ K₀} (sn f) rtn H = sn (λ ())
  SN-ext∷-V {V = pair L R} {K₀ = N₀ pm∷ K₀} (sn f) rtn H =
    sn (λ { pm-pair-step → SN-ext∷-C (f pm-pair-step) (λ ch → rtn (_ ~>⟨ pm-pair-step ⟩ ch)) H })
  SN-ext∷-V {V = pair L R} {K₀ = W₀ pmᵛ∷ K₀} (sn f) rtn H =
    sn (λ { pmᵛ-pair-step → SN-ext∷-V (f pmᵛ-pair-step) (λ ch → rtn (_ ~>⟨ pmᵛ-pair-step ⟩ ch)) H })

mutual
  RTN-ext∷-C : {E : Ty} {M : Γ ⊢ᶜ A} {K₀ : Γ ⊢ᵏ A ⇒ D} {N : (Γ ∙ D) ⊢ᶜ E} {K : Γ ⊢ᵏ E ⇒ C}
             → (∀ {V} → ⟨ M ∥ K₀ ⟩ ↠ᵏ ⟨ return V ∥ ε ⟩ → Redᵛ D V)
             → (∀ {V} → Redᵛ D V → ∀ {V'} → ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩ ↠ᵏ ⟨ return V' ∥ ε ⟩ → Redᵛ C V')
             → {V' : _} → ⟨ M ∥ graft K₀ (N ∷ K) ⟩ ↠ᵏ ⟨ return V' ∥ ε ⟩ → Redᵛ C V'
  RTN-ext∷-C {M = push M₀ N₀} rtn H2 (_ ~>⟨ push-step ⟩ rest) =
    RTN-ext∷-C (λ ch → rtn (_ ~>⟨ push-step ⟩ ch)) H2 rest
  RTN-ext∷-C {M = app (var i) V} rtn H2 (_ ~>⟨ () ⟩ rest)
  RTN-ext∷-C {M = app (lam N₀) V} rtn H2 (_ ~>⟨ app-lam-step ⟩ rest) =
    RTN-ext∷-C (λ ch → rtn (_ ~>⟨ app-lam-step ⟩ ch)) H2 rest
  RTN-ext∷-C {M = app (pm V₀ W₀) V} rtn H2 (_ ~>⟨ app-pm-step ⟩ rest) =
    RTN-ext∷-C (λ ch → rtn (_ ~>⟨ app-pm-step ⟩ ch)) H2 rest
  RTN-ext∷-C {M = pm V₀ N₀} rtn H2 (_ ~>⟨ pm-step ⟩ rest) =
    RTN-ext∷-V (λ ch → rtn (_ ~>⟨ pm-step ⟩ ch)) H2 rest
  RTN-ext∷-C {M = return V} {K₀ = ε} rtn H2 (_ ~>⟨ return-step ⟩ rest) = H2 (rtn (_ ◼)) rest
  RTN-ext∷-C {M = return V} {K₀ = N₀ ∷ K₀} rtn H2 (_ ~>⟨ return-step ⟩ rest) =
    RTN-ext∷-C (λ ch → rtn (_ ~>⟨ return-step ⟩ ch)) H2 rest
  RTN-ext∷-C {M = return V} {K₀ = N₀ pm∷ K₀} rtn H2 (_ ~>⟨ () ⟩ rest)
  RTN-ext∷-C {M = return V} {K₀ = W₀ pmᵛ∷ K₀} rtn H2 (_ ~>⟨ () ⟩ rest)

  RTN-ext∷-V : {E : Ty} {V : Γ ⊢ᵛ A} {K₀ : Γ ⊢ᵏ A ⇒ D} {N : (Γ ∙ D) ⊢ᶜ E} {K : Γ ⊢ᵏ E ⇒ C}
             → (∀ {V'} → [ V ∥ K₀ ] ↠ᵏ ⟨ return V' ∥ ε ⟩ → Redᵛ D V')
             → (∀ {V'} → Redᵛ D V' → ∀ {V''} → ⟨ sub-comp (sub-ex sub-id V') N ∥ K ⟩ ↠ᵏ ⟨ return V'' ∥ ε ⟩ → Redᵛ C V'')
             → {V'' : _} → [ V ∥ graft K₀ (N ∷ K) ] ↠ᵏ ⟨ return V'' ∥ ε ⟩ → Redᵛ C V''
  RTN-ext∷-V {V = var i} rtn H2 (_ ~>⟨ () ⟩ rest)
  RTN-ext∷-V {V = lam N₀} rtn H2 (_ ~>⟨ () ⟩ rest)
  RTN-ext∷-V {V = unit} rtn H2 (_ ~>⟨ () ⟩ rest)
  RTN-ext∷-V {V = pm V₀ W₀} rtn H2 (_ ~>⟨ pm-val-step ⟩ rest) =
    RTN-ext∷-V (λ ch → rtn (_ ~>⟨ pm-val-step ⟩ ch)) H2 rest
  RTN-ext∷-V {V = pair L R} {K₀ = ε} rtn H2 (_ ~>⟨ () ⟩ rest)
  RTN-ext∷-V {V = pair L R} {K₀ = N₀ ∷ K₀} rtn H2 (_ ~>⟨ () ⟩ rest)
  RTN-ext∷-V {V = pair L R} {K₀ = N₀ pm∷ K₀} rtn H2 (_ ~>⟨ pm-pair-step ⟩ rest) =
    RTN-ext∷-C (λ ch → rtn (_ ~>⟨ pm-pair-step ⟩ ch)) H2 rest
  RTN-ext∷-V {V = pair L R} {K₀ = W₀ pmᵛ∷ K₀} rtn H2 (_ ~>⟨ pmᵛ-pair-step ⟩ rest) =
    RTN-ext∷-V (λ ch → rtn (_ ~>⟨ pmᵛ-pair-step ⟩ ch)) H2 rest

exp-push : {M : Γ ⊢ᶜ A} {N : (Γ ∙ A) ⊢ᶜ B}
         → Redᶜ A M → (∀ {V} → Redᵛ A V → Redᶜ B (sub-comp (sub-ex sub-id V) N))
         → Redᶜ B (push M N)
exp-push {M = M} {N} rM H =
  sn (λ { push-step → SN-ext∷-C (Red→SNᶜ _ _ rM) (Red→RTNᶜ _ _ rM) (λ {V} rv → Red→SNᶜ _ _ (H rv)) }) ,
  λ { (_ ~>⟨ push-step ⟩ rest) → RTN-ext∷-C (Red→RTNᶜ _ _ rM) (λ {V} rv → Red→RTNᶜ _ _ (H rv)) rest }

mutual
  SN-ext-pm∷-C : {X Y E : Ty} {M : Γ ⊢ᶜ A} {K₀ : Γ ⊢ᵏ A ⇒ (X `× Y)} {N : (Γ ∙ X ∙ Y) ⊢ᶜ E} {K : Γ ⊢ᵏ E ⇒ C}
               → SN ⟨ M ∥ K₀ ⟩
               → (∀ {L R} → ⟨ M ∥ K₀ ⟩ ↠ᵏ [ pair L R ∥ ε ] → Redᵛ X L × Redᵛ Y R)
               → (∀ {L R} → Redᵛ X L → Redᵛ Y R → SN ⟨ sub-comp (sub-ex (sub-ex sub-id L) R) N ∥ K ⟩)
               → SN ⟨ M ∥ graft K₀ (N pm∷ K) ⟩
  SN-ext-pm∷-C {M = push M₀ N₀} (sn f) rtn H =
    sn (λ { push-step → SN-ext-pm∷-C (f push-step) (λ ch → rtn (_ ~>⟨ push-step ⟩ ch)) H })
  SN-ext-pm∷-C {M = app (var i) V} (sn f) rtn H = sn (λ ())
  SN-ext-pm∷-C {M = app (lam N₀) V} (sn f) rtn H =
    sn (λ { app-lam-step → SN-ext-pm∷-C (f app-lam-step) (λ ch → rtn (_ ~>⟨ app-lam-step ⟩ ch)) H })
  SN-ext-pm∷-C {M = app (pm V₀ W₀) V} (sn f) rtn H =
    sn (λ { app-pm-step → SN-ext-pm∷-C (f app-pm-step) (λ ch → rtn (_ ~>⟨ app-pm-step ⟩ ch)) H })
  SN-ext-pm∷-C {M = pm V₀ N₀} (sn f) rtn H =
    sn (λ { pm-step → SN-ext-pm∷-V (f pm-step) (λ ch → rtn (_ ~>⟨ pm-step ⟩ ch)) H })
  SN-ext-pm∷-C {M = return V} {K₀ = ε} (sn f) rtn H = sn (λ ())
  SN-ext-pm∷-C {M = return V} {K₀ = N₀ ∷ K₀} (sn f) rtn H =
    sn (λ { return-step → SN-ext-pm∷-C (f return-step) (λ ch → rtn (_ ~>⟨ return-step ⟩ ch)) H })
  SN-ext-pm∷-C {M = return V} {K₀ = N₀ pm∷ K₀} (sn f) rtn H = sn (λ ())
  SN-ext-pm∷-C {M = return V} {K₀ = W₀ pmᵛ∷ K₀} (sn f) rtn H = sn (λ ())

  SN-ext-pm∷-V : {X Y E : Ty} {V : Γ ⊢ᵛ A} {K₀ : Γ ⊢ᵏ A ⇒ (X `× Y)} {N : (Γ ∙ X ∙ Y) ⊢ᶜ E} {K : Γ ⊢ᵏ E ⇒ C}
               → SN [ V ∥ K₀ ]
               → (∀ {L R} → [ V ∥ K₀ ] ↠ᵏ [ pair L R ∥ ε ] → Redᵛ X L × Redᵛ Y R)
               → (∀ {L R} → Redᵛ X L → Redᵛ Y R → SN ⟨ sub-comp (sub-ex (sub-ex sub-id L) R) N ∥ K ⟩)
               → SN [ V ∥ graft K₀ (N pm∷ K) ]
  SN-ext-pm∷-V {V = var i} (sn f) rtn H = sn (λ ())
  SN-ext-pm∷-V {V = lam N₀} (sn f) rtn H = sn (λ ())
  SN-ext-pm∷-V {V = unit} (sn f) rtn H = sn (λ ())
  SN-ext-pm∷-V {V = pm V₀ W₀} (sn f) rtn H =
    sn (λ { pm-val-step → SN-ext-pm∷-V (f pm-val-step) (λ ch → rtn (_ ~>⟨ pm-val-step ⟩ ch)) H })
  SN-ext-pm∷-V {V = pair L R} {K₀ = ε} (sn f) rtn H =
    sn (λ { pm-pair-step → H (proj₁ (rtn (_ ◼))) (proj₂ (rtn (_ ◼))) })
  SN-ext-pm∷-V {V = pair L R} {K₀ = N₀ ∷ K₀} (sn f) rtn H = sn (λ ())
  SN-ext-pm∷-V {V = pair L R} {K₀ = N₀ pm∷ K₀} (sn f) rtn H =
    sn (λ { pm-pair-step → SN-ext-pm∷-C (f pm-pair-step) (λ ch → rtn (_ ~>⟨ pm-pair-step ⟩ ch)) H })
  SN-ext-pm∷-V {V = pair L R} {K₀ = W₀ pmᵛ∷ K₀} (sn f) rtn H =
    sn (λ { pmᵛ-pair-step → SN-ext-pm∷-V (f pmᵛ-pair-step) (λ ch → rtn (_ ~>⟨ pmᵛ-pair-step ⟩ ch)) H })

mutual
  RTN-ext-pm∷-C : {X Y E : Ty} {M : Γ ⊢ᶜ A} {K₀ : Γ ⊢ᵏ A ⇒ (X `× Y)} {N : (Γ ∙ X ∙ Y) ⊢ᶜ E} {K : Γ ⊢ᵏ E ⇒ C}
                → (∀ {L R} → ⟨ M ∥ K₀ ⟩ ↠ᵏ [ pair L R ∥ ε ] → Redᵛ X L × Redᵛ Y R)
                → (∀ {L R} → Redᵛ X L → Redᵛ Y R → ∀ {V'} → ⟨ sub-comp (sub-ex (sub-ex sub-id L) R) N ∥ K ⟩ ↠ᵏ ⟨ return V' ∥ ε ⟩ → Redᵛ C V')
                → {V' : _} → ⟨ M ∥ graft K₀ (N pm∷ K) ⟩ ↠ᵏ ⟨ return V' ∥ ε ⟩ → Redᵛ C V'
  RTN-ext-pm∷-C {M = push M₀ N₀} rtn H2 (_ ~>⟨ push-step ⟩ rest) =
    RTN-ext-pm∷-C (λ ch → rtn (_ ~>⟨ push-step ⟩ ch)) H2 rest
  RTN-ext-pm∷-C {M = app (var i) V} rtn H2 (_ ~>⟨ () ⟩ rest)
  RTN-ext-pm∷-C {M = app (lam N₀) V} rtn H2 (_ ~>⟨ app-lam-step ⟩ rest) =
    RTN-ext-pm∷-C (λ ch → rtn (_ ~>⟨ app-lam-step ⟩ ch)) H2 rest
  RTN-ext-pm∷-C {M = app (pm V₀ W₀) V} rtn H2 (_ ~>⟨ app-pm-step ⟩ rest) =
    RTN-ext-pm∷-C (λ ch → rtn (_ ~>⟨ app-pm-step ⟩ ch)) H2 rest
  RTN-ext-pm∷-C {M = pm V₀ N₀} rtn H2 (_ ~>⟨ pm-step ⟩ rest) =
    RTN-ext-pm∷-V (λ ch → rtn (_ ~>⟨ pm-step ⟩ ch)) H2 rest
  RTN-ext-pm∷-C {M = return V} {K₀ = ε} rtn H2 (_ ~>⟨ () ⟩ rest)
  RTN-ext-pm∷-C {M = return V} {K₀ = N₀ ∷ K₀} rtn H2 (_ ~>⟨ return-step ⟩ rest) =
    RTN-ext-pm∷-C (λ ch → rtn (_ ~>⟨ return-step ⟩ ch)) H2 rest
  RTN-ext-pm∷-C {M = return V} {K₀ = N₀ pm∷ K₀} rtn H2 (_ ~>⟨ () ⟩ rest)
  RTN-ext-pm∷-C {M = return V} {K₀ = W₀ pmᵛ∷ K₀} rtn H2 (_ ~>⟨ () ⟩ rest)

  RTN-ext-pm∷-V : {X Y E : Ty} {V : Γ ⊢ᵛ A} {K₀ : Γ ⊢ᵏ A ⇒ (X `× Y)} {N : (Γ ∙ X ∙ Y) ⊢ᶜ E} {K : Γ ⊢ᵏ E ⇒ C}
                → (∀ {L R} → [ V ∥ K₀ ] ↠ᵏ [ pair L R ∥ ε ] → Redᵛ X L × Redᵛ Y R)
                → (∀ {L R} → Redᵛ X L → Redᵛ Y R → ∀ {V'} → ⟨ sub-comp (sub-ex (sub-ex sub-id L) R) N ∥ K ⟩ ↠ᵏ ⟨ return V' ∥ ε ⟩ → Redᵛ C V')
                → {V' : _} → [ V ∥ graft K₀ (N pm∷ K) ] ↠ᵏ ⟨ return V' ∥ ε ⟩ → Redᵛ C V'
  RTN-ext-pm∷-V {V = pm V₀ W₀} rtn H2 (_ ~>⟨ pm-val-step ⟩ rest) =
    RTN-ext-pm∷-V (λ ch → rtn (_ ~>⟨ pm-val-step ⟩ ch)) H2 rest
  RTN-ext-pm∷-V {V = pair L R} {K₀ = ε} rtn H2 (_ ~>⟨ pm-pair-step ⟩ rest) =
    H2 (proj₁ (rtn (_ ◼))) (proj₂ (rtn (_ ◼))) rest
  RTN-ext-pm∷-V {V = pair L R} {K₀ = N₀ pm∷ K₀} rtn H2 (_ ~>⟨ pm-pair-step ⟩ rest) =
    RTN-ext-pm∷-C (λ ch → rtn (_ ~>⟨ pm-pair-step ⟩ ch)) H2 rest
  RTN-ext-pm∷-V {V = pair L R} {K₀ = W₀ pmᵛ∷ K₀} rtn H2 (_ ~>⟨ pmᵛ-pair-step ⟩ rest) =
    RTN-ext-pm∷-V (λ ch → rtn (_ ~>⟨ pmᵛ-pair-step ⟩ ch)) H2 rest

mutual
  SN-ext-pmᵛ∷-C : {X Y E : Ty} {M : Γ ⊢ᶜ A} {K₀ : Γ ⊢ᵏ A ⇒ (X `× Y)} {W : (Γ ∙ X ∙ Y) ⊢ᵛ E} {K : Γ ⊢ᵏ E ⇒ C}
               → SN ⟨ M ∥ K₀ ⟩
               → (∀ {L R} → ⟨ M ∥ K₀ ⟩ ↠ᵏ [ pair L R ∥ ε ] → Redᵛ X L × Redᵛ Y R)
               → (∀ {L R} → Redᵛ X L → Redᵛ Y R → SN [ sub-val (sub-ex (sub-ex sub-id L) R) W ∥ K ])
               → SN ⟨ M ∥ graft K₀ (W pmᵛ∷ K) ⟩
  SN-ext-pmᵛ∷-C {M = push M₀ N₀} (sn f) rtn H =
    sn (λ { push-step → SN-ext-pmᵛ∷-C (f push-step) (λ ch → rtn (_ ~>⟨ push-step ⟩ ch)) H })
  SN-ext-pmᵛ∷-C {M = app (var i) V} (sn f) rtn H = sn (λ ())
  SN-ext-pmᵛ∷-C {M = app (lam N₀) V} (sn f) rtn H =
    sn (λ { app-lam-step → SN-ext-pmᵛ∷-C (f app-lam-step) (λ ch → rtn (_ ~>⟨ app-lam-step ⟩ ch)) H })
  SN-ext-pmᵛ∷-C {M = app (pm V₀ W₀) V} (sn f) rtn H =
    sn (λ { app-pm-step → SN-ext-pmᵛ∷-C (f app-pm-step) (λ ch → rtn (_ ~>⟨ app-pm-step ⟩ ch)) H })
  SN-ext-pmᵛ∷-C {M = pm V₀ N₀} (sn f) rtn H =
    sn (λ { pm-step → SN-ext-pmᵛ∷-V (f pm-step) (λ ch → rtn (_ ~>⟨ pm-step ⟩ ch)) H })
  SN-ext-pmᵛ∷-C {M = return V} {K₀ = ε} (sn f) rtn H = sn (λ ())
  SN-ext-pmᵛ∷-C {M = return V} {K₀ = N₀ ∷ K₀} (sn f) rtn H =
    sn (λ { return-step → SN-ext-pmᵛ∷-C (f return-step) (λ ch → rtn (_ ~>⟨ return-step ⟩ ch)) H })
  SN-ext-pmᵛ∷-C {M = return V} {K₀ = N₀ pm∷ K₀} (sn f) rtn H = sn (λ ())
  SN-ext-pmᵛ∷-C {M = return V} {K₀ = W₀ pmᵛ∷ K₀} (sn f) rtn H = sn (λ ())

  SN-ext-pmᵛ∷-V : {X Y E : Ty} {V : Γ ⊢ᵛ A} {K₀ : Γ ⊢ᵏ A ⇒ (X `× Y)} {W : (Γ ∙ X ∙ Y) ⊢ᵛ E} {K : Γ ⊢ᵏ E ⇒ C}
               → SN [ V ∥ K₀ ]
               → (∀ {L R} → [ V ∥ K₀ ] ↠ᵏ [ pair L R ∥ ε ] → Redᵛ X L × Redᵛ Y R)
               → (∀ {L R} → Redᵛ X L → Redᵛ Y R → SN [ sub-val (sub-ex (sub-ex sub-id L) R) W ∥ K ])
               → SN [ V ∥ graft K₀ (W pmᵛ∷ K) ]
  SN-ext-pmᵛ∷-V {V = var i} (sn f) rtn H = sn (λ ())
  SN-ext-pmᵛ∷-V {V = lam N₀} (sn f) rtn H = sn (λ ())
  SN-ext-pmᵛ∷-V {V = unit} (sn f) rtn H = sn (λ ())
  SN-ext-pmᵛ∷-V {V = pm V₀ W₀} (sn f) rtn H =
    sn (λ { pm-val-step → SN-ext-pmᵛ∷-V (f pm-val-step) (λ ch → rtn (_ ~>⟨ pm-val-step ⟩ ch)) H })
  SN-ext-pmᵛ∷-V {V = pair L R} {K₀ = ε} (sn f) rtn H =
    sn (λ { pmᵛ-pair-step → H (proj₁ (rtn (_ ◼))) (proj₂ (rtn (_ ◼))) })
  SN-ext-pmᵛ∷-V {V = pair L R} {K₀ = N₀ ∷ K₀} (sn f) rtn H = sn (λ ())
  SN-ext-pmᵛ∷-V {V = pair L R} {K₀ = N₀ pm∷ K₀} (sn f) rtn H =
    sn (λ { pm-pair-step → SN-ext-pmᵛ∷-C (f pm-pair-step) (λ ch → rtn (_ ~>⟨ pm-pair-step ⟩ ch)) H })
  SN-ext-pmᵛ∷-V {V = pair L R} {K₀ = W₀ pmᵛ∷ K₀} (sn f) rtn H =
    sn (λ { pmᵛ-pair-step → SN-ext-pmᵛ∷-V (f pmᵛ-pair-step) (λ ch → rtn (_ ~>⟨ pmᵛ-pair-step ⟩ ch)) H })

mutual
  RTN-ext-pmᵛ∷ᴾ-C : {X Y E X' Y' : Ty} {M : Γ ⊢ᶜ A} {K₀ : Γ ⊢ᵏ A ⇒ (X `× Y)} {W : (Γ ∙ X ∙ Y) ⊢ᵛ E} {K : Γ ⊢ᵏ E ⇒ (X' `× Y')}
                → (∀ {L R} → ⟨ M ∥ K₀ ⟩ ↠ᵏ [ pair L R ∥ ε ] → Redᵛ X L × Redᵛ Y R)
                → (∀ {L R} → Redᵛ X L → Redᵛ Y R → ∀ {L' R'} → [ sub-val (sub-ex (sub-ex sub-id L) R) W ∥ K ] ↠ᵏ [ pair L' R' ∥ ε ] → Redᵛ X' L' × Redᵛ Y' R')
                → {L' : Γ ⊢ᵛ X'} {R' : Γ ⊢ᵛ Y'} → ⟨ M ∥ graft K₀ (W pmᵛ∷ K) ⟩ ↠ᵏ [ pair L' R' ∥ ε ] → Redᵛ X' L' × Redᵛ Y' R'
  RTN-ext-pmᵛ∷ᴾ-C {M = push M₀ N₀} rtn H2 (_ ~>⟨ push-step ⟩ rest) =
    RTN-ext-pmᵛ∷ᴾ-C (λ ch → rtn (_ ~>⟨ push-step ⟩ ch)) H2 rest
  RTN-ext-pmᵛ∷ᴾ-C {M = app (var i) V} rtn H2 (_ ~>⟨ () ⟩ rest)
  RTN-ext-pmᵛ∷ᴾ-C {M = app (lam N₀) V} rtn H2 (_ ~>⟨ app-lam-step ⟩ rest) =
    RTN-ext-pmᵛ∷ᴾ-C (λ ch → rtn (_ ~>⟨ app-lam-step ⟩ ch)) H2 rest
  RTN-ext-pmᵛ∷ᴾ-C {M = app (pm V₀ W₀) V} rtn H2 (_ ~>⟨ app-pm-step ⟩ rest) =
    RTN-ext-pmᵛ∷ᴾ-C (λ ch → rtn (_ ~>⟨ app-pm-step ⟩ ch)) H2 rest
  RTN-ext-pmᵛ∷ᴾ-C {M = pm V₀ N₀} rtn H2 (_ ~>⟨ pm-step ⟩ rest) =
    RTN-ext-pmᵛ∷ᴾ-V (λ ch → rtn (_ ~>⟨ pm-step ⟩ ch)) H2 rest
  RTN-ext-pmᵛ∷ᴾ-C {M = return V} {K₀ = ε} rtn H2 (_ ~>⟨ () ⟩ rest)
  RTN-ext-pmᵛ∷ᴾ-C {M = return V} {K₀ = N₀ ∷ K₀} rtn H2 (_ ~>⟨ return-step ⟩ rest) =
    RTN-ext-pmᵛ∷ᴾ-C (λ ch → rtn (_ ~>⟨ return-step ⟩ ch)) H2 rest
  RTN-ext-pmᵛ∷ᴾ-C {M = return V} {K₀ = N₀ pm∷ K₀} rtn H2 (_ ~>⟨ () ⟩ rest)
  RTN-ext-pmᵛ∷ᴾ-C {M = return V} {K₀ = W₀ pmᵛ∷ K₀} rtn H2 (_ ~>⟨ () ⟩ rest)

  RTN-ext-pmᵛ∷ᴾ-V : {X Y E X' Y' : Ty} {V : Γ ⊢ᵛ A} {K₀ : Γ ⊢ᵏ A ⇒ (X `× Y)} {W : (Γ ∙ X ∙ Y) ⊢ᵛ E} {K : Γ ⊢ᵏ E ⇒ (X' `× Y')}
                → (∀ {L R} → [ V ∥ K₀ ] ↠ᵏ [ pair L R ∥ ε ] → Redᵛ X L × Redᵛ Y R)
                → (∀ {L R} → Redᵛ X L → Redᵛ Y R → ∀ {L' R'} → [ sub-val (sub-ex (sub-ex sub-id L) R) W ∥ K ] ↠ᵏ [ pair L' R' ∥ ε ] → Redᵛ X' L' × Redᵛ Y' R')
                → {L' : Γ ⊢ᵛ X'} {R' : Γ ⊢ᵛ Y'} → [ V ∥ graft K₀ (W pmᵛ∷ K) ] ↠ᵏ [ pair L' R' ∥ ε ] → Redᵛ X' L' × Redᵛ Y' R'
  RTN-ext-pmᵛ∷ᴾ-V {V = var i} rtn H2 (_ ~>⟨ () ⟩ rest)
  RTN-ext-pmᵛ∷ᴾ-V {V = lam N₀} rtn H2 (_ ~>⟨ () ⟩ rest)
  RTN-ext-pmᵛ∷ᴾ-V {V = unit} rtn H2 (_ ~>⟨ () ⟩ rest)
  RTN-ext-pmᵛ∷ᴾ-V {V = pm V₀ W₀} rtn H2 (_ ~>⟨ pm-val-step ⟩ rest) =
    RTN-ext-pmᵛ∷ᴾ-V (λ ch → rtn (_ ~>⟨ pm-val-step ⟩ ch)) H2 rest
  RTN-ext-pmᵛ∷ᴾ-V {V = pair L R} {K₀ = ε} rtn H2 (_ ~>⟨ pmᵛ-pair-step ⟩ rest) =
    H2 (proj₁ (rtn (_ ◼))) (proj₂ (rtn (_ ◼))) rest
  RTN-ext-pmᵛ∷ᴾ-V {V = pair L R} {K₀ = N₀ ∷ K₀} rtn H2 (_ ~>⟨ () ⟩ rest)
  RTN-ext-pmᵛ∷ᴾ-V {V = pair L R} {K₀ = N₀ pm∷ K₀} rtn H2 (_ ~>⟨ pm-pair-step ⟩ rest) =
    RTN-ext-pmᵛ∷ᴾ-C (λ ch → rtn (_ ~>⟨ pm-pair-step ⟩ ch)) H2 rest
  RTN-ext-pmᵛ∷ᴾ-V {V = pair L R} {K₀ = W₀ pmᵛ∷ K₀} rtn H2 (_ ~>⟨ pmᵛ-pair-step ⟩ rest) =
    RTN-ext-pmᵛ∷ᴾ-V (λ ch → rtn (_ ~>⟨ pmᵛ-pair-step ⟩ ch)) H2 rest

exp-pm-comp : {V : Γ ⊢ᵛ X `× Y} {M : (Γ ∙ X ∙ Y) ⊢ᶜ C}
            → Redᵛ (X `× Y) V → (∀ {L R} → Redᵛ X L → Redᵛ Y R → Redᶜ C (sub-comp (sub-ex (sub-ex sub-id L) R) M))
            → Redᶜ C (pm V M)
exp-pm-comp {V = V} {M} redV H =
  sn (λ { pm-step → SN-ext-pm∷-V (Red→SNᵛ _ V redV) (proj₂ redV) (λ redL redR → Red→SNᶜ _ _ (H redL redR)) }) ,
  λ { (_ ~>⟨ pm-step ⟩ rest) → RTN-ext-pm∷-V (proj₂ redV) (λ redL redR → Red→RTNᶜ _ _ (H redL redR)) rest }

exp-app-lam : {N : (Γ ∙ A) ⊢ᶜ B} {V : Γ ⊢ᵛ A}
            → Redᶜ B (sub-comp (sub-ex sub-id V) N) → Redᶜ B (app (lam N) V)
exp-app-lam {N = N} {V} (snN , rtnN) =
  sn (λ { app-lam-step → snN }) ,
  λ { (_ ~>⟨ app-lam-step ⟩ rest) → rtnN rest }

exp-app-pm : {V : Γ ⊢ᵛ X `× Y} {W : (Γ ∙ X ∙ Y) ⊢ᵛ A `⇒ B} {N : Γ ⊢ᵛ A}
           → Redᶜ B (pm V (app W (wk-val (wk-wk (wk-wk wk-id)) N))) → Redᶜ B (app (pm V W) N)
exp-app-pm {V = V} {W} {N} (snM , rtnM) =
  sn (λ { app-pm-step → snM }) ,
  λ { (_ ~>⟨ app-pm-step ⟩ rest) → rtnM rest }

Red-varᵛ : (A : Ty) (i : Γ ∋ A) → Redᵛ A (var i)
Red-varᵛ `Unit    i           = sn (λ ())
Red-varᵛ (A `× B) i           = sn (λ ()) , λ { (_ ~>⟨ () ⟩ _) }
Red-varᵛ (A `⇒ B) i           = sn (λ ()) , λ π {W} rw → sn (λ ()) , λ { (_ ~>⟨ () ⟩ _) }

--------------------------------------------------------------------------
-- weakening preserves reducibility

wk-reflect* : {Γ' : Ctx} (π : Γ' ⊇ Γ) {σ : Cfg Γ B} {τ' : Cfg Γ' B}
            → wk-cfg π σ ↠ᵏ τ' → Σ[ σ' ∈ Cfg Γ B ] (σ ↠ᵏ σ') × (τ' ≡ wk-cfg π σ')
wk-reflect* π (_ ◼) = _ , (_ ◼) , refl
wk-reflect* π (_ ~>⟨ step ⟩ rest) with wk-reflect π step
wk-reflect* π (_ ~>⟨ step ⟩ rest) | (σ₁ , σ-step , refl) =
  let (σ' , σ₁-steps , eq₂) = wk-reflect* π rest
  in σ' , _ ~>⟨ σ-step ⟩ σ₁-steps , eq₂

pair-cfg-inv : {Γ' : Ctx} {A B : Ty} (π : Γ' ⊇ Γ) {σ' : Cfg Γ (A `× B)} {L' : Γ' ⊢ᵛ A} {R' : Γ' ⊢ᵛ B}
             → [ pair L' R' ∥ ε ] ≡ wk-cfg π σ'
             → Σ[ L ∈ Γ ⊢ᵛ A ] Σ[ R ∈ Γ ⊢ᵛ B ] (σ' ≡ [ pair L R ∥ ε ]) × (wk-val π L ≡ L') × (wk-val π R ≡ R')
pair-cfg-inv π {σ' = ⟨ M ∥ K ⟩}               ()
pair-cfg-inv π {σ' = [ var i ∥ K ]}           ()
pair-cfg-inv π {σ' = [ lam N ∥ K ]}           ()
pair-cfg-inv π {σ' = [ pair L R ∥ ε ]}        refl = L , R , refl , refl , refl
pair-cfg-inv π {σ' = [ pair L R ∥ N ∷ K ]}    ()
pair-cfg-inv π {σ' = [ pair L R ∥ N pm∷ K ]}  ()
pair-cfg-inv π {σ' = [ pair L R ∥ W pmᵛ∷ K ]} ()
pair-cfg-inv π {σ' = [ pm V W ∥ K ]}          ()
pair-cfg-inv π {σ' = [ unit ∥ K ]}            ()

Red-wk : (A : Ty) {Γ' : Ctx} (π : Γ' ⊇ Γ) {V : Γ ⊢ᵛ A} → Redᵛ A V → Redᵛ A (wk-val π V)
Red-wk `Unit    π r          = SN-wk π r
Red-wk (A `× B) π {V} (snV , f) = SN-wk π snV , g
  where
  g : ∀ {L' R'} → [ wk-val π V ∥ ε ] ↠ᵏ [ pair L' R' ∥ ε ] → Redᵛ A L' × Redᵛ B R'
  g p =
    let (σ' , σ-steps , eq)          = wk-reflect* π p
        (L , R , σ'-eq , eqL , eqR)  = pair-cfg-inv π eq
        (redL , redR)                = f (Eq.subst (λ x → [ V ∥ ε ] ↠ᵏ x) σ'-eq σ-steps)
    in Eq.subst (Redᵛ A) eqL (Red-wk A π redL) , Eq.subst (Redᵛ B) eqR (Red-wk B π redR)
Red-wk (A `⇒ B) π {V} (snV , f) = SN-wk π snV , harrow
  where
  harrow : ∀ {Γ''} (ρ : Γ'' ⊇ _) {W : Γ'' ⊢ᵛ A} → Redᵛ A W → Redᶜ B (app (wk-val ρ (wk-val π V)) W)
  harrow ρ {W = W} redW =
    Eq.subst (Redᶜ B) (sym (cong (λ x → app x W) (wk-val-trans V ρ π))) (f (wk-trans ρ π) redW)

sub-val-ins2-cancel : (L : Γ ⊢ᵛ X) (R : Γ ⊢ᵛ Y) (N : Γ ⊢ᵛ A)
                     → sub-val (sub-ex (sub-ex sub-id L) R) (wk-val (wk-wk (wk-wk wk-id)) N) ≡ N
sub-val-ins2-cancel L R N = begin
  sub-val (sub-ex (sub-ex sub-id L) R) (wk-val (wk-wk (wk-wk wk-id)) N)  ≡⟨ sub-val-wk-pre (sub-ex (sub-ex sub-id L) R) (wk-wk (wk-wk wk-id)) N ⟩
  sub-val (sub-pre sub-id wk-id) N                                      ≡⟨ cong (λ θ → sub-val θ N) (sub-pre-wk-id sub-id) ⟩
  sub-val sub-id N                                                      ≡⟨ sub-val-id N ⟩
  N ∎

exp-pm-val : (C : Ty) {V : Γ ⊢ᵛ X `× Y} {W : (Γ ∙ X ∙ Y) ⊢ᵛ C}
           → Redᵛ (X `× Y) V
           → (∀ {Γ'} (π : Γ' ⊇ Γ) {L R} → Redᵛ X L → Redᵛ Y R → Redᵛ C (sub-val (sub-ex (sub-ex sub-id L) R) (wk-val (wk-cong (wk-cong π)) W)))
           → Redᵛ C (pm V W)
exp-pm-val {Γ} {X} {Y} `Unit {V} {W} redV H =
  sn (λ { pm-val-step →
    SN-ext-pmᵛ∷-V (Red→SNᵛ _ V redV) (proj₂ redV)
      (λ redL redR → Red→SNᵛ `Unit _ (H0 redL redR)) })
  where
  H0 : ∀ {L R} → Redᵛ X L → Redᵛ Y R → Redᵛ `Unit (sub-val (sub-ex (sub-ex sub-id L) R) W)
  H0 {L} {R} redL redR = Eq.subst (Redᵛ `Unit) (cong (sub-val (sub-ex (sub-ex sub-id L) R)) (wk-val-id W)) (H wk-id redL redR)
exp-pm-val {Γ} {X} {Y} (C1 `× C2) {V} {W} redV H =
  sn (λ { pm-val-step →
    SN-ext-pmᵛ∷-V (Red→SNᵛ _ V redV) (proj₂ redV)
      (λ redL redR → Red→SNᵛ (C1 `× C2) _ (H0 redL redR)) }) ,
  λ { (_ ~>⟨ pm-val-step ⟩ rest) → RTN-ext-pmᵛ∷ᴾ-V (proj₂ redV) (λ redL redR → proj₂ (H0 redL redR)) rest }
  where
  H0 : ∀ {L R} → Redᵛ X L → Redᵛ Y R → Redᵛ (C1 `× C2) (sub-val (sub-ex (sub-ex sub-id L) R) W)
  H0 {L} {R} redL redR = Eq.subst (Redᵛ (C1 `× C2)) (cong (sub-val (sub-ex (sub-ex sub-id L) R)) (wk-val-id W)) (H wk-id redL redR)
exp-pm-val {Γ} {X} {Y} (C1 `⇒ C2) {V} {W} redV H =
  sn (λ { pm-val-step →
    SN-ext-pmᵛ∷-V (Red→SNᵛ _ V redV) (proj₂ redV)
      (λ redL redR → Red→SNᵛ (C1 `⇒ C2) _ (H0 redL redR)) }) ,
  harrow
  where
  H0 : ∀ {L R} → Redᵛ X L → Redᵛ Y R → Redᵛ (C1 `⇒ C2) (sub-val (sub-ex (sub-ex sub-id L) R) W)
  H0 {L} {R} redL redR = Eq.subst (Redᵛ (C1 `⇒ C2)) (cong (sub-val (sub-ex (sub-ex sub-id L) R)) (wk-val-id W)) (H wk-id redL redR)

  harrow : ∀ {Γ''} (ρ : Γ'' ⊇ Γ) {N : Γ'' ⊢ᵛ C1} → Redᵛ C1 N → Redᶜ C2 (app (wk-val ρ (pm V W)) N)
  harrow ρ {N} redN =
    exp-app-pm
      (exp-pm-comp (Red-wk (X `× Y) ρ redV)
        (λ {L} {R} redL redR →
          let redW1 = H ρ redL redR
              redN' = Eq.subst (Redᵛ C1) (sym (sub-val-ins2-cancel L R N)) redN
          in Eq.subst (Redᶜ C2)
                      (cong (λ w → app w (sub-val (sub-ex (sub-ex sub-id L) R) (wk-val (wk-wk (wk-wk wk-id)) N)))
                            (wk-val-id (sub-val (sub-ex (sub-ex sub-id L) R) (wk-val (wk-cong (wk-cong ρ)) W))))
                      (proj₂ redW1 wk-id redN')))

record RedSub (θ : Γ ⊢ Δ) : Set where
  field red : (i : Δ ∋ A) → Redᵛ A (sub-mem θ i)
open RedSub

RedSub-wk : {Γ' : Ctx} (ρ : Γ' ⊇ Γ) {θ : Γ ⊢ Δ} → RedSub θ → RedSub (sub-wk ρ θ)
RedSub-wk ρ {θ} rθ = record
  { red = λ i → Eq.subst (Redᵛ _) (sym (sub-mem-wk ρ θ i)) (Red-wk _ ρ (rθ .red i)) }

RedSub-ext : {θ : Γ ⊢ Δ} {V : Γ ⊢ᵛ A} → RedSub θ → Redᵛ A V → RedSub (sub-ex θ V)
RedSub-ext rθ rv = record { red = λ { h → rv ; (t i) → rθ .red i } }

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
Fundamental-val θ rθ (pair V1 V2) =
  sn (λ ()) , λ { (_ ◼) → Fundamental-val θ rθ V1 , Fundamental-val θ rθ V2 ; (_ ~>⟨ () ⟩ _) }
Fundamental-val θ rθ (pm {A = X} {B = Y} V W) =
  exp-pm-val _ (Fundamental-val θ rθ V)
    (λ π {L} {R} redL redR →
      Eq.subst (Redᵛ _)
        (begin
           sub-val (sub-ex (sub-ex (sub-wk π θ) L) R) W
         ≡˘⟨ fund-pm-eqᵛ (sub-wk π θ) L R W ⟩
           sub-val (sub-ex (sub-ex sub-id L) R)
                   (sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-wk π θ)) (var (t h))) (var h)) W)
         ≡˘⟨ cong (sub-val (sub-ex (sub-ex sub-id L) R))
                  (begin
                     wk-val (wk-cong (wk-cong π))
                            (sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) W)
                   ≡⟨ wk-sub-val (wk-cong (wk-cong π)) (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) W ⟩
                     sub-val (sub-wk (wk-cong (wk-cong π)) (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h))) W
                   ≡⟨ cong (λ w → sub-val w W)
                           (cong (λ w → sub-ex w (var h))
                                 (cong (λ w → sub-ex w (var (t h))) (wk-cong2-sub-wk-lemma π θ))) ⟩
                     sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-wk π θ)) (var (t h))) (var h)) W ∎) ⟩
           sub-val (sub-ex (sub-ex sub-id L) R)
                   (wk-val (wk-cong (wk-cong π))
                           (sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) W)) ∎)
        (Fundamental-val (sub-ex (sub-ex (sub-wk π θ) L) R) (RedSub-ext (RedSub-ext (RedSub-wk π rθ) redL) redR) W))

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
              (λ {L} {R} redL redR →
                Eq.subst (Redᶜ _) (sym (fund-pm-eqᶜ θ L R M))
                         (Fundamental-comp (sub-ex (sub-ex θ L) R) (RedSub-ext (RedSub-ext rθ redL) redR) M))

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
step? ⟨ push M N ∥ K ⟩            = next push-step
step? ⟨ return V ∥ ε ⟩            = done (λ ())
step? ⟨ return V ∥ N ∷ K ⟩        = next return-step
step? ⟨ return V ∥ N pm∷ K ⟩      = done (λ ())
step? ⟨ return V ∥ W pmᵛ∷ K ⟩     = done (λ ())
step? ⟨ app (var i) V ∥ K ⟩       = done (λ ())
step? ⟨ app (lam N) V ∥ K ⟩       = next app-lam-step
step? ⟨ app (pm V W) N ∥ K ⟩      = next app-pm-step
step? ⟨ pm V N ∥ K ⟩              = next pm-step
step? [ var i ∥ K ]               = done (λ ())
step? [ lam N ∥ K ]               = done (λ ())
step? [ unit ∥ K ]                = done (λ ())
step? [ pm V W ∥ K ]              = next pm-val-step
step? [ pair L R ∥ ε ]            = done (λ ())
step? [ pair L R ∥ N ∷ K ]        = done (λ ())
step? [ pair L R ∥ N pm∷ K ]      = next pm-pair-step
step? [ pair L R ∥ W pmᵛ∷ K ]     = next pmᵛ-pair-step

eval-acc : {σ : Cfg Γ B} → SN σ → Σ[ σ' ∈ Cfg Γ B ] (σ ↠ᵏ σ') × Normal σ'
eval-acc {σ = σ} (sn f) with step? σ
... | done normal    = σ , σ ◼ , normal
... | next {σ'} step with eval-acc (f step)
...   | (σ'' , chain , normal) = σ'' , σ ~>⟨ step ⟩ chain , normal

eval : (M : Γ ⊢ᶜ A) → Σ[ σ' ∈ Cfg Γ A ] (⟨ M ∥ ε ⟩ ↠ᵏ σ') × Normal σ'
eval M = eval-acc (SN-theorem M)
