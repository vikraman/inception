{-# OPTIONS --no-postfix-projections #-}

module Inception.Lam.CK where

open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂)
open Eq.≡-Reasoning

open import Inception.Lam.Syntax
open import Inception.Prelude
open Inception.Prelude.RTC

--------------------------------------------------------------------------
-- stacks, configurations, transitions

infixr 20 _∷_

syntax Stk Γ X Y = Γ ⊢ᵏ X ⇒ Y

data Stk (Γ : Ctx) : Ty → Ty → Set where

  ε      : Γ ⊢ᵏ X ⇒ X

  _∷_    : (N : (Γ ∙ X) ⊢ᶜ Y) → (K : Γ ⊢ᵏ Y ⇒ Z)
         ------------------------------------------
         → Γ ⊢ᵏ X ⇒ Z

infix 5 ⟨_∥_⟩

data Cfg (Γ : Ctx) (X : Ty) : Set where

  ⟨_∥_⟩ : (M : Γ ⊢ᶜ Y) → (K : Γ ⊢ᵏ Y ⇒ X)
        -------------------------------------
        → Cfg Γ X

infix 5 _→ᵏ_

data _→ᵏ_ {Γ} : {X : Ty} → Cfg Γ X → Cfg Γ X → Set where

  push-step      : {M : Γ ⊢ᶜ Y} {N : (Γ ∙ Y) ⊢ᶜ X} {K : Γ ⊢ᵏ X ⇒ Z}
                 → ⟨ push M N ∥ K ⟩ →ᵏ ⟨ M ∥ N ∷ K ⟩

  return-step    : {V : Γ ⊢ᵛ Y} {N : (Γ ∙ Y) ⊢ᶜ X} {K : Γ ⊢ᵏ X ⇒ Z}
                 → ⟨ return V ∥ N ∷ K ⟩ →ᵏ ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩

  app-lam-step   : {N : (Γ ∙ Y) ⊢ᶜ X} {V : Γ ⊢ᵛ Y} {K : Γ ⊢ᵏ X ⇒ Z}
                 → ⟨ app (lam N) V ∥ K ⟩ →ᵏ ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩

--------------------------------------------------------------------------
-- accessibility

data SN {Γ X} (σ : Cfg Γ X) : Set where
  sn : (∀ {σ₁} → σ →ᵏ σ₁ → SN σ₁) → SN σ

infix 5 _↠ᵏ_

_↠ᵏ_ : {Γ : Ctx} {X : Ty} → Cfg Γ X → Cfg Γ X → Set
_↠ᵏ_ {Γ} {X} = _~>*_ (_→ᵏ_ {Γ = Γ} {X = X})

--------------------------------------------------------------------------
-- weakening a configuration

wk-stk : {Γ₁ : Ctx} → Γ₁ ⊇ Γ → Γ ⊢ᵏ X ⇒ Y → Γ₁ ⊢ᵏ X ⇒ Y
wk-stk π ε       = ε
wk-stk π (N ∷ K) = wk-comp (wk-cong π) N ∷ wk-stk π K

wk-cfg : {Γ₁ : Ctx} → Γ₁ ⊇ Γ → Cfg Γ X → Cfg Γ₁ X
wk-cfg π ⟨ M ∥ K ⟩ = ⟨ wk-comp π M ∥ wk-stk π K ⟩

--------------------------------------------------------------------------
-- reducibility candidates

graft : Γ ⊢ᵏ X ⇒ Y → Γ ⊢ᵏ Y ⇒ Z → Γ ⊢ᵏ X ⇒ Z
graft ε        K = K
graft (N ∷ L) K  = N ∷ graft L K

Redᵛ : (X : Ty) → Γ ⊢ᵛ X → Set
Redᶜ : (X : Ty) → Γ ⊢ᶜ X → Set

Redᵛ `𝟙        V    = ⊤
Redᵛ {Γ} (X `⇒ Y) V = ∀ {Γ₁} (π : Γ₁ ⊇ Γ) {W : Γ₁ ⊢ᵛ X} → Redᵛ X W → Redᶜ Y (app (wk-val π V) W)

Redᶜ X M = SN ⟨ M ∥ ε ⟩ × (∀ {V} → ⟨ M ∥ ε ⟩ ↠ᵏ ⟨ return V ∥ ε ⟩ → Redᵛ X V)

Red→SNᶜ : (X : Ty) (M : Γ ⊢ᶜ X) → Redᶜ X M → SN ⟨ M ∥ ε ⟩
Red→SNᶜ X M (snM , ret) = snM

Red→RTNᶜ : (X : Ty) (M : Γ ⊢ᶜ X) → Redᶜ X M → (∀ {V} → ⟨ M ∥ ε ⟩ ↠ᵏ ⟨ return V ∥ ε ⟩ → Redᵛ X V)
Red→RTNᶜ X M (snM , ret) = ret

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
SN-ext∷-C {M = return V} {L = ε} (sn f) rtn H =
  sn (λ { return-step → H (rtn (_ ◼)) })
SN-ext∷-C {M = return V} {L = N ∷ L} (sn f) rtn H =
  sn (λ { return-step → SN-ext∷-C (f return-step) (λ ch → rtn (_ ~>⟨ return-step ⟩ ch)) H })

RTN-ext∷-C : {X : Ty} {M : Γ ⊢ᶜ Y} {L : Γ ⊢ᵏ Y ⇒ Z} {N : (Γ ∙ Z) ⊢ᶜ X} {K : Γ ⊢ᵏ X ⇒ X₁}
           → (∀ {V} → ⟨ M ∥ L ⟩ ↠ᵏ ⟨ return V ∥ ε ⟩ → Redᵛ Z V)
           → (∀ {V} → Redᵛ Z V → ∀ {W} → ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩ ↠ᵏ ⟨ return W ∥ ε ⟩ → Redᵛ X₁ W)
           → {W : Γ ⊢ᵛ X₁} → ⟨ M ∥ graft L (N ∷ K) ⟩ ↠ᵏ ⟨ return W ∥ ε ⟩ → Redᵛ X₁ W
RTN-ext∷-C {M = push M N} rtn H (_ ~>⟨ push-step ⟩ rest) =
  RTN-ext∷-C (λ ch → rtn (_ ~>⟨ push-step ⟩ ch)) H rest
RTN-ext∷-C {M = app (var i) V} rtn H (_ ~>⟨ () ⟩ rest)
RTN-ext∷-C {M = app (lam N) V} rtn H (_ ~>⟨ app-lam-step ⟩ rest) =
  RTN-ext∷-C (λ ch → rtn (_ ~>⟨ app-lam-step ⟩ ch)) H rest
RTN-ext∷-C {M = return V} {L = ε} rtn H (_ ~>⟨ return-step ⟩ rest) = H (rtn (_ ◼)) rest
RTN-ext∷-C {M = return V} {L = N ∷ L} rtn H (_ ~>⟨ return-step ⟩ rest) =
  RTN-ext∷-C (λ ch → rtn (_ ~>⟨ return-step ⟩ ch)) H rest

exp-push : {M : Γ ⊢ᶜ X} {N : (Γ ∙ X) ⊢ᶜ Y}
         → Redᶜ X M → (∀ {V : Γ ⊢ᵛ X} → Redᵛ X V → Redᶜ Y (sub-comp (sub-ex sub-id V) N))
         → Redᶜ Y (push M N)
exp-push {X = X} {Y = Y} {M = M} {N} rM H =
  sn (λ { push-step → SN-ext∷-C (Red→SNᶜ X M rM) (Red→RTNᶜ X M rM) (λ {V} rv → Red→SNᶜ Y (sub-comp (sub-ex sub-id V) N) (H rv)) }) ,
  λ { (_ ~>⟨ push-step ⟩ rest) → RTN-ext∷-C (Red→RTNᶜ X M rM) (λ {V} rv → Red→RTNᶜ Y (sub-comp (sub-ex sub-id V) N) (H rv)) rest }

exp-app-lam : {N : (Γ ∙ X) ⊢ᶜ Y} {V : Γ ⊢ᵛ X}
            → Redᶜ Y (sub-comp (sub-ex sub-id V) N) → Redᶜ Y (app (lam N) V)
exp-app-lam {N = N} {V} (snN , rtnN) =
  sn (λ { app-lam-step → snN }) ,
  λ { (_ ~>⟨ app-lam-step ⟩ rest) → rtnN rest }

Red-varᵛ : (X : Ty) (i : Γ ∋ X) → Redᵛ X (var i)
Red-varᵛ `𝟙    i    = tt
Red-varᵛ (X `⇒ Y) i = λ π {W} rw → sn (λ ()) , λ { (_ ~>⟨ () ⟩ s) }

--------------------------------------------------------------------------
-- weakening/substitution preserves reducibility

Red-wk : (X : Ty) {Γ₁ : Ctx} (π : Γ₁ ⊇ Γ) {V : Γ ⊢ᵛ X} → Redᵛ X V → Redᵛ X (wk-val π V)
Red-wk `𝟙    π r = tt
Red-wk (X `⇒ Y) π {V} f δ {W} redW =
  Eq.subst (Redᶜ Y)
           (begin
             app (wk-val (wk-trans δ π) V) W
           ≡˘⟨ cong (λ x → app x W) (wk-val-trans V δ π) ⟩
             app (wk-val δ (wk-val π V)) W
           ∎)
           (f (wk-trans δ π) redW)

record RedSub (θ : Γ ⊢ Δ) : Set where
  field red : (i : Δ ∋ X) → Redᵛ X (sub-mem θ i)
open RedSub

RedSub-wk : {Γ₁ : Ctx} (ρ : Γ₁ ⊇ Γ) {θ : Γ ⊢ Δ} → RedSub θ → RedSub (sub-wk ρ θ)
red (RedSub-wk ρ {θ} rθ) {X = X} i =
  Eq.subst (Redᵛ X)
           (begin
             wk-val ρ (sub-mem θ i)
             ≡˘⟨ sub-mem-wk ρ θ i ⟩
             sub-mem (sub-wk ρ θ) i
             ∎)
           (Red-wk X ρ (rθ .red i))

RedSub-ext : {θ : Γ ⊢ Δ} {V : Γ ⊢ᵛ X} → RedSub θ → Redᵛ X V → RedSub (sub-ex θ V)
RedSub-ext rθ rv = record { red = λ { here → rv ; (there i) → rθ .red i } }

RedSub-id : RedSub (sub-id {Γ})
red (RedSub-id {Γ}) {X = X} i =
  Eq.subst (Redᵛ X)
           (begin
             var i
           ≡˘⟨ sub-mem-id i ⟩
             sub-mem sub-id i
           ∎)
           (Red-varᵛ X i)

--------------------------------------------------------------------------
-- Fundamental Lemma

Fundamental-val : (θ : Γ ⊢ Δ) → RedSub θ → (V : Δ ⊢ᵛ X) → Redᵛ X (sub-val θ V)
Fundamental-comp : (θ : Γ ⊢ Δ) → RedSub θ → (M : Δ ⊢ᶜ X) → Redᶜ X (sub-comp θ M)

Fundamental-val θ rθ (var i) = rθ .red i
Fundamental-val θ rθ unit    = tt
Fundamental-val θ rθ (lam M) π {W} rw =
  exp-app-lam
    (Eq.subst (Redᶜ _)
              (begin
                sub-comp (sub-ex (sub-wk π θ) W) M
              ≡˘⟨ fund-lam-eq θ π W M ⟩
                sub-comp (sub-ex sub-id W) (wk-comp (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M))
              ∎)
              (Fundamental-comp (sub-ex (sub-wk π θ) W) (RedSub-ext (RedSub-wk π rθ) rw) M))

Fundamental-comp θ rθ (return V) =
  sn (λ ()) , λ { (_ ◼) → Fundamental-val θ rθ V ; (_ ~>⟨ () ⟩ _) }
Fundamental-comp θ rθ (app V W) =
  Eq.subst (λ U → Redᶜ _ (app U (sub-val θ W))) (wk-val-id (sub-val θ V))
           (Fundamental-val θ rθ V wk-id (Fundamental-val θ rθ W))
Fundamental-comp θ rθ (push M N) =
  exp-push (Fundamental-comp θ rθ M)
           (λ {V} rv →
             Eq.subst (Redᶜ _)
                      (begin
                        sub-comp (sub-ex θ V) N
                      ≡˘⟨ fund-push-eq θ V N ⟩
                        sub-comp (sub-ex sub-id V) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
                      ∎)
                      (Fundamental-comp (sub-ex θ V) (RedSub-ext rθ rv) N))

SN-theorem : (M : Γ ⊢ᶜ X) → SN ⟨ M ∥ ε ⟩
SN-theorem {Γ} {X} M =
  Eq.subst (λ N → SN ⟨ N ∥ ε ⟩) (sub-comp-id M)
           (Red→SNᶜ X (sub-comp sub-id M) (Fundamental-comp sub-id RedSub-id M))

--------------------------------------------------------------------------
-- eval

Normal : Cfg Γ X → Set
Normal σ = ∀ {σ₁} → σ →ᵏ σ₁ → ⊥

data Step? (σ : Cfg Γ X) : Set where
  done : Normal σ → Step? σ
  next : {σ₁ : Cfg Γ X} → σ →ᵏ σ₁ → Step? σ

step? : (σ : Cfg Γ X) → Step? σ
step? ⟨ push M N ∥ K ⟩      = next push-step
step? ⟨ return V ∥ ε ⟩      = done (λ ())
step? ⟨ return V ∥ N ∷ K ⟩  = next return-step
step? ⟨ app (var i) V ∥ K ⟩ = done (λ ())
step? ⟨ app (lam N) V ∥ K ⟩ = next app-lam-step

eval-acc : {σ : Cfg Γ X} → SN σ → Σ[ σ₁ ∈ Cfg Γ X ] (σ ↠ᵏ σ₁) × Normal σ₁
eval-acc {σ = σ} (sn f) with step? σ
... | done normal    = σ , σ ◼ , normal
... | next {σ₁} step with eval-acc (f step)
...   | (σ₂ , chain , normal) = σ₂ , σ ~>⟨ step ⟩ chain , normal

eval : (M : Γ ⊢ᶜ X) → Σ[ σ ∈ Cfg Γ X ] (⟨ M ∥ ε ⟩ ↠ᵏ σ) × Normal σ
eval M = eval-acc (SN-theorem M)
