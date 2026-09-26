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

syntax Stk Γ A B = Γ ⊢ᵏ A ⇒ B

data Stk (Γ : Ctx) : Ty → Ty → Set where

  ε      : Γ ⊢ᵏ A ⇒ A

  _∷_    : (N : (Γ ∙ A) ⊢ᶜ B) → (K : Γ ⊢ᵏ B ⇒ C)
         ------------------------------------------
         → Γ ⊢ᵏ A ⇒ C

infix 5 ⟨_∥_⟩

data Cfg (Γ : Ctx) (B : Ty) : Set where

  ⟨_∥_⟩ : (M : Γ ⊢ᶜ A) → (K : Γ ⊢ᵏ A ⇒ B)
        -------------------------------------
        → Cfg Γ B

infix 5 _→ᵏ_

data _→ᵏ_ {Γ} : {B : Ty} → Cfg Γ B → Cfg Γ B → Set where

  push-step      : {M : Γ ⊢ᶜ A} {N : (Γ ∙ A) ⊢ᶜ B} {K : Γ ⊢ᵏ B ⇒ C}
                 → ⟨ push M N ∥ K ⟩ →ᵏ ⟨ M ∥ N ∷ K ⟩

  return-step    : {V : Γ ⊢ᵛ A} {N : (Γ ∙ A) ⊢ᶜ B} {K : Γ ⊢ᵏ B ⇒ C}
                 → ⟨ return V ∥ N ∷ K ⟩ →ᵏ ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩

  app-lam-step   : {N : (Γ ∙ A) ⊢ᶜ B} {V : Γ ⊢ᵛ A} {K : Γ ⊢ᵏ B ⇒ C}
                 → ⟨ app (lam N) V ∥ K ⟩ →ᵏ ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩

--------------------------------------------------------------------------
-- accessibility

data SN {Γ B} (σ : Cfg Γ B) : Set where
  sn : (∀ {σ₁} → σ →ᵏ σ₁ → SN σ₁) → SN σ

infix 5 _↠ᵏ_

_↠ᵏ_ : {Γ : Ctx} {B : Ty} → Cfg Γ B → Cfg Γ B → Set
_↠ᵏ_ {Γ} {B} = _~>*_ (_→ᵏ_ {Γ = Γ} {B = B})

--------------------------------------------------------------------------
-- weakening a configuration

wk-stk : {Γ₁ : Ctx} → Γ₁ ⊇ Γ → Γ ⊢ᵏ A ⇒ B → Γ₁ ⊢ᵏ A ⇒ B
wk-stk π ε       = ε
wk-stk π (N ∷ K) = wk-comp (wk-cong π) N ∷ wk-stk π K

wk-cfg : {Γ₁ : Ctx} → Γ₁ ⊇ Γ → Cfg Γ B → Cfg Γ₁ B
wk-cfg π ⟨ M ∥ K ⟩ = ⟨ wk-comp π M ∥ wk-stk π K ⟩

--------------------------------------------------------------------------
-- reducibility candidates

graft : Γ ⊢ᵏ A ⇒ D → Γ ⊢ᵏ D ⇒ C → Γ ⊢ᵏ A ⇒ C
graft ε        K = K
graft (N ∷ L) K  = N ∷ graft L K

Redᵛ : (A : Ty) → Γ ⊢ᵛ A → Set
Redᶜ : (A : Ty) → Γ ⊢ᶜ A → Set

Redᵛ `Unit        V = ⊤
Redᵛ {Γ} (A `⇒ B) V = ∀ {Γ₁} (π : Γ₁ ⊇ Γ) {W : Γ₁ ⊢ᵛ A} → Redᵛ A W → Redᶜ B (app (wk-val π V) W)

Redᶜ A M = SN ⟨ M ∥ ε ⟩ × (∀ {V} → ⟨ M ∥ ε ⟩ ↠ᵏ ⟨ return V ∥ ε ⟩ → Redᵛ A V)

Red→SNᶜ : (A : Ty) (M : Γ ⊢ᶜ A) → Redᶜ A M → SN ⟨ M ∥ ε ⟩
Red→SNᶜ A M (snM , ret) = snM

Red→RTNᶜ : (A : Ty) (M : Γ ⊢ᶜ A) → Redᶜ A M → (∀ {V} → ⟨ M ∥ ε ⟩ ↠ᵏ ⟨ return V ∥ ε ⟩ → Redᵛ A V)
Red→RTNᶜ A M (snM , ret) = ret

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
SN-ext∷-C {M = return V} {L = ε} (sn f) rtn H =
  sn (λ { return-step → H (rtn (_ ◼)) })
SN-ext∷-C {M = return V} {L = N ∷ L} (sn f) rtn H =
  sn (λ { return-step → SN-ext∷-C (f return-step) (λ ch → rtn (_ ~>⟨ return-step ⟩ ch)) H })

RTN-ext∷-C : {E : Ty} {M : Γ ⊢ᶜ A} {L : Γ ⊢ᵏ A ⇒ D} {N : (Γ ∙ D) ⊢ᶜ E} {K : Γ ⊢ᵏ E ⇒ C}
           → (∀ {V} → ⟨ M ∥ L ⟩ ↠ᵏ ⟨ return V ∥ ε ⟩ → Redᵛ D V)
           → (∀ {V} → Redᵛ D V → ∀ {W} → ⟨ sub-comp (sub-ex sub-id V) N ∥ K ⟩ ↠ᵏ ⟨ return W ∥ ε ⟩ → Redᵛ C W)
           → {W : Γ ⊢ᵛ C} → ⟨ M ∥ graft L (N ∷ K) ⟩ ↠ᵏ ⟨ return W ∥ ε ⟩ → Redᵛ C W
RTN-ext∷-C {M = push M N} rtn H (_ ~>⟨ push-step ⟩ rest) =
  RTN-ext∷-C (λ ch → rtn (_ ~>⟨ push-step ⟩ ch)) H rest
RTN-ext∷-C {M = app (var i) V} rtn H (_ ~>⟨ () ⟩ rest)
RTN-ext∷-C {M = app (lam N) V} rtn H (_ ~>⟨ app-lam-step ⟩ rest) =
  RTN-ext∷-C (λ ch → rtn (_ ~>⟨ app-lam-step ⟩ ch)) H rest
RTN-ext∷-C {M = return V} {L = ε} rtn H (_ ~>⟨ return-step ⟩ rest) = H (rtn (_ ◼)) rest
RTN-ext∷-C {M = return V} {L = N ∷ L} rtn H (_ ~>⟨ return-step ⟩ rest) =
  RTN-ext∷-C (λ ch → rtn (_ ~>⟨ return-step ⟩ ch)) H rest

exp-push : {M : Γ ⊢ᶜ A} {N : (Γ ∙ A) ⊢ᶜ B}
         → Redᶜ A M → (∀ {V : Γ ⊢ᵛ A} → Redᵛ A V → Redᶜ B (sub-comp (sub-ex sub-id V) N))
         → Redᶜ B (push M N)
exp-push {A = A} {B = B} {M = M} {N} rM H =
  sn (λ { push-step → SN-ext∷-C (Red→SNᶜ A M rM) (Red→RTNᶜ A M rM) (λ {V} rv → Red→SNᶜ B (sub-comp (sub-ex sub-id V) N) (H rv)) }) ,
  λ { (_ ~>⟨ push-step ⟩ rest) → RTN-ext∷-C (Red→RTNᶜ A M rM) (λ {V} rv → Red→RTNᶜ B (sub-comp (sub-ex sub-id V) N) (H rv)) rest }

exp-app-lam : {N : (Γ ∙ A) ⊢ᶜ B} {V : Γ ⊢ᵛ A}
            → Redᶜ B (sub-comp (sub-ex sub-id V) N) → Redᶜ B (app (lam N) V)
exp-app-lam {N = N} {V} (snN , rtnN) =
  sn (λ { app-lam-step → snN }) ,
  λ { (_ ~>⟨ app-lam-step ⟩ rest) → rtnN rest }

Red-varᵛ : (A : Ty) (i : Γ ∋ A) → Redᵛ A (var i)
Red-varᵛ `Unit    i = tt
Red-varᵛ (A `⇒ B) i = λ π {W} rw → sn (λ ()) , λ { (_ ~>⟨ () ⟩ s) }

--------------------------------------------------------------------------
-- weakening/substitution preserves reducibility

Red-wk : (A : Ty) {Γ₁ : Ctx} (π : Γ₁ ⊇ Γ) {V : Γ ⊢ᵛ A} → Redᵛ A V → Redᵛ A (wk-val π V)
Red-wk `Unit    π r = tt
Red-wk (A `⇒ B) π {V} f δ {W} redW =
  Eq.subst (Redᶜ B)
           (begin
             app (wk-val (wk-trans δ π) V) W
           ≡˘⟨ cong (λ x → app x W) (wk-val-trans V δ π) ⟩
             app (wk-val δ (wk-val π V)) W
           ∎)
           (f (wk-trans δ π) redW)

record RedSub (θ : Γ ⊢ Δ) : Set where
  field red : (i : Δ ∋ A) → Redᵛ A (sub-mem θ i)
open RedSub

RedSub-wk : {Γ₁ : Ctx} (ρ : Γ₁ ⊇ Γ) {θ : Γ ⊢ Δ} → RedSub θ → RedSub (sub-wk ρ θ)
red (RedSub-wk ρ {θ} rθ) {A = A} i =
  Eq.subst (Redᵛ A)
           (begin
             wk-val ρ (sub-mem θ i)
             ≡˘⟨ sub-mem-wk ρ θ i ⟩
             sub-mem (sub-wk ρ θ) i
             ∎)
           (Red-wk A ρ (rθ .red i))

RedSub-ext : {θ : Γ ⊢ Δ} {V : Γ ⊢ᵛ A} → RedSub θ → Redᵛ A V → RedSub (sub-ex θ V)
RedSub-ext rθ rv = record { red = λ { here → rv ; (there i) → rθ .red i } }

RedSub-id : RedSub (sub-id {Γ})
red (RedSub-id {Γ}) {A = A} i =
  Eq.subst (Redᵛ A)
           (begin
             var i
           ≡˘⟨ sub-mem-id i ⟩
             sub-mem sub-id i
           ∎)
           (Red-varᵛ A i)

--------------------------------------------------------------------------
-- Fundamental Lemma

Fundamental-val : (θ : Γ ⊢ Δ) → RedSub θ → (V : Δ ⊢ᵛ A) → Redᵛ A (sub-val θ V)
Fundamental-comp : (θ : Γ ⊢ Δ) → RedSub θ → (M : Δ ⊢ᶜ A) → Redᶜ A (sub-comp θ M)

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

SN-theorem : (M : Γ ⊢ᶜ A) → SN ⟨ M ∥ ε ⟩
SN-theorem {Γ} {A} M =
  Eq.subst (λ N → SN ⟨ N ∥ ε ⟩) (sub-comp-id M)
           (Red→SNᶜ A (sub-comp sub-id M) (Fundamental-comp sub-id RedSub-id M))

--------------------------------------------------------------------------
-- eval

Normal : Cfg Γ B → Set
Normal σ = ∀ {σ₁} → σ →ᵏ σ₁ → ⊥

data Step? (σ : Cfg Γ B) : Set where
  done : Normal σ → Step? σ
  next : {σ₁ : Cfg Γ B} → σ →ᵏ σ₁ → Step? σ

step? : (σ : Cfg Γ B) → Step? σ
step? ⟨ push M N ∥ K ⟩      = next push-step
step? ⟨ return V ∥ ε ⟩      = done (λ ())
step? ⟨ return V ∥ N ∷ K ⟩  = next return-step
step? ⟨ app (var i) V ∥ K ⟩ = done (λ ())
step? ⟨ app (lam N) V ∥ K ⟩ = next app-lam-step

eval-acc : {σ : Cfg Γ B} → SN σ → Σ[ σ₁ ∈ Cfg Γ B ] (σ ↠ᵏ σ₁) × Normal σ₁
eval-acc {σ = σ} (sn f) with step? σ
... | done normal    = σ , σ ◼ , normal
... | next {σ₁} step with eval-acc (f step)
...   | (σ₂ , chain , normal) = σ₂ , σ ~>⟨ step ⟩ chain , normal

eval : (M : Γ ⊢ᶜ A) → Σ[ σ ∈ Cfg Γ A ] (⟨ M ∥ ε ⟩ ↠ᵏ σ) × Normal σ
eval M = eval-acc (SN-theorem M)
