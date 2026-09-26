module Inception.Lam.CEK where

open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)

open import Inception.Lam.Syntax
open import Inception.Prelude
open Inception.Prelude.RTC

--------------------------------------------------------------------------
-- closures and environments

mutual
  data MVal : Ty → Set where
    unit : MVal `Unit
    clo  : {Γ : Ctx} → (Γ ∙ A) ⊢ᶜ B → Env Γ → MVal (A `⇒ B)

  data Env : Ctx → Set where
    ∅   : Env ε
    _∷_ : Env Γ → MVal A → Env (Γ ∙ A)

lookup : Env Γ → Γ ∋ A → MVal A
lookup (γ ∷ 𝐕) here     = 𝐕
lookup (γ ∷ 𝐕) (there i) = lookup γ i

eval-val : Γ ⊢ᵛ A → Env Γ → MVal A
eval-val (var i) γ = lookup γ i
eval-val (lam M) γ = clo M γ
eval-val unit    γ = unit

--------------------------------------------------------------------------
-- continuations

infixr 20 _◂_∷_

data Kont : Ty → Ty → Set where
  ε     : Kont A A
  _◂_∷_ : {Γ : Ctx} → (N : (Γ ∙ A) ⊢ᶜ B) → (γ : Env Γ) → (K : Kont B C) → Kont A C

--------------------------------------------------------------------------
-- states, configurations, transitions

infix 5 ⟨_∥_∥_⟩
infix 5 ⟨_∥_⟩

data Cfg : Ty → Set where
  ⟨_∥_∥_⟩ : {Γ : Ctx} → Γ ⊢ᶜ A → Env Γ → Kont A B → Cfg B
  ⟨_∥_⟩   : MVal A → Kont A B → Cfg B

apply : MVal (A `⇒ B) → MVal A → Kont B C → Cfg C
apply (clo N γ) 𝐖 K = ⟨ N ∥ γ ∷ 𝐖 ∥ K ⟩

infix 5 _→ᵏ_

data _→ᵏ_ : {B : Ty} → Cfg B → Cfg B → Set where

  push-step   : {Γ : Ctx} {M : Γ ⊢ᶜ A} {N : (Γ ∙ A) ⊢ᶜ B} {γ : Env Γ} {K : Kont B C}
              → ⟨ push M N ∥ γ ∥ K ⟩ →ᵏ ⟨ M ∥ γ ∥ N ◂ γ ∷ K ⟩

  return-step : {Γ : Ctx} {V : Γ ⊢ᵛ A} {γ : Env Γ} {K : Kont A B}
              → ⟨ return V ∥ γ ∥ K ⟩ →ᵏ ⟨ eval-val V γ ∥ K ⟩

  resume-step : {Γ : Ctx} {𝐕 : MVal A} {N : (Γ ∙ A) ⊢ᶜ B} {γ : Env Γ} {K : Kont B C}
              → ⟨ 𝐕 ∥ N ◂ γ ∷ K ⟩ →ᵏ ⟨ N ∥ γ ∷ 𝐕 ∥ K ⟩

  app-step    : {Γ : Ctx} {V : Γ ⊢ᵛ (A `⇒ B)} {W : Γ ⊢ᵛ A} {γ : Env Γ} {K : Kont B C}
              → ⟨ app V W ∥ γ ∥ K ⟩ →ᵏ apply (eval-val V γ) (eval-val W γ) K

infix 5 _↠ᵏ_

_↠ᵏ_ : {B : Ty} → Cfg B → Cfg B → Set
_↠ᵏ_ {B} = _~>*_ (_→ᵏ_ {B = B})

--------------------------------------------------------------------------
-- accessibility

data SN {B} (σ : Cfg B) : Set where
  sn : (∀ {σ₁} → σ →ᵏ σ₁ → SN σ₁) → SN σ

--------------------------------------------------------------------------
-- reducibility candidates

Redᵛ : (A : Ty) → MVal A → Set
Redᵏ : (A : Ty) → Kont A B → Set

Redᵛ `Unit    𝐕 = ⊤
Redᵛ (A `⇒ B) 𝐕 = ∀ {𝐖} → Redᵛ A 𝐖 → ∀ {C} {K : Kont B C} → Redᵏ B K → SN (apply 𝐕 𝐖 K)

Redᵏ A K = ∀ {𝐕} → Redᵛ A 𝐕 → SN ⟨ 𝐕 ∥ K ⟩

record RedEnv (γ : Env Γ) : Set where
  field red : (i : Γ ∋ A) → Redᵛ A (lookup γ i)
open RedEnv

RedEnv-∅ : RedEnv ∅
red RedEnv-∅ ()

RedEnv-ext : {γ : Env Γ} {𝐕 : MVal A} → RedEnv γ → Redᵛ A 𝐕 → RedEnv (γ ∷ 𝐕)
RedEnv-ext redγ redv = record { red = λ { here → redv ; (there i) → redγ .red i } }

Redᵏ-ε : Redᵏ A ε
Redᵏ-ε redv = sn (λ ())

--------------------------------------------------------------------------
-- Fundamental Lemma

Fundamental-val  : (V : Γ ⊢ᵛ A) {γ : Env Γ} → RedEnv γ → Redᵛ A (eval-val V γ)
Fundamental-comp : (M : Γ ⊢ᶜ A) {γ : Env Γ} → RedEnv γ → {K : Kont A B} → Redᵏ A K → SN ⟨ M ∥ γ ∥ K ⟩

Fundamental-val (var i) redγ = redγ .red i
Fundamental-val unit    redγ = tt
Fundamental-val (lam M) {γ} redγ {𝐖} redw redk = Fundamental-comp M (RedEnv-ext redγ redw) redk

Fundamental-comp (return V) redγ redk =
  sn (λ { return-step → redk (Fundamental-val V redγ) })
Fundamental-comp (app V W) redγ redk =
  sn (λ { app-step → Fundamental-val V redγ (Fundamental-val W redγ) redk })
Fundamental-comp (push {A = A} M N) {γ} redγ {K} redk =
  sn (λ { push-step → Fundamental-comp M redγ redk₁ })
  where
  redk₁ : Redᵏ A (N ◂ γ ∷ K)
  redk₁ redv = sn (λ { resume-step → Fundamental-comp N (RedEnv-ext redγ redv) redk })

SN-theorem : (M : ε ⊢ᶜ A) → SN ⟨ M ∥ ∅ ∥ ε ⟩
SN-theorem M = Fundamental-comp M RedEnv-∅ Redᵏ-ε

--------------------------------------------------------------------------
-- eval

Normal : Cfg B → Set
Normal σ = ∀ {σ₁} → σ →ᵏ σ₁ → ⊥

data Step? (σ : Cfg B) : Set where
  done : Normal σ → Step? σ
  next : {σ₁ : Cfg B} → σ →ᵏ σ₁ → Step? σ

step? : (σ : Cfg B) → Step? σ
step? ⟨ push M N ∥ γ ∥ K ⟩ = next push-step
step? ⟨ return V ∥ γ ∥ K ⟩ = next return-step
step? ⟨ app V W ∥ γ ∥ K ⟩  = next app-step
step? ⟨ 𝐕 ∥ ε ⟩            = done (λ ())
step? ⟨ 𝐕 ∥ N ◂ γ ∷ K ⟩    = next resume-step

eval-acc : {σ : Cfg B} → SN σ → Σ[ σ₁ ∈ Cfg B ] (σ ↠ᵏ σ₁) × Normal σ₁
eval-acc {σ = σ} (sn f) with step? σ
... | done normal    = σ , σ ◼ , normal
... | next {σ₁} step with eval-acc (f step)
...   | (σ₂ , chain , normal) = σ₂ , σ ~>⟨ step ⟩ chain , normal

eval : (M : ε ⊢ᶜ A) → Σ[ σ ∈ Cfg A ] (⟨ M ∥ ∅ ∥ ε ⟩ ↠ᵏ σ) × Normal σ
eval M = eval-acc (SN-theorem M)
