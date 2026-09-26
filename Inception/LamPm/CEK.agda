module Inception.LamPm.CEK where

open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Inception.LamPm.Syntax
open import Inception.Prelude
open Inception.Prelude.RTC

--------------------------------------------------------------------------
-- closures and environments

infixl 20 _∷_

mutual
  data MVal : Ty → Set where
    unit : MVal `𝟙
    pair : MVal X → MVal Y → MVal (X `× Y)
    clo  : {Γ : Ctx} → (Γ ∙ X) ⊢ᶜ Y → Env Γ → MVal (X `⇒ Y)

  data Env : Ctx → Set where
    ∅   : Env ε
    _∷_ : Env Γ → MVal X → Env (Γ ∙ X)

lookup : Env Γ → Γ ∋ X → MVal X
lookup (γ ∷ 𝐕) here     = 𝐕
lookup (γ ∷ 𝐕) (there i) = lookup γ i

fst-v : MVal (X `× Y) → MVal X
fst-v (pair 𝐕 𝐖) = 𝐕

snd-v : MVal (X `× Y) → MVal Y
snd-v (pair 𝐕 𝐖) = 𝐖

eval-val : Γ ⊢ᵛ X → Env Γ → MVal X
eval-val (var i)    γ = lookup γ i
eval-val (lam M)    γ = clo M γ
eval-val (pair V W) γ = pair (eval-val V γ) (eval-val W γ)
eval-val (pm V W)   γ = eval-val W (γ ∷ fst-v (eval-val V γ) ∷ snd-v (eval-val V γ))
eval-val unit       γ = unit

--------------------------------------------------------------------------
-- continuations

infixr 20 _◂_∷_

data Kont : Ty → Ty → Set where
  ε     : Kont X X
  _◂_∷_ : {Γ : Ctx} → (N : (Γ ∙ X) ⊢ᶜ Y) → (γ : Env Γ) → (K : Kont Y Z) → Kont X Z

--------------------------------------------------------------------------
-- configurations, transitions

infix 5 ⟨_∥_∥_⟩
infix 5 [_∥_]

data Cfg : Ty → Set where
  ⟨_∥_∥_⟩ : {Γ : Ctx} → Γ ⊢ᶜ X → Env Γ → Kont X Y → Cfg Y
  [_∥_]   : MVal X → Kont X Y → Cfg Y

apply : MVal (X `⇒ Y) → MVal X → Kont Y Z → Cfg Z
apply (clo N γ) 𝐖 K = ⟨ N ∥ γ ∷ 𝐖 ∥ K ⟩

split : MVal (X `× Y) → (Γ ∙ X ∙ Y) ⊢ᶜ Z → Env Γ → Kont Z U → Cfg U
split 𝐕 M γ K = ⟨ M ∥ γ ∷ fst-v 𝐕 ∷ snd-v 𝐕 ∥ K ⟩

infix 5 _→ᵏ_

data _→ᵏ_ : {X : Ty} → Cfg X → Cfg X → Set where

  push-step   : {Γ : Ctx} {M : Γ ⊢ᶜ X} {N : (Γ ∙ X) ⊢ᶜ Y} {γ : Env Γ} {K : Kont Y Z}
              → ⟨ push M N ∥ γ ∥ K ⟩ →ᵏ ⟨ M ∥ γ ∥ N ◂ γ ∷ K ⟩

  return-step : {Γ : Ctx} {V : Γ ⊢ᵛ X} {γ : Env Γ} {K : Kont X Y}
              → ⟨ return V ∥ γ ∥ K ⟩ →ᵏ [ eval-val V γ ∥ K ]

  resume-step : {Γ : Ctx} {𝐕 : MVal X} {N : (Γ ∙ X) ⊢ᶜ Y} {γ : Env Γ} {K : Kont Y Z}
              → [ 𝐕 ∥ N ◂ γ ∷ K ] →ᵏ ⟨ N ∥ γ ∷ 𝐕 ∥ K ⟩

  app-step    : {Γ : Ctx} {V : Γ ⊢ᵛ (X `⇒ Y)} {W : Γ ⊢ᵛ X} {γ : Env Γ} {K : Kont Y Z}
              → ⟨ app V W ∥ γ ∥ K ⟩ →ᵏ apply (eval-val V γ) (eval-val W γ) K

  pm-step     : {Γ : Ctx} {V : Γ ⊢ᵛ (X `× Y)} {M : (Γ ∙ X ∙ Y) ⊢ᶜ Z} {γ : Env Γ} {K : Kont Z U}
              → ⟨ pm V M ∥ γ ∥ K ⟩ →ᵏ split (eval-val V γ) M γ K

infix 5 _↠ᵏ_

_↠ᵏ_ : {X : Ty} → Cfg X → Cfg X → Set
_↠ᵏ_ {X} = _~>*_ (_→ᵏ_ {X = X})

--------------------------------------------------------------------------
-- accessibility

data SN {X} (σ : Cfg X) : Set where
  sn : (∀ {σ₁} → σ →ᵏ σ₁ → SN σ₁) → SN σ

--------------------------------------------------------------------------
-- reducibility candidates

Redᵛ : (X : Ty) → MVal X → Set
Redᵏ : (X : Ty) → Kont X Y → Set

Redᵛ `𝟙    𝐕    = ⊤
Redᵛ (X `× Y) 𝐕 = Redᵛ X (fst-v 𝐕) × Redᵛ Y (snd-v 𝐕)
Redᵛ (X `⇒ Y) 𝐕 = ∀ {𝐖} → Redᵛ X 𝐖 → ∀ {Z} {K : Kont Y Z} → Redᵏ Y K → SN (apply 𝐕 𝐖 K)

Redᵏ X K = ∀ {𝐕} → Redᵛ X 𝐕 → SN [ 𝐕 ∥ K ]

record RedEnv (γ : Env Γ) : Set where
  field red : (i : Γ ∋ X) → Redᵛ X (lookup γ i)
open RedEnv

RedEnv-∅ : RedEnv ∅
red RedEnv-∅ ()

RedEnv-ext : {γ : Env Γ} {𝐕 : MVal X} → RedEnv γ → Redᵛ X 𝐕 → RedEnv (γ ∷ 𝐕)
RedEnv-ext redγ redv = record { red = λ { here → redv ; (there i) → redγ .red i } }

Redᵏ-ε : Redᵏ X ε
Redᵏ-ε redv = sn (λ ())

--------------------------------------------------------------------------
-- fundamental lemma

Fundamental-val  : (V : Γ ⊢ᵛ X) {γ : Env Γ} → RedEnv γ → Redᵛ X (eval-val V γ)
Fundamental-comp : (M : Γ ⊢ᶜ X) {γ : Env Γ} → RedEnv γ → {K : Kont X Y} → Redᵏ X K → SN ⟨ M ∥ γ ∥ K ⟩

Fundamental-val (var i)    redγ = redγ .red i
Fundamental-val unit       redγ = tt
Fundamental-val (pair V W) redγ = Fundamental-val V redγ , Fundamental-val W redγ
Fundamental-val (lam M) {γ} redγ {𝐖} redw redk = Fundamental-comp M (RedEnv-ext redγ redw) redk
Fundamental-val (pm V W) {γ} redγ =
  Fundamental-val W (RedEnv-ext (RedEnv-ext redγ (proj₁ (Fundamental-val V redγ))) (proj₂ (Fundamental-val V redγ)))

Fundamental-comp (return V) redγ redk =
  sn (λ { return-step → redk (Fundamental-val V redγ) })
Fundamental-comp (app V W) redγ redk =
  sn (λ { app-step → Fundamental-val V redγ (Fundamental-val W redγ) redk })
Fundamental-comp (push {X = X} M N) {γ} redγ {K} redk =
  sn (λ { push-step → Fundamental-comp M redγ redk₁ })
  where
  redk₁ : Redᵏ X (N ◂ γ ∷ K)
  redk₁ redv = sn (λ { resume-step → Fundamental-comp N (RedEnv-ext redγ redv) redk })
Fundamental-comp (pm V M) {γ} redγ redk =
  sn (λ { pm-step → Fundamental-comp M (RedEnv-ext (RedEnv-ext redγ (proj₁ (Fundamental-val V redγ))) (proj₂ (Fundamental-val V redγ))) redk })

SN-theorem : (M : ε ⊢ᶜ X) → SN ⟨ M ∥ ∅ ∥ ε ⟩
SN-theorem M = Fundamental-comp M RedEnv-∅ Redᵏ-ε

--------------------------------------------------------------------------
-- eval

Normal : Cfg X → Set
Normal σ = ∀ {σ₁} → σ →ᵏ σ₁ → ⊥

data Step? (σ : Cfg X) : Set where
  done : Normal σ → Step? σ
  next : {σ₁ : Cfg X} → σ →ᵏ σ₁ → Step? σ

step? : (σ : Cfg X) → Step? σ
step? ⟨ push M N ∥ γ ∥ K ⟩ = next push-step
step? ⟨ return V ∥ γ ∥ K ⟩ = next return-step
step? ⟨ app V W ∥ γ ∥ K ⟩  = next app-step
step? ⟨ pm V M ∥ γ ∥ K ⟩   = next pm-step
step? [ 𝐕 ∥ ε ]            = done (λ ())
step? [ 𝐕 ∥ N ◂ γ ∷ K ]    = next resume-step

eval-acc : {σ : Cfg X} → SN σ → Σ[ σ₁ ∈ Cfg X ] (σ ↠ᵏ σ₁) × Normal σ₁
eval-acc {σ = σ} (sn f) with step? σ
... | done normal    = σ , σ ◼ , normal
... | next {σ₁} step with eval-acc (f step)
...   | (σ₂ , chain , normal) = σ₂ , σ ~>⟨ step ⟩ chain , normal

eval : (M : ε ⊢ᶜ X) → Σ[ σ ∈ Cfg X ] (⟨ M ∥ ∅ ∥ ε ⟩ ↠ᵏ σ) × Normal σ
eval M = eval-acc (SN-theorem M)

open import Relation.Binary.PropositionalEquality

_ : eval (pm (pair unit unit) (return (lam {X = `𝟙} (return (var here)))))
       ≡ ([ clo (return (var here)) (∅ ∷ unit ∷ unit) ∥ ε ] ,
          _ ~>⟨ pm-step ⟩ _ ~>⟨ return-step ⟩ _ ◼ , (λ ()))
_ = refl
