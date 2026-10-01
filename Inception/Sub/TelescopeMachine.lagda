\begin{code}
{-# OPTIONS --no-postfix-projections #-}

open import Inception.Sub.Syntax using (Ty)

module Inception.Sub.TelescopeMachine (ℛ : Ty) where

open import Inception.Sub.Syntax
open import Inception.Prelude

open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

---------------------------------------------------------------------------------

infixl 27 _·_

---------------------------------------------------------------------------------
-- ENVIRONMENTS

\end{code}
%<*Env>
\begin{code}

mutual

  data CStack : (Γ : Ctx) → (X : Ty) → Set where

    ◻ :        CStack ε ℛ

    <_；_；_>∷_ :  Comp (Γ ∙ Y) X → (γ : MEnv Γ)
                → (π : Wk Γ Γ₁)
                → (K : CStack Γ₁ X)
                ------------------------------------
                → CStack Γ Y

  data MClo : Ctx → Ty → Set where

    unit :
              -------------------
              MClo Γ `𝟙

    pair :    (𝐖₁ : MClo Γ X₁) → (𝐖₂ : MClo Γ X₂)
              -------------------------------------------------
              → MClo Γ (X₁ `× X₂)

    lam :     (M : Comp (Γ ∙ X) Y)
              ----------------------------------------------------
              → MClo Γ (X `⇒ Y)

    label :   (x : Γ ∋ `ℓ)
              ----------------------------------------------------
              → MClo Γ `ℓ


  data MEnv : Ctx → Set where

    ⋄ :
               --------------
               MEnv ε

    _·_ :      MEnv Γ → MClo Γ X
               ----------------------------------
               → MEnv (Γ ∙ X)

    _·﹝_╎_╎_﹞ :  MEnv Γ → Comp Γ X → Wk Γ Γ₁ → CStack Γ₁ X
               ----------------------------------------------
               → MEnv (Γ ∙ `ℓ)

wk-mclo : Wk Γ Δ → MClo Δ X → MClo Γ X
wk-mclo π unit = unit
wk-mclo π (pair 𝐖₁ 𝐖₂) = pair (wk-mclo π 𝐖₁) (wk-mclo π 𝐖₂)
wk-mclo π (lam M) = lam (wk-comp (wk-cong π) M)
wk-mclo π (label x) = label (wk-mem π x)

data CState : Set where

  ⟨_；_╎_╎_⟩ :  (𝐖 : MClo Γ X) → (γ : MEnv Γ) → (π : Wk Γ Γ₁) → (K : CStack Γ₁ X)
              ---------------------------------------------------
              → CState

  ⟨_╎_╎_╎_⟩ :  (M : Comp Γ X) → (γ : MEnv Γ) → (π : Wk Γ Γ₁) → (K : CStack Γ₁ X)
             -----------------------------------------------------------------
             → CState

lookup : Γ ∋ X → MEnv Γ → MClo Γ X
lookup here (γ · 𝐖) = wk-mclo (wk-wk wk-id) 𝐖
lookup here (γ ·﹝ 𝐖 ╎ π ╎ K ﹞) = label here
lookup (there x) (γ · 𝐖) = wk-mclo (wk-wk wk-id) (lookup x γ)
lookup (there x) (γ ·﹝ 𝐖 ╎ π ╎ K ﹞) = wk-mclo (wk-wk wk-id) (lookup x γ)

lookup-label : Γ ∋ `ℓ → MEnv Γ → CState
lookup-label here (γ · label x) = lookup-label x γ
lookup-label here (γ ·﹝ M ╎ π ╎ K ﹞) = ⟨ M ╎ γ ╎ π ╎ K ⟩
lookup-label (there x) (γ · 𝐖) = lookup-label x γ
lookup-label (there x) (γ ·﹝ M ╎ π ╎ stack ﹞) = lookup-label x γ

lam-to-comp :  MClo Γ (X `⇒ Y) → Comp (Γ ∙ X) Y
lam-to-comp (lam M) = M

jump-to-state : MClo Γ `ℓ → MEnv Γ → CState
jump-to-state (label x) γ = lookup-label x γ

eval : Val Γ X → MEnv Γ → MClo Γ X
eval (var i) γ = lookup i γ
eval (lam M) γ = lam M
eval (pair V W) γ = pair (eval V γ) (eval W γ)
eval unit γ = unit

eval-jump : Val Γ `ℓ → MEnv Γ → CState
eval-jump W γ = jump-to-state (eval W γ) γ

proj₁-mclo : MClo Γ (X₁ `× X₂) → MClo Γ X₁
proj₁-mclo (pair 𝐖₁ 𝐖₂) = 𝐖₁

proj₂-mclo : MClo Γ (X₁ `× X₂) → MClo Γ X₂
proj₂-mclo (pair 𝐖₁ 𝐖₂) = 𝐖₂

eval₁ : Val Γ (X₁ `× X₂) → MEnv Γ → MClo Γ X₁
eval₁ W γ = proj₁-mclo (eval W γ)

eval₂ : Val Γ (X₁ `× X₂) → MEnv Γ → MClo Γ X₂
eval₂ W γ = proj₂-mclo (eval W γ)

eval-app : Val Γ (X `⇒ Y) → Val Γ X → MEnv Γ
           → Wk Γ Γ₁ → CStack Γ₁ Y → CState
eval-app V W γ π K =
  let
    M  = lam-to-comp (eval V γ)
  in
  ⟨ M ╎ γ · eval W γ ╎ wk-wk π ╎ K ⟩


data _→ᶜ_ : CState → CState → Set where

  eval→ :    {W : Val Γ X} {γ : MEnv Γ} {π : Wk Γ Γ₁} {K : CStack Γ₁ X}
             -------------------------------------------
             →  ⟨ return W ╎ γ ╎ π ╎ K ⟩ →ᶜ ⟨ eval W γ ； γ ╎ π ╎ K ⟩

  return→ :  {𝐖 : MClo Γ X} {M₁ : Comp (Γ₁ ∙ X) Y} {γ : MEnv Γ} {γ₁ : MEnv Γ₁} {Γ₂ : Ctx} {K : CStack Γ₂ Y}
             {π : Wk Γ Γ₁} {π₁ : Wk Γ₁ Γ₂} --{M≡wkM₁ : M ≡ wk-comp (wk-cong π) M₁}
             --------------------------------------------------------------
             →  ⟨ 𝐖 ； γ ╎ π ╎ < M₁ ； γ₁ ； π₁ >∷ K ⟩ →ᶜ ⟨ wk-comp (wk-cong π) M₁ ╎ γ · 𝐖 ╎ wk-wk (wk-trans π π₁) ╎ K ⟩

  push→ :    {M₁ : Comp Γ X} {M₂ : Comp (Γ ∙ X) Y} {γ : MEnv Γ} {π : Wk Γ Γ₁} {K : CStack Γ₁ Y}
             ----------------------------------------------------------------
             →  ⟨ push M₁ M₂ ╎ γ ╎ π ╎ K ⟩ →ᶜ ⟨ M₁ ╎ γ ╎ wk-id ╎ < M₂ ； γ ； π >∷ K ⟩

  sub→ :     {M₁ : Comp (Γ ∙ `ℓ) X} {M₂ : Comp Γ X} {γ : MEnv Γ} {π : Wk Γ Γ₁} {K : CStack Γ₁ X}
             ----------------------------------------------------------------
             →  ⟨ sub M₁ M₂ ╎ γ ╎ π ╎ K ⟩ →ᶜ ⟨ M₁ ╎ γ ·﹝ M₂ ╎ π ╎ K ﹞ ╎ wk-wk π ╎ K ⟩

  var→ :     {W : Val Γ `ℓ} {γ : MEnv Γ} {π : Wk Γ Γ₁} {K : CStack Γ₁ X}
             ------------------------------------------
             →  ⟨ var W ╎ γ ╎ π ╎ K ⟩ →ᶜ eval-jump W γ

  pmᶜ→ :     {W : Val Γ (X `× Y)} {γ : MEnv Γ}
             {M : Comp (Γ ∙ X ∙ Y) Z} {π : Wk Γ Γ₁} {K : CStack Γ₁ Z}
             -------------------------------------------------------------
             →  ⟨ pm W M ╎ γ ╎ π ╎ K ⟩ →ᶜ ⟨ M ╎ γ · eval₁ W γ · (wk-mclo (wk-wk wk-id) (eval₂ W γ)) ╎ wk-wk (wk-wk π) ╎ K ⟩

  app→ :     {W₁ : Val Γ (X `⇒ Y)} {W₂ : Val Γ X} {γ : MEnv Γ} {π : Wk Γ Γ₁} {K : CStack Γ₁ Y}
             ----------------------------------------------------------------
             →  ⟨ app W₁ W₂ ╎ γ ╎ π ╎ K ⟩ →ᶜ eval-app W₁ W₂ γ π K


determinismꟲ : {ℛ : Ty} {S S' : CState} (S→S'₁ S→S'₂ : S →ᶜ S') → (S→S'₁ ≡ S→S'₂)
determinismꟲ eval→ eval→ = refl
determinismꟲ return→ return→ = refl
determinismꟲ push→ push→ = refl
determinismꟲ sub→ sub→ = refl
determinismꟲ var→ var→ = refl
determinismꟲ pmᶜ→ pmᶜ→ = refl
determinismꟲ app→ app→ = refl

open Inception.Prelude.RTC renaming (_~>⟨_⟩_ to _→ᶜ⟨_⟩_)

_→ᶜ*_ : CState → CState → Set
_→ᶜ*_ = _~>*_ (_→ᶜ_)

_⨾ᶜ_ : {σ₁ σ₂ σ₃ : CState} → (σ₁ →ᶜ* σ₂) → (σ₂ →ᶜ* σ₃) → (σ₁ →ᶜ* σ₃)
_⨾ᶜ_ (σ ◼) ss = ss
_⨾ᶜ_ (σ →ᶜ⟨ s ⟩ ss₁) ss₂ = σ →ᶜ⟨ s ⟩ (ss₁ ⨾ᶜ ss₂)

{-
data SN (σ : CState) : Set where
  sn : (∀ {σ₁} → σ →ᶜ σ₁ → SN σ₁) → SN σ

Rᵛ : (X : Ty) → MClo Γ X → MEnv Γ → Set
Rᵏ : (X : Ty) → CStack X → Set
Rᴱ : MEnv Γ → Set

Rᵛ `𝟙 unit γ = ⊤
Rᵛ (X `× Y) (pair 𝐕 𝐖) γ = Rᵛ X 𝐕 γ × Rᵛ Y 𝐖 γ
Rᵛ {Γ = Γ} (X `⇒ Y) (lam M) γ = ∀ {𝐖 : MClo Γ X} → Rᵛ X 𝐖 γ → Rᴱ γ → ∀ {K : CStack Y} → Rᵏ Y K → SN ⟨ M ╎ γ · 𝐖 ╎ K ⟩
Rᵛ `ℓ (label x) γ = SN (lookup-label x γ)

Rᴱ {Γ = Γ} ⋄ = ⊤
Rᴱ {Γ = Γ ∙ X} (γ · 𝐖) = Rᴱ γ × Rᵛ X 𝐖 γ
Rᴱ {Γ = Γ} (γ ·﹝ M ╎ K ﹞) = SN ⟨ M ╎ γ ╎ K ⟩

-- termination check fails here
Rᵏ X ◻ = ⊤
Rᵏ X (<_；_>∷_ {Γ = Γ} {Y = Y} M γ K) = ∀ {𝐖 : MClo Γ Y} → {!!} --Rᵛ Y 𝐖 γ → {!!}
-}

-- A CState is Normal, if there are no transitions from it.
Normal : CState → Set
Normal σ₁ = ∀ {σ₂} → σ₁ →ᶜ σ₂ → ⊥

data Progress (σ : CState) : Set where
  done : Normal σ → Progress σ
  step : {σ' : CState} → σ →ᶜ σ' → Progress σ

progress : (σ : CState) → Progress σ
progress ⟨ 𝐖 ； γ ╎ π ╎ ◻ ⟩ = done (λ ())
progress ⟨ 𝐖 ； γ ╎ π ╎ < x ； γ₁ ； π₁ >∷ K ⟩ = step return→
progress ⟨ return x ╎ γ ╎ π ╎ K ⟩ = step eval→
progress ⟨ pm x M ╎ γ ╎ π ╎ K ⟩ = step pmᶜ→
progress ⟨ push M M₁ ╎ γ ╎ π ╎ K ⟩ = step push→
progress ⟨ app x x₁ ╎ γ ╎ π ╎ K ⟩ = step app→
progress ⟨ var x ╎ γ ╎ π ╎ K ⟩ = step var→
progress ⟨ sub M M₁ ╎ γ ╎ π ╎ K ⟩ = step sub→

-- A Normal CState is a halting state and of the form ⟨ 𝐖 ╎ ◻ ⟩.
halting-state :    (cstate : CState) → Normal cstate
                 → Σ[ Γ ∈ Ctx ] Σ[ π ∈ Wk Γ ε ] Σ[ 𝐖 ∈ MClo Γ ℛ ] Σ[ γ ∈ MEnv Γ ] cstate ≡ ⟨ 𝐖 ； γ ╎ π ╎ ◻ ⟩
halting-state ⟨ 𝐖 ； γ ╎ π ╎ ◻ ⟩ normal = _ , π , 𝐖 , γ , refl
halting-state ⟨ 𝐖 ； γ ╎ π ╎ < x ； γ₁ ； π₁ >∷ K ⟩ normal = ql (normal return→) (Σ-syntax Ctx (λ Γ₃ → Σ-syntax (Wk Γ₃ ε) (λ π₂ → Σ-syntax (MClo Γ₃ ℛ) (λ 𝐖₁ → Σ-syntax (MEnv Γ₃) (λ γ₂ → ⟨ 𝐖 ； γ ╎ π ╎ < x ； γ₁ ； π₁ >∷ K ⟩ ≡ ⟨ 𝐖₁ ； γ₂ ╎ π₂ ╎ ◻ ⟩)))))
halting-state ⟨ return W ╎ γ ╎ π ╎ K ⟩ normal = ql (normal eval→) (Σ-syntax Ctx (λ Γ₂ → Σ-syntax (Wk Γ₂ ε) (λ π₁ → Σ-syntax (MClo Γ₂ ℛ) (λ 𝐖 → Σ-syntax (MEnv Γ₂) (λ γ₁ → ⟨ return W ╎ γ ╎ π ╎ K ⟩ ≡ ⟨ 𝐖 ； γ₁ ╎ π₁ ╎ ◻ ⟩)))))
halting-state ⟨ pm W M ╎ γ ╎ π ╎ K ⟩ normal = ql (normal pmᶜ→) (Σ-syntax Ctx (λ Γ₂ → Σ-syntax (Wk Γ₂ ε) (λ π₁ → Σ-syntax (MClo Γ₂ ℛ) (λ 𝐖 → Σ-syntax (MEnv Γ₂) (λ γ₁ → ⟨ pm W M ╎ γ ╎ π ╎ K ⟩ ≡ ⟨ 𝐖 ； γ₁ ╎ π₁ ╎ ◻ ⟩)))))
halting-state ⟨ push M₁ M₂ ╎ γ ╎ π ╎ K ⟩ normal = ql (normal push→) (Σ-syntax Ctx (λ Γ₂ → Σ-syntax (Wk Γ₂ ε) (λ π₁ → Σ-syntax (MClo Γ₂ ℛ) (λ 𝐖 → Σ-syntax (MEnv Γ₂) (λ γ₁ → ⟨ push M₁ M₂ ╎ γ ╎ π ╎ K ⟩ ≡ ⟨ 𝐖 ； γ₁ ╎ π₁ ╎ ◻ ⟩)))))
halting-state ⟨ app W₁ W₂ ╎ γ ╎ π ╎ K ⟩ normal = ql (normal app→) (Σ-syntax Ctx (λ Γ₂ → Σ-syntax (Wk Γ₂ ε) (λ π₁ → Σ-syntax (MClo Γ₂ ℛ) (λ 𝐖 → Σ-syntax (MEnv Γ₂) (λ γ₁ → ⟨ app W₁ W₂ ╎ γ ╎ π ╎ K ⟩ ≡ ⟨ 𝐖 ； γ₁ ╎ π₁ ╎ ◻ ⟩)))))
halting-state ⟨ var W ╎ γ ╎ π ╎ K ⟩ normal = ql (normal var→) (Σ-syntax Ctx (λ Γ₂ → Σ-syntax (Wk Γ₂ ε) (λ π₁ → Σ-syntax (MClo Γ₂ ℛ) (λ 𝐖 → Σ-syntax (MEnv Γ₂) (λ γ₁ → ⟨ var W ╎ γ ╎ π ╎ K ⟩ ≡ ⟨ 𝐖 ； γ₁ ╎ π₁ ╎ ◻ ⟩)))))
halting-state ⟨ sub M₁ M₂ ╎ γ ╎ π ╎ K ⟩ normal = ql (normal sub→) (Σ-syntax Ctx (λ Γ₂ → Σ-syntax (Wk Γ₂ ε) (λ π₁ → Σ-syntax (MClo Γ₂ ℛ) (λ 𝐖 → Σ-syntax (MEnv Γ₂) (λ γ₁ → ⟨ sub M₁ M₂ ╎ γ ╎ π ╎ K ⟩ ≡ ⟨ 𝐖 ； γ₁ ╎ π₁ ╎ ◻ ⟩)))))

\end{code}
