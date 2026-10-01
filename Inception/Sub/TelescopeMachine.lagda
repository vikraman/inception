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

  data CStack : (X : Ty) → Set where

    ◻ :        CStack ℛ

    <_；_>∷_ :  Comp (Γ ∙ Y) X → (γ : MEnv Γ)
                → (pstack : CStack X)
                ------------------------------------
                → CStack Y

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

    _·﹝_╎_﹞ :  MEnv Γ → Comp Γ X → CStack X
               ----------------------------------------------
               → MEnv (Γ ∙ `ℓ)

wk-mclo : Wk Γ Δ → MClo Δ X → MClo Γ X
wk-mclo π unit = unit
wk-mclo π (pair 𝐖₁ 𝐖₂) = pair (wk-mclo π 𝐖₁) (wk-mclo π 𝐖₂)
wk-mclo π (lam M) = lam (wk-comp (wk-cong π) M)
wk-mclo π (label x) = label (wk-mem π x)

data CState : Set where

  ⟨_；_╎_⟩ :  (𝐖 : MClo Γ X) → (γ : MEnv Γ) → (K : CStack X)
              ---------------------------------------------------
              → CState

  ⟨_╎_╎_⟩ :  (M : Comp Γ X) → (γ : MEnv Γ) → (K : CStack X)
             -----------------------------------------------------------------
             → CState

lookup : Γ ∋ X → MEnv Γ → MClo Γ X
lookup here (γ · 𝐖) = wk-mclo (wk-wk wk-id) 𝐖
lookup here (γ ·﹝ 𝐖 ╎ K ﹞) = label here
lookup (there x) (γ · 𝐖) = wk-mclo (wk-wk wk-id) (lookup x γ)
lookup (there x) (γ ·﹝ 𝐖 ╎ K ﹞) = wk-mclo (wk-wk wk-id) (lookup x γ)

lookup-label : Γ ∋ `ℓ → MEnv Γ → CState
lookup-label here (γ · label x) = lookup-label x γ
lookup-label here (γ ·﹝ M ╎ K ﹞) = ⟨ M ╎ γ ╎ K ⟩
lookup-label (there x) (γ · 𝐖) = lookup-label x γ
lookup-label (there x) (γ ·﹝ M ╎ stack ﹞) = lookup-label x γ

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
           → CStack Y → CState
eval-app V W γ K =
  let
    M  = lam-to-comp (eval V γ)
  in
  ⟨ M ╎ γ · eval W γ ╎ K ⟩


data _→ᶜ_ : CState → CState → Set where

  eval→ :    {W : Val Γ X} {γ : MEnv Γ} {K : CStack X}
             -------------------------------------------
             →  ⟨ return W ╎ γ ╎ K ⟩ →ᶜ ⟨ eval W γ ； γ ╎ K ⟩

  return→ :  {𝐖 : MClo Γ X} {𝐖₁ : MClo Γ₁ X} {M : Comp (Γ₁ ∙ X) Y} {γ : MEnv Γ} {γ₁ : MEnv Γ₁} {K : CStack Y}
             {π : Wk Γ₁ Γ} {𝐖₁≡wk𝐖 : 𝐖₁ ≡ wk-mclo π 𝐖}
             --------------------------------------------------------------
             →  ⟨ 𝐖 ； γ ╎ < M ； γ₁ >∷ K ⟩ →ᶜ ⟨ M ╎ γ₁ · 𝐖₁ ╎ K ⟩

  push→ :    {M₁ : Comp Γ X} {M₂ : Comp (Γ ∙ X) Y} {γ : MEnv Γ} {K : CStack Y}
             ----------------------------------------------------------------
             →  ⟨ push M₁ M₂ ╎ γ ╎ K ⟩ →ᶜ ⟨ M₁ ╎ γ ╎ < M₂ ； γ >∷ K ⟩

  sub→ :     {M₁ : Comp (Γ ∙ `ℓ) X} {M₂ : Comp Γ X} {γ : MEnv Γ} {K : CStack X}
             ----------------------------------------------------------------
             →  ⟨ sub M₁ M₂ ╎ γ ╎ K ⟩ →ᶜ ⟨ M₁ ╎ γ ·﹝ M₂ ╎ K ﹞ ╎ K ⟩

  var→ :     {W : Val Γ `ℓ} {γ : MEnv Γ} {K : CStack X}
             ------------------------------------------
             →  ⟨ var W ╎ γ ╎ K ⟩ →ᶜ eval-jump W γ

  pmᶜ→ :     {W : Val Γ (X `× Y)} {γ : MEnv Γ}
             {M : Comp (Γ ∙ X ∙ Y) Z} {K : CStack Z}
             -------------------------------------------------------------
             →  ⟨ pm W M ╎ γ ╎ K ⟩ →ᶜ ⟨ M ╎ γ · eval₁ W γ · (wk-mclo (wk-wk wk-id) (eval₂ W γ)) ╎ K ⟩

  app→ :     {W₁ : Val Γ (X `⇒ Y)} {W₂ : Val Γ X} {γ : MEnv Γ} {K : CStack Y}
             ----------------------------------------------------------------
             →  ⟨ app W₁ W₂ ╎ γ ╎ K ⟩ →ᶜ eval-app W₁ W₂ γ K


{-

-- first need to prove that the weakening from the context of the main term to
-- the context of the term at the top of the stack develops deterministically;
-- should be true, but skipping this for now as the result might not be needed

determinismꟲ : {ℛ : Ty} {S S' : CState} (S→S'₁ S→S'₂ : S →ᶜ S') → (S→S'₁ ≡ S→S'₂)
determinismꟲ eval→ eval→ = refl
determinismꟲ (return→ {𝐖 = 𝐖} {𝐖₁ = 𝐖₁}) (return→ {𝐖 = 𝐖} {𝐖₁ = 𝐖₁}) = {!refl!}
determinismꟲ push→ push→ = refl
determinismꟲ sub→ sub→ = refl
determinismꟲ var→ var→ = refl
determinismꟲ pmᶜ→ pmᶜ→ = refl
determinismꟲ app→ app→ = refl
-}

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
progress ⟨ 𝐖 ； γ ╎ ◻ ⟩ = done (λ ())
progress ⟨ 𝐖 ； γ ╎ < x ； γ₁ >∷ K ⟩ = {!!} --step return→
progress ⟨ return x ╎ γ ╎ K ⟩ = step eval→
progress ⟨ pm x M ╎ γ ╎ K ⟩ = step pmᶜ→
progress ⟨ push M M₁ ╎ γ ╎ K ⟩ = step push→
progress ⟨ app x x₁ ╎ γ ╎ K ⟩ = step app→
progress ⟨ var x ╎ γ ╎ K ⟩ = step var→
progress ⟨ sub M M₁ ╎ γ ╎ K ⟩ = step sub→

-- A Normal CState is a halting state and of the form ⟨ 𝐖 ╎ ◻ ⟩.
halting-state :    (cstate : CState) → Normal cstate
                 → Σ[ Γ ∈ Ctx ] Σ[ 𝐖 ∈ MClo Γ ℛ ] Σ[ γ ∈ MEnv Γ ] cstate ≡ ⟨ 𝐖 ； γ ╎ ◻ ⟩
halting-state ⟨ 𝐖 ； γ ╎ ◻ ⟩ normal = _ , 𝐖 , γ , refl
halting-state ⟨ 𝐖 ； γ ╎ < x ； γ₁ >∷ K ⟩ normal = {!!} --ql (normal return→) (Σ-syntax Ctx (λ Γ₂ → Σ-syntax (MClo Γ₂ ℛ) (λ 𝐖₁ → Σ-syntax (MEnv Γ₂) (λ γ₂ → ⟨ 𝐖 ； γ ╎ < x ； γ₁ >∷ K ⟩ ≡ ⟨ 𝐖₁ ； γ₂ ╎ ◻ ⟩))))
halting-state ⟨ return x ╎ γ ╎ K ⟩ normal = ql (normal eval→) (Σ-syntax Ctx (λ Γ₁ → Σ-syntax (MClo Γ₁ ℛ) (λ 𝐖 → Σ-syntax (MEnv Γ₁) (λ γ₁ → ⟨ return x ╎ γ ╎ K ⟩ ≡ ⟨ 𝐖 ； γ₁ ╎ ◻ ⟩))))
halting-state ⟨ pm x M ╎ γ ╎ K ⟩ normal = ql (normal pmᶜ→) (Σ-syntax Ctx (λ Γ₁ → Σ-syntax (MClo Γ₁ ℛ) (λ 𝐖 → Σ-syntax (MEnv Γ₁) (λ γ₁ → ⟨ pm x M ╎ γ ╎ K ⟩ ≡ ⟨ 𝐖 ； γ₁ ╎ ◻ ⟩))))
halting-state ⟨ push M M₁ ╎ γ ╎ K ⟩ normal = ql (normal push→) (Σ-syntax Ctx (λ Γ₁ → Σ-syntax (MClo Γ₁ ℛ) (λ 𝐖 → Σ-syntax (MEnv Γ₁) (λ γ₁ → ⟨ push M M₁ ╎ γ ╎ K ⟩ ≡ ⟨ 𝐖 ； γ₁ ╎ ◻ ⟩))))
halting-state ⟨ app x x₁ ╎ γ ╎ K ⟩ normal = ql (normal app→) (Σ-syntax Ctx (λ Γ₁ → Σ-syntax (MClo Γ₁ ℛ) (λ 𝐖 → Σ-syntax (MEnv Γ₁) (λ γ₁ → ⟨ app x x₁ ╎ γ ╎ K ⟩ ≡ ⟨ 𝐖 ； γ₁ ╎ ◻ ⟩))))
halting-state ⟨ var x ╎ γ ╎ K ⟩ normal = ql (normal var→) (Σ-syntax Ctx (λ Γ₁ → Σ-syntax (MClo Γ₁ ℛ) (λ 𝐖 → Σ-syntax (MEnv Γ₁) (λ γ₁ → ⟨ var x ╎ γ ╎ K ⟩ ≡ ⟨ 𝐖 ； γ₁ ╎ ◻ ⟩))))
halting-state ⟨ sub M M₁ ╎ γ ╎ K ⟩ normal = ql (normal sub→) (Σ-syntax Ctx (λ Γ₁ → Σ-syntax (MClo Γ₁ ℛ) (λ 𝐖 → Σ-syntax (MEnv Γ₁) (λ γ₁ → ⟨ sub M M₁ ╎ γ ╎ K ⟩ ≡ ⟨ 𝐖 ； γ₁ ╎ ◻ ⟩))))

\end{code}
