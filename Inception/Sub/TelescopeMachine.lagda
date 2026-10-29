\begin{code}
{-# OPTIONS --no-postfix-projections #-}

open import Inception.Sub.Syntax using (Ty)

module Inception.Sub.TelescopeMachine (ℛ : Ty) where

open import Inception.Prelude
open import Inception.Sub.Syntax

open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Unit using (⊤; tt)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

--------------------------------------------------------------------------

infixl 27 _·﹝_╎_╎_﹞
infixl 27 <_；_；_>∷_
infixl 27 _·_

--------------------------------------------------------------------------
-- environments

\end{code}
%<*Env>
\begin{code}

mutual

  data CStack : (Γ : Ctx) → (X : Ty) → Set where

    ◻ :        CStack ε ℛ

    <_；_；_>∷_ :  (Γ ∙ Y) ⊢ᶜ X → (γ : MEnv Γ)
                → (π : Γ ⊇ Δ)
                → (K : CStack Δ X)
                ------------------------------------
                → CStack Γ Y

  data OMVal : Ctx → Ty → Set where

    unit :
              -------------------
              OMVal Γ `𝟙

    pair :    (𝐕 : OMVal Γ X) → (𝐖 : OMVal Γ Y)
              -------------------------------------------------
              → OMVal Γ (X `× Y)

    lam :     (M : (Γ ∙ X) ⊢ᶜ Y)
              ----------------------------------------------------
              → OMVal Γ (X `⇒ Y)

    label :   (i : Γ ∋ `ℓ)
              ----------------------------------------------------
              → OMVal Γ `ℓ


  data MEnv : Ctx → Set where

    ⋄ :
               --------------
               MEnv ε

    _·_ :      MEnv Γ → OMVal Γ X
               ----------------------------------
               → MEnv (Γ ∙ X)

    _·﹝_╎_╎_﹞ :  MEnv Γ → Γ ⊢ᶜ X → Γ ⊇ Δ → CStack Δ X
               ----------------------------------------------
               → MEnv (Γ ∙ `ℓ)

wk-omval : Γ ⊇ Δ → OMVal Δ X → OMVal Γ X
wk-omval π unit = unit
wk-omval π (pair 𝐕 𝐖) = pair (wk-omval π 𝐕) (wk-omval π 𝐖)
wk-omval π (lam M) = lam (wk-comp (wk-cong π) M)
wk-omval π (label x) = label (wk-mem π x)

data CState : Set where

  ⟨_；_╎_╎_⟩ :  (𝐖 : OMVal Γ X) → (γ : MEnv Γ) → (π : Γ ⊇ Δ) → (K : CStack Δ X)
              ---------------------------------------------------
              → CState

  ⟨_╎_╎_╎_⟩ :  (M : Γ ⊢ᶜ X) → (γ : MEnv Γ) → (π : Γ ⊇ Δ) → (K : CStack Δ X)
             -----------------------------------------------------------------
             → CState

lookup : Γ ∋ X → MEnv Γ → OMVal Γ X
lookup here (γ · 𝐖) = wk-omval (wk-wk wk-id) 𝐖
lookup here (γ ·﹝ 𝐖 ╎ π ╎ K ﹞) = label here
lookup (there x) (γ · 𝐖) = wk-omval (wk-wk wk-id) (lookup x γ)
lookup (there x) (γ ·﹝ 𝐖 ╎ π ╎ K ﹞) = wk-omval (wk-wk wk-id) (lookup x γ)

-- currently not used; would have to figure out eval for pairs when doing this
lookup₁ : Γ ∋ X → MEnv Γ → Σ[ Δ ∈ Ctx ] (MEnv Δ × OMVal Δ X)
lookup₁ here (γ · 𝐖) = _ , γ , 𝐖
lookup₁ here (γ ·﹝ 𝐖 ╎ π ╎ K ﹞) = _ , γ ·﹝ 𝐖 ╎ π ╎ K ﹞ , label here
lookup₁ (there x) (γ · 𝐖) = lookup₁ x γ
lookup₁ (there x) (γ ·﹝ 𝐖 ╎ π ╎ K ﹞) = lookup₁ x γ

lookup-label : Γ ∋ `ℓ → MEnv Γ → CState
lookup-label here (γ · label x) = lookup-label x γ
lookup-label here (γ ·﹝ M ╎ π ╎ K ﹞) = ⟨ M ╎ γ ╎ π ╎ K ⟩
lookup-label (there x) (γ · 𝐖) = lookup-label x γ
lookup-label (there x) (γ ·﹝ M ╎ π ╎ stack ﹞) = lookup-label x γ

lam-to-comp :  OMVal Γ (X `⇒ Y) → (Γ ∙ X) ⊢ᶜ Y
lam-to-comp (lam M) = M

eval : Γ ⊢ᵛ X → MEnv Γ → OMVal Γ X
eval (var i) γ = lookup i γ
eval (lam M) γ = lam M
eval (pair V W) γ = pair (eval V γ) (eval W γ)
eval unit γ = unit

eval-jump : Γ ⊢ᵛ `ℓ → MEnv Γ → CState
eval-jump (var i) γ = lookup-label i γ

proj₁-omval : OMVal Γ (X `× Y) → OMVal Γ X
proj₁-omval (pair 𝐕 𝐖) = 𝐕

proj₂-omval : OMVal Γ (X `× Y) → OMVal Γ Y
proj₂-omval (pair 𝐕 𝐖) = 𝐖

eval₁ : Γ ⊢ᵛ (X `× Y) → MEnv Γ → OMVal Γ X
eval₁ W γ = proj₁-omval (eval W γ)

eval₂ : Γ ⊢ᵛ (X `× Y) → MEnv Γ → OMVal Γ Y
eval₂ W γ = proj₂-omval (eval W γ)

eval-app : Γ ⊢ᵛ (X `⇒ Y) → Γ ⊢ᵛ X → MEnv Γ
           → Γ ⊇ Δ → CStack Δ Y → CState
eval-app V W γ π K =
  let
    M  = lam-to-comp (eval V γ)
  in
  ⟨ M ╎ γ · eval W γ ╎ wk-wk π ╎ K ⟩


data _→ᶜ_ : CState → CState → Set where

  eval→ :    {W : Γ ⊢ᵛ X} {γ : MEnv Γ} {π : Γ ⊇ Δ} {K : CStack Δ X}
             -------------------------------------------
             →  ⟨ return W ╎ γ ╎ π ╎ K ⟩ →ᶜ ⟨ eval W γ ； γ ╎ π ╎ K ⟩

  return→ :  {𝐖 : OMVal Γ X} {M : (Δ ∙ X) ⊢ᶜ Y} {γ : MEnv Γ} {δ : MEnv Δ} {Ψ : Ctx} {K : CStack Ψ Y}
             {π : Γ ⊇ Δ} {π₁ : Δ ⊇ Ψ}
             --------------------------------------------------------------
             →  ⟨ 𝐖 ； γ ╎ π ╎ < M ； δ ； π₁ >∷ K ⟩ →ᶜ ⟨ wk-comp (wk-cong π) M ╎ γ · 𝐖 ╎ wk-wk (wk-trans π π₁) ╎ K ⟩

  push→ :    {M : Γ ⊢ᶜ X} {N : (Γ ∙ X) ⊢ᶜ Y} {γ : MEnv Γ} {π : Γ ⊇ Δ} {K : CStack Δ Y}
             ----------------------------------------------------------------
             →  ⟨ push M N ╎ γ ╎ π ╎ K ⟩ →ᶜ ⟨ M ╎ γ ╎ wk-id ╎ < N ； γ ； π >∷ K ⟩

  sub→ :     {M : (Γ ∙ `ℓ) ⊢ᶜ X} {N : Γ ⊢ᶜ X} {γ : MEnv Γ} {π : Γ ⊇ Δ} {K : CStack Δ X}
             ----------------------------------------------------------------
             →  ⟨ sub M N ╎ γ ╎ π ╎ K ⟩ →ᶜ ⟨ M ╎ γ ·﹝ N ╎ π ╎ K ﹞ ╎ wk-wk π ╎ K ⟩

  var→ :     {W : Γ ⊢ᵛ `ℓ} {γ : MEnv Γ} {π : Γ ⊇ Δ} {K : CStack Δ X}
             ------------------------------------------
             →  ⟨ var W ╎ γ ╎ π ╎ K ⟩ →ᶜ eval-jump W γ

  pmᶜ→ :     {W : Γ ⊢ᵛ (X `× Y)} {γ : MEnv Γ}
             {M : (Γ ∙ X ∙ Y) ⊢ᶜ Z} {π : Γ ⊇ Δ} {K : CStack Δ Z}
             -------------------------------------------------------------
             →  ⟨ pm W M ╎ γ ╎ π ╎ K ⟩ →ᶜ ⟨ M ╎ γ · eval₁ W γ · (wk-omval (wk-wk wk-id) (eval₂ W γ)) ╎ wk-wk (wk-wk π) ╎ K ⟩

  app→ :     {V : Γ ⊢ᵛ (X `⇒ Y)} {W : Γ ⊢ᵛ X} {γ : MEnv Γ} {π : Γ ⊇ Δ} {K : CStack Δ Y}
             ----------------------------------------------------------------
             →  ⟨ app V W ╎ γ ╎ π ╎ K ⟩ →ᶜ eval-app V W γ π K


determinismꟲ : {ℛ : Ty} {σ σ₁ : CState} (σ→σ₁₁ σ→σ₁₂ : σ →ᶜ σ₁) → (σ→σ₁₁ ≡ σ→σ₁₂)
determinismꟲ eval→ eval→ = refl
determinismꟲ return→ return→ = refl
determinismꟲ push→ push→ = refl
determinismꟲ sub→ sub→ = refl
determinismꟲ var→ var→ = refl
determinismꟲ pmᶜ→ pmᶜ→ = refl
determinismꟲ app→ app→ = refl

open import Inception.Rewriting.Reduction _→ᶜ_

progress : (σ : CState) → Step? σ
progress ⟨ 𝐖 ； γ ╎ π ╎ ◻ ⟩ = done (λ ())
progress ⟨ 𝐖 ； γ ╎ π ╎ < x ； δ ； π₁ >∷ K ⟩ = next return→
progress ⟨ return V ╎ γ ╎ π ╎ K ⟩ = next eval→
progress ⟨ pm V M ╎ γ ╎ π ╎ K ⟩ = next pmᶜ→
progress ⟨ push M N ╎ γ ╎ π ╎ K ⟩ = next push→
progress ⟨ app V W ╎ γ ╎ π ╎ K ⟩ = next app→
progress ⟨ var V ╎ γ ╎ π ╎ K ⟩ = next var→
progress ⟨ sub M N ╎ γ ╎ π ╎ K ⟩ = next sub→

-- A Normal CState is a halting state and of the form ⟨ 𝐖 ╎ ◻ ⟩.
halting-state :    (σ : CState) → Normal σ
                 → Σ[ Γ ∈ Ctx ] Σ[ π ∈ Γ ⊇ ε ] Σ[ 𝐖 ∈ OMVal Γ ℛ ] Σ[ γ ∈ MEnv Γ ] σ ≡ ⟨ 𝐖 ； γ ╎ π ╎ ◻ ⟩
halting-state ⟨ 𝐖 ； γ ╎ π ╎ ◻ ⟩ normal = _ , π , 𝐖 , γ , refl
halting-state ⟨ 𝐖 ； γ ╎ π ╎ < x ； δ ； π₁ >∷ K ⟩ normal = ql (normal return→) (Σ-syntax Ctx (λ Ψ → Σ-syntax (Ψ ⊇ ε) (λ π₂ → Σ-syntax (OMVal Ψ ℛ) (λ 𝐕 → Σ-syntax (MEnv Ψ) (λ ψ → ⟨ 𝐖 ； γ ╎ π ╎ < x ； δ ； π₁ >∷ K ⟩ ≡ ⟨ 𝐕 ； ψ ╎ π₂ ╎ ◻ ⟩)))))
halting-state ⟨ return W ╎ γ ╎ π ╎ K ⟩ normal = ql (normal eval→) (Σ-syntax Ctx (λ Δ → Σ-syntax (Δ ⊇ ε) (λ π₁ → Σ-syntax (OMVal Δ ℛ) (λ 𝐖 → Σ-syntax (MEnv Δ) (λ δ → ⟨ return W ╎ γ ╎ π ╎ K ⟩ ≡ ⟨ 𝐖 ； δ ╎ π₁ ╎ ◻ ⟩)))))
halting-state ⟨ pm W M ╎ γ ╎ π ╎ K ⟩ normal = ql (normal pmᶜ→) (Σ-syntax Ctx (λ Δ → Σ-syntax (Δ ⊇ ε) (λ π₁ → Σ-syntax (OMVal Δ ℛ) (λ 𝐖 → Σ-syntax (MEnv Δ) (λ δ → ⟨ pm W M ╎ γ ╎ π ╎ K ⟩ ≡ ⟨ 𝐖 ； δ ╎ π₁ ╎ ◻ ⟩)))))
halting-state ⟨ push M N ╎ γ ╎ π ╎ K ⟩ normal = ql (normal push→) (Σ-syntax Ctx (λ Δ → Σ-syntax (Δ ⊇ ε) (λ π₁ → Σ-syntax (OMVal Δ ℛ) (λ 𝐖 → Σ-syntax (MEnv Δ) (λ δ → ⟨ push M N ╎ γ ╎ π ╎ K ⟩ ≡ ⟨ 𝐖 ； δ ╎ π₁ ╎ ◻ ⟩)))))
halting-state ⟨ app V W ╎ γ ╎ π ╎ K ⟩ normal = ql (normal app→) (Σ-syntax Ctx (λ Δ → Σ-syntax (Δ ⊇ ε) (λ π₁ → Σ-syntax (OMVal Δ ℛ) (λ 𝐖 → Σ-syntax (MEnv Δ) (λ δ → ⟨ app V W ╎ γ ╎ π ╎ K ⟩ ≡ ⟨ 𝐖 ； δ ╎ π₁ ╎ ◻ ⟩)))))
halting-state ⟨ var W ╎ γ ╎ π ╎ K ⟩ normal = ql (normal var→) (Σ-syntax Ctx (λ Δ → Σ-syntax (Δ ⊇ ε) (λ π₁ → Σ-syntax (OMVal Δ ℛ) (λ 𝐖 → Σ-syntax (MEnv Δ) (λ δ → ⟨ var W ╎ γ ╎ π ╎ K ⟩ ≡ ⟨ 𝐖 ； δ ╎ π₁ ╎ ◻ ⟩)))))
halting-state ⟨ sub M N ╎ γ ╎ π ╎ K ⟩ normal = ql (normal sub→) (Σ-syntax Ctx (λ Δ → Σ-syntax (Δ ⊇ ε) (λ π₁ → Σ-syntax (OMVal Δ ℛ) (λ 𝐖 → Σ-syntax (MEnv Δ) (λ δ → ⟨ sub M N ╎ γ ╎ π ╎ K ⟩ ≡ ⟨ 𝐖 ； δ ╎ π₁ ╎ ◻ ⟩)))))

\end{code}
