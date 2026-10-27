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

-- currently not used; would have to figure out eval for pairs when doing this
lookup' : Γ ∋ X → MEnv Γ → Σ[ Γ' ∈ Ctx ] (MEnv Γ' × MClo Γ' X)
lookup' here (γ · 𝐖) = _ , γ , 𝐖
lookup' here (γ ·﹝ 𝐖 ╎ π ╎ K ﹞) = _ , γ ·﹝ 𝐖 ╎ π ╎ K ﹞ , label here
lookup' (there x) (γ · 𝐖) = lookup' x γ
lookup' (there x) (γ ·﹝ 𝐖 ╎ π ╎ K ﹞) = lookup' x γ

lookup-label : Γ ∋ `ℓ → MEnv Γ → CState
lookup-label here (γ · label x) = lookup-label x γ
lookup-label here (γ ·﹝ M ╎ π ╎ K ﹞) = ⟨ M ╎ γ ╎ π ╎ K ⟩
lookup-label (there x) (γ · 𝐖) = lookup-label x γ
lookup-label (there x) (γ ·﹝ M ╎ π ╎ stack ﹞) = lookup-label x γ

lam-to-comp :  MClo Γ (X `⇒ Y) → Comp (Γ ∙ X) Y
lam-to-comp (lam M) = M

eval : Val Γ X → MEnv Γ → MClo Γ X
eval (var i) γ = lookup i γ
eval (lam M) γ = lam M
eval (pair V W) γ = pair (eval V γ) (eval W γ)
eval unit γ = unit

eval-jump : Val Γ `ℓ → MEnv Γ → CState
eval-jump (var i) γ = lookup-label i γ

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

data SN (σ : CState) : Set where
  sn : (∀ {σ₁} → σ →ᶜ σ₁ → SN σ₁) → SN σ

Rᵛ : (X : Ty) → MClo Γ X → MEnv Γ → Set
Rᵏ : (X : Ty) → CStack Γ X → Set
Rᴱ : MEnv Γ → Set

Rᵛ `𝟙 unit γ = ⊤
Rᵛ (X `× Y) (pair 𝐕 𝐖) γ = Rᵛ X 𝐕 γ × Rᵛ Y 𝐖 γ
Rᵛ {Γ = Γ} (X `⇒ Y) (lam M) γ =
            ∀ {Δ : Ctx} (π₁ : Wk Δ Γ)
              (𝐖 : MClo Δ X) (δ : MEnv Δ)
              {Ψ : Ctx} (π₂ : Wk Δ Ψ)
            → Rᵛ X 𝐖 δ → {K : CStack Ψ Y} → Rᵏ Y K
            → SN ⟨ wk-comp (wk-cong π₁) M ╎ δ · 𝐖 ╎ wk-wk π₂ ╎ K ⟩
Rᵛ `ℓ (label x) γ = SN (lookup-label x γ)

Rᴱ {Γ = Γ} γ = ∀ {X : Ty} → (i : Γ ∋ X) → Rᵛ X (lookup i γ) γ

Rᵏ {Γ = Γ} X K = ∀ {Δ : Ctx} {𝐖 : MClo Δ X} {δ : MEnv Δ} {π : Wk Δ Γ} → Rᵛ X 𝐖 δ → SN ⟨ 𝐖 ； δ ╎ π ╎ K ⟩

{-
Rᵛ-wk : {Δ : Ctx} {π : Wk Δ Γ} {γ : MEnv Γ} {𝐖 : MClo Γ X}
        → (δ : MEnv Δ) → Rᵛ X 𝐖 γ → Rᵛ X (wk-mclo π 𝐖) δ
Rᵛ-wk {𝐖 = unit} _ Rv = tt
Rᵛ-wk {π = π} {𝐖 = pair 𝐖 𝐕} δ (fst , snd) =
  let
    RW = Rᵛ-wk {π = π} δ fst
    RV = Rᵛ-wk {π = π} δ snd
  in
  RW , RV
Rᵛ-wk {𝐖 = lam M} δ Rv = λ π₁ 𝐖 δ₁ π₂ x x₁ → {!!}
Rᵛ-wk {𝐖 = label x} δ Rv =
  {!subst () !}

Rᴱ-ext : {γ : MEnv Γ} {𝐖 : MClo Γ X} → Rᴱ γ → Rᵛ X 𝐖 γ → Rᴱ (γ · 𝐖)
Rᴱ-ext Rγ RW here = {!!}
Rᴱ-ext Rγ RW (there i) = {!!}
-}

mutual

  fundamentalᵛ  : (W : Γ ⊢ᵛ X) → {Δ : Ctx} → {δ : MEnv Δ} → Rᴱ δ
                 → (π : Wk Δ Γ)
                 → Rᵛ X (eval (wk-val π W) δ) δ
  fundamentalᵛ (var i) Rδ π = Rδ (wk-mem π i)
  fundamentalᵛ (lam M) Rδ π π₁ 𝐖 δ₁ π₂ Rv Rk = fundamentalᶜ M {!!} (wk-trans (Wk.wk-cong π₁) (Wk.wk-cong π)) (wk-wk π₂) Rk
  fundamentalᵛ (pair V W) Rδ π = (fundamentalᵛ V Rδ π) , (fundamentalᵛ W Rδ π)
  fundamentalᵛ unit Rδ π = tt

  fundamentalᶜ : (M : Γ ⊢ᶜ X) → {Δ : Ctx} → {δ : MEnv Δ} → Rᴱ δ
                 → (π₁ : Wk Δ Γ)
                 → {Ψ : Ctx} → (π₂ : Wk Δ Ψ)
                 → {K : CStack Ψ X} → Rᵏ X K
                 → SN ⟨ wk-comp π₁ M ╎ δ ╎ π₂ ╎ K ⟩
  fundamentalᶜ (return W) Rδ π₁ π₂ Rk = sn (λ { eval→ → Rk (fundamentalᵛ W Rδ π₁) })
  fundamentalᶜ (pm W M) Rδ π₁ π₂ Rk = sn (λ { pmᶜ→ → {!!} })
  fundamentalᶜ (push M N) Rδ π₁ π₂ Rk = sn (λ { push→ →
                                                fundamentalᶜ M {!!} π₁ wk-id {!!} })
  fundamentalᶜ (app V W) Rδ π₁ π₂ Rk = sn (λ { app→ → {!!} })
  fundamentalᶜ (var W) Rδ π₁ π₂ Rk = sn (λ { var→ → {!!} })
  fundamentalᶜ (sub M N) Rδ π₁ π₂ Rk = sn (λ { sub→ → {!!} })

{-
  fundamentalᶜ : (M : Γ ⊢ᶜ X) → {γ : MEnv Γ} → Rᴱ γ → {Ψ : Ctx}
                 → {K : CStack Ψ X} → Rᵏ X K → (π : Wk Γ Ψ) → SN ⟨ M ╎ γ ╎ π ╎ K ⟩
  fundamentalᶜ (return W) Rγ Rk π = sn (λ {eval→ → Rk (fundamentalᵛ W Rγ)})
  fundamentalᶜ (pm W M) Rγ Rk π = sn (λ { pmᶜ→ → fundamentalᶜ M {!!} Rk (wk-wk (wk-wk π))})
  fundamentalᶜ (push M N) Rγ Rk π = sn (λ { push→ → fundamentalᶜ {!!} {!!} {!!} {!!}})
  fundamentalᶜ (app W V) Rγ Rk π = sn (λ { app→ → {!!}})
  fundamentalᶜ (var W) Rγ Rk π = sn λ { var→ → {!!}}
  fundamentalᶜ (sub M N) Rγ Rk π = sn λ { sub→ → {!!}}
-}

open import Inception.Rewriting.Reduction _→ᶜ_

progress : (σ : CState) → Step? σ
progress ⟨ 𝐖 ； γ ╎ π ╎ ◻ ⟩ = done (λ ())
progress ⟨ 𝐖 ； γ ╎ π ╎ < x ； γ₁ ； π₁ >∷ K ⟩ = next return→
progress ⟨ return x ╎ γ ╎ π ╎ K ⟩ = next eval→
progress ⟨ pm x M ╎ γ ╎ π ╎ K ⟩ = next pmᶜ→
progress ⟨ push M M₁ ╎ γ ╎ π ╎ K ⟩ = next push→
progress ⟨ app x x₁ ╎ γ ╎ π ╎ K ⟩ = next app→
progress ⟨ var x ╎ γ ╎ π ╎ K ⟩ = next var→
progress ⟨ sub M M₁ ╎ γ ╎ π ╎ K ⟩ = next sub→

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
