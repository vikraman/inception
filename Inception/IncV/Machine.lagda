\begin{code}

{-# OPTIONS --no-postfix-projections #-}

open import Inception.IncV.Data

import Inception.IncV.Syntax as Syntax using (Ty)

module Inception.IncV.Machine (𝒜 : Alg) (ℝ : Syntax.Ty 𝒜) where

open import Inception.IncV.Syntax 𝒜
open import Inception.Prelude
open import Inception.Rewriting

open import Data.Empty using (⊥)
open import Data.Nat
open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Unit using (⊤; tt)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

--------------------------------------------------------------------------

infixl 27 <_；_>∷_
infixl 27 _·_

--------------------------------------------------------------------------
-- environments

\end{code}
%<*MEnv>
\begin{code}

mutual

  data CStack : (X : Ty) → Set where

    ◻ :        CStack ℝ

    <_；_>∷_ :  (Γ ∙ Y) ⊢ᶜ X → (γ : MEnv Γ)
                → (K : CStack X)
                ------------------------------------
                → CStack Y

  data MVal : Ty → Set where

    unitᵛ :
              -------------------
              MVal `𝟙

    datᵛ :    (N : 𝒟)
              -------------------
              → MVal `𝓅

    pairᵛ :   (𝐕 : MVal X) → (𝐖 : MVal Y)
              -------------------------------------------------
              → MVal (X `× Y)

    cloᵛ :    {Γ : Ctx} → (M : (Γ ∙ X) ⊢ᶜ Y) → (γ : MEnv Γ)
              ----------------------------------------------------
              → MVal (X `⇒ Y)

    jumpᵛ :   {Γ : Ctx} → (M : (Γ ∙ `𝓅) ⊢ᶜ X) → (γ : MEnv Γ)
              → (K : CStack X)
              -----------------------------------------------
              → MVal `ℓ

  data MEnv : Ctx → Set where

    ⋄ :
           --------------
           MEnv ε

    _·_ :  MEnv Γ → MVal X
           ----------------------------------
           → MEnv (Γ ∙ X)

\end{code}
%</MEnv>
\begin{code}

lookup : (i : Γ ∋ X) → MEnv Γ → MVal X
lookup here (γ · 𝐖) = 𝐖
lookup (there i) (γ · 𝐖) = lookup i γ

--------------------------------------------------------------------------
-- value projections

proj₁-val : MVal (X `× Y) → MVal X
proj₁-val (pairᵛ 𝐕 𝐖) = 𝐕

proj₂-val : MVal (X `× Y) → MVal Y
proj₂-val (pairᵛ 𝐕 𝐖) = 𝐖

pairᵛ-η : (𝐖 : MVal (X `× Y)) → (pairᵛ (proj₁-val 𝐖) (proj₂-val 𝐖) ≡ 𝐖)
pairᵛ-η (pairᵛ 𝐕 𝐖) = refl

--------------------------------------------------------------------------
-- machine for effectful terms / computations

\end{code}
%<*CStates>
\begin{code}

data CState : Set where

  ⟨_╎_⟩ :    (𝐖 : MVal X) → (K : CStack X)
             ---------------------------------------------------
             → CState

  ⟨_╎_╎_⟩ :  (M : Γ ⊢ᶜ X) → (γ : MEnv Γ) → (K : CStack X)
             -----------------------------------------------------------------
             → CState

\end{code}
%</CStates>
\begin{code}

eval : Γ ⊢ᵛ X → MEnv Γ → MVal X
eval (var i) γ = lookup i γ
eval (lam M) γ = cloᵛ M γ
eval (pair V W) γ = pairᵛ (eval V γ) (eval W γ)
eval unit γ = unitᵛ
eval (dat N) γ = datᵛ N
eval (op o a) γ = datᵛ (apply o a)

jump-to-state : MVal `ℓ → MVal `𝓅 → CState
jump-to-state (jumpᵛ M γ K) 𝐖 = ⟨ M ╎ γ · 𝐖 ╎ K ⟩

clo-to-comp : MVal (X `⇒ Y) → Σ[ Γ ∈ Ctx ] (Γ ∙ X) ⊢ᶜ Y × MEnv Γ
clo-to-comp (cloᵛ M γ) = _ , M , γ

cloᵛ-η : (𝐖 : MVal (X `⇒ Y)) → (cloᵛ (proj₁ (proj₂ (clo-to-comp 𝐖))) (proj₂ (proj₂ (clo-to-comp 𝐖))) ≡ 𝐖)
cloᵛ-η (cloᵛ M γ) = refl

eval-jump : Γ ⊢ᵛ `ℓ → Γ ⊢ᵛ `𝓅 → MEnv Γ → CState
eval-jump V W γ = jump-to-state (eval V γ) (eval W γ)

eval-clo : Γ ⊢ᵛ (X `⇒ Y) → Γ ⊢ᵛ X → MEnv Γ → CStack Y → CState
eval-clo V W γ K = ⟨ proj₁ (proj₂ (clo-to-comp (eval V γ))) ╎ proj₂ (proj₂ (clo-to-comp (eval V γ))) · eval W γ ╎ K ⟩

eval₁ : Γ ⊢ᵛ (X `× Y) → MEnv Γ → MVal X
eval₁ W γ = proj₁-val (eval W γ)

eval₂ : Γ ⊢ᵛ (X `× Y) → MEnv Γ → MVal Y
eval₂ W γ = proj₂-val (eval W γ)

\end{code}
%<*CTrans>
\begin{code}

data _→ᶜ_ : CState → CState → Set where

  eval→ :    {W : Γ ⊢ᵛ X} {γ : MEnv Γ} {K : CStack X}
             -------------------------------------------
             →  ⟨ return W ╎ γ ╎ K ⟩ →ᶜ ⟨ eval W γ ╎ K ⟩

  return→ :  {𝐖 : MVal X} {M : (Γ ∙ X) ⊢ᶜ Y} {γ : MEnv Γ} {K : CStack Y}
             --------------------------------------------------------------
             →  ⟨ 𝐖 ╎ < M ； γ >∷ K ⟩ →ᶜ ⟨ M ╎ γ · 𝐖 ╎ K ⟩

  push→ :    {M : Γ ⊢ᶜ X} {N : (Γ ∙ X) ⊢ᶜ Y} {γ : MEnv Γ} {K : CStack Y}
             ----------------------------------------------------------------
             →  ⟨ push M N ╎ γ ╎ K ⟩ →ᶜ ⟨ M ╎ γ ╎ < N ； γ >∷ K ⟩

  inc→ :     {M : (Γ ∙ `ℓ) ⊢ᶜ X} {N : (Γ ∙ `𝓅) ⊢ᶜ X} {γ : MEnv Γ} {K : CStack X}
             ----------------------------------------------------------------
             →  ⟨ inc M N ╎ γ ╎ K ⟩ →ᶜ ⟨ M ╎ γ · (jumpᵛ N γ K) ╎ K ⟩

  rec→ :     {V : Γ ⊢ᵛ `ℓ} {W : Γ ⊢ᵛ `𝓅} {γ : MEnv Γ} {K : CStack X}
             -------------------------------------------------------
             →  ⟨ rec V W ╎ γ ╎ K ⟩ →ᶜ eval-jump V W γ

  pmᶜ→ :     {W : Γ ⊢ᵛ (X `× Y)} {γ : MEnv Γ}
             {M : (Γ ∙ X ∙ Y) ⊢ᶜ Z} {K : CStack Z}
             -------------------------------------------------------------
             →  ⟨ pm W M ╎ γ ╎ K ⟩ →ᶜ ⟨ M ╎ γ · eval₁ W γ · eval₂ W γ ╎ K ⟩

  app→ :     {V : Γ ⊢ᵛ (X `⇒ Y)} {W : Γ ⊢ᵛ X} {γ : MEnv Γ} {K : CStack Y}
             ----------------------------------------------------------------
             →  ⟨ app V W ╎ γ ╎ K ⟩ →ᶜ eval-clo V W γ K

\end{code}
%</CTrans>
\begin{code}

determinismꟲ : {σ σ₁ : CState} (s₁ s₂ : σ →ᶜ σ₁) → (s₁ ≡ s₂)
determinismꟲ eval→ eval→ = refl
determinismꟲ return→ return→ = refl
determinismꟲ push→ push→ = refl
determinismꟲ inc→ inc→ = refl
determinismꟲ rec→ rec→ = refl
determinismꟲ pmᶜ→ pmᶜ→ = refl
determinismꟲ app→ app→ = refl

open Reduction _→ᶜ_ public
  renaming (_~>*_ to _→ᶜ*_)


Rᵛ : (X : Ty) → MVal X → Set
Rᵏ : (X : Ty) → CStack X → Set

Rᵛ `𝟙 unitᵛ = ⊤
Rᵛ (X `× Y) (pairᵛ 𝐕 𝐖) = Rᵛ X 𝐕 × Rᵛ Y 𝐖
Rᵛ (X `⇒ Y) (cloᵛ M γ) = ∀ {𝐖 : MVal X} → Rᵛ X 𝐖 → ∀ {K : CStack Y} → Rᵏ Y K → SN ⟨ M ╎ γ · 𝐖 ╎ K ⟩
Rᵛ `ℓ (jumpᵛ M γ K) = ∀ {𝐖 : MVal `𝓅} → SN ⟨ M ╎ γ · 𝐖 ╎ K ⟩
Rᵛ `𝓅 (datᵛ N) = ⊤

Rᵏ X K = ∀ {𝐖 : MVal X} → Rᵛ X 𝐖 → SN ⟨ 𝐖 ╎ K ⟩

Rᴱ : MEnv Γ → Set
Rᴱ {Γ = Γ} γ = ∀ {X : Ty} → (i : Γ ∋ X) → Rᵛ X (lookup i γ)

Rᴱ-ext : {γ : MEnv Γ} {𝐖 : MVal X} → Rᴱ γ → Rᵛ X 𝐖 → Rᴱ (γ · 𝐖)
Rᴱ-ext Rγ RW here = RW
Rᴱ-ext Rγ RW (there i) = Rγ i

rv≡sn : (𝐖 : MVal `ℓ) → Rᵛ `ℓ 𝐖 ≡ (∀ {𝐕 : MVal `𝓅} → SN (jump-to-state 𝐖 𝐕))
rv≡sn (jumpᵛ _ _ _) = refl

mutual

  fundamentalᵛ  : (W : Γ ⊢ᵛ X) → {γ : MEnv Γ} → Rᴱ γ → Rᵛ X (eval W γ)
  fundamentalᵛ (var i) Rγ = Rγ i
  fundamentalᵛ (lam M) Rγ RW Rk = fundamentalᶜ M (Rᴱ-ext Rγ RW) Rk
  fundamentalᵛ (pair V W) Rγ = (fundamentalᵛ V Rγ) , (fundamentalᵛ W Rγ)
  fundamentalᵛ unit Rγ = tt
  fundamentalᵛ (dat N) Rγ = tt
  fundamentalᵛ (op o a) Rγ = tt

  fundamentalᶜ : (M : Γ ⊢ᶜ X) → {γ : MEnv Γ} → Rᴱ γ → {K : CStack X} → Rᵏ X K → SN ⟨ M ╎ γ ╎ K ⟩
  fundamentalᶜ (return W) Rγ Rk = sn λ { eval→ → Rk (fundamentalᵛ W Rγ)}
  fundamentalᶜ (pm W M) {γ = γ} Rγ Rk =
    sn λ { pmᶜ→ → fundamentalᶜ M (Rᴱ-ext (Rᴱ-ext Rγ (proj₁ IH₁)) (proj₂ IH₁)) Rk }
    where
      IH = fundamentalᵛ W Rγ
      𝐖  = eval W γ
      IH₁ : Rᵛ _ (pairᵛ (proj₁-val 𝐖) (proj₂-val 𝐖))
      IH₁ = subst (λ x → Rᵛ _ x) (sym (pairᵛ-η 𝐖)) IH
  fundamentalᶜ (push M N) {γ = γ} Rγ {K = K} Rk =
    sn λ { push→ → fundamentalᶜ M Rγ Rk₁ }
    where
      Rk₁ : Rᵏ _ (< N ； γ >∷ K)
      Rk₁ RW = sn (λ { return→ → fundamentalᶜ N (Rᴱ-ext Rγ RW) Rk })
  fundamentalᶜ (app V W) {γ = γ} Rγ {K = K} Rk =
    sn λ { app→ → IH₁ (fundamentalᵛ W Rγ) Rk }
    where
      IH = fundamentalᵛ V Rγ
      𝐕 = eval V γ
      eq = sym (cloᵛ-η 𝐕)
      IH₁ = subst (λ x → Rᵛ _ x) eq IH
  fundamentalᶜ (rec V W) {γ = γ} Rγ Rk = sn λ { rec→ → subst (λ x → x) (rv≡sn (eval V γ)) (fundamentalᵛ V Rγ)}
  fundamentalᶜ (inc M N) Rγ Rk =
    sn λ { inc→ → fundamentalᶜ M (Rᴱ-ext Rγ (λ { {datᵛ n} → fundamentalᶜ N (Rᴱ-ext {𝐖 = datᵛ n} Rγ tt) Rk })) Rk }

Rᴱ-⊘ : Rᴱ ⋄
Rᴱ-⊘ = λ ()

Rᵏ-◻ : Rᵏ ℝ ◻
Rᵏ-◻ RW = sn λ {σ} ()

SN-theorem : (M : ε ⊢ᶜ ℝ) → SN ⟨ M ╎ ⋄ ╎ ◻ ⟩
SN-theorem M = fundamentalᶜ M Rᴱ-⊘ Rᵏ-◻

progress : (σ : CState) → Step? σ
progress ⟨ 𝐖 ╎ ◻ ⟩ = done (λ ())
progress ⟨ 𝐖 ╎ < M ； γ >∷ K ⟩ = next return→
progress ⟨ return W ╎ γ ╎ K ⟩ = next eval→
progress ⟨ pm W M ╎ γ ╎ K ⟩ = next pmᶜ→
progress ⟨ push M N ╎ γ ╎ K ⟩ = next push→
progress ⟨ app V W ╎ γ ╎ K ⟩ = next app→
progress ⟨ rec V W ╎ γ ╎ K ⟩ = next rec→
progress ⟨ inc M N ╎ γ ╎ K ⟩ = next inc→

halting-state : (σ : CState) → Normal σ → Σ[ 𝐖 ∈ MVal ℝ ] σ ≡ ⟨ 𝐖 ╎ ◻ ⟩
halting-state ⟨ 𝐖 ╎ ◻ ⟩ normal = 𝐖 , refl
halting-state ⟨ 𝐖 ╎ < M ； γ >∷ K ⟩ normal = ql (normal return→) _
halting-state ⟨ return _ ╎ γ ╎ K ⟩ normal = ql (normal eval→) _
halting-state ⟨ pm _ _ ╎ γ ╎ K ⟩ normal = ql (normal pmᶜ→) _
halting-state ⟨ push _ _ ╎ γ ╎ K ⟩ normal = ql (normal push→) _
halting-state ⟨ app _ _ ╎ γ ╎ K ⟩ normal = ql (normal app→) _
halting-state ⟨ rec _ _ ╎ γ ╎ K ⟩ normal = ql (normal rec→) _
halting-state ⟨ inc _ _ ╎ γ ╎ K ⟩ normal = ql (normal inc→) _


exec : (M : ε ⊢ᶜ ℝ) → Σ[ σ ∈ CState ] Σ[ 𝐖 ∈ MVal ℝ ] Σ[ NF ∈ Normal σ ] (⟨ M ╎ ⋄ ╎ ◻ ⟩ →ᶜ* σ) × (𝐖 ≡ proj₁ (halting-state σ NF))
exec M with eval-acc progress (SN-theorem M)
... | (σ , ss , NF) = σ , proj₁ (halting-state σ NF) , NF , ss , refl

\end{code}
