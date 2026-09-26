\begin{code}
{-# OPTIONS --no-postfix-projections #-}

open import Inception.Sub.Syntax using (Ty)

module Inception.Sub.Machine (ℛ : Ty) where

open import Inception.Prelude
open import Inception.Sub.Syntax

open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Unit using (⊤; tt)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

--------------------------------------------------------------------------

infixl 27 _·_

--------------------------------------------------------------------------
-- environments

\end{code}
%<*Env>
\begin{code}

mutual

  data CStack : (X : Ty) → Set where

    ◻ :        CStack ℛ

    <_；_>∷_ :  (Γ ∙ Y) ⊢ᶜ X → (γ : MEnv Γ)
                → (K : CStack X)
                ------------------------------------
                → CStack Y

  data MVal : Ty → Set where

    unitᵛ :
              -------------------
              MVal `𝟙

    pairᵛ :   (𝐕 : MVal X) → (𝐖 : MVal Y)
              -------------------------------------------------
              → MVal (X `× Y)

    cloᵛ :    {Γ : Ctx} → (M : (Γ ∙ X) ⊢ᶜ Y) → (γ : MEnv Γ)
              ----------------------------------------------------
              → MVal (X `⇒ Y)

    jumpᵛ :   {Γ : Ctx} → (M : Γ ⊢ᶜ X) → (γ : MEnv Γ)
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

lookup : Γ ∋ X → MEnv Γ → MVal X
lookup here (γ · 𝐖) = 𝐖
lookup (there i) (γ · 𝐖) = lookup i γ

\end{code}
%</MEnv>
\begin{code}

--------------------------------------------------------------------------
-- value projections

proj₁-val : MVal (X `× Y) → MVal X
proj₁-val (pairᵛ 𝐕 𝐖) = 𝐕

proj₂-val : MVal (X `× Y) → MVal Y
proj₂-val (pairᵛ 𝐕 𝐖) = 𝐖

pair-val : (𝐖 : MVal (X `× Y)) → (pairᵛ (proj₁-val 𝐖) (proj₂-val 𝐖) ≡ 𝐖)
pair-val (pairᵛ 𝐕 𝐖) = refl

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

%<*Eval>
\begin{code}
jump-to-state : MVal `ℓ → CState
jump-to-state (jumpᵛ M γ K) = ⟨ M ╎ γ ╎ K ⟩

clo-to-comp :  MVal (X `⇒ Y)
               → Σ[ Γ ∈ Ctx ] (Γ ∙ X) ⊢ᶜ Y × MEnv Γ
clo-to-comp (cloᵛ M γ) = _ , M , γ

eval : Γ ⊢ᵛ X → MEnv Γ → MVal X
eval (var i) γ = lookup i γ
eval (lam M) γ = cloᵛ M γ
eval (pair V W) γ = pairᵛ (eval V γ) (eval W γ)
eval unit γ = unitᵛ

eval-jump : Γ ⊢ᵛ `ℓ → MEnv Γ → CState
eval-jump W γ = jump-to-state (eval W γ)

eval-clo :  Γ ⊢ᵛ (X `⇒ Y) → Γ ⊢ᵛ X → MEnv Γ
            → CStack Y → CState
eval-clo V W γ K =
  let
    M  = proj₁ (proj₂ (clo-to-comp (eval V γ)))
    γ₁ = proj₂ (proj₂ (clo-to-comp (eval V γ)))
  in
  ⟨ M ╎ γ₁ · eval W γ ╎ K  ⟩

eval₁ : Γ ⊢ᵛ (X `× Y) → MEnv Γ → MVal X
eval₁ W γ = proj₁-val (eval W γ)

eval₂ : Γ ⊢ᵛ (X `× Y) → MEnv Γ → MVal Y
eval₂ W γ = proj₂-val (eval W γ)
\end{code}
%</Eval>
\begin{code}

clo-val : (𝐖 : MVal (X `⇒ Y)) → (cloᵛ (proj₁ (proj₂ (clo-to-comp 𝐖))) (proj₂ (proj₂ (clo-to-comp 𝐖))) ≡ 𝐖)
clo-val (cloᵛ M γ) = refl

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

  sub→ :     {M : (Γ ∙ `ℓ) ⊢ᶜ X} {N : Γ ⊢ᶜ X} {γ : MEnv Γ} {K : CStack X}
             ----------------------------------------------------------------
             →  ⟨ sub M N ╎ γ ╎ K ⟩ →ᶜ ⟨ M ╎ γ · (jumpᵛ N γ K) ╎ K ⟩

  var→ :     {W : Γ ⊢ᵛ `ℓ} {γ : MEnv Γ} {K : CStack X}
             ------------------------------------------
             →  ⟨ var W ╎ γ ╎ K ⟩ →ᶜ eval-jump W γ

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


\end{code}
%<*SubVarSN>
\begin{code}
data SN (σ : CState) : Set where
  sn : (∀ {σ₁} → σ →ᶜ σ₁ → SN σ₁) → SN σ
\end{code}
%</SubVarSN>
\begin{code}

Rᵛ : (X : Ty) → MVal X → Set
Rᵏ : (X : Ty) → CStack X → Set

Rᵛ `𝟙 unitᵛ = ⊤
Rᵛ (X `× Y) (pairᵛ 𝐕 𝐖) = Rᵛ X 𝐕 × Rᵛ Y 𝐖
Rᵛ (X `⇒ Y) (cloᵛ M γ) = ∀ {𝐖 : MVal X} → Rᵛ X 𝐖 → ∀ {K : CStack Y} → Rᵏ Y K → SN ⟨ M ╎ γ · 𝐖 ╎ K ⟩
Rᵛ `ℓ (jumpᵛ M γ K) = SN ⟨ M ╎ γ ╎ K ⟩

Rᵏ X K = ∀ {𝐖 : MVal X} → Rᵛ X 𝐖 → SN ⟨ 𝐖 ╎ K ⟩

Rᴱ : MEnv Γ → Set
Rᴱ {Γ = Γ} γ = ∀ {X : Ty} → (i : Γ ∋ X) → Rᵛ X (lookup i γ)

Rᴱ-ext : {γ : MEnv Γ} {𝐖 : MVal X} → Rᴱ γ → Rᵛ X 𝐖 → Rᴱ (γ · 𝐖)
Rᴱ-ext Rγ RW here = RW
Rᴱ-ext Rγ RW (there i) = Rγ i

rv≡sn : (𝐖 : MVal `ℓ) → Rᵛ `ℓ 𝐖 ≡ SN (jump-to-state 𝐖)
rv≡sn (jumpᵛ _ _ _) = refl

mutual

  fundamentalᵛ  : (W : Γ ⊢ᵛ X) → {γ : MEnv Γ} → Rᴱ γ → Rᵛ X (eval W γ)
  fundamentalᵛ (var i) Rγ = Rγ i
  fundamentalᵛ (lam M) Rγ RW Rk = fundamentalᶜ M (Rᴱ-ext Rγ RW) Rk
  fundamentalᵛ (pair V W) Rγ = (fundamentalᵛ V Rγ) , (fundamentalᵛ W Rγ)
  fundamentalᵛ unit Rγ = tt

  fundamentalᶜ : (M : Γ ⊢ᶜ X) → {γ : MEnv Γ} → Rᴱ γ → {K : CStack X} → Rᵏ X K → SN ⟨ M ╎ γ ╎ K ⟩
  fundamentalᶜ (return W) Rγ Rk = sn λ { eval→ → Rk (fundamentalᵛ W Rγ)}
  fundamentalᶜ (pm W M) {γ = γ} Rγ Rk =
    let
      IH = fundamentalᵛ W Rγ
      𝐖  = eval W γ
      IH₁ : Rᵛ _ (pairᵛ (proj₁-val 𝐖) (proj₂-val 𝐖))
      IH₁ = subst (λ x → Rᵛ _ x) (sym (pair-val 𝐖)) IH
    in
    sn λ { pmᶜ→ → fundamentalᶜ M (Rᴱ-ext (Rᴱ-ext Rγ (proj₁ IH₁)) (proj₂ IH₁)) Rk }
  fundamentalᶜ (push M N) {γ = γ} Rγ {K = K} Rk =
    let
      Rk₁ : Rᵏ _ (< N ； γ >∷ K)
      Rk₁ RW = sn (λ { return→ → fundamentalᶜ N (Rᴱ-ext Rγ RW) Rk })
    in
    sn λ { push→ → fundamentalᶜ M Rγ Rk₁ }
  fundamentalᶜ (app V W) {γ = γ} Rγ {K = K} Rk =
    let
      IH = fundamentalᵛ V Rγ
      𝐕 = eval V γ
      eq = sym (clo-val 𝐕)
      IH₁ = subst (λ x → Rᵛ _ x) eq IH
    in
    sn λ { app→ → IH₁ (fundamentalᵛ W Rγ) Rk }
  fundamentalᶜ (var W) {γ = γ} Rγ Rk = sn λ { var→ → subst (λ x → x) (rv≡sn (eval W γ)) (fundamentalᵛ W Rγ)}
  fundamentalᶜ (sub M N) Rγ Rk = sn λ { sub→ → fundamentalᶜ M (Rᴱ-ext Rγ (fundamentalᶜ N Rγ Rk)) Rk}

Rᴱ-⊘ : Rᴱ ⋄
Rᴱ-⊘ = λ ()

Rᵏ-◻ : Rᵏ ℛ ◻
Rᵏ-◻ RW = sn λ {σ} ()

SN-theorem : (M : ε ⊢ᶜ ℛ) → SN ⟨ M ╎ ⋄ ╎ ◻ ⟩
SN-theorem M = fundamentalᶜ M Rᴱ-⊘ Rᵏ-◻

\end{code}
%<*SubVarNormal>
\begin{code}
-- A CState is Normal, if there are no transitions from it.
Normal : CState → Set
Normal σ = ∀ {σ₁} → σ →ᶜ σ₁ → ⊥
\end{code}
%</SubVarNormal>
\begin{code}

data Progress (σ : CState) : Set where
  done : Normal σ → Progress σ
  step : {σ₁ : CState} → σ →ᶜ σ₁ → Progress σ

progress : (σ : CState) → Progress σ
progress ⟨ 𝐖 ╎ ◻ ⟩ = done (λ ())
progress ⟨ 𝐖 ╎ < M ； γ >∷ K ⟩ = step return→
progress ⟨ return W ╎ γ ╎ K ⟩ = step eval→
progress ⟨ pm W M ╎ γ ╎ K ⟩ = step pmᶜ→
progress ⟨ push M N ╎ γ ╎ K ⟩ = step push→
progress ⟨ app V W ╎ γ ╎ K ⟩ = step app→
progress ⟨ var W ╎ γ ╎ K ⟩ = step var→
progress ⟨ sub M N ╎ γ ╎ K ⟩ = step sub→

\end{code}
%<*SubVarHaltingState>
\begin{code}
-- A Normal CState is a halting state and of the form ⟨ 𝐖 ╎ ◻ ⟩.
halting-state :    (σ : CState) → Normal σ
                 → Σ[ 𝐖 ∈ MVal ℛ ] σ ≡ ⟨ 𝐖 ╎ ◻ ⟩
\end{code}
%</SubVarHaltingState>
\begin{code}

halting-state ⟨ 𝐖 ╎ ◻ ⟩ normal = 𝐖 , refl
halting-state ⟨ 𝐖 ╎ < M ； γ >∷ K ⟩ normal = ql (normal return→) _
halting-state ⟨ return _ ╎ γ ╎ K ⟩ normal = ql (normal eval→) _
halting-state ⟨ pm _ _ ╎ γ ╎ K ⟩ normal = ql (normal pmᶜ→) _
halting-state ⟨ push _ _ ╎ γ ╎ K ⟩ normal = ql (normal push→) _
halting-state ⟨ app _ _ ╎ γ ╎ K ⟩ normal = ql (normal app→) _
halting-state ⟨ var _ ╎ γ ╎ K ⟩ normal = ql (normal var→) _
halting-state ⟨ sub _ _ ╎ γ ╎ K ⟩ normal = ql (normal sub→) _


exec-acc : {σ : CState} → SN σ → Σ[ σ₁ ∈ CState ] Σ[ 𝐖 ∈ MVal ℛ ] Σ[ NF ∈ Normal σ₁ ] (σ →ᶜ* σ₁) × (𝐖 ≡ proj₁ (halting-state σ₁ NF))
exec-acc {σ = σ} (sn f) with progress σ
... | done NF    = σ , proj₁ (halting-state σ NF) , NF , (σ ◼) , refl
... | step s with exec-acc (f s)
...   | (σ₁ , 𝐖 , NF , ss , eq) = σ₁ , 𝐖 , NF , (_ →ᶜ⟨ s ⟩ ss) , eq

\end{code}
%<*SubVarEval>
\begin{code}
exec :    (M : ε ⊢ᶜ ℛ)
        → Σ[ σ ∈ CState ]
          Σ[ 𝐖 ∈ MVal ℛ ]
          Σ[ NF ∈ Normal σ ]
          (⟨ M ╎ ⋄ ╎ ◻ ⟩ →ᶜ* σ) × (𝐖 ≡ proj₁ (halting-state σ NF))
\end{code}
%</SubVarEval>
\begin{code}

exec M = exec-acc (SN-theorem M)

\end{code}
