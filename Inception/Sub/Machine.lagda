\begin{code}
{-# OPTIONS --no-postfix-projections #-}

open import Inception.Sub.Syntax using (Ty)

module Inception.Sub.Machine (ℛ : Ty) where

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

  data MVal : Ty → Set where

    unitᵛ :
              -------------------
              MVal `𝟙

    pairᵛ :   (𝐖₁ : MVal X₁) → (𝐖₂ : MVal X₂)
              -------------------------------------------------
              → MVal (X₁ `× X₂)

    cloᵛ :    {Γ : Ctx} → (M : Comp (Γ ∙ X) Y) → (γ : MEnv Γ)
              ----------------------------------------------------
              → MVal (X `⇒ Y)

    jumpᵛ :   {Γ : Ctx} → (M : Comp Γ X) → (γ : MEnv Γ)
              → (cs : CStack X)
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
lookup (there x) (γ · 𝐖) = lookup x γ

\end{code}
%</MEnv>
\begin{code}

---------------------------------------------------------------------------------
-- VALUE PROJECTIONS

proj₁-val : MVal (X `× Y) → MVal X
proj₁-val (pairᵛ W₁ W₂) = W₁

proj₂-val : MVal (X `× Y) → MVal Y
proj₂-val (pairᵛ W₁ W₂) = W₂

pair-val : (W : MVal (X `× Y)) → (pairᵛ (proj₁-val W) (proj₂-val W) ≡ W)
pair-val (pairᵛ W₁ W₂) = refl

---------------------------------------------------------------------------------
-- MACHINE FOR EFFECTFUL TERMS / COMPUTATIONS

\end{code}
%<*CStates>
\begin{code}

data CState : Set where

  ⟨_╎_⟩ :    (𝐖 : MVal X) → (cstack : CStack X)
             ---------------------------------------------------
             → CState

  ⟨_╎_╎_⟩ :  (M : Comp Γ X) → (γ : MEnv Γ) → (cstack : CStack X)
             -----------------------------------------------------------------
             → CState

\end{code}
%</CStates>

%<*Eval>
\begin{code}
jump-to-state : MVal `ℓ → CState
jump-to-state (jumpᵛ M γ k) = ⟨ M ╎ γ ╎ k ⟩

clo-to-comp :  MVal (X `⇒ Y)
               → Σ[ Γ ∈ Ctx ] Comp (Γ ∙ X) Y × MEnv Γ
clo-to-comp (cloᵛ M γ) = _ , M , γ

eval : Val Γ X → MEnv Γ → MVal X
eval (var i) γ = lookup i γ
eval (lam M) γ = cloᵛ M γ
eval (pair W₁ W₂) γ = pairᵛ (eval W₁ γ) (eval W₂ γ)
eval unit γ = unitᵛ

eval-jump : Val Γ `ℓ → MEnv Γ → CState
eval-jump W γ = jump-to-state (eval W γ)

eval-clo :  Val Γ (X `⇒ Y) → Val Γ X → MEnv Γ
            → CStack Y → CState
eval-clo W₁ W₂ γ k =
  let
    M  = proj₁ (proj₂ (clo-to-comp (eval W₁ γ)))
    γ' = proj₂ (proj₂ (clo-to-comp (eval W₁ γ)))
  in
  ⟨ M ╎ γ' · eval W₂ γ ╎ k  ⟩

eval₁ : Val Γ (X₁ `× X₂) → MEnv Γ → MVal X₁
eval₁ W γ = proj₁-val (eval W γ)

eval₂ : Val Γ (X₁ `× X₂) → MEnv Γ → MVal X₂
eval₂ W γ = proj₂-val (eval W γ)
\end{code}
%</Eval>
\begin{code}

clo-val : (W : MVal (X `⇒ Y)) → (cloᵛ (proj₁ (proj₂ (clo-to-comp W))) (proj₂ (proj₂ (clo-to-comp W))) ≡ W)
clo-val (cloᵛ M γ) = refl

\end{code}

%<*CTrans>
\begin{code}

data _→ᶜ_ : CState → CState → Set where

  eval→ :    {W : Val Γ X} {γ : MEnv Γ} {cstack : CStack X}
             -------------------------------------------
             →  ⟨ return W ╎ γ ╎ cstack ⟩ →ᶜ ⟨ eval W γ ╎ cstack ⟩

  return→ :  {𝐖 : MVal X} {M : Comp (Γ ∙ X) Y} {γ : MEnv Γ} {cstack : CStack Y}
             --------------------------------------------------------------
             →  ⟨ 𝐖 ╎ < M ； γ >∷ cstack ⟩ →ᶜ ⟨ M ╎ γ · 𝐖 ╎ cstack ⟩

  push→ :    {M₁ : Comp Γ X} {M₂ : Comp (Γ ∙ X) Y} {γ : MEnv Γ} {cstack : CStack Y}
             ----------------------------------------------------------------
             →  ⟨ push M₁ M₂ ╎ γ ╎ cstack ⟩ →ᶜ ⟨ M₁ ╎ γ ╎ < M₂ ； γ >∷ cstack ⟩

  sub→ :     {M₁ : Comp (Γ ∙ `ℓ) X} {M₂ : Comp Γ X} {γ : MEnv Γ} {cstack : CStack X}
             ----------------------------------------------------------------
             →  ⟨ sub M₁ M₂ ╎ γ ╎ cstack ⟩ →ᶜ ⟨ M₁ ╎ γ · (jumpᵛ M₂ γ cstack) ╎ cstack ⟩

  var→ :     {W : Val Γ `ℓ} {γ : MEnv Γ} {cstack : CStack X}
             ------------------------------------------
             →  ⟨ var W ╎ γ ╎ cstack ⟩ →ᶜ eval-jump W γ

  pmᶜ→ :     {W : Val Γ (X `× Y)} {γ : MEnv Γ}
             {M : Comp (Γ ∙ X ∙ Y) Z} {cstack : CStack Z}
             -------------------------------------------------------------
             →  ⟨ pm W M ╎ γ ╎ cstack ⟩ →ᶜ ⟨ M ╎ γ · eval₁ W γ · eval₂ W γ ╎ cstack ⟩

  app→ :     {W₁ : Val Γ (X `⇒ Y)} {W₂ : Val Γ X} {γ : MEnv Γ} {cstack : CStack Y}
             ----------------------------------------------------------------
             →  ⟨ app W₁ W₂ ╎ γ ╎ cstack ⟩ →ᶜ eval-clo W₁ W₂ γ cstack

\end{code}
%</CTrans>
\begin{code}


determinismꟲ : {S S' : CState} (S→S'₁ S→S'₂ : S →ᶜ S') → (S→S'₁ ≡ S→S'₂)
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

_⨾ᶜ_ : {F S T : CState} → (F →ᶜ* S) → (S →ᶜ* T) → (F →ᶜ* T)
_⨾ᶜ_ (S ◼) S>>T = S>>T
_⨾ᶜ_ (F →ᶜ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᶜ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ᶜ S₂>>T)


\end{code}
%<*SubVarSN>
\begin{code}
data SN (σ : CState) : Set where
  sn : (∀ {σ'} → σ →ᶜ σ' → SN σ') → SN σ
\end{code}
%</SubVarSN>
\begin{code}

Rᵛ : (X : Ty) → MVal X → Set
Rᵏ : (X : Ty) → CStack X → Set

Rᵛ `𝟙 unitᵛ = ⊤
Rᵛ (X `× Y) (pairᵛ W₁ W₂) = Rᵛ X W₁ × Rᵛ Y W₂
Rᵛ (X `⇒ Y) (cloᵛ M γ) = ∀ {W' : MVal X} → Rᵛ X W' → ∀ {cstack : CStack Y} → Rᵏ Y cstack → SN ⟨ M ╎ γ · W' ╎ cstack ⟩
Rᵛ `ℓ (jumpᵛ M γ cstack) = SN ⟨ M ╎ γ ╎ cstack ⟩

Rᵏ X cstack = ∀ {W : MVal X} → Rᵛ X W → SN ⟨ W ╎ cstack ⟩

Rᴱ : MEnv Γ → Set
Rᴱ {Γ = Γ} γ = ∀ {X : Ty} → (i : Γ ∋ X) → Rᵛ X (lookup i γ)

Rᴱ-ext : {γ : MEnv Γ} {W : MVal X} → Rᴱ γ → Rᵛ X W → Rᴱ (γ · W)
Rᴱ-ext Rγ RW here = RW
Rᴱ-ext Rγ RW (there i) = Rγ i

rv≡sn : (𝐖 : MVal `ℓ) → Rᵛ `ℓ 𝐖 ≡ SN (jump-to-state 𝐖)
rv≡sn (jumpᵛ _ _ _) = refl

mutual

  fundamentalᵛ  : (W : Val Γ X) → {γ : MEnv Γ} → Rᴱ γ → Rᵛ X (eval W γ)
  fundamentalᵛ (var i) Rγ = Rγ i
  fundamentalᵛ (lam M) Rγ RW Rk = fundamentalᶜ M (Rᴱ-ext Rγ RW) Rk
  fundamentalᵛ (pair W₁ W₂) Rγ = (fundamentalᵛ W₁ Rγ) , (fundamentalᵛ W₂ Rγ)
  fundamentalᵛ unit Rγ = tt

  fundamentalᶜ : (M : Comp Γ X) → {γ : MEnv Γ} → Rᴱ γ → {cstack : CStack X} → Rᵏ X cstack → SN ⟨ M ╎ γ ╎ cstack ⟩
  fundamentalᶜ (return W) Rγ Rk = sn λ { eval→ → Rk (fundamentalᵛ W Rγ)}
  fundamentalᶜ (pm W M) {γ = γ} Rγ Rk =
    let
      IH = fundamentalᵛ W Rγ
      W' = eval W γ
      IH' : Rᵛ _ (pairᵛ (proj₁-val W') (proj₂-val W'))
      IH' = subst (λ x → Rᵛ _ x) (sym (pair-val W')) IH
    in
    sn λ { pmᶜ→ → fundamentalᶜ M (Rᴱ-ext (Rᴱ-ext Rγ (proj₁ IH')) (proj₂ IH')) Rk }
  fundamentalᶜ (push M₁ M₂) {γ = γ} Rγ {cstack = k} Rk =
    let
      Rk' : Rᵏ _ (< M₂ ； γ >∷ k)
      Rk' RW = sn (λ { return→ → fundamentalᶜ M₂ (Rᴱ-ext Rγ RW) Rk })
    in
    sn λ { push→ → fundamentalᶜ M₁ Rγ Rk' }
  fundamentalᶜ (app W₁ W₂) {γ = γ} Rγ {cstack = k} Rk =
    let
      IH = fundamentalᵛ W₁ Rγ
      W₁' = eval W₁ γ
      eq = sym (clo-val W₁')
      IH' = subst (λ x → Rᵛ _ x) eq IH
    in
    sn λ { app→ → IH' (fundamentalᵛ W₂ Rγ) Rk }
  fundamentalᶜ (var W) {γ = γ} Rγ Rk = sn λ { var→ → subst (λ x → x) (rv≡sn (eval W γ)) (fundamentalᵛ W Rγ)}
  fundamentalᶜ (sub M₁ M₂) Rγ Rk = sn λ { sub→ → fundamentalᶜ M₁ (Rᴱ-ext Rγ (fundamentalᶜ M₂ Rγ Rk)) Rk}

Rᴱ-⊘ : Rᴱ ⋄
Rᴱ-⊘ = λ ()

Rᵏ-◻ : Rᵏ ℛ ◻
Rᵏ-◻ RW = sn λ {σ'} ()

SN-theorem : (M : Comp ε ℛ) → SN ⟨ M ╎ ⋄ ╎ ◻ ⟩
SN-theorem M = fundamentalᶜ M Rᴱ-⊘ Rᵏ-◻

\end{code}
%<*SubVarNormal>
\begin{code}
-- A CState is Normal, if there are no transitions from it.
Normal : CState → Set
Normal cstate₁ = ∀ {cstate₂} → cstate₁ →ᶜ cstate₂ → ⊥
\end{code}
%</SubVarNormal>
\begin{code}

data Progress (σ : CState) : Set where
  done : Normal σ → Progress σ
  step : {σ' : CState} → σ →ᶜ σ' → Progress σ

progress : (σ : CState) → Progress σ
progress ⟨ W' ╎ ◻ ⟩ = done (λ ())
progress ⟨ W' ╎ < M ； γ >∷ cstack ⟩ = step return→
progress ⟨ return W ╎ γ ╎ cstack ⟩ = step eval→
progress ⟨ pm W M ╎ γ ╎ cstack ⟩ = step pmᶜ→
progress ⟨ push M₁ M₂ ╎ γ ╎ cstack ⟩ = step push→
progress ⟨ app W₁ W₂ ╎ γ ╎ cstack ⟩ = step app→
progress ⟨ var W ╎ γ ╎ cstack ⟩ = step var→
progress ⟨ sub M₁ M₂ ╎ γ ╎ cstack ⟩ = step sub→

\end{code}
%<*SubVarHaltingState>
\begin{code}
-- A Normal CState is a halting state and of the form ⟨ 𝐖 ╎ ◻ ⟩.
halting-state :    (cstate : CState) → Normal cstate
                 → Σ[ 𝐖 ∈ MVal ℛ ] cstate ≡ ⟨ 𝐖 ╎ ◻ ⟩
\end{code}
%</SubVarHaltingState>
\begin{code}

halting-state ⟨ W' ╎ ◻ ⟩ normal = W' , refl
halting-state ⟨ W' ╎ < x ； γ >∷ cstack ⟩ normal = ql (normal return→) _
halting-state ⟨ return _ ╎ γ ╎ cstack ⟩ normal = ql (normal eval→) _
halting-state ⟨ pm _ _ ╎ γ ╎ cstack ⟩ normal = ql (normal pmᶜ→) _
halting-state ⟨ push _ _ ╎ γ ╎ cstack ⟩ normal = ql (normal push→) _
halting-state ⟨ app _ _ ╎ γ ╎ cstack ⟩ normal = ql (normal app→) _
halting-state ⟨ var _ ╎ γ ╎ cstack ⟩ normal = ql (normal var→) _
halting-state ⟨ sub _ _ ╎ γ ╎ cstack ⟩ normal = ql (normal sub→) _


exec-acc : {σ : CState} → SN σ → Σ[ σ' ∈ CState ] Σ[ W' ∈ MVal ℛ ] Σ[ NF ∈ Normal σ' ] (σ →ᶜ* σ') × (W' ≡ proj₁ (halting-state σ' NF))
exec-acc {σ = σ} (sn f) with progress σ
... | done NF    = σ , proj₁ (halting-state σ NF) , NF , (σ ◼) , refl
... | step S→S' with exec-acc (f S→S')
...   | (σ'' , W' , NF , S'→*S'' , eq) = σ'' , W' , NF , (_ →ᶜ⟨ S→S' ⟩ S'→*S'') , eq

\end{code}
%<*SubVarEval>
\begin{code}
exec :    (M : Comp ε ℛ)
        → Σ[ cstate ∈ CState ]
          Σ[ 𝐖 ∈ MVal ℛ ]
          Σ[ NF ∈ Normal cstate ]
          (⟨ M ╎ ⋄ ╎ ◻ ⟩ →ᶜ* cstate) × (𝐖 ≡ proj₁ (halting-state cstate NF))
\end{code}
%</SubVarEval>
\begin{code}

exec M = exec-acc (SN-theorem M)

\end{code}
