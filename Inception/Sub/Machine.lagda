\begin{code}
{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Machine where

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

  data CStack {ℛ : Ty} : (X : Ty) → Set where

    ◻ :        CStack ℛ

    <_；_>∷_ :  Comp (Γ ∙ Y) X → (γ : MEnv {ℛ = ℛ} Γ)
                → (pstack : CStack {ℛ = ℛ} X)
                ------------------------------------
                → CStack Y

  data MVal {ℛ : Ty} : Ty → Set where

    unitᵛ :
              -------------------
              MVal {ℛ = ℛ} `𝟙

    pairᵛ :   (𝐖₁ : MVal {ℛ = ℛ} X₁) → (𝐖₂ : MVal {ℛ = ℛ} X₂)
              -------------------------------------------------
              → MVal (X₁ `× X₂)

    cloᵛ :    {Γ : Ctx} → (M : Comp (Γ ∙ X) Y) → (γ : MEnv {ℛ = ℛ} Γ)
              ----------------------------------------------------
              → MVal (X `⇒ Y)

    jumpᵛ :   {Γ : Ctx} → (M : Comp Γ X) → (γ : MEnv {ℛ = ℛ} Γ)
              → (cs : CStack {ℛ = ℛ} X)
              -----------------------------------------------
              → MVal `ℓ

  data MEnv {ℛ : Ty} : Ctx → Set where

    ⋄ :
           --------------
           MEnv {ℛ = ℛ} ε

    _·_ :  MEnv {ℛ = ℛ} Γ → MVal {ℛ = ℛ} X
           ----------------------------------
           → MEnv {ℛ = ℛ} (Γ ∙ X)

lookup : Γ ∋ X → MEnv {ℛ = ℛ} Γ → MVal {ℛ = ℛ} X
lookup here (γ · 𝐖) = 𝐖
lookup (there x) (γ · 𝐖) = lookup x γ

\end{code}
%</MEnv>
\begin{code}

---------------------------------------------------------------------------------
-- VALUE PROJECTIONS

proj₁-val : {ℛ : Ty} → MVal {ℛ = ℛ} (X `× Y) → MVal {ℛ = ℛ} X
proj₁-val (pairᵛ W₁ W₂) = W₁

proj₂-val : {ℛ : Ty} → MVal {ℛ = ℛ} (X `× Y) → MVal {ℛ = ℛ} Y
proj₂-val (pairᵛ W₁ W₂) = W₂

pair-val : {ℛ : Ty} → (W : MVal {ℛ = ℛ} (X `× Y)) → (pairᵛ (proj₁-val W) (proj₂-val W) ≡ W)
pair-val (pairᵛ W₁ W₂) = refl

---------------------------------------------------------------------------------
-- MACHINE FOR EFFECTFUL TERMS / COMPUTATIONS

\end{code}
%<*CStates>
\begin{code}

data CState {ℛ : Ty} : Set where

  ⟨_╎_⟩ :    (𝐖 : MVal {ℛ = ℛ} X) → (cstack : CStack {ℛ = ℛ} X)
             ---------------------------------------------------
             → CState {ℛ = ℛ}

  ⟨_╎_╎_⟩ :  (M : Comp Γ X) → (γ : MEnv {ℛ = ℛ} Γ) → (cstack : CStack {ℛ = ℛ} X)
             -----------------------------------------------------------------
             → CState {ℛ = ℛ}

\end{code}
%</CStates>

%<*Eval>
\begin{code}
jump-to-state : {ℛ : Ty} → MVal {ℛ = ℛ} `ℓ → CState {ℛ = ℛ}
jump-to-state (jumpᵛ M γ k) = ⟨ M ╎ γ ╎ k ⟩

clo-to-comp :  {ℛ : Ty} → MVal {ℛ = ℛ} (X `⇒ Y)
               → Σ[ Γ ∈ Ctx ] Comp (Γ ∙ X) Y × MEnv {ℛ = ℛ} Γ
clo-to-comp (cloᵛ M γ) = _ , M , γ

eval : {ℛ : Ty} → Val Γ X → MEnv {ℛ = ℛ} Γ → MVal {ℛ = ℛ} X
eval (var i) γ = lookup i γ
eval (lam M) γ = cloᵛ M γ
eval (pair W₁ W₂) γ = pairᵛ (eval W₁ γ) (eval W₂ γ)
eval unit γ = unitᵛ

eval-jump : {ℛ : Ty} → Val Γ `ℓ → MEnv {ℛ = ℛ} Γ → CState {ℛ = ℛ}
eval-jump W γ = jump-to-state (eval W γ)

eval-clo :  {ℛ : Ty} → Val Γ (X `⇒ Y) → Val Γ X → MEnv {ℛ = ℛ} Γ
            → CStack {ℛ = ℛ} Y → CState {ℛ = ℛ}
eval-clo W₁ W₂ γ k =
  let
    M  = proj₁ (proj₂ (clo-to-comp (eval W₁ γ)))
    γ' = proj₂ (proj₂ (clo-to-comp (eval W₁ γ)))
  in
  ⟨ M ╎ γ' · eval W₂ γ ╎ k  ⟩

eval₁ : {ℛ : Ty} → Val Γ (X₁ `× X₂) → MEnv {ℛ = ℛ} Γ → MVal {ℛ = ℛ} X₁
eval₁ W γ = proj₁-val (eval W γ)

eval₂ : {ℛ : Ty} → Val Γ (X₁ `× X₂) → MEnv {ℛ = ℛ} Γ → MVal {ℛ = ℛ} X₂
eval₂ W γ = proj₂-val (eval W γ)
\end{code}
%</Eval>
\begin{code}

clo-val : {ℛ : Ty} → (W : MVal {ℛ = ℛ} (X `⇒ Y)) → (cloᵛ (proj₁ (proj₂ (clo-to-comp W))) (proj₂ (proj₂ (clo-to-comp W))) ≡ W)
clo-val (cloᵛ M γ) = refl

\end{code}

%<*CTrans>
\begin{code}

data _→ᶜ_ {ℛ : Ty} : CState {ℛ = ℛ} → CState {ℛ = ℛ} → Set where

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


determinismꟲ : {ℛ : Ty} {S S' : CState {ℛ = ℛ}} (S→S'₁ S→S'₂ : S →ᶜ S') → (S→S'₁ ≡ S→S'₂)
determinismꟲ eval→ eval→ = refl
determinismꟲ return→ return→ = refl
determinismꟲ push→ push→ = refl
determinismꟲ sub→ sub→ = refl
determinismꟲ var→ var→ = refl
determinismꟲ pmᶜ→ pmᶜ→ = refl
determinismꟲ app→ app→ = refl

open Inception.Prelude.RTC renaming (_~>⟨_⟩_ to _→ᶜ⟨_⟩_)

_→ᶜ*_ : {ℛ : Ty} → CState {ℛ = ℛ} → CState {ℛ = ℛ} → Set
_→ᶜ*_ {ℛ = ℛ} = _~>*_ (_→ᶜ_ {ℛ = ℛ})

_⨾ᶜ_ : {ℛ : Ty} → {F S T : CState {ℛ = ℛ}} → (F →ᶜ* S) → (S →ᶜ* T) → (F →ᶜ* T)
_⨾ᶜ_ (S ◼) S>>T = S>>T
_⨾ᶜ_ (F →ᶜ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᶜ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ᶜ S₂>>T)


\end{code}
%<*SubVarSN>
\begin{code}
data SN {ℛ : Ty} (σ : CState {ℛ = ℛ}) : Set where
  sn : (∀ {σ'} → σ →ᶜ σ' → SN σ') → SN σ
\end{code}
%</SubVarSN>
\begin{code}

Rᵛ : {ℛ : Ty} → (X : Ty) → MVal {ℛ = ℛ} X → Set
Rᵏ : {ℛ : Ty} → (X : Ty) → CStack {ℛ = ℛ} X → Set

Rᵛ `𝟙 unitᵛ = ⊤
Rᵛ (X `× Y) (pairᵛ W₁ W₂) = Rᵛ X W₁ × Rᵛ Y W₂
Rᵛ {ℛ = ℛ} (X `⇒ Y) (cloᵛ M γ) = ∀ {W' : MVal {ℛ = ℛ} X} → Rᵛ X W' → ∀ {cstack : CStack {ℛ = ℛ} Y} → Rᵏ Y cstack → SN ⟨ M ╎ γ · W' ╎ cstack ⟩
Rᵛ `ℓ (jumpᵛ M γ cstack) = SN ⟨ M ╎ γ ╎ cstack ⟩

Rᵏ {ℛ = ℛ} X cstack = ∀ {W : MVal {ℛ = ℛ} X} → Rᵛ X W → SN ⟨ W ╎ cstack ⟩

Rᴱ : {ℛ : Ty} → MEnv {ℛ = ℛ} Γ → Set
Rᴱ {Γ = Γ} γ = ∀ {X : Ty} → (i : Γ ∋ X) → Rᵛ X (lookup i γ)

Rᴱ-ext : {ℛ : Ty} {γ : MEnv {ℛ = ℛ} Γ} {W : MVal {ℛ = ℛ} X} → Rᴱ γ → Rᵛ X W → Rᴱ (γ · W)
Rᴱ-ext Rγ RW here = RW
Rᴱ-ext Rγ RW (there i) = Rγ i

rv≡sn : {ℛ : Ty} → (𝐖 : MVal {ℛ = ℛ} `ℓ) → Rᵛ `ℓ 𝐖 ≡ SN (jump-to-state 𝐖)
rv≡sn (jumpᵛ _ _ _) = refl

mutual

  fundamentalᵛ  : {ℛ : Ty} → (W : Val Γ X) → {γ : MEnv {ℛ = ℛ} Γ} → Rᴱ γ → Rᵛ X (eval W γ)
  fundamentalᵛ (var i) Rγ = Rγ i
  fundamentalᵛ (lam M) Rγ RW Rk = fundamentalᶜ M (Rᴱ-ext Rγ RW) Rk
  fundamentalᵛ (pair W₁ W₂) Rγ = (fundamentalᵛ W₁ Rγ) , (fundamentalᵛ W₂ Rγ)
  fundamentalᵛ unit Rγ = tt

  fundamentalᶜ : {ℛ : Ty} → (M : Comp Γ X) → {γ : MEnv {ℛ = ℛ} Γ} → Rᴱ γ → {cstack : CStack {ℛ = ℛ} X} → Rᵏ X cstack → SN ⟨ M ╎ γ ╎ cstack ⟩
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

Rᴱ-⊘ : {ℛ : Ty} → Rᴱ {ℛ = ℛ} ⋄
Rᴱ-⊘ = λ ()

Rᵏ-◻ : {ℛ : Ty} → Rᵏ {ℛ = ℛ} ℛ ◻
Rᵏ-◻ RW = sn λ {σ'} ()

SN-theorem : {ℛ : Ty} → (M : Comp ε ℛ) → SN {ℛ = ℛ} ⟨ M ╎ ⋄ ╎ ◻ ⟩
SN-theorem M = fundamentalᶜ M Rᴱ-⊘ Rᵏ-◻

\end{code}
%<*SubVarNormal>
\begin{code}
-- A CState is Normal, if there are no transitions from it.
Normal : {ℛ : Ty} → CState {ℛ = ℛ} → Set
Normal cstate₁ = ∀ {cstate₂} → cstate₁ →ᶜ cstate₂ → ⊥
\end{code}
%</SubVarNormal>
\begin{code}

data Progress {ℛ : Ty} (σ : CState {ℛ = ℛ}) : Set where
  done : Normal σ → Progress σ
  step : {σ' : CState} → σ →ᶜ σ' → Progress σ

progress : {ℛ : Ty} (σ : CState {ℛ = ℛ}) → Progress σ
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
halting-state :    (cstate : CState {ℛ = ℛ}) → Normal cstate
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


exec-acc : {ℛ : Ty} {σ : CState {ℛ = ℛ}} → SN σ → Σ[ σ' ∈ CState ] Σ[ W' ∈ MVal {ℛ = ℛ} ℛ ] Σ[ NF ∈ Normal σ' ] (σ →ᶜ* σ') × (W' ≡ proj₁ (halting-state σ' NF))
exec-acc {σ = σ} (sn f) with progress σ
... | done NF    = σ , proj₁ (halting-state σ NF) , NF , (σ ◼) , refl
... | step S→S' with exec-acc (f S→S')
...   | (σ'' , W' , NF , S'→*S'' , eq) = σ'' , W' , NF , (_ →ᶜ⟨ S→S' ⟩ S'→*S'') , eq

\end{code}
%<*SubVarEval>
\begin{code}
exec :    {ℛ : Ty} → (M : Comp ε ℛ)
        → Σ[ cstate ∈ CState ]
          Σ[ 𝐖 ∈ MVal {ℛ = ℛ} ℛ ]
          Σ[ NF ∈ Normal cstate ]
          (⟨ M ╎ ⋄ ╎ ◻ ⟩ →ᶜ* cstate) × (𝐖 ≡ proj₁ (halting-state cstate NF))
\end{code}
%</SubVarEval>
\begin{code}

exec M = exec-acc (SN-theorem M)

---------------------------------------------------------------------------------
-- EXAMPLES

ex15 : ε ⊢ᶜ (`𝟙)
ex15 = push (push (app (lam {X = `𝟙} (sub (var (var here)) (return unit))) unit) (return unit)) (return unit)

_ : exec ex15 ≡ (_ , unitᵛ , _ ,
                  (⟨ push (push (app (lam (sub (var (var here)) (return unit))) unit) (return unit)) (return unit) ╎ ⋄ ╎ ◻ ⟩
    →ᶜ⟨ push→ ⟩   (⟨ push (app (lam (sub (var (var here)) (return unit))) unit) (return unit) ╎ ⋄ ╎ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ push→ ⟩   (⟨ app (lam (sub (var (var here)) (return unit))) unit ╎ ⋄ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ app→ ⟩    (⟨ sub (var (var here)) (return unit) ╎ ⋄ · unitᵛ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ sub→ ⟩    (⟨ var (var here) ╎ ⋄ · unitᵛ · jumpᵛ (return unit) (⋄ · unitᵛ) (< return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻) ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ var→ ⟩    (⟨ return unit ╎ ⋄ · unitᵛ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ eval→ ⟩ (⟨ unitᵛ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ return→ ⟩ (⟨ return unit ╎ ⋄ · unitᵛ ╎ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ eval→ ⟩ (⟨ unitᵛ ╎ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ return→ ⟩ (⟨ return unit ╎ ⋄ · unitᵛ ╎ ◻ ⟩
    →ᶜ⟨ eval→ ⟩ (⟨ unitᵛ ╎ ◻ ⟩ ◼)))))))))))
    , _)
_ = refl

\end{code}
