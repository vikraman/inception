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
--∀ {Γ : Ctx} {𝐖 : MClo Γ X} {γ : MEnv Γ} → Rᵛ X 𝐖 γ → SN ⟨ 𝐖 ； γ ╎ K ⟩
--∀ {𝐖 : MVal X} → Rᵛ X 𝐖 → SN ⟨ 𝐖 ╎ K ⟩

\end{code}

% Rᵛ : {ℛ : Ty} → (X : Ty) → Value {ℛ = ℛ} X → Set
% Rᵏ : {ℛ : Ty} → (X : Ty) → CStack {ℛ = ℛ} X → Set
%
% Rᵛ `𝟙 unitᵛ = ⊤
% Rᵛ (X `× Y) (pairᵛ W₁ W₂) = Rᵛ X W₁ × Rᵛ Y W₂
% Rᵛ {ℛ = ℛ} (X `⇒ Y) (cloᵛ M γ) = ∀ {W' : Value {ℛ = ℛ} X} → Rᵛ X W' → ∀ {cstack : CStack {ℛ = ℛ} Y} → Rᵏ Y cstack → SN ⟨ M ╎ γ · W' ╎ cstack ⟩
% Rᵛ `ℓ (jumpᵛ M γ cstack) = SN ⟨ M ╎ γ ╎ cstack ⟩
%
% Rᵏ {ℛ = ℛ} X cstack = ∀ {W : Value {ℛ = ℛ} X} → Rᵛ X W → SN ⟨ W ╎ cstack ⟩
%
% Rᴱ : {ℛ : Ty} → MEnv {ℛ = ℛ} Γ → Set
% Rᴱ {Γ = Γ} γ = ∀ {X : Ty} → (i : Γ ∋ X) → Rᵛ X (lookup i γ)
%
% Rᴱ-ext : {ℛ : Ty} {γ : MEnv {ℛ = ℛ} Γ} {W : Value {ℛ = ℛ} X} → Rᴱ γ → Rᵛ X W → Rᴱ (γ · W)
% Rᴱ-ext Rγ RW here = RW
% Rᴱ-ext Rγ RW (there i) = Rγ i
%
% rv≡sn : {ℛ : Ty} → (𝐖 : Value {ℛ = ℛ} `ℓ) → Rᵛ `ℓ 𝐖 ≡ SN (jump-to-state 𝐖)
% rv≡sn (jumpᵛ _ _ _) = refl
%
% mutual
%
%   fundamentalᵖ  : {ℛ : Ty} → (W : Pure Γ X) → {γ : MEnv {ℛ = ℛ} Γ} → Rᴱ γ → Rᵛ X (eval W γ)
%   fundamentalᵖ (var i) Rγ = Rγ i
%   fundamentalᵖ (lam M) Rγ RW Rk = fundamentalᶜ M (Rᴱ-ext Rγ RW) Rk
%   fundamentalᵖ (pair W₁ W₂) Rγ = (fundamentalᵖ W₁ Rγ) , (fundamentalᵖ W₂ Rγ)
%   fundamentalᵖ unit Rγ = tt
%
%   fundamentalᶜ : {ℛ : Ty} → (M : Comp Γ X) → {γ : MEnv {ℛ = ℛ} Γ} → Rᴱ γ → {cstack : CStack {ℛ = ℛ} X} → Rᵏ X cstack → SN ⟨ M ╎ γ ╎ cstack ⟩
%   fundamentalᶜ (return W) Rγ Rk = sn λ { eval→ → Rk (fundamentalᵖ W Rγ)}
%   fundamentalᶜ (pm W M) {γ = γ} Rγ Rk =
%     let
%       IH = fundamentalᵖ W Rγ
%       W' = eval W γ
%       IH' : Rᵛ _ (pairᵛ (proj₁-val W') (proj₂-val W'))
%       IH' = subst (λ x → Rᵛ _ x) (sym (pair-val W')) IH
%     in
%     sn λ { pmᶜ→ → fundamentalᶜ M (Rᴱ-ext (Rᴱ-ext Rγ (proj₁ IH')) (proj₂ IH')) Rk }
%   fundamentalᶜ (push M₁ M₂) {γ = γ} Rγ {cstack = k} Rk =
%     let
%       Rk' : Rᵏ _ (< M₂ ； γ >∷ k)
%       Rk' RW = sn (λ { return→ → fundamentalᶜ M₂ (Rᴱ-ext Rγ RW) Rk })
%     in
%     sn λ { push→ → fundamentalᶜ M₁ Rγ Rk' }
%   fundamentalᶜ (app W₁ W₂) {γ = γ} Rγ {cstack = k} Rk =
%     let
%       IH = fundamentalᵖ W₁ Rγ
%       W₁' = eval W₁ γ
%       eq = sym (clo-val W₁')
%       IH' = subst (λ x → Rᵛ _ x) eq IH
%     in
%     sn λ { app→ → IH' (fundamentalᵖ W₂ Rγ) Rk }
%   fundamentalᶜ (var W) {γ = γ} Rγ Rk = sn λ { var→ → subst (λ x → x) (rv≡sn (eval W γ)) (fundamentalᵖ W Rγ)}
%   fundamentalᶜ (sub M₁ M₂) Rγ Rk = sn λ { sub→ → fundamentalᶜ M₁ (Rᴱ-ext Rγ (fundamentalᶜ M₂ Rγ Rk)) Rk}
%
% Rᴱ-⊘ : {ℛ : Ty} → Rᴱ {ℛ = ℛ} ⋄
% Rᴱ-⊘ = λ ()
%
% Rᵏ-◻ : {ℛ : Ty} → Rᵏ {ℛ = ℛ} ℛ ◻
% Rᵏ-◻ RW = sn λ {σ'} ()
%
% SN-theorem : {ℛ : Ty} → (M : Comp ε ℛ) → SN {ℛ = ℛ} ⟨ M ╎ ⋄ ╎ ◻ ⟩
% SN-theorem M = fundamentalᶜ M Rᴱ-⊘ Rᵏ-◻
%
% \end{code}
% %<*SubVarNormal>
% \begin{code}
% -- A CState is Normal, if there are no transitions from it.
% Normal : {ℛ : Ty} → CState {ℛ = ℛ} → Set
% Normal cstate₁ = ∀ {cstate₂} → cstate₁ →ᶜ cstate₂ → ⊥
% \end{code}
% %</SubVarNormal>
% \begin{code}
%
% data Progress {ℛ : Ty} (σ : CState {ℛ = ℛ}) : Set where
%   done : Normal σ → Progress σ
%   step : {σ' : CState} → σ →ᶜ σ' → Progress σ
%
% progress : {ℛ : Ty} (σ : CState {ℛ = ℛ}) → Progress σ
% progress ⟨ W' ╎ ◻ ⟩ = done (λ ())
% progress ⟨ W' ╎ < M ； γ >∷ cstack ⟩ = step return→
% progress ⟨ return W ╎ γ ╎ cstack ⟩ = step eval→
% progress ⟨ pm W M ╎ γ ╎ cstack ⟩ = step pmᶜ→
% progress ⟨ push M₁ M₂ ╎ γ ╎ cstack ⟩ = step push→
% progress ⟨ app W₁ W₂ ╎ γ ╎ cstack ⟩ = step app→
% progress ⟨ var W ╎ γ ╎ cstack ⟩ = step var→
% progress ⟨ sub M₁ M₂ ╎ γ ╎ cstack ⟩ = step sub→
%
% \end{code}
% %<*SubVarHaltingState>
% \begin{code}
% -- A Normal CState is a halting state and of the form ⟨ 𝐖 ╎ ◻ ⟩.
% halting-state :    (cstate : CState {ℛ = ℛ}) → Normal cstate
%                  → Σ[ 𝐖 ∈ Value ℛ ] cstate ≡ ⟨ 𝐖 ╎ ◻ ⟩
% \end{code}
% %</SubVarHaltingState>
% \begin{code}
%
% halting-state ⟨ W' ╎ ◻ ⟩ normal = W' , refl
% halting-state ⟨ W' ╎ < x ； γ >∷ cstack ⟩ normal = ql (normal return→) _
% halting-state ⟨ return _ ╎ γ ╎ cstack ⟩ normal = ql (normal eval→) _
% halting-state ⟨ pm _ _ ╎ γ ╎ cstack ⟩ normal = ql (normal pmᶜ→) _
% halting-state ⟨ push _ _ ╎ γ ╎ cstack ⟩ normal = ql (normal push→) _
% halting-state ⟨ app _ _ ╎ γ ╎ cstack ⟩ normal = ql (normal app→) _
% halting-state ⟨ var _ ╎ γ ╎ cstack ⟩ normal = ql (normal var→) _
% halting-state ⟨ sub _ _ ╎ γ ╎ cstack ⟩ normal = ql (normal sub→) _
%
%
% exec-acc : {ℛ : Ty} {σ : CState {ℛ = ℛ}} → SN σ → Σ[ σ' ∈ CState ] Σ[ W' ∈ Value {ℛ = ℛ} ℛ ] Σ[ NF ∈ Normal σ' ] (σ →ᶜ* σ') × (W' ≡ proj₁ (halting-state σ' NF))
% exec-acc {σ = σ} (sn f) with progress σ
% ... | done NF    = σ , proj₁ (halting-state σ NF) , NF , (σ ◼) , refl
% ... | step S→S' with exec-acc (f S→S')
% ...   | (σ'' , W' , NF , S'→*S'' , eq) = σ'' , W' , NF , (_ →ᶜ⟨ S→S' ⟩ S'→*S'') , eq
%
% \end{code}
% %<*SubVarEval>
% \begin{code}
% exec :    {ℛ : Ty} → (M : Comp ε ℛ)
%         → Σ[ cstate ∈ CState ]
%           Σ[ 𝐖 ∈ Value {ℛ = ℛ} ℛ ]
%           Σ[ NF ∈ Normal cstate ]
%           (⟨ M ╎ ⋄ ╎ ◻ ⟩ →ᶜ* cstate) × (𝐖 ≡ proj₁ (halting-state cstate NF))
% \end{code}
% %</SubVarEval>
% \begin{code}
%
% exec M = exec-acc (SN-theorem M)
%
% ---------------------------------------------------------------------------------
% -- EXAMPLES
%
% ex15 : ε ⊢ᶜ (`𝟙)
% ex15 = push (push (app (lam {X = `𝟙} (sub (var (var here)) (return unit))) unit) (return unit)) (return unit)
%
% _ : exec ex15 ≡ (_ , unitᵛ , _ ,
%                   (⟨ push (push (app (lam (sub (var (var here)) (return unit))) unit) (return unit)) (return unit) ╎ ⋄ ╎ ◻ ⟩
%     →ᶜ⟨ push→ ⟩   (⟨ push (app (lam (sub (var (var here)) (return unit))) unit) (return unit) ╎ ⋄ ╎ < return unit ； ⋄ >∷ ◻ ⟩
%     →ᶜ⟨ push→ ⟩   (⟨ app (lam (sub (var (var here)) (return unit))) unit ╎ ⋄ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
%     →ᶜ⟨ app→ ⟩    (⟨ sub (var (var here)) (return unit) ╎ ⋄ · unitᵛ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
%     →ᶜ⟨ sub→ ⟩    (⟨ var (var here) ╎ ⋄ · unitᵛ · jumpᵛ (return unit) (⋄ · unitᵛ) (< return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻) ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
%     →ᶜ⟨ var→ ⟩    (⟨ return unit ╎ ⋄ · unitᵛ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
%     →ᶜ⟨ eval→ ⟩ (⟨ unitᵛ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
%     →ᶜ⟨ return→ ⟩ (⟨ return unit ╎ ⋄ · unitᵛ ╎ < return unit ； ⋄ >∷ ◻ ⟩
%     →ᶜ⟨ eval→ ⟩ (⟨ unitᵛ ╎ < return unit ； ⋄ >∷ ◻ ⟩
%     →ᶜ⟨ return→ ⟩ (⟨ return unit ╎ ⋄ · unitᵛ ╎ ◻ ⟩
%     →ᶜ⟨ eval→ ⟩ (⟨ unitᵛ ╎ ◻ ⟩ ◼)))))))))))
%     , _)
% _ = refl
% \end{code}
