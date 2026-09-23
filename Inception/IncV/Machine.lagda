\begin{code}

{-# OPTIONS --no-postfix-projections #-}

module Inception.IncV.Machine where

open import Inception.IncV.Syntax
open import Inception.Prelude

open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Nat

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

---------------------------------------------------------------------------------

infixl 27 _·_

---------------------------------------------------------------------------------
-- ENVIRONMENTS

\end{code}
%<*Env>
\begin{code}

mutual

  data CStack {Z₀ : Ty} : (X : Ty) → Set where

    ◻ :        CStack Z₀

    <_；_>∷_ :  Comp (Γ ∙ Y) X → (γ : Env {Z₀ = Z₀} Γ)
                → (pstack : CStack {Z₀ = Z₀} X)
                ------------------------------------
                → CStack Y

  data Value {Z₀ : Ty} : Ty → Set where

    unitᵛ :
              -------------------
              Value {Z₀ = Z₀} `Unit

    datᵛ :    (N : ℕ)
              -------------------
              → Value {Z₀ = Z₀} `P

    pairᵛ :   (Ẇ₁ : Value {Z₀ = Z₀} X₁) → (Ẇ₂ : Value {Z₀ = Z₀} X₂)
              -------------------------------------------------
              → Value (X₁ `× X₂)

    cloᵛ :    {Γ : Ctx} → (M : Comp (Γ ∙ X) Y) → (γ : Env {Z₀ = Z₀} Γ)
              ----------------------------------------------------
              → Value (X `⇒ Y)

    jumpᵛ :   {Γ : Ctx} → (M : Comp (Γ ∙ `P) X) → (γ : Env {Z₀ = Z₀} Γ)
              → (cs : CStack {Z₀ = Z₀} X)
              -----------------------------------------------
              → Value `L

  data Env {Z₀ : Ty} : Ctx → Set where

    ⋄ :
           --------------
           Env {Z₀ = Z₀} ε

    _·_ :  Env {Z₀ = Z₀} Γ → Value {Z₀ = Z₀} X
           ----------------------------------
           → Env {Z₀ = Z₀} (Γ ∙ X)

\end{code}
%</Env>
\begin{code}

lookup : (i : Γ ∋ X) → Env {Z₀ = Z₀} Γ → Value {Z₀ = Z₀} X
lookup here (γ · W') = W'
lookup (there i) (γ · W') = lookup i γ

---------------------------------------------------------------------------------
-- VALUE PROJECTIONS

proj₁-val : {Z₀ : Ty} → Value {Z₀ = Z₀} (X `× Y) → Value {Z₀ = Z₀} X
proj₁-val (pairᵛ W₁ W₂) = W₁

proj₂-val : {Z₀ : Ty} → Value {Z₀ = Z₀} (X `× Y) → Value {Z₀ = Z₀} Y
proj₂-val (pairᵛ W₁ W₂) = W₂

pair-val : {Z₀ : Ty} → (W : Value {Z₀ = Z₀} (X `× Y)) → (pairᵛ (proj₁-val W) (proj₂-val W) ≡ W)
pair-val (pairᵛ W₁ W₂) = refl

---------------------------------------------------------------------------------
-- MACHINE FOR EFFECTFUL TERMS / COMPUTATIONS

\end{code}
%<*CStates>
\begin{code}

data CState {Z₀ : Ty} : Set where

  ⟨_╎_⟩ :    (Ẇ : Value {Z₀ = Z₀} X) → (cstack : CStack {Z₀ = Z₀} X)
             ---------------------------------------------------
             → CState {Z₀ = Z₀}

  ⟨_╎_╎_⟩ :  (M : Comp Γ X) → (γ : Env {Z₀ = Z₀} Γ) → (cstack : CStack {Z₀ = Z₀} X)
             -----------------------------------------------------------------
             → CState {Z₀ = Z₀}

\end{code}
%</CStates>
\begin{code}

run : {Z₀ : Ty} → Pure Γ X → Env {Z₀ = Z₀} Γ → Value {Z₀ = Z₀} X
run (var i) γ = lookup i γ
run (lam M) γ = cloᵛ M γ
run (pair W₁ W₂) γ = pairᵛ (run W₁ γ) (run W₂ γ)
run unit γ = unitᵛ
run (dat N) γ = datᵛ N

jump-to-state : {Z₀ : Ty} → Value {Z₀ = Z₀} `L → Value `P → CState {Z₀ = Z₀}
jump-to-state (jumpᵛ M γ k) W = ⟨ M ╎ γ · W ╎ k ⟩

clo-to-comp : {Z₀ : Ty} → Value {Z₀ = Z₀} (X `⇒ Y) → Σ[ Γ ∈ Ctx ] Comp (Γ ∙ X) Y × Env {Z₀ = Z₀} Γ
clo-to-comp (cloᵛ M γ) = _ , M , γ

clo-val : {Z₀ : Ty} → (W : Value {Z₀ = Z₀} (X `⇒ Y)) → (cloᵛ (proj₁ (proj₂ (clo-to-comp W))) (proj₂ (proj₂ (clo-to-comp W))) ≡ W)
clo-val (cloᵛ M γ) = refl

run-jump : {Z₀ : Ty} → Pure Γ `L → Pure Γ `P → Env {Z₀ = Z₀} Γ → CState {Z₀ = Z₀}
run-jump W₁ W₂ γ = jump-to-state (run W₁ γ) (run W₂ γ)

run-clo : {Z₀ : Ty} → Pure Γ (X `⇒ Y) → Pure Γ X → Env {Z₀ = Z₀} Γ → CStack {Z₀ = Z₀} Y → CState {Z₀ = Z₀}
run-clo W₁ W₂ γ k = ⟨ proj₁ (proj₂ (clo-to-comp (run W₁ γ))) ╎ proj₂ (proj₂ (clo-to-comp (run W₁ γ))) · run W₂ γ ╎ k ⟩

run₁ : {Z₀ : Ty} → Pure Γ (X₁ `× X₂) → Env {Z₀ = Z₀} Γ → Value {Z₀ = Z₀} X₁
run₁ W γ = proj₁-val (run W γ)

run₂ : {Z₀ : Ty} → Pure Γ (X₁ `× X₂) → Env {Z₀ = Z₀} Γ → Value {Z₀ = Z₀} X₂
run₂ W γ = proj₂-val (run W γ)

\end{code}
%<*CTrans>
\begin{code}

data _→ᶜ_ {Z₀ : Ty} : CState {Z₀ = Z₀} → CState {Z₀ = Z₀} → Set where

  pure→ :    {W : Pure Γ X} {γ : Env Γ} {cstack : CStack X}
             -------------------------------------------
             →  ⟨ return W ╎ γ ╎ cstack ⟩ →ᶜ ⟨ run W γ ╎ cstack ⟩

  return→ :  {Ẇ : Value X} {M : Comp (Γ ∙ X) Y} {γ : Env Γ} {cstack : CStack Y}
             --------------------------------------------------------------
             →  ⟨ Ẇ ╎ < M ； γ >∷ cstack ⟩ →ᶜ ⟨ M ╎ γ · Ẇ ╎ cstack ⟩

  push→ :    {M₁ : Comp Γ X} {M₂ : Comp (Γ ∙ X) Y} {γ : Env Γ} {cstack : CStack Y}
             ----------------------------------------------------------------
             →  ⟨ push M₁ M₂ ╎ γ ╎ cstack ⟩ →ᶜ ⟨ M₁ ╎ γ ╎ < M₂ ； γ >∷ cstack ⟩

  inc→ :     {M₁ : Comp (Γ ∙ `L) X} {M₂ : Comp (Γ ∙ `P) X} {γ : Env Γ} {cstack : CStack X}
             ----------------------------------------------------------------
             →  ⟨ inc M₁ M₂ ╎ γ ╎ cstack ⟩ →ᶜ ⟨ M₁ ╎ γ · (jumpᵛ M₂ γ cstack) ╎ cstack ⟩

  rec→ :     {W₁ : Pure Γ `L} {W₂ : Pure Γ `P} {γ : Env Γ} {cstack : CStack X}
             -------------------------------------------------------
             →  ⟨ rec W₁ W₂ ╎ γ ╎ cstack ⟩ →ᶜ run-jump W₁ W₂ γ

  pmᶜ→ :     {W : Pure Γ (X `× Y)} {γ : Env Γ}
             {M : Comp (Γ ∙ X ∙ Y) Z} {cstack : CStack Z}
             -------------------------------------------------------------
             →  ⟨ pm W M ╎ γ ╎ cstack ⟩ →ᶜ ⟨ M ╎ γ · run₁ W γ · run₂ W γ ╎ cstack ⟩

  app→ :     {W₁ : Pure Γ (X `⇒ Y)} {W₂ : Pure Γ X} {γ : Env Γ} {cstack : CStack Y}
             ----------------------------------------------------------------
             →  ⟨ app W₁ W₂ ╎ γ ╎ cstack ⟩ →ᶜ run-clo W₁ W₂ γ cstack

\end{code}
%</CTrans>
\begin{code}

determinismꟲ : {Z₀ : Ty} {S S' : CState {Z₀ = Z₀}} (S→S'₁ S→S'₂ : S →ᶜ S') → (S→S'₁ ≡ S→S'₂)
determinismꟲ pure→ pure→ = refl
determinismꟲ return→ return→ = refl
determinismꟲ push→ push→ = refl
determinismꟲ inc→ inc→ = refl
determinismꟲ rec→ rec→ = refl
determinismꟲ pmᶜ→ pmᶜ→ = refl
determinismꟲ app→ app→ = refl

open Inception.Prelude.RTC renaming (_~>⟨_⟩_ to _→ᶜ⟨_⟩_)

_→ᶜ*_ : {Z₀ : Ty} → CState {Z₀ = Z₀} → CState {Z₀ = Z₀} → Set
_→ᶜ*_ {Z₀ = Z₀} = _~>*_ (_→ᶜ_ {Z₀ = Z₀})

_⨾ᶜ_ : {Z₀ : Ty} → {F S T : CState {Z₀ = Z₀}} → (F →ᶜ* S) → (S →ᶜ* T) → (F →ᶜ* T)
_⨾ᶜ_ (S ◼) S>>T = S>>T
_⨾ᶜ_ (F →ᶜ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᶜ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ᶜ S₂>>T)


data SN {Z₀ : Ty} (σ : CState {Z₀ = Z₀}) : Set where
  sn : (∀ {σ'} → σ →ᶜ σ' → SN σ') → SN σ

Rᵛ : {Z₀ : Ty} → (X : Ty) → Value {Z₀ = Z₀} X → Set
Rᵏ : {Z₀ : Ty} → (X : Ty) → CStack {Z₀ = Z₀} X → Set

Rᵛ `Unit unitᵛ = ⊤
Rᵛ (X `× Y) (pairᵛ W₁ W₂) = Rᵛ X W₁ × Rᵛ Y W₂
Rᵛ {Z₀ = Z₀} (X `⇒ Y) (cloᵛ M γ) = ∀ {W' : Value {Z₀ = Z₀} X} → Rᵛ X W' → ∀ {cstack : CStack {Z₀ = Z₀} Y} → Rᵏ Y cstack → SN ⟨ M ╎ γ · W' ╎ cstack ⟩
Rᵛ {Z₀ = Z₀} `L (jumpᵛ M γ cstack) = ∀ {W' : Value {Z₀ = Z₀} `P} → SN ⟨ M ╎ γ · W' ╎ cstack ⟩
Rᵛ `P (datᵛ N) = ⊤

Rᵏ {Z₀ = Z₀} X cstack = ∀ {W : Value {Z₀ = Z₀} X} → Rᵛ X W → SN ⟨ W ╎ cstack ⟩

Rᴱ : {Z₀ : Ty} → Env {Z₀ = Z₀} Γ → Set
Rᴱ {Γ = Γ} γ = ∀ {X : Ty} → (i : Γ ∋ X) → Rᵛ X (lookup i γ)

Rᴱ-ext : {Z₀ : Ty} {γ : Env {Z₀ = Z₀} Γ} {W : Value {Z₀ = Z₀} X} → Rᴱ γ → Rᵛ X W → Rᴱ (γ · W)
Rᴱ-ext Rγ RW here = RW
Rᴱ-ext Rγ RW (there i) = Rγ i

rv≡sn : {Z₀ : Ty} → (Ẇ : Value {Z₀ = Z₀} `L) → Rᵛ `L Ẇ ≡ (∀ {W' : Value {Z₀ = Z₀} `P} → SN (jump-to-state Ẇ W'))
rv≡sn (jumpᵛ _ _ _) = refl

mutual

  fundamentalᵖ  : {Z₀ : Ty} → (W : Pure Γ X) → {γ : Env {Z₀ = Z₀} Γ} → Rᴱ γ → Rᵛ X (run W γ)
  fundamentalᵖ (var i) Rγ = Rγ i
  fundamentalᵖ (lam M) Rγ RW Rk = fundamentalᶜ M (Rᴱ-ext Rγ RW) Rk
  fundamentalᵖ (pair W₁ W₂) Rγ = (fundamentalᵖ W₁ Rγ) , (fundamentalᵖ W₂ Rγ)
  fundamentalᵖ unit Rγ = tt
  fundamentalᵖ (dat N) Rγ = tt

  fundamentalᶜ : {Z₀ : Ty} → (M : Comp Γ X) → {γ : Env {Z₀ = Z₀} Γ} → Rᴱ γ → {cstack : CStack {Z₀ = Z₀} X} → Rᵏ X cstack → SN ⟨ M ╎ γ ╎ cstack ⟩
  fundamentalᶜ (return W) Rγ Rk = sn λ { pure→ → Rk (fundamentalᵖ W Rγ)}
  fundamentalᶜ (pm W M) {γ = γ} Rγ Rk =
    let
      IH = fundamentalᵖ W Rγ
      W' = run W γ
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
      IH = fundamentalᵖ W₁ Rγ
      W₁' = run W₁ γ
      eq = sym (clo-val W₁')
      IH' = subst (λ x → Rᵛ _ x) eq IH
    in
    sn λ { app→ → IH' (fundamentalᵖ W₂ Rγ) Rk }
  fundamentalᶜ (rec W₁ W₂) {γ = γ} Rγ Rk = sn λ { rec→ → subst (λ x → x) (rv≡sn (run W₁ γ)) (fundamentalᵖ W₁ Rγ)}
  fundamentalᶜ (inc M₁ M₂) Rγ Rk =
    sn λ { inc→ → fundamentalᶜ M₁ (Rᴱ-ext Rγ (λ { {datᵛ N} → fundamentalᶜ M₂ (Rᴱ-ext {W = datᵛ N} Rγ tt) Rk })) Rk }

Rᴱ-⊘ : {Z₀ : Ty} → Rᴱ {Z₀ = Z₀} ⋄
Rᴱ-⊘ = λ ()

Rᵏ-◻ : {Z₀ : Ty} → Rᵏ {Z₀ = Z₀} Z₀ ◻
Rᵏ-◻ RW = sn λ {σ'} ()

SN-theorem : {Z₀ : Ty} → (M : Comp ε Z₀) → SN {Z₀ = Z₀} ⟨ M ╎ ⋄ ╎ ◻ ⟩
SN-theorem M = fundamentalᶜ M Rᴱ-⊘ Rᵏ-◻

Normal : {Z₀ : Ty} → CState {Z₀ = Z₀} → Set
Normal σ = ∀ {σ'} → σ →ᶜ σ' → ⊥

data Progress {Z₀ : Ty} (σ : CState {Z₀ = Z₀}) : Set where
  done : Normal σ → Progress σ
  step : {σ' : CState} → σ →ᶜ σ' → Progress σ

progress : {Z₀ : Ty} (σ : CState {Z₀ = Z₀}) → Progress σ
progress ⟨ W' ╎ ◻ ⟩ = done (λ ())
progress ⟨ W' ╎ < M ； γ >∷ cstack ⟩ = step return→
progress ⟨ return W ╎ γ ╎ cstack ⟩ = step pure→
progress ⟨ pm W M ╎ γ ╎ cstack ⟩ = step pmᶜ→
progress ⟨ push M₁ M₂ ╎ γ ╎ cstack ⟩ = step push→
progress ⟨ app W₁ W₂ ╎ γ ╎ cstack ⟩ = step app→
progress ⟨ rec W₁ W₂ ╎ γ ╎ cstack ⟩ = step rec→
progress ⟨ inc M₁ M₂ ╎ γ ╎ cstack ⟩ = step inc→

halting-state : (σ : CState {Z₀ = Z₀}) → Normal σ → Σ[ W ∈ Value Z₀ ] σ ≡ ⟨ W ╎ ◻ ⟩
halting-state ⟨ W' ╎ ◻ ⟩ normal = W' , refl
halting-state ⟨ W' ╎ < x ； γ >∷ cstack ⟩ normal = ql (normal return→) _
halting-state ⟨ return _ ╎ γ ╎ cstack ⟩ normal = ql (normal pure→) _
halting-state ⟨ pm _ _ ╎ γ ╎ cstack ⟩ normal = ql (normal pmᶜ→) _
halting-state ⟨ push _ _ ╎ γ ╎ cstack ⟩ normal = ql (normal push→) _
halting-state ⟨ app _ _ ╎ γ ╎ cstack ⟩ normal = ql (normal app→) _
halting-state ⟨ rec _ _ ╎ γ ╎ cstack ⟩ normal = ql (normal rec→) _
halting-state ⟨ inc _ _ ╎ γ ╎ cstack ⟩ normal = ql (normal inc→) _


eval-acc : {Z₀ : Ty} {σ : CState {Z₀ = Z₀}} → SN σ → Σ[ σ' ∈ CState ] Σ[ W' ∈ Value {Z₀ = Z₀} Z₀ ] Σ[ NF ∈ Normal σ' ] (σ →ᶜ* σ') × (W' ≡ proj₁ (halting-state σ' NF))
eval-acc {σ = σ} (sn f) with progress σ
... | done NF    = σ , proj₁ (halting-state σ NF) , NF , (σ ◼) , refl
... | step S→S' with eval-acc (f S→S')
...   | (σ'' , W' , NF , S'→*S'' , eq) = σ'' , W' , NF , (_ →ᶜ⟨ S→S' ⟩ S'→*S'') , eq

eval : {Z₀ : Ty} → (M : Comp ε Z₀) → Σ[ σ' ∈ CState ] Σ[ W' ∈ Value {Z₀ = Z₀} Z₀ ] Σ[ NF ∈ Normal σ' ] (⟨ M ╎ ⋄ ╎ ◻ ⟩ →ᶜ* σ') × (W' ≡ proj₁ (halting-state σ' NF))
eval M = eval-acc (SN-theorem M)

\end{code}
