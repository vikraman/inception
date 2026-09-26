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

  data MVal {Z₀ : Ty} : Ty → Set where

    unitᵛ :
              -------------------
              MVal {Z₀ = Z₀} `Unit

    datᵛ :    (N : ℕ)
              -------------------
              → MVal {Z₀ = Z₀} `P

    pairᵛ :   (𝐕 : MVal {Z₀ = Z₀} X₁) → (𝐖 : MVal {Z₀ = Z₀} X₂)
              -------------------------------------------------
              → MVal (X₁ `× X₂)

    cloᵛ :    {Γ : Ctx} → (M : Comp (Γ ∙ X) Y) → (γ : Env {Z₀ = Z₀} Γ)
              ----------------------------------------------------
              → MVal (X `⇒ Y)

    jumpᵛ :   {Γ : Ctx} → (M : Comp (Γ ∙ `P) X) → (γ : Env {Z₀ = Z₀} Γ)
              → (K : CStack {Z₀ = Z₀} X)
              -----------------------------------------------
              → MVal `L

  data Env {Z₀ : Ty} : Ctx → Set where

    ⋄ :
           --------------
           Env {Z₀ = Z₀} ε

    _·_ :  Env {Z₀ = Z₀} Γ → MVal {Z₀ = Z₀} X
           ----------------------------------
           → Env {Z₀ = Z₀} (Γ ∙ X)

\end{code}
%</Env>
\begin{code}

lookup : (i : Γ ∋ X) → Env {Z₀ = Z₀} Γ → MVal {Z₀ = Z₀} X
lookup here (γ · 𝐖) = 𝐖
lookup (there i) (γ · 𝐖) = lookup i γ

---------------------------------------------------------------------------------
-- VALUE PROJECTIONS

proj₁-val : {Z₀ : Ty} → MVal {Z₀ = Z₀} (X `× Y) → MVal {Z₀ = Z₀} X
proj₁-val (pairᵛ 𝐕 𝐖) = 𝐕

proj₂-val : {Z₀ : Ty} → MVal {Z₀ = Z₀} (X `× Y) → MVal {Z₀ = Z₀} Y
proj₂-val (pairᵛ 𝐕 𝐖) = 𝐖

pair-val : {Z₀ : Ty} → (W : MVal {Z₀ = Z₀} (X `× Y)) → (pairᵛ (proj₁-val W) (proj₂-val W) ≡ W)
pair-val (pairᵛ 𝐕 𝐖) = refl

---------------------------------------------------------------------------------
-- MACHINE FOR EFFECTFUL TERMS / COMPUTATIONS

\end{code}
%<*CStates>
\begin{code}

data CState {Z₀ : Ty} : Set where

  ⟨_╎_⟩ :    (𝐖 : MVal {Z₀ = Z₀} X) → (K : CStack {Z₀ = Z₀} X)
             ---------------------------------------------------
             → CState {Z₀ = Z₀}

  ⟨_╎_╎_⟩ :  (M : Comp Γ X) → (γ : Env {Z₀ = Z₀} Γ) → (K : CStack {Z₀ = Z₀} X)
             -----------------------------------------------------------------
             → CState {Z₀ = Z₀}

\end{code}
%</CStates>
\begin{code}

run : {Z₀ : Ty} → Val Γ X → Env {Z₀ = Z₀} Γ → MVal {Z₀ = Z₀} X
run (var i) γ = lookup i γ
run (lam M) γ = cloᵛ M γ
run (pair V W) γ = pairᵛ (run V γ) (run W γ)
run unit γ = unitᵛ
run (dat N) γ = datᵛ N

jump-to-state : {Z₀ : Ty} → MVal {Z₀ = Z₀} `L → MVal `P → CState {Z₀ = Z₀}
jump-to-state (jumpᵛ M γ K) 𝐖 = ⟨ M ╎ γ · 𝐖 ╎ K ⟩

clo-to-comp : {Z₀ : Ty} → MVal {Z₀ = Z₀} (X `⇒ Y) → Σ[ Γ ∈ Ctx ] Comp (Γ ∙ X) Y × Env {Z₀ = Z₀} Γ
clo-to-comp (cloᵛ M γ) = _ , M , γ

clo-val : {Z₀ : Ty} → (W : MVal {Z₀ = Z₀} (X `⇒ Y)) → (cloᵛ (proj₁ (proj₂ (clo-to-comp W))) (proj₂ (proj₂ (clo-to-comp W))) ≡ W)
clo-val (cloᵛ M γ) = refl

run-jump : {Z₀ : Ty} → Val Γ `L → Val Γ `P → Env {Z₀ = Z₀} Γ → CState {Z₀ = Z₀}
run-jump V W γ = jump-to-state (run V γ) (run W γ)

run-clo : {Z₀ : Ty} → Val Γ (X `⇒ Y) → Val Γ X → Env {Z₀ = Z₀} Γ → CStack {Z₀ = Z₀} Y → CState {Z₀ = Z₀}
run-clo V W γ K = ⟨ proj₁ (proj₂ (clo-to-comp (run V γ))) ╎ proj₂ (proj₂ (clo-to-comp (run V γ))) · run W γ ╎ K ⟩

run₁ : {Z₀ : Ty} → Val Γ (X₁ `× X₂) → Env {Z₀ = Z₀} Γ → MVal {Z₀ = Z₀} X₁
run₁ W γ = proj₁-val (run W γ)

run₂ : {Z₀ : Ty} → Val Γ (X₁ `× X₂) → Env {Z₀ = Z₀} Γ → MVal {Z₀ = Z₀} X₂
run₂ W γ = proj₂-val (run W γ)

\end{code}
%<*CTrans>
\begin{code}

data _→ᶜ_ {Z₀ : Ty} : CState {Z₀ = Z₀} → CState {Z₀ = Z₀} → Set where

  run→ :    {W : Val Γ X} {γ : Env Γ} {K : CStack X}
             -------------------------------------------
             →  ⟨ return W ╎ γ ╎ K ⟩ →ᶜ ⟨ run W γ ╎ K ⟩

  return→ :  {𝐖 : MVal X} {M : Comp (Γ ∙ X) Y} {γ : Env Γ} {K : CStack Y}
             --------------------------------------------------------------
             →  ⟨ 𝐖 ╎ < M ； γ >∷ K ⟩ →ᶜ ⟨ M ╎ γ · 𝐖 ╎ K ⟩

  push→ :    {M : Comp Γ X} {N : Comp (Γ ∙ X) Y} {γ : Env Γ} {K : CStack Y}
             ----------------------------------------------------------------
             →  ⟨ push M N ╎ γ ╎ K ⟩ →ᶜ ⟨ M ╎ γ ╎ < N ； γ >∷ K ⟩

  inc→ :     {M : Comp (Γ ∙ `L) X} {N : Comp (Γ ∙ `P) X} {γ : Env Γ} {K : CStack X}
             ----------------------------------------------------------------
             →  ⟨ inc M N ╎ γ ╎ K ⟩ →ᶜ ⟨ M ╎ γ · (jumpᵛ N γ K) ╎ K ⟩

  rec→ :     {V : Val Γ `L} {W : Val Γ `P} {γ : Env Γ} {K : CStack X}
             -------------------------------------------------------
             →  ⟨ rec V W ╎ γ ╎ K ⟩ →ᶜ run-jump V W γ

  pmᶜ→ :     {W : Val Γ (X `× Y)} {γ : Env Γ}
             {M : Comp (Γ ∙ X ∙ Y) Z} {K : CStack Z}
             -------------------------------------------------------------
             →  ⟨ pm W M ╎ γ ╎ K ⟩ →ᶜ ⟨ M ╎ γ · run₁ W γ · run₂ W γ ╎ K ⟩

  app→ :     {V : Val Γ (X `⇒ Y)} {W : Val Γ X} {γ : Env Γ} {K : CStack Y}
             ----------------------------------------------------------------
             →  ⟨ app V W ╎ γ ╎ K ⟩ →ᶜ run-clo V W γ K

\end{code}
%</CTrans>
\begin{code}

determinismꟲ : {Z₀ : Ty} {σ σ' : CState {Z₀ = Z₀}} (s₁ s₂ : σ →ᶜ σ') → (s₁ ≡ s₂)
determinismꟲ run→ run→ = refl
determinismꟲ return→ return→ = refl
determinismꟲ push→ push→ = refl
determinismꟲ inc→ inc→ = refl
determinismꟲ rec→ rec→ = refl
determinismꟲ pmᶜ→ pmᶜ→ = refl
determinismꟲ app→ app→ = refl

open Inception.Prelude.RTC renaming (_~>⟨_⟩_ to _→ᶜ⟨_⟩_)

_→ᶜ*_ : {Z₀ : Ty} → CState {Z₀ = Z₀} → CState {Z₀ = Z₀} → Set
_→ᶜ*_ {Z₀ = Z₀} = _~>*_ (_→ᶜ_ {Z₀ = Z₀})

_⨾ᶜ_ : {Z₀ : Ty} → {σ₁ σ₂ σ₃ : CState {Z₀ = Z₀}} → (σ₁ →ᶜ* σ₂) → (σ₂ →ᶜ* σ₃) → (σ₁ →ᶜ* σ₃)
_⨾ᶜ_ (σ ◼) ss = ss
_⨾ᶜ_ (σ →ᶜ⟨ s ⟩ ss₁) ss₂ = σ →ᶜ⟨ s ⟩ (ss₁ ⨾ᶜ ss₂)


data SN {Z₀ : Ty} (σ : CState {Z₀ = Z₀}) : Set where
  sn : (∀ {σ'} → σ →ᶜ σ' → SN σ') → SN σ

Rᵛ : {Z₀ : Ty} → (X : Ty) → MVal {Z₀ = Z₀} X → Set
Rᵏ : {Z₀ : Ty} → (X : Ty) → CStack {Z₀ = Z₀} X → Set

Rᵛ `Unit unitᵛ = ⊤
Rᵛ (X `× Y) (pairᵛ 𝐕 𝐖) = Rᵛ X 𝐕 × Rᵛ Y 𝐖
Rᵛ {Z₀ = Z₀} (X `⇒ Y) (cloᵛ M γ) = ∀ {𝐖 : MVal {Z₀ = Z₀} X} → Rᵛ X 𝐖 → ∀ {K : CStack {Z₀ = Z₀} Y} → Rᵏ Y K → SN ⟨ M ╎ γ · 𝐖 ╎ K ⟩
Rᵛ {Z₀ = Z₀} `L (jumpᵛ M γ K) = ∀ {𝐖 : MVal {Z₀ = Z₀} `P} → SN ⟨ M ╎ γ · 𝐖 ╎ K ⟩
Rᵛ `P (datᵛ N) = ⊤

Rᵏ {Z₀ = Z₀} X K = ∀ {𝐖 : MVal {Z₀ = Z₀} X} → Rᵛ X 𝐖 → SN ⟨ 𝐖 ╎ K ⟩

Rᴱ : {Z₀ : Ty} → Env {Z₀ = Z₀} Γ → Set
Rᴱ {Γ = Γ} γ = ∀ {X : Ty} → (i : Γ ∋ X) → Rᵛ X (lookup i γ)

Rᴱ-ext : {Z₀ : Ty} {γ : Env {Z₀ = Z₀} Γ} {𝐖 : MVal {Z₀ = Z₀} X} → Rᴱ γ → Rᵛ X 𝐖 → Rᴱ (γ · 𝐖)
Rᴱ-ext Rγ RW here = RW
Rᴱ-ext Rγ RW (there i) = Rγ i

rv≡sn : {Z₀ : Ty} → (𝐖 : MVal {Z₀ = Z₀} `L) → Rᵛ `L 𝐖 ≡ (∀ {𝐕 : MVal {Z₀ = Z₀} `P} → SN (jump-to-state 𝐖 𝐕))
rv≡sn (jumpᵛ _ _ _) = refl

mutual

  fundamentalᵛ  : {Z₀ : Ty} → (W : Val Γ X) → {γ : Env {Z₀ = Z₀} Γ} → Rᴱ γ → Rᵛ X (run W γ)
  fundamentalᵛ (var i) Rγ = Rγ i
  fundamentalᵛ (lam M) Rγ RW Rk = fundamentalᶜ M (Rᴱ-ext Rγ RW) Rk
  fundamentalᵛ (pair V W) Rγ = (fundamentalᵛ V Rγ) , (fundamentalᵛ W Rγ)
  fundamentalᵛ unit Rγ = tt
  fundamentalᵛ (dat N) Rγ = tt

  fundamentalᶜ : {Z₀ : Ty} → (M : Comp Γ X) → {γ : Env {Z₀ = Z₀} Γ} → Rᴱ γ → {K : CStack {Z₀ = Z₀} X} → Rᵏ X K → SN ⟨ M ╎ γ ╎ K ⟩
  fundamentalᶜ (return W) Rγ Rk = sn λ { run→ → Rk (fundamentalᵛ W Rγ)}
  fundamentalᶜ (pm W M) {γ = γ} Rγ Rk =
    let
      IH = fundamentalᵛ W Rγ
      𝐖  = run W γ
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
      𝐕 = run V γ
      eq = sym (clo-val 𝐕)
      IH₁ = subst (λ x → Rᵛ _ x) eq IH
    in
    sn λ { app→ → IH₁ (fundamentalᵛ W Rγ) Rk }
  fundamentalᶜ (rec V W) {γ = γ} Rγ Rk = sn λ { rec→ → subst (λ x → x) (rv≡sn (run V γ)) (fundamentalᵛ V Rγ)}
  fundamentalᶜ (inc M N) Rγ Rk =
    sn λ { inc→ → fundamentalᶜ M (Rᴱ-ext Rγ (λ { {datᵛ n} → fundamentalᶜ N (Rᴱ-ext {𝐖 = datᵛ n} Rγ tt) Rk })) Rk }

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
progress ⟨ 𝐖 ╎ ◻ ⟩ = done (λ ())
progress ⟨ 𝐖 ╎ < M ； γ >∷ K ⟩ = step return→
progress ⟨ return W ╎ γ ╎ K ⟩ = step run→
progress ⟨ pm W M ╎ γ ╎ K ⟩ = step pmᶜ→
progress ⟨ push M N ╎ γ ╎ K ⟩ = step push→
progress ⟨ app V W ╎ γ ╎ K ⟩ = step app→
progress ⟨ rec V W ╎ γ ╎ K ⟩ = step rec→
progress ⟨ inc M N ╎ γ ╎ K ⟩ = step inc→

halting-state : (σ : CState {Z₀ = Z₀}) → Normal σ → Σ[ W ∈ MVal Z₀ ] σ ≡ ⟨ W ╎ ◻ ⟩
halting-state ⟨ 𝐖 ╎ ◻ ⟩ normal  = 𝐖 , refl
halting-state ⟨ 𝐖 ╎ < M ； γ >∷ K ⟩ normal = ql (normal return→) _
halting-state ⟨ return _ ╎ γ ╎ K ⟩ normal = ql (normal run→) _
halting-state ⟨ pm _ _ ╎ γ ╎ K ⟩ normal = ql (normal pmᶜ→) _
halting-state ⟨ push _ _ ╎ γ ╎ K ⟩ normal = ql (normal push→) _
halting-state ⟨ app _ _ ╎ γ ╎ K ⟩ normal = ql (normal app→) _
halting-state ⟨ rec _ _ ╎ γ ╎ K ⟩ normal = ql (normal rec→) _
halting-state ⟨ inc _ _ ╎ γ ╎ K ⟩ normal = ql (normal inc→) _


eval-acc : {Z₀ : Ty} {σ : CState {Z₀ = Z₀}} → SN σ → Σ[ σ' ∈ CState ] Σ[ 𝐖 ∈ MVal {Z₀ = Z₀} Z₀ ] Σ[ NF ∈ Normal σ' ] (σ →ᶜ* σ') × (𝐖 ≡ proj₁ (halting-state σ' NF))
eval-acc {σ = σ} (sn f) with progress σ
... | done NF    = σ , proj₁ (halting-state σ NF) , NF , (σ ◼) , refl
... | step s with eval-acc (f s)
...   | (σ'' , 𝐖 , NF , ss , eq) = σ'' , 𝐖 , NF , (_ →ᶜ⟨ s ⟩ ss) , eq

eval : {Z₀ : Ty} → (M : Comp ε Z₀) → Σ[ σ' ∈ CState ] Σ[ 𝐖 ∈ MVal {Z₀ = Z₀} Z₀ ] Σ[ NF ∈ Normal σ' ] (⟨ M ╎ ⋄ ╎ ◻ ⟩ →ᶜ* σ') × (𝐖 ≡ proj₁ (halting-state σ' NF))
eval M = eval-acc (SN-theorem M)

\end{code}
