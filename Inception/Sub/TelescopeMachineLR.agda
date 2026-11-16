{-# OPTIONS --no-postfix-projections #-}

open import Inception.Sub.Syntax using (Ty)

module Inception.Sub.TelescopeMachineLR (ℛ : Ty) where

open import Inception.Prelude
open import Inception.Sub.Syntax

open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Unit using (⊤; tt)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

open import Inception.Sub.TelescopeMachine ℛ

open import Inception.Rewriting.Reduction _→ᶜ_

--------------------------------------------------------------------------
-- environment extension

data Ext : Δ ⊇ Γ → MEnv Δ → MEnv Γ → Set where

  ext-id   : {γ : MEnv Γ}
           → Ext wk-id γ γ

  ext-val  : {π : Δ ⊇ Γ} {γ₁ : MEnv Δ} {γ : MEnv Γ} {𝐖 : OMVal Δ X}
           → Ext π γ₁ γ
           → Ext (wk-wk π) (γ₁ · 𝐖) γ

  ext-jump : {π : Δ ⊇ Γ} {γ₁ : MEnv Δ} {γ : MEnv Γ} {M : Δ ⊢ᶜ X} {δ : Δ ⊇ Ψ} {K : CStack Ψ X}
           → Ext π γ₁ γ
           → Ext (wk-wk π) (γ₁ ·﹝ M ╎ δ ╎ K ﹞) γ

ext-trans : {π : Δ ⊇ Γ} {δ : Ψ ⊇ Δ} {γ : MEnv Γ} {γ₁ : MEnv Δ} {γ₂ : MEnv Ψ}
          → Ext π γ₁ γ → Ext δ γ₂ γ₁ → Ext (wk-trans δ π) γ₂ γ
ext-trans e ext-id        = e
ext-trans e₁ (ext-val e₂)  = ext-val (ext-trans e₁ e₂)
ext-trans e₁ (ext-jump e₂) = ext-jump (ext-trans e₁ e₂)

ext-lookup : {π : Δ ⊇ Γ} {γ₁ : MEnv Δ} {γ : MEnv Γ}
           → Ext π γ₁ γ → (i : Γ ∋ X) → lookup (wk-mem π i) γ₁ ≡ wk-omval π (lookup i γ)
ext-lookup ext-id       i = refl
ext-lookup (ext-val e)  i = cong (wk-omval (wk-wk wk-id)) (ext-lookup e i)
ext-lookup (ext-jump e) i = cong (wk-omval (wk-wk wk-id)) (ext-lookup e i)

ext-label : {π : Δ ⊇ Γ} {γ₁ : MEnv Δ} {γ : MEnv Γ}
          → Ext π γ₁ γ → (i : Γ ∋ `ℓ) → lookup-label (wk-mem π i) γ₁ ≡ lookup-label i γ
ext-label ext-id       i = refl
ext-label (ext-val e)  i = ext-label e i
ext-label (ext-jump e) i = ext-label e i

stack-env : CStack Γ X → MEnv Γ
stack-env ◻ = ⋄
stack-env (< N ； γ ； π >∷ K) = γ

--------------------------------------------------------------------------
-- reducibility

mutual

  Rᵛ : (X : Ty) → OMVal Γ X → MEnv Γ → Set
  Rᵛ `𝟙 unit γ = ⊤
  Rᵛ (X `× Y) (pair 𝐕 𝐖) γ = Rᵛ X 𝐕 γ × Rᵛ Y 𝐖 γ
  Rᵛ {Γ = Γ} (X `⇒ Y) (lam M) γ =
    ∀ {Δ} {γ₁ : MEnv Δ} {π : Δ ⊇ Γ} → Ext π γ₁ γ
    → ∀ {𝐖} → Rᵛ X 𝐖 γ₁
    → ∀ {Ψ} {δ : Δ ⊇ Ψ} {K : CStack Ψ Y} → Ext δ γ₁ (stack-env K) → Rᵏ Y K
    → SN ⟨ wk-comp (wk-cong π) M ╎ γ₁ · 𝐖 ╎ wk-wk δ ╎ K ⟩
  Rᵛ `ℓ (label i) γ = SN (lookup-label i γ)

  Rᵏ : (X : Ty) → CStack Γ X → Set
  Rᵏ {Γ = Γ} X K =
    ∀ {Δ} {γ : MEnv Δ} {π : Δ ⊇ Γ} → Ext π γ (stack-env K)
    → ∀ {𝐖} → Rᵛ X 𝐖 γ
    → SN ⟨ 𝐖 ； γ ╎ π ╎ K ⟩

Rᵏ-◻ : Rᵏ ℛ ◻
Rᵏ-◻ e rw = sn λ ()

--------------------------------------------------------------------------
-- monotonicity

Rᵛ-wk : {π : Δ ⊇ Γ} {γ₁ : MEnv Δ} {γ : MEnv Γ}
      → (X : Ty) (𝐖 : OMVal Γ X) → Ext π γ₁ γ → Rᵛ X 𝐖 γ → Rᵛ X (wk-omval π 𝐖) γ₁
Rᵛ-wk `𝟙 unit e rw = tt
Rᵛ-wk (X `× Y) (pair 𝐕 𝐖) e (rv , rw) = Rᵛ-wk X 𝐕 e rv , Rᵛ-wk Y 𝐖 e rw
Rᵛ-wk (X `⇒ Y) (lam M) e rw e₁ = rw (ext-trans e e₁)
Rᵛ-wk `ℓ (label i) e rw = subst SN (sym (ext-label e i)) rw

--------------------------------------------------------------------------
-- good environments

Rᴱ : Δ ⊇ Γ → MEnv Δ → Set
Rᴱ {Γ = Γ} π γ = ∀ {X} (i : Γ ∋ X) → Rᵛ X (lookup (wk-mem π i) γ) γ

Rᴱ-ε : {π : Δ ⊇ ε} {γ : MEnv Δ} → Rᴱ π γ
Rᴱ-ε ()

Rᴱ-wk : {π : Δ ⊇ Γ} {δ : Ψ ⊇ Δ} {γ : MEnv Δ} {γ₁ : MEnv Ψ}
      → Rᴱ π γ → Ext δ γ₁ γ → Rᴱ (wk-trans δ π) γ₁
Rᴱ-wk {π = π} {γ₁ = γ₁} rγ e {X = X} i =
  subst (λ 𝐕 → Rᵛ X 𝐕 γ₁) (sym (ext-lookup e (wk-mem π i))) (Rᵛ-wk X _ e (rγ i))

Rᴱ-val : {π : Δ ⊇ Γ} {γ : MEnv Δ} {𝐖 : OMVal Δ X}
       → Rᴱ π γ → Rᵛ X 𝐖 γ → Rᴱ (wk-cong π) (γ · 𝐖)
Rᴱ-val {X = X} {𝐖 = 𝐖} rγ rw here = Rᵛ-wk X 𝐖 (ext-val ext-id) rw
Rᴱ-val rγ rw {X = X} (there i) = Rᵛ-wk X _ (ext-val ext-id) (rγ i)

Rᴱ-jump : {π : Δ ⊇ Γ} {γ : MEnv Δ} {M : Δ ⊢ᶜ X} {δ : Δ ⊇ Ψ} {K : CStack Ψ X}
        → Rᴱ π γ → SN ⟨ M ╎ γ ╎ δ ╎ K ⟩ → Rᴱ (wk-cong π) (γ ·﹝ M ╎ δ ╎ K ﹞)
Rᴱ-jump rγ rm here = rm
Rᴱ-jump rγ rm {X = X} (there i) = Rᵛ-wk X _ (ext-jump ext-id) (rγ i)

--------------------------------------------------------------------------
-- eliminations

Rᵛ-proj₁ : {γ : MEnv Γ} → (𝐖 : OMVal Γ (X `× Y)) → Rᵛ _ 𝐖 γ → Rᵛ X (proj₁-omval 𝐖) γ
Rᵛ-proj₁ (pair 𝐕 𝐖) (rv , rw) = rv

Rᵛ-proj₂ : {γ : MEnv Γ} → (𝐖 : OMVal Γ (X `× Y)) → Rᵛ _ 𝐖 γ → Rᵛ Y (proj₂-omval 𝐖) γ
Rᵛ-proj₂ (pair 𝐕 𝐖) (rv , rw) = rw

Rᵛ-app : {γ : MEnv Γ} {𝐖 : OMVal Γ X} {δ : Γ ⊇ Ψ} {K : CStack Ψ Y}
       → (𝐕 : OMVal Γ (X `⇒ Y)) → Rᵛ _ 𝐕 γ → Rᵛ X 𝐖 γ → Ext δ γ (stack-env K) → Rᵏ Y K
       → SN ⟨ lam-to-comp 𝐕 ╎ γ · 𝐖 ╎ wk-wk δ ╎ K ⟩
Rᵛ-app (lam M) rv rw e rk = rv ext-id rw e rk

Rᵛ-label : {π : Δ ⊇ Γ} {γ₁ : MEnv Δ} {γ : MEnv Γ}
         → (𝐖 : OMVal Γ `ℓ) → Ext π γ₁ γ → Rᵛ `ℓ (wk-omval π 𝐖) γ₁ → Rᵛ `ℓ 𝐖 γ
Rᵛ-label (label i) e rw = subst SN (ext-label e i) rw

Rᵛ-jump : (i : Γ ∋ `ℓ) {γ : MEnv Γ} → Rᵛ `ℓ (lookup i γ) γ → SN (lookup-label i γ)
Rᵛ-jump here {γ = γ · label j} rw = rw
Rᵛ-jump here {γ = γ ·﹝ M ╎ π ╎ K ﹞} rw = rw
Rᵛ-jump (there i) {γ = γ · 𝐖} rw = Rᵛ-jump i (Rᵛ-label (lookup i γ) (ext-val ext-id) rw)
Rᵛ-jump (there i) {γ = γ ·﹝ M ╎ π ╎ K ﹞} rw = Rᵛ-jump i (Rᵛ-label (lookup i γ) (ext-jump ext-id) rw)

--------------------------------------------------------------------------
-- fundamental lemma

mutual

  fundamentalᵛ : (W : Γ ⊢ᵛ X) → {π : Δ ⊇ Γ} {γ : MEnv Δ} → Rᴱ π γ → Rᵛ X (eval (wk-val π W) γ) γ
  fundamentalᵛ (var i) rγ = rγ i
  fundamentalᵛ (lam M) {π = π} rγ e rw e₁ rk = fundamentalᶜ M (Rᴱ-val (Rᴱ-wk {π = π} rγ e) rw) (ext-val e₁) rk
  fundamentalᵛ (pair V W) rγ = fundamentalᵛ V rγ , fundamentalᵛ W rγ
  fundamentalᵛ unit rγ = tt

  fundamentalᶜ : (M : Γ ⊢ᶜ X) → {π : Δ ⊇ Γ} {γ : MEnv Δ} → Rᴱ π γ
               → {δ : Δ ⊇ Ψ} {K : CStack Ψ X} → Ext δ γ (stack-env K) → Rᵏ X K
               → SN ⟨ wk-comp π M ╎ γ ╎ δ ╎ K ⟩
  fundamentalᶜ (return W) rγ e rk =
    sn λ { eval→ → rk e (fundamentalᵛ W rγ) }
  fundamentalᶜ (sub M N) rγ e rk =
    sn λ { sub→ → fundamentalᶜ M (Rᴱ-jump rγ (fundamentalᶜ N rγ e rk)) (ext-jump e) rk }
  fundamentalᶜ (pm W M) {π = π} {γ = γ} rγ e rk =
    sn λ { pmᶜ→ → fundamentalᶜ M (Rᴱ-val (Rᴱ-val rγ rv) (Rᵛ-wk _ _ (ext-val ext-id) rw)) (ext-val (ext-val e)) rk }
    where
      𝐖 = eval (wk-val π W) γ
      rv = Rᵛ-proj₁ 𝐖 (fundamentalᵛ W rγ)
      rw = Rᵛ-proj₂ 𝐖 (fundamentalᵛ W rγ)
  fundamentalᶜ (push M N) {π = π} {γ = γ} rγ {δ = δ} {K = K} e rk =
    sn λ { push→ → fundamentalᶜ M rγ ext-id rk₁ }
    where
      rk₁ : Rᵏ _ (< wk-comp (wk-cong π) N ； γ ； δ >∷ K)
      rk₁ e₁ rw = sn λ { return→ → fundamentalᶜ N (Rᴱ-val (Rᴱ-wk {π = π} rγ e₁) rw) (ext-val (ext-trans e e₁)) rk }
  fundamentalᶜ (app V W) {π = π} {γ = γ} rγ e rk =
    sn λ { app→ → Rᵛ-app (eval (wk-val π V) γ) (fundamentalᵛ V rγ) (fundamentalᵛ W rγ) e rk }
  fundamentalᶜ (var (var i)) {π = π} rγ e rk =
    sn λ { var→ → Rᵛ-jump (wk-mem π i) (rγ i) }

--------------------------------------------------------------------------
-- strong normalisation

SN-theorem : (M : ε ⊢ᶜ ℛ) → SN ⟨ M ╎ ⋄ ╎ wk-ε ╎ ◻ ⟩
SN-theorem M = fundamentalᶜ M {π = wk-ε} (Rᴱ-ε {π = wk-ε}) ext-id Rᵏ-◻

exec : (M : ε ⊢ᶜ ℛ) → Σ[ σ ∈ CState ] Σ[ NF ∈ Normal σ ] ⟨ M ╎ ⋄ ╎ wk-ε ╎ ◻ ⟩ ~>* σ
exec M with eval-acc progress (SN-theorem M)
... | (σ , r , n) = σ , n , r

