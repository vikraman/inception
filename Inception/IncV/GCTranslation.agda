{-# OPTIONS --no-postfix-projections #-}

open import Inception.IncV.Data
import Inception.IncV.Syntax as Syntax using (Ty)
module Inception.IncV.GCTranslation (𝒜 : Alg) (ℛ : Syntax.Ty 𝒜) where

open import Inception.IncV.Syntax 𝒜
open import Inception.Prelude
open import Inception.Rewriting

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; cong; cong₂; sym; dcong₂; trans)

open import Inception.IncV.GCMachine 𝒜 ℛ as GCM renaming (_→ᶜ_ to _→ᴳ_)
open import Inception.IncV.Machine 𝒜 ℛ as M renaming (_→ᶜ_ to _→ᴹ_)

open import Inception.IncV.MachineProps 𝒜 ℛ as MProps

open import Data.Vec

--------------------------------------------------------------------------
-- translation of telescope environments into list environments
--------------------------------------------------------------------------

mutual

  gcmcstack-to-mcstack : GCM.MEnv Γ → {π : Γ ⊇ Δ} → (p : WkExt π) → GCM.CStack Δ X → M.CStack X
  gcmcstack-to-mcstack _ _ ◻ = ◻
  gcmcstack-to-mcstack γ p (< M ； p₁ >∷ K) = < M ； gcmenv-to-menv γ p >∷ gcmcstack-to-mcstack γ (wkext-trans p p₁) K

  gcmenv-to-menv : GCM.MEnv Γ → {π : Γ ⊇ Δ} → (p : WkExt π) → M.MEnv Δ
  gcmenv-to-menv ⋄ wkext-id = ⋄
  gcmenv-to-menv (γ · 𝐖) {π = wk-cong π} wkext-id = gcmenv-to-menv γ {π = π} wkext-id · omval-to-mval γ 𝐖
  gcmenv-to-menv (γ · 𝐖) {π = wk-wk π} wkext-id = ql (wk-absurd wk-id π) _
  gcmenv-to-menv (γ · 𝐖) {π = wk-wk π} (wkext-wk p) = gcmenv-to-menv γ p
  gcmenv-to-menv (γ ·﹝ M ╎ p ╎ K ﹞) {π = wk-cong π} wkext-id = let γ₁ = gcmenv-to-menv γ {π = π} wkext-id in γ₁ · jumpᵛ M γ₁ (gcmcstack-to-mcstack γ p K)
  gcmenv-to-menv (γ ·﹝ M ╎ p ╎ K ﹞) {π = wk-wk π} wkext-id = ql (wk-absurd wk-id π) _
  gcmenv-to-menv (γ ·﹝ M ╎ p ╎ K ﹞) {π = wk-wk π} (wkext-wk p₁) = gcmenv-to-menv γ p₁

  omval-to-mval : GCM.MEnv Γ → GCM.OMVal Γ X → M.MVal X
  omval-to-mval γ unit = unitᵛ
  omval-to-mval γ (dat D) = datᵛ D
  omval-to-mval γ (pair 𝐕 𝐖) = pairᵛ (omval-to-mval γ 𝐕) (omval-to-mval γ 𝐖)
  omval-to-mval γ (lam M) = cloᵛ M (gcmenv-to-menv γ {π = wk-id} wkext-id)
  omval-to-mval ⋄ (var ())
  omval-to-mval (γ · 𝐖) (var here) = omval-to-mval γ 𝐖
  omval-to-mval (γ · 𝐖) (var (there i)) = omval-to-mval γ (var i)
  omval-to-mval (γ ·﹝ M ╎ p ╎ K ﹞) (var here) = jumpᵛ M (gcmenv-to-menv γ {π = wk-id} wkext-id) (gcmcstack-to-mcstack γ p K)
  omval-to-mval (γ ·﹝ M ╎ p ╎ K ﹞) (var (there i)) = omval-to-mval γ (var i)

gcmcstate-to-mcstate : GCM.CState → M.CState
gcmcstate-to-mcstate ⟨ γ ； 𝐖 ╎ p ╎ K ⟩ = ⟨ omval-to-mval γ 𝐖 ╎ gcmcstack-to-mcstack γ p K ⟩
gcmcstate-to-mcstate ⟨ γ ╎ M ╎ p ╎ K ⟩ = ⟨ M ╎ gcmenv-to-menv γ {π = wk-id} wkext-id ╎ gcmcstack-to-mcstack γ p K ⟩

--------------------------------------------------------------------------

menvext-to-wkext : {π : Γ ⊇ Δ} {γ : GCM.MEnv Γ} {δ : GCM.MEnv Δ} → MEnvExt π γ δ → WkExt π
menvext-to-wkext {π = wk-ε} {γ = ⋄} {δ = ⋄} (menv-id π γ) = wkext-id
menvext-to-wkext {π = wk-cong π} {γ = γ · x} {δ = δ · _} (menv-id π₁ γ₁) = wkext-id
menvext-to-wkext {π = wk-cong π} {γ = γ · x} {δ = δ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞} ()
menvext-to-wkext {π = wk-cong π} {γ = γ ·﹝ x ╎ x₁ ╎ x₂ ﹞} {δ = δ · x₃} ()
menvext-to-wkext {π = wk-cong π} {γ = γ ·﹝ x ╎ x₁ ╎ x₂ ﹞} {δ = δ ·﹝ _ ╎ _ ╎ _ ﹞} (menv-id π₁ γ₁) = wkext-id
menvext-to-wkext {π = wk-wk π} {γ = γ · x} {δ = ⋄} (menv-wk-omval mx 𝐖) = wkext-wk (menvext-to-wkext mx)
menvext-to-wkext {π = wk-wk π} {γ = γ · x} {δ = δ · _} (menv-id π₁ γ₁) = wkext-id
menvext-to-wkext {π = wk-wk π} {γ = γ · x} {δ = δ · x₁} (menv-wk-omval mx 𝐖) = wkext-wk (menvext-to-wkext mx)
menvext-to-wkext {π = wk-wk π} {γ = γ · x} {δ = δ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞} (menv-wk-omval mx 𝐖) = wkext-wk (menvext-to-wkext mx)
menvext-to-wkext {π = wk-wk π} {γ = γ ·﹝ x ╎ x₁ ╎ x₂ ﹞} {δ = ⋄} (menv-wk-jump mx M r K) = wkext-wk (menvext-to-wkext mx)
menvext-to-wkext {π = wk-wk π} {γ = γ ·﹝ x ╎ x₁ ╎ x₂ ﹞} {δ = δ · x₃} (menv-wk-jump mx M r K) = wkext-wk (menvext-to-wkext mx)
menvext-to-wkext {π = wk-wk π} {γ = γ ·﹝ x ╎ x₁ ╎ x₂ ﹞} {δ = δ ·﹝ _ ╎ _ ╎ _ ﹞} (menv-id π₁ γ₁) = wkext-id
menvext-to-wkext {π = wk-wk π} {γ = γ ·﹝ x ╎ x₁ ╎ x₂ ﹞} {δ = δ ·﹝ x₃ ╎ x₄ ╎ x₅ ﹞} (menv-wk-jump mx M r K) = wkext-wk (menvext-to-wkext mx)

wkext-π-uniq : {π₁ π₂ : Γ ⊇ Δ} → WkExt π₁ → WkExt π₂ → π₁ ≡ π₂
wkext-π-uniq {π₁ = wk-ε} {π₂ = wk-ε} wkext-id wkext-id = refl
wkext-π-uniq {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} wkext-id wkext-id = cong wk-cong (wkext-π-uniq wkext-id wkext-id)
wkext-π-uniq {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} wkext-id wkext-id = ql (wk-absurd wk-id π₂) _
wkext-π-uniq {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} wkext-id (wkext-wk p₂) = ql (wk-absurd π₂ π₁) _
wkext-π-uniq {π₁ = wk-wk π₁} {π₂ = wk-cong π₂} wkext-id wkext-id = ql (wk-absurd π₁ π₂) _
wkext-π-uniq {π₁ = wk-wk π₁} {π₂ = wk-cong π₂} (wkext-wk p₁) wkext-id = ql (wk-absurd wk-id π₁) _
wkext-π-uniq {π₁ = wk-wk π₁} {π₂ = wk-wk π₂} wkext-id wkext-id = ql (wk-absurd wk-id π₂) _
wkext-π-uniq {π₁ = wk-wk π₁} {π₂ = wk-wk π₂} wkext-id (wkext-wk p₂) = ql (wk-absurd wk-id π₁) _
wkext-π-uniq {π₁ = wk-wk π₁} {π₂ = wk-wk π₂} (wkext-wk p₁) wkext-id = ql (wk-absurd wk-id π₁) _
wkext-π-uniq {π₁ = wk-wk π₁} {π₂ = wk-wk π₂} (wkext-wk p₁) (wkext-wk p₂) = cong wk-wk (wkext-π-uniq p₁ p₂)

wkext-uniq : {π : Γ ⊇ Δ} → (p₁ : WkExt π) → (p₂ : WkExt π) → p₁ ≡ p₂
wkext-uniq wkext-id wkext-id = refl
wkext-uniq {π = wk-wk π} wkext-id (wkext-wk p₂) = ql (wk-absurd (wk-wk π) π) _
wkext-uniq {π = wk-wk π} (wkext-wk p₁) wkext-id = ql (wk-absurd (wk-wk π) π) _
wkext-uniq (wkext-wk p₁) (wkext-wk p₂) = cong wkext-wk (wkext-uniq p₁ p₂)

---- lemmas for eval→ case

open GCM.EvalGC
open GCM.WkExtSplit
open GCM.DiamondSplit

wk-omval-id-β : {𝐖 : GCM.OMVal Γ X} → wk-omval wk-id 𝐖 ≡ 𝐖
wk-omval-id-β {𝐖 = unit} = refl
wk-omval-id-β {𝐖 = pair 𝐕 𝐖} = cong₂ pair wk-omval-id-β wk-omval-id-β
wk-omval-id-β {𝐖 = lam M} = cong lam (wk-comp-id-β M)
wk-omval-id-β {𝐖 = var i} = refl
wk-omval-id-β {𝐖 = dat D} = refl

omval-dat : (γ : GCM.MEnv Γ) → {π : Γ ⊇ Δ} → (p : WkExt π) → (D : 𝒟) → (omval-to-mval (ψ-gc (eval-gc γ p (dat D))) (result (eval-gc γ p (dat D)))) ≡ (datᵛ D)
omval-dat ⋄ wkext-id D = refl
omval-dat (γ · x) wkext-id D = refl
omval-dat (γ · x) (wkext-wk p) D = refl
omval-dat (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) wkext-id D = refl
omval-dat (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (wkext-wk p) D = refl

omval-op : (γ : GCM.MEnv Γ) → {π : Γ ⊇ Δ} → (p : WkExt π) → (o : 𝒪) → (a : Vec 𝒟 ∣ o ∣) → (omval-to-mval (ψ-gc (eval-gc γ p (op o a))) (result (eval-gc γ p (op o a)))) ≡ (datᵛ (Alg.apply 𝒜 o a))
omval-op ⋄ wkext-id o a = refl
omval-op (γ · x) wkext-id o a = refl
omval-op (γ · x) (wkext-wk p) o a = refl
omval-op (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) wkext-id o a = refl
omval-op (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (wkext-wk p) o a = refl

omval-unit : (γ : GCM.MEnv Γ) → (W : GCM.OMVal Γ `𝟙) → omval-to-mval γ W ≡ unitᵛ
omval-unit γ unit = refl
omval-unit (γ · 𝐖) (var here) = omval-unit γ 𝐖
omval-unit (γ · 𝐖) (var (there i)) = omval-unit γ (var i)
omval-unit (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (var (there i)) = omval-unit γ (var i)

omval-wk-drop₁ : (𝐕 : GCM.OMVal Γ Y) → (𝐖 : GCM.OMVal Δ X) → (π : Γ ⊇ Δ) → (γ : GCM.MEnv Γ)
                → WkMVal (omval-to-mval (γ · 𝐕) (wk-omval (Wk.wk-wk π) 𝐖)) (omval-to-mval γ (wk-omval π 𝐖))
omval-wk-drop₁ 𝐕 unit π γ = wk-unitᵛ
omval-wk-drop₁ 𝐕 (pair 𝐖₁ 𝐖₂) π γ = wk-pairᵛ (omval-wk-drop₁ 𝐕 𝐖₁ π γ) (omval-wk-drop₁ 𝐕 𝐖₂ π γ)
omval-wk-drop₁ 𝐕 (lam M) π γ = wk-cloᵛ (wk-wk wk-id) (wk-comp-id-β (wk-comp (wk-cong (Wk.wk-wk π)) M)) (wk-menv-wk (omval-to-mval γ 𝐕) wk-menv-id)
omval-wk-drop₁ 𝐕 (var i) π γ = wk-mval-id
omval-wk-drop₁ 𝐕 (dat D) π γ = wk-mval-id

omval-wk-drop₂ : (M : (Γ ∙ `𝓅) ⊢ᶜ Y) → {ρ : Γ ⊇ Ψ} → (r : WkExt ρ) → (K : GCM.CStack Ψ Y) → (𝐖 : GCM.OMVal Δ X) → (π : Γ ⊇ Δ) → (γ : GCM.MEnv Γ)
                → WkMVal (omval-to-mval (γ ·﹝ M ╎ r ╎ K ﹞) (wk-omval (Wk.wk-wk π) 𝐖)) (omval-to-mval γ (wk-omval π 𝐖))
omval-wk-drop₂ M r K unit π γ = wk-unitᵛ
omval-wk-drop₂ M r K (dat D) π γ = wk-datᵛ
omval-wk-drop₂ M r K (pair 𝐕 𝐖) π γ = wk-pairᵛ (omval-wk-drop₂ M r K 𝐕 π γ) (omval-wk-drop₂ M r K 𝐖 π γ)
omval-wk-drop₂ M r K (lam N) π γ = wk-cloᵛ (Wk.wk-wk wk-id) refl (wk-menv-wk (jumpᵛ M (gcmenv-to-menv γ wkext-id) (gcmcstack-to-mcstack γ r K)) wk-menv-id)
omval-wk-drop₂ M r K (var i) π γ = wk-mval-id

omval-wk : (𝐖 : GCM.OMVal Δ X) → {π : Γ ⊇ Δ} → {γ : GCM.MEnv Γ} → {δ : GCM.MEnv Δ} → MEnvExt π γ δ
           → WkMVal (omval-to-mval γ (wk-omval π 𝐖)) (omval-to-mval δ 𝐖)
omval-wk 𝐖 (menv-id π γ) rewrite wk-id-η π | wk-omval-id-β {𝐖 = 𝐖} = wk-mval-id
omval-wk 𝐖 {π = (wk-wk π)} {γ = γ · _} {δ = δ} (menv-wk-omval mx 𝐕) = wk-mval-trans (omval-wk-drop₁ 𝐕 𝐖 π γ) (omval-wk 𝐖 mx)
omval-wk 𝐖 {π = (wk-wk π)} {γ = γ ·﹝ M ╎ r ╎ K ﹞} {δ = δ} (menv-wk-jump mx M r K) = wk-mval-trans (omval-wk-drop₂ M r K 𝐖 π γ) (omval-wk 𝐖 mx)

gc-wkext-id : (γ : GCM.MEnv Γ) → (π : Γ ⊇ Γ) → gc γ {π = π} wkext-id ≡ γ
gc-wkext-id ⋄ wk-ε = refl
gc-wkext-id (γ · x) (wk-cong π) = refl
gc-wkext-id (γ · x) (wk-wk π) = refl
gc-wkext-id (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (wk-cong π) = refl
gc-wkext-id (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (wk-wk π) = refl

gc-menvext-l : (γ : GCM.MEnv Γ) → (δ : GCM.MEnv Δ) → {π₁ : Γ ⊇ Ψ} → (p₁ : WkExt π₁) → {π₂ : Ψ ⊇ Δ} → (p₂ : WkExt π₂) → {π₃ : Γ ⊇ Δ} → (MEnvExt π₃ γ δ) → MEnvExt π₂ (gc γ p₁) δ
gc-menvext-l γ δ {π₁ = π₁} wkext-id wkext-id (menv-id π γ₁) rewrite gc-wkext-id γ π₁ = menv-id _ γ
gc-menvext-l γ δ {π₁ = π₁} wkext-id wkext-id (menv-wk-omval {π = π} mx 𝐖) rewrite gc-wkext-id γ π₁ = ql (wk-absurd wk-id π) _
gc-menvext-l γ δ {π₁ = π₁} wkext-id wkext-id (menv-wk-jump {π = π} mx M r K) rewrite gc-wkext-id γ π₁ = ql (wk-absurd wk-id π) _
gc-menvext-l γ δ {π₁ = π₁} wkext-id {π₂ = wk-wk π₂} (wkext-wk p₂) (menv-id π γ₁) = ql (wk-absurd wk-id π₂) _
gc-menvext-l (γ · 𝐖) δ {π₁ = π₁} wkext-id {π₂ = wk-wk π₂} (wkext-wk p₂) (menv-wk-omval {π = π₃} mx 𝐖) rewrite gc-wkext-id (γ · 𝐖) π₁ =
  let
    m : MEnvExt π₂ γ δ
    m = subst (λ x → MEnvExt x γ δ) (wkext-π-uniq (menvext-to-wkext mx) p₂) mx
  in
  menv-wk-omval m 𝐖
gc-menvext-l (γ ·﹝ M ╎ r ╎ K ﹞) δ {π₁ = π₁} wkext-id {π₂ = wk-wk π₂} (wkext-wk p₂) (menv-wk-jump {π = π₃} mx M r K) rewrite gc-wkext-id (γ ·﹝ M ╎ r ╎ K ﹞) π₁ =
  let
    m : MEnvExt π₂ γ δ
    m = subst (λ x → MEnvExt x γ δ) (wkext-π-uniq (menvext-to-wkext mx) p₂) mx
  in
  menv-wk-jump m M r K
gc-menvext-l γ δ {π₁ = wk-wk π₁} (wkext-wk p₁) {π₂ = π₂} p₂ {π₃ = π₃} (menv-id π γ₁) = ql (wk-absurd wk-id (wk-trans π₁ π₂)) _
gc-menvext-l γ δ (wkext-wk p₁) p₂ (menv-wk-omval mx 𝐖) = gc-menvext-l _ δ p₁ p₂ mx
gc-menvext-l γ δ (wkext-wk p₁) p₂ (menv-wk-jump mx M r K) = gc-menvext-l _ δ p₁ p₂ mx

lookup-next-eq : (γ : GCM.MEnv Γ) → (i : Γ ∋ X) → (M.lookup i (gcmenv-to-menv γ {π = wk-id} wkext-id)) ≡ (M.lookup here (gcmenv-to-menv (γ · var i) {π = wk-id} wkext-id))
lookup-next-eq ⋄ ()
lookup-next-eq (γ · x) here = refl
lookup-next-eq (γ · x) (there i) = lookup-next-eq γ i
lookup-next-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here = refl
lookup-next-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) = lookup-next-eq γ i

lookup-ctx-wk : (γ : GCM.MEnv Γ) → (i : Γ ∋ X) → (𝐖 : OMVal Γ Y) → (π : Γ ⊇ Γ) → (Ψ-gc (lookup-gc (γ · 𝐖) {π = wk-cong π} wkext-id (there i))) ⊇ (Ψ-gc (lookup-gc γ {π = π} wkext-id i))
lookup-ctx-wk ⋄ () 𝐖 π
lookup-ctx-wk (γ · x) here 𝐖 (wk-cong π) = Wk.wk-wk (Wk.wk-cong π)
lookup-ctx-wk (γ · x) here 𝐖 (wk-wk π) = Wk.wk-wk (Wk.wk-wk π)
lookup-ctx-wk (γ · x) (there i) 𝐖 (wk-cong π) = Wk.wk-wk (Wk.wk-cong π)
lookup-ctx-wk (γ · x) (there i) 𝐖 (wk-wk π) = ql (wk-absurd wk-id π) _
lookup-ctx-wk (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here 𝐖 (wk-cong π) = Wk.wk-wk (Wk.wk-cong π)
lookup-ctx-wk (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here 𝐖 (wk-wk π) = Wk.wk-wk (Wk.wk-wk π)
lookup-ctx-wk (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) 𝐖 (wk-cong π) = Wk.wk-wk (Wk.wk-cong π)
lookup-ctx-wk (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) 𝐖 (wk-wk π) = Wk.wk-wk (Wk.wk-wk π)

lookup-ctx-label-wk : (γ : GCM.MEnv Γ) → (i : Γ ∋ X) → (M : (Γ ∙ `𝓅) ⊢ᶜ Y) → {ρ : Γ ⊇ Δ} → (r : WkExt ρ) → (K : GCM.CStack Δ Y) → (π : Γ ⊇ Γ)
                      → (Ψ-gc (lookup-gc (γ ·﹝ M ╎ r ╎ K ﹞) {π = wk-cong π} wkext-id (there i))) ⊇ (Ψ-gc (lookup-gc γ {π = π} wkext-id i))
lookup-ctx-label-wk ⋄ () M r K π
lookup-ctx-label-wk (γ · x) here M r K (wk-cong π) = Wk.wk-wk (Wk.wk-cong π)
lookup-ctx-label-wk (γ · x) here M r K (wk-wk π) = Wk.wk-wk (Wk.wk-wk π)
lookup-ctx-label-wk (γ · x) (there i) M r K (wk-cong π) = Wk.wk-wk (Wk.wk-cong π)
lookup-ctx-label-wk (γ · x) (there i) M r K (wk-wk π) = ql (wk-absurd wk-id π) _
lookup-ctx-label-wk (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here M r K (wk-cong π) = Wk.wk-wk (Wk.wk-cong π)
lookup-ctx-label-wk (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here M r K (wk-wk π) = Wk.wk-wk (Wk.wk-wk π)
lookup-ctx-label-wk (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) M r K (wk-cong π) = Wk.wk-wk (Wk.wk-cong π)
lookup-ctx-label-wk (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) M r K (wk-wk π) = Wk.wk-wk (Wk.wk-wk π)

lookup-there-eq : (γ : GCM.MEnv Γ) → (i : Γ ∋ X) → (𝐖 : OMVal Γ Y) → (π : Γ ⊇ Γ) → wk-omval (lookup-ctx-wk γ i 𝐖 π) (result (lookup-gc γ wkext-id i)) ≡ (result (lookup-gc (γ · 𝐖) {π = wk-cong π} wkext-id (there i)))
lookup-there-eq ⋄ () 𝐖 π
lookup-there-eq (γ · 𝐕) here 𝐖 (wk-cong π) rewrite wk-id-η π = refl
lookup-there-eq (γ · x) here 𝐖 (wk-wk π) = ql (wk-absurd wk-id π) _
lookup-there-eq (γ · x) (there i) 𝐖 (wk-cong π) rewrite wk-id-η π = refl
lookup-there-eq (γ · x) (there i) 𝐖 (wk-wk π) = ql (wk-absurd wk-id π) _
lookup-there-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here 𝐖 (wk-cong π) = refl
lookup-there-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here 𝐖 (wk-wk π) = ql (wk-absurd wk-id π) _
lookup-there-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) 𝐖 (wk-cong π) rewrite wk-id-η π = refl
lookup-there-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) 𝐖 (wk-wk π) = ql (wk-absurd wk-id π) _

lookup-omval-eq : (γ : GCM.MEnv Γ) → (i : Γ ∋ X) → (𝐖 : OMVal Γ Y) → (π : Γ ⊇ Γ) →
                    (omval-to-mval (γ · 𝐖) (wk-omval (lookup-ctx-wk γ i 𝐖 π) (result (lookup-gc γ wkext-id i))))
                  ≡ (omval-to-mval (ψ-gc (lookup-gc (γ · 𝐖) {π = wk-cong π} wkext-id (there i))) (result (lookup-gc (γ · 𝐖) {π = wk-cong π} wkext-id (there i))))
lookup-omval-eq ⋄ () 𝐖 π
lookup-omval-eq (γ · x) here 𝐖 (wk-cong π) rewrite wk-id-η π = refl
lookup-omval-eq (γ · x) here 𝐖 (wk-wk π) = ql (wk-absurd wk-id π) _
lookup-omval-eq (γ · x) (there i) 𝐖 (wk-cong π) rewrite wk-id-η π = refl
lookup-omval-eq (γ · x) (there i) 𝐖 (wk-wk π) = ql (wk-absurd wk-id π) _
lookup-omval-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here 𝐖 (wk-cong π) = refl
lookup-omval-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here 𝐖 (wk-wk π) = ql (wk-absurd wk-id π) _
lookup-omval-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) 𝐖 (wk-cong π) rewrite wk-id-η π = refl
lookup-omval-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) 𝐖 (wk-wk π) = ql (wk-absurd wk-id π) _

lookup-omval-label-eq : (γ : GCM.MEnv Γ) → (i : Γ ∋ X) → (M : (Γ ∙ `𝓅) ⊢ᶜ Y) → {ρ : Γ ⊇ Δ} → (r : WkExt ρ) → (K : GCM.CStack Δ Y) → (π : Γ ⊇ Γ) →
                      (omval-to-mval (γ ·﹝ M ╎ r ╎ K ﹞) (wk-omval (lookup-ctx-label-wk γ i M r K π) (result (lookup-gc γ wkext-id i))))
                    ≡ (omval-to-mval (ψ-gc (lookup-gc (γ ·﹝ M ╎ r ╎ K ﹞) {π = wk-cong π} wkext-id (there i))) (result (lookup-gc (γ ·﹝ M ╎ r ╎ K ﹞) {π = wk-cong π} wkext-id (there i))))
lookup-omval-label-eq ⋄ () M r K π
lookup-omval-label-eq (γ · x) here M r K (wk-cong π) rewrite wk-id-η π = refl
lookup-omval-label-eq (γ · x) here M r K (wk-wk π) = ql (wk-absurd wk-id π) _
lookup-omval-label-eq (γ · x) (there i) M r K (wk-cong π) rewrite wk-id-η π = refl
lookup-omval-label-eq (γ · x) (there i) M r K (wk-wk π) = ql (wk-absurd wk-id π) _
lookup-omval-label-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here M r K (wk-cong π) = refl
lookup-omval-label-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here M r K (wk-wk π) = ql (wk-absurd wk-id π) _
lookup-omval-label-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) M r K (wk-cong π) rewrite wk-id-η π = refl
lookup-omval-label-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) M r K (wk-wk π) = ql (wk-absurd wk-id π) _

lookup-gc-menvext : (γ : GCM.MEnv Γ) → (i : Γ ∋ X) → (𝐖 : OMVal Γ Y) → (π : Γ ⊇ Γ) → MEnvExt (lookup-ctx-wk γ i 𝐖 π) (γ · 𝐖) (ψ-gc (lookup-gc γ {π = π} wkext-id i))
lookup-gc-menvext ⋄ () 𝐖 π
lookup-gc-menvext (γ · x) here 𝐖 (wk-cong π) = menv-wk-omval (menv-id (Wk.wk-cong π) (γ · x)) 𝐖
lookup-gc-menvext (γ · x) here 𝐖 (wk-wk π) = menv-wk-omval (menv-id (Wk.wk-wk π) (γ · x)) 𝐖
lookup-gc-menvext (γ · x) (there i) 𝐖 (wk-cong π) = menv-wk-omval (menv-id (Wk.wk-cong π) (γ · x)) 𝐖
lookup-gc-menvext (γ · x) (there i) 𝐖 (wk-wk π) = ql (wk-absurd wk-id π) _
lookup-gc-menvext (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here 𝐖 (wk-cong π) = menv-wk-omval (menv-id (Wk.wk-cong π) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) 𝐖
lookup-gc-menvext (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here 𝐖 (wk-wk π) = menv-wk-omval (menv-id (Wk.wk-wk π) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) 𝐖
lookup-gc-menvext (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) 𝐖 (wk-cong π) = menv-wk-omval (menv-id (Wk.wk-cong π) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) 𝐖
lookup-gc-menvext (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) 𝐖 (wk-wk π) = menv-wk-omval (menv-id (Wk.wk-wk π) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) 𝐖

lookup-gc-label-menvext : (γ : GCM.MEnv Γ) → (i : Γ ∋ X) → (M : (Γ ∙ `𝓅) ⊢ᶜ Y) → {ρ : Γ ⊇ Δ} → (r : WkExt ρ) → (K : GCM.CStack Δ Y) → (π : Γ ⊇ Γ) → MEnvExt (lookup-ctx-label-wk γ i M r K π) (γ ·﹝ M ╎ r ╎ K ﹞) (ψ-gc (lookup-gc γ {π = π} wkext-id i))
lookup-gc-label-menvext ⋄ () M r K π
lookup-gc-label-menvext (γ · x) here M r K (wk-cong π) = menv-wk-jump (menv-id (Wk.wk-cong π) (γ · x)) M r K
lookup-gc-label-menvext (γ · x) here M r K (wk-wk π) = menv-wk-jump (menv-id (Wk.wk-wk π) (γ · x)) M r K
lookup-gc-label-menvext (γ · x) (there i) M r K (wk-cong π) = menv-wk-jump (menv-id (Wk.wk-cong π) (γ · x)) M r K
lookup-gc-label-menvext (γ · x) (there i) M r K (wk-wk π) = ql (wk-absurd wk-id π) _
lookup-gc-label-menvext (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here M r K (wk-cong π) = menv-wk-jump (menv-id (Wk.wk-cong π) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) M r K
lookup-gc-label-menvext (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here M r K (wk-wk π) = menv-wk-jump (menv-id (Wk.wk-wk π) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) M r K
lookup-gc-label-menvext (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) M r K (wk-cong π) = menv-wk-jump (menv-id (Wk.wk-cong π) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) M r K
lookup-gc-label-menvext (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) M r K (wk-wk π) = menv-wk-jump (menv-id (Wk.wk-wk π) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) M r K

lookup-gc-wk : (γ : GCM.MEnv Γ) → (i : Γ ∋ X) → {π : Γ ⊇ Δ} → (p : WkExt π)
          → WkMVal (omval-to-mval (ψ-gc (lookup-gc γ p i)) (result (lookup-gc γ p i))) (M.lookup i (gcmenv-to-menv γ {π = wk-id} wkext-id))
lookup-gc-wk ⋄ () p
lookup-gc-wk (γ · 𝐖) here wkext-id =
  let
    goal : WkMVal (omval-to-mval (γ · 𝐖) (wk-omval (Wk.wk-wk wk-id) 𝐖)) (omval-to-mval γ 𝐖)
    goal = omval-wk 𝐖 (menv-wk-omval (menv-id wk-id γ) 𝐖)
  in
  goal

lookup-gc-wk (γ · unit) here (wkext-wk p) = wk-unitᵛ
lookup-gc-wk (γ · (dat D)) here (wkext-wk p) = wk-datᵛ
lookup-gc-wk (γ · pair 𝐕 𝐖) here (wkext-wk p) = wk-pairᵛ wk-mval-id wk-mval-id
lookup-gc-wk (γ · lam M) here (wkext-wk p) = wk-mval-id
lookup-gc-wk (γ · var i) here (wkext-wk p) rewrite sym (lookup-next-eq γ i) = lookup-gc-wk γ i p

lookup-gc-wk (γ · 𝐖) (there i) {π = wk-wk π} wkext-id = ql (wk-absurd wk-id π) _
lookup-gc-wk (γ · 𝐖) (there i) {π = wk-cong π} wkext-id =
  let
    lhs = Ψ-gc (lookup-gc γ {π = π} wkext-id i)
    rhs = Ψ-gc (lookup-gc (γ · 𝐖) {π = wk-cong π} wkext-id (there i))

    IH   : WkMVal (omval-to-mval (ψ-gc (lookup-gc γ wkext-id i)) (result (lookup-gc γ wkext-id i))) (M.lookup (there i) (gcmenv-to-menv γ wkext-id · omval-to-mval γ 𝐖))
    IH = lookup-gc-wk γ i {π = π} wkext-id

    c : WkMVal (omval-to-mval (γ · 𝐖) (wk-omval (lookup-ctx-wk γ i 𝐖 π) (result (lookup-gc γ wkext-id i)))) (omval-to-mval (ψ-gc (lookup-gc γ {π = π} wkext-id i)) (result (lookup-gc γ wkext-id i)))
    c = omval-wk (result (lookup-gc γ wkext-id i)) (lookup-gc-menvext γ i 𝐖 π)

    d : WkMVal (omval-to-mval (ψ-gc (lookup-gc (γ · 𝐖) {π = wk-cong π} wkext-id (there i))) (result (lookup-gc (γ · 𝐖) {π = wk-cong π} wkext-id (there i))))      (omval-to-mval (ψ-gc (lookup-gc γ {π = π} wkext-id i)) (result (lookup-gc γ wkext-id i)))
    d = subst (λ x → WkMVal x (omval-to-mval (ψ-gc (lookup-gc γ {π = π} wkext-id i)) (result (lookup-gc γ wkext-id i)))) (lookup-omval-eq γ i 𝐖 π) c

    goal : WkMVal (omval-to-mval (ψ-gc (lookup-gc (γ · 𝐖) {π = wk-cong π} wkext-id (there i))) (result (lookup-gc (γ · 𝐖) {π = wk-cong π} wkext-id (there i)))) (M.lookup (there i) (gcmenv-to-menv γ wkext-id · omval-to-mval γ 𝐖))
    goal = wk-mval-trans d IH
  in
  goal

lookup-gc-wk (γ · unit) (there i) (wkext-wk p) = lookup-gc-wk γ i p
lookup-gc-wk (γ · (dat D)) (there i) (wkext-wk p) = lookup-gc-wk γ i p
lookup-gc-wk (γ · pair 𝐖 𝐖₁) (there i) (wkext-wk p) = lookup-gc-wk γ i p
lookup-gc-wk (γ · lam M) (there i) (wkext-wk p) = lookup-gc-wk γ i p
lookup-gc-wk (γ · var i₂) (there i) (wkext-wk p) = lookup-gc-wk γ i p

lookup-gc-wk (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here wkext-id = wk-mval-id
lookup-gc-wk (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here (wkext-wk p) = wk-mval-id

lookup-gc-wk (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) {π = wk-wk π} wkext-id = ql (wk-absurd wk-id π) _
lookup-gc-wk (γ ·﹝ M ╎ p ╎ K ﹞) (there i) {π = wk-cong π} wkext-id =
  let

    IH = lookup-gc-wk γ i {π = π} wkext-id

    c : WkMVal (omval-to-mval (γ ·﹝ M ╎ p ╎ K ﹞) (wk-omval (lookup-ctx-label-wk γ i M p K π) (result (lookup-gc γ wkext-id i)))) (omval-to-mval (ψ-gc (lookup-gc γ {π = π} wkext-id i)) (result (lookup-gc γ wkext-id i)))
    c = omval-wk (result (lookup-gc γ wkext-id i)) (lookup-gc-label-menvext γ i M p K π)

    d : WkMVal (omval-to-mval (ψ-gc (lookup-gc (γ ·﹝ M ╎ p ╎ K ﹞) {π = wk-cong π} wkext-id (there i))) (result (lookup-gc (γ ·﹝ M ╎ p ╎ K ﹞) {π = wk-cong π} wkext-id (there i))))
               (omval-to-mval (ψ-gc (lookup-gc γ wkext-id i)) (result (lookup-gc γ wkext-id i)))
    d = subst (λ x → WkMVal x (omval-to-mval (ψ-gc (lookup-gc γ wkext-id i)) (result (lookup-gc γ wkext-id i)))) (lookup-omval-label-eq γ i M p K π) c

    goal : WkMVal (omval-to-mval (ψ-gc (lookup-gc (γ ·﹝ M ╎ p ╎ K ﹞) {π = wk-cong π} wkext-id (there i))) (result (lookup-gc (γ ·﹝ M ╎ p ╎ K ﹞) {π = wk-cong π} wkext-id (there i))))
                  (M.lookup (there i) (gcmenv-to-menv γ wkext-id · jumpᵛ M (gcmenv-to-menv γ {π = π} wkext-id) (gcmcstack-to-mcstack γ p K)))
    goal = wk-mval-trans d IH
  in
  goal

lookup-gc-wk (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) (wkext-wk p) = lookup-gc-wk γ i p

eval-gc-wk : (γ : GCM.MEnv Γ) → (W : Γ ⊢ᵛ X) → {π : Γ ⊇ Δ} → (p : WkExt π)
          → WkMVal (omval-to-mval (ψ-gc (eval-gc γ p W)) (result (eval-gc γ p W))) (M.eval W (gcmenv-to-menv γ {π = wk-id} wkext-id))
eval-gc-wk γ (var i) p =
  let
    goal : WkMVal (omval-to-mval (ψ-gc (lookup-gc γ p i)) (result (lookup-gc γ p i))) (M.lookup i (gcmenv-to-menv γ wkext-id))
    goal = lookup-gc-wk γ i p
  in
  goal
eval-gc-wk {Γ = Γ} γ (lam M) p = wk-cloᵛ wk-id (sym (wk-comp-id-β M)) wk-menv-id
eval-gc-wk {Γ = Γ} {Δ = Δ} γ (pair V W) p =
  let
    mv = (eval-gc γ p V)
    mw = (eval-gc γ p W)
    m = squash (EvalGC.split mv) (EvalGC.split mw)

    d₁ = omval-wk (result mv) (gc-menvext-l γ (ψ-gc mv) (p-part₂ (mid-split m)) (p-part₂ (lhs-split m)) (menvext mv))
    IH₁ = eval-gc-wk γ V p
    goal₁ = wk-mval-trans d₁ IH₁

    d₂ = omval-wk (result mw) (gc-menvext-l γ (ψ-gc mw) (p-part₂ (mid-split m)) (p-part₂ (rhs-split m)) (menvext mw))
    IH₂ = eval-gc-wk γ W p
    goal₂ = wk-mval-trans d₂ IH₂
  in
  wk-pairᵛ goal₁ goal₂
eval-gc-wk γ unit p rewrite omval-unit (ψ-gc (eval-gc γ p unit)) (result (eval-gc γ p unit)) = wk-unitᵛ
eval-gc-wk γ (dat D) p rewrite omval-dat γ p D = wk-datᵛ
eval-gc-wk γ (op o a) p rewrite omval-op γ p o a = wk-datᵛ


gcexteq : {γ : GCM.MEnv Γ} {ψ : GCM.MEnv Ψ} → {π₁ : Γ ⊇ Ψ} → MEnvExt π₁ γ ψ → {π : Γ ⊇ Δ} → (p : WkExt π) → {π₂ : Ψ ⊇ Δ} → (p₂ : WkExt π₂)
          → gcmenv-to-menv γ p ≡ gcmenv-to-menv ψ p₂
gcexteq (menv-id π₁ γ) {π = π} wkext-id {π₂ = π₂} wkext-id rewrite wk-id-η π | wk-id-η π₂ = refl
gcexteq (menv-id π γ) wkext-id {π₂ = wk-wk π₂} (wkext-wk p₂) = ql (wk-absurd wk-id π₂) _
gcexteq (menv-id π γ) {π = wk-wk π₁} (wkext-wk p) wkext-id = ql (wk-absurd wk-id π₁) _
gcexteq (menv-id (wk-cong π) (γ · x)) (wkext-wk p) (wkext-wk p₂) = gcexteq (menv-id π γ) p p₂
gcexteq (menv-id (wk-wk π) (γ · x)) (wkext-wk p) (wkext-wk p₂) = ql (wk-absurd (Wk.wk-wk π) π) _
gcexteq (menv-id (wk-cong π) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) (wkext-wk p) (wkext-wk p₂) = gcexteq (menv-id π γ) p p₂
gcexteq (menv-id (wk-wk π) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) (wkext-wk p) (wkext-wk p₂) = ql (wk-absurd (Wk.wk-wk π) π) _
gcexteq {π₁ = wk-wk π₁} (menv-wk-omval mx 𝐖) wkext-id wkext-id = ql (wk-absurd wk-id π₁) _
gcexteq {π₁ = wk-wk π₁} (menv-wk-omval mx 𝐖) wkext-id {π₂ = wk-wk π₂} (wkext-wk p₂) = ql (wk-absurd wk-id (wk-trans π₁ (Wk.wk-wk π₂))) _
gcexteq (menv-wk-omval mx 𝐖) (wkext-wk p) wkext-id = gcexteq mx p WkExt.wkext-id
gcexteq (menv-wk-omval mx 𝐖) (wkext-wk p) (wkext-wk p₂) = gcexteq mx p (WkExt.wkext-wk p₂)
gcexteq {π₁ = wk-wk π₁} (menv-wk-jump mx M r K) wkext-id wkext-id = ql (wk-absurd (Wk.wk-wk π₁) π₁) _
gcexteq {π₁ = wk-wk π₁} (menv-wk-jump mx M r K) wkext-id {π₂ = wk-wk π₂} (wkext-wk p₂) = ql (wk-absurd (Wk.wk-wk π₁) π₂) _
gcexteq (menv-wk-jump mx M r K) (wkext-wk p) wkext-id = gcexteq mx p WkExt.wkext-id
gcexteq (menv-wk-jump mx M r K) (wkext-wk p) (wkext-wk p₂) = gcexteq mx p (WkExt.wkext-wk p₂)

gcstackeq : {γ : GCM.MEnv Γ} {ψ : GCM.MEnv Ψ} → {π₁ : Γ ⊇ Ψ} → MEnvExt π₁ γ ψ → {π : Γ ⊇ Δ} → (p : WkExt π) → {π₂ : Ψ ⊇ Δ} → (p₂ : WkExt π₂) → (K : GCM.CStack Δ X)
          → gcmcstack-to-mcstack γ p K ≡ gcmcstack-to-mcstack ψ p₂ K
gcstackeq (menv-id π₁ γ) {π = π} wkext-id {π₂ = π₂} wkext-id K rewrite wk-id-η π | wk-id-η π₂ = refl

gcstackeq (menv-id π γ) wkext-id {π₂ = wk-wk π₂} (wkext-wk p₂) K = ql (wk-absurd wk-id π₂) _
gcstackeq (menv-id π γ) {π = wk-wk π₁} (wkext-wk p) wkext-id K = ql (wk-absurd wk-id π₁) _
gcstackeq (menv-id (wk-cong π) (γ · x)) (wkext-wk p) (wkext-wk p₂) ◻ = refl
gcstackeq (menv-id (wk-cong π) (γ · x)) (wkext-wk p) (wkext-wk p₂) (< x₁ ； x₂ >∷ K) rewrite gcexteq (menv-id π γ) p p₂ = cong (< x₁ ； gcmenv-to-menv γ p₂ >∷_) (gcstackeq (menv-id (Wk.wk-cong π) (γ · x)) (wkext-trans (WkExt.wkext-wk p) x₂) (wkext-trans (WkExt.wkext-wk p₂) x₂) K)
gcstackeq (menv-id (wk-wk π) (γ · x)) (wkext-wk p) (wkext-wk p₂) K = ql (wk-absurd (Wk.wk-wk π) π) _
gcstackeq (menv-id (wk-cong π) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) (wkext-wk p) (wkext-wk p₂) ◻ = refl
gcstackeq (menv-id (wk-cong π) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) (wkext-wk p) (wkext-wk p₂) (< x₃ ； x₄ >∷ K) rewrite gcexteq (menv-id π γ) p p₂ = cong (< x₃ ； gcmenv-to-menv γ p₂ >∷_) (gcstackeq (menv-id (Wk.wk-cong π) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) (wkext-trans (WkExt.wkext-wk p) x₄) (wkext-trans (WkExt.wkext-wk p₂) x₄) K)
gcstackeq (menv-id (wk-wk π) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) (wkext-wk p) (wkext-wk p₂) K = ql (wk-absurd (Wk.wk-wk π) π) _
gcstackeq {π₁ = wk-wk π₁} (menv-wk-omval mx 𝐖) wkext-id wkext-id K = ql (wk-absurd wk-id π₁) _
gcstackeq {π₁ = wk-wk π₁} (menv-wk-omval mx 𝐖) wkext-id {π₂ = wk-wk π₂} (wkext-wk p₂) K = ql (wk-absurd wk-id (wk-trans π₁ (Wk.wk-wk π₂))) _
gcstackeq (menv-wk-omval mx 𝐖) (wkext-wk p) wkext-id ◻ = refl
gcstackeq {ψ = ψ} (menv-wk-omval mx 𝐖) (wkext-wk p) {π₂ = π₂} wkext-id (< x ； x₁ >∷ K) rewrite gcexteq mx p {π₂ = π₂} wkext-id = cong (< x ； gcmenv-to-menv ψ WkExt.wkext-id >∷_) (gcstackeq (menv-wk-omval mx 𝐖) (wkext-trans (WkExt.wkext-wk p) x₁) x₁ K)
gcstackeq (menv-wk-omval mx 𝐖) (wkext-wk p) (wkext-wk p₂) ◻ = refl
gcstackeq {ψ = ψ} (menv-wk-omval mx 𝐖) (wkext-wk p) (wkext-wk p₂) (< x ； x₁ >∷ K) rewrite gcexteq mx p (wkext-wk p₂) = cong (< x ； gcmenv-to-menv ψ (WkExt.wkext-wk p₂) >∷_) (gcstackeq (menv-wk-omval mx 𝐖) (wkext-trans (WkExt.wkext-wk p) x₁) (wkext-trans (WkExt.wkext-wk p₂) x₁) K)
gcstackeq {π₁ = wk-wk π₁} (menv-wk-jump mx M r K₁) wkext-id wkext-id K = ql (wk-absurd (Wk.wk-wk π₁) π₁) _
gcstackeq {π₁ = wk-wk π₁} (menv-wk-jump mx M r K₁) wkext-id {π₂ = wk-wk π₂} (wkext-wk p₂) K = ql (wk-absurd (Wk.wk-wk π₁) π₂) _
gcstackeq (menv-wk-jump mx M r K₁) (wkext-wk p) wkext-id ◻ = refl
gcstackeq {ψ = ψ} (menv-wk-jump mx M r K₁) (wkext-wk p) {π₂ = π₂} wkext-id (< x ； x₁ >∷ K) rewrite gcexteq mx p {π₂ = π₂} wkext-id = cong (< x ； gcmenv-to-menv ψ WkExt.wkext-id >∷_) (gcstackeq (menv-wk-jump mx M r K₁) (wkext-trans (WkExt.wkext-wk p) x₁) x₁ K)
gcstackeq (menv-wk-jump mx M r K₁) (wkext-wk p) (wkext-wk p₂) ◻ = refl
gcstackeq {ψ = ψ} (menv-wk-jump mx M r K₁) (wkext-wk p) (wkext-wk p₂) (< x ； x₁ >∷ K) rewrite gcexteq mx p (wkext-wk p₂) = cong (< x ； gcmenv-to-menv ψ (WkExt.wkext-wk p₂) >∷_) (gcstackeq (menv-wk-jump mx M r K₁) (wkext-trans (WkExt.wkext-wk p) x₁) (wkext-trans (WkExt.wkext-wk p₂) x₁) K)


wk-menv-id-t : {Γ Δ : Ctx} → (γ : GCM.MEnv Γ) → {π : Γ ⊇ Δ} → (p : WkExt π) → (W : Γ ⊢ᵛ X) → WkMEnv wk-id (gcmenv-to-menv (ψ-gc (eval-gc γ p W)) (p-part₁ (EvalGC.split (eval-gc γ p W)))) (gcmenv-to-menv γ p)
wk-menv-id-t γ p W =
  let
    a = eval-gc γ p W
    b = gcmenv-to-menv γ p
    c = gcexteq (menvext a) p (p-part₁ (EvalGC.split a))
  in
  subst (λ x → WkMEnv wk-id x b) c wk-menv-id

wk-cstack : {Γ Δ : Ctx} → (γ : GCM.MEnv Γ) → {π : Γ ⊇ Δ} → (p : WkExt π) → (W : Γ ⊢ᵛ X) → (K : GCM.CStack Δ X) →
            WkCStack (gcmcstack-to-mcstack (ψ-gc (eval-gc γ p W)) (p-part₁ (EvalGC.split (eval-gc γ p W))) K) (gcmcstack-to-mcstack γ p K)
wk-cstack γ p W ◻ = wk-cstack-empty
wk-cstack γ p W (< M ； p₁ >∷ K) =
  let
    a = eval-gc γ p W

    b : WkCStack (gcmcstack-to-mcstack (ψ-gc (eval-gc γ p W)) (wkext-trans (p-part₁ (EvalGC.split (eval-gc γ p W))) p₁) K) (gcmcstack-to-mcstack γ (wkext-trans p p₁) K)
    b = subst (λ x → WkCStack x (gcmcstack-to-mcstack γ (wkext-trans p p₁) K)) (gcstackeq (menvext a) (wkext-trans p p₁) _ K) (wk-cstack-id {K = (gcmcstack-to-mcstack γ (wkext-trans p p₁) K)})

    goal : WkCStack (< M ； gcmenv-to-menv (ψ-gc (eval-gc γ p W)) (p-part₁ (EvalGC.split (eval-gc γ p W))) >∷ gcmcstack-to-mcstack (ψ-gc (eval-gc γ p W)) (wkext-trans (p-part₁ (EvalGC.split (eval-gc γ p W))) p₁) K) (< M ； gcmenv-to-menv γ p >∷ gcmcstack-to-mcstack γ (wkext-trans p p₁) K)
    goal = wk-cstack-push {M₂ = M} wk-id (sym (wk-comp-id-β M)) (wk-menv-id-t γ p W) b
  in
  goal

---- lemmas for return→ case

--TODO: move this to MachineProps
wk-menv-id-uniq : (γ : M.MEnv Γ) → (π₁ π₂ : Γ ⊇ Γ) → WkMEnv π₁ γ γ ≡ WkMEnv π₂ γ γ
wk-menv-id-uniq γ π₁ π₂ =
  let
    a = refl {x = WkMEnv wk-id γ γ}
    b = subst (λ x → WkMEnv x γ γ ≡ WkMEnv wk-id γ γ) (sym (wk-id-η π₁)) a
  in
  subst (λ x → WkMEnv π₁ γ γ ≡ WkMEnv x γ γ) (sym (wk-id-η π₂)) b

gcmenv-eq : (γ : GCM.MEnv Γ) → (π₁ π₂ : Γ ⊇ Γ) → (gcmenv-to-menv γ {π₁} (wkext-id {π = π₁})) ≡ (gcmenv-to-menv γ {π₂} (wkext-id {π = π₂}))
gcmenv-eq ⋄ wk-ε wk-ε = refl
gcmenv-eq (γ · x) (wk-cong π₁) (wk-cong π₂) = cong (_· omval-to-mval γ x) (gcmenv-eq γ π₁ π₂)
gcmenv-eq (γ · x) (wk-cong π₁) (wk-wk π₂) = ql (wk-absurd wk-id π₂) _
gcmenv-eq (γ · x) (wk-wk π₁) (wk-cong π₂) = ql (wk-absurd π₁ π₂) _
gcmenv-eq (γ · x) (wk-wk π₁) (wk-wk π₂) = ql (wk-absurd wk-id π₂) _
gcmenv-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (wk-cong π₁) (wk-cong π₂) = cong (λ y →  y · (jumpᵛ x y (gcmcstack-to-mcstack γ x₁ x₂))) (gcmenv-eq γ π₁ π₂)
gcmenv-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (wk-cong π₁) (wk-wk π₂) = ql (wk-absurd wk-id π₂) _
gcmenv-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (wk-wk π₁) (wk-cong π₂) = ql (wk-absurd π₁ π₂) _
gcmenv-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (wk-wk π₁) (wk-wk π₂) = ql (wk-absurd wk-id π₂) _

wk-gcmenv-eq : (γ : GCM.MEnv Γ) → (ρ₁ ρ₂ π₁ π₂ π₃ π₄ : Γ ⊇ Γ) → WkMEnv ρ₁ (gcmenv-to-menv γ {π₁} (wkext-id {π = π₁})) (gcmenv-to-menv γ {π₃} (wkext-id {π = π₃})) ≡ WkMEnv ρ₂ (gcmenv-to-menv γ {π₂} (wkext-id {π = π₂})) (gcmenv-to-menv γ {π₄} (wkext-id {π = π₄}))
wk-gcmenv-eq γ ρ₁ ρ₂ π₁ π₂ π₃ π₄ =
  let
    a = refl {x = (WkMEnv ρ₁ (gcmenv-to-menv γ {π₁} (wkext-id {_} {π₁})))}
    b = cong (λ x → WkMEnv x (gcmenv-to-menv γ (wkext-id {π = π₁})) (gcmenv-to-menv γ (wkext-id {π = π₃}))) (wk-id-η ρ₁)
    c = cong (λ x → WkMEnv x (gcmenv-to-menv γ (wkext-id {π = π₂})) (gcmenv-to-menv γ (wkext-id {π = π₄}))) (sym (wk-id-η ρ₂))
  in
  trans b (subst₂ (λ x y → WkMEnv wk-id x y ≡ WkMEnv ρ₂ (gcmenv-to-menv γ wkext-id) (gcmenv-to-menv γ wkext-id)) (gcmenv-eq γ π₂ π₁) (gcmenv-eq γ π₄ π₃) c)

wkmenv-id-eq : (γ : GCM.MEnv Γ) → {π : Γ ⊇ Δ} → (p : WkExt π) → {ρ : Γ ⊇ Γ} → WkMEnv π (gcmenv-to-menv γ {π = ρ} wkext-id) (gcmenv-to-menv γ p)
wkmenv-id-eq {Γ = Γ} {Δ = Γ} γ {π = π} wkext-id {ρ = ρ} = subst (λ x → x) (wk-gcmenv-eq γ wk-id π π ρ π π) (wk-menv-id {γ = gcmenv-to-menv γ {π = π} wkext-id})
wkmenv-id-eq (γ · 𝐖) {π = wk-wk π} (wkext-wk p) {ρ = ρ} =
  let
    IH = wkmenv-id-eq γ p

    goal₀ : WkMEnv (wk-wk π) (gcmenv-to-menv (γ · 𝐖) {π = wk-id} wkext-id) (gcmenv-to-menv γ p)
    goal₀ = wk-menv-wk (omval-to-mval γ 𝐖) (wkmenv-id-eq γ p)

    goal : WkMEnv (wk-wk π) (gcmenv-to-menv (γ · 𝐖) {π = ρ} wkext-id) (gcmenv-to-menv γ p)
    goal = subst (λ x → WkMEnv (wk-wk π) (gcmenv-to-menv (γ · 𝐖) {π = x} wkext-id) (gcmenv-to-menv γ p)) (sym (wk-id-η ρ)) goal₀
  in
  goal
wkmenv-id-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) {π = wk-wk π} (wkext-wk p) {ρ = ρ} =
  let
    IH = wkmenv-id-eq γ p

    goal₀ : WkMEnv (Wk.wk-wk π) (gcmenv-to-menv (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) {π = wk-id} wkext-id) (gcmenv-to-menv γ p)
    goal₀ = wk-menv-wk (jumpᵛ x (gcmenv-to-menv γ wkext-id) (gcmcstack-to-mcstack γ x₁ x₂)) (wkmenv-id-eq γ p)

    goal : WkMEnv (Wk.wk-wk π) (gcmenv-to-menv (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) {π = ρ} wkext-id) (gcmenv-to-menv γ p)
    goal = subst (λ y → WkMEnv (Wk.wk-wk π) (gcmenv-to-menv (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) {π = y} wkext-id) (gcmenv-to-menv γ p)) (sym (wk-id-η ρ)) goal₀
  in
  goal

gcmcstack-wk-eq₁ : (γ : GCM.MEnv Γ) → (𝐖 : GCM.OMVal Γ Y) → {π : Γ ⊇ Δ} → (p : WkExt π) → (K : GCM.CStack Δ X)
                  → gcmcstack-to-mcstack γ p K ≡ gcmcstack-to-mcstack (γ · 𝐖) (wkext-wk p) K
gcmcstack-wk-eq₁ γ 𝐖 p ◻ = refl
gcmcstack-wk-eq₁ γ 𝐖 {π = π} p (< N ； wkext-id >∷ K) = cong (< N ； gcmenv-to-menv γ p >∷_) (gcmcstack-wk-eq₁ γ 𝐖 (wkext-trans p {ρ = wk-id} wkext-id) K)
gcmcstack-wk-eq₁ γ 𝐖 p (< N ； wkext-wk p₁ >∷ K) = cong (< N ； gcmenv-to-menv γ p >∷_) (gcmcstack-wk-eq₁ γ 𝐖 (wkext-trans p (wkext-wk p₁)) K)

---- lemmas for inc→ case
gcmcstack-wk-eq : (γ : GCM.MEnv Γ) → (N : (Γ ∙ `𝓅) ⊢ᶜ X) → {π : Γ ⊇ Δ} → (p : WkExt π) → (K : GCM.CStack Δ X)
                  → {π₁ : Γ ⊇ Ψ} → (p₁ : WkExt π₁) → (K₁ : GCM.CStack Ψ X₁)
                  → gcmcstack-to-mcstack γ p₁ K₁ ≡ gcmcstack-to-mcstack (γ ·﹝ N ╎ p ╎ K ﹞) (wkext-wk p₁) K₁
gcmcstack-wk-eq γ N p K p₁ ◻ = refl
gcmcstack-wk-eq γ N p K p₁ (< N₂ ； wkext-id >∷ K₁) = cong (< N₂ ； gcmenv-to-menv γ p₁ >∷_) (gcmcstack-wk-eq γ N p K p₁ K₁)
gcmcstack-wk-eq γ N p K p₁ (< N₂ ； wkext-wk p₂ >∷ K₁) = cong (< N₂ ； gcmenv-to-menv γ p₁ >∷_) (gcmcstack-wk-eq γ N p K (wkext-trans p₁ (wkext-wk p₂)) K₁)

--------------------------------------------------------------------------
---- lemmas for rec→ case

str-dat-id : (γ : GCM.MEnv Γ) → (𝐖 : OMVal Γ `𝓅) → (π : Γ ⊇ Γ) → (str-dat 𝐖 {π = π} WkExt.wkext-id γ) ≡ 𝐖
str-dat-id ⋄ (dat N) _ = refl
str-dat-id (γ · x) (var here) _ = refl
str-dat-id (γ · x) (var (there i)) _ = refl
str-dat-id (γ · x) (dat N) _ = refl
str-dat-id (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (var (there i)) _ = refl
str-dat-id (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (dat N) _ = refl

omval-str-dat-eq : (γ : GCM.MEnv Γ) → (𝐕 : OMVal Γ X) → (π : Γ ⊇ Γ) → (i : (Γ ∙ X) ∋ `𝓅) → omval-to-mval γ (str-dat (var i) (WkExt.wkext-wk {π = π} WkExt.wkext-id) (γ · 𝐕)) ≡ omval-to-mval (γ · 𝐕) (var i)
omval-str-dat-eq ⋄ (dat N) π here = refl
omval-str-dat-eq (γ · 𝐖) 𝐕 π here =
  let
    goal : omval-to-mval (γ · 𝐖) (str-dat 𝐕 (WkExt.wkext-id {π = π}) (γ · 𝐖)) ≡ omval-to-mval (γ · 𝐖) 𝐕
    goal = subst (λ x → omval-to-mval (γ · 𝐖) x ≡ omval-to-mval (γ · 𝐖) 𝐕) (sym (str-dat-id (γ · 𝐖) 𝐕 π)) refl
  in
  goal
omval-str-dat-eq (γ · 𝐖) 𝐕 π (there i) = subst (λ x → omval-to-mval (γ · 𝐖) x ≡ omval-to-mval (γ · 𝐖) (var i)) (sym (str-dat-id (γ · 𝐖) (var i) π)) refl
omval-str-dat-eq (γ ·﹝ M ╎ p ╎ K ﹞) 𝐕 π here = subst (λ x → omval-to-mval (γ ·﹝ M ╎ p ╎ K ﹞) x ≡ omval-to-mval (γ ·﹝ M ╎ p ╎ K ﹞) 𝐕) (sym (str-dat-id (γ ·﹝ M ╎ p ╎ K ﹞) 𝐕 π)) refl
omval-str-dat-eq (γ ·﹝ M ╎ p ╎ K ﹞) 𝐕 (wk-cong π) (there i) = subst (λ x → omval-to-mval (γ ·﹝ M ╎ p ╎ K ﹞) x ≡ omval-to-mval (γ ·﹝ M ╎ p ╎ K ﹞) (var i)) (sym (str-dat-id (γ ·﹝ M ╎ p ╎ K ﹞) (var i) (Wk.wk-cong π))) refl
omval-str-dat-eq (γ ·﹝ M ╎ p ╎ K ﹞) 𝐕 (wk-wk π) (there i) = ql (wk-absurd wk-id π) _

omval-str-dat-eq' : (γ : GCM.MEnv Γ) → (𝐕 : OMVal Γ X) → (π : Γ ⊇ Γ) → (𝐖 : OMVal (Γ ∙ X) `𝓅) → omval-to-mval γ (str-dat 𝐖 (WkExt.wkext-wk {π = π} WkExt.wkext-id) (γ · 𝐕)) ≡ omval-to-mval (γ · 𝐕) 𝐖
omval-str-dat-eq' γ 𝐕 π (var i) = omval-str-dat-eq γ 𝐕 π i
omval-str-dat-eq' γ 𝐕 π (dat N) = refl

lookup-omval-comm : (γ : GCM.MEnv Γ) → (π : Γ ⊇ Γ) → (i : Γ ∋ X) → (M.lookup i (gcmenv-to-menv γ {π = π} WkExt.wkext-id)) ≡ (omval-to-mval γ (var i))
lookup-omval-comm γ (wk-wk π) i = ql (wk-absurd (Wk.wk-wk π) π) _
lookup-omval-comm (γ · x) (wk-cong π) here = refl
lookup-omval-comm (γ · x) (wk-cong π) (there i) = lookup-omval-comm γ π i
lookup-omval-comm (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (wk-cong π) here rewrite wk-id-η π = refl
lookup-omval-comm (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (wk-cong π) (there i) = lookup-omval-comm γ π i

lookup-label-v : (i : Γ ∋ `ℓ) → (𝐖 : OMVal Γ `𝓅) → (γ : GCM.MEnv Γ) → {π : Γ ⊇ Γ} → (jump-to-state (M.lookup i (gcmenv-to-menv γ {π = π} WkExt.wkext-id)) (omval-to-mval γ 𝐖)) ≡ (gcmcstate-to-mcstate (lookup-label i 𝐖 γ))
lookup-label-v i 𝐖 γ {π = wk-wk π} = ql (wk-absurd wk-id π) _
lookup-label-v here 𝐖 (γ · var i) {π = wk-cong π} =
  let
    IH = lookup-label-v i (str-dat 𝐖 (WkExt.wkext-wk WkExt.wkext-id) (γ · var i)) γ

    a : (M.lookup i (gcmenv-to-menv γ {π = π} WkExt.wkext-id)) ≡ (omval-to-mval γ (var i))
    a  = lookup-omval-comm γ π i

    b : omval-to-mval (γ · var i) 𝐖 ≡ omval-to-mval γ (str-dat 𝐖 (WkExt.wkext-wk WkExt.wkext-id) (γ · var i))
    b = sym (omval-str-dat-eq' γ (var i) wk-id 𝐖)

    d : jump-to-state (omval-to-mval γ (var i)) (omval-to-mval (γ · var i) 𝐖) ≡ jump-to-state (M.lookup i (gcmenv-to-menv γ WkExt.wkext-id)) (omval-to-mval γ (str-dat 𝐖 (WkExt.wkext-wk WkExt.wkext-id) (γ · var i)))
    d = subst₂ (λ x y → jump-to-state (omval-to-mval γ (var i)) (omval-to-mval (γ · var i) 𝐖) ≡ jump-to-state x y) (sym a) b refl

    goal : jump-to-state (omval-to-mval γ (var i)) (omval-to-mval (γ · var i) 𝐖) ≡ gcmcstate-to-mcstate (lookup-label i (str-dat 𝐖 (WkExt.wkext-wk WkExt.wkext-id) (γ · var i)) γ)
    goal = trans d IH
  in
  goal
lookup-label-v here (var (there i)) (γ ·﹝ M ╎ p ╎ K ﹞) {π = wk-cong π} rewrite wk-id-η π =
  let
    b :      ⟨ M ╎ gcmenv-to-menv γ WkExt.wkext-id · omval-to-mval γ (var i) ╎ gcmcstack-to-mcstack γ p K ⟩
           ≡ ⟨ M ╎ gcmenv-to-menv γ WkExt.wkext-id · omval-to-mval γ (var i) ╎ gcmcstack-to-mcstack (γ · (var i)) (WkExt.wkext-wk p) K ⟩
    b = subst (λ x → ⟨ M ╎ gcmenv-to-menv γ WkExt.wkext-id · omval-to-mval γ (var i) ╎ gcmcstack-to-mcstack γ p K ⟩ ≡ ⟨ M ╎ gcmenv-to-menv γ WkExt.wkext-id · omval-to-mval γ (var i) ╎ x ⟩) (sym (gcstackeq (menv-wk-omval (menv-id π γ) (var i)) (WkExt.wkext-wk p) p K)) refl

    goal :   ⟨ M ╎ gcmenv-to-menv γ WkExt.wkext-id · omval-to-mval γ (var i) ╎ gcmcstack-to-mcstack γ p K ⟩
           ≡ ⟨ M ╎ gcmenv-to-menv γ WkExt.wkext-id · omval-to-mval γ (str-dat (var i) WkExt.wkext-id γ) ╎ gcmcstack-to-mcstack (γ · str-dat (var i) WkExt.wkext-id γ) (WkExt.wkext-wk p) K ⟩
    goal = subst (λ x → ⟨ M ╎ gcmenv-to-menv γ WkExt.wkext-id · omval-to-mval γ (var i) ╎ gcmcstack-to-mcstack γ p K ⟩ ≡ ⟨ M ╎ gcmenv-to-menv γ WkExt.wkext-id · omval-to-mval γ x ╎ gcmcstack-to-mcstack (γ · x) (WkExt.wkext-wk p) K ⟩) (sym (str-dat-id γ (var i) wk-id)) b
  in
  goal
lookup-label-v here (dat N) (γ ·﹝ M ╎ p ╎ K ﹞) {π = wk-cong π} rewrite wk-id-η π =
  let
    goal :   ⟨ M ╎ gcmenv-to-menv γ WkExt.wkext-id · (datᵛ N) ╎ gcmcstack-to-mcstack γ p K ⟩
           ≡ ⟨ M ╎ gcmenv-to-menv γ WkExt.wkext-id · (datᵛ N) ╎ gcmcstack-to-mcstack (γ · (dat N)) (WkExt.wkext-wk p) K ⟩
    goal = subst (λ x → ⟨ M ╎ gcmenv-to-menv γ WkExt.wkext-id · (datᵛ N) ╎ gcmcstack-to-mcstack γ p K ⟩ ≡ ⟨ M ╎ gcmenv-to-menv γ WkExt.wkext-id · (datᵛ N) ╎ x ⟩) (sym (gcstackeq (menv-wk-omval (menv-id π γ) (dat N)) (WkExt.wkext-wk p) p K)) refl
  in
  goal
lookup-label-v (there i) (var i₂) (γ · 𝐕) {π = wk-cong π} =
  let
    IH :   jump-to-state (M.lookup i (gcmenv-to-menv γ {π = π} WkExt.wkext-id)) (omval-to-mval γ (str-dat (var i₂) (WkExt.wkext-wk {π = wk-id} WkExt.wkext-id) (γ · 𝐕))) ≡ gcmcstate-to-mcstate (lookup-label i (str-dat (var i₂) (WkExt.wkext-wk WkExt.wkext-id) (γ · 𝐕)) γ)
    IH = lookup-label-v i (str-dat (var i₂) (WkExt.wkext-wk WkExt.wkext-id) (γ · 𝐕)) γ {π = π}
    goal : jump-to-state (M.lookup i (gcmenv-to-menv γ {π = π} WkExt.wkext-id)) (omval-to-mval (γ · 𝐕) (var i₂)) ≡ gcmcstate-to-mcstate (lookup-label i (str-dat (var i₂) (WkExt.wkext-wk WkExt.wkext-id) (γ · 𝐕)) γ)
    goal = subst (λ x → jump-to-state (M.lookup i (gcmenv-to-menv γ {π = π} WkExt.wkext-id)) x ≡ gcmcstate-to-mcstate (lookup-label i (str-dat (var i₂) (WkExt.wkext-wk WkExt.wkext-id) (γ · 𝐕)) γ))
                 (omval-str-dat-eq γ 𝐕 wk-id i₂) IH
  in
  goal
lookup-label-v (there i) (dat N) (γ · 𝐕) {π = wk-cong π} = lookup-label-v i (str-dat (dat N) (WkExt.wkext-wk {π = π} WkExt.wkext-id) (γ · 𝐕)) γ {π = π}
lookup-label-v (there i) (var (there i₁)) (γ ·﹝ M ╎ p ╎ K ﹞) {π = wk-cong π} =
  let
    IH = lookup-label-v i (str-dat (var (there i₁)) (WkExt.wkext-wk {π = wk-id} WkExt.wkext-id) (γ · (var i))) γ {π = π}
    goal :  jump-to-state (M.lookup i (gcmenv-to-menv γ WkExt.wkext-id)) (omval-to-mval γ (var i₁)) ≡ gcmcstate-to-mcstate (lookup-label i (str-dat (var i₁) WkExt.wkext-id γ) γ)
    goal = subst (λ x → jump-to-state (M.lookup i (gcmenv-to-menv γ WkExt.wkext-id)) (omval-to-mval γ x) ≡ gcmcstate-to-mcstate (lookup-label i (str-dat (var i₁) WkExt.wkext-id γ) γ))  ((str-dat-id γ (var i₁) wk-id)) IH
  in
  goal
lookup-label-v (there i) (dat D) (γ ·﹝ M ╎ p ╎ K ﹞) {π = wk-cong π} =
  lookup-label-v i (str-dat (dat D) (WkExt.wkext-wk {π = π} WkExt.wkext-id) (γ · (var i))) γ {π = π}


omval-lookup-ext-eq : (γ : GCM.MEnv Γ) → (δ : GCM.MEnv Δ) → {π : Γ ⊇ Δ} → (MEnvExt π γ δ) → (𝐖 : GCM.OMVal Δ `𝓅) → omval-to-mval γ (wk-omval π 𝐖) ≡ omval-to-mval δ 𝐖
omval-lookup-ext-eq ⋄ ⋄ (menv-id π γ) (dat N) = refl
omval-lookup-ext-eq ⋄ (δ · x) () 𝐖
omval-lookup-ext-eq ⋄ (δ ·﹝ x ╎ x₁ ╎ x₂ ﹞) () 𝐖
omval-lookup-ext-eq (γ · x) ⋄ (menv-wk-omval mx 𝐖) (dat N) = refl
omval-lookup-ext-eq (γ · x) (δ · _) (menv-id π γ₁) (var i) = refl
omval-lookup-ext-eq (γ · x) (δ · _) (menv-id π γ₁) (dat N) = refl
omval-lookup-ext-eq (γ · x) (δ · x₁) {π = wk-wk π} (menv-wk-omval mx 𝐖) (var i) = omval-lookup-ext-eq γ (δ · x₁) {π = π} mx (var i)
omval-lookup-ext-eq (γ · x) (δ · x₁) (menv-wk-omval mx 𝐖) (dat N) = refl
omval-lookup-ext-eq (γ · x) (δ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) {π = wk-wk π} (menv-wk-omval mx 𝐖) (var i) = omval-lookup-ext-eq γ (δ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) {π = π} mx (var i)
omval-lookup-ext-eq (γ · x) (δ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) (menv-wk-omval mx 𝐖) (dat N) = refl
omval-lookup-ext-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) ⋄ (menv-wk-jump mx M r K) (dat N) = refl
omval-lookup-ext-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (δ · x₃) {π = wk-wk π} (menv-wk-jump mx M r K) (var i) = omval-lookup-ext-eq γ (δ · x₃) {π = π} mx (var i)
omval-lookup-ext-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (δ · x₃) (menv-wk-jump mx M r K) (dat N) = refl
omval-lookup-ext-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (δ ·﹝ _ ╎ _ ╎ _ ﹞) (menv-id π γ₁) (var i) = refl
omval-lookup-ext-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (δ ·﹝ _ ╎ _ ╎ _ ﹞) (menv-id π γ₁) (dat N) = refl
omval-lookup-ext-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (δ ·﹝ x₃ ╎ x₄ ╎ x₅ ﹞) {π = wk-wk π} (menv-wk-jump mx M r K) (var i) = omval-lookup-ext-eq γ (δ ·﹝ x₃ ╎ x₄ ╎ x₅ ﹞) {π = π} mx (var i)
omval-lookup-ext-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (δ ·﹝ x₃ ╎ x₄ ╎ x₅ ﹞) (menv-wk-jump mx M r K) (dat N) = refl


lookup-eq : (i : Γ ∋ `𝓅) → (γ : GCM.MEnv Γ) → {π : Γ ⊇ Γ} → omval-to-mval γ (GCM.lookup i γ) ≡ M.lookup i (gcmenv-to-menv γ {π = π} WkExt.wkext-id)
lookup-eq i γ {π = wk-wk π} = ql (wk-absurd (Wk.wk-wk π) π) _
lookup-eq here (γ · var i) {π = wk-cong π} = refl
lookup-eq here (γ · dat N) {π = wk-cong π} = refl
lookup-eq (there i) (γ · 𝐖) {π = wk-cong π} =
  let
    IH = lookup-eq i γ {π = π}
    goal : omval-to-mval (γ · 𝐖) (wk-omval (Wk.wk-wk wk-id) (GCM.lookup i γ)) ≡ M.lookup i (gcmenv-to-menv γ WkExt.wkext-id)
    goal = trans (omval-lookup-ext-eq (γ · 𝐖) γ (menv-wk-omval (menv-id wk-id γ) 𝐖) (GCM.lookup i γ)) IH
  in
  goal
lookup-eq (there i) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) {π = wk-cong π} =
  let
    IH = lookup-eq i γ {π = π}
    goal = trans (omval-lookup-ext-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) γ (menv-wk-jump (menv-id wk-id γ) x x₁ x₂) (GCM.lookup i γ)) IH
  in
  goal

omval-eval-eq : (W : Γ ⊢ᵛ `𝓅) → (γ : GCM.MEnv Γ) → {π : Γ ⊇ Γ} → omval-to-mval γ (GCM.eval γ W) ≡ (M.eval W (gcmenv-to-menv γ {π = π} WkExt.wkext-id))
omval-eval-eq (Syntax.var i) γ =
  let
    goal : omval-to-mval γ (GCM.lookup i γ) ≡ M.lookup i (gcmenv-to-menv γ WkExt.wkext-id)
    goal = lookup-eq i γ
  in
  goal
omval-eval-eq (Syntax.dat D) γ = refl
omval-eval-eq (Syntax.op o args) γ = refl

lookup-label-wk : (i : Γ ∋ `ℓ) → (W : Γ ⊢ᵛ `𝓅) → (γ : GCM.MEnv Γ) → {π : Γ ⊇ Γ} → MProps.WkCState (jump-to-state (M.lookup i (gcmenv-to-menv γ {π = π} WkExt.wkext-id)) (M.eval W (gcmenv-to-menv γ {π = π} WkExt.wkext-id))) (gcmcstate-to-mcstate (lookup-label i (GCM.eval γ W) γ))

lookup-label-wk i W γ {π = π} rewrite sym (lookup-label-v i (GCM.eval γ W) γ {π = π}) | omval-eval-eq W γ {π = π} = wk-cstate-id


eval-jump-wk : (V : Γ ⊢ᵛ `ℓ) → (W : Γ ⊢ᵛ `𝓅) → (γ : GCM.MEnv Γ) → MProps.WkCState (jump-to-state (M.eval V (gcmenv-to-menv γ {π = wk-id} WkExt.wkext-id)) (M.eval W (gcmenv-to-menv γ {π = wk-id} WkExt.wkext-id))) (gcmcstate-to-mcstate (GCM.eval-jump V W γ))
eval-jump-wk (var i) W γ = lookup-label-wk i W γ

--------------------------------------------------------------------------
---- lemmas for pmᶜ→ case

wk-omval-wk-η : (M : OMVal Γ X) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → wk-omval π (wk-omval δ M) ≡ wk-omval (wk-trans π δ) M
wk-omval-wk-η unit π δ = refl
wk-omval-wk-η (pair M N) π δ = cong₂ pair (wk-omval-wk-η M π δ) (wk-omval-wk-η N π δ)
wk-omval-wk-η (lam M) π δ = refl
wk-omval-wk-η (var i) π δ = refl
wk-omval-wk-η (dat D) π δ = refl

lookup-wk : (γ : GCM.MEnv Γ) → (i : Γ ∋ X) → WkMVal (omval-to-mval γ (GCM.lookup i γ)) (M.lookup i (gcmenv-to-menv γ {π = wk-id} WkExt.wkext-id))
lookup-wk (γ · 𝐖) (there i) =
  let
    IH : WkMVal (omval-to-mval γ (GCM.lookup i γ)) (M.lookup i (gcmenv-to-menv γ WkExt.wkext-id))
    IH = lookup-wk γ i
    a : WkMVal (omval-to-mval (γ · 𝐖) (wk-omval (Wk.wk-wk wk-id) (GCM.lookup i γ))) (omval-to-mval γ (wk-omval wk-id (GCM.lookup i γ)))
    a = omval-wk-drop₁ 𝐖 (GCM.lookup i γ) wk-id γ
    b : WkMVal (omval-to-mval (γ · 𝐖) (wk-omval (Wk.wk-wk wk-id) (GCM.lookup i γ))) (omval-to-mval γ (GCM.lookup i γ))
    b = subst (λ x → WkMVal (omval-to-mval (γ · 𝐖) (wk-omval (Wk.wk-wk wk-id) (GCM.lookup i γ))) (omval-to-mval γ x)) (wk-omval-id-β {𝐖 = GCM.lookup i γ}) a
    goal : WkMVal (omval-to-mval (γ · 𝐖) (wk-omval (Wk.wk-wk wk-id) (GCM.lookup i γ))) (M.lookup i (gcmenv-to-menv γ {π = wk-id} WkExt.wkext-id))
    goal = wk-mval-trans b IH
  in
  goal
lookup-wk (γ ·﹝ M ╎ p ╎ K ﹞) (there i) =
  let
    IH : WkMVal (omval-to-mval γ (GCM.lookup i γ)) (M.lookup i (gcmenv-to-menv γ WkExt.wkext-id))
    IH = lookup-wk γ i
    a : WkMVal (omval-to-mval (γ ·﹝ M ╎ p ╎ K ﹞) (wk-omval (Wk.wk-wk wk-id) (GCM.lookup i γ))) (omval-to-mval γ (wk-omval wk-id (GCM.lookup i γ)))
    a = omval-wk-drop₂ M p K (GCM.lookup i γ) wk-id γ
    b : WkMVal (omval-to-mval (γ ·﹝ M ╎ p ╎ K ﹞) (wk-omval (Wk.wk-wk wk-id) (GCM.lookup i γ))) (omval-to-mval γ (GCM.lookup i γ))
    b = subst (λ x → WkMVal (omval-to-mval (γ ·﹝ M ╎ p ╎ K ﹞) (wk-omval (Wk.wk-wk wk-id) (GCM.lookup i γ))) (omval-to-mval γ x)) (wk-omval-id-β {𝐖 = GCM.lookup i γ}) a
    goal : WkMVal (omval-to-mval (γ ·﹝ M ╎ p ╎ K ﹞) (wk-omval (Wk.wk-wk wk-id) (GCM.lookup i γ))) (M.lookup i (gcmenv-to-menv γ {π = wk-id} WkExt.wkext-id))
    goal = wk-mval-trans b IH
  in
  goal
lookup-wk (γ · unit) here = wk-unitᵛ
lookup-wk (γ · pair 𝐕 𝐖) here =
  let
    LHS : WkMVal (omval-to-mval (γ · pair 𝐕 𝐖) (wk-omval (wk-wk wk-id) 𝐕)) (omval-to-mval γ 𝐕)
    LHS = subst (λ x → WkMVal (omval-to-mval (γ · pair 𝐕 𝐖) (wk-omval (wk-wk wk-id) 𝐕)) (omval-to-mval γ x)) (wk-omval-id-β {𝐖 = 𝐕}) (omval-wk-drop₁ (pair 𝐕 𝐖) 𝐕 wk-id γ)

    RHS : WkMVal (omval-to-mval (γ · pair 𝐕 𝐖) (wk-omval (wk-wk wk-id) 𝐖)) (omval-to-mval γ 𝐖)
    RHS = subst (λ x → WkMVal (omval-to-mval (γ · pair 𝐕 𝐖) (wk-omval (wk-wk wk-id) 𝐖)) (omval-to-mval γ x)) (wk-omval-id-β {𝐖 = 𝐖}) (omval-wk-drop₁ (pair 𝐕 𝐖) 𝐖 wk-id γ)
  in
  wk-pairᵛ LHS RHS
lookup-wk (γ · lam M) here = wk-cloᵛ (wk-wk wk-id) refl (wk-menv-wk (omval-to-mval γ (lam M)) wk-menv-id)
lookup-wk (γ · var i) here = wk-mval-id
lookup-wk (γ · dat N) here = wk-datᵛ
lookup-wk (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here = wk-jumpᵛ wk-id (sym (wk-comp-id-β x)) wk-menv-id wk-cstack-id

eval-wk : (γ : GCM.MEnv Γ) → (W : Γ ⊢ᵛ X) → WkMVal (omval-to-mval γ (GCM.eval γ W)) (M.eval W (gcmenv-to-menv γ {π = wk-id} WkExt.wkext-id))
eval-wk γ (var i) = lookup-wk γ i
eval-wk γ (lam M) = wk-mval-id
eval-wk γ (pair V W) = wk-pairᵛ (eval-wk γ V) (eval-wk γ W)
eval-wk γ unit = wk-mval-id
eval-wk γ (dat D) = wk-mval-id
eval-wk γ (op o args) = wk-mval-id

{-
proj₁-wk-comm : (γ : GCM.MEnv Γ) → (δ : GCM.MEnv Δ) → {π : Γ ⊇ Δ} → (MEnvExt π γ δ) → (i : Δ ∋ (X `× Y)) → wk-omval π (proj₁-omval δ (var i)) ≡ proj₁-omval γ (var (wk-mem π i))
proj₁-wk-comm γ δ {π = π} (menv-id π γ) i rewrite wk-id-η π | wk-omval-id-β {𝐖 = (proj₁-omval γ (var i))} = refl
proj₁-wk-comm (γ · 𝐕) δ {π = wk-wk π} (menv-wk-omval mx 𝐕) i =
  let
    IH : wk-omval π (proj₁-omval δ (var i)) ≡ proj₁-omval γ (var (wk-mem π i))
    IH = proj₁-wk-comm γ δ {π = π} mx i
    b : wk-omval (Wk.wk-wk wk-id) (wk-omval π (proj₁-omval δ (var i))) ≡ wk-omval (Wk.wk-wk wk-id) (proj₁-omval γ (var (wk-mem π i)))
    b = cong (wk-omval (Wk.wk-wk wk-id)) IH
    goal : wk-omval (wk-trans (Wk.wk-wk wk-id) π) (proj₁-omval δ (var i)) ≡ wk-omval (Wk.wk-wk wk-id) (proj₁-omval γ (var (wk-mem π i)))
    goal = subst (λ x → x ≡ wk-omval (Wk.wk-wk wk-id) (proj₁-omval γ (var (wk-mem π i)))) (wk-omval-wk-η (proj₁-omval δ (var i)) (Wk.wk-wk wk-id) π) b
  in
  goal
proj₁-wk-comm (γ ·﹝ M ╎ r ╎ K ﹞) δ {π = wk-wk π} (menv-wk-jump mx M r K) i =
  let
    IH : wk-omval π (proj₁-omval δ (var i)) ≡ proj₁-omval γ (var (wk-mem π i))
    IH = proj₁-wk-comm γ δ {π = π} mx i
    b : wk-omval (Wk.wk-wk wk-id) (wk-omval π (proj₁-omval δ (var i))) ≡ wk-omval (Wk.wk-wk wk-id) (proj₁-omval γ (var (wk-mem π i)))
    b = cong (wk-omval (Wk.wk-wk wk-id)) IH
    goal : wk-omval (Wk.wk-wk π) (proj₁-omval δ (var i)) ≡ wk-omval (Wk.wk-wk wk-id) (proj₁-omval γ (var (wk-mem π i)))
    goal = subst (λ x → x ≡ wk-omval (Wk.wk-wk wk-id) (proj₁-omval γ (var (wk-mem π i)))) (wk-omval-wk-η (proj₁-omval δ (var i)) (wk-wk wk-id) π) b
  in
  goal

proj₂-wk-comm : (γ : GCM.MEnv Γ) → (δ : GCM.MEnv Δ) → {π : Γ ⊇ Δ} → (MEnvExt π γ δ) → (i : Δ ∋ (X `× Y)) → wk-omval π (proj₂-omval δ (var i)) ≡ proj₂-omval γ (var (wk-mem π i))
proj₂-wk-comm γ δ {π = π} (menv-id π γ) i rewrite wk-id-η π | wk-omval-id-β {𝐖 = (proj₂-omval γ (var i))} = refl
proj₂-wk-comm (γ · 𝐕) δ {π = wk-wk π} (menv-wk-omval mx 𝐕) i =
  let
    IH : wk-omval π (proj₂-omval δ (var i)) ≡ proj₂-omval γ (var (wk-mem π i))
    IH = proj₂-wk-comm γ δ {π = π} mx i
    b : wk-omval (Wk.wk-wk wk-id) (wk-omval π (proj₂-omval δ (var i))) ≡ wk-omval (Wk.wk-wk wk-id) (proj₂-omval γ (var (wk-mem π i)))
    b = cong (wk-omval (Wk.wk-wk wk-id)) IH
    goal : wk-omval (wk-trans (Wk.wk-wk wk-id) π) (proj₂-omval δ (var i)) ≡ wk-omval (Wk.wk-wk wk-id) (proj₂-omval γ (var (wk-mem π i)))
    goal = subst (λ x → x ≡ wk-omval (Wk.wk-wk wk-id) (proj₂-omval γ (var (wk-mem π i)))) (wk-omval-wk-η (proj₂-omval δ (var i)) (Wk.wk-wk wk-id) π) b
  in
  goal
proj₂-wk-comm (γ ·﹝ M ╎ r ╎ K ﹞) δ {π = wk-wk π} (menv-wk-jump mx M r K) i =
  let
    IH : wk-omval π (proj₂-omval δ (var i)) ≡ proj₂-omval γ (var (wk-mem π i))
    IH = proj₂-wk-comm γ δ {π = π} mx i
    b : wk-omval (Wk.wk-wk wk-id) (wk-omval π (proj₂-omval δ (var i))) ≡ wk-omval (Wk.wk-wk wk-id) (proj₂-omval γ (var (wk-mem π i)))
    b = cong (wk-omval (Wk.wk-wk wk-id)) IH
    goal : wk-omval (Wk.wk-wk π) (proj₂-omval δ (var i)) ≡ wk-omval (Wk.wk-wk wk-id) (proj₂-omval γ (var (wk-mem π i)))
    goal = subst (λ x → x ≡ wk-omval (Wk.wk-wk wk-id) (proj₂-omval γ (var (wk-mem π i)))) (wk-omval-wk-η (proj₂-omval δ (var i)) (wk-wk wk-id) π) b
  in
  goal
-}

proj₁-wk : (𝐕 𝐖 : M.MVal (X `× Y)) → WkMVal 𝐕 𝐖 → WkMVal (proj₁-val 𝐕) (proj₁-val 𝐖)
proj₁-wk 𝐕 𝐖 (wk-pairᵛ wmv₁ wmv₂) = wmv₁

proj₂-wk : (𝐕 𝐖 : M.MVal (X `× Y)) → WkMVal 𝐕 𝐖 → WkMVal (proj₂-val 𝐕) (proj₂-val 𝐖)
proj₂-wk 𝐕 𝐖 (wk-pairᵛ wmv₁ wmv₂) = wmv₂

proj₁-wk-mval-wk : (𝐖 : GCM.OMVal Γ (X `× Y)) → (γ : GCM.MEnv Γ) →  WkMVal (omval-to-mval γ (GCM.proj₁-omval γ 𝐖)) (M.proj₁-val (omval-to-mval γ 𝐖))
proj₁-wk-mval-wk (pair 𝐕 𝐖) ⋄ = wk-mval-id
proj₁-wk-mval-wk (pair 𝐕 𝐖) (γ · x) = wk-mval-id
proj₁-wk-mval-wk (pair 𝐕 𝐖) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-mval-id
proj₁-wk-mval-wk (var here) (γ · pair 𝐕 𝐖) =
  let
    IH = proj₁-wk-mval-wk (pair 𝐕 𝐖) γ
    a : WkMVal (omval-to-mval (γ · pair 𝐕 𝐖) (wk-omval (Wk.wk-wk wk-id) 𝐕)) (omval-to-mval γ (wk-omval wk-id 𝐕))
    a = omval-wk-drop₁ (pair 𝐕 𝐖) 𝐕 wk-id γ
    b : WkMVal (omval-to-mval (γ · pair 𝐕 𝐖) (wk-omval (Wk.wk-wk wk-id) 𝐕)) (omval-to-mval γ 𝐕)
    b = subst (λ x → WkMVal (omval-to-mval (γ · pair 𝐕 𝐖) (wk-omval (Wk.wk-wk wk-id) 𝐕)) (omval-to-mval γ x)) (wk-omval-id-β {𝐖 = 𝐕}) a
  in
  wk-mval-trans b IH
proj₁-wk-mval-wk (var here) (γ · var i) =
  let
    a : WkMVal (omval-to-mval (γ · var i) (proj₁-omval (γ · var i) (var here))) (omval-to-mval γ (wk-omval wk-id (proj₁-omval γ (var i))))
    a = omval-wk-drop₁ (var i) (proj₁-omval γ (var i)) wk-id γ
    c : WkMVal (omval-to-mval (γ · var i) (proj₁-omval (γ · var i) (var here))) (omval-to-mval γ (proj₁-omval γ (var i)))
    c = subst (λ x → WkMVal (omval-to-mval (γ · var i) (proj₁-omval (γ · var i) (var here))) (omval-to-mval γ x)) (wk-omval-id-β {𝐖 = proj₁-omval γ (var i)}) a
  in
  wk-mval-trans c (proj₁-wk-mval-wk (var i) γ)
proj₁-wk-mval-wk (var (there i)) (γ · 𝐖) =
  let
    a : WkMVal (omval-to-mval (γ · 𝐖) (proj₁-omval (γ · 𝐖) (var (there i)))) (omval-to-mval γ (wk-omval wk-id (proj₁-omval γ (var i))))
    a = omval-wk-drop₁ 𝐖 (proj₁-omval γ (var i)) wk-id γ
    c : WkMVal (omval-to-mval (γ · 𝐖) (proj₁-omval (γ · 𝐖) (var (there i)))) (omval-to-mval γ (proj₁-omval γ (var i)))
    c = subst (λ x → WkMVal (omval-to-mval (γ · 𝐖) (proj₁-omval (γ · 𝐖) (var (there i)))) (omval-to-mval γ x)) (wk-omval-id-β {𝐖 = proj₁-omval γ (var i)}) a
  in
  wk-mval-trans c (proj₁-wk-mval-wk (var i) γ)
proj₁-wk-mval-wk (var (there i)) (γ ·﹝ M ╎ p ╎ K ﹞) =
  let
    a : WkMVal (omval-to-mval (γ ·﹝ M ╎ p ╎ K ﹞) (proj₁-omval (γ ·﹝ M ╎ p ╎ K ﹞) (var (there i)))) (omval-to-mval γ (wk-omval wk-id (proj₁-omval γ (var i))))
    a = omval-wk-drop₂ M p K (proj₁-omval γ (var i)) wk-id γ
    c : WkMVal (omval-to-mval (γ ·﹝ M ╎ p ╎ K ﹞) (proj₁-omval (γ ·﹝ M ╎ p ╎ K ﹞) (var (there i)))) (omval-to-mval γ (proj₁-omval γ (var i)))
    c = subst (λ x → WkMVal (omval-to-mval (γ ·﹝ M ╎ p ╎ K ﹞) (proj₁-omval (γ ·﹝ M ╎ p ╎ K ﹞) (var (there i)))) (omval-to-mval γ x)) (wk-omval-id-β {𝐖 = proj₁-omval γ (var i)}) a
  in
  wk-mval-trans c (proj₁-wk-mval-wk (var i) γ)

proj₂-wk-mval-wk : (𝐖 : GCM.OMVal Γ (X `× Y)) → (γ : GCM.MEnv Γ) →  WkMVal (omval-to-mval γ (GCM.proj₂-omval γ 𝐖)) (M.proj₂-val (omval-to-mval γ 𝐖))
proj₂-wk-mval-wk (pair 𝐕 𝐖) ⋄ = wk-mval-id
proj₂-wk-mval-wk (pair 𝐕 𝐖) (γ · x) = wk-mval-id
proj₂-wk-mval-wk (pair 𝐕 𝐖) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-mval-id
proj₂-wk-mval-wk (var here) (γ · pair 𝐕 𝐖) =
  let
    IH = proj₂-wk-mval-wk (pair 𝐕 𝐖) γ
    a : WkMVal (omval-to-mval (γ · pair 𝐕 𝐖) (wk-omval (Wk.wk-wk wk-id) 𝐖)) (omval-to-mval γ (wk-omval wk-id 𝐖))
    a = omval-wk-drop₁ (pair 𝐕 𝐖) 𝐖 wk-id γ
    b : WkMVal (omval-to-mval (γ · pair 𝐕 𝐖) (wk-omval (Wk.wk-wk wk-id) 𝐖)) (omval-to-mval γ 𝐖)
    b = subst (λ x → WkMVal (omval-to-mval (γ · pair 𝐕 𝐖) (wk-omval (Wk.wk-wk wk-id) 𝐖)) (omval-to-mval γ x)) (wk-omval-id-β {𝐖 = 𝐖}) a
  in
  wk-mval-trans b IH
proj₂-wk-mval-wk (var here) (γ · var i) =
  let
    a : WkMVal (omval-to-mval (γ · var i) (proj₂-omval (γ · var i) (var here))) (omval-to-mval γ (wk-omval wk-id (proj₂-omval γ (var i))))
    a = omval-wk-drop₁ (var i) (proj₂-omval γ (var i)) wk-id γ
    c : WkMVal (omval-to-mval (γ · var i) (proj₂-omval (γ · var i) (var here))) (omval-to-mval γ (proj₂-omval γ (var i)))
    c = subst (λ x → WkMVal (omval-to-mval (γ · var i) (proj₂-omval (γ · var i) (var here))) (omval-to-mval γ x)) (wk-omval-id-β {𝐖 = proj₂-omval γ (var i)}) a
  in
  wk-mval-trans c (proj₂-wk-mval-wk (var i) γ)
proj₂-wk-mval-wk (var (there i)) (γ · 𝐖) =
  let
    a : WkMVal (omval-to-mval (γ · 𝐖) (proj₂-omval (γ · 𝐖) (var (there i)))) (omval-to-mval γ (wk-omval wk-id (proj₂-omval γ (var i))))
    a = omval-wk-drop₁ 𝐖 (proj₂-omval γ (var i)) wk-id γ
    c : WkMVal (omval-to-mval (γ · 𝐖) (proj₂-omval (γ · 𝐖) (var (there i)))) (omval-to-mval γ (proj₂-omval γ (var i)))
    c = subst (λ x → WkMVal (omval-to-mval (γ · 𝐖) (proj₂-omval (γ · 𝐖) (var (there i)))) (omval-to-mval γ x)) (wk-omval-id-β {𝐖 = proj₂-omval γ (var i)}) a
  in
  wk-mval-trans c (proj₂-wk-mval-wk (var i) γ)
proj₂-wk-mval-wk (var (there i)) (γ ·﹝ M ╎ p ╎ K ﹞) =
  let
    a : WkMVal (omval-to-mval (γ ·﹝ M ╎ p ╎ K ﹞) (proj₂-omval (γ ·﹝ M ╎ p ╎ K ﹞) (var (there i)))) (omval-to-mval γ (wk-omval wk-id (proj₂-omval γ (var i))))
    a = omval-wk-drop₂ M p K (proj₂-omval γ (var i)) wk-id γ
    c : WkMVal (omval-to-mval (γ ·﹝ M ╎ p ╎ K ﹞) (proj₂-omval (γ ·﹝ M ╎ p ╎ K ﹞) (var (there i)))) (omval-to-mval γ (proj₂-omval γ (var i)))
    c = subst (λ x → WkMVal (omval-to-mval (γ ·﹝ M ╎ p ╎ K ﹞) (proj₂-omval (γ ·﹝ M ╎ p ╎ K ﹞) (var (there i)))) (omval-to-mval γ x)) (wk-omval-id-β {𝐖 = proj₂-omval γ (var i)}) a
  in
  wk-mval-trans c (proj₂-wk-mval-wk (var i) γ)

eval₁-wk : (γ : GCM.MEnv Γ) → (W : Γ ⊢ᵛ (X `× Y)) → WkMVal (omval-to-mval γ (proj₁-omval γ (GCM.eval γ W))) (proj₁-val (M.eval W (gcmenv-to-menv γ {π = wk-id} WkExt.wkext-id)))
eval₁-wk γ W =
  let
    ek : WkMVal (omval-to-mval γ (proj₁-omval γ (GCM.eval γ W))) (proj₁-val (omval-to-mval γ (GCM.eval γ W)))
    ek = proj₁-wk-mval-wk (GCM.eval γ W) γ
    goal : WkMVal (omval-to-mval γ (proj₁-omval γ (GCM.eval γ W))) (proj₁-val (M.eval W (gcmenv-to-menv γ WkExt.wkext-id)))
    goal = wk-mval-trans ek (proj₁-wk (omval-to-mval γ (GCM.eval γ W)) (M.eval W (gcmenv-to-menv γ WkExt.wkext-id)) (eval-wk γ W))
  in
  goal

eval₂-wk : (γ : GCM.MEnv Γ) → (W : Γ ⊢ᵛ (X `× Y)) → WkMVal (omval-to-mval (γ · proj₁-omval γ (GCM.eval γ W)) (wk-omval (Wk.wk-wk wk-id) (proj₂-omval γ (GCM.eval γ W)))) (proj₂-val (M.eval W (gcmenv-to-menv γ {π = wk-id} WkExt.wkext-id)))
eval₂-wk γ W =
  let
    ek : WkMVal (omval-to-mval γ (proj₂-omval γ (GCM.eval γ W))) (proj₂-val (omval-to-mval γ (GCM.eval γ W)))
    ek = proj₂-wk-mval-wk (GCM.eval γ W) γ
    a : WkMVal (omval-to-mval γ (proj₂-omval γ (GCM.eval γ W))) (proj₂-val (M.eval W (gcmenv-to-menv γ {π = wk-id} WkExt.wkext-id)))
    a = wk-mval-trans ek (proj₂-wk (omval-to-mval γ (GCM.eval γ W)) (M.eval W (gcmenv-to-menv γ WkExt.wkext-id)) (eval-wk γ W))
    b : WkMVal (omval-to-mval (γ · proj₁-omval γ (GCM.eval γ W)) (wk-omval (Wk.wk-wk wk-id) (proj₂-omval γ (GCM.eval γ W)))) (omval-to-mval γ (wk-omval wk-id (proj₂-omval γ (GCM.eval γ W))))
    b = omval-wk-drop₁ (proj₁-omval γ (GCM.eval γ W)) (proj₂-omval γ (GCM.eval γ W)) wk-id γ
    c : WkMVal (omval-to-mval (γ · proj₁-omval γ (GCM.eval γ W)) (wk-omval (Wk.wk-wk wk-id) (proj₂-omval γ (GCM.eval γ W)))) (omval-to-mval γ (proj₂-omval γ (GCM.eval γ W)))
    c = subst (λ x → WkMVal (omval-to-mval (γ · proj₁-omval γ (GCM.eval γ W)) (wk-omval (Wk.wk-wk wk-id) (proj₂-omval γ (GCM.eval γ W)))) (omval-to-mval γ x)) (wk-omval-id-β {𝐖 = proj₂-omval γ (GCM.eval γ W)}) b
    goal : WkMVal (omval-to-mval (γ · proj₁-omval γ (GCM.eval γ W)) (wk-omval (Wk.wk-wk wk-id) (proj₂-omval γ (GCM.eval γ W)))) (proj₂-val (M.eval W (gcmenv-to-menv γ WkExt.wkext-id)))
    goal = wk-mval-trans c a
  in
  goal

--------------------------------------------------------------------------
---- lemmas for app→ case

ctx-clo-to-comp-wk : (γ : GCM.MEnv Γ) → (𝐖 : GCM.OMVal Γ (X `⇒ Y)) → Γ ⊇ proj₁ (clo-to-comp (omval-to-mval γ 𝐖))
ctx-clo-to-comp-wk ⋄ (lam M) = Wk.wk-ε
ctx-clo-to-comp-wk (γ · _) (lam M) = wk-id
ctx-clo-to-comp-wk (γ · 𝐖) (var here) = wk-wk (ctx-clo-to-comp-wk γ 𝐖)
ctx-clo-to-comp-wk (γ · _) (var (there i)) = wk-wk (ctx-clo-to-comp-wk γ (var i))
ctx-clo-to-comp-wk (γ ·﹝ _ ╎ _ ╎ _ ﹞) (lam M) = wk-id
ctx-clo-to-comp-wk (γ ·﹝ _ ╎ _ ╎ _ ﹞) (var (there i)) = wk-wk (ctx-clo-to-comp-wk γ (var i))

eval-gc-wkextid-eq : (γ : GCM.MEnv Γ) → (V : Γ ⊢ᵛ (X `⇒ Y)) → EvalGC.Ψ-gc (eval-gc γ {π = wk-id} wkext-id V) ≡ Γ
eval-gc-wkextid-eq ⋄ (Syntax.lam x) = refl
eval-gc-wkextid-eq (γ · x) (Syntax.var here) = refl
eval-gc-wkextid-eq (γ · x) (Syntax.var (there i)) = refl
eval-gc-wkextid-eq (γ · x) (Syntax.lam x₁) = refl
eval-gc-wkextid-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (Syntax.var (there i)) = refl
eval-gc-wkextid-eq (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (Syntax.lam x₃) = refl

lookup-gc-id-next : (γ : GCM.MEnv Γ)→ (𝐖 : GCM.OMVal Γ X)  → (i : Γ ∋ Y) → (π : Γ ⊇ Γ) → (EvalGC.Ψ-gc (lookup-gc (γ · 𝐖) {π = wk-cong π} wkext-id (there i))) ⊇ (EvalGC.Ψ-gc (lookup-gc γ {π = π} wkext-id i))
lookup-gc-id-next γ 𝐖 i (wk-wk π) = ql (wk-absurd wk-id π) _
lookup-gc-id-next {Γ = Γ ∙ X} {X = Y} (γ · x) 𝐖 here (wk-cong π) = wk-wk wk-id
lookup-gc-id-next (γ · x) 𝐖 (there i) (wk-cong π) = wk-wk wk-id
lookup-gc-id-next (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) 𝐖 here (wk-cong π) = wk-wk wk-id
lookup-gc-id-next (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) 𝐖 (there i) (wk-cong π) = wk-wk wk-id

lookup-gc-l-next : (γ : GCM.MEnv Γ) → (M : (Γ ∙ `𝓅) ⊢ᶜ X) → {ρ : Γ ⊇ Δ} → (r : WkExt ρ) → (K : GCM.CStack Δ X) → (i : Γ ∋ Y) → (π : Γ ⊇ Γ) → (EvalGC.Ψ-gc (lookup-gc (γ ·﹝ M ╎ r ╎ K ﹞) {π = wk-cong π} wkext-id (there i))) ⊇ (EvalGC.Ψ-gc (lookup-gc γ {π = π} wkext-id i))
lookup-gc-l-next γ M r K i (wk-wk π) = ql (wk-absurd wk-id π) _
lookup-gc-l-next (γ · x) M r K here (wk-cong π) = wk-wk wk-id
lookup-gc-l-next (γ · x) M r K (there i) (wk-cong π) = wk-wk wk-id
lookup-gc-l-next (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) M r K here (wk-cong π) = wk-wk wk-id
lookup-gc-l-next (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) M r K (there i) (wk-cong π) = wk-wk wk-id

clo-gc-lookup-gc : (γ : GCM.MEnv Γ) → (i : Γ ∋ (X `⇒ Y)) → {π : Γ ⊇ Δ} → (p : WkExt π) → (EvalGC.Ψ-gc (lookup-gc γ p i)) ⊇ (proj₁ (clo-to-comp (omval-to-mval γ (var i))))
clo-gc-lookup-gc ⋄ () {π = π} wkext-id
clo-gc-lookup-gc (γ · 𝐖) (there i) {π = wk-wk π} wkext-id = ql (wk-absurd wk-id π) _
clo-gc-lookup-gc (γ · 𝐖) (there i) {π = wk-cong π} wkext-id = wk-trans (lookup-gc-id-next γ 𝐖 i wk-id) (clo-gc-lookup-gc γ i {π = wk-id} wkext-id)
clo-gc-lookup-gc (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) {π = wk-wk π} wkext-id = ql (wk-absurd wk-id π) _
clo-gc-lookup-gc (γ ·﹝ M ╎ r ╎ K ﹞) (there i) {π = wk-cong π} wkext-id = wk-trans (lookup-gc-l-next γ M r K i wk-id) (clo-gc-lookup-gc γ i {π = wk-id} wkext-id)
clo-gc-lookup-gc (γ · lam M) here {π = π} wkext-id = wk-wk wk-id
clo-gc-lookup-gc (γ · var i) here {π = wk-wk π} wkext-id = ql (wk-absurd wk-id π) _
clo-gc-lookup-gc (γ · var i) here {π = wk-cong π} wkext-id = wk-trans (lookup-gc-id-next γ (var i) i wk-id) (clo-gc-lookup-gc γ i {π = wk-id} wkext-id)
clo-gc-lookup-gc (γ · unit) (there i) (wkext-wk p) = clo-gc-lookup-gc γ i p
clo-gc-lookup-gc (γ · pair 𝐖 𝐖₁) (there i) (wkext-wk p) = clo-gc-lookup-gc γ i p
clo-gc-lookup-gc (γ · lam M) (there i) (wkext-wk p) = clo-gc-lookup-gc γ i p
clo-gc-lookup-gc (γ · var i₂) (there i) (wkext-wk p) = clo-gc-lookup-gc γ i p
clo-gc-lookup-gc (γ · dat N) (there i) (wkext-wk p) = clo-gc-lookup-gc γ i p
clo-gc-lookup-gc (γ · lam M) here (wkext-wk p) = wk-id
clo-gc-lookup-gc (γ · var i) here (wkext-wk p) = clo-gc-lookup-gc γ i p
clo-gc-lookup-gc (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) (wkext-wk p) = clo-gc-lookup-gc γ i p

ctx-wk-clo : (γ : GCM.MEnv Γ) → (i : Γ ∋ (X `⇒ Y)) → (π : Γ ⊇ Γ) → Γ ⊇ (proj₁ (clo-to-comp (M.lookup i (gcmenv-to-menv γ {π = π} wkext-id))))
ctx-wk-clo γ i (wk-wk π) = ql (wk-absurd wk-id π) _
ctx-wk-clo {Γ = Γ ∙ X} (γ · 𝐖) (there i) (wk-cong π) = wk-wk (ctx-wk-clo γ i π)
ctx-wk-clo (γ · lam M) here (wk-cong π) = wk-wk π
ctx-wk-clo {Γ = Γ ∙ (X `⇒ Y)} (γ · var i) here (wk-cong π) = wk-wk (ctx-clo-to-comp-wk γ (var i))
ctx-wk-clo (γ ·﹝ M ╎ p ╎ K ﹞) (there i) (wk-cong π) = wk-wk (ctx-wk-clo γ i π)

clo-gc-ctx-lookup : (γ : GCM.MEnv Γ) → (i : Γ ∋ (X `⇒ Y)) → {π : Γ ⊇ Δ} → (p : WkExt π) → (EvalGC.Ψ-gc (lookup-gc γ p i)) ⊇ (proj₁ (clo-to-comp (M.lookup i (gcmenv-to-menv γ {π = wk-id} wkext-id))))
clo-gc-ctx-lookup (γ · x) (there i) {π = wk-wk π} wkext-id = ql (wk-absurd (Wk.wk-wk π) π) _
clo-gc-ctx-lookup (γ · x) (there i) {π = wk-cong π} wkext-id rewrite sym (wk-id-η π) = wk-wk (ctx-wk-clo γ i π)
clo-gc-ctx-lookup (γ · unit) (there i) (wkext-wk p) = clo-gc-ctx-lookup γ i p
clo-gc-ctx-lookup (γ · pair 𝐖 𝐖₁) (there i) (wkext-wk p) = clo-gc-ctx-lookup γ i p
clo-gc-ctx-lookup (γ · lam M) (there i) (wkext-wk p) = clo-gc-ctx-lookup γ i p
clo-gc-ctx-lookup (γ · var i₂) (there i) (wkext-wk p) = clo-gc-ctx-lookup γ i p
clo-gc-ctx-lookup (γ · dat N) (there i) (wkext-wk p) = clo-gc-ctx-lookup γ i p
clo-gc-ctx-lookup (γ · lam M) here wkext-id = wk-wk wk-id
clo-gc-ctx-lookup (γ · lam M) here (wkext-wk p) = wk-id
clo-gc-ctx-lookup (γ · var i) here wkext-id = wk-wk (ctx-clo-to-comp-wk γ (var i))
clo-gc-ctx-lookup (γ · var i) here (wkext-wk p) =
  let
    goal : Wk (EvalGC.Ψ-gc (lookup-gc γ p i)) (proj₁ (clo-to-comp (omval-to-mval γ (var i))))
    goal = clo-gc-lookup-gc γ i p
  in
  goal
clo-gc-ctx-lookup {Γ = Γ ∙ `ℓ} (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) wkext-id =
  let
    a : Wk Γ (proj₁ (clo-to-comp (M.lookup i (gcmenv-to-menv γ WkExt.wkext-id))))
    a = ctx-wk-clo γ i wk-id
  in
  wk-wk a
clo-gc-ctx-lookup (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) (wkext-wk p) = clo-gc-ctx-lookup γ i p

clo-gc-ctx : (γ : GCM.MEnv Γ) → (V : Γ ⊢ᵛ (X `⇒ Y)) → {π : Γ ⊇ Δ} → (p : WkExt π) → EvalGC.Ψ-gc (eval-gc γ p V) ⊇ proj₁ (clo-to-comp (M.eval V (gcmenv-to-menv γ {π = wk-id} wkext-id)))
clo-gc-ctx γ (lam M) p = wk-id
clo-gc-ctx (γ · 𝐖) (var i) p = clo-gc-ctx-lookup (γ · 𝐖) i p
clo-gc-ctx (γ ·﹝ M ╎ p₁ ╎ K ﹞) (var i) p = clo-gc-ctx-lookup (γ ·﹝ M ╎ p₁ ╎ K ﹞) i p


--------------------------------------------------------------------------

gcmstep-to-mstep : {σ σ₁ : GCM.CState} → (σ →ᴳ σ₁) → Σ[ σᴹ ∈ M.CState ] (((gcmcstate-to-mcstate σ) →ᴹ σᴹ) × σᴹ ≈ᴹ (gcmcstate-to-mcstate σ₁))

gcmstep-to-mstep (eval→ {W = W} {γ = γ} {π = π} {p = p} {K = K}) = _ , eval→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-result (eval-gc-wk γ W p) (wk-cstack γ p W K)))
gcmstep-to-mstep (return→ {𝐖 = 𝐖} {M = M} {γ = γ} {Ψ = Ψ} {K = K} {π = π} {p = p} {π₁ = π₁} {p₁ = p₁}) =
  let
    eqv₀ : ⟨ M ╎ gcmenv-to-menv γ p · omval-to-mval γ 𝐖 ╎ gcmcstack-to-mcstack γ (wkext-trans p p₁) K ⟩ ≈ᴹ ⟨ wk-comp (wk-cong π) M ╎ gcmenv-to-menv γ {π = wk-id} wkext-id · omval-to-mval γ 𝐖 ╎ gcmcstack-to-mcstack γ (wkext-trans p p₁) K ⟩
    eqv₀ = ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp (wk-cong π) refl (wk-menv-cong wk-mval-id (wkmenv-id-eq γ p)) wk-cstack-id))

    eqv : ⟨ M ╎ gcmenv-to-menv γ p · omval-to-mval γ 𝐖 ╎ gcmcstack-to-mcstack γ (wkext-trans p p₁) K ⟩ ≈ᴹ ⟨ wk-comp (wk-cong π) M ╎ gcmenv-to-menv γ {π = wk-id} wkext-id · omval-to-mval γ 𝐖 ╎ gcmcstack-to-mcstack (γ · 𝐖) (wkext-wk (wkext-trans p p₁)) K ⟩
    eqv = subst (λ x → ⟨ M ╎ gcmenv-to-menv γ p · omval-to-mval γ 𝐖 ╎ gcmcstack-to-mcstack γ (wkext-trans p p₁) K ⟩ ≈ᴹ ⟨ wk-comp (wk-cong π) M ╎ gcmenv-to-menv γ {π = wk-id} wkext-id · omval-to-mval γ 𝐖 ╎ x ⟩) (gcmcstack-wk-eq₁ γ 𝐖 (wkext-trans p p₁) K) eqv₀
  in
  _ , return→ , eqv
gcmstep-to-mstep (push→ {M = M} {N = N} {γ = γ} {π = π} {p = p} {K = K}) = _ , push→ , ≈ᴹ-refl
gcmstep-to-mstep (inc→ {M = M} {N = N} {γ = γ} {π = π} {p = p} {K = K}) =
  let
    eqv₀ : ⟨ M ╎ gcmenv-to-menv γ {π = wk-id} wkext-id · jumpᵛ N (gcmenv-to-menv γ {π = wk-id} wkext-id) (gcmcstack-to-mcstack γ p K) ╎ gcmcstack-to-mcstack γ p K ⟩ ≈ᴹ ⟨ M ╎ gcmenv-to-menv γ {π = wk-id} wkext-id · jumpᵛ N (gcmenv-to-menv γ {π = wk-id} wkext-id) (gcmcstack-to-mcstack γ p K) ╎ gcmcstack-to-mcstack γ p K ⟩
    eqv₀ = ≈ᴹ-refl

    eqv : ⟨ M ╎ gcmenv-to-menv γ {π = wk-id} wkext-id · jumpᵛ N (gcmenv-to-menv γ {π = wk-id} wkext-id) (gcmcstack-to-mcstack γ p K) ╎ gcmcstack-to-mcstack γ p K ⟩ ≈ᴹ ⟨ M ╎ gcmenv-to-menv γ {π = wk-id} wkext-id · jumpᵛ N (gcmenv-to-menv γ {π = wk-id} wkext-id) (gcmcstack-to-mcstack γ p K) ╎ gcmcstack-to-mcstack (γ ·﹝ N ╎ p ╎ K ﹞) (wkext-wk p) K ⟩
    eqv = subst (λ x → ⟨ M ╎ gcmenv-to-menv γ wkext-id · jumpᵛ N (gcmenv-to-menv γ wkext-id) (gcmcstack-to-mcstack γ p K) ╎ gcmcstack-to-mcstack γ p K ⟩ ≈ᴹ ⟨ M ╎ gcmenv-to-menv γ wkext-id · jumpᵛ N (gcmenv-to-menv γ wkext-id) (gcmcstack-to-mcstack γ p K) ╎ x ⟩) (gcmcstack-wk-eq γ N p K p K) eqv₀
  in
  _ , inc→ , eqv
gcmstep-to-mstep (rec→ {V = V} {W = W} {γ = γ} {π = π} {p = p} {K = K}) =
  let
    wk : WkCState (jump-to-state (M.eval V (gcmenv-to-menv γ {π = wk-id} WkExt.wkext-id)) (M.eval W (gcmenv-to-menv γ WkExt.wkext-id))) (gcmcstate-to-mcstate (GCM.eval-jump V W γ))
    wk = eval-jump-wk V W γ
    eqv : M.eval-jump V W (gcmenv-to-menv γ wkext-id) ≈ᴹ gcmcstate-to-mcstate (GCM.eval-jump V W γ)
    eqv = ≈ᴹ-bc (≈-wk₂ wk)
  in
  _ , rec→ , eqv
gcmstep-to-mstep (pmᶜ→ {W = W} {γ = γ} {M = M} {π = π} {p = p} {K = K}) =
  let
    wkcs : WkCStack (gcmcstack-to-mcstack (γ · proj₁-omval γ (GCM.eval γ W) · wk-omval (Wk.wk-wk wk-id) (proj₂-omval γ (GCM.eval γ W))) (WkExt.wkext-wk (WkExt.wkext-wk p)) K) (gcmcstack-to-mcstack γ p K)
    wkcs = subst (λ x → WkCStack x (gcmcstack-to-mcstack γ p K)) (sym (gcstackeq (menv-wk-omval (menv-wk-omval (menv-id wk-id γ) (proj₁-omval γ (GCM.eval γ W))) (wk-omval (Wk.wk-wk wk-id) (proj₂-omval γ (GCM.eval γ W)))) (WkExt.wkext-wk (WkExt.wkext-wk p)) p K)) wk-cstack-id
    eqv : ⟨ M ╎ gcmenv-to-menv γ wkext-id · M.eval₁ W (gcmenv-to-menv γ wkext-id) · M.eval₂ W (gcmenv-to-menv γ wkext-id) ╎ gcmcstack-to-mcstack γ p K ⟩ ≈ᴹ
          ⟨ M ╎ gcmenv-to-menv γ wkext-id · omval-to-mval γ (GCM.eval₁ W γ) · omval-to-mval (γ · GCM.eval₁ W γ) (wk-omval (wk-wk wk-id) (GCM.eval₂ W γ)) ╎
                  gcmcstack-to-mcstack (γ · GCM.eval₁ W γ · wk-omval (wk-wk wk-id) (GCM.eval₂ W γ)) (WkExt.wkext-wk (WkExt.wkext-wk p)) K ⟩
    eqv = ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp wk-id (sym (wk-comp-id-β M)) (wk-menv-cong (eval₂-wk γ W) (wk-menv-cong (eval₁-wk γ W) wk-menv-id)) wkcs))
  in
  _ , pmᶜ→ , eqv
gcmstep-to-mstep (app→ {V = V} {W = W} {γ = γ} {π = π} {p = p} {K = K}) =
  let
    π₁  = WkExtSplit.π-part₂ (DiamondSplit.lhs-split (squash (EvalGC.split (eval-gc γ p V)) (EvalGC.split (eval-gc γ p W))))
    π₂  = WkExtSplit.p-part₂ (DiamondSplit.mid-split (squash (EvalGC.split (eval-gc γ p V)) (EvalGC.split (eval-gc γ p W))))
    π₃  = WkExtSplit.π-part₂ (DiamondSplit.rhs-split (squash (EvalGC.split (eval-gc γ p V)) (EvalGC.split (eval-gc γ p W))))
    gc₁ = gc γ π₂
    mv₁ = wk-omval π₃ (EvalGC.result (eval-gc γ p W))

    M₁ = wk-comp (Wk.wk-cong π₁) (lam-to-comp (EvalGC.ψ-gc (eval-gc γ p V)) (EvalGC.result (eval-gc γ p V)))
    M₂ = (proj₁ (proj₂ (clo-to-comp (M.eval V (gcmenv-to-menv γ WkExt.wkext-id)))))
    γ₁ = gcmenv-to-menv gc₁ WkExt.wkext-id                                        · omval-to-mval gc₁ mv₁
    γ₂ = proj₂ (proj₂ (clo-to-comp (M.eval V (gcmenv-to-menv γ WkExt.wkext-id)))) · M.eval W (gcmenv-to-menv γ WkExt.wkext-id)

    p₁ = ((WkExtSplit.p-part₁ (DiamondSplit.mid-split (squash (EvalGC.split (eval-gc γ p V)) (EvalGC.split (eval-gc γ p W))))))
    K₀ = gcmcstack-to-mcstack gc₁ p₁ K
    K₁ = gcmcstack-to-mcstack (gc₁ · mv₁) (WkExt.wkext-wk p₁) K
    K₂ = gcmcstack-to-mcstack γ p K

    ρ : Wk (DiamondSplit.Ψ-merge (squash (EvalGC.split (eval-gc γ p V)) (EvalGC.split (eval-gc γ p W))) ∙ X) (proj₁ (clo-to-comp (M.eval V (gcmenv-to-menv γ {π = wk-id} wkext-id))) ∙ X)
    ρ = wk-cong {!!}

    cseq₁ : K₁ ≡ K₀
    cseq₁ = gcstackeq (menv-wk-omval (menv-id wk-id gc₁) mv₁) (wkext-wk p₁) p₁ K
    cseq₂ : K₂ ≡ K₀
    cseq₂ = gcstackeq {!!} p p₁ K

    wk₁ : WkCState ⟨ M₁ ╎ γ₁ ╎ K₁ ⟩ ⟨ M₂ ╎ γ₂ ╎ K₂ ⟩
    wk₁ = wk-cstate-comp ρ {!!} {!!} (subst (λ x → WkCStack x K₂) (trans cseq₂ (sym cseq₁)) wk-cstack-id)

    eqv = ≈ᴹ-bc (≈-wk₁ wk₁)
  in
  _ , app→ , eqv
