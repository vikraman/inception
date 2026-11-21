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

lookup-wk : (γ : GCM.MEnv Γ) → (i : Γ ∋ X) → {π : Γ ⊇ Δ} → (p : WkExt π)
          → WkMVal (omval-to-mval (ψ-gc (lookup-gc γ p i)) (result (lookup-gc γ p i))) (M.lookup i (gcmenv-to-menv γ {π = wk-id} wkext-id))
lookup-wk ⋄ () p
lookup-wk (γ · 𝐖) here wkext-id =
  let
    goal : WkMVal (omval-to-mval (γ · 𝐖) (wk-omval (Wk.wk-wk wk-id) 𝐖)) (omval-to-mval γ 𝐖)
    goal = omval-wk 𝐖 (menv-wk-omval (menv-id wk-id γ) 𝐖)
  in
  goal

lookup-wk (γ · unit) here (wkext-wk p) = wk-unitᵛ
lookup-wk (γ · (dat D)) here (wkext-wk p) = wk-datᵛ
lookup-wk (γ · pair 𝐕 𝐖) here (wkext-wk p) = wk-pairᵛ wk-mval-id wk-mval-id
lookup-wk (γ · lam M) here (wkext-wk p) = wk-mval-id
lookup-wk (γ · var i) here (wkext-wk p) rewrite sym (lookup-next-eq γ i) = lookup-wk γ i p

lookup-wk (γ · 𝐖) (there i) {π = wk-wk π} wkext-id = ql (wk-absurd wk-id π) _
lookup-wk (γ · 𝐖) (there i) {π = wk-cong π} wkext-id =
  let
    lhs = Ψ-gc (lookup-gc γ {π = π} wkext-id i)
    rhs = Ψ-gc (lookup-gc (γ · 𝐖) {π = wk-cong π} wkext-id (there i))

    IH   : WkMVal (omval-to-mval (ψ-gc (lookup-gc γ wkext-id i)) (result (lookup-gc γ wkext-id i))) (M.lookup (there i) (gcmenv-to-menv γ wkext-id · omval-to-mval γ 𝐖))
    IH = lookup-wk γ i {π = π} wkext-id

    c : WkMVal (omval-to-mval (γ · 𝐖) (wk-omval (lookup-ctx-wk γ i 𝐖 π) (result (lookup-gc γ wkext-id i)))) (omval-to-mval (ψ-gc (lookup-gc γ {π = π} wkext-id i)) (result (lookup-gc γ wkext-id i)))
    c = omval-wk (result (lookup-gc γ wkext-id i)) (lookup-gc-menvext γ i 𝐖 π)

    d : WkMVal (omval-to-mval (ψ-gc (lookup-gc (γ · 𝐖) {π = wk-cong π} wkext-id (there i))) (result (lookup-gc (γ · 𝐖) {π = wk-cong π} wkext-id (there i))))      (omval-to-mval (ψ-gc (lookup-gc γ {π = π} wkext-id i)) (result (lookup-gc γ wkext-id i)))
    d = subst (λ x → WkMVal x (omval-to-mval (ψ-gc (lookup-gc γ {π = π} wkext-id i)) (result (lookup-gc γ wkext-id i)))) (lookup-omval-eq γ i 𝐖 π) c

    goal : WkMVal (omval-to-mval (ψ-gc (lookup-gc (γ · 𝐖) {π = wk-cong π} wkext-id (there i))) (result (lookup-gc (γ · 𝐖) {π = wk-cong π} wkext-id (there i)))) (M.lookup (there i) (gcmenv-to-menv γ wkext-id · omval-to-mval γ 𝐖))
    goal = wk-mval-trans d IH
  in
  goal

lookup-wk (γ · unit) (there i) (wkext-wk p) = lookup-wk γ i p
lookup-wk (γ · (dat D)) (there i) (wkext-wk p) = lookup-wk γ i p
lookup-wk (γ · pair 𝐖 𝐖₁) (there i) (wkext-wk p) = lookup-wk γ i p
lookup-wk (γ · lam M) (there i) (wkext-wk p) = lookup-wk γ i p
lookup-wk (γ · var i₂) (there i) (wkext-wk p) = lookup-wk γ i p

lookup-wk (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here wkext-id = wk-mval-id
lookup-wk (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) here (wkext-wk p) = wk-mval-id

lookup-wk (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) {π = wk-wk π} wkext-id = ql (wk-absurd wk-id π) _
lookup-wk (γ ·﹝ M ╎ p ╎ K ﹞) (there i) {π = wk-cong π} wkext-id =
  let

    IH = lookup-wk γ i {π = π} wkext-id

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

lookup-wk (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (there i) (wkext-wk p) = lookup-wk γ i p

eval-wk : (γ : GCM.MEnv Γ) → (W : Γ ⊢ᵛ X) → {π : Γ ⊇ Δ} → (p : WkExt π)
          → WkMVal (omval-to-mval (ψ-gc (eval-gc γ p W)) (result (eval-gc γ p W))) (M.eval W (gcmenv-to-menv γ {π = wk-id} wkext-id))
eval-wk γ (var i) p =
  let
    goal : WkMVal (omval-to-mval (ψ-gc (lookup-gc γ p i)) (result (lookup-gc γ p i))) (M.lookup i (gcmenv-to-menv γ wkext-id))
    goal = lookup-wk γ i p
  in
  goal
eval-wk {Γ = Γ} γ (lam M) p = wk-cloᵛ wk-id (sym (wk-comp-id-β M)) wk-menv-id
eval-wk {Γ = Γ} {Δ = Δ} γ (pair V W) p =
  let
    mv = (eval-gc γ p V)
    mw = (eval-gc γ p W)
    m = squash (EvalGC.split mv) (EvalGC.split mw)

    d₁ = omval-wk (result mv) (gc-menvext-l γ (ψ-gc mv) (p-part₂ (mid-split m)) (p-part₂ (lhs-split m)) (menvext mv))
    IH₁ = eval-wk γ V p
    goal₁ = wk-mval-trans d₁ IH₁

    d₂ = omval-wk (result mw) (gc-menvext-l γ (ψ-gc mw) (p-part₂ (mid-split m)) (p-part₂ (rhs-split m)) (menvext mw))
    IH₂ = eval-wk γ W p
    goal₂ = wk-mval-trans d₂ IH₂
  in
  wk-pairᵛ goal₁ goal₂
eval-wk γ unit p rewrite omval-unit (ψ-gc (eval-gc γ p unit)) (result (eval-gc γ p unit)) = wk-unitᵛ
eval-wk γ (dat D) p rewrite omval-dat γ p D = wk-datᵛ
eval-wk γ (op o a) p rewrite omval-op γ p o a = wk-datᵛ


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

---- lemmas for sub→ case
gcmcstack-wk-eq : (γ : GCM.MEnv Γ) → (N : (Γ ∙ `𝓅) ⊢ᶜ X) → {π : Γ ⊇ Δ} → (p : WkExt π) → (K : GCM.CStack Δ X)
                  → {π₁ : Γ ⊇ Ψ} → (p₁ : WkExt π₁) → (K₁ : GCM.CStack Ψ X₁)
                  → gcmcstack-to-mcstack γ p₁ K₁ ≡ gcmcstack-to-mcstack (γ ·﹝ N ╎ p ╎ K ﹞) (wkext-wk p₁) K₁
gcmcstack-wk-eq γ N p K p₁ ◻ = refl
gcmcstack-wk-eq γ N p K p₁ (< N₂ ； wkext-id >∷ K₁) = cong (< N₂ ； gcmenv-to-menv γ p₁ >∷_) (gcmcstack-wk-eq γ N p K p₁ K₁)
gcmcstack-wk-eq γ N p K p₁ (< N₂ ； wkext-wk p₂ >∷ K₁) = cong (< N₂ ； gcmenv-to-menv γ p₁ >∷_) (gcmcstack-wk-eq γ N p K (wkext-trans p₁ (wkext-wk p₂)) K₁)


--------------------------------------------------------------------------

-- halting work on this in favour of work on IncV version of the GC machine
gcmstep-to-mstep : {σ σ₁ : GCM.CState} → (σ →ᴳ σ₁) → Σ[ σᴹ ∈ M.CState ] (((gcmcstate-to-mcstate σ) →ᴹ σᴹ) × σᴹ ≈ᴹ (gcmcstate-to-mcstate σ₁))

gcmstep-to-mstep (eval→ {W = W} {γ = γ} {π = π} {p = p} {K = K}) = _ , eval→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-result (eval-wk γ W p) (wk-cstack γ p W K)))
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
gcmstep-to-mstep rec→ = _ , rec→ , {!!}
gcmstep-to-mstep pmᶜ→ = _ , pmᶜ→ , {!!}
gcmstep-to-mstep app→ = _ , app→ , {!!}
