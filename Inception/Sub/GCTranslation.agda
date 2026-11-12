{-# OPTIONS --no-postfix-projections #-}

open import Inception.Sub.Syntax using (Ty)

module Inception.Sub.GCTranslation (ℛ : Ty) where

open import Inception.Prelude
open import Inception.Rewriting
open import Inception.Sub.Syntax

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; subst₂; cong; cong₂; sym; dcong₂; trans)

open import Inception.Sub.GCMachine ℛ as GCM renaming (_→ᶜ_ to _→ᴳ_)
open import Inception.Sub.Machine ℛ as M renaming (_→ᶜ_ to _→ᴹ_)

open import Inception.Sub.MachineProps ℛ as MProps

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
  omval-to-mval γ (pair 𝐖₁ 𝐖₂) = pairᵛ (omval-to-mval γ 𝐖₁) (omval-to-mval γ 𝐖₂)
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

---- lemmas for eval→ case

wk-omval-id-β : {𝐖 : GCM.OMVal Γ X} → wk-omval wk-id 𝐖 ≡ 𝐖
wk-omval-id-β {𝐖 = unit} = refl
wk-omval-id-β {𝐖 = pair 𝐕 𝐖} = cong₂ pair wk-omval-id-β wk-omval-id-β
wk-omval-id-β {𝐖 = lam M} = refl
wk-omval-id-β {𝐖 = var i} = refl

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

omval-wk-drop₂ : (M : Γ ⊢ᶜ Y) → {ρ : Γ ⊇ Ψ} → (r : WkExt ρ) → (K : GCM.CStack Ψ Y) → (𝐖 : GCM.OMVal Δ X) → (π : Γ ⊇ Δ) → (γ : GCM.MEnv Γ)
                → WkMVal (omval-to-mval (γ ·﹝ M ╎ r ╎ K ﹞) (wk-omval (Wk.wk-wk π) 𝐖)) (omval-to-mval γ (wk-omval π 𝐖))
omval-wk-drop₂ M r K unit π γ = wk-unitᵛ
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
gc-menvext-l γ δ {π₁ = π₁} wkext-id wkext-id (menv-id π γ₁) rewrite gc-wkext-id γ π₁ = {!!}
gc-menvext-l γ δ {π₁ = π₁} wkext-id wkext-id (menv-wk-omval {π = π} mx 𝐖) rewrite gc-wkext-id γ π₁ = ql (wk-absurd wk-id π) _
gc-menvext-l γ δ {π₁ = π₁} wkext-id wkext-id (menv-wk-jump {π = π} mx M r K) rewrite gc-wkext-id γ π₁ = ql (wk-absurd wk-id π) _
gc-menvext-l γ δ {π₁ = π₁} wkext-id {π₂ = wk-wk π₂} (wkext-wk p₂) (menv-id π γ₁) = ql (wk-absurd wk-id π₂) _
gc-menvext-l γ δ {π₁ = π₁} wkext-id (wkext-wk p₂) (menv-wk-omval mx 𝐖) rewrite gc-wkext-id γ π₁ = menv-wk-omval {!!} 𝐖
gc-menvext-l γ δ {π₁ = π₁} wkext-id (wkext-wk p₂) (menv-wk-jump mx M r K) rewrite gc-wkext-id γ π₁ = menv-wk-jump {!!} M r K
gc-menvext-l γ δ {π₁ = wk-wk π₁} (wkext-wk p₁) {π₂ = π₂} p₂ {π₃ = π₃} (menv-id π γ₁) = ql (wk-absurd wk-id (wk-trans π₁ π₂)) _
gc-menvext-l γ δ (wkext-wk p₁) p₂ (menv-wk-omval mx 𝐖) = gc-menvext-l _ δ p₁ p₂ mx
gc-menvext-l γ δ (wkext-wk p₁) p₂ (menv-wk-jump mx M r K) = gc-menvext-l _ δ p₁ p₂ mx


open GCM.EvalGC
open GCM.WkExtSplit
open GCM.DiamondSplit

lookup-wk : (γ : GCM.MEnv Γ) → (i : Γ ∋ X) → {π : Γ ⊇ Δ} → (p : WkExt π)
          → WkMVal (M.lookup i (gcmenv-to-menv γ {π = wk-id} wkext-id)) (omval-to-mval (ψ-gc (lookup-gc γ p i)) (result (lookup-gc γ p i)))
lookup-wk ⋄ () p
lookup-wk (γ · unit) here wkext-id = wk-unitᵛ
lookup-wk (γ · unit) here (wkext-wk p) = wk-unitᵛ
lookup-wk (γ · pair 𝐕 𝐖) here wkext-id = wk-pairᵛ {!!} {!!}
lookup-wk (γ · pair 𝐕 𝐖) here (wkext-wk p) = {!!}
lookup-wk (γ · lam M) here wkext-id = {!!}
lookup-wk (γ · lam M) here (wkext-wk p) = {!!}
lookup-wk (γ · var i) here wkext-id = {!!}
lookup-wk (γ · var i) here (wkext-wk p) = {!!}
{-
  let
    goal₀ : WkMVal (omval-to-mval γ 𝐖) (omval-to-mval γ 𝐖)
    goal₀ = wk-mval-id

    --goal : WkMVal (omval-to-mval (ψ-gc (lookup-gc (γ · 𝐖) p here)) (result (lookup-gc (γ · 𝐖) p here))) (M.lookup here (gcmenv-to-menv γ wkext-id · omval-to-mval γ 𝐖))
    goal : WkMVal (omval-to-mval γ 𝐖) (omval-to-mval (ψ-gc (lookup-gc (γ · 𝐖) p here)) (result (lookup-gc (γ · 𝐖) p here)))
    goal = {!!}
  in
  goal
-}
lookup-wk (γ · 𝐖) (there i) p = {!!}
lookup-wk (γ ·﹝ M ╎ p₁ ╎ K ﹞) here p = {!!}
lookup-wk (γ ·﹝ M ╎ p₁ ╎ K ﹞) (there i) p = {!!}

eval-wk : (γ : GCM.MEnv Γ) → (W : Γ ⊢ᵛ X) → {π : Γ ⊇ Δ} → (p : WkExt π)
          → WkMVal (omval-to-mval (ψ-gc (eval-gc γ p W)) (result (eval-gc γ p W))) (M.eval W (gcmenv-to-menv γ {π = wk-id} wkext-id))
eval-wk γ (var i) p =
  let
    goal : WkMVal (omval-to-mval (ψ-gc (lookup-gc γ p i)) (result (lookup-gc γ p i))) (M.lookup i (gcmenv-to-menv γ wkext-id))
    goal = {!!}
  in
  goal
eval-wk {Γ = Γ} γ (lam M) p = wk-cloᵛ wk-id refl wk-menv-id
eval-wk {Γ = Γ} {Δ = Δ} γ (pair V W) p =
  let
    mv = (eval-gc γ p V)
    mw = (eval-gc γ p W)
    m = squash (split mv) (split mw)

    d₁ = omval-wk (result mv) (gc-menvext-l γ (ψ-gc mv) (p-part₂ (mid-split m)) (p-part₂ (lhs-split m)) (menvext mv))
    IH₁ = eval-wk γ V p
    goal₁ = wk-mval-trans d₁ IH₁

    d₂ = omval-wk (result mw) (gc-menvext-l γ (ψ-gc mw) (p-part₂ (mid-split m)) (p-part₂ (rhs-split m)) (menvext mw))
    IH₂ = eval-wk γ W p
    goal₂ = wk-mval-trans d₂ IH₂
  in
  wk-pairᵛ goal₁ goal₂
eval-wk γ unit p rewrite omval-unit (ψ-gc (eval-gc γ p unit)) (result (eval-gc γ p unit)) = wk-unitᵛ


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
gcmcstack-wk-eq₁ γ 𝐖 p (< N ； wkext-id >∷ K) = cong (< N ； gcmenv-to-menv γ p >∷_) (gcmcstack-wk-eq₁ γ 𝐖 (wkext-trans p {ρ = wk-id} wkext-id) K)
gcmcstack-wk-eq₁ γ 𝐖 p (< N ； wkext-wk p₁ >∷ K) = cong (< N ； gcmenv-to-menv γ p >∷_) (gcmcstack-wk-eq₁ γ 𝐖 (wkext-trans p (wkext-wk p₁)) K)

---- lemmas for sub→ case
gcmcstack-wk-eq : (γ : GCM.MEnv Γ) → (N : Γ ⊢ᶜ X) → {π : Γ ⊇ Δ} → (p : WkExt π) → (K : GCM.CStack Δ X)
                  → {π₁ : Γ ⊇ Ψ} → (p₁ : WkExt π₁) → (K₁ : GCM.CStack Ψ X₁)
                  → gcmcstack-to-mcstack γ p₁ K₁ ≡ gcmcstack-to-mcstack (γ ·﹝ N ╎ p ╎ K ﹞) (wkext-wk p₁) K₁
gcmcstack-wk-eq γ N p K p₁ ◻ = refl
gcmcstack-wk-eq γ N p K p₁ (< N₂ ； wkext-id >∷ K₁) = cong (< N₂ ； gcmenv-to-menv γ p₁ >∷_) (gcmcstack-wk-eq γ N p K p₁ K₁)
gcmcstack-wk-eq γ N p K p₁ (< N₂ ； wkext-wk p₂ >∷ K₁) = cong (< N₂ ； gcmenv-to-menv γ p₁ >∷_) (gcmcstack-wk-eq γ N p K (wkext-trans p₁ (wkext-wk p₂)) K₁)


--------------------------------------------------------------------------


gcmstep-to-mstep : {σ σ₁ : GCM.CState} → (σ →ᴳ σ₁) → Σ[ σᴹ ∈ M.CState ] (((gcmcstate-to-mcstate σ) →ᴹ σᴹ) × σᴹ ≈ᴹ (gcmcstate-to-mcstate σ₁))
gcmstep-to-mstep (eval→ {W = W} {γ = γ} {π = π} {p = p} {K = K}) =
  _ , eval→ , ≈ᴹ-bc (≈-wk₁ (wk-cstate-result (eval-wk γ W p) {!!}))
gcmstep-to-mstep (return→ {𝐖 = 𝐖} {M = M} {γ = γ} {Ψ = Ψ} {K = K} {π = π} {p = p} {π₁ = π₁} {p₁ = p₁}) =
  let
    eqv₀ : ⟨ M ╎ gcmenv-to-menv γ p · omval-to-mval γ 𝐖 ╎ gcmcstack-to-mcstack γ (wkext-trans p p₁) K ⟩ ≈ᴹ ⟨ wk-comp (wk-cong π) M ╎ gcmenv-to-menv γ {π = wk-id} wkext-id · omval-to-mval γ 𝐖 ╎ gcmcstack-to-mcstack γ (wkext-trans p p₁) K ⟩
    eqv₀ = ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp (wk-cong π) refl (wk-menv-cong wk-mval-id (wkmenv-id-eq γ p)) wk-cstack-id))

    eqv : ⟨ M ╎ gcmenv-to-menv γ p · omval-to-mval γ 𝐖 ╎ gcmcstack-to-mcstack γ (wkext-trans p p₁) K ⟩ ≈ᴹ ⟨ wk-comp (wk-cong π) M ╎ gcmenv-to-menv γ {π = wk-id} wkext-id · omval-to-mval γ 𝐖 ╎ gcmcstack-to-mcstack (γ · 𝐖) (wkext-wk (wkext-trans p p₁)) K ⟩
    eqv = subst (λ x → ⟨ M ╎ gcmenv-to-menv γ p · omval-to-mval γ 𝐖 ╎ gcmcstack-to-mcstack γ (wkext-trans p p₁) K ⟩ ≈ᴹ ⟨ wk-comp (wk-cong π) M ╎ gcmenv-to-menv γ {π = wk-id} wkext-id · omval-to-mval γ 𝐖 ╎ x ⟩) (gcmcstack-wk-eq₁ γ 𝐖 (wkext-trans p p₁) K) eqv₀
  in
  _ , return→ , eqv
gcmstep-to-mstep (push→ {M = M} {N = N} {γ = γ} {π = π} {p = p} {K = K}) = _ , push→ , ≈ᴹ-refl
gcmstep-to-mstep (sub→ {M = M} {N = N} {γ = γ} {π = π} {p = p} {K = K}) =
  let
    eqv₀ : ⟨ M ╎ gcmenv-to-menv γ {π = wk-id} wkext-id · jumpᵛ N (gcmenv-to-menv γ {π = wk-id} wkext-id) (gcmcstack-to-mcstack γ p K) ╎ gcmcstack-to-mcstack γ p K ⟩ ≈ᴹ ⟨ M ╎ gcmenv-to-menv γ {π = wk-id} wkext-id · jumpᵛ N (gcmenv-to-menv γ {π = wk-id} wkext-id) (gcmcstack-to-mcstack γ p K) ╎ gcmcstack-to-mcstack γ p K ⟩
    eqv₀ = ≈ᴹ-refl

    eqv : ⟨ M ╎ gcmenv-to-menv γ {π = wk-id} wkext-id · jumpᵛ N (gcmenv-to-menv γ {π = wk-id} wkext-id) (gcmcstack-to-mcstack γ p K) ╎ gcmcstack-to-mcstack γ p K ⟩ ≈ᴹ ⟨ M ╎ gcmenv-to-menv γ {π = wk-id} wkext-id · jumpᵛ N (gcmenv-to-menv γ {π = wk-id} wkext-id) (gcmcstack-to-mcstack γ p K) ╎ gcmcstack-to-mcstack (γ ·﹝ N ╎ p ╎ K ﹞) (wkext-wk p) K ⟩
    eqv = subst (λ x → ⟨ M ╎ gcmenv-to-menv γ wkext-id · jumpᵛ N (gcmenv-to-menv γ wkext-id) (gcmcstack-to-mcstack γ p K) ╎ gcmcstack-to-mcstack γ p K ⟩ ≈ᴹ ⟨ M ╎ gcmenv-to-menv γ wkext-id · jumpᵛ N (gcmenv-to-menv γ wkext-id) (gcmcstack-to-mcstack γ p K) ╎ x ⟩) (gcmcstack-wk-eq γ N p K p K) eqv₀
  in
  _ , sub→ , eqv
gcmstep-to-mstep var→ = _ , var→ , {!!}
gcmstep-to-mstep pmᶜ→ = _ , pmᶜ→ , {!!}
gcmstep-to-mstep app→ = _ , app→ , {!!}

--------------------------------------------------------------------------
--------------------------------------------------------------------------


{- XXX
--------------------------------------------------------------------------
-- lemmas for tmstep-to-mstep
--------------------------------------------------------------------------

--------------------------------------------------------------------------
---- lemmas for eval→ case

wk-omval-wk-comm : {𝐕 : TM.OMVal Γ X} → (𝐖 : TM.OMVal Γ Y) → (γ : TM.MEnv Γ) → WkMVal (mclo-to-mval (TM.wk-omval (Wk.wk-wk wk-id) 𝐖) (γ · 𝐕)) (mclo-to-mval 𝐖 γ)
wk-omval-wk-comm unit ⋄ = wk-unitᵛ
wk-omval-wk-comm unit (γ · x) = wk-unitᵛ
wk-omval-wk-comm unit (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-unitᵛ
wk-omval-wk-comm (pair 𝐖 𝐕) ⋄ = wk-pairᵛ (wk-omval-wk-comm 𝐖 ⋄) (wk-omval-wk-comm 𝐕 ⋄)
wk-omval-wk-comm (pair 𝐖 𝐕) (γ · x) = wk-pairᵛ (wk-omval-wk-comm 𝐖 (γ · x)) (wk-omval-wk-comm 𝐕 (γ · x))
wk-omval-wk-comm (pair 𝐖 𝐕) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-pairᵛ (wk-omval-wk-comm 𝐖 (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) (wk-omval-wk-comm 𝐕 (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞))
wk-omval-wk-comm {𝐕 = 𝐕} (lam M) ⋄ = wk-cloᵛ (wk-wk wk-ε) refl (wk-menv-wk (mclo-to-mval 𝐕 ⋄) wk-menv-ε)
wk-omval-wk-comm (lam M) (γ · x) = wk-cloᵛ (wk-wk wk-id) refl (wk-menv-wk _ MProps.wk-menv-id)
wk-omval-wk-comm (lam M) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-cloᵛ (wk-wk wk-id) refl (wk-menv-wk _ MProps.wk-menv-id)
wk-omval-wk-comm (label x) (γ · x₁) = wk-mval-id
wk-omval-wk-comm (label x) (γ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) = wk-mval-id

wk-omval-wk-jump-comm : {M : Γ ⊢ᶜ X} {π : Γ ⊇ Δ} {K : TM.CStack Δ X} → (𝐖 : TM.OMVal Γ Y) → (γ : TM.MEnv Γ) → WkMVal (mclo-to-mval (TM.wk-omval (Wk.wk-wk wk-id) 𝐖) (γ ·﹝ M ╎ π ╎ K ﹞)) (mclo-to-mval 𝐖 γ)
wk-omval-wk-jump-comm unit ⋄ = wk-unitᵛ
wk-omval-wk-jump-comm unit (γ · x) = wk-unitᵛ
wk-omval-wk-jump-comm unit (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-unitᵛ
wk-omval-wk-jump-comm (pair 𝐕 𝐖) ⋄ = wk-pairᵛ (wk-omval-wk-jump-comm 𝐕 ⋄) (wk-omval-wk-jump-comm 𝐖 ⋄)
wk-omval-wk-jump-comm (pair 𝐕 𝐖) (γ · x) = wk-pairᵛ (wk-omval-wk-jump-comm 𝐕 (γ · x)) (wk-omval-wk-jump-comm 𝐖 (γ · x))
wk-omval-wk-jump-comm (pair 𝐕 𝐖) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-pairᵛ (wk-omval-wk-jump-comm 𝐕 (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) (wk-omval-wk-jump-comm 𝐖 (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞))
wk-omval-wk-jump-comm (lam M) ⋄ = wk-cloᵛ (wk-wk wk-ε) refl (wk-menv-wk (M.jumpᵛ _ (tmenv-to-menv ⋄) (tmcstack-to-mcstack _)) wk-menv-ε)
wk-omval-wk-jump-comm (lam M) (γ · x) = wk-cloᵛ (wk-wk wk-id) refl (wk-menv-wk _ MProps.wk-menv-id)
wk-omval-wk-jump-comm (lam M) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-cloᵛ (wk-wk wk-id) refl (wk-menv-wk _ MProps.wk-menv-id)
wk-omval-wk-jump-comm (label x) (γ · x₁) = wk-mval-id
wk-omval-wk-jump-comm (label x) (γ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) = wk-mval-id

lookup-wk : (i : Γ ∋ X) → (γ : TM.MEnv Γ) → WkMVal (mclo-to-mval (TM.lookup i γ) γ) (M.lookup i (tmenv-to-menv γ))
lookup-wk here (γ · x) = wk-omval-wk-comm x γ
lookup-wk here (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-omval-wk-comm {𝐕 = label here} (label here) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)
lookup-wk {X = X} (there i) (γ · x) = wk-mval-trans (wk-omval-wk-comm (TM.lookup i γ) γ) (lookup-wk i γ)
lookup-wk (there i) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-mval-trans (wk-omval-wk-jump-comm (TM.lookup i γ) γ) (lookup-wk i γ)

eval-wk : (W : Γ ⊢ᵛ X) → (γ : TM.MEnv Γ) → WkMVal (mclo-to-mval (TM.eval W γ) γ) (M.eval W (tmenv-to-menv γ))
eval-wk (var i) (γ · 𝐖) = lookup-wk i (γ · 𝐖)
eval-wk (var i) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = lookup-wk i (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)
eval-wk (lam x) ⋄ = wk-mval-id
eval-wk (lam x) (γ · x₁) = wk-mval-id
eval-wk (lam x) (γ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) = wk-mval-id
eval-wk (pair V W) ⋄ = wk-pairᵛ (eval-wk V ⋄) (eval-wk W ⋄)
eval-wk (pair V W) (γ · x) = wk-pairᵛ (eval-wk V (γ · x)) (eval-wk W (γ · x))
eval-wk (pair V W) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-pairᵛ (eval-wk V (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) (eval-wk W (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞))
eval-wk unit ⋄ = wk-mval-id
eval-wk unit (γ · x) = wk-mval-id
eval-wk unit (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-mval-id

--------------------------------------------------------------------------
---- lemmas for return→ case

mutual

  wkmval : {Γ Δ : Ctx} → (𝐖 : TM.OMVal Δ X) → (π : Γ ⊇ Δ) → (γ : TM.MEnv Γ) → (δ : TM.MEnv Δ) → TMProps.WkMEnv π γ δ → WkMVal (mclo-to-mval (TM.wk-omval π 𝐖) γ) (mclo-to-mval 𝐖 δ)
  wkmval TM.unit π γ δ g = wk-unitᵛ
  wkmval (TM.pair 𝐖 𝐕) π γ δ g = wk-pairᵛ (wkmval 𝐖 π γ δ g) (wkmval 𝐕 π γ δ g)
  wkmval (TM.lam M) π γ δ g = wk-cloᵛ π refl (wk-MEnvᵀ-to-wk-MEnvᴹ g)
  wkmval (label here) π γ (δ · (label x)) (wk-tmenv-omval-cong 𝐖 g) = wkmval (label x) _ _ _ g
  wkmval (label here) π γ δ (wk-tmenv-jump-cong {π = π₁} M πᵀ K g) = wk-jumpᵛ π₁ refl (wk-MEnvᵀ-to-wk-MEnvᴹ g) wk-cstack-id
  wkmval (label here) π γ δ (wk-tmenv-omval-wk 𝐖 g) = wkmval (label here) _ _ _ g
  wkmval (label here) π γ δ (wk-tmenv-jump-wk M πᵀ K g) = wkmval (label here) _ _ _ g
  wkmval (label (there x)) π γ δ (wk-tmenv-omval-cong 𝐖 g) = wkmval (label x) _ _ _ g
  wkmval (label (there x)) π γ δ (wk-tmenv-jump-cong M πᵀ K g) = wkmval (label x) _ _ _ g
  wkmval (label (there x)) π γ δ (wk-tmenv-omval-wk 𝐖 g) = wkmval (label (there x)) _ _ _ g
  wkmval (label (there x)) π γ δ (wk-tmenv-jump-wk M πᵀ K g) = wkmval (label (there x)) _ _ _ g

  wk-MEnvᵀ-to-wk-MEnvᴹ : {Γ Δ : Ctx} {π : Γ ⊇ Δ} {γ : TM.MEnv Γ} {δ : TM.MEnv Δ} → TMProps.WkMEnv π γ δ → MProps.WkMEnv π (tmenv-to-menv γ) (tmenv-to-menv δ)
  wk-MEnvᵀ-to-wk-MEnvᴹ wk-tmenv-ε = wk-menv-ε
  wk-MEnvᵀ-to-wk-MEnvᴹ (wk-tmenv-omval-cong {π = π} {γ = γ} {δ = δ} 𝐖 g) =
    let
      a₀ : WkMVal (mclo-to-mval (TM.wk-omval π 𝐖) γ) (mclo-to-mval 𝐖 δ)
      a₀ = wkmval 𝐖 π γ δ g
      a₁ = wk-menv-cong a₀ (wk-MEnvᵀ-to-wk-MEnvᴹ g)
    in
    a₁
  wk-MEnvᵀ-to-wk-MEnvᴹ (wk-tmenv-jump-cong M πᵀ K g) =
    let
      a₀ = wk-jumpᵛ _ refl (wk-MEnvᵀ-to-wk-MEnvᴹ g) wk-cstack-id
      a₁ = wk-menv-cong a₀ (wk-MEnvᵀ-to-wk-MEnvᴹ g)
    in
    a₁
  wk-MEnvᵀ-to-wk-MEnvᴹ (wk-tmenv-omval-wk 𝐖 g) = wk-menv-wk (mclo-to-mval 𝐖 _) (wk-MEnvᵀ-to-wk-MEnvᴹ g)
  wk-MEnvᵀ-to-wk-MEnvᴹ (wk-tmenv-jump-wk M πᵀ K g) = wk-menv-wk (M.jumpᵛ M (tmenv-to-menv _) (tmcstack-to-mcstack K)) (wk-MEnvᵀ-to-wk-MEnvᴹ g)

--------------------------------------------------------------------------
---- lemmas for var→ case

lookup-eq : (i : Γ ∋ `ℓ) → (γ : TM.MEnv Γ) → (M.lookup i (tmenv-to-menv γ)) ≡ (mclo-to-mval (label i) γ)
lookup-eq here (γ · (label x)) = refl
lookup-eq here (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = refl
lookup-eq (there x) (γ · x₁) = lookup-eq x γ
lookup-eq (there x) (γ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) = lookup-eq x γ

lookup-label-wk : (i : Γ ∋ `ℓ) → (γ : TM.MEnv Γ) → MProps.WkCState (M.jump-to-state (M.lookup i (tmenv-to-menv γ))) (tmcstate-to-mcstate (TM.lookup-label i γ))
lookup-label-wk here (γ · (label x)) =
  let
    a : MProps.WkCState (M.jump-to-state (M.lookup x (tmenv-to-menv γ))) (tmcstate-to-mcstate (TM.lookup-label x γ))
    a = lookup-label-wk x γ
    goal : MProps.WkCState (M.jump-to-state (mclo-to-mval (label x) γ)) (tmcstate-to-mcstate (TM.lookup-label x γ))
    goal = subst (λ z → MProps.WkCState (M.jump-to-state z) (tmcstate-to-mcstate (TM.lookup-label x γ))) (lookup-eq x γ) a
  in
  goal
lookup-label-wk here (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-cstate-comp wk-id refl MProps.wk-menv-id wk-cstack-id
lookup-label-wk (there i) (γ · 𝐖) = lookup-label-wk i γ
lookup-label-wk (there i) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = lookup-label-wk i γ

eval-jump-wk : (W : Γ ⊢ᵛ `ℓ) → (γ : TM.MEnv Γ) → MProps.WkCState (M.eval-jump W (tmenv-to-menv γ)) (tmcstate-to-mcstate (TM.eval-jump W γ))
eval-jump-wk (var i) γ = lookup-label-wk i γ

--------------------------------------------------------------------------
---- lemmas for pmᶜ→ case

proj₁-wk-mval-eq : (𝐖 : TM.OMVal Γ (X `× Y)) → (γ : TM.MEnv Γ) → (M.proj₁-val (mclo-to-mval 𝐖 γ)) ≡ (mclo-to-mval (TM.proj₁-omval 𝐖) γ)
proj₁-wk-mval-eq (pair 𝐕 𝐖) ⋄ = refl
proj₁-wk-mval-eq (pair 𝐕 𝐖) (γ · x) = refl
proj₁-wk-mval-eq (pair 𝐕 𝐖) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = refl

proj₂-wk-mval-eq : (𝐖 : TM.OMVal Γ (X `× Y)) → (γ : TM.MEnv Γ) → (M.proj₂-val (mclo-to-mval 𝐖 γ)) ≡ (mclo-to-mval (TM.proj₂-omval 𝐖) γ)
proj₂-wk-mval-eq (pair 𝐕 𝐖) ⋄ = refl
proj₂-wk-mval-eq (pair 𝐕 𝐖) (γ · x) = refl
proj₂-wk-mval-eq (pair 𝐕 𝐖) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = refl

eval₁-wk : (W : Γ ⊢ᵛ (X `× Y)) → (γ : TM.MEnv Γ) → WkMVal (mclo-to-mval (TM.proj₁-omval (TM.eval W γ)) γ) (M.proj₁-val (M.eval W (tmenv-to-menv γ)))
eval₁-wk W γ =
  let
    goal′ : WkMVal (M.proj₁-val (mclo-to-mval (TM.eval W γ) γ)) (M.proj₁-val (M.eval W (tmenv-to-menv γ)))
    goal′ = proj₁-wk-mval (eval-wk W γ)

    goal : WkMVal (mclo-to-mval (TM.proj₁-omval (TM.eval W γ)) γ) (M.proj₁-val (M.eval W (tmenv-to-menv γ)))
    goal = subst (λ x → WkMVal x (M.proj₁-val (M.eval W (tmenv-to-menv γ)))) (proj₁-wk-mval-eq (TM.eval W γ) γ) goal′
  in
  goal

eval₂-wk : (W : Γ ⊢ᵛ (X `× Y)) → (γ : TM.MEnv Γ) → WkMVal (mclo-to-mval (TM.wk-omval (Wk.wk-wk wk-id) (TM.proj₂-omval (TM.eval W γ))) (γ · TM.proj₁-omval (TM.eval W γ))) (M.proj₂-val (M.eval W (tmenv-to-menv γ)))
eval₂-wk W γ =
  let
    goal′ : WkMVal (M.proj₂-val (mclo-to-mval (TM.eval W γ) γ)) (M.proj₂-val (M.eval W (tmenv-to-menv γ)))
    goal′ = proj₂-wk-mval (eval-wk W γ)

    goal′′ : WkMVal (mclo-to-mval (TM.proj₂-omval (TM.eval W γ)) γ) (M.proj₂-val (M.eval W (tmenv-to-menv γ)))
    goal′′ = subst (λ x → WkMVal x (M.proj₂-val (M.eval W (tmenv-to-menv γ)))) (proj₂-wk-mval-eq (TM.eval W γ) γ) goal′

    goal : WkMVal (mclo-to-mval (TM.wk-omval (Wk.wk-wk wk-id) (TM.proj₂-omval (TM.eval W γ))) (γ · TM.proj₁-omval (TM.eval W γ))) (M.proj₂-val (M.eval W (tmenv-to-menv γ)))
    goal = wk-mval-trans (wk-omval-wk-comm (TM.proj₂-omval (TM.eval W γ)) γ) goal′′
  in
  goal

--------------------------------------------------------------------------
---- lemmas for app→ case

ctx-clo-to-comp-wk : (W : Γ ⊢ᵛ (X `⇒ Y)) → (γ : TM.MEnv Γ) → Γ ⊇ (proj₁ (M.clo-to-comp (M.eval W (tmenv-to-menv γ))))
ctx-clo-to-comp-wk {Γ = Γ ∙ (X `⇒ Y)} (var here) (γ · lam M) = wk-wk wk-id
ctx-clo-to-comp-wk (var (there i)) (γ · 𝐖) = wk-wk (ctx-clo-to-comp-wk (var i) γ)
ctx-clo-to-comp-wk (var (there i)) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-wk (ctx-clo-to-comp-wk (var i) γ)
ctx-clo-to-comp-wk (lam M) ⋄ = wk-id
ctx-clo-to-comp-wk (lam M) (γ · 𝐖) = wk-id
ctx-clo-to-comp-wk (lam M) (γ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) = wk-id

clo-to-comp-eq : (W : Γ ⊢ᵛ (X `⇒ Y)) → (γ : TM.MEnv Γ) → TM.lam-to-comp (TM.eval W γ) ≡ wk-comp (wk-cong (ctx-clo-to-comp-wk W γ)) (proj₁ (proj₂ (M.clo-to-comp (M.eval W (tmenv-to-menv γ)))))
clo-to-comp-eq (var here) (γ · lam M) = refl
clo-to-comp-eq {Γ = Γ ∙ Z} (var (there i)) (γ · 𝐖) with (TM.lookup i γ) in eq
... | lam M =
  let
    a₀ : TM.lookup i γ ≡ lam M
    a₀ = eq

    a₁ : TM.lam-to-comp (TM.lookup i γ) ≡ wk-comp (wk-cong (ctx-clo-to-comp-wk (var i) γ)) (proj₁ (proj₂ (M.clo-to-comp (M.eval (var i) (tmenv-to-menv γ)))))
    a₁ = clo-to-comp-eq (var i) γ

    a₂ : M ≡ wk-comp (wk-cong (ctx-clo-to-comp-wk (var i) γ)) (proj₁ (proj₂ (M.clo-to-comp (M.eval (var i) (tmenv-to-menv γ)))))
    a₂ = subst (λ x → TM.lam-to-comp x ≡ wk-comp (wk-cong (ctx-clo-to-comp-wk (var i) γ)) (proj₁ (proj₂ (M.clo-to-comp (M.eval (var i) (tmenv-to-menv γ)))))) a₀ a₁

    goal : wk-comp (Wk.wk-cong (Wk.wk-wk wk-id)) M ≡ wk-comp (Wk.wk-cong (Wk.wk-wk (ctx-clo-to-comp-wk (var i) γ))) (proj₁ (proj₂ (M.clo-to-comp (M.lookup i (tmenv-to-menv γ)))))
    goal = cong (wk-comp (Wk.wk-cong (Wk.wk-wk wk-id))) a₂
  in
  goal
clo-to-comp-eq (var (there i)) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)  with (TM.lookup i γ) in eq
... | lam M =
  let
    a₀ : TM.lookup i γ ≡ lam M
    a₀ = eq

    a₁ : TM.lam-to-comp (TM.lookup i γ) ≡ wk-comp (wk-cong (ctx-clo-to-comp-wk (var i) γ)) (proj₁ (proj₂ (M.clo-to-comp (M.eval (var i) (tmenv-to-menv γ)))))
    a₁ = clo-to-comp-eq (var i) γ

    a₂ : M ≡ wk-comp (wk-cong (ctx-clo-to-comp-wk (var i) γ)) (proj₁ (proj₂ (M.clo-to-comp (M.eval (var i) (tmenv-to-menv γ)))))
    a₂ = subst (λ x → TM.lam-to-comp x ≡ wk-comp (wk-cong (ctx-clo-to-comp-wk (var i) γ)) (proj₁ (proj₂ (M.clo-to-comp (M.eval (var i) (tmenv-to-menv γ)))))) a₀ a₁

    goal : wk-comp (Wk.wk-cong (Wk.wk-wk wk-id)) M ≡ wk-comp (Wk.wk-cong (Wk.wk-wk (ctx-clo-to-comp-wk (var i) γ))) (proj₁ (proj₂ (M.clo-to-comp (M.lookup i (tmenv-to-menv γ)))))
    goal = cong (wk-comp (Wk.wk-cong (Wk.wk-wk wk-id))) a₂
  in
  goal
clo-to-comp-eq (lam M) ⋄ = refl
clo-to-comp-eq (lam M) (γ · _) = refl
clo-to-comp-eq (lam M) (γ ·﹝ _ ╎ _ ╎ _ ﹞) = refl

clo-wk-menv : (W : Γ ⊢ᵛ (X `⇒ Y)) → (γ : TM.MEnv Γ) → MProps.WkMEnv (ctx-clo-to-comp-wk W γ) (tmenv-to-menv γ) (proj₂ (proj₂ (M.clo-to-comp (M.eval W (tmenv-to-menv γ)))))
clo-wk-menv (var here) (γ · lam M) = wk-menv-wk (mclo-to-mval (lam M) γ) MProps.wk-menv-id
clo-wk-menv (var (there i)) (γ · 𝐖) = wk-menv-wk (mclo-to-mval 𝐖 γ) (clo-wk-menv (var i) γ)
clo-wk-menv (var (there i)) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-menv-wk (M.jumpᵛ x (tmenv-to-menv γ) (tmcstack-to-mcstack x₂)) (clo-wk-menv (var i) γ)
clo-wk-menv (lam M) ⋄ = wk-menv-ε
clo-wk-menv (lam M) (γ · _) = MProps.wk-menv-id
clo-wk-menv (lam M) (γ ·﹝ _ ╎ _ ╎ _ ﹞) = MProps.wk-menv-id

eval-clos : (V : Γ ⊢ᵛ (X `⇒ Y)) → (W : Γ ⊢ᵛ X) → (γ : TM.MEnv Γ) → (K : M.CStack Y) → MProps.WkCState ⟨ TM.lam-to-comp (TM.eval V γ) ╎ tmenv-to-menv γ · mclo-to-mval (TM.eval W γ) γ ╎ K ⟩ (M.eval-clo V W (tmenv-to-menv γ) K)
eval-clos V W γ K =
  let
    a = clo-to-comp-eq V γ

    b : MProps.WkMEnv (wk-cong (ctx-clo-to-comp-wk V γ)) (tmenv-to-menv γ · mclo-to-mval (TM.eval W γ) γ) (proj₂ (proj₂ (M.clo-to-comp (M.eval V (tmenv-to-menv γ)))) · M.eval W (tmenv-to-menv γ))
    b = wk-menv-cong (eval-wk W γ) (clo-wk-menv V γ)
  in
  wk-cstate-comp (wk-cong (ctx-clo-to-comp-wk V γ)) a b wk-cstack-id

--------------------------------------------------------------------------
-- translation of steps
--------------------------------------------------------------------------

tmstep-to-mstep : {σ σ₁ : TM.CState} → (WellFormedCState σ) → (σ →ᵀᴹ σ₁) → Σ[ σᴹ ∈ M.CState ] (((tmcstate-to-mcstate σ) →ᴹ σᴹ) × σᴹ ≈ᴹ (tmcstate-to-mcstate σ₁))
tmstep-to-mstep wf (eval→ {W = W} {γ = γ} {K = K}) =
  let
    eqv : ⟨ M.eval W (tmenv-to-menv γ) ╎ tmcstack-to-mcstack K ⟩ ≈ᴹ ⟨ mclo-to-mval (TM.eval W γ) γ ╎ tmcstack-to-mcstack K ⟩
    eqv = ≈ᴹ-bc (≈-wk₁ (wk-cstate-result (eval-wk W γ) wk-cstack-id))
  in
  ⟨ M.eval W (tmenv-to-menv γ) ╎ tmcstack-to-mcstack K ⟩ , eval→ , eqv
tmstep-to-mstep (wf-state-result {π₁ = π₁} {π₂ = π₂} _ w _ _ _) (return→ {𝐖 = 𝐖} {M = M} {γ = γ} {δ = δ} {K = K} {π = π}) =
  let
    eqv : ⟨ M₁ ╎ tmenv-to-menv δ · mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩ ≈ᴹ ⟨ wk-comp (wk-cong π) M₁ ╎ tmenv-to-menv γ M.· mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩
    eqv = ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp (Wk.wk-cong π₁) refl (wk-menv-cong wk-mval-id (wk-MEnvᵀ-to-wk-MEnvᴹ w)) wk-cstack-id))
  in
  ⟨ M ╎ tmenv-to-menv δ · mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩ , return→ , eqv
tmstep-to-mstep wf push→ = _ , push→ , ≈ᴹ-refl
tmstep-to-mstep wf sub→ = _ , sub→ , ≈ᴹ-refl
tmstep-to-mstep wf (var→ {W = W} {γ = γ} {K = K}) =
  let
    eqv : M.eval-jump W (tmenv-to-menv γ) ≈ᴹ tmcstate-to-mcstate (TM.eval-jump W γ)
    eqv = ≈ᴹ-bc (≈-wk₂ (eval-jump-wk W γ))
  in
  _ , var→ , eqv
tmstep-to-mstep wf (pmᶜ→ {W = W} {γ = γ} {M = M} {K = K}) =
  let
    wk₁ : MProps.WkMEnv (Wk.wk-cong (Wk.wk-cong wk-id)) (tmenv-to-menv γ · mclo-to-mval (TM.proj₁-omval (TM.eval W γ)) γ · mclo-to-mval (TM.wk-omval (Wk.wk-wk wk-id) (TM.proj₂-omval (TM.eval W γ))) (γ · TM.proj₁-omval (TM.eval W γ))) (tmenv-to-menv γ · M.proj₁-val (M.eval W (tmenv-to-menv γ)) · M.proj₂-val (M.eval W (tmenv-to-menv γ)))
    wk₁ = wk-menv-cong (eval₂-wk W γ) (wk-menv-cong (eval₁-wk W γ) MProps.wk-menv-id)

    eqv : ⟨ M ╎ tmenv-to-menv γ · M.eval₁ W (tmenv-to-menv γ) · M.eval₂ W (tmenv-to-menv γ) ╎ tmcstack-to-mcstack K ⟩ ≈ᴹ ⟨ M ╎ tmenv-to-menv γ M.· mclo-to-mval (TM.eval₁ W γ) γ M.· mclo-to-mval (TM.wk-omval (wk-wk wk-id) (TM.eval₂ W γ)) (γ TM.· TM.eval₁ W γ) ╎ tmcstack-to-mcstack K ⟩
    eqv = ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp wk-id refl wk₁ wk-cstack-id))
  in
  _ , pmᶜ→ , eqv
tmstep-to-mstep wf (app→ {V = V} {W = W} {γ = γ} {K = K}) =
  let
    wk₁ : MProps.WkCState ⟨ TM.lam-to-comp (TM.eval V γ) ╎ tmenv-to-menv γ · mclo-to-mval (TM.eval W γ) γ ╎ tmcstack-to-mcstack K ⟩ (M.eval-clo V W (tmenv-to-menv γ) (tmcstack-to-mcstack K))
    wk₁ = eval-clos V W γ (tmcstack-to-mcstack K)

    eqv : M.eval-clo V W (tmenv-to-menv γ) (tmcstack-to-mcstack K) ≈ᴹ ⟨ TM.lam-to-comp (TM.eval V γ) ╎ tmenv-to-menv γ M.· mclo-to-mval (TM.eval W γ) γ ╎ tmcstack-to-mcstack K ⟩
    eqv = ≈ᴹ-bc (≈-wk₁ wk₁)
  in
  _ , app→ , eqv



tmstep-to-mstep-eqv : {σ σ₁ : TM.CState} {σᴹ : M.CState} → (WellFormedCState σ) → (σ →ᵀᴹ σ₁) → ((tmcstate-to-mcstate σ) →ᴹ σᴹ) → σᴹ ≈ᴹ (tmcstate-to-mcstate σ₁)
tmstep-to-mstep-eqv {σ₁ = σ₁} {σᴹ = σᴹ} wf σ→ᵀᴹσ₁ mσ→ᴹσᴹ =
  let
    t = tmstep-to-mstep wf σ→ᵀᴹσ₁
    t₁ = proj₂ (proj₂ t)
    goal : σᴹ ≈ᴹ tmcstate-to-mcstate σ₁
    goal = subst (λ x → x ≈ᴹ tmcstate-to-mcstate σ₁) (M.determinismꟲ′ (proj₁ (proj₂ t)) mσ→ᴹσᴹ) t₁
  in
  goal

XXX -}
