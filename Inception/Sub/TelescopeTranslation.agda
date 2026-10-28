{-# OPTIONS --no-postfix-projections #-}

open import Inception.Sub.Syntax using (Ty)

module Inception.Sub.TelescopeTranslation (ℛ : Ty) where

open import Inception.Prelude
open import Inception.Rewriting
open import Inception.Sub.Syntax

open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)

open import Inception.Sub.Machine ℛ as M renaming (_→ᶜ_ to _→ᴹ_)
open import Inception.Sub.TelescopeMachine ℛ as TM renaming (_→ᶜ_ to _→ᵀᴹ_)
-- open M using (⟨_╎_⟩; ⟨_╎_╎_⟩; _·_; ◻; <_；_>∷_; ⋄; jumpᵛ; unitᵛ; pairᵛ; cloᵛ; eval→; return→; push→; sub→; var→; pmᶜ→; app→; progress) renaming (_→ᶜ_ to _→ᴹ_)
-- open TM using (⟨_；_╎_╎_⟩; ⟨_╎_╎_╎_⟩; <_；_；_>∷_; _·_; _·﹝_╎_╎_﹞; ⋄; ◻; unit; pair; lam; label; eval→; return→; push→; sub→; var→; pmᶜ→; app→) renaming (_→ᶜ_ to _→ᵀᴹ_)

open import Inception.Sub.MachineProps ℛ
open import Inception.Sub.TelescopeMachineProps ℛ

---------------------------------------------------------------------------------
-- Translation of Telescope Environments into List Environments
---------------------------------------------------------------------------------

mutual

  tmcstack-to-mcstack : TM.CStack Γ X → M.CStack X
  tmcstack-to-mcstack ◻ = ◻
  tmcstack-to-mcstack (< x ； γ ； π >∷ K) = < x ； tmenv-to-menv γ >∷ tmcstack-to-mcstack K

  tmenv-to-menv : TM.MEnv Γ → M.MEnv Γ
  tmenv-to-menv ⋄ = ⋄
  tmenv-to-menv (γ · 𝐖) = tmenv-to-menv γ · mclo-to-mval 𝐖 γ
  tmenv-to-menv (γ ·﹝ M ╎ π ╎ K ﹞) = tmenv-to-menv γ · jumpᵛ M (tmenv-to-menv γ) (tmcstack-to-mcstack K)

  mclo-to-mval : TM.MClo Γ X → TM.MEnv Γ → M.MVal X
  mclo-to-mval unit γ = unitᵛ
  mclo-to-mval (pair 𝐖₁ 𝐖₂) γ = pairᵛ (mclo-to-mval 𝐖₁ γ) (mclo-to-mval 𝐖₂ γ)
  mclo-to-mval (lam M) γ = cloᵛ M (tmenv-to-menv γ)
  mclo-to-mval (label here) (γ · label i) = mclo-to-mval (label i) γ
  mclo-to-mval (label here) (γ ·﹝ M ╎ π ╎ K ﹞) = jumpᵛ M (tmenv-to-menv γ) (tmcstack-to-mcstack K)
  mclo-to-mval (label (there i)) (γ · 𝐖) = mclo-to-mval (label i) γ
  mclo-to-mval (label (there i)) (γ ·﹝ M ╎ π ╎ K ﹞) = mclo-to-mval (label i) γ

tmcstate-to-mcstate : TM.CState → M.CState
tmcstate-to-mcstate ⟨ 𝐖 ； γ ╎ π ╎ K ⟩ = ⟨ mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩
tmcstate-to-mcstate ⟨ M ╎ γ ╎ π ╎ K ⟩ = ⟨ M ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩

--------------------------------------------------------------------------------
-- Lemmas for tmstep-to-mstep
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
---- Lemmas for eval→ case

wk-mclo-wk-comm : {𝐕 : TM.MClo Γ X} → (𝐖 : TM.MClo Γ Y) → (γ : TM.MEnv Γ) → WkMVal (mclo-to-mval (TM.wk-mclo (Wk.wk-wk wk-id) 𝐖) (γ · 𝐕)) (mclo-to-mval 𝐖 γ)
wk-mclo-wk-comm unit ⋄ = wk-unitᵛ
wk-mclo-wk-comm unit (γ · x) = wk-unitᵛ
wk-mclo-wk-comm unit (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-unitᵛ
wk-mclo-wk-comm (pair 𝐖 𝐖₁) ⋄ = wk-pairᵛ (wk-mclo-wk-comm 𝐖 ⋄) (wk-mclo-wk-comm 𝐖₁ ⋄)
wk-mclo-wk-comm (pair 𝐖 𝐖₁) (γ · x) = wk-pairᵛ (wk-mclo-wk-comm 𝐖 (γ · x)) (wk-mclo-wk-comm 𝐖₁ (γ · x))
wk-mclo-wk-comm (pair 𝐖 𝐖₁) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-pairᵛ (wk-mclo-wk-comm 𝐖 (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) (wk-mclo-wk-comm 𝐖₁ (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞))
wk-mclo-wk-comm {𝐕 = 𝐕} (lam M) ⋄ = wk-cloᵛ (wk-wk wk-ε) refl (wk-menv-wk (mclo-to-mval 𝐕 ⋄) wk-menv-ε)
wk-mclo-wk-comm (lam M) (γ · x) = wk-cloᵛ (wk-wk wk-id) refl (wk-menv-wk _ wk-menv-id)
wk-mclo-wk-comm (lam M) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-cloᵛ (wk-wk wk-id) refl (wk-menv-wk _ wk-menv-id)
wk-mclo-wk-comm (label x) (γ · x₁) = wk-mval-id
wk-mclo-wk-comm (label x) (γ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) = wk-mval-id

wk-mclo-wk-jump-comm : {M : Γ ⊢ᶜ X} {π : Γ ⊇ Δ} {K : TM.CStack Δ X} → (𝐖 : TM.MClo Γ Y) → (γ : TM.MEnv Γ) → WkMVal (mclo-to-mval (TM.wk-mclo (Wk.wk-wk wk-id) 𝐖) (γ ·﹝ M ╎ π ╎ K ﹞)) (mclo-to-mval 𝐖 γ)
wk-mclo-wk-jump-comm unit ⋄ = wk-unitᵛ
wk-mclo-wk-jump-comm unit (γ · x) = wk-unitᵛ
wk-mclo-wk-jump-comm unit (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-unitᵛ
wk-mclo-wk-jump-comm (pair 𝐖₁ 𝐖₂) ⋄ = wk-pairᵛ (wk-mclo-wk-jump-comm 𝐖₁ ⋄) (wk-mclo-wk-jump-comm 𝐖₂ ⋄)
wk-mclo-wk-jump-comm (pair 𝐖₁ 𝐖₂) (γ · x) = wk-pairᵛ (wk-mclo-wk-jump-comm 𝐖₁ (γ · x)) (wk-mclo-wk-jump-comm 𝐖₂ (γ · x))
wk-mclo-wk-jump-comm (pair 𝐖₁ 𝐖₂) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-pairᵛ (wk-mclo-wk-jump-comm 𝐖₁ (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) (wk-mclo-wk-jump-comm 𝐖₂ (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞))
wk-mclo-wk-jump-comm (lam M) ⋄ = wk-cloᵛ (wk-wk wk-ε) refl (wk-menv-wk (M.jumpᵛ _ (tmenv-to-menv ⋄) (tmcstack-to-mcstack _)) wk-menv-ε)
wk-mclo-wk-jump-comm (lam M) (γ · x) = wk-cloᵛ (wk-wk wk-id) refl (wk-menv-wk _ wk-menv-id)
wk-mclo-wk-jump-comm (lam M) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-cloᵛ (wk-wk wk-id) refl (wk-menv-wk _ wk-menv-id)
wk-mclo-wk-jump-comm (label x) (γ · x₁) = wk-mval-id
wk-mclo-wk-jump-comm (label x) (γ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) = wk-mval-id

lookup-wk : (i : Γ ∋ X) → (γ : TM.MEnv Γ) → WkMVal (mclo-to-mval (TM.lookup i γ) γ) (M.lookup i (tmenv-to-menv γ))
lookup-wk here (γ · x) = wk-mclo-wk-comm x γ
lookup-wk here (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-mclo-wk-comm {𝐕 = label here} (label here) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)
lookup-wk {X = X} (there i) (γ · x) = wk-mval-trans (wk-mclo-wk-comm (TM.lookup i γ) γ) (lookup-wk i γ)
lookup-wk (there i) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-mval-trans (wk-mclo-wk-jump-comm (TM.lookup i γ) γ) (lookup-wk i γ)

eval-wk : (W : Γ ⊢ᵛ X) → (γ : TM.MEnv Γ) → WkMVal (mclo-to-mval (TM.eval W γ) γ) (M.eval W (tmenv-to-menv γ))
eval-wk (var i) (γ · 𝐖) = lookup-wk i (γ · 𝐖)
eval-wk (var i) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = lookup-wk i (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)
eval-wk (lam x) ⋄ = wk-mval-id
eval-wk (lam x) (γ · x₁) = wk-mval-id
eval-wk (lam x) (γ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) = wk-mval-id
eval-wk (pair W₁ W₂) ⋄ = wk-pairᵛ (eval-wk W₁ ⋄) (eval-wk W₂ ⋄)
eval-wk (pair W₁ W₂) (γ · x) = wk-pairᵛ (eval-wk W₁ (γ · x)) (eval-wk W₂ (γ · x))
eval-wk (pair W₁ W₂) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-pairᵛ (eval-wk W₁ (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞)) (eval-wk W₂ (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞))
eval-wk unit ⋄ = wk-mval-id
eval-wk unit (γ · x) = wk-mval-id
eval-wk unit (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-mval-id

---------------------------------------------------------------------------------
---- Lemmas for return→ case

mutual

  wkmval : {Γ₁ Γ₂ : Ctx} → (𝐖 : TM.MClo Γ₂ X) → (π : Γ₁ ⊇ Γ₂) → (γ₁ : TM.MEnv Γ₁) → (γ₂ : TM.MEnv Γ₂) → WkMEnvᵀ π γ₁ γ₂ → WkMVal (mclo-to-mval (TM.wk-mclo π 𝐖) γ₁) (mclo-to-mval 𝐖 γ₂)
  wkmval TM.unit π γ₁ γ₂ g = wk-unitᵛ
  wkmval (TM.pair 𝐖 𝐖₁) π γ₁ γ₂ g = wk-pairᵛ (wkmval 𝐖 π γ₁ γ₂ g) (wkmval 𝐖₁ π γ₁ γ₂ g)
  wkmval (TM.lam M) π γ₁ γ₂ g = wk-cloᵛ π refl (wk-MEnvᵀ-to-wk-MEnvᴹ g)
  wkmval (label here) π γ₁ (γ₂ · (label x)) (wk-tmenv-mclo-cong 𝐖 g) = wkmval (label x) _ _ _ g
  wkmval (label here) π γ₁ γ₂ (wk-tmenv-jump-cong {π = π₁} M πᵀ K g) = wk-jumpᵛ π₁ refl (wk-MEnvᵀ-to-wk-MEnvᴹ g) wk-cstack-id
  wkmval (label here) π γ₁ γ₂ (wk-tmenv-mclo-wk 𝐖 g) = wkmval (label here) _ _ _ g
  wkmval (label here) π γ₁ γ₂ (wk-tmenv-jump-wk M πᵀ K g) = wkmval (label here) _ _ _ g
  wkmval (label (there x)) π γ₁ γ₂ (wk-tmenv-mclo-cong 𝐖 g) = wkmval (label x) _ _ _ g
  wkmval (label (there x)) π γ₁ γ₂ (wk-tmenv-jump-cong M πᵀ K g) = wkmval (label x) _ _ _ g
  wkmval (label (there x)) π γ₁ γ₂ (wk-tmenv-mclo-wk 𝐖 g) = wkmval (label (there x)) _ _ _ g
  wkmval (label (there x)) π γ₁ γ₂ (wk-tmenv-jump-wk M πᵀ K g) = wkmval (label (there x)) _ _ _ g

  wk-MEnvᵀ-to-wk-MEnvᴹ : {Γ₁ Γ₂ : Ctx} {π : Γ₁ ⊇ Γ₂} {γ₁ : TM.MEnv Γ₁} {γ₂ : TM.MEnv Γ₂} → WkMEnvᵀ π γ₁ γ₂ → WkMEnvᴹ π (tmenv-to-menv γ₁) (tmenv-to-menv γ₂)
  wk-MEnvᵀ-to-wk-MEnvᴹ wk-tmenv-ε = wk-menv-ε
  wk-MEnvᵀ-to-wk-MEnvᴹ (wk-tmenv-mclo-cong {π = π} {γ₁ = γ₁} {γ₂ = γ₂} 𝐖 g) =
    let
      a₀ : WkMVal (mclo-to-mval (TM.wk-mclo π 𝐖) γ₁) (mclo-to-mval 𝐖 γ₂)
      a₀ = wkmval 𝐖 π γ₁ γ₂ g
      a₁ = wk-menv-cong a₀ (wk-MEnvᵀ-to-wk-MEnvᴹ g)
    in
    a₁
  wk-MEnvᵀ-to-wk-MEnvᴹ (wk-tmenv-jump-cong M πᵀ K g) =
    let
      a₀ = wk-jumpᵛ _ refl (wk-MEnvᵀ-to-wk-MEnvᴹ g) wk-cstack-id
      a₁ = wk-menv-cong a₀ (wk-MEnvᵀ-to-wk-MEnvᴹ g)
    in
    a₁
  wk-MEnvᵀ-to-wk-MEnvᴹ (wk-tmenv-mclo-wk 𝐖 g) = wk-menv-wk (mclo-to-mval 𝐖 _) (wk-MEnvᵀ-to-wk-MEnvᴹ g)
  wk-MEnvᵀ-to-wk-MEnvᴹ (wk-tmenv-jump-wk M πᵀ K g) = wk-menv-wk (M.jumpᵛ M (tmenv-to-menv _) (tmcstack-to-mcstack K)) (wk-MEnvᵀ-to-wk-MEnvᴹ g)

--------------------------------------------------------------------------------
---- Lemmas for var→ case

lookup-eq : (x : Γ ∋ `ℓ) → (γ : TM.MEnv Γ) → (M.lookup x (tmenv-to-menv γ)) ≡ (mclo-to-mval (label x) γ)
lookup-eq here (γ · (label x)) = refl
lookup-eq here (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = refl
lookup-eq (there x) (γ · x₁) = lookup-eq x γ
lookup-eq (there x) (γ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) = lookup-eq x γ

lookup-label-wk : (i : Γ ∋ `ℓ) → (γ : TM.MEnv Γ) → WkCStateᴹ (M.jump-to-state (M.lookup i (tmenv-to-menv γ))) (tmcstate-to-mcstate (TM.lookup-label i γ))
lookup-label-wk here (γ · (label x)) =
  let
    a₀ : WkCStateᴹ (M.jump-to-state (M.lookup x (tmenv-to-menv γ))) (tmcstate-to-mcstate (TM.lookup-label x γ))
    a₀ = lookup-label-wk x γ
    goal : WkCStateᴹ (M.jump-to-state (mclo-to-mval (label x) γ)) (tmcstate-to-mcstate (TM.lookup-label x γ))
    goal = subst (λ z → WkCStateᴹ (M.jump-to-state z) (tmcstate-to-mcstate (TM.lookup-label x γ))) (lookup-eq x γ) a₀
  in
  goal
lookup-label-wk here (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-cstate-comp wk-id refl wk-menv-id wk-cstack-id
lookup-label-wk (there i) (γ · 𝐖) = lookup-label-wk i γ
lookup-label-wk (there i) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = lookup-label-wk i γ

eval-jump-wk : (W : Γ ⊢ᵛ `ℓ) → (γ : TM.MEnv Γ) → WkCStateᴹ (M.eval-jump W (tmenv-to-menv γ)) (tmcstate-to-mcstate (TM.eval-jump W γ))
eval-jump-wk (var i) γ = lookup-label-wk i γ

--------------------------------------------------------------------------------
---- Lemmas for pmᶜ→ case

proj₁-wk-mval-eq : (𝐖 : TM.MClo Γ (X₁ `× X₂)) → (γ : TM.MEnv Γ) → (M.proj₁-val (mclo-to-mval 𝐖 γ)) ≡ (mclo-to-mval (TM.proj₁-mclo 𝐖) γ)
proj₁-wk-mval-eq (pair 𝐖₁ 𝐖₂) ⋄ = refl
proj₁-wk-mval-eq (pair 𝐖₁ 𝐖₂) (γ · x) = refl
proj₁-wk-mval-eq (pair 𝐖₁ 𝐖₂) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = refl

proj₂-wk-mval-eq : (𝐖 : TM.MClo Γ (X₁ `× X₂)) → (γ : TM.MEnv Γ) → (M.proj₂-val (mclo-to-mval 𝐖 γ)) ≡ (mclo-to-mval (TM.proj₂-mclo 𝐖) γ)
proj₂-wk-mval-eq (pair 𝐖₁ 𝐖₂) ⋄ = refl
proj₂-wk-mval-eq (pair 𝐖₁ 𝐖₂) (γ · x) = refl
proj₂-wk-mval-eq (pair 𝐖₁ 𝐖₂) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = refl

eval₁-wk : (W : Γ ⊢ᵛ (X₁ `× X₂)) → (γ : TM.MEnv Γ) → WkMVal (mclo-to-mval (TM.proj₁-mclo (TM.eval W γ)) γ) (M.proj₁-val (M.eval W (tmenv-to-menv γ)))
eval₁-wk W γ =
  let
    goal′ : WkMVal (M.proj₁-val (mclo-to-mval (TM.eval W γ) γ)) (M.proj₁-val (M.eval W (tmenv-to-menv γ)))
    goal′ = proj₁-wk-mval (eval-wk W γ)

    goal : WkMVal (mclo-to-mval (TM.proj₁-mclo (TM.eval W γ)) γ) (M.proj₁-val (M.eval W (tmenv-to-menv γ)))
    goal = subst (λ x → WkMVal x (M.proj₁-val (M.eval W (tmenv-to-menv γ)))) (proj₁-wk-mval-eq (TM.eval W γ) γ) goal′
  in
  goal

eval₂-wk : (W : Γ ⊢ᵛ (X₁ `× X₂)) → (γ : TM.MEnv Γ) → WkMVal (mclo-to-mval (TM.wk-mclo (Wk.wk-wk wk-id) (TM.proj₂-mclo (TM.eval W γ))) (γ · TM.proj₁-mclo (TM.eval W γ))) (M.proj₂-val (M.eval W (tmenv-to-menv γ)))
eval₂-wk W γ =
  let
    goal′ : WkMVal (M.proj₂-val (mclo-to-mval (TM.eval W γ) γ)) (M.proj₂-val (M.eval W (tmenv-to-menv γ)))
    goal′ = proj₂-wk-mval (eval-wk W γ)

    goal′′ : WkMVal (mclo-to-mval (TM.proj₂-mclo (TM.eval W γ)) γ) (M.proj₂-val (M.eval W (tmenv-to-menv γ)))
    goal′′ = subst (λ x → WkMVal x (M.proj₂-val (M.eval W (tmenv-to-menv γ)))) (proj₂-wk-mval-eq (TM.eval W γ) γ) goal′

    goal : WkMVal (mclo-to-mval (TM.wk-mclo (Wk.wk-wk wk-id) (TM.proj₂-mclo (TM.eval W γ))) (γ · TM.proj₁-mclo (TM.eval W γ))) (M.proj₂-val (M.eval W (tmenv-to-menv γ)))
    goal = wk-mval-trans (wk-mclo-wk-comm (TM.proj₂-mclo (TM.eval W γ)) γ) goal′′
  in
  goal

--------------------------------------------------------------------------------
---- Lemmas for app→ case

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
clo-to-comp-eq (lam M) (γ · x₁) = refl
clo-to-comp-eq (lam M) (γ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) = refl

clo-wk-menv : (W : Γ ⊢ᵛ (X `⇒ Y)) → (γ : TM.MEnv Γ) → WkMEnvᴹ (ctx-clo-to-comp-wk W γ) (tmenv-to-menv γ) (proj₂ (proj₂ (M.clo-to-comp (M.eval W (tmenv-to-menv γ)))))
clo-wk-menv (var here) (γ · lam M) = wk-menv-wk (mclo-to-mval (lam M) γ) wk-menv-id
clo-wk-menv (var (there i)) (γ · 𝐖) = wk-menv-wk (mclo-to-mval 𝐖 γ) (clo-wk-menv (var i) γ)
clo-wk-menv (var (there i)) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-menv-wk (M.jumpᵛ x (tmenv-to-menv γ) (tmcstack-to-mcstack x₂)) (clo-wk-menv (var i) γ)
clo-wk-menv (lam M) ⋄ = wk-menv-ε
clo-wk-menv (lam M) (γ · x₁) = wk-menv-id
clo-wk-menv (lam M) (γ ·﹝ x₁ ╎ x₂ ╎ x₃ ﹞) = wk-menv-id

eval-clos : (W₁ : Γ ⊢ᵛ (X `⇒ Y)) → (W₂ : Γ ⊢ᵛ X) → (γ : TM.MEnv Γ) → (K : M.CStack Y) → WkCStateᴹ ⟨ TM.lam-to-comp (TM.eval W₁ γ) ╎ tmenv-to-menv γ · mclo-to-mval (TM.eval W₂ γ) γ ╎ K ⟩ (M.eval-clo W₁ W₂ (tmenv-to-menv γ) K)
eval-clos W₁ W₂ γ K =
  let
    a₀ = clo-to-comp-eq W₁ γ

    b₃ : WkMEnvᴹ (wk-cong (ctx-clo-to-comp-wk W₁ γ)) (tmenv-to-menv γ · mclo-to-mval (TM.eval W₂ γ) γ) (proj₂ (proj₂ (M.clo-to-comp (M.eval W₁ (tmenv-to-menv γ)))) · M.eval W₂ (tmenv-to-menv γ))
    b₃ = wk-menv-cong (eval-wk W₂ γ) (clo-wk-menv W₁ γ)
  in
  wk-cstate-comp (wk-cong (ctx-clo-to-comp-wk W₁ γ)) a₀ b₃ wk-cstack-id

---------------------------------------------------------------------------------
-- Translation of Steps
---------------------------------------------------------------------------------

tmstep-to-mstep : {σ σ₁ : TM.CState} → (WellFormedTMCState σ) → (σ →ᵀᴹ σ₁) → Σ[ σᴹ ∈ M.CState ] (((tmcstate-to-mcstate σ) →ᴹ σᴹ) × σᴹ ≈ᴹ (tmcstate-to-mcstate σ₁))
tmstep-to-mstep wf (eval→ {W = W} {γ = γ} {K = K}) =
  let
    eqv : ⟨ M.eval W (tmenv-to-menv γ) ╎ tmcstack-to-mcstack K ⟩ ≈ᴹ ⟨ mclo-to-mval (TM.eval W γ) γ ╎ tmcstack-to-mcstack K ⟩
    eqv = ≈ᴹ-bc (≈-wk₁ (wk-cstate-result (eval-wk W γ) wk-cstack-id))
  in
  ⟨ M.eval W (tmenv-to-menv γ) ╎ tmcstack-to-mcstack K ⟩ , eval→ , eqv
tmstep-to-mstep (wf-state-result {π₁ = π₁} {π₂ = π₂} _ w _ _ _) (return→ {𝐖 = 𝐖} {M₁ = M₁} {γ = γ} {γ₁ = γ₁} {K = K} {π = π}) =
  let
    eqv : ⟨ M₁ ╎ tmenv-to-menv γ₁ · mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩ ≈ᴹ ⟨ wk-comp (wk-cong π) M₁ ╎ tmenv-to-menv γ M.· mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩
    eqv = ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp (Wk.wk-cong π₁) refl (wk-menv-cong wk-mval-id (wk-MEnvᵀ-to-wk-MEnvᴹ w)) wk-cstack-id))
  in
  ⟨ M₁ ╎ tmenv-to-menv γ₁ · mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩ , return→ , eqv
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
    wk₁ : WkMEnvᴹ (Wk.wk-cong (Wk.wk-cong wk-id)) (tmenv-to-menv γ · mclo-to-mval (TM.proj₁-mclo (TM.eval W γ)) γ · mclo-to-mval (TM.wk-mclo (Wk.wk-wk wk-id) (TM.proj₂-mclo (TM.eval W γ))) (γ · TM.proj₁-mclo (TM.eval W γ))) (tmenv-to-menv γ · M.proj₁-val (M.eval W (tmenv-to-menv γ)) · M.proj₂-val (M.eval W (tmenv-to-menv γ)))
    wk₁ = wk-menv-cong (eval₂-wk W γ) (wk-menv-cong (eval₁-wk W γ) wk-menv-id)

    eqv : ⟨ M ╎ tmenv-to-menv γ · M.eval₁ W (tmenv-to-menv γ) · M.eval₂ W (tmenv-to-menv γ) ╎ tmcstack-to-mcstack K ⟩ ≈ᴹ ⟨ M ╎ tmenv-to-menv γ M.· mclo-to-mval (TM.eval₁ W γ) γ M.· mclo-to-mval (TM.wk-mclo (wk-wk wk-id) (TM.eval₂ W γ)) (γ TM.· TM.eval₁ W γ) ╎ tmcstack-to-mcstack K ⟩
    eqv = ≈ᴹ-bc (≈-wk₁ (wk-cstate-comp wk-id refl wk₁ wk-cstack-id))
  in
  _ , pmᶜ→ , eqv
tmstep-to-mstep wf (app→ {W₁ = W₁} {W₂ = W₂} {γ = γ} {K = K}) =
  let
    wk₁ : WkCStateᴹ ⟨ TM.lam-to-comp (TM.eval W₁ γ) ╎ tmenv-to-menv γ · mclo-to-mval (TM.eval W₂ γ) γ ╎ tmcstack-to-mcstack K ⟩ (M.eval-clo W₁ W₂ (tmenv-to-menv γ) (tmcstack-to-mcstack K))
    wk₁ = eval-clos W₁ W₂ γ (tmcstack-to-mcstack K)

    eqv : M.eval-clo W₁ W₂ (tmenv-to-menv γ) (tmcstack-to-mcstack K) ≈ᴹ ⟨ TM.lam-to-comp (TM.eval W₁ γ) ╎ tmenv-to-menv γ M.· mclo-to-mval (TM.eval W₂ γ) γ ╎ tmcstack-to-mcstack K ⟩
    eqv = ≈ᴹ-bc (≈-wk₁ wk₁)
  in
  _ , app→ , eqv



tmstep-to-mstep-eqv : {σ σ₁ : TM.CState} {σᴹ : M.CState} → (WellFormedTMCState σ) → (σ →ᵀᴹ σ₁) → ((tmcstate-to-mcstate σ) →ᴹ σᴹ) → σᴹ ≈ᴹ (tmcstate-to-mcstate σ₁)
tmstep-to-mstep-eqv {σ₁ = σ₁} {σᴹ = σᴹ} wf σ→ᵀᴹσ₁ mσ→ᴹσᴹ =
  let
    t = tmstep-to-mstep wf σ→ᵀᴹσ₁
    t₁ = proj₂ (proj₂ t)
    goal : σᴹ ≈ᴹ tmcstate-to-mcstate σ₁
    goal = subst (λ x → x ≈ᴹ tmcstate-to-mcstate σ₁) (M.determinismꟲ′ (proj₁ (proj₂ t)) mσ→ᴹσᴹ) t₁
  in
  goal
