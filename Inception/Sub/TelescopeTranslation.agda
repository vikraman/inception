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

open import Inception.Sub.MachineProps ℛ as MProps
open import Inception.Sub.TelescopeMachineProps ℛ as TMProps

--------------------------------------------------------------------------
-- translation of telescope environments into list environments
--------------------------------------------------------------------------

mutual

  tmcstack-to-mcstack : TM.CStack Γ X → M.CStack X
  tmcstack-to-mcstack ◻ = ◻
  tmcstack-to-mcstack (< x ； γ ； π >∷ K) = < x ； tmenv-to-menv γ >∷ tmcstack-to-mcstack K

  tmenv-to-menv : TM.MEnv Γ → M.MEnv Γ
  tmenv-to-menv ⋄ = ⋄
  tmenv-to-menv (γ · 𝐖) = tmenv-to-menv γ · mclo-to-mval 𝐖 γ
  tmenv-to-menv (γ ·﹝ M ╎ π ╎ K ﹞) = tmenv-to-menv γ · jumpᵛ M (tmenv-to-menv γ) (tmcstack-to-mcstack K)

  mclo-to-mval : TM.OMVal Γ X → TM.MEnv Γ → M.MVal X
  mclo-to-mval unit γ = unitᵛ
  mclo-to-mval (pair 𝐕 𝐖) γ = pairᵛ (mclo-to-mval 𝐕 γ) (mclo-to-mval 𝐖 γ)
  mclo-to-mval (lam M) γ = cloᵛ M (tmenv-to-menv γ)
  mclo-to-mval (label here) (γ · label i) = mclo-to-mval (label i) γ
  mclo-to-mval (label here) (γ ·﹝ M ╎ π ╎ K ﹞) = jumpᵛ M (tmenv-to-menv γ) (tmcstack-to-mcstack K)
  mclo-to-mval (label (there i)) (γ · 𝐖) = mclo-to-mval (label i) γ
  mclo-to-mval (label (there i)) (γ ·﹝ M ╎ π ╎ K ﹞) = mclo-to-mval (label i) γ

tmcstate-to-mcstate : TM.CState → M.CState
tmcstate-to-mcstate ⟨ 𝐖 ； γ ╎ π ╎ K ⟩ = ⟨ mclo-to-mval 𝐖 γ ╎ tmcstack-to-mcstack K ⟩
tmcstate-to-mcstate ⟨ M ╎ γ ╎ π ╎ K ⟩ = ⟨ M ╎ tmenv-to-menv γ ╎ tmcstack-to-mcstack K ⟩

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

lookup-label-wk : (i : Γ ∋ `ℓ) → (γ : TM.MEnv Γ) → WkCState (M.jump-to-state (M.lookup i (tmenv-to-menv γ))) (tmcstate-to-mcstate (TM.lookup-label i γ))
lookup-label-wk here (γ · (label x)) =
  let
    a : WkCState (M.jump-to-state (M.lookup x (tmenv-to-menv γ))) (tmcstate-to-mcstate (TM.lookup-label x γ))
    a = lookup-label-wk x γ
    goal : WkCState (M.jump-to-state (mclo-to-mval (label x) γ)) (tmcstate-to-mcstate (TM.lookup-label x γ))
    goal = subst (λ z → WkCState (M.jump-to-state z) (tmcstate-to-mcstate (TM.lookup-label x γ))) (lookup-eq x γ) a
  in
  goal
lookup-label-wk here (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = wk-cstate-comp wk-id refl MProps.wk-menv-id wk-cstack-id
lookup-label-wk (there i) (γ · 𝐖) = lookup-label-wk i γ
lookup-label-wk (there i) (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) = lookup-label-wk i γ

eval-jump-wk : (W : Γ ⊢ᵛ `ℓ) → (γ : TM.MEnv Γ) → WkCState (M.eval-jump W (tmenv-to-menv γ)) (tmcstate-to-mcstate (TM.eval-jump W γ))
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

eval-clos : (V : Γ ⊢ᵛ (X `⇒ Y)) → (W : Γ ⊢ᵛ X) → (γ : TM.MEnv Γ) → (K : M.CStack Y) → WkCState ⟨ TM.lam-to-comp (TM.eval V γ) ╎ tmenv-to-menv γ · mclo-to-mval (TM.eval W γ) γ ╎ K ⟩ (M.eval-clo V W (tmenv-to-menv γ) K)
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
    wk₁ : WkCState ⟨ TM.lam-to-comp (TM.eval V γ) ╎ tmenv-to-menv γ · mclo-to-mval (TM.eval W γ) γ ╎ tmcstack-to-mcstack K ⟩ (M.eval-clo V W (tmenv-to-menv γ) (tmcstack-to-mcstack K))
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
