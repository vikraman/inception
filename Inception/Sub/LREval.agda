{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.LREval (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_; _$_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)
open Eq.≡-Reasoning using (step-≡-⟩; step-≡-∣; step-≡-⟨; _∎; step-≡)

open import Relation.Binary.PropositionalEquality.Properties using (dcong₂)
open import Agda.Primitive using (Level)

open import Relation.Binary.Reasoning.Syntax

open import Relation.Binary.Definitions
  using (Symmetric; Transitive; Substitutive; Irreflexive
        ; _Respects_; _Respectsˡ_; _Respectsʳ_; _Respects₂_)

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Unit
open import Data.Nat
open import Data.List using (List; _∷_; []; _++_)

open import Inception.Sub.Equality
open import Inception.Sub.Environments R
open import Inception.Sub.States R
open import Inception.Sub.Machine R

module EvalMain {R₀ : Ty} (k₀ : ⟦ R₀ ⟧ → R) where

  open StatesMain {R₀ = R₀} k₀
  open MachineMain {R₀ = R₀} k₀
  open EnvMain {R₀ = R₀} k₀

  -------------------------------------------------------------------

  {- without halting condition
  data LookupSteps : LookupState X → Set where

    steps : {S T : LookupState X} → (S→T : S →ᴸ* T) → (H : LookupHaltingState T) → ⟦ S ⟧ᴸ ≡ ⟦ T ⟧ᴸ → (π : Wk (lCtx S) (lTCtx T)) → (⟦ π ⟧ʷ ⟦ lEnv S ⟧ᴱ ≡ ⟦ lTEnv T ⟧ᴱ)
            --→ TermHalts H
            → EnvExt (lookup-index S→T) (lEnv S) (lEnv T)
            → WkExt π
            → EnvEq π (lEnv S) (lTEnv T)
            → LookupSteps S

  lookup : (i : Γ ∋ X) → (γ : Env Γ) → LookupSteps {X = X} ⟨ i ∥ γ ⟩
  lookup Cx.h (γ ﹐ l̲a̲m̲ W) = steps (⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩ ◼) (found-lam {W = W} {γ = γ}) refl (wk-wk wk-id) refl env-val (wk-ext wk-id (wk-eq wk-id)) (wk-env-val-wk (l̲a̲m̲ W) enveq-id)
  lookup Cx.h (γ ﹐ pa̲i̲r̲ LHS RHS) = steps (⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩ ◼) found-pair refl (wk-wk wk-id) refl env-val (wk-ext wk-id (wk-eq wk-id)) (wk-env-val-wk (pa̲i̲r̲ LHS RHS) enveq-id)
  lookup h (γ ﹐ u̲n̲i̲t̲) = steps (⟨ h ∥ _﹐_ γ (u̲n̲i̲t̲) ⟩ ◼) found-unit refl (wk-wk wk-id) refl env-val (wk-ext wk-id (wk-eq wk-id)) (wk-env-val-wk u̲n̲i̲t̲ enveq-id)
  lookup Cx.h (γ ﹐ v̲a̲r̲ i) with lookup i γ
  ... | steps {T = T} i>>T HT i≡T WK w≡γ ext we ϖ =
              let
                a0 = li≡i i>>T HT
                a1 = subst (λ x → EnvExt x γ (lEnv T)) (a0) ext
              in
              steps (_ →ᴸ⟨ val-h-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ (ext-jmp a1) (wk-ext WK we) (wk-env-val-wk (v̲a̲r̲ i) ϖ)
  lookup Cx.h ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) =
    steps (⟨ h ∥ γ ﹐﹝ W ╎ cs ﹞ ⟩ ◼) found-comp refl (wk-wk wk-id) refl env-comp (wk-ext wk-id (wk-eq wk-id)) (wk-env-comp-wk W cs enveq-id)
  lookup (Cx.t i) (γ ﹐ M) with lookup i γ
  ... | steps {T = T} i>>T HT i≡T WK w≡γ ext we ϖ = steps (_ →ᴸ⟨ val-t-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ (ext-val ext) (wk-ext WK we) (wk-env-val-wk M ϖ)
  lookup (Cx.t i) (γ ﹐﹝ W ╎ cs ﹞) with lookup i γ
  ... | steps {T = T} i>>T HT i≡T WK w≡γ ext we ϖ =
      steps (_ →ᴸ⟨ (comp-t-step) ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ (ext-comp ext) (wk-ext WK we) (wk-env-comp-wk W cs ϖ)

  get-lsteps : {S : LookupState X} → LookupSteps S → Σ[ T ∈ LookupState X ] ((S →ᴸ* T) × (LookupHaltingState T))
  get-lsteps {S = S} (steps {T = T} S→T H x π x₁ x₂ x₃ x₄) = T , S→T , H

  lh-eq : {T : LookupState X} → (H : LookupHaltingState T) → Σ[ Γ ∈ Ctx ] Σ[ γ ∈ Env (Γ ∙ X) ] (T ≡ ⟨ h  ∥ γ ⟩)
  lh-eq {T = ⟨ h ∥ _ ⟩} found-unit = _ , _ Env.﹐ u̲n̲i̲t̲ , refl
  lh-eq {T = ⟨ h ∥ _ ⟩} found-pair = _ , _ Env.﹐ pa̲i̲r̲ _ _ , refl
  lh-eq {T = ⟨ h ∥ _ ⟩} found-lam = _ , _ Env.﹐ l̲a̲m̲ _ , refl
  lh-eq {T = ⟨ h ∥ _ ⟩} found-comp = _ , _ Env.﹐﹝ _ ╎ _ ﹞ , refl
  -}

  data CompHalts : (W : Γ ⊢ᶜ Z) (γ : Env Γ) (cs : CompStack Δ Z) (π : Wk Γ Δ) (wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → Set

  data CompHalts where

    comp-halts : {W : Γ ⊢ᶜ Z} {γ : Env Γ} {cs : CompStack Δ Z} {π : Wk Γ Δ} {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
            → (T : CompState) → (H : CompHaltingState T)
            → (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡})) →ᶜ* T
            → ⟦ (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡})) ⟧ᶜꟴ ≡ ⟦ T ⟧ᶜꟴ
            → CompHalts W γ cs π wk≡


  --get-chsteps : {S : CompState} → CompSteps S → Σ[ T ∈ CompState ] ((CompHaltingState T) × (S →ᶜ* T) × (⟦ S ⟧ᶜꟴ ≡ ⟦ T ⟧ᶜꟴ))
  --get-chsteps {S = S} (steps {T = T} S→T H eq) = T , H , S→T , eq

  get-chsteps : {W : Γ ⊢ᶜ Z} {γ : Env Γ} {cs : CompStack Δ Z} {π : Wk Γ Δ} {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → CompHalts W γ cs π wk≡ → Σ[ T ∈ CompState ] ((((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡})) →ᶜ* T)
  get-chsteps (comp-halts T H S→T eq) = T , S→T

  data EnvWk : (π : Wk Γ Γ') → Env Γ → Env Γ' → Set where

      ⟨_⟩     :  {π : Wk Γ Γ} → (γ : Env Γ) → EnvWk π γ γ

      _﹐_     :  {π : Wk Γ Γ'} → {γ : Env Γ} → {γ' : Env Γ'} → EnvWk π γ γ' → (M : V̲a̲l̲ Γ X) → EnvWk (wk-wk {A = X} π) (γ ﹐ M) γ'

  -----------------------------------------------------

  ValHalts : (M : V̲a̲l̲ Γ Z) → (γ : Env Γ) → Set

  ValHalts {Γ = Γ} (l̲a̲m̲ {X = X} {Y = Y} W) γ = (Δ : Ctx) → (cs : CompStack Δ Y) → (π : Wk Γ Δ) → (wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → (N : V̲a̲l̲ Γ X) → (n↓ : ValHalts N γ) → (CompHalts W (γ ﹐ N) cs (wk-wk π) wk≡)
  ValHalts {Γ = Γ} (pa̲i̲r̲ M₁ M₂) γ = ValHalts M₁ γ × ValHalts M₂ γ
  ValHalts u̲n̲i̲t̲ _ = ⊤
  ValHalts (v̲a̲r̲ Cx.h) (γ ﹐ v̲a̲r̲ i) = ValHalts (v̲a̲r̲ i) γ
  ValHalts (v̲a̲r̲ (Cx.t i)) (γ ﹐ M) = ValHalts (v̲a̲r̲ i) γ
  ValHalts (v̲a̲r̲ Cx.h) ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) = CompHalts W γ cs π wk≡
  ValHalts (v̲a̲r̲ (Cx.t i)) (γ ﹐﹝ W ╎ cs ﹞) = ValHalts (v̲a̲r̲ i) γ

  data EnvHalts : Env Γ → Set where

    empty-env : EnvHalts ∗

    val-in-env  : (M : V̲a̲l̲ Γ X) → (γ : Env Γ) → (vH : ValHalts M γ) → (γH : EnvHalts γ) → EnvHalts (γ ﹐ M)

    comp-in-env : (W : Γ ⊢ᶜ X) → (γ : Env Γ) → (cs : CompStack Δ X) → {π : Wk Γ Δ} → {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → CompHalts W γ cs π wk≡
                  → EnvHalts γ
                  → EnvHalts ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡})

  {-
  data CSHalts : {Δ : Ctx} {Z : Ty} → CompStack Δ Z → Set where

    cs-empty : CSHalts ◻

    cs-head-halts : {W : (Γ ∙ X) ⊢ᶜ Z} {γ : Env Γ} {cs : CompStack Δ Z} {π : Wk Γ Δ} {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
      → ((Γ' : Ctx) → (π' : Wk Γ' Γ) → (π'' : Wk (Γ' ∙ X) Δ) → (γ' : Env Γ') → (EnvHalts γ') → (M : V̲a̲l̲ Γ' X) → (ValHalts M γ') → (wk≡' : ⟦ π'' ⟧ʷ ⟦ γ' ﹐ M ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → CompHalts (wk-comp (wk-cong π') W) (γ' ﹐ M) cs π'' wk≡') → CSHalts cs
      → CSHalts ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡})
  -}



  -- data VSHalts : {T : ValState X} → (H : ValHaltingState T) → Set where
  --   vs-halts : {M : V̲a̲l̲ Γ Z} {γ : Env Γ} → ValHalts M γ → VSHalts ∙ M ⊲ γ ■

  --------------------------------------------------------------

  PValHalts : (M : V̲a̲l̲ Γ' Z) → Set
  PValHalts {Γ' = Γ'} (l̲a̲m̲ {X = X} {Y = Y} W) =
    (Γ : Ctx) → (γ : Env Γ) → (↓ᴱ : EnvHalts γ) → (π' : Wk Γ Γ') → (Δ : Ctx) → (cs : CompStack Δ Y) → (π : Wk Γ Δ) → (wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → (N : V̲a̲l̲ Γ X) → (n↓ : ValHalts N γ) → (CompHalts (wk-comp (wk-cong π') W) (γ ﹐ N) cs (wk-wk π) wk≡)
  PValHalts {Γ' = Γ'} (pa̲i̲r̲ M₁ M₂) = PValHalts M₁ × PValHalts M₂
  PValHalts {Γ' = Γ'} u̲n̲i̲t̲ = {Γ : Ctx} → (γ : Env Γ) → (↓ᴱ : EnvHalts γ) → (π' : Wk Γ Γ') → ⊤
  PValHalts {Γ' = Γ'} (v̲a̲r̲ i) = {Γ : Ctx} → (γ : Env Γ) → (↓ᴱ : EnvHalts γ) → (π' : Wk Γ Γ') → ValHalts (wk-v̲a̲l̲ π' (v̲a̲r̲ i)) γ

  {-
  data CSHalts : {Δ : Ctx} {Z : Ty} → CompStack Δ Z → Set where

    cs-empty : CSHalts ◻

    cs-head-halts : {W : (Γ ∙ X) ⊢ᶜ Z} {γ : Env Γ} {cs : CompStack Δ Z} {π : Wk Γ Δ} {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
      → ((M : V̲a̲l̲ Γ X) → (PValHalts M) → CompHalts W (γ ﹐ M) cs (wk-wk π) wk≡) → CSHalts cs
      → CSHalts ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡})
  -}


  {-
  data CSHalts : {Γ Δ : Ctx} {Z : Ty} → CompStack Δ Z → Env Γ → Set where

    cs-empty : CSHalts ◻ ∗

    cs-head-halts : {W : (Γ ∙ X) ⊢ᶜ Z} {γ : Env Γ} {cs : CompStack Δ Z} {π : Wk Γ Δ} {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
      → (↓ᴱ : EnvHalts γ)
      → ((M : V̲a̲l̲ Γ X) → (PValHalts M) → (CompHalts W (γ ﹐ M) cs (wk-wk π) wk≡) × (CSHalts cs (γ ﹐ M)))
      → CSHalts ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡}) γ
  -}

  wk-pvalhalts : {Γ Γ' : Ctx} → (M : V̲a̲l̲ Γ' X) → (π : Wk Γ Γ') → PValHalts M → PValHalts (wk-v̲a̲l̲ π M)
  wk-pvalhalts {Γ = Γ} {Γ' = Γ'} (l̲a̲m̲ W) π pM =
    λ Γ₁ γ ↓ᴱ π' Δ cs π₁ wk≡ N n↓ →
    let
      --ch = pM Γ₁ γ ↓ᴱ (wk-trans π' π) Δ cs ↓ᶜˢ π₁ wk≡ N n↓
      ch = pM Γ₁ γ ↓ᴱ (wk-trans π' π) Δ cs π₁ wk≡ N n↓
    in
    subst (λ x → CompHalts x (γ ﹐ N) cs (wk-wk π₁) wk≡) (sym (wk-comp-trans W (wk-cong π') (wk-cong π))) ch
  wk-pvalhalts (pa̲i̲r̲ M₁ M₂) π pM = (wk-pvalhalts M₁ π (proj₁ pM)) , (wk-pvalhalts M₂ π (proj₂ pM))
  wk-pvalhalts u̲n̲i̲t̲ π pM = λ γ ↓ᴱ π' → tt
  wk-pvalhalts (v̲a̲r̲ i) π pM =
    λ γ ↓ᴱ π' →
    let
      vh = pM γ ↓ᴱ (wk-trans π' π)
    in
    subst (λ x → ValHalts (v̲a̲r̲ x) γ) (sym (wk-mem-trans i π' π)) vh

  data PEnvHalts : Env Γ → Set where

    empty-penv : PEnvHalts ∗

    val-in-env  : (M : V̲a̲l̲ Γ X) → (γ : Env Γ) → (vH : PValHalts M) → (γH : PEnvHalts γ) → PEnvHalts (γ ﹐ M)

    comp-in-env : (W : Γ ⊢ᶜ X) → (γ : Env Γ) → (cs : CompStack Δ X) → {π : Wk Γ Δ} → {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → CompHalts W γ cs π wk≡
                  → PEnvHalts γ
                  → PEnvHalts ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡})

  PVH-to-VH : {M : V̲a̲l̲ Γ X} {γ : Env Γ} → PValHalts M → EnvHalts γ → ValHalts M γ
  PVH-to-VH {M = l̲a̲m̲ W} {γ = γ} ↓ᵛ ↓ᴱ =
    λ Δ cs π wk≡ N n↓ →
    let
      vh = ↓ᵛ _ γ ↓ᴱ wk-id Δ cs π wk≡ N n↓
    in
    {!!}
  PVH-to-VH {M = pa̲i̲r̲ M₁ M₂} {γ = γ} ↓ᵛ ↓ᴱ = PVH-to-VH (proj₁ ↓ᵛ) ↓ᴱ , PVH-to-VH (proj₂ ↓ᵛ) ↓ᴱ
  PVH-to-VH {M = u̲n̲i̲t̲} {γ = γ} ↓ᵛ ↓ᴱ = tt
  PVH-to-VH {M = v̲a̲r̲ i} {γ = γ} ↓ᵛ ↓ᴱ = {!!}

  PEH-to-EH : {γ : Env Γ} → PEnvHalts γ → EnvHalts γ
  PEH-to-EH {γ = γ} empty-penv = empty-env
  PEH-to-EH {γ = γ} (val-in-env M γ₁ vH ↓ᴱ) = val-in-env M γ₁ (PVH-to-VH vH (PEH-to-EH ↓ᴱ)) (PEH-to-EH ↓ᴱ)
  PEH-to-EH {γ = γ} (comp-in-env W γ₁ cs x ↓ᴱ) = comp-in-env W γ₁ cs x (PEH-to-EH ↓ᴱ)

  {-
  data CSHalts : {Γ Δ : Ctx} {Z : Ty} → CompStack Δ Z → Env Γ → Set where

    cs-empty : CSHalts ◻ ∗

    cs-head-halts : {W : (Γ ∙ X) ⊢ᶜ Z} {γ : Env Γ} {cs : CompStack Δ Z} {π : Wk Γ Δ} {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
      → (Γ' : Ctx) → (π' : Wk Γ' Γ) → (π'' : Wk (Γ' ∙ X) Δ) → (γ' : Env Γ') → (EnvHalts γ')
      → ((M : V̲a̲l̲ Γ' X) → (ValHalts M γ') → (wk≡' : ⟦ π'' ⟧ʷ ⟦ γ' ﹐ M ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → (CompHalts (wk-comp (wk-cong π') W) (γ' ﹐ M) cs π'' wk≡') × (CSHalts cs (γ' ﹐ M)))
      → CSHalts ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡}) γ'
  -}

  {-
  data CSHalts : {Δ : Ctx} {Z : Ty} → CompStack Δ Z → Set where

    cs-empty : CSHalts ◻

    cs-head-halts : {W : (Γ ∙ X) ⊢ᶜ Z} {γ : Env Γ} {cs : CompStack Δ Z} {π : Wk Γ Δ} {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
      → ((M : V̲a̲l̲ Γ X) → (PValHalts M) → CompHalts W (γ ﹐ M) cs (wk-wk π) wk≡) → CSHalts cs
      → CSHalts ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡})
  -}

  data CSHalts : {Δ : Ctx} {Z : Ty} → CompStack Δ Z → Set where

    cs-empty : CSHalts ◻

    cs-head-halts : {W : (Γ ∙ X) ⊢ᶜ Z} {γ : Env Γ} {cs : CompStack Δ Z} {π : Wk Γ Δ} {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
      → ((Γ' : Ctx) → (π' : Wk Γ' Γ) → (π'' : Wk (Γ' ∙ X) Δ) → (γ' : Env Γ') → (PEnvHalts γ') → (M : V̲a̲l̲ Γ' X) → (PValHalts M) → (wk≡' : ⟦ π'' ⟧ʷ ⟦ γ' ﹐ M ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → CompHalts (wk-comp (wk-cong π') W) (γ' ﹐ M) cs π'' wk≡') → CSHalts cs
      → CSHalts ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡})

  data TermHalts : {T : LookupState X} → (H : LookupHaltingState T) → Set where

    unit-term-halts : {γ : Env Γ} → TermHalts (found-unit {γ = γ})

    --pair-term-halts : {γ : Env Γ} {LHS : V̲a̲l̲ Γ X} {RHS : V̲a̲l̲ Γ Y} → PValHalts (pa̲i̲r̲ LHS RHS) → TermHalts (found-pair {LHS = LHS} {RHS = RHS} {γ = γ})
    pair-term-halts : {γ : Env Γ} {LHS : V̲a̲l̲ Γ X} {RHS : V̲a̲l̲ Γ Y} → PValHalts LHS → PValHalts RHS → TermHalts (found-pair {LHS = LHS} {RHS = RHS} {γ = γ})

    lam-term-halts  : {γ : Env Γ} {W : (Γ ∙ X) ⊢ᶜ Y} → PValHalts (l̲a̲m̲ W) → TermHalts (found-lam {W = W} {γ = γ})

    comp-term-halts : {γ : Env Γ} → {W : Γ ⊢ᶜ X} → {cs : CompStack Δ X} → {π : Wk Γ Δ} → {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → CompHalts W γ cs π wk≡ → TermHalts (found-comp {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡})

  --------------------------------------------------------------

  data ValSteps : ValState T◾ → Set where

    steps : {S T : ValState T◾} → S ↠ᵛ T → (H : ValHaltingState T) → ⟦ S ⟧ᵛꟴ ≡ ⟦ T ⟧ᵛꟴ → (π : Wk (botCtx T) (botCtx S)) → (⟦ π ⟧ʷ ⟦ botEnv T ⟧ᴱ ≡ ⟦ botEnv S ⟧ᴱ)
            → PEnvHalts (botEnv T)
            --→ VSHalts H
            → PValHalts (haltingTerm H)
            → ValSteps S

  data LookupSteps : LookupState X → Set where

    steps : {S T : LookupState X} → (S→T : S →ᴸ* T) → (H : LookupHaltingState T) → ⟦ S ⟧ᴸ ≡ ⟦ T ⟧ᴸ → (π : Wk (lCtx S) (lTCtx T)) → (⟦ π ⟧ʷ ⟦ lEnv S ⟧ᴱ ≡ ⟦ lTEnv T ⟧ᴱ)
            → TermHalts H
            → EnvExt (lookup-index S→T) (lEnv S) (lEnv T)
            → WkExt π
            → EnvEq π (lEnv S) (lTEnv T)
            → LookupSteps S

  lookup : (i : Γ ∋ X) → (γ : Env Γ) → (PEnvHalts γ) → LookupSteps {X = X} ⟨ i ∥ γ ⟩
  lookup Cx.h (γ ﹐ l̲a̲m̲ W) (val-in-env M γ₁ vH eh) = steps (⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩ ◼) (found-lam {W = W} {γ = γ}) refl (wk-wk wk-id) refl (lam-term-halts vH) env-val (wk-ext wk-id (wk-eq wk-id)) (wk-env-val-wk (l̲a̲m̲ W) enveq-id)
  --lookup Cx.h (γ ﹐ pa̲i̲r̲ LHS RHS) (val-in-env M γ₁ (pval-halts _ f) eh) = steps (⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩ ◼) found-pair refl (wk-wk wk-id) refl (pair-term-halts (pval-halts LHS (λ γ₂ ↓ᴱ π → proj₁ (f γ₂ ↓ᴱ π))) (pval-halts RHS (λ {Γ = Γ₁} γ₂ ↓ᴱ π → proj₂ (f γ₂ ↓ᴱ π)))) env-val (wk-ext wk-id (wk-eq wk-id)) (wk-env-val-wk (pa̲i̲r̲ LHS RHS) enveq-id)
  lookup Cx.h (γ ﹐ pa̲i̲r̲ LHS RHS) (val-in-env M γ₁ f eh) = steps (⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩ ◼) found-pair refl (wk-wk wk-id) refl (pair-term-halts (proj₁ f) (proj₂ f)) env-val (wk-ext wk-id (wk-eq wk-id)) (wk-env-val-wk (pa̲i̲r̲ LHS RHS) enveq-id)
  --lookup Cx.h (γ ﹐ pa̲i̲r̲ LHS RHS) (val-in-env M γ₁ f eh) = steps (⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩ ◼) found-pair refl (wk-wk wk-id) refl (pair-term-halts {!!} {!!}) env-val (wk-ext wk-id (wk-eq wk-id)) (wk-env-val-wk (pa̲i̲r̲ LHS RHS) enveq-id)
  lookup Cx.h (γ ﹐ u̲n̲i̲t̲) (val-in-env M γ₁ vH eh) = steps (⟨ h ∥ _﹐_ γ (u̲n̲i̲t̲) ⟩ ◼) found-unit refl (wk-wk wk-id) refl unit-term-halts env-val (wk-ext wk-id (wk-eq wk-id)) (wk-env-val-wk u̲n̲i̲t̲ enveq-id)
  lookup Cx.h (γ ﹐ v̲a̲r̲ i) (val-in-env M γ₁ vH eh) with lookup i γ eh
  ... | steps {T = T} i>>T HT i≡T WK w≡γ eh' ext we ϖ =
              let
                a0 = li≡i i>>T HT
                a1 = subst (λ x → EnvExt x γ (lEnv T)) (a0) ext
              in
              steps (_ →ᴸ⟨ val-h-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ eh' (ext-jmp a1) (wk-ext WK we) (wk-env-val-wk (v̲a̲r̲ i) ϖ)
  lookup Cx.h ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) (comp-in-env W₁ γ₁ cs₁ x eh) =
    steps (⟨ h ∥ γ ﹐﹝ W ╎ cs ﹞ ⟩ ◼) found-comp refl (wk-wk wk-id) refl (comp-term-halts x) env-comp (wk-ext wk-id (wk-eq wk-id)) (wk-env-comp-wk W cs enveq-id)
  lookup (Cx.t i) (γ ﹐ M) (val-in-env M₁ γ₁ vH eh) with lookup i γ eh
  ... | steps {T = T} i>>T HT i≡T WK w≡γ eh' ext we ϖ = steps (_ →ᴸ⟨ val-t-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ eh' (ext-val ext) (wk-ext WK we) (wk-env-val-wk M ϖ)
  lookup (Cx.t i) (γ ﹐﹝ W ╎ cs ﹞) (comp-in-env W₁ γ₁ cs₁ x eh) with lookup i γ eh
  ... | steps {T = T} i>>T HT i≡T WK w≡γ eh' ext we ϖ =
      steps (_ →ᴸ⟨ (comp-t-step) ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ eh' (ext-comp ext) (wk-ext WK we) (wk-env-comp-wk W cs ϖ)

  -------------------------------------------------------------------

  data CompSteps : CompState → Set where

      steps : {S T : CompState} → S →ᶜ* T → CompHaltingState T → (⟦ S ⟧ᶜꟴ ≡ ⟦ T ⟧ᶜꟴ) → CompSteps S

  get-csteps : {S : CompState} → CompSteps S → Σ[ T ∈ CompState ] ((CompHaltingState T) × (S →ᶜ* T) × (⟦ S ⟧ᶜꟴ ≡ ⟦ T ⟧ᶜꟴ))
  get-csteps {S = S} (steps {T = T} S→T H eq) = T , H , S→T , eq

  wk-comm-explicit : (M : V̲a̲l̲ Γ X) → (π : Wk Δ Γ) → toVal (wk-v̲a̲l̲ π M) ≡ wk-val π (toVal M)
  wk-comm-explicit M π = sym wk-comm
  {-# REWRITE wk-comm-explicit #-}

  mutual

    val-eval-rec : (M : Γ' ⊢ᵛ X) → (γ : Env Γ) → (↓ : PEnvHalts γ) → (π : Wk Γ Γ') → ValSteps {T◾ = X} (∘ ((⇡ (wk-val π M) ⊲ γ ∷ □) {↥ = 🗆}))

    val-eval-rec {X = `V} (var {A = .`V} i) γ ↓ π = steps (_ →ᵛ⟨ ∘var-c ⟩．) (∙ v̲a̲r̲ (wk-mem π i) ⊲ γ ■) refl wk-id refl ↓ {!!} --(pval-halts (haltingTerm ∙ v̲a̲r̲ (wk-mem π i) ⊲ γ ■) (λ {Γ = Γ₁} γ₁ ↓ᴱ π₁ → tt)) --(vs-halts tt)

    val-eval-rec {X = `Unit} (var {A = .`Unit} i) γ ↓ π with lookup (wk-mem π i) γ ↓
    ... | steps i>>T found-unit i≡T π₁ w≡γ ↓ᴸᴴ ext we ϖ =

                steps (_ →ᵛ⟨ ∘var i>>T π₁ ext we ϖ found-unit ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id refl ↓ (λ {Γ = Γ₂} γ₂ ↓ᴱ π' → tt) --(pval-halts (haltingTerm ∙ u̲n̲i̲t̲ ⊲ γ ■) (λ {Γ = Γ₂} γ₂ ↓ᴱ π₂ → tt)) --(vs-halts tt)

    val-eval-rec {X = X `× X₁} (var {A = .(X `× X₁)} i) γ ↓ π with lookup (wk-mem π i) γ ↓
    --... | steps i>>T (found-pair {LHS = LHS} {RHS = RHS} {γ = γ₁}) i≡T π₁ w≡γ (pair-term-halts (pval-halts LHS fL) (pval-halts RHS fR)) ext we ϖ =
    ... | steps i>>T (found-pair {LHS = LHS} {RHS = RHS} {γ = γ₁}) i≡T π₁ w≡γ (pair-term-halts pvL pvR) ext we ϖ =

              steps

              (_ →ᵛ⟨ ∘var i>>T π₁ ext we ϖ found-pair ⟩．)

              (∙ pa̲i̲r̲ (wk-v̲a̲l̲ π₁ LHS) (wk-v̲a̲l̲ π₁ RHS) ⊲ γ ■)

              (⟦ wk-mem π i ⟧ᵐ ⟦ γ ⟧ᴱ
              ≡⟨ i≡T ⟩
              (< ⟦ toVal LHS ⟧ᵛ , ⟦ toVal RHS ⟧ᵛ > ⟦ γ₁ ⟧ᴱ)
              ≡⟨ cong (λ x → < ⟦ toVal LHS ⟧ᵛ , ⟦ toVal RHS ⟧ᵛ > x) (sym w≡γ) ⟩
              (< ⟦ toVal LHS ⟧ᵛ , ⟦ toVal RHS ⟧ᵛ > (⟦ π₁ ⟧ʷ ⟦ γ ⟧ᴱ))
              ≡⟨ refl ⟩
              (⟦ wk-val π₁ (toVal LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ wk-val π₁ (toVal RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)
              ≡⟨ cong (λ x → (⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ wk-val π₁ (toVal RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)) (wk-comm {M = LHS} {π = π₁}) ⟩
              (⟦ toVal (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ wk-val π₁ (toVal RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)
              ≡⟨ cong (λ x → (⟦ toVal (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ)) (wk-comm {M = RHS} {π = π₁}) ⟩
              (⟦ toVal (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ toVal (wk-v̲a̲l̲ π₁ RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)
              ≡⟨ refl ⟩
              (< ⟦ toVal (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ , ⟦ toVal (wk-v̲a̲l̲ π₁ RHS) ⟧ᵛ > ⟦ γ ⟧ᴱ) ∎)

              wk-id

              refl

              ↓

              (wk-pvalhalts LHS π₁ pvL , wk-pvalhalts RHS π₁ pvR) --(pval-halts (haltingTerm ∙ pa̲i̲r̲ (wk-v̲a̲l̲ π₁ LHS) (wk-v̲a̲l̲ π₁ RHS) ⊲ γ ■) λ γ₂ ↓ᴱ π₂ → {!!})

    val-eval-rec {Γ' = Γ'} {X = X `⇒ X₁} {Γ = Γ} (var {A = .(X `⇒ X₁)} i) γ ↓ π with lookup (wk-mem π i) γ ↓

    --... | steps i>>T (found-lam {W = W} {γ = γ₁}) i≡T π₁ w≡γ (lam-term-halts (pval-halts _ f)) ext we ϖ =
    ... | steps i>>T (found-lam {X = X₂} {Y = Y₂} {W = W} {γ = γ₁}) i≡T π₁ w≡γ (lam-term-halts {Γ = Γ₂} {W = W} f) ext we ϖ =

              steps

              (_ →ᵛ⟨ ∘var i>>T π₁ ext we ϖ found-lam ⟩．)

              (∙ (wk-v̲a̲l̲ π₁ (l̲a̲m̲ W)) ⊲ γ ■)

              (⟦ wk-mem π i ⟧ᵐ ⟦ γ ⟧ᴱ
                ≡⟨ i≡T ⟩
              ((λ y → ⟦ W ⟧ᶜ (⟦ γ₁ ⟧ᴱ , y) ))
                ≡⟨ cong (λ x → (λ y → ⟦ W ⟧ᶜ (x , y) )) (sym w≡γ) ⟩
              (λ y → ⟦ W ⟧ᶜ (⟦ π₁ ⟧ʷ ⟦ γ ⟧ᴱ , y) )
                ≡⟨ refl ⟩
              (curry (< (λ r → proj₁ r) ； ⟦ π₁ ⟧ʷ , (λ r → proj₂ r) > ； ⟦ W ⟧ᶜ)) ⟦ γ ⟧ᴱ ∎)

              wk-id

              refl

              ↓

              (wk-pvalhalts (l̲a̲m̲ W) π₁ f) --(pval-halts (haltingTerm ∙ wk-v̲a̲l̲ π₁ (l̲a̲m̲ W) ⊲ γ ■) (λ γ₂ ↓ᴱ π₂ Δ cs π₃ wk≡ N n↓ → {!!}))

    val-eval-rec (lam W) γ ↓ π =

              steps

              (∘ ⇡ (wk-val π (lam W)) ⊲ γ ∷ □ →ᵛ⟨ ∘lam ⟩．)

              (∙ l̲a̲m̲ (wk-comp (wk-cong π) W) ⊲ γ ■)

              refl

              wk-id

              refl

              ↓

              {!-u!} --(pval-halts (haltingTerm ∙ l̲a̲m̲ (wk-comp (wk-cong π) W) ⊲ γ ■) (λ γ₁ ↓ᴱ π₁ Δ cs π₂ wk≡ N n↓ → {!!}))

              -- (vs-halts (λ Δ cs πₓ wk≡₀ N n↓ →
              --   let
              --     IH = comp-eval-rec W (γ ﹐ N) (val-in-env N γ n↓ ↓) (wk-cong π) cs (wk-wk πₓ) wk≡₀ {!!}
              --     s = get-csteps IH
              --   in
              --   comp-halts (proj₁ s) (proj₁ (proj₂ s)) (proj₁ (proj₂ (proj₂ s))) (proj₂ (proj₂ (proj₂ s)))))

              -- (vs-halts (lam-halts λ Δ cs πₓ wk≡₀ N →
              --   let
              --     IH = comp-eval-rec W (γ ﹐ N) {!!} (wk-cong π) cs (wk-wk πₓ) wk≡₀
              --   in
              --   {!!})
              -- )

    val-eval-rec unit γ ↓ π = steps (_ →ᵛ⟨ ∘unit ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id refl ↓ {!!} --(vs-halts tt)

    val-eval-rec (pair {A = X} {B = Y} LHS RHS) γ ↓ π with val-eval-rec {X = X} LHS γ ↓ π
    ... | steps {T = ∙ (⭭_ {X = X} LT ⊲ γ₁ ∷ □) {↥ = 🗆}} L>T ∙LT L≡T πᴸ wk≡ᴸ ↓ᴸ vl↓ with  val-eval-rec {X = Y} RHS γ₁ ↓ᴸ (wk-trans πᴸ π)
    ...      | steps {T = ∙ (⭭_ {X = Y} RT ⊲ γ₂ ∷ □) {↥ = 🗆}} R>T ∙RT R≡T πᴿ wk≡ᴿ ↓ᴿ vr↓ rewrite sym (wk-val-trans RHS πᴸ π) =

              let

                R≡T' : ⟦ wk-val πᴸ (wk-val π RHS) ⟧ᵛ ⟦ γ₁ ⟧ᴱ ≡ ⟦ toVal RT ⟧ᵛ ⟦ γ₂ ⟧ᴱ
                R≡T' =  ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ (⟦ πᴸ ⟧ʷ ⟦ γ₁ ⟧ᴱ))
                      ≡⟨ cong ⟦ RHS ⟧ᵛ (wk-sem-trans πᴸ π ⟦ γ₁ ⟧ᴱ) ⟩
                        ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                      ≡⟨ R≡T ⟩
                        ⟦ toVal RT ⟧ᵛ ⟦ γ₂ ⟧ᴱ ∎

              in

              steps

                (
                ∘ ⇡ (wk-val π (pair LHS RHS)) ⊲ γ ∷ □ →ᵛ⟨ ∘pair ⟩． ⨾
                (⟪ L>T ⟫⧻ (⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⊲ γ ∷ □)) ⨾
                (∙ ⭭ LT ⊲ γ₁ ∷ ⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⊲ γ ∷ □) →ᵛ⟨ ∙M∷l (sym wk≡ᴸ) L≡T ⟩． ⨾
                (⟪ R>T ⟫⧻ (⇡ᴿ LT (wk-val πᴸ (wk-val π RHS)) ⊲ γ₁ ∷ □)) ⨾
                (∙ ⭭ RT ⊲ γ₂ ∷ ⇡ᴿ LT (wk-val πᴸ (wk-val π RHS)) ⊲ γ₁ ∷ □) →ᵛ⟨ ∙M∷r (sym wk≡ᴿ) R≡T' ⟩．
                )

                ∙ pa̲i̲r̲ (wk-v̲a̲l̲ πᴿ LT) RT ⊲ γ₂ ■

                ( ⟦ wk-val π (pair LHS RHS) ⟧ᵛ ⟦ γ ⟧ᴱ
                ≡⟨ refl ⟩
                  (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))
                ≡⟨ cong (λ y → (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ y))) (sym wk≡ᴸ) ⟩
                  (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ (⟦ πᴸ ⟧ʷ ⟦ γ₁ ⟧ᴱ)))
                ≡⟨ cong (λ y → (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ y)) (wk-sem-trans πᴸ π ⟦ γ₁ ⟧ᴱ) ⟩
                  (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
                ≡⟨ cong (λ y → (y , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))) L≡T ⟩
                  (⟦ toVal LT ⟧ᵛ ⟦ γ₁ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
                ≡⟨ cong (λ y → (⟦ toVal LT ⟧ᵛ y , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))) (sym wk≡ᴿ) ⟩
                  (⟦ toVal LT ⟧ᵛ (⟦ πᴿ ⟧ʷ ⟦ γ₂ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
                ≡⟨ refl ⟩
                  (⟦ wk-val πᴿ (toVal LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
                ≡⟨ cong (λ y → (⟦ y ⟧ᵛ ⟦ γ₂ ⟧ᴱ  , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))) (wk-comm {M = LT} {π = πᴿ}) ⟩
                  (⟦ toVal (wk-v̲a̲l̲ πᴿ LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
                ≡⟨ cong (λ y → (⟦ toVal (wk-v̲a̲l̲ πᴿ LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , y)) R≡T ⟩
                  (⟦ toVal (wk-v̲a̲l̲ πᴿ LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , ⟦ toVal RT ⟧ᵛ ⟦ γ₂ ⟧ᴱ)
                ≡⟨ refl ⟩
                  ⟦ pair (toVal (wk-v̲a̲l̲ πᴿ LT)) (toVal RT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ
                ≡⟨ refl ⟩
                  ⟦ toVal (pa̲i̲r̲ (wk-v̲a̲l̲ πᴿ LT) RT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ
                ≡⟨ refl ⟩
                  ⟦ ∙ (⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πᴿ LT) RT ⊲ γ₂ ∷ □) {↥ = 🗆} ⟧ᵛꟴ ∎ )

                (wk-trans πᴿ πᴸ)

                ( ⟦ wk-trans πᴿ πᴸ ⟧ʷ ⟦ γ₂ ⟧ᴱ
                ≡⟨ sym (wk-sem-trans πᴿ πᴸ ⟦ γ₂ ⟧ᴱ) ⟩
                  ⟦ πᴸ ⟧ʷ (⟦ πᴿ ⟧ʷ ⟦ γ₂ ⟧ᴱ)
                ≡⟨ cong (λ y → ⟦ πᴸ ⟧ʷ y) wk≡ᴿ ⟩
                  ⟦ πᴸ ⟧ʷ ⟦ γ₁ ⟧ᴱ
                ≡⟨ wk≡ᴸ ⟩
                  ⟦ γ ⟧ᴱ ∎)

                ↓ᴿ

                {!!}

    val-eval-rec {Γ = Γ} (pm {A = A} {B = B} M N) γ ↓ π with val-eval-rec M γ ↓ π
    ... | steps {S = S} M>T ∙ pa̲i̲r̲ LHS RHS ⊲ γ₁ ■ M≡T π₁ wk≡₁ ↓₁ pv↓ {-(vs-halts v↓)-} with val-eval-rec N (_﹐_ (_﹐_ γ₁ LHS) (wk-v̲a̲l̲ (wk-wk wk-id) RHS)) {!!} {-(val-in-env (wk-v̲a̲l̲ (wk-wk wk-id) RHS) (γ₁ ﹐ LHS) (let v↓' = v↓ (wk-wk wk-id) (γ₁ ﹐ LHS) (⟨ γ₁ ⟩ ﹐ LHS) in proj₂ v↓') (val-in-env LHS γ₁ (let v↓' = v↓ wk-id γ₁ ⟨ γ₁ ⟩ in subst (λ x → ValHalts x γ₁) (wk-v̲a̲l̲-id LHS) (proj₁ v↓')) ↓₁))-} ((wk-cong (wk-cong (wk-trans π₁ π)))) | (wk-val-trans N (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π)))
    ...    | steps {T = T} N>T ∙T N≡T π₂ wk≡₂ ↓₂ v↓₂ | eq with N>T
    ...      | N>T' rewrite sym eq =

          steps
            (
              (∘ ⇡ pm (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⊲ γ ∷ □) →ᵛ⟨ ∘pm ⟩． ⨾
              (⟪ M>T ⟫⧻ (⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⊲ γ ∷ □)) ⨾
              (∙ ⭭ pa̲i̲r̲ LHS RHS ⊲ γ₁ ∷ ⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⊲ γ ∷ □) →ᵛ⟨ ∙pair∷pm (sym wk≡₁) (cong proj₁ M≡T) (cong proj₂ M≡T) ⟩． ⨾
              N>T'
            )

            ∙T

            (  ⟦ wk-val π (pm M N) ⟧ᵛ ⟦ γ ⟧ᴱ
              ≡⟨ refl ⟩
                ⟦ pm (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⟧ᵛ ⟦ γ ⟧ᴱ
              ≡⟨ refl ⟩
              (< idf , ⟦ π ⟧ʷ ； ⟦ M ⟧ᵛ > ； assocl ； ⟦ wk-val (wk-cong (wk-cong π)) N ⟧ᵛ) ⟦ γ ⟧ᴱ
              ≡⟨ refl ⟩
              ⟦ wk-val (wk-cong (wk-cong π)) N ⟧ᵛ (assocl ( (⟦ γ ⟧ᴱ ,  ⟦ M ⟧ᵛ  (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))))
              ≡⟨ cong (λ y → ⟦ wk-val (wk-cong (wk-cong π)) N ⟧ᵛ (assocl ( (⟦ γ ⟧ᴱ , y   )))) M≡T ⟩
              ⟦ wk-val (wk-cong (wk-cong π)) N ⟧ᵛ (assocl ( (⟦ γ ⟧ᴱ ,  (⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)  )))
              ≡⟨ refl ⟩
                ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
              ≡⟨ cong  (λ y → ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ y , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)) (sym wk≡₁) ⟩
                ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
              ≡⟨ refl ⟩
                ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ (wk-val (wk-wk wk-id) (toVal RHS)) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
              ≡⟨ cong (λ y → ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ y ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))) (wk-comm {M = RHS} {π = wk-wk wk-id}) ⟩
                ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
              ≡⟨ cong (λ y → ⟦ N ⟧ᵛ ((y , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))  ) (wk-sem-trans π₁ π ⟦ γ₁ ⟧ᴱ) ⟩
              ⟦ N ⟧ᵛ ((⟦ wk-trans π₁ π ⟧ʷ ⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
              ≡⟨ N≡T ⟩
              ⟦ T ⟧ᵛꟴ ∎)

            (wk-trans π₂ (wk-wk (wk-wk π₁)))

            ( ⟦ wk-trans π₂ (wk-wk (wk-wk π₁)) ⟧ʷ ⟦ botEnv T ⟧ᴱ
              ≡⟨ sym (wk-sem-trans π₂ (wk-wk (wk-wk π₁)) ⟦ botEnv T ⟧ᴱ) ⟩
              ⟦ wk-wk (wk-wk π₁) ⟧ʷ (⟦ π₂ ⟧ʷ ⟦ botEnv T ⟧ᴱ)
              ≡⟨ cong (λ y → ⟦ wk-wk (wk-wk π₁) ⟧ʷ y) wk≡₂ ⟩
              ⟦ wk-wk (wk-wk π₁) ⟧ʷ (((⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))
              ≡⟨ refl ⟩
              ⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ
              ≡⟨ wk≡₁ ⟩
              ⟦ γ ⟧ᴱ ∎)

            ↓₂

            v↓₂

    val-eval : (M : ε ⊢ᵛ X) → ValSteps {T◾ = X} (∘ ((⇡ wk-val wk-id M ⊲ ∗ ∷ □) {↥ = 🗆}))
    val-eval M = val-eval-rec M ∗ empty-penv wk-id


    app-eval-rec :   (M : Γ' ⊢ᵛ X `⇒ Y) → (N : V̲a̲l̲ Γ X) → (γ : Env Γ) → (↓ : PEnvHalts γ) → (n↓ : PValHalts N) → (π : Wk Γ Γ') → (cs : CompStack Δ Y) → (πₓ : Wk Γ Δ)
                   → (wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → (↓ᶜ : CSHalts cs)
                   → CompSteps ((∙⟨ (a̲pp (wk-val π M) N) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    app-eval-rec (var i) N γ ↓ n↓ π cs πₓ wk≡₀ ↓ᶜ with lookup (wk-mem π i) γ ↓
    ... | steps i>>T (found-lam {X = X} {W = W} {γ = γ₁}) i≡T π₁ w≡γ (lam-term-halts f) ext we ϖ =

                let
                  --a0 = f _ γ {!!} π₁ _ cs ↓ᶜ πₓ wk≡₀ N {!!}
                  a0 = f _ γ {!!} π₁ _ cs πₓ wk≡₀ N {!!}
                  a1 = get-chsteps a0
                in

                steps

                  ((∙⟨ a̲pp (wk-val π (var i)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-var {wk≡ₓ = wk≡₀} i>>T π₁ ⟩ proj₂ a1))

                  {!!}

                  {!!}

    {-
    with comp-eval-rec W (γ ﹐ N) (val-in-env N γ n↓ ↓) (wk-cong π₁) cs (wk-wk πₓ) wk≡₀
    ... | steps {T = T} W>WT HT S≡T =

                 steps

                    ((∙⟨ a̲pp (wk-val π (var i)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-var {wk≡ₓ = wk≡₀} i>>T π₁ ⟩ W>WT))

                    HT

                    (   ⟦ ((∙⟨ C̲o̲m̲p.a̲pp (var (wk-mem π i)) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀}) ⟧ᶜꟴ
                      ≡⟨ refl ⟩
                        ⟦ wk-mem π i ⟧ᵐ ⟦ γ ⟧ᴱ (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ cong (λ x → x (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) i≡T ⟩
                       ⟦ W ⟧ᶜ (⟦ γ₁ ⟧ᴱ , (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ))  (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ cong (λ x → ⟦ W ⟧ᶜ (x , (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ))  (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym w≡γ) ⟩
                       ⟦ W ⟧ᶜ (⟦ π₁ ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ refl ⟩
                        ⟦ ((∘⟨ wk-comp (wk-cong π₁) W ⊰ γ Env.﹐ N ╎ cs ⟩) {π = wk-wk πₓ} {wk≡ = wk≡₀}) ⟧ᶜꟴ
                      ≡⟨ S≡T ⟩
                        ⟦ T ⟧ᶜꟴ ∎)
    -}


    app-eval-rec (lam W) N γ ↓ n↓ π cs πₓ wk≡₀ ↓ᶜ with comp-eval-rec W (γ ﹐ N) (val-in-env N γ n↓ ↓) (wk-cong π) cs (wk-wk πₓ) wk≡₀ {!!}
    ... | steps {T = T} W>WT HT S≡T =

                  steps

                     ( ∙⟨ a̲pp (wk-val π (lam W)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-lam {wk≡ₓ = wk≡₀} ⟩ W>WT)

                     HT

                     S≡T

    app-eval-rec (pm M₁ N₁) N γ ↓ n↓ π cs πₓ wk≡₀ ↓ᶜ with val-eval-rec M₁ γ ↓ π
    ... | steps {T = ∙ (⭭ pa̲i̲r̲ {X = X} {Y = Y} LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ ↓ᵛ v↓ with wk-val-trans N₁ (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
    ...       | eq with
                    app-eval-rec
                      N₁
                      ((wk-v̲a̲l̲ (wk-wk (wk-wk π')) N))
                      (γ₁ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS)
                      {!!}
                      {!!}
                      (wk-cong (wk-cong (wk-trans π' π)))
                      cs
                      (wk-wk (wk-wk (wk-trans π' πₓ)))
                      (⟦ wk-wk (wk-wk (wk-trans π' πₓ)) ⟧ʷ ⟦ γ₁ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ⟧ᴱ
                       ≡⟨ refl ⟩ ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                       ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                       ≡⟨ wk≡₀ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎)
                      {!!}
    ...          | steps {T = T} N>NT NT S≡T rewrite (sym eq) =

                 steps

                    (∙⟨ (a̲pp (wk-val π (pm M₁ N₁)) N) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-pm {wk≡ₓ = wk≡₀} {wk≡ₓ' = ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ) ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡⟨ wk≡₀ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎} M>T π' ⟩ N>NT )

                    NT

                    (⟦ N₁ ⟧ᵛ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , proj₁ (⟦ M₁ ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))) , proj₂ (⟦ M₁ ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))) (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ cong (λ x → ⟦ N₁ ⟧ᵛ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , proj₁ x) , proj₂ x) (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) M≡T ⟩
                     ⟦ N₁ ⟧ᵛ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ cong (λ x → ⟦ N₁ ⟧ᵛ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) (⟦ toVal N ⟧ᵛ x) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym wk≡) ⟩
                     ⟦ N₁ ⟧ᵛ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ wk-id RHS) ⟧ᵛ ⟦ γ₁ ⟧ᴱ) (⟦ toVal N ⟧ᵛ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ refl ⟩
                     ⟦ N₁ ⟧ᵛ (( ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                               ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ ,
                               ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
                             (⟦ toVal (wk-v̲a̲l̲ (wk-wk (wk-wk π')) N) ⟧ᵛ ((⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                              ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))
                             (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ cong (λ x → ⟦ N₁ ⟧ᵛ ((⟦ π ⟧ʷ x , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                                               ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ ,
                                               ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)) (⟦ toVal (wk-v̲a̲l̲ (wk-wk (wk-wk π')) N) ⟧ᵛ ((⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                                               ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))
                                             (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym wk≡) ⟩
                     ⟦ N₁ ⟧ᵛ (( ⟦ π ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                               ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
                             ( ⟦ toVal (wk-v̲a̲l̲ (wk-wk (wk-wk π')) N) ⟧ᵛ ((⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                               ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ cong (λ x → ⟦ N₁ ⟧ᵛ ((x ,
                                              ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                                              ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
                                             (⟦ toVal (wk-v̲a̲l̲ (wk-wk (wk-wk π')) N) ⟧ᵛ ((⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                                              ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))
                                             (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀) ) (wk-sem-trans π' π ⟦ γ₁ ⟧ᴱ) ⟩
                     ⟦ N₁ ⟧ᵛ (( ⟦ wk-trans π' π ⟧ʷ ⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                               ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
                             ( ⟦ toVal (wk-v̲a̲l̲ (wk-wk (wk-wk π')) N) ⟧ᵛ ((⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                               ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))
                             (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ S≡T ⟩
                     ⟦ T ⟧ᶜꟴ ∎)

    comp-eval-rec : (W : Γ' ⊢ᶜ X) → (γ : Env Γ) → (↓ : PEnvHalts γ) → (π : Wk Γ Γ') → (cs : CompStack Δ X) → (πₓ : Wk Γ Δ)
                  → (wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → (↓ᶜ : CSHalts cs)
                  → CompSteps ((∘⟨ wk-comp π W ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    comp-eval-rec (return {A = X} M) γ ↓ π ◻ πₓ wk≡₀ ↓ᶜ with val-eval-rec {X = X} M γ ↓ π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ ↓ᵛ v↓ =

                 steps

                    (∘⟨ wk-comp π (return M) ⊰ γ ╎ ◻ ⟩ →ᶜ⟨ ∘return {wk≡ₓ = wk≡₀} {wk≡ₓ' = wk≡₀} M>T ⟩ (∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ ◻ ⟩ ◼))

                    ret

                    (cong (λ x → (η x) k₀) M≡T)

    comp-eval-rec (return {A = X} M) γ ↓ π ((M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁}) πₓ wk≡₀ (cs-head-halts ↓ᵂ _) with val-eval-rec {X = X} M γ ↓ π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ ↓ᵛ pv↓ {-(vs-halts v↓)-} with ↓ᵂ _ (wk-trans π' πₓ) (wk-trans (wk-trans (wk-wk π') πₓ) π₁) γ₁ ↓ᵛ {-↓ᵛ-} M₁ {!-u!} {-v↓-} {!!}
    ... | (comp-halts T' H' S→T' eq') = --{!!}
                 steps

                 ((∘⟨ wk-comp π (return M) ⊰ γ ╎ (M' ⊲ γ' ⦂⦂ cs) ⟩
                    →ᶜ⟨ ∘return {wk≡ₓ = wk≡₀} {wk≡ₓ' = ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ
                                         ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                                         ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                                         ≡⟨ wk≡₀ ⟩ ⟦ γ' ⟧ᴱ ∎} M>T ⟩ _
                    →ᶜ⟨ ∙return {πₓ = wk-trans (wk-trans π' πₓ) π₁} {πₓ' = π₁} {wk≡ₓ = ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ) ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ _ ⟧ᴱ ≡⟨ wk≡₀ ⟩ ⟦ γ' ⟧ᴱ ∎} {wk≡ₓ' = ⟦ wk-trans (wk-trans π' πₓ) π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡⟨ sym (wk-sem-trans (wk-trans π' πₓ) π₁ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ π₁ ⟧ʷ (⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ) ≡⟨ cong ⟦ π₁ ⟧ʷ (sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ)) ⟩ ⟦ π₁ ⟧ʷ (⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ)) ≡⟨ cong (λ x → ⟦ π₁ ⟧ʷ (⟦ πₓ ⟧ʷ x)) wk≡ ⟩ ⟦ π₁ ⟧ʷ (⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ) ≡⟨ cong ⟦ π₁ ⟧ʷ wk≡₀ ⟩ ⟦ π₁ ⟧ʷ ⟦ γ' ⟧ᴱ ≡⟨ wk≡₁ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎} ⟩
                    S→T' ) )

                 H'

                 {!!}
    {-
    with
                 comp-eval-rec
                   M'
                   (γ₁ ﹐ M₁)
                   (val-in-env M₁ γ₁ v↓ ↓ᵛ)
                   (wk-cong (wk-trans π' πₓ))
                   cs
                   (wk-wk (wk-trans (wk-trans π' πₓ) π₁))
                   (⟦ wk-wk (wk-trans (wk-trans π' πₓ) π₁) ⟧ʷ ⟦ γ₁ ﹐ M₁ ⟧ᴱ
                    ≡⟨ refl ⟩ ⟦ (wk-trans (wk-trans π' πₓ) π₁) ⟧ʷ ⟦ γ₁ ⟧ᴱ
                    ≡⟨ sym (wk-sem-trans (wk-trans π' πₓ) π₁ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ π₁ ⟧ʷ (⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                    ≡⟨ cong ⟦ π₁ ⟧ʷ (sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ)) ⟩ ⟦ π₁ ⟧ʷ (⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ))
                    ≡⟨ cong (λ x → ⟦ π₁ ⟧ʷ (⟦ πₓ ⟧ʷ x)) wk≡ ⟩ ⟦ π₁ ⟧ʷ (⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ)
                    ≡⟨ cong ⟦ π₁ ⟧ʷ wk≡₀ ⟩ ⟦ π₁ ⟧ʷ ⟦ γ' ⟧ᴱ
                    ≡⟨ wk≡₁ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎)
    ... | steps {T = ∙⟨ r̲e̲t̲u̲r̲n̲  M₂ ⊰ γ₂ ╎ ◻ ⟩} M'>T ret S≡T =

                   steps

                   (∘⟨ wk-comp π (return M) ⊰ γ ╎ (M' ⊲ γ' ⦂⦂ cs) ⟩
                    →ᶜ⟨ ∘return {wk≡ₓ = wk≡₀} {wk≡ₓ' = ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ
                                         ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                                         ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                                         ≡⟨ wk≡₀ ⟩ ⟦ γ' ⟧ᴱ ∎} M>T ⟩ ((∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ M' ⊲ γ' ⦂⦂ cs ⟩) {wk≡ = ≡-syntax.step-≡-⟩ _≡_ trans (⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                                                                                                                   (≡-syntax.step-≡-⟩ _≡_ trans (⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ))
                                                                                                                    (≡-syntax.step-≡-⟩ _≡_ trans (⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ)
                                                                                                                     ((_≡_ end-syntax.∎) refl ⟦ γ' ⟧ᴱ) wk≡₀)
                                                                                                                    (cong ⟦ πₓ ⟧ʷ wk≡))
                                                                                                                   (sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ))})
                    →ᶜ⟨ ∙return {πₓ = wk-trans (wk-trans π' πₓ) π₁} {πₓ' = π₁} {wk≡ₓ = ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ) ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ _ ⟧ᴱ ≡⟨ wk≡₀ ⟩ ⟦ γ' ⟧ᴱ ∎} {wk≡ₓ' = ⟦ wk-trans (wk-trans π' πₓ) π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡⟨ sym (wk-sem-trans (wk-trans π' πₓ) π₁ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ π₁ ⟧ʷ (⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ) ≡⟨ cong ⟦ π₁ ⟧ʷ (sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ)) ⟩ ⟦ π₁ ⟧ʷ (⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ)) ≡⟨ cong (λ x → ⟦ π₁ ⟧ʷ (⟦ πₓ ⟧ʷ x)) wk≡ ⟩ ⟦ π₁ ⟧ʷ (⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ) ≡⟨ cong ⟦ π₁ ⟧ʷ wk≡₀ ⟩ ⟦ π₁ ⟧ʷ ⟦ γ' ⟧ᴱ ≡⟨ wk≡₁ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎} ⟩ M'>T)

                   ret

                   (   ((⟦ π ⟧ʷ ； ⟦ M ⟧ᵛ) ； η) ⟦ γ ⟧ᴱ ⟦ (M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁} ⟧ᴷ
                     ≡⟨ refl ⟩
                       ⟦ cs ⟧ᶜˢ (λ k → ⟦ M' ⟧ᶜ (⟦ γ' ⟧ᴱ , ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) k) k₀
                     ≡⟨ lem0 cs (⟦ M' ⟧ᶜ (⟦ γ' ⟧ᴱ , ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))) ⟩
                       ⟦ M' ⟧ᶜ (⟦ γ' ⟧ᴱ , ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                     ≡⟨ cong (λ x → ⟦ M' ⟧ᶜ (x , ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym wk≡₀) ⟩
                       ⟦ M' ⟧ᶜ (⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                     ≡⟨ cong (λ x → ⟦ M' ⟧ᶜ (⟦ πₓ ⟧ʷ x , ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym wk≡) ⟩
                       ⟦ M' ⟧ᶜ (⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                     ≡⟨ cong (λ x → ⟦ M' ⟧ᶜ (⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ) , x) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) M≡T ⟩
                       ⟦ M' ⟧ᶜ (⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                     ≡⟨ cong (λ x → ⟦ M' ⟧ᶜ (x , ⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ) ⟩
                       ⟦ M' ⟧ᶜ (⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ , ⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                     ≡⟨ refl ⟩
                       (< (λ r → proj₁ r) ； ⟦ wk-trans π' πₓ ⟧ʷ , (λ r → proj₂ r) > ； ⟦ M' ⟧ᶜ) (⟦ γ₁ ⟧ᴱ , ⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ⟦ cs ⟧ᴷ
                     ≡⟨ S≡T ⟩
                       (⟦ toVal M₂ ⟧ᵛ ； η) ⟦ γ₂ ⟧ᴱ ⟦ ◻ ⟧ᴷ ∎)
    -}

    comp-eval-rec (pm {A = X} {B = Y} M W) γ ↓ π cs πₓ wk≡₀ ↓ᶜ with val-eval-rec {X = X `× Y} M γ ↓ π
    ...  | steps {T = ∙ ((⭭_ {X = X `× Y} (pa̲i̲r̲ LHS RHS) ⊲ γ' ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ ↓ᵛ pv↓ {-(vs-halts v↓)-} with
                    comp-eval-rec
                     W
                     (γ' ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS)
                     {!!} --((val-in-env (wk-v̲a̲l̲ (wk-wk wk-id) RHS) (γ' ﹐ LHS) (let v↓' = {!!} {-v↓-} (wk-wk wk-id) (γ' ﹐ LHS) (⟨ γ' ⟩ ﹐ LHS) in proj₂ v↓') (val-in-env LHS γ' (let v↓' = {!!} {-v↓-} wk-id γ' ⟨ γ' ⟩ in subst (λ x → ValHalts x γ') (wk-v̲a̲l̲-id LHS) (proj₁ v↓')) ↓ᵛ)))
                     (wk-trans (wk-cong (wk-cong π')) (wk-cong (wk-cong π)))
                     cs
                     (wk-wk (wk-wk (wk-trans π' πₓ)))
                     (⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ' ⟧ᴱ
                      ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ' ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ)
                      ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                      ≡⟨ wk≡₀ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎)
                     {!!} --↓ᶜ
    ...   | steps {T = T} W>T HT S≡T with wk-comp-trans W (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
    ...     | eq rewrite (sym eq) =

                steps

                   (∘⟨ wk-comp π (pm M W) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘pm {wk≡ₓ = wk≡₀} {wk≡ₓ' = ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ' ⟧ᴱ ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ' ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ) ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡⟨ wk≡₀ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎} π M>T π' ⟩ W>T)

                   HT

                   ( ⟦ W ⟧ᶜ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , proj₁ (⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))) , proj₂ (⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ cong₂ (λ x y → ⟦ W ⟧ᶜ ((⟦ π ⟧ʷ x , proj₁ y) , proj₂ y) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym wk≡) M≡T ⟩
                     ⟦ W ⟧ᶜ ((⟦ π ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ' ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ' ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ cong (λ x → ⟦ W ⟧ᶜ ((x , ⟦ toVal LHS ⟧ᵛ ⟦ γ' ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ' ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (wk-sem-trans π' π ⟦ γ' ⟧ᴱ) ⟩
                     ⟦ W ⟧ᶜ ((⟦ wk-trans π' π ⟧ʷ ⟦ γ' ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ' ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ' ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ S≡T ⟩
                     ⟦ T ⟧ᶜꟴ ∎)

    comp-eval-rec (push W V) γ ↓ π cs πₓ wk≡₀ ↓ᶜ with
      comp-eval-rec W γ ↓ π (((wk-comp (wk-cong π) V) ⊲ γ ⦂⦂ cs) {wk≡ = wk≡₀}) wk-id refl --{!!}
        (cs-head-halts
          (λ Γ' π' π'' γ' ↓ᴱ M ↓ᵛ wk≡' →
            let
              IH = comp-eval-rec V (γ' ﹐ M) (val-in-env M γ' ↓ᵛ ↓ᴱ) (wk-cong (wk-trans π' π)) cs π'' wk≡' ↓ᶜ
              s = get-csteps IH
              s1 = (proj₁ (proj₂ (proj₂ s)))
            in
            comp-halts (proj₁ s) (proj₁ (proj₂ s)) {!!} {!!})
          ↓ᶜ)
    ... | steps {T = ∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ₁ ╎ ◻ ⟩} W>T ret S≡T =

                steps

                  (  ∘⟨ push (wk-comp π W) (wk-comp (wk-cong π) V) ⊰ γ ╎ cs ⟩  →ᶜ⟨ ∘push {wk≡ₓ = wk≡₀} ⟩ W>T )

                  ret

                  (  ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (λ z → ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀))
                  ≡⟨  cong (⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) (extensionality (λ z → sym (lem0 cs ((⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , z)))))) ⟩
                     ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (λ z → ⟦ cs ⟧ᶜˢ (λ k → ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , z) k) k₀)
                  ≡⟨ refl ⟩
                    (⟦ π ⟧ʷ ； ⟦ W ⟧ᶜ) ⟦ γ ⟧ᴱ ⟦ (wk-comp (wk-cong π) V ⊲ γ ⦂⦂ cs) {π = πₓ} {wk≡ = wk≡₀} ⟧ᴷ
                  ≡⟨ S≡T ⟩
                    (⟦ toVal M ⟧ᵛ ； η) ⟦ γ₁ ⟧ᴱ ⟦ ◻ ⟧ᴷ ∎)

    comp-eval-rec (app M N) γ ↓ π cs πₓ wk≡₀ ↓ᶜ with val-eval-rec N γ ↓ π
    ... | steps {T = ∙ ((⭭_ NT ⊲ γᴺ ∷ □) {↥ = 🗆})} N>NT ∙NT N≡NT πᴺ wk≡ᴺ ↓ᵛ pv↓ {-(vs-halts v↓)-} with
                    app-eval-rec
                      M
                      NT
                      γᴺ
                      ↓ᵛ
                      {!!} --v↓
                      (wk-trans πᴺ π)
                      cs
                      (wk-trans πᴺ πₓ)
                      (⟦ wk-trans πᴺ πₓ ⟧ʷ ⟦ γᴺ ⟧ᴱ
                       ≡⟨ sym (wk-sem-trans πᴺ πₓ ⟦ γᴺ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ πᴺ ⟧ʷ ⟦ γᴺ ⟧ᴱ)
                       ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ᴺ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                       ≡⟨ wk≡₀ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎)
                      {!!} --↓ᶜ
    ... | steps {T = T} W>WT HT S≡T rewrite (sym (wk-val-trans M πᴺ π)) =

            steps

                ((∘⟨ app (wk-val π M) (wk-val π N) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘app {wk≡ₓ = wk≡₀} {wk≡ₓ' = ⟦ wk-trans πᴺ πₓ ⟧ʷ ⟦ γᴺ ⟧ᴱ ≡⟨ sym (wk-sem-trans πᴺ πₓ ⟦ γᴺ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ πᴺ ⟧ʷ ⟦ γᴺ ⟧ᴱ) ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ᴺ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡⟨ wk≡₀ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎} N>NT πᴺ ⟩ W>WT ))

                HT

                ((< ⟦ π ⟧ʷ ； ⟦ M ⟧ᵛ , ⟦ π ⟧ʷ ； ⟦ N ⟧ᵛ > ； Data.Product.uncurry idf) ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ
                ≡⟨ refl ⟩
                 ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (⟦ N ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                ≡⟨ cong (λ x → ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) x (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) N≡NT ⟩
                 ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (⟦ toVal NT ⟧ᵛ ⟦ γᴺ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                ≡⟨ cong (λ x → ⟦ M ⟧ᵛ (⟦ π ⟧ʷ x) (⟦ toVal NT ⟧ᵛ ⟦ γᴺ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym wk≡ᴺ) ⟩
                 ⟦ M ⟧ᵛ (⟦ π ⟧ʷ (⟦ πᴺ ⟧ʷ ⟦ γᴺ ⟧ᴱ)) (⟦ toVal NT ⟧ᵛ ⟦ γᴺ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                ≡⟨ cong (λ x → ⟦ M ⟧ᵛ x (⟦ toVal NT ⟧ᵛ ⟦ γᴺ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (wk-sem-trans πᴺ π ⟦ γᴺ ⟧ᴱ) ⟩
                 ⟦ M ⟧ᵛ (⟦ wk-trans πᴺ π ⟧ʷ ⟦ γᴺ ⟧ᴱ) (⟦ toVal NT ⟧ᵛ ⟦ γᴺ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                ≡⟨ S≡T ⟩
                ⟦ T ⟧ᶜꟴ ∎)

    comp-eval-rec (var {A = X} M) γ ↓ π cs πₓ wk≡₀ ↓ᶜ with val-eval-rec {X = `V} M γ ↓ π
    ... | steps {T = ∙ ((⭭ v̲a̲r̲ i) ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ ↓ᵛ v↓ with lookup i γ₁ ↓ᵛ
    ... | steps i>>T (found-comp {X = X} {W = W'} {γ = γ'} {cs = cs'} {π = πᶜ} {wk≡ = wk≡c}) i≡T π₂ w≡γ (comp-term-halts (comp-halts T' H' S→T' eq')) ext we ϖ =

                steps

                  ((∘⟨ var (wk-val π M) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘var {wk≡ₓ = wk≡₀} M>T π' i>>T π₂ ⟩ S→T'))

                  H'

                  (((⟦ π ⟧ʷ ； ⟦ M ⟧ᵛ) ； varK) ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ
                    ≡⟨ refl ⟩
                      ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)
                    ≡⟨ M≡T ⟩
                      ⟦ i ⟧ᵐ ⟦ γ₁ ⟧ᴱ
                    ≡⟨ i≡T ⟩
                      ⟦ W' ⟧ᶜ ⟦ γ' ⟧ᴱ (λ y → ⟦ cs' ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ eq' ⟩
                      ⟦ T' ⟧ᶜꟴ ∎
                  )
    {-
    with
                    comp-eval-rec
                     W'
                     γ'
                     {!!}
                     wk-id
                     cs'
                     πᶜ
                     wk≡c
    ... | steps {T = ∙⟨ C̲o̲m̲p.r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₂ ╎ ◻ ⟩} W>T ret S≡T rewrite wk-comp-id W' =

                steps

                  ((∘⟨ var (wk-val π M) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘var {wk≡ₓ = wk≡₀} M>T π' i>>T π₂ ⟩ W>T))

                  ret

                  (((⟦ π ⟧ʷ ； ⟦ M ⟧ᵛ) ； varK) ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ
                    ≡⟨ refl ⟩
                      ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)
                    ≡⟨ M≡T ⟩
                      ⟦ i ⟧ᵐ ⟦ γ₁ ⟧ᴱ
                    ≡⟨ i≡T ⟩
                      ⟦ W' ⟧ᶜ ⟦ γ' ⟧ᴱ (λ y → ⟦ cs' ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ S≡T ⟩
                      (⟦ toVal M₁ ⟧ᵛ ； η) ⟦ γ₂ ⟧ᴱ ⟦ ◻ ⟧ᴷ ∎
                  )
                 -}

    comp-eval-rec (sub W V) γ ↓ π cs πₓ wk≡₀ ↓ᶜ with comp-eval-rec W ((γ ﹐﹝ wk-comp π V ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡₀}) {!!} (wk-cong π) cs (wk-wk πₓ) wk≡₀ {!comp-halts ? ?!} --↓ᶜ
    ... | steps {T = T} W>WT HT S≡T =

                steps

                    (∘⟨ sub (wk-comp (wk-cong π) W) (wk-comp π V) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘sub ⟩ W>WT)

                    HT

                    S≡T

    comp-eval : (W : ε ⊢ᶜ R₀) → CompSteps ((∘⟨ wk-comp wk-id W ⊰ ∗ ╎ ◻ ⟩) {π = wk-id} {wk≡ = refl})
    comp-eval W = comp-eval-rec W ∗ empty-penv wk-id ◻ wk-id refl cs-empty


postulate k₀ : ⟦ `Unit ⟧ → R

open MachineMain {R₀ = `Unit} k₀
open EvalMain {R₀ = `Unit} k₀

---- Examples

-- s/\(PartialTerm\.\|ValStack\.\|Env\.\|V̲a̲l̲\.\|CompStack\.\|ValStack\.\|ValState\.\|_↠ᵛ_\.\|_→ᵛ_\.\|_→ᴸ\*_\.\|_→ᴸ_\.\|LookupState\.\|C̲o̲m̲p.\)//g

ex3 : ε ⊢ᶜ `Unit
ex3 = return (pm (pair unit unit) (var (t h)))

ex4 : ε ⊢ᶜ `Unit
ex4 = sub (var (var h)) (return (pm (pair unit unit) (var (t h))))

ex5 : ε ⊢ᶜ `Unit
ex5 = push (sub (push (return (var h)) (var (var h))) (return (pm (pair unit unit) (var (t h))))) (return (var h))

ex6 : ε ⊢ᶜ `Unit
ex6 = sub (var (pm (pair (var h) unit) (var (t h)))) (return unit)

ex7 : ε ⊢ᶜ `Unit
ex7 = push (sub (var (pm (pair (var h) unit) (var (t h)))) (return unit)) (return (var h))

ex8 : ε ⊢ᶜ `Unit
ex8 = sub (push (var (var h)) (app (var h) unit)) (return unit)

ex9 : ε ⊢ᶜ `Unit
ex9 = sub (push (sub (return (var h)) ((return (var h)))) (var (var h))) (return unit)

ex10 : ε ⊢ᶜ `Unit
ex10 = push (sub (push (var (var h)) (app (var h) unit)) (return unit)) (return unit)

ex11 : ε ⊢ᶜ `Unit
ex11 = app (lam (app (lam (push (sub (push (var (var h)) (app (var h) unit)) (return (lam (return (var h))))) (app (var h) unit))) unit)) unit

ex12 : ε ⊢ᶜ `Unit
ex12 = push (return unit) (return (pm (pair (pair unit unit) (pair unit unit)) unit))

ex13 : ε ⊢ᶜ `Unit
ex13 = sub ((var (var h))) (return (pm (pair (pair unit unit) (pair unit unit)) unit))

ex14 : ε ⊢ᶜ (`Unit)
ex14 = push (push (app (lam {A = `Unit} (sub (var (var h)) (return unit))) unit) (return unit)) (app (lam (return unit)) (pair (pair (pair (var h) (var h)) (var h)) (var h)))

ex15 : ε ⊢ᶜ (`Unit)
ex15 = push (push (app (lam {A = `Unit} (sub (var (var h)) (return unit))) unit) (return unit)) (return unit)

-- _ : comp-eval ex15 ≡ {! comp-eval ex15 !}
-- _ = refl
