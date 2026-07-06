{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Eval (R : Set) where

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

  -------------------------------------------------------------------

  data ValHalts : (M : V̲a̲l̲ Γ Z) (γ : Env Γ) → Set

  data CompHalts : (W : Γ ⊢ᶜ Z) (γ : Env Γ) (cs : CompStack Δ Z) (π : Wk Γ Δ) .(wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → Set

  data CompHalts where

    comp-halts : {W : Γ ⊢ᶜ Z} {γ : Env Γ} {cs : CompStack Δ Z} {π : Wk Γ Δ} .{wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
            {M : V̲a̲l̲ Γ' Z} {γ' : Env Γ'} {π' : Wk Γ' Δ} .{wk≡' : ⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
            → (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡})) →ᶜ* ((∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ' ╎ cs ⟩) {π = π'} {wk≡ = wk≡'})
            → ⟦ (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡})) ⟧ᶜꟴ ≡ ⟦ ((∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ' ╎ cs ⟩) {π = π'} {wk≡ = wk≡'}) ⟧ᶜꟴ
            → CompHalts W γ cs π wk≡

  data ValHalts where

    unit-halts : {γ : Env Γ} → ValHalts u̲n̲i̲t̲ γ

    pair-halts : {γ : Env Γ} {M₁ : V̲a̲l̲ Γ X} {M₂ : V̲a̲l̲ Γ X} → ValHalts M₁ γ → ValHalts M₂ γ → ValHalts (pa̲i̲r̲ M₁ M₂) γ

    var-halts : {γ : Env Γ} {i : Γ ∋ `V} → ValHalts (v̲a̲r̲ i) γ

    lam-halts : {W : (Γ ∙ X) ⊢ᶜ Y} {γ : Env Γ} →
                 ( Σ[ Δ ∈ Ctx ]
                   Σ[ cs ∈ CompStack Δ Y ]
                   Σ[ π ∈ Wk Γ Δ ]
                   Σ[ wk≡ ∈ ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ ]
                   Σ[ N ∈ Val Γ X ]
                   (CompHalts (app (lam W) N) γ cs π wk≡) )
                   → ValHalts (l̲a̲m̲ W) γ


  ------------------------------------------------------

  {-
  wk-comp-halts : {W : Γ ⊢ᶜ Z} {γ : Env Γ} {cs : CompStack Δ Z} {π : Wk Γ Δ} .{wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                  {π' : Wk Γ' Γ} {γ' : Env Γ'} → EnvEq π' γ' γ
                  → CompHalts W γ cs π wk≡
                  → Σ[ π'' ∈ Wk Γ' Δ ] Σ[ wk≡' ∈ ⟦ π'' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ ] CompHalts (wk-comp π' W) γ' cs π'' wk≡'
  wk-comp-halts {W = W} {γ = γ} {cs = cs} {π = π} {π' = π'} {γ' = γ'} ϖ (comp-halts {W = W} {γ = γ} {cs = cs} {π = π} {M = M} {γ' = γ₁} {π' = π₁} W→W' W≡W') =
                _ , {!!} , comp-halts {W = wk-comp π' W} {γ = γ'} {cs = cs} {π = wk-trans π' π} {M = {!!}} {γ' = γ₁} {π' = π₁} {wk≡' = {!!}} {!!} {!!}
                -- wk-trans π' π , {!!} , {!!}


  wk-val-halts : {M : V̲a̲l̲ Γ X} {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ} → EnvEq π γ' γ → ValHalts M γ → ValHalts (wk-v̲a̲l̲ π M) γ'
  wk-val-halts {M = M} {π = π} {γ' = γ'} {γ = γ} _ unit-halts = unit-halts
  wk-val-halts {M = M} {π = π} {γ' = γ'} {γ = γ} ϖ (pair-halts vH₁ vH₂) = pair-halts (wk-val-halts ϖ vH₁) (wk-val-halts ϖ vH₂)
  wk-val-halts {M = M} {π = π} {γ' = γ'} {γ = γ} _ var-halts = var-halts
  wk-val-halts {M = M} {π = π} {γ' = γ'} {γ = γ} ϖ (lam-halts (Δ₁ , cs₁ , π₁ , wk≡₁ , N₁ , CH₁)) = lam-halts (Δ₁ , cs₁ , wk-trans π π₁ , {!!} , wk-val π N₁ , {!!})
  -}

  ------------------------------------------------------

  data EnvHalts : Env Γ → Set

  data EnvHalts where

    empty-env : EnvHalts ∗

    val-in-env  : (M : V̲a̲l̲ Γ X) → (γ : Env Γ) → (vH : ValHalts M γ) → (γH : EnvHalts γ) → EnvHalts (γ ﹐ M)

    comp-in-env : (W : Γ ⊢ᶜ X) → (γ : Env Γ) → (cs : CompStack Δ X) → {π : Wk Γ Δ} → {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → CompHalts W γ cs π wk≡
                  → EnvHalts γ
                  → EnvHalts ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡})

  -------------------------

  data TermHalts : {T : LookupState X} → (H : LookupHaltingState T) → Set where

    unit-term-halts : {γ : Env Γ} → TermHalts (found-unit {γ = γ})

    pair-term-halts : {γ : Env Γ} {LHS : V̲a̲l̲ Γ X} {RHS : V̲a̲l̲ Γ Y} → ValHalts (pa̲i̲r̲ LHS RHS) γ → TermHalts (found-pair {LHS = LHS} {RHS = RHS} {γ = γ})

    lam-term-halts  : {γ : Env Γ} {W : (Γ ∙ X) ⊢ᶜ Y} → ValHalts (l̲a̲m̲ W) γ → TermHalts (found-lam {W = W} {γ = γ})

    comp-term-halts : {γ : Env Γ} → {W : Γ ⊢ᶜ X} → {cs : CompStack Δ X} → {π : Wk Γ Δ} → .{wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → CompHalts W γ cs π wk≡ → TermHalts (found-comp {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡})

  ------------------------------

  -- BEGIN WITHOUT HALTING CONDITION

  --- data LookupSteps : LookupState X → Set where

  ---   steps : {S T : LookupState X} → S →ᴸ* T → (H : LookupHaltingState T) → ⟦ S ⟧ᴸ ≡ ⟦ T ⟧ᴸ → (π : Wk (lCtx S) (lTCtx T)) → (⟦ π ⟧ʷ ⟦ lEnv S ⟧ᴱ ≡ ⟦ lTEnv T ⟧ᴱ)
  ---           → LookupSteps S

  --- lookup : (i : Γ ∋ X) → (γ : Env Γ) → LookupSteps {X = X} ⟨ i ∥ γ ⟩
  --- lookup h (γ ﹐ l̲a̲m̲ W) = steps (⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩ ◼) found-lam refl (wk-wk wk-id) refl
  --- lookup h (γ ﹐ pa̲i̲r̲ LHS RHS) = steps (⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩ ◼) found-pair refl (wk-wk wk-id) refl
  --- lookup h (γ ﹐ u̲n̲i̲t̲) = steps (⟨ h ∥ _﹐_ γ (u̲n̲i̲t̲) ⟩ ◼) found-unit refl (wk-wk wk-id) refl
  --- lookup h (γ ﹐ v̲a̲r̲ i) with lookup i γ
  --- ... | steps {T = T} i>>T HT i≡T WK w≡γ = steps (_ →ᴸ⟨ val-h-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ
  --- lookup h ((γ ﹐﹝ W ╎ cs ﹞ ) {π = π} {wk≡ = wk≡}) =
  ---     steps (⟨ h ∥ γ ﹐﹝ W ╎ cs ﹞ ⟩ ◼) found-comp refl (wk-wk wk-id) refl
  --- lookup (t i) (γ ﹐ M) with lookup i γ
  --- ... | steps {T = T} i>>T HT i≡T WK w≡γ = steps (_ →ᴸ⟨ val-t-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ
  --- lookup (t i) (γ ﹐﹝ W ╎ cs ﹞) with lookup i γ
  --- ... | steps {T = T} i>>T HT i≡T WK w≡γ =
  ---     steps (_ →ᴸ⟨ comp-t-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ


  data ValSteps : ValState T◾ → Set where

    steps : {S T : ValState T◾} → S ↠ᵛ T → ValHaltingState T → ⟦ S ⟧ᵛꟴ ≡ ⟦ T ⟧ᵛꟴ → (π : Wk (botCtx T) (botCtx S)) → (⟦ π ⟧ʷ ⟦ botEnv T ⟧ᴱ ≡ ⟦ botEnv S ⟧ᴱ)
            → ValSteps S


  val-eval-rec : (M : Γ' ⊢ᵛ X) → (γ : Env Γ) → (π : Wk Γ Γ') → ValSteps {T◾ = X} (∘ ((⇡ (wk-val π M) ⊲ γ ∷ □) {↥ = 🗆}))

  val-eval-rec {X = `V} (var {A = .`V} i) γ π = steps (_ →ᵛ⟨ ∘var-c ⟩．) (∙ v̲a̲r̲ (wk-mem π i) ⊲ γ ■) refl wk-id refl

  --val-eval-rec {X = `Unit} (var {A = .`Unit} i) γ π with lookup (wk-mem π i) γ
  --... | steps i>>T found-unit i≡T π₁ w≡γ = steps (_ →ᵛ⟨ ∘var i>>T π₁ ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id refl

  val-eval-rec {X = `Unit} (var {A = .`Unit} i) γ π with lookup (wk-mem π i) γ
  ... | steps i>>T found-unit i≡T π₁ w≡γ ext we ϖ =

              steps (_ →ᵛ⟨ ∘var i>>T π₁ ext we ϖ found-unit ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id refl

  val-eval-rec {X = X `× X₁} (var {A = .(X `× X₁)} i) γ π with lookup (wk-mem π i) γ
  ... | steps i>>T (found-pair {LHS = LHS} {RHS = RHS} {γ = γ₁}) i≡T π₁ w≡γ ext we ϖ =

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

  val-eval-rec {X = X `⇒ X₁} (var {A = .(X `⇒ X₁)} i) γ π with lookup (wk-mem π i) γ

  ... | steps i>>T (found-lam {W = W} {γ = γ₁}) i≡T π₁ w≡γ ext we ϖ =

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

  val-eval-rec (lam W) γ π = steps (∘ ⇡ (wk-val π (lam W)) ⊲ γ ∷ □ →ᵛ⟨ ∘lam ⟩．) (∙ l̲a̲m̲ (wk-comp (wk-cong π) W) ⊲ γ ■) refl wk-id refl

  val-eval-rec unit γ π = steps (_ →ᵛ⟨ ∘unit ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id refl

  val-eval-rec (pair {A = X} {B = Y} LHS RHS) γ π with val-eval-rec {X = X} LHS γ π
  ... | steps {T = ∙ (⭭_ {X = X} LT ⊲ γ₁ ∷ □) {↥ = 🗆}} L>T ∙LT L≡T πᴸ wk≡ᴸ with  val-eval-rec {X = Y} RHS γ₁ (wk-trans πᴸ π)
  ...      | steps {T = ∙ (⭭_ {X = Y} RT ⊲ γ₂ ∷ □) {↥ = 🗆}} R>T ∙RT R≡T πᴿ wk≡ᴿ rewrite sym (wk-val-trans RHS πᴸ π) =

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


  val-eval-rec {Γ = Γ} (pm {A = A} {B = B} M N) γ π with val-eval-rec M γ π
  ... | steps {S = S} M>T ∙ pa̲i̲r̲ LHS RHS ⊲ γ₁ ■ M≡T π₁ wk≡₁ with val-eval-rec N (_﹐_ (_﹐_ γ₁ LHS) (wk-v̲a̲l̲ (wk-wk wk-id) RHS)) ((wk-cong (wk-cong (wk-trans π₁ π)))) | (wk-val-trans N (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π)))
  ...    | steps {T = T} N>T ∙T N≡T π₂ wk≡₂ | eq with N>T
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

  val-eval : (M : ε ⊢ᵛ X) → ValSteps {T◾ = X} (∘ ((⇡ wk-val wk-id M ⊲ ∗ ∷ □) {↥ = 🗆}))
  val-eval M = val-eval-rec M ∗ wk-id

  data CompSteps : CompState → Set where

      steps : {S T : CompState} → S →ᶜ* T → CompHaltingState T → .(⟦ S ⟧ᶜꟴ ≡ ⟦ T ⟧ᶜꟴ) → CompSteps S

  wk-comm-explicit : (M : V̲a̲l̲ Γ X) → (π : Wk Δ Γ) → toVal (wk-v̲a̲l̲ π M) ≡ wk-val π (toVal M)
  wk-comm-explicit M π = sym wk-comm
  {-# REWRITE wk-comm-explicit #-}

  {-# TERMINATING #-}
  mutual

    app-eval-rec :   (M : Γ' ⊢ᵛ X `⇒ Y) → (N : V̲a̲l̲ Γ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ Y) → (πₓ : Wk Γ Δ)
                   → .(wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ)
                   → CompSteps ((∙⟨ (a̲pp (wk-val π M) N) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    app-eval-rec (var i) N γ π cs πₓ wk≡₀ with lookup (wk-mem π i) γ
    ... | steps i>>T (found-lam {X = X} {W = W} {γ = γ₁}) i≡T π₁ w≡γ ext we ϖ with comp-eval-rec W (γ ﹐ N) (wk-cong π₁) cs (wk-wk πₓ) wk≡₀
    ... | steps {T = T} W>WT HT S≡T =

                 steps

                    ((∙⟨ a̲pp (wk-val π (var i)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-var i>>T π₁ ⟩ W>WT))

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


    app-eval-rec (lam W) N γ π cs πₓ wk≡₀ with comp-eval-rec W (γ ﹐ N) (wk-cong π) cs (wk-wk πₓ) wk≡₀
    ... | steps {T = T} W>WT HT S≡T =

                  steps

                     ( ∙⟨ a̲pp (wk-val π (lam W)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-lam ⟩ W>WT)

                     HT

                     S≡T

    app-eval-rec (pm M₁ N₁) N γ π cs πₓ wk≡₀ with val-eval-rec M₁ γ π
    ... | steps {T = ∙ (⭭ pa̲i̲r̲ {X = X} {Y = Y} LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ with wk-val-trans N₁ (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
    ...       | eq with
                    app-eval-rec
                      N₁
                      ((wk-v̲a̲l̲ (wk-wk (wk-wk π')) N))
                      (γ₁ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS)
                      (wk-cong (wk-cong (wk-trans π' π)))
                      cs
                      (wk-wk (wk-wk (wk-trans π' πₓ)))
                      (⟦ wk-wk (wk-wk (wk-trans π' πₓ)) ⟧ʷ ⟦ γ₁ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ⟧ᴱ
                       ≡⟨ refl ⟩ ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                       ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                       ≡⟨ wk≡₀ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎)
    ...          | steps {T = T} N>NT NT S≡T rewrite (sym eq) =

                 steps

                    (∙⟨ (a̲pp (wk-val π (pm M₁ N₁)) N) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-pm M>T π' ⟩ N>NT )

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

    comp-eval-rec : (W : Γ' ⊢ᶜ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ X) → (πₓ : Wk Γ Δ)
                  → .(wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ)
                  → CompSteps ((∘⟨ wk-comp π W ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    comp-eval-rec (return {A = X} M) γ π ◻ πₓ wk≡₀ with val-eval-rec {X = X} M γ π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ =

                 steps

                    (∘⟨ wk-comp π (return M) ⊰ γ ╎ ◻ ⟩ →ᶜ⟨ ∘return M>T ⟩ (∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ ◻ ⟩ ◼))

                    ret

                    (cong (λ x → (η x) k₀) M≡T)

    comp-eval-rec (return {A = X} M) γ π ((M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁}) πₓ wk≡₀ with val-eval-rec {X = X} M γ π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ with
                 comp-eval-rec
                   M'
                   (γ₁ ﹐ M₁)
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
                    →ᶜ⟨ ∘return {wk≡ₓ' = ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ
                                         ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                                         ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                                         ≡⟨ wk≡₀ ⟩ ⟦ γ' ⟧ᴱ ∎} M>T ⟩ ((∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ M' ⊲ γ' ⦂⦂ cs ⟩) {wk≡ = ≡-syntax.step-≡-⟩ _≡_ trans (⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                                                                                                                   (≡-syntax.step-≡-⟩ _≡_ trans (⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ))
                                                                                                                    (≡-syntax.step-≡-⟩ _≡_ trans (⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ)
                                                                                                                     ((_≡_ end-syntax.∎) refl ⟦ γ' ⟧ᴱ) wk≡₀)
                                                                                                                    (cong ⟦ πₓ ⟧ʷ wk≡))
                                                                                                                   (sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ))})
                    →ᶜ⟨ ∙return {πₓ = wk-trans (wk-trans π' πₓ) π₁} {πₓ' = π₁} ⟩ M'>T)

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

    comp-eval-rec (pm {A = X} {B = Y} M W) γ π cs πₓ wk≡₀ with val-eval-rec {X = X `× Y} M γ π
    ...  | steps {T = ∙ ((⭭_ {X = X `× Y} (pa̲i̲r̲ LHS RHS) ⊲ γ' ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ with
                    comp-eval-rec
                     W
                     (γ' ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS)
                     (wk-trans (wk-cong (wk-cong π')) (wk-cong (wk-cong π)))
                     cs
                     (wk-wk (wk-wk (wk-trans π' πₓ)))
                     (⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ' ⟧ᴱ
                      ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ' ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ)
                      ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                      ≡⟨ wk≡₀ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎)
    ...   | steps {T = T} W>T HT S≡T with wk-comp-trans W (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
    ...     | eq rewrite (sym eq) =

                steps

                   (∘⟨ wk-comp π (pm M W) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘pm π M>T π' ⟩ W>T)

                   HT

                   ( ⟦ W ⟧ᶜ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , proj₁ (⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))) , proj₂ (⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ cong₂ (λ x y → ⟦ W ⟧ᶜ ((⟦ π ⟧ʷ x , proj₁ y) , proj₂ y) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym wk≡) M≡T ⟩
                     ⟦ W ⟧ᶜ ((⟦ π ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ' ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ' ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ cong (λ x → ⟦ W ⟧ᶜ ((x , ⟦ toVal LHS ⟧ᵛ ⟦ γ' ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ' ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (wk-sem-trans π' π ⟦ γ' ⟧ᴱ) ⟩
                     ⟦ W ⟧ᶜ ((⟦ wk-trans π' π ⟧ʷ ⟦ γ' ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ' ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ' ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ S≡T ⟩
                     ⟦ T ⟧ᶜꟴ ∎)

    comp-eval-rec (push W V) γ π cs πₓ wk≡₀ with comp-eval-rec W γ π (((wk-comp (wk-cong π) V) ⊲ γ ⦂⦂ cs) {wk≡ = wk≡₀}) wk-id refl
    ... | steps {T = ∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ₁ ╎ ◻ ⟩} W>T ret S≡T =

                steps

                  (  ∘⟨ push (wk-comp π W) (wk-comp (wk-cong π) V) ⊰ γ ╎ cs ⟩  →ᶜ⟨ ∘push ⟩ W>T )

                  ret

                  (  ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (λ z → ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀))
                  ≡⟨  cong (⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) (extensionality (λ z → sym (lem0 cs ((⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , z)))))) ⟩
                     ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (λ z → ⟦ cs ⟧ᶜˢ (λ k → ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , z) k) k₀)
                  ≡⟨ refl ⟩
                    (⟦ π ⟧ʷ ； ⟦ W ⟧ᶜ) ⟦ γ ⟧ᴱ ⟦ (wk-comp (wk-cong π) V ⊲ γ ⦂⦂ cs) {π = πₓ} {wk≡ = wk≡₀} ⟧ᴷ
                  ≡⟨ S≡T ⟩
                    (⟦ toVal M ⟧ᵛ ； η) ⟦ γ₁ ⟧ᴱ ⟦ ◻ ⟧ᴷ ∎)

    comp-eval-rec (app M N) γ π cs πₓ wk≡₀ with val-eval-rec N γ π
    ... | steps {T = ∙ ((⭭_ NT ⊲ γᴺ ∷ □) {↥ = 🗆})} N>NT ∙NT N≡NT πᴺ wk≡ᴺ with
                    app-eval-rec
                      M
                      NT
                      γᴺ
                      (wk-trans πᴺ π)
                      cs
                      (wk-trans πᴺ πₓ)
                      (⟦ wk-trans πᴺ πₓ ⟧ʷ ⟦ γᴺ ⟧ᴱ
                       ≡⟨ sym (wk-sem-trans πᴺ πₓ ⟦ γᴺ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ πᴺ ⟧ʷ ⟦ γᴺ ⟧ᴱ)
                       ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ᴺ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                       ≡⟨ wk≡₀ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎)
    ... | steps {T = T} W>WT HT S≡T rewrite (sym (wk-val-trans M πᴺ π)) =

            steps

                ((∘⟨ app (wk-val π M) (wk-val π N) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘app N>NT πᴺ ⟩ W>WT ))

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

    comp-eval-rec (var {A = X} M) γ π cs πₓ wk≡₀ with val-eval-rec {X = `V} M γ π
    ... | steps {T = ∙ ((⭭ v̲a̲r̲ i) ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ with lookup i γ₁
    ... | steps i>>T (found-comp {X = X} {W = W'} {γ = γ'} {cs = cs'} {π = πᶜ} {wk≡ = wk≡c}) i≡T π₂ w≡γ ext we ϖ with
                    comp-eval-rec
                     W'
                     γ'
                     wk-id
                     cs'
                     πᶜ
                     wk≡c
    ... | steps {T = ∙⟨ C̲o̲m̲p.r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₂ ╎ ◻ ⟩} W>T ret S≡T rewrite wk-comp-id W' =

                steps

                  ((∘⟨ var (wk-val π M) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘var M>T π' i>>T π₂ ⟩ W>T))

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

    comp-eval-rec (sub W V) γ π cs πₓ wk≡₀ with comp-eval-rec W ((γ ﹐﹝ wk-comp π V ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡₀}) (wk-cong π) cs (wk-wk πₓ) wk≡₀
    ... | steps {T = T} W>WT HT S≡T =

                steps

                    (∘⟨ sub (wk-comp (wk-cong π) W) (wk-comp π V) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘sub ⟩ W>WT)

                    HT

                    S≡T

    comp-eval : (W : ε ⊢ᶜ R₀) → CompSteps ((∘⟨ wk-comp wk-id W ⊰ ∗ ╎ ◻ ⟩) {π = wk-id} {wk≡ = refl})
    comp-eval W = comp-eval-rec W ∗ wk-id ◻ wk-id refl

  -- END WITHOUT HALTING CONDITION

{- WITH HALTING CONDITION
  data LookupSteps : LookupState X → Set where

    steps : {S T : LookupState X} → (S→T : S →ᴸ* T) → (H : LookupHaltingState T) → ⟦ S ⟧ᴸ ≡ ⟦ T ⟧ᴸ → (π : Wk (lCtx S) (lTCtx T)) → (⟦ π ⟧ʷ ⟦ lEnv S ⟧ᴱ ≡ ⟦ lTEnv T ⟧ᴱ)
            → TermHalts H
            → EnvExt (lookup-index S→T) (lEnv S) (lEnv T)
            → WkExt π
            → EnvEq π (lEnv S) (lTEnv T)
            → LookupSteps S

  lookup : (i : Γ ∋ X) → (γ : Env Γ) → EnvHalts γ → LookupSteps {X = X} ⟨ i ∥ γ ⟩
  lookup Cx.h (γ ﹐ l̲a̲m̲ W) (val-in-env (l̲a̲m̲ W) γ vH γH) = steps (⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩ ◼) (found-lam {W = W} {γ = γ}) refl (wk-wk wk-id) refl (lam-term-halts vH) env-val (wk-ext wk-id (wk-eq wk-id)) (wk-env-val-wk (l̲a̲m̲ W) enveq-id)
  lookup Cx.h (γ ﹐ pa̲i̲r̲ LHS RHS) (val-in-env (pa̲i̲r̲ LHS RHS) γ vH γH) = steps (⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩ ◼) found-pair refl (wk-wk wk-id) refl (pair-term-halts vH) env-val (wk-ext wk-id (wk-eq wk-id)) (wk-env-val-wk (pa̲i̲r̲ LHS RHS) enveq-id)
  lookup h (γ ﹐ u̲n̲i̲t̲) γH = steps (⟨ h ∥ _﹐_ γ (u̲n̲i̲t̲) ⟩ ◼) found-unit refl (wk-wk wk-id) refl unit-term-halts env-val (wk-ext wk-id (wk-eq wk-id)) (wk-env-val-wk u̲n̲i̲t̲ enveq-id)
  lookup Cx.h (γ ﹐ v̲a̲r̲ i) (val-in-env (v̲a̲r̲ i) γ vH γH) with lookup i γ γH
  ... | steps {T = T} i>>T HT i≡T WK w≡γ hT ext we ϖ =
              let
                a0 = li≡i i>>T HT
                a1 = subst (λ x → EnvExt x γ (lEnv T)) (a0) ext
              in
              steps (_ →ᴸ⟨ val-h-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ hT (ext-jmp a1) (wk-ext WK we) (wk-env-val-wk (v̲a̲r̲ i) ϖ)
  lookup Cx.h ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) (comp-in-env W₁ γ₁ cs₁ {wk≡ = wk≡₁} vH γH) =
    steps (⟨ h ∥ γ ﹐﹝ W ╎ cs ﹞ ⟩ ◼) found-comp refl (wk-wk wk-id) refl (comp-term-halts vH) env-comp (wk-ext wk-id (wk-eq wk-id)) (wk-env-comp-wk W cs enveq-id)
  lookup (Cx.t i) (γ ﹐ M) (val-in-env M₁ γ₁ vH γH) with lookup i γ γH
  ... | steps {T = T} i>>T HT i≡T WK w≡γ hT ext we ϖ = steps (_ →ᴸ⟨ val-t-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ hT (ext-val ext) (wk-ext WK we) (wk-env-val-wk M ϖ)
  lookup (Cx.t i) (γ ﹐﹝ W ╎ cs ﹞) (comp-in-env W₁ γ₁ cs₁ {wk≡ = wk≡₁} x γH) with lookup i γ γH
  ... | steps {T = T} i>>T HT i≡T WK w≡γ hT ext we ϖ =
      steps (_ →ᴸ⟨ (comp-t-step) ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ hT (ext-comp ext) (wk-ext WK we) (wk-env-comp-wk W cs ϖ)

  -- val-index : {π : Wk Γ Γ'} → WkExt π → Γ ∋ X
  -- val-index {π = π} (wk-eq π₁) = {!h!}
  -- val-index {π = π} (wk-ext π₁ ext) = {!!}


  data ValSteps : ValState T◾ → Set where

    steps : {S T : ValState T◾} → S ↠ᵛ T → (HT : ValHaltingState T) → ⟦ S ⟧ᵛꟴ ≡ ⟦ T ⟧ᵛꟴ → (π : Wk (botCtx T) (botCtx S)) → (⟦ π ⟧ʷ ⟦ botEnv T ⟧ᴱ ≡ ⟦ botEnv S ⟧ᴱ)
            → EnvHalts (botEnv T) → ValHalts (haltingTerm HT) (botEnv T)
            --→ EnvExt {!!} (botEnv S) (botEnv T)
            → WkExt π
            → EnvEq π (botEnv T) (botEnv S)
            → ValSteps S

  val-eval-rec : (M : Γ' ⊢ᵛ X) → (γ : Env Γ) → (γH : EnvHalts γ) → (π : Wk Γ Γ') → ValSteps {T◾ = X} (∘ ((⇡ (wk-val π M) ⊲ γ ∷ □) {↥ = 🗆}))

  val-eval-rec {X = `V} (var {A = .`V} i) γ γH π = steps (_ →ᵛ⟨ ∘var-c ⟩．) (∙ v̲a̲r̲ (wk-mem π i) ⊲ γ ■) refl wk-id refl γH var-halts (wk-eq wk-id) enveq-id

  val-eval-rec {X = `Unit} (var {A = .`Unit} i) γ γH π with lookup (wk-mem π i) γ γH
  ... | steps i>>T found-unit i≡T π₁ w≡γ γLH ext we ϖ =

              --let
              --  ext' = subst (λ x → EnvExt x γ (_ ﹐ u̲n̲i̲t̲)) (li≡i i>>T found-unit) ext
              --in

              steps (_ →ᵛ⟨ ∘var i>>T π₁ ext we ϖ found-unit ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id refl γH unit-halts (wk-eq wk-id) enveq-id

  val-eval-rec {X = X `× X₁} (var {A = .(X `× X₁)} i) γ γH π with lookup (wk-mem π i) γ γH
  ... | steps i>>T (found-pair {LHS = LHS} {RHS = RHS} {γ = γ₁}) i≡T π₁ w≡γ (pair-term-halts vH) ext we ϖ =

              --let
              --  ext' = subst (λ x → EnvExt x γ (_ ﹐ pa̲i̲r̲ LHS RHS)) (li≡i i>>T found-pair) ext
              --in

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

              γH

              {!!}

              (wk-eq wk-id)

              enveq-id

  val-eval-rec {X = X `⇒ X₁} (var {A = .(X `⇒ X₁)} i) γ γH π with lookup (wk-mem π i) γ γH

  ... | steps i>>T (found-lam {W = W} {γ = γ₁}) i≡T π₁ w≡γ γLH ext we ϖ =

              --let
              --  ext' = subst (λ x → EnvExt x γ (_ ﹐ l̲a̲m̲ W)) (li≡i i>>T found-lam) ext
              --in

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

              γH

              {!!}

              (wk-eq wk-id)

              enveq-id

  val-eval-rec (lam W) γ γH π = steps (∘ ⇡ (wk-val π (lam W)) ⊲ γ ∷ □ →ᵛ⟨ ∘lam ⟩．) (∙ l̲a̲m̲ (wk-comp (wk-cong π) W) ⊲ γ ■) refl wk-id refl γH {!!} (wk-eq wk-id) enveq-id

  val-eval-rec unit γ γH π = steps (_ →ᵛ⟨ ∘unit ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id refl γH unit-halts (wk-eq wk-id) enveq-id

  val-eval-rec (pair {A = X} {B = Y} LHS RHS) γ γH π with val-eval-rec {X = X} LHS γ γH π
  ... | steps {T = ∙ (⭭_ {X = X} LT ⊲ γ₁ ∷ □) {↥ = 🗆}} L>T ∙LT L≡T πᴸ wk≡ᴸ γH₁ tH we₁ ϖ₁ with val-eval-rec {X = Y} RHS γ₁ γH₁ (wk-trans πᴸ π)
  ...      | steps {T = ∙ (⭭_ {X = Y} RT ⊲ γ₂ ∷ □) {↥ = 🗆}} R>T ∙RT R≡T πᴿ wk≡ᴿ γH₂ tH we₂ ϖ₂ rewrite sym (wk-val-trans RHS πᴸ π) =

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

              γH₂

              {!!}

              (wk-ext-trans we₂ we₁)

              (env-eq-trans we₂ we₁ ϖ₂ ϖ₁)

  val-eval-rec {Γ = Γ} (pm {A = A} {B = B} M N) γ γH π with val-eval-rec M γ γH π
  ... | steps {S = S} M>T ∙ pa̲i̲r̲ LHS RHS ⊲ γ₁ ■ M≡T π₁ wk≡₁ γH₁ tH₁ we₁ ϖ₁ with val-eval-rec N (_﹐_ (_﹐_ γ₁ LHS) (wk-v̲a̲l̲ (wk-wk wk-id) RHS)) {!!} ((wk-cong (wk-cong (wk-trans π₁ π)))) | (wk-val-trans N (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π)))
  ...    | steps {T = T} N>T ∙T N≡T π₂ wk≡₂ γH₂ tH₂ we₂ ϖ₂ | eq with N>T
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

          γH₂

          tH₂

          (wk-ext-trans we₂ (wk-ext (wk-wk π₁) (wk-ext π₁ we₁)))

          (env-eq-trans we₂ (wk-ext (wk-wk π₁) (wk-ext π₁ we₁)) ϖ₂ (wk-env-val-wk (wk-v̲a̲l̲ (wk-wk wk-id) RHS) (wk-env-val-wk LHS ϖ₁)))

  val-eval : (M : ε ⊢ᵛ X) → ValSteps {T◾ = X} (∘ ((⇡ wk-val wk-id M ⊲ ∗ ∷ □) {↥ = 🗆}))
  val-eval M = val-eval-rec M ∗ empty-env wk-id

  -------------------------------------------------------------------

  data CompSteps : CompState → Set where

      steps : {S T : CompState} → S →ᶜ* T → CompHaltingState T → .(⟦ S ⟧ᶜꟴ ≡ ⟦ T ⟧ᶜꟴ) → CompSteps S

  {-# TERMINATING #-}
  mutual

    app-eval-rec :   (M : Γ' ⊢ᵛ X `⇒ Y) → (N : V̲a̲l̲ Γ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ Y) → (πₓ : Wk Γ Δ)
                   → .(wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ)
                   → CompSteps ((∙⟨ (a̲pp (wk-val π M) N) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    app-eval-rec (var i) N γ π cs πₓ wk≡₀ with lookup (wk-mem π i) γ {!!}
    ... | steps i>>T (found-lam {X = X} {W = W} {γ = γ₁}) i≡T π₁ w≡γ _ _ _ _ with comp-eval-rec W (γ ﹐ N) (wk-cong π₁) cs (wk-wk πₓ) wk≡₀
    ... | steps {T = T} W>WT HT S≡T =

                 steps

                    ((∙⟨ a̲pp (wk-val π (var i)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-var i>>T π₁ ⟩ W>WT))

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


    app-eval-rec (lam W) N γ π cs πₓ wk≡₀ with comp-eval-rec W (γ ﹐ N) (wk-cong π) cs (wk-wk πₓ) wk≡₀
    ... | steps {T = T} W>WT HT S≡T =

                  steps

                     ( ∙⟨ a̲pp (wk-val π (lam W)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-lam ⟩ W>WT)

                     HT

                     S≡T

    app-eval-rec (pm M₁ N₁) N γ π cs πₓ wk≡₀ with val-eval-rec M₁ γ {!!} π
    ... | steps {T = ∙ (⭭ pa̲i̲r̲ {X = X} {Y = Y} LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ _ _ _ _ with wk-val-trans N₁ (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
    ...       | eq with
                    app-eval-rec
                      N₁
                      ((wk-v̲a̲l̲ (wk-wk (wk-wk π')) N))
                      (γ₁ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS)
                      (wk-cong (wk-cong (wk-trans π' π)))
                      cs
                      (wk-wk (wk-wk (wk-trans π' πₓ)))
                      (⟦ wk-wk (wk-wk (wk-trans π' πₓ)) ⟧ʷ ⟦ γ₁ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ⟧ᴱ
                       ≡⟨ refl ⟩ ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                       ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                       ≡⟨ wk≡₀ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎)
    ...          | steps {T = T} N>NT NT S≡T rewrite (sym eq) =

                 steps

                    (∙⟨ (a̲pp (wk-val π (pm M₁ N₁)) N) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-pm M>T π' ⟩ N>NT )

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

    comp-eval-rec : (W : Γ' ⊢ᶜ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ X) → (πₓ : Wk Γ Δ)
                  → .(wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ)
                  → CompSteps ((∘⟨ wk-comp π W ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    comp-eval-rec (return {A = X} M) γ π ◻ πₓ wk≡₀ with val-eval-rec {X = X} M γ {!!} π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ _ _ _ _ =

                 steps

                    (∘⟨ wk-comp π (return M) ⊰ γ ╎ ◻ ⟩ →ᶜ⟨ ∘return M>T ⟩ (∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ ◻ ⟩ ◼))

                    ret

                    (cong (λ x → (η x) k₀) M≡T)

    comp-eval-rec (return {A = X} M) γ π ((M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁}) πₓ wk≡₀ with val-eval-rec {X = X} M γ {!!} π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ _ _ _ _ with
                 comp-eval-rec
                   M'
                   (γ₁ ﹐ M₁)
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
                    →ᶜ⟨ ∘return {wk≡ₓ' = ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ
                                         ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                                         ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                                         ≡⟨ wk≡₀ ⟩ ⟦ γ' ⟧ᴱ ∎} M>T ⟩ ((∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ M' ⊲ γ' ⦂⦂ cs ⟩) {wk≡ = ≡-syntax.step-≡-⟩ _≡_ trans (⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                                                                                                                   (≡-syntax.step-≡-⟩ _≡_ trans (⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ))
                                                                                                                    (≡-syntax.step-≡-⟩ _≡_ trans (⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ)
                                                                                                                     ((_≡_ end-syntax.∎) refl ⟦ γ' ⟧ᴱ) wk≡₀)
                                                                                                                    (cong ⟦ πₓ ⟧ʷ wk≡))
                                                                                                                   (sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ))})
                    →ᶜ⟨ ∙return {πₓ = wk-trans (wk-trans π' πₓ) π₁} {πₓ' = π₁} ⟩ M'>T)

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

    comp-eval-rec (pm {A = X} {B = Y} M W) γ π cs πₓ wk≡₀ with val-eval-rec {X = X `× Y} M γ {!!} π
    ...  | steps {T = ∙ ((⭭_ {X = X `× Y} (pa̲i̲r̲ LHS RHS) ⊲ γ' ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ _ _ _ _ with
                    comp-eval-rec
                     W
                     (γ' ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS)
                     (wk-trans (wk-cong (wk-cong π')) (wk-cong (wk-cong π)))
                     cs
                     (wk-wk (wk-wk (wk-trans π' πₓ)))
                     (⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ' ⟧ᴱ
                      ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ' ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ)
                      ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                      ≡⟨ wk≡₀ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎)
    ...   | steps {T = T} W>T HT S≡T with wk-comp-trans W (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
    ...     | eq rewrite (sym eq) =

                steps

                   (∘⟨ wk-comp π (pm M W) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘pm π M>T π' ⟩ W>T)

                   HT

                   ( ⟦ W ⟧ᶜ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , proj₁ (⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))) , proj₂ (⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ cong₂ (λ x y → ⟦ W ⟧ᶜ ((⟦ π ⟧ʷ x , proj₁ y) , proj₂ y) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym wk≡) M≡T ⟩
                     ⟦ W ⟧ᶜ ((⟦ π ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ' ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ' ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ cong (λ x → ⟦ W ⟧ᶜ ((x , ⟦ toVal LHS ⟧ᵛ ⟦ γ' ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ' ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (wk-sem-trans π' π ⟦ γ' ⟧ᴱ) ⟩
                     ⟦ W ⟧ᶜ ((⟦ wk-trans π' π ⟧ʷ ⟦ γ' ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ' ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ' ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ S≡T ⟩
                     ⟦ T ⟧ᶜꟴ ∎)

    comp-eval-rec (push W V) γ π cs πₓ wk≡₀ with comp-eval-rec W γ π (((wk-comp (wk-cong π) V) ⊲ γ ⦂⦂ cs) {wk≡ = wk≡₀}) wk-id refl
    ... | steps {T = ∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ₁ ╎ ◻ ⟩} W>T ret S≡T =

                steps

                  (  ∘⟨ push (wk-comp π W) (wk-comp (wk-cong π) V) ⊰ γ ╎ cs ⟩  →ᶜ⟨ ∘push ⟩ W>T )

                  ret

                  (  ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (λ z → ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀))
                  ≡⟨  cong (⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) (extensionality (λ z → sym (lem0 cs ((⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , z)))))) ⟩
                     ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (λ z → ⟦ cs ⟧ᶜˢ (λ k → ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , z) k) k₀)
                  ≡⟨ refl ⟩
                    (⟦ π ⟧ʷ ； ⟦ W ⟧ᶜ) ⟦ γ ⟧ᴱ ⟦ (wk-comp (wk-cong π) V ⊲ γ ⦂⦂ cs) {π = πₓ} {wk≡ = wk≡₀} ⟧ᴷ
                  ≡⟨ S≡T ⟩
                    (⟦ toVal M ⟧ᵛ ； η) ⟦ γ₁ ⟧ᴱ ⟦ ◻ ⟧ᴷ ∎)

    comp-eval-rec (app M N) γ π cs πₓ wk≡₀ with val-eval-rec N γ {!!} π
    ... | steps {T = ∙ ((⭭_ NT ⊲ γᴺ ∷ □) {↥ = 🗆})} N>NT ∙NT N≡NT πᴺ wk≡ᴺ _ _ _ _ with
                    app-eval-rec
                      M
                      NT
                      γᴺ
                      (wk-trans πᴺ π)
                      cs
                      (wk-trans πᴺ πₓ)
                      (⟦ wk-trans πᴺ πₓ ⟧ʷ ⟦ γᴺ ⟧ᴱ
                       ≡⟨ sym (wk-sem-trans πᴺ πₓ ⟦ γᴺ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ πᴺ ⟧ʷ ⟦ γᴺ ⟧ᴱ)
                       ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ᴺ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                       ≡⟨ wk≡₀ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎)
    ... | steps {T = T} W>WT HT S≡T rewrite (sym (wk-val-trans M πᴺ π)) =

            steps

                ((∘⟨ app (wk-val π M) (wk-val π N) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘app N>NT πᴺ ⟩ W>WT ))

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

    comp-eval-rec (var {A = X} M) γ π cs πₓ wk≡₀ with val-eval-rec {X = `V} M γ {!!} π
    ... | steps {T = ∙ ((⭭ v̲a̲r̲ i) ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ _ _ _ _ with lookup i γ₁ {!!}
    ... | steps i>>T (found-comp {X = X} {W = W'} {γ = γ'} {cs = cs'} {π = πᶜ} {wk≡ = wk≡c}) i≡T π₂ w≡γ _ _ _ _ with
                    comp-eval-rec
                     W'
                     γ'
                     wk-id
                     cs'
                     πᶜ
                     wk≡c
    ... | steps {T = ∙⟨ C̲o̲m̲p.r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₂ ╎ ◻ ⟩} W>T ret S≡T rewrite wk-comp-id W' =

                steps

                  ((∘⟨ var (wk-val π M) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘var M>T π' i>>T π₂ ⟩ W>T))

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

    comp-eval-rec (sub W V) γ π cs πₓ wk≡₀ with comp-eval-rec W ((γ ﹐﹝ wk-comp π V ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡₀}) (wk-cong π) cs (wk-wk πₓ) wk≡₀
    ... | steps {T = T} W>WT HT S≡T =

                steps

                    (∘⟨ sub (wk-comp (wk-cong π) W) (wk-comp π V) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘sub ⟩ W>WT)

                    HT

                    S≡T

    comp-eval : (W : ε ⊢ᶜ R₀) → CompSteps ((∘⟨ wk-comp wk-id W ⊰ ∗ ╎ ◻ ⟩) {π = wk-id} {wk≡ = refl})
    comp-eval W = comp-eval-rec W ∗ wk-id ◻ wk-id refl

    -- END WITH HALTING CONDITION -}


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
