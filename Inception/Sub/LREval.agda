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
open import Data.List.NonEmpty.Base using (List⁺; _∷_; toList)

open import Inception.Sub.Equality
open import Inception.Sub.Environments R
open import Inception.Sub.States R
open import Inception.Sub.Machine R

-- open import Level using (0ℓ)
-- open import Relation.Binary.Core using (Rel)

open import Inception.Sub.Arithmetic

module EvalMain {R₀ : Ty} (k₀ : ⟦ R₀ ⟧ → R) where

  open StatesMain {R₀ = R₀} k₀
  open MachineMain {R₀ = R₀} k₀
  open EnvMain {R₀ = R₀} k₀

  -------------------------------------------------------------------

  {- without halting condition
  data LookupSteps : LookupState X → Set where

    steps : {S T : LookupState X} → (S→T : S →ᴸ* T) → (H : LookupHaltingState T) → ⟦ S ⟧ᴸ ≡ ⟦ T ⟧ᴸ → (π : Wk (lCtx S) (lTCtx T)) → (⟦ π ⟧ʷ ⟦ lEnv S ⟧ᴱ ≡ ⟦ lTEnv T ⟧ᴱ)
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


  data EnvWk : (π : Wk Γ Γ') → Env Γ → Env Γ' → Set where

      ⟨_⟩     :  {π : Wk Γ Γ} → (γ : Env Γ) → EnvWk π γ γ

      _﹐_     :  {π : Wk Γ Γ'} → {γ : Env Γ} → {γ' : Env Γ'} → EnvWk π γ γ' → (M : V̲a̲l̲ Γ X) → EnvWk (wk-wk {A = X} π) (γ ﹐ M) γ'


  -------------------------------------------------------------------

  data CompSteps : CompState → Set where

      steps : {S T : CompState} → S →ᶜ* T → CompHaltingState T → (⟦ S ⟧ᶜꟴ ≡ ⟦ T ⟧ᶜꟴ) → CompSteps S

  get-csteps : {S : CompState} → CompSteps S → Σ[ T ∈ CompState ] ((CompHaltingState T) × (S →ᶜ* T) × (⟦ S ⟧ᶜꟴ ≡ ⟦ T ⟧ᶜꟴ))
  get-csteps {S = S} (steps {T = T} S→T H eq) = T , H , S→T , eq

  wk-comm-explicit : (M : V̲a̲l̲ Γ X) → (π : Wk Δ Γ) → toVal (wk-v̲a̲l̲ π M) ≡ wk-val π (toVal M)
  wk-comm-explicit M π = sym wk-comm
  {-# REWRITE wk-comm-explicit #-}


  record CStateHalts (c : CompState) : Set where
    field
      target-state : CompState
      target-is-halting : CompHaltingState target-state
      trace : c →ᶜ* target-state
      result-eq : ⟦ c ⟧ᶜꟴ ≡ ⟦ target-state ⟧ᶜꟴ

  -- ∘C↑ : {Γ' : Ctx} {Z : Ty} → ((W : Γ' ⊢ᶜ Z) → Set) → (Δ : Ctx) → (Γ : Ctx) → (γ : Env Γ) → (cs : CompStack Δ Z) → (π : Wk Γ Δ) → (π' : Wk Γ Γ') → (wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → Set
  -- ∘C↑ {Γ' = Γ'} {Z = Z} P Γ Δ γ cs π π' wk≡ = ∀ {W : Γ' ⊢ᶜ Z} → P W → CStateHalts (((∘⟨ wk-comp π' W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡}))

  -- ∘C↓ : {Γ' : Ctx} {Z : Ty} → ((Δ : Ctx) → (Γ : Ctx) → (γ : Env Γ) → (cs : CompStack Δ Z) → (π : Wk Γ Δ) → (π' : Wk Γ Γ') → (wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → Set) → (W : Γ' ⊢ᶜ Z) → Set
  -- ∘C↓ {Γ' = Γ'} {Z = Z} Q W = ∀ (Δ : Ctx) → (Γ : Ctx) → (γ : Env Γ) → (cs : CompStack Δ Z) → (π : Wk Γ Δ) → (π' : Wk Γ Γ') → (wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → Q Δ Γ γ cs π π' wk≡ → CStateHalts ((∘⟨ wk-comp π' W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡})


  -- ∘C↓ : {Γ' : Ctx} {Z : Ty} → ((Δ : Ctx) → (Γ : Ctx) → (γ : Env Γ) → (cs : CompStack Δ Z) → (π : Wk Γ Δ) → (π' : Wk Γ Γ') → (wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → Set) → (W : Γ' ⊢ᶜ Z) → Set
  -- ∘C↓ {Γ' = Γ'} {Z = Z} Q W = ∀ (Δ : Ctx) → (Γ : Ctx) → (γ : Env Γ) → (cs : CompStack Δ Z) → (π : Wk Γ Δ) → (π' : Wk Γ Γ') → (wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → Q Δ Γ γ cs π π' wk≡ → CStateHalts ((∘⟨ wk-comp π' W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡})

  ∣_∣ : Wk Γ Γ' → ℕ
  ∣ wk-ε ∣ = 0
  ∣ wk-cong π ∣ = ∣ π ∣
  ∣ wk-wk π ∣ = suc ∣ π ∣

  wk-id-lemma : ∣ wk-id {Γ = Γ} ∣ ≡ 0
  wk-id-lemma {Γ = Cx.ε} = refl
  wk-id-lemma {Γ = Γ Cx.∙ x} = wk-id-lemma {Γ = Γ}

  wk-trans-lemma : (π : Wk Γ (Δ ∙ X)) → suc ∣ π ∣ ≡ ∣ wk-trans π (wk-wk wk-id) ∣
  wk-trans-lemma (wk-cong π) = cong suc (subst (λ x → ∣ π ∣ ≡ ∣ x ∣) (sym (wk-trans-id' {π = π})) refl)
  wk-trans-lemma (wk-wk π) = cong suc (wk-trans-lemma π)

  wk-lemma : (π π' : Wk Γ Δ) → ∣ π ∣ ≡ ∣ π' ∣
  wk-lemma wk-ε wk-ε = refl
  wk-lemma (wk-cong π) (wk-cong π') = wk-lemma π π'
  wk-lemma (wk-cong π) (wk-wk π') =
    let
      IH = wk-lemma π (wk-trans π' (wk-wk wk-id))
    in
    trans IH (sym (wk-trans-lemma π'))
  wk-lemma (wk-wk π) (wk-cong π') =
    let
      IH = wk-lemma (wk-trans π (wk-wk wk-id)) π'
    in
    trans (wk-trans-lemma π) IH
  wk-lemma (wk-wk π) (wk-wk π') = cong suc (wk-lemma π π')

  {-
  wkext-lemma : {Γ Δ Γ' : Ctx} → (π : Wk Γ Γ') → (π₁ : Wk Γ Δ) → (π₂ : Wk Δ Γ') → (ext : WkExt π) → (ext₁ : WkExt π₁) → (ext₂ : WkExt π₂) → (∣ π₁ ∣ ≤ ∣ π ∣)
  wkext-lemma π π₁ π₂ (wk-eq π₃) (wk-eq π₄) (wk-eq π₅) rewrite wk-id-id {π = π} | wk-id-id {π = π₁} = ≤-refl
  wkext-lemma π π₁ π₂ (wk-eq π₃) (wk-eq π₄) (wk-ext π₅ ext₂) rewrite wk-id-id {π = π} | wk-id-id {π = π₁} = ≤-refl
  wkext-lemma π π₁ π₂ (wk-eq π₃) (wk-ext π₄ ext₁) (wk-eq π₅) = ql (wk-absurd (wk-wk π₄) π₄) _
  wkext-lemma π π₁ π₂ (wk-eq π₃) (wk-ext π₄ ext₁) (wk-ext π₅ ext₂) = ql (wk-absurd (wk-wk π₅) π₄) _
  wkext-lemma π π₁ π₂ (wk-ext π₃ ext) (wk-eq π₄) (wk-eq π₅) = ql (wk-absurd (wk-wk π₃) π₃) _
  wkext-lemma π (wk-cong π₁) π₂ (wk-ext π₃ ext) (wk-eq π₄) (wk-ext π₅ ext₂) = let IH = wkext-lemma π₃ π₁ π₃ ext (WkExt.wk-eq π₁) ext in n≤sm IH
  wkext-lemma π (wk-wk π₁) π₂ (wk-ext π₃ ext) (wk-eq π₄) (wk-ext π₅ ext₂) = ql (wk-absurd (wk-wk π₁) π₁) _
  wkext-lemma π π₁ π₂ (wk-ext π₃ ext) (wk-ext π₄ ext₁) (wk-eq π₅) = let IH = (wkext-lemma π₃ π₄ π₂ ext ext₁ (WkExt.wk-eq π₂)) in s≤s IH
  wkext-lemma π π₁ π₂ (wk-ext π₃ ext) (wk-ext π₄ ext₁) (wk-ext π₅ ext₂) = let IH = (wkext-lemma π₃ π₄ π₂ ext ext₁ (WkExt.wk-ext π₅ ext₂)) in s≤s IH
  -}

  wk-trans-lemma₁ : (π₁ : Wk Γ Γ') → (π₂ : Wk Γ' Γ'') → ∣ π₁ ∣ ≤ ∣ wk-trans π₁ π₂ ∣
  wk-trans-lemma₁ wk-ε wk-ε = z≤n
  wk-trans-lemma₁ (wk-cong π₁) (wk-cong π₂) = wk-trans-lemma₁ π₁ π₂
  wk-trans-lemma₁ (wk-cong π₁) (wk-wk π₂) = n≤sm (wk-trans-lemma₁ π₁ π₂)
  wk-trans-lemma₁ (wk-wk π₁) wk-ε = s≤s (wk-trans-lemma₁ π₁ wk-ε)
  wk-trans-lemma₁ (wk-wk π₁) (wk-cong π₂) = s≤s (wk-trans-lemma₁ π₁ (wk-cong π₂))
  wk-trans-lemma₁ (wk-wk π₁) (wk-wk π₂) = s≤s (wk-trans-lemma₁ π₁ (wk-wk π₂))

  n-lemma : {Γ Δ Γ' : Ctx} → (π : Wk Γ Γ') → (π₁ : Wk Γ Δ) → (π₂ : Wk Δ Γ') → (∣ π₁ ∣ ≤ ∣ π ∣)
  n-lemma π π₁ π₂ rewrite wk-lemma π (wk-trans π₁ π₂) = wk-trans-lemma₁ π₁ π₂

  wk-trans-lemma-eq : (π₁ : Wk Γ Γ') → (π₂ : Wk Γ' Γ'') → ∣ π₁ ∣ + ∣ π₂ ∣ ≡ ∣ wk-trans π₁ π₂ ∣
  wk-trans-lemma-eq wk-ε wk-ε = refl
  wk-trans-lemma-eq (wk-cong π₁) (wk-cong π₂) = wk-trans-lemma-eq π₁ π₂
  wk-trans-lemma-eq (wk-cong π₁) (wk-wk π₂) rewrite sym (snm {n = ∣ π₁ ∣} {m = ∣ π₂ ∣}) = cong suc (wk-trans-lemma-eq π₁ π₂)
  wk-trans-lemma-eq (wk-wk π₁) wk-ε = cong suc (wk-trans-lemma-eq π₁ wk-ε)
  wk-trans-lemma-eq (wk-wk π₁) (wk-cong π₂) = cong suc (wk-trans-lemma-eq π₁ (wk-cong π₂))
  wk-trans-lemma-eq (wk-wk π₁) (wk-wk π₂) = cong suc (wk-trans-lemma-eq π₁ (wk-wk π₂))

  wk-suc-eq : (π : Wk Γ Γ') → (π' : Wk Γ (Γ' ∙ X)) → ∣ π ∣ ≡ suc ∣ π' ∣
  wk-suc-eq {Γ = Γ} {Γ' = Γ'} π π' =
    let
      a1 = wk-trans-lemma-eq π' (wk-wk wk-id)
      a2 : suc (∣ π' ∣ + ∣ wk-id {Γ = Γ'} ∣) ≡ ∣ wk-trans π' (wk-wk wk-id) ∣
      a2 = trans (snm {n = ∣ π' ∣} {m = ∣ wk-id {Γ = Γ'} ∣}) a1
      a3 : ∣ wk-id {Γ = Γ'} ∣ + ∣ π' ∣ ≡ ∣ π' ∣
      a3 = subst (λ x → x + ∣ π' ∣ ≡ ∣ π' ∣) (sym (wk-id-lemma {Γ = Γ'})) refl
      a4 : ∣ π' ∣ + ∣ wk-id {Γ = Γ'} ∣ ≡ ∣ π' ∣
      a4 = trans (+-comm {n = ∣ π' ∣} {m = ∣ wk-id {Γ = Γ'} ∣}) a3
      a5 : suc ∣ π' ∣ ≡ ∣ wk-trans π' (wk-wk wk-id) ∣
      a5 = subst (λ x → suc x ≡ ∣ wk-trans π' (wk-wk wk-id) ∣) a4 a2
      a6 : ∣ wk-trans π' (wk-wk wk-id) ∣ ≡ ∣ π ∣
      a6 = wk-lemma (wk-trans π' (wk-wk wk-id)) π
    in
    sym (trans a5 a6)

  vh-lemma : (π : Wk Γ (Γ' ∙ A)) → (eq : n ≡ ∣ π ∣) → suc n ≡ ∣ wk-trans π (wk-wk {A = A} (wk-id {Γ = Γ'})) ∣
  vh-lemma {n = n} π eq rewrite eq = wk-trans-lemma π

  {- TODO: fix
  CompHalts : (W : Comp Γ Z) → (γ : Env Γ) → Set
  CompHalts {Γ = Γ} {Z = Z} W γ = ∀ (Δ : Ctx) → (cs : CompStack Δ Z) → (π : Wk Γ Δ) → (wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → CStateHalts ((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡})
  -}

  {- biorthogonality experiments
  --V↑ : {Γ : Ctx} {X : Ty} → ((M : V̲a̲l̲ Γ X) → Set) → (Δ : Ctx) → (Γ' : Ctx) → (Y : Ty) → (W : Comp (Γ' ∙ X) Y) → (γ : Env Γ) → (cs : CompStack Δ Y) → (π : Wk Γ Δ) → (π' : Wk Γ Γ') → (wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → Set
  --V↑ {Γ = Γ} {X = X} P Δ Γ' Y W γ cs π π' wk≡ = ∀ {M : V̲a̲l̲ Γ X} → P M → CStateHalts (((∙⟨ a̲pp (wk-val π' (lam W)) M ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡}))

  V↑ : {Γ : Ctx} {X : Ty} → (γ : Env Γ) → ((M : V̲a̲l̲ Γ X) → Set) → (Δ : Ctx) → (Γ' : Ctx) → (γ' : Env Γ') → (cs : CompStack Δ X) → (π' : Wk Γ' Δ) → (π : Wk Γ' Γ) → (ϖ : EnvEq π ) → (wk≡ : ⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → Set
  V↑ {Γ = Γ} {X = X} P Δ Γ' γ' cs π' π wk≡ = ∀ {M : V̲a̲l̲ Γ X} → P M → CStateHalts (((∙⟨ wk-c̲o̲m̲p π (r̲e̲t̲u̲r̲n̲ M) ⊰ γ' ╎ cs ⟩) {π = π'} {wk≡ = wk≡}))

  --V↓ : {Γ : Ctx} {X : Ty} → ((Δ : Ctx) → (Γ' : Ctx) → (Y : Ty) → (W : Comp (Γ' ∙ X) Y) → (γ : Env Γ) → (cs : CompStack Δ Y) → (π : Wk Γ Δ) → (π' : Wk Γ Γ') → (wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → Set) → (M : V̲a̲l̲ Γ X) → Set
  --V↓ {Γ = Γ} {X = X} Q M = ∀ (Δ : Ctx) → (Γ' : Ctx) → (Y : Ty) → (W : Comp (Γ' ∙ X) Y) → (γ : Env Γ) → (cs : CompStack Δ Y) → (π : Wk Γ Δ) → (π' : Wk Γ Γ') → (wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → CStateHalts (((∙⟨ a̲pp (wk-val π' (lam W)) M ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡}))

  V↓ : {Γ : Ctx} {X : Ty} → ((Δ : Ctx) → (Γ' : Ctx) → (γ' : Env Γ') → (cs : CompStack Δ X) → (π' : Wk Γ' Δ) → (π : Wk Γ' Γ) → (wk≡ : ⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → Set) → (W : Comp Γ X) → Set
  V↓ {Γ = Γ} {X = X} Q W = ∀ (Δ : Ctx) → (Γ' : Ctx) → (γ' : Env Γ') → (cs : CompStack Δ X) → (π' : Wk Γ' Δ) → (π : Wk Γ' Γ) → (wk≡ : ⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → (Q Δ Γ' γ' cs π' π wk≡) → CStateHalts (((∙⟨ {!!} ⊰ γ' ╎ cs ⟩) {π = π'} {wk≡ = wk≡}))

  V̲a̲l̲Halts : (M : V̲a̲l̲ Γ' Z) → (γ' : Env Γ') → Set
  V̲a̲l̲Halts {Γ' = Γ'} (l̲a̲m̲ {X = X} {Y = Y} W) γ' = ∀ (Γ : Ctx) → (γ : Env Γ) → (π : Wk Γ Γ') → (ϖ : EnvEq π γ γ') → (M : V̲a̲l̲ Γ X) → {!!} → CompHalts (wk-comp (wk-cong π) W) (γ ﹐ M)
  V̲a̲l̲Halts {Γ' = Γ'} (pa̲i̲r̲ M₁ M₂) γ' = V̲a̲l̲Halts M₁ γ' × V̲a̲l̲Halts M₂ γ'
  V̲a̲l̲Halts {Γ' = Γ'} u̲n̲i̲t̲ γ' = {Γ : Ctx} → (γ : Env Γ) → (π' : Wk Γ Γ') → ⊤
  V̲a̲l̲Halts {Γ' = Γ'} (v̲a̲r̲ i) γ' = {!!}

  END biorthogonality experiments -}

  {- valhalts (using max)
  V̲a̲l̲Halts : {Γ Γ' : Ctx} → (M : V̲a̲l̲ Γ' Z) → (γ' : Env Γ') → (n : ℕ) → (π : Wk Γ Γ') → (m : ℕ) → (n ≡ m + ∣ π ∣) → Set
  V̲a̲l̲Halts {Γ = Γ} {Γ' = Γ'} (l̲a̲m̲ {X = X} {Y = Y} W) γ' zero π zero eq = ⊤
  V̲a̲l̲Halts {Γ = Γ} {Γ' = Γ'} (l̲a̲m̲ {X = X} {Y = Y} W) γ' zero π (suc m) ()
  V̲a̲l̲Halts {Γ = Γ} {Γ' = Γ'} (l̲a̲m̲ {X = X} {Y = Y} W) γ' (suc n) π zero eq =
    ∀ (Δ : Ctx) → (δ : Env Δ) → (π'' : Wk Γ (Δ ∙ X)) → (π' : Wk (Δ ∙ X) (Γ' ∙ X)) → (M : V̲a̲l̲ Δ X)
      → V̲a̲l̲Halts {Γ = Γ} (wk-v̲a̲l̲ (wk-wk wk-id) M) (δ ﹐ M) n π'' ∣ π' ∣
                     (let
                        a4 = wk-suc-eq π (wk-trans π'' π')
                        a5 = trans eq a4
                        a6 : n ≡ ∣ wk-trans π'' π' ∣
                        a6 = p-eq-p a5
                        a7 = wk-trans-lemma-eq π'' π'
                        a8 = sym (+-comm {n = ∣ π'' ∣} {m = ∣ π' ∣})
                        a9 = trans a6 (sym (trans a8 a7))
                      in a9)
      → CompHalts (wk-comp π' W) (δ ﹐ M)
  V̲a̲l̲Halts {Γ = Γ} {Γ' = Γ'} (l̲a̲m̲ {X = X} {Y = Y} W) γ' (suc n) π (suc m) refl = V̲a̲l̲Halts {Γ = Γ} {Γ' = Γ'} (l̲a̲m̲ {X = X} {Y = Y} W) γ' n π m refl
  V̲a̲l̲Halts {Γ = Γ} {Γ' = Γ'} (pa̲i̲r̲ M₁ M₂) γ' n π m eq = V̲a̲l̲Halts M₁ γ' n π m eq × V̲a̲l̲Halts M₂ γ' n π m eq
  V̲a̲l̲Halts {Γ' = Γ'} u̲n̲i̲t̲ _ _ _ _ _ = ⊤

  V̲a̲l̲Halts {Γ = Γ} {Γ' = Γ'} (v̲a̲r̲ Cx.h) (γ' ﹐ (v̲a̲r̲ i)) n π zero eq =  V̲a̲l̲Halts {Γ = Γ} (v̲a̲r̲ i) γ' (suc n) (wk-trans π (wk-wk wk-id)) 0 (vh-lemma π eq)
  V̲a̲l̲Halts {Γ = Γ} {Γ' = Γ'} (v̲a̲r̲ Cx.h) (γ' ﹐ (v̲a̲r̲ i)) (suc n) π (suc m) eq = V̲a̲l̲Halts {Γ = Γ} {Γ' = Γ'} (v̲a̲r̲ Cx.h) (γ' ﹐ (v̲a̲r̲ i)) n π m (p-eq-p eq)
  V̲a̲l̲Halts {Γ = Γ} {Γ' = Γ'} (v̲a̲r̲ Cx.h) ((γ' ﹐﹝ W ╎ cs ﹞) {π = π'} {wk≡ = wk≡}) n π zero eq = CStateHalts (((∘⟨ W ⊰ γ' ╎ cs ⟩) {π = π'} {wk≡ = wk≡}))
  V̲a̲l̲Halts {Γ = Γ} {Γ' = Γ'} (v̲a̲r̲ Cx.h) ((γ' ﹐﹝ W ╎ cs ﹞) {π = π'} {wk≡ = wk≡}) (suc n) π (suc m) eq = V̲a̲l̲Halts {Γ = Γ} {Γ' = Γ'} (v̲a̲r̲ Cx.h) ((γ' ﹐﹝ W ╎ cs ﹞) {π = π'} {wk≡ = wk≡}) n π m (p-eq-p eq)
  V̲a̲l̲Halts {Γ = Γ} {Γ' = Γ'} (v̲a̲r̲ (Cx.t i)) (γ' ﹐ M) n π zero eq = V̲a̲l̲Halts {Γ = Γ} (v̲a̲r̲ i) γ' (suc n) (wk-trans π (wk-wk wk-id)) 0 (vh-lemma π eq)
  V̲a̲l̲Halts {Γ = Γ} {Γ' = Γ'} (v̲a̲r̲ (Cx.t i)) (γ' ﹐ M) (suc n) π (suc m) eq = V̲a̲l̲Halts {Γ = Γ} {Γ' = Γ'} (v̲a̲r̲ (t i)) (γ' ﹐ M) n π m (p-eq-p eq)
  V̲a̲l̲Halts {Γ = Γ} {Γ' = Γ'} (v̲a̲r̲ (Cx.t i)) ((γ' ﹐﹝ W ╎ cs ﹞) {π = π'} {wk≡ = wk≡}) n π zero eq = V̲a̲l̲Halts {Γ = Γ} (v̲a̲r̲ i) γ' (suc n) (wk-trans π (wk-wk wk-id)) 0 (vh-lemma π eq)
  V̲a̲l̲Halts {Γ = Γ} {Γ' = Γ'} (v̲a̲r̲ (Cx.t i)) ((γ' ﹐﹝ W ╎ cs ﹞) {π = π'} {wk≡ = wk≡}) (suc n) π (suc m) eq = V̲a̲l̲Halts {Γ = Γ} {Γ' = Γ'} (v̲a̲r̲ (Cx.t i)) ((γ' ﹐﹝ W ╎ cs ﹞) {π = π'} {wk≡ = wk≡}) n π m (p-eq-p eq)

  END valhalts (using max) -}

  {-
  data CompStackHalts : CompStack Δ X → Set where

    empty : CompStackHalts ◻

    cons :    (W : Comp (Γ ∙ Z) X) → (γ : Env Γ) → (cs : CompStack Δ X) → (π : Wk Γ Δ) → (wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ)
            → ((Γ' : Ctx) → (γ' : Env Γ') → (π' : Wk (Γ' ∙ Z) Δ) → (π'' : Wk Γ' Γ) → (M : V̲a̲l̲ Γ' Z) → (wk≡' : ⟦ π' ⟧ʷ ⟦ γ' ﹐ M ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → CStateHalts ((∘⟨ wk-comp (wk-cong π'') W ⊰ γ' ﹐ M ╎ cs ⟩) {π = π'} {wk≡ = wk≡'}) )
            → CompStackHalts ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡})
  -}

  {-
  TermHalts : {T : LookupState X} → (H : LookupHaltingState T) → Set
  TermHalts found-unit = ⊤
  TermHalts (found-pair {LHS = LHS} {RHS = RHS} {γ = γ}) = V̲a̲l̲Halts LHS γ × V̲a̲l̲Halts RHS γ
  TermHalts (found-lam {W = W} {γ = γ}) = V̲a̲l̲Halts (l̲a̲m̲ W) γ --(∘C↓ (∘C↑ CompHalts)) W
  TermHalts (found-comp {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡}) = CStateHalts (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡}))
  -}

  LabelHalts : (M : V̲a̲l̲ Γ Z) → (γ : Env Γ) → Set
  LabelHalts (l̲a̲m̲ W) γ = ⊤
  LabelHalts (pa̲i̲r̲ M₁ M₂) γ = LabelHalts M₁ γ × LabelHalts M₂ γ
  LabelHalts u̲n̲i̲t̲ γ = ⊤
  LabelHalts (v̲a̲r̲ Cx.h) (γ ﹐ v̲a̲r̲ i) = LabelHalts (v̲a̲r̲ i) γ

  --LabelHalts (v̲a̲r̲ Cx.h) ((γ' ﹐﹝ W ╎ cs ﹞) {π = π'} {wk≡ = wk≡}) = CStateHalts (((∘⟨ W ⊰ γ' ╎ cs ⟩) {π = π'} {wk≡ = wk≡}))
  --LabelHalts {Γ = Γ ∙ `V} (v̲a̲r̲ Cx.h) (_﹐﹝_╎_﹞ {Δ = Δ} γ W cs {π = π} {wk≡ = wk≡}) =
  --  (Γ' : Ctx) → (γ' : Env Γ') → (π' : Wk Γ' Γ) → (ext' : WkExt π') → (π'' : Wk Γ' Δ) → (wk≡'' : ⟦ π'' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → (ϖ : EnvEq π' γ' γ) → CStateHalts (((∘⟨ wk-comp π' W ⊰ γ' ╎ cs ⟩) {π = π''} {wk≡ = wk≡''}))
  LabelHalts {Γ = Γ ∙ `V} (v̲a̲r̲ Cx.h) (_﹐﹝_╎_﹞ {Δ = Δ} γ W cs {π = π} {ϖ = ϖ}) =
    (Γ' : Ctx) → (γ' : Env Γ') → (π' : Wk Γ' Γ) → (ext' : WkExt π') → (π'' : Wk Γ' Δ) → (ϖ'' : EnvEq π'' γ' (topCsEnv cs)) → (ϖ : EnvEq π' γ' γ) → CStateHalts (((∘⟨ wk-comp π' W ⊰ γ' ╎ cs ⟩) {π = π''} {ϖ = ϖ''}))

  LabelHalts (v̲a̲r̲ (Cx.t i)) (γ ﹐ M) = LabelHalts (v̲a̲r̲ i) γ
  LabelHalts (v̲a̲r̲ (Cx.t i)) (γ ﹐﹝ W ╎ cs ﹞) = LabelHalts (v̲a̲r̲ i) γ

  wk-LabelHalts : (M : V̲a̲l̲ Γ Z) → (γ' : Env Γ') → (γ : Env Γ) → (π : Wk Γ' Γ) → (ext : WkExt π) → (ϖ : EnvEq π γ' γ) → (↓ᴸ : LabelHalts M γ) → LabelHalts (wk-v̲a̲l̲ π M) γ'
  wk-LabelHalts (l̲a̲m̲ W) γ' γ π ext ϖ ↓ᴸ = tt
  wk-LabelHalts (pa̲i̲r̲ M₁ M₂) γ' γ π ext ϖ ↓ᴸ = wk-LabelHalts M₁ γ' γ π ext ϖ (proj₁ ↓ᴸ) , wk-LabelHalts M₂ γ' γ π ext ϖ (proj₂ ↓ᴸ)
  wk-LabelHalts u̲n̲i̲t̲ γ' γ π ext ϖ ↓ᴸ = tt
  wk-LabelHalts (v̲a̲r̲ Cx.h) ∗ (γ ﹐ M) () ext ϖ ↓ᴸ
  wk-LabelHalts (v̲a̲r̲ Cx.h) ∗ (γ ﹐﹝ W ╎ cs ﹞) () ext ϖ ↓ᴸ
  wk-LabelHalts (v̲a̲r̲ Cx.h) (γ' ﹐ M) (γ ﹐ v̲a̲r̲ i) (wk-cong π) (wk-eq π₁) (wk-env-val-cong M₂ ϖ) ↓ᴸ = wk-LabelHalts (v̲a̲r̲ i) γ' γ π (wk-eq π) ϖ ↓ᴸ
  wk-LabelHalts (v̲a̲r̲ Cx.h) (γ' ﹐ M) (γ ﹐ v̲a̲r̲ i) (wk-wk π) (wk-eq (wk-wk π)) (wk-env-val-wk M₂ ϖ) ↓ᴸ = ql (wk-absurd wk-id π) (LabelHalts (wk-v̲a̲l̲ (wk-wk π) (v̲a̲r̲ h)) (γ' Env.﹐ M))
  wk-LabelHalts (v̲a̲r̲ Cx.h) (γ' ﹐ M) (γ ﹐ v̲a̲r̲ i) (wk-wk π) (wk-ext π₁ ext) (wk-env-val-wk M₂ ϖ) ↓ᴸ = wk-LabelHalts (v̲a̲r̲ h) γ' (γ ﹐ v̲a̲r̲ i) π ext ϖ ↓ᴸ
  wk-LabelHalts (v̲a̲r̲ Cx.h) (γ' ﹐ M) (γ ﹐﹝ W ╎ cs ﹞) (wk-cong π) (wk-eq π₁) () ↓ᴸ
  wk-LabelHalts (v̲a̲r̲ Cx.h) (γ' ﹐ M) (γ ﹐﹝ W ╎ cs ﹞) (wk-wk π) (wk-eq π₁) (wk-env-val-wk M₁ ϖ) ↓ᴸ = ql (wk-absurd (wk-wk π) π) (LabelHalts (wk-v̲a̲l̲ (wk-wk π) (v̲a̲r̲ h)) (γ' Env.﹐ M))
  wk-LabelHalts (v̲a̲r̲ Cx.h) (γ' ﹐ M) (γ ﹐﹝ W ╎ cs ﹞) (wk-wk π) (wk-ext π₁ ext) (wk-env-val-wk M₁ ϖ) ↓ᴸ = wk-LabelHalts (v̲a̲r̲ Cx.h) γ' (γ ﹐﹝ W ╎ cs ﹞) π ext ϖ ↓ᴸ
  wk-LabelHalts (v̲a̲r̲ Cx.h) (γ' ﹐﹝ W ╎ cs ﹞) (γ ﹐ M) (wk-cong π) (wk-eq π₁) () ↓ᴸ
  wk-LabelHalts (v̲a̲r̲ Cx.h) (γ' ﹐﹝ W ╎ cs ﹞) (γ ﹐ M) (wk-wk π) (wk-eq π₁) (wk-env-comp-wk W₁ cs₁ ϖ) ↓ᴸ = ql (wk-absurd (wk-wk π) π) _
  wk-LabelHalts (v̲a̲r̲ Cx.h) (γ' ﹐﹝ W ╎ cs ﹞) (γ ﹐ M) (wk-wk π) (wk-ext π₁ ext) (wk-env-comp-wk W₁ cs₁ ϖ) ↓ᴸ = wk-LabelHalts (v̲a̲r̲ Cx.h) γ' (γ ﹐ M) π ext ϖ ↓ᴸ
  wk-LabelHalts (v̲a̲r̲ Cx.h) (γ' ﹐﹝ W ╎ cs ﹞) (γ ﹐﹝ W₁ ╎ cs₁ ﹞) (wk-cong π) (wk-eq π₁) (wk-env-comp-cong W₂ cs₂ ϖ) ↓ᴸ =
    λ Γ' γ'' π' ext' π'' ϖ'' ϖ₃ →
    let
      ϖ1 : EnvEq wk-id γ' γ
      ϖ1 = subst (λ x → EnvEq x γ' γ) wk-id-id ϖ
      ϖ''' : EnvEq π' γ'' γ
      ϖ''' = subst (λ x → EnvEq π' γ'' x) (enveq-id-eq ϖ1) ϖ₃
      csh = ↓ᴸ Γ' γ'' π' ext' π'' ϖ'' ϖ'''
      weq : wk-comp π' W₁ ≡ wk-comp π' (wk-comp π W₁)
      weq = wk-comp π' W₁ ≡⟨ cong (wk-comp π') (sym (wk-comp-id W₁)) ⟩ wk-comp π' (wk-comp wk-id W₁) ≡⟨ cong (λ x → wk-comp π' (wk-comp x W₁)) (sym (wk-id-id {π = π})) ⟩ wk-comp π' (wk-comp π W₁) ∎
      goal : CStateHalts ((∘⟨ wk-comp π' (wk-comp π W₁) ⊰ γ'' ╎ cs ⟩) {π = π''} {ϖ = ϖ''})
      goal = subst (λ x → CStateHalts x) (cstate-eq weq) csh
    in
    goal
  wk-LabelHalts (v̲a̲r̲ Cx.h) (γ' ﹐﹝ W ╎ cs ﹞) (γ ﹐﹝ W₁ ╎ cs₁ ﹞) (wk-wk π) (wk-eq π₁) (wk-env-comp-wk W₂ cs₂ ϖ) ↓ᴸ = ql (wk-absurd (wk-wk π) π) _
  wk-LabelHalts (v̲a̲r̲ Cx.h) (γ' ﹐﹝ W ╎ cs ﹞) (γ ﹐﹝ W₁ ╎ cs₁ ﹞) (wk-wk π) (wk-ext π₁ ext) (wk-env-comp-wk W₂ cs₂ ϖ) ↓ᴸ = wk-LabelHalts (v̲a̲r̲ Cx.h) γ' (γ ﹐﹝ W₁ ╎ cs₁ ﹞) π ext ϖ ↓ᴸ
  wk-LabelHalts (v̲a̲r̲ (Cx.t i)) ∗ (γ ﹐ M) () ext ϖ ↓ᴸ
  wk-LabelHalts (v̲a̲r̲ (Cx.t i)) ∗ (γ ﹐﹝ W ╎ cs ﹞) () ext ϖ ↓ᴸ
  wk-LabelHalts (v̲a̲r̲ (Cx.t i)) (γ' ﹐ M) (γ ﹐ M₁) (wk-cong π) (wk-eq π₁) (wk-env-val-cong M₂ ϖ) ↓ᴸ = wk-LabelHalts (v̲a̲r̲ i) γ' γ π (WkExt.wk-eq π) ϖ ↓ᴸ
  wk-LabelHalts (v̲a̲r̲ (Cx.t i)) (γ' ﹐ M) (γ ﹐ M₁) (wk-wk π) (wk-eq π₁) (wk-env-val-wk M₂ ϖ) ↓ᴸ = ql (wk-absurd (wk-wk π) π) (LabelHalts (wk-v̲a̲l̲ (wk-wk π) (v̲a̲r̲ (t i))) (γ' Env.﹐ M))
  wk-LabelHalts (v̲a̲r̲ (Cx.t i)) (γ' ﹐ M) (γ ﹐ M₁) (wk-wk π) (wk-ext π₁ ext) (wk-env-val-wk M₂ ϖ) ↓ᴸ = wk-LabelHalts (v̲a̲r̲ (Cx.t i)) γ' (γ ﹐ M₁) π ext ϖ ↓ᴸ
  wk-LabelHalts (v̲a̲r̲ (Cx.t i)) (γ' ﹐ M) (γ ﹐﹝ W ╎ cs ﹞) (wk-cong π) (wk-eq π₁) () ↓ᴸ
  wk-LabelHalts (v̲a̲r̲ (Cx.t i)) (γ' ﹐ M) (γ ﹐﹝ W ╎ cs ﹞) (wk-wk π) (wk-eq π₁) (wk-env-val-wk M₁ ϖ) ↓ᴸ = ql (wk-absurd (wk-wk π) π) (LabelHalts (wk-v̲a̲l̲ (wk-wk π) (v̲a̲r̲ (t i))) (γ' Env.﹐ M))
  wk-LabelHalts (v̲a̲r̲ (Cx.t i)) (γ' ﹐ M) (γ ﹐﹝ W ╎ cs ﹞) (wk-wk π) (wk-ext π₁ ext) (wk-env-val-wk M₁ ϖ) ↓ᴸ = wk-LabelHalts (v̲a̲r̲ (Cx.t i)) γ' (γ ﹐﹝ W ╎ cs ﹞) π ext ϖ ↓ᴸ
  wk-LabelHalts (v̲a̲r̲ (Cx.t i)) (γ' ﹐﹝ W ╎ cs ﹞) (γ ﹐ M) (wk-cong π) (wk-eq π₁) () ↓ᴸ
  wk-LabelHalts (v̲a̲r̲ (Cx.t i)) (γ' ﹐﹝ W ╎ cs ﹞) (γ ﹐ M) (wk-wk π) (wk-eq π₁) (wk-env-comp-wk W₁ cs₁ ϖ) ↓ᴸ = ql (wk-absurd (wk-wk π) π) _
  wk-LabelHalts (v̲a̲r̲ (Cx.t i)) (γ' ﹐﹝ W ╎ cs ﹞) (γ ﹐ M) (wk-wk π) (wk-ext π₁ ext) (wk-env-comp-wk W₁ cs₁ ϖ) ↓ᴸ = wk-LabelHalts (v̲a̲r̲ (Cx.t i)) γ' (γ ﹐ M) π ext ϖ ↓ᴸ
  wk-LabelHalts (v̲a̲r̲ (Cx.t i)) (γ' ﹐﹝ W ╎ cs ﹞) (γ ﹐﹝ W₁ ╎ cs₁ ﹞) (wk-cong π) (wk-eq π₁) (wk-env-comp-cong W₂ cs₂ ϖ) ↓ᴸ = wk-LabelHalts (v̲a̲r̲ i) γ' γ π (WkExt.wk-eq π) ϖ ↓ᴸ
  wk-LabelHalts (v̲a̲r̲ (Cx.t i)) (γ' ﹐﹝ W ╎ cs ﹞) (γ ﹐﹝ W₁ ╎ cs₁ ﹞) (wk-wk π) (wk-eq π₁) (wk-env-comp-wk W₂ cs₂ ϖ) ↓ᴸ = ql (wk-absurd (wk-wk π) π) _
  wk-LabelHalts (v̲a̲r̲ (Cx.t i)) (γ' ﹐﹝ W ╎ cs ﹞) (γ ﹐﹝ W₁ ╎ cs₁ ﹞) (wk-wk π) (wk-ext π₁ ext) (wk-env-comp-wk W₂ cs₂ ϖ) ↓ᴸ = wk-LabelHalts (v̲a̲r̲ (Cx.t i)) γ' (γ ﹐﹝ W₁ ╎ cs₁ ﹞) π ext ϖ ↓ᴸ


  LookupTermHalts : {T : LookupState X} → (H : LookupHaltingState T) → Set
  LookupTermHalts found-unit = ⊤
  LookupTermHalts (found-pair {LHS = LHS} {RHS = RHS} {γ = γ}) = LabelHalts LHS γ × LabelHalts RHS γ
  LookupTermHalts (found-lam {W = W} {γ = γ}) = ⊤
  --LookupTermHalts (found-comp {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡}) = CStateHalts (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡}))
  LookupTermHalts (found-comp {W = W} {γ = γ} {cs = cs} {π = π} {ϖ = ϖ}) = LabelHalts (v̲a̲r̲ h) ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {ϖ = ϖ}) --CStateHalts (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {ϖ = ϖ}))

  LookupEnvHalts : {Γ : Ctx} → (γ : Env Γ) → Set
  LookupEnvHalts ∗ = ⊤
  LookupEnvHalts (γ ﹐ M) = LookupEnvHalts γ × (LabelHalts M γ)
  --LookupEnvHalts ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) = LookupEnvHalts γ × CStateHalts (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡}))
  --LookupEnvHalts ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {ϖ = ϖ}) = LookupEnvHalts γ × CStateHalts (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {ϖ = ϖ}))
  --LookupEnvHalts ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {ϖ = ϖ}) = LookupEnvHalts γ × ⊤
  LookupEnvHalts ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {ϖ = ϖ}) = LookupEnvHalts γ × LabelHalts (v̲a̲r̲ h) ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {ϖ = ϖ})

  data LookupSteps : LookupState X → Set where

    steps : {S T : LookupState X} → (S→T : S →ᴸ* T) → (H : LookupHaltingState T) → ⟦ S ⟧ᴸ ≡ ⟦ T ⟧ᴸ → (π : Wk (lCtx S) (lTCtx T)) → (⟦ π ⟧ʷ ⟦ lEnv S ⟧ᴱ ≡ ⟦ lTEnv T ⟧ᴱ)
            → EnvExt (lookup-index S→T) (lEnv S) (lEnv T)
            → WkExt π
            → EnvEq π (lEnv S) (lTEnv T)
            → LookupTermHalts H
            → LookupSteps S

  lookup : (i : Γ ∋ X) → (γ : Env Γ) → (↓ᴱ : LookupEnvHalts γ) → LookupSteps {X = X} ⟨ i ∥ γ ⟩
  lookup Cx.h (γ ﹐ l̲a̲m̲ W) ↓ᴱ = steps (⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩ ◼) (found-lam {W = W} {γ = γ}) refl (wk-wk wk-id) refl env-val (wk-ext wk-id (wk-eq wk-id)) (wk-env-val-wk (l̲a̲m̲ W) enveq-id) (proj₂ ↓ᴱ)
  lookup Cx.h (γ ﹐ pa̲i̲r̲ LHS RHS) ↓ᴱ = steps (⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩ ◼) found-pair refl (wk-wk wk-id) refl env-val (wk-ext wk-id (wk-eq wk-id)) (wk-env-val-wk (pa̲i̲r̲ LHS RHS) enveq-id) (proj₂ ↓ᴱ)
  lookup Cx.h (γ ﹐ u̲n̲i̲t̲) ↓ᴱ = steps (⟨ h ∥ _﹐_ γ (u̲n̲i̲t̲) ⟩ ◼) found-unit refl (wk-wk wk-id) refl env-val (wk-ext wk-id (wk-eq wk-id)) (wk-env-val-wk u̲n̲i̲t̲ enveq-id) tt
  lookup Cx.h (γ ﹐ v̲a̲r̲ i) ↓ᴱ with lookup i γ (proj₁ ↓ᴱ)
  ... | steps {T = T} i>>T HT i≡T WK w≡γ ext we ϖ ↓ᴱ' =
              let
                a0 = li≡i i>>T HT
                a1 = subst (λ x → EnvExt x γ (lEnv T)) (a0) ext
              in
              steps (_ →ᴸ⟨ val-h-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ (ext-jmp a1) (wk-ext WK we) (wk-env-val-wk (v̲a̲r̲ i) ϖ) ↓ᴱ'
  --lookup Cx.h ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) ↓ᴱ =
  lookup Cx.h ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {ϖ = ϖ}) ↓ᴱ =
    steps (⟨ h ∥ γ ﹐﹝ W ╎ cs ﹞ ⟩ ◼) found-comp refl (wk-wk wk-id) refl env-comp (wk-ext wk-id (wk-eq wk-id)) (wk-env-comp-wk W cs enveq-id) (proj₂ ↓ᴱ)
  lookup (Cx.t i) (γ ﹐ M) ↓ᴱ with lookup i γ (proj₁ ↓ᴱ)
  ... | steps {T = T} i>>T HT i≡T WK w≡γ ext we ϖ ↓ᴱ' = steps (_ →ᴸ⟨ val-t-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ (ext-val ext) (wk-ext WK we) (wk-env-val-wk M ϖ) ↓ᴱ'
  lookup (Cx.t i) (γ ﹐﹝ W ╎ cs ﹞) ↓ᴱ  with lookup i γ (proj₁ ↓ᴱ)
  ... | steps {T = T} i>>T HT i≡T WK w≡γ ext we ϖ ↓ᴱ' =
      steps (_ →ᴸ⟨ (comp-t-step) ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ (ext-comp ext) (wk-ext WK we) (wk-env-comp-wk W cs ϖ) ↓ᴱ'

  lookup-halt-lemma : (i : Γ' ∋ `V) → (γ : Env Γ) → (↓ᴱ : LookupEnvHalts γ) → (π : Wk Γ Γ') → (LabelHalts (v̲a̲r̲ (wk-mem π i)) γ)
  lookup-halt-lemma Cx.h ∗ ↓ᴱ ()
  lookup-halt-lemma Cx.h (γ ﹐ v̲a̲r̲ i) ↓ᴱ (wk-cong π) =
    let
     IH = lookup-halt-lemma i γ (proj₁ ↓ᴱ) wk-id
     goal : LabelHalts (v̲a̲r̲ i) γ
     goal = subst (λ x → LabelHalts (v̲a̲r̲ x) γ) wk-mem-id IH
    in
    goal
  lookup-halt-lemma Cx.h (γ ﹐ l̲a̲m̲ _) ↓ᴱ (wk-wk π) = lookup-halt-lemma h γ (proj₁ ↓ᴱ) π
  lookup-halt-lemma Cx.h (γ ﹐ pa̲i̲r̲ _ _) ↓ᴱ (wk-wk π) = lookup-halt-lemma h γ (proj₁ ↓ᴱ) π
  lookup-halt-lemma Cx.h (γ ﹐ u̲n̲i̲t̲) ↓ᴱ (wk-wk π) = lookup-halt-lemma h γ (proj₁ ↓ᴱ) π
  lookup-halt-lemma Cx.h (γ ﹐ v̲a̲r̲ _) ↓ᴱ (wk-wk π) = lookup-halt-lemma h γ (proj₁ ↓ᴱ) π
  lookup-halt-lemma Cx.h (γ ﹐﹝ W ╎ cs ﹞) ↓ᴱ (wk-cong π) = proj₂ ↓ᴱ
  lookup-halt-lemma Cx.h (γ ﹐﹝ W ╎ cs ﹞) ↓ᴱ (wk-wk π) = lookup-halt-lemma h γ (proj₁ ↓ᴱ) π
  lookup-halt-lemma (Cx.t i) ∗ ↓ᴱ ()
  lookup-halt-lemma (Cx.t i) (γ ﹐ M) ↓ᴱ (wk-cong π) = lookup-halt-lemma i γ (proj₁ ↓ᴱ) π
  lookup-halt-lemma (Cx.t i) (γ ﹐ M) ↓ᴱ (wk-wk π) = lookup-halt-lemma (t i) γ (proj₁ ↓ᴱ) π
  lookup-halt-lemma (Cx.t i) (γ ﹐﹝ W ╎ cs ﹞) ↓ᴱ (wk-cong π) = lookup-halt-lemma i γ (proj₁ ↓ᴱ) π
  lookup-halt-lemma (Cx.t i) (γ ﹐﹝ W ╎ cs ﹞) ↓ᴱ (wk-wk π) = lookup-halt-lemma (t i) γ (proj₁ ↓ᴱ) π

  data ValSteps : ValState T◾ → Set where

    steps : {S T : ValState T◾} → S ↠ᵛ T → (H : ValHaltingState T) → ⟦ S ⟧ᵛꟴ ≡ ⟦ T ⟧ᵛꟴ → (π : Wk (botCtx T) (botCtx S)) --→ (⟦ π ⟧ʷ ⟦ botEnv T ⟧ᴱ ≡ ⟦ botEnv S ⟧ᴱ)
            → WkExt π
            → EnvEq π (botEnv T) (botEnv S)
            → LookupEnvHalts (botEnv T)
            → LabelHalts (haltingTerm H) (botEnv T)
            → ValSteps S


  mutual

    val-eval-rec : (M : Γ' ⊢ᵛ X) → (γ : Env Γ) → (↓ᴱ : LookupEnvHalts γ) → (π : Wk Γ Γ') → ValSteps {T◾ = X} (∘ ((⇡ (wk-val π M) ⊲ γ ∷ □) {↥ = 🗆}))

    val-eval-rec {X = `V} (var {A = .`V} i) γ ↓ᴱ π = steps (_ →ᵛ⟨ ∘var-c ⟩．) (∙ v̲a̲r̲ (wk-mem π i) ⊲ γ ■) refl wk-id (WkExt.wk-eq wk-id) enveq-id ↓ᴱ (lookup-halt-lemma i γ ↓ᴱ π)

    val-eval-rec {X = `Unit} (var {A = .`Unit} i) γ ↓ᴱ π with lookup (wk-mem π i) γ ↓ᴱ
    ... | steps i>>T found-unit i≡T π₁ w≡γ ext we ϖ ↓ᴸ =

                steps (_ →ᵛ⟨ ∘var i>>T π₁ ext we ϖ found-unit ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id (WkExt.wk-eq wk-id) enveq-id ↓ᴱ tt

    val-eval-rec {X = X `× X₁} (var {A = .(X `× X₁)} i) γ ↓ᴱ π with lookup (wk-mem π i) γ ↓ᴱ
    ... | steps i>>T (found-pair {LHS = LHS} {RHS = RHS} {γ = γ₁}) i≡T π₁ w≡γ ext we ϖ ↓ᴸ =

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

              (WkExt.wk-eq wk-id)

              enveq-id

              ↓ᴱ

              (wk-LabelHalts LHS _ γ₁ π₁ we ϖ (proj₁ ↓ᴸ) , wk-LabelHalts RHS _ (lTEnv LookupState.⟨ h ∥ γ₁ Env.﹐ pa̲i̲r̲ LHS RHS ⟩) π₁ we ϖ (proj₂ ↓ᴸ))

    val-eval-rec {Γ' = Γ'} {X = X `⇒ X₁} {Γ = Γ} (var {A = .(X `⇒ X₁)} i) γ ↓ᴱ π with lookup (wk-mem π i) γ ↓ᴱ

    ... | steps i>>T (found-lam {X = X₂} {Y = Y₂} {W = W} {γ = γ₁}) i≡T π₁ w≡γ ext we ϖ ↓ᴸ =

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

              (WkExt.wk-eq wk-id)

              enveq-id

              ↓ᴱ

              tt

    val-eval-rec (lam W) γ ↓ᴱ π =

              steps

              (∘ ⇡ (wk-val π (lam W)) ⊲ γ ∷ □ →ᵛ⟨ ∘lam ⟩．)

              (∙ l̲a̲m̲ (wk-comp (wk-cong π) W) ⊲ γ ■)

              refl

              wk-id

              (WkExt.wk-eq wk-id)

              enveq-id

              ↓ᴱ

              tt

    val-eval-rec unit γ ↓ᴱ π = steps (_ →ᵛ⟨ ∘unit ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id (WkExt.wk-eq wk-id) enveq-id ↓ᴱ tt

    val-eval-rec (pair {A = X} {B = Y} LHS RHS) γ ↓ᴱ π with val-eval-rec {X = X} LHS γ ↓ᴱ π
    ... | steps {T = ∙ (⭭_ {X = X} LT ⊲ γ₁ ∷ □) {↥ = 🗆}} L>T (∙ LT ⊲ γ₁ ■) L≡T πᴸ extᴸ ϖᴸ ↓ᴱ' ↓ᴸ' with val-eval-rec {X = Y} RHS γ₁ ↓ᴱ' (wk-trans πᴸ π)
    ... | steps {T = ∙ (⭭_ {X = Y} RT ⊲ γ₂ ∷ □) {↥ = 🗆}} R>T (∙ RT ⊲ γ₂ ■) R≡T πᴿ extᴿ ϖᴿ ↓ᴱ'' ↓ᴸ''  rewrite sym (wk-val-trans RHS πᴸ π) =

              let

                R≡T' : ⟦ wk-val πᴸ (wk-val π RHS) ⟧ᵛ ⟦ γ₁ ⟧ᴱ ≡ ⟦ toVal RT ⟧ᵛ ⟦ γ₂ ⟧ᴱ
                R≡T' =  ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ (⟦ πᴸ ⟧ʷ ⟦ γ₁ ⟧ᴱ))
                      ≡⟨ cong ⟦ RHS ⟧ᵛ (wk-sem-trans πᴸ π ⟦ γ₁ ⟧ᴱ) ⟩
                        ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                      ≡⟨ R≡T ⟩
                        ⟦ toVal RT ⟧ᵛ ⟦ γ₂ ⟧ᴱ ∎
                wk≡ᴸ = env-eq-sem-lemma ϖᴸ
                wk≡ᴿ = env-eq-sem-lemma ϖᴿ

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

                (wk-ext-trans extᴿ extᴸ)

                (env-eq-trans extᴿ extᴸ ϖᴿ ϖᴸ)
                {- ( ⟦ wk-trans πᴿ πᴸ ⟧ʷ ⟦ γ₂ ⟧ᴱ
                ≡⟨ sym (wk-sem-trans πᴿ πᴸ ⟦ γ₂ ⟧ᴱ) ⟩
                  ⟦ πᴸ ⟧ʷ (⟦ πᴿ ⟧ʷ ⟦ γ₂ ⟧ᴱ)
                ≡⟨ cong (λ y → ⟦ πᴸ ⟧ʷ y) wk≡ᴿ ⟩
                  ⟦ πᴸ ⟧ʷ ⟦ γ₁ ⟧ᴱ
                ≡⟨ wk≡ᴸ ⟩
                  ⟦ γ ⟧ᴱ ∎) -}

                ↓ᴱ''

                (wk-LabelHalts LT _ γ₁ πᴿ extᴿ ϖᴿ ↓ᴸ' , ↓ᴸ'')

    val-eval-rec {Γ = Γ} (pm {A = A} {B = B} M N) γ ↓ᴱ π with val-eval-rec M γ ↓ᴱ π
    ... | steps {S = S} M>T ∙ pa̲i̲r̲ LHS RHS ⊲ γ₁ ■ M≡T π₁ ext₁ ϖ₁ ↓ᴱ' (↓ᴸᴸ' , ↓ᴸᴿ') with val-eval-rec N (_﹐_ (_﹐_ γ₁ LHS) (wk-v̲a̲l̲ (wk-wk wk-id) RHS)) ((↓ᴱ' , ↓ᴸᴸ') , wk-LabelHalts RHS (γ₁ ﹐ LHS) γ₁ (wk-wk wk-id) (WkExt.wk-ext wk-id (WkExt.wk-eq wk-id)) (EnvEq.wk-env-val-wk LHS enveq-id) ↓ᴸᴿ') ((wk-cong (wk-cong (wk-trans π₁ π)))) | (wk-val-trans N (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π)))
    ...    | steps {T = T} N>T ∙T N≡T π₂ ext₂ ϖ₂ ↓ᴱ'' ↓ᴸ'' | eq with N>T
    ...      | N>T' rewrite sym eq =

          let
            wk≡₁ = env-eq-sem-lemma ϖ₁
            wk≡₂ = env-eq-sem-lemma ϖ₂
          in

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

            (wk-ext-trans ext₂ (WkExt.wk-ext (wk-wk π₁) (WkExt.wk-ext π₁ ext₁)))

            (env-eq-trans ext₂ (WkExt.wk-ext (wk-wk π₁) (WkExt.wk-ext π₁ ext₁)) ϖ₂ (EnvEq.wk-env-val-wk (wk-v̲a̲l̲ (wk-wk wk-id) RHS) (EnvEq.wk-env-val-wk LHS ϖ₁)))
            {- ( ⟦ wk-trans π₂ (wk-wk (wk-wk π₁)) ⟧ʷ ⟦ botEnv T ⟧ᴱ
              ≡⟨ sym (wk-sem-trans π₂ (wk-wk (wk-wk π₁)) ⟦ botEnv T ⟧ᴱ) ⟩
              ⟦ wk-wk (wk-wk π₁) ⟧ʷ (⟦ π₂ ⟧ʷ ⟦ botEnv T ⟧ᴱ)
              ≡⟨ cong (λ y → ⟦ wk-wk (wk-wk π₁) ⟧ʷ y) wk≡₂ ⟩
              ⟦ wk-wk (wk-wk π₁) ⟧ʷ (((⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))
              ≡⟨ refl ⟩
              ⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ
              ≡⟨ wk≡₁ ⟩
              ⟦ γ ⟧ᴱ ∎) -}

            ↓ᴱ''

            ↓ᴸ''

    val-eval : (M : ε ⊢ᵛ X) → ValSteps {T◾ = X} (∘ ((⇡ wk-val wk-id M ⊲ ∗ ∷ □) {↥ = 🗆}))
    val-eval M = val-eval-rec M ∗ tt wk-id

{- ZZZ
  -- {-# TERMINATING #-}
  --mutual
    app-eval-rec :   (M : Γ' ⊢ᵛ X `⇒ Y) → (N : V̲a̲l̲ Γ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ Y) → (πₓ : Wk Γ Δ)
                   → (wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ)
                   → CompSteps ((∙⟨ (a̲pp (wk-val π M) N) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    app-eval-rec (var i) N γ π cs πₓ wk≡₀ with lookup (wk-mem π i) γ {!!} --(allEnvHalt γ)
    ... | steps i>>T (found-lam {X = X} {W = W} {γ = γ₁}) i≡T π₁ w≡γ ext we ϖ ↓ᴹ =
      let
        a1 = {!!} --↓ᴹ {!!} {!!} {!!}
        -- a2 = a1 _ _ _ cs (wk-wk πₓ) (wk-cong π₁) {!!} wk≡₀
        -- a3 = CStateHalts.trace a2
      in
                 steps

                    ((∙⟨ a̲pp (wk-val π (var i)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-var {wk≡ₓ = wk≡₀} i>>T π₁ ⟩ {!!}))

                    {!!}

                    (   ⟦ ((∙⟨ C̲o̲m̲p.a̲pp (var (wk-mem π i)) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀}) ⟧ᶜꟴ
                      ≡⟨ refl ⟩
                        ⟦ wk-mem π i ⟧ᵐ ⟦ γ ⟧ᴱ (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ cong (λ x → x (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) i≡T ⟩
                       ⟦ W ⟧ᶜ (⟦ γ₁ ⟧ᴱ , (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ))  (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ cong (λ x → ⟦ W ⟧ᶜ (x , (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ))  (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym w≡γ) ⟩
                       ⟦ W ⟧ᶜ (⟦ π₁ ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ refl ⟩
                        ⟦ ((∘⟨ wk-comp (wk-cong π₁) W ⊰ γ Env.﹐ N ╎ cs ⟩) {π = wk-wk πₓ} {wk≡ = wk≡₀}) ⟧ᶜꟴ
                      ≡⟨ {!!} ⟩
                        ⟦ {!!} ⟧ᶜꟴ ∎)

    {-with lookup (wk-mem π i) γ {!!}
    ... | steps i>>T (found-lam {X = X} {W = W} {γ = γ₁}) i≡T π₁ w≡γ ext we ϖ ↓ᴱ' with comp-eval-rec W (γ ﹐ N) (wk-cong π₁) cs (wk-wk πₓ) wk≡₀
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
                        ⟦ T ⟧ᶜꟴ ∎) -}


    app-eval-rec (lam W) N γ π cs πₓ wk≡₀ with comp-eval-rec W (γ ﹐ N) (wk-cong π) cs (wk-wk πₓ) wk≡₀
    ... | steps {T = T} W>WT HT S≡T =

                  steps

                     ( ∙⟨ a̲pp (wk-val π (lam W)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-lam {wk≡ₓ = wk≡₀} ⟩ W>WT)

                     HT

                     S≡T

    app-eval-rec (pm M₁ N₁) N γ π cs πₓ wk≡₀ with val-eval-rec M₁ γ {!!} π
    ... | steps {T = ∙ (⭭ pa̲i̲r̲ {X = X} {Y = Y} LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ _ _ with wk-val-trans N₁ (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
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

    comp-eval-rec : (W : Γ' ⊢ᶜ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ X) → (πₓ : Wk Γ Δ)
                  → (wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ)
                  → CompSteps ((∘⟨ wk-comp π W ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    comp-eval-rec (return {A = X} M) γ π ◻ πₓ wk≡₀ with val-eval-rec {X = X} M γ {!!} π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ _ _ =

                 steps

                    (∘⟨ wk-comp π (return M) ⊰ γ ╎ ◻ ⟩ →ᶜ⟨ ∘return {πₓ' = wk-wk-ε} {wk≡ₓ = wk≡₀} {wk≡ₓ' = wk≡₀} M>T ⟩ (∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ ◻ ⟩ ◼))

                    ret --ret

                    (cong (λ x → (η x) k₀) M≡T)

    comp-eval-rec (return {A = X} M) γ π ((M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁}) πₓ wk≡₀ = {!!} {-with val-eval-rec {X = X} M γ π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ ↓ᴱ with
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

    comp-eval-rec (pm {A = X} {B = Y} M W) γ π cs πₓ wk≡₀ with val-eval-rec {X = X `× Y} M γ {!!} π
    ...  | steps {T = ∙ ((⭭_ {X = X `× Y} (pa̲i̲r̲ LHS RHS) ⊲ γ' ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ _ _ with
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

                   (∘⟨ wk-comp π (pm M W) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘pm {wk≡ₓ = wk≡₀} {wk≡ₓ' = ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ' ⟧ᴱ ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ' ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ) ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡⟨ wk≡₀ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎} π M>T π' ⟩ W>T)

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

                  (  ∘⟨ push (wk-comp π W) (wk-comp (wk-cong π) V) ⊰ γ ╎ cs ⟩  →ᶜ⟨ ∘push {wk≡ₓ = wk≡₀} ⟩ W>T )

                  ret

                  (  ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (λ z → ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀))
                  ≡⟨  cong (⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) (extensionality (λ z → sym (lem0 cs ((⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , z)))))) ⟩
                     ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (λ z → ⟦ cs ⟧ᶜˢ (λ k → ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , z) k) k₀)
                  ≡⟨ refl ⟩
                    (⟦ π ⟧ʷ ； ⟦ W ⟧ᶜ) ⟦ γ ⟧ᴱ ⟦ (wk-comp (wk-cong π) V ⊲ γ ⦂⦂ cs) {π = πₓ} {wk≡ = wk≡₀} ⟧ᴷ
                  ≡⟨ S≡T ⟩
                    (⟦ toVal M ⟧ᵛ ； η) ⟦ γ₁ ⟧ᴱ ⟦ ◻ ⟧ᴷ ∎)

    comp-eval-rec (app M N) γ π cs πₓ wk≡₀ with val-eval-rec N γ {!!} π
    ... | steps {T = ∙ ((⭭_ NT ⊲ γᴺ ∷ □) {↥ = 🗆})} N>NT ∙NT N≡NT πᴺ wk≡ᴺ _ _ with
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

    comp-eval-rec (var {A = X} M) γ π cs πₓ wk≡₀ = {!!} {-with val-eval-rec {X = `V} M γ π
    ... | steps {T = ∙ ((⭭ v̲a̲r̲ i) ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ ↓ᴱ with lookup i γ₁ {!!}
    ... | steps i>>T (found-comp {X = X} {W = W'} {γ = γ'} {cs = cs'} {π = πᶜ} {wk≡ = wk≡c}) i≡T π₂ w≡γ ext we ϖ ↓ᴱ' with
                    comp-eval-rec
                     W'
                     γ'
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

    comp-eval-rec (sub W V) γ π cs πₓ wk≡₀ with comp-eval-rec W ((γ ﹐﹝ wk-comp π V ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡₀}) (wk-cong π) cs (wk-wk πₓ) wk≡₀
    ... | steps {T = T} W>WT HT S≡T =

                steps

                    (∘⟨ sub (wk-comp (wk-cong π) W) (wk-comp π V) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘sub ⟩ W>WT)

                    HT

                    S≡T

    comp-eval : (W : ε ⊢ᶜ R₀) → CompSteps ((∘⟨ wk-comp wk-id W ⊰ ∗ ╎ ◻ ⟩) {π = wk-id} {wk≡ = refl})
    comp-eval W = comp-eval-rec W ∗ wk-id ◻ wk-id refl


{- XXX
    app-eval-rec :   (M : Γ' ⊢ᵛ X `⇒ Y) → (N : V̲a̲l̲ Γ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ Y) → (πₓ : Wk Γ Δ)
                   → (wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ)
                   → CompSteps ((∙⟨ (a̲pp (wk-val π M) N) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    app-eval-rec (var i) N γ π cs πₓ wk≡₀ with lookup (wk-mem π i) γ
    ... | steps i>>T (found-lam {X = X} {W = W} {γ = γ₁}) i≡T π₁ w≡γ ext we ϖ =

                --let
                --  --a0 = f _ γ {!!} π₁ _ cs ↓ᶜ πₓ wk≡₀ N {!!}
                --  --a0 = f _ γ (PEH-to-EH ↓) π₁ _ cs ↓ᶜ πₓ wk≡₀ N (PVH-to-VH n↓ (PEH-to-EH ↓))
                --  a0 = f _ γ ↓ π₁ _ cs ↓ᶜ πₓ wk≡₀ N n↓
                --  a1 = get-chsteps a0
                --in

                steps

                  ((∙⟨ a̲pp (wk-val π (var i)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-var {wk≡ₓ = wk≡₀} i>>T π₁ ⟩ {!!}))

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


    app-eval-rec (lam W) N γ π cs πₓ wk≡₀ with comp-eval-rec W (γ ﹐ N) (wk-cong π) cs (wk-wk πₓ) wk≡₀
    ... | steps {T = T} W>WT HT S≡T =

                  steps

                     ( ∙⟨ a̲pp (wk-val π (lam W)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-lam {wk≡ₓ = wk≡₀} ⟩ W>WT)

                     HT

                     S≡T

    app-eval-rec (pm M₁ N₁) N γ π cs πₓ wk≡₀ with val-eval-rec M₁ γ ? π
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

    comp-eval-rec : (W : Γ' ⊢ᶜ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ X) → (πₓ : Wk Γ Δ)
                  → (wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ)
                  → CompSteps ((∘⟨ wk-comp π W ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    comp-eval-rec (return {A = X} M) γ π ◻ πₓ wk≡₀ with val-eval-rec {X = X} M γ ? π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ =

                 steps

                    (∘⟨ wk-comp π (return M) ⊰ γ ╎ ◻ ⟩ →ᶜ⟨ ∘return {wk≡ₓ = wk≡₀} {wk≡ₓ' = wk≡₀} M>T ⟩ (∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ ◻ ⟩ ◼))

                    {!!} --ret

                    (cong (λ x → (η x) k₀) M≡T)

    comp-eval-rec (return {A = X} M) γ π ((M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁}) πₓ wk≡₀ with val-eval-rec {X = X} M γ ? π
    ... | steps {T = ∙ ((⭭ M₁) ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T (∙ M₁ ⊲ γ₁ ■) M≡T π' wk≡ =
    --with ↓ᵂ _ (wk-trans π' πₓ) (wk-trans (wk-trans (wk-wk π') πₓ) π₁) γ₁ {!!} {-↓ᵛ-} M₁ {!!} {- pv↓ -} {-v↓-} {!!}
    --... | (comp-halts T' H' S→T' eq') = --{!!}
                 steps

                 ((∘⟨ wk-comp π (return M) ⊰ γ ╎ (M' ⊲ γ' ⦂⦂ cs) ⟩
                    →ᶜ⟨ ∘return {wk≡ₓ = wk≡₀} {wk≡ₓ' = ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ
                                         ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                                         ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                                         ≡⟨ wk≡₀ ⟩ ⟦ γ' ⟧ᴱ ∎} M>T ⟩ _
                    →ᶜ⟨ ∙return {πₓ = wk-trans (wk-trans π' πₓ) π₁} {πₓ' = π₁} {wk≡ₓ = ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ) ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ _ ⟧ᴱ ≡⟨ wk≡₀ ⟩ ⟦ γ' ⟧ᴱ ∎} {wk≡ₓ' = ⟦ wk-trans (wk-trans π' πₓ) π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡⟨ sym (wk-sem-trans (wk-trans π' πₓ) π₁ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ π₁ ⟧ʷ (⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ) ≡⟨ cong ⟦ π₁ ⟧ʷ (sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ)) ⟩ ⟦ π₁ ⟧ʷ (⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ)) ≡⟨ cong (λ x → ⟦ π₁ ⟧ʷ (⟦ πₓ ⟧ʷ x)) wk≡ ⟩ ⟦ π₁ ⟧ʷ (⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ) ≡⟨ cong ⟦ π₁ ⟧ʷ wk≡₀ ⟩ ⟦ π₁ ⟧ʷ ⟦ γ' ⟧ᴱ ≡⟨ wk≡₁ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎} ⟩
                    {!!} ) )

                 {!!} --H'

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

    comp-eval-rec (pm {A = X} {B = Y} M W) γ π cs πₓ wk≡₀ with val-eval-rec {X = X `× Y} M γ ? π
    ...  | steps {T = ∙ ((⭭_ {X = X `× Y} (pa̲i̲r̲ LHS RHS) ⊲ γ' ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ {-(vs-halts v↓)-} with
                    comp-eval-rec
                     W
                     (γ' ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS)
                     --(val-in-env (wk-v̲a̲l̲ (wk-wk wk-id) RHS) (γ' ﹐ LHS) {!!} {!!}) --((val-in-env (wk-v̲a̲l̲ (wk-wk wk-id) RHS) (γ' ﹐ LHS) (let v↓' = {!!} {-v↓-} (wk-wk wk-id) (γ' ﹐ LHS) (⟨ γ' ⟩ ﹐ LHS) in proj₂ v↓') (val-in-env LHS γ' (let v↓' = {!!} {-v↓-} wk-id γ' ⟨ γ' ⟩ in subst (λ x → ValHalts x γ') (wk-v̲a̲l̲-id LHS) (proj₁ v↓')) ↓ᵛ)))
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

                   (∘⟨ wk-comp π (pm M W) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘pm {wk≡ₓ = wk≡₀} {wk≡ₓ' = ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ' ⟧ᴱ ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ' ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ) ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡⟨ wk≡₀ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎} π M>T π' ⟩ W>T)

                   HT

                   ( ⟦ W ⟧ᶜ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , proj₁ (⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))) , proj₂ (⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ cong₂ (λ x y → ⟦ W ⟧ᶜ ((⟦ π ⟧ʷ x , proj₁ y) , proj₂ y) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym wk≡) M≡T ⟩
                     ⟦ W ⟧ᶜ ((⟦ π ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ' ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ' ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ cong (λ x → ⟦ W ⟧ᶜ ((x , ⟦ toVal LHS ⟧ᵛ ⟦ γ' ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ' ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (wk-sem-trans π' π ⟦ γ' ⟧ᴱ) ⟩
                     ⟦ W ⟧ᶜ ((⟦ wk-trans π' π ⟧ʷ ⟦ γ' ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ' ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ' ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ S≡T ⟩
                     ⟦ T ⟧ᶜꟴ ∎)

    comp-eval-rec (push W V) γ π cs πₓ wk≡₀ with
      comp-eval-rec W γ π (((wk-comp (wk-cong π) V) ⊲ γ ⦂⦂ cs) {wk≡ = wk≡₀}) wk-id refl --{!!}
        --(cs-head-halts
        --  (λ Γ' π' π'' γ' ↓ᴱ M ↓ᵛ wk≡' →
        --    let
        --      IH = comp-eval-rec V (γ' ﹐ M) (val-in-env M γ' {!!} {-↓ᵛ-} {!!} {-↓ᴱ-}) (wk-cong (wk-trans π' π)) cs π'' wk≡' ↓ᶜ
        --      s = get-csteps IH
        --      s1 = (proj₁ (proj₂ (proj₂ s)))
        --    in
        --    comp-halts (proj₁ s) (proj₁ (proj₂ s)) {!!} {!!})
        --  ↓ᶜ)
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

    comp-eval-rec (app M N) γ π cs πₓ wk≡₀ with val-eval-rec N γ ? π
    ... | steps {T = ∙ ((⭭_ NT ⊲ γᴺ ∷ □) {↥ = 🗆})} N>NT ∙NT N≡NT πᴺ wk≡ᴺ {-(vs-halts v↓)-} with
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

    comp-eval-rec (var {A = X} M) γ π cs πₓ wk≡₀ with val-eval-rec {X = `V} M γ ? π
    ... | steps {T = ∙ ((⭭ v̲a̲r̲ i) ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ with lookup i γ₁
    ... | steps i>>T (found-comp {X = X} {W = W'} {γ = γ'} {cs = cs'} {π = πᶜ} {wk≡ = wk≡c}) i≡T π₂ w≡γ ext we ϖ =

                steps

                  ((∘⟨ var (wk-val π M) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘var {wk≡ₓ = wk≡₀} M>T π' i>>T π₂ ⟩ {!!}))

                  {!!} --H'

                  (((⟦ π ⟧ʷ ； ⟦ M ⟧ᵛ) ； varK) ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ
                    ≡⟨ refl ⟩
                      ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)
                    ≡⟨ M≡T ⟩
                      ⟦ i ⟧ᵐ ⟦ γ₁ ⟧ᴱ
                    ≡⟨ i≡T ⟩
                      ⟦ W' ⟧ᶜ ⟦ γ' ⟧ᴱ (λ y → ⟦ cs' ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ {!!} ⟩
                      ⟦ {!!} ⟧ᶜꟴ ∎
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

    comp-eval-rec (sub W V) γ π cs πₓ wk≡₀ with comp-eval-rec W ((γ ﹐﹝ wk-comp π V ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡₀}) (wk-cong π) cs (wk-wk πₓ) wk≡₀
    ... | steps {T = T} W>WT HT S≡T =

                steps

                    (∘⟨ sub (wk-comp (wk-cong π) W) (wk-comp π V) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘sub ⟩ W>WT)

                    HT

                    S≡T

    comp-eval : (W : ε ⊢ᶜ R₀) → CompSteps ((∘⟨ wk-comp wk-id W ⊰ ∗ ╎ ◻ ⟩) {π = wk-id} {wk≡ = refl})
    comp-eval W = comp-eval-rec W ∗ wk-id ◻ wk-id refl


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

XXX -}
ZZZ -}
