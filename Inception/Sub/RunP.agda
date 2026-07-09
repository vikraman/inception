{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.RunP where

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

open import Data.Unit
open import Data.Nat
open import Data.List using (List; _∷_; []; _++_)
open import Data.List.NonEmpty.Base using (List⁺; _∷_; toList)

open import Inception.Sub.Equality
open import Inception.Sub.EnvironmentsP
open import Inception.Sub.StatesP
open import Inception.Sub.MachineP

open import Inception.Sub.Arithmetic

private
  variable
    Γ₀ : Ctx
    Z₀ : Ty

-------------------------------------------------------------------

data EnvWk : (π : Wk Γ Γ') → Env Γ Z₀ → Env Γ' Z₀ → Set where

  ⟨_⟩     :  {π : Wk Γ Γ} → (γ : Env Γ Z₀) → EnvWk π γ γ

  _﹐_     :  {π : Wk Γ Γ'} → {γ : Env Γ Z₀} → {γ' : Env Γ' Z₀} → EnvWk π γ γ' → (M : V̲a̲l̲ Γ X) → EnvWk (wk-wk {A = X} π) (γ ﹐ M) γ'


-------------------------------------------------------------------

data CompSteps : CompState Z₀ → Set where

  steps : {S T : CompState Z₀} → S →ᶜ* T → CompHaltingState T → CompSteps S

get-csteps : {S : CompState Z₀} → CompSteps S → Σ[ T ∈ CompState Z₀ ] ((CompHaltingState T) × (S →ᶜ* T))
get-csteps {S = S} (steps {T = T} S→T H) = T , H , S→T

--wk-comm-explicit : (M : V̲a̲l̲ Γ X) → (π : Wk Δ Γ) → toVal (wk-v̲a̲l̲ π M) ≡ wk-val π (toVal M)
--wk-comm-explicit M π = sym wk-comm
--{-# REWRITE wk-comm-explicit #-}


record CStateHalts (c : CompState Z₀) : Set where
  field
    target-state : CompState Z₀
    target-is-halting : CompHaltingState target-state
    trace : c →ᶜ* target-state

{-
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
-}

LabelHalts : (M : V̲a̲l̲ Γ Z) → (γ : Env Γ Z₀) → Set
LabelHalts (l̲a̲m̲ W) γ = ⊤
LabelHalts (pa̲i̲r̲ M₁ M₂) γ = LabelHalts M₁ γ × LabelHalts M₂ γ
LabelHalts u̲n̲i̲t̲ γ = ⊤
LabelHalts (v̲a̲r̲ Cx.h) (γ ﹐ v̲a̲r̲ i) = LabelHalts (v̲a̲r̲ i) γ
LabelHalts {Γ = Γ ∙ `V} (v̲a̲r̲ Cx.h) (_﹐﹝_╎_﹞ {Δ = Δ} γ W cs {π = π} {ϖ = ϖ}) = CStateHalts (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {ϖ = ϖ}))
LabelHalts (v̲a̲r̲ (Cx.t i)) (γ ﹐ M) = LabelHalts (v̲a̲r̲ i) γ
LabelHalts (v̲a̲r̲ (Cx.t i)) (γ ﹐﹝ W ╎ cs ﹞) = LabelHalts (v̲a̲r̲ i) γ

wk-LabelHalts : (M : V̲a̲l̲ Γ Z) → (γ' : Env Γ' Z₀) → (γ : Env Γ Z₀) → (π : Wk Γ' Γ) → (ext : WkExt π) → (ϖ : EnvEq π γ' γ) → (↓ᴸ : LabelHalts M γ) → LabelHalts (wk-v̲a̲l̲ π M) γ'
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
wk-LabelHalts (v̲a̲r̲ Cx.h) ((γ' ﹐﹝ W ╎ cs ﹞) {π = π₀₁} {ϖ = ϖ₀₁}) ((γ ﹐﹝ W₁ ╎ cs₁ ﹞) {π = π₀₂} {ϖ = ϖ₀₂}) (wk-cong π) (wk-eq π₁) (wk-env-comp-cong W₂ cs₂ ϖ) ↓ᴸ =
  let
    Weq : W₁ ≡ wk-comp π W₁
    Weq = W₁ ≡⟨ sym (wk-comp-id W₁) ⟩ wk-comp wk-id W₁ ≡⟨ cong (λ x → wk-comp x W₁) (sym wk-id-id) ⟩ wk-comp π W₁ ∎

    γeq : γ ≡ γ'
    γeq = sym (enveq-id-eq (subst (λ x → EnvEq x γ' γ) wk-id-id ϖ))

    πeq : π₀₂ ≡ wk-trans π π₀₂
    πeq = π₀₂ ≡⟨ sym wk-trans-id ⟩ wk-trans wk-id π₀₂ ≡⟨ cong (λ x → wk-trans x π₀₂) (sym wk-id-id) ⟩ wk-trans π π₀₂ ∎

    eq : (W₁ , γ , π₀₂) ≡ (wk-comp π W₁ , γ' , wk-trans π π₀₂)
    eq = pair-eq Weq (pair-eq γeq πeq)

    goal : CStateHalts ((∘⟨ (wk-comp π W₁) ⊰ γ' ╎ cs ⟩) {π = wk-trans π π₀₂} {ϖ = ϖ₀₁})
    goal = subst (λ x → CStateHalts x) (cstate-eq' eq) ↓ᴸ
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

LookupTermHalts : {T : LookupState X Z₀} → (H : LookupHaltingState T) → Set
LookupTermHalts found-unit = ⊤
LookupTermHalts (found-pair {LHS = LHS} {RHS = RHS} {γ = γ}) = LabelHalts LHS γ × LabelHalts RHS γ
LookupTermHalts (found-lam {W = W} {γ = γ}) = ⊤
LookupTermHalts (found-comp {W = W} {γ = γ} {cs = cs} {π = π} {ϖ = ϖ}) = LabelHalts (v̲a̲r̲ h) ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {ϖ = ϖ}) --CStateHalts (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {ϖ = ϖ}))

LookupEnvHalts : {Γ : Ctx} → (γ : Env Γ Z₀) → Set
LookupEnvHalts ∗ = ⊤
LookupEnvHalts (γ ﹐ M) = LookupEnvHalts γ × (LabelHalts M γ)
LookupEnvHalts ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {ϖ = ϖ}) = LookupEnvHalts γ × LabelHalts (v̲a̲r̲ h) ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {ϖ = ϖ})

data LookupSteps : LookupState X Z₀ → Set where

  steps : {S T : LookupState X Z₀} → (S→T : S →ᴸ* T) → (H : LookupHaltingState T) → (π : Wk (lCtx S) (lTCtx T))
          → EnvExt (lookup-index S→T) (lEnv S) (lEnv T)
          → WkExt π
          → EnvEq π (lEnv S) (lTEnv T)
          → LookupTermHalts H
          → LookupSteps S

lookup : (i : Γ ∋ X) → (γ : Env Γ Z₀) → (↓ᴱ : LookupEnvHalts γ) → LookupSteps {X = X} ⟨ i ∥ γ ⟩
lookup Cx.h (γ ﹐ l̲a̲m̲ W) ↓ᴱ = steps (⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩ ◼) (found-lam {W = W} {γ = γ}) (wk-wk wk-id) env-val (wk-ext wk-id (wk-eq wk-id)) (wk-env-val-wk (l̲a̲m̲ W) enveq-id) (proj₂ ↓ᴱ)
lookup Cx.h (γ ﹐ pa̲i̲r̲ LHS RHS) ↓ᴱ = steps (⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩ ◼) found-pair (wk-wk wk-id) env-val (wk-ext wk-id (wk-eq wk-id)) (wk-env-val-wk (pa̲i̲r̲ LHS RHS) enveq-id) (proj₂ ↓ᴱ)
lookup Cx.h (γ ﹐ u̲n̲i̲t̲) ↓ᴱ = steps (⟨ h ∥ _﹐_ γ (u̲n̲i̲t̲) ⟩ ◼) found-unit (wk-wk wk-id) env-val (wk-ext wk-id (wk-eq wk-id)) (wk-env-val-wk u̲n̲i̲t̲ enveq-id) tt
lookup Cx.h (γ ﹐ v̲a̲r̲ i) ↓ᴱ with lookup i γ (proj₁ ↓ᴱ)
... | steps {T = T} i>>T HT WK ext we ϖ ↓ᴱ' =
          let
            a0 = li≡i i>>T HT
            a1 = subst (λ x → EnvExt x γ (lEnv T)) (a0) ext
          in
          steps (_ →ᴸ⟨ val-h-step ⟩ i>>T) HT (wk-wk WK) (ext-jmp a1) (wk-ext WK we) (wk-env-val-wk (v̲a̲r̲ i) ϖ) ↓ᴱ'
lookup Cx.h ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {ϖ = ϖ}) ↓ᴱ =
  steps (⟨ h ∥ γ ﹐﹝ W ╎ cs ﹞ ⟩ ◼) found-comp  (wk-wk wk-id)  env-comp (wk-ext wk-id (wk-eq wk-id)) (wk-env-comp-wk W cs enveq-id) (proj₂ ↓ᴱ)
lookup (Cx.t i) (γ ﹐ M) ↓ᴱ with lookup i γ (proj₁ ↓ᴱ)
... | steps {T = T} i>>T HT WK ext we ϖ ↓ᴱ' = steps (_ →ᴸ⟨ val-t-step ⟩ i>>T) HT (wk-wk WK) (ext-val ext) (wk-ext WK we) (wk-env-val-wk M ϖ) ↓ᴱ'
lookup (Cx.t i) (γ ﹐﹝ W ╎ cs ﹞) ↓ᴱ  with lookup i γ (proj₁ ↓ᴱ)
... | steps {T = T} i>>T HT WK ext we ϖ ↓ᴱ' =
  steps (_ →ᴸ⟨ (comp-t-step) ⟩ i>>T) HT (wk-wk WK) (ext-comp ext) (wk-ext WK we) (wk-env-comp-wk W cs ϖ) ↓ᴱ'

lookup-halt-lemma : (i : Γ' ∋ `V) → (γ : Env Γ Z₀) → (↓ᴱ : LookupEnvHalts γ) → (π : Wk Γ Γ') → (LabelHalts (v̲a̲r̲ (wk-mem π i)) γ)
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

data ValSteps : ValState T◾ Z₀ → Set where

  steps : {S T : ValState T◾ Z₀} → S ↠ᵛ T → (H : ValHaltingState T) → (π : Wk (botCtx T) (botCtx S))
          → WkExt π
          → EnvEq π (botEnv T) (botEnv S)
          → LookupEnvHalts (botEnv T)
          → LabelHalts (haltingTerm H) (botEnv T)
          → ValSteps S

val-eval-rec : (M : Γ' ⊢ᵛ X) → (γ : Env Γ Z₀) → (↓ᴱ : LookupEnvHalts γ) → (π : Wk Γ Γ') → ValSteps {T◾ = X} (∘ ((⇡ (wk-val π M) ⊲ γ ∷ □) {↥ = 🗆}))

val-eval-rec {X = `V} (var {A = .`V} i) γ ↓ᴱ π = steps (_ →ᵛ⟨ ∘var-c ⟩．) (∙ v̲a̲r̲ (wk-mem π i) ⊲ γ ■) wk-id (WkExt.wk-eq wk-id) enveq-id ↓ᴱ (lookup-halt-lemma i γ ↓ᴱ π)

val-eval-rec {X = `Unit} (var {A = .`Unit} i) γ ↓ᴱ π with lookup (wk-mem π i) γ ↓ᴱ
... | steps i>>T found-unit π₁ ext we ϖ ↓ᴸ =

            steps (_ →ᵛ⟨ ∘var i>>T π₁ ext we ϖ found-unit ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) wk-id (WkExt.wk-eq wk-id) enveq-id ↓ᴱ tt

val-eval-rec {X = X `× X₁} (var {A = .(X `× X₁)} i) γ ↓ᴱ π with lookup (wk-mem π i) γ ↓ᴱ
... | steps i>>T (found-pair {LHS = LHS} {RHS = RHS} {γ = γ₁}) π₁ ext we ϖ ↓ᴸ =

          steps

          (_ →ᵛ⟨ ∘var i>>T π₁ ext we ϖ found-pair ⟩．)

          (∙ pa̲i̲r̲ (wk-v̲a̲l̲ π₁ LHS) (wk-v̲a̲l̲ π₁ RHS) ⊲ γ ■)

          wk-id

          (WkExt.wk-eq wk-id)

          enveq-id

          ↓ᴱ

          (wk-LabelHalts LHS _ γ₁ π₁ we ϖ (proj₁ ↓ᴸ) , wk-LabelHalts RHS _ (lTEnv LookupState.⟨ h ∥ γ₁ Env.﹐ pa̲i̲r̲ LHS RHS ⟩) π₁ we ϖ (proj₂ ↓ᴸ))

val-eval-rec {Γ' = Γ'} {X = X `⇒ X₁} {Γ = Γ} (var {A = .(X `⇒ X₁)} i) γ ↓ᴱ π with lookup (wk-mem π i) γ ↓ᴱ

... | steps i>>T (found-lam {X = X₂} {Y = Y₂} {W = W} {γ = γ₁}) π₁ ext we ϖ ↓ᴸ =

          steps

          (_ →ᵛ⟨ ∘var i>>T π₁ ext we ϖ found-lam ⟩．)

          (∙ (wk-v̲a̲l̲ π₁ (l̲a̲m̲ W)) ⊲ γ ■)

          wk-id

          (WkExt.wk-eq wk-id)

          enveq-id

          ↓ᴱ

          tt

val-eval-rec (lam W) γ ↓ᴱ π =

          steps

          (∘ ⇡ (wk-val π (lam W)) ⊲ γ ∷ □ →ᵛ⟨ ∘lam ⟩．)

          (∙ l̲a̲m̲ (wk-comp (wk-cong π) W) ⊲ γ ■)

          wk-id

          (WkExt.wk-eq wk-id)

          enveq-id

          ↓ᴱ

          tt

val-eval-rec unit γ ↓ᴱ π = steps (_ →ᵛ⟨ ∘unit ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) wk-id (WkExt.wk-eq wk-id) enveq-id ↓ᴱ tt

val-eval-rec (pair {A = X} {B = Y} LHS RHS) γ ↓ᴱ π with val-eval-rec {X = X} LHS γ ↓ᴱ π
... | steps {T = ∙ (⭭_ {X = X} LT ⊲ γ₁ ∷ □) {↥ = 🗆}} L>T (∙ LT ⊲ γ₁ ■) πᴸ extᴸ ϖᴸ ↓ᴱ' ↓ᴸ' with val-eval-rec {X = Y} RHS γ₁ ↓ᴱ' (wk-trans πᴸ π)
... | steps {T = ∙ (⭭_ {X = Y} RT ⊲ γ₂ ∷ □) {↥ = 🗆}} R>T (∙ RT ⊲ γ₂ ■) πᴿ extᴿ ϖᴿ ↓ᴱ'' ↓ᴸ''  rewrite sym (wk-val-trans RHS πᴸ π) =

          steps

            (
            ∘ ⇡ (wk-val π (pair LHS RHS)) ⊲ γ ∷ □ →ᵛ⟨ ∘pair ⟩． ⨾
            (⟪ L>T ⟫⧻ (⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⊲ γ ∷ □)) ⨾
            (∙ ⭭ LT ⊲ γ₁ ∷ ⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⊲ γ ∷ □) →ᵛ⟨ ∙M∷l ϖᴸ L>T ⟩． ⨾
            (⟪ R>T ⟫⧻ (⇡ᴿ LT (wk-val πᴸ (wk-val π RHS)) ⊲ γ₁ ∷ □)) ⨾
            (∙ ⭭ RT ⊲ γ₂ ∷ ⇡ᴿ LT (wk-val πᴸ (wk-val π RHS)) ⊲ γ₁ ∷ □) →ᵛ⟨ ∙M∷r ϖᴿ R>T ⟩．
            )

            ∙ pa̲i̲r̲ (wk-v̲a̲l̲ πᴿ LT) RT ⊲ γ₂ ■

            (wk-trans πᴿ πᴸ)

            (wk-ext-trans extᴿ extᴸ)

            (env-eq-trans ϖᴿ ϖᴸ)

            ↓ᴱ''

            (wk-LabelHalts LT _ γ₁ πᴿ extᴿ ϖᴿ ↓ᴸ' , ↓ᴸ'')

val-eval-rec {Γ = Γ} (pm {A = A} {B = B} M N) γ ↓ᴱ π with val-eval-rec M γ ↓ᴱ π
... | steps {S = S} M>T (∙ pa̲i̲r̲ LHS RHS ⊲ γ₁ ■) π₁ ext₁ ϖ₁ ↓ᴱ' (↓ᴸᴸ' , ↓ᴸᴿ') with val-eval-rec N (_﹐_ (_﹐_ γ₁ LHS) (wk-v̲a̲l̲ (wk-wk wk-id) RHS)) ((↓ᴱ' , ↓ᴸᴸ') , wk-LabelHalts RHS (γ₁ ﹐ LHS) γ₁ (wk-wk wk-id) (WkExt.wk-ext wk-id (WkExt.wk-eq wk-id)) (EnvEq.wk-env-val-wk LHS enveq-id) ↓ᴸᴿ') ((wk-cong (wk-cong (wk-trans π₁ π)))) | (wk-val-trans N (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π)))
...    | steps {T = T} N>T ∙T π₂ ext₂ ϖ₂ ↓ᴱ'' ↓ᴸ'' | eq with N>T
...      | N>T' rewrite sym eq =

      steps
        (
          (∘ ⇡ pm (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⊲ γ ∷ □) →ᵛ⟨ ∘pm ⟩． ⨾
          (⟪ M>T ⟫⧻ (⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⊲ γ ∷ □)) ⨾
          (∙ ⭭ pa̲i̲r̲ LHS RHS ⊲ γ₁ ∷ ⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⊲ γ ∷ □) →ᵛ⟨ ∙pair∷pm ϖ₁ M>T ⟩． ⨾
          N>T'
        )

        ∙T

        (wk-trans π₂ (wk-wk (wk-wk π₁)))

        (wk-ext-trans ext₂ (WkExt.wk-ext (wk-wk π₁) (WkExt.wk-ext π₁ ext₁)))

        (env-eq-trans ϖ₂ (EnvEq.wk-env-val-wk (wk-v̲a̲l̲ (wk-wk wk-id) RHS) (EnvEq.wk-env-val-wk LHS ϖ₁)))

        ↓ᴱ''

        ↓ᴸ''

val-eval : (M : ε ⊢ᵛ X) → ValSteps {T◾ = X} {Z₀ = Z₀} (∘ ((⇡ wk-val wk-id M ⊲ ∗ ∷ □) {↥ = 🗆}))
val-eval M = val-eval-rec M ∗ tt wk-id

{-# TERMINATING #-}
mutual
  app-eval-rec :   (M : Γ' ⊢ᵛ X `⇒ Y) → (N : V̲a̲l̲ Γ X) → (γ : Env Γ Z₀) → (↓ᴸ : LabelHalts N γ) → (↓ᴱ : LookupEnvHalts γ) → (π : Wk Γ Γ') → (cs : CompStack Δ Y Z₀) → (πₓ : Wk Γ Δ)
                  → (ϖ₀ : EnvEq πₓ γ (topCsEnv cs))
                  → CompSteps ((∙⟨ (a̲pp (wk-val π M) N) ⊰ γ ╎ cs ⟩) {π = πₓ} {ϖ = ϖ₀})

  app-eval-rec (var i) N γ ↓ᴸ ↓ᴱ π cs πₓ ϖ₀ with lookup (wk-mem π i) γ ↓ᴱ
  ... | steps i>>T (found-lam {X = X} {W = W} {γ = γ₁}) π₁ ext we ϖ ↓ᴱ' with comp-eval-rec W (γ ﹐ N) (↓ᴱ , ↓ᴸ) (wk-cong π₁) cs (wk-wk πₓ) (wk-env-val-wk N ϖ₀)
  ... | steps {T = T} W>WT HT =

                steps ((∙⟨ a̲pp (wk-val π (var i)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-var {ϖₓ = ϖ₀} i>>T π₁ ⟩ W>WT)) HT


  app-eval-rec (lam W) N γ ↓ᴸ ↓ᴱ π cs πₓ ϖ₀ with comp-eval-rec W (γ ﹐ N) (↓ᴱ , ↓ᴸ) (wk-cong π) cs (wk-wk πₓ) (EnvEq.wk-env-val-wk N ϖ₀)
  ... | steps {T = T} W>WT HT =

                steps ( ∙⟨ a̲pp (wk-val π (lam W)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-lam {ϖₓ = ϖ₀} ⟩ W>WT) HT

  app-eval-rec (pm M₁ N₁) N γ ↓ᴸ ↓ᴱ π cs πₓ ϖ₀ with val-eval-rec M₁ γ ↓ᴱ π
  ... | steps {T = ∙ ((⭭ pa̲i̲r̲ {X = X} {Y = Y} LHS RHS) ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T (∙ (pa̲i̲r̲ {X = X} {Y = Y} LHS RHS) ⊲ γ₁ ■) π' ext₁ ϖ₁ ↓ᴱ' ↓ᴸ' with wk-val-trans N₁ (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
  ...       | eq with
                  app-eval-rec
                    N₁
                    ((wk-v̲a̲l̲ (wk-wk (wk-wk π')) N))
                    (γ₁ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS)
                    (wk-LabelHalts N (γ₁ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS) γ (wk-wk (wk-wk π')) (WkExt.wk-ext (wk-wk π') (WkExt.wk-ext π' ext₁)) (wk-env-val-wk (wk-v̲a̲l̲ (wk-wk wk-id) RHS) (wk-env-val-wk LHS ϖ₁)) ↓ᴸ)
                    ((↓ᴱ' , proj₁ ↓ᴸ') , wk-LabelHalts RHS (γ₁ ﹐ LHS) γ₁ (wk-wk wk-id) (WkExt.wk-ext wk-id (WkExt.wk-eq wk-id)) (wk-env-val-wk LHS enveq-id) (proj₂ ↓ᴸ'))
                    (wk-cong (wk-cong (wk-trans π' π)))
                    cs
                    (wk-wk (wk-wk (wk-trans π' πₓ)))
                    (wk-env-val-wk (wk-v̲a̲l̲ (wk-wk wk-id) RHS) (wk-env-val-wk LHS (env-eq-trans ϖ₁ ϖ₀)))
  ...          | steps {T = T} N>NT NT rewrite (sym eq) =

                steps (∙⟨ (a̲pp (wk-val π (pm M₁ N₁)) N) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-pm {ϖₓ = ϖ₀} {ϖₓ' = env-eq-trans ϖ₁ ϖ₀} M>T π' ⟩ N>NT) NT

  comp-eval-rec : (W : Γ' ⊢ᶜ X) → (γ : Env Γ Z₀) → (↓ᴱ : LookupEnvHalts γ) → (π : Wk Γ Γ') → (cs : CompStack Δ X Z₀) → (πₓ : Wk Γ Δ)
                → (ϖ₀ : EnvEq πₓ γ (topCsEnv cs))
                → CompSteps ((∘⟨ wk-comp π W ⊰ γ ╎ cs ⟩) {π = πₓ} {ϖ = ϖ₀})

  comp-eval-rec (return {A = X} M) γ ↓ᴱ π ◻ πₓ ϖ₀ with val-eval-rec {X = X} M γ ↓ᴱ π
  ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T π' ext₁ ϖ₁ _ _ =
                steps (∘⟨ wk-comp π (return M) ⊰ γ ╎ ◻ ⟩ →ᶜ⟨ ∘return {πₓ' = wk-wk-ε} {ϖₓ = ϖ₀} {ϖₓ' = env-wk-wk-ε γ₁} M>T ⟩ (∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ ◻ ⟩ ◼)) ret

  comp-eval-rec (return {A = X} M) γ ↓ᴱ π ((M' ⊲ γ' ⦂⦂ cs) {π = π₁} {ϖ = ϖ}) πₓ ϖ₀ with val-eval-rec {X = X} M γ ↓ᴱ π
  ... | steps {T = ∙ ((⭭ M₁) ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T (∙ M₁ ⊲ γ₁ ■) π' ext₁ ϖ₁ ↓ᴱ₁ ↓ᴸ₁ with
                comp-eval-rec M' (γ₁ ﹐ M₁) (↓ᴱ₁ , ↓ᴸ₁) (wk-cong (wk-trans π' πₓ)) cs (wk-wk (wk-trans (wk-trans π' πₓ) π₁)) (env-eq-trans (EnvEq.wk-env-val-wk M₁ (env-eq-trans ϖ₁ ϖ₀)) ϖ)
  ... | steps {T = (∙⟨ r̲e̲t̲u̲r̲n̲  M₂ ⊰ γ₂ ╎ ◻ ⟩) {ϖ = ϖ₂}} M'>T ret =

                  steps

                  (∘⟨ wk-comp π (return M) ⊰ γ ╎ (M' ⊲ γ' ⦂⦂ cs) ⟩
                  →ᶜ⟨ ∘return {ϖₓ = ϖ₀} {ϖₓ' = env-eq-trans ϖ₁ ϖ₀} M>T ⟩ ((∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ M' ⊲ γ' ⦂⦂ cs ⟩) {ϖ = env-eq-trans ϖ₁ ϖ₀})
                  →ᶜ⟨ ∙return {πₓ = wk-trans (wk-trans π' πₓ) π₁} {πₓ' = π₁} {ϖₓ = env-eq-trans ϖ₁ ϖ₀} {ϖₓ' = env-eq-trans (env-eq-trans ϖ₁ ϖ₀) ϖ} ⟩ M'>T)

                  ret

  comp-eval-rec (pm {A = X} {B = Y} M W) γ ↓ᴱ π cs πₓ ϖ₀ with val-eval-rec {X = X `× Y} M γ ↓ᴱ π
  ...  | steps {T = ∙ ((⭭_ {X = X `× Y} (pa̲i̲r̲ LHS RHS) ⊲ γ' ∷ □) {↥ = 🗆})} M>T (∙ (pa̲i̲r̲ {X = X} {Y = Y} LHS RHS) ⊲ γ' ■) π' ext₁ ϖ₁ ↓ᴱ₁ ↓ᴸ₁ with
                  comp-eval-rec
                    W
                    (γ' ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS)
                    ((↓ᴱ₁ , proj₁ ↓ᴸ₁) , wk-LabelHalts RHS (γ' ﹐ LHS) γ' (wk-wk wk-id) (WkExt.wk-ext wk-id (WkExt.wk-eq wk-id)) (EnvEq.wk-env-val-wk LHS enveq-id) (proj₂ ↓ᴸ₁))
                    (wk-trans (wk-cong (wk-cong π')) (wk-cong (wk-cong π)))
                    cs
                    (wk-wk (wk-wk (wk-trans π' πₓ)))
                    (wk-env-val-wk (wk-v̲a̲l̲ (wk-wk wk-id) RHS) (wk-env-val-wk LHS ((env-eq-trans ϖ₁ ϖ₀))))
  ...   | steps {T = T} W>T HT with wk-comp-trans W (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
  ...     | eq rewrite (sym eq) = steps (∘⟨ wk-comp π (pm M W) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘pm {ϖₓ = ϖ₀} {ϖₓ' = env-eq-trans ϖ₁ ϖ₀} π M>T π' ⟩ W>T) HT

  comp-eval-rec (push W V) γ ↓ᴱ π cs πₓ ϖ₀ with comp-eval-rec W γ ↓ᴱ π (((wk-comp (wk-cong π) V) ⊲ γ ⦂⦂ cs) {ϖ = ϖ₀}) wk-id enveq-id
  ... | steps {T = ∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ₁ ╎ ◻ ⟩} W>T ret = steps (∘⟨ push (wk-comp π W) (wk-comp (wk-cong π) V) ⊰ γ ╎ cs ⟩  →ᶜ⟨ ∘push {ϖₓ = ϖ₀} ⟩ W>T) ret

  comp-eval-rec (app M N) γ ↓ᴱ π cs πₓ ϖ₀ with val-eval-rec N γ ↓ᴱ π
  ... | steps {T = ∙ ((⭭ NT) ⊲ γᴺ ∷ □) {↥ = 🗆}} N>NT (∙ NT ⊲ γᴺ ■) πᴺ extᴺ ϖ₁ ↓ᴱ₁ ↓ᴸ₁ with app-eval-rec M NT γᴺ ↓ᴸ₁ ↓ᴱ₁ (wk-trans πᴺ π) cs (wk-trans πᴺ πₓ) (env-eq-trans ϖ₁ ϖ₀)
  ... | steps {T = T} W>WT HT rewrite (sym (wk-val-trans M πᴺ π)) =
          steps ((∘⟨ app (wk-val π M) (wk-val π N) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘app {ϖₓ = ϖ₀} {ϖₓ' = env-eq-trans ϖ₁ ϖ₀} N>NT πᴺ ⟩ W>WT )) HT

  comp-eval-rec (var {A = X} M) γ ↓ᴱ π cs πₓ ϖ₀ with val-eval-rec {X = `V} M γ ↓ᴱ π
  ... | steps {T = ∙ ((⭭ v̲a̲r̲ i) ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T (∙ M₁ ⊲ γ₂ ■) π' ext₁ ϖ₁ ↓ᴱ₁ ↓ᴸ₁ with lookup i γ₁ ↓ᴱ₁
  ... | steps i>>T (found-comp {X = X} {W = W'} {γ = γ'} {cs = cs'} {π = πᶜ} {ϖ = ϖc}) π₂ ext we ϖ record { target-state = ∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ CompStack.◻ ⟩ ; target-is-halting = ret ; trace = trace } =
              steps ((∘⟨ var (wk-val π M) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘var {ϖₓ = ϖ₀} M>T π' i>>T π₂ ⟩ trace)) ret

  comp-eval-rec (sub W V) γ ↓ᴱ π cs πₓ ϖ₀ with
    comp-eval-rec W ((γ ﹐﹝ wk-comp π V ╎ cs ﹞) {π = πₓ} {ϖ = ϖ₀})
      (↓ᴱ ,
        let
          IH = comp-eval-rec V γ ↓ᴱ π cs πₓ ϖ₀
          csh = get-csteps IH
        in
        record
          { target-state = proj₁ csh
          ; target-is-halting = proj₁ (proj₂ csh)
          ; trace = proj₂ (proj₂ csh)
          })
      (wk-cong π) cs (wk-wk πₓ) (wk-env-comp-wk (wk-comp π V) cs ϖ₀)
  ... | steps {T = T} W>WT HT =

              steps

                  (∘⟨ sub (wk-comp (wk-cong π) W) (wk-comp π V) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘sub ⟩ W>WT)

                  HT

  comp-eval : (W : ε ⊢ᶜ Z₀) → CompSteps ((∘⟨ wk-comp wk-id W ⊰ ∗ ╎ ◻ ⟩) {π = wk-id} {ϖ = EnvEq.wk-env-ε})
  comp-eval W = comp-eval-rec W ∗ tt wk-id ◻ wk-id EnvEq.wk-env-ε

---- Examples

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

-- s/\(PartialTerm\.\|ValStack\.\|Env\.\|V̲a̲l̲\.\|CompStack\.\|ValStack\.\|ValState\.\|_↠ᵛ_\.\|_→ᵛ_\.\|_→ᴸ\*_\.\|_→ᴸ_\.\|LookupState\.\|C̲o̲m̲p.\)//g

_ : comp-eval ex15 ≡

 steps

  ( ∘⟨ push (push (app (lam (sub (var (var h)) (return unit))) unit) (return unit)) (return unit) ⊰ ∗ ╎ ◻ ⟩
  →ᶜ⟨ ∘push ⟩
    ∘⟨ push (app (lam (sub (var (var h)) (return unit))) unit) (return unit) ⊰ ∗ ╎ return unit ⊲ ∗ ⦂⦂ ◻ ⟩
  →ᶜ⟨ ∘push ⟩
    ∘⟨ app (lam (sub (var (var h)) (return unit))) unit ⊰ ∗ ╎ return unit ⊲ ∗ ⦂⦂ (return unit ⊲ ∗ ⦂⦂ ◻) ⟩
  →ᶜ⟨ ∘app (∘ ⇡ unit ⊲ ∗ ∷ □ →ᵛ⟨ ∘unit ⟩．) wk-ε ⟩
    ∙⟨ a̲pp (lam (sub (var (var h)) (return unit))) u̲n̲i̲t̲ ⊰ ∗ ╎ return unit ⊲ ∗ ⦂⦂ (return unit ⊲ ∗ ⦂⦂ ◻) ⟩
  →ᶜ⟨ ∙app-lam ⟩
    ∘⟨ sub (var (var h)) (return unit) ⊰ ∗ ﹐ u̲n̲i̲t̲ ╎ return unit ⊲ ∗ ⦂⦂ (return unit ⊲ ∗ ⦂⦂ ◻) ⟩
  →ᶜ⟨ ∘sub ⟩
    ∘⟨ var (var h) ⊰ ∗ ﹐ u̲n̲i̲t̲ ﹐﹝ return unit ╎ return unit ⊲ ∗ ⦂⦂ (return unit ⊲ ∗ ⦂⦂ ◻) ﹞ ╎ return unit ⊲ ∗ ⦂⦂ (return unit ⊲ ∗ ⦂⦂ ◻) ⟩
  →ᶜ⟨ ∘var (∘ ⇡ var h ⊲ ∗ ﹐ u̲n̲i̲t̲ ﹐﹝ return unit ╎ return unit ⊲ ∗ ⦂⦂ (return unit ⊲ ∗ ⦂⦂ ◻) ﹞ ∷ □ →ᵛ⟨ ∘var-c ⟩．) (wk-cong (wk-cong wk-ε)) (⟨ h ∥ ∗ ﹐ u̲n̲i̲t̲ ﹐﹝ return unit ╎ return unit ⊲ ∗ ⦂⦂ (return unit ⊲ ∗ ⦂⦂ ◻) ﹞ ⟩ _→ᴸ*_.◼) (wk-wk (wk-cong wk-ε)) ⟩
    ∘⟨ return unit ⊰ ∗ ﹐ u̲n̲i̲t̲ ╎ return unit ⊲ ∗ ⦂⦂ (return unit ⊲ ∗ ⦂⦂ ◻) ⟩
  →ᶜ⟨ ∘return (∘ ⇡ unit ⊲ ∗ ﹐ u̲n̲i̲t̲ ∷ □ →ᵛ⟨ ∘unit ⟩．) ⟩
    ∙⟨ r̲e̲t̲u̲r̲n̲ u̲n̲i̲t̲ ⊰ ∗ ﹐ u̲n̲i̲t̲ ╎ return unit ⊲ ∗ ⦂⦂ (return unit ⊲ ∗ ⦂⦂ ◻) ⟩
  →ᶜ⟨ ∙return ⟩
    ∘⟨ return unit ⊰ ∗ ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ╎ return unit ⊲ ∗ ⦂⦂ ◻ ⟩ →ᶜ⟨ ∘return (∘ ⇡ unit ⊲ ∗ ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ∷ □ →ᵛ⟨ ∘unit ⟩．) ⟩ ∙⟨ r̲e̲t̲u̲r̲n̲ u̲n̲i̲t̲ ⊰ ∗ ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ╎ return unit ⊲ ∗ ⦂⦂ ◻ ⟩ →ᶜ⟨ ∙return ⟩ ∘⟨ return unit ⊰ ∗ ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ╎ ◻ ⟩
  →ᶜ⟨ ∘return (∘ ⇡ unit ⊲ ∗ ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ∷ □ →ᵛ⟨ ∘unit ⟩．) ⟩
   (∙⟨ r̲e̲t̲u̲r̲n̲ u̲n̲i̲t̲ ⊰ ∗ ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ╎ ◻ ⟩ ◼))

  ret

_ = refl
