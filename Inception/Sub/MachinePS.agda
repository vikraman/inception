{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.MachinePS where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Function.Base using (const; _∘_; _$_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; cong-app; dcong₂; sym; trans; subst; subst₂)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax

open import Data.Unit
open import Data.Nat
open import Data.List using (List; _∷_; []; _++_)

open import Inception.Sub.Equality

open import Inception.Sub.EnvironmentsPS
open import Inception.Sub.StatesPS

-----------------------------------------------------------------------

private
  variable
    Γ₀ : Ctx
    Z₀ : Ty

infixr 17 _→ᵛ⟨_⟩．
infixr 15 _→ᵛ⟨_⟩_
infix  15 _→ᵛ_
infix  15 _→ᴸ_
infixr 10 _⨾_

------------------------------------------------------------------------------
-- Lookup Machine
------------------------------------------------------------------------------
data _→ᴸ_ : LookupState Γ X Z₀ → LookupState Γ' X Z₀ → Set where

    val-h-step    : {E : Env Γ Z₀} → {i : Γ ∋ `V} → ⟨ h  ∥ E ﹐ (v̲a̲r̲ i) ⟩ →ᴸ ⟨ i ∥ E ⟩

    val-t-step    : {i : Γ ∋ Y} → {E : Env Γ Z₀} → {M : V̲a̲l̲ Γ X} → ⟨ t i  ∥ _﹐_ E M ⟩ →ᴸ ⟨ i ∥ E ⟩

    comp-t-step   : {i : Γ ∋ Y} → {γ : Env Γ Z₀} → {W : Γ ⊢ᶜ X} → {cs : CompStack Δ X Z₀} → ⟨ t i  ∥ (_﹐﹝_╎_﹞ γ W cs) ⟩ →ᴸ ⟨ i ∥ γ ⟩

data _→ᴸ*_ : LookupState Γ X Z₀ → LookupState Γ' X Z₀ → Set where

  _◼ : (S : LookupState Γ X Z₀) → S →ᴸ* S

  _→ᴸ⟨_⟩_ : (S : LookupState (Γ ∙ Y) X Z₀) → {S' : LookupState Γ X Z₀} → {S'' : LookupState Γ'' X Z₀} → S →ᴸ S' → S' →ᴸ* S'' → S →ᴸ* S''

data LookupHaltingState : LookupState Γ X Z₀ → Set where

      found-unit : {γ : Env Γ Z₀} → LookupHaltingState ⟨ h ∥ _﹐_ γ u̲n̲i̲t̲ ⟩

      found-pair : {LHS : V̲a̲l̲ Γ X} → {RHS : V̲a̲l̲ Γ Y} → {γ : Env Γ Z₀} → LookupHaltingState ⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩

      found-lam : {W : (Γ ∙ X) ⊢ᶜ Y} → {γ : Env Γ Z₀} → LookupHaltingState ⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩

      found-comp : {W : Γ ⊢ᶜ X} → {γ : Env Γ Z₀} → {cs : CompStack Δ X Z₀} → LookupHaltingState ⟨ h ∥ (_﹐﹝_╎_﹞ γ W cs) ⟩

lookup-index : {S : LookupState Γ X Z₀} → {T : LookupState Γ' X Z₀} → S →ᴸ* T → (lCtx S) ∋ X
lookup-index (⟨ i ∥ _ ⟩ ◼) = i
lookup-index (⟨ h ∥ E ﹐ v̲a̲r̲ i ⟩ →ᴸ⟨ val-h-step ⟩ S→T) = h
lookup-index (⟨ t i ∥ _ ⟩ →ᴸ⟨ val-t-step ⟩ S→T) = t (lookup-index S→T)
lookup-index (⟨ t i ∥ _ ⟩ →ᴸ⟨ comp-t-step ⟩ S→T) = t (lookup-index S→T)

li≡i : {T : LookupState Γ' X Z₀} {γ : Env Γ Z₀} {i : Γ ∋ X} → (S→T : ⟨ i ∥ γ ⟩ →ᴸ* T) → LookupHaltingState T → lookup-index S→T ≡ i
li≡i (S ◼) found-unit = refl
li≡i (S ◼) found-pair = refl
li≡i (S ◼) found-lam = refl
li≡i (S ◼) found-comp = refl
li≡i (S →ᴸ⟨ val-t-step ⟩ S→T) found-unit = cong t (li≡i S→T found-unit)
li≡i (S →ᴸ⟨ comp-t-step ⟩ S→T) found-unit = cong t (li≡i S→T found-unit)
li≡i (S →ᴸ⟨ val-t-step ⟩ S→T) found-pair = cong t (li≡i S→T found-pair)
li≡i (S →ᴸ⟨ comp-t-step ⟩ S→T) found-pair = cong t (li≡i S→T found-pair)
li≡i (S →ᴸ⟨ val-t-step ⟩ S→T) found-lam = cong t (li≡i S→T found-lam)
li≡i (S →ᴸ⟨ comp-t-step ⟩ S→T) found-lam = cong t (li≡i S→T found-lam)
li≡i (S →ᴸ⟨ val-h-step ⟩ S→T) found-comp = refl
li≡i (S →ᴸ⟨ val-t-step ⟩ S→T) (found-comp) = cong t (li≡i S→T (found-comp))
li≡i (S →ᴸ⟨ comp-t-step ⟩ S→T) (found-comp) = cong t (li≡i S→T (found-comp))

lstep-ext : {i₁ : Γ₁ ∋ X} {γ₁ : Env Γ₁ Z₀} {γ₂ : Env (Γ₂ ∙ X) Z₀} → ⟨ i₁ ∥ γ₁ ⟩ →ᴸ* ⟨ h ∥ γ₂ ⟩ → EnvExt i₁ γ₁ γ₂
lstep-ext (⟨ h ∥ γ₁ ⟩ ◼) = envext-id
lstep-ext (S →ᴸ⟨ val-h-step ⟩ L→T) = ext-jmp (lstep-ext L→T)
lstep-ext (S →ᴸ⟨ val-t-step ⟩ L→T) = ext-val (lstep-ext L→T)
lstep-ext (S →ᴸ⟨ comp-t-step ⟩ L→T) = ext-comp (lstep-ext L→T)

------------------------------------------------------------------------------
-- Value Machine
------------------------------------------------------------------------------

-------

{-
-- THIS CODE DOES THE SAME THING AS THE VALUE MACHINE

record Traversal (Γ : Ctx) (X : Ty) (Z₀ : Ty) (γ : Env Γ Z₀): Set where
  field
    Γₘₐₓ : Ctx
    γₘₐₓ : Env Γₘₐₓ Z₀
    πₘₐₓ : Wk Γₘₐₓ Γ
    ϖₘₐₓ : EnvEq πₘₐₓ γₘₐₓ γ
    result : V̲a̲l̲ Γₘₐₓ X

open Traversal

p₁ : V̲a̲l̲ Γ (X `× Y) →  V̲a̲l̲ Γ X
p₁ (pa̲i̲r̲ W₁ W₂) = W₁

p₂ : V̲a̲l̲ Γ (X `× Y) →  V̲a̲l̲ Γ Y
p₂ (pa̲i̲r̲ W₁ W₂) = W₂

mutual
  traverseˡ : Γ' ∋ X → (π₀ : Wk Γ₀ Γ) → Wk Γ Γ' → (γ₀ : Env Γ₀ Z₀) → (γ : Env Γ Z₀) → EnvEq π₀ γ₀ γ → Traversal Γ X Z₀ γ
  traverseˡ {Γ₀ = Γ₀} Cx.h π₀ (wk-cong π) γ₀ (γ ﹐ M) ϖ = record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; ϖₘₐₓ = ϖ ; result = wk-v̲a̲l̲ (wk-trans π₀ (wk-wk wk-id)) M }
  traverseˡ {Γ₀ = Γ₀} Cx.h π₀ (wk-cong π) γ₀ (γ ﹐﹝ W ╎ cs ﹞) ϖ = record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; ϖₘₐₓ = ϖ ; result = wk-v̲a̲l̲ π₀ (v̲a̲r̲ h) }
  traverseˡ {X = X} {Γ₀ = Γ₀} Cx.h π₀ (wk-wk π) γ₀ (γ ﹐ M) ϖ =
    let
      IH = traverseˡ {Γ₀ = Γ₀} Cx.h (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ (env-eq-trans ϖ (wk-env-val-wk M enveq-id))
      r = subst (λ x →  V̲a̲l̲ x X) (Γₘₐₓ≡Γ₀ Γ₀ Cx.h (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ (env-eq-trans ϖ (wk-env-val-wk M enveq-id))) (result IH)
    in
    record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; ϖₘₐₓ = ϖ ; result = r }
  traverseˡ {X = X} {Γ₀ = Γ₀} Cx.h π₀ (wk-wk π) γ₀ (γ ﹐﹝ W ╎ cs ﹞) ϖ =
    let
      IH = traverseˡ {Γ₀ = Γ₀} Cx.h (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ (env-eq-trans ϖ (wk-env-comp-wk W cs enveq-id))
      r = subst (λ x →  V̲a̲l̲ x X) (Γₘₐₓ≡Γ₀ Γ₀ Cx.h (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ (env-eq-trans ϖ (wk-env-comp-wk W cs enveq-id))) (result IH)
    in
    record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; ϖₘₐₓ = ϖ ; result = r}
  traverseˡ {X = X} {Γ₀ = Γ₀} (Cx.t i) π₀ (wk-cong π) γ₀ (γ ﹐ M) ϖ =
    let
      IH = traverseˡ {Γ₀ = Γ₀} i (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ (env-eq-trans ϖ (wk-env-val-wk M enveq-id))
      r = subst (λ x →  V̲a̲l̲ x X) (Γₘₐₓ≡Γ₀ Γ₀ i (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ (env-eq-trans ϖ (wk-env-val-wk M enveq-id))) (result IH)
    in
    record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; ϖₘₐₓ = ϖ ; result = r }
  traverseˡ {X = X} {Γ₀ = Γ₀} (Cx.t i) π₀ (wk-cong π) γ₀ (γ ﹐﹝ W ╎ cs ﹞) ϖ =
    let
      IH = traverseˡ {Γ₀ = Γ₀} i (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ (env-eq-trans ϖ (wk-env-comp-wk W cs enveq-id))
      r = subst (λ x →  V̲a̲l̲ x X) (Γₘₐₓ≡Γ₀ Γ₀ i (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ (env-eq-trans ϖ (wk-env-comp-wk W cs enveq-id))) (result IH)
    in
    record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; ϖₘₐₓ = ϖ ; result = r }
  traverseˡ {X = X} {Γ₀ = Γ₀} (Cx.t i) π₀ (wk-wk π) γ₀ (γ ﹐ M) ϖ =
    let
      IH = traverseˡ {Γ₀ = Γ₀} (t i) (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ (env-eq-trans ϖ (wk-env-val-wk M enveq-id))
      r = subst (λ x →  V̲a̲l̲ x X) (Γₘₐₓ≡Γ₀ Γ₀ (t i) (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ (env-eq-trans ϖ (wk-env-val-wk M enveq-id))) (result IH)
    in
    record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; ϖₘₐₓ = ϖ ; result = r}
  traverseˡ {X = X} {Γ₀ = Γ₀} (Cx.t i) π₀ (wk-wk π) γ₀ (γ ﹐﹝ W ╎ cs ﹞) ϖ =
    let
      IH = traverseˡ {Γ₀ = Γ₀} (t i) (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ (env-eq-trans ϖ (wk-env-comp-wk W cs enveq-id))
      r = subst (λ x →  V̲a̲l̲ x X) (Γₘₐₓ≡Γ₀ Γ₀ (t i) (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ (env-eq-trans ϖ (wk-env-comp-wk W cs enveq-id))) (result IH)
    in
    record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; ϖₘₐₓ = ϖ ; result = r}

  Γₘₐₓ≡Γ₀ : (Γ₀ : Ctx) → (i : Γ' ∋ X) → (π₀ : Wk Γ₀ Γ) → (π : Wk Γ Γ') → (γ₀ : Env Γ₀ Z₀) → (γ : Env Γ Z₀) → (ϖ : EnvEq π₀ γ₀ γ) → Γₘₐₓ (traverseˡ {Γ₀ = Γ₀} i π₀ π γ₀ γ ϖ) ≡ Γ₀
  Γₘₐₓ≡Γ₀ Γ₀ Cx.h π₀ (wk-cong π) γ₀ (γ ﹐ M) ϖ = refl
  Γₘₐₓ≡Γ₀ Γ₀ Cx.h π₀ (wk-cong π) γ₀ (γ ﹐﹝ W ╎ cs ﹞) ϖ = refl
  Γₘₐₓ≡Γ₀ Γ₀ Cx.h π₀ (wk-wk π) γ₀ (γ ﹐ M) ϖ = refl
  Γₘₐₓ≡Γ₀ Γ₀ Cx.h π₀ (wk-wk π) γ₀ (γ ﹐﹝ W ╎ cs ﹞) ϖ = refl
  Γₘₐₓ≡Γ₀ Γ₀ (Cx.t i) π₀ (wk-cong π) γ₀ (γ ﹐ M) ϖ = refl
  Γₘₐₓ≡Γ₀ Γ₀ (Cx.t i) π₀ (wk-cong π) γ₀ (γ ﹐﹝ W ╎ cs ﹞) ϖ = refl
  Γₘₐₓ≡Γ₀ Γ₀ (Cx.t i) π₀ (wk-wk π) γ₀ (γ ﹐ M) ϖ = refl
  Γₘₐₓ≡Γ₀ Γ₀ (Cx.t i) π₀ (wk-wk π) γ₀ (γ ﹐﹝ W ╎ cs ﹞) ϖ = refl

traverseᵛ : Val Γ' X → Wk Γ Γ' → (γ : Env Γ Z₀) → Traversal Γ X Z₀ γ
traverseᵛ (var i) π γ = traverseˡ i wk-id π γ γ enveq-id
traverseᵛ {Γ = Γ} (lam M) π γ =
  record { Γₘₐₓ = Γ ; γₘₐₓ = γ ; πₘₐₓ = wk-id ; ϖₘₐₓ = enveq-id ; result = l̲a̲m̲ (wk-comp (wk-cong π) M) }
traverseᵛ (pair W₁ W₂) π γ =
  let
    IH₁ = traverseᵛ W₁ π γ
    IH₂ = traverseᵛ W₂ (wk-trans (πₘₐₓ IH₁) π) (γₘₐₓ IH₁)
  in
  record { Γₘₐₓ = Γₘₐₓ IH₂ ; γₘₐₓ = γₘₐₓ IH₂ ; πₘₐₓ = wk-trans (πₘₐₓ IH₂) (πₘₐₓ IH₁) ; ϖₘₐₓ = env-eq-trans (ϖₘₐₓ IH₂) (ϖₘₐₓ IH₁) ; result = pa̲i̲r̲ (wk-v̲a̲l̲ (πₘₐₓ IH₂) (result IH₁)) (result IH₂) }
traverseᵛ (pm W₁ W₂) π γ =
  let
    IH = traverseᵛ W₁ π γ
    IH' = traverseᵛ W₂ (wk-cong (wk-cong (wk-trans (πₘₐₓ IH) π))) (γₘₐₓ IH ﹐ p₁ (result IH) ﹐ wk-v̲a̲l̲ (wk-wk wk-id) (p₂ (result IH)))
  in
  record { Γₘₐₓ = Γₘₐₓ IH' ; γₘₐₓ = γₘₐₓ IH' ; πₘₐₓ = wk-trans (πₘₐₓ IH') (wk-wk (wk-wk (πₘₐₓ IH))) ; ϖₘₐₓ = env-eq-trans (ϖₘₐₓ IH') (wk-env-val-wk (wk-v̲a̲l̲ (wk-wk wk-id) (p₂ (result IH))) (wk-env-val-wk (p₁ (result IH)) (ϖₘₐₓ IH))) ; result = result IH' }
traverseᵛ {Γ = Γ} unit π γ = record { Γₘₐₓ = Γ ; γₘₐₓ = γ ; πₘₐₓ = wk-id ; ϖₘₐₓ = enveq-id ; result = u̲n̲i̲t̲ }
-}

{-
data LookupSteps : LookupState Γ X Z₀ → Set where

  --steps : {S : LookupState Γ X Z₀} → {T : LookupState (Γ' ∙ Y) X Z₀} → (S→T : S →ᴸ* T) → (H : LookupHaltingState T) → (π : Wk (lCtx S) (lTCtx T)) → LookupSteps S
  steps : {S : LookupState Γ X Z₀} → {T : LookupState (Γ' ∙ Y) X Z₀} → (S→T : S →ᴸ* T) → (H : LookupHaltingState T) → (π : Wk Γ Γ') → LookupSteps S

  lookup-proj : {S : LookupState Γ X Z₀} → LookupSteps S → Σ[ Γ' ∈ Ctx ] Σ[ Y ∈ Ty ] (LookupState (Γ' ∙ Y) X Z₀ × Wk Γ Γ')
  lookup-proj (steps {Γ' = Γ'} {Y = Y} {T = T} S→T H π) = Γ' , Y , T , π
-}

record LookupSteps (start : LookupState Γ X Z₀) : Set where
  field
    target-ctx   : Ctx
    ty           : Ty
    target       : LookupState (target-ctx ∙ ty) X Z₀
    target-halts : LookupHaltingState target
    steps        : start →ᴸ* target
    weaken       : Wk Γ target-ctx
open LookupSteps

run-lookup : (i : Γ ∋ X) → (γ : Env Γ Z₀) → LookupSteps {X = X} ⟨ i ∥ γ ⟩
run-lookup {Γ = Γ ∙ X'} {X = X} Cx.h (γ ﹐ l̲a̲m̲ W) = record { target-ctx = Γ ; ty = X' ; target = ⟨ h ∥ γ ﹐ l̲a̲m̲ W ⟩ ; target-halts = found-lam ; steps = ⟨ h ∥ γ ﹐ l̲a̲m̲ W ⟩ ◼ ; weaken = wk-wk wk-id}
run-lookup {Γ = Γ ∙ X'} {X = X} Cx.h (γ ﹐ pa̲i̲r̲ LHS RHS) = record { target-ctx = Γ ; ty = X' ; target = ⟨ h ∥ γ ﹐ pa̲i̲r̲ LHS RHS ⟩ ; target-halts = found-pair ; steps = ⟨ h ∥ γ ﹐ pa̲i̲r̲ LHS RHS ⟩ ◼ ; weaken = wk-wk wk-id}
run-lookup {Γ = Γ ∙ X'} {X = X} Cx.h (γ ﹐ u̲n̲i̲t̲) = record { target-ctx = Γ ; ty = X' ; target = ⟨ h ∥ γ ﹐ u̲n̲i̲t̲ ⟩ ; target-halts = found-unit ; steps = ⟨ h ∥ γ ﹐ u̲n̲i̲t̲ ⟩ ◼ ; weaken = wk-wk wk-id}
run-lookup {Γ = Γ ∙ X'} {X = X} Cx.h (γ ﹐ v̲a̲r̲ i) =
  let IH = run-lookup i γ in
  record { target-ctx = target-ctx IH ; ty = ty IH ; target = target IH ; target-halts = target-halts IH ; steps = ⟨ h ∥ γ ﹐ v̲a̲r̲ i ⟩ →ᴸ⟨ val-h-step ⟩ steps IH ; weaken = wk-wk (weaken IH)}
run-lookup {Γ = Γ ∙ X'} {X = X} Cx.h ((γ ﹐﹝ W ╎ cs ﹞)) = record { target-ctx = Γ ; ty = X' ; target = ⟨ h ∥ γ ﹐﹝ W ╎ cs ﹞ ⟩ ; target-halts = found-comp ; steps = ⟨ h ∥ γ ﹐﹝ W ╎ cs ﹞ ⟩ ◼ ; weaken = wk-wk wk-id}
run-lookup {Γ = Γ ∙ X'} {X = X} (Cx.t i) (γ ﹐ M) =
  let IH = run-lookup i γ in
  record { target-ctx = target-ctx IH ; ty = ty IH ; target = target IH ; target-halts = target-halts IH ; steps = ⟨ t i ∥ γ ﹐ M ⟩ →ᴸ⟨ val-t-step ⟩ steps IH ; weaken = wk-wk (weaken IH)}
run-lookup {Γ = Γ ∙ X'} {X = X} (Cx.t i) (γ ﹐﹝ W ╎ cs ﹞) =
  let IH = run-lookup i γ in
  record { target-ctx = target-ctx IH ; ty = ty IH ; target = target IH ; target-halts = target-halts IH ; steps = ⟨ t i ∥ γ ﹐﹝ W ╎ cs ﹞ ⟩ →ᴸ⟨ comp-t-step ⟩ steps IH ; weaken = wk-wk (weaken IH)}

data NonJump : (X : Ty) → Set where
  isUnit : NonJump `Unit
  isProd : NonJump (X `× Y)
  isLam : NonJump (X `⇒ Y)

--get-pair : {S : LookupState (Γ ∙ (X `× Y)) (X `× Y) Z₀} → LookupHaltingState S → V̲a̲l̲ Γ (X `× Y)
--get-pair (found-pair {LHS = LHS} {RHS = RHS}) = pa̲i̲r̲ LHS RHS

get-pair : {S : LookupState Γ (X `× Y) Z₀} → (s : LookupSteps S) → V̲a̲l̲ (target-ctx s) (X `× Y)
get-pair {Γ = Γ} record { target-ctx = target-ctx₁ ; ty = ty₁ ; target = target₁ ; target-halts = found-pair {LHS = LHS} {RHS = RHS} ; steps = steps₁ ; weaken = weaken₁ } = pa̲i̲r̲ LHS RHS

--get-lam : {S : LookupState (Γ ∙ (X `⇒ Y)) (X `⇒ Y) Z₀} → LookupHaltingState S → V̲a̲l̲ Γ (X `⇒ Y)
--get-lam (found-lam {W = W}) = l̲a̲m̲ W

get-lam : {S : LookupState Γ (X `⇒ Y) Z₀} → (s : LookupSteps S) → V̲a̲l̲ (target-ctx s) (X `⇒ Y)
get-lam {Γ = Γ} record { target-ctx = target-ctx₁ ; ty = ty₁ ; target = target₁ ; target-halts = found-lam {W = W} ; steps = steps₁ ; weaken = weaken₁ } = l̲a̲m̲ W

lookup : (i : Γ ∋ X) → (γ : Env Γ Z₀) → (NonJump X) →  V̲a̲l̲ Γ X
lookup i γ isUnit = let rl = run-lookup i γ in wk-v̲a̲l̲ (weaken rl) u̲n̲i̲t̲
lookup i γ isProd = let rl = run-lookup i γ in wk-v̲a̲l̲ (weaken rl) (get-pair rl)
lookup i γ isLam = let rl = run-lookup i γ in wk-v̲a̲l̲ (weaken rl) (get-lam rl)

determinismᴸ : {S : LookupState Γ X Z₀} → {S' : LookupState Γ' X Z₀} → (S→S'₁ S→S'₂ : S →ᴸ S') → (S→S'₁ ≡ S→S'₂)
determinismᴸ val-h-step val-h-step = refl
determinismᴸ val-t-step val-t-step = refl
determinismᴸ comp-t-step comp-t-step = refl

data _↠ᵛ_ : ValState T◾ Z₀ → ValState T◾ Z₀ → Set

data _→ᵛ_ {T◾ : Ty} {Z₀ : Ty} : ValState T◾ Z₀ → ValState T◾ Z₀ → Set where

    ∘var-c  :    {γ : Env Γ Z₀} {i : Γ ∋ `V} → {tail : ValStack b T◾ Z₀} → {↥ : BottomTypeEqualsNextType b `V T◾}
              ----------------------------------------------------------------
                → ∘ ((⇡ var i ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((⭭ v̲a̲r̲ i ⊲ γ ∷ tail) {↥ = ↥})

    {-
    ∘var    :    {γ : Env Γ Z₀} {γ' : Env Γ' Z₀} {i : Γ ∋ X} → {tail : ValStack b T◾ Z₀} → {↥ : BottomTypeEqualsNextType b X T◾}
                → {M : V̲a̲l̲ Γ' X}
                → (i>>T : (⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ (γ' ﹐ M) ⟩)) → (πᵥ : Wk Γ Γ')
                -- not needed for correctness, but makes things easier:
                -- → EnvExt (lookup-index i>>T) γ (γ' ﹐ M)
                -- → WkExt πᵥ
                -- → EnvEq πᵥ γ γ'
                → LookupHaltingState ⟨ h ∥ (γ' ﹐ M) ⟩
              ----------------------------------------------------------------
                → ∘ ((⇡ var i ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((⭭ (wk-v̲a̲l̲ πᵥ M) ⊲ γ ∷ tail) {↥ = ↥})
    -}

    ∘var    :    {γ : Env Γ Z₀} {i : Γ ∋ X} {tail : ValStack b T◾ Z₀} → {↥ : BottomTypeEqualsNextType b X T◾} {nj : NonJump X}
                 {W : V̲a̲l̲ Γ X} {eq : W ≡ (lookup i γ nj)}
              ----------------------------------------------------------------
                → ∘ ((⇡ var i ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((⭭ W ⊲ γ ∷ tail) {↥ = ↥})


    ∘lam   :  {M : (Γ ∙ X) ⊢ᶜ Y} → {γ  : Env Γ Z₀}
            → {tail : ValStack b T◾ Z₀} → {↥ : BottomTypeEqualsNextType b (X `⇒ Y) T◾}
              ---------------------------------------------------------------------------
            →     ∘ ((⇡ lam M ⊲ γ ∷ tail) {↥ = ↥})
                →ᵛ ∙ ((⭭ l̲a̲m̲ M ⊲ γ ∷ tail) {↥ = ↥})

    ∘pair  :  {γ : Env Γ Z₀} {LHS : Γ ⊢ᵛ X} → {RHS : Γ ⊢ᵛ Y}
            → {tail : ValStack b T◾ Z₀} → {↥ : BottomTypeEqualsNextType b (X `× Y) T◾}
              ---------------------------------------------------------------------------
            →     ∘ ((⇡ pair LHS RHS ⊲ γ ∷ tail) {↥ = ↥})
                →ᵛ ∘ ((⇡ LHS ⊲ γ ∷ ((⇡ᴸ LHS RHS ⊲ γ ∷ tail) {↥ = ↥})) {↥ = 🗇})

    ∘pm    :  {γ : Env Γ Z₀} {M : Γ ⊢ᵛ X `× Y} → {N : (Γ ∙ X ∙ Y) ⊢ᵛ Z}
            → {tail : ValStack b T◾ Z₀} → {↥ : BottomTypeEqualsNextType b Z T◾}
              ---------------------------------------------------------------------------
            →     ∘ ((⇡ pm M N ⊲ γ ∷ tail) {↥ = ↥})
                →ᵛ ∘ ((⇡ M ⊲ γ ∷ (⇡ᴹ M N ⊲ γ ∷ tail) {↥ = ↥}) {↥ = 🗇})

    ∘unit  :  {γ  : Env Γ Z₀}
            → {tail : ValStack b T◾ Z₀} → {↥ : BottomTypeEqualsNextType b `Unit T◾}
              ---------------------------------------------------------------------------
            →     ∘ ((⇡ unit ⊲ γ ∷ tail) {↥ = ↥})
                →ᵛ ∙ ((⭭ u̲n̲i̲t̲ ⊲ γ ∷ tail) {↥ = ↥})

    ∙M∷l   :  {γ' : Env Γ' Z₀} {γ : Env Γ Z₀} {M : V̲a̲l̲ Γ X} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y} → {π' : Wk Γ Γ'} → {ext : WkExt π'}
            → {tail : ValStack b T◾ Z₀} → {↥ : BottomTypeEqualsNextType b (X `× Y) T◾} → {RHS' : Val Γ Y} → {eq : RHS' ≡ wk-val π' RHS}
            -- not needed for correctness, but makes things easier  --→ (LHS→M : (∘ (⇡ LHS ⊲ γ' ∷ □) {↥ = 🗆}) ↠ᵛ (∙ (⭭ M ⊲ γ ∷ □) {↥ = 🗆}))
              -- → (ϖ : EnvEq π' γ γ')
              -- → (∘ ((⇡ LHS ⊲ γ' ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ M ⊲ γ ∷ □) {↥ = 🗆}))
              --→ traverseᵛ LHS wk-id γ' ≡ record { Γₘₐₓ = Γ ; γₘₐₓ = γ ; πₘₐₓ = π' ; ϖₘₐₓ = ϖ ; result = M }
              ---------------------------------------------------------------------------
            →     ∙ ((⭭ M ⊲ γ ∷ ((⇡ᴸ LHS RHS ⊲ γ' ∷ tail) {↥ = ↥})) {↥ = 🗇})
                →ᵛ ∘ ((⇡ RHS' ⊲ γ ∷ ((⇡ᴿ M RHS' ⊲ γ ∷ tail) {↥ = ↥})) {↥ = 🗇})

    ∙M∷r   :  {γ' : Env Γ' Z₀} {γ : Env Γ Z₀} {M : V̲a̲l̲ Γ Y} → {LHS : V̲a̲l̲ Γ' X} → {RHS : Γ' ⊢ᵛ Y} → {π' : Wk Γ Γ'} → {ext : WkExt π'}
            → {tail : ValStack b T◾ Z₀} → {↥ : BottomTypeEqualsNextType b (X `× Y) T◾} → {LHS' : V̲a̲l̲ Γ X} → {eq : LHS' ≡ wk-v̲a̲l̲ π' LHS}
            -- not needed for correctness, but makes things easier
              --→ (ϖ : EnvEq π' γ γ')
              --→ (∘ ((⇡ RHS ⊲ γ' ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ M ⊲ γ ∷ □) {↥ = 🗆}))
              ---------------------------------------------------------------------------
            →     ∙ ((⭭ M ⊲ γ ∷ ((⇡ᴿ LHS RHS ⊲ γ' ∷ tail) {↥ = ↥})) {↥ = 🗇})
                →ᵛ ∙ ((⭭ pa̲i̲r̲ LHS' M ⊲ γ ∷ tail) {↥ = ↥})

    ∙pair∷pm  :  {γ' : Env Γ' Z₀} {γ : Env Γ Z₀} {LHS : V̲a̲l̲ Γ X} → {RHS : V̲a̲l̲ Γ Y} → {M : Γ' ⊢ᵛ X `× Y} → {N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z}
            → {π' : Wk Γ Γ'} → {ext : WkExt π'} → {N' : Val (Γ ∙ X ∙ Y) Z} → {eq₁ : N' ≡ (wk-val (wk-cong (wk-cong π')) N)}
            → {RHS' : V̲a̲l̲ (Γ ∙ X) Y} → {eq₂ : RHS' ≡ (wk-v̲a̲l̲ (wk-wk wk-id) RHS)}
            → {tail : ValStack b T◾ Z₀} → {↥ : BottomTypeEqualsNextType b Z T◾}
            -- not needed for correctness, but makes things easier
              --→ (ϖ : EnvEq π' γ γ')
              --→ (∘ ((⇡ M ⊲ γ' ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ ∷ □) {↥ = 🗆}))
              ---------------------------------------------------------------------------
            →     ∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ ∷ ((⇡ᴹ M N ⊲ γ' ∷ tail) {↥ = ↥})) {↥ = 🗇})
                →ᵛ  ∘ ((⇡ N' ⊲ γ ﹐ LHS ﹐ RHS' ∷ tail) {↥ = ↥})

--data _↠ᵛ_ : ValState T◾ → ValState T◾ → Set where
data _↠ᵛ_ where

  _→ᵛ⟨_⟩． : (S : ValState T◾ Z₀) → {S' : ValState T◾ Z₀} → (laststep : S →ᵛ S') → S ↠ᵛ S'

  _→ᵛ⟨_⟩_ : (S : ValState T◾ Z₀) → {S' S'' : ValState T◾ Z₀} → S →ᵛ S' → S' ↠ᵛ S'' → S ↠ᵛ S''

_⨾_ : {F S T : ValState T◾ Z₀} → (F ↠ᵛ S) → (S ↠ᵛ T) → (F ↠ᵛ T)
_⨾_ (F →ᵛ⟨ F>S ⟩．) S>>T = F →ᵛ⟨ F>S ⟩ S>>T
_⨾_ (F →ᵛ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᵛ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ S₂>>T)

⟨_⟩⧻_ : {from : ValState T◾ Z₀} → {to : ValState T◾ Z₀} → (F>T : from →ᵛ to) → (tail : ValStack non-empty T◾' Z₀) → (from ⧻ tail) →ᵛ (to ⧻ tail)
⟨ ∘var-c ⟩⧻ tail = ∘var-c
--⟨ ∘var T>>U π H ⟩⧻ tail = ∘var T>>U π H
⟨ ∘var {nj = nj} {eq = refl} ⟩⧻ tail = ∘var {nj = nj} {eq = refl}
⟨ ∘lam ⟩⧻ tail = ∘lam
⟨ ∘pair ⟩⧻ tail = ∘pair
⟨ ∘pm ⟩⧻ tail = ∘pm
⟨ ∘unit ⟩⧻ tail = ∘unit
-- ⟨ ∙pair∷pm π≡ L R ⟩⧻ tail = ∙pair∷pm π≡ L R
-- ⟨ ∙M∷l π≡ LHS≡M ⟩⧻ tail = ∙M∷l π≡ LHS≡M
-- ⟨ ∙M∷r π≡ RHS≡M ⟩⧻ tail = ∙M∷r π≡ RHS≡M
⟨ ∙pair∷pm {ext = ext} {eq₁ = eq₁} {eq₂ = eq₂} ⟩⧻ tail = ∙pair∷pm {ext = ext} {eq₁ = eq₁} {eq₂ = eq₂}
⟨ ∙M∷l {ext = ext} {eq = eq} ⟩⧻ tail = ∙M∷l {ext = ext} {eq = eq}
⟨ ∙M∷r {ext = ext} {eq = eq} ⟩⧻ tail = ∙M∷r {ext = ext} {eq = eq}

⟪_⟫⧻_ : {from : ValState T◾ Z₀} → {to : ValState T◾ Z₀} → (F>T : from ↠ᵛ to) → (tail : ValStack non-empty T◾' Z₀) → (from ⧻ tail) ↠ᵛ (to ⧻ tail)
⟪ _ →ᵛ⟨ F>T ⟩． ⟫⧻ tail =  _ →ᵛ⟨ ⟨ F>T ⟩⧻ tail ⟩．
⟪ _ →ᵛ⟨ F>T ⟩ F>>T ⟫⧻ tail =   _ →ᵛ⟨ ⟨ F>T ⟩⧻ tail ⟩ (⟪ F>>T ⟫⧻ tail)

data ValHaltingState : ValState T◾ Z₀ → Set where

    ∙_⊲_■ : (M : V̲a̲l̲ Γ X) → (γ : Env Γ Z₀) → ValHaltingState (∙ ((⭭ M ⊲ γ ∷ □) {↥ = 🗆}))

haltingTerm : {S : ValState T◾ Z₀} → (ValHaltingState S) → V̲a̲l̲ (botCtx S) (T◾)
haltingTerm ∙ M ⊲ γ ■ = M

-----------------------

record ValSteps (M : Val Γ X) (γ : Env Γ Z₀) : Set where
  field
    target-ctx : Ctx
    target-term : V̲a̲l̲ target-ctx X
    target-env : Env target-ctx Z₀
    steps  : (∘ ((⇡ M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ target-term ⊲ target-env ∷ □) {↥ = 🗆}))
    weaken : Wk target-ctx Γ
    ext : WkExt weaken

open ValSteps

proj₁-val : V̲a̲l̲ Γ (X `× Y) → V̲a̲l̲ Γ X
proj₁-val (pa̲i̲r̲ W₁ W₂) = W₁

proj₂-val : V̲a̲l̲ Γ (X `× Y) → V̲a̲l̲ Γ Y
proj₂-val (pa̲i̲r̲ W₁ W₂) = W₂

pair-val : (W : V̲a̲l̲ Γ (X `× Y)) → (pa̲i̲r̲ (proj₁-val W) (proj₂-val W) ≡ W)
pair-val (pa̲i̲r̲ W W₁) = refl

-----------------------

run-val : (M : Γ' ⊢ᵛ X) → (γ : Env Γ Z₀) → (π : Wk Γ Γ') → ValSteps (wk-val π M) γ
run-val {X = `V} (var i) γ π = record { steps = ∘ ⇡ wk-val π (var i) ⊲ γ ∷ □ →ᵛ⟨ ∘var-c ⟩． ; weaken = wk-id ; ext = wk-eq wk-id }
run-val {X = `Unit} (var i) γ π = record { steps = ∘ ⇡ wk-val π (var i) ⊲ γ ∷ □ →ᵛ⟨ ∘var {nj = isUnit} {eq = refl} ⟩． ; weaken = wk-id ; ext = wk-eq wk-id }
run-val {X = X `× X₁} (var i) γ π = record { steps = ∘ ⇡ wk-val π (var i) ⊲ γ ∷ □ →ᵛ⟨ ∘var {nj = isProd} {eq = refl} ⟩． ; weaken = wk-id ; ext = wk-eq wk-id }
run-val {X = X `⇒ X₁} (var i) γ π = record { steps = ∘ ⇡ wk-val π (var i) ⊲ γ ∷ □ →ᵛ⟨ ∘var {nj = isLam} {eq = refl} ⟩． ; weaken = wk-id ; ext = wk-eq wk-id }
run-val (lam M) γ π = record { steps = ∘ ⇡ wk-val π (lam M) ⊲ γ ∷ □ →ᵛ⟨ ∘lam ⟩． ; weaken = wk-id ; ext = wk-eq wk-id }
run-val {Γ = Γ} (pair W₁ W₂) γ π =
  let
    IH₁ = run-val W₁ γ π
    IH₂ = run-val W₂ (target-env IH₁) (wk-trans (weaken IH₁) π)
    ⟪stepsIH₂⟫⧻ = subst (λ x → (∘ ⇡ x ⊲ target-env IH₁ ∷ ⇡ᴿ (target-term IH₁) x ⊲ target-env IH₁ ∷ □) ↠ᵛ (∙ ⭭ target-term IH₂ ⊲ target-env IH₂ ∷ ⇡ᴿ (target-term IH₁) x ⊲ target-env IH₁ ∷ □)) (sym (wk-val-trans W₂ (weaken IH₁) π)) (⟪ steps IH₂ ⟫⧻ _)
  in
  record { steps = _ →ᵛ⟨ ∘pair ⟩． ⨾ ⟪ steps IH₁ ⟫⧻ _ ⨾ _ →ᵛ⟨ ∙M∷l {π' = weaken IH₁} {ext = ext IH₁} {eq = refl} ⟩． ⨾ ⟪stepsIH₂⟫⧻ ⨾ _ →ᵛ⟨ ∙M∷r {π' = weaken IH₂} {ext = ext IH₂} {eq = refl} ⟩．
         ; weaken = wk-trans (weaken IH₂) (weaken IH₁)
         ; ext = wk-ext-trans (ext IH₂) (ext IH₁)}
run-val (pm W₁ W₂) γ π =
  let
    IH₁ = run-val W₁ γ π
    IH₂ = run-val W₂ (((target-env IH₁) ﹐ proj₁-val (target-term IH₁)) ﹐ (wk-v̲a̲l̲ (wk-wk wk-id) (proj₂-val (target-term IH₁)))) ((wk-cong (wk-cong (wk-trans (weaken IH₁) π))))

    ∙pair∷pm' = subst (λ x → ∙ ((⭭ x ⊲ target-env IH₁ ∷ ((⇡ᴹ (wk-val π W₁) (wk-val (wk-cong (wk-cong π)) W₂) ⊲ γ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ  ∘ ((⇡ (wk-val (wk-cong (wk-cong (weaken IH₁))) (wk-val (wk-cong (wk-cong π)) W₂)) ⊲ target-env IH₁ ﹐ proj₁-val (target-term IH₁) ﹐ (wk-v̲a̲l̲ (wk-wk wk-id) (proj₂-val (target-term IH₁))) ∷ □) {↥ = 🗆})) (pair-val (target-term IH₁)) (∙pair∷pm {ext = ext IH₁} {eq₁ = refl} {eq₂ = refl})
    stepsIH₂ = subst (λ x → (∘ ⇡ x ⊲ target-env IH₁ ﹐ proj₁-val (target-term IH₁) ﹐ wk-v̲a̲l̲ (wk-wk wk-id) (proj₂-val (target-term IH₁)) ∷ □) ↠ᵛ (∙ ⭭ target-term IH₂ ⊲ target-env IH₂ ∷ □)) (sym (wk-val-trans W₂ (wk-cong (wk-cong (weaken IH₁))) (wk-cong (wk-cong π)))) (steps IH₂)
  in
  record { steps = _ →ᵛ⟨ ∘pm ⟩． ⨾ ⟪ steps IH₁ ⟫⧻ _ ⨾ _ →ᵛ⟨ ∙pair∷pm' ⟩． ⨾ stepsIH₂
         ; weaken = wk-trans (weaken IH₂) (wk-wk (wk-wk (weaken IH₁)))
         ; ext = wk-ext-trans (ext IH₂) (wk-ext (wk-wk (weaken IH₁)) (wk-ext (weaken IH₁) (ext IH₁))) }
run-val unit γ π = record { steps = ∘ ⇡ wk-val π unit ⊲ γ ∷ □ →ᵛ⟨ ∘unit ⟩． ; weaken = wk-id ; ext = wk-eq wk-id }

uip-val : {W W' : Val Γ X} → (eq1 eq2 : W ≡ W') → eq1 ≡ eq2
uip-val refl refl = refl

uip-v̲a̲l̲ : {W W' : V̲a̲l̲ Γ X} → (eq1 eq2 : W ≡ W') → eq1 ≡ eq2
uip-v̲a̲l̲ refl refl = refl

ext-uniq : (π₁ π₂ : Wk Γ Γ') → (ext₁ : WkExt π₁) → (ext₂ : WkExt π₂) → π₁ ≡ π₂
ext-uniq wk-ε wk-ε (wk-eq π) (wk-eq π₁) = refl
ext-uniq (wk-cong π₁) (wk-cong π₂) (wk-eq π) (wk-eq π₃) = cong wk-cong (ext-uniq π₁ π₂ (wk-eq π₁) (wk-eq π₂))
ext-uniq (wk-cong π₁) (wk-wk π₂) (wk-eq π) (wk-eq π₃) = ql (wk-absurd (wk-cong π₁) π₂) (wk-cong π₁ ≡ wk-wk π₂)
ext-uniq (wk-cong π₁) (wk-wk π₂) (wk-eq π) (wk-ext π₃ ext₂) = ql (wk-absurd π₂ π₁) (wk-cong π₁ ≡ wk-wk π₂)
ext-uniq (wk-wk π₁) (wk-cong π₂) (wk-eq π) (wk-eq π₃) = ql (wk-absurd π₁ π₂) (wk-wk π₁ ≡ wk-cong π₂)
ext-uniq (wk-wk π₁) (wk-cong π₂) (wk-ext π ext₁) (wk-eq π₃) = ql (wk-absurd (wk-cong π₂) π₁) (wk-wk π₁ ≡ wk-cong π₂)
ext-uniq (wk-wk π₁) (wk-wk π₂) (wk-eq π) (wk-eq π₃) = ql (wk-absurd (wk-wk π₁) π₂) (wk-wk π₁ ≡ wk-wk π₂)
ext-uniq (wk-wk π₁) (wk-wk π₂) (wk-eq π) (wk-ext π₃ ext₂) = ql (wk-absurd (wk-wk π₁) π₁) (wk-wk π₁ ≡ wk-wk π₂)
ext-uniq (wk-wk π₁) (wk-wk π₂) (wk-ext π ext₁) (wk-eq π₃) = ql (wk-absurd (wk-wk π₂) π₁) (wk-wk π₁ ≡ wk-wk π₂)
ext-uniq (wk-wk π₁) (wk-wk π₂) (wk-ext π ext₁) (wk-ext π₃ ext₂) = cong wk-wk (ext-uniq π₁ π₂ ext₁ ext₂)

wk-ext-uniq : (π : Wk Γ Γ') → (ext₁ ext₂ : WkExt π) → ext₁ ≡ ext₂
wk-ext-uniq wk-ε (wk-eq π) (wk-eq π₁) = refl
wk-ext-uniq (wk-cong π) (wk-eq π₁) (wk-eq π₂) = refl
wk-ext-uniq (wk-wk π) (wk-eq π₁) (wk-eq π₂) = refl
wk-ext-uniq (wk-wk π) (wk-eq π₁) (wk-ext π₂ ext₂) = ql (wk-absurd (wk-wk π) π) (wk-eq (wk-wk π) ≡ wk-ext π ext₂)
wk-ext-uniq (wk-wk π) (wk-ext π₁ ext₁) (wk-eq π₂) = ql (wk-absurd (wk-wk π) π) (wk-ext π ext₁ ≡ wk-eq (wk-wk π))
wk-ext-uniq (wk-wk π) (wk-ext π₁ ext₁) (wk-ext π₂ ext₂) = cong (wk-ext π) (wk-ext-uniq π ext₁ ext₂)

determinismⱽ : {S S' : ValState T◾ Z₀} → (S→S'₁ S→S'₂ : S →ᵛ S') → (S→S'₁ ≡ S→S'₂)
determinismⱽ {S = ∘ x} {S' = ∘ x₁} ∘pair ∘pair = refl
determinismⱽ {S = ∘ x} {S' = ∘ x₁} ∘pm ∘pm = refl
determinismⱽ {S = ∘ ⇡ var i ⊲ γ ∷ x₁} {S' = ∙ ⭭ x ⊲ γ₁ ∷ x₃} ∘var-c ∘var-c = refl
determinismⱽ {S = ∘ ⇡ var i ⊲ γ ∷ x₁} {S' = ∙ ⭭ x ⊲ γ₁ ∷ x₃} (∘var {nj = isUnit} {eq = refl}) (∘var {nj = isUnit} {eq = refl}) = refl
determinismⱽ {S = ∘ ⇡ var i ⊲ γ ∷ x₁} {S' = ∙ ⭭ x ⊲ γ₁ ∷ x₃} (∘var {nj = isProd} {eq = refl}) (∘var {nj = isProd} {eq = refl}) = refl
determinismⱽ {S = ∘ ⇡ var i ⊲ γ ∷ x₁} {S' = ∙ ⭭ x ⊲ γ₁ ∷ x₃} (∘var {nj = isLam} {eq = refl}) (∘var {nj = isLam} {eq = refl}) = refl
determinismⱽ {S = ∘ ⇡ lam x₂ ⊲ γ ∷ x₁} {S' = ∙ ⭭ x ⊲ γ₁ ∷ x₃} ∘lam ∘lam = refl
determinismⱽ {S = ∘ ⇡ unit ⊲ γ ∷ x₁} {S' = ∙ ⭭ x ⊲ γ₁ ∷ x₃} ∘unit ∘unit = refl
determinismⱽ {S = ∙ ⭭ LHS ⊲ γ ∷ ⇡ᴹ M₁ N ⊲ γ₁ ∷ x₂} {S' = ∘ ⇡ M ⊲ γ₂ ∷ x₄} (∙pair∷pm {π' = π₁} {ext = ext₁} {eq₁ = eq₁} {eq₂ = eq₂}) (∙pair∷pm {π' = π₂} {ext = ext₂} {eq₁ = eq₁'} {eq₂ = eq₂'}) =
  let
    π₁≡π₂ : (π₁ , ext₁) ≡ (π₂ , ext₂)
    π₁≡π₂ = dcong₂ (λ x y → x , y) (ext-uniq π₁ π₂ ext₁ ext₂) (wk-ext-uniq π₂ (subst WkExt (ext-uniq π₁ π₂ ext₁ ext₂) ext₁) ext₂)
    goal : (∙pair∷pm {eq₁ = eq₁} {eq₂ = eq₂}) ≡ (∙pair∷pm {eq₁ = eq₁'} {eq₂ = eq₂'})
    goal = dcong₂ (λ x y → ∙pair∷pm {π' = proj₁ x} {ext = proj₂ x} {eq₁ = proj₁ y} {eq₂ = proj₂ y}) π₁≡π₂ (pair-eq (uip-val _ eq₁') (uip-v̲a̲l̲ _ eq₂'))
  in
  goal
determinismⱽ {S = ∙ ⭭ LHS ⊲ γ ∷ ⇡ᴸ LHS₁ RHS ⊲ γ₁ ∷ x₂} {S' = ∘ ⇡ RHS' ⊲ γ₂ ∷ ⇡ᴿ LHS₂ RHS₁ ⊲ γ₃ ∷ x₄} (∙M∷l {Y = Y} {π' = π₁} {ext = ext₁} {RHS' = RHS'} {eq = eq}) (∙M∷l {π' = π₂} {ext = ext₂} {RHS' = RHS'} {eq = eq'}) =
  let
    π₁≡π₂ : (π₁ , ext₁) ≡ (π₂ , ext₂)
    π₁≡π₂ = dcong₂ (λ x y → x , y) (ext-uniq π₁ π₂ ext₁ ext₂) (wk-ext-uniq π₂ (subst WkExt (ext-uniq π₁ π₂ ext₁ ext₂) ext₁) ext₂)
    goal : (∙M∷l {eq = eq}) ≡ (∙M∷l {eq = eq'})
    goal = dcong₂ (λ x y → ∙M∷l {π' = proj₁ x} {ext = proj₂ x} {eq = y}) π₁≡π₂ (uip-val _ eq')
  in
  goal
determinismⱽ {S = ∙ ⭭ x ⊲ γ ∷ ⇡ᴿ LHS RHS ⊲ γ₁ ∷ x₂} {S' = ∙ ⭭ x₃ ⊲ γ₂ ∷ x₄} (∙M∷r {π' = π₁} {ext = ext₁} {eq = eq₁}) (∙M∷r {π' = π₂} {ext = ext₂} {eq = eq₂}) =
  let
    π₁≡π₂ : (π₁ , ext₁) ≡ (π₂ , ext₂)
    π₁≡π₂ = dcong₂ (λ x y → x , y) (ext-uniq π₁ π₂ ext₁ ext₂) (wk-ext-uniq π₂ (subst WkExt (ext-uniq π₁ π₂ ext₁ ext₂) ext₁) ext₂)
    goal : (∙M∷r {eq = eq₁}) ≡ (∙M∷r {eq = eq₂})
    goal = dcong₂ (λ x y → ∙M∷r {π' = proj₁ x} {ext = proj₂ x} {eq = y}) π₁≡π₂ (uip-v̲a̲l̲ _ eq₂)
  in
  goal

{-
determinismⱽ' : {S S' S'' : ValState T◾ Z₀} → (S→S' : S →ᵛ S') → (S→S'' : S →ᵛ S'') → (S' ≡ S'')
determinismⱽ' ∘var-c ∘var-c = refl
determinismⱽ' ∘var ∘var = {!!}
determinismⱽ' ∘lam ∘lam = refl
determinismⱽ' ∘pair ∘pair = refl
determinismⱽ' ∘pm ∘pm = refl
determinismⱽ' ∘unit ∘unit = refl
determinismⱽ' (∙M∷l {π' = π₁} {ext = ext₁} {eq = refl}) (∙M∷l {π' = π₂} {ext = ext₂} {eq = refl}) = cong (λ x → ∘ ⇡ wk-val x _ ⊲ _ ∷ ⇡ᴿ _ (wk-val x _) ⊲ _ ∷ _) (ext-uniq π₁ π₂ ext₁ ext₂)
determinismⱽ' ∙M∷r ∙M∷r = {!!}
determinismⱽ' ∙pair∷pm ∙pair∷pm = {!!}
-}

detᵛ-absurd :   {S S' : ValState X Z₀} → {M' : V̲a̲l̲ Γ'' X} → {γ' : Env Γ'' Z₀} → (S→S' : (∙ ((⭭ M' ⊲ γ' ∷ □) {↥ = 🗆})) ↠ᵛ S') → ⊥
detᵛ-absurd (S →ᵛ⟨ () ⟩．)
detᵛ-absurd (S →ᵛ⟨ () ⟩ S→S')

detᵛ-absurd' :   {S S'' S''' : ValState X Z₀} → {M' : V̲a̲l̲ Γ'' X} → {γ' : Env Γ'' Z₀}
                 → (S→S' : S →ᵛ (∙ ((⭭ M' ⊲ γ' ∷ □) {↥ = 🗆})))
                 → (S→S'' : S →ᵛ S'')
                 → (S''→S''' : S'' →ᵛ S''') → ⊥
detᵛ-absurd' ∘var-c ∘var-c ()
detᵛ-absurd' ∘var-c ∘var ()
detᵛ-absurd' ∘var ∘var-c ()
detᵛ-absurd' ∘var ∘var ()
detᵛ-absurd' ∘lam ∘lam ()
detᵛ-absurd' ∘unit ∘unit ()
detᵛ-absurd' ∙M∷r ∙M∷r ()

detᵛ-absurd'' :   {S S'' S''' : ValState X Z₀} → {M' : V̲a̲l̲ Γ'' X} → {γ' : Env Γ'' Z₀}
                 → (S→S' : S →ᵛ (∙ ((⭭ M' ⊲ γ' ∷ □) {↥ = 🗆})))
                 → (S→S'' : S →ᵛ S'')
                 → (S''→S''' : S'' ↠ᵛ S''') → ⊥
detᵛ-absurd'' S→S' S→S'' (S →ᵛ⟨ laststep ⟩．) = ql (detᵛ-absurd' S→S' S→S'' laststep) _
detᵛ-absurd'' S→S' S→S'' (S →ᵛ⟨ x ⟩ S''→S''') = ql (detᵛ-absurd' S→S' S→S'' x) _


determinismⱽ* :   {S : ValState X Z₀} → {M' : V̲a̲l̲ Γ'' X} → {γ' : Env Γ'' Z₀}
                → (S→S S→S' : S ↠ᵛ (∙ ((⭭ M' ⊲ γ' ∷ □) {↥ = 🗆}))) → S→S ≡ S→S'

determinismⱽ* {S = S} (S →ᵛ⟨ laststep ⟩．) (S₁ →ᵛ⟨ laststep₁ ⟩．) = cong (λ x → S →ᵛ⟨ x ⟩．) (determinismⱽ laststep laststep₁)

determinismⱽ* {S = S} (S →ᵛ⟨ S→S' ⟩．) (S →ᵛ⟨ S→S'' ⟩ S''→S''') =  ql (detᵛ-absurd'' S→S' S→S'' S''→S''') _
determinismⱽ* {S = S} (S →ᵛ⟨ S→S'' ⟩ S''→S''') (S →ᵛ⟨ S→S' ⟩．) = ql (detᵛ-absurd'' S→S' S→S'' S''→S''') _

determinismⱽ* {S = S} (S₁ →ᵛ⟨ ∘var-c ⟩ S→S') (S₂ →ᵛ⟨ ∘var-c ⟩ S→S'') = cong (λ x → _ →ᵛ⟨ _ ⟩ x) (determinismⱽ* S→S' S→S'')
determinismⱽ* {S = S} (S₁ →ᵛ⟨ ∘var {nj = isUnit} {eq = refl} ⟩ S→S') (S₂ →ᵛ⟨ ∘var {nj = isUnit} {eq = refl} ⟩ S→S'') = cong (λ x → _ →ᵛ⟨ _ ⟩ x) (determinismⱽ* S→S' S→S'')
determinismⱽ* {S = S} (S₁ →ᵛ⟨ ∘var {nj = isProd} {eq = refl} ⟩ S→S') (S₂ →ᵛ⟨ ∘var {nj = isProd} {eq = refl} ⟩ S→S'') = cong (λ x → _ →ᵛ⟨ _ ⟩ x) (determinismⱽ* S→S' S→S'')
determinismⱽ* {S = S} (S₁ →ᵛ⟨ ∘var {nj = isLam} {eq = refl} ⟩ S→S') (S₂ →ᵛ⟨ ∘var {nj = isLam} {eq = refl} ⟩ S→S'') = cong (λ x → _ →ᵛ⟨ _ ⟩ x) (determinismⱽ* S→S' S→S'')
determinismⱽ* {S = S} (S₁ →ᵛ⟨ ∘lam ⟩ S→S') (S₂ →ᵛ⟨ ∘lam ⟩ S→S'') = cong (λ x → _ →ᵛ⟨ _ ⟩ x) (determinismⱽ* S→S' S→S'')
determinismⱽ* {S = S} (S₁ →ᵛ⟨ ∘pair ⟩ S→S') (S₂ →ᵛ⟨ ∘pair ⟩ S→S'') = cong (λ x → _ →ᵛ⟨ _ ⟩ x) (determinismⱽ* S→S' S→S'')
determinismⱽ* {S = S} (S₁ →ᵛ⟨ ∘pm ⟩ S→S') (S₂ →ᵛ⟨ ∘pm ⟩ S→S'') = cong (λ x → _ →ᵛ⟨ _ ⟩ x) (determinismⱽ* S→S' S→S'')
determinismⱽ* {S = S} (S₁ →ᵛ⟨ ∘unit ⟩ S→S') (S₂ →ᵛ⟨ ∘unit ⟩ S→S'') = cong (λ x → _ →ᵛ⟨ _ ⟩ x) (determinismⱽ* S→S' S→S'')
determinismⱽ* {S = S} (S₁ →ᵛ⟨ ∙M∷l {RHS = RHS} {π' = π₁} {ext = ext₁} {eq = refl} ⟩ S→S') (S₂ →ᵛ⟨ ∙M∷l {RHS = RHS} {π' = π₂} {ext = ext₂} {eq = refl} ⟩ S→S'') =
  let
    eq1 : (π₁ , ext₁) ≡ (π₂ , ext₂)
    eq1 = dcong₂ (λ x y → x , y) (ext-uniq π₁ π₂ ext₁ ext₂) (wk-ext-uniq π₂ (subst WkExt (ext-uniq π₁ π₂ ext₁ ext₂) ext₁) ext₂)
    goal : S →ᵛ⟨ ∙M∷l {π' = π₁} {ext = ext₁} ⟩ S→S' ≡ S →ᵛ⟨ ∙M∷l {π' = π₂} {ext = ext₂} ⟩ S→S''
    goal = dcong₂ (λ x y → S →ᵛ⟨ ∙M∷l {π' = proj₁ x} {ext = proj₂ x} {RHS' = wk-val (proj₁ x) RHS} {eq = (proj₁ y)} ⟩ (proj₂ y)) eq1 (pair-eq (uip-val _ _) (determinismⱽ* _ S→S''))
  in
  goal
determinismⱽ* {S = S} (S₁ →ᵛ⟨ ∙M∷r {LHS = LHS} {π' = π₁} {ext = ext₁} {eq = refl} ⟩ S→S') (S₁ →ᵛ⟨ ∙M∷r {LHS = LHS} {π' = π₂} {ext = ext₂} {eq = refl} ⟩ S→S'') =
  let
    eq1 : (π₁ , ext₁) ≡ (π₂ , ext₂)
    eq1 = dcong₂ (λ x y → x , y) (ext-uniq π₁ π₂ ext₁ ext₂) (wk-ext-uniq π₂ (subst WkExt (ext-uniq π₁ π₂ ext₁ ext₂) ext₁) ext₂)
    goal : S →ᵛ⟨ ∙M∷r {π' = π₁} {ext = ext₁} ⟩ S→S' ≡ S →ᵛ⟨ ∙M∷r {π' = π₂} {ext = ext₂} ⟩ S→S''
    goal = dcong₂ (λ x y → S →ᵛ⟨ ∙M∷r {π' = proj₁ x} {ext = proj₂ x} {LHS' = wk-v̲a̲l̲ (proj₁ x) LHS} {eq = (proj₁ y)} ⟩ (proj₂ y)) eq1 (pair-eq (uip-v̲a̲l̲ _ _) (determinismⱽ* _ S→S''))
  in
  goal
determinismⱽ* {S = S} (S₁ →ᵛ⟨ ∙pair∷pm {RHS = RHS} {N = N} {π' = π₁} {ext = ext₁} {eq₁ = refl} {eq₂ = refl} ⟩ S→S') (S₂ →ᵛ⟨ ∙pair∷pm {RHS = RHS} {N = N} {π' = π₂} {ext = ext₂} {eq₁ = refl} {eq₂ = refl} ⟩ S→S'') =
  let
    eq1 : (π₁ , ext₁) ≡ (π₂ , ext₂)
    eq1 = dcong₂ (λ x y → x , y) (ext-uniq π₁ π₂ ext₁ ext₂) (wk-ext-uniq π₂ (subst WkExt (ext-uniq π₁ π₂ ext₁ ext₂) ext₁) ext₂)
    goal : S →ᵛ⟨ ∙pair∷pm {π' = π₁} {ext = ext₁} ⟩ S→S' ≡ S →ᵛ⟨ ∙pair∷pm {π' = π₂} {ext = ext₂} ⟩ S→S''
    goal = dcong₂ (λ x y → S →ᵛ⟨ ∙pair∷pm {π' = proj₁ x} {ext = proj₂ x} {N' = wk-val (wk-cong (wk-cong (proj₁ x))) N} {eq₁ = (proj₁ y)} {eq₂ = proj₁ (proj₂ y)} ⟩ (proj₂ (proj₂ y))) eq1 (pair-eq (uip-val _ refl) (pair-eq (uip-v̲a̲l̲ _ refl) (determinismⱽ* _ S→S'')))
  in
  goal


-----------------------

infixr 15 _→ᶜ⟨_⟩_
infixr 15 _→ᶜ*_
infixr 10 _⨾ᶜ_

-- Computation Machine
--------------------------------------------------

infix  15 _→ᶜ_
data _→ᶜ_ {Z₀ : Ty} : CompState Z₀ → CompState Z₀ → Set where

      ∘return  :    {M : Γ ⊢ᵛ X} → {γ : Env Γ Z₀} → {M' : V̲a̲l̲ Γ'' X} → {γ' : Env Γ'' Z₀} → {cs : CompStack Δ X Z₀}
                    → ((∘ ((⇡ M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ M' ⊲ γ' ∷ □) {↥ = 🗆})))
                    ----------------------------------------------------------------
                    →     ((∘⟨ return M ⊰ γ ╎ cs ⟩) ) →ᶜ ((∙⟨ r̲e̲t̲u̲r̲n̲ M' ⊰ γ' ╎ cs ⟩))


      ∙return  :    {M : V̲a̲l̲ Γ X} → {γ : Env Γ Z₀} → {N : (Γ' ∙ X) ⊢ᶜ Y} → {γ' : Env Γ' Z₀} → {π : Wk Γ Γ'}
                  → {cs : CompStack Δ Y Z₀}
                ----------------------------------------------------------------
                  →       ((∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ ╎ ((N ⊲ γ' ⦂⦂ cs)) ⟩))
                        →ᶜ ((∘⟨ wk-comp (wk-cong π) N ⊰ γ ﹐ M ╎ cs ⟩))

      ∘push    :    {M : Γ ⊢ᶜ X} → {N : (Γ ∙ X) ⊢ᶜ Y} → {γ : Env Γ Z₀} → {cs : CompStack Δ Y Z₀}
                ----------------------------------------------------------------
                  →       ((∘⟨ push M N ⊰ γ ╎ cs ⟩)) →ᶜ ((∘⟨ M ⊰ γ ╎ ((N ⊲ γ ⦂⦂ cs)) ⟩))

      ∘sub     :    {M : (Γ ∙ `V) ⊢ᶜ X} → {N : Γ ⊢ᶜ X} → {γ : Env Γ Z₀} → {cs : CompStack Δ X Z₀}
                ----------------------------------------------------------------
                  →       ((∘⟨ sub M N ⊰ γ ╎ cs ⟩)) →ᶜ ((∘⟨ M ⊰ ((γ ﹐﹝ N ╎ cs ﹞)) ╎ cs ⟩))

      ∘pm      :    {M : Γ ⊢ᵛ X `× Y} → {γ : Env Γ Z₀} → {W : (Γ ∙ X ∙ Y) ⊢ᶜ Z}
                  → {cs : CompStack Δ Z Z₀}
                  → {γ'' : Env Γ'' Z₀} → {LHS : V̲a̲l̲ Γ'' X} → {RHS : V̲a̲l̲ Γ'' Y}
                  → ((∘ ((⇡ M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ'' ∷ □) {↥ = 🗆}))) → (π' : Wk Γ'' Γ)
                ----------------------------------------------------------------
                  →       ((∘⟨ pm M W ⊰ γ ╎ cs ⟩))
                        →ᶜ ((∘⟨ wk-comp (wk-cong (wk-cong π')) W ⊰ γ'' ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ╎ cs ⟩))

      ∙app-var   :     {i : Γ ∋ (Z' `⇒ Z)} → {N : V̲a̲l̲ Γ Z'} → {γ : Env Γ Z₀} → {cs : CompStack Δ Z Z₀}
                      → {W : (Γ' ∙ Z') ⊢ᶜ Z} → {γ' : Env Γ' Z₀}
                      → (⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ _﹐_ γ' (l̲a̲m̲ W) ⟩) → (πᵥ : Wk Γ Γ')
                    ----------------------------------------------------------------
                      →    ((∙⟨ a̲pp (var i) N ⊰ γ ╎ cs ⟩))
                        →ᶜ ((∘⟨ (wk-comp (wk-cong πᵥ) W) ⊰ γ ﹐ N ╎ cs ⟩))

      ∙app-pm     :    {M : Γ ⊢ᵛ (X `× Y)} → {N₁ : (Γ ∙ X ∙ Y) ⊢ᵛ (Z' `⇒ Z)} → {N : V̲a̲l̲ Γ Z'} → {γ : Env Γ Z₀}
                      → {cs : CompStack Δ Z Z₀}
                      → {LHS : V̲a̲l̲ Γ' X} → {RHS : V̲a̲l̲ Γ' Y} → {γ' : Env Γ' Z₀}
                      → ((∘ ((⇡ M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ' ∷ □) {↥ = 🗆}))) → (π : Wk Γ' Γ)
                    ----------------------------------------------------------------
                      →    ((∙⟨ a̲pp (pm M N₁) N ⊰ γ ╎ cs ⟩))
                        →ᶜ ((∙⟨ a̲pp ((wk-val (wk-cong (wk-cong π)) N₁)) (wk-v̲a̲l̲ (wk-wk (wk-wk π)) N) ⊰ γ' ﹐ LHS ﹐ (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ╎ cs ⟩))

      ∙app-lam     :   {W : (Γ ∙ X) ⊢ᶜ Y} → {N : V̲a̲l̲ Γ X} → {γ : Env Γ Z₀}
                      → {cs : CompStack Δ Y Z₀}
                    ----------------------------------------------------------------
                      → ((∙⟨ a̲pp (lam W) N ⊰ γ ╎ cs ⟩)) →ᶜ ((∘⟨ W ⊰ γ ﹐ N ╎ cs ⟩))

      ∘app         :   {M : Γ ⊢ᵛ X `⇒ Y} → {N : Γ ⊢ᵛ X} → {γ : Env Γ Z₀} → {cs : CompStack Δ Y Z₀}
                      → {N' : V̲a̲l̲ Γ' X} → {γ' : Env Γ' Z₀}
                      → ((∘ ((⇡ N ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ N' ⊲ γ' ∷ □) {↥ = 🗆}))) → (π : Wk Γ' Γ)
                    ----------------------------------------------------------------
                      →    ((∘⟨ app M N ⊰ γ ╎ cs ⟩))
                        →ᶜ ((∙⟨ a̲pp (wk-val π M) N' ⊰ γ' ╎ cs ⟩))

      ∘var         :   {M : Γ ⊢ᵛ `V} → {γ : Env Γ Z₀} → {i : Γ' ∋ `V} → {γ' : Env Γ' Z₀} → {W : Γ'' ⊢ᶜ X'} → {γ'' : Env Γ'' Z₀}
                      → {cs : CompStack Δ X Z₀} → {cs' : CompStack Δ' X' Z₀}
                      → ((∘ ((⇡ M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ v̲a̲r̲ i ⊲ γ' ∷ □) {↥ = 🗆}))) → (π' : Wk Γ' Γ)
                      → (⟨ i ∥ γ' ⟩ →ᴸ* ⟨ h ∥ ((γ'' ﹐﹝ W ╎ cs' ﹞)) ⟩) → (πᵥ : Wk Γ' Γ'')
                ----------------------------------------------------------------
                      →    ((∘⟨ var M ⊰ γ ╎ cs ⟩)) →ᶜ ((∘⟨ W ⊰ γ'' ╎ cs' ⟩))


determinismꟲ : {C C' : CompState Z₀} → (S→S' T→T' : C →ᶜ C') → (S→S' ≡ T→T')
determinismꟲ {C = ∘⟨ return x ⊰ γ ╎ cs ⟩} (∘return W→W') (∘return W→W'') =
  let
    goal : ∘return W→W' ≡ ∘return  W→W''
    goal = cong ∘return (determinismⱽ* W→W' W→W'')
  in
  goal
determinismꟲ {C = ∘⟨ pm x W ⊰ γ ╎ cs ⟩} S→S' T→T' = {!!}
determinismꟲ {C = ∘⟨ push W W₁ ⊰ γ ╎ cs ⟩} S→S' T→T' = {!!}
determinismꟲ {C = ∘⟨ app x x₁ ⊰ γ ╎ cs ⟩} S→S' T→T' = {!!}
determinismꟲ {C = ∘⟨ var x ⊰ γ ╎ cs ⟩} S→S' T→T' = {!!}
determinismꟲ {C = ∘⟨ sub W W₁ ⊰ γ ╎ cs ⟩} S→S' T→T' = {!!}
determinismꟲ {C = ∙⟨ r̲e̲t̲u̲r̲n̲ x ⊰ γ ╎ cs ⟩} S→S' T→T' = {!!}
determinismꟲ {C = ∙⟨ a̲pp x x₁ ⊰ γ ╎ cs ⟩} S→S' T→T' = {!!}

{-
infix  15 _→ᶜ_
data _→ᶜ_ {Z₀ : Ty} : CompState Z₀ → CompState Z₀ → Set where

      -- ∘return  :    {M : Γ ⊢ᵛ X} → {γ : Env Γ' Z₀} → {π : Wk Γ' Γ} → {M' : V̲a̲l̲ Γ'' X} → {γ' : Env Γ'' Z₀} → {cs : CompStack Δ X Z₀}
      --               → ((∘ ((⇡ wk-val π M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ M' ⊲ γ' ∷ □) {↥ = 🗆})))
      --               ----------------------------------------------------------------
      --               →     ((∘⟨ wk-comp π (return M) ⊰ γ ╎ cs ⟩) ) →ᶜ ((∙⟨ r̲e̲t̲u̲r̲n̲ M' ⊰ γ' ╎ cs ⟩))

      ∘return  :    {M : Γ ⊢ᵛ X} → {γ : Env Γ' Z₀} → {π : Wk Γ' Γ} → {M' : V̲a̲l̲ Γ'' X} → {γ' : Env Γ'' Z₀} → {cs : CompStack Δ X Z₀}
                    → {Mʷᵏ : Val Γ' X} → {eq̭ᴹ : Mʷᵏ ≡ wk-val π M}
                    → ((∘ ((⇡ Mʷᵏ ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ M' ⊲ γ' ∷ □) {↥ = 🗆})))
                    ----------------------------------------------------------------
                    →     ((∘⟨ return Mʷᵏ ⊰ γ ╎ cs ⟩) ) →ᶜ ((∙⟨ r̲e̲t̲u̲r̲n̲ M' ⊰ γ' ╎ cs ⟩))


      ∙return  :    {M : V̲a̲l̲ Γ X} → {γ : Env Γ Z₀} → {N : (Γ' ∙ X) ⊢ᶜ Y} → {γ' : Env Γ' Z₀} → {π : Wk Γ Γ'}
                  → {cs : CompStack Δ Y Z₀}
                ----------------------------------------------------------------
                  →       ((∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ ╎ ((N ⊲ γ' ⦂⦂ cs)) ⟩))
                        →ᶜ ((∘⟨ wk-comp (wk-cong π) N ⊰ γ ﹐ M ╎ cs ⟩))

      ∘push    :    {M : Γ ⊢ᶜ X} → {N : (Γ ∙ X) ⊢ᶜ Y} → {γ : Env Γ Z₀} → {cs : CompStack Δ Y Z₀}
                ----------------------------------------------------------------
                  →       ((∘⟨ push M N ⊰ γ ╎ cs ⟩)) →ᶜ ((∘⟨ M ⊰ γ ╎ ((N ⊲ γ ⦂⦂ cs)) ⟩))

      ∘sub     :    {M : (Γ ∙ `V) ⊢ᶜ X} → {N : Γ ⊢ᶜ X} → {γ : Env Γ Z₀} → {cs : CompStack Δ X Z₀}
                ----------------------------------------------------------------
                  →       ((∘⟨ sub M N ⊰ γ ╎ cs ⟩)) →ᶜ ((∘⟨ M ⊰ ((γ ﹐﹝ N ╎ cs ﹞)) ╎ cs ⟩))

      ∘pm      :    {M : Γ' ⊢ᵛ X `× Y} → {γ : Env Γ Z₀} → {W : (Γ' ∙ X ∙ Y) ⊢ᶜ Z}
                  → {cs : CompStack Δ Z Z₀} → {γ'' : Env Γ'' Z₀}
                  → {LHS : V̲a̲l̲ Γ'' X} → {RHS : V̲a̲l̲ Γ'' Y} → (π : Wk Γ Γ')
                  → ((∘ ((⇡ wk-val π M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ'' ∷ □) {↥ = 🗆}))) → (π' : Wk Γ'' Γ)
                ----------------------------------------------------------------
                  →       ((∘⟨ pm (wk-val π M) (wk-comp (wk-cong (wk-cong π)) W) ⊰ γ ╎ cs ⟩))
                        →ᶜ ((∘⟨ wk-comp (wk-cong (wk-cong π')) (wk-comp (wk-cong (wk-cong π)) W) ⊰ γ'' ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ╎ cs ⟩))

      ∙app-var   :     {i : Γ ∋ (Z' `⇒ Z)} → {N : V̲a̲l̲ Γ Z'} → {γ : Env Γ Z₀} → {cs : CompStack Δ Z Z₀}
                      → {W : (Γ' ∙ Z') ⊢ᶜ Z} → {γ' : Env Γ' Z₀}
                      → (⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ _﹐_ γ' (l̲a̲m̲ W) ⟩) → (πᵥ : Wk Γ Γ')
                    ----------------------------------------------------------------
                      →    ((∙⟨ a̲pp (var i) N ⊰ γ ╎ cs ⟩))
                        →ᶜ ((∘⟨ (wk-comp (wk-cong πᵥ) W) ⊰ γ ﹐ N ╎ cs ⟩))

      ∙app-pm     :    {M : Γ ⊢ᵛ (X `× Y)} → {N₁ : (Γ ∙ X ∙ Y) ⊢ᵛ (Z' `⇒ Z)} → {N : V̲a̲l̲ Γ Z'} → {γ : Env Γ Z₀}
                      → {cs : CompStack Δ Z Z₀}
                      → {LHS : V̲a̲l̲ Γ' X} → {RHS : V̲a̲l̲ Γ' Y} → {γ' : Env Γ' Z₀}
                      → ((∘ ((⇡ M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ' ∷ □) {↥ = 🗆}))) → (π : Wk Γ' Γ)
                    ----------------------------------------------------------------
                      →    ((∙⟨ a̲pp (pm M N₁) N ⊰ γ ╎ cs ⟩))
                        →ᶜ ((∙⟨ a̲pp ((wk-val (wk-cong (wk-cong π)) N₁)) (wk-v̲a̲l̲ (wk-wk (wk-wk π)) N) ⊰ γ' ﹐ LHS ﹐ (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ╎ cs ⟩))

      ∙app-lam     :   {W : (Γ ∙ X) ⊢ᶜ Y} → {N : V̲a̲l̲ Γ X} → {γ : Env Γ Z₀}
                      → {cs : CompStack Δ Y Z₀}
                    ----------------------------------------------------------------
                      → ((∙⟨ a̲pp (lam W) N ⊰ γ ╎ cs ⟩)) →ᶜ ((∘⟨ W ⊰ γ ﹐ N ╎ cs ⟩))

      ∘app         :   {M : Γ ⊢ᵛ X `⇒ Y} → {N : Γ ⊢ᵛ X} → {γ : Env Γ Z₀} → {cs : CompStack Δ Y Z₀}
                      → {N' : V̲a̲l̲ Γ' X} → {γ' : Env Γ' Z₀}
                      → ((∘ ((⇡ N ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ N' ⊲ γ' ∷ □) {↥ = 🗆}))) → (π : Wk Γ' Γ)
                    ----------------------------------------------------------------
                      →    ((∘⟨ app M N ⊰ γ ╎ cs ⟩))
                        →ᶜ ((∙⟨ a̲pp (wk-val π M) N' ⊰ γ' ╎ cs ⟩))

      ∘var         :   {M : Γ ⊢ᵛ `V} → {γ : Env Γ Z₀} → {i : Γ' ∋ `V} → {γ' : Env Γ' Z₀} → {W : Γ'' ⊢ᶜ X'} → {γ'' : Env Γ'' Z₀}
                      → {cs : CompStack Δ X Z₀} → {cs' : CompStack Δ' X' Z₀}
                      → ((∘ ((⇡ M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ v̲a̲r̲ i ⊲ γ' ∷ □) {↥ = 🗆}))) → (π' : Wk Γ' Γ)
                      → (⟨ i ∥ γ' ⟩ →ᴸ* ⟨ h ∥ ((γ'' ﹐﹝ W ╎ cs' ﹞)) ⟩) → (πᵥ : Wk Γ' Γ'')
                ----------------------------------------------------------------
                      →    ((∘⟨ var M ⊰ γ ╎ cs ⟩)) →ᶜ ((∘⟨ W ⊰ γ'' ╎ cs' ⟩))
-}

data _→ᶜ*_ {Z₀ : Ty} : CompState Z₀ → CompState Z₀ → Set where

  _◼ : (S : CompState Z₀) → S →ᶜ* S

  _→ᶜ⟨_⟩_ : (S : CompState Z₀) → {S' S'' : CompState Z₀} → S →ᶜ S' → S' →ᶜ* S'' → S →ᶜ* S''

_⨾ᶜ_ : {F S T : CompState Z₀} → (F →ᶜ* S) → (S →ᶜ* T) → (F →ᶜ* T)
_⨾ᶜ_ (S ◼) S>>T = S>>T
_⨾ᶜ_ (F →ᶜ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᶜ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ᶜ S₂>>T)

data CompHaltingState : CompState Z₀ → Set where

    ret : {M : V̲a̲l̲ Γ Z₀} → {γ : Env Γ Z₀} → {ϖ : EnvEq wk-wk-ε γ (topCsEnv ◻)} → CompHaltingState ((∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ ╎ ◻ ⟩) )


valstate-wk : {S S' : ValState X Z₀} → S →ᵛ S' → Wk (topCtx S') (topCtx S)
valstate-wk ∘var-c = wk-id
valstate-wk (∘var) = wk-id
valstate-wk ∘lam = wk-id
valstate-wk ∘pair = wk-id
valstate-wk ∘pm = wk-id
valstate-wk ∘unit = wk-id
valstate-wk (∙M∷l) = wk-id
valstate-wk (∙M∷r) = wk-id
valstate-wk (∙pair∷pm {tail = tail} {↥ = ↥}) = wk-wk (wk-wk wk-id)

valstate-env-eq : {S S' : ValState X Z₀} → (S→S' : S →ᵛ S') → EnvEq (valstate-wk S→S') (topEnv S') (topEnv S)
valstate-env-eq ∘var-c = enveq-id
valstate-env-eq (∘var) = enveq-id
valstate-env-eq ∘lam = enveq-id
valstate-env-eq ∘pair = enveq-id
valstate-env-eq ∘pm = enveq-id
valstate-env-eq ∘unit = enveq-id
valstate-env-eq (∙M∷l) = enveq-id
valstate-env-eq (∙M∷r) = enveq-id
valstate-env-eq (∙pair∷pm {LHS = LHS} {RHS' = RHS'}) = wk-env-val-wk RHS' (wk-env-val-wk LHS enveq-id)

valstate-wkext : {S S' : ValState X Z₀} → (S→S' : S →ᵛ S') → WkExt (valstate-wk S→S')
valstate-wkext ∘var-c = wk-eq _
valstate-wkext (∘var) = wk-eq _
valstate-wkext ∘lam = wk-eq _
valstate-wkext ∘pair = wk-eq _
valstate-wkext ∘pm = wk-eq _
valstate-wkext ∘unit = wk-eq _
valstate-wkext (∙M∷l) = wk-eq _
valstate-wkext (∙M∷r) = wk-eq _
valstate-wkext (∙pair∷pm) = wk-ext (wk-wk wk-id) (wk-ext wk-id (wk-eq wk-id))
