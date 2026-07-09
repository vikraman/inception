{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.MachineP where

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

open import Inception.Sub.EnvironmentsP
open import Inception.Sub.StatesP

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
data _→ᴸ_ : LookupState X Z₀ → LookupState X Z₀ → Set where

    val-h-step    : {E : Env Γ Z₀} → {i : Γ ∋ `V} → ⟨ h  ∥ E ﹐ (v̲a̲r̲ i) ⟩ →ᴸ ⟨ i ∥ E ⟩

    val-t-step    : {i : Γ ∋ Y} → {E : Env Γ Z₀} → {M : V̲a̲l̲ Γ X} → ⟨ t i  ∥ _﹐_ E M ⟩ →ᴸ ⟨ i ∥ E ⟩

    comp-t-step   : {i : Γ ∋ Y} → {γ : Env Γ Z₀} → {W : Γ ⊢ᶜ X} → {cs : CompStack Δ X Z₀} → {π : Wk Γ Δ} → {ϖ : EnvEq π γ (topCsEnv cs)} → ⟨ t i  ∥ (_﹐﹝_╎_﹞ γ W cs {π = π} {ϖ = ϖ}) ⟩ →ᴸ ⟨ i ∥ γ ⟩


data _→ᴸ*_ : LookupState X Z₀ → LookupState X Z₀ → Set where

  _◼ : (S : LookupState X Z₀) → S →ᴸ* S

  _→ᴸ⟨_⟩_ : (S : LookupState X Z₀) → {S' S'' : LookupState X Z₀} → S →ᴸ S' → S' →ᴸ* S'' → S →ᴸ* S''


data LookupHaltingState : LookupState X Z₀ → Set where

      found-unit : {γ : Env Γ Z₀} → LookupHaltingState ⟨ h ∥ _﹐_ γ u̲n̲i̲t̲ ⟩

      found-pair : {LHS : V̲a̲l̲ Γ X} → {RHS : V̲a̲l̲ Γ Y} → {γ : Env Γ Z₀} → LookupHaltingState ⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩

      found-lam : {W : (Γ ∙ X) ⊢ᶜ Y} → {γ : Env Γ Z₀} → LookupHaltingState ⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩

      found-comp : {W : Γ ⊢ᶜ X} → {γ : Env Γ Z₀} → {cs : CompStack Δ X Z₀} → {π : Wk Γ Δ} → {ϖ : EnvEq π γ (topCsEnv cs)} → LookupHaltingState ⟨ h ∥ (_﹐﹝_╎_﹞ γ W cs {π = π} {ϖ = ϖ}) ⟩

lookup-index : {S T : LookupState X Z₀} → S →ᴸ* T → (lCtx S) ∋ X
lookup-index (⟨ i ∥ _ ⟩ ◼) = i
lookup-index (⟨ h ∥ E ﹐ v̲a̲r̲ i ⟩ →ᴸ⟨ val-h-step ⟩ S→T) = h
lookup-index (⟨ t i ∥ _ ⟩ →ᴸ⟨ val-t-step ⟩ S→T) = t (lookup-index S→T)
lookup-index (⟨ t i ∥ _ ⟩ →ᴸ⟨ comp-t-step ⟩ S→T) = t (lookup-index S→T)

li≡i : {T : LookupState X Z₀} {γ : Env Γ Z₀} {i : Γ ∋ X} → (S→T : ⟨ i ∥ γ ⟩ →ᴸ* T) → LookupHaltingState T → lookup-index S→T ≡ i
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
li≡i (S →ᴸ⟨ val-t-step ⟩ S→T) (found-comp {ϖ = ϖ}) = cong t (li≡i S→T (found-comp {ϖ = ϖ}))
li≡i (S →ᴸ⟨ comp-t-step ⟩ S→T) (found-comp {ϖ = ϖ}) = cong t (li≡i S→T (found-comp {ϖ = ϖ}))

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


data _↠ᵛ_ : ValState T◾ Z₀ → ValState T◾ Z₀ → Set

data _→ᵛ_ : ValState T◾ Z₀ → ValState T◾ Z₀ → Set where

    ∘var-c  :    {γ : Env Γ Z₀} {i : Γ ∋ `V} → {tail : ValStack b T◾ Z₀} → {↥ : BottomTypeEqualsNextType b `V T◾}
              ----------------------------------------------------------------
                → ∘ ((⇡ var i ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((⭭ v̲a̲r̲ i ⊲ γ ∷ tail) {↥ = ↥})

    ∘var    :    {γ : Env Γ Z₀} {γ' : Env Γ' Z₀} {i : Γ ∋ X} → {tail : ValStack b T◾ Z₀} → {↥ : BottomTypeEqualsNextType b X T◾}
                → {M : V̲a̲l̲ Γ' X}
                → (i>>T : (⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ (γ' ﹐ M) ⟩)) → (πᵥ : Wk Γ Γ')
                -- not needed for correctness, but makes things easier:
                → EnvExt (lookup-index i>>T) γ (γ' ﹐ M)
                → WkExt πᵥ
                → EnvEq πᵥ γ γ'
                → LookupHaltingState ⟨ h ∥ (γ' ﹐ M) ⟩
              ----------------------------------------------------------------
                → ∘ ((⇡ var i ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((⭭ (wk-v̲a̲l̲ πᵥ M) ⊲ γ ∷ tail) {↥ = ↥})


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

    ∙M∷l   :  {γ' : Env Γ' Z₀} {γ : Env Γ Z₀} {M : V̲a̲l̲ Γ X} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y} → {π' : Wk Γ Γ'}
            → {tail : ValStack b T◾ Z₀} → {↥ : BottomTypeEqualsNextType b (X `× Y) T◾}
            -- not needed for correctness, but makes things easier  --→ (LHS→M : (∘ (⇡ LHS ⊲ γ' ∷ □) {↥ = 🗆}) ↠ᵛ (∙ (⭭ M ⊲ γ ∷ □) {↥ = 🗆}))
            -- → (π≡ : ⟦ γ' ⟧ᴱ ≡ ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ)
            -- → (LHS≡M : ⟦ LHS ⟧ᵛ ⟦ γ' ⟧ᴱ ≡ ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ)
              → (ϖ : EnvEq π' γ γ')
              → (∘ ((⇡ LHS ⊲ γ' ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ M ⊲ γ ∷ □) {↥ = 🗆}))
              --→ traverseᵛ LHS wk-id γ' ≡ record { Γₘₐₓ = Γ ; γₘₐₓ = γ ; πₘₐₓ = π' ; ϖₘₐₓ = ϖ ; result = M }
              ---------------------------------------------------------------------------
            →     ∙ ((⭭ M ⊲ γ ∷ ((⇡ᴸ LHS RHS ⊲ γ' ∷ tail) {↥ = ↥})) {↥ = 🗇})
                →ᵛ ∘ ((⇡ wk-val π' RHS ⊲ γ ∷ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ tail) {↥ = ↥})) {↥ = 🗇})

    ∙M∷r   :  {γ' : Env Γ' Z₀} {γ : Env Γ Z₀} {M : V̲a̲l̲ Γ Y} → {LHS : V̲a̲l̲ Γ' X} → {RHS : Γ' ⊢ᵛ Y} {π' : Wk Γ Γ'}
            → {tail : ValStack b T◾ Z₀} → {↥ : BottomTypeEqualsNextType b (X `× Y) T◾}
            -- not needed for correctness, but makes things easier
            -- → (π≡ : ⟦ γ' ⟧ᴱ ≡ ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ)
            -- → (RHS≡M : ⟦ RHS ⟧ᵛ ⟦ γ' ⟧ᴱ ≡ ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ)
              → (ϖ : EnvEq π' γ γ')
              → (∘ ((⇡ RHS ⊲ γ' ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ M ⊲ γ ∷ □) {↥ = 🗆}))
              ---------------------------------------------------------------------------
            →     ∙ ((⭭ M ⊲ γ ∷ ((⇡ᴿ LHS RHS ⊲ γ' ∷ tail) {↥ = ↥})) {↥ = 🗇})
                →ᵛ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M ⊲ γ ∷ tail) {↥ = ↥})

    ∙pair∷pm  :  {γ' : Env Γ' Z₀} {γ : Env Γ Z₀} {LHS : V̲a̲l̲ Γ X} → {RHS : V̲a̲l̲ Γ Y} → {M : Γ' ⊢ᵛ X `× Y} → {N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z}
            → {π' : Wk Γ Γ'}
            → {tail : ValStack b T◾ Z₀} → {↥ : BottomTypeEqualsNextType b Z T◾}
            -- not needed for correctness, but makes things easier
            -- →  (π≡ : ⟦ γ' ⟧ᴱ ≡ ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ)
            -- →  (p₁M≡LHS : proj₁ (⟦ M ⟧ᵛ ⟦ γ' ⟧ᴱ) ≡ ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ)
            -- →  (p₂M≡RHS : proj₂ (⟦ M ⟧ᵛ ⟦ γ' ⟧ᴱ) ≡ ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ)
              → (ϖ : EnvEq π' γ γ')
              → (∘ ((⇡ M ⊲ γ' ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ ∷ □) {↥ = 🗆}))
              ---------------------------------------------------------------------------
            →     ∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ ∷ ((⇡ᴹ M N ⊲ γ' ∷ tail) {↥ = ↥})) {↥ = 🗇})
                →ᵛ  ∘ ((⇡ (wk-val (wk-cong (wk-cong π')) N) ⊲ γ ﹐ LHS ﹐ (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ∷ tail) {↥ = ↥})

--data _↠ᵛ_ : ValState T◾ → ValState T◾ → Set where
data _↠ᵛ_ where

  _→ᵛ⟨_⟩． : (S : ValState T◾ Z₀) → {S' : ValState T◾ Z₀} → (laststep : S →ᵛ S') → S ↠ᵛ S'

  _→ᵛ⟨_⟩_ : (S : ValState T◾ Z₀) → {S' S'' : ValState T◾ Z₀} → S →ᵛ S' → S' ↠ᵛ S'' → S ↠ᵛ S''

_⨾_ : {F S T : ValState T◾ Z₀} → (F ↠ᵛ S) → (S ↠ᵛ T) → (F ↠ᵛ T)
_⨾_ (F →ᵛ⟨ F>S ⟩．) S>>T = F →ᵛ⟨ F>S ⟩ S>>T
_⨾_ (F →ᵛ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᵛ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ S₂>>T)

⟨_⟩⧻_ : {from : ValState T◾ Z₀} → {to : ValState T◾ Z₀} → (F>T : from →ᵛ to) → (tail : ValStack non-empty T◾' Z₀) → (from ⧻ tail) →ᵛ (to ⧻ tail)
⟨ ∘var-c ⟩⧻ tail = ∘var-c
⟨ ∘var T>>U π ext we ϖ H ⟩⧻ tail = ∘var T>>U π ext we ϖ H
⟨ ∘lam ⟩⧻ tail = ∘lam
⟨ ∘pair ⟩⧻ tail = ∘pair
⟨ ∘pm ⟩⧻ tail = ∘pm
⟨ ∘unit ⟩⧻ tail = ∘unit
-- ⟨ ∙pair∷pm π≡ L R ⟩⧻ tail = ∙pair∷pm π≡ L R
-- ⟨ ∙M∷l π≡ LHS≡M ⟩⧻ tail = ∙M∷l π≡ LHS≡M
-- ⟨ ∙M∷r π≡ RHS≡M ⟩⧻ tail = ∙M∷r π≡ RHS≡M
⟨ ∙pair∷pm ϖ M→P ⟩⧻ tail = ∙pair∷pm ϖ M→P
⟨ ∙M∷l ϖ LHS→M ⟩⧻ tail = ∙M∷l ϖ LHS→M
⟨ ∙M∷r ϖ RHS→M ⟩⧻ tail = ∙M∷r ϖ RHS→M

⟪_⟫⧻_ : {from : ValState T◾ Z₀} → {to : ValState T◾ Z₀} → (F>T : from ↠ᵛ to) → (tail : ValStack non-empty T◾' Z₀) → (from ⧻ tail) ↠ᵛ (to ⧻ tail)
⟪ _ →ᵛ⟨ F>T ⟩． ⟫⧻ tail =  _ →ᵛ⟨ ⟨ F>T ⟩⧻ tail ⟩．
⟪ _ →ᵛ⟨ F>T ⟩ F>>T ⟫⧻ tail =   _ →ᵛ⟨ ⟨ F>T ⟩⧻ tail ⟩ (⟪ F>>T ⟫⧻ tail)

data ValHaltingState : ValState T◾ Z₀ → Set where

    ∙_⊲_■ : (M : V̲a̲l̲ Γ X) → (γ : Env Γ Z₀) → ValHaltingState (∙ ((⭭ M ⊲ γ ∷ □) {↥ = 🗆}))

haltingTerm : {S : ValState T◾ Z₀} → (ValHaltingState S) → V̲a̲l̲ (botCtx S) (T◾)
haltingTerm ∙ M ⊲ γ ■ = M

-----------------------

data CompHaltingState : CompState Z₀ → Set where

    ret : {M : V̲a̲l̲ Γ Z₀} → {γ : Env Γ Z₀} → {ϖ : EnvEq wk-wk-ε γ (topCsEnv ◻)} → CompHaltingState ((∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ ╎ ◻ ⟩) {π = wk-wk-ε} {ϖ = ϖ} )


infixr 15 _→ᶜ⟨_⟩_
infixr 15 _→ᶜ*_
infixr 10 _⨾ᶜ_

-- Computation Machine
--------------------------------------------------

infix  15 _→ᶜ_
data _→ᶜ*_ : CompState Z₀ → CompState Z₀ → Set
data _→ᶜ_ : CompState Z₀ → CompState Z₀ → Set

data _→ᶜ_  where

      ∘return  :    {M : Γ ⊢ᵛ X} → {γ : Env Γ' Z₀} → {π : Wk Γ' Γ} → {M' : V̲a̲l̲ Γ'' X} → {γ' : Env Γ'' Z₀}
                    → {cs : CompStack Δ X Z₀} → {πₓ : Wk Γ' Δ} → {πₓ' : Wk Γ'' Δ}
                    → {ϖₓ : EnvEq πₓ γ (topCsEnv cs)} → {ϖₓ' : EnvEq πₓ' γ' (topCsEnv cs)}
                    → ((∘ ((⇡ wk-val π M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ M' ⊲ γ' ∷ □) {↥ = 🗆})))
                    ----------------------------------------------------------------
                    →     ((∘⟨ wk-comp π (return M) ⊰ γ ╎ cs ⟩) {π = πₓ} {ϖ = ϖₓ} )
                        →ᶜ ((∙⟨ r̲e̲t̲u̲r̲n̲ M' ⊰ γ' ╎ cs ⟩) {π = πₓ'} {ϖ = ϖₓ'})

      ∙return  :    {M : V̲a̲l̲ Γ X} → {γ : Env Γ Z₀} → {N : (Γ' ∙ X) ⊢ᶜ Y} → {γ' : Env Γ' Z₀} → {π : Wk Γ Γ'}
                    → {cs : CompStack Δ Y Z₀} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ' Δ}
                    → {ϖₓ : EnvEq π γ γ'} → {ϖₓ' : EnvEq πₓ γ (topCsEnv cs)} → {ϖ : EnvEq πₓ' γ' (topCsEnv cs)}
                ----------------------------------------------------------------
                  →       ((∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ ╎ ((N ⊲ γ' ⦂⦂ cs) {π = πₓ'} {ϖ = ϖ}) ⟩) {π = π} {ϖ = ϖₓ})
                        →ᶜ ((∘⟨ wk-comp (wk-cong π) N ⊰ γ ﹐ M ╎ cs ⟩) {π = wk-wk πₓ} {ϖ = EnvEq.wk-env-val-wk M ϖₓ'})

      ∘push    :    {M : Γ ⊢ᶜ X} → {N : (Γ ∙ X) ⊢ᶜ Y} → {γ : Env Γ Z₀}
                  → {cs : CompStack Δ Y Z₀} → {πₓ : Wk Γ Δ}
                  → {ϖₓ : EnvEq πₓ γ (topCsEnv cs)} → {ϖ : EnvEq πₓ γ (topCsEnv cs)}
                ----------------------------------------------------------------
                  →       ((∘⟨ push M N ⊰ γ ╎ cs ⟩) {π = πₓ} {ϖ = ϖₓ})
                      →ᶜ ((∘⟨ M ⊰ γ ╎ ((N ⊲ γ ⦂⦂ cs) {π = πₓ}  {ϖ = ϖ}) ⟩) {π = wk-id} {ϖ = enveq-id})

      ∘sub     :    {M : (Γ ∙ `V) ⊢ᶜ X} → {N : Γ ⊢ᶜ X} → {γ : Env Γ Z₀}
                  → {cs : CompStack Δ X Z₀} → {πₓ : Wk Γ Δ} → {ϖₓ : EnvEq πₓ γ (topCsEnv cs)}
                ----------------------------------------------------------------
                  →       ((∘⟨ sub M N ⊰ γ ╎ cs ⟩) {π = πₓ} {ϖ = ϖₓ})
                        →ᶜ ((∘⟨ M ⊰ ((γ ﹐﹝ N ╎ cs ﹞) {π = πₓ} {ϖ = ϖₓ}) ╎ cs ⟩) {π = wk-wk πₓ} {ϖ = EnvEq.wk-env-comp-wk N cs ϖₓ})

      ∘pm      :    {M : Γ' ⊢ᵛ X `× Y} → {γ : Env Γ Z₀} → {W : (Γ' ∙ X ∙ Y) ⊢ᶜ Z}
                  → {cs : CompStack Δ Z Z₀} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ'' Δ} → {γ'' : Env Γ'' Z₀}
                  → {ϖₓ : EnvEq πₓ γ (topCsEnv cs)} → {ϖₓ' : EnvEq πₓ' γ'' (topCsEnv cs)}
                  → {LHS : V̲a̲l̲ Γ'' X} → {RHS : V̲a̲l̲ Γ'' Y} → (π : Wk Γ Γ')
                  → ((∘ ((⇡ wk-val π M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ'' ∷ □) {↥ = 🗆}))) → (π' : Wk Γ'' Γ)
                ----------------------------------------------------------------
                  →       ((∘⟨ pm (wk-val π M) (wk-comp (wk-cong (wk-cong π)) W) ⊰ γ ╎ cs ⟩) {π = πₓ} {ϖ = ϖₓ})
                        →ᶜ ((∘⟨ wk-comp (wk-cong (wk-cong π')) (wk-comp (wk-cong (wk-cong π)) W) ⊰ γ'' ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ╎ cs ⟩)
                              {π = wk-wk (wk-wk πₓ')}  {ϖ = EnvEq.wk-env-val-wk (wk-v̲a̲l̲ (wk-wk wk-id) RHS) (EnvEq.wk-env-val-wk LHS ϖₓ')})

      ∙app-var   :     {i : Γ ∋ (Z' `⇒ Z)} → {N : V̲a̲l̲ Γ Z'} → {γ : Env Γ Z₀} → {cs : CompStack Δ Z Z₀} → {πₓ : Wk Γ Δ} → {ϖₓ : EnvEq πₓ γ (topCsEnv cs)}
                      → {W : (Γ' ∙ Z') ⊢ᶜ Z} → {γ' : Env Γ' Z₀}
                      → (⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ _﹐_ γ' (l̲a̲m̲ W) ⟩) → (πᵥ : Wk Γ Γ')
                    ----------------------------------------------------------------
                      →    ((∙⟨ a̲pp (var i) N ⊰ γ ╎ cs ⟩) {π = πₓ} {ϖ = ϖₓ})
                        →ᶜ ((∘⟨ (wk-comp (wk-cong πᵥ) W) ⊰ γ ﹐ N ╎ cs ⟩) {π = wk-wk πₓ} {ϖ = EnvEq.wk-env-val-wk N ϖₓ})

      ∙app-pm     :    {M : Γ ⊢ᵛ (X `× Y)} → {N₁ : (Γ ∙ X ∙ Y) ⊢ᵛ (Z' `⇒ Z)} → {N : V̲a̲l̲ Γ Z'} → {γ : Env Γ Z₀}
                      → {cs : CompStack Δ Z Z₀} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ' Δ}
                      → {LHS : V̲a̲l̲ Γ' X} → {RHS : V̲a̲l̲ Γ' Y} → {γ' : Env Γ' Z₀}
                      → {ϖₓ : EnvEq πₓ γ (topCsEnv cs)} → {ϖₓ' : EnvEq πₓ' γ' (topCsEnv cs)}
                      → ((∘ ((⇡ M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ' ∷ □) {↥ = 🗆}))) → (π : Wk Γ' Γ)
                    ----------------------------------------------------------------
                      →    ((∙⟨ a̲pp (pm M N₁) N ⊰ γ ╎ cs ⟩) {π = πₓ} {ϖ = ϖₓ})
                        →ᶜ ((∙⟨ a̲pp ((wk-val (wk-cong (wk-cong π)) N₁)) (wk-v̲a̲l̲ (wk-wk (wk-wk π)) N) ⊰ γ' ﹐ LHS ﹐ (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ╎ cs ⟩)
                              {π = wk-wk (wk-wk πₓ')} {ϖ = EnvEq.wk-env-val-wk (wk-v̲a̲l̲ (wk-wk wk-id) RHS) (EnvEq.wk-env-val-wk LHS ϖₓ')})

      ∙app-lam     :   {W : (Γ ∙ X) ⊢ᶜ Y} → {N : V̲a̲l̲ Γ X} → {γ : Env Γ Z₀}
                      → {cs : CompStack Δ Y Z₀} → {πₓ : Wk Γ Δ} → {ϖₓ : EnvEq πₓ γ (topCsEnv cs)}
                    ----------------------------------------------------------------
                      → ((∙⟨ a̲pp (lam W) N ⊰ γ ╎ cs ⟩) {π = πₓ} {ϖ = ϖₓ}) →ᶜ ((∘⟨ W ⊰ γ ﹐ N ╎ cs ⟩) {π = wk-wk πₓ} {ϖ = EnvEq.wk-env-val-wk N ϖₓ})

      ∘app         :   {M : Γ ⊢ᵛ X `⇒ Y} → {N : Γ ⊢ᵛ X} → {γ : Env Γ Z₀} → {cs : CompStack Δ Y Z₀} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ' Δ}
                      → {N' : V̲a̲l̲ Γ' X} → {γ' : Env Γ' Z₀} → {ϖₓ : EnvEq πₓ γ (topCsEnv cs)} → {ϖₓ' : EnvEq πₓ' γ' (topCsEnv cs)}
                      → ((∘ ((⇡ N ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ N' ⊲ γ' ∷ □) {↥ = 🗆}))) → (π : Wk Γ' Γ)
                    ----------------------------------------------------------------
                      →    ((∘⟨ app M N ⊰ γ ╎ cs ⟩) {π = πₓ} {ϖ = ϖₓ})
                        →ᶜ ((∙⟨ a̲pp (wk-val π M) N' ⊰ γ' ╎ cs ⟩) {π = πₓ'} {ϖ = ϖₓ'})

      ∘var         :   {M : Γ ⊢ᵛ `V} → {γ : Env Γ Z₀} → {i : Γ' ∋ `V} → {γ' : Env Γ' Z₀} → {W : Γ'' ⊢ᶜ X'} → {γ'' : Env Γ'' Z₀}
                      → {cs : CompStack Δ X Z₀} → {cs' : CompStack Δ' X' Z₀} → {πₓ : Wk Γ Δ} → {πₓ'' : Wk Γ'' Δ'}
                      → {ϖₓ : EnvEq πₓ γ (topCsEnv cs)} → {ϖₓ'' : EnvEq πₓ'' γ'' (topCsEnv cs')}
                      → ((∘ ((⇡ M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ v̲a̲r̲ i ⊲ γ' ∷ □) {↥ = 🗆}))) → (π' : Wk Γ' Γ)
                      → (⟨ i ∥ γ' ⟩ →ᴸ* ⟨ h ∥ ((γ'' ﹐﹝ W ╎ cs' ﹞) {π = πₓ''} {ϖ = ϖₓ''}) ⟩) → (πᵥ : Wk Γ' Γ'')
                ----------------------------------------------------------------
                      →    ((∘⟨ var M ⊰ γ ╎ cs ⟩) {π = πₓ} {ϖ = ϖₓ})
                        →ᶜ ((∘⟨ W ⊰ γ'' ╎ cs' ⟩) {π = πₓ''} {ϖ = ϖₓ''})

data _→ᶜ*_ where

  _◼ : (S : CompState Z₀) → S →ᶜ* S

  _→ᶜ⟨_⟩_ : (S : CompState Z₀) → {S' S'' : CompState Z₀} → S →ᶜ S' → S' →ᶜ* S'' → S →ᶜ* S''

_⨾ᶜ_ : {F S T : CompState Z₀} → (F →ᶜ* S) → (S →ᶜ* T) → (F →ᶜ* T)
_⨾ᶜ_ (S ◼) S>>T = S>>T
_⨾ᶜ_ (F →ᶜ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᶜ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ᶜ S₂>>T)


valstate-wk : {S S' : ValState X Z₀} → S →ᵛ S' → Wk (topCtx S') (topCtx S)
valstate-wk ∘var-c = wk-id
valstate-wk (∘var i>>T πᵥ x x₁ x₂ x₃) = wk-id
valstate-wk ∘lam = wk-id
valstate-wk ∘pair = wk-id
valstate-wk ∘pm = wk-id
valstate-wk ∘unit = wk-id
-- valstate-wk (∙M∷l π≡ LHS≡M) = wk-id
-- valstate-wk (∙M∷r π≡ RHS≡M) = wk-id
-- valstate-wk (∙pair∷pm {tail = tail} {↥ = ↥} π≡ p₁M≡LHS p₂M≡RHS) = wk-wk (wk-wk wk-id)
valstate-wk (∙M∷l ϖ LHS→M) = wk-id
valstate-wk (∙M∷r ϖ RHS→M) = wk-id
valstate-wk (∙pair∷pm {tail = tail} {↥ = ↥} ϖ M→P) = wk-wk (wk-wk wk-id)


valstate-env-eq : {S S' : ValState X Z₀} → (S→S' : S →ᵛ S') → EnvEq (valstate-wk S→S') (topEnv S') (topEnv S)
valstate-env-eq ∘var-c = enveq-id
valstate-env-eq (∘var i>>T πᵥ x x₁ x₂ x₃) = enveq-id
valstate-env-eq ∘lam = enveq-id
valstate-env-eq ∘pair = enveq-id
valstate-env-eq ∘pm = enveq-id
valstate-env-eq ∘unit = enveq-id
--valstate-env-eq (∙M∷l π≡ LHS≡M) = enveq-id
valstate-env-eq (∙M∷l ϖ LHS→M) = enveq-id
--valstate-env-eq (∙M∷r π≡ RHS≡M) = enveq-id
valstate-env-eq (∙M∷r ϖ RHS→M) = enveq-id
--valstate-env-eq (∙pair∷pm {Γ = Γ} {X = X} {Y = Y} {Z = Z} {γ' = γ'} {γ = γ} {LHS = LHS} {RHS = RHS} {M = M} {N = N} {π' = π'} {tail = tail} {↥ = ↥} π≡ p₁M≡LHS p₂M≡RHS) =
valstate-env-eq (∙pair∷pm {Γ = Γ} {X = X} {Y = Y} {Z = Z} {γ' = γ'} {γ = γ} {LHS = LHS} {RHS = RHS} {M = M} {N = N} {π' = π'} {tail = tail} {↥ = ↥} ϖ M→P) =
                let
                  goal : EnvEq (wk-wk (wk-wk wk-id)) (γ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS) γ
                  goal = wk-env-val-wk (wk-v̲a̲l̲ (wk-wk wk-id) RHS) (wk-env-val-wk LHS enveq-id)
                in
                goal

valstate-wkext : {S S' : ValState X Z₀} → (S→S' : S →ᵛ S') → WkExt (valstate-wk S→S')
valstate-wkext ∘var-c = wk-eq _
valstate-wkext (∘var i>>T πᵥ x x₁ x₂ x₃) = wk-eq _
valstate-wkext ∘lam = wk-eq _
valstate-wkext ∘pair = wk-eq _
valstate-wkext ∘pm = wk-eq _
valstate-wkext ∘unit = wk-eq _
--valstate-wkext (∙M∷l π≡ LHS≡M) = wk-eq _
--valstate-wkext (∙M∷r π≡ RHS≡M) = wk-eq _
--valstate-wkext (∙pair∷pm π≡ p₁M≡LHS p₂M≡RHS) = wk-ext (wk-wk wk-id) (wk-ext wk-id (wk-eq wk-id))
valstate-wkext (∙M∷l _ _) = wk-eq _
valstate-wkext (∙M∷r _ _) = wk-eq _
valstate-wkext (∙pair∷pm _ _) = wk-ext (wk-wk wk-id) (wk-ext wk-id (wk-eq wk-id))
