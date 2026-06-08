{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Machine (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Function.Base using (const; _∘_; _$_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; cong-app; dcong₂; sym; trans; subst; subst₂)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Unit
open import Data.Nat
open import Data.List using (List; _∷_; []; _++_)

open import Inception.Sub.Equality

open import Inception.Sub.Environments R

-----------------------------------------------------------------------

module MachineMain {R₀ : Ty} (k₀ : ⟦ R₀ ⟧ → R) where

  open EnvMain {R₀ = R₀} k₀

  infixr 17 _→ᵛ⟨_⟩．
  infixr 15 _→ᵛ⟨_⟩_
  infix  15 _→ᵛ_
  infix  15 _→ᴸ_
  infixr 10 _⨾_

  ------------------------------------------------------------------------------
  -- Lookup Machine
  ------------------------------------------------------------------------------

  data LookupState : Ty → Set where

      ⟨_∥_⟩   :  (i : Γ ∋ X) → Env Γ → LookupState X

  ⟦_⟧ᴸ : (S : LookupState X) → ⟦ X ⟧
  ⟦ ⟨ i ∥ E ⟩ ⟧ᴸ = ⟦ i ⟧ᵐ ⟦ E ⟧ᴱ

  lCtx : (S : LookupState X) → Ctx
  lCtx (⟨_∥_⟩ {Γ = Γ} i E)= Γ

  lTCtx : (S : LookupState X) → Ctx
  lTCtx (⟨_∥_⟩ i ∗) = ε
  lTCtx (⟨_∥_⟩ i (_﹐_ {Γ = Γ} E M)) = Γ
  lTCtx (⟨_∥_⟩ i (_﹐﹝_╎_﹞ {Γ = Γ} E M k)) = Γ

  lEnv : (S : LookupState X) → Env (lCtx S)
  lEnv ⟨ i ∥ E ⟩ = E

  lTEnv : (S : LookupState X) → Env (lTCtx S)
  lTEnv ⟨ i ∥ E ﹐ M ⟩ = E
  lTEnv ⟨ i ∥ E ﹐﹝ M ╎ cs ﹞ ⟩ = E

  data _→ᴸ_ : LookupState X → LookupState X → Set where

      val-h-step    : {E : Env Γ} → {i : Γ ∋ `V} → ⟨ h  ∥ E ﹐ (v̲a̲r̲ i) ⟩ →ᴸ ⟨ i ∥ E ⟩

      val-t-step    : {i : Γ ∋ Y} → {E : Env Γ} → {M : V̲a̲l̲ Γ X} → ⟨ t i  ∥ _﹐_ E M ⟩ →ᴸ ⟨ i ∥ E ⟩

      comp-t-step   : {i : Γ ∋ Y} → {γ : Env Γ} → {W : Γ ⊢ᶜ X} → {cs : CompStack Δ X} → {π : Wk Γ Δ} → .{wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → ⟨ t i  ∥ (_﹐﹝_╎_﹞ γ W cs {π = π} {wk≡ = wk≡}) ⟩ →ᴸ ⟨ i ∥ γ ⟩


  data _→ᴸ*_ : LookupState X → LookupState X → Set where

    _◼ : (S : LookupState X) → S →ᴸ* S

    _→ᴸ⟨_⟩_ : (S : LookupState X) → {S' S'' : LookupState X} → S →ᴸ S' → S' →ᴸ* S'' → S →ᴸ* S''


  data LookupHaltingState : LookupState X → Set where

        found-unit : {γ : Env Γ} → LookupHaltingState ⟨ h ∥ _﹐_ γ u̲n̲i̲t̲ ⟩

        found-pair : {LHS : V̲a̲l̲ Γ X} → {RHS : V̲a̲l̲ Γ Y} → {γ : Env Γ} → LookupHaltingState ⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩

        found-lam : {W : (Γ ∙ X) ⊢ᶜ Y} → {γ : Env Γ} → LookupHaltingState ⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩

        found-comp : {W : Γ ⊢ᶜ X} → {γ : Env Γ} → {cs : CompStack Δ X} → {π : Wk Γ Δ} → .{wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → LookupHaltingState ⟨ h ∥ (_﹐﹝_╎_﹞ γ W cs {π = π} {wk≡ = wk≡}) ⟩

  lookup-index : {S T : LookupState X} → S →ᴸ* T → (lCtx S) ∋ X
  lookup-index (⟨ i ∥ _ ⟩ ◼) = i
  lookup-index (⟨ h ∥ E ﹐ v̲a̲r̲ i ⟩ →ᴸ⟨ val-h-step ⟩ S→T) = h
  lookup-index (⟨ t i ∥ _ ⟩ →ᴸ⟨ val-t-step ⟩ S→T) = t (lookup-index S→T)
  lookup-index (⟨ t i ∥ _ ⟩ →ᴸ⟨ comp-t-step ⟩ S→T) = t (lookup-index S→T)

  li≡i : {T : LookupState X} {γ : Env Γ} {i : Γ ∋ X} → (S→T : ⟨ i ∥ γ ⟩ →ᴸ* T) → LookupHaltingState T → lookup-index S→T ≡ i
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
  li≡i (S →ᴸ⟨ val-t-step ⟩ S→T) (found-comp {wk≡ = wk≡}) = cong t (li≡i S→T (found-comp {wk≡ = wk≡}))
  li≡i (S →ᴸ⟨ comp-t-step ⟩ S→T) (found-comp {wk≡ = wk≡}) = cong t (li≡i S→T (found-comp {wk≡ = wk≡}))

  ------------------------------------------------------------------------------
  -- Value Machine
  ------------------------------------------------------------------------------

  -------

  data _↠ᵛ_ : ValState T◾ → ValState T◾ → Set

  data _→ᵛ_ : ValState T◾ → ValState T◾ → Set where

      ∘var-c  :    {i : Γ ∋ `V} → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b `V T◾}
                ----------------------------------------------------------------
                  → ∘ ((⇡ var i ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((⭭ v̲a̲r̲ i ⊲ γ ∷ tail) {↥ = ↥})

      ∘var    :    {i : Γ ∋ X} → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b X T◾}
                  → {M : V̲a̲l̲ Γ' X}
                  → (i>>T : (⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ (γ' ﹐ M) ⟩)) → (πᵥ : Wk Γ Γ')
                  -- not needed for correctness, but makes things easier:
                  → EnvExt (lookup-index i>>T) γ (γ' ﹐ M)
                  → WkExt πᵥ
                  → EnvEq πᵥ γ γ'
                  → LookupHaltingState ⟨ h ∥ (γ' ﹐ M) ⟩
                ----------------------------------------------------------------
                  → ∘ ((⇡ var i ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((⭭ (wk-v̲a̲l̲ πᵥ M) ⊲ γ ∷ tail) {↥ = ↥})


      ∘lam   :  {M : (Γ ∙ X) ⊢ᶜ Y} → {γ  : Env Γ}
              → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b (X `⇒ Y) T◾}
                ---------------------------------------------------------------------------
              →     ∘ ((⇡ lam M ⊲ γ ∷ tail) {↥ = ↥})
                  →ᵛ ∙ ((⭭ l̲a̲m̲ M ⊲ γ ∷ tail) {↥ = ↥})

      ∘pair  :  {LHS : Γ ⊢ᵛ X} → {RHS : Γ ⊢ᵛ Y}
              → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b (X `× Y) T◾}
                ---------------------------------------------------------------------------
              →     ∘ ((⇡ pair LHS RHS ⊲ γ ∷ tail) {↥ = ↥})
                  →ᵛ ∘ ((⇡ LHS ⊲ γ ∷ ((⇡ᴸ LHS RHS ⊲ γ ∷ tail) {↥ = ↥})) {↥ = 🗇})

      ∘pm    :  {M : Γ ⊢ᵛ X `× Y} → {N : (Γ ∙ X ∙ Y) ⊢ᵛ Z}
              → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b Z T◾}
                ---------------------------------------------------------------------------
              →     ∘ ((⇡ pm M N ⊲ γ ∷ tail) {↥ = ↥})
                  →ᵛ ∘ ((⇡ M ⊲ γ ∷ (⇡ᴹ M N ⊲ γ ∷ tail) {↥ = ↥}) {↥ = 🗇})

      ∘unit  :  {γ  : Env Γ}
              → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b `Unit T◾}
                ---------------------------------------------------------------------------
              →     ∘ ((⇡ unit ⊲ γ ∷ tail) {↥ = ↥})
                  →ᵛ ∙ ((⭭ u̲n̲i̲t̲ ⊲ γ ∷ tail) {↥ = ↥})

      ∙M∷l   :  {M : V̲a̲l̲ Γ X} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y} → {π' : Wk Γ Γ'}
              → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b (X `× Y) T◾}
              -- not needed for correctness, but makes things easier  --→ (LHS→M : (∘ (⇡ LHS ⊲ γ' ∷ □) {↥ = 🗆}) ↠ᵛ (∙ (⭭ M ⊲ γ ∷ □) {↥ = 🗆}))
              → (π≡ : ⟦ γ' ⟧ᴱ ≡ ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ)
              → (LHS≡M : ⟦ LHS ⟧ᵛ ⟦ γ' ⟧ᴱ ≡ ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ)
                ---------------------------------------------------------------------------
              →     ∙ ((⭭ M ⊲ γ ∷ ((⇡ᴸ LHS RHS ⊲ γ' ∷ tail) {↥ = ↥})) {↥ = 🗇})
                  →ᵛ ∘ ((⇡ wk-val π' RHS ⊲ γ ∷ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ tail) {↥ = ↥})) {↥ = 🗇})

      ∙M∷r   :  {M : V̲a̲l̲ Γ Y} → {LHS : V̲a̲l̲ Γ' X} → {RHS : Γ' ⊢ᵛ Y} {π' : Wk Γ Γ'}
              → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b (X `× Y) T◾}
              -- not needed for correctness, but makes things easier
              → (π≡ : ⟦ γ' ⟧ᴱ ≡ ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ)
              → (RHS≡M : ⟦ RHS ⟧ᵛ ⟦ γ' ⟧ᴱ ≡ ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ)
                ---------------------------------------------------------------------------
              →     ∙ ((⭭ M ⊲ γ ∷ ((⇡ᴿ LHS RHS ⊲ γ' ∷ tail) {↥ = ↥})) {↥ = 🗇})
                  →ᵛ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M ⊲ γ ∷ tail) {↥ = ↥})

      ∙pair∷pm  :  {LHS : V̲a̲l̲ Γ X} → {RHS : V̲a̲l̲ Γ Y} → {M : Γ' ⊢ᵛ X `× Y} → {N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z}
              → {π' : Wk Γ Γ'}
              → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b Z T◾}
              -- not needed for correctness, but makes things easier
              →  (π≡ : ⟦ γ' ⟧ᴱ ≡ ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ)
              →  (p₁M≡LHS : proj₁ (⟦ M ⟧ᵛ ⟦ γ' ⟧ᴱ) ≡ ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ)
              →  (p₂M≡RHS : proj₂ (⟦ M ⟧ᵛ ⟦ γ' ⟧ᴱ) ≡ ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ)
                ---------------------------------------------------------------------------
              →     ∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ ∷ ((⇡ᴹ M N ⊲ γ' ∷ tail) {↥ = ↥})) {↥ = 🗇})
                  →ᵛ  ∘ ((⇡ (wk-val (wk-cong (wk-cong π')) N) ⊲ γ ﹐ LHS ﹐ (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ∷ tail) {↥ = ↥})

  --data _↠ᵛ_ : ValState T◾ → ValState T◾ → Set where
  data _↠ᵛ_ where

    _→ᵛ⟨_⟩． : (S : ValState T◾) → {S' : ValState T◾} → (laststep : S →ᵛ S') → S ↠ᵛ S'

    _→ᵛ⟨_⟩_ : (S : ValState T◾) → {S' S'' : ValState T◾} → S →ᵛ S' → S' ↠ᵛ S'' → S ↠ᵛ S''

  _⨾_ : {F S T : ValState T◾} → (F ↠ᵛ S) → (S ↠ᵛ T) → (F ↠ᵛ T)
  _⨾_ (F →ᵛ⟨ F>S ⟩．) S>>T = F →ᵛ⟨ F>S ⟩ S>>T
  _⨾_ (F →ᵛ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᵛ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ S₂>>T)

  _⧺_ : ValStack b T◾ → ValStack non-empty T◾' → ValStack non-empty T◾'
  □ ⧺ lower = lower
  (M ⊲ γ ∷ upper) ⧺ lower = (M ⊲ γ ∷ (upper ⧺ lower)) {↥ = 🗇}

  _⧻_ : (upper : ValState T◾) → ValStack non-empty T◾' → ValState T◾'
  (∘ upper) ⧻ lower = ∘ (upper ⧺ lower)
  (∙ upper) ⧻ lower = ∙ (upper ⧺ lower)

  ⟨_⟩⧻_ : {from : ValState T◾} → {to : ValState T◾} → (F>T : from →ᵛ to) → (tail : ValStack non-empty T◾') → (from ⧻ tail) →ᵛ (to ⧻ tail)
  ⟨ ∘var-c ⟩⧻ tail = ∘var-c
  ⟨ ∘var T>>U π ext we ϖ H ⟩⧻ tail = ∘var T>>U π ext we ϖ H
  ⟨ ∘lam ⟩⧻ tail = ∘lam
  ⟨ ∘pair ⟩⧻ tail = ∘pair
  ⟨ ∘pm ⟩⧻ tail = ∘pm
  ⟨ ∘unit ⟩⧻ tail = ∘unit
  ⟨ ∙pair∷pm π≡ L R ⟩⧻ tail = ∙pair∷pm π≡ L R
  ⟨ ∙M∷l π≡ LHS≡M ⟩⧻ tail = ∙M∷l π≡ LHS≡M
  ⟨ ∙M∷r π≡ RHS≡M ⟩⧻ tail = ∙M∷r π≡ RHS≡M

  ⟪_⟫⧻_ : {from : ValState T◾} → {to : ValState T◾} → (F>T : from ↠ᵛ to) → (tail : ValStack non-empty T◾') → (from ⧻ tail) ↠ᵛ (to ⧻ tail)
  ⟪ _ →ᵛ⟨ F>T ⟩． ⟫⧻ tail =  _ →ᵛ⟨ ⟨ F>T ⟩⧻ tail ⟩．
  ⟪ _ →ᵛ⟨ F>T ⟩ F>>T ⟫⧻ tail =   _ →ᵛ⟨ ⟨ F>T ⟩⧻ tail ⟩ (⟪ F>>T ⟫⧻ tail)

  ⟦_⟧ᵛˢ : (S : ValStack non-empty T◾) → ⟦ T◾ ⟧
  ⟦ (⭭ x ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ toVal x ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⇡ M ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ M ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⇡ᴹ M N ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ pm M N ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⇡ᴸ LHS RHS ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ pair LHS RHS ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⇡ᴿ LHS RHS ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ pair (toVal LHS) RHS ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⭭ x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ
  ⟦ (⇡ M ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ
  ⟦ (⇡ᴹ M N ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ
  ⟦ (⇡ᴸ LHS RHS ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ
  ⟦ (⇡ᴿ LHS RHS ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ


  ⟦_⟧ᵛꟴ : (S : ValState T◾) → ⟦ T◾ ⟧
  ⟦ ∘ tail ⟧ᵛꟴ = ⟦ tail ⟧ᵛˢ
  ⟦ ∙ tail ⟧ᵛꟴ = ⟦ tail ⟧ᵛˢ

  topStackCtx : (S : ValStack non-empty T◾) → Ctx
  topStackCtx (_⊲_∷_ {Γ = Γ} _ _ _) = Γ

  topCtx : ValState T◾ → Ctx
  topCtx (∘ S) = topStackCtx S
  topCtx (∙ S) = topStackCtx S

  topStackEnv : (S : ValStack non-empty T◾) → Env (topStackCtx S)
  topStackEnv (_⊲_∷_ _ γ _) = γ

  topEnv : (S : ValState T◾) → Env (topCtx S)
  topEnv (∘ S) = topStackEnv S
  topEnv (∙ S) = topStackEnv S

  data ValHaltingState : ValState T◾ → Set where

      ∙_⊲_■ : (M : V̲a̲l̲ Γ X) → (γ : Env Γ) → ValHaltingState (∙ ((⭭ M ⊲ γ ∷ □) {↥ = 🗆}))

  botStackCtx : ValStack non-empty T◾ → Ctx
  botStackCtx ((_⊲_∷_) {Γ = Γ} _ _ □) = Γ
  botStackCtx ((x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})) {↥ = ↥}) = botStackCtx ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})

  botCtx : ValState T◾ → Ctx
  botCtx (∘ S) = botStackCtx S
  botCtx (∙ S) = botStackCtx S

  botStackEnv : (S : ValStack non-empty T◾) → Env (botStackCtx S)
  botStackEnv ((_⊲_∷_) {Γ = Γ} _ γ □) = γ
  botStackEnv ((x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})) {↥ = ↥}) = botStackEnv ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})

  botEnv : (S : ValState T◾) → Env (botCtx S)
  botEnv (∘ S) = botStackEnv S
  botEnv (∙ S) = botStackEnv S

  botStackTerm : (S : ValStack non-empty T◾) → PartialTerm (botStackCtx S) (T◾)
  botStackTerm ((_⊲_∷_) {Γ = Γ} M γ □ {↥ = 🗆}) = M
  botStackTerm ((x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})) {↥ = ↥}) = botStackTerm ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})

  -- botTerm : (S : ValState T◾) → PartialTerm (botCtx S) (T◾)
  -- botTerm (∘ S) = botStackTerm S
  -- botTerm (∙ S) = botStackTerm S

  haltingTerm : {S : ValState T◾} → (ValHaltingState S) → V̲a̲l̲ (botCtx S) (T◾)
  haltingTerm ∙ M ⊲ γ ■ = M

-----------------------

  data CompState : Set where

        ∘⟨_⊰_╎_⟩ : (W : Γ ⊢ᶜ X) → (γ : Env Γ) → (cs : CompStack Δ X) → {π : Wk Γ Δ} → .{wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → CompState

        ∙⟨_⊰_╎_⟩ : (W : C̲o̲m̲p Γ X) → (γ : Env Γ) → (cs : CompStack Δ X) → {π : Wk Γ Δ} → .{wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → CompState

  data CompHaltingState : CompState → Set where

      ret : {M : V̲a̲l̲ Γ R₀} → {γ : Env Γ} → CompHaltingState ((∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ ╎ ◻ ⟩) {π = wk-wk-ε} {wk≡ = refl} )


  infixr 15 _→ᶜ⟨_⟩_
  infixr 15 _→ᶜ*_
  infixr 10 _⨾ᶜ_

  ⟦_⟧ᶜꟴ : CompState → R
  ⟦ ∘⟨ W ⊰ γ ╎ cs ⟩ ⟧ᶜꟴ = ⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ
  ⟦ ∙⟨ W ⊰ γ ╎ cs ⟩ ⟧ᶜꟴ = ⟦ toComp W ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ

  -- Computation Machine
  --------------------------------------------------

  infix  15 _→ᶜ_
  data _→ᶜ*_ : CompState → CompState → Set
  data _→ᶜ_ : CompState → CompState → Set

  data _→ᶜ_  where

        ∘return  :    {M : Γ ⊢ᵛ X} → {γ : Env Γ'} → {π : Wk Γ' Γ} → {M' : V̲a̲l̲ Γ'' X} → {γ' : Env Γ''}
                      → {cs : CompStack Δ X} → {πₓ : Wk Γ' Δ} → {πₓ' : Wk Γ'' Δ}
                      → .{wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → .{wk≡ₓ' : ⟦ πₓ' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                      → ((∘ ((⇡ wk-val π M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ M' ⊲ γ' ∷ □) {↥ = 🗆})))
                     ----------------------------------------------------------------
                      →     ((∘⟨ wk-comp π (return M) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ} )
                         →ᶜ ((∙⟨ r̲e̲t̲u̲r̲n̲ M' ⊰ γ' ╎ cs ⟩) {π = πₓ'} {wk≡ = wk≡ₓ'})

        ∙return  :    {M : V̲a̲l̲ Γ X} → {γ : Env Γ} → {N : (Γ' ∙ X) ⊢ᶜ Y} → {γ' : Env Γ'} → {π : Wk Γ Γ'}
                      → {cs : CompStack Δ Y} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ' Δ}
                      → .{wk≡ₓ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ} → .{wk≡ₓ' : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → .{wk≡ : ⟦ πₓ' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ }
                  ----------------------------------------------------------------
                    →       ((∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ ╎ ((N ⊲ γ' ⦂⦂ cs) {π = πₓ'} {wk≡ = wk≡}) ⟩) {π = π} {wk≡ = wk≡ₓ})
                         →ᶜ ((∘⟨ wk-comp (wk-cong π) N ⊰ γ ﹐ M ╎ cs ⟩) {π = wk-wk πₓ} {wk≡ = wk≡ₓ'})

        ∘push    :    {M : Γ ⊢ᶜ X} → {N : (Γ ∙ X) ⊢ᶜ Y} → {γ : Env Γ}
                    → {cs : CompStack Δ Y} → {πₓ : Wk Γ Δ}
                    → .{wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → .{wk≡ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                  ----------------------------------------------------------------
                    →       ((∘⟨ push M N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ})

                        →ᶜ ((∘⟨ M ⊰ γ ╎ ((N ⊲ γ ⦂⦂ cs) {π = πₓ}  {wk≡ = wk≡}) ⟩) {π = wk-id} {wk≡ = refl})

        ∘sub     :    {M : (Γ ∙ `V) ⊢ᶜ X} → {N : Γ ⊢ᶜ X} → {γ : Env Γ}
                    → {cs : CompStack Δ X} → {πₓ : Wk Γ Δ} → .{wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                  ----------------------------------------------------------------
                    →       ((∘⟨ sub M N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ})
                         →ᶜ ((∘⟨ M ⊰ ((γ ﹐﹝ N ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡ₓ}) ╎ cs ⟩) {π = wk-wk πₓ} {wk≡ = wk≡ₓ})

        ∘pm      :    {M : Γ' ⊢ᵛ X `× Y} → {γ : Env Γ} → {W : (Γ' ∙ X ∙ Y) ⊢ᶜ Z}
                    → {cs : CompStack Δ Z} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ'' Δ} → {γ'' : Env Γ''}
                    → .{wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → .{wk≡ₓ' : ⟦ πₓ' ⟧ʷ ⟦ γ'' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                    → {LHS : V̲a̲l̲ Γ'' X} → {RHS : V̲a̲l̲ Γ'' Y} → (π : Wk Γ Γ')
                    → ((∘ ((⇡ wk-val π M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ'' ∷ □) {↥ = 🗆}))) → (π' : Wk Γ'' Γ)
                  ----------------------------------------------------------------
                    →       ((∘⟨ pm (wk-val π M) (wk-comp (wk-cong (wk-cong π)) W) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ})
                         →ᶜ ((∘⟨ wk-comp (wk-cong (wk-cong π')) (wk-comp (wk-cong (wk-cong π)) W) ⊰ γ'' ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ╎ cs ⟩)
                               {π = wk-wk (wk-wk πₓ')}  {wk≡ = wk≡ₓ'})

        ∙app-var   :     {i : Γ ∋ (Z' `⇒ Z)} → {N : V̲a̲l̲ Γ Z'} → {γ : Env Γ} → {cs : CompStack Δ Z} → {πₓ : Wk Γ Δ} → .{wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → {W : (Γ' ∙ Z') ⊢ᶜ Z} → {γ' : Env Γ'}
                       → (⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ _﹐_ γ' (l̲a̲m̲ W) ⟩) → (πᵥ : Wk Γ Γ')
                     ----------------------------------------------------------------
                       →    ((∙⟨ a̲pp (var i) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ})
                         →ᶜ ((∘⟨ (wk-comp (wk-cong πᵥ) W) ⊰ γ ﹐ N ╎ cs ⟩) {π = wk-wk πₓ} {wk≡ = wk≡ₓ})

        ∙app-pm     :    {M : Γ ⊢ᵛ (X `× Y)} → {N₁ : (Γ ∙ X ∙ Y) ⊢ᵛ (Z' `⇒ Z)} → {N : V̲a̲l̲ Γ Z'} → {γ : Env Γ}
                       → {cs : CompStack Δ Z} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ' Δ}
                       → {LHS : V̲a̲l̲ Γ' X} → {RHS : V̲a̲l̲ Γ' Y} → {γ' : Env Γ'}
                       → .{wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → .{wk≡ₓ' : ⟦ πₓ' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → ((∘ ((⇡ M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ' ∷ □) {↥ = 🗆}))) → (π : Wk Γ' Γ)
                     ----------------------------------------------------------------
                       →    ((∙⟨ a̲pp (pm M N₁) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ})
                         →ᶜ ((∙⟨ a̲pp ((wk-val (wk-cong (wk-cong π)) N₁)) (wk-v̲a̲l̲ (wk-wk (wk-wk π)) N) ⊰ γ' ﹐ LHS ﹐ (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ╎ cs ⟩)
                               {π = wk-wk (wk-wk πₓ')} {wk≡ = wk≡ₓ'})

        ∙app-lam     :   {W : (Γ ∙ X) ⊢ᶜ Y} → {N : V̲a̲l̲ Γ X} → {γ : Env Γ}
                       → {cs : CompStack Δ Y} → {πₓ : Wk Γ Δ} → .{wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                     ----------------------------------------------------------------
                       → ((∙⟨ a̲pp (lam W) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ}) →ᶜ ((∘⟨ W ⊰ γ ﹐ N ╎ cs ⟩) {π = wk-wk πₓ} {wk≡ = wk≡ₓ})

        ∘app         :   {M : Γ ⊢ᵛ X `⇒ Y} → {N : Γ ⊢ᵛ X} → {γ : Env Γ} → {cs : CompStack Δ Y} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ' Δ}
                       → {N' : V̲a̲l̲ Γ' X} → {γ' : Env Γ'} → .{wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → .{wk≡ₓ' : ⟦ πₓ' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → ((∘ ((⇡ N ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ N' ⊲ γ' ∷ □) {↥ = 🗆}))) → (π : Wk Γ' Γ)
                     ----------------------------------------------------------------
                       →    ((∘⟨ app M N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ})
                         →ᶜ ((∙⟨ a̲pp (wk-val π M) N' ⊰ γ' ╎ cs ⟩) {π = πₓ'} {wk≡ = wk≡ₓ'})

        ∘var         :   {M : Γ ⊢ᵛ `V} → {γ : Env Γ} → {i : Γ' ∋ `V} → {γ' : Env Γ'} → {W : Γ'' ⊢ᶜ X'} → {γ'' : Env Γ''}
                       → {cs : CompStack Δ X} → {cs' : CompStack Δ' X'} → {πₓ : Wk Γ Δ} → {πₓ'' : Wk Γ'' Δ'}
                       → .{wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → .{wk≡ₓ'' : ⟦ πₓ'' ⟧ʷ ⟦ γ'' ⟧ᴱ ≡ ⟦ topCsEnv cs' ⟧ᴱ}
                       → ((∘ ((⇡ M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ v̲a̲r̲ i ⊲ γ' ∷ □) {↥ = 🗆}))) → (π' : Wk Γ' Γ)
                       → (⟨ i ∥ γ' ⟩ →ᴸ* ⟨ h ∥ ((γ'' ﹐﹝ W ╎ cs' ﹞) {π = πₓ''} {wk≡ = wk≡ₓ''}) ⟩) → (πᵥ : Wk Γ' Γ'')
                  ----------------------------------------------------------------
                       →    ((∘⟨ var M ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ})
                         →ᶜ ((∘⟨ W ⊰ γ'' ╎ cs' ⟩) {π = πₓ''} {wk≡ = wk≡ₓ''})

  data _→ᶜ*_ where

    _◼ : (S : CompState) → S →ᶜ* S

    _→ᶜ⟨_⟩_ : (S : CompState) → {S' S'' : CompState} → S →ᶜ S' → S' →ᶜ* S'' → S →ᶜ* S''

  _⨾ᶜ_ : {F S T : CompState} → (F →ᶜ* S) → (S →ᶜ* T) → (F →ᶜ* T)
  _⨾ᶜ_ (S ◼) S>>T = S>>T
  _⨾ᶜ_ (F →ᶜ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᶜ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ᶜ S₂>>T)

  topCompCtx : CompState → Ctx
  topCompCtx (∘⟨_⊰_╎_⟩ {Γ = Γ} _ _ _) = Γ
  topCompCtx (∙⟨_⊰_╎_⟩ {Γ = Γ} _ _ _) = Γ

  topCompEnv : (Q : CompState) → Env (topCompCtx Q)
  topCompEnv (∘⟨_⊰_╎_⟩ _ γ _) = γ
  topCompEnv (∙⟨_⊰_╎_⟩ _ γ _) = γ

  lem0 : (cs : CompStack Δ X) → (MM : K ⟦ X ⟧) → ⟦ cs ⟧ᶜˢ (λ k → MM k) k₀ ≡ MM (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
  lem0 ◻ MM = refl
  lem0 {X = X} ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡}) MM =           ⟦ (W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡} ⟧ᶜˢ MM k₀
                                   ≡⟨ refl ⟩
                                     ⟦ cs ⟧ᶜˢ (λ k → (λ x → MM (λ z → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) x)) k) k₀
                                   ≡⟨ lem0 cs (λ x → MM (λ z → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) x)) ⟩
                                     (λ x → MM (λ z → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) x)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                                   ≡⟨ refl ⟩
                                     MM (λ z →       ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)            )
                                   ≡⟨ cong MM lem0'' ⟩
                                     MM (λ z →       ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) k) k₀                      )
                                   ≡⟨ refl ⟩
                                     MM (λ y → ⟦ (W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡} ⟧ᶜˢ (λ k → k y) k₀) ∎

                                   where
                                      lem0' : (z : ⟦ X ⟧) → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀) ≡ ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) k) k₀
                                      lem0' z = sym (lem0 cs (⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z)))

                                      lem0'' : (λ z → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) ≡ (λ z → ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) k) k₀)
                                      lem0'' = extensionality lem0'


  -----------------------------------------------------

  lstate-eq : {L L' : LookupState X} → L →ᴸ L' → ⟦ L ⟧ᴸ ≡ ⟦ L' ⟧ᴸ
  lstate-eq {L = L} {L' = L'} val-h-step = refl
  lstate-eq {L = L} {L' = L'} val-t-step = refl
  lstate-eq {L = L} {L' = L'} comp-t-step = refl

  lstate-eq* : {L L' : LookupState X} → L →ᴸ* L' → ⟦ L ⟧ᴸ ≡ ⟦ L' ⟧ᴸ
  lstate-eq* {L = L} {L' = L'} (L ◼) = refl
  lstate-eq* {L = L} {L' = L'} (L →ᴸ⟨ L→L' ⟩ L'→L'') =
             let
               IH0 = lstate-eq L→L'
               IH1 = lstate-eq* L'→L''
             in
             trans IH0 IH1

  valstate-eq : {S S' : ValState X} → S →ᵛ S' → ⟦ S ⟧ᵛꟴ ≡ ⟦ S' ⟧ᵛꟴ
  valstate-eq {S = S} {S' = S'} (∘var-c {tail = □} {↥ = 🗆}) = refl
  valstate-eq {S = S} {S' = S'} (∘var-c {tail = (x ⊲ γ ∷ tail) {↥ = ↥}} {↥ = 🗇}) = refl
  valstate-eq {S = S} {S' = S'} (∘var {γ = γ} {γ' = γ'} {i = i} {tail = □} {↥ = 🗆} {M = M} i>>T πᵥ x x₁ ϖ x₃) =
              let
                IH0 = lstate-eq* i>>T
                eq : ⟦ γ' ⟧ᴱ ≡ ⟦ πᵥ ⟧ʷ ⟦ γ ⟧ᴱ
                eq = enveq-eq ϖ
              in
               ⟦ ∘ ((⇡ var i ⊲ γ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ
              ≡⟨ refl ⟩
                 ⟦ i ⟧ᵐ ⟦ γ ⟧ᴱ
              ≡⟨ IH0 ⟩
                 ⟦ toVal M ⟧ᵛ ⟦ γ' ⟧ᴱ
              ≡⟨ cong ⟦ toVal M ⟧ᵛ eq ⟩
               ⟦ toVal M ⟧ᵛ (⟦ πᵥ ⟧ʷ ⟦ γ ⟧ᴱ)
              ≡⟨ cong (λ x → ⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ) (wk-comm {M = M} {π = πᵥ}) ⟩
               ⟦ ∙ ((⭭ wk-v̲a̲l̲ πᵥ M ⊲ γ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ∎
  valstate-eq {S = S} {S' = S'} (∘var {γ = γ} {γ' = γ'} {i = i} {tail = ((M'' ⊲ γ'' ∷ tail) {↥ = ↥})} {↥ = 🗇} {M = M} i>>T πᵥ x x₁ ϖ x₃) =
               ⟦ ∘ ((⇡ var i ⊲ γ ∷ ((M'' ⊲ γ'' ∷ tail) {↥ = ↥})) {↥ = 🗇}) ⟧ᵛꟴ
              ≡⟨ refl ⟩
               ⟦ ∙ ((⭭ wk-v̲a̲l̲ πᵥ M ⊲ γ ∷ ((M'' ⊲ γ'' ∷ tail) {↥ = ↥})) {↥ = 🗇}) ⟧ᵛꟴ ∎

  valstate-eq {S = S} {S' = S'} (∘lam {M = W} {γ = γ} {tail = □} {↥ = 🗆}) = refl
  valstate-eq {S = S} {S' = S'} (∘lam {M = W} {γ = γ} {tail = x ⊲ γ₁ ∷ tail} {↥ = 🗇}) = refl

  valstate-eq {S = S} {S' = S'} (∘pair {tail = □} {↥ = 🗆}) = refl
  valstate-eq {S = S} {S' = S'} (∘pair {tail = x ⊲ γ ∷ tail} {↥ = 🗇}) = refl

  valstate-eq {S = S} {S' = S'} (∘pm {tail = □} {↥ = 🗆}) = refl
  valstate-eq {S = S} {S' = S'} (∘pm {tail = x ⊲ γ ∷ tail} {↥ = 🗇}) = refl

  valstate-eq {S = S} {S' = S'} (∘unit {tail = □} {↥ = 🗆}) = refl
  valstate-eq {S = S} {S' = S'} (∘unit {tail = x ⊲ γ ∷ tail} {↥ = 🗇}) = refl

  valstate-eq {S = S} {S' = S'} (∙M∷l {γ' = γ'} {γ = γ} {M = M} {LHS = LHS} {RHS = RHS} {π' = π'} {tail = □} {↥ = 🗆} π≡ LHS≡M) =
               ⟦ ∙ ((⭭ M ⊲ γ ∷ ((⇡ᴸ LHS RHS ⊲ γ' ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ
              ≡⟨ refl ⟩
               ⟦ LHS ⟧ᵛ ⟦ γ' ⟧ᴱ , ⟦ RHS ⟧ᵛ ⟦ γ' ⟧ᴱ
              ≡⟨ cong₂ (λ x y → x , ⟦ RHS ⟧ᵛ y) LHS≡M π≡ ⟩
               ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ)
              ≡⟨ refl ⟩
               ⟦ ∘ ((⇡ wk-val π' RHS ⊲ γ ∷ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ ∎
  valstate-eq {S = S} {S' = S'} (∙M∷l {tail = x ⊲ γ ∷ tail} {↥ = 🗇} π≡ LHS≡M) = refl

  valstate-eq {S = S} {S' = S'} (∙M∷r {γ' = γ'} {γ = γ} {M = M} {LHS = LHS} {RHS = RHS} {π' = π'} {tail = □} {↥ = 🗆} π≡ RHS≡M) =
               ⟦ ∙ ((⭭ M ⊲ γ ∷ ((⇡ᴿ LHS RHS ⊲ γ' ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ
              ≡⟨ refl ⟩
               ⟦ toVal LHS ⟧ᵛ ⟦ γ' ⟧ᴱ , ⟦ RHS ⟧ᵛ ⟦ γ' ⟧ᴱ
              ≡⟨ cong₂ (λ x y → ⟦ toVal LHS ⟧ᵛ x , y) π≡ RHS≡M ⟩
               ⟦ toVal LHS ⟧ᵛ (⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ
              ≡⟨ cong (λ x → ⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ) (wk-comm {M = LHS} {π = π'}) ⟩
               ⟦ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M ⊲ γ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ∎
  valstate-eq {S = S} {S' = S'} (∙M∷r {tail = x ⊲ γ ∷ tail} {↥ = 🗇} π≡ RHS≡M) = refl

  valstate-eq {S = S} {S' = S'} (∙pair∷pm {γ' = γ'} {γ = γ} {LHS = LHS} {RHS = RHS} {M = M} {N = N} {π' = π'} {tail = □} {↥ = 🗆} π≡ p₁M≡LHS p₂M≡RHS) =
               ⟦ ∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ ∷ ((⇡ᴹ M N ⊲ γ' ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ
              ≡⟨ refl ⟩
               ⟦ N ⟧ᵛ ((⟦ γ' ⟧ᴱ , proj₁ (⟦ M ⟧ᵛ ⟦ γ' ⟧ᴱ)) , proj₂ (⟦ M ⟧ᵛ ⟦ γ' ⟧ᴱ))
              ≡⟨ cong ⟦ N ⟧ᵛ (cong₂ _,_ (cong₂ _,_ π≡ p₁M≡LHS) p₂M≡RHS) ⟩
               ⟦ N ⟧ᵛ ((⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ)
              ≡⟨ refl  ⟩
               ⟦ N ⟧ᵛ ((⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ wk-val (wk-wk wk-id) (toVal RHS) ⟧ᵛ (⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ))
              ≡⟨ cong (λ x → ⟦ N ⟧ᵛ ((⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ x ⟧ᵛ (⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ))) (wk-comm {M = RHS} {π = wk-wk wk-id}) ⟩
               ⟦ N ⟧ᵛ ((⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ))
              ≡⟨ refl ⟩
               ⟦ ∘ ((⇡ wk-val (wk-cong (wk-cong π')) N ⊲ γ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ∎
  valstate-eq {S = S} {S' = S'} (∙pair∷pm {tail = x ⊲ γ ∷ tail} {↥ = 🗇} _ _ _) = refl


  valstate-wk : {S S' : ValState X} → S →ᵛ S' → Wk (topCtx S') (topCtx S)
  valstate-wk ∘var-c = wk-id
  valstate-wk (∘var i>>T πᵥ x x₁ x₂ x₃) = wk-id
  valstate-wk ∘lam = wk-id
  valstate-wk ∘pair = wk-id
  valstate-wk ∘pm = wk-id
  valstate-wk ∘unit = wk-id
  valstate-wk (∙M∷l π≡ LHS≡M) = wk-id
  valstate-wk (∙M∷r π≡ RHS≡M) = wk-id
  valstate-wk (∙pair∷pm {tail = tail} {↥ = ↥} π≡ p₁M≡LHS p₂M≡RHS) = wk-wk (wk-wk wk-id)


  valstate-env-eq : {S S' : ValState X} → (S→S' : S →ᵛ S') → EnvEq (valstate-wk S→S') (topEnv S') (topEnv S)
  valstate-env-eq ∘var-c = enveq-id
  valstate-env-eq (∘var i>>T πᵥ x x₁ x₂ x₃) = enveq-id
  valstate-env-eq ∘lam = enveq-id
  valstate-env-eq ∘pair = enveq-id
  valstate-env-eq ∘pm = enveq-id
  valstate-env-eq ∘unit = enveq-id
  valstate-env-eq (∙M∷l π≡ LHS≡M) = enveq-id
  valstate-env-eq (∙M∷r π≡ RHS≡M) = enveq-id
  valstate-env-eq (∙pair∷pm {Γ = Γ} {X = X} {Y = Y} {Z = Z} {γ' = γ'} {γ = γ} {LHS = LHS} {RHS = RHS} {M = M} {N = N} {π' = π'} {tail = tail} {↥ = ↥} π≡ p₁M≡LHS p₂M≡RHS) =
                  let
                    goal : EnvEq (wk-wk (wk-wk wk-id)) (γ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS) γ
                    goal = wk-env-val-wk (wk-v̲a̲l̲ (wk-wk wk-id) RHS) (wk-env-val-wk LHS enveq-id)
                  in
                  goal

  valstate-wkext : {S S' : ValState X} → (S→S' : S →ᵛ S') → WkExt (valstate-wk S→S')
  valstate-wkext ∘var-c = wk-eq _
  valstate-wkext (∘var i>>T πᵥ x x₁ x₂ x₃) = wk-eq _
  valstate-wkext ∘lam = wk-eq _
  valstate-wkext ∘pair = wk-eq _
  valstate-wkext ∘pm = wk-eq _
  valstate-wkext ∘unit = wk-eq _
  valstate-wkext (∙M∷l π≡ LHS≡M) = wk-eq _
  valstate-wkext (∙M∷r π≡ RHS≡M) = wk-eq _
  valstate-wkext (∙pair∷pm π≡ p₁M≡LHS p₂M≡RHS) = wk-ext (wk-wk wk-id) (wk-ext wk-id (wk-eq wk-id))
