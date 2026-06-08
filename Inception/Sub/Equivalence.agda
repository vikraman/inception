{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Equivalence (R : Set) where

open import Agda.Primitive using (Level)

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Function.Base using (const; _∘_; _$_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; cong-app; icong; dcong₂; sym; trans; subst; subst₂)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.Renaming
open import Inception.Sub.CPS R

open import Data.Unit
open import Data.Nat
open import Data.List using (List; _∷_; []; _++_)

open import Inception.Sub.Equality
open import Inception.Sub.Environments R


module Equivalence {R₀ : Ty} (k₀ : ⟦ R₀ ⟧ → R) where
  open EnvMain {R₀ = R₀} k₀
------------------------------------------------------------------------
-- Equivalence Relation
------------------------------------------------------------------------

  record _≍ᵐ_ {Γ₁ Γ₂ : Ctx} {X : Ty} (i₁ : Γ₁ ∋ X) (i₂ : Γ₂ ∋ X) : Set where
    field
      ctx  : Ctx
      wkn₁ : Wk Γ₁ ctx
      wkn₂ : Wk Γ₂ ctx
      base : ctx ∋ X
      eq₁  : i₁ ≡ wk-mem wkn₁ base
      eq₂  : i₂ ≡ wk-mem wkn₂ base

  record _≍ᵛ_ {Γ₁ Γ₂ : Ctx} {X : Ty} (M₁ : Val Γ₁ X) (M₂ : Val Γ₂ X) : Set where
    field
      ctx  : Ctx
      wkn₁ : Wk Γ₁ ctx
      wkn₂ : Wk Γ₂ ctx
      base : Val ctx X
      eq₁  : M₁ ≡ wk-val wkn₁ base
      eq₂  : M₂ ≡ wk-val wkn₂ base

  record _≍ᵉᵛ_ {Γ₁ Γ₂ : Ctx} {X : Ty} (M₁ : V̲a̲l̲ Γ₁ X) (M₂ : V̲a̲l̲ Γ₂ X) : Set where
    field
      ctx  : Ctx
      wkn₁ : Wk Γ₁ ctx
      wkn₂ : Wk Γ₂ ctx
      base : V̲a̲l̲ ctx X
      eq₁  : M₁ ≡ wk-v̲a̲l̲ wkn₁ base
      eq₂  : M₂ ≡ wk-v̲a̲l̲ wkn₂ base

  record _≍ᶜ_ {Γ₁ Γ₂ : Ctx} {X : Ty} (W₁ : Comp Γ₁ X) (W₂ : Comp Γ₂ X) : Set where
    field
      ctx  : Ctx
      wkn₁ : Wk Γ₁ ctx
      wkn₂ : Wk Γ₂ ctx
      base : Comp ctx X
      eq₁  : W₁ ≡ wk-comp wkn₁ base
      eq₂  : W₂ ≡ wk-comp wkn₂ base

  data _≍ᴱ_ : Env Γ → Env Γ' → Set

  data _≍ᶜˢ_ : {Δ₁ Δ₂ : Ctx} → CompStack Δ₁ X → CompStack Δ₂ X → Set where
    emp : ◻ ≍ᶜˢ ◻
    cat :   {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {W₁ : Comp (Γ₁ ∙ Z) X} {W₂ : Comp (Γ₂ ∙ Z) X} {γ₁ : Env Γ₁} {γ₂ : Env Γ₂} {tail₁ : CompStack Δ₁ X} {tail₂ : CompStack Δ₂ X}
            {π₁ : Wk Γ₁ Δ₁} {π₂ : Wk Γ₂ Δ₂} .{wk≡₁ : ⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡ ⟦ topCsEnv tail₁ ⟧ᴱ} .{wk≡₂ : ⟦ π₂ ⟧ʷ ⟦ γ₂ ⟧ᴱ ≡ ⟦ topCsEnv tail₂ ⟧ᴱ}
          → (W₁ ≍ᶜ W₂) → (γ₁ ≍ᴱ γ₂) → (tail₁ ≍ᶜˢ tail₂) → (((W₁ ⊲ γ₁ ⦂⦂ tail₁) {π = π₁} {wk≡ = wk≡₁}) ≍ᶜˢ ((W₂ ⊲ γ₂ ⦂⦂ tail₂) {π = π₂} {wk≡ = wk≡₂}))

  data _≍ᴱ_ where
    emp  : ∗ ≍ᴱ ∗
    catᵛ :    {Γ₁ Γ₂ : Ctx} {M₁ : V̲a̲l̲ Γ₁ X} {M₂ : V̲a̲l̲ Γ₂ X} {γ₁ : Env Γ₁} {γ₂ : Env Γ₂}
           → (γ₁ ≍ᴱ γ₂) → (M₁ ≍ᵉᵛ M₂)
           → ((γ₁ ﹐ M₁) ≍ᴱ (γ₂ ﹐ M₂))
    catᶜ :    {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {W₁ : Comp Γ₁ X} {W₂ : Comp Γ₂ X} {γ₁ : Env Γ₁} {γ₂ : Env Γ₂} {cs₁ : CompStack Δ₁ X} {cs₂ : CompStack Δ₂ X}
              {π₁ : Wk Γ₁ Δ₁} {π₂ : Wk Γ₂ Δ₂} .{wk≡₁ : ⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡ ⟦ topCsEnv cs₁ ⟧ᴱ} .{wk≡₂ : ⟦ π₂ ⟧ʷ ⟦ γ₂ ⟧ᴱ ≡ ⟦ topCsEnv cs₂ ⟧ᴱ}
           → (W₁ ≍ᶜ W₂) → (γ₁ ≍ᴱ γ₂) → (cs₁ ≍ᶜˢ cs₂)
           → (((γ₁ ﹐﹝ W₁ ╎ cs₁ ﹞) {π = π₁} {wk≡ = wk≡₁}) ≍ᴱ ((γ₂ ﹐﹝ W₂ ╎ cs₂ ﹞) {π = π₂} {wk≡ = wk≡₂}))
