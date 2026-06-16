{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.TransitionLift (R : Set) where

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
open import Inception.Sub.Equivalence R
open import Inception.Sub.Machine R

open import Inception.Sub.Renaming

module LiftMain {R₀ : Ty} (k₀ : ⟦ R₀ ⟧ → R) where

  open MachineMain {R₀ = R₀} k₀
  open StatesMain {R₀ = R₀} k₀
  open EquivMain {R₀ = R₀} k₀
  open EnvMain {R₀ = R₀} k₀

  ----------------------------------------------------------------

  record LookupWkStr
    (i   : Γ ∋ X)
    (M   : V̲a̲l̲ Δ' X)
    --(δ   : Env Δ)
    --(δ'  : Env Δ')
    --(πₗ  : Wk Δ Γ)
    (γ   : Env Γ)
    : Set
    where

    field
      str-ctx : Ctx

      str-wk-r : Wk Δ' str-ctx
      str-wk  : Wk Γ str-ctx

      str-env : Env str-ctx

      -- M = wk-v̲a̲l̲ str-wk-r M'
      str-M :  V̲a̲l̲ str-ctx X
      str-eq : M ≡ wk-v̲a̲l̲ str-wk-r str-M

      str-steps :
        ⟨ i ∥ γ ⟩
        →ᴸ*
        ⟨ h ∥ str-env ﹐ str-M ⟩

      str-halt :
        LookupHaltingState
          ⟨ h ∥ str-env ﹐ str-M ⟩

      str-env-ext :
        EnvExt
          (lookup-index str-steps)
          γ
          (str-env ﹐ str-M)

      str-wk-ext :
        WkExt str-wk

      str-env-eq :
        EnvEq str-wk γ str-env

      str-eval-eq :
        ⟦ ⟨ i ∥ γ ⟩ ⟧ᴸ
        ≡
        ⟦ ⟨ h ∥ str-env ﹐ str-M ⟩ ⟧ᴸ

      str-sem-eq :
        ⟦ str-wk ⟧ʷ ⟦ γ ⟧ᴱ
        ≡
        ⟦ str-env ⟧ᴱ

  open LookupWkStr

  lhaltingstate-str :   {Δ Γ : Ctx} {X : Ty} {δ : Env Δ} {γ : Env Γ} {M : V̲a̲l̲ Γ X}
                      → (π : Wk Δ Γ) → (H : LookupHaltingState ⟨ h ∥ δ ﹐ wk-v̲a̲l̲ π M ⟩)
                      → LookupHaltingState ⟨ h ∥ γ ﹐ M ⟩
  lhaltingstate-str {M = l̲a̲m̲ W} π found-lam = found-lam
  lhaltingstate-str {M = pa̲i̲r̲ M₁ M₂} π found-pair = found-pair
  lhaltingstate-str {M = u̲n̲i̲t̲} π found-unit = found-unit


  lookup-eq-absurd : {i : Γ ∋ X} → h ≡ t i → ⊥
  lookup-eq-absurd ()

  enveq-lem0 : {π : Wk Δ (Γ ∙ X)} {δ : Env Δ} {γ : Env Γ} {M : V̲a̲l̲ Γ X} → (ϖ : EnvEq π δ (γ ﹐ M)) → EnvEq (wk-trans π (wk-wk wk-id)) δ γ
  enveq-lem0 {π = π} {δ = δ ﹐ _} {γ = γ} {M = M} (wk-env-val-cong M ϖ) = wk-env-val-wk (wk-v̲a̲l̲ _ M) (subst (λ x → EnvEq x δ γ) (sym wk-trans-id') ϖ)
  enveq-lem0 {π = wk-wk π} {δ = δ ﹐ _} {γ = γ} {M = M} (wk-env-val-wk M₁ ϖ) = wk-env-val-wk M₁ (enveq-lem0 ϖ)
  enveq-lem0 {π = wk-wk π} {δ = δ ﹐﹝ W ╎ cs ﹞} {γ = γ} {M = M} (wk-env-comp-wk W cs ϖ) = wk-env-comp-wk W cs (enveq-lem0 ϖ)

  enveq-lem1 :   {Γ' : Ctx} {X : Ty} {π : Wk Δ (Γ ∙ `V)} {δ : Env Δ} {γ : Env Γ} {W : Comp Γ X} {cs : CompStack Γ' X} {π' : Wk Γ Γ'} .{wk≡ : ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
               → (ϖ : EnvEq π δ ((γ ﹐﹝ W ╎ cs ﹞) {π = π'} {wk≡ = wk≡}))
               → EnvEq (wk-trans π (wk-wk wk-id)) δ γ
  enveq-lem1 {π = π} {δ = δ ﹐﹝ _ ╎ _ ﹞} {γ = γ} {W = W} (wk-env-comp-cong W cs ϖ) = wk-env-comp-wk (wk-comp _ W) cs (subst (λ x → EnvEq x δ γ) (sym wk-trans-id') ϖ)
  enveq-lem1 {π = wk-wk π} {δ = δ ﹐ _} {γ = γ} {W = W} {wk≡ = wk≡} (wk-env-val-wk M ϖ) = wk-env-val-wk M (enveq-lem1 {wk≡ = wk≡} ϖ)
  enveq-lem1 {π = wk-wk π} {δ = δ ﹐﹝ _ ╎ _ ﹞} {γ = γ} {W = W} {wk≡ = wk≡} (wk-env-comp-wk W₁ cs ϖ) = wk-env-comp-wk W₁ cs (enveq-lem1 {wk≡ = wk≡} ϖ)


  lookup-wk-str :  {δ  : Env Δ} {δ' : Env Δ'}
                 → (j  : Δ ∋ X)
                 → (i  : Γ ∋ X) → (M : V̲a̲l̲ Δ' X)
                 → (πₗ : Wk Δ Γ)
                 → (ext : EnvExt j δ (δ' ﹐ M))
                 → (j≡wki : j ≡ wk-mem πₗ i)
                 → ⟨ j ∥ δ ⟩ →ᴸ* ⟨ h ∥ δ' ﹐ M ⟩
                 → (H  : LookupHaltingState ⟨ h ∥ δ' ﹐ M ⟩)
                 → (γ  : Env Γ)
                 → (ϖₗ : EnvEq πₗ δ γ)
                 → LookupWkStr i M γ

  lookup-wk-str {Δ = Δ} {Δ' = Δ'} {Γ = Γ ∙ X} {δ = δ' ﹐ M} {δ' = δ'} Cx.h Cx.h M (wk-cong πₗ) env-val j≡wki (S ◼) H (γ ﹐ M₁) (wk-env-val-cong M₁ ϖₗ) =
    record
     { str-ctx = Γ
     ; str-wk-r = πₗ
     ; str-wk = wk-wk wk-id
     ; str-env = γ
     ; str-M = M₁
     ; str-eq = refl
     ; str-steps = ⟨ h ∥ γ Env.﹐ M₁ ⟩ ◼
     ; str-halt = lhaltingstate-str πₗ H
     ; str-env-ext = env-val
     ; str-wk-ext = wk-ext wk-id (wk-eq wk-id)
     ; str-env-eq = wk-env-val-wk M₁ enveq-id
     ; str-eval-eq = refl
     ; str-sem-eq = refl
     }

  lookup-wk-str {δ = δ' ﹐ M} {δ' = δ'} h h M (wk-wk πₗ) env-val j≡wki (S ◼) H γ (wk-env-val-wk M₁ ϖₗ) = ql (lookup-eq-absurd j≡wki) (LookupWkStr h M γ)
  lookup-wk-str {δ = δ} {δ' = δ'} h (t i) M (wk-wk πₗ) env-val j≡wki (S ◼) H γ (wk-env-val-wk M₁ ϖₗ) = ql (lookup-eq-absurd j≡wki) (LookupWkStr (t i) M γ)
  lookup-wk-str {Δ = Δ} {Δ' = Δ'} {Γ = Γ ∙ X} {δ = δ} {δ' = δ'} h h M (wk-cong πₗ) env-val j≡wki (S →ᴸ⟨ x ⟩ L→T) H (γ ﹐ M₁) (wk-env-val-cong M₁ ϖₗ) =
    record
     { str-ctx = Γ
     ; str-wk-r = πₗ
     ; str-wk = wk-wk wk-id
     ; str-env = γ
     ; str-M = M₁
     ; str-eq = refl
     ; str-steps = ⟨ h ∥ γ ﹐ M₁ ⟩ ◼
     ; str-halt = lhaltingstate-str πₗ H
     ; str-env-ext = EnvExt.env-val
     ; str-wk-ext = WkExt.wk-ext wk-id (WkExt.wk-eq wk-id)
     ; str-env-eq = EnvEq.wk-env-val-wk M₁ enveq-id
     ; str-eval-eq = refl
     ; str-sem-eq = refl
     }
  lookup-wk-str {δ = δ} {δ' = δ'} h h M (wk-wk πₗ) env-val j≡wki (S →ᴸ⟨ x ⟩ L→T) H γ (wk-env-val-wk M₁ ϖₗ) = ql (lookup-eq-absurd j≡wki) (LookupWkStr h M γ)
  lookup-wk-str {δ = δ} {δ' = δ'} h (t i) M (wk-wk πₗ) env-val j≡wki (S →ᴸ⟨ x ⟩ L→T) H γ (wk-env-val-wk M₁ ϖₗ) = ql (lookup-eq-absurd j≡wki) (LookupWkStr (t i) M γ)

  lookup-wk-str {Δ = Δ Cx.∙ X} {Δ' = Δ'} {Γ = Γ Cx.∙ X} {δ = δ ﹐ _} {δ' = δ'} (Cx.t j) (Cx.t i) M (wk-cong πₗ) (ext-val ext₁) j≡wki (S →ᴸ⟨ val-t-step ⟩ L→T) H (γ ﹐ M₁) (wk-env-val-cong M₁ ϖₗ) =
    let
      IH = lookup-wk-str j i M πₗ ext₁ (t-injective j≡wki) L→T H γ ϖₗ
    in
    record
     { str-ctx = str-ctx IH
     ; str-wk-r = str-wk-r IH
     ; str-wk = wk-wk (str-wk IH)
     ; str-env = str-env IH
     ; str-M = str-M IH
     ; str-eq = str-eq IH
     ; str-steps = ⟨ t i ∥ γ ﹐ M₁ ⟩ →ᴸ⟨ val-t-step ⟩ (str-steps IH)
     ; str-halt = str-halt IH
     ; str-env-ext = ext-val (str-env-ext IH)
     ; str-wk-ext = wk-ext (str-wk IH) (str-wk-ext IH)
     ; str-env-eq = wk-env-val-wk M₁ (str-env-eq IH)
     ; str-eval-eq = str-eval-eq IH
     ; str-sem-eq = str-sem-eq IH
     }

  lookup-wk-str {Δ = Δ Cx.∙ X} {Δ' = Δ'} {Γ = Γ Cx.∙ Y} {δ = δ ﹐ M₁} {δ' = δ'} (Cx.t j) Cx.h M (wk-wk πₗ) (ext-val ext₁) j≡wki (S →ᴸ⟨ val-t-step ⟩ L→T) H γ (wk-env-val-wk M₁ ϖₗ) =
    lookup-wk-str j h M πₗ ext₁ (t-injective j≡wki) L→T H γ ϖₗ
  lookup-wk-str {Δ = Δ Cx.∙ X} {Δ' = Δ'} {Γ = Γ Cx.∙ Y} {δ = δ ﹐ M₁} {δ' = δ'} (Cx.t j) (Cx.t i) M (wk-wk πₗ) (ext-val ext₁) j≡wki (S →ᴸ⟨ val-t-step ⟩ L→T) H (γ ﹐ M₂) (wk-env-val-wk M₁ ϖₗ) =
    lookup-wk-str j (t i) M πₗ ext₁ (t-injective j≡wki) L→T H (γ Env.﹐ M₂) ϖₗ
  lookup-wk-str {Δ = Δ Cx.∙ X} {Δ' = Δ'} {Γ = Γ Cx.∙ Y} {δ = δ ﹐ M₁} {δ' = δ'} (Cx.t j) (Cx.t i) M (wk-wk πₗ) (ext-val ext₁) j≡wki (S →ᴸ⟨ val-t-step ⟩ L→T) H ((γ ﹐﹝ W ╎ cs ﹞) {wk≡ = wk≡}) (wk-env-val-wk M₁ ϖₗ) = lookup-wk-str j (t i) M πₗ ext₁ (t-injective j≡wki) L→T H (γ Env.﹐﹝ W ╎ cs ﹞) ϖₗ
  lookup-wk-str {Δ = Δ} {Δ' = Δ'} {Γ = Γ Cx.∙ X} {δ = δ} {δ' = δ'} (Cx.t j) (Cx.t i) M (wk-cong πₗ) (ext-comp ext₁) j≡wki (S →ᴸ⟨ comp-t-step ⟩ L→T) H (γ ﹐﹝ W ╎ cs ﹞) (wk-env-comp-cong W cs ϖₗ) =
    let
      IH = lookup-wk-str j i M πₗ ext₁ (t-injective j≡wki) L→T H γ ϖₗ
    in
    record
     { str-ctx = str-ctx IH
     ; str-wk-r = str-wk-r IH
     ; str-wk = wk-wk (str-wk IH)
     ; str-env = str-env IH
     ; str-M = str-M IH
     ; str-eq = str-eq IH
     ; str-steps = ⟨ t i ∥ γ Env.﹐﹝ W ╎ cs ﹞ ⟩ →ᴸ⟨ comp-t-step ⟩ (str-steps IH)
     ; str-halt = str-halt IH
     ; str-env-ext = ext-comp (str-env-ext IH)
     ; str-wk-ext = WkExt.wk-ext (str-wk IH) (str-wk-ext IH)
     ; str-env-eq = wk-env-comp-wk W cs (str-env-eq IH)
     ; str-eval-eq = str-eval-eq IH
     ; str-sem-eq = str-sem-eq IH
     }
  lookup-wk-str {Δ = Δ} {Δ' = Δ'} {Γ = Γ Cx.∙ X} {δ = δ} {δ' = δ'} (Cx.t j) Cx.h M (wk-wk πₗ) (ext-comp ext₁) j≡wki (S →ᴸ⟨ comp-t-step ⟩ L→T) H γ (wk-env-comp-wk W cs ϖₗ) =
    lookup-wk-str j h M πₗ ext₁ (t-injective j≡wki) L→T H γ ϖₗ
  lookup-wk-str {Δ = Δ} {Δ' = Δ'} {Γ = Γ Cx.∙ X} {δ = δ} {δ' = δ'} (Cx.t j) (Cx.t i) M (wk-wk πₗ) (ext-comp ext₁) j≡wki (S →ᴸ⟨ comp-t-step ⟩ L→T) H (γ ﹐ M₁) (wk-env-comp-wk W cs ϖₗ) =
    let
      IH = lookup-wk-str j i M (wk-prev {X = X} (wk-wk πₗ)) ext₁ (Eq.trans (t-injective j≡wki) (sym (wk-wk-trans-id πₗ i))) L→T H γ (enveq-lem0 ϖₗ)
    in
    record
     { str-ctx = str-ctx IH
     ; str-wk-r = str-wk-r IH
     ; str-wk = wk-wk (str-wk IH)
     ; str-env = str-env IH
     ; str-M = str-M IH
     ; str-eq = str-eq IH
     ; str-steps = ⟨ t i ∥ γ ﹐ M₁ ⟩ →ᴸ⟨ val-t-step ⟩ (str-steps IH)
     ; str-halt = str-halt IH
     ; str-env-ext = EnvExt.ext-val (str-env-ext IH)
     ; str-wk-ext = WkExt.wk-ext (str-wk IH) (str-wk-ext IH)
     ; str-env-eq = EnvEq.wk-env-val-wk M₁ (str-env-eq IH)
     ; str-eval-eq = str-eval-eq IH
     ; str-sem-eq = str-sem-eq IH
     }
  lookup-wk-str {Δ = Δ} {Δ' = Δ'} {Γ = Γ Cx.∙ X} {δ = δ} {δ' = δ'} (Cx.t j) (Cx.t i) M (wk-wk πₗ) (ext-comp ext₁) j≡wki (S →ᴸ⟨ comp-t-step ⟩ L→T) H ((γ ﹐﹝ W₁ ╎ cs₁ ﹞) {wk≡ = wk≡}) (wk-env-comp-wk W cs ϖₗ) =
    let
      IH = lookup-wk-str j i M (wk-prev {X = X} (wk-wk πₗ)) ext₁ (Eq.trans (t-injective j≡wki) (sym (wk-wk-trans-id πₗ i))) L→T H γ (enveq-lem1 {wk≡ = wk≡} ϖₗ)
    in
    record
     { str-ctx = str-ctx IH
     ; str-wk-r = str-wk-r IH
     ; str-wk = wk-wk (str-wk IH)
     ; str-env = str-env IH
     ; str-M = str-M IH
     ; str-eq = str-eq IH
     ; str-steps = ⟨ t i ∥ γ ﹐﹝ W₁ ╎ cs₁ ﹞ ⟩ →ᴸ⟨ comp-t-step ⟩ (str-steps IH)
     ; str-halt = str-halt IH
     ; str-env-ext = EnvExt.ext-comp (str-env-ext IH)
     ; str-wk-ext = WkExt.wk-ext (str-wk IH) (str-wk-ext IH)
     ; str-env-eq = EnvEq.wk-env-comp-wk W₁ cs₁ (str-env-eq IH)
     ; str-eval-eq = str-eval-eq IH
     ; str-sem-eq = str-sem-eq IH
     }

  ----------------------------------------------------------

  {-
  ltrans-str :   {Δ Δ' Γ : Ctx} {X : Ty} {j : Γ ∋ X} {δ : Env Δ} {j' : Γ ∋ X} {δ' : Env Δ} {i : Γ ∋ X} {γ : Env Γ}
                → (L₁→L₂ : ⟨ j ∥ δ ⟩ →ᴸ* ⟨ j' ∥ δ' ⟩) → ⟨ j , δ ⟩←⟨ i , γ ⟩
                → Σ[ Γ' ∈ Ctx ] Σ[ i' ∈ Γ' ∋ X ] Σ[ γ' ∈ Env Γ' ] ((⟨ i ∥ γ ⟩ →ᴸ ⟨ i' ∥ γ' ⟩) × (⟨ j' , δ' ⟩←⟨ i' , γ' ⟩))
  -}

  {-
  ltrans-lift :   {Γ₁ Γ₁' Γ₂ : Ctx} {X : Ty} {i₁ : Γ₁ ∋ X} {γ₁ : Env Γ₁} {i₁' : Γ₁' ∋ X} {γ₁' : Env Γ₁'} {i₂ : Γ₂ ∋ X} {γ₂ : Env Γ₂}
                → (L₁→L₂ : ⟨ i₁ ∥ γ₁ ⟩ →ᴸ ⟨ i₂ ∥ γ₂ ⟩) → ⟨ i₁ ∥ γ₁ ⟩≍ᴸ⟨ i₁' ∥ γ₁' ⟩
                → Σ[ Γ₂' ∈ Ctx ] Σ[ i₂' ∈ Γ₂' ∋ X ] Σ[ γ₂' ∈ Env Γ₂' ] ((⟨ i₁' ∥ γ₁' ⟩ →ᴸ ⟨ i₂' ∥ γ₂' ⟩) × (⟨ i₂ ∥ γ₂ ⟩≍ᴸ⟨ i₂' ∥ γ₂' ⟩))
  ltrans-lift {Γ₁ = Γ₂ Cx.∙ `V} {Γ₁' = Γ₁'} {Γ₂ = Γ₂} {X = X} {i₁ = Cx.h} {γ₁ = γ₂ ﹐ v̲a̲r̲ i₂} {i₁' = Cx.h} {γ₁' = γ₁' ﹐ M} {i₂ = i₂} {γ₂ = γ₂} val-h-step record { ctx = (Γ Cx.∙ `V) ; env = env ; idx = Cx.h ; eqv = record { ext₁ = record { wkn = (wk-cong wkn) ; enveq = enveq ; eq = refl } ; ext₂ = ext₂ } } = {!enveq!}
  ltrans-lift {Γ₁ = Γ₂ Cx.∙ `V} {Γ₁' = Γ₁'} {Γ₂ = Γ₂} {X = X} {i₁ = Cx.h} {γ₁ = γ₂ ﹐ v̲a̲r̲ i₂} {i₁' = Cx.h} {γ₁' = γ₁' ﹐﹝ W ╎ cs ﹞} {i₂ = i₂} {γ₂ = γ₂} val-h-step record { ctx = (Γ Cx.∙ `V) ; env = env ; idx = Cx.h ; eqv = record { ext₁ = record { wkn = (wk-cong wkn) ; enveq = enveq ; eq = refl } ; ext₂ = ext₂ } } = {!!}
  ltrans-lift {Γ₁ = Γ₂ Cx.∙ `V} {Γ₁' = Γ₁'} {Γ₂ = Γ₂} {X = X} {i₁ = Cx.h} {γ₁ = γ₂ ﹐ v̲a̲r̲ i₂} {i₁' = Cx.h} {γ₁' = γ₁'} {i₂ = i₂} {γ₂ = γ₂} val-h-step record { ctx = ctx ; env = env ; idx = (Cx.t idx) ; eqv = record { ext₁ = record { wkn = wkn ; enveq = enveq ; eq = eq } ; ext₂ = ext₂ } } = {!!}
  --Γ₂ , i₂ , γ₂ , {!-u!} , {!!}
  ltrans-lift {Γ₁ = Γ₂ Cx.∙ `V} {Γ₁' = Γ₁'} {Γ₂ = Γ₂} {X = X} {i₁ = Cx.h} {γ₁ = γ₂ ﹐ v̲a̲r̲ i₂} {i₁' = Cx.t i₁'} {γ₁' = γ₁'} {i₂ = i₂} {γ₂ = γ₂} val-h-step record { ctx = ctx ; env = env ; idx = idx ; eqv = eqv } = {!!}
  ltrans-lift {Γ₁ = Γ₁} {Γ₁' = Γ₁'} {Γ₂ = Γ₂} {X = X} {i₁ = i₁} {γ₁ = γ₁} {i₁' = i₁'} {γ₁' = γ₁'} {i₂ = i₂} {γ₂ = γ₂} val-t-step eqv = {!!}
  ltrans-lift {Γ₁ = Γ₁} {Γ₁' = Γ₁'} {Γ₂ = Γ₂} {X = X} {i₁ = i₁} {γ₁ = γ₁} {i₁' = i₁'} {γ₁' = γ₁'} {i₂ = i₂} {γ₂ = γ₂} comp-t-step eqv = {!!}
  -}

  --ltrans-lift :   {Γ₁ Γ₁' Γ₂ : Ctx} {X : Ty} {i₁ : Γ₁ ∋ X} {γ₁ : Env Γ₁} {i₁' : Γ₁' ∋ X} {γ₁' : Env Γ₁'} {i₂ : Γ₂ ∋ X} {γ₂ : Env Γ₂}
  --              → (L₁→L₂ : ⟨ i₁ ∥ γ₁ ⟩ →ᴸ ⟨ i₂ ∥ γ₂ ⟩) → ⟨ i₁ ∥ γ₁ ⟩≍ᴸ⟨ i₁' ∥ γ₁' ⟩
  --              → Σ[ Γ₂' ∈ Ctx ] Σ[ i₂' ∈ Γ₂' ∋ X ] Σ[ γ₂' ∈ Env Γ₂' ] ((⟨ i₁' ∥ γ₁' ⟩ →ᴸ ⟨ i₂' ∥ γ₂' ⟩) × (⟨ i₂ ∥ γ₂ ⟩≍ᴸ⟨ i₂' ∥ γ₂' ⟩))
  --ltrans-lift {Γ₁ = Γ₁} {Γ₁' = Γ₁'} {Γ₂ = Γ₂} {X = X} {i₁ = i₁} {γ₁ = γ₁} {i₁' = i₁'} {γ₁' = γ₁'} {i₂ = i₂} {γ₂ = γ₂} L₁→L₂ eqv = ?

  --ltrans-lift : {X : Ty} {L₁ L₂ L₁' : LookupState X} → (L₁→L₂ : L₁ →ᴸ L₂) → (L₁' ≍ᴸ L₁) → Σ[ L₂' ∈ LookupState X ] ((L₁' →ᴸ L₂') × (L₂' ≍ᴸ L₂))
  --ltrans-lift {X = X} {L₁ = L₁} {L₂ = L₂} {L₁' = L₁'} L₁→L₂ eqv = {!!}

{-
  ----------------------------------------------------------

  lhwk : (γ' : Env Γ')
          → (M : V̲a̲l̲ Γ' X)
          → (H : LookupHaltingState ⟨ h ∥ γ' ﹐ M ⟩)
          → (Ψ' : Ctx)
          → (πᵣ : Wk Ψ' Γ')
          → (γᵣ : Env Ψ')
          → (LookupHaltingState ⟨ h ∥ γᵣ ﹐ wk-v̲a̲l̲ πᵣ M ⟩)
  lhwk γ' M found-unit Ψ' πᵣ γᵣ = found-unit
  lhwk γ' M found-pair Ψ' πᵣ γᵣ = found-pair
  lhwk γ' M found-lam Ψ' πᵣ γᵣ = found-lam

  record LookupWkLift
    (i   : Γ ∋ X)
    (M   : V̲a̲l̲ Γ' X)
    (γ   : Env Γ)
    (γ'  : Env Γ')
    (πₗ  : Wk Ψ Γ)
    (γₗ  : Env Ψ)
    : Set
    where

    field
      lift-ctx : Ctx

      lift-wk-r : Wk lift-ctx Γ'
      lift-wk  : Wk Ψ lift-ctx

      lift-env : Env lift-ctx

      lift-steps :
        ⟨ wk-mem πₗ i ∥ γₗ ⟩
        →ᴸ*
        ⟨ h ∥ lift-env ﹐ wk-v̲a̲l̲ lift-wk-r M ⟩

      lift-halt :
        LookupHaltingState
          ⟨ h ∥ lift-env ﹐ wk-v̲a̲l̲ lift-wk-r M ⟩

      lift-env-ext :
        EnvExt
          (lookup-index lift-steps)
          γₗ
          (lift-env ﹐ wk-v̲a̲l̲ lift-wk-r M)

      lift-wk-ext :
        WkExt lift-wk

      lift-env-eq :
        EnvEq lift-wk γₗ lift-env

      lift-eval-eq :
        ⟦ ⟨ wk-mem πₗ i ∥ γₗ ⟩ ⟧ᴸ
        ≡
        ⟦ ⟨ h ∥ lift-env ﹐ wk-v̲a̲l̲ lift-wk-r M ⟩ ⟧ᴸ

      lift-sem-eq :
        ⟦ lift-wk ⟧ʷ ⟦ γₗ ⟧ᴱ
        ≡
        ⟦ lift-env ⟧ᴱ

  open LookupWkLift

  lookup-wk-lift : {γ : Env Γ} {γ' : Env Γ'}
                 → (i : Γ ∋ X) → (M : V̲a̲l̲ Γ' X) → (ext : EnvExt i γ (γ' ﹐ M))
                 → ⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ γ' ﹐ M ⟩
                 → (H : LookupHaltingState ⟨ h ∥ γ' ﹐ M ⟩)
                 → (πₗ : Wk Ψ Γ)
                 → (γₗ : Env Ψ)
                 → (ϖₗ : EnvEq πₗ γₗ γ)
                 → LookupWkLift i M γ γ' πₗ γₗ

  lookup-wk-lift {X = X} i M env-val (S ◼) H (wk-cong {Γ = Γₗ} πₗ) (γₗ ﹐ M₁) (wk-env-val-cong M₂ ϖₗ) =
    record
     { lift-ctx = Γₗ
     ; lift-wk-r = πₗ
     ; lift-wk = wk-wk wk-id
     ; lift-env = γₗ
     ; lift-steps = ⟨ wk-mem (wk-cong πₗ) h ∥ γₗ Env.﹐ wk-v̲a̲l̲ πₗ M ⟩ ◼
     ; lift-halt = lhwk _ M H Γₗ πₗ γₗ
     ; lift-env-ext = EnvExt.env-val
     ; lift-wk-ext = WkExt.wk-ext wk-id (WkExt.wk-eq wk-id)
     ; lift-env-eq = EnvEq.wk-env-val-wk (wk-v̲a̲l̲ πₗ M) enveq-id
     ; lift-eval-eq = refl
     ; lift-sem-eq = refl
     }
  lookup-wk-lift {X = X} i M env-val (S ◼) H (wk-cong πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) ()
  lookup-wk-lift {X = X} {γ' = γ'} i M env-val (S ◼) H (wk-wk πₗ) (γₗ ﹐ M₁) (wk-env-val-wk M₂ ϖₗ) =
    let
      t = lookup-wk-lift h M env-val (⟨ h ∥ γ' ﹐ M ⟩ ◼) H πₗ γₗ ϖₗ
    in
    record
     { lift-ctx = lift-ctx t
     ; lift-wk-r = lift-wk-r t
     ; lift-wk = wk-wk (lift-wk t)
     ; lift-env = lift-env t
     ; lift-steps = ⟨ wk-mem (wk-wk πₗ) h ∥ γₗ Env.﹐ M₁ ⟩ →ᴸ⟨ val-t-step ⟩ lift-steps t
     ; lift-halt = lift-halt t
     ; lift-env-ext = EnvExt.ext-val (lift-env-ext t)
     ; lift-wk-ext = WkExt.wk-ext (lift-wk t) (lift-wk-ext t)
     ; lift-env-eq = EnvEq.wk-env-val-wk M₁ (lift-env-eq t)
     ; lift-eval-eq = lift-eval-eq t
     ; lift-sem-eq = lift-sem-eq t
     }
  lookup-wk-lift {X = X} i M env-val (S ◼) H (wk-wk πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) (wk-env-comp-wk W₁ cs₁ ϖₗ) =
    let
      t = lookup-wk-lift h M env-val (_ ◼) H πₗ γₗ ϖₗ
    in
    record
     { lift-ctx = lift-ctx t
     ; lift-wk-r = lift-wk-r t
     ; lift-wk = wk-wk (lift-wk t)
     ; lift-env = lift-env t
     ; lift-steps = ⟨ wk-mem (wk-wk πₗ) h ∥ γₗ Env.﹐﹝ W ╎ cs ﹞ ⟩ →ᴸ⟨ comp-t-step ⟩ lift-steps t
     ; lift-halt = lift-halt t
     ; lift-env-ext = ext-comp (lift-env-ext t)
     ; lift-wk-ext = WkExt.wk-ext (lift-wk t) (lift-wk-ext t)
     ; lift-env-eq = wk-env-comp-wk W cs (lift-env-eq t)
     ; lift-eval-eq = lift-eval-eq t
     ; lift-sem-eq = lift-sem-eq t
     }
  lookup-wk-lift {X = X} i M env-val (⟨ h ∥ _ ⟩ →ᴸ⟨ x ⟩ L→L') H (wk-cong {Γ = Γₗ} πₗ) (γₗ ﹐ M₁) (wk-env-val-cong M₂ ϖₗ) =
    record
     { lift-ctx = Γₗ
     ; lift-wk-r = πₗ
     ; lift-wk = wk-wk wk-id
     ; lift-env = γₗ
     ; lift-steps = ⟨ wk-mem (wk-cong πₗ) h ∥ γₗ Env.﹐ wk-v̲a̲l̲ πₗ M ⟩ ◼
     ; lift-halt = lhwk _ M H Γₗ πₗ γₗ
     ; lift-env-ext = EnvExt.env-val
     ; lift-wk-ext = WkExt.wk-ext wk-id (WkExt.wk-eq wk-id)
     ; lift-env-eq = EnvEq.wk-env-val-wk (wk-v̲a̲l̲ πₗ M) enveq-id
     ; lift-eval-eq = refl
     ; lift-sem-eq = ⟦ wk-wk wk-id ⟧ʷ ⟦ γₗ Env.﹐ wk-v̲a̲l̲ πₗ M ⟧ᴱ ∎
     }
  lookup-wk-lift {X = X} i M env-val (S →ᴸ⟨ x ⟩ L→L') H (wk-cong πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) ()
  lookup-wk-lift {X = X} i M env-val (S →ᴸ⟨ x ⟩ L→L') H (wk-wk πₗ) (γₗ ﹐ M₁) (wk-env-val-wk M₂ ϖₗ) =
    let
      t = lookup-wk-lift h M env-val (_ ◼) H πₗ γₗ ϖₗ
    in
    record
     { lift-ctx = lift-ctx t
     ; lift-wk-r = lift-wk-r t
     ; lift-wk = wk-wk (lift-wk t)
     ; lift-env = lift-env t
     ; lift-steps = ⟨ wk-mem (wk-wk πₗ) h ∥ γₗ Env.﹐ M₁ ⟩ →ᴸ⟨ val-t-step ⟩ lift-steps t
     ; lift-halt = lift-halt t
     ; lift-env-ext = EnvExt.ext-val (lift-env-ext t)
     ; lift-wk-ext = WkExt.wk-ext (lift-wk t) (lift-wk-ext t)
     ; lift-env-eq = EnvEq.wk-env-val-wk M₁ (lift-env-eq t)
     ; lift-eval-eq = lift-eval-eq t
     ; lift-sem-eq = lift-sem-eq t
     }
  lookup-wk-lift {X = X} i M env-val (S →ᴸ⟨ x ⟩ L→L') H (wk-wk πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) (wk-env-comp-wk W₁ cs₁ ϖₗ) =
    let
      t = lookup-wk-lift h M env-val (_ ◼) H πₗ γₗ ϖₗ
    in
    record
     { lift-ctx = lift-ctx t
     ; lift-wk-r = lift-wk-r t
     ; lift-wk = wk-wk (lift-wk t)
     ; lift-env = lift-env t
     ; lift-steps =  ⟨ wk-mem (wk-wk πₗ) h ∥ γₗ Env.﹐﹝ W ╎ cs ﹞ ⟩ →ᴸ⟨ comp-t-step ⟩ lift-steps t
     ; lift-halt = lift-halt t
     ; lift-env-ext = ext-comp (lift-env-ext t)
     ; lift-wk-ext = WkExt.wk-ext (lift-wk t) (lift-wk-ext t)
     ; lift-env-eq = wk-env-comp-wk W cs (lift-env-eq t)
     ; lift-eval-eq = lift-eval-eq t
     ; lift-sem-eq = lift-sem-eq t
     }
  lookup-wk-lift {X = X} i M (ext-val ext) (⟨ t i₁ ∥ _ ⟩ →ᴸ⟨ val-t-step ⟩ L→L') H (wk-cong πₗ) (γₗ ﹐ M₁) (wk-env-val-cong M₂ ϖₗ) =
    let
      t = lookup-wk-lift i₁ M ext L→L' H πₗ γₗ ϖₗ
    in
    record
     { lift-ctx = lift-ctx t
     ; lift-wk-r = lift-wk-r t
     ; lift-wk = wk-wk (lift-wk t)
     ; lift-env = lift-env t
     ; lift-steps = ⟨ wk-mem (wk-cong πₗ) (Inception.Sub.Syntax.t i₁) ∥ γₗ Env.﹐ wk-v̲a̲l̲ πₗ M₂ ⟩ →ᴸ⟨ val-t-step ⟩ lift-steps t
     ; lift-halt = lift-halt t
     ; lift-env-ext = EnvExt.ext-val (lift-env-ext t)
     ; lift-wk-ext = WkExt.wk-ext (lift-wk t) (lift-wk-ext t)
     ; lift-env-eq = EnvEq.wk-env-val-wk (wk-v̲a̲l̲ πₗ M₂) (lift-env-eq t)
     ; lift-eval-eq = lift-eval-eq t
     ; lift-sem-eq = lift-sem-eq t
     }
  lookup-wk-lift {X = X} i M (ext-val ext) (S →ᴸ⟨ x ⟩ L→L') H (wk-cong πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) ()
  lookup-wk-lift {X = X} i M (ext-val ext) (⟨ t i₁ ∥ _ ⟩ →ᴸ⟨ val-t-step ⟩ L→L') H (wk-wk πₗ) (γₗ ﹐ M₁) (wk-env-val-wk M₂ ϖₗ) =
    let
      t = lookup-wk-lift (t i₁) M (ext-val ext) (_ →ᴸ⟨ val-t-step ⟩ L→L') H πₗ γₗ ϖₗ
    in
    record
     { lift-ctx = lift-ctx t
     ; lift-wk-r = lift-wk-r t
     ; lift-wk = wk-wk (lift-wk t)
     ; lift-env = lift-env t
     ; lift-steps = ⟨ wk-mem (wk-wk πₗ) (Inception.Sub.Syntax.t i₁) ∥ γₗ Env.﹐ M₁ ⟩ →ᴸ⟨ val-t-step ⟩ lift-steps t
     ; lift-halt = lift-halt t
     ; lift-env-ext = EnvExt.ext-val (lift-env-ext t)
     ; lift-wk-ext = WkExt.wk-ext (lift-wk t) (lift-wk-ext t)
     ; lift-env-eq = EnvEq.wk-env-val-wk M₁ (lift-env-eq t)
     ; lift-eval-eq = lift-eval-eq t
     ; lift-sem-eq = lift-sem-eq t
     }
  lookup-wk-lift i M (ext-val ext) (⟨ t i₁ ∥ tail ⟩ →ᴸ⟨ val-t-step ⟩ L→L') H (wk-wk πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) (wk-env-comp-wk W₁ cs₁ ϖₗ) =
    let
      t = lookup-wk-lift (t i₁) M (ext-val ext) (_ →ᴸ⟨ val-t-step ⟩ L→L') H πₗ γₗ ϖₗ
    in
    record
     { lift-ctx = lift-ctx t
     ; lift-wk-r = lift-wk-r t
     ; lift-wk = wk-wk (lift-wk t)
     ; lift-env = lift-env t
     ; lift-steps = ⟨ wk-mem (wk-wk πₗ) (Inception.Sub.Syntax.t i₁) ∥ γₗ Env.﹐﹝ W ╎ cs ﹞ ⟩ →ᴸ⟨ comp-t-step ⟩ lift-steps t
     ; lift-halt = lift-halt t
     ; lift-env-ext = ext-comp (lift-env-ext t)
     ; lift-wk-ext = WkExt.wk-ext (lift-wk t) (lift-wk-ext t)
     ; lift-env-eq = wk-env-comp-wk W cs (lift-env-eq t)
     ; lift-eval-eq = lift-eval-eq t
     ; lift-sem-eq = lift-sem-eq t
     }
  lookup-wk-lift {X = X} i M (ext-comp ext) (S →ᴸ⟨ x ⟩ L→L') H (wk-cong πₗ) (γₗ ﹐ M₁) ()
  lookup-wk-lift {X = X} i M (ext-comp ext) (⟨ t i₁ ∥ _ ﹐﹝ W₁ ╎ cs ﹞ ⟩ →ᴸ⟨ comp-t-step ⟩ L→L') H (wk-cong πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) (wk-env-comp-cong W₁ cs₁ ϖₗ) =
    let
      t = lookup-wk-lift i₁ M ext L→L' H πₗ γₗ ϖₗ
    in
    record
     { lift-ctx = lift-ctx t
     ; lift-wk-r = lift-wk-r t
     ; lift-wk = wk-wk (lift-wk t)
     ; lift-env = lift-env t
     ; lift-steps = ⟨ wk-mem (wk-cong πₗ) (Inception.Sub.Syntax.t i₁) ∥ γₗ Env.﹐﹝ wk-comp πₗ W₁ ╎ cs ﹞ ⟩ →ᴸ⟨ comp-t-step ⟩ lift-steps t
     ; lift-halt = lift-halt t
     ; lift-env-ext = ext-comp (lift-env-ext t)
     ; lift-wk-ext = WkExt.wk-ext (lift-wk t) (lift-wk-ext t)
     ; lift-env-eq = wk-env-comp-wk (wk-comp πₗ W₁) cs (lift-env-eq t)
     ; lift-eval-eq = lift-eval-eq t
     ; lift-sem-eq = lift-sem-eq t
     }
  lookup-wk-lift {X = X} i M (ext-comp ext) (⟨ t i₁ ∥ _ ⟩ →ᴸ⟨ comp-t-step ⟩ L→L') H (wk-wk πₗ) (γₗ ﹐ M₁) (wk-env-val-wk M₂ ϖₗ) =
    let
      t = lookup-wk-lift (t i₁) M (ext-comp ext) (⟨ t i₁ ∥ _ ﹐﹝ _ ╎ _ ﹞ ⟩ →ᴸ⟨ comp-t-step ⟩ L→L') H πₗ γₗ ϖₗ
    in
    record
     { lift-ctx = lift-ctx t
     ; lift-wk-r = lift-wk-r t
     ; lift-wk = wk-wk (lift-wk t)
     ; lift-env = lift-env t
     ; lift-steps = ⟨ wk-mem (wk-wk πₗ) (Inception.Sub.Syntax.t i₁) ∥ γₗ Env.﹐ M₁ ⟩ →ᴸ⟨ val-t-step ⟩ lift-steps t
     ; lift-halt = lift-halt t
     ; lift-env-ext = EnvExt.ext-val (lift-env-ext t)
     ; lift-wk-ext = WkExt.wk-ext (lift-wk t) (lift-wk-ext t)
     ; lift-env-eq = EnvEq.wk-env-val-wk M₁ (lift-env-eq t)
     ; lift-eval-eq = lift-eval-eq t
     ; lift-sem-eq = lift-sem-eq t
     }
  lookup-wk-lift {X = X} i M (ext-comp ext) (⟨ t i₁ ∥ _ ﹐﹝ _ ╎ _ ﹞ ⟩ →ᴸ⟨ comp-t-step ⟩ L→L') H (wk-wk πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) (wk-env-comp-wk W₁ cs₁ ϖₗ) =
    let
      t = lookup-wk-lift (t i₁) M (ext-comp ext) (⟨ t i₁ ∥ _ ⟩ →ᴸ⟨ comp-t-step ⟩ L→L') H πₗ γₗ ϖₗ
    in
    record
     { lift-ctx = lift-ctx t
     ; lift-wk-r = lift-wk-r t
     ; lift-wk = wk-wk (lift-wk t)
     ; lift-env = lift-env t
     ; lift-steps = ⟨ wk-mem (wk-wk πₗ) (Inception.Sub.Syntax.t i₁) ∥ γₗ Env.﹐﹝ W ╎ cs ﹞ ⟩ →ᴸ⟨ comp-t-step ⟩ lift-steps t
     ; lift-halt = lift-halt t
     ; lift-env-ext = ext-comp (lift-env-ext t)
     ; lift-wk-ext = WkExt.wk-ext (lift-wk t) (lift-wk-ext t)
     ; lift-env-eq = wk-env-comp-wk W cs (lift-env-eq t)
     ; lift-eval-eq = lift-eval-eq t
     ; lift-sem-eq = lift-sem-eq t
     }
  lookup-wk-lift {X = X} i M (ext-jmp ext) (S ◼) H (wk-cong πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) ()
  lookup-wk-lift {X = X} i M (ext-jmp ext) (S →ᴸ⟨ x ⟩ L→L') H (wk-cong πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) ()

  ----------------------------------------------------------
  {- OLD LEMMAS; must rethink this
  var-c-LHS-eq : {Γ : Ctx} {X Z : Ty} {b : _} {γ : Env Γ} {x : Γ ∋ X} {tail : ValStack b Z}
                 {↥ : BottomTypeEqualsNextType b X Z} {S' : ValState Z}
               → ((∘ ((⇡ (var x) ⊲ γ ∷ tail) {↥ = ↥})) ≍ᵛꟴ S')
               → Σ[ Γ' ∈ Ctx ] Σ[ b' ∈ _ ] Σ[ x' ∈ Γ' ∋ X ] Σ[ γ' ∈ Env Γ' ] Σ[ tail' ∈ ValStack b' Z ]
                 Σ[ ↥' ∈ BottomTypeEqualsNextType b' X Z ]
                 (S' ≡ (∘ ((⇡ (var x') ⊲ γ' ∷ tail') {↥ = ↥'})))
  var-c-LHS-eq {Γ = Γ} {X = X} {Z = Z} {γ = γ} {x = x} {tail = tail} {↥ = ↥} {S' = S'} (∘eqv (cons {Γ₂ = Γ₂} {b₂ = b₂} {γ₂ = γ₂} {tail₂ = tail₂} {↥₂ = ↥₂} (⇡eqv record { ctx = ctx ; wkn₁ = wkn₁ ; wkn₂ = wkn₂ ; base = (var x₁) ; eq₁ = refl ; eq₂ = refl }) x₂ x₃)) = Γ₂ , b₂ , wk-mem wkn₂ x₁ , γ₂ , tail₂ , ↥₂ , refl

  var-LHS-eq : {Γ : Ctx} {X Z : Ty} {b : _} {γ : Env Γ} {i : Γ ∋ X} {tail : ValStack b Z}
               {↥ : BottomTypeEqualsNextType b X Z} {S' : ValState Z}
             → ((∘ ((⇡ var i ⊲ γ ∷ tail) {↥ = ↥})) ≍ᵛꟴ S')
             → Σ[ Γ' ∈ Ctx ] Σ[ b' ∈ _ ] Σ[ i' ∈ Γ' ∋ X ] Σ[ γ' ∈ Env Γ' ] Σ[ tail' ∈ ValStack b' Z ]
               Σ[ ↥' ∈ BottomTypeEqualsNextType b' X Z ]
               (S' ≡ (∘ ((⇡ var i' ⊲ γ' ∷ tail') {↥ = ↥'})))
  var-LHS-eq {Γ = Γ} {X = X} {Z = Z} {γ = γ} {i = i} {tail = tail} {↥ = ↥} {S' = S'} (∘eqv (cons {Γ₂ = Γ₂} {b₂ = b₂} {γ₂ = γ₂} {tail₂ = tail₂} {↥₂ = ↥₂} (⇡eqv record { ctx = ctx ; wkn₁ = wkn₁ ; wkn₂ = wkn₂ ; base = (var j) ; eq₁ = refl ; eq₂ = refl }) x₁ x₂)) = Γ₂ , b₂ , wk-mem wkn₂ j , γ₂ , tail₂ , ↥₂ , refl

  lam-LHS-eq : {Γ : Ctx} {X Y Z : Ty} {b : _} {γ : Env Γ} {M : (Γ ∙ X) ⊢ᶜ Y} {tail : ValStack b Z}
               {↥ : BottomTypeEqualsNextType b (X `⇒ Y) Z} {S' : ValState Z}
             → ((∘ ((⇡ lam M ⊲ γ ∷ tail) {↥ = ↥})) ≍ᵛꟴ S')
             → Σ[ Γ' ∈ Ctx ] Σ[ b' ∈ _ ] Σ[ M' ∈ (Γ' ∙ X) ⊢ᶜ Y ] Σ[ γ' ∈ Env Γ' ] Σ[ tail' ∈ ValStack b' Z ]
               Σ[ ↥' ∈ BottomTypeEqualsNextType b' (X `⇒ Y) Z ]
               (S' ≡ (∘ ((⇡ lam M' ⊲ γ' ∷ tail') {↥ = ↥'})))
  lam-LHS-eq {Γ = Γ} {X = X} {Y = Y} {Z = Z} {γ = γ} {M = M} {tail = tail} {↥ = ↥} {S' = S'} (∘eqv (cons {Γ₂ = Γ₂} {b₂ = b₂} {γ₂ = γ₂} {tail₂ = tail₂} {↥₂ = ↥₂} (⇡eqv record { ctx = ctx ; wkn₁ = wkn₁ ; wkn₂ = wkn₂ ; base = (lam W) ; eq₁ = refl ; eq₂ = refl }) x₁ x₂)) = Γ₂ , b₂ , _ , γ₂ , tail₂ , ↥₂ , refl

  pair-LHS-eq : {Γ : Ctx} {X Y Z : Ty} {b : _} {γ : Env Γ} {LHS : Val Γ X} {RHS : Val Γ Y} {tail : ValStack b Z}
                {↥ : BottomTypeEqualsNextType b (X `× Y) Z} {S' : ValState Z}
              → ((∘ ((⇡ pair LHS RHS ⊲ γ ∷ tail) {↥ = ↥})) ≍ᵛꟴ S')
              → Σ[ Γ' ∈ Ctx ] Σ[ b' ∈ _ ] Σ[ LHS' ∈ Val Γ' X ] Σ[ RHS' ∈ Val Γ' Y ] Σ[ γ' ∈ Env Γ' ] Σ[ tail' ∈ ValStack b' Z ]
                Σ[ ↥' ∈ BottomTypeEqualsNextType b' (X `× Y) Z ]
                (S' ≡ (∘ ((⇡ pair LHS' RHS' ⊲ γ' ∷ tail') {↥ = ↥'})))
  pair-LHS-eq {Γ = Γ} {X = X} {Y = Y} {Z = Z} {γ = γ} {LHS = LHS} {RHS = RHS} {tail = tail} {↥ = ↥} {S' = S'} (∘eqv (cons {Γ₂ = Γ₂} {b₂ = b₂} {γ₂ = γ₂} {tail₂ = tail₂} {↥₂ = ↥₂} (⇡eqv record { ctx = ctx ; wkn₁ = wkn₁ ; wkn₂ = wkn₂ ; base = pair A B ; eq₁ = refl ; eq₂ = refl }) x₂ x₃)) = Γ₂ , b₂ , _ , _ , γ₂ , tail₂ , ↥₂ , refl

  unit-LHS-eq : {Γ : Ctx} {Z : Ty} {b : _} {γ : Env Γ} {tail : ValStack b Z}
                {↥ : BottomTypeEqualsNextType b `Unit Z} {S' : ValState Z}
              → ((∘ ((⇡ unit ⊲ γ ∷ tail) {↥ = ↥})) ≍ᵛꟴ S')
              → Σ[ Γ' ∈ Ctx ] Σ[ b' ∈ _ ] Σ[ γ' ∈ Env Γ' ] Σ[ tail' ∈ ValStack b' Z ]
                Σ[ ↥' ∈ BottomTypeEqualsNextType b' `Unit Z ]
                (S' ≡ (∘ ((⇡ unit ⊲ γ' ∷ tail') {↥ = ↥'})))
  unit-LHS-eq {Γ = Γ} {Z = Z} {γ = γ} {tail = tail} {↥ = ↥} {S' = S'} (∘eqv (cons {Γ₂ = Γ₂} {b₂ = b₂} {γ₂ = γ₂} {tail₂ = tail₂} {↥₂ = ↥₂} (⇡eqv record { ctx = ctx ; wkn₁ = wkn₁ ; wkn₂ = wkn₂ ; base = unit ; eq₁ = refl ; eq₂ = refl }) x₁ x₂)) = Γ₂ , b₂ , γ₂ , tail₂ , ↥₂ , refl
  -}

-}
