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
