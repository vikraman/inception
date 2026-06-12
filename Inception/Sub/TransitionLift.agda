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


  {-
  lstate-eqv : {S S' : LookupState X} → (S →ᴸ S') → (S ≍ᴸꟴ S')
  lstate-eqv {S = ⟨ h  ∥ γ ﹐ (v̲a̲r̲ {Γ = Γ ∙ X} i) ⟩} {S' = ⟨ i ∥ γ ⟩} val-h-step =
    let
      st = get-lsteps (lookup i γ)
      T = proj₁ st
      S'→T = proj₁ (proj₂ st)
      H = proj₂ (proj₂ st)
      eq = lh-eq H
    in
    record
     { T₁ = T
     ; T₂ = T
     ; path₁ = LookupState.⟨ h ∥ γ Env.﹐ v̲a̲r̲ i ⟩ _→ᴸ*_.→ᴸ⟨ _→ᴸ_.val-h-step ⟩ S'→T
     ; path₂ = S'→T
     ; halt₁ = H
     ; halt₂ = H
     ; eqv = ≣ᴸꟴ-refl T
     }
  lstate-eqv {S = ⟨ t i  ∥ E ﹐ M ⟩} {S' = ⟨ i ∥ γ ⟩} val-t-step =
    let
      st = get-lsteps (lookup i γ)
      T = proj₁ st
      S'→T = proj₁ (proj₂ st)
      H = proj₂ (proj₂ st)
      eq = lh-eq H
    in
    record
     { T₁ = T
     ; T₂ = T
     ; path₁ = LookupState.⟨ t i ∥ E Env.﹐ M ⟩ _→ᴸ*_.→ᴸ⟨ _→ᴸ_.val-t-step ⟩ S'→T
     ; path₂ = S'→T
     ; halt₁ = H
     ; halt₂ = H
     ; eqv = ≣ᴸꟴ-refl T
     }
  lstate-eqv {S = ⟨ t i  ∥ (_﹐﹝_╎_﹞ γ W cs {π = π} {wk≡ = wk≡}) ⟩} {S' = ⟨ i ∥ γ ⟩} comp-t-step =
    let
      st = get-lsteps (lookup i γ)
      T = proj₁ st
      S'→T = proj₁ (proj₂ st)
      H = proj₂ (proj₂ st)
      eq = lh-eq H
    in
    record
     { T₁ = T
     ; T₂ = T
     ; path₁ = LookupState.⟨ t i ∥ γ Env.﹐﹝ W ╎ cs ﹞ ⟩ _→ᴸ*_.→ᴸ⟨ _→ᴸ_.comp-t-step
                ⟩ S'→T
     ; path₂ = S'→T
     ; halt₁ = H
     ; halt₂ = H
     ; eqv = ≣ᴸꟴ-refl T
     }
  -}


  --lstate-eqv :    {S S' : LookupState X} → (S →ᴸ S') → (S ≍ᴸꟴ S')
  --lstate-eqv {S = ⟨ h  ∥ E ﹐ (v̲a̲r̲ {Γ = Γ} i) ⟩} {S' = ⟨ i ∥ E ⟩} val-h-step =
  --  ls-eqv
  --    (record { ctx = Γ ; wkn₁ = wk-wk wk-id ; wkn₂ = wk-id ; base = i ; eq₁ = {!-u!} ; eq₂ = {!!} })
  --    (record { ctx = Γ ; wkn₁ = wk-wk wk-id ; wkn₂ = wk-id ; base = E ; enveq₁ = wk-env-val-wk (v̲a̲r̲ i) enveq-id ; enveq₂ = enveq-id})
  --lstate-eqv {S = ⟨ t i  ∥ E ﹐ M ⟩} {S' = ⟨ i ∥ E ⟩} val-t-step = {!!}
  --lstate-eqv {S = ⟨ t i  ∥ (_﹐﹝_╎_﹞ γ W cs {π = π} {wk≡ = wk≡}) ⟩} {S' = ⟨ i ∥ γ ⟩} comp-t-step = {!!}

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

-------------------------------------

  {-
  wk-lstep : {Δ Γ : Ctx} {X : Ty} {i : Γ ∋ X} {δ : Env Δ} {γ : Env Γ} {π : Wk Δ Γ} {T : LookupState X} {H : LookupHaltingState T}
            → EnvEq π δ γ → ⟨ i ∥ γ ⟩ →ᴸ T
            → Σ[ Ψ ∈ Ctx ] Σ[ i' ∈ Ψ ∋ X ] Σ[ γ' ∈ Env Ψ ] ⟨ wk-mem π i ∥ δ ⟩ →ᴸ* ⟨ i' ∥ γ' ⟩
  wk-lstep {Δ = Δ} {Γ = Γ} {X = X} {i = Cx.h} {δ = δ} {γ = γ ﹐ M} {π = wk-cong π} {T = ⟨ i ∥ γ ⟩} {H = H} (wk-env-val-cong M ϖ) val-h-step = {!!}
    --let
    --  a0 = wk-lstep {π = π} ϖ {!!}
    --in
    --{!!}
  wk-lstep {Δ = Δ} {Γ = Γ} {X = X} {i = Cx.t i} {δ = δ} {γ = γ ﹐ M} {π = wk-cong π} {T = T} {H = H} (wk-env-val-cong M ϖ) L→T = {!!}
  wk-lstep {Δ = Δ} {Γ = Γ} {X = X} {i = i} {δ = δ} {γ = γ} {π = wk-cong π} {T = T} {H = H} (wk-env-comp-cong W cs ϖ) L→T = {!!}
  wk-lstep {Δ = Δ} {Γ = Γ} {X = X} {i = i} {δ = δ} {γ = γ} {π = wk-wk π} {T = T} {H = H} ϖ L→T = {!!}

  mE-to-L :   {Γ₁ Γ₂ : Ctx} {X : Ty} {i₁ : Γ₁ ∋ X} {γ₁ : Env Γ₁} {i₂ : Γ₂ ∋ X} {γ₂ : Env Γ₂}
            → ⟨ i₁ , γ₁ ⟩≍ᵐᴱ⟨ i₂ , γ₂ ⟩ → ⟨ i₁ ∥ γ₁ ⟩ ≍ᴸ ⟨ i₂ ∥ γ₂ ⟩
  mE-to-L record { ctx = Γ ; env = γ ; wkn₁ = π₁ ; wkn₂ = π₂ ; base = i ; eq₁ = ≡₁ ; eq₂ = ≡₂ ; enveq₁ = ϖ₁ ; enveq₂ = ϖ₂ } =
    let
      ls = lookup i γ
      gs = get-lsteps ls
      t = proj₁ gs
      s = proj₁ (proj₂ gs)
      h = proj₂ (proj₂ gs)
    in
    record { T = t ; halt = h ; path₁ = {!!} ; path₂ = {!!} }
  -}

-------------------------------------
  {-
  lstate-≣-to-≍ : {S S' : LookupState X} → (S ≣ᴸꟴ S') → (S ≍ᴸꟴ S')
  lstate-≣-to-≍ {S = ⟨ i₁ ∥ γ₁ ⟩} {S' = ⟨ i₂ ∥ γ₂ ⟩} (ls-eqv record { ctx = Γ ; wkn₁ = π₁ ; wkn₂ = π₂ ; base = i ; eq₁ = eq₁ ; eq₂ = eq₂ } γ₁≍γ₂) = --{!!}
    let
      l₁ = lookup i₁ γ₁
      g₁ = get-lsteps l₁
      s₁ = proj₁ (proj₂ g₁)

      l₂ = lookup i₂ γ₂
      g₂ = get-lsteps l₂
      s₂ = proj₁ (proj₂ g₂)
    in
    {!!}
  -}

-------------------------------------

  ----------------------------------------------------------

  var-c-LHS-eq : {Γ : Ctx} {X Z : Ty} {b : _} {γ : Env Γ} {x : Γ ∋ X} {tail : ValStack b Z}
                 {↥ : BottomTypeEqualsNextType b X Z} {S' : ValState Z}
               → ((∘ ((⇡ (var x) ⊲ γ ∷ tail) {↥ = ↥})) ≍ᵛꟴ S')
               → Σ[ Γ' ∈ Ctx ] Σ[ b' ∈ _ ] Σ[ x' ∈ Γ' ∋ X ] Σ[ γ' ∈ Env Γ' ] Σ[ tail' ∈ ValStack b' Z ]
                 Σ[ ↥' ∈ BottomTypeEqualsNextType b' X Z ]
                 (S' ≡ (∘ ((⇡ (var x') ⊲ γ' ∷ tail') {↥ = ↥'})))
  var-c-LHS-eq {Γ = Γ} {X = X} {Z = Z} {γ = γ} {x = x} {tail = tail} {↥ = ↥} {S' = S'} (∘eqv (cons {Γ₂ = Γ₂} {b₂ = b₂} {γ₂ = γ₂} {tail₂ = tail₂} {↥₂ = ↥₂} (⇡eqv record { ctx = ctx ; wkn₁ = wkn₁ ; wkn₂ = wkn₂ ; base = (var x₁) ; eq₁ = refl ; eq₂ = refl }) x₂ x₃)) = Γ₂ , b₂ , wk-mem wkn₂ x₁ , γ₂ , tail₂ , ↥₂ , refl

  {-
  var-c-RHS-eq : {Γ : Ctx} {Z : Ty} {b : _} {γ : Env Γ} {i : Γ ∋ `V} {tail : ValStack b Z}
                 {↥ : BottomTypeEqualsNextType b `V Z} {S' : ValState Z}
               → ((∙ ((⭭ v̲a̲r̲ i ⊲ γ ∷ tail) {↥ = ↥})) ≍ᵛꟴ S')
               → Σ[ Γ' ∈ Ctx ] Σ[ b' ∈ _ ] Σ[ i' ∈ Γ' ∋ `V ] Σ[ γ' ∈ Env Γ' ] Σ[ tail' ∈ ValStack b' Z ]
                 Σ[ ↥' ∈ BottomTypeEqualsNextType b' `V Z ]
                 (S' ≡ (∙ ((⭭ v̲a̲r̲ i' ⊲ γ' ∷ tail') {↥ = ↥'})))
  var-c-RHS-eq {Γ = Γ} {Z = Z} {γ = γ} {i = i} {tail = tail} {↥ = ↥} {S' = S'} (∙eqv (cons {Γ₂ = Γ₂} {b₂ = b₂} {γ₂ = γ₂} {tail₂ = tail₂} {↥₂ = ↥₂} (⭭eqv record { ctx = ctx ; wkn₁ = wkn₁ ; wkn₂ = wkn₂ ; base = (v̲a̲r̲ i₁) ; eq₁ = refl ; eq₂ = refl }) x₁ x₂)) = Γ₂ , b₂ , wk-mem wkn₂ i₁ , γ₂ , tail₂ , ↥₂ , refl
  -}

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

  {-
  lam-RHS-eq : {Γ : Ctx} {X Y Z : Ty} {b : _} {γ : Env Γ} {M : (Γ ∙ X) ⊢ᶜ Y} {tail : ValStack b Z}
               {↥ : BottomTypeEqualsNextType b (X `⇒ Y) Z} {S' : ValState Z}
             → ((∙ ((⭭ l̲a̲m̲ M ⊲ γ ∷ tail) {↥ = ↥})) ≍ᵛꟴ S')
             → Σ[ Γ' ∈ Ctx ] Σ[ b' ∈ _ ] Σ[ M' ∈ (Γ' ∙ X) ⊢ᶜ Y ] Σ[ γ' ∈ Env Γ' ] Σ[ tail' ∈ ValStack b' Z ]
               Σ[ ↥' ∈ BottomTypeEqualsNextType b' (X `⇒ Y) Z ]
               (S' ≡ (∙ ((⭭ l̲a̲m̲ M' ⊲ γ' ∷ tail') {↥ = ↥'})))
  lam-RHS-eq {Γ = Γ} {X = X} {Y = Y} {Z = Z} {γ = γ} {M = M} {tail = tail} {↥ = ↥} {S' = S'} (∙eqv (cons {Γ₂ = Γ₂} {b₂ = b₂} {γ₂ = γ₂} {tail₂ = tail₂} {↥₂ = ↥₂} (⭭eqv record { ctx = ctx ; wkn₁ = wkn₁ ; wkn₂ = wkn₂ ; base = (l̲a̲m̲ W) ; eq₁ = refl ; eq₂ = refl }) x₁ x₂)) = Γ₂ , b₂ , _ , γ₂ , tail₂ , ↥₂ , refl
  -}

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

  unit-RHS-eq : {Γ : Ctx} {Z : Ty} {b : _} {γ : Env Γ} {tail : ValStack b Z}
                {↥ : BottomTypeEqualsNextType b `Unit Z} {S' : ValState Z}
              → ((∙ ((⭭ u̲n̲i̲t̲ ⊲ γ ∷ tail) {↥ = ↥})) ≍ᵛꟴ S')
              → Σ[ Γ' ∈ Ctx ] Σ[ b' ∈ _ ] Σ[ γ' ∈ Env Γ' ] Σ[ tail' ∈ ValStack b' Z ]
                Σ[ ↥' ∈ BottomTypeEqualsNextType b' `Unit Z ]
                (S' ≡ (∙ ((⭭ u̲n̲i̲t̲ ⊲ γ' ∷ tail') {↥ = ↥'})))
  unit-RHS-eq {Γ = Γ} {Z = Z} {γ = γ} {tail = tail} {↥ = ↥} {S' = S'} (∙eqv (cons {Γ₂ = Γ₂} {b₂ = b₂} {γ₂ = γ₂} {tail₂ = tail₂} {↥₂ = ↥₂} (⭭eqv record { ctx = ctx ; wkn₁ = wkn₁ ; wkn₂ = wkn₂ ; base = u̲n̲i̲t̲ ; eq₁ = refl ; eq₂ = refl }) x₁ x₂)) = Γ₂ , b₂ , γ₂ , tail₂ , ↥₂ , refl

  ----------------------------------------------------------

  {-
  lstate-lift :    {Γ₀ Γ₁ Γ₂ : Ctx} {X : Ty} {i₁ : Γ₁ ∋ X} {γ₀ : Env Γ₀} {γ₁ : Env Γ₁} {i₂ : Γ₂ ∋ X} {γ₂ : Env Γ₂} {M : V̲a̲l̲ Γ₀ X}
                 → (⟨ i₁ , γ₁ ⟩≍ᵐᴱ⟨ i₂ , γ₂ ⟩) → (⟨ i₁ ∥ γ₁ ⟩ →ᴸ* ⟨ h ∥ (γ₀ ﹐ M) ⟩) → LookupHaltingState ⟨ h ∥ (γ₀ ﹐ M) ⟩
                 → Σ[ Γ' ∈ Ctx ]
                   Σ[ γ' ∈ Env Γ' ]
                   Σ[ M' ∈ V̲a̲l̲ Γ' X ]
                   ((⟨ i₂ ∥ γ₂ ⟩ →ᴸ* ⟨ h ∥ (γ' ﹐ M') ⟩) × (M ≍ᵉᵛ M') × LookupHaltingState ⟨ h ∥ (γ' ﹐ M') ⟩)
  lstate-lift {γ₀ = γ₀} {γ₁ = γ₁} {γ₂ = γ₂} {M = M} record { ctx = Γ ; env = γ ; wkn₁ = π₁ ; wkn₂ = π₂ ; base = i ; eq₁ = eq₁ ; eq₂ = eq₂ ; enveq₁ = ϖ₁ ; enveq₂ = ϖ₂ } L→T H =
    let
      a0 = lookup-wk-lift {!!} {!!} {!!} L→T H {!!} γ {!!}
      ls = lift-steps a0
      L→T' : ⟨ wk-mem π₁ i ∥ γ₁ ⟩ →ᴸ* ⟨ h ∥ γ₀ ﹐ M ⟩
      L→T' = subst (λ x → ⟨ x ∥ γ₁ ⟩ →ᴸ* ⟨ h ∥ γ₀ ﹐ M ⟩) eq₁ L→T
    in
    {!!} , {!!} , {!!} , {!!} , {!!} , {!!}
  -}

  ----------------------------------------------------------

  {-
  vstate-lift :  {S T S' : ValState X} → (S ≍ᵛꟴ S') → (S →ᵛ T) → Σ[ T' ∈ ValState X ] ((S' →ᵛ T') × (T ≍ᵛꟴ T'))

  vstate-lift {S = ∘ ((⇡ var i ⊲ γ ∷ tail) {↥ = ↥})} {T = T} {S' = S'} (∘eqv (cons {Γ₂ = Γ₂} {b₂ = b₂} {γ₂ = γ₂} {tail₂ = tail₂} {↥₂ = ↥₂} (⇡eqv record { ctx = ctx ; wkn₁ = wkn₁ ; wkn₂ = wkn₂ ; base = (var x₁) ; eq₁ = refl ; eq₂ = refl }) x₂ x₃)) ∘var-c =
    let
      l = var-c-LHS-eq {↥ = ↥} ((∘eqv (cons {Γ₂ = Γ₂} {b₂ = b₂} {γ₂ = γ₂} {tail₂ = tail₂} {↥₂ = ↥₂} (⇡eqv record { ctx = ctx ; wkn₁ = wkn₁ ; wkn₂ = wkn₂ ; base = (var x₁) ; eq₁ = refl ; eq₂ = refl }) x₂ x₃)))
      t' = ∘var-c {γ = proj₁ (proj₂ (proj₂ (proj₂ l)))} {i = (proj₁ (proj₂ (proj₂ l)))} {tail = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ l))))} {↥ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ l)))))}
      st : S' →ᵛ ∙ ⭭ v̲a̲r̲ (proj₁ (proj₂ (proj₂ l))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ l))) ∷ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ l))))
      st = subst (λ x → x →ᵛ ∙ ((⭭ v̲a̲r̲ (proj₁ (proj₂ (proj₂ l))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ l))) ∷ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ l))))) {↥ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ l)))))})) (sym (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ l))))))) t'
    in
    (∙ (((⭭ v̲a̲r̲ (proj₁ (proj₂ (proj₂ l)))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ l))) ∷ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ l))))) {↥ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ l)))))})) ,
    st ,
    ∙eqv (cons (⭭eqv (record { ctx = ctx ; wkn₁ = wkn₁ ; wkn₂ = wkn₂ ; base = v̲a̲r̲ x₁ ; eq₁ = refl ; eq₂ = refl})) x₂ x₃)

  vstate-lift {S = ∘ ((⇡ var i ⊲ γ ∷ tail) {↥ = ↥})} {T = T} {S' = S'} ((∘eqv (cons {Γ₂ = Γ₂} {b₂ = b₂} {γ₂ = γ₂} {tail₂ = tail₂} {↥₂ = ↥₂} (⇡eqv record { ctx = ctx ; wkn₁ = wkn₁ ; wkn₂ = wkn₂ ; base = (var i') ; eq₁ = refl ; eq₂ = refl }) y₂ y₃))) (∘var {γ = γ} {γ' = γ'} {M = M} i>>T πᵥ envext wkext ϖ H) =
    let
      l = var-LHS-eq {↥ = ↥} ((∘eqv (cons {Γ₂ = Γ₂} {b₂ = b₂} {γ₂ = γ₂} {tail₂ = tail₂} {↥₂ = ↥₂} (⇡eqv record { ctx = ctx ; wkn₁ = wkn₁ ; wkn₂ = wkn₂ ; base = (var i') ; eq₁ = refl ; eq₂ = refl }) y₂ y₃)))

      p :  ⟨ wk-mem wkn₁ i' ∥ γ ⟩ →ᴸ* ⟨ h ∥ γ' ﹐ M ⟩
      p = i>>T

      p' : ⟨ wk-mem wkn₂ i' ∥ γ₂ ⟩ →ᴸ* ⟨ h ∥ {!!} ﹐ {!!} ⟩
      p' = {!!}

      lm : ⟨ wk-mem wkn₁ i' ∥ γ ⟩ ≣ᴸꟴ ⟨ wk-mem wkn₂ i' ∥ γ₂ ⟩
      lm = _≣ᴸꟴ_.ls-eqv
            (record
             { ctx = ctx
             ; wkn₁ = wkn₁
             ; wkn₂ = wkn₂
             ; base = i'
             ; eq₁ = refl
             ; eq₂ = refl
             })
            y₂

      geq : γ ≍ᴱ γ₂
      geq = y₂

      t : (∘ ⇡ var (wk-mem wkn₂ i') ⊲ γ₂ ∷ tail₂) →ᵛ {!!}
      t = ∘var {!!} wkn₂ {!!} {!!} {!!} {!!}

      t' : (∘ ⇡ var (wk-mem wkn₂ i') ⊲ γ₂ ∷ tail₂) →ᵛ {!!}
      t' = {!!}
    in
    {!!} , t' , {!!}

  vstate-lift {S = S} {T = T} {S' = S'} (∘eqv (cons {Γ₂ = Γ₂} {b₂ = b₂} {γ₂ = γ₂} {tail₂ = tail₂} {↥₂ = ↥₂} (⇡eqv record { ctx = ctx ; wkn₁ = wkn₁ ; wkn₂ = wkn₂ ; base = (lam W) ; eq₁ = refl ; eq₂ = refl }) x₂ x₃)) ∘lam = {!!}

  vstate-lift {S = S} {T = T} {S' = S'} (∘eqv (cons {Γ₂ = Γ₂} {b₂ = b₂} {γ₂ = γ₂} {tail₂ = tail₂} {↥₂ = ↥₂} (⇡eqv record { ctx = ctx ; wkn₁ = wkn₁ ; wkn₂ = wkn₂ ; base = (pair M₁ M₂) ; eq₁ = refl ; eq₂ = refl }) x₂ x₃)) ∘pair = {!!}

  vstate-lift {S = S} {T = T} {S' = S'} (∘eqv (cons {Γ₂ = Γ₂} {b₂ = b₂} {γ₂ = γ₂} {tail₂ = tail₂} {↥₂ = ↥₂} (⇡eqv record { ctx = ctx ; wkn₁ = wkn₁ ; wkn₂ = wkn₂ ; base = (pm M N) ; eq₁ = refl ; eq₂ = refl }) x₂ x₃)) ∘pm = {!!}

  vstate-lift {S = S} {T = T} {S' = S'} (∘eqv (cons {Γ₂ = Γ₂} {b₂ = b₂} {γ₂ = γ₂} {tail₂ = tail₂} {↥₂ = ↥₂} (⇡eqv record { ctx = ctx ; wkn₁ = wkn₁ ; wkn₂ = wkn₂ ; base = unit ; eq₁ = refl ; eq₂ = refl }) x₂ x₃)) ∘unit = {!!}

  vstate-lift {S = S} {T = T} {S' = S'} S≍S' (∙M∷l π≡ LHS≡M) = {!!}

  vstate-lift {S = S} {T = T} {S' = S'} S≍S' (∙M∷r π≡ RHS≡M) = {!!}

  vstate-lift {S = S} {T = T} {S' = S'} S≍S' (∙pair∷pm π≡ p₁M≡LHS p₂M≡RHS) = {!!}
  -}


  ----------------------------------------------------------

  {-
  vs-height : ValStack b T◾ → ℕ
  vs-height □ = 0
  vs-height (_ ⊲ _ ∷ tail) = suc (vs-height tail)

  pair-val-eq : {π : Wk Γ Δ} {M : PartialTerm Δ (X `× Y)} {LHS : V̲a̲l̲ Γ X} {RHS : V̲a̲l̲ Γ Y} → (wk-pt π M ≡ ⭭ pa̲i̲r̲ LHS RHS) → Σ[ LHS' ∈ V̲a̲l̲ Δ X ] Σ[ RHS' ∈ V̲a̲l̲ Δ Y ] (⭭ pa̲i̲r̲ LHS' RHS' ≡ M)
  pair-val-eq {π = π} {M = ⭭ pa̲i̲r̲ LHS' RHS'} {LHS = LHS} {RHS = RHS} refl = LHS' , RHS' , refl

  vs-zero-eq : {vs : ValStack empty T◾} → (0 ≡ vs-height vs) → vs ≡ □
  vs-zero-eq {vs = □} _ = refl

  pt-⭭-inj : {M M' : V̲a̲l̲ Γ X} → ⭭ M ≡ ⭭ M' → M ≡ M'
  pt-⭭-inj refl = refl

  uniq-bot : (↥ : BottomTypeEqualsNextType non-empty X T◾) → (↥ ≡ 🗇)
  uniq-bot 🗇 = refl

  data VSWk : ValStack b T◾ → ValStack b T◾ → Set where

    vs-empty : VSWk {T◾ = T◾} □ □

    vs-wk : {M : PartialTerm Γ X} {γ' : Env Γ'} {γ : Env Γ} {tail' tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾}
            → (π : Wk Γ' Γ) → (ϖ : EnvEq π γ' γ) → VSWk tail' tail
            → VSWk ((wk-pt π M ⊲ γ' ∷ tail') {↥ = ↥}) ((M ⊲ γ ∷ tail) {↥ = ↥})

  vs-wk-id : {tail : ValStack b T◾} → VSWk tail tail
  vs-wk-id {tail = □} = vs-empty
  vs-wk-id {tail = M ⊲ γ ∷ tail} =
    let
      a0 = vs-wk {M = M} wk-id enveq-id vs-wk-id
      goal : VSWk (M ⊲ γ ∷ tail) (M ⊲ γ ∷ tail)
      goal = subst (λ x → VSWk (x ⊲ γ ∷ tail) (M ⊲ γ ∷ tail)) (wk-pt-id M) a0
    in
    goal
  -}

  {-
  val-ren-lift-∘∙ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → {ρₗ : Ren Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ
          → (tailₗ : ValStack b T◾)
          --→ (vs-height tail ≡ vs-height tailₗ)
          → (vw : VSWk tailₗ tail)
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ Γ'' ∈ Ctx ]
            Σ[ M'' ∈ PartialTerm Γ'' X' ]
            Σ[ πᵣ ∈ Wk Ψ' Γ'' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tailₗ) {↥ = ↥}) →ᵛ ∙ (((wk-pt πᵣ M'') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
                --× (vs-height tail' ≡ vs-height tailᵣ)
                × (VSWk tailᵣ tail')
                )
  -}


  ----------------------------------------------------------
  -- OLD:
  ----------------------------------------------------------

  -- val-wk-lift : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
  --         → (∘ ((M ⊲ γ ∷ tail) {↥ = ↥})) ↠ᵛ (∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}))
  --         → ⟦ ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
  --         → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
  --         → Σ[ Ψ' ∈ Ctx ]
  --           --
  --           Σ[ Γ'' ∈ Ctx ]
  --           Σ[ M'' ∈ PartialTerm Γ'' X' ]
  --           Σ[ πᵣ ∈ Wk Ψ' Γ'' ]
  --           Σ[ πᵥ ∈ Wk Γ' Γ'' ]
  --           Σ[ γᵣ ∈ Env Ψ' ]
  --           Σ[ tailᵣ ∈ ValStack b' T◾ ]
  --           ( (∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥})) ↠ᵛ (∙ (((wk-pt πᵣ M'') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}))
  --             × ( ⟦ ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ (((wk-pt πᵣ M'') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ
  --               × (wk-pt πᵥ M'' ≡ M') ) )
  -- --val-wk-lift {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} Q→Q' Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = {!!}
  -- val-wk-lift {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (S →ᵛ⟨ ∘var-c ⟩．) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = {!!}
  -- val-wk-lift {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (S →ᵛ⟨ ∘var i>>T πᵥ x x₁ x₂ x₃ ⟩．) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = {!!}
  -- val-wk-lift {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (S →ᵛ⟨ ∘lam ⟩．) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = {!!}
  -- val-wk-lift {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (S →ᵛ⟨ ∘unit ⟩．) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = {!!}
  -- val-wk-lift {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (S →ᵛ⟨ x ⟩ Q→Q') Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = {!!}

  {-
  ----
  postulate
    val-wk-lift-∘∙' : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ
          → (tailₗ : ValStack b T◾)
          --→ (vs-height tail ≡ vs-height tailₗ)
          → (vw : VSWk tailₗ tail)
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ Γ'' ∈ Ctx ]
            Σ[ M'' ∈ PartialTerm Γ'' X' ]
            Σ[ πᵣ ∈ Wk Ψ' Γ'' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tailₗ) {↥ = ↥}) →ᵛ ∙ (((wk-pt πᵣ M'') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
                --× (vs-height tail' ≡ vs-height tailᵣ)
                × (VSWk tailᵣ tail')
                )

  postulate
    val-wk-lift-∘∘' : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ
          → (tailₗ : ValStack b T◾)
          --→ (vs-height tail ≡ vs-height tailₗ)
          → (vw : VSWk tailₗ tail)
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tailₗ) {↥ = ↥}) →ᵛ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              × EnvEq πᵣ γᵣ γ'
              --× (vs-height tail' ≡ vs-height tailᵣ)
              × (VSWk tailᵣ tail')
              )
  ----

  val-wk-lift-∘ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → (∘ ((M ⊲ γ ∷ tail) {↥ = ↥})) ↠ᵛ (∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}))
          → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ
          → (tailₗ : ValStack b T◾)
          --→ (vs-height tail ≡ vs-height tailₗ)
          → (vw : VSWk tailₗ tail)
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ Γ'' ∈ Ctx ]
            Σ[ M'' ∈ PartialTerm Γ'' X' ]
            Σ[ πᵣ ∈ Wk Ψ' Γ'' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( (∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tailₗ) {↥ = ↥})) ↠ᵛ (∙ ((wk-pt πᵣ M'' ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}))
              --× (vs-height tail' ≡ vs-height tailᵣ)
              × (VSWk tailᵣ tail')
              )

  val-wk-lift-∘ {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (S →ᵛ⟨ laststep ⟩．) {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vw =
                let

                  IH = val-wk-lift-∘∙' {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} laststep {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vw
                  Ψ'↑    = proj₁ IH
                  Γ''↑   = proj₁ (proj₂ IH)
                  M''↑   = proj₁ (proj₂ (proj₂ IH))
                  πᵣ↑    = proj₁ (proj₂ (proj₂ (proj₂ IH)))
                  γᵣ↑    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
                  tailᵣ↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
                  S→T↑   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))
                  vs≡↑   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))

                in
                Ψ'↑ , Γ''↑ , M''↑ , πᵣ↑ , γᵣ↑ , tailᵣ↑ , (_ →ᵛ⟨ S→T↑ ⟩．) , vs≡↑
                --Ψ'↑ , Γ''↑ , M''↑ , πᵣ↑ , πᵥ↑ , γᵣ↑ , tailᵣ↑ , (_ →ᵛ⟨ S→T↑ ⟩．) , Q≡Q'↑ , π≡↑ , vs≡↑
  val-wk-lift-∘ {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (_→ᵛ⟨_⟩_ S {S' = ∘ (M₁ ⊲ γ₁ ∷ tail'')} S→S' S'→T) {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vw =
                let

                  IH = val-wk-lift-∘∘' S→S' {πₗ = πₗ} ϖ tailₗ vw
                  Ψ'↑     = proj₁ IH
                  πᵣ↑     = proj₁ (proj₂ IH)
                  γᵣ↑     = proj₁ (proj₂ (proj₂ IH))
                  tailᵣ↑  = proj₁ (proj₂ (proj₂ (proj₂ IH)))
                  S→S'↑   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
                  ϖ↑    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
                  vw↑    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))

                  IH2 = val-wk-lift-∘ S'→T {πₗ = πᵣ↑} {γₗ = γᵣ↑} ϖ↑ tailᵣ↑ vw↑

                  Ψ'↑*     = proj₁ IH2
                  Γ''↑*     = proj₁ (proj₂ IH2)
                  M''*     = proj₁ (proj₂ (proj₂ IH2))
                  πᵣ↑*  = proj₁ (proj₂ (proj₂ (proj₂ IH2)))
                  γᵣ↑*   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH2))))
                  tailᵣ*    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH2)))))
                  S'→T↑*    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH2))))))
                  vw↑*    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH2))))))

                in
                {!!} , {!!} , {!!} , {!!} , {!!} , tailᵣ* , (_ →ᵛ⟨ S→S'↑ ⟩ S'→T↑*) , vw↑*
  val-wk-lift-∘ {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (_→ᵛ⟨_⟩_ S {S' = ∙ x} S→S' S'→T) {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vw = {!!}

{- YYY
  val-wk-lift-∘ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → (∘ ((M ⊲ γ ∷ tail) {↥ = ↥})) ↠ᵛ (∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}))
          --→ (Q≡Q' : ⟦ ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ)
          --→ {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ Γ'' ∈ Ctx ]
            Σ[ M'' ∈ PartialTerm Γ'' X' ]
            Σ[ πᵣ ∈ Wk Ψ' Γ'' ]
            --Σ[ πᵥ ∈ Wk Γ' Γ'' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( (∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥})) ↠ᵛ (∙ ((wk-pt πᵣ M'' ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}))
              -- × ⟦ ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((wk-pt πᵣ M'' ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ
              -- × (wk-pt πᵥ M'' ≡ M')
              × (vs-height tail' ≡ vs-height tailᵣ))
  --val-wk-lift-∘ {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} S→T Q≡Q' VH {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = ?
  --? , ? , ? , ? , ? , ? , ? , ? , ? , ? , ?

  val-wk-lift-∘ {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (S →ᵛ⟨ laststep ⟩．) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                let

                  IH = val-wk-lift-∘∙ {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} laststep {πₗ = πₗ} {γₗ = γₗ} ϖ
                  Ψ'↑    = proj₁ IH
                  Γ''↑   = proj₁ (proj₂ IH)
                  M''↑   = proj₁ (proj₂ (proj₂ IH))
                  πᵣ↑    = proj₁ (proj₂ (proj₂ (proj₂ IH)))
                  γᵣ↑    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
                  tailᵣ↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
                  S→T↑   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))
                  vs≡↑   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))

                in
                Ψ'↑ , Γ''↑ , M''↑ , πᵣ↑ , γᵣ↑ , tailᵣ↑ , (_ →ᵛ⟨ S→T↑ ⟩．) , vs≡↑
                --Ψ'↑ , Γ''↑ , M''↑ , πᵣ↑ , πᵥ↑ , γᵣ↑ , tailᵣ↑ , (_ →ᵛ⟨ S→T↑ ⟩．) , Q≡Q'↑ , π≡↑ , vs≡↑
  val-wk-lift-∘ {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (_→ᵛ⟨_⟩_ S {S' = ∘ (M₁ ⊲ γ₁ ∷ tail'')} S→S' S'→T) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                let

                  IH = val-wk-lift-∘∘ S→S' {πₗ = πₗ} ϖ
                  Ψ'↑     = proj₁ IH
                  πᵣ↑     = proj₁ (proj₂ IH)
                  γᵣ↑     = proj₁ (proj₂ (proj₂ IH))
                  tailᵣ↑  = proj₁ (proj₂ (proj₂ (proj₂ IH)))
                  S→S'↑   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
                  ϖ↑    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
                  vs≡↑    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))

                  -- Ψ'↑    = proj₁ IH
                  -- πᵣ↑   = proj₁ (proj₂ IH)
                  -- γᵣ↑   = proj₁ (proj₂ (proj₂ IH))
                  -- wk≡ᵣ↑    = proj₁ (proj₂ (proj₂ (proj₂ IH)))
                  -- tailᵣ↑    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
                  -- S→S'↑    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
                  -- Q≡Q'↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))
                  -- vs≡↑ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))

                  -- ϖ' = (valstate-env-eq S→S'↑)
                  -- ϖ'' = env-eq-trans {!!} {!!} ϖ' ϖ

                  IH2 = val-wk-lift-∘ S'→T {πₗ = πᵣ↑} {γₗ = γᵣ↑} ϖ↑

                  Ψ'↑*     = proj₁ IH2
                  Γ''↑*     = proj₁ (proj₂ IH2)
                  M''*     = proj₁ (proj₂ (proj₂ IH2))
                  πᵣ↑*  = proj₁ (proj₂ (proj₂ (proj₂ IH2)))
                  γᵣ↑*   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH2))))
                  tailᵣ*    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH2)))))
                  S'→T↑*    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH2))))))
                  vs≡↑*    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH2))))))

                in
                {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , (_ →ᵛ⟨ S→S'↑ ⟩ {!S'→T↑*!}) , {!!}
  val-wk-lift-∘ {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (_→ᵛ⟨_⟩_ S {S' = ∙ x} S→S' S'→T) {πₗ = πₗ} {γₗ = γₗ} ϖ = {!!}
  YYY -}

{-
  val-wk-pair-lift-∘ : {M : PartialTerm Γ Z} {γ : Env Γ} {tail : ValStack b (X' `× Y')} {↥ : BottomTypeEqualsNextType b Z (X' `× Y')} {LHS : V̲a̲l̲ Γ' X'} {RHS : V̲a̲l̲ Γ' Y'} {γ' : Env Γ'} --{tail' : ValStack b' (X' `× Y')} {↥' : BottomTypeEqualsNextType b' (X' `× Y') (X' `× Y')}
          → (∘ ((M ⊲ γ ∷ tail) {↥ = ↥})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ' ∷ □) {↥ = 🗆}))
          → ⟦ ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ' ∷ □) {↥ = 🗆}) ⟧ᵛꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → Σ[ Ψ' ∈ Ctx ]
            --
            Σ[ Γ'' ∈ Ctx ]
            Σ[ LHS' ∈ V̲a̲l̲ Γ'' X' ]
            Σ[ RHS' ∈ V̲a̲l̲ Γ'' Y' ]
            Σ[ πᵣ ∈ Wk Ψ' Γ'' ]
            Σ[ πᵥ ∈ Wk Γ' Γ'' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            --Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( (∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πᵣ LHS') (wk-v̲a̲l̲ πᵣ RHS') ⊲ γᵣ ∷ □) {↥ = 🗆}))
              × ( ⟦ ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πᵣ LHS') (wk-v̲a̲l̲ πᵣ RHS') ⊲ γᵣ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ
                × (pa̲i̲r̲ (wk-v̲a̲l̲ πᵥ LHS') (wk-v̲a̲l̲ πᵥ RHS') ≡ pa̲i̲r̲ LHS RHS) ) )

  val-wk-pair-lift-∘ {Γ = Γ} {b = empty} {Γ' = Γ'} {Ψ = Ψ} {M = ⇡ var i} {γ = γ} {tail = □} {↥ = 🗆} {LHS = LHS} {RHS = RHS} {γ' = γ'} (_→ᵛ⟨_⟩． {T◾ = .(_ `× _)} (∘ ((⇡ var i ⊲ γ ∷ □) {↥ = 🗆})) laststep) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                     let

                       IH = val-wk-lift-∘∙ {M = ⇡ var i} {γ = γ} {tail = □} {↥ = 🗆} {M' = ⭭ pa̲i̲r̲ LHS RHS} {γ' = γ'} {tail' = □} {↥' = 🗆} laststep Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ}

                       t : ∘ wk-pt πₗ (⇡ var i) ⊲ γₗ ∷ □ →ᵛ ∙ wk-pt (proj₁ (proj₂ (proj₂ (proj₂ IH)))) (proj₁ (proj₂ (proj₂ IH))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))
                       t = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))))

                       eq = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))))))
                       eq' = pair-val-eq eq
                       eq₂ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))))))
                       eq₂' = vs-zero-eq eq₂
                       πᵣ↑ = proj₁ (proj₂ (proj₂ (proj₂ IH)))
                       πᵥ↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))

                       Q≡Q'↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))))
                       π≡π'↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))))))

                       t' : ∘ ⇡ var (wk-mem πₗ i) ⊲ γₗ ∷ □ →ᵛ ∙ ⭭ pa̲i̲r̲ (wk-v̲a̲l̲ (proj₁ (proj₂ (proj₂ (proj₂ IH)))) (proj₁ eq')) (wk-v̲a̲l̲ (proj₁ (proj₂ (proj₂ (proj₂ IH)))) (proj₁ (proj₂ eq'))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))
                       t' = subst (λ x → ∘ wk-pt πₗ (⇡ var i) ⊲ γₗ ∷ □ →ᵛ ∙ wk-pt (proj₁ (proj₂ (proj₂ (proj₂ IH)))) x ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))) ) (sym (proj₂ (proj₂ eq'))) t

                       t'' = subst (λ x → ∘ ⇡ var (wk-mem πₗ i) ⊲ γₗ ∷ □ →ᵛ ∙ ⭭ pa̲i̲r̲ (wk-v̲a̲l̲ (proj₁ (proj₂ (proj₂ (proj₂ IH)))) (proj₁ eq')) (wk-v̲a̲l̲ (proj₁ (proj₂ (proj₂ (proj₂ IH)))) (proj₁ (proj₂ eq'))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ x) eq₂' t'

                       Q-eq-goal : ⟦ ∘ ((wk-pt πₗ (⇡ var i) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ≡ ⟦ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πᵣ↑ (proj₁ eq')) (wk-v̲a̲l̲ πᵣ↑ (proj₁ (proj₂ eq'))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ □) {↥ = 🗆}) ⟧ᵛꟴ
                       Q-eq-goal =  ⟦ ∘ ((wk-pt πₗ (⇡ var i) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ
                                   ≡⟨ refl ⟩
                                     ⟦ wk-mem πₗ i ⟧ᵐ ⟦ γₗ ⟧ᴱ
                                   ≡⟨ Q≡Q'↑ ⟩
                                     ⟦ ∙ wk-pt πᵣ↑ (proj₁ (proj₂ (proj₂ IH))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))) ⟧ᵛꟴ
                                   ≡⟨ cong (λ x → ⟦ ∙ wk-pt πᵣ↑ (proj₁ (proj₂ (proj₂ IH))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ x ⟧ᵛꟴ) eq₂' ⟩
                                      ⟦ ∙ wk-pt πᵣ↑ (proj₁ (proj₂ (proj₂ IH))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ □ ⟧ᵛꟴ
                                   ≡⟨ cong (λ x → ⟦ ∙ wk-pt πᵣ↑ x ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ □ ⟧ᵛꟴ) (sym (proj₂ (proj₂ eq'))) ⟩
                                   ⟦ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πᵣ↑ (proj₁ eq')) (wk-v̲a̲l̲ πᵣ↑ (proj₁ (proj₂ eq'))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ∎

                       wk-eq-goal₀ : ⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πᵥ↑ (proj₁ eq')) (wk-v̲a̲l̲ πᵥ↑ (proj₁ (proj₂ eq'))) ≡ ⭭ pa̲i̲r̲ LHS RHS
                       wk-eq-goal₀ =    ⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πᵥ↑ (proj₁ eq')) (wk-v̲a̲l̲ πᵥ↑ (proj₁ (proj₂ eq')))
                                     ≡⟨ refl ⟩
                                        wk-pt πᵥ↑ (⭭ pa̲i̲r̲ (proj₁ eq') (proj₁ (proj₂ eq')))
                                     ≡⟨ cong (wk-pt πᵥ↑) (proj₂ (proj₂ eq')) ⟩
                                        wk-pt πᵥ↑ (proj₁ (proj₂ (proj₂ IH)))
                                     ≡⟨ π≡π'↑  ⟩
                                        ⭭ pa̲i̲r̲ LHS RHS ∎

                       wk-eq-goal : pa̲i̲r̲ (wk-v̲a̲l̲ πᵥ↑ (proj₁ eq')) (wk-v̲a̲l̲ πᵥ↑ (proj₁ (proj₂ eq'))) ≡ pa̲i̲r̲ LHS RHS
                       wk-eq-goal = pt-⭭-inj wk-eq-goal₀
                     in
                     proj₁ IH ,  proj₁ (proj₂ IH) , proj₁ eq' , proj₁ (proj₂ eq') , πᵣ↑ , πᵥ↑ , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) , ( _ →ᵛ⟨ t'' ⟩．) , Q-eq-goal , wk-eq-goal

  val-wk-pair-lift-∘ {Γ = Γ} {b = non-empty} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {LHS = LHS} {RHS = RHS} {γ' = γ'} (_→ᵛ⟨_⟩_ S {S' = ∘ (M₁ ⊲ γ₁ ∷ tail₁)} Q→Q' Q→*Q') Q≡Q' ϖ = --{!!}
                     let
                       IH = val-wk-pair-lift-∘ Q→*Q' {!!} {!!}
                     in
                     {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}
  val-wk-pair-lift-∘ {Γ = Γ} {b = non-empty} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {LHS = LHS} {RHS = RHS} {γ' = γ'} (_→ᵛ⟨_⟩_ S {S' = ∙ x} Q→Q' Q→*Q') Q≡Q' ϖ = {!!}
                     --let
                     --  IH = val-wk-pair-lift-∘ Q→*Q' ? ?
                     --in
                     --{!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}

  val-wk-pair-lift-∘ {Γ = Γ} {b = empty} {Γ' = Γ'} {Ψ = Ψ} {M = ⇡ M} {γ = γ} {tail = □} {↥ = 🗆} {LHS = LHS} {RHS = RHS} {γ' = γ'} (S →ᵛ⟨ Q→Q' ⟩ Q→*Q') Q≡Q' ϖ = {!!}

  -- val-wk-pair-lift-∘ {Γ = Γ} {b = non-empty} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {LHS = LHS} {RHS = RHS} {γ' = γ'} (_→ᵛ⟨_⟩_ S {S' = S'} Q→Q' Q→*Q') Q≡Q' ϖ = {!!}
  -- val-wk-pair-lift-∘ {Γ = Γ} {b = empty} {Γ' = Γ'} {Ψ = Ψ} {M = ⇡ M} {γ = γ} {tail = □} {↥ = 🗆} {LHS = LHS} {RHS = RHS} {γ' = γ'} (S →ᵛ⟨ Q→Q' ⟩ Q→*Q') Q≡Q' ϖ = {!!}

  --val-wk-pair-lift-∘ {Γ = Γ} {b = b} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {LHS = LHS} {RHS = RHS} {γ' = γ'} (S →ᵛ⟨ Q→Q' ⟩ Q→*Q') Q≡Q' ϖ = {!!}
  --                   {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}

  -- x     : (∘ ⇡ wk-val π₁ M ⊲ γ ∷ □) ↠ᵛ
  --         (∙ ⭭ pa̲i̲r̲ LHS RHS ⊲ γ'' ∷ □)
-}

  --------------------------------------------------

  cs-height : CompStack Δ X → ℕ
  cs-height ◻ = 0
  cs-height (x ⊲ γ ⦂⦂ cs) = suc (cs-height cs)

  comp-wk-lift-∘∘ :
          {-
            {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → ⟦ ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          -}
            {W : Γ ⊢ᶜ Z} {γ : Env Γ} {cs : CompStack Δ Z} {π : Wk Γ Δ} {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
            {W' : Γ' ⊢ᶜ Z} {γ' : Env Γ'} {cs' : CompStack Δ' Z} {π' : Wk Γ' Δ'} {wk≡' : ⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs' ⟧ᴱ}
          → (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡})) →ᶜ ((∘⟨ W' ⊰ γ' ╎ cs' ⟩) {π = π'} {wk≡ = wk≡'})
          → ⟦ (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡})) ⟧ᶜꟴ ≡ ⟦ ((∘⟨ W' ⊰ γ' ╎ cs' ⟩) {π = π'} {wk≡ = wk≡'}) ⟧ᶜꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}

          {-
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ Γ'' ∈ Ctx ]
            Σ[ M'' ∈ PartialTerm Γ'' X' ]
            Σ[ πᵣ ∈ Wk Ψ' Γ'' ]
            Σ[ πᵥ ∈ Wk Γ' Γ'' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) →ᵛ ∙ (((wk-pt πᵣ M'') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              × ( ⟦ ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ (((wk-pt πᵣ M'') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ
                × (wk-pt πᵥ M'' ≡ M') ) )
          -}

          → Σ[ Ψ' ∈ Ctx ]
            Σ[ Γ'' ∈ Ctx ]
            Σ[ W'' ∈ Comp Γ'' Z ]
            Σ[ πᵣ ∈ Wk Ψ' Γ'' ]
            Σ[ πᵥ ∈ Wk Γ' Γ'' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            --
            --Σ[ wk≡ᵣ ∈ ⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ ]
            Σ[ Δᵣ ∈ Ctx ]
            Σ[ πₚ ∈ Wk Ψ' Δᵣ ]
            Σ[ csᵣ ∈ CompStack Δᵣ Z ]
            Σ[ wk≡ₚ ∈ ⟦ πₚ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ topCsEnv csᵣ ⟧ᴱ ]
            --{!!}
             ( (((∘⟨ wk-comp πₗ W ⊰ γₗ ╎ cs ⟩) {π = wk-trans πₗ π} {wk≡ = ⟦ wk-trans πₗ π ⟧ʷ ⟦ γₗ ⟧ᴱ ≡⟨ sym (wk-sem-trans πₗ π ⟦ γₗ ⟧ᴱ) ⟩ ⟦ π ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) ≡⟨ cong (⟦ π ⟧ʷ) wk≡ₗ ⟩ ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡⟨ wk≡ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎ })) →ᶜ ((∘⟨ wk-comp πᵣ W'' ⊰ γᵣ ╎ csᵣ ⟩) {π = πₚ} {wk≡ = wk≡ₚ})
               × ⟦ (((∘⟨ wk-comp πₗ W ⊰ γₗ ╎ cs ⟩) {π = wk-trans πₗ π} {wk≡ = ⟦ wk-trans πₗ π ⟧ʷ ⟦ γₗ ⟧ᴱ ≡⟨ sym (wk-sem-trans πₗ π ⟦ γₗ ⟧ᴱ) ⟩ ⟦ π ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) ≡⟨ cong (⟦ π ⟧ʷ) wk≡ₗ ⟩ ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡⟨ wk≡ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎})) ⟧ᶜꟴ ≡ ⟦ ((∘⟨ wk-comp πᵣ W'' ⊰ γᵣ ╎ csᵣ ⟩) {π = πₚ} {wk≡ = wk≡ₚ}) ⟧ᶜꟴ
               × (cs-height csᵣ ≡ cs-height cs') )

  --comp-wk-lift-∘∘ {Γ = Γ} {Z = Z} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {Ψ = Ψ} {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {cs' = cs'} {π' = π'} {wk≡' = wk≡'} W→W' W≡W' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = {!!}
  comp-wk-lift-∘∘ {Γ = Γ} {Z = Z} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {Ψ = Ψ} {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {cs' = cs'} {π' = π'} {wk≡' = wk≡'} (∘push {Γ = Γ} {N = N}) W≡W' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                   wk≡'' = ⟦ wk-trans πₗ π ⟧ʷ ⟦ γₗ ⟧ᴱ
                         ≡⟨ sym (wk-sem-trans πₗ π ⟦ γₗ ⟧ᴱ) ⟩
                           ⟦ π ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                         ≡⟨ cong (⟦ π ⟧ʷ) wk≡ₗ ⟩
                           ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ
                         ≡⟨ wk≡ ⟩
                           ⟦ topCsEnv cs ⟧ᴱ ∎
                 in
                  Ψ , Γ , W' , πₗ , πₜ , γₗ , Ψ , wk-id , (((wk-comp (wk-cong πₗ) N) ⊲ γₗ ⦂⦂ cs) {π = wk-trans πₗ π} {wk≡ = wk≡''}) , refl , (∘push {wk≡ₓ = wk≡''} {wk≡ = wk≡''}) ,
                  ((< idf , ⟦ πₗ ⟧ʷ ； ⟦ W' ⟧ᶜ > ； τ ； (< (λ r → proj₁ r) ； ⟦ πₗ ⟧ʷ , (λ r → proj₂ r) > ； ⟦ N ⟧ᶜ) ♯) ⟦ γₗ ⟧ᴱ ⟦ cs ⟧ᴷ
                 ≡⟨ refl ⟩
                   ⟦ W' ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) (λ z → ⟦ N ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀))
                 ≡⟨ cong (⟦ W' ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)) (extensionality λ x → sym (lem0 cs (⟦ N ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , x)))) ⟩
                   ⟦ W' ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → ⟦ N ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , y) k) k₀)
                 ≡⟨ refl ⟩
                  (⟦ πₗ ⟧ʷ ； ⟦ W' ⟧ᶜ) ⟦ γₗ ⟧ᴱ ⟦ (wk-comp (wk-cong πₗ) N ⊲ γₗ ⦂⦂ cs) {π = wk-trans πₗ π} {wk≡ = wk≡''} ⟧ᴷ ∎) ,
                  refl
                  -- ? , ? , ? , ? , ? , ? , ? , ? , ? , ? , ? , ? , ?
  comp-wk-lift-∘∘ {Γ = Γ} {Z = Z} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {Ψ = Ψ} {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {cs' = cs'} {π' = π'} {wk≡' = wk≡'} (∘sub {N = N}) W≡W' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = -- {!!}
                 let
                   wk≡'' = ⟦ wk-trans πₗ π ⟧ʷ ⟦ γₗ ⟧ᴱ
                         ≡⟨ sym (wk-sem-trans πₗ π ⟦ γₗ ⟧ᴱ) ⟩
                           ⟦ π ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                         ≡⟨ cong (⟦ π ⟧ʷ) wk≡ₗ ⟩
                           ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ
                         ≡⟨ wk≡ ⟩
                           ⟦ topCsEnv cs ⟧ᴱ ∎
                 in
                  Ψ ∙ `V , Γ ∙ `V , W' , wk-cong πₗ , wk-id , ((γₗ ﹐﹝ wk-comp πₗ N ╎ cs ﹞) {π = wk-trans πₗ π} {wk≡ = wk≡''}) , Δ , wk-wk (wk-trans πₗ π) , cs , wk≡'' , (∘sub {wk≡ₓ = wk≡''}) , refl , refl
  comp-wk-lift-∘∘ {Γ = Γ} {Z = Z} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {cs' = cs'} {π' = π'} {wk≡' = wk≡'} (∘pm π₁ x π'') W≡W' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = --{!!}
                  -- Goal: ∘⟨ pm (wk-val πₗ (wk-val π₁ M)) (wk-comp (wk-cong (wk-cong πₗ)) (wk-comp (wk-cong (wk-cong π₁)) W₁)) ⊰ γₗ ╎ cs ⟩ →ᶜ ∘⟨ wk-comp ?3 ?2 ⊰ ?5 ╎ ?8 ⟩
                  {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , ∘pm πₗ {!!} {!!} , {!!} , {!!}
  comp-wk-lift-∘∘ {Γ = Γ} {Z = Z} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {cs' = cs'} {π' = π'} {wk≡' = wk≡'} (∘var x π'' x₁ πᵥ) W≡W' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = {!!}
                  -- ? , ? , ? , ? , ? , ? , ? , ? , ? , ? , ? , ? , ?

  {-
  comp-wk-lift : {W : Γ ⊢ᶜ Z} {γ : Env Γ} {cs : CompStack Δ Z} {π : Wk Γ Δ} {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
          {W' : Γ' ⊢ᶜ Z} {γ' : Env Γ'} {cs' : CompStack Δ' Z} {π' : Wk Γ' Δ'} {wk≡' : ⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs' ⟧ᴱ}
          → (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡})) →ᶜ ((∘⟨ W' ⊰ γ' ╎ cs' ⟩) {π = π'} {wk≡ = wk≡'})
          → ⟦ (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡})) ⟧ᶜꟴ ≡ ⟦ ((∘⟨ W' ⊰ γ' ╎ cs' ⟩) {π = π'} {wk≡ = wk≡'}) ⟧ᶜꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ wk≡ᵣ ∈ ⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ ]
            Σ[ Δᵣ ∈ Ctx ]
            Σ[ πₚ ∈ Wk Ψ' Δᵣ ]
            Σ[ csᵣ ∈ CompStack Δᵣ Z ]
            Σ[ wk≡ₚ ∈ ⟦ πₚ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ topCsEnv csᵣ ⟧ᴱ ]
             ( (((∘⟨ wk-comp πₗ W ⊰ γₗ ╎ cs ⟩) {π = wk-trans πₗ π} {wk≡ = ⟦ wk-trans πₗ π ⟧ʷ ⟦ γₗ ⟧ᴱ ≡⟨ sym (wk-sem-trans πₗ π ⟦ γₗ ⟧ᴱ) ⟩ ⟦ π ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) ≡⟨ cong (⟦ π ⟧ʷ) wk≡ₗ ⟩ ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡⟨ wk≡ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎ })) →ᶜ ((∘⟨ wk-comp πᵣ W' ⊰ γᵣ ╎ csᵣ ⟩) {π = πₚ} {wk≡ = wk≡ₚ})
               × ⟦ (((∘⟨ wk-comp πₗ W ⊰ γₗ ╎ cs ⟩) {π = wk-trans πₗ π} {wk≡ = ⟦ wk-trans πₗ π ⟧ʷ ⟦ γₗ ⟧ᴱ ≡⟨ sym (wk-sem-trans πₗ π ⟦ γₗ ⟧ᴱ) ⟩ ⟦ π ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) ≡⟨ cong (⟦ π ⟧ʷ) wk≡ₗ ⟩ ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡⟨ wk≡ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎})) ⟧ᶜꟴ ≡ ⟦ ((∘⟨ wk-comp πᵣ W' ⊰ γᵣ ╎ csᵣ ⟩) {π = πₚ} {wk≡ = wk≡ₚ}) ⟧ᶜꟴ
               × (height csᵣ ≡ height cs') )

  comp-wk-lift {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {Ψ = Ψ} {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {π' = π'} {wk≡' = wk≡'} (∘push {Γ = Γ} {N = N}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                   wk≡'' = ⟦ wk-trans πₗ π ⟧ʷ ⟦ γₗ ⟧ᴱ
                         ≡⟨ sym (wk-sem-trans πₗ π ⟦ γₗ ⟧ᴱ) ⟩
                           ⟦ π ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                         ≡⟨ cong (⟦ π ⟧ʷ) wk≡ₗ ⟩
                           ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ
                         ≡⟨ wk≡ ⟩
                           ⟦ topCsEnv cs ⟧ᴱ ∎
                 in
                 Ψ , πₗ , γₗ , wk≡ₗ , Ψ , wk-id , (((wk-comp (wk-cong πₗ) N) ⊲ γₗ ⦂⦂ cs) {π = wk-trans πₗ π}
                  {wk≡ = wk≡''}) ,
                 refl , (∘push {wk≡ₓ = wk≡''} {wk≡ = wk≡''} ) ,
                 ((< idf , ⟦ πₗ ⟧ʷ ； ⟦ W' ⟧ᶜ > ； τ ； (< (λ r → proj₁ r) ； ⟦ πₗ ⟧ʷ , (λ r → proj₂ r) > ； ⟦ N ⟧ᶜ) ♯) ⟦ γₗ ⟧ᴱ ⟦ cs ⟧ᴷ
                 ≡⟨ refl ⟩
                   ⟦ W' ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) (λ z → ⟦ N ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀))
                 ≡⟨ cong (⟦ W' ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)) (extensionality λ x → sym (lem0 cs (⟦ N ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , x)))) ⟩
                   ⟦ W' ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → ⟦ N ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , y) k) k₀)
                 ≡⟨ refl ⟩
                  (⟦ πₗ ⟧ʷ ； ⟦ W' ⟧ᶜ) ⟦ γₗ ⟧ᴱ ⟦ (wk-comp (wk-cong πₗ) N ⊲ γₗ ⦂⦂ cs) {π = wk-trans πₗ π} {wk≡ = wk≡''} ⟧ᴷ ∎) ,
                 refl

  comp-wk-lift {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {Ψ = Ψ} {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {π' = π'} {wk≡' = wk≡'} (∘sub {N = N}) Q≡Q' {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                   wk≡'' = ⟦ wk-trans πₗ π ⟧ʷ ⟦ γₗ ⟧ᴱ
                         ≡⟨ sym (wk-sem-trans πₗ π ⟦ γₗ ⟧ᴱ) ⟩
                           ⟦ π ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                         ≡⟨ cong (⟦ π ⟧ʷ) wk≡ₗ ⟩
                           ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ
                         ≡⟨ wk≡ ⟩
                           ⟦ topCsEnv cs ⟧ᴱ ∎
                 in
                 Ψ ∙ `V ,
                 wk-cong πₗ ,
                 ((γₗ ﹐﹝ wk-comp πₗ N ╎ cs ﹞) {π = wk-trans πₗ π} {wk≡ = wk≡''}) ,
                 (⟦ wk-cong πₗ ⟧ʷ ⟦ (γₗ ﹐﹝ wk-comp πₗ N ╎ cs ﹞) {π = wk-trans πₗ π} {wk≡ = wk≡''} ⟧ᴱ
                 ≡⟨ refl ⟩
                   < (λ r → proj₁ r) ； ⟦ πₗ ⟧ʷ , (λ r → proj₂ r) > (⟦ γₗ ⟧ᴱ , (⟦ πₗ ⟧ʷ ； ⟦ N ⟧ᶜ) ⟦ γₗ ⟧ᴱ ⟦ cs ⟧ᴷ)
                 ≡⟨ refl ⟩
                   ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , (⟦ N ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)) ⟦ cs ⟧ᴷ
                 ≡⟨ cong₂ (λ x y → x , (⟦ N ⟧ᶜ y) ⟦ cs ⟧ᴷ ) wk≡ₗ wk≡ₗ ⟩
                   ⟦ γ ⟧ᴱ , ⟦ N ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ
                 ≡⟨ refl ⟩
                  ⟦ (γ ﹐﹝ N ╎ cs ﹞) {π = π} {wk≡ = wk≡} ⟧ᴱ ∎) ,
                 Δ ,
                 wk-wk (wk-trans πₗ π) ,
                 cs ,
                 wk≡'' ,
                 (∘sub {wk≡ₓ = wk≡''}) ,
                 refl ,
                 refl

  comp-wk-lift {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {Ψ = Ψ} {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {π' = π'} {wk≡' = wk≡'} (∘pm π₁ M→M' π'') Q≡Q' {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
               {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}

  comp-wk-lift {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {π' = π'} {wk≡' = wk≡'} (∘var x π'' x₁ πᵥ) Q≡Q' ϖ {wk≡ₗ = wk≡ₗ} =
               {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}
  -}
  -}


  --------------------------------------------------------

  vs-height : ValStack b T◾ → ℕ
  vs-height □ = 0
  vs-height (_ ⊲ _ ∷ tail) = suc (vs-height tail)

  pair-val-eq : {π : Wk Γ Δ} {M : PartialTerm Δ (X `× Y)} {LHS : V̲a̲l̲ Γ X} {RHS : V̲a̲l̲ Γ Y} → (wk-pt π M ≡ ⭭ pa̲i̲r̲ LHS RHS) → Σ[ LHS' ∈ V̲a̲l̲ Δ X ] Σ[ RHS' ∈ V̲a̲l̲ Δ Y ] (⭭ pa̲i̲r̲ LHS' RHS' ≡ M)
  pair-val-eq {π = π} {M = ⭭ pa̲i̲r̲ LHS' RHS'} {LHS = LHS} {RHS = RHS} refl = LHS' , RHS' , refl

  vs-zero-eq : {vs : ValStack empty T◾} → (0 ≡ vs-height vs) → vs ≡ □
  vs-zero-eq {vs = □} _ = refl

  pt-⭭-inj : {M M' : V̲a̲l̲ Γ X} → ⭭ M ≡ ⭭ M' → M ≡ M'
  pt-⭭-inj refl = refl

  uniq-bot : (↥ : BottomTypeEqualsNextType non-empty X T◾) → (↥ ≡ 🗇)
  uniq-bot 🗇 = refl

  record LookupRenLift
    (i   : Γ ∋ X)
    (M   : V̲a̲l̲ Γ' X)
    (γ   : Env Γ)
    (γ'  : Env Γ')
    (ρₗ  : Ren Ψ Γ)
    (Ρₗ  : Injective ρₗ)
    (γₗ  : Env Ψ)
    : Set
    where

    field
      ren-lift-Γ : Ctx

      ren-lift-ρᵣ : Ren ren-lift-Γ Γ'

      ren-lift-γᵣ : Env ren-lift-Γ

      ren-lift-steps :
        ⟨ ρₗ i ∥ γₗ ⟩
        →ᴸ*
        ⟨ h ∥ ren-lift-γᵣ ﹐ ren-v̲a̲l̲ ren-lift-ρᵣ M ⟩

      ren-lift-halt :
        LookupHaltingState
          ⟨ h ∥ ren-lift-γᵣ ﹐ ren-v̲a̲l̲ ren-lift-ρᵣ M ⟩

  open LookupRenLift

  -- ren-nxt : Ren Γ (Γ' ∙ X) → Ren Γ Γ'
  -- ren-nxt ρ Cx.h = ρ (t h)
  -- ren-nxt ρ (Cx.t i) = ρ (t (t i))

  -- -- NOT TRUE
  -- ren-prev : Ren (Γ ∙ X) (Γ' ∙ X) → Ren Γ Γ'
  -- ren-prev {Γ = Cx.ε} {Γ' = Γ' Cx.∙ Y} ρ Cx.h = {!!}
  -- ren-prev {Γ = Γ Cx.∙ x} {Γ' = Γ' Cx.∙ Y} ρ Cx.h = {!!}
  -- ren-prev {Γ = Γ} {Γ' = Γ' ∙ Y} ρ (Cx.t i) = {!!}

  ren-absurd : Ren ε (Γ ∙ X) → ⊥
  ren-absurd ρ with ρ h
  ... | ()

  --lookup-ren-lift : {γ : Env Γ} {γ' : Env Γ'}
  --               → (i : Γ ∋ X) → (M : V̲a̲l̲ Γ' X)
  --               --→ (ext : EnvExt i γ (γ' ﹐ M))
  --               → ⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ γ' ﹐ M ⟩
  --               → (H : LookupHaltingState ⟨ h ∥ γ' ﹐ M ⟩)
  --               → (ρₗ : Ren Ψ Γ)
  --               → (Pₗ : Injective ρₗ)
  --               → (γₗ : Env Ψ)
  --               --→ (ϖₗ : EnvEq πₗ γₗ γ)
  --               → LookupRenLift i M γ γ' ρₗ Pₗ γₗ

  --lookup-ren-lift {Γ = Γ} {Γ' = Γ'} {Ψ = Ψ} {γ = γ} {γ' = γ'} i M L→L' H ρₗ Pₗ γₗ = ?
  --i M L→L' H γ γₗ

