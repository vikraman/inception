{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Traverse (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
-- open import Data.Sum using (_⊎_; inj₁; inj₂)
-- open import Function.Base using (_∘_; _$_)
-- 
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)
open Eq.≡-Reasoning using (step-≡-⟩; step-≡-∣; step-≡-⟨; _∎; step-≡)
-- 
-- open import Relation.Binary.PropositionalEquality.Properties using (dcong₂)
-- open import Agda.Primitive using (Level)
-- 
-- open import Relation.Binary.Reasoning.Syntax
-- 
-- open import Relation.Binary.Definitions
--   using (Symmetric; Transitive; Substitutive; Irreflexive
--         ; _Respects_; _Respectsˡ_; _Respectsʳ_; _Respects₂_)
-- 
open import Inception.Sub.Syntax
open import Inception.Sub.CPS R
-- 
-- open import Data.Unit
-- open import Data.Nat
-- open import Data.List using (List; _∷_; []; _++_)
-- open import Data.List.NonEmpty.Base using (List⁺; _∷_; toList)
-- 
open import Inception.Sub.Equality
open import Inception.Sub.Environments R
--open import Inception.Sub.States R
--open import Inception.Sub.Machine R
--
--open import Inception.Sub.Arithmetic

module EvalMain {R₀ : Ty} (k₀ : ⟦ R₀ ⟧ → R) where

--  open StatesMain {R₀ = R₀} k₀
--  open MachineMain {R₀ = R₀} k₀
  open EnvMain {R₀ = R₀} k₀

  data MEnv : Ctx → Set where

    ∗     :  MEnv ε

    _﹐_   :  MEnv Γ → (M : V̲a̲l̲ Γ X) → MEnv (Γ ∙ X)

    _﹐j   :  (γ : MEnv Γ) → MEnv (Γ ∙ `V)

  {-
  data MTree : Comp Γ X → Set where

    halt  : MEnv Γ → (W : Val Γ R₀) → MTree (return W)

    jump  : MEnv Γ → (i : Γ ∋ `V) → MTree (var {A = A} (var i))

    split : MEnv Γ → (W₁ : Comp (Γ ∙ `V) X) → (W₂ : Comp Γ X) → MTree (sub W₁ W₂)
  -}

  data MEnvEq : (π : Wk Γ' Γ) → (γ' : MEnv Γ') → (γ : MEnv Γ) → Set where

    wk-menv-ε    : MEnvEq wk-ε ∗ ∗

    wk-menv-val-cong : {π : Wk Γ' Γ} {γ' : MEnv Γ'} {γ : MEnv Γ} → (M : V̲a̲l̲ Γ X) → MEnvEq π γ' γ → MEnvEq (wk-cong π) (γ' ﹐ wk-v̲a̲l̲ π M) (γ ﹐ M)

    wk-menv-comp-cong : {π : Wk Γ' Γ} {γ' : MEnv Γ'} {γ : MEnv Γ} → MEnvEq π γ' γ → MEnvEq (wk-cong π) (γ' ﹐j) (γ ﹐j)

    wk-menv-val-wk : {π : Wk Γ' Γ} {γ' : MEnv Γ'} {γ : MEnv Γ} → (M : V̲a̲l̲ Γ' X) → MEnvEq π γ' γ → MEnvEq (wk-wk π) (γ' ﹐ M) γ

    wk-menv-comp-wk : {π : Wk Γ' Γ} {γ' : MEnv Γ'} {γ : MEnv Γ} → MEnvEq π γ' γ → MEnvEq (wk-wk π) (γ' ﹐j) γ

  data MTree : MEnv Γ → Set where

    leaf  : (γ : MEnv Γ) → MTree γ

    node : (γ : MEnv Γ) → (γ₁ : MEnv Γ₁) → (γ₂ : MEnv Γ₂) → {π₁ : Wk Γ₁ Γ} → {π₂ : Wk Γ₂ Γ} → MEnvEq π₁ γ₁ γ → MEnvEq π₂ γ₂ γ → MTree γ₁ → MTree γ₂ → MTree γ

  record Traversal (Γ : Ctx) (X : Ty) : Set where
    field
      Γₘₐₓ : Ctx
      γₘₐₓ : MEnv Γₘₐₓ
      πₘₐₓ : Wk Γₘₐₓ Γ
      tree : MTree γₘₐₓ
      result : V̲a̲l̲ Γₘₐₓ X

  p₁ : V̲a̲l̲ Γ (X `× Y) →  V̲a̲l̲ Γ X
  p₁ (pa̲i̲r̲ W₁ W₂) = W₁

  p₂ : V̲a̲l̲ Γ (X `× Y) →  V̲a̲l̲ Γ Y
  p₂ (pa̲i̲r̲ W₁ W₂) = W₂

  c₁ :  V̲a̲l̲ Γ (X `⇒ Y) →  Comp (Γ ∙ X) Y
  c₁ (l̲a̲m̲ M) = M

  data Arg : Ctx → Ty → Set where
    empty : Arg Γ X
    arg   : V̲a̲l̲ Γ X → Arg Γ (X `⇒ Y)

  result-type : Arg Γ X → Ty
  result-type {X = X} empty = X
  result-type {X = X `⇒ Y} (arg W) = Y

  open Traversal

{- XXX
  mutual

  {-
    traverseᶜ : Comp Γ X → Env Γ → Σ[ Γ' ∈ Ctx ] Env Γ'
    traverseᶜ (return W) γ = traverseᵛ W γ
    traverseᶜ (pm W M) γ = {!traverseᶜ M (proj₂ (traverseᵛ W γ))!}
    traverseᶜ (push M₁ M₂) γ = {!!}
    traverseᶜ (app W₁ W₂) γ = {!!}
    traverseᶜ (var W) γ = {!!}
    traverseᶜ (sub M₁ M₂) γ = {!!}

    traverseᵛ : Val Γ X → Env Γ → Σ[ Γ' ∈ Ctx ] Env Γ'
    traverseᵛ (var i) γ = {!!}
    traverseᵛ (lam M) γ = {!!}
    traverseᵛ (pair W₁ W₂) γ = {!!}
    traverseᵛ (pm W₁ W₂) γ = {!!}
    traverseᵛ unit γ = {!!}
  -}

    traverseᶜ : (X : Ty) → Comp Γ' X → Wk Γ Γ' → (γ : MEnv Γ) → Traversal Γ X
    traverseᶜ X (return W) π γ =
      let
        IH = traverseᵛ empty {!!} {!!} W π γ
      in
      record { Γₘₐₓ = Γₘₐₓ IH ; γₘₐₓ = γₘₐₓ IH ; πₘₐₓ = πₘₐₓ IH ; tree = tree IH ; result = result IH}
    traverseᶜ X (pm W M) π γ =
      let
        IH = traverseᵛ empty {!!} {!!} W π γ
        IH' = traverseᶜ X M (wk-cong (wk-cong (wk-trans (πₘₐₓ IH) π))) (γₘₐₓ IH ﹐ p₁ (result IH) ﹐ wk-v̲a̲l̲ (wk-wk wk-id) (p₂ (result IH)))
      in
      record { Γₘₐₓ = Γₘₐₓ IH' ; γₘₐₓ = γₘₐₓ IH' ; πₘₐₓ = wk-trans (πₘₐₓ IH') (wk-wk (wk-wk (πₘₐₓ IH))) ; tree = tree IH' ; result = result IH' }
    traverseᶜ X (push M₁ M₂) π γ =
      let
        IH₁ = traverseᶜ _ M₁ π γ
        IH' = traverseᶜ X M₂ (wk-cong (wk-trans (πₘₐₓ IH₁) π)) (γₘₐₓ IH₁ ﹐ result IH₁)
      in
      record { Γₘₐₓ = Γₘₐₓ IH' ; γₘₐₓ = γₘₐₓ IH' ; πₘₐₓ = wk-trans (πₘₐₓ IH') (wk-wk (πₘₐₓ IH₁)) ; tree = tree IH' ; result = result IH' }
    traverseᶜ X (app W₁ W₂) π γ =
      let
        IH₂ = traverseᵛ empty {!!} {!!} W₂ π γ
        IH₁ = traverseᵛ (arg (result IH₂)) {!!} {!!} W₁ (wk-trans (πₘₐₓ IH₂) π) (γₘₐₓ IH₂)
      in
      record { Γₘₐₓ = Γₘₐₓ IH₁ ; γₘₐₓ = γₘₐₓ IH₁ ; πₘₐₓ = wk-trans (πₘₐₓ IH₁) (πₘₐₓ IH₂) ; tree = tree IH₁ ; result = result IH₁ }
    traverseᶜ {Γ = Γ} X (var W) π γ =
      record { Γₘₐₓ = Γ ; γₘₐₓ = γ ; πₘₐₓ = wk-id ; tree = leaf γ ; result = {!!} }
    traverseᶜ X (sub M₁ M₂) π γ = {!!}

    traverseˡ : {Γ₀ : Ctx} → (a : Arg Γ₀ X) → (Γ' ∋ X) → Wk Γ₀ Γ → Wk Γ Γ' → MEnv Γ₀ → MEnv Γ → Traversal Γ (result-type a)
    traverseˡ {Γ₀ = Γ₀} empty Cx.h π₀ (wk-cong π) γ₀ (γ ﹐ W) = record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; tree = leaf γ₀ ; result = wk-v̲a̲l̲ {!!} W }
    traverseˡ {Γ₀ = Γ₀} (arg W) Cx.h π₀ (wk-cong π) γ₀ (γ ﹐ l̲a̲m̲ M) =
      let
        IH = {!!} --traverseᶜ M (wk-cong (wk-trans π₀ (wk-wk wk-id))) (γ₀ ﹐ W)
      in
      record { Γₘₐₓ = Γₘₐₓ IH ; γₘₐₓ = γₘₐₓ IH ; πₘₐₓ = wk-trans (πₘₐₓ IH) (wk-wk π₀) ; tree = tree IH ; result = result IH }
    traverseˡ {Γ₀ = Γ₀} empty Cx.h π₀ (wk-cong π) γ₀ (γ ﹐j) = record { Γₘₐₓ = Γ₀ ∙ `V ; γₘₐₓ = γ₀ ﹐j ; πₘₐₓ = wk-wk π₀ ; tree = leaf (γ₀ ﹐j) ; result = v̲a̲r̲ h }
    traverseˡ {Γ₀ = Γ₀} empty Cx.h π₀ (wk-wk π) γ₀ (γ ﹐ M) =
      let
        IH = traverseˡ {Γ₀ = Γ₀} empty h (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ
      in
      record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; tree = leaf γ₀ ; result = wk-v̲a̲l̲ {!!} (result IH) }
    traverseˡ {Γ₀ = Γ₀} (arg W) Cx.h π₀ (wk-wk π) γ₀ (γ ﹐ M) =
      let
        IH = traverseˡ {Γ₀ = Γ₀} (arg W) Cx.h (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ
      in
      record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; tree = leaf γ₀ ; result = wk-v̲a̲l̲ {!!} (result IH) }
    traverseˡ {Γ₀ = Γ₀} empty Cx.h π₀ (wk-wk π) γ₀ (γ ﹐j) =
      let
        IH = traverseˡ {Γ₀ = Γ₀} empty h (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ
      in
      record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; tree = leaf γ₀ ; result = wk-v̲a̲l̲ {!!} (result IH) }
    traverseˡ {Γ₀ = Γ₀} (arg W) Cx.h π₀ (wk-wk π) γ₀ (γ ﹐j) =
      let
        IH = traverseˡ {Γ₀ = Γ₀} (arg W) h (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ
      in
      record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; tree = leaf γ₀ ; result = wk-v̲a̲l̲ {!!} (result IH) }
    traverseˡ {Γ₀ = Γ₀} empty (Cx.t i) π₀ (wk-cong π) γ₀ (γ ﹐ M) =
      let
        IH = traverseˡ {Γ₀ = Γ₀} empty i (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ
      in
      record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; tree = leaf γ₀ ; result = wk-v̲a̲l̲ {!!} (result IH) }
    traverseˡ {Γ₀ = Γ₀} empty (Cx.t i) π₀ (wk-cong π) γ₀ (γ ﹐j) =
      let
        IH = traverseˡ {Γ₀ = Γ₀} empty i (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ
      in
      record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; tree = leaf γ₀ ; result = wk-v̲a̲l̲ {!!} (result IH) }
    traverseˡ {Γ₀ = Γ₀} empty (Cx.t i) π₀ (wk-wk π) γ₀ (γ ﹐ M) =
      let
        IH = traverseˡ {Γ₀ = Γ₀} empty (t i) (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ
      in
      record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; tree = leaf γ₀ ; result = wk-v̲a̲l̲ {!!} (result IH) }
    traverseˡ {Γ₀ = Γ₀} empty (Cx.t i) π₀ (wk-wk π) γ₀ (γ ﹐j) =
      let
        IH = traverseˡ {Γ₀ = Γ₀} empty (Cx.t i) (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ
      in
      record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; tree = leaf γ₀ ; result = wk-v̲a̲l̲ {!!} (result IH) }
    traverseˡ {Γ₀ = Γ₀} (arg W) (Cx.t i) π₀ (wk-cong π) γ₀ (γ ﹐ M) =
      let
        IH = traverseˡ {Γ₀ = Γ₀} (arg W) i (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ
      in
      record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; tree = leaf γ₀ ; result = wk-v̲a̲l̲ {!!} (result IH) }
    traverseˡ {Γ₀ = Γ₀} (arg W) (Cx.t i) π₀ (wk-cong π) γ₀ (γ ﹐j) =
      let
        IH = traverseˡ {Γ₀ = Γ₀} (arg W) i (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ
      in
      record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; tree = leaf γ₀ ; result = wk-v̲a̲l̲ {!!} (result IH) }
    traverseˡ {Γ₀ = Γ₀} (arg W) (Cx.t i) π₀ (wk-wk π) γ₀ (γ ﹐ M) =
      let
        IH = traverseˡ {Γ₀ = Γ₀} (arg W) (t i) (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ
      in
      record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; tree = leaf γ₀ ; result = wk-v̲a̲l̲ {!!} (result IH) }
    traverseˡ {Γ₀ = Γ₀} (arg W) (Cx.t i) π₀ (wk-wk π) γ₀ (γ ﹐j) =
      let
        IH = traverseˡ {Γ₀ = Γ₀} (arg W) (t i) (wk-trans π₀ (wk-wk wk-id)) π γ₀ γ
      in
      record { Γₘₐₓ = Γ₀ ; γₘₐₓ = γ₀ ; πₘₐₓ = π₀ ; tree = leaf γ₀ ; result = wk-v̲a̲l̲ {!!} (result IH) }

    traverseᵛ : (a : Arg Γ X) → (Z : Ty) → Z ≡ (result-type a) → Val Γ' X → Wk Γ Γ' → MEnv Γ → Traversal Γ (result-type a)
    traverseᵛ a Z eq (var i) π γ = traverseˡ a i wk-id π γ γ
    traverseᵛ {Γ = Γ} empty Z eq (lam M) π γ =
      record { Γₘₐₓ = Γ ; γₘₐₓ = γ ; πₘₐₓ = wk-id ; tree = leaf γ ; result = l̲a̲m̲ (wk-comp (wk-cong π) M) }
    traverseᵛ (arg W) Z eq (lam M) π γ =
      let
        IH = traverseᶜ _ M (wk-cong π) (γ ﹐ W)
      in
      record { Γₘₐₓ = Γₘₐₓ IH ; γₘₐₓ = γₘₐₓ IH ; πₘₐₓ = wk-trans (πₘₐₓ IH) (wk-wk wk-id) ; tree = tree IH ; result = result IH }
    traverseᵛ empty Z eq (pair W₁ W₂) π γ =
      let
        IH₁ = traverseᵛ empty _ refl W₁ π γ
        IH₂ = traverseᵛ empty _ refl W₂ (wk-trans (πₘₐₓ IH₁) π) (γₘₐₓ IH₁)
      in
      record { Γₘₐₓ = Γₘₐₓ IH₂ ; γₘₐₓ = γₘₐₓ IH₂ ; πₘₐₓ = wk-trans (πₘₐₓ IH₂) (πₘₐₓ IH₁) ; tree = tree IH₂ ; result = pa̲i̲r̲ (wk-v̲a̲l̲ (πₘₐₓ IH₂) (result IH₁)) (result IH₂) }
    traverseᵛ empty Z eq (pm W₁ W₂) π γ =
      let
        IH = traverseᵛ empty _ refl W₁ π γ
        IH' = traverseᵛ empty _ refl W₂ (wk-cong (wk-cong (wk-trans (πₘₐₓ IH) π))) (γₘₐₓ IH ﹐ p₁ (result IH) ﹐ wk-v̲a̲l̲ (wk-wk wk-id) (p₂ (result IH)))
      in
      record { Γₘₐₓ = Γₘₐₓ IH' ; γₘₐₓ = γₘₐₓ IH' ; πₘₐₓ = wk-trans (πₘₐₓ IH') (wk-wk (wk-wk (πₘₐₓ IH))) ; tree = tree IH' ; result = result IH' }
    traverseᵛ (arg W) Z eq (pm W₁ W₂) π γ =
      let
        IH = traverseᵛ empty _ refl W₁ π γ
        IH' = traverseᵛ (arg (wk-v̲a̲l̲ (wk-wk (wk-wk (πₘₐₓ IH))) W)) _ refl W₂ (wk-cong (wk-cong (wk-trans (πₘₐₓ IH) π))) (γₘₐₓ IH ﹐ p₁ (result IH) ﹐ wk-v̲a̲l̲ (wk-wk wk-id) (p₂ (result IH)))
      in
      record { Γₘₐₓ = Γₘₐₓ IH' ; γₘₐₓ = γₘₐₓ IH' ; πₘₐₓ = wk-trans (πₘₐₓ IH') (wk-wk (wk-wk (πₘₐₓ IH))) ; tree = tree IH' ; result = result IH' }
    traverseᵛ {Γ = Γ} empty Z eq unit π γ = record { Γₘₐₓ = Γ ; γₘₐₓ = γ ; πₘₐₓ = wk-id ; tree = leaf γ ; result = u̲n̲i̲t̲ }

{-
    traverseᶜ : Comp Γ' X → Wk Γ Γ' → (γ : MEnv Γ) → Traversal Γ X
    traverseᶜ (return W) π γ =
      let
        IH = traverseᵛ W π γ
      in
      record { Γₘₐₓ = Γₘₐₓ IH ; γₘₐₓ = γₘₐₓ IH ; πₘₐₓ = πₘₐₓ IH ; tree = tree IH ; result = result IH}
    traverseᶜ (pm W M) π γ =
      let
        IH = traverseᵛ W π γ
        IH' = traverseᶜ M (wk-cong (wk-cong (wk-trans (πₘₐₓ IH) π))) (γₘₐₓ IH ﹐ p₁ (result IH) ﹐ wk-v̲a̲l̲ (wk-wk wk-id) (p₂ (result IH)))
      in
      record { Γₘₐₓ = Γₘₐₓ IH' ; γₘₐₓ = γₘₐₓ IH' ; πₘₐₓ = wk-trans (πₘₐₓ IH') (wk-wk (wk-wk (πₘₐₓ IH))) ; tree = tree IH' ; result = result IH' }
    traverseᶜ (push M₁ M₂) π γ =
      let
        IH₁ = traverseᶜ M₁ π γ
        IH' = traverseᶜ M₂ (wk-cong (wk-trans (πₘₐₓ IH₁) π)) (γₘₐₓ IH₁ ﹐ result IH₁)
      in
      record { Γₘₐₓ = Γₘₐₓ IH' ; γₘₐₓ = γₘₐₓ IH' ; πₘₐₓ = wk-trans (πₘₐₓ IH') (wk-wk (πₘₐₓ IH₁)) ; tree = tree IH' ; result = result IH' }
    traverseᶜ (app W₁ W₂) π γ =
      let
        IH₂ = traverseᵛ W₂ π γ
        IH₁ = traverseᵛ W₁ (wk-trans (πₘₐₓ IH₂) π) (γₘₐₓ IH₂)
        IH  = traverseᶜ (c₁ (result IH₁)) wk-id (γₘₐₓ IH₁ ﹐ wk-v̲a̲l̲ (πₘₐₓ IH₁) (result IH₂))
      in
      record { Γₘₐₓ = {!!} ; γₘₐₓ = {!!} ; πₘₐₓ = {!!} ; tree = {!!} ; result = {!!} }
    traverseᶜ (var W) π γ = {!!}
    traverseᶜ (sub M₁ M₂) π γ = {!!}

    traverseᵛ : Val Γ' X → Wk Γ Γ' → MEnv Γ → Traversal Γ X --Σ[ t ∈ Traversal Γ ] (V̲a̲l̲ (Γₘₐₓ t) X)
    traverseᵛ (var i) π γ = {!!}
    traverseᵛ (lam M) π γ = {!!}
    traverseᵛ (pair W₁ W₂) π γ = {!!}
    traverseᵛ (pm W₁ W₂) π γ = {!!}
    traverseᵛ unit π γ = {!!}
-}

XXX -}
