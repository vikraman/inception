module Inception.Ctx.Sub (Ty : Set) where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)

open import Inception.Ctx.Base Ty
open import Inception.Ctx.Wk Ty

--------------------------------------------------------------------------
-- substitutions

data Sub (P : Ty → Set) : Ctx → Set where
  sub-ε  : Sub P ε
  sub-ex : (θ : Sub P Δ) → (V : P X) → Sub P (Δ ∙ X)

sub-mem : {P : Ty → Set} → Sub P Δ → Δ ∋ X → P X
sub-mem (sub-ex θ V) here      = V
sub-mem (sub-ex θ V) (there i) = sub-mem θ i

sub-map : {P Q : Ty → Set} → (∀ {X} → P X → Q X) → Sub P Δ → Sub Q Δ
sub-map f sub-ε        = sub-ε
sub-map f (sub-ex θ V) = sub-ex (sub-map f θ) (f V)

sub-pre : {P : Ty → Set} → Sub P Δ → Δ ⊇ Ψ → Sub P Ψ
sub-pre θ wk-ε                   = sub-ε
sub-pre (sub-ex θ V) (wk-cong π) = sub-ex (sub-pre θ π) V
sub-pre (sub-ex θ V) (wk-wk π)   = sub-pre θ π

--------------------------------------------------------------------------
-- substitution laws

sub-mem-map-β : {P Q : Ty → Set} (f : ∀ {X} → P X → Q X) (θ : Sub P Δ) (i : Δ ∋ X) → sub-mem (sub-map f θ) i ≡ f (sub-mem θ i)
sub-mem-map-β f (sub-ex θ V) here      = refl
sub-mem-map-β f (sub-ex θ V) (there i) = sub-mem-map-β f θ i
{-# REWRITE sub-mem-map-β #-}

sub-map-id-β : {P : Ty → Set} (θ : Sub P Δ) → sub-map (λ V → V) θ ≡ θ
sub-map-id-β sub-ε        = refl
sub-map-id-β (sub-ex θ V) = cong (λ φ → sub-ex φ V) (sub-map-id-β θ)
{-# REWRITE sub-map-id-β #-}

sub-map-map-η : {P Q R : Ty → Set} (f : ∀ {X} → Q X → R X) (g : ∀ {X} → P X → Q X) (θ : Sub P Δ) → sub-map f (sub-map g θ) ≡ sub-map (λ V → f (g V)) θ
sub-map-map-η f g sub-ε        = refl
sub-map-map-η f g (sub-ex θ V) = cong (λ φ → sub-ex φ (f (g V))) (sub-map-map-η f g θ)
{-# REWRITE sub-map-map-η #-}

sub-mem-pre-β : {P : Ty → Set} (θ : Sub P Δ) (π : Δ ⊇ Ψ) (i : Ψ ∋ X) → sub-mem (sub-pre θ π) i ≡ sub-mem θ (wk-mem π i)
sub-mem-pre-β (sub-ex θ V) (wk-cong π) here      = refl
sub-mem-pre-β (sub-ex θ V) (wk-cong π) (there i) = sub-mem-pre-β θ π i
sub-mem-pre-β (sub-ex θ V) (wk-wk π) i           = sub-mem-pre-β θ π i
{-# REWRITE sub-mem-pre-β #-}

sub-pre-map-η : {P Q : Ty → Set} (f : ∀ {X} → P X → Q X) (θ : Sub P Δ) (π : Δ ⊇ Ψ) → sub-pre (sub-map f θ) π ≡ sub-map f (sub-pre θ π)
sub-pre-map-η f θ wk-ε                   = refl
sub-pre-map-η f (sub-ex θ V) (wk-cong π) = cong (λ φ → sub-ex φ (f V)) (sub-pre-map-η f θ π)
sub-pre-map-η f (sub-ex θ V) (wk-wk π)   = sub-pre-map-η f θ π
{-# REWRITE sub-pre-map-η #-}

sub-pre-idr-β : {P : Ty → Set} (θ : Sub P Δ) → sub-pre θ wk-id ≡ θ
sub-pre-idr-β sub-ε        = refl
sub-pre-idr-β (sub-ex θ V) = cong (λ φ → sub-ex φ V) (sub-pre-idr-β θ)
{-# REWRITE sub-pre-idr-β #-}

sub-pre-idr-η : {P : Ty → Set} (θ : Sub P Δ) (π : Δ ⊇ Δ) → sub-pre θ π ≡ θ
sub-pre-idr-η θ π = cong (sub-pre θ) (wk-id-η π)
{-# REWRITE sub-pre-idr-η #-}

sub-pre-pre-η : {P : Ty → Set} (θ : Sub P Δ) (π : Δ ⊇ Ψ) (δ : Ψ ⊇ Ξ) → sub-pre (sub-pre θ π) δ ≡ sub-pre θ (wk-trans π δ)
sub-pre-pre-η θ wk-ε wk-ε                          = refl
sub-pre-pre-η (sub-ex θ V) (wk-cong π) (wk-cong δ) = cong (λ φ → sub-ex φ V) (sub-pre-pre-η θ π δ)
sub-pre-pre-η (sub-ex θ V) (wk-cong π) (wk-wk δ)   = sub-pre-pre-η θ π δ
sub-pre-pre-η (sub-ex θ V) (wk-wk π) δ             = sub-pre-pre-η θ π δ
{-# REWRITE sub-pre-pre-η #-}
