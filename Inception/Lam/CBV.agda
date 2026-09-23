{-# OPTIONS --no-postfix-projections #-}

module Inception.Lam.CBV (R : Set) where

open import Inception.Lam.Syntax

open import Data.Unit
open import Data.Product as P
open import Function as F hiding (_∋_)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Inception.Prelude

open import Level using (0ℓ)
open import Inception.Cont.Base
open import Inception.Monad.Base using (Monad)

K : Set -> Set
K = K[ R ]

open Monad (K[_]-Monad {x = 0ℓ} R) using (η; _*)

⟦_⟧ : Ty -> Set
⟦ `Unit ⟧  = ⊤
⟦ A `⇒ B ⟧ = ⟦ A ⟧ -> K ⟦ B ⟧

open Sem ⟦_⟧

mutual
  ⟦_⟧ᵛ : Γ ⊢ᵛ A -> ⟦ Γ ⟧ˣ -> ⟦ A ⟧
  ⟦ var i ⟧ᵛ = ⟦ i ⟧ᵐ
  ⟦ lam M ⟧ᵛ = curry ⟦ M ⟧ᶜ
  ⟦ unit ⟧ᵛ  = const tt

  ⟦_⟧ᶜ : Γ ⊢ᶜ A -> ⟦ Γ ⟧ˣ -> K ⟦ A ⟧
  ⟦ return V ⟧ᶜ = ⟦ V ⟧ᵛ ； η
  ⟦ push M N ⟧ᶜ = < idf , ⟦ M ⟧ᶜ > ； τ ； ⟦ N ⟧ᶜ *
  ⟦ app V W ⟧ᶜ  = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ > ； ev

⟦_⟧ˢ : Γ ⊢ Δ -> ⟦ Γ ⟧ˣ -> ⟦ Δ ⟧ˣ
⟦ sub-ε ⟧ˢ      = const tt
⟦ sub-ex θ V ⟧ˢ = < ⟦ θ ⟧ˢ , ⟦ V ⟧ᵛ >

-- coherences

mutual
  wk-val-coh : (π : Γ ⊇ Δ) (V : Δ ⊢ᵛ A) -> ⟦ wk-val π V ⟧ᵛ ≡ (⟦ π ⟧ʷ ； ⟦ V ⟧ᵛ)
  wk-val-coh π (var i) rewrite wk-mem-coh π i = refl
  wk-val-coh π (lam M) rewrite wk-comp-coh (wk-cong π) M = refl
  wk-val-coh π unit    = refl

  wk-comp-coh : (π : Γ ⊇ Δ) (M : Δ ⊢ᶜ A) -> ⟦ wk-comp π M ⟧ᶜ ≡ (⟦ π ⟧ʷ ； ⟦ M ⟧ᶜ)
  wk-comp-coh π (return V) rewrite wk-val-coh π V = refl
  wk-comp-coh π (push M N) rewrite wk-comp-coh π M | wk-comp-coh (wk-cong π) N = refl
  wk-comp-coh π (app V W)  rewrite wk-val-coh π V | wk-val-coh π W = refl

{-# REWRITE wk-val-coh #-}
{-# REWRITE wk-comp-coh #-}

sub-mem-coh : (θ : Γ ⊢ Δ) (i : Δ ∋ A) -> ⟦ sub-mem θ i ⟧ᵛ ≡ (⟦ θ ⟧ˢ ； ⟦ i ⟧ᵐ)
sub-mem-coh (sub-ex θ V) here     = refl
sub-mem-coh (sub-ex θ V) (there i) rewrite sub-mem-coh θ i = refl
{-# REWRITE sub-mem-coh #-}

sub-wk-coh : (π : Γ ⊇ Δ) (θ : Δ ⊢ Ψ) -> ⟦ sub-wk π θ ⟧ˢ ≡ (⟦ π ⟧ʷ ； ⟦ θ ⟧ˢ)
sub-wk-coh π sub-ε        = refl
sub-wk-coh π (sub-ex θ V) rewrite sub-wk-coh π θ | wk-val-coh π V = refl
{-# REWRITE sub-wk-coh #-}

sub-id-coh : ⟦ sub-id {Γ} ⟧ˢ ≡ id
sub-id-coh {ε}     = refl
sub-id-coh {Γ ∙ A} = funext \(γ , a) -> cong₂ _,_ (happly sub-id-coh γ) refl
{-# REWRITE sub-id-coh #-}

mutual
  sub-val-coh : (θ : Γ ⊢ Δ) (V : Δ ⊢ᵛ A) -> ⟦ sub-val θ V ⟧ᵛ ≡ (⟦ θ ⟧ˢ ； ⟦ V ⟧ᵛ)
  sub-val-coh θ (var i) = refl
  sub-val-coh θ (lam M) rewrite sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M = refl
  sub-val-coh θ unit    = refl

  sub-comp-coh : (θ : Γ ⊢ Δ) (M : Δ ⊢ᶜ A) -> ⟦ sub-comp θ M ⟧ᶜ ≡ (⟦ θ ⟧ˢ ； ⟦ M ⟧ᶜ)
  sub-comp-coh θ (return V) rewrite sub-val-coh θ V = refl
  sub-comp-coh θ (push M N) rewrite sub-comp-coh θ M | sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N = refl
  sub-comp-coh θ (app V W)  rewrite sub-val-coh θ V | sub-val-coh θ W = refl

{-# REWRITE sub-val-coh #-}
{-# REWRITE sub-comp-coh #-}

--------------------------------------------------------------------------
-- semantics of CK machine

module CK where
  open import Inception.Lam.CK

  ⟦_⟧ᵏ : Γ ⊢ᵏ A ⇒ B -> ⟦ Γ ⟧ˣ -> (R ^ ⟦ B ⟧) -> (R ^ ⟦ A ⟧)
  ⟦ ε ⟧ᵏ     γ k = k
  ⟦ N ∷ K ⟧ᵏ γ k = \a -> ⟦ N ⟧ᶜ (γ , a) (⟦ K ⟧ᵏ γ k)

  ⟦_⟧ᶜᶠᵍ : Cfg Γ B -> ⟦ Γ ⟧ˣ -> (R ^ ⟦ B ⟧) -> R
  ⟦ ⟨ M ∥ K ⟩ ⟧ᶜᶠᵍ γ k = ⟦ M ⟧ᶜ γ (⟦ K ⟧ᵏ γ k)

--------------------------------------------------------------------------
-- semantics of CEK machine

module CEK where
  open import Inception.Lam.CEK

  mutual
    ⟦_⟧ⱽ : Value A -> ⟦ A ⟧
    ⟦ unit ⟧ⱽ    = tt
    ⟦ clo N ρ ⟧ⱽ = \a -> ⟦ N ⟧ᶜ (⟦ ρ ⟧ᴱ , a)

    ⟦_⟧ᴱ : Env Γ -> ⟦ Γ ⟧ˣ
    ⟦ ∅ ⟧ᴱ     = tt
    ⟦ ρ ∷ v ⟧ᴱ = ⟦ ρ ⟧ᴱ , ⟦ v ⟧ⱽ

    ⟦_⟧ᴷ : Kont A B -> (R ^ ⟦ B ⟧) -> (R ^ ⟦ A ⟧)
    ⟦ ε ⟧ᴷ           k = k
    ⟦ N ◂ ρ ∷ κ ⟧ᴷ k = \a -> ⟦ N ⟧ᶜ (⟦ ρ ⟧ᴱ , a) (⟦ κ ⟧ᴷ k)

  ⟦_⟧ᶜᶠᵍ : Cfg B -> (R ^ ⟦ B ⟧) -> R
  ⟦ ⟨ M ∥ ρ ∥ κ ⟩ ⟧ᶜᶠᵍ k = ⟦ M ⟧ᶜ ⟦ ρ ⟧ᴱ (⟦ κ ⟧ᴷ k)
  ⟦ ⟨ v ∥ κ ⟩ ⟧ᶜᶠᵍ     k = ⟦ κ ⟧ᴷ k ⟦ v ⟧ⱽ
