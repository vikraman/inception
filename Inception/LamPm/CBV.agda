{-# OPTIONS --no-postfix-projections #-}

module Inception.LamPm.CBV (R : Set) where

open import Inception.LamPm.Syntax

open import Data.Unit
open import Data.Product as P
open import Function as F hiding (_∋_)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Inception.Prelude

open import Level using (0ℓ)
open import Inception.Cont.Base
open import Inception.Monad.Base using (Monad)

K : Set → Set
K = K[ R ]

open Monad (K[_]-Monad {x = 0ℓ} R) using (η; _*)

⟦_⟧ : Ty → Set
⟦ `𝟙 ⟧     = ⊤
⟦ X `× Y ⟧ = ⟦ X ⟧ × ⟦ Y ⟧
⟦ X `⇒ Y ⟧ = ⟦ X ⟧ → K ⟦ Y ⟧

open Sem ⟦_⟧

mutual
  ⟦_⟧ᵛ : Γ ⊢ᵛ X → ⟦ Γ ⟧ˣ → ⟦ X ⟧
  ⟦ var i ⟧ᵛ    = ⟦ i ⟧ᵐ
  ⟦ lam M ⟧ᵛ    = curry ⟦ M ⟧ᶜ
  ⟦ pair V W ⟧ᵛ = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ >
  ⟦ pm V W ⟧ᵛ   = < idf , ⟦ V ⟧ᵛ > ； assocl ； ⟦ W ⟧ᵛ
  ⟦ unit ⟧ᵛ     = const tt

  ⟦_⟧ᶜ : Γ ⊢ᶜ X → ⟦ Γ ⟧ˣ → K ⟦ X ⟧
  ⟦ return V ⟧ᶜ = ⟦ V ⟧ᵛ ； η
  ⟦ push M N ⟧ᶜ = < idf , ⟦ M ⟧ᶜ > ； τ ； ⟦ N ⟧ᶜ *
  ⟦ app V W ⟧ᶜ  = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ > ； ev
  ⟦ pm V M ⟧ᶜ   = < idf , ⟦ V ⟧ᵛ > ； assocl ； ⟦ M ⟧ᶜ

⟦_⟧ˢ : Γ ⊢ Δ → ⟦ Γ ⟧ˣ → ⟦ Δ ⟧ˣ
⟦ sub-ε ⟧ˢ      = const tt
⟦ sub-ex θ V ⟧ˢ = < ⟦ θ ⟧ˢ , ⟦ V ⟧ᵛ >

-- coherences

mutual
  wk-val-coh : (π : Γ ⊇ Δ) (V : Δ ⊢ᵛ X) → ⟦ wk-val π V ⟧ᵛ ≡ (⟦ π ⟧ʷ ； ⟦ V ⟧ᵛ)
  wk-val-coh π (var i)      rewrite wk-mem-coh π i = refl
  wk-val-coh π (lam M)      rewrite wk-comp-coh (wk-cong π) M = refl
  wk-val-coh π (pair V W) rewrite wk-val-coh π V | wk-val-coh π W = refl
  wk-val-coh π (pm V W)     rewrite wk-val-coh π V | wk-val-coh (wk-cong (wk-cong π)) W = refl
  wk-val-coh π unit         = refl

  wk-comp-coh : (π : Γ ⊇ Δ) (M : Δ ⊢ᶜ X) → ⟦ wk-comp π M ⟧ᶜ ≡ (⟦ π ⟧ʷ ； ⟦ M ⟧ᶜ)
  wk-comp-coh π (return V) rewrite wk-val-coh π V = refl
  wk-comp-coh π (push M N) rewrite wk-comp-coh π M | wk-comp-coh (wk-cong π) N = refl
  wk-comp-coh π (app V W)  rewrite wk-val-coh π V | wk-val-coh π W = refl
  wk-comp-coh π (pm V M)   rewrite wk-val-coh π V | wk-comp-coh (wk-cong (wk-cong π)) M = refl

{-# REWRITE wk-val-coh #-}
{-# REWRITE wk-comp-coh #-}

sub-mem-coh : (θ : Γ ⊢ Δ) (i : Δ ∋ X) → ⟦ sub-mem θ i ⟧ᵛ ≡ (⟦ θ ⟧ˢ ； ⟦ i ⟧ᵐ)
sub-mem-coh (sub-ex θ V) here     = refl
sub-mem-coh (sub-ex θ V) (there i) rewrite sub-mem-coh θ i = refl
{-# REWRITE sub-mem-coh #-}

sub-wk-coh : (π : Γ ⊇ Δ) (θ : Δ ⊢ Ψ) → ⟦ sub-wk π θ ⟧ˢ ≡ (⟦ π ⟧ʷ ； ⟦ θ ⟧ˢ)
sub-wk-coh π sub-ε        = refl
sub-wk-coh π (sub-ex θ V) rewrite sub-wk-coh π θ | wk-val-coh π V = refl
{-# REWRITE sub-wk-coh #-}

sub-id-coh : ⟦ sub-id {Γ} ⟧ˢ ≡ id
sub-id-coh {ε}     = refl
sub-id-coh {Γ ∙ X} = funext \(γ , a) → cong₂ _,_ (happly sub-id-coh γ) refl
{-# REWRITE sub-id-coh #-}

mutual
  sub-val-coh : (θ : Γ ⊢ Δ) (V : Δ ⊢ᵛ X) → ⟦ sub-val θ V ⟧ᵛ ≡ (⟦ θ ⟧ˢ ； ⟦ V ⟧ᵛ)
  sub-val-coh θ (var i)      = refl
  sub-val-coh θ (lam M)      rewrite sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M = refl
  sub-val-coh θ (pair V W) rewrite sub-val-coh θ V | sub-val-coh θ W = refl
  sub-val-coh θ (pm V W)     rewrite sub-val-coh θ V | sub-val-coh (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) W = refl
  sub-val-coh θ unit         = refl

  sub-comp-coh : (θ : Γ ⊢ Δ) (M : Δ ⊢ᶜ X) → ⟦ sub-comp θ M ⟧ᶜ ≡ (⟦ θ ⟧ˢ ； ⟦ M ⟧ᶜ)
  sub-comp-coh θ (return V) rewrite sub-val-coh θ V = refl
  sub-comp-coh θ (push M N) rewrite sub-comp-coh θ M | sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N = refl
  sub-comp-coh θ (app V W)  rewrite sub-val-coh θ V | sub-val-coh θ W = refl
  sub-comp-coh θ (pm V M)   rewrite sub-val-coh θ V | sub-comp-coh (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M = refl

{-# REWRITE sub-val-coh #-}
{-# REWRITE sub-comp-coh #-}

--------------------------------------------------------------------------
-- semantics of CK machine

module CK where
  open import Inception.LamPm.CK

  ⟦_⟧ᵏ : Γ ⊢ᵏ X ⇒ Y → ⟦ Γ ⟧ˣ → (R ^ ⟦ Y ⟧) → (R ^ ⟦ X ⟧)
  ⟦ ε ⟧ᵏ        γ k = k
  ⟦ N ∷ K ⟧ᵏ    γ k = \a → ⟦ N ⟧ᶜ (γ , a) (⟦ K ⟧ᵏ γ k)
  ⟦ N pm∷ K ⟧ᵏ  γ k = \{ (a , b) → ⟦ N ⟧ᶜ ((γ , a) , b) (⟦ K ⟧ᵏ γ k) }
  ⟦ W pmᵛ∷ K ⟧ᵏ γ k = \{ (a , b) → ⟦ K ⟧ᵏ γ k (⟦ W ⟧ᵛ ((γ , a) , b)) }

  ⟦_⟧ᶜᶠᵍ : Cfg Γ X → ⟦ Γ ⟧ˣ → (R ^ ⟦ X ⟧) → R
  ⟦ ⟨ M ∥ K ⟩ ⟧ᶜᶠᵍ γ k = ⟦ M ⟧ᶜ γ (⟦ K ⟧ᵏ γ k)
  ⟦ [ V ∥ K ] ⟧ᶜᶠᵍ γ k = ⟦ K ⟧ᵏ γ k (⟦ V ⟧ᵛ γ)

--------------------------------------------------------------------------
-- semantics of CEK machine

module CEK where
  open import Inception.LamPm.CEK

  mutual
    ⟦_⟧ⱽ : MVal X → ⟦ X ⟧
    ⟦ unit ⟧ⱽ     = tt
    ⟦ pair 𝐕 𝐖 ⟧ⱽ = ⟦ 𝐕 ⟧ⱽ , ⟦ 𝐖 ⟧ⱽ
    ⟦ clo N γ ⟧ⱽ  = \a → ⟦ N ⟧ᶜ (⟦ γ ⟧ᴱ , a)

    ⟦_⟧ᴱ : Env Γ → ⟦ Γ ⟧ˣ
    ⟦ ∅ ⟧ᴱ     = tt
    ⟦ γ ∷ 𝐕 ⟧ᴱ = ⟦ γ ⟧ᴱ , ⟦ 𝐕 ⟧ⱽ

    ⟦_⟧ᴷ : Kont X Y → (R ^ ⟦ Y ⟧) → (R ^ ⟦ X ⟧)
    ⟦ ε ⟧ᴷ         k = k
    ⟦ N ◂ γ ∷ K ⟧ᴷ k = \a → ⟦ N ⟧ᶜ (⟦ γ ⟧ᴱ , a) (⟦ K ⟧ᴷ k)

  ⟦_⟧ᶜᶠᵍ : Cfg X → (R ^ ⟦ X ⟧) → R
  ⟦ ⟨ M ∥ γ ∥ K ⟩ ⟧ᶜᶠᵍ k = ⟦ M ⟧ᶜ ⟦ γ ⟧ᴱ (⟦ K ⟧ᴷ k)
  ⟦ [ 𝐕 ∥ K ] ⟧ᶜᶠᵍ     k = ⟦ K ⟧ᴷ k ⟦ 𝐕 ⟧ⱽ
