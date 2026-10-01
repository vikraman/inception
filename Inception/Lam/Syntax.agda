{-# OPTIONS --no-postfix-projections #-}

module Inception.Lam.Syntax where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; cong₂; sym)
open Eq.≡-Reasoning

--------------------------------------------------------------------------
-- types and contexts

infixr 25 _`⇒_

data Ty : Set where
  `𝟙 : Ty
  _`⇒_  : Ty → Ty → Ty

open import Inception.Ctx Ty public

--------------------------------------------------------------------------
-- values and computations

syntax Val Γ X = Γ ⊢ᵛ X
data Val : Ctx → Ty → Set

syntax Comp Γ X = Γ ⊢ᶜ X
data Comp : Ctx → Ty → Set

data Val where
  var  : (i : Γ ∋ X) → Γ ⊢ᵛ X
  lam  : (Γ ∙ X) ⊢ᶜ Y → Γ ⊢ᵛ X `⇒ Y
  unit : Γ ⊢ᵛ `𝟙

data Comp where
  return : Γ ⊢ᵛ X → Γ ⊢ᶜ X
  push   : Γ ⊢ᶜ X → (Γ ∙ X) ⊢ᶜ Y → Γ ⊢ᶜ Y
  app    : Γ ⊢ᵛ X `⇒ Y → Γ ⊢ᵛ X → Γ ⊢ᶜ Y

--------------------------------------------------------------------------
-- weakenings

mutual
  wk-val : Γ ⊇ Δ → Δ ⊢ᵛ X → Γ ⊢ᵛ X
  wk-val π (var i)      = var (wk-mem π i)
  wk-val π (lam M)      = lam (wk-comp (wk-cong π) M)
  wk-val π unit         = unit

  wk-comp : Γ ⊇ Δ → Δ ⊢ᶜ X → Γ ⊢ᶜ X
  wk-comp π (return V) = return (wk-val π V)
  wk-comp π (push M N) = push (wk-comp π M) (wk-comp (wk-cong π) N)
  wk-comp π (app V W)  = app (wk-val π V) (wk-val π W)

wk : Γ ⊢ᵛ X → (Γ ∙ Y) ⊢ᵛ X
wk = wk-val (wk-wk wk-id)

--------------------------------------------------------------------------
-- substitutions

syntax Sub Γ Δ = Γ ⊢ Δ
data Sub (Γ : Ctx) : (Δ : Ctx) → Set where
  sub-ε  : Γ ⊢ ε
  sub-ex : (θ : Γ ⊢ Δ) → (V : Γ ⊢ᵛ X) → Γ ⊢ (Δ ∙ X)

sub-mem : Γ ⊢ Δ → Δ ∋ X → Γ ⊢ᵛ X
sub-mem (sub-ex θ V) here     = V
sub-mem (sub-ex θ V) (there i) = sub-mem θ i

sub-wk : Γ ⊇ Δ → Δ ⊢ Ψ → Γ ⊢ Ψ
sub-wk π sub-ε        = sub-ε
sub-wk π (sub-ex θ V) = sub-ex (sub-wk π θ) (wk-val π V)

sub-id : Γ ⊢ Γ
sub-id {Γ = ε}     = sub-ε
sub-id {Γ = Γ ∙ X} = sub-ex (sub-wk (wk-wk wk-id) sub-id) (var here)

mutual
  sub-val : Γ ⊢ Δ → Δ ⊢ᵛ X → Γ ⊢ᵛ X
  sub-val θ (var i)      = sub-mem θ i
  sub-val θ (lam M)      = lam (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  sub-val θ unit         = unit

  sub-comp : Γ ⊢ Δ → Δ ⊢ᶜ X → Γ ⊢ᶜ X
  sub-comp θ (return V) = return (sub-val θ V)
  sub-comp θ (push M N) = push (sub-comp θ M) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
  sub-comp θ (app V W)  = app (sub-val θ V) (sub-val θ W)

--------------------------------------------------------------------------
-- weakening

mutual
  wk-val-id-β : (V : Γ ⊢ᵛ X) → wk-val wk-id V ≡ V
  wk-val-id-β (var i) = refl
  wk-val-id-β (lam M) = cong lam (wk-comp-id-β M)
  wk-val-id-β unit    = refl

  wk-comp-id-β : (M : Γ ⊢ᶜ X) → wk-comp wk-id M ≡ M
  wk-comp-id-β (return V) = cong return (wk-val-id-β V)
  wk-comp-id-β (push M N) = cong₂ push (wk-comp-id-β M) (wk-comp-id-β N)
  wk-comp-id-β (app V W)  = cong₂ app (wk-val-id-β V) (wk-val-id-β W)

{-# REWRITE wk-val-id-β wk-comp-id-β #-}

wk-val-id-η : (π : Γ ⊇ Γ) (V : Γ ⊢ᵛ X) → wk-val π V ≡ V
wk-val-id-η π V = cong (λ δ → wk-val δ V) (wk-id-η π)

wk-comp-id-η : (π : Γ ⊇ Γ) (M : Γ ⊢ᶜ X) → wk-comp π M ≡ M
wk-comp-id-η π M = cong (λ δ → wk-comp δ M) (wk-id-η π)

{-# REWRITE wk-val-id-η wk-comp-id-η #-}

mutual
  wk-val-wk-η : (V : Γ ⊢ᵛ X) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → wk-val π (wk-val δ V) ≡ wk-val (wk-trans π δ) V
  wk-val-wk-η (var i) π δ = refl
  wk-val-wk-η (lam M) π δ = cong lam (wk-comp-wk-η M (wk-cong π) (wk-cong δ))
  wk-val-wk-η unit π δ    = refl

  wk-comp-wk-η : (M : Γ ⊢ᶜ X) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → wk-comp π (wk-comp δ M) ≡ wk-comp (wk-trans π δ) M
  wk-comp-wk-η (return V) π δ = cong return (wk-val-wk-η V π δ)
  wk-comp-wk-η (push M N) π δ = cong₂ push (wk-comp-wk-η M π δ) (wk-comp-wk-η N (wk-cong π) (wk-cong δ))
  wk-comp-wk-η (app V W) π δ  = cong₂ app (wk-val-wk-η V π δ) (wk-val-wk-η W π δ)

{-# REWRITE wk-val-wk-η wk-comp-wk-η #-}

--------------------------------------------------------------------------
-- weakening/substitution

sub-wk-id-β : (θ : Γ ⊢ Δ) → sub-wk wk-id θ ≡ θ
sub-wk-id-β sub-ε        = refl
sub-wk-id-β (sub-ex θ V) = cong₂ sub-ex (sub-wk-id-β θ) refl
{-# REWRITE sub-wk-id-β #-}

sub-wk-id-η : (π : Γ ⊇ Γ) (θ : Γ ⊢ Δ) → sub-wk π θ ≡ θ
sub-wk-id-η π θ = cong (λ δ → sub-wk δ θ) (wk-id-η π)
{-# REWRITE sub-wk-id-η #-}

sub-wk-wk-η : (π : Γ ⊇ Ψ) (δ : Ψ ⊇ Ξ) (θ : Ξ ⊢ Δ)
             → sub-wk π (sub-wk δ θ) ≡ sub-wk (wk-trans π δ) θ
sub-wk-wk-η π δ sub-ε        = refl
sub-wk-wk-η π δ (sub-ex θ V) = cong₂ sub-ex (sub-wk-wk-η π δ θ) refl
{-# REWRITE sub-wk-wk-η #-}

sub-mem-wk-β : (π : Γ ⊇ Δ) (θ : Δ ⊢ Ψ) (i : Ψ ∋ X) → sub-mem (sub-wk π θ) i ≡ wk-val π (sub-mem θ i)
sub-mem-wk-β π (sub-ex θ V) here     = refl
sub-mem-wk-β π (sub-ex θ V) (there i) = sub-mem-wk-β π θ i
{-# REWRITE sub-mem-wk-β #-}

mutual
  wk-val-sub-η : (π : Ψ ⊇ Γ) (θ : Γ ⊢ Δ) (V : Δ ⊢ᵛ X) → wk-val π (sub-val θ V) ≡ sub-val (sub-wk π θ) V
  wk-val-sub-η π θ (var i) = refl
  wk-val-sub-η π θ (lam M) = cong lam (wk-comp-sub-η (wk-cong π) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  wk-val-sub-η π θ unit    = refl

  wk-comp-sub-η : (π : Ψ ⊇ Γ) (θ : Γ ⊢ Δ) (M : Δ ⊢ᶜ X) → wk-comp π (sub-comp θ M) ≡ sub-comp (sub-wk π θ) M
  wk-comp-sub-η π θ (return V) = cong return (wk-val-sub-η π θ V)
  wk-comp-sub-η π θ (push M N) =
    cong₂ push (wk-comp-sub-η π θ M) (wk-comp-sub-η (wk-cong π) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
  wk-comp-sub-η π θ (app V W)  = cong₂ app (wk-val-sub-η π θ V) (wk-val-sub-η π θ W)

{-# REWRITE wk-val-sub-η wk-comp-sub-η #-}

--------------------------------------------------------------------------
-- substitution precomposed with weakening

sub-pre : Γ ⊢ Δ → Δ ⊇ Ψ → Γ ⊢ Ψ
sub-pre θ wk-ε              = sub-ε
sub-pre (sub-ex θ V) (wk-cong π) = sub-ex (sub-pre θ π) V
sub-pre (sub-ex θ V) (wk-wk π)   = sub-pre θ π

sub-mem-pre-β : (θ : Γ ⊢ Δ) (π : Δ ⊇ Ψ) (i : Ψ ∋ X) → sub-mem (sub-pre θ π) i ≡ sub-mem θ (wk-mem π i)
sub-mem-pre-β (sub-ex θ V) (wk-cong π) here      = refl
sub-mem-pre-β (sub-ex θ V) (wk-cong π) (there i) = sub-mem-pre-β θ π i
sub-mem-pre-β (sub-ex θ V) (wk-wk π) i           = sub-mem-pre-β θ π i
{-# REWRITE sub-mem-pre-β #-}

sub-pre-wk-η : (π : Ξ ⊇ Γ) (θ : Γ ⊢ Δ) (δ : Δ ⊇ Ψ) → sub-pre (sub-wk π θ) δ ≡ sub-wk π (sub-pre θ δ)
sub-pre-wk-η π θ wk-ε                   = refl
sub-pre-wk-η π (sub-ex θ V) (wk-cong δ) = cong₂ sub-ex (sub-pre-wk-η π θ δ) refl
sub-pre-wk-η π (sub-ex θ V) (wk-wk δ)   = sub-pre-wk-η π θ δ
{-# REWRITE sub-pre-wk-η #-}

sub-pre-idr-β : (θ : Γ ⊢ Δ) → sub-pre θ (wk-id {Δ}) ≡ θ
sub-pre-idr-β sub-ε        = refl
sub-pre-idr-β (sub-ex θ V) = cong₂ sub-ex (sub-pre-idr-β θ) refl
{-# REWRITE sub-pre-idr-β #-}

sub-pre-idr-η : (θ : Γ ⊢ Δ) (π : Δ ⊇ Δ) → sub-pre θ π ≡ θ
sub-pre-idr-η θ π = cong (sub-pre θ) (wk-id-η π)
{-# REWRITE sub-pre-idr-η #-}

sub-pre-pre-η : (θ : Γ ⊢ Δ) (π : Δ ⊇ Ψ) (δ : Ψ ⊇ Ξ) → sub-pre (sub-pre θ π) δ ≡ sub-pre θ (wk-trans π δ)
sub-pre-pre-η θ wk-ε wk-ε                       = refl
sub-pre-pre-η (sub-ex θ V) (wk-cong π) (wk-cong δ) = cong₂ sub-ex (sub-pre-pre-η θ π δ) refl
sub-pre-pre-η (sub-ex θ V) (wk-cong π) (wk-wk δ)   = sub-pre-pre-η θ π δ
sub-pre-pre-η (sub-ex θ V) (wk-wk π) δ             = sub-pre-pre-η θ π δ
{-# REWRITE sub-pre-pre-η #-}

sub-pre-idl-β : (π : Δ ⊇ Γ) → sub-pre (sub-id {Δ}) π ≡ sub-wk π (sub-id {Γ})
sub-pre-idl-β wk-ε        = refl
sub-pre-idl-β (wk-cong π) = cong (λ θ → sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-pre-idl-β π)
sub-pre-idl-β (wk-wk π)   = cong (sub-wk (wk-wk wk-id)) (sub-pre-idl-β π)
{-# REWRITE sub-pre-idl-β #-}

mutual
  sub-val-wk-η : (θ : Γ ⊢ Ψ) (π : Ψ ⊇ Δ) (V : Δ ⊢ᵛ X) → sub-val θ (wk-val π V) ≡ sub-val (sub-pre θ π) V
  sub-val-wk-η θ π (var i) = refl
  sub-val-wk-η θ π (lam M) = cong lam (sub-comp-wk-η (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-cong π) M)
  sub-val-wk-η θ π unit    = refl

  sub-comp-wk-η : (θ : Γ ⊢ Ψ) (π : Ψ ⊇ Δ) (M : Δ ⊢ᶜ X) → sub-comp θ (wk-comp π M) ≡ sub-comp (sub-pre θ π) M
  sub-comp-wk-η θ π (return V) = cong return (sub-val-wk-η θ π V)
  sub-comp-wk-η θ π (push M N) =
    cong₂ push (sub-comp-wk-η θ π M) (sub-comp-wk-η (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-cong π) N)
  sub-comp-wk-η θ π (app V W)  = cong₂ app (sub-val-wk-η θ π V) (sub-val-wk-η θ π W)

{-# REWRITE sub-val-wk-η sub-comp-wk-η #-}

--------------------------------------------------------------------------
-- substitution composition

sub-∘ : Γ ⊢ Δ → Δ ⊢ Ψ → Γ ⊢ Ψ
sub-∘ θ sub-ε        = sub-ε
sub-∘ θ (sub-ex φ V) = sub-ex (sub-∘ θ φ) (sub-val θ V)

sub-mem-sub-β : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) (i : Ψ ∋ X) → sub-mem (sub-∘ θ φ) i ≡ sub-val θ (sub-mem φ i)
sub-mem-sub-β θ (sub-ex φ V) here      = refl
sub-mem-sub-β θ (sub-ex φ V) (there i) = sub-mem-sub-β θ φ i
{-# REWRITE sub-mem-sub-β #-}

sub-∘-wkr-η : (θ : Γ ⊢ Ξ) (π : Ξ ⊇ Δ) (φ : Δ ⊢ Ψ) → sub-∘ θ (sub-wk π φ) ≡ sub-∘ (sub-pre θ π) φ
sub-∘-wkr-η θ π sub-ε        = refl
sub-∘-wkr-η θ π (sub-ex φ V) = cong₂ sub-ex (sub-∘-wkr-η θ π φ) refl
{-# REWRITE sub-∘-wkr-η #-}

sub-∘-wkl-η : (π : Ξ ⊇ Γ) (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) → sub-∘ (sub-wk π θ) φ ≡ sub-wk π (sub-∘ θ φ)
sub-∘-wkl-η π θ sub-ε        = refl
sub-∘-wkl-η π θ (sub-ex φ V) = cong₂ sub-ex (sub-∘-wkl-η π θ φ) refl
{-# REWRITE sub-∘-wkl-η #-}

sub-pre-sub-η : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) (π : Ψ ⊇ Ξ) → sub-pre (sub-∘ θ φ) π ≡ sub-∘ θ (sub-pre φ π)
sub-pre-sub-η θ φ wk-ε                   = refl
sub-pre-sub-η θ (sub-ex φ V) (wk-cong π) = cong₂ sub-ex (sub-pre-sub-η θ φ π) refl
sub-pre-sub-η θ (sub-ex φ V) (wk-wk π)   = sub-pre-sub-η θ φ π
{-# REWRITE sub-pre-sub-η #-}

mutual
  sub-val-sub-η : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) (V : Ψ ⊢ᵛ X) → sub-val θ (sub-val φ V) ≡ sub-val (sub-∘ θ φ) V
  sub-val-sub-η θ φ (var i) = refl
  sub-val-sub-η θ φ (lam M) =
    cong lam (sub-comp-sub-η (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here)) M)
  sub-val-sub-η θ φ unit    = refl

  sub-comp-sub-η : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) (M : Ψ ⊢ᶜ X) → sub-comp θ (sub-comp φ M) ≡ sub-comp (sub-∘ θ φ) M
  sub-comp-sub-η θ φ (return V) = cong return (sub-val-sub-η θ φ V)
  sub-comp-sub-η θ φ (push M N) =
    cong₂ push (sub-comp-sub-η θ φ M)
               (sub-comp-sub-η (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here)) N)
  sub-comp-sub-η θ φ (app V W)  = cong₂ app (sub-val-sub-η θ φ V) (sub-val-sub-η θ φ W)

{-# REWRITE sub-val-sub-η sub-comp-sub-η #-}

sub-∘-assoc-η : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) (ψ : Ψ ⊢ Ξ)
                   → sub-∘ θ (sub-∘ φ ψ) ≡ sub-∘ (sub-∘ θ φ) ψ
sub-∘-assoc-η θ φ sub-ε        = refl
sub-∘-assoc-η θ φ (sub-ex ψ V) = cong₂ sub-ex (sub-∘-assoc-η θ φ ψ) refl
{-# REWRITE sub-∘-assoc-η #-}

--------------------------------------------------------------------------
-- identity substitution

sub-mem-id-β : (i : Γ ∋ X) → sub-mem (sub-id {Γ}) i ≡ var i
sub-mem-id-β here      = refl
sub-mem-id-β (there i) = cong (wk-val (wk-wk wk-id)) (sub-mem-id-β i)
{-# REWRITE sub-mem-id-β #-}

mutual
  sub-val-ren-β : (π : Γ ⊇ Δ) (V : Δ ⊢ᵛ X) → sub-val (sub-wk π sub-id) V ≡ wk-val π V
  sub-val-ren-β π (var i) = refl
  sub-val-ren-β π (lam M) = cong lam (sub-comp-ren-β (wk-cong π) M)
  sub-val-ren-β π unit    = refl

  sub-comp-ren-β : (π : Γ ⊇ Δ) (M : Δ ⊢ᶜ X) → sub-comp (sub-wk π sub-id) M ≡ wk-comp π M
  sub-comp-ren-β π (return V) = cong return (sub-val-ren-β π V)
  sub-comp-ren-β π (push M N) = cong₂ push (sub-comp-ren-β π M) (sub-comp-ren-β (wk-cong π) N)
  sub-comp-ren-β π (app V W)  = cong₂ app (sub-val-ren-β π V) (sub-val-ren-β π W)

{-# REWRITE sub-val-ren-β sub-comp-ren-β #-}

sub-val-id-β : (V : Γ ⊢ᵛ X) → sub-val (sub-id {Γ}) V ≡ V
sub-val-id-β = sub-val-ren-β wk-id

sub-comp-id-β : (M : Γ ⊢ᶜ X) → sub-comp (sub-id {Γ}) M ≡ M
sub-comp-id-β = sub-comp-ren-β wk-id

{-# REWRITE sub-val-id-β sub-comp-id-β #-}

sub-∘-idl-β : (θ : Γ ⊢ Δ) → sub-∘ sub-id θ ≡ θ
sub-∘-idl-β sub-ε        = refl
sub-∘-idl-β (sub-ex θ V) = cong₂ sub-ex (sub-∘-idl-β θ) refl
{-# REWRITE sub-∘-idl-β #-}

sub-∘-idr-β : (θ : Γ ⊢ Δ) → sub-∘ θ sub-id ≡ θ
sub-∘-idr-β sub-ε        = refl
sub-∘-idr-β (sub-ex θ V) = cong₂ sub-ex (sub-∘-idr-β θ) refl
{-# REWRITE sub-∘-idr-β #-}
