{-# OPTIONS --no-postfix-projections #-}

module Inception.LamPm.Syntax where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; cong₂; sym)
open Eq.≡-Reasoning

--------------------------------------------------------------------------
-- types and contexts

infixr 40 _`×_
infixr 25 _`⇒_

data Ty : Set where
  `𝟙 : Ty
  _`×_  : Ty → Ty → Ty
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
  pair : Γ ⊢ᵛ X → Γ ⊢ᵛ Y → Γ ⊢ᵛ X `× Y
  pm   : Γ ⊢ᵛ X `× Y → (Γ ∙ X ∙ Y) ⊢ᵛ Z → Γ ⊢ᵛ Z
  unit : Γ ⊢ᵛ `𝟙

data Comp where
  return : Γ ⊢ᵛ X → Γ ⊢ᶜ X
  push   : Γ ⊢ᶜ X → (Γ ∙ X) ⊢ᶜ Y → Γ ⊢ᶜ Y
  app    : Γ ⊢ᵛ X `⇒ Y → Γ ⊢ᵛ X → Γ ⊢ᶜ Y
  pm     : Γ ⊢ᵛ X `× Y → (Γ ∙ X ∙ Y) ⊢ᶜ Z → Γ ⊢ᶜ Z

--------------------------------------------------------------------------
-- weakenings

mutual
  wk-val : Γ ⊇ Δ → Δ ⊢ᵛ X → Γ ⊢ᵛ X
  wk-val π (var i)    = var (wk-mem π i)
  wk-val π (lam M)    = lam (wk-comp (wk-cong π) M)
  wk-val π (pair V W) = pair (wk-val π V) (wk-val π W)
  wk-val π (pm V W)   = pm (wk-val π V) (wk-val (wk-cong (wk-cong π)) W)
  wk-val π unit       = unit

  wk-comp : Γ ⊇ Δ → Δ ⊢ᶜ X → Γ ⊢ᶜ X
  wk-comp π (return V) = return (wk-val π V)
  wk-comp π (push M N) = push (wk-comp π M) (wk-comp (wk-cong π) N)
  wk-comp π (app V W)  = app (wk-val π V) (wk-val π W)
  wk-comp π (pm V M)   = pm (wk-val π V) (wk-comp (wk-cong (wk-cong π)) M)

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
  sub-val θ (var i)    = sub-mem θ i
  sub-val θ (lam M)    = lam (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  sub-val θ (pair V W) = pair (sub-val θ V) (sub-val θ W)
  sub-val θ (pm V W)   = pm (sub-val θ V) (sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) W)
  sub-val θ unit       = unit

  sub-comp : Γ ⊢ Δ → Δ ⊢ᶜ X → Γ ⊢ᶜ X
  sub-comp θ (return V) = return (sub-val θ V)
  sub-comp θ (push M N) = push (sub-comp θ M) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
  sub-comp θ (app V W)  = app (sub-val θ V) (sub-val θ W)
  sub-comp θ (pm V M)   = pm (sub-val θ V) (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M)

--------------------------------------------------------------------------
-- weakening

mutual
  wk-val-id : (V : Γ ⊢ᵛ X) → wk-val wk-id V ≡ V
  wk-val-id (var i)    = refl
  wk-val-id (lam M)    = cong lam (wk-comp-id M)
  wk-val-id (pair V W) = cong₂ pair (wk-val-id V) (wk-val-id W)
  wk-val-id (pm V W)   = cong₂ pm (wk-val-id V) (wk-val-id W)
  wk-val-id unit       = refl

  wk-comp-id : (M : Γ ⊢ᶜ X) → wk-comp wk-id M ≡ M
  wk-comp-id (return V) = cong return (wk-val-id V)
  wk-comp-id (push M N) = cong₂ push (wk-comp-id M) (wk-comp-id N)
  wk-comp-id (app V W)  = cong₂ app (wk-val-id V) (wk-val-id W)
  wk-comp-id (pm V M)   = cong₂ pm (wk-val-id V) (wk-comp-id M)

{-# REWRITE wk-val-id wk-comp-id #-}

mutual
  wk-val-trans : (V : Γ ⊢ᵛ X) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → wk-val π (wk-val δ V) ≡ wk-val (wk-trans π δ) V
  wk-val-trans (var i) π δ    = refl
  wk-val-trans (lam M) π δ    = cong lam (wk-comp-trans M (wk-cong π) (wk-cong δ))
  wk-val-trans (pair V W) π δ = cong₂ pair (wk-val-trans V π δ) (wk-val-trans W π δ)
  wk-val-trans (pm V W) π δ   = cong₂ pm (wk-val-trans V π δ) (wk-val-trans W (wk-cong (wk-cong π)) (wk-cong (wk-cong δ)))
  wk-val-trans unit π δ       = refl

  wk-comp-trans : (M : Γ ⊢ᶜ X) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → wk-comp π (wk-comp δ M) ≡ wk-comp (wk-trans π δ) M
  wk-comp-trans (return V) π δ = cong return (wk-val-trans V π δ)
  wk-comp-trans (push M N) π δ = cong₂ push (wk-comp-trans M π δ) (wk-comp-trans N (wk-cong π) (wk-cong δ))
  wk-comp-trans (app V W) π δ  = cong₂ app (wk-val-trans V π δ) (wk-val-trans W π δ)
  wk-comp-trans (pm V M) π δ   = cong₂ pm (wk-val-trans V π δ) (wk-comp-trans M (wk-cong (wk-cong π)) (wk-cong (wk-cong δ)))

{-# REWRITE wk-val-trans wk-comp-trans #-}

--------------------------------------------------------------------------
-- weakening/substitution

sub-wk-id : (θ : Γ ⊢ Δ) → sub-wk wk-id θ ≡ θ
sub-wk-id sub-ε        = refl
sub-wk-id (sub-ex θ V) = cong₂ sub-ex (sub-wk-id θ) refl
{-# REWRITE sub-wk-id #-}

sub-wk-trans : (π : Γ ⊇ Ψ) (δ : Ψ ⊇ Ξ) (θ : Ξ ⊢ Δ)
             → sub-wk π (sub-wk δ θ) ≡ sub-wk (wk-trans π δ) θ
sub-wk-trans π δ sub-ε        = refl
sub-wk-trans π δ (sub-ex θ V) = cong₂ sub-ex (sub-wk-trans π δ θ) refl
{-# REWRITE sub-wk-trans #-}

sub-mem-wk : (π : Γ ⊇ Δ) (θ : Δ ⊢ Ψ) (i : Ψ ∋ X) → sub-mem (sub-wk π θ) i ≡ wk-val π (sub-mem θ i)
sub-mem-wk π (sub-ex θ V) here      = refl
sub-mem-wk π (sub-ex θ V) (there i) = sub-mem-wk π θ i
{-# REWRITE sub-mem-wk #-}

mutual
  wk-sub-val : (π : Ψ ⊇ Γ) (θ : Γ ⊢ Δ) (V : Δ ⊢ᵛ X) → wk-val π (sub-val θ V) ≡ sub-val (sub-wk π θ) V
  wk-sub-val π θ (var i)    = refl
  wk-sub-val π θ (lam M)    = cong lam (wk-sub-comp (wk-cong π) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  wk-sub-val π θ (pair V W) = cong₂ pair (wk-sub-val π θ V) (wk-sub-val π θ W)
  wk-sub-val π θ (pm V W)   =
    cong₂ pm (wk-sub-val π θ V)
             (wk-sub-val (wk-cong (wk-cong π)) (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) W)
  wk-sub-val π θ unit       = refl

  wk-sub-comp : (π : Ψ ⊇ Γ) (θ : Γ ⊢ Δ) (M : Δ ⊢ᶜ X) → wk-comp π (sub-comp θ M) ≡ sub-comp (sub-wk π θ) M
  wk-sub-comp π θ (return V) = cong return (wk-sub-val π θ V)
  wk-sub-comp π θ (push M N) =
    cong₂ push (wk-sub-comp π θ M) (wk-sub-comp (wk-cong π) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
  wk-sub-comp π θ (app V W)  = cong₂ app (wk-sub-val π θ V) (wk-sub-val π θ W)
  wk-sub-comp π θ (pm V M)   =
    cong₂ pm (wk-sub-val π θ V)
             (wk-sub-comp (wk-cong (wk-cong π)) (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M)

{-# REWRITE wk-sub-val wk-sub-comp #-}

--------------------------------------------------------------------------
-- substitution precomposed with weakening

sub-pre : Γ ⊢ Δ → Δ ⊇ Ψ → Γ ⊢ Ψ
sub-pre θ wk-ε              = sub-ε
sub-pre (sub-ex θ V) (wk-cong π) = sub-ex (sub-pre θ π) V
sub-pre (sub-ex θ V) (wk-wk π)   = sub-pre θ π

sub-mem-pre : (θ : Γ ⊢ Δ) (π : Δ ⊇ Ψ) (i : Ψ ∋ X) → sub-mem (sub-pre θ π) i ≡ sub-mem θ (wk-mem π i)
sub-mem-pre (sub-ex θ V) (wk-cong π) here      = refl
sub-mem-pre (sub-ex θ V) (wk-cong π) (there i) = sub-mem-pre θ π i
sub-mem-pre (sub-ex θ V) (wk-wk π) i           = sub-mem-pre θ π i
{-# REWRITE sub-mem-pre #-}

sub-pre-wk-l : (π : Ξ ⊇ Γ) (θ : Γ ⊢ Δ) (δ : Δ ⊇ Ψ) → sub-pre (sub-wk π θ) δ ≡ sub-wk π (sub-pre θ δ)
sub-pre-wk-l π θ wk-ε                   = refl
sub-pre-wk-l π (sub-ex θ V) (wk-cong δ) = cong₂ sub-ex (sub-pre-wk-l π θ δ) refl
sub-pre-wk-l π (sub-ex θ V) (wk-wk δ)   = sub-pre-wk-l π θ δ
{-# REWRITE sub-pre-wk-l #-}

sub-pre-wk-id : (θ : Γ ⊢ Δ) → sub-pre θ (wk-id {Δ}) ≡ θ
sub-pre-wk-id sub-ε        = refl
sub-pre-wk-id (sub-ex θ V) = cong₂ sub-ex (sub-pre-wk-id θ) refl
{-# REWRITE sub-pre-wk-id #-}

sub-pre-trans : (θ : Γ ⊢ Δ) (π : Δ ⊇ Ψ) (δ : Ψ ⊇ Ξ) → sub-pre (sub-pre θ π) δ ≡ sub-pre θ (wk-trans π δ)
sub-pre-trans θ wk-ε wk-ε                          = refl
sub-pre-trans (sub-ex θ V) (wk-cong π) (wk-cong δ) = cong₂ sub-ex (sub-pre-trans θ π δ) refl
sub-pre-trans (sub-ex θ V) (wk-cong π) (wk-wk δ)   = sub-pre-trans θ π δ
sub-pre-trans (sub-ex θ V) (wk-wk π) δ             = sub-pre-trans θ π δ
{-# REWRITE sub-pre-trans #-}

sub-pre-id : (π : Δ ⊇ Γ) → sub-pre (sub-id {Δ}) π ≡ sub-wk π (sub-id {Γ})
sub-pre-id wk-ε        = refl
sub-pre-id (wk-cong π) = cong (λ θ → sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-pre-id π)
sub-pre-id (wk-wk π)   = cong (sub-wk (wk-wk wk-id)) (sub-pre-id π)
{-# REWRITE sub-pre-id #-}

mutual
  sub-val-wk-pre : (θ : Γ ⊢ Ψ) (π : Ψ ⊇ Δ) (V : Δ ⊢ᵛ X) → sub-val θ (wk-val π V) ≡ sub-val (sub-pre θ π) V
  sub-val-wk-pre θ π (var i)    = refl
  sub-val-wk-pre θ π (lam M)    = cong lam (sub-comp-wk-pre (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-cong π) M)
  sub-val-wk-pre θ π (pair V W) = cong₂ pair (sub-val-wk-pre θ π V) (sub-val-wk-pre θ π W)
  sub-val-wk-pre θ π (pm V W)   =
    cong₂ pm (sub-val-wk-pre θ π V)
             (sub-val-wk-pre (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) (wk-cong (wk-cong π)) W)
  sub-val-wk-pre θ π unit       = refl

  sub-comp-wk-pre : (θ : Γ ⊢ Ψ) (π : Ψ ⊇ Δ) (M : Δ ⊢ᶜ X) → sub-comp θ (wk-comp π M) ≡ sub-comp (sub-pre θ π) M
  sub-comp-wk-pre θ π (return V) = cong return (sub-val-wk-pre θ π V)
  sub-comp-wk-pre θ π (push M N) =
    cong₂ push (sub-comp-wk-pre θ π M) (sub-comp-wk-pre (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-cong π) N)
  sub-comp-wk-pre θ π (app V W)  = cong₂ app (sub-val-wk-pre θ π V) (sub-val-wk-pre θ π W)
  sub-comp-wk-pre θ π (pm V M)   =
    cong₂ pm (sub-val-wk-pre θ π V)
             (sub-comp-wk-pre (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) (wk-cong (wk-cong π)) M)

{-# REWRITE sub-val-wk-pre sub-comp-wk-pre #-}

--------------------------------------------------------------------------
-- substitution composition

sub-comp-sub : Γ ⊢ Δ → Δ ⊢ Ψ → Γ ⊢ Ψ
sub-comp-sub θ sub-ε        = sub-ε
sub-comp-sub θ (sub-ex φ V) = sub-ex (sub-comp-sub θ φ) (sub-val θ V)

sub-mem-sub : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) (i : Ψ ∋ X) → sub-mem (sub-comp-sub θ φ) i ≡ sub-val θ (sub-mem φ i)
sub-mem-sub θ (sub-ex φ V) here      = refl
sub-mem-sub θ (sub-ex φ V) (there i) = sub-mem-sub θ φ i
{-# REWRITE sub-mem-sub #-}

sub-comp-sub-wk-r : (θ : Γ ⊢ Ξ) (π : Ξ ⊇ Δ) (φ : Δ ⊢ Ψ) → sub-comp-sub θ (sub-wk π φ) ≡ sub-comp-sub (sub-pre θ π) φ
sub-comp-sub-wk-r θ π sub-ε        = refl
sub-comp-sub-wk-r θ π (sub-ex φ V) = cong₂ sub-ex (sub-comp-sub-wk-r θ π φ) refl
{-# REWRITE sub-comp-sub-wk-r #-}

sub-comp-sub-wk-l : (π : Ξ ⊇ Γ) (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) → sub-comp-sub (sub-wk π θ) φ ≡ sub-wk π (sub-comp-sub θ φ)
sub-comp-sub-wk-l π θ sub-ε        = refl
sub-comp-sub-wk-l π θ (sub-ex φ V) = cong₂ sub-ex (sub-comp-sub-wk-l π θ φ) refl
{-# REWRITE sub-comp-sub-wk-l #-}

sub-pre-comp-sub : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) (π : Ψ ⊇ Ξ) → sub-pre (sub-comp-sub θ φ) π ≡ sub-comp-sub θ (sub-pre φ π)
sub-pre-comp-sub θ φ wk-ε                   = refl
sub-pre-comp-sub θ (sub-ex φ V) (wk-cong π) = cong₂ sub-ex (sub-pre-comp-sub θ φ π) refl
sub-pre-comp-sub θ (sub-ex φ V) (wk-wk π)   = sub-pre-comp-sub θ φ π
{-# REWRITE sub-pre-comp-sub #-}

mutual
  sub-sub-val : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) (V : Ψ ⊢ᵛ X) → sub-val θ (sub-val φ V) ≡ sub-val (sub-comp-sub θ φ) V
  sub-sub-val θ φ (var i)    = refl
  sub-sub-val θ φ (lam M)    =
    cong lam (sub-sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here)) M)
  sub-sub-val θ φ (pair V W) = cong₂ pair (sub-sub-val θ φ V) (sub-sub-val θ φ W)
  sub-sub-val θ φ (pm V W)   =
    cong₂ pm (sub-sub-val θ φ V)
             (sub-sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here))
                          (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) φ) (var (there here))) (var here)) W)
  sub-sub-val θ φ unit       = refl

  sub-sub-comp : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) (M : Ψ ⊢ᶜ X) → sub-comp θ (sub-comp φ M) ≡ sub-comp (sub-comp-sub θ φ) M
  sub-sub-comp θ φ (return V) = cong return (sub-sub-val θ φ V)
  sub-sub-comp θ φ (push M N) =
    cong₂ push (sub-sub-comp θ φ M)
               (sub-sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here)) N)
  sub-sub-comp θ φ (app V W)  = cong₂ app (sub-sub-val θ φ V) (sub-sub-val θ φ W)
  sub-sub-comp θ φ (pm V M)   =
    cong₂ pm (sub-sub-val θ φ V)
             (sub-sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here))
                           (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) φ) (var (there here))) (var here)) M)

{-# REWRITE sub-sub-val sub-sub-comp #-}

sub-comp-sub-assoc : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) (ψ : Ψ ⊢ Ξ)
                   → sub-comp-sub θ (sub-comp-sub φ ψ) ≡ sub-comp-sub (sub-comp-sub θ φ) ψ
sub-comp-sub-assoc θ φ sub-ε        = refl
sub-comp-sub-assoc θ φ (sub-ex ψ V) = cong₂ sub-ex (sub-comp-sub-assoc θ φ ψ) refl
{-# REWRITE sub-comp-sub-assoc #-}

--------------------------------------------------------------------------
-- identity substitution

sub-mem-id : (i : Γ ∋ X) → sub-mem (sub-id {Γ}) i ≡ var i
sub-mem-id here      = refl
sub-mem-id (there i) = cong (wk-val (wk-wk wk-id)) (sub-mem-id i)
{-# REWRITE sub-mem-id #-}

mutual
  sub-val-wk-id : (π : Γ ⊇ Δ) (V : Δ ⊢ᵛ X) → sub-val (sub-wk π sub-id) V ≡ wk-val π V
  sub-val-wk-id π (var i)    = refl
  sub-val-wk-id π (lam M)    = cong lam (sub-comp-wk-id (wk-cong π) M)
  sub-val-wk-id π (pair V W) = cong₂ pair (sub-val-wk-id π V) (sub-val-wk-id π W)
  sub-val-wk-id π (pm V W)   = cong₂ pm (sub-val-wk-id π V) (sub-val-wk-id (wk-cong (wk-cong π)) W)
  sub-val-wk-id π unit       = refl

  sub-comp-wk-id : (π : Γ ⊇ Δ) (M : Δ ⊢ᶜ X) → sub-comp (sub-wk π sub-id) M ≡ wk-comp π M
  sub-comp-wk-id π (return V) = cong return (sub-val-wk-id π V)
  sub-comp-wk-id π (push M N) = cong₂ push (sub-comp-wk-id π M) (sub-comp-wk-id (wk-cong π) N)
  sub-comp-wk-id π (app V W)  = cong₂ app (sub-val-wk-id π V) (sub-val-wk-id π W)
  sub-comp-wk-id π (pm V M)   = cong₂ pm (sub-val-wk-id π V) (sub-comp-wk-id (wk-cong (wk-cong π)) M)

{-# REWRITE sub-val-wk-id sub-comp-wk-id #-}

sub-val-id : (V : Γ ⊢ᵛ X) → sub-val (sub-id {Γ}) V ≡ V
sub-val-id = sub-val-wk-id wk-id

sub-comp-id : (M : Γ ⊢ᶜ X) → sub-comp (sub-id {Γ}) M ≡ M
sub-comp-id = sub-comp-wk-id wk-id

{-# REWRITE sub-val-id sub-comp-id #-}

sub-comp-sub-idl : (θ : Γ ⊢ Δ) → sub-comp-sub sub-id θ ≡ θ
sub-comp-sub-idl sub-ε        = refl
sub-comp-sub-idl (sub-ex θ V) = cong₂ sub-ex (sub-comp-sub-idl θ) refl
{-# REWRITE sub-comp-sub-idl #-}

sub-comp-sub-idr : (θ : Γ ⊢ Δ) → sub-comp-sub θ sub-id ≡ θ
sub-comp-sub-idr sub-ε        = refl
sub-comp-sub-idr (sub-ex θ V) = cong₂ sub-ex (sub-comp-sub-idr θ) refl
{-# REWRITE sub-comp-sub-idr #-}
