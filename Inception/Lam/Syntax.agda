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
  wk-val-id : (V : Γ ⊢ᵛ X) → wk-val wk-id V ≡ V
  wk-val-id (var i) = cong var wk-mem-id
  wk-val-id (lam M) = cong lam (wk-comp-id M)
  wk-val-id unit    = refl

  wk-comp-id : (M : Γ ⊢ᶜ X) → wk-comp wk-id M ≡ M
  wk-comp-id (return V) = cong return (wk-val-id V)
  wk-comp-id (push M N) = cong₂ push (wk-comp-id M) (wk-comp-id N)
  wk-comp-id (app V W)  = cong₂ app (wk-val-id V) (wk-val-id W)

mutual
  wk-val-trans : (V : Γ ⊢ᵛ X) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → wk-val π (wk-val δ V) ≡ wk-val (wk-trans π δ) V
  wk-val-trans (var i) π δ = cong var (wk-mem-trans i π δ)
  wk-val-trans (lam M) π δ = cong lam (wk-comp-trans M (wk-cong π) (wk-cong δ))
  wk-val-trans unit π δ    = refl

  wk-comp-trans : (M : Γ ⊢ᶜ X) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → wk-comp π (wk-comp δ M) ≡ wk-comp (wk-trans π δ) M
  wk-comp-trans (return V) π δ = cong return (wk-val-trans V π δ)
  wk-comp-trans (push M N) π δ = cong₂ push (wk-comp-trans M π δ) (wk-comp-trans N (wk-cong π) (wk-cong δ))
  wk-comp-trans (app V W) π δ  = cong₂ app (wk-val-trans V π δ) (wk-val-trans W π δ)

--------------------------------------------------------------------------
-- weakening/substitution

sub-wk-trans : (π : Γ ⊇ Ψ) (δ : Ψ ⊇ Ξ) (θ : Ξ ⊢ Δ)
             → sub-wk π (sub-wk δ θ) ≡ sub-wk (wk-trans π δ) θ
sub-wk-trans π δ sub-ε        = refl
sub-wk-trans π δ (sub-ex θ V) = cong₂ sub-ex (sub-wk-trans π δ θ) (wk-val-trans V π δ)

sub-wk-wk-wk-id : (θ : Γ ⊢ Δ) → sub-wk (wk-wk {X = X} wk-id) (sub-wk (wk-wk {X = Y} wk-id) θ) ≡ sub-wk (wk-wk {X = X} (wk-wk {X = Y} wk-id)) θ
sub-wk-wk-wk-id θ = begin
  sub-wk (wk-wk wk-id) (sub-wk (wk-wk wk-id) θ)   ≡⟨ sub-wk-trans (wk-wk wk-id) (wk-wk wk-id) θ ⟩
  sub-wk (wk-trans (wk-wk wk-id) (wk-wk wk-id)) θ ≡⟨ cong (λ π → sub-wk π θ) (cong wk-wk (wk-trans-idl (wk-wk wk-id))) ⟩
  sub-wk (wk-wk (wk-wk wk-id)) θ ∎

ren : Γ ⊇ Δ → Γ ⊢ Δ
ren wk-ε        = sub-ε
ren (wk-cong π) = sub-ex (sub-wk (wk-wk wk-id) (ren π)) (var here)
ren (wk-wk π)   = sub-wk (wk-wk wk-id) (ren π)

sub-mem-wk : (π : Γ ⊇ Δ) (θ : Δ ⊢ Ψ) (i : Ψ ∋ X) → sub-mem (sub-wk π θ) i ≡ wk-val π (sub-mem θ i)
sub-mem-wk π (sub-ex θ V) here     = refl
sub-mem-wk π (sub-ex θ V) (there i) = sub-mem-wk π θ i

wk-val-var-wk-wk-id : (i : Γ ∋ X) → wk-val (wk-wk {X = Y} wk-id) (var i) ≡ var (there i)
wk-val-var-wk-wk-id i = cong var (begin
  wk-mem (wk-wk wk-id) i ≡⟨ wk-mem-wk-wk wk-id i ⟩
  there (wk-mem wk-id i)     ≡⟨ cong there wk-mem-id ⟩
  there i                    ∎)

sub-mem-ren : (π : Γ ⊇ Δ) (i : Δ ∋ X) → sub-mem (ren π) i ≡ var (wk-mem π i)
sub-mem-ren (wk-cong π) here     = refl
sub-mem-ren (wk-cong π) (there i) = begin
  sub-mem (sub-wk (wk-wk wk-id) (ren π)) i  ≡⟨ sub-mem-wk (wk-wk wk-id) (ren π) i ⟩
  wk-val (wk-wk wk-id) (sub-mem (ren π) i)  ≡⟨ cong (wk-val (wk-wk wk-id)) (sub-mem-ren π i) ⟩
  wk-val (wk-wk wk-id) (var (wk-mem π i))   ≡⟨ wk-val-var-wk-wk-id (wk-mem π i) ⟩
  var (there (wk-mem π i))                      ∎
sub-mem-ren (wk-wk π) i = begin
  sub-mem (sub-wk (wk-wk wk-id) (ren π)) i  ≡⟨ sub-mem-wk (wk-wk wk-id) (ren π) i ⟩
  wk-val (wk-wk wk-id) (sub-mem (ren π) i)  ≡⟨ cong (wk-val (wk-wk wk-id)) (sub-mem-ren π i) ⟩
  wk-val (wk-wk wk-id) (var (wk-mem π i))   ≡⟨ wk-val-var-wk-wk-id (wk-mem π i) ⟩
  var (there (wk-mem π i))                      ≡˘⟨ cong var (wk-mem-wk-wk π i) ⟩
  var (wk-mem (wk-wk π) i)                  ∎

wk-cong-sub-wk-lemma : (π : Ψ ⊇ Γ) (θ : Γ ⊢ Δ)
                     → sub-wk (wk-cong {X = X} π) (sub-wk (wk-wk wk-id) θ) ≡ sub-wk (wk-wk wk-id) (sub-wk π θ)
wk-cong-sub-wk-lemma π θ = begin
  sub-wk (wk-cong π) (sub-wk (wk-wk wk-id) θ) ≡⟨ sub-wk-trans (wk-cong π) (wk-wk wk-id) θ ⟩
  sub-wk (wk-wk (wk-trans π wk-id)) θ         ≡⟨ cong (λ w → sub-wk w θ) (cong wk-wk (wk-trans-comm-id π)) ⟩
  sub-wk (wk-wk (wk-trans wk-id π)) θ         ≡˘⟨ sub-wk-trans (wk-wk wk-id) π θ ⟩
  sub-wk (wk-wk wk-id) (sub-wk π θ)           ∎

mutual
  wk-sub-val : (π : Ψ ⊇ Γ) (θ : Γ ⊢ Δ) (V : Δ ⊢ᵛ X) → wk-val π (sub-val θ V) ≡ sub-val (sub-wk π θ) V
  wk-sub-val π θ (var i) = sym (sub-mem-wk π θ i)
  wk-sub-val π θ (lam M) =
    cong lam (begin
      wk-comp (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
    ≡⟨ wk-sub-comp (wk-cong π) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M ⟩
      sub-comp (sub-ex (sub-wk (wk-cong π) (sub-wk (wk-wk wk-id) θ)) (var here)) M
    ≡⟨ cong (λ w → sub-comp (sub-ex w (var here)) M) (wk-cong-sub-wk-lemma π θ) ⟩
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-wk π θ)) (var here)) M ∎)
  wk-sub-val π θ unit = refl

  wk-sub-comp : (π : Ψ ⊇ Γ) (θ : Γ ⊢ Δ) (M : Δ ⊢ᶜ X) → wk-comp π (sub-comp θ M) ≡ sub-comp (sub-wk π θ) M
  wk-sub-comp π θ (return V) = cong return (wk-sub-val π θ V)
  wk-sub-comp π θ (push M N) =
    cong₂ push (wk-sub-comp π θ M)
               (begin
                 wk-comp (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
               ≡⟨ wk-sub-comp (wk-cong π) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N ⟩
                 sub-comp (sub-ex (sub-wk (wk-cong π) (sub-wk (wk-wk wk-id) θ)) (var here)) N
               ≡⟨ cong (λ w → sub-comp (sub-ex w (var here)) N) (wk-cong-sub-wk-lemma π θ) ⟩
                 sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-wk π θ)) (var here)) N ∎)
  wk-sub-comp π θ (app V W) = cong₂ app (wk-sub-val π θ V) (wk-sub-val π θ W)

sub-pre : Γ ⊢ Δ → Δ ⊇ Ψ → Γ ⊢ Ψ
sub-pre θ wk-ε              = sub-ε
sub-pre (sub-ex θ V) (wk-cong π) = sub-ex (sub-pre θ π) V
sub-pre (sub-ex θ V) (wk-wk π)   = sub-pre θ π

sub-mem-pre : (θ : Γ ⊢ Δ) (π : Δ ⊇ Ψ) (i : Ψ ∋ X) → sub-mem (sub-pre θ π) i ≡ sub-mem θ (wk-mem π i)
sub-mem-pre (sub-ex θ V) (wk-cong π) here     = refl
sub-mem-pre (sub-ex θ V) (wk-cong π) (there i) = sub-mem-pre θ π i
sub-mem-pre (sub-ex θ V) (wk-wk π) i = begin
  sub-mem (sub-pre θ π) i                    ≡⟨ sub-mem-pre θ π i ⟩
  sub-mem θ (wk-mem π i)                     ≡˘⟨ cong (sub-mem (sub-ex θ V)) (wk-mem-wk-wk π i) ⟩
  sub-mem (sub-ex θ V) (wk-mem (wk-wk π) i)  ∎

sub-pre-wk-l : (π : Ξ ⊇ Γ) (θ : Γ ⊢ Δ) (δ : Δ ⊇ Ψ) → sub-pre (sub-wk π θ) δ ≡ sub-wk π (sub-pre θ δ)
sub-pre-wk-l ρ θ wk-ε              = refl
sub-pre-wk-l π (sub-ex θ V) (wk-cong δ) = cong₂ sub-ex (sub-pre-wk-l π θ δ) refl
sub-pre-wk-l π (sub-ex θ V) (wk-wk δ)   = sub-pre-wk-l π θ δ

sub-pre-wk-id : (θ : Γ ⊢ Δ) → sub-pre θ (wk-id {Δ}) ≡ θ
sub-pre-wk-id sub-ε        = refl
sub-pre-wk-id (sub-ex θ V) = cong (λ w → sub-ex w V) (sub-pre-wk-id θ)

sub-pre-id-ren : (π : Δ ⊇ Γ) → sub-pre (sub-id {Δ}) π ≡ ren π
sub-pre-id-ren wk-ε        = refl
sub-pre-id-ren (wk-cong π) =
  cong (λ w → sub-ex w (var here)) (begin
    sub-pre (sub-wk (wk-wk wk-id) sub-id) π  ≡⟨ sub-pre-wk-l (wk-wk wk-id) sub-id π ⟩
    sub-wk (wk-wk wk-id) (sub-pre sub-id π)  ≡⟨ cong (sub-wk (wk-wk wk-id)) (sub-pre-id-ren π) ⟩
    sub-wk (wk-wk wk-id) (ren π)             ∎)
sub-pre-id-ren (wk-wk π) = begin
  sub-pre (sub-wk (wk-wk wk-id) sub-id) π  ≡⟨ sub-pre-wk-l (wk-wk wk-id) sub-id π ⟩
  sub-wk (wk-wk wk-id) (sub-pre sub-id π)  ≡⟨ cong (sub-wk (wk-wk wk-id)) (sub-pre-id-ren π) ⟩
  sub-wk (wk-wk wk-id) (ren π)             ∎

sub-wk-id-ren : (π : Δ ⊇ Γ) → sub-wk π (sub-id {Γ}) ≡ ren π
sub-wk-id-ren wk-ε        = refl
sub-wk-id-ren (wk-cong π) =
  cong (λ w → sub-ex w (var here)) (begin
    sub-wk (wk-cong π) (sub-wk (wk-wk wk-id) sub-id)  ≡⟨ sub-wk-trans (wk-cong π) (wk-wk wk-id) sub-id ⟩
    sub-wk (wk-wk (wk-trans π wk-id)) sub-id          ≡⟨ cong (λ δ → sub-wk (wk-wk δ) sub-id) (wk-trans-idr π) ⟩
    sub-wk (wk-wk π) sub-id                           ≡˘⟨ cong (λ δ → sub-wk (wk-wk δ) sub-id) (wk-trans-idl π) ⟩
    sub-wk (wk-wk (wk-trans wk-id π)) sub-id          ≡˘⟨ sub-wk-trans (wk-wk wk-id) π sub-id ⟩
    sub-wk (wk-wk wk-id) (sub-wk π sub-id)            ≡⟨ cong (sub-wk (wk-wk wk-id)) (sub-wk-id-ren π) ⟩
    sub-wk (wk-wk wk-id) (ren π)                      ∎)
sub-wk-id-ren (wk-wk π) = begin
  sub-wk (wk-wk π) sub-id                   ≡˘⟨ cong (λ δ → sub-wk (wk-wk δ) sub-id) (wk-trans-idl π) ⟩
  sub-wk (wk-wk (wk-trans wk-id π)) sub-id  ≡˘⟨ sub-wk-trans (wk-wk wk-id) π sub-id ⟩
  sub-wk (wk-wk wk-id) (sub-wk π sub-id)    ≡⟨ cong (sub-wk (wk-wk wk-id)) (sub-wk-id-ren π) ⟩
  sub-wk (wk-wk wk-id) (ren π)              ∎

mutual
  sub-val-wk-pre : (θ : Γ ⊢ Ψ) (π : Ψ ⊇ Δ) (V : Δ ⊢ᵛ X) → sub-val θ (wk-val π V) ≡ sub-val (sub-pre θ π) V
  sub-val-wk-pre θ π (var i) = sym (sub-mem-pre θ π i)
  sub-val-wk-pre θ π (lam M) =
    cong lam (begin
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-comp (wk-cong π) M)
    ≡⟨ sub-comp-wk-pre (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-cong π) M ⟩
      sub-comp (sub-ex (sub-pre (sub-wk (wk-wk wk-id) θ) π) (var here)) M
    ≡⟨ cong (λ w → sub-comp (sub-ex w (var here)) M) (sub-pre-wk-l (wk-wk wk-id) θ π) ⟩
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-pre θ π)) (var here)) M ∎)
  sub-val-wk-pre θ π unit = refl

  sub-comp-wk-pre : (θ : Γ ⊢ Ψ) (π : Ψ ⊇ Δ) (M : Δ ⊢ᶜ X) → sub-comp θ (wk-comp π M) ≡ sub-comp (sub-pre θ π) M
  sub-comp-wk-pre θ π (return V) = cong return (sub-val-wk-pre θ π V)
  sub-comp-wk-pre θ π (push M N) =
    cong₂ push (sub-comp-wk-pre θ π M)
               (begin
                 sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-comp (wk-cong π) N)
               ≡⟨ sub-comp-wk-pre (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-cong π) N ⟩
                 sub-comp (sub-ex (sub-pre (sub-wk (wk-wk wk-id) θ) π) (var here)) N
               ≡⟨ cong (λ w → sub-comp (sub-ex w (var here)) N) (sub-pre-wk-l (wk-wk wk-id) θ π) ⟩
                 sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-pre θ π)) (var here)) N ∎)
  sub-comp-wk-pre θ π (app V W) = cong₂ app (sub-val-wk-pre θ π V) (sub-val-wk-pre θ π W)

wk-beta-1 : (π : Δ ⊇ Γ) (V : Γ ⊢ᵛ X) (M : (Γ ∙ X) ⊢ᶜ Y)
  → sub-comp (sub-ex sub-id (wk-val π V)) (wk-comp (wk-cong π) M) ≡ wk-comp π (sub-comp (sub-ex sub-id V) M)
wk-beta-1 π V M = begin
    sub-comp (sub-ex sub-id (wk-val π V)) (wk-comp (wk-cong π) M)
  ≡⟨ sub-comp-wk-pre (sub-ex sub-id (wk-val π V)) (wk-cong π) M ⟩
    sub-comp (sub-ex (sub-pre sub-id π) (wk-val π V)) M
  ≡⟨ cong (λ z → sub-comp (sub-ex z (wk-val π V)) M) (sub-pre-id-ren π) ⟩
    sub-comp (sub-ex (ren π) (wk-val π V)) M
  ≡˘⟨ cong (λ z → sub-comp (sub-ex z (wk-val π V)) M) (sub-wk-id-ren π) ⟩
    sub-comp (sub-ex (sub-wk π sub-id) (wk-val π V)) M
  ≡˘⟨ wk-sub-comp π (sub-ex sub-id V) M ⟩
    wk-comp π (sub-comp (sub-ex sub-id V) M) ∎

--------------------------------------------------------------------------
-- substitution composition

sub-comp-sub : Γ ⊢ Δ → Δ ⊢ Ψ → Γ ⊢ Ψ
sub-comp-sub θ sub-ε        = sub-ε
sub-comp-sub θ (sub-ex φ V) = sub-ex (sub-comp-sub θ φ) (sub-val θ V)

sub-mem-sub : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) (i : Ψ ∋ X) → sub-mem (sub-comp-sub θ φ) i ≡ sub-val θ (sub-mem φ i)
sub-mem-sub θ (sub-ex φ V) here     = refl
sub-mem-sub θ (sub-ex φ V) (there i) = sub-mem-sub θ φ i

sub-comp-sub-wk-r : (θ : Γ ⊢ Ξ) (π : Ξ ⊇ Δ) (φ : Δ ⊢ Ψ) → sub-comp-sub θ (sub-wk π φ) ≡ sub-comp-sub (sub-pre θ π) φ
sub-comp-sub-wk-r θ π sub-ε        = refl
sub-comp-sub-wk-r θ π (sub-ex φ V) = cong₂ sub-ex (sub-comp-sub-wk-r θ π φ) (sub-val-wk-pre θ π V)

sub-comp-sub-wk-l : (ρ : Ξ ⊇ Γ) (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) → sub-comp-sub (sub-wk ρ θ) φ ≡ sub-wk ρ (sub-comp-sub θ φ)
sub-comp-sub-wk-l ρ θ sub-ε        = refl
sub-comp-sub-wk-l ρ θ (sub-ex φ V) = cong₂ sub-ex (sub-comp-sub-wk-l ρ θ φ) (sym (wk-sub-val ρ θ V))

sub-comp-sub-ext1 : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ)
  → sub-comp-sub (sub-ex (sub-wk (wk-wk {X = X} wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here))
   ≡ sub-ex (sub-wk (wk-wk wk-id) (sub-comp-sub θ φ)) (var here)
sub-comp-sub-ext1 θ φ =
  cong₂ sub-ex
    (begin
      sub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-wk (wk-wk wk-id) φ)
    ≡⟨ sub-comp-sub-wk-r (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-wk wk-id) φ ⟩
      sub-comp-sub (sub-pre (sub-wk (wk-wk wk-id) θ) wk-id) φ
    ≡⟨ cong (λ w → sub-comp-sub w φ) (sub-pre-wk-id (sub-wk (wk-wk wk-id) θ)) ⟩
      sub-comp-sub (sub-wk (wk-wk wk-id) θ) φ
    ≡⟨ sub-comp-sub-wk-l (wk-wk wk-id) θ φ ⟩
      sub-wk (wk-wk wk-id) (sub-comp-sub θ φ) ∎)
    refl

mutual
  sub-sub-val : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) (V : Ψ ⊢ᵛ X) → sub-val θ (sub-val φ V) ≡ sub-val (sub-comp-sub θ φ) V
  sub-sub-val θ φ (var i) = sym (sub-mem-sub θ φ i)
  sub-sub-val θ φ (lam M) =
    cong lam (begin
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) φ) (var here)) M)
    ≡⟨ sub-sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here)) M ⟩
      sub-comp (sub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here))) M
    ≡⟨ cong (λ w → sub-comp w M) (sub-comp-sub-ext1 θ φ) ⟩
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-comp-sub θ φ)) (var here)) M ∎)
  sub-sub-val θ φ unit = refl

  sub-sub-comp : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) (M : Ψ ⊢ᶜ X) → sub-comp θ (sub-comp φ M) ≡ sub-comp (sub-comp-sub θ φ) M
  sub-sub-comp θ φ (return V) = cong return (sub-sub-val θ φ V)
  sub-sub-comp θ φ (push M N) =
    cong₂ push (sub-sub-comp θ φ M)
               (begin
                 sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) φ) (var here)) N)
               ≡⟨ sub-sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here)) N ⟩
                 sub-comp (sub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here))) N
               ≡⟨ cong (λ w → sub-comp w N) (sub-comp-sub-ext1 θ φ) ⟩
                 sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-comp-sub θ φ)) (var here)) N ∎)
  sub-sub-comp θ φ (app V W) = cong₂ app (sub-sub-val θ φ V) (sub-sub-val θ φ W)

mutual
  sub-val-ren : (π : Γ ⊇ Δ) (V : Δ ⊢ᵛ X) → sub-val (ren π) V ≡ wk-val π V
  sub-val-ren π (var i) = sub-mem-ren π i
  sub-val-ren π (lam M) = cong lam (sub-comp-ren (wk-cong π) M)
  sub-val-ren π unit    = refl

  sub-comp-ren : (π : Γ ⊇ Δ) (M : Δ ⊢ᶜ X) → sub-comp (ren π) M ≡ wk-comp π M
  sub-comp-ren π (return V) = cong return (sub-val-ren π V)
  sub-comp-ren π (push M N) = cong₂ push (sub-comp-ren π M) (sub-comp-ren (wk-cong π) N)
  sub-comp-ren π (app V W)  = cong₂ app (sub-val-ren π V) (sub-val-ren π W)

ren-wk-id : ren (wk-id {Γ}) ≡ sub-id {Γ}
ren-wk-id {ε}     = refl
ren-wk-id {Γ ∙ X} = cong (λ θ → sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (ren-wk-id {Γ})

sub-mem-id : (i : Γ ∋ X) → sub-mem (sub-id {Γ}) i ≡ var i
sub-mem-id {Γ} i = begin
  sub-mem (sub-id {Γ}) i  ≡˘⟨ cong (λ θ → sub-mem θ i) (ren-wk-id {Γ}) ⟩
  sub-mem (ren wk-id) i   ≡⟨ sub-mem-ren wk-id i ⟩
  var (wk-mem wk-id i)    ≡⟨ cong var wk-mem-id ⟩
  var i                   ∎

sub-val-id : (V : Γ ⊢ᵛ X) → sub-val (sub-id {Γ}) V ≡ V
sub-val-id {Γ} V = begin
  sub-val (sub-id {Γ}) V  ≡˘⟨ cong (λ θ → sub-val θ V) (ren-wk-id {Γ}) ⟩
  sub-val (ren wk-id) V   ≡⟨ sub-val-ren wk-id V ⟩
  wk-val wk-id V          ≡⟨ wk-val-id V ⟩
  V                       ∎

sub-comp-id : (M : Γ ⊢ᶜ X) → sub-comp (sub-id {Γ}) M ≡ M
sub-comp-id {Γ} M = begin
  sub-comp (sub-id {Γ}) M  ≡˘⟨ cong (λ θ → sub-comp θ M) (ren-wk-id {Γ}) ⟩
  sub-comp (ren wk-id) M   ≡⟨ sub-comp-ren wk-id M ⟩
  wk-comp wk-id M          ≡⟨ wk-comp-id M ⟩
  M                        ∎

sub-comp-sub-idl : (θ : Γ ⊢ Δ) → sub-comp-sub sub-id θ ≡ θ
sub-comp-sub-idl sub-ε        = refl
sub-comp-sub-idl (sub-ex θ V) = cong₂ sub-ex (sub-comp-sub-idl θ) (sub-val-id V)

sub-wk-as-comp-ren : (π : Ψ ⊇ Γ) (θ : Γ ⊢ Δ) → sub-wk π θ ≡ sub-comp-sub (ren π) θ
sub-wk-as-comp-ren π sub-ε        = refl
sub-wk-as-comp-ren π (sub-ex θ V) = cong₂ sub-ex (sub-wk-as-comp-ren π θ) (sym (sub-val-ren π V))

--------------------------------------------------------------------------
-- fundamental lemma

fund-lam-eq : (θ : Γ ⊢ Δ) (π : Ψ ⊇ Γ) (W : Ψ ⊢ᵛ X) (M : (Δ ∙ X) ⊢ᶜ Y)
  → sub-comp (sub-ex sub-id W) (wk-comp (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M))
   ≡ sub-comp (sub-ex (sub-wk π θ) W) M
fund-lam-eq θ π W M = begin
    sub-comp (sub-ex sub-id W) (wk-comp (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M))
  ≡⟨ sub-comp-wk-pre (sub-ex sub-id W) (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M) ⟩
    sub-comp (sub-ex (sub-pre sub-id π) W) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  ≡⟨ cong (λ ξ → sub-comp (sub-ex ξ W) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)) (sub-pre-id-ren π) ⟩
    sub-comp (sub-ex (ren π) W) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  ≡⟨ sub-sub-comp (sub-ex (ren π) W) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M ⟩
    sub-comp (sub-ex (sub-comp-sub (sub-ex (ren π) W) (sub-wk (wk-wk wk-id) θ)) W) M
  ≡⟨ cong (λ ξ → sub-comp (sub-ex ξ W) M)
          (begin
             sub-comp-sub (sub-ex (ren π) W) (sub-wk (wk-wk wk-id) θ)
           ≡⟨ sub-comp-sub-wk-r (sub-ex (ren π) W) (wk-wk wk-id) θ ⟩
             sub-comp-sub (sub-pre (ren π) wk-id) θ
           ≡⟨ cong (λ δ → sub-comp-sub δ θ) (sub-pre-wk-id (ren π)) ⟩
             sub-comp-sub (ren π) θ
           ≡˘⟨ sub-wk-as-comp-ren π θ ⟩
             sub-wk π θ ∎) ⟩
    sub-comp (sub-ex (sub-wk π θ) W) M ∎

fund-push-eq : (θ : Γ ⊢ Δ) (V : Γ ⊢ᵛ X) (N : (Δ ∙ X) ⊢ᶜ Y)
  → sub-comp (sub-ex sub-id V) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
   ≡ sub-comp (sub-ex θ V) N
fund-push-eq θ V N = begin
    sub-comp (sub-ex sub-id V) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
  ≡⟨ sub-sub-comp (sub-ex sub-id V) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N ⟩
    sub-comp (sub-ex (sub-comp-sub (sub-ex sub-id V) (sub-wk (wk-wk wk-id) θ)) V) N
  ≡⟨ cong (λ ξ → sub-comp (sub-ex ξ V) N)
          (begin
             sub-comp-sub (sub-ex sub-id V) (sub-wk (wk-wk wk-id) θ)
           ≡⟨ sub-comp-sub-wk-r (sub-ex sub-id V) (wk-wk wk-id) θ ⟩
             sub-comp-sub (sub-pre sub-id wk-id) θ
           ≡⟨ cong (λ ρ → sub-comp-sub ρ θ) (sub-pre-wk-id sub-id) ⟩
             sub-comp-sub sub-id θ
           ≡⟨ sub-comp-sub-idl θ ⟩
             θ ∎) ⟩
    sub-comp (sub-ex θ V) N ∎
