{-# OPTIONS --no-postfix-projections #-}

module Inception.Lam.Syntax where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; cong₂; sym)
open Eq.≡-Reasoning

--------------------------------------------------------------------------
-- types and contexts

infixr 25 _`⇒_

data Ty : Set where
  `Unit : Ty
  _`⇒_  : Ty -> Ty -> Ty

open import Inception.Ctx Ty public

--------------------------------------------------------------------------
-- values and computations

syntax Val Γ A = Γ ⊢ᵛ A
data Val : Ctx -> Ty -> Set

syntax Comp Γ A = Γ ⊢ᶜ A
data Comp : Ctx -> Ty -> Set

data Val where
  var  : (i : Γ ∋ A) -> Γ ⊢ᵛ A
  lam  : (Γ ∙ A) ⊢ᶜ B -> Γ ⊢ᵛ A `⇒ B
  unit : Γ ⊢ᵛ `Unit

data Comp where
  return : Γ ⊢ᵛ A -> Γ ⊢ᶜ A
  push   : Γ ⊢ᶜ A -> (Γ ∙ A) ⊢ᶜ B -> Γ ⊢ᶜ B
  app    : Γ ⊢ᵛ A `⇒ B -> Γ ⊢ᵛ A -> Γ ⊢ᶜ B

--------------------------------------------------------------------------
-- weakenings

mutual
  wk-val : Γ ⊇ Δ -> Δ ⊢ᵛ A -> Γ ⊢ᵛ A
  wk-val π (var i)      = var (wk-mem π i)
  wk-val π (lam M)      = lam (wk-comp (wk-cong π) M)
  wk-val π unit         = unit

  wk-comp : Γ ⊇ Δ -> Δ ⊢ᶜ A -> Γ ⊢ᶜ A
  wk-comp π (return V) = return (wk-val π V)
  wk-comp π (push M N) = push (wk-comp π M) (wk-comp (wk-cong π) N)
  wk-comp π (app V W)  = app (wk-val π V) (wk-val π W)

wk : Γ ⊢ᵛ A -> (Γ ∙ B) ⊢ᵛ A
wk = wk-val (wk-wk wk-id)

--------------------------------------------------------------------------
-- substitutions

syntax Sub Γ Δ = Γ ⊢ Δ
data Sub (Γ : Ctx) : (Δ : Ctx) -> Set where
  sub-ε  : Γ ⊢ ε
  sub-ex : (θ : Γ ⊢ Δ) -> (V : Γ ⊢ᵛ A) -> Γ ⊢ (Δ ∙ A)

sub-mem : Γ ⊢ Δ -> Δ ∋ A -> Γ ⊢ᵛ A
sub-mem (sub-ex θ V) here     = V
sub-mem (sub-ex θ V) (there i) = sub-mem θ i

sub-wk : Γ ⊇ Δ -> Δ ⊢ Ψ -> Γ ⊢ Ψ
sub-wk π sub-ε        = sub-ε
sub-wk π (sub-ex θ V) = sub-ex (sub-wk π θ) (wk-val π V)

sub-id : Γ ⊢ Γ
sub-id {Γ = ε}     = sub-ε
sub-id {Γ = Γ ∙ A} = sub-ex (sub-wk (wk-wk wk-id) sub-id) (var here)

mutual
  sub-val : Γ ⊢ Δ -> Δ ⊢ᵛ A -> Γ ⊢ᵛ A
  sub-val θ (var i)      = sub-mem θ i
  sub-val θ (lam M)      = lam (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  sub-val θ unit         = unit

  sub-comp : Γ ⊢ Δ -> Δ ⊢ᶜ A -> Γ ⊢ᶜ A
  sub-comp θ (return V) = return (sub-val θ V)
  sub-comp θ (push M N) = push (sub-comp θ M) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
  sub-comp θ (app V W)  = app (sub-val θ V) (sub-val θ W)

variable
  x : Γ ∋ A
  V V₁ V₂ V₃ : Γ ⊢ᵛ A
  W W₁ W₂ W₃ : Γ ⊢ᵛ A
  M M₁ M₂ M₃ : Γ ⊢ᶜ A
  N N₁ N₂ N₃ : Γ ⊢ᶜ A

--------------------------------------------------------------------------
-- weakening

mutual
  wk-val-id : (V : Γ ⊢ᵛ A) → wk-val wk-id V ≡ V
  wk-val-id (var i) = cong var wk-mem-id
  wk-val-id (lam M) = cong lam (wk-comp-id M)
  wk-val-id unit    = refl

  wk-comp-id : (M : Γ ⊢ᶜ A) → wk-comp wk-id M ≡ M
  wk-comp-id (return V) = cong return (wk-val-id V)
  wk-comp-id (push M N) = cong₂ push (wk-comp-id M) (wk-comp-id N)
  wk-comp-id (app V W)  = cong₂ app (wk-val-id V) (wk-val-id W)

mutual
  wk-val-trans : (V : Γ ⊢ᵛ A) → (π₁ : Ψ ⊇ Δ) → (π₂ : Δ ⊇ Γ) → wk-val π₁ (wk-val π₂ V) ≡ wk-val (wk-trans π₁ π₂) V
  wk-val-trans (var i) π₁ π₂ = cong var (wk-mem-trans i π₁ π₂)
  wk-val-trans (lam M) π₁ π₂ = cong lam (wk-comp-trans M (wk-cong π₁) (wk-cong π₂))
  wk-val-trans unit π₁ π₂    = refl

  wk-comp-trans : (M : Γ ⊢ᶜ A) → (π₁ : Ψ ⊇ Δ) → (π₂ : Δ ⊇ Γ) → wk-comp π₁ (wk-comp π₂ M) ≡ wk-comp (wk-trans π₁ π₂) M
  wk-comp-trans (return V) π₁ π₂ = cong return (wk-val-trans V π₁ π₂)
  wk-comp-trans (push M N) π₁ π₂ = cong₂ push (wk-comp-trans M π₁ π₂) (wk-comp-trans N (wk-cong π₁) (wk-cong π₂))
  wk-comp-trans (app V W) π₁ π₂  = cong₂ app (wk-val-trans V π₁ π₂) (wk-val-trans W π₁ π₂)

--------------------------------------------------------------------------
-- weakening/substitution

sub-wk-trans : (π₁ : Γ ⊇ Γ') (π₂ : Γ' ⊇ Γ'') (θ : Γ'' ⊢ Δ)
             -> sub-wk π₁ (sub-wk π₂ θ) ≡ sub-wk (wk-trans π₁ π₂) θ
sub-wk-trans π₁ π₂ sub-ε        = refl
sub-wk-trans π₁ π₂ (sub-ex θ V) = cong₂ sub-ex (sub-wk-trans π₁ π₂ θ) (wk-val-trans V π₁ π₂)

sub-wk-wk-wk-id : (θ : Γ ⊢ Δ) -> sub-wk (wk-wk {A = A} wk-id) (sub-wk (wk-wk {A = B} wk-id) θ) ≡ sub-wk (wk-wk {A = A} (wk-wk {A = B} wk-id)) θ
sub-wk-wk-wk-id θ = begin
  sub-wk (wk-wk wk-id) (sub-wk (wk-wk wk-id) θ)   ≡⟨ sub-wk-trans (wk-wk wk-id) (wk-wk wk-id) θ ⟩
  sub-wk (wk-trans (wk-wk wk-id) (wk-wk wk-id)) θ ≡⟨ cong (λ π -> sub-wk π θ) (cong wk-wk (wk-trans-idl (wk-wk wk-id))) ⟩
  sub-wk (wk-wk (wk-wk wk-id)) θ ∎

ren : Γ ⊇ Δ -> Γ ⊢ Δ
ren wk-ε        = sub-ε
ren (wk-cong π) = sub-ex (sub-wk (wk-wk wk-id) (ren π)) (var here)
ren (wk-wk π)   = sub-wk (wk-wk wk-id) (ren π)

sub-mem-wk : (π : Γ ⊇ Δ) (θ : Δ ⊢ Ψ) (i : Ψ ∋ A) -> sub-mem (sub-wk π θ) i ≡ wk-val π (sub-mem θ i)
sub-mem-wk π (sub-ex θ V) here     = refl
sub-mem-wk π (sub-ex θ V) (there i) = sub-mem-wk π θ i

wk-val-var-wk-wk-id : (i : Γ ∋ A) -> wk-val (wk-wk {A = B} wk-id) (var i) ≡ var (there i)
wk-val-var-wk-wk-id i = cong var (begin
  wk-mem (wk-wk wk-id) i ≡⟨ wk-mem-wk-wk wk-id i ⟩
  there (wk-mem wk-id i)     ≡⟨ cong there wk-mem-id ⟩
  there i                    ∎)

sub-mem-ren : (π : Γ ⊇ Δ) (i : Δ ∋ A) -> sub-mem (ren π) i ≡ var (wk-mem π i)
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

wk-cong-sub-wk-lemma : (π : Γ' ⊇ Γ) (θ : Γ ⊢ Δ)
                     -> sub-wk (wk-cong {A = A} π) (sub-wk (wk-wk wk-id) θ) ≡ sub-wk (wk-wk wk-id) (sub-wk π θ)
wk-cong-sub-wk-lemma π θ = begin
  sub-wk (wk-cong π) (sub-wk (wk-wk wk-id) θ) ≡⟨ sub-wk-trans (wk-cong π) (wk-wk wk-id) θ ⟩
  sub-wk (wk-wk (wk-trans π wk-id)) θ         ≡⟨ cong (λ w -> sub-wk w θ) (cong wk-wk (wk-trans-comm-id π)) ⟩
  sub-wk (wk-wk (wk-trans wk-id π)) θ         ≡˘⟨ sub-wk-trans (wk-wk wk-id) π θ ⟩
  sub-wk (wk-wk wk-id) (sub-wk π θ)           ∎

mutual
  wk-sub-val : (π : Γ' ⊇ Γ) (θ : Γ ⊢ Δ) (V : Δ ⊢ᵛ A) -> wk-val π (sub-val θ V) ≡ sub-val (sub-wk π θ) V
  wk-sub-val π θ (var i) = sym (sub-mem-wk π θ i)
  wk-sub-val π θ (lam M) =
    cong lam (begin
      wk-comp (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
    ≡⟨ wk-sub-comp (wk-cong π) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M ⟩
      sub-comp (sub-ex (sub-wk (wk-cong π) (sub-wk (wk-wk wk-id) θ)) (var here)) M
    ≡⟨ cong (λ w -> sub-comp (sub-ex w (var here)) M) (wk-cong-sub-wk-lemma π θ) ⟩
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-wk π θ)) (var here)) M ∎)
  wk-sub-val π θ unit = refl

  wk-sub-comp : (π : Γ' ⊇ Γ) (θ : Γ ⊢ Δ) (M : Δ ⊢ᶜ A) -> wk-comp π (sub-comp θ M) ≡ sub-comp (sub-wk π θ) M
  wk-sub-comp π θ (return V) = cong return (wk-sub-val π θ V)
  wk-sub-comp π θ (push M N) =
    cong₂ push (wk-sub-comp π θ M)
               (begin
                 wk-comp (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
               ≡⟨ wk-sub-comp (wk-cong π) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N ⟩
                 sub-comp (sub-ex (sub-wk (wk-cong π) (sub-wk (wk-wk wk-id) θ)) (var here)) N
               ≡⟨ cong (λ w -> sub-comp (sub-ex w (var here)) N) (wk-cong-sub-wk-lemma π θ) ⟩
                 sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-wk π θ)) (var here)) N ∎)
  wk-sub-comp π θ (app V W) = cong₂ app (wk-sub-val π θ V) (wk-sub-val π θ W)

sub-pre : Γ ⊢ Δ -> Δ ⊇ Ψ -> Γ ⊢ Ψ
sub-pre θ wk-ε              = sub-ε
sub-pre (sub-ex θ V) (wk-cong π) = sub-ex (sub-pre θ π) V
sub-pre (sub-ex θ V) (wk-wk π)   = sub-pre θ π

sub-mem-pre : (θ : Γ ⊢ Δ) (π : Δ ⊇ Ψ) (i : Ψ ∋ A) -> sub-mem (sub-pre θ π) i ≡ sub-mem θ (wk-mem π i)
sub-mem-pre (sub-ex θ V) (wk-cong π) here     = refl
sub-mem-pre (sub-ex θ V) (wk-cong π) (there i) = sub-mem-pre θ π i
sub-mem-pre (sub-ex θ V) (wk-wk π) i = begin
  sub-mem (sub-pre θ π) i                    ≡⟨ sub-mem-pre θ π i ⟩
  sub-mem θ (wk-mem π i)                     ≡˘⟨ cong (sub-mem (sub-ex θ V)) (wk-mem-wk-wk π i) ⟩
  sub-mem (sub-ex θ V) (wk-mem (wk-wk π) i)  ∎

sub-pre-wk-l : (ρ : Γ' ⊇ Γ) (θ : Γ ⊢ Δ) (π : Δ ⊇ Ψ) -> sub-pre (sub-wk ρ θ) π ≡ sub-wk ρ (sub-pre θ π)
sub-pre-wk-l ρ θ wk-ε              = refl
sub-pre-wk-l ρ (sub-ex θ V) (wk-cong π) = cong₂ sub-ex (sub-pre-wk-l ρ θ π) refl
sub-pre-wk-l ρ (sub-ex θ V) (wk-wk π)   = sub-pre-wk-l ρ θ π

sub-pre-wk-id : (θ : Γ ⊢ Δ) -> sub-pre θ (wk-id {Δ}) ≡ θ
sub-pre-wk-id sub-ε        = refl
sub-pre-wk-id (sub-ex θ V) = cong (λ w -> sub-ex w V) (sub-pre-wk-id θ)

sub-pre-id-ren : (π : Γ' ⊇ Γ) -> sub-pre (sub-id {Γ'}) π ≡ ren π
sub-pre-id-ren wk-ε        = refl
sub-pre-id-ren (wk-cong π) =
  cong (λ w -> sub-ex w (var here)) (begin
    sub-pre (sub-wk (wk-wk wk-id) sub-id) π  ≡⟨ sub-pre-wk-l (wk-wk wk-id) sub-id π ⟩
    sub-wk (wk-wk wk-id) (sub-pre sub-id π)  ≡⟨ cong (sub-wk (wk-wk wk-id)) (sub-pre-id-ren π) ⟩
    sub-wk (wk-wk wk-id) (ren π)             ∎)
sub-pre-id-ren (wk-wk π) = begin
  sub-pre (sub-wk (wk-wk wk-id) sub-id) π  ≡⟨ sub-pre-wk-l (wk-wk wk-id) sub-id π ⟩
  sub-wk (wk-wk wk-id) (sub-pre sub-id π)  ≡⟨ cong (sub-wk (wk-wk wk-id)) (sub-pre-id-ren π) ⟩
  sub-wk (wk-wk wk-id) (ren π)             ∎

sub-wk-id-ren : (π : Γ' ⊇ Γ) -> sub-wk π (sub-id {Γ}) ≡ ren π
sub-wk-id-ren wk-ε        = refl
sub-wk-id-ren (wk-cong π) =
  cong (λ w -> sub-ex w (var here)) (begin
    sub-wk (wk-cong π) (sub-wk (wk-wk wk-id) sub-id)  ≡⟨ sub-wk-trans (wk-cong π) (wk-wk wk-id) sub-id ⟩
    sub-wk (wk-wk (wk-trans π wk-id)) sub-id          ≡⟨ cong (λ ρ -> sub-wk (wk-wk ρ) sub-id) (wk-trans-idr π) ⟩
    sub-wk (wk-wk π) sub-id                           ≡˘⟨ cong (λ ρ -> sub-wk (wk-wk ρ) sub-id) (wk-trans-idl π) ⟩
    sub-wk (wk-wk (wk-trans wk-id π)) sub-id          ≡˘⟨ sub-wk-trans (wk-wk wk-id) π sub-id ⟩
    sub-wk (wk-wk wk-id) (sub-wk π sub-id)            ≡⟨ cong (sub-wk (wk-wk wk-id)) (sub-wk-id-ren π) ⟩
    sub-wk (wk-wk wk-id) (ren π)                      ∎)
sub-wk-id-ren (wk-wk π) = begin
  sub-wk (wk-wk π) sub-id                   ≡˘⟨ cong (λ ρ -> sub-wk (wk-wk ρ) sub-id) (wk-trans-idl π) ⟩
  sub-wk (wk-wk (wk-trans wk-id π)) sub-id  ≡˘⟨ sub-wk-trans (wk-wk wk-id) π sub-id ⟩
  sub-wk (wk-wk wk-id) (sub-wk π sub-id)    ≡⟨ cong (sub-wk (wk-wk wk-id)) (sub-wk-id-ren π) ⟩
  sub-wk (wk-wk wk-id) (ren π)              ∎

mutual
  sub-val-wk-pre : (θ : Γ ⊢ Δ') (π : Δ' ⊇ Δ) (V : Δ ⊢ᵛ A) -> sub-val θ (wk-val π V) ≡ sub-val (sub-pre θ π) V
  sub-val-wk-pre θ π (var i) = sym (sub-mem-pre θ π i)
  sub-val-wk-pre θ π (lam M) =
    cong lam (begin
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-comp (wk-cong π) M)
    ≡⟨ sub-comp-wk-pre (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-cong π) M ⟩
      sub-comp (sub-ex (sub-pre (sub-wk (wk-wk wk-id) θ) π) (var here)) M
    ≡⟨ cong (λ w -> sub-comp (sub-ex w (var here)) M) (sub-pre-wk-l (wk-wk wk-id) θ π) ⟩
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-pre θ π)) (var here)) M ∎)
  sub-val-wk-pre θ π unit = refl

  sub-comp-wk-pre : (θ : Γ ⊢ Δ') (π : Δ' ⊇ Δ) (M : Δ ⊢ᶜ A) -> sub-comp θ (wk-comp π M) ≡ sub-comp (sub-pre θ π) M
  sub-comp-wk-pre θ π (return V) = cong return (sub-val-wk-pre θ π V)
  sub-comp-wk-pre θ π (push M N) =
    cong₂ push (sub-comp-wk-pre θ π M)
               (begin
                 sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-comp (wk-cong π) N)
               ≡⟨ sub-comp-wk-pre (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-cong π) N ⟩
                 sub-comp (sub-ex (sub-pre (sub-wk (wk-wk wk-id) θ) π) (var here)) N
               ≡⟨ cong (λ w -> sub-comp (sub-ex w (var here)) N) (sub-pre-wk-l (wk-wk wk-id) θ π) ⟩
                 sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-pre θ π)) (var here)) N ∎)
  sub-comp-wk-pre θ π (app V W) = cong₂ app (sub-val-wk-pre θ π V) (sub-val-wk-pre θ π W)

wk-beta-1 : (π : Γ' ⊇ Γ) (V : Γ ⊢ᵛ A) (M : (Γ ∙ A) ⊢ᶜ B)
  -> sub-comp (sub-ex sub-id (wk-val π V)) (wk-comp (wk-cong π) M) ≡ wk-comp π (sub-comp (sub-ex sub-id V) M)
wk-beta-1 π V M = begin
    sub-comp (sub-ex sub-id (wk-val π V)) (wk-comp (wk-cong π) M)
  ≡⟨ sub-comp-wk-pre (sub-ex sub-id (wk-val π V)) (wk-cong π) M ⟩
    sub-comp (sub-ex (sub-pre sub-id π) (wk-val π V)) M
  ≡⟨ cong (λ z -> sub-comp (sub-ex z (wk-val π V)) M) (sub-pre-id-ren π) ⟩
    sub-comp (sub-ex (ren π) (wk-val π V)) M
  ≡˘⟨ cong (λ z -> sub-comp (sub-ex z (wk-val π V)) M) (sub-wk-id-ren π) ⟩
    sub-comp (sub-ex (sub-wk π sub-id) (wk-val π V)) M
  ≡˘⟨ wk-sub-comp π (sub-ex sub-id V) M ⟩
    wk-comp π (sub-comp (sub-ex sub-id V) M) ∎

--------------------------------------------------------------------------
-- substitution composition

sub-comp-sub : Γ ⊢ Δ -> Δ ⊢ Ψ -> Γ ⊢ Ψ
sub-comp-sub θ₁ sub-ε        = sub-ε
sub-comp-sub θ₁ (sub-ex θ₂ V) = sub-ex (sub-comp-sub θ₁ θ₂) (sub-val θ₁ V)

sub-mem-sub : (θ₁ : Γ ⊢ Δ) (θ₂ : Δ ⊢ Ψ) (i : Ψ ∋ A) -> sub-mem (sub-comp-sub θ₁ θ₂) i ≡ sub-val θ₁ (sub-mem θ₂ i)
sub-mem-sub θ₁ (sub-ex θ₂ V) here     = refl
sub-mem-sub θ₁ (sub-ex θ₂ V) (there i) = sub-mem-sub θ₁ θ₂ i

sub-comp-sub-wk-r : (θ₁ : Γ ⊢ Δ') (π : Δ' ⊇ Δ) (θ₂ : Δ ⊢ Ψ) -> sub-comp-sub θ₁ (sub-wk π θ₂) ≡ sub-comp-sub (sub-pre θ₁ π) θ₂
sub-comp-sub-wk-r θ₁ π sub-ε        = refl
sub-comp-sub-wk-r θ₁ π (sub-ex θ₂ V) = cong₂ sub-ex (sub-comp-sub-wk-r θ₁ π θ₂) (sub-val-wk-pre θ₁ π V)

sub-comp-sub-wk-l : (ρ : Γ' ⊇ Γ) (θ₁ : Γ ⊢ Δ) (θ₂ : Δ ⊢ Ψ) -> sub-comp-sub (sub-wk ρ θ₁) θ₂ ≡ sub-wk ρ (sub-comp-sub θ₁ θ₂)
sub-comp-sub-wk-l ρ θ₁ sub-ε        = refl
sub-comp-sub-wk-l ρ θ₁ (sub-ex θ₂ V) = cong₂ sub-ex (sub-comp-sub-wk-l ρ θ₁ θ₂) (sym (wk-sub-val ρ θ₁ V))

sub-comp-sub-ext1 : (θ₁ : Γ ⊢ Δ) (θ₂ : Δ ⊢ Ψ)
  -> sub-comp-sub (sub-ex (sub-wk (wk-wk {A = A} wk-id) θ₁) (var here)) (sub-ex (sub-wk (wk-wk wk-id) θ₂) (var here))
   ≡ sub-ex (sub-wk (wk-wk wk-id) (sub-comp-sub θ₁ θ₂)) (var here)
sub-comp-sub-ext1 θ₁ θ₂ =
  cong₂ sub-ex
    (begin
      sub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) θ₁) (var here)) (sub-wk (wk-wk wk-id) θ₂)
    ≡⟨ sub-comp-sub-wk-r (sub-ex (sub-wk (wk-wk wk-id) θ₁) (var here)) (wk-wk wk-id) θ₂ ⟩
      sub-comp-sub (sub-pre (sub-wk (wk-wk wk-id) θ₁) wk-id) θ₂
    ≡⟨ cong (λ w -> sub-comp-sub w θ₂) (sub-pre-wk-id (sub-wk (wk-wk wk-id) θ₁)) ⟩
      sub-comp-sub (sub-wk (wk-wk wk-id) θ₁) θ₂
    ≡⟨ sub-comp-sub-wk-l (wk-wk wk-id) θ₁ θ₂ ⟩
      sub-wk (wk-wk wk-id) (sub-comp-sub θ₁ θ₂) ∎)
    refl

mutual
  sub-sub-val : (θ₁ : Γ ⊢ Δ) (θ₂ : Δ ⊢ Ψ) (V : Ψ ⊢ᵛ A) -> sub-val θ₁ (sub-val θ₂ V) ≡ sub-val (sub-comp-sub θ₁ θ₂) V
  sub-sub-val θ₁ θ₂ (var i) = sym (sub-mem-sub θ₁ θ₂ i)
  sub-sub-val θ₁ θ₂ (lam M) =
    cong lam (begin
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ₁) (var here)) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ₂) (var here)) M)
    ≡⟨ sub-sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ₁) (var here)) (sub-ex (sub-wk (wk-wk wk-id) θ₂) (var here)) M ⟩
      sub-comp (sub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) θ₁) (var here)) (sub-ex (sub-wk (wk-wk wk-id) θ₂) (var here))) M
    ≡⟨ cong (λ w -> sub-comp w M) (sub-comp-sub-ext1 θ₁ θ₂) ⟩
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-comp-sub θ₁ θ₂)) (var here)) M ∎)
  sub-sub-val θ₁ θ₂ unit = refl

  sub-sub-comp : (θ₁ : Γ ⊢ Δ) (θ₂ : Δ ⊢ Ψ) (M : Ψ ⊢ᶜ A) -> sub-comp θ₁ (sub-comp θ₂ M) ≡ sub-comp (sub-comp-sub θ₁ θ₂) M
  sub-sub-comp θ₁ θ₂ (return V) = cong return (sub-sub-val θ₁ θ₂ V)
  sub-sub-comp θ₁ θ₂ (push M N) =
    cong₂ push (sub-sub-comp θ₁ θ₂ M)
               (begin
                 sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ₁) (var here)) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ₂) (var here)) N)
               ≡⟨ sub-sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ₁) (var here)) (sub-ex (sub-wk (wk-wk wk-id) θ₂) (var here)) N ⟩
                 sub-comp (sub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) θ₁) (var here)) (sub-ex (sub-wk (wk-wk wk-id) θ₂) (var here))) N
               ≡⟨ cong (λ w -> sub-comp w N) (sub-comp-sub-ext1 θ₁ θ₂) ⟩
                 sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-comp-sub θ₁ θ₂)) (var here)) N ∎)
  sub-sub-comp θ₁ θ₂ (app V W) = cong₂ app (sub-sub-val θ₁ θ₂ V) (sub-sub-val θ₁ θ₂ W)

mutual
  sub-val-ren : (π : Γ ⊇ Δ) (V : Δ ⊢ᵛ A) -> sub-val (ren π) V ≡ wk-val π V
  sub-val-ren π (var i) = sub-mem-ren π i
  sub-val-ren π (lam M) = cong lam (sub-comp-ren (wk-cong π) M)
  sub-val-ren π unit    = refl

  sub-comp-ren : (π : Γ ⊇ Δ) (M : Δ ⊢ᶜ A) -> sub-comp (ren π) M ≡ wk-comp π M
  sub-comp-ren π (return V) = cong return (sub-val-ren π V)
  sub-comp-ren π (push M N) = cong₂ push (sub-comp-ren π M) (sub-comp-ren (wk-cong π) N)
  sub-comp-ren π (app V W)  = cong₂ app (sub-val-ren π V) (sub-val-ren π W)

ren-wk-id : ren (wk-id {Γ}) ≡ sub-id {Γ}
ren-wk-id {ε}     = refl
ren-wk-id {Γ ∙ A} = cong (λ θ -> sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (ren-wk-id {Γ})

sub-mem-id : (i : Γ ∋ A) -> sub-mem (sub-id {Γ}) i ≡ var i
sub-mem-id {Γ} i = begin
  sub-mem (sub-id {Γ}) i  ≡˘⟨ cong (λ θ -> sub-mem θ i) (ren-wk-id {Γ}) ⟩
  sub-mem (ren wk-id) i   ≡⟨ sub-mem-ren wk-id i ⟩
  var (wk-mem wk-id i)    ≡⟨ cong var wk-mem-id ⟩
  var i                   ∎

sub-val-id : (V : Γ ⊢ᵛ A) -> sub-val (sub-id {Γ}) V ≡ V
sub-val-id {Γ} V = begin
  sub-val (sub-id {Γ}) V  ≡˘⟨ cong (λ θ -> sub-val θ V) (ren-wk-id {Γ}) ⟩
  sub-val (ren wk-id) V   ≡⟨ sub-val-ren wk-id V ⟩
  wk-val wk-id V          ≡⟨ wk-val-id V ⟩
  V                       ∎

sub-comp-id : (M : Γ ⊢ᶜ A) -> sub-comp (sub-id {Γ}) M ≡ M
sub-comp-id {Γ} M = begin
  sub-comp (sub-id {Γ}) M  ≡˘⟨ cong (λ θ -> sub-comp θ M) (ren-wk-id {Γ}) ⟩
  sub-comp (ren wk-id) M   ≡⟨ sub-comp-ren wk-id M ⟩
  wk-comp wk-id M          ≡⟨ wk-comp-id M ⟩
  M                        ∎

sub-comp-sub-idl : (θ : Γ ⊢ Δ) -> sub-comp-sub sub-id θ ≡ θ
sub-comp-sub-idl sub-ε        = refl
sub-comp-sub-idl (sub-ex θ V) = cong₂ sub-ex (sub-comp-sub-idl θ) (sub-val-id V)

sub-wk-as-comp-ren : (π : Γ' ⊇ Γ) (θ : Γ ⊢ Δ) -> sub-wk π θ ≡ sub-comp-sub (ren π) θ
sub-wk-as-comp-ren π sub-ε        = refl
sub-wk-as-comp-ren π (sub-ex θ V) = cong₂ sub-ex (sub-wk-as-comp-ren π θ) (sym (sub-val-ren π V))

--------------------------------------------------------------------------
-- fundamental lemma

fund-lam-eq : (θ : Γ ⊢ Δ) (π : Γ' ⊇ Γ) (W : Γ' ⊢ᵛ A) (M : (Δ ∙ A) ⊢ᶜ B)
  -> sub-comp (sub-ex sub-id W) (wk-comp (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M))
   ≡ sub-comp (sub-ex (sub-wk π θ) W) M
fund-lam-eq θ π W M = begin
    sub-comp (sub-ex sub-id W) (wk-comp (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M))
  ≡⟨ sub-comp-wk-pre (sub-ex sub-id W) (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M) ⟩
    sub-comp (sub-ex (sub-pre sub-id π) W) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  ≡⟨ cong (λ ξ -> sub-comp (sub-ex ξ W) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)) (sub-pre-id-ren π) ⟩
    sub-comp (sub-ex (ren π) W) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  ≡⟨ sub-sub-comp (sub-ex (ren π) W) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M ⟩
    sub-comp (sub-ex (sub-comp-sub (sub-ex (ren π) W) (sub-wk (wk-wk wk-id) θ)) W) M
  ≡⟨ cong (λ ξ -> sub-comp (sub-ex ξ W) M)
          (begin
             sub-comp-sub (sub-ex (ren π) W) (sub-wk (wk-wk wk-id) θ)
           ≡⟨ sub-comp-sub-wk-r (sub-ex (ren π) W) (wk-wk wk-id) θ ⟩
             sub-comp-sub (sub-pre (ren π) wk-id) θ
           ≡⟨ cong (λ ρ -> sub-comp-sub ρ θ) (sub-pre-wk-id (ren π)) ⟩
             sub-comp-sub (ren π) θ
           ≡˘⟨ sub-wk-as-comp-ren π θ ⟩
             sub-wk π θ ∎) ⟩
    sub-comp (sub-ex (sub-wk π θ) W) M ∎

fund-push-eq : (θ : Γ ⊢ Δ) (V : Γ ⊢ᵛ A) (N : (Δ ∙ A) ⊢ᶜ B)
  -> sub-comp (sub-ex sub-id V) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
   ≡ sub-comp (sub-ex θ V) N
fund-push-eq θ V N = begin
    sub-comp (sub-ex sub-id V) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
  ≡⟨ sub-sub-comp (sub-ex sub-id V) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N ⟩
    sub-comp (sub-ex (sub-comp-sub (sub-ex sub-id V) (sub-wk (wk-wk wk-id) θ)) V) N
  ≡⟨ cong (λ ξ -> sub-comp (sub-ex ξ V) N)
          (begin
             sub-comp-sub (sub-ex sub-id V) (sub-wk (wk-wk wk-id) θ)
           ≡⟨ sub-comp-sub-wk-r (sub-ex sub-id V) (wk-wk wk-id) θ ⟩
             sub-comp-sub (sub-pre sub-id wk-id) θ
           ≡⟨ cong (λ ρ -> sub-comp-sub ρ θ) (sub-pre-wk-id sub-id) ⟩
             sub-comp-sub sub-id θ
           ≡⟨ sub-comp-sub-idl θ ⟩
             θ ∎) ⟩
    sub-comp (sub-ex θ V) N ∎
