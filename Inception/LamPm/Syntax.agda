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
  `Unit : Ty
  _`×_  : Ty -> Ty -> Ty
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
  pair : Γ ⊢ᵛ A -> Γ ⊢ᵛ B -> Γ ⊢ᵛ A `× B
  pm   : Γ ⊢ᵛ A `× B -> (Γ ∙ A ∙ B) ⊢ᵛ C -> Γ ⊢ᵛ C
  unit : Γ ⊢ᵛ `Unit

data Comp where
  return : Γ ⊢ᵛ A -> Γ ⊢ᶜ A
  push   : Γ ⊢ᶜ A -> (Γ ∙ A) ⊢ᶜ B -> Γ ⊢ᶜ B
  app    : Γ ⊢ᵛ A `⇒ B -> Γ ⊢ᵛ A -> Γ ⊢ᶜ B
  pm     : Γ ⊢ᵛ A `× B -> (Γ ∙ A ∙ B) ⊢ᶜ C -> Γ ⊢ᶜ C

--------------------------------------------------------------------------
-- weakenings

mutual
  wk-val : Γ ⊇ Δ -> Δ ⊢ᵛ A -> Γ ⊢ᵛ A
  wk-val π (var i)    = var (wk-mem π i)
  wk-val π (lam M)    = lam (wk-comp (wk-cong π) M)
  wk-val π (pair V W) = pair (wk-val π V) (wk-val π W)
  wk-val π (pm V W)   = pm (wk-val π V) (wk-val (wk-cong (wk-cong π)) W)
  wk-val π unit       = unit

  wk-comp : Γ ⊇ Δ -> Δ ⊢ᶜ A -> Γ ⊢ᶜ A
  wk-comp π (return V) = return (wk-val π V)
  wk-comp π (push M N) = push (wk-comp π M) (wk-comp (wk-cong π) N)
  wk-comp π (app V W)  = app (wk-val π V) (wk-val π W)
  wk-comp π (pm V M)   = pm (wk-val π V) (wk-comp (wk-cong (wk-cong π)) M)

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
  sub-val θ (var i)    = sub-mem θ i
  sub-val θ (lam M)    = lam (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  sub-val θ (pair V W) = pair (sub-val θ V) (sub-val θ W)
  sub-val θ (pm V W)   = pm (sub-val θ V) (sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) W)
  sub-val θ unit       = unit

  sub-comp : Γ ⊢ Δ -> Δ ⊢ᶜ A -> Γ ⊢ᶜ A
  sub-comp θ (return V) = return (sub-val θ V)
  sub-comp θ (push M N) = push (sub-comp θ M) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
  sub-comp θ (app V W)  = app (sub-val θ V) (sub-val θ W)
  sub-comp θ (pm V M)   = pm (sub-val θ V) (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M)


--------------------------------------------------------------------------
-- weakening

mutual
  wk-val-id : (V : Γ ⊢ᵛ A) → wk-val wk-id V ≡ V
  wk-val-id (var i)    = cong var wk-mem-id
  wk-val-id (lam M)    = cong lam (wk-comp-id M)
  wk-val-id (pair V W) = cong₂ pair (wk-val-id V) (wk-val-id W)
  wk-val-id (pm V W)   = cong₂ pm (wk-val-id V) (wk-val-id W)
  wk-val-id unit       = refl

  wk-comp-id : (M : Γ ⊢ᶜ A) → wk-comp wk-id M ≡ M
  wk-comp-id (return V) = cong return (wk-val-id V)
  wk-comp-id (push M N) = cong₂ push (wk-comp-id M) (wk-comp-id N)
  wk-comp-id (app V W)  = cong₂ app (wk-val-id V) (wk-val-id W)
  wk-comp-id (pm V M)   = cong₂ pm (wk-val-id V) (wk-comp-id M)

mutual
  wk-val-trans : (V : Γ ⊢ᵛ A) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → wk-val π (wk-val δ V) ≡ wk-val (wk-trans π δ) V
  wk-val-trans (var i) π δ = cong var (wk-mem-trans i π δ)
  wk-val-trans (lam M) π δ = cong lam (wk-comp-trans M (wk-cong π) (wk-cong δ))
  wk-val-trans (pair V W) π δ = cong₂ pair (wk-val-trans V π δ) (wk-val-trans W π δ)
  wk-val-trans (pm V W) π δ = cong₂ pm (wk-val-trans V π δ) (wk-val-trans W (wk-cong (wk-cong π)) (wk-cong (wk-cong δ)))
  wk-val-trans unit π δ    = refl

  wk-comp-trans : (M : Γ ⊢ᶜ A) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → wk-comp π (wk-comp δ M) ≡ wk-comp (wk-trans π δ) M
  wk-comp-trans (return V) π δ = cong return (wk-val-trans V π δ)
  wk-comp-trans (push M N) π δ = cong₂ push (wk-comp-trans M π δ) (wk-comp-trans N (wk-cong π) (wk-cong δ))
  wk-comp-trans (app V W) π δ  = cong₂ app (wk-val-trans V π δ) (wk-val-trans W π δ)
  wk-comp-trans (pm V M) π δ   = cong₂ pm (wk-val-trans V π δ) (wk-comp-trans M (wk-cong (wk-cong π)) (wk-cong (wk-cong δ)))

--------------------------------------------------------------------------
-- weakening/substitution

sub-wk-trans : (π : Γ ⊇ Γ₁) (δ : Γ₁ ⊇ Γ₂) (θ : Γ₂ ⊢ Δ)
             -> sub-wk π (sub-wk δ θ) ≡ sub-wk (wk-trans π δ) θ
sub-wk-trans π δ sub-ε        = refl
sub-wk-trans π δ (sub-ex θ V) = cong₂ sub-ex (sub-wk-trans π δ θ) (wk-val-trans V π δ)

sub-wk-wk-wk-id : (θ : Γ ⊢ Δ) -> sub-wk (wk-wk {A = A} wk-id) (sub-wk (wk-wk {A = B} wk-id) θ) ≡ sub-wk (wk-wk {A = A} (wk-wk {A = B} wk-id)) θ
sub-wk-wk-wk-id θ = begin
  sub-wk (wk-wk wk-id) (sub-wk (wk-wk wk-id) θ)   ≡⟨ sub-wk-trans (wk-wk wk-id) (wk-wk wk-id) θ ⟩
  sub-wk (wk-trans (wk-wk wk-id) (wk-wk wk-id)) θ ≡⟨ cong (λ π -> sub-wk π θ) (cong wk-wk (wk-trans-idl (wk-wk wk-id))) ⟩
  sub-wk (wk-wk (wk-wk wk-id)) θ ∎

ren : Γ ⊇ Δ -> Γ ⊢ Δ
ren wk-ε        = sub-ε
ren (wk-cong π) = sub-ex (sub-wk (wk-wk wk-id) (ren π)) (var here)
ren (wk-wk π)   = sub-wk (wk-wk wk-id) (ren π)

ren-cong2 : (π : Γ ⊇ Δ) -> ren (wk-cong {A = A} (wk-cong {A = B} π)) ≡ sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (ren π)) (var (there here))) (var here)
ren-cong2 π = cong (λ x -> sub-ex x (var here)) (cong (λ x -> sub-ex x (var (there here))) (sub-wk-wk-wk-id (ren π)))

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

wk-cong-sub-wk-lemma : (π : Γ₁ ⊇ Γ) (θ : Γ ⊢ Δ)
                     -> sub-wk (wk-cong {A = A} π) (sub-wk (wk-wk wk-id) θ) ≡ sub-wk (wk-wk wk-id) (sub-wk π θ)
wk-cong-sub-wk-lemma π θ = begin
  sub-wk (wk-cong π) (sub-wk (wk-wk wk-id) θ) ≡⟨ sub-wk-trans (wk-cong π) (wk-wk wk-id) θ ⟩
  sub-wk (wk-wk (wk-trans π wk-id)) θ         ≡⟨ cong (λ w -> sub-wk w θ) (cong wk-wk (wk-trans-comm-id π)) ⟩
  sub-wk (wk-wk (wk-trans wk-id π)) θ         ≡˘⟨ sub-wk-trans (wk-wk wk-id) π θ ⟩
  sub-wk (wk-wk wk-id) (sub-wk π θ)           ∎

wk-cong2-sub-wk-lemma : (π : Γ₁ ⊇ Γ) (θ : Γ ⊢ Δ)
                      -> sub-wk (wk-cong {A = A} (wk-cong {A = B} π)) (sub-wk (wk-wk (wk-wk wk-id)) θ) ≡ sub-wk (wk-wk (wk-wk wk-id)) (sub-wk π θ)
wk-cong2-sub-wk-lemma π θ = begin
  sub-wk (wk-cong (wk-cong π)) (sub-wk (wk-wk (wk-wk wk-id)) θ) ≡⟨ sub-wk-trans (wk-cong (wk-cong π)) (wk-wk (wk-wk wk-id)) θ ⟩
  sub-wk (wk-wk (wk-wk (wk-trans π wk-id))) θ                   ≡⟨ cong (λ w -> sub-wk w θ) (cong wk-wk (cong wk-wk (wk-trans-comm-id π))) ⟩
  sub-wk (wk-wk (wk-wk (wk-trans wk-id π))) θ                   ≡˘⟨ sub-wk-trans (wk-wk (wk-wk wk-id)) π θ ⟩
  sub-wk (wk-wk (wk-wk wk-id)) (sub-wk π θ)                     ∎

mutual
  wk-sub-val : (π : Γ₁ ⊇ Γ) (θ : Γ ⊢ Δ) (V : Δ ⊢ᵛ A) -> wk-val π (sub-val θ V) ≡ sub-val (sub-wk π θ) V
  wk-sub-val π θ (var i) = sym (sub-mem-wk π θ i)
  wk-sub-val π θ (lam M) =
    cong lam (begin
      wk-comp (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
    ≡⟨ wk-sub-comp (wk-cong π) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M ⟩
      sub-comp (sub-ex (sub-wk (wk-cong π) (sub-wk (wk-wk wk-id) θ)) (var here)) M
    ≡⟨ cong (λ w -> sub-comp (sub-ex w (var here)) M) (wk-cong-sub-wk-lemma π θ) ⟩
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-wk π θ)) (var here)) M ∎)
  wk-sub-val π θ (pair V W) = cong₂ pair (wk-sub-val π θ V) (wk-sub-val π θ W)
  wk-sub-val π θ (pm {A = A₁} {B = B₁} V W) =
    cong₂ pm (wk-sub-val π θ V)
      (begin
        wk-val (wk-cong (wk-cong π)) (sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) W)
      ≡⟨ wk-sub-val (wk-cong (wk-cong π)) (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) W ⟩
        sub-val (sub-ex (sub-ex (sub-wk (wk-cong (wk-cong π)) (sub-wk (wk-wk (wk-wk wk-id)) θ)) (var (there here))) (var here)) W
      ≡⟨ cong (λ w -> sub-val (sub-ex (sub-ex w (var (there here))) (var here)) W) (wk-cong2-sub-wk-lemma {A = B₁} {B = A₁} π θ) ⟩
        sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-wk π θ)) (var (there here))) (var here)) W ∎)
  wk-sub-val π θ unit = refl

  wk-sub-comp : (π : Γ₁ ⊇ Γ) (θ : Γ ⊢ Δ) (M : Δ ⊢ᶜ A) -> wk-comp π (sub-comp θ M) ≡ sub-comp (sub-wk π θ) M
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
  wk-sub-comp π θ (pm {A = A₁} {B = B₁} V M) =
    cong₂ pm (wk-sub-val π θ V)
      (begin
        wk-comp (wk-cong (wk-cong π)) (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M)
      ≡⟨ wk-sub-comp (wk-cong (wk-cong π)) (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M ⟩
        sub-comp (sub-ex (sub-ex (sub-wk (wk-cong (wk-cong π)) (sub-wk (wk-wk (wk-wk wk-id)) θ)) (var (there here))) (var here)) M
      ≡⟨ cong (λ w -> sub-comp (sub-ex (sub-ex w (var (there here))) (var here)) M) (wk-cong2-sub-wk-lemma {A = B₁} {B = A₁} π θ) ⟩
        sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-wk π θ)) (var (there here))) (var here)) M ∎)

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

sub-pre-wk-l : (π : Γ₁ ⊇ Γ) (θ : Γ ⊢ Δ) (δ : Δ ⊇ Ψ) -> sub-pre (sub-wk π θ) δ ≡ sub-wk π (sub-pre θ δ)
sub-pre-wk-l ρ θ wk-ε              = refl
sub-pre-wk-l π (sub-ex θ V) (wk-cong δ) = cong₂ sub-ex (sub-pre-wk-l π θ δ) refl
sub-pre-wk-l π (sub-ex θ V) (wk-wk δ)   = sub-pre-wk-l π θ δ

sub-pre-wk-id : (θ : Γ ⊢ Δ) -> sub-pre θ (wk-id {Δ}) ≡ θ
sub-pre-wk-id sub-ε        = refl
sub-pre-wk-id (sub-ex θ V) = cong (λ w -> sub-ex w V) (sub-pre-wk-id θ)

sub-pre-id-ren : (π : Γ₁ ⊇ Γ) -> sub-pre (sub-id {Γ₁}) π ≡ ren π
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

sub-wk-id-ren : (π : Γ₁ ⊇ Γ) -> sub-wk π (sub-id {Γ}) ≡ ren π
sub-wk-id-ren wk-ε        = refl
sub-wk-id-ren (wk-cong π) =
  cong (λ w -> sub-ex w (var here)) (begin
    sub-wk (wk-cong π) (sub-wk (wk-wk wk-id) sub-id)  ≡⟨ sub-wk-trans (wk-cong π) (wk-wk wk-id) sub-id ⟩
    sub-wk (wk-wk (wk-trans π wk-id)) sub-id          ≡⟨ cong (λ δ -> sub-wk (wk-wk δ) sub-id) (wk-trans-idr π) ⟩
    sub-wk (wk-wk π) sub-id                           ≡˘⟨ cong (λ δ -> sub-wk (wk-wk δ) sub-id) (wk-trans-idl π) ⟩
    sub-wk (wk-wk (wk-trans wk-id π)) sub-id          ≡˘⟨ sub-wk-trans (wk-wk wk-id) π sub-id ⟩
    sub-wk (wk-wk wk-id) (sub-wk π sub-id)            ≡⟨ cong (sub-wk (wk-wk wk-id)) (sub-wk-id-ren π) ⟩
    sub-wk (wk-wk wk-id) (ren π)                      ∎)
sub-wk-id-ren (wk-wk π) = begin
  sub-wk (wk-wk π) sub-id                   ≡˘⟨ cong (λ δ -> sub-wk (wk-wk δ) sub-id) (wk-trans-idl π) ⟩
  sub-wk (wk-wk (wk-trans wk-id π)) sub-id  ≡˘⟨ sub-wk-trans (wk-wk wk-id) π sub-id ⟩
  sub-wk (wk-wk wk-id) (sub-wk π sub-id)    ≡⟨ cong (sub-wk (wk-wk wk-id)) (sub-wk-id-ren π) ⟩
  sub-wk (wk-wk wk-id) (ren π)              ∎

mutual
  sub-val-wk-pre : (θ : Γ ⊢ Δ₁) (π : Δ₁ ⊇ Δ) (V : Δ ⊢ᵛ A) -> sub-val θ (wk-val π V) ≡ sub-val (sub-pre θ π) V
  sub-val-wk-pre θ π (var i) = sym (sub-mem-pre θ π i)
  sub-val-wk-pre θ π (lam M) =
    cong lam (begin
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-comp (wk-cong π) M)
    ≡⟨ sub-comp-wk-pre (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-cong π) M ⟩
      sub-comp (sub-ex (sub-pre (sub-wk (wk-wk wk-id) θ) π) (var here)) M
    ≡⟨ cong (λ w -> sub-comp (sub-ex w (var here)) M) (sub-pre-wk-l (wk-wk wk-id) θ π) ⟩
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-pre θ π)) (var here)) M ∎)
  sub-val-wk-pre θ π (pair V W) = cong₂ pair (sub-val-wk-pre θ π V) (sub-val-wk-pre θ π W)
  sub-val-wk-pre θ π (pm {A = A₁} {B = B₁} V W) =
    cong₂ pm (sub-val-wk-pre θ π V)
      (begin
        sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) (wk-val (wk-cong (wk-cong π)) W)
      ≡⟨ sub-val-wk-pre (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) (wk-cong (wk-cong π)) W ⟩
        sub-val (sub-ex (sub-ex (sub-pre (sub-wk (wk-wk (wk-wk wk-id)) θ) π) (var (there here))) (var here)) W
      ≡⟨ cong (λ w -> sub-val (sub-ex (sub-ex w (var (there here))) (var here)) W) (sub-pre-wk-l (wk-wk (wk-wk wk-id)) θ π) ⟩
        sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-pre θ π)) (var (there here))) (var here)) W ∎)
  sub-val-wk-pre θ π unit = refl

  sub-comp-wk-pre : (θ : Γ ⊢ Δ₁) (π : Δ₁ ⊇ Δ) (M : Δ ⊢ᶜ A) -> sub-comp θ (wk-comp π M) ≡ sub-comp (sub-pre θ π) M
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
  sub-comp-wk-pre θ π (pm {A = A₁} {B = B₁} V M) =
    cong₂ pm (sub-val-wk-pre θ π V)
      (begin
        sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) (wk-comp (wk-cong (wk-cong π)) M)
      ≡⟨ sub-comp-wk-pre (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) (wk-cong (wk-cong π)) M ⟩
        sub-comp (sub-ex (sub-ex (sub-pre (sub-wk (wk-wk (wk-wk wk-id)) θ) π) (var (there here))) (var here)) M
      ≡⟨ cong (λ w -> sub-comp (sub-ex (sub-ex w (var (there here))) (var here)) M) (sub-pre-wk-l (wk-wk (wk-wk wk-id)) θ π) ⟩
        sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-pre θ π)) (var (there here))) (var here)) M ∎)

wk-beta-1 : (π : Γ₁ ⊇ Γ) (V : Γ ⊢ᵛ A) (M : (Γ ∙ A) ⊢ᶜ B)
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

wk-beta-pmᵛ : (π : Γ₁ ⊇ Γ) (V₁ : Γ ⊢ᵛ A) (V₂ : Γ ⊢ᵛ B) (W : (Γ ∙ A ∙ B) ⊢ᵛ C)
  -> sub-val (sub-ex (sub-ex sub-id (wk-val π V₁)) (wk-val π V₂)) (wk-val (wk-cong (wk-cong π)) W) ≡ wk-val π (sub-val (sub-ex (sub-ex sub-id V₁) V₂) W)
wk-beta-pmᵛ π V₁ V₂ W = begin
    sub-val (sub-ex (sub-ex sub-id (wk-val π V₁)) (wk-val π V₂)) (wk-val (wk-cong (wk-cong π)) W)
  ≡⟨ sub-val-wk-pre (sub-ex (sub-ex sub-id (wk-val π V₁)) (wk-val π V₂)) (wk-cong (wk-cong π)) W ⟩
    sub-val (sub-ex (sub-ex (sub-pre sub-id π) (wk-val π V₁)) (wk-val π V₂)) W
  ≡⟨ cong (λ z -> sub-val (sub-ex (sub-ex z (wk-val π V₁)) (wk-val π V₂)) W) (sub-pre-id-ren π) ⟩
    sub-val (sub-ex (sub-ex (ren π) (wk-val π V₁)) (wk-val π V₂)) W
  ≡˘⟨ cong (λ z -> sub-val (sub-ex (sub-ex z (wk-val π V₁)) (wk-val π V₂)) W) (sub-wk-id-ren π) ⟩
    sub-val (sub-ex (sub-ex (sub-wk π sub-id) (wk-val π V₁)) (wk-val π V₂)) W
  ≡˘⟨ wk-sub-val π (sub-ex (sub-ex sub-id V₁) V₂) W ⟩
    wk-val π (sub-val (sub-ex (sub-ex sub-id V₁) V₂) W) ∎

wk-beta-pmᶜ : (π : Γ₁ ⊇ Γ) (V : Γ ⊢ᵛ A) (W : Γ ⊢ᵛ B) (M : (Γ ∙ A ∙ B) ⊢ᶜ C)
  -> sub-comp (sub-ex (sub-ex sub-id (wk-val π V)) (wk-val π W)) (wk-comp (wk-cong (wk-cong π)) M) ≡ wk-comp π (sub-comp (sub-ex (sub-ex sub-id V) W) M)
wk-beta-pmᶜ π V W M = begin
    sub-comp (sub-ex (sub-ex sub-id (wk-val π V)) (wk-val π W)) (wk-comp (wk-cong (wk-cong π)) M)
  ≡⟨ sub-comp-wk-pre (sub-ex (sub-ex sub-id (wk-val π V)) (wk-val π W)) (wk-cong (wk-cong π)) M ⟩
    sub-comp (sub-ex (sub-ex (sub-pre sub-id π) (wk-val π V)) (wk-val π W)) M
  ≡⟨ cong (λ z -> sub-comp (sub-ex (sub-ex z (wk-val π V)) (wk-val π W)) M) (sub-pre-id-ren π) ⟩
    sub-comp (sub-ex (sub-ex (ren π) (wk-val π V)) (wk-val π W)) M
  ≡˘⟨ cong (λ z -> sub-comp (sub-ex (sub-ex z (wk-val π V)) (wk-val π W)) M) (sub-wk-id-ren π) ⟩
    sub-comp (sub-ex (sub-ex (sub-wk π sub-id) (wk-val π V)) (wk-val π W)) M
  ≡˘⟨ wk-sub-comp π (sub-ex (sub-ex sub-id V) W) M ⟩
    wk-comp π (sub-comp (sub-ex (sub-ex sub-id V) W) M) ∎

--------------------------------------------------------------------------
-- substitution composition

sub-comp-sub : Γ ⊢ Δ -> Δ ⊢ Ψ -> Γ ⊢ Ψ
sub-comp-sub θ sub-ε        = sub-ε
sub-comp-sub θ (sub-ex φ V) = sub-ex (sub-comp-sub θ φ) (sub-val θ V)

sub-mem-sub : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) (i : Ψ ∋ A) -> sub-mem (sub-comp-sub θ φ) i ≡ sub-val θ (sub-mem φ i)
sub-mem-sub θ (sub-ex φ V) here     = refl
sub-mem-sub θ (sub-ex φ V) (there i) = sub-mem-sub θ φ i

sub-comp-sub-wk-r : (θ : Γ ⊢ Δ₁) (π : Δ₁ ⊇ Δ) (φ : Δ ⊢ Ψ) -> sub-comp-sub θ (sub-wk π φ) ≡ sub-comp-sub (sub-pre θ π) φ
sub-comp-sub-wk-r θ π sub-ε        = refl
sub-comp-sub-wk-r θ π (sub-ex φ V) = cong₂ sub-ex (sub-comp-sub-wk-r θ π φ) (sub-val-wk-pre θ π V)

sub-comp-sub-wk-l : (ρ : Γ₁ ⊇ Γ) (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) -> sub-comp-sub (sub-wk ρ θ) φ ≡ sub-wk ρ (sub-comp-sub θ φ)
sub-comp-sub-wk-l ρ θ sub-ε        = refl
sub-comp-sub-wk-l ρ θ (sub-ex φ V) = cong₂ sub-ex (sub-comp-sub-wk-l ρ θ φ) (sym (wk-sub-val ρ θ V))

sub-comp-sub-ext1 : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ)
  -> sub-comp-sub (sub-ex (sub-wk (wk-wk {A = A} wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here))
   ≡ sub-ex (sub-wk (wk-wk wk-id) (sub-comp-sub θ φ)) (var here)
sub-comp-sub-ext1 θ φ =
  cong₂ sub-ex
    (begin
      sub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-wk (wk-wk wk-id) φ)
    ≡⟨ sub-comp-sub-wk-r (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-wk wk-id) φ ⟩
      sub-comp-sub (sub-pre (sub-wk (wk-wk wk-id) θ) wk-id) φ
    ≡⟨ cong (λ w -> sub-comp-sub w φ) (sub-pre-wk-id (sub-wk (wk-wk wk-id) θ)) ⟩
      sub-comp-sub (sub-wk (wk-wk wk-id) θ) φ
    ≡⟨ sub-comp-sub-wk-l (wk-wk wk-id) θ φ ⟩
      sub-wk (wk-wk wk-id) (sub-comp-sub θ φ) ∎)
    refl

sub-comp-sub-ext2 : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ)
  -> sub-comp-sub (sub-ex (sub-ex (sub-wk (wk-wk {A = A} (wk-wk {A = B} wk-id)) θ) (var (there here))) (var here))
                  (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) φ) (var (there here))) (var here))
   ≡ sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-comp-sub θ φ)) (var (there here))) (var here)
sub-comp-sub-ext2 θ φ =
  cong₂ sub-ex
    (cong₂ sub-ex
      (begin
        sub-comp-sub (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) (sub-wk (wk-wk (wk-wk wk-id)) φ)
      ≡⟨ sub-comp-sub-wk-r (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) (wk-wk (wk-wk wk-id)) φ ⟩
        sub-comp-sub (sub-pre (sub-wk (wk-wk (wk-wk wk-id)) θ) wk-id) φ
      ≡⟨ cong (λ w -> sub-comp-sub w φ) (sub-pre-wk-id (sub-wk (wk-wk (wk-wk wk-id)) θ)) ⟩
        sub-comp-sub (sub-wk (wk-wk (wk-wk wk-id)) θ) φ
      ≡⟨ sub-comp-sub-wk-l (wk-wk (wk-wk wk-id)) θ φ ⟩
        sub-wk (wk-wk (wk-wk wk-id)) (sub-comp-sub θ φ) ∎)
      refl)
    refl

mutual
  sub-sub-val : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) (V : Ψ ⊢ᵛ A) -> sub-val θ (sub-val φ V) ≡ sub-val (sub-comp-sub θ φ) V
  sub-sub-val θ φ (var i) = sym (sub-mem-sub θ φ i)
  sub-sub-val θ φ (lam M) =
    cong lam (begin
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) φ) (var here)) M)
    ≡⟨ sub-sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here)) M ⟩
      sub-comp (sub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here))) M
    ≡⟨ cong (λ w -> sub-comp w M) (sub-comp-sub-ext1 θ φ) ⟩
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-comp-sub θ φ)) (var here)) M ∎)
  sub-sub-val θ φ (pair V W) = cong₂ pair (sub-sub-val θ φ V) (sub-sub-val θ φ W)
  sub-sub-val θ φ (pm {A = A₁} {B = B₁} V W) =
    cong₂ pm (sub-sub-val θ φ V)
      (begin
        sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here))
                (sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) φ) (var (there here))) (var here)) W)
      ≡⟨ sub-sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here))
                     (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) φ) (var (there here))) (var here)) W ⟩
        sub-val (sub-comp-sub (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here))
                              (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) φ) (var (there here))) (var here))) W
      ≡⟨ cong (λ w -> sub-val w W) (sub-comp-sub-ext2 {A = B₁} {B = A₁} θ φ) ⟩
        sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-comp-sub θ φ)) (var (there here))) (var here)) W ∎)
  sub-sub-val θ φ unit = refl

  sub-sub-comp : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) (M : Ψ ⊢ᶜ A) -> sub-comp θ (sub-comp φ M) ≡ sub-comp (sub-comp-sub θ φ) M
  sub-sub-comp θ φ (return V) = cong return (sub-sub-val θ φ V)
  sub-sub-comp θ φ (push M N) =
    cong₂ push (sub-sub-comp θ φ M)
               (begin
                 sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) φ) (var here)) N)
               ≡⟨ sub-sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here)) N ⟩
                 sub-comp (sub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here))) N
               ≡⟨ cong (λ w -> sub-comp w N) (sub-comp-sub-ext1 θ φ) ⟩
                 sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-comp-sub θ φ)) (var here)) N ∎)
  sub-sub-comp θ φ (app V W) = cong₂ app (sub-sub-val θ φ V) (sub-sub-val θ φ W)
  sub-sub-comp θ φ (pm {A = A₁} {B = B₁} V M) =
    cong₂ pm (sub-sub-val θ φ V)
      (begin
        sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here))
                 (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) φ) (var (there here))) (var here)) M)
      ≡⟨ sub-sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here))
                      (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) φ) (var (there here))) (var here)) M ⟩
        sub-comp (sub-comp-sub (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here))
                               (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) φ) (var (there here))) (var here))) M
      ≡⟨ cong (λ w -> sub-comp w M) (sub-comp-sub-ext2 {A = B₁} {B = A₁} θ φ) ⟩
        sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-comp-sub θ φ)) (var (there here))) (var here)) M ∎)

mutual
  sub-val-ren : (π : Γ ⊇ Δ) (V : Δ ⊢ᵛ A) -> sub-val (ren π) V ≡ wk-val π V
  sub-val-ren π (var i) = sub-mem-ren π i
  sub-val-ren π (lam M) = cong lam (sub-comp-ren (wk-cong π) M)
  sub-val-ren π (pair V W) = cong₂ pair (sub-val-ren π V) (sub-val-ren π W)
  sub-val-ren π (pm {A = A₁} {B = B₁} V W) =
    cong₂ pm (sub-val-ren π V)
      (begin
        sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (ren π)) (var (there here))) (var here)) W
      ≡˘⟨ cong (λ θ -> sub-val θ W) (ren-cong2 {A = B₁} {B = A₁} π) ⟩
        sub-val (ren (wk-cong (wk-cong π))) W
      ≡⟨ sub-val-ren (wk-cong (wk-cong π)) W ⟩
        wk-val (wk-cong (wk-cong π)) W ∎)
  sub-val-ren π unit    = refl

  sub-comp-ren : (π : Γ ⊇ Δ) (M : Δ ⊢ᶜ A) -> sub-comp (ren π) M ≡ wk-comp π M
  sub-comp-ren π (return V) = cong return (sub-val-ren π V)
  sub-comp-ren π (push M N) = cong₂ push (sub-comp-ren π M) (sub-comp-ren (wk-cong π) N)
  sub-comp-ren π (app V W)  = cong₂ app (sub-val-ren π V) (sub-val-ren π W)
  sub-comp-ren π (pm {A = A₁} {B = B₁} V M) =
    cong₂ pm (sub-val-ren π V)
      (begin
        sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (ren π)) (var (there here))) (var here)) M
      ≡˘⟨ cong (λ θ -> sub-comp θ M) (ren-cong2 {A = B₁} {B = A₁} π) ⟩
        sub-comp (ren (wk-cong (wk-cong π))) M
      ≡⟨ sub-comp-ren (wk-cong (wk-cong π)) M ⟩
        wk-comp (wk-cong (wk-cong π)) M ∎)

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

sub-wk-as-comp-ren : (π : Γ₁ ⊇ Γ) (θ : Γ ⊢ Δ) -> sub-wk π θ ≡ sub-comp-sub (ren π) θ
sub-wk-as-comp-ren π sub-ε        = refl
sub-wk-as-comp-ren π (sub-ex θ V) = cong₂ sub-ex (sub-wk-as-comp-ren π θ) (sym (sub-val-ren π V))

--------------------------------------------------------------------------
-- fundamental lemma

fund-lam-eq : (θ : Γ ⊢ Δ) (π : Γ₁ ⊇ Γ) (V : Γ₁ ⊢ᵛ A) (M : (Δ ∙ A) ⊢ᶜ B)
  -> sub-comp (sub-ex sub-id V) (wk-comp (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M))
   ≡ sub-comp (sub-ex (sub-wk π θ) V) M
fund-lam-eq θ π V M = begin
    sub-comp (sub-ex sub-id V) (wk-comp (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M))
  ≡⟨ sub-comp-wk-pre (sub-ex sub-id V) (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M) ⟩
    sub-comp (sub-ex (sub-pre sub-id π) V) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  ≡⟨ cong (λ ξ -> sub-comp (sub-ex ξ V) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)) (sub-pre-id-ren π) ⟩
    sub-comp (sub-ex (ren π) V) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  ≡⟨ sub-sub-comp (sub-ex (ren π) V) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M ⟩
    sub-comp (sub-ex (sub-comp-sub (sub-ex (ren π) V) (sub-wk (wk-wk wk-id) θ)) V) M
  ≡⟨ cong (λ ξ -> sub-comp (sub-ex ξ V) M)
          (begin
             sub-comp-sub (sub-ex (ren π) V) (sub-wk (wk-wk wk-id) θ)
           ≡⟨ sub-comp-sub-wk-r (sub-ex (ren π) V) (wk-wk wk-id) θ ⟩
             sub-comp-sub (sub-pre (ren π) wk-id) θ
           ≡⟨ cong (λ δ -> sub-comp-sub δ θ) (sub-pre-wk-id (ren π)) ⟩
             sub-comp-sub (ren π) θ
           ≡˘⟨ sub-wk-as-comp-ren π θ ⟩
             sub-wk π θ ∎) ⟩
    sub-comp (sub-ex (sub-wk π θ) V) M ∎

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

fund-pm-eqᵛ : (θ : Γ ⊢ Δ) (V₁ : Γ ⊢ᵛ A) (V₂ : Γ ⊢ᵛ B) (W : (Δ ∙ A ∙ B) ⊢ᵛ C)
  -> sub-val (sub-ex (sub-ex sub-id V₁) V₂) (sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) W)
   ≡ sub-val (sub-ex (sub-ex θ V₁) V₂) W
fund-pm-eqᵛ θ V₁ V₂ W = begin
    sub-val (sub-ex (sub-ex sub-id V₁) V₂) (sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) W)
  ≡⟨ sub-sub-val (sub-ex (sub-ex sub-id V₁) V₂) (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) W ⟩
    sub-val (sub-ex (sub-ex (sub-comp-sub (sub-ex (sub-ex sub-id V₁) V₂) (sub-wk (wk-wk (wk-wk wk-id)) θ)) V₁) V₂) W
  ≡⟨ cong (λ ρ -> sub-val (sub-ex (sub-ex ρ V₁) V₂) W)
          (begin
             sub-comp-sub (sub-ex (sub-ex sub-id V₁) V₂) (sub-wk (wk-wk (wk-wk wk-id)) θ)
           ≡⟨ sub-comp-sub-wk-r (sub-ex (sub-ex sub-id V₁) V₂) (wk-wk (wk-wk wk-id)) θ ⟩
             sub-comp-sub (sub-pre sub-id wk-id) θ
           ≡⟨ cong (λ ρ -> sub-comp-sub ρ θ) (sub-pre-wk-id sub-id) ⟩
             sub-comp-sub sub-id θ
           ≡⟨ sub-comp-sub-idl θ ⟩
             θ ∎) ⟩
    sub-val (sub-ex (sub-ex θ V₁) V₂) W ∎

fund-pm-eqᶜ : (θ : Γ ⊢ Δ) (V : Γ ⊢ᵛ A) (W : Γ ⊢ᵛ B) (M : (Δ ∙ A ∙ B) ⊢ᶜ C)
  -> sub-comp (sub-ex (sub-ex sub-id V) W) (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M)
   ≡ sub-comp (sub-ex (sub-ex θ V) W) M
fund-pm-eqᶜ θ V W M = begin
    sub-comp (sub-ex (sub-ex sub-id V) W) (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M)
  ≡⟨ sub-sub-comp (sub-ex (sub-ex sub-id V) W) (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M ⟩
    sub-comp (sub-ex (sub-ex (sub-comp-sub (sub-ex (sub-ex sub-id V) W) (sub-wk (wk-wk (wk-wk wk-id)) θ)) V) W) M
  ≡⟨ cong (λ ρ -> sub-comp (sub-ex (sub-ex ρ V) W) M)
          (begin
             sub-comp-sub (sub-ex (sub-ex sub-id V) W) (sub-wk (wk-wk (wk-wk wk-id)) θ)
           ≡⟨ sub-comp-sub-wk-r (sub-ex (sub-ex sub-id V) W) (wk-wk (wk-wk wk-id)) θ ⟩
             sub-comp-sub (sub-pre sub-id wk-id) θ
           ≡⟨ cong (λ ρ -> sub-comp-sub ρ θ) (sub-pre-wk-id sub-id) ⟩
             sub-comp-sub sub-id θ
           ≡⟨ sub-comp-sub-idl θ ⟩
             θ ∎) ⟩
    sub-comp (sub-ex (sub-ex θ V) W) M ∎
