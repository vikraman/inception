{-# OPTIONS --no-postfix-projections #-}

module Inception.LamPm.Syntax where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; cong₂)
open Eq.≡-Reasoning

--------------------------------------------------------------------------
-- types and contexts

infixr 40 _`×_
infixr 25 _`⇒_

data Ty : Set where
  `Unit : Ty
  _`×_  : Ty -> Ty -> Ty
  _`⇒_  : Ty -> Ty -> Ty

infixl 15 _∙_
infix  10 _∋_

data Ctx : Set where
  ε   : Ctx
  _∙_ : Ctx -> Ty -> Ctx

variable
  A B C D X Y : Ty
  Γ Δ Ψ Γ' Γ'' Γ''' Δ' : Ctx

data _∋_ : Ctx -> Ty -> Set where
  h : Γ ∙ A ∋ A
  t : Γ ∋ A -> Γ ∙ B ∋ A

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

syntax Wk Γ Δ = Γ ⊇ Δ
data Wk : (Γ Δ : Ctx) -> Set where
  wk-ε    : ε ⊇ ε
  wk-cong : Γ ⊇ Δ -> (Γ ∙ A) ⊇ (Δ ∙ A)
  wk-wk   : Γ ⊇ Δ -> (Γ ∙ A) ⊇ Δ

wk-id : Γ ⊇ Γ
wk-id {Γ = ε}     = wk-ε
wk-id {Γ = Γ ∙ A} = wk-cong wk-id

wk-mem : Γ ⊇ Δ -> Δ ∋ A -> Γ ∋ A
wk-mem (wk-cong π) h     = h
wk-mem (wk-wk π)   h     = t (wk-mem π h)
wk-mem (wk-cong π) (t i) = t (wk-mem π i)
wk-mem (wk-wk π)   (t i) = t (wk-mem π (t i))

mutual
  wk-val : Γ ⊇ Δ -> Δ ⊢ᵛ A -> Γ ⊢ᵛ A
  wk-val π (var i)      = var (wk-mem π i)
  wk-val π (lam M)      = lam (wk-comp (wk-cong π) M)
  wk-val π (pair V1 V2) = pair (wk-val π V1) (wk-val π V2)
  wk-val π (pm V W)     = pm (wk-val π V) (wk-val (wk-cong (wk-cong π)) W)
  wk-val π unit         = unit

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
sub-mem (sub-ex θ V) h     = V
sub-mem (sub-ex θ V) (t i) = sub-mem θ i

sub-wk : Γ ⊇ Δ -> Δ ⊢ Ψ -> Γ ⊢ Ψ
sub-wk π sub-ε        = sub-ε
sub-wk π (sub-ex θ V) = sub-ex (sub-wk π θ) (wk-val π V)

sub-id : Γ ⊢ Γ
sub-id {Γ = ε}     = sub-ε
sub-id {Γ = Γ ∙ A} = sub-ex (sub-wk (wk-wk wk-id) sub-id) (var h)

mutual
  sub-val : Γ ⊢ Δ -> Δ ⊢ᵛ A -> Γ ⊢ᵛ A
  sub-val θ (var i)      = sub-mem θ i
  sub-val θ (lam M)      = lam (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) M)
  sub-val θ (pair V1 V2) = pair (sub-val θ V1) (sub-val θ V2)
  sub-val θ (pm V W)     = pm (sub-val θ V) (sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) W)
  sub-val θ unit         = unit

  sub-comp : Γ ⊢ Δ -> Δ ⊢ᶜ A -> Γ ⊢ᶜ A
  sub-comp θ (return V) = return (sub-val θ V)
  sub-comp θ (push M N) = push (sub-comp θ M) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) N)
  sub-comp θ (app V W)  = app (sub-val θ V) (sub-val θ W)
  sub-comp θ (pm V M)   = pm (sub-val θ V) (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) M)

variable
  x : Γ ∋ A
  V V1 V2 V3 : Γ ⊢ᵛ A
  W W1 W2 W3 : Γ ⊢ᵛ A
  M M1 M2 M3 : Γ ⊢ᶜ A
  N N1 N2 N3 : Γ ⊢ᶜ A

--------------------------------------------------------------------------
-- weakening

wk-trans : Γ ⊇ Δ → Δ ⊇ Ψ → Γ ⊇ Ψ
wk-trans wk-ε π₂        = π₂
wk-trans (wk-cong π₁) (wk-cong π₂) = wk-cong (wk-trans π₁ π₂)
wk-trans (wk-cong π₁) (wk-wk π₂)   = wk-wk (wk-trans π₁ π₂)
wk-trans (wk-wk π₁) π₂             = wk-wk (wk-trans π₁ π₂)

wk-mem-id : {i : Γ ∋ A} → wk-mem wk-id i ≡ i
wk-mem-id {i = h}   = refl
wk-mem-id {i = t i} = cong t wk-mem-id

mutual
  wk-val-id : (M : Γ ⊢ᵛ A) → wk-val wk-id M ≡ M
  wk-val-id (var i)      = cong var wk-mem-id
  wk-val-id (lam W)      = cong lam (wk-comp-id W)
  wk-val-id (pair V1 V2) = cong₂ pair (wk-val-id V1) (wk-val-id V2)
  wk-val-id (pm V W)     = cong₂ pm (wk-val-id V) (wk-val-id W)
  wk-val-id unit         = refl

  wk-comp-id : (W : Γ ⊢ᶜ A) → wk-comp wk-id W ≡ W
  wk-comp-id (return x) = cong return (wk-val-id x)
  wk-comp-id (push M N) = cong₂ push (wk-comp-id M) (wk-comp-id N)
  wk-comp-id (app W W₁) = cong₂ app (wk-val-id W) (wk-val-id W₁)
  wk-comp-id (pm V M)   = cong₂ pm (wk-val-id V) (wk-comp-id M)

wk-mem-trans : (i : Γ ∋ A) → (π₁ : Ψ ⊇ Δ) → (π₂ : Δ ⊇ Γ) → wk-mem π₁ (wk-mem π₂ i) ≡ wk-mem (wk-trans π₁ π₂) i
wk-mem-trans h (wk-cong π₁) (wk-cong π₂) = refl
wk-mem-trans h (wk-cong π₁) (wk-wk π₂)   = cong t (wk-mem-trans h π₁ π₂)
wk-mem-trans h (wk-wk π₁)   (wk-cong π₂) = cong t (wk-mem-trans h π₁ (wk-cong π₂))
wk-mem-trans h (wk-wk π₁)   (wk-wk π₂)   = cong t (wk-mem-trans h π₁ (wk-wk π₂))
wk-mem-trans (t i) (wk-cong π₁) (wk-cong π₂) = cong t (wk-mem-trans i π₁ π₂)
wk-mem-trans (t i) (wk-wk (wk-cong π₁)) (wk-cong π₂) = cong t (cong t (wk-mem-trans i π₁ π₂))
wk-mem-trans (t i) (wk-wk (wk-wk π₁)) (wk-cong π₂)   = cong t (cong t (wk-mem-trans (t i) π₁ (wk-cong π₂)))
wk-mem-trans (t i) (wk-cong π₁) (wk-wk π₂) = cong t (wk-mem-trans (t i) π₁ π₂)
wk-mem-trans (t i) (wk-wk (wk-cong π₁)) (wk-wk π₂) = cong t (wk-mem-trans (t i) (wk-cong π₁) (wk-wk π₂))
wk-mem-trans (t i) (wk-wk (wk-wk π₁)) (wk-wk π₂)   = cong t (wk-mem-trans (t i) (wk-wk π₁) (wk-wk π₂))

mutual
  wk-val-trans : (M : Γ ⊢ᵛ A) → (π₁ : Ψ ⊇ Δ) → (π₂ : Δ ⊇ Γ) → wk-val π₁ (wk-val π₂ M) ≡ wk-val (wk-trans π₁ π₂) M
  wk-val-trans (var i) π₁ π₂ = cong var (wk-mem-trans i π₁ π₂)
  wk-val-trans (lam x) π₁ π₂ = cong lam (wk-comp-trans x (wk-cong π₁) (wk-cong π₂))
  wk-val-trans (pair V1 V2) π₁ π₂ = cong₂ pair (wk-val-trans V1 π₁ π₂) (wk-val-trans V2 π₁ π₂)
  wk-val-trans (pm V W) π₁ π₂ = cong₂ pm (wk-val-trans V π₁ π₂) (wk-val-trans W (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π₂)))
  wk-val-trans unit π₁ π₂    = refl

  wk-comp-trans : (W : Γ ⊢ᶜ A) → (π₁ : Ψ ⊇ Δ) → (π₂ : Δ ⊇ Γ) → wk-comp π₁ (wk-comp π₂ W) ≡ wk-comp (wk-trans π₁ π₂) W
  wk-comp-trans (return M) π₁ π₂ = cong return (wk-val-trans M π₁ π₂)
  wk-comp-trans (push M N) π₁ π₂ = cong₂ push (wk-comp-trans M π₁ π₂) (wk-comp-trans N (wk-cong π₁) (wk-cong π₂))
  wk-comp-trans (app V W) π₁ π₂  = cong₂ app (wk-val-trans V π₁ π₂) (wk-val-trans W π₁ π₂)
  wk-comp-trans (pm V M) π₁ π₂   = cong₂ pm (wk-val-trans V π₁ π₂) (wk-comp-trans M (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π₂)))

wk-trans-idl : (π : Γ ⊇ Δ) -> wk-trans wk-id π ≡ π
wk-trans-idl wk-ε        = refl
wk-trans-idl (wk-cong π) = cong wk-cong (wk-trans-idl π)
wk-trans-idl (wk-wk π)   = cong wk-wk (wk-trans-idl π)

wk-trans-idr : (π : Γ ⊇ Δ) -> wk-trans π wk-id ≡ π
wk-trans-idr wk-ε        = refl
wk-trans-idr (wk-cong π) = cong wk-cong (wk-trans-idr π)
wk-trans-idr (wk-wk π)   = cong wk-wk (wk-trans-idr π)

wk-trans-comm-id : (π : Γ ⊇ Δ) -> wk-trans π wk-id ≡ wk-trans wk-id π
wk-trans-comm-id π = begin
  wk-trans π wk-id  ≡⟨ wk-trans-idr π ⟩
  π                 ≡˘⟨ wk-trans-idl π ⟩
  wk-trans wk-id π  ∎

--------------------------------------------------------------------------
-- weakening/substitution

sub-wk-trans : (π1 : Γ ⊇ Γ') (π2 : Γ' ⊇ Γ'') (θ : Γ'' ⊢ Δ)
             -> sub-wk π1 (sub-wk π2 θ) ≡ sub-wk (wk-trans π1 π2) θ
sub-wk-trans π1 π2 sub-ε        = refl
sub-wk-trans π1 π2 (sub-ex θ V) = cong₂ sub-ex (sub-wk-trans π1 π2 θ) (wk-val-trans V π1 π2)

sub-wk-wk-wk-id : (θ : Γ ⊢ Δ) -> sub-wk (wk-wk {A = A} wk-id) (sub-wk (wk-wk {A = B} wk-id) θ) ≡ sub-wk (wk-wk {A = A} (wk-wk {A = B} wk-id)) θ
sub-wk-wk-wk-id θ = begin
  sub-wk (wk-wk wk-id) (sub-wk (wk-wk wk-id) θ)   ≡⟨ sub-wk-trans (wk-wk wk-id) (wk-wk wk-id) θ ⟩
  sub-wk (wk-trans (wk-wk wk-id) (wk-wk wk-id)) θ ≡⟨ cong (λ π -> sub-wk π θ) (cong wk-wk (wk-trans-idl (wk-wk wk-id))) ⟩
  sub-wk (wk-wk (wk-wk wk-id)) θ ∎

ren : Γ ⊇ Δ -> Γ ⊢ Δ
ren wk-ε        = sub-ε
ren (wk-cong π) = sub-ex (sub-wk (wk-wk wk-id) (ren π)) (var h)
ren (wk-wk π)   = sub-wk (wk-wk wk-id) (ren π)

ren-cong2 : (π : Γ ⊇ Δ) -> ren (wk-cong {A = A} (wk-cong {A = B} π)) ≡ sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (ren π)) (var (t h))) (var h)
ren-cong2 π = cong (λ x -> sub-ex x (var h)) (cong (λ x -> sub-ex x (var (t h))) (sub-wk-wk-wk-id (ren π)))

sub-mem-wk : (π : Γ ⊇ Δ) (θ : Δ ⊢ Ψ) (i : Ψ ∋ A) -> sub-mem (sub-wk π θ) i ≡ wk-val π (sub-mem θ i)
sub-mem-wk π (sub-ex θ V) h     = refl
sub-mem-wk π (sub-ex θ V) (t i) = sub-mem-wk π θ i

wk-mem-wk-wk : (π : Γ ⊇ Δ) (i : Δ ∋ A) -> wk-mem (wk-wk {A = B} π) i ≡ t (wk-mem π i)
wk-mem-wk-wk π h     = refl
wk-mem-wk-wk π (t i) = refl

wk-val-var-wk-wk-id : (i : Γ ∋ A) -> wk-val (wk-wk {A = B} wk-id) (var i) ≡ var (t i)
wk-val-var-wk-wk-id i = cong var (begin
  wk-mem (wk-wk wk-id) i ≡⟨ wk-mem-wk-wk wk-id i ⟩
  t (wk-mem wk-id i)     ≡⟨ cong t wk-mem-id ⟩
  t i                    ∎)

sub-mem-ren : (π : Γ ⊇ Δ) (i : Δ ∋ A) -> sub-mem (ren π) i ≡ var (wk-mem π i)
sub-mem-ren (wk-cong π) h     = refl
sub-mem-ren (wk-cong π) (t i) = begin
  sub-mem (sub-wk (wk-wk wk-id) (ren π)) i  ≡⟨ sub-mem-wk (wk-wk wk-id) (ren π) i ⟩
  wk-val (wk-wk wk-id) (sub-mem (ren π) i)  ≡⟨ cong (wk-val (wk-wk wk-id)) (sub-mem-ren π i) ⟩
  wk-val (wk-wk wk-id) (var (wk-mem π i))   ≡⟨ wk-val-var-wk-wk-id (wk-mem π i) ⟩
  var (t (wk-mem π i))                      ∎
sub-mem-ren (wk-wk π) i = begin
  sub-mem (sub-wk (wk-wk wk-id) (ren π)) i  ≡⟨ sub-mem-wk (wk-wk wk-id) (ren π) i ⟩
  wk-val (wk-wk wk-id) (sub-mem (ren π) i)  ≡⟨ cong (wk-val (wk-wk wk-id)) (sub-mem-ren π i) ⟩
  wk-val (wk-wk wk-id) (var (wk-mem π i))   ≡⟨ wk-val-var-wk-wk-id (wk-mem π i) ⟩
  var (t (wk-mem π i))                      ≡˘⟨ cong var (wk-mem-wk-wk π i) ⟩
  var (wk-mem (wk-wk π) i)                  ∎

wk-cong-sub-wk-lemma : (π : Γ' ⊇ Γ) (θ : Γ ⊢ Δ)
                     -> sub-wk (wk-cong {A = A} π) (sub-wk (wk-wk wk-id) θ) ≡ sub-wk (wk-wk wk-id) (sub-wk π θ)
wk-cong-sub-wk-lemma π θ = begin
  sub-wk (wk-cong π) (sub-wk (wk-wk wk-id) θ) ≡⟨ sub-wk-trans (wk-cong π) (wk-wk wk-id) θ ⟩
  sub-wk (wk-wk (wk-trans π wk-id)) θ         ≡⟨ cong (λ w -> sub-wk w θ) (cong wk-wk (wk-trans-comm-id π)) ⟩
  sub-wk (wk-wk (wk-trans wk-id π)) θ         ≡˘⟨ sub-wk-trans (wk-wk wk-id) π θ ⟩
  sub-wk (wk-wk wk-id) (sub-wk π θ)           ∎

wk-cong2-sub-wk-lemma : (π : Γ' ⊇ Γ) (θ : Γ ⊢ Δ)
                      -> sub-wk (wk-cong {A = A} (wk-cong {A = B} π)) (sub-wk (wk-wk (wk-wk wk-id)) θ) ≡ sub-wk (wk-wk (wk-wk wk-id)) (sub-wk π θ)
wk-cong2-sub-wk-lemma π θ = begin
  sub-wk (wk-cong (wk-cong π)) (sub-wk (wk-wk (wk-wk wk-id)) θ) ≡⟨ sub-wk-trans (wk-cong (wk-cong π)) (wk-wk (wk-wk wk-id)) θ ⟩
  sub-wk (wk-wk (wk-wk (wk-trans π wk-id))) θ                   ≡⟨ cong (λ w -> sub-wk w θ) (cong wk-wk (cong wk-wk (wk-trans-comm-id π))) ⟩
  sub-wk (wk-wk (wk-wk (wk-trans wk-id π))) θ                   ≡˘⟨ sub-wk-trans (wk-wk (wk-wk wk-id)) π θ ⟩
  sub-wk (wk-wk (wk-wk wk-id)) (sub-wk π θ)                     ∎

mutual
  wk-sub-val : (π : Γ' ⊇ Γ) (θ : Γ ⊢ Δ) (V : Δ ⊢ᵛ A) -> wk-val π (sub-val θ V) ≡ sub-val (sub-wk π θ) V
  wk-sub-val π θ (var i) = begin _ ≡˘⟨ sub-mem-wk π θ i ⟩ _ ∎
  wk-sub-val π θ (lam M) =
    cong lam (begin
      wk-comp (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) M)
    ≡⟨ wk-sub-comp (wk-cong π) (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) M ⟩
      sub-comp (sub-ex (sub-wk (wk-cong π) (sub-wk (wk-wk wk-id) θ)) (var h)) M
    ≡⟨ cong (λ w -> sub-comp (sub-ex w (var h)) M) (wk-cong-sub-wk-lemma π θ) ⟩
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-wk π θ)) (var h)) M ∎)
  wk-sub-val π θ (pair V1 V2) = cong₂ pair (wk-sub-val π θ V1) (wk-sub-val π θ V2)
  wk-sub-val π θ (pm {A = A'} {B = B'} V W) =
    cong₂ pm (wk-sub-val π θ V)
      (begin
        wk-val (wk-cong (wk-cong π)) (sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) W)
      ≡⟨ wk-sub-val (wk-cong (wk-cong π)) (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) W ⟩
        sub-val (sub-ex (sub-ex (sub-wk (wk-cong (wk-cong π)) (sub-wk (wk-wk (wk-wk wk-id)) θ)) (var (t h))) (var h)) W
      ≡⟨ cong (λ w -> sub-val (sub-ex (sub-ex w (var (t h))) (var h)) W) (wk-cong2-sub-wk-lemma {A = B'} {B = A'} π θ) ⟩
        sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-wk π θ)) (var (t h))) (var h)) W ∎)
  wk-sub-val π θ unit = refl

  wk-sub-comp : (π : Γ' ⊇ Γ) (θ : Γ ⊢ Δ) (M : Δ ⊢ᶜ A) -> wk-comp π (sub-comp θ M) ≡ sub-comp (sub-wk π θ) M
  wk-sub-comp π θ (return V) = cong return (wk-sub-val π θ V)
  wk-sub-comp π θ (push M N) =
    cong₂ push (wk-sub-comp π θ M)
               (begin
                 wk-comp (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) N)
               ≡⟨ wk-sub-comp (wk-cong π) (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) N ⟩
                 sub-comp (sub-ex (sub-wk (wk-cong π) (sub-wk (wk-wk wk-id) θ)) (var h)) N
               ≡⟨ cong (λ w -> sub-comp (sub-ex w (var h)) N) (wk-cong-sub-wk-lemma π θ) ⟩
                 sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-wk π θ)) (var h)) N ∎)
  wk-sub-comp π θ (app V W) = cong₂ app (wk-sub-val π θ V) (wk-sub-val π θ W)
  wk-sub-comp π θ (pm {A = A'} {B = B'} V M) =
    cong₂ pm (wk-sub-val π θ V)
      (begin
        wk-comp (wk-cong (wk-cong π)) (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) M)
      ≡⟨ wk-sub-comp (wk-cong (wk-cong π)) (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) M ⟩
        sub-comp (sub-ex (sub-ex (sub-wk (wk-cong (wk-cong π)) (sub-wk (wk-wk (wk-wk wk-id)) θ)) (var (t h))) (var h)) M
      ≡⟨ cong (λ w -> sub-comp (sub-ex (sub-ex w (var (t h))) (var h)) M) (wk-cong2-sub-wk-lemma {A = B'} {B = A'} π θ) ⟩
        sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-wk π θ)) (var (t h))) (var h)) M ∎)

sub-pre : Γ ⊢ Δ -> Δ ⊇ Ψ -> Γ ⊢ Ψ
sub-pre θ wk-ε              = sub-ε
sub-pre (sub-ex θ V) (wk-cong π) = sub-ex (sub-pre θ π) V
sub-pre (sub-ex θ V) (wk-wk π)   = sub-pre θ π

sub-mem-pre : (θ : Γ ⊢ Δ) (π : Δ ⊇ Ψ) (i : Ψ ∋ A) -> sub-mem (sub-pre θ π) i ≡ sub-mem θ (wk-mem π i)
sub-mem-pre (sub-ex θ V) (wk-cong π) h     = refl
sub-mem-pre (sub-ex θ V) (wk-cong π) (t i) = sub-mem-pre θ π i
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
  cong (λ w -> sub-ex w (var h)) (begin
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
  cong (λ w -> sub-ex w (var h)) (begin
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
  sub-val-wk-pre θ π (var i) = begin _ ≡˘⟨ sub-mem-pre θ π i ⟩ _ ∎
  sub-val-wk-pre θ π (lam M) =
    cong lam (begin
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) (wk-comp (wk-cong π) M)
    ≡⟨ sub-comp-wk-pre (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) (wk-cong π) M ⟩
      sub-comp (sub-ex (sub-pre (sub-wk (wk-wk wk-id) θ) π) (var h)) M
    ≡⟨ cong (λ w -> sub-comp (sub-ex w (var h)) M) (sub-pre-wk-l (wk-wk wk-id) θ π) ⟩
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-pre θ π)) (var h)) M ∎)
  sub-val-wk-pre θ π (pair V1 V2) = cong₂ pair (sub-val-wk-pre θ π V1) (sub-val-wk-pre θ π V2)
  sub-val-wk-pre θ π (pm {A = A'} {B = B'} V W) =
    cong₂ pm (sub-val-wk-pre θ π V)
      (begin
        sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) (wk-val (wk-cong (wk-cong π)) W)
      ≡⟨ sub-val-wk-pre (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) (wk-cong (wk-cong π)) W ⟩
        sub-val (sub-ex (sub-ex (sub-pre (sub-wk (wk-wk (wk-wk wk-id)) θ) π) (var (t h))) (var h)) W
      ≡⟨ cong (λ w -> sub-val (sub-ex (sub-ex w (var (t h))) (var h)) W) (sub-pre-wk-l (wk-wk (wk-wk wk-id)) θ π) ⟩
        sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-pre θ π)) (var (t h))) (var h)) W ∎)
  sub-val-wk-pre θ π unit = refl

  sub-comp-wk-pre : (θ : Γ ⊢ Δ') (π : Δ' ⊇ Δ) (M : Δ ⊢ᶜ A) -> sub-comp θ (wk-comp π M) ≡ sub-comp (sub-pre θ π) M
  sub-comp-wk-pre θ π (return V) = cong return (sub-val-wk-pre θ π V)
  sub-comp-wk-pre θ π (push M N) =
    cong₂ push (sub-comp-wk-pre θ π M)
               (begin
                 sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) (wk-comp (wk-cong π) N)
               ≡⟨ sub-comp-wk-pre (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) (wk-cong π) N ⟩
                 sub-comp (sub-ex (sub-pre (sub-wk (wk-wk wk-id) θ) π) (var h)) N
               ≡⟨ cong (λ w -> sub-comp (sub-ex w (var h)) N) (sub-pre-wk-l (wk-wk wk-id) θ π) ⟩
                 sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-pre θ π)) (var h)) N ∎)
  sub-comp-wk-pre θ π (app V W) = cong₂ app (sub-val-wk-pre θ π V) (sub-val-wk-pre θ π W)
  sub-comp-wk-pre θ π (pm {A = A'} {B = B'} V M) =
    cong₂ pm (sub-val-wk-pre θ π V)
      (begin
        sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) (wk-comp (wk-cong (wk-cong π)) M)
      ≡⟨ sub-comp-wk-pre (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) (wk-cong (wk-cong π)) M ⟩
        sub-comp (sub-ex (sub-ex (sub-pre (sub-wk (wk-wk (wk-wk wk-id)) θ) π) (var (t h))) (var h)) M
      ≡⟨ cong (λ w -> sub-comp (sub-ex (sub-ex w (var (t h))) (var h)) M) (sub-pre-wk-l (wk-wk (wk-wk wk-id)) θ π) ⟩
        sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-pre θ π)) (var (t h))) (var h)) M ∎)

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

wk-beta-pmᵛ : (π : Γ' ⊇ Γ) (V1 : Γ ⊢ᵛ A) (V2 : Γ ⊢ᵛ B) (W : (Γ ∙ A ∙ B) ⊢ᵛ C)
  -> sub-val (sub-ex (sub-ex sub-id (wk-val π V1)) (wk-val π V2)) (wk-val (wk-cong (wk-cong π)) W) ≡ wk-val π (sub-val (sub-ex (sub-ex sub-id V1) V2) W)
wk-beta-pmᵛ π V1 V2 W = begin
    sub-val (sub-ex (sub-ex sub-id (wk-val π V1)) (wk-val π V2)) (wk-val (wk-cong (wk-cong π)) W)
  ≡⟨ sub-val-wk-pre (sub-ex (sub-ex sub-id (wk-val π V1)) (wk-val π V2)) (wk-cong (wk-cong π)) W ⟩
    sub-val (sub-ex (sub-ex (sub-pre sub-id π) (wk-val π V1)) (wk-val π V2)) W
  ≡⟨ cong (λ z -> sub-val (sub-ex (sub-ex z (wk-val π V1)) (wk-val π V2)) W) (sub-pre-id-ren π) ⟩
    sub-val (sub-ex (sub-ex (ren π) (wk-val π V1)) (wk-val π V2)) W
  ≡˘⟨ cong (λ z -> sub-val (sub-ex (sub-ex z (wk-val π V1)) (wk-val π V2)) W) (sub-wk-id-ren π) ⟩
    sub-val (sub-ex (sub-ex (sub-wk π sub-id) (wk-val π V1)) (wk-val π V2)) W
  ≡˘⟨ wk-sub-val π (sub-ex (sub-ex sub-id V1) V2) W ⟩
    wk-val π (sub-val (sub-ex (sub-ex sub-id V1) V2) W) ∎

wk-beta-pmᶜ : (π : Γ' ⊇ Γ) (V1 : Γ ⊢ᵛ A) (V2 : Γ ⊢ᵛ B) (M : (Γ ∙ A ∙ B) ⊢ᶜ C)
  -> sub-comp (sub-ex (sub-ex sub-id (wk-val π V1)) (wk-val π V2)) (wk-comp (wk-cong (wk-cong π)) M) ≡ wk-comp π (sub-comp (sub-ex (sub-ex sub-id V1) V2) M)
wk-beta-pmᶜ π V1 V2 M = begin
    sub-comp (sub-ex (sub-ex sub-id (wk-val π V1)) (wk-val π V2)) (wk-comp (wk-cong (wk-cong π)) M)
  ≡⟨ sub-comp-wk-pre (sub-ex (sub-ex sub-id (wk-val π V1)) (wk-val π V2)) (wk-cong (wk-cong π)) M ⟩
    sub-comp (sub-ex (sub-ex (sub-pre sub-id π) (wk-val π V1)) (wk-val π V2)) M
  ≡⟨ cong (λ z -> sub-comp (sub-ex (sub-ex z (wk-val π V1)) (wk-val π V2)) M) (sub-pre-id-ren π) ⟩
    sub-comp (sub-ex (sub-ex (ren π) (wk-val π V1)) (wk-val π V2)) M
  ≡˘⟨ cong (λ z -> sub-comp (sub-ex (sub-ex z (wk-val π V1)) (wk-val π V2)) M) (sub-wk-id-ren π) ⟩
    sub-comp (sub-ex (sub-ex (sub-wk π sub-id) (wk-val π V1)) (wk-val π V2)) M
  ≡˘⟨ wk-sub-comp π (sub-ex (sub-ex sub-id V1) V2) M ⟩
    wk-comp π (sub-comp (sub-ex (sub-ex sub-id V1) V2) M) ∎

--------------------------------------------------------------------------
-- substitution composition

sub-comp-sub : Γ ⊢ Δ -> Δ ⊢ Ψ -> Γ ⊢ Ψ
sub-comp-sub θ1 sub-ε        = sub-ε
sub-comp-sub θ1 (sub-ex θ2 V) = sub-ex (sub-comp-sub θ1 θ2) (sub-val θ1 V)

sub-mem-sub : (θ1 : Γ ⊢ Δ) (θ2 : Δ ⊢ Ψ) (i : Ψ ∋ A) -> sub-mem (sub-comp-sub θ1 θ2) i ≡ sub-val θ1 (sub-mem θ2 i)
sub-mem-sub θ1 (sub-ex θ2 V) h     = refl
sub-mem-sub θ1 (sub-ex θ2 V) (t i) = sub-mem-sub θ1 θ2 i

sub-comp-sub-wk-r : (θ1 : Γ ⊢ Δ') (π : Δ' ⊇ Δ) (θ2 : Δ ⊢ Ψ) -> sub-comp-sub θ1 (sub-wk π θ2) ≡ sub-comp-sub (sub-pre θ1 π) θ2
sub-comp-sub-wk-r θ1 π sub-ε        = refl
sub-comp-sub-wk-r θ1 π (sub-ex θ2 V) = cong₂ sub-ex (sub-comp-sub-wk-r θ1 π θ2) (sub-val-wk-pre θ1 π V)

sub-comp-sub-wk-l : (ρ : Γ' ⊇ Γ) (θ1 : Γ ⊢ Δ) (θ2 : Δ ⊢ Ψ) -> sub-comp-sub (sub-wk ρ θ1) θ2 ≡ sub-wk ρ (sub-comp-sub θ1 θ2)
sub-comp-sub-wk-l ρ θ1 sub-ε        = refl
sub-comp-sub-wk-l ρ θ1 (sub-ex θ2 V) = cong₂ sub-ex (sub-comp-sub-wk-l ρ θ1 θ2) (begin _ ≡˘⟨ wk-sub-val ρ θ1 V ⟩ _ ∎)

sub-comp-sub-ext1 : (θ1 : Γ ⊢ Δ) (θ2 : Δ ⊢ Ψ)
  -> sub-comp-sub (sub-ex (sub-wk (wk-wk {A = A} wk-id) θ1) (var h)) (sub-ex (sub-wk (wk-wk wk-id) θ2) (var h))
   ≡ sub-ex (sub-wk (wk-wk wk-id) (sub-comp-sub θ1 θ2)) (var h)
sub-comp-sub-ext1 θ1 θ2 =
  cong₂ sub-ex
    (begin
      sub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) θ1) (var h)) (sub-wk (wk-wk wk-id) θ2)
    ≡⟨ sub-comp-sub-wk-r (sub-ex (sub-wk (wk-wk wk-id) θ1) (var h)) (wk-wk wk-id) θ2 ⟩
      sub-comp-sub (sub-pre (sub-wk (wk-wk wk-id) θ1) wk-id) θ2
    ≡⟨ cong (λ w -> sub-comp-sub w θ2) (sub-pre-wk-id (sub-wk (wk-wk wk-id) θ1)) ⟩
      sub-comp-sub (sub-wk (wk-wk wk-id) θ1) θ2
    ≡⟨ sub-comp-sub-wk-l (wk-wk wk-id) θ1 θ2 ⟩
      sub-wk (wk-wk wk-id) (sub-comp-sub θ1 θ2) ∎)
    refl

sub-comp-sub-ext2 : (θ1 : Γ ⊢ Δ) (θ2 : Δ ⊢ Ψ)
  -> sub-comp-sub (sub-ex (sub-ex (sub-wk (wk-wk {A = A} (wk-wk {A = B} wk-id)) θ1) (var (t h))) (var h))
                  (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ2) (var (t h))) (var h))
   ≡ sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-comp-sub θ1 θ2)) (var (t h))) (var h)
sub-comp-sub-ext2 θ1 θ2 =
  cong₂ sub-ex
    (cong₂ sub-ex
      (begin
        sub-comp-sub (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ1) (var (t h))) (var h)) (sub-wk (wk-wk (wk-wk wk-id)) θ2)
      ≡⟨ sub-comp-sub-wk-r (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ1) (var (t h))) (var h)) (wk-wk (wk-wk wk-id)) θ2 ⟩
        sub-comp-sub (sub-pre (sub-wk (wk-wk (wk-wk wk-id)) θ1) wk-id) θ2
      ≡⟨ cong (λ w -> sub-comp-sub w θ2) (sub-pre-wk-id (sub-wk (wk-wk (wk-wk wk-id)) θ1)) ⟩
        sub-comp-sub (sub-wk (wk-wk (wk-wk wk-id)) θ1) θ2
      ≡⟨ sub-comp-sub-wk-l (wk-wk (wk-wk wk-id)) θ1 θ2 ⟩
        sub-wk (wk-wk (wk-wk wk-id)) (sub-comp-sub θ1 θ2) ∎)
      refl)
    refl

mutual
  sub-sub-val : (θ1 : Γ ⊢ Δ) (θ2 : Δ ⊢ Ψ) (V : Ψ ⊢ᵛ A) -> sub-val θ1 (sub-val θ2 V) ≡ sub-val (sub-comp-sub θ1 θ2) V
  sub-sub-val θ1 θ2 (var i) = begin _ ≡˘⟨ sub-mem-sub θ1 θ2 i ⟩ _ ∎
  sub-sub-val θ1 θ2 (lam M) =
    cong lam (begin
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ1) (var h)) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ2) (var h)) M)
    ≡⟨ sub-sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ1) (var h)) (sub-ex (sub-wk (wk-wk wk-id) θ2) (var h)) M ⟩
      sub-comp (sub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) θ1) (var h)) (sub-ex (sub-wk (wk-wk wk-id) θ2) (var h))) M
    ≡⟨ cong (λ w -> sub-comp w M) (sub-comp-sub-ext1 θ1 θ2) ⟩
      sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-comp-sub θ1 θ2)) (var h)) M ∎)
  sub-sub-val θ1 θ2 (pair V1 V2) = cong₂ pair (sub-sub-val θ1 θ2 V1) (sub-sub-val θ1 θ2 V2)
  sub-sub-val θ1 θ2 (pm {A = A'} {B = B'} V W) =
    cong₂ pm (sub-sub-val θ1 θ2 V)
      (begin
        sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ1) (var (t h))) (var h))
                (sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ2) (var (t h))) (var h)) W)
      ≡⟨ sub-sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ1) (var (t h))) (var h))
                     (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ2) (var (t h))) (var h)) W ⟩
        sub-val (sub-comp-sub (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ1) (var (t h))) (var h))
                              (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ2) (var (t h))) (var h))) W
      ≡⟨ cong (λ w -> sub-val w W) (sub-comp-sub-ext2 {A = B'} {B = A'} θ1 θ2) ⟩
        sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-comp-sub θ1 θ2)) (var (t h))) (var h)) W ∎)
  sub-sub-val θ1 θ2 unit = refl

  sub-sub-comp : (θ1 : Γ ⊢ Δ) (θ2 : Δ ⊢ Ψ) (M : Ψ ⊢ᶜ A) -> sub-comp θ1 (sub-comp θ2 M) ≡ sub-comp (sub-comp-sub θ1 θ2) M
  sub-sub-comp θ1 θ2 (return V) = cong return (sub-sub-val θ1 θ2 V)
  sub-sub-comp θ1 θ2 (push M N) =
    cong₂ push (sub-sub-comp θ1 θ2 M)
               (begin
                 sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ1) (var h)) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ2) (var h)) N)
               ≡⟨ sub-sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ1) (var h)) (sub-ex (sub-wk (wk-wk wk-id) θ2) (var h)) N ⟩
                 sub-comp (sub-comp-sub (sub-ex (sub-wk (wk-wk wk-id) θ1) (var h)) (sub-ex (sub-wk (wk-wk wk-id) θ2) (var h))) N
               ≡⟨ cong (λ w -> sub-comp w N) (sub-comp-sub-ext1 θ1 θ2) ⟩
                 sub-comp (sub-ex (sub-wk (wk-wk wk-id) (sub-comp-sub θ1 θ2)) (var h)) N ∎)
  sub-sub-comp θ1 θ2 (app V W) = cong₂ app (sub-sub-val θ1 θ2 V) (sub-sub-val θ1 θ2 W)
  sub-sub-comp θ1 θ2 (pm {A = A'} {B = B'} V M) =
    cong₂ pm (sub-sub-val θ1 θ2 V)
      (begin
        sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ1) (var (t h))) (var h))
                 (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ2) (var (t h))) (var h)) M)
      ≡⟨ sub-sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ1) (var (t h))) (var h))
                      (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ2) (var (t h))) (var h)) M ⟩
        sub-comp (sub-comp-sub (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ1) (var (t h))) (var h))
                               (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ2) (var (t h))) (var h))) M
      ≡⟨ cong (λ w -> sub-comp w M) (sub-comp-sub-ext2 {A = B'} {B = A'} θ1 θ2) ⟩
        sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (sub-comp-sub θ1 θ2)) (var (t h))) (var h)) M ∎)

mutual
  sub-val-ren : (π : Γ ⊇ Δ) (V : Δ ⊢ᵛ A) -> sub-val (ren π) V ≡ wk-val π V
  sub-val-ren π (var i) = sub-mem-ren π i
  sub-val-ren π (lam M) = cong lam (sub-comp-ren (wk-cong π) M)
  sub-val-ren π (pair V1 V2) = cong₂ pair (sub-val-ren π V1) (sub-val-ren π V2)
  sub-val-ren π (pm {A = A'} {B = B'} V W) =
    cong₂ pm (sub-val-ren π V)
      (begin
        sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (ren π)) (var (t h))) (var h)) W
      ≡˘⟨ cong (λ θ -> sub-val θ W) (ren-cong2 {A = B'} {B = A'} π) ⟩
        sub-val (ren (wk-cong (wk-cong π))) W
      ≡⟨ sub-val-ren (wk-cong (wk-cong π)) W ⟩
        wk-val (wk-cong (wk-cong π)) W ∎)
  sub-val-ren π unit    = refl

  sub-comp-ren : (π : Γ ⊇ Δ) (M : Δ ⊢ᶜ A) -> sub-comp (ren π) M ≡ wk-comp π M
  sub-comp-ren π (return V) = cong return (sub-val-ren π V)
  sub-comp-ren π (push M N) = cong₂ push (sub-comp-ren π M) (sub-comp-ren (wk-cong π) N)
  sub-comp-ren π (app V W)  = cong₂ app (sub-val-ren π V) (sub-val-ren π W)
  sub-comp-ren π (pm {A = A'} {B = B'} V M) =
    cong₂ pm (sub-val-ren π V)
      (begin
        sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) (ren π)) (var (t h))) (var h)) M
      ≡˘⟨ cong (λ θ -> sub-comp θ M) (ren-cong2 {A = B'} {B = A'} π) ⟩
        sub-comp (ren (wk-cong (wk-cong π))) M
      ≡⟨ sub-comp-ren (wk-cong (wk-cong π)) M ⟩
        wk-comp (wk-cong (wk-cong π)) M ∎)

ren-wk-id : ren (wk-id {Γ}) ≡ sub-id {Γ}
ren-wk-id {ε}     = refl
ren-wk-id {Γ ∙ A} = cong (λ θ -> sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) (ren-wk-id {Γ})

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
sub-wk-as-comp-ren π (sub-ex θ V) = cong₂ sub-ex (sub-wk-as-comp-ren π θ) (begin _ ≡˘⟨ sub-val-ren π V ⟩ _ ∎)

--------------------------------------------------------------------------
-- fundamental lemma

fund-lam-eq : (θ : Γ ⊢ Δ) (π : Γ' ⊇ Γ) (V : Γ' ⊢ᵛ A) (M : (Δ ∙ A) ⊢ᶜ B)
  -> sub-comp (sub-ex sub-id V) (wk-comp (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) M))
   ≡ sub-comp (sub-ex (sub-wk π θ) V) M
fund-lam-eq θ π V M = begin
    sub-comp (sub-ex sub-id V) (wk-comp (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) M))
  ≡⟨ sub-comp-wk-pre (sub-ex sub-id V) (wk-cong π) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) M) ⟩
    sub-comp (sub-ex (sub-pre sub-id π) V) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) M)
  ≡⟨ cong (λ ξ -> sub-comp (sub-ex ξ V) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) M)) (sub-pre-id-ren π) ⟩
    sub-comp (sub-ex (ren π) V) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) M)
  ≡⟨ sub-sub-comp (sub-ex (ren π) V) (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) M ⟩
    sub-comp (sub-ex (sub-comp-sub (sub-ex (ren π) V) (sub-wk (wk-wk wk-id) θ)) V) M
  ≡⟨ cong (λ ξ -> sub-comp (sub-ex ξ V) M)
          (begin
             sub-comp-sub (sub-ex (ren π) V) (sub-wk (wk-wk wk-id) θ)
           ≡⟨ sub-comp-sub-wk-r (sub-ex (ren π) V) (wk-wk wk-id) θ ⟩
             sub-comp-sub (sub-pre (ren π) wk-id) θ
           ≡⟨ cong (λ ρ -> sub-comp-sub ρ θ) (sub-pre-wk-id (ren π)) ⟩
             sub-comp-sub (ren π) θ
           ≡˘⟨ sub-wk-as-comp-ren π θ ⟩
             sub-wk π θ ∎) ⟩
    sub-comp (sub-ex (sub-wk π θ) V) M ∎

fund-push-eq : (θ : Γ ⊢ Δ) (V : Γ ⊢ᵛ A) (N : (Δ ∙ A) ⊢ᶜ B)
  -> sub-comp (sub-ex sub-id V) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) N)
   ≡ sub-comp (sub-ex θ V) N
fund-push-eq θ V N = begin
    sub-comp (sub-ex sub-id V) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) N)
  ≡⟨ sub-sub-comp (sub-ex sub-id V) (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) N ⟩
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

fund-pm-eqᵛ : (θ : Γ ⊢ Δ) (V1 : Γ ⊢ᵛ A) (V2 : Γ ⊢ᵛ B) (W : (Δ ∙ A ∙ B) ⊢ᵛ C)
  -> sub-val (sub-ex (sub-ex sub-id V1) V2) (sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) W)
   ≡ sub-val (sub-ex (sub-ex θ V1) V2) W
fund-pm-eqᵛ θ V1 V2 W = begin
    sub-val (sub-ex (sub-ex sub-id V1) V2) (sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) W)
  ≡⟨ sub-sub-val (sub-ex (sub-ex sub-id V1) V2) (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) W ⟩
    sub-val (sub-ex (sub-ex (sub-comp-sub (sub-ex (sub-ex sub-id V1) V2) (sub-wk (wk-wk (wk-wk wk-id)) θ)) V1) V2) W
  ≡⟨ cong (λ ρ -> sub-val (sub-ex (sub-ex ρ V1) V2) W)
          (begin
             sub-comp-sub (sub-ex (sub-ex sub-id V1) V2) (sub-wk (wk-wk (wk-wk wk-id)) θ)
           ≡⟨ sub-comp-sub-wk-r (sub-ex (sub-ex sub-id V1) V2) (wk-wk (wk-wk wk-id)) θ ⟩
             sub-comp-sub (sub-pre sub-id wk-id) θ
           ≡⟨ cong (λ ρ -> sub-comp-sub ρ θ) (sub-pre-wk-id sub-id) ⟩
             sub-comp-sub sub-id θ
           ≡⟨ sub-comp-sub-idl θ ⟩
             θ ∎) ⟩
    sub-val (sub-ex (sub-ex θ V1) V2) W ∎

fund-pm-eqᶜ : (θ : Γ ⊢ Δ) (V1 : Γ ⊢ᵛ A) (V2 : Γ ⊢ᵛ B) (M : (Δ ∙ A ∙ B) ⊢ᶜ C)
  -> sub-comp (sub-ex (sub-ex sub-id V1) V2) (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) M)
   ≡ sub-comp (sub-ex (sub-ex θ V1) V2) M
fund-pm-eqᶜ θ V1 V2 M = begin
    sub-comp (sub-ex (sub-ex sub-id V1) V2) (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) M)
  ≡⟨ sub-sub-comp (sub-ex (sub-ex sub-id V1) V2) (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) M ⟩
    sub-comp (sub-ex (sub-ex (sub-comp-sub (sub-ex (sub-ex sub-id V1) V2) (sub-wk (wk-wk (wk-wk wk-id)) θ)) V1) V2) M
  ≡⟨ cong (λ ρ -> sub-comp (sub-ex (sub-ex ρ V1) V2) M)
          (begin
             sub-comp-sub (sub-ex (sub-ex sub-id V1) V2) (sub-wk (wk-wk (wk-wk wk-id)) θ)
           ≡⟨ sub-comp-sub-wk-r (sub-ex (sub-ex sub-id V1) V2) (wk-wk (wk-wk wk-id)) θ ⟩
             sub-comp-sub (sub-pre sub-id wk-id) θ
           ≡⟨ cong (λ ρ -> sub-comp-sub ρ θ) (sub-pre-wk-id sub-id) ⟩
             sub-comp-sub sub-id θ
           ≡⟨ sub-comp-sub-idl θ ⟩
             θ ∎) ⟩
    sub-comp (sub-ex (sub-ex θ V1) V2) M ∎
