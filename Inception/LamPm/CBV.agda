{-# OPTIONS --no-postfix-projections #-}

module Inception.LamPm.CBV (R : Set) where

open import Inception.LamPm.Syntax

open import Data.Unit
open import Data.Product as P
open import Function as F hiding (_∋_)
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Inception.Prelude

infixr 4 _；_

_；_ : ∀ {ℓ} {A B C : Set ℓ} -> (A -> B) -> (B -> C) -> (A -> C)
f ； g = g ∘ f

idf : ∀ {ℓ} {A : Set ℓ} -> A -> A
idf a = a

assocl : ∀ {ℓ} {A B C : Set ℓ} -> A × (B × C) -> (A × B) × C
assocl (a , (b , c)) = (a , b) , c

K : Set -> Set
K X = (X -> R) -> R

infix 5 _♯

_♯ : {X Y : Set} -> (X -> K Y) -> K X -> K Y
(f ♯) kx k = kx \x -> f x k

η : {X : Set} -> X -> K X
η x k = k x

τ : {X Y : Set} -> X × K Y -> K (X × Y)
τ (x , ky) k = ky \z -> k (x , z)

⟦_⟧ : Ty -> Set
⟦ `Unit ⟧  = ⊤
⟦ A `× B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A `⇒ B ⟧ = ⟦ A ⟧ -> K ⟦ B ⟧

⟦_⟧ˣ : Ctx -> Set
⟦ ε ⟧ˣ     = ⊤
⟦ Γ ∙ A ⟧ˣ = ⟦ Γ ⟧ˣ × ⟦ A ⟧

⟦_⟧ʷ : Γ ⊇ Δ -> ⟦ Γ ⟧ˣ -> ⟦ Δ ⟧ˣ
⟦ wk-ε ⟧ʷ      = idf
⟦ wk-cong π ⟧ʷ = < proj₁ ； ⟦ π ⟧ʷ , proj₂ >
⟦ wk-wk π ⟧ʷ   = proj₁ ； ⟦ π ⟧ʷ

⟦_⟧ᵐ : Γ ∋ A -> ⟦ Γ ⟧ˣ -> ⟦ A ⟧
⟦ h ⟧ᵐ   = proj₂
⟦ t x ⟧ᵐ = proj₁ ； ⟦ x ⟧ᵐ

mutual
  ⟦_⟧ᵛ : Γ ⊢ᵛ A -> ⟦ Γ ⟧ˣ -> ⟦ A ⟧
  ⟦ var i ⟧ᵛ    = ⟦ i ⟧ᵐ
  ⟦ lam M ⟧ᵛ    = curry ⟦ M ⟧ᶜ
  ⟦ pair V W ⟧ᵛ = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ >
  ⟦ pm V W ⟧ᵛ   = < idf , ⟦ V ⟧ᵛ > ； assocl ； ⟦ W ⟧ᵛ
  ⟦ unit ⟧ᵛ     = const tt

  ⟦_⟧ᶜ : Γ ⊢ᶜ A -> ⟦ Γ ⟧ˣ -> K ⟦ A ⟧
  ⟦ return V ⟧ᶜ = ⟦ V ⟧ᵛ ； η
  ⟦ push M N ⟧ᶜ = < idf , ⟦ M ⟧ᶜ > ； τ ； ⟦ N ⟧ᶜ ♯
  ⟦ app V W ⟧ᶜ  = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ > ； uncurry idf
  ⟦ pm V M ⟧ᶜ   = < idf , ⟦ V ⟧ᵛ > ； assocl ； ⟦ M ⟧ᶜ

⟦_⟧ˢ : Γ ⊢ Δ -> ⟦ Γ ⟧ˣ -> ⟦ Δ ⟧ˣ
⟦ sub-ε ⟧ˢ      = const tt
⟦ sub-ex θ V ⟧ˢ = < ⟦ θ ⟧ˢ , ⟦ V ⟧ᵛ >

-- coherences

wk-id-coh : ⟦ wk-id {Γ} ⟧ʷ ≡ id
wk-id-coh {ε}     = refl
wk-id-coh {Γ ∙ A} rewrite wk-id-coh {Γ} = refl
{-# REWRITE wk-id-coh #-}

wk-mem-coh : (π : Γ ⊇ Δ) (i : Δ ∋ A) -> ⟦ wk-mem π i ⟧ᵐ ≡ (⟦ π ⟧ʷ ； ⟦ i ⟧ᵐ)
wk-mem-coh (wk-cong π) h     = refl
wk-mem-coh (wk-cong π) (t i) rewrite wk-mem-coh π i = refl
wk-mem-coh (wk-wk π)   h     rewrite wk-mem-coh π h = refl
wk-mem-coh (wk-wk π)   (t i) rewrite wk-mem-coh π (t i) = refl

mutual
  wk-val-coh : (π : Γ ⊇ Δ) (V : Δ ⊢ᵛ A) -> ⟦ wk-val π V ⟧ᵛ ≡ (⟦ π ⟧ʷ ； ⟦ V ⟧ᵛ)
  wk-val-coh π (var i)      rewrite wk-mem-coh π i = refl
  wk-val-coh π (lam M)      rewrite wk-comp-coh (wk-cong π) M = refl
  wk-val-coh π (pair V1 V2) rewrite wk-val-coh π V1 | wk-val-coh π V2 = refl
  wk-val-coh π (pm V W)     rewrite wk-val-coh π V | wk-val-coh (wk-cong (wk-cong π)) W = refl
  wk-val-coh π unit         = refl

  wk-comp-coh : (π : Γ ⊇ Δ) (M : Δ ⊢ᶜ A) -> ⟦ wk-comp π M ⟧ᶜ ≡ (⟦ π ⟧ʷ ； ⟦ M ⟧ᶜ)
  wk-comp-coh π (return V) rewrite wk-val-coh π V = refl
  wk-comp-coh π (push M N) rewrite wk-comp-coh π M | wk-comp-coh (wk-cong π) N = refl
  wk-comp-coh π (app V W)  rewrite wk-val-coh π V | wk-val-coh π W = refl
  wk-comp-coh π (pm V M)   rewrite wk-val-coh π V | wk-comp-coh (wk-cong (wk-cong π)) M = refl

{-# REWRITE wk-val-coh #-}
{-# REWRITE wk-comp-coh #-}

sub-mem-coh : (θ : Γ ⊢ Δ) (i : Δ ∋ A) -> ⟦ sub-mem θ i ⟧ᵛ ≡ (⟦ θ ⟧ˢ ； ⟦ i ⟧ᵐ)
sub-mem-coh (sub-ex θ V) h     = refl
sub-mem-coh (sub-ex θ V) (t i) rewrite sub-mem-coh θ i = refl
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
  sub-val-coh θ (var i)      = refl
  sub-val-coh θ (lam M)      rewrite sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) M = refl
  sub-val-coh θ (pair V1 V2) rewrite sub-val-coh θ V1 | sub-val-coh θ V2 = refl
  sub-val-coh θ (pm V W)     rewrite sub-val-coh θ V | sub-val-coh (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) W = refl
  sub-val-coh θ unit         = refl

  sub-comp-coh : (θ : Γ ⊢ Δ) (M : Δ ⊢ᶜ A) -> ⟦ sub-comp θ M ⟧ᶜ ≡ (⟦ θ ⟧ˢ ； ⟦ M ⟧ᶜ)
  sub-comp-coh θ (return V) rewrite sub-val-coh θ V = refl
  sub-comp-coh θ (push M N) rewrite sub-comp-coh θ M | sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) N = refl
  sub-comp-coh θ (app V W)  rewrite sub-val-coh θ V | sub-val-coh θ W = refl
  sub-comp-coh θ (pm V M)   rewrite sub-val-coh θ V | sub-comp-coh (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) M = refl

{-# REWRITE sub-val-coh #-}
{-# REWRITE sub-comp-coh #-}

--------------------------------------------------------------------------
-- semantics of CK machine

module CK where
  open import Inception.LamPm.CK

  ⟦_⟧ᵏ : Γ ⊢ᵏ A ⇒ B -> ⟦ Γ ⟧ˣ -> (R ^ ⟦ B ⟧) -> (R ^ ⟦ A ⟧)
  ⟦ ε ⟧ᵏ        γ k = k
  ⟦ N ∷ K ⟧ᵏ    γ k = \a -> ⟦ N ⟧ᶜ (γ , a) (⟦ K ⟧ᵏ γ k)
  ⟦ N pm∷ K ⟧ᵏ  γ k = \{ (a , b) -> ⟦ N ⟧ᶜ ((γ , a) , b) (⟦ K ⟧ᵏ γ k) }
  ⟦ W pmᵛ∷ K ⟧ᵏ γ k = \{ (a , b) -> ⟦ K ⟧ᵏ γ k (⟦ W ⟧ᵛ ((γ , a) , b)) }

  ⟦_⟧ᶜᶠᵍ : Cfg Γ B -> ⟦ Γ ⟧ˣ -> (R ^ ⟦ B ⟧) -> R
  ⟦ ⟨ M ∥ K ⟩ ⟧ᶜᶠᵍ γ k = ⟦ M ⟧ᶜ γ (⟦ K ⟧ᵏ γ k)
  ⟦ [ V ∥ K ] ⟧ᶜᶠᵍ γ k = ⟦ K ⟧ᵏ γ k (⟦ V ⟧ᵛ γ)

--------------------------------------------------------------------------
-- semantics of CEK machine

module CEK where
  open import Inception.LamPm.CEK

  mutual
    ⟦_⟧ⱽ : Value A -> ⟦ A ⟧
    ⟦ unit ⟧ⱽ     = tt
    ⟦ pair v w ⟧ⱽ = ⟦ v ⟧ⱽ , ⟦ w ⟧ⱽ
    ⟦ clo N ρ ⟧ⱽ  = \a -> ⟦ N ⟧ᶜ (⟦ ρ ⟧ᴱ , a)

    ⟦_⟧ᴱ : Env Γ -> ⟦ Γ ⟧ˣ
    ⟦ ∅ ⟧ᴱ     = tt
    ⟦ ρ ∷ v ⟧ᴱ = ⟦ ρ ⟧ᴱ , ⟦ v ⟧ⱽ

    ⟦_⟧ᴷ : Kont A B -> (R ^ ⟦ B ⟧) -> (R ^ ⟦ A ⟧)
    ⟦ ε ⟧ᴷ         k = k
    ⟦ N ◂ ρ ∷ κ ⟧ᴷ k = \a -> ⟦ N ⟧ᶜ (⟦ ρ ⟧ᴱ , a) (⟦ κ ⟧ᴷ k)

  ⟦_⟧ᶜᶠᵍ : Cfg B -> (R ^ ⟦ B ⟧) -> R
  ⟦ ⟨ M ∥ ρ ∥ κ ⟩ ⟧ᶜᶠᵍ k = ⟦ M ⟧ᶜ ⟦ ρ ⟧ᴱ (⟦ κ ⟧ᴷ k)
  ⟦ ⟨ v ∥ κ ⟩ ⟧ᶜᶠᵍ     k = ⟦ κ ⟧ᴷ k ⟦ v ⟧ⱽ
