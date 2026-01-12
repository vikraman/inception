module Inception.LamBarMuMuTilde.CBV (R : Set) where

open import Inception.LamBarMuMuTilde.Syntax

open import Level
open import Data.Unit
open import Data.Empty
open import Data.Product as P
open import Function as F hiding (_∋_)
open import Data.Sum as S
open import Relation.Binary.PropositionalEquality
open import Inception.Prelude

infixr 4 _；_

_；_ : ∀ {ℓ} {A B C : Set ℓ} -> (A -> B) -> (B -> C) -> (A -> C)
f ； g = g ∘ f

idf : ∀ {ℓ} {A : Set ℓ} -> A -> A
idf a = a

assocl : ∀ {ℓ} {A B C : Set ℓ} -> A × (B × C) -> (A × B) × C
assocl (a , (b , c)) = (a , b) , c

shuffle : ∀ {ℓ} {A B C : Set ℓ} -> (A × B) × C -> (A × C) × B
shuffle ((a , b) , c) = (a , c) , b

open import Inception.Cont.Base

K : Set -> Set
K = K[ R ]
T = K[_]-Monad {x = zero} R

open import Inception.Monad.Base using (Monad)
open Monad T public

τ : {X Y : Set} -> X × K Y -> K (X × Y)
τ (x , ky) k = ky \z -> k (x , z)

cbv : {X Y : Set} -> (X -> K Y) -> R ^ (R ^ Y × X)
cbv f (k , x) = f x k

eval : {X Y : Set} -> Y ^ X × X -> Y
eval = uncurry′ idf

⟦_⟧ : Ty -> Set
⟦ A `⇒ B ⟧ = ⟦ A ⟧ -> K ⟦ B ⟧

⟦_⟧ⁿ : Env -> Set
⟦ ε ⟧ⁿ = ⊤
⟦ Γ ∙ A ⟧ⁿ = ⟦ Γ ⟧ⁿ × ⟦ A ⟧

⟦_⟧ⁿ̃ : Env -> Set
⟦ ε ⟧ⁿ̃ = ⊥
⟦ Δ ∙ A ⟧ⁿ̃ = ⟦ Δ ⟧ⁿ̃ ⊎ ⟦ A ⟧

-- ⟦_⟧ʷ : Γ ⊇ Δ -> ⟦ Γ ⟧ⁿ -> ⟦ Δ ⟧ⁿ
-- ⟦ wk-ε ⟧ʷ = idf
-- ⟦ wk-cong π ⟧ʷ = < proj₁ ； ⟦ π ⟧ʷ , proj₂ >
-- ⟦ wk-wk π ⟧ʷ = proj₁ ； ⟦ π ⟧ʷ

⟦_⟧ᵐ : Γ ∋ A -> ⟦ Γ ⟧ⁿ -> ⟦ A ⟧
⟦ z ⟧ᵐ = proj₂
⟦ s x ⟧ᵐ = proj₁ ； ⟦ x ⟧ᵐ

⟦_⟧ᵐ̃ : Δ ∋ A -> ⟦ A ⟧ -> ⟦ Δ ⟧ⁿ̃
⟦ z ⟧ᵐ̃ = inj₂
⟦ s i ⟧ᵐ̃ = ⟦ i ⟧ᵐ̃ ； inj₁

mutual
  ⟦_⟧ᶜ : Γ ⊢ Δ -> ⟦ Γ ⟧ⁿ × R ^ ⟦ Δ ⟧ⁿ̃ -> R
  ⟦ cut e t ⟧ᶜ = < ⟦ t ⟧ᵗ , ⟦ e ⟧ᵉ > ； eval

  ⟦_⟧ᵛ : Γ ⊢ᵛ A ∣ Δ -> ⟦ Γ ⟧ⁿ × R ^ ⟦ Δ ⟧ⁿ̃ -> ⟦ A ⟧
  ⟦ var i ⟧ᵛ = proj₁ ； ⟦ i ⟧ᵐ
  ⟦ lam t ⟧ᵛ = curry′ (shuffle ； ⟦ t ⟧ᵗ)

  ⟦_⟧ᵗ : Γ ⊢ᵗ A ∣ Δ -> ⟦ Γ ⟧ⁿ × R ^ ⟦ Δ ⟧ⁿ̃ -> K ⟦ A ⟧
  ⟦ ret v ⟧ᵗ = ⟦ v ⟧ᵛ ； η
  ⟦ μ c ⟧ᵗ = councurry (curry′ ⟦ c ⟧ᶜ)

  ⟦_⟧ᵉ : Γ ∣ A ⊢ᵉ Δ -> ⟦ Γ ⟧ⁿ × R ^ ⟦ Δ ⟧ⁿ̃ -> R ^ ⟦ A ⟧
  ⟦ covar i ⟧ᵉ = proj₂ ； ([ R ]^ ⟦ i ⟧ᵐ̃)
  ⟦ app v e ⟧ᵉ = < ⟦ e ⟧ᵉ , ⟦ v ⟧ᵛ > ； η ； [ R ]^ cbv
  ⟦ μ̃ c ⟧ᵉ = curry′ (shuffle ； ⟦ c ⟧ᶜ)
