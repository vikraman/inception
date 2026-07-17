{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Equality where

open import Agda.Primitive using (Level)

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; cong-app; dcong₂; sym; trans; subst; subst₂)
open Eq.≡-Reasoning

import Relation.Binary.HeterogeneousEquality as H

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

-- https://stackoverflow.com/questions/56304634/is-functional-extensionality-with-dependent-functions-consistent
extensionality' : ∀ {A : Set}{B : A → Set}{f g : ∀ a → B a} → (∀ x → f x ≡ g x) → f ≡ g
extensionality' {A}{B}{f}{g} e =
    H.≅-to-≡ (H.cong (λ f x → proj₂ (f x)) (H.≡-to-≅ (extensionality λ a → cong (a ,_) (e a))))

dcong₂-irr : {a b c : Level} → ∀ {A : Set a} {B : A → Set b} {C : Set c}
            (f : (x : A) → .(B x) → C) {x₁ x₂} .{y₁ y₂}
          → (p : x₁ ≡ x₂)
          → f x₁ y₁ ≡ f x₂ y₂
dcong₂-irr f refl = refl

pair-eq : {A B : Set} {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)
pair-eq a₁≡a₂ b₁≡b₂ = cong₂ (λ x y → x , y) a₁≡a₂ b₁≡b₂

proj₁-eq : {A B : Set} {a₁ a₂ : A} {b₁ b₂ : B} → (a₁ , b₁) ≡ (a₂ , b₂) → a₁ ≡ a₂
proj₁-eq refl = refl

proj₂-eq : {A B : Set} {a₁ a₂ : A} {b₁ b₂ : B} → (a₁ , b₁) ≡ (a₂ , b₂) → b₁ ≡ b₂
proj₂-eq refl = refl

proj₁-d-eq : {a b : Level} {A : Set a} {x : A} {b : A → Set b} {p₁ p₂ : Σ[ x ∈ A ] b x}
             → p₁ ≡ p₂
             → proj₁ p₁ ≡ proj₁ p₂
proj₁-d-eq refl = refl

data ⊥ : Set where

ql : ⊥ → (A : Set) → A
ql () b
