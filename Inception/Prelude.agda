module Inception.Prelude where

open import Level
open import Function

open import Agda.Primitive using (Level)

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Empty using (⊥)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; cong-app; dcong₂; sym; trans; subst; subst₂; cong-∘)
open Eq.≡-Reasoning

import Relation.Binary.HeterogeneousEquality as H

postulate
  TODO : ∀ {a} {A : Set a} -> A

{-# BUILTIN REWRITE _≡_ #-}

module _ where
  postulate
    I : Set
    i0 i1 : I
    seg : i0 ≡ i1

  module _ {p} {P : Set p} where
    postulate
      I-rec : (p0 p1 : P) (p : p0 ≡ p1) -> I -> P
      I-rec-i0 : ∀ {p0} {p1} {p} -> I-rec p0 p1 p i0 ≡ p0
      {-# REWRITE I-rec-i0 #-}
      I-rec-i1 : ∀ {p0} {p1} {p} -> I-rec p0 p1 p i1 ≡ p1
      {-# REWRITE I-rec-i1 #-}
      I-rec-seg : ∀ {p0} {p1} {p} -> cong (I-rec p0 p1 p) seg ≡ p

funext : ∀ {a b} {A : Set a} {B : Set b} {f g : A -> B} -> ((x : A) -> f x ≡ g x) -> f ≡ g
funext {f = f} {g = g} H = cong (flip \a -> I-rec (f a) (g a) (H a)) seg

happly : ∀ {a b} {A : Set a} {B : Set b} {f g : A -> B} -> f ≡ g -> (x : A) -> f x ≡ g x
happly p x = cong (_$ x) p

happly-funext : ∀ {a b} {A : Set a} {B : Set b} {f g : A -> B} (H : (x : A) -> f x ≡ g x) -> ∀ x -> happly (funext H) x ≡ H x
happly-funext {f = f} {g = g} H x = let open Eq.≡-Reasoning in
  happly (funext H) x                                         ≡⟨ refl ⟩
  cong (_$ x) (cong (flip \a -> I-rec (f a) (g a) (H a)) seg) ≡⟨ sym (cong-∘ seg) ⟩
  cong ((_$ x) ∘ (flip \a -> I-rec (f a) (g a) (H a))) seg    ≡⟨ I-rec-seg ⟩
  H x ∎

-- functions
infixr 20 _^_

_^_ : ∀ {r a} (R : Set r) (A : Set a) -> Set (r ⊔ a)
R ^ A = A -> R

[_]^_ : ∀ {r a b} (R : Set r) {A : Set a} {B : Set b} -> (A -> B) -> (R ^ B) -> (R ^ A)
[ R ]^ f = \k a -> k (f a)

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

--data ⊥ : Set where

ql : ⊥ → (A : Set) → A
ql () b
