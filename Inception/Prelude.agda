module Inception.Prelude where

open import Function
open import Level

open import Agda.Primitive using (Level)

open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax) public

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; cong-app; dcong₂; sym; trans; subst; subst₂; cong-∘)
open Eq.≡-Reasoning

--postulate
--  TODO : ∀ {a} {A : Set a} → A

{-# BUILTIN REWRITE _≡_ #-}

module _ where
  postulate
    I : Set
    i₀ i₁ : I
    seg : i₀ ≡ i₁

  module _ {p} {P : Set p} where
    postulate
      I-rec : (p₀ p₁ : P) (p : p₀ ≡ p₁) → I → P
      I-rec-i0 : ∀ {p₀} {p₁} {p} → I-rec p₀ p₁ p i₀ ≡ p₀
      {-# REWRITE I-rec-i0 #-}
      I-rec-i1 : ∀ {p₀} {p₁} {p} → I-rec p₀ p₁ p i₁ ≡ p₁
      {-# REWRITE I-rec-i1 #-}
      I-rec-seg : ∀ {p₀} {p₁} {p} → cong (I-rec p₀ p₁ p) seg ≡ p

funext : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
funext {f = f} {g = g} H = cong (flip \a → I-rec (f a) (g a) (H a)) seg

happly : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
happly p x = cong (_$ x) p

happly-funext : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} (H : (x : A) → f x ≡ g x) → ∀ x → happly (funext H) x ≡ H x
happly-funext {f = f} {g = g} H x =
  happly (funext H) x                                         ≡⟨ refl ⟩
  cong (_$ x) (cong (flip \a → I-rec (f a) (g a) (H a)) seg) ≡⟨ sym (cong-∘ seg) ⟩
  cong ((_$ x) ∘ (flip \a → I-rec (f a) (g a) (H a))) seg    ≡⟨ I-rec-seg ⟩
  H x ∎

-- categorical combinators
infixr 4 _；_

_；_ : ∀ {ℓ} {A B C : Set ℓ} → (A → B) → (B → C) → (A → C)
f ； g = g ∘ f

idf : ∀ {ℓ} {A : Set ℓ} → A → A
idf a = a

assocl : ∀ {ℓ} {A B C : Set ℓ} → A × (B × C) → (A × B) × C
assocl (a , (b , c)) = (a , b) , c

shuffle : ∀ {ℓ} {A B C : Set ℓ} → (A × B) × C → (A × C) × B
shuffle ((a , b) , c) = (a , c) , b

-- functions
infixr 20 _^_

_^_ : ∀ {r a} (R : Set r) (A : Set a) → Set (r ⊔ a)
R ^ A = A → R

[_]^_ : ∀ {r a b} (R : Set r) {A : Set a} {B : Set b} → (A → B) → (R ^ B) → (R ^ A)
[ R ]^ f = \k a → k (f a)

ev : ∀ {r a} {R : Set r} {A : Set a} → R ^ A × A → R
ev (f , a) = f a

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

ql : ⊥ → (A : Set) → A
ql () b

-- generic reflexive and transitive closure
module RTC {A : Set} (_~>_ : A → A → Set) where

  data _~>*_ : A → A → Set where

    _◼ : (a : A) → a ~>* a

    _~>⟨_⟩_ : (a : A) → {b c : A} → a ~> b → b ~>* c → a ~>* c

  infix  25 _◼
  infixr 20 _~>⟨_⟩_
