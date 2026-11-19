module Inception.Prelude where

open import Data.Empty public
  using (⊥)
open import Data.Nat public
  using (ℕ; zero; suc; _+_)
open import Data.Product public
  using (_×_; _,_; <_,_>; ∃; ∃-syntax; Σ; Σ-syntax; curry; curry′; map₁; map₂; proj₁; proj₂; uncurry; uncurry′)
open import Data.Sum public
  using (_⊎_; inj₁; inj₂; [_,_]; [_,_]′)
open import Data.Unit public
  using (⊤; tt)
open import Function public
  using (_$_; _∘_; const; flip; id)
open import Level public
  using (0ℓ; Level; _⊔_)
open import Relation.Binary.PropositionalEquality public
  using (_≡_; _≢_; refl; cong; cong₂; cong-app; dcong₂; sym; trans; subst; subst₂; cong-∘; module ≡-Reasoning)

open ≡-Reasoning

{-# BUILTIN REWRITE _≡_ #-}

--------------------------------------------------------------------------
-- interval and function extensionality

module _ where
  postulate
    I : Set
    i₀ i₁ : I
    seg : i₀ ≡ i₁

  module _ {p} {P : Set p} where
    postulate
      I-rec : (p₀ p₁ : P) (p : p₀ ≡ p₁) → I → P
      I-rec-i0-β : ∀ {p₀} {p₁} {p} → I-rec p₀ p₁ p i₀ ≡ p₀
      {-# REWRITE I-rec-i0-β #-}
      I-rec-i1-β : ∀ {p₀} {p₁} {p} → I-rec p₀ p₁ p i₁ ≡ p₁
      {-# REWRITE I-rec-i1-β #-}
      I-rec-seg : ∀ {p₀} {p₁} {p} → cong (I-rec p₀ p₁ p) seg ≡ p

funext : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g
funext {f = f} {g = g} H = cong (flip λ a → I-rec (f a) (g a) (H a)) seg

happly : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
happly p x = cong (_$ x) p

happly-funext : ∀ {a b} {A : Set a} {B : Set b} {f g : A → B} (H : (x : A) → f x ≡ g x) → ∀ x → happly (funext H) x ≡ H x
happly-funext {f = f} {g = g} H x =
  happly (funext H) x                                         ≡⟨ refl ⟩
  cong (_$ x) (cong (flip λ a → I-rec (f a) (g a) (H a)) seg) ≡⟨ sym (cong-∘ seg) ⟩
  cong ((_$ x) ∘ (flip λ a → I-rec (f a) (g a) (H a))) seg    ≡⟨ I-rec-seg ⟩
  H x ∎

--------------------------------------------------------------------------
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

--------------------------------------------------------------------------
-- exponentials

infixr 20 _^_

_^_ : ∀ {r a} (R : Set r) (A : Set a) → Set (r ⊔ a)
R ^ A = A → R

[_]^_ : ∀ {r a b} (R : Set r) {A : Set a} {B : Set b} → (A → B) → (R ^ B) → (R ^ A)
[ R ]^ f = λ k a → k (f a)

ev : ∀ {r a} {R : Set r} {A : Set a} → R ^ A × A → R
ev (f , a) = f a

--------------------------------------------------------------------------
-- empty

ql : ⊥ → (A : Set) → A
ql () b
