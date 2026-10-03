module Inception.Rewriting.Normal {A : Set} (_~>_ : A → A → Set) where

open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Relation.Nullary.Negation using (contradiction)

import Relation.Binary.Rewriting as Rewriting
open Rewriting using (det⇒conf)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)

open import Inception.Rewriting.Closure _~>_

--------------------------------------------------------------------------
-- normal forms

Normal : A → Set
Normal a = ∀ {b} → a ~> b → ⊥

data Step? (a : A) : Set where
  done : Normal a → Step? a
  next : {b : A} → a ~> b → Step? a

Deterministic : Set
Deterministic = Rewriting.Deterministic _≡_ _~>_

--------------------------------------------------------------------------
-- determinism

module _ (det : Deterministic) where

  ↠-confluent : {a b c : A} → a ~>* b → a ~>* c → Σ[ d ∈ A ] (b ~>* d) × (c ~>* d)
  ↠-confluent = det⇒conf det

  ↠-normal : {a b : A} → Normal a → a ~>* b → a ≡ b
  ↠-normal n ε       = refl
  ↠-normal n (s ◅ r) = contradiction s n

  ↠-normal-unique : {a b c : A} → a ~>* b → Normal b → a ~>* c → Normal c → b ≡ c
  ↠-normal-unique r₁ n₁ r₂ n₂ with ↠-confluent r₁ r₂
  ... | (d , r₃ , r₄) with ↠-normal n₁ r₃ | ↠-normal n₂ r₄
  ... | refl | refl = refl
