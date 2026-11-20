module Inception.Reasoning where

open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

module Equational {A : Set} (_≈_ : A → A → Set)
  (≈-refl : ∀ {x} → x ≈ x)
  (≈-sym : ∀ {x y} → x ≈ y → y ≈ x)
  (≈-trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z) where

  isEquivalence : IsEquivalence _≈_
  isEquivalence = record { refl = ≈-refl ; sym = ≈-sym ; trans = ≈-trans }

  setoid : Setoid _ _
  setoid = record { isEquivalence = isEquivalence }

  open import Relation.Binary.Reasoning.Setoid setoid public
