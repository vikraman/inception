{-# OPTIONS --no-postfix-projections #-}

module Inception.IncV.Data where

open import Inception.Prelude

open import Data.Nat
open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Vec

record Alg : Set₁ where
  field
    𝒟 : Set
    𝒪 : Set
    ∣_∣ : ((o : 𝒪) → ℕ)
    apply : (o : 𝒪) → (args : Vec 𝒟 ∣ o ∣) → 𝒟
