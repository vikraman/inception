module Inception.Cont.Base where

open import Level
open import Data.Unit
open import Data.Product as P
open import Function as F
open import Data.Sum as S
open import Relation.Binary.PropositionalEquality

open import Inception.Prelude

K[_] : ∀ {v x} -> Set v -> Set x -> Set (v ⊔ x)
K[ V ] X = V ^ V ^ X

open import Inception.Monad.Base

K[_]-Monad : ∀ {v x} -> (V : Set v) -> Monad {x = x} {y = v ⊔ x} K[ V ]
K[ V ]-Monad .η a k = k a
K[ V ]-Monad ._* f m k = m λ a -> f a k
K[ V ]-Monad .unitl a = refl
K[ V ]-Monad .unitr f = refl
K[ V ]-Monad .assoc f g = refl

cocurry : ∀ {v x} -> {V : Set v} {X Y Z : Set x} -> (Z × V ^ X -> K[ V ] Y) -> Z -> K[ V ] (X ⊎ Y)
cocurry f z k = f (z , k ∘ inj₁) (k ∘ inj₂)

councurry : ∀ {v x} -> {V : Set v} {X Y Z : Set x} -> (Z -> K[ V ] (X ⊎ Y)) -> Z × V ^ X -> K[ V ] Y
councurry g (z , k₁) k₂ = g z S.[ k₁ , k₂ ]

[]~ : ∀ {v x} -> {V : Set v} {X : Set x} -> V -> K[ V ] X
[]~ v k = v

inc1 : ∀ {v x} -> {V : Set v} {X : Set x} -> (K[ V ] X) ^ V -> K[ V ] (⊤ ⊎ X)
inc1 f k = f (k (inj₁ tt)) (k ∘ inj₂)

incP : ∀ {v p x} -> {V : Set v} {P : Set p} {X : Set x} -> (K[ V ] X) ^ (V ^ P) -> K[ V ] (P ⊎ X)
incP f k = f (k ∘ inj₁) (k ∘ inj₂)
