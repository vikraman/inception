module Inception.Cont.Base where

open import Level
open import Data.Unit
open import Data.Product as P
open import Function as F
open import Data.Sum as S
open import Relation.Binary.PropositionalEquality

K[_] : ∀ {v x} -> Set v -> Set x -> Set (v ⊔ x)
K[ V ] X = (X -> V) -> V

open import Inception.Monad.Base

K[_]-Monad : ∀ {v x} -> (V : Set v) -> Monad {x = x} {y = v ⊔ x} K[ V ]
K[ V ]-Monad .η a k = k a
K[ V ]-Monad ._* f m k = m λ a -> f a k
K[ V ]-Monad .unitl a = refl
K[ V ]-Monad .unitr f = refl
K[ V ]-Monad .assoc f g = refl
