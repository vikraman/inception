module Inception.Cont.Repr where

open import Level
open import Data.Unit
open import Data.Product as P
open import Function as F
open import Data.Sum
open import Relation.Binary.PropositionalEquality

open import Inception.Prelude
open import Inception.Cont.Base
open import Inception.Monad.Base

module _ {v y} (V : Set v) {S : Set v -> Set y} (S-Monad : Monad S) where
  open MonadMorphism
  module S = Monad S-Monad
  module _ (S-Alg-V : MonadAlg S-Monad V) where
    module A = MonadAlg S-Alg-V

    AlgToMor : MonadMorphism S-Monad K[ V ]-Monad
    AlgToMor .F m k = (k A.#) m
    AlgToMor .F-η = funext λ a -> funext λ k -> happly (A.η-# k) a
    AlgToMor .F-* f = funext λ m -> funext λ k -> sym (happly (A.*-# f k) m)

  module _ (Mor : MonadMorphism S-Monad K[ V ]-Monad) where
    module M = MonadMorphism Mor

    MorToAlg : MonadAlg S-Monad V
    MorToAlg ._# k m = M.F m k
    MorToAlg .η-# k = funext λ y -> happly (happly M.F-η y) k
    MorToAlg .*-# f g = funext λ m -> sym (happly (happly (M.F-* f) m) g)

  module _ (S-Alg-V : MonadAlg S-Monad V) where
    AlgToAlg : MonadAlg≡ (MorToAlg (AlgToMor S-Alg-V)) S-Alg-V
    AlgToAlg f = refl

  module _ (Mor : MonadMorphism S-Monad K[ V ]-Monad) where
    MorToMor : MonadMorphism≡ (AlgToMor (MorToAlg Mor)) Mor
    MorToMor = refl
