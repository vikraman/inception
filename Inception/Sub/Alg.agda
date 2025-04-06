module Inception.Sub.Alg where

open import Level
open import Data.Unit
open import Data.Product as P
open import Function as F
open import Relation.Binary.PropositionalEquality

record Alg[_] {v x} (V : Set v) (X : Set x) : Set (v ⊔ x) where
  field
    var : V -> X
    sub : (V -> X) × X -> X
  field
    weak : ∀ {M N : X} -> sub ((λ a -> M) , N) ≡ M
    subs : ∀ {N : X} -> sub (var , N) ≡ N
    ext : ∀ {M : V -> X} {b : V} -> sub (M , var b) ≡ M b
    assoc : ∀ {M : V -> X} {N : X} {L : V -> V -> X} 
          -> sub ((λ a -> sub ((λ b -> L a b) , M a)) , N) ≡ sub ((λ b -> sub ((λ a -> L a b) , N)) , sub (M , N))

open Alg[_] public

V-Alg : ∀ {v} -> (V : Set v) -> Alg[ V ] V
V-Alg V .var v = v
V-Alg V .sub (f , v) = f v
V-Alg V .weak = refl
V-Alg V .subs = refl
V-Alg V .ext = refl
V-Alg V .assoc = refl

K[_] : ∀ {v x} -> Set v -> Set x -> Set (v ⊔ x)
K[ V ] X = (X -> V) -> V

K[_]-Alg : ∀ {v x} -> (V : Set v) (X : Set x) -> Alg[ V ] (K[ V ] X)
K[ V ]-Alg X .var v k = v
K[ V ]-Alg X .sub (M , N) k = M (N k) k
K[ V ]-Alg X .weak = refl
K[ V ]-Alg X .subs = refl
K[ V ]-Alg X .ext = refl
K[ V ]-Alg X .assoc = refl
