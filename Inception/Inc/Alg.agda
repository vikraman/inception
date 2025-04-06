module Inception.Inc.Alg where

open import Level
open import Data.Unit
open import Data.Product as P
open import Function as F
open import Data.Sum as S
open import Relation.Binary.PropositionalEquality

record Alg[_,_] {v p x} (V : Set v) (P : Set p) (X : Set x) : Set (v ⊔ p ⊔ x) where
  field
    rec : V × P -> X
    inc : (V -> X) × (P -> X) -> X
  field
    weak : ∀ {M : X} {N : P -> X} -> inc ((λ a -> M) , N) ≡ M
    subs : ∀ {M : V -> X} {N : P -> X} {p : P} -> inc ((λ a -> rec (a , p)) , N) ≡ N p
    ext : ∀ {M : V -> X} {b : V} -> inc (M , λ p -> rec (b , p)) ≡ M b
    assoc : ∀ {M : V -> P -> X} {N : P -> X} {L : V -> V -> X}
          -> inc ((λ a -> inc ((λ b -> L a b) , λ p -> M a p)) , N) ≡ inc ((λ b -> inc ((λ a -> L a b) , N)) , λ p -> inc ((λ a -> M a p) , N))

open Alg[_,_]

V-Alg : ∀ {v p} -> (V : Set v) (P : Set p) -> Alg[ (P -> V) , P ] V
V-Alg V P .rec (v , p) = v p
V-Alg V P .inc (M , N) = M N
V-Alg V P .weak = refl
V-Alg V P .subs = refl
V-Alg V P .ext = refl
V-Alg V P .assoc = refl

import Inception.Sub.Alg as S
open S.Alg[_]

Sub[_]-Alg : ∀ {v x} -> (V : Set v) (X : Set x) (α : S.Alg[ V ] X) -> Alg[ V , ⊤ ] X
Sub[ V ]-Alg X α .rec (v , tt) = α .var v
Sub[ V ]-Alg X α .inc (M , N) = α .sub (M , N tt)
Sub[ V ]-Alg X α .weak = α .weak
Sub[ V ]-Alg X α .subs = α .subs
Sub[ V ]-Alg X α .ext = α .ext
Sub[ V ]-Alg X α .assoc = α .assoc

K[_] : ∀ {v x} -> Set v -> Set x -> Set (v ⊔ x)
K[ V ] X = (X -> V) -> V

K[_]-Alg : ∀ {v p x} -> (V : Set v) (P : Set p) (X : Set x) -> Alg[ (P -> V) , P ] (K[ V ] X)
K[ V ]-Alg P X .rec (v , p) k = v p
K[ V ]-Alg P X .inc (M , N) k = M (λ p -> N p k) k
K[ V ]-Alg P X .weak = refl
K[ V ]-Alg P X .subs = refl
K[ V ]-Alg P X .ext = refl
K[ V ]-Alg P X .assoc = refl
