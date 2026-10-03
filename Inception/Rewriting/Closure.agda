module Inception.Rewriting.Closure {A : Set} (_~>_ : A → A → Set) where

open import Function using (flip)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
open import Relation.Binary.Construct.Closure.Transitive
  using (TransClosure; [_]; _∷_; _∷ʳ_)

--------------------------------------------------------------------------
-- closures

infix 4 _~>*_ _~>⁺_

_~>*_ : A → A → Set
_~>*_ = Star _~>_

_~>⁺_ : A → A → Set
_~>⁺_ = TransClosure _~>_

⁺→* : {a b : A} → a ~>⁺ b → a ~>* b
⁺→* [ s ]   = s ◅ ε
⁺→* (s ∷ r) = s ◅ ⁺→* r

⁺-reverse : {a b : A} → a ~>⁺ b → TransClosure (flip _~>_) b a
⁺-reverse [ s ]   = [ s ]
⁺-reverse (s ∷ r) = ⁺-reverse r ∷ʳ s
