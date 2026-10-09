module Inception.Rewriting.Reduction {A : Set} (_~>_ : A → A → Set) where

open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Function using (_⇔_; mk⇔)

open import Induction.WellFounded using (Acc; acc; acc-inverse; module Subrelation)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_)
open import Relation.Binary.Construct.Closure.Transitive
  using (TransClosure; [_]; _∷_; _∷ʳ_; accessible)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
import Relation.Binary.Rewriting as Rewriting
open Rewriting using (IsNormalForm; StronglyNormalizing; det⇒conf)

open import Relation.Nullary.Negation using (contradiction)

open import Inception.Rewriting.Relation using (_†)

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

⁺-reverse : {a b : A} → a ~>⁺ b → TransClosure (_~>_ †) b a
⁺-reverse [ s ]   = [ s ]
⁺-reverse (s ∷ r) = ⁺-reverse r ∷ʳ s

--------------------------------------------------------------------------
-- normal forms

Normal : A → Set
Normal a = ∀ {b} → a ~> b → ⊥

data Step? (a : A) : Set where
  done : Normal a → Step? a
  next : {b : A} → a ~> b → Step? a

Normal→IsNormalForm : {a : A} → Normal a → IsNormalForm _~>_ a
Normal→IsNormalForm n (b , s) = n s

IsNormalForm→Normal : {a : A} → IsNormalForm _~>_ a → Normal a
IsNormalForm→Normal n s = n (_ , s)

Normal⇔IsNormalForm : {a : A} → Normal a ⇔ IsNormalForm _~>_ a
Normal⇔IsNormalForm = mk⇔ Normal→IsNormalForm IsNormalForm→Normal

Deterministic : Set
Deterministic = Rewriting.Deterministic _≡_ _~>_

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

--------------------------------------------------------------------------
-- strong normalisation

SN : A → Set
SN = Acc (_~>_ †)

pattern sn f = acc f

SN-step : {a b : A} → SN a → a ~> b → SN b
SN-step h = acc-inverse h

SN-↠ : {a b : A} → SN a → a ~>* b → SN b
SN-↠ h ε       = h
SN-↠ h (s ◅ r) = SN-↠ (SN-step h s) r

Normal→SN : {a : A} → Normal a → SN a
Normal→SN n = sn (λ s → contradiction s n)

SN-back : Deterministic → {a b : A} → a ~> b → SN b → SN a
SN-back det s h = sn (λ s₁ → Eq.subst SN (det s s₁) h)

SN⇔StronglyNormalizing : ((a : A) → SN a) ⇔ StronglyNormalizing _~>_
SN⇔StronglyNormalizing = mk⇔ (λ h → h) (λ h → h)

SN⁺ : A → Set
SN⁺ = Acc (_~>⁺_ †)

pattern sn⁺ f = acc f

SN→SN⁺ : {a : A} → SN a → SN⁺ a
SN→SN⁺ h = Subrelation.accessible ⁺-reverse (accessible (_~>_ †) h)

--------------------------------------------------------------------------
-- evaluation

eval-acc : ((a : A) → Step? a) → {a : A} → SN a → Σ[ b ∈ A ] (a ~>* b) × Normal b
eval-acc step? {a} (sn f) with step? a
... | done n = a , ε , n
... | next s with eval-acc step? (f s)
... | (b , r , n) = b , s ◅ r , n
