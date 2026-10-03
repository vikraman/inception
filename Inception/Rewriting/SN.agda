module Inception.Rewriting.SN {A : Set} (_~>_ : A → A → Set) where

open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Function using (flip)

open import Induction.WellFounded using (Acc; acc; acc-inverse; module Subrelation)

open import Relation.Binary.Construct.Closure.Transitive using (accessible)

import Relation.Binary.PropositionalEquality as Eq

open import Relation.Nullary.Negation using (contradiction)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_)

open import Inception.Rewriting.Closure _~>_
open import Inception.Rewriting.Normal _~>_

--------------------------------------------------------------------------
-- strong normalisation

SN : A → Set
SN = Acc (flip _~>_)

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

--------------------------------------------------------------------------
-- strong normalisation for the transitive closure

SN⁺ : A → Set
SN⁺ = Acc (flip _~>⁺_)

pattern sn⁺ f = acc f

SN→SN⁺ : {a : A} → SN a → SN⁺ a
SN→SN⁺ h = Subrelation.accessible ⁺-reverse (accessible (flip _~>_) h)

--------------------------------------------------------------------------
-- evaluation

eval-acc : ((a : A) → Step? a) → {a : A} → SN a → Σ[ b ∈ A ] (a ~>* b) × Normal b
eval-acc step? {a} (sn f) with step? a
... | done n = a , ε , n
... | next s with eval-acc step? (f s)
... | (b , r , n) = b , s ◅ r , n
