module Inception.Rewriting.Simulation where

open import Data.Product using (Σ; Σ-syntax; _×_; _,_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _◅◅_)
open import Relation.Binary.Construct.Closure.Transitive using ([_])
open import Relation.Binary.Construct.Composition using (_;_)

import Inception.Rewriting.Reduction as Reduction
open import Inception.Rewriting.Relation using (_†; Acc-sim)

--------------------------------------------------------------------------
-- simulations

module _ {A B : Set} (_~>_ : A → A → Set) (_⇝_ : B → B → Set) where

  open Reduction _~>_ using (Normal)
  open Reduction _⇝_ using ()
    renaming (_~>*_ to _⇝*_; _~>⁺_ to _⇝⁺_; Normal to Normalᴮ)

  record Sim (R : A → B → Set) : Set where
    field simulate : ∀ {a a₁ b} → R a b → a ~> a₁ → Σ[ b₁ ∈ B ] (b ⇝ b₁) × R a₁ b₁
  open Sim public

  record PlusSim (R : A → B → Set) : Set where
    field simulate⁺ : ∀ {a a₁ b} → R a b → a ~> a₁ → Σ[ b₁ ∈ B ] (b ⇝⁺ b₁) × R a₁ b₁
  open PlusSim public

  record WeakSim (R : A → B → Set) : Set where
    field simulate* : ∀ {a a₁ b} → R a b → a ~> a₁ → Σ[ b₁ ∈ B ] (b ⇝* b₁) × R a₁ b₁
  open WeakSim public

  NormalPreserving : (A → B → Set) → Set
  NormalPreserving R = ∀ {a b} → R a b → Normal a → Σ[ b₁ ∈ B ] (b ⇝* b₁) × Normalᴮ b₁ × R a b₁

module _ {A B : Set} {_~>_ : A → A → Set} {_⇝_ : B → B → Set} {R : A → B → Set} where

  open Reduction _~>_
  open Reduction _⇝_ using ()
    renaming ( _~>*_ to _⇝*_; ⁺→* to ⁺→*ᴮ
             ; SN to SNᴮ; SN→SN⁺ to SN→SN⁺ᴮ
             ; Normal to Normalᴮ; Deterministic to Deterministicᴮ; ↠-normal-unique to ↠-normal-uniqueᴮ )

  Sim→PlusSim : Sim _~>_ _⇝_ R → PlusSim _~>_ _⇝_ R
  Sim→PlusSim h .simulate⁺ r s with h .simulate r s
  ... | (b , t , r₁) = b , [ t ] , r₁

  PlusSim→WeakSim : PlusSim _~>_ _⇝_ R → WeakSim _~>_ _⇝_ R
  PlusSim→WeakSim h .simulate* r s with h .simulate⁺ r s
  ... | (b , t , r₁) = b , ⁺→*ᴮ t , r₁

  Sim→WeakSim : Sim _~>_ _⇝_ R → WeakSim _~>_ _⇝_ R
  Sim→WeakSim h = PlusSim→WeakSim (Sim→PlusSim h)

  weak-sim-* : WeakSim _~>_ _⇝_ R → ∀ {a a₁ b} → R a b → a ~>* a₁ → Σ[ b₁ ∈ B ] (b ⇝* b₁) × R a₁ b₁
  weak-sim-* h {b = b} r ε = b , ε , r
  weak-sim-* h r (s ◅ ss) with h .simulate* r s
  ... | (b₁ , t , r₁) with weak-sim-* h r₁ ss
  ... | (b₂ , ts , r₂) = b₂ , (t ◅◅ ts) , r₂

  ------------------------------------------------------------------------
  -- termination

  SN-plus-sim : PlusSim _~>_ _⇝_ R → ∀ {a b} → R a b → SNᴮ b → SN a
  SN-plus-sim h r hb = Acc-sim R (h .simulate⁺) r (SN→SN⁺ᴮ hb)

  SN-sim : Sim _~>_ _⇝_ R → ∀ {a b} → R a b → SNᴮ b → SN a
  SN-sim h = SN-plus-sim (Sim→PlusSim h)

  ------------------------------------------------------------------------
  -- normal forms

  eval-agree : WeakSim _~>_ _⇝_ R → NormalPreserving _~>_ _⇝_ R → Deterministicᴮ
             → ∀ {a a₁ b b₁} → R a b → a ~>* a₁ → Normal a₁ → b ⇝* b₁ → Normalᴮ b₁ → R a₁ b₁
  eval-agree h np det r ss n ts m with weak-sim-* h r ss
  ... | (b₂ , ts₂ , r₂) with np r₂ n
  ... | (b₃ , ts₃ , m₃ , r₃) with ↠-normal-uniqueᴮ det (ts₂ ◅◅ ts₃) m₃ ts m
  ... | refl = r₃

--------------------------------------------------------------------------
-- bisimulations

module _ {A B : Set} (_~>_ : A → A → Set) (_⇝_ : B → B → Set) where

  record Bisim (R : A → B → Set) : Set where
    field
      bisim-to   : Sim _~>_ _⇝_ R
      bisim-from : Sim _⇝_ _~>_ (R †)
  open Bisim public

  record WeakBisim (R : A → B → Set) : Set where
    field
      weak-bisim-to   : WeakSim _~>_ _⇝_ R
      weak-bisim-from : WeakSim _⇝_ _~>_ (R †)
  open WeakBisim public

module _ {A B : Set} {_~>_ : A → A → Set} {_⇝_ : B → B → Set} {R : A → B → Set} where

  Bisim→WeakBisim : Bisim _~>_ _⇝_ R → WeakBisim _~>_ _⇝_ R
  Bisim→WeakBisim h .weak-bisim-to   = Sim→WeakSim (h .bisim-to)
  Bisim→WeakBisim h .weak-bisim-from = Sim→WeakSim (h .bisim-from)

  bisim-sym : Bisim _~>_ _⇝_ R → Bisim _⇝_ _~>_ (R †)
  bisim-sym h .bisim-to   = h .bisim-from
  bisim-sym h .bisim-from = h .bisim-to

  weak-bisim-sym : WeakBisim _~>_ _⇝_ R → WeakBisim _⇝_ _~>_ (R †)
  weak-bisim-sym h .weak-bisim-to   = h .weak-bisim-from
  weak-bisim-sym h .weak-bisim-from = h .weak-bisim-to

--------------------------------------------------------------------------
-- composition

module _ {A B C : Set} {_~>_ : A → A → Set} {_⇝_ : B → B → Set} {_⊸_ : C → C → Set}
         {R : A → B → Set} {S : B → C → Set} where

  sim-∘ : Sim _~>_ _⇝_ R → Sim _⇝_ _⊸_ S → Sim _~>_ _⊸_ (R ; S)
  sim-∘ h₁ h₂ .simulate (b , r , q) s with h₁ .simulate r s
  ... | (b₁ , t , r₁) with h₂ .simulate q t
  ... | (c₁ , u , q₁) = c₁ , u , (b₁ , r₁ , q₁)

  weak-sim-∘ : WeakSim _~>_ _⇝_ R → WeakSim _⇝_ _⊸_ S → WeakSim _~>_ _⊸_ (R ; S)
  weak-sim-∘ h₁ h₂ .simulate* (b , r , q) s with h₁ .simulate* r s
  ... | (b₁ , ts , r₁) with weak-sim-* h₂ q ts
  ... | (c , us , q₁) = c , us , (b₁ , r₁ , q₁)
