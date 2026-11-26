module Inception.Rewriting.Simulation where

open import Data.Product using (Σ; Σ-syntax; _×_; _,_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; subst)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
open import Relation.Binary.Construct.Closure.Transitive using ([_]; _∷_)
open import Relation.Binary.Construct.Composition using (_;_)
open import Relation.Nullary.Negation using (contradiction)

import Inception.Rewriting.Reduction as Reduction
open import Inception.Rewriting.Relation using (_†; Acc-sim)

--------------------------------------------------------------------------
-- simulations

module _ {A B : Set} (_~>_ : A → A → Set) (_⇝_ : B → B → Set) where

  open Reduction _~>_ using ()
    renaming (Normal to Normalᴬ)
  open Reduction _⇝_ using ()
    renaming (_~>*_ to _⇝*_; _~>⁺_ to _⇝⁺_; Normal to Normalᴮ)

  record Sim (R : A → B → Set) : Set where
    field simulate : ∀ {a₁ a₂ b₁} → R a₁ b₁ → a₁ ~> a₂ → Σ[ b₂ ∈ B ] (b₁ ⇝ b₂) × R a₂ b₂
  open Sim public

  record PlusSim (R : A → B → Set) : Set where
    field simulate⁺ : ∀ {a₁ a₂ b₁} → R a₁ b₁ → a₁ ~> a₂ → Σ[ b₂ ∈ B ] (b₁ ⇝⁺ b₂) × R a₂ b₂
  open PlusSim public

  record WeakSim (R : A → B → Set) : Set where
    field simulate* : ∀ {a₁ a₂ b₁} → R a₁ b₁ → a₁ ~> a₂ → Σ[ b₂ ∈ B ] (b₁ ⇝* b₂) × R a₂ b₂
  open WeakSim public

  NormalPreserving : (A → B → Set) → Set
  NormalPreserving R = ∀ {a b₁} → R a b₁ → Normalᴬ a → Σ[ b₂ ∈ B ] (b₁ ⇝* b₂) × Normalᴮ b₂ × R a b₂

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

  weak-sim-* : WeakSim _~>_ _⇝_ R → ∀ {a₁ a₂ b₁} → R a₁ b₁ → a₁ ~>* a₂ → Σ[ b₂ ∈ B ] (b₁ ⇝* b₂) × R a₂ b₂
  weak-sim-* h {b₁ = b} r ε = b , ε , r
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
             → ∀ {a₁ a₂ b₁ b₂} → R a₁ b₁ → a₁ ~>* a₂ → Normal a₂ → b₁ ⇝* b₂ → Normalᴮ b₂ → R a₂ b₂
  eval-agree h np det r ss n ts m with weak-sim-* h r ss
  ... | (b₃ , ts₁ , r₁) with np r₁ n
  ... | (b₄ , ts₂ , m₁ , r₂) with ↠-normal-uniqueᴮ det (ts₁ ◅◅ ts₂) m₁ ts m
  ... | refl = r₂

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
-- general fact about simulation into a deterministic target

module Simulation {A B : Set} (_~>_ : A → A → Set) (_⇝_ : B → B → Set) where

  open Reduction _~>_
  open Reduction _⇝_ using ()
    renaming (_~>*_ to _⇝*_; _~>⁺_ to _⇝⁺_; ⁺→* to ⁺→*ᴮ; Normal to Normalᴮ; Deterministic to Deterministicᴮ)

  infixl 30 _⇐ _↾SN
  infix 4 _⊑* _≈* _⊑ⁿ _⊑⁺

  private
    variable
      R : A → B → Set

  -- closure of R under backward target reduction
  _⇐ : (A → B → Set) → A → B → Set
  R ⇐ = R ; (Star _⇝_ †)

  -- R restricted to SN sources
  _↾SN : (A → B → Set) → A → B → Set
  (R ↾SN) a b = SN a × R a b

  _⊑* _≈* _⊑ⁿ : (A → B → Set) → Set
  R ⊑* = WeakSim _~>_ _⇝_ R
  R ≈* = WeakBisim _~>_ _⇝_ R
  R ⊑ⁿ = NormalPreserving _~>_ _⇝_ R

  -- if the target can step, the source catches up one or more target steps later
  --
  --   a₁ ──R── b₁ ─⇝─▶ b₂
  --   ┊        ┊
  --   ~>*      ⇝⁺
  --   ↓        ↓
  --   a₂ ──R── b₃
  _⊑⁺ : (A → B → Set) → Set
  R ⊑⁺ = ∀ {a₁ b₁ b₂} → R a₁ b₁ → b₁ ⇝ b₂ → Σ[ a₂ ∈ A ] Σ[ b₃ ∈ B ] (a₁ ~>* a₂) × (b₁ ⇝⁺ b₃) × R a₂ b₃

  private
    _◅⁺_ : ∀ {b₁ b₂ b₃} → b₁ ⇝ b₂ → b₂ ⇝* b₃ → b₁ ⇝⁺ b₃
    u ◅⁺ ε        = [ u ]
    u ◅⁺ (v ◅ vs) = u ∷ (v ◅⁺ vs)

  ------------------------------------------------------------------------
  -- expansion

  expand-forward : R ⊑* → R ⇐ ⊑*
  expand-forward h .simulate* (b₁ , r₁ , us) s with h .simulate* r₁ s
  ... | (b₂ , ts , r₂) = b₂ , us ◅◅ ts , b₂ , r₂ , ε

  expand-normal : R ⊑ⁿ → R ⇐ ⊑ⁿ
  expand-normal np (b₁ , r₁ , us) n with np r₁ n
  ... | (b₂ , ts , m , r₂) = b₂ , us ◅◅ ts , m , b₂ , r₂ , ε

  -- determinism turns progress into backward simulation
  -- cf. CompCert forward_to_backward_simulation: https://compcert.org/doc/html/compcert.common.Smallstep.html#forward_to_backward_simulation
  --
  --   a₁ ──R── b₁
  --   ┊        │ ⇝
  --   ~>*      ↓
  --   ┊        b₂      determinism: b₂ is the head of b₁ ⇝⁺ b₃
  --   ↓        ┊ ⇝*
  --   a₂ ──R── b₃      hence a₂ ─R⇐─ b₂
  expand-backward : Deterministicᴮ → R ⊑⁺ → WeakSim _⇝_ _~>_ ((R ⇐) †)
  expand-backward det p .simulate* (b , r , u ◅ us) t = _ , ε , b , r , subst (_⇝* b) (det u t) us
  expand-backward det p .simulate* (_ , r₁ , ε) t with p r₁ t
  ... | (a , b , ss , [ u ] , r₂)    = a , ss , b , r₂ , subst (_⇝* b) (det u t) ε
  ... | (a , b , ss , u ∷ us , r₂) = a , ss , b , r₂ , subst (_⇝* b) (det u t) (⁺→*ᴮ us)

  progress→weak-bisim : R ⊑* → R ⊑⁺ → Deterministicᴮ → R ⇐ ≈*
  progress→weak-bisim h p det .weak-bisim-to   = expand-forward h
  progress→weak-bisim h p det .weak-bisim-from = expand-backward det p

  ------------------------------------------------------------------------
  -- strong normalisation bounds stuttering

  on-sn-weak-sim : R ⊑* → R ↾SN ⊑*
  on-sn-weak-sim h .simulate* (hs , r₁) s with h .simulate* r₁ s
  ... | (b , ts , r₂) = b , ts , SN-step hs s , r₂

  on-sn-normal : R ⊑ⁿ → R ↾SN ⊑ⁿ
  on-sn-normal np (hs , r₁) n with np r₁ n
  ... | (b , ts , m , r₂) = b , ts , m , hs , r₂

  -- this is a finite chain because SN a₁
  --
  --   a₁ ~> a₂ ~> a₃ ~> ⋯ ~> aₙ    each ─R─ b₁
  --
  -- it ends in a square with b₁ ⇝⁺ b, or at a normal aₙ where ⊑ⁿ gives b₁ ⇝⁺ b
  sn-progress : ((a : A) → Step? a) → R ⊑* → R ⊑ⁿ → R ↾SN ⊑⁺
  sn-progress {R = R} step? h np (hs , r) t = go hs r t
    where
    go : ∀ {a₁ b₁ b₂} → SN a₁ → R a₁ b₁ → b₁ ⇝ b₂ → Σ[ a₂ ∈ A ] Σ[ b₃ ∈ B ] (a₁ ~>* a₂) × (b₁ ⇝⁺ b₃) × (R ↾SN) a₂ b₃
    go {a₁ = a} (sn f) r₁ t with step? a
    go {a₁ = a} (sn f) r₁ t | done n with np r₁ n
    ... | (_ , ε , m , _)        = contradiction t m
    ... | (b , u ◅ us , _ , r₂) = a , b , ε , u ◅⁺ us , sn f , r₂
    go {a₁ = a} (sn f) r₁ t | next s with h .simulate* r₁ s
    ... | (b , u ◅ us , r₂) = _ , b , s ◅ ε , u ◅⁺ us , f s , r₂
    ... | (_ , ε , r₂) with go (f s) r₂ t
    ... | (a₂ , b , ss , us , q) = a₂ , b , s ◅ ss , us , q

  -- forward weak sim + normal preservation + deterministic target ⇒ weak bisim
  WeakSim→WeakBisim : ((a : A) → Step? a) → R ⊑* → R ⊑ⁿ → Deterministicᴮ → R ↾SN ⇐ ≈*
  WeakSim→WeakBisim step? h np det = progress→weak-bisim (on-sn-weak-sim h) (sn-progress step? h np) det

--------------------------------------------------------------------------
-- decodings

record Decoding {A B : Set} (_~>_ : A → A → Set) (_⇝_ : B → B → Set) : Set where
  open Reduction _~>_ using (Step?) renaming (Normal to Normalᴬ)
  open Reduction _⇝_ using ()
    renaming (_~>*_ to _⇝*_; Normal to Normalᴮ; Deterministic to Deterministicᴮ)
  open Simulation _~>_ _⇝_ using (_⇐; _↾SN; _⊑*; _≈*; _⊑ⁿ; WeakSim→WeakBisim)

  field
    decode        : A → B
    decode-sim    : ∀ {a₁ a₂} → a₁ ~> a₂ → decode a₁ ⇝* decode a₂
    decode-normal : ∀ {a} → Normalᴬ a → Normalᴮ (decode a)

  Decoded : A → B → Set
  Decoded a b = decode a ≡ b

  decode-weak-sim : Decoded ⊑*
  decode-weak-sim .simulate* refl s = _ , decode-sim s , refl

  decode-normal-preserving : Decoded ⊑ⁿ
  decode-normal-preserving refl n = _ , ε , decode-normal n , refl

  decode-run : ∀ {a₁ a₂} → Star _~>_ a₁ a₂ → decode a₁ ⇝* decode a₂
  decode-run ss with weak-sim-* decode-weak-sim refl ss
  ... | (_ , ts , refl) = ts

  decode-weak-bisim : ((a : A) → Step? a) → Deterministicᴮ → Decoded ↾SN ⇐ ≈*
  decode-weak-bisim step? det = WeakSim→WeakBisim step? decode-weak-sim decode-normal-preserving det

  decode-agree : Deterministicᴮ → ∀ {a₁ a₂ b} → Star _~>_ a₁ a₂ → Normalᴬ a₂ → decode a₁ ⇝* b → Normalᴮ b
               → decode a₂ ≡ b
  decode-agree det ss n ts m = eval-agree decode-weak-sim decode-normal-preserving det refl ss n ts m

--------------------------------------------------------------------------
-- composition

module _ {A B C : Set} {_~>_ : A → A → Set} {_⇝_ : B → B → Set} {_⊸_ : C → C → Set}
         {R : A → B → Set} {S : B → C → Set} where

  sim-∘ : Sim _~>_ _⇝_ R → Sim _⇝_ _⊸_ S → Sim _~>_ _⊸_ (R ; S)
  sim-∘ h₁ h₂ .simulate (b₁ , r₁ , q₁) s with h₁ .simulate r₁ s
  ... | (b₂ , t , r₂) with h₂ .simulate q₁ t
  ... | (c , u , q₂) = c , u , (b₂ , r₂ , q₂)

  weak-sim-∘ : WeakSim _~>_ _⇝_ R → WeakSim _⇝_ _⊸_ S → WeakSim _~>_ _⊸_ (R ; S)
  weak-sim-∘ h₁ h₂ .simulate* (b₁ , r₁ , q₁) s with h₁ .simulate* r₁ s
  ... | (b₂ , ts , r₂) with weak-sim-* h₂ q₁ ts
  ... | (c , us , q₂) = c , us , (b₂ , r₂ , q₂)
