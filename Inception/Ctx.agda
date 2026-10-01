module Inception.Ctx (Ty : Set) where

open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂; _,_; <_,_>; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Function using (id)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning

open import Inception.Prelude

infixl 15 _∙_
infix  10 _∋_

--------------------------------------------------------------------------
-- contexts

data Ctx : Set where
  ε   : Ctx
  _∙_ : Ctx → Ty → Ctx

variable
  X X₀ X₁ X₂ X₃ Y Y₀ Y₁ Y₂ Y₃ Z Z₀ Z₁ Z₂ Z₃ U U₀ U₁ U₂ U₃ S S₀ S₁ S₂ S₃ T T₀ T₁ T₂ T₃ : Ty
  Γ Δ Ψ Ξ Γ₁ Δ₁ Ψ₁ : Ctx

data _∋_ : Ctx → Ty → Set where
  here  : Γ ∙ X ∋ X
  there : Γ ∋ X → Γ ∙ Y ∋ X

there-injective : {i j : Γ ∋ X} → there {Y = Y} i ≡ there j → i ≡ j
there-injective refl = refl

--------------------------------------------------------------------------
-- weakenings

syntax Wk Γ Δ = Γ ⊇ Δ

data Wk : (Γ Δ : Ctx) → Set where
  wk-ε    : ε ⊇ ε
  wk-cong : Γ ⊇ Δ → (Γ ∙ X) ⊇ (Δ ∙ X)
  wk-wk   : Γ ⊇ Δ → (Γ ∙ X) ⊇ Δ

wk-id : Γ ⊇ Γ
wk-id {Γ = ε}     = wk-ε
wk-id {Γ = Γ ∙ X} = wk-cong wk-id

wk-emp : Γ ⊇ ε
wk-emp {Γ = ε}     = wk-ε
wk-emp {Γ = Γ ∙ X} = wk-wk wk-emp

wk-mem : Γ ⊇ Δ → Δ ∋ X → Γ ∋ X
wk-mem (wk-cong π) here      = here
wk-mem (wk-wk π)   here      = there (wk-mem π here)
wk-mem (wk-cong π) (there i) = there (wk-mem π i)
wk-mem (wk-wk π)   (there i) = there (wk-mem π (there i))

wk-trans : Γ ⊇ Δ → Δ ⊇ Ψ → Γ ⊇ Ψ
wk-trans wk-ε π                  = π
wk-trans (wk-cong π) (wk-cong δ) = wk-cong (wk-trans π δ)
wk-trans (wk-cong π) (wk-wk δ)   = wk-wk (wk-trans π δ)
wk-trans (wk-wk π) δ             = wk-wk (wk-trans π δ)

wk-prev : (Γ ∙ X) ⊇ (Δ ∙ Y) → Γ ⊇ Δ
wk-prev (wk-cong π) = π
wk-prev (wk-wk π)   = wk-trans π (wk-wk wk-id)

--------------------------------------------------------------------------
-- weakening laws

wk-mem-id-β : {i : Γ ∋ X} → wk-mem wk-id i ≡ i
wk-mem-id-β {i = here}    = refl
wk-mem-id-β {i = there i} = cong there wk-mem-id-β
{-# REWRITE wk-mem-id-β #-}

wk-mem-wk-wk-β : (π : Γ ⊇ Δ) (i : Δ ∋ X) → wk-mem (wk-wk {X = Y} π) i ≡ there (wk-mem π i)
wk-mem-wk-wk-β π here      = refl
wk-mem-wk-wk-β π (there i) = refl
{-# REWRITE wk-mem-wk-wk-β #-}

wk-mem-wk-η : (i : Γ ∋ X) (π : Ψ ⊇ Δ) (δ : Δ ⊇ Γ) → wk-mem π (wk-mem δ i) ≡ wk-mem (wk-trans π δ) i
wk-mem-wk-η here (wk-cong π) (wk-cong δ) = refl
wk-mem-wk-η here (wk-cong π) (wk-wk δ)   = cong there (wk-mem-wk-η here π δ)
wk-mem-wk-η here (wk-wk π)   (wk-cong δ) = cong there (wk-mem-wk-η here π (wk-cong δ))
wk-mem-wk-η here (wk-wk π)   (wk-wk δ)   = cong there (wk-mem-wk-η here π (wk-wk δ))
wk-mem-wk-η (there i) (wk-cong π) (wk-cong δ)         = cong there (wk-mem-wk-η i π δ)
wk-mem-wk-η (there i) (wk-wk (wk-cong π)) (wk-cong δ) = cong there (cong there (wk-mem-wk-η i π δ))
wk-mem-wk-η (there i) (wk-wk (wk-wk π)) (wk-cong δ)   = cong there (cong there (wk-mem-wk-η (there i) π (wk-cong δ)))
wk-mem-wk-η (there i) (wk-cong π) (wk-wk δ)           = cong there (wk-mem-wk-η (there i) π δ)
wk-mem-wk-η (there i) (wk-wk (wk-cong π)) (wk-wk δ)   = cong there (wk-mem-wk-η (there i) (wk-cong π) (wk-wk δ))
wk-mem-wk-η (there i) (wk-wk (wk-wk π)) (wk-wk δ)     = cong there (wk-mem-wk-η (there i) (wk-wk π) (wk-wk δ))
{-# REWRITE wk-mem-wk-η #-}

wk-trans-idl-β : (π : Γ ⊇ Δ) → wk-trans wk-id π ≡ π
wk-trans-idl-β wk-ε        = refl
wk-trans-idl-β (wk-cong π) = cong wk-cong (wk-trans-idl-β π)
wk-trans-idl-β (wk-wk π)   = cong wk-wk (wk-trans-idl-β π)
{-# REWRITE wk-trans-idl-β #-}

wk-trans-idr-β : (π : Γ ⊇ Δ) → wk-trans π wk-id ≡ π
wk-trans-idr-β wk-ε        = refl
wk-trans-idr-β (wk-cong π) = cong wk-cong (wk-trans-idr-β π)
wk-trans-idr-β (wk-wk π)   = cong wk-wk (wk-trans-idr-β π)
{-# REWRITE wk-trans-idr-β #-}

wk-trans-assoc-η : {π₁ : Γ ⊇ Δ} {π₂ : Δ ⊇ Ψ} {π₃ : Ψ ⊇ Ξ} → wk-trans π₁ (wk-trans π₂ π₃) ≡ wk-trans (wk-trans π₁ π₂) π₃
wk-trans-assoc-η {π₁ = wk-ε} = refl
wk-trans-assoc-η {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {π₃ = wk-cong π₃} = cong wk-cong (wk-trans-assoc-η {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
wk-trans-assoc-η {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {π₃ = wk-wk π₃}   = cong wk-wk (wk-trans-assoc-η {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
wk-trans-assoc-η {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {π₃ = π₃}           = cong wk-wk (wk-trans-assoc-η {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
wk-trans-assoc-η {π₁ = wk-wk π₁} {π₂ = π₂} {π₃ = π₃}                   = cong wk-wk (wk-trans-assoc-η {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
{-# REWRITE wk-trans-assoc-η #-}

wk-emp-uniq : (π : Γ ⊇ ε) → π ≡ wk-emp
wk-emp-uniq wk-ε      = refl
wk-emp-uniq (wk-wk π) = cong wk-wk (wk-emp-uniq π)

wk-absurd : Γ ⊇ (Δ ∙ X) → Δ ⊇ Γ → ⊥
wk-absurd (wk-cong π) (wk-cong δ) = wk-absurd π δ
wk-absurd (wk-cong π) (wk-wk δ)   = wk-absurd (wk-trans δ (wk-wk π)) wk-id
wk-absurd (wk-wk π)   (wk-cong δ) = wk-absurd π (wk-wk δ)
wk-absurd {X = X} (wk-wk π) (wk-wk δ) = wk-absurd π (wk-wk (wk-prev {X = X} (wk-wk δ)))

wk-id-id : {π : Γ ⊇ Γ} → π ≡ wk-id
wk-id-id {π = wk-ε} = refl
wk-id-id {π = wk-cong π} rewrite wk-id-id {π = π} = refl
wk-id-id {π = wk-wk π} = ql (wk-absurd π wk-id) (wk-wk π ≡ wk-id)

wk-merge : (π₁ : Γ ⊇ Δ) (π₂ : Γ ⊇ Ψ)
         → Σ[ Ξ ∈ Ctx ] Σ[ π ∈ Γ ⊇ Ξ ] Σ[ π₃ ∈ Ξ ⊇ Δ ] Σ[ π₄ ∈ Ξ ⊇ Ψ ] ((π₁ ≡ wk-trans π π₃) × (π₂ ≡ wk-trans π π₄))
wk-merge wk-ε wk-ε = ε , wk-ε , wk-ε , wk-ε , refl , refl
wk-merge {Γ = Γ ∙ X} (wk-cong π) (wk-cong δ) with wk-merge π δ
... | Γ , π , π₁ , π₂ , eq₁ , eq₂ = Γ ∙ X , wk-cong π , wk-cong π₁ , wk-cong π₂ , cong wk-cong eq₁ , cong wk-cong eq₂
wk-merge {Γ = Γ ∙ X} (wk-cong π) (wk-wk δ) with wk-merge π δ
... | Γ , π , π₁ , π₂ , eq₁ , eq₂ = Γ ∙ X , wk-cong π , wk-cong π₁ , wk-wk π₂ , cong wk-cong eq₁ , cong wk-wk eq₂
wk-merge {Γ = Γ ∙ X} (wk-wk π) (wk-cong δ) with wk-merge π δ
... | Γ , π , π₁ , π₂ , eq₁ , eq₂ = Γ ∙ X , wk-cong π , wk-wk π₁ , wk-cong π₂ , cong wk-wk eq₁ , cong wk-cong eq₂
wk-merge (wk-wk π) (wk-wk δ) with wk-merge π δ
... | Γ , π , π₁ , π₂ , eq₁ , eq₂ = Γ , wk-wk π , π₁ , π₂ , cong wk-wk eq₁ , cong wk-wk eq₂

wk-mem-trans-wk-β : (π : Ψ ⊇ (Δ ∙ Y)) (δ : Δ ⊇ Γ) (i : Γ ∋ X) → wk-mem (wk-trans π (wk-wk δ)) i ≡ wk-mem π (there (wk-mem δ i))
wk-mem-trans-wk-β π δ i = sym (wk-mem-wk-η i π (wk-wk δ))
{-# REWRITE wk-mem-trans-wk-β #-}

wk-mem-trans-cong-here-β : (π : Ψ ⊇ (Δ ∙ X)) (δ : Δ ⊇ Γ) → wk-mem (wk-trans π (wk-cong δ)) here ≡ wk-mem π here
wk-mem-trans-cong-here-β π δ = sym (wk-mem-wk-η here π (wk-cong δ))
{-# REWRITE wk-mem-trans-cong-here-β #-}

wk-mem-trans-cong-there-β : (π : Ψ ⊇ (Δ ∙ Y)) (δ : Δ ⊇ Γ) (i : Γ ∋ X) → wk-mem (wk-trans π (wk-cong δ)) (there i) ≡ wk-mem π (there (wk-mem δ i))
wk-mem-trans-cong-there-β π δ i = sym (wk-mem-wk-η (there i) π (wk-cong δ))
{-# REWRITE wk-mem-trans-cong-there-β #-}

wk-trans-trans-wk-β : (π : Ξ ⊇ (Δ ∙ X)) (δ : Δ ⊇ Ψ) (ρ : Ψ ⊇ Γ) → wk-trans (wk-trans π (wk-wk δ)) ρ ≡ wk-trans π (wk-wk (wk-trans δ ρ))
wk-trans-trans-wk-β π δ ρ = sym (wk-trans-assoc-η {π₁ = π} {π₂ = wk-wk δ} {π₃ = ρ})
{-# REWRITE wk-trans-trans-wk-β #-}

wk-trans-trans-cong-cong-β : (π : Ξ ⊇ (Δ ∙ X)) (δ : Δ ⊇ Ψ) (ρ : Ψ ⊇ Γ) → wk-trans (wk-trans π (wk-cong δ)) (wk-cong ρ) ≡ wk-trans π (wk-cong (wk-trans δ ρ))
wk-trans-trans-cong-cong-β π δ ρ = sym (wk-trans-assoc-η {π₁ = π} {π₂ = wk-cong δ} {π₃ = wk-cong ρ})
{-# REWRITE wk-trans-trans-cong-cong-β #-}

wk-trans-trans-cong-wk-β : (π : Ξ ⊇ (Δ ∙ X)) (δ : Δ ⊇ Ψ) (ρ : Ψ ⊇ Γ) → wk-trans (wk-trans π (wk-cong δ)) (wk-wk ρ) ≡ wk-trans π (wk-wk (wk-trans δ ρ))
wk-trans-trans-cong-wk-β π δ ρ = sym (wk-trans-assoc-η {π₁ = π} {π₂ = wk-cong δ} {π₃ = wk-wk ρ})
{-# REWRITE wk-trans-trans-cong-wk-β #-}

--------------------------------------------------------------------------
-- semantics

module Sem (⟦_⟧ : Ty → Set) where

  ⟦_⟧ˣ : Ctx → Set
  ⟦ ε ⟧ˣ     = ⊤
  ⟦ Γ ∙ X ⟧ˣ = ⟦ Γ ⟧ˣ × ⟦ X ⟧

  ⟦_⟧ʷ : Γ ⊇ Δ → ⟦ Γ ⟧ˣ → ⟦ Δ ⟧ˣ
  ⟦ wk-ε ⟧ʷ      = idf
  ⟦ wk-cong π ⟧ʷ = < proj₁ ； ⟦ π ⟧ʷ , proj₂ >
  ⟦ wk-wk π ⟧ʷ   = proj₁ ； ⟦ π ⟧ʷ

  ⟦_⟧ᵐ : Γ ∋ X → ⟦ Γ ⟧ˣ → ⟦ X ⟧
  ⟦ here ⟧ᵐ    = proj₂
  ⟦ there i ⟧ᵐ = proj₁ ； ⟦ i ⟧ᵐ

  wk-id-coh : ⟦ wk-id {Γ} ⟧ʷ ≡ id
  wk-id-coh {ε}     = refl
  wk-id-coh {Γ ∙ X} rewrite wk-id-coh {Γ} = refl

  {-# REWRITE wk-id-coh #-}

  wk-mem-coh : (π : Γ ⊇ Δ) (i : Δ ∋ X) → ⟦ wk-mem π i ⟧ᵐ ≡ (⟦ π ⟧ʷ ； ⟦ i ⟧ᵐ)
  wk-mem-coh (wk-cong π) here      = refl
  wk-mem-coh (wk-cong π) (there i) rewrite wk-mem-coh π i = refl
  wk-mem-coh (wk-wk π)   here      rewrite wk-mem-coh π here = refl
  wk-mem-coh (wk-wk π)   (there i) rewrite wk-mem-coh π (there i) = refl

  -- co-contexts

  ⟦_⟧ˣ̃ : Ctx → Set
  ⟦ ε ⟧ˣ̃     = ⊥
  ⟦ Δ ∙ X ⟧ˣ̃ = ⟦ Δ ⟧ˣ̃ ⊎ ⟦ X ⟧

  ⟦_⟧ʷ̃ : Δ ⊇ Γ → ⟦ Γ ⟧ˣ̃ → ⟦ Δ ⟧ˣ̃
  ⟦ wk-ε ⟧ʷ̃ ()
  ⟦ wk-cong π ⟧ʷ̃ (inj₁ x) = inj₁ (⟦ π ⟧ʷ̃ x)
  ⟦ wk-cong π ⟧ʷ̃ (inj₂ y) = inj₂ y
  ⟦ wk-wk π ⟧ʷ̃ x          = inj₁ (⟦ π ⟧ʷ̃ x)

  ⟦_⟧ᵐ̃ : Δ ∋ X → ⟦ X ⟧ → ⟦ Δ ⟧ˣ̃
  ⟦ here ⟧ᵐ̃    = inj₂
  ⟦ there i ⟧ᵐ̃ = ⟦ i ⟧ᵐ̃ ； inj₁

  wk-id-coh̃ : ⟦ wk-id {Δ} ⟧ʷ̃ ≡ id
  wk-id-coh̃ {ε} = funext λ ()
  wk-id-coh̃ {Δ ∙ X} = funext λ
    { (inj₁ x) → cong inj₁ (happly wk-id-coh̃ x)
    ; (inj₂ y) → refl
    }

  {-# REWRITE wk-id-coh̃ #-}

  wk-mem-coh̃ : (ρ : Δ ⊇ Γ) (i : Γ ∋ X) → ⟦ wk-mem ρ i ⟧ᵐ̃ ≡ (⟦ i ⟧ᵐ̃ ； ⟦ ρ ⟧ʷ̃)
  wk-mem-coh̃ (wk-cong ρ) here      = funext λ a → refl
  wk-mem-coh̃ (wk-cong ρ) (there i) = funext λ a → cong inj₁ (happly (wk-mem-coh̃ ρ i) a)
  wk-mem-coh̃ (wk-wk ρ) here        = funext λ a → cong inj₁ (happly (wk-mem-coh̃ ρ here) a)
  wk-mem-coh̃ (wk-wk ρ) (there i)   = funext λ a → cong inj₁ (happly (wk-mem-coh̃ ρ (there i)) a)
