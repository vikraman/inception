module Inception.Ctx (Ty : Set) where

open import Function using (id)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂; _,_; <_,_>; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

open import Inception.Prelude

infixl 15 _∙_
infix  10 _∋_

--------------------------------------------------------------------------
-- contexts

data Ctx : Set where
  ε   : Ctx
  _∙_ : Ctx -> Ty -> Ctx

variable
  A B C D : Ty
  X X₁ X₂ Y Z Z₀ Z₁ : Ty
  Γ Δ Ψ Γ₁ Γ₂ Γ₃ Δ₁ Δ₂ Ψ₁ : Ctx

data _∋_ : Ctx -> Ty -> Set where
  here  : Γ ∙ X ∋ X
  there : Γ ∋ X -> Γ ∙ Y ∋ X

there-injective : {i i₁ : Γ ∋ X} -> there {Y = Y} i ≡ there i₁ -> i ≡ i₁
there-injective refl = refl

--------------------------------------------------------------------------
-- weakenings

syntax Wk Γ Δ = Γ ⊇ Δ

data Wk : (Γ Δ : Ctx) -> Set where
  wk-ε    : ε ⊇ ε
  wk-cong : Γ ⊇ Δ -> (Γ ∙ X) ⊇ (Δ ∙ X)
  wk-wk   : Γ ⊇ Δ -> (Γ ∙ X) ⊇ Δ

wk-id : Γ ⊇ Γ
wk-id {Γ = ε}     = wk-ε
wk-id {Γ = Γ ∙ X} = wk-cong wk-id

wk-emp : Γ ⊇ ε
wk-emp {Γ = ε}     = wk-ε
wk-emp {Γ = Γ ∙ X} = wk-wk wk-emp

wk-mem : Γ ⊇ Δ -> Δ ∋ X -> Γ ∋ X
wk-mem (wk-cong π) here      = here
wk-mem (wk-wk π)   here      = there (wk-mem π here)
wk-mem (wk-cong π) (there i) = there (wk-mem π i)
wk-mem (wk-wk π)   (there i) = there (wk-mem π (there i))

wk-trans : Γ ⊇ Δ -> Δ ⊇ Ψ -> Γ ⊇ Ψ
wk-trans wk-ε π                  = π
wk-trans (wk-cong π) (wk-cong δ) = wk-cong (wk-trans π δ)
wk-trans (wk-cong π) (wk-wk δ)   = wk-wk (wk-trans π δ)
wk-trans (wk-wk π) δ             = wk-wk (wk-trans π δ)

wk-prev : (Γ ∙ X) ⊇ (Δ ∙ Y) -> Γ ⊇ Δ
wk-prev (wk-cong π) = π
wk-prev (wk-wk π)   = wk-trans π (wk-wk wk-id)

--------------------------------------------------------------------------
-- weakening laws

wk-mem-id : {i : Γ ∋ X} -> wk-mem wk-id i ≡ i
wk-mem-id {i = here}    = refl
wk-mem-id {i = there i} = cong there wk-mem-id

wk-mem-wk-wk : (π : Γ ⊇ Δ) (i : Δ ∋ X) -> wk-mem (wk-wk {X = Y} π) i ≡ there (wk-mem π i)
wk-mem-wk-wk π here      = refl
wk-mem-wk-wk π (there i) = refl

wk-mem-trans : (i : Γ ∋ X) (π : Ψ ⊇ Δ) (δ : Δ ⊇ Γ) -> wk-mem π (wk-mem δ i) ≡ wk-mem (wk-trans π δ) i
wk-mem-trans here (wk-cong π) (wk-cong δ) = refl
wk-mem-trans here (wk-cong π) (wk-wk δ)   = cong there (wk-mem-trans here π δ)
wk-mem-trans here (wk-wk π)   (wk-cong δ) = cong there (wk-mem-trans here π (wk-cong δ))
wk-mem-trans here (wk-wk π)   (wk-wk δ)   = cong there (wk-mem-trans here π (wk-wk δ))
wk-mem-trans (there i) (wk-cong π) (wk-cong δ)         = cong there (wk-mem-trans i π δ)
wk-mem-trans (there i) (wk-wk (wk-cong π)) (wk-cong δ) = cong there (cong there (wk-mem-trans i π δ))
wk-mem-trans (there i) (wk-wk (wk-wk π)) (wk-cong δ)   = cong there (cong there (wk-mem-trans (there i) π (wk-cong δ)))
wk-mem-trans (there i) (wk-cong π) (wk-wk δ)           = cong there (wk-mem-trans (there i) π δ)
wk-mem-trans (there i) (wk-wk (wk-cong π)) (wk-wk δ)   = cong there (wk-mem-trans (there i) (wk-cong π) (wk-wk δ))
wk-mem-trans (there i) (wk-wk (wk-wk π)) (wk-wk δ)     = cong there (wk-mem-trans (there i) (wk-wk π) (wk-wk δ))

wk-trans-idl : (π : Γ ⊇ Δ) -> wk-trans wk-id π ≡ π
wk-trans-idl wk-ε        = refl
wk-trans-idl (wk-cong π) = cong wk-cong (wk-trans-idl π)
wk-trans-idl (wk-wk π)   = cong wk-wk (wk-trans-idl π)

wk-trans-idr : (π : Γ ⊇ Δ) -> wk-trans π wk-id ≡ π
wk-trans-idr wk-ε        = refl
wk-trans-idr (wk-cong π) = cong wk-cong (wk-trans-idr π)
wk-trans-idr (wk-wk π)   = cong wk-wk (wk-trans-idr π)

wk-trans-comm-id : (π : Γ ⊇ Δ) -> wk-trans π wk-id ≡ wk-trans wk-id π
wk-trans-comm-id π = begin
  wk-trans π wk-id  ≡⟨ wk-trans-idr π ⟩
  π                 ≡˘⟨ wk-trans-idl π ⟩
  wk-trans wk-id π  ∎

wk-assoc : {π₁ : Γ ⊇ Γ₁} {π₂ : Γ₁ ⊇ Γ₂} {π₃ : Γ₂ ⊇ Γ₃} -> wk-trans π₁ (wk-trans π₂ π₃) ≡ wk-trans (wk-trans π₁ π₂) π₃
wk-assoc {π₁ = wk-ε} = refl
wk-assoc {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {π₃ = wk-cong π₃} = cong wk-cong (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
wk-assoc {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {π₃ = wk-wk π₃}   = cong wk-wk (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
wk-assoc {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {π₃ = π₃}           = cong wk-wk (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
wk-assoc {π₁ = wk-wk π₁} {π₂ = π₂} {π₃ = π₃}                   = cong wk-wk (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})

wk-emp-uniq : (π : Γ ⊇ ε) -> π ≡ wk-emp
wk-emp-uniq wk-ε      = refl
wk-emp-uniq (wk-wk π) = cong wk-wk (wk-emp-uniq π)

wk-absurd : Γ ⊇ (Δ ∙ X) -> Δ ⊇ Γ -> ⊥
wk-absurd (wk-cong π) (wk-cong δ) = wk-absurd π δ
wk-absurd (wk-cong π) (wk-wk δ)   = wk-absurd (wk-trans δ (wk-wk π)) wk-id
wk-absurd (wk-wk π)   (wk-cong δ) = wk-absurd π (wk-wk δ)
wk-absurd {X = X} (wk-wk π) (wk-wk δ) = wk-absurd π (wk-wk (wk-prev {X = X} (wk-wk δ)))

wk-id-id : {π : Γ ⊇ Γ} -> π ≡ wk-id
wk-id-id {π = wk-ε} = refl
wk-id-id {π = wk-cong π} rewrite wk-id-id {π = π} = refl
wk-id-id {π = wk-wk π} = ql (wk-absurd π wk-id) (wk-wk π ≡ wk-id)

wk-merge : (π₁ : Γ ⊇ Δ) (π₂ : Γ ⊇ Δ₁)
         -> Σ[ Γ₁ ∈ Ctx ] Σ[ π ∈ Γ ⊇ Γ₁ ] Σ[ π₃ ∈ Γ₁ ⊇ Δ ] Σ[ π₄ ∈ Γ₁ ⊇ Δ₁ ] ((π₁ ≡ wk-trans π π₃) × (π₂ ≡ wk-trans π π₄))
wk-merge wk-ε wk-ε = ε , wk-ε , wk-ε , wk-ε , refl , refl
wk-merge {Γ = Γ ∙ X} (wk-cong π) (wk-cong δ) with wk-merge π δ
... | Γ , π , π₁ , π₂ , eq₁ , eq₂ = Γ ∙ X , wk-cong π , wk-cong π₁ , wk-cong π₂ , cong wk-cong eq₁ , cong wk-cong eq₂
wk-merge {Γ = Γ ∙ X} (wk-cong π) (wk-wk δ) with wk-merge π δ
... | Γ , π , π₁ , π₂ , eq₁ , eq₂ = Γ ∙ X , wk-cong π , wk-cong π₁ , wk-wk π₂ , cong wk-cong eq₁ , cong wk-wk eq₂
wk-merge {Γ = Γ ∙ X} (wk-wk π) (wk-cong δ) with wk-merge π δ
... | Γ , π , π₁ , π₂ , eq₁ , eq₂ = Γ ∙ X , wk-cong π , wk-wk π₁ , wk-cong π₂ , cong wk-wk eq₁ , cong wk-cong eq₂
wk-merge (wk-wk π) (wk-wk δ) with wk-merge π δ
... | Γ , π , π₁ , π₂ , eq₁ , eq₂ = Γ , wk-wk π , π₁ , π₂ , cong wk-wk eq₁ , cong wk-wk eq₂

wk-wk-trans-id : (π : Δ ⊇ (Γ ∙ X)) (i : Γ ∋ Y) -> wk-mem (wk-trans π (wk-wk wk-id)) i ≡ wk-mem π (there i)
wk-wk-trans-id (wk-cong (wk-cong π)) here      = refl
wk-wk-trans-id (wk-cong (wk-cong π)) (there i) = cong (λ x → there (there (wk-mem x i))) (wk-trans-idr π)
wk-wk-trans-id (wk-cong (wk-wk π)) here        = cong (λ x → there (there (wk-mem x here))) (wk-trans-idr π)
wk-wk-trans-id (wk-cong (wk-wk π)) (there i)   = cong (λ x → there (there (wk-mem x (there i)))) (wk-trans-idr π)
wk-wk-trans-id (wk-wk π) here                  = cong there (wk-wk-trans-id π here)
wk-wk-trans-id (wk-wk π) (there i)             = cong there (wk-wk-trans-id π (there i))

mutual
  wk-cong-wk-trans : (π : Δ ⊇ (Γ ∙ X)) (δ : Γ ⊇ Ψ) -> wk-trans (wk-trans π (wk-cong wk-id)) (wk-wk δ) ≡ wk-trans π (wk-wk δ)
  wk-cong-wk-trans (wk-cong π) wk-ε        = wk-trans-idr _
  wk-cong-wk-trans (wk-cong π) (wk-cong δ) = cong wk-wk (wk-cong-trans π δ)
  wk-cong-wk-trans (wk-cong π) (wk-wk δ)   = cong wk-wk (wk-cong-wk-trans π δ)
  wk-cong-wk-trans (wk-wk π) wk-ε          = cong wk-wk (wk-cong-wk-trans π wk-ε)
  wk-cong-wk-trans (wk-wk π) (wk-cong δ)   = cong wk-wk (wk-cong-wk-trans π (wk-cong δ))
  wk-cong-wk-trans (wk-wk π) (wk-wk δ)     = cong wk-wk (wk-cong-wk-trans π (wk-wk δ))

  wk-cong-trans : (π : Δ ⊇ (Γ ∙ X)) (δ : Γ ⊇ Ψ) -> wk-trans (wk-trans π (wk-cong wk-id)) (wk-cong δ) ≡ wk-trans π (wk-cong δ)
  wk-cong-trans (wk-cong π) wk-ε        = wk-trans-idr _
  wk-cong-trans (wk-cong π) (wk-cong δ) = cong wk-cong (wk-cong-trans π δ)
  wk-cong-trans (wk-cong π) (wk-wk δ)   = cong wk-cong (wk-cong-wk-trans π δ)
  wk-cong-trans (wk-wk π) wk-ε          = wk-trans-idr _
  wk-cong-trans (wk-wk π) (wk-cong δ)   = cong wk-wk (wk-cong-trans π (wk-cong δ))
  wk-cong-trans (wk-wk π) (wk-wk δ)     = cong wk-wk (wk-cong-trans π (wk-wk δ))

  wk-wk-trans : (π : Δ ⊇ (Γ ∙ X)) (δ : Γ ⊇ Ψ) -> wk-trans (wk-trans π (wk-wk wk-id)) δ ≡ wk-trans π (wk-wk δ)
  wk-wk-trans (wk-cong π) wk-ε        = cong wk-wk (wk-trans-idr _)
  wk-wk-trans (wk-cong π) (wk-cong δ) = cong wk-wk (wk-cong-trans π δ)
  wk-wk-trans (wk-cong π) (wk-wk δ)   = cong wk-wk (wk-cong-wk-trans π δ)
  wk-wk-trans (wk-wk π) wk-ε          = cong wk-wk (wk-wk-trans π wk-ε)
  wk-wk-trans (wk-wk π) (wk-cong δ)   = cong wk-wk (wk-wk-trans π (wk-cong δ))
  wk-wk-trans (wk-wk π) (wk-wk δ)     = cong wk-wk (wk-wk-trans π (wk-wk δ))

--------------------------------------------------------------------------
-- semantics

module Sem (⟦_⟧ : Ty -> Set) where

  ⟦_⟧ˣ : Ctx -> Set
  ⟦ ε ⟧ˣ     = ⊤
  ⟦ Γ ∙ X ⟧ˣ = ⟦ Γ ⟧ˣ × ⟦ X ⟧

  ⟦_⟧ʷ : Γ ⊇ Δ -> ⟦ Γ ⟧ˣ -> ⟦ Δ ⟧ˣ
  ⟦ wk-ε ⟧ʷ      = idf
  ⟦ wk-cong π ⟧ʷ = < proj₁ ； ⟦ π ⟧ʷ , proj₂ >
  ⟦ wk-wk π ⟧ʷ   = proj₁ ； ⟦ π ⟧ʷ

  ⟦_⟧ᵐ : Γ ∋ X -> ⟦ Γ ⟧ˣ -> ⟦ X ⟧
  ⟦ here ⟧ᵐ    = proj₂
  ⟦ there i ⟧ᵐ = proj₁ ； ⟦ i ⟧ᵐ

  wk-id-coh : ⟦ wk-id {Γ} ⟧ʷ ≡ id
  wk-id-coh {ε}     = refl
  wk-id-coh {Γ ∙ X} rewrite wk-id-coh {Γ} = refl

  {-# REWRITE wk-id-coh #-}

  wk-mem-coh : (π : Γ ⊇ Δ) (i : Δ ∋ X) -> ⟦ wk-mem π i ⟧ᵐ ≡ (⟦ π ⟧ʷ ； ⟦ i ⟧ᵐ)
  wk-mem-coh (wk-cong π) here      = refl
  wk-mem-coh (wk-cong π) (there i) rewrite wk-mem-coh π i = refl
  wk-mem-coh (wk-wk π)   here      rewrite wk-mem-coh π here = refl
  wk-mem-coh (wk-wk π)   (there i) rewrite wk-mem-coh π (there i) = refl

  -- co-contexts

  ⟦_⟧ˣ̃ : Ctx -> Set
  ⟦ ε ⟧ˣ̃     = ⊥
  ⟦ Δ ∙ X ⟧ˣ̃ = ⟦ Δ ⟧ˣ̃ ⊎ ⟦ X ⟧

  ⟦_⟧ʷ̃ : Δ ⊇ Δ₁ -> ⟦ Δ₁ ⟧ˣ̃ -> ⟦ Δ ⟧ˣ̃
  ⟦ wk-ε ⟧ʷ̃ ()
  ⟦ wk-cong π ⟧ʷ̃ (inj₁ x) = inj₁ (⟦ π ⟧ʷ̃ x)
  ⟦ wk-cong π ⟧ʷ̃ (inj₂ y) = inj₂ y
  ⟦ wk-wk π ⟧ʷ̃ x          = inj₁ (⟦ π ⟧ʷ̃ x)

  ⟦_⟧ᵐ̃ : Δ ∋ X -> ⟦ X ⟧ -> ⟦ Δ ⟧ˣ̃
  ⟦ here ⟧ᵐ̃    = inj₂
  ⟦ there i ⟧ᵐ̃ = ⟦ i ⟧ᵐ̃ ； inj₁

  wk-id-coh̃ : ⟦ wk-id {Δ} ⟧ʷ̃ ≡ id
  wk-id-coh̃ {ε} = funext λ ()
  wk-id-coh̃ {Δ ∙ X} = funext λ
    { (inj₁ x) → cong inj₁ (happly wk-id-coh̃ x)
    ; (inj₂ y) → refl
    }

  {-# REWRITE wk-id-coh̃ #-}

  wk-mem-coh̃ : (ρ : Δ ⊇ Δ₁) (i : Δ₁ ∋ X) -> ⟦ wk-mem ρ i ⟧ᵐ̃ ≡ (⟦ i ⟧ᵐ̃ ； ⟦ ρ ⟧ʷ̃)
  wk-mem-coh̃ (wk-cong ρ) here      = funext λ a → refl
  wk-mem-coh̃ (wk-cong ρ) (there i) = funext λ a → cong inj₁ (happly (wk-mem-coh̃ ρ i) a)
  wk-mem-coh̃ (wk-wk ρ) here        = funext λ a → cong inj₁ (happly (wk-mem-coh̃ ρ here) a)
  wk-mem-coh̃ (wk-wk ρ) (there i)   = funext λ a → cong inj₁ (happly (wk-mem-coh̃ ρ (there i)) a)
