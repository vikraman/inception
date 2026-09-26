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
  A B C D A₁ A₂ B₁ B₂ : Ty
  X X' X₁ X₂ Y Y' Z Z' Z₀ Z₁ Z₁' : Ty
  Γ Δ Ψ Γ' Γ'' Γ''' Δ' Δ'' Ψ' Γ₀ Γ₁ Γ₂ Γ₃ Δ₁ : Ctx

data _∋_ : Ctx -> Ty -> Set where
  here  : Γ ∙ A ∋ A
  there : Γ ∋ A -> Γ ∙ B ∋ A

there-injective : {i i' : Γ ∋ A} -> there {B = B} i ≡ there i' -> i ≡ i'
there-injective refl = refl

--------------------------------------------------------------------------
-- weakenings

syntax Wk Γ Δ = Γ ⊇ Δ

data Wk : (Γ Δ : Ctx) -> Set where
  wk-ε    : ε ⊇ ε
  wk-cong : Γ ⊇ Δ -> (Γ ∙ A) ⊇ (Δ ∙ A)
  wk-wk   : Γ ⊇ Δ -> (Γ ∙ A) ⊇ Δ

wk-id : Γ ⊇ Γ
wk-id {Γ = ε}     = wk-ε
wk-id {Γ = Γ ∙ A} = wk-cong wk-id

wk-emp : Γ ⊇ ε
wk-emp {Γ = ε}     = wk-ε
wk-emp {Γ = Γ ∙ A} = wk-wk wk-emp

wk-mem : Γ ⊇ Δ -> Δ ∋ A -> Γ ∋ A
wk-mem (wk-cong π) here      = here
wk-mem (wk-wk π)   here      = there (wk-mem π here)
wk-mem (wk-cong π) (there i) = there (wk-mem π i)
wk-mem (wk-wk π)   (there i) = there (wk-mem π (there i))

wk-trans : Γ ⊇ Δ -> Δ ⊇ Ψ -> Γ ⊇ Ψ
wk-trans wk-ε π₂                   = π₂
wk-trans (wk-cong π₁) (wk-cong π₂) = wk-cong (wk-trans π₁ π₂)
wk-trans (wk-cong π₁) (wk-wk π₂)   = wk-wk (wk-trans π₁ π₂)
wk-trans (wk-wk π₁) π₂             = wk-wk (wk-trans π₁ π₂)

wk-prev : (Γ ∙ A) ⊇ (Δ ∙ B) -> Γ ⊇ Δ
wk-prev (wk-cong π) = π
wk-prev (wk-wk π)   = wk-trans π (wk-wk wk-id)

--------------------------------------------------------------------------
-- weakening laws

wk-mem-id : {i : Γ ∋ A} -> wk-mem wk-id i ≡ i
wk-mem-id {i = here}    = refl
wk-mem-id {i = there i} = cong there wk-mem-id

wk-mem-wk-wk : (π : Γ ⊇ Δ) (i : Δ ∋ A) -> wk-mem (wk-wk {A = B} π) i ≡ there (wk-mem π i)
wk-mem-wk-wk π here      = refl
wk-mem-wk-wk π (there i) = refl

wk-mem-trans : (i : Γ ∋ A) (π₁ : Ψ ⊇ Δ) (π₂ : Δ ⊇ Γ) -> wk-mem π₁ (wk-mem π₂ i) ≡ wk-mem (wk-trans π₁ π₂) i
wk-mem-trans here (wk-cong π₁) (wk-cong π₂) = refl
wk-mem-trans here (wk-cong π₁) (wk-wk π₂)   = cong there (wk-mem-trans here π₁ π₂)
wk-mem-trans here (wk-wk π₁)   (wk-cong π₂) = cong there (wk-mem-trans here π₁ (wk-cong π₂))
wk-mem-trans here (wk-wk π₁)   (wk-wk π₂)   = cong there (wk-mem-trans here π₁ (wk-wk π₂))
wk-mem-trans (there i) (wk-cong π₁) (wk-cong π₂)         = cong there (wk-mem-trans i π₁ π₂)
wk-mem-trans (there i) (wk-wk (wk-cong π₁)) (wk-cong π₂) = cong there (cong there (wk-mem-trans i π₁ π₂))
wk-mem-trans (there i) (wk-wk (wk-wk π₁)) (wk-cong π₂)   = cong there (cong there (wk-mem-trans (there i) π₁ (wk-cong π₂)))
wk-mem-trans (there i) (wk-cong π₁) (wk-wk π₂)           = cong there (wk-mem-trans (there i) π₁ π₂)
wk-mem-trans (there i) (wk-wk (wk-cong π₁)) (wk-wk π₂)   = cong there (wk-mem-trans (there i) (wk-cong π₁) (wk-wk π₂))
wk-mem-trans (there i) (wk-wk (wk-wk π₁)) (wk-wk π₂)     = cong there (wk-mem-trans (there i) (wk-wk π₁) (wk-wk π₂))

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

wk-assoc : {π₁ : Γ ⊇ Γ'} {π₂ : Γ' ⊇ Γ''} {π₃ : Γ'' ⊇ Γ'''} -> wk-trans π₁ (wk-trans π₂ π₃) ≡ wk-trans (wk-trans π₁ π₂) π₃
wk-assoc {π₁ = wk-ε} = refl
wk-assoc {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {π₃ = wk-cong π₃} = cong wk-cong (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
wk-assoc {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {π₃ = wk-wk π₃}   = cong wk-wk (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
wk-assoc {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {π₃ = π₃}           = cong wk-wk (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
wk-assoc {π₁ = wk-wk π₁} {π₂ = π₂} {π₃ = π₃}                   = cong wk-wk (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})

wk-emp-uniq : (π : Γ ⊇ ε) -> π ≡ wk-emp
wk-emp-uniq wk-ε      = refl
wk-emp-uniq (wk-wk π) = cong wk-wk (wk-emp-uniq π)

wk-absurd : Γ ⊇ (Δ ∙ A) -> Δ ⊇ Γ -> ⊥
wk-absurd (wk-cong π) (wk-cong π') = wk-absurd π π'
wk-absurd (wk-cong π) (wk-wk π')   = wk-absurd (wk-trans π' (wk-wk π)) wk-id
wk-absurd (wk-wk π)   (wk-cong π') = wk-absurd π (wk-wk π')
wk-absurd {A = A} (wk-wk π) (wk-wk π') = wk-absurd π (wk-wk (wk-prev {A = A} (wk-wk π')))

wk-id-id : {π : Γ ⊇ Γ} -> π ≡ wk-id
wk-id-id {π = wk-ε} = refl
wk-id-id {π = wk-cong π} rewrite wk-id-id {π = π} = refl
wk-id-id {π = wk-wk π} = ql (wk-absurd π wk-id) (wk-wk π ≡ wk-id)

wk-merge : (π₁ : Γ ⊇ Δ) (π₂ : Γ ⊇ Δ')
         -> Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Γ ⊇ Γ' ] Σ[ π₁' ∈ Γ' ⊇ Δ ] Σ[ π₂' ∈ Γ' ⊇ Δ' ] ((π₁ ≡ wk-trans π π₁') × (π₂ ≡ wk-trans π π₂'))
wk-merge wk-ε wk-ε = ε , wk-ε , wk-ε , wk-ε , refl , refl
wk-merge {Γ = Γ ∙ A} (wk-cong π₁) (wk-cong π₂) with wk-merge π₁ π₂
... | Γ₀ , π₀ , π₁' , π₂' , eq₁ , eq₂ = Γ₀ ∙ A , wk-cong π₀ , wk-cong π₁' , wk-cong π₂' , cong wk-cong eq₁ , cong wk-cong eq₂
wk-merge {Γ = Γ ∙ A} (wk-cong π₁) (wk-wk π₂) with wk-merge π₁ π₂
... | Γ₀ , π₀ , π₁' , π₂' , eq₁ , eq₂ = Γ₀ ∙ A , wk-cong π₀ , wk-cong π₁' , wk-wk π₂' , cong wk-cong eq₁ , cong wk-wk eq₂
wk-merge {Γ = Γ ∙ A} (wk-wk π₁) (wk-cong π₂) with wk-merge π₁ π₂
... | Γ₀ , π₀ , π₁' , π₂' , eq₁ , eq₂ = Γ₀ ∙ A , wk-cong π₀ , wk-wk π₁' , wk-cong π₂' , cong wk-wk eq₁ , cong wk-cong eq₂
wk-merge (wk-wk π₁) (wk-wk π₂) with wk-merge π₁ π₂
... | Γ₀ , π₀ , π₁' , π₂' , eq₁ , eq₂ = Γ₀ , wk-wk π₀ , π₁' , π₂' , cong wk-wk eq₁ , cong wk-wk eq₂

wk-wk-trans-id : (π : Δ ⊇ (Γ ∙ A)) (i : Γ ∋ B) -> wk-mem (wk-trans π (wk-wk wk-id)) i ≡ wk-mem π (there i)
wk-wk-trans-id (wk-cong (wk-cong π)) here      = refl
wk-wk-trans-id (wk-cong (wk-cong π)) (there i) = cong (λ x → there (there (wk-mem x i))) (wk-trans-idr π)
wk-wk-trans-id (wk-cong (wk-wk π)) here        = cong (λ x → there (there (wk-mem x here))) (wk-trans-idr π)
wk-wk-trans-id (wk-cong (wk-wk π)) (there i)   = cong (λ x → there (there (wk-mem x (there i)))) (wk-trans-idr π)
wk-wk-trans-id (wk-wk π) here                  = cong there (wk-wk-trans-id π here)
wk-wk-trans-id (wk-wk π) (there i)             = cong there (wk-wk-trans-id π (there i))

mutual
  wk-cong-wk-trans : (π : Δ ⊇ (Γ ∙ A)) (π' : Γ ⊇ Ψ) -> wk-trans (wk-trans π (wk-cong wk-id)) (wk-wk π') ≡ wk-trans π (wk-wk π')
  wk-cong-wk-trans (wk-cong π) wk-ε         = wk-trans-idr _
  wk-cong-wk-trans (wk-cong π) (wk-cong π') = cong wk-wk (wk-cong-trans π π')
  wk-cong-wk-trans (wk-cong π) (wk-wk π')   = cong wk-wk (wk-cong-wk-trans π π')
  wk-cong-wk-trans (wk-wk π) wk-ε           = cong wk-wk (wk-cong-wk-trans π wk-ε)
  wk-cong-wk-trans (wk-wk π) (wk-cong π')   = cong wk-wk (wk-cong-wk-trans π (wk-cong π'))
  wk-cong-wk-trans (wk-wk π) (wk-wk π')     = cong wk-wk (wk-cong-wk-trans π (wk-wk π'))

  wk-cong-trans : (π : Δ ⊇ (Γ ∙ A)) (π' : Γ ⊇ Ψ) -> wk-trans (wk-trans π (wk-cong wk-id)) (wk-cong π') ≡ wk-trans π (wk-cong π')
  wk-cong-trans (wk-cong π) wk-ε         = wk-trans-idr _
  wk-cong-trans (wk-cong π) (wk-cong π') = cong wk-cong (wk-cong-trans π π')
  wk-cong-trans (wk-cong π) (wk-wk π')   = cong wk-cong (wk-cong-wk-trans π π')
  wk-cong-trans (wk-wk π) wk-ε           = wk-trans-idr _
  wk-cong-trans (wk-wk π) (wk-cong π')   = cong wk-wk (wk-cong-trans π (wk-cong π'))
  wk-cong-trans (wk-wk π) (wk-wk π')     = cong wk-wk (wk-cong-trans π (wk-wk π'))

  wk-wk-trans : (π : Δ ⊇ (Γ ∙ A)) (π' : Γ ⊇ Ψ) -> wk-trans (wk-trans π (wk-wk wk-id)) π' ≡ wk-trans π (wk-wk π')
  wk-wk-trans (wk-cong π) wk-ε         = cong wk-wk (wk-trans-idr _)
  wk-wk-trans (wk-cong π) (wk-cong π') = cong wk-wk (wk-cong-trans π π')
  wk-wk-trans (wk-cong π) (wk-wk π')   = cong wk-wk (wk-cong-wk-trans π π')
  wk-wk-trans (wk-wk π) wk-ε           = cong wk-wk (wk-wk-trans π wk-ε)
  wk-wk-trans (wk-wk π) (wk-cong π')   = cong wk-wk (wk-wk-trans π (wk-cong π'))
  wk-wk-trans (wk-wk π) (wk-wk π')     = cong wk-wk (wk-wk-trans π (wk-wk π'))

--------------------------------------------------------------------------
-- semantics

module Sem (⟦_⟧ : Ty -> Set) where

  ⟦_⟧ˣ : Ctx -> Set
  ⟦ ε ⟧ˣ     = ⊤
  ⟦ Γ ∙ A ⟧ˣ = ⟦ Γ ⟧ˣ × ⟦ A ⟧

  ⟦_⟧ʷ : Γ ⊇ Δ -> ⟦ Γ ⟧ˣ -> ⟦ Δ ⟧ˣ
  ⟦ wk-ε ⟧ʷ      = idf
  ⟦ wk-cong π ⟧ʷ = < proj₁ ； ⟦ π ⟧ʷ , proj₂ >
  ⟦ wk-wk π ⟧ʷ   = proj₁ ； ⟦ π ⟧ʷ

  ⟦_⟧ᵐ : Γ ∋ A -> ⟦ Γ ⟧ˣ -> ⟦ A ⟧
  ⟦ here ⟧ᵐ    = proj₂
  ⟦ there i ⟧ᵐ = proj₁ ； ⟦ i ⟧ᵐ

  wk-id-coh : ⟦ wk-id {Γ} ⟧ʷ ≡ id
  wk-id-coh {ε}     = refl
  wk-id-coh {Γ ∙ A} rewrite wk-id-coh {Γ} = refl

  {-# REWRITE wk-id-coh #-}

  wk-mem-coh : (π : Γ ⊇ Δ) (i : Δ ∋ A) -> ⟦ wk-mem π i ⟧ᵐ ≡ (⟦ π ⟧ʷ ； ⟦ i ⟧ᵐ)
  wk-mem-coh (wk-cong π) here      = refl
  wk-mem-coh (wk-cong π) (there i) rewrite wk-mem-coh π i = refl
  wk-mem-coh (wk-wk π)   here      rewrite wk-mem-coh π here = refl
  wk-mem-coh (wk-wk π)   (there i) rewrite wk-mem-coh π (there i) = refl

  -- co-contexts

  ⟦_⟧ˣ̃ : Ctx -> Set
  ⟦ ε ⟧ˣ̃     = ⊥
  ⟦ Δ ∙ A ⟧ˣ̃ = ⟦ Δ ⟧ˣ̃ ⊎ ⟦ A ⟧

  ⟦_⟧ʷ̃ : Δ ⊇ Δ' -> ⟦ Δ' ⟧ˣ̃ -> ⟦ Δ ⟧ˣ̃
  ⟦ wk-ε ⟧ʷ̃ ()
  ⟦ wk-cong π ⟧ʷ̃ (inj₁ x) = inj₁ (⟦ π ⟧ʷ̃ x)
  ⟦ wk-cong π ⟧ʷ̃ (inj₂ y) = inj₂ y
  ⟦ wk-wk π ⟧ʷ̃ x          = inj₁ (⟦ π ⟧ʷ̃ x)

  ⟦_⟧ᵐ̃ : Δ ∋ A -> ⟦ A ⟧ -> ⟦ Δ ⟧ˣ̃
  ⟦ here ⟧ᵐ̃    = inj₂
  ⟦ there i ⟧ᵐ̃ = ⟦ i ⟧ᵐ̃ ； inj₁

  wk-id-coh̃ : ⟦ wk-id {Δ} ⟧ʷ̃ ≡ id
  wk-id-coh̃ {ε} = funext λ ()
  wk-id-coh̃ {Δ ∙ A} = funext λ
    { (inj₁ x) → cong inj₁ (happly wk-id-coh̃ x)
    ; (inj₂ y) → refl
    }

  {-# REWRITE wk-id-coh̃ #-}

  wk-mem-coh̃ : (σ : Δ ⊇ Δ') (i : Δ' ∋ A) -> ⟦ wk-mem σ i ⟧ᵐ̃ ≡ (⟦ i ⟧ᵐ̃ ； ⟦ σ ⟧ʷ̃)
  wk-mem-coh̃ (wk-cong σ) here      = funext λ a → refl
  wk-mem-coh̃ (wk-cong σ) (there i) = funext λ a → cong inj₁ (happly (wk-mem-coh̃ σ i) a)
  wk-mem-coh̃ (wk-wk σ) here        = funext λ a → cong inj₁ (happly (wk-mem-coh̃ σ here) a)
  wk-mem-coh̃ (wk-wk σ) (there i)   = funext λ a → cong inj₁ (happly (wk-mem-coh̃ σ (there i)) a)
