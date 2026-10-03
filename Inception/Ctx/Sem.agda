module Inception.Ctx.Sem (Ty : Set) (⟦_⟧ : Ty → Set) where

open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂; _,_; <_,_>; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Function using (id)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)

open import Inception.Ctx.Base Ty
open import Inception.Ctx.Wk Ty
open import Inception.Prelude

--------------------------------------------------------------------------
-- semantics

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
