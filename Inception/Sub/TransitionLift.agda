{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.TransitionLift (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_; _$_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)
open Eq.≡-Reasoning using (step-≡-⟩; step-≡-∣; step-≡-⟨; _∎; step-≡)

open import Relation.Binary.PropositionalEquality.Properties using (dcong₂)
open import Agda.Primitive using (Level)

open import Relation.Binary.Reasoning.Syntax

open import Relation.Binary.Definitions
  using (Symmetric; Transitive; Substitutive; Irreflexive
        ; _Respects_; _Respectsˡ_; _Respectsʳ_; _Respects₂_)

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Unit
open import Data.Nat
open import Data.List using (List; _∷_; []; _++_)

open import Inception.Sub.Equality
open import Inception.Sub.Environments R
open import Inception.Sub.Machine R

module LiftMain {R₀ : Ty} (k₀ : ⟦ R₀ ⟧ → R) where

  open MachineMain {R₀ = R₀} k₀
  open EnvMain {R₀ = R₀} k₀

  -- val-wk-lift : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
  --         → (∘ ((M ⊲ γ ∷ tail) {↥ = ↥})) ↠ᵛ (∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}))
  --         → ⟦ ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
  --         → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
  --         → Σ[ Ψ' ∈ Ctx ]
  --           --
  --           Σ[ Γ'' ∈ Ctx ]
  --           Σ[ M'' ∈ PartialTerm Γ'' X' ]
  --           Σ[ πᵣ ∈ Wk Ψ' Γ'' ]
  --           Σ[ πᵥ ∈ Wk Γ' Γ'' ]
  --           Σ[ γᵣ ∈ Env Ψ' ]
  --           Σ[ tailᵣ ∈ ValStack b' T◾ ]
  --           ( (∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥})) ↠ᵛ (∙ (((wk-pt πᵣ M'') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}))
  --             × ( ⟦ ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ (((wk-pt πᵣ M'') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ
  --               × (wk-pt πᵥ M'' ≡ M') ) )
  -- --val-wk-lift {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} Q→Q' Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = {!!}
  -- val-wk-lift {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (S →ᵛ⟨ ∘var-c ⟩．) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = {!!}
  -- val-wk-lift {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (S →ᵛ⟨ ∘var i>>T πᵥ x x₁ x₂ x₃ ⟩．) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = {!!}
  -- val-wk-lift {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (S →ᵛ⟨ ∘lam ⟩．) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = {!!}
  -- val-wk-lift {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (S →ᵛ⟨ ∘unit ⟩．) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = {!!}
  -- val-wk-lift {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (S →ᵛ⟨ x ⟩ Q→Q') Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = {!!}

  {-
  ----
  postulate
    val-wk-lift-∘∙' : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ
          → (tailₗ : ValStack b T◾)
          --→ (vs-height tail ≡ vs-height tailₗ)
          → (vw : VSWk tailₗ tail)
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ Γ'' ∈ Ctx ]
            Σ[ M'' ∈ PartialTerm Γ'' X' ]
            Σ[ πᵣ ∈ Wk Ψ' Γ'' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tailₗ) {↥ = ↥}) →ᵛ ∙ (((wk-pt πᵣ M'') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
                --× (vs-height tail' ≡ vs-height tailᵣ)
                × (VSWk tailᵣ tail')
                )

  postulate
    val-wk-lift-∘∘' : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ
          → (tailₗ : ValStack b T◾)
          --→ (vs-height tail ≡ vs-height tailₗ)
          → (vw : VSWk tailₗ tail)
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tailₗ) {↥ = ↥}) →ᵛ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              × EnvEq πᵣ γᵣ γ'
              --× (vs-height tail' ≡ vs-height tailᵣ)
              × (VSWk tailᵣ tail')
              )
  ----

  val-wk-lift-∘ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → (∘ ((M ⊲ γ ∷ tail) {↥ = ↥})) ↠ᵛ (∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}))
          → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ
          → (tailₗ : ValStack b T◾)
          --→ (vs-height tail ≡ vs-height tailₗ)
          → (vw : VSWk tailₗ tail)
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ Γ'' ∈ Ctx ]
            Σ[ M'' ∈ PartialTerm Γ'' X' ]
            Σ[ πᵣ ∈ Wk Ψ' Γ'' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( (∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tailₗ) {↥ = ↥})) ↠ᵛ (∙ ((wk-pt πᵣ M'' ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}))
              --× (vs-height tail' ≡ vs-height tailᵣ)
              × (VSWk tailᵣ tail')
              )

  val-wk-lift-∘ {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (S →ᵛ⟨ laststep ⟩．) {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vw =
                let

                  IH = val-wk-lift-∘∙' {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} laststep {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vw
                  Ψ'↑    = proj₁ IH
                  Γ''↑   = proj₁ (proj₂ IH)
                  M''↑   = proj₁ (proj₂ (proj₂ IH))
                  πᵣ↑    = proj₁ (proj₂ (proj₂ (proj₂ IH)))
                  γᵣ↑    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
                  tailᵣ↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
                  S→T↑   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))
                  vs≡↑   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))

                in
                Ψ'↑ , Γ''↑ , M''↑ , πᵣ↑ , γᵣ↑ , tailᵣ↑ , (_ →ᵛ⟨ S→T↑ ⟩．) , vs≡↑
                --Ψ'↑ , Γ''↑ , M''↑ , πᵣ↑ , πᵥ↑ , γᵣ↑ , tailᵣ↑ , (_ →ᵛ⟨ S→T↑ ⟩．) , Q≡Q'↑ , π≡↑ , vs≡↑
  val-wk-lift-∘ {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (_→ᵛ⟨_⟩_ S {S' = ∘ (M₁ ⊲ γ₁ ∷ tail'')} S→S' S'→T) {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vw =
                let

                  IH = val-wk-lift-∘∘' S→S' {πₗ = πₗ} ϖ tailₗ vw
                  Ψ'↑     = proj₁ IH
                  πᵣ↑     = proj₁ (proj₂ IH)
                  γᵣ↑     = proj₁ (proj₂ (proj₂ IH))
                  tailᵣ↑  = proj₁ (proj₂ (proj₂ (proj₂ IH)))
                  S→S'↑   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
                  ϖ↑    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
                  vw↑    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))

                  IH2 = val-wk-lift-∘ S'→T {πₗ = πᵣ↑} {γₗ = γᵣ↑} ϖ↑ tailᵣ↑ vw↑

                  Ψ'↑*     = proj₁ IH2
                  Γ''↑*     = proj₁ (proj₂ IH2)
                  M''*     = proj₁ (proj₂ (proj₂ IH2))
                  πᵣ↑*  = proj₁ (proj₂ (proj₂ (proj₂ IH2)))
                  γᵣ↑*   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH2))))
                  tailᵣ*    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH2)))))
                  S'→T↑*    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH2))))))
                  vw↑*    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH2))))))

                in
                {!!} , {!!} , {!!} , {!!} , {!!} , tailᵣ* , (_ →ᵛ⟨ S→S'↑ ⟩ S'→T↑*) , vw↑*
  val-wk-lift-∘ {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (_→ᵛ⟨_⟩_ S {S' = ∙ x} S→S' S'→T) {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vw = {!!}

{- YYY
  val-wk-lift-∘ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → (∘ ((M ⊲ γ ∷ tail) {↥ = ↥})) ↠ᵛ (∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}))
          --→ (Q≡Q' : ⟦ ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ)
          --→ {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ Γ'' ∈ Ctx ]
            Σ[ M'' ∈ PartialTerm Γ'' X' ]
            Σ[ πᵣ ∈ Wk Ψ' Γ'' ]
            --Σ[ πᵥ ∈ Wk Γ' Γ'' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( (∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥})) ↠ᵛ (∙ ((wk-pt πᵣ M'' ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}))
              -- × ⟦ ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((wk-pt πᵣ M'' ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ
              -- × (wk-pt πᵥ M'' ≡ M')
              × (vs-height tail' ≡ vs-height tailᵣ))
  --val-wk-lift-∘ {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} S→T Q≡Q' VH {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = ?
  --? , ? , ? , ? , ? , ? , ? , ? , ? , ? , ?

  val-wk-lift-∘ {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (S →ᵛ⟨ laststep ⟩．) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                let

                  IH = val-wk-lift-∘∙ {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} laststep {πₗ = πₗ} {γₗ = γₗ} ϖ
                  Ψ'↑    = proj₁ IH
                  Γ''↑   = proj₁ (proj₂ IH)
                  M''↑   = proj₁ (proj₂ (proj₂ IH))
                  πᵣ↑    = proj₁ (proj₂ (proj₂ (proj₂ IH)))
                  γᵣ↑    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
                  tailᵣ↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
                  S→T↑   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))
                  vs≡↑   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))

                in
                Ψ'↑ , Γ''↑ , M''↑ , πᵣ↑ , γᵣ↑ , tailᵣ↑ , (_ →ᵛ⟨ S→T↑ ⟩．) , vs≡↑
                --Ψ'↑ , Γ''↑ , M''↑ , πᵣ↑ , πᵥ↑ , γᵣ↑ , tailᵣ↑ , (_ →ᵛ⟨ S→T↑ ⟩．) , Q≡Q'↑ , π≡↑ , vs≡↑
  val-wk-lift-∘ {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (_→ᵛ⟨_⟩_ S {S' = ∘ (M₁ ⊲ γ₁ ∷ tail'')} S→S' S'→T) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                let

                  IH = val-wk-lift-∘∘ S→S' {πₗ = πₗ} ϖ
                  Ψ'↑     = proj₁ IH
                  πᵣ↑     = proj₁ (proj₂ IH)
                  γᵣ↑     = proj₁ (proj₂ (proj₂ IH))
                  tailᵣ↑  = proj₁ (proj₂ (proj₂ (proj₂ IH)))
                  S→S'↑   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
                  ϖ↑    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
                  vs≡↑    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))

                  -- Ψ'↑    = proj₁ IH
                  -- πᵣ↑   = proj₁ (proj₂ IH)
                  -- γᵣ↑   = proj₁ (proj₂ (proj₂ IH))
                  -- wk≡ᵣ↑    = proj₁ (proj₂ (proj₂ (proj₂ IH)))
                  -- tailᵣ↑    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
                  -- S→S'↑    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
                  -- Q≡Q'↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))
                  -- vs≡↑ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))

                  -- ϖ' = (valstate-env-eq S→S'↑)
                  -- ϖ'' = env-eq-trans {!!} {!!} ϖ' ϖ

                  IH2 = val-wk-lift-∘ S'→T {πₗ = πᵣ↑} {γₗ = γᵣ↑} ϖ↑

                  Ψ'↑*     = proj₁ IH2
                  Γ''↑*     = proj₁ (proj₂ IH2)
                  M''*     = proj₁ (proj₂ (proj₂ IH2))
                  πᵣ↑*  = proj₁ (proj₂ (proj₂ (proj₂ IH2)))
                  γᵣ↑*   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH2))))
                  tailᵣ*    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH2)))))
                  S'→T↑*    = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH2))))))
                  vs≡↑*    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH2))))))

                in
                {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , (_ →ᵛ⟨ S→S'↑ ⟩ {!S'→T↑*!}) , {!!}
  val-wk-lift-∘ {M = M} {γ = γ} {tail = tail} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (_→ᵛ⟨_⟩_ S {S' = ∙ x} S→S' S'→T) {πₗ = πₗ} {γₗ = γₗ} ϖ = {!!}
  YYY -}

{-
  val-wk-pair-lift-∘ : {M : PartialTerm Γ Z} {γ : Env Γ} {tail : ValStack b (X' `× Y')} {↥ : BottomTypeEqualsNextType b Z (X' `× Y')} {LHS : V̲a̲l̲ Γ' X'} {RHS : V̲a̲l̲ Γ' Y'} {γ' : Env Γ'} --{tail' : ValStack b' (X' `× Y')} {↥' : BottomTypeEqualsNextType b' (X' `× Y') (X' `× Y')}
          → (∘ ((M ⊲ γ ∷ tail) {↥ = ↥})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ' ∷ □) {↥ = 🗆}))
          → ⟦ ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ' ∷ □) {↥ = 🗆}) ⟧ᵛꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → Σ[ Ψ' ∈ Ctx ]
            --
            Σ[ Γ'' ∈ Ctx ]
            Σ[ LHS' ∈ V̲a̲l̲ Γ'' X' ]
            Σ[ RHS' ∈ V̲a̲l̲ Γ'' Y' ]
            Σ[ πᵣ ∈ Wk Ψ' Γ'' ]
            Σ[ πᵥ ∈ Wk Γ' Γ'' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            --Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( (∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πᵣ LHS') (wk-v̲a̲l̲ πᵣ RHS') ⊲ γᵣ ∷ □) {↥ = 🗆}))
              × ( ⟦ ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πᵣ LHS') (wk-v̲a̲l̲ πᵣ RHS') ⊲ γᵣ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ
                × (pa̲i̲r̲ (wk-v̲a̲l̲ πᵥ LHS') (wk-v̲a̲l̲ πᵥ RHS') ≡ pa̲i̲r̲ LHS RHS) ) )

  val-wk-pair-lift-∘ {Γ = Γ} {b = empty} {Γ' = Γ'} {Ψ = Ψ} {M = ⇡ var i} {γ = γ} {tail = □} {↥ = 🗆} {LHS = LHS} {RHS = RHS} {γ' = γ'} (_→ᵛ⟨_⟩． {T◾ = .(_ `× _)} (∘ ((⇡ var i ⊲ γ ∷ □) {↥ = 🗆})) laststep) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                     let

                       IH = val-wk-lift-∘∙ {M = ⇡ var i} {γ = γ} {tail = □} {↥ = 🗆} {M' = ⭭ pa̲i̲r̲ LHS RHS} {γ' = γ'} {tail' = □} {↥' = 🗆} laststep Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ}

                       t : ∘ wk-pt πₗ (⇡ var i) ⊲ γₗ ∷ □ →ᵛ ∙ wk-pt (proj₁ (proj₂ (proj₂ (proj₂ IH)))) (proj₁ (proj₂ (proj₂ IH))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))
                       t = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))))

                       eq = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))))))
                       eq' = pair-val-eq eq
                       eq₂ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))))))
                       eq₂' = vs-zero-eq eq₂
                       πᵣ↑ = proj₁ (proj₂ (proj₂ (proj₂ IH)))
                       πᵥ↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))

                       Q≡Q'↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))))
                       π≡π'↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))))))

                       t' : ∘ ⇡ var (wk-mem πₗ i) ⊲ γₗ ∷ □ →ᵛ ∙ ⭭ pa̲i̲r̲ (wk-v̲a̲l̲ (proj₁ (proj₂ (proj₂ (proj₂ IH)))) (proj₁ eq')) (wk-v̲a̲l̲ (proj₁ (proj₂ (proj₂ (proj₂ IH)))) (proj₁ (proj₂ eq'))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))
                       t' = subst (λ x → ∘ wk-pt πₗ (⇡ var i) ⊲ γₗ ∷ □ →ᵛ ∙ wk-pt (proj₁ (proj₂ (proj₂ (proj₂ IH)))) x ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))) ) (sym (proj₂ (proj₂ eq'))) t

                       t'' = subst (λ x → ∘ ⇡ var (wk-mem πₗ i) ⊲ γₗ ∷ □ →ᵛ ∙ ⭭ pa̲i̲r̲ (wk-v̲a̲l̲ (proj₁ (proj₂ (proj₂ (proj₂ IH)))) (proj₁ eq')) (wk-v̲a̲l̲ (proj₁ (proj₂ (proj₂ (proj₂ IH)))) (proj₁ (proj₂ eq'))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ x) eq₂' t'

                       Q-eq-goal : ⟦ ∘ ((wk-pt πₗ (⇡ var i) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ≡ ⟦ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πᵣ↑ (proj₁ eq')) (wk-v̲a̲l̲ πᵣ↑ (proj₁ (proj₂ eq'))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ □) {↥ = 🗆}) ⟧ᵛꟴ
                       Q-eq-goal =  ⟦ ∘ ((wk-pt πₗ (⇡ var i) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ
                                   ≡⟨ refl ⟩
                                     ⟦ wk-mem πₗ i ⟧ᵐ ⟦ γₗ ⟧ᴱ
                                   ≡⟨ Q≡Q'↑ ⟩
                                     ⟦ ∙ wk-pt πᵣ↑ (proj₁ (proj₂ (proj₂ IH))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))) ⟧ᵛꟴ
                                   ≡⟨ cong (λ x → ⟦ ∙ wk-pt πᵣ↑ (proj₁ (proj₂ (proj₂ IH))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ x ⟧ᵛꟴ) eq₂' ⟩
                                      ⟦ ∙ wk-pt πᵣ↑ (proj₁ (proj₂ (proj₂ IH))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ □ ⟧ᵛꟴ
                                   ≡⟨ cong (λ x → ⟦ ∙ wk-pt πᵣ↑ x ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ □ ⟧ᵛꟴ) (sym (proj₂ (proj₂ eq'))) ⟩
                                   ⟦ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πᵣ↑ (proj₁ eq')) (wk-v̲a̲l̲ πᵣ↑ (proj₁ (proj₂ eq'))) ⊲ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ∎

                       wk-eq-goal₀ : ⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πᵥ↑ (proj₁ eq')) (wk-v̲a̲l̲ πᵥ↑ (proj₁ (proj₂ eq'))) ≡ ⭭ pa̲i̲r̲ LHS RHS
                       wk-eq-goal₀ =    ⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πᵥ↑ (proj₁ eq')) (wk-v̲a̲l̲ πᵥ↑ (proj₁ (proj₂ eq')))
                                     ≡⟨ refl ⟩
                                        wk-pt πᵥ↑ (⭭ pa̲i̲r̲ (proj₁ eq') (proj₁ (proj₂ eq')))
                                     ≡⟨ cong (wk-pt πᵥ↑) (proj₂ (proj₂ eq')) ⟩
                                        wk-pt πᵥ↑ (proj₁ (proj₂ (proj₂ IH)))
                                     ≡⟨ π≡π'↑  ⟩
                                        ⭭ pa̲i̲r̲ LHS RHS ∎

                       wk-eq-goal : pa̲i̲r̲ (wk-v̲a̲l̲ πᵥ↑ (proj₁ eq')) (wk-v̲a̲l̲ πᵥ↑ (proj₁ (proj₂ eq'))) ≡ pa̲i̲r̲ LHS RHS
                       wk-eq-goal = pt-⭭-inj wk-eq-goal₀
                     in
                     proj₁ IH ,  proj₁ (proj₂ IH) , proj₁ eq' , proj₁ (proj₂ eq') , πᵣ↑ , πᵥ↑ , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))) , ( _ →ᵛ⟨ t'' ⟩．) , Q-eq-goal , wk-eq-goal

  val-wk-pair-lift-∘ {Γ = Γ} {b = non-empty} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {LHS = LHS} {RHS = RHS} {γ' = γ'} (_→ᵛ⟨_⟩_ S {S' = ∘ (M₁ ⊲ γ₁ ∷ tail₁)} Q→Q' Q→*Q') Q≡Q' ϖ = --{!!}
                     let
                       IH = val-wk-pair-lift-∘ Q→*Q' {!!} {!!}
                     in
                     {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}
  val-wk-pair-lift-∘ {Γ = Γ} {b = non-empty} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {LHS = LHS} {RHS = RHS} {γ' = γ'} (_→ᵛ⟨_⟩_ S {S' = ∙ x} Q→Q' Q→*Q') Q≡Q' ϖ = {!!}
                     --let
                     --  IH = val-wk-pair-lift-∘ Q→*Q' ? ?
                     --in
                     --{!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}

  val-wk-pair-lift-∘ {Γ = Γ} {b = empty} {Γ' = Γ'} {Ψ = Ψ} {M = ⇡ M} {γ = γ} {tail = □} {↥ = 🗆} {LHS = LHS} {RHS = RHS} {γ' = γ'} (S →ᵛ⟨ Q→Q' ⟩ Q→*Q') Q≡Q' ϖ = {!!}

  -- val-wk-pair-lift-∘ {Γ = Γ} {b = non-empty} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {LHS = LHS} {RHS = RHS} {γ' = γ'} (_→ᵛ⟨_⟩_ S {S' = S'} Q→Q' Q→*Q') Q≡Q' ϖ = {!!}
  -- val-wk-pair-lift-∘ {Γ = Γ} {b = empty} {Γ' = Γ'} {Ψ = Ψ} {M = ⇡ M} {γ = γ} {tail = □} {↥ = 🗆} {LHS = LHS} {RHS = RHS} {γ' = γ'} (S →ᵛ⟨ Q→Q' ⟩ Q→*Q') Q≡Q' ϖ = {!!}

  --val-wk-pair-lift-∘ {Γ = Γ} {b = b} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = tail} {↥ = ↥} {LHS = LHS} {RHS = RHS} {γ' = γ'} (S →ᵛ⟨ Q→Q' ⟩ Q→*Q') Q≡Q' ϖ = {!!}
  --                   {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}

  -- x     : (∘ ⇡ wk-val π₁ M ⊲ γ ∷ □) ↠ᵛ
  --         (∙ ⭭ pa̲i̲r̲ LHS RHS ⊲ γ'' ∷ □)
-}

  --------------------------------------------------

  cs-height : CompStack Δ X → ℕ
  cs-height ◻ = 0
  cs-height (x ⊲ γ ⦂⦂ cs) = suc (cs-height cs)

  comp-wk-lift-∘∘ :
          {-
            {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → ⟦ ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          -}
            {W : Γ ⊢ᶜ Z} {γ : Env Γ} {cs : CompStack Δ Z} {π : Wk Γ Δ} {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
            {W' : Γ' ⊢ᶜ Z} {γ' : Env Γ'} {cs' : CompStack Δ' Z} {π' : Wk Γ' Δ'} {wk≡' : ⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs' ⟧ᴱ}
          → (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡})) →ᶜ ((∘⟨ W' ⊰ γ' ╎ cs' ⟩) {π = π'} {wk≡ = wk≡'})
          → ⟦ (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡})) ⟧ᶜꟴ ≡ ⟦ ((∘⟨ W' ⊰ γ' ╎ cs' ⟩) {π = π'} {wk≡ = wk≡'}) ⟧ᶜꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}

          {-
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ Γ'' ∈ Ctx ]
            Σ[ M'' ∈ PartialTerm Γ'' X' ]
            Σ[ πᵣ ∈ Wk Ψ' Γ'' ]
            Σ[ πᵥ ∈ Wk Γ' Γ'' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) →ᵛ ∙ (((wk-pt πᵣ M'') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              × ( ⟦ ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ (((wk-pt πᵣ M'') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ
                × (wk-pt πᵥ M'' ≡ M') ) )
          -}

          → Σ[ Ψ' ∈ Ctx ]
            Σ[ Γ'' ∈ Ctx ]
            Σ[ W'' ∈ Comp Γ'' Z ]
            Σ[ πᵣ ∈ Wk Ψ' Γ'' ]
            Σ[ πᵥ ∈ Wk Γ' Γ'' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            --
            --Σ[ wk≡ᵣ ∈ ⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ ]
            Σ[ Δᵣ ∈ Ctx ]
            Σ[ πₚ ∈ Wk Ψ' Δᵣ ]
            Σ[ csᵣ ∈ CompStack Δᵣ Z ]
            Σ[ wk≡ₚ ∈ ⟦ πₚ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ topCsEnv csᵣ ⟧ᴱ ]
            --{!!}
             ( (((∘⟨ wk-comp πₗ W ⊰ γₗ ╎ cs ⟩) {π = wk-trans πₗ π} {wk≡ = ⟦ wk-trans πₗ π ⟧ʷ ⟦ γₗ ⟧ᴱ ≡⟨ sym (wk-sem-trans πₗ π ⟦ γₗ ⟧ᴱ) ⟩ ⟦ π ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) ≡⟨ cong (⟦ π ⟧ʷ) wk≡ₗ ⟩ ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡⟨ wk≡ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎ })) →ᶜ ((∘⟨ wk-comp πᵣ W'' ⊰ γᵣ ╎ csᵣ ⟩) {π = πₚ} {wk≡ = wk≡ₚ})
               × ⟦ (((∘⟨ wk-comp πₗ W ⊰ γₗ ╎ cs ⟩) {π = wk-trans πₗ π} {wk≡ = ⟦ wk-trans πₗ π ⟧ʷ ⟦ γₗ ⟧ᴱ ≡⟨ sym (wk-sem-trans πₗ π ⟦ γₗ ⟧ᴱ) ⟩ ⟦ π ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) ≡⟨ cong (⟦ π ⟧ʷ) wk≡ₗ ⟩ ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡⟨ wk≡ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎})) ⟧ᶜꟴ ≡ ⟦ ((∘⟨ wk-comp πᵣ W'' ⊰ γᵣ ╎ csᵣ ⟩) {π = πₚ} {wk≡ = wk≡ₚ}) ⟧ᶜꟴ
               × (cs-height csᵣ ≡ cs-height cs') )

  --comp-wk-lift-∘∘ {Γ = Γ} {Z = Z} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {Ψ = Ψ} {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {cs' = cs'} {π' = π'} {wk≡' = wk≡'} W→W' W≡W' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = {!!}
  comp-wk-lift-∘∘ {Γ = Γ} {Z = Z} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {Ψ = Ψ} {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {cs' = cs'} {π' = π'} {wk≡' = wk≡'} (∘push {Γ = Γ} {N = N}) W≡W' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                   wk≡'' = ⟦ wk-trans πₗ π ⟧ʷ ⟦ γₗ ⟧ᴱ
                         ≡⟨ sym (wk-sem-trans πₗ π ⟦ γₗ ⟧ᴱ) ⟩
                           ⟦ π ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                         ≡⟨ cong (⟦ π ⟧ʷ) wk≡ₗ ⟩
                           ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ
                         ≡⟨ wk≡ ⟩
                           ⟦ topCsEnv cs ⟧ᴱ ∎
                 in
                  Ψ , Γ , W' , πₗ , πₜ , γₗ , Ψ , wk-id , (((wk-comp (wk-cong πₗ) N) ⊲ γₗ ⦂⦂ cs) {π = wk-trans πₗ π} {wk≡ = wk≡''}) , refl , (∘push {wk≡ₓ = wk≡''} {wk≡ = wk≡''}) ,
                  ((< idf , ⟦ πₗ ⟧ʷ ； ⟦ W' ⟧ᶜ > ； τ ； (< (λ r → proj₁ r) ； ⟦ πₗ ⟧ʷ , (λ r → proj₂ r) > ； ⟦ N ⟧ᶜ) ♯) ⟦ γₗ ⟧ᴱ ⟦ cs ⟧ᴷ
                 ≡⟨ refl ⟩
                   ⟦ W' ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) (λ z → ⟦ N ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀))
                 ≡⟨ cong (⟦ W' ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)) (extensionality λ x → sym (lem0 cs (⟦ N ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , x)))) ⟩
                   ⟦ W' ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → ⟦ N ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , y) k) k₀)
                 ≡⟨ refl ⟩
                  (⟦ πₗ ⟧ʷ ； ⟦ W' ⟧ᶜ) ⟦ γₗ ⟧ᴱ ⟦ (wk-comp (wk-cong πₗ) N ⊲ γₗ ⦂⦂ cs) {π = wk-trans πₗ π} {wk≡ = wk≡''} ⟧ᴷ ∎) ,
                  refl
                  -- ? , ? , ? , ? , ? , ? , ? , ? , ? , ? , ? , ? , ?
  comp-wk-lift-∘∘ {Γ = Γ} {Z = Z} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {Ψ = Ψ} {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {cs' = cs'} {π' = π'} {wk≡' = wk≡'} (∘sub {N = N}) W≡W' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = -- {!!}
                 let
                   wk≡'' = ⟦ wk-trans πₗ π ⟧ʷ ⟦ γₗ ⟧ᴱ
                         ≡⟨ sym (wk-sem-trans πₗ π ⟦ γₗ ⟧ᴱ) ⟩
                           ⟦ π ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                         ≡⟨ cong (⟦ π ⟧ʷ) wk≡ₗ ⟩
                           ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ
                         ≡⟨ wk≡ ⟩
                           ⟦ topCsEnv cs ⟧ᴱ ∎
                 in
                  Ψ ∙ `V , Γ ∙ `V , W' , wk-cong πₗ , wk-id , ((γₗ ﹐﹝ wk-comp πₗ N ╎ cs ﹞) {π = wk-trans πₗ π} {wk≡ = wk≡''}) , Δ , wk-wk (wk-trans πₗ π) , cs , wk≡'' , (∘sub {wk≡ₓ = wk≡''}) , refl , refl
  comp-wk-lift-∘∘ {Γ = Γ} {Z = Z} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {cs' = cs'} {π' = π'} {wk≡' = wk≡'} (∘pm π₁ x π'') W≡W' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = --{!!}
                  -- Goal: ∘⟨ pm (wk-val πₗ (wk-val π₁ M)) (wk-comp (wk-cong (wk-cong πₗ)) (wk-comp (wk-cong (wk-cong π₁)) W₁)) ⊰ γₗ ╎ cs ⟩ →ᶜ ∘⟨ wk-comp ?3 ?2 ⊰ ?5 ╎ ?8 ⟩
                  {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , ∘pm πₗ {!!} {!!} , {!!} , {!!}
  comp-wk-lift-∘∘ {Γ = Γ} {Z = Z} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {cs' = cs'} {π' = π'} {wk≡' = wk≡'} (∘var x π'' x₁ πᵥ) W≡W' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = {!!}
                  -- ? , ? , ? , ? , ? , ? , ? , ? , ? , ? , ? , ? , ?

  {-
  comp-wk-lift : {W : Γ ⊢ᶜ Z} {γ : Env Γ} {cs : CompStack Δ Z} {π : Wk Γ Δ} {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
          {W' : Γ' ⊢ᶜ Z} {γ' : Env Γ'} {cs' : CompStack Δ' Z} {π' : Wk Γ' Δ'} {wk≡' : ⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs' ⟧ᴱ}
          → (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡})) →ᶜ ((∘⟨ W' ⊰ γ' ╎ cs' ⟩) {π = π'} {wk≡ = wk≡'})
          → ⟦ (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡})) ⟧ᶜꟴ ≡ ⟦ ((∘⟨ W' ⊰ γ' ╎ cs' ⟩) {π = π'} {wk≡ = wk≡'}) ⟧ᶜꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ wk≡ᵣ ∈ ⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ ]
            Σ[ Δᵣ ∈ Ctx ]
            Σ[ πₚ ∈ Wk Ψ' Δᵣ ]
            Σ[ csᵣ ∈ CompStack Δᵣ Z ]
            Σ[ wk≡ₚ ∈ ⟦ πₚ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ topCsEnv csᵣ ⟧ᴱ ]
             ( (((∘⟨ wk-comp πₗ W ⊰ γₗ ╎ cs ⟩) {π = wk-trans πₗ π} {wk≡ = ⟦ wk-trans πₗ π ⟧ʷ ⟦ γₗ ⟧ᴱ ≡⟨ sym (wk-sem-trans πₗ π ⟦ γₗ ⟧ᴱ) ⟩ ⟦ π ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) ≡⟨ cong (⟦ π ⟧ʷ) wk≡ₗ ⟩ ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡⟨ wk≡ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎ })) →ᶜ ((∘⟨ wk-comp πᵣ W' ⊰ γᵣ ╎ csᵣ ⟩) {π = πₚ} {wk≡ = wk≡ₚ})
               × ⟦ (((∘⟨ wk-comp πₗ W ⊰ γₗ ╎ cs ⟩) {π = wk-trans πₗ π} {wk≡ = ⟦ wk-trans πₗ π ⟧ʷ ⟦ γₗ ⟧ᴱ ≡⟨ sym (wk-sem-trans πₗ π ⟦ γₗ ⟧ᴱ) ⟩ ⟦ π ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) ≡⟨ cong (⟦ π ⟧ʷ) wk≡ₗ ⟩ ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡⟨ wk≡ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎})) ⟧ᶜꟴ ≡ ⟦ ((∘⟨ wk-comp πᵣ W' ⊰ γᵣ ╎ csᵣ ⟩) {π = πₚ} {wk≡ = wk≡ₚ}) ⟧ᶜꟴ
               × (height csᵣ ≡ height cs') )

  comp-wk-lift {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {Ψ = Ψ} {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {π' = π'} {wk≡' = wk≡'} (∘push {Γ = Γ} {N = N}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                   wk≡'' = ⟦ wk-trans πₗ π ⟧ʷ ⟦ γₗ ⟧ᴱ
                         ≡⟨ sym (wk-sem-trans πₗ π ⟦ γₗ ⟧ᴱ) ⟩
                           ⟦ π ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                         ≡⟨ cong (⟦ π ⟧ʷ) wk≡ₗ ⟩
                           ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ
                         ≡⟨ wk≡ ⟩
                           ⟦ topCsEnv cs ⟧ᴱ ∎
                 in
                 Ψ , πₗ , γₗ , wk≡ₗ , Ψ , wk-id , (((wk-comp (wk-cong πₗ) N) ⊲ γₗ ⦂⦂ cs) {π = wk-trans πₗ π}
                  {wk≡ = wk≡''}) ,
                 refl , (∘push {wk≡ₓ = wk≡''} {wk≡ = wk≡''} ) ,
                 ((< idf , ⟦ πₗ ⟧ʷ ； ⟦ W' ⟧ᶜ > ； τ ； (< (λ r → proj₁ r) ； ⟦ πₗ ⟧ʷ , (λ r → proj₂ r) > ； ⟦ N ⟧ᶜ) ♯) ⟦ γₗ ⟧ᴱ ⟦ cs ⟧ᴷ
                 ≡⟨ refl ⟩
                   ⟦ W' ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) (λ z → ⟦ N ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀))
                 ≡⟨ cong (⟦ W' ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)) (extensionality λ x → sym (lem0 cs (⟦ N ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , x)))) ⟩
                   ⟦ W' ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → ⟦ N ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , y) k) k₀)
                 ≡⟨ refl ⟩
                  (⟦ πₗ ⟧ʷ ； ⟦ W' ⟧ᶜ) ⟦ γₗ ⟧ᴱ ⟦ (wk-comp (wk-cong πₗ) N ⊲ γₗ ⦂⦂ cs) {π = wk-trans πₗ π} {wk≡ = wk≡''} ⟧ᴷ ∎) ,
                 refl

  comp-wk-lift {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {Ψ = Ψ} {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {π' = π'} {wk≡' = wk≡'} (∘sub {N = N}) Q≡Q' {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                   wk≡'' = ⟦ wk-trans πₗ π ⟧ʷ ⟦ γₗ ⟧ᴱ
                         ≡⟨ sym (wk-sem-trans πₗ π ⟦ γₗ ⟧ᴱ) ⟩
                           ⟦ π ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                         ≡⟨ cong (⟦ π ⟧ʷ) wk≡ₗ ⟩
                           ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ
                         ≡⟨ wk≡ ⟩
                           ⟦ topCsEnv cs ⟧ᴱ ∎
                 in
                 Ψ ∙ `V ,
                 wk-cong πₗ ,
                 ((γₗ ﹐﹝ wk-comp πₗ N ╎ cs ﹞) {π = wk-trans πₗ π} {wk≡ = wk≡''}) ,
                 (⟦ wk-cong πₗ ⟧ʷ ⟦ (γₗ ﹐﹝ wk-comp πₗ N ╎ cs ﹞) {π = wk-trans πₗ π} {wk≡ = wk≡''} ⟧ᴱ
                 ≡⟨ refl ⟩
                   < (λ r → proj₁ r) ； ⟦ πₗ ⟧ʷ , (λ r → proj₂ r) > (⟦ γₗ ⟧ᴱ , (⟦ πₗ ⟧ʷ ； ⟦ N ⟧ᶜ) ⟦ γₗ ⟧ᴱ ⟦ cs ⟧ᴷ)
                 ≡⟨ refl ⟩
                   ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , (⟦ N ⟧ᶜ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)) ⟦ cs ⟧ᴷ
                 ≡⟨ cong₂ (λ x y → x , (⟦ N ⟧ᶜ y) ⟦ cs ⟧ᴷ ) wk≡ₗ wk≡ₗ ⟩
                   ⟦ γ ⟧ᴱ , ⟦ N ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ
                 ≡⟨ refl ⟩
                  ⟦ (γ ﹐﹝ N ╎ cs ﹞) {π = π} {wk≡ = wk≡} ⟧ᴱ ∎) ,
                 Δ ,
                 wk-wk (wk-trans πₗ π) ,
                 cs ,
                 wk≡'' ,
                 (∘sub {wk≡ₓ = wk≡''}) ,
                 refl ,
                 refl

  comp-wk-lift {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {Ψ = Ψ} {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {π' = π'} {wk≡' = wk≡'} (∘pm π₁ M→M' π'') Q≡Q' {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
               {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}

  comp-wk-lift {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {π' = π'} {wk≡' = wk≡'} (∘var x π'' x₁ πᵥ) Q≡Q' ϖ {wk≡ₗ = wk≡ₗ} =
               {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}
  -}
  -}
