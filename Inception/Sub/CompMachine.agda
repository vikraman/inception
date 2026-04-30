{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.CompMachine (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_; _$_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)
open Eq.≡-Reasoning using (step-≡-⟩; step-≡-∣; step-≡-⟨; _∎; step-≡)

open import Relation.Binary.PropositionalEquality.Properties using (dcong₂)

open import Relation.Binary.Reasoning.Syntax

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Unit
open import Data.Nat
open import Data.List using (List; _∷_; []; _++_)

open import Inception.Sub.ValueMachine R

module CMain {R₀ : Ty} (k₀ : ⟦ R₀ ⟧ → R) where

  open VMain {R₀ = R₀} k₀

  data CompState : Set where

        ∘⟨_⊰_╎_⟩ : (W : Γ ⊢ᶜ X) → (γ : Env Γ) → (cs : CompStack Δ X) → {π : Wk Γ Δ} → {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → CompState

        ∙⟨_⊰_╎_⟩ : (W : C̲o̲m̲p Γ X) → (γ : Env Γ) → (cs : CompStack Δ X) → {π : Wk Γ Δ} → {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → CompState

  data CompHaltingState : CompState → Set where

      ret : {M : V̲a̲l̲ Γ R₀} → {γ : Env Γ} → CompHaltingState ((∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ ╎ ◻ ⟩) {π = wk-wk-ε} {wk≡ = refl} )


  infixr 15 _→ᶜ⟨_⟩_
  infixr 15 _→ᶜ*_
  infixr 10 _⨾ᶜ_

  ⟦_⟧ᶜꟴ : CompState → R
  ⟦ ∘⟨ W ⊰ γ ╎ cs ⟩ ⟧ᶜꟴ = ⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ
  ⟦ ∙⟨ W ⊰ γ ╎ cs ⟩ ⟧ᶜꟴ = ⟦ toComp W ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ

  -- Computation Machine
  --------------------------------------------------

  infix  15 _→ᶜ_
  data _→ᶜ*_ : CompState → CompState → Set
  data _→ᶜ_ : CompState → CompState → Set

  data _→ᶜ_  where

        ∘return  :    {M : Γ ⊢ᵛ X} → {γ : Env Γ'} → {π : Wk Γ' Γ} → {M' : V̲a̲l̲ Γ'' X} → {γ' : Env Γ''}
                      → {cs : CompStack Δ X} → {πₓ : Wk Γ' Δ} → {πₓ' : Wk Γ'' Δ}
                      → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → {wk≡ₓ' : ⟦ πₓ' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                      → ((∘ ((⇡ wk-val π M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ M' ⊲ γ' ∷ □) {↥ = 🗆})))
                     ----------------------------------------------------------------
                      →     ((∘⟨ wk-comp π (return M) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ} )
                         →ᶜ ((∙⟨ r̲e̲t̲u̲r̲n̲ M' ⊰ γ' ╎ cs ⟩) {π = πₓ'} {wk≡ = wk≡ₓ'})

        ∙return  :    {M : V̲a̲l̲ Γ X} → {γ : Env Γ} → {N : (Γ' ∙ X) ⊢ᶜ Y} → {γ' : Env Γ'} → {π : Wk Γ Γ'}
                      → {cs : CompStack Δ Y} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ' Δ}
                      → {wk≡ₓ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ} → {wk≡ₓ' : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → {wk≡ : ⟦ πₓ' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ }
                  ----------------------------------------------------------------
                    →       ((∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ ╎ ((N ⊲ γ' ⦂⦂ cs) {π = πₓ'} {wk≡ = wk≡}) ⟩) {π = π} {wk≡ = wk≡ₓ})
                         →ᶜ ((∘⟨ wk-comp (wk-cong π) N ⊰ γ ﹐ M ╎ cs ⟩) {π = wk-wk πₓ} {wk≡ = wk≡ₓ'})

        ∘push    :    {M : Γ ⊢ᶜ X} → {N : (Γ ∙ X) ⊢ᶜ Y} → {γ : Env Γ}
                    → {cs : CompStack Δ Y} → {πₓ : Wk Γ Δ}
                    → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → {wk≡ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                  ----------------------------------------------------------------
                    →       ((∘⟨ push M N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ})

                        →ᶜ ((∘⟨ M ⊰ γ ╎ ((N ⊲ γ ⦂⦂ cs) {π = πₓ}  {wk≡ = wk≡}) ⟩) {π = wk-id} {wk≡ = refl})

        ∘sub     :    {M : (Γ ∙ `V) ⊢ᶜ X} → {N : Γ ⊢ᶜ X} → {γ : Env Γ}
                    → {cs : CompStack Δ X} → {πₓ : Wk Γ Δ} → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                  ----------------------------------------------------------------
                    →       ((∘⟨ sub M N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ})
                         →ᶜ ((∘⟨ M ⊰ ((γ ﹐﹝ N ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡ₓ}) ╎ cs ⟩) {π = wk-wk πₓ} {wk≡ = wk≡ₓ})

        ∘pm      :    {M : Γ' ⊢ᵛ X `× Y} → {γ : Env Γ} → {W : (Γ' ∙ X ∙ Y) ⊢ᶜ Z}
                    → {cs : CompStack Δ Z} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ'' Δ} → {γ'' : Env Γ''}
                    → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → {wk≡ₓ' : ⟦ πₓ' ⟧ʷ ⟦ γ'' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                    → {LHS : V̲a̲l̲ Γ'' X} → {RHS : V̲a̲l̲ Γ'' Y} → (π : Wk Γ Γ')
                    → ((∘ ((⇡ wk-val π M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ'' ∷ □) {↥ = 🗆}))) → (π' : Wk Γ'' Γ)
                  ----------------------------------------------------------------
                    →       ((∘⟨ pm (wk-val π M) (wk-comp (wk-cong (wk-cong π)) W) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ})
                         →ᶜ ((∘⟨ wk-comp (wk-cong (wk-cong π')) (wk-comp (wk-cong (wk-cong π)) W) ⊰ γ'' ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ╎ cs ⟩)
                               {π = wk-wk (wk-wk πₓ')}  {wk≡ = wk≡ₓ'})

        ∙app-var   :     {i : Γ ∋ (Z' `⇒ Z)} → {N : V̲a̲l̲ Γ Z'} → {γ : Env Γ} → {cs : CompStack Δ Z} → {πₓ : Wk Γ Δ} → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → {W : (Γ' ∙ Z') ⊢ᶜ Z} → {γ' : Env Γ'}
                       → (⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ _﹐_ γ' (l̲a̲m̲ W) ⟩) → (πᵥ : Wk Γ Γ')
                     ----------------------------------------------------------------
                       →    ((∙⟨ a̲pp (var i) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ})
                         →ᶜ ((∘⟨ (wk-comp (wk-cong πᵥ) W) ⊰ γ ﹐ N ╎ cs ⟩) {π = wk-wk πₓ} {wk≡ = wk≡ₓ})

        ∙app-pm     :    {M : Γ ⊢ᵛ (X `× Y)} → {N₁ : (Γ ∙ X ∙ Y) ⊢ᵛ (Z' `⇒ Z)} → {N : V̲a̲l̲ Γ Z'} → {γ : Env Γ}
                       → {cs : CompStack Δ Z} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ' Δ}
                       → {LHS : V̲a̲l̲ Γ' X} → {RHS : V̲a̲l̲ Γ' Y} → {γ' : Env Γ'}
                       → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → {wk≡ₓ' : ⟦ πₓ' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → ((∘ ((⇡ M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ' ∷ □) {↥ = 🗆}))) → (π : Wk Γ' Γ)
                     ----------------------------------------------------------------
                       →    ((∙⟨ a̲pp (pm M N₁) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ})
                         →ᶜ ((∙⟨ a̲pp ((wk-val (wk-cong (wk-cong π)) N₁)) (wk-v̲a̲l̲ (wk-wk (wk-wk π)) N) ⊰ γ' ﹐ LHS ﹐ (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ╎ cs ⟩)
                               {π = wk-wk (wk-wk πₓ')} {wk≡ = wk≡ₓ'})

        ∙app-lam     :   {W : (Γ ∙ X) ⊢ᶜ Y} → {N : V̲a̲l̲ Γ X} → {γ : Env Γ}
                       → {cs : CompStack Δ Y} → {πₓ : Wk Γ Δ} → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                     ----------------------------------------------------------------
                       → ((∙⟨ a̲pp (lam W) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ}) →ᶜ ((∘⟨ W ⊰ γ ﹐ N ╎ cs ⟩) {π = wk-wk πₓ} {wk≡ = wk≡ₓ})

        ∘app         :   {M : Γ ⊢ᵛ X `⇒ Y} → {N : Γ ⊢ᵛ X} → {γ : Env Γ} → {cs : CompStack Δ Y} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ' Δ}
                       → {N' : V̲a̲l̲ Γ' X} → {γ' : Env Γ'} → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → {wk≡ₓ' : ⟦ πₓ' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → ((∘ ((⇡ N ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ N' ⊲ γ' ∷ □) {↥ = 🗆}))) → (π : Wk Γ' Γ)
                     ----------------------------------------------------------------
                       →    ((∘⟨ app M N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ})
                         →ᶜ ((∙⟨ a̲pp (wk-val π M) N' ⊰ γ' ╎ cs ⟩) {π = πₓ'} {wk≡ = wk≡ₓ'})

        ∘var         :   {M : Γ ⊢ᵛ `V} → {γ : Env Γ} → {i : Γ' ∋ `V} → {γ' : Env Γ'} → {W : Γ'' ⊢ᶜ X'} → {γ'' : Env Γ''}
                       → {cs : CompStack Δ X} → {cs' : CompStack Δ' X'} → {πₓ : Wk Γ Δ} → {πₓ'' : Wk Γ'' Δ'}
                       → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → {wk≡ₓ'' : ⟦ πₓ'' ⟧ʷ ⟦ γ'' ⟧ᴱ ≡ ⟦ topCsEnv cs' ⟧ᴱ}
                       → ((∘ ((⇡ M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ v̲a̲r̲ i ⊲ γ' ∷ □) {↥ = 🗆}))) → (π' : Wk Γ' Γ)
                       → (⟨ i ∥ γ' ⟩ →ᴸ* ⟨ h ∥ ((γ'' ﹐﹝ W ╎ cs' ﹞) {π = πₓ''} {wk≡ = wk≡ₓ''}) ⟩) → (πᵥ : Wk Γ' Γ'')
                  ----------------------------------------------------------------
                       →    ((∘⟨ var M ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ})
                         →ᶜ ((∘⟨ W ⊰ γ'' ╎ cs' ⟩) {π = πₓ''} {wk≡ = wk≡ₓ''})

  data _→ᶜ*_ where

    _◼ : (S : CompState) → S →ᶜ* S

    _→ᶜ⟨_⟩_ : (S : CompState) → {S' S'' : CompState} → S →ᶜ S' → S' →ᶜ* S'' → S →ᶜ* S''

  _⨾ᶜ_ : {F S T : CompState} → (F →ᶜ* S) → (S →ᶜ* T) → (F →ᶜ* T)
  _⨾ᶜ_ (S ◼) S>>T = S>>T
  _⨾ᶜ_ (F →ᶜ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᶜ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ᶜ S₂>>T)

  topCompCtx : CompState → Ctx
  topCompCtx (∘⟨_⊰_╎_⟩ {Γ = Γ} _ _ _) = Γ
  topCompCtx (∙⟨_⊰_╎_⟩ {Γ = Γ} _ _ _) = Γ

  topCompEnv : (Q : CompState) → Env (topCompCtx Q)
  topCompEnv (∘⟨_⊰_╎_⟩ _ γ _) = γ
  topCompEnv (∙⟨_⊰_╎_⟩ _ γ _) = γ

  lem0 : (cs : CompStack Δ X) → (MM : K ⟦ X ⟧) → ⟦ cs ⟧ᶜˢ (λ k → MM k) k₀ ≡ MM (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
  lem0 ◻ MM = refl
  lem0 {X = X} ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡}) MM =           ⟦ (W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡} ⟧ᶜˢ MM k₀
                                   ≡⟨ refl ⟩
                                     ⟦ cs ⟧ᶜˢ (λ k → (λ x → MM (λ z → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) x)) k) k₀
                                   ≡⟨ lem0 cs (λ x → MM (λ z → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) x)) ⟩
                                     (λ x → MM (λ z → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) x)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                                   ≡⟨ refl ⟩
                                     MM (λ z →       ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)            )
                                   ≡⟨ cong MM lem0'' ⟩
                                     MM (λ z →       ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) k) k₀                      )
                                   ≡⟨ refl ⟩
                                     MM (λ y → ⟦ (W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡} ⟧ᶜˢ (λ k → k y) k₀) ∎

                                   where
                                      lem0' : (z : ⟦ X ⟧) → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀) ≡ ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) k) k₀
                                      lem0' z = sym (lem0 cs (⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z)))

                                      lem0'' : (λ z → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) ≡ (λ z → ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) k) k₀)
                                      lem0'' = extensionality lem0'

  wk-v̲a̲l̲-id : (M : V̲a̲l̲ Γ X) → wk-v̲a̲l̲ wk-id M ≡ M
  wk-v̲a̲l̲-id (l̲a̲m̲ M) = cong l̲a̲m̲ (wk-comp-id M)
  wk-v̲a̲l̲-id (pa̲i̲r̲ LHS RHS) = cong₂ pa̲i̲r̲ (wk-v̲a̲l̲-id LHS) (wk-v̲a̲l̲-id RHS)
  wk-v̲a̲l̲-id u̲n̲i̲t̲ = refl
  wk-v̲a̲l̲-id (v̲a̲r̲ i) = cong v̲a̲r̲ (wk-mem-id)

  {-# REWRITE wk-v̲a̲l̲-id #-}

  wk-comm-explicit : (M : V̲a̲l̲ Γ X) → (π : Wk Δ Γ) → toVal (wk-v̲a̲l̲ π M) ≡ wk-val π (toVal M)
  wk-comm-explicit M π = sym wk-comm

  {-# REWRITE wk-comm-explicit #-}

  -------------------------------------------------------------------

  {- maybe not needed

  data BasicTy : Set where
    Unit` : BasicTy
    _×`_ : BasicTy -> BasicTy -> BasicTy
    V` : BasicTy

  data AnyTy : Set where
    [_]  : BasicTy → AnyTy
    _⇒`_ : AnyTy → AnyTy → AnyTy

  bty-to-ty : BasicTy → Ty
  bty-to-ty Unit` = `Unit
  bty-to-ty (bty₁ ×` bty₂) = (bty-to-ty bty₁) `× (bty-to-ty bty₂)
  bty-to-ty V` = `V

  aty-to-ty : AnyTy → Ty
  aty-to-ty [ bty ] =  bty-to-ty bty
  aty-to-ty (aty₁ ⇒` aty₂) = (aty-to-ty aty₁) `⇒ (aty-to-ty aty₂)

  -}

  -------------------------------------------------------------------

  data ValHalts : (M : V̲a̲l̲ Γ Z) (γ : Env Γ) → Set

  data CompHalts : (W : Γ ⊢ᶜ Z) (γ : Env Γ) (cs : CompStack Δ Z) (π : Wk Γ Δ) (wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → Set

  data CompHalts where

    comp-halts : {W : Γ ⊢ᶜ Z} {γ : Env Γ} {cs : CompStack Δ Z} {π : Wk Γ Δ} {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
            {M : V̲a̲l̲ Γ' Z} {γ' : Env Γ'} {π' : Wk Γ' Δ} {wk≡' : ⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
            → (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡})) →ᶜ* ((∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ' ╎ cs ⟩) {π = π'} {wk≡ = wk≡'})
            → ⟦ (((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {wk≡ = wk≡})) ⟧ᶜꟴ ≡ ⟦ ((∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ' ╎ cs ⟩) {π = π'} {wk≡ = wk≡'}) ⟧ᶜꟴ
            → CompHalts W γ cs π wk≡

  data ValHalts where

    unit-halts : {γ : Env Γ} → ValHalts u̲n̲i̲t̲ γ

    pair-halts : {γ : Env Γ} {M₁ : V̲a̲l̲ Γ X} {M₂ : V̲a̲l̲ Γ X} → ValHalts M₁ γ → ValHalts M₂ γ → ValHalts (pa̲i̲r̲ M₁ M₂) γ

    var-halts : {γ : Env Γ} {i : Γ ∋ `V} → ValHalts (v̲a̲r̲ i) γ

    lam-halts : {W : (Γ ∙ X) ⊢ᶜ Y} {γ : Env Γ} → (∀ (cs : CompStack Δ Y) (π : Wk Γ Δ) (wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) (N : Val Γ X) → CompHalts (app (lam W) N) γ cs π wk≡)
                → ValHalts (l̲a̲m̲ W) γ


  ------------------------------------------------------

  data EnvEq : (π : Wk Γ' Γ) → (γ' : Env Γ') → (γ : Env Γ) → Set where

    wk-env-ε    : EnvEq wk-ε ∗ ∗

    wk-env-val-cong : {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ} → (M : V̲a̲l̲ Γ X) → EnvEq π γ' γ → EnvEq (wk-cong π) (γ' ﹐ wk-v̲a̲l̲ π M) (γ ﹐ M)

    wk-env-comp-cong : {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ}
                       → (W : Γ ⊢ᶜ X) → (cs : CompStack Δ X) → {πᶜ : Wk Γ Δ} → {wk≡ : ⟦ πᶜ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → {wk≡' : ⟦ wk-trans π πᶜ ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} -- not sure about this one
                       → EnvEq π γ' γ
                       → EnvEq (wk-cong π) ((γ' ﹐﹝ wk-comp π W ╎ cs ﹞) {π = wk-trans π πᶜ}
                               {wk≡ = wk≡'}) -- not sure about this one
                               ((γ ﹐﹝ W ╎ cs ﹞) {π = πᶜ} {wk≡ = wk≡})

    {- TOO RESTRICTIVE: The context of W does not really matter!
    wk-env-val-wk : {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ} → (M : V̲a̲l̲ Γ X) → EnvEq π γ' γ → EnvEq (wk-wk π) (γ' ﹐ wk-v̲a̲l̲ π M) γ

    wk-env-comp-wk : {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ}
                       → (W : Γ ⊢ᶜ X) → (cs : CompStack Δ X) → {πᶜ' : Wk Γ' Δ} --→ {wk≡ : ⟦ πᶜ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → {wk≡' : ⟦ πᶜ' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} -- not sure about this one
                       → EnvEq π γ' γ
                       → EnvEq (wk-wk π) ((γ' ﹐﹝ wk-comp π W ╎ cs ﹞) {π = πᶜ'}
                               {wk≡ = wk≡'}) -- not sure about this one
                               γ
    -}

    wk-env-val-wk : {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ} → (M : V̲a̲l̲ Γ' X) → EnvEq π γ' γ → EnvEq (wk-wk π) (γ' ﹐ M) γ

    wk-env-comp-wk : {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ}
                       → (W : Γ' ⊢ᶜ X) → (cs : CompStack Δ X) → {πᶜ' : Wk Γ' Δ} --→ {wk≡ : ⟦ πᶜ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → {wk≡' : ⟦ πᶜ' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} -- not sure about this one
                       → EnvEq π γ' γ
                       → EnvEq (wk-wk π) ((γ' ﹐﹝ W ╎ cs ﹞) {π = πᶜ'}
                               {wk≡ = wk≡'}) -- not sure about this one
                               γ

  rewrite-comp-env : (γ : Env Γ) (W W' : Γ ⊢ᶜ X) → (cs : CompStack Δ X) → {π π' : Wk Γ Δ} → {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                     → (Wπ≡Wπ' : (W , π) ≡ (W' , π'))
                     → (γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡} ≡ (γ ﹐﹝ W' ╎ cs ﹞) {π = π'} {wk≡ = subst (λ x → ⟦ proj₂ x ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) Wπ≡Wπ' wk≡}
  rewrite-comp-env γ W W' cs Wπ≡Wπ' = dcong₂ (λ x y → (γ ﹐﹝ proj₁ x ╎ cs ﹞) {π = proj₂ x} {wk≡ = y} ) Wπ≡Wπ' refl

  wk-assoc : {π₁ : Wk Γ Γ'} {π₂ : Wk Γ' Γ''} {π₃ : Wk Γ'' Γ'''} → wk-trans π₁ (wk-trans π₂ π₃) ≡ wk-trans (wk-trans π₁ π₂) π₃
  wk-assoc {π₁ = wk-ε} {π₂ = π₂} {π₃ = π₃} = refl
  wk-assoc {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {π₃ = wk-cong π₃} = cong wk-cong (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
  wk-assoc {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {π₃ = wk-wk π₃} = cong wk-wk (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
  wk-assoc {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {π₃ = π₃} = cong wk-wk (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
  wk-assoc {π₁ = wk-wk π₁} {π₂ = π₂} {π₃ = π₃} = cong wk-wk (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})

  -- proj₁-eq : {A B : Set} {a₁ a₂ : A} {b₁ b₂ : B} → (a₁ , b₁) ≡ (a₂ , b₂) → a₁ ≡ a₂
  -- proj₁-eq refl = refl

  pair-eq : {A B : Set} {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)
  pair-eq a₁≡a₂ b₁≡b₂ = cong₂ (λ x y → x , y) a₁≡a₂ b₁≡b₂

  enveq-id : {γ : Env Γ} → EnvEq wk-id γ γ
  enveq-id {γ = ∗} = wk-env-ε
  enveq-id {γ = γ ﹐ M} = wk-env-val-cong M enveq-id
  enveq-id {γ = (_﹐﹝_╎_﹞) {Γ = Γ} {Δ = Δ} γ W cs {π = π} {wk≡ = wk≡}} =
           let
             W≡ = wk-comp-id W
             π≡ = wk-trans-id {π = π}

             eq1 : (γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡} ≡ (γ ﹐﹝ (wk-comp wk-id W) ╎ cs ﹞) {π = wk-trans wk-id π} {wk≡ = subst (λ x → ⟦ proj₂ x ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) (sym (pair-eq W≡ π≡)) wk≡}
             eq1 = rewrite-comp-env γ W (wk-comp wk-id W) cs {π = π} {π' = wk-trans wk-id π} {wk≡ = wk≡} (sym (pair-eq W≡ π≡))

             a0 = wk-env-comp-cong {π = wk-id} {γ' = γ} {γ = γ} W cs {πᶜ = π} {wk≡ = wk≡} {wk≡' = subst (λ x → ⟦ proj₂ x ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) (sym (pair-eq W≡ π≡)) wk≡} (enveq-id {γ = γ})

             goal : EnvEq (wk-cong {A = `V} wk-id) ((γ ﹐﹝ W ╎ cs ﹞) {π} {wk≡}) ((γ ﹐﹝ W ╎ cs ﹞) {π} {wk≡})
             goal =  subst (λ x → EnvEq (wk-cong {A = `V} wk-id) x ((γ ﹐﹝ W ╎ cs ﹞) {π} {wk≡}) ) (sym eq1) a0
           in
           goal

  data WkExt : Wk Γ Δ → Set where

    wk-eq : (π : Wk Γ Γ) → WkExt π

    wk-ext : (π : Wk Γ Δ) → WkExt π → WkExt (wk-wk {A = A} π)

  wk-ext-trans : {π₁ : Wk Γ Δ} {π₂ : Wk Δ Ψ} → WkExt π₁ → WkExt π₂ → WkExt (wk-trans π₁ π₂)
  wk-ext-trans (wk-eq π₁) (wk-eq π₂) = wk-eq (wk-trans π₁ π₂)
  wk-ext-trans (wk-eq π₁) (wk-ext {A = A} π₂ we₂) =
               let
                 a0 : WkExt (wk-wk {A = A} π₂)
                 a0 = wk-ext π₂ we₂
                 a1 : WkExt (wk-trans wk-id (wk-wk {A = A} π₂))
                 a1 = subst (λ x → WkExt x) (sym wk-trans-id) a0
                 a2 : WkExt (wk-trans π₁ (wk-wk {A = A} π₂))
                 a2 = subst (λ x → WkExt (wk-trans x (wk-wk {A = A} π₂))) (sym wk-id-id) a1
               in
               a2
  wk-ext-trans (wk-ext π₁ we₁) (wk-eq π₂) = wk-ext (wk-trans π₁ π₂) (wk-ext-trans we₁ (wk-eq π₂))
  wk-ext-trans (wk-ext π₁ we₁) (wk-ext π₂ we₂) = wk-ext (wk-trans π₁ (wk-wk π₂)) (wk-ext-trans we₁ (wk-ext π₂ we₂))

  wk-ext-cong-lift : {π : Wk Γ Δ} → WkExt (wk-cong {A = A} π) → WkExt π
  wk-ext-cong-lift (wk-eq π) = wk-eq _

  wk-ext-wk-lift : {π : Wk Γ Δ} → WkExt (wk-wk {A = A} π) → WkExt π
  wk-ext-wk-lift (wk-eq (wk-wk π)) = ql (wk-absurd π wk-id) (WkExt π)
  wk-ext-wk-lift (wk-ext π we) = we

  env-eq-trans : {π₁ : Wk Γ Γ'} {π₂ : Wk Γ' Γ''} {γ : Env Γ} {γ' : Env Γ'} {γ'' : Env Γ''}
                 → WkExt π₁ → WkExt π₂ → EnvEq π₁ γ γ' → EnvEq π₂ γ' γ'' → EnvEq (wk-trans π₁ π₂) γ γ''
  env-eq-trans {π₁ = wk-ε} {π₂ = π₂} {γ = γ} {γ' = γ'} {γ'' = γ''} (wk-eq π) we₂ wk-env-ε ϖ₂ = ϖ₂
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {γ = γ ﹐ _} {γ' = γ' ﹐ M} {γ'' = γ'' ﹐ M₁} we₁ we₂ (wk-env-val-cong M ϖ₁) (wk-env-val-cong M₁ ϖ₂) =
               let
                 a0 = env-eq-trans (wk-ext-cong-lift we₁) (wk-ext-cong-lift we₂) ϖ₁ ϖ₂
                 a1 : EnvEq (wk-cong (wk-trans π₁ π₂)) (γ ﹐ wk-v̲a̲l̲ (wk-trans π₁ π₂) M₁) (γ'' ﹐ M₁)
                 a1 = wk-env-val-cong M₁ a0
                 a2 : EnvEq (wk-cong (wk-trans π₁ π₂)) (γ ﹐ wk-v̲a̲l̲ π₁ (wk-v̲a̲l̲ π₂ M₁)) (γ'' ﹐ M₁)
                 a2 = subst (λ x → EnvEq (wk-cong (wk-trans π₁ π₂)) (γ ﹐ x) (γ'' ﹐ M₁)) (sym (wk-v̲a̲l̲-trans M₁ π₁ π₂)) a1
               in
               a2
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {γ = γ ﹐ _} {γ' = γ' ﹐ M} {γ'' = ∗} (wk-eq .(wk-cong π₁)) we₂ (wk-env-val-cong M ϖ₁) (wk-env-val-wk M₁ ϖ₂) =
               wk-env-val-wk (wk-v̲a̲l̲ π₁ M) (env-eq-trans (wk-eq π₁) (wk-ext-wk-lift we₂) ϖ₁ ϖ₂)
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {γ = γ ﹐ _} {γ' = γ' ﹐ M} {γ'' = γ'' ﹐ M₂} (wk-eq .(wk-cong π₁)) we₂ (wk-env-val-cong M ϖ₁) (wk-env-val-wk M₁ ϖ₂) =
               let
                 a0 = env-eq-trans (wk-eq π₁) (wk-ext-wk-lift we₂) ϖ₁ ϖ₂
                 a1 : EnvEq (wk-wk (wk-trans π₁ π₂)) (γ ﹐ M₁) (γ'' ﹐ M₂)
                 a1 = wk-env-val-wk M₁ a0
               in
               wk-env-val-wk (wk-v̲a̲l̲ π₁ M) a0
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {γ = γ ﹐ _} {γ' = γ' ﹐ M} {γ'' = γ'' ﹐﹝ W ╎ cs ﹞} (wk-eq .(wk-cong π₁)) we₂ (wk-env-val-cong M ϖ₁) (wk-env-val-wk M₁ ϖ₂) =
               let
                 a0 = env-eq-trans (wk-eq π₁) (wk-ext-wk-lift we₂) ϖ₁ ϖ₂
                 a1 : EnvEq (wk-wk (wk-trans π₁ π₂)) (γ ﹐ M₁) (γ'' ﹐﹝ W ╎ cs ﹞)
                 a1 = wk-env-val-wk M₁ a0
               in
               wk-env-val-wk (wk-v̲a̲l̲ π₁ M) a0
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {γ = (γ ﹐﹝ _ ╎ _ ﹞) {wk≡ = wk≡₁}} {γ' = (γ' ﹐﹝ _ ╎ _ ﹞) {wk≡ = wk≡₂}} {γ'' = (γ'' ﹐﹝ _ ╎ _ ﹞) {π = π₃} {wk≡ = wk≡₃}} (wk-eq π) we₂ (wk-env-comp-cong W cs ϖ₁) (wk-env-comp-cong W₁ cs₁ ϖ₂) =
               let
                 a0 = env-eq-trans (wk-eq π₁) (wk-ext-cong-lift we₂) ϖ₁ ϖ₂

                 a1 : EnvEq (wk-cong (wk-trans π₁ π₂)) ((γ ﹐﹝ wk-comp (wk-trans π₁ π₂) W₁ ╎ cs ﹞) {π = wk-trans (wk-trans π₁ π₂) π₃} {wk≡ = subst (λ x → ⟦ proj₂ x ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) (pair-eq (wk-comp-trans W₁ π₁ π₂) (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})) wk≡₁}) ((γ'' ﹐﹝ W₁ ╎ cs ﹞) {π = π₃} {wk≡ = wk≡₃})
                 a1 = wk-env-comp-cong W₁ cs {πᶜ = π₃} {wk≡ = wk≡₃} {wk≡' = subst (λ x → ⟦ proj₂ x ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) (pair-eq (wk-comp-trans W₁ π₁ π₂) (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})) wk≡₁} a0

                 π≡ : wk-trans π₁ (wk-trans π₂ π₃) ≡ wk-trans (wk-trans π₁ π₂) π₃
                 π≡ = wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃}
                 W≡ : wk-comp π₁ (wk-comp π₂ W₁) ≡ wk-comp (wk-trans π₁ π₂) W₁
                 W≡ = wk-comp-trans W₁ π₁ π₂
                 eq1 = rewrite-comp-env γ (wk-comp π₁ (wk-comp π₂ W₁)) (wk-comp (wk-trans π₁ π₂) W₁) cs {π = wk-trans π₁ (wk-trans π₂ π₃)} {π' = wk-trans (wk-trans π₁ π₂) π₃} {wk≡ = wk≡₁} (pair-eq W≡ π≡)
                 a2 : EnvEq (wk-cong (wk-trans π₁ π₂)) ((γ ﹐﹝ wk-comp π₁ (wk-comp π₂ W₁) ╎ cs ﹞) {π = wk-trans π₁ (wk-trans π₂ π₃)} {wk≡ = wk≡₁}) ((γ'' ﹐﹝ W₁ ╎ cs ﹞) {π = π₃} {wk≡ = wk≡₃})
                 a2 = subst (λ x → EnvEq (wk-cong (wk-trans π₁ π₂)) x ((γ'' ﹐﹝ W₁ ╎ cs ﹞) {π = π₃} {wk≡ = wk≡₃})) (sym eq1) a1
              in
               a2
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {γ = γ} {γ' = γ'} {γ'' = ∗} (wk-eq .(wk-cong π₁)) we₂ (wk-env-comp-cong W cs ϖ₁) (wk-env-comp-wk W₁ cs₁ ϖ₂) =
               wk-env-comp-wk (wk-comp π₁ W) cs (env-eq-trans (wk-eq π₁) (wk-ext-wk-lift we₂) ϖ₁ ϖ₂)
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {γ = (γ ﹐﹝ _ ╎ _ ﹞) {π = πₓ} {wk≡ = wk≡}} {γ' = γ'} {γ'' = γ'' ﹐ M} (wk-eq .(wk-cong π₁)) we₂ (wk-env-comp-cong W cs ϖ₁) (wk-env-comp-wk W₁ cs₁ ϖ₂) =
               let
                 a0 = env-eq-trans (wk-eq π₁) (wk-ext-wk-lift we₂) ϖ₁ ϖ₂
                 a1 = wk-env-comp-wk W₁ cs {πᶜ' = wk-trans π₁ _} {wk≡' = wk≡} a0
               in
               wk-env-comp-wk (wk-comp π₁ W) cs a0
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {γ = (γ ﹐﹝ _ ╎ _ ﹞) {π = πₓ} {wk≡ = wk≡}} {γ' = γ' ﹐﹝ _ ╎ _ ﹞} {γ'' = γ'' ﹐﹝ W₂ ╎ cs₂ ﹞} (wk-eq .(wk-cong π₁)) we₂ (wk-env-comp-cong W cs ϖ₁) (wk-env-comp-wk W₁ cs₁ ϖ₂) =
               let
                 a0 = env-eq-trans (wk-eq π₁) (wk-ext-wk-lift we₂) ϖ₁ ϖ₂
                 a1 = wk-env-comp-wk W₁ cs {πᶜ' = wk-trans π₁ _} {wk≡' = wk≡} a0
               in
               wk-env-comp-wk (wk-comp π₁ W) cs a0
  env-eq-trans {π₁ = wk-wk π₁} {π₂ = π₂} {γ = γ ﹐ _} {γ' = γ'} {γ'' = γ''} (wk-eq π) we₂ (wk-env-val-wk M ϖ₁) ϖ₂ = ql (wk-absurd π₁ wk-id) _
  env-eq-trans {π₁ = wk-wk π₁} {π₂ = π₂} {γ = γ} {γ' = γ'} {γ'' = γ''} (wk-eq π) we₂ (wk-env-comp-wk W cs ϖ₁) ϖ₂ = ql (wk-absurd π₁ wk-id) _
  env-eq-trans {π₁ = wk-wk π₁} {π₂ = π₂} {γ = γ} {γ' = γ'} {γ'' = γ''} (wk-ext π we₁) (wk-eq π₃) (wk-env-val-wk M ϖ₁) ϖ₂ = wk-env-val-wk M (env-eq-trans we₁ (wk-eq π₂) ϖ₁ ϖ₂)
  env-eq-trans {π₁ = wk-wk π₁} {π₂ = π₂} {γ = γ} {γ' = γ'} {γ'' = γ''} (wk-ext π we₁) (wk-ext π₃ we₂) (wk-env-val-wk M ϖ₁) ϖ₂ = wk-env-val-wk M (env-eq-trans we₁ (wk-ext π₃ we₂) ϖ₁ ϖ₂)
  env-eq-trans {π₁ = wk-wk π₁} {π₂ = π₂} {γ = γ} {γ' = γ'} {γ'' = γ''} (wk-ext π we₁) (wk-eq π₃) (wk-env-comp-wk W cs ϖ₁) ϖ₂ = wk-env-comp-wk W cs (env-eq-trans we₁ (wk-eq π₂) ϖ₁ ϖ₂)
  env-eq-trans {π₁ = wk-wk π₁} {π₂ = π₂} {γ = γ} {γ' = γ'} {γ'' = γ''} (wk-ext π we₁) (wk-ext π₃ we₂) (wk-env-comp-wk W cs ϖ₁) ϖ₂ = wk-env-comp-wk W cs (env-eq-trans we₁ (wk-ext π₃ we₂) ϖ₁ ϖ₂)



  lhwk : (γ' : Env Γ')
          → (M : V̲a̲l̲ Γ' X)
          → (H : LookupHaltingState ⟨ h ∥ γ' ﹐ M ⟩)
          → (Ψ' : Ctx)
          → (πᵣ : Wk Ψ' Γ')
          → (γᵣ : Env Ψ')
          → (LookupHaltingState ⟨ h ∥ γᵣ ﹐ wk-v̲a̲l̲ πᵣ M ⟩)
  lhwk γ' M found-unit Ψ' πᵣ γᵣ = found-unit
  lhwk γ' M found-pair Ψ' πᵣ γᵣ = found-pair
  lhwk γ' M found-lam Ψ' πᵣ γᵣ = found-lam

  lookup-wk-lift : {γ : Env Γ} {γ' : Env Γ'}
                 → (i : Γ ∋ X) → (M : V̲a̲l̲ Γ' X) → (ext : EnvExt i γ (γ' ﹐ M))
                 → ⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ γ' ﹐ M ⟩
                 → (H : LookupHaltingState ⟨ h ∥ γ' ﹐ M ⟩)
                 → (πₗ : Wk Ψ Γ)
                 → (γₗ : Env Ψ)
                 → (ϖₗ : EnvEq πₗ γₗ γ)
                 → Σ[ Ψ' ∈ Ctx ]
                   Σ[ πᵣ ∈ Wk Ψ' Γ' ]
                   Σ[ γᵣ ∈ Env Ψ' ]
                   ( ⟨ (wk-mem πₗ i) ∥ γₗ ⟩ →ᴸ* ⟨ h ∥ γᵣ ﹐ wk-v̲a̲l̲ πᵣ M ⟩
                     × (LookupHaltingState ⟨ h ∥ γᵣ ﹐ wk-v̲a̲l̲ πᵣ M ⟩) )

  -- lookup-wk-lift i M ext L→*L' H πₗ γₗ ϖₗ = {!!}

  lookup-wk-lift i M env-val (S ◼) H (wk-cong {Γ = Γₗ} πₗ) (γₗ ﹐ M₁) (wk-env-val-cong M₂ ϖₗ) =
                 Γₗ , πₗ , γₗ , (⟨ h ∥ γₗ ﹐ wk-v̲a̲l̲ πₗ M ⟩ ◼) , lhwk _ M H Γₗ πₗ γₗ
  lookup-wk-lift i M env-val (S ◼) H (wk-cong πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) ()
  lookup-wk-lift {γ' = γ'} i M env-val (S ◼) H (wk-wk πₗ) (γₗ ﹐ M₁) (wk-env-val-wk M₂ ϖₗ) =
                 let
                   t = lookup-wk-lift h M env-val (⟨ h ∥ γ' ﹐ M ⟩ ◼) H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , proj₁ (proj₂ (proj₂ t)) , (_ →ᴸ⟨ val-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ t)))) , proj₂ (proj₂ (proj₂ (proj₂ t)))
  lookup-wk-lift i M env-val (S ◼) H (wk-wk πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) (wk-env-comp-wk W₁ cs₁ ϖₗ) =
                 let
                   t = lookup-wk-lift h M env-val (_ ◼) H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , proj₁ (proj₂ (proj₂ t)) , (_ →ᴸ⟨ comp-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ t)))) , proj₂ (proj₂ (proj₂ (proj₂ t)))
  lookup-wk-lift i M env-val (S →ᴸ⟨ x ⟩ L→*L') H (wk-cong {Γ = Γₗ} πₗ) (γₗ ﹐ M₁) (wk-env-val-cong M₂ ϖₗ) =
                 Γₗ , πₗ , γₗ , (_ ◼) , lhwk _ M H Γₗ πₗ γₗ
  lookup-wk-lift i M env-val (S →ᴸ⟨ x ⟩ L→*L') H (wk-cong πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) ()
  lookup-wk-lift i M env-val (S →ᴸ⟨ x ⟩ L→*L') H (wk-wk πₗ) (γₗ ﹐ M₁) (wk-env-val-wk M₂ ϖₗ) =
                 let
                   t = lookup-wk-lift h M env-val (_ ◼) H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , proj₁ (proj₂ (proj₂ t)) , (_ →ᴸ⟨ val-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ t)))) , proj₂ (proj₂ (proj₂ (proj₂ t)))
  lookup-wk-lift i M env-val (S →ᴸ⟨ x ⟩ L→*L') H (wk-wk πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) (wk-env-comp-wk W₁ cs₁ ϖₗ) =
                 let
                   t = lookup-wk-lift h M env-val (_ ◼) H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , proj₁ (proj₂ (proj₂ t)) , ( _ →ᴸ⟨ comp-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ t)))) , proj₂ (proj₂ (proj₂ (proj₂ t)))
  lookup-wk-lift i M (ext-val ext) (⟨ t i₁ ∥ _ ⟩ →ᴸ⟨ val-t-step ⟩ L→*L') H (wk-cong πₗ) (γₗ ﹐ M₁) (wk-env-val-cong M₂ ϖₗ) = --{!S!}
                 let
                   t = lookup-wk-lift i₁ M ext L→*L' H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , proj₁ (proj₂ (proj₂ t)) , ( _ →ᴸ⟨ val-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ t)))) , proj₂ (proj₂ (proj₂ (proj₂ t)))
  lookup-wk-lift i M (ext-val ext) (S →ᴸ⟨ x ⟩ L→*L') H (wk-cong πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) ()
  lookup-wk-lift i M (ext-val ext) (⟨ t i₁ ∥ _ ⟩ →ᴸ⟨ val-t-step ⟩ L→*L') H (wk-wk πₗ) (γₗ ﹐ M₁) (wk-env-val-wk M₂ ϖₗ) =
                 let
                   t = lookup-wk-lift (t i₁) M (ext-val ext) (_ →ᴸ⟨ val-t-step ⟩ L→*L') H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , proj₁ (proj₂ (proj₂ t)) , (_ →ᴸ⟨ val-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ t)))) , proj₂ (proj₂ (proj₂ (proj₂ t)))
  lookup-wk-lift i M (ext-val ext) ((⟨ t i₁ ∥ _ ﹐ _ ⟩) →ᴸ⟨ val-t-step ⟩ L→*L') H (wk-wk πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) (wk-env-comp-wk W₁ cs₁ ϖₗ) =
                 let
                   t = lookup-wk-lift (t i₁) M (ext-val ext) (_ →ᴸ⟨ val-t-step ⟩ L→*L') H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , proj₁ (proj₂ (proj₂ t)) , (_ →ᴸ⟨ comp-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ t)))) , proj₂ (proj₂ (proj₂ (proj₂ t)))
  lookup-wk-lift i M (ext-comp ext) (S →ᴸ⟨ x ⟩ L→*L') H (wk-cong πₗ) (γₗ ﹐ M₁) ()
  lookup-wk-lift i M (ext-comp ext) ((⟨ t i₁ ∥ _ ﹐﹝ W₁ ╎ cs ﹞ ⟩) →ᴸ⟨ comp-t-step ⟩ L→*L') H (wk-cong πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) (wk-env-comp-cong W₁ cs₁ ϖₗ) =
                 let
                   t = lookup-wk-lift i₁ M ext L→*L' H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , proj₁ (proj₂ (proj₂ t)) , (_ →ᴸ⟨ comp-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ t)))) , proj₂ (proj₂ (proj₂ (proj₂ t)))
  lookup-wk-lift {X = X} i M (ext-comp ext) (⟨ t i₁ ∥ _ ⟩ →ᴸ⟨ comp-t-step ⟩ L→*L') H (wk-wk πₗ) (γₗ ﹐ M₁) (wk-env-val-wk M₂ ϖₗ) =
                 let
                   t = lookup-wk-lift (t i₁) M (ext-comp ext) (⟨ t i₁ ∥ _ ﹐﹝ _ ╎ _ ﹞ ⟩ →ᴸ⟨ comp-t-step ⟩ L→*L') H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , proj₁ (proj₂ (proj₂ t)) , (_ →ᴸ⟨ val-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ t)))) , proj₂ (proj₂ (proj₂ (proj₂ t)))
  lookup-wk-lift i M (ext-comp ext) ((⟨ t i₁ ∥ _ ﹐﹝ _ ╎ _ ﹞ ⟩) →ᴸ⟨ comp-t-step ⟩ L→*L') H (wk-wk πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) (wk-env-comp-wk W₁ cs₁ ϖₗ) =
                 let
                   t = lookup-wk-lift (t i₁) M (ext-comp ext) (⟨ t i₁ ∥ _ ⟩ →ᴸ⟨ comp-t-step ⟩ L→*L') H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , proj₁ (proj₂ (proj₂ t)) , (_ →ᴸ⟨ comp-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ t)))) , proj₂ (proj₂ (proj₂ (proj₂ t)))

  --------------------------------------------------

{-
  lookup-skip : {Γₗ : Ctx} {γₗ : Env Γₗ} {γ : Env Γ}
                 → (πₗ : Wk Γₗ Γ)
                 → (weₗ : WkExt πₗ)
                 → (i : Γ ∋ X)
                 → ⟨ wk-mem πₗ i ∥ γₗ ⟩ →ᴸ* ⟨ i ∥ γ ⟩
  lookup-skip {γₗ = γₗ} {γ = γ} wk-ε (wk-eq π) ()
  lookup-skip {γₗ = γₗ} {γ = γ} (wk-cong πₗ) (wk-eq π) Cx.h = {!!}
  lookup-skip {γₗ = γₗ} {γ = γ} (wk-cong πₗ) (wk-eq π) (Cx.t i) = {!!}
  lookup-skip {γₗ = γₗ} {γ = γ} (wk-wk πₗ) (wk-eq π) Cx.h = {!!}
  lookup-skip {γₗ = γₗ} {γ = γ} (wk-wk πₗ) (wk-eq π) (Cx.t i) = {!!}
  lookup-skip {γₗ = γₗ} {γ = γ} (wk-wk πₗ) (wk-ext π weₗ) Cx.h = {!!}
  lookup-skip {γₗ = γₗ} {γ = γ} (wk-wk πₗ) (wk-ext π weₗ) (Cx.t i) = {!!}
-}

  --------------------------------------------------

  uniq-bot : (↥ : BottomTypeEqualsNextType non-empty X T◾) → (↥ ≡ 🗇)
  uniq-bot 🗇 = refl


{- BEGIN W/O ENV EQ
  val-wk-lift-∘∘ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → ⟦ ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ wk≡ᵣ ∈ ⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) →ᵛ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              × ⟦ ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ )
  val-wk-lift-∘∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘pair {LHS = LHS} {RHS = RHS}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , ⇡ᴸ (wk-val πₗ LHS) (wk-val πₗ RHS) ⊲ γₗ ∷ □ , ∘pair , refl
  val-wk-lift-∘∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘pair {LHS = LHS} {RHS = RHS}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , ⇡ᴸ (wk-val πₗ LHS) (wk-val πₗ RHS) ⊲ γₗ ∷ M₁ ⊲ γ₁ ∷ tail , ∘pair , refl
  val-wk-lift-∘∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘pm {M = Mₚ} {N = Nₚ}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , ⇡ᴹ (wk-val πₗ Mₚ) (wk-val (wk-cong (wk-cong πₗ)) Nₚ) ⊲ γₗ ∷ □ , ∘pm , refl
  val-wk-lift-∘∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘pm {M = Mₚ} {N = Nₚ}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , ⇡ᴹ (wk-val πₗ Mₚ) (wk-val (wk-cong (wk-cong πₗ)) Nₚ) ⊲ γₗ ∷ M₁ ⊲ γ₁ ∷ tail , ∘pm , refl

  val-wk-lift-∘∙ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → ⟦ ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ wk≡ᵣ ∈ ⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) →ᵛ ∙ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              × ⟦ ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ )
  val-wk-lift-∘∙ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} ∘var-c Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , □ , ∘var-c , refl
  val-wk-lift-∘∙ {Ψ = Ψ} {M = ⇡ var i} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ} {tail' = □} {↥' = ↥'} (∘var L→*L' πᵥ) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , □ , {!!} , {!!}
  val-wk-lift-∘∙ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} ∘lam Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , □ , ∘lam , refl
  val-wk-lift-∘∙ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} ∘unit Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , □ , ∘unit , Q≡Q'
  val-wk-lift-∘∙ {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} ∘var-c Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , M₁ ⊲ γ₁ ∷ tail , ∘var-c , Q≡Q'
  val-wk-lift-∘∙ {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘var x₁ πᵥ) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ} = {!!}
  val-wk-lift-∘∙ {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} ∘lam Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , M₁ ⊲ γ₁ ∷ tail , ∘lam , Q≡Q'
  val-wk-lift-∘∙ {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} ∘unit Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , M₁ ⊲ γ₁ ∷ tail , ∘unit , Q≡Q'

  val-wk-lift-∙∘ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∙ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → ⟦ ∙ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ wk≡ᵣ ∈ ⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∙ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) →ᵛ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              × ⟦ ∙ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ )
  val-wk-lift-∙∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} () Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ}
  val-wk-lift-∙∘ {Ψ = Ψ} {M = ⭭ M} {γ = γ} {tail = ⇡ᴸ LHS RHS ⊲ γ₁ ∷ □} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = ((⇡ᴿ M) _ ⊲ γ ∷ □) {↥ = 🗆}} {↥' = 🗇} (∙M∷l {X = X} {Y = Y} {M = M} {LHS = LHS} {RHS = RHS} {π' = π'}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ} =
                 let
                   eq : (⇡ wk-val (wk-trans πₗ π') RHS) ≡ wk-pt πₗ (⇡ wk-val π' RHS)
                   eq = cong (⇡_) (sym (wk-val-trans RHS πₗ π'))
                   M→M'' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ (((⇡ wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇})
                   M→M'' = ∙M∷l
                   M→M''' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇})
                   M→M''' = subst (λ x → ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇})) eq M→M''
                 in
                 Ψ , πₗ , γₗ , wk≡ₗ , (⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆} , M→M''' ,
                 ( ⟦ ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ
                 ≡⟨ refl ⟩
                   ⟦ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                   ⟦ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆}) ⟧ᵛˢ
                 ≡⟨ Q≡Q' ⟩
                   (⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ))
                 ≡⟨ cong (λ x → (⟦ toVal M ⟧ᵛ x , ⟦ RHS ⟧ᵛ (⟦ π' ⟧ʷ x))) (sym wk≡ₗ)  ⟩
                   (⟦ toVal M ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)))
                 ≡⟨ cong (λ x → (⟦ toVal M ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) , ⟦ RHS ⟧ᵛ x)) (wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ)  ⟩
                   ⟦ toVal M ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ)
                 ≡⟨ refl ⟩
                   ⟦ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                   ⟦ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                  ⟦ ∘ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ ∎ )

  val-wk-lift-∙∘ {Ψ = Ψ} {M = ⭭ M} {γ = γ} {tail = ⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∙M∷l {M = M} {LHS = LHS} {RHS = RHS} {π' = π'} {↥ = ↥₀}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ} =
                 let
                   eq : (⇡ wk-val (wk-trans πₗ π') RHS) ≡ wk-pt πₗ (⇡ wk-val π' RHS)
                   eq = cong (⇡_) (sym (wk-val-trans RHS πₗ π'))
                   M→M''' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) →ᵛ ∘ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇})
                   M→M''' = subst₂ (λ x y → ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = y})) {↥ = 🗇})) eq (uniq-bot ↥₀) ∙M∷l
                 in
                 Ψ , πₗ , γₗ , wk≡ₗ , (⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇} , M→M''' , --{!!}

                 ( ⟦ ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) ⟧ᵛꟴ
                 ≡⟨ refl ⟩
                   ⟦ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                   ⟦ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀}) ⟧ᵛˢ
                 ≡⟨ Q≡Q' ⟩
                   ⟦ ∘ ((⇡ wk-val π' RHS ⊲ γ ∷ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) ⟧ᵛꟴ
                 ≡⟨ refl ⟩
                   ⟦ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀}) ⟧ᵛˢ
                 ≡⟨ cong (λ x → ⟦ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = x}) ⟧ᵛˢ) (uniq-bot ↥₀) ⟩
                   ⟦ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                   ⟦ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                  ⟦ ∘ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇}) ⟧ᵛꟴ ∎ )

  val-wk-lift-∙∘ {Ψ = Ψ} {M = ⭭ pa̲i̲r̲ LHS RHS} {γ = γ} {tail = ⇡ᴹ M N ⊲ γ₁ ∷ □} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = 🗆} (∙pair∷pm {X = X} {Y = Y} {Γ' = Γ₁} {π' = π'} {↥ = ↥₀}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ} =
                 let
                   eq0 : (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N) ≡ (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N))
                   eq0 =   (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N)
                          ≡⟨ refl ⟩
                           (⇡ wk-val (wk-trans (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π'))) N)
                          ≡⟨ cong (⇡_) (sym (wk-val-trans N (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π')))) ⟩
                           (⇡ wk-val (wk-cong (wk-cong πₗ)) (wk-val (wk-cong (wk-cong π')) N))
                          ≡⟨ refl ⟩
                           (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N)) ∎
                   eq1 : (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS)) ≡ (wk-v̲a̲l̲ (wk-wk πₗ) RHS)
                   eq1 =   (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS))
                          ≡⟨ wk-v̲a̲l̲-trans RHS (wk-wk wk-id) πₗ ⟩
                           (wk-v̲a̲l̲ (wk-trans (wk-wk wk-id) πₗ) RHS)
                          ≡⟨ refl ⟩
                           (wk-v̲a̲l̲ (wk-wk (wk-trans wk-id πₗ)) RHS)
                          ≡⟨ cong (λ x → wk-v̲a̲l̲ (wk-wk x) RHS) wk-trans-id ⟩
                           (wk-v̲a̲l̲ (wk-wk πₗ) RHS) ∎

                   t : ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS) ∷ □
                   t = ∙pair∷pm {π' = wk-trans πₗ π'}

                   t' : ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ □)
                   t' = subst₂ (λ x y → ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ y ∷ □) {↥ = 🗆})) eq0 eq1 t

                 in
                 Ψ ∙ X ∙ Y , wk-cong (wk-cong πₗ) , (γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS) ,
                 ( ⟦ wk-cong (wk-cong πₗ) ⟧ʷ ⟦ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ⟧ᴱ
                  ≡⟨ refl ⟩
                   (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)) , ⟦ toVal RHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                  ≡⟨ cong (λ x → (x , ⟦ toVal LHS ⟧ᵛ x) , ⟦ toVal RHS ⟧ᵛ x) wk≡ₗ ⟩
                   (⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ
                  ≡⟨ refl ⟩
                    ⟦ γ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ⟧ᴱ ∎ ) ,
                 □ , t' ,
                 ( ⟦ ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ LHS RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ
                 ≡⟨ refl ⟩
                    ⟦ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                    ⟦ (⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆} ⟧ᵛˢ
                 ≡⟨ Q≡Q' ⟩
                   ⟦ ((⇡ wk-val (wk-cong (wk-cong π')) N ⊲ γ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ∷ □) {↥ = 🗆}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                   ⟦ N ⟧ᵛ ((⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ)
                 ≡⟨ cong (λ x → ⟦ N ⟧ᵛ ((⟦ π' ⟧ʷ x , ⟦ toVal LHS ⟧ᵛ x) , ⟦ toVal RHS ⟧ᵛ x)) (sym wk≡ₗ) ⟩
                   ⟦ N ⟧ᵛ ((⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)) , ⟦ toVal RHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ))
                 ≡⟨ refl ⟩
                   ⟦ (⇡ wk-val (wk-cong (wk-cong πₗ)) (wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ □) {↥ = 🗆} ⟧ᵛˢ
                 ≡⟨ refl ⟩
                   ⟦ ∘ ((wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ∎ )


  val-wk-lift-∙∘ {b = non-empty} {b' = non-empty} {Ψ = Ψ} {M = ⭭ pa̲i̲r̲ LHS RHS} {γ = γ} {tail = (⇡ᴹ M N ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇}} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = 🗇} (∙pair∷pm {X = X} {Y = Y} {Γ' = Γ₁} {b = non-empty} {π' = π'} {↥ = ↥₀}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ} =
                 let
                   eq0 : (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N) ≡ (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N))
                   eq0 =   (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N)
                          ≡⟨ refl ⟩
                           (⇡ wk-val (wk-trans (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π'))) N)
                          ≡⟨ cong (⇡_) (sym (wk-val-trans N (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π')))) ⟩
                           (⇡ wk-val (wk-cong (wk-cong πₗ)) (wk-val (wk-cong (wk-cong π')) N))
                          ≡⟨ refl ⟩
                           (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N)) ∎
                   eq1 : (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS)) ≡ (wk-v̲a̲l̲ (wk-wk πₗ) RHS)
                   eq1 =   (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS))
                          ≡⟨ wk-v̲a̲l̲-trans RHS (wk-wk wk-id) πₗ ⟩
                           (wk-v̲a̲l̲ (wk-trans (wk-wk wk-id) πₗ) RHS)
                          ≡⟨ refl ⟩
                           (wk-v̲a̲l̲ (wk-wk (wk-trans wk-id πₗ)) RHS)
                          ≡⟨ cong (λ x → wk-v̲a̲l̲ (wk-wk x) RHS) wk-trans-id ⟩
                           (wk-v̲a̲l̲ (wk-wk πₗ) RHS) ∎

                   t : ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ LHS RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∘ ((⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS) ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})
                   t = ∙pair∷pm {π' = wk-trans πₗ π'}

                   t' : ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ LHS RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∘ ((wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})
                   t' = subst₂ (λ x y → ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ (M₂ ⊲ γ₂ ∷ tail) {↥ = ↥}) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ y ∷ (M₂ ⊲ γ₂ ∷ tail) {↥ = ↥}) {↥ = 🗇})) eq0 eq1 t
                 in
                 Ψ ∙ X ∙ Y , wk-cong (wk-cong πₗ) , (γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS) ,
                 ( ⟦ wk-cong (wk-cong πₗ) ⟧ʷ ⟦ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ⟧ᴱ
                  ≡⟨ refl ⟩
                   (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)) , ⟦ toVal RHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                  ≡⟨ cong (λ x → (x , ⟦ toVal LHS ⟧ᵛ x) , ⟦ toVal RHS ⟧ᵛ x) wk≡ₗ ⟩
                  (⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ
                  ≡⟨ refl ⟩
                  ⟦ γ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ⟧ᴱ ∎ ) ,
                  ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥}) ,
                  t' ,
                  ( ⟦ ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ LHS RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇}) ⟧ᵛꟴ
                  ≡⟨ Q≡Q' ⟩
                   ⟦ ((⇡ wk-val (wk-cong (wk-cong π')) N ⊲ γ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇}) ⟧ᵛˢ
                  ≡⟨ refl ⟩
                   ⟦ ∘ ((wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇}) ⟧ᵛꟴ ∎)


  val-wk-lift-∙∙ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∙ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → ⟦ ∙ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ wk≡ᵣ ∈ ⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∙ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) →ᵛ ∙ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              × ⟦ ∙ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ )
  val-wk-lift-∙∙ {Ψ = Ψ} {M = ⭭ M} {γ = γ} {tail = ⇡ᴿ LHS RHS ⊲ γ'' ∷ □} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = □} {↥' = 🗆} (∙M∷r {M = M} {LHS = LHS} {RHS = RHS} {π' = π'}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ} =
                 let
                   eq0 : (wk-v̲a̲l̲ (wk-trans πₗ π') LHS) ≡ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS))
                   eq0 = sym (wk-v̲a̲l̲-trans LHS πₗ π')

                   t : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∙ ⭭ pa̲i̲r̲ (wk-v̲a̲l̲ (wk-trans πₗ π') LHS) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ □
                   t = ∙M∷r {π' = wk-trans πₗ π'}

                   t' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS)) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ □) {↥ = 🗆})
                   t' = subst (λ x → ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∙ ⭭ pa̲i̲r̲ x (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ □) eq0 t
                 in
                 Ψ , πₗ , γₗ , wk≡ₗ , □ , t' ,
                 ( ⟦ ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ
                  ≡⟨ refl ⟩
                   ⟦ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ □) {↥ = 🗆}) ⟧ᵛˢ
                  ≡⟨ Q≡Q' ⟩
                    ⟦ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M ⊲ γ ∷ □) {↥ = 🗆}) ⟧ᵛˢ
                  ≡⟨ refl ⟩
                    ⟦ toVal LHS ⟧ᵛ (⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ
                  ≡⟨ cong (λ x → ⟦ toVal LHS ⟧ᵛ (⟦ π' ⟧ʷ x) , ⟦ toVal M ⟧ᵛ x) (sym wk≡ₗ) ⟩
                    ⟦ toVal LHS ⟧ᵛ (⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)) , ⟦ toVal M ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                  ≡⟨ refl ⟩
                   ⟦ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS)) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛˢ
                  ≡⟨ refl ⟩
                   ⟦ ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ∎ )

  val-wk-lift-∙∙ {Ψ = Ψ} {M = ⭭ M} {γ = γ} {tail = ⇡ᴿ LHS RHS ⊲ γ'' ∷ ((M₁ ⊲ γ₁ ∷ tail'') {↥ = ↥''})} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = (M₁ ⊲ γ₁ ∷ tail'') {↥ = ↥''}} {↥' = 🗇} (∙M∷r {M = M} {LHS = LHS} {RHS = RHS} {π' = π'}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} {wk≡ₗ = wk≡ₗ} =
                 let
                   eq0 : (wk-v̲a̲l̲ (wk-trans πₗ π') LHS) ≡ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS))
                   eq0 = sym (wk-v̲a̲l̲-trans LHS πₗ π')

                   t : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ ((M₁ ⊲ γ₁ ∷ tail'') {↥ = ↥''})) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∙ ⭭ pa̲i̲r̲ (wk-v̲a̲l̲ (wk-trans πₗ π') LHS) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ (M₁ ⊲ γ₁ ∷ tail'')
                   t = ∙M∷r {π' = wk-trans πₗ π'}

                   t' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ (M₁ ⊲ γ₁ ∷ tail'')) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS)) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ ((M₁ ⊲ γ₁ ∷ tail'') {↥ = ↥''})) {↥ = 🗇})
                   t' = subst (λ x → ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ ((M₁ ⊲ γ₁ ∷ tail'') {↥ = ↥''})) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∙ ⭭ pa̲i̲r̲ x (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ (M₁ ⊲ γ₁ ∷ tail'')) eq0 t
                 in
                 Ψ , πₗ , γₗ , wk≡ₗ , (M₁ ⊲ γ₁ ∷ tail'') , t' ,
                 ( ⟦ ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ (M₁ ⊲ γ₁ ∷ tail'')) {↥ = 🗇})) {↥ = 🗇}) ⟧ᵛꟴ
                  ≡⟨ refl ⟩
                   ⟦ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ (M₁ ⊲ γ₁ ∷ tail'')) {↥ = 🗇}) ⟧ᵛˢ
                  ≡⟨ Q≡Q' ⟩
                   ⟦ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M ⊲ γ ∷ (M₁ ⊲ γ₁ ∷ tail'')) {↥ = 🗇}) ⟧ᵛˢ
                  ≡⟨ refl ⟩
                   ⟦ M₁ ⊲ γ₁ ∷ tail'' ⟧ᵛˢ
                  ≡⟨ refl ⟩
                   ⟦ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS)) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ (M₁ ⊲ γ₁ ∷ tail'')) {↥ = 🗇}) ⟧ᵛˢ
                  ≡⟨ refl ⟩
                   ⟦ ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M) ⊲ γₗ ∷ (M₁ ⊲ γ₁ ∷ tail'')) {↥ = 🗇}) ⟧ᵛꟴ ∎ )
END W/O ENV EQ -}

-- WITH ENV EQ
  val-wk-lift-∘∘ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → ⟦ ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ wk≡ᵣ ∈ ⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) →ᵛ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              × ⟦ ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ )
  val-wk-lift-∘∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘pair {LHS = LHS} {RHS = RHS}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , ⇡ᴸ (wk-val πₗ LHS) (wk-val πₗ RHS) ⊲ γₗ ∷ □ , ∘pair , refl
  val-wk-lift-∘∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘pair {LHS = LHS} {RHS = RHS}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , ⇡ᴸ (wk-val πₗ LHS) (wk-val πₗ RHS) ⊲ γₗ ∷ M₁ ⊲ γ₁ ∷ tail , ∘pair , refl
  val-wk-lift-∘∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘pm {M = Mₚ} {N = Nₚ}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , ⇡ᴹ (wk-val πₗ Mₚ) (wk-val (wk-cong (wk-cong πₗ)) Nₚ) ⊲ γₗ ∷ □ , ∘pm , refl
  val-wk-lift-∘∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘pm {M = Mₚ} {N = Nₚ}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , ⇡ᴹ (wk-val πₗ Mₚ) (wk-val (wk-cong (wk-cong πₗ)) Nₚ) ⊲ γₗ ∷ M₁ ⊲ γ₁ ∷ tail , ∘pm , refl

  val-wk-lift-∘∙ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → ⟦ ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ wk≡ᵣ ∈ ⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) →ᵛ ∙ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              × ⟦ ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ )
  val-wk-lift-∘∙ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} ∘var-c Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , □ , ∘var-c , refl
  val-wk-lift-∘∙ {Γ = Γ} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘var {Γ = Γ₁} {Γ' = Γ₂} {γ = γ₁} {γ' = γ₂} {i = i} {M = M₁} L→L' πᵥ ext H) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                    a0 : EnvEq wk-id γ γ
                    a0 = enveq-id
                    a1 : EnvEq πₜ γ γ
                    a1 = subst (λ x → EnvEq x γ γ) (sym wk-id-id) a0

                    --b0 = lookup-wk-lift i M₁ ext L→L' H πₜ γ a1

                    b0 : Σ Ctx
                          (λ Ψ' →
                             Σ-syntax (Wk Ψ' Γ₂)
                             (λ πᵣ →
                                Σ-syntax (Env Ψ')
                                (λ γᵣ →
                                   (⟨ wk-mem πₗ i ∥ γₗ ⟩ →ᴸ* ⟨ h ∥ γᵣ ﹐ wk-v̲a̲l̲ πᵣ M₁ ⟩) ×
                                   LookupHaltingState ⟨ h ∥ γᵣ ﹐ wk-v̲a̲l̲ πᵣ M₁ ⟩)))
                    b0 = lookup-wk-lift i M₁ ext L→L' H πₗ γₗ ϖ

                    --b1 : ⟨ wk-mem πₗ i ∥ γₗ ⟩ →ᴸ* ⟨ h ∥ γ ﹐ (wk-v̲a̲l̲ πᵥ M₁) ⟩
                    --b1 = proj₂ (proj₂ (proj₂ (lookup-wk-lift i M₁ ext L→L' H πₗ γₗ ϖ)))

                    --goal : ∘ wk-pt πₗ (PartialTerm.⇡ var i) ⊲ γₗ ∷ □ →ᵛ ∙ wk-pt πₗ (⭭ wk-v̲a̲l̲ πᵥ M₁) ⊲ γₗ ∷ □
                    --goal : ∘ (PartialTerm.⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ □ →ᵛ ∙ wk-pt πₗ (⭭ wk-v̲a̲l̲ πᵥ M₁) ⊲ γₗ ∷ □

                    --c0 : ∘ (PartialTerm.⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ □ →ᵛ ∙ (⭭ wk-v̲a̲l̲ (wk-trans πₗ πᵥ) M₁) ⊲ γₗ ∷ □
                    --c0 = ∘var {i = wk-mem πₗ i} {M = M₁} {!proj₂ (proj₂ (proj₂ b0))!} (wk-trans πₗ πᵥ) {!!} H

                    --d0 : ∘ (PartialTerm.⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ □ →ᵛ ∙ (⭭ wk-v̲a̲l̲ (wk-trans πₗ πᵥ) M₁) ⊲ γₗ ∷ □


                    c0 : ∘ (PartialTerm.⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ □ →ᵛ ∙ (⭭ wk-v̲a̲l̲ (wk-trans πₗ πᵥ) M₁) ⊲ γₗ ∷ □
                    c0 = ∘var {γ' = γ₂} {i = wk-mem πₗ i} {M = M₁} {!!} (wk-trans πₗ πᵥ) {!!} H

                    d0 : ∘ (PartialTerm.⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ □ →ᵛ ∙ (⭭ wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ πᵥ M₁)) ⊲ γₗ ∷ □
                    d0 = ∘var {γ' = γ} {i = wk-mem πₗ i} {M = (wk-v̲a̲l̲ πᵥ M₁)} {!!} πₗ {!!} {!!}

                    goal : ∘ (PartialTerm.⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ □ →ᵛ ∙ (⭭ wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ πᵥ M₁)) ⊲ γₗ ∷ □
                    goal = d0
                 in
                 Ψ , πₗ , γₗ , wk≡ₗ , □ , goal , {!!}
  val-wk-lift-∘∙ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} ∘lam Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , □ , ∘lam , refl
  val-wk-lift-∘∙ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} ∘unit Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , □ , ∘unit , Q≡Q'
  val-wk-lift-∘∙ {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} ∘var-c Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , M₁ ⊲ γ₁ ∷ tail , ∘var-c , Q≡Q'
  val-wk-lift-∘∙ {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘var x₁ πᵥ ext H) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = {!!}
  val-wk-lift-∘∙ {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} ∘lam Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , M₁ ⊲ γ₁ ∷ tail , ∘lam , Q≡Q'
  val-wk-lift-∘∙ {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} ∘unit Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , M₁ ⊲ γ₁ ∷ tail , ∘unit , Q≡Q'

  val-wk-lift-∙∘ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∙ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → ⟦ ∙ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ wk≡ᵣ ∈ ⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∙ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) →ᵛ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              × ⟦ ∙ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ )
  val-wk-lift-∙∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} () Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ}
  val-wk-lift-∙∘ {Ψ = Ψ} {M = ⭭ M} {γ = γ} {tail = ⇡ᴸ LHS RHS ⊲ γ₁ ∷ □} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = ((⇡ᴿ M) _ ⊲ γ ∷ □) {↥ = 🗆}} {↥' = 🗇} (∙M∷l {X = X} {Y = Y} {M = M} {LHS = LHS} {RHS = RHS} {π' = π'}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                   eq : (⇡ wk-val (wk-trans πₗ π') RHS) ≡ wk-pt πₗ (⇡ wk-val π' RHS)
                   eq = cong (⇡_) (sym (wk-val-trans RHS πₗ π'))
                   M→M'' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ (((⇡ wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇})
                   M→M'' = ∙M∷l
                   M→M''' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇})
                   M→M''' = subst (λ x → ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇})) eq M→M''
                 in
                 Ψ , πₗ , γₗ , wk≡ₗ , (⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆} , M→M''' ,
                 ( ⟦ ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ
                 ≡⟨ refl ⟩
                   ⟦ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                   ⟦ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆}) ⟧ᵛˢ
                 ≡⟨ Q≡Q' ⟩
                   (⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ))
                 ≡⟨ cong (λ x → (⟦ toVal M ⟧ᵛ x , ⟦ RHS ⟧ᵛ (⟦ π' ⟧ʷ x))) (sym wk≡ₗ)  ⟩
                   (⟦ toVal M ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)))
                 ≡⟨ cong (λ x → (⟦ toVal M ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) , ⟦ RHS ⟧ᵛ x)) (wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ)  ⟩
                   ⟦ toVal M ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ)
                 ≡⟨ refl ⟩
                   ⟦ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                   ⟦ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                  ⟦ ∘ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ ∎ )

  val-wk-lift-∙∘ {Ψ = Ψ} {M = ⭭ M} {γ = γ} {tail = ⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∙M∷l {M = M} {LHS = LHS} {RHS = RHS} {π' = π'} {↥ = ↥₀}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                   eq : (⇡ wk-val (wk-trans πₗ π') RHS) ≡ wk-pt πₗ (⇡ wk-val π' RHS)
                   eq = cong (⇡_) (sym (wk-val-trans RHS πₗ π'))
                   M→M''' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) →ᵛ ∘ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇})
                   M→M''' = subst₂ (λ x y → ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = y})) {↥ = 🗇})) eq (uniq-bot ↥₀) ∙M∷l
                 in
                 Ψ , πₗ , γₗ , wk≡ₗ , (⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇} , M→M''' , --{!!}

                 ( ⟦ ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) ⟧ᵛꟴ
                 ≡⟨ refl ⟩
                   ⟦ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                   ⟦ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀}) ⟧ᵛˢ
                 ≡⟨ Q≡Q' ⟩
                   ⟦ ∘ ((⇡ wk-val π' RHS ⊲ γ ∷ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) ⟧ᵛꟴ
                 ≡⟨ refl ⟩
                   ⟦ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀}) ⟧ᵛˢ
                 ≡⟨ cong (λ x → ⟦ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = x}) ⟧ᵛˢ) (uniq-bot ↥₀) ⟩
                   ⟦ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                   ⟦ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                  ⟦ ∘ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇}) ⟧ᵛꟴ ∎ )

  val-wk-lift-∙∘ {Ψ = Ψ} {M = ⭭ pa̲i̲r̲ LHS RHS} {γ = γ} {tail = ⇡ᴹ M N ⊲ γ₁ ∷ □} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = 🗆} (∙pair∷pm {X = X} {Y = Y} {Γ' = Γ₁} {π' = π'} {↥ = ↥₀}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                   eq0 : (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N) ≡ (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N))
                   eq0 =   (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N)
                          ≡⟨ refl ⟩
                           (⇡ wk-val (wk-trans (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π'))) N)
                          ≡⟨ cong (⇡_) (sym (wk-val-trans N (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π')))) ⟩
                           (⇡ wk-val (wk-cong (wk-cong πₗ)) (wk-val (wk-cong (wk-cong π')) N))
                          ≡⟨ refl ⟩
                           (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N)) ∎
                   eq1 : (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS)) ≡ (wk-v̲a̲l̲ (wk-wk πₗ) RHS)
                   eq1 =   (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS))
                          ≡⟨ wk-v̲a̲l̲-trans RHS (wk-wk wk-id) πₗ ⟩
                           (wk-v̲a̲l̲ (wk-trans (wk-wk wk-id) πₗ) RHS)
                          ≡⟨ refl ⟩
                           (wk-v̲a̲l̲ (wk-wk (wk-trans wk-id πₗ)) RHS)
                          ≡⟨ cong (λ x → wk-v̲a̲l̲ (wk-wk x) RHS) wk-trans-id ⟩
                           (wk-v̲a̲l̲ (wk-wk πₗ) RHS) ∎

                   t : ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS) ∷ □
                   t = ∙pair∷pm {π' = wk-trans πₗ π'}

                   t' : ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ □)
                   t' = subst₂ (λ x y → ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ y ∷ □) {↥ = 🗆})) eq0 eq1 t

                 in
                 Ψ ∙ X ∙ Y , wk-cong (wk-cong πₗ) , (γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS) ,
                 ( ⟦ wk-cong (wk-cong πₗ) ⟧ʷ ⟦ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ⟧ᴱ
                  ≡⟨ refl ⟩
                   (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)) , ⟦ toVal RHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                  ≡⟨ cong (λ x → (x , ⟦ toVal LHS ⟧ᵛ x) , ⟦ toVal RHS ⟧ᵛ x) wk≡ₗ ⟩
                   (⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ
                  ≡⟨ refl ⟩
                    ⟦ γ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ⟧ᴱ ∎ ) ,
                 □ , t' ,
                 ( ⟦ ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ LHS RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ
                 ≡⟨ refl ⟩
                    ⟦ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                    ⟦ (⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆} ⟧ᵛˢ
                 ≡⟨ Q≡Q' ⟩
                   ⟦ ((⇡ wk-val (wk-cong (wk-cong π')) N ⊲ γ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ∷ □) {↥ = 🗆}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                   ⟦ N ⟧ᵛ ((⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ)
                 ≡⟨ cong (λ x → ⟦ N ⟧ᵛ ((⟦ π' ⟧ʷ x , ⟦ toVal LHS ⟧ᵛ x) , ⟦ toVal RHS ⟧ᵛ x)) (sym wk≡ₗ) ⟩
                   ⟦ N ⟧ᵛ ((⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)) , ⟦ toVal RHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ))
                 ≡⟨ refl ⟩
                   ⟦ (⇡ wk-val (wk-cong (wk-cong πₗ)) (wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ □) {↥ = 🗆} ⟧ᵛˢ
                 ≡⟨ refl ⟩
                   ⟦ ∘ ((wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ∎ )


  val-wk-lift-∙∘ {b = non-empty} {b' = non-empty} {Ψ = Ψ} {M = ⭭ pa̲i̲r̲ LHS RHS} {γ = γ} {tail = (⇡ᴹ M N ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇}} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = 🗇} (∙pair∷pm {X = X} {Y = Y} {Γ' = Γ₁} {b = non-empty} {π' = π'} {↥ = ↥₀}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = --{!!}
                 let
                   eq0 : (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N) ≡ (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N))
                   eq0 =   (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N)
                          ≡⟨ refl ⟩
                           (⇡ wk-val (wk-trans (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π'))) N)
                          ≡⟨ cong (⇡_) (sym (wk-val-trans N (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π')))) ⟩
                           (⇡ wk-val (wk-cong (wk-cong πₗ)) (wk-val (wk-cong (wk-cong π')) N))
                          ≡⟨ refl ⟩
                           (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N)) ∎
                   eq1 : (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS)) ≡ (wk-v̲a̲l̲ (wk-wk πₗ) RHS)
                   eq1 =   (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS))
                          ≡⟨ wk-v̲a̲l̲-trans RHS (wk-wk wk-id) πₗ ⟩
                           (wk-v̲a̲l̲ (wk-trans (wk-wk wk-id) πₗ) RHS)
                          ≡⟨ refl ⟩
                           (wk-v̲a̲l̲ (wk-wk (wk-trans wk-id πₗ)) RHS)
                          ≡⟨ cong (λ x → wk-v̲a̲l̲ (wk-wk x) RHS) wk-trans-id ⟩
                           (wk-v̲a̲l̲ (wk-wk πₗ) RHS) ∎

                   t : ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ LHS RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∘ ((⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS) ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})
                   t = ∙pair∷pm {π' = wk-trans πₗ π'}

                   t' : ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ LHS RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∘ ((wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})
                   t' = subst₂ (λ x y → ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ (M₂ ⊲ γ₂ ∷ tail) {↥ = ↥}) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ y ∷ (M₂ ⊲ γ₂ ∷ tail) {↥ = ↥}) {↥ = 🗇})) eq0 eq1 t
                 in
                 Ψ ∙ X ∙ Y , wk-cong (wk-cong πₗ) , (γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS) ,
                 ( ⟦ wk-cong (wk-cong πₗ) ⟧ʷ ⟦ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ⟧ᴱ
                  ≡⟨ refl ⟩
                   (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)) , ⟦ toVal RHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                  ≡⟨ cong (λ x → (x , ⟦ toVal LHS ⟧ᵛ x) , ⟦ toVal RHS ⟧ᵛ x) wk≡ₗ ⟩
                  (⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ
                  ≡⟨ refl ⟩
                  ⟦ γ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ⟧ᴱ ∎ ) ,
                  ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥}) ,
                  t' ,
                  ( ⟦ ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ LHS RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇}) ⟧ᵛꟴ
                  ≡⟨ Q≡Q' ⟩
                   ⟦ ((⇡ wk-val (wk-cong (wk-cong π')) N ⊲ γ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇}) ⟧ᵛˢ
                  ≡⟨ refl ⟩
                   ⟦ ∘ ((wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇}) ⟧ᵛꟴ ∎)


  val-wk-lift-∙∙ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∙ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → ⟦ ∙ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ wk≡ᵣ ∈ ⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∙ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) →ᵛ ∙ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              × ⟦ ∙ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ )
  val-wk-lift-∙∙ {Ψ = Ψ} {M = ⭭ M} {γ = γ} {tail = ⇡ᴿ LHS RHS ⊲ γ'' ∷ □} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = □} {↥' = 🗆} (∙M∷r {M = M} {LHS = LHS} {RHS = RHS} {π' = π'}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                   eq0 : (wk-v̲a̲l̲ (wk-trans πₗ π') LHS) ≡ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS))
                   eq0 = sym (wk-v̲a̲l̲-trans LHS πₗ π')

                   t : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∙ ⭭ pa̲i̲r̲ (wk-v̲a̲l̲ (wk-trans πₗ π') LHS) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ □
                   t = ∙M∷r {π' = wk-trans πₗ π'}

                   t' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS)) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ □) {↥ = 🗆})
                   t' = subst (λ x → ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∙ ⭭ pa̲i̲r̲ x (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ □) eq0 t
                 in
                 Ψ , πₗ , γₗ , wk≡ₗ , □ , t' ,
                 ( ⟦ ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ
                  ≡⟨ refl ⟩
                   ⟦ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ □) {↥ = 🗆}) ⟧ᵛˢ
                  ≡⟨ Q≡Q' ⟩
                    ⟦ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M ⊲ γ ∷ □) {↥ = 🗆}) ⟧ᵛˢ
                  ≡⟨ refl ⟩
                    ⟦ toVal LHS ⟧ᵛ (⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ
                  ≡⟨ cong (λ x → ⟦ toVal LHS ⟧ᵛ (⟦ π' ⟧ʷ x) , ⟦ toVal M ⟧ᵛ x) (sym wk≡ₗ) ⟩
                    ⟦ toVal LHS ⟧ᵛ (⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)) , ⟦ toVal M ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                  ≡⟨ refl ⟩
                   ⟦ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS)) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛˢ
                  ≡⟨ refl ⟩
                   ⟦ ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ∎ )

  val-wk-lift-∙∙ {Ψ = Ψ} {M = ⭭ M} {γ = γ} {tail = ⇡ᴿ LHS RHS ⊲ γ'' ∷ ((M₁ ⊲ γ₁ ∷ tail'') {↥ = ↥''})} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = (M₁ ⊲ γ₁ ∷ tail'') {↥ = ↥''}} {↥' = 🗇} (∙M∷r {M = M} {LHS = LHS} {RHS = RHS} {π' = π'}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                   eq0 : (wk-v̲a̲l̲ (wk-trans πₗ π') LHS) ≡ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS))
                   eq0 = sym (wk-v̲a̲l̲-trans LHS πₗ π')

                   t : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ ((M₁ ⊲ γ₁ ∷ tail'') {↥ = ↥''})) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∙ ⭭ pa̲i̲r̲ (wk-v̲a̲l̲ (wk-trans πₗ π') LHS) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ (M₁ ⊲ γ₁ ∷ tail'')
                   t = ∙M∷r {π' = wk-trans πₗ π'}

                   t' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ (M₁ ⊲ γ₁ ∷ tail'')) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS)) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ ((M₁ ⊲ γ₁ ∷ tail'') {↥ = ↥''})) {↥ = 🗇})
                   t' = subst (λ x → ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ ((M₁ ⊲ γ₁ ∷ tail'') {↥ = ↥''})) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∙ ⭭ pa̲i̲r̲ x (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ (M₁ ⊲ γ₁ ∷ tail'')) eq0 t
                 in
                 Ψ , πₗ , γₗ , wk≡ₗ , (M₁ ⊲ γ₁ ∷ tail'') , t' ,
                 ( ⟦ ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ (M₁ ⊲ γ₁ ∷ tail'')) {↥ = 🗇})) {↥ = 🗇}) ⟧ᵛꟴ
                  ≡⟨ refl ⟩
                   ⟦ ((⇡ᴿ LHS RHS ⊲ γ'' ∷ (M₁ ⊲ γ₁ ∷ tail'')) {↥ = 🗇}) ⟧ᵛˢ
                  ≡⟨ Q≡Q' ⟩
                   ⟦ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M ⊲ γ ∷ (M₁ ⊲ γ₁ ∷ tail'')) {↥ = 🗇}) ⟧ᵛˢ
                  ≡⟨ refl ⟩
                   ⟦ M₁ ⊲ γ₁ ∷ tail'' ⟧ᵛˢ
                  ≡⟨ refl ⟩
                   ⟦ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS)) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ (M₁ ⊲ γ₁ ∷ tail'')) {↥ = 🗇}) ⟧ᵛˢ
                  ≡⟨ refl ⟩
                   ⟦ ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M) ⊲ γₗ ∷ (M₁ ⊲ γ₁ ∷ tail'')) {↥ = 🗇}) ⟧ᵛꟴ ∎ )

  --------------------------------------------------

  height : CompStack Δ X → ℕ
  height ◻ = 0
  height (x ⊲ γ ⦂⦂ cs) = suc (height cs)

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
                 refl , ∘push ,
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
                 ∘sub ,
                 refl ,
                 refl

  comp-wk-lift {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {Ψ = Ψ} {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {π' = π'} {wk≡' = wk≡'} (∘pm π₁ M→M' π'') Q≡Q' {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
               {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}

  comp-wk-lift {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡} {W' = W'} {γ' = γ'} {π' = π'} {wk≡' = wk≡'} (∘var x π'' x₁ πᵥ) Q≡Q' ϖ {wk≡ₗ = wk≡ₗ} =
               {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!} , {!!}

  wk-val-halts : {M : V̲a̲l̲ Γ X} {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ} → EnvEq π γ' γ → ValHalts M γ → ValHalts (wk-v̲a̲l̲ π M) γ'
  wk-val-halts {M = M} {π = π} {γ' = γ'} {γ = γ} _ unit-halts = unit-halts
  wk-val-halts {M = M} {π = π} {γ' = γ'} {γ = γ} ϖ (pair-halts vH₁ vH₂) = pair-halts (wk-val-halts ϖ vH₁) (wk-val-halts ϖ vH₂)
  wk-val-halts {M = M} {π = π} {γ' = γ'} {γ = γ} _ var-halts = var-halts
  wk-val-halts {M = M} {π = π} {γ' = γ'} {γ = γ} ϖ (lam-halts f) = lam-halts {!!}

  ------------------------------------------------------

  {- just here for reference
  data CompStack  where

      ◻     :   CompStack ε R₀

      _⊲_⦂⦂_    : (Γ ∙ Z) ⊢ᶜ X → (γ : Env Γ) → (tail : CompStack Δ X) → {π : Wk Γ Δ} → {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv tail ⟧ᴱ} → CompStack Γ Z
  -}

  data EnvHalts : Env Γ → Set

  {-
  -- is this needed???
  data CSHalts : CompStack Δ X → Set where

    empty-cs : CSHalts ◻

    tocs-halts : (Γ ∙ Z) ⊢ᶜ X → (γ : Env Γ) → (tail : CompStack Δ X) → {π : Wk Γ Δ} → {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv tail ⟧ᴱ}
                 → EnvHalts γ
                 → ...
  -}

  data EnvHalts where

    empty-env : EnvHalts ∗

    val-in-env  : (M : V̲a̲l̲ Γ X) → (γ : Env Γ) → (vH : ValHalts M γ) → (γH : EnvHalts γ) → EnvHalts (γ ﹐ M)

    comp-in-env : (W : Γ ⊢ᶜ X) → (γ : Env Γ) → (cs : CompStack Δ X) → {π : Wk Γ Δ} → {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → CompHalts W γ cs π wk≡
                  → EnvHalts γ
                  → EnvHalts ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡})

  -------------------------

  data TermHalts : {T : LookupState X} → (H : LookupHaltingState T) → Set where

    unit-term-halts : {γ : Env Γ} → TermHalts (found-unit {γ = γ})

    pair-term-halts : {γ : Env Γ} {LHS : V̲a̲l̲ Γ X} {RHS : V̲a̲l̲ Γ Y} → ValHalts (pa̲i̲r̲ LHS RHS) γ → TermHalts (found-pair {LHS = LHS} {RHS = RHS} {γ = γ})

    lam-term-halts  : {γ : Env Γ} {W : (Γ ∙ X) ⊢ᶜ Y} → ValHalts (l̲a̲m̲ W) γ → TermHalts (found-lam {W = W} {γ = γ})

    comp-term-halts : {γ : Env Γ} → {W : Γ ⊢ᶜ X} → {cs : CompStack Δ X} → {π : Wk Γ Δ} → {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → CompHalts W γ cs π wk≡ → TermHalts (found-comp {W = W} {γ = γ} {cs = cs} {π = π} {wk≡ = wk≡})

  ------------------------------

  data LookupSteps : LookupState X → Set where

    steps : {S T : LookupState X} → (S→T : S →ᴸ* T) → (H : LookupHaltingState T) → ⟦ S ⟧ᴸ ≡ ⟦ T ⟧ᴸ → (π : Wk (lCtx S) (lTCtx T)) → (⟦ π ⟧ʷ ⟦ lEnv S ⟧ᴱ ≡ ⟦ lTEnv T ⟧ᴱ)
            → TermHalts H
            → EnvExt (lookup-index S→T) (lEnv S) (lEnv T)
            → LookupSteps S

  lookup : (i : Γ ∋ X) → (γ : Env Γ) → EnvHalts γ → LookupSteps {X = X} ⟨ i ∥ γ ⟩
  lookup Cx.h (γ ﹐ l̲a̲m̲ W) (val-in-env (l̲a̲m̲ W) γ vH γH) = steps (⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩ ◼) (found-lam {W = W} {γ = γ}) refl (wk-wk wk-id) refl (lam-term-halts vH) env-val
  lookup Cx.h (γ ﹐ pa̲i̲r̲ LHS RHS) (val-in-env (pa̲i̲r̲ LHS RHS) γ vH γH) = steps (⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩ ◼) found-pair refl (wk-wk wk-id) refl (pair-term-halts vH) env-val
  lookup h (γ ﹐ u̲n̲i̲t̲) γH = steps (⟨ h ∥ _﹐_ γ (u̲n̲i̲t̲) ⟩ ◼) found-unit refl (wk-wk wk-id) refl unit-term-halts env-val
  lookup Cx.h (γ ﹐ v̲a̲r̲ i) (val-in-env (v̲a̲r̲ i) γ vH γH) with lookup i γ γH
  ... | steps {T = T} i>>T HT i≡T WK w≡γ hT ext =
              let
                a0 = li≡i i>>T HT
                a1 = subst (λ x → EnvExt x γ (lEnv T)) (a0) ext
              in
              steps (_ →ᴸ⟨ val-h-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ hT (ext-jmp a1)
  lookup Cx.h ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) (comp-in-env W₁ γ₁ cs₁ vH γH) =
    steps (⟨ h ∥ γ ﹐﹝ W ╎ cs ﹞ ⟩ ◼) found-comp refl (wk-wk wk-id) refl (comp-term-halts vH) env-comp
  lookup (Cx.t i) (γ ﹐ M) (val-in-env M₁ γ₁ vH γH) with lookup i γ γH
  ... | steps {T = T} i>>T HT i≡T WK w≡γ hT ext = steps (_ →ᴸ⟨ val-t-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ hT (ext-val ext)
  lookup (Cx.t i) (γ ﹐﹝ W ╎ cs ﹞) (comp-in-env W₁ γ₁ cs₁ x γH) with lookup i γ γH
  ... | steps {T = T} i>>T HT i≡T WK w≡γ hT ext =
      steps (_ →ᴸ⟨ comp-t-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ hT (ext-comp ext)


  data ValSteps : ValState T◾ → Set where

    steps : {S T : ValState T◾} → S ↠ᵛ T → (HT : ValHaltingState T) → ⟦ S ⟧ᵛꟴ ≡ ⟦ T ⟧ᵛꟴ → (π : Wk (botCtx T) (botCtx S)) → (⟦ π ⟧ʷ ⟦ botEnv T ⟧ᴱ ≡ ⟦ botEnv S ⟧ᴱ)
            → EnvHalts (botEnv T) → ValHalts (haltingTerm HT) (botEnv T)
            → WkExt π
            → EnvEq π (botEnv T) (botEnv S)
            → ValSteps S

  val-eval-rec : (M : Γ' ⊢ᵛ X) → (γ : Env Γ) → (γH : EnvHalts γ) → (π : Wk Γ Γ') → ValSteps {T◾ = X} (∘ ((⇡ (wk-val π M) ⊲ γ ∷ □) {↥ = 🗆}))

  val-eval-rec {X = `V} (var {A = .`V} i) γ γH π = steps (_ →ᵛ⟨ ∘var-c ⟩．) (∙ v̲a̲r̲ (wk-mem π i) ⊲ γ ■) refl wk-id refl γH var-halts (wk-eq wk-id) enveq-id

  val-eval-rec {X = `Unit} (var {A = .`Unit} i) γ γH π with lookup (wk-mem π i) γ γH
  ... | steps i>>T found-unit i≡T π₁ w≡γ γLH ext =

              let
                ext' = subst (λ x → EnvExt x γ (_ ﹐ u̲n̲i̲t̲)) (li≡i i>>T found-unit) ext
              in

              steps (_ →ᵛ⟨ ∘var i>>T π₁ ext' found-unit ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id refl γH unit-halts (wk-eq wk-id) enveq-id

  val-eval-rec {X = X `× X₁} (var {A = .(X `× X₁)} i) γ γH π with lookup (wk-mem π i) γ γH
  ... | steps i>>T (found-pair {LHS = LHS} {RHS = RHS} {γ = γ₁}) i≡T π₁ w≡γ (pair-term-halts vH) ext =

              let
                ext' = subst (λ x → EnvExt x γ (_ ﹐ pa̲i̲r̲ LHS RHS)) (li≡i i>>T found-pair) ext
              in

              steps

              (_ →ᵛ⟨ ∘var i>>T π₁ ext' found-pair ⟩．)

              (∙ pa̲i̲r̲ (wk-v̲a̲l̲ π₁ LHS) (wk-v̲a̲l̲ π₁ RHS) ⊲ γ ■)

              (⟦ wk-mem π i ⟧ᵐ ⟦ γ ⟧ᴱ
              ≡⟨ i≡T ⟩
              (< ⟦ toVal LHS ⟧ᵛ , ⟦ toVal RHS ⟧ᵛ > ⟦ γ₁ ⟧ᴱ)
              ≡⟨ cong (λ x → < ⟦ toVal LHS ⟧ᵛ , ⟦ toVal RHS ⟧ᵛ > x) (sym w≡γ) ⟩
              (< ⟦ toVal LHS ⟧ᵛ , ⟦ toVal RHS ⟧ᵛ > (⟦ π₁ ⟧ʷ ⟦ γ ⟧ᴱ))
              ≡⟨ refl ⟩
              (⟦ wk-val π₁ (toVal LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ wk-val π₁ (toVal RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)
              ≡⟨ cong (λ x → (⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ wk-val π₁ (toVal RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)) (wk-comm {M = LHS} {π = π₁}) ⟩
              (⟦ toVal (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ wk-val π₁ (toVal RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)
              ≡⟨ cong (λ x → (⟦ toVal (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ)) (wk-comm {M = RHS} {π = π₁}) ⟩
              (⟦ toVal (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ toVal (wk-v̲a̲l̲ π₁ RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)
              ≡⟨ refl ⟩
              (< ⟦ toVal (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ , ⟦ toVal (wk-v̲a̲l̲ π₁ RHS) ⟧ᵛ > ⟦ γ ⟧ᴱ) ∎)

              wk-id

              refl

              γH

              {!!}

              (wk-eq wk-id)

              enveq-id

  val-eval-rec {X = X `⇒ X₁} (var {A = .(X `⇒ X₁)} i) γ γH π with lookup (wk-mem π i) γ γH

  ... | steps i>>T (found-lam {W = W} {γ = γ₁}) i≡T π₁ w≡γ γLH ext =

              let
                ext' = subst (λ x → EnvExt x γ (_ ﹐ l̲a̲m̲ W)) (li≡i i>>T found-lam) ext
              in

              steps

              (_ →ᵛ⟨ ∘var i>>T π₁ ext' found-lam ⟩．)

              (∙ (wk-v̲a̲l̲ π₁ (l̲a̲m̲ W)) ⊲ γ ■)

              (⟦ wk-mem π i ⟧ᵐ ⟦ γ ⟧ᴱ
                ≡⟨ i≡T ⟩
              ((λ y → ⟦ W ⟧ᶜ (⟦ γ₁ ⟧ᴱ , y) ))
                ≡⟨ cong (λ x → (λ y → ⟦ W ⟧ᶜ (x , y) )) (sym w≡γ) ⟩
              (λ y → ⟦ W ⟧ᶜ (⟦ π₁ ⟧ʷ ⟦ γ ⟧ᴱ , y) )
                ≡⟨ refl ⟩
              (curry (< (λ r → proj₁ r) ； ⟦ π₁ ⟧ʷ , (λ r → proj₂ r) > ； ⟦ W ⟧ᶜ)) ⟦ γ ⟧ᴱ ∎)

              wk-id

              refl

              γH

              {!!}

              (wk-eq wk-id)

              enveq-id

  val-eval-rec (lam W) γ γH π = steps (∘ ⇡ (wk-val π (lam W)) ⊲ γ ∷ □ →ᵛ⟨ ∘lam ⟩．) (∙ l̲a̲m̲ (wk-comp (wk-cong π) W) ⊲ γ ■) refl wk-id refl γH {!!} (wk-eq wk-id) enveq-id

  val-eval-rec unit γ γH π = steps (_ →ᵛ⟨ ∘unit ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id refl γH unit-halts (wk-eq wk-id) enveq-id

  val-eval-rec (pair {A = X} {B = Y} LHS RHS) γ γH π with val-eval-rec {X = X} LHS γ γH π
  ... | steps {T = ∙ (⭭_ {X = X} LT ⊲ γ₁ ∷ □) {↥ = 🗆}} L>T ∙LT L≡T πᴸ wk≡ᴸ γH₁ tH we₁ ϖ₁ with val-eval-rec {X = Y} RHS γ₁ γH₁ (wk-trans πᴸ π)
  ...      | steps {T = ∙ (⭭_ {X = Y} RT ⊲ γ₂ ∷ □) {↥ = 🗆}} R>T ∙RT R≡T πᴿ wk≡ᴿ γH₂ tH we₂ ϖ₂ rewrite sym (wk-val-trans RHS πᴸ π) =

            steps

              (
              ∘ ⇡ (wk-val π (pair LHS RHS)) ⊲ γ ∷ □ →ᵛ⟨ ∘pair ⟩． ⨾
              (⟪ L>T ⟫⧻ (⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⊲ γ ∷ □)) ⨾
              (∙ ⭭ LT ⊲ γ₁ ∷ ⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⊲ γ ∷ □) →ᵛ⟨ ∙M∷l ⟩． ⨾
              (⟪ R>T ⟫⧻ (⇡ᴿ LT (wk-val πᴸ (wk-val π RHS)) ⊲ γ₁ ∷ □)) ⨾
              (∙ ⭭ RT ⊲ γ₂ ∷ ⇡ᴿ LT (wk-val πᴸ (wk-val π RHS)) ⊲ γ₁ ∷ □) →ᵛ⟨ ∙M∷r ⟩．
              )

              ∙ pa̲i̲r̲ (wk-v̲a̲l̲ πᴿ LT) RT ⊲ γ₂ ■

              ( ⟦ wk-val π (pair LHS RHS) ⟧ᵛ ⟦ γ ⟧ᴱ
              ≡⟨ refl ⟩
                (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))
              ≡⟨ cong (λ y → (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ y))) (sym wk≡ᴸ) ⟩
                (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ (⟦ πᴸ ⟧ʷ ⟦ γ₁ ⟧ᴱ)))
              ≡⟨ cong (λ y → (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ y)) (wk-sem-trans πᴸ π ⟦ γ₁ ⟧ᴱ) ⟩
                (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
              ≡⟨ cong (λ y → (y , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))) L≡T ⟩
                (⟦ toVal LT ⟧ᵛ ⟦ γ₁ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
              ≡⟨ cong (λ y → (⟦ toVal LT ⟧ᵛ y , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))) (sym wk≡ᴿ) ⟩
                (⟦ toVal LT ⟧ᵛ (⟦ πᴿ ⟧ʷ ⟦ γ₂ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
              ≡⟨ refl ⟩
                (⟦ wk-val πᴿ (toVal LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
              ≡⟨ cong (λ y → (⟦ y ⟧ᵛ ⟦ γ₂ ⟧ᴱ  , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))) (wk-comm {M = LT} {π = πᴿ}) ⟩
                (⟦ toVal (wk-v̲a̲l̲ πᴿ LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
              ≡⟨ cong (λ y → (⟦ toVal (wk-v̲a̲l̲ πᴿ LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , y)) R≡T ⟩
                (⟦ toVal (wk-v̲a̲l̲ πᴿ LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , ⟦ toVal RT ⟧ᵛ ⟦ γ₂ ⟧ᴱ)
              ≡⟨ refl ⟩
                ⟦ pair (toVal (wk-v̲a̲l̲ πᴿ LT)) (toVal RT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ
              ≡⟨ refl ⟩
                ⟦ toVal (pa̲i̲r̲ (wk-v̲a̲l̲ πᴿ LT) RT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ
              ≡⟨ refl ⟩
                ⟦ ∙ (⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πᴿ LT) RT ⊲ γ₂ ∷ □) {↥ = 🗆} ⟧ᵛꟴ ∎ )

              (wk-trans πᴿ πᴸ)

              ( ⟦ wk-trans πᴿ πᴸ ⟧ʷ ⟦ γ₂ ⟧ᴱ
              ≡⟨ sym (wk-sem-trans πᴿ πᴸ ⟦ γ₂ ⟧ᴱ) ⟩
                ⟦ πᴸ ⟧ʷ (⟦ πᴿ ⟧ʷ ⟦ γ₂ ⟧ᴱ)
              ≡⟨ cong (λ y → ⟦ πᴸ ⟧ʷ y) wk≡ᴿ ⟩
                ⟦ πᴸ ⟧ʷ ⟦ γ₁ ⟧ᴱ
              ≡⟨ wk≡ᴸ ⟩
                ⟦ γ ⟧ᴱ ∎)

              γH₂

              {!!}

              (wk-ext-trans we₂ we₁)

              (env-eq-trans we₂ we₁ ϖ₂ ϖ₁)

  val-eval-rec {Γ = Γ} (pm {A = A} {B = B} M N) γ γH π with val-eval-rec M γ γH π
  ... | steps {S = S} M>T ∙ pa̲i̲r̲ LHS RHS ⊲ γ₁ ■ M≡T π₁ wk≡₁ γH₁ tH₁ we₁ ϖ₁ with val-eval-rec N (_﹐_ (_﹐_ γ₁ LHS) (wk-v̲a̲l̲ (wk-wk wk-id) RHS)) {!!} ((wk-cong (wk-cong (wk-trans π₁ π)))) | (wk-val-trans N (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π)))
  ...    | steps {T = T} N>T ∙T N≡T π₂ wk≡₂ γH₂ tH₂ we₂ ϖ₂ | eq with N>T
  ...      | N>T' rewrite sym eq =

        steps
          (
            (∘ ⇡ pm (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⊲ γ ∷ □) →ᵛ⟨ ∘pm ⟩． ⨾
            (⟪ M>T ⟫⧻ (⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⊲ γ ∷ □)) ⨾
            (∙ ⭭ pa̲i̲r̲ LHS RHS ⊲ γ₁ ∷ ⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⊲ γ ∷ □) →ᵛ⟨ ∙pair∷pm ⟩． ⨾
            N>T'
          )

          ∙T

          (  ⟦ wk-val π (pm M N) ⟧ᵛ ⟦ γ ⟧ᴱ
            ≡⟨ refl ⟩
              ⟦ pm (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⟧ᵛ ⟦ γ ⟧ᴱ
            ≡⟨ refl ⟩
            (< idf , ⟦ π ⟧ʷ ； ⟦ M ⟧ᵛ > ； assocl ； ⟦ wk-val (wk-cong (wk-cong π)) N ⟧ᵛ) ⟦ γ ⟧ᴱ
            ≡⟨ refl ⟩
            ⟦ wk-val (wk-cong (wk-cong π)) N ⟧ᵛ (assocl ( (⟦ γ ⟧ᴱ ,  ⟦ M ⟧ᵛ  (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))))
            ≡⟨ cong (λ y → ⟦ wk-val (wk-cong (wk-cong π)) N ⟧ᵛ (assocl ( (⟦ γ ⟧ᴱ , y   )))) M≡T ⟩
            ⟦ wk-val (wk-cong (wk-cong π)) N ⟧ᵛ (assocl ( (⟦ γ ⟧ᴱ ,  (⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)  )))
            ≡⟨ refl ⟩
              ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
            ≡⟨ cong  (λ y → ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ y , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)) (sym wk≡₁) ⟩
              ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
            ≡⟨ refl ⟩
              ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ (wk-val (wk-wk wk-id) (toVal RHS)) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
            ≡⟨ cong (λ y → ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ y ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))) (wk-comm {M = RHS} {π = wk-wk wk-id}) ⟩
              ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
            ≡⟨ cong (λ y → ⟦ N ⟧ᵛ ((y , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))  ) (wk-sem-trans π₁ π ⟦ γ₁ ⟧ᴱ) ⟩
            ⟦ N ⟧ᵛ ((⟦ wk-trans π₁ π ⟧ʷ ⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
            ≡⟨ N≡T ⟩
            ⟦ T ⟧ᵛꟴ ∎)

          (wk-trans π₂ (wk-wk (wk-wk π₁)))

          ( ⟦ wk-trans π₂ (wk-wk (wk-wk π₁)) ⟧ʷ ⟦ botEnv T ⟧ᴱ
            ≡⟨ sym (wk-sem-trans π₂ (wk-wk (wk-wk π₁)) ⟦ botEnv T ⟧ᴱ) ⟩
            ⟦ wk-wk (wk-wk π₁) ⟧ʷ (⟦ π₂ ⟧ʷ ⟦ botEnv T ⟧ᴱ)
            ≡⟨ cong (λ y → ⟦ wk-wk (wk-wk π₁) ⟧ʷ y) wk≡₂ ⟩
            ⟦ wk-wk (wk-wk π₁) ⟧ʷ (((⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))
            ≡⟨ refl ⟩
            ⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ
            ≡⟨ wk≡₁ ⟩
            ⟦ γ ⟧ᴱ ∎)

          γH₂

          tH₂

          (wk-ext-trans we₂ (wk-ext (wk-wk π₁) (wk-ext π₁ we₁)))

          (env-eq-trans we₂ (wk-ext (wk-wk π₁) (wk-ext π₁ we₁)) ϖ₂ (wk-env-val-wk (wk-v̲a̲l̲ (wk-wk wk-id) RHS) (wk-env-val-wk LHS ϖ₁)))

  val-eval : (M : ε ⊢ᵛ X) → ValSteps {T◾ = X} (∘ ((⇡ wk-val wk-id M ⊲ ∗ ∷ □) {↥ = 🗆}))
  val-eval M = val-eval-rec M ∗ empty-env wk-id

  -------------------------------------------------------------------

  {- BEGIN OLD EVAL

  This is the old evaluation function, which is correct, but hard to show to terminate.

  data CompSteps : CompState → Set where

      steps : {S T : CompState} → S →ᶜ* T → CompHaltingState T → ⟦ S ⟧ᶜꟴ ≡ ⟦ T ⟧ᶜꟴ → CompSteps S

  {-# TERMINATING #-}
  mutual

    app-eval-rec :   (M : Γ' ⊢ᵛ X `⇒ Y) → (N : V̲a̲l̲ Γ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ Y) → (πₓ : Wk Γ Δ)
                   → (wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ)
                   → CompSteps ((∙⟨ (a̲pp (wk-val π M) N) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    app-eval-rec (var i) N γ π cs πₓ wk≡₀ with lookup (wk-mem π i) γ
    ... | steps i>>T (found-lam {X = X} {W = W} {γ = γ₁}) i≡T π₁ w≡γ _ with comp-eval-rec W (γ ﹐ N) (wk-cong π₁) cs (wk-wk πₓ) wk≡₀
    ... | steps {T = T} W>WT HT S≡T =

                 steps

                    ((∙⟨ a̲pp (wk-val π (var i)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-var i>>T π₁ ⟩ W>WT))

                    HT

                    (   ⟦ ((∙⟨ C̲o̲m̲p.a̲pp (var (wk-mem π i)) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀}) ⟧ᶜꟴ
                      ≡⟨ refl ⟩
                        ⟦ wk-mem π i ⟧ᵐ ⟦ γ ⟧ᴱ (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ cong (λ x → x (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) i≡T ⟩
                       ⟦ W ⟧ᶜ (⟦ γ₁ ⟧ᴱ , (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ))  (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ cong (λ x → ⟦ W ⟧ᶜ (x , (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ))  (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym w≡γ) ⟩
                       ⟦ W ⟧ᶜ (⟦ π₁ ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ refl ⟩
                        ⟦ ((∘⟨ wk-comp (wk-cong π₁) W ⊰ γ Env.﹐ N ╎ cs ⟩) {π = wk-wk πₓ} {wk≡ = wk≡₀}) ⟧ᶜꟴ
                      ≡⟨ S≡T ⟩
                        ⟦ T ⟧ᶜꟴ ∎)


    app-eval-rec (lam W) N γ π cs πₓ wk≡₀ with comp-eval-rec W (γ ﹐ N) (wk-cong π) cs (wk-wk πₓ) wk≡₀
    ... | steps {T = T} W>WT HT S≡T =

                  steps

                     ( ∙⟨ a̲pp (wk-val π (lam W)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-lam ⟩ W>WT)

                     HT

                     S≡T

    app-eval-rec (pm M₁ N₁) N γ π cs πₓ wk≡₀ with val-eval-rec M₁ γ π
    ... | steps {T = ∙ (⭭ pa̲i̲r̲ {X = X} {Y = Y} LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ with wk-val-trans N₁ (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
    ...       | eq with
                    app-eval-rec
                      N₁
                      ((wk-v̲a̲l̲ (wk-wk (wk-wk π')) N))
                      (γ₁ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS)
                      (wk-cong (wk-cong (wk-trans π' π)))
                      cs
                      (wk-wk (wk-wk (wk-trans π' πₓ)))
                      (⟦ wk-wk (wk-wk (wk-trans π' πₓ)) ⟧ʷ ⟦ γ₁ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ⟧ᴱ
                       ≡⟨ refl ⟩ ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                       ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                       ≡⟨ wk≡₀ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎)
    ...          | steps {T = T} N>NT NT S≡T rewrite (sym eq) =

                 steps

                    (∙⟨ (a̲pp (wk-val π (pm M₁ N₁)) N) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-pm M>T π' ⟩ N>NT )

                    NT

                    (⟦ N₁ ⟧ᵛ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , proj₁ (⟦ M₁ ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))) , proj₂ (⟦ M₁ ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))) (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ cong (λ x → ⟦ N₁ ⟧ᵛ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , proj₁ x) , proj₂ x) (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) M≡T ⟩
                     ⟦ N₁ ⟧ᵛ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ cong (λ x → ⟦ N₁ ⟧ᵛ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) (⟦ toVal N ⟧ᵛ x) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym wk≡) ⟩
                     ⟦ N₁ ⟧ᵛ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ wk-id RHS) ⟧ᵛ ⟦ γ₁ ⟧ᴱ) (⟦ toVal N ⟧ᵛ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ refl ⟩
                     ⟦ N₁ ⟧ᵛ (( ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                               ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ ,
                               ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
                             (⟦ toVal (wk-v̲a̲l̲ (wk-wk (wk-wk π')) N) ⟧ᵛ ((⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                              ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))
                             (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ cong (λ x → ⟦ N₁ ⟧ᵛ ((⟦ π ⟧ʷ x , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                                               ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ ,
                                               ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)) (⟦ toVal (wk-v̲a̲l̲ (wk-wk (wk-wk π')) N) ⟧ᵛ ((⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                                               ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))
                                             (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym wk≡) ⟩
                     ⟦ N₁ ⟧ᵛ (( ⟦ π ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                               ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
                             ( ⟦ toVal (wk-v̲a̲l̲ (wk-wk (wk-wk π')) N) ⟧ᵛ ((⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                               ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ cong (λ x → ⟦ N₁ ⟧ᵛ ((x ,
                                              ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                                              ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
                                             (⟦ toVal (wk-v̲a̲l̲ (wk-wk (wk-wk π')) N) ⟧ᵛ ((⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                                              ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))
                                             (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀) ) (wk-sem-trans π' π ⟦ γ₁ ⟧ᴱ) ⟩
                     ⟦ N₁ ⟧ᵛ (( ⟦ wk-trans π' π ⟧ʷ ⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                               ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
                             ( ⟦ toVal (wk-v̲a̲l̲ (wk-wk (wk-wk π')) N) ⟧ᵛ ((⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ,
                               ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))
                             (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ S≡T ⟩
                     ⟦ T ⟧ᶜꟴ ∎)

    comp-eval-rec : (W : Γ' ⊢ᶜ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ X) → (πₓ : Wk Γ Δ)
                  → (wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ)
                  → CompSteps ((∘⟨ wk-comp π W ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    comp-eval-rec (return {A = X} M) γ π ◻ πₓ wk≡₀ with val-eval-rec {X = X} M γ π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ =

                 steps

                    (∘⟨ wk-comp π (return M) ⊰ γ ╎ ◻ ⟩ →ᶜ⟨ ∘return M>T ⟩ (∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ ◻ ⟩ ◼))

                    ret

                    (cong (λ x → (η x) k₀) M≡T)

    comp-eval-rec (return {A = X} M) γ π ((M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁}) πₓ wk≡₀ with val-eval-rec {X = X} M γ π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ with
                 comp-eval-rec
                   M'
                   (γ₁ ﹐ M₁)
                   (wk-cong (wk-trans π' πₓ))
                   cs
                   (wk-wk (wk-trans (wk-trans π' πₓ) π₁))
                   (⟦ wk-wk (wk-trans (wk-trans π' πₓ) π₁) ⟧ʷ ⟦ γ₁ ﹐ M₁ ⟧ᴱ
                    ≡⟨ refl ⟩ ⟦ (wk-trans (wk-trans π' πₓ) π₁) ⟧ʷ ⟦ γ₁ ⟧ᴱ
                    ≡⟨ sym (wk-sem-trans (wk-trans π' πₓ) π₁ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ π₁ ⟧ʷ (⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                    ≡⟨ cong ⟦ π₁ ⟧ʷ (sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ)) ⟩ ⟦ π₁ ⟧ʷ (⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ))
                    ≡⟨ cong (λ x → ⟦ π₁ ⟧ʷ (⟦ πₓ ⟧ʷ x)) wk≡ ⟩ ⟦ π₁ ⟧ʷ (⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ)
                    ≡⟨ cong ⟦ π₁ ⟧ʷ wk≡₀ ⟩ ⟦ π₁ ⟧ʷ ⟦ γ' ⟧ᴱ
                    ≡⟨ wk≡₁ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎)
    ... | steps {T = ∙⟨ r̲e̲t̲u̲r̲n̲  M₂ ⊰ γ₂ ╎ ◻ ⟩} M'>T ret S≡T =

                   steps

                   (∘⟨ wk-comp π (return M) ⊰ γ ╎ (M' ⊲ γ' ⦂⦂ cs) ⟩
                    →ᶜ⟨ ∘return {wk≡ₓ' = ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ
                                         ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                                         ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                                         ≡⟨ wk≡₀ ⟩ ⟦ γ' ⟧ᴱ ∎} M>T ⟩ ((∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ M' ⊲ γ' ⦂⦂ cs ⟩) {wk≡ = ≡-syntax.step-≡-⟩ _≡_ trans (⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                                                                                                                   (≡-syntax.step-≡-⟩ _≡_ trans (⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ))
                                                                                                                    (≡-syntax.step-≡-⟩ _≡_ trans (⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ)
                                                                                                                     ((_≡_ end-syntax.∎) refl ⟦ γ' ⟧ᴱ) wk≡₀)
                                                                                                                    (cong ⟦ πₓ ⟧ʷ wk≡))
                                                                                                                   (sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ))})
                    →ᶜ⟨ ∙return {πₓ = wk-trans (wk-trans π' πₓ) π₁} {πₓ' = π₁} ⟩ M'>T)

                   ret

                   (   ((⟦ π ⟧ʷ ； ⟦ M ⟧ᵛ) ； η) ⟦ γ ⟧ᴱ ⟦ (M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁} ⟧ᴷ
                     ≡⟨ refl ⟩
                       ⟦ cs ⟧ᶜˢ (λ k → ⟦ M' ⟧ᶜ (⟦ γ' ⟧ᴱ , ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) k) k₀
                     ≡⟨ lem0 cs (⟦ M' ⟧ᶜ (⟦ γ' ⟧ᴱ , ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))) ⟩
                       ⟦ M' ⟧ᶜ (⟦ γ' ⟧ᴱ , ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                     ≡⟨ cong (λ x → ⟦ M' ⟧ᶜ (x , ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym wk≡₀) ⟩
                       ⟦ M' ⟧ᶜ (⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                     ≡⟨ cong (λ x → ⟦ M' ⟧ᶜ (⟦ πₓ ⟧ʷ x , ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym wk≡) ⟩
                       ⟦ M' ⟧ᶜ (⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                     ≡⟨ cong (λ x → ⟦ M' ⟧ᶜ (⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ) , x) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) M≡T ⟩
                       ⟦ M' ⟧ᶜ (⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                     ≡⟨ cong (λ x → ⟦ M' ⟧ᶜ (x , ⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ) ⟩
                       ⟦ M' ⟧ᶜ (⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ , ⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                     ≡⟨ refl ⟩
                       (< (λ r → proj₁ r) ； ⟦ wk-trans π' πₓ ⟧ʷ , (λ r → proj₂ r) > ； ⟦ M' ⟧ᶜ) (⟦ γ₁ ⟧ᴱ , ⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ⟦ cs ⟧ᴷ
                     ≡⟨ S≡T ⟩
                       (⟦ toVal M₂ ⟧ᵛ ； η) ⟦ γ₂ ⟧ᴱ ⟦ ◻ ⟧ᴷ ∎)

    comp-eval-rec (pm {A = X} {B = Y} M W) γ π cs πₓ wk≡₀ with val-eval-rec {X = X `× Y} M γ π
    ...  | steps {T = ∙ ((⭭_ {X = X `× Y} (pa̲i̲r̲ LHS RHS) ⊲ γ' ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ with
                    comp-eval-rec
                     W
                     (γ' ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS)
                     (wk-trans (wk-cong (wk-cong π')) (wk-cong (wk-cong π)))
                     cs
                     (wk-wk (wk-wk (wk-trans π' πₓ)))
                     (⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ' ⟧ᴱ
                      ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ' ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ)
                      ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                      ≡⟨ wk≡₀ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎)
    ...   | steps {T = T} W>T HT S≡T with wk-comp-trans W (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
    ...     | eq rewrite (sym eq) =

                steps

                   (∘⟨ wk-comp π (pm M W) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘pm π M>T π' ⟩ W>T)

                   HT

                   ( ⟦ W ⟧ᶜ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , proj₁ (⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))) , proj₂ (⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ cong₂ (λ x y → ⟦ W ⟧ᶜ ((⟦ π ⟧ʷ x , proj₁ y) , proj₂ y) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym wk≡) M≡T ⟩
                     ⟦ W ⟧ᶜ ((⟦ π ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ' ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ' ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ' ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ cong (λ x → ⟦ W ⟧ᶜ ((x , ⟦ toVal LHS ⟧ᵛ ⟦ γ' ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ' ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (wk-sem-trans π' π ⟦ γ' ⟧ᴱ) ⟩
                     ⟦ W ⟧ᶜ ((⟦ wk-trans π' π ⟧ʷ ⟦ γ' ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ' ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ' ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ S≡T ⟩
                     ⟦ T ⟧ᶜꟴ ∎)

    comp-eval-rec (push W V) γ π cs πₓ wk≡₀ with comp-eval-rec W γ π (((wk-comp (wk-cong π) V) ⊲ γ ⦂⦂ cs) {wk≡ = wk≡₀}) wk-id refl
    ... | steps {T = ∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ₁ ╎ ◻ ⟩} W>T ret S≡T =

                steps

                  (  ∘⟨ push (wk-comp π W) (wk-comp (wk-cong π) V) ⊰ γ ╎ cs ⟩  →ᶜ⟨ ∘push ⟩ W>T )

                  ret

                  (  ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (λ z → ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀))
                  ≡⟨  cong (⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) (extensionality (λ z → sym (lem0 cs ((⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , z)))))) ⟩
                     ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (λ z → ⟦ cs ⟧ᶜˢ (λ k → ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , z) k) k₀)
                  ≡⟨ refl ⟩
                    (⟦ π ⟧ʷ ； ⟦ W ⟧ᶜ) ⟦ γ ⟧ᴱ ⟦ (wk-comp (wk-cong π) V ⊲ γ ⦂⦂ cs) {π = πₓ} {wk≡ = wk≡₀} ⟧ᴷ
                  ≡⟨ S≡T ⟩
                    (⟦ toVal M ⟧ᵛ ； η) ⟦ γ₁ ⟧ᴱ ⟦ ◻ ⟧ᴷ ∎)

    comp-eval-rec (app M N) γ π cs πₓ wk≡₀ with val-eval-rec N γ π
    ... | steps {T = ∙ ((⭭_ NT ⊲ γᴺ ∷ □) {↥ = 🗆})} N>NT ∙NT N≡NT πᴺ wk≡ᴺ with
                    app-eval-rec
                      M
                      NT
                      γᴺ
                      (wk-trans πᴺ π)
                      cs
                      (wk-trans πᴺ πₓ)
                      (⟦ wk-trans πᴺ πₓ ⟧ʷ ⟦ γᴺ ⟧ᴱ
                       ≡⟨ sym (wk-sem-trans πᴺ πₓ ⟦ γᴺ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ πᴺ ⟧ʷ ⟦ γᴺ ⟧ᴱ)
                       ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ᴺ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                       ≡⟨ wk≡₀ ⟩ ⟦ topCsEnv cs ⟧ᴱ ∎)
    ... | steps {T = T} W>WT HT S≡T rewrite (sym (wk-val-trans M πᴺ π)) =

            steps

                ((∘⟨ app (wk-val π M) (wk-val π N) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘app N>NT πᴺ ⟩ W>WT ))

                HT

                ((< ⟦ π ⟧ʷ ； ⟦ M ⟧ᵛ , ⟦ π ⟧ʷ ； ⟦ N ⟧ᵛ > ； Data.Product.uncurry idf) ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ
                ≡⟨ refl ⟩
                 ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (⟦ N ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                ≡⟨ cong (λ x → ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) x (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) N≡NT ⟩
                 ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (⟦ toVal NT ⟧ᵛ ⟦ γᴺ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                ≡⟨ cong (λ x → ⟦ M ⟧ᵛ (⟦ π ⟧ʷ x) (⟦ toVal NT ⟧ᵛ ⟦ γᴺ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym wk≡ᴺ) ⟩
                 ⟦ M ⟧ᵛ (⟦ π ⟧ʷ (⟦ πᴺ ⟧ʷ ⟦ γᴺ ⟧ᴱ)) (⟦ toVal NT ⟧ᵛ ⟦ γᴺ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                ≡⟨ cong (λ x → ⟦ M ⟧ᵛ x (⟦ toVal NT ⟧ᵛ ⟦ γᴺ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (wk-sem-trans πᴺ π ⟦ γᴺ ⟧ᴱ) ⟩
                 ⟦ M ⟧ᵛ (⟦ wk-trans πᴺ π ⟧ʷ ⟦ γᴺ ⟧ᴱ) (⟦ toVal NT ⟧ᵛ ⟦ γᴺ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                ≡⟨ S≡T ⟩
                ⟦ T ⟧ᶜꟴ ∎)

    comp-eval-rec (var {A = X} M) γ π cs πₓ wk≡₀ with val-eval-rec {X = `V} M γ π
    ... | steps {T = ∙ ((⭭ v̲a̲r̲ i) ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ with lookup i γ₁
    ... | steps i>>T (found-comp {X = X} {W = W'} {γ = γ'} {cs = cs'} {π = πᶜ} {wk≡ = wk≡c}) i≡T π₂ w≡γ _ with
                    comp-eval-rec
                     W'
                     γ'
                     wk-id
                     cs'
                     πᶜ
                     wk≡c
    ... | steps {T = ∙⟨ C̲o̲m̲p.r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₂ ╎ ◻ ⟩} W>T ret S≡T rewrite wk-comp-id W' =

                steps

                  ((∘⟨ var (wk-val π M) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘var M>T π' i>>T π₂ ⟩ W>T))

                  ret

                  (((⟦ π ⟧ʷ ； ⟦ M ⟧ᵛ) ； varK) ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ
                    ≡⟨ refl ⟩
                      ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)
                    ≡⟨ M≡T ⟩
                      ⟦ i ⟧ᵐ ⟦ γ₁ ⟧ᴱ
                    ≡⟨ i≡T ⟩
                      ⟦ W' ⟧ᶜ ⟦ γ' ⟧ᴱ (λ y → ⟦ cs' ⟧ᶜˢ (λ k → k y) k₀)
                    ≡⟨ S≡T ⟩
                      (⟦ toVal M₁ ⟧ᵛ ； η) ⟦ γ₂ ⟧ᴱ ⟦ ◻ ⟧ᴷ ∎
                  )

    comp-eval-rec (sub W V) γ π cs πₓ wk≡₀ with comp-eval-rec W ((γ ﹐﹝ wk-comp π V ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡₀}) (wk-cong π) cs (wk-wk πₓ) wk≡₀
    ... | steps {T = T} W>WT HT S≡T =

                steps

                    (∘⟨ sub (wk-comp (wk-cong π) W) (wk-comp π V) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘sub ⟩ W>WT)

                    HT

                    S≡T

    comp-eval : (W : ε ⊢ᶜ R₀) → CompSteps ((∘⟨ wk-comp wk-id W ⊰ ∗ ╎ ◻ ⟩) {π = wk-id} {wk≡ = refl})
    comp-eval W = comp-eval-rec W ∗ wk-id ◻ wk-id refl

    END OLD EVAL -}


postulate k₀ : ⟦ `Unit ⟧ → R

open VMain {R₀ = `Unit} k₀
open CMain {R₀ = `Unit} k₀

---- Examples

-- s/\(PartialTerm\.\|ValStack\.\|Env\.\|V̲a̲l̲\.\|CompStack\.\|ValStack\.\|ValState\.\|_↠ᵛ_\.\|_→ᵛ_\.\|_→ᴸ\*_\.\|_→ᴸ_\.\|LookupState\.\|C̲o̲m̲p.\)//g

ex3 : ε ⊢ᶜ `Unit
ex3 = return (pm (pair unit unit) (var (t h)))

ex4 : ε ⊢ᶜ `Unit
ex4 = sub (var (var h)) (return (pm (pair unit unit) (var (t h))))

ex5 : ε ⊢ᶜ `Unit
ex5 = push (sub (push (return (var h)) (var (var h))) (return (pm (pair unit unit) (var (t h))))) (return (var h))

ex6 : ε ⊢ᶜ `Unit
ex6 = sub (var (pm (pair (var h) unit) (var (t h)))) (return unit)

ex7 : ε ⊢ᶜ `Unit
ex7 = push (sub (var (pm (pair (var h) unit) (var (t h)))) (return unit)) (return (var h))

ex8 : ε ⊢ᶜ `Unit
ex8 = sub (push (var (var h)) (app (var h) unit)) (return unit)

ex9 : ε ⊢ᶜ `Unit
ex9 = sub (push (sub (return (var h)) ((return (var h)))) (var (var h))) (return unit)

ex10 : ε ⊢ᶜ `Unit
ex10 = push (sub (push (var (var h)) (app (var h) unit)) (return unit)) (return unit)

ex11 : ε ⊢ᶜ `Unit
ex11 = app (lam (app (lam (push (sub (push (var (var h)) (app (var h) unit)) (return (lam (return (var h))))) (app (var h) unit))) unit)) unit

ex12 : ε ⊢ᶜ `Unit
ex12 = push (return unit) (return (pm (pair (pair unit unit) (pair unit unit)) unit))

ex13 : ε ⊢ᶜ `Unit
ex13 = sub ((var (var h))) (return (pm (pair (pair unit unit) (pair unit unit)) unit))

ex14 : ε ⊢ᶜ (`Unit)
ex14 = push (push (app (lam {A = `Unit} (sub (var (var h)) (return unit))) unit) (return unit)) (app (lam (return unit)) (pair (pair (pair (var h) (var h)) (var h)) (var h)))

ex15 : ε ⊢ᶜ (`Unit)
ex15 = push (push (app (lam {A = `Unit} (sub (var (var h)) (return unit))) unit) (return unit)) (return unit)

-- _ : comp-eval ex15 ≡ {! comp-eval ex15 !}
-- _ = refl
