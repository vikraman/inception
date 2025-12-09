module Inception.Sub.CompMachine (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)
open Eq.≡-Reasoning using (step-≡-⟩; step-≡-∣; step-≡-⟨; _∎; step-≡)

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
                         →ᶜ ((∙⟨ a̲pp (wk-val πᵥ (lam W)) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ})

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

  data CompSteps : CompState → Set where

      steps : {S T : CompState} → S →ᶜ* T → CompHaltingState T → ⟦ S ⟧ᶜꟴ ≡ ⟦ T ⟧ᶜꟴ → List ℕ → CompSteps S


  postulate
    extensionality : ∀ {A B : Set} {f g : A → B}
      → (∀ (x : A) → f x ≡ g x)
        -----------------------
      → f ≡ g

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

-----------------------------------------------------

  variable
    n m n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ : ℕ

  ≤-trans : n₁ ≤ n₂ → n₂ ≤ n₃ → n₁ ≤ n₃
  ≤-trans {n₁ = zero} {n₂ = n₂} {n₃ = n₃} n₁≤n₂ n₂≤n₃ = z≤n
  ≤-trans {n₁ = suc n₁} {n₂ = suc n₂} {n₃ = suc n₃} (s≤s n₁≤n₂) (s≤s n₂≤n₃) = s≤s (≤-trans n₁≤n₂ n₂≤n₃)

  ≤-refl : n ≤ n
  ≤-refl {n = zero} = z≤n
  ≤-refl {n = suc n} = s≤s ≤-refl

  n≤sn : n ≤ suc n
  n≤sn {n = zero} = z≤n
  n≤sn {n = suc n} = s≤s n≤sn

  n≤sm : n ≤ m → n ≤ suc m
  n≤sm {n = zero} {m = zero} n≤m = n≤sn
  n≤sm {n = zero} {m = suc m} n≤m = z≤n
  n≤sm {n = suc n} {m = suc m} (s≤s n≤m) = s≤s (≤-trans n≤sn (s≤s n≤m))

  p≤p : suc n ≤ suc m → n ≤ m
  p≤p (s≤s sn≤sm) = sn≤sm

  p≤n : suc n ≤ m → n ≤ m
  p≤n {m = suc m} (s≤s sn≤m) = n≤sm sn≤m

  n+z : (n : ℕ) → n + zero ≡ n
  n+z zero = refl
  n+z (suc n) = cong suc (n+z n)

  --{-# REWRITE n+z #-}

-----------------------------------------------------

  +-assoc : {n₁ n₂ n₃ : ℕ} → n₁ + n₂ + n₃ ≡ n₁ + (n₂ + n₃)
  +-assoc {zero} {n₂} {n₃} = refl
  +-assoc {suc n₁} {n₂} {n₃} rewrite +-assoc {n₁} {n₂} {n₃} = refl

  +-comm : n + m ≡ m + n
  +-comm {n = zero} {m = zero} = refl
  +-comm {n = zero} {m = suc m} = cong suc (+-comm {n = zero} {m = m})
  +-comm {n = suc n} {m = zero} = cong suc (+-comm {n = n} {m = zero})
  +-comm {n = suc n} {m = suc m} rewrite +-comm {n = n} {m = suc m} | +-comm {n = m} {m = suc n} | +-comm {n = m} {m = n} = refl

  *-comm : n * m ≡ m * n
  *-comm {n = zero} {m = zero} = refl
  *-comm {n = zero} {m = suc m} = *-comm {n = zero} {m = m}
  *-comm {n = suc n} {m = zero} = *-comm {n = n} {m = zero}
  *-comm {n = suc n} {m = suc m}
    rewrite *-comm {n = n} {m = suc m} | *-comm {n = m} {m = suc n}
     | *-comm {n = n} {m = m}
     | sym (+-assoc {n₁ = m} {n₂ = n} {n₃ = m * n})
     | sym (+-assoc {n₁ = n} {n₂ = m} {n₃ = m * n})
     | +-comm {n = n} {m = m}
     = refl

-----------------------------------------------------

  +-≤-cong : (n₁ ≤ n₃) → (n₂ ≤ n₄) → (n₁ + n₂ ≤ n₃ + n₄)
  +-≤-cong z≤n z≤n = z≤n
  +-≤-cong {n₃ = n₃} z≤n (s≤s {m = m} {n = n} n₂≤n₄) rewrite +-comm {n = n₃} {m = suc n} | +-comm {n = n} {m = n₃} = s≤s (+-≤-cong z≤n n₂≤n₄)
  +-≤-cong (s≤s n₁≤n₃) n₂≤n₄ = s≤s (+-≤-cong n₁≤n₃ n₂≤n₄)

  snm : suc (n + m) ≡ n + (suc m)
  snm {n = zero} {m = m} = refl
  snm {n = suc n} {m = m} = cong suc snm

  +-≤-cong-rev-left : (n + m₁ ≤ n + m₂) → (m₁ ≤ m₂)
  +-≤-cong-rev-left {n = zero} m₁≤m₂ = m₁≤m₂
  +-≤-cong-rev-left {n = suc n} {m₁ = m₁} {m₂ = m₂} m₁≤m₂ rewrite snm {n = n} {m = m₁} | snm {n = n} {m = m₂} = p≤p (+-≤-cong-rev-left m₁≤m₂)

  *-≤-cong : (n₁ ≤ n₃) → (n₂ ≤ n₄) → (n₁ * n₂ ≤ n₃ * n₄)
  *-≤-cong z≤n z≤n = z≤n
  *-≤-cong z≤n (s≤s n₂≤n₄) = z≤n
  *-≤-cong (s≤s {m = m} n₁≤n₃) z≤n rewrite *-comm {n = m} {m = zero} = z≤n
  *-≤-cong (s≤s n₁≤n₃) (s≤s n₂≤n₄) = s≤s (+-≤-cong n₂≤n₄ (*-≤-cong n₁≤n₃ (s≤s n₂≤n₄)))

-----------------------------------------------------

  mutual
    count-in-val : (i : Γ ∋ X) → (M : Val Γ Z) → ℕ

    count-in-val Cx.h (var Cx.h) = 1
    count-in-val Cx.h (var (Cx.t i)) = 0
    count-in-val (Cx.t i) (var Cx.h) = 0
    count-in-val (Cx.t i₁) (var (Cx.t i₂)) = count-in-val i₁ (var i₂)

    count-in-val Cx.h (lam W) = count-in-comp (t h) W
    count-in-val (Cx.t i) (lam W) = count-in-comp (t (t i)) W

    count-in-val Cx.h (pair M N) = count-in-val h M + count-in-val h N
    count-in-val (Cx.t i) (pair M N) = count-in-val (t i) M + count-in-val (t i) N

    count-in-val Cx.h (pm M N) = count-in-val h M + count-in-val (t (t h)) N
    count-in-val (Cx.t i) (pm M N) = count-in-val (t i) M + count-in-val (t (t (t i))) N

    count-in-val Cx.h unit = 0
    count-in-val (Cx.t i) unit = 0

    count-in-comp : (i : Γ ∋ X) → (W : Comp Γ Z) → ℕ
    count-in-comp i (return M) = count-in-val i M
    count-in-comp i (pm M W) = count-in-val i M + count-in-comp (t (t i)) W
    count-in-comp i (push W₁ W₂) = count-in-comp i W₁ + count-in-comp (t i) W₂
    count-in-comp i (app M N) = count-in-val i M + count-in-val i N
    count-in-comp i (var M) = count-in-val i M
    count-in-comp i (sub W₁ W₂) = count-in-comp (t i) W₁ + count-in-comp i W₂

-------------------------------

  data TermMetric : Ty → Set where
    m-Unit : (m : ℕ) → TermMetric `Unit
    m-V : (m : ℕ) → (w : ℕ) → (csn : List (ℕ × ℕ)) → TermMetric (`V)
    m-⇒ : (m : ℕ) → (cnt : ℕ) → (nm : TermMetric Y) → TermMetric (X `⇒ Y)
    m-×   : (m : ℕ) → (nm₁ : TermMetric X) → (nm₂ : TermMetric Y) → TermMetric (X `× Y)

  data Wkn : (Γ : Ctx) → (ns : List (Σ[ X ∈ Ty ] TermMetric X)) → Set where
    wkn-nil  : Wkn ε []
    wkn-cong :   {Γ : Ctx} → {ne : List (Σ[ X ∈ Ty ] TermMetric X)} → {Y : Ty}
               → {e : TermMetric Y} → (ϖ : Wkn Γ ne) → Wkn (Γ ∙ Y) ((Y , e) ∷ ne)
    wkn-cons :   {Γ : Ctx} → {ne : List (Σ[ X ∈ Ty ] TermMetric X)}
               → {Y : Ty} → (ϖ : Wkn Γ ne) → Wkn (Γ ∙ Y) ne

  p1 : TermMetric (X `⇒ Y) → ℕ
  p1 (m-⇒ m cnt nm) = m

  p2 : TermMetric (X `⇒ Y) → ℕ
  p2 (m-⇒ m cnt nm) = cnt

  p3 : TermMetric (X `⇒ Y) → TermMetric Y
  p3 (m-⇒ m cnt nm) = nm

  vx : TermMetric (X `× Y) → ℕ
  vx (m-× m l r) = m

  lhs : TermMetric (X `× Y) → TermMetric X
  lhs (m-× m l r) = l

  rhs : TermMetric (X `× Y) → TermMetric Y
  rhs (m-× m l r) = r

  incr : ℕ → TermMetric X → TermMetric X
  incr n (m-Unit m) = m-Unit (n + m)
  incr n (m-V m w csn) = m-V (n + m) w csn
  incr n (m-⇒ m cnt nm) = m-⇒ (n + m) cnt nm
  incr n (m-× m nm₁ nm₂) = m-× (n + m) nm₁ nm₂

  csn-to-nat₀ : ℕ → List (ℕ × ℕ) → ℕ
  csn-to-nat₀ w [] = 0
  csn-to-nat₀ w ((tm , cnt) ∷ csn) = (tm + (w * cnt)) + (csn-to-nat₀ (tm + (w * cnt)) csn)

  ⟪_⟫ : TermMetric X → ℕ
  ⟪ m-Unit m ⟫ = m
  ⟪ m-V m w csn ⟫ = m + w + csn-to-nat₀ w csn
  ⟪ m-⇒ m cnt nm ⟫ = m + ⟪ nm ⟫
  ⟪ m-× m nm₁ nm₂ ⟫ = m + ⟪ nm₁ ⟫ + ⟪ nm₂ ⟫

  lhs-incr-drop : (n : ℕ) → (nm : TermMetric (X `× Y)) → ⟪ lhs (incr n nm) ⟫ ≡ ⟪ lhs nm ⟫
  lhs-incr-drop n (m-× m nm₁ nm₂) = refl

  rhs-incr-drop : (n : ℕ) → (nm : TermMetric (X `× Y)) → ⟪ rhs (incr n nm) ⟫ ≡ ⟪ rhs nm ⟫
  rhs-incr-drop n (m-× m nm₁ nm₂) = refl

  zero-metric : TermMetric X
  zero-metric {X = `Unit} = m-Unit 0
  zero-metric {X = X `× Y} = m-× 0 (zero-metric {X = X}) (zero-metric {X = Y})
  zero-metric {X = X `⇒ Y} = m-⇒ 0 0 (zero-metric {X = Y})
  zero-metric {X = `V} = m-V 0 0 []

  lookup-metric : (i : Γ ∋ Y) → (E : List (Σ[ X ∈ Ty ] TermMetric X)) → Wkn Γ E → TermMetric Y
  lookup-metric Cx.h ((Y , e) ∷ ne) (wkn-cong ϖ) = e
  lookup-metric (Cx.t i) ((X , e) ∷ ne) (wkn-cong ϖ) = lookup-metric i ne ϖ
  lookup-metric {Y = Y} Cx.h [] (wkn-cons ϖ) = zero-metric
  lookup-metric {Y = Y} Cx.h (x ∷ E) (wkn-cons ϖ) = zero-metric
  lookup-metric {Y = Y} (Cx.t i) [] (wkn-cons ϖ) = zero-metric
  lookup-metric (Cx.t i) (x ∷ E) (wkn-cons ϖ) = lookup-metric i (x ∷ E) ϖ

  mutual

    val-metric : (M : Val Γ Y) → (E : List (Σ[ X ∈ Ty ] TermMetric X)) → Wkn Γ E → (csn : List (ℕ × ℕ)) → TermMetric Y
    val-metric (var i) E ϖ csn = incr 2 (lookup-metric i E ϖ)
    val-metric (lam W) E ϖ csn = incr 2 (m-⇒ 0 (count-in-comp h W) (comp-metric W E (wkn-cons ϖ) csn))
    val-metric (pair M N) E ϖ csn = incr 2 (m-× 0 (val-metric M E ϖ csn) (val-metric N E ϖ csn))
    val-metric (pm {A = X} {B = Y} M N) E ϖ csn = let IH = val-metric M E ϖ csn in incr (suc (vx IH + ⟪ val-metric N E (wkn-cons (wkn-cons ϖ)) csn ⟫)) (val-metric N ((Y , rhs IH) ∷ (X , lhs IH) ∷ E) (wkn-cong (wkn-cong ϖ)) csn)
    val-metric unit E ϖ csn = m-Unit 2

    comp-metric : (W : Comp Γ Y) → (E : List (Σ[ X ∈ Ty ] TermMetric X)) → Wkn Γ E → (csn : List (ℕ × ℕ)) → TermMetric Y
    comp-metric (return M) E ϖ csn = incr 2 (val-metric M E ϖ csn)
    comp-metric (pm {A = X} {B = Y} M W) E ϖ csn = let IH = val-metric M E ϖ csn in incr (suc (vx IH + ⟪ comp-metric W E (wkn-cons (wkn-cons ϖ)) csn ⟫)) (comp-metric W ((Y , rhs IH) ∷ (X , lhs IH) ∷ E) (wkn-cong (wkn-cong ϖ)) csn)
    comp-metric (push {A = X} W₁ W₂) E ϖ csn =
      let
        w = (comp-metric W₂ ((X , (comp-metric W₁ E ϖ csn)) ∷ E) (wkn-cong ϖ) csn)
      in
        incr (suc ⟪ comp-metric W₁ E ϖ ((count-in-comp h W₂ , ⟪ w ⟫) ∷ csn) ⟫) w
    comp-metric (app M N) E ϖ csn = let IH = val-metric M E ϖ csn in incr (2 + ((p1 IH) + ((suc (p2 IH)) * ⟪ val-metric N E ϖ csn ⟫))) (p3 IH)
    comp-metric (var M) E ϖ csn = incr (suc ⟪ val-metric M E ϖ csn ⟫) zero-metric
    comp-metric (sub W₁ W₂) E ϖ csn = let w = ⟪ comp-metric W₂ E ϖ csn ⟫ in incr (suc ⟪ comp-metric W₂ E ϖ csn ⟫) (comp-metric W₁ ((`V , m-V 0 w csn) ∷ E) (wkn-cong ϖ) csn)

    v̲a̲l̲-metric : (M : V̲a̲l̲ Γ Y) → (E : List (Σ[ X ∈ Ty ] TermMetric X)) → Wkn Γ E → (csn : List (ℕ × ℕ)) → TermMetric Y
    v̲a̲l̲-metric (l̲a̲m̲ W) E ϖ csn = incr 1 (m-⇒ 0 (count-in-comp h W) (comp-metric W E (wkn-cons ϖ) csn))
    v̲a̲l̲-metric (pa̲i̲r̲ M N) E ϖ csn = incr 1 (m-× 0 (v̲a̲l̲-metric M E ϖ csn) (v̲a̲l̲-metric N E ϖ csn))
    v̲a̲l̲-metric u̲n̲i̲t̲ E ϖ csn = m-Unit 1
    v̲a̲l̲-metric (v̲a̲r̲ i) E ϖ csn = incr 1 (lookup-metric i E ϖ)

    c̲o̲m̲p-metric : (W : C̲o̲m̲p Γ Y) → (E : List (Σ[ X ∈ Ty ] TermMetric X)) → Wkn Γ E → (csn : List (ℕ × ℕ)) → TermMetric Y
    c̲o̲m̲p-metric (r̲e̲t̲u̲r̲n̲ M) E ϖ csn = incr 1 (v̲a̲l̲-metric M E ϖ csn)
    c̲o̲m̲p-metric (a̲pp M N) E ϖ csn = let IH = val-metric M E ϖ csn in incr (suc ((p1 IH) + ((suc (p2 IH)) * ⟪ v̲a̲l̲-metric N E ϖ csn ⟫))) (p3 IH)

  mutual

    env-metric : Env Γ → List (ℕ × ℕ) → Σ[ E ∈ List (Σ[ X ∈ Ty ] TermMetric X) ] Wkn Γ E
    env-metric ∗ _ = [] , wkn-nil
    env-metric {Γ = Γ ∙ X} (γ ﹐ M) csn =
      let
        IH = env-metric γ csn
      in
        (X , v̲a̲l̲-metric M (proj₁ IH) (proj₂ IH) csn) ∷ (proj₁ IH) , wkn-cong (proj₂ IH)
    env-metric {Γ = Γ ∙ `V} ((γ ﹐﹝ W ╎ cs ﹞) {π = π}) csn =
      let
        IH = env-metric γ csn
        IH2 = env-metric γ (cs-to-csn cs)
        w = ⟪ comp-metric W (proj₁ IH2) (proj₂ IH2) (cs-to-csn cs) ⟫
      in
        (`V , m-V 0 w (cs-to-csn cs)) ∷ (proj₁ IH) , wkn-cong (proj₂ IH)

    cs-to-csn : (cs : CompStack Δ Z) → List (ℕ × ℕ)
    cs-to-csn ◻ = []
    cs-to-csn ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡}) =
      let
        csn = cs-to-csn cs
        IH = env-metric γ csn
      in
        ( ⟪ comp-metric W (proj₁ IH) (wkn-cons (proj₂ IH)) csn ⟫ , (count-in-comp h W) ) ∷ csn

  compstate-metric : CompState → ℕ
  compstate-metric ((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π}) =
    let
      csn = cs-to-csn cs
      e = env-metric γ csn
      w = ⟪ comp-metric W (proj₁ e) (proj₂ e) csn ⟫
    in
      w + csn-to-nat₀ w csn
  compstate-metric ((∙⟨ W ⊰ γ ╎ cs ⟩) {π = π}) =
    let
      csn = cs-to-csn cs
      e = env-metric γ csn
      w = ⟪ c̲o̲m̲p-metric W (proj₁ e) (proj₂ e) csn ⟫
    in
      w + csn-to-nat₀ w csn

  botCtx : ValStack non-empty T◾ → Ctx
  botCtx ((_⊲_∷_) {Γ = Γ} _ _ □) = Γ
  botCtx ((x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})) {↥ = ↥}) = botCtx ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})

  botEnv : (S : ValStack non-empty T◾) → Env (botCtx S)
  botEnv ((_⊲_∷_) {Γ = Γ} _ γ □) = γ
  botEnv ((x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})) {↥ = ↥}) = botEnv ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})

  botTerm : (S : ValStack non-empty T◾) → PartialTerm (botCtx S) (T◾)
  botTerm ((_⊲_∷_) {Γ = Γ} M γ □ {↥ = 🗆}) = M
  botTerm ((x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})) {↥ = ↥}) = botTerm ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})

  partial-term-metric : PartialTerm Γ X → (E : List (Σ[ X ∈ Ty ] TermMetric X)) → Wkn Γ E → List (ℕ × ℕ) → ℕ
  partial-term-metric (⭭ M) E ϖ csn = ⟪ v̲a̲l̲-metric M E ϖ csn ⟫
  partial-term-metric (⇡ M) E ϖ csn = ⟪ val-metric M E ϖ csn ⟫
  partial-term-metric (⇡ᴹ M N) E ϖ csn = ⟪ val-metric (pm M N) E ϖ csn ⟫
  partial-term-metric (⇡ᴸ LHS RHS) E ϖ csn = ⟪ val-metric (pair LHS RHS) E ϖ csn ⟫
  partial-term-metric (⇡ᴿ LHS RHS) E ϖ csn = ⟪ val-metric (pair (toVal LHS) RHS) E ϖ csn ⟫

  valstate-metric : ValState X → ℕ → List (ℕ × ℕ) → ℕ
  valstate-metric (∘ S) w csn =
    let
      e = env-metric (botEnv S) csn
      m = partial-term-metric (botTerm S) (proj₁ e) (proj₂ e) csn
    in
      (w + m) + (csn-to-nat₀ (w + m) csn)
  valstate-metric (∙ S) w csn =
    let
      e = env-metric (botEnv S) csn
      m = partial-term-metric (botTerm S) (proj₁ e) (proj₂ e) csn
    in
      (w + m) + (csn-to-nat₀ (w + m) csn)

-------------------------------------------------------

  csn-decr : (n₁ ≤ n₂) → (csn : List (ℕ × ℕ)) → csn-to-nat₀ n₁ csn ≤ csn-to-nat₀ n₂ csn
  csn-decr {n₁ = n₁} {n₂ = n₂} z≤n [] = ≤-refl
  csn-decr {n₁ = n₁} {n₂ = n₂} z≤n (x ∷ csn) = let le1 = (+-≤-cong (≤-refl {n = proj₁ x}) z≤n) in +-≤-cong le1 (csn-decr le1 csn)
  csn-decr {n₁ = n₁} {n₂ = n₂} (s≤s n₁≤n₂) [] = ≤-refl
  csn-decr {n₁ = n₁} {n₂ = n₂} (s≤s n₁≤n₂) (x ∷ csn) = let le1 = (+-≤-cong (≤-refl {n = proj₁ x}) (+-≤-cong (≤-refl {n = proj₂ x}) (*-≤-cong n₁≤n₂ (≤-refl {n = proj₂ x})))) in +-≤-cong le1 (csn-decr le1 csn)

  zm-coh : (X : Ty) → ⟪ zero-metric {X = X} ⟫ ≡ 0
  zm-coh `Unit = refl
  zm-coh (X `× Y) rewrite zm-coh X | zm-coh Y = refl
  zm-coh (X `⇒ Y) rewrite zm-coh Y = refl
  zm-coh `V = refl

  {-# REWRITE zm-coh #-}

  incr-coh : (n : ℕ) → (X : Ty) → (nm : TermMetric X) → ⟪ incr n nm ⟫ ≡ n + ⟪ nm ⟫
  incr-coh zero `Unit (m-Unit m) = refl
  incr-coh zero (X `× X₁) (m-× m nm nm₁) = refl
  incr-coh zero (X `⇒ X₁) (m-⇒ m cnt nm) = refl
  incr-coh zero `V (m-V m w csn) = refl
  incr-coh (suc n) `Unit (m-Unit m) = refl
  incr-coh (suc n) (X `× X₁) (m-× m nm nm₁) rewrite +-assoc {n} {m} {⟪ nm ⟫} | +-assoc {n} {m + ⟪ nm ⟫} {⟪ nm₁ ⟫} = refl
  incr-coh (suc n) (X `⇒ X₁) (m-⇒ m cnt nm) rewrite +-assoc {n} {m} {⟪ nm ⟫} = refl
  incr-coh (suc n) `V (m-V m w csn) rewrite +-assoc {n} {m} {w} | +-assoc {n} {m + w} {csn-to-nat₀ w csn} = refl

  {-# REWRITE incr-coh #-}

  incr-zero-coh : (X : Ty) → (nm : TermMetric X) → incr zero nm ≡ nm
  incr-zero-coh `Unit (m-Unit m) = refl
  incr-zero-coh (X `× X₁) (m-× m nm₁ nm₂) = refl
  incr-zero-coh (X `⇒ X₁) (m-⇒ m cnt nm) = refl
  incr-zero-coh `V (m-V m w csn) = refl

  {-# REWRITE incr-zero-coh #-}

  vx+n : (nm : TermMetric (X `× Y)) → vx (incr n nm) ≡ n + (vx nm)
  vx+n (m-× m nm nm₁) = refl

  {-# REWRITE vx+n #-}

-------------------------------------------------------

  data ⊥ : Set where

  ql : ⊥ → (A : Set) → A
  ql () b

  data Wke : {E E' : List (Σ[ X ∈ Ty ] TermMetric X)} → (ϖ : Wkn Γ E) → (ϖ' : Wkn Γ E') → Set where
   wke-nil : Wke wkn-nil wkn-nil
   wke-cc  : {E E' : List (Σ[ X ∈ Ty ] TermMetric X)} → {ϖ : Wkn Γ E} → {ϖ' : Wkn Γ E'} → (θ : Wke ϖ ϖ') → {e : TermMetric Y} → Wke (wkn-cong {Y = Y} {e = e} ϖ) (wkn-cong {Y = Y} {e = e} ϖ')
   wke-ww  : {E E' : List (Σ[ X ∈ Ty ] TermMetric X)} → {ϖ : Wkn Γ E} → {ϖ' : Wkn Γ E'} → (θ : Wke ϖ ϖ') → Wke (wkn-cons {Y = Y} ϖ) (wkn-cons {Y = Y} ϖ')

  wke-id : {E : List (Σ[ X ∈ Ty ] TermMetric X)} → {ϖ : Wkn Γ E} → Wke ϖ ϖ
  wke-id {ϖ = wkn-nil} = wke-nil
  wke-id {ϖ = wkn-cong ϖ} = wke-cc wke-id
  wke-id {ϖ = wkn-cons ϖ} = wke-ww wke-id

  wke-z-l : {e : (Σ[ X ∈ Ty ] TermMetric X)} {E : List (Σ[ X ∈ Ty ] TermMetric X)} {ϖ : Wkn Γ []} {ϖ' : Wkn Γ (e ∷ E)} → Wke ϖ ϖ' → ⊥
  wke-z-l (wke-ww θ) = wke-z-l θ

  wke-z-r : {e : (Σ[ X ∈ Ty ] TermMetric X)} {E : List (Σ[ X ∈ Ty ] TermMetric X)} {ϖ : Wkn Γ (e ∷ E)} {ϖ' : Wkn Γ []} → Wke ϖ ϖ' → ⊥
  wke-z-r (wke-ww θ) = wke-z-r θ

  wk-e : (π : Wk Γ Δ) → {E : List (Σ[ X ∈ Ty ] TermMetric X)} → (ϖ : Wkn Δ E) → Wkn Γ E
  wk-e wk-ε ϖ = ϖ
  wk-e (wk-cong π) (wkn-cong ϖ) = wkn-cong (wk-e π ϖ)
  wk-e (wk-cong π) (wkn-cons ϖ) = wkn-cons (wk-e π ϖ)
  wk-e (wk-wk π) ϖ = wkn-cons (wk-e π ϖ)

  wk-e-id : {E : List (Σ[ X ∈ Ty ] TermMetric X)} → (ϖ : Wkn Γ E) → wk-e wk-id ϖ ≡ ϖ
  wk-e-id {Γ = Cx.ε} ϖ = refl
  wk-e-id {Γ = Γ Cx.∙ x} (wkn-cong ϖ) = cong wkn-cong (wk-e-id ϖ)
  wk-e-id {Γ = Γ Cx.∙ x} (wkn-cons ϖ) = cong wkn-cons (wk-e-id ϖ)


------------------------------------------------------------------------------------------------------
-- THIS SECTION IS PROBABLY REDUNDANT

  mutual

    wk-mem-eq : (i : Γ ∋ Y) → (E E' : List (Σ[ X ∈ Ty ] TermMetric X)) → {ϖ : Wkn Γ E} → {ϖ' : Wkn Γ E'} → (θ : Wke ϖ ϖ') → (csn : List (ℕ × ℕ)) → (lookup-metric i E' ϖ') ≡ (lookup-metric i E ϖ)
    wk-mem-eq Cx.h E E' {ϖ = ϖ} {ϖ' = ϖ'} (wke-cc θ) csn = refl
    wk-mem-eq Cx.h [] [] {ϖ = ϖ} {ϖ' = ϖ'} (wke-ww θ) csn = refl
    wk-mem-eq Cx.h [] (x ∷ E') {ϖ = ϖ} {ϖ' = ϖ'} (wke-ww θ) csn = refl
    wk-mem-eq Cx.h (x ∷ E) [] {ϖ = ϖ} {ϖ' = ϖ'} (wke-ww θ) csn = refl
    wk-mem-eq Cx.h (x ∷ E) (x₁ ∷ E') {ϖ = ϖ} {ϖ' = ϖ'} (wke-ww θ) csn = refl
    wk-mem-eq (Cx.t i) ((B , e) ∷ E) ((B , e) ∷ E') {ϖ = ϖ} {ϖ' = ϖ'} (wke-cc θ) csn = wk-mem-eq i E E' θ csn
    wk-mem-eq (Cx.t i) [] [] {ϖ = ϖ} {ϖ' = ϖ'} (wke-ww θ) csn = refl
    wk-mem-eq (Cx.t {B = B} i) [] (x ∷ E') {ϖ = wkn-cons ϖ} {ϖ' = wkn-cons ϖ'} (wke-ww θ) csn = ql (wke-z-l θ) (lookup-metric (t {B = B} i) (x ∷ E') (wkn-cons ϖ') ≡ lookup-metric (t {B = B} i) [] (wkn-cons ϖ))
    wk-mem-eq (Cx.t {B = B} i) (x ∷ E) [] {ϖ = wkn-cons ϖ} {ϖ' = wkn-cons ϖ'} (wke-ww θ) csn = ql (wke-z-r θ) (lookup-metric (t {B = B} i) [] (wkn-cons ϖ') ≡ lookup-metric (t {B = B} i) (x ∷ E) (wkn-cons ϖ))
    wk-mem-eq (Cx.t i) (x ∷ E) (x₁ ∷ E') {ϖ = ϖ} {ϖ' = ϖ'} (wke-ww θ) csn = wk-mem-eq i (x ∷ E) (x₁ ∷ E') θ csn

    wk-val-eq :   (N : Val Γ Y) → (E E' : List (Σ[ X ∈ Ty ] TermMetric X)) → {ϖ : Wkn Γ E} → {ϖ' : Wkn Γ E'} → (θ : Wke ϖ ϖ') → (csn : List (ℕ × ℕ))
                → val-metric N E' ϖ' csn ≡ val-metric N E ϖ csn
    wk-val-eq (var i) E E' θ csn = cong (incr 2) (wk-mem-eq i E E' θ csn)
    wk-val-eq (lam W) E E' θ csn = cong (m-⇒ 2 (count-in-comp h W)) (wk-comp-eq W E E' (wke-ww θ) csn)
    wk-val-eq (pair N M) E E' θ csn = cong₂ (m-× 2) (wk-val-eq N E E' θ csn) (wk-val-eq M E E' θ csn)
    wk-val-eq (pm {A = A} {B = B} {C = C} N M) E E' {ϖ = ϖ} {ϖ' = ϖ'} θ csn rewrite wk-val-eq N E E' θ csn | wk-val-eq M E E' (wke-ww (wke-ww θ)) csn =
      cong (incr (suc (vx (val-metric N E ϖ csn) + ⟪ val-metric M E (wkn-cons (wkn-cons ϖ)) csn ⟫)))
           (wk-val-eq M
                      ((B , rhs (val-metric N E ϖ csn)) ∷ (A , lhs (val-metric N E ϖ csn)) ∷ E)
                      ((B , rhs (val-metric N E ϖ csn)) ∷ (A , lhs (val-metric N E ϖ csn)) ∷ E')
                      (wke-cc (wke-cc θ))
                      csn)
    wk-val-eq unit E E' θ csn = refl

    wk-comp-eq :   (W : Comp Γ Y) → (E E' : List (Σ[ X ∈ Ty ] TermMetric X)) → {ϖ : Wkn Γ E} → {ϖ' : Wkn Γ E'} → (θ : Wke ϖ ϖ') → (csn : List (ℕ × ℕ))
                 → comp-metric W E' ϖ' csn ≡ comp-metric W E ϖ csn
    wk-comp-eq (return M) E E' θ csn = cong (incr 2) (wk-val-eq M E E' θ csn)
    wk-comp-eq (pm {A = A} {B = B} {C = C} M W) E E' {ϖ = ϖ} {ϖ' = ϖ'} θ csn rewrite wk-val-eq M E E' θ csn | wk-comp-eq W E E' (wke-ww (wke-ww θ)) csn =
      cong (incr (suc (vx (val-metric M E ϖ csn) + ⟪ comp-metric W E (wkn-cons (wkn-cons ϖ)) csn ⟫)))
           (wk-comp-eq W
                       ((B , rhs (val-metric M E ϖ csn)) ∷ (A , lhs (val-metric M E ϖ csn)) ∷ E)
                       ((B , rhs (val-metric M E ϖ csn)) ∷ (A , lhs (val-metric M E ϖ csn)) ∷ E')
                       (wke-cc (wke-cc θ))
                       csn)
    wk-comp-eq (push {A = A} W₁ W₂) E E' {ϖ = ϖ} {ϖ' = ϖ'} θ csn
      rewrite
          wk-comp-eq W₁ E E' θ csn
        | wk-comp-eq W₂ ((A , comp-metric W₁ E ϖ csn) ∷ E) ((A , comp-metric W₁ E ϖ csn) ∷ E') (wke-cc θ) csn
        | wk-comp-eq W₁ E E' θ ((count-in-comp h W₂ , ⟪ comp-metric W₂ ((A , comp-metric W₁ E ϖ csn) ∷ E) (wkn-cong ϖ) csn ⟫) ∷ csn)
      =
        cong (incr (suc ⟪ comp-metric W₁ E ϖ ((count-in-comp h W₂ , ⟪ comp-metric W₂ ((A , comp-metric W₁ E ϖ csn) ∷ E) (wkn-cong ϖ) csn ⟫) ∷ csn) ⟫))
             (wk-comp-eq W₂ ((A , comp-metric W₁ E ϖ csn) ∷ E) ((A , comp-metric W₁ E ϖ csn) ∷ E) (wke-cc wke-id) csn)
    wk-comp-eq (app M N) E E' θ csn rewrite wk-val-eq M E E' θ csn | wk-val-eq N E E' θ csn = refl
    wk-comp-eq (var M) E E' θ csn rewrite wk-val-eq M E E' θ csn = refl
    wk-comp-eq (sub {A = A} W₁ W₂) E E' {ϖ = ϖ} {ϖ' = ϖ'} θ csn
      rewrite
          wk-comp-eq W₂ E E' θ csn
        | wk-comp-eq W₁
                     ((`V , m-V 0 ⟪ comp-metric W₂ E ϖ csn ⟫ csn) ∷ E)
                     ((`V , m-V 0 ⟪ comp-metric W₂ E ϖ csn ⟫ csn) ∷ E')
                     (wke-cc θ)
                     csn
      =
        refl

------------------------------------------------------------------------------------------------------

  mutual

    wk-val-count-eq : (π : Wk Γ Γ') → (i : Γ' ∋ Y) → (M : Val Γ' X) → count-in-val i M ≡ count-in-val (wk-mem π i) (wk-val π M)

    wk-val-count-eq wk-ε () M

    wk-val-count-eq (wk-cong π) Cx.h (var Cx.h) = refl
    wk-val-count-eq (wk-cong π) Cx.h (var (Cx.t i)) = refl

    wk-val-count-eq (wk-cong π) Cx.h (lam W) = wk-comp-count-eq (wk-cong (wk-cong π)) (t h) W
    wk-val-count-eq (wk-cong π) Cx.h (pair M₁ M₂) = cong₂ _+_ (wk-val-count-eq (wk-cong π) h M₁) (wk-val-count-eq (wk-cong π) h M₂)
    wk-val-count-eq (wk-cong π) Cx.h (pm M₁ M₂) = cong₂ _+_ (wk-val-count-eq (wk-cong π) h M₁) (wk-val-count-eq (wk-cong (wk-cong (wk-cong π))) (t (t h)) M₂)
    wk-val-count-eq (wk-cong π) Cx.h unit = refl

    wk-val-count-eq (wk-cong π) (Cx.t i) (var Cx.h) = refl
    wk-val-count-eq (wk-cong π) (Cx.t i) (var (Cx.t i₁)) = wk-val-count-eq π i (var i₁)

    wk-val-count-eq (wk-cong π) (Cx.t i) (lam W) = wk-comp-count-eq (wk-cong (wk-cong π)) (t (t i)) W
    wk-val-count-eq (wk-cong π) (Cx.t i) (pair M₁ M₂) = cong₂ _+_ (wk-val-count-eq (wk-cong π) (t i) M₁) (wk-val-count-eq (wk-cong π) (t i) M₂)
    wk-val-count-eq (wk-cong π) (Cx.t i) (pm M₁ M₂) = cong₂ _+_ (wk-val-count-eq (wk-cong π) (t i) M₁) (wk-val-count-eq (wk-cong (wk-cong (wk-cong π))) (t (t (t i))) M₂)
    wk-val-count-eq (wk-cong π) (Cx.t i) unit = refl

    wk-val-count-eq (wk-wk π) Cx.h (var Cx.h) = wk-val-count-eq π h (var h)
    wk-val-count-eq (wk-wk π) Cx.h (var (Cx.t i)) = wk-val-count-eq π h (var (t i))

    wk-val-count-eq (wk-wk π) Cx.h (lam W) = wk-comp-count-eq (wk-cong (wk-wk π)) (t h) W
    wk-val-count-eq (wk-wk π) Cx.h (pair M₁ M₂) = cong₂ _+_ (wk-val-count-eq (wk-wk π) h M₁) (wk-val-count-eq (wk-wk π) h M₂)
    wk-val-count-eq (wk-wk π) Cx.h (pm M₁ M₂) = cong₂ _+_ (wk-val-count-eq (wk-wk π) h M₁) (wk-val-count-eq (wk-cong (wk-cong (wk-wk π))) (t (t h)) M₂)
    wk-val-count-eq (wk-wk π) Cx.h unit = refl

    wk-val-count-eq (wk-wk π) (Cx.t i) (var Cx.h) = wk-val-count-eq π (t i) (var h)
    wk-val-count-eq (wk-wk π) (Cx.t i) (var (Cx.t i₁)) = wk-val-count-eq π (t i) (var (t i₁))

    wk-val-count-eq (wk-wk π) (Cx.t i) (lam W) = wk-comp-count-eq (wk-cong (wk-wk π)) (t (t i)) W
    wk-val-count-eq (wk-wk π) (Cx.t i) (pair M₁ M₂) = cong₂ _+_ (wk-val-count-eq (wk-wk π) (t i) M₁) (wk-val-count-eq (wk-wk π) (t i) M₂)
    wk-val-count-eq (wk-wk π) (Cx.t i) (pm M₁ M₂) = cong₂ _+_ (wk-val-count-eq (wk-wk π) (t i) M₁) (wk-val-count-eq (wk-cong (wk-cong (wk-wk π))) (t (t (t i))) M₂)
    wk-val-count-eq (wk-wk π) (Cx.t i) unit = refl

    wk-comp-count-eq : (π : Wk Γ Γ') → (i : Γ' ∋ Y) → (W : Comp Γ' X) → count-in-comp i W ≡ count-in-comp (wk-mem π i) (wk-comp π W)
    wk-comp-count-eq π i (return M) = wk-val-count-eq π i M
    wk-comp-count-eq π i (pm M W) = cong₂ _+_ (wk-val-count-eq π i M) (wk-comp-count-eq (wk-cong (wk-cong π)) (t (t i)) W)
    wk-comp-count-eq π i (push W₁ W₂) = cong₂ _+_ (wk-comp-count-eq π i W₁) (wk-comp-count-eq (wk-cong π) (t i) W₂)
    wk-comp-count-eq π i (app M₁ M₂) = cong₂ _+_ (wk-val-count-eq π i M₁) (wk-val-count-eq π i M₂)
    wk-comp-count-eq π i (var M) = wk-val-count-eq π i M
    wk-comp-count-eq π i (sub W₁ W₂) = cong₂ _+_ (wk-comp-count-eq (wk-cong π) (t i) W₁) (wk-comp-count-eq π i W₂)

  mutual

    wk-mem-pi : (i : Γ' ∋ Y) → (π : Wk Γ Γ') → (E : List (Σ[ X ∈ Ty ] TermMetric X)) → {ϖ : Wkn Γ' E} → (csn : List (ℕ × ℕ)) → (lookup-metric i E ϖ) ≡ (lookup-metric (wk-mem π i) E (wk-e π ϖ))
    wk-mem-pi Cx.h (wk-cong π) E {ϖ = wkn-cong ϖ} csn = refl
    wk-mem-pi Cx.h (wk-cong π) [] {ϖ = wkn-cons ϖ} csn = refl
    wk-mem-pi Cx.h (wk-cong π) (x ∷ E) {ϖ = wkn-cons ϖ} csn = refl
    wk-mem-pi Cx.h (wk-wk π) ((Y , e) ∷ E) {ϖ = wkn-cong ϖ} csn = wk-mem-pi h π ((Y , e) ∷ E) {ϖ = wkn-cong ϖ} csn
    wk-mem-pi Cx.h (wk-wk π) [] {ϖ = wkn-cons ϖ} csn = refl
    wk-mem-pi Cx.h (wk-wk π) (x ∷ E) {ϖ = wkn-cons ϖ} csn = wk-mem-pi Cx.h π (x ∷ E) {ϖ = wkn-cons ϖ} csn
    wk-mem-pi (Cx.t i) (wk-cong π) [] {ϖ = wkn-cons ϖ} csn = refl
    wk-mem-pi (Cx.t i) (wk-cong π) (x ∷ E) {ϖ = wkn-cong ϖ} csn = wk-mem-pi i π E {ϖ = ϖ} csn
    wk-mem-pi (Cx.t i) (wk-cong π) (x ∷ E) {ϖ = wkn-cons ϖ} csn = wk-mem-pi i π (x ∷ E) {ϖ = ϖ} csn
    wk-mem-pi (Cx.t i) (wk-wk π) E {ϖ = wkn-cong ϖ} csn = wk-mem-pi (t i) π ((_ , _) ∷ _) csn
    wk-mem-pi (Cx.t i) (wk-wk π) [] {ϖ = wkn-cons ϖ} csn = refl
    wk-mem-pi (Cx.t i) (wk-wk π) (x ∷ E) {ϖ = wkn-cons ϖ} csn = wk-mem-pi (t i) π (x ∷ E) csn

    wk-val-pi : (M : Val Γ' Y) → (π : Wk Γ Γ') → (E : List (Σ[ X ∈ Ty ] TermMetric X)) → {ϖ : Wkn Γ' E} → (csn : List (ℕ × ℕ)) → (val-metric M E ϖ csn) ≡ (val-metric (wk-val π M) E (wk-e π ϖ) csn)
    wk-val-pi (var i) π E {ϖ = ϖ} csn = cong (incr 2) (wk-mem-pi i π E csn)
    wk-val-pi (lam W) π E {ϖ = ϖ} csn = cong₂ (m-⇒ 2) (wk-comp-count-eq (wk-cong π) h W) (wk-comp-pi W (wk-cong π) E {ϖ = wkn-cons ϖ} csn)
    wk-val-pi (pair M N) π E {ϖ = ϖ} csn = cong₂ (m-× 2) (wk-val-pi M π E csn) (wk-val-pi N π E csn)
    wk-val-pi (pm {A = A} {B = B} {C = C} M N) π E {ϖ = ϖ} csn
      rewrite
          wk-val-pi M π E {ϖ = ϖ} csn
        | wk-val-pi N (wk-cong (wk-cong π)) E {ϖ = wkn-cons (wkn-cons ϖ)} csn
        | wk-val-pi N (wk-cong (wk-cong π)) ((B , rhs (val-metric (wk-val π M) E (wk-e π ϖ) csn)) ∷ (A , lhs (val-metric (wk-val π M) E (wk-e π ϖ) csn)) ∷ E) {ϖ = wkn-cong (wkn-cong ϖ)} csn = refl
    wk-val-pi unit π E {ϖ = ϖ} csn = refl

    wk-comp-pi : (W : Comp Γ' Y) → (π : Wk Γ Γ') → (E : List (Σ[ X ∈ Ty ] TermMetric X)) → {ϖ : Wkn Γ' E} → (csn : List (ℕ × ℕ)) → (comp-metric W E ϖ csn) ≡ (comp-metric (wk-comp π W) E (wk-e π ϖ) csn)
    wk-comp-pi (return M) π E {ϖ = ϖ} csn = cong (incr 2) (wk-val-pi M π E csn)
    wk-comp-pi (pm {A = A} {B = B} {C = C} M W) π E {ϖ = ϖ} csn
      rewrite
          wk-val-pi M π E {ϖ = ϖ} csn
        | wk-comp-pi W (wk-cong (wk-cong π)) E {ϖ = wkn-cons (wkn-cons ϖ)} csn
        | wk-comp-pi W (wk-cong (wk-cong π)) ((B , rhs (val-metric (wk-val π M) E (wk-e π ϖ) csn)) ∷ (A , lhs (val-metric (wk-val π M) E (wk-e π ϖ) csn)) ∷ E) {ϖ = wkn-cong (wkn-cong ϖ)} csn = refl
    wk-comp-pi (push {A = A} W₁ W₂) π E {ϖ = ϖ} csn
      rewrite
          wk-comp-pi W₁ π E {ϖ = ϖ} csn
        | wk-comp-pi W₂ (wk-cong π) ((A , comp-metric (wk-comp π W₁) E (wk-e π ϖ) csn) ∷ E) {ϖ = wkn-cong ϖ} csn
        | wk-comp-pi W₁ π E {ϖ = ϖ} ((count-in-comp h W₂ , ⟪ comp-metric (wk-comp (wk-cong π) W₂) ((A , comp-metric (wk-comp π W₁) E (wk-e π ϖ) csn) ∷ E) (wkn-cong (wk-e π ϖ)) csn ⟫) ∷ csn)
        | wk-comp-count-eq (wk-cong π) h W₂
        = refl
    wk-comp-pi (app M₁ M₂) π E {ϖ = ϖ} csn
      rewrite
          wk-val-pi M₁ π E {ϖ = ϖ} csn
        | wk-val-pi M₂ π E {ϖ = ϖ} csn
        = refl
    wk-comp-pi (var M) π E {ϖ = ϖ} csn
      rewrite
          wk-val-pi M π E {ϖ = ϖ} csn
        = refl
    wk-comp-pi (sub W₁ W₂) π E {ϖ = ϖ} csn
      rewrite
          wk-comp-pi W₂ π E {ϖ = ϖ} csn
        | wk-comp-pi W₁ (wk-cong π) ((`V , m-V 0 ⟪ comp-metric (wk-comp π W₂) E (wk-e π ϖ) csn ⟫ csn) ∷ E) {ϖ = wkn-cong ϖ} csn
        = refl

-------------------------------------------------------

  data _≤ᶜˢⁿ_ : List (ℕ × ℕ) → List (ℕ × ℕ) → Set where
   [c≤c] : {csn : List (ℕ × ℕ)} → csn ≤ᶜˢⁿ csn
   [s≤s] : {cnt : ℕ} {csn₁ csn₂ : List (ℕ × ℕ)} → n₁ ≤ n₂ → csn₁ ≤ᶜˢⁿ csn₂ → ((cnt , n₁) ∷ csn₁) ≤ᶜˢⁿ ((cnt , n₂) ∷ csn₂)

  data _≤ᴹ_ : TermMetric X → TermMetric X → Set where
    ≤-Unit : (n₁ ≤ n₂) → (m-Unit n₁) ≤ᴹ (m-Unit n₂)
    ≤-V    : {w₁ w₂ : ℕ} {csn₁ csn₂ : List (ℕ × ℕ)} → (m₁ ≤ m₂) → (w₁ ≤ w₂) → (csn₁ ≤ᶜˢⁿ csn₂) → (m-V m₁ w₁ csn₁) ≤ᴹ (m-V m₂ w₂ csn₂)
    ≤-⇒    : {cnt : ℕ} {nm₁ nm₂ : TermMetric Y} → (m₁ ≤ m₂) → (nm₁ ≤ᴹ nm₂) → (m-⇒ {X = X} m₁ cnt nm₁) ≤ᴹ (m-⇒ m₂ cnt nm₂)
    ≤-×    : {lhs₁ lhs₂ : TermMetric X} → {rhs₁ rhs₂ : TermMetric Y} → (n₁ ≤ n₂) → (lhs₁ ≤ᴹ lhs₂) → (rhs₁ ≤ᴹ rhs₂) → (m-× n₁ lhs₁ rhs₁) ≤ᴹ (m-× n₂ lhs₂ rhs₂)

  ≤ᶜˢⁿ-decr : {csn₁ csn₂ : List (ℕ × ℕ)} → (n₁ ≤ n₂) → csn₁ ≤ᶜˢⁿ csn₂ → csn-to-nat₀ n₁ csn₁ ≤ csn-to-nat₀ n₂ csn₂
  ≤ᶜˢⁿ-decr {n₁ = n₁} {n₂ = n₂} n₁≤n₂ ([c≤c] {csn = csn}) = csn-decr n₁≤n₂ csn
  ≤ᶜˢⁿ-decr {n₁ = n₁} {n₂ = n₂} n₁≤n₂ ([s≤s] n₃≤n₄ c₁≤c₂) =
    let
      m₁≤m₂ = +-≤-cong ≤-refl (*-≤-cong n₁≤n₂ n₃≤n₄)
    in
      +-≤-cong m₁≤m₂ (≤ᶜˢⁿ-decr m₁≤m₂ c₁≤c₂)

  ≤ᴹ-incr-drop : (n : ℕ) → (nm₁ nm₂ : TermMetric X) → ((incr n nm₁) ≤ᴹ (incr n nm₂)) → (nm₁ ≤ᴹ nm₂)
  ≤ᴹ-incr-drop {X = `Unit} n (m-Unit m₁) (m-Unit m₂) (≤-Unit n+m₁≤n+m₂) = ≤-Unit (+-≤-cong-rev-left n+m₁≤n+m₂)
  ≤ᴹ-incr-drop {X = X `× Y} n (m-× m₁ nm₁ nm₂) (m-× m₂ nm₃ nm₄) (≤-× n+m₁≤n+m₂ nm₁≤nm₃ nm₂≤nm₄) = ≤-× (+-≤-cong-rev-left n+m₁≤n+m₂) nm₁≤nm₃ nm₂≤nm₄
  ≤ᴹ-incr-drop {X = X `⇒ Y} n (m-⇒ m₁ cnt nm₁) (m-⇒ m₂ cnt nm₂) (≤-⇒ n+m₁≤n+m₂ nm₁≤nm₂) = ≤-⇒ (+-≤-cong-rev-left n+m₁≤n+m₂) nm₁≤nm₂
  ≤ᴹ-incr-drop {X = `V} n (m-V m₁ w₁ csn₁) (m-V m₂ w₂ csn₂) (≤-V n+m₁≤n+m₂ w₁≤w₂ c₁≤c₂) = ≤-V (+-≤-cong-rev-left n+m₁≤n+m₂) w₁≤w₂ c₁≤c₂

  ≤ᴹ-incr-cong : (n₁≤n₂ : n₁ ≤ n₂) → {nm₁ nm₂ : TermMetric X} → (nm₁ ≤ᴹ nm₂) → ((incr n₁ nm₁) ≤ᴹ (incr n₂ nm₂))
  ≤ᴹ-incr-cong n₁≤n₂ (≤-Unit m₁≤m₂) = ≤-Unit (+-≤-cong n₁≤n₂ m₁≤m₂)
  ≤ᴹ-incr-cong n₁≤n₂ (≤-V m₁≤m₂ w₁≤w₂ c₁≤c₂) = ≤-V (+-≤-cong n₁≤n₂ m₁≤m₂) w₁≤w₂ c₁≤c₂
  ≤ᴹ-incr-cong n₁≤n₂ (≤-⇒ m₁≤m₂ nm₁≤nm₂) = ≤-⇒ (+-≤-cong n₁≤n₂ m₁≤m₂) nm₁≤nm₂
  ≤ᴹ-incr-cong n₁≤n₂ (≤-× m₁≤m₂ nm₁≤nm₃ nm₂≤nm₄) = ≤-× (+-≤-cong n₁≤n₂ m₁≤m₂) nm₁≤nm₃ nm₂≤nm₄

  ≤ᴹ-refl : {nm : TermMetric X} → nm ≤ᴹ nm
  ≤ᴹ-refl {nm = m-Unit m} = ≤-Unit ≤-refl
  ≤ᴹ-refl {nm = m-V m n csn} = ≤-V  ≤-refl ≤-refl [c≤c]
  ≤ᴹ-refl {nm = m-⇒ m cnt nm} = ≤-⇒ ≤-refl ≤ᴹ-refl
  ≤ᴹ-refl {nm = m-× m nm nm₁} = ≤-× ≤-refl ≤ᴹ-refl ≤ᴹ-refl

  ≤ᴹ-p1 : {nm₁ nm₂ : TermMetric (X `⇒ Y)} → (nm₁ ≤ᴹ nm₂) → (p1 nm₁) ≤ (p1 nm₂)
  ≤ᴹ-p1 (≤-⇒ n₁≤n₂ nm₁≤nm₂) = n₁≤n₂

  ≡-p2-incr : (n : ℕ) → (nm : TermMetric (X `⇒ Y)) → p2 (incr n nm) ≡ p2 nm
  ≡-p2-incr n (m-⇒ m cnt nm) = refl

  {-# REWRITE ≡-p2-incr #-}

  ≤ᴹ-p3 : {nm₁ nm₂ : TermMetric (X `⇒ Y)} → (nm₁ ≤ᴹ nm₂) → (p3 nm₁) ≤ᴹ (p3 nm₂)
  ≤ᴹ-p3 (≤-⇒ n₁≤n₂ nm₁≤nm₂) = nm₁≤nm₂

  ≤ᴹ-lhs : {nm₁ nm₂ : TermMetric (X `× Y)} → (nm₁ ≤ᴹ nm₂) → (lhs nm₁) ≤ᴹ (lhs nm₂)
  ≤ᴹ-lhs (≤-× x nm₁≤nm₃ nm₂≤nm₄) = nm₁≤nm₃

  ≤ᴹ-rhs : {nm₁ nm₂ : TermMetric (X `× Y)} → (nm₁ ≤ᴹ nm₂) → (rhs nm₁) ≤ᴹ (rhs nm₂)
  ≤ᴹ-rhs (≤-× x nm₁≤nm₃ nm₂≤nm₄) = nm₂≤nm₄

  ≤ᴹ-vx : {nm₁ nm₂ : TermMetric (X `× Y)} → (nm₁ ≤ᴹ nm₂) → (vx nm₁) ≤ (vx nm₂)
  ≤ᴹ-vx (≤-× n₁≤n₂ nm₁≤nm₂ nm₁≤nm₃) = n₁≤n₂

  ≤ᴹ⇒≤ : {nm₁ nm₂ : TermMetric X} → (nm₁ ≤ᴹ nm₂) → (⟪ nm₁ ⟫ ≤ ⟪ nm₂ ⟫)
  ≤ᴹ⇒≤ (≤-Unit n₁≤n₂) = n₁≤n₂
  ≤ᴹ⇒≤ (≤-V n₁≤n₂ w₁≤w₂ c₁≤c₂) = +-≤-cong (+-≤-cong n₁≤n₂ w₁≤w₂) (≤ᶜˢⁿ-decr w₁≤w₂ c₁≤c₂)
  ≤ᴹ⇒≤ (≤-⇒ n₁≤n₂ nm₁≤nm₂) = +-≤-cong n₁≤n₂ (≤ᴹ⇒≤ nm₁≤nm₂)
  ≤ᴹ⇒≤ (≤-× n₁≤n₂ nm₁≤nm₃ nm₂≤nm₄) = +-≤-cong (+-≤-cong n₁≤n₂ (≤ᴹ⇒≤ nm₁≤nm₃)) (≤ᴹ⇒≤ nm₂≤nm₄)

  data _≤ᴱ_       : (E₁ E₂ : List (Σ[ X ∈ Ty ] TermMetric X)) → Set where
    ≤ᴱ-id       : {E : List (Σ[ X ∈ Ty ] TermMetric X)} → E ≤ᴱ E
    ≤ᴱ-cong     : {E₁ E₂ : List (Σ[ X ∈ Ty ] TermMetric X)} → {nm₁ nm₂ : TermMetric X} → (E₁≤E₂ : E₁ ≤ᴱ E₂) → (nm₁≤nm₂ : nm₁ ≤ᴹ nm₂) → ((X , nm₁) ∷ E₁) ≤ᴱ ((X , nm₂) ∷ E₂)

  -- maybe get rid of Wke
  data _≤ʷ_ : {E₁ E₂ : List (Σ[ X ∈ Ty ] TermMetric X)} → (ϖ₁ : Wkn Γ E₁) → (ϖ₂ : Wkn Γ E₂) → Set where
   ≤ʷ-nil : wkn-nil ≤ʷ wkn-nil
   ≤ʷ-cc  : {E₁ E₂ : List (Σ[ X ∈ Ty ] TermMetric X)} → {ϖ₁ : Wkn Γ E₁} → {ϖ₂ : Wkn Γ E₂} → (θ : ϖ₁ ≤ʷ ϖ₂) → {nm₁ nm₂ : TermMetric Y} → (nm₁≤nm₂ : nm₁ ≤ᴹ nm₂) → (wkn-cong {Y = Y} {e = nm₁} ϖ₁) ≤ʷ (wkn-cong {Y = Y} {e = nm₂} ϖ₂)
   ≤ʷ-ww  : {E₁ E₂ : List (Σ[ X ∈ Ty ] TermMetric X)} → {ϖ₁ : Wkn Γ E₁} → {ϖ₂ : Wkn Γ E₂} → (θ : ϖ₁ ≤ʷ ϖ₂) → (wkn-cons {Y = Y} ϖ₁) ≤ʷ (wkn-cons {Y = Y} ϖ₂)

  ≤ʷ-z-l : {e : (Σ[ X ∈ Ty ] TermMetric X)} {E : List (Σ[ X ∈ Ty ] TermMetric X)} {ϖ₁ : Wkn Γ []} {ϖ₂ : Wkn Γ (e ∷ E)} → ϖ₁ ≤ʷ ϖ₂ → ⊥
  ≤ʷ-z-l (≤ʷ-ww θ) = ≤ʷ-z-l θ

  ≤ʷ-z-r : {e : (Σ[ X ∈ Ty ] TermMetric X)} {E : List (Σ[ X ∈ Ty ] TermMetric X)} {ϖ₁ : Wkn Γ (e ∷ E)} {ϖ₂ : Wkn Γ []} → ϖ₁ ≤ʷ ϖ₂ → ⊥
  ≤ʷ-z-r (≤ʷ-ww θ) = ≤ʷ-z-r θ

----------------------------------------------------------------

  mutual

    p2-mem-eq : {E₁ E₂ : List (Σ[ X ∈ Ty ] TermMetric X)} → (i : Γ ∋ (X `⇒ Y)) → (ϖ₁ : Wkn Γ E₁) → (ϖ₂ : Wkn Γ E₂) → (θ : ϖ₁ ≤ʷ ϖ₂) → p2 (lookup-metric i E₁ ϖ₁) ≡ p2 (lookup-metric i E₂ ϖ₂)

    p2-mem-eq {E₁ = x₁ ∷ E₁} {E₂ = x₂ ∷ E₂} Cx.h (wkn-cong ϖ₁) (wkn-cong ϖ₂) (≤ʷ-cc θ (≤-⇒ x nm₁≤nm₂)) = refl
    p2-mem-eq {E₁ = []} {E₂ = []} Cx.h (wkn-cons ϖ₁) (wkn-cons ϖ₂) θ = refl
    p2-mem-eq {E₁ = []} {E₂ = x ∷ E₂} Cx.h (wkn-cons ϖ₁) (wkn-cons ϖ₂) θ = refl
    p2-mem-eq {E₁ = x ∷ E₁} {E₂ = []} Cx.h (wkn-cons ϖ₁) (wkn-cons ϖ₂) θ = refl
    p2-mem-eq {E₁ = x ∷ E₁} {E₂ = x₁ ∷ E₂} Cx.h (wkn-cons ϖ₁) (wkn-cons ϖ₂) θ = refl
    p2-mem-eq {E₁ = _ ∷ E₁} {E₂ = _ ∷ E₂} (Cx.t i) (wkn-cong ϖ₁) (wkn-cong ϖ₂) (≤ʷ-cc θ nm₁≤nm₂) = p2-mem-eq {E₁ = E₁} {E₂ = E₂} i ϖ₁ ϖ₂ θ

    p2-mem-eq {E₁ = []} {E₂ = []} (Cx.t i) (wkn-cons ϖ₁) (wkn-cons ϖ₂) (≤ʷ-ww θ) = refl
    p2-mem-eq {X = X} {Y = Y} {E₁ = []} {E₂ = (B , e) ∷ E₂} (Cx.t i) (wkn-cons ϖ₁) (wkn-cons ϖ₂) (≤ʷ-ww θ) = ql (≤ʷ-z-l θ) (p2 (lookup-metric (t {A = X `⇒ Y} {B = R₀} i) [] (wkn-cons ϖ₁)) ≡ p2 (lookup-metric (t {A = X `⇒ Y} {B = R₀} i) ((B , e) ∷ E₂) (wkn-cons ϖ₂)))
    p2-mem-eq {E₁ = x ∷ E₁} {E₂ = []} (Cx.t i) (wkn-cons ϖ₁) (wkn-cons ϖ₂) (≤ʷ-ww θ) = ql (≤ʷ-z-r θ) (p2 (lookup-metric (t {B = R₀} i) (x ∷ E₁) (wkn-cons ϖ₁)) ≡ p2 (lookup-metric (t {B = R₀} i) [] (wkn-cons ϖ₂)))
    p2-mem-eq {E₁ = x ∷ E₁} {E₂ = x₁ ∷ E₂} (Cx.t i) (wkn-cons ϖ₁) (wkn-cons ϖ₂) (≤ʷ-ww θ) = p2-mem-eq i ϖ₁ ϖ₂ θ


    p2-val-eq : {E₁ E₂ : List (Σ[ X ∈ Ty ] TermMetric X)} → (M : Val Γ (X `⇒ Y)) → (E₁≤E₂ : E₁ ≤ᴱ E₂) → (ϖ₁ : Wkn Γ E₁) → (ϖ₂ : Wkn Γ E₂) → (θ : ϖ₁ ≤ʷ ϖ₂) → (csn₁ csn₂ : List (ℕ × ℕ)) → (csn₁ ≤ᶜˢⁿ csn₂) → p2 (val-metric M E₁ ϖ₁ csn₁) ≡ p2 (val-metric M E₂ ϖ₂ csn₂)
    p2-val-eq (var i) E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂ = p2-mem-eq i ϖ₁ ϖ₂ θ
    p2-val-eq (lam W) E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂ = refl
    p2-val-eq {E₁ = E₁} {E₂ = E₂} (pm M N) E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂ =
      let
        a1 = val-csn-le M E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂
      in
      p2-val-eq N (≤ᴱ-cong (≤ᴱ-cong E₁≤E₂ (≤ᴹ-lhs a1)) (≤ᴹ-rhs a1)) (wkn-cong (wkn-cong ϖ₁)) (wkn-cong (wkn-cong ϖ₂)) (≤ʷ-cc (≤ʷ-cc θ (≤ᴹ-lhs a1)) (≤ᴹ-rhs a1)) csn₁ csn₂ c₁≤c₂


    mem-csn-le : (i : Γ ∋ X) → (E₁ E₂ : List (Σ[ X ∈ Ty ] TermMetric X)) → (E₁≤E₂ : E₁ ≤ᴱ E₂) → (ϖ₁ : Wkn Γ E₁) → (ϖ₂ : Wkn Γ E₂) → (θ : ϖ₁ ≤ʷ ϖ₂) →
                 (lookup-metric i E₁ ϖ₁) ≤ᴹ (lookup-metric i E₂ ϖ₂)

    mem-csn-le Cx.h E₁ E₂ ≤ᴱ-id ϖ₁ ϖ₂ (≤ʷ-cc θ nm₁≤nm₂) = ≤ᴹ-refl
    mem-csn-le Cx.h [] [] ≤ᴱ-id (wkn-cons ϖ₁) (wkn-cons ϖ₂) (≤ʷ-ww θ) = ≤ᴹ-refl
    mem-csn-le Cx.h (x ∷ E₁) (x ∷ E₂) ≤ᴱ-id (wkn-cons ϖ₁) (wkn-cons ϖ₂) (≤ʷ-ww θ) = ≤ᴹ-refl
    mem-csn-le Cx.h ((X , nm₁) ∷ E₁) ((X , nm₂) ∷ E₂) (≤ᴱ-cong E₁≤E₂ nm₁≤nm₂) (wkn-cong ϖ₁) (wkn-cong ϖ₂) (≤ʷ-cc θ nm₁≤nm₃) = nm₁≤nm₂
    mem-csn-le Cx.h ((X , nm₁) ∷ E₁) ((X , nm₂) ∷ E₂) (≤ᴱ-cong E₁≤E₂ nm₁≤nm₂) (wkn-cong ϖ₁) (wkn-cons ϖ₂) ()
    mem-csn-le Cx.h ((X , nm₁) ∷ E₁) ((X , nm₂) ∷ E₂) (≤ᴱ-cong E₁≤E₂ nm₁≤nm₂) (wkn-cons ϖ₁) (wkn-cong ϖ₂) ()
    mem-csn-le Cx.h ((X , nm₁) ∷ E₁) ((X , nm₂) ∷ E₂) (≤ᴱ-cong E₁≤E₂ nm₁≤nm₂) (wkn-cons ϖ₁) (wkn-cons ϖ₂) (≤ʷ-ww θ) = ≤ᴹ-refl
    mem-csn-le (Cx.t i) [] [] ≤ᴱ-id (wkn-cons ϖ₁) (wkn-cons ϖ₂) (≤ʷ-ww θ) = ≤ᴹ-refl
    mem-csn-le (Cx.t i) ((X , nm₁) ∷ E₁) ((X , nm₂) ∷ E₂) ≤ᴱ-id (wkn-cong ϖ₁) (wkn-cong ϖ₂) (≤ʷ-cc θ nm₁≤nm₂) = mem-csn-le i E₁ E₂ ≤ᴱ-id ϖ₁ ϖ₂ θ
    mem-csn-le (Cx.t i) (x ∷ E₁) E₂ ≤ᴱ-id (wkn-cong ϖ₁) (wkn-cons ϖ₂) ()
    mem-csn-le (Cx.t i) (x ∷ E₁) E₂ ≤ᴱ-id (wkn-cons ϖ₁) (wkn-cong ϖ₂) ()
    mem-csn-le (Cx.t i) ((X , nm₁) ∷ E₁) ((X , nm₂) ∷ E₂) ≤ᴱ-id (wkn-cons ϖ₁) (wkn-cons ϖ₂) (≤ʷ-ww θ) = mem-csn-le i ((X , nm₁) ∷ E₁) ((X , nm₂) ∷ E₂) ≤ᴱ-id ϖ₁ ϖ₂ θ
    mem-csn-le (Cx.t i) ((X , nm₁) ∷ E₁) ((X , nm₂) ∷ E₂) (≤ᴱ-cong E₁≤E₂ nm₁≤nm₂) (wkn-cong ϖ₁) (wkn-cong ϖ₂) (≤ʷ-cc θ nm₁≤nm₃) = mem-csn-le i E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ
    mem-csn-le (Cx.t i) ((X , nm₁) ∷ E₁) ((X , nm₂) ∷ E₂) (≤ᴱ-cong E₁≤E₂ nm₁≤nm₂) (wkn-cong ϖ₁) (wkn-cons ϖ₂) ()
    mem-csn-le (Cx.t i) ((X , nm₁) ∷ E₁) ((X , nm₂) ∷ E₂) (≤ᴱ-cong E₁≤E₂ nm₁≤nm₂) (wkn-cons ϖ₁) (wkn-cong ϖ₂) ()
    mem-csn-le (Cx.t i) ((X , nm₁) ∷ E₁) ((X , nm₂) ∷ E₂) (≤ᴱ-cong E₁≤E₂ nm₁≤nm₂) (wkn-cons ϖ₁) (wkn-cons ϖ₂) (≤ʷ-ww θ) = mem-csn-le i ((X , nm₁) ∷ E₁) ((X , nm₂) ∷ E₂) (≤ᴱ-cong E₁≤E₂ nm₁≤nm₂) ϖ₁ ϖ₂ θ


    val-csn-le : (M : Val Γ X) → (E₁ E₂ : List (Σ[ X ∈ Ty ] TermMetric X)) → (E₁≤E₂ : E₁ ≤ᴱ E₂) → (ϖ₁ : Wkn Γ E₁) → (ϖ₂ : Wkn Γ E₂) → (θ : ϖ₁ ≤ʷ ϖ₂) → (csn₁ csn₂ : List (ℕ × ℕ)) → (csn₁ ≤ᶜˢⁿ csn₂) →
                 (val-metric M E₁ ϖ₁ csn₁) ≤ᴹ (val-metric M E₂ ϖ₂ csn₂)

    val-csn-le (var i) E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂ = ≤ᴹ-incr-cong (≤-refl {n = 2}) (mem-csn-le i E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ)
    val-csn-le (lam W) E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂ = ≤-⇒ (≤-refl {n = 2}) ( comp-csn-le W E₁ E₂ E₁≤E₂ (wkn-cons ϖ₁) (wkn-cons ϖ₂) (≤ʷ-ww θ) csn₁ csn₂ c₁≤c₂)
    val-csn-le (pair M₁ M₂) E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂ = ≤-× ≤-refl (val-csn-le M₁ E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂) (val-csn-le M₂ E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂)
    val-csn-le (pm {A = A} {B = B} {C = C} M N) E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂ =
      let
        a1 = val-csn-le M E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂
        a2 = val-csn-le N E₁ E₂ E₁≤E₂ (wkn-cons (wkn-cons ϖ₁)) (wkn-cons (wkn-cons ϖ₂)) (≤ʷ-ww (≤ʷ-ww θ)) csn₁ csn₂ c₁≤c₂
        a3 = val-csn-le
               N
               ((B , rhs (val-metric M E₁ ϖ₁ csn₁)) ∷ (A , lhs (val-metric M E₁ ϖ₁ csn₁)) ∷ E₁)
               ((B , rhs (val-metric M E₂ ϖ₂ csn₂)) ∷ (A , lhs (val-metric M E₂ ϖ₂ csn₂)) ∷ E₂)
               (≤ᴱ-cong (≤ᴱ-cong E₁≤E₂ (≤ᴹ-lhs a1)) (≤ᴹ-rhs a1))
               (wkn-cong (wkn-cong ϖ₁))
               (wkn-cong (wkn-cong ϖ₂))
               (≤ʷ-cc (≤ʷ-cc θ (≤ᴹ-lhs a1)) (≤ᴹ-rhs a1))
               csn₁ csn₂ c₁≤c₂
      in
      ≤ᴹ-incr-cong (s≤s (+-≤-cong (≤ᴹ-vx a1) (≤ᴹ⇒≤ a2))) a3
    val-csn-le unit E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂ = ≤ᴹ-refl


    comp-csn-le : (W : Comp Γ X) → (E₁ E₂ : List (Σ[ X ∈ Ty ] TermMetric X)) → (E₁≤E₂ : E₁ ≤ᴱ E₂) → (ϖ₁ : Wkn Γ E₁) → (ϖ₂ : Wkn Γ E₂) → (θ : ϖ₁ ≤ʷ ϖ₂) → (csn₁ csn₂ : List (ℕ × ℕ)) → (csn₁ ≤ᶜˢⁿ csn₂) →
                 (comp-metric W E₁ ϖ₁ csn₁) ≤ᴹ (comp-metric W E₂ ϖ₂ csn₂)

    comp-csn-le (return M) E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂ = ≤ᴹ-incr-cong (≤-refl {n = 2}) (val-csn-le M E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂)
    comp-csn-le (pm {A = A} {B = B} {C = C} M W) E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂ =
      let
        a1 = val-csn-le M E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂
        a2 = comp-csn-le W E₁ E₂ E₁≤E₂ (wkn-cons (wkn-cons ϖ₁)) (wkn-cons (wkn-cons ϖ₂)) (≤ʷ-ww (≤ʷ-ww θ)) csn₁ csn₂ c₁≤c₂
        a3 = comp-csn-le
               W
               ((B , rhs (val-metric M E₁ ϖ₁ csn₁)) ∷ (A , lhs (val-metric M E₁ ϖ₁ csn₁)) ∷ E₁)
               ((B , rhs (val-metric M E₂ ϖ₂ csn₂)) ∷ (A , lhs (val-metric M E₂ ϖ₂ csn₂)) ∷ E₂)
               (≤ᴱ-cong (≤ᴱ-cong E₁≤E₂ (≤ᴹ-lhs a1)) (≤ᴹ-rhs a1))
               (wkn-cong (wkn-cong ϖ₁))
               (wkn-cong (wkn-cong ϖ₂))
               (≤ʷ-cc (≤ʷ-cc θ (≤ᴹ-lhs a1)) (≤ᴹ-rhs a1))
               csn₁ csn₂ c₁≤c₂
      in
      ≤ᴹ-incr-cong (s≤s (+-≤-cong (≤ᴹ-vx a1) (≤ᴹ⇒≤ a2))) a3
    comp-csn-le (push {A = A} W₁ W₂) E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂ =
      let
        a1 = comp-csn-le W₁ E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂
        a2 = comp-csn-le W₂
                 ((A , comp-metric W₁ E₁ ϖ₁ csn₁) ∷ E₁)
                 ((A , comp-metric W₁ E₂ ϖ₂ csn₂) ∷ E₂)
                 (≤ᴱ-cong E₁≤E₂ a1)
                 (wkn-cong ϖ₁)
                 (wkn-cong ϖ₂)
                 (≤ʷ-cc θ a1)
                 csn₁ csn₂ c₁≤c₂
        c1 = [s≤s] {cnt = count-in-comp h W₂} (≤ᴹ⇒≤ a2) c₁≤c₂
        d1 = comp-csn-le W₁ E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ
               ((count-in-comp h W₂ , ⟪ comp-metric W₂ ((A , comp-metric W₁ E₁ ϖ₁ csn₁) ∷ E₁) (wkn-cong ϖ₁) csn₁ ⟫) ∷ csn₁)
               ((count-in-comp h W₂ , ⟪ comp-metric W₂ ((A , comp-metric W₁ E₂ ϖ₂ csn₂) ∷ E₂) (wkn-cong ϖ₂) csn₂ ⟫) ∷ csn₂)
               c1
      in
      ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ d1)) a2
    comp-csn-le (app M N) E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂
      rewrite
        p2-val-eq M E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂
      =
      let
        a1 = val-csn-le M E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂
        a2 = val-csn-le N E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂
        b1 = ≤ᴹ-p1 a1
        c1 = ≤ᴹ-p3 a1
        d1 = s≤s (s≤s (+-≤-cong (b1) (+-≤-cong (≤ᴹ⇒≤ a2) (*-≤-cong (≤-refl {n = p2 (val-metric M E₂ ϖ₂ csn₂)}) (≤ᴹ⇒≤ a2)))))
      in
      ≤ᴹ-incr-cong d1 c1
    comp-csn-le (var M) E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂ = ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ (val-csn-le M E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂))) (≤ᴹ-refl {nm = zero-metric})
    comp-csn-le (sub W₁ W₂) E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂ =
      let
        a1 = comp-csn-le W₂ E₁ E₂ E₁≤E₂ ϖ₁ ϖ₂ θ csn₁ csn₂ c₁≤c₂
        a2 = comp-csn-le
               W₁
               ((`V , m-V 0 ⟪ comp-metric W₂ E₁ ϖ₁ csn₁ ⟫ csn₁) ∷ E₁)
               ((`V , m-V 0 ⟪ comp-metric W₂ E₂ ϖ₂ csn₂ ⟫ csn₂) ∷ E₂)
               (≤ᴱ-cong E₁≤E₂ (≤-V z≤n (≤ᴹ⇒≤ a1) c₁≤c₂))
               (wkn-cong ϖ₁)
               (wkn-cong ϖ₂)
               (≤ʷ-cc θ (≤-V z≤n (≤ᴹ⇒≤ a1) c₁≤c₂))
               csn₁
               csn₂
               c₁≤c₂
      in
      ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ a1)) a2


-------------------------------------------------------
-------------------------------------------------------
-------------------------------------------------------
{-

  return-val-lemma : (M₁ : Val (Γ ∙ X) Y) → (M : V̲a̲l̲ Γ X) → (γ : Env Γ) → (csn : List (ℕ × ℕ)) → ⟪ val-metric (wk-val (wk-cong wk-id) M₁) ((X , v̲a̲l̲-metric M (proj₁ (env-metric γ csn)) (proj₂ (env-metric γ csn)) csn) ∷ (proj₁ (env-metric γ csn))) (wkn-cong (proj₂ (env-metric γ csn))) csn ⟫ ≤ ⟪ val-metric M₁ (proj₁ (env-metric γ csn)) (wkn-cons (proj₂ (env-metric γ csn))) csn ⟫ + (count-in-val h M₁ + ⟪ v̲a̲l̲-metric M (proj₁ (env-metric γ ((⟪ val-metric M₁ (proj₁ (env-metric γ csn)) (wkn-cons (proj₂ (env-metric γ csn))) csn ⟫ , count-in-val h M₁) ∷ csn))) (proj₂ (env-metric γ ((⟪ val-metric M₁ (proj₁ (env-metric γ csn)) (wkn-cons (proj₂ (env-metric γ csn))) csn ⟫ , count-in-val h M₁) ∷ csn))) ((⟪ val-metric M₁ (proj₁ (env-metric γ csn)) (wkn-cons (proj₂ (env-metric γ csn))) csn ⟫ , count-in-val h M₁) ∷ csn) ⟫ * count-in-val h M₁)
  return-val-lemma M₁ M γ csn = {!!}

  return-comp-lemma : (W : Comp (Γ ∙ X) Y) → (M : V̲a̲l̲ Γ X) → (γ : Env Γ) → (csn : List (ℕ × ℕ)) → ⟪ comp-metric (wk-comp (wk-cong wk-id) W) ((X , v̲a̲l̲-metric M (proj₁ (env-metric γ csn)) (proj₂ (env-metric γ csn)) csn) ∷ (proj₁ (env-metric γ csn))) (wkn-cong (proj₂ (env-metric γ csn))) csn ⟫ ≤ ⟪ comp-metric W (proj₁ (env-metric γ csn)) (wkn-cons (proj₂ (env-metric γ csn))) csn ⟫ + (count-in-comp h W + ⟪ v̲a̲l̲-metric M (proj₁ (env-metric γ ((⟪ comp-metric W (proj₁ (env-metric γ csn)) (wkn-cons (proj₂ (env-metric γ csn))) csn ⟫ , count-in-comp h W) ∷ csn))) (proj₂ (env-metric γ ((⟪ comp-metric W (proj₁ (env-metric γ csn)) (wkn-cons (proj₂ (env-metric γ csn))) csn ⟫ , count-in-comp h W) ∷ csn))) ((⟪ comp-metric W (proj₁ (env-metric γ csn)) (wkn-cons (proj₂ (env-metric γ csn))) csn ⟫ , count-in-comp h W) ∷ csn) ⟫ * count-in-comp h W)

  return-comp-lemma (return M₁) M γ csn =
    let
      a1 = return-val-lemma M₁ M γ csn
    in
    {!!}
  return-comp-lemma (pm M₁ W) M γ csn = {!!}
  return-comp-lemma (push W₁ W₂) M γ csn = {!!}
  return-comp-lemma (app M₁ M₂) M γ csn = {!!}
  return-comp-lemma (var M₁) M γ csn = {!!}
  return-comp-lemma (sub W₁ W₂) M γ csn = {!!}

{-

Goal: 2+ ⟪val-metric (wk-val (wk-cong wk-id) M₁) ((X , v̲a̲l̲-metric M (proj₁ (env-metric γ csn)) (proj₂ (env-metric γ csn)) csn) ∷ proj₁ (env-metric γ csn)) (wkn-cong (proj₂ (env-metric γ csn))) csn⟫ ≤ 2+ (⟪val-metric M₁ (proj₁ (env-metric γ csn)) (wkn-cons (proj₂ (env-metric γ csn))) csn⟫ + (count-in-val h M₁ + ⟪v̲a̲l̲-metric M (proj₁ (env-metric γ ((2+ ⟪val-metric M₁ (proj₁ (env-metric γ csn)) (wkn-cons (proj₂ (env-metric γ csn))) csn⟫ , count-in-val h M₁) ∷ csn))) (proj₂ (env-metric γ ((2+ ⟪val-metric M₁ (proj₁ (env-metric γ csn)) (wkn-cons (proj₂ (env-metric γ csn))) csn⟫ , count-in-val h M₁) ∷ csn))) ((2+ ⟪val-metric M₁ (proj₁ (env-metric γ csn)) (wkn-cons (proj₂ (env-metric γ csn))) csn⟫ , count-in-val h M₁) ∷ csn)⟫ * count-in-val h M₁))
a1  :    ⟪val-metric (wk-val (wk-cong wk-id) M₁) ((X , v̲a̲l̲-metric M (proj₁ (env-metric γ csn)) (proj₂ (env-metric γ csn)) csn) ∷ proj₁ (env-metric γ csn)) (wkn-cong (proj₂ (env-metric γ csn))) csn⟫ ≤     ⟪val-metric M₁ (proj₁ (env-metric γ csn)) (wkn-cons (proj₂ (env-metric γ csn))) csn⟫ + (count-in-val h M₁ + ⟪v̲a̲l̲-metric M (proj₁ (env-metric γ ((   ⟪val-metric M₁ (proj₁ (env-metric γ csn)) (wkn-cons (proj₂ (env-metric γ csn))) csn⟫ , count-in-val h M₁) ∷ csn))) (proj₂ (env-metric γ ((   ⟪val-metric M₁ (proj₁ (env-metric γ csn)) (wkn-cons (proj₂ (env-metric γ csn))) csn⟫ , count-in-val h M₁) ∷ csn))) ((   ⟪val-metric M₁ (proj₁ (env-metric γ csn)) (wkn-cons (proj₂ (env-metric γ csn))) csn⟫ , count-in-val h M₁) ∷ csn)⟫ * count-in-val h M₁)

⟪v̲a̲l̲-metric M (proj₁ (env-metric γ ((2+ m , cnt) ∷ csn))) (proj₂ (env-metric γ ((2+ m , cnt) ∷ csn))) ((2+ m , cnt) ∷ csn)⟫
⟪v̲a̲l̲-metric M (proj₁ (env-metric γ ((   m , cnt) ∷ csn))) (proj₂ (env-metric γ ((   m , cnt) ∷ csn))) ((   m , cnt) ∷ csn)⟫

-}

-------------------------------------------------------

  val-metric-decreasing : {Q₁ : ValState X} → {Q₂ : ValState X} → (Q₁→ᶜQ₂ : Q₁ ↠ᵛ Q₂) → (m : ℕ) → (csn : List (ℕ × ℕ)) → (suc (valstate-metric Q₂ m csn) ≤ (valstate-metric Q₁ m csn))
  val-metric-decreasing = {!!}


  comp-metric-decreasing : {Q₁ : CompState} → {Q₂ : CompState} → (Q₁→ᶜQ₂ : Q₁ →ᶜ Q₂) → (suc (compstate-metric Q₂) ≤ (compstate-metric Q₁))
  comp-metric-decreasing (∘return {M = M} {γ = γ} {π = π} {M' = M'} {γ' = γ'} {cs = cs} M→M') with val-metric-decreasing (M→M') 1 (cs-to-csn cs)
  ... | s≤s x =
    let
      a1 = ⟪ v̲a̲l̲-metric M' (proj₁ (env-metric γ' (cs-to-csn cs))) (proj₂ (env-metric γ' (cs-to-csn cs))) (cs-to-csn cs) ⟫
      a2 = ⟪ val-metric (wk-val π M) (proj₁ (env-metric γ (cs-to-csn cs))) (proj₂ (env-metric γ (cs-to-csn cs))) (cs-to-csn cs) ⟫
    in
      s≤s (s≤s (≤-trans (n≤sn {n = a1 + csn-to-nat₀ (suc a1) (cs-to-csn cs)}) (≤-trans x (+-≤-cong (≤-refl {n = a2}) (csn-decr (n≤sn {n = suc a2}) (cs-to-csn cs))))))
  comp-metric-decreasing (∙return {X = X} {M = M} {γ = γ} {N = N} {γ' = γ'} {π = π} {cs = cs}) =
     let
       {-
       E  = (env-metric γ (cs-to-csn cs))
       E' = (env-metric γ' (cs-to-csn cs))
       nm-M  = v̲a̲l̲-metric M (proj₁ E) (proj₂ E) (cs-to-csn cs)
       nm-N  = comp-metric                      N              (proj₁ E' ) (wkn-cons (proj₂ E')) (cs-to-csn cs)
       nm-N₁ = comp-metric                      N  ((X , nm-M) ∷ proj₁ E') (wkn-cong (proj₂ E')) (cs-to-csn cs)
       --             ==
       nm-N₂ = comp-metric (wk-comp (wk-cong π) N) ((X , nm-M) ∷ proj₁ E ) (wkn-cong (proj₂ E )) (cs-to-csn cs)
       E₂ = (env-metric γ ((⟪ nm-N ⟫ , count-in-comp h N) ∷ cs-to-csn cs))
       nm-M₂ = ⟪ v̲a̲l̲-metric M (proj₁ E₂) (proj₂ E₂) ((⟪ nm-N ⟫ , count-in-comp h N) ∷ cs-to-csn cs) ⟫
       --
       γ-test = ∗
       M-test = l̲a̲m̲ {X = `Unit} (sub (var (var h)) (return unit))
       N-test = return (var h)
       cs-test = (4 , 10) ∷ []
       E-test  = (env-metric γ-test cs-test)
       nm-M-test  = v̲a̲l̲-metric M-test (proj₁ E-test) (proj₂ E-test) cs-test
       nm-N-test  =      comp-metric                      N-test            (proj₁ E-test ) (wkn-cons (proj₂ E-test)) cs-test
       nm = (⟪ nm-N-test ⟫ , count-in-comp h N-test)
       E₂-test = (env-metric γ-test (nm ∷ cs-test))
       nm-M₂-test = ⟪ v̲a̲l̲-metric M-test (proj₁ E₂-test) (proj₂ E₂-test) (nm ∷ cs-test) ⟫
       nm-N₂-test = comp-metric (wk-comp (wk-cong wk-id) N-test) ((`Unit `⇒ `Unit , nm-M-test) ∷ proj₁ E-test ) (wkn-cong (proj₂ E-test )) cs-test
       NT-total-bigger = nm-M₂-test + ⟪ nm-N-test ⟫  + (nm-M₂-test * count-in-comp h N-test) + (csn-to-nat₀ (⟪ nm-N-test ⟫  + nm-M₂-test * count-in-comp h N-test) cs-test)
       NT-total-smaller = ⟪ nm-N₂-test ⟫ + csn-to-nat₀ ⟪ nm-N₂-test ⟫ cs-test
       NT-bigger = ⟪ nm-N-test ⟫  + (nm-M₂-test * count-in-comp h N-test)
       NT-smaller = ⟪ nm-N₂-test ⟫
       -- nm-M ≤ nm-M₂     <------ NOT TRUE
       -- TP: nm-N₂ ≤ ⟪ nm-N ⟫ + (count-in-comp h N + nm-M * count-in-comp h N)
       -- TP: nm-N₂ ≤ ⟪ nm-N ⟫ + (count-in-comp h N + nm-M₂ * count-in-comp h N)

       -- TP: ⟪ comp-metric (wk-comp (wk-cong π) N) ((X , v̲a̲l̲-metric M E ϖ csn) ∷ E ) (wkn-cong ϖ) csn ⟫ ≤ ⟪ comp-metric N E' (wkn-cons ϖ') csn ⟫ + (count-in-comp h N + ⟪ v̲a̲l̲-metric M E₂ ϖ₂ ((⟪ comp-metric N E' (wkn-cons ϖ') csn ⟫ , count-in-comp h N) ∷ csn) ⟫ * count-in-comp h N)
       -- can ignore the weakening E -> E'
       -- TP: ⟪ comp-metric (wk-comp (wk-cong π) N) ((X , v̲a̲l̲-metric M E ϖ csn) ∷ E ) (wkn-cong ϖ) csn ⟫ ≤ ⟪ comp-metric N E (wkn-cons ϖ) csn ⟫ + (count-in-comp h N + ⟪ v̲a̲l̲-metric M E₂ ϖ₂ ((⟪ comp-metric N E (wkn-cons ϖ) csn ⟫ , count-in-comp h N) ∷ csn) ⟫ * count-in-comp h N)

       -- TP: ⟪ comp-metric (wk-comp (wk-cong π) N) ((X , v̲a̲l̲-metric M (proj₁ (env-metric γ csn)) (proj₂ (env-metric γ csn))) ∷ E) (wkn-cong ϖ) csn ⟫ ≤ ⟪ comp-metric N (proj₁ (env-metric γ csn)) (wkn-cons (proj₂ (env-metric γ csn))) csn ⟫ + (count-in-comp h N + ⟪ v̲a̲l̲-metric M (proj₁ (env-metric γ ((⟪ comp-metric N E (wkn-cons ϖ) csn ⟫ , count-in-comp h N) ∷ csn))) (proj₂ (env-metric γ ((⟪ comp-metric N E (wkn-cons ϖ) csn ⟫ , count-in-comp h N) ∷ csn))) ((⟪ comp-metric N E (wkn-cons ϖ) csn ⟫ , count-in-comp h N) ∷ csn) ⟫ * count-in-comp h N)

       -- TP: ⟪ comp-metric (wk-comp (wk-cong π) N) ((X , v̲a̲l̲-metric M (proj₁ E) (proj₂ E) (cs-to-csn cs)) ∷ proj₁ E ) (wkn-cong (proj₂ E )) (cs-to-csn cs) ⟫
       --    ≤ ⟪ nm-N ⟫ + (count-in-comp h N + ⟪ v̲a̲l̲-metric M (proj₁ E₂) (proj₂ E₂) ((⟪ nm-N ⟫ , count-in-comp h N) ∷ cs-to-csn cs) ⟫ * count-in-comp h N)

       -- TP:          (⟪ nm-N₂ ⟫                                                  + csn-to-nat₀ ⟪ nm-N₂ ⟫ (cs-to-csn cs))
       --       ≤
       --     (nm-M₂ + (⟪ nm-N ⟫ + (count-in-comp h N + nm-M₂ * count-in-comp h N) + csn-to-nat₀ (⟪ nm-N ⟫ + (count-in-comp h N + nm-M₂ * count-in-comp h N)) (cs-to-csn cs)))
       lhs2 = (nm-M₂ + csn-to-nat₀ nm-M₂ ((⟪ nm-N ⟫ , count-in-comp h N) ∷ cs-to-csn cs))
       -}
       x = 1 ≡ {!!}
     in
       {!!}


  comp-metric-decreasing ∘push = {!!}
  comp-metric-decreasing ∘sub = {!!}

  comp-metric-decreasing (∘pm π M→M' π') = {!!}
  comp-metric-decreasing (∙app-var i→λW πᵥ) = {!!}
  comp-metric-decreasing (∙app-pm M→M' π) = {!!}
  comp-metric-decreasing ∙app-lam = {!!}
  comp-metric-decreasing (∘app N→N' π) = {!!}
  comp-metric-decreasing (∘var M→i π' x₁ πᵥ) = {!!}

-}
-------------------------------------------------------
-------------------------------------------------------
-------------------------------------------------------

-------------------------------------------------------

{-
  -- postulate debuglemma : m ≤ n
  debuglemma = ≤-refl

-------------------------------
  {-# TERMINATING #-}
  mutual

    app-eval-rec :   (M : Γ' ⊢ᵛ X `⇒ Y) → (N : V̲a̲l̲ Γ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ Y) → (πₓ : Wk Γ Δ)
                   → (wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → (n : ℕ)
                   → (n ≤ n)
                   -- → (compstate-metric ((∙⟨ (a̲pp (wk-val π M) N) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀}) ≤ n)
                   → CompSteps ((∙⟨ (a̲pp (wk-val π M) N) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    -- app-eval-rec (var i) N γ π cs πₓ wk≡₀ zero m≤n with m≤n
    -- ... | ()
    -- app-eval-rec (var i) N γ π cs πₓ wk≡₀ (suc n) m≤n with lookup (wk-mem π i) γ
    app-eval-rec (var i) N γ π cs πₓ wk≡₀ n m≤n with lookup (wk-mem π i) γ
    ... | steps i>>T (found-lam {X = X} {W = W} {γ = γ₁}) i≡T π₁ w≡γ with app-eval-rec (lam W) N γ π₁ cs πₓ wk≡₀ n debuglemma
    ... | steps {T = T} W>WT HT S≡T cM =

                 steps

                    (∙⟨ a̲pp (wk-val π (var i)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-var i>>T π₁ ⟩ W>WT)

                    HT

                    ( (< ⟦ wk-mem π i ⟧ᵐ , ⟦ toVal N ⟧ᵛ > ； Data.Product.uncurry idf) ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ
                     ≡⟨ refl ⟩
                      ⟦ wk-mem π i ⟧ᵐ ⟦ γ ⟧ᴱ (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                     ≡⟨ cong (λ x → x (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) i≡T ⟩
                      ⟦ W ⟧ᶜ (⟦ γ₁ ⟧ᴱ , (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ))  (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                     ≡⟨ cong (λ x → ⟦ W ⟧ᶜ (x , (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ))  (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym w≡γ) ⟩
                      ⟦ W ⟧ᶜ (⟦ π₁ ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                     ≡⟨ S≡T ⟩
                      ⟦ T ⟧ᶜꟴ ∎)

                    (compstate-metric ((∙⟨ a̲pp (wk-val π (var i)) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀}) ∷ cM)

    app-eval-rec (lam W) N γ π cs πₓ wk≡₀ n m≤n with comp-eval-rec W (γ ﹐ N) (wk-cong π) cs (wk-wk πₓ) wk≡₀ n debuglemma
    ... | steps {T = T} W>WT HT S≡T cM =

                  steps

                     ( ∙⟨ a̲pp (wk-val π (lam W)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-lam ⟩ W>WT)

                     HT

                     S≡T

                     (compstate-metric ((∙⟨ a̲pp (wk-val π (lam W)) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀}) ∷ cM)

    app-eval-rec (pm M₁ N₁) N γ π cs πₓ wk≡₀ n m≤n with val-eval-rec M₁ γ π
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
                      n
                      debuglemma
    ...          | steps {T = T} N>NT NT S≡T cM rewrite (sym eq) =

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

                     (compstate-metric ((∙⟨ (a̲pp (wk-val π (pm M₁ N₁)) N) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀}) ∷ cM)

    comp-eval-rec : (W : Γ' ⊢ᶜ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ X) → (πₓ : Wk Γ Δ)
                  → (wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → (n : ℕ)
                  → (n ≤ n)
                  -- → (compstate-metric ((∘⟨ wk-comp π W ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀}) ≤ n)
                  → CompSteps ((∘⟨ wk-comp π W ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    comp-eval-rec (return {A = X} M) γ π ◻ πₓ wk≡₀ n m≤n with val-eval-rec {X = X} M γ π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ =

                 steps

                    (∘⟨ wk-comp π (return M) ⊰ γ ╎ ◻ ⟩ →ᶜ⟨ ∘return M>T ⟩ (∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ ◻ ⟩ ◼))

                    ret

                    (cong (λ x → (η x) k₀) M≡T)

                    (compstate-metric ((∘⟨ wk-comp π (return M) ⊰ γ ╎ ◻ ⟩) {π = πₓ} {wk≡ = wk≡₀}) ∷ compstate-metric ((∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ ◻ ⟩) {π = wk-trans π' πₓ} {wk≡ = wk≡₀}) ∷ [])

    -- comp-eval-rec (return {A = X} M) γ π ((M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁}) πₓ wk≡₀ zero m≤n with m≤n
    -- ... | ()
    -- comp-eval-rec (return {A = X} M) γ π ((M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁}) πₓ wk≡₀ (suc n) m≤n with val-eval-rec {X = X} M γ π
    comp-eval-rec (return {A = X} M) γ π ((M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁}) πₓ wk≡₀ n m≤n with val-eval-rec {X = X} M γ π
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
                   n
                   debuglemma
    ... | steps {T = ∙⟨ r̲e̲t̲u̲r̲n̲  M₂ ⊰ γ₂ ╎ ◻ ⟩} M'>T ret S≡T cM =

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

                    (compstate-metric ((∘⟨ wk-comp π (return M) ⊰ γ ╎ ((M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁}) ⟩) {π = πₓ} {wk≡ = wk≡₀}) ∷ compstate-metric ((∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ ((M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁}) ⟩) {π = wk-trans π' πₓ} {wk≡ = ≡-syntax.step-≡-⟩ _≡_ trans (⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ) (≡-syntax.step-≡-⟩ _≡_ trans (⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ)) (≡-syntax.step-≡-⟩ _≡_ trans (⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ) ((_≡_ end-syntax.∎) refl ⟦ γ' ⟧ᴱ) wk≡₀) (cong ⟦ πₓ ⟧ʷ wk≡)) (sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ))}) ∷ cM)

    comp-eval-rec (pm {A = X} {B = Y} M W) γ π cs πₓ wk≡₀ n m≤n with val-eval-rec {X = X `× Y} M γ π
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
                     n
                     debuglemma
    ...   | steps {T = T} W>T HT S≡T cM with wk-comp-trans W (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
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

                   (compstate-metric ((∘⟨ wk-comp π (pm M W) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀}) ∷ cM)

    comp-eval-rec (push W V) γ π cs πₓ wk≡₀ n m≤n with comp-eval-rec W γ π (((wk-comp (wk-cong π) V) ⊲ γ ⦂⦂ cs) {wk≡ = wk≡₀}) wk-id refl n debuglemma
    ... | steps {T = ∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ₁ ╎ ◻ ⟩} W>T ret S≡T cM =

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

                  (compstate-metric ((∘⟨ push (wk-comp π W) (wk-comp (wk-cong π) V) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀}) ∷ cM)

    comp-eval-rec (app M N) γ π cs πₓ wk≡₀ n m≤n with val-eval-rec N γ π
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
                      n
                      debuglemma
    ... | steps {T = T} W>WT HT S≡T cM rewrite (sym (wk-val-trans M πᴺ π)) =

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

                (compstate-metric ((∘⟨ app (wk-val π M) (wk-val π N) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀}) ∷ cM)

    -- comp-eval-rec (var {A = X} M) γ π cs πₓ wk≡₀ zero m≤n with m≤n
    -- ... | ()
    -- comp-eval-rec (var {A = X} M) γ π cs πₓ wk≡₀ (suc n) m≤n with val-eval-rec {X = `V} M γ π
    comp-eval-rec (var {A = X} M) γ π cs πₓ wk≡₀ n m≤n with val-eval-rec {X = `V} M γ π
    ... | steps {T = ∙ ((⭭ v̲a̲r̲ i) ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ with lookup i γ₁
    ... | steps i>>T (found-comp {X = X} {W = W'} {γ = γ'} {cs = cs'} {π = πᶜ} {wk≡ = wk≡c}) i≡T π₂ w≡γ with
                    comp-eval-rec
                     W'
                     γ'
                     wk-id
                     cs'
                     πᶜ
                     wk≡c
                     n
                     debuglemma
    ... | steps {T = ∙⟨ C̲o̲m̲p.r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₂ ╎ ◻ ⟩} W>T ret S≡T cM rewrite wk-comp-id W' =

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

                  (compstate-metric ((∘⟨ var (wk-val π M) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀}) ∷ cM)

    comp-eval-rec (sub W V) γ π cs πₓ wk≡₀ n m≤n with comp-eval-rec W ((γ ﹐﹝ wk-comp π V ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡₀}) (wk-cong π) cs (wk-wk πₓ) wk≡₀ n debuglemma
    ... | steps {T = T} W>WT HT S≡T cM =

                steps

                    (∘⟨ sub (wk-comp (wk-cong π) W) (wk-comp π V) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘sub ⟩ W>WT)

                    HT

                    S≡T

                    (compstate-metric ((∘⟨ sub (wk-comp (wk-cong π) W) (wk-comp π V) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀}) ∷ cM)


    comp-eval : (W : ε ⊢ᶜ R₀) → CompSteps ((∘⟨ wk-comp wk-id W ⊰ ∗ ╎ ◻ ⟩) {π = wk-id} {wk≡ = refl})
    comp-eval W = comp-eval-rec W ∗ wk-id ◻ wk-id refl (compstate-metric ((∘⟨ wk-comp wk-id W ⊰ ∗ ╎ ◻ ⟩) {π = wk-id} {wk≡ = refl})) debuglemma

    data CompStepsTest : CompState → Set where

        steps : {S T : CompState} → S →ᶜ* T → List ℕ → CompStepsTest S

    comp-eval-test : (W : ε ⊢ᶜ R₀) → CompStepsTest ((∘⟨ wk-comp wk-id W ⊰ ∗ ╎ ◻ ⟩) {π = wk-id} {wk≡ = refl})
    comp-eval-test W with comp-eval W
    ... | steps x _ _ l = steps x l

    comp-eval-test-metric : (W : ε ⊢ᶜ R₀) → List ℕ
    comp-eval-test-metric W with comp-eval W
    ... | steps _ _ _ l = l

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

{-
_ : comp-eval-test ex7 ≡

      steps
      (           ∘⟨ push (sub (var (pm (pair (var h) unit) (var (t h)))) (return unit)) (return (var h)) ⊰ ∗ ╎ ◻ ⟩
      →ᶜ⟨ ∘push ⟩ ∘⟨ sub (var (pm (pair (var h) unit) (var (t h)))) (return unit) ⊰ ∗ ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ⟩
      →ᶜ⟨ ∘sub ⟩ ∘⟨ var (pm (pair (var h) unit) (var (t h))) ⊰ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ⟩
      →ᶜ⟨ ∘var (           ∘ ⇡ pm (pair (var h) unit) (var (t h)) ⊲ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ∷ □
                 →ᵛ⟨ ∘pm ⟩ ∘ ⇡ pair (var h) unit ⊲ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ∷ ⇡ᴹ (pair (var h) unit) (var (t h)) ⊲ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ∷ □
                 →ᵛ⟨ ∘pair ⟩ ∘ ⇡ var h ⊲ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ∷ ⇡ᴸ (var h) unit ⊲ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ∷ ⇡ᴹ (pair (var h) unit) (var (t h)) ⊲ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ∷ □
                 →ᵛ⟨ ∘var-c ⟩ ∙ ⭭ v̲a̲r̲ h ⊲ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ∷ ⇡ᴸ (var h) unit ⊲ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ∷ ⇡ᴹ (pair (var h) unit) (var (t h)) ⊲ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ∷ □
                 →ᵛ⟨ ∙M∷l ⟩ ∘ ⇡ unit ⊲ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ∷ ⇡ᴿ (v̲a̲r̲ h) unit ⊲ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ∷ ⇡ᴹ (pair (var h) unit) (var (t h)) ⊲ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ∷ □
                 →ᵛ⟨ ∘unit ⟩ ∙ ⭭ u̲n̲i̲t̲ ⊲ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ∷ ⇡ᴿ (v̲a̲r̲ h) unit ⊲ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ∷ ⇡ᴹ (pair (var h) unit) (var (t h)) ⊲ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ∷ □
                 →ᵛ⟨ ∙M∷r ⟩ ∙ ⭭ pa̲i̲r̲ (v̲a̲r̲ h) u̲n̲i̲t̲ ⊲ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ∷ ⇡ᴹ (pair (var h) unit) (var (t h)) ⊲ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ∷ □
                 →ᵛ⟨ ∙pair∷pm ⟩ ∘ ⇡ var (t h) ⊲ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ﹐ v̲a̲r̲ h ﹐ u̲n̲i̲t̲ ∷ □
                 →ᵛ⟨ ∘var-c ⟩．) (wk-wk (wk-wk (wk-cong wk-ε))) (                 ⟨ t h ∥ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ﹐ v̲a̲r̲ h ﹐ u̲n̲i̲t̲ ⟩
                                                                →ᴸ⟨ val-t-step ⟩ (⟨ h ∥ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ﹐ v̲a̲r̲ h ⟩
                                                                →ᴸ⟨ val-h-step ⟩ (⟨ h ∥ ∗ ﹐﹝ return unit ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ﹞ ⟩ ◼))) (wk-wk (wk-wk (wk-wk wk-ε)))⟩ ∘⟨ return unit ⊰ ∗ ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ⟩
      →ᶜ⟨ ∘return (∘ ⇡ unit ⊲ ∗ ∷ □ →ᵛ⟨ ∘unit ⟩．)⟩ ∙⟨ r̲e̲t̲u̲r̲n̲ u̲n̲i̲t̲ ⊰ ∗ ╎ return (var h) ⊲ ∗ ⦂⦂ ◻ ⟩
      →ᶜ⟨ ∙return ⟩ ∘⟨ return (var h) ⊰ ∗ ﹐ u̲n̲i̲t̲ ╎ ◻ ⟩
      →ᶜ⟨ ∘return (                         ∘ ⇡ var h ⊲ ∗ ﹐ u̲n̲i̲t̲ ∷ □
                   →ᵛ⟨ ∘var (⟨ h ∥ ∗ ﹐ u̲n̲i̲t̲ ⟩ ◼) (wk-wk wk-ε)⟩．)⟩ (∙⟨ r̲e̲t̲u̲r̲n̲ u̲n̲i̲t̲ ⊰ ∗ ﹐ u̲n̲i̲t̲ ╎ ◻ ⟩ ◼))
      (136 ∷ 58 ∷ 48 ∷ 12 ∷ 8 ∷ 5 ∷ 2 ∷ [])
_ = refl
-}

ex8 : ε ⊢ᶜ `Unit
ex8 = sub (push (var (var h)) (app (var h) unit)) (return unit)


ex9 : ε ⊢ᶜ `Unit
ex9 = sub (push (sub (return (var h)) ((return (var h)))) (var (var h))) (return unit)

{-
_ : comp-eval-test ex9 ≡
    steps
    (             ∘⟨ sub (push (sub (return (var h)) (return (var h))) (var (var h))) (return unit) ⊰ ∗ ╎ ◻ ⟩
    →ᶜ⟨ ∘sub ⟩    ∘⟨ push (sub (return (var h)) (return (var h))) (var (var h)) ⊰ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ╎ ◻ ⟩
    →ᶜ⟨ ∘push ⟩   ∘⟨ sub (return (var h)) (return (var h)) ⊰ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ╎
                                                                    var (var h) ⊲ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ⦂⦂ ◻ ⟩
    →ᶜ⟨ ∘sub ⟩    ∘⟨ return (var h) ⊰ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ﹐﹝ return (var h) ╎ var (var h) ⊲ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ⦂⦂ ◻ ﹞ ╎
                                                                    var (var h) ⊲ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ⦂⦂ ◻ ⟩
    →ᶜ⟨ ∘return (                 ∘ ⇡ var h ⊲ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ﹐﹝ return (var h) ╎ var (var h) ⊲ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ⦂⦂ ◻ ﹞ ∷ □
                  →ᵛ⟨ ∘var-c ⟩．) ⟩
                  ∙⟨ r̲e̲t̲u̲r̲n̲ (v̲a̲r̲ h) ⊰ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ﹐﹝ return (var h) ╎ var (var h) ⊲ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ⦂⦂ ◻ ﹞ ╎
                                                                    var (var h) ⊲ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ⦂⦂ ◻ ⟩
    →ᶜ⟨ ∙return ⟩ ∘⟨ var (var h) ⊰ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ﹐﹝ return (var h) ╎ var (var h) ⊲ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ⦂⦂ ◻ ﹞ ﹐ v̲a̲r̲ h ╎ ◻ ⟩
    →ᶜ⟨ ∘var     (                 ∘ ⇡ var h ⊲ ∗ ﹐﹝ return unit ╎ ◻ ﹞
                                                 ﹐﹝ return (var h) ╎ var (var h) ⊲ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ⦂⦂ ◻ ﹞
                                                 ﹐ v̲a̲r̲ h ∷ □ →ᵛ⟨ ∘var-c ⟩．) (wk-cong (wk-cong (wk-cong wk-ε)))
                 (⟨ h ∥ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ﹐﹝ return (var h) ╎ var (var h) ⊲ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ⦂⦂ ◻ ﹞ ﹐ v̲a̲r̲ h ⟩
                  →ᴸ⟨ val-h-step ⟩ (⟨ h ∥ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ﹐﹝ return (var h) ╎ var (var h) ⊲ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ⦂⦂ ◻ ﹞ ⟩ ◼))
                 (wk-wk (wk-wk (wk-cong wk-ε))) ⟩
                  ∘⟨ return (var h) ⊰ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ╎ var (var h) ⊲ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ⦂⦂ ◻ ⟩
    →ᶜ⟨ ∘return (∘ ⇡ var h ⊲ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ∷ □ →ᵛ⟨ ∘var-c ⟩．) ⟩
                  ∙⟨ r̲e̲t̲u̲r̲n̲ (v̲a̲r̲ h) ⊰ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ╎ var (var h) ⊲ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ⦂⦂ ◻ ⟩
    →ᶜ⟨ ∙return ⟩ ∘⟨ var (var h) ⊰ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ﹐ v̲a̲r̲ h ╎ ◻ ⟩
    →ᶜ⟨ ∘var    (∘ ⇡ var h ⊲ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ﹐ v̲a̲r̲ h ∷ □ →ᵛ⟨ ∘var-c ⟩．) (wk-cong (wk-cong wk-ε)) (⟨ h ∥ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ﹐ v̲a̲r̲ h ⟩
                                                                     →ᴸ⟨ val-h-step ⟩ (⟨ h ∥ ∗ ﹐﹝ return unit ╎ ◻ ﹞ ⟩ ◼)) (wk-wk (wk-wk wk-ε)) ⟩
                  ∘⟨ return unit ⊰ ∗ ╎ ◻ ⟩
    →ᶜ⟨ ∘return (∘ ⇡ unit ⊲ ∗ ∷ □ →ᵛ⟨ ∘unit ⟩．) ⟩
                 (∙⟨ r̲e̲t̲u̲r̲n̲ u̲n̲i̲t̲ ⊰ ∗ ╎ ◻ ⟩ ◼))
    (244 ∷ 239 ∷ 67 ∷ 49 ∷ 45 ∷ 23 ∷ 19 ∷ 15 ∷ 8 ∷ 4 ∷ 2 ∷ [])
_ = refl
-}

ex10 : ε ⊢ᶜ `Unit
ex10 = push (sub (push (var (var h)) (app (var h) unit)) (return unit)) (return unit)

{-
_ : comp-eval-test ex10 ≡
  steps
  (             ∘⟨ push (sub (push (var (var h)) (app (var h) unit)) (return unit)) (return unit) ⊰ ∗ ╎ ◻ ⟩
  →ᶜ⟨ ∘push ⟩   ∘⟨ sub (push (var (var h)) (app (var h) unit)) (return unit) ⊰ ∗ ╎ return unit ⊲ ∗ ⦂⦂ ◻ ⟩
  →ᶜ⟨ ∘sub ⟩    ∘⟨ push (var (var h)) (app (var h) unit) ⊰ ∗ ﹐﹝ return unit ╎ return unit ⊲ ∗ ⦂⦂ ◻ ﹞ ╎ return unit ⊲ ∗ ⦂⦂ ◻ ⟩
  →ᶜ⟨ ∘push ⟩   ∘⟨ var (var h) ⊰ ∗ ﹐﹝ return unit ╎ return unit ⊲ ∗ ⦂⦂ ◻ ﹞ ╎ app (var h) unit ⊲ ∗ ﹐﹝ return unit ╎ return unit ⊲ ∗ ⦂⦂ ◻ ﹞ ⦂⦂ (return unit ⊲ ∗ ⦂⦂ ◻) ⟩
  →ᶜ⟨ ∘var (∘ ⇡ var h ⊲ ∗ ﹐﹝ return unit ╎ return unit ⊲ ∗ ⦂⦂ ◻ ﹞ ∷ □ →ᵛ⟨ ∘var-c ⟩．) (wk-cong wk-ε) (⟨ h ∥ ∗ ﹐﹝ return unit ╎ return unit ⊲ ∗ ⦂⦂ ◻ ﹞ ⟩ ◼) (wk-wk wk-ε) ⟩
                ∘⟨ return unit ⊰ ∗ ╎ return unit ⊲ ∗ ⦂⦂ ◻ ⟩
  →ᶜ⟨ ∘return (∘ ⇡ unit ⊲ ∗ ∷ □ →ᵛ⟨ ∘unit ⟩．) ⟩
                ∙⟨ r̲e̲t̲u̲r̲n̲ u̲n̲i̲t̲ ⊰ ∗ ╎ return unit ⊲ ∗ ⦂⦂ ◻ ⟩
  →ᶜ⟨ ∙return ⟩ ∘⟨ return unit ⊰ ∗ ﹐ u̲n̲i̲t̲ ╎ ◻ ⟩
  →ᶜ⟨ ∘return (∘ ⇡ unit ⊲ ∗ ﹐ u̲n̲i̲t̲ ∷ □ →ᵛ⟨ ∘unit ⟩．) ⟩
               (∙⟨ r̲e̲t̲u̲r̲n̲ u̲n̲i̲t̲ ⊰ ∗ ﹐ u̲n̲i̲t̲ ╎ ◻ ⟩ ◼))
  (63 ∷ 38 ∷ 33 ∷ 32 ∷ 8 ∷ 6 ∷ 4 ∷ 2 ∷ [])
_ = refl
-}

ex11 : ε ⊢ᶜ `Unit
ex11 = app (lam (app (lam (push (sub (push (var (var h)) (app (var h) unit)) (return (lam (return (var h))))) (app (var h) unit))) unit)) unit

{-
_ : comp-eval-test-metric ex3 ≡ 11 ∷ 2 ∷ []
_ = refl

_ : comp-eval-test-metric ex4 ≡ 26 ∷ 14 ∷ 11 ∷ 2 ∷ []
_ = refl

_ : comp-eval-test-metric ex5 ≡ 1199 ∷ 156 ∷ 132 ∷ 100 ∷ 94 ∷ 64 ∷ 26 ∷ 8 ∷ 5 ∷ 2 ∷ []
_ = refl

_ : comp-eval-test-metric ex6 ≡ 19 ∷ 14 ∷ 4 ∷ 2 ∷ []
_ = refl

_ : comp-eval-test-metric ex7 ≡ 136 ∷ 58 ∷ 48 ∷ 12 ∷ 8 ∷ 5 ∷ 2 ∷ []
_ = refl

_ : comp-eval-test-metric ex8 ≡ 26 ∷ 21 ∷ 20 ∷ 4 ∷ 2 ∷ []
_ = refl

_ : comp-eval-test-metric ex9 ≡ 244 ∷ 239 ∷ 67 ∷ 49 ∷ 45 ∷ 23 ∷ 19 ∷ 15 ∷ 8 ∷ 4 ∷ 2 ∷ []
_ = refl

_ : comp-eval-test-metric ex10 ≡ 63 ∷ 38 ∷ 33 ∷ 32 ∷ 8 ∷ 6 ∷ 4 ∷ 2 ∷ []
_ = refl

_ : comp-eval-test-metric ex11 ≡ 801 ∷ 799 ∷ 795 ∷ 793 ∷ 789 ∷ 138 ∷ 120 ∷ 93 ∷ 22 ∷ 18 ∷ 13 ∷ 10 ∷ 9 ∷ 5 ∷ 2 ∷ []
_ = refl
-}

ex12 : ε ⊢ᶜ `Unit
ex12 = push (return unit) (return (pm (pair (pair unit unit) (pair unit unit)) unit))

ex13 : ε ⊢ᶜ `Unit
ex13 = sub ((var (var h))) (return (pm (pair (pair unit unit) (pair unit unit)) unit))

--               ∙⟨ r̲e̲t̲u̲r̲n̲ u̲n̲i̲t̲ ⊰ ∗ ╎ return (pm (pair (pair unit unit) (pair unit unit)) unit) ⊲ ∗ ⦂⦂ ◻ ⟩              11
-- →ᶜ⟨ ∙return ⟩ ∘⟨ return (pm (pair (pair unit unit) (pair unit unit)) unit) ⊰ ∗ ﹐ u̲n̲i̲t̲ ╎ ◻ ⟩                          9

-- return (pm (pair (pair unit unit) (pair unit unit)) unit) ⊲ ∗ ⦂⦂ ◻                                         (9 , 0) ∷ []
-- ∗                                                                                                         [] , wkn-nil
-- ∗ ﹐ u̲n̲i̲t                                                                    (`Unit , m-Unit 1) ∷ [] , wkn-cong wkn-nil
-- (r̲e̲t̲u̲r̲n̲ u̲n̲i̲t̲)                                                                                                 m-Unit 2
-- return (pm (pair (pair unit unit) (pair unit unit)) unit)                                                     m-Unit 9

ex14 : ε ⊢ᶜ (`Unit)
ex14 = push (push (app (lam {A = `Unit} (sub (var (var h)) (return unit))) unit) (return unit)) (app (lam (return unit)) (pair (pair (pair (var h) (var h)) (var h)) (var h)))

_ : comp-eval-test-metric ex11 ≡ {!comp-eval-test-metric ex14!}
_ = refl
-}

{-
postulate k₀' : ⟦ (((((`Unit `× `Unit) `× `Unit) `× `Unit) `× `Unit) `× `Unit) ⟧ → R
open VMain {R₀ = (((((`Unit `× `Unit) `× `Unit) `× `Unit) `× `Unit) `× `Unit)} k₀'
open CMain {R₀ = (((((`Unit `× `Unit) `× `Unit) `× `Unit) `× `Unit) `× `Unit)} k₀'

ex15 : ε ⊢ᶜ (`Unit `⇒ `Unit)
ex15 = return (lam {A = `Unit} (sub (var (var h)) (return unit)))

ex16 : ε ⊢ᶜ (`Unit `⇒ `Unit)
ex16 = push (return (lam (return unit))) (push (return (lam {A = `Unit} (sub (var (var h)) (return unit)))) (return (lam (return unit))))


ex17 : ε ⊢ᶜ (((((`Unit `× `Unit) `× `Unit) `× `Unit) `× `Unit) `× `Unit)
ex17 = push ((push (return (lam {A = `Unit} (sub (var (var h)) (return unit)))) (return unit))) (return (pair (pair (pair (pair (pair (var h) (var h)) (var h)) (var h)) (var h)) (var h)))

_ : 1 ≡ {! comp-eval-test-metric ex17!}
_ = refl


-- csn-decreasing {n₂ = suc n₂} {n₁ = suc n₁} {csn₁ = (suc fst , zero) ∷ csn₁} {csn₂ = csn₂} (s≤s n₂≤n₁) (extcsn-ext α c) = {!!}
-- Goal: csn-to-nat₀ (suc n₂) csn₂ ≤ suc (fst + n₁ * zero + csn-to-nat₀ (suc (fst + n₁ * zero)) csn₁)
-- Goal: csn-to-nat₀       9    [] ≤ suc (  9 + n₁ * zero + csn-to-nat₀ (suc (fst + n₁ * zero)) csn₁)
-}
