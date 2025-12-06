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
    m-⇒ : (m : ℕ) → (cnt : ℕ) → (TermMetric Y) → TermMetric (X `⇒ Y)
    m-×   : (m : ℕ) → (TermMetric X) → (TermMetric Y) → TermMetric (X `× Y)

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
  valstate-metric (∘ S) m csn =
    let
      e = env-metric (botEnv S) csn
      w = partial-term-metric (botTerm S) (proj₁ e) (proj₂ e) csn
    in
      (m + w) + (csn-to-nat₀ (m + w) csn)
  valstate-metric (∙ S) m csn =
    let
      e = env-metric (botEnv S) csn
      w = partial-term-metric (botTerm S) (proj₁ e) (proj₂ e) csn
    in
      (m + w) + (csn-to-nat₀ (m + w) csn)

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

       -- TP: ⟪ comp-metric (wk-comp (wk-cong π) N) ((X , v̲a̲l̲-metric M (proj₁ (evn cns)) (proj₂ (evn cns)) csn) ∷ E ) (wkn-cong ϖ) csn ⟫ ≤ ⟪ comp-metric N E (wkn-cons ϖ) csn ⟫ + (count-in-comp h N + ⟪ v̲a̲l̲-metric M E₂ ϖ₂ ((⟪ comp-metric N E (wkn-cons ϖ) csn ⟫ , count-in-comp h N) ∷ csn) ⟫ * count-in-comp h N)

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


  -- comp-metric-decreasing (∙return {X = X} {M = l̲a̲m̲ x} {γ = γ} {N = N} {γ' = γ'} {π = π} {cs = cs}) = {!!}
  -- comp-metric-decreasing (∙return {X = X} {M = pa̲i̲r̲ M M₁} {γ = γ} {N = N} {γ' = γ'} {π = π} {cs = cs}) = {!!}

  -- comp-metric-decreasing (∙return {X = X} {M = u̲n̲i̲t̲} {γ = γ} {N = N} {γ' = γ'} {π = π} {cs = cs}) =
  --     let
  --       E  = (env-metric γ (cs-to-csn cs))
  --       E' = (env-metric γ' (cs-to-csn cs))
  --       -- nm-M  = v̲a̲l̲-metric  u̲n̲i̲t̲ (proj₁ E) (proj₂ E) (cs-to-csn cs)
  --       nm-N  = comp-metric                      N              (proj₁ E') (wkn-cons (proj₂ E')) (cs-to-csn cs)
  --       nm-N₂ = comp-metric (wk-comp (wk-cong π) N) ((X , m-Unit 1) ∷ proj₁ E) (wkn-cong (proj₂ E )) (cs-to-csn cs)
  --       E₂ = (env-metric γ ((⟪ nm-N ⟫ , count-in-comp h N) ∷ cs-to-csn cs))
  --       -- nm-M₂ = ⟪ v̲a̲l̲-metric u̲n̲i̲t̲ (proj₁ E₂) (proj₂ E₂) ((⟪ nm-N ⟫ , count-in-comp h N) ∷ cs-to-csn cs) ⟫
  --       -- TP: nm-N₂ ≤ ⟪ nm-N ⟫ + (count-in-comp h N + nm-M₂ * count-in-comp h N)
  --     in
  --       {!!}

  -- comp-metric-decreasing (∙return {X = X} {M = v̲a̲r̲ i} {γ = γ} {N = N} {γ' = γ'} {π = π} {cs = cs}) = {!!}

  comp-metric-decreasing ∘push = {!!}
  comp-metric-decreasing ∘sub = {!!}

  comp-metric-decreasing (∘pm π M→M' π') = {!!}
--Goal: suc (⟪comp-metric (wk-comp (wk-cong (wk-cong π')) (wk-comp (wk-cong (wk-cong π)) W)) ((Y , v̲a̲l̲-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((X , v̲a̲l̲-metric LHS (proj₁ (env-metric γ'' (cs-to-csn cs))) (proj₂ (env-metric γ'' (cs-to-csn cs))) (cs-to-csn cs)) ∷ proj₁ (env-metric γ'' (cs-to-csn cs))) (wkn-cong (proj₂ (env-metric γ'' (cs-to-csn cs)))) (cs-to-csn cs)) ∷ (X , v̲a̲l̲-metric LHS (proj₁ (env-metric γ'' (cs-to-csn cs))) (proj₂ (env-metric γ'' (cs-to-csn cs))) (cs-to-csn cs)) ∷ proj₁ (env-metric γ'' (cs-to-csn cs))) (wkn-cong (wkn-cong (proj₂ (env-metric γ'' (cs-to-csn cs))))) (cs-to-csn cs)⟫
--      + csn-to-nat₀ ⟪comp-metric (wk-comp (wk-cong (wk-cong π')) (wk-comp (wk-cong (wk-cong π)) W)) ((Y , v̲a̲l̲-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((X , v̲a̲l̲-metric LHS (proj₁ (env-metric γ'' (cs-to-csn cs))) (proj₂ (env-metric γ'' (cs-to-csn cs))) (cs-to-csn cs)) ∷ proj₁ (env-metric γ'' (cs-to-csn cs))) (wkn-cong (proj₂ (env-metric γ'' (cs-to-csn cs)))) (cs-to-csn cs)) ∷ (X , v̲a̲l̲-metric LHS (proj₁ (env-metric γ'' (cs-to-csn cs))) (proj₂ (env-metric γ'' (cs-to-csn cs))) (cs-to-csn cs)) ∷ proj₁ (env-metric γ'' (cs-to-csn cs))) (wkn-cong (wkn-cong (proj₂ (env-metric γ'' (cs-to-csn cs))))) (cs-to-csn cs)⟫ (cs-to-csn cs))
--      ≤
--      suc (vx (val-metric (wk-val π M) (proj₁ (env-metric γ (cs-to-csn cs))) (proj₂ (env-metric γ (cs-to-csn cs))) (cs-to-csn cs)) + ⟪comp-metric (wk-comp (wk-cong (wk-cong π)) W) (proj₁ (env-metric γ (cs-to-csn cs))) (wkn-cons (wkn-cons (proj₂ (env-metric γ (cs-to-csn cs))))) (cs-to-csn cs)⟫
--      + ⟪comp-metric (wk-comp (wk-cong (wk-cong π)) W) ((Y , rhs (val-metric (wk-val π M) (proj₁ (env-metric γ (cs-to-csn cs))) (proj₂ (env-metric γ (cs-to-csn cs))) (cs-to-csn cs))) ∷ (X , lhs (val-metric (wk-val π M) (proj₁ (env-metric γ (cs-to-csn cs))) (proj₂ (env-metric γ (cs-to-csn cs))) (cs-to-csn cs))) ∷ proj₁ (env-metric γ (cs-to-csn cs))) (wkn-cong (wkn-cong (proj₂ (env-metric γ (cs-to-csn cs))))) (cs-to-csn cs)⟫
--      + csn-to-nat₀ (suc (vx (val-metric (wk-val π M) (proj₁ (env-metric γ (cs-to-csn cs))) (proj₂ (env-metric γ (cs-to-csn cs))) (cs-to-csn cs)) + ⟪comp-metric (wk-comp (wk-cong (wk-cong π)) W) (proj₁ (env-metric γ (cs-to-csn cs))) (wkn-cons (wkn-cons (proj₂ (env-metric γ (cs-to-csn cs))))) (cs-to-csn cs)⟫ + ⟪comp-metric (wk-comp (wk-cong (wk-cong π)) W) ((Y , rhs (val-metric (wk-val π M) (proj₁ (env-metric γ (cs-to-csn cs))) (proj₂ (env-metric γ (cs-to-csn cs))) (cs-to-csn cs))) ∷ (X , lhs (val-metric (wk-val π M) (proj₁ (env-metric γ (cs-to-csn cs))) (proj₂ (env-metric γ (cs-to-csn cs))) (cs-to-csn cs))) ∷ proj₁ (env-metric γ (cs-to-csn cs))) (wkn-cong (wkn-cong (proj₂ (env-metric γ (cs-to-csn cs))))) (cs-to-csn cs)⟫)) (cs-to-csn cs))

  comp-metric-decreasing (∙app-var i→λW πᵥ) = {!!}
  comp-metric-decreasing (∙app-pm M→M' π) = {!!}
  comp-metric-decreasing ∙app-lam = {!!}
  comp-metric-decreasing (∘app N→N' π) = {!!}
  comp-metric-decreasing (∘var M→i π' x₁ πᵥ) = {!!}

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

{-
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

_ : comp-eval-test-metric ex11 ≡ {!comp-eval-test-metric ex13!}
_ = refl

--               ∙⟨ r̲e̲t̲u̲r̲n̲ u̲n̲i̲t̲ ⊰ ∗ ╎ return (pm (pair (pair unit unit) (pair unit unit)) unit) ⊲ ∗ ⦂⦂ ◻ ⟩              11
-- →ᶜ⟨ ∙return ⟩ ∘⟨ return (pm (pair (pair unit unit) (pair unit unit)) unit) ⊰ ∗ ﹐ u̲n̲i̲t̲ ╎ ◻ ⟩                          9

-- return (pm (pair (pair unit unit) (pair unit unit)) unit) ⊲ ∗ ⦂⦂ ◻                                         (9 , 0) ∷ []
-- ∗                                                                                                         [] , wkn-nil
-- ∗ ﹐ u̲n̲i̲t                                                                    (`Unit , m-Unit 1) ∷ [] , wkn-cong wkn-nil
-- (r̲e̲t̲u̲r̲n̲ u̲n̲i̲t̲)                                                                                                 m-Unit 2
-- return (pm (pair (pair unit unit) (pair unit unit)) unit)                                                     m-Unit 9

ex14 : ε ⊢ᶜ (`Unit)
ex14 = push (push (app (lam {A = `Unit} (sub (var (var h)) (return unit))) unit) (return unit)) (app (lam (return unit)) (pair (pair (pair (var h) (var h)) (var h)) (var h)))
-}


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
