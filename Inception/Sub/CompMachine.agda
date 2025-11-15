module Inception.Sub.CompMachine (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Function.Base using (_∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Unit
open import Data.Nat
open import Data.List

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


        -- X and X' should always be the same, but I don't think we can easily check for that
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

      steps : {S T : CompState} → S →ᶜ* T → CompHaltingState T → ⟦ S ⟧ᶜꟴ ≡ ⟦ T ⟧ᶜꟴ → CompSteps S


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

-----------------------------------------------------

  data Nmetric : Ty → Set where
    m-Unit : ℕ → Nmetric `Unit
    m-V : ℕ → Nmetric `V
    m-⇒ : ℕ → ℕ → Nmetric Y → Nmetric (X `⇒ Y)
    m-×   : ℕ → Nmetric X → Nmetric Y → Nmetric (X `× Y)

  zero-tree : (Y : Ty) → Nmetric Y
  zero-tree `Unit = m-Unit 0
  zero-tree (Y `× Y₁) = m-× 0 (zero-tree Y) (zero-tree Y₁)
  zero-tree (Y `⇒ Y₁) = m-⇒ 0 0 (zero-tree Y₁)
  zero-tree `V = m-V 0

  /_/ : Nmetric X → ℕ
  / m-Unit m / = m
  / m-V m / = m
  / m-⇒ m f n / = m + / n /
  / m-× m n n' / = m + / n / + / n' /

  incr : ℕ → Nmetric X → Nmetric X
  incr n (m-Unit x) = (m-Unit (n + x))
  incr n (m-V x) =  m-V (n + x)
  incr n (m-⇒ x f nm) = m-⇒ (n + x) f nm
  incr n (m-× x nm nm₁) = m-× (n + x) nm nm₁

  -- sumup : List (Σ[ X ∈ Ty ] Nmetric X) → ℕ
  -- sumup [] = 0
  -- sumup (nt ∷ ns) = / proj₂ nt / + (sumup ns)

  data Wkn : (Γ : Ctx) → (ns : List (Σ[ X ∈ Ty ] Nmetric X)) → Set where
    wkn-nil  : Wkn ε []
    wkn-cong : {Γ : Ctx} → {ne : List (Σ[ X ∈ Ty ] Nmetric X)} → {Y : Ty} → {n : Nmetric Y} → (ϖ : Wkn Γ ne) → Wkn (Γ ∙ Y) ((Y , n) ∷ ne)
    wkn-cons : {Γ : Ctx} → {ne : List (Σ[ X ∈ Ty ] Nmetric X)} → {Y : Ty} → (ϖ : Wkn Γ ne) → Wkn (Γ ∙ Y) ne

  mutual

    env-conv : (γ : Env Γ) → List (Σ[ X ∈ Ty ] Nmetric X)
    env-conv γ = {!!}

    lhs : Nmetric (X `× Y) → Nmetric X
    lhs (m-× x nm nm₁) = nm

    rhs : Nmetric (X `× Y) → Nmetric Y
    rhs (m-× x nm nm₁) = nm₁

    tg : Nmetric (X `⇒ Y) → Nmetric Y
    tg (m-⇒ x f nm) = nm

    fc : Nmetric (X `⇒ Y) → ℕ
    fc (m-⇒ x f nm) = f

    lookup-conv : (i : Γ ∋ Y) → (E : List (Σ[ X ∈ Ty ] Nmetric X)) → Wkn Γ E → Nmetric Y

    lookup-conv {Y = `Unit} Cx.h ((Y , n) ∷ ne) (wkn-cong ϖ) = incr 1 n
    lookup-conv {Y = `Unit} (Cx.t i) ((Y , n) ∷ ne) (wkn-cong ϖ) = lookup-conv {Y = `Unit} i ne ϖ

    lookup-conv {Y = `Unit} Cx.h [] (wkn-cons ϖ) = m-Unit 0
    lookup-conv {Y = `Unit} (Cx.t i) [] (wkn-cons ϖ) = m-Unit 0

    lookup-conv {Y = `Unit} Cx.h ((Y , n) ∷ ne) (wkn-cons ϖ) = m-Unit 0
    lookup-conv {Y = `Unit} (Cx.t i) ((Y , n) ∷ ne) (wkn-cons ϖ) = lookup-conv {Y = `Unit} i ((Y , n) ∷ ne) ϖ

    lookup-conv {Y = Y `× Y₁} Cx.h ((Y₂ , n) ∷ ne) (wkn-cong ϖ) = incr 1 n
    lookup-conv {Y = Y `× Y₁} (Cx.t i) ((Y₂ , n) ∷ ne) (wkn-cong ϖ) = lookup-conv {Y = Y `× Y₁} i ne ϖ

    lookup-conv {Y = Y `× Y₁} Cx.h [] (wkn-cons ϖ) = zero-tree (Y `× Y₁)
    lookup-conv {Y = Y `× Y₁} (Cx.t i) [] (wkn-cons ϖ) = zero-tree (Y `× Y₁)

    lookup-conv {Y = Y `× Y₁} Cx.h (x ∷ E) (wkn-cons ϖ) = zero-tree (Y `× Y₁)
    lookup-conv {Y = Y `× Y₁} (Cx.t i) (x ∷ E) (wkn-cons ϖ) = lookup-conv {Y = Y `× Y₁} i (x ∷ E) ϖ

    lookup-conv {Y = Y `⇒ Y₁} Cx.h ((Y₂ , n) ∷ ne) (wkn-cong ϖ) = incr 1 n
    lookup-conv {Y = Y `⇒ Y₁} (Cx.t i) ((Y₂ , n) ∷ ne) (wkn-cong ϖ) = lookup-conv {Y = Y `⇒ Y₁} i ne ϖ

    lookup-conv {Y = Y `⇒ Y₁} Cx.h [] (wkn-cons ϖ) = zero-tree (Y `⇒ Y₁)
    lookup-conv {Y = Y `⇒ Y₁} (Cx.t i) [] (wkn-cons ϖ) = zero-tree (Y `⇒ Y₁)

    lookup-conv {Y = Y `⇒ Y₁} Cx.h ((Y₂ , n) ∷ E) (wkn-cons ϖ) = zero-tree (Y `⇒ Y₁)
    lookup-conv {Y = Y `⇒ Y₁} (Cx.t i) ((Y₂ , n) ∷ E) (wkn-cons ϖ) = lookup-conv {Y = Y `⇒ Y₁} i ((Y₂ , n) ∷ E) ϖ

    lookup-conv {Y = `V} Cx.h ((Y , n) ∷ ne) (wkn-cong ϖ) = incr 1 n
    lookup-conv {Y = `V} (Cx.t i) ((Y , n) ∷ ne) (wkn-cong ϖ) = lookup-conv {Y = `V} i ne ϖ

    lookup-conv {Y = `V} Cx.h [] (wkn-cons ϖ) = m-V 0
    lookup-conv {Y = `V} (Cx.t i) [] (wkn-cons ϖ) = m-V 0

    lookup-conv {Y = `V} Cx.h ((Y , n) ∷ E) (wkn-cons ϖ) = m-V 0
    lookup-conv {Y = `V} (Cx.t i) ((Y , n) ∷ E) (wkn-cons ϖ) = lookup-conv {Y = `V} i ((Y , n) ∷ E) ϖ


    val-conv : (M : Val Γ Y) → (E : List (Σ[ X ∈ Ty ] Nmetric X)) → Wkn Γ E → Nmetric Y

    val-conv {Y = `Unit} (var {A = A} i) [] ϖ = m-Unit 0
    val-conv {Y = A₁ `× A₂} (var {A = A} Cx.h) [] (wkn-cons ϖ) = zero-tree (A₁ `× A₂) --m-× (val-conv {Y = A₁} (var h) [] (wkn-cons ϖ)) (val-conv {Y = A₂} (var h) [] (wkn-cons ϖ))
    val-conv {Y = A₁ `× A₂} (var {A = A} (Cx.t i)) [] (wkn-cons ϖ) = zero-tree (A₁ `× A₂) --val-conv {Y = A₁ `× A₂} (var {A = A} i) [] ϖ
    val-conv {Y = A₁ `⇒ A₂} (var {A = A} i) [] ϖ = zero-tree (A₁ `⇒ A₂)
    val-conv {Y = `V} (var {A = A} i) [] ϖ = m-V 0

    val-conv unit [] ϖ = m-Unit 0

    val-conv {Y = `Unit} (var {A = A} i) (x ∷ E) ϖ = lookup-conv i (x ∷ E) ϖ
    val-conv {Y = A₁ `× A₂} (var {A = A} Cx.h) (x ∷ E) ϖ = lookup-conv h (x ∷ E) ϖ
    val-conv {Y = A₁ `× A₂} (var {A = A} (Cx.t i)) (x ∷ E) ϖ = lookup-conv (t i) (x ∷ E) ϖ
    val-conv {Y = A₁ `⇒ A₂} (var {A = A} i) (x ∷ E) ϖ = lookup-conv i (x ∷ E) ϖ
    val-conv {Y = `V} (var {A = A} i) (x ∷ E) ϖ = lookup-conv i (x ∷ E) ϖ

    val-conv {Y = A `⇒ B} (lam W) [] ϖ = m-⇒ 0 (count-in-comp h W) (comp-conv W [] (wkn-cons ϖ))
    val-conv {Y = A `⇒ B} (lam W) (x ∷ E) ϖ = m-⇒ 0 (count-in-comp h W) (comp-conv W (x ∷ E) (wkn-cons ϖ))

    val-conv (pair M N) [] ϖ = m-× 0 (val-conv M [] ϖ) (val-conv N [] ϖ)
    val-conv (pair M N) (x ∷ E) ϖ = m-× 0 (val-conv M (x ∷ E) ϖ) (val-conv N (x ∷ E) ϖ)

    val-conv {Y = `Unit} (pm {A = A} {B = B} M N) [] ϖ = incr (/ val-conv M [] ϖ /) (val-conv N ((B , rhs ((val-conv M ) [] ϖ)) ∷ (A , lhs ((val-conv M ) [] ϖ)) ∷ []) (wkn-cong (wkn-cong ϖ)))
    val-conv {Y = `Unit} (pm {A = A} {B = B} M N) (x ∷ E) ϖ = incr (/ val-conv M (x ∷ E) ϖ /) (val-conv N ((B , rhs ((val-conv M ) (x ∷ E) ϖ)) ∷ (A , lhs ((val-conv M ) (x ∷ E) ϖ)) ∷ x ∷ E) (wkn-cong (wkn-cong ϖ)))

    val-conv {Y = Y `× Y₁} (pm {A = A} {B = B} M N) [] ϖ = incr (/ val-conv M [] ϖ /) (val-conv N ((B , rhs ((val-conv M ) [] ϖ)) ∷ (A , lhs ((val-conv M ) [] ϖ)) ∷ []) (wkn-cong (wkn-cong ϖ)))
    val-conv {Y = Y `× Y₁} (pm {A = A} {B = B} M N) (x ∷ E) ϖ = incr (/ val-conv M (x ∷ E) ϖ /) (val-conv N ((B , rhs ((val-conv M ) (x ∷ E) ϖ)) ∷ (A , lhs ((val-conv M ) (x ∷ E) ϖ)) ∷ x ∷ E) (wkn-cong (wkn-cong ϖ)))

    val-conv {Y = Y `⇒ Y₁} (pm {A = A} {B = B} M N) [] ϖ = incr (/ val-conv M [] ϖ /) (val-conv N ((B , rhs ((val-conv M ) [] ϖ)) ∷ (A , lhs ((val-conv M ) [] ϖ)) ∷ []) (wkn-cong (wkn-cong ϖ)))
    val-conv {Y = Y `⇒ Y₁} (pm {A = A} {B = B} M N) (x ∷ E) ϖ = incr (/ val-conv M (x ∷ E) ϖ /) (val-conv N ((B , rhs ((val-conv M ) (x ∷ E) ϖ)) ∷ (A , lhs ((val-conv M ) (x ∷ E) ϖ)) ∷ x ∷ E) (wkn-cong (wkn-cong ϖ)))

    val-conv {Y = `V} (pm {A = A} {B = B} M N) [] ϖ = incr (/ val-conv M [] ϖ /) (val-conv N ((B , rhs ((val-conv M ) [] ϖ)) ∷ (A , lhs ((val-conv M ) [] ϖ)) ∷ []) (wkn-cong (wkn-cong ϖ)))
    val-conv {Y = `V} (pm {A = A} {B = B} M N) (x ∷ E) ϖ = incr (/ val-conv M (x ∷ E) ϖ /) (val-conv N ((B , rhs ((val-conv M ) (x ∷ E) ϖ)) ∷ (A , lhs ((val-conv M ) (x ∷ E) ϖ)) ∷ x ∷ E) (wkn-cong (wkn-cong ϖ)))


    val-conv unit (x ∷ E) ϖ = m-Unit 0

    comp-conv : (W : Comp Γ Y) → (E : List (Σ[ X ∈ Ty ] Nmetric X)) → Wkn Γ E → Nmetric Y

    comp-conv (return M) E ϖ = incr 1 (val-conv M E ϖ)
    comp-conv (pm {A = A} {B = B} M W) E ϖ = incr (/ val-conv M E ϖ /) (comp-conv W ((B , rhs (val-conv M E ϖ)) ∷ (A , lhs (val-conv M E ϖ)) ∷ E) (wkn-cong (wkn-cong ϖ)))
    comp-conv (push {A = A} W₁ W₂) E ϖ = incr (/ comp-conv W₁ E ϖ /) (comp-conv W₂ ((A , comp-conv W₁ E ϖ) ∷ E) (wkn-cong ϖ))
    comp-conv (app {A = A} (var i) N) E ϖ = {!!}
    comp-conv (app {A = A} (lam W) N) E ϖ = incr (/ val-conv N E ϖ /) (comp-conv W ((A , val-conv N E ϖ) ∷ E) (wkn-cong ϖ))
    comp-conv (app {A = A} (pm M N₁) N₂) E ϖ = {!!}
    --incr (/ val-conv N E ϖ /) (tg (val-conv M ((A , val-conv N E ϖ) ∷ E) {!!}))

    comp-conv {Y = `Unit} (var {A = A} M) E ϖ = m-Unit (/ val-conv M E ϖ /)
    comp-conv {Y = A₁ `× A₂} (var {A = A} M) E ϖ = m-× (/ val-conv M E ϖ /) (zero-tree A₁) (zero-tree A₂)
    comp-conv {Y = A₁ `⇒ A₂} (var {A = A} M) E ϖ = m-⇒ (/ val-conv M E ϖ /) {!fc (val-conv M E ϖ)!} (zero-tree A₂)
    comp-conv {Y = `V} (var {A = A} M) E ϖ = m-V (/ val-conv M E ϖ /)
    comp-conv (sub {A = A} W₁ W₂) E ϖ = incr (/ comp-conv W₂ E ϖ /) (comp-conv W₁ ((`V , m-V (/ comp-conv W₂ E ϖ /)) ∷ E) (wkn-cong ϖ))

-----------------------------------------------------

{-
  mutual
    metric-lookup : (i : Γ ∋ X) → (γ : Env Γ') → (π : WkEnd Γ Γ') → ℕ
    metric-lookup {Γ = Γ} {Γ' = Γ'} Cx.h (γ ﹐ M) wk-Γ = metric-v̲a̲l̲ M γ wk-Γ
    metric-lookup {Γ = Γ} {Γ' = Γ'} Cx.h (γ ﹐﹝ W ╎ cs ﹞) wk-Γ = metric-comp W γ wk-Γ
    metric-lookup {Γ = Γ} {Γ' = Γ'} (Cx.t i) (γ ﹐ M) wk-Γ = metric-lookup i γ wk-Γ
    metric-lookup {Γ = Γ} {Γ' = Γ'} (Cx.t i) (γ ﹐﹝ W ╎ cs ﹞) wk-Γ = metric-lookup i γ wk-Γ
    metric-lookup {Γ = Γ Cx.∙ X} {Γ' = Γ'} Cx.h ∗ (wk-wk π) = 0
    metric-lookup {Γ = Γ Cx.∙ X} {Γ' = Γ'} Cx.h (γ ﹐ M) (wk-wk π) = 0
    metric-lookup {Γ = Γ Cx.∙ X} {Γ' = Γ'} Cx.h (γ ﹐﹝ W ╎ cs ﹞) (wk-wk π) = 0
    metric-lookup {Γ = Γ Cx.∙ X} {Γ' = Γ'} (Cx.t i) ∗ (wk-wk π) = 0
    metric-lookup {Γ = Γ Cx.∙ X} {Γ' = Γ'} (Cx.t i) (γ ﹐ M) (wk-wk π) = metric-lookup i (γ ﹐ M) π
    metric-lookup {Γ = Γ Cx.∙ X} {Γ' = Γ'} (Cx.t i) ((γ ﹐﹝ W ╎ cs ﹞) {π = π'} {wk≡ = wk≡}) (wk-wk π) = metric-lookup i ((γ ﹐﹝ W ╎ cs ﹞) {π = π'} {wk≡ = wk≡}) π

    metric-v̲a̲l̲ : (M : V̲a̲l̲ Γ X) → (γ : Env Γ') → (π : WkEnd Γ Γ') → ℕ
    metric-v̲a̲l̲ (l̲a̲m̲ W) γ π = metric-comp W γ (wk-wk π)
    metric-v̲a̲l̲ (pa̲i̲r̲ M N) γ π = 0
    metric-v̲a̲l̲ u̲n̲i̲t̲ γ π = 0
    metric-v̲a̲l̲ (v̲a̲r̲ i) γ π = 0

    metric-val : (M : Γ ⊢ᵛ X) → (γ : Env Γ') → (π : WkEnd Γ Γ') → ℕ
    metric-val (var i) γ π = suc (metric-lookup i γ π)
    metric-val (lam W) γ π = metric-comp W γ (wk-wk π)
    metric-val (pair M N) γ π = metric-val M γ π + metric-val N γ π
    metric-val (pm M N) γ π = metric-val M γ π + metric-val N γ (wk-wk (wk-wk π))
    metric-val unit γ π = 0

    metric-comp : (W : Γ ⊢ᶜ X) → (γ : Env Γ') → (π : WkEnd Γ Γ') → ℕ
    metric-comp (return M) γ π = suc (metric-val M γ π)
    metric-comp (pm M W) γ π = metric-val M γ π + metric-comp W γ (wk-wk (wk-wk π))
    metric-comp (push W₁ W₂) γ π = metric-comp W₁ γ π + metric-comp W₂ γ (wk-wk π)
    metric-comp (app M N) γ π = metric-val M γ π + metric-val N γ π
    metric-comp (var M) γ π = suc (metric-val M γ π)
    metric-comp (sub W₁ W₂) γ π = metric-comp W₁ γ (wk-wk π) + metric-comp W₂ γ π
-}

 ---------------------------------------------------

{-
  mutual
    metric-lookup : (i : Γ ∋ X) → (γ : Env Γ') → (π : Wk Γ Γ') → ℕ
    metric-lookup Cx.h (γ ﹐ M) (wk-cong π) = metric-v̲a̲l̲ M γ wk-id
    metric-lookup (Cx.t i) (γ ﹐ M) (wk-cong π) = metric-lookup i γ π
    metric-lookup Cx.h (γ ﹐﹝ W ╎ cs ﹞) (wk-cong π) = metric-comp W γ wk-id
    metric-lookup (Cx.t i) (γ ﹐﹝ W ╎ cs ﹞) (wk-cong π) = metric-lookup i γ π
    metric-lookup Cx.h ∗ (wk-wk π) = 0
    metric-lookup Cx.h (γ ﹐ M) (wk-wk π) = 0
    metric-lookup Cx.h (γ ﹐﹝ W ╎ cs ﹞) (wk-wk π) = 0
    metric-lookup (Cx.t i) ∗ (wk-wk π) = 0
    metric-lookup (Cx.t i) (γ ﹐ M) (wk-wk π) = metric-lookup i (γ ﹐ M) π
    metric-lookup (Cx.t i) ((γ ﹐﹝ W ╎ cs ﹞) {π = π'} {wk≡ = wk≡}) (wk-wk π) = metric-lookup i ((γ ﹐﹝ W ╎ cs ﹞) {π = π'} {wk≡ = wk≡}) π

    metric-v̲a̲l̲ : (M : V̲a̲l̲ Γ X) → (γ : Env Γ') → (π : Wk Γ Γ') → ℕ
    metric-v̲a̲l̲ = {!!}
    -- metric-v̲a̲l̲ (l̲a̲m̲ W) γ π = metric-comp W γ (wk-wk π)
    -- metric-v̲a̲l̲ (pa̲i̲r̲ M N) γ π = 0
    -- metric-v̲a̲l̲ u̲n̲i̲t̲ γ π = 0
    -- metric-v̲a̲l̲ (v̲a̲r̲ i) γ π = 0

    metric-val : (M : Γ ⊢ᵛ X) → (γ : Env Γ') → (π : Wk Γ Γ') → ℕ
    metric-val = {!!}
    -- metric-val (var i) γ π = suc (metric-lookup i γ π)
    -- metric-val (lam W) γ π = metric-comp W γ (wk-wk π)
    -- metric-val (pair M N) γ π = metric-val M γ π + metric-val N γ π
    -- metric-val (pm M N) γ π = metric-val M γ π + metric-val N γ (wk-wk (wk-wk π))
    -- metric-val unit γ π = 0

    metric-comp : (W : Γ ⊢ᶜ X) → (γ : Env Γ') → (π : Wk Γ Γ') → ℕ
    metric-comp (return x) γ π = {!!}
    metric-comp (pm (var i) W) γ π = {!!}
    metric-comp (pm (pair M M₁) W) γ π = {!!}
    metric-comp (pm (pm M M₁) W) γ π = {!!}
    --metric-val M γ π + metric-comp W (γ ﹐ {!!} ﹐ {!!}) (wk-cong (wk-cong π))
    metric-comp (push W W₁) γ π = {!!}

    metric-comp (app (var i) N) γ π = {!!} -- metric-val N γ π + metric-lookup i γ {!!}
    metric-comp (app (lam W) N) γ π = metric-val N γ π + metric-comp W (γ ﹐ {!!}) (wk-cong π)
    metric-comp (app (pm M N₁) N₂) γ π = {!!} --metric-comp N₁ (γ ﹐ {!!} ﹐  {!!}) {!!}

    metric-comp (var x) γ π = {!!}
    metric-comp (sub W W₁) γ π = {!!}
    -- metric-comp (return M) γ π = suc (metric-val M γ π)
    -- metric-comp (pm M W) γ π = metric-val M γ π + metric-comp W γ (wk-wk (wk-wk π))
    -- metric-comp (push W₁ W₂) γ π = metric-comp W₁ γ π + metric-comp W₂ γ (wk-wk π)
    -- metric-comp (app M N) γ π = metric-val M γ π + metric-val N γ π
    -- metric-comp (var M) γ π = suc (metric-val M γ π)
    -- metric-comp (sub W₁ W₂) γ π = metric-comp W₁ γ (wk-wk π) + metric-comp W₂ γ π

-}


-----------------------------------------------------

{-

{-
  data MEnv : (Γ : Ctx) → Set where

      ∗       :  MEnv ε

      _﹐_     :  MEnv Γ → (M : V̲a̲l̲  Γ X) → MEnv (Γ ∙ X)

      _﹐﹝_╎_﹞ :  (γ : MEnv Γ) → (W : Γ ⊢ᶜ X) → (cs : CompStack Δ X) → MEnv (Γ ∙ `V)

      _﹐ₙ_     :  MEnv Γ → (n : ℕ) → MEnv (Γ ∙ X)
      -}

  data Ty' : Ty → Set where
    Unit' : Ty' `Unit
    _×'_ _⇒'_ : (Ty' X) -> (Ty' Y) -> (Ty' (X `× Y))
    V' : (Ty' X) -> (Ty' `V)

  variable
    Xₜ : Ty' X
    Yₜ : Ty' Y
    Zₜ : Ty' Z

  data Nmetric : Ty' X → Set where
    m-Unit : ℕ → Nmetric Unit'
    m-V : ℕ → Nmetric Xₜ → Nmetric (V' Xₜ)
    m-⇒ : ℕ → Nmetric Xₜ → Nmetric Yₜ → Nmetric (Xₜ ⇒' Yₜ)
    m-×   : ℕ → Nmetric Xₜ → Nmetric Yₜ → Nmetric (Xₜ ×' Yₜ)

  mutual
    data Ctx' : Set where
      ε'   : Ctx'
      _∙'_ : (ℾ : Ctx') → (Xₜ : Ty' X) → {ic : InCtx ℾ Xₜ} → Ctx'

    data InCtx : Ctx' → Ty' X → Set where
      is-unit : {ℾ : Ctx'} → InCtx ℾ Unit'
      is-× : {ℾ : Ctx'} → {Xₜ : Ty' X} → {Yₜ : Ty' Y} → InCtx ℾ (Xₜ ×' Yₜ)
      is-⇒ : {ℾ : Ctx'} → {Xₜ : Ty' X} → {Yₜ : Ty' Y} → InCtx ℾ (Xₜ ⇒' Yₜ)
      this-V : {ℾ : Ctx'} → {Xₜ : Ty' X} → {ic : InCtx ℾ Xₜ} → InCtx ((ℾ ∙' Xₜ) {ic = ic}) (V' Xₜ)
      next-V : {ℾ : Ctx'} → {Xₜ : Ty' X} → {Yₜ : Ty' Y} → {ic : InCtx ℾ Yₜ} (icx : InCtx ℾ (V' Xₜ)) → (InCtx ((ℾ ∙' Yₜ) {ic = ic}) (V' Xₜ))

  zero-tree : (Xₜ : Ty' X) → Nmetric Xₜ
  zero-tree Unit' = m-Unit 0
  zero-tree (Y ×' Y₁) = m-× 0 (zero-tree Y) (zero-tree Y₁)
  zero-tree (Y ⇒' Y₁) = m-⇒ 0 (zero-tree Y) (zero-tree Y₁)
  zero-tree (V' Xₜ) = m-V 0 (zero-tree Xₜ)

  data Nlist : Ctx' → Set where
    nil : Nlist ε'
    cons : {ℾ : Ctx'} → {Xₜ : Ty' X} → Nlist ℾ → Nmetric Xₜ → {ic : InCtx ℾ Xₜ} → Nlist ((ℾ ∙' Xₜ) {ic = ic})

  toCtx' : Env Γ → Ctx'
  toCtx' {Γ = Γ} ∗ = ε'
  toCtx' {Γ = Γ} (γ ﹐ l̲a̲m̲ x) = {!!}
  toCtx' {Γ = Γ} (γ ﹐ pa̲i̲r̲ M M₁) = {!!}
  toCtx' {Γ = Γ} (γ ﹐ u̲n̲i̲t̲) = {!!}
  toCtx' {Γ = Γ} ((γ ﹐ M) ﹐ v̲a̲r̲ i) = {!!}
  toCtx' {Γ = Γ} (_﹐﹝_╎_﹞ {X = `Unit} γ W cs {π = π} {wk≡ = wk≡} ﹐ v̲a̲r̲ i) = {!!}
  toCtx' {Γ = Γ} (_﹐﹝_╎_﹞ {X = X `× X₁} γ W cs {π = π} {wk≡ = wk≡} ﹐ v̲a̲r̲ i) = {!!}
  toCtx' {Γ = Γ} (_﹐﹝_╎_﹞ {X = X `⇒ X₁} γ W cs {π = π} {wk≡ = wk≡} ﹐ v̲a̲r̲ i) = {!!}
  toCtx' {Γ = Γ} (_﹐﹝_╎_﹞ {X = `V} γ W cs {π = π} {wk≡ = wk≡} ﹐ v̲a̲r̲ i) = {!!}
  --((toCtx' ((_﹐﹝_╎_﹞ {X = X} γ W cs {π = π} {wk≡ = wk≡}))) ∙' {!V'!}) {ic = {!!}}
  toCtx' {Γ = Γ} (γ ﹐﹝ W ╎ cs ﹞) = {!!}


  {-

  toNlist : Env Γ → Nlist Γ
  toNlist {Γ = Γ} ∗ = nil
  toNlist {Γ = Γ Cx.∙ `Unit} (γ ﹐ M) = cons-unit (toNlist γ) (zero-tree Unit')
  toNlist {Γ = Γ Cx.∙ Xₜ `× Yₜ} (γ ﹐ M) = {!cons-× (toNlist γ) (zero-tree (Xₜ ×' Yₜ))!}
  toNlist {Γ = Γ Cx.∙ Xₜ `⇒ Yₜ} (γ ﹐ M) = {!!}
  toNlist {Γ = Γ Cx.∙ `V} (γ ﹐ M) = {!!}
  toNlist {Γ = Γ} (γ ﹐﹝ W ╎ cs ﹞) = {!!}
  -}


{-
  /_/ : Nmetric X → ℕ
  / m-Unit m / = m
  / m-V m n / = m + / n /
  / m-Z m / = m
  / m-⇒ m n n' / = m + / n / + / n' /
  / m-× m n n' / = m + / n / + / n' /

  incr : ℕ → Nmetric X → Nmetric X
  incr n (m-Unit x) = (m-Unit (n + x))
  incr n (m-V x nm) =  m-V (n + x) nm
  incr n (m-Z x) =  m-Z (n + x)
  incr n (m-⇒ x nm nm₁) = m-⇒ (n + x) nm nm₁
  incr n (m-× x nm nm₁) = m-× (n + x) nm nm₁

  sumup : List (Σ[ X ∈ Ty ] Nmetric X) → ℕ
  sumup [] = 0
  sumup (nt ∷ ns) = / proj₂ nt / + (sumup ns)


  -- data CtxId : (Γ : Ctx) → (ns : List (Σ[ X ∈ Ty ] NTree X)) → Set where
  --   ε≡nil  : CtxId ε []
  --   ∙≡cons : {Γ : Ctx} → {n : NTree Y} → {ns : List (Σ[ X ∈ Ty ] NTree X) } → (CtxId Γ ns) → CtxId (Γ ∙ Y) ((Y , n ) ∷ ns)

  -- data Ext : (Γ : Ctx) → (ns : List (Σ[ X ∈ Ty ] NTree X)) → Set where
  --   ext-id  : {ns : List (Σ[ X ∈ Ty ] NTree X)} → (ϖ : CtxId Γ ns) → Ext Γ ns
  --   ext     : {ns : List (Σ[ X ∈ Ty ] NTree X)} → (ϖ : Ext Γ ns) → Ext (Γ ∙ Y) ns

  mutual

    env-conv : (γ : Env Γ) → List (Σ[ X ∈ Ty ] Nmetric X)
    env-conv γ = {!!}

{-
    lookup-conv : (i : Γ ∋ X) → (E : List (Σ[ X ∈ Ty ] NTree X)) → Ext Γ E → List (Σ[ X ∈ Ty ] NTree X)
    lookup-conv Cx.h (n ∷ E) (ext-id ϖ) = [ n ]
    lookup-conv (Cx.t i) (n ∷ E) (ext-id (∙≡cons ϖ)) = lookup-conv i E (ext-id ϖ)
    lookup-conv Cx.h [] (ext ϖ) = []
    lookup-conv Cx.h (x ∷ E) (ext ϖ) = []
    lookup-conv (Cx.t i) [] (ext ϖ) = []
    lookup-conv (Cx.t i) (n ∷ E) (ext ϖ) = lookup-conv i (n ∷ E) ϖ
  -}

    zero-tree : (Y : Ty) → Nmetric Y
    zero-tree `Unit = m-Unit 0
    zero-tree (Y `× Y₁) = m-× 0 (zero-tree Y) (zero-tree Y₁)
    zero-tree (Y `⇒ Y₁) = m-⇒ 0 (zero-tree Y) (zero-tree Y₁)
    zero-tree `V = m-Z 0

    lhs : Nmetric (X `× Y) → Nmetric X
    lhs (m-× x nm nm₁) = nm

    rhs : Nmetric (X `× Y) → Nmetric Y
    rhs (m-× x nm nm₁) = nm₁

    tg : Nmetric (X `⇒ Y) → Nmetric Y
    tg (m-⇒ x nm nm₁) = nm₁

    lookup-conv : (i : Γ ∋ Y) → (E : List (Σ[ X ∈ Ty ] Nmetric X)) → Wkn Γ E → Nmetric Y

    lookup-conv {Y = `Unit} Cx.h ((Y , n) ∷ ne) (wkn-cong ϖ) = incr 1 n
    lookup-conv {Y = `Unit} (Cx.t i) ((Y , n) ∷ ne) (wkn-cong ϖ) = lookup-conv {Y = `Unit} i ne ϖ

    lookup-conv {Y = `Unit} Cx.h [] (wkn-cons ϖ) = m-Unit 0
    lookup-conv {Y = `Unit} (Cx.t i) [] (wkn-cons ϖ) = m-Unit 0

    lookup-conv {Y = `Unit} Cx.h ((Y , n) ∷ ne) (wkn-cons ϖ) = m-Unit 0
    lookup-conv {Y = `Unit} (Cx.t i) ((Y , n) ∷ ne) (wkn-cons ϖ) = lookup-conv {Y = `Unit} i ((Y , n) ∷ ne) ϖ

    lookup-conv {Y = Y `× Y₁} Cx.h ((Y₂ , n) ∷ ne) (wkn-cong ϖ) = incr 1 n
    lookup-conv {Y = Y `× Y₁} (Cx.t i) ((Y₂ , n) ∷ ne) (wkn-cong ϖ) = lookup-conv {Y = Y `× Y₁} i ne ϖ

    lookup-conv {Y = Y `× Y₁} Cx.h [] (wkn-cons ϖ) = zero-tree (Y `× Y₁)
    lookup-conv {Y = Y `× Y₁} (Cx.t i) [] (wkn-cons ϖ) = zero-tree (Y `× Y₁)

    lookup-conv {Y = Y `× Y₁} Cx.h (x ∷ E) (wkn-cons ϖ) = zero-tree (Y `× Y₁)
    lookup-conv {Y = Y `× Y₁} (Cx.t i) (x ∷ E) (wkn-cons ϖ) = lookup-conv {Y = Y `× Y₁} i (x ∷ E) ϖ

    lookup-conv {Y = Y `⇒ Y₁} Cx.h ((Y₂ , n) ∷ ne) (wkn-cong ϖ) = incr 1 n
    lookup-conv {Y = Y `⇒ Y₁} (Cx.t i) ((Y₂ , n) ∷ ne) (wkn-cong ϖ) = lookup-conv {Y = Y `⇒ Y₁} i ne ϖ

    lookup-conv {Y = Y `⇒ Y₁} Cx.h [] (wkn-cons ϖ) = zero-tree (Y `⇒ Y₁)
    lookup-conv {Y = Y `⇒ Y₁} (Cx.t i) [] (wkn-cons ϖ) = zero-tree (Y `⇒ Y₁)

    lookup-conv {Y = Y `⇒ Y₁} Cx.h ((Y₂ , n) ∷ E) (wkn-cons ϖ) = zero-tree (Y `⇒ Y₁)
    lookup-conv {Y = Y `⇒ Y₁} (Cx.t i) ((Y₂ , n) ∷ E) (wkn-cons ϖ) = lookup-conv {Y = Y `⇒ Y₁} i ((Y₂ , n) ∷ E) ϖ

    lookup-conv {Y = `V} Cx.h ((Y , n) ∷ ne) (wkn-cong ϖ) = incr 1 n
    lookup-conv {Y = `V} (Cx.t i) ((Y , n) ∷ ne) (wkn-cong ϖ) = lookup-conv {Y = `V} i ne ϖ

    lookup-conv {Y = `V} Cx.h [] (wkn-cons ϖ) = m-Z 0
    lookup-conv {Y = `V} (Cx.t i) [] (wkn-cons ϖ) = m-Z 0

    lookup-conv {Y = `V} Cx.h ((Y , n) ∷ E) (wkn-cons ϖ) = m-Z 0
    lookup-conv {Y = `V} (Cx.t i) ((Y , n) ∷ E) (wkn-cons ϖ) = lookup-conv {Y = `V} i ((Y , n) ∷ E) ϖ


    val-conv : (M : Val Γ Y) → (E : List (Σ[ X ∈ Ty ] Nmetric X)) → Wkn Γ E → Nmetric Y

    val-conv {Y = `Unit} (var {A = A} i) [] ϖ = m-Unit 0
    val-conv {Y = A₁ `× A₂} (var {A = A} Cx.h) [] (wkn-cons ϖ) = zero-tree (A₁ `× A₂) --m-× (val-conv {Y = A₁} (var h) [] (wkn-cons ϖ)) (val-conv {Y = A₂} (var h) [] (wkn-cons ϖ))
    val-conv {Y = A₁ `× A₂} (var {A = A} (Cx.t i)) [] (wkn-cons ϖ) = zero-tree (A₁ `× A₂) --val-conv {Y = A₁ `× A₂} (var {A = A} i) [] ϖ
    val-conv {Y = A₁ `⇒ A₂} (var {A = A} i) [] ϖ = zero-tree (A₁ `⇒ A₂)
    val-conv {Y = `V} (var {A = A} i) [] ϖ = m-Z 0

    val-conv unit [] ϖ = m-Unit 0

    val-conv {Y = `Unit} (var {A = A} i) (x ∷ E) ϖ = lookup-conv i (x ∷ E) ϖ
    val-conv {Y = A₁ `× A₂} (var {A = A} Cx.h) (x ∷ E) ϖ = lookup-conv h (x ∷ E) ϖ
    val-conv {Y = A₁ `× A₂} (var {A = A} (Cx.t i)) (x ∷ E) ϖ = lookup-conv (t i) (x ∷ E) ϖ
    val-conv {Y = A₁ `⇒ A₂} (var {A = A} i) (x ∷ E) ϖ = lookup-conv i (x ∷ E) ϖ
    val-conv {Y = `V} (var {A = A} i) (x ∷ E) ϖ = lookup-conv i (x ∷ E) ϖ

    val-conv (lam W) [] ϖ = {!!}
    val-conv (lam W) (x ∷ E) ϖ = {!!}

    val-conv (pair M N) [] ϖ = m-× 0 (val-conv M [] ϖ) (val-conv N [] ϖ)
    val-conv (pair M N) (x ∷ E) ϖ = m-× 0 (val-conv M (x ∷ E) ϖ) (val-conv N (x ∷ E) ϖ)

    val-conv {Y = `Unit} (pm {A = A} {B = B} M N) [] ϖ = incr (/ val-conv M [] ϖ /) (val-conv N ((B , rhs ((val-conv M ) [] ϖ)) ∷ (A , lhs ((val-conv M ) [] ϖ)) ∷ []) (wkn-cong (wkn-cong ϖ)))
    val-conv {Y = `Unit} (pm {A = A} {B = B} M N) (x ∷ E) ϖ = incr (/ val-conv M (x ∷ E) ϖ /) (val-conv N ((B , rhs ((val-conv M ) (x ∷ E) ϖ)) ∷ (A , lhs ((val-conv M ) (x ∷ E) ϖ)) ∷ x ∷ E) (wkn-cong (wkn-cong ϖ)))

    val-conv {Y = Y `× Y₁} (pm {A = A} {B = B} M N) [] ϖ = incr (/ val-conv M [] ϖ /) (val-conv N ((B , rhs ((val-conv M ) [] ϖ)) ∷ (A , lhs ((val-conv M ) [] ϖ)) ∷ []) (wkn-cong (wkn-cong ϖ)))
    val-conv {Y = Y `× Y₁} (pm {A = A} {B = B} M N) (x ∷ E) ϖ = incr (/ val-conv M (x ∷ E) ϖ /) (val-conv N ((B , rhs ((val-conv M ) (x ∷ E) ϖ)) ∷ (A , lhs ((val-conv M ) (x ∷ E) ϖ)) ∷ x ∷ E) (wkn-cong (wkn-cong ϖ)))

    val-conv {Y = Y `⇒ Y₁} (pm {A = A} {B = B} M N) [] ϖ = incr (/ val-conv M [] ϖ /) (val-conv N ((B , rhs ((val-conv M ) [] ϖ)) ∷ (A , lhs ((val-conv M ) [] ϖ)) ∷ []) (wkn-cong (wkn-cong ϖ)))
    val-conv {Y = Y `⇒ Y₁} (pm {A = A} {B = B} M N) (x ∷ E) ϖ = incr (/ val-conv M (x ∷ E) ϖ /) (val-conv N ((B , rhs ((val-conv M ) (x ∷ E) ϖ)) ∷ (A , lhs ((val-conv M ) (x ∷ E) ϖ)) ∷ x ∷ E) (wkn-cong (wkn-cong ϖ)))

    val-conv {Y = `V} (pm {A = A} {B = B} M N) [] ϖ = incr (/ val-conv M [] ϖ /) (val-conv N ((B , rhs ((val-conv M ) [] ϖ)) ∷ (A , lhs ((val-conv M ) [] ϖ)) ∷ []) (wkn-cong (wkn-cong ϖ)))
    val-conv {Y = `V} (pm {A = A} {B = B} M N) (x ∷ E) ϖ = incr (/ val-conv M (x ∷ E) ϖ /) (val-conv N ((B , rhs ((val-conv M ) (x ∷ E) ϖ)) ∷ (A , lhs ((val-conv M ) (x ∷ E) ϖ)) ∷ x ∷ E) (wkn-cong (wkn-cong ϖ)))


    val-conv unit (x ∷ E) ϖ = m-Unit 0

    comp-conv : (W : Comp Γ Y) → (E : List (Σ[ X ∈ Ty ] Nmetric X)) → Wkn Γ E → Nmetric Y

    comp-conv (return M) E ϖ = incr 1 (val-conv M E ϖ)
    comp-conv (pm {A = A} {B = B} M W) E ϖ = incr (/ val-conv M E ϖ /) (comp-conv W ((B , rhs (val-conv M E ϖ)) ∷ (A , lhs (val-conv M E ϖ)) ∷ E) (wkn-cong (wkn-cong ϖ)))
    comp-conv (push {A = A} W₁ W₂) E ϖ = incr (/ comp-conv W₁ E ϖ /) (comp-conv W₂ ((A , comp-conv W₁ E ϖ) ∷ E) (wkn-cong ϖ))
    comp-conv (app M N) E ϖ = incr (/ val-conv N E ϖ /) (tg (val-conv M E ϖ))

    comp-conv (var {A = A} M) E ϖ with A | val-conv M E ϖ
    ... | A | m-V x z = {!incr (suc x) z!}
    ... | `Unit | m-Z x = zero-tree `Unit
    ... | A `× A₁ | m-Z x = zero-tree (A `× A₁)
    ... | A `⇒ A₁ | m-Z x = zero-tree (A `⇒ A₁)
    ... | `V | m-Z x = m-Z 0
    comp-conv (sub W₁ W₂) E ϖ = {!!}
    -}
-}

-------------------------------


{-
  -- {-# TERMINATING #-}
  mutual

    app-eval-rec :   (M : Γ' ⊢ᵛ X `⇒ Y) → (N : V̲a̲l̲ Γ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ Y) → (πₓ : Wk Γ Δ)
                   → (wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → (n : ℕ) → ((metric-val (wk-val π M) γ wk-Γ) + (metric-v̲a̲l̲ N γ wk-Γ) ≤ n)
                   → CompSteps ((∙⟨ (a̲pp (wk-val π M) N) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    app-eval-rec (var i) N γ π cs πₓ wk≡₀ zero ()
    app-eval-rec (var i) N γ π cs πₓ wk≡₀ (suc n) m≤n with lookup (wk-mem π i) γ
    -- app-eval-rec (var i) N γ π cs πₓ wk≡₀ n with lookup (wk-mem π i) γ
    ... | steps i>>T (found-lam {X = X} {W = W} {γ = γ₁}) i≡T π₁ _ w≡γ _ with app-eval-rec (lam W) N γ π₁ cs πₓ wk≡₀ n {!!}
    ... | steps {T = T} W>WT HT S≡T =

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

  --lem2'' : (i : Γ ∋ X `⇒ Y) → (γ : Env Γ) → (metric-comp (wk-comp (wk-cong (lookup-wk i γ)) (lookup-term i γ)) (lookup-env i γ) (wk-wk (lookup-wke i γ))) ≡ (metric-lookup i γ wk-Γ)
  --lem-wk-comp : (W : Comp (Γ ⊕ Ψ) Y) → (γ : Env Γ) → (π : Wk Δ Ψ) → metric-comp (wk-comp (wk-⊕ wk-id π) W) γ (wkE-wks wk-Γ Δ) ≡ metric-comp W γ (wkE-wks wk-Γ Ψ)
                  where
                  llll : metric-comp (wk-comp (wk-cong π₁) W) γ (wk-wk wk-Γ) ≡ metric-lookup (wk-mem π i) γ WkEnd.wk-Γ
                  00llll = metric-comp (wk-comp (wk-cong π₁) W) γ (wk-wk wk-Γ)
                  llll = metric-comp (wk-comp (wk-cong π₁) W) γ (wk-wk wk-Γ)
                          ≡⟨ refl ⟩
                          metric-val (wk-val π₁ (lam W)) γ wk-Γ
                          ≡⟨ {!refl!} ⟩
                          metric-comp (wk-comp (wk-cong (lookup-wk (wk-mem π i) γ)) (lookup-term (wk-mem π i) γ)) γ (wk-wk wk-Γ)
                          ≡⟨ {!refl!} ⟩
                          metric-lookup (wk-mem π i) γ (wkE-wks wk-Γ ε)
                          ≡⟨  refl ⟩
                          metric-lookup (wk-mem π i) γ WkEnd.wk-Γ ∎ --lemx-comp W γ

    -- TRICKY (try this first)
    app-eval-rec (lam W) N γ π cs πₓ wk≡₀ n m≤n with comp-eval-rec W (γ ﹐ N) (wk-cong π) cs (wk-wk πₓ) wk≡₀ n {!!}
    ... | steps {T = T} W>WT HT S≡T =

                  steps

                     ( ∙⟨ a̲pp (wk-val π (lam W)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-lam ⟩ W>WT)

                     HT

                     S≡T

    -- TRICKY
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
                      {!!}
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
                  → (wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → (n : ℕ) → ((metric-comp (wk-comp π W) γ wk-Γ) ≤ n)
                  → CompSteps ((∘⟨ wk-comp π W ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    comp-eval-rec (return {A = X} M) γ π ◻ πₓ wk≡₀ n m≤n with val-eval-rec {X = X} M γ π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ =

                 steps

                    (∘⟨ wk-comp π (return M) ⊰ γ ╎ ◻ ⟩ →ᶜ⟨ ∘return M>T ⟩ (∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ ◻ ⟩ ◼))

                    ret

                    (cong (λ x → (η x) k₀) M≡T)

    -- TRICKY
    comp-eval-rec (return {A = X} M) γ π ((M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁}) πₓ wk≡₀ zero ()
    comp-eval-rec (return {A = X} M) γ π ((M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁}) πₓ wk≡₀ (suc n) m≤n with val-eval-rec {X = X} M γ π
    -- comp-eval-rec (return {A = X} M) γ π ((M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁}) πₓ wk≡₀ n with val-eval-rec {X = X} M γ π
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
                   {!!}
    ... | steps {T = ∙⟨ r̲e̲t̲u̲r̲n̲  M₂ ⊰ γ₂ ╎ ◻ ⟩} M'>T ret S≡T =

                   steps

                   (∘⟨ wk-comp π (return M) ⊰ γ ╎ (M' ⊲ γ' ⦂⦂ cs) ⟩
                    →ᶜ⟨ ∘return {wk≡ₓ' = ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ
                                         ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ)
                                         ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ
                                         ≡⟨ wk≡₀ ⟩ ⟦ γ' ⟧ᴱ ∎} M>T ⟩ ∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ M' ⊲ γ' ⦂⦂ cs ⟩
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

    -- TRICKY
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
                     {!!}
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

    -- EASY
    comp-eval-rec (push W V) γ π cs πₓ wk≡₀ n m≤n with comp-eval-rec W γ π (((wk-comp (wk-cong π) V) ⊲ γ ⦂⦂ cs) {wk≡ = wk≡₀}) wk-id refl n {!!}
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

    -- BY VAL LEMMA
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
                      {!!}
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

    -- BY VAL LEMMA + LOOKUP LEMMA
    comp-eval-rec (var {A = X} M) γ π cs πₓ wk≡₀ zero ()
    comp-eval-rec (var {A = X} M) γ π cs πₓ wk≡₀ (suc n) m≤n with val-eval-rec {X = `V} M γ π
    -- comp-eval-rec (var {A = X} M) γ π cs πₓ wk≡₀ n with val-eval-rec {X = `V} M γ π
    ... | steps {T = ∙ ((⭭ v̲a̲r̲ i) ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ with lookup i γ₁
    ... | steps i>>T (found-comp {X = X} {W = W'} {γ = γ'} {cs = cs'} {π = πᶜ} {wk≡ = wk≡c}) i≡T π₂ _ w≡γ _ with
                    comp-eval-rec
                     W'
                     γ'
                     wk-id
                     cs'
                     πᶜ
                     wk≡c
                     n
                     {!!}
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

    -- EASY
    comp-eval-rec (sub W V) γ π cs πₓ wk≡₀ n m≤n with comp-eval-rec W ((γ ﹐﹝ wk-comp π V ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡₀}) (wk-cong π) cs (wk-wk πₓ) wk≡₀ n {!!}
    ... | steps {T = T} W>WT HT S≡T =

                steps

                    (∘⟨ sub (wk-comp (wk-cong π) W) (wk-comp π V) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘sub ⟩ W>WT)

                    HT

                    S≡T

{-
    comp-eval : (W : ε ⊢ᶜ R₀) → CompSteps ((∘⟨ wk-comp wk-id W ⊰ ∗ ╎ ◻ ⟩) {π = wk-id} {wk≡ = refl})
    comp-eval W = comp-eval-rec W ∗ wk-id ◻ wk-id refl zero -- zero should be replaced with a counter of remaining vars and pushes

---- Examples

postulate k₀ : ⟦ `Unit ⟧ → R

open VMain {R₀ = `Unit} k₀
open CMain {R₀ = `Unit} k₀

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

-- s/\(PartialTerm\.\|ValStack\.\|Env\.\|V̲a̲l̲\.\|CompStack\.\|ValStack\.\|ValState\.\|_↠ᵛ_\.\|_→ᵛ_\.\|_→ᴸ\*_\.\|_→ᴸ_\.\|LookupState\.\|C̲o̲m̲p.\)//g


-- call agda2-compute-normalised in the hole below

_ : comp-eval ex7 ≡

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
      ret (trans (cong (λ k → k tt) (extensionality (λ z → refl))) refl)

_ = refl
-}

-}
