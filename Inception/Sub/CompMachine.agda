module Inception.Sub.CompMachine (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)
open Eq.≡-Reasoning using (step-≡-⟩; step-≡-∣; step-≡-⟨; _∎; step-≡)

open import Relation.Binary.Reasoning.Syntax

open import Inception.Sub.Contr
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

        -- ∙app-var   :     {i : Γ ∋ (Z' `⇒ Z)} → {N : V̲a̲l̲ Γ Z'} → {γ : Env Γ} → {cs : CompStack Δ Z} → {πₓ : Wk Γ Δ} → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
        --                → {W : (Γ' ∙ Z') ⊢ᶜ Z} → {γ' : Env Γ'}
        --                → (⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ _﹐_ γ' (l̲a̲m̲ W) ⟩) → (πᵥ : Wk Γ Γ')
        --                → (T≤S : (csn : List (Σ ℕ (λ x → ℕ))) → m-⇒ 1 (count-in-comp h W) (comp-metric W (proj₁ (env-metric γ')) (Wkn.wkn-cons (proj₂ (env-metric γ'))) csn)
        --                   ≤ᴹ lookup-metric i (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn) -- to prove termination
        --                → (θ : Wke πᵥ (proj₂ (env-metric γ)) (proj₂ (env-metric γ'))) -- to prove termination
        --              ----------------------------------------------------------------
        --                →    ((∙⟨ a̲pp (var i) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ})
        --                  →ᶜ ((∙⟨ a̲pp (wk-val πᵥ (lam W)) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ})

        ∙app-var   :     {i : Γ ∋ (Z' `⇒ Z)} → {N : V̲a̲l̲ Γ Z'} → {γ : Env Γ} → {cs : CompStack Δ Z} → {πₓ : Wk Γ Δ} → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → {W : (Γ' ∙ Z') ⊢ᶜ Z} → {γ' : Env Γ'}
                       → (⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ _﹐_ γ' (l̲a̲m̲ W) ⟩) → (πᵥ : Wk Γ Γ')
                       → (T≤S : (csn : List CTerm) → m-⇒ 1 (inj₁ (contr-comp W)) (comp-metric W (proj₁ (env-metric γ')) (Wkn.wkn-cons (proj₂ (env-metric γ'))) csn)
                          ≤ᴹ lookup-metric i (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn) -- to prove termination
                       → (θ : Wke πᵥ (proj₂ (env-metric γ)) (proj₂ (env-metric γ'))) -- to prove termination
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


  -------------------------------

  botCtx : ValStack non-empty T◾ → Ctx
  botCtx ((_⊲_∷_) {Γ = Γ} _ _ □) = Γ
  botCtx ((x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})) {↥ = ↥}) = botCtx ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})

  botEnv : (S : ValStack non-empty T◾) → Env (botCtx S)
  botEnv ((_⊲_∷_) {Γ = Γ} _ γ □) = γ
  botEnv ((x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})) {↥ = ↥}) = botEnv ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})

  botTerm : (S : ValStack non-empty T◾) → PartialTerm (botCtx S) (T◾)
  botTerm ((_⊲_∷_) {Γ = Γ} M γ □ {↥ = 🗆}) = M
  botTerm ((x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})) {↥ = ↥}) = botTerm ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})

-------------------------------------------------------------------------------------------------

  {-
  ≤ᶜˢⁿ-decr : {csn₁ csn₂ : List (ℕ × ℕ)} → (n₁ ≤ n₂) → csn₁ ≤ᶜˢⁿ csn₂ → csn-to-nat₀ n₁ csn₁ ≤ csn-to-nat₀ n₂ csn₂
  ≤ᶜˢⁿ-decr {n₁ = n₁} {n₂ = n₂} n₁≤n₂ ([c≤c] {csn = csn}) = csn-decr n₁≤n₂ csn
  ≤ᶜˢⁿ-decr {n₁ = n₁} {n₂ = n₂} n₁≤n₂ ([s≤s] n₃≤n₄ c₁≤c₂) =
    let
      m₁≤m₂ = +-≤-cong n₃≤n₄ (*-≤-cong n₁≤n₂ ≤-refl)
    in
      +-≤-cong m₁≤m₂ (≤ᶜˢⁿ-decr m₁≤m₂ c₁≤c₂)
  -}

-------------------------------------------------------------------------------------------------
  ≤ᴹ-p1 : {nm₁ nm₂ : TermMetric (X `⇒ Y)} → (nm₁ ≤ᴹ nm₂) → (p1 nm₁) ≤ (p1 nm₂)
  ≤ᴹ-p1 (≤-⇒ n₁≤n₂ nm₁≤nm₂) = n₁≤n₂

  +-p1-incr : (n : ℕ) → (nm : TermMetric (X `⇒ Y)) → p1 (incr n nm) ≡ n + (p1 nm)
  +-p1-incr n (m-⇒ {Y = Y} {X = X} m cnt nm) with incr n (m-⇒ {Y = Y} {X = X} m cnt nm)
  ... | x = refl

  -- ≡-p2-incr : (n : ℕ) → (nm : TermMetric (X `⇒ Y)) → p2 (incr n nm) ≡ p2 nm
  -- ≡-p2-incr n (m-⇒ m cnt nm) = refl
  --{-# REWRITE ≡-p2-incr #-}

  ≡-p3-incr : (n : ℕ) → (nm : TermMetric (X `⇒ Y)) → p3 (incr n nm) ≡ p3 nm
  ≡-p3-incr n (m-⇒ m cnt nm) = refl


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
  ≤ᴹ⇒≤ (≤-V n₁≤n₂ w₁≤w₂) = +-≤-cong n₁≤n₂ w₁≤w₂ --+-≤-cong (+-≤-cong n₁≤n₂ w₁≤w₂) (≤ᶜˢⁿ-decr w₁≤w₂ c₁≤c₂)
  ≤ᴹ⇒≤ (≤-⇒ n₁≤n₂ nm₁≤nm₂) = +-≤-cong n₁≤n₂ (≤ᴹ⇒≤ nm₁≤nm₂)
  ≤ᴹ⇒≤ (≤-× n₁≤n₂ nm₁≤nm₃ nm₂≤nm₄) = +-≤-cong (+-≤-cong n₁≤n₂ (≤ᴹ⇒≤ nm₁≤nm₃)) (≤ᴹ⇒≤ nm₂≤nm₄)

{-
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
-}
-------------------------------------------------------------------------------------------------

{-
  cs-to-csf : (cs : CompStack Δ Z) → (ℕ → ℕ)
  cs-to-csf ◻ w = 0
  cs-to-csf ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡}) w =
    let
      csf = cs-to-csn cs
      IH = env-metric γ
    in
      ⟪ comp-metric W (proj₁ IH) (wkn-cons (proj₂ IH)) csn ⟫
  -}

  compstate-metric : CompState → ℕ
  compstate-metric ((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π}) =
    let
      csn = cs-to-csn cs
      e = env-metric γ
      w = λ c → ⟪ comp-metric W (proj₁ e) (proj₂ e) c ⟫
    in
      (w csn) + csn-to-nat₀ w csn
  compstate-metric ((∙⟨ W ⊰ γ ╎ cs ⟩) {π = π}) =
    let
      csn = cs-to-csn cs
      e = env-metric γ
      w = λ c → ⟪ c̲o̲m̲p-metric W (proj₁ e) (proj₂ e) c ⟫
    in
      w csn + csn-to-nat₀ w csn

  partial-term-metric : PartialTerm Γ X → (E : List (Σ[ X ∈ Ty ] (List CTerm → TermMetric X))) → Wkn Γ E → List CTerm → ℕ
  partial-term-metric (⭭ M) E ϖ csn = ⟪ v̲a̲l̲-metric M E ϖ csn ⟫
  partial-term-metric (⇡ M) E ϖ csn = ⟪ val-metric M E ϖ csn ⟫
  partial-term-metric (⇡ᴹ M N) E ϖ csn = ⟪ val-metric (pm M N) E ϖ csn ⟫
  partial-term-metric (⇡ᴸ LHS RHS) E ϖ csn = ⟪ val-metric (pair LHS RHS) E ϖ csn ⟫
  partial-term-metric (⇡ᴿ LHS RHS) E ϖ csn = ⟪ val-metric (pair (toVal LHS) RHS) E ϖ csn ⟫

{-
  valstate-metric : ValState X → ℕ → List (ℕ × ℕ) → ℕ
  valstate-metric (∘ S) w csn =
    let
      e = env-metric (botEnv S)
      m = partial-term-metric (botTerm S) (proj₁ e) (proj₂ e) csn
    in
      (w + m) + (csn-to-nat₀ (w + m) csn)
  valstate-metric (∙ S) w csn =
    let
      e = env-metric (botEnv S)
      m = partial-term-metric (botTerm S) (proj₁ e) (proj₂ e) csn
    in
      (w + m) + (csn-to-nat₀ (w + m) csn)
-}

  valstate-metric : ValState X → List CTerm → ℕ
  valstate-metric (∘ S) csn =
    let
      e = env-metric (botEnv S)
    in
      partial-term-metric (botTerm S) (proj₁ e) (proj₂ e) csn
  valstate-metric (∙ S) csn =
    let
      e = env-metric (botEnv S)
    in
       partial-term-metric (botTerm S) (proj₁ e) (proj₂ e) csn

-------------------------------------------------------------------------------------------------

  -- wk-e : (π : Wk Γ Δ) → {E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))} → (ϖ : Wkn Δ E) → Wkn Γ E
  -- wk-e wk-ε ϖ = ϖ
  -- wk-e (wk-cong π) (wkn-cong ϖ) = wkn-cong (wk-e π ϖ)
  -- wk-e (wk-cong π) (wkn-cons ϖ) = wkn-cons (wk-e π ϖ)
  -- wk-e (wk-wk π) ϖ = wkn-cons (wk-e π ϖ)

  -- wk-e-id : {E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))} → (ϖ : Wkn Γ E) → wk-e wk-id ϖ ≡ ϖ
  -- wk-e-id {Γ = Cx.ε} ϖ = refl
  -- wk-e-id {Γ = Γ Cx.∙ x} (wkn-cong ϖ) = cong wkn-cong (wk-e-id ϖ)
  -- wk-e-id {Γ = Γ Cx.∙ x} (wkn-cons ϖ) = cong wkn-cons (wk-e-id ϖ)

-------------------------------------------------------------------------------------------------
  {-
  comp-wk-e-lemma : (W : Comp Γ X) → (E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))) → (ϖ : Wkn Γ E) → (π : Wk Δ Γ) → (csn : List (ℕ × ℕ))
              → comp-metric W E ϖ csn ≡ comp-metric (wk-comp π W) E (wk-e π ϖ) csn
  comp-wk-e-lemma {Γ = Γ} M E ϖ π csn = {!!}

  v̲a̲l̲-wk-e-lemma : (M : V̲a̲l̲ Γ X) → (E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))) → (ϖ : Wkn Γ E) → (π : Wk Δ Γ) → (csn : List (ℕ × ℕ))
              → v̲a̲l̲-metric M E ϖ csn ≡ v̲a̲l̲-metric (wk-v̲a̲l̲ π M) E (wk-e π ϖ) csn
  v̲a̲l̲-wk-e-lemma {Γ = Γ} M E ϖ π csn = {!!}


  comp-wkn-lemma :   {x : Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X)} → (W : Comp Γ X) → (E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))) → (ϖ : Wkn Γ E) → (csn : List (ℕ × ℕ))
              → comp-metric W E ϖ csn ≡ comp-metric (wk-comp (wk-wk wk-id) M) (x ∷ E) (wkn-cong ϖ) csn
  comp-wkn-lemma W E ϖ csn = {!!}

  v̲a̲l̲-wkn-lemma : {x : Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X)} → (M : V̲a̲l̲ Γ X) → (E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))) → (ϖ : Wkn Γ E) → (csn : List (ℕ × ℕ))
              → v̲a̲l̲-metric M E ϖ csn ≡ v̲a̲l̲-metric (wk-v̲a̲l̲ (wk-wk wk-id) M) (x ∷ E) (wkn-cong ϖ) csn
  v̲a̲l̲-wkn-lemma {Γ = Cx.ε} {x = x} (l̲a̲m̲ W) E wkn-nil csn =
    let
      a1 = comp-wk-e-lemma {Γ = ε} (wk-comp {!!} W) (x ∷ []) {!!} {!!} csn
    in
      {!!} --rewrite comp-wkn-lemma {Γ = ε} {x = x} W E wkn-nil csn = {!!}
  v̲a̲l̲-wkn-lemma {Γ = Cx.ε} {x = x} (pa̲i̲r̲ M₁ M₂) E wkn-nil csn rewrite v̲a̲l̲-wkn-lemma {Γ = ε} {x = x} M₁ E wkn-nil csn | v̲a̲l̲-wkn-lemma {Γ = ε} {x = x} M₂ E wkn-nil csn = refl
  v̲a̲l̲-wkn-lemma {Γ = Cx.ε} {x = x} u̲n̲i̲t̲ E wkn-nil csn = refl
  v̲a̲l̲-wkn-lemma {Γ = Γ Cx.∙ x₁} {x = x} M E ϖ csn = {!!}
  -}

  {-
  lookup-wkn-lemma : {x : Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X)} → (i : Γ ∋ X) → (Eₚ E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X)))
              → (ϖ : Wkn Γ E) → (ϖ' : Wkn Γ (Eₚ ++ E)) → (π : Wk Δ Γ) → (csn : List (ℕ × ℕ))
              → lookup-metric i E ϖ csn ≡ lookup-metric (wk-mem π i) (Eₚ ++ E) (wk-e π ϖ') csn
  lookup-wkn-lemma {Γ = Γ} {x = x} Cx.h [] E ϖ ϖ' (wk-cong π) csn = {!!}
  lookup-wkn-lemma {Γ = Γ} {x = x} Cx.h [] E ϖ ϖ' (wk-wk π) csn = {!!}
  lookup-wkn-lemma {Γ = Γ} {x = x} Cx.h (x₁ ∷ Eₚ) E ϖ ϖ' π csn = {!!}
  lookup-wkn-lemma {Γ = Γ} {x = x} (Cx.t i) Eₚ E ϖ ϖ' π csn = {!!}

  mutual

    comp-wkn-lemma : {x : Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X)} → (W : Comp Γ X) → (Eₚ E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X)))
                → (ϖ : Wkn Γ E) → (ϖ' : Wkn Γ (Eₚ ++ E)) → (π : Wk Δ Γ) → (csn : List (ℕ × ℕ))
                → comp-metric W E ϖ csn ≡ comp-metric (wk-comp π W) (Eₚ ++ E) (wk-e π ϖ') csn
    comp-wkn-lemma {Γ = Γ} {x = x} W Eₚ E ϖ ϖ' π csn = {!!}

    v̲a̲l̲-wkn-lemma : {x : Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X)} → (M : V̲a̲l̲ Γ X) → (Eₚ E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X)))
                → (ϖ : Wkn Γ E) → (ϖ' : Wkn Γ (Eₚ ++ E)) → (π : Wk Δ Γ) → (csn : List (ℕ × ℕ))
                → v̲a̲l̲-metric M E ϖ csn ≡ v̲a̲l̲-metric (wk-v̲a̲l̲ π M) (Eₚ ++ E) (wk-e π ϖ') csn
    v̲a̲l̲-wkn-lemma {Γ = Γ} {x = x} (l̲a̲m̲ W) Eₚ E ϖ ϖ' π csn = {!!}
    v̲a̲l̲-wkn-lemma {Γ = Γ} {x = x} (pa̲i̲r̲ M₁ M₂) Eₚ E ϖ ϖ' π csn rewrite v̲a̲l̲-wkn-lemma {Γ = Γ} {x = x} M₁ Eₚ E ϖ ϖ' π csn | v̲a̲l̲-wkn-lemma {Γ = Γ} {x = x} M₂ Eₚ E ϖ ϖ' π csn = refl
    v̲a̲l̲-wkn-lemma {Γ = Γ} {x = x} u̲n̲i̲t̲ Eₚ E ϖ ϖ' π csn = refl
    v̲a̲l̲-wkn-lemma {Γ = Γ} {x = x} (v̲a̲r̲ i) Eₚ E ϖ ϖ' π csn = {!!}
    -}

---------------------------------------------------------------------------------------------
-- OBSOLTE
{-
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
-}
---------------------------------------------------------------------------------------------

{-
  v̲a̲l̲-wke-lemma (l̲a̲m̲ W) E E' π ϖ ϖ' θ csn
      rewrite
          comp-wke-lemma W E E' (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ) csn
        | wk-comp-count-eq (wk-cong π) h W
        = {!!}

  TermMetric.m-⇒ 1 (inj₁ (Γ' ∙ X , W))
  (comp-metric (wk-comp (wk-cong π) W) E (Wkn.wkn-cons ϖ) csn)
  ≡
  TermMetric.m-⇒ 1 (inj₁ (Γ ∙ X , wk-comp (wk-cong π) W))
  (comp-metric (wk-comp (wk-cong π) W) E (Wkn.wkn-cons ϖ) csn)

csn : List (Σ ℕ (λ x → ℕ))
θ   : Wke π ϖ ϖ'
ϖ'  : Wkn Γ' E'
ϖ   : Wkn Γ E
E'  : List (Σ Ty (λ X₁ → List (Σ ℕ (λ x → ℕ)) → TermMetric X₁))
E   : List (Σ Ty (λ X₁ → List (Σ ℕ (λ x → ℕ)) → TermMetric X₁))
π   : Wk Γ Γ'
W   : Comp (Γ' ∙ X) Y
Y   : Ty   (not in scope)
X   : Ty   (not in scope)
Γ   : Ctx   (not in scope)
Γ'  : Ctx   (not in scope)
k₀  : ⟦ R₀ ⟧ → R
R₀  : Ty
R   : Set
-}

--  fun-eq : (W : Comp (Γ' ∙ X) Y) → (π : Wk Γ Γ') → (nm : TermMetric Y)

---------------------------------------------------------------------------------------------

  wke-z-l : {e : (Σ[ X ∈ Ty ] (List CTerm → TermMetric X))} {E' : List (Σ[ X ∈ Ty ] (List CTerm → TermMetric X))} {π : Wk Γ Γ'} {ϖ : Wkn Γ []} {ϖ' : Wkn Γ' (e ∷ E')}
            → Wke π ϖ ϖ' → ⊥
  wke-z-l (wke-ww- π ϖ ϖ' θ) = wke-z-l θ
  wke-z-l (wke-cww π ϖ ϖ' θ) = wke-z-l θ

  empty-lookup : (i : Γ ∋ X) → (ϖ : Wkn Γ []) → (csn : List CTerm) → lookup-metric i [] ϖ csn ≡ zero-metric
  empty-lookup Cx.h (wkn-cons ϖ) csn = refl
  empty-lookup (Cx.t i) (wkn-cons ϖ) csn = refl

  lookup-wke-lemma : (i : Γ' ∋ X) → (E E' : List (Σ[ X ∈ Ty ] (List CTerm → TermMetric X)))
              → (π : Wk Γ Γ') → (ϖ : Wkn Γ E) → (ϖ' : Wkn Γ' E') → (θ : Wke π ϖ ϖ') → (csn : List CTerm)
              → lookup-metric i E' ϖ' csn ≡ lookup-metric (wk-mem π i) E ϖ csn

  lookup-wke-lemma Cx.h E E' π ϖ ϖ' (wke-ccc π₁ ϖ₁ ϖ'' e θ) csn = refl
  lookup-wke-lemma Cx.h (_ ∷ E) E' (wk-wk π) (wkn-cong ϖ) ϖ' (wke-wc- π ϖ ϖ' e θ) csn = lookup-wke-lemma h E E' π ϖ ϖ' θ csn
  lookup-wke-lemma Cx.h [] [] (wk-wk π) (wkn-cons ϖ) (wkn-cons ϖ'') (wke-ww- π ϖ ϖ' θ) csn = refl
  lookup-wke-lemma Cx.h [] (x ∷ E') (wk-wk π) (wkn-cons ϖ) ϖ' (wke-ww- π ϖ ϖ' θ) csn = ql (wke-z-l θ) (lookup-metric h (x ∷ E') ϖ' csn ≡ lookup-metric (wk-mem (wk-wk {A = R₀} π) h) [] (wkn-cons ϖ) csn)
  lookup-wke-lemma Cx.h (x ∷ E) E' (wk-wk π) (wkn-cons ϖ) ϖ' (wke-ww- π ϖ ϖ' θ) csn = lookup-wke-lemma h (x ∷ E) E' π ϖ ϖ' θ csn
  lookup-wke-lemma Cx.h [] [] (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ) csn = refl
  lookup-wke-lemma Cx.h [] (x ∷ E') (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ) csn = refl
  lookup-wke-lemma Cx.h (x ∷ E) [] (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ) csn = refl
  lookup-wke-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ) csn = refl

  lookup-wke-lemma (Cx.t i) E E' π ϖ ϖ' (wke-ccc π₁ ϖ₁ ϖ'' e θ) csn = lookup-wke-lemma i _ _ π₁ ϖ₁ ϖ'' θ csn
  lookup-wke-lemma (Cx.t i) E E' π ϖ ϖ' (wke-wc- π₁ ϖ₁ ϖ'' e θ) csn = lookup-wke-lemma (t i) _ E' π₁ ϖ₁ ϖ' θ csn

  lookup-wke-lemma (Cx.t i) [] [] (wk-wk π) (wkn-cons ϖ) (wkn-cons ϖ'') (wke-ww- π ϖ ϖ' θ) csn = refl
  lookup-wke-lemma (Cx.t i) [] (x ∷ E') (wk-wk π) (wkn-cons ϖ) ϖ' (wke-ww- π ϖ ϖ' θ) csn = ql (wke-z-l θ) (lookup-metric (t i) (x ∷ E') ϖ' csn ≡ lookup-metric (wk-mem (wk-wk {A = R₀} π) (t i)) [] (wkn-cons ϖ) csn)
  lookup-wke-lemma (Cx.t i) (x ∷ E) [] (wk-wk π) (wkn-cons ϖ) ϖ' (wke-ww- π ϖ ϖ' θ) csn = lookup-wke-lemma (t i) (x ∷ E) [] π ϖ ϖ' θ csn
  lookup-wke-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wk-wk π) (wkn-cons ϖ) ϖ' (wke-ww- π ϖ ϖ' θ) csn = lookup-wke-lemma (t i) (x ∷ E) (x₁ ∷ E') π ϖ ϖ' θ csn

  lookup-wke-lemma (Cx.t i) [] [] (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ) csn = refl
  lookup-wke-lemma (Cx.t {A = X} {B = Y} i) [] (x ∷ E') (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ) csn = ql (wke-z-l θ) (lookup-metric (t {A = X} {B = Y} i) (x ∷ E') (wkn-cons ϖ') csn ≡ lookup-metric (wk-mem (wk-cong {A = R₀} π) (t i)) [] (wkn-cons ϖ) csn)
  lookup-wke-lemma (Cx.t i) (x ∷ E) [] (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ) csn rewrite sym (empty-lookup i ϖ' csn) = lookup-wke-lemma i (x ∷ E) [] π ϖ ϖ' θ csn
  lookup-wke-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ) csn = lookup-wke-lemma i (x ∷ E) (x₁ ∷ E') π ϖ ϖ' θ csn

  mutual

    λ-lhs-val-wke-lemma : (M : Val Γ' (X `× Y)) → (E E' : List (Σ[ X ∈ Ty ] (List CTerm → TermMetric X)))
                  → (π : Wk Γ Γ') → (ϖ : Wkn Γ E) → (ϖ' : Wkn Γ' E') → (θ : Wke π ϖ ϖ')
                  → (λ c → lhs (val-metric M E' ϖ' c)) ≡ (λ c → lhs (val-metric (wk-val π M) E ϖ c))
    λ-lhs-val-wke-lemma M E E' π ϖ ϖ' θ = extensionality λ c → cong lhs (val-wke-lemma M E E' π ϖ ϖ' θ c)

    λ-rhs-val-wke-lemma : (M : Val Γ' (X `× Y)) → (E E' : List (Σ[ X ∈ Ty ] (List CTerm → TermMetric X)))
                  → (π : Wk Γ Γ') → (ϖ : Wkn Γ E) → (ϖ' : Wkn Γ' E') → (θ : Wke π ϖ ϖ')
                  → (λ c → rhs (val-metric M E' ϖ' c)) ≡ (λ c → rhs (val-metric (wk-val π M) E ϖ c))
    λ-rhs-val-wke-lemma M E E' π ϖ ϖ' θ = extensionality λ c → cong rhs (val-wke-lemma M E E' π ϖ ϖ' θ c)

    val-wke-lemma : (M : Val Γ' X) → (E E' : List (Σ[ X ∈ Ty ] (List CTerm → TermMetric X)))
                → (π : Wk Γ Γ') → (ϖ : Wkn Γ E) → (ϖ' : Wkn Γ' E') → (θ : Wke π ϖ ϖ') → (csn : List CTerm)
                → val-metric M E' ϖ' csn ≡ val-metric (wk-val π M) E ϖ csn
    val-wke-lemma (var i) E E' π ϖ ϖ' θ csn = cong (incr 2) (lookup-wke-lemma i E E' π ϖ ϖ' θ csn)
    val-wke-lemma (lam W) E E' π ϖ ϖ' θ csn
      rewrite
          comp-wke-lemma W E E' (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ) csn
        | contr-comp-eq W (wk-cong π)
        = refl
    val-wke-lemma (pair M₁ M₂) E E' π ϖ ϖ' θ csn rewrite val-wke-lemma M₁ E E' π ϖ ϖ' θ csn | val-wke-lemma M₂ E E' π ϖ ϖ' θ csn = refl
    val-wke-lemma (pm {A = A} {B = B} M N) E E' π ϖ ϖ' θ csn
      rewrite
          val-wke-lemma M E E' π ϖ ϖ' θ csn
        | λ-rhs-val-wke-lemma M E E' π ϖ ϖ' θ
        | λ-lhs-val-wke-lemma M E E' π ϖ ϖ' θ
        | val-wke-lemma N E E' (wk-cong (wk-cong π)) (wkn-cons (wkn-cons ϖ)) (wkn-cons (wkn-cons ϖ')) (wke-cww (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ)) csn
        | val-wke-lemma N ((B , (λ c → rhs (val-metric (wk-val π M) E ϖ c))) ∷ (A , (λ c → lhs (val-metric (wk-val π M) E ϖ c))) ∷ E) ((B , (λ c → rhs (val-metric (wk-val π M) E ϖ c))) ∷ (A , (λ c → lhs (val-metric (wk-val π M) E ϖ c))) ∷ E') (wk-cong (wk-cong π)) (wkn-cong (wkn-cong ϖ)) (wkn-cong (wkn-cong ϖ')) (wke-ccc (wk-cong π) (wkn-cong ϖ) (wkn-cong ϖ') (λ c → rhs (val-metric (wk-val π M) E ϖ c)) (wke-ccc π ϖ ϖ' (λ c → lhs (val-metric (wk-val π M) E ϖ c)) θ)) csn
      = refl
    val-wke-lemma unit E E' π ϖ ϖ' θ csn = refl

    val-wke-lemma-ext : (M : Val Γ' X) → (E E' : List (Σ[ X ∈ Ty ] (List CTerm → TermMetric X)))
                → (π : Wk Γ Γ') → (ϖ : Wkn Γ E) → (ϖ' : Wkn Γ' E') → (θ : Wke π ϖ ϖ')
                → val-metric M E' ϖ' ≡ val-metric (wk-val π M) E ϖ
    val-wke-lemma-ext M E E' π ϖ ϖ' θ = extensionality (val-wke-lemma M E E' π ϖ ϖ' θ)

    comp-wke-lemma : (W : Comp Γ' X) → (E E' : List (Σ[ X ∈ Ty ] (List CTerm → TermMetric X)))
                → (π : Wk Γ Γ') → (ϖ : Wkn Γ E) → (ϖ' : Wkn Γ' E') → (θ : Wke π ϖ ϖ') → (csn : List CTerm)
                → comp-metric W E' ϖ' csn ≡ comp-metric (wk-comp π W) E ϖ csn
    comp-wke-lemma (return M) E E' π ϖ ϖ' θ [] = cong (incr 2) (val-wke-lemma M E E' π ϖ ϖ' θ []) --refl
    comp-wke-lemma (return M) E E' π ϖ ϖ' θ (x ∷ csn) = cong (incr 2) (val-wke-lemma M E E' π ϖ ϖ' θ csn)
    comp-wke-lemma (pm {A = A} {B = B} M W) E E' π ϖ ϖ' θ csn
      rewrite
          val-wke-lemma M E E' π ϖ ϖ' θ csn
        | λ-rhs-val-wke-lemma M E E' π ϖ ϖ' θ
        | λ-lhs-val-wke-lemma M E E' π ϖ ϖ' θ
        | comp-wke-lemma W E E' (wk-cong (wk-cong π)) (wkn-cons (wkn-cons ϖ)) (wkn-cons (wkn-cons ϖ')) (wke-cww (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ)) csn
        | comp-wke-lemma W ((B , (λ c → rhs (val-metric (wk-val π M) E ϖ c))) ∷ (A , (λ c → lhs (val-metric (wk-val π M) E ϖ c))) ∷ E) ((B , (λ c → rhs (val-metric (wk-val π M) E ϖ c))) ∷ (A , (λ c → lhs (val-metric (wk-val π M) E ϖ c))) ∷ E') (wk-cong (wk-cong π)) (wkn-cong (wkn-cong ϖ)) (wkn-cong (wkn-cong ϖ')) (wke-ccc (wk-cong π) (wkn-cong ϖ) (wkn-cong ϖ') (λ c → rhs (val-metric (wk-val π M) E ϖ c)) (wke-ccc π ϖ ϖ' (λ c → lhs (val-metric (wk-val π M) E ϖ c)) θ)) csn
      = refl
    comp-wke-lemma (push W₁ W₂) E E' π ϖ ϖ' θ csn
      rewrite
          comp-wke-lemma W₂ E E' (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ) csn
        -- | comp-wke-lemma W₁ E E' π ϖ ϖ' θ (( (cterm (count-in-comp h W₂ , ⟪ comp-metric (wk-comp (wk-cong π) W₂) E (wkn-cons ϖ) csn ⟫)) ∷ csn))
        -- | wk-comp-count-eq (wk-cong π) h W₂
        = {!!} --refl
    comp-wke-lemma (app M N) E E' π ϖ ϖ' θ csn
      rewrite
          val-wke-lemma M E E' π ϖ ϖ' θ csn
        | val-wke-lemma N E E' π ϖ ϖ' θ csn
        | cong (csn-multiply (p2 (val-metric (wk-val π M) E ϖ csn))) (extensionality (λ c → cong ⟪_⟫ (val-wke-lemma N E E' π ϖ ϖ' θ c)))
        =
        refl
    comp-wke-lemma (var M) E E' π ϖ ϖ' θ csn rewrite val-wke-lemma M E E' π ϖ ϖ' θ csn = refl
    comp-wke-lemma (sub W₁ W₂) E E' π ϖ ϖ' θ csn
      rewrite
          comp-wke-lemma W₂ E E' π ϖ ϖ' θ csn
        --| comp-wke-lemma W₁ ((`V , (λ _ → m-V 0 (⟪ comp-metric (wk-comp π W₂) E ϖ csn ⟫ + csn-to-nat₀ ⟪ comp-metric (wk-comp π W₂) E ϖ csn ⟫ csn))) ∷ E) ((`V , (λ _ → m-V 0 (⟪ comp-metric (wk-comp π W₂) E ϖ csn ⟫ + csn-to-nat₀ ⟪ comp-metric (wk-comp π W₂) E ϖ csn ⟫ csn))) ∷ E') (wk-cong π) (wkn-cong ϖ) (wkn-cong ϖ') (wke-ccc π ϖ ϖ' (λ _ → m-V 0 (⟪ comp-metric (wk-comp π W₂) E ϖ csn ⟫ + csn-to-nat₀ ⟪ comp-metric (wk-comp π W₂) E ϖ csn ⟫ csn)) θ) csn
        = {!!} --refl

  {-
  v̲a̲l̲-wke-lemma : (M : V̲a̲l̲ Γ' X) → (E E' : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X)))
              → (π : Wk Γ Γ') → (ϖ : Wkn Γ E) → (ϖ' : Wkn Γ' E') → (θ : Wke π ϖ ϖ') → (csn : List (ℕ × ℕ))
              → v̲a̲l̲-metric M E' ϖ' csn ≡ v̲a̲l̲-metric (wk-v̲a̲l̲ π M) E ϖ csn
  v̲a̲l̲-wke-lemma (l̲a̲m̲ W) E E' π ϖ ϖ' θ csn
      rewrite
          comp-wke-lemma W E E' (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ) csn
        | wk-comp-count-eq (wk-cong π) h W
        = {!!} --refl
  v̲a̲l̲-wke-lemma (pa̲i̲r̲ M₁ M₂) E E' π ϖ ϖ' θ csn rewrite v̲a̲l̲-wke-lemma M₁ E E' π ϖ ϖ' θ csn | v̲a̲l̲-wke-lemma M₂ E E' π ϖ ϖ' θ csn = refl
  v̲a̲l̲-wke-lemma u̲n̲i̲t̲ E E' π ϖ ϖ' θ csn = refl
  v̲a̲l̲-wke-lemma (v̲a̲r̲ i) E E' π ϖ ϖ' θ csn = cong (incr 1) (lookup-wke-lemma i E E' π ϖ ϖ' θ csn)
  -}

-------------------------------------------------------------------------------------------------

{-
  mutual

    fun-val-lemma : (M : Val (Γ ∙ X) Y) → (nm : (List (ℕ × ℕ) → TermMetric X)) → (E : List (Σ[ Z ∈ Ty ] (List (ℕ × ℕ) → TermMetric Z))) → (ϖ : Wkn Γ E) → (csn : List (ℕ × ℕ)) → ⟪ val-metric M ((X , nm) ∷ E) (wkn-cong ϖ) csn ⟫ ≡ count-in-val h M * ⟪ nm csn ⟫ + ⟪ val-metric M E (wkn-cons ϖ) csn ⟫
    fun-val-lemma {X = X} {Y = Y} M nm E ϖ csn = {!!}

    fun-comp-lemma :   (W : Comp (Γ ∙ X) Y) → (nm : (List (ℕ × ℕ) → TermMetric X)) → (E : List (Σ[ Z ∈ Ty ] (List (ℕ × ℕ) → TermMetric Z))) → (ϖ : Wkn Γ E) → (csn : List (ℕ × ℕ))
                     → ⟪ comp-metric W ((X , nm) ∷ E) (wkn-cong ϖ) csn ⟫ ≡ count-in-comp h W * ⟪ nm csn ⟫ + ⟪ comp-metric W E (wkn-cons ϖ) csn ⟫
    fun-comp-lemma {X = X} {Y = Y} (return M) nm E ϖ [] =
                                let
                                  a1 = fun-val-lemma M nm E ϖ []
                                in
                                ⟪ comp-metric (return M) ((X , nm) ∷ E) (wkn-cong ϖ) [] ⟫
                                ≡⟨ refl ⟩
                                  2+ ⟪ val-metric M ((X , nm) ∷ E) (Wkn.wkn-cong ϖ) [] ⟫
                                ≡⟨ {!!} ⟩ -- EASY
                                  count-in-val h M * ⟪ nm [] ⟫ + 2+ ⟪ val-metric M E (Wkn.wkn-cons ϖ) [] ⟫
                                ≡⟨ refl ⟩
                                count-in-comp h (return M) * ⟪ nm [] ⟫ + ⟪ comp-metric (return M) E (wkn-cons ϖ) [] ⟫ ∎
    fun-comp-lemma {X = X} {Y = Y} (return M) nm E ϖ (x ∷ csn) =
      let
        a1 = fun-val-lemma M nm E ϖ csn
      in
      ⟪ comp-metric (return M) ((X , nm) ∷ E) (wkn-cong ϖ) (x ∷ csn) ⟫
      ≡⟨ refl ⟩
         2+ ⟪ val-metric M ((X , nm) ∷ E) (Wkn.wkn-cong ϖ) csn ⟫
      ≡⟨ {!!} ⟩
         count-in-val h M * ⟪ nm (x ∷ csn) ⟫ + 2+ ⟪ val-metric M E (Wkn.wkn-cons ϖ) csn ⟫
      ≡⟨ refl ⟩
         count-in-comp h (return M) * ⟪ nm (x ∷ csn) ⟫ + ⟪ comp-metric (return M) E (wkn-cons ϖ) (x ∷ csn) ⟫ ∎
    fun-comp-lemma (pm M W) nm E ϖ csn = {!!}
    fun-comp-lemma (push W₁ W₂) nm E ϖ csn = {!!}
    fun-comp-lemma (app M N) nm E ϖ csn = {!!}
    fun-comp-lemma (var M) nm E ϖ csn = {!!}
    fun-comp-lemma (sub W₁ W₂) nm E ϖ csn = {!!}
-}

-------------------------------------------------------------------------------------------------

{-
  data PWk : (π : Wk Γ Δ) → Set where
    pwk-id : {π : Wk Γ Γ} → PWk π
    pwk-wk : {π : Wk Γ Δ} → PWk π → PWk (wk-wk {A = X} π)

  lookup-lemma :   {X : Ty} → {Γ' : Ctx} → {i : Γ ∋ X} → {γ : Env Γ} → {γ' : Env Γ'} → {M : V̲a̲l̲ Γ' X}
                 → (⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ γ' ﹐ M ⟩)
                 → (πᵥ : Wk Γ Γ')
                 → (pπ : PWk πᵥ)
                 → (csn : List (ℕ × ℕ))
                 → v̲a̲l̲-metric (wk-v̲a̲l̲ πᵥ M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn ≤ᴹ lookup-metric i (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn
  lookup-lemma {X = X} {Γ' = Γ'} {i = i} {γ = γ} {γ' = γ'} {M = M} (S ◼) (wk-wk πᵥ) pπ csn
    rewrite
      v̲a̲l̲-wke-lemma
        M
        ((X , v̲a̲l̲-metric M (proj₁ (env-metric γ')) (proj₂ (env-metric γ'))) ∷ proj₁ (env-metric γ'))
        (proj₁ (env-metric γ'))
        (wk-wk πᵥ)
        (wkn-cong (proj₂ (env-metric γ')))
        (proj₂ (env-metric γ'))
        (wke-wc- πᵥ (proj₂ (env-metric γ')) (proj₂ (env-metric γ')) (v̲a̲l̲-metric M (proj₁ (env-metric γ')) (proj₂ (env-metric γ'))) wke-id)
        csn
    = ≤ᴹ-refl
  lookup-lemma {X = X} {i = i} {γ = γ} {γ' = γ'} {M = M} (S →ᴸ⟨ x ⟩ i→M) πᵥ pwk-id csn = {!!}
  lookup-lemma {X = X} {i = i} {γ = γ} {γ' = γ'} {M = M} (S →ᴸ⟨ x ⟩ i→M) (wk-wk πᵥ) (pwk-wk pπ) csn = {!!}
-}

-------------------------------------------------------------------------------------------------
  val-metric-decreasing : {Q₁ : ValState X} → {Q₂ : ValState X} → (Q₁→ᶜQ₂ : Q₁ ↠ᵛ Q₂) → (csn : List CTerm) → (suc (valstate-metric Q₂ csn) ≤ (valstate-metric Q₁ csn))
  val-metric-decreasing = {!!}

  comp-metric-decreasing : {Q₁ : CompState} → {Q₂ : CompState} → (Q₁→ᶜQ₂ : Q₁ →ᶜ Q₂) → (suc (compstate-metric Q₂) ≤ (compstate-metric Q₁))
  comp-metric-decreasing (∘return {M = M} {γ = γ} {π = π} {M' = M'} {γ' = γ'} {cs = ◻} M→M') with val-metric-decreasing M→M' []
  ... | x =
    let
      a1 = +-≤-cong x (z≤n {n = zero})
    in
    s≤s (≤-trans a1 n≤sn)
  comp-metric-decreasing (∘return {M = M} {γ = γ} {π = π} {M' = M'} {γ' = γ'} {cs = W ⊲ γ₁ ⦂⦂ cs} M→M') with val-metric-decreasing (M→M') (cs-to-csn cs)
  ... | x =
    let
      a1 = ⟪ v̲a̲l̲-metric M' (proj₁ (env-metric γ')) (proj₂ (env-metric γ')) (cs-to-csn cs) ⟫
      a2 = ⟪ val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫
      a3 = ⟪ comp-metric W (proj₁ (env-metric γ₁)) (wkn-cons (proj₂ (env-metric γ₁))) (cs-to-csn cs) ⟫
    in
      s≤s (s≤s {!!})

{-

Goal: a1 + (a3 + (count-in-comp h W + a1 * count-in-comp h W) + csn-to-nat₀ (a3 + (count-in-comp h W + a1 * count-in-comp h W)) (cs-to-csn cs))
      ≤
      a2 + (a3 + (count-in-comp h W + (count-in-comp h W + a2 * count-in-comp h W)) + csn-to-nat₀ (a3 + (count-in-comp h W + (count-in-comp h W + a2 * count-in-comp h W))) (cs-to-csn cs))

TP :   a3 + (count-in-comp h W +                      a1 * count-in-comp h W)
     ≤ a3 + (count-in-comp h W + (count-in-comp h W + a2 * count-in-comp h W))

TP : a1 ≤ a2

EASY

----------------------------------------------------------------------------------------------------------------

Goal: a1 + (⟪ comp-metric W (proj₁ (env-metric γ₁)) (Wkn.wkn-cons (proj₂ (env-metric γ₁))) (cs-to-csn cs) ⟫ + csn-comp-multiply h W (λ c → ⟪ c̲o̲m̲p-metric (C̲o̲m̲p.r̲e̲t̲u̲r̲n̲ M') (proj₁ (env-metric γ')) (proj₂ (env-metric γ')) c ⟫) (CTerm.cterm (Δ , X , X₁ , W , ⟪ comp-metric W (proj₁ (env-metric γ₁)) (Wkn.wkn-cons (proj₂ (env-metric γ₁))) (cs-to-csn cs) ⟫) ∷ cs-to-csn cs) + csn-to-nat₀ (λ c → ⟪ comp-metric W (proj₁ (env-metric γ₁)) (Wkn.wkn-cons (proj₂ (env-metric γ₁))) (cs-to-csn cs) ⟫ + csn-comp-multiply h W (λ c₁ → ⟪ c̲o̲m̲p-metric (C̲o̲m̲p.r̲e̲t̲u̲r̲n̲ M') (proj₁ (env-metric γ')) (proj₂ (env-metric γ')) c₁ ⟫) c) (cs-to-csn cs))
      ≤
      a2 + (⟪ comp-metric W (proj₁ (env-metric γ₁)) (Wkn.wkn-cons (proj₂ (env-metric γ₁))) (cs-to-csn cs) ⟫ + csn-comp-multiply h W (λ c → ⟪ comp-metric (return (wk-val π M)) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) c ⟫) (CTerm.cterm (Δ , X , X₁ , W , ⟪ comp-metric W (proj₁ (env-metric γ₁)) (Wkn.wkn-cons (proj₂ (env-metric γ₁))) (cs-to-csn cs) ⟫) ∷ cs-to-csn cs) + csn-to-nat₀ (λ c → ⟪ comp-metric W (proj₁ (env-metric γ₁)) (Wkn.wkn-cons (proj₂ (env-metric γ₁))) (cs-to-csn cs) ⟫ + csn-comp-multiply h W (λ c₁ → ⟪ comp-metric (return (wk-val π M)) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) c₁ ⟫) c) (cs-to-csn cs))

Goal: a1 + (csn-comp-multiply h W (λ c → ⟪ c̲o̲m̲p-metric (C̲o̲m̲p.r̲e̲t̲u̲r̲n̲ M') (proj₁ (env-metric γ')) (proj₂ (env-metric γ')) c ⟫)    (CTerm.cterm (Δ , X , X₁ , W , ⟪ comp-metric W (proj₁ (env-metric γ₁)) (Wkn.wkn-cons (proj₂ (env-metric γ₁))) (cs-to-csn cs) ⟫) ∷ cs-to-csn cs) + csn-to-nat₀ (λ c → ⟪ comp-metric W (proj₁ (env-metric γ₁)) (Wkn.wkn-cons (proj₂ (env-metric γ₁))) (cs-to-csn cs) ⟫ + csn-comp-multiply h W (λ c₁ → ⟪ c̲o̲m̲p-metric (C̲o̲m̲p.r̲e̲t̲u̲r̲n̲ M')      (proj₁ (env-metric γ')) (proj₂ (env-metric γ')) c₁ ⟫) c) (cs-to-csn cs))
      ≤
      a2 + (csn-comp-multiply h W (λ c → ⟪ comp-metric (return (wk-val π M)) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) c ⟫) (CTerm.cterm (Δ , X , X₁ , W , ⟪ comp-metric W (proj₁ (env-metric γ₁)) (Wkn.wkn-cons (proj₂ (env-metric γ₁))) (cs-to-csn cs) ⟫) ∷ cs-to-csn cs) + csn-to-nat₀ (λ c → ⟪ comp-metric W (proj₁ (env-metric γ₁)) (Wkn.wkn-cons (proj₂ (env-metric γ₁))) (cs-to-csn cs) ⟫ + csn-comp-multiply h W (λ c₁ → ⟪ comp-metric (return (wk-val π M)) (proj₁ (env-metric γ))  (proj₂ (env-metric γ)) c₁ ⟫) c) (cs-to-csn cs))

-}

  comp-metric-decreasing (∙return {X = X} {M = M} {γ = γ} {N = N} {γ' = γ'} {π = π} {cs = cs}) =
    --let
    --  a1 = comp-metric (wk-comp (wk-cong π) N) ((X , v̲a̲l̲-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) ∷ proj₁ (env-metric γ)) (wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs)
    --  a2 = v̲a̲l̲-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) ((count-in-comp h N , ⟪ comp-metric N (proj₁ (env-metric γ')) (wkn-cons (proj₂ (env-metric γ'))) (cs-to-csn cs) ⟫) ∷ cs-to-csn cs)
    --  a3 = comp-metric N (proj₁ (env-metric γ')) (wkn-cons (proj₂ (env-metric γ'))) (cs-to-csn cs)
    --  a4 = v̲a̲l̲-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs)
    --in
      {!!}

{-
   suc (⟪ comp-metric (wk-comp (wk-cong π) N) ((X , v̲a̲l̲-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) ∷ proj₁ (env-metric γ)) (wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫ + csn-to-nat₀ ⟪ comp-metric (wk-comp (wk-cong π) N) ((X , v̲a̲l̲-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) ∷ proj₁ (env-metric γ)) (wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫ (cs-to-csn cs))
≤  suc (⟪ v̲a̲l̲-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ + (⟪ a3 ⟫ + (count-in-comp h N + ⟪ v̲a̲l̲-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ * count-in-comp h N) + csn-to-nat₀ (⟪ a3 ⟫ + (count-in-comp h N + ⟪ v̲a̲l̲-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ * count-in-comp h N)) (cs-to-csn cs)))

     a1 = comp-metric (wk-comp (wk-cong π) N) ((X , v̲a̲l̲-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) ∷ proj₁ (env-metric γ)) (wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs)
     a1 =                                                                                                                                                                                                  comp-metric (wk-comp (wk-cong π) N) ((X , v̲a̲l̲-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) ∷ proj₁ (env-metric γ)) (wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs)
   suc (⟪ comp-metric (wk-comp (wk-cong π) N) ((X , v̲a̲l̲-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) ∷ proj₁ (env-metric γ)) (wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫ + csn-to-nat₀ ⟪ comp-metric (wk-comp (wk-cong π) N) ((X , v̲a̲l̲-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) ∷ proj₁ (env-metric γ)) (wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫ (cs-to-csn cs))

   suc (          ⟪ a1 ⟫ +                                                    csn-to-nat₀ ⟪ a1 ⟫                                                      (cs-to-csn cs))
≤  suc (⟪ a4 ⟫ + (⟪ a3 ⟫ + (count-in-comp h N + ⟪ a4 ⟫ * count-in-comp h N) + csn-to-nat₀ (⟪ a3 ⟫ + (count-in-comp h N + ⟪ a4 ⟫ * count-in-comp h N)) (cs-to-csn cs)))


TP: a1 ≤ (⟪ a3 ⟫ + (count-in-comp h N + ⟪ a4 ⟫ * count-in-comp h N))

IE:
comp-metric (wk-comp (wk-cong π) N) ((X , v̲a̲l̲-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) ∷ proj₁ (env-metric γ)) (wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs)
≤                                        (v̲a̲l̲-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ))  (cs-to-csn cs)) * (count-in-comp h N) +
      comp-metric N (proj₁ (env-metric γ')) (wkn-cons (proj₂ (env-metric γ'))) (cs-to-csn cs)

SEAMS REASONABLE
-}

  comp-metric-decreasing (∘push {X = X} {M = M} {N = N} {γ = γ} {cs = cs} {πₓ = πₓ} {wk≡ₓ = wk≡ₓ} {wk≡ = wk≡}) =
    -- let
    --   a1 = comp-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) ((count-in-comp h N , ⟪ comp-metric N (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫) ∷ cs-to-csn cs)
    --   a2 = comp-metric N (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs)
    -- in
      {!!}

{-
suc (⟪ comp-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) ((count-in-comp h N , ⟪ comp-metric N (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫) ∷ cs-to-csn cs) ⟫ + (⟪ comp-metric N (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫ + ⟪ comp-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) ((count-in-comp h N , ⟪ comp-metric N (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫) ∷ cs-to-csn cs) ⟫ * count-in-comp h N + csn-to-nat₀ (⟪ comp-metric N (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫ + ⟪ comp-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) ((count-in-comp h N , ⟪ comp-metric N (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫) ∷ cs-to-csn cs) ⟫ * count-in-comp h N) (cs-to-csn cs)))
≤
suc (⟪ comp-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) ((count-in-comp h N , ⟪ comp-metric N (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫) ∷ cs-to-csn cs) ⟫ + count-in-comp h N * ⟪ comp-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) ((count-in-comp h N , ⟪comp-metric N (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫) ∷ cs-to-csn cs) ⟫ + ⟪ comp-metric N (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫ + csn-to-nat₀ (suc (⟪ comp-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) ((count-in-comp h N , ⟪ comp-metric N (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫) ∷ cs-to-csn cs) ⟫ + count-in-comp h N * ⟪ comp-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) ((count-in-comp h N , ⟪ comp-metric N (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫) ∷ cs-to-csn cs) ⟫ + ⟪ comp-metric N (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫)) (cs-to-csn cs))

EASY!
   suc (⟪ a1 ⟫ +                             (⟪ a2 ⟫ + ⟪ a1 ⟫ * count-in-comp h N + csn-to-nat₀ (              ⟪ a2 ⟫ + ⟪ a1 ⟫ * count-in-comp h N ) (cs-to-csn cs)))
≤  suc (⟪ a1 ⟫ + count-in-comp h N * ⟪ a1 ⟫ + ⟪ a2 ⟫                              + csn-to-nat₀ (suc (⟪ a1 ⟫ + count-in-comp h N * ⟪ a1 ⟫ + ⟪ a2 ⟫)) (cs-to-csn cs))
-}

  comp-metric-decreasing (∘sub {M = M} {N = N} {γ = γ} {cs = cs} {πₓ = πₓ} {wk≡ₓ = wk≡ₓ}) =
    --let
    --  a1 = comp-metric M ((`V , (λ _ → m-V 0 ⟪ comp-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ (cs-to-csn cs))) ∷ proj₁ (env-metric γ)) (wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs)
    --  a2 = comp-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs)
    --in
      {!!}

{-

Goal: suc (⟪ comp-metric M ((`V , (λ _ → m-V 0 ⟪ comp-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ (cs-to-csn cs))) ∷ proj₁ (env-metric γ)) (wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫ + csn-to-nat₀ ⟪ comp-metric M ((`V , (λ _ → m-V 0 ⟪ comp-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ (cs-to-csn cs))) ∷ proj₁ (env-metric γ)) (wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫ (cs-to-csn cs))
      ≤
      suc (⟪ comp-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ + ⟪ comp-metric M ((`V , (λ _ → m-V 0 ⟪ comp-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ (cs-to-csn cs))) ∷ proj₁ (env-metric γ)) (wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫ + csn-to-nat₀ (suc (⟪ comp-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ + ⟪ comp-metric M ((`V , (λ _ → m-V 0 ⟪ comp-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ (cs-to-csn cs))) ∷ proj₁ (env-metric γ)) (wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫)) (cs-to-csn cs))

Goal: suc (⟪ a1 ⟫ + csn-to-nat₀ ⟪ a1 ⟫ (cs-to-csn cs))
      ≤
      suc (⟪ a2 ⟫ + ⟪ a1 ⟫ + csn-to-nat₀ (suc (⟪ a2 ⟫ + ⟪ a1 ⟫)) (cs-to-csn cs))
EASY
-}

  comp-metric-decreasing (∘pm {X = X} {Y = Y} {M = M} {γ = γ} {W = W} {cs = cs} {πₓ = πₓ} {πₓ' = πₓ'} {γ'' = γ''} {wk≡ₓ = wk≡ₓ} {wk≡ₓ' = wk≡ₓ'} {LHS = LHS } {RHS = RHS} π M→M' π') =
    let
      a1 = comp-metric (wk-comp (wk-cong (wk-cong π')) (wk-comp (wk-cong (wk-cong π)) W)) ((Y , v̲a̲l̲-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((X , v̲a̲l̲-metric LHS (proj₁ (env-metric γ'')) (proj₂ (env-metric γ''))) ∷ proj₁ (env-metric γ'')) (wkn-cong (proj₂ (env-metric γ'')))) ∷ (X , v̲a̲l̲-metric LHS (proj₁ (env-metric γ'')) (proj₂ (env-metric γ''))) ∷ proj₁ (env-metric γ'')) (wkn-cong (wkn-cong (proj₂ (env-metric γ'')))) (cs-to-csn cs)
      a2 = comp-metric (wk-comp (wk-cong (wk-cong π)) W) (proj₁ (env-metric γ)) (wkn-cons (wkn-cons (proj₂ (env-metric γ)))) (cs-to-csn cs)
      a3 = comp-metric (wk-comp (wk-cong (wk-cong π)) W) ((Y , (λ c → rhs (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) c))) ∷ (X , (λ c → lhs (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) c))) ∷ proj₁ (env-metric γ)) (wkn-cong (wkn-cong (proj₂ (env-metric γ)))) (cs-to-csn cs)
    in
     {!!}

{-

  suc (⟪ comp-metric (wk-comp (wk-cong (wk-cong π')) (wk-comp (wk-cong (wk-cong π)) W)) ((Y , v̲a̲l̲-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((X , v̲a̲l̲-metric LHS (proj₁ (env-metric γ'')) (proj₂ (env-metric γ''))) ∷ proj₁ (env-metric γ'')) (wkn-cong (proj₂ (env-metric γ'')))) ∷ (X , v̲a̲l̲-metric LHS (proj₁ (env-metric γ'')) (proj₂ (env-metric γ''))) ∷ proj₁ (env-metric γ'')) (wkn-cong (wkn-cong (proj₂ (env-metric γ'')))) (cs-to-csn cs) ⟫ + csn-to-nat₀ ⟪ comp-metric (wk-comp (wk-cong (wk-cong π')) (wk-comp (wk-cong (wk-cong π)) W)) ((Y , v̲a̲l̲-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((X , v̲a̲l̲-metric LHS (proj₁ (env-metric γ'')) (proj₂ (env-metric γ''))) ∷ proj₁ (env-metric γ'')) (wkn-cong (proj₂ (env-metric γ'')))) ∷ (X , v̲a̲l̲-metric LHS (proj₁ (env-metric γ'')) (proj₂ (env-metric γ''))) ∷ proj₁ (env-metric γ'')) (wkn-cong (wkn-cong (proj₂ (env-metric γ'')))) (cs-to-csn cs) ⟫ (cs-to-csn cs))
≤ suc (vx (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs)) + ⟪ comp-metric (wk-comp (wk-cong (wk-cong π)) W) (proj₁ (env-metric γ)) (wkn-cons (wkn-cons (proj₂ (env-metric γ)))) (cs-to-csn cs) ⟫ + ⟪ comp-metric (wk-comp (wk-cong (wk-cong π)) W) ((Y , (λ c → rhs (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) c))) ∷ (X , (λ c → lhs (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) c))) ∷ proj₁ (env-metric γ)) (wkn-cong (wkn-cong (proj₂ (env-metric γ)))) (cs-to-csn cs) ⟫ + csn-to-nat₀ (suc (vx (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs)) + ⟪ comp-metric (wk-comp (wk-cong (wk-cong π)) W) (proj₁ (env-metric γ)) (wkn-cons (wkn-cons (proj₂ (env-metric γ)))) (cs-to-csn cs) ⟫ + ⟪ comp-metric (wk-comp (wk-cong (wk-cong π)) W) ((Y , (λ c → rhs (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) c))) ∷ (X , (λ c → lhs (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) c))) ∷ proj₁ (env-metric γ)) (wkn-cong (wkn-cong (proj₂ (env-metric γ)))) (cs-to-csn cs) ⟫)) (cs-to-csn cs))

  suc (⟪ a1 ⟫ + csn-to-nat₀ ⟪ a1 ⟫ (cs-to-csn cs))
≤ suc (vx (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs)) + ⟪ a2 ⟫ + ⟪ a3 ⟫ + csn-to-nat₀ (suc (vx (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs)) + ⟪ a2 ⟫ + ⟪ a3 ⟫)) (cs-to-csn cs))

  suc (⟪ a1 ⟫)                                                                                                      + csn-to-nat₀ ⟪ a1 ⟫ (cs-to-csn cs)
≤ suc (vx (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs)) + ⟪ a2 ⟫ + ⟪ a3 ⟫) + csn-to-nat₀ (suc (vx (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs)) + ⟪ a2 ⟫ + ⟪ a3 ⟫)) (cs-to-csn cs)

  ⟪ a1 ⟫
≤ vx (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs)) + ⟪ a2 ⟫ + ⟪ a3 ⟫

sufficient to prove ⟪ a1 ⟫ ≤ ⟪ a3 ⟫, i.e.

  comp-metric (wk-comp (wk-cong (wk-cong π')) (wk-comp (wk-cong (wk-cong π)) W)) ((Y ,             v̲a̲l̲-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS)   ((X , v̲a̲l̲-metric LHS (proj₁ (env-metric γ'')) (proj₂ (env-metric γ''))) ∷ proj₁ (env-metric γ''))  (wkn-cong (proj₂ (env-metric γ'')))                 )    ∷   (X ,             v̲a̲l̲-metric         LHS  (proj₁ (env-metric γ'')) (proj₂ (env-metric γ''  )))        ∷ proj₁ (env-metric γ'') ) (wkn-cong (wkn-cong (proj₂ (env-metric γ'')))) (cs-to-csn cs)
≤ comp-metric (wk-comp (wk-cong (wk-cong π))                                 W)  ((Y , (λ c → rhs (val-metric (wk-val π               M)                                                                            (proj₁ (env-metric γ))              (proj₂ (env-metric γ))        c))         )    ∷   (X , (λ c → lhs (val-metric (wk-val π M) (proj₁ (env-metric γ))   (proj₂ (env-metric γ)) c)))        ∷ proj₁ (env-metric γ)   ) (wkn-cong (wkn-cong (proj₂ (env-metric γ))))   (cs-to-csn cs)

seems reasonable
-}

  comp-metric-decreasing (∙app-var {Z' = Z'} {Z = Z} {i = i} {N = N} {γ = γ} {cs = cs} {πₓ = πₓ} {wk≡ₓ = wk≡ₓ} {W = W} {γ' = γ'} i→λW πᵥ T≤S θ)
    -- rewrite
    --     sym (comp-wke-lemma W (proj₁ (env-metric γ)) (proj₁ (env-metric γ')) (wk-cong πᵥ) ((wkn-cons (proj₂ (env-metric γ)))) ((wkn-cons (proj₂ (env-metric γ')))) (wke-cww πᵥ (proj₂ (env-metric γ)) (proj₂ (env-metric γ')) θ) (cs-to-csn cs))
    --   | ≡-p3-incr 2 (lookup-metric i (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs))
    --   | +-p1-incr 2 (lookup-metric i (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs))
    {-
Goal: suc (⟪ comp-metric (wk-comp (wk-cong πᵥ) W) ((Z' , v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) ∷ proj₁ (env-metric γ)) (Wkn.wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫ +
       csn-to-nat₀ ⟪ comp-metric (wk-comp (wk-cong πᵥ) W) ((Z' , v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) ∷ proj₁ (env-metric γ)) (Wkn.wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫ (cs-to-csn cs))
      ≤
      suc (p1 (incr 2 b1) + (⟪ a1 ⟫ + p2 b1 * ⟪ a1 ⟫) + VMain.⟪ (λ z → k₀ z) ⟫ (p3 (incr 2 b1)) + csn-to-nat₀ (suc (p1 (incr 2 b1) + (⟪ a1 ⟫ + p2 b1 * ⟪ a1 ⟫) + VMain.⟪ (λ z → k₀ z) ⟫ (p3 (incr 2 b1)))) (cs-to-csn cs))
    -}
    =
    -- let
    --   a1 = v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs)
    --   --a2 = comp-metric (wk-comp (wk-cong πᵥ) W) (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs)
    --   a2 = comp-metric W (proj₁ (env-metric γ')) (wkn-cons (proj₂ (env-metric γ'))) (cs-to-csn cs)
    --   b1 = (lookup-metric i (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs))
    --   c1 = T≤S (cs-to-csn cs)
    --   c2 = ≤ᴹ-p1 c1
    --   c4 = ≤ᴹ-p3 c1
    --   e1 = comp-wke-lemma W (proj₁ (env-metric γ)) (proj₁ (env-metric γ')) (wk-cong πᵥ) ((wkn-cons (proj₂ (env-metric γ)))) ((wkn-cons (proj₂ (env-metric γ')))) (wke-cww πᵥ (proj₂ (env-metric γ)) (proj₂ (env-metric γ')) θ) (cs-to-csn cs)
    --   -- d1 : a2 ≤ᴹ p3 b1
    --   d1 : a2 ≤ᴹ p3 (incr 2 b1)
    --   d1 = ≤ᴹ-trans c4 {!!} --(≤ᴹ-incr-cong (z≤n {n = 2}) ≤ᴹ-refl)
    -- in
      {!!}

{-

Goal:
2+ (2+ (⟪ v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ + count-in-comp h (wk-comp (wk-cong πᵥ) W) * ⟪ v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ + ⟪ comp-metric (wk-comp (wk-cong πᵥ) W) (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫ + csn-to-nat₀ (2+ (suc (⟪ v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ + count-in-comp h (wk-comp (wk-cong πᵥ) W) * ⟪ v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ + ⟪ comp-metric (wk-comp (wk-cong πᵥ) W) (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫))) (cs-to-csn cs)))
      ≤
   suc (p1 (incr 2 (lookup-metric i (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs))) + (⟪ v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ + p2 (lookup-metric i (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs)) * ⟪ v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫) + ⟪ p3 (incr 2 (lookup-metric i (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs))) ⟫ + csn-to-nat₀ (suc (p1 (incr 2 (lookup-metric i (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs))) + (⟪ v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ + p2 (lookup-metric i (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs)) * ⟪ v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫) + ⟪ p3 (incr 2 (lookup-metric i (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs))) ⟫)) (cs-to-csn cs))

2+ (2+ (⟪ a1 ⟫ + count-in-comp h (wk-comp (wk-cong πᵥ) W) * ⟪ a1 ⟫ + ⟪ a2 ⟫ + csn-to-nat₀ (2+ (suc (⟪ a1 ⟫ + count-in-comp h (wk-comp (wk-cong πᵥ) W) * ⟪ a1 ⟫ + ⟪ a2 ⟫))) (cs-to-csn cs)))
≤
suc (p1 (incr 2 b1) + (⟪ a1 ⟫ + p2 b1 * ⟪ a1 ⟫) + ⟪ p3 (incr 2 b1) ⟫        + csn-to-nat₀ (suc (p1 (incr 2 b1) + (⟪ a1 ⟫ + p2 b1 * ⟪ a1 ⟫) + ⟪ p3 (incr 2 b1) ⟫)) (cs-to-csn cs))

                   3 +  ⟪ a1 ⟫ +                     count-in-comp h (wk-comp (wk-cong πᵥ) W) * ⟪ a1 ⟫ + ⟪ a2 ⟫
≤
suc (p1 (incr 2 b1)) + (⟪ a1 ⟫ +                                                        p2 b1 * ⟪ a1 ⟫) + ⟪ p3 (incr 2 b1) ⟫

lookup-lemma : (i→λW : ⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ γ' ﹐ M ⟩) → lookup-metric i E ϖ csn ≡ v̲a̲l̲-metric W E ϖ csn

lemma : (i→λW : ⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ γ' ﹐ l̲a̲m̲ W ⟩) → (lookup-metric i E ϖ csn) ≡ comp-metric (wk-comp (wk-cong πᵥ) W) E (wkn-cons ϖ)) csn

seems reasonable

---------------------------------------------------------------------


Goal: suc (⟪ comp-metric (wk-comp (wk-cong πᵥ) W) ((Z' , v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) ∷ proj₁ (env-metric γ)) (Wkn.wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫ +
       csn-to-nat₀ ⟪ comp-metric (wk-comp (wk-cong πᵥ) W) ((Z' , v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) ∷ proj₁ (env-metric γ)) (Wkn.wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫ (cs-to-csn cs))
      ≤
      suc (p1 (incr 2 b1) + (⟪ a1 ⟫ + p2 b1 * ⟪ a1 ⟫) + VMain.⟪ (λ z → k₀ z) ⟫ (p3 (incr 2 b1)) + csn-to-nat₀ (suc (p1 (incr 2 b1) + (⟪ a1 ⟫ + p2 b1 * ⟪ a1 ⟫) + VMain.⟪ (λ z → k₀ z) ⟫ (p3 (incr 2 b1)))) (cs-to-csn cs))

-}

  comp-metric-decreasing (∙app-pm M→M' π) = {!!}

        -- ∙app-lam     :   {W : (Γ ∙ X) ⊢ᶜ Y} → {N : V̲a̲l̲ Γ X} → {γ : Env Γ}
        --                → {cs : CompStack Δ Y} → {πₓ : Wk Γ Δ} → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}

  comp-metric-decreasing (∙app-lam {X = X} {Y = Y} {W = W} {N = N} {γ = γ} {cs = cs} {πₓ = πₓ} {wk≡ₓ = wk≡ₓ}) =
    let
      a0 = comp-metric W ((X , v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) ∷ proj₁ (env-metric γ)) (wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs)
      a1 =                     v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs)
      a2 = comp-metric W (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs)
    in
      {!!}

{-

      suc (⟪ comp-metric W ((X , v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) ∷ proj₁ (env-metric γ)) (wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫ + csn-to-nat₀ ⟪ comp-metric W ((X , v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) ∷ proj₁ (env-metric γ)) (wkn-cong (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫ (cs-to-csn cs))
≤ 2+ (suc (⟪ v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ + count-in-comp h W * ⟪ v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ + ⟪ comp-metric W (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫ + csn-to-nat₀ (2+ (suc (⟪ v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ + count-in-comp h W * ⟪ v̲a̲l̲-metric N (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ + ⟪ comp-metric W (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) (cs-to-csn cs) ⟫))) (cs-to-csn cs)))

  suc (⟪ a0 ⟫                                          + csn-to-nat₀ ⟪ a0 ⟫ (cs-to-csn cs))
≤ (2+ (suc (⟪ a1 ⟫)) + count-in-comp h W * ⟪ a1 ⟫ + ⟪ a2 ⟫) + (csn-to-nat₀ (2+ (suc (⟪ a1 ⟫ + count-in-comp h W * ⟪ a1 ⟫ + ⟪ a2 ⟫))) (cs-to-csn cs))

TP: ⟪ a0 ⟫ ≤ (2+ (suc (⟪ a1 ⟫)) + count-in-comp h W * ⟪ a1 ⟫ + ⟪ a2 ⟫)

seems reasonable

-}

  comp-metric-decreasing (∘app N→N' π) = {!!}

{-

Goal: 2+ (p1 (val-metric (wk-val π M) (proj₁ (env-metric γ')) (proj₂ (env-metric γ')) (cs-to-csn cs)) + (⟪ v̲a̲l̲-metric N' (proj₁ (env-metric γ')) (proj₂ (env-metric γ')) (cs-to-csn cs) ⟫ + p2 (val-metric (wk-val π M) (proj₁ (env-metric γ')) (proj₂ (env-metric γ')) (cs-to-csn cs)) * ⟪ v̲a̲l̲-metric N' (proj₁ (env-metric γ')) (proj₂ (env-metric γ')) (cs-to-csn cs) ⟫) + ⟪ p3 (val-metric (wk-val π M) (proj₁ (env-metric γ')) (proj₂ (env-metric γ')) (cs-to-csn cs)) ⟫ + csn-to-nat₀ (suc (p1 (val-metric (wk-val π M) (proj₁ (env-metric γ')) (proj₂ (env-metric γ')) (cs-to-csn cs)) + (⟪ v̲a̲l̲-metric N' (proj₁ (env-metric γ')) (proj₂ (env-metric γ')) (cs-to-csn cs) ⟫ + p2 (val-metric (wk-val π M) (proj₁ (env-metric γ')) (proj₂ (env-metric γ')) (cs-to-csn cs)) * ⟪ v̲a̲l̲-metric N' (proj₁ (env-metric γ')) (proj₂ (env-metric γ')) (cs-to-csn cs) ⟫) + ⟪ p3 (val-metric (wk-val π M) (proj₁ (env-metric γ')) (proj₂ (env-metric γ')) (cs-to-csn cs)) ⟫)) (cs-to-csn cs))
≤     2+ (p1 (val-metric           M  (proj₁ (env-metric γ))  (proj₂ (env-metric γ))  (cs-to-csn cs)) + (⟪ val-metric N  (proj₁ (env-metric γ))  (proj₂ (env-metric γ))  (cs-to-csn cs) ⟫ + p2 (val-metric           M  (proj₁ (env-metric γ))  (proj₂ (env-metric γ))  (cs-to-csn cs)) * ⟪ val-metric N  (proj₁ (env-metric γ))  (proj₂ (env-metric γ))  (cs-to-csn cs) ⟫) + ⟪ p3 (val-metric           M  (proj₁ (env-metric γ))  (proj₂ (env-metric γ)) (cs-to-csn cs))  ⟫ + csn-to-nat₀ (2+  (p1 (val-metric           M  (proj₁ (env-metric γ))  (proj₂ (env-metric γ))  (cs-to-csn cs)) + (⟪ val-metric N  (proj₁ (env-metric γ)) (proj₂ (env-metric γ))   (cs-to-csn cs) ⟫ + p2 (val-metric           M  (proj₁ (env-metric γ))  (proj₂ (env-metric γ))  (cs-to-csn cs)) * ⟪ val-metric N  (proj₁ (env-metric γ))  (proj₂ (env-metric γ))  (cs-to-csn cs) ⟫) + ⟪ p3 (val-metric           M  (proj₁ (env-metric γ))  (proj₂ (env-metric γ))  (cs-to-csn cs)) ⟫)) (cs-to-csn cs))

seems easy
-}

  comp-metric-decreasing (∘var {M = M} {γ = γ} {i = i} {γ' = γ'} {W = W} {γ'' = γ''} {cs = cs} {cs' = cs'} {πₓ = πₓ} {πₓ'' = πₓ''} {wk≡ₓ = wk≡ₓ} {wk≡ₓ'' = wk≡ₓ''} M→i π' x₁ πᵥ) =
    let
      a1 = comp-metric W (proj₁ (env-metric γ'')) (proj₂ (env-metric γ'')) (cs-to-csn cs')
      a2 = val-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs)
    in
      {!!}

{-

   suc (⟪ comp-metric W (proj₁ (env-metric γ'')) (proj₂ (env-metric γ'')) (cs-to-csn cs') ⟫ + csn-to-nat₀ ⟪ comp-metric W (proj₁ (env-metric γ'')) (proj₂ (env-metric γ'')) (cs-to-csn cs') ⟫ (cs-to-csn cs'))
≤  suc (⟪ val-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ + 0 + csn-to-nat₀ (suc (⟪ val-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ + 0)) (cs-to-csn cs))

  suc (⟪ a1 ⟫ + csn-to-nat₀ ⟪ a1 ⟫ (cs-to-csn cs'))
≤ suc (⟪ a2 ⟫ + csn-to-nat₀ (suc (⟪ a2 ⟫)) (cs-to-csn cs))

TP: ⟪ a1 ⟫ ≤ ⟪ a2 ⟫

seems easy

-}

-------------------------------------------------------
-------------------------------------------------------
-------------------------------------------------------

-------------------------------------------------------
  --postulate debuglemma : m ≤ n
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
    ... | steps i>>T (found-lam {X = X} {W = W} {γ = γ₁}) i≡T π₁ w≡γ T≤S θ with comp-eval-rec W (γ ﹐ N) (wk-cong π₁) cs (wk-wk πₓ) wk≡₀ n debuglemma
    ... | steps {T = T} W>WT HT S≡T cM =

    -- with app-eval-rec (lam W) N γ π₁ cs πₓ wk≡₀ n debuglemma
    -- ... | steps {T = T} W>WT HT S≡T cM =

                 steps

                    ((∙⟨ a̲pp (wk-val π (var i)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-var i>>T π₁ T≤S θ ⟩ W>WT))

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

                    cM

                 -- steps

                 --    (∙⟨ a̲pp (wk-val π (var i)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-var i>>T π₁ T≤S θ ⟩ W>WT)

                 --    HT

                 --    ( (< ⟦ wk-mem π i ⟧ᵐ , ⟦ toVal N ⟧ᵛ > ； Data.Product.uncurry idf) ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ
                 --     ≡⟨ refl ⟩
                 --      ⟦ wk-mem π i ⟧ᵐ ⟦ γ ⟧ᴱ (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                 --     ≡⟨ cong (λ x → x (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) i≡T ⟩
                 --      ⟦ W ⟧ᶜ (⟦ γ₁ ⟧ᴱ , (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ))  (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                 --     ≡⟨ cong (λ x → ⟦ W ⟧ᶜ (x , (⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ))  (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (sym w≡γ) ⟩
                 --      ⟦ W ⟧ᶜ (⟦ π₁ ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal N ⟧ᵛ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                 --     ≡⟨ S≡T ⟩
                 --      ⟦ T ⟧ᶜꟴ ∎)

                 --    (compstate-metric ((∙⟨ a̲pp (wk-val π (var i)) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀}) ∷ cM)

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
    ... | steps i>>T (found-comp {X = X} {W = W'} {γ = γ'} {cs = cs'} {π = πᶜ} {wk≡ = wk≡c}) i≡T π₂ w≡γ T≤S θ with
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

ex15 : ε ⊢ᶜ (`Unit)
--ex15 = push ((return unit)) (app (lam (return unit)) (pair (pair (pair (var h) (var h)) (var h)) (var h)))
--ex15 = push (push (app (lam {A = `Unit} (return unit)) unit) (return unit)) (app (lam (return unit)) (pair (pair (pair (var h) (var h)) (var h)) (var h)))
ex15 = push (push (app (lam {A = `Unit} (sub (var (var h)) (return unit))) unit) (return unit)) (return unit)

--  88 ∷ 347 ∷ 102 ∷ 100 ∷ 96 ∷ 91 ∷ 46 ∷ 44 ∷ 42 ∷ 32 ∷ 26 ∷ 14 ∷ 4 ∷ 2 ∷ []
-- 304 ∷ 347 ∷ 102 ∷ 100 ∷ 96 ∷ 91 ∷ 46 ∷ 44 ∷ 42 ∷ 32 ∷ 26 ∷ 14 ∷ 4 ∷ 2 ∷ []

-- ex13: 22 ∷ 12 ∷ 9 ∷ 2 ∷ []
-- ex14: 358 ∷ 357 ∷ 104 ∷ 101 ∷ 96 ∷ 91 ∷ 46 ∷ 44 ∷ 42 ∷ 32 ∷ 26 ∷ 14 ∷ 4 ∷ 2 ∷ []
_ : comp-eval-test-metric ex11 ≡ {! comp-eval-test-metric ex14!}
_ = let
      tm = push (push (app (lam {A = `Unit} (sub (var (var h)) (return unit))) unit) (return unit)) (app (lam (return unit)) (pair (pair (pair (var h) (var h)) (var h)) (var h)))
      tmR = (app (lam (return unit)) (pair (pair (pair (var h) (var h)) (var h)) (var h)))
      tmL = (push (app (lam {A = `Unit} (sub (var (var h)) (return unit))) unit) (return unit))
      csn1 = cs-to-csn ◻
      csn2 = cs-to-csn ((app (lam (return unit)) (pair (pair (pair (var h) (var h)) (var h)) (var h))) ⊲ ∗ ⦂⦂ ◻)
      e = env-metric ∗
      --cm1 = comp-metric tm (proj₁ e) (proj₂ e) csn1
      cmL = comp-metric tmL (proj₁ e) (proj₂ e) csn2
      cmR = comp-metric tmR (proj₁ e) (wkn-cons (proj₂ e)) csn1
      cmRcong = comp-metric tmR ((`Unit , λ x → comp-metric tmL (proj₁ e) (proj₂ e) csn2) ∷ (proj₁ e)) (wkn-cong (proj₂ e)) csn1
      --cm1l = comp-metric tmL (proj₁ e) (proj₂ e) csn1
      --c1+ = csn-to-nat₀ ⟪ cm1 ⟫ csn1
      --cm2 = comp-metric tmL (proj₁ e) (proj₂ e) csn2
      --c2+ = csn-to-nat₀ ⟪ cm2 ⟫ csn2
    {-
      tm2 = (push ((sub (var (var h)) (return unit))) (return unit))
      e1 = env-metric ∗ csn1
      e2 = env-metric ∗ csn2
      cm1 = comp-metric tm1 (proj₁ e1) (proj₂ e1) csn1
      cm1l = comp-metric tm2 (proj₁ e1) (proj₂ e1) csn1
      --cm1r = comp-metric tm1r ((proj₁ e1)) (wkn-cong (proj₂ e1)) csn1
      c1+ = csn-to-nat₀ ⟪ cm1 ⟫ csn1
      cm2 = comp-metric tm2 (proj₁ e1) (proj₂ e1) csn2
      c2+ = csn-to-nat₀ ⟪ cm2 ⟫ csn2
    -}
      x = {!!}
    in
    {!c2+!}

-- 138 ∷ 327 ∷ 102 ∷ 100 ∷ 96 ∷ 91 ∷ 46 ∷ 44 ∷ 42 ∷ 32 ∷ 26 ∷ 14 ∷ 4 ∷ 2 ∷ []

{-
ex14 = push (push (app (lam {A = `Unit} (sub (var (var h)) (return unit))) unit) (return unit)) (app (lam (return unit)) (pair (pair (pair (var h) (var h)) (var h)) (var h)))
∘⟨push (push (app (lam (sub (var (var h)) (return unit))) unit) (return unit)) (app (lam (return unit)) (pair (pair (pair (var h) (var h)) (var h)) (var h))) ⊰ ∗ ╎ ◻ ⟩
 →ᶜ⟨ ∘push ⟩
∘⟨push (app (lam (sub (var (var h)) (return unit))) unit) (return unit) ⊰ ∗ ╎ app (lam (return unit)) (pair (pair (pair (var h) (var h)) (var h)) (var h)) ⊲ ∗ ⦂⦂ ◻ ⟩
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

