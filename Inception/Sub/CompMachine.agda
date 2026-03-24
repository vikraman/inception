{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.CompMachine (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_; _$_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; subst)
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
                      → {VS>VT : (csn : List (ℕ × ℕ)) → proj₁ (proj₂ (v̲a̲l̲-mono-metric M' (proj₁ (env-mono-metric γ')) (proj₂ (env-mono-metric γ')))) csn
                                ≤ᴹ proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) csn} -- for termination -}
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
                       -- → (T≤S : (csn : List (Σ ℕ (λ x → ℕ))) → m-⇒ 1 (count-in-comp h W) (comp-metric W (proj₁ (env-metric γ')) (Wkn.wkn-cons (proj₂ (env-metric γ'))) csn)
                       --    ≤ᴹ lookup-metric i (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn) -- to prove termination
                       → {!!} --(T≤S : (csn : List (Σ ℕ (λ x → ℕ))) → m-⇒ 1 {!!} ((proj₁ (comp-mono-metric W (proj₁ (env-mono-metric γ')) (Wkn.wkn-cons (proj₂ (env-mono-metric γ'))))) csn)
                          --≤ᴹ (proj₁ (lookup-mono-metric i (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) csn) -- to prove termination
                       → {!!} --(θ : WkE πᵥ (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric γ'))) -- to prove termination
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

  compstate-metric : CompState → ℕ
  compstate-metric ((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π}) =
    let
      csn = cs-to-csn cs
      e = env-mono-metric γ
      w = ⟪ (proj₁ (proj₂ (comp-mono-metric W (proj₁ e) (proj₂ e)))) csn ⟫
    in
      w + csn-to-nat₀ w csn
  compstate-metric ((∙⟨ W ⊰ γ ╎ cs ⟩) {π = π}) =
    let
      csn = cs-to-csn cs
      e = env-mono-metric γ
      w = ⟪ (proj₁ (proj₂ (c̲o̲m̲p-mono-metric W (proj₁ e) (proj₂ e)))) csn ⟫
    in
      w + csn-to-nat₀ w csn

{-
  compstate-metric : CompState → ℕ
  compstate-metric ((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π}) =
    let
      csn = cs-to-csn cs
      e = env-metric γ
      w = ⟪ comp-metric W (proj₁ e) (proj₂ e) csn ⟫
    in
      w + csn-to-nat₀ w csn
  compstate-metric ((∙⟨ W ⊰ γ ╎ cs ⟩) {π = π}) =
    let
      csn = cs-to-csn cs
      e = env-metric γ
      w = ⟪ c̲o̲m̲p-metric W (proj₁ e) (proj₂ e) csn ⟫
    in
      w + csn-to-nat₀ w csn
-}

-------------------------------------------------------------------------------------------------

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

  {- MAYBE UNNECCESSARY

  mutual

    postulate wk-val-count-eq :   (π : Wk Γ Γ') → (i : Γ' ∋ Y) → (M : Val Γ' X)
                      → (E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))) → (ϖ : Wkn Γ' E) → (csn : List (ℕ × ℕ))
                      → count-in-val i M E ϖ csn ≡ count-in-val (wk-mem π i) (wk-val π M) E (wk-e π ϖ) csn
    -- probably easy
    {-
    wk-val-count-eq wk-ε () M E ϖ csn

    wk-val-count-eq (wk-cong π) Cx.h (var Cx.h) E ϖ csn = refl
    wk-val-count-eq (wk-cong π) Cx.h (var (Cx.t i)) E ϖ csn = refl

    wk-val-count-eq (wk-cong π) Cx.h (lam W) E ϖ csn = wk-comp-count-eq (wk-cong (wk-cong π)) (t h) W E (wkn-cons ϖ) csn
    wk-val-count-eq (wk-cong π) Cx.h (pair M₁ M₂) E ϖ csn = cong₂ _+_ (wk-val-count-eq (wk-cong π) h M₁ E ϖ csn) (wk-val-count-eq (wk-cong π) h M₂ E ϖ csn)
    wk-val-count-eq (wk-cong π) Cx.h (pm M N) E ϖ csn =
      let
        a1 = wk-val-count-eq (wk-cong π) h M E ϖ csn
        a2 = wk-val-count-eq (wk-cong (wk-cong (wk-cong π))) h N E (wkn-cons (wkn-cons ϖ)) csn
        a3 = wk-val-count-eq (wk-cong (wk-cong (wk-cong π))) (t h) N E (wkn-cons (wkn-cons ϖ)) csn
        a4 = wk-val-count-eq (wk-cong (wk-cong (wk-cong π))) (t (t h)) N E (wkn-cons (wkn-cons ϖ)) csn
        b1 = cong₂ _*_ a1 (cong suc (cong₂ _+_ a2 a3))
        b2 = cong₂ _+_ b1 a4
      in
      count-in-val h (pm M N) E ϖ csn
      ≡⟨ refl ⟩
        count-in-val h M E ϖ csn * suc (count-in-val h N E (Wkn.wkn-cons (Wkn.wkn-cons ϖ)) csn + count-in-val (t h) N E (Wkn.wkn-cons (Wkn.wkn-cons ϖ)) csn) + count-in-val (t (t h)) N E (Wkn.wkn-cons (Wkn.wkn-cons ϖ)) csn
      ≡⟨ b2 ⟩
        count-in-val h (wk-val (wk-cong π) M) E (wk-e (wk-cong π) ϖ) csn * suc (count-in-val h (wk-val (wk-cong (wk-cong (wk-cong π))) N) E (Wkn.wkn-cons (Wkn.wkn-cons (wk-e (wk-cong π) ϖ))) csn + count-in-val (t h) (wk-val (wk-cong (wk-cong (wk-cong π))) N) E (Wkn.wkn-cons (Wkn.wkn-cons (wk-e (wk-cong π) ϖ))) csn) + count-in-val (t (t h)) (wk-val (wk-cong (wk-cong (wk-cong π))) N) E (Wkn.wkn-cons (Wkn.wkn-cons (wk-e (wk-cong π) ϖ))) csn
      ≡⟨ refl ⟩
      count-in-val h (pm (wk-val (wk-cong π) M) (wk-val (wk-cong (wk-cong (wk-cong π))) N)) E (wk-e (wk-cong π) ϖ) csn ∎

    wk-val-count-eq (wk-cong π) Cx.h unit E ϖ csn = refl

    wk-val-count-eq (wk-cong π) (Cx.t i) (var i₁) E ϖ csn = {!!}
    wk-val-count-eq (wk-cong π) (Cx.t i) (lam W) E ϖ csn = {!!}
    wk-val-count-eq (wk-cong π) (Cx.t i) (pair M₁ M₂) E ϖ csn = {!!}
    wk-val-count-eq (wk-cong π) (Cx.t i) (pm M N) E ϖ csn = {!!}
    wk-val-count-eq (wk-cong π) (Cx.t i) unit E ϖ csn = {!!}

    wk-val-count-eq (wk-wk π) Cx.h (var i) E ϖ csn = {!!}
    wk-val-count-eq (wk-wk π) Cx.h (lam x) E ϖ csn = {!!}
    wk-val-count-eq (wk-wk π) Cx.h (pair M M₁) E ϖ csn = {!!}
    wk-val-count-eq (wk-wk π) Cx.h (pm M M₁) E ϖ csn = {!!}
    wk-val-count-eq (wk-wk π) Cx.h unit E ϖ csn = {!!}
    wk-val-count-eq (wk-wk π) (Cx.t i) (var i₁) E ϖ csn = {!!}
    wk-val-count-eq (wk-wk π) (Cx.t i) (lam x) E ϖ csn = {!!}
    wk-val-count-eq (wk-wk π) (Cx.t i) (pair M M₁) E ϖ csn = {!!}
    wk-val-count-eq (wk-wk π) (Cx.t i) (pm M M₁) E ϖ csn = {!!}
    wk-val-count-eq (wk-wk π) (Cx.t i) unit E ϖ csn = {!!}
    -}

    postulate wk-comp-count-eq :   (π : Wk Γ Γ') → (i : Γ' ∋ Y) → (W : Comp Γ' X)
                       → (E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))) → (ϖ : Wkn Γ' E) → (csn : List (ℕ × ℕ))
                       → count-in-comp i W E ϖ csn ≡ count-in-comp (wk-mem π i) (wk-comp π W) E (wk-e π ϖ) csn
    -- probably easy
    --wk-comp-count-eq π i W E ϖ csn = {!!}


  {- OLD
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

  -}

-------------------------------------------------------------------------------------------------

{-
  data Missing-i : {E : List (Σ[ Z ∈ Ty ] (List (ℕ × ℕ) → TermMetric Z))} → (i : Γ ∋ X) → (ϖ : Wkn Γ E) → Set where
    missing-h : {E : List (Σ[ Z ∈ Ty ] (List (ℕ × ℕ) → TermMetric Z))} → (ϖ : Wkn Γ E) → Missing-i {X = X} h (wkn-cons ϖ)
    missing-t-cong : {E : List (Σ[ Z ∈ Ty ] (List (ℕ × ℕ) → TermMetric Z))} → {e : (List (ℕ × ℕ) → TermMetric B)}
                     → (i : Γ ∋ X) → (ϖ : Wkn Γ E) → (μ : Missing-i i ϖ) → Missing-i (t {B = B} i) (wkn-cong {e = e} ϖ)
    missing-t-cons : {E : List (Σ[ Z ∈ Ty ] (List (ℕ × ℕ) → TermMetric Z))}
                     → (i : Γ ∋ X) → (ϖ : Wkn Γ E) → (μ : Missing-i i ϖ) → Missing-i (t {B = B} i) (wkn-cons ϖ)

  with-i :  {E : List (Σ[ Z ∈ Ty ] (List (ℕ × ℕ) → TermMetric Z))} → (i : Γ ∋ X) → (ϖ : Wkn Γ E) → (μ : Missing-i i ϖ) → (e : (List (ℕ × ℕ) → TermMetric X))
           → Σ[ E' ∈ List (Σ[ Z ∈ Ty ] (List (ℕ × ℕ) → TermMetric Z)) ] (Wkn Γ E')
  with-i i (wkn-cons ϖ) (missing-h ϖ) e = _ , wkn-cong {e = e} ϖ
  with-i (t i) (wkn-cong ϖ) (missing-t-cong {e = e'} i ϖ μ) e =
    let
      a1 = with-i i ϖ μ e
    in
    _ , wkn-cong {e = e'} (proj₂ a1)
  with-i (t i) (wkn-cons ϖ) (missing-t-cons i ϖ μ) e =
    let
      a1 = with-i i ϖ μ e
    in
      _ , wkn-cons (proj₂ a1)
-}

  {-
  mutual
    fun-val-lemma :    (M : Val Γ Y)
                     → (nm : (List (ℕ × ℕ) → TermMetric X))
                     → (E : List (Σ[ Z ∈ Ty ] (List (ℕ × ℕ) → TermMetric Z))) → (ϖ : Wkn Γ E) → (csn : List (ℕ × ℕ))
                     → (i : Γ ∋ X) → (μ : Missing-i i ϖ)
                     →   ⟪ val-metric M (proj₁ (with-i i ϖ μ nm)) (proj₂ (with-i i ϖ μ nm)) csn ⟫
                       ≡ count-in-val i M * ⟪ nm csn ⟫ + ⟪ val-metric M E ϖ csn ⟫
    fun-val-lemma M nm E ϖ csn i μ = {!!}


    fun-comp-lemma :   (W : Comp Γ Y)
                     → (nm : (List (ℕ × ℕ) → TermMetric X))
                     → (E : List (Σ[ Z ∈ Ty ] (List (ℕ × ℕ) → TermMetric Z))) → (ϖ : Wkn Γ E) → (csn : List (ℕ × ℕ))
                     → (i : Γ ∋ X) → (μ : Missing-i i ϖ)
                     →   ⟪ comp-metric W (proj₁ (with-i i ϖ μ nm)) (proj₂ (with-i i ϖ μ nm)) csn ⟫
                       ≡ count-in-comp i W * ⟪ nm csn ⟫ + ⟪ comp-metric W E ϖ csn ⟫
    fun-comp-lemma (return M) nm E ϖ csn i μ rewrite
        +-comm {n = count-in-val i M * ⟪ nm csn ⟫} {m = 2+ ⟪ val-metric M E ϖ csn ⟫}
      | +-comm {n = ⟪ val-metric M E ϖ csn ⟫} {m = count-in-val i M * ⟪ nm csn ⟫}
      | fun-val-lemma M nm E ϖ csn i μ
      = refl
    fun-comp-lemma (pm {A = A} {B = B} M W) nm E ϖ csn i μ --rewrite
      --  fun-val-lemma M nm E ϖ csn i μ
      -- |
      --fun-comp-lemma W nm ((B , (λ c → rhs (val-metric M E ϖ c))) ∷ (A , (λ c → lhs (val-metric M E ϖ c))) ∷ E) (Wkn.wkn-cong (Wkn.wkn-cong ϖ)) csn (t (t i)) (missing-t-cong (t i) (Wkn.wkn-cong ϖ) (missing-t-cong i ϖ μ))
      =
      let
        a1 = fun-val-lemma M nm E ϖ csn i μ
        a2 = fun-comp-lemma W nm ((B , (λ c → rhs (val-metric M E ϖ c))) ∷ (A , (λ c → lhs (val-metric M E ϖ c))) ∷ E) (Wkn.wkn-cong (Wkn.wkn-cong ϖ)) csn (t (t i)) (missing-t-cong (t i) (Wkn.wkn-cong ϖ) (missing-t-cong i ϖ μ))
      in
        ⟪ comp-metric (pm M W) (proj₁ (with-i i ϖ μ nm)) (proj₂ (with-i i ϖ μ nm)) csn ⟫
      ≡⟨ refl ⟩
          suc (vx (val-metric M (proj₁ (with-i i ϖ μ nm)) (proj₂ (with-i i ϖ μ nm)) csn) + ⟪ comp-metric W (proj₁ (with-i i ϖ μ nm)) (Wkn.wkn-cons (Wkn.wkn-cons (proj₂ (with-i i ϖ μ nm)))) csn ⟫ + ⟪ comp-metric W ((B , (λ c → rhs (val-metric M (proj₁ (with-i i ϖ μ nm)) (proj₂ (with-i i ϖ μ nm)) c))) ∷ (A , (λ c → lhs (val-metric M (proj₁ (with-i i ϖ μ nm)) (proj₂ (with-i i ϖ μ nm)) c))) ∷ proj₁ (with-i i ϖ μ nm)) (Wkn.wkn-cong (Wkn.wkn-cong (proj₂ (with-i i ϖ μ nm)))) csn ⟫)
      ≡⟨ {!!} ⟩
          (count-in-val i M + count-in-comp (t (t i)) W) * ⟪ nm csn ⟫ + suc (vx (val-metric M E ϖ csn) + ⟪ comp-metric W E (Wkn.wkn-cons (Wkn.wkn-cons ϖ)) csn ⟫ + ⟪ comp-metric W ((B , (λ c → rhs (val-metric M E ϖ c))) ∷ (A , (λ c → lhs (val-metric M E ϖ c))) ∷ E) (Wkn.wkn-cong (Wkn.wkn-cong ϖ)) csn ⟫)
      ≡⟨ refl ⟩
        count-in-comp i (pm M W) * ⟪ nm csn ⟫ + ⟪ comp-metric (pm M W) E ϖ csn ⟫ ∎
    fun-comp-lemma (push W₁ W₂) nm E ϖ csn i μ = {!!}
    fun-comp-lemma (app M N) nm E ϖ csn i μ = {!!}
    fun-comp-lemma (var M) nm E ϖ csn i μ = {!!}
    fun-comp-lemma (sub W₁ W₂) nm E ϖ csn i μ = {!!}
    -}

{-
  mutual
    fun-val-lemma : (M : Val (Γ ∙ X) Y) → (nm : (List (ℕ × ℕ) → TermMetric X)) → (E : List (Σ[ Z ∈ Ty ] (List (ℕ × ℕ) → TermMetric Z))) → (ϖ : Wkn Γ E) → (csn : List (ℕ × ℕ)) → ⟪ val-metric M ((X , nm) ∷ E) (wkn-cong ϖ) csn ⟫ ≡ count-in-val h M * ⟪ nm csn ⟫ + ⟪ val-metric M E (wkn-cons ϖ) csn ⟫
    fun-val-lemma {X = X} {Y = Y} M nm E ϖ csn = {!!}

    fun-comp-lemma :   (W : Comp (Γ ∙ X) Y) → (nm : (List (ℕ × ℕ) → TermMetric X)) → (E : List (Σ[ Z ∈ Ty ] (List (ℕ × ℕ) → TermMetric Z))) → (ϖ : Wkn Γ E) → (csn : List (ℕ × ℕ))
                     → ⟪ comp-metric W ((X , nm) ∷ E) (wkn-cong ϖ) csn ⟫ ≡ count-in-comp h W * ⟪ nm csn ⟫ + ⟪ comp-metric W E (wkn-cons ϖ) csn ⟫
    fun-comp-lemma {X = X} {Y = Y} (return M) nm E ϖ csn rewrite
        +-comm {n = count-in-val h M * ⟪ nm csn ⟫} {m = 2+ ⟪ val-metric M E (wkn-cons ϖ) csn ⟫}
      | +-comm {n = ⟪ val-metric M E (wkn-cons ϖ) csn ⟫} {m = count-in-val h M * ⟪ nm csn ⟫}
      | fun-val-lemma M nm E ϖ csn
      = refl
    fun-comp-lemma {X = X} (pm {A = A} {B = B} M W) nm E ϖ csn =
        let
          a1 = fun-comp-lemma W {!nm!} E (Wkn.wkn-cons (Wkn.wkn-cons ϖ)) csn
        in
        ⟪ comp-metric (pm M W) ((X , nm) ∷ E) (wkn-cong ϖ) csn ⟫
        ≡⟨ refl ⟩
           suc (vx (val-metric M ((X , nm) ∷ E) (Wkn.wkn-cong ϖ) csn)                                                  + ⟪ comp-metric W ((X , nm) ∷ E) (Wkn.wkn-cons (Wkn.wkn-cons (Wkn.wkn-cong ϖ))) csn ⟫ + ⟪ comp-metric W ((B , (λ c → rhs (val-metric M ((X , nm) ∷ E) (Wkn.wkn-cong ϖ) c))) ∷ (A , (λ c → lhs (val-metric M ((X , nm) ∷ E) (Wkn.wkn-cong ϖ) c))) ∷ (X , nm) ∷ E) (Wkn.wkn-cong (Wkn.wkn-cong (Wkn.wkn-cong ϖ))) csn ⟫)
        ≡⟨ {!!} ⟩
           (count-in-val h M + count-in-comp (t (t h)) W) * ⟪ nm csn ⟫ + suc (vx (val-metric M E (Wkn.wkn-cons ϖ) csn) + ⟪ comp-metric W E (Wkn.wkn-cons (Wkn.wkn-cons (Wkn.wkn-cons ϖ))) csn ⟫              + ⟪ comp-metric W ((B , (λ c → rhs (val-metric M E (Wkn.wkn-cons ϖ) c))) ∷ (A , (λ c → lhs (val-metric M E (Wkn.wkn-cons ϖ) c))) ∷ E) (Wkn.wkn-cong (Wkn.wkn-cong (Wkn.wkn-cons ϖ))) csn ⟫)
        ≡⟨ refl ⟩
         count-in-comp h (pm M W) * ⟪ nm csn ⟫ + ⟪ comp-metric (pm M W) E (wkn-cons ϖ) csn ⟫ ∎
{-
Goal:   suc (vx (val-metric M ((X , nm) ∷ E) (Wkn.wkn-cong ϖ) csn) + ⟪ comp-metric W ((X , nm) ∷ E) (Wkn.wkn-cons (Wkn.wkn-cons (Wkn.wkn-cong ϖ))) csn ⟫
      + ⟪ comp-metric W ((B , (λ c → rhs (val-metric M ((X , nm) ∷ E) (Wkn.wkn-cong ϖ) c))) ∷ (A , (λ c → lhs (val-metric M ((X , nm) ∷ E) (Wkn.wkn-cong ϖ) c))) ∷ (X , nm) ∷ E) (Wkn.wkn-cong (Wkn.wkn-cong (Wkn.wkn-cong ϖ))) csn⟫)
      ≡
        (count-in-val h M + count-in-comp (t (t h)) W) * ⟪ nm csn ⟫
      + suc (vx (val-metric M E (Wkn.wkn-cons ϖ) csn) + ⟪ comp-metric W E (Wkn.wkn-cons (Wkn.wkn-cons (Wkn.wkn-cons ϖ))) csn ⟫ + ⟪ comp-metric W ((B , (λ c → rhs (val-metric M E (Wkn.wkn-cons ϖ) c))) ∷ (A , (λ c → lhs (val-metric M E (Wkn.wkn-cons ϖ) c))) ∷ E) (Wkn.wkn-cong (Wkn.wkn-cong (Wkn.wkn-cons ϖ))) csn ⟫)
      ≡
        (count-in-val h M) * ⟪ nm csn ⟫
        (count-in-comp (t (t h)) W) * ⟪ nm csn ⟫
      + suc (vx (val-metric M E (Wkn.wkn-cons ϖ) csn) + ⟪ comp-metric W E (Wkn.wkn-cons (Wkn.wkn-cons (Wkn.wkn-cons ϖ))) csn ⟫ + ⟪ comp-metric W ((B , (λ c → rhs (val-metric M E (Wkn.wkn-cons ϖ) c))) ∷ (A , (λ c → lhs (val-metric M E (Wkn.wkn-cons ϖ) c))) ∷ E) (Wkn.wkn-cong (Wkn.wkn-cong (Wkn.wkn-cons ϖ))) csn ⟫)
      ≡

-}
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

{-
  data WkCW  : {E E' : List ℕ} → (ç : WkC Γ E) → (ç' : WkC Γ E') → Set where
    wkcw-nil       : {ç : WkC ε []} → {ç' : WkC ε []} → WkCW ç ç'
    wkcw-cong     :   {E E' : List ℕ}
                  → {ç : WkC Γ E} → {ç' : WkC Γ E'}
                  → {cnt : ℕ}
                  → (ç≤ç' : WkCW ç ç') → WkCW (wkc-cong {Y = Y} {e = cnt} ç) (wkc-cong {Y = Y} {e = cnt} ç')
    wkcw-wk       :  {E E' : List ℕ}
                  → {ç : WkC Γ E} → {ç' : WkC Γ E'}
                  → (ç≤ç' : WkCW ç ç') → WkCW (wkc-cons {Y = Y} ç) (wkc-cons {Y = Y} ç')
    wkcw-skip     :  {E E' : List ℕ}
                  → {ç : WkC Γ E} → {ç' : WkC Γ E'}
                  → {cnt : ℕ}
                  → (ç≤ç' : WkCW ç ç') → WkCW (wkc-cong {Y = Y} {e = cnt} ç) (wkc-cons {Y = Y} ç')
-}

  data WkCW  : {E E' : List ℕ} → (ç : WkC Γ E) → (ç' : WkC Γ E') → Set where
    wkcw-nil       : {ç : WkC ε []} → {ç' : WkC ε []} → WkCW ç ç'
    wkcw-cong     :   {E E' : List ℕ}
                  → {ç : WkC Γ E} → {ç' : WkC Γ E'}
                  → {cnt₁ cnt₂ : ℕ}
                  → (cnt₁≤cnt₂ : cnt₁ ≤ cnt₂)
                  → (ç≤ç' : WkCW ç ç') → WkCW (wkc-cong {Y = Y} {e = cnt₂} ç) (wkc-cong {Y = Y} {e = cnt₁} ç')
    wkcw-wk       :  {E E' : List ℕ}
                  → {ç : WkC Γ E} → {ç' : WkC Γ E'}
                  → (ç≤ç' : WkCW ç ç') → WkCW (wkc-cons {Y = Y} ç) (wkc-cons {Y = Y} ç')
    wkcw-skip     :  {E E' : List ℕ}
                  → {ç : WkC Γ E} → {ç' : WkC Γ E'}
                  → {cnt : ℕ}
                  → (ç≤ç' : WkCW ç ç') → WkCW (wkc-cong {Y = Y} {e = cnt} ç) (wkc-cons {Y = Y} ç')

  wkcw-id : {E : List ℕ} → {ϖ : WkC Γ E} → WkCW ϖ ϖ
  wkcw-id {E = E} {ϖ = wkc-nil} = wkcw-nil
  wkcw-id {E = E} {ϖ = wkc-cong ϖ} = wkcw-cong n≤m+n wkcw-id
  wkcw-id {E = E} {ϖ = wkc-cons ϖ} = wkcw-wk wkcw-id

  lookup-wkcw-lemma : (i : Γ ∋ X) → (E E' : List ℕ) → (nz : NonZeroList E) → (nz' : NonZeroList E') → (ç : WkC Γ E) → (ç' : WkC Γ E') → (ζ : WkCW ç ç')
                    → (lcount i E' ç') ≤ (lcount i E ç)
  lookup-wkcw-lemma Cx.h [] [] nz nz' ç ç' ζ rewrite empty-lcount h ç | empty-lcount h ç' = s≤s z≤n
  lookup-wkcw-lemma Cx.h [] (x ∷ E') nz nz' ç ç' (wkcw-wk ζ) = s≤s z≤n
  lookup-wkcw-lemma Cx.h (x ∷ E) [] nz nz' ç ç' ζ rewrite empty-lcount h ç' = lcount-non-zero h (x ∷ E) nz ç
  lookup-wkcw-lemma Cx.h (x ∷ E) (x₁ ∷ E') nz nz' ç ç' (wkcw-cong cnt₁≤cnt₂ ζ) = cnt₁≤cnt₂
  lookup-wkcw-lemma Cx.h (x ∷ E) (x₁ ∷ E') nz nz' ç ç' (wkcw-wk ζ) = ≤-refl
  lookup-wkcw-lemma {X = X} Cx.h (x ∷ E) (x₁ ∷ E') nz nz' (wkc-cong ç) (wkc-cons ç') (wkcw-skip ζ) = lcount-non-zero {Z = X} h (x ∷ E) nz (wkc-cong ç)
  lookup-wkcw-lemma (Cx.t i) [] [] nz nz' ç ç' ζ rewrite empty-lcount (t i) ç | empty-lcount (t i) ç' = s≤s z≤n
  lookup-wkcw-lemma (Cx.t {B = B} i) [] (x ∷ E') nz nz' (wkc-cons ç) (wkc-cons ç') (wkcw-wk ζ) rewrite empty-lcount (t {B = B} i) (wkc-cons ç) =
    let
      a0 = lookup-wkcw-lemma i [] (x ∷ E') nz nz' ç ç' ζ
      a1 : lcount i (x ∷ E') ç' ≤ 1
      a1 = subst (λ y → lcount i (x ∷ E') ç' ≤ y) (empty-lcount i ç) a0
    in
    a1
  lookup-wkcw-lemma (Cx.t i) (x ∷ E) [] nz nz' ç ç' ζ rewrite empty-lcount (t i) ç' = lcount-non-zero (t i) (x ∷ E) nz ç
  lookup-wkcw-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (suc-nz-list n nz) (suc-nz-list n₁ nz') (wkc-cong ç) (wkc-cong ç') (wkcw-cong cnt₁≤cnt₂ ζ) = lookup-wkcw-lemma i E E' nz nz' ç ç' ζ
  lookup-wkcw-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (suc-nz-list n nz) (suc-nz-list n₁ nz') (wkc-cong ç) (wkc-cons ç') (wkcw-skip ζ) = lookup-wkcw-lemma i E (suc n₁ ∷ E') nz (NonZeroList.suc-nz-list n₁ nz') ç ç' ζ
  lookup-wkcw-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') nz nz' (wkc-cons ç) (wkc-cong ç') ()
  lookup-wkcw-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (suc-nz-list n nz) (suc-nz-list n₁ nz') (wkc-cons ç) (wkc-cons ç') (wkcw-wk ζ) = lookup-wkcw-lemma i (suc n ∷ E) (suc n₁ ∷ E') (NonZeroList.suc-nz-list n nz) (NonZeroList.suc-nz-list n₁ nz') ç ç' ζ

  val-wkcw-lemma : (M : Val Γ X) → (E E' : List ℕ) → (nz : NonZeroList E) → (nz' : NonZeroList E') → (ç : WkC Γ E) → (ç' : WkC Γ E') → (ζ : WkCW ç ç')
                    → (vcount M E' ç') ≤ (vcount M E ç)
  val-wkcw-lemma (var i) E E' nz nz' ç ç' ζ = lookup-wkcw-lemma i E E' nz nz' ç ç' ζ
  val-wkcw-lemma (lam W) E E' nz nz' ç ç' ζ = {!!}
  val-wkcw-lemma (pair M₁ M₂) E E' nz nz' ç ç' ζ =
    let
      a0 = val-wkcw-lemma M₁ E E' nz nz' ç ç' ζ
      a1 = val-wkcw-lemma M₂ E E' nz nz' ç ç' ζ
    in
    +-≤-cong a0 a1
  val-wkcw-lemma (pm {A = A} {B = B} M N) E E' nz nz' ç ç' ζ =
    let
      a0 = val-wkcw-lemma M E E' nz nz' ç ç' ζ
      a1 = wkcw-cong {Y = B} a0 (wkcw-cong {Y = A} a0 ζ)
      a2 : NonZeroList (suc (pred (vcount M E ç)) ∷ suc (pred (vcount M E ç)) ∷ E)
      a2 = suc-nz-list (vcount M E ç ∸ 1) (suc-nz-list (vcount M E ç ∸ 1) nz)
      a3 : NonZeroList ((vcount M E ç) ∷ (vcount M E ç) ∷ E)
      a3 = subst (λ x → NonZeroList (x ∷ x ∷ E)) (sym (pred-eq (vcount-non-zero M E nz ç))) a2
      b2 : NonZeroList (suc (pred (vcount M E' ç')) ∷ suc (pred (vcount M E' ç')) ∷ E')
      b2 = suc-nz-list (vcount M E' ç' ∸ 1) (suc-nz-list (vcount M E' ç' ∸ 1) nz')
      b3 : NonZeroList ((vcount M E' ç') ∷ (vcount M E' ç') ∷ E')
      b3 = subst (λ x → NonZeroList (x ∷ x ∷ E')) (sym (pred-eq (vcount-non-zero M E' nz' ç'))) b2
      c1 = val-wkcw-lemma N (vcount M E ç ∷ vcount M E ç ∷ E) (vcount M E' ç' ∷ vcount M E' ç' ∷ E') a3 b3 (WkC.wkc-cong (WkC.wkc-cong ç)) (WkC.wkc-cong (WkC.wkc-cong ç')) a1
    in
    c1
  val-wkcw-lemma unit E E' nz nz' ç ç' ζ = s≤s z≤n


  comp-wkcw-lemma : (W : Comp Γ X) → (E E' : List ℕ) → (nz : NonZeroList E) → (nz' : NonZeroList E') → (ç : WkC Γ E) → (ç' : WkC Γ E') → (ζ : WkCW ç ç')
                    → (ccount W E' ç') ≤ (ccount W E ç)
  comp-wkcw-lemma (return M) E E' nz nz' ç ç' ζ = val-wkcw-lemma M E E' nz nz' ç ç' ζ
  comp-wkcw-lemma (pm {A = A} {B = B} M W) E E' nz nz' ç ç' ζ =
    let
      a0 = val-wkcw-lemma M E E' nz nz' ç ç' ζ
      a1 = wkcw-cong {Y = B} a0 (wkcw-cong {Y = A} a0 ζ)
      a2 : NonZeroList (suc (pred (vcount M E ç)) ∷ suc (pred (vcount M E ç)) ∷ E)
      a2 = suc-nz-list (vcount M E ç ∸ 1) (suc-nz-list (vcount M E ç ∸ 1) nz)
      a3 : NonZeroList ((vcount M E ç) ∷ (vcount M E ç) ∷ E)
      a3 = subst (λ x → NonZeroList (x ∷ x ∷ E)) (sym (pred-eq (vcount-non-zero M E nz ç))) a2
      b2 : NonZeroList (suc (pred (vcount M E' ç')) ∷ suc (pred (vcount M E' ç')) ∷ E')
      b2 = suc-nz-list (vcount M E' ç' ∸ 1) (suc-nz-list (vcount M E' ç' ∸ 1) nz')
      b3 : NonZeroList ((vcount M E' ç') ∷ (vcount M E' ç') ∷ E')
      b3 = subst (λ x → NonZeroList (x ∷ x ∷ E')) (sym (pred-eq (vcount-non-zero M E' nz' ç'))) b2
      c1 = comp-wkcw-lemma W (vcount M E ç ∷ vcount M E ç ∷ E) (vcount M E' ç' ∷ vcount M E' ç' ∷ E') a3 b3 (WkC.wkc-cong (WkC.wkc-cong ç)) (WkC.wkc-cong (WkC.wkc-cong ç')) a1
    in
    c1
  comp-wkcw-lemma (push {A = A} W₁ W₂) E E' nz nz' ç ç' ζ =
    let
      a0 = comp-wkcw-lemma W₁ E E' nz nz' ç ç' ζ
      a1 = (wkcw-cong {Y = A} a0 ζ)
      a2 : NonZeroList (suc (pred (ccount W₁ E ç)) ∷ E)
      a2 = suc-nz-list (ccount W₁ E ç ∸ 1) nz
      a3 : NonZeroList ((ccount W₁ E ç) ∷ E)
      a3 = subst (λ x → NonZeroList (x ∷ E)) (sym (pred-eq (ccount-non-zero W₁ E nz ç))) a2
      b2 : NonZeroList (suc (pred (ccount W₁ E' ç')) ∷ E')
      b2 = suc-nz-list (ccount W₁ E' ç' ∸ 1) nz'
      b3 : NonZeroList ((ccount W₁ E' ç') ∷ E')
      b3 = subst (λ x → NonZeroList (x ∷ E')) (sym (pred-eq (ccount-non-zero W₁ E' nz' ç'))) b2
      c1 = comp-wkcw-lemma W₂ ((ccount W₁ E ç) ∷ E) ((ccount W₁ E' ç') ∷ E') a3 b3 (WkC.wkc-cong ç) (WkC.wkc-cong ç') a1
    in
    c1
  comp-wkcw-lemma (app M N) E E' nz nz' ç ç' ζ =
    let
      a0 = val-wkcw-lemma M E E' nz nz' ç ç' ζ
      a1 = val-wkcw-lemma N E E' nz nz' ç ç' ζ
    in
    *-≤-cong a0 a1
  comp-wkcw-lemma (var M) E E' nz nz' ç ç' ζ = val-wkcw-lemma M E E' nz nz' ç ç' ζ
  comp-wkcw-lemma (sub {A = A} W₁ W₂) E E' nz nz' ç ç' ζ =
    let
      a0 = comp-wkcw-lemma W₂ E E' nz nz' ç ç' ζ
      a1 = (wkcw-cong {Y = `V} a0 ζ)
      a2 : NonZeroList (suc (pred (ccount W₂ E ç)) ∷ E)
      a2 = suc-nz-list (ccount W₂ E ç ∸ 1) nz
      a3 : NonZeroList ((ccount W₂ E ç) ∷ E)
      a3 = subst (λ x → NonZeroList (x ∷ E)) (sym (pred-eq (ccount-non-zero W₂ E nz ç))) a2
      b2 : NonZeroList (suc (pred (ccount W₂ E' ç')) ∷ E')
      b2 = suc-nz-list (ccount W₂ E' ç' ∸ 1) nz'
      b3 : NonZeroList ((ccount W₂ E' ç') ∷ E')
      b3 = subst (λ x → NonZeroList (x ∷ E')) (sym (pred-eq (ccount-non-zero W₂ E' nz' ç'))) b2
      c1 = comp-wkcw-lemma W₁ ((ccount W₂ E ç) ∷ E) ((ccount W₂ E' ç') ∷ E') a3 b3 (WkC.wkc-cong ç) (WkC.wkc-cong ç') a1
    in
    c1

-------------------------------------------------------------------------------------------------

{- BBBB
  data Missing-i : {E : EMetric} → (i : Γ ∋ X) → (ϖ : WkN Γ E) → Set where
    missing-h : {E : EMetric} → (ϖ : WkN Γ E) → Missing-i {X = X} h (wkn-cons ϖ)
    missing-t-cong : {E : EMetric} → {e : EElem B}
                     → (i : Γ ∋ X) → (ϖ : WkN Γ E) → (μ : Missing-i i ϖ) → Missing-i (t {B = B} i) (wkn-cong {e = e} ϖ)
    missing-t-cons : {E : EMetric}
                     → (i : Γ ∋ X) → (ϖ : WkN Γ E) → (μ : Missing-i i ϖ) → Missing-i (t {B = B} i) (wkn-cons ϖ)

  with-i :  {E : EMetric} → (i : Γ ∋ X) → (ϖ : WkN Γ E) → (μ : Missing-i i ϖ) → (e : EElem X)
           → Σ[ E' ∈ EMetric ] (WkN Γ E')
  with-i i (wkn-cons ϖ) (missing-h ϖ) e = _ , wkn-cong {e = e} ϖ
  with-i (t i) (wkn-cong ϖ) (missing-t-cong {e = e'} i ϖ μ) e =
    let
      a1 = with-i i ϖ μ e
    in
    _ , wkn-cong {e = e'} (proj₂ a1)
  with-i (t i) (wkn-cons ϖ) (missing-t-cons i ϖ μ) e =
    let
      a1 = with-i i ϖ μ e
    in
      _ , wkn-cons (proj₂ a1)

  comp-mult-lemma : (W : Comp Γ Y) (e : EElem X) (E : EMetric) (ϖ : WkN Γ E) (csn : List (ℕ × ℕ))
              → (i : Γ ∋ X) → (μ : Missing-i i ϖ)
              →    ⟪ proj₁ (proj₂ (comp-mono-metric W (proj₁ (with-i i ϖ μ e)) (proj₂ (with-i i ϖ μ e)))) csn ⟫
                ≤ (⟪ proj₁ (proj₂ (comp-mono-metric W E ϖ)) csn ⟫ + ⟪ proj₁ (proj₂ e) csn ⟫ * suc (proj₁ (comp-mono-metric W E ϖ)))
  comp-mult-lemma (return M) e E ϖ csn i μ = {!!}
  comp-mult-lemma (pm M W) e E ϖ csn i μ = {!!}
  comp-mult-lemma (push {A = A} W₁ W₂) e E ϖ csn i μ =
    let
      eq :   proj₁ (proj₂ (comp-mono-metric (push W₁ W₂) (proj₁ (with-i i ϖ μ e)) (proj₂ (with-i i ϖ μ e)))) csn
           ≡ (incr (suc ((2+ (ccount W₂ (elist-to-clist (proj₁ (with-i i ϖ μ e))) (wkn-to-wkc (wkn-cons (proj₂ (with-i i ϖ μ e))))))
                   * (⟪ (proj₁ $ proj₂ (comp-mono-metric W₁ (proj₁ (with-i i ϖ μ e)) (proj₂ (with-i i ϖ μ e)))) (((ccount W₂ (elist-to-clist (proj₁ (with-i i ϖ μ e))) (wkn-to-wkc (wkn-cons (proj₂ (with-i i ϖ μ e))))) ,
                                                                     ⟪ (proj₁ $ proj₂ (comp-mono-metric W₂ (proj₁ (with-i i ϖ μ e)) (wkn-cons (proj₂ (with-i i ϖ μ e))))) csn ⟫) ∷ csn) ⟫)))
               ((proj₁ $ proj₂ (comp-mono-metric W₂ (proj₁ (with-i i ϖ μ e)) (wkn-cons (proj₂ (with-i i ϖ μ e))))) csn))
      eq = refl

      eq2 :  ⟪ proj₁ (proj₂ (comp-mono-metric (push W₁ W₂) (proj₁ (with-i i ϖ μ e)) (proj₂ (with-i i ϖ μ e)))) csn ⟫
           ≡ (suc ((2+ (ccount W₂ (elist-to-clist (proj₁ (with-i i ϖ μ e))) (wkn-to-wkc (wkn-cons (proj₂ (with-i i ϖ μ e))))))
                   * (⟪ (proj₁ $ proj₂ (comp-mono-metric W₁ (proj₁ (with-i i ϖ μ e)) (proj₂ (with-i i ϖ μ e))))
                                            (((ccount W₂ (elist-to-clist (proj₁ (with-i i ϖ μ e))) (wkn-to-wkc (wkn-cons (proj₂ (with-i i ϖ μ e))))) ,
                                             ⟪ (proj₁ $ proj₂ (comp-mono-metric W₂ (proj₁ (with-i i ϖ μ e)) (wkn-cons (proj₂ (with-i i ϖ μ e))))) csn ⟫) ∷ csn)
                      ⟫)))
              + ⟪ (proj₁ $ proj₂ (comp-mono-metric W₂ (proj₁ (with-i i ϖ μ e)) (wkn-cons (proj₂ (with-i i ϖ μ e))))) csn ⟫
      eq2 = refl

      eq3 : (proj₁ (comp-mono-metric (push W₁ W₂) E ϖ)) ≡ ccount (push W₁ W₂) (elist-to-clist E) (wkn-to-wkc ϖ)
      eq3 = refl

      eq4 : (proj₁ (comp-mono-metric (push W₁ W₂) E ϖ)) ≡ ccount W₂ ((ccount W₁ (elist-to-clist E) (wkn-to-wkc ϖ)) ∷ (elist-to-clist E)) (wkc-cong {Y = A} (wkn-to-wkc ϖ))
      eq4 = refl

      a0  :   ⟪ proj₁ (proj₂ (comp-mono-metric W₁ (proj₁ (with-i i ϖ μ e)) (proj₂ (with-i i ϖ μ e)))) csn ⟫
            ≤ ⟪ proj₁ (proj₂ (comp-mono-metric W₁ E ϖ)) csn ⟫ + ⟪ proj₁ (proj₂ e) csn ⟫ * suc (proj₁ (comp-mono-metric W₁ E ϖ))
      a0 = comp-mult-lemma W₁ e E ϖ csn i μ

      a1  :   ⟪ proj₁ (proj₂ (comp-mono-metric W₂ (with-i i ϖ μ e .proj₁) (wkn-cons (proj₂ (with-i i ϖ μ e))))) csn ⟫
            ≤ ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn ⟫ + ⟪ proj₁ (proj₂ e) csn ⟫ * suc (proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)))
      a1 = comp-mult-lemma W₂ e E (wkn-cons ϖ) csn (t i) (missing-t-cons i ϖ μ)

      a2  :   ⟪ proj₁ (proj₂ (comp-mono-metric W₂ (with-i i ϖ μ e .proj₁) (wkn-cons (proj₂ (with-i i ϖ μ e))))) csn ⟫
            ≤ ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn ⟫ + ⟪ proj₁ (proj₂ e) csn ⟫ * suc (ccount W₂ (elist-to-clist E) (wkn-to-wkc (wkn-cons ϖ)))
      a2 = comp-mult-lemma W₂ e E (wkn-cons ϖ) csn (t i) (missing-t-cons i ϖ μ)

      b1 : WkCW (wkc-cong {Y = A} {e = (ccount W₁ (elist-to-clist E) (wkn-to-wkc ϖ))} (wkn-to-wkc ϖ)) (wkc-cons (wkn-to-wkc ϖ))
      b1 = wkcw-skip {cnt = (ccount W₁ (elist-to-clist E) (wkn-to-wkc ϖ))} wkcw-id

      b2 : WkCW (wkc-cong {Y = A} {e = (ccount W₁ (elist-to-clist E) (wkn-to-wkc ϖ))} (wkn-to-wkc ϖ)) (wkn-to-wkc (wkn-cons ϖ))
      b2 = subst (λ x → WkCW (wkc-cong {Y = A} {e = (ccount W₁ (elist-to-clist E) (wkn-to-wkc ϖ))} (wkn-to-wkc ϖ)) x) (wkc-cons-comm ϖ) b1

      ntp : ccount W₂ (elist-to-clist E) (wkn-to-wkc (wkn-cons ϖ)) ≤ ccount W₂ ((ccount W₁ (elist-to-clist E) (wkn-to-wkc ϖ)) ∷ (elist-to-clist E)) (wkc-cong {Y = A} (wkn-to-wkc ϖ))
      ntp = {!!}

    in
    {!!}
  {-

  b1  = comp-mono-metric W₁ (proj₁ (with-i i ϖ μ e)) (proj₂ (with-i i ϖ μ e))

  Goal: ⟪ proj₁ (proj₂ (comp-mono-metric (push W₁ W₂) (proj₁ (with-i i ϖ μ e)) (proj₂ (with-i i ϖ μ e)))) csn ⟫
      ≤
        suc (⟪ proj₁ (proj₂ (comp-mono-metric W₁ E ϖ)) ((proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)) , ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn ⟫) ∷ csn) ⟫
       + (⟪ proj₁ (proj₂ (comp-mono-metric W₁ E ϖ)) ((proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)) , ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn ⟫) ∷ csn) ⟫
       + proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)) * ⟪ proj₁ (proj₂ (comp-mono-metric W₁ E ϖ)) ((proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)) , ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn ⟫) ∷ csn) ⟫)
       + ⟪ (proj₁ (proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn) ⟫
       + ⟪ proj₁ (proj₂ e) csn ⟫ * suc (proj₁ (comp-mono-metric (push W₁ W₂) E ϖ)))

   Rewritten Goal:
        (suc ((2+ (ccount W₂ (elist-to-clist (proj₁ (with-i i ϖ μ e))) (wkn-to-wkc (wkn-cons (proj₂ (with-i i ϖ μ e))))))
                   * (⟪ (proj₁ $ proj₂ (comp-mono-metric W₁ (proj₁ (with-i i ϖ μ e)) (proj₂ (with-i i ϖ μ e))))
                                            (((ccount W₂ (elist-to-clist (proj₁ (with-i i ϖ μ e))) (wkn-to-wkc (wkn-cons (proj₂ (with-i i ϖ μ e))))) ,
                                             ⟪ (proj₁ $ proj₂ (comp-mono-metric W₂ (proj₁ (with-i i ϖ μ e)) (wkn-cons (proj₂ (with-i i ϖ μ e))))) csn ⟫) ∷ csn)
                      ⟫)))
              + ⟪ (proj₁ $ proj₂ (comp-mono-metric W₂ (proj₁ (with-i i ϖ μ e)) (wkn-cons (proj₂ (with-i i ϖ μ e))))) csn ⟫

      ≤
        suc (⟪ proj₁ (proj₂ (comp-mono-metric W₁ E ϖ)) ((proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)) , ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn ⟫) ∷ csn) ⟫
       + (⟪ proj₁ (proj₂ (comp-mono-metric W₁ E ϖ)) ((proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)) , ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn ⟫) ∷ csn) ⟫
       + proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)) * ⟪proj₁ (proj₂ (comp-mono-metric W₁ E ϖ)) ((proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)) , ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn ⟫) ∷ csn) ⟫)
       + ⟪ (proj₁ (proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn) ⟫
       + ⟪ proj₁ (proj₂ e) csn ⟫ * suc (proj₁ (comp-mono-metric (push W₁ W₂) E ϖ)))

   STP:
        (2+ (ccount W₂ (elist-to-clist (proj₁ (with-i i ϖ μ e))) (wkn-to-wkc (wkn-cons (proj₂ (with-i i ϖ μ e))))))
                   * (⟪ (proj₁ $ proj₂ (comp-mono-metric W₁ (proj₁ (with-i i ϖ μ e)) (proj₂ (with-i i ϖ μ e))))
                                            (((ccount W₂ (elist-to-clist (proj₁ (with-i i ϖ μ e))) (wkn-to-wkc (wkn-cons (proj₂ (with-i i ϖ μ e))))) ,
                                             ⟪ (proj₁ $ proj₂ (comp-mono-metric W₂ (proj₁ (with-i i ϖ μ e)) (wkn-cons (proj₂ (with-i i ϖ μ e))))) csn ⟫) ∷ csn)
                      ⟫)
              + ⟪ (proj₁ $ proj₂ (comp-mono-metric W₂ (proj₁ (with-i i ϖ μ e)) (wkn-cons (proj₂ (with-i i ϖ μ e))))) csn ⟫

      ≤
        ⟪ proj₁ (proj₂ (comp-mono-metric W₁ E ϖ)) ((proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)) , ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn ⟫) ∷ csn) ⟫
       + ⟪ proj₁ (proj₂ (comp-mono-metric W₁ E ϖ)) ((proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)) , ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn ⟫) ∷ csn) ⟫
       + proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)) * ⟪proj₁ (proj₂ (comp-mono-metric W₁ E ϖ)) ((proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)) , ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn ⟫) ∷ csn) ⟫
       + ⟪ (proj₁ (proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn) ⟫
       + ⟪ proj₁ (proj₂ e) csn ⟫ * suc (proj₁ (comp-mono-metric (push W₁ W₂) E ϖ))



  -}
  comp-mult-lemma (app M N) e E ϖ csn i μ = {!!}
  comp-mult-lemma (var M) e E ϖ csn i μ = {!!}
  comp-mult-lemma (sub W₁ W₂) e E ϖ csn i μ = {!!}

BBBB -}


  {-
  comp-mult-lemma : (W : Comp (Γ ∙ X) Y) (e : EElem X) (E : EMetric) (ϖ : WkN Γ E) (csn : List (ℕ × ℕ))
              →    ⟪ proj₁ (proj₂ (comp-mono-metric W ((X , e) ∷ E) (wkn-cong ϖ))) csn ⟫
                ≤ (⟪ proj₁ (proj₂ (comp-mono-metric W E (wkn-cons ϖ))) csn ⟫ + ⟪ proj₁ (proj₂ e) csn ⟫ * suc (proj₁ (comp-mono-metric W E (wkn-cons ϖ))))
  comp-mult-lemma (return M) e E ϖ csn = {!!}
  comp-mult-lemma (pm M W) e E ϖ csn = {!!}
  comp-mult-lemma {X = X} (push W₁ W₂) e E ϖ csn =
    let
      eq1 :   proj₁ (proj₂ (comp-mono-metric (push W₁ W₂) ((X , e) ∷ E) (wkn-cong ϖ))) csn
            ≡ (incr (suc ((2+ (ccount W₂ (elist-to-clist ((X , e) ∷ E)) (wkn-to-wkc (wkn-cons (wkn-cong {e = e} ϖ)))))
                   * (⟪ (proj₁ $ proj₂ (comp-mono-metric W₁ ((X , e) ∷ E) (wkn-cong ϖ))) (((ccount W₂ (elist-to-clist ((X , e) ∷ E)) (wkn-to-wkc (wkn-cons (wkn-cong {e = e} ϖ)))) ,
                                                                     ⟪ (proj₁ $ proj₂ (comp-mono-metric W₂ ((X , e) ∷ E) (wkn-cons (wkn-cong ϖ)))) csn ⟫) ∷ csn) ⟫)))
              ((proj₁ $ proj₂ (comp-mono-metric W₂ ((X , e) ∷ E) (wkn-cons (wkn-cong ϖ)))) csn))
      eq1 = refl

      a0 = comp-mult-lemma W₁ e E ϖ csn
      --a0 = comp-mult-lemma W₂ e E (wkn-cons ϖ) csn
    in
    {!!}
  {-
  Goal: ⟪ proj₁ (proj₂ (comp-mono-metric (push W₁ W₂) ((X , e) ∷ E) (wkn-cong ϖ))) csn ⟫
      ≤
      suc (⟪ proj₁ (proj₂ (comp-mono-metric W₁ E (wkn-cons ϖ))) ((proj₁ (comp-mono-metric W₂ E (WkN.wkn-cons (wkn-cons ϖ))) ,
         ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (WkN.wkn-cons (wkn-cons ϖ)))) csn ⟫) ∷ csn) ⟫
       + (⟪ proj₁ (proj₂ (comp-mono-metric W₁ E (wkn-cons ϖ))) ((proj₁ (comp-mono-metric W₂ E (WkN.wkn-cons (wkn-cons ϖ))) ,
          ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (WkN.wkn-cons (wkn-cons ϖ)))) csn ⟫) ∷ csn) ⟫
        + proj₁ (comp-mono-metric W₂ E (WkN.wkn-cons (wkn-cons ϖ))) * ⟪ proj₁ (proj₂ (comp-mono-metric W₁ E (wkn-cons ϖ))) ((proj₁ (comp-mono-metric W₂ E (WkN.wkn-cons (wkn-cons ϖ))) ,
          ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (WkN.wkn-cons (wkn-cons ϖ)))) csn ⟫) ∷ csn)⟫)
       + ⟪ (proj₁ (proj₂ (comp-mono-metric W₂ E (WkN.wkn-cons (wkn-cons ϖ)))) csn) ⟫
       + ⟪ proj₁ (proj₂ e) csn ⟫ * suc (proj₁ (comp-mono-metric (push W₁ W₂) E (wkn-cons ϖ))))

   Rewritten Goal: 

      (suc ((2+ (ccount W₂ (elist-to-clist ((X , e) ∷ E)) (wkn-to-wkc (wkn-cons (wkn-cong {e = e} ϖ)))))
                   * (⟪ (proj₁ $ proj₂ (comp-mono-metric W₁ ((X , e) ∷ E) (wkn-cong ϖ))) (((ccount W₂ (elist-to-clist ((X , e) ∷ E)) (wkn-to-wkc (wkn-cons (wkn-cong {e = e} ϖ)))) ,
                                                                     ⟪ (proj₁ $ proj₂ (comp-mono-metric W₂ ((X , e) ∷ E) (wkn-cons (wkn-cong ϖ)))) csn ⟫) ∷ csn) ⟫)))
       ⟪ (proj₁ $ proj₂ (comp-mono-metric W₂ ((X , e) ∷ E) (wkn-cons (wkn-cong ϖ)))) csn)) ⟫

      ≤
      suc (⟪ proj₁ (proj₂ (comp-mono-metric W₁ E (wkn-cons ϖ))) ((proj₁ (comp-mono-metric W₂ E (WkN.wkn-cons (wkn-cons ϖ))) ,
         ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (WkN.wkn-cons (wkn-cons ϖ)))) csn ⟫) ∷ csn) ⟫
       + (⟪ proj₁ (proj₂ (comp-mono-metric W₁ E (wkn-cons ϖ))) ((proj₁ (comp-mono-metric W₂ E (WkN.wkn-cons (wkn-cons ϖ))) ,
          ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (WkN.wkn-cons (wkn-cons ϖ)))) csn ⟫) ∷ csn) ⟫
        + proj₁ (comp-mono-metric W₂ E (WkN.wkn-cons (wkn-cons ϖ))) * ⟪ proj₁ (proj₂ (comp-mono-metric W₁ E (wkn-cons ϖ))) ((proj₁ (comp-mono-metric W₂ E (WkN.wkn-cons (wkn-cons ϖ))) ,
          ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (WkN.wkn-cons (wkn-cons ϖ)))) csn ⟫) ∷ csn)⟫)
       + ⟪ (proj₁ (proj₂ (comp-mono-metric W₂ E (WkN.wkn-cons (wkn-cons ϖ)))) csn) ⟫
       + ⟪ proj₁ (proj₂ e) csn ⟫ * suc (proj₁ (comp-mono-metric (push W₁ W₂) E (wkn-cons ϖ))))

  ----------------
      (incr (suc ((2+ (ccount W₂ (elist-to-clist E) (wkn-to-wkc (wkn-cons ϖ))))
                   * (⟪ (proj₁ $ proj₂ (comp-mono-metric W₁ E ϖ)) (((ccount W₂ (elist-to-clist E) (wkn-to-wkc (wkn-cons ϖ))) ,
                                                                     ⟪ (proj₁ $ proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn ⟫) ∷ csn) ⟫)))
        ((proj₁ $ proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn))
  -}
  comp-mult-lemma (app M N) e E ϖ csn = {!!}
  comp-mult-lemma (var M) e E ϖ csn = {!!}
  comp-mult-lemma (sub W₁ W₂) e E ϖ csn = {!!}
  -}

  {-
  val-mult-lemma : (N : Val (Γ' ∙ X) Y) (e : EElem X) (E : EMetric) (E' : EMetric) (π : Wk Γ Γ') (ϖ : WkN Γ E) (ϖ' : WkN Γ' E') (csn : List (ℕ × ℕ))
              →    ⟪ proj₁ (proj₂ (val-mono-metric (wk-val (wk-cong π) N) ((X , e) ∷ E) (wkn-cong ϖ))) csn ⟫
                ≤ (⟪ proj₁ (proj₂ (val-mono-metric N E' (wkn-cons ϖ'))) csn ⟫ + ⟪ proj₁ (proj₂ e) csn ⟫ * suc (proj₁ (val-mono-metric N E' (wkn-cons ϖ'))))
  val-mult-lemma N e E E' π ϖ ϖ' csn = {!!}

  comp-mult-lemma : (W : Comp (Γ' ∙ X) Y) (e : EElem X) (E : EMetric) (E' : EMetric) (π : Wk Γ Γ') (ϖ : WkN Γ E) (ϖ' : WkN Γ' E') (csn : List (ℕ × ℕ))
              →    ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W) ((X , e) ∷ E) (wkn-cong ϖ))) csn ⟫
                ≤ (⟪ proj₁ (proj₂ (comp-mono-metric W E' (wkn-cons ϖ'))) csn ⟫ + ⟪ proj₁ (proj₂ e) csn ⟫ * suc (proj₁ (comp-mono-metric W E' (wkn-cons ϖ'))))

  comp-mult-lemma (return M) e E E' π ϖ ϖ' csn = {!E E' π ϖ ϖ'!}

  comp-mult-lemma (pm M W) e E E' π ϖ ϖ' csn = {!!}
  comp-mult-lemma (push W₁ W₂) e E E' π ϖ ϖ' csn =
    let
      a1 = comp-mult-lemma W₁ e E E' π ϖ ϖ' csn
      a2 = comp-mult-lemma W₂ {!!} E E' {!!} {!!} {!!} csn
    in
    {!!}
  {-

    Goal: ⟪ proj₁ (proj₂ (comp-mono-metric (push (wk-comp (wk-cong π) W₁) (wk-comp (wk-cong (wk-cong π)) W₂)) ((X , e) ∷ E) (wkn-cong ϖ))) csn ⟫
          ≤
          suc (⟪ proj₁ (proj₂ (comp-mono-metric W₁ E' (wkn-cons ϖ'))) ((proj₁ (comp-mono-metric W₂ E' (WkN.wkn-cons (wkn-cons ϖ'))) , ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' (WkN.wkn-cons (wkn-cons ϖ')))) csn ⟫) ∷ csn) ⟫
          + (⟪ proj₁ (proj₂ (comp-mono-metric W₁ E' (wkn-cons ϖ'))) ((proj₁ (comp-mono-metric W₂ E' (WkN.wkn-cons (wkn-cons ϖ'))) , ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' (WkN.wkn-cons (wkn-cons ϖ')))) csn ⟫) ∷ csn) ⟫
          + proj₁ (comp-mono-metric W₂ E' (WkN.wkn-cons (wkn-cons ϖ'))) * ⟪ proj₁ (proj₂ (comp-mono-metric W₁ E' (wkn-cons ϖ'))) ((proj₁ (comp-mono-metric W₂ E' (WkN.wkn-cons (wkn-cons ϖ'))) , ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' (WkN.wkn-cons (wkn-cons ϖ')))) csn ⟫) ∷ csn) ⟫)
          + ⟪ (proj₁ (proj₂ (comp-mono-metric W₂ E' (WkN.wkn-cons (wkn-cons ϖ')))) csn) ⟫
          + ⟪ proj₁ (proj₂ e) csn ⟫ * suc (proj₁ (comp-mono-metric (push W₁ W₂) E' (wkn-cons ϖ'))))

  -}
  comp-mult-lemma (app M N) e E E' π ϖ ϖ' csn = {!!}
  comp-mult-lemma (var M) e E E' π ϖ ϖ' csn = {!!}
  comp-mult-lemma (sub W₁ W₂) e E E' π ϖ ϖ' csn = {!!}
  -}

-------------------------------------------------------------------------------------------------
--  val-metric-decreasing : {Q₁ : ValState X} → {Q₂ : ValState X} → (Q₁→ᶜQ₂ : Q₁ ↠ᵛ Q₂) → (csn : List (ℕ × ℕ)) → suc ⟪ valstate-metric Q₂ csn ⟫ ≤ ⟪ valstate-metric Q₁ csn ⟫
--  val-metric-decreasing = {!!}

{- AAAAAAAA

  comp-metric-decreasing : {Q₁ : CompState} → {Q₂ : CompState} → (Q₁→ᶜQ₂ : Q₁ →ᶜ Q₂) → (suc (compstate-metric Q₂) ≤ (compstate-metric Q₁))
  comp-metric-decreasing (∘return {M = M} {γ = γ} {π = π} {M' = M'} {γ' = γ'} {cs = cs} {VS>VT = VS>VT} M→M') =
    let
      a1 = ≤-trans (s≤s (≤ᴹ⇒≤ (VS>VT (cs-to-csn cs)))) (+-≤-cong (s≤s (z≤n {n = 1})) (≤-refl {n = ⟪ proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) (cs-to-csn cs) ⟫}))
      a2 = csn-decr a1 (cs-to-csn cs)
      a3 = ≤ᴹ⇒≤ (VS>VT (cs-to-csn cs))
    in
    s≤s (s≤s (+-≤-cong a3 a2))

    {-
    Goal: 2+ (⟪proj₁ (proj₂ (v̲a̲l̲-mono-metric M' (proj₁ (env-mono-metric γ')) (proj₂ (env-mono-metric γ')))) (cs-to-csn cs)⟫
            + csn-to-nat₀ (suc ⟪proj₁ (proj₂ (v̲a̲l̲-mono-metric M' (proj₁ (env-mono-metric γ')) (proj₂ (env-mono-metric γ')))) (cs-to-csn cs)⟫) (cs-to-csn cs))
      ≤
          2+ (⟪proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) (cs-to-csn cs)⟫
            + csn-to-nat₀ (2+ ⟪proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) (cs-to-csn cs)⟫) (cs-to-csn cs))
    -}

    -- OLDX:
    -- let
    --   a1 = ≤-trans (s≤s (≤ᴹ⇒≤ (VS>VT (cs-to-csn cs)))) (+-≤-cong (s≤s (z≤n {n = 1})) (≤-refl {n = ⟪ proj₁ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) (cs-to-csn cs) ⟫}))
    --   a2 = csn-decr a1 (cs-to-csn cs)
    --   a3 = ≤ᴹ⇒≤ (VS>VT (cs-to-csn cs))
    -- in
    -- s≤s (s≤s (+-≤-cong a3 a2))

  comp-metric-decreasing (∙return {Γ = Γ} {X = X} {Γ' = Γ'} {Y = Y} {M = M} {γ = γ} {N = N} {γ' = γ'} {π = π} {cs = cs}) =
    --OLD:
    --let
    --  EW  = (env-metric γ)
    --  EW' = (env-metric γ')
    --  E = proj₁ EW
    --  E' = proj₁ EW'
    --  ϖ = proj₂ EW
    --  ϖ' = proj₂ EW'
    --  csn = cs-to-csn cs
    --  ----------------------------------------------------------------
    --  a0 = ⟪ comp-metric N E' (Wkn.wkn-cons ϖ') csn ⟫
    --  a1 = ⟪ comp-metric (wk-comp (wk-cong π) N) ((X , v̲a̲l̲-metric M E ϖ) ∷ E) (Wkn.wkn-cong ϖ) csn ⟫
    --  b1 = ⟪ v̲a̲l̲-metric M E ϖ ((count-in-comp h N E' (Wkn.wkn-cons ϖ') csn , a0) ∷ csn) ⟫
    --  ----------------------------------------------------------------
    --  postulate l1 : a1 ≤ a0
    --  ----------------------------------------------------------------
    --  l2 : a1 ≤ a0 + suc (count-in-comp h N E' (Wkn.wkn-cons ϖ') csn + b1 * suc (count-in-comp h N E' (Wkn.wkn-cons ϖ') csn))
    --  l2 = ≤-trans l1 (n≤n+m {n = a0} {m = (suc (count-in-comp h N E' (Wkn.wkn-cons ϖ') csn + b1 * suc (count-in-comp h N E' (Wkn.wkn-cons ϖ') csn)))})
    --  l3 : csn-to-nat₀ a1 csn ≤ csn-to-nat₀ (a0 + suc (count-in-comp h N E' (Wkn.wkn-cons ϖ') csn + b1 * suc (count-in-comp h N E' (Wkn.wkn-cons ϖ') csn))) csn
    --  l3 = csn-decr l2 csn
    --  l4 :        a1 + (csn-to-nat₀ a1 csn)
    --       ≤      b1 + ((a0 + suc (count-in-comp h N E' (Wkn.wkn-cons ϖ') csn + b1 * suc (count-in-comp h N E' (Wkn.wkn-cons ϖ') csn)))
    --           + (csn-to-nat₀ (a0 + suc (count-in-comp h N E' (Wkn.wkn-cons ϖ') csn + b1 * suc (count-in-comp h N E' (Wkn.wkn-cons ϖ') csn))) csn))
    --  l4 = +-≤-cong (z≤n {n = b1}) (+-≤-cong l2 l3)
    --in
    --  s≤s l4
    let
      EW  = env-mono-metric γ
      EW' = env-mono-metric γ'
      E = proj₁ EW
      E' = proj₁ EW'
      ϖ = proj₂ EW
      ϖ' = proj₂ EW'
      csn = cs-to-csn cs
      x : (VMain.comp-mono-metric (λ z → k₀ z) N E' (WkN.wkn-cons ϖ')) ≡ comp-mono-metric N E' (WkN.wkn-cons ϖ')
      x = refl
      lem1 = comp-wke-lemma N ((X , v̲a̲l̲-mono-metric M E ϖ) ∷ E) E' (wk-cong π) (WkN.wkn-cong ϖ) (WkN.wkn-cons ϖ') {!-m!}
      b1 = v̲a̲l̲-mono-metric M E ϖ
      {-
    comp-wke-lemma : (W : Comp Γ' X) → (E E' : EMetric)
                → (π : Wk Γ Γ') → (ϖ : WkN Γ E) → (ϖ' : WkN Γ' E') → (θ : WkE π ϖ ϖ')
                → (comp-mono-metric W E' ϖ') ≡ (comp-mono-metric (wk-comp π W) E ϖ)
      -}
    in
    {!!}
{-

a0 = comp-mono-metric N E' (WkN.wkn-cons ϖ')
a1 = comp-mono-metric (wk-comp (wk-cong π) N) ((X , v̲a̲l̲-mono-metric M E ϖ) ∷ E) (WkN.wkn-cong ϖ)
b1 = v̲a̲l̲-mono-metric M E ϖ

Goal:          suc (⟪ proj₁ (proj₂ (a1)) csn ⟫
      + csn-to-nat₀ ⟪ proj₁ (proj₂ (a1)) csn ⟫ csn)
    ≤           suc (⟪ proj₁ (proj₂ (b1)) ((proj₁ (a0) , ⟪ proj₁ (proj₂ (a0)) csn ⟫) ∷ csn) ⟫ + (⟪ proj₁ (proj₂ (a0)) csn ⟫ + suc (proj₁ (a0) + ⟪ proj₁ (proj₂ (b1)) ((proj₁ (a0) , ⟪ proj₁ (proj₂ (a0)) csn ⟫) ∷ csn) ⟫ * suc (proj₁ (a0)))
      + csn-to-nat₀ (⟪ proj₁ (proj₂ (a0)) csn ⟫ + suc (proj₁ (a0) + ⟪ proj₁ (proj₂ (b1)) ((proj₁ (a0) , ⟪ proj₁ (proj₂ (a0)) csn ⟫) ∷ csn) ⟫ * suc (proj₁ (a0)))) csn))

rewriting goal:
                   (⟪ proj₁ (proj₂ (a1)) csn ⟫
      + csn-to-nat₀ ⟪ proj₁ (proj₂ (a1)) csn ⟫ csn)
    ≤              (⟪ proj₁ (proj₂ (b1)) ((proj₁ (a0) , ⟪ proj₁ (proj₂ (a0)) csn ⟫) ∷ csn) ⟫ +
                                (⟪ proj₁ (proj₂ (a0)) csn ⟫ + suc (proj₁ (a0) + ⟪ proj₁ (proj₂ (b1)) ((proj₁ (a0) , ⟪ proj₁ (proj₂ (a0)) csn ⟫) ∷ csn) ⟫ * suc (proj₁ (a0)))
                  + csn-to-nat₀ (⟪ proj₁ (proj₂ (a0)) csn ⟫ + suc (proj₁ (a0) + ⟪ proj₁ (proj₂ (b1)) ((proj₁ (a0) , ⟪ proj₁ (proj₂ (a0)) csn ⟫) ∷ csn) ⟫ * suc (proj₁ (a0)))) csn))

STP:
           ⟪ proj₁ (proj₂ (a1)) csn ⟫
         ≤ (⟪ proj₁ (proj₂ (a0)) csn ⟫ + ⟪ proj₁ (proj₂ (b1)) ((proj₁ (a0) , ⟪ proj₁ (proj₂ (a0)) csn ⟫) ∷ csn) ⟫ * suc (proj₁ (a0)))

STP:

a0 = comp-mono-metric N E' (WkN.wkn-cons ϖ')
a1 = comp-mono-metric (wk-comp (wk-cong π) N) ((X , v̲a̲l̲-mono-metric M E ϖ) ∷ E) (WkN.wkn-cong ϖ)
b1 = v̲a̲l̲-mono-metric M E ϖ

           ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) N) ((X , b1) ∷ E) (WkN.wkn-cong ϖ))) csn ⟫
         ≤ (⟪ proj₁ (proj₂ (comp-mono-metric N E' (WkN.wkn-cons ϖ'))) csn ⟫ + ⟪ proj₁ (proj₂ b1) csn ⟫ * suc (proj₁ (comp-mono-metric N E' (WkN.wkn-cons ϖ'))))


OLDX:

a0 = comp-mono-metric N E' (WkN.wkn-cons ϖ')
a1 = comp-mono-metric (wk-comp (wk-cong π) N) ((X , v̲a̲l̲-mono-metric M E ϖ) ∷ E) (WkN.wkn-cong ϖ)
b1 = v̲a̲l̲-mono-metric M E ϖ
c1 = mono-comp-count h N E' (WkN.wkn-cons ϖ')

Goal:      suc (⟪ proj₁ (a1) csn ⟫ + csn-to-nat₀ ⟪ proj₁ (a1) csn ⟫ csn)
      ≤    suc (⟪ proj₁ (b1) ((proj₁ (c1) csn , ⟪ proj₁ (a0) csn ⟫) ∷ csn) ⟫ + (⟪ proj₁ (a0) csn ⟫ + suc (proj₁ (c1) csn + ⟪ proj₁ (b1) ((proj₁ (c1) csn , ⟪ proj₁ (a0) csn ⟫) ∷ csn) ⟫ * suc (proj₁ (c1) csn)) + csn-to-nat₀ (⟪ proj₁ (a0) csn ⟫ + suc (proj₁ (c1) csn + ⟪ proj₁ (b1) ((proj₁ (c1) csn , ⟪ proj₁ (a0) csn ⟫) ∷ csn) ⟫ * suc (proj₁ (c1) csn))) csn))

Rewritten
Goal:      suc (         ⟪ proj₁ (a1) csn ⟫
           + csn-to-nat₀ ⟪ proj₁ (a1) csn ⟫ csn)
      ≤    suc (⟪ proj₁ (b1) ((proj₁ (c1) csn , ⟪ proj₁ (a0) csn ⟫) ∷ csn) ⟫)
           +             (⟪ proj₁ (a0) csn ⟫ + suc (proj₁ (c1) csn + ⟪ proj₁ (b1) ((proj₁ (c1) csn , ⟪ proj₁ (a0) csn ⟫) ∷ csn) ⟫ * suc (proj₁ (c1) csn)))
           + csn-to-nat₀ (⟪ proj₁ (a0) csn ⟫ + suc (proj₁ (c1) csn + ⟪ proj₁ (b1) ((proj₁ (c1) csn , ⟪ proj₁ (a0) csn ⟫) ∷ csn) ⟫ * suc (proj₁ (c1) csn))) csn

EASY: follows from a1 ≤ a0

-}

  comp-metric-decreasing (∘push {X = X} {M = M} {N = N} {γ = γ} {cs = cs} {πₓ = πₓ} {wk≡ₓ = wk≡ₓ} {wk≡ = wk≡}) =
    --OLD:
    --let
    --  EW  = (env-metric γ)
    --  E = proj₁ EW
    --  ϖ = proj₂ EW
    --  csn = cs-to-csn cs
    --  ----------------------------------------------------------------
    --  a1 = comp-metric N E (Wkn.wkn-cons ϖ) csn
    --  a2 = comp-metric M E ϖ ((count-in-comp h N E (wkn-cons ϖ) csn , ⟪ a1 ⟫) ∷ csn)
    --  ----------------------------------------------------------------
    --  l1  : ⟪ a2 ⟫ * suc (count-in-comp h N E (wkn-cons ϖ) csn) ≤ ⟪ a2 ⟫ + count-in-comp h N E (wkn-cons ϖ) csn * ⟪ a2 ⟫
    --  l1  = subst (λ x → _≤_ x (⟪ a2 ⟫ + count-in-comp h N E (wkn-cons ϖ) csn * ⟪ a2 ⟫)) (sym (n*sm≡n+m*n ⟪ a2 ⟫ (count-in-comp h N E (wkn-cons ϖ) csn))) ≤-refl
    --  l1a :   ⟪ a1 ⟫ + ⟪ a2 ⟫ * suc (count-in-comp h N E (wkn-cons ϖ) csn)
    --       ≤ (⟪ a2 ⟫ + count-in-comp h N E (wkn-cons ϖ) csn * ⟪ a2 ⟫) + ⟪ a1 ⟫
    --  l1a = subst
    --           (_≤_ (⟪ a1 ⟫ + ⟪ a2 ⟫ * suc (count-in-comp h N E (wkn-cons ϖ) csn)))
    --           (+-comm {n = ⟪ a1 ⟫} {m = (⟪ a2 ⟫ + count-in-comp h N E (wkn-cons ϖ) csn * ⟪ a2 ⟫)})
    --           (+-≤-cong (≤-refl {n = ⟪ a1 ⟫}) l1)
    --  l2  :  (⟪ a1 ⟫ + ⟪ a2 ⟫ * suc (count-in-comp h N E (wkn-cons ϖ) csn))
    --       ≤ ⟪ a2 ⟫ + (⟪ a2 ⟫ + count-in-comp h N E (wkn-cons ϖ) csn * ⟪ a2 ⟫) + ⟪ a1 ⟫
    --  l2  = subst
    --           (_≤_ (⟪ a1 ⟫ + ⟪ a2 ⟫ * suc (count-in-comp h N E (wkn-cons ϖ) csn)))
    --           (sym $ +-assoc {n₁ = ⟪ a2 ⟫} {n₂ = (⟪ a2 ⟫ + count-in-comp h N E (wkn-cons ϖ) csn * ⟪ a2 ⟫)} {n₃ = ⟪ a1 ⟫})
    --           (+-≤-cong (z≤n {n = ⟪ a2 ⟫}) l1a)
    --  l3  :        ⟪ a1 ⟫ +  ⟪ a2 ⟫ * suc (count-in-comp h N E (wkn-cons ϖ) csn)
    --        ≤ suc (⟪ a2 ⟫ + (⟪ a2 ⟫ + count-in-comp h N E (wkn-cons ϖ) csn * ⟪ a2 ⟫) + ⟪ a1 ⟫)
    --  l3  = +-≤-cong (z≤n {n = 1}) l2
    --  l4  :   csn-to-nat₀ (⟪ a1 ⟫ + ⟪ a2 ⟫ * suc (count-in-comp h N E (wkn-cons ϖ) csn)) csn
    --        ≤ csn-to-nat₀ (suc (⟪ a2 ⟫ + (⟪ a2 ⟫ + count-in-comp h N E (wkn-cons ϖ) csn * ⟪ a2 ⟫) + ⟪ a1 ⟫)) csn
    --  l4  = csn-decr l3 csn
    --  l5  :   (⟪ a1 ⟫ + ⟪ a2 ⟫ * suc (count-in-comp h N E (wkn-cons ϖ) csn)      + csn-to-nat₀ (⟪ a1 ⟫ + ⟪ a2 ⟫ * suc (count-in-comp h N E (wkn-cons ϖ) csn)) csn)
    --        ≤ ((⟪ a2 ⟫ + count-in-comp h N E (wkn-cons ϖ) csn * ⟪ a2 ⟫) + ⟪ a1 ⟫ + csn-to-nat₀ (suc (⟪ a2 ⟫ + (⟪ a2 ⟫ + count-in-comp h N E (wkn-cons ϖ) csn * ⟪ a2 ⟫) + ⟪ a1 ⟫)) csn)
    --  l5  = +-≤-cong l1a l4
    --  l6  :   ⟪ a2 ⟫ + ((⟪ a1 ⟫ + ⟪ a2 ⟫ * suc (count-in-comp h N E (wkn-cons ϖ) csn)  + csn-to-nat₀ (⟪ a1 ⟫ + ⟪ a2 ⟫ * suc (count-in-comp h N E (wkn-cons ϖ) csn)) csn))
    --        ≤ ⟪ a2 ⟫ + (⟪ a2 ⟫ + count-in-comp h N E (wkn-cons ϖ) csn * ⟪ a2 ⟫) + ⟪ a1 ⟫       + csn-to-nat₀ (suc (⟪ a2 ⟫ + (⟪ a2 ⟫ + count-in-comp h N E (wkn-cons ϖ) csn * ⟪ a2 ⟫) + ⟪ a1 ⟫)) csn
    --  l6 = subst
    --            (_≤_ (⟪ a2 ⟫ + ((⟪ a1 ⟫ + ⟪ a2 ⟫ * suc (count-in-comp h N E (wkn-cons ϖ) csn)  + csn-to-nat₀ (⟪ a1 ⟫ + ⟪ a2 ⟫ * suc (count-in-comp h N E (wkn-cons ϖ) csn)) csn))))
    --            (sym $ +-assoc {n₁ = ⟪ a2 ⟫ + (⟪ a2 ⟫ + count-in-comp h N E (wkn-cons ϖ) csn * ⟪ a2 ⟫)} {n₂ = ⟪ a1 ⟫} {n₃ = csn-to-nat₀ (suc (⟪ a2 ⟫ + (⟪ a2 ⟫ + count-in-comp h N E (wkn-cons ϖ) csn * ⟪ a2 ⟫) + ⟪ a1 ⟫)) csn})
    --            ( (subst
    --                  (_≤_ (⟪ a2 ⟫ + ((⟪ a1 ⟫ + ⟪ a2 ⟫ * suc (count-in-comp h N E (wkn-cons ϖ) csn)  + csn-to-nat₀ (⟪ a1 ⟫ + ⟪ a2 ⟫ * suc (count-in-comp h N E (wkn-cons ϖ) csn)) csn))))
    --                  (sym $ +-assoc {n₁ = ⟪ a2 ⟫} {n₂ = (⟪ a2 ⟫ + count-in-comp h N E (wkn-cons ϖ) csn * ⟪ a2 ⟫)} {n₃ = ⟪ a1 ⟫ + csn-to-nat₀ (suc (⟪ a2 ⟫ + (⟪ a2 ⟫ + count-in-comp h N E (wkn-cons ϖ) csn * ⟪ a2 ⟫) + ⟪ a1 ⟫)) csn})
    --                   (+-≤-cong (≤-refl {n = ⟪ a2 ⟫})
    --                     (subst
    --                          (_≤_ (⟪ a1 ⟫ + ⟪ a2 ⟫ * suc (count-in-comp h N E (wkn-cons ϖ) csn) + csn-to-nat₀ (⟪ a1 ⟫ + ⟪ a2 ⟫ * suc (count-in-comp h N E (wkn-cons ϖ) csn)) csn))
    --                          (+-assoc {n₁ = ⟪ a2 ⟫ + count-in-comp h N E (wkn-cons ϖ) csn * ⟪ a2 ⟫} {n₂ = ⟪ a1 ⟫} {n₃ = csn-to-nat₀ (suc (⟪ a2 ⟫ + (⟪ a2 ⟫ + count-in-comp h N E (wkn-cons ϖ) csn * ⟪ a2 ⟫) + ⟪ a1 ⟫)) csn})
    --                          l5 ))))
    --in
    --  s≤s l6
    let
      EW  = (env-mono-metric γ)
      E = proj₁ EW
      ϖ = proj₂ EW
      csn = cs-to-csn cs
    in
    {!!}

{-

a1 = comp-mono-metric N E (WkN.wkn-cons ϖ)
a2 = comp-mono-metric M E ϖ
c1 = mono-comp-count h N E (WkN.wkn-cons ϖ)

Goal:
      suc (⟪ proj₁ (proj₂ (a2)) ((proj₁ (a1) , ⟪ proj₁ (proj₂ (a1)) csn ⟫) ∷ csn) ⟫
                  + (⟪ proj₁ (proj₂ (a1)) csn ⟫ + ⟪ proj₁ (proj₂ (a2)) ((proj₁ (a1) , ⟪ proj₁ (proj₂ (a1)) csn ⟫) ∷ csn) ⟫ * suc (proj₁ (a1))
      + csn-to-nat₀ (⟪ proj₁ (proj₂ (a1)) csn ⟫ + ⟪ proj₁ (proj₂ (a2)) ((proj₁ (a2) , ⟪ proj₁ (proj₂ (a1)) csn ⟫) ∷ csn) ⟫ * suc (proj₁ (a1))) csn))
    ≤                suc (⟪ proj₁ (proj₂ (a2)) ((proj₁ (a1) , ⟪ proj₁ (proj₂ (a1)) csn ⟫) ∷ csn) ⟫ + (⟪ proj₁ (proj₂ (a2)) ((proj₁ (a1) , ⟪ proj₁ (proj₂ (a1)) csn ⟫) ∷ csn) ⟫ + proj₁ (a1) * ⟪ proj₁ (proj₂ (a2)) ((proj₁ (a1) , ⟪ proj₁ (proj₂ (a1)) csn ⟫) ∷ csn) ⟫) + ⟪ (proj₁ (proj₂ (a1)) csn) ⟫
      + csn-to-nat₀ (suc (⟪ proj₁ (proj₂ (a2)) ((proj₁ (a1) , ⟪ proj₁ (proj₂ (a1)) csn ⟫) ∷ csn) ⟫ + (⟪ proj₁ (proj₂ (a2)) ((proj₁ (a1) , ⟪ proj₁ (proj₂ (a1)) csn ⟫) ∷ csn) ⟫ + proj₁ (a1) * ⟪ proj₁ (proj₂ (a2)) ((proj₁ (a1) , ⟪ proj₁ (proj₂ (a1)) csn ⟫) ∷ csn) ⟫) + ⟪ (proj₁ (proj₂ (a1)) csn) ⟫)) csn)

STP:
      suc (⟪ proj₁ (proj₂ (a2)) ((proj₁ (a1) , ⟪ proj₁ (proj₂ (a1)) csn ⟫) ∷ csn) ⟫ + (⟪ proj₁ (proj₂ (a1)) csn ⟫                     + ⟪ proj₁ (proj₂ (a2)) ((proj₁ (a1) , ⟪ proj₁ (proj₂ (a1)) csn ⟫) ∷ csn) ⟫ * suc (proj₁ (a1))
    ≤ suc (⟪ proj₁ (proj₂ (a2)) ((proj₁ (a1) , ⟪ proj₁ (proj₂ (a1)) csn ⟫) ∷ csn) ⟫                                + (suc (proj₁ a1)) * ⟪ proj₁ (proj₂ (a2)) ((proj₁ (a1) , ⟪ proj₁ (proj₂ (a1)) csn ⟫) ∷ csn) ⟫)                      + ⟪ (proj₁ (proj₂ (a1)) csn) ⟫

EASY: refl

OLDX:

a1 = comp-mono-metric N E (WkN.wkn-cons ϖ)
a2 = comp-mono-metric M E ϖ
c1 = mono-comp-count h N E (WkN.wkn-cons ϖ)

Goal: suc (⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫ + (⟪ proj₁ (a1) csn ⟫ + ⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫ * suc (proj₁ (c1) csn) + csn-to-nat₀ (⟪ proj₁ (a1) csn ⟫ + ⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫ * suc (proj₁ (c1) csn)) csn))
≤ suc (⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫ + (⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫ + proj₁ (c1) csn * ⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫) + VMain.⟪ (λ z → k₀ z) ⟫ (proj₁ (a1) csn) + csn-to-nat₀ (suc (⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫ + (⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫ + proj₁ (c1) csn * ⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫) + VMain.⟪ (λ z → k₀ z) ⟫ (proj₁ (a1) csn))) csn )

Rewritten
Goal: suc (                               ⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫
                  + (⟪ proj₁ (a1) csn ⟫ + ⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫ * suc (proj₁ (c1) csn)
      + csn-to-nat₀ (⟪ proj₁ (a1) csn ⟫ + ⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫ * suc (proj₁ (c1) csn)) csn))
≤                    suc (⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫ + (⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫ + proj₁ (c1) csn * ⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫) + VMain.⟪ (λ z → k₀ z) ⟫ (proj₁ (a1) csn)
      + csn-to-nat₀ (suc (⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫ + (⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫ + proj₁ (c1) csn * ⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫) + VMain.⟪ (λ z → k₀ z) ⟫ (proj₁ (a1) csn))) csn )
=                    suc (⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫ + ((suc (proj₁ (c1) csn)) * ⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫) + ⟪ proj₁ (a1) csn ⟫
      + csn-to-nat₀ (suc (⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫ + ((suc (proj₁ (c1) csn)) * ⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫) + ⟪ proj₁ (a1) csn ⟫)) csn )

STP:
   ⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫
                  + (⟪ proj₁ (a1) csn ⟫                         +  suc (proj₁ (c1) csn) * ⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫
≤? ⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫ + (suc (proj₁ (c1) csn) * ⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫) + ⟪ proj₁ (a1) csn ⟫

STP:
   ⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫ + ⟪ proj₁ (a1) csn ⟫
≤? ⟪ proj₁ (a2) ((proj₁ (c1) csn , ⟪ proj₁ (a1) csn ⟫) ∷ csn) ⟫ + ⟪ proj₁ (a1) csn ⟫

EASY: refl

-}

  comp-metric-decreasing (∘sub {M = M} {N = N} {γ = γ} {cs = cs} {πₓ = πₓ} {wk≡ₓ = wk≡ₓ}) =
    -- OLD:
    -- let
    --   EW  = (env-metric γ)
    --   E = proj₁ EW
    --   ϖ = proj₂ EW
    --   csn = cs-to-csn cs
    --   ----------------------------------------------------------------
    --   a1 = comp-metric N E ϖ csn
    --   a2 = comp-metric M ((`V , (λ _ → TermMetric.m-V 0 (⟪ a1 ⟫ + csn-to-nat₀ ⟪ a1 ⟫ csn))) ∷ E) (Wkn.wkn-cong ϖ) csn
    --   ----------------------------------------------------------------
    --   l1 : ⟪ a2 ⟫ ≤ suc (⟪ a1 ⟫ + ⟪ a2 ⟫)
    --   l1 = ≤-trans (+-≤-cong (z≤n {n = ⟪ a1 ⟫}) (≤-refl {n = ⟪ a2 ⟫})) (n≤sn {n = ⟪ a1 ⟫ + ⟪ a2 ⟫})
    --   l2 : csn-to-nat₀ ⟪ a2 ⟫ csn ≤ csn-to-nat₀ (suc (⟪ a1 ⟫ + ⟪ a2 ⟫)) csn
    --   l2 = csn-decr l1 csn
    -- in
    --   s≤s (+-≤-cong (+-≤-cong (z≤n {n = ⟪ a1 ⟫}) (≤-refl {n = ⟪ a2 ⟫})) l2)
    let
      EW = env-mono-metric γ
      E = proj₁ EW
      ϖ = proj₂ EW
      csn = cs-to-csn cs
    in
    {!!}

{-

a1 = comp-mono-metric N E ϖ
a2 = comp-mono-metric M ((`V , proj₁ (a1) , (λ _ → TermMetric.m-V 0 (⟪ proj₁ (proj₂ (a1)) csn ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (a1)) csn ⟫ csn)) , (λ _ → _≤ᴹ_.≤-V z≤n ≤-refl)) ∷ E) (WkN.wkn-cong ϖ)

Goal:           suc (⟪ proj₁ (proj₂ (a2)) csn ⟫
       + csn-to-nat₀ ⟪ proj₁ (proj₂ (a2)) csn ⟫ csn)
      ≤
                      suc (⟪ proj₁ (proj₂ (a1)) csn ⟫ + ⟪ (proj₁ (proj₂ (a2)) csn) ⟫
       + csn-to-nat₀ (suc (⟪ proj₁ (proj₂ (a1)) csn ⟫ + ⟪ (proj₁ (proj₂ (a2)) csn) ⟫)) csn)

EASY

OLDX:

a1 = comp-mono-metric N E ϖ
a2 = comp-mono-metric M ((`V , (λ _ → TermMetric.m-V 0 (⟪ proj₁ (a1) csn ⟫ + csn-to-nat₀ ⟪ proj₁ (a1) csn ⟫ csn)) , (λ _ → _≤ᴹ_.≤-V z≤n ≤-refl)) ∷ E) (WkN.wkn-cong ϖ)

Goal: suc (         ⟪ proj₁ (a2) csn ⟫
      + csn-to-nat₀ ⟪ proj₁ (a2) csn ⟫ csn)
      ≤
                     suc (⟪ proj₁ (a1) csn ⟫ + ⟪ proj₁ (a2) csn ⟫
      + csn-to-nat₀ (suc (⟪ proj₁ (a1) csn ⟫ + ⟪ proj₁ (a2) csn ⟫)) csn)

EASY: follows from
         suc (⟪ proj₁ (a2) csn ⟫) ≤ suc (⟪ proj₁ (a1) csn ⟫ + ⟪ proj₁ (a2) csn ⟫)

-}

  comp-metric-decreasing (∘pm {X = X} {Y = Y} {M = M} {γ = γ} {W = W} {cs = cs} {πₓ = πₓ} {πₓ' = πₓ'} {γ'' = γ''} {wk≡ₓ = wk≡ₓ} {wk≡ₓ' = wk≡ₓ'} {LHS = LHS } {RHS = RHS} π M→M' π') =
    -- OLD:
    -- let
    --   EW  = (env-metric γ)
    --   E = proj₁ EW
    --   ϖ = proj₂ EW
    --   EW''  = (env-metric γ'')
    --   E'' = proj₁ EW''
    --   ϖ'' = proj₂ EW''
    --   csn = cs-to-csn cs
    -- in
    let
      EW = env-mono-metric γ
      E = proj₁ EW
      ϖ = proj₂ EW
      EW'' = env-mono-metric γ''
      E'' = proj₁ EW''
      ϖ'' = proj₂ EW''
      csn = cs-to-csn cs
    in
     {!!}

{-

aLHS = v̲a̲l̲-mono-metric LHS E'' ϖ''
aRHS = v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((X , aLHS) ∷ E'') (WkN.wkn-cong ϖ'')
a0 = comp-mono-metric (wk-comp (wk-cong (wk-cong π')) (wk-comp (wk-cong (wk-cong π)) W)) ((Y , aRHS) ∷ (X , aLHS) ∷ E'') (WkN.wkn-cong (WkN.wkn-cong ϖ''))
a1 = val-mono-metric (wk-val π M) E ϖ
b1 = comp-mono-metric (wk-comp (wk-cong (wk-cong π)) W) E (WkN.wkn-cons (WkN.wkn-cons ϖ))
c1 = comp-mono-metric (wk-comp (wk-cong (wk-cong π)) W) ((Y , proj₁ (a1) , (λ c → rhs (proj₁ (proj₂ (a1)) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (a1)) c≤c'))) ∷ (X , proj₁ (a1) , (λ c → lhs (proj₁ (proj₂ (a1)) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (a1)) c≤c'))) ∷ E) (WkN.wkn-cong (WkN.wkn-cong ϖ))

Goal:   suc (⟪ proj₁ (proj₂ (a0)) csn ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (a0)) csn ⟫ csn)
      ≤ suc (vx (proj₁ (proj₂ (a1)) csn) + ⟪ proj₁ (proj₂ (b1)) csn ⟫ + ⟪ (proj₁ (proj₂ (c1)) csn) ⟫
      + csn-to-nat₀ (suc (vx (proj₁ (proj₂ (a1)) csn) + ⟪ proj₁ (proj₂ (b1)) csn ⟫ + ⟪ (proj₁ (proj₂ (c1)) csn) ⟫)) csn)

OLDX:

aLHS = v̲a̲l̲-mono-metric LHS E'' ϖ''
aRHS = v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((X , v̲a̲l̲-mono-metric LHS E'' ϖ'') ∷ E'') (WkN.wkn-cong ϖ'')
a0 = comp-mono-metric (wk-comp (wk-cong (wk-cong π')) (wk-comp (wk-cong (wk-cong π)) W)) ((Y , aRHS) ∷ (X , aLHS) ∷ E'') (WkN.wkn-cong (WkN.wkn-cong ϖ''))
a1 = val-mono-metric (wk-val π M) E ϖ
b1 = comp-mono-metric (wk-comp (wk-cong (wk-cong π)) W) E (WkN.wkn-cons (WkN.wkn-cons ϖ))
c1 = proj₁ (comp-mono-metric (wk-comp (wk-cong (wk-cong π)) W) ((Y , (λ c → rhs (proj₁ (a1) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (a1) c≤c'))) ∷ (X , (λ c → lhs (proj₁ (a1) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (a1) c≤c'))) ∷ E) (WkN.wkn-cong (WkN.wkn-cong ϖ))) csn

Goal:   suc (         ⟪ proj₁ (a0) csn ⟫
        + csn-to-nat₀ ⟪ proj₁ (a0) csn ⟫ csn)
      ≤                suc (vx (proj₁ (a1) csn) + ⟪ proj₁ (b1) csn ⟫ + ⟪ c1 ⟫
        + csn-to-nat₀ (suc (vx (proj₁ (a1) csn) + ⟪ proj₁ (b1) csn ⟫ + ⟪ c1 ⟫)) csn)

STP: ⟪ proj₁ (a0) csn ⟫ ≤ ⟪ c1 ⟫

proof outline:
- prove that aLHS ≤ (λ c → lhs (proj₁ (a1) c)) and aRHS ≤ (λ c → rhs (proj₁ (a1) c))
- then use comp-wkx-lemma to show that ⟪ proj₁ (a0) csn ⟫ ≤ ⟪ c1 ⟫

-}

  comp-metric-decreasing (∙app-var {Z' = Z'} {Z = Z} {i = i} {N = N} {γ = γ} {cs = cs} {πₓ = πₓ} {wk≡ₓ = wk≡ₓ} {W = W} {γ' = γ'} i→λW πᵥ T≤S θ)
    =
    -- OLD:
    -- let
    --   EW  = (env-metric γ)
    --   E = proj₁ EW
    --   ϖ = proj₂ EW
    --   EW'  = (env-metric γ')
    --   E' = proj₁ EW'
    --   ϖ' = proj₂ EW'
    --   csn = cs-to-csn cs
    -- in
    let
      EW = env-mono-metric γ
      E = proj₁ EW
      ϖ = proj₂ EW
      EW' = env-mono-metric γ'
      E' = proj₁ EW'
      ϖ' = proj₂ EW'
      csn = cs-to-csn cs
    in
      {!!}
{-

a1 = v̲a̲l̲-mono-metric N E ϖ
a2 = comp-mono-metric (wk-comp (wk-cong πᵥ) W) ((Z' , a1) ∷ E) (WkN.wkn-cong ϖ)
b1 = lookup-mono-metric i E ϖ
c1 = lcount i (elist-to-clist E) (wkn-to-wkc ϖ)

Goal: suc (⟪ proj₁ (proj₂ (a2)) csn ⟫
       + csn-to-nat₀ ⟪ proj₁ (proj₂ (a2)) csn ⟫ csn)
      ≤
      suc (p1 (incr 2 (proj₁ (proj₂ (b1)) csn)) + (⟪ proj₁ (proj₂ (a1)) csn ⟫ + c1 * ⟪ proj₁ (proj₂ (a1)) csn ⟫) + ⟪ (pw (incr 2 (proj₁ (proj₂ (b1)) csn))) ⟫
       + csn-to-nat₀ (suc (p1 (incr 2 (proj₁ (proj₂ (b1)) csn)) + (⟪ proj₁ (proj₂ (a1)) csn ⟫ + c1 * ⟪ proj₁ (proj₂ (a1)) csn ⟫) + ⟪ (pw (incr 2 (proj₁ (proj₂ (b1)) csn))) ⟫)) csn)

OLDX:

a1 = v̲a̲l̲-mono-metric N E ϖ
a2 = comp-mono-metric (wk-comp (wk-cong πᵥ) W) ((Z' , a1) ∷ E) (WkN.wkn-cong ϖ)
b1 = lookup-mono-metric i E ϖ

Goal:  suc (        ⟪ proj₁ (a2) csn ⟫
      + csn-to-nat₀ ⟪ proj₁ (a2) csn ⟫ csn)
      ≤
                     suc (p1 (incr 2 (proj₁ (b1) csn)) + (⟪ proj₁ (a1) csn ⟫ + p2 (proj₁ (b1) csn) * ⟪ proj₁ (a1) csn ⟫) + ⟪ p3 (incr 2 (proj₁ (b1) csn)) ⟫
      + csn-to-nat₀ (suc (p1 (incr 2 (proj₁ (b1) csn)) + (⟪ proj₁ (a1) csn ⟫ + p2 (proj₁ (b1) csn) * ⟪ proj₁ (a1) csn ⟫) + ⟪ p3 (incr 2 (proj₁ (b1) csn)) ⟫)) csn)

Will be similar to app-lam case.

-}

  comp-metric-decreasing (∙app-pm {Γ = Γ} {X = X} {Y = Y} {Z' = Z'} {Z = Z} {Δ = Δ} {M = M} {N₁ = N₁} {N = N} {γ = γ} {cs = cs} {πₓ = πₓ} {πₓ' = πₓ'} {LHS = LHS} {RHS = RHS} {γ' = γ'} {wk≡ₓ = wk≡ₓ} {wk≡ₓ' = wk≡ₓ'} M→M' π) =
    -- let
    --   EW  = (env-metric γ)
    --   E = proj₁ EW
    --   ϖ = proj₂ EW
    --   EW'  = (env-metric γ')
    --   E' = proj₁ EW'
    --   ϖ' = proj₂ EW'
    --   csn = cs-to-csn cs
    -- in
    let
      EW  = env-mono-metric γ
      E = proj₁ EW
      ϖ = proj₂ EW
      EW'  = env-mono-metric γ'
      E' = proj₁ EW'
      ϖ' = proj₂ EW'
      csn = cs-to-csn cs
    in
      {!!}

{-

a1 = v̲a̲l̲-mono-metric LHS E' ϖ'
a2 = v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((X , a1) ∷ E') (WkN.wkn-cong ϖ')
a3 = val-mono-metric (wk-val (wk-cong (wk-cong π)) N₁) ((Y , a2) ∷ (X , a1) ∷ E') (WkN.wkn-cong (WkN.wkn-cong ϖ'))
a4 = v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk (wk-wk π)) N) ((Y , a2) ∷ (X , a1) ∷ E') (WkN.wkn-cong (WkN.wkn-cong ϖ'))
b1 = val-mono-metric M E ϖ
b2 = val-mono-metric N₁ ((Y , proj₁ (b1) , (λ c → rhs (proj₁ (proj₂ (b1)) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (b1)) c≤c'))) ∷ (X , proj₁ (b1) , (λ c → lhs (proj₁ (proj₂ (b1)) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (b1)) c≤c'))) ∷ E) (WkN.wkn-cong (WkN.wkn-cong ϖ))
b3 = val-mono-metric N₁ E (WkN.wkn-cons (WkN.wkn-cons ϖ))
b4 = v̲a̲l̲-mono-metric N E ϖ

Goal: 2+ (p1 (proj₁ (proj₂ (a3)) csn) + (⟪ proj₁ (proj₂ (a4)) csn ⟫ + proj₁ (a3) * ⟪ proj₁ (proj₂ (a4)) csn ⟫) + ⟪ (pw (proj₁ (proj₂ (a3)) csn)) ⟫
      + csn-to-nat₀ (suc (p1 (proj₁ (proj₂ (a3)) csn) + (⟪ proj₁ (proj₂ (a4)) csn ⟫ + proj₁ (a3) * ⟪ proj₁ (proj₂ (a4)) csn ⟫) + ⟪ (pw (proj₁ (proj₂ (a3)) csn)) ⟫)) csn)
      ≤
      suc (p1 (incr (suc (vx (proj₁ (proj₂ (b1)) csn) + ⟪ proj₁ (proj₂ (b3)) csn ⟫)) (proj₁ (proj₂ (b2)) csn)) + (⟪ proj₁ (proj₂ (b4)) csn ⟫ + vcount N₁ (proj₁ (b1) ∷ proj₁ (b1) ∷ elist-to-clist E) (WkC.wkc-cong (WkC.wkc-cong (wkn-to-wkc ϖ))) * ⟪ proj₁ (proj₂ (b4)) csn ⟫) + ⟪ (pw (incr (suc (vx (proj₁ (proj₂ (b1)) csn) + ⟪ proj₁ (proj₂ (b3)) csn ⟫)) (proj₁ (proj₂ (b2)) csn))) ⟫
      + csn-to-nat₀ (suc (p1 (incr (suc (vx (proj₁ (proj₂ (b1)) csn) + ⟪ proj₁ (proj₂ (b3)) csn ⟫)) (proj₁ (proj₂ (b2)) csn)) + (⟪ proj₁ (proj₂ (b4)) csn ⟫ + vcount N₁ (proj₁ (b1) ∷ proj₁ (b1) ∷ elist-to-clist E) (WkC.wkc-cong (WkC.wkc-cong (wkn-to-wkc ϖ))) * ⟪ proj₁ (proj₂ (b4)) csn ⟫) + ⟪ (pw (incr (suc (vx (proj₁ (proj₂ (b1)) csn) + ⟪ proj₁ (proj₂ (b3)) csn ⟫)) (proj₁ (proj₂ (b2)) csn))) ⟫)) csn)

OLDX:

a1 = v̲a̲l̲-mono-metric LHS E' ϖ'
a2 = v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((X , a1) ∷ E') (WkN.wkn-cong ϖ')
a3 = val-mono-metric (wk-val (wk-cong (wk-cong π)) N₁) ((Y , a2) ∷ (X , a1) ∷ E') (WkN.wkn-cong (WkN.wkn-cong ϖ'))
a4 = v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk (wk-wk π)) N) ((Y , a2) ∷ (X , a1) ∷ E') (WkN.wkn-cong (WkN.wkn-cong ϖ'))
b1 = val-mono-metric M E ϖ
b2 = val-mono-metric N₁ ((Y , (λ c → rhs (proj₁ (b1) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (b1) c≤c'))) ∷ (X , (λ c → lhs (proj₁ (b1) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (b1) c≤c'))) ∷ E) (WkN.wkn-cong (WkN.wkn-cong ϖ))
b3 = val-mono-metric N₁ E (WkN.wkn-cons (WkN.wkn-cons ϖ))
b4 = v̲a̲l̲-mono-metric N E ϖ

Goal:
               2+      (p1 (proj₁ (a3) csn) + (⟪ proj₁ (a4) csn ⟫ + p2 (proj₁ (a3) csn) * ⟪ proj₁ (a4) csn ⟫) + ⟪ p3 (proj₁ (a3) csn) ⟫
    + csn-to-nat₀ (suc (p1 (proj₁ (a3) csn) + (⟪ proj₁ (a4) csn ⟫ + p2 (proj₁ (a3) csn) * ⟪ proj₁ (a4) csn ⟫) + ⟪ p3 (proj₁ (a3) csn) ⟫)) csn)
      ≤
                   suc (p1 (incr (suc (vx (proj₁ (b1) csn) + ⟪ proj₁ (b3) csn ⟫)) (proj₁ (b2) csn)) + (⟪ proj₁ (b4) csn ⟫ + p2 (proj₁ (b2) csn) * ⟪ proj₁ (b4) csn ⟫) + ⟪ p3 (incr (suc (vx (proj₁ (b1) csn) + ⟪ proj₁ (b3) csn ⟫)) (proj₁ (b2) csn)) ⟫
    + csn-to-nat₀ (suc (p1 (incr (suc (vx (proj₁ (b1) csn) + ⟪ proj₁ (b3) csn ⟫)) (proj₁ (b2) csn)) + (⟪ proj₁ (b4) csn ⟫ + p2 (proj₁ (b2) csn) * ⟪ proj₁ (b4) csn ⟫) + ⟪ p3 (incr (suc (vx (proj₁ (b1) csn) + ⟪ proj₁ (b3) csn ⟫)) (proj₁ (b2) csn)) ⟫)) csn)

STP:
      2+      (p1 (proj₁ (a3) csn) + (⟪ proj₁ (a4) csn ⟫ + p2 (proj₁ (a3) csn) * ⟪ proj₁ (a4) csn ⟫) + ⟪ p3 (proj₁ (a3) csn) ⟫
  ≤   suc     (p1 (incr (suc (vx (proj₁ (b1) csn) + ⟪ proj₁ (b3) csn ⟫)) (proj₁ (b2) csn)) + (⟪ proj₁ (b4) csn ⟫ + p2 (proj₁ (b2) csn) * ⟪ proj₁ (b4) csn ⟫) + ⟪ p3 (incr (suc (vx (proj₁ (b1) csn) + ⟪ proj₁ (b3) csn ⟫)) (proj₁ (b2) csn)) ⟫
  =   suc     (p1 (incr (suc (vx (proj₁ (b1) csn) + ⟪ proj₁ (b3) csn ⟫)) (proj₁ (b2) csn)) + (⟪ proj₁ (b4) csn ⟫ + p2 (proj₁ (b2) csn) * ⟪ proj₁ (b4) csn ⟫) + ⟪ p3 (proj₁ (b2) csn) ⟫

We should have a3 ≤ b2. Then it is
STP:
      (⟪ proj₁ (a4) csn ⟫ + p2 (proj₁ (a3) csn) * ⟪ proj₁ (a4) csn ⟫)
  ≤   (⟪ proj₁ (b4) csn ⟫ + p2 (proj₁ (b2) csn) * ⟪ proj₁ (b4) csn ⟫)

We should also have a4 ≤ b4. The proof then follows.

-}

  comp-metric-decreasing (∙app-lam {X = X} {Y = Y} {W = W} {N = N} {γ = γ} {cs = cs} {πₓ = πₓ} {wk≡ₓ = wk≡ₓ}) =
    let
      EW  = (env-mono-metric γ)
      E = proj₁ EW
      ϖ = proj₂ EW
      csn = cs-to-csn cs
      z1 = c̲o̲m̲p-mono-metric (a̲pp (lam W) N) E ϖ
      x1 = v̲a̲l̲-mono-metric N E ϖ
      x2 = val-mono-metric (lam W) E ϖ
    in
      {!!}

{-

x1 = v̲a̲l̲-mono-metric N E ϖ

a2 = comp-mono-metric W ((X , x1) ∷ E) (WkN.wkn-cong ϖ)
a4 = comp-mono-metric W E (WkN.wkn-cons ϖ)

Goal:    suc (⟪ proj₁ (proj₂ (a2)) csn ⟫
       + csn-to-nat₀ ⟪ proj₁ (proj₂ (a2)) csn ⟫ csn)
      ≤ 2+ (suc (⟪ proj₁ (proj₂ x1) csn ⟫ + ccount W (elist-to-clist E) (WkC.wkc-cons (wkn-to-wkc ϖ)) * ⟪ proj₁ (proj₂ x1) csn ⟫ + ⟪ (proj₁ (proj₂ (a4)) csn) ⟫
        + csn-to-nat₀ (2+ (suc (⟪ proj₁ (proj₂ x1) csn ⟫ + ccount W (elist-to-clist E) (WkC.wkc-cons (wkn-to-wkc ϖ)) * ⟪ proj₁ (proj₂ x1) csn ⟫ + ⟪ (proj₁ (proj₂ (a4)) csn) ⟫))) csn))


OLDX:

a1 = v̲a̲l̲-mono-metric N E ϖ
a2 = comp-mono-metric W ((X , a1) ∷ E) (WkN.wkn-cong ϖ)
a3 = mono-comp-count h W E (WkN.wkn-cons ϖ)
a4 = comp-mono-metric W E (WkN.wkn-cons ϖ)

Goal:                suc (⟪ proj₁ (a2) csn ⟫
            + csn-to-nat₀ ⟪ proj₁ (a2) csn ⟫ csn)
      ≤
                     2+ (suc (⟪ proj₁ (a1) csn ⟫ + proj₁ (a3) csn * ⟪ proj₁ (a1) csn ⟫ + ⟪ (proj₁ (a4) csn) ⟫
      + csn-to-nat₀ (2+ (suc (⟪ proj₁ (a1) csn ⟫ + proj₁ (a3) csn * ⟪ proj₁ (a1) csn ⟫ + ⟪ (proj₁ (a4) csn) ⟫ ))) csn))

STP: suc ⟪ proj₁ (a2) csn ⟫ ≤ 3 + ⟪ proj₁ (a1) csn ⟫ + proj₁ (a3) csn * ⟪ proj₁ (a1) csn ⟫ + ⟪ (proj₁ (a4) csn) ⟫

SCRATCH:
STP: comp-mono-metric W ((X , a1) ∷ E) (wkn-cong ϖ) ≤ (mono-comp-count h W E (wkn-cons ϖ)) * ⟪ proj₁ a1 csn ⟫ + comp-mono-metric W E (wkn-cons ϖ)

-}

  comp-metric-decreasing (∘app {M = M} {N = N} {γ = γ} {cs = cs} {πₓ = πₓ} {πₓ' = πₓ'} {N' = N'} {γ' = γ'} {wk≡ₓ = wk≡ₓ} {wk≡ₓ' = wk≡ₓ'} N→N' π) =
    let
      EW  = (env-mono-metric γ)
      E = proj₁ EW
      ϖ = proj₂ EW
      EW'  = (env-mono-metric γ')
      E' = proj₁ EW'
      ϖ' = proj₂ EW'
      csn = cs-to-csn cs
      ----------------------------------------------------------------------
      -- need θ to apply lemmas
      ----------------------------------------------------------------------
    in
      {!!}

{-

a1 = val-mono-metric (wk-val π M) E' ϖ'
a2 = v̲a̲l̲-mono-metric N' E' ϖ'
b1 = val-mono-metric M E ϖ
b2 = val-mono-metric N E ϖ

Goal: 2+ (p1 (proj₁ (proj₂ (a1)) csn) + (⟪ proj₁ (proj₂ (a2)) csn ⟫ + proj₁ (a1) * ⟪ proj₁ (proj₂ (a2)) csn ⟫) + ⟪ (pw (proj₁ (proj₂ (a1)) csn)) ⟫
      + csn-to-nat₀ (suc (p1 (proj₁ (proj₂ (a1)) csn) + (⟪ proj₁ (proj₂ (a2)) csn ⟫ + proj₁ (a1) * ⟪ proj₁ (proj₂ (a2)) csn ⟫) + ⟪ (pw (proj₁ (proj₂ (a1)) csn)) ⟫)) csn)
      ≤
      2+ (p1 (proj₁ (proj₂ (b1)) csn) + (⟪ proj₁ (proj₂ (b2)) csn ⟫ + proj₁ (b1) * ⟪ proj₁ (proj₂ (b2)) csn ⟫) + ⟪ (pw (proj₁ (proj₂ (b1)) csn)) ⟫
      + csn-to-nat₀ (2+ (p1 (proj₁ (proj₂ (b1)) csn) + (⟪ proj₁ (proj₂ (b2)) csn ⟫ + proj₁ (b1) * ⟪ proj₁ (proj₂ (b2)) csn ⟫) + ⟪ (pw (proj₁ (proj₂ (b1)) csn)) ⟫)) csn)

OLDX:

a1 = val-mono-metric (wk-val π M) E' ϖ'
a2 = v̲a̲l̲-mono-metric N' E' ϖ'
b1 = val-mono-metric M E ϖ
b2 = val-mono-metric N E ϖ

Goal:                  2+ (p1 (proj₁ (a1) csn) + (⟪ proj₁ (a2) csn ⟫ + p2 (proj₁ (a1) csn) * ⟪ proj₁ (a2) csn ⟫) + ⟪ p3 (proj₁ (a1) csn) ⟫
       + csn-to-nat₀ (suc (p1 (proj₁ (a1) csn) + (⟪ proj₁ (a2) csn ⟫ + p2 (proj₁ (a1) csn) * ⟪ proj₁ (a2) csn ⟫) + ⟪ p3 (proj₁ (a1) csn) ⟫)) csn)
      ≤
                       2+ (p1 (proj₁ (b1) csn) + (⟪ proj₁ (b2) csn ⟫ + p2 (proj₁ (b1) csn) * ⟪ proj₁ (b2) csn ⟫) + ⟪ p3 (proj₁ (b1) csn) ⟫
        + csn-to-nat₀ (2+ (p1 (proj₁ (b1) csn) + (⟪ proj₁ (b2) csn ⟫ + p2 (proj₁ (b1) csn) * ⟪ proj₁ (b2) csn ⟫) + ⟪ p3 (proj₁ (b1) csn) ⟫)) csn)

STP:   2+ p1 (proj₁ (a1) csn) + (⟪ proj₁ (a2) csn ⟫ + p2 (proj₁ (a1) csn) * ⟪ proj₁ (a2) csn ⟫) + ⟪ p3 (proj₁ (a1) csn) ⟫
     ≤ 2+ p1 (proj₁ (b1) csn) + (⟪ proj₁ (b2) csn ⟫ + p2 (proj₁ (b1) csn) * ⟪ proj₁ (b2) csn ⟫) + ⟪ p3 (proj₁ (b1) csn) ⟫

STP:   ⟪ proj₁ (a2) csn ⟫ + p2 (proj₁ (a1) csn) * ⟪ proj₁ (a2) csn ⟫ + ⟪ proj₁ (a1) csn ⟫
     ≤ ⟪ proj₁ (b2) csn ⟫ + p2 (proj₁ (b1) csn) * ⟪ proj₁ (b2) csn ⟫ + ⟪ proj₁ (b1) csn ⟫

-}

  comp-metric-decreasing (∘var {M = M} {γ = γ} {i = i} {γ' = γ'} {W = W} {γ'' = γ''} {cs = cs} {cs' = cs'} {πₓ = πₓ} {πₓ'' = πₓ''} {wk≡ₓ = wk≡ₓ} {wk≡ₓ'' = wk≡ₓ''} M→i π' x₁ πᵥ) =
    let
      EW = (env-mono-metric γ)
      E = proj₁ EW
      ϖ = proj₂ EW
      EW' = (env-mono-metric γ')
      E' = proj₁ EW'
      ϖ' = proj₂ EW'
      EW''  = (env-mono-metric γ'')
      E'' = proj₁ EW''
      ϖ'' = proj₂ EW''
      csn = cs-to-csn cs
      csn' = cs-to-csn cs'
    in
      {!!}


{-

Goal:          suc (⟪ proj₁ (proj₂ (comp-mono-metric W E'' ϖ'')) csn' ⟫
      + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric W E'' ϖ'')) csn' ⟫ csn')
      ≤
                     suc (⟪ proj₁ (proj₂ (val-mono-metric M E ϖ)) csn ⟫ + 0
      + csn-to-nat₀ (suc (⟪ proj₁ (proj₂ (val-mono-metric M E ϖ)) csn ⟫ + 0)) csn)

OLDX:

a1 = comp-mono-metric W E'' ϖ''
a2 = val-mono-metric M E ϖ

Goal: suc (⟪ proj₁ (a1) csn' ⟫ + csn-to-nat₀ ⟪ proj₁ (a1) csn' ⟫ csn')
      ≤
      suc (⟪ proj₁ (a2) csn ⟫ + 0 + csn-to-nat₀ (suc (⟪ proj₁ (a2) csn ⟫ + 0)) csn)

STP:            suc (⟪ proj₁ (a1) csn' ⟫
       + csn-to-nat₀ ⟪ proj₁ (a1) csn' ⟫ csn')
      ≤
                      suc (⟪ proj₁ (a2) csn ⟫
       + csn-to-nat₀ (suc (⟪ proj₁ (a2) csn ⟫)) csn)

STP: ⟪ proj₁ (a1) csn' ⟫ ≤ ⟪ proj₁ (a2) csn ⟫

-}

-------------------------------------------------------
-------------------------------------------------------
-------------------------------------------------------

-------------------------------------------------------
  postulate debuglemma : m ≤ n
  -- debuglemma = ≤-refl

-------------------------------
  -- {-# TERMINATING #-}
  mutual

    app-eval-rec :   (M : Γ' ⊢ᵛ X `⇒ Y) → (N : V̲a̲l̲ Γ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ Y) → (πₓ : Wk Γ Δ)
                   → (wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → (n : ℕ)
                   -- → (n ≤ n)
                   → (compstate-metric ((∙⟨ (a̲pp (wk-val π M) N) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀}) ≤ n)
                   → CompSteps ((∙⟨ (a̲pp (wk-val π M) N) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    app-eval-rec (var i) N γ π cs πₓ wk≡₀ zero m≤n with m≤n
    ... | ()
    app-eval-rec (var i) N γ π cs πₓ wk≡₀ (suc n) m≤n with lookup (wk-mem π i) γ
    -- app-eval-rec (var i) N γ π cs πₓ wk≡₀ n m≤n with lookup (wk-mem π i) γ
    ... | steps i>>T (found-lam {X = X} {W = W} {γ = γ₁}) i≡T π₁ w≡γ cnt₁≤cnt₂ T≤S θ with comp-eval-rec W (γ ﹐ N) (wk-cong π₁) cs (wk-wk πₓ) wk≡₀ n debuglemma
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
    ... | steps {T = ∙ (⭭ pa̲i̲r̲ {X = X} {Y = Y} LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ _ _ _ with wk-val-trans N₁ (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
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
                  -- → (n ≤ n)
                  → (compstate-metric ((∘⟨ wk-comp π W ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀}) ≤ n)
                  → CompSteps ((∘⟨ wk-comp π W ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    comp-eval-rec (return {A = X} M) γ π ◻ πₓ wk≡₀ n m≤n with val-eval-rec {X = X} M γ π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ cnt₁≤cnt₂ VS>VT θ =

                 steps

                    (∘⟨ wk-comp π (return M) ⊰ γ ╎ ◻ ⟩ →ᶜ⟨ ∘return {VS>VT = VS>VT} M>T ⟩ (∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ ◻ ⟩ ◼))

                    ret

                    (cong (λ x → (η x) k₀) M≡T)

                    (compstate-metric ((∘⟨ wk-comp π (return M) ⊰ γ ╎ ◻ ⟩) {π = πₓ} {wk≡ = wk≡₀}) ∷ compstate-metric ((∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ ◻ ⟩) {π = wk-trans π' πₓ} {wk≡ = wk≡₀}) ∷ [])

    comp-eval-rec (return {A = X} M) γ π ((M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁}) πₓ wk≡₀ zero m≤n with m≤n
    ... | ()
    comp-eval-rec (return {A = X} M) γ π ((M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁}) πₓ wk≡₀ (suc n) m≤n with val-eval-rec {X = X} M γ π
    -- comp-eval-rec (return {A = X} M) γ π ((M' ⊲ γ' ⦂⦂ cs) {π = π₁} {wk≡ = wk≡₁}) πₓ wk≡₀ n m≤n with val-eval-rec {X = X} M γ π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ cnt₁≤cnt₂ VS>VT θ with
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
                                         ≡⟨ wk≡₀ ⟩ ⟦ γ' ⟧ᴱ ∎} {VS>VT = VS>VT} M>T ⟩ ((∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ M' ⊲ γ' ⦂⦂ cs ⟩) {wk≡ = ≡-syntax.step-≡-⟩ _≡_ trans (⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ)
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
    ...  | steps {T = ∙ ((⭭_ {X = X `× Y} (pa̲i̲r̲ LHS RHS) ⊲ γ' ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ _ _ _ with
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
    ... | steps {T = ∙ ((⭭_ NT ⊲ γᴺ ∷ □) {↥ = 🗆})} N>NT ∙NT N≡NT πᴺ wk≡ᴺ _ _ _ with
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

    comp-eval-rec (var {A = X} M) γ π cs πₓ wk≡₀ zero m≤n with m≤n
    ... | ()
    comp-eval-rec (var {A = X} M) γ π cs πₓ wk≡₀ (suc n) m≤n with val-eval-rec {X = `V} M γ π
    -- comp-eval-rec (var {A = X} M) γ π cs πₓ wk≡₀ n m≤n with val-eval-rec {X = `V} M γ π
    ... | steps {T = ∙ ((⭭ v̲a̲r̲ i) ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ _ _ _ with lookup i γ₁
    ... | steps i>>T (found-comp {X = X} {W = W'} {γ = γ'} {cs = cs'} {π = πᶜ} {wk≡ = wk≡c}) i≡T π₂ w≡γ cnt₁≤cnt₂ T≤S θ with
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
-- 1109 ∷ 1108 ∷ 662 ∷ 648 ∷ 620 ∷ 585 ∷ 74 ∷ 60 ∷ 46 ∷ 34 ∷ 26 ∷ 14 ∷ 4 ∷ 2 ∷ []
_ : comp-eval-test-metric ex11 ≡ {! comp-eval-test-metric ex15 !}
_ = let
      -- tm = push (push (app (lam {A = `Unit} (sub (var (var h)) (return unit))) unit) (return unit)) (app (lam (return unit)) (pair (pair (pair (var h) (var h)) (var h)) (var h)))
      -- tmR = (app (lam (return unit)) (pair (pair (pair (var h) (var h)) (var h)) (var h)))
      -- tmL = (push (app (lam {A = `Unit} (sub (var (var h)) (return unit))) unit) (return unit))
      -- csn1 = cs-to-csn ◻
      -- csn2 = cs-to-csn ((app (lam (return unit)) (pair (pair (pair (var h) (var h)) (var h)) (var h))) ⊲ ∗ ⦂⦂ ◻)
      -- e = env-metric ∗
      -- --cm1 = comp-metric tm (proj₁ e) (proj₂ e) csn1
      -- cmL = comp-metric tmL (proj₁ e) (proj₂ e) csn2
      -- cmR = comp-metric tmR (proj₁ e) (wkn-cons (proj₂ e)) csn1
      -- cmRcong = comp-metric tmR ((`Unit , λ x → comp-metric tmL (proj₁ e) (proj₂ e) csn2) ∷ (proj₁ e)) (wkn-cong (proj₂ e)) csn1
      -- --cm1l = comp-metric tmL (proj₁ e) (proj₂ e) csn1
      -- --c1+ = csn-to-nat₀ ⟪ cm1 ⟫ csn1
      -- --cm2 = comp-metric tmL (proj₁ e) (proj₂ e) csn2
      -- --c2+ = csn-to-nat₀ ⟪ cm2 ⟫ csn2
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


AAAAAAAA -}
