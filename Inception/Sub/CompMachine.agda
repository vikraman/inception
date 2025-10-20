module Inception.Sub.CompMachine (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry)
open import Function.Base using (_∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Unit
open import Data.Nat

open import Inception.Sub.ValueMachine R

module CMain {R₀ : Ty} (k₀ : ⟦ R₀ ⟧ → R) where

  open VMain {R₀ = R₀} k₀

  data CompState : Set where

        ∘⟨_⊰_╎_⟩ : (W : Γ ⊢ᶜ X) → (γ : Env Γ) → (cs : CompStack Δ X) → {π : Wk Γ Δ} → {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → CompState

        ∙⟨_⊰_╎_⟩ : (W : C̲o̲m̲p Γ X) → (γ : Env Γ) → (cs : CompStack Δ X) → {π : Wk Γ Δ} → {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → CompState

  data CompHaltingState : CompState → Set where

      ret : {M : V̲a̲l̲ Γ R₀} → {γ : Env Γ} → CompHaltingState ((∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ ╎ ◻ ⟩) {π = wk-wk-ε} {wk≡ = refl} )


  infixr 15 _→ᶜ⟨_⟩_
  infix  15 _→ᶜ*_
  infixr 10 _⨾ᶜ_

  -- ⟦_⟧ᶜꟴ : CompState → K ⟦ R₀ ⟧
  -- ⟦ ∘⟨ W ⊰ γ ╎ cs ⟩ ⟧ᶜꟴ = ⟦ cs ⟧ᶜˢ (⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ)
  -- ⟦ ∙⟨ W ⊰ γ ╎ cs ⟩ ⟧ᶜꟴ = ⟦ cs ⟧ᶜˢ (⟦ toComp W ⟧ᶜ ⟦ γ ⟧ᴱ)

  ⟦_⟧ᶜꟴ : CompState → R
  ⟦ ∘⟨ W ⊰ γ ╎ cs ⟩ ⟧ᶜꟴ = ⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ
  ⟦ ∙⟨ W ⊰ γ ╎ cs ⟩ ⟧ᶜꟴ = ⟦ toComp W ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ

  -- Computation Machine
  --------------------------------------------------

  data _→ᶜ*_ : CompState → CompState → Set
  data _→ᶜ_ : CompState → CompState → Set


  ---

  data _→ᶜ_  where

        ∘return  :    {M : Γ ⊢ᵛ X} → {γ : Env Γ'} → {π : Wk Γ' Γ} → {M' : V̲a̲l̲ Γ'' X} → {γ' : Env Γ''} → {cs : CompStack Δ X} → {πₓ : Wk Γ' Δ} → {πₓ' : Wk Γ'' Δ} → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → {wk≡ₓ' : ⟦ πₓ' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                      → ((∘ ((⇡ wk-val π M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ M' ⊲ γ' ∷ □) {↥ = 🗆})))
                  ----------------------------------------------------------------
                    → ((∘⟨ wk-comp π (return M) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ} )→ᶜ ((∙⟨ r̲e̲t̲u̲r̲n̲ M' ⊰ γ' ╎ cs ⟩) {π = πₓ'} {wk≡ = wk≡ₓ'})

        ∙return  :    {M : V̲a̲l̲ Γ X} → {γ : Env Γ} → {N : (Γ' ∙ X) ⊢ᶜ Y} → {γ' : Env Γ'} → {π : Wk Γ Γ'} → {cs : CompStack Δ Y} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ' Δ} → {wk≡ₓ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ} → {wk≡ₓ' : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                  ----------------------------------------------------------------
                    → ((∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ ╎ ((N ⊲ γ' ⦂⦂ cs) {π = πₓ'}) ⟩) {π = π} {wk≡ = wk≡ₓ}) →ᶜ ((∘⟨ wk-comp (wk-cong π) N ⊰ γ ﹐ M ╎ cs ⟩) {π = wk-wk πₓ} {wk≡ = wk≡ₓ'})

        ∘push    :    {M : Γ ⊢ᶜ X} → {N : (Γ ∙ X) ⊢ᶜ Y} → {γ : Env Γ} → {cs : CompStack Δ Y} → {πₓ : Wk Γ Δ} → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                  ----------------------------------------------------------------
                    → ((∘⟨ push M N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ}) →ᶜ ((∘⟨ M ⊰ γ ╎ ((N ⊲ γ ⦂⦂ cs) {π = πₓ}) ⟩) {π = wk-id} {wk≡ = refl})

        ∘sub     :    {M : (Γ ∙ `V) ⊢ᶜ X} → {N : Γ ⊢ᶜ X} → {γ : Env Γ} → {cs : CompStack Δ X} → {πₓ : Wk Γ Δ} → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                  ----------------------------------------------------------------
                    → ((∘⟨ sub M N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ}) →ᶜ ((∘⟨ M ⊰ ((γ ﹐﹝ N ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡ₓ}) ╎ cs ⟩) {π = wk-wk πₓ} {wk≡ = wk≡ₓ})

        ∘pm      :    {M : Γ' ⊢ᵛ X `× Y} → {γ : Env Γ} → {W : (Γ' ∙ X ∙ Y) ⊢ᶜ Z} → {cs : CompStack Δ Z} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ'' Δ} → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → {wk≡ₓ' : ⟦ πₓ' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                    → {LHS : V̲a̲l̲ Γ'' X} → {RHS : V̲a̲l̲ Γ'' Y} → {γ'' : Env Γ''} → (π : Wk Γ Γ')
                    → ((∘ ((⇡ wk-val π M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ'' ∷ □) {↥ = 🗆}))) → (π' : Wk Γ'' Γ)
                  ----------------------------------------------------------------
                    → ((∘⟨ pm (wk-val π M) (wk-comp (wk-cong (wk-cong π)) W) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ}) →ᶜ ((∘⟨ wk-comp (wk-cong (wk-cong π')) (wk-comp (wk-cong (wk-cong π)) W) ⊰ γ' ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ╎ cs ⟩) {π = wk-wk (wk-wk πₓ')}  {wk≡ = wk≡ₓ'})

        ∙app-var     :    {i : Γ ∋ (Z' `⇒ Z)} → {N : V̲a̲l̲ Γ Z'} → {γ : Env Γ} → {cs : CompStack Δ Z} → {πₓ : Wk Γ Δ} → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → {W : (Γ' ∙ Z') ⊢ᶜ Z} → {γ' : Env Γ'}
                       → (⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ _﹐_ γ' (l̲a̲m̲ W) ⟩) → (πᵥ : Wk Γ Γ')
                     ----------------------------------------------------------------
                       → ((∙⟨ a̲pp (var i) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ}) →ᶜ ((∙⟨ a̲pp (wk-val πᵥ (lam W)) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ})

        ∙app-pm     :    {M : Γ ⊢ᵛ (X `× Y)} → {W : (Γ ∙ X ∙ Y) ⊢ᵛ (Z' `⇒ Z)} → {N : V̲a̲l̲ Γ Z'} → {γ : Env Γ} → {cs : CompStack Δ Z} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ' Δ}
                       → {LHS : V̲a̲l̲ Γ' X} → {RHS : V̲a̲l̲ Γ' Y} → {γ' : Env Γ'} → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → {wk≡ₓ' : ⟦ πₓ' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → ((∘ ((⇡ M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ' ∷ □) {↥ = 🗆}))) → (π : Wk Γ' Γ)
                     ----------------------------------------------------------------
                       → ((∙⟨ a̲pp (pm M W) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ}) →ᶜ ((∙⟨ a̲pp ((wk-val (wk-cong (wk-cong π)) W)) (wk-v̲a̲l̲ (wk-wk (wk-wk π)) N) ⊰ γ' ﹐ LHS ﹐ (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ╎ cs ⟩) {π = wk-wk (wk-wk πₓ')} {wk≡ = wk≡ₓ'})

        ∙app-lam     :   {W : (Γ ∙ X) ⊢ᶜ Y} → {N : V̲a̲l̲ Γ X} → {γ : Env Γ} → {cs : CompStack Δ Y} → {πₓ : Wk Γ Δ} → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                     ----------------------------------------------------------------
                       → ((∙⟨ a̲pp (lam W) N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ}) →ᶜ ((∘⟨ W ⊰ γ ﹐ N ╎ cs ⟩) {π = wk-wk πₓ} {wk≡ = wk≡ₓ})

        ∘app         :   {M : Γ ⊢ᵛ X `⇒ Y} → {N : Γ ⊢ᵛ X} → {γ : Env Γ} → {cs : CompStack Δ Y} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ' Δ}
                       → {N' : V̲a̲l̲ Γ' X} → {γ' : Env Γ'} → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → {wk≡ₓ' : ⟦ πₓ' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → ((∘ ((⇡ N ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ N' ⊲ γ' ∷ □) {↥ = 🗆}))) → (π : Wk Γ' Γ)
                     ----------------------------------------------------------------
                       → ((∘⟨ app M N ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ}) →ᶜ ((∙⟨ a̲pp (wk-val π M) N' ⊰ γ' ╎ cs ⟩) {π = πₓ'} {wk≡ = wk≡ₓ'})


        -- X and X' should always be the same, but I don't think we can easily check for that
        ∘var     :   {M : Γ ⊢ᵛ `V} → {γ : Env Γ} → {i : Γ' ∋ `V} → {γ' : Env Γ'} → {W : Γ'' ⊢ᶜ X'} → {γ'' : Env Γ''} → {cs : CompStack Δ X} → {cs' : CompStack Δ' X'} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ' Δ'} → {πₓ'' : Wk Γ'' Δ'}
                  → {wk≡ₓ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → {wk≡ₓ' : ⟦ πₓ' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs' ⟧ᴱ} → {wk≡ₓ'' : ⟦ πₓ'' ⟧ʷ ⟦ γ'' ⟧ᴱ ≡ ⟦ topCsEnv cs' ⟧ᴱ}
                  → ((∘ ((⇡ M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ v̲a̲r̲ i ⊲ γ' ∷ □) {↥ = 🗆}))) → (π' : Wk Γ' Γ)
                  → (⟨ i ∥ γ' ⟩ →ᴸ* ⟨ h ∥ ((γ'' ﹐﹝ W ╎ cs' ﹞) {π = πₓ''} {wk≡ = wk≡ₓ''}) ⟩) → (πᵥ : Wk Γ' Γ'')
                  ----------------------------------------------------------------
                    → ((∘⟨ var M ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡ₓ}) →ᶜ ((∘⟨ (wk-comp πᵥ W) ⊰ γ' ╎ cs' ⟩) {π = πₓ'} {wk≡ = wk≡ₓ'})

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

      --steps : {S T : CompState} → S →ᶜ* T → CompHaltingState T → (π : Wk (topCompCtx T) (topCompCtx S)) → CompSteps S
      --steps : {S T : CompState} → S →ᶜ* T → CompHaltingState T → ⟦ S ⟧ᶜꟴ k₀ ≡ ⟦ T ⟧ᶜꟴ k₀ → (π : Wk (topCompCtx T) (topCompCtx S)) → (⟦ π ⟧ʷ ⟦ topCompEnv T ⟧ᴱ ≡ ⟦ topCompEnv S ⟧ᴱ) → CompSteps S
      steps : {S T : CompState} → S →ᶜ* T → CompHaltingState T → ⟦ S ⟧ᶜꟴ ≡ ⟦ T ⟧ᶜꟴ → (π : Wk (topCompCtx T) (topCompCtx S)) → (⟦ π ⟧ʷ ⟦ topCompEnv T ⟧ᴱ ≡ ⟦ topCompEnv S ⟧ᴱ) → CompSteps S


  sub-cps : (M : (Γ ∙ `V) ⊢ᶜ X) → (N : Γ ⊢ᶜ X) → (γ : ⟦ Γ ⟧ˣ ) → (k : ⟦ X ⟧ → R) → ⟦ sub M N ⟧ᶜ γ k ≡ ⟦ M ⟧ᶜ ( γ , ⟦ N ⟧ᶜ γ k ) k
  sub-cps M N γ k = refl

  sub-cps' : (M : (Γ ∙ `V) ⊢ᶜ X) → (N : Γ ⊢ᶜ X) → (γ : Env Γ) → (cs : CompStack Δ X) → (πₓ : Wk Γ Δ) → (wk≡ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → ⟦ sub M N ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ ≡ ⟦ M ⟧ᶜ ⟦ (γ ﹐﹝ N ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡} ⟧ᴱ ⟦ cs ⟧ᴷ
  sub-cps' M N γ cs πₓ wk≡ = refl

  lem : (cs : CompStack Γ Y) → (cs' : CompStack Γ' X) → (W : Γ'' ⊢ᶜ X) → (γ : Env Γ'') → (⟦ cs ⟧ᶜˢ (varK ((⟦ cs' ⟧ᶜˢ (⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ)) k₀))) k₀ ≡ (⟦ cs' ⟧ᶜˢ (⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ)) k₀
  lem ◻ cs' W γ = refl
  lem ((W₀ ⊲ γ₀ ⦂⦂ cs) {π = π}) cs' W₁ γ₁ =
        ⟦ ((W₀ ⊲ γ₀ ⦂⦂ cs) {π = π}) ⟧ᶜˢ (varK (⟦ cs' ⟧ᶜˢ (⟦ W₁ ⟧ᶜ ⟦ γ₁ ⟧ᴱ) k₀)) k₀
      ≡⟨ refl ⟩
        ( ⟦ cs ⟧ᶜˢ (( ⟦ W₀ ⟧ᶜ ♯)(τ (⟦ γ₀ ⟧ᴱ , (varK (⟦ cs' ⟧ᶜˢ (⟦ W₁ ⟧ᶜ ⟦ γ₁ ⟧ᴱ) k₀)) ))) ) k₀
      ≡⟨ refl ⟩
        ⟦ cs ⟧ᶜˢ (λ k → ⟦ cs' ⟧ᶜˢ (⟦ W₁ ⟧ᶜ ⟦ γ₁ ⟧ᴱ) k₀) k₀
      ≡⟨ refl ⟩
        ⟦ cs ⟧ᶜˢ (varK (⟦ cs' ⟧ᶜˢ (⟦ W₁ ⟧ᶜ ⟦ γ₁ ⟧ᴱ) k₀)) k₀
      ≡⟨ lem cs cs' W₁ γ₁ ⟩
        ⟦ cs' ⟧ᶜˢ (⟦ W₁ ⟧ᶜ ⟦ γ₁ ⟧ᴱ) k₀ ∎

{-
  -- ⟦ W₁ ⊲ γ₁ ⦂⦂ tail ⟧ᶜˢ W =  ⟦ tail ⟧ᶜˢ (( ⟦ W₁ ⟧ᶜ ♯)(τ (⟦ γ₁ ⟧ᴱ , W)))

  --     ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) k) k) k₀
  --   ≡⟨ {!!} ⟩
  --      (⟦ cs ⟧ᶜˢ (⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ cs ⟧ᶜˢ (⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) k₀))) k₀

  {-
  lem2 : (cs : CompStack Δ X) → (W : Comp (Γ' ∙ `V) X) → (π : Wk Γ Γ') → (γ : Env Γ) → (V : Comp Γ' X) → ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) k) k) k₀ ≡ (⟦ cs ⟧ᶜˢ (⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ cs ⟧ᶜˢ (⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) k₀))) k₀
  lem2 ◻ W π γ V = refl
  lem2 ((W₀ ⊲ γ₀ ⦂⦂ cs) {π = πₓ}) W π γ V =

          ⟦ (W₀ ⊲ γ₀ ⦂⦂ cs) {π = πₓ} ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) k) k) k₀
        ≡⟨ refl ⟩
          ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ  (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ,    ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (λ z → ⟦ W₀ ⟧ᶜ (⟦ γ₀ ⟧ᴱ , z) k) )  (λ z → ⟦ W₀ ⟧ᶜ (⟦ γ₀ ⟧ᴱ , z) k)  ) k₀
        ≡⟨ refl ⟩
          ⟦ cs ⟧ᶜˢ (( ⟦ W₀ ⟧ᶜ ♯)(τ (⟦ γ₀ ⟧ᴱ ,      (λ k → ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) k) k)                  ))) k₀

  --                                    ⟦ cs ⟧ᶜˢ   (λ k → ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) k) k)                 k₀
  --                                 ≡  ⟦ cs ⟧ᶜˢ   (⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ cs ⟧ᶜˢ           (⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) k₀))   k₀
        ≡⟨ cong (λ x → ⟦ cs ⟧ᶜˢ (( ⟦ W₀ ⟧ᶜ ♯)(τ (⟦ γ₀ ⟧ᴱ , x ))) k₀) {!lem2 ? ? ? ? ?!} ⟩
          ⟦ cs ⟧ᶜˢ (( ⟦ W₀ ⟧ᶜ ♯)(τ (⟦ γ₀ ⟧ᴱ ,      (⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ (W₀ ⊲ γ₀ ⦂⦂ cs) {π = πₓ} ⟧ᶜˢ (⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) k₀))    ))) k₀
        ≡⟨ refl ⟩
          ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ,    ⟦ cs ⟧ᶜˢ (λ k₁ → ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (λ z → ⟦ W₀ ⟧ᶜ (⟦ γ₀ ⟧ᴱ , z) k₁)) k₀)  (λ z → ⟦ W₀ ⟧ᶜ (⟦ γ₀ ⟧ᴱ , z) k) ) k₀
        ≡⟨ refl ⟩
          ⟦ (W₀ ⊲ γ₀ ⦂⦂ cs) {π = πₓ} ⟧ᶜˢ (⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ (W₀ ⊲ γ₀ ⦂⦂ cs) {π = πₓ} ⟧ᶜˢ (⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) k₀)) k₀ ∎

                     --   ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) k) k) k₀
                     -- ≡⟨ {!!} ⟩
                     --    (⟦ cs ⟧ᶜˢ (⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ cs ⟧ᶜˢ (⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) k₀))) k₀

  -}

  lem3 : {X : Ty} → (cs : CompStack Δ Y) → (W : Comp (Γ' ∙ `V) X) → (W₀ : Comp (Δ ∙ X) Y) → (γ₀ : Env Δ) → (π : Wk Γ Γ') → (γ : Env Γ) → (V : Comp Γ' X) → ⟦ cs ⟧ᶜˢ (( ⟦ W₀ ⟧ᶜ ♯)(τ (⟦ γ₀ ⟧ᴱ ,  (λ k → ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) k) k) ))) k₀ ≡ ⟦ cs ⟧ᶜˢ (( ⟦ W₀ ⟧ᶜ ♯)(τ (⟦ γ₀ ⟧ᴱ , (⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ (W₀ ⊲ γ₀ ⦂⦂ cs) {π = wk-id} ⟧ᶜˢ (⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) k₀))  ))) k₀

  lem3 ◻ W W₀ γ₀ π γ V = refl
  lem3 ((W₁ ⊲ γ₁ ⦂⦂ cs) {π = πₓ}) W W₀ γ₀ π γ V =
      ⟦ (W₁ ⊲ γ₁ ⦂⦂ cs) {π = πₓ} ⟧ᶜˢ ((⟦ W₀ ⟧ᶜ ♯) (τ (⟦ γ₀ ⟧ᴱ , (λ k → ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) k) k)))) k₀
--    ⟦ cs ⟧ᶜˢ                      (( ⟦ W₀ ⟧ᶜ ♯)(τ (⟦ γ₀ ⟧ᴱ ,  (λ k → ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) k) k) ))) k₀
--  ≡ ⟦ cs ⟧ᶜˢ                      (( ⟦ W₀ ⟧ᶜ ♯)(τ (⟦ γ₀ ⟧ᴱ , (⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ (W₀ ⊲ γ₀ ⦂⦂ cs) {π = wk-id}                       ⟧ᶜˢ (⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) k₀))  ))) k₀
      ≡⟨ refl ⟩
        ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ,                  ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (λ z → ⟦ W₀ ⟧ᶜ (⟦ γ₀ ⟧ᴱ , z) (λ z₁ → ⟦ W₁ ⟧ᶜ (⟦ γ₁ ⟧ᴱ , z₁) k)))      (λ z → ⟦ W₀ ⟧ᶜ (⟦ γ₀ ⟧ᴱ , z) (λ z₁ → ⟦ W₁ ⟧ᶜ (⟦ γ₁ ⟧ᴱ , z₁) k))) k₀
      ≡⟨ cong (λ x → ⟦ cs ⟧ᶜˢ x k₀)  {!!} ⟩
        ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ cs ⟧ᶜˢ (λ k₁ → ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (λ z → ⟦ W₀ ⟧ᶜ (⟦ γ₀ ⟧ᴱ , z) (λ z₁ → ⟦ W₁ ⟧ᶜ (⟦ γ₁ ⟧ᴱ , z₁) k₁))) k₀) (λ z → ⟦ W₀ ⟧ᶜ (⟦ γ₀ ⟧ᴱ , z) (λ z₁ → ⟦ W₁ ⟧ᶜ (⟦ γ₁ ⟧ᴱ , z₁) k))) k₀
      ≡⟨ refl ⟩
      ⟦ (W₁ ⊲ γ₁ ⦂⦂ cs) {π = πₓ} ⟧ᶜˢ ((⟦ W₀ ⟧ᶜ ♯) (τ (⟦ γ₀ ⟧ᴱ , ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ (W₀ ⊲ γ₀ ⦂⦂ ((W₁ ⊲ γ₁ ⦂⦂ cs) {π = πₓ})) {π = wk-id} ⟧ᶜˢ (⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) k₀)))) k₀ ∎


  -- ⟦ sub M N ⟧ᶜ = < curry ⟦ M ⟧ᶜ , ⟦ N ⟧ᶜ > ； subK

  lemz : (M : (Γ ∙ `V) ⊢ᶜ X) → (N : Γ ⊢ᶜ X) → (γ : Env Γ) → (cs : CompStack Δ X) → (πₓ : Wk Γ Δ) → (wk≡ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → ⟦ sub M N ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ ≡ ⟦ M ⟧ᶜ ⟦ (γ ﹐﹝ N ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡} ⟧ᴱ ⟦ cs ⟧ᴷ
  lemz M N γ cs πₓ wk≡ =
            ⟦ sub M N ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ
         ≡⟨ refl ⟩
          ⟦ M ⟧ᶜ ( ⟦ γ ⟧ᴱ , ⟦ N ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ ) ⟦ cs ⟧ᴷ
         ≡⟨ {!refl!} ⟩
          ⟦ M ⟧ᶜ ⟦ (γ ﹐﹝ N ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡} ⟧ᴱ ⟦ cs ⟧ᴷ ∎

  lemk : (N : Γ ⊢ᶜ X) → (γ : Env Γ) → (cs : CompStack Δ X) → (πₓ : Wk Γ Δ) → (wk≡ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → (⟦ γ ⟧ᴱ , ⟦ N ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ) ≡ (⟦ (γ ﹐﹝ N ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡} ⟧ᴱ)
  lemk N γ ◻ πₓ wk≡ =  refl
  lemk N γ ((W₀ ⊲ γ₀ ⦂⦂ cs) {π = π}) πₓ wk≡ =
              (⟦ γ ⟧ᴱ , ⟦ N ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ (W₀ ⊲ γ₀ ⦂⦂ cs) {π = π} ⟧ᴷ)
             ≡⟨ {!refl!} ⟩
                ⟦ γ ⟧ᴱ , ⟦ (W₀ ⊲ γ₀ ⦂⦂ cs) {π = π} ⟧ᶜˢ (⟦ N ⟧ᶜ ⟦ γ ⟧ᴱ) k₀
             ≡⟨ refl ⟩
              ⟦ (γ ﹐﹝ N ╎ (W₀ ⊲ γ₀ ⦂⦂ cs) {π = π} ﹞) {π = πₓ} {wk≡ = wk≡} ⟧ᴱ ∎

  variable
    Δ₁ : Ctx
    X₁ : Ty

  -- ⟦_⟧ᴷ : (cs : CompStack Δ Y) → ⟦ Y ⟧ → R
  -- ⟦_⟧ᴷ cs y = ⟦ cs ⟧ᶜˢ (η y) k₀

  -- ⟦ ◻ ⟧ᶜˢ W = W
  -- ⟦ W₁ ⊲ γ₁ ⦂⦂ tail ⟧ᶜˢ W =  ⟦ tail ⟧ᶜˢ (( ⟦ W₁ ⟧ᶜ ♯)(τ (⟦ γ₁ ⟧ᴱ , W)))

  lemj : (N : Γ ⊢ᶜ X) → (γ : Env Γ) → (γ₀ : Env Δ) → (W₀ : Comp (Δ ∙ X) X₁) → (cs : CompStack Δ₁ X₁) → (π : Wk Δ Δ₁) → (πₓ : Wk Γ Δ) → (wk≡ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ γ₀ ⟧ᴱ) → ⟦ N ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ (W₀ ⊲ γ₀ ⦂⦂ cs) {π = π} ⟧ᴷ ≡ ⟦ (W₀ ⊲ γ₀ ⦂⦂ cs) {π = π} ⟧ᶜˢ (⟦ N ⟧ᶜ ⟦ γ ⟧ᴱ) k₀
  --lemj N γ γ₀ W₀ cs π πₓ wk≡ = {!!}
  lemj N γ γ₀ W₀ ◻ π πₓ wk≡ = refl
  lemj N γ γ₀ W₀ ((W₁ ⊲ γ₁ ⦂⦂ cs) {π = π₁}) π πₓ wk≡ =
      ⟦ N ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ (W₀ ⊲ γ₀ ⦂⦂ ((W₁ ⊲ γ₁ ⦂⦂ cs) {π = π₁})) {π = π} ⟧ᴷ
      ≡⟨ {!!} ⟩
       {! ⟦ (W₀ ⊲ γ₀ ⦂⦂ ((W₁ ⊲ γ₁ ⦂⦂ cs) {π = π₁})) {π = π} ⟧ᶜˢ (⟦ N ⟧ᶜ ⟦ γ ⟧ᴱ) k₀!}
      ≡⟨ {!!} ⟩
      ⟦ (W₀ ⊲ γ₀ ⦂⦂ ((W₁ ⊲ γ₁ ⦂⦂ cs) {π = π₁})) {π = π} ⟧ᶜˢ (⟦ N ⟧ᶜ ⟦ γ ⟧ᴱ) k₀ ∎

  lemi : (N : Γ ⊢ᶜ X) → (γ : Env Γ) → (γ₀ : Env Δ) → (W₀ : Comp (Δ ∙ X) X₁) → (cs : CompStack Δ₁ X₁) → (π : Wk Δ Δ₁) → (πₓ : Wk Γ Δ) → (wk≡ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ γ₀ ⟧ᴱ) → ⟦ N ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ (W₀ ⊲ γ₀ ⦂⦂ cs) {π = π} ⟧ᴷ ≡ ⟦ (W₀ ⊲ γ₀ ⦂⦂ cs) {π = π} ⟧ᶜˢ (⟦ N ⟧ᶜ ⟦ γ ⟧ᴱ) k₀
  --lemj N γ γ₀ W₀ cs π πₓ wk≡ = {!!}
  lemi N ∗ γ₀ W₀ ◻ π πₓ wk≡ = refl
  lemi N ∗ γ₀ W₀ ((W₁ ⊲ γ₁ ⦂⦂ cs) {π = π₁}) π πₓ wk≡ =
      ⟦ N ⟧ᶜ ⟦ ∗ ⟧ᴱ ⟦ (W₀ ⊲ γ₀ ⦂⦂ ((W₁ ⊲ γ₁ ⦂⦂ cs) {π = π₁})) {π = π} ⟧ᴷ
      ≡⟨ {!refl!} ⟩
      ⟦ (W₀ ⊲ γ₀ ⦂⦂ ((W₁ ⊲ γ₁ ⦂⦂ cs) {π = π₁})) {π = π} ⟧ᶜˢ (⟦ N ⟧ᶜ ⟦ ∗ ⟧ᴱ) k₀ ∎

  lemi N (γ ﹐ M) γ₀ W₀ cs π πₓ wk≡ = {!!}
  lemi N (γ ﹐﹝ W ╎ cs₁ ﹞) γ₀ W₀ cs π πₓ wk≡ = {!!}

  -- ⟦ E ﹐﹝ W ╎ cs ﹞ ⟧ᴱ = ⟦ E ⟧ᴱ , ⟦ cs ⟧ᶜˢ (⟦ W ⟧ᶜ ⟦ E ⟧ᴱ) k₀

  -- lemk N (γ ﹐ M) cs πₓ wk≡ = {!!}
  -- lemk N (γ ﹐﹝ W ╎ cs₁ ﹞) cs πₓ wk≡ = {!!}

  -- lemx : (M : (Γ ∙ `V) ⊢ᶜ X) → (N : Γ ⊢ᶜ X) → (γ : Env Γ) → (cs : CompStack Δ X) → (πₓ : Wk Γ Δ) → (wk≡ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → ⟦ sub M N ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ ≡ ⟦ M ⟧ᶜ ⟦ (γ ﹐﹝ N ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡} ⟧ᴱ ⟦ cs ⟧ᴷ
  -- lemx M N γ cs πₓ wk≡ =
  --           ⟦ sub M N ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ
  --        ≡⟨ refl ⟩
  --             ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , ⟦ N ⟧ᶜ ⟦ γ ⟧ᴱ (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
  --        ≡⟨ cong (λ x → ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , x) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (lemx' N γ cs)  ⟩
  --             ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , ⟦ cs ⟧ᶜˢ (⟦ N ⟧ᶜ ⟦ γ ⟧ᴱ) k₀)                   (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
  --        ≡⟨ refl ⟩
  --           ⟦ M ⟧ᶜ ⟦ (γ ﹐﹝ N ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡} ⟧ᴱ ⟦ cs ⟧ᴷ ∎

  --        where
  --        lemx' : (N : Comp Γ X) → (γ : Env Γ) → (cs : CompStack Δ X) → ⟦ N ⟧ᶜ ⟦ γ ⟧ᴱ (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀) ≡ ⟦ cs ⟧ᶜˢ (⟦ N ⟧ᶜ ⟦ γ ⟧ᴱ) k₀
  --        lemx' (return x) γ cs = refl
  --        lemx' (pm x N) γ cs = {!!}
  --        lemx' (push N N₁) γ cs = {!!}
  --        lemx' (app x x₁) γ cs = {!!}
  --        lemx' (var x) γ cs = {!!}
  --        lemx' (sub N N₁) γ cs = {!!}

-}

  -- ⟦ E ﹐﹝ W ╎ cs ﹞ ⟧ᴱ = ⟦ E ⟧ᴱ , ⟦ W ⟧ᶜ ⟦ E ⟧ᴱ ⟦ cs ⟧ᴷ

  -- ⟦ ◻ ⟧ᶜˢ W = W
  -- ⟦ W₁ ⊲ γ₁ ⦂⦂ tail ⟧ᶜˢ W =  ⟦ tail ⟧ᶜˢ (( ⟦ W₁ ⟧ᶜ ♯)(τ (⟦ γ₁ ⟧ᴱ , W)))

  --  (W : Γ ⊢ᶜ X) → (γ : Env Γ) → (cs : CompStack Δ Y) → (π : Wk Δ Δ₁) → (πₓ : Wk Γ Δ) → (wk≡ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ γ₀ ⟧ᴱ)
  lem2 : (W : Γ ⊢ᶜ X) → (γ : Env Γ) → (cs : CompStack Δ X) → ⟦ cs ⟧ᶜˢ ( ⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ) k₀ ≡ ⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
  lem2 W γ ◻ = refl
  lem2 W γ ((W₀ ⊲ γ₀ ⦂⦂ cs) {π = π}) =
                 ⟦ (W₀ ⊲ γ₀ ⦂⦂ cs) {π = π} ⟧ᶜˢ (⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ) k₀
              ≡⟨ refl ⟩
                  ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ (λ z → ⟦ W₀ ⟧ᶜ (⟦ γ₀ ⟧ᴱ , z) k)) k₀
              ≡⟨ {!!} ⟩
                  {!⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ (λ y → ⟦ (W₀ ⊲ γ₀ ⦂⦂ cs) {π = π} ⟧ᶜˢ (λ k → k y) k₀)!}
              ≡⟨ {!!} ⟩
                 ⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ (λ y → ⟦ (W₀ ⊲ γ₀ ⦂⦂ cs) {π = π} ⟧ᶜˢ (λ k → k y) k₀) ∎

  --lem2' : (W : Γ ⊢ᶜ X) → (γ : Env Γ) → (cs : CompStack Δ X) → ⟦ cs ⟧ᶜˢ' W γ k₀ ≡ ⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
  --lem2' = ?

  lem3 : (W : Γ ⊢ᶜ X) → (γ : Env Γ) → (cs : CompStack Δ X) → ⟦ cs ⟧ᶜˢ (⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ) k₀ ≡ ⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ
  lem3 W γ ◻ = refl
  lem3 W γ (W₀ ⊲ γ₀ ⦂⦂ cs) = {!!}
            --    ⟦ cs ⟧ᶜˢ (⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ) k₀
            -- ≡⟨ {!!} ⟩
            --    {!!}
            -- ≡⟨ {!!} ⟩
            --    {! ⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ!}
            -- ≡⟨ {!!} ⟩
            --    ⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ ∎

  {-# TERMINATING #-}
  mutual

    app-eval-rec : (M : Γ' ⊢ᵛ X `⇒ Y) → (N : V̲a̲l̲ Γ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ Y) → (πₓ : Wk Γ Δ) → (wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → (n : ℕ) → CompSteps ((∙⟨ (a̲pp (wk-val π M) N) ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})
    -- app-eval-rec (var i) N γ π cs πₓ zero = {!!} -- terminates because the total number of occurrences of "var" in the term, the environment and the stack decreases
    -- app-eval-rec (var i) N γ π cs πₓ (suc n) with lookup (wk-mem π i) γ
    app-eval-rec (var i) N γ π cs πₓ wk≡₀ n with lookup (wk-mem π i) γ
    ... | steps i>>T (found-lam {W = W} {γ = γ₁}) i≡T π₁ w≡γ with app-eval-rec (lam W) N γ π₁ cs πₓ wk≡₀ n
    ... | steps W>WT HT S≡T π' wk≡ᶜ = steps (∙⟨ a̲pp (wk-val π (var i)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-var i>>T π₁ ⟩ W>WT) HT {!!} π' {!!}
    app-eval-rec (lam W) N γ π cs πₓ wk≡₀ n with comp-eval-rec W (γ ﹐ N) (wk-cong π) cs (wk-wk πₓ) {!!} n
    ... | steps W>WT HT S≡T π' wk≡ᶜ rewrite (wk-comp-id W) = steps ( ∙⟨ a̲pp (wk-val π (lam W)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-lam ⟩ W>WT) HT {!!} (wk-trans π' (wk-wk wk-id)) {!!}
    app-eval-rec (pm M₁ N₁) N γ π cs πₓ wk≡₀ n with val-eval-rec M₁ γ π
    ... | steps {T = ∙ (⭭ pa̲i̲r̲ {X = X} {Y = Y} LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ with wk-val-trans N₁ (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
    ...       | eq with app-eval-rec N₁ ((wk-v̲a̲l̲ (wk-wk (wk-wk π')) N)) (γ₁ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS) (wk-cong (wk-cong (wk-trans π' π))) cs (wk-wk (wk-wk (wk-trans π' πₓ))) {!!} n
    ...          | steps N>NT NT S≡T π'' wk≡ᶜ rewrite (sym eq) =

        steps
         (∙⟨ (a̲pp (wk-val π (pm M₁ N₁)) N) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-pm M>T π' ⟩ N>NT )
         NT
         {!!}
         (wk-trans π'' (wk-wk (wk-wk π')))
         {!!}

    comp-eval-rec : (W : Γ' ⊢ᶜ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ X) → (πₓ : Wk Γ Δ) → (wk≡₀ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → (n : ℕ) → CompSteps ((∘⟨ wk-comp π W ⊰ γ ╎ cs ⟩) {π = πₓ} {wk≡ = wk≡₀})

    comp-eval-rec (return {A = X} M) γ π ◻ πₓ wk≡₀ n with val-eval-rec {X = X} M γ π
    -- cong η M≡T
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ = steps (∘⟨ wk-comp π (return M) ⊰ γ ╎ ◻ ⟩ →ᶜ⟨ ∘return M>T ⟩ (∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ ◻ ⟩ ◼)) ret (cong (λ x → (η x) k₀) M≡T) π' wk≡
    comp-eval-rec (return {A = X} M) γ π ((M' ⊲ γ' ⦂⦂ cs) {π = π₁}) πₓ wk≡₀ n with val-eval-rec {X = X} M γ π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ with comp-eval-rec M' (γ₁ ﹐ M₁) (wk-cong (wk-trans π' πₓ)) cs (wk-wk (wk-trans (wk-trans π' πₓ) π₁)) {!!} n
    ... | steps {T = ∙⟨ r̲e̲t̲u̲r̲n̲  M₂ ⊰ γ₂ ╎ ◻ ⟩} M'>T ret S≡T π'' wk≡ᶜ =

                   steps (∘⟨ wk-comp π (return M) ⊰ γ ╎ (M' ⊲ γ' ⦂⦂ cs) ⟩ →ᶜ⟨ ∘return {wk≡ₓ' = ⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡⟨ sym (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ) ≡⟨ cong ⟦ πₓ ⟧ʷ wk≡ ⟩ ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡⟨ wk≡₀ ⟩ ⟦ γ' ⟧ᴱ ∎} M>T ⟩ ∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ M' ⊲ γ' ⦂⦂ cs ⟩ →ᶜ⟨ ∙return {πₓ = wk-trans (wk-trans π' πₓ) π₁} {πₓ' = π₁} ⟩ M'>T)

                   ret

                   {!!}
                   -- (  ⟦ cs ⟧ᶜˢ ((⟦ M' ⟧ᶜ ♯) (τ (⟦ γ' ⟧ᴱ , ((⟦ π ⟧ʷ ； ⟦ M ⟧ᵛ) ； η) ⟦ γ ⟧ᴱ)))
                   --   ≡⟨ cong (λ x → ⟦ cs ⟧ᶜˢ ((⟦ M' ⟧ᶜ ♯) (τ (⟦ γ' ⟧ᴱ , x)))) (cong η M≡T) ⟩
                   --      ⟦ cs ⟧ᶜˢ ((⟦ M' ⟧ᶜ ♯) (τ (⟦ γ' ⟧ᴱ , η (⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ))))
                   --   ≡⟨ refl ⟩
                   --      ⟦ cs ⟧ᶜˢ ((⟦ M' ⟧ᶜ) (⟦ γ' ⟧ᴱ , (⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))
                   --   ≡⟨ cong (λ x → ⟦ cs ⟧ᶜˢ ((⟦ M' ⟧ᶜ) (x , (⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))) (sym wk≡₀)  ⟩
                   --      ⟦ cs ⟧ᶜˢ (⟦ M' ⟧ᶜ (⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
                   --   ≡⟨ cong (λ x → ⟦ cs ⟧ᶜˢ ((⟦ M' ⟧ᶜ) (⟦ πₓ ⟧ʷ x , (⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))) (sym wk≡)  ⟩
                   --     ⟦ cs ⟧ᶜˢ (⟦ M' ⟧ᶜ (⟦ πₓ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
                   --   ≡⟨ cong (λ x → ⟦ cs ⟧ᶜˢ ((⟦ M' ⟧ᶜ) (x , (⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))) (wk-sem-trans π' πₓ ⟦ γ₁ ⟧ᴱ)  ⟩
                   --       ⟦ cs ⟧ᶜˢ (⟦ M' ⟧ᶜ (⟦ wk-trans π' πₓ ⟧ʷ ⟦ γ₁ ⟧ᴱ , ⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
                   --   ≡⟨ refl ⟩
                   --       ⟦ cs ⟧ᶜˢ ((⟦ M' ⟧ᶜ ∘ < ⟦ wk-trans π' πₓ ⟧ʷ ∘ (λ r → proj₁ r)  , (λ r → proj₂ r) >) (⟦ γ₁ ⟧ᴱ , ⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
                   --   ≡⟨ refl ⟩
                   --     ⟦ cs ⟧ᶜˢ ((< (λ r → proj₁ r) ； ⟦ wk-trans π' πₓ ⟧ʷ , (λ r → proj₂ r) > ； ⟦ M' ⟧ᶜ) (⟦ γ₁ ⟧ᴱ , ⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
                   --   ≡⟨ S≡T ⟩
                   --    (⟦ toVal M₂ ⟧ᵛ ； η) ⟦ γ₂ ⟧ᴱ ∎)

                   (wk-trans π'' (wk-wk π'))

                   {!!}

-- Goal: (⟦ M' ⟧ᶜ ♯) (τ (⟦ γ' ⟧ᴱ , η (⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ))) ≡
--       (< (λ r → proj₁ r) ； ⟦ wk-trans π' πₓ ⟧ʷ , (λ r → proj₂ r) > ；
--        ⟦ M' ⟧ᶜ)
--       (⟦ γ₁ ⟧ᴱ , ⟦ toVal M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ)

    comp-eval-rec (pm {A = X} {B = Y} M W) γ π cs πₓ wk≡₀ n with val-eval-rec {X = X `× Y} M γ π
    ...  | steps {T = ∙ ((⭭_ {X = X `× Y} (pa̲i̲r̲ LHS RHS) ⊲ γ' ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ with comp-eval-rec W (γ' ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS) (wk-trans (wk-cong (wk-cong π')) (wk-cong (wk-cong π))) cs (wk-wk (wk-wk (wk-trans π' πₓ))) {!!} n
    ...   | steps W>T HT S≡T π₁ wk≡ᶜ with wk-comp-trans W (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
    ...     | eq rewrite (sym eq) = steps (∘⟨ wk-comp π (pm M W) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘pm π M>T π' ⟩ W>T) HT {!!} (wk-trans π₁ (wk-wk (wk-wk π'))) {!!}

    -- comp-eval-rec (push W V) γ π cs πₓ zero = {!!} -- terminates because the total number of occurrences of "push" in the term, the environment and the stack decreases
    -- comp-eval-rec (push W V) γ π cs πₓ (suc n) with comp-eval-rec W γ π ((wk-comp (wk-cong π) V) ⊲ γ ⦂⦂ cs) wk-id n
    comp-eval-rec (push W V) γ π cs πₓ wk≡₀ n with comp-eval-rec W γ π ((wk-comp (wk-cong π) V) ⊲ γ ⦂⦂ cs) wk-id {!!} n
    ... | steps {T = ∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ₁ ╎ ◻ ⟩} W>T ret S≡T π' wk≡ᶜ =

                steps
                  (  ∘⟨ push (wk-comp π W) (wk-comp (wk-cong π) V) ⊰ γ ╎ cs ⟩  →ᶜ⟨ ∘push ⟩ W>T )
                  ret
                  {!!}
                  π'
                  {!!}

    comp-eval-rec (app M N) γ π cs πₓ wk≡₀ n with val-eval-rec N γ π
    ... | steps {T = ∙ ((⭭_ NT ⊲ γᴺ ∷ □) {↥ = 🗆})} N>NT ∙NT N≡NT πᴺ wk≡ᴺ with app-eval-rec M NT γᴺ (wk-trans πᴺ π) cs (wk-trans πᴺ πₓ) {!!} n
    ... | steps W>WT HT S≡T πᵂ wk≡ᶜ rewrite (sym (wk-val-trans M πᴺ π)) =
            steps

                ((∘⟨ app (wk-val π M) (wk-val π N) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘app N>NT πᴺ ⟩ W>WT ))
                HT
                {!!}
                (wk-trans πᵂ πᴺ)
                {!!}

    -- comp-eval-rec (var {A = X} M) γ π cs πₓ zero = {!!} -- terminates because the total number of occurrences of "var" in the term, the environment and the stack decreases
    -- comp-eval-rec (var {A = X} M) γ π cs πₓ (suc n) with val-eval-rec {X = `V} M γ π
    comp-eval-rec (var {A = X} M) γ π cs πₓ wk≡₀ n with val-eval-rec {X = `V} M γ π
    ... | steps {T = ∙ ((⭭ v̲a̲r̲ i) ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ with lookup i γ₁
    ... | steps i>>T (found-comp {X = X} {W = W'} {γ = γ'} {cs = cs'} {π = πᶜ} {wk≡ = wk≡c}) i≡T π₂ w≡γ with comp-eval-rec W' γ₁ π₂ cs' (wk-trans π₂ πᶜ) (⟦ wk-trans π₂ πᶜ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡⟨ sym (wk-sem-trans π₂ πᶜ ⟦ γ₁ ⟧ᴱ) ⟩ ⟦ πᶜ ⟧ʷ (⟦ π₂ ⟧ʷ ⟦ γ₁ ⟧ᴱ)  ≡⟨ cong ⟦ πᶜ ⟧ʷ w≡γ ⟩ ⟦ πᶜ ⟧ʷ ⟦ γ' ⟧ᴱ ≡⟨ wk≡c ⟩ ⟦ topCsEnv cs' ⟧ᴱ ∎) n
    ... | steps {T = ∙⟨ C̲o̲m̲p.r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₂ ╎ ◻ ⟩} W>T ret S≡T π'' wk≡ᶜ =
                steps
                (∘⟨ var (wk-val π M) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘var M>T π' i>>T π₂ ⟩ W>T)
                ret

                ( ((⟦ π ⟧ʷ ； ⟦ M ⟧ᵛ) ； varK) ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ
                ≡⟨ refl ⟩
                  ⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)
                ≡⟨ M≡T ⟩
                   ⟦ i ⟧ᵐ ⟦ γ₁ ⟧ᴱ
                ≡⟨ i≡T ⟩
                   ⟦ W' ⟧ᶜ ⟦ γ' ⟧ᴱ (λ y → ⟦ cs' ⟧ᶜˢ (λ k → k y) k₀)
                ≡⟨ cong (λ x → ⟦ W' ⟧ᶜ x (λ y → ⟦ cs' ⟧ᶜˢ (λ k → k y) k₀)) (sym w≡γ) ⟩
                   ⟦ W' ⟧ᶜ (⟦ π₂ ⟧ʷ ⟦ γ₁ ⟧ᴱ) (λ y → ⟦ cs' ⟧ᶜˢ (λ k → k y) k₀)
                ≡⟨ refl ⟩
                  (⟦ π₂ ⟧ʷ ； ⟦ W' ⟧ᶜ) ⟦ γ₁ ⟧ᴱ ⟦ cs' ⟧ᴷ
                ≡⟨ S≡T ⟩
                  (⟦ toVal M₁ ⟧ᵛ ； η) ⟦ γ₂ ⟧ᴱ ⟦ ◻ ⟧ᴷ ∎)

                -- ( (⟦ cs ⟧ᶜˢ (((⟦ π ⟧ʷ ； ⟦ M ⟧ᵛ) ； varK) ⟦ γ ⟧ᴱ)) k₀
                --  ≡⟨ refl ⟩
                --  (⟦ cs ⟧ᶜˢ ((varK ∘ (⟦ M ⟧ᵛ ∘ ⟦ π ⟧ʷ)) ⟦ γ ⟧ᴱ)) k₀
                --  ≡⟨ refl ⟩
                --  (⟦ cs ⟧ᶜˢ (varK (⟦ M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)))) k₀
                --  ≡⟨ cong (λ x → (⟦ cs ⟧ᶜˢ (varK x)) k₀) M≡T ⟩
                --   (⟦ cs ⟧ᶜˢ (varK (⟦ i ⟧ᵐ ⟦ γ₁ ⟧ᴱ))) k₀
                --  ≡⟨ cong (λ x → (⟦ cs ⟧ᶜˢ (varK x)) k₀) i≡T ⟩
                --   (⟦ cs ⟧ᶜˢ (varK (⟦ cs' ⟧ᶜˢ (⟦ W' ⟧ᶜ ⟦ γ' ⟧ᴱ) k₀))) k₀
                --  ≡⟨ lem cs cs' W' γ' ⟩
                --   (⟦ cs' ⟧ᶜˢ (⟦ W' ⟧ᶜ ⟦ γ' ⟧ᴱ)) k₀
                --  ≡⟨ cong (λ x → (⟦ cs' ⟧ᶜˢ (⟦ W' ⟧ᶜ x)) k₀) (sym w≡γ) ⟩
                --    (⟦ cs' ⟧ᶜˢ (⟦ W' ⟧ᶜ (⟦ π₂ ⟧ʷ ⟦ γ₁ ⟧ᴱ))) k₀
                --  ≡⟨ refl ⟩
                --    (⟦ cs' ⟧ᶜˢ ((⟦ W' ⟧ᶜ ∘ ⟦ π₂ ⟧ʷ) ⟦ γ₁ ⟧ᴱ)) k₀
                --  ≡⟨ refl ⟩
                --    (⟦ cs' ⟧ᶜˢ ((⟦ π₂ ⟧ʷ ； ⟦ W' ⟧ᶜ) ⟦ γ₁ ⟧ᴱ)) k₀
                --  ≡⟨ S≡T ⟩
                --   ((⟦ toVal M₁ ⟧ᵛ ； η) ⟦ γ₂ ⟧ᴱ) k₀ ∎)

                (wk-trans π'' π')
                {!!}


    comp-eval-rec (sub W V) γ π cs πₓ wk≡₀ n with comp-eval-rec W ((γ ﹐﹝ wk-comp π V ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡₀}) (wk-cong π) cs (wk-wk πₓ) wk≡₀ n
    ... | steps {T = T} W>WT HT S≡T πᵂ wk≡ᶜ =
                steps
                    (∘⟨ sub (wk-comp (wk-cong π) W) (wk-comp π V) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘sub ⟩ W>WT)

                    HT

                    S≡T

                    -- (  ⟦ cs ⟧ᶜˢ ((< curry (< (λ r → proj₁ r) ； ⟦ π ⟧ʷ , (λ r → proj₂ r) > ； ⟦ W ⟧ᶜ) , ⟦ π ⟧ʷ ； ⟦ V ⟧ᶜ > ； subK) ⟦ γ ⟧ᴱ) k₀
                    --  ≡⟨ refl ⟩
                    --    ⟦ cs ⟧ᶜˢ ((subK ∘ < curry (⟦ W ⟧ᶜ ∘ < ⟦ π ⟧ʷ ∘ (λ r → proj₁ r) , (λ r → proj₂ r) >) , ⟦ V ⟧ᶜ ∘ ⟦ π ⟧ʷ >) ⟦ γ ⟧ᴱ) k₀
                    --  ≡⟨ refl ⟩
                    --    ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) k) k) k₀
                    --  ≡⟨ {!!} ⟩
                    --     (⟦ cs ⟧ᶜˢ (⟦ W ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ cs ⟧ᶜˢ (⟦ V ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)) k₀))) k₀
                    --  ≡⟨ refl ⟩
                    --     ⟦ cs ⟧ᶜˢ ((< (λ r → proj₁ r) ； ⟦ π ⟧ʷ , (λ r → proj₂ r) > ； ⟦ W ⟧ᶜ) (⟦ γ ⟧ᴱ , ⟦ cs ⟧ᶜˢ ((⟦ π ⟧ʷ ； ⟦ V ⟧ᶜ) ⟦ γ ⟧ᴱ) k₀)) k₀
                    --  ≡⟨ S≡T ⟩
                    --    ⟦ T ⟧ᶜꟴ k₀ ∎)

                    (wk-trans πᵂ (wk-wk wk-id))

                    {!!}


    -- comp-eval : (W : ε ⊢ᶜ R₀) → CompSteps ((∘⟨ wk-comp wk-id W ⊰ ∗ ╎ ◻ ⟩) {π = wk-id})
    -- comp-eval W = comp-eval-rec W ∗ wk-id ◻ wk-id 100000000
