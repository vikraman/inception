{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Semantics (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)
open Eq.≡-Reasoning using (step-≡-⟩; step-≡-∣; step-≡-⟨; _∎; step-≡)

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R
open import Inception.Sub.Equality

open import Inception.Sub.EnvironmentsP
open import Inception.Sub.StatesP
open import Inception.Sub.MachineP

open import Function.Base using (const; _∘_; _$_)
open import Data.Unit

module TL {R₀ : Ty} (k₀ : ⟦ R₀ ⟧ → R) where

  mutual
    ⟦_⟧ᴱ : (E : Env Γ R₀) → ⟦ Γ ⟧ˣ
    ⟦ ∗ ⟧ᴱ = tt
    ⟦ E ﹐ M ⟧ᴱ = ⟦ E ⟧ᴱ , ⟦ toVal M ⟧ᵛ ⟦ E ⟧ᴱ
    ⟦ E ﹐﹝ W ╎ cs ﹞ ⟧ᴱ = ⟦ E ⟧ᴱ , ⟦ W ⟧ᶜ ⟦ E ⟧ᴱ ⟦ cs ⟧ᴷ

    ⟦_⟧ᶜˢ : (cs : CompStack Δ X R₀) → K ⟦ X ⟧ → K ⟦ R₀ ⟧
    ⟦ ◻ ⟧ᶜˢ = idf
    ⟦ W₁ ⊲ γ₁ ⦂⦂ tail ⟧ᶜˢ = < const ⟦ γ₁ ⟧ᴱ , idf > ； τ ； (⟦ W₁ ⟧ᶜ ♯) ； ⟦ tail ⟧ᶜˢ

    ⟦_⟧ᴷ : (cs : CompStack Δ Y R₀) → ⟦ Y ⟧ → R
    ⟦_⟧ᴷ cs y = ⟦ cs ⟧ᶜˢ (η y) k₀

  ⟦_⟧ᴸ : (S : LookupState X R₀) → ⟦ X ⟧
  ⟦ ⟨ i ∥ E ⟩ ⟧ᴸ = ⟦ i ⟧ᵐ ⟦ E ⟧ᴱ

  ⟦_⟧ᵛˢ : (S : ValStack non-empty T◾ R₀) → ⟦ T◾ ⟧
  ⟦ (⭭ x ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ toVal x ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⇡ M ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ M ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⇡ᴹ M N ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ pm M N ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⇡ᴸ LHS RHS ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ pair LHS RHS ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⇡ᴿ LHS RHS ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ pair (toVal LHS) RHS ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⭭ x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ
  ⟦ (⇡ M ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ
  ⟦ (⇡ᴹ M N ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ
  ⟦ (⇡ᴸ LHS RHS ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ
  ⟦ (⇡ᴿ LHS RHS ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ

  ⟦_⟧ᵛꟴ : (S : ValState T◾ R₀) → ⟦ T◾ ⟧
  ⟦ ∘ tail ⟧ᵛꟴ = ⟦ tail ⟧ᵛˢ
  ⟦ ∙ tail ⟧ᵛꟴ = ⟦ tail ⟧ᵛˢ

  ⟦_⟧ᶜꟴ : CompState R₀ → R
  ⟦ ∘⟨ W ⊰ γ ╎ cs ⟩ ⟧ᶜꟴ = ⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ
  ⟦ ∙⟨ W ⊰ γ ╎ cs ⟩ ⟧ᶜꟴ = ⟦ toComp W ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ

  -- SEMANTIC LEMMAS

  env-eq-sem-lemma : {π : Wk Γ' Γ} {γ' : Env Γ' R₀} {γ : Env Γ R₀} → (ϖ : EnvEq π γ' γ) → ⟦ π ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ γ ⟧ᴱ
  env-eq-sem-lemma {π = wk-ε} {γ' = ∗} {γ = ∗} wk-env-ε = refl
  env-eq-sem-lemma {π = wk-cong π} {γ' = γ' ﹐ M'} {γ = γ ﹐ M} (wk-env-val-cong M₀ ϖ) =
        ⟦ wk-cong π ⟧ʷ (⟦ γ' ⟧ᴱ , ⟦ toVal (wk-v̲a̲l̲ π M) ⟧ᵛ ⟦ γ' ⟧ᴱ)
      ≡⟨ refl ⟩
        ⟦ π ⟧ʷ ⟦ γ' ⟧ᴱ , ⟦ toVal (wk-v̲a̲l̲ π M) ⟧ᵛ ⟦ γ' ⟧ᴱ
      ≡⟨ cong (λ x → ⟦ π ⟧ʷ ⟦ γ' ⟧ᴱ , ⟦ x ⟧ᵛ ⟦ γ' ⟧ᴱ) (sym (wk-comm {M = M} {π = π})) ⟩
        ⟦ π ⟧ʷ ⟦ γ' ⟧ᴱ , ⟦ wk-val π (toVal M) ⟧ᵛ ⟦ γ' ⟧ᴱ
      ≡⟨ refl ⟩
        ⟦ π ⟧ʷ ⟦ γ' ⟧ᴱ , ⟦ toVal M ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ' ⟧ᴱ)
      ≡⟨ cong (λ x → x , ⟦ toVal M ⟧ᵛ x) (env-eq-sem-lemma ϖ) ⟩
        (⟦ γ ⟧ᴱ , ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ) ∎
  env-eq-sem-lemma {π = wk-cong π} {γ' = γ' ﹐ M} {γ = γ ﹐﹝ W ╎ cs ﹞} ()
  env-eq-sem-lemma {π = wk-cong π} {γ' = γ' ﹐﹝ W ╎ cs ﹞} {γ = γ ﹐ M} ()
  env-eq-sem-lemma {π = wk-cong π} {γ' = γ' ﹐﹝ W ╎ cs ﹞} {γ = γ ﹐﹝ W₁ ╎ cs₁ ﹞} (wk-env-comp-cong W₂ cs₂ ϖ) =
        ⟦ wk-cong π ⟧ʷ (⟦ γ' ⟧ᴱ , (⟦ π ⟧ʷ ； ⟦ W₁ ⟧ᶜ) ⟦ γ' ⟧ᴱ ⟦ cs ⟧ᴷ)
      ≡⟨ refl ⟩
        ⟦ π ⟧ʷ ⟦ γ' ⟧ᴱ , ⟦ W₁ ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ' ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
      ≡⟨ cong (λ x → x , ⟦ W₁ ⟧ᶜ x (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) (env-eq-sem-lemma ϖ) ⟩
        ⟦ γ ⟧ᴱ , ⟦ W₁ ⟧ᶜ ⟦ γ ⟧ᴱ (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
      ≡⟨ refl ⟩
        (⟦ γ ⟧ᴱ , ⟦ W₁ ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ) ∎
  env-eq-sem-lemma {π = wk-wk π} {γ' = γ' ﹐ M} {γ = ∗} (wk-env-val-wk M₁ ϖ) = env-eq-sem-lemma ϖ
  env-eq-sem-lemma {π = wk-wk π} {γ' = γ' ﹐ M} {γ = γ ﹐ M₁} (wk-env-val-wk M₂ ϖ) = env-eq-sem-lemma ϖ
  env-eq-sem-lemma {π = wk-wk π} {γ' = γ' ﹐ M} {γ = γ ﹐﹝ W ╎ cs ﹞} (wk-env-val-wk M₁ ϖ) = env-eq-sem-lemma ϖ
  env-eq-sem-lemma {π = wk-wk π} {γ' = γ' ﹐﹝ W ╎ cs ﹞} {γ = ∗} (wk-env-comp-wk W₁ cs₁ ϖ) = env-eq-sem-lemma ϖ
  env-eq-sem-lemma {π = wk-wk π} {γ' = γ' ﹐﹝ W ╎ cs ﹞} {γ = γ ﹐ M} (wk-env-comp-wk W₁ cs₁ ϖ) = env-eq-sem-lemma ϖ
  env-eq-sem-lemma {π = wk-wk π} {γ' = γ' ﹐﹝ W ╎ cs ﹞} {γ = γ ﹐﹝ W₁ ╎ cs₁ ﹞} (wk-env-comp-wk W₂ cs₂ ϖ) = env-eq-sem-lemma ϖ


  env-eq-cs-sem-lemma : {π : Wk Γ Δ} {γ : Env Γ R₀} {cs : CompStack Δ X R₀} → EnvEq π γ (topCsEnv cs) → ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ
  env-eq-cs-sem-lemma {π = π} {γ = γ} {cs = cs} ϖ = env-eq-sem-lemma ϖ


  enveq-eq : {π : Wk Γ Γ'} {γ : Env Γ R₀} {γ' : Env Γ' R₀} → EnvEq π γ γ' → ⟦ γ' ⟧ᴱ ≡ ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ
  enveq-eq {π = wk-ε} {γ = ∗} {γ' = ∗} wk-env-ε = refl
  enveq-eq {π = wk-cong π} {γ = γ ﹐ M} {γ' = γ' ﹐ M₁} (wk-env-val-cong M₂ ϖ) =
                let
                  IH = enveq-eq ϖ
                in
                  ⟦ γ' ⟧ᴱ , ⟦ toVal M₁ ⟧ᵛ ⟦ γ' ⟧ᴱ
                ≡⟨ cong (λ x → x , ⟦ toVal M₁ ⟧ᵛ x) IH ⟩
                  ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal M₁ ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)
                ≡⟨ cong (λ x → ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ) (wk-comm {M = M₁} {π = π}) ⟩
                ⟦ wk-cong π ⟧ʷ (⟦ γ ⟧ᴱ , ⟦ toVal (wk-v̲a̲l̲ π M₁) ⟧ᵛ ⟦ γ ⟧ᴱ) ∎
  enveq-eq {π = wk-cong π} {γ = γ ﹐ M} {γ' = γ' ﹐﹝ W ╎ cs ﹞} ()
  enveq-eq {π = wk-cong π} {γ = γ ﹐﹝ W ╎ cs ﹞} {γ' = γ' ﹐ M} ()
  enveq-eq {π = wk-cong π} {γ = γ ﹐﹝ W ╎ cs ﹞} {γ' = γ' ﹐﹝ W₁ ╎ cs₁ ﹞} (wk-env-comp-cong W₂ cs₂ ϖ) =
                let
                  IH = enveq-eq ϖ
                in
                  (⟦ γ' ⟧ᴱ , ⟦ W₁ ⟧ᶜ ⟦ γ' ⟧ᴱ (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀))
                ≡⟨ cong (λ x → x , ⟦ W₁ ⟧ᶜ x (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) IH ⟩
                  (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ W₁ ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) ∎
  enveq-eq {π = wk-wk π} {γ = γ ﹐ M} {γ' = ∗} (wk-env-val-wk M₁ ϖ) = enveq-eq ϖ
  enveq-eq {π = wk-wk π} {γ = γ ﹐ M} {γ' = γ' ﹐ M₁} (wk-env-val-wk M₂ ϖ) = enveq-eq ϖ
  enveq-eq {π = wk-wk π} {γ = γ ﹐ M} {γ' = γ' ﹐﹝ W ╎ cs ﹞} (wk-env-val-wk M₁ ϖ) = enveq-eq ϖ
  enveq-eq {π = wk-wk π} {γ = γ ﹐﹝ W ╎ cs ﹞} {γ' = ∗} (wk-env-comp-wk W₁ cs₁ ϖ) = enveq-eq ϖ
  enveq-eq {π = wk-wk π} {γ = γ ﹐﹝ W ╎ cs ﹞} {γ' = γ' ﹐ M} (wk-env-comp-wk W₁ cs₁ ϖ) = enveq-eq ϖ
  enveq-eq {π = wk-wk π} {γ = γ ﹐﹝ W ╎ cs ﹞} {γ' = γ' ﹐﹝ W₁ ╎ cs₁ ﹞} (wk-env-comp-wk W₂ cs₂ ϖ) = enveq-eq ϖ

  lem0 : (cs : CompStack Δ X R₀) → (MM : K ⟦ X ⟧) → ⟦ cs ⟧ᶜˢ (λ k → MM k) k₀ ≡ MM (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
  lem0 ◻ MM = refl
  lem0 {X = X} ((W ⊲ γ ⦂⦂ cs) {π = π} {ϖ = ϖ}) MM =           ⟦ (W ⊲ γ ⦂⦂ cs) {π = π} {ϖ = ϖ} ⟧ᶜˢ MM k₀
                                    ≡⟨ refl ⟩
                                      ⟦ cs ⟧ᶜˢ (λ k → (λ x → MM (λ z → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) x)) k) k₀
                                    ≡⟨ lem0 cs (λ x → MM (λ z → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) x)) ⟩
                                      (λ x → MM (λ z → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) x)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                                    ≡⟨ refl ⟩
                                      MM (λ z →       ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)            )
                                    ≡⟨ cong MM lem0'' ⟩
                                      MM (λ z →       ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) k) k₀                      )
                                    ≡⟨ refl ⟩
                                      MM (λ y → ⟦ (W ⊲ γ ⦂⦂ cs) {π = π} {ϖ = ϖ} ⟧ᶜˢ (λ k → k y) k₀) ∎

                                    where
                                      lem0' : (z : ⟦ X ⟧) → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀) ≡ ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) k) k₀
                                      lem0' z = sym (lem0 cs (⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z)))

                                      lem0'' : (λ z → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) ≡ (λ z → ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) k) k₀)
                                      lem0'' = extensionality lem0'

  lstate-eq : {L L' : LookupState X R₀} → L →ᴸ L' → ⟦ L ⟧ᴸ ≡ ⟦ L' ⟧ᴸ
  lstate-eq {L = L} {L' = L'} val-h-step = refl
  lstate-eq {L = L} {L' = L'} val-t-step = refl
  lstate-eq {L = L} {L' = L'} comp-t-step = refl

  lstate-eq* : {L L' : LookupState X R₀} → L →ᴸ* L' → ⟦ L ⟧ᴸ ≡ ⟦ L' ⟧ᴸ
  lstate-eq* {L = L} {L' = L'} (L ◼) = refl
  lstate-eq* {L = L} {L' = L'} (L →ᴸ⟨ L→L' ⟩ L'→L'') =
              let
                IH0 = lstate-eq L→L'
                IH1 = lstate-eq* L'→L''
              in
              trans IH0 IH1

  ------------------------------------------------------------------
  {-
  open Traversal

  traverse-eq : {Γ₁' : Ctx} → (π : Wk Γ Γ')
              → (M' : Val Γ₁' X) → (γ' : Env Γ' R₀) → (π₁ : Wk Γ' Γ₁')
              →  (M : V̲a̲l̲ Γ X) → (γ : Env Γ R₀)
              → (ϖ : EnvEq π γ γ')
              → traverseᵛ M' π₁ γ' ≡ record { Γₘₐₓ = Γ ; γₘₐₓ = γ ; πₘₐₓ = π ; ϖₘₐₓ = ϖ ; result = M }
              → (⟦ M' ⟧ᵛ (⟦ π₁ ⟧ʷ ⟦ γ' ⟧ᴱ) ≡ ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ)
  traverse-eq π (var i) γ' M π₁ γ ϖ refl = {!!}
  traverse-eq π (lam x) γ' M π₁ γ ϖ refl = refl
  traverse-eq π (pair M₁' M₂') π₁ γ' (pa̲i̲r̲ M₁ M₂) γ ϖ refl =
      let
        eq₂ : traverseᵛ M₂' (wk-trans (πₘₐₓ (traverseᵛ M₁' γ' π₁)) γ') (γₘₐₓ (traverseᵛ M₁' γ' π₁)) ≡ record { Γₘₐₓ = _ ; γₘₐₓ = _ ; πₘₐₓ = _ ; ϖₘₐₓ = _ ; result = result (traverseᵛ M₂' (wk-trans (πₘₐₓ (traverseᵛ M₁' γ' π₁)) γ') (γₘₐₓ (traverseᵛ M₁' γ' π₁))) }
        eq₂ = refl
        IH₂ = traverse-eq (πₘₐₓ (traverseᵛ M₂' (wk-trans (πₘₐₓ (traverseᵛ M₁' γ' π₁)) γ') (γₘₐₓ (traverseᵛ M₁' γ' π₁)))) M₂' (γₘₐₓ (traverseᵛ M₁' γ' π₁)) (wk-trans (πₘₐₓ (traverseᵛ M₁' γ' π₁)) γ') (result (traverseᵛ M₂' (wk-trans (πₘₐₓ (traverseᵛ M₁' γ' π₁)) γ') (γₘₐₓ (traverseᵛ M₁' γ' π₁)))) (γₘₐₓ (traverseᵛ M₂' (wk-trans (πₘₐₓ (traverseᵛ M₁' γ' π₁)) γ') (γₘₐₓ (traverseᵛ M₁' γ' π₁)))) (ϖₘₐₓ (traverseᵛ M₂' (wk-trans (πₘₐₓ (traverseᵛ M₁' γ' π₁)) γ') (γₘₐₓ (traverseᵛ M₁' γ' π₁)))) eq₂
      in
        ⟦ pair M₁' M₂' ⟧ᵛ (⟦ γ' ⟧ʷ ⟦ π₁ ⟧ᴱ)
      ≡⟨ refl ⟩
        ⟦ M₁' ⟧ᵛ (⟦ γ' ⟧ʷ ⟦ π₁ ⟧ᴱ) , ⟦ M₂' ⟧ᵛ (⟦ γ' ⟧ʷ ⟦ π₁ ⟧ᴱ)
      ≡⟨ {!!} ⟩
        {!!}
      ≡⟨ {!!} ⟩
        ⟦ pair (toVal (wk-v̲a̲l̲ (πₘₐₓ (traverseᵛ M₂' (wk-trans (πₘₐₓ (traverseᵛ M₁' γ' π₁)) γ') (γₘₐₓ (traverseᵛ M₁' γ' π₁)))) (result (traverseᵛ M₁' γ' π₁)))) (toVal (result (traverseᵛ M₂' (wk-trans (πₘₐₓ (traverseᵛ M₁' γ' π₁)) γ') (γₘₐₓ (traverseᵛ M₁' γ' π₁))))) ⟧ᵛ
         ⟦ γₘₐₓ (traverseᵛ M₂' (wk-trans (πₘₐₓ (traverseᵛ M₁' γ' π₁)) γ') (γₘₐₓ (traverseᵛ M₁' γ' π₁)))⟧ᴱ
      ≡⟨ refl ⟩
        ⟦ toVal (pa̲i̲r̲ (wk-v̲a̲l̲ (πₘₐₓ (traverseᵛ M₂' (wk-trans (πₘₐₓ (traverseᵛ M₁' γ' π₁)) γ') (γₘₐₓ (traverseᵛ M₁' γ' π₁)))) (result (traverseᵛ M₁' γ' π₁))) (result (traverseᵛ M₂' (wk-trans (πₘₐₓ (traverseᵛ M₁' γ' π₁)) γ') (γₘₐₓ (traverseᵛ M₁' γ' π₁))))) ⟧ᵛ
         ⟦ γₘₐₓ (traverseᵛ M₂' (wk-trans (πₘₐₓ (traverseᵛ M₁' γ' π₁)) γ') (γₘₐₓ (traverseᵛ M₁' γ' π₁)))⟧ᴱ ∎
  traverse-eq π (pm M' M'') π₁ γ' M γ ϖ refl = {!!}
  traverse-eq π unit π₁ γ' M γ ϖ refl = refl
  -}

  mutual
    valstate-trans-eq : {S S' : ValState X R₀} → S ↠ᵛ S' → ⟦ S ⟧ᵛꟴ ≡ ⟦ S' ⟧ᵛꟴ
    valstate-trans-eq (S →ᵛ⟨ S→ᵛS' ⟩．) = valstate-eq S→ᵛS'
    valstate-trans-eq (S →ᵛ⟨ S→ᵛS' ⟩ S'↠ᵛS'') = trans (valstate-eq S→ᵛS') (valstate-trans-eq S'↠ᵛS'')

    valstate-eq : {S S' : ValState X R₀} → S →ᵛ S' → ⟦ S ⟧ᵛꟴ ≡ ⟦ S' ⟧ᵛꟴ
    valstate-eq {S = S} {S' = S'} (∘var-c {tail = □} {↥ = 🗆}) = refl
    valstate-eq {S = S} {S' = S'} (∘var-c {tail = (x ⊲ γ ∷ tail) {↥ = ↥}} {↥ = 🗇}) = refl
    valstate-eq {S = S} {S' = S'} (∘var {γ = γ} {γ' = γ'} {i = i} {tail = □} {↥ = 🗆} {M = M} i>>T πᵥ x x₁ ϖ x₃) =
                let
                  IH0 = lstate-eq* i>>T
                  eq : ⟦ γ' ⟧ᴱ ≡ ⟦ πᵥ ⟧ʷ ⟦ γ ⟧ᴱ
                  eq = enveq-eq ϖ
                in
                  ⟦ ∘ ((⇡ var i ⊲ γ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ
                ≡⟨ refl ⟩
                    ⟦ i ⟧ᵐ ⟦ γ ⟧ᴱ
                ≡⟨ IH0 ⟩
                    ⟦ toVal M ⟧ᵛ ⟦ γ' ⟧ᴱ
                ≡⟨ cong ⟦ toVal M ⟧ᵛ eq ⟩
                  ⟦ toVal M ⟧ᵛ (⟦ πᵥ ⟧ʷ ⟦ γ ⟧ᴱ)
                ≡⟨ cong (λ x → ⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ) (wk-comm {M = M} {π = πᵥ}) ⟩
                  ⟦ ∙ ((⭭ wk-v̲a̲l̲ πᵥ M ⊲ γ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ∎
    valstate-eq {S = S} {S' = S'} (∘var {γ = γ} {γ' = γ'} {i = i} {tail = ((M'' ⊲ γ'' ∷ tail) {↥ = ↥})} {↥ = 🗇} {M = M} i>>T πᵥ x x₁ ϖ x₃) =
                  ⟦ ∘ ((⇡ var i ⊲ γ ∷ ((M'' ⊲ γ'' ∷ tail) {↥ = ↥})) {↥ = 🗇}) ⟧ᵛꟴ
                ≡⟨ refl ⟩
                  ⟦ ∙ ((⭭ wk-v̲a̲l̲ πᵥ M ⊲ γ ∷ ((M'' ⊲ γ'' ∷ tail) {↥ = ↥})) {↥ = 🗇}) ⟧ᵛꟴ ∎

    valstate-eq {S = S} {S' = S'} (∘lam {M = W} {γ = γ} {tail = □} {↥ = 🗆}) = refl
    valstate-eq {S = S} {S' = S'} (∘lam {M = W} {γ = γ} {tail = x ⊲ γ₁ ∷ tail} {↥ = 🗇}) = refl

    valstate-eq {S = S} {S' = S'} (∘pair {tail = □} {↥ = 🗆}) = refl
    valstate-eq {S = S} {S' = S'} (∘pair {tail = x ⊲ γ ∷ tail} {↥ = 🗇}) = refl

    valstate-eq {S = S} {S' = S'} (∘pm {tail = □} {↥ = 🗆}) = refl
    valstate-eq {S = S} {S' = S'} (∘pm {tail = x ⊲ γ ∷ tail} {↥ = 🗇}) = refl

    valstate-eq {S = S} {S' = S'} (∘unit {tail = □} {↥ = 🗆}) = refl
    valstate-eq {S = S} {S' = S'} (∘unit {tail = x ⊲ γ ∷ tail} {↥ = 🗇}) = refl

    valstate-eq {S = S} {S' = S'} (∙M∷l {γ' = γ'} {γ = γ} {M = M} {LHS = LHS} {RHS = RHS} {π' = π'} {tail = □} {↥ = 🗆} ϖ LHS→M) =
                  ⟦ ∙ ((⭭ M ⊲ γ ∷ ((⇡ᴸ LHS RHS ⊲ γ' ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ
                ≡⟨ refl ⟩
                  ⟦ LHS ⟧ᵛ ⟦ γ' ⟧ᴱ , ⟦ RHS ⟧ᵛ ⟦ γ' ⟧ᴱ
                ≡⟨ cong₂ (λ x y → x , ⟦ RHS ⟧ᵛ y) (valstate-trans-eq LHS→M) (enveq-eq ϖ) ⟩
                  ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ)
                ≡⟨ refl ⟩
                  ⟦ ∘ ((⇡ wk-val π' RHS ⊲ γ ∷ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ ∎
    valstate-eq {S = S} {S' = S'} (∙M∷l {tail = x ⊲ γ ∷ tail} {↥ = 🗇} ϖ LHS→M) = refl

    valstate-eq {S = S} {S' = S'} (∙M∷r {γ' = γ'} {γ = γ} {M = M} {LHS = LHS} {RHS = RHS} {π' = π'} {tail = □} {↥ = 🗆} ϖ RHS→M) =
                  ⟦ ∙ ((⭭ M ⊲ γ ∷ ((⇡ᴿ LHS RHS ⊲ γ' ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ
                ≡⟨ refl ⟩
                  ⟦ toVal LHS ⟧ᵛ ⟦ γ' ⟧ᴱ , ⟦ RHS ⟧ᵛ ⟦ γ' ⟧ᴱ
                ≡⟨ cong₂ (λ x y → ⟦ toVal LHS ⟧ᵛ x , y) (enveq-eq ϖ) (valstate-trans-eq RHS→M) ⟩
                  ⟦ toVal LHS ⟧ᵛ (⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ
                ≡⟨ cong (λ x → ⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ) (wk-comm {M = LHS} {π = π'}) ⟩
                  ⟦ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M ⊲ γ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ∎
    valstate-eq {S = S} {S' = S'} (∙M∷r {tail = x ⊲ γ ∷ tail} {↥ = 🗇} ϖ RHS→M) = refl

    valstate-eq {S = S} {S' = S'} (∙pair∷pm {γ' = γ'} {γ = γ} {LHS = LHS} {RHS = RHS} {M = M} {N = N} {π' = π'} {tail = □} {↥ = 🗆} ϖ M→P) =
                  ⟦ ∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ ∷ ((⇡ᴹ M N ⊲ γ' ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ
                ≡⟨ refl ⟩
                  ⟦ N ⟧ᵛ ((⟦ γ' ⟧ᴱ , proj₁ (⟦ M ⟧ᵛ ⟦ γ' ⟧ᴱ)) , proj₂ (⟦ M ⟧ᵛ ⟦ γ' ⟧ᴱ))
                ≡⟨ cong ⟦ N ⟧ᵛ (cong₂ _,_ (cong₂ _,_ (enveq-eq ϖ) (cong proj₁ (valstate-trans-eq M→P))) (cong proj₂ (valstate-trans-eq M→P))) ⟩
                  ⟦ N ⟧ᵛ ((⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ)
                ≡⟨ refl  ⟩
                  ⟦ N ⟧ᵛ ((⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ wk-val (wk-wk wk-id) (toVal RHS) ⟧ᵛ (⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ))
                ≡⟨ cong (λ x → ⟦ N ⟧ᵛ ((⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ x ⟧ᵛ (⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ))) (wk-comm {M = RHS} {π = wk-wk wk-id}) ⟩
                  ⟦ N ⟧ᵛ ((⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ))
                ≡⟨ refl ⟩
                  ⟦ ∘ ((⇡ wk-val (wk-cong (wk-cong π')) N ⊲ γ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ∎
    valstate-eq {S = S} {S' = S'} (∙pair∷pm {tail = x ⊲ γ ∷ tail} {↥ = 🗇} _ _) = refl
