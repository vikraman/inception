module Inception.Sub.VMhalts (R : Set) where

open import Function.Base using (id)
open Function.Base using (id)

open import Data.List
open import Data.Unit
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Inception.Sub.ValueMachine R

data finiteSteps : VState → Set where

  steps : {S S' : VState} → S ~>ᵛᵛ* S' → haltingVState S' → finiteSteps S


{-
eval : (M : Γ ⊢ᵛ X) → (γ : ⟦ Γ ⟧ˣ) → finiteSteps (∘ M ﹐ γ ■)
eval (var i) γ = steps ((∘ var i ﹐ γ ■) ~>ᵛᵛ⟨ ~∘var~> ⟩ (∙[var] var i ﹐ γ ■) ▣) ∙var■
eval (lam M) γ = steps ((∘ lam M ﹐ γ ■) ~>ᵛᵛ⟨ ~∘lam~> ⟩ (∙[lam] lam M ﹐ γ ■) ▣) ∙lam■
eval (pair LHS RHS) γ with eval LHS γ | eval RHS γ
... | steps s' (∙var■ {γ = γ'} {i = i'}) | steps s'' ∙var■ = steps ((∘ pair LHS RHS ﹐ γ ■) ~>ᵛᵛ⟨ ~∘pair~> ⟩ {!!} ~>ᵛᵛ⟨ {!!} ⟩ {!!} ▣) ∙pair■
... | steps s' (∙var■ {γ = γ'} {i = i'}) | steps s'' ∙unit■ = {!!}
... | steps s' (∙var■ {γ = γ'} {i = i'}) | steps s'' ∙pair■ = {!!}
... | steps s' (∙var■ {γ = γ'} {i = i'}) | steps s'' ∙lam■ = {!!}
... | steps S~>*S' ∙unit■ | s = {!!}
... | steps S~>*S' ∙pair■ | s = {!!}
... | steps S~>*S' ∙lam■ | s = {!!}
eval (pm M N) γ = {!!}
eval unit γ = {!!}
-}
