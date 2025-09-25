module Inception.Sub.VMeval (R : Set) where

open import Function.Base using (id)
open Function.Base using (id)

open import Data.List
open import Data.Unit
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤?_; z≤n; s≤s; _+_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Inception.Sub.ValueMachine R
open import Inception.Sub.VMprogress R

-- cf PLFA
record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished (S : VState T◾) : Set where

  result : {S' : VState T◾} → (haltingVState S') → Finished S

  out-of-gas : Finished S

data Steps : (VState T◾) → Set where

  no-steps : {S : VState T◾} → haltingVState S → Steps S

  steps : {S S' : VState T◾} → S ~>>ᵛᵛ S' → Finished S' → Steps S

bounded-eval : Gas → (S : VState T◾) → Steps S
bounded-eval (gas zero) S  with progress S
... | done HS = no-steps HS
... | step {S' = S'} (S~>S') = steps (S ~>ᵛᵛ⟨ S~>S' ⟩) out-of-gas
bounded-eval (gas (suc amount)) S with progress S
... | done HS = no-steps HS
... | step {S' = S'} (S~>S') with bounded-eval (gas amount) S'
... |   no-steps HS = steps (S ~>ᵛᵛ⟨ S~>S' ⟩) (result HS)
... |   steps S'~>>S'' fin = steps (S ~>ᵛᵛ⟨ S~>S' ⟩ S'~>>S'') fin


{-
-- -- cf PLFA
-- data Finished (S : VState T◾) : Set where
-- 
--    done : haltingVState S → Finished S
-- 
--    out-of-gas : Finished S

-- cf PLFA
data Steps : VState T◾ → Set where

  --steps : {S S' : VState T◾} → S ~>ᵛᵛ* S' → Finished S' → Steps S

-- cf PLFA
bounded-eval : Gas → (S : VState T◾) → Steps S
bounded-eval (gas zero) S = steps (S ▣) out-of-gas
bounded-eval (gas (suc amount)) S with progress S
... | done HS = steps (S ▣) (done HS)
... | step {S' = S'} (S~>S') with bounded-eval (gas amount) S'
... |   steps S'~>*S'' fin = steps (S ~>ᵛᵛ⟨ S~>S' ⟩ S'~>*S'') fin
-}

calc-steps : (Γ ⊢ᵛ X) → ℕ
calc-steps (var i) = 1
calc-steps (lam x) = 1
calc-steps (pair M M') = 3 + (calc-steps M) + (calc-steps M')
calc-steps (pm M N) = 2 + (calc-steps M) + (calc-steps N)
calc-steps unit = 1

quick-eval : (M : Γ ⊢ᵛ X) → (γ : ⟦ Γ ⟧ˣ) → Steps (∘ M ﹐ γ ■)
quick-eval M γ = bounded-eval (gas (calc-steps M)) (∘ M ﹐ γ ■)

ex1 : ε ⊢ᵛ `Unit
ex1 = pm (pair unit unit) (var (t h))

ex2 : (ε ∙ (`Unit `⇒ `Unit) ∙ `Unit) ⊢ᵛ (`Unit `× (`Unit `⇒ `Unit)) `× `Unit
ex2 = pair (pair (var h) (var (t h))) (var h)

ex3 : ε ⊢ᵛ (`Unit `⇒ `Unit)
ex3 = lam (return unit)

ex4 : (ε ∙ `Unit) ⊢ᵛ `Unit `× `Unit
ex4 = pair (var h) (var h)

{-
_ : quick-eval ex2 ((tt , λ _ z → z tt) , tt) ≡ {! quick-eval ex1 tt!}
_ = refl
-}

{-
data finiteSteps : VState T◾ → Set where

  steps : {S T : VState T◾} → S ~>ᵛᵛ* T → .(⟦ S ⟧◑ ≡ ⟦ T ⟧◑) → haltingVState T → finiteSteps S

eval : (M : Γ ⊢ᵛ X) → (γ : ⟦ Γ ⟧ˣ) → finiteSteps (∘ M ﹐ γ ■)
eval (var i) γ =  steps ((∘ var i ﹐ γ ■) ~>ᵛᵛ⟨ ~∘var~> ⟩ (∙[var] var i ﹐ γ ■) ▣) refl ∙var■
eval (lam M) γ = steps ((∘ lam M ﹐ γ ■) ~>ᵛᵛ⟨ ~∘lam~> ⟩ (∙[lam] lam M ﹐ γ ■) ▣) refl ∙lam■
eval (pair LHS RHS) γ  with eval LHS γ | eval RHS γ
... | steps {T = T'} s' ≡t' t' | steps {T = T''} s'' ≡t'' t'' = steps ((∘ pair LHS RHS ﹐ γ ■) ~>ᵛᵛ⟨ ~∘pair~> ⟩ (∘ LHS ﹐ γ ∷l⟨ refl ⟩ pair LHS RHS ﹐ γ ■) ~>ᵛᵛ⟨ {!!} ⟩ {!!} ▣) {!!} ∙pair■
eval (pm M N) γ = {!!}
eval unit γ = {!!}
-}

