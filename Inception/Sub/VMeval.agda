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


-- cf PLFA
data Finished (S : VState T◾) : Set where

   done : haltingVState S → Finished S

   out-of-gas : Finished S


-- cf PLFA
data Steps : VState T◾ → Set where

  steps : {S S' : VState T◾} → S ~>ᵛᵛ* S' → Finished S' → Steps S


-- cf PLFA
bounded-eval : Gas → (S : VState T◾) → Steps S
bounded-eval (gas zero) S = steps (S ▣) out-of-gas
bounded-eval (gas (suc amount)) S with progress S
... | done HS = steps (S ▣) (done HS)
... | step {S' = S'} (S~>S') with bounded-eval (gas amount) S'
... |   steps S'~>*S'' fin = steps (S ~>ᵛᵛ⟨ S~>S' ⟩ S'~>*S'') fin

calc-steps : (Γ ⊢ᵛ X) → ℕ
calc-steps (var i) = 2
calc-steps (lam x) = 2
calc-steps (pair M M') = 2 + (calc-steps M) + (calc-steps M')
calc-steps (pm M N) = 1 + (calc-steps M) + (calc-steps N)
calc-steps unit = 2

eval-term : (M : Γ ⊢ᵛ X) → (γ : ⟦ Γ ⟧ˣ) → Steps (∘ M ﹐ γ ■)
eval-term M γ = bounded-eval (gas (calc-steps M)) (∘ M ﹐ γ ■)

ex1 : ε ⊢ᵛ `Unit
ex1 = pm (pair unit unit) (var (t h))

_ : eval-term ex1 tt ≡ steps
      ((∘ pm (pair unit unit) (var (t h)) ﹐ tt ■) ~>ᵛᵛ⟨ ~∘pm~> ⟩
      ((∘
        pair unit unit ﹐ tt ∷pm⟨ refl ⟩
        pm (pair unit unit) (var (t h)) ﹐ tt ■)
        ~>ᵛᵛ⟨ ~∘pair~> ⟩
        ((∘
          unit ﹐ tt ∷l⟨ refl ⟩
          pair unit unit ﹐ tt ∷pm⟨ refl ⟩
          pm (pair unit unit) (var (t h)) ﹐ tt ■)
        ~>ᵛᵛ⟨ ~∘unit~> ⟩
        ((∙[unit]
          (unit ﹐ tt ∷l⟨ refl ⟩
            pair unit unit ﹐ tt ∷pm⟨ refl ⟩
            pm (pair unit unit) (var (t h)) ﹐ tt ■))
          ~>ᵛᵛ⟨
          ~∙unit∷l∷pm~> tt tt unit unit refl refl
          (pm (pair unit unit) (var (t h)) ﹐ tt ■)
          ⟩
          ((∘
            unit ﹐ tt ∷r⟨ refl ⟩
            pair (var h) unit ﹐ tt , tt ∷pm⟨ refl ⟩
            pm (pair unit unit) (var (t h)) ﹐ tt ■)
          ~>ᵛᵛ⟨ ~∘unit~> ⟩
          ((∙[unit]
            (unit ﹐ tt ∷r⟨ refl ⟩
              pair (var h) unit ﹐ tt , tt ∷pm⟨ refl ⟩
              pm (pair unit unit) (var (t h)) ﹐ tt ■))
            ~>ᵛᵛ⟨
            ~∙unit∷r∷pm~> tt (tt , tt) (var h) unit refl refl
            (pm (pair unit unit) (var (t h)) ﹐ tt ■)
            ⟩
            ((∙[pair]
              (pair (var (t h)) (var h) ﹐ (tt , tt) , tt ∷pm⟨ refl ⟩
              pm (pair unit unit) (var (t h)) ﹐ tt ■))
            ~>ᵛᵛ⟨
            ~∙pair∷pm■~> ((tt , tt) , tt) tt (var (t h)) (var h)
            (pair unit unit) (var (t h)) refl
            ⟩
            ((∘ var (t h) ﹐ (tt , tt) , tt ■) ~>ᵛᵛ⟨ ~∘var~> ⟩
              ((∙[var] (var (t h) ﹐ (tt , tt) , tt ■)) ▣)))))))))
      (done ∙var■)
_ = refl


data finiteSteps : VState T◾ → Set where

  steps : {S S' : VState T◾} → S ~>ᵛᵛ* S' → haltingVState S' → finiteSteps S

{-
⟦_⟧' : VState T◾ → ⟦ T◾ ⟧
⟦_⟧' = {!!}
-}

{-
eval : (M : Γ ⊢ᵛ X) → (γ : ⟦ Γ ⟧ˣ) → finiteSteps (∘ M ﹐ γ ■)
eval (var i) γ = steps ((∘ var i ﹐ γ ■) ~>ᵛᵛ⟨ ~∘var~> ⟩ (∙[var] var i ﹐ γ ■) ▣) ∙var■
eval (lam M) γ = steps ((∘ lam M ﹐ γ ■) ~>ᵛᵛ⟨ ~∘lam~> ⟩ (∙[lam] lam M ﹐ γ ■) ▣) ∙lam■
eval (pair LHS RHS) γ with eval LHS γ | eval RHS γ
... | steps s' (∙var■ {γ = γ'} {i = i'}) | steps s'' ∙var■ = steps ((∘ pair LHS RHS ﹐ γ ■) ~>ᵛᵛ⟨ ~∘pair~> ⟩ (∘ LHS ﹐ γ ∷l⟨ refl ⟩ pair LHS RHS ﹐ γ ■) ~>ᵛᵛ⟨ {!!} ⟩ {!!} ▣) ∙pair■
... | steps s' (∙var■ {γ = γ'} {i = i'}) | steps s'' ∙unit■ = {!!}
... | steps s' (∙var■ {γ = γ'} {i = i'}) | steps s'' ∙pair■ = {!!}
... | steps s' (∙var■ {γ = γ'} {i = i'}) | steps s'' ∙lam■ = {!!}
... | steps S~>*S' ∙unit■ | s = {!!}
... | steps S~>*S' ∙pair■ | s = {!!}
... | steps S~>*S' ∙lam■ | s = {!!}
eval (pm M N) γ = {!!}
eval unit γ = {!!}
-}
