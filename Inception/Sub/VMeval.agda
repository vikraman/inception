module Inception.Sub.VMeval (R : Set) where

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

-- cf PLFA
record Gas : Set where
  constructor gas
  field
    amount : ℕ


-- cf PLFA
data Finished (S : VState) : Set where

   done : haltingVState S → Finished S

   out-of-gas : Finished S


-- cf PLFA
data Steps : VState → Set where

  steps : {S S' : VState} → S ~>ᵛᵛ* S' → Finished S' → Steps S


-- cf PLFA
eval-gas : Gas → (S : VState) → Steps S
eval-gas (gas zero) S = steps (S ▣) out-of-gas
eval-gas (gas (suc amount)) S with progress S
... | done HS = steps (S ▣) (done HS)
... | step {S' = S'} (S~>S') with eval-gas (gas amount) S'
... |   steps S'~>*S'' fin = steps (S ~>ᵛᵛ⟨ S~>S' ⟩ S'~>*S'') fin


ex1 : ε ⊢ᵛ `Unit
ex1 = pm (pair unit unit) (var (t h))

_ : eval-gas (gas 100) (∘ ex1 ﹐ tt ■) ≡ steps
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
