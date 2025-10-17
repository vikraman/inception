module Inception.Sub.Examples where

open import Data.Unit

open import Inception.Sub.Syntax
open import Inception.Sub.CPS ⊤

--open import Data.Nat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)

open import Inception.Sub.ValueMachine ⟦ `Unit ⟧
open import Inception.Sub.CompMachine ⟦ `Unit ⟧

unit-id : ⟦ `Unit ⟧ → ⟦ `Unit ⟧
unit-id tt = tt

open VMain {R₀ = `Unit} unit-id
open CMain {R₀ = `Unit} unit-id

ex3 : ε ⊢ᶜ `Unit
ex3 = return (pm (pair unit unit) (var (t h)))

ex4 : ε ⊢ᶜ `Unit
ex4 = sub (var (var h)) (return (pm (pair unit unit) (var (t h))))

-- comp-eval : (W : Γ' ⊢ᶜ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ X) → (πₓ : Wk Γ Δ) → (n : ℕ) → CompSteps ((∘⟨ wk-comp π W ⊰ γ ╎ cs ⟩) {π = πₓ})

_ : comp-eval ex4 ≡ {!comp-eval ex4!}
_ = refl
