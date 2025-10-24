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

ex3' : ε ⊢ᶜ `Unit
ex3' = return (pm (pair unit unit) (var (t h)))

ex4' : ε ⊢ᶜ `Unit
ex4' = sub (var (var h)) (return (pm (pair unit unit) (var (t h))))

ex5' : ε ⊢ᶜ `Unit
ex5' = push (sub (push (return (var h)) (var (var h))) (return (pm (pair unit unit) (var (t h))))) (return (var h))

-- call agda2-compute-normalised in the hole below
-- _ : comp-eval ex5' ≡ {!comp-eval ex5' !}
-- _ = refl
