module Inception.Sub.VMcong (R : Set) where

open import Function.Base using (id)
open import Data.Product using (proj₁; proj₂; _,_; Σ; ∃; Σ-syntax; ∃-syntax)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; sym)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Product as P

open import Inception.Sub.ValueMachine R

{-
-- F≡*T : {from : VState T◾} → {to : VState T◾} → (F>>T : from ~>>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS' RHS) γ') → (⟦ from ⟧◑ ≡ ⟦ to ⟧◑)
-- F≡*T (_ ~>ᵛᵛ⟨ F>T ⟩) f≡L' tail = F≡T F>T f≡L' tail
-- F≡*T (_ ~>ᵛᵛ⟨ F>S ⟩ S>>T) f≡L' tail with (F≡T F>S f≡L' tail)
-- ... | F≡S =  trans F≡S (F≡*T S>>T (trans (sym F≡S) f≡L') tail)

⟪_⟫::l⟨_⟩_ : {from : VState T◾} → {to : VState T◾} → (F>>T : from ~>>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS' RHS) γ') → (from ::l⟨ f≡L' ⟩ tail) ~>>ᵛᵛ (to ::l⟨ trans (sym (F≡*T F>>T f≡L' tail)) f≡L' ⟩ tail)

⟪ _ ~>ᵛᵛ⟨ F>S ⟩ ⟫::l⟨ f≡L' ⟩ tail = (_ ::l⟨ _ ⟩ tail) ~>ᵛᵛ⟨ (⟨ F>S ⟩::l⟨ f≡L' ⟩ tail) ⟩
⟪ _ ~>ᵛᵛ⟨ F>S ⟩ F>>T ⟫::l⟨ f≡L' ⟩ tail = {!!}
-}
