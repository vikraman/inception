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
open import Inception.Sub.VMequalities R

{-
F≡T : {from : VState T◾} → {to : VState T◾} → (F>T : from ~>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS' RHS) γ') → (⟦ from ⟧◑ ≡ ⟦ to ⟧◑)
F≡T ~∘var~> f≡L' tail = refl
F≡T ~∘lam~> f≡L' tail = refl
F≡T ~∘pair~> f≡L' tail = refl
F≡T ~∘pm~> f≡L' tail = refl
F≡T ~∘unit~> f≡L' tail = refl
F≡T (~∙var∷pm■~> γ γ' i M N ≡M) f≡L' tail = var∷pm≡N γ γ' i M N ≡M
F≡T (~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' tail₁) f≡L' tail = refl
F≡T (~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS tail₁) f≡L' tail = refl
F≡T (~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS tail₁) f≡L' tail = refl
F≡T (~∙pair∷pm■~> γ γ' x y M N ≡M) f≡L' tail = {!!}
F≡T (~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' tail₁) f≡L' tail = refl
F≡T (~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS tail₁) f≡L' tail = refl
F≡T (~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS tail₁) f≡L' tail = refl
F≡T (~∙var∷l■~> γ γ' i LHS RHS ≡LHS) f≡L' tail = {!!}
F≡T (~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = refl
F≡T (~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = refl
F≡T (~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = refl
F≡T (~∙lam∷l■~> γ γ' M LHS RHS ≡LHS) f≡L' tail = {!!}
F≡T (~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = refl
F≡T (~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = refl
F≡T (~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = refl
F≡T (~∙unit∷l■~> γ γ' LHS RHS ≡LHS) f≡L' tail = {!!}
F≡T (~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = refl
F≡T (~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = refl
F≡T (~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = refl
F≡T (~∙pair∷l■~> γ γ' x y LHS RHS ≡LHS) f≡L' tail = {!!}
F≡T (~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = refl
F≡T (~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = refl
F≡T (~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = refl
F≡T (~∙var∷r■~> γ γ' i LHS RHS ≡RHS) f≡L' tail = {!!}
F≡T (~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = refl
F≡T (~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = refl
F≡T (~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = refl
F≡T (~∙lam∷r■~> γ γ' M LHS RHS ≡RHS) f≡L' tail = {!!}
F≡T (~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = refl
F≡T (~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = refl
F≡T (~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = refl
F≡T (~∙unit∷r■~> γ γ' LHS RHS ≡RHS) f≡L' tail = {!!}
F≡T (~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = refl
F≡T (~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = refl
F≡T (~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = refl
F≡T (~∙pair∷r■~> γ γ' x y LHS RHS ≡RHS) f≡L' tail = {!!}
F≡T (~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = refl
F≡T (~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = refl
F≡T (~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = refl
-}

{-
eqdx : {from : VState T◾} → {to : VState T◾} → (F>>T : from ~>>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS' RHS) γ') → (⟦ from ⟧◑ ≡ ⟦ to ⟧◑)
eqdx (_ ~>ᵛᵛ⟨ F>T ⟩) f≡L' tail = {!!}
eqdx (_ ~>ᵛᵛ⟨ F>S ⟩ S>>T) f≡L' tail = {!!}
-}

-- ⟪_⟫::l⟨_⨾_⟩_ : {from : VState T◾} → {to : VState T◾} → (F>>T : from ~>>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (f≡t : ⟦ from ⟧◑ ≡ ⟦ to ⟧◑) → (tail : valStack T◾' (pair LHS' RHS) γ') → (from ::l⟨ f≡L' ⟩ tail) ~>>ᵛᵛ (to ::l⟨ trans (sym f≡t) f≡L' ⟩ tail)
-- 
-- ⟪ _ ~>ᵛᵛ⟨ F>S ⟩ ⟫::l⟨ f≡L' ⨾ f≡t ⟩ tail = (_ ::l⟨ _ ⟩ tail) ~>ᵛᵛ⟨ (⟨ F>S ⟩::l⟨ f≡L' ⟩ tail) ⟩
-- ⟪ _ ~>ᵛᵛ⟨ F>S ⟩ F>>T ⟫::l⟨ f≡L' ⨾ f≡t ⟩ tail = {!!}
