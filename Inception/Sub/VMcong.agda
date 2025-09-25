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

⟪_⟫::l⟨_⨾_⟩_ : {from : VState T◾} → {to : VState T◾} → (F>>T : from ~>>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (f≡t : ⟦ from ⟧◑ ≡ ⟦ to ⟧◑) → (tail : valStack T◾' (pair LHS' RHS) γ') → (from ::l⟨ f≡L' ⟩ tail) ~>>ᵛᵛ (to ::l⟨ trans (sym f≡t) f≡L' ⟩ tail)

⟪ F>>T ⟫::l⟨ f≡L' ⨾ f≡t ⟩ tail = {!!}

--⟪ .(∙[var] (var i ﹐ γ ∷pm⟨ _ ⟩ pm M N ﹐ γ' ■)) ~>ᵛᵛ⟨ ~∙var∷pm■~> γ γ' i M N ≡M ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (_ ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙var∷pm■~> γ γ' i M N ≡M ⟩::l⟨ {!!} ⨾ {! trans (sym (var∷pm≡N γ γ' i M N ≡M)) f≡L'!} ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ {!!} ⨾ t≡L' ⟩ tail)

{-
⟪ .(_) ~>ᵛᵛ⟨ F>T ⟩ ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail =  (_ ::l⟨ _ ⟩ tail) ~>ᵛᵛ⟨ (⟨ F>T ⟩::l⟨ f≡L' ⨾ t≡L' ⟩ tail) ⟩
⟪ .(∘ _)  ~>ᵛᵛ⟨ ~∘var~> ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (_ ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∘var~> ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ .(∘ _) ~>ᵛᵛ⟨ ~∘lam~> ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (_ ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∘lam~> ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ .(∘ _) ~>ᵛᵛ⟨ ~∘pair~> ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (_ ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∘pair~> ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ .(∘ _) ~>ᵛᵛ⟨ ~∘pm~> ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (_ ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∘pm~> ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ .(∘ _) ~>ᵛᵛ⟨ ~∘unit~> ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (_ ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∘unit~> ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)

⟪ .(∙[var] (var i ﹐ γ ∷pm⟨ _ ⟩ pm M N ﹐ γ' ∷pm⟨ _ ⟩ tail₁)) ~>ᵛᵛ⟨ ~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (_ ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ from ~>ᵛᵛ⟨ ~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ .(∙[var] (var i ﹐ γ ∷pm⟨ _ ⟩ pm M N ﹐ γ' ∷r⟨ _ ⟩ tail₁)) ~>ᵛᵛ⟨ ~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (_ ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)

⟪ .(∙[pair] (pair x y ﹐ γ ∷pm⟨ _ ⟩ pm M N ﹐ γ' ■)) ~>ᵛᵛ⟨ ~∙pair∷pm■~> γ γ' x y M N ≡M ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = {!!}

⟪ .(∙[pair] (pair x y ﹐ γ ∷pm⟨ _ ⟩ pm M N ﹐ γ' ∷pm⟨ _ ⟩ tail₁)) ~>ᵛᵛ⟨ ~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (_ ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ from ~>ᵛᵛ⟨ ~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ .(∙[pair] (pair x y ﹐ γ ∷pm⟨ _ ⟩ pm M N ﹐ γ' ∷r⟨ _ ⟩ tail₁)) ~>ᵛᵛ⟨ ~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (_ ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)

⟪ .(∙[var] (var i ﹐ γ ∷l⟨ _ ⟩ pair LHS RHS ﹐ γ' ■)) ~>ᵛᵛ⟨ ~∙var∷l■~> γ γ' i LHS RHS ≡LHS ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = {!!}

⟪ from ~>ᵛᵛ⟨ ~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ from ~>ᵛᵛ⟨ ~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ from ~>ᵛᵛ⟨ ~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)

⟪ .(∙[lam] (lam M ﹐ γ ∷l⟨ _ ⟩ pair LHS RHS ﹐ γ' ■)) ~>ᵛᵛ⟨ ~∙lam∷l■~> γ γ' M LHS RHS ≡LHS ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = {!!}

⟪ from ~>ᵛᵛ⟨ ~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ from ~>ᵛᵛ⟨ ~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ from ~>ᵛᵛ⟨ ~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)

⟪ .(∙[unit] (unit ﹐ γ ∷l⟨ _ ⟩ pair LHS RHS ﹐ γ' ■)) ~>ᵛᵛ⟨ ~∙unit∷l■~> γ γ' LHS RHS ≡LHS ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = {!!}

⟪ from ~>ᵛᵛ⟨ ~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ from ~>ᵛᵛ⟨ ~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ from ~>ᵛᵛ⟨ ~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)

⟪ .(∙[pair] (pair x y ﹐ γ ∷l⟨ _ ⟩ pair LHS RHS ﹐ γ' ■)) ~>ᵛᵛ⟨ ~∙pair∷l■~> γ γ' x y LHS RHS ≡LHS ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = {!!}

⟪ from ~>ᵛᵛ⟨ ~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ from ~>ᵛᵛ⟨ ~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ from ~>ᵛᵛ⟨ ~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)

⟪ .(∙[var] (var i ﹐ γ ∷r⟨ _ ⟩ pair LHS RHS ﹐ γ' ■)) ~>ᵛᵛ⟨ ~∙var∷r■~> γ γ' i LHS RHS ≡RHS ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = {!!}

⟪ .(∙[var] (var i ﹐ γ ∷r⟨ _ ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ _ ⟩ tail₁)) ~>ᵛᵛ⟨ ~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (_ ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ from ~>ᵛᵛ⟨ ~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ .(∙[var] (var i ﹐ γ ∷r⟨ _ ⟩ pair LHS RHS ﹐ γ' ∷r⟨ _ ⟩ tail₁)) ~>ᵛᵛ⟨ ~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (_ ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)

⟪ .(∙[lam] (lam M ﹐ γ ∷r⟨ _ ⟩ pair LHS RHS ﹐ γ' ■)) ~>ᵛᵛ⟨ ~∙lam∷r■~> γ γ' M LHS RHS ≡RHS ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = {!!}

⟪ .(∙[lam] (lam M ﹐ γ ∷r⟨ _ ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ _ ⟩ tail₁)) ~>ᵛᵛ⟨ ~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (_ ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ from ~>ᵛᵛ⟨ ~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ .(∙[lam] (lam M ﹐ γ ∷r⟨ _ ⟩ pair LHS RHS ﹐ γ' ∷r⟨ _ ⟩ tail₁)) ~>ᵛᵛ⟨ ~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (_ ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)

⟪ .(∙[unit] (unit ﹐ γ ∷r⟨ _ ⟩ pair LHS RHS ﹐ γ' ■)) ~>ᵛᵛ⟨ ~∙unit∷r■~> γ γ' LHS RHS ≡RHS ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = {!!}

⟪ .(∙[unit] (unit ﹐ γ ∷r⟨ _ ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ _ ⟩ tail₁)) ~>ᵛᵛ⟨ ~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (_ ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ from ~>ᵛᵛ⟨ ~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ .(∙[unit] (unit ﹐ γ ∷r⟨ _ ⟩ pair LHS RHS ﹐ γ' ∷r⟨ _ ⟩ tail₁)) ~>ᵛᵛ⟨ ~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (_ ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)

⟪ .(∙[pair] (pair x y ﹐ γ ∷r⟨ _ ⟩ pair LHS RHS ﹐ γ' ■)) ~>ᵛᵛ⟨ ~∙pair∷r■~> γ γ' x y LHS RHS ≡RHS ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = {!!}

⟪ .(∙[pair] (pair x y ﹐ γ ∷r⟨ _ ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ _ ⟩ tail₁)) ~>ᵛᵛ⟨ ~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (_ ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ from ~>ᵛᵛ⟨ ~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)
⟪ .(∙[pair] (pair x y ﹐ γ ∷r⟨ _ ⟩ pair LHS RHS ﹐ γ' ∷r⟨ _ ⟩ tail₁)) ~>ᵛᵛ⟨ ~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' tail₁ ⟩ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (_ ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ ~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' tail₁ ⟩::l⟨ f≡L' ⨾ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail)

-- (from ::l⟨ _ ⟩ tail) ~>ᵛᵛ⟨ (⟨ F>S ⟩::l⟨ f≡L' ⨾ _ ⟩ tail) ⟩ {!!}
-}
