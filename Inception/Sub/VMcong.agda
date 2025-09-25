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

_⦂⦂pm⟨_⟩_ : {H : Γ ⊢ᵛ A} → {γ : ⟦ Γ ⟧ˣ} → (head : valStack (T◾₁ `× T◾₂) H γ) → {M' : Γ' ⊢ᵛ T◾₁ `× T◾₂} → {γ' : ⟦ Γ' ⟧ˣ} → {N : (Γ' ∙ T◾₁ ∙ T◾₂) ⊢ᵛ C} → .(h≡M' : ⟦ head ⟧↥ ≡ ⟦ M' ⟧ᵛ γ') → valStack T◾' (pm M' N) γ' → valStack T◾' H γ
_⦂⦂pm⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ■) h≡M' tail = H ﹐ γ ∷pm⟨ h≡M' ⟩ tail
_⦂⦂pm⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ∷pm⟨ H≡M' ⟩ htail) h≡M' tail = H ﹐ γ ∷pm⟨ H≡M' ⟩ (htail ⦂⦂pm⟨ h≡M' ⟩ tail)
_⦂⦂pm⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ∷l⟨ H≡L' ⟩ htail) h≡M' tail = H ﹐ γ ∷l⟨ H≡L' ⟩ (htail ⦂⦂pm⟨ h≡M' ⟩ tail)
_⦂⦂pm⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ∷r⟨ H≡R' ⟩ htail) h≡M' tail = H ﹐ γ ∷r⟨ H≡R' ⟩ (htail ⦂⦂pm⟨ h≡M' ⟩ tail)

_⦂⦂r⟨_⟩_ : {H : Γ ⊢ᵛ A} → {γ : ⟦ Γ ⟧ˣ} → (head : valStack T◾ H γ) → {RHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → .(h≡R' : ⟦ head ⟧↥ ≡ ⟦ RHS' ⟧ᵛ γ') → {LHS : Γ' ⊢ᵛ B} → valStack T◾' (pair LHS RHS') γ' → valStack T◾' H γ
_⦂⦂r⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ■) h≡R' tail = H ﹐ γ ∷r⟨ h≡R' ⟩ tail
_⦂⦂r⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ∷pm⟨ H≡M' ⟩ htail) h≡R' tail = H ﹐ γ ∷pm⟨ H≡M' ⟩ (htail ⦂⦂r⟨ h≡R' ⟩ tail)
_⦂⦂r⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ∷l⟨ H≡L' ⟩ htail) h≡R' tail = H ﹐ γ ∷l⟨ H≡L' ⟩ (htail ⦂⦂r⟨ h≡R' ⟩ tail)
_⦂⦂r⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ∷r⟨ H≡R' ⟩ htail) h≡R' tail = H ﹐ γ ∷r⟨ H≡R' ⟩ (htail ⦂⦂r⟨ h≡R' ⟩ tail)

_⦂⦂l⟨_⟩_ : {H : Γ ⊢ᵛ A} → {γ : ⟦ Γ ⟧ˣ} → (head : valStack T◾ H γ) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → .(h≡L' : ⟦ head ⟧↥ ≡ ⟦ LHS' ⟧ᵛ γ') → {RHS : Γ' ⊢ᵛ B} → (tail : valStack T◾' (pair LHS' RHS) γ') → valStack T◾' H γ
_⦂⦂l⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ■) h≡L' tail = H ﹐ γ ∷l⟨ h≡L' ⟩ tail
_⦂⦂l⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ∷pm⟨ H≡M' ⟩ htail) h≡L' tail = H ﹐ γ ∷pm⟨ H≡M' ⟩ (htail ⦂⦂l⟨ h≡L' ⟩ tail)
_⦂⦂l⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ∷l⟨ H≡L' ⟩ htail) h≡L' tail = H ﹐ γ ∷l⟨ H≡L' ⟩ (htail ⦂⦂l⟨ h≡L' ⟩ tail)
_⦂⦂l⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ∷r⟨ H≡R' ⟩ htail) h≡L' tail = H ﹐ γ ∷r⟨ H≡R' ⟩ (htail ⦂⦂l⟨ h≡L' ⟩ tail)

_::pm⟨_⟩_ : (head : VState (T◾₁ `× T◾₂)) → {M' : Γ' ⊢ᵛ T◾₁ `× T◾₂} → {γ' : ⟦ Γ' ⟧ˣ} → {N : (Γ' ∙ T◾₁ ∙ T◾₂) ⊢ᵛ C} → .(h≡M' : ⟦ head ⟧◑ ≡ ⟦ M' ⟧ᵛ γ') → valStack T◾' (pm M' N) γ' → VState T◾'
(∘ M) ::pm⟨ h≡M' ⟩ tail = ∘ (M ⦂⦂pm⟨ h≡M' ⟩ tail)
(∙[var] M) ::pm⟨ h≡M' ⟩ tail = ∙[var] (M ⦂⦂pm⟨ h≡M' ⟩ tail)
(∙[lam] M) ::pm⟨ h≡M' ⟩ tail = ∙[lam] (M ⦂⦂pm⟨ h≡M' ⟩ tail)
(∙[unit] M) ::pm⟨ h≡M' ⟩ tail = ∙[unit] (M ⦂⦂pm⟨ h≡M' ⟩ tail)
(∙[pair] M) ::pm⟨ h≡M' ⟩ tail = ∙[pair] (M ⦂⦂pm⟨ h≡M' ⟩ tail)

_::r⟨_⟩_ : (head : VState T◾) → {RHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → .(h≡R' : ⟦ head ⟧◑ ≡ ⟦ RHS' ⟧ᵛ γ') → {LHS : Γ' ⊢ᵛ B} → valStack T◾' (pair LHS RHS') γ' → VState T◾'
(∘ M) ::r⟨ h≡R' ⟩ tail = ∘ (M ⦂⦂r⟨ h≡R' ⟩ tail)
(∙[var] M) ::r⟨ h≡R' ⟩ tail = ∙[var] (M ⦂⦂r⟨ h≡R' ⟩ tail)
(∙[lam] M) ::r⟨ h≡R' ⟩ tail = ∙[lam] (M ⦂⦂r⟨ h≡R' ⟩ tail)
(∙[unit] M) ::r⟨ h≡R' ⟩ tail = ∙[unit] (M ⦂⦂r⟨ h≡R' ⟩ tail)
(∙[pair] M) ::r⟨ h≡R' ⟩ tail = ∙[pair] (M ⦂⦂r⟨ h≡R' ⟩ tail)

_::l⟨_⟩_ : (head : VState T◾) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → .(h≡L' : ⟦ head ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → {RHS : Γ' ⊢ᵛ B} → (tail : valStack T◾' (pair LHS' RHS) γ') → VState T◾'
(∘ M) ::l⟨ h≡L' ⟩ tail =  ∘ (M ⦂⦂l⟨ h≡L' ⟩ tail)
(∙[var] M) ::l⟨ h≡L' ⟩ tail = ∙[var] (M ⦂⦂l⟨ h≡L' ⟩ tail)
(∙[lam] M) ::l⟨ h≡L' ⟩ tail = ∙[lam] (M ⦂⦂l⟨ h≡L' ⟩ tail)
(∙[unit] M) ::l⟨ h≡L' ⟩ tail = ∙[unit] (M ⦂⦂l⟨ h≡L' ⟩ tail)
(∙[pair] M) ::l⟨ h≡L' ⟩ tail = ∙[pair] (M ⦂⦂l⟨ h≡L' ⟩ tail)

⟨_⟩::l⟨_⨾_⟩_ : {from : VState T◾} → {to : VState T◾} → (F>T : from ~>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (t≡L' : ⟦ to ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS' RHS) γ') → (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ (to ::l⟨ t≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ ~∘var~> _ _ _ = ~∘var~>
⟨_⟩::l⟨_⨾_⟩_ ~∘lam~> _ _ _ = ~∘lam~>
⟨_⟩::l⟨_⨾_⟩_ ~∘pair~> _ _ _ = ~∘pair~>
⟨_⟩::l⟨_⨾_⟩_  ~∘pm~> _ _ _ = ~∘pm~>
⟨_⟩::l⟨_⨾_⟩_  ~∘unit~> _ _ _ = ~∘unit~>
⟨_⟩::l⟨_⨾_⟩_ (~∙var∷pm■~> γ γ'' i M N ≡M) f≡L' t≡L' tail = (~∙var∷pm∷l~> γ γ'' i M N ≡M f≡L' tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙var∷pm∷pm~> γ γ'' i M N ≡M ≡M' tail₁) f≡L' t≡L' tail = ~∙var∷pm∷pm~> γ γ'' i M N ≡M ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙var∷pm∷l~> γ γ'' i M N ≡M ≡LHS tail₁) f≡L' t≡L' tail = ~∙var∷pm∷l~> γ γ'' i M N ≡M ≡LHS (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙var∷pm∷r~> γ γ'' i M N ≡M ≡RHS tail₁) f≡L' t≡L' tail = ~∙var∷pm∷r~> γ γ'' i M N ≡M ≡RHS (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙pair∷pm■~> γ γ'' x y M N ≡M) f≡L' t≡L' tail = ~∙pair∷pm∷l~> γ γ'' x y M N ≡M f≡L' tail
⟨_⟩::l⟨_⨾_⟩_ (~∙pair∷pm∷pm~> γ γ'' x y M N ≡M ≡M' tail₁) f≡L' t≡L' tail = ~∙pair∷pm∷pm~> γ γ'' x y M N ≡M ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙pair∷pm∷l~> γ γ'' x y M N ≡M ≡LHS tail₁) f≡L' t≡L' tail = ~∙pair∷pm∷l~> γ γ'' x y M N ≡M ≡LHS (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙pair∷pm∷r~> γ γ'' x y M N ≡M ≡RHS tail₁) f≡L' t≡L' tail = ~∙pair∷pm∷r~> γ γ'' x y M N ≡M ≡RHS (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙var∷l■~> γ γ'' i LHS RHS₁ ≡LHS) f≡L' t≡L' tail = ~∙var∷l∷l~> γ γ'' i LHS RHS₁ ≡LHS f≡L' tail
⟨_⟩::l⟨_⨾_⟩_ (~∙var∷l∷pm~> γ γ'' i LHS RHS₁ ≡LHS ≡M' tail₁) f≡L' t≡L' tail = ~∙var∷l∷pm~> γ γ'' i LHS RHS₁ ≡LHS ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙var∷l∷l~> γ γ'' i LHS RHS₁ ≡LHS ≡LHS' tail₁) f≡L' t≡L' tail = ~∙var∷l∷l~> γ γ'' i LHS RHS₁ ≡LHS ≡LHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙var∷l∷r~> γ γ'' i LHS RHS₁ ≡LHS ≡RHS' tail₁) f≡L' t≡L' tail = ~∙var∷l∷r~> γ γ'' i LHS RHS₁ ≡LHS ≡RHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙lam∷l■~> γ γ'' M LHS RHS₁ ≡LHS) f≡L' t≡L' tail = ~∙lam∷l∷l~> γ γ'' M LHS RHS₁ ≡LHS f≡L' tail
⟨_⟩::l⟨_⨾_⟩_ (~∙lam∷l∷pm~> γ γ'' M LHS RHS₁ ≡LHS ≡M' tail₁) f≡L' t≡L' tail = ~∙lam∷l∷pm~> γ γ'' M LHS RHS₁ ≡LHS ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙lam∷l∷l~> γ γ'' M LHS RHS₁ ≡LHS ≡LHS' tail₁) f≡L' t≡L' tail = ~∙lam∷l∷l~> γ γ'' M LHS RHS₁ ≡LHS ≡LHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙lam∷l∷r~> γ γ'' M LHS RHS₁ ≡LHS ≡RHS' tail₁) f≡L' t≡L' tail = ~∙lam∷l∷r~> γ γ'' M LHS RHS₁ ≡LHS ≡RHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙unit∷l■~> γ γ'' LHS RHS₁ ≡LHS) f≡L' t≡L' tail = ~∙unit∷l∷l~> γ γ'' LHS RHS₁ ≡LHS f≡L' tail 
⟨_⟩::l⟨_⨾_⟩_ (~∙unit∷l∷pm~> γ γ'' LHS RHS₁ ≡LHS ≡M' tail₁) f≡L' t≡L' tail = ~∙unit∷l∷pm~> γ γ'' LHS RHS₁ ≡LHS ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙unit∷l∷l~> γ γ'' LHS RHS₁ ≡LHS ≡LHS' tail₁) f≡L' t≡L' tail = ~∙unit∷l∷l~> γ γ'' LHS RHS₁ ≡LHS ≡LHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙unit∷l∷r~> γ γ'' LHS RHS₁ ≡LHS ≡RHS' tail₁) f≡L' t≡L' tail = ~∙unit∷l∷r~> γ γ'' LHS RHS₁ ≡LHS ≡RHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙pair∷l■~> γ γ'' x y LHS RHS₁ ≡LHS) f≡L' t≡L' tail =  ~∙pair∷l∷l~> γ γ'' x y LHS RHS₁ ≡LHS f≡L' tail
⟨_⟩::l⟨_⨾_⟩_ (~∙pair∷l∷pm~> γ γ'' x y LHS RHS₁ ≡LHS ≡M' tail₁) f≡L' t≡L' tail = ~∙pair∷l∷pm~> γ γ'' x y LHS RHS₁ ≡LHS ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙pair∷l∷l~> γ γ'' x y LHS RHS₁ ≡LHS ≡LHS' tail₁) f≡L' t≡L' tail = ~∙pair∷l∷l~> γ γ'' x y LHS RHS₁ ≡LHS ≡LHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙pair∷l∷r~> γ γ'' x y LHS RHS₁ ≡LHS ≡RHS' tail₁) f≡L' t≡L' tail = ~∙pair∷l∷r~> γ γ'' x y LHS RHS₁ ≡LHS ≡RHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙var∷r■~> γ γ'' i LHS RHS₁ ≡RHS) f≡L' t≡L' tail = ~∙var∷r∷l~> γ γ'' i LHS RHS₁ ≡RHS f≡L' tail
⟨_⟩::l⟨_⨾_⟩_ (~∙var∷r∷pm~> γ γ'' i LHS RHS₁ ≡RHS ≡M' tail₁) f≡L' t≡L' tail = ~∙var∷r∷pm~> γ γ'' i LHS RHS₁ ≡RHS ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙var∷r∷l~> γ γ'' i LHS RHS₁ ≡RHS ≡LHS' tail₁) f≡L' t≡L' tail = ~∙var∷r∷l~> γ γ'' i LHS RHS₁ ≡RHS ≡LHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙var∷r∷r~> γ γ'' i LHS RHS₁ ≡RHS ≡RHS' tail₁) f≡L' t≡L' tail = ~∙var∷r∷r~> γ γ'' i LHS RHS₁ ≡RHS ≡RHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙lam∷r■~> γ γ'' M LHS RHS₁ ≡RHS) f≡L' t≡L' tail = ~∙lam∷r∷l~> γ γ'' M LHS RHS₁ ≡RHS f≡L' tail
⟨_⟩::l⟨_⨾_⟩_ (~∙lam∷r∷pm~> γ γ'' M LHS RHS₁ ≡RHS ≡M' tail₁) f≡L' t≡L' tail = ~∙lam∷r∷pm~> γ γ'' M LHS RHS₁ ≡RHS ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙lam∷r∷l~> γ γ'' M LHS RHS₁ ≡RHS ≡LHS' tail₁) f≡L' t≡L' tail = ~∙lam∷r∷l~> γ γ'' M LHS RHS₁ ≡RHS ≡LHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙lam∷r∷r~> γ γ'' M LHS RHS₁ ≡RHS ≡RHS' tail₁) f≡L' t≡L' tail = ~∙lam∷r∷r~> γ γ'' M LHS RHS₁ ≡RHS ≡RHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙unit∷r■~> γ γ'' LHS RHS₁ ≡RHS) f≡L' t≡L' tail = ~∙unit∷r∷l~> γ γ'' LHS RHS₁ ≡RHS f≡L' tail
⟨_⟩::l⟨_⨾_⟩_ (~∙unit∷r∷pm~> γ γ'' LHS RHS₁ ≡RHS ≡M' tail₁) f≡L' t≡L' tail = ~∙unit∷r∷pm~> γ γ'' LHS RHS₁ ≡RHS ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙unit∷r∷l~> γ γ'' LHS RHS₁ ≡RHS ≡LHS' tail₁) f≡L' t≡L' tail = ~∙unit∷r∷l~> γ γ'' LHS RHS₁ ≡RHS ≡LHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙unit∷r∷r~> γ γ'' LHS RHS₁ ≡RHS ≡RHS' tail₁) f≡L' t≡L' tail = ~∙unit∷r∷r~> γ γ'' LHS RHS₁ ≡RHS ≡RHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙pair∷r■~> γ γ'' x y LHS RHS₁ ≡RHS) f≡L' t≡L' tail = ~∙pair∷r∷l~> γ γ'' x y LHS RHS₁ ≡RHS f≡L' tail
⟨_⟩::l⟨_⨾_⟩_ (~∙pair∷r∷pm~> γ γ'' x y LHS RHS₁ ≡RHS ≡M' tail₁) f≡L' t≡L' tail = ~∙pair∷r∷pm~> γ γ'' x y LHS RHS₁ ≡RHS ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙pair∷r∷l~> γ γ'' x y LHS RHS₁ ≡RHS ≡LHS' tail₁) f≡L' t≡L' tail = ~∙pair∷r∷l~> γ γ'' x y LHS RHS₁ ≡RHS ≡LHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⨾_⟩_ (~∙pair∷r∷r~> γ γ'' x y LHS RHS₁ ≡RHS ≡RHS' tail₁) f≡L' t≡L' tail = ~∙pair∷r∷r~> γ γ'' x y LHS RHS₁ ≡RHS ≡RHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)

⟨_⟩::r⟨_⨾_⟩_ : {from : VState T◾} → {to : VState T◾} → (F>T : from ~>ᵛᵛ to) → {LHS : Γ' ⊢ᵛ A} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS' : Γ' ⊢ᵛ T◾} → (f≡R' : ⟦ from ⟧◑ ≡ ⟦ RHS' ⟧ᵛ γ') → (t≡R' : ⟦ to ⟧◑ ≡ ⟦ RHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS RHS') γ') → (from ::r⟨ f≡R' ⟩ tail) ~>ᵛᵛ (to ::r⟨ t≡R' ⟩ tail)
⟨ ~∘var~> ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∘var~>
⟨ ~∘lam~> ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∘lam~>
⟨ ~∘pair~> ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∘pair~>
⟨ ~∘pm~> ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∘pm~>
⟨ ~∘unit~> ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∘unit~>
⟨ ~∙var∷pm■~> γ γ' i M N ≡M ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙var∷pm∷r~> γ γ' i M N ≡M f≡R' tail
⟨ ~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙pair∷pm■~> γ γ' x y M N ≡M ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙pair∷pm∷r~> γ γ' x y M N ≡M f≡R' tail
⟨ ~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙var∷l■~> γ γ' i LHS RHS ≡LHS ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS f≡R' tail
⟨ ~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙lam∷l■~> γ γ' M LHS RHS ≡LHS ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS f≡R' tail
⟨ ~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙unit∷l■~> γ γ' LHS RHS ≡LHS ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS f≡R' tail
⟨ ~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙pair∷l■~> γ γ' x y LHS RHS ≡LHS ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS f≡R' tail
⟨ ~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙var∷r■~> γ γ' i LHS RHS ≡RHS ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS f≡R' tail
⟨ ~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙lam∷r■~> γ γ' M LHS RHS ≡RHS ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS f≡R' tail
⟨ ~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙unit∷r■~> γ γ' LHS RHS ≡RHS ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS f≡R' tail
⟨ ~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙pair∷r■~> γ γ' x y LHS RHS ≡RHS ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS f≡R' tail
⟨ ~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' tail₁ ⟩::r⟨ f≡R' ⨾ t≡R' ⟩ tail = ~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)

⟨_⟩::pm⟨_⨾_⟩_ : {from : VState (T◾₁ `× T◾₂)} → {to : VState (T◾₁ `× T◾₂)} → (F>T : from ~>ᵛᵛ to) → {M' : Γ' ⊢ᵛ (T◾₁ `× T◾₂)} → {γ' : ⟦ Γ' ⟧ˣ} → {N : (Γ' ∙ T◾₁ ∙ T◾₂) ⊢ᵛ C} → .(f≡M' : ⟦ from ⟧◑ ≡ ⟦ M' ⟧ᵛ γ') → .(t≡M' : ⟦ to ⟧◑ ≡ ⟦ M' ⟧ᵛ γ') → (tail : valStack T◾ (pm M' N) γ') → (from ::pm⟨ f≡M' ⟩ tail) ~>ᵛᵛ (to ::pm⟨ t≡M' ⟩ tail)
⟨ ~∘var~> ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∘var~>
⟨ ~∘lam~> ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∘lam~>
⟨ ~∘pair~> ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∘pair~>
⟨ ~∘pm~> ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∘pm~>
⟨ ~∘unit~> ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∘unit~>
⟨ ~∙var∷pm■~> γ γ' i M N ≡M ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙var∷pm∷pm~> γ γ' i M N ≡M f≡M' tail
⟨ ~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙pair∷pm■~> γ γ' x y M N ≡M ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙pair∷pm∷pm~> γ γ' x y M N ≡M f≡M' tail
⟨ ~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙var∷l■~> γ γ' i LHS RHS ≡LHS ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS f≡M' tail
⟨ ~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙lam∷l■~> γ γ' M LHS RHS ≡LHS ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS f≡M' tail
⟨ ~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙unit∷l■~> γ γ' LHS RHS ≡LHS ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS f≡M' tail
⟨ ~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙pair∷l■~> γ γ' x y LHS RHS ≡LHS ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS f≡M' tail
⟨ ~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙var∷r■~> γ γ' i LHS RHS ≡RHS ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS f≡M' tail
⟨ ~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙lam∷r■~> γ γ' M LHS RHS ≡RHS ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS f≡M' tail
⟨ ~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙unit∷r■~> γ γ' LHS RHS ≡RHS ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS f≡M' tail
⟨ ~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙pair∷r■~> γ γ' x y LHS RHS ≡RHS ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS f≡M' tail
⟨ ~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' tail₁ ⟩::pm⟨ f≡M' ⨾ t≡M' ⟩ tail = ~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)


-- ⟪_⟫::l⟨_⨾_⟩_ : {from : VState T◾} → {to : VState T◾} → (F>>T : from ~>>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (t≡L' : ⟦ to ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS' RHS) γ') → (from ::l⟨ f≡L' ⟩ tail) ~>>ᵛᵛ (to ::l⟨ t≡L' ⟩ tail)
-- ⟪ F>T ▣ ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = (⟨ F>T ⟩::l⟨ f≡L' ⨾ t≡L' ⟩ tail) ▣
-- ⟪ _ ~>>ᵛᵛ⟨ F>T ⟩ F>>T ⟫::l⟨ f≡L' ⨾ t≡L' ⟩ tail = {!!}
