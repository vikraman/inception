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
_⦂⦂pm⟨_⟩_ : {H : Γ ⊢ᵛ A} → {γ : ⟦ Γ ⟧ˣ} → (head : valStack (T◾₁ `× T◾₂) H γ) → {M' : Γ' ⊢ᵛ T◾₁ `× T◾₂} → {γ' : ⟦ Γ' ⟧ˣ} → {N : (Γ' ∙ T◾₁ ∙ T◾₂) ⊢ᵛ C} → (h≡M' : ⟦ head ⟧↥ ≡ ⟦ M' ⟧ᵛ γ') → valStack T◾' (pm M' N) γ' → valStack T◾' H γ
_⦂⦂pm⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ■) h≡M' tail = H ﹐ γ ∷pm⟨ h≡M' ⟩ tail
_⦂⦂pm⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ∷pm⟨ H≡M' ⟩ htail) h≡M' tail = H ﹐ γ ∷pm⟨ H≡M' ⟩ (htail ⦂⦂pm⟨ h≡M' ⟩ tail)
_⦂⦂pm⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ∷l⟨ H≡L' ⟩ htail) h≡M' tail = H ﹐ γ ∷l⟨ H≡L' ⟩ (htail ⦂⦂pm⟨ h≡M' ⟩ tail)
_⦂⦂pm⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ∷r⟨ H≡R' ⟩ htail) h≡M' tail = H ﹐ γ ∷r⟨ H≡R' ⟩ (htail ⦂⦂pm⟨ h≡M' ⟩ tail)

_⦂⦂r⟨_⟩_ : {H : Γ ⊢ᵛ A} → {γ : ⟦ Γ ⟧ˣ} → (head : valStack T◾ H γ) → {RHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → (h≡R' : ⟦ head ⟧↥ ≡ ⟦ RHS' ⟧ᵛ γ') → {LHS : Γ' ⊢ᵛ B} → valStack T◾' (pair LHS RHS') γ' → valStack T◾' H γ
_⦂⦂r⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ■) h≡R' tail = H ﹐ γ ∷r⟨ h≡R' ⟩ tail
_⦂⦂r⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ∷pm⟨ H≡M' ⟩ htail) h≡R' tail = H ﹐ γ ∷pm⟨ H≡M' ⟩ (htail ⦂⦂r⟨ h≡R' ⟩ tail)
_⦂⦂r⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ∷l⟨ H≡L' ⟩ htail) h≡R' tail = H ﹐ γ ∷l⟨ H≡L' ⟩ (htail ⦂⦂r⟨ h≡R' ⟩ tail)
_⦂⦂r⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ∷r⟨ H≡R' ⟩ htail) h≡R' tail = H ﹐ γ ∷r⟨ H≡R' ⟩ (htail ⦂⦂r⟨ h≡R' ⟩ tail)

_⦂⦂l⟨_⟩_ : {H : Γ ⊢ᵛ A} → {γ : ⟦ Γ ⟧ˣ} → (head : valStack T◾ H γ) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → (h≡L' : ⟦ head ⟧↥ ≡ ⟦ LHS' ⟧ᵛ γ') → {RHS : Γ' ⊢ᵛ B} → (tail : valStack T◾' (pair LHS' RHS) γ') → valStack T◾' H γ
_⦂⦂l⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ■) h≡L' tail = H ﹐ γ ∷l⟨ h≡L' ⟩ tail
_⦂⦂l⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ∷pm⟨ H≡M' ⟩ htail) h≡L' tail = H ﹐ γ ∷pm⟨ H≡M' ⟩ (htail ⦂⦂l⟨ h≡L' ⟩ tail)
_⦂⦂l⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ∷l⟨ H≡L' ⟩ htail) h≡L' tail = H ﹐ γ ∷l⟨ H≡L' ⟩ (htail ⦂⦂l⟨ h≡L' ⟩ tail)
_⦂⦂l⟨_⟩_ {H = H} {γ = γ} (.H ﹐ .γ ∷r⟨ H≡R' ⟩ htail) h≡L' tail = H ﹐ γ ∷r⟨ H≡R' ⟩ (htail ⦂⦂l⟨ h≡L' ⟩ tail)

_::pm⟨_⟩_ : (head : VState (T◾₁ `× T◾₂)) → {M' : Γ' ⊢ᵛ T◾₁ `× T◾₂} → {γ' : ⟦ Γ' ⟧ˣ} → {N : (Γ' ∙ T◾₁ ∙ T◾₂) ⊢ᵛ C} → (h≡M' : ⟦ head ⟧◑ ≡ ⟦ M' ⟧ᵛ γ') → valStack T◾' (pm M' N) γ' → VState T◾'
(∘ M) ::pm⟨ h≡M' ⟩ tail = ∘ (M ⦂⦂pm⟨ h≡M' ⟩ tail)
(∙[var] M) ::pm⟨ h≡M' ⟩ tail = ∙[var] (M ⦂⦂pm⟨ h≡M' ⟩ tail)
(∙[lam] M) ::pm⟨ h≡M' ⟩ tail = ∙[lam] (M ⦂⦂pm⟨ h≡M' ⟩ tail)
(∙[unit] M) ::pm⟨ h≡M' ⟩ tail = ∙[unit] (M ⦂⦂pm⟨ h≡M' ⟩ tail)
(∙[pair] M) ::pm⟨ h≡M' ⟩ tail = ∙[pair] (M ⦂⦂pm⟨ h≡M' ⟩ tail)

_::r⟨_⟩_ : (head : VState T◾) → {RHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → (h≡R' : ⟦ head ⟧◑ ≡ ⟦ RHS' ⟧ᵛ γ') → {LHS : Γ' ⊢ᵛ B} → valStack T◾' (pair LHS RHS') γ' → VState T◾'
(∘ M) ::r⟨ h≡R' ⟩ tail = ∘ (M ⦂⦂r⟨ h≡R' ⟩ tail)
(∙[var] M) ::r⟨ h≡R' ⟩ tail = ∙[var] (M ⦂⦂r⟨ h≡R' ⟩ tail)
(∙[lam] M) ::r⟨ h≡R' ⟩ tail = ∙[lam] (M ⦂⦂r⟨ h≡R' ⟩ tail)
(∙[unit] M) ::r⟨ h≡R' ⟩ tail = ∙[unit] (M ⦂⦂r⟨ h≡R' ⟩ tail)
(∙[pair] M) ::r⟨ h≡R' ⟩ tail = ∙[pair] (M ⦂⦂r⟨ h≡R' ⟩ tail)

_::l⟨_⟩_ : (head : VState T◾) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → (h≡L' : ⟦ head ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → {RHS : Γ' ⊢ᵛ B} → (tail : valStack T◾' (pair LHS' RHS) γ') → VState T◾'
(∘ M) ::l⟨ h≡L' ⟩ tail =  ∘ (M ⦂⦂l⟨ h≡L' ⟩ tail)
(∙[var] M) ::l⟨ h≡L' ⟩ tail = ∙[var] (M ⦂⦂l⟨ h≡L' ⟩ tail)
(∙[lam] M) ::l⟨ h≡L' ⟩ tail = ∙[lam] (M ⦂⦂l⟨ h≡L' ⟩ tail)
(∙[unit] M) ::l⟨ h≡L' ⟩ tail = ∙[unit] (M ⦂⦂l⟨ h≡L' ⟩ tail)
(∙[pair] M) ::l⟨ h≡L' ⟩ tail = ∙[pair] (M ⦂⦂l⟨ h≡L' ⟩ tail)


T≡Fl : {from : VState T◾} → {to : VState T◾} → (F>T : from ~>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS' RHS) γ') → (⟦ to ⟧◑ ≡ ⟦ from ⟧◑)
T≡Fl ~∘var~> f≡L' tail = refl
T≡Fl ~∘lam~> f≡L' tail = refl
T≡Fl ~∘pair~> f≡L' tail = refl
T≡Fl ~∘pm~> f≡L' tail = refl
T≡Fl ~∘unit~> f≡L' tail = refl
T≡Fl (~∙var∷pm■~> γ γ' i M N ≡M) f≡L' tail = cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (_ , p)) ≡M
T≡Fl (~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' tail₁) f≡L' tail = refl
T≡Fl (~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS tail₁) f≡L' tail = refl
T≡Fl (~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS tail₁) f≡L' tail = refl
T≡Fl (~∙pair∷pm■~> γ γ' x y M N ≡M) f≡L' tail = cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (_ , p)) ≡M
T≡Fl (~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' tail₁) f≡L' tail = refl
T≡Fl (~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS tail₁) f≡L' tail = refl
T≡Fl (~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS tail₁) f≡L' tail = refl
T≡Fl (~∙var∷l■~> γ γ' i LHS RHS ≡LHS) f≡L' tail = cong (λ t₁ → t₁ , _) ≡LHS
T≡Fl (~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = refl
T≡Fl (~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = refl
T≡Fl (~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = refl
T≡Fl (~∙lam∷l■~> γ γ' M LHS RHS ≡LHS) f≡L' tail = cong (λ t₁ → t₁ , _) ≡LHS
T≡Fl (~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = refl
T≡Fl (~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = refl
T≡Fl (~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = refl
T≡Fl (~∙unit∷l■~> γ γ' LHS RHS ≡LHS) f≡L' tail = cong (λ t₁ → t₁ , _) ≡LHS
T≡Fl (~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = refl
T≡Fl (~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = refl
T≡Fl (~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = refl
T≡Fl (~∙pair∷l■~> γ γ' x y LHS RHS ≡LHS) f≡L' tail = cong (λ t₁ → t₁ , _) ≡LHS
T≡Fl (~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = refl
T≡Fl (~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = refl
T≡Fl (~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = refl
T≡Fl (~∙var∷r■~> γ γ' i LHS RHS ≡RHS) f≡L' tail = cong (λ t₁ → _ , t₁) ≡RHS
T≡Fl (~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = refl
T≡Fl (~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = refl
T≡Fl (~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = refl
T≡Fl (~∙lam∷r■~> γ γ' M LHS RHS ≡RHS) f≡L' tail = cong (λ t₁ → _ , t₁) ≡RHS
T≡Fl (~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = refl
T≡Fl (~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = refl
T≡Fl (~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = refl
T≡Fl (~∙unit∷r■~> γ γ' LHS RHS ≡RHS) f≡L' tail = cong (λ t₁ → _ , t₁) ≡RHS
T≡Fl (~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = refl
T≡Fl (~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = refl
T≡Fl (~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = refl
T≡Fl (~∙pair∷r■~> γ γ' x y LHS RHS ≡RHS) f≡L' tail = cong (λ t₁ → _ , t₁) ≡RHS
T≡Fl (~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = refl
T≡Fl (~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = refl
T≡Fl (~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = refl

T≡Fr : {from : VState T◾} → {to : VState T◾} → (F>T : from ~>ᵛᵛ to) → {LHS : Γ' ⊢ᵛ A} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS' : Γ' ⊢ᵛ T◾} → (f≡R' : ⟦ from ⟧◑ ≡ ⟦ RHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS RHS') γ') → (⟦ to ⟧◑ ≡ ⟦ from ⟧◑)
T≡Fr ~∘var~> f≡R' tail = refl
T≡Fr ~∘lam~> f≡R' tail = refl
T≡Fr ~∘pair~> f≡R' tail = refl
T≡Fr ~∘pm~> f≡R' tail = refl
T≡Fr ~∘unit~> f≡R' tail = refl
T≡Fr (~∙var∷pm■~> γ γ' i M N ≡M) f≡R' tail = cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p)) ≡M
T≡Fr (~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' tail₁) f≡R' tail = refl
T≡Fr (~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS tail₁) f≡R' tail = refl
T≡Fr (~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS tail₁) f≡R' tail = refl
T≡Fr (~∙pair∷pm■~> γ γ' x y M N ≡M) f≡R' tail = cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p)) ≡M
T≡Fr (~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' tail₁) f≡R' tail = refl
T≡Fr (~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS tail₁) f≡R' tail = refl
T≡Fr (~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS tail₁) f≡R' tail = refl
T≡Fr (~∙var∷l■~> γ γ' i LHS RHS ≡LHS) f≡R' tail = cong (λ t₁ → t₁ , ⟦ RHS ⟧ᵛ γ') ≡LHS
T≡Fr (~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' tail₁) f≡R' tail = refl
T≡Fr (~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' tail₁) f≡R' tail = refl
T≡Fr (~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' tail₁) f≡R' tail = refl
T≡Fr (~∙lam∷l■~> γ γ' M LHS RHS ≡LHS) f≡R' tail = cong (λ t₁ → t₁ , ⟦ RHS ⟧ᵛ γ') ≡LHS
T≡Fr (~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' tail₁) f≡R' tail = refl
T≡Fr (~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' tail₁) f≡R' tail = refl
T≡Fr (~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' tail₁) f≡R' tail = refl
T≡Fr (~∙unit∷l■~> γ γ' LHS RHS ≡LHS) f≡R' tail = cong (λ t₁ → t₁ , ⟦ RHS ⟧ᵛ γ') ≡LHS
T≡Fr (~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' tail₁) f≡R' tail = refl
T≡Fr (~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' tail₁) f≡R' tail = refl
T≡Fr (~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' tail₁) f≡R' tail = refl
T≡Fr (~∙pair∷l■~> γ γ' x y LHS RHS ≡LHS) f≡R' tail = cong (λ t₁ → t₁ , ⟦ RHS ⟧ᵛ γ') ≡LHS
T≡Fr (~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' tail₁) f≡R' tail = refl
T≡Fr (~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' tail₁) f≡R' tail = refl
T≡Fr (~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' tail₁) f≡R' tail = refl
T≡Fr (~∙var∷r■~> γ γ' i LHS RHS ≡RHS) f≡R' tail = cong (λ t₁ → ⟦ LHS ⟧ᵛ γ' , t₁) ≡RHS
T≡Fr (~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' tail₁) f≡R' tail = refl
T≡Fr (~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' tail₁) f≡R' tail = refl
T≡Fr (~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' tail₁) f≡R' tail = refl
T≡Fr (~∙lam∷r■~> γ γ' M LHS RHS ≡RHS) f≡R' tail = cong (λ t₁ → ⟦ LHS ⟧ᵛ γ' , t₁) ≡RHS
T≡Fr (~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' tail₁) f≡R' tail = refl
T≡Fr (~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' tail₁) f≡R' tail = refl
T≡Fr (~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' tail₁) f≡R' tail = refl
T≡Fr (~∙unit∷r■~> γ γ' LHS RHS ≡RHS) f≡R' tail = cong (λ t₁ → ⟦ LHS ⟧ᵛ γ' , t₁) ≡RHS
T≡Fr (~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' tail₁) f≡R' tail = refl
T≡Fr (~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' tail₁) f≡R' tail = refl
T≡Fr (~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' tail₁) f≡R' tail = refl
T≡Fr (~∙pair∷r■~> γ γ' x y LHS RHS ≡RHS) f≡R' tail = cong (λ t₁ → ⟦ LHS ⟧ᵛ γ' , t₁) ≡RHS
T≡Fr (~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' tail₁) f≡R' tail = refl
T≡Fr (~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' tail₁) f≡R' tail = refl
T≡Fr (~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' tail₁) f≡R' tail = refl

T≡Fpm : {from : VState (T◾₁ `× T◾₂)} → {to : VState (T◾₁ `× T◾₂)} → (F>T : from ~>ᵛᵛ to) → {M' : Γ' ⊢ᵛ (T◾₁ `× T◾₂)} → {γ' : ⟦ Γ' ⟧ˣ} → {N : (Γ' ∙ T◾₁ ∙ T◾₂) ⊢ᵛ C} → (f≡M' : ⟦ from ⟧◑ ≡ ⟦ M' ⟧ᵛ γ') → (tail : valStack T◾ (pm M' N) γ') → (⟦ to ⟧◑ ≡ ⟦ from ⟧◑)
T≡Fpm ~∘var~> f≡M' tail = refl
T≡Fpm ~∘lam~> f≡M' tail = refl
T≡Fpm ~∘pair~> f≡M' tail = refl
T≡Fpm ~∘pm~> f≡M' tail = refl
T≡Fpm ~∘unit~> f≡M' tail = refl
T≡Fpm (~∙var∷pm■~> γ γ' i M N ≡M) f≡M' tail = cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p)) ≡M
T≡Fpm (~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' tail₁) f≡M' tail = refl
T≡Fpm (~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS tail₁) f≡M' tail = refl
T≡Fpm (~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS tail₁) f≡M' tail = refl
T≡Fpm (~∙pair∷pm■~> γ γ' x y M N ≡M) f≡M' tail = cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p)) ≡M
T≡Fpm (~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' tail₁) f≡M' tail = refl
T≡Fpm (~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS tail₁) f≡M' tail = refl
T≡Fpm (~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS tail₁) f≡M' tail = refl
T≡Fpm (~∙var∷l■~> γ γ' i LHS RHS ≡LHS) f≡M' tail = cong (λ t₁ → t₁ , ⟦ RHS ⟧ᵛ γ') ≡LHS
T≡Fpm (~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' tail₁) f≡M' tail = refl
T≡Fpm (~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' tail₁) f≡M' tail = refl
T≡Fpm (~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' tail₁) f≡M' tail = refl
T≡Fpm (~∙lam∷l■~> γ γ' M LHS RHS ≡LHS) f≡M' tail = cong (λ t₁ → t₁ , ⟦ RHS ⟧ᵛ γ') ≡LHS
T≡Fpm (~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' tail₁) f≡M' tail = refl
T≡Fpm (~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' tail₁) f≡M' tail = refl
T≡Fpm (~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' tail₁) f≡M' tail = refl
T≡Fpm (~∙unit∷l■~> γ γ' LHS RHS ≡LHS) f≡M' tail = cong (λ t₁ → t₁ , ⟦ RHS ⟧ᵛ γ') ≡LHS
T≡Fpm (~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' tail₁) f≡M' tail = refl
T≡Fpm (~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' tail₁) f≡M' tail = refl
T≡Fpm (~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' tail₁) f≡M' tail = refl
T≡Fpm (~∙pair∷l■~> γ γ' x y LHS RHS ≡LHS) f≡M' tail = cong (λ t₁ → t₁ , ⟦ RHS ⟧ᵛ γ') ≡LHS
T≡Fpm (~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' tail₁) f≡M' tail = refl
T≡Fpm (~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' tail₁) f≡M' tail = refl
T≡Fpm (~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' tail₁) f≡M' tail = refl
T≡Fpm (~∙var∷r■~> γ γ' i LHS RHS ≡RHS) f≡M' tail = cong (λ t₁ → ⟦ LHS ⟧ᵛ γ' , t₁) ≡RHS
T≡Fpm (~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' tail₁) f≡M' tail = refl
T≡Fpm (~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' tail₁) f≡M' tail = refl
T≡Fpm (~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' tail₁) f≡M' tail = refl
T≡Fpm (~∙lam∷r■~> γ γ' M LHS RHS ≡RHS) f≡M' tail = cong (λ t₁ → ⟦ LHS ⟧ᵛ γ' , t₁) ≡RHS
T≡Fpm (~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' tail₁) f≡M' tail = refl
T≡Fpm (~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' tail₁) f≡M' tail = refl
T≡Fpm (~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' tail₁) f≡M' tail = refl
T≡Fpm (~∙unit∷r■~> γ γ' LHS RHS ≡RHS) f≡M' tail = cong (λ t₁ → ⟦ LHS ⟧ᵛ γ' , t₁) ≡RHS
T≡Fpm (~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' tail₁) f≡M' tail = refl
T≡Fpm (~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' tail₁) f≡M' tail = refl
T≡Fpm (~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' tail₁) f≡M' tail = refl
T≡Fpm (~∙pair∷r■~> γ γ' x y LHS RHS ≡RHS) f≡M' tail = cong (λ t₁ → ⟦ LHS ⟧ᵛ γ' , t₁) ≡RHS
T≡Fpm (~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' tail₁) f≡M' tail = refl
T≡Fpm (~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' tail₁) f≡M' tail = refl
T≡Fpm (~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' tail₁) f≡M' tail = refl

⟨_⟩::l⟨_⟩_ : {from : VState T◾} → {to : VState T◾} → (F>T : from ~>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS' RHS) γ') → (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ (to ::l⟨ trans (T≡Fl F>T f≡L' tail) f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ ~∘var~> _ _ = ~∘var~>
⟨_⟩::l⟨_⟩_ ~∘lam~> _ _ = ~∘lam~>
⟨_⟩::l⟨_⟩_ ~∘pair~> _ _ = ~∘pair~>
⟨_⟩::l⟨_⟩_  ~∘pm~> _ _ = ~∘pm~>
⟨_⟩::l⟨_⟩_  ~∘unit~> _ _ = ~∘unit~>
⟨_⟩::l⟨_⟩_ (~∙var∷pm■~> γ γ'' i M N ≡M) f≡L' tail = (~∙var∷pm∷l~> γ γ'' i M N ≡M f≡L' tail)
⟨_⟩::l⟨_⟩_ (~∙var∷pm∷pm~> γ γ'' i M N ≡M ≡M' tail₁) f≡L' tail = ~∙var∷pm∷pm~> γ γ'' i M N ≡M ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙var∷pm∷l~> γ γ'' i M N ≡M ≡LHS tail₁) f≡L' tail = ~∙var∷pm∷l~> γ γ'' i M N ≡M ≡LHS (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙var∷pm∷r~> γ γ'' i M N ≡M ≡RHS tail₁) f≡L' tail = ~∙var∷pm∷r~> γ γ'' i M N ≡M ≡RHS (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙pair∷pm■~> γ γ'' x y M N ≡M) f≡L' tail = ~∙pair∷pm∷l~> γ γ'' x y M N ≡M f≡L' tail
⟨_⟩::l⟨_⟩_ (~∙pair∷pm∷pm~> γ γ'' x y M N ≡M ≡M' tail₁) f≡L' tail = ~∙pair∷pm∷pm~> γ γ'' x y M N ≡M ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙pair∷pm∷l~> γ γ'' x y M N ≡M ≡LHS tail₁) f≡L' tail = ~∙pair∷pm∷l~> γ γ'' x y M N ≡M ≡LHS (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙pair∷pm∷r~> γ γ'' x y M N ≡M ≡RHS tail₁) f≡L' tail = ~∙pair∷pm∷r~> γ γ'' x y M N ≡M ≡RHS (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙var∷l■~> γ γ'' i LHS RHS₁ ≡LHS) f≡L' tail = ~∙var∷l∷l~> γ γ'' i LHS RHS₁ ≡LHS f≡L' tail
⟨_⟩::l⟨_⟩_ (~∙var∷l∷pm~> γ γ'' i LHS RHS₁ ≡LHS ≡M' tail₁) f≡L' tail = ~∙var∷l∷pm~> γ γ'' i LHS RHS₁ ≡LHS ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙var∷l∷l~> γ γ'' i LHS RHS₁ ≡LHS ≡LHS' tail₁) f≡L' tail = ~∙var∷l∷l~> γ γ'' i LHS RHS₁ ≡LHS ≡LHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙var∷l∷r~> γ γ'' i LHS RHS₁ ≡LHS ≡RHS' tail₁) f≡L' tail = ~∙var∷l∷r~> γ γ'' i LHS RHS₁ ≡LHS ≡RHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙lam∷l■~> γ γ'' M LHS RHS₁ ≡LHS) f≡L' tail = ~∙lam∷l∷l~> γ γ'' M LHS RHS₁ ≡LHS f≡L' tail
⟨_⟩::l⟨_⟩_ (~∙lam∷l∷pm~> γ γ'' M LHS RHS₁ ≡LHS ≡M' tail₁) f≡L' tail = ~∙lam∷l∷pm~> γ γ'' M LHS RHS₁ ≡LHS ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙lam∷l∷l~> γ γ'' M LHS RHS₁ ≡LHS ≡LHS' tail₁) f≡L' tail = ~∙lam∷l∷l~> γ γ'' M LHS RHS₁ ≡LHS ≡LHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙lam∷l∷r~> γ γ'' M LHS RHS₁ ≡LHS ≡RHS' tail₁) f≡L' tail = ~∙lam∷l∷r~> γ γ'' M LHS RHS₁ ≡LHS ≡RHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙unit∷l■~> γ γ'' LHS RHS₁ ≡LHS) f≡L' tail = ~∙unit∷l∷l~> γ γ'' LHS RHS₁ ≡LHS f≡L' tail 
⟨_⟩::l⟨_⟩_ (~∙unit∷l∷pm~> γ γ'' LHS RHS₁ ≡LHS ≡M' tail₁) f≡L' tail = ~∙unit∷l∷pm~> γ γ'' LHS RHS₁ ≡LHS ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙unit∷l∷l~> γ γ'' LHS RHS₁ ≡LHS ≡LHS' tail₁) f≡L' tail = ~∙unit∷l∷l~> γ γ'' LHS RHS₁ ≡LHS ≡LHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙unit∷l∷r~> γ γ'' LHS RHS₁ ≡LHS ≡RHS' tail₁) f≡L' tail = ~∙unit∷l∷r~> γ γ'' LHS RHS₁ ≡LHS ≡RHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙pair∷l■~> γ γ'' x y LHS RHS₁ ≡LHS) f≡L' tail =  ~∙pair∷l∷l~> γ γ'' x y LHS RHS₁ ≡LHS f≡L' tail
⟨_⟩::l⟨_⟩_ (~∙pair∷l∷pm~> γ γ'' x y LHS RHS₁ ≡LHS ≡M' tail₁) f≡L' tail = ~∙pair∷l∷pm~> γ γ'' x y LHS RHS₁ ≡LHS ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙pair∷l∷l~> γ γ'' x y LHS RHS₁ ≡LHS ≡LHS' tail₁) f≡L' tail = ~∙pair∷l∷l~> γ γ'' x y LHS RHS₁ ≡LHS ≡LHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙pair∷l∷r~> γ γ'' x y LHS RHS₁ ≡LHS ≡RHS' tail₁) f≡L' tail = ~∙pair∷l∷r~> γ γ'' x y LHS RHS₁ ≡LHS ≡RHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙var∷r■~> γ γ'' i LHS RHS₁ ≡RHS) f≡L' tail = ~∙var∷r∷l~> γ γ'' i LHS RHS₁ ≡RHS f≡L' tail
⟨_⟩::l⟨_⟩_ (~∙var∷r∷pm~> γ γ'' i LHS RHS₁ ≡RHS ≡M' tail₁) f≡L' tail = ~∙var∷r∷pm~> γ γ'' i LHS RHS₁ ≡RHS ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙var∷r∷l~> γ γ'' i LHS RHS₁ ≡RHS ≡LHS' tail₁) f≡L' tail = ~∙var∷r∷l~> γ γ'' i LHS RHS₁ ≡RHS ≡LHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙var∷r∷r~> γ γ'' i LHS RHS₁ ≡RHS ≡RHS' tail₁) f≡L' tail = ~∙var∷r∷r~> γ γ'' i LHS RHS₁ ≡RHS ≡RHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙lam∷r■~> γ γ'' M LHS RHS₁ ≡RHS) f≡L' tail = ~∙lam∷r∷l~> γ γ'' M LHS RHS₁ ≡RHS f≡L' tail
⟨_⟩::l⟨_⟩_ (~∙lam∷r∷pm~> γ γ'' M LHS RHS₁ ≡RHS ≡M' tail₁) f≡L' tail = ~∙lam∷r∷pm~> γ γ'' M LHS RHS₁ ≡RHS ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙lam∷r∷l~> γ γ'' M LHS RHS₁ ≡RHS ≡LHS' tail₁) f≡L' tail = ~∙lam∷r∷l~> γ γ'' M LHS RHS₁ ≡RHS ≡LHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙lam∷r∷r~> γ γ'' M LHS RHS₁ ≡RHS ≡RHS' tail₁) f≡L' tail = ~∙lam∷r∷r~> γ γ'' M LHS RHS₁ ≡RHS ≡RHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙unit∷r■~> γ γ'' LHS RHS₁ ≡RHS) f≡L' tail = ~∙unit∷r∷l~> γ γ'' LHS RHS₁ ≡RHS f≡L' tail
⟨_⟩::l⟨_⟩_ (~∙unit∷r∷pm~> γ γ'' LHS RHS₁ ≡RHS ≡M' tail₁) f≡L' tail = ~∙unit∷r∷pm~> γ γ'' LHS RHS₁ ≡RHS ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙unit∷r∷l~> γ γ'' LHS RHS₁ ≡RHS ≡LHS' tail₁) f≡L' tail = ~∙unit∷r∷l~> γ γ'' LHS RHS₁ ≡RHS ≡LHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙unit∷r∷r~> γ γ'' LHS RHS₁ ≡RHS ≡RHS' tail₁) f≡L' tail = ~∙unit∷r∷r~> γ γ'' LHS RHS₁ ≡RHS ≡RHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙pair∷r■~> γ γ'' x y LHS RHS₁ ≡RHS) f≡L' tail = ~∙pair∷r∷l~> γ γ'' x y LHS RHS₁ ≡RHS f≡L' tail
⟨_⟩::l⟨_⟩_ (~∙pair∷r∷pm~> γ γ'' x y LHS RHS₁ ≡RHS ≡M' tail₁) f≡L' tail = ~∙pair∷r∷pm~> γ γ'' x y LHS RHS₁ ≡RHS ≡M' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙pair∷r∷l~> γ γ'' x y LHS RHS₁ ≡RHS ≡LHS' tail₁) f≡L' tail = ~∙pair∷r∷l~> γ γ'' x y LHS RHS₁ ≡RHS ≡LHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)
⟨_⟩::l⟨_⟩_ (~∙pair∷r∷r~> γ γ'' x y LHS RHS₁ ≡RHS ≡RHS' tail₁) f≡L' tail = ~∙pair∷r∷r~> γ γ'' x y LHS RHS₁ ≡RHS ≡RHS' (tail₁ ⦂⦂l⟨ f≡L' ⟩ tail)

⟨_⟩::r⟨_⟩_ : {from : VState T◾} → {to : VState T◾} → (F>T : from ~>ᵛᵛ to) → {LHS : Γ' ⊢ᵛ A} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS' : Γ' ⊢ᵛ T◾} → (f≡R' : ⟦ from ⟧◑ ≡ ⟦ RHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS RHS') γ') → (from ::r⟨ f≡R' ⟩ tail) ~>ᵛᵛ (to ::r⟨ trans (T≡Fr F>T f≡R' tail) f≡R' ⟩ tail)
⟨ ~∘var~> ⟩::r⟨ f≡R' ⟩ tail = ~∘var~>
⟨ ~∘lam~> ⟩::r⟨ f≡R' ⟩ tail = ~∘lam~>
⟨ ~∘pair~> ⟩::r⟨ f≡R' ⟩ tail = ~∘pair~>
⟨ ~∘pm~> ⟩::r⟨ f≡R' ⟩ tail = ~∘pm~>
⟨ ~∘unit~> ⟩::r⟨ f≡R' ⟩ tail = ~∘unit~>
⟨ ~∙var∷pm■~> γ γ' i M N ≡M ⟩::r⟨ f≡R' ⟩ tail = ~∙var∷pm∷r~> γ γ' i M N ≡M f≡R' tail
⟨ ~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙pair∷pm■~> γ γ' x y M N ≡M ⟩::r⟨ f≡R' ⟩ tail = ~∙pair∷pm∷r~> γ γ' x y M N ≡M f≡R' tail
⟨ ~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙var∷l■~> γ γ' i LHS RHS ≡LHS ⟩::r⟨ f≡R' ⟩ tail = ~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS f≡R' tail
⟨ ~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙lam∷l■~> γ γ' M LHS RHS ≡LHS ⟩::r⟨ f≡R' ⟩ tail = ~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS f≡R' tail
⟨ ~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙unit∷l■~> γ γ' LHS RHS ≡LHS ⟩::r⟨ f≡R' ⟩ tail = ~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS f≡R' tail
⟨ ~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙pair∷l■~> γ γ' x y LHS RHS ≡LHS ⟩::r⟨ f≡R' ⟩ tail = ~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS f≡R' tail
⟨ ~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙var∷r■~> γ γ' i LHS RHS ≡RHS ⟩::r⟨ f≡R' ⟩ tail = ~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS f≡R' tail
⟨ ~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙lam∷r■~> γ γ' M LHS RHS ≡RHS ⟩::r⟨ f≡R' ⟩ tail = ~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS f≡R' tail
⟨ ~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙unit∷r■~> γ γ' LHS RHS ≡RHS ⟩::r⟨ f≡R' ⟩ tail = ~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS f≡R' tail
⟨ ~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙pair∷r■~> γ γ' x y LHS RHS ≡RHS ⟩::r⟨ f≡R' ⟩ tail = ~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS f≡R' tail
⟨ ~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)
⟨ ~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' tail₁ ⟩::r⟨ f≡R' ⟩ tail = ~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' (tail₁ ⦂⦂r⟨ f≡R' ⟩ tail)

⟨_⟩::pm⟨_⟩_ : {from : VState (T◾₁ `× T◾₂)} → {to : VState (T◾₁ `× T◾₂)} → (F>T : from ~>ᵛᵛ to) → {M' : Γ' ⊢ᵛ (T◾₁ `× T◾₂)} → {γ' : ⟦ Γ' ⟧ˣ} → {N : (Γ' ∙ T◾₁ ∙ T◾₂) ⊢ᵛ C} → (f≡M' : ⟦ from ⟧◑ ≡ ⟦ M' ⟧ᵛ γ') → (tail : valStack T◾ (pm M' N) γ') → (from ::pm⟨ f≡M' ⟩ tail) ~>ᵛᵛ (to ::pm⟨ trans (T≡Fpm F>T f≡M' tail) f≡M' ⟩ tail)
⟨ ~∘var~> ⟩::pm⟨ f≡M' ⟩ tail = ~∘var~>
⟨ ~∘lam~> ⟩::pm⟨ f≡M' ⟩ tail = ~∘lam~>
⟨ ~∘pair~> ⟩::pm⟨ f≡M' ⟩ tail = ~∘pair~>
⟨ ~∘pm~> ⟩::pm⟨ f≡M' ⟩ tail = ~∘pm~>
⟨ ~∘unit~> ⟩::pm⟨ f≡M' ⟩ tail = ~∘unit~>
⟨ ~∙var∷pm■~> γ γ' i M N ≡M ⟩::pm⟨ f≡M' ⟩ tail = ~∙var∷pm∷pm~> γ γ' i M N ≡M f≡M' tail
⟨ ~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙pair∷pm■~> γ γ' x y M N ≡M ⟩::pm⟨ f≡M' ⟩ tail = ~∙pair∷pm∷pm~> γ γ' x y M N ≡M f≡M' tail
⟨ ~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙var∷l■~> γ γ' i LHS RHS ≡LHS ⟩::pm⟨ f≡M' ⟩ tail = ~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS f≡M' tail
⟨ ~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙lam∷l■~> γ γ' M LHS RHS ≡LHS ⟩::pm⟨ f≡M' ⟩ tail = ~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS f≡M' tail
⟨ ~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙unit∷l■~> γ γ' LHS RHS ≡LHS ⟩::pm⟨ f≡M' ⟩ tail = ~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS f≡M' tail
⟨ ~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙pair∷l■~> γ γ' x y LHS RHS ≡LHS ⟩::pm⟨ f≡M' ⟩ tail = ~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS f≡M' tail
⟨ ~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙var∷r■~> γ γ' i LHS RHS ≡RHS ⟩::pm⟨ f≡M' ⟩ tail = ~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS f≡M' tail
⟨ ~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙lam∷r■~> γ γ' M LHS RHS ≡RHS ⟩::pm⟨ f≡M' ⟩ tail = ~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS f≡M' tail
⟨ ~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙unit∷r■~> γ γ' LHS RHS ≡RHS ⟩::pm⟨ f≡M' ⟩ tail = ~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS f≡M' tail
⟨ ~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙pair∷r■~> γ γ' x y LHS RHS ≡RHS ⟩::pm⟨ f≡M' ⟩ tail = ~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS f≡M' tail
⟨ ~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)
⟨ ~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' tail₁ ⟩::pm⟨ f≡M' ⟩ tail = ~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' (tail₁ ⦂⦂pm⟨ f≡M' ⟩ tail)

-- T≡*Fl : {from : VState T◾} → {to : VState T◾} → (F>>T : from ~>>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS' RHS) γ') → (⟦ to ⟧◑ ≡ ⟦ from ⟧◑)
-- T≡*Fl (_ ~>ᵛᵛ⟨ F>T ⟩) f≡L' tail = T≡Fl F>T f≡L' tail
-- T≡*Fl (_ ~>ᵛᵛ⟨ F>S ⟩ S>>T) f≡L' tail with (T≡Fl F>S f≡L' tail)
-- ... | S≡F =  trans (T≡*Fl S>>T (trans S≡F f≡L') tail) S≡F

-- because of proof relevance
T≡*LHS : {from : VState T◾} → {to : VState T◾} → (F>>T : from ~>>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS' RHS) γ') → (⟦ to ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ')
T≡*LHS (_ ~>ᵛᵛ⟨ F>T ⟩) f≡L' tail = trans (T≡Fl F>T f≡L' tail) f≡L'
T≡*LHS (_ ~>ᵛᵛ⟨ F>S ⟩ S>>T) f≡L' tail = T≡*LHS S>>T (trans (T≡Fl F>S f≡L' tail) f≡L') tail

⟪_⟫::l⟨_⟩_ : {from : VState T◾} → {to : VState T◾} → (F>>T : from ~>>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS' RHS) γ') → (from ::l⟨ f≡L' ⟩ tail) ~>>ᵛᵛ (to ::l⟨ T≡*LHS F>>T f≡L' tail ⟩ tail)
⟪ _ ~>ᵛᵛ⟨ F>T ⟩ ⟫::l⟨ f≡L' ⟩ tail = (_ ::l⟨ _ ⟩ tail) ~>ᵛᵛ⟨ (⟨ F>T ⟩::l⟨ f≡L' ⟩ tail) ⟩
⟪ from ~>ᵛᵛ⟨ F>S ⟩ S>>T ⟫::l⟨ f≡L' ⟩ tail = (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ⟨ (⟨ F>S ⟩::l⟨ f≡L' ⟩ tail) ⟩ (⟪ S>>T ⟫::l⟨ trans (T≡Fl F>S f≡L' tail) f≡L' ⟩ tail)


T≡*RHS : {from : VState T◾} → {to : VState T◾} → (F>T : from ~>>ᵛᵛ to) → {LHS : Γ' ⊢ᵛ A} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS' : Γ' ⊢ᵛ T◾} → (f≡R' : ⟦ from ⟧◑ ≡ ⟦ RHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS RHS') γ') → (⟦ to ⟧◑ ≡ ⟦ RHS' ⟧ᵛ γ')
T≡*RHS (_ ~>ᵛᵛ⟨ F>T ⟩) f≡R' tail = trans (T≡Fr F>T f≡R' tail) f≡R'
T≡*RHS (_ ~>ᵛᵛ⟨ F>S ⟩ S>>T) f≡R' tail = T≡*RHS S>>T (trans (T≡Fr F>S f≡R' tail) f≡R') tail

⟪_⟫::r⟨_⟩_ : {from : VState T◾} → {to : VState T◾} → (F>>T : from ~>>ᵛᵛ to) → {LHS : Γ' ⊢ᵛ A} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS' : Γ' ⊢ᵛ T◾} → (f≡R' : ⟦ from ⟧◑ ≡ ⟦ RHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS RHS') γ') → (from ::r⟨ f≡R' ⟩ tail) ~>>ᵛᵛ (to ::r⟨ T≡*RHS F>>T f≡R' tail ⟩ tail)
⟪ from ~>ᵛᵛ⟨ F>T ⟩ ⟫::r⟨ f≡R' ⟩ tail = (from ::r⟨ f≡R' ⟩ tail) ~>ᵛᵛ⟨ (⟨ F>T ⟩::r⟨ f≡R' ⟩ tail) ⟩
⟪ from ~>ᵛᵛ⟨ F>S ⟩ S>>T ⟫::r⟨ f≡R' ⟩ tail = (from ::r⟨ f≡R' ⟩ tail) ~>ᵛᵛ⟨ (⟨ F>S ⟩::r⟨ f≡R' ⟩ tail) ⟩ (⟪ S>>T ⟫::r⟨ trans (T≡Fr F>S f≡R' tail) f≡R' ⟩ tail)


T≡*M : {from : VState (T◾₁ `× T◾₂)} → {to : VState (T◾₁ `× T◾₂)} → (F>>T : from ~>>ᵛᵛ to) → {M' : Γ' ⊢ᵛ (T◾₁ `× T◾₂)} → {γ' : ⟦ Γ' ⟧ˣ} → {N : (Γ' ∙ T◾₁ ∙ T◾₂) ⊢ᵛ C} → (f≡M' : ⟦ from ⟧◑ ≡ ⟦ M' ⟧ᵛ γ') → (tail : valStack T◾ (pm M' N) γ') → (⟦ to ⟧◑ ≡ ⟦ M' ⟧ᵛ γ')
T≡*M (_ ~>ᵛᵛ⟨ F>T ⟩) f≡M' tail = trans (T≡Fpm F>T f≡M' tail) f≡M'
T≡*M (_ ~>ᵛᵛ⟨ F>S ⟩ S>>T) f≡M' tail = T≡*M S>>T (trans (T≡Fpm F>S f≡M' tail) f≡M') tail

⟪_⟫::pm⟨_⟩_ : {from : VState (T◾₁ `× T◾₂)} → {to : VState (T◾₁ `× T◾₂)} → (F>>T : from ~>>ᵛᵛ to) → {M' : Γ' ⊢ᵛ (T◾₁ `× T◾₂)} → {γ' : ⟦ Γ' ⟧ˣ} → {N : (Γ' ∙ T◾₁ ∙ T◾₂) ⊢ᵛ C} → (f≡M' : ⟦ from ⟧◑ ≡ ⟦ M' ⟧ᵛ γ') → (tail : valStack T◾ (pm M' N) γ') → (from ::pm⟨ f≡M' ⟩ tail) ~>>ᵛᵛ (to ::pm⟨ T≡*M F>>T f≡M' tail ⟩ tail)
⟪ from ~>ᵛᵛ⟨ F>T ⟩ ⟫::pm⟨ f≡M' ⟩ tail = (from ::pm⟨ f≡M' ⟩ tail) ~>ᵛᵛ⟨ (⟨ F>T ⟩::pm⟨ f≡M' ⟩ tail) ⟩
⟪ from ~>ᵛᵛ⟨ F>S ⟩ S>>T ⟫::pm⟨ f≡M' ⟩ tail = (from ::pm⟨ f≡M' ⟩ tail) ~>ᵛᵛ⟨ (⟨ F>S ⟩::pm⟨ f≡M' ⟩ tail) ⟩ (⟪ S>>T ⟫::pm⟨ trans (T≡Fpm F>S f≡M' tail) f≡M' ⟩ tail)
-}
