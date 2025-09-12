-- {-# OPTIONS --show-implicit #-}

module Inception.Sub.Machine (R : Set) where

open import Data.List
open import Data.Unit
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

variable
  X Y Z : Ty

data valStack : (Γ ⊢ᵛ A) → ⟦ Γ ⟧ˣ → Set

data valStack where

    _,_■ : (M : Γ ⊢ᵛ A) → (γ : ⟦ Γ ⟧ˣ)
        ---------
        → valStack M γ

    _,_∷pm_ : (M : Γ ⊢ᵛ A `× B) -> (γ : ⟦ Γ ⟧ˣ) -> {M' : Γ ⊢ᵛ A `× B} -> {γ' : ⟦ Γ ⟧ˣ} -> {M≡M' : ⟦ M ⟧ᵛ γ ≡ ⟦ M' ⟧ᵛ γ'} -> {N : (Γ ∙ A ∙ B) ⊢ᵛ C} -> valStack (pm M' N) γ'
        ---------
        → valStack M γ

    _,_∷l_ : (L : Γ ⊢ᵛ A) -> (γ : ⟦ Γ ⟧ˣ) -> {L' : Γ ⊢ᵛ A} -> {γ' : ⟦ Γ ⟧ˣ} -> {L≡L' : ⟦ L ⟧ᵛ γ ≡ ⟦ L' ⟧ᵛ γ'} -> {R : Γ ⊢ᵛ B} -> valStack (pair L' R) γ'
        ---------
        → valStack L γ

    _,_∷r_ : (R : Γ ⊢ᵛ A) -> (γ : ⟦ Γ ⟧ˣ) -> {R' : Γ ⊢ᵛ A} -> {γ' : ⟦ Γ ⟧ˣ} -> {R≡R' : ⟦ R ⟧ᵛ γ ≡ ⟦ R' ⟧ᵛ γ'} -> {L : Γ ⊢ᵛ B} -> valStack (pair L R') γ'
        ---------
        → valStack R γ
