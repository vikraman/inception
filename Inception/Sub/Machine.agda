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
  A' B' C' D' X Y Z X' Y' Z' : Ty
  Γ' : Ctx

data valStack : (Γ ⊢ᵛ A) → ⟦ Γ ⟧ˣ → Set

infix 25 _,_■
infixr 25 _,_∷pm⟨_⟩_
infixr 25 _,_∷l⟨_⟩_
infixr 25 _,_∷r⟨_⟩_

data valStack where

    _,_■ : (M : Γ ⊢ᵛ A) → (γ : ⟦ Γ ⟧ˣ)
        ---------
        → valStack M γ

    _,_∷pm⟨_⟩_ : (M : Γ ⊢ᵛ A `× B) -> (γ : ⟦ Γ ⟧ˣ) -> {M' : Γ' ⊢ᵛ A `× B} -> {γ' : ⟦ Γ' ⟧ˣ} -> (M≡M' : ⟦ M ⟧ᵛ γ ≡ ⟦ M' ⟧ᵛ γ') -> {N : (Γ' ∙ A ∙ B) ⊢ᵛ C} -> valStack (pm M' N) γ'
        ---------
        → valStack M γ

    _,_∷l⟨_⟩_ : (L : Γ ⊢ᵛ A) -> (γ : ⟦ Γ ⟧ˣ) -> {L' : Γ' ⊢ᵛ A} -> {γ' : ⟦ Γ' ⟧ˣ} -> (L≡L' : ⟦ L ⟧ᵛ γ ≡ ⟦ L' ⟧ᵛ γ') -> {R : Γ' ⊢ᵛ B} -> valStack (pair L' R) γ'
        ---------
        → valStack L γ

    _,_∷r⟨_⟩_ : (RHS : Γ ⊢ᵛ A) -> (γ : ⟦ Γ ⟧ˣ) -> {R' : Γ' ⊢ᵛ A} -> {γ' : ⟦ Γ' ⟧ˣ} -> (R≡R' : ⟦ RHS ⟧ᵛ γ ≡ ⟦ R' ⟧ᵛ γ') -> {L : Γ' ⊢ᵛ B} -> valStack (pair L R') γ'
        ---------
        → valStack RHS γ

infix 20 ∘_
infix 20 ∙_

data State : Set where

     ∘_ : {M : Γ ⊢ᵛ A} → {γ : ⟦ Γ ⟧ˣ} → valStack M γ → State

     ∙_ : {M : Γ ⊢ᵛ A} → {γ : ⟦ Γ ⟧ˣ} → valStack M γ → State

infix 15 _~>_

data _~>_ : State → State → Set where

     ~∘var■~>   : {i : Γ ∋ A} → {γ : ⟦ Γ ⟧ˣ}
                  → ∘ var i , γ ■ ~> ∙ var i , γ ■

     -- should get stuck on these
     {-
     ~∘var∷pm~> : {i : Γ ∋ A `× B} → {γ : ⟦ Γ ⟧ˣ}
                 -> {M' : Γ ⊢ᵛ A `× B} -> {γ' : ⟦ Γ ⟧ˣ} -> {M≡M' : ⟦ var i ⟧ᵛ γ ≡ ⟦ M' ⟧ᵛ γ'}
                 -> {N : (Γ ∙ A ∙ B) ⊢ᵛ C}
                 -> (tail : valStack (pm M' N) γ')
                 -> ∘ var i , γ ∷pm⟨ M≡M' ⟩ tail ~> ∙ var i , γ ∷pm⟨ M≡M' ⟩ tail

     ~∙var∷pm∷pm~> : {i : Γ ∋ A `× B} → {γ : ⟦ Γ ⟧ˣ}
                 -> {M' : Γ ⊢ᵛ A `× B} -> {γ' : ⟦ Γ ⟧ˣ} -> {≡M' : ⟦ var i ⟧ᵛ γ ≡ ⟦ M' ⟧ᵛ γ'}
                 -> {N : (Γ ∙ A ∙ B) ⊢ᵛ X `× Y}
                 -> {M'' : Γ ⊢ᵛ X `× Y}
                 -> {γ'' : ⟦ Γ ⟧ˣ} -> {≡M'' : ⟦ pm M' N ⟧ᵛ γ' ≡ ⟦ M'' ⟧ᵛ γ''} -> {N' : (Γ ∙ X ∙ Y) ⊢ᵛ C}
                 -> {tail : valStack (pm M'' N') γ''}
                 ->  ∙ var i , γ ∷pm⟨ ≡M' ⟩ pm M' N ,  γ' ∷pm⟨  ≡M'' ⟩ tail
                      ~>
                     ∘ N , ((γ , {!!}) , {!!}) ∷pm⟨ {!!} ⟩ tail

     ~∙var∷pm∷pm~> : {i : Γ ∋ A `× B} → {γ : ⟦ Γ ⟧ˣ}
                 -> {M' : Γ ⊢ᵛ A `× B} -> {γ' : ⟦ Γ ⟧ˣ} -> {≡M' : ⟦ var i ⟧ᵛ γ ≡ ⟦ M' ⟧ᵛ γ'}
                 -> {N : (Γ ∙ A ∙ B) ⊢ᵛ X `× Y}
                 -> {M'' : Γ ⊢ᵛ X `× Y}
                 -> {γ'' : ⟦ Γ ⟧ˣ} -> {≡M'' : ⟦ pm M' N ⟧ᵛ γ' ≡ ⟦ M'' ⟧ᵛ γ''} -> {N' : (Γ ∙ X ∙ Y) ⊢ᵛ C}
                 -> {tail : valStack (pm M'' N') γ''}
                 ->  ∙ var i , γ ∷pm⟨ ≡M' ⟩ pm M' N ,  γ' ∷pm⟨  ≡M'' ⟩ tail
                      ~>
                     ∘ N , ((γ , {!!}) , {!!}) ∷pm⟨ {!!} ⟩ tail
    -}

     ~∙pair∷pm∷pm~> : {x : Γ ⊢ᵛ X} -> {y : Γ ⊢ᵛ Y} → {γ : ⟦ Γ ⟧ˣ}
                 -> {M' : Γ ⊢ᵛ X `× Y} -> {γ' : ⟦ Γ ⟧ˣ} -> {≡M' : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ M' ⟧ᵛ γ'}
                 -> {N : (Γ ∙ X ∙ Y) ⊢ᵛ X' `× Y'}
                 -> {M'' : Γ ⊢ᵛ X' `× Y'}
                 -> {γ'' : ⟦ Γ ⟧ˣ} -> {≡M'' : ⟦ pm M' N ⟧ᵛ γ' ≡ ⟦ M'' ⟧ᵛ γ''} -> {N' : (Γ ∙ X' ∙ Y') ⊢ᵛ C}
                 -> {tail : valStack (pm M'' N') γ''}
                 ->  ∙ pair x y , γ ∷pm⟨ ≡M' ⟩ pm M' N ,  γ' ∷pm⟨ ≡M'' ⟩ tail
                      ~>
                     ∘ N , ((γ , ⟦ x ⟧ᵛ γ) , ⟦ y ⟧ᵛ γ) ∷pm⟨ {!!} ⟩ tail
