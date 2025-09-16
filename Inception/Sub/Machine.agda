-- {-# OPTIONS --show-implicit #-}

module Inception.Sub.Machine (R : Set) where

open import Function.Base using (id)
open Function.Base using (id)

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
  Γ' Γ'' Δ' : Ctx

data valStack : (Γ ⊢ᵛ A) → ⟦ Γ ⟧ˣ → Set

infix 25 _,_■
infixr 25 _,_∷pm⟨_⟩_
infixr 25 _,_∷l⟨_⟩_
infixr 25 _,_∷r⟨_⟩_

data valStack where

    _,_■ : (M : Γ ⊢ᵛ A) → (γ : ⟦ Γ ⟧ˣ)
        ---------
        → valStack M γ

    _,_∷pm⟨_⟩_ : (M : Γ ⊢ᵛ A `× B) -> (γ : ⟦ Γ ⟧ˣ) -> {M' : Γ' ⊢ᵛ A `× B} -> {γ' : ⟦ Γ' ⟧ˣ} -> {N : (Γ' ∙ A ∙ B) ⊢ᵛ C} → (M≡M' : ⟦ M ⟧ᵛ γ ≡ ⟦ M' ⟧ᵛ γ') -> valStack (pm M' N) γ'
        ---------
        → valStack M γ

    _,_∷l⟨_⟩_ : (LHS : Γ ⊢ᵛ A) -> (γ : ⟦ Γ ⟧ˣ) -> {LHS' : Γ' ⊢ᵛ A} -> {γ' : ⟦ Γ' ⟧ˣ} -> (L≡L' : ⟦ LHS ⟧ᵛ γ ≡ ⟦ LHS' ⟧ᵛ γ') -> {RHS : Γ' ⊢ᵛ B} -> valStack (pair LHS' RHS) γ'
        ---------
        → valStack LHS γ

    _,_∷r⟨_⟩_ : (RHS : Γ ⊢ᵛ A) -> (γ : ⟦ Γ ⟧ˣ) -> {RHS' : Γ' ⊢ᵛ A} -> {γ' : ⟦ Γ' ⟧ˣ} -> (R≡R' : ⟦ RHS ⟧ᵛ γ ≡ ⟦ RHS' ⟧ᵛ γ') -> {LHS : Γ' ⊢ᵛ B} -> valStack (pair LHS RHS') γ'
        ---------
        → valStack RHS γ

infix 20 ∘_
infix 20 ∙_

data VState : Set where

     ∘_ : {M : Γ ⊢ᵛ A} → {γ : ⟦ Γ ⟧ˣ} → valStack M γ → VState

     ∙_ : {M : Γ ⊢ᵛ A} → {γ : ⟦ Γ ⟧ˣ} → valStack M γ → VState

infix 15 _~>ᵛᵛ_

eq-pair∷pm : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (x : Γ ⊢ᵛ X) -> (y : Γ ⊢ᵛ Y) → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z)
                 → (≡M : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ')
                 → ⟦ N ⟧ᵛ ((γ' , ⟦ x ⟧ᵛ γ) , ⟦ y ⟧ᵛ γ) ≡ ⟦ (pm M N) ⟧ᵛ γ'
eq-pair∷pm γ γ' γ'' x y M N ≡M =         ⟦ N ⟧ᵛ ((γ' , ⟦ x ⟧ᵛ γ) , ⟦ y ⟧ᵛ γ)
                                ≡⟨ refl ⟩
                                    (assocl ； ⟦ N ⟧ᵛ) (γ' , ⟦ pair x y ⟧ᵛ γ)
                                ≡⟨  cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p) ) ≡M ⟩
                                    (assocl ； ⟦ N ⟧ᵛ) (γ' , ⟦ M ⟧ᵛ γ')
                                ≡⟨ refl ⟩
                                    (< idf , ⟦ M ⟧ᵛ > ； assocl ； ⟦ N ⟧ᵛ) γ'
                                ≡⟨ refl ⟩
                                    ⟦ (pm M N) ⟧ᵛ γ' ∎

eq-lam∷l∷pm :   (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
     → (M : (Γ ∙ X) ⊢ᶜ Y)
     → (LHS : Γ' ⊢ᵛ X `⇒ Y) → (RHS : Γ' ⊢ᵛ Z)
     → (M' : Γ'' ⊢ᵛ (X `⇒ Y) `× Z)
     → (≡LHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
     → ⟦ pair (var h) (wk-val (wk-wk wk-id) RHS) ⟧ᵛ (γ' , ⟦ lam M ⟧ᵛ γ) ≡ ⟦ M' ⟧ᵛ γ''
eq-lam∷l∷pm γ γ' γ'' M LHS RHS M' ≡LHS ≡M' =  ⟦ pair (var h) (wk-val (wk-wk wk-id) RHS) ⟧ᵛ (γ' , ⟦ lam M ⟧ᵛ γ)
                                         ≡⟨ refl ⟩
                                           < ⟦ var h ⟧ᵛ , ⟦ wk-val (wk-wk wk-id) RHS ⟧ᵛ > (γ' , ⟦ lam M ⟧ᵛ γ)
                                         ≡⟨ refl ⟩
                                            (⟦ var h ⟧ᵛ (γ' , ⟦ lam M ⟧ᵛ γ) ,  ⟦ wk-val (wk-wk wk-id) RHS ⟧ᵛ (γ' , ⟦ lam M ⟧ᵛ γ))
                                         ≡⟨ refl ⟩
                                            (⟦ lam M ⟧ᵛ γ , ⟦ RHS ⟧ᵛ γ')
                                         ≡⟨ cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS ⟩
                                            (⟦ LHS ⟧ᵛ γ' , ⟦ RHS ⟧ᵛ γ')
                                         ≡⟨ refl ⟩
                                            ⟦ pair LHS RHS ⟧ᵛ γ'
                                         ≡⟨ ≡M' ⟩
                                          ⟦ M' ⟧ᵛ γ'' ∎

eq-lam∷r∷pm : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
           → (M : (Γ ∙ X) ⊢ᶜ Y)
           → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `⇒ Y)
           → (M' : Γ'' ⊢ᵛ Z `× (X `⇒ Y))
           → (≡RHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
           → ⟦ pair (wk-val (wk-wk wk-id) LHS) (var h) ⟧ᵛ (γ' , ⟦ lam M ⟧ᵛ γ) ≡ ⟦ M' ⟧ᵛ γ''
eq-lam∷r∷pm γ γ' γ'' M LHS RHS M' ≡RHS ≡M' =   ⟦ pair (wk-val (wk-wk wk-id) LHS) (var h) ⟧ᵛ (γ' , ⟦ lam M ⟧ᵛ γ)
                                              ≡⟨ refl ⟩
                                                (⟦ LHS ⟧ᵛ γ' , ⟦ lam M ⟧ᵛ γ)
                                              ≡⟨  cong (λ t → (⟦ LHS ⟧ᵛ γ' , t)) ≡RHS ⟩
                                                 (⟦ LHS ⟧ᵛ γ' , ⟦ RHS ⟧ᵛ γ')
                                              ≡⟨ ≡M' ⟩
                                               ⟦ M' ⟧ᵛ γ'' ∎


data _~>ᵛᵛ_ : VState → VState → Set where

     -- (∘ T ∷ tail) transitions with T = var i or T = unit or T = lam M
     ~∘var~>   : (γ : ⟦ Γ ⟧ˣ) → (i : Γ ∋ A)
                 → (tail : valStack (var i) γ)
                  → ∘ tail ~>ᵛᵛ ∙ tail

     ~∘unit~> : (γ : ⟦ Γ ⟧ˣ)
                 → (tail : valStack unit γ)
                 → ∘ tail ~>ᵛᵛ ∙ tail

     ~∘lam~> : (γ : ⟦ Γ ⟧ˣ)
                  → (M : (Γ ∙ X) ⊢ᶜ Y)
                  → (tail : valStack (lam M) γ)
                  → ∘ tail ~>ᵛᵛ ∙ tail

     -- (∙ pair ∷ pm ∷ tail) transitions
     ~∙pair∷pm∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ X' `× Y')
                 → (M' : Γ'' ⊢ᵛ X' `× Y') → (N' : (Γ'' ∙ X' ∙ Y') ⊢ᵛ C)
                 → (≡M : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ') → (≡M' : ⟦ (pm M N) ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack (pm M' N') γ'')
                 →   ∙ pair x y , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                      ∘ N , ((γ' ,  ⟦ x ⟧ᵛ γ) ,  ⟦ y ⟧ᵛ γ) ∷pm⟨ trans (eq-pair∷pm γ γ' γ'' x y M N ≡M) ≡M' ⟩ tail

     ~∙pair∷pm∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (x : Γ ⊢ᵛ X) -> (y : Γ ⊢ᵛ Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z)
                 → (LHS : Γ'' ⊢ᵛ Z) → (RHS : Γ'' ⊢ᵛ Z')
                 → (≡M : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ') → (≡LHS : ⟦ (pm M N) ⟧ᵛ γ' ≡ ⟦ LHS ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS RHS) γ'')
                 ->    ∙ pair x y , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ∷l⟨ ≡LHS ⟩ tail
                      ~>ᵛᵛ
                       ∘ N , ((γ' ,  ⟦ x ⟧ᵛ γ) ,  ⟦ y ⟧ᵛ γ) ∷l⟨ trans (eq-pair∷pm γ γ' γ'' x y M N ≡M) ≡LHS ⟩ tail

     ~∙pair∷pm∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (x : Γ ⊢ᵛ X) -> (y : Γ ⊢ᵛ Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z')
                 → (LHS : Γ'' ⊢ᵛ Z) → (RHS : Γ'' ⊢ᵛ Z')
                 → (≡M : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ') → (≡RHS : ⟦ (pm M N) ⟧ᵛ γ' ≡ ⟦ RHS ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS RHS) γ'')
                 ->    ∙ pair x y , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ∷r⟨ ≡RHS ⟩ tail
                      ~>ᵛᵛ
                       ∘ N , ((γ' ,  ⟦ x ⟧ᵛ γ) ,  ⟦ y ⟧ᵛ γ) ∷r⟨ trans (eq-pair∷pm γ γ' γ'' x y M N ≡M) ≡RHS ⟩ tail

     -- (∘ pm ∷ tail) transition
     ~∘pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (M : Γ ⊢ᵛ X `× Y) → (N : (Γ ∙ X ∙ Y) ⊢ᵛ X' `× Y')
                 → (tail : valStack (pm M N) γ)
                 ->    ∘ tail
                      ~>ᵛᵛ
                       ∘ M , γ ∷pm⟨ refl ⟩ tail

     -- (∙ T ∷ (_ , RHS) ∷ tail) transitions with T = lam M
     ~∙lam∷l∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ X `⇒ Y) → (RHS : Γ' ⊢ᵛ Z)
                 → (M' : Γ'' ⊢ᵛ (X `⇒ Y) `× Z) → (N' : (Γ'' ∙ (X `⇒ Y) ∙ Z) ⊢ᵛ Z')
                 → (≡LHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack (pm M' N') γ'')
                 →   ∙ lam M , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) , (γ' ,  ⟦ lam M ⟧ᵛ γ) ∷pm⟨ eq-lam∷l∷pm γ γ' γ'' M LHS RHS M' ≡LHS ≡M' ⟩ tail

{-
     ~∙lam∷l∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ X `⇒ Y) → (RHS : Γ' ⊢ᵛ Z)
                 → (LHS' : Γ'' ⊢ᵛ (X `⇒ Y) `× Z) → (RHS' : Γ'' ⊢ᵛ Z')
                 → (≡LHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙ lam M , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail

     ~∙lam∷l∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ X `⇒ Y) → (RHS : Γ' ⊢ᵛ Z)
                 → (LHS' : Γ'' ⊢ᵛ Z') → (RHS' : Γ'' ⊢ᵛ (X `⇒ Y) `× Z)
                 → (≡LHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙ lam M , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail

     -- (∙ T ∷ (_ , RHS) ∷ tail) transitions with T = pair x y
     ~∙pair∷l∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (x : Γ ⊢ᵛ X) -> (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ X `× Y) → (RHS : Γ' ⊢ᵛ Z)
                 → (M' : Γ'' ⊢ᵛ (X `× Y) `× Z) → (N' : (Γ'' ∙ (X `× Y) ∙ Z) ⊢ᵛ Z')
                 → (≡LHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack (pm M' N') γ'')
                 →   ∙ pair x y , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail

     ~∙pair∷l∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (x : Γ ⊢ᵛ X) -> (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ X `× Y) → (RHS : Γ' ⊢ᵛ Z)
                 → (LHS' : Γ'' ⊢ᵛ (X `× Y) `× Z) → (RHS' : Γ'' ⊢ᵛ Z')
                 → (≡LHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙ pair x y , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail

     ~∙pair∷l∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (x : Γ ⊢ᵛ X) -> (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ X `× Y) → (RHS : Γ' ⊢ᵛ Z)
                 → (LHS' : Γ'' ⊢ᵛ Z') → (RHS' : Γ'' ⊢ᵛ (X `× Y) `× Z)
                 → (≡LHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙ pair x y , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail

     -- (∙ T ∷ (_ , RHS) ∷ tail) transitions with T = var i
     ~∙var∷l∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (i : Γ ∋ X)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → (M' : Γ'' ⊢ᵛ X `× Y) → (N' : (Γ'' ∙ X ∙ Y) ⊢ᵛ Z)
                 → (≡LHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack (pm M' N') γ'')
                 →   ∙ var i , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail

     ~∙var∷l∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (i : Γ ∋ X)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → (LHS' : Γ'' ⊢ᵛ X `× Y) → (RHS' : Γ'' ⊢ᵛ Z)
                 → (≡LHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙ var i , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail

     ~∙var∷l∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (i : Γ ∋ X)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → (LHS' : Γ'' ⊢ᵛ Z) → (RHS' : Γ'' ⊢ᵛ X `× Y)
                 → (≡LHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙ var i , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail

     -- (∙ T ∷ (_ , RHS) ∷ tail) transitions with T = unit
     ~∙unit∷l∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (LHS : Γ' ⊢ᵛ `Unit) → (RHS : Γ' ⊢ᵛ Y)
                 → (M' : Γ'' ⊢ᵛ `Unit `× Y) → (N' : (Γ'' ∙ `Unit ∙ Y) ⊢ᵛ Z)
                 → (≡LHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack (pm M' N') γ'')
                 →   ∙ unit , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail

     ~∙unit∷l∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (LHS : Γ' ⊢ᵛ `Unit) → (RHS : Γ' ⊢ᵛ Y)
                 → (LHS' : Γ'' ⊢ᵛ `Unit `× Y) → (RHS' : Γ'' ⊢ᵛ Z)
                 → (≡LHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙ unit , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail

     ~∙unit∷l∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (LHS : Γ' ⊢ᵛ `Unit) → (RHS : Γ' ⊢ᵛ Y)
                 → (LHS' : Γ'' ⊢ᵛ Z) → (RHS' : Γ'' ⊢ᵛ `Unit `× Y)
                 → (≡LHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙ unit , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail
-}

     --------------------------------------------------------------------------------------
     -- (∙ T ∷ (LHS , _) ∷ tail) transitions with T = lam M
     ~∙lam∷r∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `⇒ Y)
                 → (M' : Γ'' ⊢ᵛ Z `× (X `⇒ Y)) → (N' : (Γ'' ∙ Z ∙ (X `⇒ Y)) ⊢ᵛ Z')
                 → (≡RHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack (pm M' N') γ'')
                 →   ∙ lam M , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∙ pair (wk-val (wk-wk wk-id) LHS) (var h) , (γ' , ⟦ lam M ⟧ᵛ γ) ∷pm⟨ eq-lam∷r∷pm γ γ' γ'' M LHS RHS M' ≡RHS ≡M' ⟩ tail
