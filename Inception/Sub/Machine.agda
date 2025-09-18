-- {-# OPTIONS --show-implicit #-}

module Inception.Sub.Machine (R : Set) where

open import Function.Base using (id)
open Function.Base using (id)

open import Data.List
open import Data.Unit
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

variable
  A' B' C' D' X Y Z X' Y' Z' : Ty
  Γ' Γ'' Δ' : Ctx


infix 30 _,_■
infixr 25 _,_∷pm⟨_⟩_
infixr 25 _,_∷l⟨_⟩_
infixr 25 _,_∷r⟨_⟩_

data valStack : (Γ ⊢ᵛ A) → ⟦ Γ ⟧ˣ → Set where

    _,_■ : (M : Γ ⊢ᵛ A) → (γ : ⟦ Γ ⟧ˣ) → valStack M γ

    _,_∷pm⟨_⟩_ : (M : Γ ⊢ᵛ A `× B) → (γ : ⟦ Γ ⟧ˣ) → {M' : Γ' ⊢ᵛ A `× B} → {γ' : ⟦ Γ' ⟧ˣ} → {N : (Γ' ∙ A ∙ B) ⊢ᵛ C} → (M≡M' : ⟦ M ⟧ᵛ γ ≡ ⟦ M' ⟧ᵛ γ') → valStack (pm M' N) γ'
        → valStack M γ

    _,_∷l⟨_⟩_ : (LHS : Γ ⊢ᵛ A) → (γ : ⟦ Γ ⟧ˣ) → {LHS' : Γ' ⊢ᵛ A} → {γ' : ⟦ Γ' ⟧ˣ} → (L≡L' : ⟦ LHS ⟧ᵛ γ ≡ ⟦ LHS' ⟧ᵛ γ') → {RHS : Γ' ⊢ᵛ B} → valStack (pair LHS' RHS) γ'
        → valStack LHS γ

    _,_∷r⟨_⟩_ : (RHS : Γ ⊢ᵛ A) → (γ : ⟦ Γ ⟧ˣ) → {RHS' : Γ' ⊢ᵛ A} → {γ' : ⟦ Γ' ⟧ˣ} → (R≡R' : ⟦ RHS ⟧ᵛ γ ≡ ⟦ RHS' ⟧ᵛ γ') → {LHS : Γ' ⊢ᵛ B} → valStack (pair LHS RHS') γ'
        → valStack RHS γ


infix 20 ∘_

data VState : Set where

     ∘_ : {M : Γ ⊢ᵛ A} → {γ : ⟦ Γ ⟧ˣ} → valStack M γ → VState

     ∙[var]_ : {i : Γ ∋ X} → {γ : ⟦ Γ ⟧ˣ} → valStack (var i) γ → VState

     ∙[lam]_ : {M : (Γ ∙ X) ⊢ᶜ Y} → {γ : ⟦ Γ ⟧ˣ} → valStack (lam M) γ → VState

     ∙[unit]_ : {γ : ⟦ Γ ⟧ˣ} → valStack unit γ → VState

     ∙[pair]_ : {x : Γ ⊢ᵛ X} → {y : Γ ⊢ᵛ Y} → {γ : ⟦ Γ ⟧ˣ} → valStack (pair x y) γ → VState


infix 15 _~>ᵛᵛ_

data _~>ᵛᵛ_ : VState → VState → Set where

     ~∘var~>   : {γ : ⟦ Γ ⟧ˣ} → {i : Γ ∋ X} → {tail : valStack (var i) γ} → ∘ tail ~>ᵛᵛ ∙[var] tail

     ~∘lam~> : {γ : ⟦ Γ ⟧ˣ} → {M : (Γ ∙ X) ⊢ᶜ Y} → {tail : valStack (lam M) γ} → ∘ tail ~>ᵛᵛ ∙[lam] tail

     ~∘pair~> : {γ : ⟦ Γ ⟧ˣ} → {LHS : Γ ⊢ᵛ X} → {RHS : Γ ⊢ᵛ Y} → {tail : valStack (pair LHS RHS) γ} → ∘ tail ~>ᵛᵛ ∘ LHS , γ ∷l⟨ refl ⟩ tail

     ~∘pm~> : {γ : ⟦ Γ ⟧ˣ} → {M : Γ ⊢ᵛ X `× Y} → {N : (Γ ∙ X ∙ Y) ⊢ᵛ Z} → {tail : valStack (pm M N) γ} → ∘ tail ~>ᵛᵛ ∘ M , γ ∷pm⟨ refl ⟩ tail

     ~∘unit~> : {γ : ⟦ Γ ⟧ˣ} → {tail : valStack unit γ} → ∘ tail ~>ᵛᵛ ∙[unit] tail

     -- (∙ var ∷ pm ∷ tail) transitions

     ~∙var∷pm■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (i : Γ ∋ X `× Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z')
                 → (≡M : ⟦ var i ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ')
                 →    ∙[var] var i , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ■
                      ~>ᵛᵛ
                        ∘ N , ((γ' , proj₁ (⟦ var i ⟧ᵛ γ)) , proj₂ (⟦ var i ⟧ᵛ γ)) ■

     ~∙var∷pm∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (i : Γ ∋ X `× Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ X' `× Y')
                 → {M' : Γ'' ⊢ᵛ X' `× Y'} → {N' : (Γ'' ∙ X' ∙ Y') ⊢ᵛ Z}
                 → (≡M : ⟦ var i ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ') → (≡M' : ⟦ (pm M N) ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack (pm M' N') γ'')
                 →   ∙[var] var i , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                      ∘ N , ((γ' ,  proj₁ (⟦ var i ⟧ᵛ γ)) ,  proj₂ (⟦ var i ⟧ᵛ γ)) ∷pm⟨ trans (cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p) ) ≡M) ≡M' ⟩ tail

     ~∙var∷pm∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (i : Γ ∋ X `× Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z)
                 → {LHS : Γ'' ⊢ᵛ Z} → {RHS : Γ'' ⊢ᵛ Z'}
                 → (≡M : ⟦ var i ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ') → (≡LHS : ⟦ (pm M N) ⟧ᵛ γ' ≡ ⟦ LHS ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS RHS) γ'')
                 →    ∙[var] var i , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ∷l⟨ ≡LHS ⟩ tail
                      ~>ᵛᵛ
                       ∘ N , ((γ' ,  proj₁ (⟦ var i ⟧ᵛ γ)) ,  proj₂ (⟦ var i ⟧ᵛ γ)) ∷l⟨ trans (cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p) ) ≡M) ≡LHS ⟩ tail

     ~∙var∷pm∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (i : Γ ∋ X `× Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z')
                 → {LHS : Γ'' ⊢ᵛ Z} → {RHS : Γ'' ⊢ᵛ Z'}
                 → (≡M : ⟦ var i ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ') → (≡RHS : ⟦ (pm M N) ⟧ᵛ γ' ≡ ⟦ RHS ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS RHS) γ'')
                 →    ∙[var] var i , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ∷r⟨ ≡RHS ⟩ tail
                      ~>ᵛᵛ
                       ∘ N , ((γ' , proj₁ (⟦ var i ⟧ᵛ γ)) , proj₂ (⟦ var i ⟧ᵛ γ)) ∷r⟨ trans (cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p) ) ≡M) ≡RHS ⟩ tail

     -- (∙ pair ∷ pm ∷ tail) transitions
     ~∙pair∷pm■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z')
                 → (≡M : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ')
                 →    ∙[pair] pair x y , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ■
                      ~>ᵛᵛ
                       ∘ N , ((γ' ,  ⟦ x ⟧ᵛ γ) ,  ⟦ y ⟧ᵛ γ) ■

     ~∙pair∷pm∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ X' `× Y')
                 → {M' : Γ'' ⊢ᵛ X' `× Y'} → {N' : (Γ'' ∙ X' ∙ Y') ⊢ᵛ C}
                 → (≡M : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ') → (≡M' : ⟦ (pm M N) ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack (pm M' N') γ'')
                 →   ∙[pair] pair x y , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                      ∘ N , ((γ' ,  ⟦ x ⟧ᵛ γ) ,  ⟦ y ⟧ᵛ γ) ∷pm⟨ trans (cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p) ) ≡M) ≡M' ⟩ tail

     ~∙pair∷pm∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z)
                 → {LHS : Γ'' ⊢ᵛ Z} → {RHS : Γ'' ⊢ᵛ Z'}
                 → (≡M : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ') → (≡LHS : ⟦ (pm M N) ⟧ᵛ γ' ≡ ⟦ LHS ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS RHS) γ'')
                 →    ∙[pair] pair x y , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ∷l⟨ ≡LHS ⟩ tail
                      ~>ᵛᵛ
                       ∘ N , ((γ' ,  ⟦ x ⟧ᵛ γ) ,  ⟦ y ⟧ᵛ γ) ∷l⟨ trans (cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p) ) ≡M) ≡LHS ⟩ tail

     ~∙pair∷pm∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z')
                 → {LHS : Γ'' ⊢ᵛ Z} → {RHS : Γ'' ⊢ᵛ Z'}
                 → (≡M : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ') → (≡RHS : ⟦ (pm M N) ⟧ᵛ γ' ≡ ⟦ RHS ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS RHS) γ'')
                 →    ∙[pair] pair x y , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ∷r⟨ ≡RHS ⟩ tail
                      ~>ᵛᵛ
                       ∘ N , ((γ' ,  ⟦ x ⟧ᵛ γ) ,  ⟦ y ⟧ᵛ γ) ∷r⟨ trans (cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p) ) ≡M) ≡RHS ⟩ tail

     -------------------------------------------------------------------------------------

     -- (∙ T ∷ (_ , RHS) ∷ tail) transitions with T = var i
     ~∙var∷l■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (i : Γ ∋ X)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → (≡LHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ')
                 →   ∙[var] var i , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ■
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) , (γ' ,  ⟦ var i ⟧ᵛ γ) ■

     ~∙var∷l∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (i : Γ ∋ X)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → {M' : Γ'' ⊢ᵛ X `× Y} → {N' : (Γ'' ∙ X ∙ Y) ⊢ᵛ Z}
                 → (≡LHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack (pm M' N') γ'')
                 →   ∙[var] var i , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) , (γ' ,  ⟦ var i ⟧ᵛ γ) ∷pm⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡M' ⟩ tail

     ~∙var∷l∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (i : Γ ∋ X)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → {LHS' : Γ'' ⊢ᵛ X `× Y} → {RHS' : Γ'' ⊢ᵛ Z}
                 → (≡LHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙[var] var i , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) , (γ' ,  ⟦ var i ⟧ᵛ γ) ∷l⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡LHS' ⟩ tail

     ~∙var∷l∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (i : Γ ∋ X)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → {LHS' : Γ'' ⊢ᵛ Z} → {RHS' : Γ'' ⊢ᵛ X `× Y}
                 → (≡LHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙[var] var i , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) , (γ' ,  ⟦ var i ⟧ᵛ γ) ∷r⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡RHS' ⟩ tail

     -- (∙ T ∷ (_ , RHS) ∷ tail) transitions with T = lam M
     ~∙lam∷l■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ X `⇒ Y) → (RHS : Γ' ⊢ᵛ Z)
                 → (≡LHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ')
                 →   ∙[lam] lam M , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ■
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) , (γ' ,  ⟦ lam M ⟧ᵛ γ) ■

     ~∙lam∷l∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ X `⇒ Y) → (RHS : Γ' ⊢ᵛ Z)
                 → {M' : Γ'' ⊢ᵛ (X `⇒ Y) `× Z} → {N' : (Γ'' ∙ (X `⇒ Y) ∙ Z) ⊢ᵛ Z'}
                 → (≡LHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack (pm M' N') γ'')
                 →   ∙[lam] lam M , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) , (γ' ,  ⟦ lam M ⟧ᵛ γ) ∷pm⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡M' ⟩ tail

     ~∙lam∷l∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ X `⇒ Y) → (RHS : Γ' ⊢ᵛ Z)
                 → {LHS' : Γ'' ⊢ᵛ (X `⇒ Y) `× Z} → {RHS' : Γ'' ⊢ᵛ Z'}
                 → (≡LHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙[lam] lam M , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) , (γ' ,  ⟦ lam M ⟧ᵛ γ) ∷l⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡LHS' ⟩ tail

     ~∙lam∷l∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ X `⇒ Y) → (RHS : Γ' ⊢ᵛ Z)
                 → {LHS' : Γ'' ⊢ᵛ Z'} → {RHS' : Γ'' ⊢ᵛ (X `⇒ Y) `× Z}
                 → (≡LHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙[lam] lam M , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) , (γ' ,  ⟦ lam M ⟧ᵛ γ) ∷r⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡RHS' ⟩ tail

     -- (∙ T ∷ (_ , RHS) ∷ tail) transitions with T = unit
     ~∙unit∷l■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (LHS : Γ' ⊢ᵛ `Unit) → (RHS : Γ' ⊢ᵛ Y)
                 → (≡LHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ')
                 →   ∙[unit] unit , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ■
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) , (γ' ,  ⟦ unit ⟧ᵛ γ) ■

     ~∙unit∷l∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (LHS : Γ' ⊢ᵛ `Unit) → (RHS : Γ' ⊢ᵛ Y)
                 → {M' : Γ'' ⊢ᵛ `Unit `× Y} → {N' : (Γ'' ∙ `Unit ∙ Y) ⊢ᵛ Z}
                 → (≡LHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack (pm M' N') γ'')
                 →   ∙[unit] unit , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) , (γ' ,  ⟦ unit ⟧ᵛ γ) ∷pm⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡M' ⟩ tail

     ~∙unit∷l∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (LHS : Γ' ⊢ᵛ `Unit) → (RHS : Γ' ⊢ᵛ Y)
                 → {LHS' : Γ'' ⊢ᵛ `Unit `× Y} → {RHS' : Γ'' ⊢ᵛ Z}
                 → (≡LHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙[unit] unit , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) , (γ' ,  ⟦ unit ⟧ᵛ γ) ∷l⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡LHS' ⟩ tail

     ~∙unit∷l∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (LHS : Γ' ⊢ᵛ `Unit) → (RHS : Γ' ⊢ᵛ Y)
                 → {LHS' : Γ'' ⊢ᵛ Z} → {RHS' : Γ'' ⊢ᵛ `Unit `× Y}
                 → (≡LHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙[unit] unit , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) , (γ' ,  ⟦ unit ⟧ᵛ γ) ∷r⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡RHS' ⟩ tail

     -- (∙ T ∷ (_ , RHS) ∷ tail) transitions with T = pair x y
     ~∙pair∷l■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ X `× Y) → (RHS : Γ' ⊢ᵛ Z)
                 → (≡LHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ')
                 →   ∙[pair] pair x y , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ■
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) , (γ' ,  ⟦ pair x y ⟧ᵛ γ) ■

     ~∙pair∷l∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ X `× Y) → (RHS : Γ' ⊢ᵛ Z)
                 → {M' : Γ'' ⊢ᵛ (X `× Y) `× Z} → {N' : (Γ'' ∙ (X `× Y) ∙ Z) ⊢ᵛ Z'}
                 → (≡LHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack (pm M' N') γ'')
                 →   ∙[pair] pair x y , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) , (γ' ,  ⟦ pair x y ⟧ᵛ γ) ∷pm⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡M' ⟩ tail

     ~∙pair∷l∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ X `× Y) → (RHS : Γ' ⊢ᵛ Z)
                 → {LHS' : Γ'' ⊢ᵛ (X `× Y) `× Z} → {RHS' : Γ'' ⊢ᵛ Z'}
                 → (≡LHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙[pair] pair x y , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) , (γ' ,  ⟦ pair x y ⟧ᵛ γ) ∷l⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡LHS' ⟩ tail

     ~∙pair∷l∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ X `× Y) → (RHS : Γ' ⊢ᵛ Z)
                 → {LHS' : Γ'' ⊢ᵛ Z'} → {RHS' : Γ'' ⊢ᵛ (X `× Y) `× Z}
                 → (≡LHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙[pair] pair x y , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS , γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) , (γ' ,  ⟦ pair x y ⟧ᵛ γ) ∷r⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡RHS' ⟩ tail

     --------------------------------------------------------------------------------------
     -- (∙ T ∷ (LHS , _) ∷ tail) transitions with T = var i
     ~∙var∷r■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (i : Γ ∋ Y)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → (≡RHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ')
                 →   ∙[var] var i , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ■
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) , (γ' , ⟦ var i ⟧ᵛ γ) ■

     ~∙var∷r∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (i : Γ ∋ Y)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → {M' : Γ'' ⊢ᵛ X `× Y} → {N' : (Γ'' ∙ X ∙ Y) ⊢ᵛ Z}
                 → (≡RHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack (pm M' N') γ'')
                 →   ∙[var] var i , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) , (γ' , ⟦ var i ⟧ᵛ γ) ∷pm⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡M' ⟩ tail

     ~∙var∷r∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (i : Γ ∋ Y)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → {LHS' : Γ'' ⊢ᵛ X `× Y} → {RHS' : Γ'' ⊢ᵛ Z}
                 → (≡RHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙[var] var i , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) , (γ' , ⟦ var i ⟧ᵛ γ) ∷l⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡LHS' ⟩ tail

     ~∙var∷r∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (i : Γ ∋ Y)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → {LHS' : Γ'' ⊢ᵛ Z} → {RHS' : Γ'' ⊢ᵛ X `× Y}
                 → (≡RHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙[var] var i , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) , (γ' , ⟦ var i ⟧ᵛ γ) ∷r⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡RHS' ⟩ tail

     -- (∙ T ∷ (LHS , _) ∷ tail) transitions with T = lam M
     ~∙lam∷r■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `⇒ Y)
                 → (≡RHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ')
                 →   ∙[lam] lam M , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ■
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) , (γ' , ⟦ lam M ⟧ᵛ γ) ■

     ~∙lam∷r∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `⇒ Y)
                 → {M' : Γ'' ⊢ᵛ Z `× (X `⇒ Y)} → {N' : (Γ'' ∙ Z ∙ (X `⇒ Y)) ⊢ᵛ Z'}
                 → (≡RHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack (pm M' N') γ'')
                 →   ∙[lam] lam M , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) , (γ' , ⟦ lam M ⟧ᵛ γ) ∷pm⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡M' ⟩ tail

     ~∙lam∷r∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `⇒ Y)
                 → {LHS' : Γ'' ⊢ᵛ Z `× (X `⇒ Y)} → {RHS' : Γ'' ⊢ᵛ Z'}
                 → (≡RHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙[lam] lam M , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) , (γ' , ⟦ lam M ⟧ᵛ γ) ∷l⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡LHS' ⟩ tail

     ~∙lam∷r∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `⇒ Y)
                 → {LHS' : Γ'' ⊢ᵛ Z'} → {RHS' : Γ'' ⊢ᵛ Z `× (X `⇒ Y)}
                 → (≡RHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙[lam] lam M , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) , (γ' , ⟦ lam M ⟧ᵛ γ) ∷r⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡RHS' ⟩ tail

     -- (∙ T ∷ (LHS , _) ∷ tail) transitions with T = unit
     ~∙unit∷r■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ `Unit)
                 → (≡RHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ')
                 →   ∙[unit] unit , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ■
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) , (γ' , ⟦ unit ⟧ᵛ γ) ■

     ~∙unit∷r∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ `Unit)
                 → {M' : Γ'' ⊢ᵛ X `× `Unit} → {N' : (Γ'' ∙ X ∙ `Unit) ⊢ᵛ Z}
                 → (≡RHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack (pm M' N') γ'')
                 →   ∙[unit] unit , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) , (γ' , ⟦ unit ⟧ᵛ γ) ∷pm⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡M' ⟩ tail

     ~∙unit∷r∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ `Unit)
                 → {LHS' : Γ'' ⊢ᵛ X `× `Unit} → {RHS' : Γ'' ⊢ᵛ Z}
                 → (≡RHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙[unit] unit , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) , (γ' , ⟦ unit ⟧ᵛ γ) ∷l⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡LHS' ⟩ tail

     ~∙unit∷r∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ `Unit)
                 → {LHS' : Γ'' ⊢ᵛ Z} → {RHS' : Γ'' ⊢ᵛ X `× `Unit}
                 → (≡RHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙[unit] unit , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) , (γ' , ⟦ unit ⟧ᵛ γ) ∷r⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡RHS' ⟩ tail

     -- (∙ T ∷ (LHS , _) ∷ tail) transitions with T = pair x y
     ~∙pair∷r■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `× Y)
                 → (≡RHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ')
                 →   ∙[pair] pair x y , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ■
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) , (γ' , ⟦ pair x y ⟧ᵛ γ) ■

     ~∙pair∷r∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `× Y)
                 → {M' : Γ'' ⊢ᵛ Z `× (X `× Y)} → {N' : (Γ'' ∙ Z ∙ (X `× Y)) ⊢ᵛ Z'}
                 → (≡RHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack (pm M' N') γ'')
                 →   ∙[pair] pair x y , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) , (γ' , ⟦ pair x y ⟧ᵛ γ) ∷pm⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡M' ⟩ tail

     ~∙pair∷r∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `× Y)
                 → {LHS' : Γ'' ⊢ᵛ Z `× (X `× Y)} → {RHS' : Γ'' ⊢ᵛ Z'}
                 → (≡RHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙[pair] pair x y , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) , (γ' , ⟦ pair x y ⟧ᵛ γ) ∷l⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡LHS' ⟩ tail

     ~∙pair∷r∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `× Y)
                 → {LHS' : Γ'' ⊢ᵛ Z'} → {RHS' : Γ'' ⊢ᵛ Z `× (X `× Y)}
                 → (≡RHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS' RHS') γ'')
                 →   ∙[pair] pair x y , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) , (γ' , ⟦ pair x y ⟧ᵛ γ) ∷r⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡RHS' ⟩ tail


data haltingVState : VState → Set where

     ∙var■ : {γ : ⟦ Γ ⟧ˣ} → {i : Γ ∋ X} → haltingVState (∙[var] (var i) , γ ■)

     ∙unit■ : {γ : ⟦ Γ ⟧ˣ} → haltingVState (∙[unit] unit , γ ■)

     ∙pair■ : {γ : ⟦ Γ ⟧ˣ} → {LHS : Γ ⊢ᵛ X} → {RHS : Γ ⊢ᵛ Y} → haltingVState (∙[pair] pair LHS RHS , γ ■)

     ∙lam■ : {γ : ⟦ Γ ⟧ˣ} → {M : (Γ ∙ X) ⊢ᶜ Y} → haltingVState (∙[lam] lam M , γ ■)


data Progress (S : VState) : Set where

     step : {S' : VState} → S ~>ᵛᵛ S' → Progress S

     done : haltingVState S → Progress S


progress : (S : VState) → Progress S

progress (∘_ {M = var _} _) = step ~∘var~>
progress (∘_ {M = lam _} _) = step ~∘lam~>
progress (∘_ {M = pair _ _} _) = step ~∘pair~>
progress (∘_ {M = pm _ _} _) = step ~∘pm~>
progress (∘_ {M = unit} _) = step ~∘unit~>

---

progress (∙[var] (.(var _) , _ ■)) = done ∙var■
progress (∙[lam] (.(lam _) , _ ■)) = done ∙lam■
progress (∙[unit] (.unit , _ ■)) = done ∙unit■
progress (∙[pair] (.(pair _ _) , _ ■)) = done ∙pair■

---

progress (∙[var] ((var i) , γ ∷pm⟨ ≡M ⟩ (pm M N) , γ' ■)) = step (~∙var∷pm■~> γ γ' i M N ≡M)
progress (∙[var] (var i , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' tail)
progress (∙[var] (var i , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ∷l⟨ ≡LHS ⟩ tail)) = step (~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS tail)
progress (∙[var] (var i , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ∷r⟨ ≡RHS ⟩ tail)) = step (~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS tail)

progress (∙[pair] (pair x y , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ■)) = step (~∙pair∷pm■~> γ γ' x y M N ≡M)
progress (∙[pair] (pair x y , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' tail)
progress (∙[pair] (pair x y , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ∷l⟨ ≡LHS ⟩ tail)) = step (~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS tail)
progress (∙[pair] (pair x y , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ∷r⟨ ≡RHS ⟩ tail)) = step (~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS tail)

---

progress (∙[var] (var i , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ■)) = step (~∙var∷l■~> γ γ' i LHS RHS ≡LHS)
progress (∙[var] (var i , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' tail)
progress (∙[var] (var i , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' tail)
progress (∙[var] (var i , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' tail)

progress (∙[lam] (lam M , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ■)) = step (~∙lam∷l■~> γ γ' M LHS RHS ≡LHS)
progress (∙[lam] (lam M , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' tail)
progress (∙[lam] (lam M , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' tail)
progress (∙[lam] (lam M , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' tail)

progress (∙[unit] (unit , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ■)) = step (~∙unit∷l■~> γ γ' LHS RHS ≡LHS)
progress (∙[unit] (unit , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' tail)
progress (∙[unit] (unit , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' tail)
progress (∙[unit] (unit , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' tail)

progress (∙[pair] (pair x y , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ■)) = step (~∙pair∷l■~> γ γ' x y LHS RHS ≡LHS)
progress (∙[pair] (pair x y , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' tail)
progress (∙[pair] (pair x y , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' tail)
progress (∙[pair] (pair x y , γ ∷l⟨ ≡LHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' tail)

---

progress (∙[var] (var i , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ■)) = step (~∙var∷r■~> γ γ' i LHS RHS ≡RHS)
progress (∙[var] (var i , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' tail)
progress (∙[var] (var i , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' tail)
progress (∙[var] (var i , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' tail)

progress (∙[lam] (lam M , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ■)) = step (~∙lam∷r■~> γ γ' M LHS RHS ≡RHS)
progress (∙[lam] (lam M , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' tail)
progress (∙[lam] (lam M , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' tail)
progress (∙[lam] (lam M , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' tail)

progress (∙[unit] (unit , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ■)) = step (~∙unit∷r■~> γ γ' LHS RHS ≡RHS)
progress (∙[unit] (unit , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' tail)
progress (∙[unit] (unit , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' tail)
progress (∙[unit] (unit , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' tail)

progress (∙[pair] (pair x y , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ■)) = step (~∙pair∷r■~> γ γ' x y LHS RHS ≡RHS)
progress (∙[pair] (pair x y , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' tail)
progress (∙[pair] (pair x y , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' tail)
progress (∙[pair] (pair x y , γ ∷r⟨ ≡RHS ⟩ pair LHS RHS , γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' tail)


data _~>ᵛᵛ*_ : VState → VState → Set where

  _▣ : (VS : VState) → VS ~>ᵛᵛ* VS

  _~>ᵛᵛ⟨_⟩_ : (VS : VState) {VS' VS'' : VState} → VS ~>ᵛᵛ VS' → VS' ~>ᵛᵛ* VS'' → VS ~>ᵛᵛ* VS''

-- cf PLFA
record Gas : Set where
  constructor gas
  field
    amount : ℕ

-- cf PLFA
data Finished (S : VState) : Set where

   done : haltingVState S → Finished S

   out-of-gas : Finished S

-- cf PLFA
data Steps : VState → Set where

  steps : {S S' : VState} → S ~>ᵛᵛ* S' → Finished S' → Steps S

-- cf PLFA
eval : Gas → (S : VState) → Steps S
eval (gas zero) S = steps (S ▣) out-of-gas
eval (gas (suc amount)) S with progress S
... | done HS = steps (S ▣) (done HS)
... | step {S' = S'} (S~>S') with eval (gas amount) S'
... |   steps S'~>*S'' fin = steps (S ~>ᵛᵛ⟨ S~>S' ⟩ S'~>*S'') fin

ex1 : ε ⊢ᵛ `Unit
ex1 = pm (pair unit unit) (var (t h))

_ : eval (gas 100) (∘ ex1 , tt ■) ≡ steps
      ((∘ pm (pair unit unit) (var (t h)) , tt ■) ~>ᵛᵛ⟨ ~∘pm~> ⟩
      ((∘
        pair unit unit , tt ∷pm⟨ refl ⟩
        pm (pair unit unit) (var (t h)) , tt ■)
        ~>ᵛᵛ⟨ ~∘pair~> ⟩
        ((∘
          unit , tt ∷l⟨ refl ⟩
          pair unit unit , tt ∷pm⟨ refl ⟩
          pm (pair unit unit) (var (t h)) , tt ■)
        ~>ᵛᵛ⟨ ~∘unit~> ⟩
        ((∙[unit]
          (unit , tt ∷l⟨ refl ⟩
            pair unit unit , tt ∷pm⟨ refl ⟩
            pm (pair unit unit) (var (t h)) , tt ■))
          ~>ᵛᵛ⟨
          ~∙unit∷l∷pm~> tt tt unit unit refl refl
          (pm (pair unit unit) (var (t h)) , tt ■)
          ⟩
          ((∘ (unit , tt ∷r⟨ refl ⟩ (((pair (var h)) unit) , (tt , tt) ∷pm⟨ refl ⟩ (((pm (pair unit unit)) (var (t h))) , tt ■))))
          ~>ᵛᵛ⟨ ~∘unit~> ⟩
          ((∙[unit]
            (unit , tt ∷r⟨ refl ⟩
              pair (var h) unit , (tt , tt) ∷pm⟨ refl ⟩
              pm (pair unit unit) (var (t h)) , tt ■))
            ~>ᵛᵛ⟨
            ~∙unit∷r∷pm~> tt (tt , tt) (var h) unit refl refl
            (pm (pair unit unit) (var (t h)) , tt ■)
            ⟩
            ((∙[pair]
              (pair (var (t h)) (var h) , ((tt , tt) , tt) ∷pm⟨ refl ⟩
              pm (pair unit unit) (var (t h)) , tt ■))
            ~>ᵛᵛ⟨
            ~∙pair∷pm■~> ((tt , tt) , tt) tt (var (t h)) (var h)
            (pair unit unit) (var (t h)) refl
            ⟩
            ((∘ var (t h) , ((tt , tt) , tt) ■) ~>ᵛᵛ⟨ ~∘var~> ⟩
              ((∙[var] (var (t h) , ((tt , tt) , tt) ■)) ▣)))))))))
      (done ∙var■)
_ = refl
