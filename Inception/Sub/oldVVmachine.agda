module Inception.Sub.oldVVmachine (R : Set) where

open import Function.Base using (id)
open import Data.Product using (proj₁; proj₂; _,_; Σ; ∃; Σ-syntax; ∃-syntax)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; sym)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Product as P
open import Data.Unit
open import Data.Nat using (ℕ; zero; suc; _+_)

variable
  A' B' C' D' X Y Z X' Y' Z' X₁ Y₁ Z₁ X₂ Y₂ Z₂ X◾ Y◾ Z◾ X↓ Y↓ Z↓ T◾ T◾' T◾₁ T◾₂ : Ty
  Γ' Γ'' Γ''' Δ' Γ₁ Γ₂ Γ◾ Γ↓ : Ctx

infixr 35 _~>ᵛᵛ⟨_⟩_
infix 30 _﹐_■
infixr 25 _﹐_∷pm⟨_⟩_
infixr 25 _﹐_∷l⟨_⟩_
infixr 25 _﹐_∷r⟨_⟩_
infix 20 ∘_
infix 15 _~>ᵛᵛ_

data valStack : (T◾ : Ty) → (Γ ⊢ᵛ A) → ⟦ Γ ⟧ˣ → Set where

    _﹐_■ : (M : Γ ⊢ᵛ T◾) → (γ : ⟦ Γ ⟧ˣ) → valStack T◾ M γ

    _﹐_∷pm⟨_⟩_ : (M : Γ ⊢ᵛ A `× B) → (γ : ⟦ Γ ⟧ˣ) → {M' : Γ' ⊢ᵛ A `× B} → {γ' : ⟦ Γ' ⟧ˣ} → {N : (Γ' ∙ A ∙ B) ⊢ᵛ C} → (M≡M' : ⟦ M ⟧ᵛ γ ≡ ⟦ M' ⟧ᵛ γ') → valStack T◾ (pm M' N) γ'
        → valStack T◾ M γ

    _﹐_∷l⟨_⟩_ : (LHS : Γ ⊢ᵛ A) → (γ : ⟦ Γ ⟧ˣ) → {LHS' : Γ' ⊢ᵛ A} → {γ' : ⟦ Γ' ⟧ˣ} → (L≡L' : ⟦ LHS ⟧ᵛ γ ≡ ⟦ LHS' ⟧ᵛ γ') → {RHS : Γ' ⊢ᵛ B} → valStack T◾ (pair LHS' RHS) γ'
        → valStack T◾ LHS γ

    _﹐_∷r⟨_⟩_ : (RHS : Γ ⊢ᵛ A) → (γ : ⟦ Γ ⟧ˣ) → {RHS' : Γ' ⊢ᵛ A} → {γ' : ⟦ Γ' ⟧ˣ} → (R≡R' : ⟦ RHS ⟧ᵛ γ ≡ ⟦ RHS' ⟧ᵛ γ') → {LHS : Γ' ⊢ᵛ B} → valStack T◾ (pair LHS RHS') γ'
        → valStack T◾ RHS γ

data VState : (T◾ : Ty) → Set where

     ∘_ : {M : Γ ⊢ᵛ A} → {γ : ⟦ Γ ⟧ˣ} → valStack T◾ M γ → VState T◾

     ∙[var]_ : {i : Γ ∋ X} → {γ : ⟦ Γ ⟧ˣ} → valStack T◾ (var i) γ → VState T◾

     ∙[lam]_ : {M : (Γ ∙ X) ⊢ᶜ Y} → {γ : ⟦ Γ ⟧ˣ} → valStack T◾ (lam M) γ → VState T◾

     ∙[unit]_ : {γ : ⟦ Γ ⟧ˣ} → valStack T◾ unit γ → VState T◾

     ∙[pair]_ : {x : Γ ⊢ᵛ X} → {y : Γ ⊢ᵛ Y} → {γ : ⟦ Γ ⟧ˣ} → valStack T◾ (pair x y) γ → VState T◾

data _~>ᵛᵛ_ : VState T◾ → VState T◾ → Set where

     ~∘var~>   : {γ : ⟦ Γ ⟧ˣ} → {i : Γ ∋ X} → {tail : valStack T◾ (var i) γ} → ∘ tail ~>ᵛᵛ ∙[var] tail

     ~∘lam~> : {γ : ⟦ Γ ⟧ˣ} → {M : (Γ ∙ X) ⊢ᶜ Y} → {tail : valStack T◾ (lam M) γ} → ∘ tail ~>ᵛᵛ ∙[lam] tail

     ~∘pair~> : {γ : ⟦ Γ ⟧ˣ} → {LHS : Γ ⊢ᵛ X} → {RHS : Γ ⊢ᵛ Y} → {tail : valStack T◾ (pair LHS RHS) γ} → ∘ tail ~>ᵛᵛ ∘ LHS ﹐ γ ∷l⟨ refl ⟩ tail

     ~∘pm~> : {γ : ⟦ Γ ⟧ˣ} → {M : Γ ⊢ᵛ X `× Y} → {N : (Γ ∙ X ∙ Y) ⊢ᵛ Z} → {tail : valStack T◾ (pm M N) γ} → ∘ tail ~>ᵛᵛ ∘ M ﹐ γ ∷pm⟨ refl ⟩ tail

     ~∘unit~> : {γ : ⟦ Γ ⟧ˣ} → {tail : valStack T◾ unit γ} → ∘ tail ~>ᵛᵛ ∙[unit] tail

     -- (∙ var ∷ pm ∷ tail) transitions

     ~∙var∷pm■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (i : Γ ∋ X `× Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z')
                 → (≡M : ⟦ var i ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ')
                 →    ∙[var] var i ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ■
                      ~>ᵛᵛ
                        ∘ N ﹐ ((γ' , proj₁ (⟦ var i ⟧ᵛ γ)) , proj₂ (⟦ var i ⟧ᵛ γ)) ■

     ~∙var∷pm∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (i : Γ ∋ X `× Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ X' `× Y')
                 → {M' : Γ'' ⊢ᵛ X' `× Y'} → {N' : (Γ'' ∙ X' ∙ Y') ⊢ᵛ Z}
                 → (≡M : ⟦ var i ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ') → (≡M' : ⟦ (pm M N) ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pm M' N') γ'')
                 →   ∙[var] var i ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                      ∘ N ﹐ ((γ' ,  proj₁ (⟦ var i ⟧ᵛ γ)) ,  proj₂ (⟦ var i ⟧ᵛ γ)) ∷pm⟨ trans (cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p) ) ≡M) ≡M' ⟩ tail

     ~∙var∷pm∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (i : Γ ∋ X `× Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z)
                 → {LHS : Γ'' ⊢ᵛ Z} → {RHS : Γ'' ⊢ᵛ Z'}
                 → (≡M : ⟦ var i ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ') → (≡LHS : ⟦ (pm M N) ⟧ᵛ γ' ≡ ⟦ LHS ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS RHS) γ'')
                 →    ∙[var] var i ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ∷l⟨ ≡LHS ⟩ tail
                      ~>ᵛᵛ
                       ∘ N ﹐ ((γ' ,  proj₁ (⟦ var i ⟧ᵛ γ)) ,  proj₂ (⟦ var i ⟧ᵛ γ)) ∷l⟨ trans (cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p) ) ≡M) ≡LHS ⟩ tail

     ~∙var∷pm∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (i : Γ ∋ X `× Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z')
                 → {LHS : Γ'' ⊢ᵛ Z} → {RHS : Γ'' ⊢ᵛ Z'}
                 → (≡M : ⟦ var i ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ') → (≡RHS : ⟦ (pm M N) ⟧ᵛ γ' ≡ ⟦ RHS ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS RHS) γ'')
                 →    ∙[var] var i ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ∷r⟨ ≡RHS ⟩ tail
                      ~>ᵛᵛ
                       ∘ N ﹐ ((γ' , proj₁ (⟦ var i ⟧ᵛ γ)) , proj₂ (⟦ var i ⟧ᵛ γ)) ∷r⟨ trans (cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p) ) ≡M) ≡RHS ⟩ tail

     -- (∙ pair ∷ pm ∷ tail) transitions
     ~∙pair∷pm■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z')
                 → (≡M : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ')
                 →    ∙[pair] pair x y ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ■
                      ~>ᵛᵛ
                       ∘ N ﹐ ((γ' ,  ⟦ x ⟧ᵛ γ) ,  ⟦ y ⟧ᵛ γ) ■

     ~∙pair∷pm∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ X' `× Y')
                 → {M' : Γ'' ⊢ᵛ X' `× Y'} → {N' : (Γ'' ∙ X' ∙ Y') ⊢ᵛ C}
                 → (≡M : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ') → (≡M' : ⟦ (pm M N) ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pm M' N') γ'')
                 →   ∙[pair] pair x y ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                      ∘ N ﹐ ((γ' ,  ⟦ x ⟧ᵛ γ) ,  ⟦ y ⟧ᵛ γ) ∷pm⟨ trans (cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p) ) ≡M) ≡M' ⟩ tail

     ~∙pair∷pm∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z)
                 → {LHS : Γ'' ⊢ᵛ Z} → {RHS : Γ'' ⊢ᵛ Z'}
                 → (≡M : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ') → (≡LHS : ⟦ (pm M N) ⟧ᵛ γ' ≡ ⟦ LHS ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS RHS) γ'')
                 →    ∙[pair] pair x y ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ∷l⟨ ≡LHS ⟩ tail
                      ~>ᵛᵛ
                       ∘ N ﹐ ((γ' ,  ⟦ x ⟧ᵛ γ) ,  ⟦ y ⟧ᵛ γ) ∷l⟨ trans (cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p) ) ≡M) ≡LHS ⟩ tail

     ~∙pair∷pm∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z')
                 → {LHS : Γ'' ⊢ᵛ Z} → {RHS : Γ'' ⊢ᵛ Z'}
                 → (≡M : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ') → (≡RHS : ⟦ (pm M N) ⟧ᵛ γ' ≡ ⟦ RHS ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS RHS) γ'')
                 →    ∙[pair] pair x y ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ∷r⟨ ≡RHS ⟩ tail
                      ~>ᵛᵛ
                       ∘ N ﹐ ((γ' ,  ⟦ x ⟧ᵛ γ) ,  ⟦ y ⟧ᵛ γ) ∷r⟨ trans (cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p) ) ≡M) ≡RHS ⟩ tail

     -------------------------------------------------------------------------------------

     -- (∙ T ∷ (_ ﹐ RHS) ∷ tail) transitions with T = var i
     ~∙var∷l■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (i : Γ ∋ X)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → (≡LHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ')
                 →   ∙[var] var i ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ■
                      ~>ᵛᵛ
                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ var i ⟧ᵛ γ) ■

     ~∙var∷l∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (i : Γ ∋ X)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → {M' : Γ'' ⊢ᵛ X `× Y} → {N' : (Γ'' ∙ X ∙ Y) ⊢ᵛ Z}
                 → (≡LHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pm M' N') γ'')
                 →   ∙[var] var i ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ var i ⟧ᵛ γ) ∷pm⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡M' ⟩ tail

     ~∙var∷l∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (i : Γ ∋ X)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → {LHS' : Γ'' ⊢ᵛ X `× Y} → {RHS' : Γ'' ⊢ᵛ Z}
                 → (≡LHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS' RHS') γ'')
                 →   ∙[var] var i ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ var i ⟧ᵛ γ) ∷l⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡LHS' ⟩ tail

     ~∙var∷l∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (i : Γ ∋ X)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → {LHS' : Γ'' ⊢ᵛ Z} → {RHS' : Γ'' ⊢ᵛ X `× Y}
                 → (≡LHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS' RHS') γ'')
                 →   ∙[var] var i ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ var i ⟧ᵛ γ) ∷r⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡RHS' ⟩ tail

     -- (∙ T ∷ (_ ﹐ RHS) ∷ tail) transitions with T = lam M
     ~∙lam∷l■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ X `⇒ Y) → (RHS : Γ' ⊢ᵛ Z)
                 → (≡LHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ')
                 →   ∙[lam] lam M ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ■
                      ~>ᵛᵛ
                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ lam M ⟧ᵛ γ) ■

     ~∙lam∷l∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ X `⇒ Y) → (RHS : Γ' ⊢ᵛ Z)
                 → {M' : Γ'' ⊢ᵛ (X `⇒ Y) `× Z} → {N' : (Γ'' ∙ (X `⇒ Y) ∙ Z) ⊢ᵛ Z'}
                 → (≡LHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pm M' N') γ'')
                 →   ∙[lam] lam M ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ lam M ⟧ᵛ γ) ∷pm⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡M' ⟩ tail

     ~∙lam∷l∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ X `⇒ Y) → (RHS : Γ' ⊢ᵛ Z)
                 → {LHS' : Γ'' ⊢ᵛ (X `⇒ Y) `× Z} → {RHS' : Γ'' ⊢ᵛ Z'}
                 → (≡LHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS' RHS') γ'')
                 →   ∙[lam] lam M ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ lam M ⟧ᵛ γ) ∷l⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡LHS' ⟩ tail

     ~∙lam∷l∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ X `⇒ Y) → (RHS : Γ' ⊢ᵛ Z)
                 → {LHS' : Γ'' ⊢ᵛ Z'} → {RHS' : Γ'' ⊢ᵛ (X `⇒ Y) `× Z}
                 → (≡LHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS' RHS') γ'')
                 →   ∙[lam] lam M ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ lam M ⟧ᵛ γ) ∷r⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡RHS' ⟩ tail

     -- (∙ T ∷ (_ ﹐ RHS) ∷ tail) transitions with T = unit
     ~∙unit∷l■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (LHS : Γ' ⊢ᵛ `Unit) → (RHS : Γ' ⊢ᵛ Y)
                 → (≡LHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ')
                 →   ∙[unit] unit ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ■
                      ~>ᵛᵛ
                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ unit ⟧ᵛ γ) ■

     ~∙unit∷l∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (LHS : Γ' ⊢ᵛ `Unit) → (RHS : Γ' ⊢ᵛ Y)
                 → {M' : Γ'' ⊢ᵛ `Unit `× Y} → {N' : (Γ'' ∙ `Unit ∙ Y) ⊢ᵛ Z}
                 → (≡LHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pm M' N') γ'')
                 →   ∙[unit] unit ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ unit ⟧ᵛ γ) ∷pm⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡M' ⟩ tail

     ~∙unit∷l∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (LHS : Γ' ⊢ᵛ `Unit) → (RHS : Γ' ⊢ᵛ Y)
                 → {LHS' : Γ'' ⊢ᵛ `Unit `× Y} → {RHS' : Γ'' ⊢ᵛ Z}
                 → (≡LHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS' RHS') γ'')
                 →   ∙[unit] unit ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ unit ⟧ᵛ γ) ∷l⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡LHS' ⟩ tail

     ~∙unit∷l∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (LHS : Γ' ⊢ᵛ `Unit) → (RHS : Γ' ⊢ᵛ Y)
                 → {LHS' : Γ'' ⊢ᵛ Z} → {RHS' : Γ'' ⊢ᵛ `Unit `× Y}
                 → (≡LHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS' RHS') γ'')
                 →   ∙[unit] unit ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ unit ⟧ᵛ γ) ∷r⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡RHS' ⟩ tail

     -- (∙ T ∷ (_ ﹐ RHS) ∷ tail) transitions with T = pair x y
     ~∙pair∷l■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ X `× Y) → (RHS : Γ' ⊢ᵛ Z)
                 → (≡LHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ')
                 →   ∙[pair] pair x y ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ■
                      ~>ᵛᵛ
                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ pair x y ⟧ᵛ γ) ■

     ~∙pair∷l∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ X `× Y) → (RHS : Γ' ⊢ᵛ Z)
                 → {M' : Γ'' ⊢ᵛ (X `× Y) `× Z} → {N' : (Γ'' ∙ (X `× Y) ∙ Z) ⊢ᵛ Z'}
                 → (≡LHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pm M' N') γ'')
                 →   ∙[pair] pair x y ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ pair x y ⟧ᵛ γ) ∷pm⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡M' ⟩ tail

     ~∙pair∷l∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ X `× Y) → (RHS : Γ' ⊢ᵛ Z)
                 → {LHS' : Γ'' ⊢ᵛ (X `× Y) `× Z} → {RHS' : Γ'' ⊢ᵛ Z'}
                 → (≡LHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS' RHS') γ'')
                 →   ∙[pair] pair x y ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ pair x y ⟧ᵛ γ) ∷l⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡LHS' ⟩ tail

     ~∙pair∷l∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ X `× Y) → (RHS : Γ' ⊢ᵛ Z)
                 → {LHS' : Γ'' ⊢ᵛ Z'} → {RHS' : Γ'' ⊢ᵛ (X `× Y) `× Z}
                 → (≡LHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS' RHS') γ'')
                 →   ∙[pair] pair x y ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ pair x y ⟧ᵛ γ) ∷r⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡RHS' ⟩ tail

     --------------------------------------------------------------------------------------
     -- (∙ T ∷ (LHS ﹐ _) ∷ tail) transitions with T = var i
     ~∙var∷r■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (i : Γ ∋ Y)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → (≡RHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ')
                 →   ∙[var] var i ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ■
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ var i ⟧ᵛ γ) ■

     ~∙var∷r∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (i : Γ ∋ Y)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → {M' : Γ'' ⊢ᵛ X `× Y} → {N' : (Γ'' ∙ X ∙ Y) ⊢ᵛ Z}
                 → (≡RHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pm M' N') γ'')
                 →   ∙[var] var i ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ var i ⟧ᵛ γ) ∷pm⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡M' ⟩ tail

     ~∙var∷r∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (i : Γ ∋ Y)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → {LHS' : Γ'' ⊢ᵛ X `× Y} → {RHS' : Γ'' ⊢ᵛ Z}
                 → (≡RHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS' RHS') γ'')
                 →   ∙[var] var i ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ var i ⟧ᵛ γ) ∷l⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡LHS' ⟩ tail

     ~∙var∷r∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (i : Γ ∋ Y)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
                 → {LHS' : Γ'' ⊢ᵛ Z} → {RHS' : Γ'' ⊢ᵛ X `× Y}
                 → (≡RHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS' RHS') γ'')
                 →   ∙[var] var i ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ var i ⟧ᵛ γ) ∷r⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡RHS' ⟩ tail

     -- (∙ T ∷ (LHS ﹐ _) ∷ tail) transitions with T = lam M
     ~∙lam∷r■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `⇒ Y)
                 → (≡RHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ')
                 →   ∙[lam] lam M ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ■
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ lam M ⟧ᵛ γ) ■

     ~∙lam∷r∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `⇒ Y)
                 → {M' : Γ'' ⊢ᵛ Z `× (X `⇒ Y)} → {N' : (Γ'' ∙ Z ∙ (X `⇒ Y)) ⊢ᵛ Z'}
                 → (≡RHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pm M' N') γ'')
                 →   ∙[lam] lam M ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ lam M ⟧ᵛ γ) ∷pm⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡M' ⟩ tail

     ~∙lam∷r∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `⇒ Y)
                 → {LHS' : Γ'' ⊢ᵛ Z `× (X `⇒ Y)} → {RHS' : Γ'' ⊢ᵛ Z'}
                 → (≡RHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS' RHS') γ'')
                 →   ∙[lam] lam M ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ lam M ⟧ᵛ γ) ∷l⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡LHS' ⟩ tail

     ~∙lam∷r∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (M : (Γ ∙ X) ⊢ᶜ Y)
                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `⇒ Y)
                 → {LHS' : Γ'' ⊢ᵛ Z'} → {RHS' : Γ'' ⊢ᵛ Z `× (X `⇒ Y)}
                 → (≡RHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS' RHS') γ'')
                 →   ∙[lam] lam M ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ lam M ⟧ᵛ γ) ∷r⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡RHS' ⟩ tail

     -- (∙ T ∷ (LHS ﹐ _) ∷ tail) transitions with T = unit
     ~∙unit∷r■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ `Unit)
                 → (≡RHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ')
                 →   ∙[unit] unit ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ■
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ unit ⟧ᵛ γ) ■

     ~∙unit∷r∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ `Unit)
                 → {M' : Γ'' ⊢ᵛ X `× `Unit} → {N' : (Γ'' ∙ X ∙ `Unit) ⊢ᵛ Z}
                 → (≡RHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pm M' N') γ'')
                 →   ∙[unit] unit ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ unit ⟧ᵛ γ) ∷pm⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡M' ⟩ tail

     ~∙unit∷r∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ `Unit)
                 → {LHS' : Γ'' ⊢ᵛ X `× `Unit} → {RHS' : Γ'' ⊢ᵛ Z}
                 → (≡RHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS' RHS') γ'')
                 →   ∙[unit] unit ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ unit ⟧ᵛ γ) ∷l⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡LHS' ⟩ tail

     ~∙unit∷r∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ `Unit)
                 → {LHS' : Γ'' ⊢ᵛ Z} → {RHS' : Γ'' ⊢ᵛ X `× `Unit}
                 → (≡RHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS' RHS') γ'')
                 →   ∙[unit] unit ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ unit ⟧ᵛ γ) ∷r⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡RHS' ⟩ tail

     -- (∙ T ∷ (LHS ﹐ _) ∷ tail) transitions with T = pair x y
     ~∙pair∷r■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `× Y)
                 → (≡RHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ')
                 →   ∙[pair] pair x y ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ■
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ pair x y ⟧ᵛ γ) ■

     ~∙pair∷r∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `× Y)
                 → {M' : Γ'' ⊢ᵛ Z `× (X `× Y)} → {N' : (Γ'' ∙ Z ∙ (X `× Y)) ⊢ᵛ Z'}
                 → (≡RHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡M' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pm M' N') γ'')
                 →   ∙[pair] pair x y ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ pair x y ⟧ᵛ γ) ∷pm⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡M' ⟩ tail

     ~∙pair∷r∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `× Y)
                 → {LHS' : Γ'' ⊢ᵛ Z `× (X `× Y)} → {RHS' : Γ'' ⊢ᵛ Z'}
                 → (≡RHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡LHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ LHS' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS' RHS') γ'')
                 →   ∙[pair] pair x y ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ pair x y ⟧ᵛ γ) ∷l⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡LHS' ⟩ tail

     ~∙pair∷r∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → {γ'' : ⟦ Γ'' ⟧ˣ}
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `× Y)
                 → {LHS' : Γ'' ⊢ᵛ Z'} → {RHS' : Γ'' ⊢ᵛ Z `× (X `× Y)}
                 → (≡RHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ') → (≡RHS' : ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ RHS' ⟧ᵛ γ'')
                 → (tail : valStack T◾ (pair LHS' RHS') γ'')
                 →   ∙[pair] pair x y ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail
                      ~>ᵛᵛ
                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ pair x y ⟧ᵛ γ) ∷r⟨ trans (cong (λ t → (⟦ LHS ⟧ᵛ γ' , t) ) ≡RHS) ≡RHS' ⟩ tail


data _~>>ᵛᵛ_ : VState T◾ → VState T◾ → Set where

  _~>ᵛᵛ⟨_⟩ : (VS : VState T◾) → {VS' : VState T◾} → VS ~>ᵛᵛ VS' → VS ~>>ᵛᵛ VS'

  _~>ᵛᵛ⟨_⟩_ : (VS : VState T◾) {VS' VS'' : VState T◾} → VS ~>ᵛᵛ VS' → VS' ~>>ᵛᵛ VS'' → VS ~>>ᵛᵛ VS''

~>>ᵛᵛ-trans : {F S T : VState T◾} → (F ~>>ᵛᵛ S) → (S ~>>ᵛᵛ T) → (F ~>>ᵛᵛ T)
~>>ᵛᵛ-trans (F ~>ᵛᵛ⟨ F>S ⟩) S>>T = F ~>ᵛᵛ⟨ F>S ⟩ S>>T
~>>ᵛᵛ-trans (F ~>ᵛᵛ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F ~>ᵛᵛ⟨ F>S₁ ⟩ (~>>ᵛᵛ-trans S₁>>S₂ S₂>>T)

infixr 15 ~>>ᵛᵛ-trans
syntax ~>>ᵛᵛ-trans {S = S} F>>S S>>T = F>>S +[ S ]+ S>>T


data haltingVState : VState T◾ → Set where

     ∙var_⹁_■ : (i : Γ ∋ X) → (γ : ⟦ Γ ⟧ˣ) → haltingVState (∙[var] (var i) ﹐ γ ■)

     ∙unit⹁_■ : (γ : ⟦ Γ ⟧ˣ) → haltingVState (∙[unit] unit ﹐ γ ■)

     ∙pair[_⹁_]⹁_■ : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → (γ : ⟦ Γ ⟧ˣ) → haltingVState (∙[pair] pair LHS RHS ﹐ γ ■)

     ∙lam_⹁_■ : (M : (Γ ∙ X) ⊢ᶜ Y) → (γ : ⟦ Γ ⟧ˣ) → haltingVState (∙[lam] lam M ﹐ γ ■)


⟦_⟧↥ : {M : Γ ⊢ᵛ A} → {γ : ⟦ Γ ⟧ˣ} → valStack T◾ M γ → ⟦ T◾ ⟧
⟦ (M ﹐ γ ■) ⟧↥ = ⟦ M ⟧ᵛ γ
⟦ (_ ﹐ _ ∷pm⟨ _ ⟩ tail) ⟧↥ = ⟦ tail ⟧↥
⟦ (_ ﹐ _ ∷l⟨ _ ⟩ tail) ⟧↥ = ⟦ tail ⟧↥
⟦ (_ ﹐ _ ∷r⟨ _ ⟩ tail) ⟧↥ = ⟦ tail ⟧↥

⟦_⟧◑ : VState T◾ → ⟦ T◾ ⟧
⟦ ∘ tail ⟧◑ = ⟦ tail ⟧↥
⟦ ∙[var] tail ⟧◑ = ⟦ tail ⟧↥
⟦ ∙[lam] tail ⟧◑ = ⟦ tail ⟧↥
⟦ ∙[unit] tail ⟧◑ = ⟦ tail ⟧↥
⟦ ∙[pair] tail ⟧◑ = ⟦ tail ⟧↥


--------------------------------------------------

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

----

data Progress (S : VState T◾) : Set where

     step : {S' : VState T◾} → S ~>ᵛᵛ S' → Progress S

     done : haltingVState S → Progress S


progress : (S : VState T◾) → Progress S

progress (∘_ {M = var _} _) = step ~∘var~>
progress (∘_ {M = lam _} _) = step ~∘lam~>
progress (∘_ {M = pair _ _} _) = step ~∘pair~>
progress (∘_ {M = pm _ _} _) = step ~∘pm~>
progress (∘_ {M = unit} _) = step ~∘unit~>

---

progress (∙[var] ((var i) ﹐ γ ■)) = done ∙var i ⹁ γ ■
progress (∙[lam] ((lam M) ﹐ γ ■)) = done ∙lam M ⹁ γ ■
progress (∙[unit] (unit ﹐ γ ■)) = done ∙unit⹁ γ ■
progress (∙[pair] ((pair LHS RHS ) ﹐ γ ■)) = done ∙pair[ LHS ⹁ RHS ]⹁ γ ■

---

progress (∙[var] ((var i) ﹐ γ ∷pm⟨ ≡M ⟩ (pm M N) ﹐ γ' ■)) = step (~∙var∷pm■~> γ γ' i M N ≡M)
progress (∙[var] (var i ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' tail)
progress (∙[var] (var i ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ∷l⟨ ≡LHS ⟩ tail)) = step (~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS tail)
progress (∙[var] (var i ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ∷r⟨ ≡RHS ⟩ tail)) = step (~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS tail)

progress (∙[pair] (pair x y ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ■)) = step (~∙pair∷pm■~> γ γ' x y M N ≡M)
progress (∙[pair] (pair x y ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' tail)
progress (∙[pair] (pair x y ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ∷l⟨ ≡LHS ⟩ tail)) = step (~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS tail)
progress (∙[pair] (pair x y ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ∷r⟨ ≡RHS ⟩ tail)) = step (~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS tail)

---

progress (∙[var] (var i ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ■)) = step (~∙var∷l■~> γ γ' i LHS RHS ≡LHS)
progress (∙[var] (var i ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' tail)
progress (∙[var] (var i ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' tail)
progress (∙[var] (var i ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' tail)

progress (∙[lam] (lam M ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ■)) = step (~∙lam∷l■~> γ γ' M LHS RHS ≡LHS)
progress (∙[lam] (lam M ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' tail)
progress (∙[lam] (lam M ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' tail)
progress (∙[lam] (lam M ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' tail)

progress (∙[unit] (unit ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ■)) = step (~∙unit∷l■~> γ γ' LHS RHS ≡LHS)
progress (∙[unit] (unit ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' tail)
progress (∙[unit] (unit ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' tail)
progress (∙[unit] (unit ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' tail)

progress (∙[pair] (pair x y ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ■)) = step (~∙pair∷l■~> γ γ' x y LHS RHS ≡LHS)
progress (∙[pair] (pair x y ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' tail)
progress (∙[pair] (pair x y ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' tail)
progress (∙[pair] (pair x y ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' tail)

---

progress (∙[var] (var i ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ■)) = step (~∙var∷r■~> γ γ' i LHS RHS ≡RHS)
progress (∙[var] (var i ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' tail)
progress (∙[var] (var i ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' tail)
progress (∙[var] (var i ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' tail)

progress (∙[lam] (lam M ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ■)) = step (~∙lam∷r■~> γ γ' M LHS RHS ≡RHS)
progress (∙[lam] (lam M ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' tail)
progress (∙[lam] (lam M ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' tail)
progress (∙[lam] (lam M ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' tail)

progress (∙[unit] (unit ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ■)) = step (~∙unit∷r■~> γ γ' LHS RHS ≡RHS)
progress (∙[unit] (unit ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' tail)
progress (∙[unit] (unit ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' tail)
progress (∙[unit] (unit ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' tail)

progress (∙[pair] (pair x y ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ■)) = step (~∙pair∷r■~> γ γ' x y LHS RHS ≡RHS)
progress (∙[pair] (pair x y ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' tail)
progress (∙[pair] (pair x y ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' tail)
progress (∙[pair] (pair x y ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' tail)

-- Using progress and 'gas' we can evaluate expressions (quick-eval).
-- However, we can also prove termination and evaluate expressions using that proof (eval).

-- cf PLFA
record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished (S : VState T◾) : Set where

  result : {S' : VState T◾} → (haltingVState S') → Finished S

  out-of-gas : Finished S

data Steps : (VState T◾) → Set where

  no-steps : {S : VState T◾} → haltingVState S → Steps S

  steps : {S S' : VState T◾} → S ~>>ᵛᵛ S' → Finished S' → Steps S

bounded-eval : Gas → (S : VState T◾) → Steps S
bounded-eval (gas zero) S  with progress S
... | done HS = no-steps HS
... | step {S' = S'} (S~>S') = steps (S ~>ᵛᵛ⟨ S~>S' ⟩) out-of-gas
bounded-eval (gas (suc amount)) S with progress S
... | done HS = no-steps HS
... | step {S' = S'} (S~>S') with bounded-eval (gas amount) S'
... |   no-steps HS = steps (S ~>ᵛᵛ⟨ S~>S' ⟩) (result HS)
... |   steps S'~>>S'' fin = steps (S ~>ᵛᵛ⟨ S~>S' ⟩ S'~>>S'') fin


calc-steps : (Γ ⊢ᵛ X) → ℕ
calc-steps (var i) = 1
calc-steps (lam x) = 1
calc-steps (pair M M') = 3 + (calc-steps M) + (calc-steps M')
calc-steps (pm M N) = 2 + (calc-steps M) + (calc-steps N)
calc-steps unit = 1

quick-eval : (M : Γ ⊢ᵛ X) → (γ : ⟦ Γ ⟧ˣ) → Steps (∘ M ﹐ γ ■)
quick-eval M γ = bounded-eval (gas (calc-steps M)) (∘ M ﹐ γ ■)

data finiteSteps : VState T◾ → Set where

  steps : {S T : VState T◾} → S ~>>ᵛᵛ T →  haltingVState T → finiteSteps S

getctx : (T : VState X) → {HT : haltingVState T} → Ctx
getctx (∙[var] var {Γ = Γ} i₁ ﹐ γ₁ ■) = Γ
getctx (∙[lam] lam {Γ = Γ} M₁ ﹐ γ₁ ■) = Γ
getctx (∙[unit] unit {Γ = Γ} ﹐ γ₁ ■) = Γ
getctx (∙[pair] pair {Γ = Γ} x₁ y₁ ﹐ γ₁ ■) = Γ

getenv : (T : VState X) → {HT : haltingVState T} → ⟦ getctx T {HT = HT} ⟧ˣ
getenv (∙[var] var i₁ ﹐ γ₁ ■) = γ₁
getenv (∙[lam] lam M₁ ﹐ γ₁ ■) = γ₁
getenv (∙[unit] unit ﹐ γ₁ ■) = γ₁
getenv (∙[pair] pair x₁ y₁ ﹐ γ₁ ■) = γ₁

getterm : (T : VState X) → {HT : haltingVState T} → (getctx T {HT = HT}) ⊢ᵛ X
getterm (∙[var] var i₁ ﹐ γ₁ ■) = var i₁
getterm (∙[lam] lam M₁ ﹐ γ₁ ■) = lam M₁
getterm (∙[unit] unit ﹐ γ₁ ■) = unit
getterm (∙[pair] pair x₁ y₁ ﹐ γ₁ ■) = pair x₁ y₁

gettrans-left : (T' : VState X) → {HT' : haltingVState T'} → (γ : ⟦ Γ ⟧ˣ) → (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → (LHS>>T' : (∘ LHS ﹐ γ ■) ~>>ᵛᵛ T') → ( (T' ::l⟨ (T≡*LHS LHS>>T' refl (pair LHS RHS ﹐ γ ■)) ⟩ (pair LHS RHS ﹐ γ ■)) ~>ᵛᵛ (∘ RHS ﹐ γ ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ ,  ⟦ (getterm T' {HT = HT'}) ⟧ᵛ (getenv T') ) ■) )
gettrans-left (∙[var] var i₁ ﹐ γ₁ ■) γ LHS RHS LHS>>T' = ~∙var∷l■~> γ₁ γ i₁ LHS RHS (T≡*LHS LHS>>T' refl (pair LHS RHS ﹐ γ ■))
gettrans-left (∙[lam] lam M₁ ﹐ γ₁ ■) γ LHS RHS LHS>>T' = ~∙lam∷l■~> γ₁ γ M₁ LHS RHS (T≡*LHS LHS>>T' refl (pair LHS RHS ﹐ γ ■))
gettrans-left (∙[unit] unit ﹐ γ₁ ■) γ LHS RHS LHS>>T' =  ~∙unit∷l■~> γ₁ γ LHS RHS (T≡*LHS LHS>>T' refl (pair LHS RHS ﹐ γ ■))
gettrans-left (∙[pair] pair x₁ y₁ ﹐ γ₁ ■) γ LHS RHS LHS>>T' = ~∙pair∷l■~> γ₁ γ x₁ y₁ LHS RHS (T≡*LHS LHS>>T' refl (pair LHS RHS ﹐ γ ■))

gettrans-right : (T' : VState X) → {HT' : haltingVState T'} → (T'' : VState Y) → {HT'' : haltingVState T''} → (γ : ⟦ Γ ⟧ˣ) → (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → (RHS>>T'' : (∘ RHS ﹐ γ ■) ~>>ᵛᵛ T'') → ( (T'' ::r⟨ T≡*RHS RHS>>T'' refl (pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) ■) ⟩ (pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) ■)) ~>ᵛᵛ (∙[pair] pair (wk-val (wk-wk wk-id) (var h)) (var h)  ﹐ ((γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) , ⟦ getterm T'' {HT = HT''} ⟧ᵛ (getenv T'' {HT = HT''})) ■) )
gettrans-right T' {HT' = HT'} (∙[var] var i₂ ﹐ γ₂ ■) γ LHS RHS RHS>>T'' = ~∙var∷r■~> γ₂ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) i₂ (var h) (wk-val (wk-wk wk-id) RHS) (T≡*RHS RHS>>T'' refl (pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) ■))
gettrans-right T' {HT' = HT'} (∙[lam] lam M₂ ﹐ γ₂ ■) γ LHS RHS RHS>>T'' = ~∙lam∷r■~> γ₂ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) M₂ (var h) (wk-val (wk-wk wk-id) RHS) (T≡*RHS RHS>>T'' refl (pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) ■))
gettrans-right T' {HT' = HT'} (∙[unit] unit ﹐ γ₂ ■) γ LHS RHS RHS>>T'' = ~∙unit∷r■~> γ₂ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) (var h) (wk-val (wk-wk wk-id) RHS) (T≡*RHS RHS>>T'' refl (pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) ■))
gettrans-right T' {HT' = HT'} (∙[pair] pair x₂ y₂ ﹐ γ₂ ■) γ LHS RHS RHS>>T'' = ~∙pair∷r■~> γ₂ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) x₂ y₂ (var h) (wk-val (wk-wk wk-id) RHS) (T≡*RHS RHS>>T'' refl (pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) ■))

get-pair-steps : {T' : VState X} → {T'' : VState Y} → {HT' : haltingVState T'} → {HT'' : haltingVState T''} → (γ : ⟦ Γ ⟧ˣ) → (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → ((∘ LHS ﹐ γ ■) ~>>ᵛᵛ T') → ((∘ RHS ﹐ γ ■) ~>>ᵛᵛ T'') → finiteSteps (∘ pair LHS RHS ﹐ γ ■)
get-pair-steps {T' = T'} {T'' = T''} {HT' = HT'} {HT'' = HT''} γ LHS RHS LHS>>T' RHS>>T'' =
        steps (    (∘ (pair LHS RHS) ﹐ γ ■)                                       ~>ᵛᵛ⟨ ~∘pair~> ⟩
                +[ _ ]+       ⟪ LHS>>T' ⟫::l⟨ refl ⟩ (pair LHS RHS ﹐ γ ■)
                +[ _ ]+       _ ~>ᵛᵛ⟨ gettrans-left T' γ LHS RHS LHS>>T' ⟩
                +[ _ ]+       ⟪ RHS>>T'' ⟫::r⟨ refl ⟩ (pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ ,  ⟦ LHS' ⟧ᵛ γ₁) ■)
                +[ _ ]+       _ ~>ᵛᵛ⟨ gettrans-right T' T'' γ LHS RHS RHS>>T'' ⟩
              ) ∙pair[ wk-val (wk-wk wk-id) (var h) ⹁ var h ]⹁ ((γ ,  ⟦ LHS' ⟧ᵛ γ₁) , ⟦ RHS' ⟧ᵛ γ₂) ■
        where
         LHS'  = getterm T' {HT = HT'}
         RHS'  = getterm T'' {HT = HT''}
         γ₁  = getenv T' {HT = HT'}
         γ₂  = getenv T'' {HT = HT''}

get-pm-N-env : (T' : VState (X `× Y)) → (HT' : haltingVState T') → (γ : ⟦ Γ ⟧ˣ) → ⟦ Γ ∙ X ∙ Y ⟧ˣ
get-pm-N-env (∙[var] var i ﹐ γ' ■) HT' γ = ((γ , proj₁ (⟦ var i ⟧ᵛ γ')) , proj₂ (⟦ var i ⟧ᵛ γ'))
get-pm-N-env (∙[pair] pair x y ﹐ γ' ■) HT' γ = ((γ , ⟦ x ⟧ᵛ γ') , ⟦ y ⟧ᵛ γ')

get-pm-trans : {T' : VState (X `× Y)} → {T'' : VState Z} → {HT' : haltingVState T'} → {HT'' : haltingVState T''} → (γ : ⟦ Γ ⟧ˣ) → (M : Γ ⊢ᵛ X `× Y) → (N : (Γ ∙ X ∙ Y) ⊢ᵛ Z) → (M>>T' : (∘ M ﹐ γ ■) ~>>ᵛᵛ T') → (T' ::pm⟨ T≡*M M>>T' refl ((pm M N) ﹐ γ ■) ⟩ (pm M N) ﹐ γ ■) ~>>ᵛᵛ (∘ N ﹐ get-pm-N-env T' HT' γ ■)
get-pm-trans {T' = ∙[var] var i ﹐ γ' ■} {T'' = T''} {HT' = HT'} {HT'' = HT''} γ M N M>>T' =  _ ~>ᵛᵛ⟨ ~∙var∷pm■~> γ' γ i M N (T≡*M M>>T' refl ((pm M N) ﹐ γ ■)) ⟩
get-pm-trans {T' = ∙[pair] pair x y ﹐ γ' ■} {T'' = T''} {HT' = HT'} {HT'' = HT''} γ M N M>>T' = _ ~>ᵛᵛ⟨ ~∙pair∷pm■~> γ' γ x y M N (T≡*M M>>T' refl ((pm M N) ﹐ γ ■)) ⟩


get-pm-steps : {T' : VState (X `× Y)} → {T'' : VState Z} → {HT' : haltingVState T'} → {HT'' : haltingVState T''} → (γ : ⟦ Γ ⟧ˣ) → (M : Γ ⊢ᵛ X `× Y) → (N : (Γ ∙ X ∙ Y) ⊢ᵛ Z) → ((∘ M ﹐ γ ■) ~>>ᵛᵛ T') → ((∘ N ﹐ get-pm-N-env T' HT' γ ■) ~>>ᵛᵛ T'') → finiteSteps (∘ pm M N ﹐ γ ■)
get-pm-steps {T' = T'} {T'' = T''} {HT' = HT'} {HT'' = HT''} γ M N M>>T' N>>T'' =

           steps (    (∘ (pm M N) ﹐ γ ■)  ~>ᵛᵛ⟨ ~∘pm~> ⟩
                   +[ MS  ]+       (⟪ M>>T' ⟫::pm⟨ refl ⟩ ((pm M N) ﹐ γ ■))
                   +[ MS' ]+       get-pm-trans {T' = T'} {T'' = T''} {HT' = HT'} {HT'' = HT''} γ M N M>>T'
                   +[ NS  ]+       N>>T''
                 ) HT''

         where
             MS  = ∘ M ﹐ γ ∷pm⟨ refl ⟩ pm M N ﹐ γ ■
             MS' = T' ::pm⟨ T≡*M M>>T' refl ((pm M N) ﹐ γ ■) ⟩ (pm M N) ﹐ γ ■
             NS  = ∘ N ﹐ get-pm-N-env T' HT' γ ■


-- termination proof / evaluation
stepVMᵢ : (M : Γ ⊢ᵛ X) → (γ : ⟦ Γ ⟧ˣ) → finiteSteps (∘ M ﹐ γ ■)
stepVMᵢ (var i) γ = steps ((∘ var i ﹐ γ ■) ~>ᵛᵛ⟨ ~∘var~> ⟩) (∙var i ⹁ γ ■)
stepVMᵢ (lam M) γ = steps ((∘ lam M ﹐ γ ■) ~>ᵛᵛ⟨ ~∘lam~> ⟩) (∙lam M ⹁ γ ■)
stepVMᵢ unit γ = steps ((∘ unit ﹐ γ ■) ~>ᵛᵛ⟨ ~∘unit~> ⟩) ∙unit⹁ γ ■
stepVMᵢ (pair LHS RHS) γ with stepVMᵢ  LHS γ | stepVMᵢ  RHS γ
... | steps {T = T'} LHS>>T' HT' | steps {T = T''} RHS>>T'' HT'' = get-pair-steps {T' = T'} {T'' = T''} {HT' = HT'} {HT'' = HT''} γ LHS RHS LHS>>T' RHS>>T''
stepVMᵢ  (pm M N) γ with stepVMᵢ  M γ
... | steps {T = T'} M>>T' HT' with stepVMᵢ  N (get-pm-N-env T' HT' γ)
...       |    steps {T = T''} N>>T'' HT'' = get-pm-steps {T' = T'} {T'' = T''} {HT' = HT'} {HT'' = HT''} γ M N M>>T' N>>T''


-------------------------------------

ex1 : ε ⊢ᵛ `Unit
ex1 = pm (pair unit unit) (var (t h))

ex2 : (ε ∙ (`Unit `⇒ `Unit) ∙ `Unit) ⊢ᵛ (`Unit `× (`Unit `⇒ `Unit)) `× `Unit
ex2 = pair (pair (var h) (var (t h))) (var h)

ex3 : ε ⊢ᵛ (`Unit `⇒ `Unit)
ex3 = lam (return unit)

ex4 : (ε ∙ `Unit) ⊢ᵛ `Unit `× `Unit
ex4 = pair (var h) (var h)

---------------------------------------

{-
-- calling agda2-compute-normalised in the hole below evaluates ex2
_ : stepVMᵢ  ex2 ((tt , λ _ z → z tt) , tt) ≡ {! stepVMᵢ  ex1 tt!}
_ = refl
-}

