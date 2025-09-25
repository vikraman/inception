module Inception.Sub.ValueMachine (R : Set) where

open import Function.Base using (id)
open import Data.Product using (proj₁; proj₂; _,_; Σ; ∃; Σ-syntax; ∃-syntax)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; sym)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Product as P

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


data haltingVState : VState T◾ → Set where

     ∙var_⹁_■ : (i : Γ ∋ X) → (γ : ⟦ Γ ⟧ˣ) → haltingVState (∙[var] (var i) ﹐ γ ■)

     ∙unit■ : {γ : ⟦ Γ ⟧ˣ} → haltingVState (∙[unit] unit ﹐ γ ■)

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

--------------------

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

{-
  var∷pm-eq : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (i : Γ ∋ X `× Y) → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z') → (≡M : ⟦ var i ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ')
            →   ⟦ pm M N ⟧ᵛ γ' ≡ ⟦ N ⟧ᵛ ((γ' , proj₁ (⟦ var i ⟧ᵛ γ)) , proj₂ (⟦ var i ⟧ᵛ γ))
  var∷pm-eq γ γ' i M N ≡M =
                  ⟦ pm M N ⟧ᵛ γ'
                ≡⟨ refl ⟩
                  ⟦ N ⟧ᵛ ( assocl (< idf , ⟦ M ⟧ᵛ > γ'))
                ≡⟨ refl ⟩
                  ⟦ N ⟧ᵛ ( assocl (γ' , ⟦ M ⟧ᵛ γ'))
                ≡⟨ cong (λ x → ⟦ N ⟧ᵛ ( assocl (γ' , x))) (sym ≡M) ⟩
                  ⟦ N ⟧ᵛ ( assocl (γ' , ⟦ var i ⟧ᵛ γ))
                ≡⟨ refl ⟩
                  ⟦ N ⟧ᵛ ((γ' , proj₁ (⟦ var i ⟧ᵛ γ)) , proj₂ (⟦ var i ⟧ᵛ γ)) ∎
-}

∷pm-eq : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (L : Γ ⊢ᵛ X `× Y) → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z') → (≡M : ⟦ L ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ')
                 →    ⟦ pm M N ⟧ᵛ γ' ≡ ⟦ N ⟧ᵛ ((γ' , proj₁ (⟦ L ⟧ᵛ γ)) , proj₂ (⟦ L ⟧ᵛ γ))
∷pm-eq γ γ' L M N ≡M = cong (λ x → ⟦ N ⟧ᵛ (assocl (γ' , x))) (sym ≡M)

{-
var∷l-eq : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (i : Γ ∋ X) → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y) → (≡LHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ')
            →   ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ pair (var h) (wk-val (wk-wk wk-id) RHS) ⟧ᵛ (γ' ,  ⟦ var i ⟧ᵛ γ)
var∷l-eq γ γ' i LHS RHS ≡LHS =
                ⟦ pair LHS RHS ⟧ᵛ γ'
              ≡⟨ refl ⟩
                ⟦ LHS ⟧ᵛ γ' , ⟦ RHS ⟧ᵛ γ'
              ≡⟨ cong (λ x → x , _) (sym ≡LHS) ⟩
                 ⟦ var i ⟧ᵛ γ , ⟦ RHS ⟧ᵛ γ'
              ≡⟨ refl ⟩
                 ⟦ var i ⟧ᵛ γ , ⟦ wk-val (wk-wk wk-id) RHS ⟧ᵛ (γ' ,  ⟦ var i ⟧ᵛ γ)
              ≡⟨ refl ⟩
                 ⟦ var h ⟧ᵛ (γ' , ⟦ var i ⟧ᵛ γ) , ⟦ wk-val (wk-wk wk-id) RHS ⟧ᵛ (γ' ,  ⟦ var i ⟧ᵛ γ)
              ≡⟨ refl ⟩
                ⟦ pair (var h) (wk-val (wk-wk wk-id) RHS) ⟧ᵛ (γ' ,  ⟦ var i ⟧ᵛ γ) ∎
-}

∷l-eq : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (M : Γ ⊢ᵛ X) → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y) → (≡LHS : ⟦ M ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ')
            →   ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ pair (var h) (wk-val (wk-wk wk-id) RHS) ⟧ᵛ (γ' ,  ⟦ M ⟧ᵛ γ)
∷l-eq γ γ' M LHS RHS ≡LHS = cong (λ x → x , _) (sym ≡LHS)

∷r-eq : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (M : Γ ⊢ᵛ Y) → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y) → (≡RHS : ⟦ M ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ')
           →   ⟦ pair LHS RHS ⟧ᵛ γ' ≡ ⟦ pair (wk-val (wk-wk wk-id) LHS) (var h) ⟧ᵛ (γ' , ⟦ M ⟧ᵛ γ)
∷r-eq γ γ' M LHS RHS ≡RHS = cong (λ x → _ , x) (sym ≡RHS)

F≡T : {from : VState T◾} → {to : VState T◾} → (F>T : from ~>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS' RHS) γ') → (⟦ from ⟧◑ ≡ ⟦ to ⟧◑)
F≡T ~∘var~> f≡L' tail = refl
F≡T ~∘lam~> f≡L' tail = refl
F≡T ~∘pair~> f≡L' tail = refl
F≡T ~∘pm~> f≡L' tail = refl
F≡T ~∘unit~> f≡L' tail = refl
F≡T (~∙var∷pm■~> γ γ' i M N ≡M) f≡L' tail = ∷pm-eq γ γ' (var i) M N ≡M
F≡T (~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' tail₁) f≡L' tail = refl
F≡T (~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS tail₁) f≡L' tail = refl
F≡T (~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS tail₁) f≡L' tail = refl
F≡T (~∙pair∷pm■~> γ γ' x y M N ≡M) f≡L' tail = ∷pm-eq γ γ' (pair x y) M N ≡M
F≡T (~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' tail₁) f≡L' tail = refl
F≡T (~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS tail₁) f≡L' tail = refl
F≡T (~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS tail₁) f≡L' tail = refl
F≡T (~∙var∷l■~> γ γ' i LHS RHS ≡LHS) f≡L' tail = ∷l-eq γ γ' (var i) LHS RHS ≡LHS
F≡T (~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = refl
F≡T (~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = refl
F≡T (~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = refl
F≡T (~∙lam∷l■~> γ γ' M LHS RHS ≡LHS) f≡L' tail = ∷l-eq γ γ' (lam M) LHS RHS ≡LHS
F≡T (~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = refl
F≡T (~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = refl
F≡T (~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = refl
F≡T (~∙unit∷l■~> γ γ' LHS RHS ≡LHS) f≡L' tail = ∷l-eq γ γ' unit LHS RHS ≡LHS
F≡T (~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = refl
F≡T (~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = refl
F≡T (~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = refl
F≡T (~∙pair∷l■~> γ γ' x y LHS RHS ≡LHS) f≡L' tail = ∷l-eq γ γ' (pair x y) LHS RHS ≡LHS
F≡T (~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = refl
F≡T (~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = refl
F≡T (~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = refl
F≡T (~∙var∷r■~> γ γ' i LHS RHS ≡RHS) f≡L' tail = ∷r-eq γ γ' (var i) LHS RHS ≡RHS
F≡T (~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = refl
F≡T (~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = refl
F≡T (~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = refl
F≡T (~∙lam∷r■~> γ γ' M LHS RHS ≡RHS) f≡L' tail = ∷r-eq γ γ' (lam M) LHS RHS ≡RHS
F≡T (~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = refl
F≡T (~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = refl
F≡T (~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = refl
F≡T (~∙unit∷r■~> γ γ' LHS RHS ≡RHS) f≡L' tail = ∷r-eq γ γ' unit LHS RHS ≡RHS
F≡T (~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = refl
F≡T (~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = refl
F≡T (~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = refl
F≡T (~∙pair∷r■~> γ γ' x y LHS RHS ≡RHS) f≡L' tail = ∷r-eq γ γ' (pair x y) LHS RHS ≡RHS
F≡T (~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = refl
F≡T (~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = refl
F≡T (~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = refl


F≡*T : {from : VState T◾} → {to : VState T◾} → (F>>T : from ~>>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS' RHS) γ') → (⟦ from ⟧◑ ≡ ⟦ to ⟧◑)
F≡*T (_ ~>ᵛᵛ⟨ F>T ⟩) f≡L' tail = F≡T F>T f≡L' tail
F≡*T (_ ~>ᵛᵛ⟨ F>S ⟩ S>>T) f≡L' tail with (F≡T F>S f≡L' tail)
... | F≡S =  trans F≡S (F≡*T S>>T (trans (sym F≡S) f≡L') tail)

T≡F : {from : VState T◾} → {to : VState T◾} → (F>T : from ~>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS' RHS) γ') → (⟦ to ⟧◑ ≡ ⟦ from ⟧◑)
T≡F ~∘var~> f≡L' tail = refl
T≡F ~∘lam~> f≡L' tail = refl
T≡F ~∘pair~> f≡L' tail = refl
T≡F ~∘pm~> f≡L' tail = refl
T≡F ~∘unit~> f≡L' tail = refl
T≡F (~∙var∷pm■~> γ γ' i M N ≡M) f≡L' tail = cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (_ , p)) ≡M
T≡F (~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' tail₁) f≡L' tail = refl
T≡F (~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS tail₁) f≡L' tail = refl
T≡F (~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS tail₁) f≡L' tail = refl
T≡F (~∙pair∷pm■~> γ γ' x y M N ≡M) f≡L' tail = cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (_ , p)) ≡M
T≡F (~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' tail₁) f≡L' tail = refl
T≡F (~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS tail₁) f≡L' tail = refl
T≡F (~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS tail₁) f≡L' tail = refl
T≡F (~∙var∷l■~> γ γ' i LHS RHS ≡LHS) f≡L' tail = cong (λ t₁ → t₁ , _) ≡LHS
T≡F (~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = refl
T≡F (~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = refl
T≡F (~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = refl
T≡F (~∙lam∷l■~> γ γ' M LHS RHS ≡LHS) f≡L' tail = cong (λ t₁ → t₁ , _) ≡LHS
T≡F (~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = refl
T≡F (~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = refl
T≡F (~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = refl
T≡F (~∙unit∷l■~> γ γ' LHS RHS ≡LHS) f≡L' tail = cong (λ t₁ → t₁ , _) ≡LHS
T≡F (~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = refl
T≡F (~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = refl
T≡F (~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = refl
T≡F (~∙pair∷l■~> γ γ' x y LHS RHS ≡LHS) f≡L' tail = cong (λ t₁ → t₁ , _) ≡LHS
T≡F (~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = refl
T≡F (~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = refl
T≡F (~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = refl
T≡F (~∙var∷r■~> γ γ' i LHS RHS ≡RHS) f≡L' tail = cong (λ t₁ → _ , t₁) ≡RHS
T≡F (~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = refl
T≡F (~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = refl
T≡F (~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = refl
T≡F (~∙lam∷r■~> γ γ' M LHS RHS ≡RHS) f≡L' tail = cong (λ t₁ → _ , t₁) ≡RHS
T≡F (~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = refl
T≡F (~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = refl
T≡F (~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = refl
T≡F (~∙unit∷r■~> γ γ' LHS RHS ≡RHS) f≡L' tail = cong (λ t₁ → _ , t₁) ≡RHS
T≡F (~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = refl
T≡F (~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = refl
T≡F (~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = refl
T≡F (~∙pair∷r■~> γ γ' x y LHS RHS ≡RHS) f≡L' tail = {!cong (λ t₁ → _ , t₁) ≡RHS!}
T≡F (~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = refl
T≡F (~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = refl
T≡F (~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = refl

{-
eqd : {from : VState T◾} → {to : VState T◾} → (F>T : from ~>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS' RHS) γ') → (⟦ to ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ')
eqd ~∘var~> f≡L' tail = f≡L'
eqd ~∘lam~> f≡L' tail = f≡L'
eqd ~∘pair~> f≡L' tail = f≡L'
eqd ~∘pm~> f≡L' tail = f≡L'
eqd ~∘unit~> f≡L' tail = f≡L'
eqd (~∙var∷pm■~> γ γ' i M N ≡M) f≡L' tail = trans (cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (_ , p)) ≡M) f≡L'
eqd (~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' tail₁) f≡L' tail = f≡L'
eqd (~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS tail₁) f≡L' tail = f≡L'
eqd (~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS tail₁) f≡L' tail = f≡L'
eqd (~∙pair∷pm■~> γ γ' x y M N ≡M) f≡L' tail =  trans (cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (_ , p)) ≡M) f≡L'
eqd (~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' tail₁) f≡L' tail = f≡L'
eqd (~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS tail₁) f≡L' tail = f≡L'
eqd (~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS tail₁) f≡L' tail = f≡L'
eqd (~∙var∷l■~> γ γ' i LHS RHS ≡LHS) f≡L' tail =  trans (cong (λ t₁ → t₁ , _) ≡LHS) f≡L'
eqd (~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = f≡L'
eqd (~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = f≡L'
eqd (~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = f≡L'
eqd (~∙lam∷l■~> γ γ' M LHS RHS ≡LHS) f≡L' tail =  trans (cong (λ t₁ → t₁ , _) ≡LHS) f≡L'
eqd (~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = f≡L'
eqd (~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = f≡L'
eqd (~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = f≡L'
eqd (~∙unit∷l■~> γ γ' LHS RHS ≡LHS) f≡L' tail =  trans (cong (λ t₁ → t₁ , _) ≡LHS) f≡L'
eqd (~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = f≡L'
eqd (~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = f≡L'
eqd (~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = f≡L'
eqd (~∙pair∷l■~> γ γ' x y LHS RHS ≡LHS) f≡L' tail = trans (cong (λ t₁ → t₁ , _) ≡LHS) f≡L'
eqd (~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' tail₁) f≡L' tail = f≡L'
eqd (~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' tail₁) f≡L' tail = f≡L'
eqd (~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' tail₁) f≡L' tail = f≡L'
eqd (~∙var∷r■~> γ γ' i LHS RHS ≡RHS) f≡L' tail = trans (cong (λ t₁ → ⟦ LHS ⟧ᵛ _ , t₁) ≡RHS) f≡L'
eqd (~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = f≡L'
eqd (~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = f≡L'
eqd (~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = f≡L'
eqd (~∙lam∷r■~> γ γ' M LHS RHS ≡RHS) f≡L' tail = trans (cong (λ t₁ → ⟦ LHS ⟧ᵛ _ , t₁) ≡RHS) f≡L'
eqd (~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = f≡L'
eqd (~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = f≡L'
eqd (~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = f≡L'
eqd (~∙unit∷r■~> γ γ' LHS RHS ≡RHS) f≡L' tail = trans (cong (λ t₁ → ⟦ LHS ⟧ᵛ _ , t₁) ≡RHS) f≡L'
eqd (~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = f≡L'
eqd (~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = f≡L'
eqd (~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = f≡L'
eqd (~∙pair∷r■~> γ γ' x y LHS RHS ≡RHS) f≡L' tail = trans (cong (λ t₁ → ⟦ LHS ⟧ᵛ _ , t₁) ≡RHS) f≡L'
eqd (~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' tail₁) f≡L' tail = f≡L'
eqd (~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' tail₁) f≡L' tail = f≡L'
eqd (~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' tail₁) f≡L' tail = f≡L'
-}

eqdr : {from : VState T◾} → {to : VState T◾} → (F>T : from ~>ᵛᵛ to) → {LHS : Γ' ⊢ᵛ A} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS' : Γ' ⊢ᵛ T◾} → (f≡R' : ⟦ from ⟧◑ ≡ ⟦ RHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS RHS') γ') → (⟦ to ⟧◑ ≡ ⟦ RHS' ⟧ᵛ γ')
eqdr ~∘var~> f≡R' tail = f≡R'
eqdr ~∘lam~> f≡R' tail = f≡R'
eqdr ~∘pair~> f≡R' tail = f≡R'
eqdr ~∘pm~> f≡R' tail = f≡R'
eqdr ~∘unit~> f≡R' tail = f≡R'
eqdr (~∙var∷pm■~> γ γ' i M N ≡M) f≡R' tail = trans (cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p)) ≡M) f≡R'
eqdr (~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' tail₁) f≡R' tail = f≡R'
eqdr (~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS tail₁) f≡R' tail = f≡R'
eqdr (~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS tail₁) f≡R' tail = f≡R'
eqdr (~∙pair∷pm■~> γ γ' x y M N ≡M) f≡R' tail = trans (cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p)) ≡M) f≡R'
eqdr (~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' tail₁) f≡R' tail = f≡R'
eqdr (~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS tail₁) f≡R' tail = f≡R'
eqdr (~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS tail₁) f≡R' tail = f≡R'
eqdr (~∙var∷l■~> γ γ' i LHS RHS ≡LHS) f≡R' tail = trans (cong (λ t₁ → t₁ , ⟦ RHS ⟧ᵛ γ') ≡LHS) f≡R'
eqdr (~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' tail₁) f≡R' tail = f≡R'
eqdr (~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' tail₁) f≡R' tail = f≡R'
eqdr (~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' tail₁) f≡R' tail = f≡R'
eqdr (~∙lam∷l■~> γ γ' M LHS RHS ≡LHS) f≡R' tail = trans (cong (λ t₁ → t₁ , ⟦ RHS ⟧ᵛ γ') ≡LHS) f≡R'
eqdr (~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' tail₁) f≡R' tail = f≡R'
eqdr (~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' tail₁) f≡R' tail = f≡R'
eqdr (~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' tail₁) f≡R' tail = f≡R'
eqdr (~∙unit∷l■~> γ γ' LHS RHS ≡LHS) f≡R' tail = trans (cong (λ t₁ → t₁ , ⟦ RHS ⟧ᵛ γ') ≡LHS) f≡R'
eqdr (~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' tail₁) f≡R' tail = f≡R'
eqdr (~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' tail₁) f≡R' tail = f≡R'
eqdr (~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' tail₁) f≡R' tail = f≡R'
eqdr (~∙pair∷l■~> γ γ' x y LHS RHS ≡LHS) f≡R' tail = trans (cong (λ t₁ → t₁ , ⟦ RHS ⟧ᵛ γ') ≡LHS) f≡R'
eqdr (~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' tail₁) f≡R' tail = f≡R'
eqdr (~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' tail₁) f≡R' tail = f≡R'
eqdr (~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' tail₁) f≡R' tail = f≡R'
eqdr (~∙var∷r■~> γ γ' i LHS RHS ≡RHS) f≡R' tail = trans (cong (λ t₁ → ⟦ LHS ⟧ᵛ γ' , t₁) ≡RHS) f≡R'
eqdr (~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' tail₁) f≡R' tail = f≡R'
eqdr (~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' tail₁) f≡R' tail = f≡R'
eqdr (~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' tail₁) f≡R' tail = f≡R'
eqdr (~∙lam∷r■~> γ γ' M LHS RHS ≡RHS) f≡R' tail = trans (cong (λ t₁ → ⟦ LHS ⟧ᵛ γ' , t₁) ≡RHS) f≡R'
eqdr (~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' tail₁) f≡R' tail = f≡R'
eqdr (~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' tail₁) f≡R' tail = f≡R'
eqdr (~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' tail₁) f≡R' tail = f≡R'
eqdr (~∙unit∷r■~> γ γ' LHS RHS ≡RHS) f≡R' tail = trans (cong (λ t₁ → ⟦ LHS ⟧ᵛ γ' , t₁) ≡RHS) f≡R'
eqdr (~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' tail₁) f≡R' tail = f≡R'
eqdr (~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' tail₁) f≡R' tail = f≡R'
eqdr (~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' tail₁) f≡R' tail = f≡R'
eqdr (~∙pair∷r■~> γ γ' x y LHS RHS ≡RHS) f≡R' tail = trans (cong (λ t₁ → ⟦ LHS ⟧ᵛ γ' , t₁) ≡RHS) f≡R'
eqdr (~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' tail₁) f≡R' tail = f≡R'
eqdr (~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' tail₁) f≡R' tail = f≡R'
eqdr (~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' tail₁) f≡R' tail = f≡R'

eqdpm : {from : VState (T◾₁ `× T◾₂)} → {to : VState (T◾₁ `× T◾₂)} → (F>T : from ~>ᵛᵛ to) → {M' : Γ' ⊢ᵛ (T◾₁ `× T◾₂)} → {γ' : ⟦ Γ' ⟧ˣ} → {N : (Γ' ∙ T◾₁ ∙ T◾₂) ⊢ᵛ C} → (f≡M' : ⟦ from ⟧◑ ≡ ⟦ M' ⟧ᵛ γ') → (tail : valStack T◾ (pm M' N) γ') → (⟦ to ⟧◑ ≡ ⟦ M' ⟧ᵛ γ')
eqdpm ~∘var~> f≡M' tail = f≡M'
eqdpm ~∘lam~> f≡M' tail = f≡M'
eqdpm ~∘pair~> f≡M' tail = f≡M'
eqdpm ~∘pm~> f≡M' tail = f≡M'
eqdpm ~∘unit~> f≡M' tail = f≡M'
eqdpm (~∙var∷pm■~> γ γ' i M N ≡M) f≡M' tail = trans (cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p)) ≡M) f≡M'
eqdpm (~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' tail₁) f≡M' tail = f≡M'
eqdpm (~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS tail₁) f≡M' tail = f≡M'
eqdpm (~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS tail₁) f≡M' tail = f≡M'
eqdpm (~∙pair∷pm■~> γ γ' x y M N ≡M) f≡M' tail = trans (cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p)) ≡M) f≡M'
eqdpm (~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' tail₁) f≡M' tail = f≡M'
eqdpm (~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS tail₁) f≡M' tail = f≡M'
eqdpm (~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS tail₁) f≡M' tail = f≡M'
eqdpm (~∙var∷l■~> γ γ' i LHS RHS ≡LHS) f≡M' tail = trans (cong (λ t₁ → t₁ , ⟦ RHS ⟧ᵛ γ') ≡LHS) f≡M'
eqdpm (~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' tail₁) f≡M' tail = f≡M'
eqdpm (~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' tail₁) f≡M' tail = f≡M'
eqdpm (~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' tail₁) f≡M' tail = f≡M'
eqdpm (~∙lam∷l■~> γ γ' M LHS RHS ≡LHS) f≡M' tail = trans (cong (λ t₁ → t₁ , ⟦ RHS ⟧ᵛ γ') ≡LHS) f≡M'
eqdpm (~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' tail₁) f≡M' tail = f≡M'
eqdpm (~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' tail₁) f≡M' tail = f≡M'
eqdpm (~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' tail₁) f≡M' tail = f≡M'
eqdpm (~∙unit∷l■~> γ γ' LHS RHS ≡LHS) f≡M' tail = trans (cong (λ t₁ → t₁ , ⟦ RHS ⟧ᵛ γ') ≡LHS) f≡M'
eqdpm (~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' tail₁) f≡M' tail = f≡M'
eqdpm (~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' tail₁) f≡M' tail = f≡M'
eqdpm (~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' tail₁) f≡M' tail = f≡M'
eqdpm (~∙pair∷l■~> γ γ' x y LHS RHS ≡LHS) f≡M' tail = trans (cong (λ t₁ → t₁ , ⟦ RHS ⟧ᵛ γ') ≡LHS) f≡M'
eqdpm (~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' tail₁) f≡M' tail = f≡M'
eqdpm (~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' tail₁) f≡M' tail = f≡M'
eqdpm (~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' tail₁) f≡M' tail = f≡M'
eqdpm (~∙var∷r■~> γ γ' i LHS RHS ≡RHS) f≡M' tail = trans (cong (λ t₁ → ⟦ LHS ⟧ᵛ γ' , t₁) ≡RHS) f≡M'
eqdpm (~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' tail₁) f≡M' tail = f≡M'
eqdpm (~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' tail₁) f≡M' tail = f≡M'
eqdpm (~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' tail₁) f≡M' tail = f≡M'
eqdpm (~∙lam∷r■~> γ γ' M LHS RHS ≡RHS) f≡M' tail = trans (cong (λ t₁ → ⟦ LHS ⟧ᵛ γ' , t₁) ≡RHS) f≡M'
eqdpm (~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' tail₁) f≡M' tail = f≡M'
eqdpm (~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' tail₁) f≡M' tail = f≡M'
eqdpm (~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' tail₁) f≡M' tail = f≡M'
eqdpm (~∙unit∷r■~> γ γ' LHS RHS ≡RHS) f≡M' tail = trans (cong (λ t₁ → ⟦ LHS ⟧ᵛ γ' , t₁) ≡RHS) f≡M'
eqdpm (~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' tail₁) f≡M' tail = f≡M'
eqdpm (~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' tail₁) f≡M' tail = f≡M'
eqdpm (~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' tail₁) f≡M' tail = f≡M'
eqdpm (~∙pair∷r■~> γ γ' x y LHS RHS ≡RHS) f≡M' tail = trans (cong (λ t₁ → ⟦ LHS ⟧ᵛ γ' , t₁) ≡RHS) f≡M'
eqdpm (~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' tail₁) f≡M' tail = f≡M'
eqdpm (~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' tail₁) f≡M' tail = f≡M'
eqdpm (~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' tail₁) f≡M' tail = f≡M'

{-
⟨_⟩::l⟨_⟩_ : {from : VState T◾} → {to : VState T◾} → (F>T : from ~>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS' RHS) γ') → (from ::l⟨ f≡L' ⟩ tail) ~>ᵛᵛ (to ::l⟨ trans (T≡F F>T f≡L' tail) f≡L' ⟩ tail)
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
-}

⟨_⟩::r⟨_⟩_ : {from : VState T◾} → {to : VState T◾} → (F>T : from ~>ᵛᵛ to) → {LHS : Γ' ⊢ᵛ A} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS' : Γ' ⊢ᵛ T◾} → (f≡R' : ⟦ from ⟧◑ ≡ ⟦ RHS' ⟧ᵛ γ') → (tail : valStack T◾' (pair LHS RHS') γ') → (from ::r⟨ f≡R' ⟩ tail) ~>ᵛᵛ (to ::r⟨ eqdr F>T f≡R' tail ⟩ tail)
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

⟨_⟩::pm⟨_⟩_ : {from : VState (T◾₁ `× T◾₂)} → {to : VState (T◾₁ `× T◾₂)} → (F>T : from ~>ᵛᵛ to) → {M' : Γ' ⊢ᵛ (T◾₁ `× T◾₂)} → {γ' : ⟦ Γ' ⟧ˣ} → {N : (Γ' ∙ T◾₁ ∙ T◾₂) ⊢ᵛ C} → (f≡M' : ⟦ from ⟧◑ ≡ ⟦ M' ⟧ᵛ γ') → (tail : valStack T◾ (pm M' N) γ') → (from ::pm⟨ f≡M' ⟩ tail) ~>ᵛᵛ (to ::pm⟨ eqdpm F>T f≡M' tail ⟩ tail)
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
