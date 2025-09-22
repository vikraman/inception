module Inception.Sub.ValueMachine (R : Set) where

open import Function.Base using (id)
open import Data.Product using (proj₁; proj₂; _,_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; sym)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

variable
  A' B' C' D' X Y Z X' Y' Z' X₁ Y₁ Z₁ X₂ Y₂ Z₂ X◾ Y◾ Z◾ X↓ Y↓ Z↓ T◾ : Ty
  Γ' Γ'' Γ''' Δ' Γ₁ Γ₂ Γ◾ Γ↓ : Ctx


infix 40 _▣
infixr 35 _~>ᵛᵛ⟨_⟩_
infix 30 _﹐_■
infixr 25 _﹐_∷pm⟨_⟩_
infixr 25 _﹐_∷l⟨_⟩_
infixr 25 _﹐_∷r⟨_⟩_
infix 20 ∘_
infix 15 _~>ᵛᵛ_
infix 15 _~>ᵛᵛ*_


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
                     ∘ (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ unit ⟧ᵛ γ) ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ unit ⟧ᵛ γ) ∷r⟨ trans (cong (λ t → (t , ⟦ RHS ⟧ᵛ γ') ) ≡LHS) ≡RHS' ⟩ tail

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


data _~>ᵛᵛ*_ : VState T◾ → VState T◾ → Set where

  _▣ : (VS : VState T◾) → VS ~>ᵛᵛ* VS

  _~>ᵛᵛ⟨_⟩_ : (VS : VState T◾) {VS' VS'' : VState T◾} → VS ~>ᵛᵛ VS' → VS' ~>ᵛᵛ* VS'' → VS ~>ᵛᵛ* VS''


data haltingVState : VState T◾ → Set where

     ∙var■ : {γ : ⟦ Γ ⟧ˣ} → {i : Γ ∋ X} → haltingVState (∙[var] (var i) ﹐ γ ■)

     ∙unit■ : {γ : ⟦ Γ ⟧ˣ} → haltingVState (∙[unit] unit ﹐ γ ■)

     ∙pair■ : {γ : ⟦ Γ ⟧ˣ} → {LHS : Γ ⊢ᵛ X} → {RHS : Γ ⊢ᵛ Y} → haltingVState (∙[pair] pair LHS RHS ﹐ γ ■)

     ∙lam■ : {γ : ⟦ Γ ⟧ˣ} → {M : (Γ ∙ X) ⊢ᶜ Y} → haltingVState (∙[lam] lam M ﹐ γ ■)


~>ᵛᵛ*-trans : {S S' S'' : VState T◾} → S ~>ᵛᵛ* S' → S' ~>ᵛᵛ* S'' → S ~>ᵛᵛ* S''
~>ᵛᵛ*-trans (S~>S ▣) S~>S'' = S~>S''
~>ᵛᵛ*-trans (S ~>ᵛᵛ⟨ x ⟩ T~>S') S'~>S'' =  S ~>ᵛᵛ⟨ x ⟩ (~>ᵛᵛ*-trans T~>S' S'~>S'')

------------------------------------------------------------------

lem0 : {x : ⟦ X ⟧} → {γ : ⟦ Γ ⟧ˣ} → (i : Γ ∋ X') → ⟦ (wk-mem (wk-wk wk-id) i) ⟧ᵐ (γ , x) ≡ ((λ r → proj₁ r) ； ⟦ wk-mem wk-id i ⟧ᵐ) (γ , x)
lem0 h = refl
lem0 (t i) = refl

lem1 : {y : ⟦ Y ⟧} → {γ' : ⟦ Γ' ⟧ˣ} {i₁ : Γ ∋ X} → {i₂ : Γ' ∋ X'}
      → ⟦ var i₂ ⟧ᵛ γ' ≡ ⟦ (wk-val (wk-wk wk-id) (var i₂)) ⟧ᵛ (γ' , y)
lem1 {γ' = γ'} {i₁ = i₁} {i₂ = h} = refl
lem1 {Γ = Γ Cx.∙ A} {y = y} {γ' = γ' , x} {i₁ = i₁} {i₂ = Cx.t i₂} =
           ⟦ var (t i₂) ⟧ᵛ (γ' , x)
         ≡⟨ refl ⟩ ⟦ t i₂ ⟧ᵐ (γ' , x)
         ≡⟨ refl ⟩  ⟦ i₂ ⟧ᵐ γ'
         ≡⟨ refl ⟩  ⟦ var i₂ ⟧ᵛ γ'
         ≡⟨ lem1 {i₁ = i₁} {i₂ = i₂} ⟩ ⟦ wk-val (wk-wk wk-id) (var i₂) ⟧ᵛ (γ' , x)
         ≡⟨ refl ⟩ ⟦ var (wk-mem (wk-wk wk-id) i₂) ⟧ᵛ (γ' , x)
         ≡⟨ refl ⟩ ⟦ (wk-mem (wk-wk wk-id) i₂) ⟧ᵐ (γ' , x)
         ≡⟨ lem0 {x = x} {γ = γ'} i₂ ⟩ ((λ r → proj₁ r) ； ⟦ wk-mem wk-id i₂ ⟧ᵐ) (γ' , x)
         ≡⟨ refl ⟩ ⟦ wk-mem wk-id (t i₂) ⟧ᵐ (γ' , x)
         ≡⟨ refl ⟩ ⟦ t (wk-mem wk-id (t i₂))  ⟧ᵐ ((γ' , x) , y)
         ≡⟨ refl ⟩ ⟦ var (t (wk-mem wk-id (t i₂)))  ⟧ᵛ ((γ' , x) , y)
         ≡⟨ refl ⟩ ⟦ var (wk-mem (wk-wk wk-id) (t i₂))  ⟧ᵛ ((γ' , x) , y)
         ≡⟨ refl ⟩ ⟦ wk-val (wk-wk wk-id) (var (t i₂)) ⟧ᵛ ((γ' , x) , y) ∎

-- lem {Γ = ε ∙ A} {γ = γ} {γ' = γ'} {i₁ = i₁} {i₂ = t i₂} =
--          ⟦ var (t i₂) ⟧ᵛ γ'
--        ≡⟨ refl ⟩ ⟦ t i₂ ⟧ᵐ γ'
--        ≡⟨ {!!} ⟩ {!!}
--        ≡⟨ {!!} ⟩ ⟦ wk-mem wk-id (t i₂) ⟧ᵐ γ'
--        ≡⟨ refl ⟩ ⟦ t (wk-mem wk-id (t i₂))  ⟧ᵐ (γ' , ⟦ i₁ ⟧ᵐ γ)
--        ≡⟨ refl ⟩ ⟦ var (t (wk-mem wk-id (t i₂)))  ⟧ᵛ (γ' , ⟦ i₁ ⟧ᵐ γ)
--        ≡⟨ refl ⟩ ⟦ var (wk-mem (wk-wk wk-id) (t i₂))  ⟧ᵛ (γ' , ⟦ i₁ ⟧ᵐ γ)
--        ≡⟨ refl ⟩ ⟦ wk-val (wk-wk wk-id) (var (t i₂)) ⟧ᵛ (γ' , ⟦ i₁ ⟧ᵐ γ) ∎
-- lem {i₁ = Cx.h} {i₂ = Cx.h} = refl
-- lem {i₁ = h} {i₂ = Cx.t i₂} {γ = γ} {γ' = γ'}= {!refl!}
-- lem {i₁ = Cx.t i₁} {i₂ = i₂} = {!!}



------------------------------------------------------------------

{-
∙[var]∷l-cong :   {γ : ⟦ Γ ⟧ˣ} → {γ' : ⟦ Γ' ⟧ˣ} → {τ : ⟦ Γ'' ⟧ˣ}
     → {LHS' : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y}
     ---
     → {M : Γ ⊢ᵛ X}
     → {t : Γ'' ∋ X}
     → {≡T : ⟦ LHS' ⟧ᵛ γ' ≡ ⟦ var t ⟧ᵛ τ}
     ---
     → {≡LHS' : ⟦ M ⟧ᵛ γ ≡ ⟦ LHS' ⟧ᵛ γ'}
     ---
     → {tail : valStack X (pair LHS' RHS) γ'}
     → ∘ M ﹐ γ ■ ~>ᵛᵛ* ∙[var] var t ﹐ τ ■
     → ∘ M ﹐ γ ∷l⟨ ≡LHS' ⟩ tail ~>ᵛᵛ* ∙[var] var t ﹐ τ ∷l⟨ sym ≡T ⟩ tail
∙[var]∷l-cong M>T = {!!}

∙[lam]∷l-cong :   {γ : ⟦ Γ ⟧ˣ} → {γ' : ⟦ Γ' ⟧ˣ} → {τ : ⟦ Γ'' ⟧ˣ}
     → {LHS' : Γ' ⊢ᵛ (X `⇒ X')} → {RHS : Γ' ⊢ᵛ Y}
     ---
     → {M : Γ ⊢ᵛ X `⇒ X'}
     → {T : (Γ'' ∙ X) ⊢ᶜ X'}
     → {≡T : ⟦ LHS' ⟧ᵛ γ' ≡ ⟦ lam T ⟧ᵛ τ}
     ---
     → {≡LHS' : ⟦ M ⟧ᵛ γ ≡ ⟦ LHS' ⟧ᵛ γ'}
     ---
     → {tail : valStack (X `⇒ X') (pair LHS' RHS) γ'}
     → ∘ M ﹐ γ ■ ~>ᵛᵛ* ∙[lam] lam T ﹐ τ ■
     → ∘ M ﹐ γ ∷l⟨ ≡LHS' ⟩ tail ~>ᵛᵛ* ∙[lam] lam T ﹐ τ ∷l⟨ sym ≡T ⟩ tail
∙[lam]∷l-cong M>T = {!!}

∙[unit]∷l-cong :   {γ : ⟦ Γ ⟧ˣ} → {γ' : ⟦ Γ' ⟧ˣ} → {τ : ⟦ Γ'' ⟧ˣ}
     → {LHS' : Γ' ⊢ᵛ `Unit} → {RHS : Γ' ⊢ᵛ Y}
     ---
     → {M : Γ ⊢ᵛ `Unit}
     → {≡T : ⟦ LHS' ⟧ᵛ γ' ≡ ⟦ unit ⟧ᵛ τ}
     ---
     → {≡LHS' : ⟦ M ⟧ᵛ γ ≡ ⟦ LHS' ⟧ᵛ γ'}
     ---
     → {tail : valStack `Unit (pair LHS' RHS) γ'}
     → ∘ M ﹐ γ ■ ~>ᵛᵛ* ∙[unit] unit ﹐ τ ■
     → ∘ M ﹐ γ ∷l⟨ ≡LHS' ⟩ tail ~>ᵛᵛ* ∙[unit] unit ﹐ τ ∷l⟨ sym ≡T ⟩ tail
∙[unit]∷l-cong M>T = {!!}
-}

{-
∙[pair]∷l-cong :   {γ : ⟦ Γ ⟧ˣ} → {γ' : ⟦ Γ' ⟧ˣ} → {τ : ⟦ Γ'' ⟧ˣ}
     → {LHS : Γ ⊢ᵛ X₁ `× X₂} → {LHS' : Γ' ⊢ᵛ X₁ `× X₂} → {RHS : Γ' ⊢ᵛ Y}
     → {T₁ : Γ'' ⊢ᵛ X₁} → {T₂ : Γ'' ⊢ᵛ X₂}
     → (≡LHS' : ⟦ LHS ⟧ᵛ γ ≡ ⟦ LHS' ⟧ᵛ γ')
     → (≡T : ⟦ LHS' ⟧ᵛ γ' ≡ ⟦ pair T₁ T₂ ⟧ᵛ τ)
     → (tail : valStack ((X₁ `× X₂) `× Y) (pair LHS' RHS) γ')
     → ∘ LHS ﹐ γ ■ ~>ᵛᵛ* ∙[pair] pair T₁ T₂ ﹐ τ ■
     → ∘ LHS ﹐ γ ∷l⟨ ≡LHS' ⟩ tail ~>ᵛᵛ* ∙[pair] pair T₁ T₂ ﹐ τ ∷l⟨ sym ≡T ⟩ tail
∙[pair]∷l-cong ≡LHS' ≡T tail (.(∘ var _ ﹐ _ ■) ~>ᵛᵛ⟨ ~∘var~> ⟩ .(∙[var] (var _ ﹐ _ ■)) ~>ᵛᵛ⟨ () ⟩ L>T)
∙[pair]∷l-cong {LHS = pair (var i₁) (var i₂)} ≡LHS' ≡T tail ((∘ pair (var i₁) (var i₂) ﹐ γ ■) ~>ᵛᵛ⟨ ~∘pair~> ⟩ .(∘ var i₁ ﹐ _ ∷l⟨ refl ⟩ pair (var i₁) (var i₂) ﹐ _ ■) ~>ᵛᵛ⟨ ~∘var~> ⟩ L>T) =
                   -------------------------------------------------------------->
                                                                                  (∘ pair (var i₁) (var i₂) ﹐ γ ∷l⟨ ≡LHS' ⟩ tail)
                    ~>ᵛᵛ⟨ ~∘pair~> ⟩                                               (∘ (var i₁) ﹐ γ ∷l⟨ refl ⟩ pair (var i₁) (var i₂) ﹐ γ ∷l⟨ ≡LHS' ⟩ tail)
                    ~>ᵛᵛ⟨ ~∘var~> ⟩                                                (∙[var] (var i₁) ﹐ γ ∷l⟨ refl ⟩ pair (var i₁) (var i₂) ﹐ γ ∷l⟨ ≡LHS' ⟩ tail)
                    ~>ᵛᵛ⟨ ~∙var∷l∷l~> γ γ i₁ (var i₁) (var i₂) refl ≡LHS' tail ⟩  (∘ (var i₂) ﹐  γ ∷r⟨ lem1 ⟩ pair (var h) (wk-val (wk-wk wk-id) (var i₂)) ﹐  γ ,  ⟦ var i₁ ⟧ᵛ γ ∷l⟨ {! trans (cong (λ t → (t , ⟦ var i₂ ⟧ᵛ γ) ) refl) ≡LHS'!} ⟩ tail)
                    ~>ᵛᵛ⟨ {!!} ⟩  {!!}

-- (∘ (var i₂) ﹐ γ ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) (var i₂)) ﹐ (γ ,  ⟦ var i₁ ⟧ᵛ γ) ∷l⟨ trans (cong (λ t → (t , ⟦ var i₂ ⟧ᵛ γ) ) refl) ≡LHS' ⟩ tail)
-- (wk-val (wk-wk wk-id) (var i₂)) ﹐ (γ ,  ⟦ var i₁ ⟧ᵛ γ) ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) (var i₂)) ﹐ (γ ,  ⟦ var i₁ ⟧ᵛ γ) ∷l⟨ ? ⟩ tail

∙[pair]∷l-cong {LHS = pair (var i) (lam x)} ≡LHS' ≡T tail (.(∘ pair (var i) (lam x) ﹐ _ ■) ~>ᵛᵛ⟨ ~∘pair~> ⟩ .(∘ var i ﹐ _ ∷l⟨ refl ⟩ pair (var i) (lam x) ﹐ _ ■) ~>ᵛᵛ⟨ ~∘var~> ⟩ L>T) = {!!}
∙[pair]∷l-cong {LHS = pair (var i) (pair M M₁)} ≡LHS' ≡T tail (.(∘ pair (var i) (pair M M₁) ﹐ _ ■) ~>ᵛᵛ⟨ ~∘pair~> ⟩ .(∘ var i ﹐ _ ∷l⟨ refl ⟩ pair (var i) (pair M M₁) ﹐ _ ■) ~>ᵛᵛ⟨ ~∘var~> ⟩ L>T) = {!!}
∙[pair]∷l-cong {LHS = pair (var i) (pm M M₁)} ≡LHS' ≡T tail (.(∘ pair (var i) (pm M M₁) ﹐ _ ■) ~>ᵛᵛ⟨ ~∘pair~> ⟩ .(∘ var i ﹐ _ ∷l⟨ refl ⟩ pair (var i) (pm M M₁) ﹐ _ ■) ~>ᵛᵛ⟨ ~∘var~> ⟩ L>T) = {!!}
∙[pair]∷l-cong {LHS = pair (var i) unit} ≡LHS' ≡T tail (.(∘ pair (var i) unit ﹐ _ ■) ~>ᵛᵛ⟨ ~∘pair~> ⟩ .(∘ var i ﹐ _ ∷l⟨ refl ⟩ pair (var i) unit ﹐ _ ■) ~>ᵛᵛ⟨ ~∘var~> ⟩ L>T) = {!!}

--(∘ pair (var i₁) (var i₂) ﹐ γ ∷l⟨ ≡LHS' ⟩ tail) ~>ᵛᵛ⟨ ~∘pair~> ⟩ {!!} ~>ᵛᵛ⟨ {!!} ⟩ {!!}
∙[pair]∷l-cong ≡LHS' ≡T tail (.(∘ pair (lam _) _ ﹐ _ ■) ~>ᵛᵛ⟨ ~∘pair~> ⟩ .(∘ lam _ ﹐ _ ∷l⟨ refl ⟩ pair (lam _) _ ﹐ _ ■) ~>ᵛᵛ⟨ ~∘lam~> ⟩ L>T) = {!!}
∙[pair]∷l-cong ≡LHS' ≡T tail (.(∘ pair (pair _ _) _ ﹐ _ ■) ~>ᵛᵛ⟨ ~∘pair~> ⟩ .(∘ pair _ _ ﹐ _ ∷l⟨ refl ⟩ pair (pair _ _) _ ﹐ _ ■) ~>ᵛᵛ⟨ ~∘pair~> ⟩ L>T) = {!!}
∙[pair]∷l-cong ≡LHS' ≡T tail (.(∘ pair (pm _ _) _ ﹐ _ ■) ~>ᵛᵛ⟨ ~∘pair~> ⟩ .(∘ pm _ _ ﹐ _ ∷l⟨ refl ⟩ pair (pm _ _) _ ﹐ _ ■) ~>ᵛᵛ⟨ ~∘pm~> ⟩ L>T) = {!!}
∙[pair]∷l-cong ≡LHS' ≡T tail (.(∘ pair unit _ ﹐ _ ■) ~>ᵛᵛ⟨ ~∘pair~> ⟩ .(∘ unit ﹐ _ ∷l⟨ refl ⟩ pair unit _ ﹐ _ ■) ~>ᵛᵛ⟨ ~∘unit~> ⟩ L>T) = {!!}
∙[pair]∷l-cong ≡LHS' ≡T tail (.(∘ pm _ _ ﹐ _ ■) ~>ᵛᵛ⟨ ~∘pm~> ⟩ L>T) = {!!}
-}
