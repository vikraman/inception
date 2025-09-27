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

infix 26 ⇡_
-- infix 26 ⇡ᴹ_
-- infix 26 ⇡ᴸ_
-- infix 26 ⇡ᴿ_
infixr 25 _⹁_∷_

infix 20 ∘_
infix 20 ∙_

infix 15 _~>ᵛᵛ_
infix 15 _→ᵛᵛ_

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

data partialTerm : (Γ : Ctx) → (X : Ty) → Set where

    ⇡_ : (M : Γ ⊢ᵛ X) → partialTerm Γ X

    ⇡ᴹ : (M : Γ ⊢ᵛ X `× Y) → (N : (Γ ∙ X ∙ Y) ⊢ᵛ Z) → partialTerm Γ Z

    ⇡ᴸ : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → partialTerm Γ (X `× Y)

    ⇡ᴿ  : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → partialTerm Γ (X `× Y)

data vStack : (T◾ : Ty) → Set where

    □ : {T◾ : Ty} → vStack T◾

    _⹁_∷_ : partialTerm Γ X → (γ : ⟦ Γ ⟧ˣ) → vStack T◾ → vStack T◾


data vState : (T◾ : Ty) → Set where

     ∘_ : vStack T◾ → vState T◾

     ∙_ : vStack T◾ → vState T◾

data _→ᵛᵛ_ : vState T◾ → vState T◾ → Set where

     ~∘var~>   : {γ : ⟦ Γ ⟧ˣ} → {i : Γ ∋ X} → {tail : vStack T◾} → ∘ ⇡ var i ⹁ γ ∷ tail →ᵛᵛ ∙ ⇡ (var i) ⹁ γ ∷ tail

     ~∘lam~> : {γ : ⟦ Γ ⟧ˣ} → {M : (Γ ∙ X) ⊢ᶜ Y} → {tail : vStack T◾} → ∘ ⇡ lam M ⹁ γ ∷ tail →ᵛᵛ ∙ ⇡ lam M ⹁ γ ∷ tail

     ~∘pair~> : {γ : ⟦ Γ ⟧ˣ} → {LHS : Γ ⊢ᵛ X} → {RHS : Γ ⊢ᵛ Y} → {tail : vStack T◾} → ∘ ⇡ pair LHS RHS ⹁ γ ∷ tail →ᵛᵛ ∘ ⇡ LHS ⹁ γ ∷ ⇡ᴸ LHS RHS ⹁ γ ∷ tail

     ~∘pm~> : {γ : ⟦ Γ ⟧ˣ} → {M : Γ ⊢ᵛ X `× Y} → {N : (Γ ∙ X ∙ Y) ⊢ᵛ Z} → {tail : vStack T◾} → ∘ ⇡ pm M N ⹁ γ ∷ tail →ᵛᵛ ∘ ⇡ᴹ M N ⹁ γ ∷ tail

     ~∘unit~> : {γ : ⟦ Γ ⟧ˣ} → {tail : vStack T◾} → ∘ ⇡ unit ⹁ γ ∷ tail →ᵛᵛ ∙ ⇡ unit ⹁ γ ∷ tail

     ~∙M∷pm~> : {γ : ⟦ Γ ⟧ˣ} → {γ' : ⟦ Γ' ⟧ˣ} → {M₂ : Γ ⊢ᵛ X `× Y} → {M : Γ' ⊢ᵛ X `× Y} → {N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z'} → {tail : vStack T◾}
                 →    ∙ ⇡ M₂ ⹁ γ ∷ ⇡ᴹ M N ⹁ γ' ∷ tail →ᵛᵛ ∘ ⇡ N ⹁ ((γ' , proj₁ (⟦ M₂ ⟧ᵛ γ)) , proj₂ (⟦ M₂ ⟧ᵛ γ)) ∷ tail

     ~∙M∷l~> : {γ : ⟦ Γ ⟧ˣ} → {γ' : ⟦ Γ' ⟧ˣ} → {M : Γ ⊢ᵛ X} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y} → {tail : vStack T◾}
                 →    ∙ ⇡ M ⹁ γ ∷ ⇡ᴸ LHS RHS ⹁ γ' ∷ tail →ᵛᵛ ∘ ⇡ RHS ⹁ γ' ∷ ⇡ᴿ (var h) (wk-val (wk-wk wk-id) RHS) ⹁ (γ' ,  ⟦ M ⟧ᵛ γ) ∷ tail

     ~∙M∷r~> : {γ : ⟦ Γ ⟧ˣ} → {γ' : ⟦ Γ' ⟧ˣ} → {M : Γ ⊢ᵛ Y} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y} → {tail : vStack T◾}
                 →   ∙ ⇡ M ⹁ γ ∷ ⇡ᴿ LHS RHS ⹁ γ' ∷ tail →ᵛᵛ ∙ ⇡ pair (wk-val (wk-wk wk-id) LHS) (var h) ⹁ (γ' , ⟦ M ⟧ᵛ γ) ∷ tail
