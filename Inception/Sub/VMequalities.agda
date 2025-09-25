module Inception.Sub.VMequalities (R : Set) where

open import Agda.Builtin.Unit
open import Function.Base using (id)
open import Data.Product using (proj₁; proj₂; _,_; Σ; ∃; Σ-syntax; ∃-syntax)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; sym)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Inception.Sub.ValueMachine R

open import Data.Product as P


var∷pm≡N : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (i : Γ ∋ X `× Y) → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z') → (≡M : ⟦ var i ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ')
           →   ⟦ pm M N ⟧ᵛ γ' ≡ ⟦ N ⟧ᵛ ((γ' , proj₁ (⟦ var i ⟧ᵛ γ)) , proj₂ (⟦ var i ⟧ᵛ γ))
var∷pm≡N γ γ' i M N ≡M =
                ⟦ pm M N ⟧ᵛ γ'
              ≡⟨ refl ⟩
                 ⟦ N ⟧ᵛ ( assocl (< idf , ⟦ M ⟧ᵛ > γ'))
              ≡⟨ refl ⟩
                 ⟦ N ⟧ᵛ ( assocl (γ' , ⟦ M ⟧ᵛ γ'))
              ≡⟨ cong (λ x → ⟦ N ⟧ᵛ ( assocl (γ' , x))) (sym ≡M) ⟩
                 ⟦ N ⟧ᵛ ( assocl (γ' , ⟦ var i ⟧ᵛ γ))
              ≡⟨ refl ⟩
                ⟦ N ⟧ᵛ ((γ' , proj₁ (⟦ var i ⟧ᵛ γ)) , proj₂ (⟦ var i ⟧ᵛ γ)) ∎


--     ~∙var∷pm■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
--                 → (i : Γ ∋ X `× Y)
--                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z')
--                 → .(≡M : ⟦ var i ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ')
--                 →    ∙[var] var i ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ■
--                      ~>ᵛᵛ
--                        ∘ N ﹐ ((γ' , proj₁ (⟦ var i ⟧ᵛ γ)) , proj₂ (⟦ var i ⟧ᵛ γ)) ■
--
--     ~∙pair∷pm■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
--                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
--                 → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z')
--                 → .(≡M : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ')
--                 →    ∙[pair] pair x y ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ■
--                      ~>ᵛᵛ
--                       ∘ N ﹐ ((γ' ,  ⟦ x ⟧ᵛ γ) ,  ⟦ y ⟧ᵛ γ) ■




--     ~∙var∷l■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
--                 → (i : Γ ∋ X)
--                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
--                 → .(≡LHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ')
--                 →   ∙[var] var i ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ■
--                      ~>ᵛᵛ
--                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ var i ⟧ᵛ γ) ■
--
--     ~∙lam∷l■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
--                 → (M : (Γ ∙ X) ⊢ᶜ Y)
--                 → (LHS : Γ' ⊢ᵛ X `⇒ Y) → (RHS : Γ' ⊢ᵛ Z)
--                 → .(≡LHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ')
--                 →   ∙[lam] lam M ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ■
--                      ~>ᵛᵛ
--                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ lam M ⟧ᵛ γ) ■
--
--     ~∙unit∷l■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
--                 → (LHS : Γ' ⊢ᵛ `Unit) → (RHS : Γ' ⊢ᵛ Y)
--                 → .(≡LHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ')
--                 →   ∙[unit] unit ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ■
--                      ~>ᵛᵛ
--                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ unit ⟧ᵛ γ) ■
--
--     ~∙pair∷l■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
--                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
--                 → (LHS : Γ' ⊢ᵛ X `× Y) → (RHS : Γ' ⊢ᵛ Z)
--                 → .(≡LHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ LHS ⟧ᵛ γ')
--                 →   ∙[pair] pair x y ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ■
--                      ~>ᵛᵛ
--                     ∘ RHS ﹐ γ' ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ' ,  ⟦ pair x y ⟧ᵛ γ) ■




--     ~∙var∷r■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
--                 → (i : Γ ∋ Y)
--                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ Y)
--                 → .(≡RHS : ⟦ var i ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ')
--                 →   ∙[var] var i ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ■
--                      ~>ᵛᵛ
--                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ var i ⟧ᵛ γ) ■
--
--     ~∙lam∷r■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
--                 → (M : (Γ ∙ X) ⊢ᶜ Y)
--                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `⇒ Y)
--                 → .(≡RHS : ⟦ lam M ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ')
--                 →   ∙[lam] lam M ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ■
--                      ~>ᵛᵛ
--                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ lam M ⟧ᵛ γ) ■
--
--     ~∙unit∷r■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
--                 → (LHS : Γ' ⊢ᵛ X) → (RHS : Γ' ⊢ᵛ `Unit)
--                 → .(≡RHS : ⟦ unit ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ')
--                 →   ∙[unit] unit ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ■
--                      ~>ᵛᵛ
--                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ unit ⟧ᵛ γ) ■
--
--     ~∙pair∷r■~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ)
--                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y)
--                 → (LHS : Γ' ⊢ᵛ Z) → (RHS : Γ' ⊢ᵛ X `× Y)
--                 → .(≡RHS : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ RHS ⟧ᵛ γ')
--                 →   ∙[pair] pair x y ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ■
--                      ~>ᵛᵛ
--                     ∙[pair] pair (wk-val (wk-wk wk-id) LHS) (var h) ﹐ (γ' , ⟦ pair x y ⟧ᵛ γ) ■
--
