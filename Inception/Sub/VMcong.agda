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

-- ⟪_⟫::l⟨_⨾_⟩_ : {from : VState T◾} → {to : VState T◾} → (F>>T : from ~>>ᵛᵛ to) → {LHS' : Γ' ⊢ᵛ T◾} → {γ' : ⟦ Γ' ⟧ˣ} → {RHS : Γ' ⊢ᵛ B} → (f≡L' : ⟦ from ⟧◑ ≡ ⟦ LHS' ⟧ᵛ γ') → (f≡t : ⟦ from ⟧◑ ≡ ⟦ to ⟧◑) → (tail : valStack T◾' (pair LHS' RHS) γ') → (from ::l⟨ f≡L' ⟩ tail) ~>>ᵛᵛ (to ::l⟨ trans (sym f≡t) f≡L' ⟩ tail)
-- 
-- ⟪ _ ~>ᵛᵛ⟨ F>S ⟩ ⟫::l⟨ f≡L' ⨾ f≡t ⟩ tail = (_ ::l⟨ _ ⟩ tail) ~>ᵛᵛ⟨ (⟨ F>S ⟩::l⟨ f≡L' ⟩ tail) ⟩
-- ⟪ _ ~>ᵛᵛ⟨ F>S ⟩ F>>T ⟫::l⟨ f≡L' ⨾ f≡t ⟩ tail = {!!}
