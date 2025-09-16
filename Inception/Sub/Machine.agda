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

data State : Set where

     ∘_ : {M : Γ ⊢ᵛ A} → {γ : ⟦ Γ ⟧ˣ} → valStack M γ → State

     ∙_ : {M : Γ ⊢ᵛ A} → {γ : ⟦ Γ ⟧ˣ} → valStack M γ → State

infix 15 _~>_

eq-pm : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (x : Γ ⊢ᵛ X) -> (y : Γ ⊢ᵛ Y) → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z)
                 → (≡M : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ')
                 → ⟦ N ⟧ᵛ ((γ' , ⟦ x ⟧ᵛ γ) , ⟦ y ⟧ᵛ γ) ≡ ⟦ (pm M N) ⟧ᵛ γ'
eq-pm γ γ' γ'' x y M N ≡M =         ⟦ N ⟧ᵛ ((γ' , ⟦ x ⟧ᵛ γ) , ⟦ y ⟧ᵛ γ)
                                ≡⟨ refl ⟩
                                    (assocl ； ⟦ N ⟧ᵛ) (γ' , ⟦ pair x y ⟧ᵛ γ)
                                ≡⟨  cong (λ p → (assocl ； ⟦ N ⟧ᵛ) (γ' , p) ) ≡M ⟩
                                    (assocl ； ⟦ N ⟧ᵛ) (γ' , ⟦ M ⟧ᵛ γ')
                                ≡⟨ refl ⟩
                                    (< idf , ⟦ M ⟧ᵛ > ； assocl ； ⟦ N ⟧ᵛ) γ'
                                ≡⟨ refl ⟩
                                    ⟦ (pm M N) ⟧ᵛ γ' ∎


data _~>_ : State → State → Set where

     ~∘var■~>   : (γ : ⟦ Γ ⟧ˣ) → (i : Γ ∋ A)
                  → ∘ var i , γ ■ ~> ∙ var i , γ ■

     ~∙pair∷pm∷pm~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (x : Γ ⊢ᵛ X) → (y : Γ ⊢ᵛ Y) → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ X' `× Y')
                 → (M' : Γ'' ⊢ᵛ X' `× Y') → (N' : (Γ'' ∙ X' ∙ Y') ⊢ᵛ C)
                 → (≡M : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ') → (≡M' : ⟦ (pm M N) ⟧ᵛ γ' ≡ ⟦ M' ⟧ᵛ γ'')
                 → (tail : valStack (pm M' N') γ'')
                 →   ∙ pair x y , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ∷pm⟨ ≡M' ⟩ tail
                      ~>
                      ∘ N , ((γ' ,  ⟦ x ⟧ᵛ γ) ,  ⟦ y ⟧ᵛ γ) ∷pm⟨ trans (eq-pm γ γ' γ'' x y M N ≡M) ≡M' ⟩ tail

     ~∙pair∷pm∷l~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (x : Γ ⊢ᵛ X) -> (y : Γ ⊢ᵛ Y) → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z) → (LHS : Γ'' ⊢ᵛ Z) → (RHS : Γ'' ⊢ᵛ Z')
                 → (≡M : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ') → (≡LHS : ⟦ (pm M N) ⟧ᵛ γ' ≡ ⟦ LHS ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS RHS) γ'')
                 ->    ∙ pair x y , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ∷l⟨ ≡LHS ⟩ tail
                      ~>
                       ∘ N , ((γ' ,  ⟦ x ⟧ᵛ γ) ,  ⟦ y ⟧ᵛ γ) ∷l⟨ trans (eq-pm γ γ' γ'' x y M N ≡M) ≡LHS ⟩ tail

     ~∙pair∷pm∷r~> : (γ : ⟦ Γ ⟧ˣ) → (γ' : ⟦ Γ' ⟧ˣ) → (γ'' : ⟦ Γ'' ⟧ˣ)
                 → (x : Γ ⊢ᵛ X) -> (y : Γ ⊢ᵛ Y) → (M : Γ' ⊢ᵛ X `× Y) → (N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z') → (LHS : Γ'' ⊢ᵛ Z) → (RHS : Γ'' ⊢ᵛ Z')
                 → (≡M : ⟦ pair x y ⟧ᵛ γ ≡ ⟦ M ⟧ᵛ γ') → (≡RHS : ⟦ (pm M N) ⟧ᵛ γ' ≡ ⟦ RHS ⟧ᵛ γ'')
                 → (tail : valStack (pair LHS RHS) γ'')
                 ->    ∙ pair x y , γ ∷pm⟨ ≡M ⟩ pm M N , γ' ∷r⟨ ≡RHS ⟩ tail
                      ~>
                       ∘ N , ((γ' ,  ⟦ x ⟧ᵛ γ) ,  ⟦ y ⟧ᵛ γ) ∷r⟨ trans (eq-pm γ γ' γ'' x y M N ≡M) ≡RHS ⟩ tail


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


------------------------------------------------------------------------------------------------------
-- OLD stuff

{- _⊕_ : Ctx → Ctx → Ctx
Γ ⊕ ε = Γ
Γ ⊕ (Δ ∙ x) = (Γ ⊕ Δ) ∙ x

⊕-assoc : (Γ ⊕ Ψ) ⊕ Δ ≡ Γ ⊕ (Ψ ⊕ Δ)
⊕-assoc {Γ} {Ψ} {ε} = refl
⊕-assoc {Γ} {Ψ} {Δ ∙ x} rewrite ⊕-assoc {Γ} {Ψ} {Δ} = refl

⊕-left-id : (Γ : Ctx) → ε ⊕ Γ ≡ Γ
⊕-left-id ε = refl
⊕-left-id (Γ ∙ x) rewrite ⊕-left-id Γ = refl

ext-⊇-R : (Γ ⊕ Δ) ⊇ Δ
ext-⊇-R {ε} {ε} = wk-ε
ext-⊇-R {Γ ∙ x} {ε} = wk-wk (ext-⊇-R {Γ} {ε})
ext-⊇-R {ε} {Δ ∙ x} rewrite ⊕-left-id (Δ ∙ x) = wk-id
ext-⊇-R {Γ ∙ x₁} {Δ ∙ x} = wk-cong (ext-⊇-R {Γ ∙ x₁} {Δ})

ext-⊇-L : (Γ ⊕ Δ) ⊇ Γ
ext-⊇-L {Γ} {ε} = wk-id
ext-⊇-L {ε} {Δ ∙ x} = wk-wk ext-⊇-L
ext-⊇-L {Γ ∙ x₁} {Δ ∙ x} = wk-wk ext-⊇-L

i-assoc : (i : ((Γ ⊕ Ψ) ⊕ Δ) ∋ A) → (Γ ⊕ (Ψ ⊕ Δ)) ∋ A
i-assoc {Γ} {Ψ} {Δ} i rewrite ⊕-assoc {Γ} {Ψ} {Δ} = i

v-assoc : Val ((Γ ⊕ Ψ) ⊕ Δ) A → Val (Γ ⊕ (Ψ ⊕ Δ)) A
v-assoc {Γ} {Ψ} {Δ} v rewrite ⊕-assoc {Γ} {Ψ} {Δ} = v

ec : (w : Wk (Γ ⊕ Δ) Γ) → (γ : ⟦ Γ ⟧ˣ) → (δ : ⟦ Δ ⟧ˣ) → ⟦ Γ ⊕ Δ ⟧ˣ
ec {Γ} {ε} w γ δ = γ
ec {Γ} {Δ ∙ X} w γ (δ , x) = (ec ext-⊇-L γ δ , x)
-}

    {- A
    _,_∷pm⟨_⟩_ : (M : (Γ ⊕ Δ) ⊢ᵛ A `× B) -> (δ : ⟦ Δ ⟧ˣ) -> {M' : Γ ⊢ᵛ A `× B} -> {γ : ⟦ Γ ⟧ˣ} -> {N : (Γ ∙ A ∙ B) ⊢ᵛ C} → (M≡M' : ⟦ M ⟧ᵛ (ec ext-⊇-L γ δ) ≡ ⟦ M' ⟧ᵛ γ) -> valStack (pm M' N) γ
        ---------
        → valStack M (ec ext-⊇-L γ δ)
    -}


     {- A
     ~∙pair∷pm∷pm~> : {x : ((Γ ⊕ Δ) ⊕ Ψ) ⊢ᵛ X} -> {y : ((Γ ⊕ Δ) ⊕ Ψ) ⊢ᵛ Y} → {ψ : ⟦ Ψ ⟧ˣ} → {δ : ⟦ Δ ⟧ˣ} → {γ : ⟦ Γ ⟧ˣ}
                 -> {N : ((Γ ⊕ Δ) ∙ X ∙ Y) ⊢ᵛ X' `× Y'}
                 -> {M' : (Γ ⊕ Δ) ⊢ᵛ X `× Y} -> {≡M' : ⟦ pair x y ⟧ᵛ (ec (ext-⊇-L {Γ = Γ ⊕ Δ} {Δ = Ψ}) (ec ext-⊇-L γ δ) ψ) ≡ ⟦ M' ⟧ᵛ (ec ext-⊇-L γ δ)}
                 -> {M'' : Γ ⊢ᵛ X' `× Y'}
                 -> {N' : (Γ ∙ X' ∙ Y') ⊢ᵛ C}
                 -> {≡M'' : ⟦ (pm M' N) ⟧ᵛ (ec ext-⊇-L γ δ) ≡ ⟦ M'' ⟧ᵛ γ}
                 -> {tail : valStack (pm M'' N') γ}
                 ->  ∙ pair x y , ψ ∷pm⟨ ≡M' ⟩ pm M' N , δ ∷pm⟨ ≡M'' ⟩ tail -- ∙ pair x y , γ ∷pm⟨ ≡M' ⟩ pm M' N ,  γ' ∷pm⟨ W' ⨾ ≡M'' ⟩ tail
                      ~>
                     ∘ N , ((δ ,  ⟦ x ⟧ᵛ ((ec (ext-⊇-L {Γ = Γ ⊕ Δ} {Δ = Ψ}) (ec ext-⊇-L γ δ) ψ))) ,  ⟦ y ⟧ᵛ (ec (ext-⊇-L {Γ = Γ ⊕ Δ} {Δ = Ψ}) (ec ext-⊇-L γ δ) ψ)) ∷pm⟨ {!≡M''!} ⟩ tail -- ∘ N , ((γ' , ⟦ x ⟧ᵛ γ) , ⟦ y ⟧ᵛ γ) ∷pm⟨ {!≡M''!} ⟩ tail
                     -}

{- A
eq2 : {x : ((Γ ⊕ Δ) ⊕ Ψ) ⊢ᵛ X} -> {y : ((Γ ⊕ Δ) ⊕ Ψ) ⊢ᵛ Y} → {ψ : ⟦ Ψ ⟧ˣ} → {δ : ⟦ Δ ⟧ˣ} → {γ : ⟦ Γ ⟧ˣ}
                 -> {N : ((Γ ⊕ Δ) ∙ X ∙ Y) ⊢ᵛ X' `× Y'}
                 -> {M' : (Γ ⊕ Δ) ⊢ᵛ X `× Y} -> {≡M' : ⟦ pair x y ⟧ᵛ (ec (ext-⊇-L {Γ = Γ ⊕ Δ} {Δ = Ψ}) (ec ext-⊇-L γ δ) ψ) ≡ ⟦ M' ⟧ᵛ (ec ext-⊇-L γ δ)}
                 -> {M'' : Γ ⊢ᵛ X' `× Y'}
                 -> {N' : (Γ ∙ X' ∙ Y') ⊢ᵛ C}
                 -> {≡M'' : ⟦ (pm M' N) ⟧ᵛ (ec ext-⊇-L γ δ) ≡ ⟦ M'' ⟧ᵛ γ}
                 -> {tail : valStack (pm M'' N') γ}
                 → ⟦ N ⟧ᵛ ((ec ext-⊇-L γ δ , ⟦ x ⟧ᵛ (ec (ext-⊇-L {Γ = Γ ⊕ Δ} {Δ = Ψ}) (ec ext-⊇-L γ δ) ψ)) , ⟦ y ⟧ᵛ (ec (ext-⊇-L {Γ = Γ ⊕ Δ} {Δ = Ψ}) (ec ext-⊇-L γ δ) ψ)) ≡ ⟦ M'' ⟧ᵛ γ
eq2 {Γ = Γ} {Δ = Δ} {Ψ = Ψ} {x = x} {y = y} {ψ = ψ} {δ = δ} {γ = γ} {N = N} {M' = M'} {≡M' = ≡M'} {M'' = M''} {N' = N'} {≡M'' = ≡M''} {tail = tail} =
                    ⟦ N ⟧ᵛ ((ec ext-⊇-L γ δ , ⟦ x ⟧ᵛ (ec (ext-⊇-L {Γ = Γ ⊕ Δ} {Δ = Ψ}) (ec ext-⊇-L γ δ) ψ)) , ⟦ y ⟧ᵛ (ec (ext-⊇-L {Γ = Γ ⊕ Δ} {Δ = Ψ}) (ec ext-⊇-L γ δ) ψ))
                  ≡⟨ refl ⟩
                     (assocl ； ⟦ N ⟧ᵛ) ((ec ext-⊇-L γ δ) , ⟦ pair x y ⟧ᵛ (ec (ext-⊇-L {Γ = Γ ⊕ Δ} {Δ = Ψ}) (ec ext-⊇-L γ δ) ψ))
                  ≡⟨ cong (λ p → (assocl ； ⟦ N ⟧ᵛ) ((ec ext-⊇-L γ δ) , p) ) ≡M' ⟩
                    (assocl ； ⟦ N ⟧ᵛ) ((ec ext-⊇-L γ δ) , ⟦ M' ⟧ᵛ (ec ext-⊇-L γ δ))
                  ≡⟨ refl ⟩
                    (< idf , ⟦ M' ⟧ᵛ > ； assocl ； ⟦ N ⟧ᵛ) (ec ext-⊇-L γ δ)
                  ≡⟨ refl ⟩
                    ⟦ (pm M' N) ⟧ᵛ (ec ext-⊇-L γ δ)
                  ≡⟨ ≡M'' ⟩
                    ⟦ M'' ⟧ᵛ γ ∎
-}
