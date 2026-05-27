{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Renaming where

open import Inception.Sub.Syntax

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)

open import Level using (Level; zero)
open import Function using (_∘_)
open import Data.Unit using (⊤; tt)

open import Data.List using (List; []; _∷_)

open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions using (Reflexive; Transitive)

--
import Data.List.Relation.Binary.Permutation.Propositional
--open import Data.List.Relation.Binary.Permutation.Propositional
--  using
--    (_↭_; ↭-refl; ↭-sym; ↭-trans)

open import Relation.Binary using (Rel; Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)

{-
toList : Ctx → List Ty
toList ε       = []
toList (Γ ∙ A) = A ∷ toList Γ

fromList : List Ty → Ctx
fromList []       = ε
fromList (A ∷ xs) = fromList xs ∙ A

to-from : ∀ xs → toList (fromList xs) ≡ xs
to-from [] = refl
to-from (A ∷ xs)
  rewrite to-from xs
  = refl

from-to : ∀ Γ → fromList (toList Γ) ≡ Γ
from-to ε = refl
from-to (Γ ∙ A)
  rewrite from-to Γ
  = refl

infix 4 _≈_

_≈_ : Rel Ctx zero
Γ ≈ Δ = toList Γ ↭ toList Δ

≈-isEquivalence : IsEquivalence _≈_
≈-isEquivalence =
  record
    { refl  = ↭-refl
    ; sym   = ↭-sym
    ; trans = ↭-trans
    }

Ctx-setoid : Setoid zero zero
Ctx-setoid =
  record
    { Carrier       = Ctx
    ; _≈_           = _≈_
    ; isEquivalence = ≈-isEquivalence
    }

-}

-- copied (and adapted) from Data.List...

infix 3 _↭_

data _↭_ : Rel Ctx zero where
  refl  : Γ ↭ Γ
  prep  : ∀ X → Γ ↭ Γ' → Γ ∙ X ↭ Γ' ∙ X
  swap  : ∀ X Y → Γ ↭ Γ' → Γ ∙ Y ∙ X ↭ Γ' ∙ X ∙ Y
  trans : Γ ↭ Γ' → Γ' ↭ Γ'' → Γ ↭ Γ''

-- Constructor aliases

↭-refl : Reflexive _↭_
↭-refl = refl

↭-prep  : ∀ X → Γ ↭ Γ' → Γ ∙ X ↭ Γ' ∙ X
↭-prep = prep

↭-swap  : ∀ X Y → Γ ↭ Γ' → Γ ∙ Y ∙ X ↭ Γ' ∙ X ∙ Y
↭-swap = swap

--

↭-trans : Transitive _↭_
↭-trans refl ρ₂ = ρ₂
↭-trans (prep X ρ₁) refl = prep X ρ₁
↭-trans (swap X Y ρ₁) refl = swap X Y ρ₁
↭-trans (trans ρ₁ ρ₂) refl = trans ρ₁ ρ₂
↭-trans (prep X ρ₁) (prep X₁ ρ₂) = prep X (trans ρ₁ ρ₂)
↭-trans (prep X ρ₁) (swap X₁ Y ρ₂) = trans (prep X ρ₁) (swap X Y ρ₂)
↭-trans (prep X ρ₁) (trans ρ₂ ρ₃) = trans (trans (prep X ρ₁) ρ₂) ρ₃
↭-trans (swap X Y ρ₁) (prep X₁ ρ₂) = trans (swap X Y ρ₁) (prep Y ρ₂)
↭-trans (swap X Y ρ₁) (swap X₁ Y₁ ρ₂) = prep X (prep Y (trans ρ₁ ρ₂))
↭-trans (swap X Y ρ₁) (trans ρ₂ ρ₃) = trans (swap X Y ρ₁) (trans ρ₂ ρ₃)
↭-trans (trans ρ₁ ρ₂) (prep X ρ₃) = trans (trans ρ₁ ρ₂) (prep X ρ₃)
↭-trans (trans ρ₁ ρ₂) (swap X Y ρ₃) = trans ρ₁ (trans ρ₂ (swap X Y ρ₃))
↭-trans (trans ρ₁ ρ₂) (trans ρ₃ ρ₄) = trans ρ₁ (trans (trans ρ₂ ρ₃) ρ₄)

{- without exact splitting:
↭-trans : Transitive _↭_
↭-trans refl ρ₂ = ρ₂
↭-trans ρ₁ refl = ρ₁
↭-trans ρ₁ ρ₂   = trans ρ₁ ρ₂
-}

↭-sym : Γ ↭ Γ' → Γ' ↭ Γ
↭-sym refl                = refl
↭-sym (prep X Γ↭Γ')      = prep X (↭-sym Γ↭Γ')
↭-sym (swap X Y Γ↭Γ')    = swap Y X (↭-sym Γ↭Γ')
↭-sym (trans Γ↭Γ' Γ'↭Γ'') = trans (↭-sym Γ'↭Γ'') (↭-sym Γ↭Γ')

-------------------------------------------------------------------------------------------
-- PERMUTATIONS
-------------------------------------------------------------------------------------------

perm-mem : Γ ↭ Γ' → Γ ∋ X → Γ' ∋ X
perm-mem refl Cx.h = h
perm-mem refl (Cx.t i) = t i
perm-mem (prep X Γ↭Γ') Cx.h = h
perm-mem (prep X Γ↭Γ') (Cx.t i) = t (perm-mem Γ↭Γ' i)
perm-mem (swap X Y Γ↭Γ') Cx.h = t h
perm-mem (swap X Y Γ↭Γ') (Cx.t Cx.h) = h
perm-mem (swap X Y Γ↭Γ') (Cx.t (Cx.t i)) = t (t (perm-mem Γ↭Γ' i))
perm-mem (trans Γ↭Γ' Γ↭Γ'') Cx.h = perm-mem Γ↭Γ'' (perm-mem Γ↭Γ' h)
perm-mem (trans Γ↭Γ' Γ↭Γ'') (Cx.t i) = perm-mem Γ↭Γ'' (perm-mem Γ↭Γ' (t i))

-------------------------------------------------------------------------------------------
-- ARBITRARY RENAMINGS
-------------------------------------------------------------------------------------------

Ren : Ctx → Ctx → Set
Ren Γ Δ = ∀ {A} → Δ ∋ A → Γ ∋ A

Injective : {Γ Δ : Ctx} → (ρ : Ren Γ Δ) → Set
Injective {Γ = Γ} {Δ = Δ} ρ = (∀ {X : Ty} → (i j : Δ ∋ X) → ρ i ≡ ρ j → i ≡ j)

ren-id : Ren Γ Γ
ren-id i = i

_∘r_ : Ren Γ Δ → Ren Δ Ψ → Ren Γ Ψ
(ρ ∘r σ) i = ρ (σ i)

ext : Ren Γ Δ → Ren (Γ ∙ A) (Δ ∙ A)
ext ρ h = h
ext ρ (t i) = t (ρ i)

mutual

  ren-val : Ren Γ Δ → Δ ⊢ᵛ A → Γ ⊢ᵛ A
  ren-val ρ (var i) =
    var (ρ i)

  ren-val ρ (lam M) =
    lam (ren-comp (ext ρ) M)

  ren-val ρ (pair V W) =
    pair (ren-val ρ V) (ren-val ρ W)

  ren-val ρ (pm V W) =
    pm (ren-val ρ V)
       (ren-val (ext (ext ρ)) W)

  ren-val ρ unit =
    unit


  ren-comp : Ren Γ Δ → Δ ⊢ᶜ A → Γ ⊢ᶜ A
  ren-comp ρ (return V) =
    return (ren-val ρ V)

  ren-comp ρ (pm V M) =
    pm (ren-val ρ V)
       (ren-comp (ext (ext ρ)) M)

  ren-comp ρ (push M N) =
    push (ren-comp ρ M)
         (ren-comp (ext ρ) N)

  ren-comp ρ (app V W) =
    app (ren-val ρ V)
        (ren-val ρ W)

  ren-comp ρ (var V) =
    var (ren-val ρ V)

  ren-comp ρ (sub M N) =
    sub (ren-comp (ext ρ) M)
        (ren-comp ρ N)

ren-v̲a̲l̲ : Ren Γ Δ → V̲a̲l̲ Δ A → V̲a̲l̲ Γ A
ren-v̲a̲l̲ ρ u̲n̲i̲t̲ = u̲n̲i̲t̲
ren-v̲a̲l̲ ρ (v̲a̲r̲ i) = v̲a̲r̲ (ρ i)
ren-v̲a̲l̲ ρ (l̲a̲m̲ W) = l̲a̲m̲ (ren-comp (ext ρ) W)
ren-v̲a̲l̲ ρ (pa̲i̲r̲ M₁ M₂) = pa̲i̲r̲ (ren-v̲a̲l̲ ρ M₁) (ren-v̲a̲l̲ ρ M₂)

ren-c̲o̲m̲p : Ren Γ Δ → C̲o̲m̲p Δ A → C̲o̲m̲p Γ A
ren-c̲o̲m̲p ρ (r̲e̲t̲u̲r̲n̲ M) = r̲e̲t̲u̲r̲n̲ (ren-v̲a̲l̲ ρ M)
ren-c̲o̲m̲p ρ (a̲pp M N) = a̲pp (ren-val ρ M) (ren-v̲a̲l̲ ρ N)

wk-ren : Wk Γ Δ → Ren Γ Δ
wk-ren π {A} i = wk-mem π i

wk-val' : Wk Γ Δ → Δ ⊢ᵛ A → Γ ⊢ᵛ A
wk-val' π = ren-val (wk-ren π)

wk-comp' : Wk Γ Δ → Δ ⊢ᶜ A → Γ ⊢ᶜ A
wk-comp' π = ren-comp (wk-ren π)
