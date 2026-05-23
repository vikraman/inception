{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Renaming where

open import Inception.Sub.Syntax

{-
open import Level using (Level; zero)
open import Function using (_∘_)
open import Data.Unit using (⊤; tt)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional
  using
    (_↭_; ↭-refl; ↭-sym; ↭-trans)

open import Relation.Binary using (Rel; Setoid)
open import Relation.Binary.Structures using (IsEquivalence)

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)


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

Ren : Ctx → Ctx → Set
Ren Γ Δ = ∀ {A} → Δ ∋ A → Γ ∋ A

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

wk-ren : Wk Γ Δ → Ren Γ Δ
wk-ren π {A} i = wk-mem π i

wk-val' : Wk Γ Δ → Δ ⊢ᵛ A → Γ ⊢ᵛ A
wk-val' π = ren-val (wk-ren π)

wk-comp' : Wk Γ Δ → Δ ⊢ᶜ A → Γ ⊢ᶜ A
wk-comp' π = ren-comp (wk-ren π)
