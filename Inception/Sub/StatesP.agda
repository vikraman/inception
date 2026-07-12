{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.StatesP where

open import Agda.Primitive using (Level)

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Function.Base using (const; _∘_; _$_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; cong-app; icong; dcong₂; sym; trans; subst; subst₂)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.Renaming

open import Data.Unit
open import Data.Nat
open import Data.List using (List; _∷_; []; _++_)

open import Inception.Sub.Equality
open import Inception.Sub.EnvironmentsP

-- data types for lookup machine

data LookupState : Ty → Ty → Set where

    ⟨_∥_⟩   :  (i : Γ ∋ X) → Env Γ Z → LookupState X Z

lCtx : (S : LookupState X Z) → Ctx
lCtx (⟨_∥_⟩ {Γ = Γ} i E)= Γ

lTCtx : (S : LookupState X Z) → Ctx
lTCtx (⟨_∥_⟩ i ∗) = ε
lTCtx (⟨_∥_⟩ i (_﹐_ {Γ = Γ} E M)) = Γ
lTCtx (⟨_∥_⟩ i (_﹐﹝_╎_﹞ {Γ = Γ} E M k)) = Γ

lEnv : (S : LookupState X Z) → Env (lCtx S) Z
lEnv ⟨ i ∥ E ⟩ = E

lTEnv : (S : LookupState X Z) → Env (lTCtx S) Z
lTEnv ⟨ i ∥ E ﹐ M ⟩ = E
lTEnv ⟨ i ∥ E ﹐﹝ M ╎ cs ﹞ ⟩ = E

----------------
-- data types for value machine

infixr 25 _⊲_∷_
infix  20 ∘_
infix  20 ∙_

data IsEmpty : Set where
    non-empty : IsEmpty
    empty : IsEmpty

variable
    b b' : IsEmpty

data BottomTypeEqualsNextType : IsEmpty → Ty → Ty → Set where

    🗆 : BottomTypeEqualsNextType empty X X

    🗇 : BottomTypeEqualsNextType non-empty X Y

data ValStack : IsEmpty → Ty → Ty → Set where

    □ : ValStack empty T◾ Z

    _⊲_∷_ : PartialTerm Γ X → (γ : Env Γ Z) → (tail : ValStack b T◾ Z) → {↥ : BottomTypeEqualsNextType b X T◾} → ValStack non-empty T◾ Z


data ValState : Ty → Ty → Set where

    ∘_ : ValStack non-empty T◾ Z → ValState T◾ Z

    ∙_ : ValStack non-empty T◾ Z → ValState T◾ Z

_⧺_ : ValStack b T◾ Z → ValStack non-empty T◾' Z → ValStack non-empty T◾' Z
□ ⧺ lower = lower
(M ⊲ γ ∷ upper) ⧺ lower = (M ⊲ γ ∷ (upper ⧺ lower)) {↥ = 🗇}

_⧻_ : (upper : ValState T◾ Z) → ValStack non-empty T◾' Z → ValState T◾' Z
(∘ upper) ⧻ lower = ∘ (upper ⧺ lower)
(∙ upper) ⧻ lower = ∙ (upper ⧺ lower)


topStackCtx : (S : ValStack non-empty T◾ Z) → Ctx
topStackCtx (_⊲_∷_ {Γ = Γ} _ _ _) = Γ

topCtx : ValState T◾ Z → Ctx
topCtx (∘ S) = topStackCtx S
topCtx (∙ S) = topStackCtx S

topStackEnv : (S : ValStack non-empty T◾ Z) → Env (topStackCtx S) Z
topStackEnv (_⊲_∷_ _ γ _) = γ

topEnv : (S : ValState T◾ Z) → Env (topCtx S) Z
topEnv (∘ S) = topStackEnv S
topEnv (∙ S) = topStackEnv S

botStackCtx : ValStack non-empty T◾ Z → Ctx
botStackCtx ((_⊲_∷_) {Γ = Γ} _ _ □) = Γ
botStackCtx ((x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})) {↥ = ↥}) = botStackCtx ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})

botCtx : ValState T◾ Z → Ctx
botCtx (∘ S) = botStackCtx S
botCtx (∙ S) = botStackCtx S

botStackEnv : (S : ValStack non-empty T◾ Z) → Env (botStackCtx S) Z
botStackEnv ((_⊲_∷_) {Γ = Γ} _ γ □) = γ
botStackEnv ((x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})) {↥ = ↥}) = botStackEnv ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})

botEnv : (S : ValState T◾ Z) → Env (botCtx S) Z
botEnv (∘ S) = botStackEnv S
botEnv (∙ S) = botStackEnv S

botStackTerm : (S : ValStack non-empty T◾ Z) → PartialTerm (botStackCtx S) (T◾)
botStackTerm ((_⊲_∷_) {Γ = Γ} M γ □ {↥ = 🗆}) = M
botStackTerm ((x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})) {↥ = ↥}) = botStackTerm ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})

data CompState : Ty → Set where

      ∘⟨_⊰_╎_⟩ : (W : Γ ⊢ᶜ X) → (γ : Env Γ Z) → (cs : CompStack Δ X Z) → {π : Wk Γ Δ} → {ϖ : EnvEq π γ (topCsEnv cs)} → CompState Z

      ∙⟨_⊰_╎_⟩ : (W : C̲o̲m̲p Γ X) → (γ : Env Γ Z) → (cs : CompStack Δ X Z) → {π : Wk Γ Δ} → {ϖ : EnvEq π γ (topCsEnv cs)} → CompState Z

topCompCtx : CompState Z → Ctx
topCompCtx (∘⟨_⊰_╎_⟩ {Γ = Γ} _ _ _) = Γ
topCompCtx (∙⟨_⊰_╎_⟩ {Γ = Γ} _ _ _) = Γ

topCompEnv : (Q : CompState Z) → Env (topCompCtx Q) Z
topCompEnv (∘⟨_⊰_╎_⟩ _ γ _) = γ
topCompEnv (∙⟨_⊰_╎_⟩ _ γ _) = γ

cstate-eq : {W W' : C̲o̲m̲p Γ X} {γ γ' : Env Γ Z} {cs : CompStack Δ X Z} {π π' : Wk Γ Δ} {ϖ : EnvEq π γ (topCsEnv cs)} {ϖ' : EnvEq π' γ' (topCsEnv cs)} → (W , (γ , π)) ≡ (W' , (γ' , π')) → ((∙⟨ W ⊰ γ ╎ cs ⟩) {π = π} {ϖ = ϖ}) ≡ ((∙⟨ W' ⊰ γ' ╎ cs ⟩) {π = π'} {ϖ = ϖ'})
cstate-eq {W = W} {W' = W'} {γ = γ} {cs = cs} {π = π} {ϖ = ϖ} eq = dcong₂ (λ x y → ((∙⟨ (proj₁ x) ⊰ proj₁ (proj₂ x) ╎ cs ⟩) {π = proj₂ (proj₂ x)} {ϖ = y})) eq (env-eq-uip (subst (λ z → EnvEq (proj₂ (proj₂ z)) (proj₁ (proj₂ z)) (topCsEnv cs)) eq ϖ) _)

cstate-eq' : {W W' : Γ ⊢ᶜ X} {γ γ' : Env Γ Z} {cs : CompStack Δ X Z} {π π' : Wk Γ Δ} {ϖ : EnvEq π γ (topCsEnv cs)} {ϖ' : EnvEq π' γ' (topCsEnv cs)} → (W , (γ , π)) ≡ (W' , (γ' , π')) → ((∘⟨ W ⊰ γ ╎ cs ⟩) {π = π} {ϖ = ϖ}) ≡ ((∘⟨ W' ⊰ γ' ╎ cs ⟩) {π = π'} {ϖ = ϖ'})
cstate-eq' {W = W} {W' = W'} {γ = γ} {cs = cs} {π = π} {ϖ = ϖ} eq = dcong₂ (λ x y → ((∘⟨ (proj₁ x) ⊰ proj₁ (proj₂ x) ╎ cs ⟩) {π = proj₂ (proj₂ x)} {ϖ = y})) eq (env-eq-uip (subst (λ z → EnvEq (proj₂ (proj₂ z)) (proj₁ (proj₂ z)) (topCsEnv cs)) eq ϖ) _)
