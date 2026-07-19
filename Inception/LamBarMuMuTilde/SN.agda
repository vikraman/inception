module Inception.LamBarMuMuTilde.SN where

open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym)
open Eq.≡-Reasoning

open import Inception.LamBarMuMuTilde.Syntax

--------------------------------------------------------------------------
-- step relation on commands

infix 5 _↦_

data _↦_ {Γ Δ : Env} : Γ ⊢ Δ → Γ ⊢ Δ → Set where

  μ-step   : {A : Ty} {M : Γ ⊢ (Δ ∙ A)} {C : Γ ∣ A ⊢ᵉ Δ}
           → cut A (μ M) C ↦ letc C M

  μ̃-step   : {A : Ty} {V : Γ ⊢ᵛ A ∣ Δ} {M : (Γ ∙ A) ⊢ Δ}
           → cut A (ret V) (μ̃ M) ↦ letvc V M

  app-step : {A B : Ty} {M : (Γ ∙ A) ⊢ᵗ B ∣ Δ} {V : Γ ⊢ᵛ A ∣ Δ} {C : Γ ∣ B ⊢ᵉ Δ}
           → cut (A `⇒ B) (ret (lam M)) (app V C) ↦ cut B (letv V M) C

  fst-step : {A B : Ty} {V : Γ ⊢ᵛ A ∣ Δ} {W : Γ ⊢ᵛ B ∣ Δ} {C : Γ ∣ A ⊢ᵉ Δ}
           → cut (A `× B) (ret (pair V W)) (fst C) ↦ cut A (ret V) C

  snd-step : {A B : Ty} {V : Γ ⊢ᵛ A ∣ Δ} {W : Γ ⊢ᵛ B ∣ Δ} {C : Γ ∣ B ⊢ᵉ Δ}
           → cut (A `× B) (ret (pair V W)) (snd C) ↦ cut B (ret W) C

  inl-step : {A B : Ty} {V : Γ ⊢ᵛ A ∣ Δ} {C1 : Γ ∣ A ⊢ᵉ Δ} {C2 : Γ ∣ B ⊢ᵉ Δ}
           → cut (A `+ B) (ret (inl V)) (case C1 C2) ↦ cut A (ret V) C1

  inr-step : {A B : Ty} {W : Γ ⊢ᵛ B ∣ Δ} {C1 : Γ ∣ A ⊢ᵉ Δ} {C2 : Γ ∣ B ⊢ᵉ Δ}
           → cut (A `+ B) (ret (inr W)) (case C1 C2) ↦ cut B (ret W) C2

--------------------------------------------------------------------------
-- accessibility

data SN {Γ Δ} (M : Γ ⊢ Δ) : Set where
  sn : (∀ {M1} → M ↦ M1 → SN M1) → SN M

--------------------------------------------------------------------------
-- reducibility candidates

Redᵛ  : (A : Ty) {Γ Δ : Env} → Γ ⊢ᵛ A ∣ Δ → Set
CoRedᵉ : (A : Ty) {Γ Δ : Env} → Γ ∣ A ⊢ᵉ Δ → Set

Redᵛ `⊥        V              = ⊤
Redᵛ `Unit     V              = ⊤
Redᵛ (A `× B)  (var i)        = ⊤
Redᵛ (A `× B)  (pair V W)     = Redᵛ A V × Redᵛ B W
Redᵛ (A `+ B)  (var i)        = ⊤
Redᵛ (A `+ B)  (inl V)        = Redᵛ A V
Redᵛ (A `+ B)  (inr W)        = Redᵛ B W
Redᵛ (A `⇒ B)  (var i)        = ⊤
Redᵛ (A `⇒ B) {Γ} {Δ} (lam M) =
  ∀ {Γ' Δ'} (π : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) {W : Γ' ⊢ᵛ A ∣ Δ'} {C : Γ' ∣ B ⊢ᵉ Δ'}
  → Redᵛ A W → CoRedᵉ B C → SN (cut B (letv W (wk-tm (wk-cong π) σ M)) C)

CoRedᵉ A         (covar i)    = ⊤
CoRedᵉ A {Γ} {Δ} (μ̃ M)       =
  ∀ {Γ' Δ'} (π : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) {V : Γ' ⊢ᵛ A ∣ Δ'}
  → Redᵛ A V → SN (sub-cmd (sub-ex sub-id V) cosub-id (wk-cmd (wk-cong π) σ M))
CoRedᵉ `⊥        tp           = ⊤
CoRedᵉ (A `× B)  (fst C)      = CoRedᵉ A C
CoRedᵉ (A `× B)  (snd C)      = CoRedᵉ B C
CoRedᵉ (A `+ B)  (case C1 C2) = CoRedᵉ A C1 × CoRedᵉ B C2
CoRedᵉ (A `⇒ B)  (app V C)    = Redᵛ A V × CoRedᵉ B C

--------------------------------------------------------------------------
-- weakening preserves reducibility

Red-wk : (A : Ty) {Γ Δ Γ' Δ' : Env} (π : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) {V : Γ ⊢ᵛ A ∣ Δ}
       → Redᵛ A V → Redᵛ A (wk-val π σ V)
Red-wk `⊥        π σ r = tt
Red-wk `Unit     π σ r = tt
Red-wk (A `× B) π σ {V = var i}    r        = tt
Red-wk (A `× B) π σ {V = pair V W} (rv , rw) = Red-wk A π σ rv , Red-wk B π σ rw
Red-wk (A `+ B) π σ {V = var i}  r  = tt
Red-wk (A `+ B) π σ {V = inl V}  rv = Red-wk A π σ rv
Red-wk (A `+ B) π σ {V = inr W}  rw = Red-wk B π σ rw
Red-wk (A `⇒ B) π σ {V = var i}  r = tt
Red-wk (A `⇒ B) {Γ} {Δ} π σ {V = lam M} f =
  λ π' σ' {W} {C} rw rc →
    Eq.subst (λ x → SN (cut B (letv W x) C)) (sym (wk-tm-trans M (wk-cong π') (wk-cong π) σ' σ)) (f (wk-trans π' π) (wk-trans σ' σ) rw rc)

CoRed-wk : (A : Ty) {Γ Δ Γ' Δ' : Env} (π : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) {C : Γ ∣ A ⊢ᵉ Δ}
         → CoRedᵉ A C → CoRedᵉ A (wk-ctx π σ C)
CoRed-wk A             π σ {C = covar i}   r  = tt
CoRed-wk `⊥            π σ {C = tp}        r  = tt
CoRed-wk (A `× B)      π σ {C = fst C}     r  = CoRed-wk A π σ {C = C} r
CoRed-wk (A `× B)      π σ {C = snd C}     r  = CoRed-wk B π σ {C = C} r
CoRed-wk (A `+ B)      π σ {C = case C1 C2} (r1 , r2) = CoRed-wk A π σ {C = C1} r1 , CoRed-wk B π σ {C = C2} r2
CoRed-wk (A `⇒ B)      π σ {C = app V C}   (rv , rc)  = Red-wk A π σ rv , CoRed-wk B π σ {C = C} rc
CoRed-wk A {Γ} {Δ} π σ {C = μ̃ M} f =
  λ π' σ' {V} rv →
    Eq.subst (λ x → SN (sub-cmd (sub-ex sub-id V) cosub-id x)) (sym (wk-cmd-trans M (wk-cong π') (wk-cong π) σ' σ)) (f (wk-trans π' π) (wk-trans σ' σ) rv)
