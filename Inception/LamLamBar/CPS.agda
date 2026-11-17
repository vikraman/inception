module Inception.LamLamBar.CPS (R : Set) where

open import Inception.LamLamBar.Syntax

open import Data.Product as P
open import Data.Sum as S
open import Data.Unit
open import Function as F hiding (_∋_)
open import Inception.Prelude
open import Relation.Binary.PropositionalEquality

open import Inception.Cont.Base
open import Inception.Monad.Base using (Monad)
open import Level using (0ℓ)

K : Set → Set
K = K[ R ]

open Monad (K[_]-Monad {x = 0ℓ} R) using (η; _*)

⟦_⟧ : Ty → Set
⟦ `𝟙 ⟧ = ⊤
⟦ X ̃ ⟧ = R ^ ⟦ X ⟧
⟦ X `× Y ⟧ = ⟦ X ⟧ × ⟦ Y ⟧
⟦ X `⇒ Y ⟧ = ⟦ X ⟧ → K ⟦ Y ⟧
⟦ X `+ Y ⟧ = ⟦ X ⟧ ⊎ ⟦ Y ⟧

open Sem ⟦_⟧

mutual
  ⟦_⟧ᵛ : Γ ⊢ᵛ X → ⟦ Γ ⟧ˣ → ⟦ X ⟧
  ⟦ var i ⟧ᵛ = ⟦ i ⟧ᵐ
  ⟦ lam M ⟧ᵛ = curry ⟦ M ⟧ᶜ
  ⟦ pair V W ⟧ᵛ = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ >
  ⟦ unit ⟧ᵛ = const tt
  ⟦ inl V ⟧ᵛ = ⟦ V ⟧ᵛ ； inj₁
  ⟦ inr V ⟧ᵛ = ⟦ V ⟧ᵛ ； inj₂
  ⟦ case V W₁ W₂ ⟧ᵛ = λ γ → [ curry ⟦ W₁ ⟧ᵛ γ , curry ⟦ W₂ ⟧ᵛ γ ]′ (⟦ V ⟧ᵛ γ)

  ⟦_⟧ᶜ : Γ ⊢ᶜ X → ⟦ Γ ⟧ˣ → K ⟦ X ⟧
  ⟦ return V ⟧ᶜ = ⟦ V ⟧ᵛ ； η
  ⟦ pm V M ⟧ᶜ = < idf , ⟦ V ⟧ᵛ > ； assocl ； ⟦ M ⟧ᶜ
  ⟦ push M N ⟧ᶜ = < idf , ⟦ M ⟧ᶜ > ； τ ； ⟦ N ⟧ᶜ *
  ⟦ app V W ⟧ᶜ = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ > ； ev
  ⟦ colam M ⟧ᶜ = cocurry ⟦ M ⟧ᶜ
  ⟦ coapp M V ⟧ᶜ = < ⟦ M ⟧ᶜ , ⟦ V ⟧ᵛ > ； councurry idf

⟦_⟧ˢ : Γ ⊢ Δ → ⟦ Γ ⟧ˣ → ⟦ Δ ⟧ˣ
⟦ sub-ε ⟧ˢ = const tt
⟦ sub-ex θ V ⟧ˢ = < ⟦ θ ⟧ˢ , ⟦ V ⟧ᵛ >

[,]-η : {A B C : Set} (f : A ⊎ B → C) (s : A ⊎ B) → f s ≡ [ f ∘ inj₁ , f ∘ inj₂ ]′ s
[,]-η f (inj₁ a) = refl
[,]-η f (inj₂ b) = refl


--------------------------------------------------------------------------
-- coherences

mutual
  wk-val-coh : (π : Γ ⊇ Δ) (V : Δ ⊢ᵛ X) → ⟦ wk-val π V ⟧ᵛ ≡ (⟦ π ⟧ʷ ； ⟦ V ⟧ᵛ)
  wk-val-coh π (var i) rewrite wk-mem-coh π i = refl
  wk-val-coh π (lam M) rewrite wk-comp-coh (wk-cong π) M = refl
  wk-val-coh π (pair V W) rewrite wk-val-coh π V | wk-val-coh π W = refl
  wk-val-coh π unit = refl
  wk-val-coh π (inl V) rewrite wk-val-coh π V = refl
  wk-val-coh π (inr V) rewrite wk-val-coh π V = refl
  wk-val-coh π (case V W₁ W₂) rewrite wk-val-coh π V | wk-val-coh (wk-cong π) W₁ | wk-val-coh (wk-cong π) W₂ = refl

  wk-comp-coh : (π : Γ ⊇ Δ) (M : Δ ⊢ᶜ X) → ⟦ wk-comp π M ⟧ᶜ ≡ (⟦ π ⟧ʷ ； ⟦ M ⟧ᶜ)
  wk-comp-coh π (return V) rewrite wk-val-coh π V = refl
  wk-comp-coh π (pm V M) rewrite wk-val-coh π V | wk-comp-coh (wk-cong (wk-cong π)) M = refl
  wk-comp-coh π (push M N) rewrite wk-comp-coh π M | wk-comp-coh (wk-cong π) N = refl
  wk-comp-coh π (app V W) rewrite wk-val-coh π V | wk-val-coh π W = refl
  wk-comp-coh π (colam M) rewrite wk-comp-coh (wk-cong π) M = refl
  wk-comp-coh π (coapp M V) rewrite wk-comp-coh π M | wk-val-coh π V = refl

{-# REWRITE wk-val-coh #-}
{-# REWRITE wk-comp-coh #-}

sub-mem-coh : (θ : Γ ⊢ Δ) (i : Δ ∋ X) → ⟦ sub-mem θ i ⟧ᵛ ≡ (⟦ θ ⟧ˢ ； ⟦ i ⟧ᵐ)
sub-mem-coh (sub-ex θ V) here = refl
sub-mem-coh (sub-ex θ V) (there i) rewrite sub-mem-coh θ i = refl
{-# REWRITE sub-mem-coh #-}

sub-wk-coh : (π : Γ ⊇ Δ) (θ : Δ ⊢ Ψ) → ⟦ sub-wk π θ ⟧ˢ ≡ (⟦ π ⟧ʷ ； ⟦ θ ⟧ˢ)
sub-wk-coh π sub-ε = refl
sub-wk-coh π (sub-ex θ V) rewrite sub-wk-coh π θ | wk-val-coh π V = refl
{-# REWRITE sub-wk-coh #-}

sub-id-coh : ⟦ sub-id {Γ} ⟧ˢ ≡ id
sub-id-coh {ε} = refl
sub-id-coh {Γ ∙ X} = funext λ γ → cong₂ _,_ (happly sub-id-coh (proj₁ γ)) refl
{-# REWRITE sub-id-coh #-}

mutual
  sub-val-coh : (θ : Γ ⊢ Δ) (V : Δ ⊢ᵛ X) → ⟦ sub-val θ V ⟧ᵛ ≡ (⟦ θ ⟧ˢ ； ⟦ V ⟧ᵛ)
  sub-val-coh θ (var i) = refl
  sub-val-coh θ (lam M) rewrite sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M = refl
  sub-val-coh θ (pair V W) rewrite sub-val-coh θ V | sub-val-coh θ W = refl
  sub-val-coh θ unit = refl
  sub-val-coh θ (inl V) rewrite sub-val-coh θ V = refl
  sub-val-coh θ (inr V) rewrite sub-val-coh θ V = refl
  sub-val-coh θ (case V W₁ W₂) rewrite sub-val-coh θ V | sub-val-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) W₁ | sub-val-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) W₂ = refl

  sub-comp-coh : (θ : Γ ⊢ Δ) (M : Δ ⊢ᶜ X) → ⟦ sub-comp θ M ⟧ᶜ ≡ (⟦ θ ⟧ˢ ； ⟦ M ⟧ᶜ)
  sub-comp-coh θ (return V) rewrite sub-val-coh θ V = refl
  sub-comp-coh θ (pm V M) rewrite sub-val-coh θ V | sub-comp-coh (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M = refl
  sub-comp-coh θ (push M N) rewrite sub-comp-coh θ M | sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N = refl
  sub-comp-coh θ (app V W) rewrite sub-val-coh θ V | sub-val-coh θ W = refl
  sub-comp-coh θ (colam M) rewrite sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M = refl
  sub-comp-coh θ (coapp M V) rewrite sub-comp-coh θ M | sub-val-coh θ V = refl

{-# REWRITE sub-val-coh #-}
{-# REWRITE sub-comp-coh #-}

--------------------------------------------------------------------------
-- soundness

mutual
  eqVal : Γ ⊢ᵛ V ≈ W ∶ X → ⟦ V ⟧ᵛ ≡ ⟦ W ⟧ᵛ
  eqVal ≈-refl = refl
  eqVal (≈-sym p) = sym (eqVal p)
  eqVal (≈-trans p q) = trans (eqVal p) (eqVal q)
  eqVal (lam-cong p) = cong curry (eqComp p)
  eqVal (pair-cong p q) = cong₂ <_,_> (eqVal p) (eqVal q)
  eqVal (inl-cong p) rewrite eqVal p = refl
  eqVal (inr-cong p) rewrite eqVal p = refl
  eqVal (case-cong p q r) rewrite eqVal p | eqVal q | eqVal r = refl
  eqVal (unit-eta _) = refl
  eqVal (case-inl-beta V W₁ W₂) = refl
  eqVal (case-inr-beta V W₁ W₂) = refl
  eqVal (case-eta V W) = funext λ γ → [,]-η (curry ⟦ W ⟧ᵛ γ) (⟦ V ⟧ᵛ γ)
  eqVal (lam-eta _) = refl

  eqComp : Γ ⊢ᶜ M ≈ N ∶ X → ⟦ M ⟧ᶜ ≡ ⟦ N ⟧ᶜ
  eqComp ≈-refl = refl
  eqComp (≈-sym p) = sym (eqComp p)
  eqComp (≈-trans p q) = trans (eqComp p) (eqComp q)
  eqComp (return-cong p) rewrite eqVal p = refl
  eqComp (pm-cong p q) rewrite eqVal p | eqComp q = refl
  eqComp (push-cong p q) rewrite eqComp p | eqComp q = refl
  eqComp (app-cong p q) rewrite eqVal p | eqVal q = refl
  eqComp (colam-cong p) rewrite eqComp p = refl
  eqComp (coapp-cong p q) rewrite eqComp p | eqVal q = refl
  eqComp (pm-beta V W M) = refl
  eqComp (pm-eta V M) = refl
  eqComp (return-beta V M) = refl
  eqComp (return-eta _) = refl
  eqComp (push-eta M N P) = refl
  eqComp (lam-beta M V) = refl
  eqComp (colam-beta M V) = refl
  eqComp (colam-eta M) = funext λ γ → funext λ k → cong (⟦ M ⟧ᶜ γ) (funext ([,]-η k))
  eqComp (colam-const M) = refl
  eqComp (colam-inr-pass M N) = refl
  eqComp (colam-inl-jump M N) = refl
  eqComp (case-colam-beta V M N) = refl
