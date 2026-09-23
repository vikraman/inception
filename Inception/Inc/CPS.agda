module Inception.Inc.CPS (ℙ R : Set) where

open import Inception.Inc.Syntax

open import Data.Unit
open import Data.Product as P
open import Function as F hiding (_∋_)
open import Data.Sum as S
open import Relation.Binary.PropositionalEquality
open import Inception.Prelude

open import Level using (0ℓ)
open import Inception.Cont.Base
open import Inception.Monad.Base using (Monad)

K : Set -> Set
K = K[ R ]

open Monad (K[_]-Monad {x = 0ℓ} R) using (η; _*)

recK : {X : Set} -> R ^ ℙ × ℙ -> K X
recK (k , p) _ = k p

incK : {X : Set} -> (R ^ ℙ -> K X) × (ℙ -> K X) -> K X
incK (f , g) k = f (\p -> g p k) k

⟦_⟧ : Ty -> Set
⟦ `Unit ⟧ = ⊤
⟦ A `× B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A `⇒ B ⟧ = ⟦ A ⟧ -> K ⟦ B ⟧
⟦ `V ⟧ = ℙ -> R
⟦ `P ⟧ = ℙ

open Sem ⟦_⟧

mutual
  ⟦_⟧ᵛ : Γ ⊢ᵛ A -> ⟦ Γ ⟧ˣ -> ⟦ A ⟧
  ⟦ var i ⟧ᵛ = ⟦ i ⟧ᵐ
  ⟦ lam M ⟧ᵛ = curry ⟦ M ⟧ᶜ
  ⟦ pair V W ⟧ᵛ = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ >
  ⟦ unit ⟧ᵛ = const tt

  ⟦_⟧ᶜ : Γ ⊢ᶜ A -> ⟦ Γ ⟧ˣ -> K ⟦ A ⟧
  ⟦ return V ⟧ᶜ = ⟦ V ⟧ᵛ ； η
  ⟦ pm V M ⟧ᶜ = < idf , ⟦ V ⟧ᵛ > ； assocl ； ⟦ M ⟧ᶜ
  ⟦ push M N ⟧ᶜ = < idf , ⟦ M ⟧ᶜ > ； τ ； ⟦ N ⟧ᶜ *
  ⟦ app V W ⟧ᶜ = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ > ； ev
  ⟦ rec V W ⟧ᶜ = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ > ； recK
  ⟦ inc M N ⟧ᶜ = < curry ⟦ M ⟧ᶜ , curry ⟦ N ⟧ᶜ > ； incK

mutual
  evalVal : Γ ⊢ᵛ A -> ⟦ Γ ⟧ˣ -> ⟦ A ⟧
  evalVal (var i) γ =
    ⟦ i ⟧ᵐ γ
  evalVal (lam M) γ a =
    curry (evalComp M) (γ , a)
  evalVal (pair V W) γ =
    evalVal V γ , evalVal W γ
  evalVal unit γ = tt

  evalComp :  Γ ⊢ᶜ A -> ⟦ Γ ⟧ˣ × (⟦ A ⟧ -> R) -> R
  evalComp (return V) (γ , k) =
    let v = evalVal V γ in
      k v
  evalComp (pm V M) (γ , k) =
    let v = evalVal V γ in
      evalComp M (((γ , v .proj₁) , v .proj₂) , k)
  evalComp (push M N) (γ , k) =
    evalComp M (γ , \a ->
      evalComp N ((γ , a) , k))
  evalComp (app V W) (γ , k) =
    let v = evalVal V γ in
      let w = evalVal W γ in
        (v w) k
  evalComp (rec V W) (γ , k) =
    let v = evalVal V γ in
      let w = evalVal W γ in
        v w
  evalComp (inc M N) (γ , k) =
    evalComp M ((γ , \p ->
      evalComp N ((γ , p) , k)) , k)

⟦_⟧ˢ : Sub Γ Δ -> ⟦ Γ ⟧ˣ -> ⟦ Δ ⟧ˣ
⟦ sub-ε ⟧ˢ = const tt
⟦ sub-ex θ V ⟧ˢ = < ⟦ θ ⟧ˢ , ⟦ V ⟧ᵛ >

-- coherences
mutual
  wk-val-coh : (π : Γ ⊇ Δ) (V : Δ ⊢ᵛ A) -> ⟦ wk-val π V ⟧ᵛ ≡ (⟦ π ⟧ʷ ； ⟦ V ⟧ᵛ)
  wk-val-coh π (var i) rewrite wk-mem-coh π i = refl
  wk-val-coh π (lam M) rewrite wk-comp-coh (wk-cong π) M = refl
  wk-val-coh π (pair V W) rewrite wk-val-coh π V | wk-val-coh π W = refl
  wk-val-coh π unit = refl

  wk-comp-coh : (π : Γ ⊇ Δ) (M : Δ ⊢ᶜ A) -> ⟦ wk-comp π M ⟧ᶜ ≡ (⟦ π ⟧ʷ ； ⟦ M ⟧ᶜ)
  wk-comp-coh π (return V) rewrite wk-val-coh π V = refl
  wk-comp-coh π (pm V M) rewrite wk-val-coh π V | wk-comp-coh (wk-cong (wk-cong π)) M = refl
  wk-comp-coh π (push M N) rewrite wk-comp-coh π M | wk-comp-coh (wk-cong π) N = refl
  wk-comp-coh π (app V W) rewrite wk-val-coh π V | wk-val-coh π W = refl
  wk-comp-coh π (rec V W) rewrite wk-val-coh π V | wk-val-coh π W = refl
  wk-comp-coh π (inc M N) rewrite wk-comp-coh (wk-cong π) M | wk-comp-coh (wk-cong π) N = refl

{-# REWRITE wk-val-coh #-}
{-# REWRITE wk-comp-coh #-}

sub-mem-coh : (θ : Sub Γ Δ) (i : Δ ∋ A) -> ⟦ sub-mem θ i ⟧ᵛ ≡ (⟦ θ ⟧ˢ ； ⟦ i ⟧ᵐ)
sub-mem-coh (sub-ex θ V) here = refl
sub-mem-coh (sub-ex θ V) (there i) rewrite sub-mem-coh θ i = refl
{-# REWRITE sub-mem-coh #-}

sub-wk-coh : (π : Γ ⊇ Δ) (θ : Sub Δ Ψ) -> ⟦ sub-wk π θ ⟧ˢ ≡ (⟦ π ⟧ʷ ； ⟦ θ ⟧ˢ)
sub-wk-coh π sub-ε = refl
sub-wk-coh π (sub-ex θ V) rewrite sub-wk-coh π θ | wk-val-coh π V = refl
{-# REWRITE sub-wk-coh #-}

sub-id-coh : ⟦ sub-id {Γ} ⟧ˢ ≡ id
sub-id-coh {ε} = refl
sub-id-coh {Γ ∙ A} = funext \(γ , a) -> cong₂ _,_ (happly sub-id-coh γ) refl
{-# REWRITE sub-id-coh #-}

mutual
  sub-val-coh : (θ : Sub Γ Δ) (V : Δ ⊢ᵛ A) -> ⟦ sub-val θ V ⟧ᵛ ≡ (⟦ θ ⟧ˢ ； ⟦ V ⟧ᵛ)
  sub-val-coh θ (var i) = refl
  sub-val-coh θ (lam M) rewrite sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M = refl
  sub-val-coh θ (pair V W) rewrite sub-val-coh θ V | sub-val-coh θ W = refl
  sub-val-coh θ unit = refl

  sub-comp-coh : (θ : Sub Γ Δ) (M : Δ ⊢ᶜ A) -> ⟦ sub-comp θ M ⟧ᶜ ≡ (⟦ θ ⟧ˢ ； ⟦ M ⟧ᶜ)
  sub-comp-coh θ (return V) rewrite sub-val-coh θ V = refl
  sub-comp-coh θ (pm V M) rewrite sub-val-coh θ V | sub-comp-coh (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M = refl
  sub-comp-coh θ (push M N) rewrite sub-comp-coh θ M | sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N = refl
  sub-comp-coh θ (app V W) rewrite sub-val-coh θ V | sub-val-coh θ W = refl
  sub-comp-coh θ (rec V W) rewrite sub-val-coh θ V | sub-val-coh θ W = refl
  sub-comp-coh θ (inc M N) rewrite sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M | sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N = refl

{-# REWRITE sub-val-coh #-}
{-# REWRITE sub-comp-coh #-}

mutual
  eqVal : Γ ⊢ᵛ V ≈ W ∶ A -> ⟦ V ⟧ᵛ ≡ ⟦ W ⟧ᵛ
  eqVal ≈-refl = refl
  eqVal (≈-sym p) = sym (eqVal p)
  eqVal (≈-trans p q) = trans (eqVal p) (eqVal q)
  eqVal (lam-cong p) = cong curry (eqComp p)
  eqVal (pair-cong p q) = cong₂ <_,_> (eqVal p) (eqVal q)
  eqVal (unit-eta _) = refl
  eqVal (lam-eta _) = refl

  eqComp : Γ ⊢ᶜ M ≈ N ∶ A -> ⟦ M ⟧ᶜ ≡ ⟦ N ⟧ᶜ
  eqComp ≈-refl = refl
  eqComp (≈-sym p) = sym (eqComp p)
  eqComp (≈-trans p q) = trans (eqComp p) (eqComp q)
  eqComp (return-cong p) rewrite eqVal p = refl
  eqComp (pm-cong p q) rewrite eqVal p | eqComp q = refl
  eqComp (push-cong p q) rewrite eqComp p | eqComp q = refl
  eqComp (app-cong p q) rewrite eqVal p | eqVal q = refl
  eqComp (rec-cong p q) rewrite eqVal p | eqVal q = refl
  eqComp (inc-cong p q) rewrite eqComp p | eqComp q = refl
  eqComp (pm-beta V1 V2 M) = refl
  eqComp (pm-eta V M) = refl
  eqComp (return-beta V M) = refl
  eqComp (return-eta _) = refl
  eqComp (push-eta M N P) = refl
  eqComp (lam-beta M V) = refl
  eqComp (inc-weak _ N) = refl
  eqComp (inc-subst _ _) = refl
  eqComp (inc-ext M V) = refl
  eqComp (inc-assoc L M N) = refl
  eqComp (rec-push V W M) = refl
  eqComp (inc-push M N L) = refl
