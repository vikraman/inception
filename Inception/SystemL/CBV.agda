module Inception.SystemL.CBV (P R : Set) where

open import Inception.SystemL.Syntax hiding (K)

open import Data.Empty
open import Data.Product as P
open import Data.Sum as S
open import Data.Unit
open import Function as F hiding (_∋_)
open import Inception.Prelude
open import Level
open import Relation.Binary.PropositionalEquality

open import Inception.Cont.Base

K : Set → Set
K = K[ R ]
T = K[_]-Monad {x = zero} R

open import Inception.Monad.Base using (Monad)
open Monad T public

⟦_⟧ : Ty → Set
⟦ `⊥ ⟧ = R
⟦ `𝟙 ⟧ = ⊤
⟦ `𝓅 ⟧ = P
⟦ X `× Y ⟧ = ⟦ X ⟧ × ⟦ Y ⟧
⟦ X `⇒ Y ⟧ = ⟦ X ⟧ → K ⟦ Y ⟧
⟦ X `+ Y ⟧ = ⟦ X ⟧ ⊎ ⟦ Y ⟧

open Sem ⟦_⟧

{-# REWRITE wk-mem-coh wk-mem-coh̃ #-}

mutual
  ⟦_⟧ᶜ : Γ ⊢ Δ → ⟦ Γ ⟧ˣ × R ^ ⟦ Δ ⟧ˣ̃ → R
  ⟦ cut _ M K ⟧ᶜ = < ⟦ M ⟧ᵗ , ⟦ K ⟧ᵏ > ； ev

  ⟦_⟧ᵛ : Γ ⊢ᵛ X ∣ Δ → ⟦ Γ ⟧ˣ × R ^ ⟦ Δ ⟧ˣ̃ → ⟦ X ⟧
  ⟦ var i ⟧ᵛ = proj₁ ； ⟦ i ⟧ᵐ
  ⟦ lam M ⟧ᵛ = curry′ (shuffle ； ⟦ M ⟧ᵗ)
  ⟦ unit ⟧ᵛ = const tt
  ⟦ pair V W ⟧ᵛ = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ >
  ⟦ inl V ⟧ᵛ = ⟦ V ⟧ᵛ ； inj₁
  ⟦ inr W ⟧ᵛ = ⟦ W ⟧ᵛ ； inj₂

  ⟦_⟧ᵗ : Γ ⊢ᵗ X ∣ Δ → ⟦ Γ ⟧ˣ × R ^ ⟦ Δ ⟧ˣ̃ → K ⟦ X ⟧
  ⟦ ret V ⟧ᵗ = ⟦ V ⟧ᵛ ； η
  ⟦ μ C ⟧ᵗ = councurry (curry′ ⟦ C ⟧ᶜ)

  ⟦_⟧ᵏ : Γ ∣ X ⊢ᵏ Δ → ⟦ Γ ⟧ˣ × R ^ ⟦ Δ ⟧ˣ̃ → R ^ ⟦ X ⟧
  ⟦ covar i ⟧ᵏ = proj₂ ； ([ R ]^ ⟦ i ⟧ᵐ̃)
  ⟦ app V K ⟧ᵏ = < ⟦ K ⟧ᵏ , ⟦ V ⟧ᵛ > ； η ； [ R ]^ cbv
  ⟦ fst K ⟧ᵏ = ⟦ K ⟧ᵏ ； curry′ (assocl ； proj₁ ； ev)
  ⟦ snd K ⟧ᵏ = ⟦ K ⟧ᵏ ； curry′ (assocl ； P.map proj₁ id ； ev)
  ⟦ case K L ⟧ᵏ = < ⟦ K ⟧ᵏ , ⟦ L ⟧ᵏ > ； uncurry′ S.[_,_]
  ⟦ μ̃ C ⟧ᵏ = curry′ (shuffle ； ⟦ C ⟧ᶜ)
  ⟦ tp ⟧ᵏ = const idf

⟦_⟧ˢ : Γ ⊢ Ψ ∣ Δ → ⟦ Γ ⟧ˣ × R ^ ⟦ Δ ⟧ˣ̃ → ⟦ Ψ ⟧ˣ
⟦ sub-ε ⟧ˢ = const tt
⟦ sub-ex θ V ⟧ˢ = < ⟦ θ ⟧ˢ , ⟦ V ⟧ᵛ >

⟦_⟧ˢ̃ : Γ ∣ Ξ ⊢ Δ → ⟦ Γ ⟧ˣ × R ^ ⟦ Δ ⟧ˣ̃ → R ^ ⟦ Ξ ⟧ˣ̃
⟦ cosub-ε ⟧ˢ̃ = const λ ()
⟦ cosub-ex φ K ⟧ˢ̃ env = S.[ ⟦ φ ⟧ˢ̃ env , ⟦ K ⟧ᵏ env ]

-- coherences

wkenv : Γ ⊇ Ψ → Δ ⊇ Ξ → ⟦ Γ ⟧ˣ × R ^ ⟦ Δ ⟧ˣ̃ → ⟦ Ψ ⟧ˣ × R ^ ⟦ Ξ ⟧ˣ̃
wkenv π ρ = P.map ⟦ π ⟧ʷ ([ R ]^ ⟦ ρ ⟧ʷ̃)

mutual
  wk-cmd-coh : (π : Γ ⊇ Ψ) (ρ : Δ ⊇ Ξ) (C : Ψ ⊢ Ξ) → ⟦ wk-cmd π ρ C ⟧ᶜ ≡ (wkenv π ρ ； ⟦ C ⟧ᶜ)
  wk-cmd-coh π ρ (cut X M K) rewrite wk-tm-coh π ρ M | wk-cotm-coh π ρ K = refl

  wk-val-coh : (π : Γ ⊇ Ψ) (ρ : Δ ⊇ Ξ) (V : Ψ ⊢ᵛ X ∣ Ξ) → ⟦ wk-val π ρ V ⟧ᵛ ≡ (wkenv π ρ ； ⟦ V ⟧ᵛ)
  wk-val-coh π ρ (var i) = refl
  wk-val-coh π ρ (lam M) rewrite wk-tm-coh (wk-cong π) ρ M = refl
  wk-val-coh π ρ unit = refl
  wk-val-coh π ρ (pair V W) rewrite wk-val-coh π ρ V | wk-val-coh π ρ W = refl
  wk-val-coh π ρ (inl V) rewrite wk-val-coh π ρ V = refl
  wk-val-coh π ρ (inr W) rewrite wk-val-coh π ρ W = refl

  wk-tm-coh : (π : Γ ⊇ Ψ) (ρ : Δ ⊇ Ξ) (M : Ψ ⊢ᵗ X ∣ Ξ) → ⟦ wk-tm π ρ M ⟧ᵗ ≡ (wkenv π ρ ； ⟦ M ⟧ᵗ)
  wk-tm-coh π ρ (ret V) rewrite wk-val-coh π ρ V = refl
  wk-tm-coh π ρ (μ C) rewrite wk-cmd-coh π (wk-cong ρ) C =
    funext λ { (γ , k) → funext λ k₂ →
      cong (λ x → ⟦ C ⟧ᶜ (⟦ π ⟧ʷ γ , x)) (funext λ { (inj₁ x) → refl ; (inj₂ y) → refl }) }

  wk-cotm-coh : (π : Γ ⊇ Ψ) (ρ : Δ ⊇ Ξ) (K : Ψ ∣ X ⊢ᵏ Ξ) → ⟦ wk-cotm π ρ K ⟧ᵏ ≡ (wkenv π ρ ； ⟦ K ⟧ᵏ)
  wk-cotm-coh π ρ (covar i) = refl
  wk-cotm-coh π ρ (app V K) rewrite wk-val-coh π ρ V | wk-cotm-coh π ρ K = refl
  wk-cotm-coh π ρ (fst K) rewrite wk-cotm-coh π ρ K = refl
  wk-cotm-coh π ρ (snd K) rewrite wk-cotm-coh π ρ K = refl
  wk-cotm-coh π ρ (case K L) rewrite wk-cotm-coh π ρ K | wk-cotm-coh π ρ L = refl
  wk-cotm-coh π ρ (μ̃ C) rewrite wk-cmd-coh (wk-cong π) ρ C = refl
  wk-cotm-coh π ρ tp = refl

{-# REWRITE wk-val-coh #-}
{-# REWRITE wk-tm-coh #-}
{-# REWRITE wk-cotm-coh #-}
{-# REWRITE wk-cmd-coh #-}

sub-mem-coh : (θ : Γ ⊢ Ψ ∣ Δ) (i : Ψ ∋ X) → ⟦ sub-mem θ i ⟧ᵛ ≡ (⟦ θ ⟧ˢ ； ⟦ i ⟧ᵐ)
sub-mem-coh (sub-ex θ V) here = refl
sub-mem-coh (sub-ex θ V) (there i) rewrite sub-mem-coh θ i = refl
{-# REWRITE sub-mem-coh #-}

cosub-mem-coh : (φ : Γ ∣ Ξ ⊢ Δ) (i : Ξ ∋ X) → ⟦ cosub-mem φ i ⟧ᵏ ≡ (⟦ φ ⟧ˢ̃ ； ([ R ]^ ⟦ i ⟧ᵐ̃))
cosub-mem-coh (cosub-ex φ K) here = refl
cosub-mem-coh (cosub-ex φ K) (there i) rewrite cosub-mem-coh φ i = refl
{-# REWRITE cosub-mem-coh #-}

sub-wk-coh : (π : Ψ ⊇ Γ) (ρ : Ξ ⊇ Δ) (θ : Γ ⊢ Γ₁ ∣ Δ) → ⟦ sub-wk π ρ θ ⟧ˢ ≡ (wkenv π ρ ； ⟦ θ ⟧ˢ)
sub-wk-coh π ρ sub-ε = refl
sub-wk-coh π ρ (sub-ex θ V) rewrite sub-wk-coh π ρ θ | wk-val-coh π ρ V = refl
{-# REWRITE sub-wk-coh #-}

cosub-wk-coh : (π : Ψ ⊇ Γ) (ρ : Ξ ⊇ Δ) (φ : Γ ∣ Δ₁ ⊢ Δ) → ⟦ cosub-wk π ρ φ ⟧ˢ̃ ≡ (wkenv π ρ ； ⟦ φ ⟧ˢ̃)
cosub-wk-coh π ρ cosub-ε = refl
cosub-wk-coh π ρ (cosub-ex φ K) rewrite cosub-wk-coh π ρ φ | wk-cotm-coh π ρ K = refl
{-# REWRITE cosub-wk-coh #-}

sub-id-coh : ⟦ sub-id {Γ} {Δ} ⟧ˢ ≡ proj₁
sub-id-coh {Γ = ε} {Δ} = refl
sub-id-coh {Γ = Γ ∙ X} {Δ} = funext λ
  { ((γ , a) , k) → cong₂ _,_ (happly (sub-id-coh {Γ = Γ} {Δ}) (γ , k)) refl }
{-# REWRITE sub-id-coh #-}

cosub-id-coh : ⟦ cosub-id {Γ} {Δ} ⟧ˢ̃ ≡ proj₂
cosub-id-coh {Γ} {Δ = ε} = funext λ { (γ , k) → funext λ () }
cosub-id-coh {Γ} {Δ = Δ ∙ X} = funext λ
  { (γ , k) → trans (cong (λ x → S.[ x , k ∘ inj₂ ]) (happly (cosub-id-coh {Γ} {Δ = Δ}) (γ , k ∘ inj₁)))
                    (funext λ { (inj₁ x) → refl ; (inj₂ y) → refl }) }
{-# REWRITE cosub-id-coh #-}

subenv : Γ ⊢ Ψ ∣ Δ → Γ ∣ Ξ ⊢ Δ → ⟦ Γ ⟧ˣ × R ^ ⟦ Δ ⟧ˣ̃ → ⟦ Ψ ⟧ˣ × R ^ ⟦ Ξ ⟧ˣ̃
subenv θ φ = < ⟦ θ ⟧ˢ , ⟦ φ ⟧ˢ̃ >

mutual
  sub-cmd-coh : (θ : Γ ⊢ Ψ ∣ Δ) (φ : Γ ∣ Ξ ⊢ Δ) (C : Ψ ⊢ Ξ) → ⟦ sub-cmd θ φ C ⟧ᶜ ≡ (subenv θ φ ； ⟦ C ⟧ᶜ)
  sub-cmd-coh θ φ (cut X M K) rewrite sub-tm-coh θ φ M | sub-cotm-coh θ φ K = refl

  sub-val-coh : (θ : Γ ⊢ Ψ ∣ Δ) (φ : Γ ∣ Ξ ⊢ Δ) (V : Ψ ⊢ᵛ X ∣ Ξ) → ⟦ sub-val θ φ V ⟧ᵛ ≡ (subenv θ φ ； ⟦ V ⟧ᵛ)
  sub-val-coh θ φ (var i) = refl
  sub-val-coh θ φ (lam M) rewrite sub-tm-coh (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M = refl
  sub-val-coh θ φ unit = refl
  sub-val-coh θ φ (pair V W) rewrite sub-val-coh θ φ V | sub-val-coh θ φ W = refl
  sub-val-coh θ φ (inl V) rewrite sub-val-coh θ φ V = refl
  sub-val-coh θ φ (inr W) rewrite sub-val-coh θ φ W = refl

  sub-tm-coh : (θ : Γ ⊢ Ψ ∣ Δ) (φ : Γ ∣ Ξ ⊢ Δ) (M : Ψ ⊢ᵗ X ∣ Ξ) → ⟦ sub-tm θ φ M ⟧ᵗ ≡ (subenv θ φ ； ⟦ M ⟧ᵗ)
  sub-tm-coh θ φ (ret V) rewrite sub-val-coh θ φ V = refl
  sub-tm-coh θ φ (μ C) rewrite sub-cmd-coh (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) C = refl

  sub-cotm-coh : (θ : Γ ⊢ Ψ ∣ Δ) (φ : Γ ∣ Ξ ⊢ Δ) (K : Ψ ∣ X ⊢ᵏ Ξ) → ⟦ sub-cotm θ φ K ⟧ᵏ ≡ (subenv θ φ ； ⟦ K ⟧ᵏ)
  sub-cotm-coh θ φ (covar i) = refl
  sub-cotm-coh θ φ (app V K) rewrite sub-val-coh θ φ V | sub-cotm-coh θ φ K = refl
  sub-cotm-coh θ φ (fst K) rewrite sub-cotm-coh θ φ K = refl
  sub-cotm-coh θ φ (snd K) rewrite sub-cotm-coh θ φ K = refl
  sub-cotm-coh θ φ (case K L) rewrite sub-cotm-coh θ φ K | sub-cotm-coh θ φ L = refl
  sub-cotm-coh θ φ (μ̃ C) rewrite sub-cmd-coh (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) C = refl
  sub-cotm-coh θ φ tp = refl

{-# REWRITE sub-val-coh #-}
{-# REWRITE sub-tm-coh #-}
{-# REWRITE sub-cotm-coh #-}
{-# REWRITE sub-cmd-coh #-}

-- soundness of the equational theory

mutual
  eqVal : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ∣ Δ → ⟦ V₁ ⟧ᵛ ≡ ⟦ V₂ ⟧ᵛ
  eqVal ≈-refl = refl
  eqVal (≈-sym p) = sym (eqVal p)
  eqVal (≈-trans p q) = trans (eqVal p) (eqVal q)
  eqVal (lam-cong p) = cong (λ f → curry′ (shuffle ； f)) (eqTm p)
  eqVal (pair-cong p q) = cong₂ <_,_> (eqVal p) (eqVal q)
  eqVal (inl-cong p) = cong (_； inj₁) (eqVal p)
  eqVal (inr-cong p) = cong (_； inj₂) (eqVal p)
  eqVal (unit-eta V) = refl
  eqVal (lam-eta V) = refl

  eqTm : Γ ⊢ᵗ M₁ ≈ M₂ ∶ X ∣ Δ → ⟦ M₁ ⟧ᵗ ≡ ⟦ M₂ ⟧ᵗ
  eqTm ≈-refl = refl
  eqTm (≈-sym p) = sym (eqTm p)
  eqTm (≈-trans p q) = trans (eqTm p) (eqTm q)
  eqTm (ret-cong p) = cong (_； η) (eqVal p)
  eqTm (μ-cong p) = cong (λ f → councurry (curry′ f)) (eqCmd p)
  eqTm (μ-eta M) = refl
  eqTm (pair-eta V) = refl

  eqCoTm : Γ ∣ K₁ ≈ K₂ ∶ X ⊢ᵏ Δ → ⟦ K₁ ⟧ᵏ ≡ ⟦ K₂ ⟧ᵏ
  eqCoTm ≈-refl = refl
  eqCoTm (≈-sym p) = sym (eqCoTm p)
  eqCoTm (≈-trans p q) = trans (eqCoTm p) (eqCoTm q)
  eqCoTm (app-cong p q) = cong (_； η ； [ R ]^ cbv) (cong₂ <_,_> (eqCoTm q) (eqVal p))
  eqCoTm (fst-cong p) = cong (_； curry′ (assocl ； proj₁ ； ev)) (eqCoTm p)
  eqCoTm (snd-cong p) = cong (_； curry′ (assocl ； P.map proj₁ id ； ev)) (eqCoTm p)
  eqCoTm (case-cong p q) = cong (_； uncurry′ S.[_,_]) (cong₂ <_,_> (eqCoTm p) (eqCoTm q))
  eqCoTm (μ̃-cong p) = cong (λ f → curry′ (shuffle ； f)) (eqCmd p)
  eqCoTm (μ̃-eta K) = refl
  eqCoTm (case-eta K) = funext λ env → funext λ { (inj₁ x) → refl ; (inj₂ y) → refl }

  eqCmd : Γ ⊢ C₁ ≈ C₂ ⊣ Δ → ⟦ C₁ ⟧ᶜ ≡ ⟦ C₂ ⟧ᶜ
  eqCmd ≈-refl = refl
  eqCmd (≈-sym p) = sym (eqCmd p)
  eqCmd (≈-trans p q) = trans (eqCmd p) (eqCmd q)
  eqCmd (cut-cong p q) = cong (_； ev) (cong₂ <_,_> (eqTm p) (eqCoTm q))
  eqCmd (μ-beta M K) = refl
  eqCmd (μ̃-beta V M) = refl
  eqCmd (app-beta M V K) = refl
  eqCmd (fst-beta V W K) = refl
  eqCmd (snd-beta V W K) = refl
  eqCmd (inl-beta V K L) = refl
  eqCmd (inr-beta W K L) = refl
