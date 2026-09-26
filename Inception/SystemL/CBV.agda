module Inception.SystemL.CBV (P R : Set) where

open import Inception.SystemL.Syntax hiding (K)

open import Level
open import Data.Unit
open import Data.Empty
open import Data.Product as P
open import Function as F hiding (_∋_)
open import Data.Sum as S
open import Relation.Binary.PropositionalEquality
open import Inception.Prelude

open import Inception.Cont.Base

K : Set -> Set
K = K[ R ]
T = K[_]-Monad {x = zero} R

open import Inception.Monad.Base using (Monad)
open Monad T public

⟦_⟧ : Ty -> Set
⟦ `⊥ ⟧ = R
⟦ `Unit ⟧ = ⊤
⟦ `P ⟧ = P
⟦ A `× B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A `⇒ B ⟧ = ⟦ A ⟧ -> K ⟦ B ⟧
⟦ A `+ B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧

open Sem ⟦_⟧

{-# REWRITE wk-mem-coh wk-mem-coh̃ #-}

mutual
  ⟦_⟧ᶜ : Γ ⊢ Δ -> ⟦ Γ ⟧ˣ × R ^ ⟦ Δ ⟧ˣ̃ -> R
  ⟦ cut _ M K ⟧ᶜ = < ⟦ M ⟧ᵗ , ⟦ K ⟧ᵏ > ； ev

  ⟦_⟧ᵛ : Γ ⊢ᵛ A ∣ Δ -> ⟦ Γ ⟧ˣ × R ^ ⟦ Δ ⟧ˣ̃ -> ⟦ A ⟧
  ⟦ var i ⟧ᵛ = proj₁ ； ⟦ i ⟧ᵐ
  ⟦ lam M ⟧ᵛ = curry′ (shuffle ； ⟦ M ⟧ᵗ)
  ⟦ unit ⟧ᵛ = const tt
  ⟦ pair V W ⟧ᵛ = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ >
  ⟦ inl V ⟧ᵛ = ⟦ V ⟧ᵛ ； inj₁
  ⟦ inr W ⟧ᵛ = ⟦ W ⟧ᵛ ； inj₂

  ⟦_⟧ᵗ : Γ ⊢ᵗ A ∣ Δ -> ⟦ Γ ⟧ˣ × R ^ ⟦ Δ ⟧ˣ̃ -> K ⟦ A ⟧
  ⟦ ret V ⟧ᵗ = ⟦ V ⟧ᵛ ； η
  ⟦ μ M ⟧ᵗ = councurry (curry′ ⟦ M ⟧ᶜ)

  ⟦_⟧ᵏ : Γ ∣ A ⊢ᵏ Δ -> ⟦ Γ ⟧ˣ × R ^ ⟦ Δ ⟧ˣ̃ -> R ^ ⟦ A ⟧
  ⟦ covar i ⟧ᵏ = proj₂ ； ([ R ]^ ⟦ i ⟧ᵐ̃)
  ⟦ app V K ⟧ᵏ = < ⟦ K ⟧ᵏ , ⟦ V ⟧ᵛ > ； η ； [ R ]^ cbv
  ⟦ fst K ⟧ᵏ = ⟦ K ⟧ᵏ ； curry′ (assocl ； proj₁ ； ev)
  ⟦ snd K ⟧ᵏ = ⟦ K ⟧ᵏ ； curry′ (assocl ； P.map proj₁ id ； ev)
  ⟦ case K₁ K₂ ⟧ᵏ = < ⟦ K₁ ⟧ᵏ , ⟦ K₂ ⟧ᵏ > ； uncurry′ S.[_,_]
  ⟦ μ̃ M ⟧ᵏ = curry′ (shuffle ； ⟦ M ⟧ᶜ)
  ⟦ tp ⟧ᵏ = const idf

⟦_⟧ˢ : Sub Γ Δ Γ' -> ⟦ Γ ⟧ˣ × R ^ ⟦ Δ ⟧ˣ̃ -> ⟦ Γ' ⟧ˣ
⟦ sub-ε ⟧ˢ = const tt
⟦ sub-ex θ V ⟧ˢ = < ⟦ θ ⟧ˢ , ⟦ V ⟧ᵛ >

⟦_⟧ˢ̃ : CoSub Γ Δ Δ' -> ⟦ Γ ⟧ˣ × R ^ ⟦ Δ ⟧ˣ̃ -> R ^ ⟦ Δ' ⟧ˣ̃
⟦ cosub-ε ⟧ˢ̃ = const λ ()
⟦ cosub-ex φ K ⟧ˢ̃ env = S.[ ⟦ φ ⟧ˢ̃ env , ⟦ K ⟧ᵏ env ]

-- coherences

wkenv : Γ ⊇ Γ' -> Δ ⊇ Δ' -> ⟦ Γ ⟧ˣ × R ^ ⟦ Δ ⟧ˣ̃ -> ⟦ Γ' ⟧ˣ × R ^ ⟦ Δ' ⟧ˣ̃
wkenv ρ σ = P.map ⟦ ρ ⟧ʷ ([ R ]^ ⟦ σ ⟧ʷ̃)

mutual
  wk-cmd-coh : (ρ : Γ ⊇ Γ') (σ : Δ ⊇ Δ') (M : Γ' ⊢ Δ') -> ⟦ wk-cmd ρ σ M ⟧ᶜ ≡ (wkenv ρ σ ； ⟦ M ⟧ᶜ)
  wk-cmd-coh ρ σ (cut A M K) rewrite wk-tm-coh ρ σ M | wk-cotm-coh ρ σ K = refl

  wk-val-coh : (ρ : Γ ⊇ Γ') (σ : Δ ⊇ Δ') (V : Γ' ⊢ᵛ A ∣ Δ') -> ⟦ wk-val ρ σ V ⟧ᵛ ≡ (wkenv ρ σ ； ⟦ V ⟧ᵛ)
  wk-val-coh ρ σ (var i) = refl
  wk-val-coh ρ σ (lam M) rewrite wk-tm-coh (wk-cong ρ) σ M = refl
  wk-val-coh ρ σ unit = refl
  wk-val-coh ρ σ (pair V W) rewrite wk-val-coh ρ σ V | wk-val-coh ρ σ W = refl
  wk-val-coh ρ σ (inl V) rewrite wk-val-coh ρ σ V = refl
  wk-val-coh ρ σ (inr W) rewrite wk-val-coh ρ σ W = refl

  wk-tm-coh : (ρ : Γ ⊇ Γ') (σ : Δ ⊇ Δ') (M : Γ' ⊢ᵗ A ∣ Δ') -> ⟦ wk-tm ρ σ M ⟧ᵗ ≡ (wkenv ρ σ ； ⟦ M ⟧ᵗ)
  wk-tm-coh ρ σ (ret V) rewrite wk-val-coh ρ σ V = refl
  wk-tm-coh ρ σ (μ M) rewrite wk-cmd-coh ρ (wk-cong σ) M =
    funext λ { (γ , k) → funext λ k₂ →
      cong (λ x → ⟦ M ⟧ᶜ (⟦ ρ ⟧ʷ γ , x)) (funext λ { (inj₁ x) → refl ; (inj₂ y) → refl }) }

  wk-cotm-coh : (ρ : Γ ⊇ Γ') (σ : Δ ⊇ Δ') (K : Γ' ∣ A ⊢ᵏ Δ') -> ⟦ wk-cotm ρ σ K ⟧ᵏ ≡ (wkenv ρ σ ； ⟦ K ⟧ᵏ)
  wk-cotm-coh ρ σ (covar i) = refl
  wk-cotm-coh ρ σ (app V K) rewrite wk-val-coh ρ σ V | wk-cotm-coh ρ σ K = refl
  wk-cotm-coh ρ σ (fst K) rewrite wk-cotm-coh ρ σ K = refl
  wk-cotm-coh ρ σ (snd K) rewrite wk-cotm-coh ρ σ K = refl
  wk-cotm-coh ρ σ (case K₁ K₂) rewrite wk-cotm-coh ρ σ K₁ | wk-cotm-coh ρ σ K₂ = refl
  wk-cotm-coh ρ σ (μ̃ M) rewrite wk-cmd-coh (wk-cong ρ) σ M = refl
  wk-cotm-coh ρ σ tp = refl

{-# REWRITE wk-val-coh #-}
{-# REWRITE wk-tm-coh #-}
{-# REWRITE wk-cotm-coh #-}
{-# REWRITE wk-cmd-coh #-}

sub-mem-coh : (θ : Sub Γ Δ Γ') (i : Γ' ∋ A) -> ⟦ sub-mem θ i ⟧ᵛ ≡ (⟦ θ ⟧ˢ ； ⟦ i ⟧ᵐ)
sub-mem-coh (sub-ex θ V) here = refl
sub-mem-coh (sub-ex θ V) (there i) rewrite sub-mem-coh θ i = refl
{-# REWRITE sub-mem-coh #-}

cosub-mem-coh : (φ : CoSub Γ Δ Δ') (i : Δ' ∋ A) -> ⟦ cosub-mem φ i ⟧ᵏ ≡ (⟦ φ ⟧ˢ̃ ； ([ R ]^ ⟦ i ⟧ᵐ̃))
cosub-mem-coh (cosub-ex φ K) here = refl
cosub-mem-coh (cosub-ex φ K) (there i) rewrite cosub-mem-coh φ i = refl
{-# REWRITE cosub-mem-coh #-}

sub-wk-coh : (ρ : Γ₁ ⊇ Γ) (σ : Δ₁ ⊇ Δ) (θ : Sub Γ Δ Γ') -> ⟦ sub-wk ρ σ θ ⟧ˢ ≡ (wkenv ρ σ ； ⟦ θ ⟧ˢ)
sub-wk-coh ρ σ sub-ε = refl
sub-wk-coh ρ σ (sub-ex θ V) rewrite sub-wk-coh ρ σ θ | wk-val-coh ρ σ V = refl
{-# REWRITE sub-wk-coh #-}

cosub-wk-coh : (ρ : Γ₁ ⊇ Γ) (σ : Δ₁ ⊇ Δ) (φ : CoSub Γ Δ Δ') -> ⟦ cosub-wk ρ σ φ ⟧ˢ̃ ≡ (wkenv ρ σ ； ⟦ φ ⟧ˢ̃)
cosub-wk-coh ρ σ cosub-ε = refl
cosub-wk-coh ρ σ (cosub-ex φ K) rewrite cosub-wk-coh ρ σ φ | wk-cotm-coh ρ σ K = refl
{-# REWRITE cosub-wk-coh #-}

sub-id-coh : ⟦ sub-id {Γ} {Δ} ⟧ˢ ≡ proj₁
sub-id-coh {Γ = ε} {Δ} = refl
sub-id-coh {Γ = Γ ∙ A} {Δ} = funext λ
  { ((γ , a) , k) → cong₂ _,_ (happly (sub-id-coh {Γ = Γ} {Δ}) (γ , k)) refl }
{-# REWRITE sub-id-coh #-}

cosub-id-coh : ⟦ cosub-id {Γ} {Δ} ⟧ˢ̃ ≡ proj₂
cosub-id-coh {Γ} {Δ = ε} = funext λ { (γ , k) → funext λ () }
cosub-id-coh {Γ} {Δ = Δ ∙ A} = funext λ
  { (γ , k) → trans (cong (λ x → S.[ x , k ∘ inj₂ ]) (happly (cosub-id-coh {Γ} {Δ = Δ}) (γ , k ∘ inj₁)))
                    (funext λ { (inj₁ x) → refl ; (inj₂ y) → refl }) }
{-# REWRITE cosub-id-coh #-}

subenv : Sub Γ Δ Γ' -> CoSub Γ Δ Δ' -> ⟦ Γ ⟧ˣ × R ^ ⟦ Δ ⟧ˣ̃ -> ⟦ Γ' ⟧ˣ × R ^ ⟦ Δ' ⟧ˣ̃
subenv θ φ = < ⟦ θ ⟧ˢ , ⟦ φ ⟧ˢ̃ >

mutual
  sub-cmd-coh : (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ') (M : Γ' ⊢ Δ') -> ⟦ sub-cmd θ φ M ⟧ᶜ ≡ (subenv θ φ ； ⟦ M ⟧ᶜ)
  sub-cmd-coh θ φ (cut A M K) rewrite sub-tm-coh θ φ M | sub-cotm-coh θ φ K = refl

  sub-val-coh : (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ') (V : Γ' ⊢ᵛ A ∣ Δ') -> ⟦ sub-val θ φ V ⟧ᵛ ≡ (subenv θ φ ； ⟦ V ⟧ᵛ)
  sub-val-coh θ φ (var i) = refl
  sub-val-coh θ φ (lam M) rewrite sub-tm-coh (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M = refl
  sub-val-coh θ φ unit = refl
  sub-val-coh θ φ (pair V W) rewrite sub-val-coh θ φ V | sub-val-coh θ φ W = refl
  sub-val-coh θ φ (inl V) rewrite sub-val-coh θ φ V = refl
  sub-val-coh θ φ (inr W) rewrite sub-val-coh θ φ W = refl

  sub-tm-coh : (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ') (M : Γ' ⊢ᵗ A ∣ Δ') -> ⟦ sub-tm θ φ M ⟧ᵗ ≡ (subenv θ φ ； ⟦ M ⟧ᵗ)
  sub-tm-coh θ φ (ret V) rewrite sub-val-coh θ φ V = refl
  sub-tm-coh θ φ (μ M) rewrite sub-cmd-coh (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar here)) M = refl

  sub-cotm-coh : (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ') (K : Γ' ∣ A ⊢ᵏ Δ') -> ⟦ sub-cotm θ φ K ⟧ᵏ ≡ (subenv θ φ ； ⟦ K ⟧ᵏ)
  sub-cotm-coh θ φ (covar i) = refl
  sub-cotm-coh θ φ (app V K) rewrite sub-val-coh θ φ V | sub-cotm-coh θ φ K = refl
  sub-cotm-coh θ φ (fst K) rewrite sub-cotm-coh θ φ K = refl
  sub-cotm-coh θ φ (snd K) rewrite sub-cotm-coh θ φ K = refl
  sub-cotm-coh θ φ (case K₁ K₂) rewrite sub-cotm-coh θ φ K₁ | sub-cotm-coh θ φ K₂ = refl
  sub-cotm-coh θ φ (μ̃ M) rewrite sub-cmd-coh (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var here)) (cosub-wk (wk-wk wk-id) wk-id φ) M = refl
  sub-cotm-coh θ φ tp = refl

{-# REWRITE sub-val-coh #-}
{-# REWRITE sub-tm-coh #-}
{-# REWRITE sub-cotm-coh #-}
{-# REWRITE sub-cmd-coh #-}

-- soundness of the equational theory

mutual
  eqVal : Γ ⊢ᵛ V₁ ≈ V₂ ∶ A ∣ Δ -> ⟦ V₁ ⟧ᵛ ≡ ⟦ V₂ ⟧ᵛ
  eqVal ≈-refl = refl
  eqVal (≈-sym p) = sym (eqVal p)
  eqVal (≈-trans p q) = trans (eqVal p) (eqVal q)
  eqVal (lam-cong p) = cong (λ f → curry′ (shuffle ； f)) (eqTm p)
  eqVal (pair-cong p q) = cong₂ <_,_> (eqVal p) (eqVal q)
  eqVal (inl-cong p) = cong (_； inj₁) (eqVal p)
  eqVal (inr-cong p) = cong (_； inj₂) (eqVal p)
  eqVal (unit-eta V) = refl
  eqVal (lam-eta V) = refl

  eqTm : Γ ⊢ᵗ M₁ ≈ M₂ ∶ A ∣ Δ -> ⟦ M₁ ⟧ᵗ ≡ ⟦ M₂ ⟧ᵗ
  eqTm ≈-refl = refl
  eqTm (≈-sym p) = sym (eqTm p)
  eqTm (≈-trans p q) = trans (eqTm p) (eqTm q)
  eqTm (ret-cong p) = cong (_； η) (eqVal p)
  eqTm (μ-cong p) = cong (λ f → councurry (curry′ f)) (eqCmd p)
  eqTm (μ-eta M) = refl
  eqTm (pair-eta V) = refl

  eqCoTm : Γ ∣ K₁ ≈ K₂ ∶ A ⊢ᵏ Δ -> ⟦ K₁ ⟧ᵏ ≡ ⟦ K₂ ⟧ᵏ
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

  eqCmd : Γ ⊢ M₁' ≈ M₂' ⊣ Δ -> ⟦ M₁' ⟧ᶜ ≡ ⟦ M₂' ⟧ᶜ
  eqCmd ≈-refl = refl
  eqCmd (≈-sym p) = sym (eqCmd p)
  eqCmd (≈-trans p q) = trans (eqCmd p) (eqCmd q)
  eqCmd (cut-cong p q) = cong (_； ev) (cong₂ <_,_> (eqTm p) (eqCoTm q))
  eqCmd (μ-beta M K) = refl
  eqCmd (μ̃-beta V M) = refl
  eqCmd (app-beta M V K) = refl
  eqCmd (fst-beta V W K) = refl
  eqCmd (snd-beta V W K) = refl
  eqCmd (inl-beta V K₁ K₂) = refl
  eqCmd (inr-beta W K₁ K₂) = refl
