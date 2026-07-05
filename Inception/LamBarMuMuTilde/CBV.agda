module Inception.LamBarMuMuTilde.CBV (R : Set) where

open import Inception.LamBarMuMuTilde.Syntax

open import Level
open import Data.Unit
open import Data.Empty
open import Data.Product as P
open import Function as F hiding (_∋_)
open import Data.Sum as S
open import Relation.Binary.PropositionalEquality
open import Inception.Prelude

infixr 4 _；_

_；_ : ∀ {ℓ} {A B C : Set ℓ} -> (A -> B) -> (B -> C) -> (A -> C)
f ； g = g ∘ f

idf : ∀ {ℓ} {A : Set ℓ} -> A -> A
idf a = a

assocl : ∀ {ℓ} {A B C : Set ℓ} -> A × (B × C) -> (A × B) × C
assocl (a , (b , c)) = (a , b) , c

shuffle : ∀ {ℓ} {A B C : Set ℓ} -> (A × B) × C -> (A × C) × B
shuffle ((a , b) , c) = (a , c) , b

open import Inception.Cont.Base

K : Set -> Set
K = K[ R ]
T = K[_]-Monad {x = zero} R

open import Inception.Monad.Base using (Monad)
open Monad T public

τ : {X Y : Set} -> X × K Y -> K (X × Y)
τ (x , ky) k = ky \z -> k (x , z)

cbv : {X Y : Set} -> (X -> K Y) -> R ^ (R ^ Y × X)
cbv f (k , x) = f x k

eval : {X Y : Set} -> Y ^ X × X -> Y
eval = uncurry′ idf

⟦_⟧ : Ty -> Set
⟦ `⊥ ⟧ = R
⟦ `Unit ⟧ = ⊤
⟦ A `× B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A `⇒ B ⟧ = ⟦ A ⟧ -> K ⟦ B ⟧
⟦ A `+ B ⟧ = ⟦ A ⟧ ⊎ ⟦ B ⟧

⟦_⟧ⁿ : Env -> Set
⟦ ε ⟧ⁿ = ⊤
⟦ Γ ∙ A ⟧ⁿ = ⟦ Γ ⟧ⁿ × ⟦ A ⟧

⟦_⟧ⁿ̃ : Env -> Set
⟦ ε ⟧ⁿ̃ = ⊥
⟦ Δ ∙ A ⟧ⁿ̃ = ⟦ Δ ⟧ⁿ̃ ⊎ ⟦ A ⟧

⟦_⟧ʷ : Γ ⊇ Δ -> ⟦ Γ ⟧ⁿ -> ⟦ Δ ⟧ⁿ
⟦ wk-ε ⟧ʷ = idf
⟦ wk-cong π ⟧ʷ = < proj₁ ； ⟦ π ⟧ʷ , proj₂ >
⟦ wk-wk π ⟧ʷ = proj₁ ； ⟦ π ⟧ʷ

⟦_⟧ʷ̃ : Δ ⊇ Δ' -> ⟦ Δ' ⟧ⁿ̃ -> ⟦ Δ ⟧ⁿ̃
⟦ wk-ε ⟧ʷ̃ ()
⟦ wk-cong π ⟧ʷ̃ (inj₁ x) = inj₁ (⟦ π ⟧ʷ̃ x)
⟦ wk-cong π ⟧ʷ̃ (inj₂ y) = inj₂ y
⟦ wk-wk π ⟧ʷ̃ x = inj₁ (⟦ π ⟧ʷ̃ x)

⟦_⟧ᵐ : Γ ∋ A -> ⟦ Γ ⟧ⁿ -> ⟦ A ⟧
⟦ z ⟧ᵐ = proj₂
⟦ s x ⟧ᵐ = proj₁ ； ⟦ x ⟧ᵐ

⟦_⟧ᵐ̃ : Δ ∋ A -> ⟦ A ⟧ -> ⟦ Δ ⟧ⁿ̃
⟦ z ⟧ᵐ̃ = inj₂
⟦ s i ⟧ᵐ̃ = ⟦ i ⟧ᵐ̃ ； inj₁

mutual
  ⟦_⟧ᶜ : Γ ⊢ Δ -> ⟦ Γ ⟧ⁿ × R ^ ⟦ Δ ⟧ⁿ̃ -> R
  ⟦ cut _ t e ⟧ᶜ = < ⟦ t ⟧ᵗ , ⟦ e ⟧ᵉ > ； eval

  ⟦_⟧ᵛ : Γ ⊢ᵛ A ∣ Δ -> ⟦ Γ ⟧ⁿ × R ^ ⟦ Δ ⟧ⁿ̃ -> ⟦ A ⟧
  ⟦ var i ⟧ᵛ = proj₁ ； ⟦ i ⟧ᵐ
  ⟦ lam t ⟧ᵛ = curry′ (shuffle ； ⟦ t ⟧ᵗ)
  ⟦ unit ⟧ᵛ = const tt
  ⟦ pair v w ⟧ᵛ = < ⟦ v ⟧ᵛ , ⟦ w ⟧ᵛ >
  ⟦ inl v ⟧ᵛ = ⟦ v ⟧ᵛ ； inj₁
  ⟦ inr w ⟧ᵛ = ⟦ w ⟧ᵛ ； inj₂

  ⟦_⟧ᵗ : Γ ⊢ᵗ A ∣ Δ -> ⟦ Γ ⟧ⁿ × R ^ ⟦ Δ ⟧ⁿ̃ -> K ⟦ A ⟧
  ⟦ ret v ⟧ᵗ = ⟦ v ⟧ᵛ ； η
  ⟦ μ c ⟧ᵗ = councurry (curry′ ⟦ c ⟧ᶜ)

  ⟦_⟧ᵉ : Γ ∣ A ⊢ᵉ Δ -> ⟦ Γ ⟧ⁿ × R ^ ⟦ Δ ⟧ⁿ̃ -> R ^ ⟦ A ⟧
  ⟦ covar i ⟧ᵉ = proj₂ ； ([ R ]^ ⟦ i ⟧ᵐ̃)
  ⟦ app v e ⟧ᵉ = < ⟦ e ⟧ᵉ , ⟦ v ⟧ᵛ > ； η ； [ R ]^ cbv
  ⟦ fst e ⟧ᵉ = ⟦ e ⟧ᵉ ； curry′ (assocl ； proj₁ ； eval)
  ⟦ snd e ⟧ᵉ = ⟦ e ⟧ᵉ ； curry′ (assocl ； P.map proj₁ id ； eval)
  ⟦ case e1 e2 ⟧ᵉ = < ⟦ e1 ⟧ᵉ , ⟦ e2 ⟧ᵉ > ； uncurry′ S.[_,_]
  ⟦ μ̃ c ⟧ᵉ = curry′ (shuffle ； ⟦ c ⟧ᶜ)
  ⟦ tp ⟧ᵉ = const idf

⟦_⟧ˢ : Sub Γ Δ Γ' -> ⟦ Γ ⟧ⁿ × R ^ ⟦ Δ ⟧ⁿ̃ -> ⟦ Γ' ⟧ⁿ
⟦ sub-ε ⟧ˢ = const tt
⟦ sub-ex θ v ⟧ˢ = < ⟦ θ ⟧ˢ , ⟦ v ⟧ᵛ >

⟦_⟧ᵏ : CoSub Γ Δ Δ' -> ⟦ Γ ⟧ⁿ × R ^ ⟦ Δ ⟧ⁿ̃ -> R ^ ⟦ Δ' ⟧ⁿ̃
⟦ cosub-ε ⟧ᵏ = const λ ()
⟦ cosub-ex φ e ⟧ᵏ env = S.[ ⟦ φ ⟧ᵏ env , ⟦ e ⟧ᵉ env ]

-- coherences

wk-id-coh : ⟦ wk-id {Γ} ⟧ʷ ≡ id
wk-id-coh {ε} = refl
wk-id-coh {Γ ∙ A} rewrite wk-id-coh {Γ} = refl
{-# REWRITE wk-id-coh #-}

wk-id-coh̃ : ⟦ wk-id {Δ} ⟧ʷ̃ ≡ id
wk-id-coh̃ {ε} = funext λ ()
wk-id-coh̃ {Δ ∙ A} = funext λ
  { (inj₁ x) → cong inj₁ (happly wk-id-coh̃ x)
  ; (inj₂ y) → refl
  }
{-# REWRITE wk-id-coh̃ #-}

wk-mem-coh : (π : Γ ⊇ Δ) (i : Δ ∋ A) -> ⟦ wk-mem π i ⟧ᵐ ≡ (⟦ π ⟧ʷ ； ⟦ i ⟧ᵐ)
wk-mem-coh (wk-cong π) z = refl
wk-mem-coh (wk-cong π) (s i) rewrite wk-mem-coh π i = refl
wk-mem-coh (wk-wk π) z rewrite wk-mem-coh π z = refl
wk-mem-coh (wk-wk π) (s i) rewrite wk-mem-coh π (s i) = refl
{-# REWRITE wk-mem-coh #-}

wk-mem-coh̃ : (σ : Δ ⊇ Δ') (i : Δ' ∋ A) -> ⟦ wk-mem σ i ⟧ᵐ̃ ≡ (⟦ i ⟧ᵐ̃ ； ⟦ σ ⟧ʷ̃)
wk-mem-coh̃ (wk-cong σ) z = funext λ a → refl
wk-mem-coh̃ (wk-cong σ) (s i) = funext λ a → cong inj₁ (happly (wk-mem-coh̃ σ i) a)
wk-mem-coh̃ (wk-wk σ) z = funext λ a → cong inj₁ (happly (wk-mem-coh̃ σ z) a)
wk-mem-coh̃ (wk-wk σ) (s i) = funext λ a → cong inj₁ (happly (wk-mem-coh̃ σ (s i)) a)
{-# REWRITE wk-mem-coh̃ #-}

wkenv : Γ ⊇ Γ' -> Δ ⊇ Δ' -> ⟦ Γ ⟧ⁿ × R ^ ⟦ Δ ⟧ⁿ̃ -> ⟦ Γ' ⟧ⁿ × R ^ ⟦ Δ' ⟧ⁿ̃
wkenv ρ σ = P.map ⟦ ρ ⟧ʷ ([ R ]^ ⟦ σ ⟧ʷ̃)

mutual
  wk-cmd-coh : (ρ : Γ ⊇ Γ') (σ : Δ ⊇ Δ') (c : Γ' ⊢ Δ') -> ⟦ wk-cmd ρ σ c ⟧ᶜ ≡ (wkenv ρ σ ； ⟦ c ⟧ᶜ)
  wk-cmd-coh ρ σ (cut A t e) rewrite wk-tm-coh ρ σ t | wk-ctx-coh ρ σ e = refl

  wk-val-coh : (ρ : Γ ⊇ Γ') (σ : Δ ⊇ Δ') (v : Γ' ⊢ᵛ A ∣ Δ') -> ⟦ wk-val ρ σ v ⟧ᵛ ≡ (wkenv ρ σ ； ⟦ v ⟧ᵛ)
  wk-val-coh ρ σ (var i) = refl
  wk-val-coh ρ σ (lam t) rewrite wk-tm-coh (wk-cong ρ) σ t = refl
  wk-val-coh ρ σ unit = refl
  wk-val-coh ρ σ (pair v w) rewrite wk-val-coh ρ σ v | wk-val-coh ρ σ w = refl
  wk-val-coh ρ σ (inl v) rewrite wk-val-coh ρ σ v = refl
  wk-val-coh ρ σ (inr w) rewrite wk-val-coh ρ σ w = refl

  wk-tm-coh : (ρ : Γ ⊇ Γ') (σ : Δ ⊇ Δ') (t : Γ' ⊢ᵗ A ∣ Δ') -> ⟦ wk-tm ρ σ t ⟧ᵗ ≡ (wkenv ρ σ ； ⟦ t ⟧ᵗ)
  wk-tm-coh ρ σ (ret v) rewrite wk-val-coh ρ σ v = refl
  wk-tm-coh ρ σ (μ c) rewrite wk-cmd-coh ρ (wk-cong σ) c =
    funext λ { (γ , k) → funext λ k₂ →
      cong (λ x → ⟦ c ⟧ᶜ (⟦ ρ ⟧ʷ γ , x)) (funext λ { (inj₁ x) → refl ; (inj₂ y) → refl }) }

  wk-ctx-coh : (ρ : Γ ⊇ Γ') (σ : Δ ⊇ Δ') (e : Γ' ∣ A ⊢ᵉ Δ') -> ⟦ wk-ctx ρ σ e ⟧ᵉ ≡ (wkenv ρ σ ； ⟦ e ⟧ᵉ)
  wk-ctx-coh ρ σ (covar i) = refl
  wk-ctx-coh ρ σ (app v e) rewrite wk-val-coh ρ σ v | wk-ctx-coh ρ σ e = refl
  wk-ctx-coh ρ σ (fst e) rewrite wk-ctx-coh ρ σ e = refl
  wk-ctx-coh ρ σ (snd e) rewrite wk-ctx-coh ρ σ e = refl
  wk-ctx-coh ρ σ (case e1 e2) rewrite wk-ctx-coh ρ σ e1 | wk-ctx-coh ρ σ e2 = refl
  wk-ctx-coh ρ σ (μ̃ c) rewrite wk-cmd-coh (wk-cong ρ) σ c = refl
  wk-ctx-coh ρ σ tp = refl

{-# REWRITE wk-val-coh #-}
{-# REWRITE wk-tm-coh #-}
{-# REWRITE wk-ctx-coh #-}
{-# REWRITE wk-cmd-coh #-}

sub-mem-coh : (θ : Sub Γ Δ Γ') (i : Γ' ∋ A) -> ⟦ sub-mem θ i ⟧ᵛ ≡ (⟦ θ ⟧ˢ ； ⟦ i ⟧ᵐ)
sub-mem-coh (sub-ex θ v) z = refl
sub-mem-coh (sub-ex θ v) (s i) rewrite sub-mem-coh θ i = refl
{-# REWRITE sub-mem-coh #-}

cosub-mem-coh : (φ : CoSub Γ Δ Δ') (i : Δ' ∋ A) -> ⟦ cosub-mem φ i ⟧ᵉ ≡ (⟦ φ ⟧ᵏ ； ([ R ]^ ⟦ i ⟧ᵐ̃))
cosub-mem-coh (cosub-ex φ e) z = refl
cosub-mem-coh (cosub-ex φ e) (s i) rewrite cosub-mem-coh φ i = refl
{-# REWRITE cosub-mem-coh #-}

sub-wk-coh : (ρ : Γ₁ ⊇ Γ) (σ : Δ₁ ⊇ Δ) (θ : Sub Γ Δ Γ') -> ⟦ sub-wk ρ σ θ ⟧ˢ ≡ (wkenv ρ σ ； ⟦ θ ⟧ˢ)
sub-wk-coh ρ σ sub-ε = refl
sub-wk-coh ρ σ (sub-ex θ v) rewrite sub-wk-coh ρ σ θ | wk-val-coh ρ σ v = refl
{-# REWRITE sub-wk-coh #-}

cosub-wk-coh : (ρ : Γ₁ ⊇ Γ) (σ : Δ₁ ⊇ Δ) (φ : CoSub Γ Δ Δ') -> ⟦ cosub-wk ρ σ φ ⟧ᵏ ≡ (wkenv ρ σ ； ⟦ φ ⟧ᵏ)
cosub-wk-coh ρ σ cosub-ε = refl
cosub-wk-coh ρ σ (cosub-ex φ e) rewrite cosub-wk-coh ρ σ φ | wk-ctx-coh ρ σ e = refl
{-# REWRITE cosub-wk-coh #-}

sub-id-coh : ⟦ sub-id {Γ} {Δ} ⟧ˢ ≡ proj₁
sub-id-coh {Γ = ε} {Δ} = refl
sub-id-coh {Γ = Γ ∙ A} {Δ} = funext λ
  { ((γ , a) , k) → cong₂ _,_ (happly (sub-id-coh {Γ = Γ} {Δ}) (γ , k)) refl }
{-# REWRITE sub-id-coh #-}

cosub-id-coh : ⟦ cosub-id {Γ} {Δ} ⟧ᵏ ≡ proj₂
cosub-id-coh {Γ} {Δ = ε} = funext λ { (γ , k) → funext λ () }
cosub-id-coh {Γ} {Δ = Δ ∙ A} = funext λ
  { (γ , k) → trans (cong (λ x → S.[ x , k ∘ inj₂ ]) (happly (cosub-id-coh {Γ} {Δ = Δ}) (γ , k ∘ inj₁)))
                    (funext λ { (inj₁ x) → refl ; (inj₂ y) → refl }) }
{-# REWRITE cosub-id-coh #-}

subenv : Sub Γ Δ Γ' -> CoSub Γ Δ Δ' -> ⟦ Γ ⟧ⁿ × R ^ ⟦ Δ ⟧ⁿ̃ -> ⟦ Γ' ⟧ⁿ × R ^ ⟦ Δ' ⟧ⁿ̃
subenv θ φ = < ⟦ θ ⟧ˢ , ⟦ φ ⟧ᵏ >

mutual
  sub-cmd-coh : (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ') (c : Γ' ⊢ Δ') -> ⟦ sub-cmd θ φ c ⟧ᶜ ≡ (subenv θ φ ； ⟦ c ⟧ᶜ)
  sub-cmd-coh θ φ (cut A t e) rewrite sub-tm-coh θ φ t | sub-ctx-coh θ φ e = refl

  sub-val-coh : (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ') (v : Γ' ⊢ᵛ A ∣ Δ') -> ⟦ sub-val θ φ v ⟧ᵛ ≡ (subenv θ φ ； ⟦ v ⟧ᵛ)
  sub-val-coh θ φ (var i) = refl
  sub-val-coh θ φ (lam t) rewrite sub-tm-coh (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var z)) (cosub-wk (wk-wk wk-id) wk-id φ) t = refl
  sub-val-coh θ φ unit = refl
  sub-val-coh θ φ (pair v w) rewrite sub-val-coh θ φ v | sub-val-coh θ φ w = refl
  sub-val-coh θ φ (inl v) rewrite sub-val-coh θ φ v = refl
  sub-val-coh θ φ (inr w) rewrite sub-val-coh θ φ w = refl

  sub-tm-coh : (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ') (t : Γ' ⊢ᵗ A ∣ Δ') -> ⟦ sub-tm θ φ t ⟧ᵗ ≡ (subenv θ φ ； ⟦ t ⟧ᵗ)
  sub-tm-coh θ φ (ret v) rewrite sub-val-coh θ φ v = refl
  sub-tm-coh θ φ (μ c) rewrite sub-cmd-coh (sub-wk wk-id (wk-wk wk-id) θ) (cosub-ex (cosub-wk wk-id (wk-wk wk-id) φ) (covar z)) c = refl

  sub-ctx-coh : (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ') (e : Γ' ∣ A ⊢ᵉ Δ') -> ⟦ sub-ctx θ φ e ⟧ᵉ ≡ (subenv θ φ ； ⟦ e ⟧ᵉ)
  sub-ctx-coh θ φ (covar i) = refl
  sub-ctx-coh θ φ (app v e) rewrite sub-val-coh θ φ v | sub-ctx-coh θ φ e = refl
  sub-ctx-coh θ φ (fst e) rewrite sub-ctx-coh θ φ e = refl
  sub-ctx-coh θ φ (snd e) rewrite sub-ctx-coh θ φ e = refl
  sub-ctx-coh θ φ (case e1 e2) rewrite sub-ctx-coh θ φ e1 | sub-ctx-coh θ φ e2 = refl
  sub-ctx-coh θ φ (μ̃ c) rewrite sub-cmd-coh (sub-ex (sub-wk (wk-wk wk-id) wk-id θ) (var z)) (cosub-wk (wk-wk wk-id) wk-id φ) c = refl
  sub-ctx-coh θ φ tp = refl

{-# REWRITE sub-val-coh #-}
{-# REWRITE sub-tm-coh #-}
{-# REWRITE sub-ctx-coh #-}
{-# REWRITE sub-cmd-coh #-}

-- soundness of the equational theory

mutual
  eqVal : Γ ⊢ᵛ v1 ≈ v2 ∶ A ∣ Δ -> ⟦ v1 ⟧ᵛ ≡ ⟦ v2 ⟧ᵛ
  eqVal ≈-refl = refl
  eqVal (≈-sym p) = sym (eqVal p)
  eqVal (≈-trans p q) = trans (eqVal p) (eqVal q)
  eqVal (lam-cong p) = cong (λ f → curry′ (shuffle ； f)) (eqTm p)
  eqVal (pair-cong p q) = cong₂ <_,_> (eqVal p) (eqVal q)
  eqVal (inl-cong p) = cong (_； inj₁) (eqVal p)
  eqVal (inr-cong p) = cong (_； inj₂) (eqVal p)
  eqVal (unit-eta v) = refl

  eqTm : Γ ⊢ᵗ t1 ≈ t2 ∶ A ∣ Δ -> ⟦ t1 ⟧ᵗ ≡ ⟦ t2 ⟧ᵗ
  eqTm ≈-refl = refl
  eqTm (≈-sym p) = sym (eqTm p)
  eqTm (≈-trans p q) = trans (eqTm p) (eqTm q)
  eqTm (ret-cong p) = cong (_； η) (eqVal p)
  eqTm (μ-cong p) = cong (λ f → councurry (curry′ f)) (eqCmd p)
  eqTm (μ-eta t) = refl

  eqCtx : Γ ∣ e1 ≈ e2 ∶ A ⊢ᵉ Δ -> ⟦ e1 ⟧ᵉ ≡ ⟦ e2 ⟧ᵉ
  eqCtx ≈-refl = refl
  eqCtx (≈-sym p) = sym (eqCtx p)
  eqCtx (≈-trans p q) = trans (eqCtx p) (eqCtx q)
  eqCtx (app-cong p q) = cong (_； η ； [ R ]^ cbv) (cong₂ <_,_> (eqCtx q) (eqVal p))
  eqCtx (fst-cong p) = cong (_； curry′ (assocl ； proj₁ ； eval)) (eqCtx p)
  eqCtx (snd-cong p) = cong (_； curry′ (assocl ； P.map proj₁ id ； eval)) (eqCtx p)
  eqCtx (case-cong p q) = cong (_； uncurry′ S.[_,_]) (cong₂ <_,_> (eqCtx p) (eqCtx q))
  eqCtx (μ̃-cong p) = cong (λ f → curry′ (shuffle ； f)) (eqCmd p)
  eqCtx (μ̃-eta e) = refl

  eqCmd : Γ ⊢ c1 ≈ c2 ⊣ Δ -> ⟦ c1 ⟧ᶜ ≡ ⟦ c2 ⟧ᶜ
  eqCmd ≈-refl = refl
  eqCmd (≈-sym p) = sym (eqCmd p)
  eqCmd (≈-trans p q) = trans (eqCmd p) (eqCmd q)
  eqCmd (cut-cong p q) = cong (_； eval) (cong₂ <_,_> (eqTm p) (eqCtx q))
  eqCmd (μ-beta c e) = refl
  eqCmd (μ̃-beta v c) = refl
  eqCmd (app-beta t v e) = refl
  eqCmd (fst-beta v w e) = refl
  eqCmd (snd-beta v w e) = refl
  eqCmd (inl-beta v e1 e2) = refl
  eqCmd (inr-beta w e1 e2) = refl
