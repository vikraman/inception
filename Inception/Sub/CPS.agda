module Inception.Sub.CPS (R : Set) where

open import Inception.Sub.Syntax

open import Data.Unit
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

K : ∀ {ℓ} -> Set ℓ -> Set ℓ
K X = (X -> R) -> R

infix 5 _♯

_♯ : ∀ {ℓ} {X Y : Set ℓ} -> (X -> K Y) -> K X -> K Y
(f ♯) kx k = kx \x -> f x k

η : ∀ {ℓ} -> {X : Set ℓ} -> X -> K X
η x k = k x

μ : ∀ {ℓ} -> {X : Set ℓ} -> K (K X) -> K X
μ kkx k = kkx \kx -> kx k

τ : ∀ {ℓ} -> {X Y : Set ℓ} -> X × K Y -> K (X × Y)
τ (x , ky) k = ky \z -> k (x , z)

cocurry : ∀ {ℓ} -> {X Y Z : Set ℓ} -> (Z × (X -> R) -> K Y) -> Z -> K (X ⊎ Y)
cocurry f z k = f (z , k ∘ inj₁) (k ∘ inj₂)

varK : ∀ {ℓ} {X : Set ℓ} -> R -> K X
varK = const

subK : ∀ {ℓ} {X : Set ℓ} -> (R -> K X) × K X -> K X
subK (f , n) k = f (n k) k

⟦_⟧ : Ty -> Set
⟦ `Unit ⟧ = ⊤
⟦ A `× B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A `⇒ B ⟧ = ⟦ A ⟧ -> K ⟦ B ⟧
⟦ `V ⟧ = R

⟦_⟧ˣ : Ctx -> Set
⟦ ε ⟧ˣ = ⊤
⟦ Γ ∙ A ⟧ˣ = ⟦ Γ ⟧ˣ × ⟦ A ⟧

⟦_⟧ʷ : Γ ⊇ Δ -> ⟦ Γ ⟧ˣ -> ⟦ Δ ⟧ˣ
⟦ wk-ε ⟧ʷ = idf
⟦ wk-cong π ⟧ʷ = < proj₁ ； ⟦ π ⟧ʷ , proj₂ >
⟦ wk-wk π ⟧ʷ = proj₁ ； ⟦ π ⟧ʷ

⟦_⟧ᵐ : Γ ∋ A -> ⟦ Γ ⟧ˣ -> ⟦ A ⟧
⟦ h ⟧ᵐ = proj₂
⟦ t x ⟧ᵐ = proj₁ ； ⟦ x ⟧ᵐ

mutual
  ⟦_⟧ᵛ : Γ ⊢ᵛ A -> ⟦ Γ ⟧ˣ -> ⟦ A ⟧
  ⟦ var i ⟧ᵛ = ⟦ i ⟧ᵐ
  ⟦ lam M ⟧ᵛ = curry ⟦ M ⟧ᶜ
  ⟦ pair V W ⟧ᵛ = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ >
  ⟦ pm V W ⟧ᵛ = < idf , ⟦ V ⟧ᵛ > ； assocl ； ⟦ W ⟧ᵛ
  ⟦ unit ⟧ᵛ = const tt

  ⟦_⟧ᶜ : Γ ⊢ᶜ A -> ⟦ Γ ⟧ˣ -> K ⟦ A ⟧
  ⟦ return V ⟧ᶜ = ⟦ V ⟧ᵛ ； η
  ⟦ pm V M ⟧ᶜ = < idf , ⟦ V ⟧ᵛ > ； assocl ； ⟦ M ⟧ᶜ
  ⟦ push M N ⟧ᶜ = < idf , ⟦ M ⟧ᶜ > ； τ ； ⟦ N ⟧ᶜ ♯
  ⟦ app V W ⟧ᶜ = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ > ； uncurry idf
  ⟦ var V ⟧ᶜ = ⟦ V ⟧ᵛ ； varK
  ⟦ sub M N ⟧ᶜ = < curry ⟦ M ⟧ᶜ , ⟦ N ⟧ᶜ > ； subK

mutual
  evalVal : Γ ⊢ᵛ A -> ⟦ Γ ⟧ˣ -> ⟦ A ⟧
  evalVal (var i) γ =
    ⟦ i ⟧ᵐ γ
  evalVal (lam M) γ a =
    curry (evalComp M) (γ , a)
  evalVal (pair V W) γ =
    evalVal V γ , evalVal W γ
  evalVal (pm V W) γ =
    let v = evalVal V γ in
      evalVal W ((γ , v .proj₁) , v .proj₂)
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
  evalComp (var V) (γ , k) =
    let v = evalVal V γ in
      v
  evalComp (sub M N) (γ , k) =
    let n = evalComp N (γ , k) in
      evalComp M ((γ , n) , k)

⟦_⟧ˢ : Sub Γ Δ -> ⟦ Γ ⟧ˣ -> ⟦ Δ ⟧ˣ
⟦ sub-ε ⟧ˢ = const tt
⟦ sub-ex θ V ⟧ˢ = < ⟦ θ ⟧ˢ , ⟦ V ⟧ᵛ >

-- coherences
wk-id-coh : ⟦ wk-id {Γ} ⟧ʷ ≡ id
wk-id-coh {ε} = refl
wk-id-coh {Γ ∙ A} rewrite wk-id-coh {Γ} = refl
{-# REWRITE wk-id-coh #-}

wk-mem-coh : (π : Γ ⊇ Δ) (i : Δ ∋ A) -> ⟦ wk-mem π i ⟧ᵐ ≡ (⟦ π ⟧ʷ ； ⟦ i ⟧ᵐ)
wk-mem-coh (wk-cong π) h = refl
wk-mem-coh (wk-cong π) (t i) rewrite wk-mem-coh π i = refl
wk-mem-coh (wk-wk π) h rewrite wk-mem-coh π h = refl
wk-mem-coh (wk-wk π) (t i) rewrite wk-mem-coh π (t i) = refl

mutual
  wk-val-coh : (π : Γ ⊇ Δ) (V : Δ ⊢ᵛ A) -> ⟦ wk-val π V ⟧ᵛ ≡ (⟦ π ⟧ʷ ； ⟦ V ⟧ᵛ)
  wk-val-coh π (var i) rewrite wk-mem-coh π i = refl
  wk-val-coh π (lam M) rewrite wk-comp-coh (wk-cong π) M = refl
  wk-val-coh π (pair V W) rewrite wk-val-coh π V | wk-val-coh π W = refl
  wk-val-coh π (pm V W) rewrite wk-val-coh π V | wk-val-coh (wk-cong (wk-cong π)) W = refl
  wk-val-coh π unit = refl

  wk-comp-coh : (π : Γ ⊇ Δ) (M : Δ ⊢ᶜ A) -> ⟦ wk-comp π M ⟧ᶜ ≡ (⟦ π ⟧ʷ ； ⟦ M ⟧ᶜ)
  wk-comp-coh π (return V) rewrite wk-val-coh π V = refl
  wk-comp-coh π (pm V M) rewrite wk-val-coh π V | wk-comp-coh (wk-cong (wk-cong π)) M = refl
  wk-comp-coh π (push M N) rewrite wk-comp-coh π M | wk-comp-coh (wk-cong π) N = refl
  wk-comp-coh π (app V W) rewrite wk-val-coh π V | wk-val-coh π W = refl
  wk-comp-coh π (var V) rewrite wk-val-coh π V = refl
  wk-comp-coh π (sub M N) rewrite wk-comp-coh (wk-cong π) M | wk-comp-coh π N = refl

{-# REWRITE wk-val-coh #-}
{-# REWRITE wk-comp-coh #-}

sub-mem-coh : (θ : Sub Γ Δ) (i : Δ ∋ A) -> ⟦ sub-mem θ i ⟧ᵛ ≡ (⟦ θ ⟧ˢ ； ⟦ i ⟧ᵐ)
sub-mem-coh (sub-ex θ V) h = refl
sub-mem-coh (sub-ex θ V) (t i) rewrite sub-mem-coh θ i = refl
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
  sub-val-coh θ (lam M) rewrite sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) M = refl
  sub-val-coh θ (pair V W) rewrite sub-val-coh θ V | sub-val-coh θ W = refl
  sub-val-coh θ (pm V M) rewrite sub-val-coh θ V | sub-val-coh (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) M = refl
  sub-val-coh θ unit = refl

  sub-comp-coh : (θ : Sub Γ Δ) (M : Δ ⊢ᶜ A) -> ⟦ sub-comp θ M ⟧ᶜ ≡ (⟦ θ ⟧ˢ ； ⟦ M ⟧ᶜ)
  sub-comp-coh θ (return V) rewrite sub-val-coh θ V = refl
  sub-comp-coh θ (pm V M) rewrite sub-val-coh θ V | sub-comp-coh (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) M = refl
  sub-comp-coh θ (push M N) rewrite sub-comp-coh θ M | sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) N = refl
  sub-comp-coh θ (app V W) rewrite sub-val-coh θ V | sub-val-coh θ W = refl
  sub-comp-coh θ (var V) rewrite sub-val-coh θ V = refl
  sub-comp-coh θ (sub M N) rewrite sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) M | sub-comp-coh θ N = refl

{-# REWRITE sub-val-coh #-}
{-# REWRITE sub-comp-coh #-}

mutual
  eqVal : Γ ⊢ᵛ V ≈ W ∶ A -> ⟦ V ⟧ᵛ ≡ ⟦ W ⟧ᵛ
  eqVal ≈-refl = refl
  eqVal (≈-sym p) = sym (eqVal p)
  eqVal (≈-trans p q) = trans (eqVal p) (eqVal q)
  eqVal (lam-cong p) = cong curry (eqComp p)
  eqVal (pair-cong p q) = cong₂ <_,_> (eqVal p) (eqVal q)
  eqVal (pm-cong p q) rewrite eqVal p | eqVal q = refl
  eqVal (unit-eta _) = refl
  eqVal (pm-beta V1 V2 W) = refl
  eqVal (pm-eta V W) = refl
  eqVal (lam-eta _) = refl

  eqComp : Γ ⊢ᶜ M ≈ N ∶ A -> ⟦ M ⟧ᶜ ≡ ⟦ N ⟧ᶜ
  eqComp ≈-refl = refl
  eqComp (≈-sym p) = sym (eqComp p)
  eqComp (≈-trans p q) = trans (eqComp p) (eqComp q)
  eqComp (return-cong p) rewrite eqVal p = refl
  eqComp (pm-cong p q) rewrite eqVal p | eqComp q = refl
  eqComp (push-cong p q) rewrite eqComp p | eqComp q = refl
  eqComp (app-cong p q) rewrite eqVal p | eqVal q = refl
  eqComp (var-cong p) rewrite eqVal p = refl
  eqComp (sub-cong p q) rewrite eqComp p | eqComp q = refl
  eqComp (pm-beta V1 V2 M) = refl
  eqComp (pm-eta V M) = refl
  eqComp (return-beta V M) = refl
  eqComp (return-eta _) = refl
  eqComp (push-eta M N P) = refl
  eqComp (lam-beta M V) = refl
  eqComp (sub-weak _ N) = refl
  eqComp (sub-subst _) = refl
  eqComp (sub-ext M V) = refl
  eqComp (sub-assoc L M N) = refl
  eqComp (var-push V M) = refl
  eqComp (sub-push M N L) = refl
