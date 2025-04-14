module Inception.Sub.CPS (R : Set) where

open import Inception.Sub.Syntax

open import Data.Unit
open import Data.Product as P
open import Function as F hiding (_∋_)
open import Data.Sum as S

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
