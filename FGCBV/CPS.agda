module FGCBV.CPS (R : Set) where

open import FGCBV.Syntax

open import Data.Unit
open import Data.Product as P
open import Function as F

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

⟦_⟧ : Ty -> Set
⟦ `Unit ⟧ = ⊤
⟦ A `× B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A `⇒ B ⟧ = ⟦ A ⟧ -> K ⟦ B ⟧

⟦_⟧ˣ : Ctx -> Set
⟦ ε ⟧ˣ = ⊤
⟦ Γ ∙ A ⟧ˣ = ⟦ Γ ⟧ˣ × ⟦ A ⟧

⟦_⟧ʷ : Γ ⊇ Δ -> ⟦ Γ ⟧ˣ -> ⟦ Δ ⟧ˣ
⟦ wk-ε ⟧ʷ = idf
⟦ wk-cong π ⟧ʷ = < proj₁ ； ⟦ π ⟧ʷ , proj₂ >
⟦ wk-wk π ⟧ʷ = proj₁ ； ⟦ π ⟧ʷ

⟦_⟧ᵐ : A ∈ Γ -> ⟦ Γ ⟧ˣ -> ⟦ A ⟧
⟦ h ⟧ᵐ = proj₂
⟦ t x ⟧ᵐ = proj₁ ； ⟦ x ⟧ᵐ

mutual
  ⟦_⟧ᵛ : Γ ⊢ᵛ A -> ⟦ Γ ⟧ˣ -> ⟦ A ⟧  
  ⟦ var i ⟧ᵛ = ⟦ i ⟧ᵐ
  ⟦ letv V W ⟧ᵛ = < idf , ⟦ V ⟧ᵛ > ； ⟦ W ⟧ᵛ
  ⟦ lam M ⟧ᵛ = curry ⟦ M ⟧ᶜ
  ⟦ pair V W ⟧ᵛ = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ >
  ⟦ pm V W ⟧ᵛ = < idf , ⟦ V ⟧ᵛ > ； assocl ； ⟦ W ⟧ᵛ
  ⟦ unit ⟧ᵛ = const tt

  ⟦_⟧ᶜ : Γ ⊢ᶜ A -> ⟦ Γ ⟧ˣ -> K ⟦ A ⟧
  ⟦ produce V ⟧ᶜ = ⟦ V ⟧ᵛ ； η 
  ⟦ letv V M ⟧ᶜ = < idf , ⟦ V ⟧ᵛ > ； ⟦ M ⟧ᶜ 
  ⟦ pm V M ⟧ᶜ = < idf , ⟦ V ⟧ᵛ > ； assocl ； ⟦ M ⟧ᶜ
  ⟦ push M N ⟧ᶜ = < idf , ⟦ M ⟧ᶜ > ； τ ； ⟦ N ⟧ᶜ ♯
  ⟦ app V W ⟧ᶜ = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ > ； uncurry idf

mutual
  interpVal : Γ ⊢ᵛ A -> ⟦ Γ ⟧ˣ -> ⟦ A ⟧
  interpVal (var i) γ =
    ⟦ i ⟧ᵐ γ
  interpVal (letv V W) γ =
    let v = interpVal V γ in
      interpVal W (γ , v)
  interpVal (lam M) γ a = 
    curry (interpComp M) (γ , a)
  interpVal (pair V W) γ =
    interpVal V γ , interpVal W γ
  interpVal (pm V W) γ =
    let v = interpVal V γ in
      interpVal W ((γ , v .proj₁) , v .proj₂)
  interpVal unit γ = tt

  interpComp :  Γ ⊢ᶜ A -> ⟦ Γ ⟧ˣ × (⟦ A ⟧ -> R) -> R
  interpComp (produce V) (γ , k) =
    let v = interpVal V γ in
      k v
  interpComp (letv V M) (γ , k) =
    let v = interpVal V γ in
      interpComp M ((γ , v) , k)
  interpComp (pm V M) (γ , k) =
    let v = interpVal V γ in
      interpComp M (((γ , v .proj₁) , v .proj₂) , k)
  interpComp (push M N) (γ , k) = 
    interpComp M (γ , \a -> 
      interpComp N ((γ , a) , k))
  interpComp (app V W) (γ , k) =
    let v = interpVal V γ in 
      let w = interpVal W γ in 
        (v w) k

⟦_⟧ˢ : Sub Γ Δ -> ⟦ Γ ⟧ˣ -> ⟦ Δ ⟧ˣ
⟦ sub-ε ⟧ˢ = const tt
⟦ sub-ex θ V ⟧ˢ = < ⟦ θ ⟧ˢ , ⟦ V ⟧ᵛ >
