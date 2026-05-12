{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.ValueMachine (R : Set) where

open import Agda.Primitive using (Level)

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Function.Base using (const; _∘_; _$_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; cong-app; dcong₂; sym; trans; subst; subst₂)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Unit
open import Data.Nat
open import Data.List using (List; _∷_; []; _++_)

import Relation.Binary.HeterogeneousEquality as H

variable
  X X' Y Y' Z Z' T◾ T◾' : Ty
  Γ' Γ'' Γ''' Δ' : Ctx
  n m n₁ n₂ n₃ n₄ m₁ m₂ m₃ m₄ : ℕ

≤-trans : n₁ ≤ n₂ → n₂ ≤ n₃ → n₁ ≤ n₃
≤-trans {n₁ = zero} {n₂ = n₂} {n₃ = n₃} n₁≤n₂ n₂≤n₃ = z≤n
≤-trans {n₁ = suc n₁} {n₂ = suc n₂} {n₃ = suc n₃} (s≤s n₁≤n₂) (s≤s n₂≤n₃) = s≤s (≤-trans n₁≤n₂ n₂≤n₃)

≤-refl : n ≤ n
≤-refl {n = zero} = z≤n
≤-refl {n = suc n} = s≤s ≤-refl

n≤sn : n ≤ suc n
n≤sn {n = zero} = z≤n
n≤sn {n = suc n} = s≤s n≤sn

n≤sm : n ≤ m → n ≤ suc m
n≤sm {n = zero} {m = zero} n≤m = n≤sn
n≤sm {n = zero} {m = suc m} n≤m = z≤n
n≤sm {n = suc n} {m = suc m} (s≤s n≤m) = s≤s (≤-trans n≤sn (s≤s n≤m))

p≤p : suc n ≤ suc m → n ≤ m
p≤p (s≤s sn≤sm) = sn≤sm

p≤n : suc n ≤ m → n ≤ m
p≤n {m = suc m} (s≤s sn≤m) = n≤sm sn≤m

--pred' : suc n ≤ m → Σ[ p ∈ ℕ ] ( m ≡ suc p )
--pred' {n = n} {m = m} sn≤m = {!sn≤m!}

pred-eq : suc n ≤ m → m ≡ suc (pred m)
pred-eq {n = zero} {m = suc m} sn≤m = refl
pred-eq {n = suc n} {m = suc m} sn≤m = refl

n+z : (n : ℕ) → n + zero ≡ n
n+z zero = refl
n+z (suc n) = cong suc (n+z n)

--{-# REWRITE n+z #-}

-----------------------------------------------------

+-assoc : {n₁ n₂ n₃ : ℕ} → n₁ + n₂ + n₃ ≡ n₁ + (n₂ + n₃)
+-assoc {zero} {n₂} {n₃} = refl
+-assoc {suc n₁} {n₂} {n₃} rewrite +-assoc {n₁} {n₂} {n₃} = refl

+-comm : n + m ≡ m + n
+-comm {n = zero} {m = zero} = refl
+-comm {n = zero} {m = suc m} = cong suc (+-comm {n = zero} {m = m})
+-comm {n = suc n} {m = zero} = cong suc (+-comm {n = n} {m = zero})
+-comm {n = suc n} {m = suc m} rewrite +-comm {n = n} {m = suc m} | +-comm {n = m} {m = suc n} | +-comm {n = m} {m = n} = refl

*-comm : n * m ≡ m * n
*-comm {n = zero} {m = zero} = refl
*-comm {n = zero} {m = suc m} = *-comm {n = zero} {m = m}
*-comm {n = suc n} {m = zero} = *-comm {n = n} {m = zero}
*-comm {n = suc n} {m = suc m}
  rewrite *-comm {n = n} {m = suc m} | *-comm {n = m} {m = suc n}
    | *-comm {n = n} {m = m}
    | sym (+-assoc {n₁ = m} {n₂ = n} {n₃ = m * n})
    | sym (+-assoc {n₁ = n} {n₂ = m} {n₃ = m * n})
    | +-comm {n = n} {m = m}
    = refl

-----------------------------------------------------

+-≤-cong : (n₁ ≤ n₃) → (n₂ ≤ n₄) → (n₁ + n₂ ≤ n₃ + n₄)
+-≤-cong z≤n z≤n = z≤n
+-≤-cong {n₃ = n₃} z≤n (s≤s {m = m} {n = n} n₂≤n₄) rewrite +-comm {n = n₃} {m = suc n} | +-comm {n = n} {m = n₃} = s≤s (+-≤-cong z≤n n₂≤n₄)
+-≤-cong (s≤s n₁≤n₃) n₂≤n₄ = s≤s (+-≤-cong n₁≤n₃ n₂≤n₄)

snm : suc (n + m) ≡ n + (suc m)
snm {n = zero} {m = m} = refl
snm {n = suc n} {m = m} = cong suc snm

+-≤-cong-rev-left : (n + m₁ ≤ n + m₂) → (m₁ ≤ m₂)
+-≤-cong-rev-left {n = zero} m₁≤m₂ = m₁≤m₂
+-≤-cong-rev-left {n = suc n} {m₁ = m₁} {m₂ = m₂} m₁≤m₂ rewrite snm {n = n} {m = m₁} | snm {n = n} {m = m₂} = p≤p (+-≤-cong-rev-left m₁≤m₂)

*-≤-cong : (n₁ ≤ n₃) → (n₂ ≤ n₄) → (n₁ * n₂ ≤ n₃ * n₄)
*-≤-cong z≤n z≤n = z≤n
*-≤-cong z≤n (s≤s n₂≤n₄) = z≤n
*-≤-cong (s≤s {m = m} n₁≤n₃) z≤n rewrite *-comm {n = m} {m = zero} = z≤n
*-≤-cong (s≤s n₁≤n₃) (s≤s n₂≤n₄) = s≤s (+-≤-cong n₂≤n₄ (*-≤-cong n₁≤n₃ (s≤s n₂≤n₄)))

n≤n+m : n ≤ n + m
n≤n+m {n = zero} {m = m} = z≤n
n≤n+m {n = suc n} {m = m} = s≤s n≤n+m

n≤m+n : n ≤ m + n
n≤m+n {n = n} {m = m} rewrite +-comm {n = m} {m = n} = n≤n+m

n*sm≡n+n*m : (n : ℕ) → (m : ℕ) → n * suc m ≡ n + n * m
n*sm≡n+n*m n m rewrite *-comm {n = n} {m = suc m} | *-comm {n = n} {m = m} = refl

n*sm≡n+m*n : (n : ℕ) → (m : ℕ) → n * suc m ≡ n + m * n
n*sm≡n+m*n n m rewrite *-comm {n = n} {m = suc m} = refl

-----------------------------------------------------

module VMain {R₀ : Ty} (k₀ : ⟦ R₀ ⟧ → R) where

  infixl 27 _﹐_
  infixl 27 _﹐﹝_╎_﹞
  infix  26 ⭭_
  infix  26 ⇡_
  infixr 25 _⊲_∷_
  infix  20 ∘_
  infix  20 ∙_
  infixr 17 _→ᵛ⟨_⟩．
  infixr 15 _→ᵛ⟨_⟩_
  infix  15 _→ᵛ_
  infix  15 _→ᴸ_
  infixr 10 _⨾_

  data IsEmpty : Set where
      non-empty : IsEmpty
      empty : IsEmpty

  variable
      b b' : IsEmpty

  data V̲a̲l̲ : Ctx → Ty → Set where

      l̲a̲m̲ : (Γ ∙ X) ⊢ᶜ Y → V̲a̲l̲ Γ (X `⇒ Y)

      pa̲i̲r̲ : V̲a̲l̲ Γ X → V̲a̲l̲ Γ Y → V̲a̲l̲ Γ (X `× Y)

      u̲n̲i̲t̲ : V̲a̲l̲ Γ `Unit

      v̲a̲r̲  : (i : Γ ∋ `V) → V̲a̲l̲ Γ `V

  toVal : V̲a̲l̲ Γ X → Γ ⊢ᵛ X
  toVal (l̲a̲m̲ W) = lam W
  toVal (pa̲i̲r̲ LHS RHS) = pair (toVal LHS) (toVal RHS)
  toVal (u̲n̲i̲t̲) = unit
  toVal (v̲a̲r̲ i) = var i

  wk-v̲a̲l̲ : Wk Γ Δ → V̲a̲l̲ Δ X → V̲a̲l̲ Γ X
  wk-v̲a̲l̲ π (l̲a̲m̲ W) = l̲a̲m̲ ((wk-comp (wk-cong π) W))
  wk-v̲a̲l̲ π (pa̲i̲r̲ LHS RHS) = pa̲i̲r̲ (wk-v̲a̲l̲ π LHS) (wk-v̲a̲l̲ π RHS)
  wk-v̲a̲l̲ π u̲n̲i̲t̲ = u̲n̲i̲t̲
  wk-v̲a̲l̲ π (v̲a̲r̲ i) = v̲a̲r̲ (wk-mem π i)

  wk-comm : {M : V̲a̲l̲ Γ X} → {π : Wk Δ Γ} → wk-val π (toVal M) ≡ toVal (wk-v̲a̲l̲ π M)
  wk-comm {Γ = Γ} {Δ = Δ} {M = l̲a̲m̲ W} {π = π} = refl
  wk-comm {Γ = Γ} {Δ = Δ} {M = pa̲i̲r̲ LHS RHS} {π = π} = trans (cong (λ x → pair x _) wk-comm) ((cong (λ x → pair _ x) wk-comm))
  wk-comm {Γ = Γ} {Δ = Δ} {M = u̲n̲i̲t̲} {π = π} = refl
  wk-comm {Γ = Γ} {Δ = Δ} {M = v̲a̲r̲ i} {π = π} = refl

  wk-v̲a̲l̲-trans : (M : V̲a̲l̲ Γ A) → (π₁ : Wk Ψ Δ) → (π₂ : Wk Δ Γ) → wk-v̲a̲l̲ π₁ (wk-v̲a̲l̲ π₂ M) ≡ wk-v̲a̲l̲ (wk-trans π₁ π₂) M
  wk-v̲a̲l̲-trans (l̲a̲m̲ W) π₁ π₂ = cong l̲a̲m̲ (wk-comp-trans W (wk-cong π₁) (wk-cong π₂))
  wk-v̲a̲l̲-trans (pa̲i̲r̲ M₁ M₂) π₁ π₂ = cong₂ pa̲i̲r̲ (wk-v̲a̲l̲-trans M₁ π₁ π₂) (wk-v̲a̲l̲-trans M₂ π₁ π₂)
  wk-v̲a̲l̲-trans u̲n̲i̲t̲ π₁ π₂ = wk-v̲a̲l̲ π₁ (wk-v̲a̲l̲ π₂ u̲n̲i̲t̲) ∎
  wk-v̲a̲l̲-trans (v̲a̲r̲ i) π₁ π₂ = cong v̲a̲r̲ (wk-mem-trans i π₁ π₂)

  {- NOT TRUE:
  wk-mem-eq : (i : Γ ∋ X) → (π₁ : Wk Ψ Γ) → (π₂ : Wk Ψ Γ) → wk-mem π₁ i ≡ wk-mem π₂ i
  wk-mem-eq Cx.h (wk-cong π₁) (wk-cong π₂) = refl
  wk-mem-eq {Γ = Γ ∙ X} {Ψ = Ψ ∙ X} Cx.h (wk-cong π₁) (wk-wk π₂) =
                wk-mem (wk-cong π₁) h
               ≡⟨ {!!} ⟩
                  {!!}
               ≡⟨ {!!} ⟩
                  {!!}
               ≡⟨ {!!} ⟩
                wk-mem (wk-wk π₂) h ∎
  wk-mem-eq Cx.h (wk-wk π₁) (wk-cong π₂) = {!!}
  wk-mem-eq Cx.h (wk-wk π₁) (wk-wk π₂) = {!!}
  wk-mem-eq (Cx.t i) (wk-cong π₁) (wk-cong π₂) = {!!}
  wk-mem-eq (Cx.t i) (wk-cong π₁) (wk-wk π₂) = {!!}
  wk-mem-eq (Cx.t i) (wk-wk π₁) (wk-cong π₂) = {!!}
  wk-mem-eq (Cx.t i) (wk-wk π₁) (wk-wk π₂) = {!!}

  wk-val-eq : (M : Val Γ A) → (π₁ : Wk Ψ Γ) → (π₂ : Wk Ψ Γ) → wk-val π₁ M ≡ wk-val π₂ M
  wk-val-eq (var i) (wk-cong π₁) (wk-cong π₂) = {!!}
  wk-val-eq (var i) (wk-cong π₁) (wk-wk π₂) = {!!}
  wk-val-eq (var i) (wk-wk π₁) (wk-cong π₂) = {!!}
  wk-val-eq (var i) (wk-wk π₁) (wk-wk π₂) = {!!}
  wk-val-eq (lam W) wk-ε wk-ε = {!!}
  wk-val-eq (lam W) (wk-cong π₁) (wk-cong π₂) = {!!}
  wk-val-eq (lam W) (wk-cong π₁) (wk-wk π₂) = {!!}
  wk-val-eq (lam W) (wk-wk π₁) (wk-cong π₂) = {!!}
  wk-val-eq (lam W) (wk-wk π₁) (wk-wk π₂) = {!!}
  wk-val-eq (pair M₁ M₂) wk-ε wk-ε = {!!}
  wk-val-eq (pair M₁ M₂) (wk-cong π₁) (wk-cong π₂) = {!!}
  wk-val-eq (pair M₁ M₂) (wk-cong π₁) (wk-wk π₂) = {!!}
  wk-val-eq (pair M₁ M₂) (wk-wk π₁) (wk-cong π₂) = {!!}
  wk-val-eq (pair M₁ M₂) (wk-wk π₁) (wk-wk π₂) = {!!}
  wk-val-eq (pm M M₁) wk-ε wk-ε = {!!}
  wk-val-eq (pm M M₁) (wk-cong π₁) (wk-cong π₂) = {!!}
  wk-val-eq (pm M M₁) (wk-cong π₁) (wk-wk π₂) = {!!}
  wk-val-eq (pm M M₁) (wk-wk π₁) (wk-cong π₂) = {!!}
  wk-val-eq (pm M M₁) (wk-wk π₁) (wk-wk π₂) = {!!}
  wk-val-eq unit wk-ε wk-ε = {!!}
  wk-val-eq unit (wk-cong π₁) (wk-cong π₂) = {!!}
  wk-val-eq unit (wk-cong π₁) (wk-wk π₂) = {!!}
  wk-val-eq unit (wk-wk π₁) (wk-cong π₂) = {!!}
  wk-val-eq unit (wk-wk π₁) (wk-wk π₂) = {!!}

  wk-comp-eq : (W : Comp Γ A) → (π₁ : Wk Ψ Γ) → (π₂ : Wk Ψ Γ) → wk-comp π₁ W ≡ wk-comp π₂ W
  wk-comp-eq (return M) wk-ε wk-ε = refl
  wk-comp-eq (return M) (wk-cong π₁) (wk-cong π₂) = cong return (wk-val-eq M (wk-cong π₁) (wk-cong π₂))
  wk-comp-eq (return M) (wk-cong π₁) (wk-wk π₂) = cong return (wk-val-eq M (wk-cong π₁) (wk-wk π₂))
  wk-comp-eq (return M) (wk-wk π₁) (wk-cong π₂) = cong return (wk-val-eq M (wk-wk π₁) (wk-cong π₂))
  wk-comp-eq (return M) (wk-wk π₁) (wk-wk π₂) = cong return (wk-val-eq M (wk-wk π₁) (wk-wk π₂))
  wk-comp-eq (pm M W) wk-ε wk-ε = refl
  wk-comp-eq (pm M W) (wk-cong π₁) (wk-cong π₂) = cong₂ pm (wk-val-eq M (wk-cong π₁) (wk-cong π₂)) (wk-comp-eq W (wk-cong (wk-cong (wk-cong π₁))) (wk-cong (wk-cong (wk-cong π₂))))
  wk-comp-eq (pm M W) (wk-cong π₁) (wk-wk π₂) = cong₂ pm (wk-val-eq M (wk-cong π₁) (wk-wk π₂)) (wk-comp-eq W (wk-cong (wk-cong (wk-cong π₁))) (wk-cong (wk-cong (wk-wk π₂))))
  wk-comp-eq (pm M W) (wk-wk π₁) (wk-cong π₂) = cong₂ pm (wk-val-eq M (wk-wk π₁) (wk-cong π₂)) (wk-comp-eq W (wk-cong (wk-cong (wk-wk π₁))) (wk-cong (wk-cong (wk-cong π₂))))
  wk-comp-eq (pm M W) (wk-wk π₁) (wk-wk π₂) = cong₂ pm (wk-val-eq M (wk-wk π₁) (wk-wk π₂)) (wk-comp-eq W (wk-cong (wk-cong (wk-wk π₁))) (wk-cong (wk-cong (wk-wk π₂))))
  wk-comp-eq (push W₁ W₂) wk-ε wk-ε = cong₂ push (wk-comp-eq W₁ wk-ε wk-ε) (wk-comp-eq W₂ (wk-cong wk-ε) (wk-cong wk-ε))
  wk-comp-eq (push W₁ W₂) (wk-cong π₁) (wk-cong π₂) = cong₂ push (wk-comp-eq W₁ (wk-cong π₁) (wk-cong π₂)) (wk-comp-eq W₂ (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π₂)))
  wk-comp-eq (push W₁ W₂) (wk-cong π₁) (wk-wk π₂) = cong₂ push (wk-comp-eq W₁ (wk-cong π₁) (wk-wk π₂)) (wk-comp-eq W₂ (wk-cong (wk-cong π₁)) (wk-cong (wk-wk π₂)))
  wk-comp-eq (push W₁ W₂) (wk-wk π₁) (wk-cong π₂) = cong₂ push (wk-comp-eq W₁ (wk-wk π₁) (wk-cong π₂)) (wk-comp-eq W₂ (wk-cong (wk-wk π₁)) (wk-cong (wk-cong π₂)))
  wk-comp-eq (push W₁ W₂) (wk-wk π₁) (wk-wk π₂) = cong₂ push (wk-comp-eq W₁ (wk-wk π₁) (wk-wk π₂)) (wk-comp-eq W₂ (wk-cong (wk-wk π₁)) (wk-cong (wk-wk π₂)))
  wk-comp-eq (app M N) wk-ε wk-ε = cong₂ app (wk-val-eq M wk-ε wk-ε) (wk-val-eq N wk-ε wk-ε)
  wk-comp-eq (app M N) (wk-cong π₁) (wk-cong π₂) = cong₂ app (wk-val-eq M (wk-cong π₁) (wk-cong π₂)) (wk-val-eq N (wk-cong π₁) (wk-cong π₂))
  wk-comp-eq (app M N) (wk-cong π₁) (wk-wk π₂) = cong₂ app (wk-val-eq M (wk-cong π₁) (wk-wk π₂)) (wk-val-eq N (wk-cong π₁) (wk-wk π₂))
  wk-comp-eq (app M N) (wk-wk π₁) (wk-cong π₂) = cong₂ app (wk-val-eq M (wk-wk π₁) (wk-cong π₂)) (wk-val-eq N (wk-wk π₁) (wk-cong π₂))
  wk-comp-eq (app M N) (wk-wk π₁) (wk-wk π₂) = cong₂ app (wk-val-eq M (wk-wk π₁) (wk-wk π₂)) (wk-val-eq N (wk-wk π₁) (wk-wk π₂))
  wk-comp-eq (var M) wk-ε wk-ε = refl
  wk-comp-eq (var M) (wk-cong π₁) (wk-cong π₂) = cong var (wk-val-eq M (wk-cong π₁) (wk-cong π₂))
  wk-comp-eq (var M) (wk-cong π₁) (wk-wk π₂) = cong var (wk-val-eq M (wk-cong π₁) (wk-wk π₂))
  wk-comp-eq (var M) (wk-wk π₁) (wk-cong π₂) = cong var (wk-val-eq M (wk-wk π₁) (wk-cong π₂))
  wk-comp-eq (var M) (wk-wk π₁) (wk-wk π₂) = cong var (wk-val-eq M (wk-wk π₁) (wk-wk π₂))
  wk-comp-eq (sub W₁ W₂) wk-ε wk-ε = cong₂ sub (wk-comp-eq W₁ (wk-cong wk-ε) (wk-cong wk-ε)) (wk-comp-eq W₂ wk-ε wk-ε)
  wk-comp-eq (sub W₁ W₂) (wk-cong π₁) (wk-cong π₂) = cong₂ sub (wk-comp-eq W₁ (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π₂))) (wk-comp-eq W₂ (wk-cong π₁) (wk-cong π₂))
  wk-comp-eq (sub W₁ W₂) (wk-cong π₁) (wk-wk π₂) = cong₂ sub (wk-comp-eq W₁ (wk-cong (wk-cong π₁)) (wk-cong (wk-wk π₂))) (wk-comp-eq W₂ (wk-cong π₁) (wk-wk π₂))
  wk-comp-eq (sub W₁ W₂) (wk-wk π₁) (wk-cong π₂) = cong₂ sub (wk-comp-eq W₁ (wk-cong (wk-wk π₁)) (wk-cong (wk-cong π₂))) (wk-comp-eq W₂ (wk-wk π₁) (wk-cong π₂))
  wk-comp-eq (sub W₁ W₂) (wk-wk π₁) (wk-wk π₂) = cong₂ sub (wk-comp-eq W₁ (wk-cong (wk-wk π₁)) (wk-cong (wk-wk π₂))) (wk-comp-eq W₂ (wk-wk π₁) (wk-wk π₂))

  wk-v̲a̲l̲-eq : (M : V̲a̲l̲ Γ A) → (π₁ : Wk Ψ Γ) → (π₂ : Wk Ψ Γ) → wk-v̲a̲l̲ π₁ M ≡ wk-v̲a̲l̲ π₂ M
  wk-v̲a̲l̲-eq (l̲a̲m̲ W) wk-ε wk-ε = refl
  wk-v̲a̲l̲-eq (l̲a̲m̲ W) (wk-cong π₁) (wk-cong π₂) = {!!}
  wk-v̲a̲l̲-eq (l̲a̲m̲ W) (wk-cong π₁) (wk-wk π₂) = {!!}
  wk-v̲a̲l̲-eq (l̲a̲m̲ W) (wk-wk π₁) (wk-cong π₂) = {!!}
  wk-v̲a̲l̲-eq (l̲a̲m̲ W) (wk-wk π₁) (wk-wk π₂) = {!!}
  wk-v̲a̲l̲-eq (pa̲i̲r̲ M₁ M₂) wk-ε wk-ε = refl
  wk-v̲a̲l̲-eq (pa̲i̲r̲ M₁ M₂) (wk-cong π₁) (wk-cong π₂) = {!!}
  wk-v̲a̲l̲-eq (pa̲i̲r̲ M₁ M₂) (wk-cong π₁) (wk-wk π₂) = {!!}
  wk-v̲a̲l̲-eq (pa̲i̲r̲ M₁ M₂) (wk-wk π₁) (wk-cong π₂) = {!!}
  wk-v̲a̲l̲-eq (pa̲i̲r̲ M₁ M₂) (wk-wk π₁) (wk-wk π₂) = {!!}
  wk-v̲a̲l̲-eq u̲n̲i̲t̲ wk-ε wk-ε = refl
  wk-v̲a̲l̲-eq u̲n̲i̲t̲ (wk-cong π₁) (wk-cong π₂) = refl
  wk-v̲a̲l̲-eq u̲n̲i̲t̲ (wk-cong π₁) (wk-wk π₂) = refl
  wk-v̲a̲l̲-eq u̲n̲i̲t̲ (wk-wk π₁) (wk-cong π₂) = refl
  wk-v̲a̲l̲-eq u̲n̲i̲t̲ (wk-wk π₁) (wk-wk π₂) = refl
  wk-v̲a̲l̲-eq (v̲a̲r̲ i) (wk-cong π₁) (wk-cong π₂) = {!!}
  wk-v̲a̲l̲-eq (v̲a̲r̲ i) (wk-cong π₁) (wk-wk π₂) = {!!}
  wk-v̲a̲l̲-eq (v̲a̲r̲ i) (wk-wk π₁) (wk-cong π₂) = {!!}
  wk-v̲a̲l̲-eq (v̲a̲r̲ i) (wk-wk π₁) (wk-wk π₂) = {!!}
  -}

  data Env : (Γ : Ctx) → Set

  data CompStack : (Δ : Ctx) → (X : Ty) → Set

  topCsEnv : CompStack Δ X → Env Δ
  ⟦_⟧ᴱ : (E : Env Γ) → ⟦ Γ ⟧ˣ
  ⟦_⟧ᶜˢ : (cs : CompStack Δ X) → K ⟦ X ⟧ → K ⟦ R₀ ⟧

  data CompStack  where

      ◻     :   CompStack ε R₀

      _⊲_⦂⦂_    : (Γ ∙ Z) ⊢ᶜ X → (γ : Env Γ) → (tail : CompStack Δ X) → {π : Wk Γ Δ} → .{wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv tail ⟧ᴱ} → CompStack Γ Z

  data C̲o̲m̲p : Ctx → Ty → Set
  data C̲o̲m̲p where

      r̲e̲t̲u̲r̲n̲ : V̲a̲l̲ Γ X → C̲o̲m̲p Γ X

      a̲pp    : Γ ⊢ᵛ X `⇒ Y -> V̲a̲l̲ Γ X -> C̲o̲m̲p Γ Y

  toComp :  C̲o̲m̲p Γ X → Γ ⊢ᶜ X
  toComp (r̲e̲t̲u̲r̲n̲ M) = return (toVal M)
  toComp (a̲pp M N) = app M (toVal N)

  wk-c̲o̲m̲p : Wk Γ Δ → C̲o̲m̲p Δ X → C̲o̲m̲p Γ X
  wk-c̲o̲m̲p π (r̲e̲t̲u̲r̲n̲ M) = r̲e̲t̲u̲r̲n̲ (wk-v̲a̲l̲ π M)
  wk-c̲o̲m̲p π (a̲pp M N) = a̲pp (wk-val π M) (wk-v̲a̲l̲ π N)

  data Env where

      ∗       :  Env ε

      _﹐_     :  Env Γ → (M : V̲a̲l̲ Γ X) → Env (Γ ∙ X)

      _﹐﹝_╎_﹞ :  (γ : Env Γ) → (W : Γ ⊢ᶜ X) → (cs : CompStack Δ X) → {π : Wk Γ Δ} → .{wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → Env (Γ ∙ `V)

  variable
      γ  : Env Γ
      γ' : Env Γ'
      γ'' : Env Γ''

  topCsEnv ◻ = ∗
  topCsEnv (W ⊲ γ ⦂⦂ cs) = γ

  ⟦_⟧ᴷ : (cs : CompStack Δ Y) → ⟦ Y ⟧ → R
  ⟦_⟧ᴷ cs y = ⟦ cs ⟧ᶜˢ (η y) k₀

  ⟦ ∗ ⟧ᴱ = tt
  ⟦ E ﹐ M ⟧ᴱ = ⟦ E ⟧ᴱ , ⟦ toVal M ⟧ᵛ ⟦ E ⟧ᴱ
  ⟦ E ﹐﹝ W ╎ cs ﹞ ⟧ᴱ = ⟦ E ⟧ᴱ , ⟦ W ⟧ᶜ ⟦ E ⟧ᴱ ⟦ cs ⟧ᴷ

  ⟦ ◻ ⟧ᶜˢ = idf
  ⟦ W₁ ⊲ γ₁ ⦂⦂ tail ⟧ᶜˢ = < const ⟦ γ₁ ⟧ᴱ , idf > ； τ ； (⟦ W₁ ⟧ᶜ ♯) ； ⟦ tail ⟧ᶜˢ



  -- Lookup Machine
  ------------------------------------------------------------------------------

  data LookupState : Ty → Set where

      ⟨_∥_⟩   :  (i : Γ ∋ X) → Env Γ → LookupState X

  ⟦_⟧ᴸ : (S : LookupState X) → ⟦ X ⟧
  ⟦ ⟨ i ∥ E ⟩ ⟧ᴸ = ⟦ i ⟧ᵐ ⟦ E ⟧ᴱ

  lCtx : (S : LookupState X) → Ctx
  lCtx (⟨_∥_⟩ {Γ = Γ} i E)= Γ

  lTCtx : (S : LookupState X) → Ctx
  lTCtx (⟨_∥_⟩ i ∗) = ε
  lTCtx (⟨_∥_⟩ i (_﹐_ {Γ = Γ} E M)) = Γ
  lTCtx (⟨_∥_⟩ i (_﹐﹝_╎_﹞ {Γ = Γ} E M k)) = Γ

  lEnv : (S : LookupState X) → Env (lCtx S)
  lEnv ⟨ i ∥ E ⟩ = E

  lTEnv : (S : LookupState X) → Env (lTCtx S)
  lTEnv ⟨ i ∥ E ﹐ M ⟩ = E
  lTEnv ⟨ i ∥ E ﹐﹝ M ╎ cs ﹞ ⟩ = E

  data _→ᴸ_ : LookupState X → LookupState X → Set where

      val-h-step    : {E : Env Γ} → {i : Γ ∋ `V} → ⟨ h  ∥ E ﹐ (v̲a̲r̲ i) ⟩ →ᴸ ⟨ i ∥ E ⟩

      val-t-step    : {i : Γ ∋ Y} → {E : Env Γ} → {M : V̲a̲l̲ Γ X} → ⟨ t i  ∥ _﹐_ E M ⟩ →ᴸ ⟨ i ∥ E ⟩

      comp-t-step   : {i : Γ ∋ Y} → {γ : Env Γ} → {W : Γ ⊢ᶜ X} → {cs : CompStack Δ X} → {π : Wk Γ Δ} → .{wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → ⟨ t i  ∥ (_﹐﹝_╎_﹞ γ W cs {π = π} {wk≡ = wk≡}) ⟩ →ᴸ ⟨ i ∥ γ ⟩


  data _→ᴸ*_ : LookupState X → LookupState X → Set where

    _◼ : (S : LookupState X) → S →ᴸ* S

    _→ᴸ⟨_⟩_ : (S : LookupState X) → {S' S'' : LookupState X} → S →ᴸ S' → S' →ᴸ* S'' → S →ᴸ* S''


  data LookupHaltingState : LookupState X → Set where

        found-unit : {γ : Env Γ} → LookupHaltingState ⟨ h ∥ _﹐_ γ u̲n̲i̲t̲ ⟩

        found-pair : {LHS : V̲a̲l̲ Γ X} → {RHS : V̲a̲l̲ Γ Y} → {γ : Env Γ} → LookupHaltingState ⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩

        found-lam : {W : (Γ ∙ X) ⊢ᶜ Y} → {γ : Env Γ} → LookupHaltingState ⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩

        found-comp : {W : Γ ⊢ᶜ X} → {γ : Env Γ} → {cs : CompStack Δ X} → {π : Wk Γ Δ} → .{wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → LookupHaltingState ⟨ h ∥ (_﹐﹝_╎_﹞ γ W cs {π = π} {wk≡ = wk≡}) ⟩

  postulate
    extensionality : ∀ {A B : Set} {f g : A → B}
      → (∀ (x : A) → f x ≡ g x)
        -----------------------
      → f ≡ g

  -- https://stackoverflow.com/questions/56304634/is-functional-extensionality-with-dependent-functions-consistent
  extensionality' : ∀ {A : Set}{B : A → Set}{f g : ∀ a → B a} → (∀ x → f x ≡ g x) → f ≡ g
  extensionality' {A}{B}{f}{g} e =
      H.≅-to-≡ (H.cong (λ f x → proj₂ (f x)) (H.≡-to-≅ (extensionality λ a → cong (a ,_) (e a))))

  ≤-uniq : {n₁ n₂ : ℕ} → (n₁≤n₂ : n₁ ≤ n₂) → (n₁≤n₂' : n₁ ≤ n₂) → n₁≤n₂ ≡ n₁≤n₂'
  ≤-uniq z≤n z≤n = refl
  ≤-uniq (s≤s n₁≤n₂) (s≤s n₁≤n₂') = cong s≤s (≤-uniq n₁≤n₂ n₁≤n₂')

  data ⊥ : Set where

  ql : ⊥ → (A : Set) → A
  ql () b

  wk-prev : Wk (Γ ∙ X) (Δ ∙ Y) → Wk Γ Δ
  wk-prev (wk-cong π) = π
  wk-prev (wk-wk π) = wk-trans π (wk-wk wk-id)

  wk-absurd : Wk Γ (Δ ∙ A) → Wk Δ Γ → ⊥
  wk-absurd {Γ = Γ} {Δ = Δ} (wk-cong π) (wk-cong π') = wk-absurd π π'
  wk-absurd {Γ = Γ} {Δ = Δ} (wk-cong π) (wk-wk π') = wk-absurd (wk-trans π' (wk-wk π)) wk-id
  wk-absurd {Γ = Γ} {Δ = Δ} (wk-wk π) (wk-cong π') = wk-absurd π (wk-wk π')
  wk-absurd {Γ = Γ} {Δ = Δ} (wk-wk π) (wk-wk π') = wk-absurd π (wk-wk (wk-prev {X = R₀} (wk-wk π')))

  wk-id-id : {π : Wk Γ Γ} → π ≡ wk-id
  wk-id-id {π = wk-ε} = refl
  wk-id-id {π = wk-cong π} rewrite wk-id-id {π = π} = refl
  wk-id-id {π = wk-wk π} = ql (wk-absurd π wk-id) (wk-wk π ≡ wk-id)

  p-eq-p : suc n ≡ suc m → n ≡ m
  p-eq-p {n = zero} {m = zero} n≡m = refl
  p-eq-p {n = suc n} {m = suc m} refl = refl

  eq-to-ineq : n ≡ m → n ≤ m
  eq-to-ineq {n = zero} {m = zero} refl = z≤n
  eq-to-ineq {n = zero} {m = suc m} ()
  eq-to-ineq {n = suc n} {m = zero} ()
  eq-to-ineq {n = suc n} {m = suc m} refl = s≤s (eq-to-ineq refl)

  -- Value Machine
  ------------------------------------------------------------------------------

  data BottomTypeEqualsNextType : IsEmpty → Ty → Ty → Set where

      🗆 : BottomTypeEqualsNextType empty X X

      🗇 : BottomTypeEqualsNextType non-empty X Y

  data PartialTerm : (Γ : Ctx) → (X : Ty) → Set where

      ⭭_ : V̲a̲l̲ Γ X → PartialTerm Γ X

      ⇡_ : (M : Γ ⊢ᵛ X) → PartialTerm Γ X

      ⇡ᴹ : (M : Γ ⊢ᵛ X `× Y) → (N : (Γ ∙ X ∙ Y) ⊢ᵛ Z) → PartialTerm Γ Z

      ⇡ᴸ : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → PartialTerm Γ (X `× Y)

      ⇡ᴿ  : (LHS : V̲a̲l̲ Γ X) → (RHS : Γ ⊢ᵛ Y) → PartialTerm Γ (X `× Y)

  wk-v̲a̲l̲-id : (M : V̲a̲l̲ Γ X) → wk-v̲a̲l̲ wk-id M ≡ M
  wk-v̲a̲l̲-id (l̲a̲m̲ M) = cong l̲a̲m̲ (wk-comp-id M)
  wk-v̲a̲l̲-id (pa̲i̲r̲ LHS RHS) = cong₂ pa̲i̲r̲ (wk-v̲a̲l̲-id LHS) (wk-v̲a̲l̲-id RHS)
  wk-v̲a̲l̲-id u̲n̲i̲t̲ = refl
  wk-v̲a̲l̲-id (v̲a̲r̲ i) = cong v̲a̲r̲ (wk-mem-id)

  wk-pt : Wk Γ Δ → PartialTerm Δ X → PartialTerm Γ X
  wk-pt π (⭭ M) = ⭭ (wk-v̲a̲l̲ π M)
  wk-pt π (⇡ M) = ⇡ (wk-val π M)
  wk-pt π (⇡ᴹ M N) = ⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N)
  wk-pt π (⇡ᴸ LHS RHS) = ⇡ᴸ (wk-val π LHS) (wk-val π RHS)
  wk-pt π (⇡ᴿ LHS RHS) = ⇡ᴿ (wk-v̲a̲l̲ π LHS) (wk-val π RHS)

  wk-pt-id : (M : PartialTerm Γ A) → wk-pt wk-id M ≡ M
  wk-pt-id (⭭ M) = cong ⭭_ (wk-v̲a̲l̲-id M)
  wk-pt-id (⇡ M) = cong ⇡_ (wk-val-id M)
  wk-pt-id (⇡ᴹ M N) = cong₂ ⇡ᴹ (wk-val-id M) (wk-val-id N)
  wk-pt-id (⇡ᴸ LHS RHS) = cong₂ ⇡ᴸ (wk-val-id LHS) (wk-val-id RHS)
  wk-pt-id (⇡ᴿ LHS RHS) = cong₂ ⇡ᴿ (wk-v̲a̲l̲-id LHS) (wk-val-id RHS)

  data ValStack : IsEmpty → Ty → Set where

      □ : ValStack empty T◾

      _⊲_∷_ : PartialTerm Γ X → (γ : Env Γ) → (tail : ValStack b T◾) → {↥ : BottomTypeEqualsNextType b X T◾} → ValStack non-empty T◾


  data ValState : Ty → Set where

      ∘_ : ValStack non-empty T◾ → ValState T◾

      ∙_ : ValStack non-empty T◾ → ValState T◾

  lookup-index : {S T : LookupState X} → S →ᴸ* T → (lCtx S) ∋ X
  lookup-index (⟨ i ∥ _ ⟩ ◼) = i
  lookup-index (⟨ h ∥ E ﹐ v̲a̲r̲ i ⟩ →ᴸ⟨ val-h-step ⟩ S→T) = h
  lookup-index (⟨ t i ∥ _ ⟩ →ᴸ⟨ val-t-step ⟩ S→T) = t (lookup-index S→T)
  lookup-index (⟨ t i ∥ _ ⟩ →ᴸ⟨ comp-t-step ⟩ S→T) = t (lookup-index S→T)

  li≡i : {T : LookupState X} {γ : Env Γ} {i : Γ ∋ X} → (S→T : ⟨ i ∥ γ ⟩ →ᴸ* T) → LookupHaltingState T → lookup-index S→T ≡ i
  li≡i (S ◼) found-unit = refl
  li≡i (S ◼) found-pair = refl
  li≡i (S ◼) found-lam = refl
  li≡i (S ◼) found-comp = refl
  li≡i (S →ᴸ⟨ val-t-step ⟩ S→T) found-unit = cong t (li≡i S→T found-unit)
  li≡i (S →ᴸ⟨ comp-t-step ⟩ S→T) found-unit = cong t (li≡i S→T found-unit)
  li≡i (S →ᴸ⟨ val-t-step ⟩ S→T) found-pair = cong t (li≡i S→T found-pair)
  li≡i (S →ᴸ⟨ comp-t-step ⟩ S→T) found-pair = cong t (li≡i S→T found-pair)
  li≡i (S →ᴸ⟨ val-t-step ⟩ S→T) found-lam = cong t (li≡i S→T found-lam)
  li≡i (S →ᴸ⟨ comp-t-step ⟩ S→T) found-lam = cong t (li≡i S→T found-lam)
  li≡i (S →ᴸ⟨ val-h-step ⟩ S→T) found-comp = refl
  li≡i (S →ᴸ⟨ val-t-step ⟩ S→T) (found-comp {wk≡ = wk≡}) = cong t (li≡i S→T (found-comp {wk≡ = wk≡}))
  li≡i (S →ᴸ⟨ comp-t-step ⟩ S→T) (found-comp {wk≡ = wk≡}) = cong t (li≡i S→T (found-comp {wk≡ = wk≡}))

  data _↠ᵛ_ : ValState T◾ → ValState T◾ → Set

  data _→ᵛ_ : ValState T◾ → ValState T◾ → Set where

      ∘var-c  :    {i : Γ ∋ `V} → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b `V T◾}
                ----------------------------------------------------------------
                  → ∘ ((⇡ var i ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((⭭ v̲a̲r̲ i ⊲ γ ∷ tail) {↥ = ↥})

      ∘var    :    {i : Γ ∋ X} → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b X T◾}
                  → {M : V̲a̲l̲ Γ' X}
                  → (i>>T : (⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ (γ' ﹐ M) ⟩)) → (πᵥ : Wk Γ Γ')
                  -- not needed for correctness, but makes things easier:
                  -- → EnvExt (lookup-index i>>T) γ (γ' ﹐ M)
                  -- → WkExt πᵥ
                  -- → EnvEq πᵥ γ γ'
                  → LookupHaltingState ⟨ h ∥ (γ' ﹐ M) ⟩
                ----------------------------------------------------------------
                  --→ ∘ ((⇡ var i ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((⭭ (wk-v̲a̲l̲ πᵥ M) ⊲ γ ∷ tail) {↥ = ↥})
                  → ∘ ((⇡ var i ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((⭭ M ⊲ γ' ∷ tail) {↥ = ↥}) -- garbage collection step


      ∘lam   :  {M : (Γ ∙ X) ⊢ᶜ Y} → {γ  : Env Γ}
              → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b (X `⇒ Y) T◾}
                ---------------------------------------------------------------------------
              →     ∘ ((⇡ lam M ⊲ γ ∷ tail) {↥ = ↥})
                  →ᵛ ∙ ((⭭ l̲a̲m̲ M ⊲ γ ∷ tail) {↥ = ↥})

      ∘pair  :  {LHS : Γ ⊢ᵛ X} → {RHS : Γ ⊢ᵛ Y}
              → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b (X `× Y) T◾}
                ---------------------------------------------------------------------------
              →     ∘ ((⇡ pair LHS RHS ⊲ γ ∷ tail) {↥ = ↥})
                  →ᵛ ∘ ((⇡ LHS ⊲ γ ∷ ((⇡ᴸ LHS RHS ⊲ γ ∷ tail) {↥ = ↥})) {↥ = 🗇})

      ∘pm    :  {M : Γ ⊢ᵛ X `× Y} → {N : (Γ ∙ X ∙ Y) ⊢ᵛ Z}
              → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b Z T◾}
                ---------------------------------------------------------------------------
              →     ∘ ((⇡ pm M N ⊲ γ ∷ tail) {↥ = ↥})
                  →ᵛ ∘ ((⇡ M ⊲ γ ∷ (⇡ᴹ M N ⊲ γ ∷ tail) {↥ = ↥}) {↥ = 🗇})

      ∘unit  :  {γ  : Env Γ}
              → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b `Unit T◾}
                ---------------------------------------------------------------------------
              →     ∘ ((⇡ unit ⊲ γ ∷ tail) {↥ = ↥})
                  →ᵛ ∙ ((⭭ u̲n̲i̲t̲ ⊲ γ ∷ tail) {↥ = ↥})

      ∙M∷l   :  {M : V̲a̲l̲ Γ X} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y} → {π' : Wk Γ Γ'}
              → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b (X `× Y) T◾}
              -- not needed for correctness, but makes things easier  --→ (LHS→M : (∘ (⇡ LHS ⊲ γ' ∷ □) {↥ = 🗆}) ↠ᵛ (∙ (⭭ M ⊲ γ ∷ □) {↥ = 🗆}))
              → (π≡ : ⟦ γ' ⟧ᴱ ≡ ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ)
              → (LHS≡M : ⟦ LHS ⟧ᵛ ⟦ γ' ⟧ᴱ ≡ ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ)
                ---------------------------------------------------------------------------
              →     ∙ ((⭭ M ⊲ γ ∷ ((⇡ᴸ LHS RHS ⊲ γ' ∷ tail) {↥ = ↥})) {↥ = 🗇})
                  →ᵛ ∘ ((⇡ wk-val π' RHS ⊲ γ ∷ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ tail) {↥ = ↥})) {↥ = 🗇})

      ∙M∷r   :  {M : V̲a̲l̲ Γ Y} → {LHS : V̲a̲l̲ Γ' X} → {RHS : Γ' ⊢ᵛ Y} {π' : Wk Γ Γ'}
              → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b (X `× Y) T◾}
              -- not needed for correctness, but makes things easier
              → (π≡ : ⟦ γ' ⟧ᴱ ≡ ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ)
              → (RHS≡M : ⟦ RHS ⟧ᵛ ⟦ γ' ⟧ᴱ ≡ ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ)
                ---------------------------------------------------------------------------
              →     ∙ ((⭭ M ⊲ γ ∷ ((⇡ᴿ LHS RHS ⊲ γ' ∷ tail) {↥ = ↥})) {↥ = 🗇})
                  →ᵛ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M ⊲ γ ∷ tail) {↥ = ↥})

      ∙pair∷pm  :  {LHS : V̲a̲l̲ Γ X} → {RHS : V̲a̲l̲ Γ Y} → {M : Γ' ⊢ᵛ X `× Y} → {N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z}
              → {π' : Wk Γ Γ'}
              → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b Z T◾}
              -- not needed for correctness, but makes things easier
              →  (π≡ : ⟦ γ' ⟧ᴱ ≡ ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ)
              →  (p₁M≡LHS : proj₁ (⟦ M ⟧ᵛ ⟦ γ' ⟧ᴱ) ≡ ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ)
              →  (p₂M≡RHS : proj₂ (⟦ M ⟧ᵛ ⟦ γ' ⟧ᴱ) ≡ ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ)
                ---------------------------------------------------------------------------
              →     ∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ ∷ ((⇡ᴹ M N ⊲ γ' ∷ tail) {↥ = ↥})) {↥ = 🗇})
                  →ᵛ  ∘ ((⇡ (wk-val (wk-cong (wk-cong π')) N) ⊲ γ ﹐ LHS ﹐ (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ∷ tail) {↥ = ↥})

  --data _↠ᵛ_ : ValState T◾ → ValState T◾ → Set where
  data _↠ᵛ_ where

    _→ᵛ⟨_⟩． : (S : ValState T◾) → {S' : ValState T◾} → (laststep : S →ᵛ S') → S ↠ᵛ S'

    _→ᵛ⟨_⟩_ : (S : ValState T◾) → {S' S'' : ValState T◾} → S →ᵛ S' → S' ↠ᵛ S'' → S ↠ᵛ S''

  _⨾_ : {F S T : ValState T◾} → (F ↠ᵛ S) → (S ↠ᵛ T) → (F ↠ᵛ T)
  _⨾_ (F →ᵛ⟨ F>S ⟩．) S>>T = F →ᵛ⟨ F>S ⟩ S>>T
  _⨾_ (F →ᵛ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᵛ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ S₂>>T)

  _⧺_ : ValStack b T◾ → ValStack non-empty T◾' → ValStack non-empty T◾'
  □ ⧺ lower = lower
  (M ⊲ γ ∷ upper) ⧺ lower = (M ⊲ γ ∷ (upper ⧺ lower)) {↥ = 🗇}

  _⧻_ : (upper : ValState T◾) → ValStack non-empty T◾' → ValState T◾'
  (∘ upper) ⧻ lower = ∘ (upper ⧺ lower)
  (∙ upper) ⧻ lower = ∙ (upper ⧺ lower)

  ⟨_⟩⧻_ : {from : ValState T◾} → {to : ValState T◾} → (F>T : from →ᵛ to) → (tail : ValStack non-empty T◾') → (from ⧻ tail) →ᵛ (to ⧻ tail)
  ⟨ ∘var-c ⟩⧻ tail = ∘var-c
  -- ⟨ ∘var T>>U π ext we ϖ H ⟩⧻ tail = ∘var T>>U π ext we ϖ H
  ⟨ ∘var T>>U π H ⟩⧻ tail = ∘var T>>U π H
  ⟨ ∘lam ⟩⧻ tail = ∘lam
  ⟨ ∘pair ⟩⧻ tail = ∘pair
  ⟨ ∘pm ⟩⧻ tail = ∘pm
  ⟨ ∘unit ⟩⧻ tail = ∘unit
  ⟨ ∙pair∷pm π≡ L R ⟩⧻ tail = ∙pair∷pm π≡ L R
  ⟨ ∙M∷l π≡ LHS≡M ⟩⧻ tail = ∙M∷l π≡ LHS≡M
  ⟨ ∙M∷r π≡ RHS≡M ⟩⧻ tail = ∙M∷r π≡ RHS≡M

  ⟪_⟫⧻_ : {from : ValState T◾} → {to : ValState T◾} → (F>T : from ↠ᵛ to) → (tail : ValStack non-empty T◾') → (from ⧻ tail) ↠ᵛ (to ⧻ tail)
  ⟪ _ →ᵛ⟨ F>T ⟩． ⟫⧻ tail =  _ →ᵛ⟨ ⟨ F>T ⟩⧻ tail ⟩．
  ⟪ _ →ᵛ⟨ F>T ⟩ F>>T ⟫⧻ tail =   _ →ᵛ⟨ ⟨ F>T ⟩⧻ tail ⟩ (⟪ F>>T ⟫⧻ tail)

  ⟦_⟧ᵛˢ : (S : ValStack non-empty T◾) → ⟦ T◾ ⟧
  ⟦ (⭭ x ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ toVal x ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⇡ M ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ M ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⇡ᴹ M N ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ pm M N ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⇡ᴸ LHS RHS ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ pair LHS RHS ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⇡ᴿ LHS RHS ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ pair (toVal LHS) RHS ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⭭ x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ
  ⟦ (⇡ M ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ
  ⟦ (⇡ᴹ M N ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ
  ⟦ (⇡ᴸ LHS RHS ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ
  ⟦ (⇡ᴿ LHS RHS ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ


  ⟦_⟧ᵛꟴ : (S : ValState T◾) → ⟦ T◾ ⟧
  ⟦ ∘ tail ⟧ᵛꟴ = ⟦ tail ⟧ᵛˢ
  ⟦ ∙ tail ⟧ᵛꟴ = ⟦ tail ⟧ᵛˢ

  topStackCtx : (S : ValStack non-empty T◾) → Ctx
  topStackCtx (_⊲_∷_ {Γ = Γ} _ _ _) = Γ

  topCtx : ValState T◾ → Ctx
  topCtx (∘ S) = topStackCtx S
  topCtx (∙ S) = topStackCtx S

  topStackEnv : (S : ValStack non-empty T◾) → Env (topStackCtx S)
  topStackEnv (_⊲_∷_ _ γ _) = γ

  topEnv : (S : ValState T◾) → Env (topCtx S)
  topEnv (∘ S) = topStackEnv S
  topEnv (∙ S) = topStackEnv S

  data ValHaltingState : ValState T◾ → Set where

      ∙_⊲_■ : (M : V̲a̲l̲ Γ X) → (γ : Env Γ) → ValHaltingState (∙ ((⭭ M ⊲ γ ∷ □) {↥ = 🗆}))

  botStackCtx : ValStack non-empty T◾ → Ctx
  botStackCtx ((_⊲_∷_) {Γ = Γ} _ _ □) = Γ
  botStackCtx ((x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})) {↥ = ↥}) = botStackCtx ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})

  botCtx : ValState T◾ → Ctx
  botCtx (∘ S) = botStackCtx S
  botCtx (∙ S) = botStackCtx S

  botStackEnv : (S : ValStack non-empty T◾) → Env (botStackCtx S)
  botStackEnv ((_⊲_∷_) {Γ = Γ} _ γ □) = γ
  botStackEnv ((x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})) {↥ = ↥}) = botStackEnv ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})

  botEnv : (S : ValState T◾) → Env (botCtx S)
  botEnv (∘ S) = botStackEnv S
  botEnv (∙ S) = botStackEnv S

  botStackTerm : (S : ValStack non-empty T◾) → PartialTerm (botStackCtx S) (T◾)
  botStackTerm ((_⊲_∷_) {Γ = Γ} M γ □ {↥ = 🗆}) = M
  botStackTerm ((x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})) {↥ = ↥}) = botStackTerm ((x₁ ⊲ γ₁ ∷ xs) {↥ = ↥'})

  -- botTerm : (S : ValState T◾) → PartialTerm (botCtx S) (T◾)
  -- botTerm (∘ S) = botStackTerm S
  -- botTerm (∙ S) = botStackTerm S

  haltingTerm : {S : ValState T◾} → (ValHaltingState S) → V̲a̲l̲ (botCtx S) (T◾)
  haltingTerm ∙ M ⊲ γ ■ = M


{-
  -- EXAMPLES
  --------------------------------------------------

  ex1 : ε ⊢ᵛ `Unit
  ex1 = pm (pair unit unit) (var (t h))

  ex2 : ε ⊢ᵛ `Unit `× `Unit
  ex2 = pm (pm (pair (lam {A = `Unit} {B = `Unit} (return (var h))) unit) (pair unit (var (t h)))) (pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))))

  ---------------------------------------

  -- call agda2-compute-normalised in the hole below
  -- _ : val-eval ex2 ≡ {!val-eval ex2!}
  -- _ = refl

  --------------------------------------------------------------

  -- This is not used anywhere, but shows that the interpretations of environments and computation stacks respect the cps translation of sub

  sub-cps : (M : (Γ ∙ `V) ⊢ᶜ X) → (N : Γ ⊢ᶜ X) → (γ : ⟦ Γ ⟧ˣ ) → (k : ⟦ X ⟧ → R) → ⟦ sub M N ⟧ᶜ γ k ≡ ⟦ M ⟧ᶜ ( γ , ⟦ N ⟧ᶜ γ k ) k
  sub-cps M N γ k = refl

  sub-cps' : (M : (Γ ∙ `V) ⊢ᶜ X) → (N : Γ ⊢ᶜ X) → (γ : Env Γ) → (cs : CompStack Δ X) → (πₓ : Wk Γ Δ) → (wk≡ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → ⟦ sub M N ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ ≡ ⟦ M ⟧ᶜ ⟦ (γ ﹐﹝ N ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡} ⟧ᴱ ⟦ cs ⟧ᴷ
  sub-cps' M N γ cs πₓ wk≡ = refl
-}


  --{-# REWRITE wk-v̲a̲l̲-id #-}

  wk-comm-explicit : (M : V̲a̲l̲ Γ X) → (π : Wk Δ Γ) → toVal (wk-v̲a̲l̲ π M) ≡ wk-val π (toVal M)
  wk-comm-explicit M π = sym wk-comm

  {-# REWRITE wk-comm-explicit #-}

-----------------------
  -- dcong₂' : {a b c : Level} → ∀ {A : Set a} {B : A → Set b} {C : Set c}
  --         (f : (x : A) → .(B x) → C) {x₁ x₂} .{y₁ y₂}
  --       → (p : x₁ ≡ x₂) → .({!subst B p y₁ ≡ y₂!}) --subst B p y₁ ≡ y₂
  --       → f x₁ y₁ ≡ f x₂ y₂
  -- dcong₂' f refl _ = refl

  -- rewrite-comp-env : (γ : Env Γ) (W W' : Γ ⊢ᶜ X) → (cs : CompStack Δ X) → {π π' : Wk Γ Δ} → {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
  --                    → (Wπ≡Wπ' : (W , π) ≡ (W' , π'))
  --                    → (γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡} ≡ (γ ﹐﹝ W' ╎ cs ﹞) {π = π'} {wk≡ = subst (λ x → ⟦ proj₂ x ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) Wπ≡Wπ' wk≡}
  -- rewrite-comp-env γ W W' cs {wk≡ = wk≡} Wπ≡Wπ' = dcong₂ (λ x y → (γ ﹐﹝ proj₁ x ╎ cs ﹞) {π = proj₂ x} {wk≡ = y} ) {y₁ = wk≡} Wπ≡Wπ' refl

  wk-assoc : {π₁ : Wk Γ Γ'} {π₂ : Wk Γ' Γ''} {π₃ : Wk Γ'' Γ'''} → wk-trans π₁ (wk-trans π₂ π₃) ≡ wk-trans (wk-trans π₁ π₂) π₃
  wk-assoc {π₁ = wk-ε} {π₂ = π₂} {π₃ = π₃} = refl
  wk-assoc {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {π₃ = wk-cong π₃} = cong wk-cong (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
  wk-assoc {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {π₃ = wk-wk π₃} = cong wk-wk (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
  wk-assoc {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {π₃ = π₃} = cong wk-wk (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
  wk-assoc {π₁ = wk-wk π₁} {π₂ = π₂} {π₃ = π₃} = cong wk-wk (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})

  -- proj₁-eq : {A B : Set} {a₁ a₂ : A} {b₁ b₂ : B} → (a₁ , b₁) ≡ (a₂ , b₂) → a₁ ≡ a₂
  -- proj₁-eq refl = refl

  dcong₂-irr : {a b c : Level} → ∀ {A : Set a} {B : A → Set b} {C : Set c}
              (f : (x : A) → .(B x) → C) {x₁ x₂} .{y₁ y₂}
            → (p : x₁ ≡ x₂)
            → f x₁ y₁ ≡ f x₂ y₂
  dcong₂-irr f refl = refl

  pair-eq : {A B : Set} {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ≡ a₂ → b₁ ≡ b₂ → (a₁ , b₁) ≡ (a₂ , b₂)
  pair-eq a₁≡a₂ b₁≡b₂ = cong₂ (λ x y → x , y) a₁≡a₂ b₁≡b₂

  --------

  data EnvExt : (i : Γ ∋ X) → (γ : Env Γ) → (γ' : Env Γ') → Set where

    env-val : {M : V̲a̲l̲ Γ X} → EnvExt h (γ ﹐ M) (γ ﹐ M)

    env-comp : {W : Γ ⊢ᶜ X} {cs : CompStack Δ X} {π : Wk Γ Δ} .{wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → EnvExt h ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡})

    ext-val : {γ : Env Γ} {γ' : Env Γ'} {M : V̲a̲l̲ Γ Y} {i : Γ ∋ X} → EnvExt i γ γ' → EnvExt (t i) (γ ﹐ M) γ'

    ext-comp : {γ : Env Γ} {γ' : Env Γ'} {W : Γ ⊢ᶜ Y} {cs : CompStack Δ Y} {π : Wk Γ Δ} .{wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} {i : Γ ∋ X} → EnvExt i γ γ' → EnvExt (t i) ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) γ'

    ext-jmp : {γ : Env Γ} {γ' : Env Γ'} {i : Γ ∋ `V} → EnvExt i γ γ' → EnvExt h (γ ﹐ v̲a̲r̲ i) γ'

  data EnvEq : (π : Wk Γ' Γ) → (γ' : Env Γ') → (γ : Env Γ) → Set where

    wk-env-ε    : EnvEq wk-ε ∗ ∗

    wk-env-val-cong : {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ} → (M : V̲a̲l̲ Γ X) → EnvEq π γ' γ → EnvEq (wk-cong π) (γ' ﹐ wk-v̲a̲l̲ π M) (γ ﹐ M)

    wk-env-comp-cong : {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ}
                       → (W : Γ ⊢ᶜ X) → (cs : CompStack Δ X) → {πᶜ : Wk Γ Δ} → .{wk≡ : ⟦ πᶜ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → .{wk≡' : ⟦ wk-trans π πᶜ ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → EnvEq π γ' γ
                       → EnvEq (wk-cong π) ((γ' ﹐﹝ wk-comp π W ╎ cs ﹞) {π = wk-trans π πᶜ}
                               {wk≡ = wk≡'})
                               ((γ ﹐﹝ W ╎ cs ﹞) {π = πᶜ} {wk≡ = wk≡})

    wk-env-val-wk : {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ} → (M : V̲a̲l̲ Γ' X) → EnvEq π γ' γ → EnvEq (wk-wk π) (γ' ﹐ M) γ

    wk-env-comp-wk : {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ}
                       → (W : Γ' ⊢ᶜ X) → (cs : CompStack Δ X) → {πᶜ' : Wk Γ' Δ}
                       → .{wk≡' : ⟦ πᶜ' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → EnvEq π γ' γ
                       → EnvEq (wk-wk π) ((γ' ﹐﹝ W ╎ cs ﹞) {π = πᶜ'}
                               {wk≡ = wk≡'})
                               γ

  data WkExt : Wk Γ Δ → Set where

    wk-eq : (π : Wk Γ Γ) → WkExt π

    wk-ext : (π : Wk Γ Δ) → WkExt π → WkExt (wk-wk {A = A} π)


  enveq-id : {γ : Env Γ} → EnvEq wk-id γ γ
  enveq-id {γ = ∗} = wk-env-ε
  enveq-id {γ = γ ﹐ M} = subst (λ x → EnvEq (wk-cong wk-id) (γ ﹐ x) (γ ﹐ M)) (wk-v̲a̲l̲-id M) (wk-env-val-cong M enveq-id ) --wk-env-val-cong M enveq-id
  enveq-id {γ = (_﹐﹝_╎_﹞) {Γ = Γ} {Δ = Δ} γ W cs {π = π} {wk≡ = wk≡}} =
            let
              W≡ = wk-comp-id W
              π≡ = wk-trans-id {π = π}

              a0 = wk-env-comp-cong {π = wk-id} {γ' = γ} {γ = γ} W cs {πᶜ = π} {wk≡ = wk≡} {wk≡' = subst (λ x → ⟦ proj₂ x ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) (sym (pair-eq W≡ π≡)) wk≡} (enveq-id {γ = γ})

              eq1 : ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) ≡ ((γ ﹐﹝ wk-comp wk-id W ╎ cs ﹞) {π = wk-trans wk-id π} {wk≡ = subst (λ x → ⟦ proj₂ x ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) (sym (pair-eq W≡ π≡)) wk≡})
              eq1 = dcong₂-irr ((λ x z → (γ ﹐﹝ proj₁ x ╎ cs ﹞) {π = proj₂ x} {wk≡ = z})) (sym (pair-eq W≡ π≡))

              goal : EnvEq (wk-cong {A = `V} wk-id) ((γ ﹐﹝ W ╎ cs ﹞) {π} {wk≡}) ((γ ﹐﹝ W ╎ cs ﹞) {π} {wk≡})
              goal =  subst (λ x → EnvEq (wk-cong {A = `V} wk-id) x ((γ ﹐﹝ W ╎ cs ﹞) {π} {wk≡}) ) (sym eq1) a0
            in
            goal

  env-id : {γ γ' : Env Γ} → EnvEq wk-id γ γ' → γ ≡ γ'
  env-id {γ = γ} {γ' = γ'} wk-env-ε = refl
  env-id {γ = γ ﹐ _} {γ' = γ' ﹐ M} (wk-env-val-cong M ϖ) = cong₂ (λ x y → x ﹐ y) (env-id ϖ) (wk-v̲a̲l̲-id M)
  env-id {γ = (γ ﹐﹝ _ ╎ _ ﹞) {π = π'} {wk≡ = wk≡'}} {γ' = (γ' ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}} (wk-env-comp-cong W cs ϖ) = --{!!}
              let
                γ≡ = env-id ϖ
                π≡ : wk-trans wk-id π ≡ π
                π≡ = wk-trans-id
                W≡ : wk-comp wk-id W ≡ W
                W≡ = wk-comp-id W

                goal : γ ﹐﹝ wk-comp wk-id W ╎ cs ﹞ ≡ γ' ﹐﹝ W ╎ cs ﹞
                goal = dcong₂-irr ((λ x z → ((proj₁ x) ﹐﹝ proj₁ (proj₂ x) ╎ cs ﹞) {π = proj₂ (proj₂ x)} {wk≡ = z})) {y₁ = wk≡'} {y₂ = wk≡} (pair-eq γ≡ (pair-eq W≡ π≡))
              in
              goal


  wk-ext-trans : {π₁ : Wk Γ Δ} {π₂ : Wk Δ Ψ} → WkExt π₁ → WkExt π₂ → WkExt (wk-trans π₁ π₂)
  wk-ext-trans (wk-eq π₁) (wk-eq π₂) = wk-eq (wk-trans π₁ π₂)
  wk-ext-trans (wk-eq π₁) (wk-ext {A = A} π₂ we₂) =
               let
                 a0 : WkExt (wk-wk {A = A} π₂)
                 a0 = wk-ext π₂ we₂
                 a1 : WkExt (wk-trans wk-id (wk-wk {A = A} π₂))
                 a1 = subst (λ x → WkExt x) (sym wk-trans-id) a0
                 a2 : WkExt (wk-trans π₁ (wk-wk {A = A} π₂))
                 a2 = subst (λ x → WkExt (wk-trans x (wk-wk {A = A} π₂))) (sym wk-id-id) a1
               in
               a2
  wk-ext-trans (wk-ext π₁ we₁) (wk-eq π₂) = wk-ext (wk-trans π₁ π₂) (wk-ext-trans we₁ (wk-eq π₂))
  wk-ext-trans (wk-ext π₁ we₁) (wk-ext π₂ we₂) = wk-ext (wk-trans π₁ (wk-wk π₂)) (wk-ext-trans we₁ (wk-ext π₂ we₂))

  wk-ext-cong-lift : {π : Wk Γ Δ} → WkExt (wk-cong {A = A} π) → WkExt π
  wk-ext-cong-lift (wk-eq π) = wk-eq _

  wk-ext-wk-lift : {π : Wk Γ Δ} → WkExt (wk-wk {A = A} π) → WkExt π
  wk-ext-wk-lift (wk-eq (wk-wk π)) = ql (wk-absurd π wk-id) (WkExt π)
  wk-ext-wk-lift (wk-ext π we) = we


  env-eq-trans : {π₁ : Wk Γ Γ'} {π₂ : Wk Γ' Γ''} {γ : Env Γ} {γ' : Env Γ'} {γ'' : Env Γ''}
                 → WkExt π₁ → WkExt π₂ → EnvEq π₁ γ γ' → EnvEq π₂ γ' γ'' → EnvEq (wk-trans π₁ π₂) γ γ''
  env-eq-trans {π₁ = wk-ε} {π₂ = π₂} {γ = γ} {γ' = γ'} {γ'' = γ''} (wk-eq π) we₂ wk-env-ε ϖ₂ = ϖ₂
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {γ = γ ﹐ _} {γ' = γ' ﹐ M} {γ'' = γ'' ﹐ M₁} we₁ we₂ (wk-env-val-cong M ϖ₁) (wk-env-val-cong M₁ ϖ₂) =
               let
                 a0 = env-eq-trans (wk-ext-cong-lift we₁) (wk-ext-cong-lift we₂) ϖ₁ ϖ₂
                 a1 : EnvEq (wk-cong (wk-trans π₁ π₂)) (γ ﹐ wk-v̲a̲l̲ (wk-trans π₁ π₂) M₁) (γ'' ﹐ M₁)
                 a1 = wk-env-val-cong M₁ a0
                 a2 : EnvEq (wk-cong (wk-trans π₁ π₂)) (γ ﹐ wk-v̲a̲l̲ π₁ (wk-v̲a̲l̲ π₂ M₁)) (γ'' ﹐ M₁)
                 a2 = subst (λ x → EnvEq (wk-cong (wk-trans π₁ π₂)) (γ ﹐ x) (γ'' ﹐ M₁)) (sym (wk-v̲a̲l̲-trans M₁ π₁ π₂)) a1
               in
               a2
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {γ = γ ﹐ _} {γ' = γ' ﹐ M} {γ'' = ∗} (wk-eq .(wk-cong π₁)) we₂ (wk-env-val-cong M ϖ₁) (wk-env-val-wk M₁ ϖ₂) =
               wk-env-val-wk (wk-v̲a̲l̲ π₁ M) (env-eq-trans (wk-eq π₁) (wk-ext-wk-lift we₂) ϖ₁ ϖ₂)
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {γ = γ ﹐ _} {γ' = γ' ﹐ M} {γ'' = γ'' ﹐ M₂} (wk-eq .(wk-cong π₁)) we₂ (wk-env-val-cong M ϖ₁) (wk-env-val-wk M₁ ϖ₂) =
               let
                 a0 = env-eq-trans (wk-eq π₁) (wk-ext-wk-lift we₂) ϖ₁ ϖ₂
                 a1 : EnvEq (wk-wk (wk-trans π₁ π₂)) (γ ﹐ M₁) (γ'' ﹐ M₂)
                 a1 = wk-env-val-wk M₁ a0
               in
               wk-env-val-wk (wk-v̲a̲l̲ π₁ M) a0
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {γ = γ ﹐ _} {γ' = γ' ﹐ M} {γ'' = γ'' ﹐﹝ W ╎ cs ﹞} (wk-eq .(wk-cong π₁)) we₂ (wk-env-val-cong M ϖ₁) (wk-env-val-wk M₁ ϖ₂) =
               let
                 a0 = env-eq-trans (wk-eq π₁) (wk-ext-wk-lift we₂) ϖ₁ ϖ₂
                 a1 : EnvEq (wk-wk (wk-trans π₁ π₂)) (γ ﹐ M₁) (γ'' ﹐﹝ W ╎ cs ﹞)
                 a1 = wk-env-val-wk M₁ a0
               in
               wk-env-val-wk (wk-v̲a̲l̲ π₁ M) a0
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {γ = (γ ﹐﹝ _ ╎ _ ﹞) {wk≡ = wk≡₁}} {γ' = (γ' ﹐﹝ _ ╎ _ ﹞) {wk≡ = wk≡₂}} {γ'' = (γ'' ﹐﹝ _ ╎ _ ﹞) {π = π₃} {wk≡ = wk≡₃}} (wk-eq π) we₂ (wk-env-comp-cong W cs {wk≡ = wk≡₄} {wk≡' = wk≡₅} ϖ₁) (wk-env-comp-cong W₁ cs₁ {wk≡ = wk≡₆} {wk≡' = wk≡₇} ϖ₂) = --{!!}
              let
                a0 = env-eq-trans (wk-eq π₁) (wk-ext-cong-lift we₂) ϖ₁ ϖ₂

                a1 : EnvEq (wk-cong (wk-trans π₁ π₂)) ((γ ﹐﹝ wk-comp (wk-trans π₁ π₂) W₁ ╎ cs ﹞) {π = wk-trans (wk-trans π₁ π₂) π₃} {wk≡ = subst (λ x → ⟦ proj₂ x ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) (pair-eq (wk-comp-trans W₁ π₁ π₂) (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})) wk≡₁}) ((γ'' ﹐﹝ W₁ ╎ cs ﹞) {π = π₃} {wk≡ = wk≡₃})
                a1 = wk-env-comp-cong W₁ cs {πᶜ = π₃} {wk≡ = wk≡₃} {wk≡' = subst (λ x → ⟦ proj₂ x ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) (pair-eq (wk-comp-trans W₁ π₁ π₂) (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})) wk≡₁} a0

                π≡ : wk-trans π₁ (wk-trans π₂ π₃) ≡ wk-trans (wk-trans π₁ π₂) π₃
                π≡ = wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃}
                W≡ : wk-comp π₁ (wk-comp π₂ W₁) ≡ wk-comp (wk-trans π₁ π₂) W₁
                W≡ = wk-comp-trans W₁ π₁ π₂

                eq2 :    ((γ ﹐﹝ wk-comp π₁ (wk-comp π₂ W₁) ╎ cs ﹞) {π = wk-trans π₁ (wk-trans π₂ π₃)} {wk≡ = wk≡₁})
                       ≡ ((γ ﹐﹝ wk-comp (wk-trans π₁ π₂) W₁ ╎ cs ﹞) {π = wk-trans (wk-trans π₁ π₂) π₃} {wk≡ = subst (λ x → ⟦ proj₂ x ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) (pair-eq W≡ π≡) wk≡₁})
                eq2 = dcong₂-irr ((λ x z → (γ ﹐﹝ proj₁ x ╎ cs ﹞) {π = proj₂ x} {wk≡ = z})) (pair-eq W≡ π≡)

                a2 : EnvEq (wk-cong (wk-trans π₁ π₂)) ((γ ﹐﹝ wk-comp π₁ (wk-comp π₂ W₁) ╎ cs ﹞) {π = wk-trans π₁ (wk-trans π₂ π₃)} {wk≡ = wk≡₁}) ((γ'' ﹐﹝ W₁ ╎ cs ﹞) {π = π₃} {wk≡ = wk≡₃})
                a2 = subst (λ x → EnvEq (wk-cong (wk-trans π₁ π₂)) x ((γ'' ﹐﹝ W₁ ╎ cs ﹞) {π = π₃} {wk≡ = wk≡₃})) (sym eq2) a1
              in
              a2

  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {γ = γ} {γ' = γ'} {γ'' = ∗} (wk-eq .(wk-cong π₁)) we₂ (wk-env-comp-cong W cs ϖ₁) (wk-env-comp-wk W₁ cs₁ ϖ₂) =
               wk-env-comp-wk (wk-comp π₁ W) cs (env-eq-trans (wk-eq π₁) (wk-ext-wk-lift we₂) ϖ₁ ϖ₂)
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {γ = (γ ﹐﹝ _ ╎ _ ﹞) {π = πₓ} {wk≡ = wk≡}} {γ' = γ'} {γ'' = γ'' ﹐ M} (wk-eq .(wk-cong π₁)) we₂ (wk-env-comp-cong W cs ϖ₁) (wk-env-comp-wk W₁ cs₁ ϖ₂) =
               let
                 a0 = env-eq-trans (wk-eq π₁) (wk-ext-wk-lift we₂) ϖ₁ ϖ₂
                 a1 = wk-env-comp-wk W₁ cs {πᶜ' = wk-trans π₁ _} {wk≡' = wk≡} a0
               in
               wk-env-comp-wk (wk-comp π₁ W) cs a0
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {γ = (γ ﹐﹝ _ ╎ _ ﹞) {π = πₓ} {wk≡ = wk≡}} {γ' = γ' ﹐﹝ _ ╎ _ ﹞} {γ'' = γ'' ﹐﹝ W₂ ╎ cs₂ ﹞} (wk-eq .(wk-cong π₁)) we₂ (wk-env-comp-cong W cs ϖ₁) (wk-env-comp-wk W₁ cs₁ ϖ₂) =
               let
                 a0 = env-eq-trans (wk-eq π₁) (wk-ext-wk-lift we₂) ϖ₁ ϖ₂
                 a1 = wk-env-comp-wk W₁ cs {πᶜ' = wk-trans π₁ _} {wk≡' = wk≡} a0
               in
               wk-env-comp-wk (wk-comp π₁ W) cs a0
  env-eq-trans {π₁ = wk-wk π₁} {π₂ = π₂} {γ = γ ﹐ _} {γ' = γ'} {γ'' = γ''} (wk-eq π) we₂ (wk-env-val-wk M ϖ₁) ϖ₂ = ql (wk-absurd π₁ wk-id) _
  env-eq-trans {π₁ = wk-wk π₁} {π₂ = π₂} {γ = γ} {γ' = γ'} {γ'' = γ''} (wk-eq π) we₂ (wk-env-comp-wk W cs ϖ₁) ϖ₂ = ql (wk-absurd π₁ wk-id) _
  env-eq-trans {π₁ = wk-wk π₁} {π₂ = π₂} {γ = γ} {γ' = γ'} {γ'' = γ''} (wk-ext π we₁) (wk-eq π₃) (wk-env-val-wk M ϖ₁) ϖ₂ = wk-env-val-wk M (env-eq-trans we₁ (wk-eq π₂) ϖ₁ ϖ₂)
  env-eq-trans {π₁ = wk-wk π₁} {π₂ = π₂} {γ = γ} {γ' = γ'} {γ'' = γ''} (wk-ext π we₁) (wk-ext π₃ we₂) (wk-env-val-wk M ϖ₁) ϖ₂ = wk-env-val-wk M (env-eq-trans we₁ (wk-ext π₃ we₂) ϖ₁ ϖ₂)
  env-eq-trans {π₁ = wk-wk π₁} {π₂ = π₂} {γ = γ} {γ' = γ'} {γ'' = γ''} (wk-ext π we₁) (wk-eq π₃) (wk-env-comp-wk W cs ϖ₁) ϖ₂ = wk-env-comp-wk W cs (env-eq-trans we₁ (wk-eq π₂) ϖ₁ ϖ₂)
  env-eq-trans {π₁ = wk-wk π₁} {π₂ = π₂} {γ = γ} {γ' = γ'} {γ'' = γ''} (wk-ext π we₁) (wk-ext π₃ we₂) (wk-env-comp-wk W cs ϖ₁) ϖ₂ = wk-env-comp-wk W cs (env-eq-trans we₁ (wk-ext π₃ we₂) ϖ₁ ϖ₂)


  env-eq-sem : {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ} → EnvEq π γ' γ → ⟦ π ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ γ ⟧ᴱ
  env-eq-sem {π = π} {γ' = γ'} {γ = γ} wk-env-ε = refl
  env-eq-sem {π = π} {γ' = γ'} {γ = γ} (wk-env-val-cong {π = π₁} {γ' = γ''} {γ = γ₁} M ϖ) =
             let
               IH = env-eq-sem ϖ
               goal : ⟦ wk-cong π₁ ⟧ʷ (⟦ γ'' ⟧ᴱ , (⟦ π₁ ⟧ʷ ； ⟦ toVal M ⟧ᵛ) ⟦ γ'' ⟧ᴱ) ≡ (⟦ γ₁ ⟧ᴱ , ⟦ toVal M ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
               goal =   ⟦ π₁ ⟧ʷ ⟦ γ'' ⟧ᴱ , ⟦ toVal M ⟧ᵛ (⟦ π₁ ⟧ʷ ⟦ γ'' ⟧ᴱ)
                      ≡⟨ cong (λ x → x , ⟦ toVal M ⟧ᵛ x) IH ⟩
                        (⟦ γ₁ ⟧ᴱ , ⟦ toVal M ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ∎
             in
             goal
  env-eq-sem {π = π} {γ' = γ'} {γ = γ} (wk-env-comp-cong {π = π₁} {γ' = γ''} {γ = γ₁} W cs ϖ) =
             let
               IH = env-eq-sem ϖ
               goal : ⟦ wk-cong π₁ ⟧ʷ (⟦ γ'' ⟧ᴱ , (⟦ π₁ ⟧ʷ ； ⟦ W ⟧ᶜ) ⟦ γ'' ⟧ᴱ ⟦ cs ⟧ᴷ) ≡ (⟦ γ₁ ⟧ᴱ , ⟦ W ⟧ᶜ ⟦ γ₁ ⟧ᴱ ⟦ cs ⟧ᴷ)
               goal =   ⟦ π₁ ⟧ʷ ⟦ γ'' ⟧ᴱ , ⟦ W ⟧ᶜ (⟦ π₁ ⟧ʷ ⟦ γ'' ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ cong (λ x → x , ⟦ W ⟧ᶜ x (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) IH ⟩
                        ⟦ γ₁ ⟧ᴱ , ⟦ W ⟧ᶜ ⟦ γ₁ ⟧ᴱ (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀) ∎
             in
             goal
  env-eq-sem {π = π} {γ' = γ'} {γ = γ} (wk-env-val-wk M ϖ) = env-eq-sem ϖ
  env-eq-sem {π = π} {γ' = γ'} {γ = γ} (wk-env-comp-wk W cs ϖ) = env-eq-sem ϖ

  enveq-eq : {π : Wk Γ Γ'} {γ : Env Γ} {γ' : Env Γ'} → EnvEq π γ γ' → ⟦ γ' ⟧ᴱ ≡ ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ
  enveq-eq {π = wk-ε} {γ = ∗} {γ' = ∗} wk-env-ε = refl
  enveq-eq {π = wk-cong π} {γ = γ ﹐ M} {γ' = γ' ﹐ M₁} (wk-env-val-cong M₂ ϖ) =
                let
                  IH = enveq-eq ϖ
                in
                  ⟦ γ' ⟧ᴱ , ⟦ toVal M₁ ⟧ᵛ ⟦ γ' ⟧ᴱ
                ≡⟨ cong (λ x → x , ⟦ toVal M₁ ⟧ᵛ x) IH ⟩
                  ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal M₁ ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) ∎
  enveq-eq {π = wk-cong π} {γ = γ ﹐ M} {γ' = γ' ﹐﹝ W ╎ cs ﹞} ()
  enveq-eq {π = wk-cong π} {γ = γ ﹐﹝ W ╎ cs ﹞} {γ' = γ' ﹐ M} ()
  enveq-eq {π = wk-cong π} {γ = γ ﹐﹝ W ╎ cs ﹞} {γ' = γ' ﹐﹝ W₁ ╎ cs₁ ﹞} (wk-env-comp-cong W₂ cs₂ ϖ) =
                let
                  IH = enveq-eq ϖ
                in
                  (⟦ γ' ⟧ᴱ , ⟦ W₁ ⟧ᶜ ⟦ γ' ⟧ᴱ (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀))
                ≡⟨ cong (λ x → x , ⟦ W₁ ⟧ᶜ x (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) IH ⟩
                  (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ W₁ ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) ∎
  enveq-eq {π = wk-wk π} {γ = γ ﹐ M} {γ' = ∗} (wk-env-val-wk M₁ ϖ) = enveq-eq ϖ
  enveq-eq {π = wk-wk π} {γ = γ ﹐ M} {γ' = γ' ﹐ M₁} (wk-env-val-wk M₂ ϖ) = enveq-eq ϖ
  enveq-eq {π = wk-wk π} {γ = γ ﹐ M} {γ' = γ' ﹐﹝ W ╎ cs ﹞} (wk-env-val-wk M₁ ϖ) = enveq-eq ϖ
  enveq-eq {π = wk-wk π} {γ = γ ﹐﹝ W ╎ cs ﹞} {γ' = ∗} (wk-env-comp-wk W₁ cs₁ ϖ) = enveq-eq ϖ
  enveq-eq {π = wk-wk π} {γ = γ ﹐﹝ W ╎ cs ﹞} {γ' = γ' ﹐ M} (wk-env-comp-wk W₁ cs₁ ϖ) = enveq-eq ϖ
  enveq-eq {π = wk-wk π} {γ = γ ﹐﹝ W ╎ cs ﹞} {γ' = γ' ﹐﹝ W₁ ╎ cs₁ ﹞} (wk-env-comp-wk W₂ cs₂ ϖ) = enveq-eq ϖ

---------------------------------------------------------------

  data EnvSim : (γ' : Env Γ') → (γ : Env Γ) → Set where

    env-sim-geq : {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ} → EnvEq π γ' γ → EnvSim γ' γ

    env-sim-leq : {π : Wk Γ Γ'} {γ' : Env Γ'} {γ : Env Γ} → EnvEq π γ γ' → EnvSim γ' γ

  envsim-id : {γ : Env Γ} → EnvSim γ γ
  envsim-id {γ = γ} = env-sim-geq enveq-id

---------------------------------------------------------------

  lstate-eq : {L L' : LookupState X} → L →ᴸ L' → ⟦ L ⟧ᴸ ≡ ⟦ L' ⟧ᴸ
  lstate-eq {L = L} {L' = L'} val-h-step = refl
  lstate-eq {L = L} {L' = L'} val-t-step = refl
  lstate-eq {L = L} {L' = L'} comp-t-step = refl

  lstate-eq* : {L L' : LookupState X} → L →ᴸ* L' → ⟦ L ⟧ᴸ ≡ ⟦ L' ⟧ᴸ
  lstate-eq* {L = L} {L' = L'} (L ◼) = refl
  lstate-eq* {L = L} {L' = L'} (L →ᴸ⟨ L→L' ⟩ L'→L'') =
             let
               IH0 = lstate-eq L→L'
               IH1 = lstate-eq* L'→L''
             in
             trans IH0 IH1

  valstate-eq : {S S' : ValState X} → S →ᵛ S' → ⟦ S ⟧ᵛꟴ ≡ ⟦ S' ⟧ᵛꟴ
  valstate-eq {S = S} {S' = S'} (∘var-c {tail = □} {↥ = 🗆}) = refl
  valstate-eq {S = S} {S' = S'} (∘var-c {tail = (x ⊲ γ ∷ tail) {↥ = ↥}} {↥ = 🗇}) = refl
  valstate-eq {S = S} {S' = S'} (∘var {γ = γ} {γ' = γ'} {i = i} {tail = □} {↥ = 🗆} {M = M} i>>T πᵥ x) =
              lstate-eq* i>>T
  valstate-eq {S = S} {S' = S'} (∘var {γ = γ} {γ' = γ'} {i = i} {tail = ((M'' ⊲ γ'' ∷ tail) {↥ = ↥})} {↥ = 🗇} {M = M} i>>T πᵥ x) =
               ⟦ ∘ ((⇡ var i ⊲ γ ∷ ((M'' ⊲ γ'' ∷ tail) {↥ = ↥})) {↥ = 🗇}) ⟧ᵛꟴ
              ≡⟨ refl ⟩
               ⟦ ∙ ((⭭ wk-v̲a̲l̲ πᵥ M ⊲ γ ∷ ((M'' ⊲ γ'' ∷ tail) {↥ = ↥})) {↥ = 🗇}) ⟧ᵛꟴ ∎

  valstate-eq {S = S} {S' = S'} (∘lam {M = W} {γ = γ} {tail = □} {↥ = 🗆}) = refl
  valstate-eq {S = S} {S' = S'} (∘lam {M = W} {γ = γ} {tail = x ⊲ γ₁ ∷ tail} {↥ = 🗇}) = refl

  valstate-eq {S = S} {S' = S'} (∘pair {tail = □} {↥ = 🗆}) = refl
  valstate-eq {S = S} {S' = S'} (∘pair {tail = x ⊲ γ ∷ tail} {↥ = 🗇}) = refl

  valstate-eq {S = S} {S' = S'} (∘pm {tail = □} {↥ = 🗆}) = refl
  valstate-eq {S = S} {S' = S'} (∘pm {tail = x ⊲ γ ∷ tail} {↥ = 🗇}) = refl

  valstate-eq {S = S} {S' = S'} (∘unit {tail = □} {↥ = 🗆}) = refl
  valstate-eq {S = S} {S' = S'} (∘unit {tail = x ⊲ γ ∷ tail} {↥ = 🗇}) = refl

  valstate-eq {S = S} {S' = S'} (∙M∷l {γ' = γ'} {γ = γ} {M = M} {LHS = LHS} {RHS = RHS} {π' = π'} {tail = □} {↥ = 🗆} π≡ LHS≡M) =
               ⟦ ∙ ((⭭ M ⊲ γ ∷ ((⇡ᴸ LHS RHS ⊲ γ' ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ
              ≡⟨ refl ⟩
               ⟦ LHS ⟧ᵛ ⟦ γ' ⟧ᴱ , ⟦ RHS ⟧ᵛ ⟦ γ' ⟧ᴱ
              ≡⟨ cong₂ (λ x y → x , ⟦ RHS ⟧ᵛ y) LHS≡M π≡ ⟩
               ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ)
              ≡⟨ refl ⟩
               ⟦ ∘ ((⇡ wk-val π' RHS ⊲ γ ∷ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ ∎
  valstate-eq {S = S} {S' = S'} (∙M∷l {tail = x ⊲ γ ∷ tail} {↥ = 🗇} π≡ LHS≡M) = refl

  valstate-eq {S = S} {S' = S'} (∙M∷r {γ' = γ'} {γ = γ} {M = M} {LHS = LHS} {RHS = RHS} {π' = π'} {tail = □} {↥ = 🗆} π≡ RHS≡M) =
               ⟦ ∙ ((⭭ M ⊲ γ ∷ ((⇡ᴿ LHS RHS ⊲ γ' ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ
              ≡⟨ refl ⟩
               ⟦ toVal LHS ⟧ᵛ ⟦ γ' ⟧ᴱ , ⟦ RHS ⟧ᵛ ⟦ γ' ⟧ᴱ
              ≡⟨ cong₂ (λ x y → ⟦ toVal LHS ⟧ᵛ x , y) π≡ RHS≡M ⟩
               ⟦ toVal LHS ⟧ᵛ (⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ
              ≡⟨ refl ⟩
               ⟦ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M ⊲ γ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ∎
  valstate-eq {S = S} {S' = S'} (∙M∷r {tail = x ⊲ γ ∷ tail} {↥ = 🗇} π≡ RHS≡M) = refl

  valstate-eq {S = S} {S' = S'} (∙pair∷pm {γ' = γ'} {γ = γ} {LHS = LHS} {RHS = RHS} {M = M} {N = N} {π' = π'} {tail = □} {↥ = 🗆} π≡ p₁M≡LHS p₂M≡RHS) =
               ⟦ ∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ ∷ ((⇡ᴹ M N ⊲ γ' ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ
              ≡⟨ refl ⟩
               ⟦ N ⟧ᵛ ((⟦ γ' ⟧ᴱ , proj₁ (⟦ M ⟧ᵛ ⟦ γ' ⟧ᴱ)) , proj₂ (⟦ M ⟧ᵛ ⟦ γ' ⟧ᴱ))
              ≡⟨ cong ⟦ N ⟧ᵛ (cong₂ _,_ (cong₂ _,_ π≡ p₁M≡LHS) p₂M≡RHS) ⟩
               ⟦ N ⟧ᵛ ((⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ)
              ≡⟨ refl ⟩
               ⟦ ∘ ((⇡ wk-val (wk-cong (wk-cong π')) N ⊲ γ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ∎
  valstate-eq {S = S} {S' = S'} (∙pair∷pm {tail = x ⊲ γ ∷ tail} {↥ = 🗇} _ _ _) = refl

{- not true with GC
  valstate-wk : {S S' : ValState X} → S →ᵛ S' → Wk (topCtx S') (topCtx S)
  valstate-wk ∘var-c = wk-id
  valstate-wk (∘var i>>T πᵥ x x₁ x₂ x₃) = wk-id
  valstate-wk ∘lam = wk-id
  valstate-wk ∘pair = wk-id
  valstate-wk ∘pm = wk-id
  valstate-wk ∘unit = wk-id
  valstate-wk (∙M∷l π≡ LHS≡M) = wk-id
  valstate-wk (∙M∷r π≡ RHS≡M) = wk-id
  valstate-wk (∙pair∷pm {tail = tail} {↥ = ↥} π≡ p₁M≡LHS p₂M≡RHS) = wk-wk (wk-wk wk-id)
-}

  lstate-env-sim : {L L' : LookupState X} → (L→L' : L →ᴸ L') → EnvSim (lTEnv L') (lEnv L)
  lstate-env-sim (val-h-step {E = γ ﹐ M} {i = i}) = env-sim-leq (wk-env-val-wk (v̲a̲r̲ i) (wk-env-val-wk M enveq-id))
  lstate-env-sim (val-h-step {E = γ ﹐﹝ W ╎ cs ﹞} {i = i}) = env-sim-leq (wk-env-val-wk (v̲a̲r̲ i) (wk-env-comp-wk W cs enveq-id))
  lstate-env-sim (val-t-step {i = i} {E = γ ﹐ M}) = env-sim-leq (wk-env-val-wk _ (wk-env-val-wk M enveq-id))
  lstate-env-sim (val-t-step {i = i} {E = γ ﹐﹝ W ╎ cs ﹞}) = env-sim-leq (wk-env-val-wk _ (wk-env-comp-wk W cs enveq-id))
  lstate-env-sim (comp-t-step {i = i} {γ = γ ﹐ M} {W = W} {cs = cs}) = env-sim-leq (wk-env-comp-wk W cs (wk-env-val-wk M enveq-id))
  lstate-env-sim (comp-t-step {i = i} {γ = γ ﹐﹝ W₂ ╎ cs₂ ﹞} {W = W₁} {cs = cs₁}) = env-sim-leq (wk-env-comp-wk W₁ cs₁ (wk-env-comp-wk W₂ cs₂ enveq-id))

  -- lstate-env-sim* : {L L' : LookupState X} → (L→L' : L →ᴸ* L') → EnvSim (lTEnv L') (lEnv L)
  -- lstate-env-sim* L→L' = {!!}

  valstate-env-sim : {S S' : ValState X} → (S→S' : S →ᵛ S') → EnvSim (topEnv S') (topEnv S)
  valstate-env-sim ∘var-c = envsim-id
  valstate-env-sim (∘var i>>T πᵥ x) = {!-m!}
  valstate-env-sim ∘lam = envsim-id
  valstate-env-sim ∘pair = envsim-id
  valstate-env-sim ∘pm = envsim-id
  valstate-env-sim ∘unit = envsim-id
  valstate-env-sim (∙M∷l π≡ LHS≡M) = envsim-id
  valstate-env-sim (∙M∷r π≡ RHS≡M) = envsim-id
  valstate-env-sim (∙pair∷pm π≡ p₁M≡LHS p₂M≡RHS) = env-sim-geq (wk-env-val-wk (wk-v̲a̲l̲ (wk-wk wk-id) _) (wk-env-val-wk _ enveq-id))

{- not true with GC
  valstate-env-eq : {S S' : ValState X} → (S→S' : S →ᵛ S') → EnvEq (valstate-wk S→S') (topEnv S') (topEnv S)
  valstate-env-eq ∘var-c = enveq-id
  valstate-env-eq (∘var i>>T πᵥ x x₁ x₂ x₃) = enveq-id
  valstate-env-eq ∘lam = enveq-id
  valstate-env-eq ∘pair = enveq-id
  valstate-env-eq ∘pm = enveq-id
  valstate-env-eq ∘unit = enveq-id
  valstate-env-eq (∙M∷l π≡ LHS≡M) = enveq-id
  valstate-env-eq (∙M∷r π≡ RHS≡M) = enveq-id
  valstate-env-eq (∙pair∷pm {Γ = Γ} {X = X} {Y = Y} {Z = Z} {γ' = γ'} {γ = γ} {LHS = LHS} {RHS = RHS} {M = M} {N = N} {π' = π'} {tail = tail} {↥ = ↥} π≡ p₁M≡LHS p₂M≡RHS) =
                  let
                    goal : EnvEq (wk-wk (wk-wk wk-id)) (γ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS) γ
                    goal = wk-env-val-wk (wk-v̲a̲l̲ (wk-wk wk-id) RHS) (wk-env-val-wk LHS enveq-id)
                  in
                  goal

  valstate-wkext-eq : {S S' : ValState X} → (S→S' : S →ᵛ S') → WkExt (valstate-wk S→S')
  valstate-wkext-eq ∘var-c = wk-eq _
  valstate-wkext-eq (∘var i>>T πᵥ x x₁ x₂ x₃) = wk-eq _
  valstate-wkext-eq ∘lam = wk-eq _
  valstate-wkext-eq ∘pair = wk-eq _
  valstate-wkext-eq ∘pm = wk-eq _
  valstate-wkext-eq ∘unit = wk-eq _
  valstate-wkext-eq (∙M∷l π≡ LHS≡M) = wk-eq _
  valstate-wkext-eq (∙M∷r π≡ RHS≡M) = wk-eq _
  valstate-wkext-eq (∙pair∷pm π≡ p₁M≡LHS p₂M≡RHS) = wk-ext (wk-wk wk-id) (wk-ext wk-id (wk-eq wk-id))
-}

-----------------------------------------------

  lhwk : (γ' : Env Γ')
          → (M : V̲a̲l̲ Γ' X)
          → (H : LookupHaltingState ⟨ h ∥ γ' ﹐ M ⟩)
          → (Ψ' : Ctx)
          → (πᵣ : Wk Ψ' Γ')
          → (γᵣ : Env Ψ')
          → (LookupHaltingState ⟨ h ∥ γᵣ ﹐ wk-v̲a̲l̲ πᵣ M ⟩)
  lhwk γ' M found-unit Ψ' πᵣ γᵣ = found-unit
  lhwk γ' M found-pair Ψ' πᵣ γᵣ = found-pair
  lhwk γ' M found-lam Ψ' πᵣ γᵣ = found-lam


{- XXX
  lookup-wk-lift : {γ : Env Γ} {γ' : Env Γ'}
                 → (i : Γ ∋ X) → (M : V̲a̲l̲ Γ' X) → (ext : EnvExt i γ (γ' ﹐ M))
                 → ⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ γ' ﹐ M ⟩
                 → (H : LookupHaltingState ⟨ h ∥ γ' ﹐ M ⟩)
                 → (πₗ : Wk Ψ Γ)
                 → (γₗ : Env Ψ)
                 → (ϖₗ : EnvEq πₗ γₗ γ)
                 → Σ[ Ψ' ∈ Ctx ]
                   Σ[ πᵣ ∈ Wk Ψ' Γ' ]
                   Σ[ π' ∈ Wk Ψ Ψ' ]
                   Σ[ γᵣ ∈ Env Ψ' ]
                   Σ[ L→*L' ∈ ⟨ (wk-mem πₗ i) ∥ γₗ ⟩ →ᴸ* ⟨ h ∥ γᵣ ﹐ wk-v̲a̲l̲ πᵣ M ⟩ ]
                   ( (LookupHaltingState ⟨ h ∥ γᵣ ﹐ wk-v̲a̲l̲ πᵣ M ⟩)
                     × EnvExt (lookup-index L→*L') γₗ (γᵣ ﹐ wk-v̲a̲l̲ πᵣ M)
                     × WkExt π'
                     × EnvEq π' γₗ γᵣ
                     × ⟦ ⟨ (wk-mem πₗ i) ∥ γₗ ⟩ ⟧ᴸ ≡ ⟦ ⟨ h ∥ γᵣ ﹐ wk-v̲a̲l̲ πᵣ M ⟩ ⟧ᴸ
                     × ⟦ π' ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γᵣ ⟧ᴱ )

  lookup-wk-lift {X = X} i M env-val (S ◼) H (wk-cong {Γ = Γₗ} πₗ) (γₗ ﹐ M₁) (wk-env-val-cong M₂ ϖₗ) =
                 Γₗ , πₗ , wk-wk wk-id , γₗ , (⟨ h ∥ γₗ ﹐ wk-v̲a̲l̲ πₗ M ⟩ ◼) , lhwk _ M H Γₗ πₗ γₗ , env-val , WkExt.wk-ext wk-id (WkExt.wk-eq wk-id) , EnvEq.wk-env-val-wk (wk-v̲a̲l̲ πₗ M) enveq-id , refl , refl -- refl
  lookup-wk-lift i M env-val (S ◼) H (wk-cong πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) ()
  lookup-wk-lift {γ' = γ'} i M env-val (S ◼) H (wk-wk πₗ) (γₗ ﹐ M₁) (wk-env-val-wk M₂ ϖₗ) =
                 let
                   t = lookup-wk-lift h M env-val (⟨ h ∥ γ' ﹐ M ⟩ ◼) H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , wk-wk (proj₁ (proj₂ (proj₂ t))) , proj₁ (proj₂ (proj₂ (proj₂ t))) , (⟨ wk-mem (wk-wk πₗ) h ∥ γₗ Env.﹐ M₁ ⟩ _→ᴸ*_.→ᴸ⟨ _→ᴸ_.val-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , EnvExt.ext-val (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))) , WkExt.wk-ext (proj₁ (proj₂ (proj₂ t))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t)))))))) , EnvEq.wk-env-val-wk M₁ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) --  proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))
  lookup-wk-lift i M env-val (S ◼) H (wk-wk πₗ) ((γₗ ﹐﹝ W ╎ cs ﹞) {wk≡ = wk≡}) (wk-env-comp-wk W₁ cs₁ ϖₗ) =
                 let
                   t = lookup-wk-lift h M env-val (_ ◼) H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , wk-wk (proj₁ (proj₂ (proj₂ t))) , proj₁ (proj₂ (proj₂ (proj₂ t))) , (⟨ wk-mem (wk-wk πₗ) h ∥ γₗ Env.﹐﹝ W ╎ cs ﹞ ⟩ →ᴸ⟨ comp-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , EnvExt.ext-comp (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))) , WkExt.wk-ext (proj₁ (proj₂ (proj₂ t))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t)))))))) , EnvEq.wk-env-comp-wk W cs (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) --  proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))
  lookup-wk-lift i M env-val (S →ᴸ⟨ x ⟩ L→*L') H (wk-cong {Γ = Γₗ} πₗ) (γₗ ﹐ M₁) (wk-env-val-cong M₂ ϖₗ) =
                 Γₗ , πₗ , wk-wk wk-id , γₗ , (_ ◼) , lhwk _ M H Γₗ πₗ γₗ , EnvExt.env-val , WkExt.wk-ext wk-id (WkExt.wk-eq wk-id) , wk-env-val-wk (wk-v̲a̲l̲ πₗ M) enveq-id , refl , refl --  refl
  lookup-wk-lift i M env-val (S →ᴸ⟨ x ⟩ L→*L') H (wk-cong πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) ()
  lookup-wk-lift i M env-val (S →ᴸ⟨ x ⟩ L→*L') H (wk-wk πₗ) (γₗ ﹐ M₁) (wk-env-val-wk M₂ ϖₗ) =
                 let
                   t = lookup-wk-lift h M env-val (_ ◼) H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , wk-wk (proj₁ (proj₂ (proj₂ t))) , proj₁ (proj₂ (proj₂ (proj₂ t))) , (⟨ wk-mem (wk-wk πₗ) h ∥ γₗ Env.﹐ M₁ ⟩ _→ᴸ*_.→ᴸ⟨ _→ᴸ_.val-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , EnvExt.ext-val (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))) , WkExt.wk-ext (proj₁ (proj₂ (proj₂ t))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t)))))))) , EnvEq.wk-env-val-wk M₁ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) --  proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))
  lookup-wk-lift i M env-val (S →ᴸ⟨ x ⟩ L→*L') H (wk-wk πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) (wk-env-comp-wk W₁ cs₁ ϖₗ) =
                 let
                   t = lookup-wk-lift h M env-val (_ ◼) H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , wk-wk (proj₁ (proj₂ (proj₂ t))) , proj₁ (proj₂ (proj₂ (proj₂ t))) , (_ →ᴸ⟨ comp-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , (ext-comp (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t)))))))) , WkExt.wk-ext (proj₁ (proj₂ (proj₂ t))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t)))))))) , wk-env-comp-wk W cs (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) --  proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))
  lookup-wk-lift i M (ext-val ext) (⟨ t i₁ ∥ _ ⟩ →ᴸ⟨ val-t-step ⟩ L→*L') H (wk-cong πₗ) (γₗ ﹐ M₁) (wk-env-val-cong M₂ ϖₗ) =
                 let
                   t = lookup-wk-lift i₁ M ext L→*L' H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , wk-wk (proj₁ (proj₂ (proj₂ t))) , proj₁ (proj₂ (proj₂ (proj₂ t))) , (⟨ wk-mem (wk-cong πₗ) (Inception.Sub.Syntax.t i₁) ∥ γₗ Env.﹐ wk-v̲a̲l̲ πₗ M₂ ⟩ _→ᴸ*_.→ᴸ⟨ _→ᴸ_.val-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , EnvExt.ext-val (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))) , WkExt.wk-ext (proj₁ (proj₂ (proj₂ t))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t)))))))) , wk-env-val-wk (wk-v̲a̲l̲ πₗ M₂) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) --  proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))
  lookup-wk-lift i M (ext-val ext) (S →ᴸ⟨ x ⟩ L→*L') H (wk-cong πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) ()
  lookup-wk-lift i M (ext-val ext) (⟨ t i₁ ∥ _ ⟩ →ᴸ⟨ val-t-step ⟩ L→*L') H (wk-wk πₗ) (γₗ ﹐ M₁) (wk-env-val-wk M₂ ϖₗ) =
                 let
                   t = lookup-wk-lift (t i₁) M (ext-val ext) (_ →ᴸ⟨ val-t-step ⟩ L→*L') H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , wk-wk (proj₁ (proj₂ (proj₂ t))) , proj₁ (proj₂ (proj₂ (proj₂ t))) , (⟨ wk-mem (wk-wk πₗ) (Inception.Sub.Syntax.t i₁) ∥ γₗ Env.﹐ M₁ ⟩ _→ᴸ*_.→ᴸ⟨ _→ᴸ_.val-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , EnvExt.ext-val (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))) , WkExt.wk-ext (proj₁ (proj₂ (proj₂ t))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t)))))))) , EnvEq.wk-env-val-wk M₁ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) --  proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))
  lookup-wk-lift i M (ext-val ext) ((⟨ t i₁ ∥ _ ﹐ _ ⟩) →ᴸ⟨ val-t-step ⟩ L→*L') H (wk-wk πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) (wk-env-comp-wk W₁ cs₁ ϖₗ) =
                 let
                   t = lookup-wk-lift (t i₁) M (ext-val ext) (_ →ᴸ⟨ val-t-step ⟩ L→*L') H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , wk-wk (proj₁ (proj₂ (proj₂ t))) , proj₁ (proj₂ (proj₂ (proj₂ t))) , (_ →ᴸ⟨ comp-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , ext-comp (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))) , WkExt.wk-ext (proj₁ (proj₂ (proj₂ t))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t)))))))) ,  wk-env-comp-wk W cs (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) --  proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))
  lookup-wk-lift i M (ext-comp ext) (S →ᴸ⟨ x ⟩ L→*L') H (wk-cong πₗ) (γₗ ﹐ M₁) ()
  lookup-wk-lift i M (ext-comp ext) ((⟨ t i₁ ∥ _ ﹐﹝ W₁ ╎ cs ﹞ ⟩) →ᴸ⟨ comp-t-step ⟩ L→*L') H (wk-cong πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) (wk-env-comp-cong W₁ cs₁ ϖₗ) =
                 let
                   t = lookup-wk-lift i₁ M ext L→*L' H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , wk-wk (proj₁ (proj₂ (proj₂ t))) , proj₁ (proj₂ (proj₂ (proj₂ t))) , (_ →ᴸ⟨ comp-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , ext-comp (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))) , WkExt.wk-ext (proj₁ (proj₂ (proj₂ t))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t)))))))) , wk-env-comp-wk (wk-comp πₗ W₁) cs (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) --  proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))
  lookup-wk-lift {X = X} i M (ext-comp ext) (⟨ t i₁ ∥ _ ⟩ →ᴸ⟨ comp-t-step ⟩ L→*L') H (wk-wk πₗ) (γₗ ﹐ M₁) (wk-env-val-wk M₂ ϖₗ) =
                 let
                   t = lookup-wk-lift (t i₁) M (ext-comp ext) (⟨ t i₁ ∥ _ ﹐﹝ _ ╎ _ ﹞ ⟩ →ᴸ⟨ comp-t-step ⟩ L→*L') H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , wk-wk (proj₁ (proj₂ (proj₂ t))) , proj₁ (proj₂ (proj₂ (proj₂ t))) , (⟨ wk-mem (wk-wk πₗ) (Inception.Sub.Syntax.t i₁) ∥ γₗ Env.﹐ M₁ ⟩ _→ᴸ*_.→ᴸ⟨ _→ᴸ_.val-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , EnvExt.ext-val (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))) , WkExt.wk-ext (proj₁ (proj₂ (proj₂ t))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t)))))))) , EnvEq.wk-env-val-wk M₁ (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) --  proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))
  lookup-wk-lift i M (ext-comp ext) ((⟨ t i₁ ∥ _ ﹐﹝ _ ╎ _ ﹞ ⟩) →ᴸ⟨ comp-t-step ⟩ L→*L') H (wk-wk πₗ) (γₗ ﹐﹝ W ╎ cs ﹞) (wk-env-comp-wk W₁ cs₁ ϖₗ) =
                 let
                   t = lookup-wk-lift (t i₁) M (ext-comp ext) (⟨ t i₁ ∥ _ ⟩ →ᴸ⟨ comp-t-step ⟩ L→*L') H πₗ γₗ ϖₗ
                 in
                 proj₁ t , proj₁ (proj₂ t) , wk-wk (proj₁ (proj₂ (proj₂ t))) , proj₁ (proj₂ (proj₂ (proj₂ t))) , (_ →ᴸ⟨ comp-t-step ⟩ proj₁ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))) , ext-comp (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))) , WkExt.wk-ext (proj₁ (proj₂ (proj₂ t))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t)))))))) , wk-env-comp-wk W cs (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) , proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))) --  proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ t))))))))


  --------------------------------------------------

  vs-height : ValStack b T◾ → ℕ
  vs-height □ = 0
  vs-height (_ ⊲ _ ∷ tail) = suc (vs-height tail)

  pair-val-eq : {π : Wk Γ Δ} {M : PartialTerm Δ (X `× Y)} {LHS : V̲a̲l̲ Γ X} {RHS : V̲a̲l̲ Γ Y} → (wk-pt π M ≡ ⭭ pa̲i̲r̲ LHS RHS) → Σ[ LHS' ∈ V̲a̲l̲ Δ X ] Σ[ RHS' ∈ V̲a̲l̲ Δ Y ] (⭭ pa̲i̲r̲ LHS' RHS' ≡ M)
  pair-val-eq {π = π} {M = ⭭ pa̲i̲r̲ LHS' RHS'} {LHS = LHS} {RHS = RHS} refl = LHS' , RHS' , refl

  vs-zero-eq : {vs : ValStack empty T◾} → (0 ≡ vs-height vs) → vs ≡ □
  vs-zero-eq {vs = □} _ = refl

  pt-⭭-inj : {M M' : V̲a̲l̲ Γ X} → ⭭ M ≡ ⭭ M' → M ≡ M'
  pt-⭭-inj refl = refl

  uniq-bot : (↥ : BottomTypeEqualsNextType non-empty X T◾) → (↥ ≡ 🗇)
  uniq-bot 🗇 = refl

  data VSWk : ValStack b T◾ → ValStack b T◾ → Set where

    vs-empty : VSWk {T◾ = T◾} □ □

    vs-wk : {M : PartialTerm Γ X} {γ' : Env Γ'} {γ : Env Γ} {tail' tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾}
            → (π : Wk Γ' Γ) → (ϖ : EnvEq π γ' γ) → VSWk tail' tail
            → VSWk ((wk-pt π M ⊲ γ' ∷ tail') {↥ = ↥}) ((M ⊲ γ ∷ tail) {↥ = ↥})

  vs-wk-id : {tail : ValStack b T◾} → VSWk tail tail
  vs-wk-id {tail = □} = vs-empty
  vs-wk-id {tail = M ⊲ γ ∷ tail} =
    let
      a0 = vs-wk {M = M} wk-id enveq-id vs-wk-id
      goal : VSWk (M ⊲ γ ∷ tail) (M ⊲ γ ∷ tail)
      goal = subst (λ x → VSWk (x ⊲ γ ∷ tail) (M ⊲ γ ∷ tail)) (wk-pt-id M) a0
    in
    goal

  val-wk-lift-∘∘ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          -- → ⟦ ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
          -- → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            -- Σ[ wk≡ᵣ ∈ ⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) →ᵛ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              --× ⟦ ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ
              × EnvEq πᵣ γᵣ γ'
              × (vs-height tail' ≡ vs-height tailᵣ))
  val-wk-lift-∘∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘pair {LHS = LHS} {RHS = RHS}) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                 Ψ , πₗ , γₗ , ⇡ᴸ (wk-val πₗ LHS) (wk-val πₗ RHS) ⊲ γₗ ∷ □ , ∘pair , ϖ , refl
                 -- Ψ , πₗ , γₗ , wk≡ₗ , ⇡ᴸ (wk-val πₗ LHS) (wk-val πₗ RHS) ⊲ γₗ ∷ □ , ∘pair , refl , refl
  val-wk-lift-∘∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘pair {LHS = LHS} {RHS = RHS}) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                 Ψ , πₗ , γₗ , ⇡ᴸ (wk-val πₗ LHS) (wk-val πₗ RHS) ⊲ γₗ ∷ M₁ ⊲ γ₁ ∷ tail , ∘pair , ϖ , refl
                 -- Ψ , πₗ , γₗ , wk≡ₗ , ⇡ᴸ (wk-val πₗ LHS) (wk-val πₗ RHS) ⊲ γₗ ∷ M₁ ⊲ γ₁ ∷ tail , ∘pair , refl , refl
  val-wk-lift-∘∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘pm {M = Mₚ} {N = Nₚ}) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                 Ψ , πₗ , γₗ , ⇡ᴹ (wk-val πₗ Mₚ) (wk-val (wk-cong (wk-cong πₗ)) Nₚ) ⊲ γₗ ∷ □ , ∘pm , ϖ , refl
                 -- Ψ , πₗ , γₗ , wk≡ₗ , ⇡ᴹ (wk-val πₗ Mₚ) (wk-val (wk-cong (wk-cong πₗ)) Nₚ) ⊲ γₗ ∷ □ , ∘pm , refl , refl
  val-wk-lift-∘∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘pm {M = Mₚ} {N = Nₚ}) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                 Ψ , πₗ , γₗ , ⇡ᴹ (wk-val πₗ Mₚ) (wk-val (wk-cong (wk-cong πₗ)) Nₚ) ⊲ γₗ ∷ M₁ ⊲ γ₁ ∷ tail , ∘pm , ϖ , refl
                 -- Ψ , πₗ , γₗ , wk≡ₗ , ⇡ᴹ (wk-val πₗ Mₚ) (wk-val (wk-cong (wk-cong πₗ)) Nₚ) ⊲ γₗ ∷ M₁ ⊲ γ₁ ∷ tail , ∘pm , refl , refl

  ------
  {- NEW
  val-wk-lift-∘∙ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ
          → (tailₗ : ValStack b T◾)
          → (vs-height tail ≡ vs-height tailₗ)
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ Γ'' ∈ Ctx ]
            Σ[ M'' ∈ PartialTerm Γ'' X' ]
            Σ[ πᵣ ∈ Wk Ψ' Γ'' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tailₗ) {↥ = ↥}) →ᵛ ∙ (((wk-pt πᵣ M'') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
                × (vs-height tail' ≡ vs-height tailᵣ))
  val-wk-lift-∘∙ {Γ = Γ} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘var-c {i = i}) {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vs≡ₗ =
                 Ψ , Γ' , M' , πₗ , γₗ , tailₗ , ∘var-c , vs≡ₗ
  val-wk-lift-∘∙ {Γ = Γ} {X = X} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘var {Γ = Γ₁} {Γ' = Γ₂} {γ = γ₁} {γ' = γ₂} {i = i} {M = M₁} L→L' πᵥ extᵥ weᵥ ϖᵥ H) {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vs≡ₗ =
                 let
                    a0 : EnvEq wk-id γ γ
                    a0 = enveq-id

                    a2 = li≡i L→L' H
                    a3 : EnvExt i γ (γ₂ ﹐ M₁)
                    a3 = subst (λ x → EnvExt x γ (γ₂ ﹐ M₁)) a2 extᵥ

                    b0 = lookup-wk-lift i M₁ a3 L→L' H πₗ γₗ ϖ

                    Ψ' = proj₁ b0
                    πᵣ = proj₁ (proj₂ b0)
                    π' = proj₁ (proj₂ (proj₂ b0))
                    γᵣ = proj₁ (proj₂ (proj₂ (proj₂ b0)))
                    L→L↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ b0))))
                    LH↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))
                    ext↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0))))))
                    we↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))))
                    ϖ↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0))))))))
                    S≡T↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))))))
                    π≡↑ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))))))

                    e1 : ∘ (⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ □ →ᵛ ∙ (⭭ wk-v̲a̲l̲ π' (wk-v̲a̲l̲ πᵣ M₁)) ⊲ γₗ ∷ □
                    e1 = ∘var {T◾ = X} {γ' = γᵣ} {i = wk-mem πₗ i} {tail = □} {↥ = 🗆} {M = wk-v̲a̲l̲ πᵣ M₁} L→L↑ π' ext↑ we↑ ϖ↑ LH↑

                    goal₀ : ∘ (⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ □ →ᵛ ∙ (⭭ wk-v̲a̲l̲ (wk-trans π' πᵣ) M₁) ⊲ γₗ ∷ □
                    goal₀ = subst (λ x → ∘ (((⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ □) {↥ = 🗆}) →ᵛ ∙ (((⭭ x) ⊲ γₗ ∷ □) {↥ = 🗆})) (wk-v̲a̲l̲-trans M₁ π' πᵣ) e1

                    goal' : ∘ (⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ tailₗ →ᵛ ∙ (⭭ wk-v̲a̲l̲ (wk-trans π' πᵣ) M₁) ⊲ γₗ ∷ tailₗ
                    goal' = subst (λ x → ∘ (⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ x →ᵛ ∙ (⭭ wk-v̲a̲l̲ (wk-trans π' πᵣ) M₁) ⊲ γₗ ∷ x) (sym (vs-zero-eq vs≡ₗ)) goal₀
                 in
                 Ψ , Γ₂ , (⭭ M₁) , wk-trans π' πᵣ , γₗ , tailₗ , goal' , vs≡ₗ
  val-wk-lift-∘∙ {Γ = Γ} {X = X} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘lam {M = W}) {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vs≡ₗ =
                 Ψ , Γ' , M' , πₗ , γₗ , tailₗ , ∘lam , vs≡ₗ
  val-wk-lift-∘∙ {Γ = Γ} {X = X} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} ∘unit {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vs≡ₗ =
                 Ψ , Γ , ⭭ u̲n̲i̲t̲ , πₗ , γₗ , tailₗ , ∘unit , vs≡ₗ
  val-wk-lift-∘∙ {Γ = Γ} {X = X} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘var-c {i = i}) {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vs≡ₗ =
                 Ψ , Γ , ⭭ v̲a̲r̲ i , πₗ , γₗ , tailₗ , ∘var-c , vs≡ₗ
  val-wk-lift-∘∙ {Ψ = Ψ} {M = M} {γ = γ} {tail = ((M₀ ⊲ γ₀ ∷ tail) {↥ = ↥})} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘var {Γ = Γ₁} {T◾ = T◾} {Γ' = Γ₂} {γ = γ₁} {γ' = γ₂} {i = i} {M = M₁} L→L' πᵥ extᵥ weᵥ ϖᵥ H) {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vs≡ₗ =
                 let
                    a2 = li≡i L→L' H
                    a3 : EnvExt i γ (γ₂ ﹐ M₁)
                    a3 = subst (λ x → EnvExt x γ (γ₂ ﹐ M₁)) a2 extᵥ

                    b0 = lookup-wk-lift i M₁ a3 L→L' H πₗ γₗ ϖ
                    Ψ' = proj₁ b0
                    πᵣ = proj₁ (proj₂ b0)
                    π' = proj₁ (proj₂ (proj₂ b0))
                    γᵣ = proj₁ (proj₂ (proj₂ (proj₂ b0)))
                    L→L↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ b0))))
                    LH↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))
                    ext↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0))))))
                    we↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))))
                    ϖ↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0))))))))
                    S≡T↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))))))
                    π≡↑ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))))))

                    e1 : ∘ (⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ tailₗ →ᵛ ∙ (⭭ wk-v̲a̲l̲ π' (wk-v̲a̲l̲ πᵣ M₁)) ⊲ γₗ ∷ tailₗ
                    e1 = ∘var {T◾ = T◾} {γ' = γᵣ} {i = wk-mem πₗ i} {tail = tailₗ} {↥ = 🗇} {M = wk-v̲a̲l̲ πᵣ M₁} L→L↑ π' ext↑ we↑ ϖ↑ LH↑

                    goal : ∘ wk-pt πₗ (⇡ var i) ⊲ γₗ ∷ tailₗ →ᵛ ∙ (⭭ wk-v̲a̲l̲ (wk-trans π' πᵣ) M₁) ⊲ γₗ ∷ tailₗ
                    goal = subst (λ x → ∘ ((wk-pt πₗ (⇡ var i) ⊲ γₗ ∷ tailₗ) {↥ = 🗇}) →ᵛ ∙ ((⭭ x) ⊲ γₗ ∷ tailₗ) {↥ = 🗇}) (wk-v̲a̲l̲-trans M₁ π' πᵣ) e1

                 in
                 Ψ , Γ₂ , ⭭ M₁ , wk-trans π' πᵣ , γₗ , tailₗ , goal , vs≡ₗ
  val-wk-lift-∘∙ {Γ = Γ} {X = X} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘lam {M = W}) {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vs≡ₗ =
                 Ψ , Γ , ⭭ l̲a̲m̲ W , πₗ , γₗ , tailₗ , ∘lam , vs≡ₗ
  val-wk-lift-∘∙ {Γ = Γ} {X = X} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} ∘unit {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vs≡ₗ =
                 Ψ , Γ , ⭭ u̲n̲i̲t̲ , πₗ , γₗ , tailₗ , ∘unit , vs≡ₗ
  -}

  val-wk-lift-∘∙ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          --→ ⟦ ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
          --→ {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ
          → Σ[ Ψ' ∈ Ctx ]
            --
            Σ[ Γ'' ∈ Ctx ]
            Σ[ M'' ∈ PartialTerm Γ'' X' ]
            Σ[ πᵣ ∈ Wk Ψ' Γ'' ]
            --Σ[ πᵥ ∈ Wk Γ' Γ'' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) →ᵛ ∙ (((wk-pt πᵣ M'') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
                --× ⟦ ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ (((wk-pt πᵣ M'') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ
                --× (wk-pt πᵥ M'' ≡ M')
                × (vs-height tail' ≡ vs-height tailᵣ))
  val-wk-lift-∘∙ {Γ = Γ} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘var-c {i = i}) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                 Ψ , Γ' , M' , πₗ , γₗ , □ , ∘var-c , refl
                 --Ψ , Γ' , M' , πₗ , wk-id , γₗ , □ , ∘var-c , refl , wk-pt-id (⭭ v̲a̲r̲ i) , refl
  val-wk-lift-∘∙ {Γ = Γ} {X = X} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘var {Γ = Γ₁} {Γ' = Γ₂} {γ = γ₁} {γ' = γ₂} {i = i} {M = M₁} L→L' πᵥ extᵥ weᵥ ϖᵥ H) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                 let
                    a0 : EnvEq wk-id γ γ
                    a0 = enveq-id
                    -- a1 : EnvEq πₜ γ γ
                    -- a1 = subst (λ x → EnvEq x γ γ) (sym wk-id-id) a0

                    a2 = li≡i L→L' H
                    a3 : EnvExt i γ (γ₂ ﹐ M₁)
                    a3 = subst (λ x → EnvExt x γ (γ₂ ﹐ M₁)) a2 extᵥ

                    b0 = lookup-wk-lift i M₁ a3 L→L' H πₗ γₗ ϖ

                    Ψ' = proj₁ b0
                    πᵣ = proj₁ (proj₂ b0)
                    π' = proj₁ (proj₂ (proj₂ b0))
                    γᵣ = proj₁ (proj₂ (proj₂ (proj₂ b0)))
                    L→L↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ b0))))
                    LH↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))
                    ext↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0))))))
                    we↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))))
                    ϖ↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0))))))))
                    S≡T↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))))))
                    π≡↑ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))))))

                    e1 : ∘ (⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ □ →ᵛ ∙ (⭭ wk-v̲a̲l̲ π' (wk-v̲a̲l̲ πᵣ M₁)) ⊲ γₗ ∷ □
                    e1 = ∘var {T◾ = X} {γ' = γᵣ} {i = wk-mem πₗ i} {tail = □} {↥ = 🗆} {M = wk-v̲a̲l̲ πᵣ M₁} L→L↑ π' ext↑ we↑ ϖ↑ LH↑

                    goal : ∘ (⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ □ →ᵛ ∙ (⭭ wk-v̲a̲l̲ (wk-trans π' πᵣ) M₁) ⊲ γₗ ∷ □
                    goal = subst (λ x → ∘ (((⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ □) {↥ = 🗆}) →ᵛ ∙ (((⭭ x) ⊲ γₗ ∷ □) {↥ = 🗆})) (wk-v̲a̲l̲-trans M₁ π' πᵣ) e1

                    eq : ⟦ ∘ ((wk-pt πₗ (⇡ var i) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ≡ ⟦ ∙ ((wk-pt (wk-trans π' πᵣ) (⭭ M₁) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ
                    eq =      ⟦ ∘ ((wk-pt πₗ (⇡ var i) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ
                            ≡⟨ refl ⟩
                               ⟦ wk-mem πₗ i ⟧ᵐ ⟦ γₗ ⟧ᴱ
                            ≡⟨ S≡T↑ ⟩
                               ⟦ ⟨ h ∥ γᵣ ﹐ wk-v̲a̲l̲ πᵣ M₁ ⟩ ⟧ᴸ
                            ≡⟨ refl ⟩
                               ⟦ toVal M₁ ⟧ᵛ (⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ)
                            ≡⟨ cong (λ x → ⟦ toVal M₁ ⟧ᵛ (⟦ πᵣ ⟧ʷ x)) (sym π≡↑) ⟩
                                ⟦ toVal M₁ ⟧ᵛ (⟦ πᵣ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γₗ ⟧ᴱ))
                            ≡⟨ refl ⟩
                              ⟦ ∙ (((⭭ wk-v̲a̲l̲ π' (wk-v̲a̲l̲ πᵣ M₁)) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ
                            ≡⟨ cong (λ x → ⟦ ∙ ((⭭ x ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ) (wk-v̲a̲l̲-trans M₁ π' πᵣ) ⟩
                              ⟦ ∙ (((⭭ wk-v̲a̲l̲ (wk-trans π' πᵣ) M₁) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ∎
                 in
                 Ψ , Γ₂ , (⭭ M₁) , wk-trans π' πᵣ , γₗ , □ , goal , refl
                 -- Ψ , Γ₂ , (⭭ M₁) , wk-trans π' πᵣ , πᵥ , γₗ , □ , goal , eq , refl , refl
  val-wk-lift-∘∙ {Γ = Γ} {X = X} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘lam {M = W}) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                 Ψ , Γ' , M' , πₗ , γₗ , □ , ∘lam , refl
                 --Ψ , Γ' , M' , πₗ , wk-id , γₗ , □ , ∘lam , refl , (wk-pt-id (⭭ l̲a̲m̲ W)) , refl
  val-wk-lift-∘∙ {Γ = Γ} {X = X} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} ∘unit {πₗ = πₗ} {γₗ = γₗ} ϖ =
                 Ψ , Γ , ⭭ u̲n̲i̲t̲ , πₗ , γₗ , □ , ∘unit , refl
                 --Ψ , Γ , ⭭ u̲n̲i̲t̲ , πₗ , wk-id , γₗ , □ , ∘unit , Q≡Q' , refl , refl
  val-wk-lift-∘∙ {Γ = Γ} {X = X} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘var-c {i = i}) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                 Ψ , Γ , ⭭ v̲a̲r̲ i , πₗ , γₗ , M₁ ⊲ γ₁ ∷ tail , ∘var-c , refl
                 --Ψ , Γ , ⭭ v̲a̲r̲ i , πₗ , wk-id , γₗ , M₁ ⊲ γ₁ ∷ tail , ∘var-c , Q≡Q' , wk-pt-id (⭭ v̲a̲r̲ i) , refl
  val-wk-lift-∘∙ {Ψ = Ψ} {M = M} {γ = γ} {tail = ((M₀ ⊲ γ₀ ∷ tail) {↥ = ↥})} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘var {Γ = Γ₁} {T◾ = T◾} {Γ' = Γ₂} {γ = γ₁} {γ' = γ₂} {i = i} {M = M₁} L→L' πᵥ extᵥ weᵥ ϖᵥ H) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                 let
                    a2 = li≡i L→L' H
                    a3 : EnvExt i γ (γ₂ ﹐ M₁)
                    a3 = subst (λ x → EnvExt x γ (γ₂ ﹐ M₁)) a2 extᵥ

                    b0 = lookup-wk-lift i M₁ a3 L→L' H πₗ γₗ ϖ
                    Ψ' = proj₁ b0
                    πᵣ = proj₁ (proj₂ b0)
                    π' = proj₁ (proj₂ (proj₂ b0))
                    γᵣ = proj₁ (proj₂ (proj₂ (proj₂ b0)))
                    L→L↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ b0))))
                    LH↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))
                    ext↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0))))))
                    we↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))))
                    ϖ↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0))))))))
                    S≡T↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))))))
                    π≡↑ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))))))

                    e1 : ∘ (⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ M₀ ⊲ γ₀ ∷ tail →ᵛ ∙ (⭭ wk-v̲a̲l̲ π' (wk-v̲a̲l̲ πᵣ M₁)) ⊲ γₗ ∷ M₀ ⊲ γ₀ ∷ tail
                    e1 = ∘var {T◾ = T◾} {γ' = γᵣ} {i = wk-mem πₗ i} {tail = ((M₀ ⊲ γ₀ ∷ tail) {↥ = ↥})} {↥ = 🗇} {M = wk-v̲a̲l̲ πᵣ M₁} L→L↑ π' ext↑ we↑ ϖ↑ LH↑

                    goal : ∘ wk-pt πₗ (⇡ var i) ⊲ γₗ ∷ M₀ ⊲ γ₀ ∷ tail →ᵛ ∙ (⭭ wk-v̲a̲l̲ (wk-trans π' πᵣ) M₁) ⊲ γₗ ∷ M₀ ⊲ γ₀ ∷ tail
                    goal = subst (λ x → ∘ ((wk-pt πₗ (⇡ var i) ⊲ γₗ ∷ ((M₀ ⊲ γ₀ ∷ tail) {↥ = ↥})) {↥ = 🗇}) →ᵛ ∙ (((⭭ x) ⊲ γₗ ∷ ((M₀ ⊲ γ₀ ∷ tail)) {↥ = ↥})) {↥ = 🗇}) (wk-v̲a̲l̲-trans M₁ π' πᵣ) e1

                 in
                 Ψ , Γ₂ , ⭭ M₁ , wk-trans π' πᵣ , γₗ , (M₀ ⊲ γ₀ ∷ tail) , goal , refl
                 --Ψ , Γ₂ , ⭭ M₁ , wk-trans π' πᵣ , πᵥ , γₗ , (M₀ ⊲ γ₀ ∷ tail) , goal , Q≡Q' , refl , refl
  val-wk-lift-∘∙ {Γ = Γ} {X = X} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘lam {M = W}) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                 Ψ , Γ , ⭭ l̲a̲m̲ W , πₗ , γₗ , M₁ ⊲ γ₁ ∷ tail , ∘lam , refl
                 --Ψ , Γ , ⭭ V̲a̲l̲.l̲a̲m̲ W , πₗ , wk-id , γₗ , M₁ ⊲ γ₁ ∷ tail , ∘lam , Q≡Q' , (wk-pt-id (⭭ l̲a̲m̲ W)) , refl
  val-wk-lift-∘∙ {Γ = Γ} {X = X} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} ∘unit {πₗ = πₗ} {γₗ = γₗ} ϖ =
                 Ψ , Γ , ⭭ u̲n̲i̲t̲ , πₗ , γₗ , M₁ ⊲ γ₁ ∷ tail , ∘unit , refl
                 --Ψ , Γ , ⭭ u̲n̲i̲t̲ , πₗ , wk-id , γₗ , M₁ ⊲ γ₁ ∷ tail , ∘unit , Q≡Q' , refl , refl

  ----------------
  {- NEW
  val-wk-lift-∙∘ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∙ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ
          → (tailₗ : ValStack b T◾)
          --→ (vs-height tail ≡ vs-height tailₗ)
          → VSWk tailₗ tail
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∙ (((wk-pt πₗ M) ⊲ γₗ ∷ tailₗ) {↥ = ↥}) →ᵛ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              --× (vs-height tail' ≡ vs-height tailᵣ)
              × VSWk tailᵣ tail'
              )
  val-wk-lift-∙∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} () {πₗ = πₗ} {γₗ = γₗ} ϖ _ _
  val-wk-lift-∙∘ {Ψ = Ψ} {M = ⭭ M} {γ = γ} {tail = ⇡ᴸ LHS RHS ⊲ γ₁ ∷ □} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = (⇡ᴿ M _ ⊲ γ ∷ □) {↥ = 🗆}} {↥' = 🗇} (∙M∷l {X = X} {Y = Y} {M = M} {LHS = LHS} {RHS = RHS} {π' = π'} π≡ LHS≡M) {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ (vs-wk {γ' = γ''} {tail' = □} π ϖ₁ vw) = --{!tailₗ!}
                 let
                   vs-eq : tailₗ ≡ ⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⊲ γ'' ∷ □
                   vs-eq = refl

                   eq : (⇡ wk-val (wk-trans πₗ π') RHS) ≡ wk-pt πₗ (⇡ wk-val π' RHS)
                   eq = cong (⇡_) (sym (wk-val-trans RHS πₗ π'))
                   π≡' : ⟦ γ₁ ⟧ᴱ ≡ ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ
                   π≡' =  ⟦ γ₁ ⟧ᴱ
                        ≡⟨ π≡  ⟩
                          ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ
                        ≡⟨ cong ⟦ π' ⟧ʷ (sym (env-eq-sem ϖ))  ⟩
                          ⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                        ≡⟨ wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ ⟩
                          ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ ∎
                   {-
                   M→M'' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ (((⇡ wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇})
                   M→M'' = ∙M∷l π≡' (trans LHS≡M (cong ⟦ toVal M ⟧ᵛ (sym (env-eq-sem ϖ))))
                   M→M''' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇})
                   M→M''' = subst (λ x → ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇})) eq M→M''

                   M→M'''' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ tailₗ) {↥ = 🗇}) →ᵛ ∘ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ tailₗ) {↥ = 🗇})
                   M→M'''' = {!!}
                   -}

                   M→M'' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⊲ γ'' ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ {!!}
                   M→M'' = ∙M∷l {!!} {!!}

                 in
                 Ψ , πₗ , γₗ , {!!} , {!!} , {!!}
                 --Ψ , πₗ , γₗ , tailₗ , M→M'''' , vs≡ₗ
                 --Ψ , πₗ , γₗ , (⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆} , M→M''' , refl

  val-wk-lift-∙∘ {Ψ = Ψ} {M = ⭭ M} {γ = γ} {tail = ⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∙M∷l {M = M} {LHS = LHS} {RHS = RHS} {π' = π'} {↥ = ↥₀} π≡ LHS≡M) {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vw =
                 let
                   eq : (⇡ wk-val (wk-trans πₗ π') RHS) ≡ wk-pt πₗ (⇡ wk-val π' RHS)
                   eq = cong (⇡_) (sym (wk-val-trans RHS πₗ π'))
                   π≡' =  ⟦ γ₁ ⟧ᴱ
                        ≡⟨ π≡  ⟩
                          ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ
                        ≡⟨ cong ⟦ π' ⟧ʷ (sym (env-eq-sem ϖ))  ⟩
                          ⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                        ≡⟨ wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ ⟩
                          ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ ∎
                   M→M''' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) →ᵛ ∘ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇})
                   M→M''' = subst₂ (λ x y → ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = y})) {↥ = 🗇})) eq (uniq-bot ↥₀) (∙M∷l π≡' ((trans LHS≡M (cong ⟦ toVal M ⟧ᵛ (sym (env-eq-sem ϖ))))))
                 in
                 {!!} --Ψ , πₗ , γₗ , (⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇} , M→M''' , refl

  val-wk-lift-∙∘ {Ψ = Ψ} {M = ⭭ pa̲i̲r̲ LHS RHS} {γ = γ} {tail = ⇡ᴹ M N ⊲ γ₁ ∷ □} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = 🗆} (∙pair∷pm {X = X} {Y = Y} {Γ' = Γ₁} {π' = π'} {↥ = ↥₀} π≡ p₁M≡LHS p₂M≡RHS) {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vw =
                 let
                   eq0 : (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N) ≡ (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N))
                   eq0 =   (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N)
                          ≡⟨ refl ⟩
                           (⇡ wk-val (wk-trans (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π'))) N)
                          ≡⟨ cong (⇡_) (sym (wk-val-trans N (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π')))) ⟩
                           (⇡ wk-val (wk-cong (wk-cong πₗ)) (wk-val (wk-cong (wk-cong π')) N))
                          ≡⟨ refl ⟩
                           (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N)) ∎
                   eq1 : (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS)) ≡ (wk-v̲a̲l̲ (wk-wk πₗ) RHS)
                   eq1 =   (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS))
                          ≡⟨ wk-v̲a̲l̲-trans RHS (wk-wk wk-id) πₗ ⟩
                           (wk-v̲a̲l̲ (wk-trans (wk-wk wk-id) πₗ) RHS)
                          ≡⟨ refl ⟩
                           (wk-v̲a̲l̲ (wk-wk (wk-trans wk-id πₗ)) RHS)
                          ≡⟨ cong (λ x → wk-v̲a̲l̲ (wk-wk x) RHS) wk-trans-id ⟩
                           (wk-v̲a̲l̲ (wk-wk πₗ) RHS) ∎

                   π≡' =  ⟦ γ₁ ⟧ᴱ
                        ≡⟨ π≡  ⟩
                          ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ
                        ≡⟨ cong ⟦ π' ⟧ʷ (sym (env-eq-sem ϖ))  ⟩
                          ⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                        ≡⟨ wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ ⟩
                          ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ ∎

                   p₁M=LHS' : proj₁ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ≡ ⟦ wk-val πₗ (toVal LHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ
                   p₁M=LHS' =  proj₁ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
                              ≡⟨ p₁M≡LHS ⟩
                                ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ
                              ≡⟨ cong ⟦ toVal LHS ⟧ᵛ (sym (env-eq-sem ϖ)) ⟩
                                ⟦ toVal LHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                              ≡⟨ refl ⟩
                               ⟦ wk-val πₗ (toVal LHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ ∎

                   p₂M=RHS' : proj₂ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ≡ ⟦ wk-val πₗ (toVal RHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ
                   p₂M=RHS' =  proj₂ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
                              ≡⟨ p₂M≡RHS ⟩
                                ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ
                              ≡⟨ cong ⟦ toVal RHS ⟧ᵛ (sym (env-eq-sem ϖ)) ⟩
                                ⟦ toVal RHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                              ≡⟨ refl ⟩
                               ⟦ wk-val πₗ (toVal RHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ ∎

                   t : ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS) ∷ □
                   t = ∙pair∷pm {π' = wk-trans πₗ π'} π≡' p₁M=LHS' p₂M=RHS'

                   t' : ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ □)
                   t' = subst₂ (λ x y → ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ y ∷ □) {↥ = 🗆})) eq0 eq1 t
                 in
                 {!!} --Ψ ∙ X ∙ Y , wk-cong (wk-cong πₗ) , (γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS) , □ , t' , refl

  val-wk-lift-∙∘ {b = non-empty} {b' = non-empty} {Ψ = Ψ} {M = ⭭ pa̲i̲r̲ LHS RHS} {γ = γ} {tail = (⇡ᴹ M N ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇}} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = 🗇} (∙pair∷pm {X = X} {Y = Y} {Γ' = Γ₁} {b = non-empty} {π' = π'} {↥ = ↥₀} π≡ p₁M≡LHS p₂M≡RHS) {πₗ = πₗ} {γₗ = γₗ} ϖ tailₗ vw =
                 let
                   eq0 : (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N) ≡ (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N))
                   eq0 =   (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N)
                          ≡⟨ refl ⟩
                           (⇡ wk-val (wk-trans (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π'))) N)
                          ≡⟨ cong (⇡_) (sym (wk-val-trans N (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π')))) ⟩
                           (⇡ wk-val (wk-cong (wk-cong πₗ)) (wk-val (wk-cong (wk-cong π')) N))
                          ≡⟨ refl ⟩
                           (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N)) ∎
                   eq1 : (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS)) ≡ (wk-v̲a̲l̲ (wk-wk πₗ) RHS)
                   eq1 =   (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS))
                          ≡⟨ wk-v̲a̲l̲-trans RHS (wk-wk wk-id) πₗ ⟩
                           (wk-v̲a̲l̲ (wk-trans (wk-wk wk-id) πₗ) RHS)
                          ≡⟨ refl ⟩
                           (wk-v̲a̲l̲ (wk-wk (wk-trans wk-id πₗ)) RHS)
                          ≡⟨ cong (λ x → wk-v̲a̲l̲ (wk-wk x) RHS) wk-trans-id ⟩
                           (wk-v̲a̲l̲ (wk-wk πₗ) RHS) ∎

                   π≡' =  ⟦ γ₁ ⟧ᴱ
                        ≡⟨ π≡  ⟩
                          ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ
                        ≡⟨ cong ⟦ π' ⟧ʷ (sym (env-eq-sem ϖ))  ⟩
                          ⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                        ≡⟨ wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ ⟩
                          ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ ∎

                   p₁M=LHS' : proj₁ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ≡ ⟦ wk-val πₗ (toVal LHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ
                   p₁M=LHS' =  proj₁ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
                              ≡⟨ p₁M≡LHS ⟩
                                ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ
                              ≡⟨ cong ⟦ toVal LHS ⟧ᵛ (sym (env-eq-sem ϖ)) ⟩
                                ⟦ toVal LHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                              ≡⟨ refl ⟩
                               ⟦ wk-val πₗ (toVal LHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ ∎

                   p₂M=RHS' : proj₂ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ≡ ⟦ wk-val πₗ (toVal RHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ
                   p₂M=RHS' =  proj₂ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
                              ≡⟨ p₂M≡RHS ⟩
                                ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ
                              ≡⟨ cong ⟦ toVal RHS ⟧ᵛ (sym (env-eq-sem ϖ)) ⟩
                                ⟦ toVal RHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                              ≡⟨ refl ⟩
                               ⟦ wk-val πₗ (toVal RHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ ∎

                   t : ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ LHS RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∘ ((⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS) ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})
                   t = ∙pair∷pm {π' = wk-trans πₗ π'} π≡' p₁M=LHS' p₂M=RHS'

                   t' : ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ LHS RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∘ ((wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})
                   t' = subst₂ (λ x y → ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ (M₂ ⊲ γ₂ ∷ tail) {↥ = ↥}) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ y ∷ (M₂ ⊲ γ₂ ∷ tail) {↥ = ↥}) {↥ = 🗇})) eq0 eq1 t
                 in
                 {!!} --Ψ ∙ X ∙ Y , wk-cong (wk-cong πₗ) , (γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS) , ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥}) , t' , refl
  -}

  val-wk-lift-∙∘ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∙ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          -- → ⟦ ∙ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
          -- → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            -- Σ[ wk≡ᵣ ∈ ⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∙ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) →ᵛ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              --× ⟦ ∙ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ
              × (vs-height tail' ≡ vs-height tailᵣ))
  val-wk-lift-∙∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} () {πₗ = πₗ} {γₗ = γₗ} ϖ
  val-wk-lift-∙∘ {Ψ = Ψ} {M = ⭭ M} {γ = γ} {tail = ⇡ᴸ LHS RHS ⊲ γ₁ ∷ □} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = ((⇡ᴿ M) _ ⊲ γ ∷ □) {↥ = 🗆}} {↥' = 🗇} (∙M∷l {X = X} {Y = Y} {M = M} {LHS = LHS} {RHS = RHS} {π' = π'} π≡ LHS≡M) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                 let
                   eq : (⇡ wk-val (wk-trans πₗ π') RHS) ≡ wk-pt πₗ (⇡ wk-val π' RHS)
                   eq = cong (⇡_) (sym (wk-val-trans RHS πₗ π'))
                   π≡' : ⟦ γ₁ ⟧ᴱ ≡ ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ
                   π≡' =  ⟦ γ₁ ⟧ᴱ
                        ≡⟨ π≡  ⟩
                          ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ
                        ≡⟨ cong ⟦ π' ⟧ʷ (sym (env-eq-sem ϖ))  ⟩
                          ⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                        ≡⟨ wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ ⟩
                          ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ ∎
                   M→M'' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ (((⇡ wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇})
                   M→M'' = ∙M∷l π≡' (trans LHS≡M (cong ⟦ toVal M ⟧ᵛ (sym (env-eq-sem ϖ))))
                   M→M''' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇})
                   M→M''' = subst (λ x → ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇})) eq M→M''
                 in
                 Ψ , πₗ , γₗ , (⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆} , M→M''' , refl

  val-wk-lift-∙∘ {Ψ = Ψ} {M = ⭭ M} {γ = γ} {tail = ⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∙M∷l {M = M} {LHS = LHS} {RHS = RHS} {π' = π'} {↥ = ↥₀} π≡ LHS≡M) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                 let
                   eq : (⇡ wk-val (wk-trans πₗ π') RHS) ≡ wk-pt πₗ (⇡ wk-val π' RHS)
                   eq = cong (⇡_) (sym (wk-val-trans RHS πₗ π'))
                   π≡' =  ⟦ γ₁ ⟧ᴱ
                        ≡⟨ π≡  ⟩
                          ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ
                        ≡⟨ cong ⟦ π' ⟧ʷ (sym (env-eq-sem ϖ))  ⟩
                          ⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                        ≡⟨ wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ ⟩
                          ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ ∎
                   M→M''' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) →ᵛ ∘ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇})
                   M→M''' = subst₂ (λ x y → ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = y})) {↥ = 🗇})) eq (uniq-bot ↥₀) (∙M∷l π≡' ((trans LHS≡M (cong ⟦ toVal M ⟧ᵛ (sym (env-eq-sem ϖ))))))
                 in
                 Ψ , πₗ , γₗ , (⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇} , M→M''' , refl

  val-wk-lift-∙∘ {Ψ = Ψ} {M = ⭭ pa̲i̲r̲ LHS RHS} {γ = γ} {tail = ⇡ᴹ M N ⊲ γ₁ ∷ □} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = 🗆} (∙pair∷pm {X = X} {Y = Y} {Γ' = Γ₁} {π' = π'} {↥ = ↥₀} π≡ p₁M≡LHS p₂M≡RHS) {πₗ = πₗ} {γₗ = γₗ} ϖ = --{!!}
                 let
                   eq0 : (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N) ≡ (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N))
                   eq0 =   (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N)
                          ≡⟨ refl ⟩
                           (⇡ wk-val (wk-trans (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π'))) N)
                          ≡⟨ cong (⇡_) (sym (wk-val-trans N (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π')))) ⟩
                           (⇡ wk-val (wk-cong (wk-cong πₗ)) (wk-val (wk-cong (wk-cong π')) N))
                          ≡⟨ refl ⟩
                           (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N)) ∎
                   eq1 : (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS)) ≡ (wk-v̲a̲l̲ (wk-wk πₗ) RHS)
                   eq1 =   (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS))
                          ≡⟨ wk-v̲a̲l̲-trans RHS (wk-wk wk-id) πₗ ⟩
                           (wk-v̲a̲l̲ (wk-trans (wk-wk wk-id) πₗ) RHS)
                          ≡⟨ refl ⟩
                           (wk-v̲a̲l̲ (wk-wk (wk-trans wk-id πₗ)) RHS)
                          ≡⟨ cong (λ x → wk-v̲a̲l̲ (wk-wk x) RHS) wk-trans-id ⟩
                           (wk-v̲a̲l̲ (wk-wk πₗ) RHS) ∎

                   π≡' =  ⟦ γ₁ ⟧ᴱ
                        ≡⟨ π≡  ⟩
                          ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ
                        ≡⟨ cong ⟦ π' ⟧ʷ (sym (env-eq-sem ϖ))  ⟩
                          ⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                        ≡⟨ wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ ⟩
                          ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ ∎

                   p₁M=LHS' : proj₁ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ≡ ⟦ wk-val πₗ (toVal LHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ
                   p₁M=LHS' =  proj₁ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
                              ≡⟨ p₁M≡LHS ⟩
                                ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ
                              ≡⟨ cong ⟦ toVal LHS ⟧ᵛ (sym (env-eq-sem ϖ)) ⟩
                                ⟦ toVal LHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                              ≡⟨ refl ⟩
                               ⟦ wk-val πₗ (toVal LHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ ∎

                   p₂M=RHS' : proj₂ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ≡ ⟦ wk-val πₗ (toVal RHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ
                   p₂M=RHS' =  proj₂ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
                              ≡⟨ p₂M≡RHS ⟩
                                ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ
                              ≡⟨ cong ⟦ toVal RHS ⟧ᵛ (sym (env-eq-sem ϖ)) ⟩
                                ⟦ toVal RHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                              ≡⟨ refl ⟩
                               ⟦ wk-val πₗ (toVal RHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ ∎

                   t : ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS) ∷ □
                   t = ∙pair∷pm {π' = wk-trans πₗ π'} π≡' p₁M=LHS' p₂M=RHS'

                   t' : ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ □)
                   t' = subst₂ (λ x y → ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ y ∷ □) {↥ = 🗆})) eq0 eq1 t
                 in
                 Ψ ∙ X ∙ Y , wk-cong (wk-cong πₗ) , (γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS) , □ , t' , refl

  val-wk-lift-∙∘ {b = non-empty} {b' = non-empty} {Ψ = Ψ} {M = ⭭ pa̲i̲r̲ LHS RHS} {γ = γ} {tail = (⇡ᴹ M N ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇}} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = 🗇} (∙pair∷pm {X = X} {Y = Y} {Γ' = Γ₁} {b = non-empty} {π' = π'} {↥ = ↥₀} π≡ p₁M≡LHS p₂M≡RHS) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                 let
                   eq0 : (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N) ≡ (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N))
                   eq0 =   (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N)
                          ≡⟨ refl ⟩
                           (⇡ wk-val (wk-trans (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π'))) N)
                          ≡⟨ cong (⇡_) (sym (wk-val-trans N (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π')))) ⟩
                           (⇡ wk-val (wk-cong (wk-cong πₗ)) (wk-val (wk-cong (wk-cong π')) N))
                          ≡⟨ refl ⟩
                           (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N)) ∎
                   eq1 : (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS)) ≡ (wk-v̲a̲l̲ (wk-wk πₗ) RHS)
                   eq1 =   (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS))
                          ≡⟨ wk-v̲a̲l̲-trans RHS (wk-wk wk-id) πₗ ⟩
                           (wk-v̲a̲l̲ (wk-trans (wk-wk wk-id) πₗ) RHS)
                          ≡⟨ refl ⟩
                           (wk-v̲a̲l̲ (wk-wk (wk-trans wk-id πₗ)) RHS)
                          ≡⟨ cong (λ x → wk-v̲a̲l̲ (wk-wk x) RHS) wk-trans-id ⟩
                           (wk-v̲a̲l̲ (wk-wk πₗ) RHS) ∎

                   π≡' =  ⟦ γ₁ ⟧ᴱ
                        ≡⟨ π≡  ⟩
                          ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ
                        ≡⟨ cong ⟦ π' ⟧ʷ (sym (env-eq-sem ϖ))  ⟩
                          ⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                        ≡⟨ wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ ⟩
                          ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ ∎

                   p₁M=LHS' : proj₁ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ≡ ⟦ wk-val πₗ (toVal LHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ
                   p₁M=LHS' =  proj₁ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
                              ≡⟨ p₁M≡LHS ⟩
                                ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ
                              ≡⟨ cong ⟦ toVal LHS ⟧ᵛ (sym (env-eq-sem ϖ)) ⟩
                                ⟦ toVal LHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                              ≡⟨ refl ⟩
                               ⟦ wk-val πₗ (toVal LHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ ∎

                   p₂M=RHS' : proj₂ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ≡ ⟦ wk-val πₗ (toVal RHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ
                   p₂M=RHS' =  proj₂ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
                              ≡⟨ p₂M≡RHS ⟩
                                ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ
                              ≡⟨ cong ⟦ toVal RHS ⟧ᵛ (sym (env-eq-sem ϖ)) ⟩
                                ⟦ toVal RHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                              ≡⟨ refl ⟩
                               ⟦ wk-val πₗ (toVal RHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ ∎

                   t : ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ LHS RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∘ ((⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS) ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})
                   t = ∙pair∷pm {π' = wk-trans πₗ π'} π≡' p₁M=LHS' p₂M=RHS'

                   t' : ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ LHS RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∘ ((wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})
                   t' = subst₂ (λ x y → ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ (M₂ ⊲ γ₂ ∷ tail) {↥ = ↥}) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ y ∷ (M₂ ⊲ γ₂ ∷ tail) {↥ = ↥}) {↥ = 🗇})) eq0 eq1 t
                 in
                 Ψ ∙ X ∙ Y , wk-cong (wk-cong πₗ) , (γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS) , ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥}) , t' , refl

  ------

  val-wk-lift-∙∙ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∙ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          --→ ⟦ ∙ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
          --→ {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            --Σ[ wk≡ᵣ ∈ ⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∙ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) →ᵛ ∙ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              --× ⟦ ∙ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ
              × (vs-height tail' ≡ vs-height tailᵣ))
  val-wk-lift-∙∙ {Ψ = Ψ} {M = ⭭ M} {γ = γ} {tail = ⇡ᴿ LHS RHS ⊲ γ₁ ∷ □} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = □} {↥' = 🗆} (∙M∷r {M = M} {LHS = LHS} {RHS = RHS} {π' = π'} π≡ RHS≡M) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                 let
                   eq0 : (wk-v̲a̲l̲ (wk-trans πₗ π') LHS) ≡ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS))
                   eq0 = sym (wk-v̲a̲l̲-trans LHS πₗ π')
                   π≡' : ⟦ γ₁ ⟧ᴱ ≡ ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ
                   π≡' =  ⟦ γ₁ ⟧ᴱ
                        ≡⟨ π≡  ⟩
                          ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ
                        ≡⟨ cong ⟦ π' ⟧ʷ (sym (env-eq-sem ϖ))  ⟩
                          ⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                        ≡⟨ wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ ⟩
                          ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ ∎

                   t : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∙ ⭭ pa̲i̲r̲ (wk-v̲a̲l̲ (wk-trans πₗ π') LHS) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ □
                   t = ∙M∷r {π' = wk-trans πₗ π'} π≡' (trans RHS≡M (cong ⟦ toVal M ⟧ᵛ (sym (env-eq-sem ϖ))))

                   t' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS)) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ □) {↥ = 🗆})
                   t' = subst (λ x → ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∙ ((⭭ pa̲i̲r̲ x (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ □)) {↥ = 🗆}) eq0 t
                 in
                 Ψ , πₗ , γₗ , □ , t' , refl

  val-wk-lift-∙∙ {Ψ = Ψ} {M = ⭭ M} {γ = γ} {tail = ⇡ᴿ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail'') {↥ = ↥''})} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = (M₂ ⊲ γ₂ ∷ tail'') {↥ = ↥''}} {↥' = 🗇} (∙M∷r {M = M} {LHS = LHS} {RHS = RHS} {π' = π'} π≡ RHS≡M) {πₗ = πₗ} {γₗ = γₗ} ϖ =
                 let
                   eq0 : (wk-v̲a̲l̲ (wk-trans πₗ π') LHS) ≡ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS))
                   eq0 = sym (wk-v̲a̲l̲-trans LHS πₗ π')

                   π≡' =  ⟦ γ₁ ⟧ᴱ
                        ≡⟨ π≡  ⟩
                          ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ
                        ≡⟨ cong ⟦ π' ⟧ʷ (sym (env-eq-sem ϖ))  ⟩
                          ⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                        ≡⟨ wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ ⟩
                          ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ ∎

                   t : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail'') {↥ = ↥''})) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∙ ⭭ pa̲i̲r̲ (wk-v̲a̲l̲ (wk-trans πₗ π') LHS) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ (M₂ ⊲ γ₂ ∷ tail'')
                   t = ∙M∷r {π' = wk-trans πₗ π'} π≡' (trans RHS≡M (cong ⟦ toVal M ⟧ᵛ (sym (env-eq-sem ϖ))))

                   t' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ₁ ∷ (M₂ ⊲ γ₂ ∷ tail'')) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS)) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail'') {↥ = ↥''})) {↥ = 🗇})
                   t' = subst (λ x → ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail'') {↥ = ↥''})) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∙ ((⭭ pa̲i̲r̲ x (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ (M₂ ⊲ γ₂ ∷ tail'') {↥ = ↥''})) {↥ = 🗇}) eq0 t
                 in
                 Ψ , πₗ , γₗ , (M₂ ⊲ γ₂ ∷ tail'') , t' , refl

  {- OLD VERSIONS (correct, but probably unnecessarily complicated

  val-wk-lift-∘∘ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → ⟦ ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ wk≡ᵣ ∈ ⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) →ᵛ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              × ⟦ ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ
              × (vs-height tail' ≡ vs-height tailᵣ))
  val-wk-lift-∘∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘pair {LHS = LHS} {RHS = RHS}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , ⇡ᴸ (wk-val πₗ LHS) (wk-val πₗ RHS) ⊲ γₗ ∷ □ , ∘pair , refl , refl
  val-wk-lift-∘∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘pair {LHS = LHS} {RHS = RHS}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , ⇡ᴸ (wk-val πₗ LHS) (wk-val πₗ RHS) ⊲ γₗ ∷ M₁ ⊲ γ₁ ∷ tail , ∘pair , refl , refl
  val-wk-lift-∘∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘pm {M = Mₚ} {N = Nₚ}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , ⇡ᴹ (wk-val πₗ Mₚ) (wk-val (wk-cong (wk-cong πₗ)) Nₚ) ⊲ γₗ ∷ □ , ∘pm , refl , refl
  val-wk-lift-∘∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘pm {M = Mₚ} {N = Nₚ}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , πₗ , γₗ , wk≡ₗ , ⇡ᴹ (wk-val πₗ Mₚ) (wk-val (wk-cong (wk-cong πₗ)) Nₚ) ⊲ γₗ ∷ M₁ ⊲ γ₁ ∷ tail , ∘pm , refl , refl

  --
  val-wk-lift-∘∙ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → ⟦ ∘ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → Σ[ Ψ' ∈ Ctx ]
            --
            Σ[ Γ'' ∈ Ctx ]
            Σ[ M'' ∈ PartialTerm Γ'' X' ]
            Σ[ πᵣ ∈ Wk Ψ' Γ'' ]
            Σ[ πᵥ ∈ Wk Γ' Γ'' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) →ᵛ ∙ (((wk-pt πᵣ M'') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              × ⟦ ∘ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ (((wk-pt πᵣ M'') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ
                × (wk-pt πᵥ M'' ≡ M')
                × (vs-height tail' ≡ vs-height tailᵣ))
  val-wk-lift-∘∙ {Γ = Γ} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘var-c {i = i}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , Γ' , M' , πₗ , wk-id , γₗ , □ , ∘var-c , refl , wk-pt-id (⭭ v̲a̲r̲ i) , refl
  val-wk-lift-∘∙ {Γ = Γ} {X = X} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘var {Γ = Γ₁} {Γ' = Γ₂} {γ = γ₁} {γ' = γ₂} {i = i} {M = M₁} L→L' πᵥ extᵥ weᵥ ϖᵥ H) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                    a0 : EnvEq wk-id γ γ
                    a0 = enveq-id
                    a1 : EnvEq πₜ γ γ
                    a1 = subst (λ x → EnvEq x γ γ) (sym wk-id-id) a0

                    a2 = li≡i L→L' H
                    a3 : EnvExt i γ (γ₂ ﹐ M₁)
                    a3 = subst (λ x → EnvExt x γ (γ₂ ﹐ M₁)) a2 extᵥ

                    b0 = lookup-wk-lift i M₁ a3 L→L' H πₗ γₗ ϖ

                    Ψ' = proj₁ b0
                    πᵣ = proj₁ (proj₂ b0)
                    π' = proj₁ (proj₂ (proj₂ b0))
                    γᵣ = proj₁ (proj₂ (proj₂ (proj₂ b0)))
                    L→L↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ b0))))
                    LH↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))
                    ext↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0))))))
                    we↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))))
                    ϖ↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0))))))))
                    S≡T↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))))))
                    π≡↑ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))))))

                    e1 : ∘ (⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ □ →ᵛ ∙ (⭭ wk-v̲a̲l̲ π' (wk-v̲a̲l̲ πᵣ M₁)) ⊲ γₗ ∷ □
                    e1 = ∘var {T◾ = X} {γ' = γᵣ} {i = wk-mem πₗ i} {tail = □} {↥ = 🗆} {M = wk-v̲a̲l̲ πᵣ M₁} L→L↑ π' ext↑ we↑ ϖ↑ LH↑

                    goal : ∘ (⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ □ →ᵛ ∙ (⭭ wk-v̲a̲l̲ (wk-trans π' πᵣ) M₁) ⊲ γₗ ∷ □
                    goal = subst (λ x → ∘ (((⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ □) {↥ = 🗆}) →ᵛ ∙ (((⭭ x) ⊲ γₗ ∷ □) {↥ = 🗆})) (wk-v̲a̲l̲-trans M₁ π' πᵣ) e1

                    eq : ⟦ ∘ ((wk-pt πₗ (⇡ var i) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ≡ ⟦ ∙ ((wk-pt (wk-trans π' πᵣ) (⭭ M₁) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ
                    eq =      ⟦ ∘ ((wk-pt πₗ (⇡ var i) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ
                            ≡⟨ refl ⟩
                               ⟦ wk-mem πₗ i ⟧ᵐ ⟦ γₗ ⟧ᴱ
                            ≡⟨ S≡T↑ ⟩
                               ⟦ ⟨ h ∥ γᵣ ﹐ wk-v̲a̲l̲ πᵣ M₁ ⟩ ⟧ᴸ
                            ≡⟨ refl ⟩
                               ⟦ toVal M₁ ⟧ᵛ (⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ)
                            ≡⟨ cong (λ x → ⟦ toVal M₁ ⟧ᵛ (⟦ πᵣ ⟧ʷ x)) (sym π≡↑) ⟩
                                ⟦ toVal M₁ ⟧ᵛ (⟦ πᵣ ⟧ʷ (⟦ π' ⟧ʷ ⟦ γₗ ⟧ᴱ))
                            ≡⟨ refl ⟩
                              ⟦ ∙ (((⭭ wk-v̲a̲l̲ π' (wk-v̲a̲l̲ πᵣ M₁)) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ
                            ≡⟨ cong (λ x → ⟦ ∙ ((⭭ x ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ) (wk-v̲a̲l̲-trans M₁ π' πᵣ) ⟩
                              ⟦ ∙ (((⭭ wk-v̲a̲l̲ (wk-trans π' πᵣ) M₁) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ∎
                 in
                 Ψ , Γ₂ , (⭭ M₁) , wk-trans π' πᵣ , πᵥ , γₗ , □ , goal , eq , refl , refl
  val-wk-lift-∘∙ {Γ = Γ} {X = X} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘lam {M = W}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , Γ' , M' , πₗ , wk-id , γₗ , □ , ∘lam , refl , (wk-pt-id (⭭ l̲a̲m̲ W)) , refl
  val-wk-lift-∘∙ {Γ = Γ} {X = X} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} ∘unit Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , Γ , ⭭ u̲n̲i̲t̲ , πₗ , wk-id , γₗ , □ , ∘unit , Q≡Q' , refl , refl
  val-wk-lift-∘∙ {Γ = Γ} {X = X} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘var-c {i = i}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = Ψ , Γ , ⭭ v̲a̲r̲ i , πₗ , wk-id , γₗ , M₁ ⊲ γ₁ ∷ tail , ∘var-c , Q≡Q' , wk-pt-id (⭭ v̲a̲r̲ i) , refl
  val-wk-lift-∘∙ {Ψ = Ψ} {M = M} {γ = γ} {tail = ((M₀ ⊲ γ₀ ∷ tail) {↥ = ↥})} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘var {Γ = Γ₁} {T◾ = T◾} {Γ' = Γ₂} {γ = γ₁} {γ' = γ₂} {i = i} {M = M₁} L→L' πᵥ extᵥ weᵥ ϖᵥ H) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                    a2 = li≡i L→L' H
                    a3 : EnvExt i γ (γ₂ ﹐ M₁)
                    a3 = subst (λ x → EnvExt x γ (γ₂ ﹐ M₁)) a2 extᵥ

                    b0 = lookup-wk-lift i M₁ a3 L→L' H πₗ γₗ ϖ
                    Ψ' = proj₁ b0
                    πᵣ = proj₁ (proj₂ b0)
                    π' = proj₁ (proj₂ (proj₂ b0))
                    γᵣ = proj₁ (proj₂ (proj₂ (proj₂ b0)))
                    L→L↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ b0))))
                    LH↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))
                    ext↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0))))))
                    we↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))))
                    ϖ↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0))))))))
                    S≡T↑ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))))))
                    π≡↑ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ b0)))))))))

                    e1 : ∘ (⇡ var (wk-mem πₗ i)) ⊲ γₗ ∷ M₀ ⊲ γ₀ ∷ tail →ᵛ ∙ (⭭ wk-v̲a̲l̲ π' (wk-v̲a̲l̲ πᵣ M₁)) ⊲ γₗ ∷ M₀ ⊲ γ₀ ∷ tail
                    e1 = ∘var {T◾ = T◾} {γ' = γᵣ} {i = wk-mem πₗ i} {tail = ((M₀ ⊲ γ₀ ∷ tail) {↥ = ↥})} {↥ = 🗇} {M = wk-v̲a̲l̲ πᵣ M₁} L→L↑ π' ext↑ we↑ ϖ↑ LH↑

                    goal : ∘ wk-pt πₗ (⇡ var i) ⊲ γₗ ∷ M₀ ⊲ γ₀ ∷ tail →ᵛ ∙ (⭭ wk-v̲a̲l̲ (wk-trans π' πᵣ) M₁) ⊲ γₗ ∷ M₀ ⊲ γ₀ ∷ tail
                    goal = subst (λ x → ∘ ((wk-pt πₗ (⇡ var i) ⊲ γₗ ∷ ((M₀ ⊲ γ₀ ∷ tail) {↥ = ↥})) {↥ = 🗇}) →ᵛ ∙ (((⭭ x) ⊲ γₗ ∷ ((M₀ ⊲ γ₀ ∷ tail)) {↥ = ↥})) {↥ = 🗇}) (wk-v̲a̲l̲-trans M₁ π' πᵣ) e1

                 in
                 Ψ , Γ₂ , ⭭ M₁ , wk-trans π' πᵣ , πᵥ , γₗ , (M₀ ⊲ γ₀ ∷ tail) , goal , Q≡Q' , refl , refl
  val-wk-lift-∘∙ {Γ = Γ} {X = X} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∘lam {M = W}) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , Γ , ⭭ V̲a̲l̲.l̲a̲m̲ W , πₗ , wk-id , γₗ , M₁ ⊲ γ₁ ∷ tail , ∘lam , Q≡Q' , (wk-pt-id (⭭ l̲a̲m̲ W)) , refl
  val-wk-lift-∘∙ {Γ = Γ} {X = X} {Γ' = Γ'} {Ψ = Ψ} {M = M} {γ = γ} {tail = M₁ ⊲ γ₁ ∷ tail} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} ∘unit Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 Ψ , Γ , ⭭ u̲n̲i̲t̲ , πₗ , wk-id , γₗ , M₁ ⊲ γ₁ ∷ tail , ∘unit , Q≡Q' , refl , refl

  --

  val-wk-lift-∙∘ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∙ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → ⟦ ∙ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∘ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ wk≡ᵣ ∈ ⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∙ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) →ᵛ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              × ⟦ ∙ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∘ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ
              × (vs-height tail' ≡ vs-height tailᵣ))
  val-wk-lift-∙∘ {Ψ = Ψ} {M = M} {γ = γ} {tail = □} {↥ = 🗆} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} () Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ}
  val-wk-lift-∙∘ {Ψ = Ψ} {M = ⭭ M} {γ = γ} {tail = ⇡ᴸ LHS RHS ⊲ γ₁ ∷ □} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = ((⇡ᴿ M) _ ⊲ γ ∷ □) {↥ = 🗆}} {↥' = 🗇} (∙M∷l {X = X} {Y = Y} {M = M} {LHS = LHS} {RHS = RHS} {π' = π'} π≡ LHS≡M) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                   eq : (⇡ wk-val (wk-trans πₗ π') RHS) ≡ wk-pt πₗ (⇡ wk-val π' RHS)
                   eq = cong (⇡_) (sym (wk-val-trans RHS πₗ π'))
                   π≡' : ⟦ γ₁ ⟧ᴱ ≡ ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ
                   π≡' =  ⟦ γ₁ ⟧ᴱ
                        ≡⟨ π≡  ⟩
                          ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ
                        ≡⟨ cong ⟦ π' ⟧ʷ (sym wk≡ₗ)  ⟩
                          ⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                        ≡⟨ wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ ⟩
                          ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ ∎
                   M→M'' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ (((⇡ wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇})
                   M→M'' = ∙M∷l π≡' (trans LHS≡M (cong ⟦ toVal M ⟧ᵛ (sym wk≡ₗ)))
                   M→M''' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇})
                   M→M''' = subst (λ x → ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇})) eq M→M''
                 in
                 Ψ , πₗ , γₗ , wk≡ₗ , (⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆} , M→M''' ,
                 ( ⟦ ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ
                 ≡⟨ refl ⟩
                   ⟦ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                   ⟦ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆}) ⟧ᵛˢ
                 ≡⟨ Q≡Q' ⟩
                   (⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ))
                 ≡⟨ cong (λ x → (⟦ toVal M ⟧ᵛ x , ⟦ RHS ⟧ᵛ (⟦ π' ⟧ʷ x))) (sym wk≡ₗ)  ⟩
                   (⟦ toVal M ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)))
                 ≡⟨ cong (λ x → (⟦ toVal M ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) , ⟦ RHS ⟧ᵛ x)) (wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ)  ⟩
                   ⟦ toVal M ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ)
                 ≡⟨ refl ⟩
                   ⟦ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                   ⟦ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                  ⟦ ∘ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ ∎ ) ,
                 refl

  val-wk-lift-∙∘ {Ψ = Ψ} {M = ⭭ M} {γ = γ} {tail = ⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = ↥'} (∙M∷l {M = M} {LHS = LHS} {RHS = RHS} {π' = π'} {↥ = ↥₀} π≡ LHS≡M) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                   eq : (⇡ wk-val (wk-trans πₗ π') RHS) ≡ wk-pt πₗ (⇡ wk-val π' RHS)
                   eq = cong (⇡_) (sym (wk-val-trans RHS πₗ π'))
                   π≡' =  ⟦ γ₁ ⟧ᴱ
                        ≡⟨ π≡  ⟩
                          ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ
                        ≡⟨ cong ⟦ π' ⟧ʷ (sym wk≡ₗ)  ⟩
                          ⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                        ≡⟨ wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ ⟩
                          ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ ∎
                   M→M''' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) →ᵛ ∘ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇})
                   M→M''' = subst₂ (λ x y → ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = y})) {↥ = 🗇})) eq (uniq-bot ↥₀) (∙M∷l π≡' ((trans LHS≡M (cong ⟦ toVal M ⟧ᵛ (sym wk≡ₗ)))))
                 in
                 Ψ , πₗ , γₗ , wk≡ₗ , (⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇} , M→M''' ,

                 ( ⟦ ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) ⟧ᵛꟴ
                 ≡⟨ refl ⟩
                   ⟦ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                   ⟦ ((⇡ᴸ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀}) ⟧ᵛˢ
                 ≡⟨ Q≡Q' ⟩
                   ⟦ ∘ ((⇡ wk-val π' RHS ⊲ γ ∷ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀})) {↥ = 🗇}) ⟧ᵛꟴ
                 ≡⟨ refl ⟩
                   ⟦ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = ↥₀}) ⟧ᵛˢ
                 ≡⟨ cong (λ x → ⟦ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = x}) ⟧ᵛˢ) (uniq-bot ↥₀) ⟩
                   ⟦ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                   ⟦ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                  ⟦ ∘ ((wk-pt πₗ (⇡ wk-val π' RHS) ⊲ γₗ ∷ ((⇡ᴿ (wk-v̲a̲l̲ πₗ M) (wk-val (wk-trans πₗ π') RHS) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇}) ⟧ᵛꟴ ∎ ) ,
                 refl

  val-wk-lift-∙∘ {Ψ = Ψ} {M = ⭭ pa̲i̲r̲ LHS RHS} {γ = γ} {tail = ⇡ᴹ M N ⊲ γ₁ ∷ □} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = 🗆} (∙pair∷pm {X = X} {Y = Y} {Γ' = Γ₁} {π' = π'} {↥ = ↥₀} π≡ p₁M≡LHS p₂M≡RHS) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                   eq0 : (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N) ≡ (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N))
                   eq0 =   (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N)
                          ≡⟨ refl ⟩
                           (⇡ wk-val (wk-trans (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π'))) N)
                          ≡⟨ cong (⇡_) (sym (wk-val-trans N (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π')))) ⟩
                           (⇡ wk-val (wk-cong (wk-cong πₗ)) (wk-val (wk-cong (wk-cong π')) N))
                          ≡⟨ refl ⟩
                           (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N)) ∎
                   eq1 : (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS)) ≡ (wk-v̲a̲l̲ (wk-wk πₗ) RHS)
                   eq1 =   (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS))
                          ≡⟨ wk-v̲a̲l̲-trans RHS (wk-wk wk-id) πₗ ⟩
                           (wk-v̲a̲l̲ (wk-trans (wk-wk wk-id) πₗ) RHS)
                          ≡⟨ refl ⟩
                           (wk-v̲a̲l̲ (wk-wk (wk-trans wk-id πₗ)) RHS)
                          ≡⟨ cong (λ x → wk-v̲a̲l̲ (wk-wk x) RHS) wk-trans-id ⟩
                           (wk-v̲a̲l̲ (wk-wk πₗ) RHS) ∎

                   π≡' =  ⟦ γ₁ ⟧ᴱ
                        ≡⟨ π≡  ⟩
                          ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ
                        ≡⟨ cong ⟦ π' ⟧ʷ (sym wk≡ₗ)  ⟩
                          ⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                        ≡⟨ wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ ⟩
                          ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ ∎

                   p₁M=LHS' : proj₁ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ≡ ⟦ wk-val πₗ (toVal LHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ
                   p₁M=LHS' =  proj₁ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
                              ≡⟨ p₁M≡LHS ⟩
                                ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ
                              ≡⟨ cong ⟦ toVal LHS ⟧ᵛ (sym wk≡ₗ) ⟩
                                ⟦ toVal LHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                              ≡⟨ refl ⟩
                               ⟦ wk-val πₗ (toVal LHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ ∎

                   p₂M=RHS' : proj₂ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ≡ ⟦ wk-val πₗ (toVal RHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ
                   p₂M=RHS' =  proj₂ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
                              ≡⟨ p₂M≡RHS ⟩
                                ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ
                              ≡⟨ cong ⟦ toVal RHS ⟧ᵛ (sym wk≡ₗ) ⟩
                                ⟦ toVal RHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                              ≡⟨ refl ⟩
                               ⟦ wk-val πₗ (toVal RHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ ∎

                   t : ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS) ∷ □
                   t = ∙pair∷pm {π' = wk-trans πₗ π'} π≡' p₁M=LHS' p₂M=RHS'

                   t' : ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ □)
                   t' = subst₂ (λ x y → ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ y ∷ □) {↥ = 🗆})) eq0 eq1 t

                 in
                 Ψ ∙ X ∙ Y , wk-cong (wk-cong πₗ) , (γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS) ,
                 ( ⟦ wk-cong (wk-cong πₗ) ⟧ʷ ⟦ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ⟧ᴱ
                  ≡⟨ refl ⟩
                   (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)) , ⟦ toVal RHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                  ≡⟨ cong (λ x → (x , ⟦ toVal LHS ⟧ᵛ x) , ⟦ toVal RHS ⟧ᵛ x) wk≡ₗ ⟩
                   (⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ
                  ≡⟨ refl ⟩
                    ⟦ γ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ⟧ᴱ ∎ ) ,
                 □ , t' ,
                 ( ⟦ ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ LHS RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ
                 ≡⟨ refl ⟩
                    ⟦ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                    ⟦ (⇡ᴹ M N ⊲ γ₁ ∷ □) {↥ = 🗆} ⟧ᵛˢ
                 ≡⟨ Q≡Q' ⟩
                   ⟦ ((⇡ wk-val (wk-cong (wk-cong π')) N ⊲ γ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ∷ □) {↥ = 🗆}) ⟧ᵛˢ
                 ≡⟨ refl ⟩
                   ⟦ N ⟧ᵛ ((⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ)
                 ≡⟨ cong (λ x → ⟦ N ⟧ᵛ ((⟦ π' ⟧ʷ x , ⟦ toVal LHS ⟧ᵛ x) , ⟦ toVal RHS ⟧ᵛ x)) (sym wk≡ₗ) ⟩
                   ⟦ N ⟧ᵛ ((⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)) , ⟦ toVal RHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ))
                 ≡⟨ refl ⟩
                   ⟦ (⇡ wk-val (wk-cong (wk-cong πₗ)) (wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ □) {↥ = 🗆} ⟧ᵛˢ
                 ≡⟨ refl ⟩
                   ⟦ ∘ ((wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ∎ ) ,
                 refl


  val-wk-lift-∙∘ {b = non-empty} {b' = non-empty} {Ψ = Ψ} {M = ⭭ pa̲i̲r̲ LHS RHS} {γ = γ} {tail = (⇡ᴹ M N ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇}} {↥ = 🗇} {M' = M'} {γ' = γ'} {tail' = tail'} {↥' = 🗇} (∙pair∷pm {X = X} {Y = Y} {Γ' = Γ₁} {b = non-empty} {π' = π'} {↥ = ↥₀} π≡ p₁M≡LHS p₂M≡RHS) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} = --{!!}
                 let
                   eq0 : (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N) ≡ (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N))
                   eq0 =   (⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N)
                          ≡⟨ refl ⟩
                           (⇡ wk-val (wk-trans (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π'))) N)
                          ≡⟨ cong (⇡_) (sym (wk-val-trans N (wk-cong (wk-cong πₗ)) (wk-cong (wk-cong π')))) ⟩
                           (⇡ wk-val (wk-cong (wk-cong πₗ)) (wk-val (wk-cong (wk-cong π')) N))
                          ≡⟨ refl ⟩
                           (wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N)) ∎
                   eq1 : (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS)) ≡ (wk-v̲a̲l̲ (wk-wk πₗ) RHS)
                   eq1 =   (wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS))
                          ≡⟨ wk-v̲a̲l̲-trans RHS (wk-wk wk-id) πₗ ⟩
                           (wk-v̲a̲l̲ (wk-trans (wk-wk wk-id) πₗ) RHS)
                          ≡⟨ refl ⟩
                           (wk-v̲a̲l̲ (wk-wk (wk-trans wk-id πₗ)) RHS)
                          ≡⟨ cong (λ x → wk-v̲a̲l̲ (wk-wk x) RHS) wk-trans-id ⟩
                           (wk-v̲a̲l̲ (wk-wk πₗ) RHS) ∎

                   π≡' =  ⟦ γ₁ ⟧ᴱ
                        ≡⟨ π≡  ⟩
                          ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ
                        ≡⟨ cong ⟦ π' ⟧ʷ (sym wk≡ₗ)  ⟩
                          ⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                        ≡⟨ wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ ⟩
                          ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ ∎

                   p₁M=LHS' : proj₁ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ≡ ⟦ wk-val πₗ (toVal LHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ
                   p₁M=LHS' =  proj₁ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
                              ≡⟨ p₁M≡LHS ⟩
                                ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ
                              ≡⟨ cong ⟦ toVal LHS ⟧ᵛ (sym wk≡ₗ) ⟩
                                ⟦ toVal LHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                              ≡⟨ refl ⟩
                               ⟦ wk-val πₗ (toVal LHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ ∎

                   p₂M=RHS' : proj₂ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ≡ ⟦ wk-val πₗ (toVal RHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ
                   p₂M=RHS' =  proj₂ (⟦ M ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
                              ≡⟨ p₂M≡RHS ⟩
                                ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ
                              ≡⟨ cong ⟦ toVal RHS ⟧ᵛ (sym wk≡ₗ) ⟩
                                ⟦ toVal RHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                              ≡⟨ refl ⟩
                               ⟦ wk-val πₗ (toVal RHS) ⟧ᵛ ⟦ γₗ ⟧ᴱ ∎

                   t : ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ LHS RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∘ ((⇡ wk-val (wk-cong (wk-cong (wk-trans πₗ π'))) N ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) (wk-v̲a̲l̲ πₗ RHS) ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})
                   t = ∙pair∷pm {π' = wk-trans πₗ π'} π≡' p₁M=LHS' p₂M=RHS'

                   t' : ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ LHS RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∘ ((wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})
                   t' = subst₂ (λ x y → ∙ (((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ LHS) (wk-v̲a̲l̲ πₗ RHS)) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ (M₂ ⊲ γ₂ ∷ tail) {↥ = ↥}) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∘ ((x ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ y ∷ (M₂ ⊲ γ₂ ∷ tail) {↥ = ↥}) {↥ = 🗇})) eq0 eq1 t
                 in
                 Ψ ∙ X ∙ Y , wk-cong (wk-cong πₗ) , (γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS) ,
                 ( ⟦ wk-cong (wk-cong πₗ) ⟧ʷ ⟦ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ⟧ᴱ
                  ≡⟨ refl ⟩
                   (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)) , ⟦ toVal RHS ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                  ≡⟨ cong (λ x → (x , ⟦ toVal LHS ⟧ᵛ x) , ⟦ toVal RHS ⟧ᵛ x) wk≡ₗ ⟩
                  (⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ ⟧ᴱ
                  ≡⟨ refl ⟩
                  ⟦ γ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ⟧ᴱ ∎ ) ,
                  ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥}) ,
                  t' ,
                  ( ⟦ ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ LHS RHS) ⊲ γₗ ∷ ((⇡ᴹ M N ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇})) {↥ = 🗇}) ⟧ᵛꟴ
                  ≡⟨ Q≡Q' ⟩
                   ⟦ ((⇡ wk-val (wk-cong (wk-cong π')) N ⊲ γ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇}) ⟧ᵛˢ
                  ≡⟨ refl ⟩
                   ⟦ ∘ ((wk-pt (wk-cong (wk-cong πₗ)) (⇡ wk-val (wk-cong (wk-cong π')) N) ⊲ γₗ ﹐ wk-v̲a̲l̲ πₗ LHS ﹐ wk-v̲a̲l̲ (wk-wk πₗ) RHS ∷ ((M₂ ⊲ γ₂ ∷ tail) {↥ = ↥})) {↥ = 🗇}) ⟧ᵛꟴ ∎) ,
                  refl


  val-wk-lift-∙∙ : {M : PartialTerm Γ X} {γ : Env Γ} {tail : ValStack b T◾} {↥ : BottomTypeEqualsNextType b X T◾} {M' : PartialTerm Γ' X'} {γ' : Env Γ'} {tail' : ValStack b' T◾} {↥' : BottomTypeEqualsNextType b' X' T◾}
          → ∙ ((M ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'})
          → ⟦ ∙ ((M ⊲ γ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ ((M' ⊲ γ' ∷ tail') {↥ = ↥'}) ⟧ᵛꟴ
          → {πₜ : Wk Γ' Γ} → {πₗ : Wk Ψ Γ} → {γₗ : Env Ψ} → EnvEq πₗ γₗ γ → {wk≡ₗ : ⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ ≡ ⟦ γ ⟧ᴱ}
          → Σ[ Ψ' ∈ Ctx ]
            Σ[ πᵣ ∈ Wk Ψ' Γ' ]
            Σ[ γᵣ ∈ Env Ψ' ]
            Σ[ wk≡ᵣ ∈ ⟦ πᵣ ⟧ʷ ⟦ γᵣ ⟧ᴱ ≡ ⟦ γ' ⟧ᴱ ]
            Σ[ tailᵣ ∈ ValStack b' T◾ ]
            ( ∙ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) →ᵛ ∙ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'})
              × ⟦ ∙ (((wk-pt πₗ M) ⊲ γₗ ∷ tail) {↥ = ↥}) ⟧ᵛꟴ ≡ ⟦ ∙ (((wk-pt πᵣ M') ⊲ γᵣ ∷ tailᵣ) {↥ = ↥'}) ⟧ᵛꟴ
              × (vs-height tail' ≡ vs-height tailᵣ))
  val-wk-lift-∙∙ {Ψ = Ψ} {M = ⭭ M} {γ = γ} {tail = ⇡ᴿ LHS RHS ⊲ γ₁ ∷ □} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = □} {↥' = 🗆} (∙M∷r {M = M} {LHS = LHS} {RHS = RHS} {π' = π'} π≡ RHS≡M) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                   eq0 : (wk-v̲a̲l̲ (wk-trans πₗ π') LHS) ≡ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS))
                   eq0 = sym (wk-v̲a̲l̲-trans LHS πₗ π')
                   π≡' : ⟦ γ₁ ⟧ᴱ ≡ ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ
                   π≡' =  ⟦ γ₁ ⟧ᴱ
                        ≡⟨ π≡  ⟩
                          ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ
                        ≡⟨ cong ⟦ π' ⟧ʷ (sym wk≡ₗ)  ⟩
                          ⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                        ≡⟨ wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ ⟩
                          ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ ∎

                   t : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∙ ⭭ pa̲i̲r̲ (wk-v̲a̲l̲ (wk-trans πₗ π') LHS) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ □
                   t = ∙M∷r {π' = wk-trans πₗ π'} π≡' (trans RHS≡M (cong ⟦ toVal M ⟧ᵛ (sym wk≡ₗ)))

                   t' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS)) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ □) {↥ = 🗆})
                   t' = subst (λ x → ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) →ᵛ ∙ ((⭭ pa̲i̲r̲ x (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ □)) {↥ = 🗆}) eq0 t
                 in
                 Ψ , πₗ , γₗ , wk≡ₗ , □ , t' ,
                 ( ⟦ ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆})) {↥ = 🗇}) ⟧ᵛꟴ
                  ≡⟨ refl ⟩
                   ⟦ ((⇡ᴿ LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆}) ⟧ᵛˢ
                  ≡⟨ Q≡Q' ⟩
                    ⟦ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M ⊲ γ ∷ □) {↥ = 🗆}) ⟧ᵛˢ
                  ≡⟨ refl ⟩
                    ⟦ toVal LHS ⟧ᵛ (⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ
                  ≡⟨ cong (λ x → ⟦ toVal LHS ⟧ᵛ (⟦ π' ⟧ʷ x) , ⟦ toVal M ⟧ᵛ x) (sym wk≡ₗ) ⟩
                    ⟦ toVal LHS ⟧ᵛ (⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)) , ⟦ toVal M ⟧ᵛ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                  ≡⟨ refl ⟩
                   ⟦ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS)) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛˢ
                  ≡⟨ refl ⟩
                   ⟦ ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M) ⊲ γₗ ∷ □) {↥ = 🗆}) ⟧ᵛꟴ ∎ ) ,
                  refl

  val-wk-lift-∙∙ {Ψ = Ψ} {M = ⭭ M} {γ = γ} {tail = ⇡ᴿ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail'') {↥ = ↥''})} {↥ = ↥} {M' = M'} {γ' = γ'} {tail' = (M₂ ⊲ γ₂ ∷ tail'') {↥ = ↥''}} {↥' = 🗇} (∙M∷r {M = M} {LHS = LHS} {RHS = RHS} {π' = π'} π≡ RHS≡M) Q≡Q' {πₜ = πₜ} {πₗ = πₗ} {γₗ = γₗ} ϖ {wk≡ₗ = wk≡ₗ} =
                 let
                   eq0 : (wk-v̲a̲l̲ (wk-trans πₗ π') LHS) ≡ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS))
                   eq0 = sym (wk-v̲a̲l̲-trans LHS πₗ π')

                   π≡' =  ⟦ γ₁ ⟧ᴱ
                        ≡⟨ π≡  ⟩
                          ⟦ π' ⟧ʷ ⟦ γ ⟧ᴱ
                        ≡⟨ cong ⟦ π' ⟧ʷ (sym wk≡ₗ)  ⟩
                          ⟦ π' ⟧ʷ (⟦ πₗ ⟧ʷ ⟦ γₗ ⟧ᴱ)
                        ≡⟨ wk-sem-trans πₗ π' ⟦ γₗ ⟧ᴱ ⟩
                          ⟦ wk-trans πₗ π' ⟧ʷ ⟦ γₗ ⟧ᴱ ∎

                   t : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail'') {↥ = ↥''})) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∙ ⭭ pa̲i̲r̲ (wk-v̲a̲l̲ (wk-trans πₗ π') LHS) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ (M₂ ⊲ γ₂ ∷ tail'')
                   t = ∙M∷r {π' = wk-trans πₗ π'} π≡' (trans RHS≡M (cong ⟦ toVal M ⟧ᵛ (sym wk≡ₗ)))

                   t' : ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ₁ ∷ (M₂ ⊲ γ₂ ∷ tail'')) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS)) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ ((M₂ ⊲ γ₂ ∷ tail'') {↥ = ↥''})) {↥ = 🗇})
                   t' = subst (λ x → ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ₁ ∷ ((M₂ ⊲ γ₂ ∷ tail'') {↥ = ↥''})) {↥ = 🗇})) {↥ = 🗇}) →ᵛ ∙ ((⭭ pa̲i̲r̲ x (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ (M₂ ⊲ γ₂ ∷ tail'') {↥ = ↥''})) {↥ = 🗇}) eq0 t
                 in
                 Ψ , πₗ , γₗ , wk≡ₗ , (M₂ ⊲ γ₂ ∷ tail'') , t' ,
                 ( ⟦ ∙ ((wk-pt πₗ (⭭ M) ⊲ γₗ ∷ ((⇡ᴿ LHS RHS ⊲ γ₁ ∷ (M₂ ⊲ γ₂ ∷ tail'')) {↥ = 🗇})) {↥ = 🗇}) ⟧ᵛꟴ
                  ≡⟨ refl ⟩
                   ⟦ ((⇡ᴿ LHS RHS ⊲ γ₁ ∷ (M₂ ⊲ γ₂ ∷ tail'')) {↥ = 🗇}) ⟧ᵛˢ
                  ≡⟨ Q≡Q' ⟩
                   ⟦ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M ⊲ γ ∷ (M₂ ⊲ γ₂ ∷ tail'')) {↥ = 🗇}) ⟧ᵛˢ
                  ≡⟨ refl ⟩
                   ⟦ M₂ ⊲ γ₂ ∷ tail'' ⟧ᵛˢ
                  ≡⟨ refl ⟩
                   ⟦ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πₗ (wk-v̲a̲l̲ π' LHS)) (wk-v̲a̲l̲ πₗ M) ⊲ γₗ ∷ (M₂ ⊲ γ₂ ∷ tail'')) {↥ = 🗇}) ⟧ᵛˢ
                  ≡⟨ refl ⟩
                   ⟦ ∙ ((wk-pt πₗ (⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M) ⊲ γₗ ∷ (M₂ ⊲ γ₂ ∷ tail'')) {↥ = 🗇}) ⟧ᵛꟴ ∎ ) ,
                 refl
  -}

XXX -}

---
