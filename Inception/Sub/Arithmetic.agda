{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Arithmetic where

open import Data.Nat

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; cong-app; dcong₂; sym; trans; subst; subst₂)
open Eq.≡-Reasoning

variable
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

pred-eq : suc n ≤ m → m ≡ suc (pred m)
pred-eq {n = zero} {m = suc m} sn≤m = refl
pred-eq {n = suc n} {m = suc m} sn≤m = refl

n+z : (n : ℕ) → n + zero ≡ n
n+z zero = refl
n+z (suc n) = cong suc (n+z n)

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

≤-uniq : {n₁ n₂ : ℕ} → (n₁≤n₂ : n₁ ≤ n₂) → (n₁≤n₂' : n₁ ≤ n₂) → n₁≤n₂ ≡ n₁≤n₂'
≤-uniq z≤n z≤n = refl
≤-uniq (s≤s n₁≤n₂) (s≤s n₁≤n₂') = cong s≤s (≤-uniq n₁≤n₂ n₁≤n₂')

p-eq-p : suc n ≡ suc m → n ≡ m
p-eq-p {n = zero} {m = zero} n≡m = refl
p-eq-p {n = suc n} {m = suc m} refl = refl

eq-to-ineq : n ≡ m → n ≤ m
eq-to-ineq {n = zero} {m = zero} refl = z≤n
eq-to-ineq {n = zero} {m = suc m} ()
eq-to-ineq {n = suc n} {m = zero} ()
eq-to-ineq {n = suc n} {m = suc m} refl = s≤s (eq-to-ineq refl)
