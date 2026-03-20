module Inception.Sub.ValueMachine (R : Set) where

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
  Γ' Γ'' Δ' : Ctx
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
      b : IsEmpty

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

  data Env : (Γ : Ctx) → Set

  data CompStack : (Δ : Ctx) → (X : Ty) → Set

  topCsEnv : CompStack Δ X → Env Δ
  ⟦_⟧ᴱ : (E : Env Γ) → ⟦ Γ ⟧ˣ
  ⟦_⟧ᶜˢ : (cs : CompStack Δ X) → K ⟦ X ⟧ → K ⟦ R₀ ⟧

  data CompStack  where

      ◻     :   CompStack ε R₀

      _⊲_⦂⦂_    : (Γ ∙ Z) ⊢ᶜ X → (γ : Env Γ) → (tail : CompStack Δ X) → {π : Wk Γ Δ} → {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv tail ⟧ᴱ} → CompStack Γ Z

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

      _﹐﹝_╎_﹞ :  (γ : Env Γ) → (W : Γ ⊢ᶜ X) → (cs : CompStack Δ X) → {π : Wk Γ Δ} → {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → Env (Γ ∙ `V)

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

  -- ⟦ ◻ ⟧ᶜˢ W = W
  ⟦ ◻ ⟧ᶜˢ = idf
  -- ⟦ W₁ ⊲ γ₁ ⦂⦂ tail ⟧ᶜˢ W =  ⟦ tail ⟧ᶜˢ (( ⟦ W₁ ⟧ᶜ ♯)(τ (⟦ γ₁ ⟧ᴱ , W)))
  -- ⟦ W₁ ⊲ γ₁ ⦂⦂ tail ⟧ᶜˢ =  ⟦ tail ⟧ᶜˢ ∘ (⟦ W₁ ⟧ᶜ ♯) ∘ τ ∘ < ⟦ γ₁ ⟧ᴱ , idf >
  -- ⟦ W₁ ⊲ γ₁ ⦂⦂ tail ⟧ᶜˢ W = (τ ； (⟦ W₁ ⟧ᶜ ♯) ； ⟦ tail ⟧ᶜˢ) (⟦ γ₁ ⟧ᴱ , W)
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

      comp-t-step   : {i : Γ ∋ Y} → {γ : Env Γ} → {W : Γ ⊢ᶜ X} → {cs : CompStack Δ X} → {π : Wk Γ Δ} → {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → ⟨ t i  ∥ (_﹐﹝_╎_﹞ γ W cs {π = π} {wk≡ = wk≡}) ⟩ →ᴸ ⟨ i ∥ γ ⟩


  data _→ᴸ*_ : LookupState X → LookupState X → Set where

    _◼ : (S : LookupState X) → S →ᴸ* S

    _→ᴸ⟨_⟩_ : (S : LookupState X) → {S' S'' : LookupState X} → S →ᴸ S' → S' →ᴸ* S'' → S →ᴸ* S''


  data LookupHaltingState : LookupState X → Set where

        found-unit : {γ : Env Γ} → LookupHaltingState ⟨ h ∥ _﹐_ γ u̲n̲i̲t̲ ⟩

        found-pair : {LHS : V̲a̲l̲ Γ X} → {RHS : V̲a̲l̲ Γ Y} → {γ : Env Γ} → LookupHaltingState ⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩

        found-lam : {W : (Γ ∙ X) ⊢ᶜ Y} → {γ : Env Γ} → LookupHaltingState ⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩

        found-comp : {W : Γ ⊢ᶜ X} → {γ : Env Γ} → {cs : CompStack Δ X} → {π : Wk Γ Δ} → {wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → LookupHaltingState ⟨ h ∥ (_﹐﹝_╎_﹞ γ W cs {π = π} {wk≡ = wk≡}) ⟩

  --------------------------------------------------------------------
  {-
  cnt-type : Ty → Set
  cnt-type `Unit = ℕ
  cnt-type (T₁ `× T₂) = (cnt-type T₁) × (cnt-type T₂)
  cnt-type (T₁ `⇒ T₂) = (cnt-type T₁) → (cnt-type T₂)
  cnt-type `V = ℕ

  data _≤ᴺ_ : {T : Ty} → (cnt-type T) → (cnt-type T) → Set where
    ≤ᴺ-unit : {n m : ℕ} → (n≤m : n ≤ m) → _≤ᴺ_ {T = `Unit} n m
    ≤ᴺ-pair : {T₁ T₂ : Ty} → {f₁ f₂ : cnt-type T₁} → {g₁ g₂ : cnt-type T₂} → (f₁ ≤ᴺ f₂) → (g₁ ≤ᴺ g₂) → (f₁ , g₁) ≤ᴺ (f₂ , g₂)
    ≤ᴺ-func : {T T₁ : Ty} → {h : cnt-type T} → {f₁ f₂ : cnt-type (T `⇒ T₁)} → (f₁ h) ≤ᴺ (f₂ h) → f₁ ≤ᴺ f₂
    ≤ᴺ-V : {n m : ℕ} → (n≤m : n ≤ m) → _≤ᴺ_ {T = `V} n m

  _*ᴺ_ : {T : Ty} → (cnt-type T) → (cnt-type T) → (cnt-type T)
  _*ᴺ_ {T = `Unit} n₁ n₂ = n₁ * n₂
  _*ᴺ_ {T = T₁ `× T₂} (f₁ , f₂) (g₁ , g₂) = f₁ *ᴺ g₁ , f₂ *ᴺ g₂
  _*ᴺ_ {T = T `⇒ T₁} f₁ f₂ = λ h → (f₁ h) *ᴺ (f₂ h)
  _*ᴺ_ {T = `V} n₁ n₂ = n₁ * n₂

  _+ᴺ_ : {T : Ty} → (cnt-type T) → (cnt-type T) → (cnt-type T)
  _+ᴺ_ {T = `Unit} n₁ n₂ = n₁ + n₂
  _+ᴺ_ {T = T₁ `× T₂} (f₁ , f₂) (g₁ , g₂) = f₁ +ᴺ g₁ , f₂ +ᴺ g₂
  _+ᴺ_ {T = T `⇒ T₁} f₁ f₂ = λ h → (f₁ h) +ᴺ (f₂ h)
  _+ᴺ_ {T = `V} n₁ n₂ = n₁ + n₂

  const-zero : (T : Ty) → cnt-type T
  const-zero `Unit = 0
  const-zero (T₁ `× T₂) = (const-zero T₁) , (const-zero T₂)
  const-zero (T `⇒ T₁) = λ _ → const-zero T₁
  const-zero `V = 0

  const-one : (T : Ty) → cnt-type T
  const-one `Unit = 1
  const-one (T₁ `× T₂) = (const-zero T₁) , (const-zero T₂)
  const-one (T `⇒ T₁) = λ _ → const-zero T₁
  const-one `V = 1
  -}

  {-
  data TermCounter : Ty → Set where
    c-Unit : (n : ℕ) → TermCounter `Unit
    c-V : (n : ℕ) → TermCounter (`V)
    c-⇒ : (n : ℕ) → (x : ℕ) → (c : TermCounter Y) → TermCounter (X `⇒ Y)
    c-×   : (n : ℕ) → (c₁ : TermCounter X) → (c₂ : TermCounter Y) → TermCounter (X `× Y)

  _++ᴺ_ : ℕ → TermCounter X → TermCounter X
  n ++ᴺ c-Unit n₁ = c-Unit (n + n₁)
  n ++ᴺ c-V n₁ = c-V (n + n₁)
  n ++ᴺ c-⇒ n₁ x c = c-⇒ (n + n₁) x c
  n ++ᴺ c-× n₁ c c₁ = c-× (n + n₁) c c₁

  │_│ : TermCounter X → ℕ
  │ c-Unit n │ = n
  │ c-V n │ = n
  │ c-⇒ n x c │ = n + │ c │
  │ c-× n c₁ c₂ │ = n + │ c₁ │ + │ c₂ │

  _+ᴺ_ : TermCounter X → TermCounter X → TermCounter X
  c-Unit n +ᴺ c-Unit n' = c-Unit (n + n')
  c-V n +ᴺ c-V n' = c-V (n + n')
  c-⇒ n x c +ᴺ c-⇒ n' x' c' = c-⇒ (n + n') (x + x') (c +ᴺ c')
  c-× n c₁ c₂ +ᴺ c-× n' c₁' c₂' = c-× (n + n') (c₁ +ᴺ c₁') (c₂ +ᴺ c₂')

  zero-counter : TermCounter X
  zero-counter {X = `Unit} = c-Unit zero
  zero-counter {X = X `× X₁} = c-× zero zero-counter zero-counter
  zero-counter {X = X `⇒ X₁} = c-⇒ zero zero zero-counter
  zero-counter {X = `V} = c-V zero

  one-counter : TermCounter X
  one-counter {X = `Unit} = c-Unit 1
  one-counter {X = X `× X₁} = c-× 1 zero-counter zero-counter
  one-counter {X = X `⇒ X₁} = c-⇒ 1 zero zero-counter
  one-counter {X = `V} = c-V 1

  data _≤ᴺ_ : {X : Ty} → (TermCounter X) → (TermCounter X) → Set where
    ≤ᴺ-unit : {n n' : ℕ} → (n≤n' : n ≤ n') → (c-Unit n) ≤ᴺ (c-Unit n')
    ≤ᴺ-pair : {n n' : ℕ} → {c₁ c₁' : TermCounter X} → {c₂ c₂' : TermCounter Y} → (n≤n' : n ≤ n') → (c₁ ≤ᴺ c₁') → (c₂ ≤ᴺ c₂') → (c-× n c₁ c₂) ≤ᴺ (c-× n' c₁' c₂')
    ≤ᴺ-func : {X : Ty} → {n n' x : ℕ} → {c c' : TermCounter Y} → (n≤n' : n ≤ n') → (c ≤ᴺ c') → (c-⇒ {X = X} n x c) ≤ᴺ (c-⇒ n' x c')
    ≤ᴺ-V : {n n' : ℕ} → (n≤n' : n ≤ n') → (c-V n) ≤ᴺ (c-V n')
  -}

  --------------------------------------------------------------------

  {-
  data TermMetric : Ty → Set where
    m-Unit : (cnt : ℕ) → (m : ℕ) → TermMetric `Unit
    m-V : (cnt : ℕ) → (m : ℕ) → (w : ℕ) → TermMetric (`V)
    m-⇒ : (cnt : ℕ) → (m : ℕ) → (nm : TermMetric Y) → TermMetric (X `⇒ Y)
    m-×   : (cnt : ℕ) → (m : ℕ) → (nm₁ : TermMetric X) → (nm₂ : TermMetric Y) → TermMetric (X `× Y)
  -}

  data TermMetric : Ty → Set where
    m-Unit : (m : ℕ) → TermMetric `Unit
    m-V : (m : ℕ) → (w : ℕ) → TermMetric (`V)
    m-⇒ : (m : ℕ) → (nm : TermMetric Y) → TermMetric (X `⇒ Y)
    m-× : (m : ℕ) → (nm₁ : TermMetric X) → (nm₂ : TermMetric Y) → TermMetric (X `× Y)

  {-
  data Wkn : (Γ : Ctx) → (E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))) → Set where
    wkn-nil  : Wkn ε []
    wkn-cong :   {Γ : Ctx} → {ne : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))} → {Y : Ty}
               → {e : (List (ℕ × ℕ) → TermMetric Y)} → (ϖ : Wkn Γ ne) → Wkn (Γ ∙ Y) ((Y , e) ∷ ne)
    wkn-cons :   {Γ : Ctx} → {ne : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))}
               → {Y : Ty} → (ϖ : Wkn Γ ne) → Wkn (Γ ∙ Y) ne
  -}

  data _≤ᶜˢⁿ_ : List (ℕ × ℕ) → List (ℕ × ℕ) → Set where
   [c≤c] : {csn : List (ℕ × ℕ)} → csn ≤ᶜˢⁿ csn
   -- FST: [s≤s] : {cnt : ℕ} {csn₁ csn₂ : List (ℕ × ℕ)} → n₁ ≤ n₂ → csn₁ ≤ᶜˢⁿ csn₂ → ((cnt , n₁) ∷ csn₁) ≤ᶜˢⁿ ((cnt , n₂) ∷ csn₂)
   [s≤s] : {cnt₁ cnt₂ : ℕ} {csn₁ csn₂ : List (ℕ × ℕ)} → cnt₁ ≤ cnt₂ → n₁ ≤ n₂ → csn₁ ≤ᶜˢⁿ csn₂ → ((cnt₁ , n₁) ∷ csn₁) ≤ᶜˢⁿ ((cnt₂ , n₂) ∷ csn₂)

  ≤ᶜˢⁿ-trans : {csn₁ csn₂ csn₃ : List (ℕ × ℕ)} → csn₁ ≤ᶜˢⁿ csn₂ → csn₂ ≤ᶜˢⁿ csn₃ → csn₁ ≤ᶜˢⁿ csn₃
  ≤ᶜˢⁿ-trans [c≤c] [c≤c] = [c≤c]
  ≤ᶜˢⁿ-trans [c≤c] ([s≤s] cnt₁≤cnt₂ x c₂≤c₃) = [s≤s] cnt₁≤cnt₂ x c₂≤c₃
  ≤ᶜˢⁿ-trans ([s≤s] cnt₁≤cnt₂ x c₁≤c₂) [c≤c] = [s≤s] cnt₁≤cnt₂ x c₁≤c₂
  ≤ᶜˢⁿ-trans ([s≤s] cnt₁≤cnt₂ x c₁≤c₂) ([s≤s] cnt₁≤cnt₂' x₁ c₂≤c₃) = [s≤s] (≤-trans cnt₁≤cnt₂ cnt₁≤cnt₂') (≤-trans x x₁) (≤ᶜˢⁿ-trans c₁≤c₂ c₂≤c₃)

  -- FST:
  -- ≤ᶜˢⁿ-trans : {csn₁ csn₂ csn₃ : List (ℕ × ℕ)} → csn₁ ≤ᶜˢⁿ csn₂ → csn₂ ≤ᶜˢⁿ csn₃ → csn₁ ≤ᶜˢⁿ csn₃
  -- ≤ᶜˢⁿ-trans [c≤c] [c≤c] = [c≤c]
  -- ≤ᶜˢⁿ-trans [c≤c] ([s≤s] x c₂≤c₃) = [s≤s] x c₂≤c₃
  -- ≤ᶜˢⁿ-trans ([s≤s] x c₁≤c₂) [c≤c] = [s≤s] x c₁≤c₂
  -- ≤ᶜˢⁿ-trans ([s≤s] x c₁≤c₂) ([s≤s] x₁ c₂≤c₃) = [s≤s] (≤-trans x x₁) (≤ᶜˢⁿ-trans c₁≤c₂ c₂≤c₃)

  --------------------------------------------------------------------

  data WkC : (Γ : Ctx) → (E : List ℕ) → Set where
    wkc-nil  : WkC ε []
    wkc-cong :   {Γ : Ctx} → {E : List ℕ} → {Y : Ty}
               → {e : ℕ} → (ϖ : WkC Γ E) → WkC (Γ ∙ Y) (e ∷ E)
    wkc-cons :   {Γ : Ctx} → {E : List ℕ}
               → {Y : Ty} → (ϖ : WkC Γ E) → WkC (Γ ∙ Y) E

  lcount : (i : Γ ∋ Z) → (E : List ℕ) → WkC Γ E → ℕ
  lcount Cx.h [] (wkc-cons ç) = 1
  lcount Cx.h (e ∷ E) (wkc-cong ç) = e
  lcount Cx.h (e ∷ E) (wkc-cons ç) = 1 --e
  lcount (Cx.t i) [] (wkc-cons ç) = 1
  lcount (Cx.t i) (e ∷ E) (wkc-cong ç) = lcount i E ç
  lcount (Cx.t i) (e ∷ E) (wkc-cons ç) = lcount i (e ∷ E) ç

  mutual

    vcount : (M : Val Γ Z) → (E : List ℕ) → WkC Γ E → ℕ
    vcount (var i) E ç = lcount i E ç
    vcount (lam W) E ç = ccount W E (wkc-cons ç)
    vcount (pair M₁ M₂) E ç = (vcount M₁ E ç) + (vcount M₂ E ç)
    vcount (pm M N) E ç =
      let
        a1 = vcount M E ç
      in
        vcount N (a1 ∷ a1 ∷ E) (wkc-cong (wkc-cong ç))
    vcount unit E ç = 0

    ccount : (W : Comp Γ Z) → (E : List ℕ) → WkC Γ E → ℕ
    ccount (return M) E ç = vcount M E ç
    ccount (pm M W) E ç =
      let
        a1 = vcount M E ç
      in
        ccount W (a1 ∷ a1 ∷ E) (wkc-cong (wkc-cong ç))
    ccount (push W₁ W₂) E ç =
      let
        a1 = ccount W₁ E ç
      in
        ccount W₂ (a1 ∷ E) (wkc-cong ç)
    ccount (app M N) E ç = (suc (vcount M E ç)) * (suc (vcount N E ç))
    ccount (var M) E ç = vcount M E ç
    ccount (sub W₁ W₂) E ç =
      let
        a1 = ccount W₂ E ç
      in
        ccount W₁ (a1 ∷ E) (wkc-cong ç)

  v̲c̲o̲u̲n̲t̲ : (M : V̲a̲l̲ Γ Y) → (E : List ℕ) → WkC Γ E → ℕ
  v̲c̲o̲u̲n̲t̲ (l̲a̲m̲ W) E ç = ccount W E (wkc-cons ç)
  v̲c̲o̲u̲n̲t̲ (pa̲i̲r̲ M₁ M₂) E ç = (v̲c̲o̲u̲n̲t̲ M₁ E ç) + (v̲c̲o̲u̲n̲t̲ M₂ E ç)
  v̲c̲o̲u̲n̲t̲ u̲n̲i̲t̲ E ç = 0
  v̲c̲o̲u̲n̲t̲ (v̲a̲r̲ i) E ç = lcount i E ç

  c̲c̲o̲u̲n̲t̲ : (W : C̲o̲m̲p Γ Z) → (E : List ℕ) → WkC Γ E → ℕ
  c̲c̲o̲u̲n̲t̲ (r̲e̲t̲u̲r̲n̲ M) E ç = v̲c̲o̲u̲n̲t̲ M E ç
  c̲c̲o̲u̲n̲t̲ (a̲pp M N) E ç = (suc (vcount M E ç)) * (suc (v̲c̲o̲u̲n̲t̲ N E ç))

  -------------------------------------------------------------------
  {-
  test-term-1 : Val ε `Unit
  test-term-1 = unit

  test-term-2 : Comp ε _
  test-term-2 = app (lam (app (lam (return (pair (lam (app (var h) (var (t h)))) (var h)))) (lam (return (pair (var h) (var h)))))) (unit)

  _ : vcount test-term-1 [] wkc-nil ≡ {!ccount test-term-2 [] wkc-nil!}
  _ = refl
  -}
  -------------------------------------------------------------------

  {-
  data _≤ᴹ_ : TermMetric X → TermMetric X → Set where
    ≤-Unit : {cnt₁ cnt₂ : ℕ} → (cnt₁ ≤ cnt₂) → (n₁ ≤ n₂) → (m-Unit cnt₁ n₁) ≤ᴹ (m-Unit cnt₂ n₂)
    ≤-V    : {cnt₁ cnt₂ : ℕ} → {w₁ w₂ : ℕ} → (cnt₁ ≤ cnt₂) → (m₁ ≤ m₂) → (w₁ ≤ w₂) → (m-V cnt₁ m₁ w₁) ≤ᴹ (m-V cnt₂ m₂ w₂)
    ≤-⇒    : {cnt₁ cnt₂ : ℕ} → {nm₁ nm₂ : TermMetric Y} → (cnt₁ ≤ cnt₂) → (m₁ ≤ m₂) → (nm₁ ≤ᴹ nm₂) → (m-⇒ {X = X} cnt₁ m₁ nm₁) ≤ᴹ (m-⇒ cnt₂ m₂ nm₂)
    ≤-×    : {cnt₁ cnt₂ : ℕ} → {lhs₁ lhs₂ : TermMetric X} → {rhs₁ rhs₂ : TermMetric Y} → (cnt₁ ≤ cnt₂) → (n₁ ≤ n₂) → (lhs₁ ≤ᴹ lhs₂) → (rhs₁ ≤ᴹ rhs₂) → (m-× cnt₁ n₁ lhs₁ rhs₁) ≤ᴹ (m-× cnt₂ n₂ lhs₂ rhs₂)

  ≤ᴹ-refl : {nm : TermMetric X} → nm ≤ᴹ nm
  ≤ᴹ-refl {nm = m-Unit cnt m} = ≤-Unit ≤-refl ≤-refl
  ≤ᴹ-refl {nm = m-V cnt m w} = ≤-V ≤-refl ≤-refl ≤-refl
  ≤ᴹ-refl {nm = m-⇒ cnt m nm} = ≤-⇒ ≤-refl ≤-refl ≤ᴹ-refl
  ≤ᴹ-refl {nm = m-× cnt m nm nm₁} = ≤-× ≤-refl ≤-refl ≤ᴹ-refl ≤ᴹ-refl

  ≤ᴹ-trans : {nm₁ nm₂ nm₃ : TermMetric X} → nm₁ ≤ᴹ nm₂ → nm₂ ≤ᴹ nm₃ → nm₁ ≤ᴹ nm₃
  ≤ᴹ-trans (≤-Unit cnt₁ x) (≤-Unit cnt₂ x₁) = ≤-Unit (≤-trans cnt₁ cnt₂) (≤-trans x x₁)
  ≤ᴹ-trans (≤-V cnt₁ x x₁) (≤-V cnt₂ x₃ x₄) = ≤-V (≤-trans cnt₁ cnt₂) (≤-trans x x₃) (≤-trans x₁ x₄)
  ≤ᴹ-trans (≤-⇒ cnt₁ x nm₁≤nm₂) (≤-⇒ cnt₂ x₁ nm₂≤nm₃) = ≤-⇒ (≤-trans cnt₁ cnt₂) (≤-trans x x₁) (≤ᴹ-trans nm₁≤nm₂ nm₂≤nm₃)
  ≤ᴹ-trans (≤-× cnt₁ x nm₁≤nm₂ nm₁≤nm₃) (≤-× cnt₂ x₁ nm₂≤nm₃ nm₂≤nm₄) = ≤-× (≤-trans cnt₁ cnt₂) (≤-trans x x₁) (≤ᴹ-trans nm₁≤nm₂ nm₂≤nm₃) (≤ᴹ-trans nm₁≤nm₃ nm₂≤nm₄)
  -}

  {-
  data _≤ᴹ_ : TermMetric X → TermMetric X → Set where
    ≤-Unit : {cnt : ℕ} → (n₁ ≤ n₂) → (m-Unit cnt n₁) ≤ᴹ (m-Unit cnt n₂)
    ≤-V    : {cnt : ℕ} → {w₁ w₂ : ℕ} → (m₁ ≤ m₂) → (w₁ ≤ w₂) → (m-V cnt m₁ w₁) ≤ᴹ (m-V cnt m₂ w₂)
    ≤-⇒    : {cnt : ℕ} → {nm₁ nm₂ : TermMetric Y} → (m₁ ≤ m₂) → (nm₁ ≤ᴹ nm₂) → (m-⇒ {X = X} cnt m₁ nm₁) ≤ᴹ (m-⇒ cnt m₂ nm₂)
    ≤-×    : {cnt : ℕ} → {lhs₁ lhs₂ : TermMetric X} → {rhs₁ rhs₂ : TermMetric Y} → (n₁ ≤ n₂) → (lhs₁ ≤ᴹ lhs₂) → (rhs₁ ≤ᴹ rhs₂) → (m-× cnt n₁ lhs₁ rhs₁) ≤ᴹ (m-× cnt n₂ lhs₂ rhs₂)

  ≤ᴹ-refl : {nm : TermMetric X} → nm ≤ᴹ nm
  ≤ᴹ-refl {nm = m-Unit cnt m} = ≤-Unit ≤-refl
  ≤ᴹ-refl {nm = m-V cnt m w} = ≤-V ≤-refl ≤-refl
  ≤ᴹ-refl {nm = m-⇒ cnt m nm} = ≤-⇒ ≤-refl ≤ᴹ-refl
  ≤ᴹ-refl {nm = m-× cnt m nm nm₁} = ≤-× ≤-refl ≤ᴹ-refl ≤ᴹ-refl

  ≤ᴹ-trans : {nm₁ nm₂ nm₃ : TermMetric X} → nm₁ ≤ᴹ nm₂ → nm₂ ≤ᴹ nm₃ → nm₁ ≤ᴹ nm₃
  ≤ᴹ-trans (≤-Unit x) (≤-Unit x₁) = ≤-Unit (≤-trans x x₁)
  ≤ᴹ-trans (≤-V x x₁) (≤-V x₃ x₄) = ≤-V (≤-trans x x₃) (≤-trans x₁ x₄)
  ≤ᴹ-trans (≤-⇒ x nm₁≤nm₂) (≤-⇒ x₁ nm₂≤nm₃) = ≤-⇒ (≤-trans x x₁) (≤ᴹ-trans nm₁≤nm₂ nm₂≤nm₃)
  ≤ᴹ-trans (≤-× x nm₁≤nm₂ nm₁≤nm₃) (≤-× x₁ nm₂≤nm₃ nm₂≤nm₄) = ≤-× (≤-trans x x₁) (≤ᴹ-trans nm₁≤nm₂ nm₂≤nm₃) (≤ᴹ-trans nm₁≤nm₃ nm₂≤nm₄)
  -}

  data _≤ᴹ_ : TermMetric X → TermMetric X → Set where
    ≤-Unit : (n₁ ≤ n₂) → (m-Unit n₁) ≤ᴹ (m-Unit n₂)
    ≤-V    : {w₁ w₂ : ℕ} → (m₁ ≤ m₂) → (w₁ ≤ w₂) → (m-V m₁ w₁) ≤ᴹ (m-V m₂ w₂)
    ≤-⇒    : {nm₁ nm₂ : TermMetric Y} → (m₁ ≤ m₂) → (nm₁ ≤ᴹ nm₂) → (m-⇒ {X = X} m₁ nm₁) ≤ᴹ (m-⇒ m₂ nm₂)
    ≤-×    : {lhs₁ lhs₂ : TermMetric X} → {rhs₁ rhs₂ : TermMetric Y} → (n₁ ≤ n₂) → (lhs₁ ≤ᴹ lhs₂) → (rhs₁ ≤ᴹ rhs₂) → (m-× n₁ lhs₁ rhs₁) ≤ᴹ (m-× n₂ lhs₂ rhs₂)

  ≤ᴹ-refl : {nm : TermMetric X} → nm ≤ᴹ nm
  ≤ᴹ-refl {nm = m-Unit m} = ≤-Unit ≤-refl
  ≤ᴹ-refl {nm = m-V m w} = ≤-V ≤-refl ≤-refl
  ≤ᴹ-refl {nm = m-⇒ m nm} = ≤-⇒ ≤-refl ≤ᴹ-refl
  ≤ᴹ-refl {nm = m-× m nm nm₁} = ≤-× ≤-refl ≤ᴹ-refl ≤ᴹ-refl

  ≤ᴹ-trans : {nm₁ nm₂ nm₃ : TermMetric X} → nm₁ ≤ᴹ nm₂ → nm₂ ≤ᴹ nm₃ → nm₁ ≤ᴹ nm₃
  ≤ᴹ-trans (≤-Unit x) (≤-Unit x₁) = ≤-Unit (≤-trans x x₁)
  ≤ᴹ-trans (≤-V x x₁) (≤-V x₃ x₄) = ≤-V (≤-trans x x₃) (≤-trans x₁ x₄)
  ≤ᴹ-trans (≤-⇒ x nm₁≤nm₂) (≤-⇒ x₁ nm₂≤nm₃) = ≤-⇒ (≤-trans x x₁) (≤ᴹ-trans nm₁≤nm₂ nm₂≤nm₃)
  ≤ᴹ-trans (≤-× x nm₁≤nm₂ nm₁≤nm₃) (≤-× x₁ nm₂≤nm₃ nm₂≤nm₄) = ≤-× (≤-trans x x₁) (≤ᴹ-trans nm₁≤nm₂ nm₂≤nm₃) (≤ᴹ-trans nm₁≤nm₃ nm₂≤nm₄)

  postulate
    extensionality : ∀ {A B : Set} {f g : A → B}
      → (∀ (x : A) → f x ≡ g x)
        -----------------------
      → f ≡ g

  -- postulate
  --   extensionality' : ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x}
  --     → (∀ (x : A) → f x ≡ g x)
  --       -----------------------
  --     → f ≡ g


  -- https://stackoverflow.com/questions/56304634/is-functional-extensionality-with-dependent-functions-consistent
  extensionality' : ∀ {A : Set}{B : A → Set}{f g : ∀ a → B a} → (∀ x → f x ≡ g x) → f ≡ g
  extensionality' {A}{B}{f}{g} e =
      H.≅-to-≡ (H.cong (λ f x → proj₂ (f x)) (H.≡-to-≅ (extensionality λ a → cong (a ,_) (e a))))

  ≤-uniq : {n₁ n₂ : ℕ} → (n₁≤n₂ : n₁ ≤ n₂) → (n₁≤n₂' : n₁ ≤ n₂) → n₁≤n₂ ≡ n₁≤n₂'
  ≤-uniq z≤n z≤n = refl
  ≤-uniq (s≤s n₁≤n₂) (s≤s n₁≤n₂') = cong s≤s (≤-uniq n₁≤n₂ n₁≤n₂')

  ≤ᴹ-uniq : {nm₁ nm₂ : TermMetric X} → (nm₁≤ᴹnm₂ nm₁≤ᴹnm₂' : nm₁ ≤ᴹ nm₂) → nm₁≤ᴹnm₂ ≡ nm₁≤ᴹnm₂'
  ≤ᴹ-uniq (≤-Unit x) (≤-Unit x₁) rewrite ≤-uniq x x₁ = refl
  ≤ᴹ-uniq (≤-V x x₁) (≤-V x₂ x₃) rewrite ≤-uniq x x₂ | ≤-uniq x₁ x₃ = refl
  ≤ᴹ-uniq (≤-⇒ x nm₁≤ᴹnm₂) (≤-⇒ x₁ nm₁≤ᴹnm₂') rewrite ≤-uniq x x₁ | ≤ᴹ-uniq nm₁≤ᴹnm₂ nm₁≤ᴹnm₂' = refl
  ≤ᴹ-uniq (≤-× x nm₁≤ᴹnm₂ nm₁≤ᴹnm₂') (≤-× x₁ nm₃≤ᴹnm₄ nm₃≤ᴹnm₄') rewrite ≤-uniq x x₁ | ≤ᴹ-uniq nm₁≤ᴹnm₂ nm₃≤ᴹnm₄ | ≤ᴹ-uniq nm₁≤ᴹnm₂' nm₃≤ᴹnm₄' = refl

  --EElemR X = (Σ[ f ∈ (List (ℕ × ℕ) → TermMetric X) ] ({csn₁ csn₂ : List (ℕ × ℕ)} → csn₁ ≤ᶜˢⁿ csn₂ → f csn₁ ≤ᴹ f csn₂))

  f-≤ᴹ-uniq : {f : (List (ℕ × ℕ) → TermMetric X)} → (f≤ᴹg f≤ᴹg' : ({csn₁ csn₂ : List (ℕ × ℕ)} → csn₁ ≤ᶜˢⁿ csn₂ → f csn₁ ≤ᴹ f csn₂)) → (λ {csn₁ csn₂ : List (ℕ × ℕ)} → f≤ᴹg {csn₁} {csn₂}) ≡ f≤ᴹg'
  f-≤ᴹ-uniq {f = f} f≤ᴹg f≤ᴹg' =
    let
      a0 = λ (csn₁ csn₂ : List (ℕ × ℕ)) (c≤c' : csn₁ ≤ᶜˢⁿ csn₂) →
           let
             a00 = f≤ᴹg c≤c'
             a01 = f≤ᴹg' c≤c'
            in
            ≤ᴹ-uniq a00 a01
      a1 csn₁ csn₂ = extensionality (a0 csn₁ csn₂)
      a2 csn₁ = extensionality' (a1 csn₁)
      a3 = extensionality' a2
      a4 = cong (λ x → λ {csn₁ csn₂ : List (ℕ × ℕ)} → x csn₁ csn₂) a3
    in
    a4

  {-
  zero-metric : TermMetric X
  zero-metric {X = `Unit} = m-Unit 0 0
  zero-metric {X = X `× Y} = m-× 0 0 (zero-metric {X = X}) (zero-metric {X = Y})
  zero-metric {X = X `⇒ Y} = m-⇒ 0 0 (zero-metric {X = Y})
  zero-metric {X = `V} = m-V 0 0 0
  -}

  zero-metric : TermMetric X
  zero-metric {X = `Unit} = m-Unit 0
  zero-metric {X = X `× Y} = m-× 0 (zero-metric {X = X}) (zero-metric {X = Y})
  zero-metric {X = X `⇒ Y} = m-⇒ 0 (zero-metric {X = Y})
  zero-metric {X = `V} = m-V 0 0

  -------------------------------

  csn-to-nat₀ : ℕ → List (ℕ × ℕ) → ℕ
  csn-to-nat₀ w [] = 0
  csn-to-nat₀ w ((cnt , tm) ∷ csn) = (tm + (w * (suc cnt))) + (csn-to-nat₀ (tm + (w * (suc cnt))) csn)

  csn-decr : (n₁ ≤ n₂) → (csn : List (ℕ × ℕ)) → csn-to-nat₀ n₁ csn ≤ csn-to-nat₀ n₂ csn
  csn-decr {n₁ = n₁} {n₂ = n₂} z≤n [] = ≤-refl
  csn-decr {n₁ = n₁} {n₂ = n₂} z≤n (x ∷ csn) = let le1 = +-≤-cong (≤-refl {n = proj₂ x}) z≤n in +-≤-cong le1 (csn-decr le1 csn)
  csn-decr {n₁ = n₁} {n₂ = n₂} (s≤s n₁≤n₂) [] = ≤-refl
  csn-decr {n₁ = n₁} {n₂ = n₂} (s≤s n₁≤n₂) (x ∷ csn) =
    let
      le1 = +-≤-cong (≤-refl {n = proj₂ x}) (s≤s (+-≤-cong (≤-refl {n = proj₁ x}) (*-≤-cong n₁≤n₂ (s≤s (≤-refl {n = proj₁ x})))))
    in
      +-≤-cong le1 (csn-decr le1 csn)

  csn-len-decr : (n₀ : ℕ) → (n×m : ℕ × ℕ) → (csn : List (ℕ × ℕ)) → csn-to-nat₀ n₀ csn ≤ csn-to-nat₀ n₀ (n×m ∷ csn)
  csn-len-decr n₀ n×m [] = z≤n
  csn-len-decr n₀ n×m (n×m' ∷ csn) =
    let
      b0 : n₀ ≤ n₀ + 0
      b0 = subst (_≤_ n₀) (+-comm {n = 0} {m = n₀}) ≤-refl
      b1 : n₀ ≤ n₀ * 1
      b1 = subst (_≤_ n₀) (*-comm {n = 1} {m = n₀}) b0
      a0 = ≤-trans b1 (*-≤-cong (≤-refl {n = n₀}) ((+-≤-cong (≤-refl {n = 1}) (z≤n {n = proj₁ n×m}))))
      a1 = +-≤-cong (z≤n {n = proj₂ n×m}) a0
      a2 = *-≤-cong a1 (≤-refl {n = suc (proj₁ n×m')})
      a3 = +-≤-cong (≤-refl {n = proj₂ n×m'}) a2
      c1 = csn-decr a3 csn
      d1 = +-≤-cong (+-≤-cong (≤-refl {n = proj₂ n×m'}) a2) c1
      d2 = (+-≤-cong (z≤n {n = proj₂ n×m + n₀ * suc (proj₁ n×m)}) d1)
    in
    d2

  ≤ᶜˢⁿ-decr : {csn₁ csn₂ : List (ℕ × ℕ)} → (n₁ ≤ n₂) → csn₁ ≤ᶜˢⁿ csn₂ → csn-to-nat₀ n₁ csn₁ ≤ csn-to-nat₀ n₂ csn₂
  ≤ᶜˢⁿ-decr {n₁ = n₁} {n₂ = n₂} n₁≤n₂ ([c≤c] {csn = csn}) = csn-decr n₁≤n₂ csn
  ≤ᶜˢⁿ-decr {n₁ = n₁} {n₂ = n₂} n₁≤n₂ ([s≤s] cnt₁≤cnt₂ n₃≤n₄ c₁≤c₂) =
    let
      m₁≤m₂ = +-≤-cong n₃≤n₄ (*-≤-cong n₁≤n₂ (s≤s cnt₁≤cnt₂))
    in
    +-≤-cong m₁≤m₂ (≤ᶜˢⁿ-decr m₁≤m₂ c₁≤c₂)

  -- FST:
  -- ≤ᶜˢⁿ-decr : {csn₁ csn₂ : List (ℕ × ℕ)} → (n₁ ≤ n₂) → csn₁ ≤ᶜˢⁿ csn₂ → csn-to-nat₀ n₁ csn₁ ≤ csn-to-nat₀ n₂ csn₂
  -- ≤ᶜˢⁿ-decr {n₁ = n₁} {n₂ = n₂} n₁≤n₂ ([c≤c] {csn = csn}) = csn-decr n₁≤n₂ csn
  -- ≤ᶜˢⁿ-decr {n₁ = n₁} {n₂ = n₂} n₁≤n₂ ([s≤s] n₃≤n₄ c₁≤c₂) =
  --   let
  --     m₁≤m₂ = +-≤-cong n₃≤n₄ (*-≤-cong n₁≤n₂ ≤-refl)
  --   in
  --     +-≤-cong m₁≤m₂ (≤ᶜˢⁿ-decr m₁≤m₂ c₁≤c₂)

  {-
  ⟪_⟫ : TermMetric X → ℕ
  ⟪ m-Unit _ m ⟫ = m
  ⟪ m-V _ m w ⟫ = m + w
  ⟪ m-⇒ _ m nm ⟫ = m + ⟪ nm ⟫
  ⟪ m-× _ m nm₁ nm₂ ⟫ = m + ⟪ nm₁ ⟫ + ⟪ nm₂ ⟫
  -}

  ⟪_⟫ : TermMetric X → ℕ
  ⟪ m-Unit m ⟫ = m
  ⟪ m-V m w ⟫ = m + w
  ⟪ m-⇒ m nm ⟫ = m + ⟪ nm ⟫
  ⟪ m-× m nm₁ nm₂ ⟫ = m + ⟪ nm₁ ⟫ + ⟪ nm₂ ⟫

  incr : ℕ → TermMetric X → TermMetric X
  incr n (m-Unit m) = m-Unit (n + m)
  incr n (m-V m w) = m-V (n + m) w
  incr n (m-⇒ m nm) = m-⇒ (n + m) nm
  incr n (m-× m nm₁ nm₂) = m-× (n + m) nm₁ nm₂

  incr-coh : (n : ℕ) → (X : Ty) → (nm : TermMetric X) → ⟪ incr n nm ⟫ ≡ n + ⟪ nm ⟫
  incr-coh zero `Unit (m-Unit m) = refl
  incr-coh zero (X `× X₁) (m-× m nm nm₁) = refl
  incr-coh zero (X `⇒ X₁) (m-⇒ m nm) = refl
  incr-coh zero `V (m-V m w) = refl
  incr-coh (suc n) `Unit (m-Unit m) = refl
  incr-coh (suc n) (X `× X₁) (m-× m nm nm₁) rewrite +-assoc {n} {m} {⟪ nm ⟫} | +-assoc {n} {m + ⟪ nm ⟫} {⟪ nm₁ ⟫} = refl
  incr-coh (suc n) (X `⇒ X₁) (m-⇒ m nm) rewrite +-assoc {n} {m} {⟪ nm ⟫} = refl
  incr-coh (suc n) `V (m-V m w) rewrite +-assoc {n} {m} {w} = refl

  {-# REWRITE incr-coh #-}

  incr-zero-coh : (X : Ty) → (nm : TermMetric X) → incr zero nm ≡ nm
  incr-zero-coh `Unit (m-Unit m) = refl
  incr-zero-coh (X `× X₁) (m-× m nm₁ nm₂) = refl
  incr-zero-coh (X `⇒ X₁) (m-⇒ m nm) = refl
  incr-zero-coh `V (m-V m w) = refl

  {-# REWRITE incr-zero-coh #-}

  {-
  p1 : TermMetric (X `⇒ Y) → ℕ
  p1 (m-⇒ m cnt nm) = m

  --p2 : TermMetric (X `⇒ Y) → (TermCounter X)
  p2 : TermMetric (X `⇒ Y) → ℕ
  p2 (m-⇒ m cnt nm) = cnt

  p3 : TermMetric (X `⇒ Y) → TermMetric Y
  p3 (m-⇒ m cnt nm) = nm
  -}

  p1 : TermMetric (X `⇒ Y) → ℕ
  p1 (m-⇒ m w) = m

  pw : TermMetric (X `⇒ Y) → TermMetric Y
  pw (m-⇒ m w) = w

  vx : TermMetric (X `× Y) → ℕ
  vx (m-× m l r) = m

  vx+n : (nm : TermMetric (X `× Y)) → vx (incr n nm) ≡ n + (vx nm)
  vx+n (m-× m nm nm₁) = refl

  {-# REWRITE vx+n #-}

  lhs : TermMetric (X `× Y) → TermMetric X
  lhs (m-× m l r) = l

  rhs : TermMetric (X `× Y) → TermMetric Y
  rhs (m-× m l r) = r

  lhs-incr-drop : (n : ℕ) → (nm : TermMetric (X `× Y)) → ⟪ lhs (incr n nm) ⟫ ≡ ⟪ lhs nm ⟫
  lhs-incr-drop n (m-× m nm₁ nm₂) = refl

  rhs-incr-drop : (n : ℕ) → (nm : TermMetric (X `× Y)) → ⟪ rhs (incr n nm) ⟫ ≡ ⟪ rhs nm ⟫
  rhs-incr-drop n (m-× m nm₁ nm₂) = refl

  zm-coh : (X : Ty) → ⟪ zero-metric {X = X} ⟫ ≡ 0
  zm-coh `Unit = refl
  zm-coh (X `× Y) rewrite zm-coh X | zm-coh Y = refl
  zm-coh (X `⇒ Y) rewrite zm-coh Y = refl
  zm-coh `V = refl

  {-# REWRITE zm-coh #-}

  {-
  ≤ᴹ-incr-drop : (n : ℕ) → (nm₁ nm₂ : TermMetric X) → ((incr n nm₁) ≤ᴹ (incr n nm₂)) → (nm₁ ≤ᴹ nm₂)
  ≤ᴹ-incr-drop {X = `Unit} n (m-Unit _ m₁) (m-Unit _ m₂) (≤-Unit c≤c' n+m₁≤n+m₂) = ≤-Unit c≤c' (+-≤-cong-rev-left n+m₁≤n+m₂)
  ≤ᴹ-incr-drop {X = X `× Y} n (m-× _ m₁ nm₁ nm₂) (m-× _ m₂ nm₃ nm₄) (≤-× c≤c' n+m₁≤n+m₂ nm₁≤nm₃ nm₂≤nm₄) = ≤-× c≤c' (+-≤-cong-rev-left n+m₁≤n+m₂) nm₁≤nm₃ nm₂≤nm₄
  ≤ᴹ-incr-drop {X = X `⇒ Y} n (m-⇒ _ m₁ nm₁) (m-⇒ _ m₂ nm₂) (≤-⇒ c≤c' n+m₁≤n+m₂ nm₁≤nm₂) = ≤-⇒ c≤c' (+-≤-cong-rev-left n+m₁≤n+m₂) nm₁≤nm₂
  ≤ᴹ-incr-drop {X = `V} n (m-V _ m₁ w₁) (m-V _ m₂ w₂) (≤-V c≤c' n+m₁≤n+m₂ w₁≤w₂) = ≤-V c≤c' (+-≤-cong-rev-left n+m₁≤n+m₂) w₁≤w₂

  ≤ᴹ-incr-cong : (n₁≤n₂ : n₁ ≤ n₂) → {nm₁ nm₂ : TermMetric X} → (nm₁ ≤ᴹ nm₂) → ((incr n₁ nm₁) ≤ᴹ (incr n₂ nm₂))
  ≤ᴹ-incr-cong n₁≤n₂ (≤-Unit c≤c' m₁≤m₂) = ≤-Unit c≤c' (+-≤-cong n₁≤n₂ m₁≤m₂)
  ≤ᴹ-incr-cong n₁≤n₂ (≤-V c≤c' m₁≤m₂ w₁≤w₂) = ≤-V c≤c' (+-≤-cong n₁≤n₂ m₁≤m₂) w₁≤w₂
  ≤ᴹ-incr-cong n₁≤n₂ (≤-⇒ c≤c' m₁≤m₂ nm₁≤nm₂) = ≤-⇒ c≤c' (+-≤-cong n₁≤n₂ m₁≤m₂) nm₁≤nm₂
  ≤ᴹ-incr-cong n₁≤n₂ (≤-× c≤c' m₁≤m₂ nm₁≤nm₃ nm₂≤nm₄) = ≤-× c≤c' (+-≤-cong n₁≤n₂ m₁≤m₂) nm₁≤nm₃ nm₂≤nm₄
  -}

  ≤ᴹ-incr-drop : (n : ℕ) → (nm₁ nm₂ : TermMetric X) → ((incr n nm₁) ≤ᴹ (incr n nm₂)) → (nm₁ ≤ᴹ nm₂)
  ≤ᴹ-incr-drop {X = `Unit} n (m-Unit m₁) (m-Unit m₂) (≤-Unit n+m₁≤n+m₂) = ≤-Unit (+-≤-cong-rev-left n+m₁≤n+m₂)
  ≤ᴹ-incr-drop {X = X `× Y} n (m-× m₁ nm₁ nm₂) (m-× m₂ nm₃ nm₄) (≤-× n+m₁≤n+m₂ nm₁≤nm₃ nm₂≤nm₄) = ≤-× (+-≤-cong-rev-left n+m₁≤n+m₂) nm₁≤nm₃ nm₂≤nm₄
  ≤ᴹ-incr-drop {X = X `⇒ Y} n (m-⇒ m₁ nm₁) (m-⇒ m₂ nm₂) (≤-⇒ n+m₁≤n+m₂ nm₁≤nm₂) = ≤-⇒ (+-≤-cong-rev-left n+m₁≤n+m₂) nm₁≤nm₂
  ≤ᴹ-incr-drop {X = `V} n (m-V m₁ w₁) (m-V m₂ w₂) (≤-V n+m₁≤n+m₂ w₁≤w₂) = ≤-V (+-≤-cong-rev-left n+m₁≤n+m₂) w₁≤w₂

  ≤ᴹ-incr-cong : (n₁≤n₂ : n₁ ≤ n₂) → {nm₁ nm₂ : TermMetric X} → (nm₁ ≤ᴹ nm₂) → ((incr n₁ nm₁) ≤ᴹ (incr n₂ nm₂))
  ≤ᴹ-incr-cong n₁≤n₂ (≤-Unit m₁≤m₂) = ≤-Unit (+-≤-cong n₁≤n₂ m₁≤m₂)
  ≤ᴹ-incr-cong n₁≤n₂ (≤-V m₁≤m₂ w₁≤w₂) = ≤-V (+-≤-cong n₁≤n₂ m₁≤m₂) w₁≤w₂
  ≤ᴹ-incr-cong n₁≤n₂ (≤-⇒ m₁≤m₂ nm₁≤nm₂) = ≤-⇒ (+-≤-cong n₁≤n₂ m₁≤m₂) nm₁≤nm₂
  ≤ᴹ-incr-cong n₁≤n₂ (≤-× m₁≤m₂ nm₁≤nm₃ nm₂≤nm₄) = ≤-× (+-≤-cong n₁≤n₂ m₁≤m₂) nm₁≤nm₃ nm₂≤nm₄

-------------------------------------------------------------------------------------------------

  ≤ᴹ-p1 : {nm₁ nm₂ : TermMetric (X `⇒ Y)} → (nm₁ ≤ᴹ nm₂) → (p1 nm₁) ≤ (p1 nm₂)
  ≤ᴹ-p1 (≤-⇒ n₁≤n₂ nm₁≤nm₂) = n₁≤n₂

  {-
  ≤ᴹ-p2 : {nm₁ nm₂ : TermMetric (X `⇒ Y)} → (nm₁ ≤ᴹ nm₂) → (p2 nm₁) ≡ (p2 nm₂)
  ≤ᴹ-p2 (≤-⇒ n₁≤n₂ nm₁≤nm₂) = refl

  ≡⇒≤ : n ≡ m → n ≤ m
  ≡⇒≤ {n = n} {m = m} n≡m rewrite n≡m = ≤-refl

  +-p1-incr : (n : ℕ) → (nm : TermMetric (X `⇒ Y)) → p1 (incr n nm) ≡ n + (p1 nm)
  --+-p1-incr n (m-⇒ {X = X} {Y = Y} m cnt nm) with incr n (m-⇒ {X = X} {Y = Y} m cnt nm)
  +-p1-incr n (m-⇒ {Y = Y} {X = X} m cnt nm) with incr n (m-⇒ {Y = Y} {X = X} m cnt nm)
  ... | x = refl

  ≡-p2-incr : (n : ℕ) → (nm : TermMetric (X `⇒ Y)) → p2 (incr n nm) ≡ p2 nm
  ≡-p2-incr n (m-⇒ m cnt nm) = refl

  ≡-p3-incr : (n : ℕ) → (nm : TermMetric (X `⇒ Y)) → p3 (incr n nm) ≡ p3 nm
  ≡-p3-incr n (m-⇒ m cnt nm) = refl

  {-# REWRITE ≡-p2-incr #-}
  -}

  ≤ᴹ-pw : {nm₁ nm₂ : TermMetric (X `⇒ Y)} → (nm₁ ≤ᴹ nm₂) → (pw nm₁) ≤ᴹ (pw nm₂)
  ≤ᴹ-pw (≤-⇒ n₁≤n₂ nm₁≤nm₂) = nm₁≤nm₂

  ≤ᴹ-lhs : {nm₁ nm₂ : TermMetric (X `× Y)} → (nm₁ ≤ᴹ nm₂) → (lhs nm₁) ≤ᴹ (lhs nm₂)
  ≤ᴹ-lhs (≤-× x nm₁≤nm₃ nm₂≤nm₄) = nm₁≤nm₃

  ≤ᴹ-rhs : {nm₁ nm₂ : TermMetric (X `× Y)} → (nm₁ ≤ᴹ nm₂) → (rhs nm₁) ≤ᴹ (rhs nm₂)
  ≤ᴹ-rhs (≤-× x nm₁≤nm₃ nm₂≤nm₄) = nm₂≤nm₄

  ≤ᴹ-vx : {nm₁ nm₂ : TermMetric (X `× Y)} → (nm₁ ≤ᴹ nm₂) → (vx nm₁) ≤ (vx nm₂)
  ≤ᴹ-vx (≤-× n₁≤n₂ nm₁≤nm₂ nm₁≤nm₃) = n₁≤n₂

  ≤ᴹ⇒≤ : {nm₁ nm₂ : TermMetric X} → (nm₁ ≤ᴹ nm₂) → (⟪ nm₁ ⟫ ≤ ⟪ nm₂ ⟫)
  ≤ᴹ⇒≤ (≤-Unit n₁≤n₂) = n₁≤n₂
  ≤ᴹ⇒≤ (≤-V n₁≤n₂ w₁≤w₂) = +-≤-cong n₁≤n₂ w₁≤w₂
  ≤ᴹ⇒≤ (≤-⇒ n₁≤n₂ nm₁≤nm₂) = +-≤-cong n₁≤n₂ (≤ᴹ⇒≤ nm₁≤nm₂)
  ≤ᴹ⇒≤ (≤-× n₁≤n₂ nm₁≤nm₃ nm₂≤nm₄) = +-≤-cong (+-≤-cong n₁≤n₂ (≤ᴹ⇒≤ nm₁≤nm₃)) (≤ᴹ⇒≤ nm₂≤nm₄)

  --------------------------------------------------------------------

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

  --------------------------------------------------------------------

  p-eq-p : suc n ≡ suc m → n ≡ m
  p-eq-p {n = zero} {m = zero} n≡m = refl
  p-eq-p {n = suc n} {m = suc m} refl = refl

  eq-to-ineq : n ≡ m → n ≤ m
  eq-to-ineq {n = zero} {m = zero} refl = z≤n
  eq-to-ineq {n = zero} {m = suc m} ()
  eq-to-ineq {n = suc n} {m = zero} ()
  eq-to-ineq {n = suc n} {m = suc m} refl = s≤s (eq-to-ineq refl)

  --------------------------------------------------------------------
  EElemR : Ty → Set
  EElemR X = (Σ[ f ∈ (List (ℕ × ℕ) → TermMetric X) ] ({csn₁ csn₂ : List (ℕ × ℕ)} → csn₁ ≤ᶜˢⁿ csn₂ → f csn₁ ≤ᴹ f csn₂))

  EElem : Ty → Set
  EElem X = ℕ × (EElemR X)

  EMetric = List (Σ[ X ∈ Ty ] (EElem X))

  data WkN : (Γ : Ctx) → (E : EMetric) → Set where
    wkn-nil  : WkN ε []
    wkn-cong :   {Γ : Ctx} → {ne : EMetric} → {Y : Ty}
               → {e : EElem Y} → (ϖ : WkN Γ ne) → WkN (Γ ∙ Y) ((Y , e) ∷ ne)
    wkn-cons :   {Γ : Ctx} → {ne : EMetric}
               → {Y : Ty} → (ϖ : WkN Γ ne) → WkN (Γ ∙ Y) ne

  data WkE :   (π : Wk Γ Γ')
             → {E E' : EMetric}
             → (ϖ : WkN Γ E) → (ϖ' : WkN Γ' E') → Set where
   wke-ε   :     WkE wk-ε wkn-nil wkn-nil
   wke-ccc :     {E E' : EMetric} → (π : Wk Γ Γ') → (ϖ : WkN Γ E) → (ϖ' : WkN Γ' E') → (e : EElem X)
               → (θ : WkE π ϖ ϖ')
               → (WkE (wk-cong π) {E = (X , e) ∷ E} {E' = (X , e) ∷ E'} (wkn-cong ϖ) (wkn-cong ϖ'))
   wke-wc- :     {E E' : EMetric} → (π : Wk Γ Γ') → (ϖ : WkN Γ E) → (ϖ' : WkN Γ' E') → (e : EElem X)
               → (θ : WkE π ϖ ϖ')
               → (WkE (wk-wk {A = X} π) {E = (X , e) ∷ E} {E' = E'} (wkn-cong ϖ) ϖ')
   wke-ww- :     {E E' : EMetric} → (π : Wk Γ Γ') → (ϖ : WkN Γ E) → (ϖ' : WkN Γ' E')
               → (θ : WkE π ϖ ϖ')
               → (WkE (wk-wk {A = X} π) {E = E} {E' = E'} (wkn-cons ϖ) ϖ')
   wke-cww :     {E E' : EMetric} → (π : Wk Γ Γ') → (ϖ : WkN Γ E) → (ϖ' : WkN Γ' E')
               → (θ : WkE π ϖ ϖ')
               → (WkE (wk-cong {A = X} π) {E = E} {E' = E'} (wkn-cons ϖ) (wkn-cons ϖ'))


  wke-z-l : {e : Σ[ X ∈ Ty ] (EElem X)} {E' : EMetric} {π : Wk Γ Γ'} {ϖ : WkN Γ []} {ϖ' : WkN Γ' (e ∷ E')} → WkE π ϖ ϖ' → ⊥
  wke-z-l (wke-ww- π ϖ ϖ' θ) = wke-z-l θ
  wke-z-l (wke-cww π ϖ ϖ' θ) = wke-z-l θ

  wke-z-r : {e : Σ[ X ∈ Ty ] (EElem X)} {E' : EMetric} {π : Wk Γ Γ} {ϖ : WkN Γ (e ∷ E')}  {ϖ' : WkN Γ []} → WkE π ϖ ϖ' → ⊥
  wke-z-r (wke-wc- π ϖ ϖ' e θ) = wk-absurd (wk-wk π) π
  wke-z-r (wke-ww- π ϖ ϖ' θ) = wk-absurd (wk-wk π) π
  wke-z-r (wke-cww π ϖ ϖ' θ) = wke-z-r θ

  wke-id : {E : EMetric} → {π : Wk Γ Γ} → {ϖ : WkN Γ E} → WkE π ϖ ϖ
  wke-id {π = π} {ϖ = wkn-nil} rewrite wk-id-id {π = π} = wke-ε
  wke-id {π = π} {ϖ = wkn-cong ϖ} rewrite wk-id-id {π = π} = wke-ccc wk-id ϖ ϖ _ wke-id
  wke-id {π = π} {ϖ = wkn-cons ϖ} rewrite wk-id-id {π = π} = wke-cww wk-id ϖ ϖ wke-id

  -- DEPRECATED:
  -- data WkX  : {E E' : EMetric} → (π : Wk Γ Γ') → (ϖ : WkN Γ E) → (ϖ' : WkN Γ' E') → Set where
  --   wkx-bc       : {E E' : EMetric} → {π : Wk Γ Γ'} → {ϖ : WkN Γ E} → {ϖ' : WkN Γ' E'} → (θ : WkE π ϖ ϖ') → WkX π ϖ ϖ'
  --   wkx-cong     :   {E E' : EMetric}
  --                 → {π : Wk Γ Γ'} → {ϖ : WkN Γ E} → {ϖ' : WkN Γ' E'}
  --                 → {nm₁ nm₂ : EElem X}
  --                 → (cnt₁≤cnt₂ : proj₁ nm₁ ≤ proj₁ nm₂)
  --                 → (nm₁≤nm₂ : ((csn : (List (ℕ × ℕ))) → (proj₁ (proj₂ nm₁) csn) ≤ᴹ (proj₁ (proj₂ nm₂) csn)))
  --                 → (ϖ≤ϖ' : WkX π ϖ ϖ') → WkX (wk-cong π) (wkn-cong {e = nm₁} ϖ) (wkn-cong {e = nm₂} ϖ')
  --   wkx-wk       :   {E E' : EMetric}
  --                 → {π : Wk Γ Γ'} → {ϖ : WkN Γ E} → {ϖ' : WkN Γ' E'}
  --                 → (ϖ≤ϖ' : WkX π ϖ ϖ') → WkX (wk-cong π) (wkn-cons {Y = Y} ϖ) (wkn-cons {Y = Y} ϖ')

  -- wkx-id : {π : Wk Γ Γ} → {E : EMetric} → {ϖ : WkN Γ E} → WkX π ϖ ϖ
  -- wkx-id {π = π} {E = E} {ϖ = ϖ} = wkx-bc wke-id

  -- wkx-z-r : {e : Σ[ X ∈ Ty ] (EElem X)} {E' : EMetric} {π : Wk Γ Γ} {ϖ : WkN Γ (e ∷ E')}  {ϖ' : WkN Γ []} → (ϕ : WkX π ϖ ϖ') → ⊥
  -- wkx-z-r (wkx-bc θ) = wke-z-r θ
  -- wkx-z-r (wkx-wk ϕ) = wkx-z-r ϕ

  -- wkx-z-l : {e : Σ[ X ∈ Ty ] (EElem X)} {E' : EMetric} {π : Wk Γ Γ'} {ϖ : WkN Γ []} {ϖ' : WkN Γ' (e ∷ E')} → (ϕ : WkX π ϖ ϖ') → ⊥
  -- wkx-z-l (wkx-bc θ) = wke-z-l θ
  -- wkx-z-l (wkx-wk ϕ) = wkx-z-l ϕ

  -----------------------------------------------------------------------
  {- without inequality
  data WkZ  : {E E' : EMetric} → (ϖ : WkN Γ E) → (ϖ' : WkN Γ E') → Set where
    wkz-nil       : {E E' : EMetric} → {ϖ : WkN ε E} → {ϖ' : WkN ε E'} → WkZ ϖ ϖ'
    wkz-cong     :   {E E' : EMetric}
                  → {ϖ : WkN Γ E} → {ϖ' : WkN Γ E'}
                  → {nm₁ nm₂ : EElemR X}
                  → (nm₁≤nm₂ : ((csn : (List (ℕ × ℕ))) → (proj₁ nm₁ csn) ≤ᴹ (proj₁ nm₂ csn)))
                  → (ϖ≤ϖ' : WkZ ϖ ϖ') → WkZ (wkn-cong {e = n , nm₁} ϖ) (wkn-cong {e = n , nm₂} ϖ')
    wkz-wk       :  {E E' : EMetric}
                  → {ϖ : WkN Γ E} → {ϖ' : WkN Γ E'}
                  → (ϖ≤ϖ' : WkZ ϖ ϖ') → WkZ (wkn-cons {Y = Y} ϖ) (wkn-cons {Y = Y} ϖ')

  wkz-id : {E : EMetric} → {ϖ : WkN Γ E} → WkZ ϖ ϖ
  wkz-id {E = E} {ϖ = wkn-nil} = wkz-nil
  wkz-id {E = E} {ϖ = wkn-cong ϖ} = wkz-cong (λ csn → ≤ᴹ-refl) wkz-id
  wkz-id {E = E} {ϖ = wkn-cons ϖ} = wkz-wk wkz-id

  -}

  --------------------------------------------------------------------------

  data WkCE :   (π : Wk Γ Γ')
             → {E E' : List ℕ}
             → (ϖ : WkC Γ E) → (ϖ' : WkC Γ' E') → Set where
   wkce-ε   :     WkCE wk-ε wkc-nil wkc-nil
   wkce-ccc :     {E E' : List ℕ} → (π : Wk Γ Γ') → (ϖ : WkC Γ E) → (ϖ' : WkC Γ' E') → (e : ℕ)
               → (θ : WkCE π ϖ ϖ')
               → (WkCE (wk-cong {A = X} π) {E = e ∷ E} {E' = e ∷ E'} (wkc-cong ϖ) (wkc-cong ϖ'))
   wkce-wc- :     {E E' : List ℕ} → (π : Wk Γ Γ') → (ϖ : WkC Γ E) → (ϖ' : WkC Γ' E') → (e : ℕ)
               → (θ : WkCE π ϖ ϖ')
               → (WkCE (wk-wk {A = X} π) {E = e ∷ E} {E' = E'} (wkc-cong ϖ) ϖ')
   wkce-ww- :     {E E' : List ℕ} → (π : Wk Γ Γ') → (ϖ : WkC Γ E) → (ϖ' : WkC Γ' E')
               → (θ : WkCE π ϖ ϖ')
               → (WkCE (wk-wk {A = X} π) {E = E} {E' = E'} (wkc-cons ϖ) ϖ')
   wkce-cww :     {E E' : List ℕ} → (π : Wk Γ Γ') → (ϖ : WkC Γ E) → (ϖ' : WkC Γ' E')
               → (θ : WkCE π ϖ ϖ')
               → (WkCE (wk-cong {A = X} π) {E = E} {E' = E'} (wkc-cons ϖ) (wkc-cons ϖ'))

  wkce-z-l : {e : ℕ} {E' : List ℕ} {π : Wk Γ Γ'} {ϖ : WkC Γ []} {ϖ' : WkC Γ' (e ∷ E')} → WkCE π ϖ ϖ' → ⊥
  wkce-z-l (wkce-ww- π ϖ ϖ' θ) = wkce-z-l θ
  wkce-z-l (wkce-cww π ϖ ϖ' θ) = wkce-z-l θ

  wkce-z-r : {e : ℕ} {E' : List ℕ} {π : Wk Γ Γ} {ϖ : WkC Γ (e ∷ E')}  {ϖ' : WkC Γ []} → WkCE π ϖ ϖ' → ⊥
  wkce-z-r (wkce-wc- π ϖ ϖ' e θ) = wk-absurd (wk-wk π) π
  wkce-z-r (wkce-ww- π ϖ ϖ' θ) = wk-absurd (wk-wk π) π
  wkce-z-r (wkce-cww π ϖ ϖ' θ) = wkce-z-r θ

  --------------------------------------------------------------------------

  data WkZ  : {E E' : EMetric} → (ϖ : WkN Γ E) → (ϖ' : WkN Γ E') → Set where
    wkz-nil       : {E E' : EMetric} → {ϖ : WkN ε E} → {ϖ' : WkN ε E'} → WkZ ϖ ϖ'
    wkz-cong     :   {E E' : EMetric}
                  → {ϖ : WkN Γ E} → {ϖ' : WkN Γ E'}
                  → {cnt₁ cnt₂ : ℕ}
                  → {nm₁ nm₂ : EElemR X}
                  → (cnt₁≤cnt₂ : cnt₁ ≤ cnt₂)
                  → (nm₁≤nm₂ : ((csn : (List (ℕ × ℕ))) → (proj₁ nm₁ csn) ≤ᴹ (proj₁ nm₂ csn)))
                  → (ϖ≤ϖ' : WkZ ϖ ϖ') → WkZ (wkn-cong {e = cnt₁ , nm₁} ϖ) (wkn-cong {e = cnt₂ , nm₂} ϖ')
    wkz-wk       :  {E E' : EMetric}
                  → {ϖ : WkN Γ E} → {ϖ' : WkN Γ E'}
                  → (ϖ≤ϖ' : WkZ ϖ ϖ') → WkZ (wkn-cons {Y = Y} ϖ) (wkn-cons {Y = Y} ϖ')

  wkz-id : {E : EMetric} → {ϖ : WkN Γ E} → WkZ ϖ ϖ
  wkz-id {E = E} {ϖ = wkn-nil} = wkz-nil
  wkz-id {E = E} {ϖ = wkn-cong ϖ} = wkz-cong ≤-refl (λ csn → ≤ᴹ-refl) wkz-id
  wkz-id {E = E} {ϖ = wkn-cons ϖ} = wkz-wk wkz-id

  wkz-l : {e : Σ[ X ∈ Ty ] (EElem X)} {E' : EMetric} {ϖ : WkN Γ []} {ϖ' : WkN Γ (e ∷ E')} → (ϕ : WkZ ϖ ϖ') → ⊥
  wkz-l (wkz-wk ϕ) = wkz-l ϕ

  wkz-r : {e : Σ[ X ∈ Ty ] (EElem X)} {E' : EMetric} {ϖ : WkN Γ (e ∷ E')}  {ϖ' : WkN Γ []} → (ϕ : WkZ ϖ ϖ') → ⊥
  wkz-r (wkz-wk ϕ) = wkz-r ϕ

  -----------------------------------------------------------------------

  data WkCZ  : {E E' : List ℕ} → (ϖ : WkC Γ E) → (ϖ' : WkC Γ E') → Set where
    wkcz-nil       : {ϖ : WkC ε []} → {ϖ' : WkC ε []} → WkCZ ϖ ϖ'
    wkcz-cong     :   {E E' : List ℕ}
                  → {ϖ : WkC Γ E} → {ϖ' : WkC Γ E'}
                  → {cnt₁ cnt₂ : ℕ}
                  → (cnt₁≤cnt₂ : cnt₁ ≤ cnt₂)
                  → (ϖ≤ϖ' : WkCZ ϖ ϖ') → WkCZ (wkc-cong {Y = Y} {e = cnt₁} ϖ) (wkc-cong {Y = Y} {e = cnt₂} ϖ')
    wkcz-wk       :  {E E' : List ℕ}
                  → {ϖ : WkC Γ E} → {ϖ' : WkC Γ E'}
                  → (ϖ≤ϖ' : WkCZ ϖ ϖ') → WkCZ (wkc-cons {Y = Y} ϖ) (wkc-cons {Y = Y} ϖ')

  wkcz-id : {E : List ℕ} → {ϖ : WkC Γ E} → WkCZ ϖ ϖ
  wkcz-id {E = E} {ϖ = wkc-nil} = wkcz-nil
  wkcz-id {E = E} {ϖ = wkc-cong ϖ} = wkcz-cong ≤-refl wkcz-id
  wkcz-id {E = E} {ϖ = wkc-cons ϖ} = wkcz-wk wkcz-id

  wkcz-l : {E' : List ℕ} {ϖ : WkC Γ []} {ϖ' : WkC Γ (n ∷ E')} → (ϕ : WkCZ ϖ ϖ') → ⊥
  wkcz-l (wkcz-wk ϕ) = wkcz-l ϕ

  wkcz-r : {E' : List ℕ} {ϖ : WkC Γ (n ∷ E')} {ϖ' : WkC Γ []} → (ϕ : WkCZ ϖ ϖ') → ⊥
  wkcz-r (wkcz-wk ϕ) = wkcz-r ϕ

  -----------------------------------------------------------------------

  -- TEMP
  -- data WkC : (Γ : Ctx) → (E : List ℕ) → Set where
  --   wkc-nil  : WkC ε []
  --   wkc-cong :   {Γ : Ctx} → {E : List ℕ} → {Y : Ty}
  --              → {e : ℕ} → (ϖ : WkC Γ E) → WkC (Γ ∙ Y) (e ∷ E)
  --   wkc-cons :   {Γ : Ctx} → {E : List ℕ}
  --              → {Y : Ty} → (ϖ : WkC Γ E) → WkC (Γ ∙ Y) E

  elist-to-clist : (E : EMetric) → List ℕ
  elist-to-clist [] = []
  elist-to-clist ((X , cnt , e) ∷ E) = cnt ∷ elist-to-clist E

  wkn-to-wkc : {E : EMetric} → (ϖ : WkN Γ E) → (WkC Γ (elist-to-clist E))
  wkn-to-wkc {E = []} wkn-nil = wkc-nil
  wkn-to-wkc {E = []} (wkn-cons ϖ) = wkc-cons (wkn-to-wkc {E = []} ϖ)
  wkn-to-wkc {E = (x ∷ E)} (wkn-cong ϖ) = wkc-cong (wkn-to-wkc {E = E} ϖ)
  wkn-to-wkc {E = (x ∷ E)} (wkn-cons ϖ) = wkc-cons (wkn-to-wkc {E = (x ∷ E)} ϖ)

  wkc-cong-comm : {E : EMetric} → {e : EElem Y} → (ϖ : WkN Γ E) → (wkc-cong {Y = Y} {e = proj₁ e} (wkn-to-wkc ϖ)) ≡ (wkn-to-wkc (wkn-cong {e = e} ϖ))
  wkc-cong-comm wkn-nil = refl
  wkc-cong-comm (wkn-cong ϖ) = refl
  wkc-cong-comm (wkn-cons ϖ) = refl

  wkc-cons-comm : {E : EMetric} → (ϖ : WkN Γ E) → (wkc-cons {Y = Y} (wkn-to-wkc ϖ)) ≡ (wkn-to-wkc (wkn-cons ϖ))
  wkc-cons-comm wkn-nil = refl
  wkc-cons-comm (wkn-cong ϖ) = refl
  wkc-cons-comm {Γ = ε ∙ Y} {E = []} (wkn-cons {Y = Y} ϖ) = refl
  wkc-cons-comm {Γ = Γ ∙ X ∙ Y} {E = []} (wkn-cons {Y = Y} ϖ) = refl
  wkc-cons-comm {Γ = Γ ∙ X ∙ Y} {E = x ∷ E} (wkn-cons {Y = Y} ϖ) = refl

  {- without inequality
  wkz-to-wkcz : {E E' : EMetric} {ϖ : WkN Γ E} {ϖ' : WkN Γ E'} → (ϕ : WkZ ϖ ϖ') → WkCZ (wkn-to-wkc ϖ) (wkn-to-wkc ϖ')
  wkz-to-wkcz {ϖ = wkn-nil} {ϖ' = wkn-nil} wkz-nil = wkcz-nil
  wkz-to-wkcz {ϖ = ϖ} {ϖ' = ϖ'} (wkz-cong nm₁≤nm₂ ϕ) = wkcz-cong (wkz-to-wkcz ϕ)
  wkz-to-wkcz {ϖ = wkn-cons {Y = Y} ϖ} {ϖ' = wkn-cons {Y = Y'} ϖ'} (wkz-wk ϕ) rewrite sym (wkc-cons-comm {Y = Y} ϖ) | sym (wkc-cons-comm {Y = Y'} ϖ') = wkcz-wk (wkz-to-wkcz ϕ)
  -}

  wkz-to-wkcz : {E E' : EMetric} {ϖ : WkN Γ E} {ϖ' : WkN Γ E'} → (ϕ : WkZ ϖ ϖ') → WkCZ (wkn-to-wkc ϖ) (wkn-to-wkc ϖ')
  wkz-to-wkcz {ϖ = wkn-nil} {ϖ' = wkn-nil} wkz-nil = wkcz-nil
  wkz-to-wkcz {ϖ = ϖ} {ϖ' = ϖ'} (wkz-cong cnt₁≤cnt₂ nm₁≤nm₂ ϕ) = wkcz-cong cnt₁≤cnt₂ (wkz-to-wkcz ϕ)
  wkz-to-wkcz {ϖ = wkn-cons {Y = Y} ϖ} {ϖ' = wkn-cons {Y = Y'} ϖ'} (wkz-wk ϕ) rewrite sym (wkc-cons-comm {Y = Y} ϖ) | sym (wkc-cons-comm {Y = Y'} ϖ') = wkcz-wk (wkz-to-wkcz ϕ)

  wke-to-wkce : {E E' : EMetric} {ϖ : WkN Γ E} {ϖ' : WkN Γ' E'} {π : Wk Γ Γ'} → (θ : WkE π ϖ ϖ') → WkCE π (wkn-to-wkc ϖ) (wkn-to-wkc ϖ')
  wke-to-wkce {E = E} {E' = E'} {ϖ = ϖ} {ϖ' = ϖ'} {π = π} wke-ε = wkce-ε
  wke-to-wkce {E = E} {E' = E'} {ϖ = ϖ} {ϖ' = ϖ'} {π = π} (wke-ccc π₁ ϖ₁ ϖ'' e θ) = wkce-ccc π₁ (wkn-to-wkc ϖ₁) (wkn-to-wkc ϖ'') (e .proj₁) (wke-to-wkce θ)
  wke-to-wkce {E = E} {E' = E'} {ϖ = ϖ} {ϖ' = ϖ'} {π = π} (wke-wc- π₁ ϖ₁ ϖ'' e θ) = wkce-wc- π₁ (wkn-to-wkc ϖ₁) (wkn-to-wkc ϖ') (e .proj₁) (wke-to-wkce θ)
  wke-to-wkce {E = E} {E' = E'} {ϖ = wkn-cons {Y = Y} ϖ} {ϖ' = ϖ'} {π = π} (wke-ww- {X = X} π₁ ϖ ϖ' θ) rewrite sym (wkc-cons-comm {Y = Y} ϖ) = wkce-ww- π₁ (wkn-to-wkc ϖ) (wkn-to-wkc ϖ') (wke-to-wkce θ)
  wke-to-wkce {E = E} {E' = E'} {ϖ = wkn-cons {Y = Y} ϖ} {ϖ' = wkn-cons {Y = Y'} ϖ'} {π = π} (wke-cww π₁ ϖ ϖ' θ) rewrite sym (wkc-cons-comm {Y = Y} ϖ) | sym (wkc-cons-comm {Y = Y'} ϖ') = wkce-cww π₁ (wkn-to-wkc ϖ) (wkn-to-wkc ϖ') (wke-to-wkce θ)

  {-
   wkce-ww- :     {E E' : List ℕ} → (π : Wk Γ Γ') → (ϖ : WkC Γ E) → (ϖ' : WkC Γ' E')
               → (θ : WkCE π ϖ ϖ')
               → (WkCE (wk-wk {A = X} π) {E = E} {E' = E'} (wkc-cons ϖ) ϖ')
   wke-ww- :     {E E' : EMetric} → (π : Wk Γ Γ') → (ϖ : WkN Γ E) → (ϖ' : WkN Γ' E')
               → (θ : WkE π ϖ ϖ')
               → (WkE (wk-wk {A = X} π) {E = E} {E' = E'} (wkn-cons ϖ) ϖ')
  -}

  lookup-mono-metric : (i : Γ ∋ Y) → (E : EMetric) → WkN Γ E → EElem Y
  lookup-mono-metric Cx.h ((Y , e) ∷ ne) (wkn-cong ϖ) = e
  lookup-mono-metric (Cx.t i) ((X , e) ∷ ne) (wkn-cong ϖ) = lookup-mono-metric i ne ϖ
  lookup-mono-metric {Y = Y} Cx.h [] (wkn-cons ϖ) = (lcount {Z = Y} Cx.h [] (wkn-to-wkc (wkn-cons ϖ))) , (λ _ → zero-metric) , λ _ → ≤ᴹ-refl
  lookup-mono-metric {Y = Y} Cx.h (x ∷ E) (wkn-cons ϖ) = (lcount {Z = Y} Cx.h (elist-to-clist (x ∷ E)) (wkn-to-wkc (wkn-cons ϖ))) , (λ _ → zero-metric) , λ _ → ≤ᴹ-refl
  lookup-mono-metric {Y = Y} (Cx.t i) [] (wkn-cons ϖ) = (lcount (t {B = Y} i) [] (wkn-to-wkc (wkn-cons ϖ))) , (λ _ → zero-metric) , λ _ → ≤ᴹ-refl
  lookup-mono-metric (Cx.t i) (x ∷ E) (wkn-cons ϖ) = lookup-mono-metric i (x ∷ E) ϖ

  empty-lookup : (i : Γ ∋ X) → (ϖ : WkN Γ []) → lookup-mono-metric i [] ϖ ≡ (1 , ((λ _ → zero-metric) , λ _ → ≤ᴹ-refl))
  empty-lookup Cx.h (wkn-cons ϖ) = refl
  empty-lookup (Cx.t i) (wkn-cons ϖ) = refl

  empty-lcount : (i : Γ ∋ X) → (ϖ : WkC Γ []) → lcount i [] ϖ ≡ 1
  empty-lcount Cx.h (wkc-cons ϖ) = refl
  empty-lcount (Cx.t i) (wkc-cons ϖ) = refl

  -- DEPRECATED:
  -- lookup-wkx-lemma : (i : Γ ∋ X) → (E E' : EMetric) → (π : Wk Γ Γ) → (ϖ : WkN Γ E) → (ϖ' : WkN Γ E') → (ϕ : WkX π ϖ ϖ')
  --             → (csn : List (ℕ × ℕ)) → (proj₁ (proj₂ (lookup-mono-metric i E ϖ))) csn ≤ᴹ (proj₁ (proj₂ (lookup-mono-metric i E' ϖ'))) csn
  -- lookup-wkx-lemma Cx.h [] [] π ϖ ϖ' (wkx-bc θ) csn rewrite empty-lookup h ϖ | empty-lookup h ϖ' = ≤ᴹ-refl
  -- lookup-wkx-lemma Cx.h [] [] π ϖ ϖ' (wkx-wk ϕ) csn = ≤ᴹ-refl
  -- lookup-wkx-lemma Cx.h [] (x ∷ E') π ϖ ϖ' (wkx-bc θ) csn = ql (wke-z-l θ)
  --                                                            (proj₁ (proj₂ (lookup-mono-metric h [] ϖ)) csn ≤ᴹ
  --                                                             proj₁ (proj₂ (lookup-mono-metric h (x ∷ E') ϖ')) csn)
  -- lookup-wkx-lemma Cx.h [] (x ∷ E') π ϖ ϖ' (wkx-wk ϕ) csn = ≤ᴹ-refl
  -- lookup-wkx-lemma Cx.h (x ∷ E) [] π ϖ ϖ' (wkx-bc θ) csn = ql (wke-z-r θ)
  --                                                           (proj₁ (proj₂ (lookup-mono-metric h (x ∷ E) ϖ)) csn ≤ᴹ
  --                                                            proj₁ (proj₂ (lookup-mono-metric h [] ϖ')) csn)
  -- lookup-wkx-lemma Cx.h (x ∷ E) [] π ϖ ϖ' (wkx-wk ϕ) csn = ≤ᴹ-refl
  -- lookup-wkx-lemma Cx.h (x ∷ E) (x₁ ∷ E') π ϖ ϖ' (wkx-bc (wke-ccc π₁ ϖ₁ ϖ'' e θ)) csn = ≤ᴹ-refl
  -- lookup-wkx-lemma Cx.h (x ∷ E) (x₁ ∷ E') π ϖ ϖ' (wkx-bc (wke-wc- π₁ ϖ₁ ϖ'' e θ)) csn = ql (wk-absurd (wk-wk π₁) π₁)
  --                                                                                        (proj₁ (proj₂ (lookup-mono-metric h ((_ , e) ∷ E) (wkn-cong ϖ₁)))
  --                                                                                         csn
  --                                                                                         ≤ᴹ proj₁ (proj₂ (lookup-mono-metric h (x₁ ∷ E') ϖ')) csn)
  -- lookup-wkx-lemma Cx.h (x ∷ E) (x₁ ∷ E') π ϖ ϖ' (wkx-bc (wke-ww- π₁ ϖ₁ ϖ'' θ)) csn = ql (wk-absurd (wk-wk π₁) π₁)
  --                                                                                      (proj₁ (proj₂ (lookup-mono-metric h (x ∷ E) (wkn-cons ϖ₁))) csn ≤ᴹ
  --                                                                                       proj₁ (proj₂ (lookup-mono-metric h (x₁ ∷ E') ϖ')) csn)
  -- lookup-wkx-lemma Cx.h (x ∷ E) (x₁ ∷ E') π ϖ ϖ' (wkx-bc (wke-cww π₁ ϖ₁ ϖ'' θ)) csn = ≤ᴹ-refl
  -- lookup-wkx-lemma Cx.h (x ∷ E) (x₁ ∷ E') π ϖ ϖ' (wkx-cong _ nm₁≤nm₂ ϕ) csn = nm₁≤nm₂ csn
  -- lookup-wkx-lemma Cx.h (x ∷ E) (x₁ ∷ E') π ϖ ϖ' (wkx-wk ϕ) csn = ≤ᴹ-refl
  -- lookup-wkx-lemma (Cx.t i) [] [] π ϖ ϖ' (wkx-bc θ) csn rewrite empty-lookup (t i) ϖ | empty-lookup (t i) ϖ' = ≤ᴹ-refl
  -- lookup-wkx-lemma (Cx.t i) [] [] π ϖ ϖ' (wkx-wk ϕ) csn = ≤ᴹ-refl
  -- lookup-wkx-lemma (Cx.t i) [] (x ∷ E') π ϖ ϖ' (wkx-bc θ) csn = ql (wke-z-l θ)
  --                                                                (proj₁ (proj₂ (lookup-mono-metric (t i) [] ϖ)) csn ≤ᴹ
  --                                                                 proj₁ (proj₂ (lookup-mono-metric (t i) (x ∷ E') ϖ')) csn)
  -- lookup-wkx-lemma (Cx.t i) [] (x ∷ E') π ϖ ϖ' (wkx-wk ϕ) csn = ql (wkx-z-l ϕ)
  --                                                                (proj₁ (proj₂ (lookup-mono-metric (t {B = R₀} i) [] (wkn-cons (ql (wkx-z-l ϕ) (WkN _ []))))) csn ≤ᴹ
  --                                                                 proj₁ (proj₂ (lookup-mono-metric (t {B = R₀} i) (x ∷ E') (wkn-cons _))) csn)
  -- lookup-wkx-lemma (Cx.t i) (x ∷ E) [] π ϖ ϖ' (wkx-bc θ) csn = ql (wke-z-r θ)
  --                                                               (proj₁ (proj₂ (lookup-mono-metric (t i) (x ∷ E) ϖ)) csn ≤ᴹ
  --                                                                proj₁ (proj₂ (lookup-mono-metric (t i) [] ϖ')) csn)
  -- lookup-wkx-lemma (Cx.t i) (x ∷ E) [] π ϖ ϖ' (wkx-wk ϕ) csn = ql (wkx-z-r ϕ)
  --                                                               (proj₁ (proj₂ (lookup-mono-metric (t {B = R₀} i) (x ∷ E) (wkn-cons _))) csn
  --                                                                ≤ᴹ proj₁ (proj₂ (lookup-mono-metric (t {B = R₀} i) [] (wkn-cons (ql (wkx-z-r ϕ) (WkN _ []))))) csn)
  -- lookup-wkx-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') π ϖ ϖ' (wkx-bc (wke-ccc π₁ ϖ₁ ϖ'' e θ)) csn = lookup-wkx-lemma i E E' π₁ ϖ₁ ϖ'' (wkx-bc θ) csn
  -- lookup-wkx-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') π ϖ ϖ' (wkx-bc (wke-wc- π₁ ϖ₁ ϖ'' e θ)) csn = ql (wk-absurd (wk-wk π₁) π₁)
  --                                                                                            (proj₁
  --                                                                                             (proj₂ (lookup-mono-metric (t i) ((_ , e) ∷ E) (wkn-cong ϖ₁))) csn
  --                                                                                             ≤ᴹ proj₁ (proj₂ (lookup-mono-metric (t i) (x₁ ∷ E') ϖ')) csn)
  -- lookup-wkx-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') π ϖ ϖ' (wkx-bc (wke-ww- π₁ ϖ₁ ϖ'' θ)) csn = ql (wk-absurd (wk-wk π₁) π₁)
  --                                                                                          (proj₁ (proj₂ (lookup-mono-metric (t {B = R₀} i) (x ∷ E) (wkn-cons ϖ₁))) csn
  --                                                                                           ≤ᴹ proj₁ (proj₂ (lookup-mono-metric (t i) (x₁ ∷ E') ϖ')) csn)
  -- lookup-wkx-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') π ϖ ϖ' (wkx-bc (wke-cww π₁ ϖ₁ ϖ'' θ)) csn = lookup-wkx-lemma i (x ∷ E) (x₁ ∷ E') π₁ ϖ₁ ϖ'' (wkx-bc θ) csn
  -- lookup-wkx-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') π ϖ ϖ' (wkx-cong {ϖ = ϖ₁} {ϖ' = ϖ₁'} _ nm₁≤nm₂ ϕ) csn = lookup-wkx-lemma i E E' (wk-prev {X = R₀} (wk-cong _)) ϖ₁ ϖ₁' ϕ csn
  -- lookup-wkx-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') π ϖ ϖ' (wkx-wk {ϖ = ϖ₁} {ϖ' = ϖ₁'} ϕ) csn = lookup-wkx-lemma i (x ∷ E) (x₁ ∷ E') (wk-prev {X = R₀} (wk-cong _)) ϖ₁ ϖ₁' ϕ csn


  lookup-wkz-lemma : (i : Γ ∋ X) → (E E' : EMetric) → (ϖ : WkN Γ E) → (ϖ' : WkN Γ E') → (ϕ : WkZ ϖ ϖ')
              → (csn : List (ℕ × ℕ)) → (proj₁ (proj₂ (lookup-mono-metric i E ϖ))) csn ≤ᴹ (proj₁ (proj₂ (lookup-mono-metric i E' ϖ'))) csn
  lookup-wkz-lemma Cx.h [] [] (wkn-cons ϖ) ϖ' (wkz-wk ϕ) csn = ≤ᴹ-refl
  lookup-wkz-lemma Cx.h [] (x ∷ E') (wkn-cons ϖ) ϖ' (wkz-wk ϕ) csn = ≤ᴹ-refl
  lookup-wkz-lemma Cx.h (x ∷ E) [] (wkn-cong ϖ) ϖ' () csn
  lookup-wkz-lemma Cx.h (x ∷ E) [] (wkn-cons ϖ) ϖ' (wkz-wk ϕ) csn = ≤ᴹ-refl
  lookup-wkz-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wkn-cong ϖ) ϖ' (wkz-cong _ nm₁≤nm₂ ϕ) csn = nm₁≤nm₂ csn
  lookup-wkz-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wkn-cons ϖ) ϖ' (wkz-wk ϕ) csn = ≤ᴹ-refl
  lookup-wkz-lemma (Cx.t i) [] [] (wkn-cons ϖ) ϖ' (wkz-wk ϕ) csn = ≤ᴹ-refl
  lookup-wkz-lemma (Cx.t i) [] (x ∷ E') (wkn-cons ϖ) ϖ' (wkz-wk ϕ) csn = ql (wkz-l ϕ) (proj₁ (proj₂ (lookup-mono-metric (t {B = R₀} i) [] (wkn-cons ϖ))) csn ≤ᴹ proj₁ (proj₂ (lookup-mono-metric (t {B = R₀} i) (x ∷ E') (wkn-cons _))) csn)
    --ql (wkz-l ϕ) (proj₁ (proj₂ (lookup-mono-metric (t {B = R₀} i) [] (wkn-cons ϖ))) csn ≤ᴹ proj₁ (proj₂ (lookup-mono-metric (t {B = R₀} i) (x ∷ E') (wkn-cons _))) csn)
  lookup-wkz-lemma (Cx.t i) (x ∷ E) [] (wkn-cong ϖ) ϖ' () csn
  lookup-wkz-lemma (Cx.t i) (x ∷ E) [] (wkn-cons ϖ) ϖ' (wkz-wk ϕ) csn = ql (wkz-r ϕ) (proj₁ (proj₂ (lookup-mono-metric (t {B = R₀} i) (x ∷ E) (wkn-cons ϖ))) csn ≤ᴹ proj₁ (proj₂ (lookup-mono-metric (t {B = R₀} i) [] (wkn-cons (ql (wkz-r ϕ) (WkN _ []))))) csn)
    --ql (wkz-r ϕ) (proj₁ (proj₂ (lookup-mono-metric (t {B = R₀} i) (x ∷ E) (wkn-cons ϖ))) csn ≤ᴹ proj₁ (proj₂ (lookup-mono-metric (t {B = R₀} i) [] (wkn-cons (ql (wkz-r ϕ) (WkN _ []))))) csn)
  lookup-wkz-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wkn-cong ϖ) ϖ' (wkz-cong {ϖ = ϖ₁} {ϖ' = ϖ₁'} _ nm₁≤nm₂ ϕ) csn = lookup-wkz-lemma i E E' ϖ ϖ₁' ϕ csn
  lookup-wkz-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wkn-cons ϖ) ϖ' (wkz-wk ϕ) csn = lookup-wkz-lemma i (x ∷ E) (x₁ ∷ E') ϖ _ ϕ csn


  lookup-wke-lemma : (i : Γ' ∋ X) → (E E' : EMetric)
              → (π : Wk Γ Γ') → (ϖ : WkN Γ E) → (ϖ' : WkN Γ' E') → (θ : WkE π ϖ ϖ')
              → (lookup-mono-metric i E' ϖ') ≡ (lookup-mono-metric (wk-mem π i) E ϖ)
  lookup-wke-lemma Cx.h [] [] (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π₁ ϖ₁ ϖ'' θ) = refl
  lookup-wke-lemma Cx.h [] [] (wk-wk π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-ww- π₁ ϖ₁ ϖ'' θ) = refl
  lookup-wke-lemma Cx.h [] (x ∷ E') (wk-cong π) (wkn-cons ϖ) (wkn-cong ϖ') ()
  lookup-wke-lemma Cx.h [] (x ∷ E') (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π₁ ϖ₁ ϖ'' θ) = refl
  lookup-wke-lemma Cx.h [] (x ∷ E') (wk-wk π) (wkn-cons ϖ) (wkn-cong ϖ') (wke-ww- π₁ ϖ₁ ϖ'' θ) = ql (wke-z-l θ)
                                                                                                  (lookup-mono-metric h ((_ , _) ∷ E') (wkn-cong ϖ') ≡
                                                                                                   lookup-mono-metric (wk-mem (wk-wk {A = R₀} π) h) [] (wkn-cons ϖ))
  lookup-wke-lemma Cx.h [] (x ∷ E') (wk-wk π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-ww- π₁ ϖ₁ ϖ'' θ) = refl
  lookup-wke-lemma Cx.h (x ∷ E) [] (wk-cong π) (wkn-cong ϖ) (wkn-cons ϖ') ()
  lookup-wke-lemma Cx.h (x ∷ E) [] (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π₁ ϖ₁ ϖ'' θ) = refl
  lookup-wke-lemma Cx.h (x ∷ E) [] (wk-wk π) (wkn-cong ϖ) (wkn-cons ϖ') (wke-wc- π₁ ϖ₁ ϖ'' e θ) = lookup-wke-lemma h E [] π ϖ (wkn-cons ϖ') θ
  lookup-wke-lemma Cx.h (x ∷ E) [] (wk-wk π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-ww- π₁ ϖ₁ ϖ'' θ) = lookup-wke-lemma h (x ∷ E) [] π ϖ (wkn-cons ϖ') θ
  lookup-wke-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wk-cong π) (wkn-cong ϖ) (wkn-cong ϖ') (wke-ccc π₁ ϖ₁ ϖ'' e θ) = refl
  lookup-wke-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wk-cong π) (wkn-cong ϖ) (wkn-cons ϖ') ()
  lookup-wke-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wk-cong π) (wkn-cons ϖ) (wkn-cong ϖ') ()
  lookup-wke-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π₁ ϖ₁ ϖ'' θ) = refl
  lookup-wke-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wk-wk π) (wkn-cong ϖ) (wkn-cong ϖ') (wke-wc- π₁ ϖ₁ ϖ'' e θ) = lookup-wke-lemma h E ((_ , _) ∷ E') π ϖ (wkn-cong ϖ') θ
  lookup-wke-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wk-wk π) (wkn-cong ϖ) (wkn-cons ϖ') (wke-wc- π₁ ϖ₁ ϖ'' e θ) = lookup-wke-lemma h E (x₁ ∷ E') π ϖ (wkn-cons ϖ') θ
  lookup-wke-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wk-wk π) (wkn-cons ϖ) (wkn-cong ϖ') (wke-ww- π₁ ϖ₁ ϖ'' θ) = lookup-wke-lemma h (x ∷ E) ((_ , _) ∷ E') π ϖ (wkn-cong ϖ') θ
  lookup-wke-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wk-wk π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-ww- π₁ ϖ₁ ϖ'' θ) = lookup-wke-lemma h (x ∷ E) (x₁ ∷ E') π ϖ (wkn-cons ϖ') θ
  lookup-wke-lemma (Cx.t i) [] [] (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π₁ ϖ₁ ϖ'' θ) = refl
  lookup-wke-lemma (Cx.t i) [] [] (wk-wk π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-ww- π₁ ϖ₁ ϖ'' θ) = refl
  lookup-wke-lemma (Cx.t i) [] (x ∷ E') (wk-cong π) (wkn-cons ϖ) (wkn-cong ϖ') ()
  lookup-wke-lemma (Cx.t i) [] (x ∷ E') (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π₁ ϖ₁ ϖ'' θ) = ql (wke-z-l θ)
                                                                                                        (lookup-mono-metric (t {B = R₀} i) (x ∷ E') (wkn-cons ϖ') ≡
                                                                                                         lookup-mono-metric (wk-mem (wk-cong {A = R₀} π) (t i)) [] (wkn-cons ϖ))
  lookup-wke-lemma (Cx.t i) [] (x ∷ E') (wk-wk π) (wkn-cons ϖ) (wkn-cong ϖ') (wke-ww- π₁ ϖ₁ ϖ'' θ) = ql (wke-z-l θ)
                                                                                                      (lookup-mono-metric (t i) (x ∷ E') (wkn-cong ϖ') ≡
                                                                                                       lookup-mono-metric (wk-mem (wk-wk {A = R₀} π) (t i)) [] (wkn-cons ϖ))
  lookup-wke-lemma (Cx.t i) [] (x ∷ E') (wk-wk π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-ww- π₁ ϖ₁ ϖ'' θ) = ql (wke-z-l θ)
                                                                                                      (lookup-mono-metric (t {B = R₀} i) (x ∷ E') (wkn-cons ϖ') ≡
                                                                                                       lookup-mono-metric (wk-mem (wk-wk {A = R₀} π) (t i)) [] (wkn-cons ϖ))
  lookup-wke-lemma (Cx.t i) (x ∷ E) [] (wk-cong π) (wkn-cong ϖ) (wkn-cons ϖ') ()
  lookup-wke-lemma (Cx.t i) (x ∷ E) [] (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ) rewrite sym (empty-lookup i  ϖ') = lookup-wke-lemma i (x ∷ E) [] π ϖ ϖ' θ
  lookup-wke-lemma (Cx.t i) (x ∷ E) [] (wk-wk π) (wkn-cong ϖ) (wkn-cons ϖ') (wke-wc- π₁ ϖ₁ ϖ'' e θ) = lookup-wke-lemma (t i) E [] π ϖ (wkn-cons ϖ') θ
  lookup-wke-lemma (Cx.t i) (x ∷ E) [] (wk-wk π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-ww- π₁ ϖ₁ ϖ'' θ) = lookup-wke-lemma (t i) (x ∷ E) [] π ϖ (wkn-cons ϖ') θ
  lookup-wke-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wk-cong π) (wkn-cong ϖ) (wkn-cong ϖ') (wke-ccc π₁ ϖ₁ ϖ'' e θ) = lookup-wke-lemma i E E' π ϖ ϖ' θ
  lookup-wke-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wk-cong π) (wkn-cong ϖ) (wkn-cons ϖ') ()
  lookup-wke-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wk-cong π) (wkn-cons ϖ) (wkn-cong ϖ') ()
  lookup-wke-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π₁ ϖ₁ ϖ'' θ) = lookup-wke-lemma i (x ∷ E) (x₁ ∷ E') π ϖ ϖ' θ
  lookup-wke-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wk-wk π) (wkn-cong ϖ) (wkn-cong ϖ') (wke-wc- π₁ ϖ₁ ϖ'' e θ) = lookup-wke-lemma (t i) E ((_ , _) ∷ E') π ϖ (wkn-cong ϖ') θ
  lookup-wke-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wk-wk π) (wkn-cong ϖ) (wkn-cons ϖ') (wke-wc- π₁ ϖ₁ ϖ'' e θ) = lookup-wke-lemma (t i) E (x₁ ∷ E') π ϖ (wkn-cons ϖ') θ
  lookup-wke-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wk-wk π) (wkn-cons ϖ) (wkn-cong ϖ') (wke-ww- π₁ ϖ₁ ϖ'' θ) = lookup-wke-lemma (t i) (x ∷ E) ((_ , _) ∷ E') π ϖ (wkn-cong ϖ') θ
  lookup-wke-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wk-wk π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-ww- π₁ ϖ₁ ϖ'' θ) = lookup-wke-lemma (t i) (x ∷ E) (x₁ ∷ E') π ϖ (wkn-cons ϖ') θ


  lcount-wkce-lemma : (i : Γ' ∋ X) → (E E' : List ℕ)
              → (π : Wk Γ Γ') → (ϖ : WkC Γ E) → (ϖ' : WkC Γ' E') → (θ : WkCE π ϖ ϖ')
              → (lcount i E' ϖ') ≡ (lcount (wk-mem π i) E ϖ)
  lcount-wkce-lemma Cx.h [] [] (wk-cong π) (wkc-cons ϖ) (wkc-cons ϖ') (wkce-cww π₁ ϖ₁ ϖ'' θ) = refl
  lcount-wkce-lemma Cx.h [] [] (wk-wk π) (wkc-cons ϖ) (wkc-cons ϖ') (wkce-ww- π₁ ϖ₁ ϖ'' θ) = refl
  lcount-wkce-lemma Cx.h [] (x ∷ E') (wk-cong π) (wkc-cons ϖ) (wkc-cong ϖ') ()
  lcount-wkce-lemma Cx.h [] (x ∷ E') (wk-cong π) (wkc-cons ϖ) (wkc-cons ϖ') (wkce-cww π₁ ϖ₁ ϖ'' θ) = refl
  lcount-wkce-lemma Cx.h [] (x ∷ E') (wk-wk π) (wkc-cons ϖ) (wkc-cong ϖ') (wkce-ww- π₁ ϖ₁ ϖ'' θ) = ql (wkce-z-l θ)
                                                                                                    (lcount {Z = R₀} h (x ∷ E') (wkc-cong ϖ') ≡
                                                                                                     lcount (wk-mem (wk-wk {A = R₀} π) h) [] (wkc-cons ϖ))
  lcount-wkce-lemma Cx.h [] (x ∷ E') (wk-wk π) (wkc-cons ϖ) (wkc-cons ϖ') (wkce-ww- π₁ ϖ₁ ϖ'' θ) = refl
  lcount-wkce-lemma Cx.h (x ∷ E) [] (wk-cong π) (wkc-cong ϖ) (wkc-cons ϖ') ()
  lcount-wkce-lemma Cx.h (x ∷ E) [] (wk-cong π) (wkc-cons ϖ) (wkc-cons ϖ') (wkce-cww π₁ ϖ₁ ϖ'' θ) = refl
  lcount-wkce-lemma Cx.h (x ∷ E) [] (wk-wk π) (wkc-cong ϖ) (wkc-cons ϖ') (wkce-wc- π₁ ϖ₁ ϖ'' e θ) = lcount-wkce-lemma h E [] π ϖ (wkc-cons ϖ') θ
  lcount-wkce-lemma Cx.h (x ∷ E) [] (wk-wk π) (wkc-cons ϖ) (wkc-cons ϖ') (wkce-ww- π₁ ϖ₁ ϖ'' θ) = lcount-wkce-lemma h (x ∷ E) [] π ϖ (wkc-cons ϖ') θ
  lcount-wkce-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wk-cong π) (wkc-cong ϖ) (wkc-cong ϖ') (wkce-ccc π₁ ϖ₁ ϖ'' e θ) = refl
  lcount-wkce-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wk-cong π) (wkc-cong ϖ) (wkc-cons ϖ') ()
  lcount-wkce-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wk-cong π) (wkc-cons ϖ) (wkc-cong ϖ') ()
  lcount-wkce-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wk-cong π) (wkc-cons ϖ) (wkc-cons ϖ') (wkce-cww π₁ ϖ₁ ϖ'' θ) = refl
  lcount-wkce-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wk-wk π) (wkc-cong ϖ) (wkc-cong ϖ') (wkce-wc- π₁ ϖ₁ ϖ'' e θ) = lcount-wkce-lemma h E (x₁ ∷ E') π ϖ (wkc-cong ϖ') θ
  lcount-wkce-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wk-wk π) (wkc-cong ϖ) (wkc-cons ϖ') (wkce-wc- π₁ ϖ₁ ϖ'' e θ) = lcount-wkce-lemma h E (x₁ ∷ E') π ϖ (wkc-cons ϖ') θ
  lcount-wkce-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wk-wk π) (wkc-cons ϖ) (wkc-cong ϖ') (wkce-ww- π₁ ϖ₁ ϖ'' θ) = lcount-wkce-lemma h (x ∷ E) (x₁ ∷ E') π ϖ (wkc-cong ϖ') θ
  lcount-wkce-lemma Cx.h (x ∷ E) (x₁ ∷ E') (wk-wk π) (wkc-cons ϖ) (wkc-cons ϖ') (wkce-ww- π₁ ϖ₁ ϖ'' θ) = lcount-wkce-lemma h (x ∷ E) (x₁ ∷ E') π ϖ (wkc-cons ϖ') θ
  lcount-wkce-lemma (Cx.t i) [] [] (wk-cong π) (wkc-cons ϖ) (wkc-cons ϖ') (wkce-cww π₁ ϖ₁ ϖ'' θ) = refl
  lcount-wkce-lemma (Cx.t i) [] [] (wk-wk π) (wkc-cons ϖ) (wkc-cons ϖ') (wkce-ww- π₁ ϖ₁ ϖ'' θ) = refl
  lcount-wkce-lemma (Cx.t i) [] (x ∷ E') (wk-cong π) (wkc-cons ϖ) (wkc-cong ϖ') ()
  lcount-wkce-lemma (Cx.t i) [] (x ∷ E') (wk-cong π) (wkc-cons ϖ) (wkc-cons ϖ') (wkce-cww π₁ ϖ₁ ϖ'' θ) = ql (wkce-z-l θ)
                                                                                                          (lcount (t {B = R₀} i) (x ∷ E') (wkc-cons ϖ') ≡
                                                                                                           lcount (wk-mem (wk-cong {A = R₀} π) (t i)) [] (wkc-cons ϖ))
  lcount-wkce-lemma (Cx.t i) [] (x ∷ E') (wk-wk π) (wkc-cons ϖ) (wkc-cong ϖ') (wkce-ww- π₁ ϖ₁ ϖ'' θ) = ql (wkce-z-l θ)
                                                                                                        (lcount (t {B = R₀} i) (x ∷ E') (wkc-cong ϖ') ≡
                                                                                                         lcount (wk-mem (wk-wk {A = R₀} π) (t i)) [] (wkc-cons ϖ))
  lcount-wkce-lemma (Cx.t i) [] (x ∷ E') (wk-wk π) (wkc-cons ϖ) (wkc-cons ϖ') (wkce-ww- π₁ ϖ₁ ϖ'' θ) = ql (wkce-z-l θ)
                                                                                                        (lcount (t {B = R₀} i) (x ∷ E') (wkc-cons ϖ') ≡
                                                                                                         lcount (wk-mem (wk-wk {A = R₀} π) (t i)) [] (wkc-cons ϖ))
  lcount-wkce-lemma (Cx.t i) (x ∷ E) [] (wk-cong π) (wkc-cong ϖ) (wkc-cons ϖ') ()
  lcount-wkce-lemma (Cx.t i) (x ∷ E) [] (wk-cong π) (wkc-cons ϖ) (wkc-cons ϖ') (wkce-cww π₁ ϖ₁ ϖ'' θ) rewrite sym (empty-lcount i  ϖ') = lcount-wkce-lemma i (x ∷ E) [] π ϖ ϖ' θ
  lcount-wkce-lemma (Cx.t i) (x ∷ E) [] (wk-wk π) (wkc-cong ϖ) (wkc-cons ϖ') (wkce-wc- π₁ ϖ₁ ϖ'' e θ) = lcount-wkce-lemma (t i) E [] π ϖ (wkc-cons ϖ') θ
  lcount-wkce-lemma (Cx.t i) (x ∷ E) [] (wk-wk π) (wkc-cons ϖ) (wkc-cons ϖ') (wkce-ww- π₁ ϖ₁ ϖ'' θ) = lcount-wkce-lemma (t i) (x ∷ E) [] π ϖ (wkc-cons ϖ') θ
  lcount-wkce-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wk-cong π) (wkc-cong ϖ) (wkc-cong ϖ') (wkce-ccc π₁ ϖ₁ ϖ'' e θ) = lcount-wkce-lemma i E E' π ϖ ϖ' θ
  lcount-wkce-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wk-cong π) (wkc-cong ϖ) (wkc-cons ϖ') ()
  lcount-wkce-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wk-cong π) (wkc-cons ϖ) (wkc-cong ϖ') ()
  lcount-wkce-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wk-cong π) (wkc-cons ϖ) (wkc-cons ϖ') (wkce-cww π₁ ϖ₁ ϖ'' θ) = lcount-wkce-lemma i (x ∷ E) (x₁ ∷ E') π ϖ ϖ' θ
  lcount-wkce-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wk-wk π) (wkc-cong ϖ) (wkc-cong ϖ') (wkce-wc- π₁ ϖ₁ ϖ'' e θ) = lcount-wkce-lemma (t i) E (x₁ ∷ E') π ϖ (wkc-cong ϖ') θ
  lcount-wkce-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wk-wk π) (wkc-cong ϖ) (wkc-cons ϖ') (wkce-wc- π₁ ϖ₁ ϖ'' e θ) = lcount-wkce-lemma (t i) E (x₁ ∷ E') π ϖ (wkc-cons ϖ') θ
  lcount-wkce-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wk-wk π) (wkc-cons ϖ) (wkc-cong ϖ') (wkce-ww- π₁ ϖ₁ ϖ'' θ) = lcount-wkce-lemma (t i) (x ∷ E) (x₁ ∷ E') π ϖ (wkc-cong ϖ') θ
  lcount-wkce-lemma (Cx.t i) (x ∷ E) (x₁ ∷ E') (wk-wk π) (wkc-cons ϖ) (wkc-cons ϖ') (wkce-ww- π₁ ϖ₁ ϖ'' θ) = lcount-wkce-lemma (t i) (x ∷ E) (x₁ ∷ E') π ϖ (wkc-cons ϖ') θ


  mutual

    {-
    val-cnt-lemma : (M : Val Γ X) → (E E' : List ℕ) → (ϖ : WkC Γ E) → (ϖ' : WkC Γ E') → (ϕ : WkCZ ϖ ϖ')
                → (vcount M E ϖ) ≡ (vcount M E' ϖ')
    val-cnt-lemma (var Cx.h) [] [] ϖ ϖ' (wkcz-wk ϕ) = refl
    val-cnt-lemma (var Cx.h) [] (x ∷ E') ϖ ϖ' (wkcz-wk ϕ) = refl
    val-cnt-lemma (var Cx.h) (x ∷ E) [] ϖ ϖ' (wkcz-wk ϕ) = refl
    val-cnt-lemma (var Cx.h) (x ∷ E) (x₁ ∷ E') ϖ ϖ' (wkcz-cong ϕ) = refl
    val-cnt-lemma (var Cx.h) (x ∷ E) (x₁ ∷ E') ϖ ϖ' (wkcz-wk ϕ) = refl
    val-cnt-lemma (var (Cx.t i)) [] [] ϖ ϖ' (wkcz-wk ϕ) = refl
    val-cnt-lemma (var (Cx.t i)) [] (x ∷ E') ϖ ϖ' (wkcz-wk ϕ) = ql (wkcz-l ϕ)
                                                                 (vcount (var (t {B = R₀} i)) [] (wkc-cons (ql (wkcz-l ϕ) (WkC _ []))) ≡
                                                                  vcount (var (t {B = R₀} i)) (x ∷ E') (wkc-cons _))
    val-cnt-lemma (var (Cx.t i)) (x ∷ E) [] ϖ ϖ' (wkcz-wk ϕ) = ql (wkcz-r ϕ)
                                                                (vcount (var (t {B = R₀} i)) (x ∷ E) (wkc-cons _) ≡
                                                                 vcount (var (t {B = R₀} i)) [] (wkc-cons (ql (wkcz-r ϕ) (WkC _ []))))
    val-cnt-lemma (var (Cx.t i)) (x ∷ E) (x₁ ∷ E') (wkc-cong ϖ) (wkc-cong ϖ') (wkcz-cong ϕ) = val-cnt-lemma (var i) E E' ϖ ϖ' ϕ
    val-cnt-lemma (var (Cx.t i)) (x ∷ E) (x₁ ∷ E') (wkc-cons ϖ) (wkc-cons ϖ') (wkcz-wk ϕ) = val-cnt-lemma (var i) (x ∷ E) (x₁ ∷ E') ϖ ϖ' ϕ
    val-cnt-lemma (lam W) E E' ϖ ϖ' ϕ = comp-cnt-lemma W E E' (wkc-cons ϖ) (wkc-cons ϖ') (wkcz-wk ϕ)
    val-cnt-lemma (pair M₁ M₂) E E' ϖ ϖ' ϕ = cong₂ _+_ (val-cnt-lemma M₁ E E' ϖ ϖ' ϕ) (val-cnt-lemma M₂ E E' ϖ ϖ' ϕ)
    val-cnt-lemma (pm M N) E E' ϖ ϖ' ϕ rewrite val-cnt-lemma M E E' ϖ ϖ' ϕ = val-cnt-lemma N (vcount M E' ϖ' ∷ vcount M E' ϖ' ∷ E) (vcount M E' ϖ' ∷ vcount M E' ϖ' ∷ E') (wkc-cong (wkc-cong ϖ)) (wkc-cong (wkc-cong ϖ')) (wkcz-cong (wkcz-cong ϕ))
    val-cnt-lemma unit E E' ϖ ϖ' ϕ = refl
    -}

    val-cnt-lemma : (M : Val Γ X) → (E E' : List ℕ) → (ϖ : WkC Γ E) → (ϖ' : WkC Γ E') → (ϕ : WkCZ ϖ ϖ')
                → (vcount M E ϖ) ≤ (vcount M E' ϖ')
    val-cnt-lemma (var Cx.h) [] [] ϖ ϖ' (wkcz-wk ϕ) = s≤s z≤n --refl
    val-cnt-lemma (var Cx.h) [] (x ∷ E') ϖ ϖ' (wkcz-wk ϕ) = s≤s z≤n --refl
    val-cnt-lemma (var Cx.h) (x ∷ E) [] ϖ ϖ' (wkcz-wk ϕ) = s≤s z≤n -- refl
    val-cnt-lemma (var Cx.h) (x ∷ E) (x₁ ∷ E') ϖ ϖ' (wkcz-cong cnt₁≤cnt₂ ϕ) = cnt₁≤cnt₂ --refl
    val-cnt-lemma (var Cx.h) (x ∷ E) (x₁ ∷ E') ϖ ϖ' (wkcz-wk ϕ) = s≤s z≤n --refl
    val-cnt-lemma (var (Cx.t i)) [] [] ϖ ϖ' (wkcz-wk ϕ) = s≤s z≤n --refl
    val-cnt-lemma (var (Cx.t i)) [] (x ∷ E') ϖ ϖ' (wkcz-wk ϕ) = ql (wkcz-l ϕ) (vcount (var (t {B = R₀} i)) [] (wkc-cons (ql (wkcz-l ϕ) (WkC _ []))) ≤ vcount (var (t {B = R₀} i)) (x ∷ E') (wkc-cons _))
      --ql (wkcz-l ϕ) (vcount (var (t {B = R₀} i)) [] (wkc-cons (ql (wkcz-l ϕ) (WkC _ []))) ≡ vcount (var (t {B = R₀} i)) (x ∷ E') (wkc-cons _))
    val-cnt-lemma (var (Cx.t i)) (x ∷ E) [] ϖ ϖ' (wkcz-wk ϕ) = ql (wkcz-r ϕ) (vcount (var (t {B = R₀} i)) (x ∷ E) (wkc-cons _) ≤ vcount (var (t {B = R₀} i)) [] (wkc-cons (ql (wkcz-r ϕ) (WkC _ []))))
      --ql (wkcz-r ϕ) (vcount (var (t {B = R₀} i)) (x ∷ E) (wkc-cons _) ≡ vcount (var (t {B = R₀} i)) [] (wkc-cons (ql (wkcz-r ϕ) (WkC _ []))))
    val-cnt-lemma (var (Cx.t i)) (x ∷ E) (x₁ ∷ E') (wkc-cong ϖ) (wkc-cong ϖ') (wkcz-cong _ ϕ) = val-cnt-lemma (var i) E E' ϖ ϖ' ϕ
    val-cnt-lemma (var (Cx.t i)) (x ∷ E) (x₁ ∷ E') (wkc-cons ϖ) (wkc-cons ϖ') (wkcz-wk ϕ) = val-cnt-lemma (var i) (x ∷ E) (x₁ ∷ E') ϖ ϖ' ϕ
    val-cnt-lemma (lam W) E E' ϖ ϖ' ϕ = comp-cnt-lemma W E E' (wkc-cons ϖ) (wkc-cons ϖ') (wkcz-wk ϕ)
    val-cnt-lemma (pair M₁ M₂) E E' ϖ ϖ' ϕ = +-≤-cong (val-cnt-lemma M₁ E E' ϖ ϖ' ϕ) (val-cnt-lemma M₂ E E' ϖ ϖ' ϕ) --cong₂ _+_ (val-cnt-lemma M₁ E E' ϖ ϖ' ϕ) (val-cnt-lemma M₂ E E' ϖ ϖ' ϕ)
    val-cnt-lemma (pm M N) E E' ϖ ϖ' ϕ =
      let
        a0 = val-cnt-lemma M E E' ϖ ϖ' ϕ
      in
      val-cnt-lemma N (vcount M E ϖ ∷ vcount M E ϖ ∷ E) (vcount M E' ϖ' ∷ vcount M E' ϖ' ∷ E') (wkc-cong (wkc-cong ϖ)) (wkc-cong (wkc-cong ϖ')) (wkcz-cong a0 (wkcz-cong a0 ϕ))
    val-cnt-lemma unit E E' ϖ ϖ' ϕ = z≤n --refl

    {-
    comp-cnt-lemma : (W : Comp Γ X) → (E E' : List ℕ) → (ϖ : WkC Γ E) → (ϖ' : WkC Γ E') → (ϕ : WkCZ ϖ ϖ')
                → (ccount W E ϖ) ≡ (ccount W E' ϖ')
    comp-cnt-lemma (return M) E E' ϖ ϖ' ϕ = val-cnt-lemma M E E' ϖ ϖ' ϕ
    comp-cnt-lemma (pm M W) E E' ϖ ϖ' ϕ rewrite val-cnt-lemma M E E' ϖ ϖ' ϕ = comp-cnt-lemma W (vcount M E' ϖ' ∷ vcount M E' ϖ' ∷ E) (vcount M E' ϖ' ∷ vcount M E' ϖ' ∷ E') (wkc-cong (wkc-cong ϖ)) (wkc-cong (wkc-cong ϖ')) (wkcz-cong (wkcz-cong ϕ))
    comp-cnt-lemma (push W₁ W₂) E E' ϖ ϖ' ϕ rewrite comp-cnt-lemma W₁ E E' ϖ ϖ' ϕ = comp-cnt-lemma W₂ (ccount W₁ E' ϖ' ∷ E) (ccount W₁ E' ϖ' ∷ E') (wkc-cong ϖ) (wkc-cong ϖ') (wkcz-cong ϕ)
    comp-cnt-lemma (app M N) E E' ϖ ϖ' ϕ =
      let
        a0 = val-cnt-lemma M E E' ϖ ϖ' ϕ
        a1 = val-cnt-lemma N E E' ϖ ϖ' ϕ
      in
      cong suc (cong₂ _+_ a1 (cong₂ _*_ a0 (cong suc a1)))
    comp-cnt-lemma (var M) E E' ϖ ϖ' ϕ = val-cnt-lemma M E E' ϖ ϖ' ϕ
    comp-cnt-lemma (sub W₁ W₂) E E' ϖ ϖ' ϕ rewrite comp-cnt-lemma W₂ E E' ϖ ϖ' ϕ = comp-cnt-lemma W₁ (ccount W₂ E' ϖ' ∷ E) (ccount W₂ E' ϖ' ∷ E') (wkc-cong ϖ) (wkc-cong ϖ') (wkcz-cong ϕ)
    -}

    comp-cnt-lemma : (W : Comp Γ X) → (E E' : List ℕ) → (ϖ : WkC Γ E) → (ϖ' : WkC Γ E') → (ϕ : WkCZ ϖ ϖ')
                → (ccount W E ϖ) ≤ (ccount W E' ϖ')
    comp-cnt-lemma (return M) E E' ϖ ϖ' ϕ = val-cnt-lemma M E E' ϖ ϖ' ϕ
    comp-cnt-lemma (pm M W) E E' ϖ ϖ' ϕ =
      let
        a0 = val-cnt-lemma M E E' ϖ ϖ' ϕ
      in
      comp-cnt-lemma W (vcount M E ϖ ∷ vcount M E ϖ ∷ E) (vcount M E' ϖ' ∷ vcount M E' ϖ' ∷ E') (wkc-cong (wkc-cong ϖ)) (wkc-cong (wkc-cong ϖ')) (wkcz-cong a0 (wkcz-cong a0 ϕ)) --rewrite val-cnt-lemma M E E' ϖ ϖ' ϕ = comp-cnt-lemma W (vcount M E' ϖ' ∷ vcount M E' ϖ' ∷ E) (vcount M E' ϖ' ∷ vcount M E' ϖ' ∷ E') (wkc-cong (wkc-cong ϖ)) (wkc-cong (wkc-cong ϖ')) (wkcz-cong (wkcz-cong ϕ))
    comp-cnt-lemma (push W₁ W₂) E E' ϖ ϖ' ϕ =
      let
        a0 = comp-cnt-lemma W₁ E E' ϖ ϖ' ϕ
      in
      comp-cnt-lemma W₂ (ccount W₁ E ϖ ∷ E) (ccount W₁ E' ϖ' ∷ E') (wkc-cong ϖ) (wkc-cong ϖ') (wkcz-cong a0 ϕ) --rewrite comp-cnt-lemma W₁ E E' ϖ ϖ' ϕ = comp-cnt-lemma W₂ (ccount W₁ E' ϖ' ∷ E) (ccount W₁ E' ϖ' ∷ E') (wkc-cong ϖ) (wkc-cong ϖ') (wkcz-cong ϕ)
    comp-cnt-lemma (app M N) E E' ϖ ϖ' ϕ =
      let
        a0 = val-cnt-lemma M E E' ϖ ϖ' ϕ
        a1 = val-cnt-lemma N E E' ϖ ϖ' ϕ
      in
      s≤s (+-≤-cong a1 (*-≤-cong a0 (s≤s a1))) --cong suc (cong₂ _+_ a1 (cong₂ _*_ a0 (cong suc a1)))
    comp-cnt-lemma (var M) E E' ϖ ϖ' ϕ = val-cnt-lemma M E E' ϖ ϖ' ϕ
    comp-cnt-lemma (sub W₁ W₂) E E' ϖ ϖ' ϕ =
      let
        a0 = comp-cnt-lemma W₂ E E' ϖ ϖ' ϕ
      in
      comp-cnt-lemma W₁ (ccount W₂ E ϖ ∷ E) (ccount W₂ E' ϖ' ∷ E') (wkc-cong ϖ) (wkc-cong ϖ') (wkcz-cong a0 ϕ) --rewrite comp-cnt-lemma W₂ E E' ϖ ϖ' ϕ = comp-cnt-lemma W₁ (ccount W₂ E' ϖ' ∷ E) (ccount W₂ E' ϖ' ∷ E') (wkc-cong ϖ) (wkc-cong ϖ') (wkcz-cong ϕ)


  val-vcount-lemma :   (M : Val Γ X) → (E E' : EMetric) → (ϖ : WkN Γ E) → (ϖ' : WkN Γ E') → (ϕ : WkCZ (wkn-to-wkc ϖ) (wkn-to-wkc ϖ'))
                    → (vcount M (elist-to-clist E) (wkn-to-wkc ϖ)) ≤ (vcount M (elist-to-clist E') (wkn-to-wkc ϖ'))
  val-vcount-lemma M E E' ϖ ϖ' ϕ = val-cnt-lemma M (elist-to-clist E) (elist-to-clist E') (wkn-to-wkc ϖ) (wkn-to-wkc ϖ') ϕ


  mutual

    val-mono-metric : (M : Val Γ Y) → (E : EMetric) → WkN Γ E → EElem Y
    val-mono-metric (var i) E ϖ =
      let
        IH = lookup-mono-metric i E ϖ
        cnt = vcount (var i) (elist-to-clist E) (wkn-to-wkc ϖ)
      in
      cnt , (λ csn → incr 2 ((proj₁ $ proj₂ IH) csn)) , λ c≤c' → ≤ᴹ-incr-cong (≤-refl {n = 2}) ((proj₂ $ proj₂ IH) c≤c')
    val-mono-metric (lam W) E ϖ =
      let
        IH2 = comp-mono-metric W E (wkn-cons ϖ)
        cnt = vcount (lam W) (elist-to-clist E) (wkn-to-wkc ϖ)
      in
      cnt , ((λ csn → incr 2 (m-⇒ 0 ((proj₁ $ proj₂ IH2) csn)))) ,
      λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → (≤-⇒ (s≤s (s≤s z≤n)) ((proj₂ $ proj₂ IH2) c≤c'))
    val-mono-metric (pair M₁ M₂) E ϖ =
      let
        cnt = vcount (pair M₁ M₂) (elist-to-clist E) (wkn-to-wkc ϖ)
        IH1 = val-mono-metric M₁ E ϖ
        IH2 = val-mono-metric M₂ E ϖ
      in
      cnt , ((λ csn → incr 2 (m-× 0 ((proj₁ $ proj₂ IH1) csn) ((proj₁ $ proj₂ IH2) csn)))) , λ c≤c' → ≤-× ≤-refl ((proj₂ $ proj₂ IH1) c≤c') ((proj₂ $ proj₂ IH2) c≤c')
    val-mono-metric (pm {A = X} {B = Y} M N) E ϖ =
      let
        cnt = vcount (pm {A = X} {B = Y} M N) (elist-to-clist E) (wkn-to-wkc ϖ)
        IH1 = val-mono-metric M E ϖ
        IH2 = val-mono-metric N E (wkn-cons (wkn-cons ϖ))
        r1 = λ c → rhs ((proj₁ $ proj₂ IH1) c)
        l1 = λ c → lhs ((proj₁ $ proj₂ IH1) c)
        IH3 = val-mono-metric N ((Y , proj₁ IH1 , r1 , λ c≤c' → ≤ᴹ-rhs ((proj₂ $ proj₂ IH1) c≤c')) ∷ (X , proj₁ IH1 , l1 , λ c≤c' → ≤ᴹ-lhs ((proj₂ $ proj₂ IH1) c≤c')) ∷ E) (wkn-cong (wkn-cong ϖ))
      in
      cnt ,
      ((λ csn → incr (suc (vx ((proj₁ $ proj₂ IH1) csn) + ⟪ (proj₁ $ proj₂ IH2) csn ⟫)) ((proj₁ $ proj₂ IH3) csn))) ,
      λ c≤c' → ≤ᴹ-incr-cong (+-≤-cong (s≤s (≤ᴹ-vx ((proj₂ $ proj₂ IH1) c≤c'))) (≤ᴹ⇒≤ ((proj₂ $ proj₂ IH2) c≤c'))) ((proj₂ $ proj₂ IH3) c≤c')
    val-mono-metric unit E ϖ =
      vcount unit (elist-to-clist E) (wkn-to-wkc ϖ) ,
      (λ _ → m-Unit 2) ,
      λ {csn₁} {csn₂} z → ≤-Unit (s≤s (s≤s z≤n)) --(λ _ → m-Unit 2) , (λ {csn₁} {csn₂} z → ≤-Unit (s≤s (s≤s z≤n)))

    comp-mono-metric : (W : Comp Γ Y) → (E : EMetric) → WkN Γ E → EElem Y
    comp-mono-metric (return M) E ϖ =
      let
        cnt = ccount (return M) (elist-to-clist E) (wkn-to-wkc ϖ)
        IH = val-mono-metric M E ϖ
      in
      cnt , (λ csn → incr 2 ((proj₁ $ proj₂ IH) csn)) , λ c≤c' → ≤ᴹ-incr-cong (≤-refl {n = 2}) ((proj₂ $ proj₂ IH) c≤c')
    comp-mono-metric (pm {A = X} {B = Y} M W) E ϖ = --{!!}
      let
        cnt = ccount (pm {A = X} {B = Y} M W) (elist-to-clist E) (wkn-to-wkc ϖ)
        IH1 = val-mono-metric M E ϖ
        IH2 = comp-mono-metric W E (wkn-cons (wkn-cons ϖ))
        r1 = λ c → rhs ((proj₁ $ proj₂ IH1) c)
        l1 = λ c → lhs ((proj₁ $ proj₂ IH1) c)
        IH3 = comp-mono-metric W ((Y , proj₁ IH1 , r1 , λ c≤c' → ≤ᴹ-rhs ((proj₂ $ proj₂ IH1) c≤c')) ∷ (X , proj₁ IH1 , l1 , λ c≤c' → ≤ᴹ-lhs ((proj₂ $ proj₂ IH1) c≤c')) ∷ E) (wkn-cong (wkn-cong ϖ))
      in
      cnt ,
      ((λ csn → incr (suc (vx ((proj₁ $ proj₂ IH1) csn) + ⟪ (proj₁ $ proj₂ IH2) csn ⟫)) ((proj₁ $ proj₂ IH3) csn))) ,
      λ c≤c' → ≤ᴹ-incr-cong (+-≤-cong (s≤s (≤ᴹ-vx ((proj₂ $ proj₂ IH1) c≤c'))) (≤ᴹ⇒≤ ((proj₂ $ proj₂ IH2) c≤c'))) ((proj₂ $ proj₂ IH3) c≤c')
    comp-mono-metric (push {A = X} W₁ W₂) E ϖ =
      let
        cnt = ccount (push {A = X} W₁ W₂) (elist-to-clist E) (wkn-to-wkc ϖ)
        IH1 = comp-mono-metric W₂ E (wkn-cons ϖ)
        cnt2 = ccount W₂ (elist-to-clist E) (wkn-to-wkc (wkn-cons ϖ))
        IH3 = comp-mono-metric W₁ E ϖ
        cs' = λ csn → ((cnt2 , ⟪ (proj₁ $ proj₂ IH1) csn ⟫) ∷ csn)
        IH3' = λ csn → ⟪ (proj₁ $ proj₂ IH3) (cs' csn) ⟫
      in
      cnt ,
      (λ csn → incr (suc ((2+ cnt2) * (IH3' csn))) ((proj₁ $ proj₂ IH1) csn)) ,
      λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' →
        let
          le = proj₂ (proj₂ IH1) c≤c'
          le1 : ⟪ proj₂ IH3 .proj₁ ((cnt2 , ⟪ proj₂ IH1 .proj₁ csn₁ ⟫) ∷ csn₁) ⟫ ≤ ⟪ proj₂ IH3 .proj₁ ((cnt2 , ⟪ proj₂ IH1 .proj₁ csn₂ ⟫) ∷ csn₂) ⟫
          -- FST: le1 = ≤ᴹ⇒≤ ((proj₂ $ proj₂ IH3) ([s≤s] {cnt = cnt2} ((≤ᴹ⇒≤ le)) c≤c'))
          le1 = ≤ᴹ⇒≤ ((proj₂ $ proj₂ IH3) ([s≤s] (≤-refl {n = cnt2}) ((≤ᴹ⇒≤ le)) c≤c'))
          le2 = s≤s (*-≤-cong (≤-refl {n = (2+ cnt2)}) le1)
        in
        ≤ᴹ-incr-cong le2 le
    comp-mono-metric (app M N) E ϖ = --{!!}
      let
        cnt = ccount (app M N) (elist-to-clist E) (wkn-to-wkc ϖ)
        IH1 = val-mono-metric M E ϖ
        IH2 = val-mono-metric N E ϖ
      in
      cnt ,
      (λ csn → incr (2 + ((p1 (proj₁ (proj₂ IH1) csn)) + ((suc $ proj₁ IH1) * ⟪ proj₁ (proj₂ IH2) csn ⟫))) (pw (proj₁ (proj₂ IH1) csn))) ,
      λ c≤c' →
        let
          le1 = +-≤-cong (≤ᴹ-p1 (proj₂ (proj₂ IH1) c≤c')) (*-≤-cong (≤-refl {n = suc $ proj₁ IH1}) (≤ᴹ⇒≤ (proj₂ (proj₂ IH2) c≤c')))
        in
        ≤ᴹ-incr-cong (s≤s (s≤s le1)) (≤ᴹ-pw (proj₂ (proj₂ IH1) c≤c'))
    comp-mono-metric (var {A = A} M) E ϖ =
      let
        cnt = ccount (var {A = A} M) (elist-to-clist E) (wkn-to-wkc ϖ)
        IH = val-mono-metric M E ϖ
      in
      cnt , (λ csn → incr (suc ⟪ (proj₁ $ proj₂ IH) csn ⟫) zero-metric) , λ c≤c' → ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ ((proj₂ $ proj₂ IH) c≤c'))) (≤ᴹ-refl {nm = zero-metric})
    comp-mono-metric (sub {Γ = Γ} W₁ W₂) E ϖ =
      let
        cnt = ccount (sub {Γ = Γ} W₁ W₂) (elist-to-clist E) (wkn-to-wkc ϖ)
        cnt2 = ccount W₂ (elist-to-clist E) (wkn-to-wkc ϖ)
        IH = comp-mono-metric W₂ E ϖ
      in
      cnt ,
      ((λ csn → incr (suc ⟪ proj₁ (proj₂ IH) csn ⟫) (proj₁ (proj₂ (comp-mono-metric W₁ ((`V , cnt2 , (λ _ → m-V 0 (⟪ proj₁ (proj₂ IH) csn ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ IH) csn ⟫ csn)) , λ c≤c' → ≤ᴹ-refl) ∷ E) (wkn-cong ϖ))) csn))) ,
      λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' →
        let
          le : csn-to-nat₀ ⟪ proj₁ (proj₂ IH) csn₁ ⟫ csn₁ ≤ csn-to-nat₀ ⟪ proj₁ (proj₂ IH) csn₂ ⟫ csn₂
          le = ≤ᶜˢⁿ-decr (≤ᴹ⇒≤ (proj₂ (proj₂ IH) c≤c')) c≤c'
          le1 : (m-V 0 (⟪ proj₁ (proj₂ IH) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ IH) csn₁ ⟫ csn₁)) ≤ᴹ (m-V 0 (⟪ proj₁ (proj₂ IH) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ IH) csn₂ ⟫ csn₂))
          le1 = ≤-V z≤n (+-≤-cong (≤ᴹ⇒≤ (proj₂ (proj₂ IH) c≤c')) le)
          ϖ₁ : WkN (Γ ∙ `V) ((`V , cnt2 , (λ _ → m-V 0 (⟪ proj₁ (proj₂ IH) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ IH) csn₁ ⟫ csn₁)) , λ c≤c' → ≤ᴹ-refl) ∷ E)
          ϖ₁ = wkn-cong ϖ
          ϖ₂ : WkN (Γ ∙ `V) ((`V , cnt2 , (λ _ → m-V 0 (⟪ proj₁ (proj₂ IH) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ IH) csn₂ ⟫ csn₂)) , λ c≤c' → ≤ᴹ-refl) ∷ E)
          ϖ₂ = wkn-cong ϖ
          ϕ : WkZ ϖ₁ ϖ₂
          ϕ = wkz-cong ≤-refl (λ csn → le1) wkz-id
          a0 = comp-wkz-lemma W₁ _ _ ϖ₁ ϖ₂ ϕ csn₁
          a1 = proj₂ (proj₂ (comp-mono-metric W₁ ((`V , cnt2 , (λ _ → m-V 0 (⟪ proj₁ (proj₂ IH) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ IH) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E) (wkn-cong ϖ))) c≤c'
          a2 = proj₂ (proj₂ IH) c≤c'
        in
        ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ a2)) (≤ᴹ-trans a0 a1)

    val-proj₁-lemma :   (M : Val Γ X) → (E E' : EMetric) → (ϖ : WkN Γ E) → (ϖ' : WkN Γ E') → (ϕ : WkCZ (wkn-to-wkc ϖ) (wkn-to-wkc ϖ'))
                      → (proj₁ (val-mono-metric M E ϖ)) ≤ (proj₁ (val-mono-metric M E' ϖ'))
    val-proj₁-lemma (var i) E E' ϖ ϖ' ϕ = val-vcount-lemma (var i) E E' ϖ ϖ' ϕ
    val-proj₁-lemma (lam W) E E' ϖ ϖ' ϕ = val-vcount-lemma (lam W) E E' ϖ ϖ' ϕ
    val-proj₁-lemma (pair M₁ M₂) E E' ϖ ϖ' ϕ = val-vcount-lemma (pair M₁ M₂) E E' ϖ ϖ' ϕ
    val-proj₁-lemma (pm M N) E E' ϖ ϖ' ϕ = val-vcount-lemma (pm M N) E E' ϖ ϖ' ϕ
    val-proj₁-lemma unit E E' ϖ ϖ' ϕ = val-vcount-lemma unit E E' ϖ ϖ' ϕ


    val-wkz-lemma : (M : Val Γ X) → (E E' : EMetric) → (ϖ : WkN Γ E) → (ϖ' : WkN Γ E') → (ϕ : WkZ ϖ ϖ')
                → (csn : List (ℕ × ℕ)) → (proj₁ (proj₂ (val-mono-metric M E ϖ))) csn ≤ᴹ (proj₁ (proj₂ (val-mono-metric M E' ϖ'))) csn
    val-wkz-lemma (var i) E E' ϖ ϖ' ϕ csn = ≤ᴹ-incr-cong (≤-refl {n = 2}) (lookup-wkz-lemma i E E' ϖ ϖ' ϕ csn)
    val-wkz-lemma (lam W) E E' ϖ ϖ' ϕ csn = ≤-⇒ (s≤s (s≤s z≤n)) (comp-wkz-lemma W E E' (wkn-cons ϖ) (wkn-cons ϖ') (wkz-wk ϕ) csn)
    val-wkz-lemma (pair M₁ M₂) E E' ϖ ϖ' ϕ csn = ≤-× (s≤s (s≤s z≤n)) (val-wkz-lemma M₁ E E' ϖ ϖ' ϕ csn) (val-wkz-lemma M₂ E E' ϖ ϖ' ϕ csn)
    val-wkz-lemma (pm {Γ = Γ} {A = A} {B = B} M N) E E' ϖ ϖ' ϕ csn =
          let
            a0 c = val-wkz-lemma M E E' ϖ ϖ' ϕ c
            avx c = ≤ᴹ-vx (a0 c)
            al c = ≤ᴹ-lhs (a0 c)
            ar c = ≤ᴹ-rhs (a0 c)
            E₁ = (B , proj₁ (val-mono-metric M E ϖ) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric M E ϖ)) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric M E ϖ)) c≤c'))) ∷ (A , proj₁ (val-mono-metric M E ϖ) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric M E ϖ)) c)) , λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric M E ϖ)) c≤c')) ∷ E
            E₂ = ((B , proj₁ (val-mono-metric M E ϖ) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric M E' ϖ')) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric M E' ϖ')) c≤c'))) ∷ (A , proj₁ (val-mono-metric M E ϖ) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric M E' ϖ')) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric M E' ϖ')) c≤c'))) ∷ E')
            E₂' = ((B , proj₁ (val-mono-metric M E' ϖ') , (λ c → rhs (proj₁ (proj₂ (val-mono-metric M E' ϖ')) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric M E' ϖ')) c≤c'))) ∷ (A , proj₁ (val-mono-metric M E' ϖ') , (λ c → lhs (proj₁ (proj₂ (val-mono-metric M E' ϖ')) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric M E' ϖ')) c≤c'))) ∷ E')
            ϖ₁ : WkN (Γ ∙ A ∙ B) E₁
            ϖ₁ = wkn-cong (wkn-cong ϖ)
            ϖ₂ : WkN (Γ ∙ A ∙ B) E₂
            ϖ₂ = wkn-cong (wkn-cong ϖ')
            ϖ₂' : WkN (Γ ∙ A ∙ B) E₂'
            ϖ₂' = wkn-cong (wkn-cong ϖ')
            λE₂ = λ x → ((B , x , (λ c → rhs (proj₁ (proj₂ (val-mono-metric M E' ϖ')) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric M E' ϖ')) c≤c'))) ∷ (A , x , (λ c → lhs (proj₁ (proj₂ (val-mono-metric M E' ϖ')) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric M E' ϖ')) c≤c'))) ∷ E')
            ineq1 = val-proj₁-lemma M E E' ϖ ϖ' (wkz-to-wkcz ϕ)
            b0 = val-wkz-lemma N E E' (wkn-cons (wkn-cons ϖ)) (wkn-cons (wkn-cons ϖ')) (wkz-wk (wkz-wk ϕ)) csn
            --b1 = val-wkz-lemma N E₁ E₂ (wkn-cong (wkn-cong ϖ)) (wkn-cong (wkn-cong ϖ')) ((wkz-cong {!!} ar (wkz-cong {!!} al ϕ))) csn
            b2 = val-wkz-lemma N E₁ E₂' (wkn-cong (wkn-cong ϖ)) (wkn-cong (wkn-cong ϖ')) ((wkz-cong ineq1 ar (wkz-cong ineq1 al ϕ))) csn
            -- b2 : proj₁ (proj₂ (val-mono-metric N E₁ ϖ₁)) csn ≤ᴹ proj₁ (proj₂ (val-mono-metric N E₂' ϖ₂')) csn
            -- b2 = subst (λ x → proj₁ (proj₂ (val-mono-metric N ((B , proj₁ (val-mono-metric M E ϖ) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric M E ϖ)) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric M E ϖ)) c≤c'))) ∷ (A , proj₁ (val-mono-metric M E ϖ) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric M E ϖ)) c)) , λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric M E ϖ)) c≤c')) ∷ E) ϖ₁)) csn ≤ᴹ proj₁ (proj₂ (val-mono-metric N ((B , x , (λ c → rhs (proj₁ (proj₂ (val-mono-metric M E' ϖ')) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric M E' ϖ')) c≤c'))) ∷ (A , x , (λ c → lhs (proj₁ (proj₂ (val-mono-metric M E' ϖ')) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric M E' ϖ')) c≤c'))) ∷ E') (wkn-cong (wkn-cong ϖ')))) csn) eq1 b1
          in
          ≤ᴹ-incr-cong (+-≤-cong (s≤s (avx csn)) (≤ᴹ⇒≤ b0)) b2 -- ≤ᴹ-incr-cong (+-≤-cong (s≤s (avx csn)) (≤ᴹ⇒≤ b0)) b2
    val-wkz-lemma unit E E' ϖ ϖ' ϕ csn = ≤-Unit (s≤s (s≤s z≤n))

    comp-wkz-lemma : (W : Comp Γ X) → (E E' : EMetric) → (ϖ : WkN Γ E) → (ϖ' : WkN Γ E') → (ϕ : WkZ ϖ ϖ')
                → (csn : List (ℕ × ℕ)) → (proj₁ (proj₂ (comp-mono-metric W E ϖ))) csn ≤ᴹ (proj₁ (proj₂ (comp-mono-metric W E' ϖ'))) csn
    comp-wkz-lemma (return M) E E' ϖ ϖ' ϕ csn = ≤ᴹ-incr-cong (≤-refl {n = 2}) (val-wkz-lemma M E E' ϖ ϖ' ϕ csn)
    comp-wkz-lemma (pm {Γ = Γ} {A = A} {B = B} M W) E E' ϖ ϖ' ϕ csn =
          let
            a0 c = val-wkz-lemma M E E' ϖ ϖ' ϕ c
            avx c = ≤ᴹ-vx (a0 c)
            al c = ≤ᴹ-lhs (a0 c)
            ar c = ≤ᴹ-rhs (a0 c)
            E₁ = (B , proj₁ (val-mono-metric M E ϖ) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric M E ϖ)) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric M E ϖ)) c≤c'))) ∷ (A , proj₁ (val-mono-metric M E ϖ) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric M E ϖ)) c)) , λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric M E ϖ)) c≤c')) ∷ E
            E₂ = ((B , proj₁ (val-mono-metric M E ϖ) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric M E' ϖ')) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric M E' ϖ')) c≤c'))) ∷ (A , proj₁ (val-mono-metric M E ϖ) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric M E' ϖ')) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric M E' ϖ')) c≤c'))) ∷ E')
            E₂' = ((B , proj₁ (val-mono-metric M E' ϖ') , (λ c → rhs (proj₁ (proj₂ (val-mono-metric M E' ϖ')) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric M E' ϖ')) c≤c'))) ∷ (A , proj₁ (val-mono-metric M E' ϖ') , (λ c → lhs (proj₁ (proj₂ (val-mono-metric M E' ϖ')) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric M E' ϖ')) c≤c'))) ∷ E')
            ϖ₁ : WkN (Γ ∙ A ∙ B) E₁
            ϖ₁ = wkn-cong (wkn-cong ϖ)
            ϖ₂ : WkN (Γ ∙ A ∙ B) E₂
            ϖ₂ = wkn-cong (wkn-cong ϖ')
            ϖ₂' : WkN (Γ ∙ A ∙ B) E₂'
            ϖ₂' = wkn-cong (wkn-cong ϖ')
            λE₂ = λ x → ((B , x , (λ c → rhs (proj₁ (proj₂ (val-mono-metric M E' ϖ')) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric M E' ϖ')) c≤c'))) ∷ (A , x , (λ c → lhs (proj₁ (proj₂ (val-mono-metric M E' ϖ')) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric M E' ϖ')) c≤c'))) ∷ E')
            ineq1 = val-proj₁-lemma M E E' ϖ ϖ' (wkz-to-wkcz ϕ)
            b0 = comp-wkz-lemma W E E' (wkn-cons (wkn-cons ϖ)) (wkn-cons (wkn-cons ϖ')) (wkz-wk (wkz-wk ϕ)) csn
            b2 = comp-wkz-lemma W E₁ E₂' (wkn-cong (wkn-cong ϖ)) (wkn-cong (wkn-cong ϖ')) ((wkz-cong ineq1 ar (wkz-cong ineq1 al ϕ))) csn
            -- b2 : proj₁ (proj₂ (comp-mono-metric W E₁ ϖ₁)) csn ≤ᴹ proj₁ (proj₂ (comp-mono-metric W E₂' ϖ₂')) csn
            -- b2 = subst (λ x → proj₁ (proj₂ (comp-mono-metric W ((B , proj₁ (val-mono-metric M E ϖ) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric M E ϖ)) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric M E ϖ)) c≤c'))) ∷ (A , proj₁ (val-mono-metric M E ϖ) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric M E ϖ)) c)) , λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric M E ϖ)) c≤c')) ∷ E) ϖ₁)) csn ≤ᴹ proj₁ (proj₂ (comp-mono-metric W ((B , x , (λ c → rhs (proj₁ (proj₂ (val-mono-metric M E' ϖ')) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric M E' ϖ')) c≤c'))) ∷ (A , x , (λ c → lhs (proj₁ (proj₂ (val-mono-metric M E' ϖ')) c)) , (λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric M E' ϖ')) c≤c'))) ∷ E') (wkn-cong (wkn-cong ϖ')))) csn) eq1 b1
          in
          ≤ᴹ-incr-cong (+-≤-cong (s≤s (avx csn)) (≤ᴹ⇒≤ b0)) b2 -- ≤ᴹ-incr-cong (+-≤-cong (s≤s (avx csn)) (≤ᴹ⇒≤ b0)) b2
    comp-wkz-lemma (push W₁ W₂) E E' ϖ ϖ' ϕ csn = -- {!!} --rewrite comp-cnt-lemma W₂ (elist-to-clist E) (elist-to-clist E') (wkn-to-wkc (wkn-cons ϖ)) (wkn-to-wkc (wkn-cons ϖ')) (wkz-to-wkcz (wkz-wk ϕ)) =
      let
        d0 = comp-cnt-lemma W₂ (elist-to-clist E) (elist-to-clist E') (wkn-to-wkc (wkn-cons ϖ)) (wkn-to-wkc (wkn-cons ϖ')) (wkz-to-wkcz (wkz-wk ϕ))
        a0 = comp-wkz-lemma W₁ E E' ϖ ϖ' ϕ
        a1 = comp-wkz-lemma W₂ E E' (wkn-cons ϖ) (wkn-cons ϖ') (wkz-wk ϕ)
        --c≤c' : ((ccount W₂ (elist-to-clist E') (wkn-to-wkc (wkn-cons ϖ')) , ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn ⟫) ∷ csn) ≤ᶜˢⁿ ((ccount W₂ (elist-to-clist E') (wkn-to-wkc (wkn-cons ϖ')) , ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' (wkn-cons ϖ'))) csn ⟫) ∷ csn)
        c≤c' : ((ccount W₂ (elist-to-clist E) (wkn-to-wkc (wkn-cons ϖ)) , ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn ⟫) ∷ csn) ≤ᶜˢⁿ ((ccount W₂ (elist-to-clist E') (wkn-to-wkc (wkn-cons ϖ')) , ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' (wkn-cons ϖ'))) csn ⟫) ∷ csn)
        c≤c' = [s≤s] d0 (≤ᴹ⇒≤ (a1 csn)) [c≤c]
        a3 = proj₂ (proj₂ (comp-mono-metric W₁ E' ϖ')) c≤c'
        --b1 = ≤ᴹ-trans (a0 ((ccount W₂ (elist-to-clist E') (wkn-to-wkc (wkn-cons ϖ')) , ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn ⟫) ∷ csn)) a3
        b1 = ≤ᴹ-trans (a0 ((ccount W₂ (elist-to-clist E) (wkn-to-wkc (wkn-cons ϖ)) , ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E (wkn-cons ϖ))) csn ⟫) ∷ csn)) a3
        --c1 = +-≤-cong (≤ᴹ⇒≤ b1) (+-≤-cong (≤ᴹ⇒≤ b1) (*-≤-cong (≤-refl {n = ccount W₂ (elist-to-clist E') (wkn-to-wkc (wkn-cons ϖ'))}) (≤ᴹ⇒≤ b1)))
        c1 = +-≤-cong (≤ᴹ⇒≤ b1) (+-≤-cong (≤ᴹ⇒≤ b1) (*-≤-cong d0 (≤ᴹ⇒≤ b1)))
      in
      ≤ᴹ-incr-cong (s≤s c1) (a1 csn) -- ≤ᴹ-incr-cong (s≤s c1) (a1 csn)
    comp-wkz-lemma (app M N) E E' ϖ ϖ' ϕ csn = -- {!!} --rewrite (val-proj₁-lemma M E E' ϖ ϖ' (wkz-to-wkcz ϕ)) =
      let
        d0 = (val-proj₁-lemma M E E' ϖ ϖ' (wkz-to-wkcz ϕ))
        a0 = val-wkz-lemma M E E' ϖ ϖ' ϕ csn
        a1 = val-wkz-lemma N E E' ϖ ϖ' ϕ csn
        b0 = ≤ᴹ-p1 a0
        b1 = ≤ᴹ-pw a0
        --c0 = +-≤-cong b0 (+-≤-cong (≤ᴹ⇒≤ a1) (*-≤-cong (≤-refl {n = proj₁ (val-mono-metric M E' ϖ')}) (≤ᴹ⇒≤ a1)))
        c0 = +-≤-cong b0 (+-≤-cong (≤ᴹ⇒≤ a1) (*-≤-cong d0 (≤ᴹ⇒≤ a1)))
      in
      ≤ᴹ-incr-cong (s≤s (s≤s c0)) b1 --≤ᴹ-incr-cong (s≤s (s≤s c0)) b1
    comp-wkz-lemma (var M) E E' ϖ ϖ' ϕ csn = ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ (val-wkz-lemma M E E' ϖ ϖ' ϕ csn))) (≤ᴹ-refl {nm = zero-metric})
    comp-wkz-lemma (sub W₁ W₂) E E' ϖ ϖ' ϕ csn = --{!!} --rewrite (comp-cnt-lemma W₂ (elist-to-clist E) (elist-to-clist E') (wkn-to-wkc ϖ) (wkn-to-wkc ϖ') (wkz-to-wkcz ϕ)) =
      let
        d0 = comp-cnt-lemma W₂ (elist-to-clist E) (elist-to-clist E') (wkn-to-wkc ϖ) (wkn-to-wkc ϖ') (wkz-to-wkcz ϕ)
        a0 = comp-wkz-lemma W₂ E E' ϖ ϖ' ϕ csn
        a1 :   (⟪ proj₁ (proj₂ (comp-mono-metric W₂ E ϖ)) csn ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E ϖ)) csn ⟫ csn)
             ≤ (⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' ϖ')) csn ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' ϖ')) csn ⟫ csn)
        a1 = +-≤-cong (≤ᴹ⇒≤ a0) (csn-decr (≤ᴹ⇒≤ a0) csn)
        E₁ = ((`V , ccount W₂ (elist-to-clist E) (wkn-to-wkc ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric W₂ E ϖ)) csn ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E ϖ)) csn ⟫ csn)) , (λ {_} {_} c≤c' → ≤-V z≤n ≤-refl)) ∷ E)
        E₂ = ((`V , ccount W₂ (elist-to-clist E') (wkn-to-wkc ϖ') , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' ϖ')) csn ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' ϖ')) csn ⟫ csn)) , (λ {_} {_} c≤c' → ≤-V z≤n ≤-refl)) ∷ E')
        b1 = comp-wkz-lemma W₁ E₁ E₂ (wkn-cong ϖ) (wkn-cong ϖ') (wkz-cong d0 (λ csn₁ → ≤-V z≤n a1) ϕ) csn
      in
      ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ a0)) b1 --≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ a0)) b1

  v̲a̲l̲-mono-metric : (M : V̲a̲l̲ Γ Y) → (E : EMetric) → WkN Γ E → EElem Y
  v̲a̲l̲-mono-metric (l̲a̲m̲ W) E ϖ =
    let
      IH2 = comp-mono-metric W E (wkn-cons ϖ)
      cnt = v̲c̲o̲u̲n̲t̲ (l̲a̲m̲ W) (elist-to-clist E) (wkn-to-wkc ϖ)
    in
    cnt , ((λ csn → incr 1 (m-⇒ 0 ((proj₁ $ proj₂ IH2) csn)))) ,
    λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → (≤-⇒ (s≤s z≤n) ((proj₂ $ proj₂ IH2) c≤c'))
  v̲a̲l̲-mono-metric (pa̲i̲r̲ M₁ M₂) E ϖ =
    let
      cnt = v̲c̲o̲u̲n̲t̲ (pa̲i̲r̲ M₁ M₂) (elist-to-clist E) (wkn-to-wkc ϖ)
      IH1 = v̲a̲l̲-mono-metric M₁ E ϖ
      IH2 = v̲a̲l̲-mono-metric M₂ E ϖ
    in
    cnt , ((λ csn → incr 1 (m-× 0 ((proj₁ $ proj₂ IH1) csn) ((proj₁ $ proj₂ IH2) csn)))) , λ c≤c' → ≤-× ≤-refl ((proj₂ $ proj₂ IH1) c≤c') ((proj₂ $ proj₂ IH2) c≤c')
  v̲a̲l̲-mono-metric u̲n̲i̲t̲ E ϖ =
    vcount unit (elist-to-clist E) (wkn-to-wkc ϖ) ,
    (λ _ → m-Unit 1) ,
    λ {csn₁} {csn₂} z → ≤-Unit (s≤s z≤n)
  v̲a̲l̲-mono-metric (v̲a̲r̲ i) E ϖ =
    let
      IH = lookup-mono-metric i E ϖ
      cnt = v̲c̲o̲u̲n̲t̲ (v̲a̲r̲ i) (elist-to-clist E) (wkn-to-wkc ϖ)
    in
    cnt , (λ csn → incr 1 ((proj₁ $ proj₂ IH) csn)) , λ c≤c' → ≤ᴹ-incr-cong (≤-refl {n = 1}) ((proj₂ $ proj₂ IH) c≤c')

  c̲o̲m̲p-mono-metric : (W : C̲o̲m̲p Γ Y) → (E : EMetric) → WkN Γ E → EElem Y
  c̲o̲m̲p-mono-metric (r̲e̲t̲u̲r̲n̲ M) E ϖ =
    let
      cnt = c̲c̲o̲u̲n̲t̲ (r̲e̲t̲u̲r̲n̲ M) (elist-to-clist E) (wkn-to-wkc ϖ)
      IH = v̲a̲l̲-mono-metric M E ϖ
    in
    cnt , (λ csn → incr 1 ((proj₁ $ proj₂ IH) csn)) , λ c≤c' → ≤ᴹ-incr-cong (≤-refl {n = 1}) ((proj₂ $ proj₂ IH) c≤c')
  c̲o̲m̲p-mono-metric (a̲pp M N) E ϖ =
      let
        cnt = c̲c̲o̲u̲n̲t̲ (a̲pp M N) (elist-to-clist E) (wkn-to-wkc ϖ)
        IH1 = val-mono-metric M E ϖ
        IH2 = v̲a̲l̲-mono-metric N E ϖ
      in
      cnt ,
      (λ csn → incr (1 + ((p1 (proj₁ (proj₂ IH1) csn)) + ((suc $ proj₁ IH1) * ⟪ proj₁ (proj₂ IH2) csn ⟫))) (pw (proj₁ (proj₂ IH1) csn))) ,
      λ c≤c' →
        let
          le1 = +-≤-cong (≤ᴹ-p1 (proj₂ (proj₂ IH1) c≤c')) (*-≤-cong (≤-refl {n = suc $ proj₁ IH1}) (≤ᴹ⇒≤ (proj₂ (proj₂ IH2) c≤c')))
        in
        ≤ᴹ-incr-cong (s≤s le1) (≤ᴹ-pw (proj₂ (proj₂ IH1) c≤c'))

  -----------------------------------------------------------------------------------------------

  lcount-lm-eq : (i : Γ ∋ X) → (E : EMetric) → (ϖ : WkN Γ E) → lcount i (elist-to-clist E) (wkn-to-wkc ϖ) ≡ proj₁ (lookup-mono-metric i E ϖ)
  lcount-lm-eq Cx.h [] (wkn-cons ϖ) = refl
  lcount-lm-eq Cx.h (x ∷ E) (wkn-cong ϖ) = refl
  lcount-lm-eq Cx.h (x ∷ E) (wkn-cons ϖ) = refl
  lcount-lm-eq (Cx.t i) [] (wkn-cons ϖ) = refl
  lcount-lm-eq (Cx.t i) (x ∷ E) (wkn-cong ϖ) = lcount-lm-eq i E ϖ
  lcount-lm-eq (Cx.t i) (x ∷ E) (wkn-cons ϖ) = lcount-lm-eq i (x ∷ E) ϖ

  ccount-eq : (W : Comp Γ X) → (E : EMetric) → (ϖ : WkN Γ E) → ccount W (elist-to-clist E) (wkn-to-wkc ϖ) ≡ proj₁ (comp-mono-metric W E ϖ)
  ccount-eq (return M) E ϖ = refl
  ccount-eq (pm M W) E ϖ = refl
  ccount-eq (push W₁ W₂) E ϖ = refl
  ccount-eq (app M N) E ϖ = refl
  ccount-eq (var M) E ϖ = refl
  ccount-eq (sub W₁ W₂) E ϖ = refl

  vcount-eq : (M : Val Γ X) → (E : EMetric) → (ϖ : WkN Γ E) → vcount M (elist-to-clist E) (wkn-to-wkc ϖ) ≡ proj₁ (val-mono-metric M E ϖ)
  vcount-eq (var i) E ϖ = refl
  vcount-eq (lam x) E ϖ = refl
  vcount-eq (pair M M₁) E ϖ = refl
  vcount-eq (pm M M₁) E ϖ = refl
  vcount-eq unit E ϖ = refl

  v̲c̲o̲u̲n̲t̲-eq : (M : V̲a̲l̲ Γ X) → (E : EMetric) → (ϖ : WkN Γ E) → v̲c̲o̲u̲n̲t̲ M (elist-to-clist E) (wkn-to-wkc ϖ) ≡ proj₁ (v̲a̲l̲-mono-metric M E ϖ)
  v̲c̲o̲u̲n̲t̲-eq (l̲a̲m̲ W) E ϖ = refl
  v̲c̲o̲u̲n̲t̲-eq (pa̲i̲r̲ M₁ M₂) E ϖ = refl
  v̲c̲o̲u̲n̲t̲-eq u̲n̲i̲t̲ E ϖ = refl
  v̲c̲o̲u̲n̲t̲-eq (v̲a̲r̲ i) E ϖ = refl

  {-# REWRITE ccount-eq #-}
  {-# REWRITE vcount-eq #-}
  {-# REWRITE v̲c̲o̲u̲n̲t̲-eq #-}

  -----------------------------------------------------------------------------------------------

  mutual
    vcount-wkce-lemma : (M : Val Γ' X) → (E E' : List ℕ)
                → (π : Wk Γ Γ') → (ϖ : WkC Γ E) → (ϖ' : WkC Γ' E') → (θ : WkCE π ϖ ϖ')
                → (vcount M E' ϖ') ≡ (vcount (wk-val π M) E ϖ)
    vcount-wkce-lemma (var i) E E' π ϖ ϖ' θ = lcount-wkce-lemma i E E' π ϖ ϖ' θ
    vcount-wkce-lemma (lam W) E E' π ϖ ϖ' θ = ccount-wkce-lemma W E E' (wk-cong π) (wkc-cons ϖ) (wkc-cons ϖ') (wkce-cww π ϖ ϖ' θ)
    vcount-wkce-lemma (pair M₁ M₂) E E' π ϖ ϖ' θ = cong₂ _+_ (vcount-wkce-lemma M₁ E E' π ϖ ϖ' θ) (vcount-wkce-lemma M₂ E E' π ϖ ϖ' θ)
    vcount-wkce-lemma (pm M N) E E' π ϖ ϖ' θ rewrite (vcount-wkce-lemma M E E' π ϖ ϖ' θ) = vcount-wkce-lemma N (vcount (wk-val π M) E ϖ ∷ vcount (wk-val π M) E ϖ ∷ E) (vcount (wk-val π M) E ϖ ∷ vcount (wk-val π M) E ϖ ∷ E') (wk-cong (wk-cong π)) (wkc-cong (wkc-cong ϖ)) (wkc-cong (wkc-cong ϖ')) (wkce-ccc (wk-cong π) (wkc-cong ϖ) (wkc-cong ϖ') (vcount (wk-val π M) E ϖ) (wkce-ccc π ϖ ϖ' (vcount (wk-val π M) E ϖ) θ))
    vcount-wkce-lemma unit E E' π ϖ ϖ' θ = refl

    ccount-wkce-lemma : (W : Comp Γ' X) → (E E' : List ℕ)
                → (π : Wk Γ Γ') → (ϖ : WkC Γ E) → (ϖ' : WkC Γ' E') → (θ : WkCE π ϖ ϖ')
                → (ccount W E' ϖ') ≡ (ccount (wk-comp π W) E ϖ)
    ccount-wkce-lemma (return M) E E' π ϖ ϖ' θ = vcount-wkce-lemma M E E' π ϖ ϖ' θ
    ccount-wkce-lemma (pm M W) E E' π ϖ ϖ' θ rewrite vcount-wkce-lemma M E E' π ϖ ϖ' θ = ccount-wkce-lemma W (vcount (wk-val π M) E ϖ ∷ vcount (wk-val π M) E ϖ ∷ E) (vcount (wk-val π M) E ϖ ∷ vcount (wk-val π M) E ϖ ∷ E') (wk-cong (wk-cong π)) (wkc-cong (wkc-cong ϖ)) (wkc-cong (wkc-cong ϖ')) (wkce-ccc (wk-cong π) (wkc-cong ϖ) (wkc-cong ϖ') (vcount (wk-val π M) E ϖ) (wkce-ccc π ϖ ϖ' (vcount (wk-val π M) E ϖ) θ))
    ccount-wkce-lemma (push W₁ W₂) E E' π ϖ ϖ' θ rewrite ccount-wkce-lemma W₁ E E' π ϖ ϖ' θ = ccount-wkce-lemma W₂ (ccount (wk-comp π W₁) E ϖ ∷ E) (ccount (wk-comp π W₁) E ϖ ∷ E') (wk-cong π) (wkc-cong ϖ) (wkc-cong ϖ') (wkce-ccc π ϖ ϖ' (ccount (wk-comp π W₁) E ϖ) θ)
    ccount-wkce-lemma (app M N) E E' π ϖ ϖ' θ rewrite vcount-wkce-lemma M E E' π ϖ ϖ' θ | vcount-wkce-lemma N E E' π ϖ ϖ' θ = refl
    ccount-wkce-lemma (var M) E E' π ϖ ϖ' θ = vcount-wkce-lemma M E E' π ϖ ϖ' θ
    ccount-wkce-lemma (sub W₁ W₂) E E' π ϖ ϖ' θ rewrite ccount-wkce-lemma W₂ E E' π ϖ ϖ' θ = ccount-wkce-lemma W₁ (ccount (wk-comp π W₂) E ϖ ∷ E) (ccount (wk-comp π W₂) E ϖ ∷ E') (wk-cong π) (wkc-cong ϖ) (wkc-cong ϖ') (wkce-ccc π ϖ ϖ' (ccount (wk-comp π W₂) E ϖ) θ)

  mutual
    val-wke-lemma : (M : Val Γ' X) → (E E' : EMetric)
                  → (π : Wk Γ Γ') → (ϖ : WkN Γ E) → (ϖ' : WkN Γ' E') → (θ : WkE π ϖ ϖ')
                  → (val-mono-metric M E' ϖ') ≡ (val-mono-metric (wk-val π M) E ϖ)
    val-wke-lemma (var i) E E' π ϖ ϖ' θ rewrite lcount-lm-eq i E' ϖ' | lcount-lm-eq (wk-mem π i) E ϖ =
                  cong
                  (λ x → (proj₁ x ,
                  (λ csn → incr 2 (proj₁ (proj₂ x) csn)) ,
                  (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (s≤s {n = 0} z≤n)) (proj₂ (proj₂ x) c≤c')))) ((lookup-wke-lemma i E E' π ϖ ϖ' θ))
    val-wke-lemma (lam {A = A} W) E E' π ϖ ϖ' θ rewrite wkc-cons-comm {Y = A} ϖ | wkc-cons-comm {Y = A} ϖ' | (comp-wke-lemma W E E' (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ)) =
                  let
                    a0 = (comp-wke-lemma W E E' (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ))
                    a2 = λ x → (proj₁ x , (λ csn → m-⇒ 2 (proj₁ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W) E (wkn-cons ϖ))) csn)) , (λ {csn₁} {csn₂} c≤c' → ≤-⇒ (s≤s (s≤s z≤n)) (proj₂ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W) E (wkn-cons ϖ))) c≤c')))
                    a3 = cong a2 a0
                  in
                  a3
    val-wke-lemma (pair M₁ M₂) E E' π ϖ ϖ' θ =
                  cong₂
                  (λ x y →
                  (proj₁ x + proj₁ y , (λ csn → m-× 2 (proj₁ (proj₂ x) csn) (proj₁ (proj₂ y) csn)) , (λ {csn₁} {csn₂} c≤c' → ≤-× (s≤s (s≤s z≤n)) (proj₂ (proj₂ x) c≤c') (proj₂ (proj₂ y) c≤c'))) )
                  (val-wke-lemma M₁ E E' π ϖ ϖ' θ)
                  (val-wke-lemma M₂ E E' π ϖ ϖ' θ)
    val-wke-lemma (pm {A = A} {B = B} M N) E E' π ϖ ϖ' θ =
      let
        a0 = λ x y → (vcount N (proj₁ x ∷ proj₁ x ∷ elist-to-clist E') (wkc-cong (wkc-cong (wkn-to-wkc ϖ'))) , (λ csn → incr (suc (vx (proj₁ (proj₂ x) csn) + ⟪ proj₁ (proj₂ y) csn ⟫)) (proj₁ (proj₂ (val-mono-metric N ((B , proj₁ x , (λ c → rhs (proj₁ (proj₂ x) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ x) c≤c'))) ∷ (A , proj₁ x , (λ c → lhs (proj₁ (proj₂ x) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ x) c≤c'))) ∷ E') (wkn-cong (wkn-cong ϖ')))) csn)) , (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (+-≤-cong (≤ᴹ-vx (proj₂ (proj₂ x) c≤c')) (≤ᴹ⇒≤ (proj₂ (proj₂ y) c≤c')))) (proj₂ (proj₂ (val-mono-metric N ((B , proj₁ x , (λ c → rhs (proj₁ (proj₂ x) c)) , (λ {csn₁} {csn₂} c≤c'' → ≤ᴹ-rhs (proj₂ (proj₂ x) c≤c''))) ∷ (A , proj₁ x , (λ c → lhs (proj₁ (proj₂ x) c)) , (λ {csn₁} {csn₂} c≤c'' → ≤ᴹ-lhs (proj₂ (proj₂ x) c≤c''))) ∷ E') (wkn-cong (wkn-cong ϖ')))) c≤c')))
        a1 = cong₂ a0 (val-wke-lemma M E E' π ϖ ϖ' θ) (val-wke-lemma N E E' (wk-cong (wk-cong π)) (wkn-cons (wkn-cons ϖ)) (wkn-cons (wkn-cons ϖ')) (wke-cww (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ)))
        a2 = val-wke-lemma
          N
          ((B , proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c≤c'))) ∷ (A , proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c≤c'))) ∷ E)
          ((B , proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (val-mono-metric (wk-val π M) E ϖ) .proj₂ c≤c')))  ∷ (A , proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (val-mono-metric (wk-val π M) E ϖ) .proj₂ c≤c'))) ∷ E')
          (wk-cong (wk-cong π))
          (wkn-cong (wkn-cong ϖ))
          (wkn-cong (wkn-cong ϖ'))
          (wke-ccc (wk-cong π) (wkn-cong ϖ) (wkn-cong ϖ') (proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c≤c'))) (wke-ccc π ϖ ϖ' (proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c≤c'))) θ))
        a3 = vcount-wkce-lemma
          N
          (proj₁ (val-mono-metric (wk-val π M) E ϖ) ∷ proj₁ (val-mono-metric (wk-val π M) E ϖ) ∷ elist-to-clist E)
          (proj₁ (val-mono-metric (wk-val π M) E ϖ) ∷ proj₁ (val-mono-metric (wk-val π M) E ϖ) ∷ elist-to-clist E')
          (wk-cong (wk-cong π))
          (wkc-cong (wkc-cong (wkn-to-wkc ϖ)))
          (wkc-cong (wkc-cong (wkn-to-wkc ϖ')))
          (wkce-ccc (wk-cong π) (wkc-cong (wkn-to-wkc ϖ)) (wkc-cong (wkn-to-wkc ϖ')) (proj₁ (val-mono-metric (wk-val π M) E ϖ))
            (wkce-ccc π (wkn-to-wkc ϖ) (wkn-to-wkc ϖ') (proj₁ (val-mono-metric (wk-val π M) E ϖ)) (wke-to-wkce θ)))
        a4 = cong (λ x → (x , (λ csn → incr (suc (vx (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) csn) + ⟪ proj₁ (proj₂ (val-mono-metric (wk-val (wk-cong (wk-cong π)) N) E (wkn-cons (wkn-cons ϖ)))) csn ⟫)) (proj₁ (proj₂ (val-mono-metric N  ((B , proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (val-mono-metric (wk-val π M) E ϖ) .proj₂ c≤c')))  ∷ (A , proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (val-mono-metric (wk-val π M) E ϖ) .proj₂ c≤c'))) ∷ E') (wkn-cong (wkn-cong ϖ')))) csn)) , (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (+-≤-cong (≤ᴹ-vx (proj₂ (val-mono-metric (wk-val π M) E ϖ) .proj₂ c≤c')) (≤ᴹ⇒≤ (proj₂ (val-mono-metric (wk-val (wk-cong (wk-cong π)) N) E (wkn-cons (wkn-cons ϖ))) .proj₂ c≤c')))) (proj₂ (proj₂ (val-mono-metric N ((B , proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ {csn₁} {csn₂} c≤c'' → ≤ᴹ-rhs (proj₂ (val-mono-metric (wk-val π M) E ϖ) .proj₂ c≤c''))) ∷ (A , proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ {csn₁} {csn₂} c≤c'' → ≤ᴹ-lhs (proj₂ (val-mono-metric (wk-val π M) E ϖ) .proj₂ c≤c''))) ∷ E') (wkn-cong (wkn-cong ϖ')))) c≤c')))) a3
        a5 = λ x → (vcount (wk-val (wk-cong (wk-cong π)) N) (proj₁ (val-mono-metric (wk-val π M) E ϖ) ∷ proj₁ (val-mono-metric (wk-val π M) E ϖ) ∷ elist-to-clist E)  (wkc-cong (wkc-cong (wkn-to-wkc ϖ)))  , (λ csn → incr (suc (vx (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) csn) + ⟪ proj₁ (proj₂ (val-mono-metric (wk-val (wk-cong (wk-cong π)) N) E (wkn-cons (wkn-cons ϖ)))) csn ⟫)) (proj₁ (proj₂ x) csn)) , (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (+-≤-cong (≤ᴹ-vx (proj₂ (val-mono-metric (wk-val π M) E ϖ) .proj₂ c≤c'))  (≤ᴹ⇒≤ (proj₂ (val-mono-metric (wk-val (wk-cong (wk-cong π)) N) E (wkn-cons (wkn-cons ϖ))) .proj₂ c≤c'))))  (proj₂ (proj₂ x) c≤c')))
        a6 = cong a5 a2
        b1 = trans a1 a4
        b2 = trans b1 a6
      in
      b2
    val-wke-lemma unit E E' π ϖ ϖ' θ = refl

    comp-wke-lemma : (W : Comp Γ' X) → (E E' : EMetric)
                → (π : Wk Γ Γ') → (ϖ : WkN Γ E) → (ϖ' : WkN Γ' E') → (θ : WkE π ϖ ϖ')
                → (comp-mono-metric W E' ϖ') ≡ (comp-mono-metric (wk-comp π W) E ϖ)
    comp-wke-lemma (return M) E E' π ϖ ϖ' θ = cong (λ x → (proj₁ x , (λ csn → incr 2 (proj₁ (proj₂ x) csn)) , (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (s≤s z≤n)) (proj₂ (proj₂ x) c≤c')))) (val-wke-lemma M E E' π ϖ ϖ' θ)
    comp-wke-lemma (pm {A = A} {B = B} M W) E E' π ϖ ϖ' θ =
      let
        a0 = λ x y → (ccount W (proj₁ x ∷ proj₁ x ∷ elist-to-clist E') (wkc-cong (wkc-cong (wkn-to-wkc ϖ'))) , (λ csn → incr (suc (vx (proj₁ (proj₂ x) csn) + ⟪ proj₁ (proj₂ y) csn ⟫)) (proj₁ (proj₂ (comp-mono-metric W ((B , proj₁ x , (λ c → rhs (proj₁ (proj₂ x) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ x) c≤c'))) ∷ (A , proj₁ x , (λ c → lhs (proj₁ (proj₂ x) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ x) c≤c'))) ∷ E') (wkn-cong (wkn-cong ϖ')))) csn)) , (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (+-≤-cong (≤ᴹ-vx (proj₂ (proj₂ x) c≤c')) (≤ᴹ⇒≤ (proj₂ (proj₂ y) c≤c')))) (proj₂ (proj₂ (comp-mono-metric W ((B , proj₁ x , (λ c → rhs (proj₁ (proj₂ x) c)) , (λ {csn₁} {csn₂} c≤c'' → ≤ᴹ-rhs (proj₂ (proj₂ x) c≤c''))) ∷ (A , proj₁ x , (λ c → lhs (proj₁ (proj₂ x) c)) , (λ {csn₁} {csn₂} c≤c'' → ≤ᴹ-lhs (proj₂ (proj₂ x) c≤c''))) ∷ E') (wkn-cong (wkn-cong ϖ')))) c≤c')))
        a1 = cong₂ a0 (val-wke-lemma M E E' π ϖ ϖ' θ) (comp-wke-lemma W E E' (wk-cong (wk-cong π)) (wkn-cons (wkn-cons ϖ)) (wkn-cons (wkn-cons ϖ')) (wke-cww (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ)))
        a2 = comp-wke-lemma
          W
          ((B , proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c≤c'))) ∷ (A , proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c≤c'))) ∷ E)
          ((B , proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (val-mono-metric (wk-val π M) E ϖ) .proj₂ c≤c')))  ∷ (A , proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (val-mono-metric (wk-val π M) E ϖ) .proj₂ c≤c'))) ∷ E')
          (wk-cong (wk-cong π))
          (wkn-cong (wkn-cong ϖ))
          (wkn-cong (wkn-cong ϖ'))
          (wke-ccc (wk-cong π) (wkn-cong ϖ) (wkn-cong ϖ') (proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c≤c'))) (wke-ccc π ϖ ϖ' (proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c≤c'))) θ))
        a3 = ccount-wkce-lemma
          W
          (proj₁ (val-mono-metric (wk-val π M) E ϖ) ∷ proj₁ (val-mono-metric (wk-val π M) E ϖ) ∷ elist-to-clist E)
          (proj₁ (val-mono-metric (wk-val π M) E ϖ) ∷ proj₁ (val-mono-metric (wk-val π M) E ϖ) ∷ elist-to-clist E')
          (wk-cong (wk-cong π))
          (wkc-cong (wkc-cong (wkn-to-wkc ϖ)))
          (wkc-cong (wkc-cong (wkn-to-wkc ϖ')))
          (wkce-ccc (wk-cong π) (wkc-cong (wkn-to-wkc ϖ)) (wkc-cong (wkn-to-wkc ϖ')) (proj₁ (val-mono-metric (wk-val π M) E ϖ))
            (wkce-ccc π (wkn-to-wkc ϖ) (wkn-to-wkc ϖ') (proj₁ (val-mono-metric (wk-val π M) E ϖ)) (wke-to-wkce θ)))
        a4 = cong (λ x → (x , (λ csn → incr (suc (vx (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) csn) + ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp (wk-cong (wk-cong π)) W) E (wkn-cons (wkn-cons ϖ)))) csn ⟫)) (proj₁ (proj₂ (comp-mono-metric W  ((B , proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (val-mono-metric (wk-val π M) E ϖ) .proj₂ c≤c')))  ∷ (A , proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (val-mono-metric (wk-val π M) E ϖ) .proj₂ c≤c'))) ∷ E') (wkn-cong (wkn-cong ϖ')))) csn)) , (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (+-≤-cong (≤ᴹ-vx (proj₂ (val-mono-metric (wk-val π M) E ϖ) .proj₂ c≤c')) (≤ᴹ⇒≤ (proj₂ (comp-mono-metric (wk-comp (wk-cong (wk-cong π)) W) E (wkn-cons (wkn-cons ϖ))) .proj₂ c≤c')))) (proj₂ (proj₂ (comp-mono-metric W ((B , proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ {csn₁} {csn₂} c≤c'' → ≤ᴹ-rhs (proj₂ (val-mono-metric (wk-val π M) E ϖ) .proj₂ c≤c''))) ∷ (A , proj₁ (val-mono-metric (wk-val π M) E ϖ) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) c)) , (λ {csn₁} {csn₂} c≤c'' → ≤ᴹ-lhs (proj₂ (val-mono-metric (wk-val π M) E ϖ) .proj₂ c≤c''))) ∷ E') (wkn-cong (wkn-cong ϖ')))) c≤c')))) a3
        a5 = λ x → (ccount (wk-comp (wk-cong (wk-cong π)) W) (proj₁ (val-mono-metric (wk-val π M) E ϖ) ∷ proj₁ (val-mono-metric (wk-val π M) E ϖ) ∷ elist-to-clist E)  (wkc-cong (wkc-cong (wkn-to-wkc ϖ)))  , (λ csn → incr (suc (vx (proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ)) csn) + ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp (wk-cong (wk-cong π)) W) E (wkn-cons (wkn-cons ϖ)))) csn ⟫)) (proj₁ (proj₂ x) csn)) , (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (+-≤-cong (≤ᴹ-vx (proj₂ (val-mono-metric (wk-val π M) E ϖ) .proj₂ c≤c'))  (≤ᴹ⇒≤ (proj₂ (comp-mono-metric (wk-comp (wk-cong (wk-cong π)) W) E (wkn-cons (wkn-cons ϖ))) .proj₂ c≤c'))))  (proj₂ (proj₂ x) c≤c')))
        a6 = cong a5 a2
        b1 = trans a1 a4
        b2 = trans b1 a6
      in
      b2
    comp-wke-lemma (push W₁ W₂) E E' π ϖ ϖ' θ =
      let
        a0 = λ x y → (ccount W₂ (proj₁ x ∷ elist-to-clist E') (wkc-cong (wkn-to-wkc ϖ')) , (λ csn → incr (suc (⟪ proj₁ (proj₂ x) ((proj₁ y , ⟪ proj₁ (proj₂ y) csn ⟫) ∷ csn) ⟫ + (⟪ proj₁ (proj₂ x) ((proj₁ y , ⟪ proj₁ (proj₂ y) csn ⟫) ∷ csn) ⟫ + proj₁ y * ⟪ proj₁ (proj₂ x) ((proj₁ y , ⟪ proj₁ (proj₂ y) csn ⟫) ∷ csn) ⟫))) (proj₁ (proj₂ y) csn)) , (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (*-≤-cong (s≤s (s≤s (≤-refl {n = (proj₁ y)}))) (≤ᴹ⇒≤ (proj₂ (proj₂ x) ([s≤s] ≤-refl (≤ᴹ⇒≤ (proj₂ (proj₂ y) c≤c')) c≤c'))))) (proj₂ (proj₂ y) c≤c'))) 
        a1 = comp-wke-lemma W₁ E E' π ϖ ϖ' θ
        a2 = comp-wke-lemma W₂ E E' (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ)
        a3 = cong₂ a0 a1 a2
        m = proj₁ (comp-mono-metric (wk-comp (wk-cong π) W₂) E (wkn-cons ϖ))
        a4 = λ x → x , (λ csn → incr (suc (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₁) E ϖ)) ((proj₁ (comp-mono-metric (wk-comp (wk-cong π) W₂) E (wkn-cons ϖ)) , ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W₂) E (wkn-cons ϖ))) csn ⟫) ∷ csn) ⟫ + (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₁) E ϖ)) ((proj₁ (comp-mono-metric (wk-comp (wk-cong π) W₂) E (wkn-cons ϖ)) , ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W₂) E (wkn-cons ϖ))) csn ⟫) ∷ csn) ⟫ + proj₁ (comp-mono-metric (wk-comp (wk-cong π) W₂) E (wkn-cons ϖ)) * ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₁) E ϖ)) ((proj₁ (comp-mono-metric (wk-comp (wk-cong π) W₂) E (wkn-cons ϖ)) , ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W₂) E (wkn-cons ϖ))) csn ⟫) ∷ csn) ⟫))) (proj₁ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W₂) E (wkn-cons ϖ))) csn)) , (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (*-≤-cong (s≤s (s≤s (≤-refl {n = m}))) (≤ᴹ⇒≤ (proj₂ (comp-mono-metric (wk-comp π W₁) E ϖ) .proj₂  ([s≤s] ≤-refl (≤ᴹ⇒≤ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W₂) E (wkn-cons ϖ)) .proj₂ c≤c')) c≤c')))))  (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W₂) E (wkn-cons ϖ)) .proj₂ c≤c'))
        a5 = ccount-wkce-lemma
              W₂
              (proj₁ (comp-mono-metric (wk-comp π W₁) E ϖ) ∷ elist-to-clist E)
              (proj₁ (comp-mono-metric (wk-comp π W₁) E ϖ) ∷ elist-to-clist E')
              (wk-cong π)
              (wkc-cong (wkn-to-wkc ϖ))
              (wkc-cong (wkn-to-wkc ϖ'))
              (wkce-ccc π (wkn-to-wkc ϖ) (wkn-to-wkc ϖ') (proj₁ (comp-mono-metric (wk-comp π W₁) E ϖ)) (wke-to-wkce θ))
        a6 = cong a4 a5
        a7 = trans a3 a6
      in
      a7
    comp-wke-lemma (app M N) E E' π ϖ ϖ' θ =
      let
        a0 = λ x y → (suc (proj₁ y + proj₁ x * suc (proj₁ y)) , (λ csn → incr (2+ (p1 (proj₁ (proj₂ x) csn) + (⟪ proj₁ (proj₂ y) csn ⟫ + proj₁ x * ⟪ proj₁ (proj₂ y) csn ⟫))) (pw (proj₁ (proj₂ x) csn))) , (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (s≤s (+-≤-cong (≤ᴹ-p1 (proj₂ (proj₂ x) c≤c')) (*-≤-cong (s≤s (≤-refl {n = proj₁ x})) (≤ᴹ⇒≤ (proj₂ (proj₂ y) c≤c')))))) (≤ᴹ-pw (proj₂ (proj₂ x) c≤c'))))
      in
      cong₂ a0 (val-wke-lemma M E E' π ϖ ϖ' θ) (val-wke-lemma N E E' π ϖ ϖ' θ)
    comp-wke-lemma (var M) E E' π ϖ ϖ' θ =
      let
        a0 = λ x → (proj₁ x , (λ csn → incr (suc ⟪ proj₁ (proj₂ x) csn ⟫) zero-metric) , (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ {nm₁ = proj₂ x .proj₁ csn₁} (proj₂ (proj₂ x) c≤c'))) {nm₁ = zero-metric} ≤ᴹ-refl))
      in
      cong a0 (val-wke-lemma M E E' π ϖ ϖ' θ)
    comp-wke-lemma (sub {A = A} W₁ W₂) E E' π ϖ ϖ' θ =
      let
        a0 : EElem A → EElem A
        a0 = λ x → (ccount W₁ (proj₁ x ∷ elist-to-clist E') (wkc-cong (wkn-to-wkc ϖ'))
              , (λ csn → incr (suc ⟪ proj₁ (proj₂ x) csn ⟫) (proj₁ (proj₂ (comp-mono-metric W₁ ((`V , proj₁ x , (λ _ → m-V 0 (⟪ proj₁ (proj₂ x) csn ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ x) csn ⟫ csn)) , (λ c≤c' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ'))) csn))
              , (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ (proj₂ (proj₂ x) c≤c'))) (≤ᴹ-trans (comp-wkz-lemma W₁ ((`V , proj₁ x , (λ _ → m-V 0 (⟪ proj₁ (proj₂ x) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ x) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') ((`V , proj₁ x , (λ _ → m-V 0 (⟪ proj₁ (proj₂ x) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ x) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ') (wkn-cong ϖ') (wkz-cong ≤-refl (λ csn → ≤-V z≤n (+-≤-cong (≤ᴹ⇒≤ (proj₂ (proj₂ x) c≤c')) (≤ᶜˢⁿ-decr (≤ᴹ⇒≤ (proj₂ (proj₂ x) c≤c')) c≤c'))) wkz-id) csn₁) (proj₂ (proj₂ (comp-mono-metric W₁ ((`V , proj₁ x , (λ _ → m-V 0 (⟪ proj₁ (proj₂ x) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ x) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ'))) c≤c'))))
        a1 = comp-wke-lemma W₂ E E' π ϖ ϖ' θ
        a2 = cong a0 a1

        b0 csn₁      = comp-wke-lemma
                                  W₁
                                  ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E)
                                  ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E')
                                  (wk-cong π)
                                  (wkn-cong ϖ)
                                  (wkn-cong ϖ')
                                  (wke-ccc π ϖ ϖ' (proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) θ)

        b1      : (csn₁ csn₂ : List (ℕ × ℕ)) (c≤c' : csn₁ ≤ᶜˢⁿ csn₂) →
                      proj₁ (proj₂ (comp-mono-metric W₁ ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ'))) csn₁
                   ≤ᴹ proj₁ (proj₂ (comp-mono-metric W₁ ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ'))) csn₁
        b1 csn₁ csn₂ c≤c'      = (comp-wkz-lemma                      W₁  ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ') (wkn-cong ϖ') (wkz-cong ≤-refl (λ csn → ≤-V z≤n (+-≤-cong (≤ᴹ⇒≤ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₂ c≤c'))  (≤ᶜˢⁿ-decr (≤ᴹ⇒≤ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₂ c≤c')) c≤c'))) wkz-id) csn₁)

        bx csn₁ = comp-wke-lemma
              W₁
              ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E)
              ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E')
              (wk-cong π)
              (wkn-cong ϖ)
              (wkn-cong ϖ')
              (wke-ccc π ϖ ϖ' (proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) θ)
        by csn₂ = comp-wke-lemma
              W₁
              ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E)
              ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E')
              (wk-cong π)
              (wkn-cong ϖ)
              (wkn-cong ϖ')
              (wke-ccc π ϖ ϖ' (proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) θ)

        b csn₁ csn₂ c≤c' = subst₂ (λ x y → proj₁ (proj₂ x) csn₁ ≤ᴹ proj₁ (proj₂ y) csn₁) (bx csn₁) (by csn₂) (b1 csn₁ csn₂ c≤c')

        b1' csn₁ csn₂ c≤c' = (≤ᴹ-trans (comp-wkz-lemma W₁ ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ') (wkn-cong ϖ') (wkz-cong ≤-refl (λ csn → ≤-V z≤n (+-≤-cong (≤ᴹ⇒≤ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₂ c≤c'))  (≤ᶜˢⁿ-decr (≤ᴹ⇒≤ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₂ c≤c')) c≤c'))) wkz-id) csn₁)  (proj₂ (proj₂ (comp-mono-metric                      W₁  ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ'))) c≤c'))

        b' csn₁ csn₂ c≤c' = subst₂ (λ x y → proj₁ (proj₂ x) csn₁ ≤ᴹ proj₁ (proj₂ y) csn₂) (bx csn₁) (by csn₂) (b1' csn₁ csn₂ c≤c')
        b'₁ csn₁ csn₂ c≤c' = (≤ᴹ-trans (comp-wkz-lemma (wk-comp (wk-cong π) W₁) ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E)  ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E)  (wkn-cong ϖ) (wkn-cong ϖ)   (wkz-cong ≤-refl (λ csn → ≤-V z≤n (+-≤-cong (≤ᴹ⇒≤ (proj₂ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) c≤c')) (≤ᶜˢⁿ-decr (≤ᴹ⇒≤ (proj₂ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) c≤c')) c≤c'))) wkz-id) csn₁) (proj₂ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W₁) ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E)  (wkn-cong ϖ)))  c≤c'))

        b'-eq : (csn₁ csn₂ : List (ℕ × ℕ)) (c≤c' : csn₁ ≤ᶜˢⁿ csn₂) → b' csn₁ csn₂ c≤c' ≡ b'₁ csn₁ csn₂ c≤c'
        b'-eq csn₁ csn₂ c≤c' = ≤ᴹ-uniq (b' csn₁ csn₂ c≤c') (b'₁ csn₁ csn₂ c≤c')

        beq'' csn₁ csn₂ c≤c' = cong (≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ (proj₂ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) c≤c')))) (b'-eq csn₁ csn₂ c≤c')

        c1 : {csn₁ csn₂ : List (ℕ × ℕ)} (c≤c' : csn₁ ≤ᶜˢⁿ csn₂) →
             incr
              (suc ⟪ proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₁ csn₁ ⟫)
              (proj₁ (proj₂ (comp-mono-metric W₁ ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ'))) csn₁)
            ≤ᴹ
             incr
              (suc ⟪ proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₁ csn₂ ⟫)
              (proj₂ (comp-mono-metric W₁ ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ')) .proj₁ csn₂)
        c1 = (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₂ c≤c')))  (≤ᴹ-trans (comp-wkz-lemma                      W₁  ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ') (wkn-cong ϖ') (wkz-cong ≤-refl (λ csn → ≤-V z≤n (+-≤-cong (≤ᴹ⇒≤ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₂ c≤c'))  (≤ᶜˢⁿ-decr (≤ᴹ⇒≤ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₂ c≤c')) c≤c'))) wkz-id) csn₁)  (proj₂ (proj₂ (comp-mono-metric                      W₁  ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ'))) c≤c')))

        c = λ {csn₁} {csn₂} c≤c' → subst₂ (λ x y →
               incr (suc ⟪ proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₁ csn₁ ⟫)
                (proj₁ (proj₂ x) csn₁)
             ≤ᴹ
               incr (suc ⟪ proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₁ csn₂ ⟫)
                (proj₁ (proj₂ y) csn₂)) (bx csn₁) (by csn₂) (≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ (proj₂ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) c≤c'))) (b1' csn₁ csn₂ c≤c'))

        d = λ (csn₁ csn₂ : List (ℕ × ℕ)) → cong₂ (λ x y →
               incr (suc ⟪ proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₁ csn₁ ⟫)
                (proj₁ (proj₂ x) csn₁)
             ≤ᴹ
               incr (suc ⟪ proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₁ csn₂ ⟫)
                (proj₁ (proj₂ y) csn₂)) (bx csn₁) (by csn₂)


        bx' csn₁ = cong (λ x → incr (suc ⟪ proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₁ csn₁ ⟫) (proj₁ (proj₂ x) csn₁)) (comp-wke-lemma
              W₁
              ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E)
              ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E')
              (wk-cong π)
              (wkn-cong ϖ)
              (wkn-cong ϖ')
              (wke-ccc π ϖ ϖ' (proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) θ) )

        by' csn₂ = cong (λ y → incr (suc ⟪ proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₁ csn₂ ⟫) (proj₁ (proj₂ y) csn₂)) (comp-wke-lemma
              W₁
              ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E)
              ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E')
              (wk-cong π)
              (wkn-cong ϖ)
              (wkn-cong ϖ')
              (wke-ccc π ϖ ϖ' (proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) θ) )

        dx :   (λ {csn₁} {csn₂} c≤c' → incr (suc ⟪ proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₁ csn₁ ⟫) (proj₁ (proj₂ (comp-mono-metric W₁ ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ'))) csn₁) ≤ᴹ incr (suc ⟪ proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₁ csn₂ ⟫) (proj₁ (proj₂ (comp-mono-metric W₁ ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ'))) csn₂))
             ≡ (λ {csn₁} {csn₂} c≤c' → incr (suc ⟪ proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₁ csn₁ ⟫) (proj₁ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W₁) ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E) (wkn-cong ϖ))) csn₁) ≤ᴹ incr (suc ⟪ proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₁ csn₂ ⟫) (proj₁ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W₁) ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E) (wkn-cong ϖ))) csn₂))
        dx = cong₂ (λ x y {csn₁ csn₂ : List (ℕ × ℕ)} (c≤c' : csn₁ ≤ᶜˢⁿ csn₂) → x csn₁ ≤ᴹ y csn₂) (extensionality bx') (extensionality by')

        e0 : {csn₁ csn₂ : List (ℕ × ℕ)} (c≤c' : csn₁ ≤ᶜˢⁿ csn₂) → incr (suc ⟪ proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₁ csn₁ ⟫) (proj₁ (proj₂ (comp-mono-metric W₁ ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ'))) csn₁) ≤ᴹ incr (suc ⟪ proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₁ csn₂ ⟫) (proj₂ (comp-mono-metric W₁ ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ')) .proj₁ csn₂)
        e0 = (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₂ c≤c')))  (≤ᴹ-trans (comp-wkz-lemma                      W₁  ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ') (wkn-cong ϖ') (wkz-cong ≤-refl (λ csn → ≤-V z≤n (+-≤-cong (≤ᴹ⇒≤ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₂ c≤c'))  (≤ᶜˢⁿ-decr (≤ᴹ⇒≤ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₂ c≤c')) c≤c'))) wkz-id) csn₁)  (proj₂ (proj₂ (comp-mono-metric                      W₁  ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ'))) c≤c')))

        e1 : {csn₁ csn₂ : List (ℕ × ℕ)} (c≤c' : csn₁ ≤ᶜˢⁿ csn₂) → incr (suc ⟪ proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₁ csn₁ ⟫) (proj₁ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W₁) ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E) (wkn-cong ϖ))) csn₁) ≤ᴹ incr (suc ⟪ proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₁ csn₂ ⟫) (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W₁) ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E) (wkn-cong ϖ)) .proj₁ csn₂)
        e1 = (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ (proj₂ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) c≤c'))) (≤ᴹ-trans (comp-wkz-lemma (wk-comp (wk-cong π) W₁) ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E)  ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E)  (wkn-cong ϖ) (wkn-cong ϖ)   (wkz-cong ≤-refl (λ csn → ≤-V z≤n (+-≤-cong (≤ᴹ⇒≤ (proj₂ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) c≤c')) (≤ᶜˢⁿ-decr (≤ᴹ⇒≤ (proj₂ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) c≤c')) c≤c'))) wkz-id) csn₁) (proj₂ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W₁) ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E)  (wkn-cong ϖ)))  c≤c')))

        h0 = (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₂ c≤c')))  (≤ᴹ-trans (comp-wkz-lemma                      W₁  ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ') (wkn-cong ϖ') (wkz-cong ≤-refl (λ csn → ≤-V z≤n (+-≤-cong (≤ᴹ⇒≤ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₂ c≤c'))  (≤ᶜˢⁿ-decr (≤ᴹ⇒≤ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₂ c≤c')) c≤c'))) wkz-id) csn₁)  (proj₂ (proj₂ (comp-mono-metric                      W₁  ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ'))) c≤c')))

        dx' csn₁ csn₂ = cong₂ (λ x y → x ≤ᴹ y) (bx' csn₁) (by' csn₂)

        f0 = subst₂ (λ x y → {csn₁ csn₂ : List (ℕ × ℕ)} (c≤c' : csn₁ ≤ᶜˢⁿ csn₂) → x csn₁ ≤ᴹ y csn₂) (extensionality bx') (extensionality by') (e0)

        f1 = subst (λ x → {csn₁ csn₂ : List (ℕ × ℕ)} (c≤c' : csn₁ ≤ᶜˢⁿ csn₂) → x csn₁ ≤ᴹ incr (suc ⟪ proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₁ csn₂ ⟫) (proj₂ (comp-mono-metric W₁ ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ')) .proj₁ csn₂))
                     (extensionality bx') (e0)

        f2 = subst (λ y → {csn₁ csn₂ : List (ℕ × ℕ)} (c≤c' : csn₁ ≤ᶜˢⁿ csn₂) → (incr (suc ⟪ proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ) .proj₁ csn₁ ⟫) (proj₁ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W₁) ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E) (wkn-cong ϖ))) csn₁)) ≤ᴹ y csn₂)
                     (extensionality by') (f1)

        h0 csn = λ x → incr (suc ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn ⟫) (proj₁ (proj₂ x) csn)
        h0' = extensionality (λ csn → cong (h0 csn) (bx csn))

        eqy : (csn₁ csn₂ : List (ℕ × ℕ)) (c≤c' : csn₁ ≤ᶜˢⁿ csn₂) →
                 ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ (proj₂ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) c≤c'))) (≤ᴹ-trans (comp-wkz-lemma (wk-comp (wk-cong π) W₁) ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E)  ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E)  (wkn-cong ϖ) (wkn-cong ϖ)   (wkz-cong ≤-refl (λ csn → ≤-V z≤n (+-≤-cong (≤ᴹ⇒≤ (proj₂ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) c≤c')) (≤ᶜˢⁿ-decr (≤ᴹ⇒≤ (proj₂ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) c≤c')) c≤c'))) wkz-id) csn₁) (proj₂ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W₁) ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E)  (wkn-cong ϖ)))  c≤c'))
               ≡ (subst₂ (λ x y → {csn₁ csn₂ : List (ℕ × ℕ)} (c≤c' : csn₁ ≤ᶜˢⁿ csn₂) → x csn₁ ≤ᴹ y csn₂) h0' h0' c1) c≤c'
        eqy csn₁ csn₂ c≤c' = ≤ᴹ-uniq (≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ (proj₂ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) c≤c'))) (≤ᴹ-trans (comp-wkz-lemma (wk-comp (wk-cong π) W₁) ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E) ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E) (wkn-cong ϖ) (wkn-cong ϖ) (wkz-cong ≤-refl (λ csn → ≤-V z≤n (+-≤-cong (≤ᴹ⇒≤ (proj₂ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) c≤c')) (≤ᶜˢⁿ-decr (≤ᴹ⇒≤ (proj₂ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) c≤c')) c≤c'))) wkz-id) csn₁) (proj₂ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W₁) ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E) (wkn-cong ϖ))) c≤c')))
                                         (subst₂ (λ x y → {csn₁ = csn₃ : List (ℕ × ℕ)} {csn₂ = csn₄ : List (ℕ × ℕ)} (c≤c'' : csn₃ ≤ᶜˢⁿ csn₄) → x csn₃ ≤ᴹ y csn₄) h0' h0' c1 c≤c')

        eqy' csn₁ csn₂ = extensionality (eqy csn₁ csn₂)
        eqy'' csn₁ = extensionality' (eqy' csn₁)
        eqy''' = extensionality' eqy''

        eqz = cong (λ x {csn₁} {csn₂} c≤c' → x csn₁ csn₂ c≤c') (sym eqy''')


        h1 = dcong₂ {A = (List (ℕ × ℕ) → TermMetric A)} {B = λ f → {csn₁ csn₂ : List (ℕ × ℕ)} → csn₁ ≤ᶜˢⁿ csn₂ → f csn₁ ≤ᴹ f csn₂}
              (λ x z → (x , λ {csn₁ csn₂ : List (ℕ × ℕ)} → z {csn₁ = csn₁} {csn₂ = csn₂}))
              {y₁ = (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ (proj₂ (comp-mono-metric W₂ E' ϖ') .proj₂ c≤c'))) (≤ᴹ-trans (comp-wkz-lemma W₁ ((`V , proj₁ (comp-mono-metric W₂ E' ϖ') , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' ϖ')) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' ϖ')) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') ((`V , proj₁ (comp-mono-metric W₂ E' ϖ') , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' ϖ')) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' ϖ')) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ') (wkn-cong ϖ') (wkz-cong ≤-refl (λ csn → ≤-V z≤n (+-≤-cong (≤ᴹ⇒≤ (proj₂ (comp-mono-metric W₂ E' ϖ') .proj₂ c≤c')) (≤ᶜˢⁿ-decr (≤ᴹ⇒≤ (proj₂ (comp-mono-metric W₂ E' ϖ') .proj₂ c≤c')) c≤c'))) wkz-id) csn₁) (proj₂ (proj₂ (comp-mono-metric W₁ ((`V , proj₁ (comp-mono-metric W₂ E' ϖ') , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' ϖ')) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' ϖ')) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ'))) c≤c')))}
              (trans (cong proj₁ (cong proj₂ a2)) h0')
              refl



        hx = f-≤ᴹ-uniq --{f = ?}
               ((λ {csn₁} {csn₂} → subst (λ f → {csn₁ = csn₃ : List (ℕ × ℕ)} {csn₂ = csn₄ : List (ℕ × ℕ)} → csn₃ ≤ᶜˢⁿ csn₄ → f csn₃ ≤ᴹ f csn₄) (trans (cong (λ r → proj₁ r) (cong (λ r → proj₂ r) a2)) h0') (λ {csn₁ = csn₃} {csn₂ = csn₄} c≤c' → ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ (proj₂ (comp-mono-metric W₂ E' ϖ') .proj₂ c≤c'))) (≤ᴹ-trans (comp-wkz-lemma W₁ ((`V , proj₁ (comp-mono-metric W₂ E' ϖ') , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' ϖ')) csn₃ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' ϖ')) csn₃ ⟫ csn₃)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') ((`V , proj₁ (comp-mono-metric W₂ E' ϖ') , (λ z → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' ϖ')) csn₄ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' ϖ')) csn₄ ⟫ csn₄)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ') (wkn-cong ϖ') (wkz-cong ≤-refl (λ csn → ≤-V z≤n (+-≤-cong (≤ᴹ⇒≤ (proj₂ (comp-mono-metric W₂ E' ϖ') .proj₂ c≤c')) (≤ᶜˢⁿ-decr (≤ᴹ⇒≤ (proj₂ (comp-mono-metric W₂ E' ϖ') .proj₂ c≤c')) c≤c'))) wkz-id) csn₃) (proj₂ (proj₂ (comp-mono-metric W₁ ((`V , proj₁ (comp-mono-metric W₂ E' ϖ') , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' ϖ')) csn₄ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric W₂ E' ϖ')) csn₄ ⟫ csn₄)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E') (wkn-cong ϖ'))) c≤c')))))
               ((λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ (proj₂ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) c≤c'))) (≤ᴹ-trans (comp-wkz-lemma (wk-comp (wk-cong π) W₁) ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₁ ⟫ csn₁)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E) ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E) (wkn-cong ϖ) (wkn-cong ϖ) (wkz-cong ≤-refl (λ csn → ≤-V z≤n (+-≤-cong (≤ᴹ⇒≤ (proj₂ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) c≤c')) (≤ᶜˢⁿ-decr (≤ᴹ⇒≤ (proj₂ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) c≤c')) c≤c'))) wkz-id) csn₁) (proj₂ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W₁) ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E) (wkn-cong ϖ))) c≤c'))))

        h1' = cong (λ x → ( (λ csn → incr (suc ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn ⟫) (proj₁ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W₁) ((`V , proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) , (λ _ → m-V 0 (⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ (comp-mono-metric (wk-comp π W₂) E ϖ)) csn ⟫ csn)) , (λ c≤c' → ≤-V z≤n ≤-refl)) ∷ E) (wkn-cong ϖ))) csn)), x))
                   hx
        h1'' = trans h1 h1' --h1'

        j0 : ccount W₁ (proj₁ (comp-mono-metric W₂ E' ϖ') ∷ elist-to-clist E') (wkc-cong (wkn-to-wkc ϖ'))
           ≡ ccount W₁ (proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) ∷ elist-to-clist E') (wkc-cong (wkn-to-wkc ϖ'))
        j0 = cong (λ x → (ccount W₁ (proj₁ x ∷ elist-to-clist E') (wkc-cong (wkn-to-wkc ϖ')))) a1

        j1 : ccount W₁ (proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) ∷ elist-to-clist E') (wkc-cong (wkn-to-wkc ϖ'))
           ≡ ccount (wk-comp (wk-cong π) W₁) (proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) ∷ elist-to-clist E) (wkc-cong (wkn-to-wkc ϖ))
        j1 = ccount-wkce-lemma W₁
                (proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) ∷ elist-to-clist E)
                (proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ) ∷ elist-to-clist E')
                (wk-cong π)
                (wkc-cong (wkn-to-wkc ϖ))
                (wkc-cong (wkn-to-wkc ϖ'))
                (wkce-ccc π (wkn-to-wkc ϖ) (wkn-to-wkc ϖ') (proj₁ (comp-mono-metric (wk-comp π W₂) E ϖ)) (wke-to-wkce θ))
        j2 = trans j0 j1

        l0 = cong₂ (λ x y → (x , y)) j2 h1''

      in
      l0

  v̲a̲l̲-wke-lemma : (M : V̲a̲l̲ Γ' X) → (E E' : EMetric)
                → (π : Wk Γ Γ') → (ϖ : WkN Γ E) → (ϖ' : WkN Γ' E') → (θ : WkE π ϖ ϖ')
                → (v̲a̲l̲-mono-metric M E' ϖ') ≡ (v̲a̲l̲-mono-metric (wk-v̲a̲l̲ π M) E ϖ)
  v̲a̲l̲-wke-lemma (l̲a̲m̲ {X = A} W) E E' π ϖ ϖ' θ rewrite wkc-cons-comm {Y = A} ϖ | wkc-cons-comm {Y = A} ϖ' | (comp-wke-lemma W E E' (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ)) =
                  let
                    a0 = (comp-wke-lemma W E E' (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wke-cww π ϖ ϖ' θ))
                    a2 = λ x → (proj₁ x , (λ csn → m-⇒ 1 (proj₁ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W) E (wkn-cons ϖ))) csn)) , (λ {csn₁} {csn₂} c≤c' → ≤-⇒ (s≤s z≤n) (proj₂ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W) E (wkn-cons ϖ))) c≤c')))
                    a3 = cong a2 a0
                  in
                  a3
  v̲a̲l̲-wke-lemma (pa̲i̲r̲ M₁ M₂) E E' π ϖ ϖ' θ =
                  cong₂
                  (λ x y →
                  (proj₁ x + proj₁ y , (λ csn → m-× 1 (proj₁ (proj₂ x) csn) (proj₁ (proj₂ y) csn)) , (λ {csn₁} {csn₂} c≤c' → ≤-× (s≤s z≤n) (proj₂ (proj₂ x) c≤c') (proj₂ (proj₂ y) c≤c'))) )
                  (v̲a̲l̲-wke-lemma M₁ E E' π ϖ ϖ' θ)
                  (v̲a̲l̲-wke-lemma M₂ E E' π ϖ ϖ' θ)
  v̲a̲l̲-wke-lemma u̲n̲i̲t̲ E E' π ϖ ϖ' θ = refl
  v̲a̲l̲-wke-lemma (v̲a̲r̲ i) E E' π ϖ ϖ' θ rewrite lcount-lm-eq i E' ϖ' | lcount-lm-eq (wk-mem π i) E ϖ =
                  cong
                  (λ x → (proj₁ x ,
                  (λ csn → incr 1 (proj₁ (proj₂ x) csn)) ,
                  (λ {csn₁} {csn₂} c≤c' → ≤ᴹ-incr-cong (s≤s {n = 0} z≤n) (proj₂ (proj₂ x) c≤c')))) ((lookup-wke-lemma i E E' π ϖ ϖ' θ))

  val-wke-lemma-p1p2 : (M : Val Γ' X) → (E E' : EMetric)
              → (π : Wk Γ Γ') → (ϖ : WkN Γ E) → (ϖ' : WkN Γ' E') → (θ : WkE π ϖ ϖ') → (csn : List (ℕ × ℕ))
              → ((proj₁ (proj₂ (val-mono-metric M E' ϖ'))) csn) ≡ ((proj₁ (proj₂ (val-mono-metric (wk-val π M) E ϖ))) csn)
  val-wke-lemma-p1p2 M E E' π ϖ ϖ' θ csn = cong (λ x → proj₁ x csn) (cong proj₂ (val-wke-lemma M E E' π ϖ ϖ' θ))

  comp-wke-lemma-p1p2 : (W : Comp Γ' X) → (E E' : EMetric)
              → (π : Wk Γ Γ') → (ϖ : WkN Γ E) → (ϖ' : WkN Γ' E') → (θ : WkE π ϖ ϖ') → (csn : List (ℕ × ℕ))
              → ((proj₁ (proj₂ (comp-mono-metric W E' ϖ'))) csn) ≡ ((proj₁ (proj₂ (comp-mono-metric (wk-comp π W) E ϖ))) csn)
  comp-wke-lemma-p1p2 W E E' π ϖ ϖ' θ csn = cong (λ x → proj₁ x csn) (cong proj₂ (comp-wke-lemma W E E' π ϖ ϖ' θ))

  v̲a̲l̲-wke-lemma-p1p2 : (M : V̲a̲l̲ Γ' X) → (E E' : EMetric)
              → (π : Wk Γ Γ') → (ϖ : WkN Γ E) → (ϖ' : WkN Γ' E') → (θ : WkE π ϖ ϖ') → (csn : List (ℕ × ℕ))
              → ((proj₁ (proj₂ (v̲a̲l̲-mono-metric M E' ϖ'))) csn) ≡ ((proj₁ (proj₂ (v̲a̲l̲-mono-metric (wk-v̲a̲l̲ π M) E ϖ))) csn)
  v̲a̲l̲-wke-lemma-p1p2 M E E' π ϖ ϖ' θ csn = cong (λ x → proj₁ x csn) (cong proj₂ (v̲a̲l̲-wke-lemma M E E' π ϖ ϖ' θ))

  v̲a̲l̲-wke-lemma-p1 : (M : V̲a̲l̲  Γ' X) → (E E' : EMetric)
              → (π : Wk Γ Γ') → {ϖ : WkN Γ E} → {ϖ' : WkN Γ' E'} → (θ : WkE π ϖ ϖ')
              → (proj₁ (v̲a̲l̲-mono-metric M E' ϖ')) ≡ (proj₁ (v̲a̲l̲-mono-metric (wk-v̲a̲l̲ π M) E ϖ))
  v̲a̲l̲-wke-lemma-p1 M E E' π {ϖ = ϖ} {ϖ' = ϖ'} θ = cong proj₁ (v̲a̲l̲-wke-lemma M E E' π ϖ ϖ' θ)

  -- these are essentially just the count-wkce-lemmas
  val-wke-lemma-p1 : (M : Val Γ' X) → (E E' : EMetric)
              → (π : Wk Γ Γ') → {ϖ : WkN Γ E} → {ϖ' : WkN Γ' E'} → (θ : WkE π ϖ ϖ')
              → (proj₁ (val-mono-metric M E' ϖ')) ≡ (proj₁ (val-mono-metric (wk-val π M) E ϖ))
  val-wke-lemma-p1 M E E' π {ϖ = ϖ} {ϖ' = ϖ'} θ = cong proj₁ (val-wke-lemma M E E' π ϖ ϖ' θ)

  comp-wke-lemma-p1 : (W : Comp Γ' X) → (E E' : EMetric)
              → (π : Wk Γ Γ') → {ϖ : WkN Γ E} → {ϖ' : WkN Γ' E'} → (θ : WkE π ϖ ϖ')
              → (proj₁ (comp-mono-metric W E' ϖ')) ≡ (proj₁ (comp-mono-metric (wk-comp π W) E ϖ))
  comp-wke-lemma-p1 W E E' π {ϖ = ϖ} {ϖ' = ϖ'} θ = cong proj₁ (comp-wke-lemma W E E' π ϖ ϖ' θ)

  -- DEPRECATED:
  -- postulate wke-val-count-lemma : (i : Γ' ∋ Y) → (M : Val Γ' X) → (E E' : EMetric)
  --             → (π : Wk Γ Γ') → (ϖ : WkN Γ E) → (ϖ' : WkN Γ' E') → (θ : WkE π ϖ ϖ') → (csn : List (ℕ × ℕ))
  --             → ((proj₁ (mono-val-count i M E' ϖ')) csn) ≡ ((proj₁ (mono-val-count (wk-mem π i) (wk-val π M) E ϖ)) csn)

  -- DEPRECATED:
  -- postulate wke-comp-count-lemma : (i : Γ' ∋ Y) → (W : Comp Γ' X) → (E E' : EMetric)
  --             → (π : Wk Γ Γ') → (ϖ : WkN Γ E) → (ϖ' : WkN Γ' E') → (θ : WkE π ϖ ϖ') → (csn : List (ℕ × ℕ))
  --             → ((proj₁ (mono-comp-count i W E' ϖ')) csn) ≡ ((proj₁ (mono-comp-count (wk-mem π i) (wk-comp π W) E ϖ)) csn)

  -- DEPRECATED:
  -- postulate val-count-wkx-lemma : (i : Γ ∋ Y) → (W : Val Γ X) → (E E' : EMetric)
  --             → (π : Wk Γ Γ) → (ϖ : WkN Γ E) → (ϖ' : WkN Γ E') → (ϕ : WkX π ϖ ϖ') → (csn : List (ℕ × ℕ))
  --             → (proj₁ (mono-val-count i W E' ϖ') csn) ≡ (proj₁ (mono-val-count i W E ϖ) csn)

  -- DEPRECATED:
  -- postulate comp-count-wkx-lemma : (i : Γ ∋ Y) → (W : Comp Γ X) → (E E' : EMetric)
  --             → (π : Wk Γ Γ) → (ϖ : WkN Γ E) → (ϖ' : WkN Γ E') → (ϕ : WkX π ϖ ϖ') → (csn : List (ℕ × ℕ))
  --             → (proj₁ (mono-comp-count i W E' ϖ') csn) ≡ (proj₁ (mono-comp-count i W E ϖ) csn)

  -- DEPRECATED:
  -- postulate val-wkx-lemma : (M : Val Γ X) → (E E' : EMetric) → (π : Wk Γ Γ) → (ϖ : WkN Γ E) → (ϖ' : WkN Γ E') → (ϕ : WkX π ϖ ϖ')
  --             → (csn : List (ℕ × ℕ)) → (proj₁ (val-mono-metric M E ϖ)) csn ≤ᴹ (proj₁ (val-mono-metric M E' ϖ')) csn

  -- DEPRECATED:
  -- comp-wkx-lemma : (W : Comp Γ X) → (E E' : EMetric) → (π : Wk Γ Γ) → (ϖ : WkN Γ E) → (ϖ' : WkN Γ E') → (ϕ : WkX π ϖ ϖ')
  --             → (csn : List (ℕ × ℕ)) → (proj₁ (comp-mono-metric W E ϖ)) csn ≤ᴹ (proj₁ (comp-mono-metric W E' ϖ')) csn

  -- DEPRECATED:
  -- a̲pp-mono-metric : (M : Val Γ (X `⇒ Y)) → (N : EElem X) → (E : EMetric) → WkN Γ E → EElem Y
  -- a̲pp-mono-metric (var i) N E ϖ = {!!}
  -- a̲pp-mono-metric (lam W) N E ϖ = {!!}
  --   -- let
  --   --   IH1 = comp-mono-metric W ((_ , N) ∷ E) (wkn-cong ϖ)
  --   -- in
  --   -- (λ csn → incr (suc ⟪ proj₁ N csn ⟫) (proj₁ IH1 csn)) ,
  --   -- λ c≤c' → ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ $ proj₂ N c≤c')) (proj₂ IH1 c≤c')
  -- a̲pp-mono-metric (pm M₁ M₂) N E ϖ = {!!}
  --   -- let
  --   --   IH = val-mono-metric M₁ E ϖ
  --   -- in
  --   --  a̲pp-mono-metric M₂ N ((_ , (λ csn → rhs (proj₁ IH csn)) , λ c≤c' → ≤ᴹ-rhs ((proj₂ IH) c≤c')) ∷ (_ , (λ csn → lhs (proj₁ IH csn)) , λ c≤c' → ≤ᴹ-lhs ((proj₂ IH) c≤c')) ∷ E) (wkn-cong (wkn-cong ϖ))

  mutual

    env-mono-metric : Env Γ → Σ[ E ∈ EMetric ] WkN Γ E
    env-mono-metric ∗ = [] , wkn-nil
    env-mono-metric {Γ = Γ ∙ X} (γ ﹐ M) =
      let
        IH = env-mono-metric γ
      in
      (X , v̲a̲l̲-mono-metric M (proj₁ IH) (proj₂ IH)) ∷ (proj₁ IH) , wkn-cong (proj₂ IH)
    env-mono-metric {Γ = Γ ∙ `V} ((γ ﹐﹝ W ╎ cs ﹞) {π = π}) =
      let
        IH = env-mono-metric γ
        IH2 = comp-mono-metric W (proj₁ IH) (proj₂ IH)
        csn = cs-to-csn cs
      in
      (`V , proj₁ IH2 , (λ _ → m-V 0 (⟪ proj₁ (proj₂ IH2) csn ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ IH2) csn ⟫ csn)) , λ _ → ≤ᴹ-refl) ∷ (proj₁ IH) , wkn-cong (proj₂ IH)

    cs-to-csn : (cs : CompStack Δ Z) → List (ℕ × ℕ)
    cs-to-csn ◻ = []
    cs-to-csn ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡}) =
      let
        csn = cs-to-csn cs
        IH = env-mono-metric γ
      in
      (ccount W (elist-to-clist (proj₁ IH)) (wkn-to-wkc (wkn-cons (proj₂ IH))) , ⟪ proj₁ (proj₂ (comp-mono-metric W (proj₁ IH) (wkn-cons (proj₂ IH)))) csn ⟫) ∷ csn
      -- ((proj₁ (mono-comp-count h W (proj₁ IH) (wkn-cons (proj₂ IH))) csn) , ⟪ proj₁ (comp-mono-metric W (proj₁ IH) (wkn-cons (proj₂ IH))) csn ⟫) ∷ csn

  getIndex : LookupState X → Σ[ Γ ∈ Ctx ] Γ ∋ X
  getIndex ⟨ i ∥ _ ⟩ = _ , i

  getLookupEnv : (S : LookupState X) → Env (proj₁ (getIndex S))
  getLookupEnv ⟨ _ ∥ γ ⟩ = γ

  LHS≤ᴹlhs : {LHSnm : TermMetric X} → {RHSnm : TermMetric Y} → {nm : TermMetric (X `× Y)} → (m-× n LHSnm RHSnm) ≤ᴹ nm → LHSnm ≤ᴹ (lhs nm)
  LHS≤ᴹlhs (≤-× x lhs₁≤ᴹlhs₂ rhs₁≤ᴹrhs₂) = lhs₁≤ᴹlhs₂

  RHS≤ᴹrhs : {LHSnm : TermMetric X} → {RHSnm : TermMetric Y} → {nm : TermMetric (X `× Y)} → (m-× n LHSnm RHSnm) ≤ᴹ nm → RHSnm ≤ᴹ (rhs nm)
  RHS≤ᴹrhs (≤-× x lhs₁≤ᴹlhs₂ rhs₁≤ᴹrhs₂) = rhs₁≤ᴹrhs₂

  ×≡vlr : (nm : TermMetric (X `× Y)) → nm ≡ (m-× (vx nm) (lhs nm) (rhs nm))
  ×≡vlr (m-× m l r) = refl

  lstate-metric : LookupState X → EElem X
  lstate-metric ⟨ i ∥ γ ⟩ =
    let
      EP = (env-mono-metric γ)
    in
      lookup-mono-metric i (proj₁ EP) (proj₂ EP)

  lhstate-metric : {T : LookupState X} → LookupHaltingState T → EElem X
  lhstate-metric (found-unit {γ = γ}) = let EP = (env-mono-metric γ) in v̲a̲l̲-mono-metric u̲n̲i̲t̲ (proj₁ EP) (proj₂ EP) -- i.e. 0 , (λ _ → m-Unit 1) , λ _ → ≤ᴹ-refl
  lhstate-metric (found-pair {LHS = LHS} {RHS = RHS} {γ = γ}) = let EP = (env-mono-metric γ) in v̲a̲l̲-mono-metric (pa̲i̲r̲ LHS RHS) (proj₁ EP) (proj₂ EP)
  lhstate-metric (found-lam {W = W} {γ = γ}) = let EP = (env-mono-metric γ) in v̲a̲l̲-mono-metric (l̲a̲m̲ W) (proj₁ EP) (proj₂ EP)
  lhstate-metric (found-comp {W = W} {γ = γ} {cs = cs}) =
    let
      EP = (env-mono-metric γ)
      w = comp-mono-metric W (proj₁ EP) (proj₂ EP)
      csn = (cs-to-csn cs)
    in
      proj₁ w , (λ _ → m-V 0 (⟪ proj₁ (proj₂ w) csn ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ w) csn ⟫ csn)) , λ _ → ≤ᴹ-refl

  data LookupSteps : LookupState X → Set where

    steps : {S T : LookupState X} → S →ᴸ* T → (H : LookupHaltingState T) → ⟦ S ⟧ᴸ ≡ ⟦ T ⟧ᴸ → (π : Wk (lCtx S) (lTCtx T)) → (⟦ π ⟧ʷ ⟦ lEnv S ⟧ᴱ ≡ ⟦ lTEnv T ⟧ᴱ)
            → (proj₁ (lhstate-metric H)) ≤ (proj₁ (lstate-metric S))
            → (∀ (csn : List (ℕ × ℕ)) → (proj₁ (proj₂ (lhstate-metric H))) csn ≤ᴹ (proj₁ (proj₂ (lstate-metric S))) csn)
            → (θ : WkE π (proj₂ (env-mono-metric (lEnv S))) (proj₂ (env-mono-metric (lTEnv T))))
            → LookupSteps S

  lookup : (i : Γ ∋ X) → (γ : Env Γ) → LookupSteps {X = X} ⟨ i ∥ γ ⟩
  lookup h (γ ﹐ l̲a̲m̲ W) = steps (⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩ ◼) found-lam refl (wk-wk wk-id) refl ≤-refl ((λ csn → ≤ᴹ-refl)) (wke-wc- wk-id (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric (lTEnv ⟨ h ∥ γ ﹐ l̲a̲m̲ W ⟩))) (v̲a̲l̲-mono-metric (l̲a̲m̲ W) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) wke-id)
  lookup h (γ ﹐ pa̲i̲r̲ LHS RHS) = steps (⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩ ◼) found-pair refl (wk-wk wk-id) refl ≤-refl ((λ csn → ≤ᴹ-refl)) (wke-wc- wk-id (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric (lTEnv ⟨ h ∥ γ ﹐ pa̲i̲r̲ LHS RHS ⟩))) (v̲a̲l̲-mono-metric (pa̲i̲r̲ LHS RHS) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) wke-id)
  lookup h (γ ﹐ u̲n̲i̲t̲) = steps (⟨ h ∥ _﹐_ γ (u̲n̲i̲t̲) ⟩ ◼) found-unit refl (wk-wk wk-id) refl ≤-refl ((λ csn → ≤ᴹ-refl)) (wke-wc- wk-id (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric (lTEnv ⟨ h ∥ γ ﹐ u̲n̲i̲t̲ ⟩))) (v̲a̲l̲-mono-metric u̲n̲i̲t̲ (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) wke-id)
  lookup h (γ ﹐ v̲a̲r̲ i) with lookup i γ
  ... | steps {T = T} i>>T HT i≡T WK w≡γ cnt₁≤cnt₂ T≤S θ rewrite sym (lcount-lm-eq i (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) = steps (_ →ᴸ⟨ val-h-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ cnt₁≤cnt₂ ((λ csn → ≤ᴹ-incr-cong (z≤n {n = 1}) (T≤S csn))) (wke-wc- WK (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric (lTEnv T))) (v̲a̲l̲-mono-metric (v̲a̲r̲ i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) θ)
  lookup h ((γ ﹐﹝ W ╎ cs ﹞ ) {π = π} {wk≡ = wk≡}) =
    let
      w = comp-mono-metric W (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))
      csn = (cs-to-csn cs)
    in
      steps (⟨ h ∥ γ ﹐﹝ W ╎ cs ﹞ ⟩ ◼) found-comp refl (wk-wk wk-id) refl ≤-refl ((λ csn → ≤ᴹ-refl)) (wke-wc- wk-id (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric (lTEnv ⟨ h ∥ ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡} ) ⟩))) (proj₁ w , (λ _ → m-V 0 (⟪ proj₁ (proj₂ w) csn ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ w) csn ⟫ csn)) , (λ _ → ≤ᴹ-refl)) wke-id)
  lookup (t i) (γ ﹐ M) with lookup i γ
  ... | steps {T = T} i>>T HT i≡T WK w≡γ cnt₁≤cnt₂ T≤S θ = steps (_ →ᴸ⟨ val-t-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ cnt₁≤cnt₂ T≤S (wke-wc- WK (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric (lTEnv T))) (v̲a̲l̲-mono-metric M (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) θ)
  lookup (t i) (γ ﹐﹝ W ╎ cs ﹞) with lookup i γ
  ... | steps {T = T} i>>T HT i≡T WK w≡γ cnt₁≤cnt₂ T≤S θ =
    let
      w = comp-mono-metric W (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))
      csn = (cs-to-csn cs)
    in
      steps (_ →ᴸ⟨ comp-t-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ cnt₁≤cnt₂ T≤S (wke-wc- WK (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric (lTEnv T))) (proj₁ w , (λ _ → m-V 0 (⟪ proj₁ (proj₂ w) csn ⟫ + csn-to-nat₀ ⟪ proj₁ (proj₂ w) csn ⟫ csn)) , (λ _ → ≤ᴹ-refl)) θ)

 --AA
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


  data ValStack : IsEmpty → Ty → Set where

      □ : ValStack empty T◾

      _⊲_∷_ : PartialTerm Γ X → (γ : Env Γ) → (tail : ValStack b T◾) → {↥ : BottomTypeEqualsNextType b X T◾} → ValStack non-empty T◾


  data ValState : Ty → Set where

      ∘_ : ValStack non-empty T◾ → ValState T◾

      ∙_ : ValStack non-empty T◾ → ValState T◾

  data _→ᵛ_ : ValState T◾ → ValState T◾ → Set where

      ∘var-c  :    {i : Γ ∋ `V} → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b `V T◾}
                ----------------------------------------------------------------
                  → ∘ ((⇡ var i ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((⭭ v̲a̲r̲ i ⊲ γ ∷ tail) {↥ = ↥})

      ∘var    :    {i : Γ ∋ X} → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b X T◾}
                  → {M : V̲a̲l̲ Γ' X}
                  → (⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ _﹐_ γ' M ⟩) → (πᵥ : Wk Γ Γ')
                ----------------------------------------------------------------
                  → ∘ ((⇡ var i ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((⭭ (wk-v̲a̲l̲ πᵥ M) ⊲ γ ∷ tail) {↥ = ↥})


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
                ---------------------------------------------------------------------------
              →     ∙ ((⭭ M ⊲ γ ∷ ((⇡ᴸ LHS RHS ⊲ γ' ∷ tail) {↥ = ↥})) {↥ = 🗇})
                  →ᵛ ∘ ((⇡ wk-val π' RHS ⊲ γ ∷ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ tail) {↥ = ↥})) {↥ = 🗇})

      ∙M∷r   :  {M : V̲a̲l̲ Γ Y} → {LHS : V̲a̲l̲ Γ' X} → {RHS : Γ' ⊢ᵛ Y} {π' : Wk Γ Γ'}
              → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b (X `× Y) T◾}
                ---------------------------------------------------------------------------
              →     ∙ ((⭭ M ⊲ γ ∷ ((⇡ᴿ LHS RHS ⊲ γ' ∷ tail) {↥ = ↥})) {↥ = 🗇})
                  →ᵛ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M ⊲ γ ∷ tail) {↥ = ↥})

      ∙pair∷pm  :  {LHS : V̲a̲l̲ Γ X} → {RHS : V̲a̲l̲ Γ Y} → {M : Γ' ⊢ᵛ X `× Y} → {N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z}
              → {π' : Wk Γ Γ'}
              → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b Z T◾}
                ---------------------------------------------------------------------------
              →     ∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ ∷ ((⇡ᴹ M N ⊲ γ' ∷ tail) {↥ = ↥})) {↥ = 🗇})
                  →ᵛ  ∘ ((⇡ (wk-val (wk-cong (wk-cong π')) N) ⊲ γ ﹐ LHS ﹐ (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ∷ tail) {↥ = ↥})


  data _↠ᵛ_ : ValState T◾ → ValState T◾ → Set where

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
  ⟨ ∘var T>>U π ⟩⧻ tail = ∘var T>>U π
  ⟨ ∘lam ⟩⧻ tail = ∘lam
  ⟨ ∘pair ⟩⧻ tail = ∘pair
  ⟨ ∘pm ⟩⧻ tail = ∘pm
  ⟨ ∘unit ⟩⧻ tail = ∘unit
  ⟨ ∙pair∷pm ⟩⧻ tail = ∙pair∷pm
  ⟨ ∙M∷l ⟩⧻ tail = ∙M∷l
  ⟨ ∙M∷r ⟩⧻ tail = ∙M∷r

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

  -------------------------------

  partial-term-metric : PartialTerm Γ X → (E : EMetric) → WkN Γ E → EElem X
  partial-term-metric (⭭ M) E ϖ = v̲a̲l̲-mono-metric M E ϖ
  partial-term-metric (⇡ M) E ϖ = val-mono-metric M E ϖ
  partial-term-metric (⇡ᴹ M N) E ϖ = val-mono-metric (pm M N) E ϖ
  partial-term-metric (⇡ᴸ LHS RHS) E ϖ = val-mono-metric (pair LHS RHS) E ϖ
  partial-term-metric (⇡ᴿ LHS RHS) E ϖ = val-mono-metric (pair (toVal LHS) RHS) E ϖ

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

  valstate-metric : (S : ValState X) → EElem X
  valstate-metric (∘ S) =
    let
      e = env-mono-metric (botStackEnv S)
    in
      partial-term-metric (botStackTerm S) (proj₁ e) (proj₂ e)
  valstate-metric (∙ S) =
    let
      e = env-mono-metric (botStackEnv S)
    in
       partial-term-metric (botStackTerm S) (proj₁ e) (proj₂ e)


{-
  topStackType : (S : ValStack non-empty T◾) → Ty
  topStackType (_⊲_∷_ {X = X} _ _ _) = X

  topStackTerm : (S : ValStack non-empty T◾) → PartialTerm (topStackCtx S) (topStackType S)
  topStackTerm (_⊲_∷_ M _ _) = M

  topType : ValState X → Ty
  topType (∘ S) = topStackType S
  topType (∙ S) = topStackType S

  topTerm : (S : ValState X) → PartialTerm (topCtx S) (topType S)
  topTerm (∘ S) = topStackTerm S
  topTerm (∙ S) = topStackTerm S

  data ValSingleState : ValState T◾ → Set where
    single-∘ : {M : PartialTerm Γ X} → {γ : Env Γ} → ValSingleState (∘ ((M ⊲ γ ∷ □) {↥ = 🗆}))
    single-∙ : {M : PartialTerm Γ X} → {γ : Env Γ} → ValSingleState (∙ ((M ⊲ γ ∷ □) {↥ = 🗆}))

  valstate-metric : (S : ValState X) → (ValSingleState S) → List (ℕ × ℕ) → TermMetric X
  valstate-metric (∘ S) _ csn =
    let
      e = env-metric (topStackEnv S)
    in
      partial-term-metric (topStackTerm S) (proj₁ e) (proj₂ e) csn
  valstate-metric (∙ S) _ csn =
    let
      e = env-metric (topStackEnv S)
    in
       partial-term-metric (topStackTerm S) (proj₁ e) (proj₂ e) csn
-}
  -----------------------------

------------------------------------------------------------------------------

  ---------------------------------------------------------------------------------------


  data ValSteps : ValState T◾ → Set where

    steps : {S T : ValState T◾} → S ↠ᵛ T → ValHaltingState T → ⟦ S ⟧ᵛꟴ ≡ ⟦ T ⟧ᵛꟴ → (π : Wk (botCtx T) (botCtx S)) → (⟦ π ⟧ʷ ⟦ botEnv T ⟧ᴱ ≡ ⟦ botEnv S ⟧ᴱ)
            → (proj₁ (valstate-metric T)) ≤ (proj₁ (valstate-metric S))
            → (∀ (csn : List (ℕ × ℕ)) → (proj₁ (proj₂ (valstate-metric T))) csn ≤ᴹ (proj₁ (proj₂ (valstate-metric S))) csn)
            → (θ : WkE π (proj₂ (env-mono-metric (botEnv T))) (proj₂ (env-mono-metric (botEnv S))))
            → ValSteps S


  wke-trans : {E E' E'' : EMetric}
                        → {π₁ : Wk Γ Γ'} → {π₂ : Wk Γ' Γ''} → {ϖ₁ : WkN Γ E} → {ϖ : WkN Γ' E'} → {ϖ₂ : WkN Γ'' E''}
                        → (θ₁ : WkE π₁ ϖ₁ ϖ) (θ₂ : WkE π₂ ϖ ϖ₂)
                        → WkE (wk-trans π₁ π₂) ϖ₁ ϖ₂
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} wke-ε wke-ε = wke-ε
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-ccc π ϖ₃ ϖ' e θ) (wke-ccc π₃ ϖ₄ ϖ'' e₁ θ') = wke-ccc (wk-trans π π₃) ϖ₃ ϖ'' e (wke-trans θ θ')
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-ccc π ϖ₃ ϖ' e θ) (wke-wc- π₃ ϖ₄ ϖ'' e₁ θ') = wke-wc- (wk-trans π π₃) ϖ₃ ϖ₂ e (wke-trans θ θ')
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-wc- π ϖ₃ ϖ' e θ) wke-ε = wke-wc- (wk-trans π wk-ε) ϖ₃ wkn-nil e (wke-trans θ wke-ε)
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-wc- π ϖ₃ ϖ' e θ) (wke-ccc π₃ ϖ₄ ϖ'' e₁ θ') = wke-wc- (wk-trans π (wk-cong π₃)) ϖ₃ (wkn-cong ϖ'') e (wke-trans θ (wke-ccc π₃ ϖ₄ ϖ'' e₁ θ'))
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-wc- π ϖ₃ ϖ' e θ) (wke-wc- π₃ ϖ₄ ϖ'' e₁ θ') = wke-wc- (wk-trans π (wk-wk π₃)) ϖ₃ ϖ₂ e (wke-trans θ (wke-wc- π₃ ϖ₄ ϖ₂ e₁ θ'))
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-wc- π ϖ₃ ϖ' e θ) (wke-ww- π₃ ϖ₄ ϖ'' θ') = wke-wc- (wk-trans π (wk-wk π₃)) ϖ₃ ϖ₂ e (wke-trans θ (wke-ww- π₃ ϖ₄ ϖ₂ θ'))
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-wc- π ϖ₃ ϖ' e θ) (wke-cww π₃ ϖ₄ ϖ'' θ') = wke-wc- (wk-trans π (wk-cong π₃)) ϖ₃ (wkn-cons ϖ'') e (wke-trans θ (wke-cww π₃ ϖ₄ ϖ'' θ'))
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-ww- π ϖ₃ ϖ' θ) wke-ε = wke-ww- (wk-trans π wk-ε) ϖ₃ wkn-nil (wke-trans θ wke-ε)
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-ww- π ϖ₃ ϖ' θ) (wke-ccc π₃ ϖ₄ ϖ'' e θ') = wke-ww- (wk-trans π (wk-cong π₃)) ϖ₃ (wkn-cong ϖ'') (wke-trans θ (wke-ccc π₃ ϖ₄ ϖ'' e θ'))
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-ww- π ϖ₃ ϖ' θ) (wke-wc- π₃ ϖ₄ ϖ'' e θ') = wke-ww- (wk-trans π (wk-wk π₃)) ϖ₃ ϖ₂ (wke-trans θ (wke-wc- π₃ ϖ₄ ϖ₂ e θ'))
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-ww- π ϖ₃ ϖ' θ) (wke-ww- π₃ ϖ₄ ϖ'' θ') = wke-ww- (wk-trans π (wk-wk π₃)) ϖ₃ ϖ₂ (wke-trans θ (wke-ww- π₃ ϖ₄ ϖ₂ θ'))
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-ww- π ϖ₃ ϖ' θ) (wke-cww π₃ ϖ₄ ϖ'' θ') = wke-ww- (wk-trans π (wk-cong π₃)) ϖ₃ (wkn-cons ϖ'') (wke-trans θ (wke-cww π₃ ϖ₄ ϖ'' θ'))
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-cww π ϖ₃ ϖ' θ) (wke-ww- π₃ ϖ₄ ϖ'' θ') = wke-ww- (wk-trans π π₃) ϖ₃ ϖ₂ (wke-trans θ θ')
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-cww π ϖ₃ ϖ' θ) (wke-cww π₃ ϖ₄ ϖ'' θ') = wke-cww (wk-trans π π₃) ϖ₃ ϖ'' (wke-trans θ θ')

  val-eval-rec : (M : Γ' ⊢ᵛ X) → (γ : Env Γ) → (π : Wk Γ Γ') → ValSteps {T◾ = X} (∘ ((⇡ (wk-val π M) ⊲ γ ∷ □) {↥ = 🗆}))

  val-eval-rec {X = `V} (var {A = .`V} i) γ π = steps (_ →ᵛ⟨ ∘var-c ⟩．) (∙ v̲a̲r̲ (wk-mem π i) ⊲ γ ■) refl wk-id refl ≤-refl (λ csn → ≤ᴹ-incr-cong (s≤s (z≤n {n = 1})) (≤ᴹ-refl {nm = (proj₁ (proj₂ (lookup-mono-metric (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) csn)})) {- (λ csn → ≤ᴹ-incr-cong (s≤s (z≤n {n = 1})) (≤ᴹ-refl {nm = {!!}}) {- (≤ᴹ-refl {nm = (proj₁ (lookup-mono-metric (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) csn)}) -} )-} wke-id
  -- OLD: (λ csn → ≤ᴹ-incr-cong (s≤s (z≤n {n = 1})) (≤ᴹ-refl {nm = (lookup-metric (wk-mem π i) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn)})) wke-id

  val-eval-rec {X = `Unit} (var {A = .`Unit} i) γ π with lookup (wk-mem π i) γ
  ... | steps i>>T found-unit i≡T π₁ w≡γ cnt₁≤cnt₂ T≤ᴹS _ = steps (_ →ᵛ⟨ ∘var i>>T π₁ ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id refl n≤n+m ( λ csn → ≤ᴹ-trans (T≤ᴹS csn) (≤ᴹ-incr-cong (z≤n {n = 2}) (≤ᴹ-refl {nm = (proj₁ (proj₂ (lookup-mono-metric (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) csn)}))) {- (λ csn → ≤ᴹ-trans (T≤ᴹS csn) (≤ᴹ-incr-cong (z≤n {n = 2}) (≤ᴹ-refl {nm = {!!} {- (proj₁ (lookup-mono-metric (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) csn) -} }))) -} wke-id
  -- OLD: (λ csn → ≤ᴹ-trans (T≤ᴹS csn) (≤ᴹ-incr-cong (z≤n {n = 2}) (≤ᴹ-refl {nm = (lookup-metric (wk-mem π i) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn)}))) wke-id

  val-eval-rec {X = X `× X₁} (var {A = .(X `× X₁)} i) γ π with lookup (wk-mem π i) γ
  ... | steps i>>T (found-pair {LHS = LHS} {RHS = RHS} {γ = γ₁}) i≡T π₁ w≡γ cnt₁≤cnt₂ T≤ᴹS θ =

            let
              a1 = v̲a̲l̲-wke-lemma-p1p2 LHS (proj₁ (env-mono-metric γ)) (proj₁ (env-mono-metric γ₁)) π₁ (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric γ₁)) θ
              a2 = v̲a̲l̲-wke-lemma-p1p2 RHS (proj₁ (env-mono-metric γ)) (proj₁ (env-mono-metric γ₁)) π₁ (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric γ₁)) θ
              T≤ᴹS' csn  = subst (λ x → (m-× 1 x ( (proj₁ (proj₂ (v̲a̲l̲-mono-metric RHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁)))) csn) ) ≤ᴹ proj₁ (proj₂ (lookup-mono-metric (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) csn)) (a1 csn) (T≤ᴹS csn) --subst (λ x → (m-× 1 x ( (proj₁ (v̲a̲l̲-mono-metric RHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) csn) ) ≤ᴹ proj₁ (lookup-mono-metric (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) csn)) (a1 csn) (T≤ᴹS csn)
              T≤ᴹS'' csn = subst (λ x → m-× 1 ((proj₁ (proj₂ (v̲a̲l̲-mono-metric (wk-v̲a̲l̲ π₁ LHS) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) csn)) x ≤ᴹ proj₁ (proj₂ (lookup-mono-metric (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) csn) (a2 csn) (T≤ᴹS' csn) --subst (λ x → m-× 1 ((proj₁ (v̲a̲l̲-mono-metric (wk-v̲a̲l̲ π₁ LHS) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) csn)) x ≤ᴹ proj₁ (lookup-mono-metric (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) csn) (a2 csn) (T≤ᴹS' csn)
              cntlhs : (proj₁ (v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁)))) ≡ (proj₁ (v̲a̲l̲-mono-metric (wk-v̲a̲l̲ π₁ LHS) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))))
              cntlhs = (v̲a̲l̲-wke-lemma-p1 LHS (proj₁ (env-mono-metric γ)) (proj₁ (env-mono-metric γ₁)) π₁ θ)
              cntlhs' :   v̲c̲o̲u̲n̲t̲ (wk-v̲a̲l̲ π₁ LHS) (elist-to-clist (proj₁ (env-mono-metric γ))) (wkn-to-wkc (proj₂ (env-mono-metric γ)))
                       ≡ v̲c̲o̲u̲n̲t̲ LHS (elist-to-clist (proj₁ (env-mono-metric γ₁))) (wkn-to-wkc (proj₂ (env-mono-metric γ₁)))
              cntlhs' = trans (v̲c̲o̲u̲n̲t̲-eq (wk-v̲a̲l̲ π₁ LHS) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) (trans (sym cntlhs) (sym (v̲c̲o̲u̲n̲t̲-eq LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁)))))
              cntrhs : (proj₁ (v̲a̲l̲-mono-metric RHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁)))) ≡ (proj₁ (v̲a̲l̲-mono-metric (wk-v̲a̲l̲ π₁ RHS) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))))
              cntrhs = (v̲a̲l̲-wke-lemma-p1 RHS (proj₁ (env-mono-metric γ)) (proj₁ (env-mono-metric γ₁)) π₁ θ)
              cntrhs' :   v̲c̲o̲u̲n̲t̲ (wk-v̲a̲l̲ π₁ RHS) (elist-to-clist (proj₁ (env-mono-metric γ))) (wkn-to-wkc (proj₂ (env-mono-metric γ)))
                       ≡ v̲c̲o̲u̲n̲t̲ RHS (elist-to-clist (proj₁ (env-mono-metric γ₁))) (wkn-to-wkc (proj₂ (env-mono-metric γ₁)))
              cntrhs' = trans (v̲c̲o̲u̲n̲t̲-eq (wk-v̲a̲l̲ π₁ RHS) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) (trans (sym cntrhs) (sym (v̲c̲o̲u̲n̲t̲-eq RHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁)))))
              cntlhs'' :   v̲c̲o̲u̲n̲t̲ (wk-v̲a̲l̲ π₁ LHS) (elist-to-clist (proj₁ (env-mono-metric γ))) (wkn-to-wkc (proj₂ (env-mono-metric γ)))
                       ≤ v̲c̲o̲u̲n̲t̲ LHS (elist-to-clist (proj₁ (env-mono-metric γ₁))) (wkn-to-wkc (proj₂ (env-mono-metric γ₁)))
              cntlhs'' = eq-to-ineq cntlhs'
              cntrhs'' :   v̲c̲o̲u̲n̲t̲ (wk-v̲a̲l̲ π₁ RHS) (elist-to-clist (proj₁ (env-mono-metric γ))) (wkn-to-wkc (proj₂ (env-mono-metric γ)))
                         ≤ v̲c̲o̲u̲n̲t̲ RHS (elist-to-clist (proj₁ (env-mono-metric γ₁))) (wkn-to-wkc (proj₂ (env-mono-metric γ₁)))
              cntrhs'' = eq-to-ineq cntrhs'
              lkeq : proj₁ (lookup-mono-metric (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) ≤ lcount (wk-mem π i) (elist-to-clist (proj₁ (env-mono-metric γ))) (wkn-to-wkc (proj₂ (env-mono-metric γ)))
              lkeq = eq-to-ineq (sym (lcount-lm-eq (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))))
            in

            steps

            (_ →ᵛ⟨ ∘var i>>T π₁ ⟩．)

            (∙ pa̲i̲r̲ (wk-v̲a̲l̲ π₁ LHS) (wk-v̲a̲l̲ π₁ RHS) ⊲ γ ■)

            (⟦ wk-mem π i ⟧ᵐ ⟦ γ ⟧ᴱ
            ≡⟨ i≡T ⟩
            (< ⟦ toVal LHS ⟧ᵛ , ⟦ toVal RHS ⟧ᵛ > ⟦ γ₁ ⟧ᴱ)
            ≡⟨ cong (λ x → < ⟦ toVal LHS ⟧ᵛ , ⟦ toVal RHS ⟧ᵛ > x) (sym w≡γ) ⟩
            (< ⟦ toVal LHS ⟧ᵛ , ⟦ toVal RHS ⟧ᵛ > (⟦ π₁ ⟧ʷ ⟦ γ ⟧ᴱ))
            ≡⟨ refl ⟩
            (⟦ wk-val π₁ (toVal LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ wk-val π₁ (toVal RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)
            ≡⟨ cong (λ x → (⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ wk-val π₁ (toVal RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)) (wk-comm {M = LHS} {π = π₁}) ⟩
            (⟦ toVal (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ wk-val π₁ (toVal RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)
            ≡⟨ cong (λ x → (⟦ toVal (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ)) (wk-comm {M = RHS} {π = π₁}) ⟩
            (⟦ toVal (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ toVal (wk-v̲a̲l̲ π₁ RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)
            ≡⟨ refl ⟩
            (< ⟦ toVal (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ , ⟦ toVal (wk-v̲a̲l̲ π₁ RHS) ⟧ᵛ > ⟦ γ ⟧ᴱ) ∎)

            wk-id

            refl

            (≤-trans (+-≤-cong cntlhs'' cntrhs'') (≤-trans cnt₁≤cnt₂ lkeq))

            (λ csn → ≤ᴹ-trans (T≤ᴹS'' csn) (≤ᴹ-incr-cong (z≤n {n = 2}) (≤ᴹ-refl {nm = (proj₁ (proj₂ (lookup-mono-metric (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) csn)}))) -- ((λ csn → ≤ᴹ-trans (T≤ᴹS'' csn) (≤ᴹ-incr-cong (z≤n {n = 2}) (≤ᴹ-refl {nm = {!!} {- proj₁ (lookup-mono-metric (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) csn -} }))))

            wke-id

  val-eval-rec {X = X `⇒ X₁} (var {A = .(X `⇒ X₁)} i) γ π with lookup (wk-mem π i) γ

  ... | steps i>>T (found-lam {W = W} {γ = γ₁}) i≡T π₁ w≡γ cnt₁≤cnt₂ T≤ᴹS θ =

            let
            --   a1 = {!!} --wke-comp-count-lemma h W (proj₁ (env-mono-metric γ)) (proj₁ (env-mono-metric γ₁)) (wk-cong π₁) (wkn-cons (proj₂ (env-mono-metric γ))) (wkn-cons (proj₂ (env-mono-metric γ₁))) (wke-cww π₁ (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric γ₁)) θ)
              a2 = comp-wke-lemma-p1p2 W (proj₁ (env-mono-metric γ)) (proj₁ (env-mono-metric γ₁)) (wk-cong π₁) (wkn-cons (proj₂ (env-mono-metric γ))) (wkn-cons (proj₂ (env-mono-metric γ₁))) (wke-cww π₁ (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric γ₁)) θ)
            --   T≤ᴹS'  csn = {!!} --subst (λ x → m-⇒ 1 x (proj₁ (comp-mono-metric W (proj₁ (env-mono-metric γ₁)) (wkn-cons (proj₂ (env-mono-metric γ₁)))) csn) ≤ᴹ proj₁ (lookup-mono-metric (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) csn) (a1 csn) (T≤ᴹS csn)
            --   T≤ᴹS'' csn = {!!} --subst (λ x → m-⇒ 1 (proj₁ (mono-comp-count h (wk-comp (wk-cong π₁) W) (proj₁ (env-mono-metric γ)) (wkn-cons (proj₂ (env-mono-metric γ)))) csn) x ≤ᴹ proj₁ (lookup-mono-metric (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) csn) (a2 csn) (T≤ᴹS' csn)

              T≤ᴹS''' csn = subst (λ x → m-⇒ 1 x ≤ᴹ proj₁ (proj₂ (lookup-mono-metric (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) csn) (a2 csn) (T≤ᴹS csn)

            in

            steps

            (_ →ᵛ⟨ ∘var i>>T π₁ ⟩．)

            (∙ (wk-v̲a̲l̲ π₁ (l̲a̲m̲ W)) ⊲ γ ■)

            (⟦ wk-mem π i ⟧ᵐ ⟦ γ ⟧ᴱ
              ≡⟨ i≡T ⟩
            ((λ y → ⟦ W ⟧ᶜ (⟦ γ₁ ⟧ᴱ , y) ))
              ≡⟨ cong (λ x → (λ y → ⟦ W ⟧ᶜ (x , y) )) (sym w≡γ) ⟩
            (λ y → ⟦ W ⟧ᶜ (⟦ π₁ ⟧ʷ ⟦ γ ⟧ᴱ , y) )
              ≡⟨ refl ⟩
            (curry (< (λ r → proj₁ r) ； ⟦ π₁ ⟧ʷ , (λ r → proj₂ r) > ； ⟦ W ⟧ᶜ)) ⟦ γ ⟧ᴱ ∎)

            wk-id

            refl

            (≤-trans (eq-to-ineq eq2) (≤-trans cnt₁≤cnt₂ (eq-to-ineq (sym (lcount-lm-eq (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))))))

            (λ csn → ≤ᴹ-trans (T≤ᴹS''' csn) (≤ᴹ-incr-cong (z≤n {n = 2}) (≤ᴹ-refl {nm = (proj₁ (proj₂ (lookup-mono-metric (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) csn) }))) -- ((λ csn → ≤ᴹ-trans (T≤ᴹS'' csn) (≤ᴹ-incr-cong (z≤n {n = 2}) (≤ᴹ-refl {nm = {!!} {- (proj₁ (lookup-mono-metric (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) csn) -} }))))

            wke-id

            where
              eq0 :   ccount (wk-comp (wk-cong π₁) W) (elist-to-clist (proj₁ (env-mono-metric γ))) (wkc-cons {Y = X} (wkn-to-wkc (proj₂ (env-mono-metric γ))))
                    ≡ proj₁ (comp-mono-metric (wk-comp (wk-cong π₁) W) (proj₁ (env-mono-metric γ)) (wkn-cons (proj₂ (env-mono-metric γ))))
              eq0 rewrite ((wkc-cons-comm {Y = X} (proj₂ (env-mono-metric γ)))) = (ccount-eq (wk-comp (wk-cong π₁) W) (proj₁ (env-mono-metric γ)) (wkn-cons (proj₂ (env-mono-metric γ))))
              eq1 :   ccount W (elist-to-clist (proj₁ (env-mono-metric γ₁))) (wkc-cons {Y = X} (wkn-to-wkc (proj₂ (env-mono-metric γ₁))))
                    ≡ proj₁ (comp-mono-metric W (proj₁ (env-mono-metric γ₁)) (wkn-cons (proj₂ (env-mono-metric γ₁))))
              eq1 rewrite ((wkc-cons-comm {Y = X} (proj₂ (env-mono-metric γ₁)))) = (ccount-eq W (proj₁ (env-mono-metric γ₁)) (wkn-cons (proj₂ (env-mono-metric γ₁))))
              eq2 :  ccount (wk-comp (wk-cong π₁) W) (elist-to-clist (proj₁ (env-mono-metric γ))) (wkc-cons (wkn-to-wkc (proj₂ (env-mono-metric γ))))
                     ≡ ccount W (elist-to-clist (proj₁ (env-mono-metric γ₁))) (wkc-cons (wkn-to-wkc (proj₂ (env-mono-metric γ₁))))
              eq2 = trans eq0 (trans (sym (comp-wke-lemma-p1 W (proj₁ (env-mono-metric γ)) (proj₁ (env-mono-metric γ₁)) (wk-cong π₁) (wke-cww π₁ (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric γ₁)) θ))) (sym eq1))

  val-eval-rec (lam W) γ π = steps (∘ ⇡ (wk-val π (lam W)) ⊲ γ ∷ □ →ᵛ⟨ ∘lam ⟩．) (∙ l̲a̲m̲ (wk-comp (wk-cong π) W) ⊲ γ ■) refl wk-id refl (eq-to-ineq refl) (λ csn → ≤ᴹ-incr-cong (z≤n {n = 1}) (≤ᴹ-refl {nm = m-⇒ 1 (proj₁ (proj₂ (comp-mono-metric (wk-comp (wk-cong π) W) (proj₁ (env-mono-metric γ)) (wkn-cons (proj₂ (env-mono-metric γ))))) csn)})) {- ((λ csn → ≤ᴹ-incr-cong (z≤n {n = 1}) (≤ᴹ-refl {nm = m-⇒ 1 (proj₁ (mono-comp-count h (wk-comp (wk-cong π) W) (proj₁ (env-mono-metric γ)) (wkn-cons (proj₂ (env-mono-metric γ)))) csn) (proj₁ (comp-mono-metric (wk-comp (wk-cong π) W) (proj₁ (env-mono-metric γ)) (wkn-cons (proj₂ (env-mono-metric γ)))) csn)}))) -} wke-id

  -- OLD: (λ csn → ≤ᴹ-incr-cong (z≤n {n = 1}) (≤ᴹ-refl {nm = m-⇒ 1 (count-in-comp h (wk-comp (wk-cong π) W) (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) csn) (comp-metric (wk-comp (wk-cong π) W) (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) csn)})) wke-id

  val-eval-rec unit γ π = steps (_ →ᵛ⟨ ∘unit ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id refl z≤n (λ csn → ≤ᴹ-incr-cong (z≤n {n = 1}) (≤ᴹ-refl {nm = m-Unit 1})) {- ((λ csn → ≤ᴹ-incr-cong (z≤n {n = 1}) (≤ᴹ-refl {nm = m-Unit 1}))) -} wke-id
  -- OLD: (λ csn → ≤ᴹ-incr-cong (z≤n {n = 1}) (≤ᴹ-refl {nm = m-Unit 1})) wke-id

  val-eval-rec (pair {A = X} {B = Y} LHS RHS) γ π with val-eval-rec {X = X} LHS γ π
  ... | steps {T = ∙ (⭭_ {X = X} LT ⊲ γ₁ ∷ □) {↥ = 🗆}} L>T ∙LT L≡T πᴸ wk≡ᴸ cnt₁≤cnt₂ T≤ᴹS θ with  val-eval-rec {X = Y} RHS γ₁ (wk-trans πᴸ π)
  ...      | steps {T = ∙ (⭭_ {X = Y} RT ⊲ γ₂ ∷ □) {↥ = 🗆}} R>T ∙RT R≡T πᴿ wk≡ᴿ cnt₁≤cnt₂' T≤ᴹS' θ' rewrite sym (wk-val-trans RHS πᴸ π) =

            let
              a1     csn = v̲a̲l̲-wke-lemma-p1p2 LT (proj₁ (env-mono-metric γ₂)) (proj₁ (env-mono-metric γ₁)) πᴿ (proj₂ (env-mono-metric γ₂)) (proj₂ (env-mono-metric γ₁)) θ' csn
              a2     csn = sym (val-wke-lemma-p1p2 (wk-val π RHS) (proj₁ (env-mono-metric γ₁)) (proj₁ (env-mono-metric γ)) πᴸ (proj₂ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ)) θ csn)
              T≤ᴹS₁  csn = subst (λ x → x ≤ᴹ proj₁ (proj₂ (val-mono-metric (wk-val π LHS) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) csn) (a1 csn) (T≤ᴹS csn)
              T≤ᴹS'₁ csn = subst (λ x → proj₁ (proj₂ (v̲a̲l̲-mono-metric RT (proj₁ (env-mono-metric γ₂)) (proj₂ (env-mono-metric γ₂)))) csn ≤ᴹ x) (a2 csn) (T≤ᴹS' csn)
              b1         = v̲a̲l̲-wke-lemma-p1 LT (proj₁ (env-mono-metric γ₂)) (proj₁ (env-mono-metric γ₁)) πᴿ θ'
              b2         = val-wke-lemma-p1 (wk-val π RHS) (proj₁ (env-mono-metric γ₁)) (proj₁ (env-mono-metric γ)) πᴸ θ
              c1         = ≤-trans (eq-to-ineq (sym b1)) cnt₁≤cnt₂
              c2         = ≤-trans cnt₁≤cnt₂' (eq-to-ineq (sym b2))
            in

            steps

              (
              ∘ ⇡ (wk-val π (pair LHS RHS)) ⊲ γ ∷ □ →ᵛ⟨ ∘pair ⟩． ⨾ -- (∘ ⇡ wk-val π LHS ⊲ γ ∷ ⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⊲ γ ∷ □)
              (⟪ L>T ⟫⧻ (⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⊲ γ ∷ □)) ⨾
              (∙ ⭭ LT ⊲ γ₁ ∷ ⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⊲ γ ∷ □) →ᵛ⟨ ∙M∷l ⟩． ⨾ -- (∘ ⇡ wk-val _π'_3203 (wk-val π RHS) ⊲ γ₁ ∷ ⇡ᴿ LT (wk-val _π'_3203 (wk-val π RHS)) ⊲ γ₁ ∷ □)
              (⟪ R>T ⟫⧻ (⇡ᴿ LT (wk-val πᴸ (wk-val π RHS)) ⊲ γ₁ ∷ □)) ⨾
              (∙ ⭭ RT ⊲ γ₂ ∷ ⇡ᴿ LT (wk-val πᴸ (wk-val π RHS)) ⊲ γ₁ ∷ □) →ᵛ⟨ ∙M∷r ⟩．
              )

              ∙ pa̲i̲r̲ (wk-v̲a̲l̲ πᴿ LT) RT ⊲ γ₂ ■

              ( ⟦ wk-val π (pair LHS RHS) ⟧ᵛ ⟦ γ ⟧ᴱ
              ≡⟨ refl ⟩
                (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))
              ≡⟨ cong (λ y → (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ y))) (sym wk≡ᴸ) ⟩
                (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ (⟦ πᴸ ⟧ʷ ⟦ γ₁ ⟧ᴱ)))
              ≡⟨ cong (λ y → (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ y)) (wk-sem-trans πᴸ π ⟦ γ₁ ⟧ᴱ) ⟩
                (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
              ≡⟨ cong (λ y → (y , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))) L≡T ⟩
                (⟦ toVal LT ⟧ᵛ ⟦ γ₁ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
              ≡⟨ cong (λ y → (⟦ toVal LT ⟧ᵛ y , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))) (sym wk≡ᴿ) ⟩
                (⟦ toVal LT ⟧ᵛ (⟦ πᴿ ⟧ʷ ⟦ γ₂ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
              ≡⟨ refl ⟩
                (⟦ wk-val πᴿ (toVal LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
              ≡⟨ cong (λ y → (⟦ y ⟧ᵛ ⟦ γ₂ ⟧ᴱ  , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))) (wk-comm {M = LT} {π = πᴿ}) ⟩
                (⟦ toVal (wk-v̲a̲l̲ πᴿ LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
              ≡⟨ cong (λ y → (⟦ toVal (wk-v̲a̲l̲ πᴿ LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , y)) R≡T ⟩
                (⟦ toVal (wk-v̲a̲l̲ πᴿ LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , ⟦ toVal RT ⟧ᵛ ⟦ γ₂ ⟧ᴱ)
              ≡⟨ refl ⟩
                ⟦ pair (toVal (wk-v̲a̲l̲ πᴿ LT)) (toVal RT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ
              ≡⟨ refl ⟩
                ⟦ toVal (pa̲i̲r̲ (wk-v̲a̲l̲ πᴿ LT) RT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ
              ≡⟨ refl ⟩
                ⟦ ∙ (⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πᴿ LT) RT ⊲ γ₂ ∷ □) {↥ = 🗆} ⟧ᵛꟴ ∎ )

              (wk-trans πᴿ πᴸ)

              ( ⟦ wk-trans πᴿ πᴸ ⟧ʷ ⟦ γ₂ ⟧ᴱ
              ≡⟨ sym (wk-sem-trans πᴿ πᴸ ⟦ γ₂ ⟧ᴱ) ⟩
                ⟦ πᴸ ⟧ʷ (⟦ πᴿ ⟧ʷ ⟦ γ₂ ⟧ᴱ)
              ≡⟨ cong (λ y → ⟦ πᴸ ⟧ʷ y) wk≡ᴿ ⟩
                ⟦ πᴸ ⟧ʷ ⟦ γ₁ ⟧ᴱ
              ≡⟨ wk≡ᴸ ⟩
                ⟦ γ ⟧ᴱ ∎)

              (+-≤-cong c1 c2)

              (λ csn → ≤-× (s≤s (z≤n {n = 1})) (T≤ᴹS₁ csn) (T≤ᴹS'₁ csn)) -- ((λ csn → ≤-× (s≤s (z≤n {n = 1})) (T≤ᴹS₁ csn) (T≤ᴹS'₁ csn)))

              (wke-trans θ' θ)

  val-eval-rec {Γ = Γ} (pm {A = A} {B = B} M N) γ π with val-eval-rec M γ π
  ... | steps {S = S} M>T ∙ pa̲i̲r̲ LHS RHS ⊲ γ₁ ■ M≡T π₁ wk≡₁ cnt₁≤cnt₂ T≤ᴹS θ with val-eval-rec N (_﹐_ (_﹐_ γ₁ LHS) (wk-v̲a̲l̲ (wk-wk wk-id) RHS)) ((wk-cong (wk-cong (wk-trans π₁ π)))) | (wk-val-trans N (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π)))
  ...    | steps {T = T} N>T ∙T N≡T π₂ wk≡₂ cnt₁≤cnt₂' T≤ᴹS' θ' | eq with N>T
  ...      | N>T' rewrite sym eq =

        let
          L≤ᴹl csn = LHS≤ᴹlhs (T≤ᴹS csn)
          R≤ᴹr csn = RHS≤ᴹrhs (T≤ᴹS csn)
          r≡      : (csn : List (ℕ × ℕ)) → proj₁ (proj₂ (v̲a̲l̲-mono-metric RHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁)))) csn ≡ proj₁ (proj₂ (v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁)) (wkn-cong (proj₂ (env-mono-metric γ₁))))) csn
          r≡ csn = v̲a̲l̲-wke-lemma-p1p2 RHS ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁)) (proj₁ (env-mono-metric γ₁)) (wk-wk wk-id) (wkn-cong (proj₂ (env-mono-metric γ₁))) (proj₂ (env-mono-metric γ₁)) (wke-wc- wk-id (proj₂ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁)) (v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) wke-id) csn
          R≤ᴹr' csn  = subst (λ x → x ≤ᴹ rhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) csn)) (r≡ csn) (R≤ᴹr csn)
          ϖ₁ : WkN (Γ ∙ A ∙ B) ((B , v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁)) (wkn-cong (proj₂ (env-mono-metric γ₁)))) ∷ (A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ))
          ϖ₁ = (wkn-cong {e = v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁)) (wkn-cong (proj₂ (env-mono-metric γ₁)))} (wkn-cong {e = v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))} (proj₂ (env-mono-metric γ))))
          ϖ₂ : WkN (Γ ∙ A ∙ B) (((B , proj₁ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c≤c'))) ∷ (A , proj₁ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c≤c'))) ∷ proj₁ (env-mono-metric γ)))
          ϖ₂ = wkn-cong {e = proj₁ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c≤c'))} (wkn-cong {e = proj₁ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c≤c'))} (proj₂ (env-mono-metric γ)))

          le1 :   proj₁ (v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁)))
                ≤ proj₁ (v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) + proj₁ (v̲a̲l̲-mono-metric RHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁)))
          le1 = n≤n+m {n = proj₁ (v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁)))}
          le2 :   proj₁ (v̲a̲l̲-mono-metric RHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁)))
                 ≤ proj₁ (v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) + proj₁ (v̲a̲l̲-mono-metric RHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁)))
          le2 = n≤m+n {n = proj₁ (v̲a̲l̲-mono-metric RHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁)))}
          le3 = eq-to-ineq (sym (v̲a̲l̲-wke-lemma-p1 RHS (((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁))) (proj₁ (env-mono-metric γ₁)) ((wk-wk wk-id)) {ϖ = wkn-cong (proj₂ (env-mono-metric γ₁))} {ϖ' = proj₂ (env-mono-metric γ₁)} (wke-wc- wk-id (proj₂ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁)) (v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) wke-id)))
          ϕ : WkZ ϖ₁ ϖ₂
          ϕ = wkz-cong (≤-trans le3 (≤-trans le2 cnt₁≤cnt₂)) R≤ᴹr' (wkz-cong (≤-trans le1 cnt₁≤cnt₂) L≤ᴹl wkz-id) --wkz-cong R≤ᴹr' (wkz-cong L≤ᴹl ?)

          a1 csn = val-wkz-lemma
                              (wk-val (wk-cong (wk-cong π)) N)
                              ((B , v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁)) (wkn-cong (proj₂ (env-mono-metric γ₁)))) ∷ (A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ))
                              ((B , proj₁ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c≤c'))) ∷ (A , proj₁ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c≤c'))) ∷ proj₁ (env-mono-metric γ))
                              ϖ₁ ϖ₂ ϕ csn

          a1-cnt = val-proj₁-lemma
                              (wk-val (wk-cong (wk-cong π)) N)
                              ((B , v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁)) (wkn-cong (proj₂ (env-mono-metric γ₁)))) ∷ (A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ))
                              ((B , proj₁ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c≤c'))) ∷ (A , proj₁ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c≤c'))) ∷ proj₁ (env-mono-metric γ))
                              ϖ₁ ϖ₂ (wkz-to-wkcz ϕ)

          a2 csn = val-wke-lemma-p1p2
                           (wk-val (wk-cong (wk-cong π)) N)
                           ((B , v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁)) (wkn-cong (proj₂ (env-mono-metric γ₁)))) ∷ ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁)))
                           ((B , v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁)) (wkn-cong (proj₂ (env-mono-metric γ₁)))) ∷ ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ)))
                           (wk-cong (wk-cong π₁))
                           (wkn-cong (wkn-cong (proj₂ (env-mono-metric γ₁))))
                           ((wkn-cong (wkn-cong (proj₂ (env-mono-metric γ)))))
                           (wke-ccc (wk-cong π₁) (wkn-cong (proj₂ (env-mono-metric γ₁))) (wkn-cong (proj₂ (env-mono-metric γ)))
                             (v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁)) (wkn-cong (proj₂ (env-mono-metric γ₁))))
                             (wke-ccc π₁ (proj₂ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ))
                               (v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁)))
                               θ))
                           csn

          a2-cnt = val-wke-lemma-p1
                           (wk-val (wk-cong (wk-cong π)) N)
                           ((B , v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁)) (wkn-cong (proj₂ (env-mono-metric γ₁)))) ∷ ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁)))
                           ((B , v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁)) (wkn-cong (proj₂ (env-mono-metric γ₁)))) ∷ ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ)))
                           (wk-cong (wk-cong π₁))
                           {ϖ = (wkn-cong (wkn-cong (proj₂ (env-mono-metric γ₁))))}
                           {ϖ' = ((wkn-cong (wkn-cong (proj₂ (env-mono-metric γ)))))}
                           (wke-ccc (wk-cong π₁) (wkn-cong (proj₂ (env-mono-metric γ₁))) (wkn-cong (proj₂ (env-mono-metric γ)))
                             (v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁)) (wkn-cong (proj₂ (env-mono-metric γ₁))))
                             (wke-ccc π₁ (proj₂ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ))
                               (v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁)))
                               θ))

          a3 csn = subst (λ x → x ≤ᴹ (proj₁ (proj₂ (val-mono-metric (wk-val (wk-cong (wk-cong π)) N) ((B , proj₁ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c≤c'))) ∷ (A , proj₁ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c≤c'))) ∷ proj₁ (env-mono-metric γ)) ϖ₂)) csn)) (a2 csn) (a1 csn)
          T≤ᴹS'' csn = ≤ᴹ-trans (T≤ᴹS' csn) (a3 csn)

          a3-cnt = subst (λ x → x ≤ proj₁ (val-mono-metric (wk-val (wk-cong (wk-cong π)) N) ((B , proj₁ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c≤c'))) ∷ (A , proj₁ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c≤c'))) ∷ proj₁ (env-mono-metric γ)) ϖ₂)) (a2-cnt) (a1-cnt)
          veq = sym (vcount-eq (wk-val (wk-cong (wk-cong π)) N) (((B , proj₁ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) , (λ c → rhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c)) , (λ c≤c' → ≤ᴹ-rhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c≤c'))) ∷ (A , proj₁ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) , (λ c → lhs (proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c)) , (λ c≤c' → ≤ᴹ-lhs (proj₂ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) c≤c'))) ∷ proj₁ (env-mono-metric γ))) ϖ₂)
          a3-cnt' = subst (λ x → proj₁ (val-mono-metric (wk-val (wk-cong (wk-cong π₁)) (wk-val (wk-cong (wk-cong π)) N)) ((B , v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁)) (wkn-cong (proj₂ (env-mono-metric γ₁)))) ∷ (A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁)) (wkn-cong (wkn-cong (proj₂ (env-mono-metric γ₁))))) ≤ x) veq a3-cnt
          cnt₁≤cnt₂'' = ≤-trans cnt₁≤cnt₂' a3-cnt'

{-

Goal: proj₁ (valstate-metric T) ≤
      vcount
        (wk-val (wk-cong (wk-cong π)) N)
        (proj₁ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) ∷ proj₁ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) ∷ elist-to-clist (proj₁ (env-mono-metric γ)))
        (wkc-cong (wkc-cong (wkn-to-wkc (proj₂ (env-mono-metric γ)))))

cnt₁≤cnt₂ : proj₁
            (v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁))
             (proj₂ (env-mono-metric γ₁)))
            +
            proj₁
            (v̲a̲l̲-mono-metric RHS (proj₁ (env-mono-metric γ₁))
             (proj₂ (env-mono-metric γ₁)))
            ≤
            proj₁
            (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ))
             (proj₂ (env-mono-metric γ)))

cnt₁≤cnt₂'
          : proj₁ (valstate-metric T) ≤
            proj₁
            (val-mono-metric
             (wk-val (wk-cong (wk-cong π₁)) (wk-val (wk-cong (wk-cong π)) N))
             ((B ,
               v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS)
               ((A ,
                 v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁))
                 (proj₂ (env-mono-metric γ₁)))
                ∷ proj₁ (env-mono-metric γ₁))
               (wkn-cong (proj₂ (env-mono-metric γ₁))))
              ∷
              (A ,
               v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁))
               (proj₂ (env-mono-metric γ₁)))
              ∷ proj₁ (env-mono-metric γ₁))
             (wkn-cong (wkn-cong (proj₂ (env-mono-metric γ₁)))))

a2-cnt    : proj₁
            (val-mono-metric (wk-val (wk-cong (wk-cong π)) N)
             (  (B , v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁)) (wkn-cong (proj₂ (env-mono-metric γ₁))))
              ∷ (A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ))
              ϖ₁)
            ≡
            proj₁
            (val-mono-metric
             (wk-val (wk-cong (wk-cong π₁)) (wk-val (wk-cong (wk-cong π)) N))
             (  (B , v̲a̲l̲-mono-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁)) (wkn-cong (proj₂ (env-mono-metric γ₁))))
              ∷ (A , v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) ∷ proj₁ (env-mono-metric γ₁))
              (wkn-cong (wkn-cong (proj₂ (env-mono-metric γ₁)))))
-}

        in

        steps
          (
            (∘ ⇡ pm (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⊲ γ ∷ □) →ᵛ⟨ ∘pm ⟩． ⨾ -- (∘ ⇡ wk-val π M ⊲ γ ∷ ⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⊲ γ ∷ □)
            (⟪ M>T ⟫⧻ (⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⊲ γ ∷ □)) ⨾
            (∙ ⭭ pa̲i̲r̲ LHS RHS ⊲ γ₁ ∷ ⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⊲ γ ∷ □) →ᵛ⟨ ∙pair∷pm ⟩． ⨾ -- (∘ ⇡ wk-val (wk-cong (wk-cong π₁)) (wk-val (wk-cong (wk-cong π)) N) ⊲ _﹐_ (_﹐_ γ₁ LHS) (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ∷ □)
            N>T'
          )

          ∙T

          (  ⟦ wk-val π (pm M N) ⟧ᵛ ⟦ γ ⟧ᴱ
            ≡⟨ refl ⟩
              ⟦ pm (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⟧ᵛ ⟦ γ ⟧ᴱ
            ≡⟨ refl ⟩
            (< idf , ⟦ π ⟧ʷ ； ⟦ M ⟧ᵛ > ； assocl ； ⟦ wk-val (wk-cong (wk-cong π)) N ⟧ᵛ) ⟦ γ ⟧ᴱ
            ≡⟨ refl ⟩
            ⟦ wk-val (wk-cong (wk-cong π)) N ⟧ᵛ (assocl ( (⟦ γ ⟧ᴱ ,  ⟦ M ⟧ᵛ  (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))))
            ≡⟨ cong (λ y → ⟦ wk-val (wk-cong (wk-cong π)) N ⟧ᵛ (assocl ( (⟦ γ ⟧ᴱ , y   )))) M≡T ⟩
            ⟦ wk-val (wk-cong (wk-cong π)) N ⟧ᵛ (assocl ( (⟦ γ ⟧ᴱ ,  (⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)  )))
            ≡⟨ refl ⟩
              ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
            ≡⟨ cong  (λ y → ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ y , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)) (sym wk≡₁) ⟩
              ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
            ≡⟨ refl ⟩
              ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ (wk-val (wk-wk wk-id) (toVal RHS)) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
            ≡⟨ cong (λ y → ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ y ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))) (wk-comm {M = RHS} {π = wk-wk wk-id}) ⟩
              ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
            ≡⟨ cong (λ y → ⟦ N ⟧ᵛ ((y , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))  ) (wk-sem-trans π₁ π ⟦ γ₁ ⟧ᴱ) ⟩
            ⟦ N ⟧ᵛ ((⟦ wk-trans π₁ π ⟧ʷ ⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
            ≡⟨ N≡T ⟩
            ⟦ T ⟧ᵛꟴ ∎)

          (wk-trans π₂ (wk-wk (wk-wk π₁)))

          ( ⟦ wk-trans π₂ (wk-wk (wk-wk π₁)) ⟧ʷ ⟦ botEnv T ⟧ᴱ
            ≡⟨ sym (wk-sem-trans π₂ (wk-wk (wk-wk π₁)) ⟦ botEnv T ⟧ᴱ) ⟩
            ⟦ wk-wk (wk-wk π₁) ⟧ʷ (⟦ π₂ ⟧ʷ ⟦ botEnv T ⟧ᴱ)
            ≡⟨ cong (λ y → ⟦ wk-wk (wk-wk π₁) ⟧ʷ y) wk≡₂ ⟩
            ⟦ wk-wk (wk-wk π₁) ⟧ʷ (((⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))
            ≡⟨ refl ⟩
            ⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ
            ≡⟨ wk≡₁ ⟩
            ⟦ γ ⟧ᴱ ∎)

          cnt₁≤cnt₂''

          (λ csn → ≤ᴹ-incr-cong (z≤n {n = suc (vx (proj₁ (proj₂ (val-mono-metric (wk-val π M) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ)))) csn) + ⟪ proj₁ (proj₂ (val-mono-metric (wk-val (wk-cong (wk-cong π)) N) (proj₁ (env-mono-metric γ)) (wkn-cons (wkn-cons (proj₂ (env-mono-metric γ)))))) csn ⟫)}) (T≤ᴹS'' csn) )

          ((wke-trans θ' (wke-wc- (wk-wk π₁) (wkn-cong (proj₂ (env-mono-metric γ₁))) (proj₂ (env-mono-metric γ)) _ (wke-wc- π₁ (proj₂ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ)) (v̲a̲l̲-mono-metric LHS (proj₁ (env-mono-metric γ₁)) (proj₂ (env-mono-metric γ₁))) θ))))

{- BBBB

  val-eval : (M : ε ⊢ᵛ X) → ValSteps {T◾ = X} (∘ ((⇡ wk-val wk-id M ⊲ ∗ ∷ □) {↥ = 🗆}))
  val-eval M = val-eval-rec M ∗ wk-id

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

BBBB -}
