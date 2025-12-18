module Inception.Sub.ValueMachine (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Function.Base using (const)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Unit
open import Data.Nat
open import Data.List using (List; _∷_; []; _++_)

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

  data TermMetric : Ty → Set where
    m-Unit : (m : ℕ) → TermMetric `Unit
    m-V : (m : ℕ) → (w : ℕ) → (csn : List (ℕ × ℕ)) → TermMetric (`V)
    m-⇒ : (m : ℕ) → (cnt : ℕ) → (nm : TermMetric Y) → TermMetric (X `⇒ Y)
    m-×   : (m : ℕ) → (nm₁ : TermMetric X) → (nm₂ : TermMetric Y) → TermMetric (X `× Y)

  data Wkn : (Γ : Ctx) → (E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))) → Set where
    wkn-nil  : Wkn ε []
    wkn-cong :   {Γ : Ctx} → {ne : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))} → {Y : Ty}
               → {e : (List (ℕ × ℕ) → TermMetric Y)} → (ϖ : Wkn Γ ne) → Wkn (Γ ∙ Y) ((Y , e) ∷ ne)
    wkn-cons :   {Γ : Ctx} → {ne : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))}
               → {Y : Ty} → (ϖ : Wkn Γ ne) → Wkn (Γ ∙ Y) ne

  data _≤ᶜˢⁿ_ : List (ℕ × ℕ) → List (ℕ × ℕ) → Set where
   [c≤c] : {csn : List (ℕ × ℕ)} → csn ≤ᶜˢⁿ csn
   [s≤s] : {cnt : ℕ} {csn₁ csn₂ : List (ℕ × ℕ)} → n₁ ≤ n₂ → csn₁ ≤ᶜˢⁿ csn₂ → ((cnt , n₁) ∷ csn₁) ≤ᶜˢⁿ ((cnt , n₂) ∷ csn₂)

  ≤ᶜˢⁿ-trans : {csn₁ csn₂ csn₃ : List (ℕ × ℕ)} → csn₁ ≤ᶜˢⁿ csn₂ → csn₂ ≤ᶜˢⁿ csn₃ → csn₁ ≤ᶜˢⁿ csn₃
  ≤ᶜˢⁿ-trans [c≤c] [c≤c] = [c≤c]
  ≤ᶜˢⁿ-trans [c≤c] ([s≤s] x c₂≤c₃) = [s≤s] x c₂≤c₃
  ≤ᶜˢⁿ-trans ([s≤s] x c₁≤c₂) [c≤c] = [s≤s] x c₁≤c₂
  ≤ᶜˢⁿ-trans ([s≤s] x c₁≤c₂) ([s≤s] x₁ c₂≤c₃) = [s≤s] (≤-trans x x₁) (≤ᶜˢⁿ-trans c₁≤c₂ c₂≤c₃)

  data _≤ᴹ_ : TermMetric X → TermMetric X → Set where
    ≤-Unit : (n₁ ≤ n₂) → (m-Unit n₁) ≤ᴹ (m-Unit n₂)
    ≤-V    : {w₁ w₂ : ℕ} {csn₁ csn₂ : List (ℕ × ℕ)} → (m₁ ≤ m₂) → (w₁ ≤ w₂) → (csn₁ ≤ᶜˢⁿ csn₂) → (m-V m₁ w₁ csn₁) ≤ᴹ (m-V m₂ w₂ csn₂)
    ≤-⇒    : {cnt : ℕ} {nm₁ nm₂ : TermMetric Y} → (m₁ ≤ m₂) → (nm₁ ≤ᴹ nm₂) → (m-⇒ {X = X} m₁ cnt nm₁) ≤ᴹ (m-⇒ m₂ cnt nm₂)
    ≤-×    : {lhs₁ lhs₂ : TermMetric X} → {rhs₁ rhs₂ : TermMetric Y} → (n₁ ≤ n₂) → (lhs₁ ≤ᴹ lhs₂) → (rhs₁ ≤ᴹ rhs₂) → (m-× n₁ lhs₁ rhs₁) ≤ᴹ (m-× n₂ lhs₂ rhs₂)

  ≤ᴹ-refl : {nm : TermMetric X} → nm ≤ᴹ nm
  ≤ᴹ-refl {nm = m-Unit m} = ≤-Unit ≤-refl
  ≤ᴹ-refl {nm = m-V m n csn} = ≤-V  ≤-refl ≤-refl [c≤c]
  ≤ᴹ-refl {nm = m-⇒ m cnt nm} = ≤-⇒ ≤-refl ≤ᴹ-refl
  ≤ᴹ-refl {nm = m-× m nm nm₁} = ≤-× ≤-refl ≤ᴹ-refl ≤ᴹ-refl

  ≤ᴹ-trans : {nm₁ nm₂ nm₃ : TermMetric X} → nm₁ ≤ᴹ nm₂ → nm₂ ≤ᴹ nm₃ → nm₁ ≤ᴹ nm₃
  ≤ᴹ-trans (≤-Unit x) (≤-Unit x₁) = ≤-Unit (≤-trans x x₁)
  ≤ᴹ-trans (≤-V x x₁ x₂) (≤-V x₃ x₄ x₅) = ≤-V (≤-trans x x₃) (≤-trans x₁ x₄) (≤ᶜˢⁿ-trans x₂ x₅)
  ≤ᴹ-trans (≤-⇒ x nm₁≤nm₂) (≤-⇒ x₁ nm₂≤nm₃) = ≤-⇒ (≤-trans x x₁) (≤ᴹ-trans nm₁≤nm₂ nm₂≤nm₃)
  ≤ᴹ-trans (≤-× x nm₁≤nm₂ nm₁≤nm₃) (≤-× x₁ nm₂≤nm₃ nm₂≤nm₄) = ≤-× (≤-trans x x₁) (≤ᴹ-trans nm₁≤nm₂ nm₂≤nm₃) (≤ᴹ-trans nm₁≤nm₃ nm₂≤nm₄)

  zero-metric : TermMetric X
  zero-metric {X = `Unit} = m-Unit 0
  zero-metric {X = X `× Y} = m-× 0 (zero-metric {X = X}) (zero-metric {X = Y})
  zero-metric {X = X `⇒ Y} = m-⇒ 0 0 (zero-metric {X = Y})
  zero-metric {X = `V} = m-V 0 0 []

  lookup-metric : (i : Γ ∋ Y) → (E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))) → Wkn Γ E → (List (ℕ × ℕ) → TermMetric Y)
  lookup-metric Cx.h ((Y , e) ∷ ne) (wkn-cong ϖ) = e
  lookup-metric (Cx.t i) ((X , e) ∷ ne) (wkn-cong ϖ) = lookup-metric i ne ϖ
  lookup-metric {Y = Y} Cx.h [] (wkn-cons ϖ) = λ csn → zero-metric
  lookup-metric {Y = Y} Cx.h (x ∷ E) (wkn-cons ϖ) = λ csn → zero-metric
  lookup-metric {Y = Y} (Cx.t i) [] (wkn-cons ϖ) = λ csn → zero-metric
  lookup-metric (Cx.t i) (x ∷ E) (wkn-cons ϖ) = lookup-metric i (x ∷ E) ϖ

  --------------------------------------------------------------------


  mutual
    count-in-val : (i : Γ ∋ X) → (M : Val Γ Z) → ℕ

    count-in-val Cx.h (var Cx.h) = 1
    count-in-val Cx.h (var (Cx.t i)) = 0
    count-in-val (Cx.t i) (var Cx.h) = 0
    count-in-val (Cx.t i₁) (var (Cx.t i₂)) = count-in-val i₁ (var i₂)

    count-in-val Cx.h (lam W) = count-in-comp (t h) W
    count-in-val (Cx.t i) (lam W) = count-in-comp (t (t i)) W

    count-in-val Cx.h (pair M N) = count-in-val h M + count-in-val h N
    count-in-val (Cx.t i) (pair M N) = count-in-val (t i) M + count-in-val (t i) N

    count-in-val Cx.h (pm M N) = count-in-val h M + count-in-val (t (t h)) N
    count-in-val (Cx.t i) (pm M N) = count-in-val (t i) M + count-in-val (t (t (t i))) N

    count-in-val Cx.h unit = 0
    count-in-val (Cx.t i) unit = 0

    count-in-comp : (i : Γ ∋ X) → (W : Comp Γ Z) → ℕ
    count-in-comp i (return M) = count-in-val i M
    count-in-comp i (pm M W) = count-in-val i M + count-in-comp (t (t i)) W
    count-in-comp i (push W₁ W₂) = count-in-comp i W₁ + count-in-comp (t i) W₂
    count-in-comp i (app M N) = count-in-val i M + count-in-val i N
    count-in-comp i (var M) = count-in-val i M
    count-in-comp i (sub W₁ W₂) = count-in-comp (t i) W₁ + count-in-comp i W₂

  -------------------------------

  csn-to-nat₀ : ℕ → List (ℕ × ℕ) → ℕ
  csn-to-nat₀ w [] = 0
  csn-to-nat₀ w ((cnt , tm) ∷ csn) = (tm + (w * (suc cnt))) + (csn-to-nat₀ (tm + (w * (suc cnt))) csn)

  postulate csn-decr : (n₁ ≤ n₂) → (csn : List (ℕ × ℕ)) → csn-to-nat₀ n₁ csn ≤ csn-to-nat₀ n₂ csn
  -- csn-decr {n₁ = n₁} {n₂ = n₂} z≤n [] = ≤-refl
  -- csn-decr {n₁ = n₁} {n₂ = n₂} z≤n (x ∷ csn) = let le1 = +-≤-cong (≤-refl {n = proj₂ x}) z≤n in +-≤-cong le1 (csn-decr le1 csn)
  -- csn-decr {n₁ = n₁} {n₂ = n₂} (s≤s n₁≤n₂) [] = ≤-refl
  -- csn-decr {n₁ = n₁} {n₂ = n₂} (s≤s n₁≤n₂) (x ∷ csn) = {!!} --let le1 = +-≤-cong (≤-refl {n = proj₂ x}) (+-≤-cong (≤-refl {n = proj₁ x}) (*-≤-cong n₁≤n₂ (≤-refl {n = proj₁ x}))) in +-≤-cong le1 (csn-decr le1 csn)

  ⟪_⟫ : TermMetric X → ℕ
  ⟪ m-Unit m ⟫ = m
  ⟪ m-V m w csn ⟫ = m + w + csn-to-nat₀ w csn
  ⟪ m-⇒ m cnt nm ⟫ = m + ⟪ nm ⟫
  ⟪ m-× m nm₁ nm₂ ⟫ = m + ⟪ nm₁ ⟫ + ⟪ nm₂ ⟫

  incr : ℕ → TermMetric X → TermMetric X
  incr n (m-Unit m) = m-Unit (n + m)
  incr n (m-V m w csn) = m-V (n + m) w csn
  incr n (m-⇒ m cnt nm) = m-⇒ (n + m) cnt nm
  incr n (m-× m nm₁ nm₂) = m-× (n + m) nm₁ nm₂

  incr-coh : (n : ℕ) → (X : Ty) → (nm : TermMetric X) → ⟪ incr n nm ⟫ ≡ n + ⟪ nm ⟫
  incr-coh zero `Unit (m-Unit m) = refl
  incr-coh zero (X `× X₁) (m-× m nm nm₁) = refl
  incr-coh zero (X `⇒ X₁) (m-⇒ m cnt nm) = refl
  incr-coh zero `V (m-V m w csn) = refl
  incr-coh (suc n) `Unit (m-Unit m) = refl
  incr-coh (suc n) (X `× X₁) (m-× m nm nm₁) rewrite +-assoc {n} {m} {⟪ nm ⟫} | +-assoc {n} {m + ⟪ nm ⟫} {⟪ nm₁ ⟫} = refl
  incr-coh (suc n) (X `⇒ X₁) (m-⇒ m cnt nm) rewrite +-assoc {n} {m} {⟪ nm ⟫} = refl
  incr-coh (suc n) `V (m-V m w csn) rewrite +-assoc {n} {m} {w} | +-assoc {n} {m + w} {csn-to-nat₀ w csn} = refl

  {-# REWRITE incr-coh #-}

  incr-zero-coh : (X : Ty) → (nm : TermMetric X) → incr zero nm ≡ nm
  incr-zero-coh `Unit (m-Unit m) = refl
  incr-zero-coh (X `× X₁) (m-× m nm₁ nm₂) = refl
  incr-zero-coh (X `⇒ X₁) (m-⇒ m cnt nm) = refl
  incr-zero-coh `V (m-V m w csn) = refl

  {-# REWRITE incr-zero-coh #-}

  p1 : TermMetric (X `⇒ Y) → ℕ
  p1 (m-⇒ m cnt nm) = m

  p2 : TermMetric (X `⇒ Y) → ℕ
  p2 (m-⇒ m cnt nm) = cnt

  p3 : TermMetric (X `⇒ Y) → TermMetric Y
  p3 (m-⇒ m cnt nm) = nm

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

  ≤ᴹ-incr-drop : (n : ℕ) → (nm₁ nm₂ : TermMetric X) → ((incr n nm₁) ≤ᴹ (incr n nm₂)) → (nm₁ ≤ᴹ nm₂)
  ≤ᴹ-incr-drop {X = `Unit} n (m-Unit m₁) (m-Unit m₂) (≤-Unit n+m₁≤n+m₂) = ≤-Unit (+-≤-cong-rev-left n+m₁≤n+m₂)
  ≤ᴹ-incr-drop {X = X `× Y} n (m-× m₁ nm₁ nm₂) (m-× m₂ nm₃ nm₄) (≤-× n+m₁≤n+m₂ nm₁≤nm₃ nm₂≤nm₄) = ≤-× (+-≤-cong-rev-left n+m₁≤n+m₂) nm₁≤nm₃ nm₂≤nm₄
  ≤ᴹ-incr-drop {X = X `⇒ Y} n (m-⇒ m₁ cnt nm₁) (m-⇒ m₂ cnt nm₂) (≤-⇒ n+m₁≤n+m₂ nm₁≤nm₂) = ≤-⇒ (+-≤-cong-rev-left n+m₁≤n+m₂) nm₁≤nm₂
  ≤ᴹ-incr-drop {X = `V} n (m-V m₁ w₁ csn₁) (m-V m₂ w₂ csn₂) (≤-V n+m₁≤n+m₂ w₁≤w₂ c₁≤c₂) = ≤-V (+-≤-cong-rev-left n+m₁≤n+m₂) w₁≤w₂ c₁≤c₂

  ≤ᴹ-incr-cong : (n₁≤n₂ : n₁ ≤ n₂) → {nm₁ nm₂ : TermMetric X} → (nm₁ ≤ᴹ nm₂) → ((incr n₁ nm₁) ≤ᴹ (incr n₂ nm₂))
  ≤ᴹ-incr-cong n₁≤n₂ (≤-Unit m₁≤m₂) = ≤-Unit (+-≤-cong n₁≤n₂ m₁≤m₂)
  ≤ᴹ-incr-cong n₁≤n₂ (≤-V m₁≤m₂ w₁≤w₂ c₁≤c₂) = ≤-V (+-≤-cong n₁≤n₂ m₁≤m₂) w₁≤w₂ c₁≤c₂
  ≤ᴹ-incr-cong n₁≤n₂ (≤-⇒ m₁≤m₂ nm₁≤nm₂) = ≤-⇒ (+-≤-cong n₁≤n₂ m₁≤m₂) nm₁≤nm₂
  ≤ᴹ-incr-cong n₁≤n₂ (≤-× m₁≤m₂ nm₁≤nm₃ nm₂≤nm₄) = ≤-× (+-≤-cong n₁≤n₂ m₁≤m₂) nm₁≤nm₃ nm₂≤nm₄

  --------------------------------------------------------------------

  mutual

    val-metric : (M : Val Γ Y) → (E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))) → Wkn Γ E → (csn : List (ℕ × ℕ)) → TermMetric Y
    val-metric (var i) E ϖ csn = incr 2 (lookup-metric i E ϖ csn)
    val-metric (lam W) E ϖ csn = incr 2 (m-⇒ 0 (count-in-comp h W) (comp-metric W E (wkn-cons ϖ) csn))
    val-metric (pair M N) E ϖ csn = incr 2 (m-× 0 (val-metric M E ϖ csn) (val-metric N E ϖ csn))
    val-metric (pm {A = X} {B = Y} M N) E ϖ csn = let IH = val-metric M E ϖ in incr (suc (vx (IH csn) + ⟪ val-metric N E (wkn-cons (wkn-cons ϖ)) csn ⟫)) (val-metric N ((Y , λ c → rhs (IH c)) ∷ (X , λ c → lhs (IH c)) ∷ E) (wkn-cong (wkn-cong ϖ)) csn)
    val-metric unit E ϖ csn = m-Unit 2

    comp-metric : (W : Comp Γ Y) → (E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))) → Wkn Γ E → (csn : List (ℕ × ℕ)) → TermMetric Y
    comp-metric (return M) E ϖ [] = incr 2 (val-metric M E ϖ []) --incr 1 (zero-metric)
    comp-metric (return M) E ϖ (x ∷ csn) = incr 2 (val-metric M E ϖ csn)
    --comp-metric (return M) E ϖ csn = incr 2 (val-metric M E ϖ csn)
    comp-metric (pm {A = X} {B = Y} M W) E ϖ csn =
      let
        IH = val-metric M E ϖ
      in
        incr (suc (vx (IH csn) + ⟪ comp-metric W E (wkn-cons (wkn-cons ϖ)) csn ⟫)) (comp-metric W ((Y , λ c → rhs (IH c)) ∷ (X , λ c → lhs (IH c)) ∷ E) (wkn-cong (wkn-cong ϖ)) csn)
    comp-metric (push {A = X} W₁ W₂) E ϖ csn =
      let
        -- w2 = (comp-metric W₂ ((X , comp-metric W₁ E ϖ) ∷ E) (wkn-cong ϖ) csn)
        w2 = (comp-metric W₂ E (wkn-cons ϖ) csn)
        csn2 = ((count-in-comp h W₂ , ⟪ w2 ⟫) ∷ csn)
        w1 = ⟪ comp-metric W₁ E ϖ csn2 ⟫
      in
        incr (suc ((2+ (count-in-comp h W₂)) * w1)) w2 --incr (suc (w1 + csn-to-nat₀ w1 csn2)) w2
    comp-metric (app M N) E ϖ csn = let IH = val-metric M E ϖ csn in incr (2 + ((p1 IH) + ((suc (p2 IH)) * ⟪ val-metric N E ϖ csn ⟫))) (p3 IH)
    comp-metric (var M) E ϖ csn = incr (suc ⟪ val-metric M E ϖ csn ⟫) zero-metric
    comp-metric (sub W₁ W₂) E ϖ csn = let w = ⟪ comp-metric W₂ E ϖ csn ⟫ in incr (suc ⟪ comp-metric W₂ E ϖ csn ⟫) (comp-metric W₁ (((`V , λ _ → m-V 0 w csn)) ∷ E) (wkn-cong ϖ) csn)

    v̲a̲l̲-metric : (M : V̲a̲l̲ Γ Y) → (E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))) → Wkn Γ E → (csn : List (ℕ × ℕ)) → TermMetric Y
    v̲a̲l̲-metric (l̲a̲m̲ W) E ϖ csn = incr 1 (m-⇒ 0 (count-in-comp h W) (comp-metric W E (wkn-cons ϖ) csn))
    v̲a̲l̲-metric (pa̲i̲r̲ M N) E ϖ csn = incr 1 (m-× 0 (v̲a̲l̲-metric M E ϖ csn) (v̲a̲l̲-metric N E ϖ csn))
    v̲a̲l̲-metric u̲n̲i̲t̲ E ϖ csn = m-Unit 1
    v̲a̲l̲-metric (v̲a̲r̲ i) E ϖ csn = incr 1 (lookup-metric i E ϖ csn)

    c̲o̲m̲p-metric : (W : C̲o̲m̲p Γ Y) → (E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))) → Wkn Γ E → (csn : List (ℕ × ℕ)) → TermMetric Y
    c̲o̲m̲p-metric (r̲e̲t̲u̲r̲n̲ M) E ϖ [] = incr 1 (v̲a̲l̲-metric M E ϖ []) -- zero-metric -- halting state
    c̲o̲m̲p-metric (r̲e̲t̲u̲r̲n̲ M) E ϖ ((cnt , w) ∷ csn) = incr 1 (v̲a̲l̲-metric M E ϖ csn)
    c̲o̲m̲p-metric (a̲pp M N) E ϖ csn = let IH = val-metric M E ϖ csn in incr (suc ((p1 IH) + ((suc (p2 IH)) * ⟪ v̲a̲l̲-metric N E ϖ csn ⟫))) (p3 IH)

  mutual

    env-metric : Env Γ → Σ[ E ∈ List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X)) ] Wkn Γ E
    env-metric ∗ = [] , wkn-nil
    env-metric {Γ = Γ ∙ X} (γ ﹐ M) =
      let
        IH = env-metric γ
      in
        (X , (λ csn → v̲a̲l̲-metric M (proj₁ IH) (proj₂ IH) csn)) ∷ (proj₁ IH) , wkn-cong (proj₂ IH)
    env-metric {Γ = Γ ∙ `V} ((γ ﹐﹝ W ╎ cs ﹞) {π = π}) =
      let
        IH = env-metric γ
        w = ⟪ comp-metric W (proj₁ IH) (proj₂ IH) (cs-to-csn cs) ⟫
      in
        (`V , λ _ → m-V 0 w (cs-to-csn cs)) ∷ (proj₁ IH) , wkn-cong (proj₂ IH)

    cs-to-csn : (cs : CompStack Δ Z) → List (ℕ × ℕ)
    cs-to-csn ◻ = []
    cs-to-csn ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡}) =
      let
        csn = cs-to-csn cs
        IH = env-metric γ
      in
        ( (count-in-comp h W) , ⟪ comp-metric W (proj₁ IH) (wkn-cons (proj₂ IH)) csn ⟫ ) ∷ csn


  --------------------------------------------------------------------

  getIndex : LookupState X → Σ[ Γ ∈ Ctx ] Γ ∋ X
  getIndex ⟨ i ∥ _ ⟩ = _ , i

  getLookupEnv : (S : LookupState X) → Env (proj₁ (getIndex S))
  getLookupEnv ⟨ _ ∥ γ ⟩ = γ

  lstate-metric : LookupState X → List (ℕ × ℕ) → TermMetric X
  lstate-metric ⟨ i ∥ γ ⟩ csn =
    let
      EP = (env-metric γ)
    in
      lookup-metric i (proj₁ EP) (proj₂ EP) csn

  lhstate-metric : {T : LookupState X} → LookupHaltingState T → List (ℕ × ℕ) → TermMetric X
  lhstate-metric (found-unit {γ = γ}) csn = m-Unit 1
  lhstate-metric (found-pair {LHS = LHS} {RHS = RHS} {γ = γ}) csn = let EP = (env-metric γ) in v̲a̲l̲-metric (pa̲i̲r̲ LHS RHS) (proj₁ EP) (proj₂ EP) csn
  lhstate-metric (found-lam {W = W} {γ = γ}) csn = let EP = (env-metric γ) in v̲a̲l̲-metric (l̲a̲m̲ W) (proj₁ EP) (proj₂ EP) csn
  lhstate-metric (found-comp {W = W} {γ = γ} {cs = cs}) csn = let EP = (env-metric γ) in m-V 0 ⟪ comp-metric W (proj₁ EP) (proj₂ EP) (cs-to-csn cs) ⟫ (cs-to-csn cs)

  --------------------------------------------------------------------

  data Wke :   (π : Wk Γ Γ')
             → {E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))} → {E' : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))}
             → (ϖ : Wkn Γ E) → (ϖ' : Wkn Γ' E') → Set where
   wke-ε   :     Wke wk-ε wkn-nil wkn-nil
   wke-ccc :     {E E' : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))} → (π : Wk Γ Γ') → (ϖ : Wkn Γ E) → (ϖ' : Wkn Γ' E') → (e : (List (ℕ × ℕ) → TermMetric X))
               → (θ : Wke π ϖ ϖ')
               → (Wke (wk-cong π) {E = (X , e) ∷ E} {E' = (X , e) ∷ E'} (wkn-cong ϖ) (wkn-cong ϖ'))
   wke-wc- :     {E E' : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))} → (π : Wk Γ Γ') → (ϖ : Wkn Γ E) → (ϖ' : Wkn Γ' E') → (e : (List (ℕ × ℕ) → TermMetric X))
               → (θ : Wke π ϖ ϖ')
               → (Wke (wk-wk {A = X} π) {E = (X , e) ∷ E} {E' = E'} (wkn-cong ϖ) ϖ')
   wke-ww- :     {E E' : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))} → (π : Wk Γ Γ') → (ϖ : Wkn Γ E) → (ϖ' : Wkn Γ' E')
               → (θ : Wke π ϖ ϖ')
               → (Wke (wk-wk {A = X} π) {E = E} {E' = E'} (wkn-cons ϖ) ϖ')
   wke-cww :     {E E' : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))} → (π : Wk Γ Γ') → (ϖ : Wkn Γ E) → (ϖ' : Wkn Γ' E')
               → (θ : Wke π ϖ ϖ')
               → (Wke (wk-cong {A = X} π) {E = E} {E' = E'} (wkn-cons ϖ) (wkn-cons ϖ'))

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

  wke-id : {E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))} → {π : Wk Γ Γ} → {ϖ : Wkn Γ E} → Wke π ϖ ϖ
  wke-id {π = π} {ϖ = wkn-nil} rewrite wk-id-id {π = π} = wke-ε
  wke-id {π = π} {ϖ = wkn-cong ϖ} rewrite wk-id-id {π = π} = wke-ccc wk-id ϖ ϖ _ wke-id
  wke-id {π = π} {ϖ = wkn-cons ϖ} rewrite wk-id-id {π = π} = wke-cww wk-id ϖ ϖ wke-id

  --------------------------------------------------------------------

  -- Wke πᵥ (proj₂ (env-metric γ)) (proj₂ (env-metric γ'))

  data LookupSteps : LookupState X → Set where

    steps : {S T : LookupState X} → S →ᴸ* T → (H : LookupHaltingState T) → ⟦ S ⟧ᴸ ≡ ⟦ T ⟧ᴸ → (π : Wk (lCtx S) (lTCtx T)) → (⟦ π ⟧ʷ ⟦ lEnv S ⟧ᴱ ≡ ⟦ lTEnv T ⟧ᴱ) → (∀ (csn : List (ℕ × ℕ))
            → lhstate-metric H csn ≤ᴹ lstate-metric S csn)
            → (θ : Wke π (proj₂ (env-metric (lEnv S))) (proj₂ (env-metric (lTEnv T))))
            → LookupSteps S
  lookup : (i : Γ ∋ X) → (γ : Env Γ) → LookupSteps {X = X} ⟨ i ∥ γ ⟩
  lookup h (γ ﹐ l̲a̲m̲ W) = steps (⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩ ◼) found-lam refl (wk-wk wk-id) refl (λ csn → ≤ᴹ-refl) (wke-wc- wk-id (proj₂ (env-metric γ)) (proj₂ (env-metric γ)) (v̲a̲l̲-metric (l̲a̲m̲ W) (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) wke-id)
  lookup h (γ ﹐ pa̲i̲r̲ LHS RHS) = steps (⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩ ◼) found-pair refl (wk-wk wk-id) refl (λ csn → ≤ᴹ-refl) (wke-wc- wk-id (proj₂ (env-metric γ)) (proj₂ (env-metric γ)) (v̲a̲l̲-metric (pa̲i̲r̲ LHS RHS) (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) wke-id)
  lookup h (γ ﹐ u̲n̲i̲t̲) = steps (⟨ h ∥ _﹐_ γ (u̲n̲i̲t̲) ⟩ ◼) found-unit refl (wk-wk wk-id) refl (λ csn → ≤ᴹ-refl) (wke-wc- wk-id (proj₂ (env-metric γ)) (proj₂ (env-metric γ)) (v̲a̲l̲-metric u̲n̲i̲t̲ (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) wke-id)
  lookup h (γ ﹐ v̲a̲r̲ i) with lookup i γ
  ... | steps {T = T} i>>T HT i≡T WK w≡γ T≤S θ = steps (_ →ᴸ⟨ val-h-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ (λ csn → ≤ᴹ-incr-cong (z≤n {n = 1}) (T≤S csn)) (wke-wc- WK (proj₂ (env-metric γ)) (proj₂ (env-metric (lTEnv T))) (v̲a̲l̲-metric (v̲a̲r̲ i) (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) θ)
  lookup h (γ ﹐﹝ W ╎ cs ﹞ ) = steps (⟨ h ∥ γ ﹐﹝ W ╎ cs ﹞ ⟩ ◼) found-comp refl (wk-wk wk-id) refl (λ csn → ≤ᴹ-refl) (wke-wc- wk-id (proj₂ (env-metric γ)) (proj₂ (env-metric γ)) (λ _ → m-V 0 ⟪ comp-metric W (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ (cs-to-csn cs)) wke-id)
  lookup (t i) (γ ﹐ M) with lookup i γ
  ... | steps {T = T} i>>T HT i≡T WK w≡γ T≤S θ = steps (_ →ᴸ⟨ val-t-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ T≤S (wke-wc- WK (proj₂ (env-metric γ)) (proj₂ (env-metric (lTEnv T))) (v̲a̲l̲-metric M (proj₁ (env-metric γ)) (proj₂ (env-metric γ))) θ)
  lookup (t i) (γ ﹐﹝ W ╎ cs ﹞) with lookup i γ
  ... | steps {T = T} i>>T HT i≡T WK w≡γ T≤S θ = steps (_ →ᴸ⟨ comp-t-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ T≤S (wke-wc- WK (proj₂ (env-metric γ)) (proj₂ (env-metric (lTEnv T))) (λ _ → m-V 0 ⟪ comp-metric W (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) (cs-to-csn cs) ⟫ (cs-to-csn cs)) θ)


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

  topCtx : ValState T◾ → Ctx
  topCtx (∘ ⭭_ {Γ = Γ} x ⊲ γ ∷ x₁) = Γ
  topCtx (∘ ⇡_ {Γ = Γ} M ⊲ γ ∷ x₁) = Γ
  topCtx (∘ ⇡ᴹ {Γ = Γ} M N ⊲ γ ∷ x₁) = Γ
  topCtx (∘ ⇡ᴸ {Γ = Γ} LHS RHS ⊲ γ ∷ x₁) = Γ
  topCtx (∘ ⇡ᴿ {Γ = Γ} LHS RHS ⊲ γ ∷ x₁) = Γ
  topCtx (∙ ⭭_ {Γ = Γ} x ⊲ γ ∷ x₁) = Γ
  topCtx (∙ ⇡_ {Γ = Γ} M ⊲ γ ∷ x₁) = Γ
  topCtx (∙ ⇡ᴹ {Γ = Γ} M N ⊲ γ ∷ x₁) = Γ
  topCtx (∙ ⇡ᴸ {Γ = Γ} LHS RHS ⊲ γ ∷ x₁) = Γ
  topCtx (∙ ⇡ᴿ {Γ = Γ} LHS RHS ⊲ γ ∷ x₁) = Γ

  topEnv : (S : ValState T◾) → Env (topCtx S)
  topEnv (∘ ⭭ x ⊲ γ ∷ x₁) = γ
  topEnv (∘ ⇡ M ⊲ γ ∷ x₁) = γ
  topEnv (∘ ⇡ᴹ M N ⊲ γ ∷ x₁) = γ
  topEnv (∘ ⇡ᴸ LHS RHS ⊲ γ ∷ x₁) = γ
  topEnv (∘ ⇡ᴿ LHS RHS ⊲ γ ∷ x₁) = γ
  topEnv (∙ ⭭ x ⊲ γ ∷ x₁) = γ
  topEnv (∙ ⇡ M ⊲ γ ∷ x₁) = γ
  topEnv (∙ ⇡ᴹ M N ⊲ γ ∷ x₁) = γ
  topEnv (∙ ⇡ᴸ LHS RHS ⊲ γ ∷ x₁) = γ
  topEnv (∙ ⇡ᴿ LHS RHS ⊲ γ ∷ x₁) = γ

  data ValHaltingState : ValState T◾ → Set where

      ∙_⊲_■ : (M : V̲a̲l̲ Γ X) → (γ : Env Γ) → ValHaltingState (∙ ((⭭ M ⊲ γ ∷ □) {↥ = 🗆}))


  data ValSteps : ValState T◾ → Set where

    steps : {S T : ValState T◾} → S ↠ᵛ T → ValHaltingState T → ⟦ S ⟧ᵛꟴ ≡ ⟦ T ⟧ᵛꟴ → (π : Wk (topCtx T) (topCtx S)) → (⟦ π ⟧ʷ ⟦ topEnv T ⟧ᴱ ≡ ⟦ topEnv S ⟧ᴱ) → ValSteps S


  val-eval-rec : (M : Γ' ⊢ᵛ X) → (γ : Env Γ) → (π : Wk Γ Γ') → ValSteps {T◾ = X} (∘ ((⇡ (wk-val π M) ⊲ γ ∷ □) {↥ = 🗆}))

  val-eval-rec {X = `V} (var {A = .`V} i) γ π = steps (_ →ᵛ⟨ ∘var-c ⟩．) (∙ v̲a̲r̲ (wk-mem π i) ⊲ γ ■) refl wk-id refl

  val-eval-rec {X = `Unit} (var {A = .`Unit} i) γ π with lookup (wk-mem π i) γ
  ... | steps i>>T found-unit i≡T π₁ w≡γ _ _ = steps (_ →ᵛ⟨ ∘var i>>T π₁ ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id refl

  val-eval-rec {X = X `× X₁} (var {A = .(X `× X₁)} i) γ π with lookup (wk-mem π i) γ
  ... | steps i>>T (found-pair {LHS = LHS} {RHS = RHS} {γ = γ₁}) i≡T π₁ w≡γ _ _ =

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
  val-eval-rec {X = X `⇒ X₁} (var {A = .(X `⇒ X₁)} i) γ π with lookup (wk-mem π i) γ

  ... | steps i>>T (found-lam {W = W} {γ = γ₁}) i≡T π₁ w≡γ _ _ =

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

  val-eval-rec (lam W) γ π = steps (∘ ⇡ (wk-val π (lam W)) ⊲ γ ∷ □ →ᵛ⟨ ∘lam ⟩．) (∙ l̲a̲m̲ (wk-comp (wk-cong π) W) ⊲ γ ■) refl wk-id refl

  val-eval-rec unit γ π = steps (_ →ᵛ⟨ ∘unit ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id refl

  val-eval-rec (pair {A = X} {B = Y} LHS RHS) γ π with val-eval-rec {X = X} LHS γ π
  ... | steps {T = ∙ (⭭_ {X = X} LT ⊲ γ₁ ∷ □) {↥ = 🗆}} L>T ∙LT L≡T πᴸ wk≡ᴸ with  val-eval-rec {X = Y} RHS γ₁ (wk-trans πᴸ π)
  ...      | steps {T = ∙ (⭭_ {X = Y} RT ⊲ γ₂ ∷ □) {↥ = 🗆}} R>T ∙RT R≡T πᴿ wk≡ᴿ rewrite sym (wk-val-trans RHS πᴸ π) =

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

  val-eval-rec (pm M N) γ π with val-eval-rec M γ π
  ... | steps M>T ∙ pa̲i̲r̲ LHS RHS ⊲ γ₁ ■ M≡T π₁ wk≡₁ with val-eval-rec N (_﹐_ (_﹐_ γ₁ LHS) (wk-v̲a̲l̲ (wk-wk wk-id) RHS)) ((wk-cong (wk-cong (wk-trans π₁ π)))) | (wk-val-trans N (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π)))
  ...    | steps {T = T} N>T ∙T N≡T π₂ wk≡₂ | eq with N>T
  ...      | N>T' rewrite sym eq =
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

          ( ⟦ wk-trans π₂ (wk-wk (wk-wk π₁)) ⟧ʷ ⟦ topEnv T ⟧ᴱ
            ≡⟨ sym (wk-sem-trans π₂ (wk-wk (wk-wk π₁)) ⟦ topEnv T ⟧ᴱ) ⟩
            ⟦ wk-wk (wk-wk π₁) ⟧ʷ (⟦ π₂ ⟧ʷ ⟦ topEnv T ⟧ᴱ)
            ≡⟨ cong (λ y → ⟦ wk-wk (wk-wk π₁) ⟧ʷ y) wk≡₂ ⟩
            ⟦ wk-wk (wk-wk π₁) ⟧ʷ (((⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))
            ≡⟨ refl ⟩
            ⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ
            ≡⟨ wk≡₁ ⟩
            ⟦ γ ⟧ᴱ ∎)


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

  _ : val-eval ex2 ≡
      steps
      (∘
      ⇡
      pm (pm (pair (lam (return (var h))) unit) (pair unit (var (t h))))
      (pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))))
      ⊲ ∗ ∷ □
      →ᵛ⟨ ∘pm ⟩
      ∘
      ⇡ pm (pair (lam (return (var h))) unit) (pair unit (var (t h))) ⊲ ∗
      ∷
      ⇡ᴹ (pm (pair (lam (return (var h))) unit) (pair unit (var (t h))))
      (pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))))
      ⊲ ∗ ∷ □
      →ᵛ⟨ ∘pm ⟩
      ∘
      ⇡ pair (lam (return (var h))) unit ⊲ ∗ ∷
      ⇡ᴹ (pair (lam (return (var h))) unit) (pair unit (var (t h))) ⊲ ∗ ∷
      ⇡ᴹ (pm (pair (lam (return (var h))) unit) (pair unit (var (t h))))
      (pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))))
      ⊲ ∗ ∷ □
      →ᵛ⟨ ∘pair ⟩
      ∘
      ⇡ lam (return (var h)) ⊲ ∗ ∷
      ⇡ᴸ (lam (return (var h))) unit ⊲ ∗ ∷
      ⇡ᴹ (pair (lam (return (var h))) unit) (pair unit (var (t h))) ⊲ ∗ ∷
      ⇡ᴹ (pm (pair (lam (return (var h))) unit) (pair unit (var (t h))))
      (pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))))
      ⊲ ∗ ∷ □
      →ᵛ⟨ ∘lam ⟩
      ∙
      ⭭ l̲a̲m̲ (return (var h)) ⊲ ∗ ∷
      ⇡ᴸ (lam (return (var h))) unit ⊲ ∗ ∷
      ⇡ᴹ (pair (lam (return (var h))) unit) (pair unit (var (t h))) ⊲ ∗ ∷
      ⇡ᴹ (pm (pair (lam (return (var h))) unit) (pair unit (var (t h))))
      (pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))))
      ⊲ ∗ ∷ □
      →ᵛ⟨ ∙M∷l ⟩
      ∘
      ⇡ unit ⊲ ∗ ∷
      ⇡ᴿ (l̲a̲m̲ (return (var h))) unit ⊲ ∗ ∷
      ⇡ᴹ (pair (lam (return (var h))) unit) (pair unit (var (t h))) ⊲ ∗ ∷
      ⇡ᴹ (pm (pair (lam (return (var h))) unit) (pair unit (var (t h))))
      (pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))))
      ⊲ ∗ ∷ □
      →ᵛ⟨ ∘unit ⟩
      ∙
      ⭭ u̲n̲i̲t̲ ⊲ ∗ ∷
      ⇡ᴿ (l̲a̲m̲ (return (var h))) unit ⊲ ∗ ∷
      ⇡ᴹ (pair (lam (return (var h))) unit) (pair unit (var (t h))) ⊲ ∗ ∷
      ⇡ᴹ (pm (pair (lam (return (var h))) unit) (pair unit (var (t h))))
      (pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))))
      ⊲ ∗ ∷ □
      →ᵛ⟨ ∙M∷r ⟩
      ∙
      ⭭ pa̲i̲r̲ (l̲a̲m̲ (return (var h))) u̲n̲i̲t̲ ⊲ ∗ ∷
      ⇡ᴹ (pair (lam (return (var h))) unit) (pair unit (var (t h))) ⊲ ∗ ∷
      ⇡ᴹ (pm (pair (lam (return (var h))) unit) (pair unit (var (t h))))
      (pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))))
      ⊲ ∗ ∷ □
      →ᵛ⟨ ∙pair∷pm ⟩
      ∘
      ⇡ pair unit (var (t h)) ⊲ ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ∷
      ⇡ᴹ (pm (pair (lam (return (var h))) unit) (pair unit (var (t h))))
      (pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))))
      ⊲ ∗ ∷ □
      →ᵛ⟨ ∘pair ⟩
      ∘
      ⇡ unit ⊲ ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ∷
      ⇡ᴸ unit (var (t h)) ⊲ ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ∷
      ⇡ᴹ (pm (pair (lam (return (var h))) unit) (pair unit (var (t h))))
      (pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))))
      ⊲ ∗ ∷ □
      →ᵛ⟨ ∘unit ⟩
      ∙
      ⭭ u̲n̲i̲t̲ ⊲ ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ∷
      ⇡ᴸ unit (var (t h)) ⊲ ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ∷
      ⇡ᴹ (pm (pair (lam (return (var h))) unit) (pair unit (var (t h))))
      (pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))))
      ⊲ ∗ ∷ □
      →ᵛ⟨ ∙M∷l ⟩
      ∘
      ⇡ var (t h) ⊲ ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ∷
      ⇡ᴿ u̲n̲i̲t̲ (var (t h)) ⊲ ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ∷
      ⇡ᴹ (pm (pair (lam (return (var h))) unit) (pair unit (var (t h))))
      (pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))))
      ⊲ ∗ ∷ □
      →ᵛ⟨
      ∘var
      (⟨ t h ∥ ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ⟩ →ᴸ⟨ val-t-step ⟩
        (⟨ h ∥ ∗ ﹐ l̲a̲m̲ (return (var h)) ⟩ ◼))
      (wk-wk (wk-wk wk-ε))
      ⟩
      ∙
      ⭭ l̲a̲m̲ (return (var h)) ⊲ ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲
      ∷
      ⇡ᴿ u̲n̲i̲t̲ (var (t h)) ⊲ ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ∷
      ⇡ᴹ (pm (pair (lam (return (var h))) unit) (pair unit (var (t h))))
      (pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))))
      ⊲ ∗ ∷ □
      →ᵛ⟨ ∙M∷r ⟩
      ∙
      ⭭ pa̲i̲r̲ u̲n̲i̲t̲ (l̲a̲m̲ (return (var h))) ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ∷
      ⇡ᴹ (pm (pair (lam (return (var h))) unit) (pair unit (var (t h))))
      (pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))))
      ⊲ ∗ ∷ □
      →ᵛ⟨ ∙pair∷pm ⟩
      ∘
      ⇡ pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))) ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ∷ □
      →ᵛ⟨ ∘pm ⟩
      ∘
      ⇡ pair unit unit ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ∷
      ⇡ᴹ (pair unit unit) (pair (var (t h)) (var (t (t (t h))))) ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ∷ □
      →ᵛ⟨ ∘pair ⟩
      ∘
      ⇡ unit ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ∷
      ⇡ᴸ unit unit ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ∷
      ⇡ᴹ (pair unit unit) (pair (var (t h)) (var (t (t (t h))))) ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ∷ □
      →ᵛ⟨ ∘unit ⟩
      ∙
      ⭭ u̲n̲i̲t̲ ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ∷
      ⇡ᴸ unit unit ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ∷
      ⇡ᴹ (pair unit unit) (pair (var (t h)) (var (t (t (t h))))) ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ∷ □
      →ᵛ⟨ ∙M∷l ⟩
      ∘
      ⇡ unit ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ∷
      ⇡ᴿ u̲n̲i̲t̲ unit ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ∷
      ⇡ᴹ (pair unit unit) (pair (var (t h)) (var (t (t (t h))))) ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ∷ □
      →ᵛ⟨ ∘unit ⟩
      ∙
      ⭭ u̲n̲i̲t̲ ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ∷
      ⇡ᴿ u̲n̲i̲t̲ unit ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ∷
      ⇡ᴹ (pair unit unit) (pair (var (t h)) (var (t (t (t h))))) ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ∷ □
      →ᵛ⟨ ∙M∷r ⟩
      ∙
      ⭭ pa̲i̲r̲ u̲n̲i̲t̲ u̲n̲i̲t̲ ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ∷
      ⇡ᴹ (pair unit unit) (pair (var (t h)) (var (t (t (t h))))) ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ∷ □
      →ᵛ⟨ ∙pair∷pm ⟩
      ∘
      ⇡ pair (var (t h)) (var (t (t (t h)))) ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ﹐ u̲n̲i̲t̲
      ﹐ u̲n̲i̲t̲
      ∷ □
      →ᵛ⟨ ∘pair ⟩
      ∘
      ⇡ var (t h) ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ﹐ u̲n̲i̲t̲
      ﹐ u̲n̲i̲t̲
      ∷
      ⇡ᴸ (var (t h)) (var (t (t (t h)))) ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ﹐ u̲n̲i̲t̲
      ﹐ u̲n̲i̲t̲
      ∷ □
      →ᵛ⟨
      ∘var
      (⟨ t h ∥
        ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
        l̲a̲m̲ (return (var h))
        ﹐ u̲n̲i̲t̲
        ﹐ u̲n̲i̲t̲
        ⟩
        →ᴸ⟨ val-t-step ⟩
        (⟨ h ∥
        ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
        l̲a̲m̲ (return (var h))
        ﹐ u̲n̲i̲t̲
        ⟩
        ◼))
      (wk-wk (wk-wk (wk-cong (wk-cong (wk-cong (wk-cong wk-ε))))))
      ⟩
      ∙
      ⭭ u̲n̲i̲t̲ ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ﹐ u̲n̲i̲t̲
      ﹐ u̲n̲i̲t̲
      ∷
      ⇡ᴸ (var (t h)) (var (t (t (t h)))) ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ﹐ u̲n̲i̲t̲
      ﹐ u̲n̲i̲t̲
      ∷ □
      →ᵛ⟨ ∙M∷l ⟩
      ∘
      ⇡ var (t (t (t h))) ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ﹐ u̲n̲i̲t̲
      ﹐ u̲n̲i̲t̲
      ∷
      ⇡ᴿ u̲n̲i̲t̲ (var (t (t (t h)))) ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ﹐ u̲n̲i̲t̲
      ﹐ u̲n̲i̲t̲
      ∷ □
      →ᵛ⟨
      ∘var
      (⟨ t (t (t h)) ∥
        ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
        l̲a̲m̲ (return (var h))
        ﹐ u̲n̲i̲t̲
        ﹐ u̲n̲i̲t̲
        ⟩
        →ᴸ⟨ val-t-step ⟩
        (⟨ t (t h) ∥
        ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
        l̲a̲m̲ (return (var h))
        ﹐ u̲n̲i̲t̲
        ⟩
        →ᴸ⟨ val-t-step ⟩
        (⟨ t h ∥
          ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
          l̲a̲m̲ (return (var h))
          ⟩
          →ᴸ⟨ val-t-step ⟩
          (⟨ h ∥ ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ⟩ ◼))))
      (wk-wk (wk-wk (wk-wk (wk-wk (wk-cong (wk-cong wk-ε))))))
      ⟩
      ∙
      ⭭ u̲n̲i̲t̲ ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ﹐ u̲n̲i̲t̲
      ﹐ u̲n̲i̲t̲
      ∷
      ⇡ᴿ u̲n̲i̲t̲ (var (t (t (t h)))) ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ﹐ u̲n̲i̲t̲
      ﹐ u̲n̲i̲t̲
      ∷ □
      →ᵛ⟨ ∙M∷r ⟩．)
      ∙ pa̲i̲r̲ u̲n̲i̲t̲ u̲n̲i̲t̲ ⊲
      ∗ ﹐ l̲a̲m̲ (return (var h)) ﹐ u̲n̲i̲t̲ ﹐ u̲n̲i̲t̲ ﹐
      l̲a̲m̲ (return (var h))
      ﹐ u̲n̲i̲t̲
      ﹐ u̲n̲i̲t̲
      ■
      refl (wk-wk (wk-wk (wk-wk (wk-wk (wk-wk (wk-wk wk-ε)))))) refl
  _ = refl

  --------------------------------------------------------------

  -- This is not used anywhere, but shows that the interpretations of environments and computation stacks respect the cps translation of sub

  sub-cps : (M : (Γ ∙ `V) ⊢ᶜ X) → (N : Γ ⊢ᶜ X) → (γ : ⟦ Γ ⟧ˣ ) → (k : ⟦ X ⟧ → R) → ⟦ sub M N ⟧ᶜ γ k ≡ ⟦ M ⟧ᶜ ( γ , ⟦ N ⟧ᶜ γ k ) k
  sub-cps M N γ k = refl

  sub-cps' : (M : (Γ ∙ `V) ⊢ᶜ X) → (N : Γ ⊢ᶜ X) → (γ : Env Γ) → (cs : CompStack Δ X) → (πₓ : Wk Γ Δ) → (wk≡ : ⟦ πₓ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) → ⟦ sub M N ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cs ⟧ᴷ ≡ ⟦ M ⟧ᶜ ⟦ (γ ﹐﹝ N ╎ cs ﹞) {π = πₓ} {wk≡ = wk≡} ⟧ᴱ ⟦ cs ⟧ᴷ
  sub-cps' M N γ cs πₓ wk≡ = refl
-}
