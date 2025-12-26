module Inception.Sub.ValueMachine (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Function.Base using (const; _∘_; _$_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; subst)
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

n≤n+m : n ≤ n + m
n≤n+m {n = zero} {m = m} = z≤n
n≤n+m {n = suc n} {m = m} = s≤s n≤n+m

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

  data TermMetric : Ty → Set where
    m-Unit : (m : ℕ) → TermMetric `Unit
    --m-V : (m : ℕ) → (w : ℕ) → (csn : List (ℕ × ℕ)) → TermMetric (`V)
    m-V : (m : ℕ) → (w : ℕ) → TermMetric (`V)
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
    --≤-V    : {w₁ w₂ : ℕ} {csn₁ csn₂ : List (ℕ × ℕ)} → (m₁ ≤ m₂) → (w₁ ≤ w₂) → (csn₁ ≤ᶜˢⁿ csn₂) → (m-V m₁ w₁ csn₁) ≤ᴹ (m-V m₂ w₂ csn₂)
    ≤-V    : {w₁ w₂ : ℕ} → (m₁ ≤ m₂) → (w₁ ≤ w₂) → (m-V m₁ w₁) ≤ᴹ (m-V m₂ w₂)
    ≤-⇒    : {cnt : ℕ} {nm₁ nm₂ : TermMetric Y} → (m₁ ≤ m₂) → (nm₁ ≤ᴹ nm₂) → (m-⇒ {X = X} m₁ cnt nm₁) ≤ᴹ (m-⇒ m₂ cnt nm₂)
    ≤-×    : {lhs₁ lhs₂ : TermMetric X} → {rhs₁ rhs₂ : TermMetric Y} → (n₁ ≤ n₂) → (lhs₁ ≤ᴹ lhs₂) → (rhs₁ ≤ᴹ rhs₂) → (m-× n₁ lhs₁ rhs₁) ≤ᴹ (m-× n₂ lhs₂ rhs₂)

  ≤ᴹ-refl : {nm : TermMetric X} → nm ≤ᴹ nm
  ≤ᴹ-refl {nm = m-Unit m} = ≤-Unit ≤-refl
  --≤ᴹ-refl {nm = m-V m n csn} = ≤-V  ≤-refl ≤-refl [c≤c]
  ≤ᴹ-refl {nm = m-V m w} = ≤-V  ≤-refl ≤-refl
  ≤ᴹ-refl {nm = m-⇒ m cnt nm} = ≤-⇒ ≤-refl ≤ᴹ-refl
  ≤ᴹ-refl {nm = m-× m nm nm₁} = ≤-× ≤-refl ≤ᴹ-refl ≤ᴹ-refl

  ≤ᴹ-trans : {nm₁ nm₂ nm₃ : TermMetric X} → nm₁ ≤ᴹ nm₂ → nm₂ ≤ᴹ nm₃ → nm₁ ≤ᴹ nm₃
  ≤ᴹ-trans (≤-Unit x) (≤-Unit x₁) = ≤-Unit (≤-trans x x₁)
  --≤ᴹ-trans (≤-V x x₁ x₂) (≤-V x₃ x₄ x₅) = ≤-V (≤-trans x x₃) (≤-trans x₁ x₄) (≤ᶜˢⁿ-trans x₂ x₅)
  ≤ᴹ-trans (≤-V x x₁) (≤-V x₃ x₄) = ≤-V (≤-trans x x₃) (≤-trans x₁ x₄)
  ≤ᴹ-trans (≤-⇒ x nm₁≤nm₂) (≤-⇒ x₁ nm₂≤nm₃) = ≤-⇒ (≤-trans x x₁) (≤ᴹ-trans nm₁≤nm₂ nm₂≤nm₃)
  ≤ᴹ-trans (≤-× x nm₁≤nm₂ nm₁≤nm₃) (≤-× x₁ nm₂≤nm₃ nm₂≤nm₄) = ≤-× (≤-trans x x₁) (≤ᴹ-trans nm₁≤nm₂ nm₂≤nm₃) (≤ᴹ-trans nm₁≤nm₃ nm₂≤nm₄)

  zero-metric : TermMetric X
  zero-metric {X = `Unit} = m-Unit 0
  zero-metric {X = X `× Y} = m-× 0 (zero-metric {X = X}) (zero-metric {X = Y})
  zero-metric {X = X `⇒ Y} = m-⇒ 0 0 (zero-metric {X = Y})
  --zero-metric {X = `V} = m-V 0 0 []
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
  ≤ᶜˢⁿ-decr {n₁ = n₁} {n₂ = n₂} n₁≤n₂ ([s≤s] n₃≤n₄ c₁≤c₂) =
    let
      m₁≤m₂ = +-≤-cong n₃≤n₄ (*-≤-cong n₁≤n₂ ≤-refl)
    in
      +-≤-cong m₁≤m₂ (≤ᶜˢⁿ-decr m₁≤m₂ c₁≤c₂)

  ⟪_⟫ : TermMetric X → ℕ
  ⟪ m-Unit m ⟫ = m
  --⟪ m-V m w csn ⟫ = m + w + csn-to-nat₀ w csn
  ⟪ m-V m w ⟫ = m + w
  ⟪ m-⇒ m cnt nm ⟫ = m + ⟪ nm ⟫
  ⟪ m-× m nm₁ nm₂ ⟫ = m + ⟪ nm₁ ⟫ + ⟪ nm₂ ⟫

  incr : ℕ → TermMetric X → TermMetric X
  incr n (m-Unit m) = m-Unit (n + m)
  --incr n (m-V m w csn) = m-V (n + m) w csn
  incr n (m-V m w) = m-V (n + m) w
  incr n (m-⇒ m cnt nm) = m-⇒ (n + m) cnt nm
  incr n (m-× m nm₁ nm₂) = m-× (n + m) nm₁ nm₂

  incr-coh : (n : ℕ) → (X : Ty) → (nm : TermMetric X) → ⟪ incr n nm ⟫ ≡ n + ⟪ nm ⟫
  incr-coh zero `Unit (m-Unit m) = refl
  incr-coh zero (X `× X₁) (m-× m nm nm₁) = refl
  incr-coh zero (X `⇒ X₁) (m-⇒ m cnt nm) = refl
  --incr-coh zero `V (m-V m w csn) = refl
  incr-coh zero `V (m-V m w) = refl
  incr-coh (suc n) `Unit (m-Unit m) = refl
  incr-coh (suc n) (X `× X₁) (m-× m nm nm₁) rewrite +-assoc {n} {m} {⟪ nm ⟫} | +-assoc {n} {m + ⟪ nm ⟫} {⟪ nm₁ ⟫} = refl
  incr-coh (suc n) (X `⇒ X₁) (m-⇒ m cnt nm) rewrite +-assoc {n} {m} {⟪ nm ⟫} = refl
  --incr-coh (suc n) `V (m-V m w csn) rewrite +-assoc {n} {m} {w} | +-assoc {n} {m + w} {csn-to-nat₀ w csn} = refl
  incr-coh (suc n) `V (m-V m w) rewrite +-assoc {n} {m} {w} = refl

  {-# REWRITE incr-coh #-}

  incr-zero-coh : (X : Ty) → (nm : TermMetric X) → incr zero nm ≡ nm
  incr-zero-coh `Unit (m-Unit m) = refl
  incr-zero-coh (X `× X₁) (m-× m nm₁ nm₂) = refl
  incr-zero-coh (X `⇒ X₁) (m-⇒ m cnt nm) = refl
  --incr-zero-coh `V (m-V m w csn) = refl
  incr-zero-coh `V (m-V m w) = refl

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
  --≤ᴹ-incr-drop {X = `V} n (m-V m₁ w₁ csn₁) (m-V m₂ w₂ csn₂) (≤-V n+m₁≤n+m₂ w₁≤w₂ c₁≤c₂) = ≤-V (+-≤-cong-rev-left n+m₁≤n+m₂) w₁≤w₂ c₁≤c₂
  ≤ᴹ-incr-drop {X = `V} n (m-V m₁ w₁) (m-V m₂ w₂) (≤-V n+m₁≤n+m₂ w₁≤w₂) = ≤-V (+-≤-cong-rev-left n+m₁≤n+m₂) w₁≤w₂

  ≤ᴹ-incr-cong : (n₁≤n₂ : n₁ ≤ n₂) → {nm₁ nm₂ : TermMetric X} → (nm₁ ≤ᴹ nm₂) → ((incr n₁ nm₁) ≤ᴹ (incr n₂ nm₂))
  ≤ᴹ-incr-cong n₁≤n₂ (≤-Unit m₁≤m₂) = ≤-Unit (+-≤-cong n₁≤n₂ m₁≤m₂)
  --≤ᴹ-incr-cong n₁≤n₂ (≤-V m₁≤m₂ w₁≤w₂ c₁≤c₂) = ≤-V (+-≤-cong n₁≤n₂ m₁≤m₂) w₁≤w₂ c₁≤c₂
  ≤ᴹ-incr-cong n₁≤n₂ (≤-V m₁≤m₂ w₁≤w₂) = ≤-V (+-≤-cong n₁≤n₂ m₁≤m₂) w₁≤w₂
  ≤ᴹ-incr-cong n₁≤n₂ (≤-⇒ m₁≤m₂ nm₁≤nm₂) = ≤-⇒ (+-≤-cong n₁≤n₂ m₁≤m₂) nm₁≤nm₂
  ≤ᴹ-incr-cong n₁≤n₂ (≤-× m₁≤m₂ nm₁≤nm₃ nm₂≤nm₄) = ≤-× (+-≤-cong n₁≤n₂ m₁≤m₂) nm₁≤nm₃ nm₂≤nm₄

-------------------------------------------------------------------------------------------------

  ≤ᴹ-p1 : {nm₁ nm₂ : TermMetric (X `⇒ Y)} → (nm₁ ≤ᴹ nm₂) → (p1 nm₁) ≤ (p1 nm₂)
  ≤ᴹ-p1 (≤-⇒ n₁≤n₂ nm₁≤nm₂) = n₁≤n₂

  ≤ᴹ-p2 : {nm₁ nm₂ : TermMetric (X `⇒ Y)} → (nm₁ ≤ᴹ nm₂) → (p2 nm₁) ≡ (p2 nm₂)
  ≤ᴹ-p2 (≤-⇒ n₁≤n₂ nm₁≤nm₂) = refl

  ≡⇒≤ : n ≡ m → n ≤ m
  ≡⇒≤ {n = n} {m = m} n≡m rewrite n≡m = ≤-refl

  +-p1-incr : (n : ℕ) → (nm : TermMetric (X `⇒ Y)) → p1 (incr n nm) ≡ n + (p1 nm)
  +-p1-incr n (m-⇒ {Y = Y} {X = X} m cnt nm) with incr n (m-⇒ {Y = Y} {X = X} m cnt nm)
  ... | x = refl

  ≡-p2-incr : (n : ℕ) → (nm : TermMetric (X `⇒ Y)) → p2 (incr n nm) ≡ p2 nm
  ≡-p2-incr n (m-⇒ m cnt nm) = refl

  ≡-p3-incr : (n : ℕ) → (nm : TermMetric (X `⇒ Y)) → p3 (incr n nm) ≡ p3 nm
  ≡-p3-incr n (m-⇒ m cnt nm) = refl

  {-# REWRITE ≡-p2-incr #-}

  ≤ᴹ-p3 : {nm₁ nm₂ : TermMetric (X `⇒ Y)} → (nm₁ ≤ᴹ nm₂) → (p3 nm₁) ≤ᴹ (p3 nm₂)
  ≤ᴹ-p3 (≤-⇒ n₁≤n₂ nm₁≤nm₂) = nm₁≤nm₂

  ≤ᴹ-lhs : {nm₁ nm₂ : TermMetric (X `× Y)} → (nm₁ ≤ᴹ nm₂) → (lhs nm₁) ≤ᴹ (lhs nm₂)
  ≤ᴹ-lhs (≤-× x nm₁≤nm₃ nm₂≤nm₄) = nm₁≤nm₃

  ≤ᴹ-rhs : {nm₁ nm₂ : TermMetric (X `× Y)} → (nm₁ ≤ᴹ nm₂) → (rhs nm₁) ≤ᴹ (rhs nm₂)
  ≤ᴹ-rhs (≤-× x nm₁≤nm₃ nm₂≤nm₄) = nm₂≤nm₄

  ≤ᴹ-vx : {nm₁ nm₂ : TermMetric (X `× Y)} → (nm₁ ≤ᴹ nm₂) → (vx nm₁) ≤ (vx nm₂)
  ≤ᴹ-vx (≤-× n₁≤n₂ nm₁≤nm₂ nm₁≤nm₃) = n₁≤n₂

  ≤ᴹ⇒≤ : {nm₁ nm₂ : TermMetric X} → (nm₁ ≤ᴹ nm₂) → (⟪ nm₁ ⟫ ≤ ⟪ nm₂ ⟫)
  ≤ᴹ⇒≤ (≤-Unit n₁≤n₂) = n₁≤n₂
  --≤ᴹ⇒≤ (≤-V n₁≤n₂ w₁≤w₂ c₁≤c₂) = +-≤-cong (+-≤-cong n₁≤n₂ w₁≤w₂) (≤ᶜˢⁿ-decr w₁≤w₂ c₁≤c₂)
  ≤ᴹ⇒≤ (≤-V n₁≤n₂ w₁≤w₂) = +-≤-cong n₁≤n₂ w₁≤w₂
  ≤ᴹ⇒≤ (≤-⇒ n₁≤n₂ nm₁≤nm₂) = +-≤-cong n₁≤n₂ (≤ᴹ⇒≤ nm₁≤nm₂)
  ≤ᴹ⇒≤ (≤-× n₁≤n₂ nm₁≤nm₃ nm₂≤nm₄) = +-≤-cong (+-≤-cong n₁≤n₂ (≤ᴹ⇒≤ nm₁≤nm₃)) (≤ᴹ⇒≤ nm₂≤nm₄)


  --------------------------------------------------------------------

  postulate
    extensionality : ∀ {A B : Set} {f g : A → B}
      → (∀ (x : A) → f x ≡ g x)
        -----------------------
      → f ≡ g

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

  EElem : Ty → Set
  EElem X = (Σ[ f ∈ (List (ℕ × ℕ) → TermMetric X) ] ({csn₁ csn₂ : List (ℕ × ℕ)} → csn₁ ≤ᶜˢⁿ csn₂ → f csn₁ ≤ᴹ f csn₂))

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

  data WkX  : {E E' : EMetric} → (π : Wk Γ Γ') → (ϖ : WkN Γ E) → (ϖ' : WkN Γ' E') → Set where
    wkx-bc       : {E E' : EMetric} → {π : Wk Γ Γ'} → {ϖ : WkN Γ E} → {ϖ' : WkN Γ' E'} → (θ : WkE π ϖ ϖ') → WkX π ϖ ϖ'
    wkx-cong     :   {E E' : EMetric}
                  → {π : Wk Γ Γ'} → {ϖ : WkN Γ E} → {ϖ' : WkN Γ' E'}
                  → {nm₁ nm₂ : EElem X}
                  → (nm₁≤nm₂ : ((csn : (List (ℕ × ℕ))) → (proj₁ nm₁ csn) ≤ᴹ (proj₁ nm₂ csn)))
                  → (ϖ≤ϖ' : WkX π ϖ ϖ') → WkX (wk-cong π) (wkn-cong {e = nm₁} ϖ) (wkn-cong {e = nm₂} ϖ')
    wkx-wk       :   {E E' : EMetric}
                  → {π : Wk Γ Γ'} → {ϖ : WkN Γ E} → {ϖ' : WkN Γ' E'}
                  → (ϖ≤ϖ' : WkX π ϖ ϖ') → WkX (wk-cong π) (wkn-cons {Y = Y} ϖ) (wkn-cons {Y = Y} ϖ')

  wkx-id : {π : Wk Γ Γ} → {E : EMetric} → {ϖ : WkN Γ E} → WkX π ϖ ϖ
  wkx-id {π = π} {E = E} {ϖ = ϖ} = wkx-bc wke-id

  wkx-z-r : {e : Σ[ X ∈ Ty ] (EElem X)} {E' : EMetric} {π : Wk Γ Γ} {ϖ : WkN Γ (e ∷ E')}  {ϖ' : WkN Γ []} → (ϕ : WkX π ϖ ϖ') → ⊥
  wkx-z-r (wkx-bc θ) = wke-z-r θ
  wkx-z-r (wkx-wk ϕ) = wkx-z-r ϕ

  wkx-z-l : {e : Σ[ X ∈ Ty ] (EElem X)} {E' : EMetric} {π : Wk Γ Γ'} {ϖ : WkN Γ []} {ϖ' : WkN Γ' (e ∷ E')} → (ϕ : WkX π ϖ ϖ') → ⊥
  wkx-z-l (wkx-bc θ) = wke-z-l θ
  wkx-z-l (wkx-wk ϕ) = wkx-z-l ϕ

  lookup-mono-metric : (i : Γ ∋ Y) → (E : EMetric) → WkN Γ E → EElem Y
  lookup-mono-metric Cx.h ((Y , e) ∷ ne) (wkn-cong ϖ) = e
  lookup-mono-metric (Cx.t i) ((X , e) ∷ ne) (wkn-cong ϖ) = lookup-mono-metric i ne ϖ
  lookup-mono-metric {Y = Y} Cx.h [] (wkn-cons ϖ) = (λ _ → zero-metric) , λ _ → ≤ᴹ-refl
  lookup-mono-metric {Y = Y} Cx.h (x ∷ E) (wkn-cons ϖ) = (λ _ → zero-metric) , λ _ → ≤ᴹ-refl
  lookup-mono-metric {Y = Y} (Cx.t i) [] (wkn-cons ϖ) = (λ _ → zero-metric) , λ _ → ≤ᴹ-refl
  lookup-mono-metric (Cx.t i) (x ∷ E) (wkn-cons ϖ) = lookup-mono-metric i (x ∷ E) ϖ

  empty-lookup : (i : Γ ∋ X) → (ϖ : WkN Γ []) → lookup-mono-metric i [] ϖ ≡ ((λ _ → zero-metric) , λ _ → ≤ᴹ-refl)
  empty-lookup Cx.h (wkn-cons ϖ) = refl
  empty-lookup (Cx.t i) (wkn-cons ϖ) = refl

  mutual

    mono-val-count : (i : Γ ∋ X) → (M : Val Γ Z) → (E : EMetric) → WkN Γ E
                             → Σ[ f ∈ (List (ℕ × ℕ) → ℕ) ] ({csn₁ csn₂ : List (ℕ × ℕ)} → csn₁ ≤ᶜˢⁿ csn₂ → f csn₁ ≡ f csn₂)

    mono-val-count Cx.h (var Cx.h) E ϖ = (λ _ → 1) , λ _ → refl --λ _ → s≤s z≤n
    mono-val-count Cx.h (var (Cx.t i)) E ϖ = (λ _ → 0) , λ _ → refl --λ _ → z≤n
    mono-val-count (Cx.t i) (var Cx.h) E ϖ = (λ _ → 0) , λ _ → refl --λ _ → z≤n
    mono-val-count (Cx.t i₁) (var (Cx.t i₂)) ((B , e) ∷ E) (wkn-cong ϖ) =
      let
        IH = mono-val-count i₁ (var i₂) E ϖ
      in
      (proj₁ IH) , proj₂ IH --proj₂ IH
    mono-val-count (Cx.t i₁) (var (Cx.t i₂)) [] (wkn-cons ϖ) =
      let
        IH = mono-val-count i₁ (var i₂) [] ϖ
      in
      (proj₁ IH) , proj₂ IH --proj₂ IH
    mono-val-count (Cx.t i₁) (var (Cx.t i₂)) (x ∷ E) (wkn-cons ϖ) =
      let
        IH = mono-val-count i₁ (var i₂) (x ∷ E) ϖ
      in
      (proj₁ IH) ,
      proj₂ IH --proj₂ IH

    mono-val-count Cx.h (lam W) E ϖ = mono-comp-count (t h) W E (wkn-cons ϖ)
    mono-val-count (Cx.t i) (lam W) E ϖ = mono-comp-count (t (t i)) W E (wkn-cons ϖ)

    mono-val-count Cx.h (pair M N) E ϖ =
      let
        IH1 = mono-val-count h M E ϖ
        IH2 = mono-val-count h N E ϖ
      in
      (λ csn → (proj₁ IH1) csn + (proj₁ IH2) csn) ,
      λ c≡c' → cong₂ _+_ ((proj₂ IH1) c≡c') ((proj₂ IH2) c≡c') --λ c≤c' → +-≤-cong ((proj₂ IH1) c≤c') ((proj₂ IH2) c≤c')
    mono-val-count (Cx.t i) (pair M N) E ϖ =
      let
        IH1 = mono-val-count (t i) M E ϖ
        IH2 = mono-val-count (t i) N E ϖ
      in
      (λ csn → (proj₁ IH1) csn + (proj₁ IH2) csn) ,
      λ c≡c' → cong₂ _+_ ((proj₂ IH1) c≡c') ((proj₂ IH2) c≡c') --λ c≤c' → +-≤-cong ((proj₂ IH1) c≤c') ((proj₂ IH2) c≤c')

    mono-val-count Cx.h (pm M N) E ϖ =
      let
        IH1 = mono-val-count h M E ϖ
        IH2 = mono-val-count h N E (wkn-cons (wkn-cons ϖ))
        IH3 = mono-val-count (t h) N E (wkn-cons (wkn-cons ϖ))
        IH4 = mono-val-count (t (t h)) N E (wkn-cons (wkn-cons ϖ))
      in
      (λ csn → (proj₁ IH1 ) csn * (suc ((proj₁ IH2) csn + (proj₁ IH3) csn)) + (proj₁ IH4) csn) ,
      λ c≡c' → cong₂ _+_ (cong₂ _*_ ((proj₂ IH1) c≡c') (cong suc (cong₂ _+_ ((proj₂ IH2) c≡c') ((proj₂ IH3) c≡c')))) ((proj₂ IH4) c≡c')
      --λ c≤c' → +-≤-cong (*-≤-cong ((proj₂ IH1) c≤c') (s≤s (+-≤-cong ((proj₂ IH2) c≤c') ((proj₂ IH3) c≤c')))) ((proj₂ IH4) c≤c')
    mono-val-count (Cx.t i) (pm M N) E ϖ =
      let
        IH1 = mono-val-count (t i) M E ϖ
        IH2 = mono-val-count h N E (wkn-cons (wkn-cons ϖ))
        IH3 = mono-val-count (t h) N E (wkn-cons (wkn-cons ϖ))
        IH4 = mono-val-count (t (t (t i))) N E (wkn-cons (wkn-cons ϖ))
      in
      (λ csn → (proj₁ IH1 ) csn * (suc ((proj₁ IH2) csn + (proj₁ IH3) csn)) + (proj₁ IH4) csn) ,
      (λ c≡c' → cong₂ _+_ (cong₂ _*_ ((proj₂ IH1) c≡c') (cong suc (cong₂ _+_ ((proj₂ IH2) c≡c') ((proj₂ IH3) c≡c')))) ((proj₂ IH4) c≡c'))
      --(λ c≤c' → +-≤-cong (*-≤-cong ((proj₂ IH1) c≤c') (s≤s (+-≤-cong ((proj₂ IH2) c≤c') ((proj₂ IH3) c≤c')))) ((proj₂ IH4) c≤c'))

    mono-val-count Cx.h unit E ϖ = (λ _ → 0) , (λ _ → refl) --λ _ → z≤n
    mono-val-count (Cx.t i) unit E ϖ = (λ _ → 0) , (λ _ → refl) --λ _ → z≤n

    mono-comp-count : (i : Γ ∋ X) → (M : Comp Γ Z) → (E : EMetric) → WkN Γ E
                             → Σ[ f ∈ (List (ℕ × ℕ) → ℕ) ] ({csn₁ csn₂ : List (ℕ × ℕ)} → csn₁ ≤ᶜˢⁿ csn₂ → f csn₁ ≡ f csn₂)
    mono-comp-count i (return M) E ϖ = mono-val-count i M E ϖ
    mono-comp-count i (pm M W) E ϖ =
      let
        IH1 = mono-val-count i M E ϖ
        IH2 = mono-comp-count h W E (wkn-cons (wkn-cons ϖ))
        IH3 = mono-comp-count (t h) W E (wkn-cons (wkn-cons ϖ))
        IH4 = mono-comp-count (t (t i)) W E (wkn-cons (wkn-cons ϖ))
      in
      (λ csn → (proj₁ IH1 ) csn * (suc ((proj₁ IH2) csn + (proj₁ IH3) csn)) + (proj₁ IH4) csn) ,
      {!!} --λ c≤c' → +-≤-cong (*-≤-cong ((proj₂ IH1) c≤c') (s≤s (+-≤-cong ((proj₂ IH2) c≤c') ((proj₂ IH3) c≤c')))) ((proj₂ IH4) c≤c')
    mono-comp-count i (push W₁ W₂) E ϖ =
      let
        IH1 = mono-comp-count i W₁ E ϖ
        IH2 = mono-comp-count h W₂ E (wkn-cons ϖ)
        IH3 = mono-comp-count (t i) W₂ E (wkn-cons ϖ)
      in
      (λ csn → (proj₁ IH1) csn * (suc ((proj₁ IH2) csn)) + (proj₁ IH3) csn) ,
      (λ c≡c' → cong₂ _+_ (cong₂ _*_ ((proj₂ IH1) c≡c') (cong suc ((proj₂ IH2) c≡c'))) ((proj₂ IH3) c≡c'))
      --(λ c≤c' → +-≤-cong (*-≤-cong ((proj₂ IH1) c≤c') (s≤s ((proj₂ IH2) c≤c'))) ((proj₂ IH3) c≤c'))
    mono-comp-count i (app M N) E ϖ =
      let
        IH1 = mono-val-count i M E ϖ
        IH2 = mono-val-count i N E ϖ
        IH3 = val-mono-metric M E ϖ
      in
      (λ csn → (proj₁ IH1) csn + (proj₁ IH2) csn * (suc (p2 ((proj₁ IH3) csn)))) ,
      λ c≡c' → cong₂ _+_ ((proj₂ IH1) c≡c') (cong₂ _*_ ((proj₂ IH2) c≡c') (cong suc (≤ᴹ-p2 ((proj₂ IH3) c≡c'))))
      --λ c≤c' → +-≤-cong ((proj₂ IH1) c≤c') (*-≤-cong ((proj₂ IH2) c≤c') (s≤s (≡⇒≤ (≤ᴹ-p2 ((proj₂ IH3) c≤c')))))
    mono-comp-count i (var M) E ϖ = mono-val-count i M E ϖ
    mono-comp-count i (sub W₁ W₂) E ϖ =
      let
        IH1 = mono-comp-count (t i) W₁ E (wkn-cons ϖ)
        IH2 = mono-comp-count i W₂ E ϖ
        IH3 = mono-comp-count h W₁ E (wkn-cons ϖ)
      in
      (λ csn → (proj₁ IH1) csn + (proj₁ IH2) csn * (suc ((proj₁ IH3) csn))) ,
      (λ c≡c' → cong₂ _+_ ((proj₂ IH1) c≡c') (cong₂ _*_ ((proj₂ IH2) c≡c') (cong suc ((proj₂ IH3) c≡c'))))
      --(λ c≤c' → +-≤-cong ((proj₂ IH1) c≤c') (*-≤-cong ((proj₂ IH2) c≤c') (s≤s ((proj₂ IH3) c≤c'))))

    val-mono-metric : (M : Val Γ Y) → (E : EMetric) → WkN Γ E → EElem Y
    val-mono-metric (var i) E ϖ =
      let
        IH = lookup-mono-metric i E ϖ
      in
      (λ csn → incr 2 ((proj₁ IH) csn)) , λ c≤c' → ≤ᴹ-incr-cong (≤-refl {n = 2}) ((proj₂ IH) c≤c')
    val-mono-metric (lam W) E ϖ =
      let
        IH1 = mono-comp-count h W E (wkn-cons ϖ)
        IH2 = comp-mono-metric W E (wkn-cons ϖ)
      in
      (λ csn → incr 2 (m-⇒ 0 ((proj₁ IH1) csn) ((proj₁ IH2) csn))) ,
      λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' →
         let
           cnt-eq = (proj₂ IH1) c≤c'
         in
         subst (λ x → m-⇒ 2 (proj₁ IH1 csn₁) (proj₁ IH2 csn₁) ≤ᴹ m-⇒ 2 x (proj₁ IH2 csn₂))
               cnt-eq
               (≤-⇒ (s≤s (s≤s z≤n)) ((proj₂ IH2) c≤c'))
    val-mono-metric (pair M₁ M₂) E ϖ =
      let
        IH1 = val-mono-metric M₁ E ϖ
        IH2 = val-mono-metric M₂ E ϖ
      in
      (λ csn → incr 2 (m-× 0 ((proj₁ IH1) csn) ((proj₁ IH2) csn))) ,
      λ c≤c' → ≤-× ≤-refl ((proj₂ IH1) c≤c') ((proj₂ IH2) c≤c')
    val-mono-metric (pm {A = X} {B = Y} M N) E ϖ =
      let
        IH1 = val-mono-metric M E ϖ
        IH2 = val-mono-metric N E (wkn-cons (wkn-cons ϖ))
        r1 = λ c → rhs ((proj₁ IH1) c)
        l1 = λ c → lhs ((proj₁ IH1) c)
        IH3 = val-mono-metric N ((Y , r1 , λ c≤c' → ≤ᴹ-rhs ((proj₂ IH1) c≤c')) ∷ (X , l1 , λ c≤c' → ≤ᴹ-lhs ((proj₂ IH1) c≤c')) ∷ E) (wkn-cong (wkn-cong ϖ))
      in
      (λ csn → incr (suc (vx ((proj₁ IH1) csn) + ⟪ (proj₁ IH2) csn ⟫)) ((proj₁ IH3) csn)) ,
      λ c≤c' → ≤ᴹ-incr-cong (+-≤-cong (s≤s (≤ᴹ-vx ((proj₂ IH1) c≤c'))) (≤ᴹ⇒≤ ((proj₂ IH2) c≤c'))) ((proj₂ IH3) c≤c')
    val-mono-metric unit E ϖ = (λ _ → m-Unit 2) , (λ {csn₁} {csn₂} z → ≤-Unit (s≤s (s≤s z≤n)))

    comp-mono-metric : (W : Comp Γ Y) → (E : EMetric) → WkN Γ E → EElem Y
    comp-mono-metric (return M) E ϖ =
      let
        IH = val-mono-metric M E ϖ
      in
      (λ csn → incr 2 ((proj₁ IH) csn)) , λ c≤c' → ≤ᴹ-incr-cong (≤-refl {n = 2}) ((proj₂ IH) c≤c')
    comp-mono-metric (pm {A = X} {B = Y} M W) E ϖ =
      let
        IH1 = val-mono-metric M E ϖ
        IH2 = comp-mono-metric W E (wkn-cons (wkn-cons ϖ))
        r1 = λ c → rhs ((proj₁ IH1) c)
        l1 = λ c → lhs ((proj₁ IH1) c)
        IH3 = comp-mono-metric W ((Y , r1 , λ c≤c' → ≤ᴹ-rhs ((proj₂ IH1) c≤c')) ∷ (X , l1 , λ c≤c' → ≤ᴹ-lhs ((proj₂ IH1) c≤c')) ∷ E) (wkn-cong (wkn-cong ϖ))
      in
      (λ csn → incr (suc (vx ((proj₁ IH1) csn) + ⟪ (proj₁ IH2) csn ⟫)) ((proj₁ IH3) csn)) ,
      λ c≤c' → ≤ᴹ-incr-cong (+-≤-cong (s≤s (≤ᴹ-vx ((proj₂ IH1) c≤c'))) (≤ᴹ⇒≤ ((proj₂ IH2) c≤c'))) ((proj₂ IH3) c≤c')
    comp-mono-metric (push {A = X} W₁ W₂) E ϖ =
      let
        IH1 = comp-mono-metric W₂ E (wkn-cons ϖ)
        IH2 = mono-comp-count h W₂ E (wkn-cons ϖ)
        IH3 = comp-mono-metric W₁ E ϖ
        cs' = λ csn → (((proj₁ IH2) csn , ⟪ (proj₁ IH1) csn ⟫) ∷ csn)
        IH3' = λ csn → ⟪ (proj₁ IH3) (cs' csn) ⟫
        IH4 = mono-comp-count h W₂ E (wkn-cons ϖ)
      in
         (λ csn → incr (suc ((2+ ((proj₁ IH4) csn)) * (IH3' csn))) ((proj₁ IH1) csn)) ,
         λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' →
           let
             le  = (proj₂ IH2) c≤c'
             le1 = ≤ᴹ⇒≤ ((proj₂ IH3) ([s≤s] {cnt = (proj₁ IH2) csn₁} ((≤ᴹ⇒≤ ((proj₂ IH1) c≤c'))) c≤c'))
             le2 = subst
              (λ x →   ⟪ comp-mono-metric W₁ E ϖ .proj₁ ((proj₁ IH2 csn₁ , ⟪ comp-mono-metric W₂ E (wkn-cons ϖ) .proj₁ csn₁ ⟫) ∷ csn₁) ⟫
                     ≤ ⟪ comp-mono-metric W₁ E ϖ .proj₁ ((x , ⟪ comp-mono-metric W₂ E (wkn-cons ϖ) .proj₁ csn₂ ⟫) ∷ csn₂) ⟫)
              le
              le1
             le4 = +-≤-cong le2 (+-≤-cong le2 (*-≤-cong ((≡⇒≤ ((proj₂ IH2) c≤c'))) le2))
           in
           ≤ᴹ-incr-cong (s≤s le4) ((proj₂ IH1) c≤c')

    comp-mono-metric (app M N) E ϖ =
      let
        IH1 = val-mono-metric M E ϖ
        IH2 = val-mono-metric N E ϖ
      in
      (λ csn → incr (2 + ((p1 (proj₁ IH1 csn)) + ((suc (p2 (proj₁ IH1 csn))) * ⟪ proj₁ IH2 csn ⟫))) (p3 (proj₁ IH1 csn))) ,
      λ c≤c' →
        let
          le1 = +-≤-cong (≤ᴹ-p1 (proj₂ IH1 c≤c')) (+-≤-cong (≤ᴹ⇒≤ (proj₂ IH2 c≤c')) (*-≤-cong (≡⇒≤ (≤ᴹ-p2 (proj₂ IH1 c≤c'))) (≤ᴹ⇒≤ (proj₂ IH2 c≤c'))))
        in
        ≤ᴹ-incr-cong (s≤s (s≤s le1)) (≤ᴹ-p3 (proj₂ IH1 c≤c'))
    comp-mono-metric (var M) E ϖ =
      let
        IH = val-mono-metric M E ϖ
      in
      (λ csn → incr (suc ⟪ (proj₁ IH) csn ⟫) zero-metric) , λ c≤c' → ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ ((proj₂ IH) c≤c'))) (≤ᴹ-refl {nm = zero-metric})
    comp-mono-metric (sub {Γ = Γ} W₁ W₂) E ϖ =
      let
        IH = comp-mono-metric W₂ E ϖ
        --IH2 = comp-mono-metric W₁ (((`V , λ _ → m-V 0 (w + csn-to-nat₀ w csn))) , ? ∷ E) (wkn-cong ϖ)
        θ : WkE wk-id ϖ ϖ
        θ = wke-id
      in
      (λ csn → proj₁ (comp-mono-metric W₁ ((`V , (λ _ → m-V 0 (⟪ proj₁ IH csn ⟫ + csn-to-nat₀ ⟪ proj₁ IH csn ⟫ csn)) , λ c≤c' → ≤ᴹ-refl) ∷ E) (wkn-cong ϖ)) csn) ,
      λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' → 
        let
          le : csn-to-nat₀ ⟪ proj₁ IH csn₁ ⟫ csn₁ ≤ csn-to-nat₀ ⟪ proj₁ IH csn₂ ⟫ csn₂
          le = ≤ᶜˢⁿ-decr (≤ᴹ⇒≤ (proj₂ IH c≤c')) c≤c'
          le1 : (m-V 0 (⟪ proj₁ IH csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ IH csn₁ ⟫ csn₁)) ≤ᴹ (m-V 0 (⟪ proj₁ IH csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ IH csn₂ ⟫ csn₂))
          le1 = ≤-V z≤n (+-≤-cong (≤ᴹ⇒≤ (proj₂ IH c≤c')) le)
          ϖ₁ : WkN (Γ ∙ `V) ((`V , (λ _ → m-V 0 (⟪ proj₁ IH csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ IH csn₁ ⟫ csn₁)) , λ c≤c' → ≤ᴹ-refl) ∷ E)
          ϖ₁ = wkn-cong ϖ
          ϖ₂ : WkN (Γ ∙ `V) ((`V , (λ _ → m-V 0 (⟪ proj₁ IH csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ IH csn₂ ⟫ csn₂)) , λ c≤c' → ≤ᴹ-refl) ∷ E)
          ϖ₂ = wkn-cong ϖ
          ϕ : WkX wk-id ϖ₁ ϖ₂
          ϕ = wkx-cong (λ csn → le1) wkx-id
          a0 = comp-wkx-lemma
                  W₁
                  ((`V , (λ _ → m-V 0 (⟪ proj₁ IH csn₁ ⟫ + csn-to-nat₀ ⟪ proj₁ IH csn₁ ⟫ csn₁)) , λ c≤c' → ≤ᴹ-refl) ∷ E)
                  ((`V , (λ _ → m-V 0 (⟪ proj₁ IH csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ IH csn₂ ⟫ csn₂)) , λ c≤c' → ≤ᴹ-refl) ∷ E)
                  wk-id
                  ϖ₁
                  ϖ₂
                  ϕ
                  csn₁
          a1 = proj₂ (comp-mono-metric W₁ ((`V , (λ _ → m-V 0 (⟪ proj₁ IH csn₂ ⟫ + csn-to-nat₀ ⟪ proj₁ IH csn₂ ⟫ csn₂)) , (λ c≤c'' → ≤-V z≤n ≤-refl)) ∷ E) (wkn-cong ϖ)) c≤c'
        in
        ≤ᴹ-trans a0 a1

    postulate comp-count-wkx-lemma : (i : Γ ∋ Y) → (W : Comp Γ X) → (E E' : EMetric)
                → (π : Wk Γ Γ) → (ϖ : WkN Γ E) → (ϖ' : WkN Γ E') → (ϕ : WkX π ϖ ϖ') → (csn : List (ℕ × ℕ))
                → (proj₁ (mono-comp-count i W E' ϖ') csn) ≡ (proj₁ (mono-comp-count i W E ϖ) csn)

    postulate val-wkx-lemma : (W : Val Γ X) → (E E' : EMetric) → (π : Wk Γ Γ) → (ϖ : WkN Γ E) → (ϖ' : WkN Γ E') → (ϕ : WkX π ϖ ϖ')
                → (csn : List (ℕ × ℕ)) → (proj₁ (val-mono-metric W E ϖ)) csn ≤ᴹ (proj₁ (val-mono-metric W E' ϖ')) csn

    comp-wkx-lemma : (W : Comp Γ X) → (E E' : EMetric) → (π : Wk Γ Γ) → (ϖ : WkN Γ E) → (ϖ' : WkN Γ E') → (ϕ : WkX π ϖ ϖ')
                → (csn : List (ℕ × ℕ)) → (proj₁ (comp-mono-metric W E ϖ)) csn ≤ᴹ (proj₁ (comp-mono-metric W E' ϖ')) csn

    comp-wkx-lemma (return M) E E' π ϖ ϖ' ϕ csn = ≤ᴹ-incr-cong (≤-refl {n = 2}) (val-wkx-lemma M E E' π ϖ ϖ' ϕ csn)
    comp-wkx-lemma (pm {Γ = Γ} {A = A} {B = B} M W) E E' π ϖ ϖ' ϕ csn =
      let
        a0 c = val-wkx-lemma M E E' π ϖ ϖ' ϕ c
        avx c = ≤ᴹ-vx (a0 c)
        al c = ≤ᴹ-lhs (a0 c)
        ar c = ≤ᴹ-rhs (a0 c)
        E₁ = ((B , (λ c → rhs (proj₁ (val-mono-metric M E ϖ) c)) , λ {_} {_} c≤c' → ≤ᴹ-rhs (proj₂ (val-mono-metric M E ϖ) c≤c')) ∷ (A , (λ c → lhs (proj₁ (val-mono-metric M E ϖ) c)) , λ {_} {_} c≤c' → ≤ᴹ-lhs (proj₂ (val-mono-metric M E ϖ) c≤c')) ∷ E)
        E₂ = ((B , (λ c → rhs (proj₁ (val-mono-metric M E' ϖ') c)) , λ {_} {_} c≤c' → ≤ᴹ-rhs (proj₂ (val-mono-metric M E' ϖ') c≤c')) ∷ (A , (λ c → lhs (proj₁ (val-mono-metric M E' ϖ') c)) , λ {_} {_} c≤c' → ≤ᴹ-lhs (proj₂ (val-mono-metric M E' ϖ') c≤c')) ∷ E')
        ϖ₁ : WkN (Γ ∙ A ∙ B) E₁
        ϖ₁ = wkn-cong (wkn-cong ϖ)
        ϖ₂ : WkN (Γ ∙ A ∙ B) E₂
        ϖ₂ = wkn-cong (wkn-cong ϖ')
        b0 = comp-wkx-lemma W E E' (wk-cong (wk-cong π)) (wkn-cons (wkn-cons ϖ)) (wkn-cons (wkn-cons ϖ')) (wkx-wk (wkx-wk ϕ)) csn
        b1 = comp-wkx-lemma W E₁ E₂ (wk-cong (wk-cong π)) (wkn-cong (wkn-cong ϖ)) (wkn-cong (wkn-cong ϖ')) (wkx-cong ar (wkx-cong al ϕ)) csn
      in
      ≤ᴹ-incr-cong (+-≤-cong (s≤s (avx csn)) (≤ᴹ⇒≤ b0)) b1
    comp-wkx-lemma (push W₁ W₂) E E' π ϖ ϖ' ϕ csn =
      let
        a0 = comp-wkx-lemma W₁ E E' π ϖ ϖ' ϕ
        a1 = comp-wkx-lemma W₂ E E' (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wkx-wk ϕ)
        a2 = comp-count-wkx-lemma h W₂ E E' (wk-cong π) (wkn-cons ϖ) (wkn-cons ϖ') (wkx-wk ϕ)
        c≤c' : ((proj₁ (mono-comp-count h W₂ E (wkn-cons ϖ)) csn , ⟪ proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)) csn ⟫) ∷ csn) ≤ᶜˢⁿ
             ((proj₁ (mono-comp-count h W₂ E' (wkn-cons ϖ')) csn , ⟪ proj₁ (comp-mono-metric W₂ E' (wkn-cons ϖ')) csn ⟫) ∷ csn)
        c≤c' = subst
               (λ x → (((proj₁ (mono-comp-count h W₂ E (wkn-cons ϖ)) csn , ⟪ proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)) csn ⟫) ∷ csn) ≤ᶜˢⁿ ((x , ⟪ proj₁ (comp-mono-metric W₂ E' (wkn-cons ϖ')) csn ⟫) ∷ csn)))
               (sym (a2 csn))
               ([s≤s] (≤ᴹ⇒≤ (a1 csn)) [c≤c])
        a3 = proj₂ (comp-mono-metric W₁ E' ϖ') c≤c'
        a4 = ≤ᴹ-trans (a0 ((proj₁ (mono-comp-count h W₂ E (wkn-cons ϖ)) csn , ⟪ proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)) csn ⟫) ∷ csn)) a3
        b1 = +-≤-cong (≤ᴹ⇒≤ a4) (+-≤-cong (≤ᴹ⇒≤ a4) (*-≤-cong (≤-refl {n = proj₁ (mono-comp-count h W₂ E (wkn-cons ϖ)) csn}) (≤ᴹ⇒≤ a4)))
        b2 = s≤s (subst (λ x → ⟪ proj₁ (comp-mono-metric W₁ E ϖ) ((proj₁ (mono-comp-count h W₂ E (wkn-cons ϖ)) csn , ⟪ proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)) csn ⟫) ∷ csn) ⟫ + (⟪ proj₁ (comp-mono-metric W₁ E ϖ) ((proj₁ (mono-comp-count h W₂ E (wkn-cons ϖ)) csn , ⟪ proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)) csn ⟫) ∷ csn) ⟫ + proj₁ (mono-comp-count h W₂ E (wkn-cons ϖ)) csn * ⟪ proj₁ (comp-mono-metric W₁ E ϖ) ((proj₁ (mono-comp-count h W₂ E (wkn-cons ϖ)) csn , ⟪ proj₁ (comp-mono-metric W₂ E (wkn-cons ϖ)) csn ⟫) ∷ csn) ⟫) ≤ ⟪ comp-mono-metric W₁ E' ϖ' .proj₁ ((proj₁ (mono-comp-count h W₂ E' (wkn-cons ϖ')) csn , ⟪ proj₁ (comp-mono-metric W₂ E' (wkn-cons ϖ')) csn ⟫) ∷ csn) ⟫ + (⟪ comp-mono-metric W₁ E' ϖ' .proj₁ ((proj₁ (mono-comp-count h W₂ E' (wkn-cons ϖ')) csn , ⟪ proj₁ (comp-mono-metric W₂ E' (wkn-cons ϖ')) csn ⟫) ∷ csn) ⟫ + x * ⟪ comp-mono-metric W₁ E' ϖ' .proj₁ ((proj₁ (mono-comp-count h W₂ E' (wkn-cons ϖ')) csn , ⟪ proj₁ (comp-mono-metric W₂ E' (wkn-cons ϖ')) csn ⟫) ∷ csn) ⟫)) (sym (a2 csn)) b1)
      in
      ≤ᴹ-incr-cong b2 (a1 csn)
    comp-wkx-lemma (app M N) E E' π ϖ ϖ' ϕ csn rewrite ≤ᴹ-p2 (val-wkx-lemma M E E' π ϖ ϖ' ϕ csn) =
      let
        a0 = val-wkx-lemma M E E' π ϖ ϖ' ϕ
        a1 = val-wkx-lemma N E E' π ϖ ϖ' ϕ
        b-p1 = ≤ᴹ-p1 (a0 csn)
        b-p2 = ≤ᴹ-p2 (a0 csn)
        b-p3 = ≤ᴹ-p3 (a0 csn)
        c1 = s≤s $ s≤s $ +-≤-cong b-p1 (+-≤-cong (≤ᴹ⇒≤ (a1 csn)) (*-≤-cong (≤-refl {n = p2 (proj₁ (val-mono-metric M E' ϖ') csn)}) (≤ᴹ⇒≤ (a1 csn))))
      in
      ≤ᴹ-incr-cong c1 b-p3
    comp-wkx-lemma (var M) E E' π ϖ ϖ' ϕ csn = ≤ᴹ-incr-cong (s≤s (≤ᴹ⇒≤ (val-wkx-lemma M E E' π ϖ ϖ' ϕ csn))) (≤ᴹ-refl {nm = zero-metric})
    comp-wkx-lemma (sub W₁ W₂) E E' π ϖ ϖ' ϕ csn =
      let
        a0 = comp-wkx-lemma W₂ E E' π ϖ ϖ' ϕ
        a1 = comp-wkx-lemma
                W₁
                ((`V , (λ _ → m-V 0 (⟪ proj₁ (comp-mono-metric W₂ E ϖ) csn ⟫ + csn-to-nat₀ ⟪ proj₁ (comp-mono-metric W₂ E ϖ) csn ⟫ csn)) , (λ c≤c' → ≤-V z≤n ≤-refl)) ∷ E)
                ((`V , (λ _ → m-V 0 (⟪ proj₁ (comp-mono-metric W₂ E' ϖ') csn ⟫ + csn-to-nat₀ ⟪ proj₁ (comp-mono-metric W₂ E' ϖ') csn ⟫ csn)) , (λ c≤c' → ≤-V z≤n ≤-refl)) ∷ E')
                (wk-cong π) (wkn-cong ϖ) (wkn-cong ϖ')
                (wkx-cong (λ c → ≤-V z≤n (+-≤-cong (≤ᴹ⇒≤ (a0 csn)) (≤ᶜˢⁿ-decr (≤ᴹ⇒≤ (a0 csn)) ([c≤c] {csn = csn})))) ϕ)

      in
      a1 csn


    v̲a̲l̲-mono-metric : (M : V̲a̲l̲ Γ Y) → (E : EMetric) → WkN Γ E → EElem Y
    v̲a̲l̲-mono-metric (l̲a̲m̲ W) E ϖ =
      let
        IH1 = mono-comp-count h W E (wkn-cons ϖ)
        IH2 = comp-mono-metric W E (wkn-cons ϖ)
      in
      (λ csn → incr 1 (m-⇒ 0 ((proj₁ IH1) csn) ((proj₁ IH2) csn))) ,
      λ {csn₁ = csn₁} {csn₂ = csn₂} c≤c' →
         let
           cnt-eq = (proj₂ IH1) c≤c'
         in
         subst (λ x → m-⇒ 1 (proj₁ IH1 csn₁) (proj₁ IH2 csn₁) ≤ᴹ m-⇒ 1 x (proj₁ IH2 csn₂))
               cnt-eq
               (≤-⇒ (s≤s z≤n) ((proj₂ IH2) c≤c'))
    v̲a̲l̲-mono-metric (pa̲i̲r̲ M₁ M₂) E ϖ =
      let
        IH1 = v̲a̲l̲-mono-metric M₁ E ϖ
        IH2 = v̲a̲l̲-mono-metric M₂ E ϖ
      in
      (λ csn → incr 1 (m-× 0 ((proj₁ IH1) csn) ((proj₁ IH2) csn))) ,
      λ c≤c' → ≤-× ≤-refl ((proj₂ IH1) c≤c') ((proj₂ IH2) c≤c')
    v̲a̲l̲-mono-metric u̲n̲i̲t̲ E ϖ = (λ _ → m-Unit 1) , (λ {csn₁} {csn₂} z → ≤-Unit (s≤s z≤n))
    v̲a̲l̲-mono-metric (v̲a̲r̲ i) E ϖ =
      let
        IH = lookup-mono-metric i E ϖ
      in
      (λ csn → incr 1 ((proj₁ IH) csn)) , λ c≤c' → ≤ᴹ-incr-cong (≤-refl {n = 1}) ((proj₂ IH) c≤c')

    c̲o̲m̲p-mono-metric : (W : C̲o̲m̲p Γ Y) → (E : EMetric) → WkN Γ E → EElem Y
    c̲o̲m̲p-mono-metric (r̲e̲t̲u̲r̲n̲ M) E ϖ =
      let
        IH = v̲a̲l̲-mono-metric M E ϖ
      in
      (λ csn → incr 1 ((proj₁ IH) csn)) , λ c≤c' → ≤ᴹ-incr-cong (≤-refl {n = 1}) ((proj₂ IH) c≤c')
    c̲o̲m̲p-mono-metric (a̲pp M N) E ϖ =
      let
        IH1 = val-mono-metric M E ϖ
        IH2 = v̲a̲l̲-mono-metric N E ϖ
      in
      (λ csn → incr (suc ((p1 (proj₁ IH1 csn)) + ((suc (p2 (proj₁ IH1 csn))) * ⟪ proj₁ IH2 csn ⟫))) (p3 (proj₁ IH1 csn))) ,
      λ c≤c' →
        let
          le1 = +-≤-cong (≤ᴹ-p1 (proj₂ IH1 c≤c')) (+-≤-cong (≤ᴹ⇒≤ (proj₂ IH2 c≤c')) (*-≤-cong (≡⇒≤ (≤ᴹ-p2 (proj₂ IH1 c≤c'))) (≤ᴹ⇒≤ (proj₂ IH2 c≤c'))))
        in
        ≤ᴹ-incr-cong (s≤s le1) (≤ᴹ-p3 (proj₂ IH1 c≤c'))

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
      (`V , (λ _ → m-V 0 (⟪ proj₁ IH2 csn ⟫ + csn-to-nat₀ ⟪ proj₁ IH2 csn ⟫ csn)) , λ _ → ≤ᴹ-refl) ∷ (proj₁ IH) , wkn-cong (proj₂ IH)

    cs-to-csn : (cs : CompStack Δ Z) → List (ℕ × ℕ)
    cs-to-csn ◻ = []
    cs-to-csn ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡}) =
      let
        csn = cs-to-csn cs
        IH = env-mono-metric γ
      in
      ((proj₁ (mono-comp-count h W (proj₁ IH) (wkn-cons (proj₂ IH))) csn) , ⟪ proj₁ (comp-mono-metric W (proj₁ IH) (wkn-cons (proj₂ IH))) csn ⟫) ∷ csn

  getIndex : LookupState X → Σ[ Γ ∈ Ctx ] Γ ∋ X
  getIndex ⟨ i ∥ _ ⟩ = _ , i

  getLookupEnv : (S : LookupState X) → Env (proj₁ (getIndex S))
  getLookupEnv ⟨ _ ∥ γ ⟩ = γ


  lstate-metric : LookupState X → EElem X
  lstate-metric ⟨ i ∥ γ ⟩ =
    let
      EP = (env-mono-metric γ)
    in
      lookup-mono-metric i (proj₁ EP) (proj₂ EP)

  lhstate-metric : {T : LookupState X} → LookupHaltingState T → EElem X
  lhstate-metric (found-unit {γ = γ}) = (λ _ → m-Unit 1) , λ _ → ≤ᴹ-refl
  lhstate-metric (found-pair {LHS = LHS} {RHS = RHS} {γ = γ}) = let EP = (env-mono-metric γ) in v̲a̲l̲-mono-metric (pa̲i̲r̲ LHS RHS) (proj₁ EP) (proj₂ EP)
  lhstate-metric (found-lam {W = W} {γ = γ}) = let EP = (env-mono-metric γ) in v̲a̲l̲-mono-metric (l̲a̲m̲ W) (proj₁ EP) (proj₂ EP)
  lhstate-metric (found-comp {W = W} {γ = γ} {cs = cs}) =
    let
      EP = (env-mono-metric γ)
      w = comp-mono-metric W (proj₁ EP) (proj₂ EP)
      csn = (cs-to-csn cs)
    in
      (λ _ → m-V 0 (⟪ proj₁ w csn ⟫ + csn-to-nat₀ ⟪ proj₁ w csn ⟫ csn)) , λ _ → ≤ᴹ-refl

  data LookupSteps : LookupState X → Set where

    steps : {S T : LookupState X} → S →ᴸ* T → (H : LookupHaltingState T) → ⟦ S ⟧ᴸ ≡ ⟦ T ⟧ᴸ → (π : Wk (lCtx S) (lTCtx T)) → (⟦ π ⟧ʷ ⟦ lEnv S ⟧ᴱ ≡ ⟦ lTEnv T ⟧ᴱ)
            → (∀ (csn : List (ℕ × ℕ)) → (proj₁ (lhstate-metric H)) csn ≤ᴹ (proj₁ (lstate-metric S)) csn)
            → (θ : WkE π (proj₂ (env-mono-metric (lEnv S))) (proj₂ (env-mono-metric (lTEnv T))))
            → LookupSteps S

  lookup : (i : Γ ∋ X) → (γ : Env Γ) → LookupSteps {X = X} ⟨ i ∥ γ ⟩
  lookup h (γ ﹐ l̲a̲m̲ W) = steps (⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩ ◼) found-lam refl (wk-wk wk-id) refl ((λ csn → ≤ᴹ-refl)) (wke-wc- wk-id (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric (lTEnv ⟨ h ∥ γ ﹐ l̲a̲m̲ W ⟩))) (v̲a̲l̲-mono-metric (l̲a̲m̲ W) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) wke-id)
  lookup h (γ ﹐ pa̲i̲r̲ LHS RHS) = steps (⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩ ◼) found-pair refl (wk-wk wk-id) refl ((λ csn → ≤ᴹ-refl)) (wke-wc- wk-id (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric (lTEnv ⟨ h ∥ γ ﹐ pa̲i̲r̲ LHS RHS ⟩))) (v̲a̲l̲-mono-metric (pa̲i̲r̲ LHS RHS) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) wke-id)
  lookup h (γ ﹐ u̲n̲i̲t̲) = steps (⟨ h ∥ _﹐_ γ (u̲n̲i̲t̲) ⟩ ◼) found-unit refl (wk-wk wk-id) refl ((λ csn → ≤ᴹ-refl)) (wke-wc- wk-id (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric (lTEnv ⟨ h ∥ γ ﹐ u̲n̲i̲t̲ ⟩))) (v̲a̲l̲-mono-metric u̲n̲i̲t̲ (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) wke-id)
  lookup h (γ ﹐ v̲a̲r̲ i) with lookup i γ
  ... | steps {T = T} i>>T HT i≡T WK w≡γ T≤S θ = steps (_ →ᴸ⟨ val-h-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ ((λ csn → ≤ᴹ-incr-cong (z≤n {n = 1}) (T≤S csn))) (wke-wc- WK (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric (lTEnv T))) (v̲a̲l̲-mono-metric (v̲a̲r̲ i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) θ)
  lookup h ((γ ﹐﹝ W ╎ cs ﹞ ) {π = π} {wk≡ = wk≡}) =
    let
      w = comp-mono-metric W (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))
      csn = (cs-to-csn cs)
    in
      steps (⟨ h ∥ γ ﹐﹝ W ╎ cs ﹞ ⟩ ◼) found-comp refl (wk-wk wk-id) refl ((λ csn → ≤ᴹ-refl)) (wke-wc- wk-id (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric (lTEnv ⟨ h ∥ ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡} ) ⟩))) ((λ _ → m-V 0 (⟪ proj₁ w csn ⟫ + csn-to-nat₀ ⟪ proj₁ w csn ⟫ csn)) , (λ _ → ≤ᴹ-refl)) wke-id)
  lookup (t i) (γ ﹐ M) with lookup i γ
  ... | steps {T = T} i>>T HT i≡T WK w≡γ T≤S θ = steps (_ →ᴸ⟨ val-t-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ T≤S (wke-wc- WK (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric (lTEnv T))) (v̲a̲l̲-mono-metric M (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) θ)
  lookup (t i) (γ ﹐﹝ W ╎ cs ﹞) with lookup i γ
  ... | steps {T = T} i>>T HT i≡T WK w≡γ T≤S θ =
    let
      w = comp-mono-metric W (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))
      csn = (cs-to-csn cs)
    in
      steps (_ →ᴸ⟨ comp-t-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ T≤S (wke-wc- WK (proj₂ (env-mono-metric γ)) (proj₂ (env-mono-metric (lTEnv T))) ((λ _ → m-V 0 (⟪ proj₁ w csn ⟫ + csn-to-nat₀ ⟪ proj₁ w csn ⟫ csn)) , (λ _ → ≤ᴹ-refl)) θ)


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

  -- partial-term-metric : PartialTerm Γ X → (E : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))) → Wkn Γ E → List (ℕ × ℕ) → TermMetric X
  -- partial-term-metric (⭭ M) E ϖ csn = v̲a̲l̲-metric M E ϖ csn
  -- partial-term-metric (⇡ M) E ϖ csn = val-metric M E ϖ csn
  -- partial-term-metric (⇡ᴹ M N) E ϖ csn = val-metric (pm M N) E ϖ csn
  -- partial-term-metric (⇡ᴸ LHS RHS) E ϖ csn = val-metric (pair LHS RHS) E ϖ csn
  -- partial-term-metric (⇡ᴿ LHS RHS) E ϖ csn = val-metric (pair (toVal LHS) RHS) E ϖ csn

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

  --valstate-metric : (S : ValState X) → List (ℕ × ℕ) → TermMetric X
  --valstate-metric (∘ S) csn =
  --  let
  --    e = env-metric (botStackEnv S)
  --  in
  --    partial-term-metric (botStackTerm S) (proj₁ e) (proj₂ e) csn
  --valstate-metric (∙ S) csn =
  --  let
  --    e = env-metric (botStackEnv S)
  --  in
  --     partial-term-metric (botStackTerm S) (proj₁ e) (proj₂ e) csn

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

  data ValSteps : ValState T◾ → Set where

    steps : {S T : ValState T◾} → S ↠ᵛ T → ValHaltingState T → ⟦ S ⟧ᵛꟴ ≡ ⟦ T ⟧ᵛꟴ → (π : Wk (botCtx T) (botCtx S)) → (⟦ π ⟧ʷ ⟦ botEnv T ⟧ᴱ ≡ ⟦ botEnv S ⟧ᴱ)
            → (∀ (csn : List (ℕ × ℕ)) → (proj₁ (valstate-metric T)) csn ≤ᴹ (proj₁ (valstate-metric S)) csn)
            → (θ : WkE π (proj₂ (env-mono-metric (botEnv T))) (proj₂ (env-mono-metric (botEnv S))))
            → ValSteps S

  -- data ValSteps : ValState T◾ → Set where

  --   steps : {S T : ValState T◾} → S ↠ᵛ T → ValHaltingState T → ⟦ S ⟧ᵛꟴ ≡ ⟦ T ⟧ᵛꟴ → (π : Wk (botCtx T) (botCtx S)) → (⟦ π ⟧ʷ ⟦ botEnv T ⟧ᴱ ≡ ⟦ botEnv S ⟧ᴱ)
  --           → (∀ (csn : List (ℕ × ℕ)) → valstate-metric T csn ≤ᴹ valstate-metric S csn)
  --           → (θ : Wke π (proj₂ (env-metric (botEnv T))) (proj₂ (env-metric (botEnv S))))
  --           → ValSteps S

  {- TODO
  wke-trans : {E E' E'' : List (Σ[ X ∈ Ty ] (List (ℕ × ℕ) → TermMetric X))}
                        → {π₁ : Wk Γ Γ'} → {π₂ : Wk Γ' Γ''} → {ϖ₁ : Wkn Γ E} → {ϖ : Wkn Γ' E'} → {ϖ₂ : Wkn Γ'' E''}
                        → (θ₁ : Wke π₁ ϖ₁ ϖ) (θ₂ : Wke π₂ ϖ ϖ₂)
                        → Wke (wk-trans π₁ π₂) ϖ₁ ϖ₂
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} wke-ε wke-ε = wke-ε
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-ccc π ϖ₃ ϖ' e θ₁) (wke-ccc π₃ ϖ₄ ϖ'' e₁ θ₂) = wke-ccc (wk-trans π π₃) ϖ₃ ϖ'' e (wke-trans θ₁ θ₂)
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-ccc π ϖ₃ ϖ' e θ₁) (wke-wc- π₃ ϖ₄ ϖ'' e₁ θ₂) = wke-wc- (wk-trans π π₃) ϖ₃ ϖ₂ e (wke-trans θ₁ θ₂)
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-wc- π ϖ₃ ϖ' e θ₁) wke-ε = wke-wc- (wk-trans π wk-ε) ϖ₃ wkn-nil e (wke-trans θ₁ wke-ε)
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-wc- π ϖ₃ ϖ' e θ₁) (wke-ccc π₃ ϖ₄ ϖ'' e₁ θ₂) = wke-wc- (wk-trans π (wk-cong π₃)) ϖ₃ (wkn-cong ϖ'') e (wke-trans θ₁ (wke-ccc π₃ ϖ₄ ϖ'' e₁ θ₂))
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-wc- π ϖ₃ ϖ' e θ₁) (wke-wc- π₃ ϖ₄ ϖ'' e₁ θ₂) = wke-wc- (wk-trans π (wk-wk π₃)) ϖ₃ ϖ₂ e (wke-trans θ₁ (wke-wc- π₃ ϖ₄ ϖ₂ e₁ θ₂))
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-wc- π ϖ₃ ϖ' e θ₁) (wke-ww- π₃ ϖ₄ ϖ'' θ₂) = wke-wc- (wk-trans π (wk-wk π₃)) ϖ₃ ϖ₂ e (wke-trans θ₁ (wke-ww- π₃ ϖ₄ ϖ₂ θ₂))
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-wc- π ϖ₃ ϖ' e θ₁) (wke-cww π₃ ϖ₄ ϖ'' θ₂) = wke-wc- (wk-trans π (wk-cong π₃)) ϖ₃ (wkn-cons ϖ'') e (wke-trans θ₁ (wke-cww π₃ ϖ₄ ϖ'' θ₂))
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-ww- π ϖ₃ ϖ' θ₁) wke-ε = wke-ww- (wk-trans π wk-ε) ϖ₃ wkn-nil (wke-trans θ₁ wke-ε)
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-ww- π ϖ₃ ϖ' θ₁) (wke-ccc π₃ ϖ₄ ϖ'' e θ₂) = wke-ww- (wk-trans π (wk-cong π₃)) ϖ₃ (wkn-cong ϖ'') (wke-trans θ₁ (wke-ccc π₃ ϖ₄ ϖ'' e θ₂))
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-ww- π ϖ₃ ϖ' θ₁) (wke-wc- π₃ ϖ₄ ϖ'' e θ₂) = wke-ww- (wk-trans π (wk-wk π₃)) ϖ₃ ϖ₂ (wke-trans θ₁ (wke-wc- π₃ ϖ₄ ϖ₂ e θ₂))
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-ww- π ϖ₃ ϖ' θ₁) (wke-ww- π₃ ϖ₄ ϖ'' θ₂) = wke-ww- (wk-trans π (wk-wk π₃)) ϖ₃ ϖ₂ (wke-trans θ₁ (wke-ww- π₃ ϖ₄ ϖ₂ θ₂))
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-ww- π ϖ₃ ϖ' θ₁) (wke-cww π₃ ϖ₄ ϖ'' θ₂) = wke-ww- (wk-trans π (wk-cong π₃)) ϖ₃ (wkn-cons ϖ'') (wke-trans θ₁ (wke-cww π₃ ϖ₄ ϖ'' θ₂))
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-cww π ϖ₃ ϖ' θ₁) (wke-ww- π₃ ϖ₄ ϖ'' θ₂) = wke-ww- (wk-trans π π₃) ϖ₃ ϖ₂ (wke-trans θ₁ θ₂)
  wke-trans {E = E} {E' = E'} {E'' = E''} {π₁ = π₁} {π₂ = π₂} {ϖ₁ = ϖ₁} {ϖ = ϖ} {ϖ₂ = ϖ₂} (wke-cww π ϖ₃ ϖ' θ₁) (wke-cww π₃ ϖ₄ ϖ'' θ₂) = wke-cww (wk-trans π π₃) ϖ₃ ϖ'' (wke-trans θ₁ θ₂)
  -}


  val-eval-rec : (M : Γ' ⊢ᵛ X) → (γ : Env Γ) → (π : Wk Γ Γ') → ValSteps {T◾ = X} (∘ ((⇡ (wk-val π M) ⊲ γ ∷ □) {↥ = 🗆}))

  val-eval-rec {X = `V} (var {A = .`V} i) γ π = steps (_ →ᵛ⟨ ∘var-c ⟩．) (∙ v̲a̲r̲ (wk-mem π i) ⊲ γ ■) refl wk-id refl (λ csn →  ≤ᴹ-incr-cong (s≤s (z≤n {n = 1})) (≤ᴹ-refl {nm = (proj₁ (lookup-mono-metric (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) csn)})) wke-id --(λ csn → ≤ᴹ-incr-cong (s≤s (z≤n {n = 1})) (≤ᴹ-refl {nm = (lookup-metric (wk-mem π i) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn)})) wke-id

  val-eval-rec {X = `Unit} (var {A = .`Unit} i) γ π with lookup (wk-mem π i) γ
  ... | steps i>>T found-unit i≡T π₁ w≡γ T≤ᴹS _ = steps (_ →ᵛ⟨ ∘var i>>T π₁ ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id refl (λ csn → ≤ᴹ-trans (T≤ᴹS csn) (≤ᴹ-incr-cong (z≤n {n = 2}) (≤ᴹ-refl {nm = (proj₁ (lookup-mono-metric (wk-mem π i) (proj₁ (env-mono-metric γ)) (proj₂ (env-mono-metric γ))) csn) }))) wke-id --(λ csn → ≤ᴹ-trans (T≤ᴹS csn) (≤ᴹ-incr-cong (z≤n {n = 2}) (≤ᴹ-refl {nm = (lookup-metric (wk-mem π i) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn)}))) wke-id

  val-eval-rec {X = X `× X₁} (var {A = .(X `× X₁)} i) γ π with lookup (wk-mem π i) γ
  ... | steps i>>T (found-pair {LHS = LHS} {RHS = RHS} {γ = γ₁}) i≡T π₁ w≡γ T≤ᴹS θ =

            -- let
            --   a1 = λ csn → v̲a̲l̲-wke-lemma LHS (proj₁ (env-metric γ)) (proj₁ (env-metric γ₁)) π₁ (proj₂ (env-metric γ)) (proj₂ (env-metric γ₁)) θ csn
            --   a2 = λ csn → v̲a̲l̲-wke-lemma RHS (proj₁ (env-metric γ)) (proj₁ (env-metric γ₁)) π₁ (proj₂ (env-metric γ)) (proj₂ (env-metric γ₁)) θ csn
            --   T≤ᴹS' csn  = subst (λ x → m-× 1 x (v̲a̲l̲-metric RHS (proj₁ (env-metric γ₁)) (proj₂ (env-metric γ₁)) csn) ≤ᴹ lookup-metric (wk-mem π i) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn) (a1 csn) (T≤ᴹS csn)
            --   T≤ᴹS'' csn = subst (λ x → m-× 1 (v̲a̲l̲-metric (wk-v̲a̲l̲ π₁ LHS) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn) x ≤ᴹ lookup-metric (wk-mem π i) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn) (a2 csn) (T≤ᴹS' csn)
            -- in

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

            {!!}

            {!!}

            -- (λ csn → ≤ᴹ-trans (T≤ᴹS'' csn) (≤ᴹ-incr-cong (z≤n {n = 2}) (≤ᴹ-refl {nm = (lookup-metric (wk-mem π i) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn)})))

            -- wke-id

  val-eval-rec {X = X `⇒ X₁} (var {A = .(X `⇒ X₁)} i) γ π with lookup (wk-mem π i) γ

  ... | steps i>>T (found-lam {W = W} {γ = γ₁}) i≡T π₁ w≡γ T≤ᴹS θ =

            -- let
            --   a1 = λ csn → wke-comp-count-lemma h W (proj₁ (env-metric γ)) (proj₁ (env-metric γ₁)) (wk-cong π₁) (wkn-cons (proj₂ (env-metric γ))) (wkn-cons (proj₂ (env-metric γ₁))) (wke-cww π₁ (proj₂ (env-metric γ)) (proj₂ (env-metric γ₁)) θ) csn
            --   a2 = λ csn → comp-wke-lemma W (proj₁ (env-metric γ)) (proj₁ (env-metric γ₁)) (wk-cong π₁) (wkn-cons (proj₂ (env-metric γ))) (wkn-cons (proj₂ (env-metric γ₁))) (wke-cww π₁ (proj₂ (env-metric γ)) (proj₂ (env-metric γ₁)) θ) csn
            --   T≤ᴹS'  csn = subst (λ x → m-⇒ 1 x (comp-metric W (proj₁ (env-metric γ₁)) (wkn-cons (proj₂ (env-metric γ₁))) csn) ≤ᴹ lookup-metric (wk-mem π i) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn) (a1 csn) (T≤ᴹS csn)
            --   T≤ᴹS'' csn = subst (λ x → m-⇒ 1 (count-in-comp h (wk-comp (wk-cong π₁) W) (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) csn) x ≤ᴹ lookup-metric (wk-mem π i) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn) (a2 csn) (T≤ᴹS' csn)
            -- in

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

            {!!}

            {!!}

            -- (λ csn → ≤ᴹ-trans (T≤ᴹS'' csn) (≤ᴹ-incr-cong (z≤n {n = 2}) (≤ᴹ-refl {nm = (lookup-metric (wk-mem π i) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn)})))

            -- wke-id

  val-eval-rec (lam W) γ π = steps (∘ ⇡ (wk-val π (lam W)) ⊲ γ ∷ □ →ᵛ⟨ ∘lam ⟩．) (∙ l̲a̲m̲ (wk-comp (wk-cong π) W) ⊲ γ ■) refl wk-id refl {!!} {!!} --(λ csn → ≤ᴹ-incr-cong (z≤n {n = 1}) (≤ᴹ-refl {nm = m-⇒ 1 (count-in-comp h (wk-comp (wk-cong π) W) (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) csn) (comp-metric (wk-comp (wk-cong π) W) (proj₁ (env-metric γ)) (wkn-cons (proj₂ (env-metric γ))) csn)})) wke-id

  val-eval-rec unit γ π = steps (_ →ᵛ⟨ ∘unit ⟩．) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id refl {!!} {!!} --(λ csn → ≤ᴹ-incr-cong (z≤n {n = 1}) (≤ᴹ-refl {nm = m-Unit 1})) wke-id

  val-eval-rec (pair {A = X} {B = Y} LHS RHS) γ π with val-eval-rec {X = X} LHS γ π
  ... | steps {T = ∙ (⭭_ {X = X} LT ⊲ γ₁ ∷ □) {↥ = 🗆}} L>T ∙LT L≡T πᴸ wk≡ᴸ T≤ᴹS θ with  val-eval-rec {X = Y} RHS γ₁ (wk-trans πᴸ π)
  ...      | steps {T = ∙ (⭭_ {X = Y} RT ⊲ γ₂ ∷ □) {↥ = 🗆}} R>T ∙RT R≡T πᴿ wk≡ᴿ T≤ᴹS' θ' rewrite sym (wk-val-trans RHS πᴸ π) =
            -- let
            --   a1     csn = v̲a̲l̲-wke-lemma LT (proj₁ (env-metric γ₂)) (proj₁ (env-metric γ₁)) πᴿ (proj₂ (env-metric γ₂)) (proj₂ (env-metric γ₁)) θ' csn
            --   a2     csn = sym (val-wke-lemma (wk-val π RHS) (proj₁ (env-metric γ₁)) (proj₁ (env-metric γ)) πᴸ (proj₂ (env-metric γ₁)) (proj₂ (env-metric γ)) θ csn)
            --   T≤ᴹS₁  csn = subst (λ x → x ≤ᴹ val-metric (wk-val π LHS) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn) (a1 csn) (T≤ᴹS csn)
            --   T≤ᴹS'₁ csn = subst (λ x → (v̲a̲l̲-metric RT (proj₁ (env-metric γ₂)) (proj₂ (env-metric γ₂)) csn) ≤ᴹ x) (a2 csn) (T≤ᴹS' csn)
            -- in

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

              {!!} --(λ csn → ≤-× (s≤s (z≤n {n = 1})) (T≤ᴹS₁ csn) (T≤ᴹS'₁ csn))

              {!!} --(wke-trans θ' θ)

  val-eval-rec (pm {A = A} {B = B} M N) γ π with val-eval-rec M γ π
  ... | steps {S = S} M>T ∙ pa̲i̲r̲ LHS RHS ⊲ γ₁ ■ M≡T π₁ wk≡₁ T≤ᴹS θ with val-eval-rec N (_﹐_ (_﹐_ γ₁ LHS) (wk-v̲a̲l̲ (wk-wk wk-id) RHS)) ((wk-cong (wk-cong (wk-trans π₁ π)))) | (wk-val-trans N (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π)))
  ...    | steps {T = T} N>T ∙T N≡T π₂ wk≡₂ T≤ᴹS' θ' | eq with N>T
  ...      | N>T' rewrite sym eq =

        -- let
        --   L≤ᴹl csn = LHS≤ᴹlhs (T≤ᴹS csn)
        --   R≤ᴹr csn = RHS≤ᴹrhs (T≤ᴹS csn)
        --   r≡      : (csn : List (ℕ × ℕ)) →
        --               v̲a̲l̲-metric                       RHS                                                                         (proj₁ (env-metric γ₁))           (proj₂ (env-metric γ₁)) csn
        --             ≡ v̲a̲l̲-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-metric LHS (proj₁ (env-metric γ₁)) (proj₂ (env-metric γ₁))) ∷ proj₁ (env-metric γ₁)) (wkn-cong (proj₂ (env-metric γ₁))) csn
        --   r≡  csn = v̲a̲l̲-wke-lemma RHS ((A , v̲a̲l̲-metric LHS (proj₁ (env-metric γ₁)) (proj₂ (env-metric γ₁))) ∷ proj₁ (env-metric γ₁)) ((proj₁ (env-metric γ₁))) (wk-wk wk-id) (wkn-cong (proj₂ (env-metric γ₁))) (proj₂ (env-metric γ₁)) (wke-wc- wk-id (proj₂ (env-metric γ₁)) (proj₂ (env-metric γ₁)) (v̲a̲l̲-metric LHS (proj₁ (env-metric γ₁)) (proj₂ (env-metric γ₁))) wke-id) csn
        --   R≤ᴹr' csn  = subst (λ x → x ≤ᴹ rhs (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn)) (r≡ csn) (R≤ᴹr csn)
        --   ϖ₁ = (wkn-cong {e = v̲a̲l̲-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-metric LHS (proj₁ (env-metric γ₁)) (proj₂ (env-metric γ₁))) ∷ proj₁ (env-metric γ₁)) (wkn-cong (proj₂ (env-metric γ₁)))} (wkn-cong {e = v̲a̲l̲-metric LHS (proj₁ (env-metric γ₁)) (proj₂ (env-metric γ₁))} (proj₂ (env-metric γ))))
        --   ϖ₂ = wkn-cong {e = λ c → rhs (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) c)} (wkn-cong {e = λ c → lhs (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) c)} (proj₂ (env-metric γ)) )
        --   ϕ : Wkx wk-id ϖ₁ ϖ₂
        --   ϕ = wkx-cong {π = wk-id } R≤ᴹr' (wkx-cong {π = wk-id} L≤ᴹl (wkx-bc (wke-id {π = wk-id})))
        --   a1 csn = val-wkx-lemma
        --                    (wk-val (wk-cong (wk-cong π)) N)
        --                    ((B , v̲a̲l̲-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-metric LHS (proj₁ (env-metric γ₁)) (proj₂ (env-metric γ₁))) ∷ proj₁ (env-metric γ₁)) (wkn-cong (proj₂ (env-metric γ₁)))) ∷ (A , v̲a̲l̲-metric LHS (proj₁ (env-metric γ₁)) (proj₂ (env-metric γ₁))) ∷ env-metric γ .proj₁)
        --                    ((B , (λ c → rhs (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) c))) ∷ (A , (λ c → lhs (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) c))) ∷ env-metric γ .proj₁)
        --                    wk-id ϖ₁ ϖ₂ ϕ csn
        --   a2 csn = val-wke-lemma
        --                    (wk-val (wk-cong (wk-cong π)) N)
        --                    ((B , v̲a̲l̲-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-metric LHS (proj₁ (env-metric γ₁)) (proj₂ (env-metric γ₁))) ∷ proj₁ (env-metric γ₁)) (wkn-cong (proj₂ (env-metric γ₁)))) ∷ (A , v̲a̲l̲-metric LHS (proj₁ (env-metric γ₁)) (proj₂ (env-metric γ₁))) ∷ env-metric γ₁ .proj₁)
        --                    ((B , v̲a̲l̲-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-metric LHS (proj₁ (env-metric γ₁)) (proj₂ (env-metric γ₁))) ∷ proj₁ (env-metric γ₁)) (wkn-cong (proj₂ (env-metric γ₁)))) ∷ (A , v̲a̲l̲-metric LHS (proj₁ (env-metric γ₁)) (proj₂ (env-metric γ₁))) ∷ env-metric γ .proj₁)
        --                    (wk-cong (wk-cong π₁)) (wkn-cong (wkn-cong (proj₂ (env-metric γ₁)))) ((wkn-cong (wkn-cong (proj₂ (env-metric γ))))) (wke-ccc (wk-cong π₁) (wkn-cong (proj₂ (env-metric γ₁))) (wkn-cong (proj₂ (env-metric γ))) (v̲a̲l̲-metric (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ((A , v̲a̲l̲-metric LHS (proj₁ (env-metric γ₁)) (proj₂ (env-metric γ₁))) ∷ proj₁ (env-metric γ₁)) (wkn-cong (proj₂ (env-metric γ₁)))) (wke-ccc π₁ (proj₂ (env-metric γ₁)) (proj₂ (env-metric γ)) (v̲a̲l̲-metric LHS (proj₁ (env-metric γ₁)) (proj₂ (env-metric γ₁))) θ)) csn
        --   a3 csn = subst (λ x → x ≤ᴹ val-metric (wk-val (wk-cong (wk-cong π)) N) ((B , (λ c → rhs (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) c))) ∷ (A , (λ c → lhs (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) c))) ∷ env-metric γ .proj₁) ϖ₂ csn)
        --                   (a2 csn) (a1 csn)
        --   T≤ᴹS'' csn = ≤ᴹ-trans (T≤ᴹS' csn) (a3 csn)
        -- in

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

          {!!} --(λ csn → ≤ᴹ-incr-cong (z≤n {n = (suc (vx (val-metric (wk-val π M) (proj₁ (env-metric γ)) (proj₂ (env-metric γ)) csn) + ⟪ val-metric (wk-val (wk-cong (wk-cong π)) N) (proj₁ (env-metric γ)) (wkn-cons (wkn-cons (proj₂ (env-metric γ)))) csn ⟫))}) (T≤ᴹS'' csn))

          {!!} --(wke-trans θ' (wke-wc- (wk-wk π₁) (wkn-cong (proj₂ (env-metric γ₁))) (proj₂ (env-metric γ)) _ (wke-wc- π₁ (proj₂ (env-metric γ₁)) (proj₂ (env-metric γ)) (v̲a̲l̲-metric LHS (proj₁ (env-metric γ₁)) (proj₂ (env-metric γ₁))) θ)))

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

