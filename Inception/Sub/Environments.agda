{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Environments (R : Set) where

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

open import Inception.Sub.Equality

open import Relation.Binary.HeterogeneousEquality as H using (_≅_)

open import Relation.Binary.HeterogeneousEquality.Core using (≡-to-≅)

variable
  X X' Y Y' Z Z' T◾ T◾' : Ty
  Γ' Γ'' Γ''' Δ' : Ctx

module EnvMain {R₀ : Ty} (k₀ : ⟦ R₀ ⟧ → R) where

  infixl 27 _﹐_
  infixl 27 _﹐﹝_╎_﹞

  data V̲a̲l̲ : Ctx → Ty → Set where

      l̲a̲m̲ : (Γ ∙ X) ⊢ᶜ Y → V̲a̲l̲ Γ (X `⇒ Y)

      pa̲i̲r̲ : V̲a̲l̲ Γ X → V̲a̲l̲ Γ Y → V̲a̲l̲ Γ (X `× Y)

      u̲n̲i̲t̲ : V̲a̲l̲ Γ `Unit

      v̲a̲r̲  : (i : Γ ∋ `V) → V̲a̲l̲ Γ `V

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

  data Env where

      ∗       :  Env ε

      _﹐_     :  Env Γ → (M : V̲a̲l̲ Γ X) → Env (Γ ∙ X)

      _﹐﹝_╎_﹞ :  (γ : Env Γ) → (W : Γ ⊢ᶜ X) → (cs : CompStack Δ X) → {π : Wk Γ Δ} → .{wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → Env (Γ ∙ `V)

  topCsEnv ◻ = ∗
  topCsEnv (W ⊲ γ ⦂⦂ cs) = γ

  toVal : V̲a̲l̲ Γ X → Γ ⊢ᵛ X
  toVal (l̲a̲m̲ W) = lam W
  toVal (pa̲i̲r̲ LHS RHS) = pair (toVal LHS) (toVal RHS)
  toVal (u̲n̲i̲t̲) = unit
  toVal (v̲a̲r̲ i) = var i

  toComp :  C̲o̲m̲p Γ X → Γ ⊢ᶜ X
  toComp (r̲e̲t̲u̲r̲n̲ M) = return (toVal M)
  toComp (a̲pp M N) = app M (toVal N)

  ⟦_⟧ᴷ : (cs : CompStack Δ Y) → ⟦ Y ⟧ → R
  ⟦_⟧ᴷ cs y = ⟦ cs ⟧ᶜˢ (η y) k₀

  ⟦ ∗ ⟧ᴱ = tt
  ⟦ E ﹐ M ⟧ᴱ = ⟦ E ⟧ᴱ , ⟦ toVal M ⟧ᵛ ⟦ E ⟧ᴱ
  ⟦ E ﹐﹝ W ╎ cs ﹞ ⟧ᴱ = ⟦ E ⟧ᴱ , ⟦ W ⟧ᶜ ⟦ E ⟧ᴱ ⟦ cs ⟧ᴷ

  ⟦ ◻ ⟧ᶜˢ = idf
  ⟦ W₁ ⊲ γ₁ ⦂⦂ tail ⟧ᶜˢ = < const ⟦ γ₁ ⟧ᴱ , idf > ； τ ； (⟦ W₁ ⟧ᶜ ♯) ； ⟦ tail ⟧ᶜˢ

  -----------------------------------------------------------------------------
  -- WEAKENINGS
  -----------------------------------------------------------------------------

  infix  26 ⭭_
  infix  26 ⇡_

  data PartialTerm : (Γ : Ctx) → (X : Ty) → Set where

      ⭭_ : V̲a̲l̲ Γ X → PartialTerm Γ X

      ⇡_ : (M : Γ ⊢ᵛ X) → PartialTerm Γ X

      ⇡ᴹ : (M : Γ ⊢ᵛ X `× Y) → (N : (Γ ∙ X ∙ Y) ⊢ᵛ Z) → PartialTerm Γ Z

      ⇡ᴸ : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → PartialTerm Γ (X `× Y)

      ⇡ᴿ  : (LHS : V̲a̲l̲ Γ X) → (RHS : Γ ⊢ᵛ Y) → PartialTerm Γ (X `× Y)

  wk-v̲a̲l̲ : Wk Γ Δ → V̲a̲l̲ Δ X → V̲a̲l̲ Γ X
  wk-v̲a̲l̲ π (l̲a̲m̲ W) = l̲a̲m̲ ((wk-comp (wk-cong π) W))
  wk-v̲a̲l̲ π (pa̲i̲r̲ LHS RHS) = pa̲i̲r̲ (wk-v̲a̲l̲ π LHS) (wk-v̲a̲l̲ π RHS)
  wk-v̲a̲l̲ π u̲n̲i̲t̲ = u̲n̲i̲t̲
  wk-v̲a̲l̲ π (v̲a̲r̲ i) = v̲a̲r̲ (wk-mem π i)

  wk-c̲o̲m̲p : Wk Γ Δ → C̲o̲m̲p Δ X → C̲o̲m̲p Γ X
  wk-c̲o̲m̲p π (r̲e̲t̲u̲r̲n̲ M) = r̲e̲t̲u̲r̲n̲ (wk-v̲a̲l̲ π M)
  wk-c̲o̲m̲p π (a̲pp M N) = a̲pp (wk-val π M) (wk-v̲a̲l̲ π N)

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

  wk-assoc : {π₁ : Wk Γ Γ'} {π₂ : Wk Γ' Γ''} {π₃ : Wk Γ'' Γ'''} → wk-trans π₁ (wk-trans π₂ π₃) ≡ wk-trans (wk-trans π₁ π₂) π₃
  wk-assoc {π₁ = wk-ε} {π₂ = π₂} {π₃ = π₃} = refl
  wk-assoc {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {π₃ = wk-cong π₃} = cong wk-cong (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
  wk-assoc {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {π₃ = wk-wk π₃} = cong wk-wk (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
  wk-assoc {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {π₃ = π₃} = cong wk-wk (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
  wk-assoc {π₁ = wk-wk π₁} {π₂ = π₂} {π₃ = π₃} = cong wk-wk (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})

  wk-comm-explicit : (M : V̲a̲l̲ Γ X) → (π : Wk Δ Γ) → toVal (wk-v̲a̲l̲ π M) ≡ wk-val π (toVal M)
  wk-comm-explicit M π = sym wk-comm

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

  wk-join : Wk Γ Δ → Wk Γ Δ' → Σ[ Γ' ∈ Ctx ] (Wk Γ Γ' × Wk Γ' Δ × Wk Γ' Δ')
  wk-join {Γ = Γ} {Δ = Δ} {Δ' = Δ'} wk-ε wk-ε = ε , wk-ε , wk-ε , wk-ε
  wk-join {Γ = Γ ∙ X} {Δ = Δ ∙ X} {Δ' = Δ' ∙ X} (wk-cong π₁) (wk-cong π₂) =
          let
            w = wk-join π₁ π₂
            Γ₀ = proj₁ w
            π₀ = proj₁ (proj₂ w)
          in
          Γ₀ ∙ X , wk-cong π₀ , wk-cong (proj₁ (proj₂ (proj₂ w))) , wk-cong (proj₂ (proj₂ (proj₂ w)))
  wk-join {Γ = Γ ∙ X} {Δ = Δ ∙ X} {Δ' = ε} (wk-cong π₁) (wk-wk π₂) =
          let
            w = wk-join π₁ π₂
            Γ₀ = proj₁ w
            π₀ = proj₁ (proj₂ w)
          in
          Γ₀ ∙ X , wk-cong π₀ , wk-cong (proj₁ (proj₂ (proj₂ w))) , wk-wk (proj₂ (proj₂ (proj₂ w)))
  wk-join {Γ = Γ ∙ X} {Δ = Δ ∙ X} {Δ' = Δ' ∙ x} (wk-cong π₁) (wk-wk π₂) =
          let
            w = wk-join π₁ π₂
            Γ₀ = proj₁ w
            π₀ = proj₁ (proj₂ w)
          in
          Γ₀ ∙ X , wk-cong π₀ , wk-cong (proj₁ (proj₂ (proj₂ w))) , wk-wk (proj₂ (proj₂ (proj₂ w)))
  wk-join {Γ = Γ ∙ X} {Δ = Δ} {Δ' = Δ' ∙ X} (wk-wk π₁) (wk-cong π₂) =
          let
            w = wk-join π₁ π₂
            Γ₀ = proj₁ w
            π₀ = proj₁ (proj₂ w)
          in
          Γ₀ ∙ X , wk-cong π₀ , wk-wk (proj₁ (proj₂ (proj₂ w))) , wk-cong (proj₂ (proj₂ (proj₂ w)))
  wk-join {Γ = Γ Cx.∙ X} {Δ = Cx.ε} {Δ' = Cx.ε} (wk-wk π₁) (wk-wk π₂) =
          let
            w = wk-join π₁ π₂
            Γ₀ = proj₁ w
            π₀ = proj₁ (proj₂ w)
          in
          Γ₀ , wk-wk π₀ , proj₁ (proj₂ (proj₂ w)) , proj₁ (proj₂ (proj₂ w))
  wk-join {Γ = Γ Cx.∙ X} {Δ = Cx.ε} {Δ' = Δ' Cx.∙ x} (wk-wk π₁) (wk-wk π₂) =
          let
            w = wk-join π₁ π₂
            Γ₀ = proj₁ w
            π₀ = proj₁ (proj₂ w)
          in
          Γ₀ , wk-wk π₀ , proj₁ (proj₂ (proj₂ w)) , proj₂ (proj₂ (proj₂ w))
  wk-join {Γ = Γ Cx.∙ X} {Δ = Δ Cx.∙ x} {Δ' = Cx.ε} (wk-wk π₁) (wk-wk π₂) =
          let
            w = wk-join π₁ π₂
            Γ₀ = proj₁ w
            π₀ = proj₁ (proj₂ w)
          in
          Γ₀ , wk-wk π₀ , proj₁ (proj₂ (proj₂ w)) , proj₂ (proj₂ (proj₂ w))
  wk-join {Γ = Γ Cx.∙ X} {Δ = Δ Cx.∙ x} {Δ' = Δ' Cx.∙ x₁} (wk-wk π₁) (wk-wk π₂) =
          let
            w = wk-join π₁ π₂
            Γ₀ = proj₁ w
            π₀ = proj₁ (proj₂ w)
          in
          Γ₀ , wk-wk π₀ , proj₁ (proj₂ (proj₂ w)) , proj₂ (proj₂ (proj₂ w))

  -----------------------------------------------------------------------------
  -- PROPERTIES OF ENVIRONMENTS
  -----------------------------------------------------------------------------

  variable
      γ  : Env Γ
      γ' : Env Γ'
      γ'' : Env Γ''

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

               goal : ⟦ wk-cong π₁ ⟧ʷ (⟦ γ'' ⟧ᴱ , ⟦ toVal (wk-v̲a̲l̲ π₁ M) ⟧ᵛ ⟦ γ'' ⟧ᴱ) ≡ (⟦ γ₁ ⟧ᴱ , ⟦ toVal M ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
               goal =   ⟦ π₁ ⟧ʷ ⟦ γ'' ⟧ᴱ , ⟦ toVal (wk-v̲a̲l̲ π₁ M) ⟧ᵛ ⟦ γ'' ⟧ᴱ
                      ≡⟨ cong (λ x → ⟦ π₁ ⟧ʷ ⟦ γ'' ⟧ᴱ , ⟦ x ⟧ᵛ ⟦ γ'' ⟧ᴱ) (wk-comm-explicit M π₁) ⟩
                        ⟦ π₁ ⟧ʷ ⟦ γ'' ⟧ᴱ , ⟦ toVal M ⟧ᵛ (⟦ π₁ ⟧ʷ ⟦ γ'' ⟧ᴱ)
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
                  ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal M₁ ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)
                ≡⟨ cong (λ x → ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ) (sym (wk-comm-explicit M₁ π)) ⟩
                ⟦ wk-cong π ⟧ʷ (⟦ γ ⟧ᴱ , ⟦ toVal (wk-v̲a̲l̲ π M₁) ⟧ᵛ ⟦ γ ⟧ᴱ) ∎
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

  ----------------------------------------------------------
  -- NORMALISE TERMS
  ----------------------------------------------------------

  pred-ctx-eq : Γ ∙ X ≡ Δ ∙ X → Γ ≡ Δ
  pred-ctx-eq refl = refl

  ctx-absurd : ε ≡ Γ ∙ X → ⊥
  ctx-absurd ()

  -- data MemGC : (Γ : Ctx) → (Γ' : Ctx) → (π : Wk Γ Γ') → (i : Γ' ∋ X) → Set where
  --   z : MemGC (Γ ∙ X) (ε ∙ X) (wk-cong wk-wk-ε) h
  --   s : {Δ : Ctx} {Y : Ty} {π : Wk Δ (ε ∙ X)} → MemGC Δ (ε ∙ X) π h → MemGC (Δ ∙ Y) (ε ∙ X) (wk-wk {A = Y} π) h

  data MemGC : (Γ : Ctx) → (Γ' : Ctx) → (π : Wk Γ Γ') → (i : Γ ∋ X) → (i' : Γ' ∋ X) → Set where
    h : MemGC (Γ ∙ X) (ε ∙ X) (wk-cong wk-wk-ε) h h
    t : {Δ : Ctx} {Y : Ty} {π : Wk Δ (ε ∙ X)} {i : Δ ∋ X} → MemGC Δ (ε ∙ X) π i h → MemGC (Δ ∙ Y) (ε ∙ X) (wk-wk {A = Y} π) (t i) h

  data CompGC : (Γ : Ctx) → (Γ' : Ctx) → (π : Wk Γ Γ') → (W : Comp Γ X) → (W' : Comp Γ' X) → Set

  data ValGC : (Γ : Ctx) → (Γ' : Ctx) → (π : Wk Γ Γ') → (M : Val Γ X) → (M' : Val Γ' X) → Set where
    var  : {π : Wk Γ Γ'} {i : Γ ∋ X} {i' : Γ' ∋ X} → MemGC Γ Γ' π i i' → ValGC Γ Γ' π (var i) (var i')
    lam  : {π : Wk Γ Γ'} {W : Comp (Γ ∙ X) Y} {W' : Comp (Γ' ∙ X) Y}
           → (WG : CompGC (Γ ∙ X) (Γ' ∙ X) (wk-cong π) W W')
           → ValGC Γ Γ' π (lam W) (lam W')
    pair : {π : Wk Γ Γ'} {M₁ : Val Γ X} {M₂ : Val Γ Y} {M₁' : Val Γ' X} {M₂' : Val Γ' Y}
           → (MG₁ : ValGC Γ Γ' π M₁ M₁') → (MG₂ : ValGC Γ Γ' π M₂ M₂')
           → ValGC Γ Γ' π (pair M₁ M₂) (pair M₁' M₂')
    pm   : {π : Wk Γ Γ'} {M : Val Γ (X `× Y)} {N : Val (Γ ∙ X ∙ Y) Z} {M' : Val Γ' (X `× Y)} {N' : Val (Γ' ∙ X ∙ Y) Z}
           → (MG : ValGC Γ Γ' π M M') → (NG : ValGC (Γ ∙ X ∙ Y) (Γ' ∙ X ∙ Y) (wk-cong (wk-cong π)) N N')
           → ValGC Γ Γ' π (pm M N) (pm M' N')
    unit : {π : Wk Γ ε} → ValGC Γ ε π unit unit

  data CompGC where
    return  : {π : Wk Γ Γ'} {M : Val Γ X} {M' : Val Γ' X} → ValGC Γ Γ' π M M' → CompGC Γ Γ' π (return M) (return M')
    pm      : {π : Wk Γ Γ'} {M : Val Γ (X `× Y)} {W : Comp (Γ ∙ X ∙ Y) Z} {M' : Val Γ' (X `× Y)} {W' : Comp (Γ' ∙ X ∙ Y) Z}
           → (MG : ValGC Γ Γ' π M M') → (WG : CompGC (Γ ∙ X ∙ Y) (Γ' ∙ X ∙ Y) (wk-cong (wk-cong π)) W W')
           → CompGC Γ Γ' π (pm M W) (pm M' W')
    push    : {π : Wk Γ Γ'} {W₁ : Comp Γ X} {W₂ : Comp (Γ ∙ X) Y} {W₁' : Comp Γ' X} {W₂' : Comp (Γ' ∙ X) Y}
           → (WG₁ : CompGC Γ Γ' π W₁ W₁') → (WG₂ : CompGC (Γ ∙ X) (Γ' ∙ X) (wk-cong π) W₂ W₂')
           → CompGC Γ Γ' π (push W₁ W₂) (push W₁' W₂')
    app     : {π : Wk Γ Γ'} {M : Val Γ (X `⇒ Y)} {N : Val Γ X} {M' : Val Γ' (X `⇒ Y)} {N' : Val Γ' X}
           → (MG : ValGC Γ Γ' π M M') → (NG : ValGC Γ Γ' π N N')
           → CompGC Γ Γ' π (app M N) (app M' N')
    var     : {π : Wk Γ Γ'} {M : Val Γ `V} {M' : Val Γ' `V} → ValGC Γ Γ' π M M' → CompGC {X = X} Γ Γ' π (var M) (var M')
    sub     : {π : Wk Γ Γ'} {W₁ : Comp (Γ ∙ `V) X} {W₂ : Comp Γ X} {W₁' : Comp (Γ' ∙ `V) X} {W₂' : Comp Γ' X}
           → (WG₁ : CompGC (Γ ∙ `V) (Γ' ∙ `V) (wk-cong π) W₁ W₁') → (WG₂ : CompGC Γ Γ' π W₂ W₂')
           → CompGC Γ Γ' π (sub W₁ W₂) (sub W₁' W₂')

  record GCMem (i : Γ ∋ X) : Set where
    field
      gmwk   : Wk Γ (ε ∙ X)
      gmgc   : MemGC Γ (ε ∙ X) gmwk i h

  record GCVal (M : Val Γ X) : Set where
    field
      gvcx   : Ctx
      gvwk   : Wk Γ gvcx
      gvtm   : Val gvcx X
      gvgc   : ValGC Γ gvcx gvwk M gvtm

  record GCComp (W : Comp Γ X) : Set where
    field
      gccx   : Ctx
      gcwk   : Wk Γ gccx
      gctm   : Comp gccx X
      gcgc   : CompGC Γ gccx gcwk W gctm

  open GCMem
  open Cx using (h ; t)

  memgc-uniq₀ : {Γ : Ctx} {Γ' Γ'' : Ctx} {π : Wk Γ Γ'} {π' : Wk Γ Γ''} {i : Γ ∋ X} {i' : Γ' ∋ X} {i'' : Γ'' ∋ X}
               → (MG₁ : MemGC Γ Γ' π i i') → (MG₂ : MemGC Γ Γ'' π' i i'')
               → Γ' ≡ Γ''
  memgc-uniq₀ {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π = π} {π'} {i = i} {i' = i'} {i'' = i''} h h = refl
  memgc-uniq₀ {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π = π} {π'} {i = i} {i' = i'} {i'' = i''} (t MG₁) (t MG₂) = refl

  memgc-uniq₁ : {Γ : Ctx} {Γ' : Ctx} {π π' : Wk Γ Γ'} {i : Γ ∋ X} {i' i'' : Γ' ∋ X}
               → (MG₁ : MemGC Γ Γ' π i i') → (MG₂ : MemGC Γ Γ' π' i i'')
               → (π ≡ π') × (i' ≡ i'')
  memgc-uniq₁ {Γ = Γ} {Γ' = Γ'} {π = π} {π'} {i = i} {i' = i'} {i'' = i''} h h = refl , refl
  memgc-uniq₁ {Γ = Γ} {Γ' = Γ'} {π = π} {π'} {i = i} {i' = i'} {i'' = i''} (t MG₁) (t MG₂) = cong wk-wk (proj₁ (memgc-uniq₁ MG₁ MG₂)) , refl


  memgc-wk-eq : {Δ Γ Γ' Γ'' : Ctx} {π₀ : Wk Δ Γ} {π : Wk Γ Γ'} {π' : Wk Δ Γ''} {i : Γ ∋ X} {i' : Γ' ∋ X} {i'' : Γ'' ∋ X}
               → (MG₁ : MemGC Γ Γ' π i i') → (MG₂ : MemGC Δ Γ'' π' (wk-mem π₀ i) i'')
               → Γ' ≡ Γ''
  memgc-wk-eq {Δ = ε ∙ X} {Γ = ε ∙ X} {Γ' = ε ∙ Y} {Γ'' = ε ∙ Z} {π₀ = wk-cong π₀} {π = π} {π' = π'} {i = h} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = Δ ∙ x ∙ X} {Γ = ε ∙ X} {Γ' = ε ∙ x₁} {Γ'' = ε ∙ x₂} {π₀ = wk-cong π₀} {π = π} {π' = π'} {i = h} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = ε ∙ x ∙ X} {Γ = ε ∙ x₁ ∙ X} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-cong π₀} {π = π} {π' = π'} {i = h} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = ε ∙ x ∙ X} {Γ = ε ∙ x₁ ∙ X} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-cong π₀} {π = π} {π' = π'} {i = t i} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = ε ∙ x ∙ X} {Γ = Γ ∙ x₄ ∙ x₁ ∙ X} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-cong π₀} {π = π} {π' = π'} {i = h} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = ε ∙ x ∙ X} {Γ = Γ ∙ x₄ ∙ x₁ ∙ X} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-cong π₀} {π = π} {π' = π'} {i = t i} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = Δ ∙ x₄ ∙ x ∙ X} {Γ = ε ∙ x₁ ∙ X} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-cong π₀} {π = π} {π' = π'} {i = h} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = Δ ∙ x₄ ∙ x ∙ X} {Γ = ε ∙ x₁ ∙ X} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-cong π₀} {π = π} {π' = π'} {i = t i} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = Δ ∙ x₄ ∙ x ∙ X} {Γ = Γ ∙ x₅ ∙ x₁ ∙ X} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-cong π₀} {π = π} {π' = π'} {i = h} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = Δ ∙ x₄ ∙ x ∙ X} {Γ = Γ ∙ x₅ ∙ x₁ ∙ X} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-cong π₀} {π = π} {π' = π'} {i = t i} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = ε ∙ x ∙ X} {Γ = ε ∙ x₁} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-wk π₀} {π = wk-cong π} {π' = wk-wk π'} {i = h} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = ε ∙ x ∙ X} {Γ = ε ∙ x₄ ∙ x₁} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-wk π₀} {π = wk-cong π} {π' = wk-wk π'} {i = h} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = ε ∙ x ∙ X} {Γ = Γ ∙ x₅ ∙ x₄ ∙ x₁} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-wk π₀} {π = wk-cong π} {π' = wk-wk π'} {i = h} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = Δ ∙ x₄ ∙ x ∙ X} {Γ = ε ∙ x₁} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-wk π₀} {π = wk-cong π} {π' = wk-wk π'} {i = h} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = ε ∙ x₄ ∙ x ∙ X} {Γ = ε ∙ x₅ ∙ x₁} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-wk π₀} {π = wk-cong π} {π' = wk-wk π'} {i = h} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = ε ∙ x₄ ∙ x ∙ X} {Γ = Γ ∙ x₆ ∙ x₅ ∙ x₁} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-wk π₀} {π = wk-cong π} {π' = wk-wk π'} {i = h} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = Δ ∙ x₆ ∙ x₄ ∙ x ∙ X} {Γ = ε ∙ x₅ ∙ x₁} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-wk π₀} {π = wk-cong π} {π' = wk-wk π'} {i = h} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = Δ ∙ x₆ ∙ x₄ ∙ x ∙ X} {Γ = Γ ∙ x₇ ∙ x₅ ∙ x₁} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-wk π₀} {π = wk-cong π} {π' = wk-wk π'} {i = h} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = ε ∙ x ∙ X} {Γ = ε ∙ x₄ ∙ x₁} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-wk π₀} {π = wk-wk π} {π' = wk-wk π'} {i = t i} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = ε ∙ x ∙ X} {Γ = Γ ∙ x₅ ∙ x₄ ∙ x₁} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-wk π₀} {π = wk-wk π} {π' = wk-wk π'} {i = t i} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = ε ∙ x₄ ∙ x ∙ X} {Γ = ε ∙ x₅ ∙ x₁} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-wk π₀} {π = wk-wk π} {π' = wk-wk π'} {i = t i} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = ε ∙ x₄ ∙ x ∙ X} {Γ = Γ ∙ x₆ ∙ x₅ ∙ x₁} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-wk π₀} {π = wk-wk π} {π' = wk-wk π'} {i = t i} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = Δ ∙ x₆ ∙ x₄ ∙ x ∙ X} {Γ = ε ∙ x₅ ∙ x₁} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-wk π₀} {π = wk-wk π} {π' = wk-wk π'} {i = t i} {i' = h} {i'' = h} MG₁ MG₂ = refl
  memgc-wk-eq {Δ = Δ ∙ x₆ ∙ x₄ ∙ x ∙ X} {Γ = Γ ∙ x₇ ∙ x₅ ∙ x₁} {Γ' = ε ∙ x₂} {Γ'' = ε ∙ x₃} {π₀ = wk-wk π₀} {π = wk-wk π} {π' = wk-wk π'} {i = t i} {i' = h} {i'' = h} MG₁ MG₂ = refl

  mutual
    valgc-wk-eq : {Δ Γ Γ' Γ'' : Ctx} {π₀ : Wk Δ Γ} {π : Wk Γ Γ'} {π' : Wk Δ Γ''} {M : Val Γ X} {M' : Val Γ' X} {M'' : Val Γ'' X}
                → (MG₁ : ValGC Γ Γ' π M M') → (MG₂ : ValGC Δ Γ'' π' (wk-val π₀ M) M'')
                → Γ' ≡ Γ''

    valgc-wk-eq {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = M'} {M'' = M''} (var i₁) (var i₂) = memgc-wk-eq i₁ i₂
    valgc-wk-eq {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = M'} {M'' = M''} (lam W₁) (lam W₂) = pred-ctx-eq (compgc-wk-eq W₁ W₂)
    valgc-wk-eq {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = M'} {M'' = M''} (pair MG₁₁ MG₂₁) (pair MG₁₂ MG₂₂) =
                let
                  IH1 = valgc-wk-eq MG₁₁ MG₁₂
                  -- IH2 = valgc-wk-eq MG₂₁ MG₂₂ -- interestingly I do not seem to need this
                in
                IH1
    valgc-wk-eq {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = M'} {M'' = M''} (pm M₁ N₁) (pm M₂ N₂) = valgc-wk-eq M₁ M₂
    valgc-wk-eq {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = M'} {M'' = M''} unit unit = refl

    compgc-wk-eq : {Δ Γ Γ' Γ'' : Ctx} {π₀ : Wk Δ Γ} {π : Wk Γ Γ'} {π' : Wk Δ Γ''} {W : Comp Γ X} {W' : Comp Γ' X} {W'' : Comp Γ'' X}
                → (MG₁ : CompGC Γ Γ' π W W') → (MG₂ : CompGC Δ Γ'' π' (wk-comp π₀ W) W'')
                → Γ' ≡ Γ''
    compgc-wk-eq {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π₀ = π₀} {π = π} {π' = π'} {W = W} {W' = W'} {W'' = W''} (return M₁) (return M₂) = valgc-wk-eq M₁ M₂
    compgc-wk-eq {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π₀ = π₀} {π = π} {π' = π'} {W = W} {W' = W'} {W'' = W''} (pm M₁ N₁) (pm M₂ N₂) = valgc-wk-eq M₁ M₂
    compgc-wk-eq {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π₀ = π₀} {π = π} {π' = π'} {W = W} {W' = W'} {W'' = W''} (push W₁₁ W₂₁) (push W₁₂ W₂₂) = compgc-wk-eq W₁₁ W₁₂
    compgc-wk-eq {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π₀ = π₀} {π = π} {π' = π'} {W = W} {W' = W'} {W'' = W''} (app M₁ N₁) (app M₂ N₂) = valgc-wk-eq M₁ M₂
    compgc-wk-eq {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π₀ = π₀} {π = π} {π' = π'} {W = W} {W' = W'} {W'' = W''} (var M₁) (var M₂) = valgc-wk-eq M₁ M₂
    compgc-wk-eq {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π₀ = π₀} {π = π} {π' = π'} {W = W} {W' = W'} {W'' = W''} (sub W₁₁ W₂₁) (sub W₁₂ W₂₂) = compgc-wk-eq W₂₁ W₂₂

  -------


  {-
  mem-uip : {i i' : Γ ∋ X} {i≡i'₁ i≡i'₂ : i ≡ i'} → i≡i'₁ ≡ i≡i'₂
  mem-uip {i = Cx.h} {i' = Cx.h} {i≡i'₁ = refl} {i≡i'₂ = refl} = refl
  mem-uip {i = Cx.t i} {i' = Cx.t i'} {i≡i'₁ = refl} {i≡i'₂ = refl} = refl

  memgc-wk₀-eq : {Δ Γ Γ' : Ctx} {π₀ : Wk Δ Γ} {π : Wk Γ Γ'} {π' : Wk Δ Γ'} {i : Γ ∋ X} {i' i'' : Γ' ∋ X}
               → (MG₁ : MemGC Γ Γ' π i i') → (MG₂ : MemGC Δ Γ' π' (wk-mem π₀ i) i'')
               → i' ≡ i''
  memgc-wk₀-eq {Δ = Δ} {Γ = Γ} {Γ' = Γ' ∙ X} {π₀ = π₀} {π = π} {π' = π'} {i = i} {i' = Cx.h {A = X}} {i'' = Cx.h} MG₁ MG₂ = refl

  -- memgc-wk₀-eq : {Δ Γ Γ' : Ctx} {π₀ : Wk Δ Γ} {π : Wk Γ Γ'} {π' : Wk Δ Γ'} {i : Γ ∋ X} {i' i'' : Γ' ∋ X}
  --              → (MG₁ : MemGC Γ Γ' π i i') → (MG₂ : MemGC Δ Γ' π' (wk-mem π₀ i) i'')
  --              → (wk-trans π₀ π , i') ≡ (π' , i'')
  -- memgc-wk₀-eq {Δ = Δ} {Γ = Γ} {Γ' = Γ' ∙ X} {π₀ = π₀} {π = π} {π' = π'} {i = i} {i' = Cx.h {A = X}} {i'' = Cx.h} MG₁ MG₂ = ?

  memgc-subst-eq : {Δ Γ Γ' Γ'' : Ctx} {π₀ : Wk Δ Γ} {π : Wk Γ Γ'} {π' : Wk Δ Γ''} {i : Γ ∋ X} {i' : Γ' ∋ X} {i'' : Γ'' ∋ X}
               → (MG₁ : MemGC Γ Γ' π i i') → (MG₂ : MemGC Δ Γ'' π' (wk-mem π₀ i) i'')
               → (ctxeq : Γ'' ≡ Γ') → (i' ≡ proj₂ (subst (λ z → Wk Δ z × z ∋ X) ctxeq (π' , i'')))
  memgc-subst-eq {Δ = Δ} {Γ = Γ} {Γ' = Γ' ∙ X} {Γ'' = Γ'' ∙ X} {π₀ = π₀} {π = π} {π' = π'} {i = i} {i' = Cx.h {A = X}} {i'' = Cx.h} MG₁ MG₂ ctxeq =
    let
      eq = dcong₂ (λ (x : Ctx) (y : (Wk Δ x) × (x ∋ X)) → x , proj₁ y , proj₂ y) {y₁ = π' , h} ctxeq refl
      MG₂' : MemGC Δ (Γ' ∙ X) (proj₁ (subst (λ z → Wk Δ z × z ∋ X) ctxeq (π' , h))) (wk-mem π₀ i) (proj₂ (subst (λ z → Wk Δ z × z ∋ X) ctxeq (π' , h)))
      MG₂' = subst (λ x → MemGC Δ (proj₁ x) (proj₁ (proj₂ x)) (wk-mem π₀ i) (proj₂ (proj₂ x))) eq MG₂
    in
    memgc-wk₀-eq MG₁ MG₂'

  ------
  -}

  subst-lemma-var : (i : Γ ∋ X) → (i' : Γ' ∋ X) → (Γ≡Γ' : Γ ≡ Γ') → (i≅i' : i ≅ i')
         → subst (λ x → Val x X) Γ≡Γ' (var i) ≅ Val.var (subst (λ x → x) (H.≅-to-type-≡ i≅i') i)
  subst-lemma-var h h refl _≅_.refl = _≅_.refl
  subst-lemma-var h (t i') refl ()
  subst-lemma-var (t i) h refl ()
  subst-lemma-var (t i) (t i') refl _≅_.refl = _≅_.refl

  subst-lemma-pair : (M₁ : Val Γ X) → (M₂ : Val Γ Y) → (M₁' : Val Γ' X) → (M₂' : Val Γ' Y) → (Γ≡Γ' : Γ ≡ Γ') → (M₁≅M₁' : M₁ ≅ M₁') → (M₂≅M₂' : M₂ ≅ M₂')
                   → subst (λ x → Val x (X `× Y)) Γ≡Γ' (pair M₁ M₂) ≅ Val.pair (subst (λ x → x) (H.≅-to-type-≡ M₁≅M₁') M₁) (subst (λ x → x) (H.≅-to-type-≡ M₂≅M₂') M₂)
  subst-lemma-pair M₁ M₂ M₁' M₂' refl _≅_.refl _≅_.refl = _≅_.refl

  subst-lemma-pm : (M : Val Γ (A `× B)) → (N : Val (Γ ∙ A ∙ B) Z) → (M' : Val Γ' (A `× B)) → (N' : Val (Γ' ∙ A ∙ B) Z) → (Γ≡Γ' : Γ ≡ Γ') → (M≅M' : M ≅ M') → (N≅N' : N ≅ N')
                   → subst (λ x → Val x Z) Γ≡Γ' (pm M N) ≅ Val.pm (subst (λ x → x) (H.≅-to-type-≡ M≅M') M) (subst (λ x → x) (H.≅-to-type-≡ N≅N') N)
  subst-lemma-pm M N M' N' refl _≅_.refl _≅_.refl = _≅_.refl

  subst-lemma-lam : (W : Comp (Γ ∙ X) Y) → (W' : Comp (Γ' ∙ X) Y) → (Γ≡Γ' : Γ ≡ Γ') → (W≅W' : W ≅ W')
                   → subst (λ x → Val x (X `⇒ Y)) Γ≡Γ' (lam W) ≅ Val.lam (subst (λ x → x) (H.≅-to-type-≡ W≅W') W)
  subst-lemma-lam W W' refl _≅_.refl = _≅_.refl

  subst-lemma-return : (M : Val Γ X) → (M' : Val Γ' X) → (Γ≡Γ' : Γ ≡ Γ') → (M≅M' : M ≅ M')
                   → subst (λ x → Comp x X) Γ≡Γ' (return M) ≅ Comp.return (subst (λ x → x) (H.≅-to-type-≡ M≅M') M)
  subst-lemma-return M M' refl _≅_.refl = _≅_.refl

  subst-lemma-pm-comp : (M : Val Γ (A `× B)) → (N : (Γ ∙ A ∙ B) ⊢ᶜ C)
                      → (M' : Val Γ' (A `× B)) → (N' : (Γ' ∙ A ∙ B) ⊢ᶜ C)
                      → (Γ≡Γ' : Γ ≡ Γ') → (M≅M' : M ≅ M') → (N≅N' : N ≅ N')
                      → subst (λ x → x ⊢ᶜ C) Γ≡Γ' (Comp.pm M N) ≅ Comp.pm (subst (λ x → x) (H.≅-to-type-≡ M≅M') M) (subst (λ x → x) (H.≅-to-type-≡ N≅N') N)
  subst-lemma-pm-comp M N M' N' refl _≅_.refl _≅_.refl = _≅_.refl

  subst-lemma-push : (M : Γ ⊢ᶜ A) → (N : (Γ ∙ A) ⊢ᶜ B)
                  → (M' : Γ' ⊢ᶜ A) → (N' : (Γ' ∙ A) ⊢ᶜ B)
                  → (Γ≡Γ' : Γ ≡ Γ') → (M≅M' : M ≅ M') → (N≅N' : N ≅ N')
                  → subst (λ x → x ⊢ᶜ B) Γ≡Γ' (Comp.push M N) ≅ Comp.push (subst (λ x → x) (H.≅-to-type-≡ M≅M') M) (subst (λ x → x) (H.≅-to-type-≡ N≅N') N)
  subst-lemma-push M N M' N' refl _≅_.refl _≅_.refl = _≅_.refl

  subst-lemma-app : (f : Val Γ (A `⇒ B)) → (x : Val Γ A)
                  → (f' : Val Γ' (A `⇒ B)) → (x' : Val Γ' A)
                  → (Γ≡Γ' : Γ ≡ Γ') → (f≅f' : f ≅ f') → (x≅x' : x ≅ x')
                  → subst (λ y → y ⊢ᶜ B) Γ≡Γ' (Comp.app f x) ≅ Comp.app (subst (λ z → z) (H.≅-to-type-≡ f≅f') f) (subst (λ z → z) (H.≅-to-type-≡ x≅x') x)
  subst-lemma-app f x f' x' refl _≅_.refl _≅_.refl = _≅_.refl

  subst-lemma-var-comp : (M : Val Γ `V) → (M' : Val Γ' `V) → (Γ≡Γ' : Γ ≡ Γ') → (M≅M' : M ≅ M')
                      → subst (λ x → x ⊢ᶜ X) Γ≡Γ' (Comp.var {A = X} M) ≅ Comp.var {A = X} (subst (λ x → x) (H.≅-to-type-≡ M≅M') M)
  subst-lemma-var-comp M M' refl _≅_.refl = _≅_.refl

  subst-lemma-sub : (M : (Γ ∙ `V) ⊢ᶜ A) → (N : Γ ⊢ᶜ A)
                  → (M' : (Γ' ∙ `V) ⊢ᶜ A) → (N' : Γ' ⊢ᶜ A)
                  → (Γ≡Γ' : Γ ≡ Γ') → (M≅M' : M ≅ M') → (N≅N' : N ≅ N')
                  → subst (λ x → x ⊢ᶜ A) Γ≡Γ' (Comp.sub M N)
                  ≅ Comp.sub (subst (λ x → x) (H.≅-to-type-≡ M≅M') M) (subst (λ x → x) (H.≅-to-type-≡ N≅N') N)
  subst-lemma-sub M N M' N' refl _≅_.refl _≅_.refl = _≅_.refl


  memgc-heq : {Δ Γ Γ' Γ'' : Ctx} {π₀ : Wk Δ Γ} {π : Wk Γ Γ'} {π' : Wk Δ Γ''} {i : Γ ∋ X} {i' : Γ' ∋ X} {i'' : Γ'' ∋ X}
               → (MG₁ : MemGC Γ Γ' π i i') → (MG₂ : MemGC Δ Γ'' π' (wk-mem π₀ i) i'')
               → (i' ≅ i'')
  memgc-heq {Δ = Δ} {Γ = Γ} {Γ' = ε ∙ X} {Γ'' = ε ∙ X} {π₀ = π₀} {π = π} {π' = π'} {i = i} {i' = h {A = X}} {i'' = h} MG₁ MG₂ = _≅_.refl

  mutual
    valgc-heq : {Δ Γ Γ' Γ'' : Ctx} {π₀ : Wk Δ Γ} {π : Wk Γ Γ'} {π' : Wk Δ Γ''} {M : Val Γ X} {M' : Val Γ' X} {M'' : Val Γ'' X}
                → (MG₁ : ValGC Γ Γ' π M M') → (MG₂ : ValGC Δ Γ'' π' (wk-val π₀ M) M'')
                → (M' ≅ M'')
    -- valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = M'} {M'' = M''} MG₁ MG₂ = ?
    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Cx.ε} {Γ'' = Cx.ε} {π₀ = π₀} {π = π} {π' = π'} {M = lam W} {M' = lam W'} {M'' = lam W''} (lam WG₁) (lam WG₂) = H.cong lam (compgc-heq WG₁ WG₂)
    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = ε} {Γ'' = ε} {π₀ = π₀} {π = π} {π' = π'} {M = pair M₁ M₂} {M' = pair M₁' M₂'} {M'' = pair M₁'' M₂''} (pair MG₁₁ MG₂₁) (pair MG₁₂ MG₂₂) =
      let
        IH1 = valgc-heq MG₁₁ MG₁₂
        IH2 = valgc-heq MG₂₁ MG₂₂
      in
      H.cong₂ pair IH1 IH2
    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = ε} {Γ'' = ε} {π₀ = π₀} {π = π} {π' = π'} {M = pm M N} {M' = pm M' N'} {M'' = pm M'' N''} (pm MG₁ NG₁) (pm MG₂ NG₂) =
      let
        IH1 = valgc-heq MG₁ MG₂
        IH2 = valgc-heq NG₁ NG₂
      in
      H.cong₂ pm IH1 IH2
    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = ε} {Γ'' = ε} {π₀ = π₀} {π = π} {π' = π'} {M = unit} {M' = unit} {M'' = unit} MG₁ MG₂ = _≅_.refl

    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = ε} {Γ'' = Γ'' ∙ X} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = M'} {M'' = M''} MG₁ MG₂ =
      let
        eq = valgc-wk-eq MG₁ MG₂
      in
      ql (ctx-absurd eq) (M' ≅ M'')

    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' ∙ X'} {Γ'' = ε} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = M'} {M'' = M''} MG₁ MG₂ =
      let
        eq = valgc-wk-eq MG₁ MG₂
      in
      ql (ctx-absurd (sym eq)) (M' ≅ M'')

    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = var {A = X} i'} {M'' = var {A = X} i''} (var MG₁) (var MG₂) =
      let
        eq = memgc-wk-eq MG₁ MG₂

        i'≅i'' : i' ≅ i''
        i'≅i'' = memgc-heq MG₁ MG₂

        i'≡i''₂ = H.≅-to-subst-≡ i'≅i''

        g : var (subst (λ x → x) (H.≅-to-type-≡ i'≅i'') i') ≡ var i''
        g = cong (var {Γ = Γ'' ∙ X''}) i'≡i''₂

        g' : subst (λ x → Val x X) eq (var i') ≅ Val.var (subst (λ x → x) (H.≅-to-type-≡ i'≅i'') i')
        g' = subst-lemma-var i' i'' eq i'≅i''

        g'' : subst (λ x → Val x X) eq (var i') ≅ var i'
        g'' = H.≡-subst-removable (λ x → Val x X) eq (var i')

        goal : var i' ≅ var i''
        goal =  H.trans (H.sym g'') (H.trans g' (≡-to-≅ g))
      in
      goal
    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = var i'} {M'' = lam x} (var x₁) ()
    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = var i'} {M'' = pair M'' M'''} (var x) ()
    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = var i'} {M'' = pm M'' M'''} (var x) ()
    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = var i'} {M'' = unit} (var x) ()
    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = lam x} {M'' = var i} (lam WG) ()

    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = lam {A = X} {B = Y} W'} {M'' = lam W''} (lam WG₁) (lam WG₂) =
      let
        eq = valgc-wk-eq (lam WG₁) (lam WG₂)

        W'≅W'' : W' ≅ W''
        W'≅W'' = compgc-heq WG₁ WG₂

        W'≡W''₂ = H.≅-to-subst-≡ W'≅W''

        g : lam (subst (λ x → x) (H.≅-to-type-≡ W'≅W'') W') ≡ lam W''
        g = cong lam W'≡W''₂

        g' : subst (λ x → Val x (X `⇒ Y)) eq (lam W') ≅ Val.lam (subst (λ x → x) (H.≅-to-type-≡ W'≅W'') W')
        g' = subst-lemma-lam W' W'' (pred-ctx-eq (compgc-wk-eq WG₁ WG₂)) W'≅W''

        g'' : subst (λ x → Val x (X `⇒ Y)) eq (lam W') ≅ lam W'
        g'' = H.≡-subst-removable (λ x → Val x (X `⇒ Y)) eq (lam W')

        goal : lam W' ≅ lam W''
        goal =  H.trans (H.sym g'') (H.trans g' (≡-to-≅ g))
      in
      goal

    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = lam x} {M'' = pm M'' M'''} (lam WG) ()
    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = pair M' M''} {M'' = var i} (pair MG₁ MG₂) ()

    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = pair {A = X} {B = Y} M₁' M₂'} {M'' = pair M₁'' M₂''} (pair MG₁₁ MG₂₁) (pair MG₁₂ MG₂₂) =
      let
        eq = valgc-wk-eq MG₁₁ MG₁₂

        M₁'≅M₁'' = valgc-heq MG₁₁ MG₁₂
        M₂'≅M₂'' = valgc-heq MG₂₁ MG₂₂

        M₁'≅M₁''₂ = H.≅-to-subst-≡ M₁'≅M₁''
        M₂'≅M₂''₂ = H.≅-to-subst-≡ M₂'≅M₂''

        g : pair (subst (λ x → x) (H.≅-to-type-≡ M₁'≅M₁'') M₁') (subst (λ x → x) (H.≅-to-type-≡ M₂'≅M₂'') M₂') ≡ pair M₁'' M₂''
        g = cong₂ pair M₁'≅M₁''₂ M₂'≅M₂''₂

        g' : subst (λ x → Val x (X `× Y)) eq (pair M₁' M₂') ≅ Val.pair (subst (λ x → x) (H.≅-to-type-≡ M₁'≅M₁'') M₁') (subst (λ x → x) (H.≅-to-type-≡ M₂'≅M₂'') M₂')
        g' = subst-lemma-pair M₁' M₂' M₁'' M₂'' eq M₁'≅M₁'' M₂'≅M₂''

        g'' : subst (λ x → Val x (X `× Y)) eq (pair M₁' M₂') ≅ pair M₁' M₂'
        g'' = H.≡-subst-removable (λ x → Val x (X `× Y)) eq (pair M₁' M₂')

        goal : pair M₁' M₂' ≅ pair M₁'' M₂''
        goal = H.trans (H.sym g'') (H.trans g' (≡-to-≅ g))
      in
      goal

    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = pair M' M''} {M'' = pm M''' M''''} (pair MG₁ MG₂) ()
    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = pm M' M''} {M'' = var i} (pm MG₁ MG₂) ()
    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = pm M' M''} {M'' = lam x} (pm MG₁ MG₂) ()
    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = pm M' M''} {M'' = pair M''' M''''} (pm MG₁ MG₂) ()

    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = pm {C = Z} M' N'} {M'' = pm M'' N''} (pm MG₁ NG₁) (pm MG₂ NG₂) =
      let
        eq = valgc-wk-eq MG₁ MG₂

        M'≅M'' = valgc-heq MG₁ MG₂
        N'≅N'' = valgc-heq NG₁ NG₂

        M'≅M''₂ = H.≅-to-subst-≡ M'≅M''
        N'≅N''₂ = H.≅-to-subst-≡ N'≅N''

        g : pm (subst (λ x → x) (H.≅-to-type-≡ M'≅M'') M') (subst (λ x → x) (H.≅-to-type-≡ N'≅N'') N') ≡ pm M'' N''
        g = cong₂ pm M'≅M''₂ N'≅N''₂

        g' : subst (λ x → Val x Z) eq (pm M' N') ≅ Val.pm (subst (λ x → x) (H.≅-to-type-≡ M'≅M'') M') (subst (λ x → x) (H.≅-to-type-≡ N'≅N'') N')
        g' = subst-lemma-pm M' N' M'' N'' eq M'≅M'' N'≅N''

        g'' : subst (λ x → Val x Z) eq (pm M' N') ≅ pm M' N'
        g'' = H.≡-subst-removable (λ x → Val x Z) eq (pm M' N')

        goal : pm M' N' ≅ pm M'' N''
        goal = H.trans (H.sym g'') (H.trans g' (≡-to-≅ g))
      in
      goal

    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = pm M' M''} {M'' = unit} (pm MG₁ MG₂) ()
    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = unit} {M'' = var i} () MG₂
    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = unit} {M'' = pm M'' M'''} () MG₂
    valgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ' Cx.∙ X'} {Γ'' = Γ'' Cx.∙ X''} {π₀ = π₀} {π = π} {π' = π'} {M = M} {M' = unit} {M'' = unit} () MG₂

    compgc-heq : {Δ Γ Γ' Γ'' : Ctx} {π₀ : Wk Δ Γ} {π : Wk Γ Γ'} {π' : Wk Δ Γ''} {W : Comp Γ X} {W' : Comp Γ' X} {W'' : Comp Γ'' X}
                → (WG₁ : CompGC Γ Γ' π W W') → (WG₂ : CompGC Δ Γ'' π' (wk-comp π₀ W) W'')
                → (W' ≅ W'')
    compgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π₀ = π₀} {π = π} {π' = π'} {W = W} {W' = return {A = X} M'} {W'' = return M''} (return MG₁) (return MG₂) =
       let
         eq = valgc-wk-eq MG₁ MG₂

         M'≅M'' = valgc-heq MG₁ MG₂

         M'≅M''₂ = H.≅-to-subst-≡ M'≅M''

         g : return (subst (λ x → x) (H.≅-to-type-≡ M'≅M'') M') ≡ return M''
         g = cong return M'≅M''₂

         g' : subst (λ x → Comp x X) eq (return M') ≅ Comp.return (subst (λ x → x) (H.≅-to-type-≡ M'≅M'') M')
         g' = subst-lemma-return M' M'' eq M'≅M''

         g'' : subst (λ x → Comp x X) eq (return M') ≅ return M'
         g'' = H.≡-subst-removable (λ x → Comp x X) eq (return M')

         goal : return M' ≅ return M''
         goal = H.trans (H.sym g'') (H.trans g' (≡-to-≅ g))
       in
       goal
    compgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π₀ = π₀} {π = π} {π' = π'} {W = W} {W' = pm {C = C} M' W'} {W'' = pm M'' W''} (pm MG₁ WG₁) (pm MG₂ WG₂) =
      let
        eq = valgc-wk-eq MG₁ MG₂

        M'≅M'' = valgc-heq MG₁ MG₂
        W'≅W'' = compgc-heq WG₁ WG₂

        M'≅M''₂ = H.≅-to-subst-≡ M'≅M''
        W'≅W''₂ = H.≅-to-subst-≡ W'≅W''

        g : pm (subst (λ x → x) (H.≅-to-type-≡ M'≅M'') M') (subst (λ x → x) (H.≅-to-type-≡ W'≅W'') W') ≡ pm M'' W''
        g = cong₂ pm M'≅M''₂ W'≅W''₂

        g' : subst (λ x → x ⊢ᶜ C) eq (pm M' W') ≅ Comp.pm (subst (λ x → x) (H.≅-to-type-≡ M'≅M'') M') (subst (λ x → x) (H.≅-to-type-≡ W'≅W'') W')
        g' = subst-lemma-pm-comp M' W' M'' W'' eq M'≅M'' W'≅W''

        g'' : subst (λ x → x ⊢ᶜ C) eq (pm M' W') ≅ pm M' W'
        g'' = H.≡-subst-removable (λ x → x ⊢ᶜ C) eq (pm M' W')

        goal : pm M' W' ≅ pm M'' W''
        goal = H.trans (H.sym g'') (H.trans g' (≡-to-≅ g))
      in
      goal
    compgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π₀ = π₀} {π = π} {π' = π'} {W = W} {W' = push {B = B} W₁' W₂'} {W'' = push W₁'' W₂''} (push WG₁₁ WG₂₁) (push WG₁₂ WG₂₂) =
      let
        eq = compgc-wk-eq WG₁₁ WG₁₂

        W₁'≅W₁'' = compgc-heq WG₁₁ WG₁₂
        W₂'≅W₂'' = compgc-heq WG₂₁ WG₂₂

        W₁'≅W₁''₂ = H.≅-to-subst-≡ W₁'≅W₁''
        W₂'≅W₂''₂ = H.≅-to-subst-≡ W₂'≅W₂''

        g : push (subst (λ x → x) (H.≅-to-type-≡ W₁'≅W₁'') W₁') (subst (λ x → x) (H.≅-to-type-≡ W₂'≅W₂'') W₂') ≡ push W₁'' W₂''
        g = cong₂ push W₁'≅W₁''₂ W₂'≅W₂''₂

        g' : subst (λ x → x ⊢ᶜ B) eq (push W₁' W₂') ≅ Comp.push (subst (λ x → x) (H.≅-to-type-≡ W₁'≅W₁'') W₁') (subst (λ x → x) (H.≅-to-type-≡ W₂'≅W₂'') W₂')
        g' = subst-lemma-push W₁' W₂' W₁'' W₂'' eq W₁'≅W₁'' W₂'≅W₂''

        g'' : subst (λ x → x ⊢ᶜ B) eq (push W₁' W₂') ≅ push W₁' W₂'
        g'' = H.≡-subst-removable (λ x → x ⊢ᶜ B) eq (push W₁' W₂')

        goal : push W₁' W₂' ≅ push W₁'' W₂''
        goal = H.trans (H.sym g'') (H.trans g' (≡-to-≅ g))
      in
      goal
    compgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π₀ = π₀} {π = π} {π' = π'} {W = W} {W' = app {B = B} M' N'} {W'' = app M'' N''} (app MG₁ NG₁) (app MG₂ NG₂) =
      let
        eq = valgc-wk-eq MG₁ MG₂

        M'≅M'' = valgc-heq MG₁ MG₂
        N'≅N'' = valgc-heq NG₁ NG₂

        M'≅M''₂ = H.≅-to-subst-≡ M'≅M''
        N'≅N''₂ = H.≅-to-subst-≡ N'≅N''

        g : app (subst (λ x → x) (H.≅-to-type-≡ M'≅M'') M') (subst (λ x → x) (H.≅-to-type-≡ N'≅N'') N') ≡ app M'' N''
        g = cong₂ app M'≅M''₂ N'≅N''₂

        g' : subst (λ x → x ⊢ᶜ B) eq (app M' N') ≅ Comp.app (subst (λ x → x) (H.≅-to-type-≡ M'≅M'') M') (subst (λ x → x) (H.≅-to-type-≡ N'≅N'') N')
        g' = subst-lemma-app M' N' M'' N'' eq M'≅M'' N'≅N''

        g'' : subst (λ x → x ⊢ᶜ B) eq (app M' N') ≅ app M' N'
        g'' = H.≡-subst-removable (λ x → x ⊢ᶜ B) eq (app M' N')

        goal : app M' N' ≅ app M'' N''
        goal = H.trans (H.sym g'') (H.trans g' (≡-to-≅ g))
      in
      goal
    compgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π₀ = π₀} {π = π} {π' = π'} {W = W} {W' = var {A = X} M'} {W'' = var {A = X} M''} (var MG₁) (var MG₂) =
      let
        eq = valgc-wk-eq MG₁ MG₂

        M'≅M'' = valgc-heq MG₁ MG₂
        M'≅M''₂ = H.≅-to-subst-≡ M'≅M''

        g : var (subst (λ x → x) (H.≅-to-type-≡ M'≅M'') M') ≡ var M''
        g = cong var M'≅M''₂

        g' : subst (λ x → x ⊢ᶜ X) eq (var M') ≅ Comp.var (subst (λ x → x) (H.≅-to-type-≡ M'≅M'') M')
        g' = subst-lemma-var-comp M' M'' eq M'≅M''

        g'' : subst (λ x → x ⊢ᶜ X) eq (var M') ≅ var M'
        g'' = H.≡-subst-removable (λ x → x ⊢ᶜ X) eq (var M')

        goal : var M' ≅ var M''
        goal = H.trans (H.sym g'') (H.trans g' (≡-to-≅ g))
      in
      goal
    compgc-heq {Δ = Δ} {Γ = Γ} {Γ' = Γ'} {Γ'' = Γ''} {π₀ = π₀} {π = π} {π' = π'} {W = W} {W' = sub {A = A} W₁' W₂'} {W'' = sub {A = A} W₁'' W₂''} (sub WG₁₁ WG₂₁) (sub WG₁₂ WG₂₂) =
      let
        eq = compgc-wk-eq WG₂₁ WG₂₂

        W₁'≅W₁'' = compgc-heq WG₁₁ WG₁₂
        W₂'≅W₂'' = compgc-heq WG₂₁ WG₂₂

        W₁'≅W₁''₂ = H.≅-to-subst-≡ W₁'≅W₁''
        W₂'≅W₂''₂ = H.≅-to-subst-≡ W₂'≅W₂''

        g : sub (subst (λ x → x) (H.≅-to-type-≡ W₁'≅W₁'') W₁') (subst (λ x → x) (H.≅-to-type-≡ W₂'≅W₂'') W₂') ≡ sub W₁'' W₂''
        g = cong₂ sub W₁'≅W₁''₂ W₂'≅W₂''₂

        g' : subst (λ x → x ⊢ᶜ A) eq (sub W₁' W₂') ≅ Comp.sub (subst (λ x → x) (H.≅-to-type-≡ W₁'≅W₁'') W₁') (subst (λ x → x) (H.≅-to-type-≡ W₂'≅W₂'') W₂')
        g' = subst-lemma-sub W₁' W₂' W₁'' W₂'' eq W₁'≅W₁'' W₂'≅W₂''

        g'' : subst (λ x → x ⊢ᶜ A) eq (sub W₁' W₂') ≅ sub W₁' W₂'
        g'' = H.≡-subst-removable (λ x → x ⊢ᶜ A) eq (sub W₁' W₂')

        goal : sub W₁' W₂' ≅ sub W₁'' W₂''
        goal = H.trans (H.sym g'') (H.trans g' (≡-to-≅ g))
      in
      goal



  mem-gc : (i : Γ ∋ X) → GCMem i
  mem-gc h = record { gmwk = wk-cong wk-wk-ε ; gmgc = h }
  mem-gc (t i) = record { gmwk = wk-wk (gmwk (mem-gc i)) ; gmgc = t (gmgc (mem-gc i)) }



{-
  mem-gc : Γ ∋ X → Σ[ Γ' ∈ Ctx ] ((Γ' ∋ X) × (Wk Γ Γ'))
  mem-gc {Γ = Γ ∙ X} h = ε ∙ X , h , wk-cong wk-wk-ε
  mem-gc (t i) =
    let
      l = mem-gc i
    in
    proj₁ l , proj₁ (proj₂ l) , wk-wk (proj₂ (proj₂ l))

  mutual

    val-gc : Val Γ X → Σ[ Γ' ∈ Ctx ] ((Val Γ' X) × (Wk Γ Γ'))
    val-gc (var i) = let l = mem-gc i in proj₁ l , var (proj₁ (proj₂ l)) , proj₂ (proj₂ l)
    val-gc (lam {A = X} W) with comp-gc W
    ... | Γ' ∙ X , W' , wk-cong π' = Γ' , lam W' , π'
    ... | ε , W' , wk-wk π' = ε , lam (wk-comp (wk-wk wk-id) W') , π'
    ... | Γ' ∙ X , W' , wk-wk π' = Γ' ∙ X , lam (wk-comp (wk-wk wk-id) W') , π'
    val-gc {Γ = Γ} (pair M₁ M₂) =
            let
              v₁ = val-gc M₁
              M₁' = proj₁ (proj₂ v₁)
              π₁ = proj₂ (proj₂ v₁)
              v₂ = val-gc M₂
              M₂' = proj₁ (proj₂ v₂)
              π₂ = proj₂ (proj₂ v₂)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , pair (wk-val π₁' M₁') (wk-val π₂' M₂') , π
    val-gc (pm {A = X} {B = Y} {C = Z} M N) with val-gc N
    ... | Γ₂ , N₂ , wk-cong (wk-cong π₂) =
            let
              v = val-gc M
              M₁ = proj₁ (proj₂ v)
              π₁ = proj₂ (proj₂ v)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , pm (wk-val π₁' M₁) (wk-val (wk-cong (wk-cong π₂')) N₂) , π
    ... | Γ₂ ∙ Y , N₂ , wk-cong (wk-wk π₂) =
            let
              v = val-gc M
              M₁ = proj₁ (proj₂ v)
              π₁ = proj₂ (proj₂ v)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , pm (wk-val π₁' M₁) (wk-val (wk-cong (wk-wk π₂')) N₂) , π
    ... | Γ₂ , N₂ , wk-wk (wk-cong π₂) =
            let
              v = val-gc M
              M₁ = proj₁ (proj₂ v)
              π₁ = proj₂ (proj₂ v)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , pm (wk-val π₁' M₁) (wk-val (wk-wk (wk-cong π₂')) N₂) , π
    ... | Γ₂ , N₂ , wk-wk (wk-wk π₂) =
            let
              v = val-gc M
              M₁ = proj₁ (proj₂ v)
              π₁ = proj₂ (proj₂ v)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , pm (wk-val π₁' M₁) (wk-val (wk-wk (wk-wk π₂')) N₂) , π
    val-gc unit = ε , unit , wk-wk-ε

    comp-gc : Comp Γ X → Σ[ Γ' ∈ Ctx ] ((Comp Γ' X) × (Wk Γ Γ'))
    comp-gc (return M) = let v = val-gc M in proj₁ v , return (proj₁ (proj₂ v)) , proj₂ (proj₂ v)
    comp-gc (pm {A = X} {B = Y} {C = Z} M W) with comp-gc W
    ... | Γ₂ , W₂ , wk-cong (wk-cong π₂) =
            let
              v = val-gc M
              M₁ = proj₁ (proj₂ v)
              π₁ = proj₂ (proj₂ v)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , pm (wk-val π₁' M₁) (wk-comp (wk-cong (wk-cong π₂')) W₂) , π
    ... | Γ₂ ∙ Y , W₂ , wk-cong (wk-wk π₂) =
            let
              v = val-gc M
              M₁ = proj₁ (proj₂ v)
              π₁ = proj₂ (proj₂ v)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , pm (wk-val π₁' M₁) (wk-comp (wk-cong (wk-wk π₂')) W₂) , π
    ... | Γ₂ , W₂ , wk-wk (wk-cong π₂) =
            let
              v = val-gc M
              M₁ = proj₁ (proj₂ v)
              π₁ = proj₂ (proj₂ v)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , pm (wk-val π₁' M₁) (wk-comp (wk-wk (wk-cong π₂')) W₂) , π
    ... | Γ₂ , W₂ , wk-wk (wk-wk π₂) =
            let
              v = val-gc M
              M₁ = proj₁ (proj₂ v)
              π₁ = proj₂ (proj₂ v)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , pm (wk-val π₁' M₁) (wk-comp (wk-wk (wk-wk π₂')) W₂) , π
    comp-gc (push {A = X} {B = Z} W₁ W₂) with comp-gc W₂
    ... | Γ₂' ∙ X , W₂' , wk-cong π₂' =
            let
              c = comp-gc W₁
              W₁' = proj₁ (proj₂ c)
              π₁' = proj₂ (proj₂ c)
              j = wk-join π₁' π₂'
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁'' = proj₁ (proj₂ (proj₂ j))
              π₂'' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , push (wk-comp π₁'' W₁') (wk-comp (wk-cong π₂'') W₂') , π
    ... | ε , W₂' , wk-wk π₂' =
            let
              c = comp-gc W₁
              W₁' = proj₁ (proj₂ c)
              π₁' = proj₂ (proj₂ c)
              j = wk-join π₁' π₂'
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁'' = proj₁ (proj₂ (proj₂ j))
              π₂'' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , push (wk-comp π₁'' W₁') (wk-comp (wk-wk π₂'') W₂') , π
    ... | Γ₂' ∙ x , W₂' , wk-wk π₂' =
            let
              c = comp-gc W₁
              W₁' = proj₁ (proj₂ c)
              π₁' = proj₂ (proj₂ c)
              j = wk-join π₁' π₂'
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁'' = proj₁ (proj₂ (proj₂ j))
              π₂'' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , push (wk-comp π₁'' W₁') (wk-comp (wk-wk π₂'') W₂') , π
    comp-gc (app M N) =
            let
              v₁ = val-gc M
              M' = proj₁ (proj₂ v₁)
              π₁ = proj₂ (proj₂ v₁)
              v₂ = val-gc N
              N' = proj₁ (proj₂ v₂)
              π₂ = proj₂ (proj₂ v₂)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , app (wk-val π₁' M') (wk-val π₂' N') , π
    comp-gc (var M) =  let v = val-gc M in proj₁ v , var (proj₁ (proj₂ v)) , proj₂ (proj₂ v)
    comp-gc (sub {A = X} W₁ W₂)  with comp-gc W₁
    ... | Γ₁' ∙ X , W₁' , wk-cong π₁' =
            let
              c = comp-gc W₂
              W₂' = proj₁ (proj₂ c)
              π₂' = proj₂ (proj₂ c)
              j = wk-join π₁' π₂'
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁'' = proj₁ (proj₂ (proj₂ j))
              π₂'' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , sub (wk-comp (wk-cong π₁'') W₁') (wk-comp π₂'' W₂') , π
    ... | ε , W₁' , wk-wk π₁' =
            let
              c = comp-gc W₂
              W₂' = proj₁ (proj₂ c)
              π₂' = proj₂ (proj₂ c)
              j = wk-join π₁' π₂'
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁'' = proj₁ (proj₂ (proj₂ j))
              π₂'' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , sub (wk-comp (wk-wk π₁'') W₁') (wk-comp π₂'' W₂') , π
    ... | Γ₁' ∙ X' , W₁' , wk-wk π₁' =
            let
              c = comp-gc W₂
              W₂' = proj₁ (proj₂ c)
              π₂' = proj₂ (proj₂ c)
              j = wk-join π₁' π₂'
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁'' = proj₁ (proj₂ (proj₂ j))
              π₂'' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , sub (wk-comp (wk-wk π₁'') W₁') (wk-comp π₂'' W₂') , π
-}
