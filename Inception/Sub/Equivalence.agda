{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Equivalence (R : Set) where

open import Agda.Primitive using (Level)

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Function.Base using (const; _∘_; _$_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; cong-app; icong; dcong₂; sym; trans; subst; subst₂)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.Renaming
open import Inception.Sub.CPS R

open import Data.Unit
open import Data.Nat
open import Data.List using (List; _∷_; []; _++_)

open import Inception.Sub.Equality
open import Inception.Sub.Environments R
open import Inception.Sub.States R
open import Inception.Sub.Machine R

module EquivMain {R₀ : Ty} (k₀ : ⟦ R₀ ⟧ → R) where
  open EnvMain {R₀ = R₀} k₀
  open StatesMain {R₀ = R₀} k₀
  open MachineMain {R₀ = R₀} k₀

  record ⟨_,_⟩←⟨_,_⟩ {Γ Δ : Ctx} {X : Ty} (j : Δ ∋ X) (δ : Env Δ) (i : Γ ∋ X) (γ : Env Γ) : Set where
    field
      wkn   : Wk Δ Γ
      -- wkext : WkExt wkn
      enveq : EnvEq wkn δ γ
      eq    : j ≡ wk-mem wkn i

  record ⟨_,_⟩←⟨_,_⟩→⟨_,_⟩ {Γ Δ₁ Δ₂ : Ctx} {X : Ty} (j₁ : Δ₁ ∋ X) (δ₁ : Env Δ₁) (i : Γ ∋ X) (γ : Env Γ) (j₂ : Δ₂ ∋ X) (δ₂ : Env Δ₂) : Set where
    field
      ext₁ : ⟨ j₁ , δ₁ ⟩←⟨ i , γ ⟩
      ext₂ : ⟨ j₂ , δ₂ ⟩←⟨ i , γ ⟩

  eqv-refl : {Γ Δ : Ctx} {X : Ty} {j : Δ ∋ X} {δ : Env Δ} {i : Γ ∋ X} {γ : Env Γ} → ⟨ j , δ ⟩←⟨ i , γ ⟩ → ⟨ j , δ ⟩←⟨ i , γ ⟩→⟨ j , δ ⟩
  eqv-refl ext = record { ext₁ = ext ; ext₂ = ext }

  eqv-trans :   {Γ Δ₁ Δ₂ Δ₃ : Ctx} {X : Ty} {i : Γ ∋ X} {γ : Env Γ} {j₁ : Δ₁ ∋ X} {δ₁ : Env Δ₁} {j₂ : Δ₂ ∋ X} {δ₂ : Env Δ₂} {j₃ : Δ₃ ∋ X} {δ₃ : Env Δ₃}
             → ⟨ j₁ , δ₁ ⟩←⟨ i , γ ⟩→⟨ j₂ , δ₂ ⟩
             → ⟨ j₂ , δ₂ ⟩←⟨ i , γ ⟩→⟨ j₃ , δ₃ ⟩
             → ⟨ j₁ , δ₁ ⟩←⟨ i , γ ⟩→⟨ j₃ , δ₃ ⟩
  eqv-trans record { ext₁ = ext₁ ; ext₂ = ext₂ } record { ext₁ = ext₃ ; ext₂ = ext₄ } = record { ext₁ = ext₁ ; ext₂ = ext₄ }

  record ⟨_∥_⟩≍ᴸ⟨_∥_⟩ {Γ₁ Γ₂ : Ctx} {X : Ty} (i₁ : Γ₁ ∋ X) (γ₁ : Env Γ₁) (i₂ : Γ₂ ∋ X) (γ₂ : Env Γ₂) : Set where
    field
      ctx   : Ctx
      env   : Env ctx
      idx   : ctx ∋ X
      eqv   : ⟨ i₁ , γ₁ ⟩←⟨ idx , env ⟩→⟨ i₂ , γ₂ ⟩

  {-
  record _≍ᴸ_ {X : Ty} (L₁ : LookupState X) (L₂ : LookupState X) : Set where
    field
      ctx   : Ctx
      env   : Env ctx
      idx   : ctx ∋ X
      ctx₁  : Ctx
      env₁  : Env ctx₁
      idx₁  : ctx₁ ∋ X
      ctx₂  : Ctx
      env₂  : Env ctx₂
      idx₂  : ctx₂ ∋ X
      eq₁   : L₁ ≡ ⟨ idx₁ ∥ env₁ ⟩
      eq₂   : L₂ ≡ ⟨ idx₂ ∥ env₂ ⟩
      eqv   : ⟨ idx₁ , env₁ ⟩←⟨ idx , env ⟩→⟨ idx₂ , env₂ ⟩
  -}

  ------------------------------------------------------------------------------------------------------
  ------------------------------------------------------------------------------------------------------

  {- OLD DEFINITIONS; must rethink this
  record _≍ᵐ_ {Γ₁ Γ₂ : Ctx} {X : Ty} (i₁ : Γ₁ ∋ X) (i₂ : Γ₂ ∋ X) : Set where
    field
      ctx  : Ctx
      wkn₁ : Wk Γ₁ ctx
      wkn₂ : Wk Γ₂ ctx
      base : ctx ∋ X
      eq₁  : i₁ ≡ wk-mem wkn₁ base
      eq₂  : i₂ ≡ wk-mem wkn₂ base

  record _≍ᵛ_ {Γ₁ Γ₂ : Ctx} {X : Ty} (M₁ : Val Γ₁ X) (M₂ : Val Γ₂ X) : Set where
    field
      ctx  : Ctx
      wkn₁ : Wk Γ₁ ctx
      wkn₂ : Wk Γ₂ ctx
      base : Val ctx X
      eq₁  : M₁ ≡ wk-val wkn₁ base
      eq₂  : M₂ ≡ wk-val wkn₂ base

  record _≍ᵉᵛ_ {Γ₁ Γ₂ : Ctx} {X : Ty} (M₁ : V̲a̲l̲ Γ₁ X) (M₂ : V̲a̲l̲ Γ₂ X) : Set where
    field
      ctx  : Ctx
      wkn₁ : Wk Γ₁ ctx
      wkn₂ : Wk Γ₂ ctx
      base : V̲a̲l̲ ctx X
      eq₁  : M₁ ≡ wk-v̲a̲l̲ wkn₁ base
      eq₂  : M₂ ≡ wk-v̲a̲l̲ wkn₂ base

  record _≍ᶜ_ {Γ₁ Γ₂ : Ctx} {X : Ty} (W₁ : Comp Γ₁ X) (W₂ : Comp Γ₂ X) : Set where
    field
      ctx  : Ctx
      wkn₁ : Wk Γ₁ ctx
      wkn₂ : Wk Γ₂ ctx
      base : Comp ctx X
      eq₁  : W₁ ≡ wk-comp wkn₁ base
      eq₂  : W₂ ≡ wk-comp wkn₂ base

  record _≍ᶜᵉᵛ_ {Γ₁ Γ₂ : Ctx} (W₁ : C̲o̲m̲p Γ₁ X) (W₂ : C̲o̲m̲p Γ₂ X) : Set where
    field
      ctx  : Ctx
      wkn₁ : Wk Γ₁ ctx
      wkn₂ : Wk Γ₂ ctx
      base : C̲o̲m̲p ctx X
      eq₁  : W₁ ≡ wk-c̲o̲m̲p wkn₁ base
      eq₂  : W₂ ≡ wk-c̲o̲m̲p wkn₂ base

  data _≍ᵖ_ : {Γ₁ Γ₂ : Ctx} → PartialTerm Γ₁ X → PartialTerm Γ₂ X → Set where
    ⭭eqv : {Γ₁ Γ₂ : Ctx} {M₁ : V̲a̲l̲ Γ₁ X} {M₂ : V̲a̲l̲ Γ₂ X}
           → (M₁ ≍ᵉᵛ M₂)
           → ((⭭ M₁) ≍ᵖ (⭭ M₂))

    ⇡eqv : {Γ₁ Γ₂ : Ctx} {X' : Ty} {M₁ : Γ₁ ⊢ᵛ X'} {M₂ : Γ₂ ⊢ᵛ X'}
           → (M₁ ≍ᵛ M₂)
           → ((⇡ M₁) ≍ᵖ (⇡ M₂))

    ⇡ᴹeqv : {Γ₁ Γ₂ : Ctx} {Y Z : Ty} {M₁ : Γ₁ ⊢ᵛ X `× Y} {M₂ : Γ₂ ⊢ᵛ X `× Y} {N₁ : (Γ₁ ∙ X ∙ Y) ⊢ᵛ Z} {N₂ : (Γ₂ ∙ X ∙ Y) ⊢ᵛ Z}
            → (M₁ ≍ᵛ M₂) → (N₁ ≍ᵛ N₂)
            → ((⇡ᴹ M₁ N₁) ≍ᵖ (⇡ᴹ M₂ N₂))

    ⇡ᴸeqv : {Γ₁ Γ₂ : Ctx} {Y : Ty} {LHS₁ : Γ₁ ⊢ᵛ X} {LHS₂ : Γ₂ ⊢ᵛ X} {RHS₁ : Γ₁ ⊢ᵛ Y} {RHS₂ : Γ₂ ⊢ᵛ Y}
            → (LHS₁ ≍ᵛ LHS₂) → (RHS₁ ≍ᵛ RHS₂)
            → ((⇡ᴸ LHS₁ RHS₁) ≍ᵖ (⇡ᴸ LHS₂ RHS₂))

    ⇡ᴿeqv : {Γ₁ Γ₂ : Ctx} {Y : Ty} {LHS₁ : V̲a̲l̲ Γ₁ X} {LHS₂ : V̲a̲l̲ Γ₂ X} {RHS₁ : Γ₁ ⊢ᵛ Y} {RHS₂ : Γ₂ ⊢ᵛ Y}
            → (LHS₁ ≍ᵉᵛ LHS₂) → (RHS₁ ≍ᵛ RHS₂)
            → ((⇡ᴿ LHS₁ RHS₁) ≍ᵖ (⇡ᴿ LHS₂ RHS₂))

  ≍ᵐ-refl : {Γ : Ctx} {X : Ty} → (i : Γ ∋ X) → i ≍ᵐ i
  ≍ᵐ-refl {Γ = Γ} i = record { ctx = Γ ; wkn₁ = wk-id ; wkn₂ = wk-id ; base = i ; eq₁ = sym wk-mem-id ; eq₂ = sym wk-mem-id }

  min-mem : (i : (Γ ∋ X)) → Σ[ π ∈ Wk Γ (ε ∙ X) ] (i ≡ wk-mem π h)
  min-mem h = wk-cong wk-wk-ε , refl
  min-mem (t i) =
    let
      IH = min-mem i
    in
    wk-wk (proj₁ IH) , cong t (proj₂ IH)

  ≍ᵐ-trans : {Γ₁ Γ₂ Γ₃ : Ctx} {X : Ty} → (i₁ : Γ₁ ∋ X) → (i₂ : Γ₂ ∋ X) → (i₃ : Γ₃ ∋ X) → i₁ ≍ᵐ i₂ → i₂ ≍ᵐ i₃ → i₁ ≍ᵐ i₃
  ≍ᵐ-trans {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ₃ = Γ₃} {X = X} i₁ i₂ i₃ i₁≍i₂ i₂≍i₃ =
    let
      mm₁ = min-mem i₁
      mm₃ = min-mem i₃
    in
    record { ctx = ε ∙ X ; wkn₁ = proj₁ mm₁ ; wkn₂ = proj₁ mm₃ ; base = h ; eq₁ = proj₂ mm₁ ; eq₂ = proj₂ mm₃ }

  ≍ᵛ-var-cong : {Γ₁ Γ₂ : Ctx} {X : Ty} (i₁ : Γ₁ ∋ X) (i₂ : Γ₂ ∋ X) → (i₁ ≍ᵐ i₂) → ((var i₁) ≍ᵛ (var i₂))
  ≍ᵛ-var-cong {Γ₁ = Γ₁} {Γ₂ = Γ₂} i₁ i₂ record { ctx = Γ ; wkn₁ = π₁ ; wkn₂ = π₂ ; base = base ; eq₁ = eq₁ ; eq₂ = eq₂ } =
    record { ctx = Γ ; wkn₁ = π₁ ; wkn₂ = π₂ ; base = var base ; eq₁ = cong var eq₁ ; eq₂ = cong var eq₂ }

  ------------------------------------------------------
  -- Confluence of strengthenings
  ------------------------------------------------------

  {-
  --To do this proof, we need a sufficiently strong induction hypothesis that asserts the equality of term weakenings where the _unused_ variables are permuted.
  mutual
    val-str-conf :   {X : Ty} {Γ₁ Γ₂ Δ : Ctx}
                  → (M₁ : Val Γ₁ X) → (M₂ : Val Γ₂ X) → (π₁ : Wk Δ Γ₁) → (π₂ : Wk Δ Γ₂) → (wk-val π₁ M₁ ≡ wk-val π₂ M₂)
                  → Σ[ Ψ ∈ Ctx ] Σ[ M ∈ Val Ψ X ] Σ[ π₁' ∈ Wk Γ₁ Ψ ] Σ[ π₂' ∈ Wk Γ₂ Ψ ] (((wk-val π₁' M) ≡ M₁) × ((wk-val π₂' M) ≡ M₂))
    val-str-conf {Γ₁ = Γ₁} {Γ₂ = Γ₂} (var i) (var i₁) π₁ π₂ eq = {!!}
    val-str-conf {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Δ = Δ} (lam {A = A} W₁) (lam {A = A} W₂) π₁ π₂ eq with comp-str-conf {Δ = Δ ∙ A} W₁ W₂ (wk-cong π₁) (wk-cong π₂) {!!}
    ... | Ψ , W , wk-cong π₁' , wk-cong π₂' , eq₁ , eq₂ = _ , lam W , π₁' , π₂' , cong lam eq₁ , cong lam eq₂
    ... | Ψ ∙ A , W , wk-cong π₁' , wk-wk π₂' , eq₁ , eq₂ = _ , lam W , π₁' , wk-trans π₂' (wk-wk wk-id) , cong lam eq₁ ,
      let
        a0 : lam (wk-comp (wk-cong π₁) (wk-comp (wk-cong π₁') W)) ≡ lam (wk-comp (wk-cong π₂) (wk-comp (wk-wk π₂') W))
        a0 = subst₂ (λ x y → lam (wk-comp (wk-cong π₁) x) ≡ lam (wk-comp (wk-cong π₂) y)) (sym eq₁) (sym eq₂) eq
        a1 : wk-comp (wk-cong π₁) (wk-comp (wk-cong π₁') W) ≡ wk-comp (wk-cong π₂) (wk-comp (wk-wk π₂') W)
        a1 = lam-injective a0
        a2 : wk-comp (wk-trans (wk-cong π₁) (wk-cong π₁')) W ≡ wk-comp (wk-trans (wk-cong π₂) (wk-wk π₂')) W
        a2 = {!-u!}
      in
      cong lam
          ( wk-comp (wk-cong (wk-trans π₂' (wk-wk wk-id))) W
           ≡⟨ refl ⟩
            wk-comp (wk-trans (wk-cong π₂') (wk-cong (wk-wk wk-id))) W
           ≡⟨ sym (wk-comp-trans W (wk-cong π₂') (wk-cong (wk-wk wk-id))) ⟩
            wk-comp (wk-cong π₂') (wk-comp (wk-cong (wk-wk (wk-id {Γ = Ψ}))) W)
           ≡⟨ cong (wk-comp (wk-cong π₂')) {!!} ⟩
             wk-comp (wk-cong π₂') (wk-comp (wk-wk (wk-cong (wk-id {Γ = Ψ}))) W)
           ≡⟨ wk-comp-trans W (wk-cong π₂') (wk-wk (wk-cong wk-id)) ⟩
             wk-comp (wk-trans (wk-cong π₂') (wk-wk (wk-cong wk-id))) W
           ≡⟨ refl ⟩
             wk-comp (wk-wk (wk-trans π₂' wk-id)) W
           ≡⟨ cong (λ x → wk-comp x W) wk-trans-id' ⟩
            wk-comp (wk-wk π₂') W
           ≡⟨ eq₂ ⟩
            W₂ ∎)
    ... | Ψ , W , wk-wk π₁' , wk-cong π₂' , eq₁ , eq₂ = _ , lam W , {!!} , π₂' , {!!} , cong lam eq₂
    ... | Ψ , W , wk-wk π₁' , wk-wk π₂' , eq₁ , eq₂ =
      _ , lam (wk-comp (wk-wk wk-id) W) , π₁' , π₂' ,
      cong lam
          (wk-comp (wk-cong π₁') (wk-comp (wk-wk wk-id) W)
        ≡⟨ wk-comp-trans W (wk-cong π₁') (wk-wk wk-id) ⟩
          wk-comp (wk-trans (wk-cong π₁') (wk-wk wk-id)) W
        ≡⟨ refl ⟩
          wk-comp (wk-wk (wk-trans π₁' wk-id)) W
        ≡⟨ cong (λ x → wk-comp x W) wk-trans-id' ⟩
          wk-comp (wk-wk π₁') W
        ≡⟨ eq₁ ⟩ W₁ ∎) ,
      cong lam
        (wk-comp (wk-cong π₂') (wk-comp (wk-wk wk-id) W)
      ≡⟨ wk-comp-trans W (wk-cong π₂') (wk-wk wk-id) ⟩
        wk-comp (wk-trans (wk-cong π₂') (wk-wk wk-id)) W
      ≡⟨ refl ⟩
        wk-comp (wk-wk (wk-trans π₂' wk-id)) W
      ≡⟨ cong (λ x → wk-comp x W) wk-trans-id' ⟩
        wk-comp (wk-wk π₂') W
      ≡⟨ eq₂ ⟩ W₂ ∎)

    val-str-conf {Γ₁ = Γ₁} {Γ₂ = Γ₂} (pair M₁ M₂) (pair M₃ M₄) π₁ π₂ eq = {!!}
    val-str-conf {Γ₁ = Γ₁} {Γ₂ = Γ₂} (pm M₁ M₂) (pm M₃ M₄) π₁ π₂ eq = {!!}
    val-str-conf {Γ₁ = Γ₁} {Γ₂ = Γ₂} unit unit π₁ π₂ eq = {!!}

    comp-str-conf :   {X : Ty} {Γ₁ Γ₂ Δ : Ctx}
                  → (W₁ : Comp Γ₁ X) → (W₂ : Comp Γ₂ X) → (π₁ : Wk Δ Γ₁) → (π₂ : Wk Δ Γ₂) → (wk-comp π₁ W₁ ≡ wk-comp π₂ W₂)
                  → Σ[ Ψ ∈ Ctx ] Σ[ W ∈ Comp Ψ X ] Σ[ π₁' ∈ Wk Γ₁ Ψ ] Σ[ π₂' ∈ Wk Γ₂ Ψ ] (((wk-comp π₁' W) ≡ W₁) × ((wk-comp π₂' W) ≡ W₂))
    comp-str-conf = {!!}
  -}

  ------------------------------------------------------

  {-
  -- For this we already seem to need confluence
  ≍ᵛ-lam-cong : {Γ₁ Γ₂ : Ctx} {X Y : Ty} (W₁ : (Γ₁ ∙ X) ⊢ᶜ Y) (W₂ : (Γ₂ ∙ X) ⊢ᶜ Y) →
                ((W₁ ≍ᶜ W₂)) → ((lam W₁) ≍ᵛ (lam W₂))
  ≍ᵛ-lam-cong {Γ₁ = Γ₁} {Γ₂ = Γ₂} {X = X} W₁ W₂ record { ctx = ε ; wkn₁ = π₁ ; wkn₂ = π₂ ; base = base ; eq₁ = eq₁ ; eq₂ = eq₂ } =
    let
      a0 : W₁ ≡ wk-comp (wk-cong wk-wk-ε) (wk-comp (wk-wk wk-ε) base)
      a0 =   W₁
           ≡⟨ eq₁ ⟩
             wk-comp π₁ base
           ≡⟨ cong (λ x → wk-comp x base) (wk-wk-uniq π₁) ⟩
             wk-comp wk-wk-ε base
           ≡⟨ cong (λ x → wk-comp x base) (sym (wk-wk-uniq (wk-trans (wk-cong wk-wk-ε) (wk-wk wk-ε)))) ⟩
             wk-comp (wk-trans (wk-cong wk-wk-ε) (wk-wk wk-ε)) base
           ≡⟨ sym (wk-comp-trans base (wk-cong wk-wk-ε) (wk-wk wk-ε)) ⟩
             wk-comp (wk-cong wk-wk-ε) (wk-comp (wk-wk wk-ε) base) ∎
      a1 : W₂ ≡ wk-comp (wk-cong wk-wk-ε) (wk-comp (wk-wk wk-ε) base)
      a1 =   W₂
           ≡⟨ eq₂ ⟩
             wk-comp π₂ base
           ≡⟨ cong (λ x → wk-comp x base) (wk-wk-uniq π₂) ⟩
             wk-comp wk-wk-ε base
           ≡⟨ cong (λ x → wk-comp x base) (sym (wk-wk-uniq (wk-trans (wk-cong wk-wk-ε) (wk-wk wk-ε)))) ⟩
             wk-comp (wk-trans (wk-cong wk-wk-ε) (wk-wk wk-ε)) base
           ≡⟨ sym (wk-comp-trans base (wk-cong wk-wk-ε) (wk-wk wk-ε)) ⟩
             wk-comp (wk-cong wk-wk-ε) (wk-comp (wk-wk wk-ε) base) ∎
    in
    record { ctx = ε ; wkn₁ = wk-wk-ε ; wkn₂ = wk-wk-ε ; base = lam (wk-comp wk-wk-ε base) ; eq₁ = cong lam a0 ; eq₂ = cong lam a1 }
  ≍ᵛ-lam-cong {Γ₁ = Γ₁} {Γ₂ = Γ₂} {X = X} W₁ W₂ record { ctx = (Γ ∙ X) ; wkn₁ = (wk-cong π₁) ; wkn₂ = (wk-cong π₂) ; base = base ; eq₁ = eq₁ ; eq₂ = eq₂ } =
    record { ctx = Γ ; wkn₁ = π₁ ; wkn₂ = π₂ ; base = lam base ; eq₁ = cong lam eq₁ ; eq₂ = cong lam eq₂ }
  ≍ᵛ-lam-cong {Γ₁ = Γ₁} {Γ₂ = Γ₂ ∙ Z} {X = X} W₁ W₂ record { ctx = (Γ ∙ X) ; wkn₁ = (wk-cong π₁) ; wkn₂ = (wk-wk π₂) ; base = base ; eq₁ = eq₁ ; eq₂ = eq₂ } =
    let
      π' : Wk (Γ₂ ∙ Z) Γ
      π' = {!!}
      a0 : W₂ ≡ wk-comp (wk-cong (wk-trans π₂ (wk-wk wk-id))) base
      a0 =   W₂
           ≡⟨ eq₂ ⟩
             wk-comp (wk-wk π₂) base
           ≡⟨ {!!} ⟩
             wk-comp (wk-cong (wk-trans π₂ (wk-wk wk-id))) base ∎
    in
    record { ctx = Γ ; wkn₁ = π₁ ; wkn₂ = wk-trans π₂ (wk-wk wk-id) ; base = lam {!!} ; eq₁ = cong lam {!!} ; eq₂ = cong lam {!!} }
  ≍ᵛ-lam-cong {Γ₁ = Γ₁} {Γ₂ = Γ₂} {X = X} W₁ W₂ record { ctx = (Γ ∙ X) ; wkn₁ = (wk-wk π₁) ; wkn₂ = (wk-cong π₂) ; base = base ; eq₁ = eq₁ ; eq₂ = eq₂ } =
    record { ctx = Γ ; wkn₁ = wk-trans π₁ (wk-wk wk-id) ; wkn₂ = π₂ ; base = lam base ; eq₁ = cong lam {!!} ; eq₂ = cong lam {!!} }
  ≍ᵛ-lam-cong {Γ₁ = Γ₁} {Γ₂ = Γ₂} {X = X} W₁ W₂ record { ctx = (Γ ∙ Y) ; wkn₁ = (wk-wk π₁) ; wkn₂ = (wk-wk π₂) ; base = base ; eq₁ = eq₁ ; eq₂ = eq₂ } =
    record { ctx = Γ ∙ Y ; wkn₁ = π₁ ; wkn₂ = π₂ ; base = lam (wk-comp (wk-wk wk-id) base) ; eq₁ = cong lam {!!} ; eq₂ = cong lam {!!} }
  -}

  ≍ᵛ-refl : {Γ : Ctx} {X : Ty} (M : Val Γ X) → M ≍ᵛ M
  ≍ᵛ-refl {Γ = Γ} {X = X} M = record { ctx = Γ ; wkn₁ = wk-id ; wkn₂ = wk-id ; base = M ; eq₁ = sym (wk-val-id M) ; eq₂ = sym (wk-val-id M) }

  ≍ᵉᵛ-refl : {Γ : Ctx} {X : Ty} (M : V̲a̲l̲ Γ X) → M ≍ᵉᵛ M
  ≍ᵉᵛ-refl {Γ = Γ} {X = X} M = record { ctx = Γ ; wkn₁ = wk-id ; wkn₂ = wk-id ; base = M ; eq₁ = sym (wk-v̲a̲l̲-id M) ; eq₂ = sym (wk-v̲a̲l̲-id M) }

  ≍ᶜ-refl : {Γ : Ctx} {X : Ty} (W : Comp Γ X) → W ≍ᶜ W
  ≍ᶜ-refl {Γ = Γ} {X = X} W = record { ctx = Γ ; wkn₁ = wk-id ; wkn₂ = wk-id ; base = W ; eq₁ = sym (wk-comp-id W) ; eq₂ = sym (wk-comp-id W) }

  ≍ᶜᵉᵛ-refl : {Γ : Ctx} {X : Ty} (W : C̲o̲m̲p Γ X) → W ≍ᶜᵉᵛ W
  ≍ᶜᵉᵛ-refl {Γ = Γ} {X = X} W = record { ctx = Γ ; wkn₁ = wk-id ; wkn₂ = wk-id ; base = W ; eq₁ = sym (wk-c̲o̲m̲p-id W) ; eq₂ = sym (wk-c̲o̲m̲p-id W) }

  postulate ≍ᵛ-trans : {Γ₁ Γ₂ Γ₃ : Ctx} {X : Ty} {M₁ : Val Γ₁ X} {M₂ : Val Γ₂ X} {M₃ : Val Γ₃ X} → M₁ ≍ᵛ M₂ → M₂ ≍ᵛ M₃ → M₁ ≍ᵛ M₃

  postulate ≍ᶜ-trans : {Γ₁ Γ₂ Γ₃ : Ctx} {X : Ty} {W₁ : Comp Γ₁ X} {W₂ : Comp Γ₂ X} {W₃ : Comp Γ₃ X} → W₁ ≍ᶜ W₂ → W₂ ≍ᶜ W₃ → W₁ ≍ᶜ W₃

  -- This would only relate identical environments to themselves I think, but it might be just what we need anyway
  data _≍ᴱ_ : Env Γ → Env Γ' → Set

  data _≍ᶜˢ_ : {Δ₁ Δ₂ : Ctx} → CompStack Δ₁ X → CompStack Δ₂ X → Set where
    emp : ◻ ≍ᶜˢ ◻
    cons :   {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {W₁ : Comp (Γ₁ ∙ Z) X} {W₂ : Comp (Γ₂ ∙ Z) X} {γ₁ : Env Γ₁} {γ₂ : Env Γ₂} {tail₁ : CompStack Δ₁ X} {tail₂ : CompStack Δ₂ X}
            {π₁ : Wk Γ₁ Δ₁} {π₂ : Wk Γ₂ Δ₂} .{wk≡₁ : ⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡ ⟦ topCsEnv tail₁ ⟧ᴱ} .{wk≡₂ : ⟦ π₂ ⟧ʷ ⟦ γ₂ ⟧ᴱ ≡ ⟦ topCsEnv tail₂ ⟧ᴱ}
          → (W₁ ≍ᶜ W₂) → (γ₁ ≍ᴱ γ₂) → (tail₁ ≍ᶜˢ tail₂) → (((W₁ ⊲ γ₁ ⦂⦂ tail₁) {π = π₁} {wk≡ = wk≡₁}) ≍ᶜˢ ((W₂ ⊲ γ₂ ⦂⦂ tail₂) {π = π₂} {wk≡ = wk≡₂}))

  data _≍ᴱ_ where
    emp  : ∗ ≍ᴱ ∗
    consᵛ :    {Γ₁ Γ₂ : Ctx} {M₁ : V̲a̲l̲ Γ₁ X} {M₂ : V̲a̲l̲ Γ₂ X} {γ₁ : Env Γ₁} {γ₂ : Env Γ₂}
           → (γ₁ ≍ᴱ γ₂) → (M₁ ≍ᵉᵛ M₂)
           → ((γ₁ ﹐ M₁) ≍ᴱ (γ₂ ﹐ M₂))
    consᶜ :    {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {W₁ : Comp Γ₁ X} {W₂ : Comp Γ₂ X} {γ₁ : Env Γ₁} {γ₂ : Env Γ₂} {cs₁ : CompStack Δ₁ X} {cs₂ : CompStack Δ₂ X}
              {π₁ : Wk Γ₁ Δ₁} {π₂ : Wk Γ₂ Δ₂} .{wk≡₁ : ⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡ ⟦ topCsEnv cs₁ ⟧ᴱ} .{wk≡₂ : ⟦ π₂ ⟧ʷ ⟦ γ₂ ⟧ᴱ ≡ ⟦ topCsEnv cs₂ ⟧ᴱ}
           → (W₁ ≍ᶜ W₂) → (γ₁ ≍ᴱ γ₂) → (cs₁ ≍ᶜˢ cs₂)
           → (((γ₁ ﹐﹝ W₁ ╎ cs₁ ﹞) {π = π₁} {wk≡ = wk≡₁}) ≍ᴱ ((γ₂ ﹐﹝ W₂ ╎ cs₂ ﹞) {π = π₂} {wk≡ = wk≡₂}))

  mutual
    ≍ᶜˢ-refl : {Δ : Ctx} {X : Ty} → (cs : CompStack Δ X) → cs ≍ᶜˢ cs
    ≍ᶜˢ-refl ◻ = emp
    ≍ᶜˢ-refl (x ⊲ γ ⦂⦂ cs) = cons (≍ᶜ-refl x) (≍ᴱ-refl γ) (≍ᶜˢ-refl cs)

    ≍ᴱ-refl : {Γ : Ctx} → (γ : Env Γ) → γ ≍ᴱ γ
    ≍ᴱ-refl ∗ = emp
    ≍ᴱ-refl (γ ﹐ M) = consᵛ (≍ᴱ-refl γ) (≍ᵉᵛ-refl M)
    ≍ᴱ-refl (γ ﹐﹝ W ╎ cs ﹞) = consᶜ (≍ᶜ-refl W) (≍ᴱ-refl γ) (≍ᶜˢ-refl cs)


  data _≍ᵛˢ_ : {b₁ b₂ : IsEmpty} → ValStack b₁ X → ValStack b₂ X → Set where
    emp  : (□ {T◾ = X}) ≍ᵛˢ □
    cons :   {Γ₁ Γ₂ : Ctx} {b₁ b₂ : IsEmpty} {pt₁ : PartialTerm Γ₁ X} {pt₂ : PartialTerm Γ₂ X} {γ₁ : Env Γ₁} {γ₂ : Env Γ₂} {tail₁ : ValStack b₁ T◾} {tail₂ : ValStack b₂ T◾}
             {↥₁ : BottomTypeEqualsNextType b₁ X T◾} {↥₂ : BottomTypeEqualsNextType b₂ X T◾}
           → (pt₁ ≍ᵖ pt₂) → (γ₁ ≍ᴱ γ₂) → (tail₁ ≍ᵛˢ tail₂)
           → (((pt₁ ⊲ γ₁ ∷ tail₁) {↥ = ↥₁}) ≍ᵛˢ ((pt₂ ⊲ γ₂ ∷ tail₂) {↥ = ↥₂}))

  data _≣ᴸꟴ_ : {X : Ty} → LookupState X → LookupState X → Set where
    ls-eqv : {Γ₁ Γ₂ : Ctx} {i₁ : Γ₁ ∋ X} {i₂ : Γ₂ ∋ X} {γ₁ : Env Γ₁} {γ₂ : Env Γ₂}
           → (i₁ ≍ᵐ i₂) → (γ₁ ≍ᴱ γ₂)
           → ((⟨ i₁ ∥ γ₁ ⟩) ≣ᴸꟴ (⟨ i₂ ∥ γ₂ ⟩))

  ≣ᴸꟴ-refl : {X : Ty} → (L : LookupState X) → L ≣ᴸꟴ L
  ≣ᴸꟴ-refl ⟨ i ∥ γ ⟩ = ls-eqv (≍ᵐ-refl i) (≍ᴱ-refl γ)

  record _≍ᴸꟴ_ {X : Ty} (L₁ : LookupState X) (L₂ : LookupState X) : Set where
    field
      T₁    : LookupState X
      T₂    : LookupState X
      path₁ : L₁ →ᴸ* T₁
      path₂ : L₂ →ᴸ* T₂
      halt₁ : LookupHaltingState T₁
      halt₂ : LookupHaltingState T₂
      eqv   : (T₁ ≣ᴸꟴ T₂)

  record _≍ᴸ_ {X : Ty} (L₁ : LookupState X) (L₂ : LookupState X) : Set where
    field
      T     : LookupState X
      halt  : LookupHaltingState T
      path₁ : L₁ →ᴸ* T
      path₂ : L₂ →ᴸ* T


  record ⟨_,_⟩≍ᵐᴱ⟨_,_⟩ {Γ₁ Γ₂ : Ctx} {X : Ty} (i₁ : Γ₁ ∋ X) (γ₁ : Env Γ₁) (i₂ : Γ₂ ∋ X) (γ₂ : Env Γ₂) : Set where
    field
      ctx  : Ctx
      env  : Env ctx
      wkn₁ : Wk Γ₁ ctx
      wkn₂ : Wk Γ₂ ctx
      base : ctx ∋ X
      eq₁  : i₁ ≡ wk-mem wkn₁ base
      eq₂  : i₂ ≡ wk-mem wkn₂ base
      enveq₁ : EnvEq wkn₁ γ₁ env
      enveq₂ : EnvEq wkn₂ γ₂ env

  {- This is not true in general. We might not have a minimal environment.
  peq-trans :   {Γ₁ Γ₂ Γ₃ : Ctx} {X : Ty} {i₁ : Γ₁ ∋ X} {γ₁ : Env Γ₁} {i₂ : Γ₂ ∋ X} {γ₂ : Env Γ₂} {i₃ : Γ₃ ∋ X} {γ₃ : Env Γ₃}
              → ⟨ i₁ , γ₁ ⟩≍ᵐᴱ⟨ i₂ , γ₂ ⟩ → ⟨ i₂ , γ₂ ⟩≍ᵐᴱ⟨ i₃ , γ₃ ⟩
              → ⟨ i₁ , γ₁ ⟩≍ᵐᴱ⟨ i₃ , γ₃ ⟩
  peq-trans {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ₃ = Γ₃} {X = X} {i₁ = i₁} {γ₁ = γ₁} {i₂ = i₂} {γ₂ = γ₂} {i₃ = i₃} {γ₃ = γ₃}
    record { ctx = Γₗ ; env = γₗ ; wkn₁ = π₁ ; wkn₂ = π₂ ; base = iₗ ; eq₁ = eq₁ ; eq₂ = eq₂ ; enveq₁ = ϖ₁ ; enveq₂ = ϖ₂ }
    record { ctx = Γᵣ ; env = γᵣ ; wkn₁ = π₃ ; wkn₂ = π₄ ; base = iᵣ ; eq₁ = eq₃ ; eq₂ = eq₄ ; enveq₁ = enveq₃ ; enveq₂ = enveq₄ } =
    let
      mm₁ = min-mem i₁
      mm₂ = min-mem i₃
    in
    record
     { ctx = ε ∙ X
     ; env = {!!}
     ; wkn₁ = proj₁ mm₁
     ; wkn₂ = proj₁ mm₂
     ; base = h
     ; eq₁ = proj₂ mm₁
     ; eq₂ = proj₂ mm₂
     ; enveq₁ = {!!}
     ; enveq₂ = {!!}
     }
  -}

  data _≍ᵛꟴ_ : {X : Ty} → ValState X → ValState X → Set where
    ∘eqv : {vs₁ : ValStack non-empty T◾} {vs₂ : ValStack non-empty T◾}
           → (vs₁ ≍ᵛˢ vs₂)
           → ((∘ vs₁) ≍ᵛꟴ (∘ vs₂))

    ∙eqv : {vs₁ : ValStack non-empty T◾} {vs₂ : ValStack non-empty T◾}
            → (vs₁ ≍ᵛˢ vs₂)
            → ((∙ vs₁) ≍ᵛꟴ (∙ vs₂))

  data _≍ᶜꟴ_ : CompState → CompState → Set where
    ∘eqv : {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {X' : Ty} {W₁ : Γ₁ ⊢ᶜ X'} {W₂ : Γ₂ ⊢ᶜ X'} {γ₁ : Env Γ₁} {γ₂ : Env Γ₂} {cs₁ : CompStack Δ₁ X'} {cs₂ : CompStack Δ₂ X'}
                {π₁ : Wk Γ₁ Δ₁} {π₂ : Wk Γ₂ Δ₂} .{wk≡₁ : ⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡ ⟦ topCsEnv cs₁ ⟧ᴱ} .{wk≡₂ : ⟦ π₂ ⟧ʷ ⟦ γ₂ ⟧ᴱ ≡ ⟦ topCsEnv cs₂ ⟧ᴱ}
              → (W₁ ≍ᶜ W₂) → (γ₁ ≍ᴱ γ₂) → (cs₁ ≍ᶜˢ cs₂)
              → (((∘⟨ W₁ ⊰ γ₁ ╎ cs₁ ⟩) {π = π₁} {wk≡ = wk≡₁}) ≍ᶜꟴ ((∘⟨ W₂ ⊰ γ₂ ╎ cs₂ ⟩) {π = π₂} {wk≡ = wk≡₂}))

    ∙eqv : {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {X' : Ty} {W₁ : C̲o̲m̲p Γ₁ X'} {W₂ : C̲o̲m̲p Γ₂ X'} {γ₁ : Env Γ₁} {γ₂ : Env Γ₂} {cs₁ : CompStack Δ₁ X'} {cs₂ : CompStack Δ₂ X'}
                 {π₁ : Wk Γ₁ Δ₁} {π₂ : Wk Γ₂ Δ₂} .{wk≡₁ : ⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡ ⟦ topCsEnv cs₁ ⟧ᴱ} .{wk≡₂ : ⟦ π₂ ⟧ʷ ⟦ γ₂ ⟧ᴱ ≡ ⟦ topCsEnv cs₂ ⟧ᴱ}
               → (W₁ ≍ᶜᵉᵛ W₂) → (γ₁ ≍ᴱ γ₂) → (cs₁ ≍ᶜˢ cs₂)
               → (((∙⟨ W₁ ⊰ γ₁ ╎ cs₁ ⟩) {π = π₁} {wk≡ = wk≡₁}) ≍ᶜꟴ ((∙⟨ W₂ ⊰ γ₂ ╎ cs₂ ⟩) {π = π₂} {wk≡ = wk≡₂}))

  -}
