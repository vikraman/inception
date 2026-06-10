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

  record _≍ᴱ_ {Γ₁ Γ₂ : Ctx} (γ₁ : Env Γ₁) (γ₂ : Env Γ₂) : Set where
    field
      ctx    : Ctx
      wkn₁   : Wk Γ₁ ctx
      wkn₂   : Wk Γ₂ ctx
      base   : Env ctx
      enveq₁ : EnvEq wkn₁ γ₁ base
      enveq₂ : EnvEq wkn₂ γ₂ base

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

  {-
  mutual
    wk-val-helper : {Γ Δ : Ctx} → (M : Val (Δ ∙ X) Z) → (M' : Val (Γ ∙ X) Z) → (π : Wk Δ (Γ ∙ X)) → M ≡ wk-val (wk-wk π) M' → Σ[ π' ∈ Wk Δ Γ ] (wk-val (wk-wk π) M' ≡ wk-val (wk-cong π') M')
    wk-val-helper (var i₁) (var i₂) π eq = (wk-trans π (wk-wk wk-id)) , {!!}
    wk-val-helper (lam W₁) (lam W₂) π eq =
      let
        a0 = wk-comp-helper W₁ W₂ {!!} {!!}
      in
      {!!} , {!!}
    wk-val-helper (pair M M₁) (pair M' M'') π eq = {!!}
    wk-val-helper (pm M M₁) (pm M' M'') π eq = {!!}
    wk-val-helper unit unit π eq = {!!}

    wk-comp-helper : {Γ Δ : Ctx} → (W : Comp (Δ ∙ X) Z) → (W' : Comp (Γ ∙ X) Z) → (π : Wk Δ (Γ ∙ X)) → W ≡ wk-comp (wk-wk π) W' → Σ[ π' ∈ Wk Δ Γ ] (wk-comp (wk-wk π) W' ≡ wk-comp (wk-cong π') W')
    wk-comp-helper W W' π eq = {!!} , {!!}
  -}

  {-
  mutual
    wk-val-prev-eq : {Γ Δ : Ctx} {X Y Z : Ty} → (M : Val (Γ ∙ Y) X) → (π : Wk (Δ ∙ Z) (Γ ∙ Y)) → wk-val (wk-wk π) M ≡ wk-val (wk-cong (wk-wk (wk-prev π))) M
    wk-val-prev-eq (var i) π = {!!}
    wk-val-prev-eq (lam W) π =
      let
        a0 = wk-comp-prev-eq W (wk-cong π)
      in
      {!!}
    wk-val-prev-eq (pair M₁ M₂) π = {!!}
    wk-val-prev-eq (pm M N) π = {!!}
    wk-val-prev-eq unit π = {!!}

    wk-comp-prev-eq : {Γ Δ : Ctx} {X Y Z : Ty} → (W : Comp (Γ ∙ Y) X) → (π : Wk (Δ ∙ Z) (Γ ∙ Y)) → wk-comp (wk-wk π) W ≡ wk-comp (wk-cong (wk-wk (wk-prev π))) W
    wk-comp-prev-eq (return M) π = {!!}
    wk-comp-prev-eq (pm M W) π = {!!}
    wk-comp-prev-eq (push W₁ W₂) π = {!!}
    wk-comp-prev-eq (app M N) π = {!!}
    wk-comp-prev-eq (var M) π = {!!}
    wk-comp-prev-eq (sub W₁ W₂) π = {!!}
  -}

  ------------------------------------------------------
  -- Confluence of strengthenings
  ------------------------------------------------------

  mutual
    val-str-conf :   {X : Ty} {Γ₁ Γ₂ : Ctx}
                  → (M₁ : Val Γ₁ X) → (M₂ : Val Γ₂ X) → (π₁ : Wk Δ Γ₁) → (π₂ : Wk Δ Γ₂) → (wk-val π₁ M₁ ≡ wk-val π₂ M₂)
                  → Σ[ Ψ ∈ Ctx ] Σ[ M ∈ Val Ψ X ] Σ[ π₁' ∈ Wk Γ₁ Ψ ] Σ[ π₂' ∈ Wk Γ₂ Ψ ] (((wk-val π₁' M) ≡ M₁) × ((wk-val π₂' M) ≡ M₂))
    val-str-conf {Γ₁ = Γ₁} {Γ₂ = Γ₂} (var i) (var i₁) π₁ π₂ eq = {!!}
    val-str-conf {Γ₁ = Γ₁} {Γ₂ = Γ₂} (lam W₁) (lam W₂) π₁ π₂ eq with comp-str-conf W₁ W₂ (wk-cong π₁) (wk-cong π₂) {!!}
    ... | Ψ , W , wk-cong π₁' , wk-cong π₂' , eq₁ , eq₂ = _ , lam W , π₁' , π₂' , cong lam eq₁ , cong lam eq₂
    ... | Ψ , W , wk-cong π₁' , wk-wk π₂' , eq₁ , eq₂ = _ , lam W , π₁' , wk-trans π₂' (wk-wk wk-id) , cong lam eq₁ ,
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
            wk-comp (wk-cong π₂') (wk-comp (wk-cong (wk-wk wk-id)) W)
           ≡⟨ cong (wk-comp (wk-cong π₂')) {!!} ⟩ -- <--- WORKING HERE
             wk-comp (wk-cong π₂') (wk-comp (wk-wk (wk-cong wk-id)) W)
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

    comp-str-conf :   {X : Ty} {Γ₁ Γ₂ : Ctx}
                  → (W₁ : Comp Γ₁ X) → (W₂ : Comp Γ₂ X) → (π₁ : Wk Δ Γ₁) → (π₂ : Wk Δ Γ₂) → (wk-comp π₁ W₁ ≡ wk-comp π₂ W₂)
                  → Σ[ Ψ ∈ Ctx ] Σ[ W ∈ Comp Ψ X ] Σ[ π₁' ∈ Wk Γ₁ Ψ ] Σ[ π₂' ∈ Wk Γ₂ Ψ ] (((wk-comp π₁' W) ≡ W₁) × ((wk-comp π₂' W) ≡ W₂))
    comp-str-conf = {!!}

  ------------------------------------------------------

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


  ≍ᵛ-refl : {Γ : Ctx} {X : Ty} (M : Val Γ X) → M ≍ᵛ M
  ≍ᵛ-refl {Γ = Γ} {X = X} (var i) = {!!}
  ≍ᵛ-refl {Γ = Γ} {X = X} (lam W) = {!!}
  ≍ᵛ-refl {Γ = Γ} {X = X} (pair M₁ M₂) = {!!}
  ≍ᵛ-refl {Γ = Γ} {X = X} (pm M N) = {!!}
  ≍ᵛ-refl {Γ = Γ} {X = X} unit = {!!}


  --≍ᵛ-trans {Γ₁ Γ₂ : Ctx} {X : Ty} (M₁ : Val Γ₁ X) (M₂ : Val Γ₂ X) : Set where


  ≍ᴱ-refl : {Γ : Ctx} → (γ : Env Γ) → γ ≍ᴱ γ
  ≍ᴱ-refl ∗ = record { ctx = ε ; wkn₁ = wk-ε ; wkn₂ = wk-ε ; base = Env.∗ ; enveq₁ = EnvEq.wk-env-ε ; enveq₂ = EnvEq.wk-env-ε}
  ≍ᴱ-refl (γ ﹐ M) = record { ctx = _≍ᴱ_.ctx (≍ᴱ-refl γ) ; wkn₁ = wk-wk (_≍ᴱ_.wkn₁ (≍ᴱ-refl γ)) ; wkn₂ = wk-wk (_≍ᴱ_.wkn₂ (≍ᴱ-refl γ)) ; base = _≍ᴱ_.base (≍ᴱ-refl γ) ; enveq₁ = EnvEq.wk-env-val-wk M (_≍ᴱ_.enveq₁ (≍ᴱ-refl γ)) ; enveq₂ = EnvEq.wk-env-val-wk M (_≍ᴱ_.enveq₂ (≍ᴱ-refl γ))}
  ≍ᴱ-refl (γ ﹐﹝ W ╎ cs ﹞) = record { ctx = _≍ᴱ_.ctx (≍ᴱ-refl γ) ; wkn₁ = wk-wk (_≍ᴱ_.wkn₁ (≍ᴱ-refl γ)) ; wkn₂ = wk-wk (_≍ᴱ_.wkn₂ (≍ᴱ-refl γ)) ; base = _≍ᴱ_.base (≍ᴱ-refl γ) ; enveq₁ = EnvEq.wk-env-comp-wk W cs (_≍ᴱ_.enveq₁ (≍ᴱ-refl γ)) ; enveq₂ = EnvEq.wk-env-comp-wk W cs (_≍ᴱ_.enveq₂ (≍ᴱ-refl γ))}

  --data _≣ᴱ_ : Env Γ → Env Γ' → Set

  data _≍ᶜˢ_ : {Δ₁ Δ₂ : Ctx} → CompStack Δ₁ X → CompStack Δ₂ X → Set where
    emp : ◻ ≍ᶜˢ ◻
    cons :   {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {W₁ : Comp (Γ₁ ∙ Z) X} {W₂ : Comp (Γ₂ ∙ Z) X} {γ₁ : Env Γ₁} {γ₂ : Env Γ₂} {tail₁ : CompStack Δ₁ X} {tail₂ : CompStack Δ₂ X}
            {π₁ : Wk Γ₁ Δ₁} {π₂ : Wk Γ₂ Δ₂} .{wk≡₁ : ⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡ ⟦ topCsEnv tail₁ ⟧ᴱ} .{wk≡₂ : ⟦ π₂ ⟧ʷ ⟦ γ₂ ⟧ᴱ ≡ ⟦ topCsEnv tail₂ ⟧ᴱ}
          → (W₁ ≍ᶜ W₂) → (γ₁ ≍ᴱ γ₂) → (tail₁ ≍ᶜˢ tail₂) → (((W₁ ⊲ γ₁ ⦂⦂ tail₁) {π = π₁} {wk≡ = wk≡₁}) ≍ᶜˢ ((W₂ ⊲ γ₂ ⦂⦂ tail₂) {π = π₂} {wk≡ = wk≡₂}))

  --data _≣ᴱ_ where
  --  emp  : ∗ ≣ᴱ ∗
  --  consᵛ :    {Γ₁ Γ₂ : Ctx} {M₁ : V̲a̲l̲ Γ₁ X} {M₂ : V̲a̲l̲ Γ₂ X} {γ₁ : Env Γ₁} {γ₂ : Env Γ₂}
  --         → (γ₁ ≣ᴱ γ₂) → (M₁ ≍ᵉᵛ M₂)
  --         → ((γ₁ ﹐ M₁) ≣ᴱ (γ₂ ﹐ M₂))
  --  consᶜ :    {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {W₁ : Comp Γ₁ X} {W₂ : Comp Γ₂ X} {γ₁ : Env Γ₁} {γ₂ : Env Γ₂} {cs₁ : CompStack Δ₁ X} {cs₂ : CompStack Δ₂ X}
  --            {π₁ : Wk Γ₁ Δ₁} {π₂ : Wk Γ₂ Δ₂} .{wk≡₁ : ⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ ≡ ⟦ topCsEnv cs₁ ⟧ᴱ} .{wk≡₂ : ⟦ π₂ ⟧ʷ ⟦ γ₂ ⟧ᴱ ≡ ⟦ topCsEnv cs₂ ⟧ᴱ}
  --         → (W₁ ≍ᶜ W₂) → (γ₁ ≣ᴱ γ₂) → (cs₁ ≍ᶜˢ cs₂)
  --         → (((γ₁ ﹐﹝ W₁ ╎ cs₁ ﹞) {π = π₁} {wk≡ = wk≡₁}) ≣ᴱ ((γ₂ ﹐﹝ W₂ ╎ cs₂ ﹞) {π = π₂} {wk≡ = wk≡₂}))

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
      -- ctx₁  : Ctx
      -- ctx₂  : Ctx
      -- env₁  : Env (ctx₁ ∙ X)
      -- env₂  : Env (ctx₂ ∙ X)
      T₁    : LookupState X
      T₂    : LookupState X
      path₁ : L₁ →ᴸ* T₁
      path₂ : L₂ →ᴸ* T₂
      halt₁ : LookupHaltingState T₁
      halt₂ : LookupHaltingState T₂
      eqv   : (T₁ ≣ᴸꟴ T₂)

      -- halt₁ : LookupHaltingState ⟨ h ∥ env₁ ⟩
      -- halt₂ : LookupHaltingState ⟨ h ∥ env₂ ⟩
      -- eqv   : (env₁ ≍ᴱ env₂)


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
