module Inception.LamLamBar.Syntax where

open import Inception.Prelude
open import Inception.Reasoning using (module Equational)

--------------------------------------------------------------------------
-- types and contexts

infix  50 _̃
infixr 40 _`×_
infixr 35 _`+_
infixr 25 _`⇒_

data Ty : Set where
  `𝟙 : Ty
  _̃ : Ty → Ty
  _`×_ _`⇒_ _`+_ : Ty → Ty → Ty

open import Inception.Ctx Ty public

--------------------------------------------------------------------------
-- values and computations

syntax Val Γ X = Γ ⊢ᵛ X

data Val : Ctx → Ty → Set

syntax Comp Γ X = Γ ⊢ᶜ X

data Comp : Ctx → Ty → Set

data Val where

  var : (i : Γ ∋ X)
      ---------
      → Γ ⊢ᵛ X

  lam : (Γ ∙ X) ⊢ᶜ Y
      -----------------
      → Γ ⊢ᵛ X `⇒ Y

  pair : Γ ⊢ᵛ X → Γ ⊢ᵛ Y
      -------------------
       → Γ ⊢ᵛ X `× Y

  unit :
       -----------
        Γ ⊢ᵛ `𝟙

  inl : Γ ⊢ᵛ X
      ---------------
      → Γ ⊢ᵛ X `+ Y

  inr : Γ ⊢ᵛ Y
      ---------------
      → Γ ⊢ᵛ X `+ Y

data Comp where

  return : Γ ⊢ᵛ X
         -----------
         → Γ ⊢ᶜ X

  pm : Γ ⊢ᵛ X `× Y → (Γ ∙ X ∙ Y) ⊢ᶜ Z
     -----------------------------------
     → Γ ⊢ᶜ Z

  push : Γ ⊢ᶜ X → (Γ ∙ X) ⊢ᶜ Y
       ---------------------------
       → Γ ⊢ᶜ Y

  case : Γ ⊢ᵛ X `+ Y → (Γ ∙ X) ⊢ᶜ Z → (Γ ∙ Y) ⊢ᶜ Z
       ------------------------------------------------
       → Γ ⊢ᶜ Z

  app : Γ ⊢ᵛ X `⇒ Y → Γ ⊢ᵛ X
      -------------------------
              → Γ ⊢ᶜ Y

  colam : (Γ ∙ X ̃) ⊢ᶜ Y
        ----------------
        → Γ ⊢ᶜ X `+ Y

  coapp : Γ ⊢ᶜ X `+ Y → Γ ⊢ᵛ X ̃
        -------------------------
        → Γ ⊢ᶜ Y

--------------------------------------------------------------------------
-- weakenings

mutual
  wk-val : Γ ⊇ Δ → Δ ⊢ᵛ X → Γ ⊢ᵛ X
  wk-val π (var i)    = var (wk-mem π i)
  wk-val π (lam M)    = lam (wk-comp (wk-cong π) M)
  wk-val π (pair V W) = pair (wk-val π V) (wk-val π W)
  wk-val π unit       = unit
  wk-val π (inl V)    = inl (wk-val π V)
  wk-val π (inr V)    = inr (wk-val π V)

  wk-comp : Γ ⊇ Δ → Δ ⊢ᶜ X → Γ ⊢ᶜ X
  wk-comp π (return V)   = return (wk-val π V)
  wk-comp π (pm V M)     = pm (wk-val π V) (wk-comp (wk-cong (wk-cong π)) M)
  wk-comp π (push M N)   = push (wk-comp π M) (wk-comp (wk-cong π) N)
  wk-comp π (case V M N) = case (wk-val π V) (wk-comp (wk-cong π) M) (wk-comp (wk-cong π) N)
  wk-comp π (app V W)    = app (wk-val π V) (wk-val π W)
  wk-comp π (colam M)    = colam (wk-comp (wk-cong π) M)
  wk-comp π (coapp M V)  = coapp (wk-comp π M) (wk-val π V)

wk : Γ ⊢ᵛ X → (Γ ∙ Y) ⊢ᵛ X
wk = wk-val (wk-wk wk-id)

--------------------------------------------------------------------------
-- substitutions

syntax Subᵛ Γ Δ = Γ ⊢ Δ

Subᵛ : Ctx → Ctx → Set
Subᵛ Γ = Sub (Val Γ)

sub-wk : Γ ⊇ Δ → Δ ⊢ Ψ → Γ ⊢ Ψ
sub-wk π = sub-map (wk-val π)

sub-id : Γ ⊢ Γ
sub-id {Γ = ε} = sub-ε
sub-id {Γ = Γ ∙ X} = sub-ex (sub-wk (wk-wk wk-id) sub-id) (var here)

mutual
  sub-val : Γ ⊢ Δ → Δ ⊢ᵛ X → Γ ⊢ᵛ X
  sub-val θ (var i)    = sub-mem θ i
  sub-val θ (lam M)    = lam (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  sub-val θ (pair V W) = pair (sub-val θ V) (sub-val θ W)
  sub-val θ unit       = unit
  sub-val θ (inl V)    = inl (sub-val θ V)
  sub-val θ (inr V)    = inr (sub-val θ V)

  sub-comp : Γ ⊢ Δ → Δ ⊢ᶜ X → Γ ⊢ᶜ X
  sub-comp θ (return V)   = return (sub-val θ V)
  sub-comp θ (pm V M)     = pm (sub-val θ V) (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M)
  sub-comp θ (push M N)   = push (sub-comp θ M) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
  sub-comp θ (case V M N) = case (sub-val θ V) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
  sub-comp θ (app V W)    = app (sub-val θ V) (sub-val θ W)
  sub-comp θ (colam M)    = colam (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  sub-comp θ (coapp M V)  = coapp (sub-comp θ M) (sub-val θ V)

--------------------------------------------------------------------------
-- weakening lemmas

mutual
  wk-val-id-β : (V : Γ ⊢ᵛ X) → wk-val wk-id V ≡ V
  wk-val-id-β (var i)    = refl
  wk-val-id-β (lam M)    = cong lam (wk-comp-id-β M)
  wk-val-id-β (pair V W) = cong₂ pair (wk-val-id-β V) (wk-val-id-β W)
  wk-val-id-β unit       = refl
  wk-val-id-β (inl V)    = cong inl (wk-val-id-β V)
  wk-val-id-β (inr V)    = cong inr (wk-val-id-β V)

  wk-comp-id-β : (M : Γ ⊢ᶜ X) → wk-comp wk-id M ≡ M
  wk-comp-id-β (return V)   = cong return (wk-val-id-β V)
  wk-comp-id-β (pm V M)     = cong₂ pm (wk-val-id-β V) (wk-comp-id-β M)
  wk-comp-id-β (push M N)   = cong₂ push (wk-comp-id-β M) (wk-comp-id-β N)
  wk-comp-id-β (case V M N) = cong₃ case (wk-val-id-β V) (wk-comp-id-β M) (wk-comp-id-β N)
  wk-comp-id-β (app V W)    = cong₂ app (wk-val-id-β V) (wk-val-id-β W)
  wk-comp-id-β (colam M)    = cong colam (wk-comp-id-β M)
  wk-comp-id-β (coapp M V)  = cong₂ coapp (wk-comp-id-β M) (wk-val-id-β V)

{-# REWRITE wk-val-id-β wk-comp-id-β #-}

wk-val-id-η : (π : Γ ⊇ Γ) (V : Γ ⊢ᵛ X) → wk-val π V ≡ V
wk-val-id-η π V = cong (λ δ → wk-val δ V) (wk-id-η π)

wk-comp-id-η : (π : Γ ⊇ Γ) (M : Γ ⊢ᶜ X) → wk-comp π M ≡ M
wk-comp-id-η π M = cong (λ δ → wk-comp δ M) (wk-id-η π)

{-# REWRITE wk-val-id-η wk-comp-id-η #-}

mutual
  wk-val-wk-η : (V : Γ ⊢ᵛ X) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → wk-val π (wk-val δ V) ≡ wk-val (wk-trans π δ) V
  wk-val-wk-η (var i) π δ    = refl
  wk-val-wk-η (lam M) π δ    = cong lam (wk-comp-wk-η M (wk-cong π) (wk-cong δ))
  wk-val-wk-η (pair V W) π δ = cong₂ pair (wk-val-wk-η V π δ) (wk-val-wk-η W π δ)
  wk-val-wk-η unit π δ       = refl
  wk-val-wk-η (inl V) π δ    = cong inl (wk-val-wk-η V π δ)
  wk-val-wk-η (inr V) π δ    = cong inr (wk-val-wk-η V π δ)

  wk-comp-wk-η : (M : Γ ⊢ᶜ X) → (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → wk-comp π (wk-comp δ M) ≡ wk-comp (wk-trans π δ) M
  wk-comp-wk-η (return V) π δ   = cong return (wk-val-wk-η V π δ)
  wk-comp-wk-η (pm V M) π δ     = cong₂ pm (wk-val-wk-η V π δ) (wk-comp-wk-η M (wk-cong (wk-cong π)) (wk-cong (wk-cong δ)))
  wk-comp-wk-η (push M N) π δ   = cong₂ push (wk-comp-wk-η M π δ) (wk-comp-wk-η N (wk-cong π) (wk-cong δ))
  wk-comp-wk-η (case V M N) π δ = cong₃ case (wk-val-wk-η V π δ) (wk-comp-wk-η M (wk-cong π) (wk-cong δ)) (wk-comp-wk-η N (wk-cong π) (wk-cong δ))
  wk-comp-wk-η (app V W) π δ    = cong₂ app (wk-val-wk-η V π δ) (wk-val-wk-η W π δ)
  wk-comp-wk-η (colam M) π δ    = cong colam (wk-comp-wk-η M (wk-cong π) (wk-cong δ))
  wk-comp-wk-η (coapp M V) π δ  = cong₂ coapp (wk-comp-wk-η M π δ) (wk-val-wk-η V π δ)

{-# REWRITE wk-val-wk-η wk-comp-wk-η #-}

--------------------------------------------------------------------------
-- weakening/substitution

mutual
  wk-val-sub-η : (π : Ψ ⊇ Γ) (θ : Γ ⊢ Δ) (V : Δ ⊢ᵛ X) → wk-val π (sub-val θ V) ≡ sub-val (sub-wk π θ) V
  wk-val-sub-η π θ (var i)    = refl
  wk-val-sub-η π θ (lam M)    = cong lam (wk-comp-sub-η (wk-cong π) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  wk-val-sub-η π θ (pair V W) = cong₂ pair (wk-val-sub-η π θ V) (wk-val-sub-η π θ W)
  wk-val-sub-η π θ unit       = refl
  wk-val-sub-η π θ (inl V)    = cong inl (wk-val-sub-η π θ V)
  wk-val-sub-η π θ (inr V)    = cong inr (wk-val-sub-η π θ V)

  wk-comp-sub-η : (π : Ψ ⊇ Γ) (θ : Γ ⊢ Δ) (M : Δ ⊢ᶜ X) → wk-comp π (sub-comp θ M) ≡ sub-comp (sub-wk π θ) M
  wk-comp-sub-η π θ (return V)   = cong return (wk-val-sub-η π θ V)
  wk-comp-sub-η π θ (pm V M)     = cong₂ pm (wk-val-sub-η π θ V) (wk-comp-sub-η (wk-cong (wk-cong π)) (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M)
  wk-comp-sub-η π θ (push M N)   = cong₂ push (wk-comp-sub-η π θ M) (wk-comp-sub-η (wk-cong π) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
  wk-comp-sub-η π θ (case V M N) = cong₃ case (wk-val-sub-η π θ V) (wk-comp-sub-η (wk-cong π) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M) (wk-comp-sub-η (wk-cong π) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N)
  wk-comp-sub-η π θ (app V W)    = cong₂ app (wk-val-sub-η π θ V) (wk-val-sub-η π θ W)
  wk-comp-sub-η π θ (colam M)    = cong colam (wk-comp-sub-η (wk-cong π) (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M)
  wk-comp-sub-η π θ (coapp M V)  = cong₂ coapp (wk-comp-sub-η π θ M) (wk-val-sub-η π θ V)

{-# REWRITE wk-val-sub-η wk-comp-sub-η #-}

--------------------------------------------------------------------------
-- substitution precomposed with weakening

sub-pre-idl-β : (π : Δ ⊇ Γ) → sub-pre (sub-id {Δ}) π ≡ sub-wk π (sub-id {Γ})
sub-pre-idl-β wk-ε        = refl
sub-pre-idl-β (wk-cong π) = cong (λ θ → sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-pre-idl-β π)
sub-pre-idl-β (wk-wk π)   = cong (sub-wk (wk-wk wk-id)) (sub-pre-idl-β π)
{-# REWRITE sub-pre-idl-β #-}

mutual
  sub-val-wk-η : (θ : Γ ⊢ Ψ) (π : Ψ ⊇ Δ) (V : Δ ⊢ᵛ X) → sub-val θ (wk-val π V) ≡ sub-val (sub-pre θ π) V
  sub-val-wk-η θ π (var i)    = refl
  sub-val-wk-η θ π (lam M)    = cong lam (sub-comp-wk-η (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-cong π) M)
  sub-val-wk-η θ π (pair V W) = cong₂ pair (sub-val-wk-η θ π V) (sub-val-wk-η θ π W)
  sub-val-wk-η θ π unit       = refl
  sub-val-wk-η θ π (inl V)    = cong inl (sub-val-wk-η θ π V)
  sub-val-wk-η θ π (inr V)    = cong inr (sub-val-wk-η θ π V)

  sub-comp-wk-η : (θ : Γ ⊢ Ψ) (π : Ψ ⊇ Δ) (M : Δ ⊢ᶜ X) → sub-comp θ (wk-comp π M) ≡ sub-comp (sub-pre θ π) M
  sub-comp-wk-η θ π (return V)   = cong return (sub-val-wk-η θ π V)
  sub-comp-wk-η θ π (pm V M)     = cong₂ pm (sub-val-wk-η θ π V) (sub-comp-wk-η (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) (wk-cong (wk-cong π)) M)
  sub-comp-wk-η θ π (push M N)   = cong₂ push (sub-comp-wk-η θ π M) (sub-comp-wk-η (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-cong π) N)
  sub-comp-wk-η θ π (case V M N) = cong₃ case (sub-val-wk-η θ π V) (sub-comp-wk-η (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-cong π) M) (sub-comp-wk-η (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-cong π) N)
  sub-comp-wk-η θ π (app V W)    = cong₂ app (sub-val-wk-η θ π V) (sub-val-wk-η θ π W)
  sub-comp-wk-η θ π (colam M)    = cong colam (sub-comp-wk-η (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (wk-cong π) M)
  sub-comp-wk-η θ π (coapp M V)  = cong₂ coapp (sub-comp-wk-η θ π M) (sub-val-wk-η θ π V)

{-# REWRITE sub-val-wk-η sub-comp-wk-η #-}

--------------------------------------------------------------------------
-- substitution composition

sub-∘ : Γ ⊢ Δ → Δ ⊢ Ψ → Γ ⊢ Ψ
sub-∘ θ = sub-map (sub-val θ)

mutual
  sub-val-sub-η : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) (V : Ψ ⊢ᵛ X) → sub-val θ (sub-val φ V) ≡ sub-val (sub-∘ θ φ) V
  sub-val-sub-η θ φ (var i)    = refl
  sub-val-sub-η θ φ (lam M)    = cong lam (sub-comp-sub-η (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here)) M)
  sub-val-sub-η θ φ (pair V W) = cong₂ pair (sub-val-sub-η θ φ V) (sub-val-sub-η θ φ W)
  sub-val-sub-η θ φ unit       = refl
  sub-val-sub-η θ φ (inl V)    = cong inl (sub-val-sub-η θ φ V)
  sub-val-sub-η θ φ (inr V)    = cong inr (sub-val-sub-η θ φ V)

  sub-comp-sub-η : (θ : Γ ⊢ Δ) (φ : Δ ⊢ Ψ) (M : Ψ ⊢ᶜ X) → sub-comp θ (sub-comp φ M) ≡ sub-comp (sub-∘ θ φ) M
  sub-comp-sub-η θ φ (return V)   = cong return (sub-val-sub-η θ φ V)
  sub-comp-sub-η θ φ (pm V M)     = cong₂ pm (sub-val-sub-η θ φ V) (sub-comp-sub-η (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) φ) (var (there here))) (var here)) M)
  sub-comp-sub-η θ φ (push M N)   = cong₂ push (sub-comp-sub-η θ φ M) (sub-comp-sub-η (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here)) N)
  sub-comp-sub-η θ φ (case V M N) = cong₃ case (sub-val-sub-η θ φ V) (sub-comp-sub-η (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here)) M) (sub-comp-sub-η (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here)) N)
  sub-comp-sub-η θ φ (app V W)    = cong₂ app (sub-val-sub-η θ φ V) (sub-val-sub-η θ φ W)
  sub-comp-sub-η θ φ (colam M)    = cong colam (sub-comp-sub-η (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) (sub-ex (sub-wk (wk-wk wk-id) φ) (var here)) M)
  sub-comp-sub-η θ φ (coapp M V)  = cong₂ coapp (sub-comp-sub-η θ φ M) (sub-val-sub-η θ φ V)

{-# REWRITE sub-val-sub-η sub-comp-sub-η #-}

--------------------------------------------------------------------------
-- identity substitution

sub-mem-id-β : (i : Γ ∋ X) → sub-mem (sub-id {Γ}) i ≡ var i
sub-mem-id-β here      = refl
sub-mem-id-β (there i) = cong (wk-val (wk-wk wk-id)) (sub-mem-id-β i)
{-# REWRITE sub-mem-id-β #-}

mutual
  sub-val-ren-β : (π : Γ ⊇ Δ) (V : Δ ⊢ᵛ X) → sub-val (sub-wk π sub-id) V ≡ wk-val π V
  sub-val-ren-β π (var i)    = refl
  sub-val-ren-β π (lam M)    = cong lam (sub-comp-ren-β (wk-cong π) M)
  sub-val-ren-β π (pair V W) = cong₂ pair (sub-val-ren-β π V) (sub-val-ren-β π W)
  sub-val-ren-β π unit       = refl
  sub-val-ren-β π (inl V)    = cong inl (sub-val-ren-β π V)
  sub-val-ren-β π (inr V)    = cong inr (sub-val-ren-β π V)

  sub-comp-ren-β : (π : Γ ⊇ Δ) (M : Δ ⊢ᶜ X) → sub-comp (sub-wk π sub-id) M ≡ wk-comp π M
  sub-comp-ren-β π (return V)   = cong return (sub-val-ren-β π V)
  sub-comp-ren-β π (pm V M)     = cong₂ pm (sub-val-ren-β π V) (sub-comp-ren-β (wk-cong (wk-cong π)) M)
  sub-comp-ren-β π (push M N)   = cong₂ push (sub-comp-ren-β π M) (sub-comp-ren-β (wk-cong π) N)
  sub-comp-ren-β π (case V M N) = cong₃ case (sub-val-ren-β π V) (sub-comp-ren-β (wk-cong π) M) (sub-comp-ren-β (wk-cong π) N)
  sub-comp-ren-β π (app V W)    = cong₂ app (sub-val-ren-β π V) (sub-val-ren-β π W)
  sub-comp-ren-β π (colam M)    = cong colam (sub-comp-ren-β (wk-cong π) M)
  sub-comp-ren-β π (coapp M V)  = cong₂ coapp (sub-comp-ren-β π M) (sub-val-ren-β π V)

{-# REWRITE sub-val-ren-β sub-comp-ren-β #-}

sub-val-id-β : (V : Γ ⊢ᵛ X) → sub-val (sub-id {Γ}) V ≡ V
sub-val-id-β = sub-val-ren-β wk-id

sub-comp-id-β : (M : Γ ⊢ᶜ X) → sub-comp (sub-id {Γ}) M ≡ M
sub-comp-id-β = sub-comp-ren-β wk-id

{-# REWRITE sub-val-id-β sub-comp-id-β #-}

sub-∘-idr-β : (θ : Γ ⊢ Δ) → sub-map (sub-val θ) sub-id ≡ θ
sub-∘-idr-β sub-ε        = refl
sub-∘-idr-β (sub-ex θ V) = cong₂ sub-ex (sub-∘-idr-β θ) refl
{-# REWRITE sub-∘-idr-β #-}

--------------------------------------------------------------------------
-- syntactic sugar

ccase : Γ ⊢ᶜ X `+ Y → (Γ ∙ X) ⊢ᶜ Z → (Γ ∙ Y) ⊢ᶜ Z
      ------------------------------------------------
      → Γ ⊢ᶜ Z
ccase M N P = push M (case (var here) (wk-comp (wk-cong (wk-wk wk-id)) N) (wk-comp (wk-cong (wk-wk wk-id)) P))

throw : Γ ⊢ᵛ X ̃ → Γ ⊢ᵛ X
      -------------------------
      → Γ ⊢ᶜ Y
throw V W = coapp (return (inl W)) V

catch : (Γ ∙ X ̃) ⊢ᶜ Y → (Γ ∙ X) ⊢ᶜ Y
      ------------------------------------
      → Γ ⊢ᶜ Y
catch M N = ccase (colam M) N (return (var here))

--------------------------------------------------------------------------
-- equational theory

variable
  V V₁ V₂ V₃ W W₁ W₂ : Γ ⊢ᵛ X
  M M₁ M₂ M₃ N N₁ N₂ : Γ ⊢ᶜ X

syntax EqVal Γ X e₁ e₂ = Γ ⊢ᵛ e₁ ≈ e₂ ∶ X

syntax EqComp Γ X e₁ e₂ = Γ ⊢ᶜ e₁ ≈ e₂ ∶ X

data EqVal (Γ : Ctx) : (X : Ty) → Γ ⊢ᵛ X → Γ ⊢ᵛ X → Set

data EqComp (Γ : Ctx) : (X : Ty) → Γ ⊢ᶜ X → Γ ⊢ᶜ X → Set

data EqVal Γ where

  -- equivalence rules
  ≈-refl  :
          -------------
          Γ ⊢ᵛ V ≈ V ∶ X

  ≈-sym   : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X
          ------------------
          → Γ ⊢ᵛ V₂ ≈ V₁ ∶ X

  ≈-trans : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X → Γ ⊢ᵛ V₂ ≈ V₃ ∶ X
          -------------------------------------
          → Γ ⊢ᵛ V₁ ≈ V₃ ∶ X

  -- congruence rules
  lam-cong : (Γ ∙ X) ⊢ᶜ M₁ ≈ M₂ ∶ Y
           ---------------------------------
           → Γ ⊢ᵛ lam M₁ ≈ lam M₂ ∶ X `⇒ Y

  pair-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X → Γ ⊢ᵛ W₁ ≈ W₂ ∶ Y
            ----------------------------------------
            → Γ ⊢ᵛ pair V₁ W₁ ≈ pair V₂ W₂ ∶ X `× Y

  inl-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X
           ---------------------------------
           → Γ ⊢ᵛ inl V₁ ≈ inl V₂ ∶ X `+ Y

  inr-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ Y
           ---------------------------------
           → Γ ⊢ᵛ inr V₁ ≈ inr V₂ ∶ X `+ Y

  -- beta/eta rules

  unit-eta : (V : Γ ⊢ᵛ `𝟙)
           ------------------------
           → Γ ⊢ᵛ V ≈ unit ∶ `𝟙

  lam-eta : (V : Γ ⊢ᵛ X `⇒ Y)
          -----------------------------------------------
          → Γ ⊢ᵛ V ≈ lam (app (wk V) (var here)) ∶ X `⇒ Y

data EqComp Γ where

  -- equivalence rules
  ≈-refl  :
          -------------
          Γ ⊢ᶜ M ≈ M ∶ X

  ≈-sym   : Γ ⊢ᶜ M₁ ≈ M₂ ∶ X
          ------------------
          → Γ ⊢ᶜ M₂ ≈ M₁ ∶ X

  ≈-trans : Γ ⊢ᶜ M₁ ≈ M₂ ∶ X → Γ ⊢ᶜ M₂ ≈ M₃ ∶ X
          ---------------------------------------
          → Γ ⊢ᶜ M₁ ≈ M₃ ∶ X

  -- congruence rules
  return-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X
              ---------------------------------
              → Γ ⊢ᶜ return V₁ ≈ return V₂ ∶ X

  pm-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X `× Y → (Γ ∙ X ∙ Y) ⊢ᶜ M₁ ≈ M₂ ∶ Z
          -------------------------------------------------------
          → Γ ⊢ᶜ pm V₁ M₁ ≈ pm V₂ M₂ ∶ Z

  case-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X `+ Y → (Γ ∙ X) ⊢ᶜ M₁ ≈ M₂ ∶ Z → (Γ ∙ Y) ⊢ᶜ N₁ ≈ N₂ ∶ Z
            ---------------------------------------------------------------------------
            → Γ ⊢ᶜ case V₁ M₁ N₁ ≈ case V₂ M₂ N₂ ∶ Z

  push-cong : Γ ⊢ᶜ M₁ ≈ M₂ ∶ X → (Γ ∙ X) ⊢ᶜ N₁ ≈ N₂ ∶ Y
            ---------------------------------------------------
            → Γ ⊢ᶜ push M₁ N₁ ≈ push M₂ N₂ ∶ Y

  app-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X `⇒ Y → Γ ⊢ᵛ W₁ ≈ W₂ ∶ X
           ------------------------------------------------
           → Γ ⊢ᶜ app V₁ W₁ ≈ app V₂ W₂ ∶ Y

  colam-cong : (Γ ∙ X ̃) ⊢ᶜ M₁ ≈ M₂ ∶ Y
             -------------------------------------
             → Γ ⊢ᶜ colam M₁ ≈ colam M₂ ∶ X `+ Y

  coapp-cong : Γ ⊢ᶜ M₁ ≈ M₂ ∶ X `+ Y → Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ̃
             ------------------------------------------------
             → Γ ⊢ᶜ coapp M₁ V₁ ≈ coapp M₂ V₂ ∶ Y

  -- beta/eta rules

  pm-beta : (V : Γ ⊢ᵛ X) → (W : Γ ⊢ᵛ Y) → (M : (Γ ∙ X ∙ Y) ⊢ᶜ Z)
          ------------------------------------------------------------------------
          → Γ ⊢ᶜ pm (pair V W) M ≈ sub-comp (sub-ex (sub-ex sub-id V) W) M ∶ Z

  pm-eta : (V : Γ ⊢ᵛ X `× Y) → (M : (Γ ∙ (X `× Y)) ⊢ᶜ Z)
         -------------------------------------------------------------------------------------------
         → Γ ⊢ᶜ sub-comp (sub-ex sub-id V) M ≈ pm V (sub-comp (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) sub-id) (pair (var (there here)) (var here))) M) ∶ Z

  return-beta : (V : Γ ⊢ᵛ X) → (M : (Γ ∙ X) ⊢ᶜ Y)
              ---------------------------------------------------------------
              → Γ ⊢ᶜ push (return V) M ≈ sub-comp (sub-ex sub-id V) M ∶ Y

  return-eta : (M : Γ ⊢ᶜ X)
             -----------------------
             → Γ ⊢ᶜ M ≈ push M (return (var here)) ∶ X

  push-eta : (M : Γ ⊢ᶜ X) → (N : (Γ ∙ X) ⊢ᶜ Y) → (P : (Γ ∙ Y) ⊢ᶜ Z)
           ----------------------------------------------------------------
           → Γ ⊢ᶜ push (push M N) P ≈ push M (push N (wk-comp (wk-cong (wk-wk wk-id)) P)) ∶ Z

  lam-beta : (M : (Γ ∙ X) ⊢ᶜ Y) → (V : Γ ⊢ᵛ X)
           --------------------------------------------------------
           → Γ ⊢ᶜ app (lam M) V ≈ sub-comp (sub-ex sub-id V) M ∶ Y

  case-inl-beta : (V : Γ ⊢ᵛ X) → (M : (Γ ∙ X) ⊢ᶜ Z) (N : (Γ ∙ Y) ⊢ᶜ Z)
                ------------------------------------------------------------
                → Γ ⊢ᶜ case (inl V) M N ≈ sub-comp (sub-ex sub-id V) M ∶ Z

  case-inr-beta : (V : Γ ⊢ᵛ Y) → (M : (Γ ∙ X) ⊢ᶜ Z) (N : (Γ ∙ Y) ⊢ᶜ Z)
                ------------------------------------------------------------
                → Γ ⊢ᶜ case (inr V) M N ≈ sub-comp (sub-ex sub-id V) N ∶ Z

  case-eta : (V : Γ ⊢ᵛ X `+ Y) → (M : (Γ ∙ X `+ Y) ⊢ᶜ Z)
           ------------------------------------------------
           → Γ ⊢ᶜ sub-comp (sub-ex sub-id V) M ≈ case V (sub-comp (sub-ex (sub-wk (wk-wk wk-id) sub-id) (inl (var here))) M) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) sub-id) (inr (var here))) M) ∶ Z

  -- colam/coapp rules

  colam-beta : (M : (Γ ∙ X ̃) ⊢ᶜ Y) → (V : Γ ⊢ᵛ X ̃)
             ------------------------------------------------------------
             → Γ ⊢ᶜ coapp (colam M) V ≈ sub-comp (sub-ex sub-id V) M ∶ Y

  colam-eta : (M : Γ ⊢ᶜ X `+ Y)
            --------------------------------------------------------------------
            → Γ ⊢ᶜ M ≈ colam (coapp (wk-comp (wk-wk wk-id) M) (var here)) ∶ X `+ Y

  -- control rules

  coapp-inl-push : (W : Γ ⊢ᵛ X) → (V : Γ ⊢ᵛ X ̃) → (N : (Γ ∙ Y) ⊢ᶜ Z)
                 ---------------------------------------------------------------------------
                 → Γ ⊢ᶜ push (coapp (return (inl W)) V) N ≈ coapp (return (inl W)) V ∶ Z

  case-colam-push : (M : (Γ ∙ X ̃) ⊢ᶜ Y) → (N : (Γ ∙ X) ⊢ᶜ Z) → (P : (Γ ∙ Y) ⊢ᶜ Z)
                  --------------------------------------------------------------------
                  → Γ ⊢ᶜ ccase (colam M) N P ≈ ccase (colam (push M (wk-comp (wk-cong (wk-wk wk-id)) P))) N (return (var here)) ∶ Z

  coapp-eta : (M : Γ ⊢ᶜ X `+ Y) → (V : Γ ⊢ᵛ X ̃)
            ------------------------------------------------------------------------
            → Γ ⊢ᶜ coapp M V ≈ ccase M (throw (wk V) (var here)) (return (var here)) ∶ Y

--------------------------------------------------------------------------
-- equational reasoning

module ≈ᵛ-Reasoning {Γ X} = Equational (EqVal Γ X) ≈-refl ≈-sym ≈-trans
module ≈ᶜ-Reasoning {Γ X} = Equational (EqComp Γ X) ≈-refl ≈-sym ≈-trans
