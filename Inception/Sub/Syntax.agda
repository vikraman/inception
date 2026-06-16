{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Syntax where

open import Data.Nat

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; trans; cong₂)
open Eq.≡-Reasoning

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)

open import Inception.Sub.Equality

infixr 40 _`×_
infixr 25 _`⇒_

data Ty : Set where
  `Unit : Ty
  _`×_ _`⇒_ : Ty -> Ty -> Ty
  `V : Ty

module Cx (Ty : Set) where

  infixl 15 _∙_
  infix 10 _∋_

  data Ctx : Set where
    ε : Ctx
    _∙_ : Ctx -> Ty -> Ctx

  variable
    A B C D X X' Y Y' Z Z' : Ty
    Γ Δ Ψ Γ' Γ'' Γ''' Δ' Γ₁ Γ₂ Γ₃ : Ctx

  data _∋_ : Ctx -> Ty -> Set where
    h :
      ---------
      Γ ∙ A ∋ A

    t : Γ ∋ A
      -------------
      -> Γ ∙ B ∋ A

open Cx Ty public

syntax Val Γ A = Γ ⊢ᵛ A

data Val : Ctx -> Ty -> Set

syntax Comp Γ A = Γ ⊢ᶜ A

data Comp : Ctx -> Ty -> Set

data Val where

  var : (i : Γ ∋ A)
      ---------
      -> Γ ⊢ᵛ A

  lam : (Γ ∙ A) ⊢ᶜ B
      -----------------
      -> Γ ⊢ᵛ A `⇒ B

  pair : Γ ⊢ᵛ A -> Γ ⊢ᵛ B
      -------------------
       -> Γ ⊢ᵛ A `× B

  pm : Γ ⊢ᵛ A `× B -> (Γ ∙ A ∙ B) ⊢ᵛ C
     -----------------------------------
     -> Γ ⊢ᵛ C

  unit :
       -----------
        Γ ⊢ᵛ `Unit

data Comp where

  return : Γ ⊢ᵛ A
         -----------
         -> Γ ⊢ᶜ A

  pm : Γ ⊢ᵛ A `× B -> (Γ ∙ A ∙ B) ⊢ᶜ C
     -----------------------------------
     -> Γ ⊢ᶜ C

  push : Γ ⊢ᶜ A -> (Γ ∙ A) ⊢ᶜ B
       ---------------------------
       -> Γ ⊢ᶜ B

  app : Γ ⊢ᵛ A `⇒ B -> Γ ⊢ᵛ A
      -------------------------
              -> Γ ⊢ᶜ B

  var : Γ ⊢ᵛ `V
      -----------
      -> Γ ⊢ᶜ A

  sub : (Γ ∙ `V) ⊢ᶜ A -> Γ ⊢ᶜ A
      ---------------------------
      -> Γ ⊢ᶜ A

data V̲a̲l̲ : Ctx → Ty → Set where

    l̲a̲m̲ : (Γ ∙ X) ⊢ᶜ Y → V̲a̲l̲ Γ (X `⇒ Y)

    pa̲i̲r̲ : V̲a̲l̲ Γ X → V̲a̲l̲ Γ Y → V̲a̲l̲ Γ (X `× Y)

    u̲n̲i̲t̲ : V̲a̲l̲ Γ `Unit

    v̲a̲r̲  : (i : Γ ∋ `V) → V̲a̲l̲ Γ `V

data C̲o̲m̲p : Ctx → Ty → Set where

    r̲e̲t̲u̲r̲n̲ : V̲a̲l̲ Γ X → C̲o̲m̲p Γ X

    a̲pp    : Γ ⊢ᵛ X `⇒ Y -> V̲a̲l̲ Γ X -> C̲o̲m̲p Γ Y

syntax Wk Γ Δ = Γ ⊇ Δ

data Wk : (Γ Δ : Ctx) -> Set where
  wk-ε : ε ⊇ ε
  wk-cong : (π : Wk Γ Δ) -> Wk (Γ ∙ A) (Δ ∙ A)
  wk-wk : (π : Wk Γ Δ) -> Wk (Γ ∙ A) Δ

wk-id : Wk Γ Γ
wk-id {Γ = ε} = wk-ε
wk-id {Γ = Γ ∙ A} = wk-cong wk-id

wk-mem : Wk Γ Δ -> Δ ∋ A -> Γ ∋ A
wk-mem (wk-cong π) h = h
wk-mem (wk-wk π) h = t (wk-mem π h)
wk-mem (wk-cong π) (t i) = t (wk-mem π i)
wk-mem (wk-wk π) (t i) = t (wk-mem π (t i))

mutual
  wk-val : Wk Γ Δ -> Δ ⊢ᵛ A -> Γ ⊢ᵛ A
  wk-val π (var x)         = var (wk-mem π x)
  wk-val π (lam M)         = lam (wk-comp (wk-cong π) M)

  wk-val π (pair V1 V2)    = pair (wk-val π V1) (wk-val π V2)
  wk-val π (pm V W)        = pm (wk-val π V) (wk-val (wk-cong (wk-cong π)) W)
  wk-val π unit            = unit

  wk-comp : Wk Γ Δ -> Δ ⊢ᶜ A -> Γ ⊢ᶜ A
  wk-comp π (return V)     = return (wk-val π V)
  wk-comp π (pm V M)       = pm (wk-val π V) (wk-comp (wk-cong (wk-cong π)) M)
  wk-comp π (push M N)     = push (wk-comp π M) (wk-comp (wk-cong π) N)
  wk-comp π (app V W)      = app (wk-val π V) (wk-val π W)
  wk-comp π (var V)        = var (wk-val π V)
  wk-comp π (sub M N)      = sub (wk-comp (wk-cong π) M) (wk-comp π N)

wk : Val Γ A -> Val (Γ ∙ B) A
wk = wk-val (wk-wk wk-id)

data Sub (Γ : Ctx) : (Δ : Ctx) -> Set where
  sub-ε : Sub Γ ε
  sub-ex : (θ : Sub Γ Δ) -> (V : Val Γ A) -> Sub Γ (Δ ∙ A)

sub-mem : Sub Γ Δ -> Δ ∋ A -> Val Γ A
sub-mem (sub-ex θ V) h = V
sub-mem (sub-ex θ V) (t i) = sub-mem θ i

sub-wk : Wk Γ Δ -> Sub Δ Ψ -> Sub Γ Ψ
sub-wk π sub-ε = sub-ε
sub-wk π (sub-ex θ V) = sub-ex (sub-wk π θ) (wk-val π V)

sub-id : Sub Γ Γ
sub-id {Γ = ε} = sub-ε
sub-id {Γ = Γ ∙ A} = sub-ex (sub-wk (wk-wk wk-id) sub-id) (var h)

mutual
  sub-val : Sub Γ Δ -> Δ ⊢ᵛ A -> Γ ⊢ᵛ A
  sub-val θ (var x) = sub-mem θ x
  sub-val θ (lam M) = lam (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) M)
  sub-val θ (pair V W) = pair (sub-val θ V) (sub-val θ W)
  sub-val θ (pm V W) = pm (sub-val θ V) (sub-val (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) W)
  sub-val θ unit = unit

  sub-comp : Sub Γ Δ -> Δ ⊢ᶜ A -> Γ ⊢ᶜ A
  sub-comp θ (return V) = return (sub-val θ V)
  sub-comp θ (pm V M) = pm (sub-val θ V) (sub-comp (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (t h))) (var h)) M)
  sub-comp θ (push M N) = push (sub-comp θ M) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) N)
  sub-comp θ (app V W) = app (sub-val θ V) (sub-val θ W)
  sub-comp θ (var V) = var (sub-val θ V)
  sub-comp θ (sub M N) = sub (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) M) (sub-comp θ N)

-- syntactic sugar

letv : Γ ⊢ᵛ A -> (Γ ∙ A) ⊢ᵛ B
     ---------------------------
    -> Γ ⊢ᵛ B
letv V W = sub-val (sub-ex sub-id V) W

letc : Γ ⊢ᵛ A -> (Γ ∙ A) ⊢ᶜ B
     ---------------------------
     -> Γ ⊢ᶜ B
letc V M = sub-comp (sub-ex sub-id V) M

exchg : Sub (Γ ∙ A ∙ B)(Γ ∙ B ∙ A)
exchg = sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) sub-id) (var h)) (var (t h))

variable
  x : Γ ∋ A
  V V1 V2 V3 V4 W W1 W2 W3 : Γ ⊢ᵛ A
  M M1 M2 M3 M4 N N1 N2 N3 P P1 P2 P3 : Γ ⊢ᶜ A

syntax EqVal Γ A e1 e2 = Γ ⊢ᵛ e1 ≈ e2 ∶ A

syntax EqComp Γ A e1 e2 = Γ ⊢ᶜ e1 ≈ e2 ∶ A

data EqVal (Γ : Ctx) : (A : Ty) -> Γ ⊢ᵛ A -> Γ ⊢ᵛ A -> Set

data EqComp (Γ : Ctx) : (A : Ty) -> Γ ⊢ᶜ A -> Γ ⊢ᶜ A -> Set

data EqVal Γ where

  -- equivalence rules
  ≈-refl  :
          -------------
          Γ ⊢ᵛ V ≈ V ∶ A

  ≈-sym   : Γ ⊢ᵛ V1 ≈ V2 ∶ A
          ------------------
          -> Γ ⊢ᵛ V2 ≈ V1 ∶ A

  ≈-trans : Γ ⊢ᵛ V1 ≈ V2 ∶ A -> Γ ⊢ᵛ V2 ≈ V3 ∶ A
          -------------------------------------
          -> Γ ⊢ᵛ V1 ≈ V3 ∶ A

  -- congruence rules
  lam-cong : (Γ ∙ A) ⊢ᶜ M1 ≈ M2 ∶ B
           ---------------------------------
           -> Γ ⊢ᵛ lam M1 ≈ lam M2 ∶ A `⇒ B

  pair-cong : Γ ⊢ᵛ V1 ≈ V2 ∶ A -> Γ ⊢ᵛ W1 ≈ W2 ∶ B
            ----------------------------------------
            -> Γ ⊢ᵛ pair V1 W1 ≈ pair V2 W2 ∶ A `× B

  pm-cong : Γ ⊢ᵛ V1 ≈ V2 ∶ A `× B -> (Γ ∙ A ∙ B) ⊢ᵛ V3 ≈ V4 ∶ C
          -------------------------------------------------------------------
          -> Γ ⊢ᵛ pm V1 V3 ≈ pm V2 V4 ∶ C

  -- beta/eta rules

  unit-eta : (V : Γ ⊢ᵛ `Unit)
           ------------------------
           -> Γ ⊢ᵛ V ≈ unit ∶ `Unit

  pm-beta : (V1 : Γ ⊢ᵛ A) -> (V2 : Γ ⊢ᵛ B) -> (W : (Γ ∙ A ∙ B) ⊢ᵛ C)
          ------------------------------------------------------------------------
          -> Γ ⊢ᵛ pm (pair V1 V2) W ≈ sub-val (sub-ex (sub-ex sub-id V1) V2) W ∶ C

  pm-eta : (V : Γ ⊢ᵛ A `× B) -> (W : (Γ ∙ (A `× B)) ⊢ᵛ C)
         -------------------------------------------------------------------------------------------
         -> Γ ⊢ᵛ sub-val (sub-ex sub-id V) W ≈ pm V (sub-val (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) sub-id) (pair (var (t h)) (var h))) W) ∶ C

  lam-eta : (V : Γ ⊢ᵛ A `⇒ B)
          ---------------------------
          -> Γ ⊢ᵛ V ≈ lam (app (wk V) (var h)) ∶ A `⇒ B

data EqComp Γ where

  -- equivalence rules
  ≈-refl  :
          -------------
          Γ ⊢ᶜ M ≈ M ∶ A

  ≈-sym   : Γ ⊢ᶜ M1 ≈ M2 ∶ A
          -------------------
          -> Γ ⊢ᶜ M2 ≈ M1 ∶ A

  ≈-trans : Γ ⊢ᶜ M1 ≈ M2 ∶ A -> Γ ⊢ᶜ M2 ≈ M3 ∶ A
          -------------------------------------
          -> Γ ⊢ᶜ M1 ≈ M3 ∶ A

  -- congruence rules
  return-cong : Γ ⊢ᵛ V1 ≈ V2 ∶ A
             -----------------------------
             -> Γ ⊢ᶜ return V1 ≈ return V2 ∶ A

  pm-cong : Γ ⊢ᵛ V1 ≈ V2 ∶ A `× B -> (Γ ∙ A ∙ B) ⊢ᶜ M1 ≈ M2 ∶ C
            -------------------------------------------------------------------
            -> Γ ⊢ᶜ pm V1 M1 ≈ pm V2 M2 ∶ C

  push-cong : Γ ⊢ᶜ M1 ≈ M2 ∶ A -> (Γ ∙ A) ⊢ᶜ N1 ≈ N2 ∶ B
            ---------------------------------------------------
            -> Γ ⊢ᶜ push M1 N1 ≈ push M2 N2 ∶ B

  app-cong : Γ ⊢ᵛ V1 ≈ V2 ∶ A `⇒ B -> Γ ⊢ᵛ W1 ≈ W2 ∶ A
            ------------------------------------------------
            -> Γ ⊢ᶜ app V1 W1 ≈ app V2 W2 ∶ B

  var-cong : Γ ⊢ᵛ V1 ≈ V2 ∶ `V
            ----------------------------
            -> Γ ⊢ᶜ var V1 ≈ var V2 ∶ A

  sub-cong : (Γ ∙ `V) ⊢ᶜ M1 ≈ M2 ∶ A -> Γ ⊢ᶜ N1 ≈ N2 ∶ A
            -------------------------------------------------------------------------------------------
            -> Γ ⊢ᶜ sub M1 N1 ≈ sub M2 N2 ∶ A

  -- beta/eta rules

  pm-beta : (V1 : Γ ⊢ᵛ A) -> (V2 : Γ ⊢ᵛ B) -> (M : (Γ ∙ A ∙ B) ⊢ᶜ C)
          ------------------------------------------------------------------------
          -> Γ ⊢ᶜ pm (pair V1 V2) M ≈ sub-comp (sub-ex (sub-ex sub-id V1) V2) M ∶ C

  pm-eta : (V : Γ ⊢ᵛ A `× B) -> (M : (Γ ∙ (A `× B)) ⊢ᶜ C)
         -------------------------------------------------------------------------------------------
         -> Γ ⊢ᶜ sub-comp (sub-ex sub-id V) M ≈ pm V (sub-comp (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) sub-id) (pair (var (t h)) (var h))) M) ∶ C

  return-beta : (V : Γ ⊢ᵛ A) -> (M : (Γ ∙ A) ⊢ᶜ B)
               ---------------------------------------------------------------
               -> Γ ⊢ᶜ push (return V) M ≈ sub-comp (sub-ex sub-id V) M ∶ B

  return-eta : (M : Γ ⊢ᶜ A)
              -----------------------
              -> Γ ⊢ᶜ M ≈ push M (return (var h)) ∶ A

  push-eta : (M : Γ ⊢ᶜ A) -> (N : (Γ ∙ A) ⊢ᶜ B) -> (P : (Γ ∙ B) ⊢ᶜ C)
           ----------------------------------------------------------------
           -> Γ ⊢ᶜ push (push M N) P ≈ push M (push N (wk-comp (wk-cong (wk-wk wk-id)) P)) ∶ C

  lam-beta : (M : (Γ ∙ A) ⊢ᶜ B) -> (V : Γ ⊢ᵛ A)
           ------------------------------------------------
           -> Γ ⊢ᶜ app (lam M) V ≈ sub-comp (sub-ex sub-id V) M ∶ B

  -- var/sub rules

  sub-weak : (M : Γ ⊢ᶜ A) -> (N : Γ ⊢ᶜ A)
           ------------------------------------------------
           -> Γ ⊢ᶜ sub (wk-comp (wk-wk wk-id) M) N ≈ M ∶ A

  sub-subst : (M : Γ ⊢ᶜ A)
            -------------------------------------------
            -> Γ ⊢ᶜ sub (var (var h)) M ≈ M ∶ A

  sub-ext : (M : (Γ ∙ `V) ⊢ᶜ A) -> (V : Γ ⊢ᵛ `V)
          ---------------------------------------------------------------------------
          -> Γ ⊢ᶜ sub (sub-comp sub-id M) (var V) ≈ sub-comp (sub-ex sub-id V) M ∶ A

  sub-assoc : (L : (Γ ∙ `V ∙ `V) ⊢ᶜ A) -> (M : (Γ ∙ `V) ⊢ᶜ A) -> (N : Γ ⊢ᶜ A)
            -----------------------------------------------------------------------------------------------
            -> Γ ⊢ᶜ sub (sub L M) N ≈ sub (sub (sub-comp exchg L) (wk-comp (wk-wk wk-id) N)) (sub M N) ∶ A

  -- algebraicity rules

  var-push : (V : Γ ⊢ᵛ `V) -> (M : (Γ ∙ A) ⊢ᶜ A)
           ----------------------------------------
           -> Γ ⊢ᶜ push (var V) M ≈ var V ∶ A

  sub-push : (M : (Γ ∙ `V) ⊢ᶜ A) -> (N : Γ ⊢ᶜ A) -> (L : (Γ ∙ A) ⊢ᶜ B)
           -------------------------------------------------------------------------------------------
           -> Γ ⊢ᶜ push (sub M N) L ≈ sub (push M (wk-comp (wk-cong (wk-wk wk-id)) L)) (push N L) ∶ B


wk-trans : Wk Γ Δ → Wk Δ Ψ → Wk Γ Ψ
wk-trans wk-ε π₂ = π₂
wk-trans (wk-cong π₁) (wk-cong π₂) = wk-cong (wk-trans π₁ π₂)
wk-trans (wk-cong π₁) (wk-wk π₂) = wk-wk (wk-trans π₁ π₂)
wk-trans (wk-wk π₁) π₂ = wk-wk (wk-trans π₁ π₂)

wk-mem-trans : (i : Γ ∋ A) → (π₁ : Wk Ψ Δ) → (π₂ : Wk Δ Γ) → wk-mem π₁ (wk-mem π₂ i) ≡ wk-mem (wk-trans π₁ π₂) i
wk-mem-trans h (wk-cong π₁) (wk-cong π₂) = refl
wk-mem-trans h (wk-cong π₁) (wk-wk π₂) = cong t (wk-mem-trans h π₁ π₂)
wk-mem-trans h (wk-wk π₁) (wk-cong π₂) = cong t (wk-mem-trans h π₁ (wk-cong π₂))
wk-mem-trans h (wk-wk π₁) (wk-wk π₂) = cong t (wk-mem-trans h π₁ (wk-wk π₂))
wk-mem-trans (t i) (wk-cong π₁) (wk-cong π₂) = cong t (wk-mem-trans i π₁ π₂)
wk-mem-trans (t i) (wk-wk (wk-cong π₁)) (wk-cong π₂) = cong t (cong t (wk-mem-trans i π₁ π₂))
wk-mem-trans (t i) (wk-wk (wk-wk π₁)) (wk-cong π₂) = cong t (cong t (wk-mem-trans (t i) π₁ (wk-cong π₂)))
wk-mem-trans (t i) (wk-cong π₁) (wk-wk π₂) = cong t (wk-mem-trans (t i) π₁ π₂)
wk-mem-trans (t i) (wk-wk (wk-cong π₁)) (wk-wk π₂) = cong t (wk-mem-trans (t i) (wk-cong π₁) (wk-wk π₂))
wk-mem-trans (t i) (wk-wk (wk-wk π₁)) (wk-wk π₂) = cong t (wk-mem-trans (t i) (wk-wk π₁) (wk-wk π₂))

mutual

  wk-val-trans : (M : Γ ⊢ᵛ A) → (π₁ : Wk Ψ Δ) → (π₂ : Wk Δ Γ) → wk-val π₁ (wk-val π₂ M) ≡ wk-val (wk-trans π₁ π₂) M
  wk-val-trans (var i) π₁ π₂ = cong var (wk-mem-trans i π₁ π₂)
  wk-val-trans (lam x) π₁ π₂ = cong lam (wk-comp-trans x (wk-cong π₁) (wk-cong π₂))
  wk-val-trans (pair LHS RHS) π₁ π₂ = pair (wk-val π₁ (wk-val π₂ LHS)) (wk-val π₁ (wk-val π₂ RHS))
               ≡⟨ cong (λ x → pair (wk-val π₁ (wk-val π₂ LHS)) x) (wk-val-trans RHS π₁ π₂) ⟩
               pair (wk-val π₁ (wk-val π₂ LHS)) (wk-val (wk-trans π₁ π₂) RHS)
               ≡⟨ cong (λ x → pair x (wk-val (wk-trans π₁ π₂) RHS)) (wk-val-trans LHS π₁ π₂) ⟩
               pair (wk-val (wk-trans π₁ π₂) LHS) (wk-val (wk-trans π₁ π₂) RHS) ∎
  wk-val-trans (pm M N) π₁ π₂ =
               pm (wk-val π₁ (wk-val π₂ M)) (wk-val (wk-cong (wk-cong π₁)) (wk-val (wk-cong (wk-cong π₂)) N))
               ≡⟨ cong (λ x → pm x (wk-val (wk-cong (wk-cong π₁)) (wk-val (wk-cong (wk-cong π₂)) N))) (wk-val-trans M π₁ π₂) ⟩
               pm (wk-val (wk-trans π₁ π₂) M) (wk-val (wk-cong (wk-cong π₁)) (wk-val (wk-cong (wk-cong π₂)) N))
               ≡⟨ cong (λ x → pm (wk-val (wk-trans π₁ π₂) M) x) (wk-val-trans N (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π₂)) ) ⟩
               pm (wk-val (wk-trans π₁ π₂) M) (wk-val (wk-cong (wk-cong (wk-trans π₁ π₂))) N) ∎
  wk-val-trans unit π₁ π₂ = refl

  wk-comp-trans : (W : Γ ⊢ᶜ A) → (π₁ : Wk Ψ Δ) → (π₂ : Wk Δ Γ) → wk-comp π₁ (wk-comp π₂ W) ≡ wk-comp (wk-trans π₁ π₂) W
  wk-comp-trans (return M) π₁ π₂ = cong return (wk-val-trans M π₁ π₂)
  wk-comp-trans (pm M N) π₁ π₂ =
                pm (wk-val π₁ (wk-val π₂ M)) (wk-comp (wk-cong (wk-cong π₁)) (wk-comp (wk-cong (wk-cong π₂)) N))
                ≡⟨ cong (λ x → pm x (wk-comp (wk-cong (wk-cong π₁)) (wk-comp (wk-cong (wk-cong π₂)) N))) (wk-val-trans M π₁ π₂) ⟩
                pm (wk-val (wk-trans π₁ π₂) M) (wk-comp (wk-cong (wk-cong π₁)) (wk-comp (wk-cong (wk-cong π₂)) N))
                ≡⟨ cong (λ x → pm (wk-val (wk-trans π₁ π₂) M) x) (wk-comp-trans N (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π₂)) ) ⟩
                pm (wk-val (wk-trans π₁ π₂) M) (wk-comp (wk-cong (wk-cong (wk-trans π₁ π₂))) N) ∎
  wk-comp-trans (push W W₁) π₁ π₂ =
                push (wk-comp π₁ (wk-comp π₂ W)) (wk-comp (wk-cong π₁) (wk-comp (wk-cong π₂) W₁))
                ≡⟨ cong (λ x → push x (wk-comp (wk-cong π₁) (wk-comp (wk-cong π₂) W₁))) (wk-comp-trans W π₁ π₂) ⟩
                push (wk-comp (wk-trans π₁ π₂) W) (wk-comp (wk-cong π₁) (wk-comp (wk-cong π₂) W₁))
                ≡⟨ cong (λ x → push (wk-comp (wk-trans π₁ π₂) W) x) (wk-comp-trans W₁ (wk-cong π₁) (wk-cong π₂)) ⟩
                push (wk-comp (wk-trans π₁ π₂) W) (wk-comp (wk-cong (wk-trans π₁ π₂)) W₁) ∎
  wk-comp-trans (app x x₁) π₁ π₂ =
                app (wk-val π₁ (wk-val π₂ x)) (wk-val π₁ (wk-val π₂ x₁))
                ≡⟨ cong (λ y → app y (wk-val π₁ (wk-val π₂ x₁))) (wk-val-trans x π₁ π₂) ⟩
                app (wk-val (wk-trans π₁ π₂) x) (wk-val π₁ (wk-val π₂ x₁))
                ≡⟨ cong (λ y → app (wk-val (wk-trans π₁ π₂) x) y) (wk-val-trans x₁ π₁ π₂) ⟩
                app (wk-val (wk-trans π₁ π₂) x) (wk-val (wk-trans π₁ π₂) x₁) ∎
  wk-comp-trans (var x) π₁ π₂ = cong var (wk-val-trans x π₁ π₂)
  wk-comp-trans (sub W W₁) π₁ π₂ =
                sub (wk-comp (wk-cong π₁) (wk-comp (wk-cong π₂) W)) (wk-comp π₁ (wk-comp π₂ W₁))
                ≡⟨ cong (λ x → sub x (wk-comp π₁ (wk-comp π₂ W₁))) (wk-comp-trans W (wk-cong π₁) (wk-cong π₂)) ⟩
                sub (wk-comp (wk-cong (wk-trans π₁ π₂)) W) (wk-comp π₁ (wk-comp π₂ W₁))
                ≡⟨ cong (λ x → sub (wk-comp (wk-cong (wk-trans π₁ π₂)) W) x) (wk-comp-trans W₁ π₁ π₂) ⟩
                sub (wk-comp (wk-cong (wk-trans π₁ π₂)) W) (wk-comp (wk-trans π₁ π₂) W₁) ∎

wk-mem-id : {i : Γ ∋ A} → wk-mem wk-id i ≡ i
wk-mem-id {i = h} = refl
wk-mem-id {i = t i} = cong t wk-mem-id

mutual

  wk-val-id : (M : Γ ⊢ᵛ A) → wk-val wk-id M ≡ M
  wk-val-id (var i) = cong var wk-mem-id
  wk-val-id (lam W) = cong lam (wk-comp-id W)
  wk-val-id (pair LHS RHS) = pair (wk-val wk-id LHS) (wk-val wk-id RHS) ≡⟨ cong (λ y → pair y (wk-val wk-id RHS)) (wk-val-id LHS) ⟩ pair LHS (wk-val wk-id RHS) ≡⟨ cong (λ y → pair LHS y) (wk-val-id RHS) ⟩ pair LHS RHS ∎
  wk-val-id (pm M N) = pm (wk-val wk-id M) (wk-val (wk-cong (wk-cong wk-id)) N) ≡⟨ refl ⟩ pm (wk-val wk-id M) (wk-val wk-id N) ≡⟨ cong (λ y → pm y (wk-val wk-id N)) (wk-val-id M) ⟩ pm M (wk-val wk-id N) ≡⟨ cong (λ y → pm M y) (wk-val-id N) ⟩ pm M N ∎
  wk-val-id unit = refl

  wk-comp-id : (W : Γ ⊢ᶜ A) → wk-comp wk-id W ≡ W
  wk-comp-id (return x) = cong return (wk-val-id x)
  wk-comp-id (pm M N) = pm (wk-val wk-id M) (wk-comp (wk-cong (wk-cong wk-id)) N) ≡⟨ refl ⟩ pm (wk-val wk-id M) (wk-comp wk-id N) ≡⟨ cong (λ y → pm y (wk-comp wk-id N)) (wk-val-id M) ⟩ pm M (wk-comp wk-id N) ≡⟨ cong (λ y → pm M y) (wk-comp-id N) ⟩ pm M N ∎
  wk-comp-id (push M N) = push (wk-comp wk-id M) (wk-comp (wk-cong wk-id) N) ≡⟨ cong (λ y → push (wk-comp wk-id M) y) (wk-comp-id N) ⟩ push (wk-comp wk-id M) N ≡⟨ cong (λ y → push y N) (wk-comp-id M) ⟩ push M N ∎
  wk-comp-id (app W W₁) = app (wk-val wk-id W) (wk-val wk-id W₁) ≡⟨ cong (λ y → app y (wk-val wk-id W₁)) (wk-val-id W) ⟩ app W (wk-val wk-id W₁) ≡⟨ cong (λ y → app W y) (wk-val-id W₁) ⟩ app W W₁ ∎
  wk-comp-id (var x) = cong var (wk-val-id x)
  wk-comp-id (sub W W₁) = sub (wk-comp (wk-cong wk-id) W) (wk-comp wk-id W₁) ≡⟨ cong (λ y → sub y (wk-comp wk-id W₁)) (wk-comp-id W) ⟩ sub W (wk-comp wk-id W₁) ≡⟨ cong (λ y → sub W y) (wk-comp-id W₁) ⟩ sub W W₁ ∎

wk-wk-ε : Wk Γ ε
wk-wk-ε {Γ = ε} = wk-ε
wk-wk-ε {Γ = Γ ∙ X} = wk-wk wk-wk-ε

wk-wk-uniq : (π : Wk Γ ε) → π ≡ wk-wk-ε
wk-wk-uniq wk-ε = refl
wk-wk-uniq (wk-wk π) = cong wk-wk (wk-wk-uniq π)

wk-trans-id : {π : Wk Γ Δ} → wk-trans wk-id π ≡ π
wk-trans-id {π = wk-ε} = refl
wk-trans-id {π = wk-cong π} = cong wk-cong wk-trans-id
wk-trans-id {π = wk-wk π} = cong wk-wk wk-trans-id

wk-trans-id' : {π : Wk Γ Δ} → wk-trans π wk-id ≡ π
wk-trans-id' {π = wk-ε} = refl
wk-trans-id' {π = wk-cong π} = cong wk-cong wk-trans-id'
wk-trans-id' {π = wk-wk π} = cong wk-wk wk-trans-id'

wk-v̲a̲l̲ : Wk Γ Δ → V̲a̲l̲ Δ X → V̲a̲l̲ Γ X
wk-v̲a̲l̲ π (l̲a̲m̲ W) = l̲a̲m̲ ((wk-comp (wk-cong π) W))
wk-v̲a̲l̲ π (pa̲i̲r̲ LHS RHS) = pa̲i̲r̲ (wk-v̲a̲l̲ π LHS) (wk-v̲a̲l̲ π RHS)
wk-v̲a̲l̲ π u̲n̲i̲t̲ = u̲n̲i̲t̲
wk-v̲a̲l̲ π (v̲a̲r̲ i) = v̲a̲r̲ (wk-mem π i)

wk-c̲o̲m̲p : Wk Γ Δ → C̲o̲m̲p Δ X → C̲o̲m̲p Γ X
wk-c̲o̲m̲p π (r̲e̲t̲u̲r̲n̲ M) = r̲e̲t̲u̲r̲n̲ (wk-v̲a̲l̲ π M)
wk-c̲o̲m̲p π (a̲pp M N) = a̲pp (wk-val π M) (wk-v̲a̲l̲ π N)

toVal : V̲a̲l̲ Γ X → Γ ⊢ᵛ X
toVal (l̲a̲m̲ W) = lam W
toVal (pa̲i̲r̲ LHS RHS) = pair (toVal LHS) (toVal RHS)
toVal (u̲n̲i̲t̲) = unit
toVal (v̲a̲r̲ i) = var i

toComp :  C̲o̲m̲p Γ X → Γ ⊢ᶜ X
toComp (r̲e̲t̲u̲r̲n̲ M) = return (toVal M)
toComp (a̲pp M N) = app M (toVal N)

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

wk-c̲o̲m̲p-id : (W : C̲o̲m̲p Γ X) → wk-c̲o̲m̲p wk-id W ≡ W
wk-c̲o̲m̲p-id (r̲e̲t̲u̲r̲n̲ M) = cong r̲e̲t̲u̲r̲n̲ (wk-v̲a̲l̲-id M)
wk-c̲o̲m̲p-id (a̲pp M N) = cong₂ a̲pp (wk-val-id M) (wk-v̲a̲l̲-id N)

wk-prev : Wk (Γ ∙ X) (Δ ∙ Y) → Wk Γ Δ
wk-prev (wk-cong π) = π
wk-prev (wk-wk π) = wk-trans π (wk-wk wk-id)

wk-assoc : {π₁ : Wk Γ Γ'} {π₂ : Wk Γ' Γ''} {π₃ : Wk Γ'' Γ'''} → wk-trans π₁ (wk-trans π₂ π₃) ≡ wk-trans (wk-trans π₁ π₂) π₃
wk-assoc {π₁ = wk-ε} {π₂ = π₂} {π₃ = π₃} = refl
wk-assoc {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {π₃ = wk-cong π₃} = cong wk-cong (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
wk-assoc {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {π₃ = wk-wk π₃} = cong wk-wk (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
wk-assoc {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {π₃ = π₃} = cong wk-wk (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})
wk-assoc {π₁ = wk-wk π₁} {π₂ = π₂} {π₃ = π₃} = cong wk-wk (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})

wk-absurd : Wk Γ (Δ ∙ A) → Wk Δ Γ → ⊥
wk-absurd {Γ = Γ} {Δ = Δ} (wk-cong π) (wk-cong π') = wk-absurd π π'
wk-absurd {Γ = Γ} {Δ = Δ} (wk-cong π) (wk-wk π') = wk-absurd (wk-trans π' (wk-wk π)) wk-id
wk-absurd {Γ = Γ} {Δ = Δ} (wk-wk π) (wk-cong π') = wk-absurd π (wk-wk π')
wk-absurd {Γ = Γ} {Δ = Δ} {A = A} (wk-wk π) (wk-wk π') = wk-absurd π (wk-wk (wk-prev {X = A} (wk-wk π')))

wk-id-id : {π : Wk Γ Γ} → π ≡ wk-id
wk-id-id {π = wk-ε} = refl
wk-id-id {π = wk-cong π} rewrite wk-id-id {π = π} = refl
wk-id-id {π = wk-wk π} = ql (wk-absurd π wk-id) (wk-wk π ≡ wk-id)

wk-merge : (π₁ : Wk Γ Δ) → (π₂ : Wk Γ Δ') → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk Γ Γ' ] Σ[ π₁' ∈ Wk Γ' Δ ] Σ[ π₂' ∈ Wk Γ' Δ' ] ((π₁ ≡ wk-trans π π₁') × (π₂ ≡ wk-trans π π₂'))
wk-merge {Γ = Γ} {Δ = Δ} {Δ' = Δ'} wk-ε wk-ε = ε , wk-ε , wk-ε , wk-ε , refl , refl
wk-merge {Γ = Γ ∙ X} {Δ = Δ ∙ X} {Δ' = Δ' ∙ X} (wk-cong π₁) (wk-cong π₂) =
        let
          w = wk-merge π₁ π₂
          Γ₀ = proj₁ w
          π₀ = proj₁ (proj₂ w)
          eq₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ w))))
          eq₂ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ w))))
        in
        Γ₀ ∙ X , wk-cong π₀ , wk-cong (proj₁ (proj₂ (proj₂ w))) , wk-cong (proj₁ (proj₂ (proj₂ (proj₂ w)))) , cong wk-cong eq₁ , cong wk-cong eq₂
wk-merge {Γ = Γ ∙ X} {Δ = Δ ∙ X} {Δ' = ε} (wk-cong π₁) (wk-wk π₂) =
        let
          w = wk-merge π₁ π₂
          Γ₀ = proj₁ w
          π₀ = proj₁ (proj₂ w)
          eq₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ w))))
          eq₂ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ w))))
        in
        Γ₀ ∙ X , wk-cong π₀ , wk-cong (proj₁ (proj₂ (proj₂ w))) , wk-wk (proj₁ (proj₂ (proj₂ (proj₂ w)))) , cong wk-cong eq₁ , cong wk-wk eq₂
wk-merge {Γ = Γ ∙ X} {Δ = Δ ∙ X} {Δ' = Δ' ∙ x} (wk-cong π₁) (wk-wk π₂) =
        let
          w = wk-merge π₁ π₂
          Γ₀ = proj₁ w
          π₀ = proj₁ (proj₂ w)
          eq₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ w))))
          eq₂ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ w))))
        in
        Γ₀ ∙ X , wk-cong π₀ , wk-cong (proj₁ (proj₂ (proj₂ w))) , wk-wk (proj₁ (proj₂ (proj₂ (proj₂ w)))) , cong wk-cong eq₁ , cong wk-wk eq₂
wk-merge {Γ = Γ ∙ X} {Δ = Δ} {Δ' = Δ' ∙ X} (wk-wk π₁) (wk-cong π₂) =
        let
          w = wk-merge π₁ π₂
          Γ₀ = proj₁ w
          π₀ = proj₁ (proj₂ w)
          eq₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ w))))
          eq₂ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ w))))
        in
        Γ₀ ∙ X , wk-cong π₀ , wk-wk (proj₁ (proj₂ (proj₂ w))) , wk-cong (proj₁ (proj₂ (proj₂ (proj₂ w)))) , cong wk-wk eq₁ , cong wk-cong eq₂
wk-merge {Γ = Γ Cx.∙ X} {Δ = Cx.ε} {Δ' = Cx.ε} (wk-wk π₁) (wk-wk π₂) =
        let
          w = wk-merge π₁ π₂
          Γ₀ = proj₁ w
          π₀ = proj₁ (proj₂ w)
          eq₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ w))))
          eq₂ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ w))))
        in
        Γ₀ , wk-wk π₀ , proj₁ (proj₂ (proj₂ w)) , (proj₁ (proj₂ (proj₂ (proj₂ w)))) , cong wk-wk eq₁ , cong wk-wk eq₂
wk-merge {Γ = Γ Cx.∙ X} {Δ = Cx.ε} {Δ' = Δ' Cx.∙ x} (wk-wk π₁) (wk-wk π₂) =
        let
          w = wk-merge π₁ π₂
          Γ₀ = proj₁ w
          π₀ = proj₁ (proj₂ w)
          eq₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ w))))
          eq₂ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ w))))
        in
        Γ₀ , wk-wk π₀ , proj₁ (proj₂ (proj₂ w)) , proj₁ (proj₂ (proj₂ (proj₂ w))) , cong wk-wk eq₁ , cong wk-wk eq₂
wk-merge {Γ = Γ Cx.∙ X} {Δ = Δ Cx.∙ x} {Δ' = Cx.ε} (wk-wk π₁) (wk-wk π₂) =
        let
          w = wk-merge π₁ π₂
          Γ₀ = proj₁ w
          π₀ = proj₁ (proj₂ w)
          eq₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ w))))
          eq₂ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ w))))
        in
        Γ₀ , wk-wk π₀ , proj₁ (proj₂ (proj₂ w)) , proj₁ (proj₂ (proj₂ (proj₂ w))) , cong wk-wk eq₁ , cong wk-wk eq₂
wk-merge {Γ = Γ Cx.∙ X} {Δ = Δ Cx.∙ x} {Δ' = Δ' Cx.∙ x₁} (wk-wk π₁) (wk-wk π₂) =
        let
          w = wk-merge π₁ π₂
          Γ₀ = proj₁ w
          π₀ = proj₁ (proj₂ w)
          eq₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ w))))
          eq₂ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ w))))
        in
        Γ₀ , wk-wk π₀ , proj₁ (proj₂ (proj₂ w)) , proj₁ (proj₂ (proj₂ (proj₂ w))) , cong wk-wk eq₁ , cong wk-wk eq₂



infix  26 ⭭_
infix  26 ⇡_

data PartialTerm : (Γ : Ctx) → (X : Ty) → Set where

    ⭭_ : V̲a̲l̲ Γ X → PartialTerm Γ X

    ⇡_ : (M : Γ ⊢ᵛ X) → PartialTerm Γ X

    ⇡ᴹ : (M : Γ ⊢ᵛ X `× Y) → (N : (Γ ∙ X ∙ Y) ⊢ᵛ Z) → PartialTerm Γ Z

    ⇡ᴸ : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → PartialTerm Γ (X `× Y)

    ⇡ᴿ  : (LHS : V̲a̲l̲ Γ X) → (RHS : Γ ⊢ᵛ Y) → PartialTerm Γ (X `× Y)

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

wk-wk-trans-id : {Δ Γ : Ctx} → {X Y : Ty} → (π : Wk Δ (Γ ∙ X)) → (i : Γ ∋ Y) → wk-mem (wk-trans π (wk-wk wk-id)) i ≡ wk-mem π (t i)
wk-wk-trans-id (wk-cong (wk-cong π)) Cx.h = refl
wk-wk-trans-id (wk-cong (wk-cong π)) (Cx.t i) = cong (λ x → t (t (wk-mem x i))) wk-trans-id'
wk-wk-trans-id (wk-cong (wk-wk π)) Cx.h = cong (λ x → (t (t (wk-mem x h)))) wk-trans-id'
wk-wk-trans-id (wk-cong (wk-wk π)) (Cx.t i) = cong (λ x → (t (t (wk-mem x (t i))))) wk-trans-id'
wk-wk-trans-id (wk-wk π) Cx.h = cong t (wk-wk-trans-id π h)
wk-wk-trans-id (wk-wk π) (Cx.t i) = cong t (wk-wk-trans-id π (t i))


mutual
  wk-cong-wk-trans : {Δ Γ : Ctx} → (π : Wk Δ (Γ ∙ X)) → (π' : Wk Γ Ψ) → wk-trans (wk-trans π (wk-cong wk-id)) (wk-wk π') ≡ wk-trans π (wk-wk π')
  wk-cong-wk-trans (wk-cong π) wk-ε = wk-trans-id'
  wk-cong-wk-trans (wk-cong π) (wk-cong π') = cong wk-wk (wk-cong-trans π π')
  wk-cong-wk-trans (wk-cong π) (wk-wk π') = cong wk-wk (wk-cong-wk-trans π π')
  wk-cong-wk-trans (wk-wk π) wk-ε = cong wk-wk (wk-cong-wk-trans π wk-ε)
  wk-cong-wk-trans (wk-wk π) (wk-cong π') = cong wk-wk (wk-cong-wk-trans π (wk-cong π'))
  wk-cong-wk-trans (wk-wk π) (wk-wk π') = cong wk-wk (wk-cong-wk-trans π (wk-wk π'))

  wk-cong-trans : {Δ Γ : Ctx} → (π : Wk Δ (Γ ∙ X)) → (π' : Wk Γ Ψ) → wk-trans (wk-trans π (wk-cong wk-id)) (wk-cong π') ≡ wk-trans π (wk-cong π')
  wk-cong-trans (wk-cong π) wk-ε = wk-trans-id'
  wk-cong-trans (wk-cong π) (wk-cong π') = cong wk-cong (wk-cong-trans π π')
  wk-cong-trans (wk-cong π) (wk-wk π') = cong wk-cong (wk-cong-wk-trans π π')
  wk-cong-trans (wk-wk π) wk-ε = wk-trans-id'
  wk-cong-trans (wk-wk π) (wk-cong π') = cong wk-wk (wk-cong-trans π (wk-cong π'))
  wk-cong-trans (wk-wk π) (wk-wk π') = cong wk-wk (wk-cong-trans π (wk-wk π'))

  wk-wk-trans : {Δ Γ : Ctx} → (π : Wk Δ (Γ ∙ X)) → (π' : Wk Γ Ψ) → wk-trans (wk-trans π (wk-wk wk-id)) π' ≡ wk-trans π (wk-wk π')
  wk-wk-trans (wk-cong π) wk-ε = cong wk-wk wk-trans-id'
  wk-wk-trans (wk-cong π) (wk-cong π') = cong wk-wk (wk-cong-trans π π')
  wk-wk-trans (wk-cong π) (wk-wk π') = cong wk-wk (wk-cong-wk-trans π π')
  wk-wk-trans (wk-wk π) wk-ε = cong wk-wk (wk-wk-trans π wk-ε)
  wk-wk-trans (wk-wk π) (wk-cong π') = cong wk-wk (wk-wk-trans π (wk-cong π'))
  wk-wk-trans (wk-wk π) (wk-wk π') = cong wk-wk (wk-wk-trans π (wk-wk π'))

t-injective : {i i' : Γ ∋ X} → t {B = B} i ≡ t i' → i ≡ i'
t-injective refl = refl
