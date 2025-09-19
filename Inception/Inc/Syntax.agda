module Inception.Inc.Syntax where

open import Data.Nat

infixr 40 _`×_
infixr 25 _`⇒_

data Ty : Set where
  `Unit : Ty
  _`×_ _`⇒_ : Ty -> Ty -> Ty
  `V `P : Ty

module Cx (Ty : Set) where

  infixl 15 _∙_
  infix 10 _∋_

  data Ctx : Set where
    ε : Ctx
    _∙_ : Ctx -> Ty -> Ctx

  variable
    A B C D : Ty
    Γ Δ Ψ : Ctx

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

  rec : Γ ⊢ᵛ `V -> Γ ⊢ᵛ `P
      -----------------------
      -> Γ ⊢ᶜ A

  inc : (Γ ∙ `V) ⊢ᶜ A -> (Γ ∙ `P) ⊢ᶜ A
      -----------------------------------
      -> Γ ⊢ᶜ A

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
  wk-comp π (rec V W)      = rec (wk-val π V) (wk-val π W)
  wk-comp π (inc M N)      = inc (wk-comp (wk-cong π) M) (wk-comp (wk-cong π) N)

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
  sub-comp θ (rec V W) = rec (sub-val θ V) (sub-val θ W)
  sub-comp θ (inc M N) = inc (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) M) (sub-comp (sub-ex (sub-wk (wk-wk wk-id) θ) (var h)) N)

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
  n : ℕ
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

  rec-cong : Γ ⊢ᵛ V1 ≈ V2 ∶ `V -> Γ ⊢ᵛ W1 ≈ W2 ∶ `P
            ----------------------------------------
            -> Γ ⊢ᶜ rec V1 W1 ≈ rec V2 W2 ∶ A

  inc-cong : (Γ ∙ `V) ⊢ᶜ M1 ≈ M2 ∶ A -> (Γ ∙ `P) ⊢ᶜ N1 ≈ N2 ∶ A
            ----------------------------------------------------
            -> Γ ⊢ᶜ inc M1 N1 ≈ inc M2 N2 ∶ A

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

  -- rec/inc rules

  inc-weak : (M : Γ ⊢ᶜ A) -> (N : (Γ ∙ `P) ⊢ᶜ A)
           ------------------------------------------------
           -> Γ ⊢ᶜ inc (wk-comp (wk-wk wk-id) M) N ≈ M ∶ A

  inc-subst : (M : (Γ ∙ `P) ⊢ᶜ A) -> (V : Γ ⊢ᵛ `P)
            -----------------------------------------------------------------------
            -> Γ ⊢ᶜ inc (rec (var h) (wk V)) M ≈ sub-comp (sub-ex sub-id V) M ∶ A

  inc-ext : (M : (Γ ∙ `V) ⊢ᶜ A) -> (V : Γ ⊢ᵛ `V)
          ----------------------------------------------------------------------------------------
          -> Γ ⊢ᶜ inc (sub-comp sub-id M) (rec (wk V) (var h)) ≈ sub-comp (sub-ex sub-id V) M ∶ A

  inc-assoc : (L : (Γ ∙ `V ∙ `V) ⊢ᶜ A) -> (M : (Γ ∙ `V ∙ `P) ⊢ᶜ A) -> (N : (Γ ∙ `P) ⊢ᶜ A)
            ------------------------------------------------------------------------------------------------------------------------------------------------------------
            -> Γ ⊢ᶜ inc (inc L M) N ≈ inc (inc (sub-comp exchg L) (wk-comp (wk-cong (wk-wk wk-id)) N)) (inc (sub-comp exchg M) (wk-comp (wk-cong (wk-wk wk-id)) N)) ∶ A

  -- algebraicity rules

  rec-push : (V : Γ ⊢ᵛ `V) -> (W : Γ ⊢ᵛ `P) -> (M : (Γ ∙ `V) ⊢ᶜ A)
           --------------------------------------------------------
           -> Γ ⊢ᶜ push (rec V W) M ≈ rec V W ∶ A

  inc-push : (M : (Γ ∙ `V) ⊢ᶜ A) -> (N : (Γ ∙ `P) ⊢ᶜ A) -> (L : (Γ ∙ A) ⊢ᶜ B)
           -------------------------------------------------------------------------------------------------------------------------------
           -> Γ ⊢ᶜ push (inc M N) L ≈ inc (push M (wk-comp (wk-cong (wk-wk wk-id)) L)) (push N (wk-comp (wk-cong (wk-wk wk-id)) L)) ∶ B
