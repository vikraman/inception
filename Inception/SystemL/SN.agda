module Inception.SystemL.SN where

open import Data.Empty using (⊥)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym)
open Eq.≡-Reasoning

open import Inception.SystemL.Syntax

--------------------------------------------------------------------------
-- step relation on commands

infix 5 _↦_

data _↦_ {Γ Δ : Ctx} : Γ ⊢ Δ → Γ ⊢ Δ → Set where

  μ-step   : {A : Ty} {M : Γ ⊢ (Δ ∙ A)} {C : Γ ∣ A ⊢ᵏ Δ}
           → cut A (μ M) C ↦ letc C M

  μ̃-step   : {A : Ty} {V : Γ ⊢ᵛ A ∣ Δ} {M : (Γ ∙ A) ⊢ Δ}
           → cut A (ret V) (μ̃ M) ↦ letvc V M

  app-step : {A B : Ty} {M : (Γ ∙ A) ⊢ᵗ B ∣ Δ} {V : Γ ⊢ᵛ A ∣ Δ} {C : Γ ∣ B ⊢ᵏ Δ}
           → cut (A `⇒ B) (ret (lam M)) (app V C) ↦ cut B (letv V M) C

  fst-step : {A B : Ty} {V : Γ ⊢ᵛ A ∣ Δ} {W : Γ ⊢ᵛ B ∣ Δ} {C : Γ ∣ A ⊢ᵏ Δ}
           → cut (A `× B) (ret (pair V W)) (fst C) ↦ cut A (ret V) C

  snd-step : {A B : Ty} {V : Γ ⊢ᵛ A ∣ Δ} {W : Γ ⊢ᵛ B ∣ Δ} {C : Γ ∣ B ⊢ᵏ Δ}
           → cut (A `× B) (ret (pair V W)) (snd C) ↦ cut B (ret W) C

  inl-step : {A B : Ty} {V : Γ ⊢ᵛ A ∣ Δ} {C1 : Γ ∣ A ⊢ᵏ Δ} {C2 : Γ ∣ B ⊢ᵏ Δ}
           → cut (A `+ B) (ret (inl V)) (case C1 C2) ↦ cut A (ret V) C1

  inr-step : {A B : Ty} {W : Γ ⊢ᵛ B ∣ Δ} {C1 : Γ ∣ A ⊢ᵏ Δ} {C2 : Γ ∣ B ⊢ᵏ Δ}
           → cut (A `+ B) (ret (inr W)) (case C1 C2) ↦ cut B (ret W) C2

--------------------------------------------------------------------------
-- accessibility

data SN {Γ Δ} (M : Γ ⊢ Δ) : Set where
  sn : (∀ {M1} → M ↦ M1 → SN M1) → SN M

--------------------------------------------------------------------------
-- reducibility candidates

Redᵛ  : (A : Ty) {Γ Δ : Ctx} → Γ ⊢ᵛ A ∣ Δ → Set
CoRedᵏ : (A : Ty) {Γ Δ : Ctx} → Γ ∣ A ⊢ᵏ Δ → Set

Redᵛ `⊥        V              = ⊤
Redᵛ `Unit     V              = ⊤
Redᵛ `P       V              = ⊤
Redᵛ (A `× B)  (var i)        = ⊤
Redᵛ (A `× B)  (pair V W)     = Redᵛ A V × Redᵛ B W
Redᵛ (A `+ B)  (var i)        = ⊤
Redᵛ (A `+ B)  (inl V)        = Redᵛ A V
Redᵛ (A `+ B)  (inr W)        = Redᵛ B W
Redᵛ (A `⇒ B)  (var i)        = ⊤
Redᵛ (A `⇒ B) {Γ} {Δ} (lam M) =
  ∀ {Γ' Δ'} (π : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) {W : Γ' ⊢ᵛ A ∣ Δ'} {C : Γ' ∣ B ⊢ᵏ Δ'}
  → Redᵛ A W → CoRedᵏ B C → SN (cut B (letv W (wk-tm (wk-cong π) σ M)) C)

CoRedᵏ A         (covar i)    = ⊤
CoRedᵏ A {Γ} {Δ} (μ̃ M)       =
  ∀ {Γ' Δ'} (π : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) {V : Γ' ⊢ᵛ A ∣ Δ'}
  → Redᵛ A V → SN (sub-cmd (sub-ex sub-id V) cosub-id (wk-cmd (wk-cong π) σ M))
CoRedᵏ `⊥        tp           = ⊤
CoRedᵏ (A `× B)  (fst C)      = CoRedᵏ A C
CoRedᵏ (A `× B)  (snd C)      = CoRedᵏ B C
CoRedᵏ (A `+ B)  (case C1 C2) = CoRedᵏ A C1 × CoRedᵏ B C2
CoRedᵏ (A `⇒ B)  (app V C)    = Redᵛ A V × CoRedᵏ B C

--------------------------------------------------------------------------
-- weakening preserves reducibility

Red-wk : (A : Ty) {Γ Δ Γ' Δ' : Ctx} (π : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) {V : Γ ⊢ᵛ A ∣ Δ}
       → Redᵛ A V → Redᵛ A (wk-val π σ V)
Red-wk `⊥        π σ r = tt
Red-wk `Unit     π σ r = tt
Red-wk `P       π σ r = tt
Red-wk (A `× B) π σ {V = var i}    r        = tt
Red-wk (A `× B) π σ {V = pair V W} (rv , rw) = Red-wk A π σ rv , Red-wk B π σ rw
Red-wk (A `+ B) π σ {V = var i}  r  = tt
Red-wk (A `+ B) π σ {V = inl V}  rv = Red-wk A π σ rv
Red-wk (A `+ B) π σ {V = inr W}  rw = Red-wk B π σ rw
Red-wk (A `⇒ B) π σ {V = var i}  r = tt
Red-wk (A `⇒ B) {Γ} {Δ} π σ {V = lam M} f =
  λ π' σ' {W} {C} rw rc →
    Eq.subst (λ x → SN (cut B (letv W x) C)) (sym (wk-tm-trans M (wk-cong π') (wk-cong π) σ' σ)) (f (wk-trans π' π) (wk-trans σ' σ) rw rc)

CoRed-wk : (A : Ty) {Γ Δ Γ' Δ' : Ctx} (π : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) {C : Γ ∣ A ⊢ᵏ Δ}
         → CoRedᵏ A C → CoRedᵏ A (wk-cotm π σ C)
CoRed-wk A             π σ {C = covar i}   r  = tt
CoRed-wk `⊥            π σ {C = tp}        r  = tt
CoRed-wk (A `× B)      π σ {C = fst C}     r  = CoRed-wk A π σ {C = C} r
CoRed-wk (A `× B)      π σ {C = snd C}     r  = CoRed-wk B π σ {C = C} r
CoRed-wk (A `+ B)      π σ {C = case C1 C2} (r1 , r2) = CoRed-wk A π σ {C = C1} r1 , CoRed-wk B π σ {C = C2} r2
CoRed-wk (A `⇒ B)      π σ {C = app V C}   (rv , rc)  = Red-wk A π σ rv , CoRed-wk B π σ {C = C} rc
CoRed-wk A {Γ} {Δ} π σ {C = μ̃ M} f =
  λ π' σ' {V} rv →
    Eq.subst (λ x → SN (sub-cmd (sub-ex sub-id V) cosub-id x)) (sym (wk-cmd-trans M (wk-cong π') (wk-cong π) σ' σ)) (f (wk-trans π' π) (wk-trans σ' σ) rv)

--------------------------------------------------------------------------
-- orthogonality

Ortho-μ̃ : {A : Ty} {Γ Δ : Ctx} {V : Γ ⊢ᵛ A ∣ Δ} {M : (Γ ∙ A) ⊢ Δ}
        → Redᵛ A V → CoRedᵏ A (μ̃ M) → SN (cut A (ret V) (μ̃ M))
Ortho-μ̃ {V = V} {M} rv rc =
  sn (λ { μ̃-step → Eq.subst SN (cong (sub-cmd (sub-ex sub-id V) cosub-id) (wk-cmd-id M)) (rc wk-id wk-id rv) })

Ortho : {A : Ty} {Γ Δ : Ctx} {V : Γ ⊢ᵛ A ∣ Δ} {C : Γ ∣ A ⊢ᵏ Δ}
      → Redᵛ A V → CoRedᵏ A C → SN (cut A (ret V) C)
Ortho {A} {V = var i} {C = covar j} rv rc = sn λ ()
Ortho {`⊥} {V = var i} {C = μ̃ M} rv rc = Ortho-μ̃ rv rc
Ortho {`⊥} {V = var i} {C = tp} rv rc = sn λ ()
Ortho {`Unit} {V = var i} {C = μ̃ M} rv rc = Ortho-μ̃ rv rc
Ortho {`Unit} {V = unit} {C = covar i} rv rc = sn λ ()
Ortho {`Unit} {V = unit} {C = μ̃ M} rv rc = Ortho-μ̃ rv rc
Ortho {`P} {V = var i} {C = μ̃ M} rv rc = Ortho-μ̃ rv rc
Ortho {A `× B} {V = var i} {C = fst C} rv rc = sn λ ()
Ortho {A `× B} {V = var i} {C = snd C} rv rc = sn λ ()
Ortho {A `× B} {V = var i} {C = μ̃ M} rv rc = Ortho-μ̃ rv rc
Ortho {A `× B} {V = pair V W} {C = covar i} rv rc = sn λ ()
Ortho {A `× B} {V = pair V W} {C = fst C} (rv , rw) rc = sn λ { fst-step → Ortho rv rc }
Ortho {A `× B} {V = pair V W} {C = snd C} (rv , rw) rc = sn λ { snd-step → Ortho rw rc }
Ortho {A `× B} {V = pair V W} {C = μ̃ M} rv rc = Ortho-μ̃ rv rc
Ortho {A `⇒ B} {V = var i} {C = app W C} rv rc = sn λ ()
Ortho {A `⇒ B} {V = var i} {C = μ̃ M} rv rc = Ortho-μ̃ rv rc
Ortho {A `⇒ B} {V = lam M} {C = covar i} rv rc = sn λ ()
Ortho {A `⇒ B} {V = lam M} {C = app W C} rv (rw , rc) =
  sn λ { app-step → Eq.subst (λ x → SN (cut B (letv W x) C)) (wk-tm-id M) (rv wk-id wk-id rw rc) }
Ortho {A `⇒ B} {V = lam M} {C = μ̃ N} rv rc = Ortho-μ̃ rv rc
Ortho {A `+ B} {V = var i} {C = case C1 C2} rv rc = sn λ ()
Ortho {A `+ B} {V = var i} {C = μ̃ M} rv rc = Ortho-μ̃ rv rc
Ortho {A `+ B} {V = inl V} {C = covar i} rv rc = sn λ ()
Ortho {A `+ B} {V = inl V} {C = case C1 C2} rv (ra , rb) = sn λ { inl-step → Ortho rv ra }
Ortho {A `+ B} {V = inl V} {C = μ̃ M} rv rc = Ortho-μ̃ rv rc
Ortho {A `+ B} {V = inr V} {C = covar i} rv rc = sn λ ()
Ortho {A `+ B} {V = inr V} {C = case C1 C2} rv (ra , rb) = sn λ { inr-step → Ortho rv rb }
Ortho {A `+ B} {V = inr V} {C = μ̃ M} rv rc = Ortho-μ̃ rv rc

--------------------------------------------------------------------------
-- fundamental lemma

record RedSub {Γ Δ Γ' : Ctx} (θ : Sub Γ Δ Γ') : Set where
  field red : {A : Ty} (i : Γ' ∋ A) → Redᵛ A (sub-mem θ i)
open RedSub

record CoRedSub {Γ Δ Δ' : Ctx} (φ : CoSub Γ Δ Δ') : Set where
  field cored : {A : Ty} (i : Δ' ∋ A) → CoRedᵏ A (cosub-mem φ i)
open CoRedSub

RedSub-wk : {Γ Δ Γ' Δ' Γ'' : Ctx} (π : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) {θ : Sub Γ Δ Γ''} → RedSub θ → RedSub (sub-wk π σ θ)
RedSub-wk π σ {θ} rθ .red {A} i = Eq.subst (Redᵛ A) (sym (sub-mem-wk π σ θ i)) (Red-wk A π σ (rθ .red i))

CoRedSub-wk : {Γ Δ Γ' Δ' Δ'' : Ctx} (π : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) {φ : CoSub Γ Δ Δ''} → CoRedSub φ → CoRedSub (cosub-wk π σ φ)
CoRedSub-wk π σ {φ} rφ .cored {A} i = Eq.subst (CoRedᵏ A) (sym (cosub-mem-wk π σ φ i)) (CoRed-wk A π σ {C = cosub-mem φ i} (rφ .cored i))

RedSub-ext : {Γ Δ Γ' : Ctx} {A : Ty} {θ : Sub Γ Δ Γ'} {V : Γ ⊢ᵛ A ∣ Δ} → RedSub θ → Redᵛ A V → RedSub (sub-ex θ V)
RedSub-ext rθ rv .red z = rv
RedSub-ext rθ rv .red (s i) = rθ .red i

CoRedSub-ext : {Γ Δ Δ' : Ctx} {A : Ty} {φ : CoSub Γ Δ Δ'} {C : Γ ∣ A ⊢ᵏ Δ} → CoRedSub φ → CoRedᵏ A C → CoRedSub (cosub-ex φ C)
CoRedSub-ext rφ rc .cored z = rc
CoRedSub-ext rφ rc .cored (s i) = rφ .cored i

Fundamental-cmd : {Γ Δ Γ' Δ' : Ctx} (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ')
                → RedSub θ → CoRedSub φ → (M : Γ' ⊢ Δ') → SN (sub-cmd θ φ M)
Fundamental-val : {Γ Δ Γ' Δ' : Ctx} {A : Ty} (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ')
                → RedSub θ → CoRedSub φ → (V : Γ' ⊢ᵛ A ∣ Δ') → Redᵛ A (sub-val θ φ V)
Fundamental-tm  : {Γ Δ Γ' Δ' : Ctx} {A : Ty} (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ')
                → RedSub θ → CoRedSub φ → (M : Γ' ⊢ᵗ A ∣ Δ') → ∀ {C : Γ ∣ A ⊢ᵏ Δ} → CoRedᵏ A C → SN (cut A (sub-tm θ φ M) C)
Fundamental-cotm : {Γ Δ Γ' Δ' : Ctx} {A : Ty} (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ')
                → RedSub θ → CoRedSub φ → (C : Γ' ∣ A ⊢ᵏ Δ') → CoRedᵏ A (sub-cotm θ φ C)

Fundamental-cmd θ φ rθ rφ (cut A M C) = Fundamental-tm θ φ rθ rφ M (Fundamental-cotm θ φ rθ rφ C)

Fundamental-val θ φ rθ rφ (var i)    = rθ .red i
Fundamental-val θ φ rθ rφ (lam M)    =
  λ π σ {W} {C} rw rc →
    Eq.subst (λ x → SN (cut _ x C)) (sym (fund-lam-eq θ φ π σ W M))
             (Fundamental-tm (sub-ex (sub-wk π σ θ) W) (cosub-wk π σ φ) (RedSub-ext (RedSub-wk π σ rθ) rw) (CoRedSub-wk π σ rφ) M rc)
Fundamental-val θ φ rθ rφ unit       = tt
Fundamental-val θ φ rθ rφ (pair V W) = Fundamental-val θ φ rθ rφ V , Fundamental-val θ φ rθ rφ W
Fundamental-val θ φ rθ rφ (inl V)    = Fundamental-val θ φ rθ rφ V
Fundamental-val θ φ rθ rφ (inr W)    = Fundamental-val θ φ rθ rφ W

Fundamental-tm θ φ rθ rφ (ret V) rc = Ortho (Fundamental-val θ φ rθ rφ V) rc
Fundamental-tm θ φ rθ rφ (μ M)   {C} rc =
  sn (λ { μ-step → Eq.subst SN (sym (fund-mu-eq θ φ C M)) (Fundamental-cmd θ (cosub-ex φ C) rθ (CoRedSub-ext rφ rc) M) })

Fundamental-cotm θ φ rθ rφ (covar i)   = rφ .cored i
Fundamental-cotm θ φ rθ rφ (app V C)   = Fundamental-val θ φ rθ rφ V , Fundamental-cotm θ φ rθ rφ C
Fundamental-cotm θ φ rθ rφ (fst C)     = Fundamental-cotm θ φ rθ rφ C
Fundamental-cotm θ φ rθ rφ (snd C)     = Fundamental-cotm θ φ rθ rφ C
Fundamental-cotm θ φ rθ rφ (case C1 C2) = Fundamental-cotm θ φ rθ rφ C1 , Fundamental-cotm θ φ rθ rφ C2
Fundamental-cotm θ φ rθ rφ (μ̃ M)       =
  λ π σ {V} rv →
    Eq.subst SN (sym (fund-mut-wk-eq θ φ π σ V M))
             (Fundamental-cmd (sub-ex (sub-wk π σ θ) V) (cosub-wk π σ φ) (RedSub-ext (RedSub-wk π σ rθ) rv) (CoRedSub-wk π σ rφ) M)
Fundamental-cotm θ φ rθ rφ tp          = tt

Red-var-triv : (A : Ty) {Γ : Ctx} (Δ : Ctx) (i : Γ ∋ A) → Redᵛ A (var {Δ = Δ} i)
Red-var-triv `⊥        Δ i = tt
Red-var-triv `Unit     Δ i = tt
Red-var-triv `P       Δ i = tt
Red-var-triv (A `× B)  Δ i = tt
Red-var-triv (A `+ B)  Δ i = tt
Red-var-triv (A `⇒ B)  Δ i = tt

RedSub-id : {Γ Δ : Ctx} → RedSub (sub-id {Γ} {Δ})
RedSub-id {Γ} {Δ} .red {A} i = Eq.subst (Redᵛ A) (sym (sub-mem-id i)) (Red-var-triv A Δ i)

CoRedSub-id : {Γ Δ : Ctx} → CoRedSub (cosub-id {Γ} {Δ})
CoRedSub-id {Γ} {Δ} .cored {A} i = Eq.subst (CoRedᵏ A) (sym (cosub-mem-id i)) tt

SN-theorem : {Γ Δ : Ctx} (M : Γ ⊢ Δ) → SN M
SN-theorem {Γ} {Δ} M = Eq.subst SN (sub-cmd-id M) (Fundamental-cmd sub-id cosub-id RedSub-id CoRedSub-id M)

--------------------------------------------------------------------------
-- eval

open import Inception.Prelude
open Inception.Prelude.RTC

_↦*_ : {Γ Δ : Ctx} -> Γ ⊢ Δ -> Γ ⊢ Δ -> Set
_↦*_ {Γ} {Δ} = _~>*_ (_↦_ {Γ = Γ} {Δ = Δ})

Normal : {Γ Δ : Ctx} → Γ ⊢ Δ → Set
Normal M = ∀ {N} → M ↦ N → ⊥

data Step? {Γ Δ : Ctx} (M : Γ ⊢ Δ) : Set where
  done : Normal M → Step? M
  next : {N : Γ ⊢ Δ} → M ↦ N → Step? M

step? : {Γ Δ : Ctx} (M : Γ ⊢ Δ) → Step? M
step? (cut A (μ M) C) = next μ-step

step? (cut A (ret (var i)) (covar j))       = done (λ ())
step? (cut A (ret (var i)) (μ̃ M))           = next μ̃-step
step? (cut `⊥ (ret (var i)) tp)             = done (λ ())
step? (cut (A `× B) (ret (var i)) (fst C))  = done (λ ())
step? (cut (A `× B) (ret (var i)) (snd C))  = done (λ ())
step? (cut (A `+ B) (ret (var i)) (case C1 C2)) = done (λ ())
step? (cut (A `⇒ B) (ret (var i)) (app V C))    = done (λ ())

step? (cut `Unit (ret unit) (covar j)) = done (λ ())
step? (cut `Unit (ret unit) (μ̃ M))     = next μ̃-step

step? (cut (A `× B) (ret (pair V W)) (covar j)) = done (λ ())
step? (cut (A `× B) (ret (pair V W)) (fst C))   = next fst-step
step? (cut (A `× B) (ret (pair V W)) (snd C))   = next snd-step
step? (cut (A `× B) (ret (pair V W)) (μ̃ M))     = next μ̃-step

step? (cut (A `+ B) (ret (inl V)) (covar j))      = done (λ ())
step? (cut (A `+ B) (ret (inl V)) (case C1 C2))   = next inl-step
step? (cut (A `+ B) (ret (inl V)) (μ̃ M))          = next μ̃-step
step? (cut (A `+ B) (ret (inr W)) (covar j))      = done (λ ())
step? (cut (A `+ B) (ret (inr W)) (case C1 C2))   = next inr-step
step? (cut (A `+ B) (ret (inr W)) (μ̃ M))          = next μ̃-step

step? (cut (A `⇒ B) (ret (lam M)) (covar j)) = done (λ ())
step? (cut (A `⇒ B) (ret (lam M)) (app V C)) = next app-step
step? (cut (A `⇒ B) (ret (lam M)) (μ̃ M'))     = next μ̃-step

eval-acc : {Γ Δ : Ctx} {M : Γ ⊢ Δ} → SN M → Σ[ N ∈ Γ ⊢ Δ ] (M ↦* N) × Normal N
eval-acc {M = M} (sn f) with step? M
... | done normal = M , M ◼ , normal
... | next {N} step with eval-acc (f step)
... | (P , chain , normal) = P , M ~>⟨ step ⟩ chain , normal

eval : {Γ Δ : Ctx} (M : Γ ⊢ Δ) → Σ[ N ∈ Γ ⊢ Δ ] (M ↦* N) × Normal N
eval M = eval-acc (SN-theorem M)
