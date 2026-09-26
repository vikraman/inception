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

  μ-step   : {A : Ty} {M : Γ ⊢ (Δ ∙ A)} {K : Γ ∣ A ⊢ᵏ Δ}
           → cut A (μ M) K ↦ letc K M

  μ̃-step   : {A : Ty} {V : Γ ⊢ᵛ A ∣ Δ} {M : (Γ ∙ A) ⊢ Δ}
           → cut A (ret V) (μ̃ M) ↦ letvc V M

  app-step : {A B : Ty} {M : (Γ ∙ A) ⊢ᵗ B ∣ Δ} {V : Γ ⊢ᵛ A ∣ Δ} {K : Γ ∣ B ⊢ᵏ Δ}
           → cut (A `⇒ B) (ret (lam M)) (app V K) ↦ cut B (letv V M) K

  fst-step : {A B : Ty} {V : Γ ⊢ᵛ A ∣ Δ} {W : Γ ⊢ᵛ B ∣ Δ} {K : Γ ∣ A ⊢ᵏ Δ}
           → cut (A `× B) (ret (pair V W)) (fst K) ↦ cut A (ret V) K

  snd-step : {A B : Ty} {V : Γ ⊢ᵛ A ∣ Δ} {W : Γ ⊢ᵛ B ∣ Δ} {K : Γ ∣ B ⊢ᵏ Δ}
           → cut (A `× B) (ret (pair V W)) (snd K) ↦ cut B (ret W) K

  inl-step : {A B : Ty} {V : Γ ⊢ᵛ A ∣ Δ} {K : Γ ∣ A ⊢ᵏ Δ} {L : Γ ∣ B ⊢ᵏ Δ}
           → cut (A `+ B) (ret (inl V)) (case K L) ↦ cut A (ret V) K

  inr-step : {A B : Ty} {W : Γ ⊢ᵛ B ∣ Δ} {K : Γ ∣ A ⊢ᵏ Δ} {L : Γ ∣ B ⊢ᵏ Δ}
           → cut (A `+ B) (ret (inr W)) (case K L) ↦ cut B (ret W) L

--------------------------------------------------------------------------
-- accessibility

data SN {Γ Δ} (M : Γ ⊢ Δ) : Set where
  sn : (∀ {N} → M ↦ N → SN N) → SN M

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
  ∀ {Γ₁ Δ₁} (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) {W : Γ₁ ⊢ᵛ A ∣ Δ₁} {K : Γ₁ ∣ B ⊢ᵏ Δ₁}
  → Redᵛ A W → CoRedᵏ B K → SN (cut B (letv W (wk-tm (wk-cong π) ρ M)) K)

CoRedᵏ A         (covar i)    = ⊤
CoRedᵏ A {Γ} {Δ} (μ̃ M)       =
  ∀ {Γ₁ Δ₁} (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) {V : Γ₁ ⊢ᵛ A ∣ Δ₁}
  → Redᵛ A V → SN (sub-cmd (sub-ex sub-id V) cosub-id (wk-cmd (wk-cong π) ρ M))
CoRedᵏ `⊥        tp         = ⊤
CoRedᵏ (A `× B)  (fst K)    = CoRedᵏ A K
CoRedᵏ (A `× B)  (snd K)    = CoRedᵏ B K
CoRedᵏ (A `+ B)  (case K L) = CoRedᵏ A K × CoRedᵏ B L
CoRedᵏ (A `⇒ B)  (app V K)  = Redᵛ A V × CoRedᵏ B K

--------------------------------------------------------------------------
-- weakening preserves reducibility

Red-wk : (A : Ty) {Γ Δ Γ₁ Δ₁ : Ctx} (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) {V : Γ ⊢ᵛ A ∣ Δ}
       → Redᵛ A V → Redᵛ A (wk-val π ρ V)
Red-wk `⊥        π ρ r = tt
Red-wk `Unit     π ρ r = tt
Red-wk `P       π ρ r = tt
Red-wk (A `× B) π ρ {V = var i}    r        = tt
Red-wk (A `× B) π ρ {V = pair V W} (rv , rw) = Red-wk A π ρ rv , Red-wk B π ρ rw
Red-wk (A `+ B) π ρ {V = var i}  r  = tt
Red-wk (A `+ B) π ρ {V = inl V}  rv = Red-wk A π ρ rv
Red-wk (A `+ B) π ρ {V = inr W}  rw = Red-wk B π ρ rw
Red-wk (A `⇒ B) π ρ {V = var i}  r = tt
Red-wk (A `⇒ B) {Γ} {Δ} π ρ {V = lam M} f =
  λ π₁ σ {W} {K} rw rk →
    Eq.subst (λ x → SN (cut B (letv W x) K)) (sym (wk-tm-trans M (wk-cong π₁) (wk-cong π) σ ρ)) (f (wk-trans π₁ π) (wk-trans σ ρ) rw rk)

CoRed-wk : (A : Ty) {Γ Δ Γ₁ Δ₁ : Ctx} (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) {K : Γ ∣ A ⊢ᵏ Δ}
         → CoRedᵏ A K → CoRedᵏ A (wk-cotm π ρ K)
CoRed-wk A             π ρ {K = covar i}   r  = tt
CoRed-wk `⊥            π ρ {K = tp}        r  = tt
CoRed-wk (A `× B)      π ρ {K = fst K}     r  = CoRed-wk A π ρ {K = K} r
CoRed-wk (A `× B)      π ρ {K = snd K}     r  = CoRed-wk B π ρ {K = K} r
CoRed-wk (A `+ B)      π ρ {K = case K L} (r₁ , r₂) = CoRed-wk A π ρ {K = K} r₁ , CoRed-wk B π ρ {K = L} r₂
CoRed-wk (A `⇒ B)      π ρ {K = app V K}   (rv , rk)  = Red-wk A π ρ rv , CoRed-wk B π ρ {K = K} rk
CoRed-wk A {Γ} {Δ} π ρ {K = μ̃ M} f =
  λ π₁ σ {V} rv →
    Eq.subst (λ x → SN (sub-cmd (sub-ex sub-id V) cosub-id x)) (sym (wk-cmd-trans M (wk-cong π₁) (wk-cong π) σ ρ)) (f (wk-trans π₁ π) (wk-trans σ ρ) rv)

--------------------------------------------------------------------------
-- orthogonality

Ortho-μ̃ : {A : Ty} {Γ Δ : Ctx} {V : Γ ⊢ᵛ A ∣ Δ} {M : (Γ ∙ A) ⊢ Δ}
        → Redᵛ A V → CoRedᵏ A (μ̃ M) → SN (cut A (ret V) (μ̃ M))
Ortho-μ̃ {V = V} {M} rv rk =
  sn (λ { μ̃-step → Eq.subst SN (cong (sub-cmd (sub-ex sub-id V) cosub-id) (wk-cmd-id M)) (rk wk-id wk-id rv) })

Ortho : {A : Ty} {Γ Δ : Ctx} {V : Γ ⊢ᵛ A ∣ Δ} {K : Γ ∣ A ⊢ᵏ Δ}
      → Redᵛ A V → CoRedᵏ A K → SN (cut A (ret V) K)
Ortho {A} {V = var i} {K = covar j} rv rk = sn λ ()
Ortho {`⊥} {V = var i} {K = μ̃ M} rv rk = Ortho-μ̃ rv rk
Ortho {`⊥} {V = var i} {K = tp} rv rk = sn λ ()
Ortho {`Unit} {V = var i} {K = μ̃ M} rv rk = Ortho-μ̃ rv rk
Ortho {`Unit} {V = unit} {K = covar i} rv rk = sn λ ()
Ortho {`Unit} {V = unit} {K = μ̃ M} rv rk = Ortho-μ̃ rv rk
Ortho {`P} {V = var i} {K = μ̃ M} rv rk = Ortho-μ̃ rv rk
Ortho {A `× B} {V = var i} {K = fst K} rv rk = sn λ ()
Ortho {A `× B} {V = var i} {K = snd K} rv rk = sn λ ()
Ortho {A `× B} {V = var i} {K = μ̃ M} rv rk = Ortho-μ̃ rv rk
Ortho {A `× B} {V = pair V W} {K = covar i} rv rk = sn λ ()
Ortho {A `× B} {V = pair V W} {K = fst K} (rv , rw) rk = sn λ { fst-step → Ortho rv rk }
Ortho {A `× B} {V = pair V W} {K = snd K} (rv , rw) rk = sn λ { snd-step → Ortho rw rk }
Ortho {A `× B} {V = pair V W} {K = μ̃ M} rv rk = Ortho-μ̃ rv rk
Ortho {A `⇒ B} {V = var i} {K = app W K} rv rk = sn λ ()
Ortho {A `⇒ B} {V = var i} {K = μ̃ M} rv rk = Ortho-μ̃ rv rk
Ortho {A `⇒ B} {V = lam M} {K = covar i} rv rk = sn λ ()
Ortho {A `⇒ B} {V = lam M} {K = app W K} rv (rw , rk) =
  sn λ { app-step → Eq.subst (λ x → SN (cut B (letv W x) K)) (wk-tm-id M) (rv wk-id wk-id rw rk) }
Ortho {A `⇒ B} {V = lam M} {K = μ̃ N} rv rk = Ortho-μ̃ rv rk
Ortho {A `+ B} {V = var i} {K = case K L} rv rk = sn λ ()
Ortho {A `+ B} {V = var i} {K = μ̃ M} rv rk = Ortho-μ̃ rv rk
Ortho {A `+ B} {V = inl V} {K = covar i} rv rk = sn λ ()
Ortho {A `+ B} {V = inl V} {K = case K L} rv (ra , rb) = sn λ { inl-step → Ortho rv ra }
Ortho {A `+ B} {V = inl V} {K = μ̃ M} rv rk = Ortho-μ̃ rv rk
Ortho {A `+ B} {V = inr V} {K = covar i} rv rk = sn λ ()
Ortho {A `+ B} {V = inr V} {K = case K L} rv (ra , rb) = sn λ { inr-step → Ortho rv rb }
Ortho {A `+ B} {V = inr V} {K = μ̃ M} rv rk = Ortho-μ̃ rv rk

--------------------------------------------------------------------------
-- fundamental lemma

record RedSub {Γ Δ Γ₁ : Ctx} (θ : Sub Γ Δ Γ₁) : Set where
  field red : {A : Ty} (i : Γ₁ ∋ A) → Redᵛ A (sub-mem θ i)
open RedSub

record CoRedSub {Γ Δ Δ₁ : Ctx} (φ : CoSub Γ Δ Δ₁) : Set where
  field cored : {A : Ty} (i : Δ₁ ∋ A) → CoRedᵏ A (cosub-mem φ i)
open CoRedSub

RedSub-wk : {Γ Δ Γ₁ Δ₁ Γ₂ : Ctx} (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) {θ : Sub Γ Δ Γ₂} → RedSub θ → RedSub (sub-wk π ρ θ)
RedSub-wk π ρ {θ} rθ .red {A} i = Eq.subst (Redᵛ A) (sym (sub-mem-wk π ρ θ i)) (Red-wk A π ρ (rθ .red i))

CoRedSub-wk : {Γ Δ Γ₁ Δ₁ Δ₂ : Ctx} (π : Γ₁ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) {φ : CoSub Γ Δ Δ₂} → CoRedSub φ → CoRedSub (cosub-wk π ρ φ)
CoRedSub-wk π ρ {φ} rφ .cored {A} i = Eq.subst (CoRedᵏ A) (sym (cosub-mem-wk π ρ φ i)) (CoRed-wk A π ρ {K = cosub-mem φ i} (rφ .cored i))

RedSub-ext : {Γ Δ Γ₁ : Ctx} {A : Ty} {θ : Sub Γ Δ Γ₁} {V : Γ ⊢ᵛ A ∣ Δ} → RedSub θ → Redᵛ A V → RedSub (sub-ex θ V)
RedSub-ext rθ rv .red here = rv
RedSub-ext rθ rv .red (there i) = rθ .red i

CoRedSub-ext : {Γ Δ Δ₁ : Ctx} {A : Ty} {φ : CoSub Γ Δ Δ₁} {K : Γ ∣ A ⊢ᵏ Δ} → CoRedSub φ → CoRedᵏ A K → CoRedSub (cosub-ex φ K)
CoRedSub-ext rφ rk .cored here = rk
CoRedSub-ext rφ rk .cored (there i) = rφ .cored i

Fundamental-cmd : {Γ Δ Γ₁ Δ₁ : Ctx} (θ : Sub Γ Δ Γ₁) (φ : CoSub Γ Δ Δ₁)
                → RedSub θ → CoRedSub φ → (M : Γ₁ ⊢ Δ₁) → SN (sub-cmd θ φ M)
Fundamental-val : {Γ Δ Γ₁ Δ₁ : Ctx} {A : Ty} (θ : Sub Γ Δ Γ₁) (φ : CoSub Γ Δ Δ₁)
                → RedSub θ → CoRedSub φ → (V : Γ₁ ⊢ᵛ A ∣ Δ₁) → Redᵛ A (sub-val θ φ V)
Fundamental-tm  : {Γ Δ Γ₁ Δ₁ : Ctx} {A : Ty} (θ : Sub Γ Δ Γ₁) (φ : CoSub Γ Δ Δ₁)
                → RedSub θ → CoRedSub φ → (M : Γ₁ ⊢ᵗ A ∣ Δ₁) → ∀ {K : Γ ∣ A ⊢ᵏ Δ} → CoRedᵏ A K → SN (cut A (sub-tm θ φ M) K)
Fundamental-cotm : {Γ Δ Γ₁ Δ₁ : Ctx} {A : Ty} (θ : Sub Γ Δ Γ₁) (φ : CoSub Γ Δ Δ₁)
                → RedSub θ → CoRedSub φ → (K : Γ₁ ∣ A ⊢ᵏ Δ₁) → CoRedᵏ A (sub-cotm θ φ K)

Fundamental-cmd θ φ rθ rφ (cut A M K) = Fundamental-tm θ φ rθ rφ M (Fundamental-cotm θ φ rθ rφ K)

Fundamental-val θ φ rθ rφ (var i)    = rθ .red i
Fundamental-val θ φ rθ rφ (lam M)    =
  λ π ρ {W} {K} rw rk →
    Eq.subst (λ x → SN (cut _ x K)) (sym (fund-lam-eq θ φ π ρ W M))
             (Fundamental-tm (sub-ex (sub-wk π ρ θ) W) (cosub-wk π ρ φ) (RedSub-ext (RedSub-wk π ρ rθ) rw) (CoRedSub-wk π ρ rφ) M rk)
Fundamental-val θ φ rθ rφ unit       = tt
Fundamental-val θ φ rθ rφ (pair V W) = Fundamental-val θ φ rθ rφ V , Fundamental-val θ φ rθ rφ W
Fundamental-val θ φ rθ rφ (inl V)    = Fundamental-val θ φ rθ rφ V
Fundamental-val θ φ rθ rφ (inr W)    = Fundamental-val θ φ rθ rφ W

Fundamental-tm θ φ rθ rφ (ret V) rk = Ortho (Fundamental-val θ φ rθ rφ V) rk
Fundamental-tm θ φ rθ rφ (μ M)   {K} rk =
  sn (λ { μ-step → Eq.subst SN (sym (fund-mu-eq θ φ K M)) (Fundamental-cmd θ (cosub-ex φ K) rθ (CoRedSub-ext rφ rk) M) })

Fundamental-cotm θ φ rθ rφ (covar i)   = rφ .cored i
Fundamental-cotm θ φ rθ rφ (app V K)   = Fundamental-val θ φ rθ rφ V , Fundamental-cotm θ φ rθ rφ K
Fundamental-cotm θ φ rθ rφ (fst K)     = Fundamental-cotm θ φ rθ rφ K
Fundamental-cotm θ φ rθ rφ (snd K)     = Fundamental-cotm θ φ rθ rφ K
Fundamental-cotm θ φ rθ rφ (case K L) = Fundamental-cotm θ φ rθ rφ K , Fundamental-cotm θ φ rθ rφ L
Fundamental-cotm θ φ rθ rφ (μ̃ M)       =
  λ π ρ {V} rv →
    Eq.subst SN (sym (fund-mut-wk-eq θ φ π ρ V M))
             (Fundamental-cmd (sub-ex (sub-wk π ρ θ) V) (cosub-wk π ρ φ) (RedSub-ext (RedSub-wk π ρ rθ) rv) (CoRedSub-wk π ρ rφ) M)
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
step? (cut A (μ M) K) = next μ-step

step? (cut A (ret (var i)) (covar j))       = done (λ ())
step? (cut A (ret (var i)) (μ̃ M))           = next μ̃-step
step? (cut `⊥ (ret (var i)) tp)             = done (λ ())
step? (cut (A `× B) (ret (var i)) (fst K))  = done (λ ())
step? (cut (A `× B) (ret (var i)) (snd K))  = done (λ ())
step? (cut (A `+ B) (ret (var i)) (case K L)) = done (λ ())
step? (cut (A `⇒ B) (ret (var i)) (app V K))  = done (λ ())

step? (cut `Unit (ret unit) (covar j)) = done (λ ())
step? (cut `Unit (ret unit) (μ̃ M))     = next μ̃-step

step? (cut (A `× B) (ret (pair V W)) (covar j)) = done (λ ())
step? (cut (A `× B) (ret (pair V W)) (fst K))   = next fst-step
step? (cut (A `× B) (ret (pair V W)) (snd K))   = next snd-step
step? (cut (A `× B) (ret (pair V W)) (μ̃ M))     = next μ̃-step

step? (cut (A `+ B) (ret (inl V)) (covar j))  = done (λ ())
step? (cut (A `+ B) (ret (inl V)) (case K L)) = next inl-step
step? (cut (A `+ B) (ret (inl V)) (μ̃ M))          = next μ̃-step
step? (cut (A `+ B) (ret (inr W)) (covar j))  = done (λ ())
step? (cut (A `+ B) (ret (inr W)) (case K L)) = next inr-step
step? (cut (A `+ B) (ret (inr W)) (μ̃ M))          = next μ̃-step

step? (cut (A `⇒ B) (ret (lam M)) (covar j)) = done (λ ())
step? (cut (A `⇒ B) (ret (lam M)) (app V K)) = next app-step
step? (cut (A `⇒ B) (ret (lam M)) (μ̃ M'))     = next μ̃-step

eval-acc : {Γ Δ : Ctx} {M : Γ ⊢ Δ} → SN M → Σ[ N ∈ Γ ⊢ Δ ] (M ↦* N) × Normal N
eval-acc {M = M} (sn f) with step? M
... | done normal = M , M ◼ , normal
... | next {N} step with eval-acc (f step)
... | (P , chain , normal) = P , M ~>⟨ step ⟩ chain , normal

eval : {Γ Δ : Ctx} (M : Γ ⊢ Δ) → Σ[ N ∈ Γ ⊢ Δ ] (M ↦* N) × Normal N
eval M = eval-acc (SN-theorem M)
