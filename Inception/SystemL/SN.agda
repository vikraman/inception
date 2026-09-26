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

  inl-step : {A B : Ty} {V : Γ ⊢ᵛ A ∣ Δ} {K₁ : Γ ∣ A ⊢ᵏ Δ} {K₂ : Γ ∣ B ⊢ᵏ Δ}
           → cut (A `+ B) (ret (inl V)) (case K₁ K₂) ↦ cut A (ret V) K₁

  inr-step : {A B : Ty} {W : Γ ⊢ᵛ B ∣ Δ} {K₁ : Γ ∣ A ⊢ᵏ Δ} {K₂ : Γ ∣ B ⊢ᵏ Δ}
           → cut (A `+ B) (ret (inr W)) (case K₁ K₂) ↦ cut B (ret W) K₂

--------------------------------------------------------------------------
-- accessibility

data SN {Γ Δ} (M : Γ ⊢ Δ) : Set where
  sn : (∀ {M₁} → M ↦ M₁ → SN M₁) → SN M

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
  ∀ {Γ' Δ'} (π : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) {W : Γ' ⊢ᵛ A ∣ Δ'} {K : Γ' ∣ B ⊢ᵏ Δ'}
  → Redᵛ A W → CoRedᵏ B K → SN (cut B (letv W (wk-tm (wk-cong π) σ M)) K)

CoRedᵏ A         (covar i)    = ⊤
CoRedᵏ A {Γ} {Δ} (μ̃ M)       =
  ∀ {Γ' Δ'} (π : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) {V : Γ' ⊢ᵛ A ∣ Δ'}
  → Redᵛ A V → SN (sub-cmd (sub-ex sub-id V) cosub-id (wk-cmd (wk-cong π) σ M))
CoRedᵏ `⊥        tp           = ⊤
CoRedᵏ (A `× B)  (fst K)      = CoRedᵏ A K
CoRedᵏ (A `× B)  (snd K)      = CoRedᵏ B K
CoRedᵏ (A `+ B)  (case K₁ K₂) = CoRedᵏ A K₁ × CoRedᵏ B K₂
CoRedᵏ (A `⇒ B)  (app V K)    = Redᵛ A V × CoRedᵏ B K

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
  λ π' σ' {W} {K} rw rk →
    Eq.subst (λ x → SN (cut B (letv W x) K)) (sym (wk-tm-trans M (wk-cong π') (wk-cong π) σ' σ)) (f (wk-trans π' π) (wk-trans σ' σ) rw rk)

CoRed-wk : (A : Ty) {Γ Δ Γ' Δ' : Ctx} (π : Γ' ⊇ Γ) (σ : Δ' ⊇ Δ) {K : Γ ∣ A ⊢ᵏ Δ}
         → CoRedᵏ A K → CoRedᵏ A (wk-cotm π σ K)
CoRed-wk A             π σ {K = covar i}   r  = tt
CoRed-wk `⊥            π σ {K = tp}        r  = tt
CoRed-wk (A `× B)      π σ {K = fst K}     r  = CoRed-wk A π σ {K = K} r
CoRed-wk (A `× B)      π σ {K = snd K}     r  = CoRed-wk B π σ {K = K} r
CoRed-wk (A `+ B)      π σ {K = case K₁ K₂} (r₁ , r₂) = CoRed-wk A π σ {K = K₁} r₁ , CoRed-wk B π σ {K = K₂} r₂
CoRed-wk (A `⇒ B)      π σ {K = app V K}   (rv , rk)  = Red-wk A π σ rv , CoRed-wk B π σ {K = K} rk
CoRed-wk A {Γ} {Δ} π σ {K = μ̃ M} f =
  λ π' σ' {V} rv →
    Eq.subst (λ x → SN (sub-cmd (sub-ex sub-id V) cosub-id x)) (sym (wk-cmd-trans M (wk-cong π') (wk-cong π) σ' σ)) (f (wk-trans π' π) (wk-trans σ' σ) rv)

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
Ortho {A `+ B} {V = var i} {K = case K₁ K₂} rv rk = sn λ ()
Ortho {A `+ B} {V = var i} {K = μ̃ M} rv rk = Ortho-μ̃ rv rk
Ortho {A `+ B} {V = inl V} {K = covar i} rv rk = sn λ ()
Ortho {A `+ B} {V = inl V} {K = case K₁ K₂} rv (ra , rb) = sn λ { inl-step → Ortho rv ra }
Ortho {A `+ B} {V = inl V} {K = μ̃ M} rv rk = Ortho-μ̃ rv rk
Ortho {A `+ B} {V = inr V} {K = covar i} rv rk = sn λ ()
Ortho {A `+ B} {V = inr V} {K = case K₁ K₂} rv (ra , rb) = sn λ { inr-step → Ortho rv rb }
Ortho {A `+ B} {V = inr V} {K = μ̃ M} rv rk = Ortho-μ̃ rv rk

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
CoRedSub-wk π σ {φ} rφ .cored {A} i = Eq.subst (CoRedᵏ A) (sym (cosub-mem-wk π σ φ i)) (CoRed-wk A π σ {K = cosub-mem φ i} (rφ .cored i))

RedSub-ext : {Γ Δ Γ' : Ctx} {A : Ty} {θ : Sub Γ Δ Γ'} {V : Γ ⊢ᵛ A ∣ Δ} → RedSub θ → Redᵛ A V → RedSub (sub-ex θ V)
RedSub-ext rθ rv .red here = rv
RedSub-ext rθ rv .red (there i) = rθ .red i

CoRedSub-ext : {Γ Δ Δ' : Ctx} {A : Ty} {φ : CoSub Γ Δ Δ'} {K : Γ ∣ A ⊢ᵏ Δ} → CoRedSub φ → CoRedᵏ A K → CoRedSub (cosub-ex φ K)
CoRedSub-ext rφ rk .cored here = rk
CoRedSub-ext rφ rk .cored (there i) = rφ .cored i

Fundamental-cmd : {Γ Δ Γ' Δ' : Ctx} (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ')
                → RedSub θ → CoRedSub φ → (M : Γ' ⊢ Δ') → SN (sub-cmd θ φ M)
Fundamental-val : {Γ Δ Γ' Δ' : Ctx} {A : Ty} (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ')
                → RedSub θ → CoRedSub φ → (V : Γ' ⊢ᵛ A ∣ Δ') → Redᵛ A (sub-val θ φ V)
Fundamental-tm  : {Γ Δ Γ' Δ' : Ctx} {A : Ty} (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ')
                → RedSub θ → CoRedSub φ → (M : Γ' ⊢ᵗ A ∣ Δ') → ∀ {K : Γ ∣ A ⊢ᵏ Δ} → CoRedᵏ A K → SN (cut A (sub-tm θ φ M) K)
Fundamental-cotm : {Γ Δ Γ' Δ' : Ctx} {A : Ty} (θ : Sub Γ Δ Γ') (φ : CoSub Γ Δ Δ')
                → RedSub θ → CoRedSub φ → (K : Γ' ∣ A ⊢ᵏ Δ') → CoRedᵏ A (sub-cotm θ φ K)

Fundamental-cmd θ φ rθ rφ (cut A M K) = Fundamental-tm θ φ rθ rφ M (Fundamental-cotm θ φ rθ rφ K)

Fundamental-val θ φ rθ rφ (var i)    = rθ .red i
Fundamental-val θ φ rθ rφ (lam M)    =
  λ π σ {W} {K} rw rk →
    Eq.subst (λ x → SN (cut _ x K)) (sym (fund-lam-eq θ φ π σ W M))
             (Fundamental-tm (sub-ex (sub-wk π σ θ) W) (cosub-wk π σ φ) (RedSub-ext (RedSub-wk π σ rθ) rw) (CoRedSub-wk π σ rφ) M rk)
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
Fundamental-cotm θ φ rθ rφ (case K₁ K₂) = Fundamental-cotm θ φ rθ rφ K₁ , Fundamental-cotm θ φ rθ rφ K₂
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
step? (cut A (μ M) K) = next μ-step

step? (cut A (ret (var i)) (covar j))       = done (λ ())
step? (cut A (ret (var i)) (μ̃ M))           = next μ̃-step
step? (cut `⊥ (ret (var i)) tp)             = done (λ ())
step? (cut (A `× B) (ret (var i)) (fst K))  = done (λ ())
step? (cut (A `× B) (ret (var i)) (snd K))  = done (λ ())
step? (cut (A `+ B) (ret (var i)) (case K₁ K₂)) = done (λ ())
step? (cut (A `⇒ B) (ret (var i)) (app V K))    = done (λ ())

step? (cut `Unit (ret unit) (covar j)) = done (λ ())
step? (cut `Unit (ret unit) (μ̃ M))     = next μ̃-step

step? (cut (A `× B) (ret (pair V W)) (covar j)) = done (λ ())
step? (cut (A `× B) (ret (pair V W)) (fst K))   = next fst-step
step? (cut (A `× B) (ret (pair V W)) (snd K))   = next snd-step
step? (cut (A `× B) (ret (pair V W)) (μ̃ M))     = next μ̃-step

step? (cut (A `+ B) (ret (inl V)) (covar j))    = done (λ ())
step? (cut (A `+ B) (ret (inl V)) (case K₁ K₂)) = next inl-step
step? (cut (A `+ B) (ret (inl V)) (μ̃ M))          = next μ̃-step
step? (cut (A `+ B) (ret (inr W)) (covar j))    = done (λ ())
step? (cut (A `+ B) (ret (inr W)) (case K₁ K₂)) = next inr-step
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
