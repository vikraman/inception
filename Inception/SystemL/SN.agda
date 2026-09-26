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

  μ-step   : {X : Ty} {C : Γ ⊢ (Δ ∙ X)} {K : Γ ∣ X ⊢ᵏ Δ}
           → cut X (μ C) K ↦ letc K C

  μ̃-step   : {X : Ty} {V : Γ ⊢ᵛ X ∣ Δ} {C : (Γ ∙ X) ⊢ Δ}
           → cut X (ret V) (μ̃ C) ↦ letvc V C

  app-step : {X Y : Ty} {M : (Γ ∙ X) ⊢ᵗ Y ∣ Δ} {V : Γ ⊢ᵛ X ∣ Δ} {K : Γ ∣ Y ⊢ᵏ Δ}
           → cut (X `⇒ Y) (ret (lam M)) (app V K) ↦ cut Y (letv V M) K

  fst-step : {X Y : Ty} {V : Γ ⊢ᵛ X ∣ Δ} {W : Γ ⊢ᵛ Y ∣ Δ} {K : Γ ∣ X ⊢ᵏ Δ}
           → cut (X `× Y) (ret (pair V W)) (fst K) ↦ cut X (ret V) K

  snd-step : {X Y : Ty} {V : Γ ⊢ᵛ X ∣ Δ} {W : Γ ⊢ᵛ Y ∣ Δ} {K : Γ ∣ Y ⊢ᵏ Δ}
           → cut (X `× Y) (ret (pair V W)) (snd K) ↦ cut Y (ret W) K

  inl-step : {X Y : Ty} {V : Γ ⊢ᵛ X ∣ Δ} {K : Γ ∣ X ⊢ᵏ Δ} {L : Γ ∣ Y ⊢ᵏ Δ}
           → cut (X `+ Y) (ret (inl V)) (case K L) ↦ cut X (ret V) K

  inr-step : {X Y : Ty} {W : Γ ⊢ᵛ Y ∣ Δ} {K : Γ ∣ X ⊢ᵏ Δ} {L : Γ ∣ Y ⊢ᵏ Δ}
           → cut (X `+ Y) (ret (inr W)) (case K L) ↦ cut Y (ret W) L

--------------------------------------------------------------------------
-- accessibility

data SN {Γ Δ} (C : Γ ⊢ Δ) : Set where
  sn : (∀ {C₁} → C ↦ C₁ → SN C₁) → SN C

--------------------------------------------------------------------------
-- reducibility candidates

Redᵛ  : (X : Ty) {Γ Δ : Ctx} → Γ ⊢ᵛ X ∣ Δ → Set
CoRedᵏ : (X : Ty) {Γ Δ : Ctx} → Γ ∣ X ⊢ᵏ Δ → Set

Redᵛ `⊥        V = ⊤
Redᵛ `𝟙     V    = ⊤
Redᵛ `𝓅       V              = ⊤
Redᵛ (X `× Y)  (var i)    = ⊤
Redᵛ (X `× Y)  (pair V W) = Redᵛ X V × Redᵛ Y W
Redᵛ (X `+ Y)  (var i)    = ⊤
Redᵛ (X `+ Y)  (inl V)    = Redᵛ X V
Redᵛ (X `+ Y)  (inr W)    = Redᵛ Y W
Redᵛ (X `⇒ Y)  (var i)    = ⊤
Redᵛ (X `⇒ Y) {Γ} {Δ} (lam M) =
  ∀ {Ψ Δ₁} (π : Ψ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) {W : Ψ ⊢ᵛ X ∣ Δ₁} {K : Ψ ∣ Y ⊢ᵏ Δ₁}
  → Redᵛ X W → CoRedᵏ Y K → SN (cut Y (letv W (wk-tm (wk-cong π) ρ M)) K)

CoRedᵏ X         (covar i)    = ⊤
CoRedᵏ X {Γ} {Δ} (μ̃ C)       =
  ∀ {Ψ Δ₁} (π : Ψ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) {V : Ψ ⊢ᵛ X ∣ Δ₁}
  → Redᵛ X V → SN (sub-cmd (sub-ex sub-id V) cosub-id (wk-cmd (wk-cong π) ρ C))
CoRedᵏ `⊥        tp         = ⊤
CoRedᵏ (X `× Y)  (fst K)    = CoRedᵏ X K
CoRedᵏ (X `× Y)  (snd K)    = CoRedᵏ Y K
CoRedᵏ (X `+ Y)  (case K L) = CoRedᵏ X K × CoRedᵏ Y L
CoRedᵏ (X `⇒ Y)  (app V K)  = Redᵛ X V × CoRedᵏ Y K

--------------------------------------------------------------------------
-- weakening preserves reducibility

Red-wk : (X : Ty) {Γ Δ Ψ Δ₁ : Ctx} (π : Ψ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) {V : Γ ⊢ᵛ X ∣ Δ}
       → Redᵛ X V → Redᵛ X (wk-val π ρ V)
Red-wk `⊥        π ρ r = tt
Red-wk `𝟙     π ρ r    = tt
Red-wk `𝓅       π ρ r = tt
Red-wk (X `× Y) π ρ {V = var i}    r        = tt
Red-wk (X `× Y) π ρ {V = pair V W} (rv , rw) = Red-wk X π ρ rv , Red-wk Y π ρ rw
Red-wk (X `+ Y) π ρ {V = var i}  r  = tt
Red-wk (X `+ Y) π ρ {V = inl V}  rv = Red-wk X π ρ rv
Red-wk (X `+ Y) π ρ {V = inr W}  rw = Red-wk Y π ρ rw
Red-wk (X `⇒ Y) π ρ {V = var i}  r = tt
Red-wk (X `⇒ Y) {Γ} {Δ} π ρ {V = lam M} f =
  λ π₁ σ {W} {K} rw rk →
    Eq.subst (λ x → SN (cut Y (letv W x) K)) (sym (wk-tm-trans M (wk-cong π₁) (wk-cong π) σ ρ)) (f (wk-trans π₁ π) (wk-trans σ ρ) rw rk)

CoRed-wk : (X : Ty) {Γ Δ Ψ Δ₁ : Ctx} (π : Ψ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) {K : Γ ∣ X ⊢ᵏ Δ}
         → CoRedᵏ X K → CoRedᵏ X (wk-cotm π ρ K)
CoRed-wk X             π ρ {K = covar i}   r  = tt
CoRed-wk `⊥            π ρ {K = tp}        r  = tt
CoRed-wk (X `× Y)      π ρ {K = fst K}     r  = CoRed-wk X π ρ {K = K} r
CoRed-wk (X `× Y)      π ρ {K = snd K}     r  = CoRed-wk Y π ρ {K = K} r
CoRed-wk (X `+ Y)      π ρ {K = case K L} (r₁ , r₂) = CoRed-wk X π ρ {K = K} r₁ , CoRed-wk Y π ρ {K = L} r₂
CoRed-wk (X `⇒ Y)      π ρ {K = app V K}   (rv , rk)  = Red-wk X π ρ rv , CoRed-wk Y π ρ {K = K} rk
CoRed-wk X {Γ} {Δ} π ρ {K = μ̃ C} f =
  λ π₁ σ {V} rv →
    Eq.subst (λ x → SN (sub-cmd (sub-ex sub-id V) cosub-id x)) (sym (wk-cmd-trans C (wk-cong π₁) (wk-cong π) σ ρ)) (f (wk-trans π₁ π) (wk-trans σ ρ) rv)

--------------------------------------------------------------------------
-- orthogonality

Ortho-μ̃ : {X : Ty} {Γ Δ : Ctx} {V : Γ ⊢ᵛ X ∣ Δ} {C : (Γ ∙ X) ⊢ Δ}
        → Redᵛ X V → CoRedᵏ X (μ̃ C) → SN (cut X (ret V) (μ̃ C))
Ortho-μ̃ {V = V} {M} rv rk =
  sn (λ { μ̃-step → Eq.subst SN (cong (sub-cmd (sub-ex sub-id V) cosub-id) (wk-cmd-id M)) (rk wk-id wk-id rv) })

Ortho : {X : Ty} {Γ Δ : Ctx} {V : Γ ⊢ᵛ X ∣ Δ} {K : Γ ∣ X ⊢ᵏ Δ}
      → Redᵛ X V → CoRedᵏ X K → SN (cut X (ret V) K)
Ortho {X} {V = var i} {K = covar j} rv rk = sn λ ()
Ortho {`⊥} {V = var i} {K = μ̃ C} rv rk = Ortho-μ̃ rv rk
Ortho {`⊥} {V = var i} {K = tp} rv rk = sn λ ()
Ortho {`𝟙} {V = var i} {K = μ̃ C} rv rk = Ortho-μ̃ rv rk
Ortho {`𝟙} {V = unit} {K = covar i} rv rk = sn λ ()
Ortho {`𝟙} {V = unit} {K = μ̃ C} rv rk = Ortho-μ̃ rv rk
Ortho {`𝓅} {V = var i} {K = μ̃ C} rv rk = Ortho-μ̃ rv rk
Ortho {X `× Y} {V = var i} {K = fst K} rv rk = sn λ ()
Ortho {X `× Y} {V = var i} {K = snd K} rv rk = sn λ ()
Ortho {X `× Y} {V = var i} {K = μ̃ C} rv rk = Ortho-μ̃ rv rk
Ortho {X `× Y} {V = pair V W} {K = covar i} rv rk = sn λ ()
Ortho {X `× Y} {V = pair V W} {K = fst K} (rv , rw) rk = sn λ { fst-step → Ortho rv rk }
Ortho {X `× Y} {V = pair V W} {K = snd K} (rv , rw) rk = sn λ { snd-step → Ortho rw rk }
Ortho {X `× Y} {V = pair V W} {K = μ̃ C} rv rk = Ortho-μ̃ rv rk
Ortho {X `⇒ Y} {V = var i} {K = app W K} rv rk = sn λ ()
Ortho {X `⇒ Y} {V = var i} {K = μ̃ C} rv rk = Ortho-μ̃ rv rk
Ortho {X `⇒ Y} {V = lam M} {K = covar i} rv rk = sn λ ()
Ortho {X `⇒ Y} {V = lam M} {K = app W K} rv (rw , rk) =
  sn λ { app-step → Eq.subst (λ x → SN (cut Y (letv W x) K)) (wk-tm-id M) (rv wk-id wk-id rw rk) }
Ortho {X `⇒ Y} {V = lam M} {K = μ̃ C} rv rk = Ortho-μ̃ rv rk
Ortho {X `+ Y} {V = var i} {K = case K L} rv rk = sn λ ()
Ortho {X `+ Y} {V = var i} {K = μ̃ C} rv rk = Ortho-μ̃ rv rk
Ortho {X `+ Y} {V = inl V} {K = covar i} rv rk = sn λ ()
Ortho {X `+ Y} {V = inl V} {K = case K L} rv (ra , rb) = sn λ { inl-step → Ortho rv ra }
Ortho {X `+ Y} {V = inl V} {K = μ̃ C} rv rk = Ortho-μ̃ rv rk
Ortho {X `+ Y} {V = inr V} {K = covar i} rv rk = sn λ ()
Ortho {X `+ Y} {V = inr V} {K = case K L} rv (ra , rb) = sn λ { inr-step → Ortho rv rb }
Ortho {X `+ Y} {V = inr V} {K = μ̃ C} rv rk = Ortho-μ̃ rv rk

--------------------------------------------------------------------------
-- fundamental lemma

record RedSub {Γ Δ Ψ : Ctx} (θ : Sub Γ Δ Ψ) : Set where
  field red : {X : Ty} (i : Ψ ∋ X) → Redᵛ X (sub-mem θ i)
open RedSub

record CoRedSub {Γ Δ Δ₁ : Ctx} (φ : CoSub Γ Δ Δ₁) : Set where
  field cored : {X : Ty} (i : Δ₁ ∋ X) → CoRedᵏ X (cosub-mem φ i)
open CoRedSub

RedSub-wk : {Γ Δ Ψ Δ₁ Γ₁ : Ctx} (π : Ψ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) {θ : Sub Γ Δ Γ₁} → RedSub θ → RedSub (sub-wk π ρ θ)
RedSub-wk π ρ {θ} rθ .red {X} i = Eq.subst (Redᵛ X) (sym (sub-mem-wk π ρ θ i)) (Red-wk X π ρ (rθ .red i))

CoRedSub-wk : {Γ Δ Ψ Δ₁ Δ₂ : Ctx} (π : Ψ ⊇ Γ) (ρ : Δ₁ ⊇ Δ) {φ : CoSub Γ Δ Δ₂} → CoRedSub φ → CoRedSub (cosub-wk π ρ φ)
CoRedSub-wk π ρ {φ} rφ .cored {X} i = Eq.subst (CoRedᵏ X) (sym (cosub-mem-wk π ρ φ i)) (CoRed-wk X π ρ {K = cosub-mem φ i} (rφ .cored i))

RedSub-ext : {Γ Δ Ψ : Ctx} {X : Ty} {θ : Sub Γ Δ Ψ} {V : Γ ⊢ᵛ X ∣ Δ} → RedSub θ → Redᵛ X V → RedSub (sub-ex θ V)
RedSub-ext rθ rv .red here = rv
RedSub-ext rθ rv .red (there i) = rθ .red i

CoRedSub-ext : {Γ Δ Δ₁ : Ctx} {X : Ty} {φ : CoSub Γ Δ Δ₁} {K : Γ ∣ X ⊢ᵏ Δ} → CoRedSub φ → CoRedᵏ X K → CoRedSub (cosub-ex φ K)
CoRedSub-ext rφ rk .cored here = rk
CoRedSub-ext rφ rk .cored (there i) = rφ .cored i

Fundamental-cmd : {Γ Δ Ψ Δ₁ : Ctx} (θ : Sub Γ Δ Ψ) (φ : CoSub Γ Δ Δ₁)
                → RedSub θ → CoRedSub φ → (C : Ψ ⊢ Δ₁) → SN (sub-cmd θ φ C)
Fundamental-val : {Γ Δ Ψ Δ₁ : Ctx} {X : Ty} (θ : Sub Γ Δ Ψ) (φ : CoSub Γ Δ Δ₁)
                → RedSub θ → CoRedSub φ → (V : Ψ ⊢ᵛ X ∣ Δ₁) → Redᵛ X (sub-val θ φ V)
Fundamental-tm  : {Γ Δ Ψ Δ₁ : Ctx} {X : Ty} (θ : Sub Γ Δ Ψ) (φ : CoSub Γ Δ Δ₁)
                → RedSub θ → CoRedSub φ → (M : Ψ ⊢ᵗ X ∣ Δ₁) → ∀ {K : Γ ∣ X ⊢ᵏ Δ} → CoRedᵏ X K → SN (cut X (sub-tm θ φ M) K)
Fundamental-cotm : {Γ Δ Ψ Δ₁ : Ctx} {X : Ty} (θ : Sub Γ Δ Ψ) (φ : CoSub Γ Δ Δ₁)
                → RedSub θ → CoRedSub φ → (K : Ψ ∣ X ⊢ᵏ Δ₁) → CoRedᵏ X (sub-cotm θ φ K)

Fundamental-cmd θ φ rθ rφ (cut X M K) = Fundamental-tm θ φ rθ rφ M (Fundamental-cotm θ φ rθ rφ K)

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
Fundamental-tm θ φ rθ rφ (μ C)   {K} rk =
  sn (λ { μ-step → Eq.subst SN (sym (fund-mu-eq θ φ K C)) (Fundamental-cmd θ (cosub-ex φ K) rθ (CoRedSub-ext rφ rk) C) })

Fundamental-cotm θ φ rθ rφ (covar i)   = rφ .cored i
Fundamental-cotm θ φ rθ rφ (app V K)   = Fundamental-val θ φ rθ rφ V , Fundamental-cotm θ φ rθ rφ K
Fundamental-cotm θ φ rθ rφ (fst K)     = Fundamental-cotm θ φ rθ rφ K
Fundamental-cotm θ φ rθ rφ (snd K)     = Fundamental-cotm θ φ rθ rφ K
Fundamental-cotm θ φ rθ rφ (case K L) = Fundamental-cotm θ φ rθ rφ K , Fundamental-cotm θ φ rθ rφ L
Fundamental-cotm θ φ rθ rφ (μ̃ C)       =
  λ π ρ {V} rv →
    Eq.subst SN (sym (fund-mut-wk-eq θ φ π ρ V C))
             (Fundamental-cmd (sub-ex (sub-wk π ρ θ) V) (cosub-wk π ρ φ) (RedSub-ext (RedSub-wk π ρ rθ) rv) (CoRedSub-wk π ρ rφ) C)
Fundamental-cotm θ φ rθ rφ tp          = tt

Red-var-triv : (X : Ty) {Γ : Ctx} (Δ : Ctx) (i : Γ ∋ X) → Redᵛ X (var {Δ = Δ} i)
Red-var-triv `⊥        Δ i = tt
Red-var-triv `𝟙     Δ i    = tt
Red-var-triv `𝓅       Δ i = tt
Red-var-triv (X `× Y)  Δ i = tt
Red-var-triv (X `+ Y)  Δ i = tt
Red-var-triv (X `⇒ Y)  Δ i = tt

RedSub-id : {Γ Δ : Ctx} → RedSub (sub-id {Γ} {Δ})
RedSub-id {Γ} {Δ} .red {X} i = Eq.subst (Redᵛ X) (sym (sub-mem-id i)) (Red-var-triv X Δ i)

CoRedSub-id : {Γ Δ : Ctx} → CoRedSub (cosub-id {Γ} {Δ})
CoRedSub-id {Γ} {Δ} .cored {X} i = Eq.subst (CoRedᵏ X) (sym (cosub-mem-id i)) tt

SN-theorem : {Γ Δ : Ctx} (C : Γ ⊢ Δ) → SN C
SN-theorem {Γ} {Δ} M = Eq.subst SN (sub-cmd-id M) (Fundamental-cmd sub-id cosub-id RedSub-id CoRedSub-id M)

--------------------------------------------------------------------------
-- eval

open import Inception.Prelude
open Inception.Prelude.RTC

_↦*_ : {Γ Δ : Ctx} → Γ ⊢ Δ → Γ ⊢ Δ → Set
_↦*_ {Γ} {Δ} = _~>*_ (_↦_ {Γ = Γ} {Δ = Δ})

Normal : {Γ Δ : Ctx} → Γ ⊢ Δ → Set
Normal C = ∀ {C₁} → C ↦ C₁ → ⊥

data Step? {Γ Δ : Ctx} (C : Γ ⊢ Δ) : Set where
  done : Normal C → Step? C
  next : {C₁ : Γ ⊢ Δ} → C ↦ C₁ → Step? C

step? : {Γ Δ : Ctx} (C : Γ ⊢ Δ) → Step? C
step? (cut X (μ C) K) = next μ-step

step? (cut X (ret (var i)) (covar j))       = done (λ ())
step? (cut X (ret (var i)) (μ̃ C))           = next μ̃-step
step? (cut `⊥ (ret (var i)) tp)            = done (λ ())
step? (cut (X `× Y) (ret (var i)) (fst K)) = done (λ ())
step? (cut (X `× Y) (ret (var i)) (snd K)) = done (λ ())
step? (cut (X `+ Y) (ret (var i)) (case K L)) = done (λ ())
step? (cut (X `⇒ Y) (ret (var i)) (app V K))  = done (λ ())

step? (cut `𝟙 (ret unit) (covar j)) = done (λ ())
step? (cut `𝟙 (ret unit) (μ̃ C))     = next μ̃-step

step? (cut (X `× Y) (ret (pair V W)) (covar j)) = done (λ ())
step? (cut (X `× Y) (ret (pair V W)) (fst K))   = next fst-step
step? (cut (X `× Y) (ret (pair V W)) (snd K))   = next snd-step
step? (cut (X `× Y) (ret (pair V W)) (μ̃ C))     = next μ̃-step

step? (cut (X `+ Y) (ret (inl V)) (covar j))  = done (λ ())
step? (cut (X `+ Y) (ret (inl V)) (case K L)) = next inl-step
step? (cut (X `+ Y) (ret (inl V)) (μ̃ C))          = next μ̃-step
step? (cut (X `+ Y) (ret (inr W)) (covar j))  = done (λ ())
step? (cut (X `+ Y) (ret (inr W)) (case K L)) = next inr-step
step? (cut (X `+ Y) (ret (inr W)) (μ̃ C))          = next μ̃-step

step? (cut (X `⇒ Y) (ret (lam M)) (covar j)) = done (λ ())
step? (cut (X `⇒ Y) (ret (lam M)) (app V K)) = next app-step
step? (cut (X `⇒ Y) (ret (lam M)) (μ̃ C))     = next μ̃-step

eval-acc : {Γ Δ : Ctx} {C : Γ ⊢ Δ} → SN C → Σ[ C₁ ∈ Γ ⊢ Δ ] (C ↦* C₁) × Normal C₁
eval-acc {C = C} (sn f) with step? C
... | done normal = C , C ◼ , normal
... | next {C₁} step with eval-acc (f step)
... | (C₂ , chain , normal) = C₂ , C ~>⟨ step ⟩ chain , normal

eval : {Γ Δ : Ctx} (C : Γ ⊢ Δ) → Σ[ C₁ ∈ Γ ⊢ Δ ] (C ↦* C₁) × Normal C₁
eval C = eval-acc (SN-theorem C)
