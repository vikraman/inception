{-# OPTIONS --no-postfix-projections #-}

open import Inception.Sub.Syntax using (Ty)

module Inception.Sub.GCMachine (ℛ : Ty) where

open import Inception.Prelude
open import Inception.Sub.Syntax

open import Data.Empty using (⊥)
open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Unit using (⊤; tt)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

--------------------------------------------------------------------------

infixl 27 _·﹝_╎_╎_﹞
infixl 27 <_；_>∷_
infixl 27 _·_

--------------------------------------------------------------------------
-- environments

data WkExt : Γ ⊇ Δ → Set where

  wkext-id : {π : Γ ⊇ Γ} → WkExt π

  wkext-wk : {π : Γ ⊇ Δ} → WkExt π → WkExt (wk-wk {X = X} π)

wkext-emp : (π : Γ ⊇ ε) → WkExt π
wkext-emp wk-ε = wkext-id
wkext-emp (wk-wk π) = wkext-wk (wkext-emp π)

mutual

  data CStack : (Γ : Ctx) → (X : Ty) → Set where

    ◻ :        CStack ε ℛ

    <_；_>∷_ :  (Γ ∙ Y) ⊢ᶜ X → {π : Γ ⊇ Δ} → WkExt π → (K : CStack Δ X)
                ------------------------------------
                → CStack Γ Y

  data OMVal : Ctx → Ty → Set where

    unit :
              -------------------
              OMVal Γ `𝟙

    pair :    (𝐕 : OMVal Γ X) → (𝐖 : OMVal Γ Y)
              -------------------------------------------------
              → OMVal Γ (X `× Y)

    lam :     (M : (Γ ∙ X) ⊢ᶜ Y)
              ----------------------------------------------------
              → OMVal Γ (X `⇒ Y)

    var :     (i : Γ ∋ X)
              ----------------------------------------------------
              → OMVal Γ X


  data MEnv : Ctx → Set where

    ⋄ :
               --------------
               MEnv ε

    _·_ :      MEnv Γ → OMVal Γ X
               ----------------------------------
               → MEnv (Γ ∙ X)

    _·﹝_╎_╎_﹞ :  MEnv Γ → Γ ⊢ᶜ X → {π : Γ ⊇ Δ} → WkExt π → CStack Δ X
               ----------------------------------------------
               → MEnv (Γ ∙ `ℓ)

data CState : Set where

  ⟨_；_╎_╎_⟩ :  (γ : MEnv Γ) → (𝐖 : OMVal Γ X) → {π : Γ ⊇ Δ} → WkExt π → (K : CStack Δ X)
             -----------------------------------------------------------------
             → CState

  ⟨_╎_╎_╎_⟩ :  (γ : MEnv Γ) → (M : Γ ⊢ᶜ X) → {π : Γ ⊇ Δ} → WkExt π → (K : CStack Δ X)
             -----------------------------------------------------------------
             → CState


data TermType : Ty → Set where

  is-unit-type : TermType `𝟙

  is-pair-type : TermType (X `× Y)

  is-func-type : TermType (X `⇒ Y)

data OMValTerm : OMVal Γ X → Set where

  is-unit : OMValTerm {Γ = Γ} unit

  is-pair : (𝐕 : OMVal Γ X) → (𝐖 : OMVal Γ Y) → OMValTerm (pair 𝐕 𝐖)

  is-lam  : (M : (Γ ∙ X) ⊢ᶜ Y) → OMValTerm (lam M)

wk-omval : Γ ⊇ Δ → OMVal Δ X → OMVal Γ X
wk-omval π unit = unit
wk-omval π (pair 𝐕 𝐖) = pair (wk-omval π 𝐕) (wk-omval π 𝐖)
wk-omval π (lam M) = lam (wk-comp (wk-cong π) M)
wk-omval π (var i) = var (wk-mem π i)

wkext-trans : {π : Γ ⊇ Δ} → WkExt π → {ρ : Δ ⊇ Ψ} → WkExt ρ → WkExt (wk-trans π ρ)
wkext-trans wkext-id wkext-id = wkext-id
wkext-trans wkext-id (wkext-wk r) = wkext-wk r
wkext-trans (wkext-wk p) wkext-id = wkext-wk p
wkext-trans (wkext-wk p) (wkext-wk r) = wkext-wk (wkext-trans p (wkext-wk r))

max : {π₁ : Γ ⊇ Ψ₁} → WkExt π₁ → {ρ₁ : Ψ₁ ⊇ Δ} → WkExt ρ₁ → {π₂ : Γ ⊇ Ψ₂} → WkExt π₂ → {ρ₂ : Ψ₂ ⊇ Δ} → WkExt ρ₂ → Σ[ Ψ ∈ Ctx ] Σ[ π ∈ Γ ⊇ Ψ ] ((WkExt π) × (Ψ ⊇ Ψ₁) × (Ψ ⊇ Ψ₂) × (Σ[ ρ ∈ Ψ ⊇ Δ ] (WkExt ρ)))
max {Γ = Γ} {Δ = Γ} wkext-id wkext-id wkext-id wkext-id = Γ , wk-id , wkext-id , wk-id , wk-id , wk-id , wkext-id
max {Γ = Γ} {Δ = Γ} wkext-id wkext-id wkext-id (wkext-wk _) = Γ , wk-id , wkext-id , wk-id , wk-id , wk-id , wkext-id
max {Γ = Γ} {Δ = Γ} wkext-id wkext-id (wkext-wk _) wkext-id = Γ , wk-id , wkext-id , wk-id , wk-id , wk-id , wkext-id
max {Γ = Γ ∙ X} {Δ = Γ ∙ X} {π₁ = π₁} wkext-id {ρ₁ = ρ₁} wkext-id {π₂ = wk-wk π₂} (wkext-wk _) {ρ₂ = wk-wk ρ₂} (wkext-wk _) = ql (wk-absurd (Wk.wk-wk π₂) ρ₂) _
max {Γ = Γ} wkext-id (wkext-wk _) wkext-id wkext-id = Γ , wk-id , wkext-id , wk-id , wk-id , wk-id , wkext-id
max {Γ = Γ} wkext-id (wkext-wk r₁) wkext-id {ρ₂ = ρ₂} (wkext-wk r₂) = Γ , wk-id , wkext-id , wk-id , wk-id , Wk.wk-wk _ , wkext-wk r₁
max {Γ = Γ} {π₁ = π₁} wkext-id {ρ₁ = wk-wk ρ₁} (wkext-wk r₁) {π₂ = wk-wk π₂} (wkext-wk _) {ρ₂ = ρ₂} wkext-id = Γ , wk-id , wkext-id , wk-id , wk-wk π₂ , _ , wkext-wk r₁
max {Γ = Γ} wkext-id (wkext-wk r₁) {π₂ = wk-wk π₂} (wkext-wk _) (wkext-wk r₂) = Γ , wk-id , wkext-id , wk-id , wk-wk π₂ , _ , wkext-wk r₁
max {Γ = Γ} (wkext-wk _) wkext-id wkext-id wkext-id = Γ , wk-id , wkext-id , wk-id , wk-id , wk-id , wkext-id
max {Γ = Γ} {π₁ = wk-wk π₁} (wkext-wk p₁) wkext-id wkext-id (wkext-wk _) = Γ , wk-id , wkext-id , wk-wk π₁ , wk-id , wk-wk π₁ , wkext-wk p₁
max {Γ = Γ} {π₁ = wk-wk π₁} (wkext-wk _) (wkext-wk _) wkext-id wkext-id = Γ , wk-id , wkext-id , wk-wk π₁ , wk-id , wk-id , wkext-id
max {Γ = Γ} {π₁ = wk-wk π₁} (wkext-wk _) (wkext-wk r₁) wkext-id {ρ₂ = wk-wk ρ₂} (wkext-wk r₂) = Γ , wk-id , wkext-id , wk-wk π₁ , wk-id , wk-wk ρ₂ , wkext-wk r₂
max {Γ = Γ ∙ X} {Δ = Δ} {π₁ = wk-wk π₁} (wkext-wk p₁) wkext-id {π₂ = wk-wk π₂} (wkext-wk p₂) wkext-id = Γ , wk-wk wk-id , wkext-wk wkext-id , π₁ , π₂ , π₁ , p₁
max {Γ = Γ ∙ X} {π₁ = wk-wk π₁} (wkext-wk p₁) wkext-id {π₂ = wk-wk π₂} (wkext-wk p₂) (wkext-wk _) = Γ , wk-wk wk-id , wkext-wk wkext-id , π₁ , π₂ , π₁ , p₁
max {Γ = Γ ∙ X} {π₁ = wk-wk π₁} (wkext-wk p₁) (wkext-wk _) {π₂ = wk-wk π₂} (wkext-wk p₂) wkext-id = Γ , wk-wk wk-id , wkext-wk wkext-id , π₁ , π₂ , π₂ , p₂
max {Γ = Γ ∙ X} {π₁ = wk-wk π₁} (wkext-wk p₁) {ρ₁ = wk-wk ρ₁} (wkext-wk r₁) {π₂ = wk-wk π₂} (wkext-wk p₂) {ρ₂ = wk-wk ρ₂} (wkext-wk r₂) = Γ , wk-wk wk-id , wkext-wk wkext-id , π₁ , π₂ , wk-trans π₁ (wk-wk ρ₁) , wkext-trans p₁ (wkext-wk r₁)

gc : MEnv Γ → {π : Γ ⊇ Δ} → WkExt π → MEnv Δ
gc ⋄ wkext-id = ⋄
gc (γ · 𝐖) wkext-id = γ · 𝐖
gc (γ · _) (wkext-wk p) = gc γ p
gc (γ ·﹝ M ╎ p ╎ K ﹞) wkext-id = γ ·﹝ M ╎ p ╎ K ﹞
gc (γ ·﹝ M ╎ p ╎ K ﹞) (wkext-wk p₁) = gc γ p₁

lookup : Γ ∋ X → MEnv Γ → OMVal Γ X
lookup here (γ · 𝐖) = wk-omval (wk-wk wk-id) 𝐖
lookup here (γ ·﹝ 𝐖 ╎ π ╎ K ﹞) = var here
lookup (there x) (γ · 𝐖) = wk-omval (wk-wk wk-id) (lookup x γ)
lookup (there x) (γ ·﹝ 𝐖 ╎ π ╎ K ﹞) = wk-omval (wk-wk wk-id) (lookup x γ)

lookup-gc : MEnv Γ → {π : Γ ⊇ Δ} → (WkExt π) → Γ ∋ X → Σ[ Ψ ∈ Ctx ] Σ[ π₁ ∈ Γ ⊇ Ψ ] (WkExt π₁ × Σ[ ρ ∈ Ψ ⊇ Δ ] (WkExt ρ × MEnv Ψ × OMVal Ψ X))
lookup-gc ⋄ wkext-id ()
lookup-gc (γ · 𝐖) {π = π} wkext-id here = _ , wk-id , wkext-id , π , wkext-id , γ · 𝐖 , (wk-omval (wk-wk wk-id) 𝐖)
lookup-gc (γ · 𝐖) {π = wk-cong π} wkext-id (there i) = _ , wk-cong π , wkext-id , wk-cong π , wkext-id , γ · 𝐖 , (lookup (there i) (γ · 𝐖))
lookup-gc (γ · 𝐖) {π = wk-wk π} wkext-id (there i) = ql (wk-absurd (wk-wk π) π) _
lookup-gc {Δ = Δ} (γ · unit) {π = wk-wk π} (wkext-wk wx) here = Δ , wk-wk π , wkext-wk wx , wk-id , wkext-id , gc γ wx , unit
lookup-gc (γ · pair 𝐕 𝐖) {π = wk-wk π} (wkext-wk wx) here = _ , wk-wk wk-id , wkext-wk wkext-id , π , wx , γ , pair 𝐕 𝐖
lookup-gc (γ · lam M) {π = wk-wk π} (wkext-wk wx) here = _ , wk-wk wk-id , wkext-wk wkext-id , π , wx , γ , lam M
lookup-gc (γ · var i) {π = wk-wk π} (wkext-wk wx) here =
  let IH = lookup-gc γ wx i in
  proj₁ IH , wk-wk (proj₁ (proj₂ IH)) , wkext-wk (proj₁ (proj₂ (proj₂ IH))) , proj₂ (proj₂ (proj₂ IH))

lookup-gc (γ · unit) {π = wk-wk π} (wkext-wk wx) (there i) =
  let IH = lookup-gc γ wx i in
  proj₁ IH , wk-wk (proj₁ (proj₂ IH)) , wkext-wk (proj₁ (proj₂ (proj₂ IH))) , proj₂ (proj₂ (proj₂ IH))
lookup-gc (γ · pair 𝐖 𝐖₁) {π = wk-wk π} (wkext-wk wx) (there i) =
  let IH = lookup-gc γ wx i in
  proj₁ IH , wk-wk (proj₁ (proj₂ IH)) , wkext-wk (proj₁ (proj₂ (proj₂ IH))) , proj₂ (proj₂ (proj₂ IH))
lookup-gc (γ · lam M) {π = wk-wk π} (wkext-wk wx) (there i) =
  let IH = lookup-gc γ wx i in
  proj₁ IH , wk-wk (proj₁ (proj₂ IH)) , wkext-wk (proj₁ (proj₂ (proj₂ IH))) , proj₂ (proj₂ (proj₂ IH))
lookup-gc (γ · var i₂) {π = wk-wk π} (wkext-wk wx) (there i) =
  let IH = lookup-gc γ wx i in
  proj₁ IH , wk-wk (proj₁ (proj₂ IH)) , wkext-wk (proj₁ (proj₂ (proj₂ IH))) , proj₂ (proj₂ (proj₂ IH))

lookup-gc (γ ·﹝ M ╎ wx ╎ K ﹞) wkext-id here = _ , wk-id , wkext-id , wk-id , wkext-id , γ ·﹝ M ╎ wx ╎ K ﹞ , var here
lookup-gc (γ ·﹝ M ╎ wx ╎ K ﹞) wkext-id (there i) = _ , wk-id , wkext-id , wk-id , wkext-id , γ ·﹝ M ╎ wx ╎ K ﹞ , lookup (there i) (γ ·﹝ M ╎ wx ╎ K ﹞)
lookup-gc (γ ·﹝ M ╎ wx ╎ K ﹞) {π = π} (wkext-wk wx₁) here = _ , wk-id , wkext-id , π , wkext-wk wx₁ , γ ·﹝ M ╎ wx ╎ K ﹞ , var here
lookup-gc (γ ·﹝ M ╎ wx ╎ K ﹞) (wkext-wk wx₁) (there i) =
  let IH = lookup-gc γ wx₁ i in
  proj₁ IH , wk-wk (proj₁ (proj₂ IH)) , wkext-wk (proj₁ (proj₂ (proj₂ IH))) , proj₂ (proj₂ (proj₂ IH))

eval : MEnv Γ → Γ ⊢ᵛ X → OMVal Γ X
eval γ (var i) = lookup i γ
eval γ (lam M) = lam M
eval γ (pair V W) = pair (eval γ V) (eval γ W)
eval γ unit = unit

eval-gc : MEnv Γ → {π : Γ ⊇ Δ} → (WkExt π) → Γ ⊢ᵛ X → Σ[ Ψ ∈ Ctx ] Σ[ π₁ ∈ Γ ⊇ Ψ ] (WkExt π₁ × Σ[ ρ ∈ Ψ ⊇ Δ ] (WkExt ρ × (MEnv Ψ × OMVal Ψ X)))
eval-gc γ wx (var i) = lookup-gc γ wx i
eval-gc γ {π = π} wx (lam M) = _ , wk-id , wkext-id , π , wx , γ , lam M
eval-gc γ wx (pair V W) =
  let
    IH₁ = eval-gc γ wx V
    IH₂ = eval-gc γ wx W
    m = max (proj₁ (proj₂ (proj₂ IH₁))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH₁))))) (proj₁ (proj₂ (proj₂ IH₂))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH₂)))))
  in
  proj₁ m , proj₁ (proj₂ m) , proj₁ (proj₂ (proj₂ m)) , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ m))))) , proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ m))))) , gc γ (proj₁ (proj₂ (proj₂ m))) , pair (wk-omval (proj₁ (proj₂ (proj₂ (proj₂ m)))) (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH₁))))))) (wk-omval (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ m))))) (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH₂)))))))
eval-gc {Δ = Δ} γ wkext-id unit = _ , wk-id , wkext-id , wk-id , wkext-id , γ , unit
eval-gc {Δ = Δ} (γ · x) (wkext-wk wx) unit =
  let
    IH = eval-gc γ wx unit
  in
  proj₁ IH , wk-wk (proj₁ (proj₂ IH)) , wkext-wk (proj₁ (proj₂ (proj₂ IH))) , proj₂ (proj₂ (proj₂ IH))
eval-gc {Δ = Δ} (γ ·﹝ x ╎ x₁ ╎ x₂ ﹞) (wkext-wk wx) unit =
  let
    IH = eval-gc γ wx unit
  in
  proj₁ IH , wk-wk (proj₁ (proj₂ IH)) , wkext-wk (proj₁ (proj₂ (proj₂ IH))) , proj₂ (proj₂ (proj₂ IH))

--------------------------------------------------------------------------

lookup-label : Γ ∋ `ℓ → MEnv Γ → CState
lookup-label here (γ · var i) = lookup-label i γ
lookup-label here (γ ·﹝ M ╎ p ╎ K ﹞) = ⟨ γ ╎ M ╎ p ╎ K ⟩
lookup-label (there i) (γ · 𝐖) = lookup-label i γ
lookup-label (there i) (γ ·﹝ M ╎ p ╎ K ﹞) = lookup-label i γ

eval-jump : Γ ⊢ᵛ `ℓ → MEnv Γ → CState
eval-jump (var i) γ = lookup-label i γ

--------------------------------------------------------------------------

wk-omval-term : (π : Γ ⊇ Δ) → {𝐖 : OMVal Δ X} → (OMValTerm 𝐖) → (OMValTerm (wk-omval π 𝐖))
wk-omval-term wk-ε is-unit = is-unit
wk-omval-term wk-ε (is-pair 𝐕 𝐖) = is-pair (wk-omval Wk.wk-ε 𝐕) (wk-omval Wk.wk-ε 𝐖)
wk-omval-term wk-ε (is-lam M) = is-lam (wk-comp (wk-cong Wk.wk-ε) M)
wk-omval-term (wk-cong π) is-unit = is-unit
wk-omval-term (wk-cong π) (is-pair 𝐕 𝐖) = is-pair (wk-omval (Wk.wk-cong π) 𝐕) (wk-omval (Wk.wk-cong π) 𝐖)
wk-omval-term (wk-cong π) (is-lam M) = is-lam (wk-comp (wk-cong (Wk.wk-cong π)) M)
wk-omval-term (wk-wk π) is-unit = is-unit
wk-omval-term (wk-wk π) (is-pair 𝐕 𝐖) = is-pair (wk-omval (Wk.wk-wk π) 𝐕) (wk-omval (Wk.wk-wk π) 𝐖)
wk-omval-term (wk-wk π) (is-lam M) = is-lam (wk-comp (wk-cong (Wk.wk-wk π)) M)

lookup-term : MEnv Γ → Γ ∋ X → TermType X → Σ[ 𝐖 ∈ OMVal Γ X ] (OMValTerm 𝐖)
lookup-term ⋄ () termtype
lookup-term (γ · unit) here termtype = unit , is-unit
lookup-term (γ · pair 𝐕 𝐖) here termtype = wk-omval (wk-wk wk-id) (pair 𝐕 𝐖) , is-pair (wk-omval (wk-wk wk-id) 𝐕) (wk-omval (wk-wk wk-id) 𝐖)
lookup-term (γ · lam M) here termtype = wk-omval (wk-wk wk-id) (lam M) , is-lam (wk-comp (wk-cong (wk-wk wk-id)) M)
lookup-term (γ · var i) here termtype = let IH = lookup-term γ i termtype in wk-omval (wk-wk wk-id) (proj₁ IH) , wk-omval-term (wk-wk wk-id) (proj₂ IH)
lookup-term (γ · unit) (there i) termtype = let IH = lookup-term γ i termtype in wk-omval (wk-wk wk-id) (proj₁ IH) , wk-omval-term (wk-wk wk-id) (proj₂ IH)
lookup-term (γ · pair 𝐖 𝐖₁) (there i) termtype = let IH = lookup-term γ i termtype in wk-omval (wk-wk wk-id) (proj₁ IH) , wk-omval-term (wk-wk wk-id) (proj₂ IH)
lookup-term (γ · lam M) (there i) termtype = let IH = lookup-term γ i termtype in wk-omval (wk-wk wk-id) (proj₁ IH) , wk-omval-term (wk-wk wk-id) (proj₂ IH)
lookup-term (γ · var _) (there i) termtype = let IH = lookup-term γ i termtype in wk-omval (wk-wk wk-id) (proj₁ IH) , wk-omval-term (wk-wk wk-id) (proj₂ IH)
lookup-term (γ ·﹝ M ╎ p ╎ K ﹞) (there i) termtype = let IH = lookup-term γ i termtype in wk-omval (wk-wk wk-id) (proj₁ IH) , wk-omval-term (wk-wk wk-id) (proj₂ IH)

proj₁-omval-term : Σ[ 𝐖 ∈ OMVal Γ (X `× Y) ] (OMValTerm 𝐖) → OMVal Γ X
proj₁-omval-term ((pair 𝐕 𝐖) , (is-pair 𝐕 𝐖)) = 𝐕
proj₁-omval-term ((var i) , ())

proj₁-omval : MEnv Γ → OMVal Γ (X `× Y) → OMVal Γ X
proj₁-omval _ (pair 𝐕 𝐖) = 𝐕
proj₁-omval ⋄ (var ())
proj₁-omval (γ · 𝐖) (var here) = proj₁-omval-term (lookup-term (γ · 𝐖) here is-pair-type)
proj₁-omval (γ · _) (var (there i)) = wk-omval (wk-wk wk-id) (proj₁-omval γ (var i))
proj₁-omval (γ ·﹝ _ ╎ _ ╎ _ ﹞) (var (there i)) = wk-omval (wk-wk wk-id) (proj₁-omval γ (var i))

proj₂-omval-term : Σ[ 𝐖 ∈ OMVal Γ (X `× Y) ] (OMValTerm 𝐖) → OMVal Γ Y
proj₂-omval-term ((pair 𝐕 𝐖) , (is-pair 𝐕 𝐖)) = 𝐖
proj₂-omval-term ((var i) , ())

proj₂-omval : MEnv Γ → OMVal Γ (X `× Y) → OMVal Γ Y
proj₂-omval _ (pair 𝐕 𝐖) = 𝐖
proj₂-omval ⋄ (var ())
proj₂-omval (γ · 𝐖) (var here) = proj₂-omval-term (lookup-term (γ · 𝐖) here is-pair-type)
proj₂-omval (γ · _) (var (there i)) = wk-omval (wk-wk wk-id) (proj₂-omval γ (var i))
proj₂-omval (γ ·﹝ _ ╎ _ ╎ _ ﹞) (var (there i)) = wk-omval (wk-wk wk-id) (proj₂-omval γ (var i))

eval₁ : Γ ⊢ᵛ (X `× Y) → MEnv Γ → OMVal Γ X
eval₁ W γ = proj₁-omval γ (eval γ W)

eval₂ : Γ ⊢ᵛ (X `× Y) → MEnv Γ → OMVal Γ Y
eval₂ W γ = proj₂-omval γ (eval γ W)

lam-term-to-comp : Σ[ 𝐖 ∈ OMVal Γ (X `⇒ Y) ] (OMValTerm 𝐖) → (Γ ∙ X) ⊢ᶜ Y
lam-term-to-comp ((lam M) , (is-lam M)) = M
lam-term-to-comp ((var i) , ())

lam-to-comp :  MEnv Γ → OMVal Γ (X `⇒ Y) → (Γ ∙ X) ⊢ᶜ Y
lam-to-comp γ (lam M) = M
lam-to-comp γ (var i) = lam-term-to-comp (lookup-term γ i is-func-type)

eval-app : MEnv Γ → Γ ⊢ᵛ (X `⇒ Y) → Γ ⊢ᵛ X
           → {π : Γ ⊇ Δ} → WkExt π → CStack Δ Y → CState
eval-app γ V W p K =
  let
    v = eval-gc γ p V
    w = eval-gc γ p W
    M = lam-to-comp (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ v)))))) (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ v))))))
    mx = max (proj₁ (proj₂ (proj₂ v))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ v))))) (proj₁ (proj₂ (proj₂ w))) (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ w)))))
    δ = gc γ (proj₁ (proj₂ (proj₂ mx)))
    𝐖 = wk-omval ((proj₁ (proj₂ (proj₂ (proj₂ (proj₂ mx)))))) (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ w))))))
  in
  ⟨ δ · 𝐖 ╎ wk-comp (wk-cong (proj₁ ((proj₂ (proj₂ (proj₂ mx)))))) M ╎ wkext-wk (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ mx)))))) ╎ K ⟩

--------------------------------------------------------------------------

eval→-helper : (W : Γ ⊢ᵛ X) → (γ : MEnv Γ) → {π : Γ ⊇ Δ} → (p : WkExt π) → (K : CStack Δ X) → CState
eval→-helper W γ p K =
  let
    a = eval-gc γ p W
    𝐖 = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ a)))))
    δ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ a)))))
    r = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ a))))
  in
  ⟨ δ ； 𝐖 ╎ r ╎ K ⟩

wkext-id-π : WkExt {Γ = Γ} wk-id
wkext-id-π = wkext-id

data _→ᶜ_ : CState → CState → Set where

  eval→ :    {W : Γ ⊢ᵛ X} {γ : MEnv Γ} {π : Γ ⊇ Δ} {p : WkExt π} {K : CStack Δ X}
             -------------------------------------------
             →  ⟨ γ ╎ return W ╎ p ╎ K ⟩ →ᶜ eval→-helper W γ p K

  return→ :  {𝐖 : OMVal Γ X} {M : (Δ ∙ X) ⊢ᶜ Y} {γ : MEnv Γ} {Ψ : Ctx} {K : CStack Ψ Y}
             {π : Γ ⊇ Δ} {p : WkExt π} {π₁ : Δ ⊇ Ψ} {p₁ : WkExt π₁}
             --------------------------------------------------------------
             →  ⟨ γ ； 𝐖 ╎ p ╎ < M ； p₁ >∷ K ⟩ →ᶜ ⟨ γ · 𝐖 ╎ wk-comp (wk-cong π) M ╎ wkext-wk (wkext-trans p p₁) ╎ K ⟩

  push→ :    {M : Γ ⊢ᶜ X} {N : (Γ ∙ X) ⊢ᶜ Y} {γ : MEnv Γ} {π : Γ ⊇ Δ} {p : WkExt π} {K : CStack Δ Y}
             ----------------------------------------------------------------
             →  ⟨ γ ╎ push M N ╎ p ╎ K ⟩ →ᶜ ⟨ γ ╎ M ╎ wkext-id-π ╎ < N ； p >∷ K ⟩

  sub→ :     {M : (Γ ∙ `ℓ) ⊢ᶜ X} {N : Γ ⊢ᶜ X} {γ : MEnv Γ} {π : Γ ⊇ Δ} {p : WkExt π} {K : CStack Δ X}
             ----------------------------------------------------------------
             →  ⟨ γ ╎ sub M N ╎ p ╎ K ⟩ →ᶜ ⟨ γ ·﹝ N ╎ p ╎ K ﹞ ╎ M ╎ wkext-wk p ╎ K ⟩

  var→ :     {W : Γ ⊢ᵛ `ℓ} {γ : MEnv Γ} {π : Γ ⊇ Δ} {p : WkExt π} {K : CStack Δ X}
             ------------------------------------------
             →  ⟨ γ ╎ var W ╎ p ╎ K ⟩ →ᶜ eval-jump W γ

  pmᶜ→ :     {W : Γ ⊢ᵛ (X `× Y)} {γ : MEnv Γ}
             {M : (Γ ∙ X ∙ Y) ⊢ᶜ Z} {π : Γ ⊇ Δ} {p : WkExt π} {K : CStack Δ Z}
             -------------------------------------------------------------
             →  ⟨ γ ╎ pm W M ╎ p ╎ K ⟩ →ᶜ ⟨ γ · eval₁ W γ · wk-omval (wk-wk wk-id) (eval₂ W γ) ╎ M ╎ wkext-wk (wkext-wk p) ╎ K ⟩

  app→ :     {V : Γ ⊢ᵛ (X `⇒ Y)} {W : Γ ⊢ᵛ X} {γ : MEnv Γ} {π : Γ ⊇ Δ} {p : WkExt π} {K : CStack Δ Y}
             ----------------------------------------------------------------
             →  ⟨ γ ╎ app V W ╎ p ╎ K ⟩ →ᶜ eval-app γ V W p K


determinismꟲ : {ℛ : Ty} {σ σ₁ : CState} (σ→σ₁₁ σ→σ₁₂ : σ →ᶜ σ₁) → (σ→σ₁₁ ≡ σ→σ₁₂)
determinismꟲ eval→ eval→ = refl
determinismꟲ return→ return→ = refl
determinismꟲ push→ push→ = refl
determinismꟲ sub→ sub→ = refl
determinismꟲ var→ var→ = refl
determinismꟲ pmᶜ→ pmᶜ→ = refl
determinismꟲ app→ app→ = refl

open import Inception.Rewriting.Reduction _→ᶜ_

progress : (σ : CState) → Step? σ
progress ⟨ γ ； 𝐖 ╎ p ╎ ◻ ⟩ = done (λ ())
progress ⟨ γ ； 𝐖 ╎ p ╎ < x ； p₁ >∷ K ⟩ = next return→
progress ⟨ γ ╎ return V ╎ p ╎ K ⟩ = next eval→
progress ⟨ γ ╎ pm V M ╎ p ╎ K ⟩ = next pmᶜ→
progress ⟨ γ ╎ push M N ╎ p ╎ K ⟩ = next push→
progress ⟨ γ ╎ app V W ╎ p ╎ K ⟩ = next app→
progress ⟨ γ ╎ var V ╎ p ╎ K ⟩ = next var→
progress ⟨ γ ╎ sub M N ╎ p ╎ K ⟩ = next sub→


-- A Normal CState is a halting state and of the form ⟨ γ ； 𝐖 ╎ p ╎ ◻ ⟩.
halting-state :    (σ : CState) → Normal σ
                 → Σ[ Γ ∈ Ctx ] Σ[ π ∈ Γ ⊇ ε ] Σ[ p ∈ WkExt π ] Σ[ 𝐖 ∈ OMVal Γ ℛ ] Σ[ γ ∈ MEnv Γ ] σ ≡ ⟨ γ ； 𝐖 ╎ p ╎ ◻ ⟩
halting-state ⟨ γ ； 𝐖 ╎ p ╎ ◻ ⟩ normal = _ , _ , p , 𝐖 , γ , refl
halting-state ⟨ γ ； 𝐖 ╎ p ╎ < _ ； _ >∷ K ⟩ normal = ql (normal return→) _
halting-state ⟨ γ ╎ return _ ╎ p ╎ K ⟩ normal = ql (normal eval→) _
halting-state ⟨ γ ╎ pm _ _ ╎ p ╎ K ⟩ normal = ql (normal pmᶜ→) _
halting-state ⟨ γ ╎ push _ _ ╎ p ╎ K ⟩ normal = ql (normal push→) _
halting-state ⟨ γ ╎ app _ _ ╎ p ╎ K ⟩ normal = ql (normal app→) _
halting-state ⟨ γ ╎ var _ ╎ p ╎ K ⟩ normal = ql (normal var→) _
halting-state ⟨ γ ╎ sub _ _ ╎ p ╎ K ⟩ normal = ql (normal sub→) _
