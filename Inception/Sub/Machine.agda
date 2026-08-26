{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Machine where

open import Inception.Sub.Syntax
open import Inception.Prelude

open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

---------------------------------------------------------------------------------

infixl 27 _،_
infix  20 ⭭_
infix  19 _∷_
infixr 17 _→ᵖ⟨_⟩．
infixr 15 _→ᵖ⟨_⟩_
infix  15 _→ᵖ_
infixr 10 _⨾_

---------------------------------------------------------------------------------
-- ENVIRONMENTS

mutual

  data CompStack {Z₀ : Ty} : (X : Ty) → Set where

    ◻     :   CompStack Z₀

    _⊲_⦂⦂_    : Comp (Γ ∙ Y) X → (γ : Env {Z₀ = Z₀} Γ) → (tail : CompStack {Z₀ = Z₀} X) → CompStack Y

  data Value {Z₀ : Ty} : Ty → Set where

    unitᵛ : Value {Z₀ = Z₀} `Unit

    pairᵛ : (𝐖₁ : Value {Z₀ = Z₀} X₁) → (𝐖₂ : Value {Z₀ = Z₀} X₂) → Value (X₁ `× X₂)

    cloᵛ  : {Γ : Ctx} → (M : Comp (Γ ∙ X) Y) → (γ : Env {Z₀ = Z₀} Γ) → Value (X `⇒ Y)

    jumpᵛ : {Γ : Ctx} → (M : Comp Γ X) → (γ : Env {Z₀ = Z₀} Γ) → (cs : CompStack {Z₀ = Z₀} X) → Value `V

  data Env {Z₀ : Ty} : Ctx → Set where
    ∅   : Env {Z₀ = Z₀} ε
    _،_ : Env {Z₀ = Z₀} Γ → Value {Z₀ = Z₀} X → Env {Z₀ = Z₀} (Γ ∙ X)

lookup : (i : Γ ∋ X) → Env {Z₀ = Z₀} Γ → Value {Z₀ = Z₀} X
lookup Cx.h (γ ، W') = W'
lookup (Cx.t i) (γ ، W') = lookup i γ

---------------------------------------------------------------------------------
-- MACHINE FOR PURE TERMS

data TermWithHole {Z₀ : Ty} : (X : Ty) → Set where

    ⭭_ : (W' : Value {Z₀ = Z₀} X) → TermWithHole X

    ⇡ : (W : Pure Γ X) → (Env {Z₀ = Z₀} Γ) → TermWithHole X

    ⇡ᴾᴹ : (Wₕₒₗₑ : Pure Γ (X₁ `× X₂)) → (W₂ : Pure (Γ ∙ X₁ ∙ X₂) Y) → (Env {Z₀ = Z₀} Γ) → TermWithHole Y

    ⇡ᴸ : (Wₕₒₗₑ : Pure Γ X₁) → (W₂ : Pure Γ X₂) → (Env {Z₀ = Z₀} Γ) → TermWithHole (X₁ `× X₂)

    ⇡ᴿ  : (W₁ : Value {Z₀ = Z₀} X₁) → (Wₕₒₗₑ : Pure Γ X₂) → (Env {Z₀ = Z₀} Γ) → TermWithHole (X₁ `× X₂)

data IsEmpty : Set where
    non-empty : IsEmpty
    empty : IsEmpty

private variable
    b b' : IsEmpty

data BottomTypeEqualsNextType : IsEmpty → Ty → Ty → Set where

    🗆 : BottomTypeEqualsNextType empty X X

    🗇 : BottomTypeEqualsNextType non-empty X Y

data PureStack {Z₀ : Ty} : IsEmpty → Ty → Set where

    □ : PureStack {Z₀ = Z₀} empty Z₁

    _∷_ : TermWithHole {Z₀ = Z₀} X → (tail : PureStack {Z₀ = Z₀} b Z₁) → {↥ : BottomTypeEqualsNextType b X Z₁} → PureStack non-empty Z₁


data PureState {Z₀ : Ty} : Ty → Set where

    ⟨_⟩ : PureStack {Z₀ = Z₀} non-empty Z₁ → PureState {Z₀ = Z₀} Z₁

_⧺_ : {Z₀ : Ty} → PureStack {Z₀ = Z₀} b Z₁ → PureStack {Z₀ = Z₀} non-empty Z₁' → PureStack {Z₀ = Z₀} non-empty Z₁'
□ ⧺ lower = lower
(W ∷ upper) ⧺ lower = (W ∷ (upper ⧺ lower)) {↥ = 🗇}

_⧻_ : {Z₀ : Ty} → (upper : PureState {Z₀ = Z₀} Z₁) → PureStack {Z₀ = Z₀} non-empty Z₁' → PureState {Z₀ = Z₀} Z₁'
⟨ upper ⟩ ⧻ lower = ⟨ upper ⧺ lower ⟩

data _→ᵖ_ {Z₀ : Ty} {Z₁ : Ty} : PureState {Z₀ = Z₀} Z₁ → PureState {Z₀ = Z₀} Z₁ → Set where

    ∘var  :    {i : Γ ∋ X} {γ : Env {Z₀ = Z₀} Γ} → {tail : PureStack {Z₀ = Z₀} b Z₁} → {↥ : BottomTypeEqualsNextType b X Z₁}
              ----------------------------------------------------------------
                → ⟨ (⇡ (var i) γ ∷ tail) {↥ = ↥} ⟩ →ᵖ ⟨ (⭭ (lookup i γ) ∷ tail) {↥ = ↥} ⟩

    ∘lam   :  {M : Comp (Γ ∙ X) Y} → {γ  : Env {Z₀ = Z₀} Γ} → {tail : PureStack {Z₀ = Z₀} b Z₁} → {↥ : BottomTypeEqualsNextType b (X `⇒ Y) Z₁}
              ---------------------------------------------------------------------------
            →     ⟨ (⇡ (lam M) γ ∷ tail) {↥ = ↥} ⟩ →ᵖ ⟨ (⭭ (cloᵛ M γ) ∷ tail) {↥ = ↥} ⟩

    ∘pair  :  {γ : Env {Z₀ = Z₀} Γ} {W₁ : Pure Γ X₁} → {W₂ : Pure Γ X₂} → {tail : PureStack {Z₀ = Z₀} b Z₁} → {↥ : BottomTypeEqualsNextType b (X₁ `× X₂) Z₁}
              ---------------------------------------------------------------------------
            →     ⟨ (⇡ (pair W₁ W₂) γ ∷ tail) {↥ = ↥} ⟩ →ᵖ ⟨ (⇡ W₁ γ ∷ ((⇡ᴸ W₁ W₂ γ ∷ tail) {↥ = ↥})) {↥ = 🗇} ⟩

    ∘pm    :  {γ : Env {Z₀ = Z₀} Γ} {W₁ : Pure Γ (X₁ `× X₂)} → {W₂ : Pure (Γ ∙ X₁ ∙ X₂) Y} → {tail : PureStack {Z₀ = Z₀} b Z₁ } → {↥ : BottomTypeEqualsNextType b Y Z₁}
              ---------------------------------------------------------------------------
            →     ⟨ (⇡ (pm W₁ W₂) γ ∷ tail) {↥ = ↥} ⟩ →ᵖ ⟨ (⇡ W₁ γ ∷ (⇡ᴾᴹ W₁ W₂ γ ∷ tail) {↥ = ↥}) {↥ = 🗇} ⟩

    ∘unit  :  {γ  : Env {Z₀ = Z₀} Γ} → {tail : PureStack {Z₀ = Z₀} b Z₁} → {↥ : BottomTypeEqualsNextType b `Unit Z₁}
              ---------------------------------------------------------------------------
            →     ⟨ (⇡ unit γ ∷ tail) {↥ = ↥} ⟩ →ᵖ ⟨ (⭭ unitᵛ ∷ tail) {↥ = ↥} ⟩

    ∙W∷l   :  {γ : Env {Z₀ = Z₀} Γ} {W₁' : Value X₁} → {W₁ : Pure Γ X₁} → {W₂ : Pure Γ X₂}
            → {tail : PureStack {Z₀ = Z₀} b Z₁} → {↥ : BottomTypeEqualsNextType b (X₁ `× X₂) Z₁}
              ---------------------------------------------------------------------------
            →     ⟨ (⭭ W₁' ∷ ((⇡ᴸ W₁ W₂ γ ∷ tail) {↥ = ↥})) {↥ = 🗇} ⟩ →ᵖ ⟨ (⇡ W₂ γ ∷ ((⇡ᴿ W₁' W₂ γ ∷ tail) {↥ = ↥})) {↥ = 🗇} ⟩

    ∙W∷r   :  {γ : Env {Z₀ = Z₀} Γ} {W₂' : Value X₂} → {W₁' : Value X₁} → {W₂ : Pure Γ X₂}
            → {tail : PureStack {Z₀ = Z₀} b Z₁} → {↥ : BottomTypeEqualsNextType b (X₁ `× X₂) Z₁}
              ---------------------------------------------------------------------------
            → ⟨ (⭭ W₂' ∷ ((⇡ᴿ W₁' W₂ γ ∷ tail) {↥ = ↥})) {↥ = 🗇} ⟩ →ᵖ ⟨ (⭭ pairᵛ W₁' W₂' ∷ tail) {↥ = ↥} ⟩

    ∙pair∷pm  :  {γ : Env {Z₀ = Z₀} Γ} {W₁' : Value X₁} → {W₂' : Value X₂} → {W₀ : Pure Γ (X₁ `× X₂)} → {W₃ : Pure (Γ ∙ X₁ ∙ X₂) Y}
            → {tail : PureStack {Z₀ = Z₀} b Z₁} → {↥ : BottomTypeEqualsNextType b Y Z₁}
              ---------------------------------------------------------------------------
            →     ⟨ (⭭ pairᵛ W₁' W₂' ∷ ((⇡ᴾᴹ W₀ W₃ γ ∷ tail) {↥ = ↥})) {↥ = 🗇} ⟩ →ᵖ  ⟨ (⇡ W₃ (γ ، W₁' ، W₂') ∷ tail) {↥ = ↥} ⟩

data _↠ᵛ_ {Z₀ Z₁ : Ty} : PureState {Z₀ = Z₀} Z₁ → PureState {Z₀ = Z₀} Z₁ → Set where

  _→ᵖ⟨_⟩． : (S : PureState Z₁) → {S' : PureState Z₁} → (laststep : S →ᵖ S') → S ↠ᵛ S'

  _→ᵖ⟨_⟩_ : (S : PureState Z₁) → {S' S'' : PureState Z₁} → S →ᵖ S' → S' ↠ᵛ S'' → S ↠ᵛ S''

_⨾_ : {Z₀ : Ty} {F S T : PureState {Z₀ = Z₀} Z₁} → (F ↠ᵛ S) → (S ↠ᵛ T) → (F ↠ᵛ T)
_⨾_ (F →ᵖ⟨ F>S ⟩．) S>>T = F →ᵖ⟨ F>S ⟩ S>>T
_⨾_ (F →ᵖ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᵖ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ S₂>>T)

⟨_⟩⧻_ : {Z₀ : Ty} {from : PureState {Z₀ = Z₀} Z₁} → {to : PureState {Z₀ = Z₀} Z₁} → (F>T : from →ᵖ to) → (tail : PureStack {Z₀ = Z₀} non-empty Z₁') → (from ⧻ tail) →ᵖ (to ⧻ tail)
⟨ ∘var ⟩⧻ tail = ∘var
⟨ ∘lam ⟩⧻ tail = ∘lam
⟨ ∘pair ⟩⧻ tail = ∘pair
⟨ ∘pm ⟩⧻ tail = ∘pm
⟨ ∘unit ⟩⧻ tail = ∘unit
⟨ ∙W∷l ⟩⧻ tail = ∙W∷l
⟨ ∙W∷r ⟩⧻ tail = ∙W∷r
⟨ ∙pair∷pm ⟩⧻ tail = ∙pair∷pm

⟪_⟫⧻_ : {from : PureState {Z₀ = Z₀} Z₁} → {to : PureState {Z₀ = Z₀} Z₁} → (F>T : from ↠ᵛ to) → (tail : PureStack {Z₀ = Z₀} non-empty Z₁') → (from ⧻ tail) ↠ᵛ (to ⧻ tail)
⟪ _ →ᵖ⟨ F>T ⟩． ⟫⧻ tail =  _ →ᵖ⟨ ⟨ F>T ⟩⧻ tail ⟩．
⟪ _ →ᵖ⟨ F>T ⟩ F>>T ⟫⧻ tail =   _ →ᵖ⟨ ⟨ F>T ⟩⧻ tail ⟩ (⟪ F>>T ⟫⧻ tail)

record PureSteps {Z₀ : Ty} (W : Pure Γ X) (γ : Env {Z₀ = Z₀} Γ) : Set where
  field
    result : Value {Z₀ = Z₀} X
    steps  : ⟨ ((⇡ W γ ∷ □) {↥ = 🗆}) ⟩ ↠ᵛ ⟨ ((⭭ result ∷ □) {↥ = 🗆}) ⟩
open PureSteps

proj₁-val : {Z₀ : Ty} → Value {Z₀ = Z₀} (X `× Y) → Value {Z₀ = Z₀} X
proj₁-val (pairᵛ W₁ W₂) = W₁

proj₂-val : {Z₀ : Ty} → Value {Z₀ = Z₀} (X `× Y) → Value {Z₀ = Z₀} Y
proj₂-val (pairᵛ W₁ W₂) = W₂

pair-val : {Z₀ : Ty} → (W : Value {Z₀ = Z₀} (X `× Y)) → (pairᵛ (proj₁-val W) (proj₂-val W) ≡ W)
pair-val (pairᵛ W₁ W₂) = refl

run-pure : {Z₀ : Ty} → (W : Pure Γ X) → (γ : Env {Z₀ = Z₀} Γ) → PureSteps W γ
run-pure (var i) γ = record { result = lookup i γ ; steps = ⟨ ⇡ (var i) γ ∷ □ ⟩ →ᵖ⟨ ∘var ⟩． }
run-pure (lam M) γ = record { result = cloᵛ M γ ; steps = ⟨ ⇡ (lam M) γ ∷ □ ⟩ →ᵖ⟨ ∘lam ⟩． }
run-pure (pair W₁ W₂) γ =
  let
    IH₁ = run-pure W₁ γ
    IH₂ = run-pure W₂ γ
    trace = _ →ᵖ⟨ ∘pair ⟩． ⨾ ⟪ steps IH₁ ⟫⧻ _ ⨾ _ →ᵖ⟨ ∙W∷l ⟩． ⨾ (⟪ steps IH₂ ⟫⧻ _) ⨾ _ →ᵖ⟨ ∙W∷r ⟩．
  in
  record { result = pairᵛ (result IH₁) (result IH₂) ; steps = trace }
run-pure (pm W₁ W₂) γ =
  let
    IH₁ = run-pure W₁ γ
    IH₂ = run-pure W₂ (γ ، proj₁-val (result IH₁) ، proj₂-val (result IH₁))
    ∙pair∷pm' = subst (λ x → ⟨ (⭭ x) ∷ (⇡ᴾᴹ W₁ W₂ γ ∷ □) ⟩ →ᵖ ⟨ ⇡ W₂ (γ ، proj₁-val (result IH₁) ، proj₂-val (result IH₁)) ∷ □ ⟩) (pair-val (result IH₁)) ∙pair∷pm
  in
  record { result = result IH₂ ; steps = _ →ᵖ⟨ ∘pm ⟩． ⨾ ⟪ steps IH₁ ⟫⧻ _ ⨾ _ →ᵖ⟨ ∙pair∷pm' ⟩． ⨾ steps IH₂ }
run-pure unit γ = record { result = unitᵛ ; steps = ⟨ ⇡ unit γ ∷ □ ⟩ →ᵖ⟨ ∘unit ⟩． }

determinismⱽ : {Z₀ : Ty} {S S' : PureState {Z₀ = Z₀} Z₁} → (S→S'₁ S→S'₂ : S →ᵖ S') → (S→S'₁ ≡ S→S'₂)
determinismⱽ ∘var ∘var = refl
determinismⱽ ∘lam ∘lam = refl
determinismⱽ ∘pair ∘pair = refl
determinismⱽ ∘pm ∘pm = refl
determinismⱽ ∘unit ∘unit = refl
determinismⱽ ∙W∷l ∙W∷l = refl
determinismⱽ ∙W∷r ∙W∷r = refl
determinismⱽ ∙pair∷pm ∙pair∷pm = refl

---------------------------------------------------------------------------------
-- MACHINE FOR EFFECTFUL TERMS / COMPUTATIONS

data CompState {Z₀ : Ty} : Set where

      ⟨return_╎_⟩ : (W' : Value {Z₀ = Z₀} X) → (k : CompStack {Z₀ = Z₀} X) → CompState {Z₀ = Z₀}
      ⟨_╎_╎_⟩ : (M : Comp Γ X) → (γ : Env {Z₀ = Z₀} Γ) → (k : CompStack {Z₀ = Z₀} X) → CompState {Z₀ = Z₀}

jump-to-state : {Z₀ : Ty} → Value {Z₀ = Z₀} `V → CompState {Z₀ = Z₀}
jump-to-state (jumpᵛ M γ k) = ⟨ M ╎ γ ╎ k ⟩

clo-to-comp : {Z₀ : Ty} → Value {Z₀ = Z₀} (X `⇒ Y) → Σ[ Γ ∈ Ctx ] Comp (Γ ∙ X) Y × Env {Z₀ = Z₀} Γ
clo-to-comp (cloᵛ M γ) = _ , M , γ

clo-val : {Z₀ : Ty} → (W : Value {Z₀ = Z₀} (X `⇒ Y)) → (cloᵛ (proj₁ (proj₂ (clo-to-comp W))) (proj₂ (proj₂ (clo-to-comp W))) ≡ W)
clo-val (cloᵛ M γ) = refl

apply : {Z₀ : Ty} → Pure Γ (X `⇒ Y) → Pure Γ X → Env {Z₀ = Z₀} Γ → CompStack {Z₀ = Z₀} Y → CompState {Z₀ = Z₀}
apply W₁ W₂ γ k = ⟨ proj₁ (proj₂ (clo-to-comp (result (run-pure W₁ γ)))) ╎ proj₂ (proj₂ (clo-to-comp (result (run-pure W₁ γ)))) ، result (run-pure W₂ γ) ╎ k ⟩


data _→ᶜ_ {Z₀ : Ty} : CompState {Z₀ = Z₀} → CompState {Z₀ = Z₀} → Set where

      ∘return  :      {W : Pure Γ X} → {γ : Env Γ} {k : CompStack X}
                    ----------------------------------------------------------------
                    → ⟨ return W ╎ γ ╎ k ⟩ →ᶜ ⟨return (result (run-pure W γ)) ╎ k ⟩

      ∙return  :    {W' : Value X} → {M : Comp (Δ ∙ X) Y} → {γ : Env Δ} → {k : CompStack Y}
                ----------------------------------------------------------------
                  → ⟨return W' ╎ M ⊲ γ ⦂⦂ k ⟩ →ᶜ ⟨ M ╎ γ ، W' ╎ k ⟩

      ∘push    :    {M₁ : Comp Γ X} → {M₂ : Comp (Γ ∙ X) Y} → {γ : Env Γ} → {k : CompStack Y}
                ----------------------------------------------------------------
                  → ⟨ push M₁ M₂ ╎ γ ╎ k ⟩ →ᶜ ⟨ M₁ ╎ γ ╎ M₂ ⊲ γ ⦂⦂ k ⟩

      ∘sub     :    {M₁ : Comp (Γ ∙ `V) X} → {M₂ : Comp Γ X} → {γ : Env Γ} → {k : CompStack X}
                ----------------------------------------------------------------
                  → ⟨ sub M₁ M₂ ╎ γ ╎ k ⟩ →ᶜ ⟨ M₁ ╎ γ ، (jumpᵛ M₂ γ k) ╎ k ⟩

      ∘var     :   {W : Pure Γ `V} → {γ : Env Γ} → {k : CompStack X}
               -------------------------------------------------------------
                  → ⟨ var W ╎ γ ╎ k ⟩ →ᶜ jump-to-state (result (run-pure W γ))

      ∘pm      :    {W : Pure Γ (X `× Y)} → {γ : Env Γ} → {M : Comp (Γ ∙ X ∙ Y) Z} → {k : CompStack Z}
                ----------------------------------------------------------------
                  → ⟨ pm W M ╎ γ ╎ k ⟩ →ᶜ ⟨ M ╎ γ ، proj₁-val (result (run-pure W γ)) ، proj₂-val (result (run-pure W γ)) ╎ k ⟩

      ∘app     :   {W₁ : Pure Γ (X `⇒ Y)} → {W₂ : Pure Γ X} → {γ : Env Γ} → {k : CompStack Y}
                    ----------------------------------------------------------------
                  →  ⟨ app W₁ W₂ ╎ γ ╎ k ⟩ →ᶜ apply W₁ W₂ γ k



determinismꟲ : {Z₀ : Ty} {S S' : CompState {Z₀ = Z₀}} (S→S'₁ S→S'₂ : S →ᶜ S') → (S→S'₁ ≡ S→S'₂)
determinismꟲ ∘return ∘return = refl
determinismꟲ ∙return ∙return = refl
determinismꟲ ∘push ∘push = refl
determinismꟲ ∘sub ∘sub = refl
determinismꟲ ∘var ∘var = refl
determinismꟲ ∘pm ∘pm = refl
determinismꟲ ∘app ∘app = refl

open Inception.Prelude.RTC renaming (_~>⟨_⟩_ to _→ᶜ⟨_⟩_)

_→ᶜ*_ : {Z₀ : Ty} → CompState {Z₀ = Z₀} → CompState {Z₀ = Z₀} → Set
_→ᶜ*_ {Z₀ = Z₀} = _~>*_ (_→ᶜ_ {Z₀ = Z₀})

_⨾ᶜ_ : {Z₀ : Ty} → {F S T : CompState {Z₀ = Z₀}} → (F →ᶜ* S) → (S →ᶜ* T) → (F →ᶜ* T)
_⨾ᶜ_ (S ◼) S>>T = S>>T
_⨾ᶜ_ (F →ᶜ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᶜ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ᶜ S₂>>T)


data SN {Z₀ : Ty} (σ : CompState {Z₀ = Z₀}) : Set where
  sn : (∀ {σ'} → σ →ᶜ σ' → SN σ') → SN σ

Rᵛ : {Z₀ : Ty} → (X : Ty) → Value {Z₀ = Z₀} X → Set
Rᵏ : {Z₀ : Ty} → (X : Ty) → CompStack {Z₀ = Z₀} X → Set

Rᵛ `Unit unitᵛ = ⊤
Rᵛ (X `× Y) (pairᵛ W₁ W₂) = Rᵛ X W₁ × Rᵛ Y W₂
Rᵛ {Z₀ = Z₀} (X `⇒ Y) (cloᵛ M γ) = ∀ {W' : Value {Z₀ = Z₀} X} → Rᵛ X W' → ∀ {k : CompStack {Z₀ = Z₀} Y} → Rᵏ Y k → SN ⟨ M ╎ γ ، W' ╎ k ⟩
Rᵛ `V (jumpᵛ M γ k) = SN ⟨ M ╎ γ ╎ k ⟩

Rᵏ {Z₀ = Z₀} X k = ∀ {W : Value {Z₀ = Z₀} X} → Rᵛ X W → SN ⟨return W ╎ k ⟩

Rᴱ : {Z₀ : Ty} → Env {Z₀ = Z₀} Γ → Set
Rᴱ {Γ = Γ} γ = ∀ {X : Ty} → (i : Γ ∋ X) → Rᵛ X (lookup i γ)

Rᴱ-ext : {Z₀ : Ty} {γ : Env {Z₀ = Z₀} Γ} {W : Value {Z₀ = Z₀} X} → Rᴱ γ → Rᵛ X W → Rᴱ (γ ، W)
Rᴱ-ext Rγ RW Cx.h = RW
Rᴱ-ext Rγ RW (Cx.t i) = Rγ i

rv≡sn : {Z₀ : Ty} → (W : Pure Γ `V) → (γ : Env {Z₀ = Z₀} Γ) → Rᵛ `V (result (run-pure W γ)) ≡ SN (jump-to-state (result (run-pure W γ)))
rv≡sn (var Cx.h) (γ ، jumpᵛ _ _ _) = refl
rv≡sn (var (Cx.t i)) (γ ، _) = rv≡sn (var i) γ
rv≡sn (pm W₁ W₂) ∅ = rv≡sn W₂ (∅ ، proj₁-val (result (run-pure W₁ ∅)) ، proj₂-val (result (run-pure W₁ ∅)))
rv≡sn (pm W₁ W₂) (γ ، W') = rv≡sn W₂ (γ ، W' ، proj₁-val (result (run-pure W₁ (γ ، W'))) ، proj₂-val (result (run-pure W₁ (γ ، W'))))

mutual

  Rʲ : {Z₀ : Ty} {γ : Env {Z₀ = Z₀} Γ} → (W : Pure Γ `V) → Rᴱ γ → Rᵛ _ (result (run-pure W γ))
  Rʲ {γ = γ} (var i) Rγ = Rγ i
  Rʲ {γ = γ} (pm W₁ W₂) Rγ =
    let
      IH = fundamentalᵖ W₁ Rγ
      W₁' = result (run-pure W₁ γ)
      IH' : Rᵛ _ (pairᵛ (proj₁-val W₁') (proj₂-val W₁'))
      IH' = subst (λ x → Rᵛ _ x) (sym (pair-val W₁')) IH
    in
    Rʲ W₂ (Rᴱ-ext (Rᴱ-ext Rγ (proj₁ IH')) (proj₂ IH'))

  fundamentalᵖ  : {Z₀ : Ty} → (W : Pure Γ X) → {γ : Env {Z₀ = Z₀} Γ} → Rᴱ γ → Rᵛ X (result (run-pure W γ))
  fundamentalᵖ (var i) Rγ = Rγ i
  fundamentalᵖ (lam M) Rγ RW Rk = fundamentalᶜ M (Rᴱ-ext Rγ RW) Rk
  fundamentalᵖ (pair W₁ W₂) Rγ = (fundamentalᵖ W₁ Rγ) , (fundamentalᵖ W₂ Rγ)
  fundamentalᵖ (pm W₁ W₂) {γ = γ} Rγ =
    let
      IH = fundamentalᵖ W₁ Rγ
      W₁' = result (run-pure W₁ γ)
      IH' : Rᵛ _ (pairᵛ (proj₁-val W₁') (proj₂-val W₁'))
      IH' = subst (λ x → Rᵛ _ x) (sym (pair-val W₁')) IH
    in
    fundamentalᵖ W₂ (Rᴱ-ext (Rᴱ-ext Rγ (proj₁ IH')) (proj₂ IH'))
  fundamentalᵖ unit Rγ = tt

  fundamentalᶜ : {Z₀ : Ty} → (M : Comp Γ X) → {γ : Env {Z₀ = Z₀} Γ} → Rᴱ γ → {k : CompStack {Z₀ = Z₀} X} → Rᵏ X k → SN ⟨ M ╎ γ ╎ k ⟩
  fundamentalᶜ (return W) Rγ Rk = sn λ { ∘return → Rk (fundamentalᵖ W Rγ)}
  fundamentalᶜ (pm W M) {γ = γ} Rγ Rk =
    let
      IH = fundamentalᵖ W Rγ
      W' = result (run-pure W γ)
      IH' : Rᵛ _ (pairᵛ (proj₁-val W') (proj₂-val W'))
      IH' = subst (λ x → Rᵛ _ x) (sym (pair-val W')) IH
    in
    sn λ { ∘pm → fundamentalᶜ M (Rᴱ-ext (Rᴱ-ext Rγ (proj₁ IH')) (proj₂ IH')) Rk }
  fundamentalᶜ (push M₁ M₂) {γ = γ} Rγ {k = k} Rk =
    let
      Rk' : Rᵏ _ (M₂ ⊲ γ ⦂⦂ k)
      Rk' RW = sn (λ { ∙return → fundamentalᶜ M₂ (Rᴱ-ext Rγ RW) Rk })
    in
    sn λ { ∘push → fundamentalᶜ M₁ Rγ Rk' }
  fundamentalᶜ (app W₁ W₂) {γ = γ} Rγ {k = k} Rk =
    let
      IH = fundamentalᵖ W₁ Rγ
      W₁' = result (run-pure W₁ γ)
      eq = sym (clo-val W₁')
      IH' = subst (λ x → Rᵛ _ x) eq IH
    in
    sn λ { ∘app → IH' (fundamentalᵖ W₂ Rγ) Rk }
  fundamentalᶜ (var W) {γ = γ} Rγ Rk = sn λ { ∘var → subst (λ x → x) (rv≡sn W γ) (Rʲ W Rγ)}
  fundamentalᶜ (sub M₁ M₂) Rγ Rk = sn λ { ∘sub → fundamentalᶜ M₁ (Rᴱ-ext Rγ (fundamentalᶜ M₂ Rγ Rk)) Rk}

Rᴱ-⊘ : {Z₀ : Ty} → Rᴱ {Z₀ = Z₀} ∅
Rᴱ-⊘ = λ ()

Rᵏ-◻ : {Z₀ : Ty} → Rᵏ {Z₀ = Z₀} Z₀ ◻
Rᵏ-◻ RW = sn λ {σ'} ()

SN-theorem : {Z₀ : Ty} → (M : Comp ε Z₀) → SN {Z₀ = Z₀} ⟨ M ╎ ∅ ╎ ◻ ⟩
SN-theorem M = fundamentalᶜ M Rᴱ-⊘ Rᵏ-◻

Normal : {Z₀ : Ty} → CompState {Z₀ = Z₀} → Set
Normal σ = ∀ {σ'} → σ →ᶜ σ' → ⊥

data Progress {Z₀ : Ty} (σ : CompState {Z₀ = Z₀}) : Set where
  done : Normal σ → Progress σ
  step : {σ' : CompState} → σ →ᶜ σ' → Progress σ

progress : {Z₀ : Ty} (σ : CompState {Z₀ = Z₀}) → Progress σ
progress ⟨return W' ╎ ◻ ⟩ = done (λ ())
progress ⟨return W' ╎ M ⊲ γ ⦂⦂ k ⟩ = step ∙return
progress ⟨ return W ╎ γ ╎ k ⟩ = step ∘return
progress ⟨ pm W M ╎ γ ╎ k ⟩ = step ∘pm
progress ⟨ push M₁ M₂ ╎ γ ╎ k ⟩ = step ∘push
progress ⟨ app W₁ W₂ ╎ γ ╎ k ⟩ = step ∘app
progress ⟨ var W ╎ γ ╎ k ⟩ = step ∘var
progress ⟨ sub M₁ M₂ ╎ γ ╎ k ⟩ = step ∘sub

halting-state : (σ : CompState {Z₀ = Z₀}) → Normal σ → Σ[ W ∈ Value Z₀ ] σ ≡ ⟨return W ╎ ◻ ⟩
halting-state ⟨return W' ╎ ◻ ⟩ normal = W' , refl
halting-state ⟨return W' ╎ x ⊲ γ ⦂⦂ k ⟩ normal = ql (normal ∙return) _
halting-state ⟨ return _ ╎ γ ╎ k ⟩ normal = ql (normal ∘return) _
halting-state ⟨ pm _ _ ╎ γ ╎ k ⟩ normal = ql (normal ∘pm) _
halting-state ⟨ push _ _ ╎ γ ╎ k ⟩ normal = ql (normal ∘push) _
halting-state ⟨ app _ _ ╎ γ ╎ k ⟩ normal = ql (normal ∘app) _
halting-state ⟨ var _ ╎ γ ╎ k ⟩ normal = ql (normal ∘var) _
halting-state ⟨ sub _ _ ╎ γ ╎ k ⟩ normal = ql (normal ∘sub) _


eval-acc : {Z₀ : Ty} {σ : CompState {Z₀ = Z₀}} → SN σ → Σ[ σ' ∈ CompState ] Σ[ W' ∈ Value {Z₀ = Z₀} Z₀ ] Σ[ NF ∈ Normal σ' ] (σ →ᶜ* σ') × (W' ≡ proj₁ (halting-state σ' NF))
eval-acc {σ = σ} (sn f) with progress σ
... | done NF    = σ , proj₁ (halting-state σ NF) , NF , (σ ◼) , refl
... | step S→S' with eval-acc (f S→S')
...   | (σ'' , W' , NF , S'→*S'' , eq) = σ'' , W' , NF , (_ →ᶜ⟨ S→S' ⟩ S'→*S'') , eq

eval : {Z₀ : Ty} → (M : Comp ε Z₀) → Σ[ σ' ∈ CompState ] Σ[ W' ∈ Value {Z₀ = Z₀} Z₀ ] Σ[ NF ∈ Normal σ' ] (⟨ M ╎ ∅ ╎ ◻ ⟩ →ᶜ* σ') × (W' ≡ proj₁ (halting-state σ' NF))
eval M = eval-acc (SN-theorem M)

---------------------------------------------------------------------------------
-- EXAMPLES

ex15 : ε ⊢ᶜ (`Unit)
ex15 = push (push (app (lam {X = `Unit} (sub (var (var h)) (return unit))) unit) (return unit)) (return unit)

_ : eval ex15 ≡ (_ , unitᵛ , _ ,
                  (⟨ push (push (app (lam (sub (var (var h)) (return unit))) unit) (return unit)) (return unit) ╎ ∅ ╎ ◻ ⟩
    →ᶜ⟨ ∘push ⟩   (⟨ push (app (lam (sub (var (var h)) (return unit))) unit) (return unit) ╎ ∅ ╎ return unit ⊲ ∅ ⦂⦂ ◻ ⟩
    →ᶜ⟨ ∘push ⟩   (⟨ app (lam (sub (var (var h)) (return unit))) unit ╎ ∅ ╎ return unit ⊲ ∅ ⦂⦂ (return unit ⊲ ∅ ⦂⦂ ◻) ⟩
    →ᶜ⟨ ∘app ⟩    (⟨ sub (var (var h)) (return unit) ╎ ∅ ، unitᵛ ╎ return unit ⊲ ∅ ⦂⦂ (return unit ⊲ ∅ ⦂⦂ ◻) ⟩
    →ᶜ⟨ ∘sub ⟩    (⟨ var (var h) ╎ ∅ ، unitᵛ ، jumpᵛ (return unit) (∅ ، unitᵛ) (return unit ⊲ ∅ ⦂⦂ (return unit ⊲ ∅ ⦂⦂ ◻)) ╎ return unit ⊲ ∅ ⦂⦂ (return unit ⊲ ∅ ⦂⦂ ◻) ⟩
    →ᶜ⟨ ∘var ⟩    (⟨ return unit ╎ ∅ ، unitᵛ ╎ return unit ⊲ ∅ ⦂⦂ (return unit ⊲ ∅ ⦂⦂ ◻) ⟩
    →ᶜ⟨ ∘return ⟩ (⟨return unitᵛ ╎ return unit ⊲ ∅ ⦂⦂ (return unit ⊲ ∅ ⦂⦂ ◻) ⟩
    →ᶜ⟨ ∙return ⟩ (⟨ return unit ╎ ∅ ، unitᵛ ╎ return unit ⊲ ∅ ⦂⦂ ◻ ⟩
    →ᶜ⟨ ∘return ⟩ (⟨return unitᵛ ╎ return unit ⊲ ∅ ⦂⦂ ◻ ⟩
    →ᶜ⟨ ∙return ⟩ (⟨ return unit ╎ ∅ ، unitᵛ ╎ ◻ ⟩
    →ᶜ⟨ ∘return ⟩ (⟨return unitᵛ ╎ ◻ ⟩ ◼)))))))))))
    , _)
_ = refl
