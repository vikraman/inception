module Inception.Sub.Machine (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Unit

variable
  X Y Z T◾ T◾' : Ty
  Γ' Γ'' : Ctx

infixl 26 _﹐_
infix  26 ⭭_
infix  26 ⇡_
infixr 25 _⊲_∷_
infix  20 ∘_
infix  20 ∙_
infixr 17 _→ᵛ⟨_⟩
infixr 15 _→ᵛ⟨_⟩_
infix  15 _→ᵛ_
infix  15 _→ᴸ_
infixr 10 _⨾_


data V̲a̲l̲ : Ctx → Ty → Set where

    l̲a̲m̲ : (Γ ∙ X) ⊢ᶜ Y → V̲a̲l̲ Γ (X `⇒ Y)

    pa̲i̲r̲ : V̲a̲l̲ Γ X → V̲a̲l̲ Γ Y → V̲a̲l̲ Γ (X `× Y)

    u̲n̲i̲t̲ : V̲a̲l̲ Γ `Unit

    v̲a̲r̲  : (i : Γ ∋ `V) → V̲a̲l̲ Γ `V

toVal : V̲a̲l̲ Γ X → Γ ⊢ᵛ X
toVal (l̲a̲m̲ W) = lam W
toVal (pa̲i̲r̲ LHS RHS) = pair (toVal LHS) (toVal RHS)
toVal (u̲n̲i̲t̲) = unit
toVal (v̲a̲r̲ i) = var i

wk-v̲a̲l̲ : Wk Γ Δ -> V̲a̲l̲ Δ X -> V̲a̲l̲ Γ X
wk-v̲a̲l̲ π (l̲a̲m̲ W) = l̲a̲m̲ ((wk-comp (wk-cong π) W))
wk-v̲a̲l̲ π (pa̲i̲r̲ LHS RHS) = pa̲i̲r̲ (wk-v̲a̲l̲ π LHS) (wk-v̲a̲l̲ π RHS)
wk-v̲a̲l̲ π u̲n̲i̲t̲ = u̲n̲i̲t̲
wk-v̲a̲l̲ π (v̲a̲r̲ i) = v̲a̲r̲ (wk-mem π i)

wk-comm : {M : V̲a̲l̲ Γ X} → {π : Wk Δ Γ} → wk-val π (toVal M) ≡ toVal (wk-v̲a̲l̲ π M)
wk-comm {Γ = Γ} {Δ = Δ} {M = l̲a̲m̲ W} {π = π} = refl
wk-comm {Γ = Γ} {Δ = Δ} {M = pa̲i̲r̲ LHS RHS} {π = π} = trans (cong (λ x → pair x _) wk-comm) ((cong (λ x → pair _ x) wk-comm))
wk-comm {Γ = Γ} {Δ = Δ} {M = u̲n̲i̲t̲} {π = π} = refl
wk-comm {Γ = Γ} {Δ = Δ} {M = v̲a̲r̲ i} {π = π} = refl


data Env : (Γ : Ctx) → Set where

    ∗       :  Env ε

    _﹐_     :   Env Γ → (M : V̲a̲l̲ Γ X) → Env (Γ ∙ X)

    s-comp  : Env Γ → (W : Γ ⊢ᶜ X) → (k : ⟦ X ⟧ → R) → Env (Γ ∙ `V)

variable
    γ  : Env Γ
    γ' : Env Γ'
    γ'' : Env Γ''

⟦_⟧ᴱ : (E : Env Γ) → ⟦ Γ ⟧ˣ
⟦ ∗ ⟧ᴱ = tt
⟦ _﹐_ E M ⟧ᴱ = ⟦ E ⟧ᴱ , ⟦ toVal M ⟧ᵛ ⟦ E ⟧ᴱ
⟦ s-comp E W k ⟧ᴱ = ⟦ E ⟧ᴱ , ⟦ W ⟧ᶜ ⟦ E ⟧ᴱ k

-- Lookup Machine
------------------------------------------------------------------------------

data LookupState : Ty → Set where

    ⟨_∥_⟩   :  (i : Γ ∋ X) → Env Γ → LookupState X

⟦_⟧ᴸ : (S : LookupState X) → ⟦ X ⟧
⟦ ⟨ i ∥ E ⟩ ⟧ᴸ = ⟦ i ⟧ᵐ ⟦ E ⟧ᴱ

lCtx : (S : LookupState X) → Ctx
lCtx (⟨_∥_⟩ {Γ = Γ} i E)= Γ

lTCtx : (S : LookupState X) → Ctx
lTCtx (⟨_∥_⟩ i ∗) = ε
lTCtx (⟨_∥_⟩ i (_﹐_ {Γ = Γ} E M)) = Γ
lTCtx (⟨_∥_⟩ i (s-comp {Γ = Γ} E M k)) = Γ

lEnv : (S : LookupState X) → Env (lCtx S)
lEnv ⟨ i ∥ E ⟩ = E

lTEnv : (S : LookupState X) → Env (lTCtx S)
lTEnv ⟨ i ∥ _﹐_ E M ⟩ = E
lTEnv ⟨ i ∥ s-comp E M k ⟩ = E

data _→ᴸ_ : LookupState X → LookupState X → Set where

    val-h-step    : {E : Env Γ} → {i : Γ ∋ `V} → ⟨ h  ∥ E ﹐ (v̲a̲r̲ i) ⟩ →ᴸ ⟨ i ∥ E ⟩

    val-t-step    : {i : Γ ∋ Y} → {E : Env Γ} → {M : V̲a̲l̲ Γ X} → ⟨ t i  ∥ _﹐_ E M ⟩ →ᴸ ⟨ i ∥ E ⟩

    comp-t-step   : {i : Γ ∋ Y} → {E : Env Γ} → {W : Γ ⊢ᶜ X} → {k : ⟦ X ⟧ → R} → ⟨ t i  ∥ s-comp E W k ⟩ →ᴸ ⟨ i ∥ E ⟩


data _→ᴸ*_ : LookupState X → LookupState X → Set where

  _◼ : (S : LookupState X) → S →ᴸ* S

  _→ᴸ⟨_⟩_ : (S : LookupState X) → {S' S'' : LookupState X} → S →ᴸ S' → S' →ᴸ* S'' → S →ᴸ* S''


-- _⨾ᴸ_ : {F S T : LookupState X} → (F →ᴸ* S) → (S →ᴸ* T) → (F →ᴸ* T)
-- _⨾ᴸ_ (S ◼) S>>T = S>>T
-- _⨾ᴸ_ (F →ᴸ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᴸ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ᴸ S₂>>T)


data LookupHaltingState : LookupState X → Set where

      found-unit : {γ : Env Γ} → LookupHaltingState ⟨ h ∥ _﹐_ γ u̲n̲i̲t̲ ⟩

      found-pair : {LHS : V̲a̲l̲ Γ X} → {RHS : V̲a̲l̲ Γ Y} → {γ : Env Γ} → LookupHaltingState ⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩

      found-lam : {W : (Γ ∙ X) ⊢ᶜ Y} → {γ : Env Γ} → LookupHaltingState ⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩

      found-comp : {W : Γ ⊢ᶜ X} → {γ : Env Γ} → {k : ⟦ X ⟧ → R} → LookupHaltingState ⟨ h ∥ s-comp γ W k ⟩


data LookupSteps : LookupState X → Set where

  steps : {S T : LookupState X} → S →ᴸ* T → LookupHaltingState T → ⟦ S ⟧ᴸ ≡ ⟦ T ⟧ᴸ → (π : Wk (lCtx S) (lTCtx T)) → (⟦ π ⟧ʷ ⟦ lEnv S ⟧ᴱ ≡ ⟦ lTEnv T ⟧ᴱ) → LookupSteps S

lookup : (i : Γ ∋ X) → (γ : Env Γ) → LookupSteps {X = X} ⟨ i ∥ γ ⟩
lookup h (γ ﹐ l̲a̲m̲ W) = steps (⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩ ◼) found-lam refl (wk-wk wk-id) refl
lookup h (γ ﹐ pa̲i̲r̲ LHS RHS) = steps (⟨ h ∥ _﹐_ γ (pa̲i̲r̲ LHS RHS) ⟩ ◼) found-pair refl (wk-wk wk-id) refl
lookup h (γ ﹐ u̲n̲i̲t̲) = steps (⟨ h ∥ _﹐_ γ (u̲n̲i̲t̲) ⟩ ◼) found-unit refl (wk-wk wk-id) refl
lookup h (γ ﹐ v̲a̲r̲ i) with lookup i γ
... | steps i>>T HT i≡T WK w≡γ = steps (_ →ᴸ⟨ val-h-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ
lookup h (s-comp γ W k) = steps (⟨ h ∥ s-comp γ W k ⟩ ◼) found-comp refl (wk-wk wk-id) refl
lookup (t i) (γ ﹐ M) with lookup i γ
... | steps i>>T HT i≡T WK w≡γ = steps (_ →ᴸ⟨ val-t-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ
lookup (t i) (s-comp γ W k) with lookup i γ
... | steps i>>T HT i≡T WK w≡γ = steps (_ →ᴸ⟨ comp-t-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ


-- Value Machine
------------------------------------------------------------------------------

data IsEmpty : Set where
     non-empty : IsEmpty
     empty : IsEmpty

variable
    b : IsEmpty

data BottomTypeEqualsNextType : IsEmpty → Ty → Ty → Set where

     🗆 : BottomTypeEqualsNextType empty X X

     🗇 : BottomTypeEqualsNextType non-empty X Y

data PartialTerm : (Γ : Ctx) → (X : Ty) → Set where

    ⭭_ : V̲a̲l̲ Γ X → PartialTerm Γ X

    ⇡_ : (M : Γ ⊢ᵛ X) → PartialTerm Γ X

    ⇡ᴹ : (M : Γ ⊢ᵛ X `× Y) → (N : (Γ ∙ X ∙ Y) ⊢ᵛ Z) → PartialTerm Γ Z

    ⇡ᴸ : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → PartialTerm Γ (X `× Y)

    ⇡ᴿ  : (LHS : V̲a̲l̲ Γ X) → (RHS : Γ ⊢ᵛ Y) → PartialTerm Γ (X `× Y)


data ValStack : IsEmpty → Ty → Set where

    □ : ValStack empty T◾

    _⊲_∷_ : PartialTerm Γ X → (γ : Env Γ) → (tail : ValStack b T◾) → {↥ : BottomTypeEqualsNextType b X T◾} → ValStack non-empty T◾

data ValState : Ty → Set where

     ∘_ : ValStack non-empty T◾ → ValState T◾

     ∙_ : ValStack non-empty T◾ → ValState T◾

data _→ᵛ_ : ValState T◾ → ValState T◾ → Set where

     ∘var-c  :    {i : Γ ∋ `V} → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b `V T◾}
               ----------------------------------------------------------------
                → ∘ ((⇡ var i ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((⭭ v̲a̲r̲ i ⊲ γ ∷ tail) {↥ = ↥})

     ∘var    :    {i : Γ ∋ X} → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b X T◾}
                → {M : V̲a̲l̲ Γ' X}
                → (⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ _﹐_ γ' M ⟩) → (πᵥ : Wk Γ Γ')
               ----------------------------------------------------------------
                → ∘ ((⇡ var i ⊲ γ ∷ tail) {↥ = ↥}) →ᵛ ∙ ((⭭ (wk-v̲a̲l̲ πᵥ M) ⊲ γ ∷ tail) {↥ = ↥})


     ∘lam   :  {M : (Γ ∙ X) ⊢ᶜ Y} → {γ  : Env Γ}
             → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b (X `⇒ Y) T◾}
               ---------------------------------------------------------------------------
             →     ∘ ((⇡ lam M ⊲ γ ∷ tail) {↥ = ↥})
                →ᵛ ∙ ((⭭ l̲a̲m̲ M ⊲ γ ∷ tail) {↥ = ↥})

     ∘pair  :  {LHS : Γ ⊢ᵛ X} → {RHS : Γ ⊢ᵛ Y}
             → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b (X `× Y) T◾}
               ---------------------------------------------------------------------------
             →     ∘ ((⇡ pair LHS RHS ⊲ γ ∷ tail) {↥ = ↥})
                →ᵛ ∘ ((⇡ LHS ⊲ γ ∷ ((⇡ᴸ LHS RHS ⊲ γ ∷ tail) {↥ = ↥})) {↥ = 🗇})

     ∘pm    :  {M : Γ ⊢ᵛ X `× Y} → {N : (Γ ∙ X ∙ Y) ⊢ᵛ Z}
             → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b Z T◾}
               ---------------------------------------------------------------------------
             →     ∘ ((⇡ pm M N ⊲ γ ∷ tail) {↥ = ↥})
                →ᵛ ∘ ((⇡ M ⊲ γ ∷ (⇡ᴹ M N ⊲ γ ∷ tail) {↥ = ↥}) {↥ = 🗇})

     ∘unit  :  {γ  : Env Γ}
             → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b `Unit T◾}
               ---------------------------------------------------------------------------
             →     ∘ ((⇡ unit ⊲ γ ∷ tail) {↥ = ↥})
                →ᵛ ∙ ((⭭ u̲n̲i̲t̲ ⊲ γ ∷ tail) {↥ = ↥})

     ∙M∷l   :  {M : V̲a̲l̲ Γ X} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y} → {π' : Wk Γ Γ'}
             → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b (X `× Y) T◾}
               ---------------------------------------------------------------------------
             →     ∙ ((⭭ M ⊲ γ ∷ ((⇡ᴸ LHS RHS ⊲ γ' ∷ tail) {↥ = ↥})) {↥ = 🗇})
                →ᵛ ∘ ((⇡ wk-val π' RHS ⊲ γ ∷ ((⇡ᴿ M (wk-val π' RHS) ⊲ γ ∷ tail) {↥ = ↥})) {↥ = 🗇})

     ∙M∷r   :  {M : V̲a̲l̲ Γ Y} → {LHS : V̲a̲l̲ Γ' X} → {RHS : Γ' ⊢ᵛ Y} {π' : Wk Γ Γ'}
             → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b (X `× Y) T◾}
               ---------------------------------------------------------------------------
             →     ∙ ((⭭ M ⊲ γ ∷ ((⇡ᴿ LHS RHS ⊲ γ' ∷ tail) {↥ = ↥})) {↥ = 🗇})
                →ᵛ ∙ ((⭭ pa̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M ⊲ γ ∷ tail) {↥ = ↥})

     ∙pair∷pm  :  {LHS : V̲a̲l̲ Γ X} → {RHS : V̲a̲l̲ Γ Y} → {M : Γ' ⊢ᵛ X `× Y} → {N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z}
             → {π' : Wk Γ Γ'}
             → {tail : ValStack b T◾} → {↥ : BottomTypeEqualsNextType b Z T◾}
               ---------------------------------------------------------------------------
             →     ∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ ∷ ((⇡ᴹ M N ⊲ γ' ∷ tail) {↥ = ↥})) {↥ = 🗇})
                →ᵛ  ∘ ((⇡ (wk-val (wk-cong (wk-cong π')) N) ⊲ _﹐_ ((_﹐_ γ LHS)) (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ∷ tail) {↥ = ↥})


data _↠ᵛ_ : ValState T◾ → ValState T◾ → Set where

  _→ᵛ⟨_⟩ : (S : ValState T◾) → {S' : ValState T◾} → (laststep : S →ᵛ S') → S ↠ᵛ S'

  _→ᵛ⟨_⟩_ : (S : ValState T◾) → {S' S'' : ValState T◾} → S →ᵛ S' → S' ↠ᵛ S'' → S ↠ᵛ S''

_⨾_ : {F S T : ValState T◾} → (F ↠ᵛ S) → (S ↠ᵛ T) → (F ↠ᵛ T)
_⨾_ (F →ᵛ⟨ F>S ⟩) S>>T = F →ᵛ⟨ F>S ⟩ S>>T
_⨾_ (F →ᵛ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᵛ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ S₂>>T)

_⧺_ : ValStack b T◾ → ValStack non-empty T◾' → ValStack non-empty T◾'
□ ⧺ lower = lower
(M ⊲ γ ∷ upper) ⧺ lower = (M ⊲ γ ∷ (upper ⧺ lower)) {↥ = 🗇}

_⧻_ : (upper : ValState T◾) → ValStack non-empty T◾' → ValState T◾'
(∘ upper) ⧻ lower = ∘ (upper ⧺ lower)
(∙ upper) ⧻ lower = ∙ (upper ⧺ lower)

⟨_⟩⧻_ : {from : ValState T◾} → {to : ValState T◾} → (F>T : from →ᵛ to) → (tail : ValStack non-empty T◾') → (from ⧻ tail) →ᵛ (to ⧻ tail)
⟨ ∘var-c ⟩⧻ tail = ∘var-c
⟨ ∘var T>>U π ⟩⧻ tail = ∘var T>>U π
⟨ ∘lam ⟩⧻ tail = ∘lam
⟨ ∘pair ⟩⧻ tail = ∘pair
⟨ ∘pm ⟩⧻ tail = ∘pm
⟨ ∘unit ⟩⧻ tail = ∘unit
⟨ ∙pair∷pm ⟩⧻ tail = ∙pair∷pm
⟨ ∙M∷l ⟩⧻ tail = ∙M∷l
⟨ ∙M∷r ⟩⧻ tail = ∙M∷r

⟪_⟫⧻_ : {from : ValState T◾} → {to : ValState T◾} → (F>T : from ↠ᵛ to) → (tail : ValStack non-empty T◾') → (from ⧻ tail) ↠ᵛ (to ⧻ tail)
⟪ _ →ᵛ⟨ F>T ⟩ ⟫⧻ tail =  _ →ᵛ⟨ ⟨ F>T ⟩⧻ tail ⟩
⟪ _ →ᵛ⟨ F>T ⟩ F>>T ⟫⧻ tail =   _ →ᵛ⟨ ⟨ F>T ⟩⧻ tail ⟩ (⟪ F>>T ⟫⧻ tail)

⟦_⟧ᵛˢ : (S : ValStack non-empty T◾) → ⟦ T◾ ⟧
⟦ (⭭ x ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ toVal x ⟧ᵛ ⟦ γ ⟧ᴱ
⟦ (⇡ M ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ M ⟧ᵛ ⟦ γ ⟧ᴱ
⟦ (⇡ᴹ M N ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ pm M N ⟧ᵛ ⟦ γ ⟧ᴱ
⟦ (⇡ᴸ LHS RHS ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ pair LHS RHS ⟧ᵛ ⟦ γ ⟧ᴱ
⟦ (⇡ᴿ LHS RHS ⊲ γ ∷ □) {↥ = 🗆} ⟧ᵛˢ = ⟦ pair (toVal LHS) RHS ⟧ᵛ ⟦ γ ⟧ᴱ
⟦ (⭭ x ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ
⟦ (⇡ M ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ
⟦ (⇡ᴹ M N ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ
⟦ (⇡ᴸ LHS RHS ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ
⟦ (⇡ᴿ LHS RHS ⊲ γ ∷ ((x₁ ⊲ γ₁ ∷ S) {↥ = ↥})) {↥ = 🗇} ⟧ᵛˢ = ⟦ (x₁ ⊲ γ₁ ∷ S) {↥ = ↥} ⟧ᵛˢ


⟦_⟧ᵛꟴ : (S : ValState T◾) → ⟦ T◾ ⟧
⟦ ∘ tail ⟧ᵛꟴ = ⟦ tail ⟧ᵛˢ
⟦ ∙ tail ⟧ᵛꟴ = ⟦ tail ⟧ᵛˢ

topCtx : ValState T◾ → Ctx
topCtx (∘ ⭭_ {Γ = Γ} x ⊲ γ ∷ x₁) = Γ
topCtx (∘ ⇡_ {Γ = Γ} M ⊲ γ ∷ x₁) = Γ
topCtx (∘ ⇡ᴹ {Γ = Γ} M N ⊲ γ ∷ x₁) = Γ
topCtx (∘ ⇡ᴸ {Γ = Γ} LHS RHS ⊲ γ ∷ x₁) = Γ
topCtx (∘ ⇡ᴿ {Γ = Γ} LHS RHS ⊲ γ ∷ x₁) = Γ
topCtx (∙ ⭭_ {Γ = Γ} x ⊲ γ ∷ x₁) = Γ
topCtx (∙ ⇡_ {Γ = Γ} M ⊲ γ ∷ x₁) = Γ
topCtx (∙ ⇡ᴹ {Γ = Γ} M N ⊲ γ ∷ x₁) = Γ
topCtx (∙ ⇡ᴸ {Γ = Γ} LHS RHS ⊲ γ ∷ x₁) = Γ
topCtx (∙ ⇡ᴿ {Γ = Γ} LHS RHS ⊲ γ ∷ x₁) = Γ

topEnv : (S : ValState T◾) → Env (topCtx S)
topEnv (∘ ⭭ x ⊲ γ ∷ x₁) = γ
topEnv (∘ ⇡ M ⊲ γ ∷ x₁) = γ
topEnv (∘ ⇡ᴹ M N ⊲ γ ∷ x₁) = γ
topEnv (∘ ⇡ᴸ LHS RHS ⊲ γ ∷ x₁) = γ
topEnv (∘ ⇡ᴿ LHS RHS ⊲ γ ∷ x₁) = γ
topEnv (∙ ⭭ x ⊲ γ ∷ x₁) = γ
topEnv (∙ ⇡ M ⊲ γ ∷ x₁) = γ
topEnv (∙ ⇡ᴹ M N ⊲ γ ∷ x₁) = γ
topEnv (∙ ⇡ᴸ LHS RHS ⊲ γ ∷ x₁) = γ
topEnv (∙ ⇡ᴿ LHS RHS ⊲ γ ∷ x₁) = γ

data ValHaltingState : ValState T◾ → Set where

     ∙_⊲_■ : (M : V̲a̲l̲ Γ X) → (γ : Env Γ) → ValHaltingState (∙ ((⭭ M ⊲ γ ∷ □) {↥ = 🗆}))


data ValSteps : ValState T◾ → Set where

  steps : {S T : ValState T◾} → S ↠ᵛ T → ValHaltingState T → ⟦ S ⟧ᵛꟴ ≡ ⟦ T ⟧ᵛꟴ → (π : Wk (topCtx T) (topCtx S)) → (⟦ π ⟧ʷ ⟦ topEnv T ⟧ᴱ ≡ ⟦ topEnv S ⟧ᴱ) → ValSteps S


val-eval-rec : (M : Γ' ⊢ᵛ X) → (γ : Env Γ) → (π : Wk Γ Γ') → ValSteps {T◾ = X} (∘ ((⇡ (wk-val π M) ⊲ γ ∷ □) {↥ = 🗆}))

val-eval-rec {X = `V} (var {A = .`V} i) γ π = steps (_ →ᵛ⟨ ∘var-c ⟩) (∙ v̲a̲r̲ (wk-mem π i) ⊲ γ ■) refl wk-id refl

val-eval-rec {X = `Unit} (var {A = .`Unit} i) γ π with lookup (wk-mem π i) γ
... | steps i>>T found-unit i≡T π₁ w≡γ = steps (_ →ᵛ⟨ ∘var i>>T π₁ ⟩) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id refl

val-eval-rec {X = X `× X₁} (var {A = .(X `× X₁)} i) γ π  with lookup (wk-mem π i) γ
... | steps i>>T (found-pair {LHS = LHS} {RHS = RHS} {γ = γ₁}) i≡T π₁ w≡γ =

           steps

           (_ →ᵛ⟨ ∘var i>>T π₁ ⟩)

           (∙ pa̲i̲r̲ (wk-v̲a̲l̲ π₁ LHS) (wk-v̲a̲l̲ π₁ RHS) ⊲ γ ■)

           (⟦ wk-mem π i ⟧ᵐ ⟦ γ ⟧ᴱ
           ≡⟨ i≡T ⟩
           (< ⟦ toVal LHS ⟧ᵛ , ⟦ toVal RHS ⟧ᵛ > ⟦ γ₁ ⟧ᴱ)
           ≡⟨ cong (λ x → < ⟦ toVal LHS ⟧ᵛ , ⟦ toVal RHS ⟧ᵛ > x) (sym w≡γ) ⟩
           (< ⟦ toVal LHS ⟧ᵛ , ⟦ toVal RHS ⟧ᵛ > (⟦ π₁ ⟧ʷ ⟦ γ ⟧ᴱ))
           ≡⟨ refl ⟩
           (⟦ wk-val π₁ (toVal LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ wk-val π₁ (toVal RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)
           ≡⟨ cong (λ x → (⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ wk-val π₁ (toVal RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)) (wk-comm {M = LHS} {π = π₁}) ⟩
           (⟦ toVal (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ wk-val π₁ (toVal RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)
           ≡⟨ cong (λ x → (⟦ toVal (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ)) (wk-comm {M = RHS} {π = π₁}) ⟩
           (⟦ toVal (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ toVal (wk-v̲a̲l̲ π₁ RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)
           ≡⟨ refl ⟩
           (< ⟦ toVal (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ , ⟦ toVal (wk-v̲a̲l̲ π₁ RHS) ⟧ᵛ > ⟦ γ ⟧ᴱ) ∎)

           wk-id

           refl
val-eval-rec {X = X `⇒ X₁} (var {A = .(X `⇒ X₁)} i) γ π with lookup (wk-mem π i) γ

... | steps i>>T (found-lam {W = W} {γ = γ₁}) i≡T π₁ w≡γ =

           steps

           (_ →ᵛ⟨ ∘var i>>T π₁ ⟩)

           (∙ (wk-v̲a̲l̲ π₁ (l̲a̲m̲ W)) ⊲ γ ■)

           (⟦ wk-mem π i ⟧ᵐ ⟦ γ ⟧ᴱ
             ≡⟨ i≡T ⟩
           ((λ y → ⟦ W ⟧ᶜ (⟦ γ₁ ⟧ᴱ , y) ))
             ≡⟨ cong (λ x → (λ y → ⟦ W ⟧ᶜ (x , y) )) (sym w≡γ) ⟩
           (λ y → ⟦ W ⟧ᶜ (⟦ π₁ ⟧ʷ ⟦ γ ⟧ᴱ , y) )
             ≡⟨ refl ⟩
           (curry (< (λ r → proj₁ r) ； ⟦ π₁ ⟧ʷ , (λ r → proj₂ r) > ； ⟦ W ⟧ᶜ)) ⟦ γ ⟧ᴱ ∎)

           wk-id

           refl

--... | steps i>>T (found-comp {W = W} {γ = γ₁} {k = k}) i≡T π₁ w≡γ =
--
--            steps {!!} {!!} {!!} {!!} {!!}

val-eval-rec (lam W) γ π = steps (∘ ⇡ (wk-val π (lam W)) ⊲ γ ∷ □ →ᵛ⟨ ∘lam ⟩) (∙ l̲a̲m̲ (wk-comp (wk-cong π) W) ⊲ γ ■) refl wk-id refl
val-eval-rec unit γ π = steps (_ →ᵛ⟨ ∘unit ⟩) (∙ u̲n̲i̲t̲ ⊲ γ ■) refl wk-id refl

val-eval-rec (pair {A = X} {B = Y} LHS RHS) γ π with val-eval-rec {X = X} LHS γ π
... | steps {T = ∙ (⭭_ {X = X} LT ⊲ γ₁ ∷ □) {↥ = 🗆}} L>T ∙LT L≡T πᴸ wk≡ᴸ with  val-eval-rec {X = Y} RHS γ₁ (wk-trans πᴸ π)
...      | steps {T = ∙ (⭭_ {X = Y} RT ⊲ γ₂ ∷ □) {↥ = 🗆}} R>T ∙RT R≡T πᴿ wk≡ᴿ rewrite sym (wk-val-trans RHS πᴸ π) =

          steps

            (
             ∘ ⇡ (wk-val π (pair LHS RHS)) ⊲ γ ∷ □ →ᵛ⟨ ∘pair ⟩  ⨾ -- (∘ ⇡ wk-val π LHS ⊲ γ ∷ ⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⊲ γ ∷ □)
             (⟪ L>T ⟫⧻ (⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⊲ γ ∷ □)) ⨾
             (∙ ⭭ LT ⊲ γ₁ ∷ ⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⊲ γ ∷ □) →ᵛ⟨ ∙M∷l ⟩ ⨾ -- (∘ ⇡ wk-val _π'_3203 (wk-val π RHS) ⊲ γ₁ ∷ ⇡ᴿ LT (wk-val _π'_3203 (wk-val π RHS)) ⊲ γ₁ ∷ □)
             (⟪ R>T ⟫⧻ (⇡ᴿ LT (wk-val πᴸ (wk-val π RHS)) ⊲ γ₁ ∷ □)) ⨾
             (∙ ⭭ RT ⊲ γ₂ ∷ ⇡ᴿ LT (wk-val πᴸ (wk-val π RHS)) ⊲ γ₁ ∷ □) →ᵛ⟨ ∙M∷r ⟩
            )

            ∙ pa̲i̲r̲ (wk-v̲a̲l̲ πᴿ LT) RT ⊲ γ₂ ■

            ( ⟦ wk-val π (pair LHS RHS) ⟧ᵛ ⟦ γ ⟧ᴱ
             ≡⟨ refl ⟩
               (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))
             ≡⟨ cong (λ y → (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ y))) (sym wk≡ᴸ) ⟩
               (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ (⟦ πᴸ ⟧ʷ ⟦ γ₁ ⟧ᴱ)))
             ≡⟨ cong (λ y → (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ y)) (wk-sem-trans πᴸ π ⟦ γ₁ ⟧ᴱ) ⟩
               (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
             ≡⟨ cong (λ y → (y , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))) L≡T ⟩
               (⟦ toVal LT ⟧ᵛ ⟦ γ₁ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
             ≡⟨ cong (λ y → (⟦ toVal LT ⟧ᵛ y , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))) (sym wk≡ᴿ) ⟩
               (⟦ toVal LT ⟧ᵛ (⟦ πᴿ ⟧ʷ ⟦ γ₂ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
             ≡⟨ refl ⟩
               (⟦ wk-val πᴿ (toVal LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
             ≡⟨ cong (λ y → (⟦ y ⟧ᵛ ⟦ γ₂ ⟧ᴱ  , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))) (wk-comm {M = LT} {π = πᴿ}) ⟩
               (⟦ toVal (wk-v̲a̲l̲ πᴿ LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
             ≡⟨ cong (λ y → (⟦ toVal (wk-v̲a̲l̲ πᴿ LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , y)) R≡T ⟩
               (⟦ toVal (wk-v̲a̲l̲ πᴿ LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , ⟦ toVal RT ⟧ᵛ ⟦ γ₂ ⟧ᴱ)
             ≡⟨ refl ⟩
               ⟦ pair (toVal (wk-v̲a̲l̲ πᴿ LT)) (toVal RT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ
             ≡⟨ refl ⟩
               ⟦ toVal (pa̲i̲r̲ (wk-v̲a̲l̲ πᴿ LT) RT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ
             ≡⟨ refl ⟩
               ⟦ ∙ (⭭ pa̲i̲r̲ (wk-v̲a̲l̲ πᴿ LT) RT ⊲ γ₂ ∷ □) {↥ = 🗆} ⟧ᵛꟴ ∎ )

            (wk-trans πᴿ πᴸ)

            ( ⟦ wk-trans πᴿ πᴸ ⟧ʷ ⟦ γ₂ ⟧ᴱ
            ≡⟨ sym (wk-sem-trans πᴿ πᴸ ⟦ γ₂ ⟧ᴱ) ⟩
               ⟦ πᴸ ⟧ʷ (⟦ πᴿ ⟧ʷ ⟦ γ₂ ⟧ᴱ)
            ≡⟨ cong (λ y → ⟦ πᴸ ⟧ʷ y) wk≡ᴿ ⟩
               ⟦ πᴸ ⟧ʷ ⟦ γ₁ ⟧ᴱ
            ≡⟨ wk≡ᴸ ⟩
               ⟦ γ ⟧ᴱ ∎)

val-eval-rec (pm M N) γ π with val-eval-rec M γ π
... | steps M>T ∙ pa̲i̲r̲ LHS RHS ⊲ γ₁ ■ M≡T π₁ wk≡₁ with val-eval-rec N (_﹐_ (_﹐_ γ₁ LHS) (wk-v̲a̲l̲ (wk-wk wk-id) RHS)) ((wk-cong (wk-cong (wk-trans π₁ π)))) | (wk-val-trans N (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π)))
...    | steps {T = T} N>T ∙T N≡T π₂ wk≡₂ | eq with N>T
...      | N>T' rewrite sym eq =
       steps
         (
          (∘ ⇡ pm (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⊲ γ ∷ □) →ᵛ⟨ ∘pm ⟩ ⨾ -- (∘ ⇡ wk-val π M ⊲ γ ∷ ⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⊲ γ ∷ □)
          (⟪ M>T ⟫⧻ (⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⊲ γ ∷ □)) ⨾
          (∙ ⭭ pa̲i̲r̲ LHS RHS ⊲ γ₁ ∷ ⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⊲ γ ∷ □) →ᵛ⟨ ∙pair∷pm ⟩ ⨾ -- (∘ ⇡ wk-val (wk-cong (wk-cong π₁)) (wk-val (wk-cong (wk-cong π)) N) ⊲ _﹐_ (_﹐_ γ₁ LHS) (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ∷ □)
          N>T'
         )

         ∙T

         (  ⟦ wk-val π (pm M N) ⟧ᵛ ⟦ γ ⟧ᴱ
           ≡⟨ refl ⟩
            ⟦ pm (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⟧ᵛ ⟦ γ ⟧ᴱ
           ≡⟨ refl ⟩
           (< idf , ⟦ π ⟧ʷ ； ⟦ M ⟧ᵛ > ； assocl ； ⟦ wk-val (wk-cong (wk-cong π)) N ⟧ᵛ) ⟦ γ ⟧ᴱ
           ≡⟨ refl ⟩
           ⟦ wk-val (wk-cong (wk-cong π)) N ⟧ᵛ (assocl ( (⟦ γ ⟧ᴱ ,  ⟦ M ⟧ᵛ  (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))))
           ≡⟨ cong (λ y → ⟦ wk-val (wk-cong (wk-cong π)) N ⟧ᵛ (assocl ( (⟦ γ ⟧ᴱ , y   )))) M≡T ⟩
           ⟦ wk-val (wk-cong (wk-cong π)) N ⟧ᵛ (assocl ( (⟦ γ ⟧ᴱ ,  (⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)  )))
           ≡⟨ refl ⟩
            ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
           ≡⟨ cong  (λ y → ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ y , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)) (sym wk≡₁) ⟩
            ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
           ≡⟨ refl ⟩
            ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ (wk-val (wk-wk wk-id) (toVal RHS)) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
           ≡⟨ cong (λ y → ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ y ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))) (wk-comm {M = RHS} {π = wk-wk wk-id}) ⟩
            ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
           ≡⟨ cong (λ y → ⟦ N ⟧ᵛ ((y , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))  ) (wk-sem-trans π₁ π ⟦ γ₁ ⟧ᴱ) ⟩
           ⟦ N ⟧ᵛ ((⟦ wk-trans π₁ π ⟧ʷ ⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
           ≡⟨ N≡T ⟩
           ⟦ T ⟧ᵛꟴ ∎)

         (wk-trans π₂ (wk-wk (wk-wk π₁)))

         ( ⟦ wk-trans π₂ (wk-wk (wk-wk π₁)) ⟧ʷ ⟦ topEnv T ⟧ᴱ
          ≡⟨ sym (wk-sem-trans π₂ (wk-wk (wk-wk π₁)) ⟦ topEnv T ⟧ᴱ) ⟩
           ⟦ wk-wk (wk-wk π₁) ⟧ʷ (⟦ π₂ ⟧ʷ ⟦ topEnv T ⟧ᴱ)
          ≡⟨ cong (λ y → ⟦ wk-wk (wk-wk π₁) ⟧ʷ y) wk≡₂ ⟩
           ⟦ wk-wk (wk-wk π₁) ⟧ʷ (((⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ toVal (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ toVal LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))
          ≡⟨ refl ⟩
           ⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ
          ≡⟨ wk≡₁ ⟩
           ⟦ γ ⟧ᴱ ∎)


--val-eval-rec : (M : Γ' ⊢ᵛ X) → (γ : Env Γ) → (π : Wk Γ Γ') → ValSteps {T◾ = X} (∘ ((⇡ (wk-val π M) ⊲ γ ∷ □) {↥ = 🗆}))
val-eval : (M : ε ⊢ᵛ X) → ValSteps {T◾ = X} (∘ ((⇡ wk-val wk-id M ⊲ ∗ ∷ □) {↥ = 🗆}))
val-eval M = val-eval-rec M ∗ wk-id

{----------------------

-- EXAMPLES
--------------------------------------------------

ex1 : ε ⊢ᵛ `Unit
ex1 = pm (pair unit unit) (var (t h))

ex2 : ε ⊢ᵛ `Unit `× `Unit
ex2 = pm (pm (pair (lam {A = `Unit} {B = `Unit} (return (var h))) unit) (pair unit (var (t h)))) (pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))))

---------------------------------------

-- -- calling agda2-compute-normalised in the hole below val-eval-recuates example
-- _ : val-eval ex2 ≡ {!val-eval ex2!}
-- _ = refl

-}
