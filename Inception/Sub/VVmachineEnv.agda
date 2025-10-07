module Inception.Sub.VVmachineEnv (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Unit

variable
  X Y Z X' Y' Z' T◾ T◾' : Ty
  Γ' Γ'' Θ Θ' Ψ' : Ctx

infixl 26 _﹐_
infix  26 ⭭_
infix  26 ⇡_
infixr 25 _⹁_∷_
infix  20 ∘_
infix  20 ∙_
infixr 17 _→ᵛᵛ⟨_⟩
infixr 15 _→ᵛᵛ⟨_⟩_
infix  15 _→ᵛᵛ_
infixr 10 _⨾_

data Bool : Set where
     true : Bool
     false : Bool

data V̲a̲l̲ : Ctx → Ty → Set where

    l̲a̲m̲ : (Γ ∙ X) ⊢ᶜ Y → V̲a̲l̲ Γ (X `⇒ Y)

    p̲a̲i̲r̲ : V̲a̲l̲ Γ X → V̲a̲l̲ Γ Y → V̲a̲l̲ Γ (X `× Y)

    u̲n̲i̲t̲ : V̲a̲l̲ Γ `Unit

data Env : (Γ : Ctx) → Set where

    z       :  Env ε

    _﹐_   :   Env Γ → (M : V̲a̲l̲ Γ X) → Env (Γ ∙ X)

--    s-comp  :  (W : Γ ⊢ᶜ X) → Env Γ → (k : ⟦ X ⟧ → R) → Env Γ' → Env (Γ' ∙ `V)

V̲a̲l̲-to-Val : V̲a̲l̲ Γ X → Γ ⊢ᵛ X
V̲a̲l̲-to-Val (l̲a̲m̲ W) = lam W
V̲a̲l̲-to-Val (p̲a̲i̲r̲ LHS RHS) = pair (V̲a̲l̲-to-Val LHS) (V̲a̲l̲-to-Val RHS)
V̲a̲l̲-to-Val (u̲n̲i̲t̲) = unit

wk-v̲a̲l̲ : Wk Γ Δ -> V̲a̲l̲ Δ X -> V̲a̲l̲ Γ X
wk-v̲a̲l̲ π (l̲a̲m̲ W) = l̲a̲m̲ ((wk-comp (wk-cong π) W))
wk-v̲a̲l̲ π (p̲a̲i̲r̲ LHS RHS) = p̲a̲i̲r̲ (wk-v̲a̲l̲ π LHS) (wk-v̲a̲l̲ π RHS)
wk-v̲a̲l̲ π u̲n̲i̲t̲ = u̲n̲i̲t̲

wk-trans : Wk Γ Δ → Wk Δ Ψ → Wk Γ Ψ
wk-trans wk-ε π₂ = π₂
wk-trans (wk-cong π₁) (wk-cong π₂) = wk-cong (wk-trans π₁ π₂)
wk-trans (wk-cong π₁) (wk-wk π₂) = wk-wk (wk-trans π₁ π₂)
wk-trans (wk-wk π₁) π₂ = wk-wk (wk-trans π₁ π₂)


variable
    b : Bool
    γ  : Env Γ
    γ' : Env Γ'
    γ'' : Env Γ''


infix  15 _→ᴸᴸ_


⟦_⟧ᴱ : (E : Env Γ) → ⟦ Γ ⟧ˣ
⟦ z ⟧ᴱ = tt
⟦ _﹐_ E M ⟧ᴱ = ⟦ E ⟧ᴱ , ⟦ V̲a̲l̲-to-Val M ⟧ᵛ ⟦ E ⟧ᴱ
--⟦ s-comp W E k E' ⟧ᴱ = ⟦ E' ⟧ᴱ , ⟦ W ⟧ᶜ ⟦ E ⟧ᴱ k

data lState : Ty → Set where

    ⟨_∥_⟩   :  (i : Γ ∋ X) → Env Γ → lState X

⟦_⟧ᴸ : (S : lState X) → ⟦ X ⟧
⟦ ⟨ i ∥ E ⟩ ⟧ᴸ = ⟦ i ⟧ᵐ ⟦ E ⟧ᴱ

lCtx : (S : lState X) → Ctx
lCtx (⟨_∥_⟩ {Γ = Γ} i E)= Γ

lTCtx : (S : lState X) → Ctx
lTCtx (⟨_∥_⟩ i z) = ε
lTCtx (⟨_∥_⟩ i (_﹐_ {Γ = Γ} E M)) = Γ

lEnv : (S : lState X) → Env (lCtx S)
lEnv ⟨ i ∥ E ⟩ = E

lTEnv : (S : lState X) → Env (lTCtx S)
lTEnv ⟨ i ∥ _﹐_ E M ⟩ = E

data _→ᴸᴸ_ : lState X → lState X → Set where

    val-t-step    : {i : Γ ∋ Y} → {E : Env Γ} → {M : V̲a̲l̲ Γ X} → ⟨ t i  ∥ _﹐_ E M ⟩ →ᴸᴸ ⟨ i ∥ E ⟩

--    comp-t-step    : {i : Γ' ∋ Y} → {E : Env Γ} → {W : Γ ⊢ᶜ X} → {k : ⟦ X ⟧ → R} → {E' : Env Γ'} → ⟨ t i  ∥ s-comp W E k E' ⟩ →ᴸᴸ ⟨ i ∥ E' ⟩


data _→ᴸᴸ*_ : lState X → lState X → Set where

  _▣ : (S : lState X) → S →ᴸᴸ* S

  _→ᴸᴸ⟨_⟩_ : (S : lState X) → {S' S'' : lState X} → S →ᴸᴸ S' → S' →ᴸᴸ* S'' → S →ᴸᴸ* S''


_⨾ᴸ_ : {F S T : lState X} → (F →ᴸᴸ* S) → (S →ᴸᴸ* T) → (F →ᴸᴸ* T)
_⨾ᴸ_ (S ▣) S>>T = S>>T
_⨾ᴸ_ (F →ᴸᴸ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᴸᴸ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ᴸ S₂>>T)


data lHaltingState : lState X → Set where

      found-unit : {γ : Env Γ} → lHaltingState ⟨ h ∥ _﹐_ γ u̲n̲i̲t̲ ⟩

      found-pair : {LHS : V̲a̲l̲ Γ X} → {RHS : V̲a̲l̲ Γ Y} → {γ : Env Γ} → lHaltingState ⟨ h ∥ _﹐_ γ (p̲a̲i̲r̲ LHS RHS) ⟩

      found-lam : {W : (Γ ∙ X) ⊢ᶜ Y} → {γ : Env Γ} → lHaltingState ⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩


data correctStepsLL : lState X → Set where

  steps : {S T : lState X} → S →ᴸᴸ* T → lHaltingState T → ⟦ S ⟧ᴸ ≡ ⟦ T ⟧ᴸ → (π : Wk (lCtx S) (lTCtx T)) → (⟦ π ⟧ʷ ⟦ lEnv S ⟧ᴱ ≡ ⟦ lTEnv T ⟧ᴱ) → correctStepsLL S


lookup : (i : Γ ∋ X) → (γ : Env Γ) → correctStepsLL {X = X} ⟨ i ∥ γ ⟩
lookup h (_﹐_ γ (l̲a̲m̲ W)) = steps (⟨ h ∥ _﹐_ γ (l̲a̲m̲ W) ⟩ ▣) found-lam refl (wk-wk wk-id) refl
lookup h (_﹐_ γ (p̲a̲i̲r̲ LHS RHS)) = steps (⟨ h ∥ _﹐_ γ (p̲a̲i̲r̲ LHS RHS) ⟩ ▣) found-pair refl (wk-wk wk-id) refl
lookup h (_﹐_ γ u̲n̲i̲t̲) = steps (⟨ h ∥ _﹐_ γ (u̲n̲i̲t̲) ⟩ ▣) found-unit refl (wk-wk wk-id) refl
lookup (t i) (_﹐_ γ M) with lookup i γ
... | steps i>>T HT i≡T WK w≡γ = steps (_ →ᴸᴸ⟨ val-t-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ

------------------------------------------------------------------------------

data goodType : Bool → Ty → Ty → Set where

     ↓ : goodType false X X

     ↕ : goodType true X Y

data partialTerm : (Γ : Ctx) → (X : Ty) → Set where

    ⭭_ : V̲a̲l̲ Γ X → partialTerm Γ X

    ⇡_ : (M : Γ ⊢ᵛ X) → partialTerm Γ X

    ⇡ᴹ : (M : Γ ⊢ᵛ X `× Y) → (N : (Γ ∙ X ∙ Y) ⊢ᵛ Z) → partialTerm Γ Z

    ⇡ᴸ : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → partialTerm Γ (X `× Y)

    ⇡ᴿ  : (LHS : V̲a̲l̲ Γ X) → (RHS : Γ ⊢ᵛ Y) → partialTerm Γ (X `× Y)


data vStack : Bool → Ty → Set where

    □ : vStack false T◾

    _⹁_∷_ : partialTerm Γ X → (γ : Env Γ) → (tail : vStack b T◾) → {gt : goodType b X T◾} → vStack true T◾

data vState : Ty → Set where

     ∘_ : vStack true T◾ → vState T◾

     ∙_ : vStack true T◾ → vState T◾

data _→ᵛᵛ_ : vState T◾ → vState T◾ → Set where

     ∘var    :    {i : Γ ∋ X} → {tail : vStack b T◾} → {gt : goodType b X T◾}
                → {M : V̲a̲l̲ Γ' X}
                → (⟨ i ∥ γ ⟩ →ᴸᴸ* ⟨ h ∥ _﹐_ γ' M ⟩) → (πᵥ : Wk Γ Γ')
               ----------------------------------------------------------------
                → ∘ ((⇡ var i ⹁ γ ∷ tail) {gt = gt}) →ᵛᵛ ∙ ((⭭ (wk-v̲a̲l̲ πᵥ M) ⹁ γ ∷ tail) {gt = gt})


     ∘lam   :  {M : (Γ ∙ X) ⊢ᶜ Y} → {γ  : Env Γ}
             → {tail : vStack b T◾} → {gt : goodType b (X `⇒ Y) T◾}
               ---------------------------------------------------------------------------
             →     ∘ ((⇡ lam M ⹁ γ ∷ tail) {gt = gt})
                →ᵛᵛ ∙ ((⭭ l̲a̲m̲ M ⹁ γ ∷ tail) {gt = gt})

     ∘pair  :  {LHS : Γ ⊢ᵛ X} → {RHS : Γ ⊢ᵛ Y}
             → {tail : vStack b T◾} → {gt : goodType b (X `× Y) T◾}
               ---------------------------------------------------------------------------
             →     ∘ ((⇡ pair LHS RHS ⹁ γ ∷ tail) {gt = gt})
                →ᵛᵛ ∘ ((⇡ LHS ⹁ γ ∷ ((⇡ᴸ LHS RHS ⹁ γ ∷ tail) {gt = gt})) {gt = ↕})

     ∘pm    :  {M : Γ ⊢ᵛ X `× Y} → {N : (Γ ∙ X ∙ Y) ⊢ᵛ Z}
             → {tail : vStack b T◾} → {gt : goodType b Z T◾}
               ---------------------------------------------------------------------------
             →     ∘ ((⇡ pm M N ⹁ γ ∷ tail) {gt = gt})
                →ᵛᵛ ∘ ((⇡ M ⹁ γ ∷ (⇡ᴹ M N ⹁ γ ∷ tail) {gt = gt}) {gt = ↕})

     ∘unit  :  {γ  : Env Γ}
             → {tail : vStack b T◾} → {gt : goodType b `Unit T◾}
               ---------------------------------------------------------------------------
             →     ∘ ((⇡ unit ⹁ γ ∷ tail) {gt = gt})
                →ᵛᵛ ∙ ((⭭ u̲n̲i̲t̲ ⹁ γ ∷ tail) {gt = gt})

     ∙M∷l   :  {M : V̲a̲l̲ Γ X} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y} → {π' : Wk Γ Γ'}
             → {tail : vStack b T◾} → {gt : goodType b (X `× Y) T◾}
               ---------------------------------------------------------------------------
             →     ∙ ((⭭ M ⹁ γ ∷ ((⇡ᴸ LHS RHS ⹁ γ' ∷ tail) {gt = gt})) {gt = ↕})
                →ᵛᵛ ∘ ((⇡ wk-val π' RHS ⹁ γ ∷ ((⇡ᴿ M (wk-val π' RHS) ⹁ γ ∷ tail) {gt = gt})) {gt = ↕})

     ∙M∷r   :  {M : V̲a̲l̲ Γ Y} → {LHS : V̲a̲l̲ Γ' X} → {RHS : Γ' ⊢ᵛ Y} {π' : Wk Γ Γ'}
             → {tail : vStack b T◾} → {gt : goodType b (X `× Y) T◾}
               ---------------------------------------------------------------------------
             →     ∙ ((⭭ M ⹁ γ ∷ ((⇡ᴿ LHS RHS ⹁ γ' ∷ tail) {gt = gt})) {gt = ↕})
                →ᵛᵛ ∙ ((⭭ p̲a̲i̲r̲ (wk-v̲a̲l̲ π' LHS) M ⹁ γ ∷ tail) {gt = gt})

     ∙pair∷pm  :  {LHS : V̲a̲l̲ Γ X} → {RHS : V̲a̲l̲ Γ Y} → {M : Γ' ⊢ᵛ X `× Y} → {N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z'}
             → {π' : Wk Γ Γ'}
             → {tail : vStack b T◾} → {gt : goodType b Z' T◾}
               ---------------------------------------------------------------------------
             →     ∙ ((⭭ p̲a̲i̲r̲ LHS RHS ⹁ γ ∷ ((⇡ᴹ M N ⹁ γ' ∷ tail) {gt = gt})) {gt = ↕})
                →ᵛᵛ  ∘ ((⇡ (wk-val (wk-cong (wk-cong π')) N) ⹁ _﹐_ ((_﹐_ γ LHS)) (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ∷ tail) {gt = gt})


data _↠ᵛᵛ_ : vState T◾ → vState T◾ → Set where

  _→ᵛᵛ⟨_⟩ : (S : vState T◾) → {S' : vState T◾} → (laststep : S →ᵛᵛ S') → S ↠ᵛᵛ S'

  _→ᵛᵛ⟨_⟩_ : (S : vState T◾) → {S' S'' : vState T◾} → S →ᵛᵛ S' → S' ↠ᵛᵛ S'' → S ↠ᵛᵛ S''

_⨾_ : {F S T : vState T◾} → (F ↠ᵛᵛ S) → (S ↠ᵛᵛ T) → (F ↠ᵛᵛ T)
_⨾_ (F →ᵛᵛ⟨ F>S ⟩) S>>T = F →ᵛᵛ⟨ F>S ⟩ S>>T
_⨾_ (F →ᵛᵛ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᵛᵛ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ S₂>>T)

_⦂⦂_ : vStack b T◾ → vStack true T◾' → vStack true T◾'
□ ⦂⦂ lower = lower
(M ⹁ γ ∷ upper) ⦂⦂ lower = (M ⹁ γ ∷ (upper ⦂⦂ lower)) {gt = ↕}

_::_ : (upper : vState T◾) → vStack true T◾' → vState T◾'
(∘ upper) :: lower = ∘ (upper ⦂⦂ lower)
(∙ upper) :: lower = ∙ (upper ⦂⦂ lower)

⟨_⟩∷_ : {from : vState T◾} → {to : vState T◾} → (F>T : from →ᵛᵛ to) → (tail : vStack true T◾') → (from :: tail) →ᵛᵛ (to :: tail)
⟨ ∘var T>>U π ⟩∷ tail = ∘var T>>U π
⟨ ∘lam ⟩∷ tail = ∘lam
⟨ ∘pair ⟩∷ tail = ∘pair
⟨ ∘pm ⟩∷ tail = ∘pm
⟨ ∘unit ⟩∷ tail = ∘unit
⟨ ∙pair∷pm ⟩∷ tail = ∙pair∷pm
⟨ ∙M∷l ⟩∷ tail = ∙M∷l
⟨ ∙M∷r ⟩∷ tail = ∙M∷r

⟪_⟫∷_ : {from : vState T◾} → {to : vState T◾} → (F>T : from ↠ᵛᵛ to) → (tail : vStack true T◾') → (from :: tail) ↠ᵛᵛ (to :: tail)
⟪ _ →ᵛᵛ⟨ F>T ⟩ ⟫∷ tail =  _ →ᵛᵛ⟨ ⟨ F>T ⟩∷ tail ⟩
⟪ _ →ᵛᵛ⟨ F>T ⟩ F>>T ⟫∷ tail =   _ →ᵛᵛ⟨ ⟨ F>T ⟩∷ tail ⟩ (⟪ F>>T ⟫∷ tail)

⟦_⟧↥ : (S : vStack true T◾) → ⟦ T◾ ⟧
⟦ (⭭ x ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ V̲a̲l̲-to-Val x ⟧ᵛ ⟦ γ ⟧ᴱ
⟦ (⇡ M ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ M ⟧ᵛ ⟦ γ ⟧ᴱ
⟦ (⇡ᴹ M N ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ pm M N ⟧ᵛ ⟦ γ ⟧ᴱ
⟦ (⇡ᴸ LHS RHS ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ pair LHS RHS ⟧ᵛ ⟦ γ ⟧ᴱ
⟦ (⇡ᴿ LHS RHS ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ pair (V̲a̲l̲-to-Val LHS) RHS ⟧ᵛ ⟦ γ ⟧ᴱ
⟦ (⭭ x ⹁ γ ∷ ((x₁ ⹁ γ₁ ∷ S) {gt = gt})) {gt = ↕} ⟧↥ = ⟦ (x₁ ⹁ γ₁ ∷ S) {gt = gt} ⟧↥
⟦ (⇡ M ⹁ γ ∷ ((x₁ ⹁ γ₁ ∷ S) {gt = gt})) {gt = ↕} ⟧↥ = ⟦ (x₁ ⹁ γ₁ ∷ S) {gt = gt} ⟧↥
⟦ (⇡ᴹ M N ⹁ γ ∷ ((x₁ ⹁ γ₁ ∷ S) {gt = gt})) {gt = ↕} ⟧↥ = ⟦ (x₁ ⹁ γ₁ ∷ S) {gt = gt} ⟧↥
⟦ (⇡ᴸ LHS RHS ⹁ γ ∷ ((x₁ ⹁ γ₁ ∷ S) {gt = gt})) {gt = ↕} ⟧↥ = ⟦ (x₁ ⹁ γ₁ ∷ S) {gt = gt} ⟧↥
⟦ (⇡ᴿ LHS RHS ⹁ γ ∷ ((x₁ ⹁ γ₁ ∷ S) {gt = gt})) {gt = ↕} ⟧↥ = ⟦ (x₁ ⹁ γ₁ ∷ S) {gt = gt} ⟧↥


⟦_⟧◑ : (S : vState T◾) → ⟦ T◾ ⟧
⟦ ∘ tail ⟧◑ = ⟦ tail ⟧↥
⟦ ∙ tail ⟧◑ = ⟦ tail ⟧↥

topCtx : vState T◾ → Ctx
topCtx (∘ ⭭_ {Γ = Γ} x ⹁ γ ∷ x₁) = Γ
topCtx (∘ ⇡_ {Γ = Γ} M ⹁ γ ∷ x₁) = Γ
topCtx (∘ ⇡ᴹ {Γ = Γ} M N ⹁ γ ∷ x₁) = Γ
topCtx (∘ ⇡ᴸ {Γ = Γ} LHS RHS ⹁ γ ∷ x₁) = Γ
topCtx (∘ ⇡ᴿ {Γ = Γ} LHS RHS ⹁ γ ∷ x₁) = Γ
topCtx (∙ ⭭_ {Γ = Γ} x ⹁ γ ∷ x₁) = Γ
topCtx (∙ ⇡_ {Γ = Γ} M ⹁ γ ∷ x₁) = Γ
topCtx (∙ ⇡ᴹ {Γ = Γ} M N ⹁ γ ∷ x₁) = Γ
topCtx (∙ ⇡ᴸ {Γ = Γ} LHS RHS ⹁ γ ∷ x₁) = Γ
topCtx (∙ ⇡ᴿ {Γ = Γ} LHS RHS ⹁ γ ∷ x₁) = Γ

topEnv : (S : vState T◾) → Env (topCtx S)
topEnv (∘ ⭭ x ⹁ γ ∷ x₁) = γ
topEnv (∘ ⇡ M ⹁ γ ∷ x₁) = γ
topEnv (∘ ⇡ᴹ M N ⹁ γ ∷ x₁) = γ
topEnv (∘ ⇡ᴸ LHS RHS ⹁ γ ∷ x₁) = γ
topEnv (∘ ⇡ᴿ LHS RHS ⹁ γ ∷ x₁) = γ
topEnv (∙ ⭭ x ⹁ γ ∷ x₁) = γ
topEnv (∙ ⇡ M ⹁ γ ∷ x₁) = γ
topEnv (∙ ⇡ᴹ M N ⹁ γ ∷ x₁) = γ
topEnv (∙ ⇡ᴸ LHS RHS ⹁ γ ∷ x₁) = γ
topEnv (∙ ⇡ᴿ LHS RHS ⹁ γ ∷ x₁) = γ

data vHaltingState : vState T◾ → Set where

     ∙_⹁_■ : (M : V̲a̲l̲ Γ X) → (γ : Env Γ) → vHaltingState (∙ ((⭭ M ⹁ γ ∷ □) {gt = ↓}))


data correctSteps : vState T◾ → Set where

  steps : {S T : vState T◾} → S ↠ᵛᵛ T → vHaltingState T → ⟦ S ⟧◑ ≡ ⟦ T ⟧◑ → (π : Wk (topCtx T) (topCtx S)) → (⟦ π ⟧ʷ ⟦ topEnv T ⟧ᴱ ≡ ⟦ topEnv S ⟧ᴱ) → correctSteps S


wk-comm : {M : V̲a̲l̲ Γ X} → {π : Wk Δ Γ} → wk-val π (V̲a̲l̲-to-Val M) ≡ V̲a̲l̲-to-Val (wk-v̲a̲l̲ π M)
wk-comm {Γ = Γ} {Δ = Δ} {M = l̲a̲m̲ W} {π = π} = refl
wk-comm {Γ = Γ} {Δ = Δ} {M = p̲a̲i̲r̲ LHS RHS} {π = π} = trans (cong (λ x → pair x _) wk-comm) ((cong (λ x → pair _ x) wk-comm))
wk-comm {Γ = Γ} {Δ = Δ} {M = u̲n̲i̲t̲} {π = π} = refl


wk-mem-trans : (i : Γ ∋ Z) → (π₁ : Wk Γ'' Γ') → (π₂ : Wk Γ' Γ) → wk-mem π₁ (wk-mem π₂ i) ≡ wk-mem (wk-trans π₁ π₂) i
wk-mem-trans Cx.h (wk-cong π₁) (wk-cong π₂) = refl
wk-mem-trans Cx.h (wk-cong π₁) (wk-wk π₂) = cong t (wk-mem-trans h π₁ π₂)
wk-mem-trans Cx.h (wk-wk π₁) (wk-cong π₂) = cong t (wk-mem-trans h π₁ (wk-cong π₂))
wk-mem-trans Cx.h (wk-wk π₁) (wk-wk π₂) = cong t (wk-mem-trans h π₁ (wk-wk π₂))
wk-mem-trans (Cx.t i) (wk-cong π₁) (wk-cong π₂) = cong t (wk-mem-trans i π₁ π₂)
wk-mem-trans (Cx.t i) (wk-wk (wk-cong π₁)) (wk-cong π₂) = cong t (cong t (wk-mem-trans i π₁ π₂))
wk-mem-trans (Cx.t i) (wk-wk (wk-wk π₁)) (wk-cong π₂) = cong t (cong t (wk-mem-trans (t i) π₁ (wk-cong π₂)))
wk-mem-trans (Cx.t i) (wk-cong π₁) (wk-wk π₂) = cong t (wk-mem-trans (t i) π₁ π₂)
wk-mem-trans (Cx.t i) (wk-wk (wk-cong π₁)) (wk-wk π₂) = cong t (wk-mem-trans (t i) (wk-cong π₁) (wk-wk π₂))
wk-mem-trans (Cx.t i) (wk-wk (wk-wk π₁)) (wk-wk π₂) = cong t (wk-mem-trans (t i) (wk-wk π₁) (wk-wk π₂))

wk-val-trans : (M : Γ ⊢ᵛ Z) → (π₁ : Wk Γ'' Γ') → (π₂ : Wk Γ' Γ) → wk-val π₁ (wk-val π₂ M) ≡ wk-val (wk-trans π₁ π₂) M
wk-comp-trans : (W : Γ ⊢ᶜ Z) → (π₁ : Wk Γ'' Γ') → (π₂ : Wk Γ' Γ) → wk-comp π₁ (wk-comp π₂ W) ≡ wk-comp (wk-trans π₁ π₂) W

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

lem2 : (π₁ : Wk Γ'' Γ') → (π₂ : Wk Γ' Γ) → (γ : ⟦ Γ'' ⟧ˣ) → ⟦ π₂ ⟧ʷ (⟦ π₁ ⟧ʷ γ) ≡ ⟦ wk-trans π₁ π₂ ⟧ʷ γ
lem2 wk-ε π₂ γ = refl
lem2 {Γ = Cx.ε} (wk-cong π₁) π₂ γ = refl
lem2 {Γ = Γ Cx.∙ x} (wk-cong π₁) (wk-cong π₂) γ = -- {!refl!}
       ⟦ wk-cong π₂ ⟧ʷ (⟦ wk-cong π₁ ⟧ʷ γ)
      ≡⟨ refl ⟩
       ⟦ π₂ ⟧ʷ (⟦ π₁ ⟧ʷ (proj₁ γ )) , proj₂ γ
      ≡⟨ cong (λ y → y , proj₂ γ) (lem2 π₁ π₂ (proj₁ γ)) ⟩
       ⟦ wk-trans π₁ π₂ ⟧ʷ (proj₁ γ) , proj₂ γ
      ≡⟨ refl ⟩
       ⟦ wk-cong (wk-trans π₁ π₂) ⟧ʷ γ ∎
lem2 {Γ = Γ Cx.∙ x} (wk-cong π₁) (wk-wk π₂) γ = --{!!}
       ⟦ wk-wk π₂ ⟧ʷ (⟦ wk-cong π₁ ⟧ʷ γ)
      ≡⟨ refl ⟩
       ⟦ π₂ ⟧ʷ (⟦ π₁ ⟧ʷ (proj₁ γ))
      ≡⟨ lem2 π₁ π₂ (proj₁ γ) ⟩
       ⟦ wk-trans π₁ π₂ ⟧ʷ (proj₁ γ)
      ≡⟨ refl ⟩
       ⟦ wk-trans (wk-cong π₁) (wk-wk π₂) ⟧ʷ γ ∎

lem2 (wk-wk π₁) wk-ε γ = refl

lem2 (wk-wk π₁) (wk-cong π₂) γ = --{!!}
       ⟦ wk-cong π₂ ⟧ʷ (⟦ wk-wk π₁ ⟧ʷ γ)
      ≡⟨ refl ⟩
       ⟦ π₂ ⟧ʷ (proj₁ (⟦ π₁ ⟧ʷ (proj₁ γ))) , proj₂ (⟦ π₁ ⟧ʷ (proj₁ γ))
      ≡⟨ lem2 π₁ (wk-cong π₂) (proj₁ γ) ⟩
       ⟦ wk-trans π₁ (wk-cong π₂) ⟧ʷ (proj₁ γ)
      ≡⟨ refl ⟩
       ⟦ wk-wk (wk-trans π₁ (wk-cong π₂)) ⟧ʷ γ ∎

lem2 (wk-wk π₁) (wk-wk π₂) γ = lem2 π₁ (wk-wk π₂) (proj₁ γ)


eval : (M : Γ' ⊢ᵛ X) → (γ : Env Γ) → (π : Wk Γ Γ') → correctSteps {T◾ = X} (∘ ((⇡ (wk-val π M) ⹁ γ ∷ □) {gt = ↓}))

eval (var i) γ π with lookup (wk-mem π i) γ
... | steps i>>T found-unit i≡T π₁ w≡γ = steps (_ →ᵛᵛ⟨ ∘var i>>T π₁ ⟩) (∙ u̲n̲i̲t̲ ⹁ γ ■) refl wk-id refl
... | steps i>>T (found-pair {LHS = LHS} {RHS = RHS} {γ = γ₁}) i≡T π₁ w≡γ = --{!!}

           steps

           (_ →ᵛᵛ⟨ ∘var i>>T π₁ ⟩)

           (∙ p̲a̲i̲r̲ (wk-v̲a̲l̲ π₁ LHS) (wk-v̲a̲l̲ π₁ RHS) ⹁ γ ■)

           (⟦ wk-mem π i ⟧ᵐ ⟦ γ ⟧ᴱ
           ≡⟨ i≡T ⟩
           (< ⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ , ⟦ V̲a̲l̲-to-Val RHS ⟧ᵛ > ⟦ γ₁ ⟧ᴱ)
           ≡⟨ cong (λ x → < ⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ , ⟦ V̲a̲l̲-to-Val RHS ⟧ᵛ > x) (sym w≡γ) ⟩
           (< ⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ , ⟦ V̲a̲l̲-to-Val RHS ⟧ᵛ > (⟦ π₁ ⟧ʷ ⟦ γ ⟧ᴱ))
           ≡⟨ refl ⟩
           (⟦ wk-val π₁ (V̲a̲l̲-to-Val LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ wk-val π₁ (V̲a̲l̲-to-Val RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)
           ≡⟨ cong (λ x → (⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ wk-val π₁ (V̲a̲l̲-to-Val RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)) (wk-comm {M = LHS} {π = π₁}) ⟩
           (⟦ V̲a̲l̲-to-Val (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ wk-val π₁ (V̲a̲l̲-to-Val RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)
           ≡⟨ cong (λ x → (⟦ V̲a̲l̲-to-Val (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ)) (wk-comm {M = RHS} {π = π₁}) ⟩
           (⟦ V̲a̲l̲-to-Val (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ V̲a̲l̲-to-Val (wk-v̲a̲l̲ π₁ RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)
           ≡⟨ refl ⟩
           (< ⟦ V̲a̲l̲-to-Val (wk-v̲a̲l̲ π₁ LHS) ⟧ᵛ , ⟦ V̲a̲l̲-to-Val (wk-v̲a̲l̲ π₁ RHS) ⟧ᵛ > ⟦ γ ⟧ᴱ) ∎)

           wk-id

           refl

... | steps i>>T (found-lam {W = W} {γ = γ₁}) i≡T π₁ w≡γ =

           steps

           (_ →ᵛᵛ⟨ ∘var i>>T π₁ ⟩)

           (∙ (wk-v̲a̲l̲ π₁ (l̲a̲m̲ W)) ⹁ γ ■)

           (⟦ wk-mem π i ⟧ᵐ ⟦ γ ⟧ᴱ
             ≡⟨ i≡T ⟩
           ((λ y → ⟦ W ⟧ᶜ (⟦ γ₁ ⟧ᴱ , y) ))
             ≡⟨ cong (λ x → (λ y → ⟦ W ⟧ᶜ (x , y) )) (sym w≡γ) ⟩
           (λ y → ⟦ W ⟧ᶜ (⟦ π₁ ⟧ʷ ⟦ γ ⟧ᴱ , y) )
             ≡⟨ refl ⟩
           (curry (< (λ r → proj₁ r) ； ⟦ π₁ ⟧ʷ , (λ r → proj₂ r) > ； ⟦ W ⟧ᶜ)) ⟦ γ ⟧ᴱ ∎)

           wk-id

           refl

eval (lam W) γ π = steps (∘ ⇡ (wk-val π (lam W)) ⹁ γ ∷ □ →ᵛᵛ⟨ ∘lam ⟩) (∙ l̲a̲m̲ (wk-comp (wk-cong π) W) ⹁ γ ■) refl wk-id refl
eval unit γ π = steps (_ →ᵛᵛ⟨ ∘unit ⟩) (∙ u̲n̲i̲t̲ ⹁ γ ■) refl wk-id refl

eval (pair {A = X} {B = Y} LHS RHS) γ π with eval {X = X} LHS γ π
... | steps {T = ∙ (⭭_ {X = X} LT ⹁ γ₁ ∷ □) {gt = ↓}} L>T ∙LT L≡T πᴸ wk≡ᴸ with  eval {X = Y} RHS γ₁ (wk-trans πᴸ π)
...      | steps {T = ∙ (⭭_ {X = Y} RT ⹁ γ₂ ∷ □) {gt = ↓}} R>T ∙RT R≡T πᴿ wk≡ᴿ rewrite sym (wk-val-trans RHS πᴸ π) = --{!!}

          steps

            (
             ∘ ⇡ (wk-val π (pair LHS RHS)) ⹁ γ ∷ □ →ᵛᵛ⟨ ∘pair ⟩  ⨾ -- (∘ ⇡ wk-val π LHS ⹁ γ ∷ ⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⹁ γ ∷ □)
             (⟪ L>T ⟫∷ (⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⹁ γ ∷ □)) ⨾
             (∙ ⭭ LT ⹁ γ₁ ∷ ⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⹁ γ ∷ □) →ᵛᵛ⟨ ∙M∷l ⟩ ⨾ -- (∘ ⇡ wk-val _π'_3203 (wk-val π RHS) ⹁ γ₁ ∷ ⇡ᴿ LT (wk-val _π'_3203 (wk-val π RHS)) ⹁ γ₁ ∷ □)
             (⟪ R>T ⟫∷ (⇡ᴿ LT (wk-val πᴸ (wk-val π RHS)) ⹁ γ₁ ∷ □)) ⨾
             (∙ ⭭ RT ⹁ γ₂ ∷ ⇡ᴿ LT (wk-val πᴸ (wk-val π RHS)) ⹁ γ₁ ∷ □) →ᵛᵛ⟨ ∙M∷r ⟩
            )

            ∙ p̲a̲i̲r̲ (wk-v̲a̲l̲ πᴿ LT) RT ⹁ γ₂ ■

            ( ⟦ wk-val π (pair LHS RHS) ⟧ᵛ ⟦ γ ⟧ᴱ
             ≡⟨ refl ⟩
               (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))
             ≡⟨ cong (λ y → (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ y))) (sym wk≡ᴸ) ⟩
               (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ (⟦ πᴸ ⟧ʷ ⟦ γ₁ ⟧ᴱ)))
             ≡⟨ cong (λ y → (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ y)) (lem2 πᴸ π ⟦ γ₁ ⟧ᴱ) ⟩
               (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
             ≡⟨ cong (λ y → (y , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))) L≡T ⟩
               (⟦ V̲a̲l̲-to-Val LT ⟧ᵛ ⟦ γ₁ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
             ≡⟨ cong (λ y → (⟦ V̲a̲l̲-to-Val LT ⟧ᵛ y , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))) (sym wk≡ᴿ) ⟩
               (⟦ V̲a̲l̲-to-Val LT ⟧ᵛ (⟦ πᴿ ⟧ʷ ⟦ γ₂ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
             ≡⟨ refl ⟩
               (⟦ wk-val πᴿ (V̲a̲l̲-to-Val LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
             ≡⟨ cong (λ y → (⟦ y ⟧ᵛ ⟦ γ₂ ⟧ᴱ  , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))) (wk-comm {M = LT} {π = πᴿ}) ⟩
               (⟦ V̲a̲l̲-to-Val (wk-v̲a̲l̲ πᴿ LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
             ≡⟨ cong (λ y → (⟦ V̲a̲l̲-to-Val (wk-v̲a̲l̲ πᴿ LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , y)) R≡T ⟩
               (⟦ V̲a̲l̲-to-Val (wk-v̲a̲l̲ πᴿ LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , ⟦ V̲a̲l̲-to-Val RT ⟧ᵛ ⟦ γ₂ ⟧ᴱ)
             ≡⟨ refl ⟩
               ⟦ pair (V̲a̲l̲-to-Val (wk-v̲a̲l̲ πᴿ LT)) (V̲a̲l̲-to-Val RT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ
             ≡⟨ refl ⟩
               ⟦ V̲a̲l̲-to-Val (p̲a̲i̲r̲ (wk-v̲a̲l̲ πᴿ LT) RT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ
             ≡⟨ refl ⟩
               ⟦ ∙ (⭭ p̲a̲i̲r̲ (wk-v̲a̲l̲ πᴿ LT) RT ⹁ γ₂ ∷ □) {gt = ↓} ⟧◑ ∎ )

            (wk-trans πᴿ πᴸ)

            ( ⟦ wk-trans πᴿ πᴸ ⟧ʷ ⟦ γ₂ ⟧ᴱ
            ≡⟨ sym (lem2 πᴿ πᴸ ⟦ γ₂ ⟧ᴱ) ⟩
               ⟦ πᴸ ⟧ʷ (⟦ πᴿ ⟧ʷ ⟦ γ₂ ⟧ᴱ)
            ≡⟨ cong (λ y → ⟦ πᴸ ⟧ʷ y) wk≡ᴿ ⟩
               ⟦ πᴸ ⟧ʷ ⟦ γ₁ ⟧ᴱ
            ≡⟨ wk≡ᴸ ⟩
               ⟦ γ ⟧ᴱ ∎)

eval (pm M N) γ π with eval M γ π
... | steps M>T ∙ p̲a̲i̲r̲ LHS RHS ⹁ γ₁ ■ M≡T π₁ wk≡₁ with eval N (_﹐_ (_﹐_ γ₁ LHS) (wk-v̲a̲l̲ (wk-wk wk-id) RHS)) ((wk-cong (wk-cong (wk-trans π₁ π)))) | (wk-val-trans N (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π)))
...    | steps {T = T} N>T ∙T N≡T π₂ wk≡₂ | eq with N>T
...      | N>T' rewrite sym eq =
       steps
         (
          (∘ ⇡ pm (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⹁ γ ∷ □) →ᵛᵛ⟨ ∘pm ⟩ ⨾ -- (∘ ⇡ wk-val π M ⹁ γ ∷ ⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⹁ γ ∷ □)
          (⟪ M>T ⟫∷ (⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⹁ γ ∷ □)) ⨾
          (∙ ⭭ p̲a̲i̲r̲ LHS RHS ⹁ γ₁ ∷ ⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⹁ γ ∷ □) →ᵛᵛ⟨ ∙pair∷pm ⟩ ⨾ -- (∘ ⇡ wk-val (wk-cong (wk-cong π₁)) (wk-val (wk-cong (wk-cong π)) N) ⹁ _﹐_ (_﹐_ γ₁ LHS) (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ∷ □)
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
           ⟦ wk-val (wk-cong (wk-cong π)) N ⟧ᵛ (assocl ( (⟦ γ ⟧ᴱ ,  (⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ , ⟦ V̲a̲l̲-to-Val RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)  )))
           ≡⟨ refl ⟩
            ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ V̲a̲l̲-to-Val RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
           ≡⟨ cong  (λ y → ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ y , ⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ V̲a̲l̲-to-Val RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)) (sym wk≡₁) ⟩
            ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ V̲a̲l̲-to-Val RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
           ≡⟨ refl ⟩
            ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ (wk-val (wk-wk wk-id) (V̲a̲l̲-to-Val RHS)) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
           ≡⟨ cong (λ y → ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ y ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))) (wk-comm {M = RHS} {π = wk-wk wk-id}) ⟩
            ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ V̲a̲l̲-to-Val (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
           ≡⟨ cong (λ y → ⟦ N ⟧ᵛ ((y , ⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ V̲a̲l̲-to-Val (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))  ) (lem2 π₁ π ⟦ γ₁ ⟧ᴱ) ⟩
           ⟦ N ⟧ᵛ ((⟦ wk-trans π₁ π ⟧ʷ ⟦ γ₁ ⟧ᴱ , ⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ V̲a̲l̲-to-Val (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
           ≡⟨ N≡T ⟩
           ⟦ T ⟧◑ ∎)

         (wk-trans π₂ (wk-wk (wk-wk π₁)))

         ( ⟦ wk-trans π₂ (wk-wk (wk-wk π₁)) ⟧ʷ ⟦ topEnv T ⟧ᴱ
          ≡⟨ sym (lem2 π₂ (wk-wk (wk-wk π₁)) ⟦ topEnv T ⟧ᴱ) ⟩
           ⟦ wk-wk (wk-wk π₁) ⟧ʷ (⟦ π₂ ⟧ʷ ⟦ topEnv T ⟧ᴱ)
          ≡⟨ cong (λ y → ⟦ wk-wk (wk-wk π₁) ⟧ʷ y) wk≡₂ ⟩
           ⟦ wk-wk (wk-wk π₁) ⟧ʷ (((⟦ γ₁ ⟧ᴱ , ⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ V̲a̲l̲-to-Val (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ V̲a̲l̲-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))
          ≡⟨ refl ⟩
           ⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ
          ≡⟨ wk≡₁ ⟩
           ⟦ γ ⟧ᴱ ∎)


-- EXAMPLES
--------------------------------------------------

ex1 : ε ⊢ᵛ `Unit
ex1 = pm (pair unit unit) (var (t h))

ex2 : ε ⊢ᵛ `Unit `× `Unit
ex2 = pm (pm (pair (lam {A = `Unit} {B = `Unit} (return (var h))) unit) (pair unit (var (t h)))) (pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))))

---------------------------------------

-- calling agda2-compute-normalised in the hole below evaluates example
--_ : eval ex2 z wk-id ≡ {!eval ex2 z wk-id!}
--_ = refl

