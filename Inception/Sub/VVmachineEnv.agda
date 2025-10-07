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
--  γ  : ⟦ Γ ⟧ˣ
--  γ' : ⟦ Γ' ⟧ˣ

infix  26 ⭭_
infix  26 ⇡_
infixr 25 _⹁_∷_
--infixr 25 _⹁_∷⟨_⟩_
infix  20 ∘_
infix  20 ∙_
infixr 17 _→ᵛᵛ⟨_⟩
infixr 15 _→ᵛᵛ⟨_⟩_
infix  15 _→ᵛᵛ_
infixr 10 _⨾_

data Bool : Set where
     true : Bool
     false : Bool

data valTerm : Ctx → Ty → Set where

    val-lam : (Γ ∙ X) ⊢ᶜ Y → valTerm Γ (X `⇒ Y)

    val-pair : valTerm Γ X → valTerm Γ Y → valTerm Γ (X `× Y)
    --val-pair : Γ ⊢ᵛ X → Γ ⊢ᵛ Y → valTerm Γ (X `× Y)

    val-unit : valTerm Γ `Unit

data Env : (Γ : Ctx) → Set where

    z       :  (γ : ⟦ ε ⟧ˣ) → Env ε

    --s-val   :  {WK : Wk Γ ε} → {WK' : Wk Γ' ε} → (M : valTerm Γ X) → Env ε Γ {WK = WK} → Env ε Γ' {WK = WK'} → Env ε (Γ' ∙ X) {WK = wk-wk WK'}
    s-val   :  (M : valTerm Γ X) → Env Γ → Env (Γ ∙ X)

--    s-comp  :  (W : Γ ⊢ᶜ X) → Env Γ → (k : ⟦ X ⟧ → R) → Env Γ' → Env (Γ' ∙ `V)

valTerm-to-Val : valTerm Γ X → Γ ⊢ᵛ X
valTerm-to-Val (val-lam W) = lam W
valTerm-to-Val (val-pair LHS RHS) = pair (valTerm-to-Val LHS) (valTerm-to-Val RHS)
--valTerm-to-Val (val-pair LHS RHS) = pair LHS RHS
valTerm-to-Val (val-unit) = unit

wk-valTerm : Wk Γ Δ -> valTerm Δ X -> valTerm Γ X
wk-valTerm π (val-lam W) = val-lam ((wk-comp (wk-cong π) W))
wk-valTerm π (val-pair LHS RHS) = val-pair (wk-valTerm π LHS) (wk-valTerm π RHS)
wk-valTerm π val-unit = val-unit

wk-trans : Wk Γ Δ → Wk Δ Ψ → Wk Γ Ψ
wk-trans wk-ε π₂ = π₂
wk-trans (wk-cong π₁) (wk-cong π₂) = wk-cong (wk-trans π₁ π₂)
wk-trans (wk-cong π₁) (wk-wk π₂) = wk-wk (wk-trans π₁ π₂)
wk-trans (wk-wk π₁) π₂ = wk-wk (wk-trans π₁ π₂)

wk-trans' : Wk Γ Δ → Wk Δ Ψ → Wk Γ Ψ
wk-trans' π₁ wk-ε = π₁
wk-trans' (wk-cong π₁) (wk-cong π₂) = wk-cong (wk-trans' π₁ π₂)
wk-trans' (wk-cong π₁) (wk-wk π₂) = wk-wk (wk-trans' π₁ π₂)
wk-trans' (wk-wk π₁) (wk-cong π₂) = wk-wk (wk-trans' π₁ (wk-cong π₂))
wk-trans' (wk-wk π₁) (wk-wk π₂) = wk-wk (wk-trans' π₁ (wk-wk π₂))


variable
    b : Bool
    γ  : Env Γ
    γ' : Env Γ'
    γ'' : Env Γ''


---------------------------------------------------------

infix  15 _→ᴸᴸ_


⟦_⟧ᴱ : (E : Env Γ) → ⟦ Γ ⟧ˣ
⟦ z γ ⟧ᴱ = γ
⟦ s-val M E ⟧ᴱ = ⟦ E ⟧ᴱ , ⟦ valTerm-to-Val M ⟧ᵛ ⟦ E ⟧ᴱ
--⟦ s-comp W E k E' ⟧ᴱ = ⟦ E' ⟧ᴱ , ⟦ W ⟧ᶜ ⟦ E ⟧ᴱ k

data lState : Ty → Set where

    ⟨_∥_⟩   :  (i : Γ ∋ X) → Env Γ → lState X

⟦_⟧ᴸ : (S : lState X) → ⟦ X ⟧
⟦ ⟨ i ∥ E ⟩ ⟧ᴸ = ⟦ i ⟧ᵐ ⟦ E ⟧ᴱ

lCtx : (S : lState X) → Ctx
lCtx (⟨_∥_⟩ {Γ = Γ} i E)= Γ

lTCtx : (S : lState X) → Ctx
lTCtx (⟨_∥_⟩ i (z γ)) = ε
lTCtx (⟨_∥_⟩ i (s-val {Γ = Γ} M E)) = Γ

lEnv : (S : lState X) → Env (lCtx S)
lEnv ⟨ i ∥ E ⟩ = E

lTEnv : (S : lState X) → Env (lTCtx S)
lTEnv ⟨ i ∥ s-val M E ⟩ = E

data _→ᴸᴸ_ : lState X → lState X → Set where

    --val-h-step    : {i : Γ ∋ Y} → {E : Env Γ} → {E' : Env Γ'} → ⟨ h  ∥ s-val (var i) E E' ⟩ →ᴸᴸ ⟨ i ∥ E ⟩

    val-t-step    : {i : Γ ∋ Y} → {E : Env Γ} → {M : valTerm Γ X} → ⟨ t i  ∥ s-val M E ⟩ →ᴸᴸ ⟨ i ∥ E ⟩

--    comp-t-step    : {i : Γ' ∋ Y} → {E : Env Γ} → {W : Γ ⊢ᶜ X} → {k : ⟦ X ⟧ → R} → {E' : Env Γ'} → ⟨ t i  ∥ s-comp W E k E' ⟩ →ᴸᴸ ⟨ i ∥ E' ⟩


data _→ᴸᴸ*_ : lState X → lState X → Set where

  _▣ : (S : lState X) → S →ᴸᴸ* S

  _→ᴸᴸ⟨_⟩_ : (S : lState X) → {S' S'' : lState X} → S →ᴸᴸ S' → S' →ᴸᴸ* S'' → S →ᴸᴸ* S''


_⨾ᴸ_ : {F S T : lState X} → (F →ᴸᴸ* S) → (S →ᴸᴸ* T) → (F →ᴸᴸ* T)
_⨾ᴸ_ (S ▣) S>>T = S>>T
_⨾ᴸ_ (F →ᴸᴸ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᴸᴸ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ᴸ S₂>>T)


data nicelHaltingState : lState X → Set where

      found-unit : {γ : Env Γ} → nicelHaltingState ⟨ h ∥ s-val val-unit γ ⟩

      found-pair : {LHS : valTerm Γ X} → {RHS : valTerm Γ Y} → {γ : Env Γ} → nicelHaltingState ⟨ h ∥ s-val (val-pair LHS RHS) γ ⟩
      --found-pair : {LHS : Γ ⊢ᵛ X} → {RHS : Γ ⊢ᵛ Y} → {WK : Wk Γ ε} → {γ : Env ε Γ {WK = WK}} → nicelHaltingState ⟨ h ∥ s-val (val-pair RHS LHS) γ ⟩

      found-lam : {W : (Γ ∙ X) ⊢ᶜ Y} → {γ : Env Γ} → nicelHaltingState ⟨ h ∥ s-val (val-lam W) γ ⟩


data nicecorrectStepsLL : lState X → Set where

  steps : {S T : lState X} → S →ᴸᴸ* T → nicelHaltingState T → ⟦ S ⟧ᴸ ≡ ⟦ T ⟧ᴸ → (π : Wk (lCtx S) (lTCtx T)) → (⟦ π ⟧ʷ ⟦ lEnv S ⟧ᴱ ≡ ⟦ lTEnv T ⟧ᴱ) → nicecorrectStepsLL S


lookup-t : (i : Γ ∋ X) → (γ : Env Γ) → nicecorrectStepsLL {X = X} ⟨ i ∥ γ ⟩
lookup-t h (s-val (val-lam W) γ) = steps (⟨ h ∥ s-val (val-lam W) γ ⟩ ▣) found-lam refl (wk-wk wk-id) refl
lookup-t h (s-val (val-pair LHS RHS) γ) = steps (⟨ h ∥ s-val (val-pair LHS RHS) γ ⟩ ▣) found-pair refl (wk-wk wk-id) refl
lookup-t h (s-val val-unit γ) = steps (⟨ h ∥ s-val (val-unit) γ ⟩ ▣) found-unit refl (wk-wk wk-id) refl
lookup-t (t i) (s-val M γ) with lookup-t i γ
... | steps i>>T HT i≡T WK w≡γ = steps (_ →ᴸᴸ⟨ val-t-step ⟩ i>>T) HT i≡T (wk-wk WK) w≡γ

------------------------------------------------------------------------------

data goodType : Bool → Ty → Ty → Set where

     ↓ : goodType false X X

     ↕ : goodType true X Y

data partialTerm : (Γ : Ctx) → (X : Ty) → Set where

    ⭭_ : valTerm Γ X → partialTerm Γ X

    ⇡_ : (M : Γ ⊢ᵛ X) → partialTerm Γ X

    ⇡ᴹ : (M : Γ ⊢ᵛ X `× Y) → (N : (Γ ∙ X ∙ Y) ⊢ᵛ Z) → partialTerm Γ Z

    ⇡ᴸ : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → partialTerm Γ (X `× Y)

    --⇡ᴿ  : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → partialTerm Γ (X `× Y)
    ⇡ᴿ  : (LHS : valTerm Γ X) → (RHS : Γ ⊢ᵛ Y) → partialTerm Γ (X `× Y)


data vStack : Bool → Ty → Set where

    □ : vStack false T◾

    _⹁_∷_ : partialTerm Γ X → (γ : Env Γ) → (tail : vStack b T◾) → {gt : goodType b X T◾} → vStack true T◾

data vState : Ty → Set where

     ∘_ : vStack true T◾ → vState T◾

     ∙_ : vStack true T◾ → vState T◾


--infix  15 _→ⱽᴸ_
--data _→ⱽᴸ_ : vState T◾ → lState X → Set where
--
--     start-lookup    : {i : Γ ∋ X} → {γ : Env Γ} → {tail : vStack b T◾} → {gt : goodType b X T◾} → ∘ ((⇡ var i ⹁ γ ∷ tail) {gt = gt}) →ⱽᴸ ⟨ i ∥ γ ∥ tail ﹐ gt ⟩
--
--infix  15 _→ᴸⱽ_
--data _→ᴸⱽ_ : lState X → vState T◾ → Set where
--
--     finish-lookup    : {M : (Γ ∙ X) ⊢ᵛ Y} → {γ : Env (Γ ∙ X)} → {γ' : Env Γ'} → {tail : vStack b T◾} → {gt : goodType b Y T◾} → ⟨ h ∥ s-val M γ γ' ∥ tail ﹐ gt ⟩ →ᴸⱽ ∙ ((⇡ M ⹁ γ ∷ tail) {gt = gt})

data _→ᵛᵛ_ : vState T◾ → vState T◾ → Set where

     -- ∘var-z    :    {i : Γ ∋ X} → {tail : vStack Γ' b T◾} → {gt : goodType b X T◾}

     --            → {i' : (Γ') ∋ X} → {γ' : ⟦ Γ' ⟧ˣ}

     --            → (⟨ i ∥ γ ⟩ →ᴸᴸ* ⟨ i' ∥ z γ' ⟩)
     --           ----------------------------------------------------------------
     --            → ∘ ((⇡ var i ⹁ γ ∷ tail) {gt = gt}) →ᵛᵛ ∙ ((_⹁_∷_ {ε = Γ'} (⇡ var i') (z γ') tail) {gt = gt}) -- ((⇡ var i' ⹁ (z γ') ∷ tail) {gt = gt})

     ∘var    :    {i : Γ ∋ X} → {tail : vStack b T◾} → {gt : goodType b X T◾}

                → {M : valTerm Γ' X} 

                → (⟨ i ∥ γ ⟩ →ᴸᴸ* ⟨ h ∥ s-val M γ' ⟩) → (πᵥ : Wk Γ Γ')

               ----------------------------------------------------------------
                → ∘ ((⇡ var i ⹁ γ ∷ tail) {gt = gt}) →ᵛᵛ ∙ ((⭭ (wk-valTerm πᵥ M) ⹁ γ ∷ tail) {gt = gt})


     ∘lam   :  {M : (Γ ∙ X) ⊢ᶜ Y} → {γ  : Env Γ}
             → {tail : vStack b T◾} → {gt : goodType b (X `⇒ Y) T◾}
               ---------------------------------------------------------------------------
             →     ∘ ((⇡ lam M ⹁ γ ∷ tail) {gt = gt})
                →ᵛᵛ ∙ ((⭭ val-lam M ⹁ γ ∷ tail) {gt = gt})

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
                →ᵛᵛ ∙ ((⭭ val-unit ⹁ γ ∷ tail) {gt = gt})

     ∙M∷l   :  {M : valTerm Γ X} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y} → {π' : Wk Γ Γ'}
             → {tail : vStack b T◾} → {gt : goodType b (X `× Y) T◾}
               ---------------------------------------------------------------------------
             →     ∙ ((⭭ M ⹁ γ ∷ ((⇡ᴸ LHS RHS ⹁ γ' ∷ tail) {gt = gt})) {gt = ↕})
                →ᵛᵛ ∘ ((⇡ wk-val π' RHS ⹁ γ ∷ ((⇡ᴿ M (wk-val π' RHS) ⹁ γ ∷ tail) {gt = gt})) {gt = ↕})
                --→ᵛᵛ ∘ ((⇡ RHS ⹁ γ' ∷⟨ ? ⟩ ((⇡ᴿ (var h) (wk-val (wk-wk wk-id) RHS) ⹁ s-val M γ γ' ∷⟨ ? ⟩ tail) {gt = gt})) {gt = ↕})

     ∙M∷r   :  {M : valTerm Γ Y} → {LHS : valTerm Γ' X} → {RHS : Γ' ⊢ᵛ Y} {π' : Wk Γ Γ'}
             → {tail : vStack b T◾} → {gt : goodType b (X `× Y) T◾}
               ---------------------------------------------------------------------------
             →     ∙ ((⭭ M ⹁ γ ∷ ((⇡ᴿ LHS RHS ⹁ γ' ∷ tail) {gt = gt})) {gt = ↕})
                →ᵛᵛ ∙ ((⭭ val-pair (wk-valTerm π' LHS) M ⹁ γ ∷ tail) {gt = gt})
                --→ᵛᵛ ∙ ((⭭ val-pair (wk-val (wk-wk wk-id) LHS) (var h) ⹁ s-val M γ γ' ∷⟨ ? ⟩ tail) {gt = gt})

     ∙pair∷pm  :  {LHS : valTerm Γ X} → {RHS : valTerm Γ Y} → {M : Γ' ⊢ᵛ X `× Y} → {N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z'}
             → {π' : Wk Γ Γ'}
             → {tail : vStack b T◾} → {gt : goodType b Z' T◾}
               ---------------------------------------------------------------------------
             →     ∙ ((⭭ val-pair LHS RHS ⹁ γ ∷ ((⇡ᴹ M N ⹁ γ' ∷ tail) {gt = gt})) {gt = ↕})
                →ᵛᵛ  ∘ ((⇡ (wk-val (wk-cong (wk-cong π')) N) ⹁ s-val (wk-valTerm (wk-wk wk-id) RHS) ((s-val LHS γ)) ∷ tail) {gt = gt})


     -- test   :  {M : valTerm Γ X} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y} → {π : Wk Γ' Ψ} → {π' : Wk Γ Γ'}
     --         → {tail : vStack Ψ Θ b T◾} → {gt : goodType b (X `× Y) T◾}
     --           ---------------------------------------------------------------------------
     --         →     ∙ ((⭭ M ⹁ γ ∷⟨ π' ⟩ ((⇡ᴸ LHS RHS ⹁ γ' ∷⟨ π ⟩ tail) {gt = gt})) {gt = ↕})
     --           →ᵛᵛ  ∙ ((⭭ M ⹁ γ ∷⟨ π' ⟩ ((⇡ᴸ LHS RHS ⹁ γ' ∷⟨ π ⟩ tail) {gt = gt})) {gt = ↕})


data _↠ᵛᵛ_ : vState T◾ → vState T◾ → Set where

  _→ᵛᵛ⟨_⟩ : (S : vState T◾) → {S' : vState T◾} → (laststep : S →ᵛᵛ S') → S ↠ᵛᵛ S'

  _→ᵛᵛ⟨_⟩_ : (S : vState T◾) → {S' S'' : vState T◾} → S →ᵛᵛ S' → S' ↠ᵛᵛ S'' → S ↠ᵛᵛ S''

_⨾_ : {F S T : vState T◾} → (F ↠ᵛᵛ S) → (S ↠ᵛᵛ T) → (F ↠ᵛᵛ T)
_⨾_ (F →ᵛᵛ⟨ F>S ⟩) S>>T = F →ᵛᵛ⟨ F>S ⟩ S>>T
_⨾_ (F →ᵛᵛ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᵛᵛ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ S₂>>T)

_⦂⦂_ : vStack b T◾ → vStack true T◾' → vStack true T◾'
□ ⦂⦂ lower = lower
(M ⹁ γ ∷ upper) ⦂⦂ lower = (M ⹁ γ ∷ (upper ⦂⦂ lower)) {gt = ↕}


{-
_⦂⦂⟨_⟩_ : vStack ε Ψ Θ true T◾ → Wk Θ Ψ' → vStack ε Ψ' Θ' true T◾' → vStack ε Ψ Θ' true T◾'


(M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ □) ⦂⦂⟨ π ⟩ lower = (M₁ ⹁ γ₁ ∷⟨ wk-trans π₁ π ⟩ lower ) {gt = ↕}
(M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ ((x ⹁ γ ∷⟨ π₃ ⟩ upper) {gt = gt})) ⦂⦂⟨ π ⟩ lower = (M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ (((x ⹁ γ ∷⟨ π₃ ⟩ upper) {gt = gt} ) ⦂⦂⟨ π ⟩ lower)) {gt = ↕}
--(M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ (x ⹁ γ ∷⟨ π₃ ⟩ □) {gt = ↓}) ⦂⦂⟨ π ⟩ lower = (M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ (x ⹁ γ ∷⟨ wk-trans π₃ π ⟩ lower) {gt = ↕}) {gt = ↕}
--(M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ (x ⹁ γ ∷⟨ π₃ ⟩ (x₁ ⹁ γ₂ ∷⟨ π₂ ⟩ upper) {gt = gt})) ⦂⦂⟨ π ⟩ lower = (M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ (x ⹁ γ ∷⟨ π₃ ⟩ (((x₁ ⹁ γ₂ ∷⟨ π₂ ⟩ upper) {gt = gt} ) ⦂⦂⟨ π ⟩ lower)) {gt = ↕}) {gt = ↕}

{-
(M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ □) ⦂⦂⟨ π ⟩ ((⭭ x ⹁ γ₂ ∷⟨ π₂ ⟩ lower) {gt = gt}) = (M₁ ⹁ γ₁ ∷⟨ wk-trans π₁ π ⟩ ((⭭ x ⹁ γ₂ ∷⟨ π₂ ⟩ lower)) {gt = gt} ) {gt = ↕}
(M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ □) ⦂⦂⟨ π ⟩ ((⇡ M ⹁ γ₂ ∷⟨ π₂ ⟩ lower) {gt = gt}) = (M₁ ⹁ γ₁ ∷⟨ wk-trans π₁ π ⟩ ((⇡ M ⹁ γ₂ ∷⟨ π₂ ⟩ lower)) {gt = gt} ) {gt = ↕}
(M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ □) ⦂⦂⟨ π ⟩ ((⇡ᴹ M N ⹁ γ₂ ∷⟨ π₂ ⟩ lower) {gt = gt}) = (M₁ ⹁ γ₁ ∷⟨ wk-trans π₁ π ⟩ ((⇡ᴹ M N ⹁ γ₂ ∷⟨ π₂ ⟩ lower)) {gt = gt} ) {gt = ↕}
(M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ □) ⦂⦂⟨ π ⟩ ((⇡ᴸ LHS RHS ⹁ γ₂ ∷⟨ π₂ ⟩ lower) {gt = gt}) = (M₁ ⹁ γ₁ ∷⟨ wk-trans π₁ π ⟩ ((⇡ᴸ LHS RHS ⹁ γ₂ ∷⟨ π₂ ⟩ lower)) {gt = gt} ) {gt = ↕}
(M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ □) ⦂⦂⟨ π ⟩ ((⇡ᴿ LHS RHS ⹁ γ₂ ∷⟨ π₂ ⟩ lower) {gt = gt}) = (M₁ ⹁ γ₁ ∷⟨ wk-trans π₁ π ⟩ ((⇡ᴿ LHS RHS ⹁ γ₂ ∷⟨ π₂ ⟩ lower)) {gt = gt} ) {gt = ↕}
((M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ ((x ⹁ γ ∷⟨ π₃ ⟩ upper) {gt = gt})) {gt = ↕}) ⦂⦂⟨ π ⟩ ((M₂ ⹁ γ₂ ∷⟨ π₂ ⟩ lower) {gt = gt2}) = (M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ (((x ⹁ γ ∷⟨ π₃ ⟩ upper) {gt = gt} ) ⦂⦂⟨ π ⟩ ((M₂ ⹁ γ₂ ∷⟨ π₂ ⟩ lower) {gt = gt2}))) {gt = ↕}
-}
-}

{-
botCtx : vState ε T◾ → Ctx
botCtx (∘_ {Θ = Θ} x) = Θ
botCtx (∙_ {Θ = Θ} x) = Θ

topCtx : vState ε T◾ → Ctx
topCtx (∘_ {Ψ = Ψ} x) = Ψ
topCtx (∙_ {Ψ = Ψ} x) = Ψ

_::⟨_⟩_ : (upper : vState ε T◾) → Wk (botCtx upper) Ψ → vStack ε Ψ Θ true T◾' → vState ε T◾'
(∘ upper) ::⟨ π ⟩ lower = ∘ (upper ⦂⦂⟨ π ⟩ lower)
(∙ upper) ::⟨ π ⟩ lower = ∙ (upper ⦂⦂⟨ π ⟩ lower)

-}

_::_ : (upper : vState T◾) → vStack true T◾' → vState T◾'
(∘ upper) :: lower = ∘ (upper ⦂⦂ lower)
(∙ upper) :: lower = ∙ (upper ⦂⦂ lower)

---  _::ᴸ_ : lState X → vStack true T◾' → lState X
---  ⟨ i ∥ γ ∥ tail ﹐ gt ⟩ ::ᴸ lower = ⟨ i ∥ γ ∥ (tail ⦂⦂ lower) ﹐ ↕ ⟩
---  
---  ⟨_⟩ⱽᴸ∷_ : {from : vState T◾} → {to : lState X} → (F>T : from →ⱽᴸ to) → (tail : vStack true T◾') → (from :: tail) →ⱽᴸ (to ::ᴸ tail)
---  ⟨ start-lookup {i = i} {γ = γ} {tail = tail₁} {gt = gt}⟩ⱽᴸ∷ tail₂ = start-lookup {i = i} {γ = γ} {tail = tail₁ ⦂⦂ tail₂} {gt = ↕}
---  
---  ⟨_⟩ᴸⱽ∷_ : {from : lState X} → {to : vState T◾} → (F>T : from →ᴸⱽ to) → (tail : vStack true T◾') → (from ::ᴸ tail) →ᴸⱽ (to :: tail)
---  ⟨ finish-lookup {M = M} {γ = γ} {γ' = γ'} {tail = tail₁} {gt = gt} ⟩ᴸⱽ∷ tail₂ = finish-lookup {M = M} {γ = γ} {γ' = γ'} {tail = tail₁ ⦂⦂ tail₂} {gt = ↕}
---  
---  ⟨_⟩ᴸᴸ∷_ : {from : lState X} → {to : lState X} → (F>T : from →ᴸᴸ to) → (tail : vStack true T◾') → (from ::ᴸ tail) →ᴸᴸ (to ::ᴸ tail)
---  ⟨ val-t-step {i = i} {E = E} {M = M} {E' = E'} {tail = tail₁} {gt = gt} ⟩ᴸᴸ∷ tail₂ = val-t-step {i = i} {E = E} {M = M} {E' = E'} {tail = tail₁ ⦂⦂ tail₂} {gt = ↕}
---  ⟨ comp-t-step {i = i} {E = E} {W = W} {k = k} {E' = E'} {tail = tail₁} {gt = gt} ⟩ᴸᴸ∷ tail₂ = comp-t-step {i = i} {E = E} {W = W} {k = k} {E' = E'} {tail = tail₁ ⦂⦂ tail₂} {gt = ↕}
---  
---  ⟪_⟫ᴸᴸ∷_ : {from : lState X} → {to : lState X} → (F>>T : from →ᴸᴸ* to) → (tail : vStack true T◾') → (from ::ᴸ tail) →ᴸᴸ* (to ::ᴸ tail)
---  ⟪ F ▣ ⟫ᴸᴸ∷ tail =  (F ::ᴸ tail) ▣
---  ⟪ _ →ᴸᴸ⟨ F>S ⟩ S>>T ⟫ᴸᴸ∷ tail =  _ →ᴸᴸ⟨ ⟨ F>S ⟩ᴸᴸ∷ tail ⟩ (⟪ S>>T ⟫ᴸᴸ∷ tail)

{-
twk : (from : vState ε T◾) → (to : vState ε T◾) → (F>T : from →ᵛᵛ to) → (π : Wk (botCtx from) Ψ) → Wk (botCtx to) Ψ
twk .(∘ ⇡ var _ ⹁ _ ∷⟨ _ ⟩ _) .(∙ ⭭ wk-valTerm _ _ ⹁ _ ∷⟨ _ ⟩ _) (∘var x) π = π
twk _ _ ∘lam π = π
twk .(∘ ⇡ pair _ _ ⹁ _ ∷⟨ _ ⟩ _) .(∘ ⇡ _ ⹁ _ ∷⟨ wk-id ⟩ ⇡ᴸ _ _ ⹁ _ ∷⟨ _ ⟩ _) ∘pair π = π
twk .(∘ ⇡ pm _ _ ⹁ _ ∷⟨ _ ⟩ _) .(∘ ⇡ _ ⹁ _ ∷⟨ wk-id ⟩ ⇡ᴹ _ _ ⹁ _ ∷⟨ _ ⟩ _) ∘pm π = π
twk .(∘ ⇡ unit ⹁ _ ∷⟨ _ ⟩ _) .(∙ ⭭ val-unit ⹁ _ ∷⟨ _ ⟩ _) ∘unit π = π
twk .(∙ ⭭ _ ⹁ _ ∷⟨ _ ⟩ ⇡ᴸ _ _ ⹁ _ ∷⟨ _ ⟩ _) .(∘ ⇡ wk-val _ _ ⹁ _ ∷⟨ wk-id ⟩ ⇡ᴿ _ (wk-val _ _) ⹁ _ ∷⟨ _ ⟩ _) ∙M∷l π = π
twk .(∙ ⭭ _ ⹁ _ ∷⟨ _ ⟩ ⇡ᴿ _ _ ⹁ _ ∷⟨ _ ⟩ _) .(∙ ⭭ val-pair (wk-valTerm _ _) _ ⹁ _ ∷⟨ _ ⟩ _) ∙M∷r π = π
twk .(∙ ⭭ val-pair _ _ ⹁ _ ∷⟨ _ ⟩ ⇡ᴹ _ _ ⹁ _ ∷⟨ _ ⟩ _) .(∘ ⇡ wk-val (wk-cong (wk-cong _)) _ ⹁ s-val (wk-valTerm (wk-wk wk-id) _) (s-val _ _) ∷⟨ wk-wk (wk-wk (_)) ⟩ _) ∙pair∷pm π = π
twk _ _ test π = π
-}

{-

⟨_⟩∷⟨_⟩_ : {from : vState ε T◾} → {to : vState ε T◾} → (F>T : from →ᵛᵛ to) → (π : Wk (botCtx from) Ψ) → (tail : vStack ε Ψ Θ true T◾') → (from ::⟨ π ⟩ tail) →ᵛᵛ (to ::⟨ twk from to F>T π ⟩ tail)
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ var _ ⹁ _ ∷⟨ _ ⟩ □) {gt = ↓}} (∘var x) π (x₁ ⹁ γ ∷⟨ π₁ ⟩ tail) = ∘var x
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ var _ ⹁ _ ∷⟨ _ ⟩ x₁ ⹁ γ ∷⟨ π₁ ⟩ tail₁) {gt = ↕}} (∘var x) π (x₂ ⹁ γ₁ ∷⟨ π₂ ⟩ tail) = ∘var x

⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ lam _ ⹁ _ ∷⟨ _ ⟩ □) {gt = ↓}} ∘lam π (x ⹁ γ ∷⟨ π₁ ⟩ tail) = ∘lam
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ lam _ ⹁ _ ∷⟨ _ ⟩ x ⹁ γ ∷⟨ π₁ ⟩ tail₁) {gt = ↕}} ∘lam π (x₁ ⹁ γ₁ ∷⟨ π₂ ⟩ tail) = ∘lam

⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pair _ _ ⹁ _ ∷⟨ _ ⟩ □) {gt = ↓}} ∘pair π (x ⹁ γ ∷⟨ π₁ ⟩ tail) = ∘pair
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pair _ _ ⹁ _ ∷⟨ _ ⟩ x ⹁ γ ∷⟨ π₁ ⟩ tail₁) {gt = ↕}} ∘pair π (x₁ ⹁ γ₁ ∷⟨ π₂ ⟩ tail) = ∘pair

⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pm _ _ ⹁ _ ∷⟨ _ ⟩ □) {gt = ↓}} ∘pm π (x ⹁ γ ∷⟨ π₁ ⟩ tail) = ∘pm
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pm _ _ ⹁ _ ∷⟨ _ ⟩ x ⹁ γ ∷⟨ π₁ ⟩ tail₁) {gt = ↕}} ∘pm π (x₁ ⹁ γ₁ ∷⟨ π₂ ⟩ tail) = ∘pm

⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ unit ⹁ _ ∷⟨ _ ⟩ □) {gt = ↓}} ∘unit π (x ⹁ γ ∷⟨ π₁ ⟩ tail) = ∘unit
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ unit ⹁ _ ∷⟨ _ ⟩ x ⹁ γ ∷⟨ π₁ ⟩ tail₁) {gt = ↕}} ∘unit π (x₁ ⹁ γ₁ ∷⟨ π₂ ⟩ tail) = ∘unit

⟨_⟩∷⟨_⟩_ {from = ∙ (⭭ _ ⹁ _ ∷⟨ _ ⟩ ((⇡ᴸ LHS RHS ⹁ γ₁ ∷⟨ π₂ ⟩ □) {gt = ↓})) {gt = ↕}} ∙M∷l π ((x ⹁ γ ∷⟨ π₁ ⟩ tail) {gt = gt}) = {!∙M∷l!}
⟨_⟩∷⟨_⟩_ {from = ∙ (⭭ _ ⹁ _ ∷⟨ _ ⟩ ⇡ᴸ _ _ ⹁ _ ∷⟨ _ ⟩ x₁ ⹁ γ₁ ∷⟨ π₂ ⟩ tail₁) {gt = ↕}} ∙M∷l π (x ⹁ γ ∷⟨ π₁ ⟩ tail) = ∙M∷l

⟨_⟩∷⟨_⟩_ {from = ∙ (⭭ _ ⹁ _ ∷⟨ _ ⟩ ((⇡ᴸ LHS RHS ⹁ γ₁ ∷⟨ π₂ ⟩ □) {gt = ↓})) {gt = ↕}} test π ((x ⹁ γ ∷⟨ π₁ ⟩ tail) {gt = gt}) = test
⟨_⟩∷⟨_⟩_ {from = ∙ (⭭ _ ⹁ _ ∷⟨ _ ⟩ ⇡ᴸ _ _ ⹁ _ ∷⟨ _ ⟩ x₁ ⹁ γ₁ ∷⟨ π₂ ⟩ tail₁) {gt = ↕}} test π (x ⹁ γ ∷⟨ π₁ ⟩ tail) = test -- ∙M∷l

⟨_⟩∷⟨_⟩_ {from = .(∙ ⭭ _ ⹁ _ ∷⟨ _ ⟩ ⇡ᴿ _ _ ⹁ _ ∷⟨ _ ⟩ _)} ∙M∷r π tail = {!!}

⟨_⟩∷⟨_⟩_ {from = ∙ (⭭ val-pair _ _ ⹁ _ ∷⟨ _ ⟩ ((⇡ᴹ _ _ ⹁ _ ∷⟨ _ ⟩ □) {gt = ↓})) {gt = ↕}} ∙pair∷pm π tail = {!∙pair∷pm!}
⟨_⟩∷⟨_⟩_ {from = ∙ ⭭ val-pair _ _ ⹁ _ ∷⟨ _ ⟩ ⇡ᴹ _ _ ⹁ _ ∷⟨ _ ⟩ x ⹁ γ ∷⟨ π₁ ⟩ tail₁} ∙pair∷pm π tail = {!!} --∙pair∷pm

{-
⟨_⟩∷⟨_⟩_ : {from : vState ε T◾} → {to : vState ε T◾} → (F>T : from →ᵛᵛ to) → (π : Wk (botCtx from) Ψ) → (tail : vStack ε Ψ Θ true T◾') → (from ::⟨ π ⟩ tail) →ᵛᵛ (to ::⟨ twk from to F>T π ⟩ tail)
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ var _ ⹁ _ ∷⟨ _ ⟩ □) {gt = ↓}} (∘var x) π (x₁ ⹁ γ ∷⟨ π₁ ⟩ tail) = ∘var x
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ var _ ⹁ _ ∷⟨ _ ⟩ x₁ ⹁ γ ∷⟨ π₁ ⟩ tail₁) {gt = ↕}} (∘var x) π (x₂ ⹁ γ₁ ∷⟨ π₂ ⟩ tail) = ∘var x

⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ lam _ ⹁ _ ∷⟨ _ ⟩ □) {gt = ↓}} ∘lam π (x ⹁ γ ∷⟨ π₁ ⟩ tail) = ∘lam
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ lam _ ⹁ _ ∷⟨ _ ⟩ x ⹁ γ ∷⟨ π₁ ⟩ tail₁) {gt = ↕}} ∘lam π (x₁ ⹁ γ₁ ∷⟨ π₂ ⟩ tail) = ∘lam

⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pair _ _ ⹁ _ ∷⟨ _ ⟩ □) {gt = ↓}} ∘pair π (x ⹁ γ ∷⟨ π₁ ⟩ tail) = ∘pair
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pair _ _ ⹁ _ ∷⟨ _ ⟩ x ⹁ γ ∷⟨ π₁ ⟩ tail₁) {gt = ↕}} ∘pair π (x₁ ⹁ γ₁ ∷⟨ π₂ ⟩ tail) = ∘pair

⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pm _ _ ⹁ _ ∷⟨ _ ⟩ □) {gt = ↓}} ∘pm π (x ⹁ γ ∷⟨ π₁ ⟩ tail) = ∘pm
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pm _ _ ⹁ _ ∷⟨ _ ⟩ x ⹁ γ ∷⟨ π₁ ⟩ tail₁) {gt = ↕}} ∘pm π (x₁ ⹁ γ₁ ∷⟨ π₂ ⟩ tail) = ∘pm

⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ unit ⹁ _ ∷⟨ _ ⟩ □) {gt = ↓}} ∘unit π (x ⹁ γ ∷⟨ π₁ ⟩ tail) = ∘unit
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ unit ⹁ _ ∷⟨ _ ⟩ x ⹁ γ ∷⟨ π₁ ⟩ tail₁) {gt = ↕}} ∘unit π (x₁ ⹁ γ₁ ∷⟨ π₂ ⟩ tail) = ∘unit

⟨_⟩∷⟨_⟩_ {from = ∙ (⭭ _ ⹁ _ ∷⟨ _ ⟩ ((⇡ᴸ LHS RHS ⹁ γ₁ ∷⟨ π₂ ⟩ □) {gt = ↓})) {gt = ↕}} ∙M∷l π ((x ⹁ γ ∷⟨ π₁ ⟩ tail) {gt = gt}) = {!!}
⟨_⟩∷⟨_⟩_ {from = ∙ (⭭ _ ⹁ _ ∷⟨ _ ⟩ ⇡ᴸ _ _ ⹁ _ ∷⟨ _ ⟩ x₁ ⹁ γ₁ ∷⟨ π₂ ⟩ tail₁) {gt = ↕}} ∙M∷l π (x ⹁ γ ∷⟨ π₁ ⟩ tail) = ∙M∷l

⟨_⟩∷⟨_⟩_ {from = .(∙ ⭭ _ ⹁ _ ∷⟨ _ ⟩ ⇡ᴿ _ _ ⹁ _ ∷⟨ _ ⟩ _)} ∙M∷r π tail = {!!}

⟨_⟩∷⟨_⟩_ {from = ∙ (⭭ val-pair _ _ ⹁ _ ∷⟨ _ ⟩ ((⇡ᴹ _ _ ⹁ _ ∷⟨ _ ⟩ □) {gt = ↓})) {gt = ↕}} ∙pair∷pm π tail = {!∙pair∷pm!}
⟨_⟩∷⟨_⟩_ {from = ∙ ⭭ val-pair _ _ ⹁ _ ∷⟨ _ ⟩ ⇡ᴹ _ _ ⹁ _ ∷⟨ _ ⟩ x ⹁ γ ∷⟨ π₁ ⟩ tail₁} ∙pair∷pm π tail = ∙pair∷pm
-}

{-
⟨_⟩∷⟨_⟩_ : {from : vState ε T◾} → {to : vState ε T◾} → (F>T : from →ᵛᵛ to) → (π : Wk (botCtx from) Ψ) → (tail : vStack ε Ψ Θ true T◾') → (from ::⟨ π ⟩ tail) →ᵛᵛ (to ::⟨ twk from to F>T π ⟩ tail)

⟨_⟩∷⟨_⟩_ {from = ∘ ⇡ var i ⹁ γ ∷⟨ π₁ ⟩ □} (∘var T>>U) π (⭭ x ⹁ γ₂ ∷⟨ π₂ ⟩ tail) = (∘var T>>U)
⟨_⟩∷⟨_⟩_ {from = ∘ ⇡ var i ⹁ γ ∷⟨ π₁ ⟩ □} (∘var T>>U) π (⇡ M ⹁ γ₂ ∷⟨ π₂ ⟩ tail) = (∘var T>>U)
⟨_⟩∷⟨_⟩_ {from = ∘ ⇡ var i ⹁ γ ∷⟨ π₁ ⟩ □} (∘var T>>U) π (⇡ᴹ M N ⹁ γ₂ ∷⟨ π₂ ⟩ tail) = (∘var T>>U)
⟨_⟩∷⟨_⟩_ {from = ∘ ⇡ var i ⹁ γ ∷⟨ π₁ ⟩ □} (∘var T>>U) π (⇡ᴸ LHS RHS ⹁ γ₂ ∷⟨ π₂ ⟩ tail) = (∘var T>>U)
⟨_⟩∷⟨_⟩_ {from = ∘ ⇡ var i ⹁ γ ∷⟨ π₁ ⟩ □} (∘var T>>U) π (⇡ᴿ LHS RHS ⹁ γ₂ ∷⟨ π₂ ⟩ tail) = (∘var T>>U)
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ var i ⹁ γ ∷⟨ π₁ ⟩ ((x ⹁ γ₁ ∷⟨ π₃ ⟩ tail₁) {gt = gt})) {gt = ↕}} (∘var T>>U) π (M₂ ⹁ γ₂ ∷⟨ π₂ ⟩ tail) = (∘var T>>U)

⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ lam M ⹁ γ ∷⟨ π₁ ⟩ □) {gt = ↓}} ∘lam π (⭭ x ⹁ γ₁ ∷⟨ π₂ ⟩ tail) = ∘lam
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ lam M ⹁ γ ∷⟨ π₁ ⟩ □) {gt = ↓}} ∘lam π (⇡ M₁ ⹁ γ₁ ∷⟨ π₂ ⟩ tail) = ∘lam
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ lam M ⹁ γ ∷⟨ π₁ ⟩ □) {gt = ↓}} ∘lam π (⇡ᴹ M₁ N ⹁ γ₁ ∷⟨ π₂ ⟩ tail) = ∘lam
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ lam M ⹁ γ ∷⟨ π₁ ⟩ □) {gt = ↓}} ∘lam π (⇡ᴸ LHS RHS ⹁ γ₁ ∷⟨ π₂ ⟩ tail) = ∘lam
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ lam M ⹁ γ ∷⟨ π₁ ⟩ □) {gt = ↓}} ∘lam π (⇡ᴿ LHS RHS ⹁ γ₁ ∷⟨ π₂ ⟩ tail) = ∘lam
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ lam M ⹁ γ ∷⟨ π₁ ⟩ (x ⹁ γ₁ ∷⟨ π₂ ⟩ upper) {gt = gt}) {gt = ↕}} ∘lam π (x₁ ⹁ γ₂ ∷⟨ π₃ ⟩ tail) = ∘lam

⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pair LHS RHS ⹁ γ ∷⟨ π₂ ⟩ □) {gt = ↓}} ∘pair π (⭭ x ⹁ γ₁ ∷⟨ π₁ ⟩ tail) = ∘pair
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pair LHS RHS ⹁ γ ∷⟨ π₂ ⟩ □) {gt = ↓}} ∘pair π (⇡ M ⹁ γ₁ ∷⟨ π₁ ⟩ tail) = ∘pair
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pair LHS RHS ⹁ γ ∷⟨ π₂ ⟩ □) {gt = ↓}} ∘pair π (⇡ᴹ M N ⹁ γ₁ ∷⟨ π₁ ⟩ tail) = ∘pair
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pair LHS RHS ⹁ γ ∷⟨ π₂ ⟩ □) {gt = ↓}} ∘pair π (⇡ᴸ LHS₁ RHS₁ ⹁ γ₁ ∷⟨ π₁ ⟩ tail) = ∘pair
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pair LHS RHS ⹁ γ ∷⟨ π₂ ⟩ □) {gt = ↓}} ∘pair π (⇡ᴿ LHS₁ RHS₁ ⹁ γ₁ ∷⟨ π₁ ⟩ tail) = ∘pair
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pair LHS RHS ⹁ γ ∷⟨ π₂ ⟩ ((x ⹁ γ₂ ∷⟨ π₃ ⟩ tail₁) {gt = gt})) {gt = ↕}} ∘pair π (M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ tail) = ∘pair

--⟨ ∘pm ⟩∷⟨ π ⟩ tail = {!!}
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pm M N ⹁ γ ∷⟨ π₁ ⟩ □) {gt = ↓}} ∘pm π (⭭ x ⹁ γₜ ∷⟨ πₜ ⟩ tail) = ∘pm
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pm M N ⹁ γ ∷⟨ π₁ ⟩ □) {gt = ↓}} ∘pm π (⇡ M₁ ⹁ γₜ ∷⟨ πₜ ⟩ tail) = ∘pm
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pm M N ⹁ γ ∷⟨ π₁ ⟩ □) {gt = ↓}} ∘pm π (⇡ᴹ M₁ N₁ ⹁ γₜ ∷⟨ πₜ ⟩ tail) = ∘pm
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pm M N ⹁ γ ∷⟨ π₁ ⟩ □) {gt = ↓}} ∘pm π (⇡ᴸ LHS RHS ⹁ γₜ ∷⟨ πₜ ⟩ tail) = ∘pm
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pm M N ⹁ γ ∷⟨ π₁ ⟩ □) {gt = ↓}} ∘pm π (⇡ᴿ LHS RHS ⹁ γₜ ∷⟨ πₜ ⟩ tail) = ∘pm
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ pm M N ⹁ γ ∷⟨ π₁ ⟩ ((x ⹁ γ₁ ∷⟨ π₂ ⟩ tail₁) {gt = gt})) {gt = ↕}} ∘pm π (Mₜ ⹁ γₜ ∷⟨ πₜ ⟩ tail) = ∘pm

--⟨ ∘unit ⟩∷⟨ π ⟩ tail = {!!}
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ unit ⹁ γ ∷⟨ π₁ ⟩ □) {gt = ↓}} ∘unit π (⭭ x ⹁ γₜ ∷⟨ πₜ ⟩ tail) = ∘unit
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ unit ⹁ γ ∷⟨ π₁ ⟩ □) {gt = ↓}} ∘unit π (⇡ M ⹁ γₜ ∷⟨ πₜ ⟩ tail) = ∘unit
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ unit ⹁ γ ∷⟨ π₁ ⟩ □) {gt = ↓}} ∘unit π (⇡ᴹ M N ⹁ γₜ ∷⟨ πₜ ⟩ tail) = ∘unit
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ unit ⹁ γ ∷⟨ π₁ ⟩ □) {gt = ↓}} ∘unit π (⇡ᴸ LHS RHS ⹁ γₜ ∷⟨ πₜ ⟩ tail) = ∘unit
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ unit ⹁ γ ∷⟨ π₁ ⟩ □) {gt = ↓}} ∘unit π (⇡ᴿ LHS RHS ⹁ γₜ ∷⟨ πₜ ⟩ tail) = ∘unit
⟨_⟩∷⟨_⟩_ {from = ∘ (⇡ unit ⹁ γ ∷⟨ π₁ ⟩ ((x ⹁ γ₁ ∷⟨ π₂ ⟩ tail₁) {gt = gt})) {gt = ↕}} ∘unit π (Mₜ ⹁ γₜ ∷⟨ πₜ ⟩ tail) = ∘unit

--⟨ ∙M∷l ⟩∷⟨ π ⟩ tail = {!!}
⟨_⟩∷⟨_⟩_ {from = ∙ (⭭ M ⹁ γ ∷⟨ π' ⟩ (⇡ᴸ LHS RHS ⹁ γ' ∷⟨ π₁ ⟩ □) {gt = ↓}) {gt = .↕}} ∙M∷l π (⭭ x ⹁ γₜ ∷⟨ πₜ ⟩ tail) = {!∙M∷l!}
⟨_⟩∷⟨_⟩_ {from = ∙ (⭭ M ⹁ γ ∷⟨ π' ⟩ (⇡ᴸ LHS RHS ⹁ γ' ∷⟨ π₁ ⟩ □) {gt = ↓}) {gt = .↕}} ∙M∷l π (⇡ M₁ ⹁ γₜ ∷⟨ πₜ ⟩ tail) = {!!}
⟨_⟩∷⟨_⟩_ {from = ∙ (⭭ M ⹁ γ ∷⟨ π' ⟩ (⇡ᴸ LHS RHS ⹁ γ' ∷⟨ π₁ ⟩ □) {gt = ↓}) {gt = .↕}} ∙M∷l π (⇡ᴹ M₁ N ⹁ γₜ ∷⟨ πₜ ⟩ tail) = {!!}
⟨_⟩∷⟨_⟩_ {from = ∙ (⭭ M ⹁ γ ∷⟨ π' ⟩ (⇡ᴸ LHS RHS ⹁ γ' ∷⟨ π₁ ⟩ □) {gt = ↓}) {gt = .↕}} ∙M∷l π (⇡ᴸ LHS₁ RHS₁ ⹁ γₜ ∷⟨ πₜ ⟩ tail) = {!!}
⟨_⟩∷⟨_⟩_ {from = ∙ (⭭ M ⹁ γ ∷⟨ π' ⟩ (⇡ᴸ LHS RHS ⹁ γ' ∷⟨ π₁ ⟩ □) {gt = ↓}) {gt = .↕}} ∙M∷l π (⇡ᴿ LHS₁ RHS₁ ⹁ γₜ ∷⟨ πₜ ⟩ tail) = {!!}
⟨_⟩∷⟨_⟩_ {from = ∙ (⭭ M ⹁ γ ∷⟨ π' ⟩ ((⇡ᴸ LHS RHS ⹁ γ' ∷⟨ π₁ ⟩ ((x ⹁ γ₁ ∷⟨ π₂ ⟩ tail₁) {gt = gt})) {gt = ↕})) {gt = .↕}} ∙M∷l π (Mₜ ⹁ γₜ ∷⟨ πₜ ⟩ tail) = {!!}

--⟨ ∙M∷r ⟩∷⟨ π ⟩ tail = {!!}
⟨_⟩∷⟨_⟩_ {from = ∙ (⭭ M ⹁ γ ∷⟨ π' ⟩ ((⇡ᴿ LHS RHS ⹁ γ' ∷⟨ π₁ ⟩ □) {gt = ↓})) {gt = .↕}} ∙M∷r π (Mₜ ⹁ γₜ ∷⟨ πₜ ⟩ tail) = {!!}
⟨_⟩∷⟨_⟩_ {from = ∙ (⭭ M ⹁ γ ∷⟨ π' ⟩ ((⇡ᴿ LHS RHS ⹁ γ' ∷⟨ π₁ ⟩ ((x ⹁ γ₁ ∷⟨ π₂ ⟩ tail₁) {gt = gt})) {gt = ↕})) {gt = .↕}} ∙M∷r π (Mₜ ⹁ γₜ ∷⟨ πₜ ⟩ tail) = {!!}

--⟨ ∙pair∷pm ⟩∷⟨ π ⟩ tail = {!!}
⟨_⟩∷⟨_⟩_ {from = ∙ (⭭ val-pair LHS RHS ⹁ γ ∷⟨ π' ⟩ (⇡ᴹ M N ⹁ γ' ∷⟨ π₁ ⟩ □) {gt = gt}) {gt = ↕}} ∙pair∷pm π (Mₜ ⹁ γₜ ∷⟨ πₜ ⟩ tail) = {!!}
⟨_⟩∷⟨_⟩_ {from = ∙ (⭭ val-pair LHS RHS ⹁ γ ∷⟨ π' ⟩ (⇡ᴹ M N ⹁ γ' ∷⟨ π₁ ⟩ x ⹁ γ₁ ∷⟨ π₂ ⟩ tail₁) {gt = gt}) {gt = ↕}} ∙pair∷pm π (Mₜ ⹁ γₜ ∷⟨ πₜ ⟩ tail) = {!!}
-}
-}


⟨_⟩∷_ : {from : vState T◾} → {to : vState T◾} → (F>T : from →ᵛᵛ to) → (tail : vStack true T◾') → (from :: tail) →ᵛᵛ (to :: tail)
--⟨ ∘var-z T>>U ⟩∷ tail = ∘var-z T>>U
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


-- ⟦_⟧↥ : (S : vStack true T◾) → ⟦ T◾ ⟧
-- ⟦ ((⇡ M) ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ M ⟧ᵛ ⟦ γ ⟧ᴱ
-- ⟦ (⇡ᴹ M N ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ pm M N ⟧ᵛ ⟦ γ ⟧ᴱ
-- ⟦ (⇡ᴸ LHS RHS ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ pair LHS RHS ⟧ᵛ ⟦ γ ⟧ᴱ
-- ⟦ (⇡ᴿ LHS RHS ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ pair LHS RHS ⟧ᵛ ⟦ γ ⟧ᴱ
-- ⟦ ((⇡ M) ⹁ γ₁ ∷ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂}) {gt = gt₁} ⟧↥ = ⟦ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂} ⟧↥
-- ⟦ (⇡ᴹ M N ⹁ γ₁ ∷ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂}) {gt = gt₁} ⟧↥ = ⟦ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂} ⟧↥
-- ⟦ (⇡ᴸ LHS RHS ⹁ γ₁ ∷ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂}) {gt = gt₁} ⟧↥ = ⟦ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂} ⟧↥
-- ⟦ (⇡ᴿ LHS RHS ⹁ γ₁ ∷ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂}) {gt = gt₁} ⟧↥ = ⟦ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂} ⟧↥

⟦_⟧↥ : (S : vStack true T◾) → ⟦ T◾ ⟧
⟦ (⭭ x ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ valTerm-to-Val x ⟧ᵛ ⟦ γ ⟧ᴱ
⟦ (⇡ M ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ M ⟧ᵛ ⟦ γ ⟧ᴱ
⟦ (⇡ᴹ M N ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ pm M N ⟧ᵛ ⟦ γ ⟧ᴱ
⟦ (⇡ᴸ LHS RHS ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ pair LHS RHS ⟧ᵛ ⟦ γ ⟧ᴱ
⟦ (⇡ᴿ LHS RHS ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ pair (valTerm-to-Val LHS) RHS ⟧ᵛ ⟦ γ ⟧ᴱ
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

     -- ∙unit⹁_■ : (γ : Env Γ) → vHaltingState (∙ ((⇡ unit ⹁ γ ∷ □) {gt = ↓}))

     -- ∙pair[_⹁_]⹁_■ : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → (γ : Env ε Γ {WK = WK}) → vHaltingState (∙ ((⇡ pair LHS RHS ⹁ γ ∷ □) {gt = ↓}))

     -- ∙lam_⹁_■ : (M : (Γ ∙ X) ⊢ᶜ Y) → (γ : Env ε Γ {WK = WK}) → vHaltingState (∙ ((⇡ lam M ⹁ γ ∷ □) {gt = ↓}))

     ∙_⹁_■ : (M : valTerm Γ X) → (γ : Env Γ) → vHaltingState (∙ ((⭭ M ⹁ γ ∷ □) {gt = ↓}))


data correctSteps : vState T◾ → Set where

  steps : {S T : vState T◾} → S ↠ᵛᵛ T → vHaltingState T → ⟦ S ⟧◑ ≡ ⟦ T ⟧◑ → (π : Wk (topCtx T) (topCtx S)) → (⟦ π ⟧ʷ ⟦ topEnv T ⟧ᴱ ≡ ⟦ topEnv S ⟧ᴱ) → correctSteps S


wk-comm : {M : valTerm Γ X} → {π : Wk Δ Γ} → wk-val π (valTerm-to-Val M) ≡ valTerm-to-Val (wk-valTerm π M)
wk-comm {Γ = Γ} {Δ = Δ} {M = val-lam W} {π = π} = refl
wk-comm {Γ = Γ} {Δ = Δ} {M = val-pair LHS RHS} {π = π} = trans (cong (λ x → pair x _) wk-comm) ((cong (λ x → pair _ x) wk-comm))
wk-comm {Γ = Γ} {Δ = Δ} {M = val-unit} {π = π} = refl


lem1b : (i : Γ ∋ Z) → (π₁ : Wk Γ'' Γ') → (π₂ : Wk Γ' Γ) → wk-mem π₁ (wk-mem π₂ i) ≡ wk-mem (wk-trans π₁ π₂) i
lem1b Cx.h (wk-cong π₁) (wk-cong π₂) = refl
lem1b Cx.h (wk-cong π₁) (wk-wk π₂) = cong t (lem1b h π₁ π₂)
lem1b Cx.h (wk-wk π₁) (wk-cong π₂) = cong t (lem1b h π₁ (wk-cong π₂))
lem1b Cx.h (wk-wk π₁) (wk-wk π₂) = cong t (lem1b h π₁ (wk-wk π₂))
lem1b (Cx.t i) (wk-cong π₁) (wk-cong π₂) = cong t (lem1b i π₁ π₂)
lem1b (Cx.t i) (wk-wk (wk-cong π₁)) (wk-cong π₂) = cong t (cong t (lem1b i π₁ π₂))
lem1b (Cx.t i) (wk-wk (wk-wk π₁)) (wk-cong π₂) = cong t (cong t (lem1b (t i) π₁ (wk-cong π₂)))
lem1b (Cx.t i) (wk-cong π₁) (wk-wk π₂) = cong t (lem1b (t i) π₁ π₂)
lem1b (Cx.t i) (wk-wk (wk-cong π₁)) (wk-wk π₂) = cong t (lem1b (t i) (wk-cong π₁) (wk-wk π₂))
lem1b (Cx.t i) (wk-wk (wk-wk π₁)) (wk-wk π₂) = cong t (lem1b (t i) (wk-wk π₁) (wk-wk π₂))

lem1a : (M : Γ ⊢ᵛ Z) → (π₁ : Wk Γ'' Γ') → (π₂ : Wk Γ' Γ) → wk-val π₁ (wk-val π₂ M) ≡ wk-val (wk-trans π₁ π₂) M
lem1a-comp : (W : Γ ⊢ᶜ Z) → (π₁ : Wk Γ'' Γ') → (π₂ : Wk Γ' Γ) → wk-comp π₁ (wk-comp π₂ W) ≡ wk-comp (wk-trans π₁ π₂) W

lem1a (var i) π₁ π₂ = cong var (lem1b i π₁ π₂)
lem1a (lam x) π₁ π₂ = cong lam (lem1a-comp x (wk-cong π₁) (wk-cong π₂))
lem1a (pair LHS RHS) π₁ π₂ = pair (wk-val π₁ (wk-val π₂ LHS)) (wk-val π₁ (wk-val π₂ RHS))
      ≡⟨ cong (λ x → pair (wk-val π₁ (wk-val π₂ LHS)) x) (lem1a RHS π₁ π₂) ⟩
       pair (wk-val π₁ (wk-val π₂ LHS)) (wk-val (wk-trans π₁ π₂) RHS)
      ≡⟨ cong (λ x → pair x (wk-val (wk-trans π₁ π₂) RHS)) (lem1a LHS π₁ π₂) ⟩
       pair (wk-val (wk-trans π₁ π₂) LHS) (wk-val (wk-trans π₁ π₂) RHS) ∎
lem1a (pm M N) π₁ π₂ =
       pm (wk-val π₁ (wk-val π₂ M)) (wk-val (wk-cong (wk-cong π₁)) (wk-val (wk-cong (wk-cong π₂)) N))
      ≡⟨ cong (λ x → pm x (wk-val (wk-cong (wk-cong π₁)) (wk-val (wk-cong (wk-cong π₂)) N))) (lem1a M π₁ π₂) ⟩
       pm (wk-val (wk-trans π₁ π₂) M) (wk-val (wk-cong (wk-cong π₁)) (wk-val (wk-cong (wk-cong π₂)) N))
      ≡⟨ cong (λ x → pm (wk-val (wk-trans π₁ π₂) M) x) (lem1a N (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π₂)) ) ⟩
       pm (wk-val (wk-trans π₁ π₂) M) (wk-val (wk-cong (wk-cong (wk-trans π₁ π₂))) N) ∎
lem1a unit π₁ π₂ = refl

lem1a-comp (return M) π₁ π₂ = cong return (lem1a M π₁ π₂)
lem1a-comp (pm M N) π₁ π₂ =
        pm (wk-val π₁ (wk-val π₂ M)) (wk-comp (wk-cong (wk-cong π₁)) (wk-comp (wk-cong (wk-cong π₂)) N))
      ≡⟨ cong (λ x → pm x (wk-comp (wk-cong (wk-cong π₁)) (wk-comp (wk-cong (wk-cong π₂)) N))) (lem1a M π₁ π₂) ⟩
       pm (wk-val (wk-trans π₁ π₂) M) (wk-comp (wk-cong (wk-cong π₁)) (wk-comp (wk-cong (wk-cong π₂)) N))
      ≡⟨ cong (λ x → pm (wk-val (wk-trans π₁ π₂) M) x) (lem1a-comp N (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π₂)) ) ⟩
       pm (wk-val (wk-trans π₁ π₂) M) (wk-comp (wk-cong (wk-cong (wk-trans π₁ π₂))) N) ∎
lem1a-comp (push W W₁) π₁ π₂ =
       push (wk-comp π₁ (wk-comp π₂ W)) (wk-comp (wk-cong π₁) (wk-comp (wk-cong π₂) W₁))
      ≡⟨ cong (λ x → push x (wk-comp (wk-cong π₁) (wk-comp (wk-cong π₂) W₁))) (lem1a-comp W π₁ π₂) ⟩
       push (wk-comp (wk-trans π₁ π₂) W) (wk-comp (wk-cong π₁) (wk-comp (wk-cong π₂) W₁))
      ≡⟨ cong (λ x → push (wk-comp (wk-trans π₁ π₂) W) x) (lem1a-comp W₁ (wk-cong π₁) (wk-cong π₂)) ⟩
       push (wk-comp (wk-trans π₁ π₂) W) (wk-comp (wk-cong (wk-trans π₁ π₂)) W₁) ∎

lem1a-comp (app x x₁) π₁ π₂ =
       app (wk-val π₁ (wk-val π₂ x)) (wk-val π₁ (wk-val π₂ x₁))
      ≡⟨ cong (λ y → app y (wk-val π₁ (wk-val π₂ x₁))) (lem1a x π₁ π₂) ⟩
       app (wk-val (wk-trans π₁ π₂) x) (wk-val π₁ (wk-val π₂ x₁))
      ≡⟨ cong (λ y → app (wk-val (wk-trans π₁ π₂) x) y) (lem1a x₁ π₁ π₂) ⟩
       app (wk-val (wk-trans π₁ π₂) x) (wk-val (wk-trans π₁ π₂) x₁) ∎

lem1a-comp (var x) π₁ π₂ = cong var (lem1a x π₁ π₂)
lem1a-comp (sub W W₁) π₁ π₂ =
       sub (wk-comp (wk-cong π₁) (wk-comp (wk-cong π₂) W)) (wk-comp π₁ (wk-comp π₂ W₁))
      ≡⟨ cong (λ x → sub x (wk-comp π₁ (wk-comp π₂ W₁))) (lem1a-comp W (wk-cong π₁) (wk-cong π₂)) ⟩
       sub (wk-comp (wk-cong (wk-trans π₁ π₂)) W) (wk-comp π₁ (wk-comp π₂ W₁))
      ≡⟨ cong (λ x → sub (wk-comp (wk-cong (wk-trans π₁ π₂)) W) x) (lem1a-comp W₁ π₁ π₂) ⟩
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

eval (var i) γ π with lookup-t (wk-mem π i) γ
... | steps i>>T found-unit i≡T π₁ w≡γ = steps (_ →ᵛᵛ⟨ ∘var i>>T π₁ ⟩) (∙ val-unit ⹁ γ ■) refl wk-id refl
... | steps i>>T (found-pair {LHS = LHS} {RHS = RHS} {γ = γ₁}) i≡T π₁ w≡γ = --{!!}

           steps

           (_ →ᵛᵛ⟨ ∘var i>>T π₁ ⟩)

           (∙ val-pair (wk-valTerm π₁ LHS) (wk-valTerm π₁ RHS) ⹁ γ ■)

           (⟦ wk-mem π i ⟧ᵐ ⟦ γ ⟧ᴱ
           ≡⟨ i≡T ⟩
           (< ⟦ valTerm-to-Val LHS ⟧ᵛ , ⟦ valTerm-to-Val RHS ⟧ᵛ > ⟦ γ₁ ⟧ᴱ)
           ≡⟨ cong (λ x → < ⟦ valTerm-to-Val LHS ⟧ᵛ , ⟦ valTerm-to-Val RHS ⟧ᵛ > x) (sym w≡γ) ⟩
           (< ⟦ valTerm-to-Val LHS ⟧ᵛ , ⟦ valTerm-to-Val RHS ⟧ᵛ > (⟦ π₁ ⟧ʷ ⟦ γ ⟧ᴱ))
           ≡⟨ refl ⟩
           (⟦ wk-val π₁ (valTerm-to-Val LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ wk-val π₁ (valTerm-to-Val RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)
           ≡⟨ cong (λ x → (⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ wk-val π₁ (valTerm-to-Val RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)) (wk-comm {M = LHS} {π = π₁}) ⟩
           (⟦ valTerm-to-Val (wk-valTerm π₁ LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ wk-val π₁ (valTerm-to-Val RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)
           ≡⟨ cong (λ x → (⟦ valTerm-to-Val (wk-valTerm π₁ LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ)) (wk-comm {M = RHS} {π = π₁}) ⟩
           (⟦ valTerm-to-Val (wk-valTerm π₁ LHS) ⟧ᵛ ⟦ γ ⟧ᴱ , ⟦ valTerm-to-Val (wk-valTerm π₁ RHS) ⟧ᵛ ⟦ γ ⟧ᴱ)
           ≡⟨ refl ⟩
           (< ⟦ valTerm-to-Val (wk-valTerm π₁ LHS) ⟧ᵛ , ⟦ valTerm-to-Val (wk-valTerm π₁ RHS) ⟧ᵛ > ⟦ γ ⟧ᴱ) ∎)

           wk-id

           refl

... | steps i>>T (found-lam {W = W} {γ = γ₁}) i≡T π₁ w≡γ =

           steps

           (_ →ᵛᵛ⟨ ∘var i>>T π₁ ⟩)

           (∙ (wk-valTerm π₁ (val-lam W)) ⹁ γ ■)

           (⟦ wk-mem π i ⟧ᵐ ⟦ γ ⟧ᴱ
             ≡⟨ i≡T ⟩
           ((λ y → ⟦ W ⟧ᶜ (⟦ γ₁ ⟧ᴱ , y) ))
             ≡⟨ cong (λ x → (λ y → ⟦ W ⟧ᶜ (x , y) )) (sym w≡γ) ⟩
           (λ y → ⟦ W ⟧ᶜ (⟦ π₁ ⟧ʷ ⟦ γ ⟧ᴱ , y) )
             ≡⟨ refl ⟩
           (curry (< (λ r → proj₁ r) ； ⟦ π₁ ⟧ʷ , (λ r → proj₂ r) > ； ⟦ W ⟧ᶜ)) ⟦ γ ⟧ᴱ ∎)

           wk-id

           refl

eval (lam W) γ π = steps (∘ ⇡ (wk-val π (lam W)) ⹁ γ ∷ □ →ᵛᵛ⟨ ∘lam ⟩) (∙ val-lam (wk-comp (wk-cong π) W) ⹁ γ ■) refl wk-id refl
eval unit γ π = steps (_ →ᵛᵛ⟨ ∘unit ⟩) (∙ val-unit ⹁ γ ■) refl wk-id refl

-- Goal: (∘
--        ⇡ wk-val _π'_3203 (wk-val π RHS) ⹁ γ₁ ∷
--        ⇡ᴿ LT (wk-val _π'_3203 (wk-val π RHS)) ⹁ γ₁ ∷ □)
--       ↠ᵛᵛ _S_3208

eval (pair {A = X} {B = Y} LHS RHS) γ π with eval {X = X} LHS γ π
... | steps {T = ∙ (⭭_ {X = X} LT ⹁ γ₁ ∷ □) {gt = ↓}} L>T ∙LT L≡T πᴸ wk≡ᴸ with  eval {X = Y} RHS γ₁ (wk-trans πᴸ π)
...      | steps {T = ∙ (⭭_ {X = Y} RT ⹁ γ₂ ∷ □) {gt = ↓}} R>T ∙RT R≡T πᴿ wk≡ᴿ rewrite sym (lem1a RHS πᴸ π) = --{!!}

          steps

            (
             ∘ ⇡ (wk-val π (pair LHS RHS)) ⹁ γ ∷ □ →ᵛᵛ⟨ ∘pair ⟩  ⨾ -- (∘ ⇡ wk-val π LHS ⹁ γ ∷ ⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⹁ γ ∷ □)
             (⟪ L>T ⟫∷ (⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⹁ γ ∷ □)) ⨾
             (∙ ⭭ LT ⹁ γ₁ ∷ ⇡ᴸ (wk-val π LHS) (wk-val π RHS) ⹁ γ ∷ □) →ᵛᵛ⟨ ∙M∷l ⟩ ⨾ -- (∘ ⇡ wk-val _π'_3203 (wk-val π RHS) ⹁ γ₁ ∷ ⇡ᴿ LT (wk-val _π'_3203 (wk-val π RHS)) ⹁ γ₁ ∷ □)
             (⟪ R>T ⟫∷ (⇡ᴿ LT (wk-val πᴸ (wk-val π RHS)) ⹁ γ₁ ∷ □)) ⨾
             (∙ ⭭ RT ⹁ γ₂ ∷ ⇡ᴿ LT (wk-val πᴸ (wk-val π RHS)) ⹁ γ₁ ∷ □) →ᵛᵛ⟨ ∙M∷r ⟩
            )

            ∙ val-pair (wk-valTerm πᴿ LT) RT ⹁ γ₂ ■

            ( ⟦ wk-val π (pair LHS RHS) ⟧ᵛ ⟦ γ ⟧ᴱ
             ≡⟨ refl ⟩
               (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ))
             ≡⟨ cong (λ y → (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ y))) (sym wk≡ᴸ) ⟩
               (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ π ⟧ʷ (⟦ πᴸ ⟧ʷ ⟦ γ₁ ⟧ᴱ)))
             ≡⟨ cong (λ y → (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ y)) (lem2 πᴸ π ⟦ γ₁ ⟧ᴱ) ⟩
               (⟦ LHS ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
             ≡⟨ cong (λ y → (y , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))) L≡T ⟩
               (⟦ valTerm-to-Val LT ⟧ᵛ ⟦ γ₁ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
             ≡⟨ cong (λ y → (⟦ valTerm-to-Val LT ⟧ᵛ y , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))) (sym wk≡ᴿ) ⟩
               (⟦ valTerm-to-Val LT ⟧ᵛ (⟦ πᴿ ⟧ʷ ⟦ γ₂ ⟧ᴱ) , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
             ≡⟨ refl ⟩
               (⟦ wk-val πᴿ (valTerm-to-Val LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
             ≡⟨ cong (λ y → (⟦ y ⟧ᵛ ⟦ γ₂ ⟧ᴱ  , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))) (wk-comm {M = LT} {π = πᴿ}) ⟩
               (⟦ valTerm-to-Val (wk-valTerm πᴿ LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , ⟦ RHS ⟧ᵛ (⟦ wk-trans πᴸ π ⟧ʷ ⟦ γ₁ ⟧ᴱ))
             ≡⟨ cong (λ y → (⟦ valTerm-to-Val (wk-valTerm πᴿ LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , y)) R≡T ⟩
               (⟦ valTerm-to-Val (wk-valTerm πᴿ LT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ , ⟦ valTerm-to-Val RT ⟧ᵛ ⟦ γ₂ ⟧ᴱ)
             ≡⟨ refl ⟩
               ⟦ pair (valTerm-to-Val (wk-valTerm πᴿ LT)) (valTerm-to-Val RT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ
             ≡⟨ refl ⟩
               ⟦ valTerm-to-Val (val-pair (wk-valTerm πᴿ LT) RT) ⟧ᵛ ⟦ γ₂ ⟧ᴱ
             ≡⟨ refl ⟩
               ⟦ ∙ (⭭ val-pair (wk-valTerm πᴿ LT) RT ⹁ γ₂ ∷ □) {gt = ↓} ⟧◑ ∎ )

            (wk-trans πᴿ πᴸ)

            ( ⟦ wk-trans πᴿ πᴸ ⟧ʷ ⟦ γ₂ ⟧ᴱ
            ≡⟨ sym (lem2 πᴿ πᴸ ⟦ γ₂ ⟧ᴱ) ⟩
               ⟦ πᴸ ⟧ʷ (⟦ πᴿ ⟧ʷ ⟦ γ₂ ⟧ᴱ)
            ≡⟨ cong (λ y → ⟦ πᴸ ⟧ʷ y) wk≡ᴿ ⟩
               ⟦ πᴸ ⟧ʷ ⟦ γ₁ ⟧ᴱ
            ≡⟨ wk≡ᴸ ⟩
               ⟦ γ ⟧ᴱ ∎)

eval (pm M N) γ π with eval M γ π
... | steps M>T ∙ val-pair LHS RHS ⹁ γ₁ ■ M≡T π₁ wk≡₁ with eval N (s-val (wk-valTerm (wk-wk wk-id) RHS) (s-val LHS γ₁)) ((wk-cong (wk-cong (wk-trans π₁ π)))) | (lem1a N (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π)))
...    | steps {T = T} N>T ∙T N≡T π₂ wk≡₂ | eq with N>T
...      | N>T' rewrite sym eq =
       steps
         (
          (∘ ⇡ pm (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⹁ γ ∷ □) →ᵛᵛ⟨ ∘pm ⟩ ⨾ -- (∘ ⇡ wk-val π M ⹁ γ ∷ ⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⹁ γ ∷ □)
          (⟪ M>T ⟫∷ (⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⹁ γ ∷ □)) ⨾
          (∙ ⭭ val-pair LHS RHS ⹁ γ₁ ∷ ⇡ᴹ (wk-val π M) (wk-val (wk-cong (wk-cong π)) N) ⹁ γ ∷ □) →ᵛᵛ⟨ ∙pair∷pm ⟩ ⨾ -- (∘ ⇡ wk-val (wk-cong (wk-cong π₁)) (wk-val (wk-cong (wk-cong π)) N) ⹁ s-val (wk-valTerm (wk-wk wk-id) RHS) (s-val LHS γ₁) ∷ □)
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
           ⟦ wk-val (wk-cong (wk-cong π)) N ⟧ᵛ (assocl ( (⟦ γ ⟧ᴱ ,  (⟦ valTerm-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ , ⟦ valTerm-to-Val RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)  )))
           ≡⟨ refl ⟩
            ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ valTerm-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ valTerm-to-Val RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
           ≡⟨ cong  (λ y → ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ y , ⟦ valTerm-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ valTerm-to-Val RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)) (sym wk≡₁) ⟩
            ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ valTerm-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ valTerm-to-Val RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
           ≡⟨ refl ⟩
            ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ valTerm-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ (wk-val (wk-wk wk-id) (valTerm-to-Val RHS)) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ valTerm-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
           ≡⟨ cong (λ y → ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ valTerm-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ y ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ valTerm-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))) (wk-comm {M = RHS} {π = wk-wk wk-id}) ⟩
            ⟦ N ⟧ᵛ ((⟦ π ⟧ʷ (⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ) , ⟦ valTerm-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ valTerm-to-Val (wk-valTerm (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ valTerm-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
           ≡⟨ cong (λ y → ⟦ N ⟧ᵛ ((y , ⟦ valTerm-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ valTerm-to-Val (wk-valTerm (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ valTerm-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))  ) (lem2 π₁ π ⟦ γ₁ ⟧ᴱ) ⟩
           ⟦ N ⟧ᵛ ((⟦ wk-trans π₁ π ⟧ʷ ⟦ γ₁ ⟧ᴱ , ⟦ valTerm-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ valTerm-to-Val (wk-valTerm (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ valTerm-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
           ≡⟨ N≡T ⟩
           ⟦ T ⟧◑ ∎)

         (wk-trans π₂ (wk-wk (wk-wk π₁)))

         ( ⟦ wk-trans π₂ (wk-wk (wk-wk π₁)) ⟧ʷ ⟦ topEnv T ⟧ᴱ
          ≡⟨ sym (lem2 π₂ (wk-wk (wk-wk π₁)) ⟦ topEnv T ⟧ᴱ) ⟩
           ⟦ wk-wk (wk-wk π₁) ⟧ʷ (⟦ π₂ ⟧ʷ ⟦ topEnv T ⟧ᴱ)
          ≡⟨ cong (λ y → ⟦ wk-wk (wk-wk π₁) ⟧ʷ y) wk≡₂ ⟩
           ⟦ wk-wk (wk-wk π₁) ⟧ʷ (((⟦ γ₁ ⟧ᴱ , ⟦ valTerm-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ valTerm-to-Val (wk-valTerm (wk-wk wk-id) RHS) ⟧ᵛ (⟦ γ₁ ⟧ᴱ , ⟦ valTerm-to-Val LHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ)))
          ≡⟨ refl ⟩
           ⟦ π₁ ⟧ʷ ⟦ γ₁ ⟧ᴱ
          ≡⟨ wk≡₁ ⟩
           ⟦ γ ⟧ᴱ ∎)

-- eval : (M : Γ ⊢ᵛ X) → {WK : Wk Γ ε} → (γ : Env ε Γ {WK = WK}) → correctSteps {T◾ = X} (∘ ((⇡ M ⹁ γ ∷ □) {gt = ↓}))
-- 
-- eval (var i) γ with lookup-s i γ
-- ... | steps i>>T found-unit i≡T = steps (_ →ᵛᵛ⟨ ∘var i>>T ⟩) ∙unit⹁ _ ■ i≡T
-- ... | steps i>>T found-pair i≡T = steps (_ →ᵛᵛ⟨ ∘var i>>T ⟩) ∙pair[ _ ⹁ _ ]⹁ _ ■ i≡T
-- ... | steps i>>T found-lam i≡T = steps (_ →ᵛᵛ⟨ ∘var i>>T ⟩) ∙lam _ ⹁ _ ■ i≡T
-- ... | steps i>>T found-pm i≡T = {!!}
-- --with lookup (t i) γ
-- --... | steps i>>T HT i≡t = {!!}
-- 
-- eval = {!!}

{-

-- with lookup i γ
-- ... | steps i>>T HT i≡t = {!!}

-- ... | steps i>>T found-z i≡t =  steps (∘ ⇡ var i ⹁ γ ∷ □ →ᵛᵛ⟨ ∘var-z i>>T ⟩) {!!} {!!}
-- ... | steps i>>T found-val i≡t = steps (∘ ⇡ var i ⹁ γ ∷ □ →ᵛᵛ⟨ ∘var i>>T ⟩) {!!} {!!}
eval (lam M) γ = steps (∘ ⇡ lam M ⹁ γ ∷ □ →ᵛᵛ⟨ ∘lam ⟩) (∙lam M ⹁ γ ■) refl
eval unit γ = steps (∘ ⇡ unit ⹁ γ ∷ □ →ᵛᵛ⟨ ∘unit ⟩) (∙unit⹁ γ ■) refl

eval {X = X `× Y} (pair LHS RHS) {WK = WK} γ with eval {X = X} LHS {WK = WK} γ | eval RHS γ
... | steps {T = ∙ ((⇡ M₁ ⹁ γ₁ ∷ □) {gt = ↓})} L>T _ L≡M | steps {T = ∙ ((⇡ M₂ ⹁ γ₂ ∷ □) {gt = ↓})} R>T _ R≡M = -- {!!}

  steps (
         ∘ ⇡ pair LHS RHS ⹁ γ ∷ □ →ᵛᵛ⟨ ∘pair ⟩  ⨾ -- ∘ ⇡ LHS ⹁ γ ∷ ⇡ᴸ LHS RHS ⹁ γ ∷ □
         ⟪ L>T ⟫∷ ((⇡ᴸ LHS RHS ⹁ γ ∷ □) {gt = ↓}) ⨾
         ∙ ⇡ M₁ ⹁ γ₁ ∷ ⇡ᴸ LHS RHS ⹁ γ ∷ □ →ᵛᵛ⟨ ∙M∷l ⟩ ⨾ -- ∙M∷l ⟩ ⨾ -- ∘ (⇡ RHS ⹁ γ ∷ ⇡ᴿ (var h) (wk-val (wk-wk wk-id) RHS) ⹁ s-val M₁ γ₁ γ ∷ □)
         (⟪ R>T ⟫∷ ((⇡ᴿ (var h) (wk-val (wk-wk wk-id) RHS) ⹁ s-val M₁ γ₁ γ ∷ □) {gt = ↓})) ⨾
         ∙ ⇡ M₂ ⹁ γ₂ ∷ ⇡ᴿ (var h) (wk-val (wk-wk wk-id) RHS) ⹁ s-val M₁ γ₁ γ ∷ □ →ᵛᵛ⟨ ∙M∷r ⟩
        )

        (∙pair[ var (t h) ⹁ var h ]⹁ s-val M₂ γ₂ (s-val M₁ γ₁ γ) ■)

        (
           ⟦ pair LHS RHS ⟧ᵛ ⟦ γ ⟧ᴱ
         ≡⟨ refl ⟩
           ⟦ pair (var (t h)) (var h) ⟧ᵛ ((⟦ γ ⟧ᴱ ,  ⟦ LHS ⟧ᵛ ⟦ γ ⟧ᴱ) , ⟦ RHS ⟧ᵛ ⟦ γ ⟧ᴱ)
         ≡⟨ cong (λ x → ⟦ pair (var (t h)) (var h) ⟧ᵛ ((⟦ γ ⟧ᴱ ,  x) , ⟦ RHS ⟧ᵛ ⟦ γ ⟧ᴱ)) L≡M  ⟩
           ⟦ pair (var (t h)) (var h) ⟧ᵛ ((⟦ γ ⟧ᴱ ,  ⟦ M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ RHS ⟧ᵛ ⟦ γ ⟧ᴱ)
         ≡⟨ cong (λ x → ⟦ pair (var (t h)) (var h) ⟧ᵛ ((⟦ γ ⟧ᴱ ,  ⟦ M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , x)) R≡M ⟩
           ⟦ pair (var (t h)) (var h) ⟧ᵛ ((⟦ γ ⟧ᴱ ,  ⟦ M₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ) , ⟦ M₂ ⟧ᵛ ⟦ γ₂ ⟧ᴱ) ∎
        )

eval (pm {A = X} {B = Y} M N) γ with eval M γ
... | steps {T = ∙ ((⇡ pair LHS RHS ⹁ γ₁ ∷ □) {gt = ↓})} M>T _ M≡T with eval N (s-val RHS γ₁ (s-val LHS γ₁ γ))
...     | steps {T = ∙ ((⇡ N' ⹁ γ₂ ∷ □) {gt = ↓})} N>T ∙T N≡T  =

  steps (
          ∘ ⇡ pm M N ⹁ γ ∷ □ →ᵛᵛ⟨ ∘pm ⟩ ⨾ -- ∘ ⇡ M ⹁ γ ∷ ⇡ᴹ M N ⹁ γ ∷ □
          ⟪ M>T ⟫∷ ((⇡ᴹ M N ⹁ γ ∷ □) {gt = ↓}) ⨾
          ∙ ⇡ pair LHS RHS ⹁ γ₁ ∷ ⇡ᴹ M N ⹁ γ ∷ □ →ᵛᵛ⟨ ∙pair∷pm ⟩ ⨾ -- ∘ ⇡ N ⹁ (s-val RHS γ₁ (s-val LHS γ₁ γ)) ∷ □
          N>T
        )

        ∙T

        (
            ⟦ pm M N ⟧ᵛ ⟦ γ ⟧ᴱ
          ≡⟨ refl ⟩
            ⟦ N ⟧ᵛ (assocl (⟦ γ ⟧ᴱ , ⟦ M ⟧ᵛ ⟦ γ ⟧ᴱ))
          ≡⟨ cong (λ x → ⟦ N ⟧ᵛ (assocl (⟦ γ ⟧ᴱ , x))) M≡T  ⟩
            ⟦ N ⟧ᵛ (assocl (⟦ γ ⟧ᴱ , ⟦ pair LHS RHS ⟧ᵛ ⟦ γ₁ ⟧ᴱ))
          ≡⟨ N≡T ⟩
            ⟦ N' ⟧ᵛ ⟦ γ₂ ⟧ᴱ ∎
        )




{-

{-

{-

-- EXAMPLES
--------------------------------------------------

ex1 : ε ⊢ᵛ `Unit
ex1 = pm (pair unit unit) (var (t h))

ex2 : (ε ∙ (`Unit `⇒ `Unit) ∙ `Unit) ⊢ᵛ (`Unit `× (`Unit `⇒ `Unit)) `× `Unit
ex2 = pair (pair (var h) (var (t h))) (var h)

ex3 : ε ⊢ᵛ (`Unit `⇒ `Unit)
ex3 = lam (return unit)

ex4 : (ε ∙ `Unit) ⊢ᵛ `Unit `× `Unit
ex4 = pair (var h) (var h)

---------------------------------------

_ : eval ex1 tt ≡
     steps
                         (∘ ⇡ pm (pair unit unit) (var (t h)) ⹁ tt ∷ □
             →ᵛᵛ⟨ ∘pm ⟩    ∘ ⇡ pair unit unit ⹁ tt ∷ ⇡ᴹ (pair unit unit) (var (t h)) ⹁ tt ∷ □
             →ᵛᵛ⟨ ∘pair ⟩  ∘ ⇡ unit ⹁ tt ∷ ⇡ᴸ unit unit ⹁ tt ∷ ⇡ᴹ (pair unit unit) (var (t h)) ⹁ tt ∷ □
             →ᵛᵛ⟨ ∘unit ⟩  ∙ ⇡ unit ⹁ tt ∷ ⇡ᴸ unit unit ⹁ tt ∷ ⇡ᴹ (pair unit unit) (var (t h)) ⹁ tt ∷ □
             →ᵛᵛ⟨ ∙M∷l ⟩   ∘ ⇡ unit ⹁ tt ∷ ⇡ᴿ (var h) unit ⹁ tt , tt ∷ ⇡ᴹ (pair unit unit) (var (t h)) ⹁ tt ∷ □
             →ᵛᵛ⟨ ∘unit ⟩  ∙ ⇡ unit ⹁ tt ∷ ⇡ᴿ (var h) unit ⹁ tt , tt ∷ ⇡ᴹ (pair unit unit) (var (t h)) ⹁ tt ∷ □
             →ᵛᵛ⟨ ∙M∷r ⟩   ∙ ⇡ pair (var (t h)) (var h) ⹁ (tt , tt) , tt ∷ ⇡ᴹ (pair unit unit) (var (t h)) ⹁ tt ∷ □
             →ᵛᵛ⟨ ∙M∷pm ⟩  ∘ ⇡ var (t h) ⹁ (tt , tt) , tt ∷ □
             →ᵛᵛ⟨ ∘var ⟩)  ∙var t h ⹁ (tt , tt) , tt ■   refl
_ = refl

{-
-- calling agda2-compute-normalised in the hole below evaluates ex2
_ : eval ex2 ((tt , λ _ z → z tt) , tt) ≡ {! eval ex2 ((tt , λ _ z → z tt) , tt) !}
_ = refl
-}

_ : eval ex2 ((tt , λ _ z → z tt) , tt) ≡
       steps
                           (∘ ⇡ pair (pair (var h) (var (t h))) (var h) ⹁ (tt , (λ _ z → z tt)) , tt ∷ □
              →ᵛᵛ⟨ ∘pair ⟩   ∘ ⇡ pair (var h) (var (t h)) ⹁ (tt , (λ _ z → z tt)) , tt ∷ ⇡ᴸ (pair (var h) (var (t h))) (var h) ⹁ (tt , (λ _ z → z tt)) , tt ∷ □
              →ᵛᵛ⟨ ∘pair ⟩   ∘ ⇡ var h ⹁ (tt , (λ _ z → z tt)) , tt ∷ ⇡ᴸ (var h) (var (t h)) ⹁ (tt , (λ _ z → z tt)) , tt ∷ ⇡ᴸ (pair (var h) (var (t h))) (var h) ⹁ (tt , (λ _ z → z tt)) , tt ∷ □
              →ᵛᵛ⟨ ∘var ⟩    ∙ ⇡ var h ⹁ (tt , (λ _ z → z tt)) , tt ∷ ⇡ᴸ (var h) (var (t h)) ⹁ (tt , (λ _ z → z tt)) , tt ∷ ⇡ᴸ (pair (var h) (var (t h))) (var h) ⹁ (tt , (λ _ z → z tt)) , tt ∷ □
              →ᵛᵛ⟨ ∙M∷l ⟩    ∘ ⇡ var (t h) ⹁ (tt , (λ _ z → z tt)) , tt ∷ ⇡ᴿ (var h) (var (t (t h))) ⹁ ((tt , (λ _ z → z tt)) , tt) , tt ∷ ⇡ᴸ (pair (var h) (var (t h))) (var h) ⹁ (tt , (λ _ z → z tt)) , tt ∷ □
              →ᵛᵛ⟨ ∘var ⟩    ∙ ⇡ var (t h) ⹁ (tt , (λ _ z → z tt)) , tt ∷ ⇡ᴿ (var h) (var (t (t h))) ⹁ ((tt , (λ _ z → z tt)) , tt) , tt ∷ ⇡ᴸ (pair (var h) (var (t h))) (var h) ⹁ (tt , (λ _ z → z tt)) , tt ∷ □
              →ᵛᵛ⟨ ∙M∷r ⟩    ∙ ⇡ pair (var (t h)) (var h) ⹁ (((tt , (λ _ z → z tt)) , tt) , tt) , (λ _ z → z tt) ∷ ⇡ᴸ (pair (var h) (var (t h))) (var h) ⹁ (tt , (λ _ z → z tt)) , tt ∷ □
              →ᵛᵛ⟨ ∙M∷l ⟩    ∘ ⇡ var h ⹁ (tt , (λ _ z → z tt)) , tt ∷ ⇡ᴿ (var h) (var (t h)) ⹁ ((tt , (λ _ z → z tt)) , tt) , tt , (λ _ z → z tt) ∷ □
              →ᵛᵛ⟨ ∘var ⟩    ∙ ⇡ var h ⹁ (tt , (λ _ z → z tt)) , tt ∷ ⇡ᴿ (var h) (var (t h)) ⹁ ((tt , (λ _ z → z tt)) , tt) , tt , (λ _ z → z tt) ∷ □
              →ᵛᵛ⟨ ∙M∷r ⟩)   ∙pair[ var (t h) ⹁ var h ]⹁ (((tt , (λ _ z → z tt)) , tt) , tt , (λ _ z → z tt)) , tt ■    refl
_ = refl
-}

-}
-}

-}


