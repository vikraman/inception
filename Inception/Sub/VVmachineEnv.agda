module Inception.Sub.VVmachineEnv (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
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
infixr 25 _⹁_∷⟨_⟩_
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

data Env : (Δ : Ctx) → (Γ : Ctx) → {WK : Wk Γ Δ} → Set where

    z       :  (γ : ⟦ Δ ⟧ˣ) → Env Δ Δ {WK = wk-id}

    --s-val   :  {WK : Wk Γ ε} → {WK' : Wk Γ' ε} → (M : valTerm Γ X) → Env ε Γ {WK = WK} → Env ε Γ' {WK = WK'} → Env ε (Γ' ∙ X) {WK = wk-wk WK'}
    s-val   :  {WK : Wk Γ ε} → (M : valTerm Γ X) → Env ε Γ {WK = WK} → Env ε (Γ ∙ X) {WK = wk-wk WK}

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


variable
    b : Bool
    WK : Wk Γ Δ
    WK' : Wk Γ' Δ
    WK'' : Wk Γ'' Δ
    γ  : Env Δ Γ {WK = WK}
    γ' : Env Δ Γ' {WK = WK'}
    γ'' : Env Δ Γ'' {WK = WK''}


---------------------------------------------------------

infix  15 _→ᴸᴸ_


⟦_⟧ᴱ : {WK : Wk Γ Δ} → (E : Env Δ Γ {WK = WK}) → ⟦ Γ ⟧ˣ
⟦ z γ ⟧ᴱ = γ
⟦ s-val M E ⟧ᴱ = ⟦ E ⟧ᴱ , ⟦ valTerm-to-Val M ⟧ᵛ ⟦ E ⟧ᴱ
--⟦ s-comp W E k E' ⟧ᴱ = ⟦ E' ⟧ᴱ , ⟦ W ⟧ᶜ ⟦ E ⟧ᴱ k


data lState : Ty → Set where

    ⟨_∥_⟩   :  (i : Γ ∋ X) → {WK : Wk Γ Δ} → Env Δ Γ {WK = WK} → lState X

⟦_⟧ᴸ : (S : lState X) → ⟦ X ⟧
⟦ ⟨ i ∥ E ⟩ ⟧ᴸ = ⟦ i ⟧ᵐ ⟦ E ⟧ᴱ

lCtx : (S : lState X) → Ctx
lCtx (⟨_∥_⟩ {Γ = Γ} i E)= Γ


data _→ᴸᴸ_ : lState X → lState X → Set where

    --val-h-step    : {i : Γ ∋ Y} → {WK : Wk Γ ε} → {E : Env ε Γ {WK = WK}} → {WK' : Wk Γ' ε} → {E' : Env ε Γ' {WK = WK'}} → ⟨ h  ∥ s-val (var i) E E' ⟩ →ᴸᴸ ⟨ i ∥ E ⟩

    val-t-step    : {i : Γ ∋ Y} → {WK : Wk Γ ε} → {E : Env ε Γ {WK = WK}} → {M : valTerm Γ X} → ⟨ t i  ∥ s-val M E ⟩ →ᴸᴸ ⟨ i ∥ E ⟩

--    comp-t-step    : {i : Γ' ∋ Y} → {E : Env Γ} → {W : Γ ⊢ᶜ X} → {k : ⟦ X ⟧ → R} → {E' : Env Γ'} → ⟨ t i  ∥ s-comp W E k E' ⟩ →ᴸᴸ ⟨ i ∥ E' ⟩


data _→ᴸᴸ*_ : lState X → lState X → Set where

  _▣ : (S : lState X) → S →ᴸᴸ* S

  _→ᴸᴸ⟨_⟩_ : (S : lState X) → {S' S'' : lState X} → S →ᴸᴸ S' → S' →ᴸᴸ* S'' → S →ᴸᴸ* S''


_⨾ᴸ_ : {F S T : lState X} → (F →ᴸᴸ* S) → (S →ᴸᴸ* T) → (F →ᴸᴸ* T)
_⨾ᴸ_ (S ▣) S>>T = S>>T
_⨾ᴸ_ (F →ᴸᴸ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᴸᴸ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ᴸ S₂>>T)


{-
data lHaltingState : lState X → Set where

      found-z      :  {i : Γ ∙ X ∋ Y} → {γ : ⟦ Γ ∙ X ⟧ˣ} → lHaltingState ⟨ i ∥ z γ ⟩

      --found-val    :  {M : Γ ⊢ᵛ X} → {WK : Wk Γ ε} → {WK' : Wk Γ' ε} → {γ : Env ε Γ {WK = WK}} → {γ' : Env ε Γ' {WK = WK'}} → lHaltingState ⟨ h ∥ s-val M γ γ' ⟩

      --found-comp   :  {W : Γ ⊢ᶜ X} → {γ : Env Γ} → {k : ⟦ X ⟧ → R} → {γ' : Env Γ'} → lHaltingState ⟨ h ∥ s-comp W γ k γ' ⟩

      found-unit : {WK : Wk Γ ε} → {WK' : Wk Γ' ε} → {γ : Env ε Γ {WK = WK}} → {γ' : Env ε Γ' {WK = WK'}} → lHaltingState ⟨ h ∥ s-val unit γ γ' ⟩

      found-pair : {LHS : Γ ⊢ᵛ X} → {RHS : Γ ⊢ᵛ Y} → {WK : Wk Γ ε} → {WK' : Wk Γ' ε} → {γ : Env ε Γ {WK = WK}} → {γ' : Env ε Γ' {WK = WK'}} → lHaltingState ⟨ h ∥ s-val (pair RHS LHS) γ γ' ⟩

      found-lam : {W : (Γ ∙ X) ⊢ᶜ Y} → {WK : Wk Γ ε} → {WK' : Wk Γ' ε} → {γ : Env ε Γ {WK = WK}} → {γ' : Env ε Γ' {WK = WK'}} → lHaltingState ⟨ h ∥ s-val (lam W) γ γ' ⟩

      -- never used
      found-pm : {M : Γ ⊢ᵛ X `× Y} → {N : (Γ ∙ X ∙ Y) ⊢ᵛ Z} → {WK : Wk Γ ε} → {WK' : Wk Γ' ε} → {γ : Env ε Γ {WK = WK}} → {γ' : Env ε Γ' {WK = WK'}} → lHaltingState ⟨ h ∥ s-val (pm M N) γ γ' ⟩
      -}

data nicelHaltingState : lState X → Set where

      found-unit : {WK : Wk Γ ε} → {γ : Env ε Γ {WK = WK}} → nicelHaltingState ⟨ h ∥ s-val val-unit γ ⟩

      found-pair : {LHS : valTerm Γ X} → {RHS : valTerm Γ Y} → {WK : Wk Γ ε} → {γ : Env ε Γ {WK = WK}} → nicelHaltingState ⟨ h ∥ s-val (val-pair RHS LHS) γ ⟩
      --found-pair : {LHS : Γ ⊢ᵛ X} → {RHS : Γ ⊢ᵛ Y} → {WK : Wk Γ ε} → {γ : Env ε Γ {WK = WK}} → nicelHaltingState ⟨ h ∥ s-val (val-pair RHS LHS) γ ⟩

      found-lam : {W : (Γ ∙ X) ⊢ᶜ Y} → {WK : Wk Γ ε} → {γ : Env ε Γ {WK = WK}} → nicelHaltingState ⟨ h ∥ s-val (val-lam W) γ ⟩

      -- -- never used
      -- found-pm : {M : Γ ⊢ᵛ X `× Y} → {N : (Γ ∙ X ∙ Y) ⊢ᵛ Z} → {WK : Wk Γ ε} → {WK' : Wk Γ' ε} → {γ : Env ε Γ {WK = WK}} → {γ' : Env ε Γ' {WK = WK'}} → nicelHaltingState ⟨ h ∥ s-val (val-pm M N) γ γ' ⟩

{-
data correctStepsLL : lState X → Set where

  steps : {S T : lState X} → S →ᴸᴸ* T → lHaltingState T → ⟦ S ⟧ᴸ ≡ ⟦ T ⟧ᴸ → correctStepsLL S
  -}

data nicecorrectStepsLL : lState X → Set where

  steps : {S T : lState X} → S →ᴸᴸ* T → nicelHaltingState T → ⟦ S ⟧ᴸ ≡ ⟦ T ⟧ᴸ → Wk (lCtx S) (lCtx T) → nicecorrectStepsLL S


{-
lookup : (i : Γ ∋ X) → {WK : Wk Γ Δ} → (γ : Env Δ Γ {WK = WK}) → correctStepsLL {X = X} ⟨ i ∥ γ ⟩
lookup h (z γ) = steps (⟨ h ∥ z γ ⟩ ▣) found-z refl
lookup h (s-val (var i) γ γ₁) with lookup i γ
... | steps i>>T HT i≡T = steps (_ →ᴸᴸ⟨ val-h-step ⟩ i>>T) HT i≡T
lookup h (s-val (lam W) γ γ₁) = steps (⟨ h ∥ s-val (lam W) γ γ₁ ⟩ ▣) found-lam refl
lookup h (s-val (pair LHS RHS) γ γ₁) = steps (⟨ h ∥ s-val (pair LHS RHS) γ γ₁ ⟩ ▣) found-pair refl
lookup h (s-val (pm M N) γ γ₁) = steps (⟨ h ∥ s-val (pm M N) γ γ₁ ⟩ ▣) found-pm refl
lookup h (s-val unit γ γ₁) = steps (⟨ h ∥ s-val unit γ γ₁ ⟩ ▣) found-unit refl
lookup (t i) (z γ) = steps (⟨ t i ∥ z γ ⟩ ▣) found-z refl
lookup (t i) (s-val M γ γ₁) with lookup i γ₁
... | steps i>>T HT i≡T = steps (_ →ᴸᴸ⟨ val-t-step ⟩ i>>T) HT i≡T

lookup-s : (i : Γ ∋ X) → {WK : Wk Γ ε} → (γ : Env ε Γ {WK = WK}) → nicecorrectStepsLL {X = X} ⟨ i ∥ γ ⟩
lookup-s h (s-val (var i) γ γ₁) with lookup-s i γ
... | steps i>>T HT i≡T = steps (_ →ᴸᴸ⟨ val-h-step ⟩ i>>T) HT i≡T
lookup-s h (s-val (lam W) γ γ₁) = steps (⟨ h ∥ s-val (lam W) γ γ₁ ⟩ ▣) found-lam refl
lookup-s h (s-val (pair LHS RHS) γ γ₁) = steps (⟨ h ∥ s-val (pair LHS RHS) γ γ₁ ⟩ ▣) found-pair refl
lookup-s h (s-val (pm M N) γ γ₁) = steps (⟨ h ∥ s-val (pm M N) γ γ₁ ⟩ ▣) found-pm refl
lookup-s h (s-val unit γ γ₁) = steps (⟨ h ∥ s-val unit γ γ₁ ⟩ ▣) found-unit refl
lookup-s (t i) (s-val M γ γ₁) with lookup-s i γ₁
... | steps i>>T HT i≡T = steps (_ →ᴸᴸ⟨ val-t-step ⟩ i>>T) HT i≡T

-}

lookup-t : (i : Γ ∋ X) → {WK : Wk Γ ε} → (γ : Env ε Γ {WK = WK}) → nicecorrectStepsLL {X = X} ⟨ i ∥ γ ⟩
lookup-t h (s-val (val-lam W) γ) = steps (⟨ h ∥ s-val (val-lam W) γ ⟩ ▣) found-lam refl wk-id
lookup-t h (s-val (val-pair LHS RHS) γ) = steps (⟨ h ∥ s-val (val-pair LHS RHS) γ ⟩ ▣) found-pair refl wk-id
lookup-t h (s-val val-unit γ) = steps (⟨ h ∥ s-val (val-unit) γ ⟩ ▣) found-unit refl wk-id
lookup-t (t i) (s-val M γ) with lookup-t i γ
... | steps i>>T HT i≡T WK = steps (_ →ᴸᴸ⟨ val-t-step ⟩ i>>T) HT i≡T (wk-wk WK)



{-
lookup : (i : Γ ∋ X) → {WK : Wk Γ Δ} → (γ : Env Δ Γ {WK = WK}) → correctStepsLL {X = X} ⟨ i ∥ γ ⟩
lookup h (z γ) = steps (⟨ h ∥ z γ ⟩ ▣) found-z refl
lookup h (s-val M γ E') = steps (⟨ h ∥ s-val M γ E' ⟩ ▣) found-val refl
--lookup h (s-comp W γ k E') = steps (⟨ h ∥ s-comp W γ k E' ⟩ ▣) found-comp refl
lookup (t i) (z γ) = steps (⟨ t i ∥ z γ ⟩ ▣) found-z refl
lookup (t i) (s-val M γ E') with lookup i E'
... | steps S>T HT S≡T = steps (⟨ t i ∥ s-val M γ E' ⟩ →ᴸᴸ⟨ val-t-step ⟩ S>T) HT S≡T
--lookup (t i) (s-comp W γ k E') with lookup i E'
--... | steps S>T HT S≡T = steps (⟨ t i ∥ s-comp W γ k E' ⟩ →ᴸᴸ⟨ comp-t-step ⟩ S>T) HT S≡T
-}


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


data vStack : Ctx → Ctx → Ctx → Bool → Ty → Set where

    □ : {Δ : Ctx} → vStack Δ Γ Γ false T◾

    _⹁_∷⟨_⟩_ : {Δ : Ctx} → partialTerm Γ X → {WK : Wk Γ Δ} → (γ : Env Δ Γ {WK = WK}) → (π : Wk Γ Ψ) → (tail : vStack Δ Ψ Θ b T◾) → {gt : goodType b X T◾} → vStack Δ Γ Θ true T◾

data vState : Ctx → Ty → Set where

     ∘_ : vStack Δ Ψ Θ true T◾ → vState Δ T◾

     ∙_ : vStack Δ Ψ Θ true T◾ → vState Δ T◾


--infix  15 _→ⱽᴸ_
--data _→ⱽᴸ_ : vState T◾ → lState X → Set where
--
--     start-lookup    : {i : Γ ∋ X} → {γ : Env Γ} → {tail : vStack b T◾} → {gt : goodType b X T◾} → ∘ ((⇡ var i ⹁ γ ∷ tail) {gt = gt}) →ⱽᴸ ⟨ i ∥ γ ∥ tail ﹐ gt ⟩
--
--infix  15 _→ᴸⱽ_
--data _→ᴸⱽ_ : lState X → vState T◾ → Set where
--
--     finish-lookup    : {M : (Γ ∙ X) ⊢ᵛ Y} → {γ : Env (Γ ∙ X)} → {γ' : Env Γ'} → {tail : vStack b T◾} → {gt : goodType b Y T◾} → ⟨ h ∥ s-val M γ γ' ∥ tail ﹐ gt ⟩ →ᴸⱽ ∙ ((⇡ M ⹁ γ ∷ tail) {gt = gt})

data _→ᵛᵛ_ : vState ε T◾ → vState ε T◾ → Set where

     -- ∘var-z    :    {i : Γ ∋ X} → {tail : vStack Γ' b T◾} → {gt : goodType b X T◾}

     --            → {i' : (Γ') ∋ X} → {γ' : ⟦ Γ' ⟧ˣ}

     --            → (⟨ i ∥ γ ⟩ →ᴸᴸ* ⟨ i' ∥ z γ' ⟩)
     --           ----------------------------------------------------------------
     --            → ∘ ((⇡ var i ⹁ γ ∷ tail) {gt = gt}) →ᵛᵛ ∙ ((_⹁_∷_ {ε = Γ'} (⇡ var i') (z γ') tail) {gt = gt}) -- ((⇡ var i' ⹁ (z γ') ∷ tail) {gt = gt})

     ∘var    :    {i : Γ ∋ X} → {tail : vStack ε Ψ Θ b T◾} → {gt : goodType b X T◾}

                → {M : valTerm Γ' X} → {π : Wk Γ Ψ} → {πᵥ : Wk Γ Γ'}

                → (⟨ i ∥ γ ⟩ →ᴸᴸ* ⟨ h ∥ s-val M γ' ⟩)

               ----------------------------------------------------------------
                → ∘ ((⇡ var i ⹁ γ ∷⟨ π ⟩ tail) {gt = gt}) →ᵛᵛ ∙ ((⭭ (wk-valTerm πᵥ M) ⹁ γ ∷⟨ π ⟩ tail) {gt = gt})

     ∘lam   :  {M : (Γ ∙ X) ⊢ᶜ Y} → {π : Wk Γ Ψ}
             → {tail : vStack ε Ψ Θ b T◾} → {gt : goodType b (X `⇒ Y) T◾}
               ---------------------------------------------------------------------------
             →     ∘ ((⇡ lam M ⹁ γ ∷⟨ π ⟩ tail) {gt = gt})
                →ᵛᵛ ∙ ((⇡ lam M ⹁ γ ∷⟨ π ⟩ tail) {gt = gt})

     ∘pair  :  {LHS : Γ ⊢ᵛ X} → {RHS : Γ ⊢ᵛ Y}  → {π : Wk Γ Ψ}
             → {tail : vStack ε Ψ Θ b T◾} → {gt : goodType b (X `× Y) T◾}
               ---------------------------------------------------------------------------
             →     ∘ ((⇡ pair LHS RHS ⹁ γ ∷⟨ π ⟩ tail) {gt = gt})
                →ᵛᵛ ∘ ((⇡ LHS ⹁ γ ∷⟨ wk-id ⟩ ((⇡ᴸ LHS RHS ⹁ γ ∷⟨ π ⟩ tail) {gt = gt})) {gt = ↕})

     ∘pm    :  {M : Γ ⊢ᵛ X `× Y} → {N : (Γ ∙ X ∙ Y) ⊢ᵛ Z} → {π : Wk Γ Ψ}
             → {tail : vStack ε Ψ Θ b T◾} → {gt : goodType b Z T◾}
               ---------------------------------------------------------------------------
             →     ∘ ((⇡ pm M N ⹁ γ ∷⟨ π ⟩ tail) {gt = gt})
                →ᵛᵛ ∘ ((⇡ M ⹁ γ ∷⟨ wk-id ⟩ (⇡ᴹ M N ⹁ γ ∷⟨ π ⟩ tail) {gt = gt}) {gt = ↕})

     ∘unit  :  {γ  : Env ε Γ {WK = WK}} → {π : Wk Γ Ψ}
             → {tail : vStack ε Ψ Θ b T◾} → {gt : goodType b `Unit T◾}
               ---------------------------------------------------------------------------
             →     ∘ ((⇡ unit ⹁ γ ∷⟨ π ⟩ tail) {gt = gt})
                →ᵛᵛ ∙ ((⭭ val-unit ⹁ γ ∷⟨ π ⟩ tail) {gt = gt})

     ∙M∷l   :  {M : valTerm Γ X} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y} → {π : Wk Γ' Ψ} → {π' : Wk Γ Γ'}
             → {tail : vStack ε Ψ Θ b T◾} → {gt : goodType b (X `× Y) T◾}
               ---------------------------------------------------------------------------
             →     ∙ ((⭭ M ⹁ γ ∷⟨ π' ⟩ ((⇡ᴸ LHS RHS ⹁ γ' ∷⟨ π ⟩ tail) {gt = gt})) {gt = ↕})
                →ᵛᵛ ∘ ((⇡ wk-val π' RHS ⹁ γ ∷⟨ wk-id ⟩ ((⇡ᴿ M (wk-val π' RHS) ⹁ γ ∷⟨ wk-trans π' π ⟩ tail) {gt = gt})) {gt = ↕})
                --→ᵛᵛ ∘ ((⇡ RHS ⹁ γ' ∷⟨ ? ⟩ ((⇡ᴿ (var h) (wk-val (wk-wk wk-id) RHS) ⹁ s-val M γ γ' ∷⟨ ? ⟩ tail) {gt = gt})) {gt = ↕})

     ∙M∷r   :  {M : valTerm Γ Y} → {LHS : valTerm Γ' X} → {RHS : Γ' ⊢ᵛ Y} → {π : Wk Γ' Ψ} → {π' : Wk Γ Γ'}
             → {tail : vStack ε Ψ Θ b T◾} → {gt : goodType b (X `× Y) T◾}
               ---------------------------------------------------------------------------
             →     ∙ ((⭭ M ⹁ γ ∷⟨ π' ⟩ ((⇡ᴿ LHS RHS ⹁ γ' ∷⟨ π ⟩ tail) {gt = gt})) {gt = ↕})
                →ᵛᵛ ∙ ((⭭ val-pair (wk-valTerm π' LHS) M ⹁ γ ∷⟨ wk-trans π' π ⟩ tail) {gt = gt})
                --→ᵛᵛ ∙ ((⭭ val-pair (wk-val (wk-wk wk-id) LHS) (var h) ⹁ s-val M γ γ' ∷⟨ ? ⟩ tail) {gt = gt})

     ∙pair∷pm  :  {LHS : valTerm Γ X} → {RHS : valTerm Γ Y} → {M : Γ' ⊢ᵛ X `× Y} → {N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z'}
             → {π : Wk Γ' Ψ} → {π' : Wk Γ Γ'}
             → {tail : vStack ε Ψ Θ b T◾} → {gt : goodType b Z' T◾}
               ---------------------------------------------------------------------------
             →     ∙ ((⭭ val-pair LHS RHS ⹁ γ ∷⟨ π' ⟩ ((⇡ᴹ M N ⹁ γ' ∷⟨ π ⟩ tail) {gt = gt})) {gt = ↕})
                →ᵛᵛ  ∘ ((⇡ (wk-val (wk-cong (wk-cong π')) N) ⹁ s-val (wk-valTerm (wk-wk wk-id) RHS) ((s-val LHS γ)) ∷⟨ wk-wk (wk-wk (wk-trans π' π)) ⟩ tail) {gt = gt})
                --→ᵛᵛ ∘ ((⇡ N ⹁ s-val RHS γ (s-val LHS γ γ') ∷⟨ ? ⟩ tail) {gt = gt})



data _↠ᵛᵛ_ : vState ε T◾ → vState ε T◾ → Set where

  _→ᵛᵛ⟨_⟩ : (S : vState ε T◾) → {S' : vState ε T◾} → (laststep : S →ᵛᵛ S') → S ↠ᵛᵛ S'

  _→ᵛᵛ⟨_⟩_ : (S : vState ε T◾) → {S' S'' : vState ε T◾} → S →ᵛᵛ S' → S' ↠ᵛᵛ S'' → S ↠ᵛᵛ S''

_⨾_ : {F S T : vState ε T◾} → (F ↠ᵛᵛ S) → (S ↠ᵛᵛ T) → (F ↠ᵛᵛ T)
_⨾_ (F →ᵛᵛ⟨ F>S ⟩) S>>T = F →ᵛᵛ⟨ F>S ⟩ S>>T
_⨾_ (F →ᵛᵛ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᵛᵛ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ S₂>>T)

-- _⦂⦂_ : vStack ε Ψ Θ b T◾ → vStack ε Θ Θ' true T◾' → vStack ε Ψ Θ' true T◾'
-- □ ⦂⦂ lower = lower
-- (M ⹁ γ ∷⟨ π ⟩ upper) ⦂⦂ lower = (M ⹁ γ ∷⟨ π ⟩ (upper ⦂⦂ lower)) {gt = ↕}

_⦂⦂⟨_⟩_ : vStack ε Ψ Θ true T◾ → Wk Θ Ψ' → vStack ε Ψ' Θ' true T◾' → vStack ε Ψ Θ' true T◾'
(M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ □) ⦂⦂⟨ π ⟩ ((⭭ x ⹁ γ₂ ∷⟨ π₂ ⟩ lower) {gt = gt}) = (M₁ ⹁ γ₁ ∷⟨ wk-id ⟩ ((⭭ wk-valTerm (wk-trans π₁ π) x ⹁ γ₁ ∷⟨ wk-trans (wk-trans π₁ π) π₂ ⟩ lower)) {gt = gt} ) {gt = ↕}
(M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ □) ⦂⦂⟨ π ⟩ ((⇡ M ⹁ γ₂ ∷⟨ π₂ ⟩ lower) {gt = gt}) = (M₁ ⹁ γ₁ ∷⟨ wk-id ⟩ ((⇡ wk-val (wk-trans π₁ π) M ⹁ γ₁ ∷⟨ wk-trans (wk-trans π₁ π) π₂ ⟩ lower)) {gt = gt} ) {gt = ↕}
(M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ □) ⦂⦂⟨ π ⟩ ((⇡ᴹ M N ⹁ γ₂ ∷⟨ π₂ ⟩ lower) {gt = gt}) = (M₁ ⹁ γ₁ ∷⟨ wk-id ⟩ ((⇡ᴹ (wk-val (wk-trans π₁ π) M) (wk-val (wk-trans (wk-cong (wk-cong π₁)) (wk-cong (wk-cong π))) N) ⹁ γ₁ ∷⟨ wk-trans (wk-trans π₁ π) π₂ ⟩ lower)) {gt = gt} ) {gt = ↕}
(M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ □) ⦂⦂⟨ π ⟩ ((⇡ᴸ LHS RHS ⹁ γ₂ ∷⟨ π₂ ⟩ lower) {gt = gt}) = (M₁ ⹁ γ₁ ∷⟨ wk-id ⟩ ((⇡ᴸ (wk-val (wk-trans π₁ π) LHS) (wk-val (wk-trans π₁ π) RHS) ⹁ γ₁ ∷⟨ wk-trans (wk-trans π₁ π) π₂ ⟩ lower)) {gt = gt} ) {gt = ↕}
(M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ □) ⦂⦂⟨ π ⟩ ((⇡ᴿ LHS RHS ⹁ γ₂ ∷⟨ π₂ ⟩ lower) {gt = gt}) = (M₁ ⹁ γ₁ ∷⟨ wk-id ⟩ ((⇡ᴿ (wk-valTerm (wk-trans π₁ π) LHS) (wk-val (wk-trans π₁ π) RHS) ⹁ γ₁ ∷⟨ wk-trans (wk-trans π₁ π) π₂ ⟩ lower)) {gt = gt} ) {gt = ↕}
((M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ ((x ⹁ γ ∷⟨ π₃ ⟩ upper) {gt = gt})) {gt = ↕}) ⦂⦂⟨ π ⟩ ((M₂ ⹁ γ₂ ∷⟨ π₂ ⟩ lower) {gt = gt2}) = (M₁ ⹁ γ₁ ∷⟨ π₁ ⟩ (((x ⹁ γ ∷⟨ π₃ ⟩ upper) {gt = gt} ) ⦂⦂⟨ π ⟩ ((M₂ ⹁ γ₂ ∷⟨ π₂ ⟩ lower) {gt = gt2}))) {gt = ↕}


{-
_::_ : vState ε T◾ → vStack ε true T◾' → vState ε T◾'
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

⟨_⟩∷_ : {from : vState ε T◾} → {to : vState ε T◾} → (F>T : from →ᵛᵛ to) → (tail : vStack ε true T◾') → (from :: tail) →ᵛᵛ (to :: tail)
--⟨ ∘var-z T>>U ⟩∷ tail = ∘var-z T>>U
⟨ ∘var T>>U ⟩∷ tail = ∘var T>>U
⟨ ∘lam ⟩∷ tail = ∘lam
⟨ ∘pair ⟩∷ tail = ∘pair
⟨ ∘pm ⟩∷ tail = ∘pm
⟨ ∘unit ⟩∷ tail = ∘unit
⟨ ∙pair∷pm ⟩∷ tail = ∙pair∷pm
⟨ ∙M∷l ⟩∷ tail = ∙M∷l
⟨ ∙M∷r ⟩∷ tail = ∙M∷r

⟪_⟫∷_ : {from : vState ε T◾} → {to : vState ε T◾} → (F>T : from ↠ᵛᵛ to) → (tail : vStack ε true T◾') → (from :: tail) ↠ᵛᵛ (to :: tail)
⟪ _ →ᵛᵛ⟨ F>T ⟩ ⟫∷ tail =  _ →ᵛᵛ⟨ ⟨ F>T ⟩∷ tail ⟩
⟪ _ →ᵛᵛ⟨ F>T ⟩ F>>T ⟫∷ tail =   _ →ᵛᵛ⟨ ⟨ F>T ⟩∷ tail ⟩ (⟪ F>>T ⟫∷ tail)


⟦_⟧↥ : (S : vStack ε true T◾) → ⟦ T◾ ⟧
⟦ ((⇡ M) ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ M ⟧ᵛ ⟦ γ ⟧ᴱ
⟦ (⇡ᴹ M N ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ pm M N ⟧ᵛ ⟦ γ ⟧ᴱ
⟦ (⇡ᴸ LHS RHS ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ pair LHS RHS ⟧ᵛ ⟦ γ ⟧ᴱ
⟦ (⇡ᴿ LHS RHS ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ pair LHS RHS ⟧ᵛ ⟦ γ ⟧ᴱ
⟦ ((⇡ M) ⹁ γ₁ ∷ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂}) {gt = gt₁} ⟧↥ = ⟦ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂} ⟧↥
⟦ (⇡ᴹ M N ⹁ γ₁ ∷ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂}) {gt = gt₁} ⟧↥ = ⟦ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂} ⟧↥
⟦ (⇡ᴸ LHS RHS ⹁ γ₁ ∷ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂}) {gt = gt₁} ⟧↥ = ⟦ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂} ⟧↥
⟦ (⇡ᴿ LHS RHS ⹁ γ₁ ∷ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂}) {gt = gt₁} ⟧↥ = ⟦ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂} ⟧↥


⟦_⟧◑ : (S : vState ε T◾) → ⟦ T◾ ⟧
⟦ ∘ tail ⟧◑ = ⟦ tail ⟧↥
⟦ ∙ tail ⟧◑ = ⟦ tail ⟧↥

data vHaltingState : vState Δ T◾ → Set where

     ∙unit⹁_■ : (γ : Env Δ Γ {WK = WK}) → vHaltingState (∙ ((⇡ unit ⹁ γ ∷ □) {gt = ↓}))

     ∙pair[_⹁_]⹁_■ : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → (γ : Env Δ Γ {WK = WK}) → vHaltingState (∙ ((⇡ pair LHS RHS ⹁ γ ∷ □) {gt = ↓}))

     ∙lam_⹁_■ : (M : (Γ ∙ X) ⊢ᶜ Y) → (γ : Env Δ Γ {WK = WK}) → vHaltingState (∙ ((⇡ lam M ⹁ γ ∷ □) {gt = ↓}))


data correctSteps : vState Δ T◾ → Set where

  steps : {S T : vState ε T◾} → S ↠ᵛᵛ T → vHaltingState T → ⟦ S ⟧◑ ≡ ⟦ T ⟧◑ → correctSteps S

eval : (M : Γ ⊢ᵛ X) → {WK : Wk Γ ε} → (γ : Env ε Γ {WK = WK}) → correctSteps {T◾ = X} (∘ ((⇡ M ⹁ γ ∷ □) {gt = ↓}))

eval (var i) γ with lookup-s i γ
... | steps i>>T found-unit i≡T = steps (_ →ᵛᵛ⟨ ∘var i>>T ⟩) ∙unit⹁ _ ■ i≡T
... | steps i>>T found-pair i≡T = steps (_ →ᵛᵛ⟨ ∘var i>>T ⟩) ∙pair[ _ ⹁ _ ]⹁ _ ■ i≡T
... | steps i>>T found-lam i≡T = steps (_ →ᵛᵛ⟨ ∘var i>>T ⟩) ∙lam _ ⹁ _ ■ i≡T
... | steps i>>T found-pm i≡T = {!!}
--with lookup (t i) γ
--... | steps i>>T HT i≡t = {!!}

eval = {!!}

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

-}

