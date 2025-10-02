module Inception.Sub.VVmachineP (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Unit

variable
  X Y Z X' Y' Z' T◾ T◾' : Ty
  Γ' : Ctx
  γ  : ⟦ Γ ⟧ˣ
  γ' : ⟦ Γ' ⟧ˣ

infix  26 ⇡_
infixr 25 _⹁_∷_
infix  20 ∘_
infix  20 ∙_
infixr 17 _→ᵛᵛ⟨_⟩
infixr 15 _→ᵛᵛ⟨_⟩_
infix  15 _→ᵛᵛ_
infixr 10 _⨾_


data partialTerm : (Γ : Ctx) → (X : Ty) → Set where

    ⇡_ : (M : Γ ⊢ᵛ X) → partialTerm Γ X

    ⇡ᴹ : (M : Γ ⊢ᵛ X `× Y) → (N : (Γ ∙ X ∙ Y) ⊢ᵛ Z) → partialTerm Γ Z

    ⇡ᴸ : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → partialTerm Γ (X `× Y)

    ⇡ᴿ  : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → partialTerm Γ (X `× Y)


data Bool : Set where
     true : Bool
     false : Bool


variable
     b : Bool


data goodType : Bool → Ty → Ty → Set where

     ↓ : goodType false X X

     ↕ : goodType true X Y


data vStack : Bool → Ty → Set where

    □ : vStack false T◾

    _⹁_∷_ : partialTerm Γ X → (γ : ⟦ Γ ⟧ˣ) → (tail : vStack b T◾) → {gt : goodType b X T◾} → vStack true T◾


data vState : Ty → Set where

     ∘_ : vStack true T◾ → vState T◾

     ∙_ : vStack true T◾ → vState T◾


data _→ᵛᵛ_ : vState T◾ → vState T◾ → Set where

     ∘var   :  {i : Γ ∋ X}
             → {tail : vStack b T◾} → {gt : goodType b X T◾}
               ---------------------------------------------------------------------------
             →     ∘ ((⇡ var i ⹁ γ ∷ tail) {gt = gt})
                →ᵛᵛ ∙ ((⇡ var i ⹁ γ ∷ tail) {gt = gt})

     ∘lam   :  {M : (Γ ∙ X) ⊢ᶜ Y}
             → {tail : vStack b T◾} → {gt : goodType b (X `⇒ Y) T◾}
               ---------------------------------------------------------------------------
             →     ∘ ((⇡ lam M ⹁ γ ∷ tail) {gt = gt})
                →ᵛᵛ ∙ ((⇡ lam M ⹁ γ ∷ tail) {gt = gt})

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

     ∘unit  :  {γ  : ⟦ Γ ⟧ˣ} → {tail : vStack b T◾} → {gt : goodType b `Unit T◾}
               ---------------------------------------------------------------------------
             →     ∘ ((⇡ unit ⹁ γ ∷ tail) {gt = gt})
                →ᵛᵛ ∙ ((⇡ unit ⹁ γ ∷ tail) {gt = gt})

     ∙pair∷pm  :  {LHS : Γ ⊢ᵛ X} → {RHS : Γ ⊢ᵛ Y} → {M : Γ' ⊢ᵛ X `× Y} → {N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z'}
             → {tail : vStack b T◾} → {gt : goodType b Z' T◾}
               ---------------------------------------------------------------------------
             →     ∙ ((⇡ pair LHS RHS ⹁ γ ∷ ((⇡ᴹ M N ⹁ γ' ∷ tail) {gt = gt})) {gt = ↕})
                →ᵛᵛ ∘ ((⇡ N ⹁ ((γ' , ⟦ LHS ⟧ᵛ γ) , ⟦ RHS ⟧ᵛ γ) ∷ tail) {gt = gt})

     ∙M∷l   :  {M : Γ ⊢ᵛ X} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y}
             → {tail : vStack b T◾} → {gt : goodType b (X `× Y) T◾}
               ---------------------------------------------------------------------------
             →     ∙ ((⇡ M ⹁ γ ∷ ((⇡ᴸ LHS RHS ⹁ γ' ∷ tail) {gt = gt})) {gt = ↕})
                →ᵛᵛ ∘ ((⇡ RHS ⹁ γ' ∷ ((⇡ᴿ (var h) (wk-val (wk-wk wk-id) RHS) ⹁ (γ' , ⟦ M ⟧ᵛ γ) ∷ tail) {gt = gt})) {gt = ↕})

     ∙M∷r   :  {M : Γ ⊢ᵛ Y} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y}
             → {tail : vStack b T◾} → {gt : goodType b (X `× Y) T◾}
               ---------------------------------------------------------------------------
             →     ∙ ((⇡ M ⹁ γ ∷ ((⇡ᴿ LHS RHS ⹁ γ' ∷ tail) {gt = gt})) {gt = ↕})
                →ᵛᵛ ∙ ((⇡ pair (wk-val (wk-wk wk-id) LHS) (var h) ⹁ (γ' , ⟦ M ⟧ᵛ γ) ∷ tail) {gt = gt})


data _↠ᵛᵛ_ : vState T◾ → vState T◾ → Set where

  _→ᵛᵛ⟨_⟩ : (S : vState T◾) → {S' : vState T◾} → (laststep : S →ᵛᵛ S') → S ↠ᵛᵛ S'

  _→ᵛᵛ⟨_⟩_ : (S : vState T◾) → {S' S'' : vState T◾} → S →ᵛᵛ S' → S' ↠ᵛᵛ S'' → S ↠ᵛᵛ S''


_⨾_ : {F S T : vState T◾} → (F ↠ᵛᵛ S) → (S ↠ᵛᵛ T) → (F ↠ᵛᵛ T)
_⨾_ (F →ᵛᵛ⟨ F>S ⟩) S>>T = F →ᵛᵛ⟨ F>S ⟩ S>>T
_⨾_ (F →ᵛᵛ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᵛᵛ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ S₂>>T)


_⦂⦂_ : vStack b T◾ → vStack true T◾' → vStack true T◾'
□ ⦂⦂ lower = lower
(M ⹁ γ ∷ upper) ⦂⦂ lower = (M ⹁ γ ∷ (upper ⦂⦂ lower)) {gt = ↕}


_::_ : vState T◾ → vStack true T◾' → vState T◾'
(∘ upper) :: lower = ∘ (upper ⦂⦂ lower)
(∙ upper) :: lower = ∙ (upper ⦂⦂ lower)

⟨_⟩∷_ : {from : vState T◾} → {to : vState T◾} → (F>T : from →ᵛᵛ to) → (tail : vStack true T◾') → (from :: tail) →ᵛᵛ (to :: tail)
⟨ ∘var ⟩∷ tail = ∘var
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
⟦ ((⇡ M) ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ M ⟧ᵛ γ
⟦ (⇡ᴹ M N ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ pm M N ⟧ᵛ γ
⟦ (⇡ᴸ LHS RHS ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ pair LHS RHS ⟧ᵛ γ
⟦ (⇡ᴿ LHS RHS ⹁ γ ∷ □) {gt = ↓} ⟧↥ = ⟦ pair LHS RHS ⟧ᵛ γ
⟦ ((⇡ M) ⹁ γ₁ ∷ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂}) {gt = gt₁} ⟧↥ = ⟦ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂} ⟧↥
⟦ (⇡ᴹ M N ⹁ γ₁ ∷ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂}) {gt = gt₁} ⟧↥ = ⟦ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂} ⟧↥
⟦ (⇡ᴸ LHS RHS ⹁ γ₁ ∷ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂}) {gt = gt₁} ⟧↥ = ⟦ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂} ⟧↥
⟦ (⇡ᴿ LHS RHS ⹁ γ₁ ∷ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂}) {gt = gt₁} ⟧↥ = ⟦ (M₂ ⹁ γ₂ ∷ S) {gt = gt₂} ⟧↥


⟦_⟧◑ : (S : vState T◾) → ⟦ T◾ ⟧
⟦ ∘ tail ⟧◑ = ⟦ tail ⟧↥
⟦ ∙ tail ⟧◑ = ⟦ tail ⟧↥


data vHaltingState : vState T◾ → Set where

     -- ∙var_⹁_■ : (i : (Γ ∙ Y) ∋ X) → (γ : ⟦ Γ ∙ Y ⟧ˣ) → vHaltingState (∙ ((⇡ var i ⹁ γ ∷ □) {gt = ↓}))

     ∙unit⹁_■ : (γ : ⟦ Γ ⟧ˣ) → vHaltingState (∙ ((⇡ unit ⹁ γ ∷ □) {gt = ↓}))

     ∙pair[_⹁_]⹁_■ : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → (γ : ⟦ Γ ⟧ˣ) → vHaltingState (∙ ((⇡ pair LHS RHS ⹁ γ ∷ □) {gt = ↓}))

     ∙lam_⹁_■ : (M : (Γ ∙ X) ⊢ᶜ Y) → (γ : ⟦ Γ ⟧ˣ) → vHaltingState (∙ ((⇡ lam M ⹁ γ ∷ □) {gt = ↓}))


data correctSteps : vState T◾ → Set where

  steps : {S T : vState T◾} → S ↠ᵛᵛ T → vHaltingState T → ⟦ S ⟧◑ ≡ ⟦ T ⟧◑ → correctSteps S

{-
eval : (M : Γ ⊢ᵛ X) → (γ : ⟦ Γ ⟧ˣ) → correctSteps {T◾ = X} (∘ ((⇡ M ⹁ γ ∷ □) {gt = ↓}))

eval (var i) γ = {!!} <<-------- WE NEED A LOOKUP MACHINE!
eval (lam M) γ = steps (∘ ⇡ lam M ⹁ γ ∷ □ →ᵛᵛ⟨ ∘lam ⟩) (∙lam M ⹁ γ ■) refl
eval unit γ = steps (∘ ⇡ unit ⹁ γ ∷ □ →ᵛᵛ⟨ ∘unit ⟩) (∙unit⹁ γ ■) refl

eval {X = X `× Y} (pair LHS RHS) γ with eval {X = X} LHS γ | eval RHS γ
... | steps {T = ∙ ((⇡ M₁ ⹁ γ₁ ∷ □) {gt = ↓})} L>T _ L≡M | steps {T = ∙ ((⇡ M₂ ⹁ γ₂ ∷ □) {gt = ↓})} R>T _ R≡M = -- {!!}

  steps (
        ∘ ⇡ pair LHS RHS ⹁ γ ∷ □ →ᵛᵛ⟨ ∘pair ⟩  ⨾ -- ∘ ⇡ LHS ⹁ γ ∷ ⇡ᴸ LHS RHS ⹁ γ ∷ □
        ⟪ L>T ⟫∷ ((⇡ᴸ LHS RHS ⹁ γ ∷ □) {gt = ↓}) ⨾
        ∙ ⇡ M₁ ⹁ γ₁ ∷ ⇡ᴸ LHS RHS ⹁ γ ∷ □ →ᵛᵛ⟨ ∙M∷l ⟩ ⨾ -- ∘ (⇡ RHS ⹁ γ ∷ ⇡ᴿ (var h) (wk-val (wk-wk wk-id) RHS) ⹁ (γ ,  ⟦ M₁ ⟧ᵛ γ₁) ∷ □)
        ⟪ R>T ⟫∷ ((⇡ᴿ (var h) (wk-val (wk-wk wk-id) RHS) ⹁ (γ ,  ⟦ M₁ ⟧ᵛ γ₁) ∷ □) {gt = ↓}) ⨾
        ∙ ⇡ M₂ ⹁ γ₂ ∷ ⇡ᴿ (var h) (wk-val (wk-wk wk-id) RHS) ⹁ (γ ,  ⟦ M₁ ⟧ᵛ γ₁) ∷ □ →ᵛᵛ⟨ ∙M∷r ⟩
        )

        (∙pair[ (wk-val (wk-wk wk-id) (var h)) ⹁ var h ]⹁ ((γ ,  ⟦ M₁ ⟧ᵛ γ₁) , ⟦ M₂ ⟧ᵛ γ₂) ■)

        (
          ⟦ pair LHS RHS ⟧ᵛ γ
        ≡⟨ refl ⟩
          ⟦ pair (wk-val (wk-wk wk-id) (var h)) (var h) ⟧ᵛ ((γ ,  ⟦ LHS ⟧ᵛ γ) , ⟦ RHS ⟧ᵛ γ)
        ≡⟨ cong (λ x → ⟦ pair (wk-val (wk-wk wk-id) (var h)) (var h) ⟧ᵛ ((γ ,  x) , ⟦ RHS ⟧ᵛ γ)) L≡M  ⟩
          ⟦ pair (wk-val (wk-wk wk-id) (var h)) (var h) ⟧ᵛ ((γ ,  ⟦ M₁ ⟧ᵛ γ₁) , ⟦ RHS ⟧ᵛ γ)
        ≡⟨ cong (λ x → ⟦ pair (wk-val (wk-wk wk-id) (var h)) (var h) ⟧ᵛ ((γ ,  ⟦ M₁ ⟧ᵛ γ₁) , x)) R≡M ⟩
          ⟦ pair (wk-val (wk-wk wk-id) (var h)) (var h) ⟧ᵛ ((γ ,  ⟦ M₁ ⟧ᵛ γ₁) , ⟦ M₂ ⟧ᵛ γ₂) ∎
        )

eval (pm {A = X} {B = Y} M N) γ with eval M γ
... | steps {T = ∙ ((⇡ pair LHS RHS ⹁ γ₁ ∷ □) {gt = ↓})} M>T _ M≡T with eval N ((γ , ⟦ LHS ⟧ᵛ γ₁) , ⟦ RHS ⟧ᵛ γ₁)
...     | steps {T = ∙ ((⇡ N' ⹁ γ₂ ∷ □) {gt = ↓})} N>T ∙T N≡T  = --{!!}

  steps (
          ∘ ⇡ pm M N ⹁ γ ∷ □ →ᵛᵛ⟨ ∘pm ⟩ ⨾ -- ∘ ⇡ M ⹁ γ ∷ ⇡ᴹ M N ⹁ γ ∷ □
          ⟪ M>T ⟫∷ ((⇡ᴹ M N ⹁ γ ∷ □) {gt = ↓}) ⨾
          ∙ ⇡ pair LHS RHS ⹁ γ₁ ∷ ⇡ᴹ M N ⹁ γ ∷ □ →ᵛᵛ⟨ ∙pair∷pm ⟩ ⨾ -- ∘ ⇡ N ⹁ ((γ , ⟦ LHS ⟧ᵛ γ₁) , ⟦ RHS ⟧ᵛ γ₁) ∷ □
          N>T
        )

        ∙T

        (
            ⟦ pm M N ⟧ᵛ γ
          ≡⟨ refl ⟩
            ⟦ N ⟧ᵛ (assocl (γ , ⟦ M ⟧ᵛ γ))
          ≡⟨ cong (λ x → ⟦ N ⟧ᵛ (assocl (γ , x))) M≡T  ⟩
            ⟦ N ⟧ᵛ (assocl (γ , ⟦ pair LHS RHS ⟧ᵛ γ₁))
          ≡⟨ N≡T ⟩
            ⟦ N' ⟧ᵛ γ₂ ∎
        )


-}
