module Inception.Sub.VVmachine (R : Set) where

open import Function.Base using (id)
open import Data.Product using (proj₁; proj₂; _,_; Σ; ∃; Σ-syntax; ∃-syntax)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; sym)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit

variable
  A' B' C' D' X Y Z X' Y' Z' X₁ Y₁ Z₁ X₂ Y₂ Z₂ X◾ Y◾ Z◾ X↓ Y↓ Z↓ T◾ T◾' T◾₁ T◾₂ : Ty
  Γ' Γ'' Γ''' Δ' Γ₁ Γ₂ Γ◾ Γ↓ : Ctx

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
     b b' : Bool


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

     ∘var   : {γ : ⟦ Γ ⟧ˣ} → {i : Γ ∋ X} → {tail : vStack b T◾} → {gt : goodType b X T◾} → ∘ (_⹁_∷_ (⇡ var i) γ tail {gt = gt}) →ᵛᵛ ∙ (_⹁_∷_ (⇡ var i) γ tail {gt = gt})

     ∘lam : {γ : ⟦ Γ ⟧ˣ} → {M : (Γ ∙ X) ⊢ᶜ Y} → {tail : vStack b T◾} → {gt : goodType b (X `⇒ Y) T◾} → ∘ (_⹁_∷_ (⇡ lam M) γ tail {gt = gt}) →ᵛᵛ ∙ (_⹁_∷_ (⇡ lam M) γ tail {gt = gt})

     ∘pair : {γ : ⟦ Γ ⟧ˣ} → {LHS : Γ ⊢ᵛ X} → {RHS : Γ ⊢ᵛ Y} → {tail : vStack b T◾} → {gt : goodType b (X `× Y) T◾} → ∘ ((⇡ pair LHS RHS ⹁ γ ∷ tail) {gt = gt}) →ᵛᵛ ∘ ((⇡ LHS ⹁ γ ∷ ((⇡ᴸ LHS RHS ⹁ γ ∷ tail) {gt = gt})) {gt = ↕})

     ∘pm : {γ : ⟦ Γ ⟧ˣ} → {M : Γ ⊢ᵛ X `× Y} → {N : (Γ ∙ X ∙ Y) ⊢ᵛ Z} → {tail : vStack b T◾} → {gt : goodType b Z T◾} → ∘ ((⇡ pm M N ⹁ γ ∷ tail) {gt = gt}) →ᵛᵛ ∘ ((⇡ M ⹁ γ ∷ (⇡ᴹ M N ⹁ γ ∷ tail) {gt = gt}) {gt = ↕})

     ∘unit : {γ : ⟦ Γ ⟧ˣ} → {tail : vStack b T◾} → {gt : goodType b `Unit T◾} → ∘ ((⇡ unit ⹁ γ ∷ tail) {gt = gt}) →ᵛᵛ ∙ ((⇡ unit ⹁ γ ∷ tail) {gt = gt})

     ∙M∷pm : {γ : ⟦ Γ ⟧ˣ} → {γ' : ⟦ Γ' ⟧ˣ} → {M₂ : Γ ⊢ᵛ X `× Y} → {M : Γ' ⊢ᵛ X `× Y} → {N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z'} → {tail : vStack b T◾} → {gt : goodType b Z' T◾}
                 →    ∙ ((⇡ M₂ ⹁ γ ∷ ((⇡ᴹ M N ⹁ γ' ∷ tail) {gt = gt})) {gt = ↕}) →ᵛᵛ ∘ ((⇡ N ⹁ ((γ' , proj₁ (⟦ M₂ ⟧ᵛ γ)) , proj₂ (⟦ M₂ ⟧ᵛ γ)) ∷ tail) {gt = gt})

     ∙M∷l : {γ : ⟦ Γ ⟧ˣ} → {γ' : ⟦ Γ' ⟧ˣ} → {M : Γ ⊢ᵛ X} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y} → {tail : vStack b T◾} → {gt : goodType b (X `× Y) T◾}
                 →    ∙ ((⇡ M ⹁ γ ∷ ((⇡ᴸ LHS RHS ⹁ γ' ∷ tail) {gt = gt})) {gt = ↕}) →ᵛᵛ ∘ ((⇡ RHS ⹁ γ' ∷ ((⇡ᴿ (var h) (wk-val (wk-wk wk-id) RHS) ⹁ (γ' ,  ⟦ M ⟧ᵛ γ) ∷ tail) {gt = gt})) {gt = ↕})

     ∙M∷r : {γ : ⟦ Γ ⟧ˣ} → {γ' : ⟦ Γ' ⟧ˣ} → {M : Γ ⊢ᵛ Y} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y} → {tail : vStack b T◾} → {gt : goodType b (X `× Y) T◾}
                 →   ∙ ((⇡ M ⹁ γ ∷ ((⇡ᴿ LHS RHS ⹁ γ' ∷ tail) {gt = gt})) {gt = ↕}) →ᵛᵛ ∙ ((⇡ pair (wk-val (wk-wk wk-id) LHS) (var h) ⹁ (γ' , ⟦ M ⟧ᵛ γ) ∷ tail) {gt = gt})


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
⟨ ∙M∷pm ⟩∷ tail = ∙M∷pm
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

     ∙var_⹁_■ : (i : Γ ∋ X) → (γ : ⟦ Γ ⟧ˣ) → vHaltingState (∙ ((⇡ var i ⹁ γ ∷ □) {gt = ↓}))

     ∙unit⹁_■ : (γ : ⟦ Γ ⟧ˣ) → vHaltingState (∙ ((⇡ unit ⹁ γ ∷ □) {gt = ↓}))

     ∙pair[_⹁_]⹁_■ : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → (γ : ⟦ Γ ⟧ˣ) → vHaltingState (∙ ((⇡ pair LHS RHS ⹁ γ ∷ □) {gt = ↓}))

     ∙lam_⹁_■ : (M : (Γ ∙ X) ⊢ᶜ Y) → (γ : ⟦ Γ ⟧ˣ) → vHaltingState (∙ ((⇡ lam M ⹁ γ ∷ □) {gt = ↓}))


data correctSteps : vState T◾ → Set where

  steps : {S T : vState T◾} → S ↠ᵛᵛ T → vHaltingState T → ⟦ S ⟧◑ ≡ ⟦ T ⟧◑ → correctSteps S


eval : (M : Γ ⊢ᵛ X) → (γ : ⟦ Γ ⟧ˣ) → correctSteps {T◾ = X} (∘ ((⇡ M ⹁ γ ∷ □) {gt = ↓}))

eval (var i) γ = steps (∘ ⇡ var i ⹁ γ ∷ □ →ᵛᵛ⟨ ∘var ⟩) (∙var i ⹁ γ ■) refl
eval (lam M) γ = steps (∘ ⇡ lam M ⹁ γ ∷ □ →ᵛᵛ⟨ ∘lam ⟩) (∙lam M ⹁ γ ■) refl
eval unit γ = steps (∘ ⇡ unit ⹁ γ ∷ □ →ᵛᵛ⟨ ∘unit ⟩) (∙unit⹁ γ ■) refl

eval {X = X `× Y} (pair LHS RHS) γ with eval {X = X} LHS γ | eval RHS γ
... | steps {T = ∙ ((⇡ M₁ ⹁ γ₁ ∷ □) {gt = ↓})} L>T _ L≡M | steps {T = ∙ ((⇡ M₂ ⹁ γ₂ ∷ □) {gt = ↓})} R>T _ R≡M =

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

eval (pm {A = X} {B = Y} M N) γ with eval {X = X `× Y} M γ
... | steps {T = ∙ ((⇡ M' ⹁ γ₁ ∷ □) {gt = ↓})} M>T _ M≡T with eval N ((γ , proj₁ (⟦ M' ⟧ᵛ γ₁)) , proj₂ (⟦ M' ⟧ᵛ γ₁))
...     | steps {T = ∙ ((⇡ N' ⹁ γ₂ ∷ □) {gt = ↓})} N>T ∙T N≡T  =

                  steps (
                         ∘ ⇡ pm M N ⹁ γ ∷ □ →ᵛᵛ⟨ ∘pm ⟩ ⨾ -- ∘ ⇡ M ⹁ γ ∷ ⇡ᴹ M N ⹁ γ ∷ □
                         ⟪ M>T ⟫∷ ((⇡ᴹ M N ⹁ γ ∷ □) {gt = ↓}) ⨾
                         ∙ ⇡ M' ⹁ γ₁ ∷ ⇡ᴹ M N ⹁ γ ∷ □ →ᵛᵛ⟨ ∙M∷pm ⟩ ⨾ -- ∘ ((⇡ N ⹁ ((γ , proj₁ (⟦ M' ⟧ᵛ γ₁)) , proj₂ (⟦ M' ⟧ᵛ γ₁)) ∷ □) {gt = gt})
                         N>T
                        )

                        ∙T

                        (
                           ⟦ pm M N ⟧ᵛ γ
                         ≡⟨ refl ⟩
                           ⟦ N ⟧ᵛ (assocl (γ , ⟦ M ⟧ᵛ γ))
                         ≡⟨ cong (λ x → ⟦ N ⟧ᵛ (assocl (γ , x))) M≡T  ⟩
                           ⟦ N ⟧ᵛ (assocl (γ , ⟦ M' ⟧ᵛ γ₁))
                         ≡⟨ N≡T ⟩
                           ⟦ N' ⟧ᵛ γ₂ ∎
                        )

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
