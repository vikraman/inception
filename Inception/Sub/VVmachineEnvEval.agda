module Inception.Sub.VVmachineEnvEval (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R
open import Inception.Sub.VVmachineEnv R

open import Data.Unit

eval : (M : Γ ⊢ᵛ X) → {WK : Wk Γ ε} → (γ : Env ε Γ {WK = WK}) → correctSteps {T◾ = X} (∘ ((⇡ M ⹁ γ ∷ □) {gt = ↓}))

eval (var h) (s-val (var i) γ γ₁) = {!!}

eval (var h) (s-val (lam x) γ γ₁) = {!!}
eval (var h) (s-val (pair M M₁) γ γ₁) = {!!}
eval (var h) (s-val (pm M M₁) γ γ₁) = {!!}
eval (var h) (s-val unit γ γ₁) = {!!}

-- steps (∘ ⇡ var h ⹁ (s-val M γ γ₁) ∷ □ →ᵛᵛ⟨ ∘var (⟨ h ∥ s-val M γ γ₁ ⟩ ▣) ⟩) {!!} {!!}

eval (var (t i)) γ with lookup (t i) γ
... | steps i>>T HT i≡t = {!!}

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
