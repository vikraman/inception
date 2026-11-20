module Inception.SystemL.Examples where

open import Inception.SystemL.Syntax

`efq : (ε ∙ `⊥) ⊢ (ε ∙ X)
`efq = cut `⊥ (ret (var here)) tp

`dne : ε ⊢ᵗ ¬ (¬ X) `⇒ X ∣ ε
`dne {X = X} =
  ret (lam (μ (cut (¬ (¬ X))
                   (ret (var here))
                   (pass (cont (covar here))))))

`lem : ε ⊢ᵗ (X `+ ¬ X) ∣ ε
`lem {X = X} =
  μ (cut (X `+ ¬ X)
         (ret (inr (cont (μ̃ (cut (X `+ ¬ X)
                                 (ret (inl (var here)))
                                 (covar here))))))
         (covar here))

`peirce : ε ⊢ᵗ ((X `⇒ Y) `⇒ X) `⇒ X ∣ ε
`peirce {X = X} {Y = Y} =
  ret (lam (μ (cut ((X `⇒ Y) `⇒ X)
                   (ret (var here))
                   (app (lam (μ (cut X
                                     (ret (var here))
                                     (covar (there here)))))
                        (covar here)))))

`callcc : ε ⊢ᵗ (¬ X `⇒ X) `⇒ X ∣ ε
`callcc {X = X} =
  ret (lam (μ (cut (¬ X `⇒ X)
                   (ret (var here))
                   (app (cont (covar here))
                        (covar here)))))

`letcc : (Γ ∙ ¬ X) ⊢ᵗ X ∣ Δ → Γ ⊢ᵗ X ∣ Δ
`letcc {X = X} M =
  lett (wk-tm wk-emp wk-emp `callcc)
       (μ (cut ((¬ X `⇒ X) `⇒ X)
               (ret (var here))
               (app (wk-val (wk-wk wk-id) (wk-wk wk-id) (lam M))
                    (covar here))))

`throw : (ε ∙ X ∙ ¬ X) ⊢ᵗ Y ∣ ε
`throw {X = X} {Y = Y} =
  μ (cut (¬ X)
         (ret (var here))
         (pass (var (there here))))

`abort : Γ ⊢ᵗ ¬ X ∣ Δ → Γ ⊢ᵗ X ∣ Δ → Γ ⊢ᵗ Y ∣ Δ
`abort {X = X} {Y = Y} M N =
  lett M
       (lett (wkᵗ N)
             (μ (cut (¬ X)
                     (ret (var (there here)))
                     (pass (var here)))))

`var : ε ⊢ᵗ `⊥ `⇒ X ∣ ε
`var = ret (lam (μ `efq))

`varr : Γ ⊢ᵗ `⊥ ∣ Δ → Γ ⊢ᵗ X ∣ Δ
`varr M = μ (cut `⊥ (wk̃ᵗ M) tp)

`sub : (ε ∙ (`⊥ `⇒ X) ∙ X)  ⊢ᵗ X ∣ ε
`sub {X = X} =
  μ (cut (`⊥ `⇒ X)
         (ret (var (there here)))
         (μ̃ (cut X
                 (ret (var (there here)))
                 (covar here))))

`subb : (Γ ∙ `⊥) ⊢ᵗ X ∣ Δ → Γ ⊢ᵗ X ∣ Δ → Γ ⊢ᵗ X ∣ Δ
`subb {X = X} M N =
  μ (cut (`⊥ `⇒ X) (ret (lam (wk̃ᵗ M)))
         (μ̃ (cut X
                 (wkᵗ (wk̃ᵗ N))
                 (covar here))))


---
open import Inception.Prelude
open import Inception.Rewriting
open import Inception.Sub.Examples using (ex15)
open import Inception.SystemL.SN
open import Inception.Translation.Sub.SystemL using (⟦_⟧ᶜ)

open StarReasoning (_↦_ {Γ = ε} {Δ = ε ∙ `𝟙})

ex15-tr : ε ⊢ᵗ `𝟙 ∣ (ε ∙ `𝟙)
ex15-tr = ⟦ ex15 ⟧ᶜ

ex15-cmd : ε ⊢ (ε ∙ `𝟙)
ex15-cmd = cut `𝟙 ex15-tr (covar here)

ex15-trace : ex15-cmd ↦* cut `𝟙 (ret unit) (covar here)
ex15-trace = eval ex15-cmd .proj₂ .proj₁

_ : ex15-trace ≡ (begin
    cut `𝟙 (μ (cut `𝟙 (μ (cut `𝟙 (μ (cut (`𝟙 `⇒ `𝟙) (ret (lam (μ (cut (`𝟙 `+ `𝟙) (μ (cut (¬ `𝟙) (ret (cont (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inl (var here))) (covar here))))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (inl unit)) (case (μ̃ (cut (¬ `𝟙) (ret (var (there here))) (pass (var here)))) (covar here)))) (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inr (var here))) (covar here))))))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (var here)) (case (μ̃ (cut `𝟙 (ret unit) (covar here))) (μ̃ (cut `𝟙 (ret (var here)) (covar here)))))) (covar here))))))) (app unit (covar here)))) (μ̃ (cut `𝟙 (ret unit) (covar here))))) (μ̃ (cut `𝟙 (ret unit) (covar here))))) (covar here)
  ⟶⟨ μ-step ⟩
    cut `𝟙 (μ (cut `𝟙 (μ (cut (`𝟙 `⇒ `𝟙) (ret (lam (μ (cut (`𝟙 `+ `𝟙) (μ (cut (¬ `𝟙) (ret (cont (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inl (var here))) (covar here))))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (inl unit)) (case (μ̃ (cut (¬ `𝟙) (ret (var (there here))) (pass (var here)))) (covar here)))) (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inr (var here))) (covar here))))))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (var here)) (case (μ̃ (cut `𝟙 (ret unit) (covar here))) (μ̃ (cut `𝟙 (ret (var here)) (covar here)))))) (covar here))))))) (app unit (covar here)))) (μ̃ (cut `𝟙 (ret unit) (covar here))))) (μ̃ (cut `𝟙 (ret unit) (covar here)))
  ⟶⟨ μ-step ⟩
    cut `𝟙 (μ (cut (`𝟙 `⇒ `𝟙) (ret (lam (μ (cut (`𝟙 `+ `𝟙) (μ (cut (¬ `𝟙) (ret (cont (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inl (var here))) (covar here))))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (inl unit)) (case (μ̃ (cut (¬ `𝟙) (ret (var (there here))) (pass (var here)))) (covar here)))) (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inr (var here))) (covar here))))))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (var here)) (case (μ̃ (cut `𝟙 (ret unit) (covar here))) (μ̃ (cut `𝟙 (ret (var here)) (covar here)))))) (covar here))))))) (app unit (covar here)))) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here)))))
  ⟶⟨ μ-step ⟩
    cut (`𝟙 `⇒ `𝟙) (ret (lam (μ (cut (`𝟙 `+ `𝟙) (μ (cut (¬ `𝟙) (ret (cont (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inl (var here))) (covar here))))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (inl unit)) (case (μ̃ (cut (¬ `𝟙) (ret (var (there here))) (pass (var here)))) (covar here)))) (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inr (var here))) (covar here))))))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (var here)) (case (μ̃ (cut `𝟙 (ret unit) (covar here))) (μ̃ (cut `𝟙 (ret (var here)) (covar here)))))) (covar here))))))) (app unit (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here))))))
  ⟶⟨ app-step ⟩
    cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (μ (cut (¬ `𝟙) (ret (cont (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inl (var here))) (covar here))))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (inl unit)) (case (μ̃ (cut (¬ `𝟙) (ret (var (there here))) (pass (var here)))) (covar here)))) (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inr (var here))) (covar here))))))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (var here)) (case (μ̃ (cut `𝟙 (ret unit) (covar here))) (μ̃ (cut `𝟙 (ret (var here)) (covar here)))))) (covar here))))) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here)))))
  ⟶⟨ μ-step ⟩
    cut (`𝟙 `+ `𝟙) (μ (cut (¬ `𝟙) (ret (cont (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inl (var here))) (covar here))))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (inl unit)) (case (μ̃ (cut (¬ `𝟙) (ret (var (there here))) (pass (var here)))) (covar here)))) (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inr (var here))) (covar here))))))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (var here)) (case (μ̃ (cut `𝟙 (ret unit) (covar here))) (μ̃ (cut `𝟙 (ret (var here)) (covar here)))))) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here)))))))
  ⟶⟨ μ-step ⟩
    cut (¬ `𝟙) (ret (cont (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inl (var here))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (var here)) (case (μ̃ (cut `𝟙 (ret unit) (covar here))) (μ̃ (cut `𝟙 (ret (var here)) (covar here)))))) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here))))))))))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (inl unit)) (case (μ̃ (cut (¬ `𝟙) (ret (var (there here))) (pass (var here)))) (covar here)))) (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inr (var here))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (var here)) (case (μ̃ (cut `𝟙 (ret unit) (covar here))) (μ̃ (cut `𝟙 (ret (var here)) (covar here)))))) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here)))))))))))
  ⟶⟨ μ̃-step ⟩
    cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (inl unit)) (case (μ̃ (cut (¬ `𝟙) (ret (cont (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inl (var here))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (var here)) (case (μ̃ (cut `𝟙 (ret unit) (covar here))) (μ̃ (cut `𝟙 (ret (var here)) (covar here)))))) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar (there here)))))))))))) (pass (var here)))) (covar here)))) (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inr (var here))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (var here)) (case (μ̃ (cut `𝟙 (ret unit) (covar here))) (μ̃ (cut `𝟙 (ret (var here)) (covar here)))))) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here)))))))))
  ⟶⟨ μ-step ⟩
    cut (`𝟙 `+ `𝟙) (ret (inl unit)) (case (μ̃ (cut (¬ `𝟙) (ret (cont (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inl (var here))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (var here)) (case (μ̃ (cut `𝟙 (ret unit) (covar here))) (μ̃ (cut `𝟙 (ret (var here)) (covar here)))))) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here))))))))))) (pass (var here)))) (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inr (var here))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (var here)) (case (μ̃ (cut `𝟙 (ret unit) (covar here))) (μ̃ (cut `𝟙 (ret (var here)) (covar here)))))) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here))))))))))
  ⟶⟨ inl-step ⟩
    cut `𝟙 (ret unit) (μ̃ (cut (¬ `𝟙) (ret (cont (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inl (var here))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (var here)) (case (μ̃ (cut `𝟙 (ret unit) (covar here))) (μ̃ (cut `𝟙 (ret (var here)) (covar here)))))) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here))))))))))) (pass (var here))))
  ⟶⟨ μ̃-step ⟩
    cut (¬ `𝟙) (ret (cont (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inl (var here))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (var here)) (case (μ̃ (cut `𝟙 (ret unit) (covar here))) (μ̃ (cut `𝟙 (ret (var here)) (covar here)))))) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here))))))))))) (pass unit)
  ⟶⟨ pass-step ⟩
    cut `𝟙 (ret unit) (μ̃ (cut (`𝟙 `+ `𝟙) (ret (inl (var here))) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (var here)) (case (μ̃ (cut `𝟙 (ret unit) (covar here))) (μ̃ (cut `𝟙 (ret (var here)) (covar here)))))) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here)))))))))
  ⟶⟨ μ̃-step ⟩
    cut (`𝟙 `+ `𝟙) (ret (inl unit)) (μ̃ (cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (var here)) (case (μ̃ (cut `𝟙 (ret unit) (covar here))) (μ̃ (cut `𝟙 (ret (var here)) (covar here)))))) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here)))))))
  ⟶⟨ μ̃-step ⟩
    cut `𝟙 (μ (cut (`𝟙 `+ `𝟙) (ret (inl unit)) (case (μ̃ (cut `𝟙 (ret unit) (covar here))) (μ̃ (cut `𝟙 (ret (var here)) (covar here)))))) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here)))))
  ⟶⟨ μ-step ⟩
    cut (`𝟙 `+ `𝟙) (ret (inl unit)) (case (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here))))))) (μ̃ (cut `𝟙 (ret (var here)) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here))))))))
  ⟶⟨ inl-step ⟩
    cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here)))))))
  ⟶⟨ μ̃-step ⟩
    cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here)))))
  ⟶⟨ μ̃-step ⟩
    cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here)))
  ⟶⟨ μ̃-step ⟩
    cut `𝟙 (ret unit) (covar here) ∎)
_ = refl


---
open import Inception.Sub.Syntax as S hiding (ε; _∙_; here; there; Subᵛ)

ex16 : S.ε ⊢ᶜ `𝟙
ex16 = push (return unit) (return unit)

ex16-tr : ε ⊢ᵗ `𝟙 ∣ (ε ∙ `𝟙)
ex16-tr = ⟦ ex16 ⟧ᶜ

ex16-cmd : ε ⊢ (ε ∙ `𝟙)
ex16-cmd = cut `𝟙 ex16-tr (covar here)

ex16-trace : ex16-cmd ↦* cut `𝟙 (ret unit) (covar here)
ex16-trace = eval ex16-cmd .proj₂ .proj₁

_ : ex16-trace ≡ (begin
    cut `𝟙 (μ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here))))) (covar here)
  ⟶⟨ μ-step ⟩
    cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here)))
  ⟶⟨ μ̃-step ⟩
    cut `𝟙 (ret unit) (covar here) ∎)
_ = refl
