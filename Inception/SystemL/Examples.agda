module Inception.SystemL.Examples where

open import Inception.SystemL.Syntax

`efq : (ε ∙ `⊥) ⊢ (ε ∙ X)
`efq = cut `⊥ (ret (var here)) tp

`dne : ε ⊢ᵗ ¬ (¬ X) `⇒ X ∣ ε
`dne {X = X} =
  ret (lam (μ (cut (¬ (¬ X))
                   (ret (var here))
                   (app (lam (μ (cut X
                                     (ret (var here))
                                     (covar (there here)))))
                        tp))))

`lem : ε ⊢ᵗ (X `+ ¬ X) ∣ ε
`lem {X = X} =
  μ (cut (X `+ ¬ X)
         (ret (inr (lam (μ (cut (X `+ ¬ X)
                                (ret (inl (var here)))
                                (covar (there here)))))))
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
                   (app (lam (μ (cut X
                                     (ret (var here))
                                     (covar (there here)))))
                        (covar here)))))

`letcc : (Γ ∙ ¬ X) ⊢ᵗ X ∣ Δ -> Γ ⊢ᵗ X ∣ Δ
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
         (app (var (there here)) tp))

`abort : Γ ⊢ᵗ ¬ X ∣ Δ -> Γ ⊢ᵗ X ∣ Δ -> Γ ⊢ᵗ Y ∣ Δ
`abort {X = X} {Y = Y} M N =
  lett M
       (lett (wkᵗ N)
             (μ (cut (¬ X)
                     (ret (var (there here)))
                     (app (var here) tp))))

`var : ε ⊢ᵗ `⊥ `⇒ X ∣ ε
`var = ret (lam (μ `efq))

`varr : Γ ⊢ᵗ `⊥ ∣ Δ -> Γ ⊢ᵗ X ∣ Δ
`varr M = μ (cut `⊥ (wk̃ᵗ M) tp)

`sub : (ε ∙ (`⊥ `⇒ X) ∙ X)  ⊢ᵗ X ∣ ε
`sub {X = X} =
  μ (cut (`⊥ `⇒ X)
         (ret (var (there here)))
         (μ̃ (cut X
                 (ret (var (there here)))
                 (covar here))))

`subb : (Γ ∙ `⊥) ⊢ᵗ X ∣ Δ -> Γ ⊢ᵗ X ∣ Δ -> Γ ⊢ᵗ X ∣ Δ
`subb {X = X} M N =
  μ (cut (`⊥ `⇒ X) (ret (lam (wk̃ᵗ M)))
         (μ̃ (cut X
                 (wkᵗ (wk̃ᵗ N))
                 (covar here))))


---
open import Inception.Sub.Examples using (ex15)
open import Inception.Sub.Translation using (⟦_⟧ᶜ)
open import Inception.SystemL.SN
open import Inception.Prelude
open Inception.Prelude.RTC
open import Relation.Binary.PropositionalEquality

ex15-tr : ε ⊢ᵗ `𝟙 ∣ (ε ∙ `𝟙)
ex15-tr = ⟦ ex15 ⟧ᶜ

ex15-cmd : ε ⊢ (ε ∙ `𝟙)
ex15-cmd = cut `𝟙 ex15-tr (covar here)

ex15-trace : ex15-cmd ↦* cut `𝟙 (ret unit) (covar here)
ex15-trace = eval ex15-cmd .proj₂ .proj₁

_ : ex15-trace ≡ (
    cut `𝟙 (μ (cut `𝟙 (μ (cut `𝟙 (μ (cut (`𝟙 `⇒ `𝟙) (ret (lam (μ (cut `𝟙 (μ (cut `⊥ (μ (cut (`𝟙 `⇒ `⊥) (ret (lam (μ (cut `𝟙 (ret unit) (covar (there (there (there here)))))))) (app unit (covar here)))) tp)) (covar here))))) (app unit (covar here)))) (μ̃ (cut `𝟙 (ret unit) (covar here))))) (μ̃ (cut `𝟙 (ret unit) (covar here))))) (covar here)
  ~>⟨ μ-step ⟩
    cut `𝟙 (μ (cut `𝟙 (μ (cut (`𝟙 `⇒ `𝟙) (ret (lam (μ (cut `𝟙 (μ (cut `⊥ (μ (cut (`𝟙 `⇒ `⊥) (ret (lam (μ (cut `𝟙 (ret unit) (covar (there (there (there here)))))))) (app unit (covar here)))) tp)) (covar here))))) (app unit (covar here)))) (μ̃ (cut `𝟙 (ret unit) (covar here))))) (μ̃ (cut `𝟙 (ret unit) (covar here)))
  ~>⟨ μ-step ⟩
    cut `𝟙 (μ (cut (`𝟙 `⇒ `𝟙) (ret (lam (μ (cut `𝟙 (μ (cut `⊥ (μ (cut (`𝟙 `⇒ `⊥) (ret (lam (μ (cut `𝟙 (ret unit) (covar (there (there (there here)))))))) (app unit (covar here)))) tp)) (covar here))))) (app unit (covar here)))) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here)))))
  ~>⟨ μ-step ⟩
    cut (`𝟙 `⇒ `𝟙) (ret (lam (μ (cut `𝟙 (μ (cut `⊥ (μ (cut (`𝟙 `⇒ `⊥) (ret (lam (μ (cut `𝟙 (ret unit) (covar (there (there (there here)))))))) (app unit (covar here)))) tp)) (covar here))))) (app unit (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here))))))
  ~>⟨ app-step ⟩
    cut `𝟙 (μ (cut `𝟙 (μ (cut `⊥ (μ (cut (`𝟙 `⇒ `⊥) (ret (lam (μ (cut `𝟙 (ret unit) (covar (there (there (there here)))))))) (app unit (covar here)))) tp)) (covar here))) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here)))))
  ~>⟨ μ-step ⟩
    cut `𝟙 (μ (cut `⊥ (μ (cut (`𝟙 `⇒ `⊥) (ret (lam (μ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar (there (there (there here)))))))))))) (app unit (covar here)))) tp)) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here)))))
  ~>⟨ μ-step ⟩
    cut `⊥ (μ (cut (`𝟙 `⇒ `⊥) (ret (lam (μ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar (there (there here))))))))))) (app unit (covar here)))) tp
  ~>⟨ μ-step ⟩
    cut (`𝟙 `⇒ `⊥) (ret (lam (μ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar (there here)))))))))) (app unit tp)
  ~>⟨ app-step ⟩
    cut `⊥ (μ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar (there here)))))))) tp
  ~>⟨ μ-step ⟩
    cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here)))))
  ~>⟨ μ̃-step ⟩
    cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here)))
  ~>⟨ μ̃-step ⟩
    cut `𝟙 (ret unit) (covar here)
  ◼)
_ = refl


---
open import Inception.Sub.Syntax as S hiding (ε; _∙_; here; there)

ex16 : S.ε ⊢ᶜ `𝟙
ex16 = push (return unit) (return unit)

ex16-tr : ε ⊢ᵗ `𝟙 ∣ (ε ∙ `𝟙)
ex16-tr = ⟦ ex16 ⟧ᶜ

ex16-cmd : ε ⊢ (ε ∙ `𝟙)
ex16-cmd = cut `𝟙 ex16-tr (covar here)

ex16-trace : ex16-cmd ↦* cut `𝟙 (ret unit) (covar here)
ex16-trace = eval ex16-cmd .proj₂ .proj₁

_ : ex16-trace ≡ (
    cut `𝟙 (μ (cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here))))) (covar here)
  ~>⟨ μ-step ⟩
    cut `𝟙 (ret unit) (μ̃ (cut `𝟙 (ret unit) (covar here)))
  ~>⟨ μ̃-step ⟩
    cut `𝟙 (ret unit) (covar here)
  ◼)
_ = refl
