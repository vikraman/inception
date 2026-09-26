module Inception.SystemL.Examples where

open import Inception.SystemL.Syntax

`efq : (ε ∙ `⊥) ⊢ (ε ∙ A)
`efq = cut `⊥ (ret (var here)) tp

`dne : ε ⊢ᵗ ¬ (¬ A) `⇒ A ∣ ε
`dne {A = A} =
  ret (lam (μ (cut (¬ (¬ A))
                   (ret (var here))
                   (app (lam (μ (cut A
                                     (ret (var here))
                                     (covar (there here)))))
                        tp))))

`lem : ε ⊢ᵗ (A `+ ¬ A) ∣ ε
`lem {A = A} =
  μ (cut (A `+ ¬ A)
         (ret (inr (lam (μ (cut (A `+ ¬ A)
                                (ret (inl (var here)))
                                (covar (there here)))))))
         (covar here))

`peirce : ε ⊢ᵗ ((A `⇒ B) `⇒ A) `⇒ A ∣ ε
`peirce {A = A} {B = B} =
  ret (lam (μ (cut ((A `⇒ B) `⇒ A)
                   (ret (var here))
                   (app (lam (μ (cut A
                                     (ret (var here))
                                     (covar (there here)))))
                        (covar here)))))

`callcc : ε ⊢ᵗ (¬ A `⇒ A) `⇒ A ∣ ε
`callcc {A = A} =
  ret (lam (μ (cut (¬ A `⇒ A)
                   (ret (var here))
                   (app (lam (μ (cut A
                                     (ret (var here))
                                     (covar (there here)))))
                        (covar here)))))

`letcc : (Γ ∙ ¬ A) ⊢ᵗ A ∣ Δ -> Γ ⊢ᵗ A ∣ Δ
`letcc {A = A} t =
  lett (wk-tm wk-emp wk-emp `callcc)
       (μ (cut ((¬ A `⇒ A) `⇒ A)
               (ret (var here))
               (app (wk-val (wk-wk wk-id) (wk-wk wk-id) (lam t))
                    (covar here))))

`throw : (ε ∙ A ∙ ¬ A) ⊢ᵗ B ∣ ε
`throw {A = A} {B = B} =
  μ (cut (¬ A)
         (ret (var here))
         (app (var (there here)) tp))

`abort : Γ ⊢ᵗ ¬ A ∣ Δ -> Γ ⊢ᵗ A ∣ Δ -> Γ ⊢ᵗ B ∣ Δ
`abort {A = A} {B = B} t1 t2 =
  lett t1
       (lett (wkᵗ t2)
             (μ (cut (¬ A)
                     (ret (var (there here)))
                     (app (var here) tp))))

`var : ε ⊢ᵗ `⊥ `⇒ A ∣ ε
`var = ret (lam (μ `efq))

`varr : Γ ⊢ᵗ `⊥ ∣ Δ -> Γ ⊢ᵗ A ∣ Δ
`varr t = μ (cut `⊥ (wk̃ᵗ t) tp)

`sub : (ε ∙ (`⊥ `⇒ A) ∙ A)  ⊢ᵗ A ∣ ε
`sub {A = A} =
  μ (cut (`⊥ `⇒ A)
         (ret (var (there here)))
         (μ̃ (cut A
                 (ret (var (there here)))
                 (covar here))))

`subb : (Γ ∙ `⊥) ⊢ᵗ A ∣ Δ -> Γ ⊢ᵗ A ∣ Δ -> Γ ⊢ᵗ A ∣ Δ
`subb {A = A} t1 t2 =
  μ (cut (`⊥ `⇒ A) (ret (lam (wk̃ᵗ t1)))
         (μ̃ (cut A
                 (wkᵗ (wk̃ᵗ t2))
                 (covar here))))


---
open import Inception.Sub.Examples using (ex15)
open import Inception.Sub.Translation using (⟦_⟧ᶜ)
open import Inception.SystemL.SN
open import Inception.Prelude
open Inception.Prelude.RTC
open import Relation.Binary.PropositionalEquality

ex15-tr : ε ⊢ᵗ `Unit ∣ (ε ∙ `Unit)
ex15-tr = ⟦ ex15 ⟧ᶜ

ex15-cmd : ε ⊢ (ε ∙ `Unit)
ex15-cmd = cut `Unit ex15-tr (covar here)

ex15-trace : ex15-cmd ↦* cut `Unit (ret unit) (covar here)
ex15-trace = eval ex15-cmd .proj₂ .proj₁

_ : ex15-trace ≡ (
    cut `Unit (μ (cut `Unit (μ (cut `Unit (μ (cut (`Unit `⇒ `Unit) (ret (lam (μ (cut `Unit (μ (cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (covar (there (there (there here)))))))) (app unit (covar here)))) tp)) (covar here))))) (app unit (covar here)))) (μ̃ (cut `Unit (ret unit) (covar here))))) (μ̃ (cut `Unit (ret unit) (covar here))))) (covar here)
  ~>⟨ μ-step ⟩
    cut `Unit (μ (cut `Unit (μ (cut (`Unit `⇒ `Unit) (ret (lam (μ (cut `Unit (μ (cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (covar (there (there (there here)))))))) (app unit (covar here)))) tp)) (covar here))))) (app unit (covar here)))) (μ̃ (cut `Unit (ret unit) (covar here))))) (μ̃ (cut `Unit (ret unit) (covar here)))
  ~>⟨ μ-step ⟩
    cut `Unit (μ (cut (`Unit `⇒ `Unit) (ret (lam (μ (cut `Unit (μ (cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (covar (there (there (there here)))))))) (app unit (covar here)))) tp)) (covar here))))) (app unit (covar here)))) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar here)))))
  ~>⟨ μ-step ⟩
    cut (`Unit `⇒ `Unit) (ret (lam (μ (cut `Unit (μ (cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (covar (there (there (there here)))))))) (app unit (covar here)))) tp)) (covar here))))) (app unit (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar here))))))
  ~>⟨ app-step ⟩
    cut `Unit (μ (cut `Unit (μ (cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (covar (there (there (there here)))))))) (app unit (covar here)))) tp)) (covar here))) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar here)))))
  ~>⟨ μ-step ⟩
    cut `Unit (μ (cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar (there (there (there here)))))))))))) (app unit (covar here)))) tp)) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar here)))))
  ~>⟨ μ-step ⟩
    cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar (there (there here))))))))))) (app unit (covar here)))) tp
  ~>⟨ μ-step ⟩
    cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar (there here)))))))))) (app unit tp)
  ~>⟨ app-step ⟩
    cut `⊥ (μ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar (there here)))))))) tp
  ~>⟨ μ-step ⟩
    cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar here)))))
  ~>⟨ μ̃-step ⟩
    cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar here)))
  ~>⟨ μ̃-step ⟩
    cut `Unit (ret unit) (covar here)
  ◼)
_ = refl


---
open import Inception.Sub.Syntax as S hiding (ε; _∙_; here; there)

ex16 : S.ε ⊢ᶜ `Unit
ex16 = push (return unit) (return unit)

ex16-tr : ε ⊢ᵗ `Unit ∣ (ε ∙ `Unit)
ex16-tr = ⟦ ex16 ⟧ᶜ

ex16-cmd : ε ⊢ (ε ∙ `Unit)
ex16-cmd = cut `Unit ex16-tr (covar here)

ex16-trace : ex16-cmd ↦* cut `Unit (ret unit) (covar here)
ex16-trace = eval ex16-cmd .proj₂ .proj₁

_ : ex16-trace ≡ (
    cut `Unit (μ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar here))))) (covar here)
  ~>⟨ μ-step ⟩
    cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar here)))
  ~>⟨ μ̃-step ⟩
    cut `Unit (ret unit) (covar here)
  ◼)
_ = refl
