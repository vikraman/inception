module Inception.LamBarMuMuTilde.Examples where

open import Inception.LamBarMuMuTilde.Syntax

`efq : (ε ∙ `⊥) ⊢ (ε ∙ A)
`efq = cut `⊥ (ret (var z)) tp

`dne : ε ⊢ᵗ ¬ (¬ A) `⇒ A ∣ ε
`dne {A = A} =
  ret (lam (μ (cut (¬ (¬ A))
                   (ret (var z))
                   (app (lam (μ (cut A
                                     (ret (var z))
                                     (covar (s z)))))
                        tp))))

`lem : ε ⊢ᵗ (A `+ ¬ A) ∣ ε
`lem {A = A} =
  μ (cut (A `+ ¬ A)
         (ret (inr (lam (μ (cut (A `+ ¬ A)
                                (ret (inl (var z)))
                                (covar (s z)))))))
         (covar z))

`peirce : ε ⊢ᵗ ((A `⇒ B) `⇒ A) `⇒ A ∣ ε
`peirce {A = A} {B = B} =
  ret (lam (μ (cut ((A `⇒ B) `⇒ A)
                   (ret (var z))
                   (app (lam (μ (cut A
                                     (ret (var z))
                                     (covar (s z)))))
                        (covar z)))))

`callcc : ε ⊢ᵗ (¬ A `⇒ A) `⇒ A ∣ ε
`callcc {A = A} =
  ret (lam (μ (cut (¬ A `⇒ A)
                   (ret (var z))
                   (app (lam (μ (cut A
                                     (ret (var z))
                                     (covar (s z)))))
                        (covar z)))))

`letcc : (Γ ∙ ¬ A) ⊢ᵗ A ∣ Δ -> Γ ⊢ᵗ A ∣ Δ
`letcc {A = A} t =
  lett (wk-tm wk-emp wk-emp `callcc)
       (μ (cut ((¬ A `⇒ A) `⇒ A)
               (ret (var z))
               (app (wk-val (wk-wk wk-id) (wk-wk wk-id) (lam t))
                    (covar z))))

`throw : (ε ∙ A ∙ ¬ A) ⊢ᵗ B ∣ ε
`throw {A = A} {B = B} =
  μ (cut (¬ A)
         (ret (var z))
         (app (var (s z)) tp))

`abort : Γ ⊢ᵗ ¬ A ∣ Δ -> Γ ⊢ᵗ A ∣ Δ -> Γ ⊢ᵗ B ∣ Δ
`abort {A = A} {B = B} t1 t2 =
  lett t1
       (lett (wkᵗ t2)
             (μ (cut (¬ A)
                     (ret (var (s z)))
                     (app (var z) tp))))

`var : ε ⊢ᵗ `⊥ `⇒ A ∣ ε
`var = ret (lam (μ `efq))

`varr : Γ ⊢ᵗ `⊥ ∣ Δ -> Γ ⊢ᵗ A ∣ Δ
`varr t = μ (cut `⊥ (wk̃ᵗ t) tp)

`sub : (ε ∙ (`⊥ `⇒ A) ∙ A)  ⊢ᵗ A ∣ ε
`sub {A = A} =
  μ (cut (`⊥ `⇒ A)
         (ret (var (s z)))
         (μ̃ (cut A
                 (ret (var (s z)))
                 (covar z))))

`subb : (Γ ∙ `⊥) ⊢ᵗ A ∣ Δ -> Γ ⊢ᵗ A ∣ Δ -> Γ ⊢ᵗ A ∣ Δ
`subb {A = A} t1 t2 =
  μ (cut (`⊥ `⇒ A) (ret (lam (wk̃ᵗ t1)))
         (μ̃ (cut A
                 (wkᵗ (wk̃ᵗ t2))
                 (covar z))))


---
open import Inception.Sub.Machine using (ex15)
open import Inception.Sub.Translation using (⟦_⟧ᶜ)
open import Inception.LamBarMuMuTilde.SN
open import Inception.Prelude
open Inception.Prelude.RTC
open import Relation.Binary.PropositionalEquality

ex15-tr : ε ⊢ᵗ `Unit ∣ (ε ∙ `Unit)
ex15-tr = ⟦ ex15 ⟧ᶜ

ex15-cmd : ε ⊢ (ε ∙ `Unit)
ex15-cmd = cut `Unit ex15-tr (covar z)

ex15-trace : ex15-cmd ↦* cut `Unit (ret unit) (covar z)
ex15-trace = eval ex15-cmd .proj₂ .proj₁

_ : ex15-trace ≡ (
    cut `Unit (μ (cut `Unit (μ (cut `Unit (μ (cut (`Unit `⇒ `Unit) (ret (lam (μ (cut `Unit (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (covar (s (s z))))))) (μ̃ (cut `Unit (μ (cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (var z)) (app unit (covar z)))) tp)) (covar z))))) (covar z))))) (μ̃ (cut `Unit (μ (cut `Unit (ret unit) (μ̃ (cut `Unit (μ (cut (`Unit `⇒ `Unit) (ret (var (s z))) (app (var z) (covar z)))) (covar z))))) (covar z))))) (μ̃ (cut `Unit (ret unit) (covar z))))) (μ̃ (cut `Unit (ret unit) (covar z))))) (covar z)
  ~>⟨ μ-step ⟩
    cut `Unit (μ (cut `Unit (μ (cut (`Unit `⇒ `Unit) (ret (lam (μ (cut `Unit (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (covar (s (s z))))))) (μ̃ (cut `Unit (μ (cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (var z)) (app unit (covar z)))) tp)) (covar z))))) (covar z))))) (μ̃ (cut `Unit (μ (cut `Unit (ret unit) (μ̃ (cut `Unit (μ (cut (`Unit `⇒ `Unit) (ret (var (s z))) (app (var z) (covar z)))) (covar z))))) (covar z))))) (μ̃ (cut `Unit (ret unit) (covar z))))) (μ̃ (cut `Unit (ret unit) (covar z)))
  ~>⟨ μ-step ⟩
    cut `Unit (μ (cut (`Unit `⇒ `Unit) (ret (lam (μ (cut `Unit (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (covar (s (s z))))))) (μ̃ (cut `Unit (μ (cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (var z)) (app unit (covar z)))) tp)) (covar z))))) (covar z))))) (μ̃ (cut `Unit (μ (cut `Unit (ret unit) (μ̃ (cut `Unit (μ (cut (`Unit `⇒ `Unit) (ret (var (s z))) (app (var z) (covar z)))) (covar z))))) (covar z))))) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar z)))))
  ~>⟨ μ-step ⟩
    cut (`Unit `⇒ `Unit) (ret (lam (μ (cut `Unit (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (covar (s (s z))))))) (μ̃ (cut `Unit (μ (cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (var z)) (app unit (covar z)))) tp)) (covar z))))) (covar z))))) (μ̃ (cut `Unit (μ (cut `Unit (ret unit) (μ̃ (cut `Unit (μ (cut (`Unit `⇒ `Unit) (ret (var (s z))) (app (var z) (covar z)))) (covar z))))) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar z)))))))
  ~>⟨ μ̃-step ⟩
    cut `Unit (μ (cut `Unit (ret unit) (μ̃ (cut `Unit (μ (cut (`Unit `⇒ `Unit) (ret (lam (μ (cut `Unit (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (covar (s (s z))))))) (μ̃ (cut `Unit (μ (cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (var z)) (app unit (covar z)))) tp)) (covar z))))) (covar z))))) (app (var z) (covar z)))) (covar z))))) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar z)))))
  ~>⟨ μ-step ⟩
    cut `Unit (ret unit) (μ̃ (cut `Unit (μ (cut (`Unit `⇒ `Unit) (ret (lam (μ (cut `Unit (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (covar (s (s z))))))) (μ̃ (cut `Unit (μ (cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (var z)) (app unit (covar z)))) tp)) (covar z))))) (covar z))))) (app (var z) (covar z)))) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar z)))))))
  ~>⟨ μ̃-step ⟩
    cut `Unit (μ (cut (`Unit `⇒ `Unit) (ret (lam (μ (cut `Unit (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (covar (s (s z))))))) (μ̃ (cut `Unit (μ (cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (var z)) (app unit (covar z)))) tp)) (covar z))))) (covar z))))) (app unit (covar z)))) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar z)))))
  ~>⟨ μ-step ⟩
    cut (`Unit `⇒ `Unit) (ret (lam (μ (cut `Unit (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (covar (s (s z))))))) (μ̃ (cut `Unit (μ (cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (var z)) (app unit (covar z)))) tp)) (covar z))))) (covar z))))) (app unit (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar z))))))
  ~>⟨ app-step ⟩
    cut `Unit (μ (cut `Unit (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (covar (s (s z))))))) (μ̃ (cut `Unit (μ (cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (var z)) (app unit (covar z)))) tp)) (covar z))))) (covar z))) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar z)))))
  ~>⟨ μ-step ⟩
    cut `Unit (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar (s (s z))))))))))) (μ̃ (cut `Unit (μ (cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (var z)) (app unit (covar z)))) tp)) (covar z))))) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar z)))))
  ~>⟨ μ-step ⟩
    cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar (s z)))))))))) (μ̃ (cut `Unit (μ (cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (var z)) (app unit (covar z)))) tp)) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar z)))))))
  ~>⟨ μ̃-step ⟩
    cut `Unit (μ (cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar (s (s (s z)))))))))))) (app unit (covar z)))) tp)) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar z)))))
  ~>⟨ μ-step ⟩
    cut `⊥ (μ (cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar (s (s z))))))))))) (app unit (covar z)))) tp
  ~>⟨ μ-step ⟩
    cut (`Unit `⇒ `⊥) (ret (lam (μ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar (s z)))))))))) (app unit tp)
  ~>⟨ app-step ⟩
    cut `⊥ (μ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar (s z)))))))) tp
  ~>⟨ μ-step ⟩
    cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar z)))))
  ~>⟨ μ̃-step ⟩
    cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar z)))
  ~>⟨ μ̃-step ⟩
    cut `Unit (ret unit) (covar z)
  ◼)
_ = refl


---
open import Inception.Sub.Syntax as S

ex16 : ε ⊢ᶜ `Unit
ex16 = push (return unit) (return unit)

ex16-tr : ε ⊢ᵗ `Unit ∣ (ε ∙ `Unit)
ex16-tr = ⟦ ex16 ⟧ᶜ

ex16-cmd : ε ⊢ (ε ∙ `Unit)
ex16-cmd = cut `Unit ex16-tr (covar z)

ex16-trace : ex16-cmd ↦* cut `Unit (ret unit) (covar z)
ex16-trace = eval ex16-cmd .proj₂ .proj₁

_ : ex16-trace ≡ (
    cut `Unit (μ (cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar z))))) (covar z)
  ~>⟨ μ-step ⟩
    cut `Unit (ret unit) (μ̃ (cut `Unit (ret unit) (covar z)))
  ~>⟨ μ̃-step ⟩
    cut `Unit (ret unit) (covar z)
  ◼)
_ = refl
