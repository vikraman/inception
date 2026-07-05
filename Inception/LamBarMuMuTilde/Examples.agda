module Inception.LamBarMuMuTilde.Examples where

open import Inception.LamBarMuMuTilde.Syntax

`efq : (ε ∙ `⊥) ⊢ (ε ∙ A)
`efq = cut `⊥ (ret (var z)) tp

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

-- classical logic

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
