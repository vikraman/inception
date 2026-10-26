module Inception.Sub.Examples where

open import Inception.Prelude
open import Inception.Rewriting
open import Inception.Sub.Syntax

open import Inception.Sub.Machine `𝟙 renaming (_→ᶜ_ to _→ᴹ_; exec to execᴹ)
import Inception.Sub.TelescopeMachine `𝟙 as TM
open TM renaming (_→ᶜ_ to _→ᵀᴹ_)
open import Inception.Sub.Simulation `𝟙 renaming (exec to execᵀᴹ)

open import Data.Product using (_,_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--open StarReasoning _→ᴹ_

ex15 : ε ⊢ᶜ (`𝟙)
ex15 = push (push (app (lam {X = `𝟙} (sub (var (var here)) (return unit))) unit) (return unit)) (return unit)

{-
_ : execᴹ ex15 ≡ (_ , unitᵛ , _ ,
                  (begin ⟨ push (push (app (lam (sub (var (var here)) (return unit))) unit) (return unit)) (return unit) ╎ ⋄ ╎ ◻ ⟩
    ⟶⟨ push→ ⟩   ⟨ push (app (lam (sub (var (var here)) (return unit))) unit) (return unit) ╎ ⋄ ╎ < return unit ； ⋄ >∷ ◻ ⟩
    ⟶⟨ push→ ⟩   ⟨ app (lam (sub (var (var here)) (return unit))) unit ╎ ⋄ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    ⟶⟨ app→ ⟩    ⟨ sub (var (var here)) (return unit) ╎ ⋄ · unitᵛ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    ⟶⟨ sub→ ⟩    ⟨ var (var here) ╎ ⋄ · unitᵛ · jumpᵛ (return unit) (⋄ · unitᵛ) (< return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻) ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    ⟶⟨ var→ ⟩    ⟨ return unit ╎ ⋄ · unitᵛ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    ⟶⟨ eval→ ⟩ ⟨ unitᵛ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    ⟶⟨ return→ ⟩ ⟨ return unit ╎ ⋄ · unitᵛ ╎ < return unit ； ⋄ >∷ ◻ ⟩
    ⟶⟨ eval→ ⟩ ⟨ unitᵛ ╎ < return unit ； ⋄ >∷ ◻ ⟩
    ⟶⟨ return→ ⟩ ⟨ return unit ╎ ⋄ · unitᵛ ╎ ◻ ⟩
    ⟶⟨ eval→ ⟩ ⟨ unitᵛ ╎ ◻ ⟩ ∎)
    , _)
_ = refl
-}

--_ : execᵀᴹ ex15 ≡ ( _ , _ , push→ ◅ push→ ◅ app→ ◅ sub→ ◅ var→ ◅ eval→ ◅ return→ ◅ eval→ ◅ return→ ◅ eval→ ◅ ε)

open StarReasoning _→ᵀᴹ_
open Reduction _→ᵀᴹ_ renaming (_~>*_ to _→ᵀᴹ*_)

s :  ⟨ ex15 ╎ ⋄ ╎ wk-ε ╎ ◻ ⟩ →ᵀᴹ* _
s = begin      TM.⟨ ex15 ╎ ⋄ ╎ wk-ε ╎ TM.◻ ⟩
    ⟶⟨ push→ ⟩ TM.⟨ push (app (lam (sub (var (var here)) (return unit))) unit) (return unit) ╎ ⋄ ╎ wk-id ╎ TM.< return unit ； ⋄ ； wk-ε >∷ ◻ ⟩
    ⟶⟨ push→ ⟩ TM.⟨ app (lam (sub (var (var here)) (return unit))) unit ╎ ⋄ ╎ wk-id ╎ TM.< return unit ； ⋄ ； wk-id >∷ (TM.< return unit ； ⋄ ； wk-ε >∷ ◻) ⟩
    ⟶⟨ app→ ⟩ TM.⟨ sub (var (var here)) (return unit) ╎ ⋄ · TM.eval unit ⋄ ╎ wk-wk wk-id ╎ TM.< return unit ； ⋄ ； wk-id >∷ (TM.< return unit ； ⋄ ； wk-ε >∷ ◻) ⟩
    ⟶⟨ sub→ ⟩  TM.⟨ var (var here) ╎ (⋄ · TM.eval unit ⋄) ·﹝ return unit ╎ wk-wk wk-id ╎ TM.< return unit ； ⋄ ； wk-id >∷ (TM.< return unit ； ⋄ ； wk-ε >∷ ◻) ﹞ ╎ wk-wk (wk-wk wk-id) ╎ TM.< return unit ； ⋄ ； wk-id >∷ (TM.< return unit ； ⋄ ； wk-ε >∷ ◻) ⟩
    ⟶⟨ var→ ⟩ TM.⟨ return unit ╎ ⋄ · TM.eval unit ⋄ ╎ wk-wk wk-id ╎ TM.< return unit ； ⋄ ； wk-id >∷ (TM.< return unit ； ⋄ ； wk-ε >∷ ◻) ⟩
    ⟶⟨ eval→ ⟩ TM.⟨ TM.eval unit (⋄ · TM.eval unit ⋄) ； ⋄ · TM.eval unit ⋄ ╎ wk-wk wk-id ╎ TM.< return unit ； ⋄ ； wk-id >∷ (TM.< return unit ； ⋄ ； wk-ε >∷ ◻) ⟩
    ⟶⟨ return→ ⟩ TM.⟨ return (wk-val (wk-cong (wk-wk wk-id)) unit) ╎ ⋄ · TM.eval unit ⋄ · TM.eval unit (⋄ · TM.eval unit ⋄) ╎ wk-wk (wk-trans (wk-wk wk-id) wk-id) ╎ TM.< return unit ； ⋄ ； wk-ε >∷ ◻ ⟩
    ⟶⟨ eval→ ⟩ TM.⟨ TM.eval (wk-val (wk-cong (wk-wk wk-id)) unit) (⋄ · TM.eval unit ⋄ · TM.eval unit (⋄ · TM.eval unit ⋄)) ； ⋄ · TM.eval unit ⋄ · TM.eval unit (⋄ · TM.eval unit ⋄) ╎ wk-wk (wk-trans (wk-wk wk-id) wk-id) ╎ TM.< return unit ； ⋄ ； wk-ε >∷ ◻ ⟩
    ⟶⟨ return→ ⟩ TM.⟨ return (wk-val (wk-cong (wk-wk (wk-trans (wk-wk wk-id) wk-id))) unit) ╎ ⋄ · TM.eval unit ⋄ · TM.eval unit (⋄ · TM.eval unit ⋄) · TM.eval (wk-val (wk-cong (wk-wk wk-id)) unit) (⋄ · TM.eval unit ⋄ · TM.eval unit (⋄ · TM.eval unit ⋄)) ╎ wk-wk (wk-trans (wk-wk (wk-trans (wk-wk wk-id) wk-id)) wk-ε) ╎ ◻ ⟩
    ⟶⟨ eval→ ⟩ TM.⟨ TM.eval (wk-val (wk-cong (wk-wk (wk-trans (wk-wk wk-id) wk-id))) unit) (⋄ · TM.eval unit ⋄ · TM.eval unit (⋄ · TM.eval unit ⋄) · TM.eval (wk-val (wk-cong (wk-wk wk-id)) unit) (⋄ · TM.eval unit ⋄ · TM.eval unit (⋄ · TM.eval unit ⋄))) ； ⋄ · TM.eval unit ⋄ · TM.eval unit (⋄ · TM.eval unit ⋄) · TM.eval (wk-val (wk-cong (wk-wk wk-id)) unit) (⋄ · TM.eval unit ⋄ · TM.eval unit (⋄ · TM.eval unit ⋄)) ╎ wk-wk (wk-trans (wk-wk (wk-trans (wk-wk wk-id) wk-id)) wk-ε) ╎ ◻ ⟩
    ∎
--(push→ ◅ app→ ◅ sub→ ◅ var→ ◅ eval→ ◅ return→ ◅ eval→ ◅ return→ ◅ eval→ ◅ ε)

--_ : proj₁ (execᵀᴹ ex15) ≡ TM.⟨ unit ； ⋄ · unit · unit · unit ╎ wk-wk (wk-wk (wk-wk wk-ε)) ╎ ◻ ⟩
_ : proj₂ (proj₂ (execᵀᴹ ex15)) ≡ s
_ = refl
