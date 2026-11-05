module Inception.Sub.Examples where

open import Inception.Prelude
open import Inception.Rewriting
open import Inception.Sub.Syntax

open import Inception.Sub.Machine `𝟙 renaming (_→ᶜ_ to _→ᴹ_; exec to execᴹ)
import Inception.Sub.TelescopeMachine `𝟙 as TM
open TM renaming (_→ᶜ_ to _→ᵀᴹ_)
import Inception.Sub.GCMachine `𝟙 as GCM
open GCM renaming (_→ᶜ_ to _→ᴳ_)
open import Inception.Sub.Simulation `𝟙

open import Data.Product using (_,_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

ex15 : ε ⊢ᶜ (`𝟙)
ex15 = push (push (app (lam {X = `𝟙} (sub (var (var here)) (return unit))) unit) (return unit)) (return unit)

module Mexamples where

  open StarReasoning _→ᴹ_

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

module TMexamples where

  open StarReasoning _→ᵀᴹ_
  open Reduction _→ᵀᴹ_ renaming (_~>*_ to _→ᵀᴹ*_)

  _ : (execᵀᴹ ex15) ≡ (_ , _ , (push→ ◅ push→ ◅ app→ ◅ sub→ ◅ var→ ◅ eval→ ◅ return→ ◅ eval→ ◅ return→ ◅ eval→ ◅ ε))
  _ = refl

  _ : (execᵀᴹ ex15) ≡ (TM.⟨ unit ； ⋄ · unit · unit · unit ╎ wk-wk (wk-wk (wk-wk wk-ε)) ╎ ◻ ⟩ , _ , (begin
                 TM.⟨ ex15 ╎ ⋄ ╎ wk-ε ╎ TM.◻ ⟩
      ⟶⟨ push→ ⟩ TM.⟨ push (app (lam (sub (var (var here)) (return unit))) unit) (return unit) ╎ ⋄ ╎ wk-id ╎ TM.< return unit ； ⋄ ； wk-ε >∷ ◻ ⟩
      ⟶⟨ push→ ⟩ TM.⟨ app (lam (sub (var (var here)) (return unit))) unit ╎ ⋄ ╎ wk-id ╎ TM.< return unit ； ⋄ ； wk-id >∷ (TM.< return unit ； ⋄ ； wk-ε >∷ ◻) ⟩
      ⟶⟨ app→ ⟩ TM.⟨ sub (var (var here)) (return unit) ╎ ⋄ · TM.eval unit ⋄ ╎ wk-wk wk-id ╎ TM.< return unit ； ⋄ ； wk-id >∷ (TM.< return unit ； ⋄ ； wk-ε >∷ ◻) ⟩
      ⟶⟨ sub→ ⟩ TM.⟨ var (var here) ╎ ⋄ · TM.eval unit ⋄ ·﹝ return unit ╎ wk-wk wk-id ╎ TM.< return unit ； ⋄ ； wk-id >∷ (TM.< return unit ； ⋄ ； wk-ε >∷ ◻) ﹞ ╎ wk-wk (wk-wk wk-id) ╎ TM.< return unit ； ⋄ ； wk-id >∷ (TM.< return unit ； ⋄ ； wk-ε >∷ ◻) ⟩
      ⟶⟨ var→ ⟩ TM.⟨ return unit ╎ ⋄ · TM.eval unit ⋄ ╎ wk-wk wk-id ╎ TM.< return unit ； ⋄ ； wk-id >∷ (TM.< return unit ； ⋄ ； wk-ε >∷ ◻) ⟩
      ⟶⟨ eval→ ⟩ TM.⟨ TM.eval unit (⋄ · TM.eval unit ⋄) ； ⋄ · TM.eval unit ⋄ ╎ wk-wk wk-id ╎ TM.< return unit ； ⋄ ； wk-id >∷ (TM.< return unit ； ⋄ ； wk-ε >∷ ◻) ⟩
      ⟶⟨ return→ ⟩ TM.⟨ return (wk-val (wk-cong (wk-wk wk-id)) unit) ╎ ⋄ · TM.eval unit ⋄ · TM.eval unit (⋄ · TM.eval unit ⋄) ╎ wk-wk (wk-trans (wk-wk wk-id) wk-id) ╎ TM.< return unit ； ⋄ ； wk-ε >∷ ◻ ⟩
      ⟶⟨ eval→ ⟩ TM.⟨ TM.eval (wk-val (wk-cong (wk-wk wk-id)) unit) (⋄ · TM.eval unit ⋄ · TM.eval unit (⋄ · TM.eval unit ⋄)) ； ⋄ · TM.eval unit ⋄ · TM.eval unit (⋄ · TM.eval unit ⋄) ╎ wk-wk (wk-trans (wk-wk wk-id) wk-id) ╎ TM.< return unit ； ⋄ ； wk-ε >∷ ◻ ⟩
      ⟶⟨ return→ ⟩ ⟨ return (wk-val (wk-cong (wk-wk (wk-trans (wk-wk wk-id) wk-id))) unit) ╎ ⋄ · TM.eval unit ⋄ · TM.eval unit (⋄ · TM.eval unit ⋄) · TM.eval (wk-val (wk-cong (wk-wk wk-id)) unit) (⋄ · TM.eval unit ⋄ · TM.eval unit (⋄ · TM.eval unit ⋄)) ╎ wk-wk (wk-trans (wk-wk (wk-trans (wk-wk wk-id) wk-id)) wk-ε) ╎ ◻ ⟩
      ⟶⟨ eval→ ⟩ TM.⟨ TM.eval (wk-val (wk-cong (wk-wk (wk-trans (wk-wk wk-id) wk-id))) unit) (⋄ · TM.eval unit ⋄ · TM.eval unit (⋄ · TM.eval unit ⋄) · TM.eval (wk-val (wk-cong (wk-wk wk-id)) unit) (⋄ · TM.eval unit ⋄ · TM.eval unit (⋄ · TM.eval unit ⋄))) ； ⋄ · TM.eval unit ⋄ · TM.eval unit (⋄ · TM.eval unit ⋄) · TM.eval (wk-val (wk-cong (wk-wk wk-id)) unit) (⋄ · TM.eval unit ⋄ · TM.eval unit (⋄ · TM.eval unit ⋄)) ╎ wk-wk (wk-trans (wk-wk (wk-trans (wk-wk wk-id) wk-id)) wk-ε) ╎ ◻ ⟩ ∎ ))
  _ = refl

module GCMexamples where

  open StarReasoning _→ᴳ_
  open Reduction _→ᴳ_ renaming (_~>*_ to _→ᴳ*_)

  _ = begin             ⟨ ⋄ ╎ ex15 ╎ wkext-ε ╎ ◻ ⟩
      ⟶⟨ push→ ⟩        ⟨ ⋄ ╎ push (app (lam (sub (var (var here)) (return unit))) unit) (return unit) ╎ wkext-id-π ╎ < return unit ； wkext-ε >∷ ◻ ⟩
      ⟶⟨ push→ ⟩        ⟨ ⋄ ╎ app (lam (sub (var (var here)) (return unit))) unit ╎ wkext-id-π ╎ < return unit ； wkext-id-π >∷ (< return unit ； wkext-ε >∷ ◻) ⟩
      ⟶⟨ app→ ⟩         ⟨ ⋄ · unit ╎ sub (var (var here)) (return unit) ╎ wkext-wk wkext-id ╎ < return unit ； wkext-id-π >∷ (< return unit ； wkext-ε >∷ ◻) ⟩
      ⟶⟨ sub→ ⟩         ⟨ ⋄ · unit ·﹝ return unit ╎ wkext-wk wkext-id ╎ < return unit ； wkext-id-π >∷ (< return unit ； wkext-ε >∷ ◻) ﹞ ╎ var (var here) ╎ wkext-wk (wkext-wk wkext-id) ╎ < return unit ； wkext-id-π >∷ (< return unit ； wkext-ε >∷ ◻) ⟩
      ⟶⟨ var→ ⟩         ⟨ ⋄ · unit ╎ return unit ╎ wkext-wk wkext-id ╎ < return unit ； wkext-id-π >∷ (< return unit ； wkext-ε >∷ ◻) ⟩
      ⟶⟨ eval→ ⟩    GCM.⟨ ⋄ ； unit ╎ wkext-id ╎ < return unit ； wkext-id >∷ (< return unit ； wkext-id >∷ ◻) ⟩
      ⟶⟨ return→ ⟩      ⟨ ⋄ · unit ╎ return (wk-val (wk-cong wk-ε) unit) ╎ wkext-wk wkext-id ╎ < return unit ； wkext-id >∷ ◻ ⟩
      ⟶⟨ eval→ ⟩    GCM.⟨ ⋄ ； unit ╎ wkext-id ╎ < return unit ； wkext-id >∷ ◻ ⟩
      ⟶⟨ return→ ⟩      ⟨ ⋄ · unit ╎ return (wk-val (wk-cong wk-ε) unit) ╎ wkext-wk wkext-id ╎ ◻ ⟩
      ⟶⟨ eval→ ⟩    GCM.⟨ ⋄ ； unit ╎ wkext-id ╎ ◻ ⟩ ∎

  -- _ : (execᴳ-quick ex15) ≡ (GCM.⟨ ⋄ ； unit ╎ wkext-ε ╎ ◻ ⟩ , (push→ ◅ push→ ◅ app→ ◅ sub→ ◅ var→ ◅ eval→ ◅ return→ ◅ eval→ ◅ return→ ◅ eval→ ◅ ε))
  -- _ = refl
