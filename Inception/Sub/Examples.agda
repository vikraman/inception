module Inception.Sub.Examples where

open import Inception.Prelude
open import Inception.Rewriting
open import Inception.Sub.Syntax

open import Inception.Sub.Machine `𝟙 renaming (_→ᶜ_ to _→ᴹ_; exec to execᴹ)
import Inception.Sub.TelescopeMachine `𝟙 as TM
open TM
open import Inception.Sub.Simulation `𝟙 renaming (exec to execᵀᴹ)

open import Data.Product using (_,_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open StarReasoning _→ᴹ_

ex15 : ε ⊢ᶜ (`𝟙)
ex15 = push (push (app (lam {X = `𝟙} (sub (var (var here)) (return unit))) unit) (return unit)) (return unit)

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

--_ : execᵀᴹ ex15 ≡ ( _ , _ , push→ ◅ push→ ◅ app→ ◅ sub→ ◅ var→ ◅ eval→ ◅ return→ ◅ eval→ ◅ return→ ◅ eval→ ◅ ε)
_ : proj₁ (execᵀᴹ ex15) ≡ TM.⟨ unit ； ⋄ · unit · unit · unit ╎ wk-wk (wk-wk (wk-wk wk-ε)) ╎ ◻ ⟩
_ = refl
