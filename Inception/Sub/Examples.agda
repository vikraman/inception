module Inception.Sub.Examples where

open import Inception.Prelude
open import Inception.Rewriting
open import Inception.Sub.Syntax

open import Inception.Sub.Machine `𝟙

open import Data.Product using (_,_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open StarReasoning _→ᶜ_

ex15 : ε ⊢ᶜ (`𝟙)
ex15 = push (push (app (lam {X = `𝟙} (sub (var (var here)) (return unit))) unit) (return unit)) (return unit)

_ : exec ex15 ≡ (_ , unitᵛ , _ ,
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
