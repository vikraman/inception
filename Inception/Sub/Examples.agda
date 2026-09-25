module Inception.Sub.Examples where

open import Inception.Sub.Syntax
open import Inception.Sub.Machine `𝟙
open import Inception.Prelude
open Inception.Prelude.RTC renaming (_~>⟨_⟩_ to _→ᶜ⟨_⟩_)

open import Data.Product using (_,_)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

ex15 : ε ⊢ᶜ (`𝟙)
ex15 = push (push (app (lam {X = `𝟙} (sub (var (var here)) (return unit))) unit) (return unit)) (return unit)

_ : exec ex15 ≡ (_ , unitᵛ , _ ,
                  (⟨ push (push (app (lam (sub (var (var here)) (return unit))) unit) (return unit)) (return unit) ╎ ⋄ ╎ ◻ ⟩
    →ᶜ⟨ push→ ⟩   (⟨ push (app (lam (sub (var (var here)) (return unit))) unit) (return unit) ╎ ⋄ ╎ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ push→ ⟩   (⟨ app (lam (sub (var (var here)) (return unit))) unit ╎ ⋄ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ app→ ⟩    (⟨ sub (var (var here)) (return unit) ╎ ⋄ · unitᵛ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ sub→ ⟩    (⟨ var (var here) ╎ ⋄ · unitᵛ · jumpᵛ (return unit) (⋄ · unitᵛ) (< return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻) ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ var→ ⟩    (⟨ return unit ╎ ⋄ · unitᵛ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ eval→ ⟩ (⟨ unitᵛ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ return→ ⟩ (⟨ return unit ╎ ⋄ · unitᵛ ╎ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ eval→ ⟩ (⟨ unitᵛ ╎ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ return→ ⟩ (⟨ return unit ╎ ⋄ · unitᵛ ╎ ◻ ⟩
    →ᶜ⟨ eval→ ⟩ (⟨ unitᵛ ╎ ◻ ⟩ ◼)))))))))))
    , _)
_ = refl
