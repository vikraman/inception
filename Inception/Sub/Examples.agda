module Inception.Sub.Examples where

open import Inception.Prelude
open import Inception.Sub.Syntax

open import Inception.Sub.Machine `𝟙
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

ex16 : ε ⊢ᶜ (`𝟙)
ex16 = push {Y = `𝟙} (return (lam {X = `𝟙} (return unit))) (push {X = `𝟙} (push (app (var (here {Γ = ε})) unit) (return (var here))) (return unit))

_ : exec ex16 ≡ (⟨ unitᵛ ╎ ◻ ⟩ , unitᵛ , (λ ()) ,
                  ⟨ push (return (lam (return unit))) (push (push (app (var _∋_.here) unit) (return (var _∋_.here))) (return unit)) ╎ ⋄ ╎ ◻ ⟩
    →ᶜ⟨ push→ ⟩   ⟨ return (lam (return unit)) ╎ ⋄ ╎ < push (push (app (var _∋_.here) unit) (return (var _∋_.here))) (return unit) ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ eval→ ⟩   ⟨ cloᵛ (return unit) ⋄ ╎ < push (push (app (var _∋_.here) unit) (return (var _∋_.here))) (return unit) ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ return→ ⟩ ⟨ push (push (app (var _∋_.here) unit) (return (var _∋_.here))) (return unit) ╎ ⋄ · cloᵛ (return unit) ⋄ ╎ ◻ ⟩
    →ᶜ⟨ push→ ⟩   ⟨ push (app (var _∋_.here) unit) (return (var _∋_.here)) ╎ ⋄ · cloᵛ (return unit) ⋄ ╎ < return unit ； ⋄ · cloᵛ (return unit) ⋄ >∷ ◻ ⟩
    →ᶜ⟨ push→ ⟩   ⟨ app (var _∋_.here) unit ╎ ⋄ · cloᵛ (return unit) ⋄ ╎ < return (var _∋_.here) ； ⋄ · cloᵛ (return unit) ⋄ >∷ (< return unit ； ⋄ · cloᵛ (return unit) ⋄ >∷ ◻) ⟩
    →ᶜ⟨ app→ ⟩    ⟨ return unit ╎ ⋄ · unitᵛ ╎ < return (var _∋_.here) ； ⋄ · cloᵛ (return unit) ⋄ >∷ (< return unit ； ⋄ · cloᵛ (return unit) ⋄ >∷ ◻) ⟩
    →ᶜ⟨ eval→ ⟩   ⟨ unitᵛ ╎ < return (var _∋_.here) ； ⋄ · cloᵛ (return unit) ⋄ >∷ (< return unit ； ⋄ · cloᵛ (return unit) ⋄ >∷ ◻) ⟩
    →ᶜ⟨ return→ ⟩ ⟨ return (var _∋_.here) ╎ ⋄ · cloᵛ (return unit) ⋄ · unitᵛ ╎ < return unit ； ⋄ · cloᵛ (return unit) ⋄ >∷ ◻ ⟩
    →ᶜ⟨ eval→ ⟩   ⟨ unitᵛ ╎ < return unit ； ⋄ · cloᵛ (return unit) ⋄ >∷ ◻ ⟩
    →ᶜ⟨ return→ ⟩ ⟨ return unit ╎ ⋄ · cloᵛ (return unit) ⋄ · unitᵛ ╎ ◻ ⟩
    →ᶜ⟨ eval→ ⟩   ⟨ unitᵛ ╎ ◻ ⟩ ◼ , refl )
_ = refl

ex17 : ε ⊢ᶜ (`𝟙)
ex17 = push (return unit) (push {Y = `𝟙} (return (lam {X = `𝟙} (return unit))) (push {X = `𝟙} (return unit) (push (app (var (there here)) unit) (return (var here)))))

_ : exec ex17 ≡ (⟨ unitᵛ ╎ ◻ ⟩ , unitᵛ , (λ ()) ,
                  ⟨ push (return unit) (push (return (lam (return unit))) (push (return unit) (push (app (var (_∋_.there _∋_.here)) unit) (return (var _∋_.here))))) ╎ ⋄ ╎ ◻ ⟩
    →ᶜ⟨ push→ ⟩   ⟨ return unit ╎ ⋄ ╎ < push (return (lam (return unit))) (push (return unit) (push (app (var (_∋_.there _∋_.here)) unit) (return (var _∋_.here)))) ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ eval→ ⟩   ⟨ unitᵛ ╎ < push (return (lam (return unit))) (push (return unit) (push (app (var (_∋_.there _∋_.here)) unit) (return (var _∋_.here)))) ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ return→ ⟩ ⟨ push (return (lam (return unit))) (push (return unit) (push (app (var (_∋_.there _∋_.here)) unit) (return (var _∋_.here)))) ╎ ⋄ · unitᵛ ╎ ◻ ⟩
    →ᶜ⟨ push→ ⟩   ⟨ return (lam (return unit)) ╎ ⋄ · unitᵛ ╎ < push (return unit) (push (app (var (_∋_.there _∋_.here)) unit) (return (var _∋_.here))) ； ⋄ · unitᵛ >∷ ◻ ⟩
    →ᶜ⟨ eval→ ⟩   ⟨ cloᵛ (return unit) (⋄ · unitᵛ) ╎ < push (return unit) (push (app (var (_∋_.there _∋_.here)) unit) (return (var _∋_.here))) ； ⋄ · unitᵛ >∷ ◻ ⟩
    →ᶜ⟨ return→ ⟩ ⟨ push (return unit) (push (app (var (_∋_.there _∋_.here)) unit) (return (var _∋_.here))) ╎ ⋄ · unitᵛ · cloᵛ (return unit) (⋄ · unitᵛ) ╎ ◻ ⟩
    →ᶜ⟨ push→ ⟩   ⟨ return unit ╎ ⋄ · unitᵛ · cloᵛ (return unit) (⋄ · unitᵛ) ╎ < push (app (var (_∋_.there _∋_.here)) unit) (return (var _∋_.here)) ； ⋄ · unitᵛ · cloᵛ (return unit) (⋄ · unitᵛ) >∷ ◻ ⟩
    →ᶜ⟨ eval→ ⟩   ⟨ unitᵛ ╎ < push (app (var (_∋_.there _∋_.here)) unit) (return (var _∋_.here)) ； ⋄ · unitᵛ · cloᵛ (return unit) (⋄ · unitᵛ) >∷ ◻ ⟩
    →ᶜ⟨ return→ ⟩ ⟨ push (app (var (_∋_.there _∋_.here)) unit) (return (var _∋_.here)) ╎ ⋄ · unitᵛ · cloᵛ (return unit) (⋄ · unitᵛ) · unitᵛ ╎ ◻ ⟩
    →ᶜ⟨ push→ ⟩   ⟨ app (var (_∋_.there _∋_.here)) unit ╎ ⋄ · unitᵛ · cloᵛ (return unit) (⋄ · unitᵛ) · unitᵛ ╎ < return (var _∋_.here) ； ⋄ · unitᵛ · cloᵛ (return unit) (⋄ · unitᵛ) · unitᵛ >∷ ◻ ⟩
    →ᶜ⟨ app→ ⟩    ⟨ return unit ╎ ⋄ · unitᵛ · unitᵛ ╎ < return (var _∋_.here) ； ⋄ · unitᵛ · cloᵛ (return unit) (⋄ · unitᵛ) · unitᵛ >∷ ◻ ⟩
    →ᶜ⟨ eval→ ⟩   ⟨ unitᵛ ╎ < return (var _∋_.here) ； ⋄ · unitᵛ · cloᵛ (return unit) (⋄ · unitᵛ) · unitᵛ >∷ ◻ ⟩
    →ᶜ⟨ return→ ⟩ ⟨ return (var _∋_.here) ╎ ⋄ · unitᵛ · cloᵛ (return unit) (⋄ · unitᵛ) · unitᵛ · unitᵛ ╎ ◻ ⟩
    →ᶜ⟨ eval→ ⟩ ⟨ unitᵛ ╎ ◻ ⟩ ◼ , refl)
_ = refl
