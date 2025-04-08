module Inception.Monad.Base where

open import Level
open import Function as F
open import Relation.Binary.PropositionalEquality

record Monad {x y} (T : Set x -> Set y) : Set (suc x ⊔ y) where
  infixl 4 _>>=_
  infixl 10 _*
  field
    η : ∀ {A} -> A -> T A
    _* : ∀ {A B} -> (A -> T B) -> T A -> T B

  field
    unitl : ∀ {A} -> (x : A) -> η {A} * ≡ id
    unitr : ∀ {A B} -> (f : A -> T B) -> f * ∘ η ≡ f
    assoc : ∀ {A B C} -> (f : A -> T B) -> (g : B -> T C) -> (g *  ∘  f) * ≡ g * ∘ f *

  map : ∀ {A B} -> (f : A -> B) -> T A -> T B
  map f = (η ∘ f) *

  _>>=_ : ∀ {A B} -> T A -> (A -> T B) -> T B
  m >>= f = (f *) m

open Monad public

record MonadMorphism {x y z} {T : Set x -> Set y} {S : Set x -> Set z} (MT : Monad T) (MS : Monad S) : Set (suc x ⊔ y ⊔ z) where
  private
    module T = Monad MT
    module S = Monad MS
  field
    F : ∀ {A} -> T A -> S A
    F-η : ∀ {A} -> F ∘ T.η {A} ≡ S.η
    F-* : ∀ {A B} -> (f : A -> T B) -> F ∘ (f T.*) ≡ (F ∘ f) S.* ∘ F

  nat : ∀ {A B} -> (f : A -> B) -> F ∘ T.map f ≡ S.map f ∘ F
  nat f = let open ≡-Reasoning in
    F ∘ (T.η ∘ f) T.* ≡⟨ F-* (T.η ∘ f) ⟩
    (F ∘ (T.η ∘ f)) S.* ∘ F ≡⟨ refl ⟩
    ((F ∘ T.η) ∘ f) S.* ∘ F ≡⟨ cong (λ p -> (p ∘ f) S.* ∘ F) F-η ⟩
    (S.η ∘ f) S.* ∘ F
    ∎

open MonadMorphism public

MonadMorphism≡ : ∀ {x y z} {T : Set x -> Set y} {S : Set x -> Set z} {MT : Monad T} {MS : Monad S} (M N : MonadMorphism MT MS) -> Set (suc x ⊔ y ⊔ z)
MonadMorphism≡ M N = ∀ {X} -> M .F {X} ≡ N .F {X}

record MonadAlg {x y} {T : Set x -> Set y} (MT : Monad T) (X : Set x) : Set (suc x ⊔ y) where
  private
    module T = Monad MT
  infixl 10 _#
  field
    _# : ∀ {Y} (f : Y -> X) -> T Y -> X
    η-# : ∀ {Y} (f : Y -> X) -> f # ∘ T.η ≡ f
    *-# : ∀ {Y Z} (g : Z -> T Y) (f : Y -> X) -> (f # ∘ g) # ≡ f # ∘ g T.*

  α : T X -> X
  α = id #

  α-η : α ∘ T.η ≡ id
  α-η = η-# id

open MonadAlg public

MonadAlg≡ : ∀ {x y} {T : Set x -> Set y} {MT : Monad T} {X : Set x} (A B : MonadAlg MT X) -> Set (suc x ⊔ y)
MonadAlg≡ A B = ∀ {Y} (f : Y -> _) -> A ._# f ≡ B ._# f
