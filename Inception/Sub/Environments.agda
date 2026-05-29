{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Environments (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Function.Base using (const; _∘_; _$_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; cong-app; dcong₂; sym; trans; subst; subst₂)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.Renaming
open import Inception.Sub.CPS R

open import Data.Unit
open import Data.Nat
open import Data.List using (List; _∷_; []; _++_)

open import Inception.Sub.Equality

open import Relation.Binary.HeterogeneousEquality as H using (_≅_)

open import Relation.Binary.HeterogeneousEquality.Core using (≡-to-≅)

----
import Data.Fin.Permutation
import Data.List.Relation.Binary.Permutation.Propositional

----

variable
  T◾ T◾' : Ty

module EnvMain {R₀ : Ty} (k₀ : ⟦ R₀ ⟧ → R) where

  infixl 27 _﹐_
  infixl 27 _﹐﹝_╎_﹞

  data Env : (Γ : Ctx) → Set

  data CompStack : (Δ : Ctx) → (X : Ty) → Set

  topCsEnv : CompStack Δ X → Env Δ
  ⟦_⟧ᴱ : (E : Env Γ) → ⟦ Γ ⟧ˣ
  ⟦_⟧ᶜˢ : (cs : CompStack Δ X) → K ⟦ X ⟧ → K ⟦ R₀ ⟧

  data CompStack  where

      ◻     :   CompStack ε R₀

      _⊲_⦂⦂_    : (Γ ∙ Z) ⊢ᶜ X → (γ : Env Γ) → (tail : CompStack Δ X) → {π : Wk Γ Δ} → .{wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv tail ⟧ᴱ} → CompStack Γ Z

  data Env where

      ∗       :  Env ε

      _﹐_     :  Env Γ → (M : V̲a̲l̲ Γ X) → Env (Γ ∙ X)

      _﹐﹝_╎_﹞ :  (γ : Env Γ) → (W : Γ ⊢ᶜ X) → (cs : CompStack Δ X) → {π : Wk Γ Δ} → .{wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → Env (Γ ∙ `V)

  variable
      γ  : Env Γ
      γ' : Env Γ'
      γ'' : Env Γ''

  topCsEnv ◻ = ∗
  topCsEnv (W ⊲ γ ⦂⦂ cs) = γ

  ⟦_⟧ᴷ : (cs : CompStack Δ Y) → ⟦ Y ⟧ → R
  ⟦_⟧ᴷ cs y = ⟦ cs ⟧ᶜˢ (η y) k₀

  ⟦ ∗ ⟧ᴱ = tt
  ⟦ E ﹐ M ⟧ᴱ = ⟦ E ⟧ᴱ , ⟦ toVal M ⟧ᵛ ⟦ E ⟧ᴱ
  ⟦ E ﹐﹝ W ╎ cs ﹞ ⟧ᴱ = ⟦ E ⟧ᴱ , ⟦ W ⟧ᶜ ⟦ E ⟧ᴱ ⟦ cs ⟧ᴷ

  ⟦ ◻ ⟧ᶜˢ = idf
  ⟦ W₁ ⊲ γ₁ ⦂⦂ tail ⟧ᶜˢ = < const ⟦ γ₁ ⟧ᴱ , idf > ； τ ； (⟦ W₁ ⟧ᶜ ♯) ； ⟦ tail ⟧ᶜˢ

  mutual
    empty-perm-absurd : ε ↭ (Γ ∙ X) → ⊥
    empty-perm-absurd (_↭_.trans perm₁ perm₂) rewrite sym (empty-perm perm₁) = empty-perm-absurd perm₂

    empty-perm : ε ↭ Γ → ε ≡ Γ
    empty-perm {Γ = ε} refl = refl
    empty-perm {Γ = ε} (_↭_.trans perm₁ perm₂) = refl
    empty-perm {Γ = Γ ∙ X} (_↭_.trans perm₁ perm₂) rewrite sym (empty-perm perm₁) = ql (empty-perm-absurd perm₂) (ε ≡ Γ ∙ X)

  perm-wk : Γ ↭ Γ' → Wk Γ Δ → Σ[ Δ' ∈ Ctx ] ((Δ ↭ Δ') × (Wk Γ' Δ'))
  perm-wk refl wk-ε = ε , refl , wk-ε
  perm-wk refl (wk-cong π) = _ ∙ _ , refl , wk-cong π
  perm-wk refl (wk-wk π) = _ , refl , wk-wk π
  perm-wk (prep X Γ↭Γ') (wk-cong π) =
    let
      IH = (perm-wk Γ↭Γ' π)
    in
    proj₁ IH ∙ X , prep X (proj₁ (proj₂ IH)) , wk-cong (proj₂ (proj₂ IH))
  perm-wk (prep X Γ↭Γ') (wk-wk π) =
    let
      IH = (perm-wk Γ↭Γ' π)
    in
    proj₁ IH , proj₁ (proj₂ IH) , wk-wk (proj₂ (proj₂ IH))
  perm-wk (swap X Y Γ↭Γ') (wk-cong (wk-cong π)) =
    let
      IH = (perm-wk Γ↭Γ' π)
    in
    proj₁ IH ∙ X ∙ Y , swap X Y (proj₁ (proj₂ IH)) , wk-cong (wk-cong (proj₂ (proj₂ IH)))
  perm-wk (swap X Y Γ↭Γ') (wk-cong (wk-wk π)) =
    let
      IH = (perm-wk Γ↭Γ' π)
    in
    proj₁ IH ∙ X , prep X (proj₁ (proj₂ IH)) , wk-wk (wk-cong (proj₂ (proj₂ IH)))
  perm-wk (swap X Y Γ↭Γ') (wk-wk (wk-cong π)) =
    let
      IH = (perm-wk Γ↭Γ' π)
    in
    proj₁ IH ∙ Y , prep Y (proj₁ (proj₂ IH)) , wk-cong (wk-wk (proj₂ (proj₂ IH)))
  perm-wk (swap X Y Γ↭Γ') (wk-wk (wk-wk π)) =
    let
      IH = (perm-wk Γ↭Γ' π)
    in
    proj₁ IH , proj₁ (proj₂ IH) , wk-wk (wk-wk (proj₂ (proj₂ IH)))
  perm-wk (_↭_.trans ε↭Γ' Γ'↭Γ'') wk-ε rewrite sym (empty-perm ε↭Γ') | sym (empty-perm Γ'↭Γ'') =
    ε , refl , wk-ε
  perm-wk (_↭_.trans Γ↭Γ' Γ'↭Γ'') (wk-cong π) =
    let
      IH1 = (perm-wk Γ↭Γ' (wk-cong π))
      IH2 = (perm-wk Γ'↭Γ'' (proj₂ (proj₂ IH1)))
    in
    proj₁ IH2 , _↭_.trans (proj₁ (proj₂ IH1)) (proj₁ (proj₂ IH2)) , proj₂ (proj₂ IH2)
  perm-wk (_↭_.trans Γ↭Γ' Γ'↭Γ'') (wk-wk π) =
    let
      IH1 = (perm-wk Γ↭Γ' (wk-wk π))
      IH2 = (perm-wk Γ'↭Γ'' (proj₂ (proj₂ IH1)))
    in
    proj₁ IH2 , _↭_.trans (proj₁ (proj₂ IH1)) (proj₁ (proj₂ IH2)) , proj₂ (proj₂ IH2)


  --perm-wk : Γ ↭ Γ' → (π : Wk Γ Δ) → Σ[ Δ' ∈ Ctx ] ((Δ ↭ Δ') × (Wk Γ' Δ'))
  -- record PermWk (Γ ↭ Γ') (Wk Γ Δ) : Set where
  --   field
  --     pwk-Δ : Ctx
  --     pwk-perm : Δ ↭ perm-Δ
  --     pwk-π : Wk Γ' perm-Δ
  --     pwk-eq : ∀ {γ : Env Γ} → (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ?) --⟦ pwk-π ⟧ʷ ⟦ γ ⟧ᴱ

  perm-sem-trans : (Γ↭Γ' : Γ ↭ Γ') → (Γ'↭Γ'' : Γ' ↭ Γ'') → ⟦ _↭_.trans Γ↭Γ' Γ'↭Γ'' ⟧ᴾ ≡ ⟦ Γ'↭Γ'' ⟧ᴾ ∘ ⟦ Γ↭Γ' ⟧ᴾ
  perm-sem-trans Γ↭Γ' Γ'↭Γ'' = refl

  perm-sem-mem : (Γ↭Γ' : Γ ↭ Γ') → (E : ⟦ Γ ⟧ˣ) → (i : Γ ∋ X) → ⟦ i ⟧ᵐ E ≡ ⟦ perm-mem Γ↭Γ' i ⟧ᵐ (⟦ Γ↭Γ' ⟧ᴾ E)
  perm-sem-mem refl E Cx.h = refl
  perm-sem-mem refl E (Cx.t i) = refl
  perm-sem-mem (prep X Γ↭Γ') E Cx.h = refl
  perm-sem-mem (prep X Γ↭Γ') E (Cx.t i) = perm-sem-mem Γ↭Γ' (proj₁ E) i
  perm-sem-mem (swap X Y Γ↭Γ') E Cx.h = refl
  perm-sem-mem (swap X Y Γ↭Γ') E (Cx.t Cx.h) = refl
  perm-sem-mem (swap X Y Γ↭Γ') E (Cx.t (Cx.t i)) = perm-sem-mem Γ↭Γ' (proj₁ (proj₁ E)) i
  perm-sem-mem (_↭_.trans Γ↭Γ' Γ'↭Γ'') E Cx.h =
    let
      IH1 = perm-sem-mem Γ↭Γ' E h
      IH2 = perm-sem-mem Γ'↭Γ'' (⟦ Γ↭Γ' ⟧ᴾ E) (perm-mem Γ↭Γ' h)
    in
    Eq.trans IH1 IH2
  perm-sem-mem (_↭_.trans Γ↭Γ' Γ'↭Γ'') E (Cx.t i) =
    let
      IH1 = perm-sem-mem Γ↭Γ' E (t i)
      IH2 = perm-sem-mem Γ'↭Γ'' (⟦ Γ↭Γ' ⟧ᴾ E) (perm-mem Γ↭Γ' (t i))
    in
    Eq.trans IH1 IH2

  mutual
    perm-sem-val : (Γ↭Γ' : Γ ↭ Γ') → (E : ⟦ Γ ⟧ˣ) → (M : Val Γ X) → ⟦ M ⟧ᵛ E ≡ ⟦ perm-val Γ↭Γ' M ⟧ᵛ (⟦ Γ↭Γ' ⟧ᴾ E)
    perm-sem-val Γ↭Γ' E (var i) = perm-sem-mem Γ↭Γ' E i
    perm-sem-val Γ↭Γ' E (lam {A = X} W) = extensionality (λ x → perm-sem-comp (prep X Γ↭Γ') (E , x) W)
    perm-sem-val Γ↭Γ' E (pair M₁ M₂) = cong₂ _,_ (perm-sem-val Γ↭Γ' E M₁) (perm-sem-val Γ↭Γ' E M₂)
    perm-sem-val Γ↭Γ' E (pm {A = X} {B = Y} M N) =
      let
        a0 : ⟦ N ⟧ᵛ ((E , proj₁ (⟦ M ⟧ᵛ E)) , proj₂ (⟦ M ⟧ᵛ E)) ≡ ⟦ perm-val (prep Y (prep X Γ↭Γ')) N ⟧ᵛ (⟦ prep Y (prep X Γ↭Γ') ⟧ᴾ ((E , proj₁ (⟦ M ⟧ᵛ E)) , proj₂ (⟦ M ⟧ᵛ E)))
        a0 = perm-sem-val (prep Y (prep X Γ↭Γ')) ((E , proj₁ (⟦ M ⟧ᵛ E)) , proj₂ (⟦ M ⟧ᵛ E)) N
        a1 : (⟦ prep Y (prep X Γ↭Γ') ⟧ᴾ ((E , proj₁ (⟦ M ⟧ᵛ E)) , proj₂ (⟦ M ⟧ᵛ E))) ≡ ((⟦ Γ↭Γ' ⟧ᴾ E , proj₁ (⟦ perm-val Γ↭Γ' M ⟧ᵛ (⟦ Γ↭Γ' ⟧ᴾ E))) , proj₂ (⟦ perm-val Γ↭Γ' M ⟧ᵛ (⟦ Γ↭Γ' ⟧ᴾ E)))
        a1 =  (⟦ prep Y (prep X Γ↭Γ') ⟧ᴾ ((E , proj₁ (⟦ M ⟧ᵛ E)) , proj₂ (⟦ M ⟧ᵛ E)))
             ≡⟨ refl ⟩
              (⟦ Γ↭Γ' ⟧ᴾ E , proj₁ (⟦ M ⟧ᵛ E)) , proj₂ (⟦ M ⟧ᵛ E)
             ≡⟨ cong (λ x → (⟦ Γ↭Γ' ⟧ᴾ E , proj₁ x) , proj₂ x) (perm-sem-val Γ↭Γ' E M) ⟩
              ((⟦ Γ↭Γ' ⟧ᴾ E , proj₁ (⟦ perm-val Γ↭Γ' M ⟧ᵛ (⟦ Γ↭Γ' ⟧ᴾ E))) , proj₂ (⟦ perm-val Γ↭Γ' M ⟧ᵛ (⟦ Γ↭Γ' ⟧ᴾ E))) ∎
      in
      ⟦ N ⟧ᵛ ((E , proj₁ (⟦ M ⟧ᵛ E)) , proj₂ (⟦ M ⟧ᵛ E))
      ≡⟨ a0 ⟩
      ⟦ perm-val (prep Y (prep X Γ↭Γ')) N ⟧ᵛ (⟦ prep Y (prep X Γ↭Γ') ⟧ᴾ ((E , proj₁ (⟦ M ⟧ᵛ E)) , proj₂ (⟦ M ⟧ᵛ E)))
      ≡⟨ cong ⟦ perm-val (prep Y (prep X Γ↭Γ')) N ⟧ᵛ a1 ⟩
      ⟦ perm-val (prep Y (prep X Γ↭Γ')) N ⟧ᵛ ((⟦ Γ↭Γ' ⟧ᴾ E , proj₁ (⟦ perm-val Γ↭Γ' M ⟧ᵛ (⟦ Γ↭Γ' ⟧ᴾ E))) , proj₂ (⟦ perm-val Γ↭Γ' M ⟧ᵛ (⟦ Γ↭Γ' ⟧ᴾ E))) ∎
    perm-sem-val Γ↭Γ' E unit = refl

    perm-sem-comp : (Γ↭Γ' : Γ ↭ Γ') → (E : ⟦ Γ ⟧ˣ) → (W : Comp Γ X) → ⟦ W ⟧ᶜ E ≡ ⟦ perm-comp Γ↭Γ' W ⟧ᶜ (⟦ Γ↭Γ' ⟧ᴾ E)
    perm-sem-comp Γ↭Γ' E (return M) = extensionality (λ k → cong k (perm-sem-val Γ↭Γ' E M))
    perm-sem-comp Γ↭Γ' E (pm {A = X} {B = Y} M W) =
      let
        a1 = perm-sem-comp (prep Y (prep X Γ↭Γ')) ((E , proj₁ (⟦ M ⟧ᵛ E)) , proj₂ (⟦ M ⟧ᵛ E)) W
        a2 = perm-sem-val Γ↭Γ' E M
        goal : ⟦ pm M W ⟧ᶜ E ≡ ⟦ pm (perm-val Γ↭Γ' M) (perm-comp (prep Y (prep X Γ↭Γ')) W) ⟧ᶜ (⟦ Γ↭Γ' ⟧ᴾ E)
        goal = ⟦ pm M W ⟧ᶜ E
               ≡⟨ refl ⟩
               ⟦ W ⟧ᶜ ((E , proj₁ (⟦ M ⟧ᵛ E)) , proj₂ (⟦ M ⟧ᵛ E))
               ≡⟨ a1 ⟩
               ⟦ perm-comp (prep Y (prep X Γ↭Γ')) W ⟧ᶜ (⟦ prep Y (prep X Γ↭Γ') ⟧ᴾ ((E , proj₁ (⟦ M ⟧ᵛ E)) , proj₂ (⟦ M ⟧ᵛ E)))
               ≡⟨ cong (λ x → ⟦ perm-comp (prep Y (prep X Γ↭Γ')) W ⟧ᶜ ((⟦ Γ↭Γ' ⟧ᴾ E , proj₁ x) , proj₂ x)) a2 ⟩
               ⟦ perm-comp (prep Y (prep X Γ↭Γ')) W ⟧ᶜ ((⟦ Γ↭Γ' ⟧ᴾ E , proj₁ (⟦ perm-val Γ↭Γ' M ⟧ᵛ (⟦ Γ↭Γ' ⟧ᴾ E))) , proj₂ (⟦ perm-val Γ↭Γ' M ⟧ᵛ (⟦ Γ↭Γ' ⟧ᴾ E)))
               ≡⟨ refl ⟩
               ⟦ pm (perm-val Γ↭Γ' M) (perm-comp (prep Y (prep X Γ↭Γ')) W) ⟧ᶜ (⟦ Γ↭Γ' ⟧ᴾ E) ∎
      in
      goal
    perm-sem-comp Γ↭Γ' E (push {A = X} W₁ W₂) =
      let
        IH1 = perm-sem-comp Γ↭Γ' E W₁
        goal : (λ k → ⟦ W₁ ⟧ᶜ E (λ z → ⟦ W₂ ⟧ᶜ (E , z) k)) ≡ (λ k → ⟦ perm-comp Γ↭Γ' W₁ ⟧ᶜ (⟦ Γ↭Γ' ⟧ᴾ E) (λ z → ⟦ perm-comp (prep X Γ↭Γ') W₂ ⟧ᶜ (⟦ Γ↭Γ' ⟧ᴾ E , z) k))
        goal = extensionality λ k → cong₂ (λ x y → x y) IH1 (extensionality λ x → cong-app (perm-sem-comp (prep X Γ↭Γ') (E , x) W₂) k)
      in
      goal
    perm-sem-comp Γ↭Γ' E (app M N) =
      let
        IH1 = perm-sem-val Γ↭Γ' E M
        IH2 = perm-sem-val Γ↭Γ' E N
        goal : ⟦ M ⟧ᵛ E (⟦ N ⟧ᵛ E) ≡ ⟦ perm-val Γ↭Γ' M ⟧ᵛ (⟦ Γ↭Γ' ⟧ᴾ E) (⟦ perm-val Γ↭Γ' N ⟧ᵛ (⟦ Γ↭Γ' ⟧ᴾ E))
        goal = cong₂ (λ x y → x y) IH1 IH2
      in
      goal
    perm-sem-comp Γ↭Γ' E (var M) = cong varK (perm-sem-val Γ↭Γ' E M)
    perm-sem-comp Γ↭Γ' E (sub {A = X} W₁ W₂) =
      let
        IH2 = perm-sem-comp Γ↭Γ' E W₂
        goal : (λ k → ⟦ W₁ ⟧ᶜ (E , ⟦ W₂ ⟧ᶜ E k) k) ≡ (λ k → ⟦ perm-comp (prep `V Γ↭Γ') W₁ ⟧ᶜ (⟦ Γ↭Γ' ⟧ᴾ E , ⟦ perm-comp Γ↭Γ' W₂ ⟧ᶜ (⟦ Γ↭Γ' ⟧ᴾ E) k) k)
        goal = extensionality λ k →
                              let
                                a1 = perm-sem-comp (prep `V Γ↭Γ') (E , ⟦ W₂ ⟧ᶜ E k) W₁
                                a2 : (⟦ Γ↭Γ' ⟧ᴾ E , ⟦ perm-comp Γ↭Γ' W₂ ⟧ᶜ (⟦ Γ↭Γ' ⟧ᴾ E) k) ≡ (⟦ prep `V Γ↭Γ' ⟧ᴾ (E , ⟦ W₂ ⟧ᶜ E k))
                                a2 =   (⟦ Γ↭Γ' ⟧ᴾ E , ⟦ perm-comp Γ↭Γ' W₂ ⟧ᶜ (⟦ Γ↭Γ' ⟧ᴾ E) k)
                                      ≡⟨ cong (⟦ Γ↭Γ' ⟧ᴾ E ,_) (sym (cong-app IH2 k)) ⟩
                                       ⟦ Γ↭Γ' ⟧ᴾ E , ⟦ W₂ ⟧ᶜ E k
                                      ≡⟨ refl ⟩
                                       (⟦ prep `V Γ↭Γ' ⟧ᴾ (E , ⟦ W₂ ⟧ᶜ E k)) ∎
                                b1 = cong-app a1 k
                              in
                              ⟦ W₁ ⟧ᶜ (E , ⟦ W₂ ⟧ᶜ E k) k
                              ≡⟨ b1 ⟩
                               ⟦ perm-comp (prep `V Γ↭Γ') W₁ ⟧ᶜ (⟦ prep `V Γ↭Γ' ⟧ᴾ (E , ⟦ W₂ ⟧ᶜ E k)) k
                              ≡⟨ cong (λ x → ⟦ perm-comp (prep `V Γ↭Γ') W₁ ⟧ᶜ x k) (sym a2) ⟩
                              ⟦ perm-comp (prep `V Γ↭Γ') W₁ ⟧ᶜ (⟦ Γ↭Γ' ⟧ᴾ E , ⟦ perm-comp Γ↭Γ' W₂ ⟧ᶜ (⟦ Γ↭Γ' ⟧ᴾ E) k) k ∎
      in
      goal


  mutual

    perm-cs : Γ ↭ Γ' → CompStack Γ X → CompStack Γ' X
    perm-cs refl ◻ = ◻
    perm-cs refl ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡}) = ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡})
    perm-cs (prep X Γ↭Γ') ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡}) = (perm-comp (prep _ (prep X Γ↭Γ')) W ⊲ perm-env (prep X Γ↭Γ') γ ⦂⦂ perm-cs (proj₁ (proj₂ (perm-wk (prep X Γ↭Γ') π))) cs) {π = proj₂ (proj₂ (perm-wk (prep X Γ↭Γ') π))} {wk≡ = {!!}}
    perm-cs (swap X Y Γ↭Γ') ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡}) = {!!}
    perm-cs (_↭_.trans Γ↭Γ' Γ'↭Γ'') ◻ = {!!}
    perm-cs (_↭_.trans Γ↭Γ' Γ'↭Γ'') ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡}) = {!!}

    perm-env : Γ ↭ Γ' → Env Γ → Env Γ'
    perm-env refl ∗ = ∗
    perm-env refl (γ ﹐ M) = γ ﹐ M
    perm-env refl ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) = (γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}
    perm-env (prep X Γ↭Γ') (γ ﹐ M) = perm-env Γ↭Γ' γ ﹐ perm-v̲a̲l̲ Γ↭Γ' M
    perm-env (prep X Γ↭Γ') ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) =
      let
        a0 = perm-wk Γ↭Γ' π
        Δ↭Δ' = proj₁ (proj₂ a0)
        π' = proj₂ (proj₂ a0)
      in
      (perm-env Γ↭Γ' γ ﹐﹝ perm-comp Γ↭Γ' W ╎ perm-cs Δ↭Δ' cs ﹞) {π = π'} {wk≡ = {!!}}
    perm-env (swap X Y Γ↭Γ') (γ ﹐ M) = {!!}
    perm-env (swap X Y Γ↭Γ') (γ ﹐﹝ W ╎ cs ﹞) = {!!}
    perm-env (_↭_.trans Γ↭Γ' Γ↭Γ'') ∗ = {!!}
    perm-env (_↭_.trans Γ↭Γ' Γ↭Γ'') (γ ﹐ M) = {!!}
    perm-env (_↭_.trans Γ↭Γ' Γ↭Γ'') (γ ﹐﹝ W ╎ cs ﹞) = {!!}

    {-
    perm-sem-mem : (Γ↭Γ' : Γ ↭ Γ') → (γ : Env Γ) → (i : Γ ∋ X) → ⟦ i ⟧ᵐ ⟦ γ ⟧ᴱ ≡ ⟦ perm-mem Γ↭Γ' i ⟧ᵐ (⟦ Γ↭Γ' ⟧ᴾ ⟦ γ ⟧ᴱ)

    perm-sem-mem refl (γ ﹐ M) Cx.h = refl
    perm-sem-mem (prep X Γ↭Γ') (γ ﹐ M) Cx.h = refl
    perm-sem-mem (swap X Y Γ↭Γ') (γ ﹐ M) Cx.h = refl
    perm-sem-mem (_↭_.trans Γ↭Γ' Γ'↭Γ'') (γ ﹐ M) Cx.h =
      let
        IH1 = perm-sem-mem Γ↭Γ' (γ ﹐ M) h
        IH2 = perm-sem-mem Γ'↭Γ'' (perm-env Γ↭Γ' (γ ﹐ M)) (perm-mem Γ↭Γ' h)
        eq1 = perm-sem Γ↭Γ' (γ ﹐ M)
      in
        ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ
      ≡⟨ IH1 ⟩
        ⟦ perm-mem Γ↭Γ' h ⟧ᵐ (⟦ Γ↭Γ' ⟧ᴾ ⟦ γ ﹐ M ⟧ᴱ)
      ≡⟨ cong ⟦ perm-mem Γ↭Γ' h ⟧ᵐ eq1 ⟩
        ⟦ perm-mem Γ↭Γ' h ⟧ᵐ ⟦ perm-env Γ↭Γ' (γ ﹐ M) ⟧ᴱ
      ≡⟨ IH2 ⟩
        ⟦ perm-mem Γ'↭Γ'' (perm-mem Γ↭Γ' h) ⟧ᵐ (⟦ Γ'↭Γ'' ⟧ᴾ ⟦ perm-env Γ↭Γ' (γ ﹐ M) ⟧ᴱ)
      ≡⟨ cong (λ x → ⟦ perm-mem Γ'↭Γ'' (perm-mem Γ↭Γ' h) ⟧ᵐ (⟦ Γ'↭Γ'' ⟧ᴾ x)) (sym eq1) ⟩
        ⟦ perm-mem Γ'↭Γ'' (perm-mem Γ↭Γ' h) ⟧ᵐ (⟦ Γ'↭Γ'' ⟧ᴾ (⟦ Γ↭Γ' ⟧ᴾ (⟦ γ ⟧ᴱ , ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ))) ∎

    perm-sem-mem refl (γ ﹐﹝ W ╎ cs ﹞) Cx.h = refl
    perm-sem-mem (prep X Γ↭Γ') (γ ﹐﹝ W ╎ cs ﹞) Cx.h = refl
    perm-sem-mem (swap X Y Γ↭Γ') (γ ﹐﹝ W ╎ cs ﹞) Cx.h = refl
    perm-sem-mem (_↭_.trans Γ↭Γ' Γ'↭Γ'') ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) Cx.h =
      let
        IH1 = perm-sem-mem Γ↭Γ' ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) h
        IH2 = perm-sem-mem Γ'↭Γ'' (perm-env Γ↭Γ' ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡})) (perm-mem Γ↭Γ' h)
        eq1 = perm-sem Γ↭Γ' ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡})
      in
        ⟦ h ⟧ᵐ ⟦ ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) ⟧ᴱ
      ≡⟨ IH1 ⟩
        ⟦ perm-mem Γ↭Γ' h ⟧ᵐ (⟦ Γ↭Γ' ⟧ᴾ ⟦ ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) ⟧ᴱ)
      ≡⟨ cong ⟦ perm-mem Γ↭Γ' h ⟧ᵐ eq1 ⟩
        ⟦ perm-mem Γ↭Γ' h ⟧ᵐ ⟦ perm-env Γ↭Γ' (γ ﹐﹝ W ╎ cs ﹞) ⟧ᴱ
      ≡⟨ IH2 ⟩
        ⟦ perm-mem Γ'↭Γ'' (perm-mem Γ↭Γ' h) ⟧ᵐ (⟦ Γ'↭Γ'' ⟧ᴾ ⟦ perm-env Γ↭Γ' (γ ﹐﹝ W ╎ cs ﹞) ⟧ᴱ)
      ≡⟨ cong (λ x → ⟦ perm-mem Γ'↭Γ'' (perm-mem Γ↭Γ' h) ⟧ᵐ (⟦ Γ'↭Γ'' ⟧ᴾ x)) (sym eq1) ⟩
        ⟦ perm-mem (_↭_.trans Γ↭Γ' Γ'↭Γ'') h ⟧ᵐ (⟦ _↭_.trans Γ↭Γ' Γ'↭Γ'' ⟧ᴾ ⟦ ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) ⟧ᴱ) ∎

    perm-sem-mem refl (γ ﹐ M) (Cx.t i) = refl
    perm-sem-mem (prep X Γ↭Γ') (γ ﹐ M) (Cx.t i) = perm-sem-mem Γ↭Γ' γ i

    perm-sem-mem (swap X Y Γ↭Γ') (γ ﹐ M₁ ﹐ M) (Cx.t Cx.h) = refl
    perm-sem-mem (swap X Y Γ↭Γ') (γ ﹐ M₁ ﹐ M) (Cx.t (Cx.t i)) = perm-sem-mem Γ↭Γ' γ i
    perm-sem-mem (swap X Y Γ↭Γ') (∗ ﹐﹝ W ╎ cs ﹞ ﹐ M) (Cx.t Cx.h) = refl
    perm-sem-mem (swap X Y Γ↭Γ') (γ ﹐ M₁ ﹐﹝ W ╎ cs ﹞ ﹐ M) (Cx.t Cx.h) = refl
    perm-sem-mem (swap X Y Γ↭Γ') (γ ﹐ M₁ ﹐﹝ W ╎ cs ﹞ ﹐ M) (Cx.t (Cx.t i)) =
      let
        IH = perm-sem-mem Γ↭Γ' (γ ﹐ M₁) i
      in
      ⟦ i ⟧ᵐ (⟦ γ ⟧ᴱ , ⟦ toVal M₁ ⟧ᵛ ⟦ γ ⟧ᴱ)
      ≡⟨ IH ⟩
       ⟦ perm-mem Γ↭Γ' i ⟧ᵐ (⟦ Γ↭Γ' ⟧ᴾ ⟦ γ ﹐ M₁ ⟧ᴱ)
      ≡⟨ refl ⟩
      ⟦ perm-mem Γ↭Γ' i ⟧ᵐ (⟦ Γ↭Γ' ⟧ᴾ (⟦ γ ⟧ᴱ , ⟦ toVal M₁ ⟧ᵛ ⟦ γ ⟧ᴱ)) ∎
    perm-sem-mem (swap X Y Γ↭Γ') (γ ﹐﹝ W₁ ╎ cs₁ ﹞ ﹐﹝ W ╎ cs ﹞ ﹐ M) (Cx.t Cx.h) = refl
    perm-sem-mem (swap X Y Γ↭Γ') (((γ ﹐﹝ W₁ ╎ cs₁ ﹞) {π = π} {wk≡ = wk≡}) ﹐﹝ W ╎ cs ﹞ ﹐ M) (Cx.t (Cx.t i)) =
      let
        IH = perm-sem-mem Γ↭Γ' ((γ ﹐﹝ W₁ ╎ cs₁ ﹞) {π = π} {wk≡ = wk≡}) i
      in
      ⟦ i ⟧ᵐ (⟦ γ ⟧ᴱ , ⟦ W₁ ⟧ᶜ ⟦ γ ⟧ᴱ (λ y → ⟦ cs₁ ⟧ᶜˢ (λ k → k y) k₀))
      ≡⟨ IH ⟩
       ⟦ perm-mem Γ↭Γ' i ⟧ᵐ (⟦ Γ↭Γ' ⟧ᴾ ⟦ ((γ ﹐﹝ W₁ ╎ cs₁ ﹞) {π = π} {wk≡ = wk≡}) ⟧ᴱ)
      ≡⟨ refl ⟩
      ⟦ perm-mem Γ↭Γ' i ⟧ᵐ (⟦ Γ↭Γ' ⟧ᴾ (⟦ γ ⟧ᴱ , ⟦ W₁ ⟧ᶜ ⟦ γ ⟧ᴱ (λ y → ⟦ cs₁ ⟧ᶜˢ (λ k → k y) k₀))) ∎

    perm-sem-mem (_↭_.trans Γ↭Γ' Γ'↭Γ'') (γ ﹐ M) (Cx.t i) =
      let
        IH1 = perm-sem-mem Γ↭Γ' (γ ﹐ M) (t i)
        IH2 = perm-sem-mem Γ'↭Γ'' (perm-env Γ↭Γ' (γ ﹐ M)) (perm-mem Γ↭Γ' (t i))
        eq1 = perm-sem Γ↭Γ' (γ ﹐ M)
      in
      ⟦ i ⟧ᵐ ⟦ γ ⟧ᴱ
      ≡⟨ IH1 ⟩
       ⟦ perm-mem Γ↭Γ' (t i) ⟧ᵐ (⟦ Γ↭Γ' ⟧ᴾ ⟦ γ ﹐ M ⟧ᴱ)
      ≡⟨ cong ⟦ perm-mem Γ↭Γ' (t i) ⟧ᵐ eq1 ⟩
       ⟦ perm-mem Γ↭Γ' (t i) ⟧ᵐ ⟦ perm-env Γ↭Γ' (γ ﹐ M) ⟧ᴱ
      ≡⟨ IH2 ⟩
       ⟦ perm-mem Γ'↭Γ'' (perm-mem Γ↭Γ' (t i)) ⟧ᵐ (⟦ Γ'↭Γ'' ⟧ᴾ ⟦ perm-env Γ↭Γ' (γ ﹐ M) ⟧ᴱ)
      ≡⟨ cong (λ x → ⟦ perm-mem Γ'↭Γ'' (perm-mem Γ↭Γ' (t i)) ⟧ᵐ (⟦ Γ'↭Γ'' ⟧ᴾ x)) (sym eq1) ⟩
       ⟦ perm-mem Γ'↭Γ'' (perm-mem Γ↭Γ' (t i)) ⟧ᵐ (⟦ Γ'↭Γ'' ⟧ᴾ (⟦ Γ↭Γ' ⟧ᴾ (⟦ γ ⟧ᴱ , ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ))) ∎

    perm-sem-mem refl (γ ﹐﹝ W ╎ cs ﹞) (Cx.t i) = refl
    perm-sem-mem (prep X Γ↭Γ') (γ ﹐﹝ W ╎ cs ﹞) (Cx.t i) = perm-sem-mem Γ↭Γ' γ i
    perm-sem-mem (swap X Y Γ↭Γ') (γ ﹐ M ﹐﹝ W ╎ cs ﹞) (Cx.t Cx.h) = refl
    perm-sem-mem (swap X Y Γ↭Γ') (γ ﹐ M ﹐﹝ W ╎ cs ﹞) (Cx.t (Cx.t i)) = perm-sem-mem Γ↭Γ' γ i
    perm-sem-mem (swap X Y Γ↭Γ') (γ ﹐﹝ W₁ ╎ cs₁ ﹞ ﹐﹝ W ╎ cs ﹞) (Cx.t Cx.h) = refl
    perm-sem-mem (swap X Y Γ↭Γ') (γ ﹐﹝ W₁ ╎ cs₁ ﹞ ﹐﹝ W ╎ cs ﹞) (Cx.t (Cx.t i)) = perm-sem-mem Γ↭Γ' γ i
    perm-sem-mem (_↭_.trans Γ↭Γ' Γ'↭Γ'') ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) (t i) =
      let
        IH1 = perm-sem-mem Γ↭Γ' ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) (t i)
        IH2 = perm-sem-mem Γ'↭Γ'' (perm-env Γ↭Γ' ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡})) (perm-mem Γ↭Γ' (t i))
        eq1 = perm-sem Γ↭Γ' ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡})
      in
       ⟦ t i ⟧ᵐ ⟦ ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) ⟧ᴱ
      ≡⟨ IH1 ⟩
       ⟦ perm-mem Γ↭Γ' (t i) ⟧ᵐ (⟦ Γ↭Γ' ⟧ᴾ ⟦ ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) ⟧ᴱ)
      ≡⟨ cong ⟦ perm-mem Γ↭Γ' (t i) ⟧ᵐ eq1 ⟩
       ⟦ perm-mem Γ↭Γ' (t i) ⟧ᵐ ⟦ perm-env Γ↭Γ' ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) ⟧ᴱ
      ≡⟨ IH2 ⟩
       ⟦ perm-mem Γ'↭Γ'' (perm-mem Γ↭Γ' (t i)) ⟧ᵐ (⟦ Γ'↭Γ'' ⟧ᴾ ⟦ perm-env Γ↭Γ' ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) ⟧ᴱ)
      ≡⟨ cong (λ x → ⟦ perm-mem Γ'↭Γ'' (perm-mem Γ↭Γ' (t i)) ⟧ᵐ (⟦ Γ'↭Γ'' ⟧ᴾ x)) (sym eq1) ⟩
       ⟦ perm-mem (_↭_.trans Γ↭Γ' Γ'↭Γ'') (t i) ⟧ᵐ (⟦ _↭_.trans Γ↭Γ' Γ'↭Γ'' ⟧ᴾ ⟦ ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) ⟧ᴱ) ∎



    perm-sem-v̲a̲l̲ : (Γ↭Γ' : Γ ↭ Γ') → (γ : Env Γ) → (M : V̲a̲l̲ Γ X) → ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ ≡ ⟦ toVal (perm-v̲a̲l̲ Γ↭Γ' M) ⟧ᵛ (⟦ Γ↭Γ' ⟧ᴾ ⟦ γ ⟧ᴱ)
    perm-sem-v̲a̲l̲ Γ↭Γ' γ (l̲a̲m̲ W) = {!!}
    perm-sem-v̲a̲l̲ Γ↭Γ' γ (pa̲i̲r̲ M₁ M₂) = cong₂ _,_ (perm-sem-v̲a̲l̲ Γ↭Γ' γ M₁) (perm-sem-v̲a̲l̲ Γ↭Γ' γ M₂)
    perm-sem-v̲a̲l̲ Γ↭Γ' γ u̲n̲i̲t̲ = refl
    perm-sem-v̲a̲l̲ Γ↭Γ' γ (v̲a̲r̲ i) = perm-sem-mem Γ↭Γ' γ i

    perm-sem-val : (Γ↭Γ' : Γ ↭ Γ') → (γ : Env Γ) → (M : Val Γ X) → ⟦ M ⟧ᵛ ⟦ γ ⟧ᴱ ≡ ⟦ perm-val Γ↭Γ' M ⟧ᵛ (⟦ Γ↭Γ' ⟧ᴾ ⟦ γ ⟧ᴱ)
    perm-sem-val Γ↭Γ' γ (var i) = perm-sem-mem Γ↭Γ' γ i
    perm-sem-val Γ↭Γ' γ (lam W) = {!perm-sem-comp ? ? W!}
    perm-sem-val Γ↭Γ' γ (pair M₁ M₂) = {!!}
    perm-sem-val Γ↭Γ' γ (pm {A = X} {B = Y} M N) =
      let
        a0 = proj₁ (⟦ M ⟧ᵛ ⟦ γ ⟧ᴱ)
      in
      perm-sem-val (prep Y (prep X Γ↭Γ')) {!!} N
    perm-sem-val Γ↭Γ' γ unit = refl

    perm-sem-comp : (Γ↭Γ' : Γ ↭ Γ') → (γ : Env Γ) → (W : Comp Γ X) → ⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ ≡ ⟦ perm-comp Γ↭Γ' W ⟧ᶜ (⟦ Γ↭Γ' ⟧ᴾ ⟦ γ ⟧ᴱ)
    perm-sem-comp Γ↭Γ' γ (return M) = {!perm-sem-val Γ↭Γ' γ M!}
    perm-sem-comp Γ↭Γ' γ (pm M W) = {!!}
    perm-sem-comp Γ↭Γ' γ (push W₁ W₂) = {!!}
    perm-sem-comp Γ↭Γ' γ (app M N) = {!!}
    perm-sem-comp Γ↭Γ' γ (var M) = {!!}
    perm-sem-comp Γ↭Γ' γ (sub W₁ W₂) = {!!}

    perm-sem : (Γ↭Γ' : Γ ↭ Γ') → (γ : Env Γ) → ⟦ Γ↭Γ' ⟧ᴾ ⟦ γ ⟧ᴱ ≡ ⟦ perm-env Γ↭Γ' γ ⟧ᴱ
    perm-sem refl ∗ = refl
    perm-sem refl (γ ﹐ M) = refl
    perm-sem refl (γ ﹐﹝ W ╎ cs ﹞) = refl
    perm-sem (prep X Γ↭Γ') (γ ﹐ M) =
       ⟦ prep X Γ↭Γ' ⟧ᴾ (⟦ γ ⟧ᴱ , ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ)
      ≡⟨ refl ⟩
        ⟦ Γ↭Γ' ⟧ᴾ ⟦ γ ⟧ᴱ , ⟦ toVal M ⟧ᵛ ⟦ γ ⟧ᴱ
      ≡⟨ {!!} ⟩
       (⟦ perm-env Γ↭Γ' γ ⟧ᴱ , ⟦ toVal (perm-v̲a̲l̲ Γ↭Γ' M) ⟧ᵛ (⟦ Γ↭Γ' ⟧ᴾ ⟦ γ ⟧ᴱ))
      ≡⟨ {!!} ⟩
       (⟦ perm-env Γ↭Γ' γ ⟧ᴱ , ⟦ toVal (perm-v̲a̲l̲ Γ↭Γ' M) ⟧ᵛ ⟦ perm-env Γ↭Γ' γ ⟧ᴱ) ∎
    perm-sem (prep X Γ↭Γ') (γ ﹐﹝ W ╎ cs ﹞) = {!!}
    perm-sem (swap X Y Γ↭Γ') (γ ﹐ M) = {!!}
    perm-sem (swap X Y Γ↭Γ') (γ ﹐﹝ W ╎ cs ﹞) = {!!}
    perm-sem (_↭_.trans Γ↭Γ' Γ↭Γ'') ∗ = {!!}
    perm-sem (_↭_.trans Γ↭Γ' Γ↭Γ'') (γ ﹐ M) = {!!}
    perm-sem (_↭_.trans Γ↭Γ' Γ↭Γ'') (γ ﹐﹝ W ╎ cs ﹞) = {!!}

    -}


  -----------------------------------------------------------------------------
  -- PROPERTIES OF ENVIRONMENTS
  -----------------------------------------------------------------------------

  data EnvExt : (i : Γ ∋ X) → (γ : Env Γ) → (γ' : Env Γ') → Set where

    env-val : {M : V̲a̲l̲ Γ X} → EnvExt h (γ ﹐ M) (γ ﹐ M)

    env-comp : {W : Γ ⊢ᶜ X} {cs : CompStack Δ X} {π : Wk Γ Δ} .{wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} → EnvExt h ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡})

    ext-val : {γ : Env Γ} {γ' : Env Γ'} {M : V̲a̲l̲ Γ Y} {i : Γ ∋ X} → EnvExt i γ γ' → EnvExt (t i) (γ ﹐ M) γ'

    ext-comp : {γ : Env Γ} {γ' : Env Γ'} {W : Γ ⊢ᶜ Y} {cs : CompStack Δ Y} {π : Wk Γ Δ} .{wk≡ : ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ} {i : Γ ∋ X} → EnvExt i γ γ' → EnvExt (t i) ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) γ'

    ext-jmp : {γ : Env Γ} {γ' : Env Γ'} {i : Γ ∋ `V} → EnvExt i γ γ' → EnvExt h (γ ﹐ v̲a̲r̲ i) γ'

  data EnvEq : (π : Wk Γ' Γ) → (γ' : Env Γ') → (γ : Env Γ) → Set where

    wk-env-ε    : EnvEq wk-ε ∗ ∗

    wk-env-val-cong : {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ} → (M : V̲a̲l̲ Γ X) → EnvEq π γ' γ → EnvEq (wk-cong π) (γ' ﹐ wk-v̲a̲l̲ π M) (γ ﹐ M)

    wk-env-comp-cong : {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ}
                       → (W : Γ ⊢ᶜ X) → (cs : CompStack Δ X) → {πᶜ : Wk Γ Δ} → .{wk≡ : ⟦ πᶜ ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → .{wk≡' : ⟦ wk-trans π πᶜ ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → EnvEq π γ' γ
                       → EnvEq (wk-cong π) ((γ' ﹐﹝ wk-comp π W ╎ cs ﹞) {π = wk-trans π πᶜ}
                               {wk≡ = wk≡'})
                               ((γ ﹐﹝ W ╎ cs ﹞) {π = πᶜ} {wk≡ = wk≡})

    wk-env-val-wk : {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ} → (M : V̲a̲l̲ Γ' X) → EnvEq π γ' γ → EnvEq (wk-wk π) (γ' ﹐ M) γ

    wk-env-comp-wk : {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ}
                       → (W : Γ' ⊢ᶜ X) → (cs : CompStack Δ X) → {πᶜ' : Wk Γ' Δ}
                       → .{wk≡' : ⟦ πᶜ' ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ}
                       → EnvEq π γ' γ
                       → EnvEq (wk-wk π) ((γ' ﹐﹝ W ╎ cs ﹞) {π = πᶜ'}
                               {wk≡ = wk≡'})
                               γ

  data WkExt : Wk Γ Δ → Set where

    wk-eq : (π : Wk Γ Γ) → WkExt π

    wk-ext : (π : Wk Γ Δ) → WkExt π → WkExt (wk-wk {A = A} π)

  enveq-id : {γ : Env Γ} → EnvEq wk-id γ γ
  enveq-id {γ = ∗} = wk-env-ε
  enveq-id {γ = γ ﹐ M} = subst (λ x → EnvEq (wk-cong wk-id) (γ ﹐ x) (γ ﹐ M)) (wk-v̲a̲l̲-id M) (wk-env-val-cong M enveq-id ) --wk-env-val-cong M enveq-id
  enveq-id {γ = (_﹐﹝_╎_﹞) {Γ = Γ} {Δ = Δ} γ W cs {π = π} {wk≡ = wk≡}} =
            let
              W≡ = wk-comp-id W
              π≡ = wk-trans-id {π = π}

              a0 = wk-env-comp-cong {π = wk-id} {γ' = γ} {γ = γ} W cs {πᶜ = π} {wk≡ = wk≡} {wk≡' = subst (λ x → ⟦ proj₂ x ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) (sym (pair-eq W≡ π≡)) wk≡} (enveq-id {γ = γ})

              eq1 : ((γ ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}) ≡ ((γ ﹐﹝ wk-comp wk-id W ╎ cs ﹞) {π = wk-trans wk-id π} {wk≡ = subst (λ x → ⟦ proj₂ x ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) (sym (pair-eq W≡ π≡)) wk≡})
              eq1 = dcong₂-irr ((λ x z → (γ ﹐﹝ proj₁ x ╎ cs ﹞) {π = proj₂ x} {wk≡ = z})) (sym (pair-eq W≡ π≡))

              goal : EnvEq (wk-cong {A = `V} wk-id) ((γ ﹐﹝ W ╎ cs ﹞) {π} {wk≡}) ((γ ﹐﹝ W ╎ cs ﹞) {π} {wk≡})
              goal =  subst (λ x → EnvEq (wk-cong {A = `V} wk-id) x ((γ ﹐﹝ W ╎ cs ﹞) {π} {wk≡}) ) (sym eq1) a0
            in
            goal

  env-id : {γ γ' : Env Γ} → EnvEq wk-id γ γ' → γ ≡ γ'
  env-id {γ = γ} {γ' = γ'} wk-env-ε = refl
  env-id {γ = γ ﹐ _} {γ' = γ' ﹐ M} (wk-env-val-cong M ϖ) = cong₂ (λ x y → x ﹐ y) (env-id ϖ) (wk-v̲a̲l̲-id M)
  env-id {γ = (γ ﹐﹝ _ ╎ _ ﹞) {π = π'} {wk≡ = wk≡'}} {γ' = (γ' ﹐﹝ W ╎ cs ﹞) {π = π} {wk≡ = wk≡}} (wk-env-comp-cong W cs ϖ) = --{!!}
              let
                γ≡ = env-id ϖ
                π≡ : wk-trans wk-id π ≡ π
                π≡ = wk-trans-id
                W≡ : wk-comp wk-id W ≡ W
                W≡ = wk-comp-id W

                goal : γ ﹐﹝ wk-comp wk-id W ╎ cs ﹞ ≡ γ' ﹐﹝ W ╎ cs ﹞
                goal = dcong₂-irr ((λ x z → ((proj₁ x) ﹐﹝ proj₁ (proj₂ x) ╎ cs ﹞) {π = proj₂ (proj₂ x)} {wk≡ = z})) {y₁ = wk≡'} {y₂ = wk≡} (pair-eq γ≡ (pair-eq W≡ π≡))
              in
              goal


  wk-ext-trans : {π₁ : Wk Γ Δ} {π₂ : Wk Δ Ψ} → WkExt π₁ → WkExt π₂ → WkExt (wk-trans π₁ π₂)
  wk-ext-trans (wk-eq π₁) (wk-eq π₂) = wk-eq (wk-trans π₁ π₂)
  wk-ext-trans (wk-eq π₁) (wk-ext {A = A} π₂ we₂) =
               let
                 a0 : WkExt (wk-wk {A = A} π₂)
                 a0 = wk-ext π₂ we₂
                 a1 : WkExt (wk-trans wk-id (wk-wk {A = A} π₂))
                 a1 = subst (λ x → WkExt x) (sym wk-trans-id) a0
                 a2 : WkExt (wk-trans π₁ (wk-wk {A = A} π₂))
                 a2 = subst (λ x → WkExt (wk-trans x (wk-wk {A = A} π₂))) (sym wk-id-id) a1
               in
               a2
  wk-ext-trans (wk-ext π₁ we₁) (wk-eq π₂) = wk-ext (wk-trans π₁ π₂) (wk-ext-trans we₁ (wk-eq π₂))
  wk-ext-trans (wk-ext π₁ we₁) (wk-ext π₂ we₂) = wk-ext (wk-trans π₁ (wk-wk π₂)) (wk-ext-trans we₁ (wk-ext π₂ we₂))

  wk-ext-cong-lift : {π : Wk Γ Δ} → WkExt (wk-cong {A = A} π) → WkExt π
  wk-ext-cong-lift (wk-eq π) = wk-eq _

  wk-ext-wk-lift : {π : Wk Γ Δ} → WkExt (wk-wk {A = A} π) → WkExt π
  wk-ext-wk-lift (wk-eq (wk-wk π)) = ql (wk-absurd π wk-id) (WkExt π)
  wk-ext-wk-lift (wk-ext π we) = we


  env-eq-trans : {π₁ : Wk Γ Γ'} {π₂ : Wk Γ' Γ''} {γ : Env Γ} {γ' : Env Γ'} {γ'' : Env Γ''}
                 → WkExt π₁ → WkExt π₂ → EnvEq π₁ γ γ' → EnvEq π₂ γ' γ'' → EnvEq (wk-trans π₁ π₂) γ γ''
  env-eq-trans {π₁ = wk-ε} {π₂ = π₂} {γ = γ} {γ' = γ'} {γ'' = γ''} (wk-eq π) we₂ wk-env-ε ϖ₂ = ϖ₂
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {γ = γ ﹐ _} {γ' = γ' ﹐ M} {γ'' = γ'' ﹐ M₁} we₁ we₂ (wk-env-val-cong M ϖ₁) (wk-env-val-cong M₁ ϖ₂) =
               let
                 a0 = env-eq-trans (wk-ext-cong-lift we₁) (wk-ext-cong-lift we₂) ϖ₁ ϖ₂
                 a1 : EnvEq (wk-cong (wk-trans π₁ π₂)) (γ ﹐ wk-v̲a̲l̲ (wk-trans π₁ π₂) M₁) (γ'' ﹐ M₁)
                 a1 = wk-env-val-cong M₁ a0
                 a2 : EnvEq (wk-cong (wk-trans π₁ π₂)) (γ ﹐ wk-v̲a̲l̲ π₁ (wk-v̲a̲l̲ π₂ M₁)) (γ'' ﹐ M₁)
                 a2 = subst (λ x → EnvEq (wk-cong (wk-trans π₁ π₂)) (γ ﹐ x) (γ'' ﹐ M₁)) (sym (wk-v̲a̲l̲-trans M₁ π₁ π₂)) a1
               in
               a2
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {γ = γ ﹐ _} {γ' = γ' ﹐ M} {γ'' = ∗} (wk-eq .(wk-cong π₁)) we₂ (wk-env-val-cong M ϖ₁) (wk-env-val-wk M₁ ϖ₂) =
               wk-env-val-wk (wk-v̲a̲l̲ π₁ M) (env-eq-trans (wk-eq π₁) (wk-ext-wk-lift we₂) ϖ₁ ϖ₂)
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {γ = γ ﹐ _} {γ' = γ' ﹐ M} {γ'' = γ'' ﹐ M₂} (wk-eq .(wk-cong π₁)) we₂ (wk-env-val-cong M ϖ₁) (wk-env-val-wk M₁ ϖ₂) =
               let
                 a0 = env-eq-trans (wk-eq π₁) (wk-ext-wk-lift we₂) ϖ₁ ϖ₂
                 a1 : EnvEq (wk-wk (wk-trans π₁ π₂)) (γ ﹐ M₁) (γ'' ﹐ M₂)
                 a1 = wk-env-val-wk M₁ a0
               in
               wk-env-val-wk (wk-v̲a̲l̲ π₁ M) a0
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {γ = γ ﹐ _} {γ' = γ' ﹐ M} {γ'' = γ'' ﹐﹝ W ╎ cs ﹞} (wk-eq .(wk-cong π₁)) we₂ (wk-env-val-cong M ϖ₁) (wk-env-val-wk M₁ ϖ₂) =
               let
                 a0 = env-eq-trans (wk-eq π₁) (wk-ext-wk-lift we₂) ϖ₁ ϖ₂
                 a1 : EnvEq (wk-wk (wk-trans π₁ π₂)) (γ ﹐ M₁) (γ'' ﹐﹝ W ╎ cs ﹞)
                 a1 = wk-env-val-wk M₁ a0
               in
               wk-env-val-wk (wk-v̲a̲l̲ π₁ M) a0
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-cong π₂} {γ = (γ ﹐﹝ _ ╎ _ ﹞) {wk≡ = wk≡₁}} {γ' = (γ' ﹐﹝ _ ╎ _ ﹞) {wk≡ = wk≡₂}} {γ'' = (γ'' ﹐﹝ _ ╎ _ ﹞) {π = π₃} {wk≡ = wk≡₃}} (wk-eq π) we₂ (wk-env-comp-cong W cs {wk≡ = wk≡₄} {wk≡' = wk≡₅} ϖ₁) (wk-env-comp-cong W₁ cs₁ {wk≡ = wk≡₆} {wk≡' = wk≡₇} ϖ₂) = --{!!}
              let
                a0 = env-eq-trans (wk-eq π₁) (wk-ext-cong-lift we₂) ϖ₁ ϖ₂

                a1 : EnvEq (wk-cong (wk-trans π₁ π₂)) ((γ ﹐﹝ wk-comp (wk-trans π₁ π₂) W₁ ╎ cs ﹞) {π = wk-trans (wk-trans π₁ π₂) π₃} {wk≡ = subst (λ x → ⟦ proj₂ x ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) (pair-eq (wk-comp-trans W₁ π₁ π₂) (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})) wk≡₁}) ((γ'' ﹐﹝ W₁ ╎ cs ﹞) {π = π₃} {wk≡ = wk≡₃})
                a1 = wk-env-comp-cong W₁ cs {πᶜ = π₃} {wk≡ = wk≡₃} {wk≡' = subst (λ x → ⟦ proj₂ x ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) (pair-eq (wk-comp-trans W₁ π₁ π₂) (wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃})) wk≡₁} a0

                π≡ : wk-trans π₁ (wk-trans π₂ π₃) ≡ wk-trans (wk-trans π₁ π₂) π₃
                π≡ = wk-assoc {π₁ = π₁} {π₂ = π₂} {π₃ = π₃}
                W≡ : wk-comp π₁ (wk-comp π₂ W₁) ≡ wk-comp (wk-trans π₁ π₂) W₁
                W≡ = wk-comp-trans W₁ π₁ π₂

                eq2 :    ((γ ﹐﹝ wk-comp π₁ (wk-comp π₂ W₁) ╎ cs ﹞) {π = wk-trans π₁ (wk-trans π₂ π₃)} {wk≡ = wk≡₁})
                       ≡ ((γ ﹐﹝ wk-comp (wk-trans π₁ π₂) W₁ ╎ cs ﹞) {π = wk-trans (wk-trans π₁ π₂) π₃} {wk≡ = subst (λ x → ⟦ proj₂ x ⟧ʷ ⟦ γ ⟧ᴱ ≡ ⟦ topCsEnv cs ⟧ᴱ) (pair-eq W≡ π≡) wk≡₁})
                eq2 = dcong₂-irr ((λ x z → (γ ﹐﹝ proj₁ x ╎ cs ﹞) {π = proj₂ x} {wk≡ = z})) (pair-eq W≡ π≡)

                a2 : EnvEq (wk-cong (wk-trans π₁ π₂)) ((γ ﹐﹝ wk-comp π₁ (wk-comp π₂ W₁) ╎ cs ﹞) {π = wk-trans π₁ (wk-trans π₂ π₃)} {wk≡ = wk≡₁}) ((γ'' ﹐﹝ W₁ ╎ cs ﹞) {π = π₃} {wk≡ = wk≡₃})
                a2 = subst (λ x → EnvEq (wk-cong (wk-trans π₁ π₂)) x ((γ'' ﹐﹝ W₁ ╎ cs ﹞) {π = π₃} {wk≡ = wk≡₃})) (sym eq2) a1
              in
              a2

  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {γ = γ} {γ' = γ'} {γ'' = ∗} (wk-eq .(wk-cong π₁)) we₂ (wk-env-comp-cong W cs ϖ₁) (wk-env-comp-wk W₁ cs₁ ϖ₂) =
               wk-env-comp-wk (wk-comp π₁ W) cs (env-eq-trans (wk-eq π₁) (wk-ext-wk-lift we₂) ϖ₁ ϖ₂)
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {γ = (γ ﹐﹝ _ ╎ _ ﹞) {π = πₓ} {wk≡ = wk≡}} {γ' = γ'} {γ'' = γ'' ﹐ M} (wk-eq .(wk-cong π₁)) we₂ (wk-env-comp-cong W cs ϖ₁) (wk-env-comp-wk W₁ cs₁ ϖ₂) =
               let
                 a0 = env-eq-trans (wk-eq π₁) (wk-ext-wk-lift we₂) ϖ₁ ϖ₂
                 a1 = wk-env-comp-wk W₁ cs {πᶜ' = wk-trans π₁ _} {wk≡' = wk≡} a0
               in
               wk-env-comp-wk (wk-comp π₁ W) cs a0
  env-eq-trans {π₁ = wk-cong π₁} {π₂ = wk-wk π₂} {γ = (γ ﹐﹝ _ ╎ _ ﹞) {π = πₓ} {wk≡ = wk≡}} {γ' = γ' ﹐﹝ _ ╎ _ ﹞} {γ'' = γ'' ﹐﹝ W₂ ╎ cs₂ ﹞} (wk-eq .(wk-cong π₁)) we₂ (wk-env-comp-cong W cs ϖ₁) (wk-env-comp-wk W₁ cs₁ ϖ₂) =
               let
                 a0 = env-eq-trans (wk-eq π₁) (wk-ext-wk-lift we₂) ϖ₁ ϖ₂
                 a1 = wk-env-comp-wk W₁ cs {πᶜ' = wk-trans π₁ _} {wk≡' = wk≡} a0
               in
               wk-env-comp-wk (wk-comp π₁ W) cs a0
  env-eq-trans {π₁ = wk-wk π₁} {π₂ = π₂} {γ = γ ﹐ _} {γ' = γ'} {γ'' = γ''} (wk-eq π) we₂ (wk-env-val-wk M ϖ₁) ϖ₂ = ql (wk-absurd π₁ wk-id) _
  env-eq-trans {π₁ = wk-wk π₁} {π₂ = π₂} {γ = γ} {γ' = γ'} {γ'' = γ''} (wk-eq π) we₂ (wk-env-comp-wk W cs ϖ₁) ϖ₂ = ql (wk-absurd π₁ wk-id) _
  env-eq-trans {π₁ = wk-wk π₁} {π₂ = π₂} {γ = γ} {γ' = γ'} {γ'' = γ''} (wk-ext π we₁) (wk-eq π₃) (wk-env-val-wk M ϖ₁) ϖ₂ = wk-env-val-wk M (env-eq-trans we₁ (wk-eq π₂) ϖ₁ ϖ₂)
  env-eq-trans {π₁ = wk-wk π₁} {π₂ = π₂} {γ = γ} {γ' = γ'} {γ'' = γ''} (wk-ext π we₁) (wk-ext π₃ we₂) (wk-env-val-wk M ϖ₁) ϖ₂ = wk-env-val-wk M (env-eq-trans we₁ (wk-ext π₃ we₂) ϖ₁ ϖ₂)
  env-eq-trans {π₁ = wk-wk π₁} {π₂ = π₂} {γ = γ} {γ' = γ'} {γ'' = γ''} (wk-ext π we₁) (wk-eq π₃) (wk-env-comp-wk W cs ϖ₁) ϖ₂ = wk-env-comp-wk W cs (env-eq-trans we₁ (wk-eq π₂) ϖ₁ ϖ₂)
  env-eq-trans {π₁ = wk-wk π₁} {π₂ = π₂} {γ = γ} {γ' = γ'} {γ'' = γ''} (wk-ext π we₁) (wk-ext π₃ we₂) (wk-env-comp-wk W cs ϖ₁) ϖ₂ = wk-env-comp-wk W cs (env-eq-trans we₁ (wk-ext π₃ we₂) ϖ₁ ϖ₂)


  env-eq-sem : {π : Wk Γ' Γ} {γ' : Env Γ'} {γ : Env Γ} → EnvEq π γ' γ → ⟦ π ⟧ʷ ⟦ γ' ⟧ᴱ ≡ ⟦ γ ⟧ᴱ
  env-eq-sem {π = π} {γ' = γ'} {γ = γ} wk-env-ε = refl
  env-eq-sem {π = π} {γ' = γ'} {γ = γ} (wk-env-val-cong {π = π₁} {γ' = γ''} {γ = γ₁} M ϖ) =
             let
               IH = env-eq-sem ϖ

               goal : ⟦ wk-cong π₁ ⟧ʷ (⟦ γ'' ⟧ᴱ , ⟦ toVal (wk-v̲a̲l̲ π₁ M) ⟧ᵛ ⟦ γ'' ⟧ᴱ) ≡ (⟦ γ₁ ⟧ᴱ , ⟦ toVal M ⟧ᵛ ⟦ γ₁ ⟧ᴱ)
               goal =   ⟦ π₁ ⟧ʷ ⟦ γ'' ⟧ᴱ , ⟦ toVal (wk-v̲a̲l̲ π₁ M) ⟧ᵛ ⟦ γ'' ⟧ᴱ
                      ≡⟨ cong (λ x → ⟦ π₁ ⟧ʷ ⟦ γ'' ⟧ᴱ , ⟦ x ⟧ᵛ ⟦ γ'' ⟧ᴱ) (sym (wk-comm {M = M} {π = π₁})) ⟩
                        ⟦ π₁ ⟧ʷ ⟦ γ'' ⟧ᴱ , ⟦ toVal M ⟧ᵛ (⟦ π₁ ⟧ʷ ⟦ γ'' ⟧ᴱ)
                      ≡⟨ cong (λ x → x , ⟦ toVal M ⟧ᵛ x) IH ⟩
                        (⟦ γ₁ ⟧ᴱ , ⟦ toVal M ⟧ᵛ ⟦ γ₁ ⟧ᴱ) ∎

             in
             goal
  env-eq-sem {π = π} {γ' = γ'} {γ = γ} (wk-env-comp-cong {π = π₁} {γ' = γ''} {γ = γ₁} W cs ϖ) =
             let
               IH = env-eq-sem ϖ
               goal : ⟦ wk-cong π₁ ⟧ʷ (⟦ γ'' ⟧ᴱ , (⟦ π₁ ⟧ʷ ； ⟦ W ⟧ᶜ) ⟦ γ'' ⟧ᴱ ⟦ cs ⟧ᴷ) ≡ (⟦ γ₁ ⟧ᴱ , ⟦ W ⟧ᶜ ⟦ γ₁ ⟧ᴱ ⟦ cs ⟧ᴷ)
               goal =   ⟦ π₁ ⟧ʷ ⟦ γ'' ⟧ᴱ , ⟦ W ⟧ᶜ (⟦ π₁ ⟧ʷ ⟦ γ'' ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                      ≡⟨ cong (λ x → x , ⟦ W ⟧ᶜ x (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) IH ⟩
                        ⟦ γ₁ ⟧ᴱ , ⟦ W ⟧ᶜ ⟦ γ₁ ⟧ᴱ (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀) ∎
             in
             goal
  env-eq-sem {π = π} {γ' = γ'} {γ = γ} (wk-env-val-wk M ϖ) = env-eq-sem ϖ
  env-eq-sem {π = π} {γ' = γ'} {γ = γ} (wk-env-comp-wk W cs ϖ) = env-eq-sem ϖ

  enveq-eq : {π : Wk Γ Γ'} {γ : Env Γ} {γ' : Env Γ'} → EnvEq π γ γ' → ⟦ γ' ⟧ᴱ ≡ ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ
  enveq-eq {π = wk-ε} {γ = ∗} {γ' = ∗} wk-env-ε = refl
  enveq-eq {π = wk-cong π} {γ = γ ﹐ M} {γ' = γ' ﹐ M₁} (wk-env-val-cong M₂ ϖ) =
                let
                  IH = enveq-eq ϖ
                in
                  ⟦ γ' ⟧ᴱ , ⟦ toVal M₁ ⟧ᵛ ⟦ γ' ⟧ᴱ
                ≡⟨ cong (λ x → x , ⟦ toVal M₁ ⟧ᵛ x) IH ⟩
                  ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ toVal M₁ ⟧ᵛ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ)
                ≡⟨ cong (λ x → ⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ x ⟧ᵛ ⟦ γ ⟧ᴱ) (wk-comm {M = M₁} {π = π}) ⟩
                ⟦ wk-cong π ⟧ʷ (⟦ γ ⟧ᴱ , ⟦ toVal (wk-v̲a̲l̲ π M₁) ⟧ᵛ ⟦ γ ⟧ᴱ) ∎
  enveq-eq {π = wk-cong π} {γ = γ ﹐ M} {γ' = γ' ﹐﹝ W ╎ cs ﹞} ()
  enveq-eq {π = wk-cong π} {γ = γ ﹐﹝ W ╎ cs ﹞} {γ' = γ' ﹐ M} ()
  enveq-eq {π = wk-cong π} {γ = γ ﹐﹝ W ╎ cs ﹞} {γ' = γ' ﹐﹝ W₁ ╎ cs₁ ﹞} (wk-env-comp-cong W₂ cs₂ ϖ) =
                let
                  IH = enveq-eq ϖ
                in
                  (⟦ γ' ⟧ᴱ , ⟦ W₁ ⟧ᶜ ⟦ γ' ⟧ᴱ (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀))
                ≡⟨ cong (λ x → x , ⟦ W₁ ⟧ᶜ x (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) IH ⟩
                  (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ , ⟦ W₁ ⟧ᶜ (⟦ π ⟧ʷ ⟦ γ ⟧ᴱ) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) ∎
  enveq-eq {π = wk-wk π} {γ = γ ﹐ M} {γ' = ∗} (wk-env-val-wk M₁ ϖ) = enveq-eq ϖ
  enveq-eq {π = wk-wk π} {γ = γ ﹐ M} {γ' = γ' ﹐ M₁} (wk-env-val-wk M₂ ϖ) = enveq-eq ϖ
  enveq-eq {π = wk-wk π} {γ = γ ﹐ M} {γ' = γ' ﹐﹝ W ╎ cs ﹞} (wk-env-val-wk M₁ ϖ) = enveq-eq ϖ
  enveq-eq {π = wk-wk π} {γ = γ ﹐﹝ W ╎ cs ﹞} {γ' = ∗} (wk-env-comp-wk W₁ cs₁ ϖ) = enveq-eq ϖ
  enveq-eq {π = wk-wk π} {γ = γ ﹐﹝ W ╎ cs ﹞} {γ' = γ' ﹐ M} (wk-env-comp-wk W₁ cs₁ ϖ) = enveq-eq ϖ
  enveq-eq {π = wk-wk π} {γ = γ ﹐﹝ W ╎ cs ﹞} {γ' = γ' ﹐﹝ W₁ ╎ cs₁ ﹞} (wk-env-comp-wk W₂ cs₂ ϖ) = enveq-eq ϖ

  ----------------------------------------------------------
  -- GARBAGE COLLECTION (not used)
  ----------------------------------------------------------
  {-
  pred-ctx-eq : Γ ∙ X ≡ Δ ∙ X → Γ ≡ Δ
  pred-ctx-eq refl = refl

  ctx-absurd : ε ≡ Γ ∙ X → ⊥
  ctx-absurd ()

  subst-lemma-var : (i : Γ ∋ X) → (i' : Γ' ∋ X) → (Γ≡Γ' : Γ ≡ Γ') → (i≅i' : i ≅ i')
         → subst (λ x → Val x X) Γ≡Γ' (var i) ≅ Val.var (subst (λ x → x) (H.≅-to-type-≡ i≅i') i)
  subst-lemma-var h h refl _≅_.refl = _≅_.refl
  subst-lemma-var h (t i') refl ()
  subst-lemma-var (t i) h refl ()
  subst-lemma-var (t i) (t i') refl _≅_.refl = _≅_.refl

  subst-lemma-pair : (M₁ : Val Γ X) → (M₂ : Val Γ Y) → (M₁' : Val Γ' X) → (M₂' : Val Γ' Y) → (Γ≡Γ' : Γ ≡ Γ') → (M₁≅M₁' : M₁ ≅ M₁') → (M₂≅M₂' : M₂ ≅ M₂')
                   → subst (λ x → Val x (X `× Y)) Γ≡Γ' (pair M₁ M₂) ≅ Val.pair (subst (λ x → x) (H.≅-to-type-≡ M₁≅M₁') M₁) (subst (λ x → x) (H.≅-to-type-≡ M₂≅M₂') M₂)
  subst-lemma-pair M₁ M₂ M₁' M₂' refl _≅_.refl _≅_.refl = _≅_.refl

  subst-lemma-pm : (M : Val Γ (A `× B)) → (N : Val (Γ ∙ A ∙ B) Z) → (M' : Val Γ' (A `× B)) → (N' : Val (Γ' ∙ A ∙ B) Z) → (Γ≡Γ' : Γ ≡ Γ') → (M≅M' : M ≅ M') → (N≅N' : N ≅ N')
                   → subst (λ x → Val x Z) Γ≡Γ' (pm M N) ≅ Val.pm (subst (λ x → x) (H.≅-to-type-≡ M≅M') M) (subst (λ x → x) (H.≅-to-type-≡ N≅N') N)
  subst-lemma-pm M N M' N' refl _≅_.refl _≅_.refl = _≅_.refl

  subst-lemma-lam : (W : Comp (Γ ∙ X) Y) → (W' : Comp (Γ' ∙ X) Y) → (Γ≡Γ' : Γ ≡ Γ') → (W≅W' : W ≅ W')
                   → subst (λ x → Val x (X `⇒ Y)) Γ≡Γ' (lam W) ≅ Val.lam (subst (λ x → x) (H.≅-to-type-≡ W≅W') W)
  subst-lemma-lam W W' refl _≅_.refl = _≅_.refl

  subst-lemma-return : (M : Val Γ X) → (M' : Val Γ' X) → (Γ≡Γ' : Γ ≡ Γ') → (M≅M' : M ≅ M')
                   → subst (λ x → Comp x X) Γ≡Γ' (return M) ≅ Comp.return (subst (λ x → x) (H.≅-to-type-≡ M≅M') M)
  subst-lemma-return M M' refl _≅_.refl = _≅_.refl

  subst-lemma-pm-comp : (M : Val Γ (A `× B)) → (N : (Γ ∙ A ∙ B) ⊢ᶜ C)
                      → (M' : Val Γ' (A `× B)) → (N' : (Γ' ∙ A ∙ B) ⊢ᶜ C)
                      → (Γ≡Γ' : Γ ≡ Γ') → (M≅M' : M ≅ M') → (N≅N' : N ≅ N')
                      → subst (λ x → x ⊢ᶜ C) Γ≡Γ' (Comp.pm M N) ≅ Comp.pm (subst (λ x → x) (H.≅-to-type-≡ M≅M') M) (subst (λ x → x) (H.≅-to-type-≡ N≅N') N)
  subst-lemma-pm-comp M N M' N' refl _≅_.refl _≅_.refl = _≅_.refl

  subst-lemma-push : (M : Γ ⊢ᶜ A) → (N : (Γ ∙ A) ⊢ᶜ B)
                  → (M' : Γ' ⊢ᶜ A) → (N' : (Γ' ∙ A) ⊢ᶜ B)
                  → (Γ≡Γ' : Γ ≡ Γ') → (M≅M' : M ≅ M') → (N≅N' : N ≅ N')
                  → subst (λ x → x ⊢ᶜ B) Γ≡Γ' (Comp.push M N) ≅ Comp.push (subst (λ x → x) (H.≅-to-type-≡ M≅M') M) (subst (λ x → x) (H.≅-to-type-≡ N≅N') N)
  subst-lemma-push M N M' N' refl _≅_.refl _≅_.refl = _≅_.refl

  subst-lemma-app : (f : Val Γ (A `⇒ B)) → (x : Val Γ A)
                  → (f' : Val Γ' (A `⇒ B)) → (x' : Val Γ' A)
                  → (Γ≡Γ' : Γ ≡ Γ') → (f≅f' : f ≅ f') → (x≅x' : x ≅ x')
                  → subst (λ y → y ⊢ᶜ B) Γ≡Γ' (Comp.app f x) ≅ Comp.app (subst (λ z → z) (H.≅-to-type-≡ f≅f') f) (subst (λ z → z) (H.≅-to-type-≡ x≅x') x)
  subst-lemma-app f x f' x' refl _≅_.refl _≅_.refl = _≅_.refl

  subst-lemma-var-comp : (M : Val Γ `V) → (M' : Val Γ' `V) → (Γ≡Γ' : Γ ≡ Γ') → (M≅M' : M ≅ M')
                      → subst (λ x → x ⊢ᶜ X) Γ≡Γ' (Comp.var {A = X} M) ≅ Comp.var {A = X} (subst (λ x → x) (H.≅-to-type-≡ M≅M') M)
  subst-lemma-var-comp M M' refl _≅_.refl = _≅_.refl

  subst-lemma-sub : (M : (Γ ∙ `V) ⊢ᶜ A) → (N : Γ ⊢ᶜ A)
                  → (M' : (Γ' ∙ `V) ⊢ᶜ A) → (N' : Γ' ⊢ᶜ A)
                  → (Γ≡Γ' : Γ ≡ Γ') → (M≅M' : M ≅ M') → (N≅N' : N ≅ N')
                  → subst (λ x → x ⊢ᶜ A) Γ≡Γ' (Comp.sub M N)
                  ≅ Comp.sub (subst (λ x → x) (H.≅-to-type-≡ M≅M') M) (subst (λ x → x) (H.≅-to-type-≡ N≅N') N)
  subst-lemma-sub M N M' N' refl _≅_.refl _≅_.refl = _≅_.refl

  mem-gc : Γ ∋ X → Σ[ Γ' ∈ Ctx ] ((Γ' ∋ X) × (Wk Γ Γ'))
  mem-gc {Γ = Γ ∙ X} h = ε ∙ X , h , wk-cong wk-wk-ε
  mem-gc (t i) =
    let
      l = mem-gc i
    in
    proj₁ l , proj₁ (proj₂ l) , wk-wk (proj₂ (proj₂ l))

  mutual

    val-gc : Val Γ X → Σ[ Γ' ∈ Ctx ] ((Val Γ' X) × (Wk Γ Γ'))
    val-gc (var i) = let l = mem-gc i in proj₁ l , var (proj₁ (proj₂ l)) , proj₂ (proj₂ l)
    val-gc (lam {A = X} W) with comp-gc W
    ... | Γ' ∙ X , W' , wk-cong π' = Γ' , lam W' , π'
    ... | ε , W' , wk-wk π' = ε , lam (wk-comp (wk-wk wk-id) W') , π'
    ... | Γ' ∙ X , W' , wk-wk π' = Γ' ∙ X , lam (wk-comp (wk-wk wk-id) W') , π'
    val-gc {Γ = Γ} (pair M₁ M₂) =
            let
              v₁ = val-gc M₁
              M₁' = proj₁ (proj₂ v₁)
              π₁ = proj₂ (proj₂ v₁)
              v₂ = val-gc M₂
              M₂' = proj₁ (proj₂ v₂)
              π₂ = proj₂ (proj₂ v₂)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , pair (wk-val π₁' M₁') (wk-val π₂' M₂') , π
    val-gc (pm {A = X} {B = Y} {C = Z} M N) with val-gc N
    ... | Γ₂ , N₂ , wk-cong (wk-cong π₂) =
            let
              v = val-gc M
              M₁ = proj₁ (proj₂ v)
              π₁ = proj₂ (proj₂ v)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , pm (wk-val π₁' M₁) (wk-val (wk-cong (wk-cong π₂')) N₂) , π
    ... | Γ₂ ∙ Y , N₂ , wk-cong (wk-wk π₂) =
            let
              v = val-gc M
              M₁ = proj₁ (proj₂ v)
              π₁ = proj₂ (proj₂ v)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , pm (wk-val π₁' M₁) (wk-val (wk-cong (wk-wk π₂')) N₂) , π
    ... | Γ₂ , N₂ , wk-wk (wk-cong π₂) =
            let
              v = val-gc M
              M₁ = proj₁ (proj₂ v)
              π₁ = proj₂ (proj₂ v)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , pm (wk-val π₁' M₁) (wk-val (wk-wk (wk-cong π₂')) N₂) , π
    ... | Γ₂ , N₂ , wk-wk (wk-wk π₂) =
            let
              v = val-gc M
              M₁ = proj₁ (proj₂ v)
              π₁ = proj₂ (proj₂ v)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , pm (wk-val π₁' M₁) (wk-val (wk-wk (wk-wk π₂')) N₂) , π
    val-gc unit = ε , unit , wk-wk-ε

    comp-gc : Comp Γ X → Σ[ Γ' ∈ Ctx ] ((Comp Γ' X) × (Wk Γ Γ'))
    comp-gc (return M) = let v = val-gc M in proj₁ v , return (proj₁ (proj₂ v)) , proj₂ (proj₂ v)
    comp-gc (pm {A = X} {B = Y} {C = Z} M W) with comp-gc W
    ... | Γ₂ , W₂ , wk-cong (wk-cong π₂) =
            let
              v = val-gc M
              M₁ = proj₁ (proj₂ v)
              π₁ = proj₂ (proj₂ v)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , pm (wk-val π₁' M₁) (wk-comp (wk-cong (wk-cong π₂')) W₂) , π
    ... | Γ₂ ∙ Y , W₂ , wk-cong (wk-wk π₂) =
            let
              v = val-gc M
              M₁ = proj₁ (proj₂ v)
              π₁ = proj₂ (proj₂ v)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , pm (wk-val π₁' M₁) (wk-comp (wk-cong (wk-wk π₂')) W₂) , π
    ... | Γ₂ , W₂ , wk-wk (wk-cong π₂) =
            let
              v = val-gc M
              M₁ = proj₁ (proj₂ v)
              π₁ = proj₂ (proj₂ v)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , pm (wk-val π₁' M₁) (wk-comp (wk-wk (wk-cong π₂')) W₂) , π
    ... | Γ₂ , W₂ , wk-wk (wk-wk π₂) =
            let
              v = val-gc M
              M₁ = proj₁ (proj₂ v)
              π₁ = proj₂ (proj₂ v)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , pm (wk-val π₁' M₁) (wk-comp (wk-wk (wk-wk π₂')) W₂) , π
    comp-gc (push {A = X} {B = Z} W₁ W₂) with comp-gc W₂
    ... | Γ₂' ∙ X , W₂' , wk-cong π₂' =
            let
              c = comp-gc W₁
              W₁' = proj₁ (proj₂ c)
              π₁' = proj₂ (proj₂ c)
              j = wk-join π₁' π₂'
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁'' = proj₁ (proj₂ (proj₂ j))
              π₂'' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , push (wk-comp π₁'' W₁') (wk-comp (wk-cong π₂'') W₂') , π
    ... | ε , W₂' , wk-wk π₂' =
            let
              c = comp-gc W₁
              W₁' = proj₁ (proj₂ c)
              π₁' = proj₂ (proj₂ c)
              j = wk-join π₁' π₂'
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁'' = proj₁ (proj₂ (proj₂ j))
              π₂'' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , push (wk-comp π₁'' W₁') (wk-comp (wk-wk π₂'') W₂') , π
    ... | Γ₂' ∙ x , W₂' , wk-wk π₂' =
            let
              c = comp-gc W₁
              W₁' = proj₁ (proj₂ c)
              π₁' = proj₂ (proj₂ c)
              j = wk-join π₁' π₂'
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁'' = proj₁ (proj₂ (proj₂ j))
              π₂'' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , push (wk-comp π₁'' W₁') (wk-comp (wk-wk π₂'') W₂') , π
    comp-gc (app M N) =
            let
              v₁ = val-gc M
              M' = proj₁ (proj₂ v₁)
              π₁ = proj₂ (proj₂ v₁)
              v₂ = val-gc N
              N' = proj₁ (proj₂ v₂)
              π₂ = proj₂ (proj₂ v₂)
              j = wk-join π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , app (wk-val π₁' M') (wk-val π₂' N') , π
    comp-gc (var M) =  let v = val-gc M in proj₁ v , var (proj₁ (proj₂ v)) , proj₂ (proj₂ v)
    comp-gc (sub {A = X} W₁ W₂)  with comp-gc W₁
    ... | Γ₁' ∙ X , W₁' , wk-cong π₁' =
            let
              c = comp-gc W₂
              W₂' = proj₁ (proj₂ c)
              π₂' = proj₂ (proj₂ c)
              j = wk-join π₁' π₂'
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁'' = proj₁ (proj₂ (proj₂ j))
              π₂'' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , sub (wk-comp (wk-cong π₁'') W₁') (wk-comp π₂'' W₂') , π
    ... | ε , W₁' , wk-wk π₁' =
            let
              c = comp-gc W₂
              W₂' = proj₁ (proj₂ c)
              π₂' = proj₂ (proj₂ c)
              j = wk-join π₁' π₂'
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁'' = proj₁ (proj₂ (proj₂ j))
              π₂'' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , sub (wk-comp (wk-wk π₁'') W₁') (wk-comp π₂'' W₂') , π
    ... | Γ₁' ∙ X' , W₁' , wk-wk π₁' =
            let
              c = comp-gc W₂
              W₂' = proj₁ (proj₂ c)
              π₂' = proj₂ (proj₂ c)
              j = wk-join π₁' π₂'
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁'' = proj₁ (proj₂ (proj₂ j))
              π₂'' = proj₂ (proj₂ (proj₂ j))
            in
            Γ' , sub (wk-comp (wk-wk π₁'') W₁') (wk-comp π₂'' W₂') , π
  -}
