{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Environments (R : Set) where

open import Agda.Primitive using (Level)

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Function.Base using (const; _∘_; _$_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; cong-app; icong; dcong₂; sym; trans; subst; subst₂)
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

  perm-E : Γ ↭ Γ' → ⟦ Γ ⟧ˣ → ⟦ Γ' ⟧ˣ
  perm-E refl E = E
  perm-E (prep X Γ↭Γ') E = perm-E Γ↭Γ' (proj₁ E) , proj₂ E
  perm-E (swap X Y Γ↭Γ') E = (perm-E Γ↭Γ' (proj₁ (proj₁ E)) , proj₂ E) , proj₂ (proj₁ E)
  perm-E (_↭_.trans Γ↭Γ' Γ↭Γ'') E = perm-E Γ↭Γ'' (perm-E Γ↭Γ' E)

  {-
  mutual

    perm-cs : Γ ↭ Γ' → CompStack Γ X → CompStack Γ' X
    perm-cs refl ◻ = ◻
    perm-cs refl ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡}) = ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡})
    perm-cs (prep X Γ↭Γ') ((W ⊲ γ ⦂⦂ cs) {π = π} {wk≡ = wk≡}) =
      let
        wk≡' : ⟦ proj₂ (proj₂ (perm-wk (prep X Γ↭Γ') π)) ⟧ʷ ⟦ perm-env (prep X Γ↭Γ') γ ⟧ᴱ ≡ ⟦ topCsEnv (perm-cs (proj₁ (proj₂ (perm-wk (prep X Γ↭Γ') π))) cs) ⟧ᴱ
        wk≡' = ⟦ proj₂ (proj₂ (perm-wk (prep X Γ↭Γ') π)) ⟧ʷ ⟦ perm-env (prep X Γ↭Γ') γ ⟧ᴱ
               ≡⟨ {!!} ⟩
               {!!}
               ≡⟨ {!!} ⟩
               ⟦ topCsEnv (perm-cs (proj₁ (proj₂ (perm-wk (prep X Γ↭Γ') π))) cs) ⟧ᴱ ∎
      in
      (perm-comp (prep _ (prep X Γ↭Γ')) W ⊲ perm-env (prep X Γ↭Γ') γ ⦂⦂ perm-cs (proj₁ (proj₂ (perm-wk (prep X Γ↭Γ') π))) cs) {π = proj₂ (proj₂ (perm-wk (prep X Γ↭Γ') π))} {wk≡ = {!!}}
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
    perm-env (swap X Y Γ↭Γ') (γ ﹐ M₁ ﹐ M) = perm-env Γ↭Γ' γ ﹐ perm-v̲a̲l̲ {!-m!} M ﹐ {!!}
    perm-env (swap X Y Γ↭Γ') (γ ﹐﹝ W ╎ cs ﹞ ﹐ M) = {!!}
    perm-env (swap X Y Γ↭Γ') (γ ﹐ M ﹐﹝ W ╎ cs ﹞) = {!!}
    perm-env (swap X Y Γ↭Γ') (γ ﹐﹝ W₁ ╎ cs₁ ﹞ ﹐﹝ W ╎ cs ﹞) = {!!}
    perm-env (_↭_.trans Γ↭Γ' Γ↭Γ'') ∗ = {!!}
    perm-env (_↭_.trans Γ↭Γ' Γ↭Γ'') (γ ﹐ M) = {!!}
    perm-env (_↭_.trans Γ↭Γ' Γ↭Γ'') (γ ﹐﹝ W ╎ cs ﹞) = {!!}

    perm-sem-env : (Γ↭Γ' : Γ ↭ Γ') → (γ : Env Γ) → ⟦ perm-env Γ↭Γ' γ ⟧ᴱ ≡ perm-E Γ↭Γ' ⟦ γ ⟧ᴱ
    perm-sem-env refl γ = {!!}
    perm-sem-env (prep X Γ↭Γ') γ = {!!}
    perm-sem-env (swap X Y Γ↭Γ') γ = {!!}
    perm-sem-env (_↭_.trans Γ↭Γ' Γ↭Γ'') γ = {!!}
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
  -- GARBAGE COLLECTION
  ----------------------------------------------------------

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

  ----

  {-
  mem-gc : Γ ∋ X → Σ[ Γ' ∈ Ctx ] ((Γ' ∋ X) × (Wk Γ Γ'))
  mem-gc {Γ = Γ ∙ X} h = ε ∙ X , h , wk-cong wk-wk-ε
  mem-gc (t i) =
    let
      l = mem-gc i
    in
    proj₁ l , proj₁ (proj₂ l) , wk-wk (proj₂ (proj₂ l))
  -}

  {-
  mem-gc-Γ-eq : (π : Wk Γ' Γ) → (i : Γ ∋ X) → (proj₁ (mem-gc i)) ≡ (proj₁ (mem-gc (wk-mem π i)))
  mem-gc-Γ-eq wk-ε ()
  mem-gc-Γ-eq (wk-cong π) Cx.h = refl
  mem-gc-Γ-eq (wk-cong π) (Cx.t i) = mem-gc-Γ-eq π i
  mem-gc-Γ-eq (wk-wk π) Cx.h = mem-gc-Γ-eq π h
  mem-gc-Γ-eq (wk-wk π) (Cx.t i) = mem-gc-Γ-eq π (t i)
  -}

  wk-mem-wk-eq : {Γ Γ' : Ctx} {X Y : Ty} → {i : Γ ∋ X} {i' : Γ' ∋ X} {π : Wk Γ Γ'} → i ≡ wk-mem π i' → t {B = Y} i ≡ wk-mem (wk-wk π) i'
  wk-mem-wk-eq {i = i} {i' = Cx.h} {π = wk-cong π} refl = refl
  wk-mem-wk-eq {i = i} {i' = Cx.h} {π = wk-wk π} refl = refl
  wk-mem-wk-eq {i = i} {i' = Cx.t i'} {π = wk-cong π} refl = refl
  wk-mem-wk-eq {i = i} {i' = Cx.t i'} {π = wk-wk π} refl = refl

  MemStr : (i : Γ ∋ X) → Set
  MemStr {Γ = Γ} {X = X} i = Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk Γ Γ' ] Σ[ i' ∈ (Γ' ∋ X) ] (i ≡ wk-mem π i')

  {-
  mem-gc : (i : Γ ∋ X) → MemStr i
  mem-gc {Γ = Γ ∙ X} h = ε ∙ X , wk-cong wk-wk-ε , h , refl
  mem-gc (t i) =
    let
      IH = mem-gc i
    in
    proj₁ IH , wk-wk (proj₁ (proj₂ IH)) , proj₁ (proj₂ (proj₂ IH)) , wk-mem-wk-eq (proj₂ (proj₂ (proj₂ IH)))
  -}

  mem-gc-helper : (i : (Γ ∋ X)) → Wk Γ (ε ∙ X)
  mem-gc-helper Cx.h = wk-cong wk-wk-ε
  mem-gc-helper (Cx.t i) = wk-wk (mem-gc-helper i)

  mutual
    mem-gc : (i : Γ ∋ X) → Σ[ iₘ ∈ MemStr i ] (∀ (iₛ : MemStr i) → Wk (proj₁ iₛ) (proj₁ iₘ))
    mem-gc {Γ = Γ ∙ X} h = (ε ∙ X , wk-cong wk-wk-ε , h , refl) , λ iₛ → mem-gc-helper (proj₁ (proj₂ (proj₂ iₛ)))
    mem-gc (t i) =
      let
        IH = mem-gc i
      in
      (proj₁ (proj₁ IH) , wk-wk (proj₁ (proj₂ (proj₁ IH))) , proj₁ (proj₂ (proj₂ (proj₁ IH))) , wk-mem-wk-eq (proj₂ (proj₂ (proj₂ (proj₁ IH))))) ,
      λ iₛ →
        let
          h = mem-gc-helper (proj₁ (proj₂ (proj₂ iₛ)))
        in
        subst (λ x → Wk (proj₁ iₛ) x) (sym (mem-gc-ctx i)) h

    mem-gc-ctx : (i : Γ ∋ X) → (proj₁ (proj₁ (mem-gc i))) ≡ ε ∙ X
    mem-gc-ctx Cx.h = refl
    mem-gc-ctx (Cx.t i) = mem-gc-ctx i



  {-
  record MemGC (i : Γ ∋ X) : Set where
    field
      mem-gc-Γ : Ctx
      mem-gc-i : mem-gc-Γ ∋ X
      mem-gc-π : Wk Γ mem-gc-Γ
      mem-gc-eq : (mem-gc i) ≡ (mem-gc-Γ , mem-gc-i , mem-gc-π)

  open MemGC

  mem-gc-rec : (i : Γ ∋ X) → MemGC i
  mem-gc-rec i =
    let
      M = mem-gc i
    in
    record { mem-gc-Γ = proj₁ M ; mem-gc-i = proj₁ (proj₂ M) ; mem-gc-π = proj₂ (proj₂ M) ; mem-gc-eq = refl }
  -}


  dproj₁-eq : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : A → Set ℓ₂} {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂} → (a₁ , b₁) ≡ (a₂ , b₂) → a₁ ≡ a₂
  dproj₁-eq refl = refl

  dproj₂-eq : {ℓ₁ ℓ₂ : Level} {A : Set ℓ₁} {B : A → Set ℓ₂} {a : A} {b₁ b₂ : B a} → (_,_ {B = B} a b₁) ≡ (_,_ {B = B} a b₂) → b₁ ≡ b₂
  dproj₂-eq refl = refl


  wk-proj₃ : Σ[ Γ' ∈ Ctx ] ((Γ' ∋ X) × (Wk Γ Γ')) → Σ[ Γ' ∈ Ctx ] ((Γ' ∋ X) × (Wk (Γ ∙ Y) Γ'))
  wk-proj₃ (Γ' , i' , π) = Γ' , i' , wk-wk π

  var-proj₂ : Σ[ Γ' ∈ Ctx ] ((Γ' ∋ X) × (Wk Γ Γ')) → Σ[ Γ' ∈ Ctx ] ((Val Γ' X) × (Wk Γ Γ'))
  var-proj₂ (Γ' , i' , π) = Γ' , var i' , π

  -------------------------------


  var-injective : {i i' : Γ ∋ X} → var i ≡ var i' → i ≡ i'
  var-injective refl = refl

  var-to-memstr : {i : Γ ∋ X} {M : Val Γ' X} {π : Wk Γ Γ'} → (var i ≡ wk-val π M) → Σ[ iₛ ∈ MemStr i ] (proj₁ iₛ ≡ Γ')
  var-to-memstr {Γ = Γ ∙ X} {Γ' = Γ' ∙ X} {i = Cx.h} {M = var Cx.h} {π = wk-cong π} refl = (Γ' ∙ X , wk-cong π , h , refl) , refl
  var-to-memstr {Γ = Γ} {Γ' = Γ'} {i = Cx.h} {M = var Cx.h} {π = wk-wk π} ()
  var-to-memstr {Γ = Γ} {Γ' = Γ'} {i = Cx.h} {M = var (Cx.t i)} {π = wk-wk π} ()
  var-to-memstr {Γ = Γ} {Γ' = Γ'} {i = Cx.t i} {M = var i₁} {π = wk-cong π} eq = (Γ' , wk-cong π , i₁ , var-injective eq) , refl
  var-to-memstr {Γ = Γ} {Γ' = Γ'} {i = Cx.t i} {M = var i₁} {π = wk-wk π} eq = (Γ' , wk-wk π , i₁ , var-injective eq) , refl

  ValStr : (M : Val Γ X) → Set
  ValStr {Γ = Γ} {X = X} M = Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk Γ Γ' ] Σ[ M' ∈ (Val Γ' X) ] (M ≡ wk-val π M')

  --ValMin : (M : Val Γ X) → Set
  --ValMin M = Σ[ Mₘ ∈ ValStr M ] (∀ (Mₛ : ValStr M) → Wk (proj₁ Mₛ) (proj₁ Mₘ))

  CompStr : (W : Comp Γ X) → Set
  CompStr {Γ = Γ} {X = X} W = Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk Γ Γ' ] Σ[ W' ∈ (Comp Γ' X) ] (W ≡ wk-comp π W')

  --CompMin : (W : Comp Γ X) → Set
  --CompMin W = Σ[ Wₘ ∈ CompStr W ] (∀ (Wₛ : CompStr W) → Wk (proj₁ Wₛ) (proj₁ Wₘ))

  val-lam-helper : (W : Comp (Γ ∙ X) Y) → CompStr W → ValStr (lam W)
  val-lam-helper W (ε , wk-wk π' , W' , eq) =
    let
      a0 : wk-comp (wk-cong π') (wk-comp (wk-wk wk-ε) W') ≡ wk-comp (wk-trans (wk-cong π') (wk-wk wk-ε)) W'
      a0 = wk-comp-trans W' (wk-cong π') (wk-wk wk-ε)
    in
    ε , π' , lam (wk-comp (wk-wk wk-id) W') , cong lam (Eq.trans (Eq.trans eq (cong (λ x → wk-comp x W') (sym wk-trans-id'))) (sym a0))
  val-lam-helper W (Γ' ∙ X , wk-cong π' , W' , eq) = Γ' , π' , lam W' , cong lam eq
  val-lam-helper {X = X} W (Γ' ∙ X' , wk-wk π' , W' , eq) =
    let
      a0 : wk-comp (wk-cong {A = X} π') (wk-comp (wk-wk wk-id) W') ≡ wk-comp (wk-trans (wk-cong π') (wk-wk (wk-cong wk-id))) W'
      a0 = wk-comp-trans W' (wk-cong π') (wk-wk wk-id)
      a1 : wk-comp (wk-wk π') W' ≡ wk-comp (wk-wk (wk-trans π' (wk-cong wk-id))) W'
      a1 = cong (λ x → wk-comp x W') (sym (cong wk-wk wk-trans-id'))
    in
    Γ' ∙ X' , π' , lam (wk-comp (wk-wk wk-id) W') , cong lam (Eq.trans (Eq.trans eq a1) (sym a0))


  val-pm-helper : (M : Val Γ (X `× Y)) → ValStr M → (N : Val (Γ ∙ X ∙ Y) Z) → ValStr N → ValStr (pm M N)
  val-pm-helper M v N (Cx.ε , wk-wk (wk-wk π₂) , N' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : N ≡ (wk-val (wk-cong (wk-cong π)) (wk-val (wk-wk (wk-wk π₂')) N'))
      eq₂'' =   N
               ≡⟨ eq₂ ⟩
                wk-val (wk-wk (wk-wk π₂)) N'
               ≡⟨ cong (λ x → wk-val (wk-wk (wk-wk x)) N') eq₂' ⟩
                wk-val (wk-wk (wk-wk (wk-trans π π₂'))) N'
               ≡⟨ refl ⟩
                wk-val (wk-wk ((wk-trans (wk-cong π) (wk-wk π₂')))) N'
               ≡⟨ refl ⟩
                wk-val (wk-trans (wk-cong (wk-cong π)) (wk-wk (wk-wk π₂'))) N'
               ≡⟨ sym (wk-val-trans N' (wk-cong (wk-cong π)) (wk-wk (wk-wk π₂'))) ⟩
                (wk-val (wk-cong (wk-cong π)) (wk-val (wk-wk (wk-wk π₂')) N')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-val (wk-wk (wk-wk π₂')) N') , cong₂ pm eq₁'' eq₂''
  val-pm-helper M v N (Γ' Cx.∙ X , wk-wk (wk-wk π₂) , N' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : N ≡ (wk-val (wk-cong (wk-cong π)) (wk-val (wk-wk (wk-wk π₂')) N'))
      eq₂'' =   N
               ≡⟨ eq₂ ⟩
                wk-val (wk-wk (wk-wk π₂)) N'
               ≡⟨ cong (λ x → wk-val (wk-wk (wk-wk x)) N') eq₂' ⟩
                wk-val (wk-wk (wk-wk (wk-trans π π₂'))) N'
               ≡⟨ refl ⟩
                wk-val (wk-wk ((wk-trans (wk-cong π) (wk-wk π₂')))) N'
               ≡⟨ refl ⟩
                wk-val (wk-trans (wk-cong (wk-cong π)) (wk-wk (wk-wk π₂'))) N'
               ≡⟨ sym (wk-val-trans N' (wk-cong (wk-cong π)) (wk-wk (wk-wk π₂'))) ⟩
                (wk-val (wk-cong (wk-cong π)) (wk-val (wk-wk (wk-wk π₂')) N')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-val (wk-wk (wk-wk π₂')) N') , cong₂ pm eq₁'' eq₂''
  val-pm-helper M v N (Γ' Cx.∙ X , wk-wk (wk-cong π₂) , N' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : N ≡ (wk-val (wk-cong (wk-cong π)) (wk-val (wk-wk (wk-cong π₂')) N'))
      eq₂'' =   N
               ≡⟨ eq₂ ⟩
                wk-val (wk-wk (wk-cong π₂)) N'
               ≡⟨ cong (λ x → wk-val (wk-wk (wk-cong x)) N') eq₂' ⟩
                wk-val (wk-wk (wk-cong (wk-trans π π₂'))) N'
               ≡⟨ refl ⟩
                wk-val (wk-trans (wk-cong (wk-cong π)) (wk-wk (wk-cong π₂'))) N'
               ≡⟨ sym (wk-val-trans N' (wk-cong (wk-cong π)) (wk-wk (wk-cong π₂'))) ⟩
                (wk-val (wk-cong (wk-cong π)) (wk-val (wk-wk (wk-cong π₂')) N')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-val (wk-wk (wk-cong π₂')) N') , cong₂ pm eq₁'' eq₂''
  val-pm-helper M v N (Γ' Cx.∙ X , wk-cong (wk-cong π₂) , N' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : N ≡ wk-val (wk-cong (wk-cong π)) (wk-val (wk-cong (wk-cong π₂')) N')
      eq₂'' =   N
               ≡⟨ eq₂ ⟩
                wk-val (wk-cong (wk-cong π₂)) N'
               ≡⟨ cong (λ x → wk-val (wk-cong (wk-cong x)) N') eq₂' ⟩
                wk-val (wk-trans (wk-cong (wk-cong π)) (wk-cong (wk-cong π₂'))) N'
               ≡⟨ sym (wk-val-trans N' (wk-cong (wk-cong π)) (wk-cong (wk-cong π₂'))) ⟩
                (wk-val (wk-cong (wk-cong π)) (wk-val (wk-cong (wk-cong π₂')) N')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-val (wk-cong (wk-cong π₂')) N') , cong₂ pm eq₁'' eq₂''
  val-pm-helper M v N (Γ' Cx.∙ X , wk-cong (wk-wk π₂) , N' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : N ≡ (wk-val (wk-cong (wk-cong π)) (wk-val (wk-cong (wk-wk π₂')) N'))
      eq₂'' =   N
               ≡⟨ eq₂ ⟩
                wk-val (wk-cong (wk-wk π₂)) N'
               ≡⟨ cong (λ x → wk-val (wk-cong (wk-wk x)) N') eq₂' ⟩
                wk-val (wk-trans (wk-cong (wk-cong π)) (wk-cong (wk-wk π₂'))) N'
               ≡⟨ sym (wk-val-trans N' (wk-cong (wk-cong π)) (wk-cong (wk-wk π₂'))) ⟩
                (wk-val (wk-cong (wk-cong π)) (wk-val (wk-cong (wk-wk π₂')) N')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-val (wk-cong (wk-wk π₂')) N') , cong₂ pm eq₁'' eq₂''


  comp-pm-helper : (M : Val Γ (X `× Y)) → ValStr M → (W : Comp (Γ ∙ X ∙ Y) Z) → CompStr W → CompStr (pm M W)
  comp-pm-helper M v W (Cx.ε , wk-wk (wk-wk π₂) , W' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : W ≡ (wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-wk (wk-wk π₂')) W'))
      eq₂'' =   W
               ≡⟨ eq₂ ⟩
                wk-comp (wk-wk (wk-wk π₂)) W'
               ≡⟨ cong (λ x → wk-comp (wk-wk (wk-wk x)) W') eq₂' ⟩
                wk-comp (wk-wk (wk-wk (wk-trans π π₂'))) W'
               ≡⟨ refl ⟩
                wk-comp (wk-wk ((wk-trans (wk-cong π) (wk-wk π₂')))) W'
               ≡⟨ refl ⟩
                wk-comp (wk-trans (wk-cong (wk-cong π)) (wk-wk (wk-wk π₂'))) W'
               ≡⟨ sym (wk-comp-trans W' (wk-cong (wk-cong π)) (wk-wk (wk-wk π₂'))) ⟩
                (wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-wk (wk-wk π₂')) W')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-comp (wk-wk (wk-wk π₂')) W') , cong₂ pm eq₁'' eq₂''
  comp-pm-helper M v W (Γ' Cx.∙ X , wk-wk (wk-wk π₂) , W' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : W ≡ (wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-wk (wk-wk π₂')) W'))
      eq₂'' =   W
               ≡⟨ eq₂ ⟩
                wk-comp (wk-wk (wk-wk π₂)) W'
               ≡⟨ cong (λ x → wk-comp (wk-wk (wk-wk x)) W') eq₂' ⟩
                wk-comp (wk-wk (wk-wk (wk-trans π π₂'))) W'
               ≡⟨ refl ⟩
                wk-comp (wk-wk ((wk-trans (wk-cong π) (wk-wk π₂')))) W'
               ≡⟨ refl ⟩
                wk-comp (wk-trans (wk-cong (wk-cong π)) (wk-wk (wk-wk π₂'))) W'
               ≡⟨ sym (wk-comp-trans W' (wk-cong (wk-cong π)) (wk-wk (wk-wk π₂'))) ⟩
                (wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-wk (wk-wk π₂')) W')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-comp (wk-wk (wk-wk π₂')) W') , cong₂ pm eq₁'' eq₂''
  comp-pm-helper M v W (Γ' Cx.∙ X , wk-wk (wk-cong π₂) , W' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : W ≡ (wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-wk (wk-cong π₂')) W'))
      eq₂'' =   W
               ≡⟨ eq₂ ⟩
                wk-comp (wk-wk (wk-cong π₂)) W'
               ≡⟨ cong (λ x → wk-comp (wk-wk (wk-cong x)) W') eq₂' ⟩
                wk-comp (wk-wk (wk-cong (wk-trans π π₂'))) W'
               ≡⟨ refl ⟩
                wk-comp (wk-trans (wk-cong (wk-cong π)) (wk-wk (wk-cong π₂'))) W'
               ≡⟨ sym (wk-comp-trans W' (wk-cong (wk-cong π)) (wk-wk (wk-cong π₂'))) ⟩
                (wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-wk (wk-cong π₂')) W')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-comp (wk-wk (wk-cong π₂')) W') , cong₂ pm eq₁'' eq₂''
  comp-pm-helper M v W (Γ' Cx.∙ X , wk-cong (wk-cong π₂) , W' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : W ≡ wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-cong (wk-cong π₂')) W')
      eq₂'' =   W
               ≡⟨ eq₂ ⟩
                wk-comp (wk-cong (wk-cong π₂)) W'
               ≡⟨ cong (λ x → wk-comp (wk-cong (wk-cong x)) W') eq₂' ⟩
                wk-comp (wk-trans (wk-cong (wk-cong π)) (wk-cong (wk-cong π₂'))) W'
               ≡⟨ sym (wk-comp-trans W' (wk-cong (wk-cong π)) (wk-cong (wk-cong π₂'))) ⟩
                (wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-cong (wk-cong π₂')) W')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-comp (wk-cong (wk-cong π₂')) W') , cong₂ pm eq₁'' eq₂''
  comp-pm-helper M v W (Γ' Cx.∙ X , wk-cong (wk-wk π₂) , W' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : W ≡ (wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-cong (wk-wk π₂')) W'))
      eq₂'' =   W
               ≡⟨ eq₂ ⟩
                wk-comp (wk-cong (wk-wk π₂)) W'
               ≡⟨ cong (λ x → wk-comp (wk-cong (wk-wk x)) W') eq₂' ⟩
                wk-comp (wk-trans (wk-cong (wk-cong π)) (wk-cong (wk-wk π₂'))) W'
               ≡⟨ sym (wk-comp-trans W' (wk-cong (wk-cong π)) (wk-cong (wk-wk π₂'))) ⟩
                (wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-cong (wk-wk π₂')) W')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-comp (wk-cong (wk-wk π₂')) W') , cong₂ pm eq₁'' eq₂''


  comp-push-helper : (W₁ : Comp Γ X) → CompStr W₁
                  → (W₂ : Comp (Γ ∙ X) Z) → CompStr W₂
                  → CompStr (push W₁ W₂)
  comp-push-helper W₁ c W₂ (Cx.ε , wk-wk π₂' , W₂' , eq₂) =
    let
      π₁' = proj₁ (proj₂ c)
      W₁' = proj₁ (proj₂ (proj₂ c))
      eq₁ = proj₂ (proj₂ (proj₂ c))
      j = wk-merge π₁' π₂'
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁'' = proj₁ (proj₂ (proj₂ j))
      π₂'' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : W₁ ≡ wk-comp π (wk-comp π₁'' W₁')
      eq₁'' = W₁ ≡⟨ eq₁ ⟩ wk-comp π₁' W₁' ≡⟨ cong (λ x → wk-comp x W₁') eq₁' ⟩ wk-comp (wk-trans π π₁'') W₁' ≡⟨ sym (wk-comp-trans W₁' π π₁'') ⟩ wk-comp π (wk-comp π₁'' W₁') ∎
      eq₂'' : W₂ ≡ (wk-comp (wk-cong π) (wk-comp (wk-wk π₂'') W₂'))
      eq₂'' =  W₂
              ≡⟨ eq₂ ⟩
               wk-comp (wk-wk π₂') W₂'
              ≡⟨ cong (λ x → wk-comp (wk-wk x) W₂') eq₂' ⟩
               wk-comp (wk-trans (wk-cong π) (wk-wk π₂'')) W₂'
              ≡⟨ sym (wk-comp-trans W₂' (wk-cong π) (wk-wk π₂'')) ⟩
               (wk-comp (wk-cong π) (wk-comp (wk-wk π₂'') W₂')) ∎
    in
    Γ' , π , push (wk-comp π₁'' W₁') (wk-comp (wk-wk π₂'') W₂') , cong₂ push eq₁'' eq₂''
  comp-push-helper W₁ c W₂ (Γ₂' Cx.∙ X , wk-wk π₂' , W₂' , eq₂) =
    let
      π₁' = proj₁ (proj₂ c)
      W₁' = proj₁ (proj₂ (proj₂ c))
      eq₁ = proj₂ (proj₂ (proj₂ c))
      j = wk-merge π₁' π₂'
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁'' = proj₁ (proj₂ (proj₂ j))
      π₂'' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : W₁ ≡ wk-comp π (wk-comp π₁'' W₁')
      eq₁'' = W₁ ≡⟨ eq₁ ⟩ wk-comp π₁' W₁' ≡⟨ cong (λ x → wk-comp x W₁') eq₁' ⟩ wk-comp (wk-trans π π₁'') W₁' ≡⟨ sym (wk-comp-trans W₁' π π₁'') ⟩ wk-comp π (wk-comp π₁'' W₁') ∎
      eq₂'' : W₂ ≡ (wk-comp (wk-cong π) (wk-comp (wk-wk π₂'') W₂'))
      eq₂'' =  W₂
              ≡⟨ eq₂ ⟩
               wk-comp (wk-wk π₂') W₂'
              ≡⟨ cong (λ x → wk-comp (wk-wk x) W₂') eq₂' ⟩
               wk-comp (wk-trans (wk-cong π) (wk-wk π₂'')) W₂'
              ≡⟨ sym (wk-comp-trans W₂' (wk-cong π) (wk-wk π₂'')) ⟩
               (wk-comp (wk-cong π) (wk-comp (wk-wk π₂'') W₂')) ∎
    in
    Γ' , π , push (wk-comp π₁'' W₁') (wk-comp (wk-wk π₂'') W₂') , cong₂ push eq₁'' eq₂''
  comp-push-helper W₁ c W₂ (Γ₂' Cx.∙ X , wk-cong π₂' , W₂' , eq₂) =
    let
      π₁' = proj₁ (proj₂ c)
      W₁' = proj₁ (proj₂ (proj₂ c))
      eq₁ = proj₂ (proj₂ (proj₂ c))
      j = wk-merge π₁' π₂'
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁'' = proj₁ (proj₂ (proj₂ j))
      π₂'' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : W₁ ≡ wk-comp π (wk-comp π₁'' W₁')
      eq₁'' = W₁ ≡⟨ eq₁ ⟩ wk-comp π₁' W₁' ≡⟨ cong (λ x → wk-comp x W₁') eq₁' ⟩ wk-comp (wk-trans π π₁'') W₁' ≡⟨ sym (wk-comp-trans W₁' π π₁'') ⟩ wk-comp π (wk-comp π₁'' W₁') ∎
      eq₂'' : W₂ ≡ wk-comp (wk-cong π) (wk-comp (wk-cong π₂'') W₂')
      eq₂'' =  W₂
              ≡⟨ eq₂ ⟩
               wk-comp (wk-cong π₂') W₂'
              ≡⟨ cong (λ x → wk-comp (wk-cong x) W₂') eq₂' ⟩
               wk-comp (wk-cong (wk-trans π π₂'')) W₂'
              ≡⟨ sym (wk-comp-trans W₂' (wk-cong π) (wk-cong π₂'')) ⟩
               wk-comp (wk-cong π) (wk-comp (wk-cong π₂'') W₂') ∎
    in
    Γ' , π , push (wk-comp π₁'' W₁') (wk-comp (wk-cong π₂'') W₂') , cong₂ push eq₁'' eq₂''


  comp-sub-helper : (W₁ : Comp (Γ ∙ `V) Z) → CompStr W₁
                  → (W₂ : Comp Γ Z) → CompStr W₂
                  → CompStr (sub W₁ W₂)
  comp-sub-helper W₁ (Γ₁' , wk-cong π₁' , W₁' , eq₁) W₂ c =
    let
      π₂' = proj₁ (proj₂ c)
      W₂' = proj₁ (proj₂ (proj₂ c))
      eq₂ = proj₂ (proj₂ (proj₂ c))
      j = wk-merge π₁' π₂'
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁'' = proj₁ (proj₂ (proj₂ j))
      π₂'' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : W₁ ≡ wk-comp (wk-cong π) (wk-comp (wk-cong π₁'') W₁')
      eq₁'' = W₁ ≡⟨ eq₁ ⟩ wk-comp (wk-cong π₁') W₁' ≡⟨ cong (λ x → wk-comp (wk-cong x) W₁') eq₁' ⟩ wk-comp (wk-cong (wk-trans π π₁'')) W₁' ≡⟨ sym (wk-comp-trans W₁' (wk-cong π) (wk-cong π₁'')) ⟩ wk-comp (wk-cong π) (wk-comp (wk-cong π₁'') W₁') ∎
      eq₂'' : W₂ ≡ wk-comp π (wk-comp π₂'' W₂')
      eq₂'' = W₂ ≡⟨ eq₂ ⟩ wk-comp π₂' W₂' ≡⟨ cong (λ x → wk-comp x W₂') eq₂' ⟩ wk-comp (wk-trans π π₂'') W₂' ≡⟨ sym (wk-comp-trans W₂' π π₂'') ⟩ wk-comp π (wk-comp π₂'' W₂') ∎
    in
    Γ' , π , sub (wk-comp (wk-cong π₁'') W₁') (wk-comp π₂'' W₂') , cong₂ sub eq₁'' eq₂''
  comp-sub-helper W₁ (Γ₁' , wk-wk π₁' , W₁' , eq₁) W₂ c =
    let
      π₂' = proj₁ (proj₂ c)
      W₂' = proj₁ (proj₂ (proj₂ c))
      eq₂ = proj₂ (proj₂ (proj₂ c))
      j = wk-merge π₁' π₂'
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁'' = proj₁ (proj₂ (proj₂ j))
      π₂'' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : W₁ ≡ (wk-comp (wk-cong π) (wk-comp (wk-wk π₁'') W₁'))
      eq₁'' = W₁ ≡⟨ eq₁ ⟩ wk-comp (wk-wk π₁') W₁' ≡⟨ cong (λ x → wk-comp (wk-wk x) W₁') eq₁' ⟩ wk-comp (wk-wk (wk-trans π π₁'')) W₁' ≡⟨ sym (wk-comp-trans W₁' (wk-cong π) (wk-wk π₁'')) ⟩ (wk-comp (wk-cong π) (wk-comp (wk-wk π₁'') W₁')) ∎
      eq₂'' : W₂ ≡ wk-comp π (wk-comp π₂'' W₂')
      eq₂'' = W₂ ≡⟨ eq₂ ⟩ wk-comp π₂' W₂' ≡⟨ cong (λ x → wk-comp x W₂') eq₂' ⟩ wk-comp (wk-trans π π₂'') W₂' ≡⟨ sym (wk-comp-trans W₂' π π₂'') ⟩ wk-comp π (wk-comp π₂'' W₂') ∎
    in
    Γ' , π , sub (wk-comp (wk-wk π₁'') W₁') (wk-comp π₂'' W₂') , cong₂ sub eq₁'' eq₂''

  mutual
    --Σ[ iₘ ∈ MemStr i ] (∀ (iₛ : MemStr i) → Wk (proj₁ iₛ) (proj₁ iₘ))

    --val-gc : (M : Val Γ X) → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk Γ Γ' ] Σ[ M' ∈ (Val Γ' X) ] (M ≡ wk-val π M')
    val-gc : (M : Val Γ X) → ValStr M --Σ[ Mₘ ∈ ValStr M ] (∀ (Mₛ : ValStr M) → Wk (proj₁ Mₛ) (proj₁ Mₘ))
    --val-gc : (M : Val Γ X) → ValMin M
    val-gc (var i) =
      let
        m = (mem-gc i)
        l = proj₁ m
        eq = proj₂ (proj₂ (proj₂ (proj₁ m)))
        c = proj₂ m
        π = proj₁ (proj₂ l)
      in
      (proj₁ l , proj₁ (proj₂ l) , var (proj₁ (proj₂ (proj₂ l))) , cong var (proj₂ (proj₂ (proj₂ l)))) --,
      -- λ Mₛ →
      --   let
      --     eq2 = proj₂ (proj₂ (proj₂ Mₛ))
      --     vm = (var-to-memstr eq2)
      --     c' = c (proj₁ vm)
      --     c'' : Wk (proj₁ Mₛ) (proj₁ (proj₁ m))
      --     c'' = subst (λ x → Wk x (proj₁ (proj₁ m))) (proj₂ vm) c'
      --   in
      --   c''
    val-gc (lam {A = X} W) = val-lam-helper W (comp-gc W)
    val-gc {Γ = Γ} (pair M₁ M₂) =
            let
              v₁ = val-gc M₁
              M₁' = proj₁ (proj₂ (proj₂ v₁))
              π₁ = proj₁ (proj₂ v₁)
              eq₁ = proj₂ (proj₂ (proj₂ v₁))
              v₂ = val-gc M₂
              M₂' = proj₁ (proj₂ (proj₂ v₂))
              π₂ = proj₁ (proj₂ v₂)
              eq₂ = proj₂ (proj₂ (proj₂ v₂))
              j = wk-merge π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
              eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
              eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
              eq₁'' : M₁ ≡ wk-val π (wk-val π₁' M₁')
              eq₁'' = M₁ ≡⟨ eq₁ ⟩ wk-val π₁ M₁' ≡⟨ cong (λ x → wk-val x M₁') eq₁' ⟩ wk-val (wk-trans π π₁') M₁' ≡⟨ sym (wk-val-trans M₁' π π₁') ⟩ wk-val π (wk-val π₁' M₁') ∎
              eq₂'' : M₂ ≡ wk-val π (wk-val π₂' M₂')
              eq₂'' = M₂ ≡⟨ eq₂ ⟩ wk-val π₂ M₂' ≡⟨ cong (λ x → wk-val x M₂') eq₂' ⟩ wk-val (wk-trans π π₂') M₂' ≡⟨ sym (wk-val-trans M₂' π π₂') ⟩ wk-val π (wk-val π₂' M₂') ∎
            in
            Γ' , π , pair (wk-val π₁' M₁') (wk-val π₂' M₂') , cong₂ pair eq₁'' eq₂''
    val-gc (pm {A = X} {B = Y} {C = Z} M N) = val-pm-helper M (val-gc M) N (val-gc N)
    val-gc unit = ε , wk-wk-ε , unit , refl

    comp-gc : (W : Comp Γ X) → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk Γ Γ' ] Σ[ W' ∈ (Comp Γ' X) ] (W ≡ wk-comp π W')
    comp-gc (return M) = let v = val-gc M in proj₁ v , proj₁ (proj₂ v) , return (proj₁ (proj₂ (proj₂ v))) , cong return (proj₂ (proj₂ (proj₂ v)))
    comp-gc (pm {A = X} {B = Y} {C = Z} M W) = comp-pm-helper M (val-gc M) W (comp-gc W)
    comp-gc (push {A = X} {B = Z} W₁ W₂) = comp-push-helper W₁ (comp-gc W₁) W₂ (comp-gc W₂)
    comp-gc (app M N) =
            let
              v₁ = val-gc M
              M' = proj₁ (proj₂ (proj₂ v₁))
              π₁ = proj₁ (proj₂ v₁)
              eq₁ = proj₂ (proj₂ (proj₂ v₁))
              v₂ = val-gc N
              N' = proj₁ (proj₂ (proj₂ v₂))
              π₂ = proj₁ (proj₂ v₂)
              eq₂ = proj₂ (proj₂ (proj₂ v₂))
              j = wk-merge π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
              eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
              eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
              eq₁'' : M ≡ wk-val π (wk-val π₁' M')
              eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
              eq₂'' : N ≡ wk-val π (wk-val π₂' N')
              eq₂'' = N ≡⟨ eq₂ ⟩ wk-val π₂ N' ≡⟨ cong (λ x → wk-val x N') eq₂' ⟩ wk-val (wk-trans π π₂') N' ≡⟨ sym (wk-val-trans N' π π₂') ⟩ wk-val π (wk-val π₂' N') ∎
            in
            Γ' , π , app (wk-val π₁' M') (wk-val π₂' N') , cong₂ app eq₁'' eq₂''

    comp-gc (var M) = let v = val-gc M in proj₁ v , proj₁ (proj₂ v) , var (proj₁ (proj₂ (proj₂ v))) , cong var (proj₂ (proj₂ (proj₂ v)))
    comp-gc (sub {A = X} W₁ W₂) = comp-sub-helper W₁ (comp-gc W₁) W₂ (comp-gc W₂)


  {- WORKING, BUT NEED TO ADD FACTORING PROPERTY
  mem-gc : (i : Γ ∋ X) → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk Γ Γ' ] Σ[ i' ∈ (Γ' ∋ X) ] (i ≡ wk-mem π i')
  mem-gc {Γ = Γ ∙ X} h = ε ∙ X , wk-cong wk-wk-ε , h , refl
  mem-gc (t i) =
    let
      IH = mem-gc i
    in
    proj₁ IH , wk-wk (proj₁ (proj₂ IH)) , proj₁ (proj₂ (proj₂ IH)) , wk-mem-wk-eq (proj₂ (proj₂ (proj₂ IH)))

  val-lam-helper : (W : Comp (Γ ∙ X) Y) → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk (Γ ∙ X) Γ' ] Σ[ W' ∈ (Comp Γ' Y) ] (W ≡ wk-comp π W') → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk Γ Γ' ] Σ[ M' ∈ (Val Γ' (X `⇒ Y)) ] (lam W ≡ wk-val π M')
  val-lam-helper W (ε , wk-wk π' , W' , eq) =
    let
      a0 : wk-comp (wk-cong π') (wk-comp (wk-wk wk-ε) W') ≡ wk-comp (wk-trans (wk-cong π') (wk-wk wk-ε)) W'
      a0 = wk-comp-trans W' (wk-cong π') (wk-wk wk-ε)
    in
    ε , π' , lam (wk-comp (wk-wk wk-id) W') , cong lam (Eq.trans (Eq.trans eq (cong (λ x → wk-comp x W') (sym wk-trans-id'))) (sym a0))
  val-lam-helper W (Γ' ∙ X , wk-cong π' , W' , eq) = Γ' , π' , lam W' , cong lam eq
  val-lam-helper {X = X} W (Γ' ∙ X' , wk-wk π' , W' , eq) =
    let
      a0 : wk-comp (wk-cong {A = X} π') (wk-comp (wk-wk wk-id) W') ≡ wk-comp (wk-trans (wk-cong π') (wk-wk (wk-cong wk-id))) W'
      a0 = wk-comp-trans W' (wk-cong π') (wk-wk wk-id)
      a1 : wk-comp (wk-wk π') W' ≡ wk-comp (wk-wk (wk-trans π' (wk-cong wk-id))) W'
      a1 = cong (λ x → wk-comp x W') (sym (cong wk-wk wk-trans-id'))
    in
    Γ' ∙ X' , π' , lam (wk-comp (wk-wk wk-id) W') , cong lam (Eq.trans (Eq.trans eq a1) (sym a0))

  val-pm-helper : (M : Val Γ (X `× Y)) → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk Γ Γ' ] Σ[ M' ∈ (Val Γ' (X `× Y)) ] (M ≡ wk-val π M')
                  → (N : Val (Γ ∙ X ∙ Y) Z) → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk (Γ ∙ X ∙ Y) Γ' ] Σ[ N' ∈ (Val Γ' Z) ] (N ≡ wk-val π N')
                  → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk Γ Γ' ] Σ[ PM ∈ (Val Γ' Z) ] (pm M N ≡ wk-val π PM)
  val-pm-helper M v N (Cx.ε , wk-wk (wk-wk π₂) , N' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : N ≡ (wk-val (wk-cong (wk-cong π)) (wk-val (wk-wk (wk-wk π₂')) N'))
      eq₂'' =   N
               ≡⟨ eq₂ ⟩
                wk-val (wk-wk (wk-wk π₂)) N'
               ≡⟨ cong (λ x → wk-val (wk-wk (wk-wk x)) N') eq₂' ⟩
                wk-val (wk-wk (wk-wk (wk-trans π π₂'))) N'
               ≡⟨ refl ⟩
                wk-val (wk-wk ((wk-trans (wk-cong π) (wk-wk π₂')))) N'
               ≡⟨ refl ⟩
                wk-val (wk-trans (wk-cong (wk-cong π)) (wk-wk (wk-wk π₂'))) N'
               ≡⟨ sym (wk-val-trans N' (wk-cong (wk-cong π)) (wk-wk (wk-wk π₂'))) ⟩
                (wk-val (wk-cong (wk-cong π)) (wk-val (wk-wk (wk-wk π₂')) N')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-val (wk-wk (wk-wk π₂')) N') , cong₂ pm eq₁'' eq₂''
  val-pm-helper M v N (Γ' Cx.∙ X , wk-wk (wk-wk π₂) , N' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : N ≡ (wk-val (wk-cong (wk-cong π)) (wk-val (wk-wk (wk-wk π₂')) N'))
      eq₂'' =   N
               ≡⟨ eq₂ ⟩
                wk-val (wk-wk (wk-wk π₂)) N'
               ≡⟨ cong (λ x → wk-val (wk-wk (wk-wk x)) N') eq₂' ⟩
                wk-val (wk-wk (wk-wk (wk-trans π π₂'))) N'
               ≡⟨ refl ⟩
                wk-val (wk-wk ((wk-trans (wk-cong π) (wk-wk π₂')))) N'
               ≡⟨ refl ⟩
                wk-val (wk-trans (wk-cong (wk-cong π)) (wk-wk (wk-wk π₂'))) N'
               ≡⟨ sym (wk-val-trans N' (wk-cong (wk-cong π)) (wk-wk (wk-wk π₂'))) ⟩
                (wk-val (wk-cong (wk-cong π)) (wk-val (wk-wk (wk-wk π₂')) N')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-val (wk-wk (wk-wk π₂')) N') , cong₂ pm eq₁'' eq₂''
  val-pm-helper M v N (Γ' Cx.∙ X , wk-wk (wk-cong π₂) , N' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : N ≡ (wk-val (wk-cong (wk-cong π)) (wk-val (wk-wk (wk-cong π₂')) N'))
      eq₂'' =   N
               ≡⟨ eq₂ ⟩
                wk-val (wk-wk (wk-cong π₂)) N'
               ≡⟨ cong (λ x → wk-val (wk-wk (wk-cong x)) N') eq₂' ⟩
                wk-val (wk-wk (wk-cong (wk-trans π π₂'))) N'
               ≡⟨ refl ⟩
                wk-val (wk-trans (wk-cong (wk-cong π)) (wk-wk (wk-cong π₂'))) N'
               ≡⟨ sym (wk-val-trans N' (wk-cong (wk-cong π)) (wk-wk (wk-cong π₂'))) ⟩
                (wk-val (wk-cong (wk-cong π)) (wk-val (wk-wk (wk-cong π₂')) N')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-val (wk-wk (wk-cong π₂')) N') , cong₂ pm eq₁'' eq₂''
  val-pm-helper M v N (Γ' Cx.∙ X , wk-cong (wk-cong π₂) , N' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : N ≡ wk-val (wk-cong (wk-cong π)) (wk-val (wk-cong (wk-cong π₂')) N')
      eq₂'' =   N
               ≡⟨ eq₂ ⟩
                wk-val (wk-cong (wk-cong π₂)) N'
               ≡⟨ cong (λ x → wk-val (wk-cong (wk-cong x)) N') eq₂' ⟩
                wk-val (wk-trans (wk-cong (wk-cong π)) (wk-cong (wk-cong π₂'))) N'
               ≡⟨ sym (wk-val-trans N' (wk-cong (wk-cong π)) (wk-cong (wk-cong π₂'))) ⟩
                (wk-val (wk-cong (wk-cong π)) (wk-val (wk-cong (wk-cong π₂')) N')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-val (wk-cong (wk-cong π₂')) N') , cong₂ pm eq₁'' eq₂''
  val-pm-helper M v N (Γ' Cx.∙ X , wk-cong (wk-wk π₂) , N' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : N ≡ (wk-val (wk-cong (wk-cong π)) (wk-val (wk-cong (wk-wk π₂')) N'))
      eq₂'' =   N
               ≡⟨ eq₂ ⟩
                wk-val (wk-cong (wk-wk π₂)) N'
               ≡⟨ cong (λ x → wk-val (wk-cong (wk-wk x)) N') eq₂' ⟩
                wk-val (wk-trans (wk-cong (wk-cong π)) (wk-cong (wk-wk π₂'))) N'
               ≡⟨ sym (wk-val-trans N' (wk-cong (wk-cong π)) (wk-cong (wk-wk π₂'))) ⟩
                (wk-val (wk-cong (wk-cong π)) (wk-val (wk-cong (wk-wk π₂')) N')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-val (wk-cong (wk-wk π₂')) N') , cong₂ pm eq₁'' eq₂''

  comp-pm-helper : (M : Val Γ (X `× Y)) → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk Γ Γ' ] Σ[ M' ∈ (Val Γ' (X `× Y)) ] (M ≡ wk-val π M')
                  → (W : Comp (Γ ∙ X ∙ Y) Z) → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk (Γ ∙ X ∙ Y) Γ' ] Σ[ W' ∈ (Comp Γ' Z) ] (W ≡ wk-comp π W')
                  → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk Γ Γ' ] Σ[ PM ∈ (Comp Γ' Z) ] (pm M W ≡ wk-comp π PM)
  comp-pm-helper M v W (Cx.ε , wk-wk (wk-wk π₂) , W' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : W ≡ (wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-wk (wk-wk π₂')) W'))
      eq₂'' =   W
               ≡⟨ eq₂ ⟩
                wk-comp (wk-wk (wk-wk π₂)) W'
               ≡⟨ cong (λ x → wk-comp (wk-wk (wk-wk x)) W') eq₂' ⟩
                wk-comp (wk-wk (wk-wk (wk-trans π π₂'))) W'
               ≡⟨ refl ⟩
                wk-comp (wk-wk ((wk-trans (wk-cong π) (wk-wk π₂')))) W'
               ≡⟨ refl ⟩
                wk-comp (wk-trans (wk-cong (wk-cong π)) (wk-wk (wk-wk π₂'))) W'
               ≡⟨ sym (wk-comp-trans W' (wk-cong (wk-cong π)) (wk-wk (wk-wk π₂'))) ⟩
                (wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-wk (wk-wk π₂')) W')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-comp (wk-wk (wk-wk π₂')) W') , cong₂ pm eq₁'' eq₂''
  comp-pm-helper M v W (Γ' Cx.∙ X , wk-wk (wk-wk π₂) , W' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : W ≡ (wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-wk (wk-wk π₂')) W'))
      eq₂'' =   W
               ≡⟨ eq₂ ⟩
                wk-comp (wk-wk (wk-wk π₂)) W'
               ≡⟨ cong (λ x → wk-comp (wk-wk (wk-wk x)) W') eq₂' ⟩
                wk-comp (wk-wk (wk-wk (wk-trans π π₂'))) W'
               ≡⟨ refl ⟩
                wk-comp (wk-wk ((wk-trans (wk-cong π) (wk-wk π₂')))) W'
               ≡⟨ refl ⟩
                wk-comp (wk-trans (wk-cong (wk-cong π)) (wk-wk (wk-wk π₂'))) W'
               ≡⟨ sym (wk-comp-trans W' (wk-cong (wk-cong π)) (wk-wk (wk-wk π₂'))) ⟩
                (wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-wk (wk-wk π₂')) W')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-comp (wk-wk (wk-wk π₂')) W') , cong₂ pm eq₁'' eq₂''
  comp-pm-helper M v W (Γ' Cx.∙ X , wk-wk (wk-cong π₂) , W' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : W ≡ (wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-wk (wk-cong π₂')) W'))
      eq₂'' =   W
               ≡⟨ eq₂ ⟩
                wk-comp (wk-wk (wk-cong π₂)) W'
               ≡⟨ cong (λ x → wk-comp (wk-wk (wk-cong x)) W') eq₂' ⟩
                wk-comp (wk-wk (wk-cong (wk-trans π π₂'))) W'
               ≡⟨ refl ⟩
                wk-comp (wk-trans (wk-cong (wk-cong π)) (wk-wk (wk-cong π₂'))) W'
               ≡⟨ sym (wk-comp-trans W' (wk-cong (wk-cong π)) (wk-wk (wk-cong π₂'))) ⟩
                (wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-wk (wk-cong π₂')) W')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-comp (wk-wk (wk-cong π₂')) W') , cong₂ pm eq₁'' eq₂''
  comp-pm-helper M v W (Γ' Cx.∙ X , wk-cong (wk-cong π₂) , W' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : W ≡ wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-cong (wk-cong π₂')) W')
      eq₂'' =   W
               ≡⟨ eq₂ ⟩
                wk-comp (wk-cong (wk-cong π₂)) W'
               ≡⟨ cong (λ x → wk-comp (wk-cong (wk-cong x)) W') eq₂' ⟩
                wk-comp (wk-trans (wk-cong (wk-cong π)) (wk-cong (wk-cong π₂'))) W'
               ≡⟨ sym (wk-comp-trans W' (wk-cong (wk-cong π)) (wk-cong (wk-cong π₂'))) ⟩
                (wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-cong (wk-cong π₂')) W')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-comp (wk-cong (wk-cong π₂')) W') , cong₂ pm eq₁'' eq₂''
  comp-pm-helper M v W (Γ' Cx.∙ X , wk-cong (wk-wk π₂) , W' , eq₂) =
    let
      π₁ = proj₁ (proj₂ v)
      M' = proj₁ (proj₂ (proj₂ v))
      eq₁ = proj₂ (proj₂ (proj₂ v))
      j = wk-merge π₁ π₂
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁' = proj₁ (proj₂ (proj₂ j))
      π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : M ≡ wk-val π (wk-val π₁' M')
      eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
      eq₂'' : W ≡ (wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-cong (wk-wk π₂')) W'))
      eq₂'' =   W
               ≡⟨ eq₂ ⟩
                wk-comp (wk-cong (wk-wk π₂)) W'
               ≡⟨ cong (λ x → wk-comp (wk-cong (wk-wk x)) W') eq₂' ⟩
                wk-comp (wk-trans (wk-cong (wk-cong π)) (wk-cong (wk-wk π₂'))) W'
               ≡⟨ sym (wk-comp-trans W' (wk-cong (wk-cong π)) (wk-cong (wk-wk π₂'))) ⟩
                (wk-comp (wk-cong (wk-cong π)) (wk-comp (wk-cong (wk-wk π₂')) W')) ∎
    in
    Γ' , π , pm (wk-val π₁' M') (wk-comp (wk-cong (wk-wk π₂')) W') , cong₂ pm eq₁'' eq₂''


  comp-push-helper : (W₁ : Comp Γ X) → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk Γ Γ' ] Σ[ W₁' ∈ (Comp Γ' X) ] (W₁ ≡ wk-comp π W₁')
                  → (W₂ : Comp (Γ ∙ X) Z) → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk (Γ ∙ X) Γ' ] Σ[ W₂' ∈ (Comp Γ' Z) ] (W₂ ≡ wk-comp π W₂')
                  → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk Γ Γ' ] Σ[ W ∈ (Comp Γ' Z) ] (push W₁ W₂ ≡ wk-comp π W)
  comp-push-helper W₁ c W₂ (Cx.ε , wk-wk π₂' , W₂' , eq₂) =
    let
      π₁' = proj₁ (proj₂ c)
      W₁' = proj₁ (proj₂ (proj₂ c))
      eq₁ = proj₂ (proj₂ (proj₂ c))
      j = wk-merge π₁' π₂'
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁'' = proj₁ (proj₂ (proj₂ j))
      π₂'' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : W₁ ≡ wk-comp π (wk-comp π₁'' W₁')
      eq₁'' = W₁ ≡⟨ eq₁ ⟩ wk-comp π₁' W₁' ≡⟨ cong (λ x → wk-comp x W₁') eq₁' ⟩ wk-comp (wk-trans π π₁'') W₁' ≡⟨ sym (wk-comp-trans W₁' π π₁'') ⟩ wk-comp π (wk-comp π₁'' W₁') ∎
      eq₂'' : W₂ ≡ (wk-comp (wk-cong π) (wk-comp (wk-wk π₂'') W₂'))
      eq₂'' =  W₂
              ≡⟨ eq₂ ⟩
               wk-comp (wk-wk π₂') W₂'
              ≡⟨ cong (λ x → wk-comp (wk-wk x) W₂') eq₂' ⟩
               wk-comp (wk-trans (wk-cong π) (wk-wk π₂'')) W₂'
              ≡⟨ sym (wk-comp-trans W₂' (wk-cong π) (wk-wk π₂'')) ⟩
               (wk-comp (wk-cong π) (wk-comp (wk-wk π₂'') W₂')) ∎
    in
    Γ' , π , push (wk-comp π₁'' W₁') (wk-comp (wk-wk π₂'') W₂') , cong₂ push eq₁'' eq₂''
  comp-push-helper W₁ c W₂ (Γ₂' Cx.∙ X , wk-wk π₂' , W₂' , eq₂) =
    let
      π₁' = proj₁ (proj₂ c)
      W₁' = proj₁ (proj₂ (proj₂ c))
      eq₁ = proj₂ (proj₂ (proj₂ c))
      j = wk-merge π₁' π₂'
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁'' = proj₁ (proj₂ (proj₂ j))
      π₂'' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : W₁ ≡ wk-comp π (wk-comp π₁'' W₁')
      eq₁'' = W₁ ≡⟨ eq₁ ⟩ wk-comp π₁' W₁' ≡⟨ cong (λ x → wk-comp x W₁') eq₁' ⟩ wk-comp (wk-trans π π₁'') W₁' ≡⟨ sym (wk-comp-trans W₁' π π₁'') ⟩ wk-comp π (wk-comp π₁'' W₁') ∎
      eq₂'' : W₂ ≡ (wk-comp (wk-cong π) (wk-comp (wk-wk π₂'') W₂'))
      eq₂'' =  W₂
              ≡⟨ eq₂ ⟩
               wk-comp (wk-wk π₂') W₂'
              ≡⟨ cong (λ x → wk-comp (wk-wk x) W₂') eq₂' ⟩
               wk-comp (wk-trans (wk-cong π) (wk-wk π₂'')) W₂'
              ≡⟨ sym (wk-comp-trans W₂' (wk-cong π) (wk-wk π₂'')) ⟩
               (wk-comp (wk-cong π) (wk-comp (wk-wk π₂'') W₂')) ∎
    in
    Γ' , π , push (wk-comp π₁'' W₁') (wk-comp (wk-wk π₂'') W₂') , cong₂ push eq₁'' eq₂''
  comp-push-helper W₁ c W₂ (Γ₂' Cx.∙ X , wk-cong π₂' , W₂' , eq₂) =
    let
      π₁' = proj₁ (proj₂ c)
      W₁' = proj₁ (proj₂ (proj₂ c))
      eq₁ = proj₂ (proj₂ (proj₂ c))
      j = wk-merge π₁' π₂'
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁'' = proj₁ (proj₂ (proj₂ j))
      π₂'' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : W₁ ≡ wk-comp π (wk-comp π₁'' W₁')
      eq₁'' = W₁ ≡⟨ eq₁ ⟩ wk-comp π₁' W₁' ≡⟨ cong (λ x → wk-comp x W₁') eq₁' ⟩ wk-comp (wk-trans π π₁'') W₁' ≡⟨ sym (wk-comp-trans W₁' π π₁'') ⟩ wk-comp π (wk-comp π₁'' W₁') ∎
      eq₂'' : W₂ ≡ wk-comp (wk-cong π) (wk-comp (wk-cong π₂'') W₂')
      eq₂'' =  W₂
              ≡⟨ eq₂ ⟩
               wk-comp (wk-cong π₂') W₂'
              ≡⟨ cong (λ x → wk-comp (wk-cong x) W₂') eq₂' ⟩
               wk-comp (wk-cong (wk-trans π π₂'')) W₂'
              ≡⟨ sym (wk-comp-trans W₂' (wk-cong π) (wk-cong π₂'')) ⟩
               wk-comp (wk-cong π) (wk-comp (wk-cong π₂'') W₂') ∎
    in
    Γ' , π , push (wk-comp π₁'' W₁') (wk-comp (wk-cong π₂'') W₂') , cong₂ push eq₁'' eq₂''

  comp-sub-helper : (W₁ : Comp (Γ ∙ `V) Z) → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk (Γ ∙ `V) Γ' ] Σ[ W₁' ∈ (Comp Γ' Z) ] (W₁ ≡ wk-comp π W₁')
                  → (W₂ : Comp Γ Z) → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk Γ Γ' ] Σ[ W₂' ∈ (Comp Γ' Z) ] (W₂ ≡ wk-comp π W₂')
                  → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk Γ Γ' ] Σ[ W ∈ (Comp Γ' Z) ] (sub W₁ W₂ ≡ wk-comp π W)
  comp-sub-helper W₁ (Γ₁' , wk-cong π₁' , W₁' , eq₁) W₂ c =
    let
      π₂' = proj₁ (proj₂ c)
      W₂' = proj₁ (proj₂ (proj₂ c))
      eq₂ = proj₂ (proj₂ (proj₂ c))
      j = wk-merge π₁' π₂'
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁'' = proj₁ (proj₂ (proj₂ j))
      π₂'' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : W₁ ≡ wk-comp (wk-cong π) (wk-comp (wk-cong π₁'') W₁')
      eq₁'' = W₁ ≡⟨ eq₁ ⟩ wk-comp (wk-cong π₁') W₁' ≡⟨ cong (λ x → wk-comp (wk-cong x) W₁') eq₁' ⟩ wk-comp (wk-cong (wk-trans π π₁'')) W₁' ≡⟨ sym (wk-comp-trans W₁' (wk-cong π) (wk-cong π₁'')) ⟩ wk-comp (wk-cong π) (wk-comp (wk-cong π₁'') W₁') ∎
      eq₂'' : W₂ ≡ wk-comp π (wk-comp π₂'' W₂')
      eq₂'' = W₂ ≡⟨ eq₂ ⟩ wk-comp π₂' W₂' ≡⟨ cong (λ x → wk-comp x W₂') eq₂' ⟩ wk-comp (wk-trans π π₂'') W₂' ≡⟨ sym (wk-comp-trans W₂' π π₂'') ⟩ wk-comp π (wk-comp π₂'' W₂') ∎
    in
    Γ' , π , sub (wk-comp (wk-cong π₁'') W₁') (wk-comp π₂'' W₂') , cong₂ sub eq₁'' eq₂''
  comp-sub-helper W₁ (Γ₁' , wk-wk π₁' , W₁' , eq₁) W₂ c =
    let
      π₂' = proj₁ (proj₂ c)
      W₂' = proj₁ (proj₂ (proj₂ c))
      eq₂ = proj₂ (proj₂ (proj₂ c))
      j = wk-merge π₁' π₂'
      Γ' = proj₁ j
      π = proj₁ (proj₂ j)
      π₁'' = proj₁ (proj₂ (proj₂ j))
      π₂'' = proj₁ (proj₂ (proj₂ (proj₂ j)))
      eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
      eq₁'' : W₁ ≡ (wk-comp (wk-cong π) (wk-comp (wk-wk π₁'') W₁'))
      eq₁'' = W₁ ≡⟨ eq₁ ⟩ wk-comp (wk-wk π₁') W₁' ≡⟨ cong (λ x → wk-comp (wk-wk x) W₁') eq₁' ⟩ wk-comp (wk-wk (wk-trans π π₁'')) W₁' ≡⟨ sym (wk-comp-trans W₁' (wk-cong π) (wk-wk π₁'')) ⟩ (wk-comp (wk-cong π) (wk-comp (wk-wk π₁'') W₁')) ∎
      eq₂'' : W₂ ≡ wk-comp π (wk-comp π₂'' W₂')
      eq₂'' = W₂ ≡⟨ eq₂ ⟩ wk-comp π₂' W₂' ≡⟨ cong (λ x → wk-comp x W₂') eq₂' ⟩ wk-comp (wk-trans π π₂'') W₂' ≡⟨ sym (wk-comp-trans W₂' π π₂'') ⟩ wk-comp π (wk-comp π₂'' W₂') ∎
    in
    Γ' , π , sub (wk-comp (wk-wk π₁'') W₁') (wk-comp π₂'' W₂') , cong₂ sub eq₁'' eq₂''

  mutual

    val-gc : (M : Val Γ X) → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk Γ Γ' ] Σ[ M' ∈ (Val Γ' X) ] (M ≡ wk-val π M')
    val-gc (var i) = let l = mem-gc i in proj₁ l , proj₁ (proj₂ l) , var (proj₁ (proj₂ (proj₂ l))) , cong var (proj₂ (proj₂ (proj₂ l)))
    val-gc (lam {A = X} W) = val-lam-helper W (comp-gc W)
    val-gc {Γ = Γ} (pair M₁ M₂) =
            let
              v₁ = val-gc M₁
              M₁' = proj₁ (proj₂ (proj₂ v₁))
              π₁ = proj₁ (proj₂ v₁)
              eq₁ = proj₂ (proj₂ (proj₂ v₁))
              v₂ = val-gc M₂
              M₂' = proj₁ (proj₂ (proj₂ v₂))
              π₂ = proj₁ (proj₂ v₂)
              eq₂ = proj₂ (proj₂ (proj₂ v₂))
              j = wk-merge π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
              eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
              eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
              eq₁'' : M₁ ≡ wk-val π (wk-val π₁' M₁')
              eq₁'' = M₁ ≡⟨ eq₁ ⟩ wk-val π₁ M₁' ≡⟨ cong (λ x → wk-val x M₁') eq₁' ⟩ wk-val (wk-trans π π₁') M₁' ≡⟨ sym (wk-val-trans M₁' π π₁') ⟩ wk-val π (wk-val π₁' M₁') ∎
              eq₂'' : M₂ ≡ wk-val π (wk-val π₂' M₂')
              eq₂'' = M₂ ≡⟨ eq₂ ⟩ wk-val π₂ M₂' ≡⟨ cong (λ x → wk-val x M₂') eq₂' ⟩ wk-val (wk-trans π π₂') M₂' ≡⟨ sym (wk-val-trans M₂' π π₂') ⟩ wk-val π (wk-val π₂' M₂') ∎
            in
            Γ' , π , pair (wk-val π₁' M₁') (wk-val π₂' M₂') , cong₂ pair eq₁'' eq₂''
    val-gc (pm {A = X} {B = Y} {C = Z} M N) = val-pm-helper M (val-gc M) N (val-gc N)
    val-gc unit = ε , wk-wk-ε , unit , refl

    comp-gc : (W : Comp Γ X) → Σ[ Γ' ∈ Ctx ] Σ[ π ∈ Wk Γ Γ' ] Σ[ W' ∈ (Comp Γ' X) ] (W ≡ wk-comp π W')
    comp-gc (return M) = let v = val-gc M in proj₁ v , proj₁ (proj₂ v) , return (proj₁ (proj₂ (proj₂ v))) , cong return (proj₂ (proj₂ (proj₂ v)))
    comp-gc (pm {A = X} {B = Y} {C = Z} M W) = comp-pm-helper M (val-gc M) W (comp-gc W)
    comp-gc (push {A = X} {B = Z} W₁ W₂) = comp-push-helper W₁ (comp-gc W₁) W₂ (comp-gc W₂)
    comp-gc (app M N) =
            let
              v₁ = val-gc M
              M' = proj₁ (proj₂ (proj₂ v₁))
              π₁ = proj₁ (proj₂ v₁)
              eq₁ = proj₂ (proj₂ (proj₂ v₁))
              v₂ = val-gc N
              N' = proj₁ (proj₂ (proj₂ v₂))
              π₂ = proj₁ (proj₂ v₂)
              eq₂ = proj₂ (proj₂ (proj₂ v₂))
              j = wk-merge π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₁ (proj₂ (proj₂ (proj₂ j)))
              eq₁' = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ j))))
              eq₂' = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ j))))
              eq₁'' : M ≡ wk-val π (wk-val π₁' M')
              eq₁'' = M ≡⟨ eq₁ ⟩ wk-val π₁ M' ≡⟨ cong (λ x → wk-val x M') eq₁' ⟩ wk-val (wk-trans π π₁') M' ≡⟨ sym (wk-val-trans M' π π₁') ⟩ wk-val π (wk-val π₁' M') ∎
              eq₂'' : N ≡ wk-val π (wk-val π₂' N')
              eq₂'' = N ≡⟨ eq₂ ⟩ wk-val π₂ N' ≡⟨ cong (λ x → wk-val x N') eq₂' ⟩ wk-val (wk-trans π π₂') N' ≡⟨ sym (wk-val-trans N' π π₂') ⟩ wk-val π (wk-val π₂' N') ∎
            in
            Γ' , π , app (wk-val π₁' M') (wk-val π₂' N') , cong₂ app eq₁'' eq₂''

    comp-gc (var M) = let v = val-gc M in proj₁ v , proj₁ (proj₂ v) , var (proj₁ (proj₂ (proj₂ v))) , cong var (proj₂ (proj₂ (proj₂ v)))
    comp-gc (sub {A = X} W₁ W₂) = comp-sub-helper W₁ (comp-gc W₁) W₂ (comp-gc W₂)
  -}


  -- EXPERIMENTAL:

  {------
  -- pair-terms : {B : (Γ' : Ctx) → (Γ' ∋ X) × (Wk Γ Γ')} {Γ₁ Γ₂ : Ctx} {b₁ : B Γ₁} {b₂ : B Γ₂} → (a₁ , b₁) ≡ (a₂ , b₂) → a₁ ≡ a₂
  -- pair-terms = ?

  --merge-lemma : ((Γ , M , wk-trans π π₀) ≡ Γ' , M' , π')

  --  val-gc : Val Γ X → Σ[ Γ' ∈ Ctx ] ((Val Γ' X) × (Wk Γ Γ'))

  --  val-gc {Γ = Γ} (pair M₁ M₂) =
  --          let
  --            v₁ = val-gc M₁
  --            M₁' = proj₁ (proj₂ v₁)
  --            π₁ = proj₂ (proj₂ v₁)
  --            v₂ = val-gc M₂
  --            M₂' = proj₁ (proj₂ v₂)
  --            π₂ = proj₂ (proj₂ v₂)
  --            j = wk-merge π₁ π₂
  --            Γ' = proj₁ j
  --            π = proj₁ (proj₂ j)
  --            π₁' = proj₁ (proj₂ (proj₂ j))
  --            π₂' = proj₂ (proj₂ (proj₂ j))
  --          in
  --          Γ' , pair (wk-val π₁' M₁') (wk-val π₂' M₂') , π


  pair-lemma : {Γ : Ctx} {X Y : Ty} → (M₁ : Val Γ X) (M₂ : Val Γ Y) → val-gc {Γ = Γ} (pair M₁ M₂) ≡ (proj₁ (wk-merge (proj₂ (proj₂ (val-gc M₁))) (proj₂ (proj₂ (val-gc M₂)))) , pair (wk-val (proj₁ (proj₂ (proj₂ (wk-merge (proj₂ (proj₂ (val-gc M₁))) (proj₂ (proj₂ (val-gc M₂))))))) (proj₁ (proj₂ (val-gc M₁)))) (wk-val (proj₂ (proj₂ (proj₂ (wk-merge (proj₂ (proj₂ (val-gc M₁))) (proj₂ (proj₂ (val-gc M₂))))))) (proj₁ (proj₂ (val-gc M₂)))) , (proj₁ (proj₂ (wk-merge (proj₂ (proj₂ (val-gc M₁))) (proj₂ (proj₂ (val-gc M₂)))))))
  pair-lemma M₁ M₂ = refl

  -- pair-lemma2 : {Γ : Ctx} {X Y : Ty} → (M₁ : Val Γ X) (M₂ : Val Γ Y) →
  --               (proj₁ (wk-merge (proj₂ (proj₂ (val-gc M₁))) (proj₂ (proj₂ (val-gc M₂)))) , pair (wk-val (proj₁ (proj₂ (proj₂ (wk-merge (proj₂ (proj₂ (val-gc M₁))) (proj₂ (proj₂ (val-gc M₂))))))) (proj₁ (proj₂ (val-gc M₁)))) (wk-val (proj₂ (proj₂ (proj₂ (wk-merge (proj₂ (proj₂ (val-gc M₁))) (proj₂ (proj₂ (val-gc M₂))))))) (proj₁ (proj₂ (val-gc M₂)))) , (proj₁ (proj₂ (wk-merge (proj₂ (proj₂ (val-gc M₁))) (proj₂ (proj₂ (val-gc M₂)))))))
  -- pair-lemma2 M₁ M₂ = refl

  val-gc-eq : {Δ : Ctx} {Γ : Ctx} {X : Ty} → (π : Wk Δ Γ) → (M : Val Γ X) → (_,_ {A = Ctx} {B = λ x → Val x X × Wk Δ x} (proj₁ (val-gc M)) (proj₁ (proj₂ (val-gc M)) , wk-trans π (proj₂ (proj₂ (val-gc M))))) ≡ (_,_ {A = Ctx} {B = λ x → Val x X × Wk Δ x} (proj₁ (val-gc (wk-val π M))) (proj₂ (val-gc (wk-val π M))))

  val-gc-eq wk-ε (lam W) = {!!}
  val-gc-eq wk-ε (pair M₁ M₂) = {!!}
  val-gc-eq wk-ε (pm M N) = {!!}
  val-gc-eq wk-ε unit = refl

  val-gc-eq (wk-cong π) (var i) = icong {f = var-proj₂} (mem-gc-eq (wk-cong π) i)
  val-gc-eq (wk-cong π) (lam W) = {!!}
  val-gc-eq {Δ = Δ ∙ _} {Γ = Γ ∙ Z} {X = X `× Y} (wk-cong π) (pair {A = X} {B = Y} M₁ M₂) =
    let
      IH1 = val-gc-eq (wk-cong π) M₁
      IH2 = val-gc-eq (wk-cong π) M₂
      eq1 = dproj₁-eq IH1

      a0 = proj₂ (val-gc M₁)

      eq2 : (proj₁ (val-gc M₁) , proj₁ (proj₂ (val-gc M₁)) , wk-trans (wk-cong π) (proj₂ (proj₂ (val-gc M₁)))) ≡ (proj₁ (val-gc (wk-val (wk-cong π) M₁)) , proj₂ (val-gc (wk-val (wk-cong π) M₁)))
      eq2 = dcong₂ (λ (x : Ctx) (y : Val x X × Wk (Δ ∙ Z) x) → x , y) {y₁ = proj₁ (proj₂ (val-gc M₁)) , wk-trans (wk-cong π) (proj₂ (proj₂ (val-gc M₁)))} {y₂ = proj₂ (val-gc (wk-val (wk-cong π) M₁))} eq1 {!refl!}
    in
    {!!}
  val-gc-eq (wk-cong π) (pm M N) = {!!}
  val-gc-eq (wk-cong π) unit = {!!}

  val-gc-eq (wk-wk π) (var i) = {!!}
  val-gc-eq (wk-wk π) (lam W) = {!!}
  val-gc-eq (wk-wk π) (pair M₁ M₂) = {!!}
  val-gc-eq (wk-wk π) (pm M N) = {!!}
  val-gc-eq (wk-wk π) unit = {!!}
  -------}

  {-
    dcong₂ : ∀ {A : Set a} {B : A → Set b} {C : Set c}
            (f : (x : A) → B x → C) {x₁ x₂ y₁ y₂}
          → (p : x₁ ≡ x₂) → subst B p y₁ ≡ y₂
          → f x₁ y₁ ≡ f x₂ y₂
    dcong₂ f refl refl = refl
  -}


  {-
  record MemGC (i : Γ ∋ X) : Set where
    field
      mem-gc-Γ : Ctx
      mem-gc-i : mem-gc-Γ ∋ X
      mem-gc-π : Wk Γ mem-gc-Γ

  record ValGC (M : Val Γ X) : Set where
    field
      val-gc-Γ : Ctx
      val-gc-M : Val val-gc-Γ X
      val-gc-π : Wk Γ val-gc-Γ

  record CompGC (W : Comp Γ X) : Set where
    field
      comp-gc-Γ : Ctx
      comp-gc-W : Comp comp-gc-Γ X
      comp-gc-π : Wk Γ comp-gc-Γ

  open MemGC
  open ValGC
  open CompGC

  mem-gc : (i : Γ ∋ X) → MemGC i
  mem-gc {Γ = Γ ∙ X} h = record { mem-gc-Γ = ε ∙ X ; mem-gc-i = h ; mem-gc-π = wk-cong wk-wk-ε }
  mem-gc (t i) =
    let
      l = mem-gc i
    in
    record { mem-gc-Γ = mem-gc-Γ l ; mem-gc-i = mem-gc-i l ; mem-gc-π = wk-wk (mem-gc-π l) }

  mem-gc-Γ-eq : (π : Wk Γ' Γ) → (i : Γ ∋ X) → (mem-gc-Γ (mem-gc i)) ≡ (mem-gc-Γ (mem-gc (wk-mem π i)))
  mem-gc-Γ-eq wk-ε ()
  mem-gc-Γ-eq (wk-cong π) Cx.h = refl
  mem-gc-Γ-eq (wk-cong π) (Cx.t i) = mem-gc-Γ-eq π i
  mem-gc-Γ-eq (wk-wk π) Cx.h = mem-gc-Γ-eq π h
  mem-gc-Γ-eq (wk-wk π) (Cx.t i) = mem-gc-Γ-eq π (t i)

  mutual
    val-gc : (M : Val Γ X) → ValGC M
    val-gc (var i) = let l = mem-gc i in record { val-gc-Γ = mem-gc-Γ l ; val-gc-M = var (mem-gc-i l) ; val-gc-π = mem-gc-π l}
    val-gc (lam {A = X} W) with comp-gc W
    ... | record { comp-gc-Γ = ε ; comp-gc-W = W' ; comp-gc-π = wk-wk π' } = record { val-gc-Γ = ε ; val-gc-M = lam (wk-comp (wk-wk wk-id) W') ; val-gc-π = π' }
    ... | record { comp-gc-Γ = Γ' ∙ X ; comp-gc-W = W' ; comp-gc-π = wk-cong π' } = record { val-gc-Γ = Γ' ; val-gc-M = lam W' ; val-gc-π = π' }
    ... | record { comp-gc-Γ = Γ' ∙ X ; comp-gc-W = W' ; comp-gc-π = wk-wk π' } = record { val-gc-Γ = Γ' ∙ X ; val-gc-M = lam (wk-comp (wk-wk wk-id) W') ; val-gc-π = π' }
    val-gc {Γ = Γ} (pair M₁ M₂) =
            let
              v₁ = val-gc M₁
              M₁' = val-gc-M v₁
              π₁  = val-gc-π v₁
              v₂  = val-gc M₂
              M₂' = val-gc-M v₂
              π₂  = val-gc-π v₂
              j = wk-merge π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            record { val-gc-Γ = Γ' ; val-gc-M = pair (wk-val π₁' M₁') (wk-val π₂' M₂') ; val-gc-π = π }
    val-gc (pm {A = X} {B = Y} {C = Z} M N) with val-gc N
    ... | record { val-gc-Γ = Γ₂ ; val-gc-M = N₂ ; val-gc-π = wk-wk (wk-wk π₂) } =
            let
              v = val-gc M
              M₁ = val-gc-M v
              π₁ = val-gc-π v
              j = wk-merge π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            record { val-gc-Γ = Γ' ; val-gc-M = pm (wk-val π₁' M₁) (wk-val (wk-wk (wk-wk π₂')) N₂) ; val-gc-π = π }
    ... | record { val-gc-Γ = Γ₂ ∙ Y ; val-gc-M = N₂ ; val-gc-π = wk-cong (wk-cong π₂) } =
            let
              v = val-gc M
              M₁ = val-gc-M v
              π₁ = val-gc-π v
              j = wk-merge π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            record { val-gc-Γ = Γ' ; val-gc-M = pm (wk-val π₁' M₁) (wk-val (wk-cong (wk-cong π₂')) N₂) ; val-gc-π = π }
    ... | record { val-gc-Γ = Γ₂ ∙ Y ; val-gc-M = N₂ ; val-gc-π = wk-cong (wk-wk π₂) } =
            let
              v = val-gc M
              M₁ = val-gc-M v
              π₁ = val-gc-π v
              j = wk-merge π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            record { val-gc-Γ = Γ' ; val-gc-M = pm (wk-val π₁' M₁) (wk-val (wk-cong (wk-wk π₂')) N₂) ; val-gc-π = π }
    ... | record { val-gc-Γ = Γ₂ ∙ x ; val-gc-M = N₂ ; val-gc-π = wk-wk (wk-cong π₂) } =
            let
              v = val-gc M
              M₁ = val-gc-M v
              π₁ = val-gc-π v
              j = wk-merge π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            record { val-gc-Γ = Γ' ; val-gc-M = pm (wk-val π₁' M₁) (wk-val (wk-wk (wk-cong π₂')) N₂) ; val-gc-π = π }
    val-gc unit = record { val-gc-Γ = ε ; val-gc-M = unit ; val-gc-π = wk-wk-ε }

    comp-gc : (W : Comp Γ X) → CompGC W
    comp-gc (return M) = let v = val-gc M in record { comp-gc-Γ = val-gc-Γ v ; comp-gc-W = return (val-gc-M v) ; comp-gc-π = val-gc-π v }
    comp-gc (pm {A = X} {B = Y} {C = Z} M W) with comp-gc W
    ... | record { comp-gc-Γ = Γ₂ ; comp-gc-W = W₂ ; comp-gc-π = wk-wk (wk-wk π₂) } =
            let
              v = val-gc M
              M₁ = val-gc-M v
              π₁ = val-gc-π v
              j = wk-merge π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            record { comp-gc-Γ = Γ' ; comp-gc-W = pm (wk-val π₁' M₁) (wk-comp (wk-wk (wk-wk π₂')) W₂) ; comp-gc-π = π }
    ... | record { comp-gc-Γ = Γ₂ ∙ Y ; comp-gc-W = W₂ ; comp-gc-π = wk-cong (wk-cong π₂) } =
            let
              v = val-gc M
              M₁ = val-gc-M v
              π₁ = val-gc-π v
              j = wk-merge π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            record { comp-gc-Γ = Γ' ; comp-gc-W = pm (wk-val π₁' M₁) (wk-comp (wk-cong (wk-cong π₂')) W₂) ; comp-gc-π = π }
    ... | record { comp-gc-Γ = Γ₂ ∙ Y ; comp-gc-W = W₂ ; comp-gc-π = wk-cong (wk-wk π₂) } =
            let
              v = val-gc M
              M₁ = val-gc-M v
              π₁ = val-gc-π v
              j = wk-merge π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            record { comp-gc-Γ = Γ' ; comp-gc-W = pm (wk-val π₁' M₁) (wk-comp (wk-cong (wk-wk π₂')) W₂) ; comp-gc-π = π }
    ... | record { comp-gc-Γ = Γ₂ ∙ x ; comp-gc-W = W₂ ; comp-gc-π = wk-wk (wk-cong π₂) } =
            let
              v = val-gc M
              M₁ = val-gc-M v
              π₁ = val-gc-π v
              j = wk-merge π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            record { comp-gc-Γ = Γ' ; comp-gc-W = pm (wk-val π₁' M₁) (wk-comp (wk-wk (wk-cong π₂')) W₂) ; comp-gc-π = π }
    comp-gc (push {A = X} {B = Z} W₁ W₂) with comp-gc W₂
    ... | record { comp-gc-Γ = ε ; comp-gc-W = W₂' ; comp-gc-π = wk-wk π₂' } =
            let
              c = comp-gc W₁
              W₁' = comp-gc-W c
              π₁' = comp-gc-π c
              j = wk-merge π₁' π₂'
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁'' = proj₁ (proj₂ (proj₂ j))
              π₂'' = proj₂ (proj₂ (proj₂ j))
            in
            record { comp-gc-Γ = Γ' ; comp-gc-W = push (wk-comp π₁'' W₁') (wk-comp (wk-wk π₂'') W₂') ; comp-gc-π = π }
    ... | record { comp-gc-Γ = Γ₂' ∙ X ; comp-gc-W = W₂' ; comp-gc-π = wk-cong π₂' } =
            let
              c = comp-gc W₁
              W₁' = comp-gc-W c
              π₁' = comp-gc-π c
              j = wk-merge π₁' π₂'
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁'' = proj₁ (proj₂ (proj₂ j))
              π₂'' = proj₂ (proj₂ (proj₂ j))
            in
            record { comp-gc-Γ = Γ' ; comp-gc-W = push (wk-comp π₁'' W₁') (wk-comp (wk-cong π₂'') W₂') ; comp-gc-π = π }
    ... | record { comp-gc-Γ = Γ₂' ∙ X ; comp-gc-W = W₂' ; comp-gc-π = wk-wk π₂' } =
            let
              c = comp-gc W₁
              W₁' = comp-gc-W c
              π₁' = comp-gc-π c
              j = wk-merge π₁' π₂'
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁'' = proj₁ (proj₂ (proj₂ j))
              π₂'' = proj₂ (proj₂ (proj₂ j))
            in
            record { comp-gc-Γ = Γ' ; comp-gc-W = push (wk-comp π₁'' W₁') (wk-comp (wk-wk π₂'') W₂') ; comp-gc-π = π }
    comp-gc (app M N) =
            let
              v₁ = val-gc M
              M' = val-gc-M v₁
              π₁ = val-gc-π v₁
              v₂ = val-gc N
              N' = val-gc-M v₂
              π₂ = val-gc-π v₂
              j = wk-merge π₁ π₂
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁' = proj₁ (proj₂ (proj₂ j))
              π₂' = proj₂ (proj₂ (proj₂ j))
            in
            record { comp-gc-Γ = Γ' ; comp-gc-W = app (wk-val π₁' M') (wk-val π₂' N') ; comp-gc-π = π }
    comp-gc (var M) = let v = val-gc M in record { comp-gc-Γ = val-gc-Γ v ; comp-gc-W = var (val-gc-M v) ; comp-gc-π = val-gc-π v }
    comp-gc (sub {A = X} W₁ W₂) with comp-gc W₁
    ... | record { comp-gc-Γ = ε ; comp-gc-W = W₁' ; comp-gc-π = wk-wk π₁' } =
            let
              c = comp-gc W₂
              W₂' = comp-gc-W c
              π₂' = comp-gc-π c
              j = wk-merge π₁' π₂'
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁'' = proj₁ (proj₂ (proj₂ j))
              π₂'' = proj₂ (proj₂ (proj₂ j))
            in
            record { comp-gc-Γ = Γ' ; comp-gc-W = sub (wk-comp (wk-wk π₁'') W₁') (wk-comp π₂'' W₂') ; comp-gc-π = π }
    ... | record { comp-gc-Γ = Γ₁' ∙ X ; comp-gc-W = W₁' ; comp-gc-π = wk-cong π₁' } =
            let
              c = comp-gc W₂
              W₂' = comp-gc-W c
              π₂' = comp-gc-π c
              j = wk-merge π₁' π₂'
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁'' = proj₁ (proj₂ (proj₂ j))
              π₂'' = proj₂ (proj₂ (proj₂ j))
            in
            record { comp-gc-Γ = Γ' ; comp-gc-W = sub (wk-comp (wk-cong π₁'') W₁') (wk-comp π₂'' W₂') ; comp-gc-π = π }
    ... | record { comp-gc-Γ = Γ₁' ∙ X ; comp-gc-W = W₁' ; comp-gc-π = wk-wk π₁' } =
            let
              c = comp-gc W₂
              W₂' = comp-gc-W c
              π₂' = comp-gc-π c
              j = wk-merge π₁' π₂'
              Γ' = proj₁ j
              π = proj₁ (proj₂ j)
              π₁'' = proj₁ (proj₂ (proj₂ j))
              π₂'' = proj₂ (proj₂ (proj₂ j))
            in
            record { comp-gc-Γ = Γ' ; comp-gc-W = sub (wk-comp (wk-wk π₁'') W₁') (wk-comp π₂'' W₂') ; comp-gc-π = π }
  -}
