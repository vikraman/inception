open import Inception.SystemL.Syntax

module Inception.Translation.Sub.SystemL where

open import Inception.Prelude
open ≡-Reasoning
import Inception.Sub.Semantics
import Inception.Sub.Syntax as I
import Inception.SystemL.CBV

--------------------------------------------------------------------------
-- types and contexts

⟦_⟧ : I.Ty → Ty
⟦ I.`𝟙 ⟧     = `𝟙
⟦ X I.`× Y ⟧ = ⟦ X ⟧ `× ⟦ Y ⟧
⟦ X I.`⇒ Y ⟧ = ⟦ X ⟧ `⇒ ⟦ Y ⟧
⟦ I.`ℓ ⟧     = ¬ `𝟙

open import Inception.Ctx.Map ⟦_⟧ public

--------------------------------------------------------------------------
-- values and computations

mutual
  ⟦_⟧ᵛ : I.Γ I.⊢ᵛ I.X → ⟦ I.Γ ⟧ˣ ⊢ᵛ ⟦ I.X ⟧ ∣ Δ
  ⟦ I.var i ⟧ᵛ    = var ⟦ i ⟧ⁱ
  ⟦ I.lam M ⟧ᵛ    = lam ⟦ M ⟧ᶜ
  ⟦ I.pair V W ⟧ᵛ = pair ⟦ V ⟧ᵛ ⟦ W ⟧ᵛ
  ⟦ I.unit ⟧ᵛ     = unit

  ⟦_⟧ᶜ : I.Γ I.⊢ᶜ I.X → ⟦ I.Γ ⟧ˣ ⊢ᵗ ⟦ I.X ⟧ ∣ Δ
  ⟦ I.return V ⟧ᶜ = ret ⟦ V ⟧ᵛ
  ⟦ I.pm V M ⟧ᶜ   = letpv ⟦ V ⟧ᵛ ⟦ M ⟧ᶜ
  ⟦ I.push M N ⟧ᶜ = lett ⟦ M ⟧ᶜ ⟦ N ⟧ᶜ
  ⟦ I.app V W ⟧ᶜ  = applyL ⟦ V ⟧ᵛ ⟦ W ⟧ᵛ
  ⟦ I.var V ⟧ᶜ    = throw ⟦ V ⟧ᵛ unit
  ⟦ I.sub M N ⟧ᶜ  = catch ⟦ M ⟧ᶜ (wkᵗ ⟦ N ⟧ᶜ)

⟦_⟧ˢ : I.Γ I.⊢ I.Δ → ⟦ I.Γ ⟧ˣ ⊢ ⟦ I.Δ ⟧ˣ ∣ Δ
⟦ I.sub-ε ⟧ˢ      = sub-ε
⟦ I.sub-ex θ V ⟧ˢ = sub-ex ⟦ θ ⟧ˢ ⟦ V ⟧ᵛ

--------------------------------------------------------------------------
-- semantics

module _ (P R : Set) where

  private
    module LC = Inception.SystemL.CBV P R
    module IC = Inception.Sub.Semantics R
    module LS = Sem LC.⟦_⟧
    module IS = I.Sem IC.⟦_⟧

  ------------------------------------------------------------------------
  -- types and contexts

  ⟦-⟧-coh : LC.⟦ ⟦ I.X ⟧ ⟧ ≡ IC.⟦ I.X ⟧
  ⟦-⟧-coh {I.`𝟙}     = refl
  ⟦-⟧-coh {X I.`× Y} = cong₂ _×_ (⟦-⟧-coh {X}) (⟦-⟧-coh {Y})
  ⟦-⟧-coh {X I.`⇒ Y} = cong₂ (λ A B → A → IC.K B) (⟦-⟧-coh {X}) (⟦-⟧-coh {Y})
  ⟦-⟧-coh {I.`ℓ}     = refl
  {-# REWRITE ⟦-⟧-coh #-}

  ⟦-⟧ˣ-coh : LS.⟦ ⟦ I.Γ ⟧ˣ ⟧ˣ ≡ IS.⟦ I.Γ ⟧ˣ
  ⟦-⟧ˣ-coh {I.ε}     = refl
  ⟦-⟧ˣ-coh {Γ I.∙ X} = cong (_× IC.⟦ X ⟧) (⟦-⟧ˣ-coh {Γ})
  {-# REWRITE ⟦-⟧ˣ-coh #-}

  ⟦_⟧ⁱ-coh : (i : I.Γ I.∋ I.X) → LS.⟦ ⟦ i ⟧ⁱ ⟧ᵐ ≡ IS.⟦ i ⟧ᵐ
  ⟦ I.here ⟧ⁱ-coh    = refl
  ⟦ I.there i ⟧ⁱ-coh = cong (proj₁ ；_) ⟦ i ⟧ⁱ-coh
  {-# REWRITE ⟦_⟧ⁱ-coh #-}

  ------------------------------------------------------------------------
  -- values and computations

  mutual
    ⟦_⟧ᵛ-coh : (V : I.Γ I.⊢ᵛ I.X) (γ : IS.⟦ I.Γ ⟧ˣ) (κ : R ^ LS.⟦ Δ ⟧ˣ̃)
             → LC.⟦ ⟦ V ⟧ᵛ ⟧ᵛ (γ , κ) ≡ IC.⟦ V ⟧ᵛ γ
    ⟦ I.var i ⟧ᵛ-coh γ κ    = refl
    ⟦ I.lam M ⟧ᵛ-coh γ κ    = funext λ a → funext λ k → ⟦ M ⟧ᶜ-coh (γ , a) κ k
    ⟦ I.pair V W ⟧ᵛ-coh γ κ = cong₂ _,_ (⟦ V ⟧ᵛ-coh γ κ) (⟦ W ⟧ᵛ-coh γ κ)
    ⟦ I.unit ⟧ᵛ-coh γ κ     = refl

    ⟦_⟧ᶜ-coh : (M : I.Γ I.⊢ᶜ I.X) (γ : IS.⟦ I.Γ ⟧ˣ) (κ : R ^ LS.⟦ Δ ⟧ˣ̃) (k : R ^ IC.⟦ I.X ⟧)
             → LC.⟦ ⟦ M ⟧ᶜ ⟧ᵗ (γ , κ) k ≡ IC.⟦ M ⟧ᶜ γ k
    ⟦ I.return V ⟧ᶜ-coh γ κ k = cong k (⟦ V ⟧ᵛ-coh γ κ)
    ⟦ I.pm V M ⟧ᶜ-coh γ κ k = begin
        LC.⟦ ⟦ I.pm V M ⟧ᶜ ⟧ᵗ (γ , κ) k
      ≡⟨ ⟦ M ⟧ᶜ-coh _ _ k ⟩
        IC.⟦ M ⟧ᶜ ((γ , proj₁ (LC.⟦ ⟦ V ⟧ᵛ ⟧ᵛ (γ , κ))) , proj₂ (LC.⟦ ⟦ V ⟧ᵛ ⟧ᵛ (γ , κ))) k
      ≡⟨ cong₂ (λ a b → IC.⟦ M ⟧ᶜ ((γ , a) , b) k) (cong proj₁ (⟦ V ⟧ᵛ-coh γ _)) (cong proj₂ (⟦ V ⟧ᵛ-coh γ _)) ⟩
        IC.⟦ I.pm V M ⟧ᶜ γ k
      ∎
    ⟦ I.push M N ⟧ᶜ-coh γ κ k = begin
        LC.⟦ ⟦ I.push M N ⟧ᶜ ⟧ᵗ (γ , κ) k
      ≡⟨ ⟦ M ⟧ᶜ-coh γ _ _ ⟩
        IC.⟦ M ⟧ᶜ γ (λ a → LC.⟦ ⟦ N ⟧ᶜ ⟧ᵗ ((γ , a) , κ) k)
      ≡⟨ cong (IC.⟦ M ⟧ᶜ γ) (funext λ a → ⟦ N ⟧ᶜ-coh (γ , a) _ k) ⟩
        IC.⟦ I.push M N ⟧ᶜ γ k
      ∎
    ⟦ I.app V W ⟧ᶜ-coh γ κ k = cong₂ (λ f a → f a k) (⟦ V ⟧ᵛ-coh γ _) (⟦ W ⟧ᵛ-coh γ _)
    ⟦ I.var V ⟧ᶜ-coh γ κ k   = cong (λ f → f tt) (⟦ V ⟧ᵛ-coh γ _)
    ⟦ I.sub M N ⟧ᶜ-coh γ κ k = begin
        LC.⟦ ⟦ I.sub M N ⟧ᶜ ⟧ᵗ (γ , κ) k
      ≡⟨ ⟦ M ⟧ᶜ-coh _ _ k ⟩
        IC.⟦ M ⟧ᶜ (γ , λ _ → LC.⟦ ⟦ N ⟧ᶜ ⟧ᵗ (γ , κ) k) k
      ≡⟨ cong (λ h → IC.⟦ M ⟧ᶜ (γ , h) k) (funext λ _ → ⟦ N ⟧ᶜ-coh γ _ k) ⟩
        IC.⟦ I.sub M N ⟧ᶜ γ k
      ∎

  ------------------------------------------------------------------------
  -- soundness

  module _ {Δ : Ctx} where
    private
      ⟦_⟧ᵗ : I.Γ I.⊢ᶜ I.X → ⟦ I.Γ ⟧ˣ ⊢ᵗ ⟦ I.X ⟧ ∣ Δ
      ⟦_⟧ᵗ = ⟦_⟧ᶜ

    sound : I.Γ I.⊢ᶜ I.M₁ ≈ I.M₂ ∶ I.X → LC.⟦ ⟦ I.M₁ ⟧ᵗ ⟧ᵗ ≡ LC.⟦ ⟦ I.M₂ ⟧ᵗ ⟧ᵗ
    sound {M₁ = M} {M₂ = N} p =
      funext λ { (γ , κ) → funext λ k → begin
          LC.⟦ ⟦ M ⟧ᵗ ⟧ᵗ (γ , κ) k
        ≡⟨ ⟦ M ⟧ᶜ-coh γ κ k ⟩
          IC.⟦ M ⟧ᶜ γ k
        ≡⟨ cong (λ f → f γ k) (IC.eqComp p) ⟩
          IC.⟦ N ⟧ᶜ γ k
        ≡⟨ ⟦ N ⟧ᶜ-coh γ κ k ⟨
          LC.⟦ ⟦ N ⟧ᵗ ⟧ᵗ (γ , κ) k
        ∎ }
