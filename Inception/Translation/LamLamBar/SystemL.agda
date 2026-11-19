open import Inception.SystemL.Syntax

module Inception.Translation.LamLamBar.SystemL where

import Inception.LamLamBar.CPS
import Inception.LamLamBar.Syntax as I
open import Inception.Prelude
open ≡-Reasoning
import Inception.SystemL.CBV

--------------------------------------------------------------------------
-- types and contexts

⟦_⟧ : I.Ty → Ty
⟦ I.`𝟙 ⟧     = `𝟙
⟦ X I.̃ ⟧     = ¬ ⟦ X ⟧
⟦ X I.`× Y ⟧ = ⟦ X ⟧ `× ⟦ Y ⟧
⟦ X I.`⇒ Y ⟧ = ⟦ X ⟧ `⇒ ⟦ Y ⟧
⟦ X I.`+ Y ⟧ = ⟦ X ⟧ `+ ⟦ Y ⟧

open import Inception.Ctx.Map ⟦_⟧ public

module _ {Δ : Ctx} where

  ------------------------------------------------------------------------
  -- values and computations

  mutual
    ⟦_⟧ᵛ : I.Γ I.⊢ᵛ I.X → ⟦ I.Γ ⟧ˣ ⊢ᵛ ⟦ I.X ⟧ ∣ Δ
    ⟦ I.var i ⟧ᵛ    = var ⟦ i ⟧ⁱ
    ⟦ I.lam M ⟧ᵛ    = lam ⟦ M ⟧ᶜ
    ⟦ I.pair V W ⟧ᵛ = pair ⟦ V ⟧ᵛ ⟦ W ⟧ᵛ
    ⟦ I.unit ⟧ᵛ     = unit
    ⟦ I.inl V ⟧ᵛ    = inl ⟦ V ⟧ᵛ
    ⟦ I.inr V ⟧ᵛ    = inr ⟦ V ⟧ᵛ

    ⟦_⟧ᶜ : I.Γ I.⊢ᶜ I.X → ⟦ I.Γ ⟧ˣ ⊢ᵗ ⟦ I.X ⟧ ∣ Δ
    ⟦ I.return V ⟧ᶜ   = ret ⟦ V ⟧ᵛ
    ⟦ I.pm V M ⟧ᶜ     = letpv ⟦ V ⟧ᵛ ⟦ M ⟧ᶜ
    ⟦ I.push M N ⟧ᶜ   = lett ⟦ M ⟧ᶜ ⟦ N ⟧ᶜ
    ⟦ I.case V M N ⟧ᶜ = casev ⟦ V ⟧ᵛ ⟦ M ⟧ᶜ ⟦ N ⟧ᶜ
    ⟦ I.app V W ⟧ᶜ    = applyL ⟦ V ⟧ᵛ ⟦ W ⟧ᵛ
    ⟦ I.colam M ⟧ᶜ    = colam ⟦ M ⟧ᶜ
    ⟦ I.coapp M V ⟧ᶜ  = coapp ⟦ M ⟧ᶜ ⟦ V ⟧ᵛ

  ⟦_⟧ˢ : I.Γ I.⊢ I.Δ → ⟦ I.Γ ⟧ˣ ⊢ ⟦ I.Δ ⟧ˣ ∣ Δ
  ⟦ I.sub-ε ⟧ˢ      = sub-ε
  ⟦ I.sub-ex θ V ⟧ˢ = sub-ex ⟦ θ ⟧ˢ ⟦ V ⟧ᵛ

  ------------------------------------------------------------------------
  -- weakening

  mutual
    ⟦-⟧ᵛ-wk-η : (π : I.Γ I.⊇ I.Δ) (V : I.Δ I.⊢ᵛ I.X) → ⟦ I.wk-val π V ⟧ᵛ ≡ wk-val ⟦ π ⟧ʷ wk-id ⟦ V ⟧ᵛ
    ⟦-⟧ᵛ-wk-η π (I.var i)    = refl
    ⟦-⟧ᵛ-wk-η π (I.lam M)    = cong lam (⟦-⟧ᶜ-wk-η (I.wk-cong π) M)
    ⟦-⟧ᵛ-wk-η π (I.pair V W) = cong₂ pair (⟦-⟧ᵛ-wk-η π V) (⟦-⟧ᵛ-wk-η π W)
    ⟦-⟧ᵛ-wk-η π I.unit       = refl
    ⟦-⟧ᵛ-wk-η π (I.inl V)    = cong inl (⟦-⟧ᵛ-wk-η π V)
    ⟦-⟧ᵛ-wk-η π (I.inr V)    = cong inr (⟦-⟧ᵛ-wk-η π V)

    ⟦-⟧ᶜ-wk-η : (π : I.Γ I.⊇ I.Δ) (M : I.Δ I.⊢ᶜ I.X) → ⟦ I.wk-comp π M ⟧ᶜ ≡ wk-tm ⟦ π ⟧ʷ wk-id ⟦ M ⟧ᶜ
    ⟦-⟧ᶜ-wk-η π (I.return V)   = cong ret (⟦-⟧ᵛ-wk-η π V)
    ⟦-⟧ᶜ-wk-η π (I.pm V M)     = cong₂ letpv (⟦-⟧ᵛ-wk-η π V) (⟦-⟧ᶜ-wk-η (I.wk-cong (I.wk-cong π)) M)
    ⟦-⟧ᶜ-wk-η π (I.push M N)   = cong₂ lett (⟦-⟧ᶜ-wk-η π M) (⟦-⟧ᶜ-wk-η (I.wk-cong π) N)
    ⟦-⟧ᶜ-wk-η π (I.case V M N) = cong₃ casev (⟦-⟧ᵛ-wk-η π V) (⟦-⟧ᶜ-wk-η (I.wk-cong π) M) (⟦-⟧ᶜ-wk-η (I.wk-cong π) N)
    ⟦-⟧ᶜ-wk-η π (I.app V W)    = cong₂ applyL (⟦-⟧ᵛ-wk-η π V) (⟦-⟧ᵛ-wk-η π W)
    ⟦-⟧ᶜ-wk-η π (I.colam M)    = cong colam (⟦-⟧ᶜ-wk-η (I.wk-cong π) M)
    ⟦-⟧ᶜ-wk-η π (I.coapp M V)  = cong₂ coapp (⟦-⟧ᶜ-wk-η π M) (⟦-⟧ᵛ-wk-η π V)

  {-# REWRITE ⟦-⟧ᵛ-wk-η ⟦-⟧ᶜ-wk-η #-}

--------------------------------------------------------------------------
-- semantics

module _ (P R : Set) where

  private
    module LC = Inception.SystemL.CBV P R
    module IC = Inception.LamLamBar.CPS R
    module LS = Sem LC.⟦_⟧
    module IS = I.Sem IC.⟦_⟧

  ------------------------------------------------------------------------
  -- types and contexts

  ⟦-⟧-coh : LC.⟦ ⟦ I.X ⟧ ⟧ ≡ IC.⟦ I.X ⟧
  ⟦-⟧-coh {I.`𝟙}     = refl
  ⟦-⟧-coh {X I.̃}     = cong (R ^_) (⟦-⟧-coh {X})
  ⟦-⟧-coh {X I.`× Y} = cong₂ _×_ (⟦-⟧-coh {X}) (⟦-⟧-coh {Y})
  ⟦-⟧-coh {X I.`⇒ Y} = cong₂ (λ A B → A → IC.K B) (⟦-⟧-coh {X}) (⟦-⟧-coh {Y})
  ⟦-⟧-coh {X I.`+ Y} = cong₂ _⊎_ (⟦-⟧-coh {X}) (⟦-⟧-coh {Y})
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
    ⟦ I.inl V ⟧ᵛ-coh γ κ    = cong inj₁ (⟦ V ⟧ᵛ-coh γ κ)
    ⟦ I.inr V ⟧ᵛ-coh γ κ    = cong inj₂ (⟦ V ⟧ᵛ-coh γ κ)

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
    ⟦ I.case V M N ⟧ᶜ-coh γ κ k = begin
        LC.⟦ ⟦ I.case V M N ⟧ᶜ ⟧ᵗ (γ , κ) k
      ≡⟨ cong [ _ , _ ]′ (⟦ V ⟧ᵛ-coh γ _) ⟩
        [ (λ a → LC.⟦ ⟦ M ⟧ᶜ ⟧ᵗ ((γ , a) , κ) k) , (λ b → LC.⟦ ⟦ N ⟧ᶜ ⟧ᵗ ((γ , b) , κ) k) ]′ (IC.⟦ V ⟧ᵛ γ)
      ≡⟨ cong₂ (λ f g → [ f , g ]′ (IC.⟦ V ⟧ᵛ γ)) (funext λ a → ⟦ M ⟧ᶜ-coh (γ , a) _ k) (funext λ b → ⟦ N ⟧ᶜ-coh (γ , b) _ k) ⟩
        [ (λ a → IC.⟦ M ⟧ᶜ (γ , a) k) , (λ b → IC.⟦ N ⟧ᶜ (γ , b) k) ]′ (IC.⟦ V ⟧ᵛ γ)
      ≡⟨ distl-[ IC.⟦ M ⟧ᶜ , IC.⟦ N ⟧ᶜ ] γ (IC.⟦ V ⟧ᵛ γ) k ⟩
        IC.⟦ I.case V M N ⟧ᶜ γ k
      ∎
    ⟦ I.app V W ⟧ᶜ-coh γ κ k = cong₂ (λ f a → f a k) (⟦ V ⟧ᵛ-coh γ _) (⟦ W ⟧ᵛ-coh γ _)
    ⟦ I.colam M ⟧ᶜ-coh γ κ k = ⟦ M ⟧ᶜ-coh _ _ _
    ⟦ I.coapp M V ⟧ᶜ-coh γ κ k = begin
        LC.⟦ ⟦ I.coapp M V ⟧ᶜ ⟧ᵗ (γ , κ) k
      ≡⟨ ⟦ M ⟧ᶜ-coh γ _ _ ⟩
        IC.⟦ M ⟧ᶜ γ [ LC.⟦ ⟦ V ⟧ᵛ ⟧ᵛ (γ , κ) , k ]′
      ≡⟨ cong (λ f → IC.⟦ M ⟧ᶜ γ [ f , k ]′) (⟦ V ⟧ᵛ-coh γ _) ⟩
        IC.⟦ I.coapp M V ⟧ᶜ γ k
      ∎

  ------------------------------------------------------------------------
  -- soundness

  module _ {Δ : Ctx} where
    private
      ⟦_⟧ᵗ : I.Γ I.⊢ᶜ I.X → ⟦ I.Γ ⟧ˣ ⊢ᵗ ⟦ I.X ⟧ ∣ Δ
      ⟦_⟧ᵗ = ⟦_⟧ᶜ

    sound : I.Γ I.⊢ᶜ I.M ≈ I.N ∶ I.X → LC.⟦ ⟦ I.M ⟧ᵗ ⟧ᵗ ≡ LC.⟦ ⟦ I.N ⟧ᵗ ⟧ᵗ
    sound {M = M} {N = N} p =
      funext λ { (γ , κ) → funext λ k → begin
          LC.⟦ ⟦ M ⟧ᵗ ⟧ᵗ (γ , κ) k
        ≡⟨ ⟦ M ⟧ᶜ-coh γ κ k ⟩
          IC.⟦ M ⟧ᶜ γ k
        ≡⟨ cong (λ f → f γ k) (IC.eqComp p) ⟩
          IC.⟦ N ⟧ᶜ γ k
        ≡⟨ ⟦ N ⟧ᶜ-coh γ κ k ⟨
          LC.⟦ ⟦ N ⟧ᵗ ⟧ᵗ (γ , κ) k
        ∎ }
