open import Inception.SystemL.Syntax

module Inception.Bisim.Sub.Triangle where

import Inception.Bisim.Sub.SystemL
import Inception.LamLamBar.CPS
open import Inception.Prelude
import Inception.Sub.Machine
import Inception.Sub.Semantics
import Inception.Sub.Syntax as I
import Inception.SystemL.CBV
open import Inception.SystemL.SN using (↦*→≈)
import Inception.Translation.LamLamBar.SystemL
import Inception.Translation.Sub.LamLamBar
import Inception.Translation.Sub.SystemL
import Inception.Translation.Sub.Triangle

private
  module B  = Inception.Bisim.Sub.SystemL
  module LS = Inception.Translation.LamLamBar.SystemL
  module IL = Inception.Translation.Sub.LamLamBar
  module IS = Inception.Translation.Sub.SystemL
  module T  = Inception.Translation.Sub.Triangle

module _ {ℛ : I.Ty} where

  private
    module M = Inception.Sub.Machine ℛ

  ------------------------------------------------------------------------
  -- syntax

  -- the machine also agrees with the composite translation, up to ≈
  --
  --   ⟨ LS.⟦ IL.⟦ M ⟧ ⟧ ∣ α ⟩ ──≈── ⟨ IS.⟦ M ⟧ ∣ α ⟩
  --          ┊                             │
  --          ≈                             ↦* (exec-coh)
  --          ↓                             ↓
  --   ⟨ ⟦ 𝐖 ⟧ⱽ ∣ α ⟩ ──────=─────── ⟨ ⟦ 𝐖 ⟧ⱽ ∣ α ⟩
  --
  -- the top ≈ is the translation triangle
  exec-∘-coh : (M : I.ε I.⊢ᶜ ℛ)
             → ε ⊢ cut IS.⟦ ℛ ⟧ LS.⟦ IL.⟦ M ⟧ᶜ ⟧ᶜ (covar here) ≈ cut IS.⟦ ℛ ⟧ (ret B.⟦ M.exec M .proj₂ .proj₁ ⟧ⱽ) (covar here) ⊣ B.Δ₀
  exec-∘-coh M = ≈-trans (cut-cong T.⟦ M ⟧ᶜ-∘ ≈-refl) (↦*→≈ (B.exec-coh M))

  ------------------------------------------------------------------------
  -- semantics

  module _ (P R : Set) where

    private
      module LC = Inception.SystemL.CBV P R
      module LL = Inception.LamLamBar.CPS R
      module IC = Inception.Sub.Semantics R

    -- LamLamBar CPS agrees with Sub CPS, hence with the machine
    --
    --   M ──────IL────── IL.⟦ M ⟧
    --   │                    │
    --   IC.⟦_⟧ᶜ tt           LL.⟦_⟧ᶜ tt
    --   ↓                    ↓
    --   λ k → k a ──=─── λ k → k a
    --
    -- both send k to k a, a = LC.⟦ ⟦ 𝐖 ⟧ⱽ ⟧ᵛ
    exec-∘-sound : (M : I.ε I.⊢ᶜ ℛ) (k : R ^ IC.⟦ ℛ ⟧)
                 → LL.⟦ IL.⟦ M ⟧ᶜ ⟧ᶜ tt k ≡ k (LC.⟦ B.⟦ M.exec M .proj₂ .proj₁ ⟧ⱽ ⟧ᵛ (tt , [ (λ ()) , k ]′))
    exec-∘-sound M k = trans (cong (λ f → f tt k) (IL.⟦_⟧ᶜ-coh R M)) (B.exec-sound P R M k)
