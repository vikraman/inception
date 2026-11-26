open import Inception.LamLamBar.Syntax using (Ty)

module Inception.Translation.Inc.Triangle (𝒫 : Ty) where

import Inception.Inc.Syntax as I
import Inception.LamLamBar.Syntax as L
open import Inception.Prelude
import Inception.SystemL.Equations as E
import Inception.SystemL.Syntax as S
import Inception.Translation.Inc.LamLamBar
import Inception.Translation.Inc.SystemL
import Inception.Translation.LamLamBar.SystemL

private
  module LS = Inception.Translation.LamLamBar.SystemL
  module IL = Inception.Translation.Inc.LamLamBar 𝒫
  module IS = Inception.Translation.Inc.SystemL LS.⟦ 𝒫 ⟧

--------------------------------------------------------------------------
-- types and contexts

-- Inc → LamLamBar → System L agrees with Inc → System L, on the nose
--
--   X ──IL.⟦_⟧── IL.⟦ X ⟧
--   │                │
--   =                LS.⟦_⟧
--   ↓                ↓
--   X ──IS.⟦_⟧── IS.⟦ X ⟧
⟦-⟧-∘-η : LS.⟦ IL.⟦ I.X ⟧ ⟧ ≡ IS.⟦ I.X ⟧
⟦-⟧-∘-η {I.`𝟙}     = refl
⟦-⟧-∘-η {X I.`× Y} = cong₂ S._`×_ (⟦-⟧-∘-η {X}) (⟦-⟧-∘-η {Y})
⟦-⟧-∘-η {X I.`⇒ Y} = cong₂ S._`⇒_ (⟦-⟧-∘-η {X}) (⟦-⟧-∘-η {Y})
⟦-⟧-∘-η {I.`ℓ}     = refl
⟦-⟧-∘-η {I.`𝓅}     = refl
{-# REWRITE ⟦-⟧-∘-η #-}

⟦-⟧ˣ-∘-η : LS.⟦ IL.⟦ I.Γ ⟧ˣ ⟧ˣ ≡ IS.⟦ I.Γ ⟧ˣ
⟦-⟧ˣ-∘-η {I.ε}     = refl
⟦-⟧ˣ-∘-η {Γ I.∙ X} = cong (S._∙ IS.⟦ X ⟧) (⟦-⟧ˣ-∘-η {Γ})
{-# REWRITE ⟦-⟧ˣ-∘-η #-}

⟦_⟧ⁱ-∘-η : (i : I.Γ I.∋ I.X) → LS.⟦ IL.⟦ i ⟧ⁱ ⟧ⁱ ≡ IS.⟦ i ⟧ⁱ
⟦ I.here ⟧ⁱ-∘-η    = refl
⟦ I.there i ⟧ⁱ-∘-η = cong S.there ⟦ i ⟧ⁱ-∘-η
{-# REWRITE ⟦_⟧ⁱ-∘-η #-}

--------------------------------------------------------------------------
-- values and computations

-- Inc → LamLamBar → System L agrees with Inc → System L, up to ≈
--
--   M ──IL.⟦_⟧── IL.⟦ M ⟧
--   │                │
--   =                LS.⟦_⟧ (up to ≈)
--   ↓                ↓
--   M ──IS.⟦_⟧── IS.⟦ M ⟧
module _ {Δ : S.Ctx} where
  private
    ⟦_⟧ᵛ : L.Γ L.⊢ᵛ L.X → LS.⟦ L.Γ ⟧ˣ S.⊢ᵛ LS.⟦ L.X ⟧ ∣ Δ
    ⟦_⟧ᵛ = LS.⟦_⟧ᵛ

    ⟦_⟧ᵗ : L.Γ L.⊢ᶜ L.X → LS.⟦ L.Γ ⟧ˣ S.⊢ᵗ LS.⟦ L.X ⟧ ∣ Δ
    ⟦_⟧ᵗ = LS.⟦_⟧ᶜ

  mutual
    ⟦_⟧ᵛ-∘ : (V : I.Γ I.⊢ᵛ I.X) → IS.⟦ I.Γ ⟧ˣ S.⊢ᵛ ⟦ IL.⟦ V ⟧ᵛ ⟧ᵛ ≈ IS.⟦ V ⟧ᵛ ∶ IS.⟦ I.X ⟧ ∣ Δ
    ⟦ I.var i ⟧ᵛ-∘    = S.≈-refl
    ⟦ I.lam M ⟧ᵛ-∘    = S.lam-cong ⟦ M ⟧ᶜ-∘
    ⟦ I.pair V W ⟧ᵛ-∘ = S.pair-cong ⟦ V ⟧ᵛ-∘ ⟦ W ⟧ᵛ-∘
    ⟦ I.unit ⟧ᵛ-∘     = S.≈-refl

    ⟦_⟧ᶜ-∘ : (M : I.Γ I.⊢ᶜ I.X) → IS.⟦ I.Γ ⟧ˣ S.⊢ᵗ ⟦ IL.⟦ M ⟧ᶜ ⟧ᵗ ≈ IS.⟦ M ⟧ᶜ ∶ IS.⟦ I.X ⟧ ∣ Δ
    ⟦ I.return V ⟧ᶜ-∘ = S.ret-cong ⟦ V ⟧ᵛ-∘
    ⟦ I.pm V M ⟧ᶜ-∘   = E.letpv-cong ⟦ V ⟧ᵛ-∘ ⟦ M ⟧ᶜ-∘
    ⟦ I.push M N ⟧ᶜ-∘ = E.lett-cong ⟦ M ⟧ᶜ-∘ ⟦ N ⟧ᶜ-∘
    ⟦ I.app V W ⟧ᶜ-∘  = E.applyL-cong ⟦ V ⟧ᵛ-∘ ⟦ W ⟧ᵛ-∘
    ⟦ I.rec V W ⟧ᶜ-∘  = S.≈-trans (E.coapp-throw ⟦ IL.⟦ V ⟧ᵛ ⟧ᵛ ⟦ IL.⟦ W ⟧ᵛ ⟧ᵛ) (E.throw-cong ⟦ V ⟧ᵛ-∘ ⟦ W ⟧ᵛ-∘)
    ⟦ I.inc M N ⟧ᶜ-∘  = S.≈-trans (E.colam-catch ⟦ IL.⟦ M ⟧ᶜ ⟧ᵗ ⟦ IL.⟦ N ⟧ᶜ ⟧ᵗ) (E.catch-cong ⟦ M ⟧ᶜ-∘ ⟦ N ⟧ᶜ-∘)
