module Inception.Translation.Sub.Triangle where

import Inception.LamLamBar.Syntax as L
open import Inception.Prelude
import Inception.Sub.Syntax as I
import Inception.SystemL.Syntax as S
import Inception.Translation.LamLamBar.SystemL
import Inception.Translation.Sub.LamLamBar
import Inception.Translation.Sub.SystemL

private
  module LS = Inception.Translation.LamLamBar.SystemL
  module IL = Inception.Translation.Sub.LamLamBar
  module IS = Inception.Translation.Sub.SystemL

--------------------------------------------------------------------------
-- types and contexts

⟦-⟧-∘-η : LS.⟦ IL.⟦ I.X ⟧ ⟧ ≡ IS.⟦ I.X ⟧
⟦-⟧-∘-η {I.`𝟙}     = refl
⟦-⟧-∘-η {X I.`× Y} = cong₂ S._`×_ (⟦-⟧-∘-η {X}) (⟦-⟧-∘-η {Y})
⟦-⟧-∘-η {X I.`⇒ Y} = cong₂ S._`⇒_ (⟦-⟧-∘-η {X}) (⟦-⟧-∘-η {Y})
⟦-⟧-∘-η {I.`ℓ}     = refl
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

module _ {Δ : S.Ctx} where
  private
    ⟦_⟧ᵛ : L.Γ L.⊢ᵛ L.X → LS.⟦ L.Γ ⟧ˣ S.⊢ᵛ LS.⟦ L.X ⟧ ∣ Δ
    ⟦_⟧ᵛ = LS.⟦_⟧ᵛ

    ⟦_⟧ᵗ : L.Γ L.⊢ᶜ L.X → LS.⟦ L.Γ ⟧ˣ S.⊢ᵗ LS.⟦ L.X ⟧ ∣ Δ
    ⟦_⟧ᵗ = LS.⟦_⟧ᶜ

  mutual
    ⟦_⟧ᵛ-∘-η : (V : I.Γ I.⊢ᵛ I.X) → ⟦ IL.⟦ V ⟧ᵛ ⟧ᵛ ≡ IS.⟦ V ⟧ᵛ
    ⟦ I.var i ⟧ᵛ-∘-η    = refl
    ⟦ I.lam M ⟧ᵛ-∘-η    = cong S.lam ⟦ M ⟧ᶜ-∘-η
    ⟦ I.pair V W ⟧ᵛ-∘-η = cong₂ S.pair ⟦ V ⟧ᵛ-∘-η ⟦ W ⟧ᵛ-∘-η
    ⟦ I.unit ⟧ᵛ-∘-η     = refl

    ⟦_⟧ᶜ-∘-η : (M : I.Γ I.⊢ᶜ I.X) → ⟦ IL.⟦ M ⟧ᶜ ⟧ᵗ ≡ IS.⟦ M ⟧ᶜ
    ⟦ I.return V ⟧ᶜ-∘-η = cong S.ret ⟦ V ⟧ᵛ-∘-η
    ⟦ I.pm V M ⟧ᶜ-∘-η   = cong₂ S.letpv ⟦ V ⟧ᵛ-∘-η ⟦ M ⟧ᶜ-∘-η
    ⟦ I.push M N ⟧ᶜ-∘-η = cong₂ S.lett ⟦ M ⟧ᶜ-∘-η ⟦ N ⟧ᶜ-∘-η
    ⟦ I.app V W ⟧ᶜ-∘-η  = cong₂ S.applyL ⟦ V ⟧ᵛ-∘-η ⟦ W ⟧ᵛ-∘-η
    ⟦ I.var V ⟧ᶜ-∘-η    = cong (λ V → S.throw V S.unit) ⟦ V ⟧ᵛ-∘-η
    ⟦ I.sub M N ⟧ᶜ-∘-η  = cong₂ (λ M N → S.catch M (S.wkᵗ N)) ⟦ M ⟧ᶜ-∘-η ⟦ N ⟧ᶜ-∘-η
