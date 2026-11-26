open import Inception.SystemL.Syntax

module Inception.Bisim.Sub.SystemL where

open import Inception.Prelude
open import Inception.Rewriting
import Inception.Sub.Machine
import Inception.Sub.Semantics
import Inception.Sub.Syntax as I
import Inception.SystemL.CBV
open import Inception.SystemL.SN
  using ( _↦_; _↦*_; ↦-det; ↦*→≈; fst-step; snd-step; pass-step
        ; catch-red; throw-red; lett-red; applyL-red; projFst-red; projSnd-red; frame-red; lam-red )
  renaming (eval to evalᴸ)
open import Inception.Translation.Sub.SystemL

module _ {ℛ : I.Ty} where

  private
    module M = Inception.Sub.Machine ℛ

  open M using ( MVal; unitᵛ; pairᵛ; cloᵛ; jumpᵛ; MEnv; ⋄; _·_; CStack; ◻; <_；_>∷_
               ; CState; ⟨_╎_⟩; ⟨_╎_╎_⟩; _→ᶜ_; eval→; return→; push→; sub→; var→; pmᶜ→; app→ )

  Δ₀ : Ctx
  Δ₀ = ε ∙ ⟦ ℛ ⟧

  ------------------------------------------------------------------------
  -- decoding

  mutual
    ⟦_⟧ᴱ : MEnv I.Γ → ε ⊢ ⟦ I.Γ ⟧ˣ ∣ Δ₀
    ⟦ ⋄ ⟧ᴱ             = sub-ε
    ⟦ γ · 𝐖 ⟧ᴱ         = sub-ex ⟦ γ ⟧ᴱ ⟦ 𝐖 ⟧ⱽ

    ⟦_⟧ⱽ : MVal I.X → ε ⊢ᵛ ⟦ I.X ⟧ ∣ Δ₀
    ⟦ unitᵛ ⟧ⱽ         = unit
    ⟦ pairᵛ 𝐕 𝐖 ⟧ⱽ     = pair ⟦ 𝐕 ⟧ⱽ ⟦ 𝐖 ⟧ⱽ
    ⟦ cloᵛ M γ ⟧ⱽ      =
      -- (λx. ⟦ M ⟧ᶜ)[⟦ γ ⟧ᴱ]
      sub-val ⟦ γ ⟧ᴱ cosub-id (lam ⟦ M ⟧ᶜ)
    ⟦ jumpᵛ M γ K ⟧ⱽ   =
      -- cont (μ̃x. ⟨ ⟦ M ⟧ᶜ[⟦ γ ⟧ᴱ] ∣ ⟦ K ⟧ᴷ ⟩)
      cont (μ̃ (cut _ (sub-tm (sub-lift ⟦ γ ⟧ᴱ) cosub-id (wkᵗ ⟦ M ⟧ᶜ)) (wkᵏ ⟦ K ⟧ᴷ)))

    ⟦_⟧ᴷ : CStack I.X → ε ∣ ⟦ I.X ⟧ ⊢ᵏ Δ₀
    ⟦ ◻ ⟧ᴷ             = covar here
    ⟦ < M ； γ >∷ K ⟧ᴷ =
      -- μ̃x. ⟨ ⟦ M ⟧ᶜ[⟦ γ ⟧ᴱ , x] ∣ ⟦ K ⟧ᴷ ⟩
      μ̃ (cut _ (sub-tm (sub-lift ⟦ γ ⟧ᴱ) cosub-id ⟦ M ⟧ᶜ) (wkᵏ ⟦ K ⟧ᴷ))

  ⟦_⟧ˢᵗ : CState → ε ⊢ Δ₀
  ⟦ ⟨ 𝐖 ╎ K ⟩ ⟧ˢᵗ      = cut _ (ret ⟦ 𝐖 ⟧ⱽ) ⟦ K ⟧ᴷ
  ⟦ ⟨ M ╎ γ ╎ K ⟩ ⟧ˢᵗ  =
    -- ⟨ ⟦ M ⟧ᶜ[⟦ γ ⟧ᴱ] ∣ ⟦ K ⟧ᴷ ⟩
    cut _ (sub-tm ⟦ γ ⟧ᴱ cosub-id ⟦ M ⟧ᶜ) ⟦ K ⟧ᴷ

  ------------------------------------------------------------------------
  -- coherences

  lookup-coh : (i : I.Γ I.∋ I.X) (γ : MEnv I.Γ) → sub-mem ⟦ γ ⟧ᴱ ⟦ i ⟧ⁱ ≡ ⟦ M.lookup i γ ⟧ⱽ
  lookup-coh I.here      (γ · 𝐖) = refl
  lookup-coh (I.there i) (γ · 𝐖) = lookup-coh i γ

  eval-coh : (W : I.Γ I.⊢ᵛ I.X) (γ : MEnv I.Γ) → sub-val ⟦ γ ⟧ᴱ cosub-id ⟦ W ⟧ᵛ ≡ ⟦ M.eval W γ ⟧ⱽ
  eval-coh (I.var i)    γ = lookup-coh i γ
  eval-coh (I.lam M)    γ = refl
  eval-coh (I.pair V W) γ = cong₂ pair (eval-coh V γ) (eval-coh W γ)
  eval-coh I.unit       γ = refl

  init-coh : (M : I.ε I.⊢ᶜ ℛ) → ⟦ ⟨ M ╎ ⋄ ╎ ◻ ⟩ ⟧ˢᵗ ≡ cut ⟦ ℛ ⟧ ⟦ M ⟧ᶜ (covar here)
  init-coh M = cong (λ N → cut ⟦ ℛ ⟧ N (covar here)) (sub-tm-id-β ⟦ M ⟧ᶜ)

  halt-coh : {σ : CState} → M.Normal σ → Reduction.Normal (_↦_ {Γ = ε} {Δ = Δ₀}) ⟦ σ ⟧ˢᵗ
  halt-coh {σ} n with M.halting-state σ n
  ... | 𝐖 , refl = λ ()

  final-coh : (σ : CState) (n : M.Normal σ) → ⟦ σ ⟧ˢᵗ ≡ cut ⟦ ℛ ⟧ (ret ⟦ M.halting-state σ n .proj₁ ⟧ⱽ) (covar here)
  final-coh σ n with M.halting-state σ n
  ... | 𝐖 , refl = refl

  ------------------------------------------------------------------------
  -- simulation

  sim-app : (V : I.Γ I.⊢ᵛ (I.X I.`⇒ I.Y)) (W : I.Γ I.⊢ᵛ I.X) (γ : MEnv I.Γ) (K : CStack I.Y)
          → ⟦ ⟨ I.app V W ╎ γ ╎ K ⟩ ⟧ˢᵗ ↦* ⟦ M.eval-clo V W γ K ⟧ˢᵗ
  sim-app {X = X} {Y = Y} V W γ K with M.eval V γ | eval-coh V γ
  ... | cloᵛ N δ | eq = begin
    cut ⟦ Y ⟧ (sub-tm ⟦ γ ⟧ᴱ cosub-id (applyL ⟦ V ⟧ᵛ ⟦ W ⟧ᵛ)) ⟦ K ⟧ᴷ
      ⟶*⟨ applyL-red ⟦ γ ⟧ᴱ cosub-id ⟦ V ⟧ᵛ ⟦ W ⟧ᵛ ⟦ K ⟧ᴷ ⟩
    cut (⟦ X ⟧ `⇒ ⟦ Y ⟧) (ret (sub-val ⟦ γ ⟧ᴱ cosub-id ⟦ V ⟧ᵛ)) (app (sub-val ⟦ γ ⟧ᴱ cosub-id ⟦ W ⟧ᵛ) ⟦ K ⟧ᴷ)
      ≡⟨ cong₂ (λ U₁ U₂ → cut (⟦ X ⟧ `⇒ ⟦ Y ⟧) (ret U₁) (app U₂ ⟦ K ⟧ᴷ)) eq (eval-coh W γ) ⟩
    cut (⟦ X ⟧ `⇒ ⟦ Y ⟧) (ret (sub-val ⟦ δ ⟧ᴱ cosub-id (lam ⟦ N ⟧ᶜ))) (app ⟦ M.eval W γ ⟧ⱽ ⟦ K ⟧ᴷ)
      ⟶*⟨ lam-red ⟦ δ ⟧ᴱ cosub-id ⟦ N ⟧ᶜ ⟦ M.eval W γ ⟧ⱽ ⟦ K ⟧ᴷ ⟩
    cut ⟦ Y ⟧ (sub-tm (sub-ex ⟦ δ ⟧ᴱ ⟦ M.eval W γ ⟧ⱽ) cosub-id ⟦ N ⟧ᶜ) ⟦ K ⟧ᴷ
      ∎
    where open StarReasoning (_↦_ {Γ = ε} {Δ = Δ₀})

  sim-var : (W : I.Γ I.⊢ᵛ I.`ℓ) (γ : MEnv I.Γ) (K : CStack I.X)
          → ⟦ ⟨ I.var W ╎ γ ╎ K ⟩ ⟧ˢᵗ ↦* ⟦ M.eval-jump W γ ⟧ˢᵗ
  sim-var {X = X} W γ K with M.eval W γ | eval-coh W γ
  ... | jumpᵛ {X = Y} N δ L | eq = begin
    cut ⟦ X ⟧ (sub-tm ⟦ γ ⟧ᴱ cosub-id (throw ⟦ W ⟧ᵛ unit)) ⟦ K ⟧ᴷ
      ⟶*⟨ throw-red ⟦ γ ⟧ᴱ cosub-id ⟦ W ⟧ᵛ unit ⟦ K ⟧ᴷ ⟩
    cut (¬ `𝟙) (ret (sub-val ⟦ γ ⟧ᴱ cosub-id ⟦ W ⟧ᵛ)) (pass unit)
      ≡⟨ cong (λ U → cut (¬ `𝟙) (ret U) (pass unit)) eq ⟩
    cut (¬ `𝟙) (ret ⟦ jumpᵛ N δ L ⟧ⱽ) (pass unit)
      ⟶⟨ pass-step ⟩
    cut `𝟙 (ret unit) (μ̃ (cut ⟦ Y ⟧ (sub-tm (sub-lift ⟦ δ ⟧ᴱ) cosub-id (wkᵗ ⟦ N ⟧ᶜ)) (wkᵏ ⟦ L ⟧ᴷ)))
      ⟶*⟨ frame-red ⟦ δ ⟧ᴱ cosub-id unit (wkᵗ ⟦ N ⟧ᶜ) ⟦ L ⟧ᴷ ⟩
    cut ⟦ Y ⟧ (sub-tm ⟦ δ ⟧ᴱ cosub-id ⟦ N ⟧ᶜ) ⟦ L ⟧ᴷ
      ∎
    where open StarReasoning (_↦_ {Γ = ε} {Δ = Δ₀})

  sim-pm : (W : I.Γ I.⊢ᵛ (I.X I.`× I.Y)) (M : ((I.Γ I.∙ I.X) I.∙ I.Y) I.⊢ᶜ I.Z) (γ : MEnv I.Γ) (K : CStack I.Z)
         → ⟦ ⟨ I.pm W M ╎ γ ╎ K ⟩ ⟧ˢᵗ ↦* ⟦ ⟨ M ╎ γ · M.eval₁ W γ · M.eval₂ W γ ╎ K ⟩ ⟧ˢᵗ
  sim-pm {X = X} {Y = Y} {Z = Z} W M γ K with M.eval W γ | eval-coh W γ
  ... | pairᵛ 𝐕 𝐖 | eq = begin
    cut ⟦ Z ⟧ (sub-tm θ cosub-id (lett (projFst ⟦ W ⟧ᵛ) (lett (projSnd (wkᵛ ⟦ W ⟧ᵛ)) ⟦ M ⟧ᶜ))) ⟦ K ⟧ᴷ
      ⟶*⟨ lett-red θ cosub-id (projFst ⟦ W ⟧ᵛ) (lett (projSnd (wkᵛ ⟦ W ⟧ᵛ)) ⟦ M ⟧ᶜ) ⟦ K ⟧ᴷ ⟩
    cut ⟦ X ⟧ (sub-tm θ cosub-id (projFst ⟦ W ⟧ᵛ)) Lᶠ
      ⟶*⟨ projFst-red θ cosub-id ⟦ W ⟧ᵛ Lᶠ ⟩
    cut (⟦ X ⟧ `× ⟦ Y ⟧) (ret (sub-val θ cosub-id ⟦ W ⟧ᵛ)) (fst Lᶠ)
      ≡⟨ cong (λ U → cut (⟦ X ⟧ `× ⟦ Y ⟧) (ret U) (fst Lᶠ)) eq ⟩
    cut (⟦ X ⟧ `× ⟦ Y ⟧) (ret (pair ⟦ 𝐕 ⟧ⱽ ⟦ 𝐖 ⟧ⱽ)) (fst Lᶠ)
      ⟶⟨ fst-step ⟩
    cut ⟦ X ⟧ (ret ⟦ 𝐕 ⟧ⱽ) Lᶠ
      ⟶*⟨ frame-red θ cosub-id ⟦ 𝐕 ⟧ⱽ (lett (projSnd (wkᵛ ⟦ W ⟧ᵛ)) ⟦ M ⟧ᶜ) ⟦ K ⟧ᴷ ⟩
    cut ⟦ Z ⟧ (sub-tm φ cosub-id (lett (projSnd (wkᵛ ⟦ W ⟧ᵛ)) ⟦ M ⟧ᶜ)) ⟦ K ⟧ᴷ
      ⟶*⟨ lett-red φ cosub-id (projSnd (wkᵛ ⟦ W ⟧ᵛ)) ⟦ M ⟧ᶜ ⟦ K ⟧ᴷ ⟩
    cut ⟦ Y ⟧ (sub-tm φ cosub-id (projSnd (wkᵛ ⟦ W ⟧ᵛ))) Lˢ
      ⟶*⟨ projSnd-red φ cosub-id (wkᵛ ⟦ W ⟧ᵛ) Lˢ ⟩
    cut (⟦ X ⟧ `× ⟦ Y ⟧) (ret (sub-val φ cosub-id (wkᵛ ⟦ W ⟧ᵛ))) (snd Lˢ)
      ≡⟨ cong (λ U → cut (⟦ X ⟧ `× ⟦ Y ⟧) (ret U) (snd Lˢ)) eq ⟩
    cut (⟦ X ⟧ `× ⟦ Y ⟧) (ret (pair ⟦ 𝐕 ⟧ⱽ ⟦ 𝐖 ⟧ⱽ)) (snd Lˢ)
      ⟶⟨ snd-step ⟩
    cut ⟦ Y ⟧ (ret ⟦ 𝐖 ⟧ⱽ) Lˢ
      ⟶*⟨ frame-red φ cosub-id ⟦ 𝐖 ⟧ⱽ ⟦ M ⟧ᶜ ⟦ K ⟧ᴷ ⟩
    cut ⟦ Z ⟧ (sub-tm (sub-ex φ ⟦ 𝐖 ⟧ⱽ) cosub-id ⟦ M ⟧ᶜ) ⟦ K ⟧ᴷ
      ∎
    where
    open StarReasoning (_↦_ {Γ = ε} {Δ = Δ₀})
    θ  = ⟦ γ ⟧ᴱ
    φ  = sub-ex θ ⟦ 𝐕 ⟧ⱽ
    Lᶠ = μ̃ (cut ⟦ Z ⟧ (sub-tm (sub-lift θ) cosub-id (lett (projSnd (wkᵛ ⟦ W ⟧ᵛ)) ⟦ M ⟧ᶜ)) (wkᵏ ⟦ K ⟧ᴷ))
    Lˢ = μ̃ (cut ⟦ Z ⟧ (sub-tm (sub-lift φ) cosub-id ⟦ M ⟧ᶜ) (wkᵏ ⟦ K ⟧ᴷ))

  -- decoding commutes with machine steps
  --
  --   σ₁ ──⟦_⟧ˢᵗ── ⟦ σ₁ ⟧ˢᵗ
  --    │               ┊
  --    →ᶜ              ↦*
  --    ↓               ↓
  --   σ₂ ──⟦_⟧ˢᵗ── ⟦ σ₂ ⟧ˢᵗ
  sim : {σ₁ σ₂ : CState} → σ₁ →ᶜ σ₂ → ⟦ σ₁ ⟧ˢᵗ ↦* ⟦ σ₂ ⟧ˢᵗ
  sim (eval→ {W = W} {γ = γ} {K = K})            = subst (λ U → cut _ (ret U) ⟦ K ⟧ᴷ ↦* cut _ (ret ⟦ M.eval W γ ⟧ⱽ) ⟦ K ⟧ᴷ) (sym (eval-coh W γ)) ε
  sim (return→ {𝐖 = 𝐖} {M = M} {γ = γ} {K = K})  = frame-red ⟦ γ ⟧ᴱ cosub-id ⟦ 𝐖 ⟧ⱽ ⟦ M ⟧ᶜ ⟦ K ⟧ᴷ
  sim (push→ {M = M} {N = N} {γ = γ} {K = K})    = lett-red ⟦ γ ⟧ᴱ cosub-id ⟦ M ⟧ᶜ ⟦ N ⟧ᶜ ⟦ K ⟧ᴷ
  sim (sub→ {M = M} {N = N} {γ = γ} {K = K})     = catch-red ⟦ γ ⟧ᴱ cosub-id ⟦ M ⟧ᶜ (wkᵗ ⟦ N ⟧ᶜ) ⟦ K ⟧ᴷ
  sim (var→ {W = W} {γ = γ} {K = K})             = sim-var W γ K
  sim (pmᶜ→ {W = W} {γ = γ} {M = M} {K = K})     = sim-pm W M γ K
  sim (app→ {V = V} {W = W} {γ = γ} {K = K})     = sim-app V W γ K

  ------------------------------------------------------------------------
  -- bisimulation

  decoding : Decoding _→ᶜ_ (_↦_ {Γ = ε} {Δ = Δ₀})
  decoding .Decoding.decode        = ⟦_⟧ˢᵗ
  decoding .Decoding.decode-sim    = sim
  decoding .Decoding.decode-normal = halt-coh

  open Decoding decoding public
    using (Decoded; decode-run; decode-weak-bisim; decode-agree)
  open Simulation _→ᶜ_ (_↦_ {Γ = ε} {Δ = Δ₀}) using (_⇐; _↾SN; _≈*)

  weak-bisim : Decoded ↾SN ⇐ ≈*
  weak-bisim = decode-weak-bisim M.progress ↦-det

  -- the initial machine state and the translated program are bisimilar
  init-bisim : (M : I.ε I.⊢ᶜ ℛ) → (Decoded ↾SN ⇐) ⟨ M ╎ ⋄ ╎ ◻ ⟩ (cut ⟦ ℛ ⟧ ⟦ M ⟧ᶜ (covar here))
  init-bisim M = _ , (M.SN-theorem M , init-coh M) , ε

  -- a machine run decodes to a System L reduction
  --
  --   ⟨ M ╎ ⋄ ╎ ◻ ⟩ ──⟦_⟧ˢᵗ── ⟨ ⟦ M ⟧ᶜ ∣ α ⟩
  --       │                          ┊
  --       →ᶜ* (exec)                 ↦*
  --       ↓                          ↓
  --   ⟨ 𝐖 ╎ ◻ ⟩ ────⟦_⟧ˢᵗ──── ⟨ ⟦ 𝐖 ⟧ⱽ ∣ α ⟩
  exec-coh : (M : I.ε I.⊢ᶜ ℛ) → cut ⟦ ℛ ⟧ ⟦ M ⟧ᶜ (covar here) ↦* cut ⟦ ℛ ⟧ (ret ⟦ M.exec M .proj₂ .proj₁ ⟧ⱽ) (covar here)
  exec-coh M =
    subst₂ _↦*_ (init-coh M) (trans (final-coh σ n) (cong (λ 𝐕 → cut ⟦ ℛ ⟧ (ret ⟦ 𝐕 ⟧ⱽ) (covar here)) (sym eq)))
           (decode-run ss)
    where
    e  = M.exec M
    σ  = e .proj₁
    n  = e .proj₂ .proj₂ .proj₁
    ss = e .proj₂ .proj₂ .proj₂ .proj₁
    eq = e .proj₂ .proj₂ .proj₂ .proj₂

  -- the two evaluators agree on normal forms
  --
  --   ⟨ M ╎ ⋄ ╎ ◻ ⟩ ──⟦_⟧ˢᵗ── ⟨ ⟦ M ⟧ᶜ ∣ α ⟩
  --   │                       │
  --   exec                    evalᴸ
  --   ↓                       ↓
  --   σ ────────⟦_⟧ˢᵗ──────── C
  --
  -- σ and C normal
  eval-agree-coh : (M : I.ε I.⊢ᶜ ℛ) → ⟦ M.exec M .proj₁ ⟧ˢᵗ ≡ evalᴸ (cut ⟦ ℛ ⟧ ⟦ M ⟧ᶜ (covar here)) .proj₁
  eval-agree-coh M = decode-agree ↦-det ss n (subst (_↦* r .proj₁) (sym (init-coh M)) (r .proj₂ .proj₁)) (r .proj₂ .proj₂)
    where
    e  = M.exec M
    n  = e .proj₂ .proj₂ .proj₁
    ss = e .proj₂ .proj₂ .proj₂ .proj₁
    r  = evalᴸ (cut ⟦ ℛ ⟧ ⟦ M ⟧ᶜ (covar here))

  ------------------------------------------------------------------------
  -- semantics

  module _ (P R : Set) where

    private
      module LC = Inception.SystemL.CBV P R
      module IC = Inception.Sub.Semantics R

    -- the Sub CPS denotation of M returns the denotation of the machine result to k
    --
    --   M ────────exec───────── 𝐖
    --   │                       │
    --   IC.⟦_⟧ᶜ tt              LC.⟦ ⟦_⟧ⱽ ⟧ᵛ
    --   ↓                       ↓
    --   IC.⟦ M ⟧ᶜ tt k ───≡──── k a
    exec-sound : (M : I.ε I.⊢ᶜ ℛ) (k : R ^ IC.⟦ ℛ ⟧)
               → IC.⟦ M ⟧ᶜ tt k ≡ k (LC.⟦ ⟦ M.exec M .proj₂ .proj₁ ⟧ⱽ ⟧ᵛ (tt , [ (λ ()) , k ]′))
    exec-sound M k = begin
        IC.⟦ M ⟧ᶜ tt k
      ≡⟨ ⟦_⟧ᶜ-coh P R M tt κ k ⟨
        LC.⟦ cut ⟦ ℛ ⟧ ⟦ M ⟧ᶜ (covar here) ⟧ᶜ (tt , κ)
      ≡⟨ cong-app (LC.eqCmd (↦*→≈ (exec-coh M))) (tt , κ) ⟩
        LC.⟦ cut ⟦ ℛ ⟧ (ret ⟦ M.exec M .proj₂ .proj₁ ⟧ⱽ) (covar here) ⟧ᶜ (tt , κ)
      ∎
      where
      open ≡-Reasoning
      κ : R ^ (⊥ ⊎ LC.⟦ ⟦ ℛ ⟧ ⟧)
      κ = [ (λ ()) , k ]′
