open import Inception.SystemL.Syntax

module Inception.SystemL.Equations where

open import Inception.Prelude

--------------------------------------------------------------------------
-- weakening of equations

sub-wk-wk : (π : Ψ ⊇ Γ) (ρ : Ξ ⊇ Δ) (θ : Γ ⊢ Γ₁ ∣ Δ) → sub-wk π ρ θ ≡ sub-wk π wk-id (sub-wk wk-id ρ θ)
sub-wk-wk π ρ sub-ε        = refl
sub-wk-wk π ρ (sub-ex θ V) = cong (λ φ → sub-ex φ (wk-val π ρ V)) (sub-wk-wk π ρ θ)

cosub-wk-wk : (π : Ψ ⊇ Γ) (ρ : Ξ ⊇ Δ) (φ : Γ ∣ Δ₁ ⊢ Δ) → cosub-wk π ρ φ ≡ cosub-wk wk-id ρ (cosub-wk π wk-id φ)
cosub-wk-wk π ρ sub-ε        = refl
cosub-wk-wk π ρ (sub-ex φ K) = cong (λ ψ → sub-ex ψ (wk-cotm π ρ K)) (cosub-wk-wk π ρ φ)

wk-letc : (π : Ψ ⊇ Γ) (ρ : Ξ ⊇ Δ) (K : Γ ∣ X ⊢ᵏ Δ) (C : Γ ⊢ (Δ ∙ X)) → wk-cmd π ρ (letc K C) ≡ letc (wk-cotm π ρ K) (wk-cmd π (wk-cong ρ) C)
wk-letc π ρ K C = cong₂ (λ θ φ → sub-cmd θ φ C) (sub-wk-wk π ρ sub-id) (cong (λ ψ → sub-ex ψ (wk-cotm π ρ K)) (cosub-wk-wk π ρ cosub-id))

wk-letvc : (π : Ψ ⊇ Γ) (ρ : Ξ ⊇ Δ) (V : Γ ⊢ᵛ X ∣ Δ) (C : (Γ ∙ X) ⊢ Δ) → wk-cmd π ρ (letvc V C) ≡ letvc (wk-val π ρ V) (wk-cmd (wk-cong π) ρ C)
wk-letvc π ρ V C = cong₂ (λ θ φ → sub-cmd θ φ C) (cong (λ ψ → sub-ex ψ (wk-val π ρ V)) (sub-wk-wk π ρ sub-id)) (cosub-wk-wk π ρ cosub-id)

wk-letv : (π : Ψ ⊇ Γ) (ρ : Ξ ⊇ Δ) (V : Γ ⊢ᵛ X ∣ Δ) (M : (Γ ∙ X) ⊢ᵗ Y ∣ Δ) → wk-tm π ρ (letv V M) ≡ letv (wk-val π ρ V) (wk-tm (wk-cong π) ρ M)
wk-letv π ρ V M = cong₂ (λ θ φ → sub-tm θ φ M) (cong (λ ψ → sub-ex ψ (wk-val π ρ V)) (sub-wk-wk π ρ sub-id)) (cosub-wk-wk π ρ cosub-id)

mutual
  wk-val-≈ : (π : Ψ ⊇ Γ) (ρ : Ξ ⊇ Δ) → Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ∣ Δ → Ψ ⊢ᵛ wk-val π ρ V₁ ≈ wk-val π ρ V₂ ∶ X ∣ Ξ
  wk-val-≈ π ρ ≈-refl = ≈-refl
  wk-val-≈ π ρ (≈-sym e) = ≈-sym (wk-val-≈ π ρ e)
  wk-val-≈ π ρ (≈-trans e₁ e₂) = ≈-trans (wk-val-≈ π ρ e₁) (wk-val-≈ π ρ e₂)
  wk-val-≈ π ρ (lam-cong e) = lam-cong (wk-tm-≈ (wk-cong π) ρ e)
  wk-val-≈ π ρ (pair-cong e₁ e₂) = pair-cong (wk-val-≈ π ρ e₁) (wk-val-≈ π ρ e₂)
  wk-val-≈ π ρ (inl-cong e) = inl-cong (wk-val-≈ π ρ e)
  wk-val-≈ π ρ (inr-cong e) = inr-cong (wk-val-≈ π ρ e)
  wk-val-≈ π ρ (cont-cong e) = cont-cong (wk-cotm-≈ π ρ e)
  wk-val-≈ π ρ (unit-eta V) = unit-eta (wk-val π ρ V)
  wk-val-≈ π ρ (lam-eta V) = lam-eta (wk-val π ρ V)
  wk-val-≈ π ρ (cont-eta V) = cont-eta (wk-val π ρ V)

  wk-tm-≈ : (π : Ψ ⊇ Γ) (ρ : Ξ ⊇ Δ) → Γ ⊢ᵗ M₁ ≈ M₂ ∶ X ∣ Δ → Ψ ⊢ᵗ wk-tm π ρ M₁ ≈ wk-tm π ρ M₂ ∶ X ∣ Ξ
  wk-tm-≈ π ρ ≈-refl = ≈-refl
  wk-tm-≈ π ρ (≈-sym e) = ≈-sym (wk-tm-≈ π ρ e)
  wk-tm-≈ π ρ (≈-trans e₁ e₂) = ≈-trans (wk-tm-≈ π ρ e₁) (wk-tm-≈ π ρ e₂)
  wk-tm-≈ π ρ (ret-cong e) = ret-cong (wk-val-≈ π ρ e)
  wk-tm-≈ π ρ (μ-cong e) = μ-cong (wk-cmd-≈ π (wk-cong ρ) e)
  wk-tm-≈ π ρ (μ-eta M) = μ-eta (wk-tm π ρ M)
  wk-tm-≈ π ρ (pair-eta V) = pair-eta (wk-val π ρ V)

  wk-cotm-≈ : (π : Ψ ⊇ Γ) (ρ : Ξ ⊇ Δ) → Γ ∣ K₁ ≈ K₂ ∶ X ⊢ᵏ Δ → Ψ ∣ wk-cotm π ρ K₁ ≈ wk-cotm π ρ K₂ ∶ X ⊢ᵏ Ξ
  wk-cotm-≈ π ρ ≈-refl = ≈-refl
  wk-cotm-≈ π ρ (≈-sym e) = ≈-sym (wk-cotm-≈ π ρ e)
  wk-cotm-≈ π ρ (≈-trans e₁ e₂) = ≈-trans (wk-cotm-≈ π ρ e₁) (wk-cotm-≈ π ρ e₂)
  wk-cotm-≈ π ρ (app-cong e₁ e₂) = app-cong (wk-val-≈ π ρ e₁) (wk-cotm-≈ π ρ e₂)
  wk-cotm-≈ π ρ (fst-cong e) = fst-cong (wk-cotm-≈ π ρ e)
  wk-cotm-≈ π ρ (snd-cong e) = snd-cong (wk-cotm-≈ π ρ e)
  wk-cotm-≈ π ρ (case-cong e₁ e₂) = case-cong (wk-cotm-≈ π ρ e₁) (wk-cotm-≈ π ρ e₂)
  wk-cotm-≈ π ρ (μ̃-cong e) = μ̃-cong (wk-cmd-≈ (wk-cong π) ρ e)
  wk-cotm-≈ π ρ (pass-cong e) = pass-cong (wk-val-≈ π ρ e)
  wk-cotm-≈ π ρ (μ̃-eta K) = μ̃-eta (wk-cotm π ρ K)
  wk-cotm-≈ π ρ (case-eta K) = case-eta (wk-cotm π ρ K)

  wk-cmd-≈ : (π : Ψ ⊇ Γ) (ρ : Ξ ⊇ Δ) → Γ ⊢ C₁ ≈ C₂ ⊣ Δ → Ψ ⊢ wk-cmd π ρ C₁ ≈ wk-cmd π ρ C₂ ⊣ Ξ
  wk-cmd-≈ π ρ ≈-refl = ≈-refl
  wk-cmd-≈ π ρ (≈-sym e) = ≈-sym (wk-cmd-≈ π ρ e)
  wk-cmd-≈ π ρ (≈-trans e₁ e₂) = ≈-trans (wk-cmd-≈ π ρ e₁) (wk-cmd-≈ π ρ e₂)
  wk-cmd-≈ π ρ (cut-cong e₁ e₂) = cut-cong (wk-tm-≈ π ρ e₁) (wk-cotm-≈ π ρ e₂)
  wk-cmd-≈ π ρ (μ-beta C K) = subst (EqCmd _ _ _) (sym (wk-letc π ρ K C)) (μ-beta (wk-cmd π (wk-cong ρ) C) (wk-cotm π ρ K))
  wk-cmd-≈ π ρ (μ̃-beta V C) = subst (EqCmd _ _ _) (sym (wk-letvc π ρ V C)) (μ̃-beta (wk-val π ρ V) (wk-cmd (wk-cong π) ρ C))
  wk-cmd-≈ π ρ (app-beta M V K) = subst (EqCmd _ _ _) (sym (cong (λ N → cut _ N (wk-cotm π ρ K)) (wk-letv π ρ V M))) (app-beta (wk-tm (wk-cong π) ρ M) (wk-val π ρ V) (wk-cotm π ρ K))
  wk-cmd-≈ π ρ (fst-beta V W K) = fst-beta (wk-val π ρ V) (wk-val π ρ W) (wk-cotm π ρ K)
  wk-cmd-≈ π ρ (snd-beta V W K) = snd-beta (wk-val π ρ V) (wk-val π ρ W) (wk-cotm π ρ K)
  wk-cmd-≈ π ρ (inl-beta V K L) = inl-beta (wk-val π ρ V) (wk-cotm π ρ K) (wk-cotm π ρ L)
  wk-cmd-≈ π ρ (inr-beta W K L) = inr-beta (wk-val π ρ W) (wk-cotm π ρ K) (wk-cotm π ρ L)
  wk-cmd-≈ π ρ (pass-beta K V) = pass-beta (wk-cotm π ρ K) (wk-val π ρ V)

--------------------------------------------------------------------------
-- derived congruences

wk̃ᵛ-≈ : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X ∣ Δ → Γ ⊢ᵛ wk̃ᵛ {Y = Y} V₁ ≈ wk̃ᵛ V₂ ∶ X ∣ (Δ ∙ Y)
wk̃ᵛ-≈ = wk-val-≈ wk-id (wk-wk wk-id)

wk̃ᵗ-≈ : Γ ⊢ᵗ M₁ ≈ M₂ ∶ X ∣ Δ → Γ ⊢ᵗ wk̃ᵗ {Y = Y} M₁ ≈ wk̃ᵗ M₂ ∶ X ∣ (Δ ∙ Y)
wk̃ᵗ-≈ = wk-tm-≈ wk-id (wk-wk wk-id)

lett-cong : {N₁ N₂ : (Γ ∙ X) ⊢ᵗ Y ∣ Δ} → Γ ⊢ᵗ M₁ ≈ M₂ ∶ X ∣ Δ → (Γ ∙ X) ⊢ᵗ N₁ ≈ N₂ ∶ Y ∣ Δ → Γ ⊢ᵗ lett M₁ N₁ ≈ lett M₂ N₂ ∶ Y ∣ Δ
lett-cong p q = μ-cong (cut-cong (wk̃ᵗ-≈ p) (μ̃-cong (cut-cong (wk̃ᵗ-≈ q) ≈-refl)))

projFst-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X `× Y ∣ Δ → Γ ⊢ᵗ projFst V₁ ≈ projFst V₂ ∶ X ∣ Δ
projFst-cong p = μ-cong (cut-cong (ret-cong (wk̃ᵛ-≈ p)) ≈-refl)

projSnd-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X `× Y ∣ Δ → Γ ⊢ᵗ projSnd V₁ ≈ projSnd V₂ ∶ Y ∣ Δ
projSnd-cong p = μ-cong (cut-cong (ret-cong (wk̃ᵛ-≈ p)) ≈-refl)

letpv-cong : {M₁ M₂ : (Γ ∙ X ∙ Z) ⊢ᵗ Y ∣ Δ} → Γ ⊢ᵛ V₁ ≈ V₂ ∶ X `× Z ∣ Δ → (Γ ∙ X ∙ Z) ⊢ᵗ M₁ ≈ M₂ ∶ Y ∣ Δ
           → Γ ⊢ᵗ letpv V₁ M₁ ≈ letpv V₂ M₂ ∶ Y ∣ Δ
letpv-cong p q = lett-cong (projFst-cong p) (lett-cong (projSnd-cong (wk-val-≈ (wk-wk wk-id) wk-id p)) q)

applyL-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X `⇒ Y ∣ Δ → Γ ⊢ᵛ W₁ ≈ W₂ ∶ X ∣ Δ → Γ ⊢ᵗ applyL V₁ W₁ ≈ applyL V₂ W₂ ∶ Y ∣ Δ
applyL-cong p q = μ-cong (cut-cong (ret-cong (wk̃ᵛ-≈ p)) (app-cong (wk̃ᵛ-≈ q) ≈-refl))

throw-cong : Γ ⊢ᵛ V₁ ≈ V₂ ∶ ¬ X ∣ Δ → Γ ⊢ᵛ W₁ ≈ W₂ ∶ X ∣ Δ → Γ ⊢ᵗ throw {Y = Y} V₁ W₁ ≈ throw V₂ W₂ ∶ Y ∣ Δ
throw-cong p q = μ-cong (cut-cong (ret-cong (wk̃ᵛ-≈ p)) (pass-cong (wk̃ᵛ-≈ q)))

catch-cong : {M₁ M₂ : (Γ ∙ ¬ X) ⊢ᵗ Y ∣ Δ} {N₁ N₂ : (Γ ∙ X) ⊢ᵗ Y ∣ Δ}
           → (Γ ∙ ¬ X) ⊢ᵗ M₁ ≈ M₂ ∶ Y ∣ Δ → (Γ ∙ X) ⊢ᵗ N₁ ≈ N₂ ∶ Y ∣ Δ → Γ ⊢ᵗ catch M₁ N₁ ≈ catch M₂ N₂ ∶ Y ∣ Δ
catch-cong p q =
  μ-cong (cut-cong (ret-cong (cont-cong (μ̃-cong (cut-cong (wk̃ᵗ-≈ q) ≈-refl)))) (μ̃-cong (cut-cong (wk̃ᵗ-≈ p) ≈-refl)))

--------------------------------------------------------------------------
-- control operator encodings

≡→≈ᵗ : M₁ ≡ M₂ → Γ ⊢ᵗ M₁ ≈ M₂ ∶ X ∣ Δ
≡→≈ᵗ refl = ≈-refl

coapp-throw : (V : Γ ⊢ᵛ ¬ X ∣ Δ) (W : Γ ⊢ᵛ X ∣ Δ) → Γ ⊢ᵗ coapp {Y = Y} (ret (inl W)) V ≈ throw V W ∶ Y ∣ Δ
coapp-throw {X = X} {Y = Y} V W = μ-cong (begin
    cut (X `+ Y) (ret (inl (wk̃ᵛ W))) (case (μ̃ (cut (¬ X) (ret (wkᵛ (wk̃ᵛ V))) (pass (var here)))) (covar here))
  ≈⟨ inl-beta _ _ _ ⟩
    cut X (ret (wk̃ᵛ W)) (μ̃ (cut (¬ X) (ret (wkᵛ (wk̃ᵛ V))) (pass (var here))))
  ≈⟨ μ̃-beta _ _ ⟩
    cut (¬ X) (ret (wk̃ᵛ V)) (pass (wk̃ᵛ W))
  ∎)
  where open ≈ᶜ-Reasoning

casev-inl : (V : Γ ⊢ᵛ X ∣ Δ) (M : (Γ ∙ X) ⊢ᵗ Z ∣ Δ) (N : (Γ ∙ Y) ⊢ᵗ Z ∣ Δ) (K : Γ ∣ Z ⊢ᵏ Δ)
          → Γ ⊢ cut Z (casev (inl V) M N) K ≈ cut Z (letv V M) K ⊣ Δ
casev-inl {X = X} {Z = Z} {Y = Y} V M N K = begin
    cut Z (casev (inl V) M N) K
  ≈⟨ μ-beta _ _ ⟩
    cut (X `+ Y) (ret (inl V)) (case (μ̃ (cut Z (sub-tm (sub-lift sub-id) (cosub-wk (wk-wk wk-id) wk-id cosub-id) M) (wkᵏ K)))
                                     (μ̃ (cut Z (sub-tm (sub-lift sub-id) (cosub-wk (wk-wk wk-id) wk-id cosub-id) N) (wkᵏ K))))
  ≈⟨ inl-beta _ _ _ ⟩
    cut X (ret V) (μ̃ (cut Z (sub-tm (sub-lift sub-id) (cosub-wk (wk-wk wk-id) wk-id cosub-id) M) (wkᵏ K)))
  ≈⟨ μ̃-beta _ _ ⟩
    cut Z (letv V M) K
  ∎
  where open ≈ᶜ-Reasoning

casev-inr : (W : Γ ⊢ᵛ Y ∣ Δ) (M : (Γ ∙ X) ⊢ᵗ Z ∣ Δ) (N : (Γ ∙ Y) ⊢ᵗ Z ∣ Δ) (K : Γ ∣ Z ⊢ᵏ Δ)
          → Γ ⊢ cut Z (casev (inr W) M N) K ≈ cut Z (letv W N) K ⊣ Δ
casev-inr {Y = Y} {X = X} {Z = Z} W M N K = begin
    cut Z (casev (inr W) M N) K
  ≈⟨ μ-beta _ _ ⟩
    cut (X `+ Y) (ret (inr W)) (case (μ̃ (cut Z (sub-tm (sub-lift sub-id) (cosub-wk (wk-wk wk-id) wk-id cosub-id) M) (wkᵏ K)))
                                     (μ̃ (cut Z (sub-tm (sub-lift sub-id) (cosub-wk (wk-wk wk-id) wk-id cosub-id) N) (wkᵏ K))))
  ≈⟨ inr-beta _ _ _ ⟩
    cut Y (ret W) (μ̃ (cut Z (sub-tm (sub-lift sub-id) (cosub-wk (wk-wk wk-id) wk-id cosub-id) N) (wkᵏ K)))
  ≈⟨ μ̃-beta _ _ ⟩
    cut Z (letv W N) K
  ∎
  where open ≈ᶜ-Reasoning

-- μ̃s. ⟨ case s of { inl x ↦ N ; inr y ↦ y } ∣ α ⟩
handler : (Γ ∙ X) ⊢ᵗ Y ∣ Δ → Γ ∣ X `+ Y ⊢ᵏ (Δ ∙ Y)
handler {Y = Y} N = μ̃ (cut Y (wk̃ᵗ (casev (var here) (wk-tm (wk-cong (wk-wk wk-id)) wk-id N) (ret (var here)))) (covar here))

handler-inl : (N : (Γ ∙ X) ⊢ᵗ Y ∣ Δ)
            → (Γ ∙ X) ⊢ cut (X `+ Y) (ret (inl (var here))) (wkᵏ (handler N)) ≈ cut Y (wk̃ᵗ N) (covar here) ⊣ (Δ ∙ Y)
handler-inl {Γ = Γ} {X = X} {Y = Y} {Δ = Δ} N = begin
    cut (X `+ Y) (ret (inl (var here))) (wkᵏ (handler N))
  ≈⟨ μ̃-beta _ _ ⟩
    cut Y (casev (inl (var here)) N₁ (ret (var here))) (covar here)
  ≈⟨ casev-inl (var here) N₁ (ret (var here)) (covar here) ⟩
    cut Y (letv (var here) N₁) (covar here)
  ≈⟨ cut-cong (≡→≈ᵗ (sub-tm-ren-β wk-id {wk-id} {wk-id} (wk-wk wk-id) N)) ≈-refl ⟩
    cut Y (wk̃ᵗ N) (covar here)
  ∎
  where
  open ≈ᶜ-Reasoning
  N₁ : (Γ ∙ X ∙ X) ⊢ᵗ Y ∣ (Δ ∙ Y)
  N₁ = sub-tm (sub-lift (sub-ex sub-id (inl {Y = Y} (var here)))) (cosub-wk (wk-wk wk-id) wk-id cosub-id)
              (wk-tm (wk-cong (wk-cong (wk-wk wk-id))) (wk-wk wk-id) (wk-tm (wk-cong (wk-wk wk-id)) wk-id N))

handler-inr-cut : (N : (Γ ∙ X) ⊢ᵗ Y ∣ Δ)
                → (Γ ∙ ¬ X ∙ Y) ⊢ cut (X `+ Y) (ret (inr (var here))) (wkᵏ (wkᵏ (handler N))) ≈ cut Y (ret (var here)) (covar here) ⊣ (Δ ∙ Y)
handler-inr-cut {Γ = Γ} {X = X} {Y = Y} {Δ = Δ} N = begin
    cut (X `+ Y) (ret (inr (var here))) (wkᵏ (wkᵏ (handler N)))
  ≈⟨ μ̃-beta _ _ ⟩
    cut Y (casev (inr (var here)) N₂ (ret (var here))) (covar here)
  ≈⟨ casev-inr (var here) N₂ (ret (var here)) (covar here) ⟩
    cut Y (ret (var here)) (covar here)
  ∎
  where
  open ≈ᶜ-Reasoning
  N₂ : (Γ ∙ ¬ X ∙ Y ∙ X) ⊢ᵗ Y ∣ (Δ ∙ Y)
  N₂ = sub-tm (sub-lift (sub-ex sub-id (inr {X = X} (var here)))) (cosub-wk (wk-wk wk-id) wk-id cosub-id)
              (wk-tm (wk-cong (wk-cong (wk-wk (wk-wk wk-id)))) (wk-wk wk-id) (wk-tm (wk-cong (wk-wk wk-id)) wk-id N))

handler-inr : (N : (Γ ∙ X) ⊢ᵗ Y ∣ Δ)
            → (Γ ∙ ¬ X) ∣ μ̃ (cut (X `+ Y) (ret (inr (var here))) (wkᵏ (wkᵏ (handler N)))) ≈ covar here ∶ Y ⊢ᵏ (Δ ∙ Y)
handler-inr {X = X} {Y = Y} N = begin
    μ̃ (cut (X `+ Y) (ret (inr (var here))) (wkᵏ (wkᵏ (handler N))))
  ≈⟨ μ̃-cong (handler-inr-cut N) ⟩
    μ̃ (cut Y (ret (var here)) (wkᵏ (covar here)))
  ≈⟨ μ̃-eta (covar here) ⟨
    covar here
  ∎
  where open ≈ᵏ-Reasoning

colam-catch : (M : (Γ ∙ ¬ X) ⊢ᵗ Y ∣ Δ) (N : (Γ ∙ X) ⊢ᵗ Y ∣ Δ) → Γ ⊢ᵗ ccase (colam M) N (ret (var here)) ≈ catch M N ∶ Y ∣ Δ
colam-catch {Γ = Γ} {X = X} {Y = Y} {Δ = Δ} M N = μ-cong (begin
    cut (X `+ Y) (wk̃ᵗ (colam M)) (handler N)
  ≈⟨ μ-beta _ _ ⟩
    cut (¬ X) (ret (cont (μ̃ (cut (X `+ Y) (ret (inl (var here))) (wkᵏ (handler N))))))
              (μ̃ (cut Y M̃ (μ̃ (cut (X `+ Y) (ret (inr (var here))) (wkᵏ (wkᵏ (handler N)))))))
  ≈⟨ cut-cong (ret-cong (cont-cong (μ̃-cong (handler-inl N))))
              (μ̃-cong (cut-cong (≡→≈ᵗ (sub-tm-ren-β wk-id {wk-id} {wk-wk wk-id} (wk-wk wk-id) M)) (handler-inr N))) ⟩
    cut (¬ X) (ret (cont (μ̃ (cut Y (wk̃ᵗ N) (covar here))))) (μ̃ (cut Y (wk̃ᵗ M) (covar here)))
  ∎)
  where
  open ≈ᶜ-Reasoning
  M̃ : (Γ ∙ ¬ X) ⊢ᵗ Y ∣ (Δ ∙ Y)
  M̃ = sub-tm (sub-lift sub-id) (cosub-wk (wk-wk wk-id) (wk-wk wk-id) cosub-id) M
