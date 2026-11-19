module Inception.LamLamBar.Equations where

open import Inception.LamLamBar.Syntax
open ≈ᶜ-Reasoning

--------------------------------------------------------------------------
-- syntactic sugar

inlc : Γ ⊢ᶜ X
     ---------------
     → Γ ⊢ᶜ X `+ Y
inlc M = push M (return (inl (var here)))

inrc : Γ ⊢ᶜ Y
     ---------------
     → Γ ⊢ᶜ X `+ Y
inrc M = push M (return (inr (var here)))

--------------------------------------------------------------------------
-- coapp on injections

coapp-inrc : (M : Γ ⊢ᶜ Y) → (V : Γ ⊢ᵛ X ̃)
           ------------------------------------
           → Γ ⊢ᶜ coapp (inrc M) V ≈ M ∶ Y
coapp-inrc M V = begin
    coapp (inrc M) V
  ≈⟨ coapp-eta (inrc M) V ⟩
    ccase (inrc M) (throw (wk V) (var here)) (return (var here))
  ≈⟨ push-eta M _ _ ⟩
    push M (push (return (inr (var here))) (wk-comp (wk-cong (wk-wk wk-id)) (case (var here) (wk-comp (wk-cong (wk-wk wk-id)) (throw (wk V) (var here))) (wk-comp (wk-cong (wk-wk wk-id)) (return (var here))))))
  ≈⟨ push-cong ≈-refl (return-beta _ _) ⟩
    push M (sub-comp (sub-ex sub-id (inr (var here))) (wk-comp (wk-cong (wk-wk wk-id)) (case (var here) (wk-comp (wk-cong (wk-wk wk-id)) (throw (wk V) (var here))) (wk-comp (wk-cong (wk-wk wk-id)) (return (var here))))))
  ≈⟨ push-cong ≈-refl (case-inr-beta _ _ _) ⟩
    push M (return (var here))
  ≈⟨ return-eta M ⟨
    M
  ∎

coapp-inlc : (M : Γ ⊢ᶜ X) → (V : Γ ⊢ᵛ X ̃)
           ------------------------------------------------------------
           → Γ ⊢ᶜ coapp (inlc M) V ≈ push M (throw (wk V) (var here)) ∶ Y
coapp-inlc M V = begin
    coapp (inlc M) V
  ≈⟨ coapp-eta (inlc M) V ⟩
    ccase (inlc M) (throw (wk V) (var here)) (return (var here))
  ≈⟨ push-eta M _ _ ⟩
    push M (push (return (inl (var here))) (wk-comp (wk-cong (wk-wk wk-id)) (case (var here) (wk-comp (wk-cong (wk-wk wk-id)) (throw (wk V) (var here))) (wk-comp (wk-cong (wk-wk wk-id)) (return (var here))))))
  ≈⟨ push-cong ≈-refl (return-beta _ _) ⟩
    push M (sub-comp (sub-ex sub-id (inl (var here))) (wk-comp (wk-cong (wk-wk wk-id)) (case (var here) (wk-comp (wk-cong (wk-wk wk-id)) (throw (wk V) (var here))) (wk-comp (wk-cong (wk-wk wk-id)) (return (var here))))))
  ≈⟨ push-cong ≈-refl (case-inl-beta _ _ _) ⟩
    push M (throw (wk V) (var here))
  ∎

--------------------------------------------------------------------------
-- control equations

colam-const : (M : Γ ⊢ᶜ Y)
            ----------------------------------------------------------
            → Γ ⊢ᶜ colam (wk-comp (wk-wk wk-id) M) ≈ inrc M ∶ X `+ Y
colam-const M = begin
    colam (wk-comp (wk-wk wk-id) M)
  ≈⟨ colam-cong (coapp-inrc (wk-comp (wk-wk wk-id) M) (var here)) ⟨
    colam (coapp (inrc (wk-comp (wk-wk wk-id) M)) (var here))
  ≈⟨ colam-eta (inrc M) ⟨
    inrc M
  ∎

colam-inr-pass : (M : Γ ⊢ᶜ Y) (N : (Γ ∙ Y) ⊢ᶜ Z)
               ------------------------------------------------
               → Γ ⊢ᶜ colam (push (coapp (inrc (wk-comp (wk-wk wk-id) M)) (var here)) (wk-comp (wk-cong (wk-wk wk-id)) N)) ≈ push M (inrc N) ∶ X `+ Z
colam-inr-pass M N = begin
    colam (push (coapp (inrc (wk-comp (wk-wk wk-id) M)) (var here)) (wk-comp (wk-cong (wk-wk wk-id)) N))
  ≈⟨ colam-cong (push-cong (coapp-inrc (wk-comp (wk-wk wk-id) M) (var here)) ≈-refl) ⟩
    colam (push (wk-comp (wk-wk wk-id) M) (wk-comp (wk-cong (wk-wk wk-id)) N))
  ≈⟨ colam-const (push M N) ⟩
    inrc (push M N)
  ≈⟨ push-eta M N _ ⟩
    push M (inrc N)
  ∎

colam-inl-jump : (M : Γ ⊢ᶜ X) (N : (Γ ∙ Y) ⊢ᶜ Z)
               ------------------------------------------------
               → Γ ⊢ᶜ colam (push (coapp (inlc (wk-comp (wk-wk wk-id) M)) (var here)) (wk-comp (wk-cong (wk-wk wk-id)) N)) ≈ inlc M ∶ X `+ Z
colam-inl-jump M N = begin
    colam (push (coapp (inlc (wk-comp (wk-wk wk-id) M)) (var here)) (wk-comp (wk-cong (wk-wk wk-id)) N))
  ≈⟨ colam-cong (push-cong (coapp-inlc (wk-comp (wk-wk wk-id) M) (var here)) ≈-refl) ⟩
    colam (push (push (wk-comp (wk-wk wk-id) M) (throw (wk (var here)) (var here))) (wk-comp (wk-cong (wk-wk wk-id)) N))
  ≈⟨ colam-cong (push-eta _ _ _) ⟩
    colam (push (wk-comp (wk-wk wk-id) M) (push (throw (wk (var here)) (var here)) (wk-comp (wk-cong (wk-wk wk-id)) (wk-comp (wk-cong (wk-wk wk-id)) N))))
  ≈⟨ colam-cong (push-cong ≈-refl (coapp-inl-push _ _ _)) ⟩
    colam (push (wk-comp (wk-wk wk-id) M) (throw (wk (var here)) (var here)))
  ≈⟨ colam-cong (coapp-inlc (wk-comp (wk-wk wk-id) M) (var here)) ⟨
    colam (coapp (inlc (wk-comp (wk-wk wk-id) M)) (var here))
  ≈⟨ colam-eta (inlc M) ⟨
    inlc M
  ∎

case-colam-beta : (V : (Γ ∙ X ̃) ⊢ᵛ Y) → (M : (Γ ∙ X) ⊢ᶜ Z) → (N : (Γ ∙ Y) ⊢ᶜ Z)
                --------------------------------------------------------------------
                → Γ ⊢ᶜ ccase (colam (return V)) M N ≈ ccase (colam (sub-comp (sub-ex (sub-wk (wk-wk wk-id) sub-id) V) N)) M (return (var here)) ∶ Z
case-colam-beta V M N = begin
    ccase (colam (return V)) M N
  ≈⟨ case-colam-push (return V) M N ⟩
    ccase (colam (push (return V) (wk-comp (wk-cong (wk-wk wk-id)) N))) M (return (var here))
  ≈⟨ push-cong (colam-cong (return-beta V _)) ≈-refl ⟩
    ccase (colam (sub-comp (sub-ex (sub-wk (wk-wk wk-id) sub-id) V) N)) M (return (var here))
  ∎
