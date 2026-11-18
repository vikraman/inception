\begin{code}
{-# OPTIONS --no-postfix-projections #-}

open import Inception.IncV.Data

module Inception.IncV.Semantics (𝒜 : Alg) (R : Set) where

open import Inception.Prelude
open import Inception.IncV.Syntax 𝒜
open import Inception.Rewriting


open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ-syntax; uncurry)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Function.Base using (const; _∘_; id)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; subst)
open Eq.≡-Reasoning using (step-≡-⟩; step-≡-∣; step-≡-⟨; _∎; step-≡)

--------------------------------------------------------------------------

\end{code}
%<*Helpers>
\begin{code}
open import Inception.Cont.Base
open import Inception.Monad.Base using (Monad)
open import Level using (0ℓ)

K : Set → Set
K = K[ R ]

open Monad (K[_]-Monad {x = 0ℓ} R) using (η; _*)
\end{code}
%</Helpers>
\begin{code}

\end{code}
%<*SemTy>
\begin{code}

⟦_⟧ : Ty → Set
⟦ `𝟙 ⟧ = ⊤
⟦ X `× Y ⟧ = ⟦ X ⟧ × ⟦ Y ⟧
⟦ X `⇒ Y ⟧ = ⟦ X ⟧ → K ⟦ Y ⟧
⟦ `ℓ ⟧ = 𝒟 → R
⟦ `𝓅 ⟧ = 𝒟

\end{code}
%</SemTy>

%<*SemCtx>
\begin{code}

open Sem ⟦_⟧

\end{code}
%</SemCtx>

\begin{code}

\end{code}
%<*SemTerms>
\begin{code}

recK : {X : Set} → R ^ 𝒟 × 𝒟 → K X
recK (k , p) _ = k p

incK : {X : Set} → (R ^ 𝒟 → K X) × (𝒟 → K X) → K X
incK (f , g) k = f (λ p → g p k) k

mutual

  ⟦_⟧ᵛ : Γ ⊢ᵛ X → ⟦ Γ ⟧ˣ → ⟦ X ⟧
  ⟦ var i ⟧ᵛ = ⟦ i ⟧ᵐ
  ⟦ lam M ⟧ᵛ = curry ⟦ M ⟧ᶜ
  ⟦ pair V W ⟧ᵛ = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ >
  ⟦ unit ⟧ᵛ = const tt
  ⟦ dat D ⟧ᵛ = const D
  ⟦ op o a ⟧ᵛ = const (apply o a)

  ⟦_⟧ᶜ : Γ ⊢ᶜ X → ⟦ Γ ⟧ˣ → K ⟦ X ⟧
  ⟦ return W ⟧ᶜ = ⟦ W ⟧ᵛ ； η
  ⟦ pm W M ⟧ᶜ = < idf , ⟦ W ⟧ᵛ > ； assocl ； ⟦ M ⟧ᶜ
  ⟦ push M N ⟧ᶜ = < idf , ⟦ M ⟧ᶜ > ； τ ； ⟦ N ⟧ᶜ *
  ⟦ app V W ⟧ᶜ = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ > ； ev
  ⟦ rec V W ⟧ᶜ = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ > ； recK
  ⟦ inc M N ⟧ᶜ = < curry ⟦ M ⟧ᶜ , curry ⟦ N ⟧ᶜ > ； incK
\end{code}
%</SemTerms>
\begin{code}

push-return-sem-eq : (γ : ⟦ Γ ⟧ˣ) → (k : (⟦ X ⟧ → R)) → (W : Γ ⊢ᵛ Z) → (M : (Γ ∙ Z) ⊢ᶜ X) →
      (< idf , ⟦ return W ⟧ᶜ > ； τ ； ⟦ M ⟧ᶜ *) γ k ≡ ⟦ M ⟧ᶜ (γ , ⟦ W ⟧ᵛ γ) k
push-return-sem-eq γ k W M = refl

push-sem-eq : (γ : ⟦ Γ ⟧ˣ) → (k : (⟦ X ⟧ → R)) → (M : Γ ⊢ᶜ Z) → (N : (Γ ∙ Z) ⊢ᶜ X) →
      (< idf , ⟦ M ⟧ᶜ > ； τ ； ⟦ N ⟧ᶜ *) γ k ≡ ⟦ M ⟧ᶜ γ (λ t → ((⟦ N ⟧ᶜ *) ∘ τ)  (γ , η t) k)
push-sem-eq γ k M N = refl

pm-sem-eq : (γ : ⟦ Γ ⟧ˣ) → (k : (⟦ X ⟧ → R)) → (W : Γ ⊢ᵛ (Y `× Z)) → (M : (Γ ∙ Y ∙ Z) ⊢ᶜ X) →
      (< idf , ⟦ W ⟧ᵛ > ； assocl ； ⟦ M ⟧ᶜ) γ k ≡ ⟦ M ⟧ᶜ ((γ , proj₁ (⟦ W ⟧ᵛ γ)) , proj₂ (⟦ W ⟧ᵛ γ)) k
pm-sem-eq γ k W M = refl

app-sem-eq : (γ : ⟦ Γ ⟧ˣ) → (k : (⟦ Y ⟧ → R)) → (V : Γ ⊢ᵛ (X `⇒ Y)) → (W : Γ ⊢ᵛ X) →
      (< ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ > ； ev) γ k ≡ (⟦ V ⟧ᵛ γ) (⟦ W ⟧ᵛ γ) k
app-sem-eq γ k V W = refl

app-lam-sem-eq : (γ : ⟦ Γ ⟧ˣ) → (k : (⟦ Y ⟧ → R)) → (M : (Γ ∙ X) ⊢ᶜ Y) → (V : Γ ⊢ᵛ X) →
      (< ⟦ lam M ⟧ᵛ , ⟦ V ⟧ᵛ > ； ev) γ k ≡ ⟦ M ⟧ᶜ (γ , (⟦ V ⟧ᵛ γ)) k
app-lam-sem-eq γ k M V = refl

mutual
  evalVal : Γ ⊢ᵛ X → ⟦ Γ ⟧ˣ → ⟦ X ⟧
  evalVal (var i) γ =
    ⟦ i ⟧ᵐ γ
  evalVal (lam M) γ a =
    curry (evalComp M) (γ , a)
  evalVal (pair V W) γ =
    evalVal V γ , evalVal W γ
  evalVal unit γ = tt

  evalVal (dat V) γ = V
  evalVal (op o a) γ = apply o a

  evalComp :  Γ ⊢ᶜ X → ⟦ Γ ⟧ˣ × (⟦ X ⟧ → R) → R
  evalComp (return W) (γ , k) =
    let w = evalVal W γ in
      k w
  evalComp (pm W M) (γ , k) =
    let w = evalVal W γ in
      evalComp M (((γ , proj₁ w) , proj₂ w) , k)
  evalComp (push M N) (γ , k) =
    evalComp M (γ , λ a →
      evalComp N ((γ , a) , k))
  evalComp (app V W) (γ , k) =
    let w₁ = evalVal V γ in
      let w₂ = evalVal W γ in
        (w₁ w₂) k
  evalComp (rec V W) (γ , k) =
    let v = evalVal V γ in
      let w = evalVal W γ in
        v w
  evalComp (inc M N) (γ , k) =
    evalComp M ((γ , λ p →
      evalComp N ((γ , p) , k)) , k)

-- coherences
mutual
  wk-val-coh : (π : Γ ⊇ Δ) (W : Δ ⊢ᵛ X) → ⟦ wk-val π W ⟧ᵛ ≡ (⟦ π ⟧ʷ ； ⟦ W ⟧ᵛ)
  wk-val-coh π (var i) rewrite wk-mem-coh π i = refl
  wk-val-coh π (lam M) rewrite wk-comp-coh (wk-cong π) M = refl
  wk-val-coh π (pair V W) rewrite wk-val-coh π V | wk-val-coh π W = refl
  wk-val-coh π unit = refl
  wk-val-coh π (dat D) = refl
  wk-val-coh π (op o a) = refl

  wk-comp-coh : (π : Γ ⊇ Δ) (M : Δ ⊢ᶜ X) → ⟦ wk-comp π M ⟧ᶜ ≡ (⟦ π ⟧ʷ ； ⟦ M ⟧ᶜ)
  wk-comp-coh π (return W) rewrite wk-val-coh π W = refl
  wk-comp-coh π (pm W M) rewrite wk-val-coh π W | wk-comp-coh (wk-cong (wk-cong π)) M = refl
  wk-comp-coh π (push M N) rewrite wk-comp-coh π M | wk-comp-coh (wk-cong π) N = refl
  wk-comp-coh π (app V W) rewrite wk-val-coh π V | wk-val-coh π W = refl
  wk-comp-coh π (rec V W) rewrite wk-val-coh π V | wk-val-coh π W = refl
  wk-comp-coh π (inc M N) rewrite wk-comp-coh (wk-cong π) M | wk-comp-coh (wk-cong π) N = refl

{-# REWRITE wk-val-coh #-}
{-# REWRITE wk-comp-coh #-}

wk-sem-trans : (π : Ψ ⊇ Δ) → (δ : Δ ⊇ Γ) → (γ : ⟦ Ψ ⟧ˣ) → ⟦ δ ⟧ʷ (⟦ π ⟧ʷ γ) ≡ ⟦ wk-trans π δ ⟧ʷ γ
wk-sem-trans wk-ε π γ = refl
wk-sem-trans {Γ = ε} (wk-cong π) δ γ = refl
wk-sem-trans {Γ = Γ ∙ X} (wk-cong {X = X} π) (wk-cong {X = X} δ) γ =
       ⟦ wk-cong {X = X} δ ⟧ʷ (⟦ wk-cong {X = X} π ⟧ʷ γ)
      ≡⟨ refl ⟩
       ⟦ δ ⟧ʷ (⟦ π ⟧ʷ (proj₁ γ )) , proj₂ γ
      ≡⟨ cong (λ y → y , proj₂ γ) (wk-sem-trans π δ (proj₁ γ)) ⟩
       ⟦ wk-trans π δ ⟧ʷ (proj₁ γ) , proj₂ γ
      ≡⟨ refl ⟩
       ⟦ wk-cong {X = X} (wk-trans π δ) ⟧ʷ γ ∎
wk-sem-trans {Γ = Γ ∙ Y} (wk-cong {X = X} π) (wk-wk {X = X} δ) γ =
       ⟦ wk-wk {X = X} δ ⟧ʷ (⟦ wk-cong {X = X} π ⟧ʷ γ)
      ≡⟨ refl ⟩
       ⟦ δ ⟧ʷ (⟦ π ⟧ʷ (proj₁ γ))
      ≡⟨ wk-sem-trans π δ (proj₁ γ) ⟩
       ⟦ wk-trans π δ ⟧ʷ (proj₁ γ)
      ≡⟨ refl ⟩
       ⟦ wk-trans (wk-cong {X = X} π) (wk-wk {X = X} δ) ⟧ʷ γ ∎
wk-sem-trans (wk-wk π) wk-ε γ = refl
wk-sem-trans (wk-wk {X = X} π) (wk-cong {X = Y} δ) γ =
       ⟦ wk-cong {X = Y} δ ⟧ʷ (⟦ wk-wk {X = X} π ⟧ʷ γ)
      ≡⟨ refl ⟩
       ⟦ δ ⟧ʷ (proj₁ (⟦ π ⟧ʷ (proj₁ γ))) , proj₂ (⟦ π ⟧ʷ (proj₁ γ))
      ≡⟨ wk-sem-trans π (wk-cong δ) (proj₁ γ) ⟩
       ⟦ wk-trans π (wk-cong δ) ⟧ʷ (proj₁ γ)
      ≡⟨ refl ⟩
       ⟦ wk-wk {X = X} (wk-trans π (wk-cong δ)) ⟧ʷ γ ∎
wk-sem-trans (wk-wk π) (wk-wk δ) γ = wk-sem-trans π (wk-wk δ) (proj₁ γ)

module TopLevel {ℛ : Ty} {k₀ : ⟦ ℛ ⟧ → R} where

  open import Inception.IncV.Machine 𝒜 ℛ

\end{code}
%<*SemMEnv>
\begin{code}
  mutual
    ⟦_⟧ᴱ : MEnv Γ → ⟦ Γ ⟧ˣ
    ⟦ ⋄ ⟧ᴱ = tt
    ⟦ γ · 𝐖 ⟧ᴱ = ⟦ γ ⟧ᴱ , ⟦ 𝐖 ⟧ⱽ

    ⟦_⟧ⱽ : (𝐖 : MVal X) → ⟦ X ⟧
    ⟦ unitᵛ ⟧ⱽ = tt
    ⟦ pairᵛ 𝐕 𝐖 ⟧ⱽ = ⟦ 𝐕 ⟧ⱽ , ⟦ 𝐖 ⟧ⱽ
    ⟦ cloᵛ M γ ⟧ⱽ = (curry ⟦ M ⟧ᶜ) ⟦ γ ⟧ᴱ
    ⟦ datᵛ D ⟧ⱽ = D
    ⟦ jumpᵛ M γ K ⟧ⱽ = λ x → ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , x) ⟦ K ⟧ᴷ

    ⟦_⟧ᶜˢ : CStack X → K ⟦ X ⟧ → K ⟦ ℛ ⟧
    ⟦ ◻ ⟧ᶜˢ = idf
    ⟦ < M ； γ >∷ K ⟧ᶜˢ = < const ⟦ γ ⟧ᴱ , idf > ； τ ； (⟦ M ⟧ᶜ *) ； ⟦ K ⟧ᶜˢ

    ⟦_⟧ᴷ : CStack X → ⟦ X ⟧ → R
    ⟦_⟧ᴷ K t = ⟦ K ⟧ᶜˢ (η t) k₀
\end{code}
%</SemMEnv>

%<*SemCState>
\begin{code}
  ⟦_⟧ᶜꟴ : CState → R
  ⟦ ⟨ 𝐖 ╎ K ⟩ ⟧ᶜꟴ = (η ⟦ 𝐖 ⟧ⱽ) ⟦ K ⟧ᴷ
  ⟦ ⟨ M ╎ γ ╎ K ⟩ ⟧ᶜꟴ = ⟦ M ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ K ⟧ᴷ
\end{code}
%</SemCState>

\begin{code}

  lookup-eq : (i : Γ ∋ X) → (γ : MEnv Γ) → ⟦ i ⟧ᵐ ⟦ γ ⟧ᴱ ≡ ⟦ lookup i γ ⟧ⱽ
  lookup-eq here (γ · 𝐖) = refl
  lookup-eq (there i) (γ · 𝐖) = lookup-eq i γ

  eval-correct : (W : Γ ⊢ᵛ X) → (γ : MEnv Γ) → ⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ ≡ ⟦ eval W γ ⟧ⱽ
  eval-correct (var i) γ = lookup-eq i γ
  eval-correct (lam M) γ = refl
  eval-correct (pair V W) γ = cong₂ _,_ (eval-correct V γ) (eval-correct W γ)
  eval-correct unit γ = refl
  eval-correct (dat D) γ = refl
  eval-correct (op o a) γ = refl

  push-eq : (K : CStack X) → (KX : K[ R ] ⟦ X ⟧) → ⟦ K ⟧ᶜˢ (λ k → KX k) k₀ ≡ KX (λ y → ⟦ K ⟧ᶜˢ (λ k → k y) k₀)
  push-eq ◻ KX = refl
  push-eq {X = X} ((< M ； γ >∷ K)) KX =           ⟦ < M ； γ >∷ K ⟧ᶜˢ KX k₀
                                    ≡⟨ refl ⟩
                                      ⟦ K ⟧ᶜˢ (λ k → (λ x → KX (λ z → ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , z) x)) k) k₀
                                    ≡⟨ push-eq K (λ x → KX (λ z → ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , z) x)) ⟩
                                      (λ x → KX (λ z → ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , z) x)) (λ y → ⟦ K ⟧ᶜˢ (λ k → k y) k₀)
                                    ≡⟨ refl ⟩
                                      KX (λ z →       ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ K ⟧ᶜˢ (λ k → k y) k₀)            )
                                    ≡⟨ cong KX push-eq-fun ⟩
                                      KX (λ z →       ⟦ K ⟧ᶜˢ (λ k → ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , z) k) k₀                      )
                                    ≡⟨ refl ⟩
                                      KX (λ y → ⟦ < M ； γ >∷ K ⟧ᶜˢ (λ k → k y) k₀) ∎

                                    where
                                      push-eq-at : (z : ⟦ X ⟧) → ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ K ⟧ᶜˢ (λ k → k y) k₀) ≡ ⟦ K ⟧ᶜˢ (λ k → ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , z) k) k₀
                                      push-eq-at z = sym (push-eq K (⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , z)))

                                      push-eq-fun : (λ z → ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ K ⟧ᶜˢ (λ k → k y) k₀)) ≡ (λ z → ⟦ K ⟧ᶜˢ (λ k → ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , z) k) k₀)
                                      push-eq-fun = funext push-eq-at

  jump-eq : (𝐖 : MVal `ℓ) → (𝐕 : MVal `𝓅) → ⟦ 𝐖 ⟧ⱽ ⟦ 𝐕 ⟧ⱽ ≡ ⟦ jump-to-state 𝐖 𝐕 ⟧ᶜꟴ
  jump-eq (jumpᵛ _ _ _) 𝐕 = refl

  eval-jump-eq : (W : Γ ⊢ᵛ `ℓ) → (V : Γ ⊢ᵛ `𝓅) → (γ : MEnv Γ) → ⟦ eval W γ ⟧ⱽ ⟦ eval V γ ⟧ⱽ ≡ ⟦ jump-to-state (eval W γ) (eval V γ) ⟧ᶜꟴ
  eval-jump-eq W V γ = jump-eq (eval W γ) (eval V γ)

  clo-eq : (𝐖 : MVal (X `⇒ Y)) → (w : ⟦ X ⟧) → (γ : ⟦ proj₁ (clo-to-comp 𝐖) ⟧ˣ) → (eq : γ ≡ ⟦ proj₂ (proj₂ (clo-to-comp 𝐖)) ⟧ᴱ) → ⟦ 𝐖 ⟧ⱽ w ≡ ⟦ proj₁ (proj₂ (clo-to-comp 𝐖)) ⟧ᶜ (γ , w)
  clo-eq (cloᵛ M _) w γ eq = cong (λ x → curry ⟦ M ⟧ᶜ x w) (sym eq)

  proj₁-val-eq : (𝐖 : MVal (X `× Y)) → proj₁ ⟦ 𝐖 ⟧ⱽ ≡ ⟦ proj₁-val 𝐖 ⟧ⱽ
  proj₁-val-eq (pairᵛ 𝐕 𝐖) = refl

  proj₂-val-eq : (𝐖 : MVal (X `× Y)) → proj₂ ⟦ 𝐖 ⟧ⱽ ≡ ⟦ proj₂-val 𝐖 ⟧ⱽ
  proj₂-val-eq (pairᵛ 𝐕 𝐖) = refl

  eval-proj₁-eq : (W : Γ ⊢ᵛ (X `× Y)) → (γ : MEnv Γ) → (proj₁ (⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ)) ≡ ⟦ proj₁-val (eval W γ) ⟧ⱽ
  eval-proj₁-eq W γ = trans (cong proj₁ (eval-correct W γ)) (proj₁-val-eq (eval W γ))

  eval-proj₂-eq : (W : Γ ⊢ᵛ (X `× Y)) → (γ : MEnv Γ) → (proj₂ (⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ)) ≡ ⟦ proj₂-val (eval W γ) ⟧ⱽ
  eval-proj₂-eq W γ = trans (cong proj₂ (eval-correct W γ)) (proj₂-val-eq (eval W γ))

  compstate-eq : {σ σ₁ : CState} → σ →ᶜ σ₁ → ⟦ σ ⟧ᶜꟴ ≡ ⟦ σ₁ ⟧ᶜꟴ
  compstate-eq (eval→ {W = W} {γ = γ} {K = K}) =
    η (⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ) ⟦ K ⟧ᴷ ≡⟨ cong (λ x → η x ⟦ K ⟧ᴷ) eq ⟩ η ⟦ eval W γ ⟧ⱽ ⟦ K ⟧ᴷ ∎
    where
      eq = eval-correct W γ
  compstate-eq (return→ {𝐖 = 𝐖} {M = M} {γ = γ} {K = K}) =
      η ⟦ 𝐖 ⟧ⱽ ⟦ < M ； γ >∷ K ⟧ᴷ
    ≡⟨ refl ⟩
     ⟦ K ⟧ᶜˢ (λ k₁ → ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , ⟦ 𝐖 ⟧ⱽ) k₁) k₀
    ≡⟨ eq ⟩
     ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , ⟦ 𝐖 ⟧ⱽ) (λ y → ⟦ K ⟧ᶜˢ (λ k₁ → k₁ y) k₀)
    ≡⟨ refl ⟩
     ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , ⟦ 𝐖 ⟧ⱽ) ⟦ K ⟧ᴷ ∎
    where
      eq = push-eq K (⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , ⟦ 𝐖 ⟧ⱽ))
  compstate-eq (push→ {M = M} {N = N} {γ = γ} {K = K}) =
    (< idf , ⟦ M ⟧ᶜ > ； τ ； ⟦ N ⟧ᶜ *) ⟦ γ ⟧ᴱ ⟦ K ⟧ᴷ
     ≡⟨ refl ⟩
     ⟦ M ⟧ᶜ ⟦ γ ⟧ᴱ (λ z → ⟦ N ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ K ⟧ᶜˢ (λ k₁ → k₁ y) k₀))
     ≡⟨ cong (⟦ M ⟧ᶜ ⟦ γ ⟧ᴱ) (funext (λ x → sym (push-eq K (⟦ N ⟧ᶜ (⟦ γ ⟧ᴱ , x))))) ⟩
     ⟦ M ⟧ᶜ ⟦ γ ⟧ᴱ (λ y → ⟦ K ⟧ᶜˢ (λ k₁ → ⟦ N ⟧ᶜ (⟦ γ ⟧ᴱ , y) k₁) k₀)
     ≡⟨ refl ⟩
     ⟦ M ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ < N ； γ >∷ K ⟧ᴷ ∎
  compstate-eq (inc→) = refl
  compstate-eq (rec→ {V = V} {W = W} {γ = γ} {K = K}) =
    (< ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ > ； recK) ⟦ γ ⟧ᴱ ⟦ K ⟧ᴷ ≡⟨ refl ⟩ ⟦ V ⟧ᵛ ⟦ γ ⟧ᴱ (⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ) ≡⟨ cong₂ (λ x y → x y) eq₁ eq₂ ⟩ ⟦ eval V γ ⟧ⱽ ⟦ eval W γ ⟧ⱽ ≡⟨ eval-jump-eq V W γ ⟩ ⟦ eval-jump V W γ ⟧ᶜꟴ ∎
    where
      eq₁ = eval-correct V γ
      eq₂ = eval-correct W γ
  compstate-eq (pmᶜ→ {W = W} {γ = γ} {M = M} {K = K}) =
    (< idf , ⟦ W ⟧ᵛ > ； assocl ； ⟦ M ⟧ᶜ) ⟦ γ ⟧ᴱ ⟦ K ⟧ᴷ
    ≡⟨ refl ⟩
      ⟦ M ⟧ᶜ (assocl ( ⟦ γ ⟧ᴱ , ⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ )) ⟦ K ⟧ᴷ
    ≡⟨ cong (λ x → ⟦ M ⟧ᶜ (assocl ( ⟦ γ ⟧ᴱ , x )) ⟦ K ⟧ᴷ) (cong₂ _,_ (eval-proj₁-eq W γ) (eval-proj₂-eq W γ)) ⟩
     ⟦ M ⟧ᶜ ((⟦ γ ⟧ᴱ , ⟦ proj₁-val (eval W γ) ⟧ⱽ) , ⟦ proj₂-val (eval W γ) ⟧ⱽ) ⟦ K ⟧ᴷ ∎
  compstate-eq (app→ {V = V} {W = W} {γ = γ} {K = K}) =
    cong (λ x → x (λ y → ⟦ K ⟧ᶜˢ (λ k → k y) k₀))
      (⟦ V ⟧ᵛ ⟦ γ ⟧ᴱ (⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ)
      ≡⟨ cong (λ x → x (⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ)) (eval-correct V γ) ⟩
      ⟦ eval V γ ⟧ⱽ (⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ)
      ≡⟨ clo-eq (eval V γ) (⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ) ⟦ proj₂ (proj₂ (clo-to-comp (eval V γ))) ⟧ᴱ refl ⟩
      ⟦ proj₁ (proj₂ (clo-to-comp (eval V γ))) ⟧ᶜ (⟦ proj₂ (proj₂ (clo-to-comp (eval V γ))) ⟧ᴱ , (⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ))
      ≡⟨ refl ⟩
      curry ⟦ proj₁ (proj₂ (clo-to-comp (eval V γ))) ⟧ᶜ ⟦ proj₂ (proj₂ (clo-to-comp (eval V γ))) ⟧ᴱ (⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ)
      ≡⟨ cong (λ x → curry ⟦ proj₁ (proj₂ (clo-to-comp (eval V γ))) ⟧ᶜ ⟦ proj₂ (proj₂ (clo-to-comp (eval V γ))) ⟧ᴱ x) (eval-correct W γ) ⟩
      curry ⟦ proj₁ (proj₂ (clo-to-comp (eval V γ))) ⟧ᶜ ⟦ proj₂ (proj₂ (clo-to-comp (eval V γ))) ⟧ᴱ ⟦ eval W γ ⟧ⱽ
      ≡⟨ cong (λ x → curry ⟦ proj₁ (proj₂ (clo-to-comp (eval V γ))) ⟧ᶜ x ⟦ eval W γ ⟧ⱽ) refl ⟩
      ⟦ proj₁ (proj₂ (clo-to-comp (eval V γ))) ⟧ᶜ (⟦ proj₂ (proj₂ (clo-to-comp (eval V γ))) ⟧ᴱ , ⟦ eval W γ ⟧ⱽ) ∎ )

  compstate-eq* : {σ σ₁ : CState} → σ →ᶜ* σ₁ → ⟦ σ ⟧ᶜꟴ ≡ ⟦ σ₁ ⟧ᶜꟴ
  compstate-eq* ε = refl
  compstate-eq* (s ◅ ss) = trans (compstate-eq s) (compstate-eq* ss)

  comp-machine-transitions-correct : (M : ε ⊢ᶜ ℛ) → ⟦ ⟨ M ╎ ⋄ ╎ ◻ ⟩ ⟧ᶜꟴ ≡ ⟦ proj₁ (exec M) ⟧ᶜꟴ
  comp-machine-transitions-correct M = compstate-eq* (proj₁ (proj₂ (proj₂ (proj₂ (exec M)))))

\end{code}
%<*SubVarCorrect>
\begin{code}
  comp-machine-correct : (M : ε ⊢ᶜ ℛ) → ⟦ M ⟧ᶜ tt k₀ ≡ k₀ ⟦ (proj₁ (proj₂ (exec M))) ⟧ⱽ
\end{code}
%</SubVarCorrect>
\begin{code}

  comp-machine-correct M =
      ⟦ M ⟧ᶜ tt k₀
    ≡⟨ eq ⟩
      ⟦ proj₁ (exec M) ⟧ᶜꟴ
    ≡⟨ cong ⟦_⟧ᶜꟴ hs ⟩
      ⟦ ⟨ proj₁ (halting-state (proj₁ (exec M)) (proj₁ (proj₂ (proj₂ (exec M))))) ╎ ◻ ⟩ ⟧ᶜꟴ
    ≡⟨ refl ⟩
      k₀ ⟦ proj₁ (halting-state (proj₁ (exec M)) (proj₁ (proj₂ (proj₂ (exec M))))) ⟧ⱽ
    ≡⟨ cong (λ x → k₀ ⟦ x ⟧ⱽ) (sym (proj₂ (proj₂ (proj₂ (proj₂ (exec M)))))) ⟩
      k₀ ⟦ proj₁ (proj₂ (exec M)) ⟧ⱽ ∎
    where
      eq = comp-machine-transitions-correct M
      hs = proj₂ (halting-state (proj₁ (exec M)) (proj₁ (proj₂ (proj₂ (exec M)))))

\end{code}
