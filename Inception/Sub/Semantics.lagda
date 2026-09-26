\begin{code}
{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Semantics (R : Set) where

open import Inception.Prelude
open Inception.Prelude.RTC
open import Inception.Sub.Syntax

open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ-syntax; uncurry)

open import Function.Base using (const; _∘_; id)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; subst)
open Eq.≡-Reasoning using (step-≡-⟩; step-≡-∣; step-≡-⟨; _∎; step-≡)

---------------------------------------------------------------------------------

\end{code}
%<*Helpers>
\begin{code}
open import Level using (0ℓ)
open import Inception.Cont.Base
open import Inception.Monad.Base using (Monad)

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
⟦ A `× B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A `⇒ B ⟧ = ⟦ A ⟧ → K ⟦ B ⟧
⟦ `ℓ ⟧ = R

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
varK : {X : Set} → R → K X
varK v k = v

subK : {X : Set} → (R → K X) × K X → K X
subK (m₁ , m₂) k = m₁ (m₂ k) k

mutual

  ⟦_⟧ᵛ : Γ ⊢ᵛ X → ⟦ Γ ⟧ˣ → ⟦ X ⟧
  ⟦ var i ⟧ᵛ = ⟦ i ⟧ᵐ
  ⟦ lam M ⟧ᵛ = curry ⟦ M ⟧ᶜ
  ⟦ pair V W ⟧ᵛ = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ >
  ⟦ unit ⟧ᵛ = const tt

  ⟦_⟧ᶜ : Γ ⊢ᶜ X → ⟦ Γ ⟧ˣ → K ⟦ X ⟧
  ⟦ return W ⟧ᶜ = ⟦ W ⟧ᵛ ； η
  ⟦ pm W M ⟧ᶜ = < idf , ⟦ W ⟧ᵛ > ； assocl ； ⟦ M ⟧ᶜ
  ⟦ push M N ⟧ᶜ = < idf , ⟦ M ⟧ᶜ > ； τ ； ⟦ N ⟧ᶜ *
  ⟦ app V W ⟧ᶜ = < ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ > ； ev
  ⟦ var W ⟧ᶜ = ⟦ W ⟧ᵛ ； varK
  ⟦ sub M N ⟧ᶜ = < curry ⟦ M ⟧ᶜ , ⟦ N ⟧ᶜ > ； subK
\end{code}
%</SemTerms>
\begin{code}

push-return-sem-eq : (γ : ⟦ Γ ⟧ˣ) → (k : (⟦ X ⟧ → R)) → (W : Val Γ Z) → (M : (Γ ∙ Z) ⊢ᶜ X) →
      (< idf , ⟦ return W ⟧ᶜ > ； τ ； ⟦ M ⟧ᶜ *) γ k ≡ ⟦ M ⟧ᶜ (γ , ⟦ W ⟧ᵛ γ) k
push-return-sem-eq γ k W M = refl

push-sem-eq : (γ : ⟦ Γ ⟧ˣ) → (k : (⟦ X ⟧ → R)) → (M : Comp Γ Z) → (N : (Γ ∙ Z) ⊢ᶜ X) →
      (< idf , ⟦ M ⟧ᶜ > ； τ ； ⟦ N ⟧ᶜ *) γ k ≡ ⟦ M ⟧ᶜ γ (λ t → ((⟦ N ⟧ᶜ *) ∘ τ)  (γ , η t) k)
push-sem-eq γ k M N = refl

pm-sem-eq : (γ : ⟦ Γ ⟧ˣ) → (k : (⟦ X ⟧ → R)) → (W : Val Γ (X₁ `× X₂)) → (M : (Γ ∙ X₁ ∙ X₂) ⊢ᶜ X) →
      (< idf , ⟦ W ⟧ᵛ > ； assocl ； ⟦ M ⟧ᶜ) γ k ≡ ⟦ M ⟧ᶜ ((γ , proj₁ (⟦ W ⟧ᵛ γ)) , proj₂ (⟦ W ⟧ᵛ γ)) k
pm-sem-eq γ k W M = refl

app-sem-eq : (γ : ⟦ Γ ⟧ˣ) → (k : (⟦ Y ⟧ → R)) → (V : Val Γ (X `⇒ Y)) → (W : Val Γ X) →
      (< ⟦ V ⟧ᵛ , ⟦ W ⟧ᵛ > ； ev) γ k ≡ (⟦ V ⟧ᵛ γ) (⟦ W ⟧ᵛ γ) k
app-sem-eq γ k V W = refl

app-lam-sem-eq : (γ : ⟦ Γ ⟧ˣ) → (k : (⟦ Y ⟧ → R)) → (M : Comp (Γ ∙ X) Y) → (V : Val Γ X) →
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

  evalComp :  Γ ⊢ᶜ X → ⟦ Γ ⟧ˣ × (⟦ X ⟧ → R) → R
  evalComp (return W) (γ , k) =
    let w = evalVal W γ in
      k w
  evalComp (pm W M) (γ , k) =
    let w = evalVal W γ in
      evalComp M (((γ , proj₁ w) , proj₂ w) , k)
  evalComp (push M N) (γ , k) =
    evalComp M (γ , \a →
      evalComp N ((γ , a) , k))
  evalComp (app V W) (γ , k) =
    let w₁ = evalVal V γ in
      let w₂ = evalVal W γ in
        (w₁ w₂) k
  evalComp (var W) (γ , k) =
    let w = evalVal W γ in
      w
  evalComp (sub M N) (γ , k) =
    let m = evalComp N (γ , k) in
      evalComp M ((γ , m) , k)

⟦_⟧ˢ : Sub Γ Δ → ⟦ Γ ⟧ˣ → ⟦ Δ ⟧ˣ
⟦ sub-ε ⟧ˢ = const tt
⟦ sub-ex θ W ⟧ˢ = < ⟦ θ ⟧ˢ , ⟦ W ⟧ᵛ >

-- coherences
mutual
  wk-val-coh : (π : Γ ⊇ Δ) (W : Δ ⊢ᵛ X) → ⟦ wk-val π W ⟧ᵛ ≡ (⟦ π ⟧ʷ ； ⟦ W ⟧ᵛ)
  wk-val-coh π (var i) rewrite wk-mem-coh π i = refl
  wk-val-coh π (lam M) rewrite wk-comp-coh (wk-cong π) M = refl
  wk-val-coh π (pair V W) rewrite wk-val-coh π V | wk-val-coh π W = refl
  wk-val-coh π unit = refl

  wk-comp-coh : (π : Γ ⊇ Δ) (M : Δ ⊢ᶜ X) → ⟦ wk-comp π M ⟧ᶜ ≡ (⟦ π ⟧ʷ ； ⟦ M ⟧ᶜ)
  wk-comp-coh π (return W) rewrite wk-val-coh π W = refl
  wk-comp-coh π (pm W M) rewrite wk-val-coh π W | wk-comp-coh (wk-cong (wk-cong π)) M = refl
  wk-comp-coh π (push M N) rewrite wk-comp-coh π M | wk-comp-coh (wk-cong π) N = refl
  wk-comp-coh π (app V W) rewrite wk-val-coh π V | wk-val-coh π W = refl
  wk-comp-coh π (var W) rewrite wk-val-coh π W = refl
  wk-comp-coh π (sub M N) rewrite wk-comp-coh (wk-cong π) M | wk-comp-coh π N = refl

{-# REWRITE wk-val-coh #-}
{-# REWRITE wk-comp-coh #-}

sub-mem-coh : (θ : Sub Γ Δ) (i : Δ ∋ X) → ⟦ sub-mem θ i ⟧ᵛ ≡ (⟦ θ ⟧ˢ ； ⟦ i ⟧ᵐ)
sub-mem-coh (sub-ex θ W) here = refl
sub-mem-coh (sub-ex θ W) (there i) rewrite sub-mem-coh θ i = refl
{-# REWRITE sub-mem-coh #-}

sub-wk-coh : (π : Γ ⊇ Δ) (θ : Sub Δ Ψ) → ⟦ sub-wk π θ ⟧ˢ ≡ (⟦ π ⟧ʷ ； ⟦ θ ⟧ˢ)
sub-wk-coh π sub-ε = refl
sub-wk-coh π (sub-ex θ W) rewrite sub-wk-coh π θ | wk-val-coh π W = refl
{-# REWRITE sub-wk-coh #-}

sub-id-coh : ⟦ sub-id {Γ} ⟧ˢ ≡ id
sub-id-coh {ε} = refl
sub-id-coh {Γ ∙ X} = funext \(γ , x) → cong₂ _,_ (happly sub-id-coh γ) refl
{-# REWRITE sub-id-coh #-}

mutual
  sub-val-coh : (θ : Sub Γ Δ) (W : Δ ⊢ᵛ X) → ⟦ sub-val θ W ⟧ᵛ ≡ (⟦ θ ⟧ˢ ； ⟦ W ⟧ᵛ)
  sub-val-coh θ (var i) = refl
  sub-val-coh θ (lam M) rewrite sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M = refl
  sub-val-coh θ (pair V W) rewrite sub-val-coh θ V | sub-val-coh θ W = refl
  sub-val-coh θ unit = refl

  sub-comp-coh : (θ : Sub Γ Δ) (M : Δ ⊢ᶜ X) → ⟦ sub-comp θ M ⟧ᶜ ≡ (⟦ θ ⟧ˢ ； ⟦ M ⟧ᶜ)
  sub-comp-coh θ (return W) rewrite sub-val-coh θ W = refl
  sub-comp-coh θ (pm W M) rewrite sub-val-coh θ W | sub-comp-coh (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M = refl
  sub-comp-coh θ (push M N) rewrite sub-comp-coh θ M | sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) N = refl
  sub-comp-coh θ (app V W) rewrite sub-val-coh θ V | sub-val-coh θ W = refl
  sub-comp-coh θ (var W) rewrite sub-val-coh θ W = refl
  sub-comp-coh θ (sub M N) rewrite sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M | sub-comp-coh θ N = refl

{-# REWRITE sub-val-coh #-}
{-# REWRITE sub-comp-coh #-}

mutual
  eqVal : Γ ⊢ᵛ V₁ ≈ V₂ ∶ X → ⟦ V₁ ⟧ᵛ ≡ ⟦ V₂ ⟧ᵛ
  eqVal ≈-refl = refl
  eqVal (≈-sym p) = sym (eqVal p)
  eqVal (≈-trans p q) = Eq.trans (eqVal p) (eqVal q)
  eqVal (lam-cong p) = cong curry (eqComp p)
  eqVal (pair-cong p q) = cong₂ <_,_> (eqVal p) (eqVal q)
  eqVal (unit-eta _) = refl
  eqVal (lam-eta _) = refl

  eqComp : Γ ⊢ᶜ M₁ ≈ M₂ ∶ X → ⟦ M₁ ⟧ᶜ ≡ ⟦ M₂ ⟧ᶜ
  eqComp ≈-refl = refl
  eqComp (≈-sym p) = sym (eqComp p)
  eqComp (≈-trans p q) = Eq.trans (eqComp p) (eqComp q)
  eqComp (return-cong p) rewrite eqVal p = refl
  eqComp (pm-cong p q) rewrite eqVal p | eqComp q = refl
  eqComp (push-cong p q) rewrite eqComp p | eqComp q = refl
  eqComp (app-cong p q) rewrite eqVal p | eqVal q = refl
  eqComp (var-cong p) rewrite eqVal p = refl
  eqComp (sub-cong p q) rewrite eqComp p | eqComp q = refl
  eqComp (pm-beta V W M) = refl
  eqComp (pm-eta V M) = refl
  eqComp (return-beta V M) = refl
  eqComp (return-eta M) = refl
  eqComp (push-eta M N P) = refl
  eqComp (lam-beta M V) = refl
  eqComp (sub-weak M N) = refl
  eqComp (sub-subst M) = refl
  eqComp (sub-ext M V) = refl
  eqComp (sub-assoc M N P) = refl
  eqComp (var-push V M) = refl
  eqComp (sub-push M N P) = refl

wk-sem-trans : (π : Wk Ψ Δ) → (δ : Wk Δ Γ) → (γ : ⟦ Ψ ⟧ˣ) → ⟦ δ ⟧ʷ (⟦ π ⟧ʷ γ) ≡ ⟦ wk-trans π δ ⟧ʷ γ
wk-sem-trans wk-ε π γ = refl
wk-sem-trans {Γ = ε} (wk-cong π) δ γ = refl
wk-sem-trans {Γ = Γ ∙ x} (wk-cong π) (wk-cong δ) γ =
       ⟦ wk-cong δ ⟧ʷ (⟦ wk-cong π ⟧ʷ γ)
      ≡⟨ refl ⟩
       ⟦ δ ⟧ʷ (⟦ π ⟧ʷ (proj₁ γ )) , proj₂ γ
      ≡⟨ cong (λ y → y , proj₂ γ) (wk-sem-trans π δ (proj₁ γ)) ⟩
       ⟦ wk-trans π δ ⟧ʷ (proj₁ γ) , proj₂ γ
      ≡⟨ refl ⟩
       ⟦ wk-cong (wk-trans π δ) ⟧ʷ γ ∎
wk-sem-trans {Γ = Γ ∙ x} (wk-cong π) (wk-wk δ) γ =
       ⟦ wk-wk δ ⟧ʷ (⟦ wk-cong π ⟧ʷ γ)
      ≡⟨ refl ⟩
       ⟦ δ ⟧ʷ (⟦ π ⟧ʷ (proj₁ γ))
      ≡⟨ wk-sem-trans π δ (proj₁ γ) ⟩
       ⟦ wk-trans π δ ⟧ʷ (proj₁ γ)
      ≡⟨ refl ⟩
       ⟦ wk-trans (wk-cong π) (wk-wk δ) ⟧ʷ γ ∎
wk-sem-trans (wk-wk π) wk-ε γ = refl
wk-sem-trans (wk-wk π) (wk-cong δ) γ =
       ⟦ wk-cong δ ⟧ʷ (⟦ wk-wk π ⟧ʷ γ)
      ≡⟨ refl ⟩
       ⟦ δ ⟧ʷ (proj₁ (⟦ π ⟧ʷ (proj₁ γ))) , proj₂ (⟦ π ⟧ʷ (proj₁ γ))
      ≡⟨ wk-sem-trans π (wk-cong δ) (proj₁ γ) ⟩
       ⟦ wk-trans π (wk-cong δ) ⟧ʷ (proj₁ γ)
      ≡⟨ refl ⟩
       ⟦ wk-wk (wk-trans π (wk-cong δ)) ⟧ʷ γ ∎
wk-sem-trans (wk-wk π) (wk-wk δ) γ = wk-sem-trans π (wk-wk δ) (proj₁ γ)

module TopLevel {ℛ : Ty} {k₀ : ⟦ ℛ ⟧ → R} where

  open import Inception.Sub.Machine ℛ

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
    ⟦ jumpᵛ M γ K ⟧ⱽ = ⟦ M ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ K ⟧ᴷ

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

  eval-correct : (W : Val Γ X) → (γ : MEnv Γ) → ⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ ≡ ⟦ eval W γ ⟧ⱽ
  eval-correct (var i) γ = lookup-eq i γ
  eval-correct (lam M) γ = refl
  eval-correct (pair V W) γ = cong₂ _,_ (eval-correct V γ) (eval-correct W γ)
  eval-correct unit γ = refl

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
                                      push-eq-fun = extensionality push-eq-at

  jump-eq : (𝐖 : MVal `ℓ) → ⟦ 𝐖 ⟧ⱽ ≡ ⟦ jump-to-state 𝐖 ⟧ᶜꟴ
  jump-eq (jumpᵛ _ _ _) = refl

  eval-jump-eq : (W : Val Γ `ℓ) → (γ : MEnv Γ) → ⟦ eval W γ ⟧ⱽ ≡ ⟦ jump-to-state (eval W γ) ⟧ᶜꟴ
  eval-jump-eq W γ = jump-eq (eval W γ)

  clo-eq : (𝐖 : MVal (X `⇒ Y)) → (T : ⟦ X ⟧) → (E : ⟦ proj₁ (clo-to-comp 𝐖) ⟧ˣ) → (eq : E ≡ ⟦ proj₂ (proj₂ (clo-to-comp 𝐖)) ⟧ᴱ) → ⟦ 𝐖 ⟧ⱽ T ≡ ⟦ proj₁ (proj₂ (clo-to-comp 𝐖)) ⟧ᶜ (E , T)
  clo-eq (cloᵛ M γ) T E eq = cong (λ x → curry ⟦ M ⟧ᶜ x T) (sym eq)

  proj₁-val-eq : (𝐖 : MVal (X `× Y)) → proj₁ ⟦ 𝐖 ⟧ⱽ ≡ ⟦ proj₁-val 𝐖 ⟧ⱽ
  proj₁-val-eq (pairᵛ 𝐕 𝐖) = refl

  proj₂-val-eq : (𝐖 : MVal (X `× Y)) → proj₂ ⟦ 𝐖 ⟧ⱽ ≡ ⟦ proj₂-val 𝐖 ⟧ⱽ
  proj₂-val-eq (pairᵛ 𝐕 𝐖) = refl

  eval-proj₁-eq : (W : Val Γ (X `× Y)) → (γ : MEnv Γ) → (proj₁ (⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ)) ≡ ⟦ proj₁-val (eval W γ) ⟧ⱽ
  eval-proj₁-eq W γ = trans (cong proj₁ (eval-correct W γ)) (proj₁-val-eq (eval W γ))

  eval-proj₂-eq : (W : Val Γ (X `× Y)) → (γ : MEnv Γ) → (proj₂ (⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ)) ≡ ⟦ proj₂-val (eval W γ) ⟧ⱽ
  eval-proj₂-eq W γ = trans (cong proj₂ (eval-correct W γ)) (proj₂-val-eq (eval W γ))

  compstate-eq : {σ σ₁ : CState} → σ →ᶜ σ₁ → ⟦ σ ⟧ᶜꟴ ≡ ⟦ σ₁ ⟧ᶜꟴ
  compstate-eq (eval→ {W = W} {γ = γ} {K = K}) =
    let
      eq = eval-correct W γ
    in
    η (⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ) ⟦ K ⟧ᴷ ≡⟨ cong (λ x → η x ⟦ K ⟧ᴷ) eq ⟩ η ⟦ eval W γ ⟧ⱽ ⟦ K ⟧ᴷ ∎
  compstate-eq (return→ {𝐖 = 𝐖} {M = M} {γ = γ} {K = K}) =
    let
      eq = push-eq K (⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , ⟦ 𝐖 ⟧ⱽ))
    in
      η ⟦ 𝐖 ⟧ⱽ ⟦ < M ； γ >∷ K ⟧ᴷ
    ≡⟨ refl ⟩
     ⟦ K ⟧ᶜˢ (λ k₁ → ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , ⟦ 𝐖 ⟧ⱽ) k₁) k₀
    ≡⟨ eq ⟩
     ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , ⟦ 𝐖 ⟧ⱽ) (λ y → ⟦ K ⟧ᶜˢ (λ k₁ → k₁ y) k₀)
    ≡⟨ refl ⟩
     ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , ⟦ 𝐖 ⟧ⱽ) ⟦ K ⟧ᴷ ∎
  compstate-eq (push→ {M = M} {N = N} {γ = γ} {K = K}) =
    (< idf , ⟦ M ⟧ᶜ > ； τ ； ⟦ N ⟧ᶜ *) ⟦ γ ⟧ᴱ ⟦ K ⟧ᴷ
     ≡⟨ refl ⟩
     ⟦ M ⟧ᶜ ⟦ γ ⟧ᴱ (λ z → ⟦ N ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ K ⟧ᶜˢ (λ k₁ → k₁ y) k₀))
     ≡⟨ cong (⟦ M ⟧ᶜ ⟦ γ ⟧ᴱ) (extensionality (λ x → sym (push-eq K (⟦ N ⟧ᶜ (⟦ γ ⟧ᴱ , x))))) ⟩
     ⟦ M ⟧ᶜ ⟦ γ ⟧ᴱ (λ y → ⟦ K ⟧ᶜˢ (λ k₁ → ⟦ N ⟧ᶜ (⟦ γ ⟧ᴱ , y) k₁) k₀)
     ≡⟨ refl ⟩
     ⟦ M ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ < N ； γ >∷ K ⟧ᴷ ∎
  compstate-eq sub→ = refl
  compstate-eq (var→ {W = W} {γ = γ} {K = K}) =
    let
      eq = eval-correct W γ
    in
    (⟦ W ⟧ᵛ ； varK) ⟦ γ ⟧ᴱ ⟦ K ⟧ᴷ ≡⟨ refl ⟩ ⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ ≡⟨ eq ⟩ ⟦ eval W γ ⟧ⱽ ≡⟨ eval-jump-eq W γ ⟩ ⟦ jump-to-state (eval W γ) ⟧ᶜꟴ ∎
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
  compstate-eq* (σ ◼) = refl
  compstate-eq* (σ ~>⟨ s ⟩ ss) = trans (compstate-eq s) (compstate-eq* ss)

  comp-machine-transitions-correct : (M : Comp ε ℛ) → ⟦ ⟨ M ╎ ⋄ ╎ ◻ ⟩ ⟧ᶜꟴ ≡ ⟦ proj₁ (exec M) ⟧ᶜꟴ
  comp-machine-transitions-correct M = compstate-eq* (proj₁ (proj₂ (proj₂ (proj₂ (exec M)))))

\end{code}
%<*SubVarCorrect>
\begin{code}
  comp-machine-correct : (M : Comp ε ℛ) → ⟦ M ⟧ᶜ tt k₀ ≡ k₀ ⟦ (proj₁ (proj₂ (exec M))) ⟧ⱽ
\end{code}
%</SubVarCorrect>
\begin{code}

  comp-machine-correct M =
    let
      eq = comp-machine-transitions-correct M
      hs = proj₂ (halting-state (proj₁ (exec M)) (proj₁ (proj₂ (proj₂ (exec M)))))
    in
      ⟦ M ⟧ᶜ tt k₀
    ≡⟨ eq ⟩
      ⟦ proj₁ (exec M) ⟧ᶜꟴ
    ≡⟨ cong ⟦_⟧ᶜꟴ hs ⟩
      ⟦ ⟨ proj₁ (halting-state (proj₁ (exec M)) (proj₁ (proj₂ (proj₂ (exec M))))) ╎ ◻ ⟩ ⟧ᶜꟴ
    ≡⟨ refl ⟩
      k₀ ⟦ proj₁ (halting-state (proj₁ (exec M)) (proj₁ (proj₂ (proj₂ (exec M))))) ⟧ⱽ
    ≡⟨ cong (λ x → k₀ ⟦ x ⟧ⱽ) (sym (proj₂ (proj₂ (proj₂ (proj₂ (exec M)))))) ⟩
      k₀ ⟦ proj₁ (proj₂ (exec M)) ⟧ⱽ ∎

\end{code}
