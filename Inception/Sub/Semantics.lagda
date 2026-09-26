\begin{code}
{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Semantics (R : Set) where

open import Inception.Prelude
open Inception.Prelude.RTC
open import Inception.Sub.Syntax
open import Inception.Sub.Machine

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
  ⟦ pair W₁ W₂ ⟧ᵛ = < ⟦ W₁ ⟧ᵛ , ⟦ W₂ ⟧ᵛ >
  ⟦ unit ⟧ᵛ = const tt

  ⟦_⟧ᶜ : Γ ⊢ᶜ X → ⟦ Γ ⟧ˣ → K ⟦ X ⟧
  ⟦ return W ⟧ᶜ = ⟦ W ⟧ᵛ ； η
  ⟦ pm W M ⟧ᶜ = < idf , ⟦ W ⟧ᵛ > ； assocl ； ⟦ M ⟧ᶜ
  ⟦ push M₁ M₂ ⟧ᶜ = < idf , ⟦ M₁ ⟧ᶜ > ； τ ； ⟦ M₂ ⟧ᶜ *
  ⟦ app W₁ W₂ ⟧ᶜ = < ⟦ W₁ ⟧ᵛ , ⟦ W₂ ⟧ᵛ > ； ev
  ⟦ var W ⟧ᶜ = ⟦ W ⟧ᵛ ； varK
  ⟦ sub M₁ M₂ ⟧ᶜ = < curry ⟦ M₁ ⟧ᶜ , ⟦ M₂ ⟧ᶜ > ； subK
\end{code}
%</SemTerms>
\begin{code}

push-return-sem-eq : (γ : ⟦ Γ ⟧ˣ) → (k : (⟦ X ⟧ → R)) → (W : Val Γ Z) → (M₂ : (Γ ∙ Z) ⊢ᶜ X) →
      (< idf , ⟦ return W ⟧ᶜ > ； τ ； ⟦ M₂ ⟧ᶜ *) γ k ≡ ⟦ M₂ ⟧ᶜ (γ , ⟦ W ⟧ᵛ γ) k
push-return-sem-eq γ k W M₂ = refl

push-sem-eq : (γ : ⟦ Γ ⟧ˣ) → (k : (⟦ X ⟧ → R)) → (M₁ : Comp Γ Z) → (M₂ : (Γ ∙ Z) ⊢ᶜ X) →
      (< idf , ⟦ M₁ ⟧ᶜ > ； τ ； ⟦ M₂ ⟧ᶜ *) γ k ≡ ⟦ M₁ ⟧ᶜ γ (λ t → ((⟦ M₂ ⟧ᶜ *) ∘ τ)  (γ , η t) k)
push-sem-eq γ k W M₂ = refl

pm-sem-eq : (γ : ⟦ Γ ⟧ˣ) → (k : (⟦ X ⟧ → R)) → (W : Val Γ (X₁ `× X₂)) → (M : (Γ ∙ X₁ ∙ X₂) ⊢ᶜ X) →
      (< idf , ⟦ W ⟧ᵛ > ； assocl ； ⟦ M ⟧ᶜ) γ k ≡ ⟦ M ⟧ᶜ ((γ , proj₁ (⟦ W ⟧ᵛ γ)) , proj₂ (⟦ W ⟧ᵛ γ)) k
pm-sem-eq γ k W M = refl

app-sem-eq : (γ : ⟦ Γ ⟧ˣ) → (k : (⟦ Y ⟧ → R)) → (W₁ : Val Γ (X `⇒ Y)) → (W₂ : Val Γ X) →
      (< ⟦ W₁ ⟧ᵛ , ⟦ W₂ ⟧ᵛ > ； ev) γ k ≡ (⟦ W₁ ⟧ᵛ γ) (⟦ W₂ ⟧ᵛ γ) k
app-sem-eq γ k W₁ W₂ = refl

app-lam-sem-eq : (γ : ⟦ Γ ⟧ˣ) → (k : (⟦ Y ⟧ → R)) → (M : Comp (Γ ∙ X) Y) → (W₂ : Val Γ X) →
      (< ⟦ lam M ⟧ᵛ , ⟦ W₂ ⟧ᵛ > ； ev) γ k ≡ ⟦ M ⟧ᶜ (γ , (⟦ W₂ ⟧ᵛ γ)) k
app-lam-sem-eq γ k M W₂ = refl

mutual
  evalVal : Γ ⊢ᵛ X → ⟦ Γ ⟧ˣ → ⟦ X ⟧
  evalVal (var i) γ =
    ⟦ i ⟧ᵐ γ
  evalVal (lam M) γ a =
    curry (evalComp M) (γ , a)
  evalVal (pair W₁ W₂) γ =
    evalVal W₁ γ , evalVal W₂ γ
  evalVal unit γ = tt

  evalComp :  Γ ⊢ᶜ X → ⟦ Γ ⟧ˣ × (⟦ X ⟧ → R) → R
  evalComp (return W) (γ , k) =
    let w = evalVal W γ in
      k w
  evalComp (pm W M) (γ , k) =
    let w = evalVal W γ in
      evalComp M (((γ , proj₁ w) , proj₂ w) , k)
  evalComp (push M₁ M₂) (γ , k) =
    evalComp M₁ (γ , \a →
      evalComp M₂ ((γ , a) , k))
  evalComp (app W₁ W₂) (γ , k) =
    let w₁ = evalVal W₁ γ in
      let w₂ = evalVal W₂ γ in
        (w₁ w₂) k
  evalComp (var W) (γ , k) =
    let w = evalVal W γ in
      w
  evalComp (sub M₁ M₂) (γ , k) =
    let m₂ = evalComp M₂ (γ , k) in
      evalComp M₁ ((γ , m₂) , k)

⟦_⟧ˢ : Sub Γ Δ → ⟦ Γ ⟧ˣ → ⟦ Δ ⟧ˣ
⟦ sub-ε ⟧ˢ = const tt
⟦ sub-ex θ W ⟧ˢ = < ⟦ θ ⟧ˢ , ⟦ W ⟧ᵛ >

-- coherences
mutual
  wk-val-coh : (π : Γ ⊇ Δ) (W : Δ ⊢ᵛ X) → ⟦ wk-val π W ⟧ᵛ ≡ (⟦ π ⟧ʷ ； ⟦ W ⟧ᵛ)
  wk-val-coh π (var i) rewrite wk-mem-coh π i = refl
  wk-val-coh π (lam M) rewrite wk-comp-coh (wk-cong π) M = refl
  wk-val-coh π (pair W₁ W₂) rewrite wk-val-coh π W₁ | wk-val-coh π W₂ = refl
  wk-val-coh π unit = refl

  wk-comp-coh : (π : Γ ⊇ Δ) (M : Δ ⊢ᶜ X) → ⟦ wk-comp π M ⟧ᶜ ≡ (⟦ π ⟧ʷ ； ⟦ M ⟧ᶜ)
  wk-comp-coh π (return W) rewrite wk-val-coh π W = refl
  wk-comp-coh π (pm W M) rewrite wk-val-coh π W | wk-comp-coh (wk-cong (wk-cong π)) M = refl
  wk-comp-coh π (push M₁ M₂) rewrite wk-comp-coh π M₁ | wk-comp-coh (wk-cong π) M₂ = refl
  wk-comp-coh π (app W₁ W₂) rewrite wk-val-coh π W₁ | wk-val-coh π W₂ = refl
  wk-comp-coh π (var W) rewrite wk-val-coh π W = refl
  wk-comp-coh π (sub M₁ M₂) rewrite wk-comp-coh (wk-cong π) M₁ | wk-comp-coh π M₂ = refl

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
  sub-val-coh θ (pair W₁ W₂) rewrite sub-val-coh θ W₁ | sub-val-coh θ W₂ = refl
  sub-val-coh θ unit = refl

  sub-comp-coh : (θ : Sub Γ Δ) (M : Δ ⊢ᶜ X) → ⟦ sub-comp θ M ⟧ᶜ ≡ (⟦ θ ⟧ˢ ； ⟦ M ⟧ᶜ)
  sub-comp-coh θ (return W) rewrite sub-val-coh θ W = refl
  sub-comp-coh θ (pm W M) rewrite sub-val-coh θ W | sub-comp-coh (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (there here))) (var here)) M = refl
  sub-comp-coh θ (push M₁ M₂) rewrite sub-comp-coh θ M₁ | sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M₂ = refl
  sub-comp-coh θ (app W₁ W₂) rewrite sub-val-coh θ W₁ | sub-val-coh θ W₂ = refl
  sub-comp-coh θ (var W) rewrite sub-val-coh θ W = refl
  sub-comp-coh θ (sub M₁ M₂) rewrite sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var here)) M₁ | sub-comp-coh θ M₂ = refl

{-# REWRITE sub-val-coh #-}
{-# REWRITE sub-comp-coh #-}

mutual
  eqVal : Γ ⊢ᵛ W ≈ W' ∶ X → ⟦ W ⟧ᵛ ≡ ⟦ W' ⟧ᵛ
  eqVal ≈-refl = refl
  eqVal (≈-sym p) = sym (eqVal p)
  eqVal (≈-trans p q) = Eq.trans (eqVal p) (eqVal q)
  eqVal (lam-cong p) = cong curry (eqComp p)
  eqVal (pair-cong p q) = cong₂ <_,_> (eqVal p) (eqVal q)
  eqVal (unit-eta _) = refl
  eqVal (lam-eta _) = refl

  eqComp : Γ ⊢ᶜ M ≈ M' ∶ X → ⟦ M ⟧ᶜ ≡ ⟦ M' ⟧ᶜ
  eqComp ≈-refl = refl
  eqComp (≈-sym p) = sym (eqComp p)
  eqComp (≈-trans p q) = Eq.trans (eqComp p) (eqComp q)
  eqComp (return-cong p) rewrite eqVal p = refl
  eqComp (pm-cong p q) rewrite eqVal p | eqComp q = refl
  eqComp (push-cong p q) rewrite eqComp p | eqComp q = refl
  eqComp (app-cong p q) rewrite eqVal p | eqVal q = refl
  eqComp (var-cong p) rewrite eqVal p = refl
  eqComp (sub-cong p q) rewrite eqComp p | eqComp q = refl
  eqComp (pm-beta W₁ W₂ M) = refl
  eqComp (pm-eta W M) = refl
  eqComp (return-beta W M) = refl
  eqComp (return-eta M) = refl
  eqComp (push-eta M₁ M₂ M₃) = refl
  eqComp (lam-beta M W) = refl
  eqComp (sub-weak M₁ M₂) = refl
  eqComp (sub-subst M) = refl
  eqComp (sub-ext M W) = refl
  eqComp (sub-assoc M₁ M₂ M₃) = refl
  eqComp (var-push W M) = refl
  eqComp (sub-push M₁ M₂ M₃) = refl

wk-sem-trans : (π₁ : Wk Ψ Δ) → (π₂ : Wk Δ Γ) → (γ : ⟦ Ψ ⟧ˣ) → ⟦ π₂ ⟧ʷ (⟦ π₁ ⟧ʷ γ) ≡ ⟦ wk-trans π₁ π₂ ⟧ʷ γ
wk-sem-trans wk-ε π₂ γ = refl
wk-sem-trans {Γ = ε} (wk-cong π₁) π₂ γ = refl
wk-sem-trans {Γ = Γ ∙ x} (wk-cong π₁) (wk-cong π₂) γ =
       ⟦ wk-cong π₂ ⟧ʷ (⟦ wk-cong π₁ ⟧ʷ γ)
      ≡⟨ refl ⟩
       ⟦ π₂ ⟧ʷ (⟦ π₁ ⟧ʷ (proj₁ γ )) , proj₂ γ
      ≡⟨ cong (λ y → y , proj₂ γ) (wk-sem-trans π₁ π₂ (proj₁ γ)) ⟩
       ⟦ wk-trans π₁ π₂ ⟧ʷ (proj₁ γ) , proj₂ γ
      ≡⟨ refl ⟩
       ⟦ wk-cong (wk-trans π₁ π₂) ⟧ʷ γ ∎
wk-sem-trans {Γ = Γ ∙ x} (wk-cong π₁) (wk-wk π₂) γ =
       ⟦ wk-wk π₂ ⟧ʷ (⟦ wk-cong π₁ ⟧ʷ γ)
      ≡⟨ refl ⟩
       ⟦ π₂ ⟧ʷ (⟦ π₁ ⟧ʷ (proj₁ γ))
      ≡⟨ wk-sem-trans π₁ π₂ (proj₁ γ) ⟩
       ⟦ wk-trans π₁ π₂ ⟧ʷ (proj₁ γ)
      ≡⟨ refl ⟩
       ⟦ wk-trans (wk-cong π₁) (wk-wk π₂) ⟧ʷ γ ∎
wk-sem-trans (wk-wk π₁) wk-ε γ = refl
wk-sem-trans (wk-wk π₁) (wk-cong π₂) γ =
       ⟦ wk-cong π₂ ⟧ʷ (⟦ wk-wk π₁ ⟧ʷ γ)
      ≡⟨ refl ⟩
       ⟦ π₂ ⟧ʷ (proj₁ (⟦ π₁ ⟧ʷ (proj₁ γ))) , proj₂ (⟦ π₁ ⟧ʷ (proj₁ γ))
      ≡⟨ wk-sem-trans π₁ (wk-cong π₂) (proj₁ γ) ⟩
       ⟦ wk-trans π₁ (wk-cong π₂) ⟧ʷ (proj₁ γ)
      ≡⟨ refl ⟩
       ⟦ wk-wk (wk-trans π₁ (wk-cong π₂)) ⟧ʷ γ ∎
wk-sem-trans (wk-wk π₁) (wk-wk π₂) γ = wk-sem-trans π₁ (wk-wk π₂) (proj₁ γ)

module TopLevel {ℛ : Ty} {k₀ : ⟦ ℛ ⟧ → R} where

\end{code}
%<*SemMEnv>
\begin{code}
  mutual
    ⟦_⟧ᴱ : MEnv {ℛ = ℛ} Γ → ⟦ Γ ⟧ˣ
    ⟦ ⋄ ⟧ᴱ = tt
    ⟦ γ · 𝐖 ⟧ᴱ = ⟦ γ ⟧ᴱ , ⟦ 𝐖 ⟧ⱽ

    ⟦_⟧ⱽ : (𝐖 : MVal {ℛ = ℛ} X) → ⟦ X ⟧
    ⟦ unitᵛ ⟧ⱽ = tt
    ⟦ pairᵛ 𝐖₁ 𝐖₂ ⟧ⱽ = ⟦ 𝐖₁ ⟧ⱽ , ⟦ 𝐖₂ ⟧ⱽ
    ⟦ cloᵛ M γ ⟧ⱽ = (curry ⟦ M ⟧ᶜ) ⟦ γ ⟧ᴱ
    ⟦ jumpᵛ M γ cstack ⟧ⱽ = ⟦ M ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cstack ⟧ᴷ

    ⟦_⟧ᶜˢ : CStack {ℛ = ℛ} X → K ⟦ X ⟧ → K ⟦ ℛ ⟧
    ⟦ ◻ ⟧ᶜˢ = idf
    ⟦ < M ； γ >∷ cstack ⟧ᶜˢ = < const ⟦ γ ⟧ᴱ , idf > ； τ ； (⟦ M ⟧ᶜ *) ； ⟦ cstack ⟧ᶜˢ

    ⟦_⟧ᴷ : CStack {ℛ = ℛ} X → ⟦ X ⟧ → R
    ⟦_⟧ᴷ cstack t = ⟦ cstack ⟧ᶜˢ (η t) k₀
\end{code}
%</SemMEnv>

%<*SemCState>
\begin{code}
  ⟦_⟧ᶜꟴ : CState {ℛ = ℛ} → R
  ⟦ ⟨ 𝐖 ╎ cstack ⟩ ⟧ᶜꟴ = (η ⟦ 𝐖 ⟧ⱽ) ⟦ cstack ⟧ᴷ
  ⟦ ⟨ M ╎ γ ╎ cstack ⟩ ⟧ᶜꟴ = ⟦ M ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ cstack ⟧ᴷ
\end{code}
%</SemCState>

\begin{code}

  lookup-eq : (i : Γ ∋ X) → (γ : MEnv {ℛ = ℛ} Γ) → ⟦ i ⟧ᵐ ⟦ γ ⟧ᴱ ≡ ⟦ lookup i γ ⟧ⱽ
  lookup-eq here (γ · x) = refl
  lookup-eq (there i) (γ · x) = lookup-eq i γ

  eval-correct : (W : Val Γ X) → (γ : MEnv {ℛ = ℛ} Γ) → ⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ ≡ ⟦ eval W γ ⟧ⱽ
  eval-correct (var i) γ = lookup-eq i γ
  eval-correct (lam M) γ = refl
  eval-correct (pair W₁ W₂) γ = cong₂ _,_ (eval-correct W₁ γ) (eval-correct W₂ γ)
  eval-correct unit γ = refl

  push-eq : (cs : CStack {ℛ = ℛ} X) → (KX : K ⟦ X ⟧) → ⟦ cs ⟧ᶜˢ (λ k → KX k) k₀ ≡ KX (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
  push-eq ◻ KX = refl
  push-eq {X = X} ((< W ； γ >∷ cs)) KX =           ⟦ < W ； γ >∷ cs ⟧ᶜˢ KX k₀
                                    ≡⟨ refl ⟩
                                      ⟦ cs ⟧ᶜˢ (λ k → (λ x → KX (λ z → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) x)) k) k₀
                                    ≡⟨ push-eq cs (λ x → KX (λ z → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) x)) ⟩
                                      (λ x → KX (λ z → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) x)) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
                                    ≡⟨ refl ⟩
                                      KX (λ z →       ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)            )
                                    ≡⟨ cong KX push-eq'' ⟩
                                      KX (λ z →       ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) k) k₀                      )
                                    ≡⟨ refl ⟩
                                      KX (λ y → ⟦ < W ； γ >∷ cs ⟧ᶜˢ (λ k → k y) k₀) ∎

                                    where
                                      push-eq' : (z : ⟦ X ⟧) → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀) ≡ ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) k) k₀
                                      push-eq' z = sym (push-eq cs (⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z)))

                                      push-eq'' : (λ z → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)) ≡ (λ z → ⟦ cs ⟧ᶜˢ (λ k → ⟦ W ⟧ᶜ (⟦ γ ⟧ᴱ , z) k) k₀)
                                      push-eq'' = extensionality push-eq'

  jump-eq : (W : MVal `ℓ) → ⟦ W ⟧ⱽ ≡ ⟦ jump-to-state W ⟧ᶜꟴ
  jump-eq (jumpᵛ _ _ _) = refl

  jump-eq' : (W : Val Γ `ℓ) → (γ : MEnv {ℛ = ℛ} Γ) → ⟦ eval W γ ⟧ⱽ ≡ ⟦ jump-to-state (eval W γ) ⟧ᶜꟴ
  jump-eq' W γ = jump-eq (eval W γ)

  clo-eq : (W : MVal (X `⇒ Y)) → (T : ⟦ X ⟧) → (E : ⟦ proj₁ (clo-to-comp W) ⟧ˣ) → (eq : E ≡ ⟦ proj₂ (proj₂ (clo-to-comp W)) ⟧ᴱ) → ⟦ W ⟧ⱽ T ≡ ⟦ proj₁ (proj₂ (clo-to-comp W)) ⟧ᶜ (E , T)
  clo-eq (cloᵛ M γ) T E eq = cong (λ x → curry ⟦ M ⟧ᶜ x T) (sym eq)

  proj₁-val-eq : (W : MVal (X `× Y)) → proj₁ ⟦ W ⟧ⱽ ≡ ⟦ proj₁-val W ⟧ⱽ
  proj₁-val-eq (pairᵛ W₁ W₂) = refl

  proj₂-val-eq : (W : MVal (X `× Y)) → proj₂ ⟦ W ⟧ⱽ ≡ ⟦ proj₂-val W ⟧ⱽ
  proj₂-val-eq (pairᵛ W₁ W₂) = refl

  proj₁-val-eq' : (W : Val Γ (X `× Y)) → (γ : MEnv {ℛ = ℛ} Γ) → (proj₁ (⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ)) ≡ ⟦ proj₁-val (eval W γ) ⟧ⱽ
  proj₁-val-eq' W γ = trans (cong proj₁ (eval-correct W γ)) (proj₁-val-eq (eval W γ))

  proj₂-val-eq' : (W : Val Γ (X `× Y)) → (γ : MEnv {ℛ = ℛ} Γ) → (proj₂ (⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ)) ≡ ⟦ proj₂-val (eval W γ) ⟧ⱽ
  proj₂-val-eq' W γ = trans (cong proj₂ (eval-correct W γ)) (proj₂-val-eq (eval W γ))

  compstate-eq : {S S' : CState {ℛ = ℛ}} → S →ᶜ S' → ⟦ S ⟧ᶜꟴ ≡ ⟦ S' ⟧ᶜꟴ
  compstate-eq (eval→ {W = W} {γ = γ} {cstack = cstack}) =
    let
      eq = eval-correct W γ
    in
    η (⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ) ⟦ cstack ⟧ᴷ ≡⟨ cong (λ x → η x ⟦ cstack ⟧ᴷ) eq ⟩ η ⟦ eval W γ ⟧ⱽ ⟦ cstack ⟧ᴷ ∎
  compstate-eq (return→ {𝐖 = 𝐖} {M = M} {γ = γ} {cstack = cstack}) =
    let
      eq = push-eq cstack (⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , ⟦ 𝐖 ⟧ⱽ))
    in
      η ⟦ 𝐖 ⟧ⱽ ⟦ < M ； γ >∷ cstack ⟧ᴷ
    ≡⟨ refl ⟩
     ⟦ cstack ⟧ᶜˢ (λ k₁ → ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , ⟦ 𝐖 ⟧ⱽ) k₁) k₀
    ≡⟨ eq ⟩
     ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , ⟦ 𝐖 ⟧ⱽ) (λ y → ⟦ cstack ⟧ᶜˢ (λ k₁ → k₁ y) k₀)
    ≡⟨ refl ⟩
     ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , ⟦ 𝐖 ⟧ⱽ) ⟦ cstack ⟧ᴷ ∎
  compstate-eq (push→ {M₁ = M₁} {M₂ = M₂} {γ = γ} {cstack = cstack}) =
    (< idf , ⟦ M₁ ⟧ᶜ > ； τ ； ⟦ M₂ ⟧ᶜ *) ⟦ γ ⟧ᴱ ⟦ cstack ⟧ᴷ
     ≡⟨ refl ⟩
     ⟦ M₁ ⟧ᶜ ⟦ γ ⟧ᴱ (λ z → ⟦ M₂ ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ cstack ⟧ᶜˢ (λ k₁ → k₁ y) k₀))
     ≡⟨ cong (⟦ M₁ ⟧ᶜ ⟦ γ ⟧ᴱ) (extensionality (λ x → sym (push-eq cstack (⟦ M₂ ⟧ᶜ (⟦ γ ⟧ᴱ , x))))) ⟩
     ⟦ M₁ ⟧ᶜ ⟦ γ ⟧ᴱ (λ y → ⟦ cstack ⟧ᶜˢ (λ k₁ → ⟦ M₂ ⟧ᶜ (⟦ γ ⟧ᴱ , y) k₁) k₀)
     ≡⟨ refl ⟩
     ⟦ M₁ ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ < M₂ ； γ >∷ cstack ⟧ᴷ ∎
  compstate-eq sub→ = refl
  compstate-eq (var→ {W = W} {γ = γ} {cstack = cstack}) =
    let
      eq = eval-correct W γ
    in
    (⟦ W ⟧ᵛ ； varK) ⟦ γ ⟧ᴱ ⟦ cstack ⟧ᴷ ≡⟨ refl ⟩ ⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ ≡⟨ eq ⟩ ⟦ eval W γ ⟧ⱽ ≡⟨ jump-eq' W γ ⟩ ⟦ jump-to-state (eval W γ) ⟧ᶜꟴ ∎
  compstate-eq (pmᶜ→ {W = W} {γ = γ} {M = M} {cstack = cstack}) =
    (< idf , ⟦ W ⟧ᵛ > ； assocl ； ⟦ M ⟧ᶜ) ⟦ γ ⟧ᴱ ⟦ cstack ⟧ᴷ
    ≡⟨ refl ⟩
      ⟦ M ⟧ᶜ (assocl ( ⟦ γ ⟧ᴱ , ⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ )) ⟦ cstack ⟧ᴷ
    ≡⟨ cong (λ x → ⟦ M ⟧ᶜ (assocl ( ⟦ γ ⟧ᴱ , x )) ⟦ cstack ⟧ᴷ) (cong₂ _,_ (proj₁-val-eq' W γ) (proj₂-val-eq' W γ)) ⟩
     ⟦ M ⟧ᶜ ((⟦ γ ⟧ᴱ , ⟦ proj₁-val (eval W γ) ⟧ⱽ) , ⟦ proj₂-val (eval W γ) ⟧ⱽ) ⟦ cstack ⟧ᴷ ∎
  compstate-eq (app→ {W₁ = W₁} {W₂ = W₂} {γ = γ} {cstack = cstack}) =
    cong (λ x → x (λ y → ⟦ cstack ⟧ᶜˢ (λ cstack₁ → cstack₁ y) k₀))
      (⟦ W₁ ⟧ᵛ ⟦ γ ⟧ᴱ (⟦ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ)
      ≡⟨ cong (λ x → x (⟦ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ)) (eval-correct W₁ γ) ⟩
      ⟦ eval W₁ γ ⟧ⱽ (⟦ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ)
      ≡⟨ clo-eq (eval W₁ γ) (⟦ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ) ⟦ proj₂ (proj₂ (clo-to-comp (eval W₁ γ))) ⟧ᴱ refl ⟩
      ⟦ proj₁ (proj₂ (clo-to-comp (eval W₁ γ))) ⟧ᶜ (⟦ proj₂ (proj₂ (clo-to-comp (eval W₁ γ))) ⟧ᴱ , (⟦ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ))
      ≡⟨ refl ⟩
      curry ⟦ proj₁ (proj₂ (clo-to-comp (eval W₁ γ))) ⟧ᶜ ⟦ proj₂ (proj₂ (clo-to-comp (eval W₁ γ))) ⟧ᴱ (⟦ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ)
      ≡⟨ cong (λ x → curry ⟦ proj₁ (proj₂ (clo-to-comp (eval W₁ γ))) ⟧ᶜ ⟦ proj₂ (proj₂ (clo-to-comp (eval W₁ γ))) ⟧ᴱ x) (eval-correct W₂ γ) ⟩
      curry ⟦ proj₁ (proj₂ (clo-to-comp (eval W₁ γ))) ⟧ᶜ ⟦ proj₂ (proj₂ (clo-to-comp (eval W₁ γ))) ⟧ᴱ ⟦ eval W₂ γ ⟧ⱽ
      ≡⟨ cong (λ x → curry ⟦ proj₁ (proj₂ (clo-to-comp (eval W₁ γ))) ⟧ᶜ x ⟦ eval W₂ γ ⟧ⱽ) refl ⟩
      ⟦ proj₁ (proj₂ (clo-to-comp (eval W₁ γ))) ⟧ᶜ (⟦ proj₂ (proj₂ (clo-to-comp (eval W₁ γ))) ⟧ᴱ , ⟦ eval W₂ γ ⟧ⱽ) ∎ )

  compstate-eq* : {S S' : CState {ℛ = ℛ}} → S →ᶜ* S' → ⟦ S ⟧ᶜꟴ ≡ ⟦ S' ⟧ᶜꟴ
  compstate-eq* (S ◼) = refl
  compstate-eq* (S ~>⟨ S→S' ⟩ S'→*S'') = trans (compstate-eq S→S') (compstate-eq* S'→*S'')

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
