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

infixr 4 _；_

_；_ : ∀ {ℓ} {A B C : Set ℓ} -> (A -> B) -> (B -> C) -> (A -> C)
f ； g = g ∘ f

idf : ∀ {ℓ} {A : Set ℓ} -> A -> A
idf a = a

assocl : ∀ {ℓ} {A B C : Set ℓ} -> A × (B × C) -> (A × B) × C
assocl (a , (b , c)) = (a , b) , c

K : ∀ {ℓ} -> Set ℓ -> Set ℓ
K X = (X -> R) -> R

infix 5 _♯

_♯ : ∀ {ℓ} {X Y : Set ℓ} -> (X -> K Y) -> K X -> K Y
(f ♯) kx k = kx \x -> f x k

η : ∀ {ℓ} -> {X : Set ℓ} -> X -> K X
η x k = k x

μ : ∀ {ℓ} -> {X : Set ℓ} -> K (K X) -> K X
μ kkx k = kkx \kx -> kx k

τ : ∀ {ℓ} -> {X Y : Set ℓ} -> X × K Y -> K (X × Y)
τ (x , ky) k = ky \z -> k (x , z)

cocurry : ∀ {ℓ} -> {X Y Z : Set ℓ} -> (Z × (X -> R) -> K Y) -> Z -> K (X ⊎ Y)
cocurry f z k = f (z , k ∘ inj₁) (k ∘ inj₂)

varK : ∀ {ℓ} {X : Set ℓ} -> R -> K X
varK = const

subK : ∀ {ℓ} {X : Set ℓ} -> (R -> K X) × K X -> K X
subK (f , n) k = f (n k) k

\end{code}
%<*SemTy>
\begin{code}

⟦_⟧ : Ty -> Set
⟦ `Unit ⟧ = ⊤
⟦ A `× B ⟧ = ⟦ A ⟧ × ⟦ B ⟧
⟦ A `⇒ B ⟧ = ⟦ A ⟧ -> K ⟦ B ⟧
⟦ `L ⟧ = R

\end{code}
%</SemTy>

%<*SemCtx>
\begin{code}

⟦_⟧ˣ : Ctx -> Set
⟦ ε ⟧ˣ = ⊤
⟦ Γ ∙ A ⟧ˣ = ⟦ Γ ⟧ˣ × ⟦ A ⟧

\end{code}
%</SemCtx>

\begin{code}

⟦_⟧ʷ : Γ ⊇ Δ -> ⟦ Γ ⟧ˣ -> ⟦ Δ ⟧ˣ
⟦ wk-ε ⟧ʷ = idf
⟦ wk-cong π ⟧ʷ = < proj₁ ； ⟦ π ⟧ʷ , proj₂ >
⟦ wk-wk π ⟧ʷ = proj₁ ； ⟦ π ⟧ʷ

\end{code}
%<*SemMem>
\begin{code}

⟦_⟧ᵐ : Γ ∋ X -> ⟦ Γ ⟧ˣ -> ⟦ X ⟧
⟦ new ⟧ᵐ = proj₂
⟦ old x ⟧ᵐ = proj₁ ； ⟦ x ⟧ᵐ

\end{code}
%</SemMem>
\begin{code}

mutual

\end{code}
%<*SemPure>
\begin{code}

  ⟦_⟧ᵖ : Γ ⊢ᵖ X -> ⟦ Γ ⟧ˣ -> ⟦ X ⟧
  ⟦ var i ⟧ᵖ = ⟦ i ⟧ᵐ
  ⟦ lam M ⟧ᵖ = curry ⟦ M ⟧ᶜ
  ⟦ pair W₁ W₂ ⟧ᵖ = < ⟦ W₁ ⟧ᵖ , ⟦ W₂ ⟧ᵖ >
  ⟦ pm W₁ W₂ ⟧ᵖ = < idf , ⟦ W₁ ⟧ᵖ > ； assocl ； ⟦ W₂ ⟧ᵖ
  ⟦ unit ⟧ᵖ = const tt

\end{code}
%</SemPure>

%<*SemComp>
\begin{code}

  ⟦_⟧ᶜ : Γ ⊢ᶜ X -> ⟦ Γ ⟧ˣ -> K ⟦ X ⟧
  ⟦ return W ⟧ᶜ = ⟦ W ⟧ᵖ ； η
  ⟦ pm W M ⟧ᶜ = < idf , ⟦ W ⟧ᵖ > ； assocl ； ⟦ M ⟧ᶜ
  ⟦ push M₁ M₂ ⟧ᶜ = < idf , ⟦ M₁ ⟧ᶜ > ； τ ； ⟦ M₂ ⟧ᶜ ♯
  ⟦ app W₁ W₂ ⟧ᶜ = < ⟦ W₁ ⟧ᵖ , ⟦ W₂ ⟧ᵖ > ； uncurry idf
  ⟦ var W ⟧ᶜ = ⟦ W ⟧ᵖ ； varK
  ⟦ sub M₁ M₂ ⟧ᶜ = < curry ⟦ M₁ ⟧ᶜ , ⟦ M₂ ⟧ᶜ > ； subK

\end{code}
%</SemComp>
\begin{code}

mutual
  evalPure : Γ ⊢ᵖ X -> ⟦ Γ ⟧ˣ -> ⟦ X ⟧
  evalPure (var i) γ =
    ⟦ i ⟧ᵐ γ
  evalPure (lam M) γ a =
    curry (evalComp M) (γ , a)
  evalPure (pair W₁ W₂) γ =
    evalPure W₁ γ , evalPure W₂ γ
  evalPure (pm W₁ W₂) γ =
    let w₁ = evalPure W₁ γ in
      evalPure W₂ ((γ , proj₁ w₁) , proj₂ w₁)
  evalPure unit γ = tt

  evalComp :  Γ ⊢ᶜ X -> ⟦ Γ ⟧ˣ × (⟦ X ⟧ -> R) -> R
  evalComp (return W) (γ , k) =
    let w = evalPure W γ in
      k w
  evalComp (pm W M) (γ , k) =
    let w = evalPure W γ in
      evalComp M (((γ , proj₁ w) , proj₂ w) , k)
  evalComp (push M₁ M₂) (γ , k) =
    evalComp M₁ (γ , \a ->
      evalComp M₂ ((γ , a) , k))
  evalComp (app W₁ W₂) (γ , k) =
    let w₁ = evalPure W₁ γ in
      let w₂ = evalPure W₂ γ in
        (w₁ w₂) k
  evalComp (var W) (γ , k) =
    let w = evalPure W γ in
      w
  evalComp (sub M₁ M₂) (γ , k) =
    let m₂ = evalComp M₂ (γ , k) in
      evalComp M₁ ((γ , m₂) , k)

⟦_⟧ˢ : Sub Γ Δ -> ⟦ Γ ⟧ˣ -> ⟦ Δ ⟧ˣ
⟦ sub-ε ⟧ˢ = const tt
⟦ sub-ex θ W ⟧ˢ = < ⟦ θ ⟧ˢ , ⟦ W ⟧ᵖ >

-- coherences
wk-id-coh : ⟦ wk-id {Γ} ⟧ʷ ≡ id
wk-id-coh {ε} = refl
wk-id-coh {Γ ∙ A} rewrite wk-id-coh {Γ} = refl
{-# REWRITE wk-id-coh #-}

wk-mem-coh : (π : Γ ⊇ Δ) (i : Δ ∋ X) -> ⟦ wk-mem π i ⟧ᵐ ≡ (⟦ π ⟧ʷ ； ⟦ i ⟧ᵐ)
wk-mem-coh (wk-cong π) new = refl
wk-mem-coh (wk-cong π) (old i) rewrite wk-mem-coh π i = refl
wk-mem-coh (wk-wk π) new rewrite wk-mem-coh π new = refl
wk-mem-coh (wk-wk π) (old i) rewrite wk-mem-coh π (old i) = refl

mutual
  wk-pure-coh : (π : Γ ⊇ Δ) (W : Δ ⊢ᵖ X) -> ⟦ wk-pure π W ⟧ᵖ ≡ (⟦ π ⟧ʷ ； ⟦ W ⟧ᵖ)
  wk-pure-coh π (var i) rewrite wk-mem-coh π i = refl
  wk-pure-coh π (lam M) rewrite wk-comp-coh (wk-cong π) M = refl
  wk-pure-coh π (pair W₁ W₂) rewrite wk-pure-coh π W₁ | wk-pure-coh π W₂ = refl
  wk-pure-coh π (pm W₁ W₂) rewrite wk-pure-coh π W₁ | wk-pure-coh (wk-cong (wk-cong π)) W₂ = refl
  wk-pure-coh π unit = refl

  wk-comp-coh : (π : Γ ⊇ Δ) (M : Δ ⊢ᶜ X) -> ⟦ wk-comp π M ⟧ᶜ ≡ (⟦ π ⟧ʷ ； ⟦ M ⟧ᶜ)
  wk-comp-coh π (return W) rewrite wk-pure-coh π W = refl
  wk-comp-coh π (pm W M) rewrite wk-pure-coh π W | wk-comp-coh (wk-cong (wk-cong π)) M = refl
  wk-comp-coh π (push M₁ M₂) rewrite wk-comp-coh π M₁ | wk-comp-coh (wk-cong π) M₂ = refl
  wk-comp-coh π (app W₁ W₂) rewrite wk-pure-coh π W₁ | wk-pure-coh π W₂ = refl
  wk-comp-coh π (var W) rewrite wk-pure-coh π W = refl
  wk-comp-coh π (sub M₁ M₂) rewrite wk-comp-coh (wk-cong π) M₁ | wk-comp-coh π M₂ = refl

{-# REWRITE wk-pure-coh #-}
{-# REWRITE wk-comp-coh #-}

sub-mem-coh : (θ : Sub Γ Δ) (i : Δ ∋ X) -> ⟦ sub-mem θ i ⟧ᵖ ≡ (⟦ θ ⟧ˢ ； ⟦ i ⟧ᵐ)
sub-mem-coh (sub-ex θ W) new = refl
sub-mem-coh (sub-ex θ W) (old i) rewrite sub-mem-coh θ i = refl
{-# REWRITE sub-mem-coh #-}

sub-wk-coh : (π : Γ ⊇ Δ) (θ : Sub Δ Ψ) -> ⟦ sub-wk π θ ⟧ˢ ≡ (⟦ π ⟧ʷ ； ⟦ θ ⟧ˢ)
sub-wk-coh π sub-ε = refl
sub-wk-coh π (sub-ex θ W) rewrite sub-wk-coh π θ | wk-pure-coh π W = refl
{-# REWRITE sub-wk-coh #-}

sub-id-coh : ⟦ sub-id {Γ} ⟧ˢ ≡ id
sub-id-coh {ε} = refl
sub-id-coh {Γ ∙ X} = funext \(γ , x) -> cong₂ _,_ (happly sub-id-coh γ) refl
{-# REWRITE sub-id-coh #-}

mutual
  sub-pure-coh : (θ : Sub Γ Δ) (W : Δ ⊢ᵖ X) -> ⟦ sub-pure θ W ⟧ᵖ ≡ (⟦ θ ⟧ˢ ； ⟦ W ⟧ᵖ)
  sub-pure-coh θ (var i) = refl
  sub-pure-coh θ (lam M) rewrite sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var new)) M = refl
  sub-pure-coh θ (pair W₁ W₂) rewrite sub-pure-coh θ W₁ | sub-pure-coh θ W₂ = refl
  sub-pure-coh θ (pm W M) rewrite sub-pure-coh θ W | sub-pure-coh (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (old new))) (var new)) M = refl
  sub-pure-coh θ unit = refl

  sub-comp-coh : (θ : Sub Γ Δ) (M : Δ ⊢ᶜ X) -> ⟦ sub-comp θ M ⟧ᶜ ≡ (⟦ θ ⟧ˢ ； ⟦ M ⟧ᶜ)
  sub-comp-coh θ (return W) rewrite sub-pure-coh θ W = refl
  sub-comp-coh θ (pm W M) rewrite sub-pure-coh θ W | sub-comp-coh (sub-ex (sub-ex (sub-wk (wk-wk (wk-wk wk-id)) θ) (var (old new))) (var new)) M = refl
  sub-comp-coh θ (push M₁ M₂) rewrite sub-comp-coh θ M₁ | sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var new)) M₂ = refl
  sub-comp-coh θ (app W₁ W₂) rewrite sub-pure-coh θ W₁ | sub-pure-coh θ W₂ = refl
  sub-comp-coh θ (var W) rewrite sub-pure-coh θ W = refl
  sub-comp-coh θ (sub M₁ M₂) rewrite sub-comp-coh (sub-ex (sub-wk (wk-wk wk-id) θ) (var new)) M₁ | sub-comp-coh θ M₂ = refl

{-# REWRITE sub-pure-coh #-}
{-# REWRITE sub-comp-coh #-}

mutual
  eqPure : Γ ⊢ᵖ W ≈ W' ∶ X -> ⟦ W ⟧ᵖ ≡ ⟦ W' ⟧ᵖ
  eqPure ≈-refl = refl
  eqPure (≈-sym p) = sym (eqPure p)
  eqPure (≈-trans p q) = Eq.trans (eqPure p) (eqPure q)
  eqPure (lam-cong p) = cong curry (eqComp p)
  eqPure (pair-cong p q) = cong₂ <_,_> (eqPure p) (eqPure q)
  eqPure (pm-cong p q) rewrite eqPure p | eqPure q = refl
  eqPure (unit-eta _) = refl
  eqPure (pm-beta W₁ W₂ W) = refl
  eqPure (pm-eta W₁ W₂) = refl
  eqPure (lam-eta _) = refl

  eqComp : Γ ⊢ᶜ M ≈ M' ∶ X -> ⟦ M ⟧ᶜ ≡ ⟦ M' ⟧ᶜ
  eqComp ≈-refl = refl
  eqComp (≈-sym p) = sym (eqComp p)
  eqComp (≈-trans p q) = Eq.trans (eqComp p) (eqComp q)
  eqComp (return-cong p) rewrite eqPure p = refl
  eqComp (pm-cong p q) rewrite eqPure p | eqComp q = refl
  eqComp (push-cong p q) rewrite eqComp p | eqComp q = refl
  eqComp (app-cong p q) rewrite eqPure p | eqPure q = refl
  eqComp (var-cong p) rewrite eqPure p = refl
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

module TopLevel {R₀ : Ty} {k₀ : ⟦ R₀ ⟧ → R} where

\end{code}
%<*SemEnv>
\begin{code}
  mutual
    ⟦_⟧ᴱ : (W : Env {Z₀ = R₀} Γ) → ⟦ Γ ⟧ˣ
    ⟦ ⋄ ⟧ᴱ = tt
    ⟦ γ · W ⟧ᴱ = ⟦ γ ⟧ᴱ , ⟦ W ⟧ⱽ

    ⟦_⟧ⱽ : (W : Value {Z₀ = R₀} X) → ⟦ X ⟧
    ⟦ unitᵛ ⟧ⱽ = tt
    ⟦ pairᵛ W₁ W₂ ⟧ⱽ = ⟦ W₁ ⟧ⱽ , ⟦ W₂ ⟧ⱽ
    ⟦ cloᵛ M γ ⟧ⱽ = (curry ⟦ M ⟧ᶜ) ⟦ γ ⟧ᴱ
    ⟦ jumpᵛ M γ k ⟧ⱽ = ⟦ M ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ k ⟧ᴷ

    ⟦_⟧ᶜˢ : (k : CStack {Z₀ = R₀} X) → K ⟦ X ⟧ → K ⟦ R₀ ⟧
    ⟦ ◻ ⟧ᶜˢ = idf
    ⟦ < W₁ ； γ₁ >∷ pstack ⟧ᶜˢ = < const ⟦ γ₁ ⟧ᴱ , idf > ； τ ； (⟦ W₁ ⟧ᶜ ♯) ； ⟦ pstack ⟧ᶜˢ

    ⟦_⟧ᴷ : (cs : CStack {Z₀ = R₀} Y) → ⟦ Y ⟧ → R
    ⟦_⟧ᴷ cs y = ⟦ cs ⟧ᶜˢ (η y) k₀
\end{code}
%</SemEnv>
\begin{code}


\end{code}
%<*SemPStack>
\begin{code}

  ⟦_⟧ᵖˢ : (S : PStack {Z₀ = R₀} non-empty Z₁) → ⟦ Z₁ ⟧
  ⟦ ((⭭ W) ∷ ⊠) {𝐛 = ▿} ⟧ᵖˢ = ⟦ W ⟧ⱽ
  ⟦ (⇡ W γ ∷ ⊠) {𝐛 = ▿} ⟧ᵖˢ = ⟦ W ⟧ᵖ ⟦ γ ⟧ᴱ
  ⟦ (⇡ᴾᴹ Wₕₒₗₑ W₂ γ ∷ ⊠) {𝐛 = ▿} ⟧ᵖˢ = ⟦ pm Wₕₒₗₑ W₂ ⟧ᵖ ⟦ γ ⟧ᴱ
  ⟦ (⇡ᴸ Wₕₒₗₑ W₂ γ ∷ ⊠) {𝐛 = ▿} ⟧ᵖˢ = ⟦ pair Wₕₒₗₑ W₂ ⟧ᵖ ⟦ γ ⟧ᴱ
  ⟦ (⇡ᴿ W₁ Wₕₒₗₑ γ ∷ ⊠) {𝐛 = ▿} ⟧ᵖˢ = ⟦ W₁ ⟧ⱽ , ⟦ Wₕₒₗₑ ⟧ᵖ ⟦ γ ⟧ᴱ
  ⟦ ((⭭ W) ∷ ((x ∷ S) {𝐛 = 𝐛})) {𝐛 = ○} ⟧ᵖˢ = ⟦ (x ∷ S) {𝐛 = 𝐛} ⟧ᵖˢ
  ⟦ (⇡ W γ ∷ ((x ∷ S) {𝐛 = 𝐛})) {𝐛 = ○} ⟧ᵖˢ = ⟦ (x ∷ S) {𝐛 = 𝐛} ⟧ᵖˢ
  ⟦ (⇡ᴾᴹ Wₕₒₗₑ W₂ γ ∷ ((x ∷ S) {𝐛 = 𝐛})) {𝐛 = ○} ⟧ᵖˢ = ⟦ (x ∷ S) {𝐛 = 𝐛} ⟧ᵖˢ
  ⟦ (⇡ᴸ Wₕₒₗₑ W₂ γ ∷ ((x ∷ S) {𝐛 = 𝐛})) {𝐛 = ○} ⟧ᵖˢ = ⟦ (x ∷ S) {𝐛 = 𝐛} ⟧ᵖˢ
  ⟦ (⇡ᴿ W₁ Wₕₒₗₑ γ ∷ ((x ∷ S) {𝐛 = 𝐛})) {𝐛 = ○} ⟧ᵖˢ = ⟦ (x ∷ S) {𝐛 = 𝐛} ⟧ᵖˢ

\end{code}
%</SemPStack>

%<*SemPState>
\begin{code}

  ⟦_⟧ᵖꟴ : (S : PState {Z₀ = R₀} Z₁) → ⟦ Z₁ ⟧
  ⟦ ⟨ pstack ⟩ ⟧ᵖꟴ = ⟦ pstack ⟧ᵖˢ

\end{code}
%</SemPState>

%<*SemCState>
\begin{code}

  ⟦_⟧ᶜꟴ : CState {Z₀ = R₀} → R
  ⟦ ⟨ W ╎ k ⟩ ⟧ᶜꟴ = (η ⟦ W ⟧ⱽ) ⟦ k ⟧ᴷ
  ⟦ ⟨ W ╎ γ ╎ k ⟩ ⟧ᶜꟴ = ⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ k ⟧ᴷ

\end{code}
%</SemCState>

%<*SemPartial>
\begin{code}

  ⟦_⟧ᵀ : Partial {Z₀ = R₀} X → ⟦ X ⟧
  ⟦ ⭭ W ⟧ᵀ = ⟦ W ⟧ⱽ
  ⟦ ⇡ W γ ⟧ᵀ = ⟦ W ⟧ᵖ ⟦ γ ⟧ᴱ
  ⟦ ⇡ᴾᴹ Wₕₒₗₑ W₂ γ ⟧ᵀ = ⟦ pm Wₕₒₗₑ W₂ ⟧ᵖ ⟦ γ ⟧ᴱ
  ⟦ ⇡ᴸ Wₕₒₗₑ W₂ γ ⟧ᵀ = ⟦ pair Wₕₒₗₑ W₂ ⟧ᵖ ⟦ γ ⟧ᴱ
  ⟦ ⇡ᴿ W₁ Wₕₒₗₑ γ ⟧ᵀ = ⟦ W₁ ⟧ⱽ , ⟦ Wₕₒₗₑ ⟧ᵖ ⟦ γ ⟧ᴱ

\end{code}
%</SemPartial>
\begin{code}

  lookup-eq : (i : Γ ∋ X) → (γ : Env {Z₀ = R₀} Γ) → ⟦ i ⟧ᵐ ⟦ γ ⟧ᴱ ≡ ⟦ lookup i γ ⟧ⱽ
  lookup-eq new (γ · x) = refl
  lookup-eq (old i) (γ · x) = lookup-eq i γ

  open PureSteps

  data PStackGood : PStack {Z₀ = R₀} non-empty Z₁ → Set where


    ▿ : (W : Partial X) → PStackGood ((W ∷ ⊠) {𝐛 = ▿})

    pm-good :   {b : IsEmpty} {pstack : PStack b Z₁}
              → {Wₕₒₗₑ : Pure Γ (X `× Y)} {W₂ : Pure (Γ ∙ X ∙ Y) Z} {γ : Env Γ} {W : Partial (X `× Y)}
              → {𝐛 : BotEq b Z Z₁}
              → PStackGood (((⇡ᴾᴹ Wₕₒₗₑ W₂ γ) ∷ pstack) {𝐛 = 𝐛})
              → (eq : ⟦ W ⟧ᵀ ≡ ⟦ Wₕₒₗₑ ⟧ᵖ ⟦ γ ⟧ᴱ) → PStackGood ((W ∷ ((⇡ᴾᴹ Wₕₒₗₑ W₂ γ) ∷ pstack) {𝐛 = 𝐛}) {𝐛 = ○})

    lhs-good :   {b : IsEmpty} {pstack : PStack b Z₁}
              → {Wₕₒₗₑ : Pure Γ X} {W₂ : Pure Γ Y} {γ : Env Γ} {W : Partial X}
              → {𝐛 : BotEq b (X `× Y) Z₁}
              → PStackGood (((⇡ᴸ Wₕₒₗₑ W₂ γ) ∷ pstack) {𝐛 = 𝐛})
              → (eq : ⟦ W ⟧ᵀ ≡ ⟦ Wₕₒₗₑ ⟧ᵖ ⟦ γ ⟧ᴱ) → PStackGood ((W ∷ ((⇡ᴸ Wₕₒₗₑ W₂ γ) ∷ pstack) {𝐛 = 𝐛}) {𝐛 = ○})

    rhs-good :   {b : IsEmpty} {pstack : PStack b Z₁}
              → {W₁ : Value X} {Wₕₒₗₑ : Pure Γ Y} {γ : Env Γ} {W : Partial Y}
              → {𝐛 : BotEq b (X `× Y) Z₁}
              → PStackGood (((⇡ᴿ W₁ Wₕₒₗₑ γ) ∷ pstack) {𝐛 = 𝐛})
              → (eq : ⟦ W ⟧ᵀ ≡ ⟦ Wₕₒₗₑ ⟧ᵖ ⟦ γ ⟧ᴱ) → PStackGood ((W ∷ ((⇡ᴿ W₁ Wₕₒₗₑ γ) ∷ pstack) {𝐛 = 𝐛}) {𝐛 = ○})

  data PStateGood : (S : PState {Z₀ = R₀} X) → Set where
      g[_] : {S : PStack {Z₀ = R₀} non-empty Z₁} → PStackGood S → PStateGood ⟨ S ⟩

  lookup-good : (i : Γ ∋ X) → (γ : Env Γ) → ⟦ lookup i γ ⟧ⱽ ≡ ⟦ i ⟧ᵐ ⟦ γ ⟧ᴱ
  lookup-good new (γ · x) = refl
  lookup-good (old i) (γ · x) = lookup-good i γ

  valstate-good : {S S' : PState {Z₀ = R₀} X} → PStateGood S → S →ᵖ S' → PStateGood S'
  valstate-good g[ ▿ W ] lookup→ = g[ ▿ (⭭ _) ]
  valstate-good g[ ▿ W ] lam→ = g[ ▿ (⭭ cloᵛ _ _) ]
  valstate-good g[ ▿ W ] pair→ = g[ lhs-good (▿ (⇡ᴸ _ _ _)) refl ]
  valstate-good g[ ▿ W ] pmᵖ→ = g[ pm-good (▿ (⇡ᴾᴹ _ _ _)) refl ]
  valstate-good g[ ▿ W ] unit→ = g[ ▿ (⭭ unitᵛ) ]
  valstate-good g[ pm-good g eq ] (lookup→ {x = x} {γ = γ}) = g[ (pm-good g (trans (lookup-good x γ) eq)) ]
  valstate-good g[ pm-good x eq ] pair→ = g[ lhs-good (pm-good x eq) refl ]
  valstate-good g[ pm-good x eq ] pmᵖ→ = g[ pm-good (pm-good x eq) refl ]
  valstate-good g[ lhs-good g eq ] (lookup→ {x = x} {γ = γ}) = g[ (lhs-good g (trans (lookup-good x γ) eq)) ]
  valstate-good g[ lhs-good x eq ] lam→ = g[ lhs-good x eq ]
  valstate-good g[ lhs-good x eq ] pair→ = g[ lhs-good (lhs-good x eq) refl ]
  valstate-good g[ lhs-good x eq ] pmᵖ→ = g[ pm-good (lhs-good x eq) refl ]
  valstate-good g[ lhs-good x eq ] unit→ = g[ lhs-good x eq ]
  valstate-good g[ rhs-good g eq ] (lookup→ {x = x} {γ = γ}) = g[ (rhs-good g (trans (lookup-good x γ) eq)) ]
  valstate-good g[ rhs-good x eq ] lam→ = g[ rhs-good x eq ]
  valstate-good g[ rhs-good x eq ] pair→ = g[ lhs-good (rhs-good x eq) refl ]
  valstate-good g[ rhs-good x eq ] pmᵖ→ = g[ pm-good (rhs-good x eq) refl ]
  valstate-good g[ rhs-good x eq ] unit→ = g[ rhs-good x eq ]
  valstate-good g[ pm-good (▿ W) eq ] pair∷pm→ = g[ ▿ (⇡ _ (_ · _ · _)) ]
  valstate-good g[ pm-good {Wₕₒₗₑ = Wₕₒₗₑ} {W₂ = W₂} {γ = γ} (pm-good {Wₕₒₗₑ = Wₕₒₗₑ'} {γ = γ'} x eq₁) eq ] (pair∷pm→ {Ẇ₁ = Ẇ₁} {Ẇ₂ = Ẇ₂}) =
    g[ (pm-good x ((⟦ W₂ ⟧ᵖ ((⟦ γ ⟧ᴱ , ⟦ Ẇ₁ ⟧ⱽ) , ⟦ Ẇ₂ ⟧ⱽ) ≡⟨ cong (λ x → ⟦ W₂ ⟧ᵖ (assocl (⟦ γ ⟧ᴱ , x))) eq ⟩ ⟦ W₂ ⟧ᵖ (assocl (⟦ γ ⟧ᴱ , ⟦ Wₕₒₗₑ ⟧ᵖ ⟦ γ ⟧ᴱ)) ≡⟨ refl ⟩ ⟦ ⇡ᴾᴹ Wₕₒₗₑ W₂ γ ⟧ᵀ ≡⟨ eq₁ ⟩ ⟦ Wₕₒₗₑ' ⟧ᵖ ⟦ γ' ⟧ᴱ ∎))) ]
  valstate-good g[ pm-good {Wₕₒₗₑ = Wₕₒₗₑ} {W₂ = W₂} {γ = γ} (lhs-good {Wₕₒₗₑ = Wₕₒₗₑ'} {γ = γ'} x eq₁) eq ] (pair∷pm→ {Ẇ₁ = Ẇ₁} {Ẇ₂ = Ẇ₂}) =
    g[ (lhs-good x ((⟦ W₂ ⟧ᵖ ((⟦ γ ⟧ᴱ , ⟦ Ẇ₁ ⟧ⱽ) , ⟦ Ẇ₂ ⟧ⱽ) ≡⟨ cong (λ x → ⟦ W₂ ⟧ᵖ (assocl (⟦ γ ⟧ᴱ , x))) eq ⟩ ⟦ W₂ ⟧ᵖ (assocl (⟦ γ ⟧ᴱ , ⟦ Wₕₒₗₑ ⟧ᵖ ⟦ γ ⟧ᴱ)) ≡⟨ refl ⟩ ⟦ ⇡ᴾᴹ Wₕₒₗₑ W₂ γ ⟧ᵀ ≡⟨ eq₁ ⟩ ⟦ Wₕₒₗₑ' ⟧ᵖ ⟦ γ' ⟧ᴱ ∎))) ]
  valstate-good g[ pm-good {Wₕₒₗₑ = Wₕₒₗₑ} {W₂ = W₂} {γ = γ} (rhs-good {Wₕₒₗₑ = Wₕₒₗₑ'} {γ = γ'} x eq₁) eq ] (pair∷pm→ {Ẇ₁ = Ẇ₁} {Ẇ₂ = Ẇ₂}) =
    g[ (rhs-good x ((⟦ W₂ ⟧ᵖ ((⟦ γ ⟧ᴱ , ⟦ Ẇ₁ ⟧ⱽ) , ⟦ Ẇ₂ ⟧ⱽ) ≡⟨ cong (λ x → ⟦ W₂ ⟧ᵖ (assocl (⟦ γ ⟧ᴱ , x))) eq ⟩ ⟦ W₂ ⟧ᵖ (assocl (⟦ γ ⟧ᴱ , ⟦ Wₕₒₗₑ ⟧ᵖ ⟦ γ ⟧ᴱ)) ≡⟨ refl ⟩ ⟦ ⇡ᴾᴹ Wₕₒₗₑ W₂ γ ⟧ᵀ ≡⟨ eq₁ ⟩ ⟦ Wₕₒₗₑ' ⟧ᵖ ⟦ γ' ⟧ᴱ ∎))) ]
  valstate-good g[ lhs-good (▿ W) eq ] W∷l→ = g[ rhs-good (▿ (⇡ᴿ _ _ _)) refl ]
  valstate-good g[ lhs-good {Wₕₒₗₑ = Wₕₒₗₑ} {W₂ = W₂} {γ = γ} (pm-good {Wₕₒₗₑ = Wₕₒₗₑ'} {γ = γ'} x eq₁) eq ] (W∷l→ {Ẇ₁ = Ẇ₁}) = g[ (rhs-good (pm-good x ((⟦ Ẇ₁ ⟧ⱽ , ⟦ W₂ ⟧ᵖ ⟦ γ ⟧ᴱ) ≡⟨ cong (λ x → x , ⟦ W₂ ⟧ᵖ ⟦ γ ⟧ᴱ) eq ⟩ ⟦ ⇡ᴸ Wₕₒₗₑ W₂ γ ⟧ᵀ ≡⟨ eq₁ ⟩ ⟦ Wₕₒₗₑ' ⟧ᵖ ⟦ γ' ⟧ᴱ ∎)) refl) ]
  valstate-good g[ lhs-good {Wₕₒₗₑ = Wₕₒₗₑ} {W₂ = W₂} {γ = γ} (lhs-good {Wₕₒₗₑ = Wₕₒₗₑ'} {W₂ = W₂'} {γ = γ'} x eq₁) eq ] (W∷l→ {Ẇ₁ = Ẇ₁}) = g[ (rhs-good (lhs-good x ((⟦ Ẇ₁ ⟧ⱽ , ⟦ W₂ ⟧ᵖ ⟦ γ ⟧ᴱ) ≡⟨ cong (λ x → x , ⟦ W₂ ⟧ᵖ ⟦ γ ⟧ᴱ) eq ⟩ ⟦ ⇡ᴸ Wₕₒₗₑ W₂ γ ⟧ᵀ ≡⟨ eq₁ ⟩ ⟦ Wₕₒₗₑ' ⟧ᵖ ⟦ γ' ⟧ᴱ ∎)) refl) ]
  valstate-good g[ lhs-good {Wₕₒₗₑ = Wₕₒₗₑ} {W₂ = W₂} {γ = γ} (rhs-good {W₁ = W₁} {Wₕₒₗₑ = Wₕₒₗₑ'} {γ = γ'} x eq₁) eq ] (W∷l→ {Ẇ₁ = Ẇ₁}) = g[ (rhs-good (rhs-good x ((⟦ Ẇ₁ ⟧ⱽ , ⟦ W₂ ⟧ᵖ ⟦ γ ⟧ᴱ) ≡⟨ cong (λ x → x , ⟦ W₂ ⟧ᵖ ⟦ γ ⟧ᴱ) eq ⟩ ⟦ ⇡ᴸ Wₕₒₗₑ W₂ γ ⟧ᵀ ≡⟨ eq₁ ⟩ ⟦ Wₕₒₗₑ' ⟧ᵖ ⟦ γ' ⟧ᴱ ∎)) refl) ]

  valstate-good g[ rhs-good {W₁ = W₁} {Wₕₒₗₑ = Wₕₒₗₑ} {γ = γ} (▿ W) eq ] W∷r→ = g[ ▿ (⭭ pairᵛ _ _) ]
  valstate-good g[ rhs-good {W₁ = W₁} {Wₕₒₗₑ = Wₕₒₗₑ} {γ = γ} (pm-good {Wₕₒₗₑ = Wₕₒₗₑ'} {γ = γ'} x eq₁) eq ] (W∷r→ {Ẇ₂ = Ẇ₂}) = g[ (pm-good x (trans (cong (λ x → ⟦ W₁ ⟧ⱽ , x) eq) eq₁)) ]
  valstate-good g[ rhs-good {W₁ = W₁} {Wₕₒₗₑ = Wₕₒₗₑ} {γ = γ} (lhs-good {Wₕₒₗₑ = Wₕₒₗₑ'} {W₂ = W₂} {γ = γ'} x eq₁) eq ] (W∷r→ {Ẇ₂ = Ẇ₂}) = g[ (lhs-good x (trans (cong (λ x → ⟦ W₁ ⟧ⱽ , x) eq) eq₁)) ]
  valstate-good g[ rhs-good {W₁ = W₁} {Wₕₒₗₑ = Wₕₒₗₑ} {γ = γ} (rhs-good {W₁ = W₁'} {Wₕₒₗₑ = Wₕₒₗₑ'} {γ = γ'} x eq₁) eq ] (W∷r→ {Ẇ₂ = Ẇ₂}) = g[ (rhs-good x (trans (cong (λ x → ⟦ W₁ ⟧ⱽ , x) eq) eq₁)) ]

  valstate-eq : {S S' : PState {Z₀ = R₀} X} → PStateGood S → S →ᵖ S' → ⟦ S ⟧ᵖꟴ ≡ ⟦ S' ⟧ᵖꟴ
  valstate-eq {S = S} {S' = S'} good (lookup→ {x = x} {γ = γ} {pstack = ⊠} {𝐛 = ▿}) = lookup-eq x γ
  valstate-eq {S = S} {S' = S'} good (lookup→ {pstack = (x ∷ pstack) {𝐛 = 𝐛}} {𝐛 = ○}) = refl
  valstate-eq {S = S} {S' = S'} good (lam→ {pstack = ⊠} {𝐛 = ▿}) = refl
  valstate-eq {S = S} {S' = S'} good (lam→ {pstack = (x ∷ pstack) {𝐛 = 𝐛}} {𝐛 = ○}) = refl
  valstate-eq {S = S} {S' = S'} good (pair→ {pstack = ⊠} {𝐛 = ▿}) = refl
  valstate-eq {S = S} {S' = S'} good (pair→ {pstack = (x ∷ pstack) {𝐛 = 𝐛}} {𝐛 = ○}) = refl
  valstate-eq {S = S} {S' = S'} good (pmᵖ→ {pstack = ⊠} {𝐛 = ▿}) = refl
  valstate-eq {S = S} {S' = S'} good (pmᵖ→ {pstack = (x ∷ pstack) {𝐛 = 𝐛}} {𝐛 = ○}) = refl
  valstate-eq {S = S} {S' = S'} good (unit→ {pstack = ⊠} {𝐛 = ▿}) = refl
  valstate-eq {S = S} {S' = S'} good (unit→ {pstack = (x ∷ pstack) {𝐛 = 𝐛}} {𝐛 = ○}) = refl
  valstate-eq {S = S} {S' = S'} g[ lhs-good {W₂ = W₂} {γ = γ} x eq ] (W∷l→ {pstack = ⊠} {𝐛 = ▿}) = cong (λ x → x , ⟦ W₂ ⟧ᵖ ⟦ γ ⟧ᴱ) (sym eq)
  valstate-eq {S = S} {S' = S'} good (W∷l→ {pstack = (x ∷ pstack) {𝐛 = 𝐛}} {𝐛 = ○}) = refl
  valstate-eq {S = S} {S' = S'} g[ rhs-good {W₁ = W₁} {γ = γ} x eq ] (W∷r→ {pstack = ⊠} {𝐛 = ▿}) = cong (λ x → ⟦ W₁ ⟧ⱽ , x) (sym eq)
  valstate-eq {S = S} {S' = S'} good (W∷r→ {pstack = (x ∷ pstack) {𝐛 = 𝐛}} {𝐛 = ○}) = refl
  valstate-eq {S = S} {S' = S'} g[ pm-good {Wₕₒₗₑ = Wₕₒₗₑ} {W₂ = W₂} x eq ] (pair∷pm→ {γ = γ} {pstack = ⊠} {𝐛 = ▿}) = cong (λ x → ⟦ W₂ ⟧ᵖ (assocl (⟦ γ ⟧ᴱ , x))) (sym eq)
  valstate-eq {S = S} {S' = S'} good (pair∷pm→ {pstack = (x ∷ pstack) {𝐛 = 𝐛}} {𝐛 = ○}) = refl

  valstate-trans-eq : {S S' : PState {Z₀ = R₀} X} → PStateGood S → S ↠ᵛ S' → ⟦ S ⟧ᵖꟴ ≡ ⟦ S' ⟧ᵖꟴ
  valstate-trans-eq good (S →ᵖ⟨ S→ᵖS' ⟩．) = valstate-eq good S→ᵖS'
  valstate-trans-eq good (S →ᵖ⟨ S→ᵖS' ⟩ S'↠ᵛS'') = trans (valstate-eq good S→ᵖS') (valstate-trans-eq (valstate-good good S→ᵖS') S'↠ᵛS'')

  value-machine-correct : (W : Pure Γ X) → (γ : Env {Z₀ = R₀} Γ) → ⟦ W ⟧ᵖ ⟦ γ ⟧ᴱ ≡ ⟦ result (normalise-pure W γ) ⟧ⱽ
  value-machine-correct W γ = valstate-trans-eq g[ ▿ (⇡ W γ) ] (steps (normalise-pure W γ))

  push-eq : (cs : CStack {Z₀ = R₀} X) → (KX : K ⟦ X ⟧) → ⟦ cs ⟧ᶜˢ (λ k → KX k) k₀ ≡ KX (λ y → ⟦ cs ⟧ᶜˢ (λ k → k y) k₀)
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

  jump-eq : (W : Value `L) → ⟦ W ⟧ⱽ ≡ ⟦ jump-to-state W ⟧ᶜꟴ
  jump-eq (jumpᵛ _ _ _) = refl

  jump-eq' : (W : Pure Γ `L) → (γ : Env {Z₀ = R₀} Γ) → ⟦ result (normalise-pure W γ) ⟧ⱽ ≡ ⟦ jump-to-state (result (normalise-pure W γ)) ⟧ᶜꟴ
  jump-eq' W γ = jump-eq (result (normalise-pure W γ))

  clo-eq : (W : Value (X `⇒ Y)) → (T : ⟦ X ⟧) → (E : ⟦ proj₁ (clo-to-comp W) ⟧ˣ) → (eq : E ≡ ⟦ proj₂ (proj₂ (clo-to-comp W)) ⟧ᴱ) → ⟦ W ⟧ⱽ T ≡ ⟦ proj₁ (proj₂ (clo-to-comp W)) ⟧ᶜ (E , T)
  clo-eq (cloᵛ M γ) T E eq = cong (λ x → curry ⟦ M ⟧ᶜ x T) (sym eq)

  proj₁-val-eq : (W : Value (X `× Y)) → proj₁ ⟦ W ⟧ⱽ ≡ ⟦ proj₁-val W ⟧ⱽ
  proj₁-val-eq (pairᵛ W₁ W₂) = refl

  proj₂-val-eq : (W : Value (X `× Y)) → proj₂ ⟦ W ⟧ⱽ ≡ ⟦ proj₂-val W ⟧ⱽ
  proj₂-val-eq (pairᵛ W₁ W₂) = refl

  mutual
    proj₂-val-eq' : (W : Pure Γ (X `× Y)) → (γ : Env {Z₀ = R₀} Γ) → (proj₂ (⟦ W ⟧ᵖ ⟦ γ ⟧ᴱ)) ≡ ⟦ proj₂-val (result (normalise-pure W γ)) ⟧ⱽ
    proj₂-val-eq' (var new) (γ · W) = proj₂-val-eq W
    proj₂-val-eq' (var (old i)) (γ · W) = proj₂-val-eq' (var i) γ
    proj₂-val-eq' (pair W₁ W₂) γ = value-machine-correct W₂ γ
    proj₂-val-eq' (pm W₁ W₂) γ =
      let
        eq₁ = proj₁-val-eq' W₁ γ
        eq₂ = proj₂-val-eq' W₁ γ
        eq = proj₂-val-eq' W₂ (γ · proj₁-val (result (normalise-pure W₁ γ)) · proj₂-val (result (normalise-pure W₁ γ)))
      in
      proj₂ (⟦ W₂ ⟧ᵖ ((⟦ γ ⟧ᴱ , proj₁ (⟦ W₁ ⟧ᵖ ⟦ γ ⟧ᴱ)) , proj₂ (⟦ W₁ ⟧ᵖ ⟦ γ ⟧ᴱ)))
      ≡⟨ cong₂ (λ x y → proj₂ (⟦ W₂ ⟧ᵖ ((⟦ γ ⟧ᴱ , x) , y))) eq₁ eq₂ ⟩
      proj₂ (⟦ W₂ ⟧ᵖ ((⟦ γ ⟧ᴱ , ⟦ proj₁-val (result (normalise-pure W₁ γ)) ⟧ⱽ) , ⟦ proj₂-val (result (normalise-pure W₁ γ)) ⟧ⱽ))
      ≡⟨ eq ⟩
      ⟦ proj₂-val (result (normalise-pure W₂ (γ · proj₁-val (result (normalise-pure W₁ γ)) · proj₂-val (result (normalise-pure W₁ γ))))) ⟧ⱽ ∎

    proj₁-val-eq' : (W : Pure Γ (X `× Y)) → (γ : Env {Z₀ = R₀} Γ) → (proj₁ (⟦ W ⟧ᵖ ⟦ γ ⟧ᴱ)) ≡ ⟦ proj₁-val (result (normalise-pure W γ)) ⟧ⱽ
    proj₁-val-eq' (var new) (γ · W) = proj₁-val-eq W
    proj₁-val-eq' (var (old i)) (γ · W) = proj₁-val-eq' (var i) γ
    proj₁-val-eq' (pair W₁ W₂) γ = value-machine-correct W₁ γ
    proj₁-val-eq' (pm W₁ W₂) γ =
      let
        eq₁ = proj₁-val-eq' W₁ γ
        eq₂ = proj₂-val-eq' W₁ γ
        eq = proj₁-val-eq' W₂ (γ · proj₁-val (result (normalise-pure W₁ γ)) · proj₂-val (result (normalise-pure W₁ γ)))
      in
      proj₁ (⟦ W₂ ⟧ᵖ ((⟦ γ ⟧ᴱ , proj₁ (⟦ W₁ ⟧ᵖ ⟦ γ ⟧ᴱ)) , proj₂ (⟦ W₁ ⟧ᵖ ⟦ γ ⟧ᴱ)))
      ≡⟨ cong₂ (λ x y → proj₁ (⟦ W₂ ⟧ᵖ ((⟦ γ ⟧ᴱ , x) , y))) eq₁ eq₂ ⟩
      proj₁ (⟦ W₂ ⟧ᵖ ((⟦ γ ⟧ᴱ , ⟦ proj₁-val (result (normalise-pure W₁ γ)) ⟧ⱽ) , ⟦ proj₂-val (result (normalise-pure W₁ γ)) ⟧ⱽ))
      ≡⟨ eq ⟩
      ⟦ proj₁-val (result (normalise-pure W₂ (γ · proj₁-val (result (normalise-pure W₁ γ)) · proj₂-val (result (normalise-pure W₁ γ))))) ⟧ⱽ ∎


  compstate-eq : {S S' : CState {Z₀ = R₀}} → S →ᶜ S' → ⟦ S ⟧ᶜꟴ ≡ ⟦ S' ⟧ᶜꟴ
  compstate-eq (pure→ {W = W} {γ = γ} {cstack = cstack}) =
    let
      eq = value-machine-correct W γ
    in
    η (⟦ W ⟧ᵖ ⟦ γ ⟧ᴱ) ⟦ cstack ⟧ᴷ ≡⟨ cong (λ x → η x ⟦ cstack ⟧ᴷ) eq ⟩ η ⟦ result (normalise-pure W γ) ⟧ⱽ ⟦ cstack ⟧ᴷ ∎
  compstate-eq (return→ {Ẇ = Ẇ} {M = M} {γ = γ} {cstack = cstack}) =
    let
      eq = push-eq cstack (⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , ⟦ Ẇ ⟧ⱽ))
    in
      η ⟦ Ẇ ⟧ⱽ ⟦ < M ； γ >∷ cstack ⟧ᴷ
    ≡⟨ refl ⟩
     ⟦ cstack ⟧ᶜˢ (λ k₁ → ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , ⟦ Ẇ ⟧ⱽ) k₁) k₀
    ≡⟨ eq ⟩
     ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , ⟦ Ẇ ⟧ⱽ) (λ y → ⟦ cstack ⟧ᶜˢ (λ k₁ → k₁ y) k₀)
    ≡⟨ refl ⟩
     ⟦ M ⟧ᶜ (⟦ γ ⟧ᴱ , ⟦ Ẇ ⟧ⱽ) ⟦ cstack ⟧ᴷ ∎
  compstate-eq (push→ {M₁ = M₁} {M₂ = M₂} {γ = γ} {cstack = cstack}) =
    (< idf , ⟦ M₁ ⟧ᶜ > ； τ ； ⟦ M₂ ⟧ᶜ ♯) ⟦ γ ⟧ᴱ ⟦ cstack ⟧ᴷ
     ≡⟨ refl ⟩
     ⟦ M₁ ⟧ᶜ ⟦ γ ⟧ᴱ (λ z → ⟦ M₂ ⟧ᶜ (⟦ γ ⟧ᴱ , z) (λ y → ⟦ cstack ⟧ᶜˢ (λ k₁ → k₁ y) k₀))
     ≡⟨ cong (⟦ M₁ ⟧ᶜ ⟦ γ ⟧ᴱ) (extensionality (λ x → sym (push-eq cstack (⟦ M₂ ⟧ᶜ (⟦ γ ⟧ᴱ , x))))) ⟩
     ⟦ M₁ ⟧ᶜ ⟦ γ ⟧ᴱ (λ y → ⟦ cstack ⟧ᶜˢ (λ k₁ → ⟦ M₂ ⟧ᶜ (⟦ γ ⟧ᴱ , y) k₁) k₀)
     ≡⟨ refl ⟩
     ⟦ M₁ ⟧ᶜ ⟦ γ ⟧ᴱ ⟦ < M₂ ； γ >∷ cstack ⟧ᴷ ∎
  compstate-eq sub→ = refl
  compstate-eq (var→ {W = W} {γ = γ} {cstack = cstack}) =
    let
      eq = value-machine-correct W γ
    in
    (⟦ W ⟧ᵖ ； varK) ⟦ γ ⟧ᴱ ⟦ cstack ⟧ᴷ ≡⟨ refl ⟩ ⟦ W ⟧ᵖ ⟦ γ ⟧ᴱ ≡⟨ eq ⟩ ⟦ result (normalise-pure W γ) ⟧ⱽ ≡⟨ jump-eq' W γ ⟩ ⟦ jump-to-state (result (normalise-pure W γ)) ⟧ᶜꟴ ∎
  compstate-eq (pmᶜ→ {W = W} {γ = γ} {M = M} {cstack = cstack}) =
    (< idf , ⟦ W ⟧ᵖ > ； assocl ； ⟦ M ⟧ᶜ) ⟦ γ ⟧ᴱ ⟦ cstack ⟧ᴷ
    ≡⟨ refl ⟩
      ⟦ M ⟧ᶜ (assocl ( ⟦ γ ⟧ᴱ , ⟦ W ⟧ᵖ ⟦ γ ⟧ᴱ )) ⟦ cstack ⟧ᴷ
    ≡⟨ cong (λ x → ⟦ M ⟧ᶜ (assocl ( ⟦ γ ⟧ᴱ , x )) ⟦ cstack ⟧ᴷ) (cong₂ _,_ (proj₁-val-eq' W γ) (proj₂-val-eq' W γ)) ⟩
     ⟦ M ⟧ᶜ ((⟦ γ ⟧ᴱ , ⟦ proj₁-val (result (normalise-pure W γ)) ⟧ⱽ) , ⟦ proj₂-val (result (normalise-pure W γ)) ⟧ⱽ) ⟦ cstack ⟧ᴷ ∎
  compstate-eq (app→ {W₁ = W₁} {W₂ = W₂} {γ = γ} {cstack = cstack}) =
    cong (λ x → x (λ y → ⟦ cstack ⟧ᶜˢ (λ cstack₁ → cstack₁ y) k₀))
      (⟦ W₁ ⟧ᵖ ⟦ γ ⟧ᴱ (⟦ W₂ ⟧ᵖ ⟦ γ ⟧ᴱ)
      ≡⟨ cong (λ x → x (⟦ W₂ ⟧ᵖ ⟦ γ ⟧ᴱ)) (value-machine-correct W₁ γ) ⟩
      ⟦ result (normalise-pure W₁ γ) ⟧ⱽ (⟦ W₂ ⟧ᵖ ⟦ γ ⟧ᴱ)
      ≡⟨ clo-eq (result (normalise-pure W₁ γ)) (⟦ W₂ ⟧ᵖ ⟦ γ ⟧ᴱ) ⟦ proj₂ (proj₂ (clo-to-comp (result (normalise-pure W₁ γ)))) ⟧ᴱ refl ⟩
      ⟦ proj₁ (proj₂ (clo-to-comp (result (normalise-pure W₁ γ)))) ⟧ᶜ (⟦ proj₂ (proj₂ (clo-to-comp (result (normalise-pure W₁ γ)))) ⟧ᴱ , (⟦ W₂ ⟧ᵖ ⟦ γ ⟧ᴱ))
      ≡⟨ refl ⟩
      curry ⟦ proj₁ (proj₂ (clo-to-comp (result (normalise-pure W₁ γ)))) ⟧ᶜ ⟦ proj₂ (proj₂ (clo-to-comp (result (normalise-pure W₁ γ)))) ⟧ᴱ (⟦ W₂ ⟧ᵖ ⟦ γ ⟧ᴱ)
      ≡⟨ cong (λ x → curry ⟦ proj₁ (proj₂ (clo-to-comp (result (normalise-pure W₁ γ)))) ⟧ᶜ ⟦ proj₂ (proj₂ (clo-to-comp (result (normalise-pure W₁ γ)))) ⟧ᴱ x) (value-machine-correct W₂ γ) ⟩
      curry ⟦ proj₁ (proj₂ (clo-to-comp (result (normalise-pure W₁ γ)))) ⟧ᶜ ⟦ proj₂ (proj₂ (clo-to-comp (result (normalise-pure W₁ γ)))) ⟧ᴱ ⟦ result (normalise-pure W₂ γ) ⟧ⱽ
      ≡⟨ cong (λ x → curry ⟦ proj₁ (proj₂ (clo-to-comp (result (normalise-pure W₁ γ)))) ⟧ᶜ x ⟦ result (normalise-pure W₂ γ) ⟧ⱽ) refl ⟩
      ⟦ proj₁ (proj₂ (clo-to-comp (result (normalise-pure W₁ γ)))) ⟧ᶜ (⟦ proj₂ (proj₂ (clo-to-comp (result (normalise-pure W₁ γ)))) ⟧ᴱ , ⟦ result (normalise-pure W₂ γ) ⟧ⱽ) ∎ )

  compstate-eq* : {S S' : CState {Z₀ = R₀}} → S →ᶜ* S' → ⟦ S ⟧ᶜꟴ ≡ ⟦ S' ⟧ᶜꟴ
  compstate-eq* (S ◼) = refl
  compstate-eq* (S ~>⟨ S→S' ⟩ S'→*S'') = trans (compstate-eq S→S') (compstate-eq* S'→*S'')

  comp-machine-transitions-correct : (M : Comp ε R₀) → ⟦ ⟨ M ╎ ⋄ ╎ ◻ ⟩ ⟧ᶜꟴ ≡ ⟦ proj₁ (eval M) ⟧ᶜꟴ
  comp-machine-transitions-correct M = compstate-eq* (proj₁ (proj₂ (proj₂ (proj₂ (eval M)))))

\end{code}
%<*SubVarCorrect>
\begin{code}

  comp-machine-correct : (M : Comp ε R₀) → ⟦ M ⟧ᶜ tt k₀ ≡ k₀ ⟦ (proj₁ (proj₂ (eval M))) ⟧ⱽ

\end{code}
%</SubVarCorrect>
\begin{code}

  comp-machine-correct M =
    let
      eq = comp-machine-transitions-correct M
      hs = proj₂ (halting-state (proj₁ (eval M)) (proj₁ (proj₂ (proj₂ (eval M)))))
    in
      ⟦ M ⟧ᶜ tt k₀
    ≡⟨ eq ⟩
      ⟦ proj₁ (eval M) ⟧ᶜꟴ
    ≡⟨ cong ⟦_⟧ᶜꟴ hs ⟩
      ⟦ ⟨ proj₁ (halting-state (proj₁ (eval M)) (proj₁ (proj₂ (proj₂ (eval M))))) ╎ ◻ ⟩ ⟧ᶜꟴ
    ≡⟨ refl ⟩
      k₀ ⟦ proj₁ (halting-state (proj₁ (eval M)) (proj₁ (proj₂ (proj₂ (eval M))))) ⟧ⱽ
    ≡⟨ cong (λ x → k₀ ⟦ x ⟧ⱽ) (sym (proj₂ (proj₂ (proj₂ (proj₂ (eval M)))))) ⟩
      k₀ ⟦ proj₁ (proj₂ (eval M)) ⟧ⱽ ∎

\end{code}
