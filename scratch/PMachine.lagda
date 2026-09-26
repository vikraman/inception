\begin{code}
{-# OPTIONS --no-postfix-projections #-}

open import Inception.Sub.Syntax using (Ty)

module scratch.PMachine (ℛ : Ty) where

open import Inception.Prelude
open import Inception.Sub.Machine ℛ
open import Inception.Sub.Syntax

open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Unit using (⊤; tt)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning

--------------------------------------------------------------------------

infix  20 ⭭_
infix  19 _∷_
infixr 17 _→ᵖ⟨_⟩．
infixr 15 _→ᵖ⟨_⟩_
infix  15 _→ᵖ_
infixr 10 _⨾_

--------------------------------------------------------------------------
-- machine for values

\end{code}
%<*Partial>
\begin{code}

data Partial : (X : Ty) → Set where

    ⭭_ :   (𝐖 : MVal X)
           ----------------------
           → Partial X

    ⇡ :    (W : Γ ⊢ᵛ X) → (MEnv Γ)
           --------------------------------
           → Partial X

    ⇡ᴸ :   (V : Γ ⊢ᵛ X) → (W : Γ ⊢ᵛ Y) → (MEnv Γ)
           ----------------------------------------------------
           → Partial (X `× Y)

    ⇡ᴿ :   (𝐕 : MVal X) → (W : Γ ⊢ᵛ Y) → (MEnv Γ)
           ------------------------------------------------------------
           → Partial (X `× Y)

\end{code}
%</Partial>
\begin{code}

\end{code}
%<*PStates>
\begin{code}

data IsEmpty : Set where

    non-empty :
                 -------
                 IsEmpty

    empty :
                 -------
                 IsEmpty

private variable
    ∅? : IsEmpty

data BotEq : IsEmpty → Ty → Ty → Set where

    ▿ :
         ---------------
         BotEq empty X X

    ○ :
         -------------------
         BotEq non-empty X Y

data PStack : IsEmpty → Ty → Set where

    ⊠ :
           -----------------------
           PStack empty Z

    _∷_ :  Partial X → (K : PStack ∅? Z)
           → {𝐛 : BotEq ∅? X Z}
           --------------------------------------------------
           → PStack non-empty Z


data PState : Ty → Set where

    ⟨_⟩ :  PStack non-empty Z
           ---------------------------
           → PState Z

\end{code}
%</PStates>
\begin{code}

_⧺_ : PStack ∅? Z → PStack non-empty X → PStack non-empty X
⊠ ⧺ K = K
(W ∷ K) ⧺ L = (W ∷ (K ⧺ L)) {𝐛 = ○}

_⧻_ : (σ : PState Z) → PStack non-empty X → PState X
⟨ σ ⟩ ⧻ K = ⟨ σ ⧺ K ⟩

\end{code}
%<*PTrans>
\begin{code}

data _→ᵖ_ {Z : Ty} :
        PState Z → PState Z → Set where

    lookup→ :   {i : Γ ∋ X} {γ : MEnv Γ}
                {K : PStack ∅? Z} {𝐛 : BotEq ∅? X Z}
                -------------------------------------------------
                →  ⟨ (⇡ (var i) γ ∷ K) {𝐛 = 𝐛} ⟩
                   →ᵖ ⟨ (⭭ (lookup i γ) ∷ K) {𝐛 = 𝐛} ⟩

    lam→ :      {M : (Γ ∙ X) ⊢ᶜ Y} {γ  : MEnv Γ}
                {K : PStack ∅? Z} {𝐛 : BotEq ∅? (X `⇒ Y) Z}
                --------------------------------------------------------
                →  ⟨ (⇡ (lam M) γ ∷ K) {𝐛 = 𝐛} ⟩
                   →ᵖ ⟨ (⭭ (cloᵛ M γ) ∷ K) {𝐛 = 𝐛} ⟩

    pair→ :     {γ : MEnv Γ} {V : Γ ⊢ᵛ X₁} {W : Γ ⊢ᵛ Y₁}
                {K : PStack ∅? Z} {𝐛 : BotEq ∅? (X₁ `× Y₁) Z}
                ---------------------------------------------------------
                →  ⟨ (⇡ (pair V W) γ ∷ K) {𝐛 = 𝐛} ⟩
                   →ᵖ ⟨ (⇡ V γ ∷ ((⇡ᴸ V W γ ∷ K) {𝐛 = 𝐛})) {𝐛 = ○} ⟩

    unit→ :     {γ  : MEnv Γ}
                {K : PStack ∅? Z} {𝐛 : BotEq ∅? `𝟙 Z}
                ----------------------------------------------------
                →  ⟨ (⇡ unit γ ∷ K) {𝐛 = 𝐛} ⟩
                   →ᵖ ⟨ (⭭ unitᵛ ∷ K) {𝐛 = 𝐛} ⟩

    W∷l→ :      {γ : MEnv Γ} {𝐕 : MVal X₁} {V : Γ ⊢ᵛ X₁}
                {W : Γ ⊢ᵛ Y₁} {K : PStack ∅? Z}
                {𝐛 : BotEq ∅? (X₁ `× Y₁) Z}
                ------------------------------------------------------
                →  ⟨ (⭭ 𝐕 ∷ ((⇡ᴸ V W γ ∷ K) {𝐛 = 𝐛})) {𝐛 = ○} ⟩
                   →ᵖ ⟨ (⇡ W γ ∷ ((⇡ᴿ 𝐕 W γ ∷ K) {𝐛 = 𝐛})) {𝐛 = ○} ⟩

    W∷r→ :      {γ : MEnv Γ} {𝐕 : MVal X₁} {𝐖 : MVal Y₁} {W : Γ ⊢ᵛ Y₁}
                {K : PStack ∅? Z} {𝐛 : BotEq ∅? (X₁ `× Y₁) Z}
                -----------------------------------------------------------------
                →  ⟨ (⭭ 𝐖 ∷ ((⇡ᴿ 𝐕 W γ ∷ K) {𝐛 = 𝐛})) {𝐛 = ○} ⟩
                   →ᵖ ⟨ (⭭ pairᵛ 𝐕 𝐖 ∷ K) {𝐛 = 𝐛} ⟩

\end{code}
%</PTrans>
\begin{code}

data _↠ᵛ_ {Z : Ty} : PState Z → PState Z → Set where

  _→ᵖ⟨_⟩． : (σ : PState Z) → {σ₁ : PState Z} → (laststep : σ →ᵖ σ₁) → σ ↠ᵛ σ₁

  _→ᵖ⟨_⟩_ : (σ : PState Z) → {σ₁ σ₂ : PState Z} → σ →ᵖ σ₁ → σ₁ ↠ᵛ σ₂ → σ ↠ᵛ σ₂

_⨾_ : {σ₁ σ₂ σ₃ : PState Z} → (σ₁ ↠ᵛ σ₂) → (σ₂ ↠ᵛ σ₃) → (σ₁ ↠ᵛ σ₃)
_⨾_ (σ →ᵖ⟨ s ⟩．) ss = σ →ᵖ⟨ s ⟩ ss
_⨾_ (σ →ᵖ⟨ s ⟩ ss₁) ss₂ = σ →ᵖ⟨ s ⟩ (ss₁ ⨾ ss₂)

⟨_⟩⧻_ : {σ : PState Z} → {σ₁ : PState Z} → (s : σ →ᵖ σ₁) → (K : PStack non-empty X) → (σ ⧻ K) →ᵖ (σ₁ ⧻ K)
⟨ lookup→ ⟩⧻ K = lookup→
⟨ lam→ ⟩⧻ K = lam→
⟨ pair→ ⟩⧻ K = pair→
⟨ unit→ ⟩⧻ K = unit→
⟨ W∷l→ ⟩⧻ K = W∷l→
⟨ W∷r→ ⟩⧻ K = W∷r→

⟪_⟫⧻_ : {σ : PState Z} → {σ₁ : PState Z} → (ss : σ ↠ᵛ σ₁) → (K : PStack non-empty X) → (σ ⧻ K) ↠ᵛ (σ₁ ⧻ K)
⟪ _ →ᵖ⟨ s ⟩． ⟫⧻ K =  _ →ᵖ⟨ ⟨ s ⟩⧻ K ⟩．
⟪ _ →ᵖ⟨ s ⟩ ss ⟫⧻ K =   _ →ᵖ⟨ ⟨ s ⟩⧻ K ⟩ (⟪ ss ⟫⧻ K)


\end{code}
%<*ValSteps>
\begin{code}
record ValSteps (W : Γ ⊢ᵛ X) (γ : MEnv Γ) : Set where
  field
    result : MVal X
    steps  : ⟨ ((⇡ W γ ∷ ⊠) {𝐛 = ▿}) ⟩ ↠ᵛ ⟨ ((⭭ result ∷ ⊠) {𝐛 = ▿}) ⟩
open ValSteps

normalise-val : (W : Γ ⊢ᵛ X) → (γ : MEnv Γ) → ValSteps W γ

-- ...
\end{code}
%</ValSteps>
\begin{code}

normalise-val (var i) γ = record { result = lookup i γ ; steps = ⟨ ⇡ (var i) γ ∷ ⊠ ⟩ →ᵖ⟨ lookup→ ⟩． }
normalise-val (lam M) γ = record { result = cloᵛ M γ ; steps = ⟨ ⇡ (lam M) γ ∷ ⊠ ⟩ →ᵖ⟨ lam→ ⟩． }
normalise-val (pair V W) γ =
  let
    IH₁ = normalise-val V γ
    IH₂ = normalise-val W γ
    trace = _ →ᵖ⟨ pair→ ⟩． ⨾ ⟪ steps IH₁ ⟫⧻ _ ⨾ _ →ᵖ⟨ W∷l→ ⟩． ⨾ (⟪ steps IH₂ ⟫⧻ _) ⨾ _ →ᵖ⟨ W∷r→ ⟩．
  in
  record { result = pairᵛ (result IH₁) (result IH₂) ; steps = trace }
normalise-val unit γ = record { result = unitᵛ ; steps = ⟨ ⇡ unit γ ∷ ⊠ ⟩ →ᵖ⟨ unit→ ⟩． }

determinismⱽ : {σ σ₁ : PState Z} → (s₁ s₂ : σ →ᵖ σ₁) → (s₁ ≡ s₂)
determinismⱽ lookup→ lookup→ = refl
determinismⱽ lam→ lam→ = refl
determinismⱽ pair→ pair→ = refl
determinismⱽ unit→ unit→ = refl
determinismⱽ W∷l→ W∷l→ = refl
determinismⱽ W∷r→ W∷r→ = refl

normalise-val-eval : (W : Γ ⊢ᵛ X) → (γ : MEnv Γ) → ValSteps.result (normalise-val W γ) ≡ eval W γ
normalise-val-eval (var i) γ = refl
normalise-val-eval (lam M) γ = refl
normalise-val-eval (pair V W) γ = cong₂ pairᵛ (normalise-val-eval V γ) (normalise-val-eval W γ)
normalise-val-eval unit γ = refl

--------------------------------------------------------------------------
-- correctness

open import Inception.Sub.Semantics as SubSem using ()

module Correct (R : Set) {k₀ : SubSem.⟦_⟧ R ℛ → R} where

  open SubSem R
  open Sem ⟦_⟧
  open TopLevel {ℛ = ℛ} {k₀ = k₀}

\end{code}

%<*SemPartial>
\begin{code}
  ⟦_⟧ᵀ : Partial X → ⟦ X ⟧
  ⟦ ⭭ 𝐖 ⟧ᵀ = ⟦ 𝐖 ⟧ⱽ
  ⟦ ⇡ W γ ⟧ᵀ = ⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ ⇡ᴸ V W γ ⟧ᵀ = ⟦ pair V W ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ ⇡ᴿ 𝐕 W γ ⟧ᵀ = ⟦ 𝐕 ⟧ⱽ , ⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ
\end{code}
%</SemPartial>

%<*SemPStack>
\begin{code}
  ⟦_⟧ᵖˢ : (K : PStack non-empty Z) → ⟦ Z ⟧
  ⟦ ((⭭ 𝐖) ∷ ⊠) {𝐛 = ▿} ⟧ᵖˢ = ⟦ 𝐖 ⟧ⱽ
  ⟦ (⇡ W γ ∷ ⊠) {𝐛 = ▿} ⟧ᵖˢ = ⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⇡ᴸ V W γ ∷ ⊠) {𝐛 = ▿} ⟧ᵖˢ = ⟦ pair V W ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⇡ᴿ 𝐕 W γ ∷ ⊠) {𝐛 = ▿} ⟧ᵖˢ = ⟦ 𝐕 ⟧ⱽ , ⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ ((⭭ 𝐖) ∷ ((x ∷ K) {𝐛 = 𝐛})) {𝐛 = ○} ⟧ᵖˢ = ⟦ (x ∷ K) {𝐛 = 𝐛} ⟧ᵖˢ
  ⟦ (⇡ W γ ∷ ((x ∷ K) {𝐛 = 𝐛})) {𝐛 = ○} ⟧ᵖˢ = ⟦ (x ∷ K) {𝐛 = 𝐛} ⟧ᵖˢ
  ⟦ (⇡ᴸ V W γ ∷ ((x ∷ K) {𝐛 = 𝐛})) {𝐛 = ○} ⟧ᵖˢ = ⟦ (x ∷ K) {𝐛 = 𝐛} ⟧ᵖˢ
  ⟦ (⇡ᴿ 𝐕 W γ ∷ ((x ∷ K) {𝐛 = 𝐛})) {𝐛 = ○} ⟧ᵖˢ = ⟦ (x ∷ K) {𝐛 = 𝐛} ⟧ᵖˢ
\end{code}
%</SemPStack>

%<*SemPState>
\begin{code}
  ⟦_⟧ᵖꟴ : (σ : PState Z) → ⟦ Z ⟧
  ⟦ ⟨ K ⟩ ⟧ᵖꟴ = ⟦ K ⟧ᵖˢ
\end{code}
%</SemPState>

\begin{code}

  data PStackGood : PStack non-empty Z → Set where


    ▿ : (W : Partial X) → PStackGood ((W ∷ ⊠) {𝐛 = ▿})

    lhs-good :   {b : IsEmpty} {K : PStack b Z}
              → {Wₕₒₗₑ : Γ ⊢ᵛ X} {W₂ : Γ ⊢ᵛ Y} {γ : MEnv Γ} {W : Partial X}
              → {𝐛 : BotEq b (X `× Y) Z}
              → PStackGood (((⇡ᴸ Wₕₒₗₑ W₂ γ) ∷ K) {𝐛 = 𝐛})
              → (eq : ⟦ W ⟧ᵀ ≡ ⟦ Wₕₒₗₑ ⟧ᵛ ⟦ γ ⟧ᴱ) → PStackGood ((W ∷ ((⇡ᴸ Wₕₒₗₑ W₂ γ) ∷ K) {𝐛 = 𝐛}) {𝐛 = ○})

    rhs-good :   {b : IsEmpty} {K : PStack b Z}
              → {𝐕 : MVal X} {Wₕₒₗₑ : Γ ⊢ᵛ Y} {γ : MEnv Γ} {W : Partial Y}
              → {𝐛 : BotEq b (X `× Y) Z}
              → PStackGood (((⇡ᴿ 𝐕 Wₕₒₗₑ γ) ∷ K) {𝐛 = 𝐛})
              → (eq : ⟦ W ⟧ᵀ ≡ ⟦ Wₕₒₗₑ ⟧ᵛ ⟦ γ ⟧ᴱ) → PStackGood ((W ∷ ((⇡ᴿ 𝐕 Wₕₒₗₑ γ) ∷ K) {𝐛 = 𝐛}) {𝐛 = ○})

  data PStateGood : (σ : PState X) → Set where
      g[_] : {K : PStack non-empty Z} → PStackGood K → PStateGood ⟨ K ⟩

  lookup-good : (i : Γ ∋ X) → (γ : MEnv Γ) → ⟦ lookup i γ ⟧ⱽ ≡ ⟦ i ⟧ᵐ ⟦ γ ⟧ᴱ
  lookup-good here (γ · x) = refl
  lookup-good (there i) (γ · x) = lookup-good i γ

  valstate-good : {σ σ₁ : PState X} → PStateGood σ → σ →ᵖ σ₁ → PStateGood σ₁
  valstate-good g[ ▿ W ] lookup→ = g[ ▿ (⭭ _) ]
  valstate-good g[ ▿ W ] lam→ = g[ ▿ (⭭ cloᵛ _ _) ]
  valstate-good g[ ▿ W ] pair→ = g[ lhs-good (▿ (⇡ᴸ _ _ _)) refl ]
  valstate-good g[ ▿ W ] unit→ = g[ ▿ (⭭ unitᵛ) ]
  valstate-good g[ lhs-good g eq ] (lookup→ {i = i} {γ = γ}) = g[ (lhs-good g (trans (lookup-good i γ) eq)) ]
  valstate-good g[ lhs-good x eq ] lam→ = g[ lhs-good x eq ]
  valstate-good g[ lhs-good x eq ] pair→ = g[ lhs-good (lhs-good x eq) refl ]
  valstate-good g[ lhs-good x eq ] unit→ = g[ lhs-good x eq ]
  valstate-good g[ rhs-good g eq ] (lookup→ {i = i} {γ = γ}) = g[ (rhs-good g (trans (lookup-good i γ) eq)) ]
  valstate-good g[ rhs-good x eq ] lam→ = g[ rhs-good x eq ]
  valstate-good g[ rhs-good x eq ] pair→ = g[ lhs-good (rhs-good x eq) refl ]
  valstate-good g[ rhs-good x eq ] unit→ = g[ rhs-good x eq ]
  valstate-good g[ lhs-good (▿ W) eq ] W∷l→ = g[ rhs-good (▿ (⇡ᴿ _ _ _)) refl ]
  valstate-good g[ lhs-good {Wₕₒₗₑ = Wₕₒₗₑ} {W₂ = W₂} {γ = γ} (lhs-good {Wₕₒₗₑ = Wₕₒₗₑ₁} {W₂ = W₁} {γ = γ₁} x eq₁) eq ] (W∷l→ {𝐕 = 𝐕}) = g[ (rhs-good (lhs-good x ((⟦ 𝐕 ⟧ⱽ , ⟦ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ) ≡⟨ cong (λ x → x , ⟦ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ) eq ⟩ ⟦ ⇡ᴸ Wₕₒₗₑ W₂ γ ⟧ᵀ ≡⟨ eq₁ ⟩ ⟦ Wₕₒₗₑ₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ ∎)) refl) ]
  valstate-good g[ lhs-good {Wₕₒₗₑ = Wₕₒₗₑ} {W₂ = W₂} {γ = γ} (rhs-good {𝐕 = 𝐕₁} {Wₕₒₗₑ = Wₕₒₗₑ₁} {γ = γ₁} x eq₁) eq ] (W∷l→ {𝐕 = 𝐕}) = g[ (rhs-good (rhs-good x ((⟦ 𝐕 ⟧ⱽ , ⟦ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ) ≡⟨ cong (λ x → x , ⟦ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ) eq ⟩ ⟦ ⇡ᴸ Wₕₒₗₑ W₂ γ ⟧ᵀ ≡⟨ eq₁ ⟩ ⟦ Wₕₒₗₑ₁ ⟧ᵛ ⟦ γ₁ ⟧ᴱ ∎)) refl) ]

  valstate-good g[ rhs-good {𝐕 = 𝐕} {Wₕₒₗₑ = Wₕₒₗₑ} {γ = γ} (▿ W) eq ] W∷r→ = g[ ▿ (⭭ pairᵛ _ _) ]
  valstate-good g[ rhs-good {𝐕 = 𝐕} {Wₕₒₗₑ = Wₕₒₗₑ} {γ = γ} (lhs-good {Wₕₒₗₑ = Wₕₒₗₑ₁} {W₂ = W₂} {γ = γ₁} x eq₁) eq ] (W∷r→ {𝐖 = 𝐖}) = g[ (lhs-good x (trans (cong (λ x → ⟦ 𝐕 ⟧ⱽ , x) eq) eq₁)) ]
  valstate-good g[ rhs-good {𝐕 = 𝐕} {Wₕₒₗₑ = Wₕₒₗₑ} {γ = γ} (rhs-good {𝐕 = 𝐕₁} {Wₕₒₗₑ = Wₕₒₗₑ₁} {γ = γ₁} x eq₁) eq ] (W∷r→ {𝐖 = 𝐖}) = g[ (rhs-good x (trans (cong (λ x → ⟦ 𝐕 ⟧ⱽ , x) eq) eq₁)) ]

  valstate-eq : {σ σ₁ : PState X} → PStateGood σ → σ →ᵖ σ₁ → ⟦ σ ⟧ᵖꟴ ≡ ⟦ σ₁ ⟧ᵖꟴ
  valstate-eq {σ = σ} {σ₁ = σ₁} good (lookup→ {i = i} {γ = γ} {K = ⊠} {𝐛 = ▿}) = lookup-eq i γ
  valstate-eq {σ = σ} {σ₁ = σ₁} good (lookup→ {K = (x ∷ K) {𝐛 = 𝐛}} {𝐛 = ○}) = refl
  valstate-eq {σ = σ} {σ₁ = σ₁} good (lam→ {K = ⊠} {𝐛 = ▿}) = refl
  valstate-eq {σ = σ} {σ₁ = σ₁} good (lam→ {K = (x ∷ K) {𝐛 = 𝐛}} {𝐛 = ○}) = refl
  valstate-eq {σ = σ} {σ₁ = σ₁} good (pair→ {K = ⊠} {𝐛 = ▿}) = refl
  valstate-eq {σ = σ} {σ₁ = σ₁} good (pair→ {K = (x ∷ K) {𝐛 = 𝐛}} {𝐛 = ○}) = refl
  valstate-eq {σ = σ} {σ₁ = σ₁} good (unit→ {K = ⊠} {𝐛 = ▿}) = refl
  valstate-eq {σ = σ} {σ₁ = σ₁} good (unit→ {K = (x ∷ K) {𝐛 = 𝐛}} {𝐛 = ○}) = refl
  valstate-eq {σ = σ} {σ₁ = σ₁} g[ lhs-good {W₂ = W₂} {γ = γ} x eq ] (W∷l→ {K = ⊠} {𝐛 = ▿}) = cong (λ x → x , ⟦ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ) (sym eq)
  valstate-eq {σ = σ} {σ₁ = σ₁} good (W∷l→ {K = (x ∷ K) {𝐛 = 𝐛}} {𝐛 = ○}) = refl
  valstate-eq {σ = σ} {σ₁ = σ₁} g[ rhs-good {𝐕 = 𝐕} {γ = γ} x eq ] (W∷r→ {K = ⊠} {𝐛 = ▿}) = cong (λ x → ⟦ 𝐕 ⟧ⱽ , x) (sym eq)
  valstate-eq {σ = σ} {σ₁ = σ₁} good (W∷r→ {K = (x ∷ K) {𝐛 = 𝐛}} {𝐛 = ○}) = refl

  valstate-trans-eq : {σ σ₁ : PState X} → PStateGood σ → σ ↠ᵛ σ₁ → ⟦ σ ⟧ᵖꟴ ≡ ⟦ σ₁ ⟧ᵖꟴ
  valstate-trans-eq good (σ →ᵖ⟨ s ⟩．) = valstate-eq good s
  valstate-trans-eq good (σ →ᵖ⟨ s ⟩ ss) = trans (valstate-eq good s) (valstate-trans-eq (valstate-good good s) ss)

  value-machine-correct : (W : Γ ⊢ᵛ X) → (γ : MEnv Γ) → ⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ ≡ ⟦ result (normalise-val W γ) ⟧ⱽ
  value-machine-correct W γ = valstate-trans-eq g[ ▿ (⇡ W γ) ] (steps (normalise-val W γ))

\end{code}
