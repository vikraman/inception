\begin{code}
{-# OPTIONS --no-postfix-projections #-}

module scratch.PMachine where

open import Inception.Sub.Syntax
open import Inception.Sub.Machine
open import Inception.Prelude

open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Unit using (⊤; tt)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst)
open Eq.≡-Reasoning

---------------------------------------------------------------------------------

infix  20 ⭭_
infix  19 _∷_
infixr 17 _→ᵖ⟨_⟩．
infixr 15 _→ᵖ⟨_⟩_
infix  15 _→ᵖ_
infixr 10 _⨾_

---------------------------------------------------------------------------------
-- MACHINE FOR VALUES

\end{code}
%<*Partial>
\begin{code}

data Partial {Z₀ : Ty} : (X : Ty) → Set where

    ⭭_ :   (Ẇ : MVal {Z₀ = Z₀} X)
           ----------------------
           → Partial X

    ⇡ :    (W : Val Γ X) → (Env {Z₀ = Z₀} Γ)
           --------------------------------
           → Partial X

    ⇡ᴸ :   (W₁ : Val Γ X₁) → (W₂ : Val Γ X₂) → (Env {Z₀ = Z₀} Γ)
           ----------------------------------------------------
           → Partial (X₁ `× X₂)

    ⇡ᴿ :   (Ẇ₁ : MVal {Z₀ = Z₀} X₁) → (W₂ : Val Γ X₂) → (Env {Z₀ = Z₀} Γ)
           ------------------------------------------------------------
           → Partial (X₁ `× X₂)

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

data PStack {Z₀ : Ty} : IsEmpty → Ty → Set where

    ⊠ :
           -----------------------
           PStack {Z₀ = Z₀} empty Z₁

    _∷_ :  Partial {Z₀ = Z₀} X → (pstack : PStack {Z₀ = Z₀} ∅? Z₁)
           → {𝐛 : BotEq ∅? X Z₁}
           --------------------------------------------------
           → PStack non-empty Z₁


data PState {Z₀ : Ty} : Ty → Set where

    ⟨_⟩ :  PStack {Z₀ = Z₀} non-empty Z₁
           ---------------------------
           → PState {Z₀ = Z₀} Z₁

\end{code}
%</PStates>
\begin{code}

_⧺_ : {Z₀ : Ty} → PStack {Z₀ = Z₀} ∅? Z₁ → PStack {Z₀ = Z₀} non-empty Z₁' → PStack {Z₀ = Z₀} non-empty Z₁'
⊠ ⧺ lower = lower
(W ∷ upper) ⧺ lower = (W ∷ (upper ⧺ lower)) {𝐛 = ○}

_⧻_ : {Z₀ : Ty} → (upper : PState {Z₀ = Z₀} Z₁) → PStack {Z₀ = Z₀} non-empty Z₁' → PState {Z₀ = Z₀} Z₁'
⟨ upper ⟩ ⧻ lower = ⟨ upper ⧺ lower ⟩

\end{code}
%<*PTrans>
\begin{code}

data _→ᵖ_ {Z₀ : Ty} {Z₁ : Ty} :
        PState {Z₀ = Z₀} Z₁ → PState {Z₀ = Z₀} Z₁ → Set where

    lookup→ :   {x : Γ ∋ X} {γ : Env {Z₀ = Z₀} Γ}
                {pstack : PStack {Z₀ = Z₀} ∅? Z₁} {𝐛 : BotEq ∅? X Z₁}
                -------------------------------------------------
                →  ⟨ (⇡ (var x) γ ∷ pstack) {𝐛 = 𝐛} ⟩
                   →ᵖ ⟨ (⭭ (lookup x γ) ∷ pstack) {𝐛 = 𝐛} ⟩

    lam→ :      {M : Comp (Γ ∙ X) Y} {γ  : Env {Z₀ = Z₀} Γ}
                {pstack : PStack {Z₀ = Z₀} ∅? Z₁} {𝐛 : BotEq ∅? (X `⇒ Y) Z₁}
                --------------------------------------------------------
                →  ⟨ (⇡ (lam M) γ ∷ pstack) {𝐛 = 𝐛} ⟩
                   →ᵖ ⟨ (⭭ (cloᵛ M γ) ∷ pstack) {𝐛 = 𝐛} ⟩

    pair→ :     {γ : Env {Z₀ = Z₀} Γ} {W₁ : Val Γ X₁} {W₂ : Val Γ X₂}
                {pstack : PStack {Z₀ = Z₀} ∅? Z₁} {𝐛 : BotEq ∅? (X₁ `× X₂) Z₁}
                ---------------------------------------------------------
                →  ⟨ (⇡ (pair W₁ W₂) γ ∷ pstack) {𝐛 = 𝐛} ⟩
                   →ᵖ ⟨ (⇡ W₁ γ ∷ ((⇡ᴸ W₁ W₂ γ ∷ pstack) {𝐛 = 𝐛})) {𝐛 = ○} ⟩

    unit→ :     {γ  : Env {Z₀ = Z₀} Γ}
                {pstack : PStack {Z₀ = Z₀} ∅? Z₁} {𝐛 : BotEq ∅? `Unit Z₁}
                ----------------------------------------------------
                →  ⟨ (⇡ unit γ ∷ pstack) {𝐛 = 𝐛} ⟩
                   →ᵖ ⟨ (⭭ unitᵛ ∷ pstack) {𝐛 = 𝐛} ⟩

    W∷l→ :      {γ : Env {Z₀ = Z₀} Γ} {Ẇ₁ : MVal X₁} {W₁ : Val Γ X₁}
                {W₂ : Val Γ X₂} {pstack : PStack {Z₀ = Z₀} ∅? Z₁}
                {𝐛 : BotEq ∅? (X₁ `× X₂) Z₁}
                ------------------------------------------------------
                →  ⟨ (⭭ Ẇ₁ ∷ ((⇡ᴸ W₁ W₂ γ ∷ pstack) {𝐛 = 𝐛})) {𝐛 = ○} ⟩
                   →ᵖ ⟨ (⇡ W₂ γ ∷ ((⇡ᴿ Ẇ₁ W₂ γ ∷ pstack) {𝐛 = 𝐛})) {𝐛 = ○} ⟩

    W∷r→ :      {γ : Env {Z₀ = Z₀} Γ} {Ẇ₁ : MVal X₁} {Ẇ₂ : MVal X₂} {W₂ : Val Γ X₂}
                {pstack : PStack {Z₀ = Z₀} ∅? Z₁} {𝐛 : BotEq ∅? (X₁ `× X₂) Z₁}
                -----------------------------------------------------------------
                →  ⟨ (⭭ Ẇ₂ ∷ ((⇡ᴿ Ẇ₁ W₂ γ ∷ pstack) {𝐛 = 𝐛})) {𝐛 = ○} ⟩
                   →ᵖ ⟨ (⭭ pairᵛ Ẇ₁ Ẇ₂ ∷ pstack) {𝐛 = 𝐛} ⟩

\end{code}
%</PTrans>
\begin{code}

data _↠ᵛ_ {Z₀ Z₁ : Ty} : PState {Z₀ = Z₀} Z₁ → PState {Z₀ = Z₀} Z₁ → Set where

  _→ᵖ⟨_⟩． : (S : PState Z₁) → {S' : PState Z₁} → (laststep : S →ᵖ S') → S ↠ᵛ S'

  _→ᵖ⟨_⟩_ : (S : PState Z₁) → {S' S'' : PState Z₁} → S →ᵖ S' → S' ↠ᵛ S'' → S ↠ᵛ S''

_⨾_ : {Z₀ : Ty} {F S T : PState {Z₀ = Z₀} Z₁} → (F ↠ᵛ S) → (S ↠ᵛ T) → (F ↠ᵛ T)
_⨾_ (F →ᵖ⟨ F>S ⟩．) S>>T = F →ᵖ⟨ F>S ⟩ S>>T
_⨾_ (F →ᵖ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᵖ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ S₂>>T)

⟨_⟩⧻_ : {Z₀ : Ty} {from : PState {Z₀ = Z₀} Z₁} → {to : PState {Z₀ = Z₀} Z₁} → (F>T : from →ᵖ to) → (pstack : PStack {Z₀ = Z₀} non-empty Z₁') → (from ⧻ pstack) →ᵖ (to ⧻ pstack)
⟨ lookup→ ⟩⧻ pstack = lookup→
⟨ lam→ ⟩⧻ pstack = lam→
⟨ pair→ ⟩⧻ pstack = pair→
⟨ unit→ ⟩⧻ pstack = unit→
⟨ W∷l→ ⟩⧻ pstack = W∷l→
⟨ W∷r→ ⟩⧻ pstack = W∷r→

⟪_⟫⧻_ : {from : PState {Z₀ = Z₀} Z₁} → {to : PState {Z₀ = Z₀} Z₁} → (F>T : from ↠ᵛ to) → (pstack : PStack {Z₀ = Z₀} non-empty Z₁') → (from ⧻ pstack) ↠ᵛ (to ⧻ pstack)
⟪ _ →ᵖ⟨ F>T ⟩． ⟫⧻ pstack =  _ →ᵖ⟨ ⟨ F>T ⟩⧻ pstack ⟩．
⟪ _ →ᵖ⟨ F>T ⟩ F>>T ⟫⧻ pstack =   _ →ᵖ⟨ ⟨ F>T ⟩⧻ pstack ⟩ (⟪ F>>T ⟫⧻ pstack)


\end{code}
%<*ValSteps>
\begin{code}
record ValSteps {Z₀ : Ty} (W : Val Γ X) (γ : Env {Z₀ = Z₀} Γ) : Set where
  field
    result : MVal {Z₀ = Z₀} X
    steps  : ⟨ ((⇡ W γ ∷ ⊠) {𝐛 = ▿}) ⟩ ↠ᵛ ⟨ ((⭭ result ∷ ⊠) {𝐛 = ▿}) ⟩
open ValSteps

normalise-val : {Z₀ : Ty} → (W : Val Γ X) → (γ : Env {Z₀ = Z₀} Γ) → ValSteps W γ

-- ...
\end{code}
%</ValSteps>
\begin{code}

normalise-val (var i) γ = record { result = lookup i γ ; steps = ⟨ ⇡ (var i) γ ∷ ⊠ ⟩ →ᵖ⟨ lookup→ ⟩． }
normalise-val (lam M) γ = record { result = cloᵛ M γ ; steps = ⟨ ⇡ (lam M) γ ∷ ⊠ ⟩ →ᵖ⟨ lam→ ⟩． }
normalise-val (pair W₁ W₂) γ =
  let
    IH₁ = normalise-val W₁ γ
    IH₂ = normalise-val W₂ γ
    trace = _ →ᵖ⟨ pair→ ⟩． ⨾ ⟪ steps IH₁ ⟫⧻ _ ⨾ _ →ᵖ⟨ W∷l→ ⟩． ⨾ (⟪ steps IH₂ ⟫⧻ _) ⨾ _ →ᵖ⟨ W∷r→ ⟩．
  in
  record { result = pairᵛ (result IH₁) (result IH₂) ; steps = trace }
normalise-val unit γ = record { result = unitᵛ ; steps = ⟨ ⇡ unit γ ∷ ⊠ ⟩ →ᵖ⟨ unit→ ⟩． }

determinismⱽ : {Z₀ : Ty} {S S' : PState {Z₀ = Z₀} Z₁} → (S→S'₁ S→S'₂ : S →ᵖ S') → (S→S'₁ ≡ S→S'₂)
determinismⱽ lookup→ lookup→ = refl
determinismⱽ lam→ lam→ = refl
determinismⱽ pair→ pair→ = refl
determinismⱽ unit→ unit→ = refl
determinismⱽ W∷l→ W∷l→ = refl
determinismⱽ W∷r→ W∷r→ = refl

normalise-val-eval : {Z₀ : Ty} → (W : Val Γ X) → (γ : Env {Z₀ = Z₀} Γ) → ValSteps.result (normalise-val W γ) ≡ eval W γ
normalise-val-eval (var i) γ = refl
normalise-val-eval (lam M) γ = refl
normalise-val-eval (pair W₁ W₂) γ = cong₂ pairᵛ (normalise-val-eval W₁ γ) (normalise-val-eval W₂ γ)
normalise-val-eval unit γ = refl

---------------------------------------------------------------------------------
-- CORRECTNESS

open import Inception.Sub.Semantics as Sem using ()

module Correct (R : Set) {R₀ : Ty} {k₀ : Sem.⟦_⟧ R R₀ → R} where

  open Sem R
  open TopLevel {R₀ = R₀} {k₀ = k₀}

\end{code}

%<*SemPartial>
\begin{code}
  ⟦_⟧ᵀ : Partial {Z₀ = R₀} X → ⟦ X ⟧
  ⟦ ⭭ 𝐖 ⟧ᵀ = ⟦ 𝐖 ⟧ⱽ
  ⟦ ⇡ W γ ⟧ᵀ = ⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ ⇡ᴸ W₁ W₂ γ ⟧ᵀ = ⟦ pair W₁ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ ⇡ᴿ 𝐖₁ W₂ γ ⟧ᵀ = ⟦ 𝐖₁ ⟧ⱽ , ⟦ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ
\end{code}
%</SemPartial>

%<*SemPStack>
\begin{code}
  ⟦_⟧ᵖˢ : (S : PStack {Z₀ = R₀} non-empty Z₁) → ⟦ Z₁ ⟧
  ⟦ ((⭭ W) ∷ ⊠) {𝐛 = ▿} ⟧ᵖˢ = ⟦ W ⟧ⱽ
  ⟦ (⇡ W γ ∷ ⊠) {𝐛 = ▿} ⟧ᵖˢ = ⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⇡ᴸ W₁ W₂ γ ∷ ⊠) {𝐛 = ▿} ⟧ᵖˢ = ⟦ pair W₁ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ (⇡ᴿ 𝐖₁ W₂ γ ∷ ⊠) {𝐛 = ▿} ⟧ᵖˢ = ⟦ 𝐖₁ ⟧ⱽ , ⟦ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ
  ⟦ ((⭭ 𝐖) ∷ ((x ∷ S) {𝐛 = 𝐛})) {𝐛 = ○} ⟧ᵖˢ = ⟦ (x ∷ S) {𝐛 = 𝐛} ⟧ᵖˢ
  ⟦ (⇡ W γ ∷ ((x ∷ S) {𝐛 = 𝐛})) {𝐛 = ○} ⟧ᵖˢ = ⟦ (x ∷ S) {𝐛 = 𝐛} ⟧ᵖˢ
  ⟦ (⇡ᴸ W₁ W₂ γ ∷ ((x ∷ S) {𝐛 = 𝐛})) {𝐛 = ○} ⟧ᵖˢ = ⟦ (x ∷ S) {𝐛 = 𝐛} ⟧ᵖˢ
  ⟦ (⇡ᴿ 𝐖₁ W₂ γ ∷ ((x ∷ S) {𝐛 = 𝐛})) {𝐛 = ○} ⟧ᵖˢ = ⟦ (x ∷ S) {𝐛 = 𝐛} ⟧ᵖˢ
\end{code}
%</SemPStack>

%<*SemPState>
\begin{code}
  ⟦_⟧ᵖꟴ : (S : PState {Z₀ = R₀} Z₁) → ⟦ Z₁ ⟧
  ⟦ ⟨ pstack ⟩ ⟧ᵖꟴ = ⟦ pstack ⟧ᵖˢ
\end{code}
%</SemPState>

\begin{code}

  data PStackGood : PStack {Z₀ = R₀} non-empty Z₁ → Set where


    ▿ : (W : Partial X) → PStackGood ((W ∷ ⊠) {𝐛 = ▿})

    lhs-good :   {b : IsEmpty} {pstack : PStack b Z₁}
              → {Wₕₒₗₑ : Val Γ X} {W₂ : Val Γ Y} {γ : Env Γ} {W : Partial X}
              → {𝐛 : BotEq b (X `× Y) Z₁}
              → PStackGood (((⇡ᴸ Wₕₒₗₑ W₂ γ) ∷ pstack) {𝐛 = 𝐛})
              → (eq : ⟦ W ⟧ᵀ ≡ ⟦ Wₕₒₗₑ ⟧ᵛ ⟦ γ ⟧ᴱ) → PStackGood ((W ∷ ((⇡ᴸ Wₕₒₗₑ W₂ γ) ∷ pstack) {𝐛 = 𝐛}) {𝐛 = ○})

    rhs-good :   {b : IsEmpty} {pstack : PStack b Z₁}
              → {W₁ : MVal X} {Wₕₒₗₑ : Val Γ Y} {γ : Env Γ} {W : Partial Y}
              → {𝐛 : BotEq b (X `× Y) Z₁}
              → PStackGood (((⇡ᴿ W₁ Wₕₒₗₑ γ) ∷ pstack) {𝐛 = 𝐛})
              → (eq : ⟦ W ⟧ᵀ ≡ ⟦ Wₕₒₗₑ ⟧ᵛ ⟦ γ ⟧ᴱ) → PStackGood ((W ∷ ((⇡ᴿ W₁ Wₕₒₗₑ γ) ∷ pstack) {𝐛 = 𝐛}) {𝐛 = ○})

  data PStateGood : (S : PState {Z₀ = R₀} X) → Set where
      g[_] : {S : PStack {Z₀ = R₀} non-empty Z₁} → PStackGood S → PStateGood ⟨ S ⟩

  lookup-good : (i : Γ ∋ X) → (γ : Env Γ) → ⟦ lookup i γ ⟧ⱽ ≡ ⟦ i ⟧ᵐ ⟦ γ ⟧ᴱ
  lookup-good new (γ · x) = refl
  lookup-good (old i) (γ · x) = lookup-good i γ

  valstate-good : {S S' : PState {Z₀ = R₀} X} → PStateGood S → S →ᵖ S' → PStateGood S'
  valstate-good g[ ▿ W ] lookup→ = g[ ▿ (⭭ _) ]
  valstate-good g[ ▿ W ] lam→ = g[ ▿ (⭭ cloᵛ _ _) ]
  valstate-good g[ ▿ W ] pair→ = g[ lhs-good (▿ (⇡ᴸ _ _ _)) refl ]
  valstate-good g[ ▿ W ] unit→ = g[ ▿ (⭭ unitᵛ) ]
  valstate-good g[ lhs-good g eq ] (lookup→ {x = x} {γ = γ}) = g[ (lhs-good g (trans (lookup-good x γ) eq)) ]
  valstate-good g[ lhs-good x eq ] lam→ = g[ lhs-good x eq ]
  valstate-good g[ lhs-good x eq ] pair→ = g[ lhs-good (lhs-good x eq) refl ]
  valstate-good g[ lhs-good x eq ] unit→ = g[ lhs-good x eq ]
  valstate-good g[ rhs-good g eq ] (lookup→ {x = x} {γ = γ}) = g[ (rhs-good g (trans (lookup-good x γ) eq)) ]
  valstate-good g[ rhs-good x eq ] lam→ = g[ rhs-good x eq ]
  valstate-good g[ rhs-good x eq ] pair→ = g[ lhs-good (rhs-good x eq) refl ]
  valstate-good g[ rhs-good x eq ] unit→ = g[ rhs-good x eq ]
  valstate-good g[ lhs-good (▿ W) eq ] W∷l→ = g[ rhs-good (▿ (⇡ᴿ _ _ _)) refl ]
  valstate-good g[ lhs-good {Wₕₒₗₑ = Wₕₒₗₑ} {W₂ = W₂} {γ = γ} (lhs-good {Wₕₒₗₑ = Wₕₒₗₑ'} {W₂ = W₂'} {γ = γ'} x eq₁) eq ] (W∷l→ {Ẇ₁ = Ẇ₁}) = g[ (rhs-good (lhs-good x ((⟦ Ẇ₁ ⟧ⱽ , ⟦ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ) ≡⟨ cong (λ x → x , ⟦ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ) eq ⟩ ⟦ ⇡ᴸ Wₕₒₗₑ W₂ γ ⟧ᵀ ≡⟨ eq₁ ⟩ ⟦ Wₕₒₗₑ' ⟧ᵛ ⟦ γ' ⟧ᴱ ∎)) refl) ]
  valstate-good g[ lhs-good {Wₕₒₗₑ = Wₕₒₗₑ} {W₂ = W₂} {γ = γ} (rhs-good {W₁ = W₁} {Wₕₒₗₑ = Wₕₒₗₑ'} {γ = γ'} x eq₁) eq ] (W∷l→ {Ẇ₁ = Ẇ₁}) = g[ (rhs-good (rhs-good x ((⟦ Ẇ₁ ⟧ⱽ , ⟦ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ) ≡⟨ cong (λ x → x , ⟦ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ) eq ⟩ ⟦ ⇡ᴸ Wₕₒₗₑ W₂ γ ⟧ᵀ ≡⟨ eq₁ ⟩ ⟦ Wₕₒₗₑ' ⟧ᵛ ⟦ γ' ⟧ᴱ ∎)) refl) ]

  valstate-good g[ rhs-good {W₁ = W₁} {Wₕₒₗₑ = Wₕₒₗₑ} {γ = γ} (▿ W) eq ] W∷r→ = g[ ▿ (⭭ pairᵛ _ _) ]
  valstate-good g[ rhs-good {W₁ = W₁} {Wₕₒₗₑ = Wₕₒₗₑ} {γ = γ} (lhs-good {Wₕₒₗₑ = Wₕₒₗₑ'} {W₂ = W₂} {γ = γ'} x eq₁) eq ] (W∷r→ {Ẇ₂ = Ẇ₂}) = g[ (lhs-good x (trans (cong (λ x → ⟦ W₁ ⟧ⱽ , x) eq) eq₁)) ]
  valstate-good g[ rhs-good {W₁ = W₁} {Wₕₒₗₑ = Wₕₒₗₑ} {γ = γ} (rhs-good {W₁ = W₁'} {Wₕₒₗₑ = Wₕₒₗₑ'} {γ = γ'} x eq₁) eq ] (W∷r→ {Ẇ₂ = Ẇ₂}) = g[ (rhs-good x (trans (cong (λ x → ⟦ W₁ ⟧ⱽ , x) eq) eq₁)) ]

  valstate-eq : {S S' : PState {Z₀ = R₀} X} → PStateGood S → S →ᵖ S' → ⟦ S ⟧ᵖꟴ ≡ ⟦ S' ⟧ᵖꟴ
  valstate-eq {S = S} {S' = S'} good (lookup→ {x = x} {γ = γ} {pstack = ⊠} {𝐛 = ▿}) = lookup-eq x γ
  valstate-eq {S = S} {S' = S'} good (lookup→ {pstack = (x ∷ pstack) {𝐛 = 𝐛}} {𝐛 = ○}) = refl
  valstate-eq {S = S} {S' = S'} good (lam→ {pstack = ⊠} {𝐛 = ▿}) = refl
  valstate-eq {S = S} {S' = S'} good (lam→ {pstack = (x ∷ pstack) {𝐛 = 𝐛}} {𝐛 = ○}) = refl
  valstate-eq {S = S} {S' = S'} good (pair→ {pstack = ⊠} {𝐛 = ▿}) = refl
  valstate-eq {S = S} {S' = S'} good (pair→ {pstack = (x ∷ pstack) {𝐛 = 𝐛}} {𝐛 = ○}) = refl
  valstate-eq {S = S} {S' = S'} good (unit→ {pstack = ⊠} {𝐛 = ▿}) = refl
  valstate-eq {S = S} {S' = S'} good (unit→ {pstack = (x ∷ pstack) {𝐛 = 𝐛}} {𝐛 = ○}) = refl
  valstate-eq {S = S} {S' = S'} g[ lhs-good {W₂ = W₂} {γ = γ} x eq ] (W∷l→ {pstack = ⊠} {𝐛 = ▿}) = cong (λ x → x , ⟦ W₂ ⟧ᵛ ⟦ γ ⟧ᴱ) (sym eq)
  valstate-eq {S = S} {S' = S'} good (W∷l→ {pstack = (x ∷ pstack) {𝐛 = 𝐛}} {𝐛 = ○}) = refl
  valstate-eq {S = S} {S' = S'} g[ rhs-good {W₁ = W₁} {γ = γ} x eq ] (W∷r→ {pstack = ⊠} {𝐛 = ▿}) = cong (λ x → ⟦ W₁ ⟧ⱽ , x) (sym eq)
  valstate-eq {S = S} {S' = S'} good (W∷r→ {pstack = (x ∷ pstack) {𝐛 = 𝐛}} {𝐛 = ○}) = refl

  valstate-trans-eq : {S S' : PState {Z₀ = R₀} X} → PStateGood S → S ↠ᵛ S' → ⟦ S ⟧ᵖꟴ ≡ ⟦ S' ⟧ᵖꟴ
  valstate-trans-eq good (S →ᵖ⟨ S→ᵖS' ⟩．) = valstate-eq good S→ᵖS'
  valstate-trans-eq good (S →ᵖ⟨ S→ᵖS' ⟩ S'↠ᵛS'') = trans (valstate-eq good S→ᵖS') (valstate-trans-eq (valstate-good good S→ᵖS') S'↠ᵛS'')

  value-machine-correct : (W : Val Γ X) → (γ : Env {Z₀ = R₀} Γ) → ⟦ W ⟧ᵛ ⟦ γ ⟧ᴱ ≡ ⟦ result (normalise-val W γ) ⟧ⱽ
  value-machine-correct W γ = valstate-trans-eq g[ ▿ (⇡ W γ) ] (steps (normalise-val W γ))

\end{code}
