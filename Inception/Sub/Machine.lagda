\begin{code}
{-# OPTIONS --no-postfix-projections #-}

module Inception.Sub.Machine where

open import Inception.Sub.Syntax
open import Inception.Prelude

open import Data.Product using (proj₁; proj₂; _,_; _×_; Σ-syntax)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

---------------------------------------------------------------------------------

infixl 27 _·_

---------------------------------------------------------------------------------
-- ENVIRONMENTS

\end{code}
%<*Env>
\begin{code}

mutual

  data CStack {Z₀ : Ty} : (X : Ty) → Set where

    ◻ :        CStack Z₀

    <_；_>∷_ :  Comp (Γ ∙ Y) X → (γ : Env {Z₀ = Z₀} Γ)
                → (pstack : CStack {Z₀ = Z₀} X)
                ------------------------------------
                → CStack Y

  data Value {Z₀ : Ty} : Ty → Set where

    unitᵛ :
              -------------------
              Value {Z₀ = Z₀} `Unit

    pairᵛ :   (Ẇ₁ : Value {Z₀ = Z₀} X₁) → (Ẇ₂ : Value {Z₀ = Z₀} X₂)
              -------------------------------------------------
              → Value (X₁ `× X₂)

    cloᵛ :    {Γ : Ctx} → (M : Comp (Γ ∙ X) Y) → (γ : Env {Z₀ = Z₀} Γ)
              ----------------------------------------------------
              → Value (X `⇒ Y)

    jumpᵛ :   {Γ : Ctx} → (M : Comp Γ X) → (γ : Env {Z₀ = Z₀} Γ)
              → (cs : CStack {Z₀ = Z₀} X)
              -----------------------------------------------
              → Value `L

  data Env {Z₀ : Ty} : Ctx → Set where

    ⋄ :
           --------------
           Env {Z₀ = Z₀} ε

    _·_ :  Env {Z₀ = Z₀} Γ → Value {Z₀ = Z₀} X
           ----------------------------------
           → Env {Z₀ = Z₀} (Γ ∙ X)

lookup : Γ ∋ X → Env {Z₀ = Z₀} Γ → Value {Z₀ = Z₀} X
lookup here (γ · Ẇ) = Ẇ
lookup (there x) (γ · Ẇ) = lookup x γ

\end{code}
%</Env>
\begin{code}

---------------------------------------------------------------------------------
-- VALUE PROJECTIONS

proj₁-val : {Z₀ : Ty} → Value {Z₀ = Z₀} (X `× Y) → Value {Z₀ = Z₀} X
proj₁-val (pairᵛ W₁ W₂) = W₁

proj₂-val : {Z₀ : Ty} → Value {Z₀ = Z₀} (X `× Y) → Value {Z₀ = Z₀} Y
proj₂-val (pairᵛ W₁ W₂) = W₂

pair-val : {Z₀ : Ty} → (W : Value {Z₀ = Z₀} (X `× Y)) → (pairᵛ (proj₁-val W) (proj₂-val W) ≡ W)
pair-val (pairᵛ W₁ W₂) = refl

---------------------------------------------------------------------------------
-- MACHINE FOR EFFECTFUL TERMS / COMPUTATIONS

\end{code}
%<*CStates>
\begin{code}

data CState {Z₀ : Ty} : Set where

  ⟨_╎_⟩ :    (Ẇ : Value {Z₀ = Z₀} X) → (cstack : CStack {Z₀ = Z₀} X)
             ---------------------------------------------------
             → CState {Z₀ = Z₀}

  ⟨_╎_╎_⟩ :  (M : Comp Γ X) → (γ : Env {Z₀ = Z₀} Γ) → (cstack : CStack {Z₀ = Z₀} X)
             -----------------------------------------------------------------
             → CState {Z₀ = Z₀}

\end{code}
%</CStates>

%<*Eval>
\begin{code}
jump-to-state : {Z₀ : Ty} → Value {Z₀ = Z₀} `L → CState {Z₀ = Z₀}
jump-to-state (jumpᵛ M γ k) = ⟨ M ╎ γ ╎ k ⟩

clo-to-comp :  {Z₀ : Ty} → Value {Z₀ = Z₀} (X `⇒ Y)
               → Σ[ Γ ∈ Ctx ] Comp (Γ ∙ X) Y × Env {Z₀ = Z₀} Γ
clo-to-comp (cloᵛ M γ) = _ , M , γ

eval : {Z₀ : Ty} → Pure Γ X → Env {Z₀ = Z₀} Γ → Value {Z₀ = Z₀} X
eval (var i) γ = lookup i γ
eval (lam M) γ = cloᵛ M γ
eval (pair W₁ W₂) γ = pairᵛ (eval W₁ γ) (eval W₂ γ)
eval unit γ = unitᵛ

eval-jump : {Z₀ : Ty} → Pure Γ `L → Env {Z₀ = Z₀} Γ → CState {Z₀ = Z₀}
eval-jump W γ = jump-to-state (eval W γ)

eval-clo :  {Z₀ : Ty} → Pure Γ (X `⇒ Y) → Pure Γ X → Env {Z₀ = Z₀} Γ
            → CStack {Z₀ = Z₀} Y → CState {Z₀ = Z₀}
eval-clo W₁ W₂ γ k =
  let
    M  = proj₁ (proj₂ (clo-to-comp (eval W₁ γ)))
    γ' = proj₂ (proj₂ (clo-to-comp (eval W₁ γ)))
  in
  ⟨ M ╎ γ' · eval W₂ γ ╎ k  ⟩

eval₁ : {Z₀ : Ty} → Pure Γ (X₁ `× X₂) → Env {Z₀ = Z₀} Γ → Value {Z₀ = Z₀} X₁
eval₁ W γ = proj₁-val (eval W γ)

eval₂ : {Z₀ : Ty} → Pure Γ (X₁ `× X₂) → Env {Z₀ = Z₀} Γ → Value {Z₀ = Z₀} X₂
eval₂ W γ = proj₂-val (eval W γ)
\end{code}
%</Eval>
\begin{code}

clo-val : {Z₀ : Ty} → (W : Value {Z₀ = Z₀} (X `⇒ Y)) → (cloᵛ (proj₁ (proj₂ (clo-to-comp W))) (proj₂ (proj₂ (clo-to-comp W))) ≡ W)
clo-val (cloᵛ M γ) = refl

\end{code}

%<*CTrans>
\begin{code}

data _→ᶜ_ {Z₀ : Ty} : CState {Z₀ = Z₀} → CState {Z₀ = Z₀} → Set where

  eval→ :    {W : Pure Γ X} {γ : Env Γ} {cstack : CStack X}
             -------------------------------------------
             →  ⟨ return W ╎ γ ╎ cstack ⟩ →ᶜ ⟨ eval W γ ╎ cstack ⟩

  return→ :  {Ẇ : Value X} {M : Comp (Γ ∙ X) Y} {γ : Env Γ} {cstack : CStack Y}
             --------------------------------------------------------------
             →  ⟨ Ẇ ╎ < M ； γ >∷ cstack ⟩ →ᶜ ⟨ M ╎ γ · Ẇ ╎ cstack ⟩

  push→ :    {M₁ : Comp Γ X} {M₂ : Comp (Γ ∙ X) Y} {γ : Env Γ} {cstack : CStack Y}
             ----------------------------------------------------------------
             →  ⟨ push M₁ M₂ ╎ γ ╎ cstack ⟩ →ᶜ ⟨ M₁ ╎ γ ╎ < M₂ ； γ >∷ cstack ⟩

  sub→ :     {M₁ : Comp (Γ ∙ `L) X} {M₂ : Comp Γ X} {γ : Env Γ} {cstack : CStack X}
             ----------------------------------------------------------------
             →  ⟨ sub M₁ M₂ ╎ γ ╎ cstack ⟩ →ᶜ ⟨ M₁ ╎ γ · (jumpᵛ M₂ γ cstack) ╎ cstack ⟩

  var→ :     {W : Pure Γ `L} {γ : Env Γ} {cstack : CStack X}
             ------------------------------------------
             →  ⟨ var W ╎ γ ╎ cstack ⟩ →ᶜ eval-jump W γ

  pmᶜ→ :     {W : Pure Γ (X `× Y)} {γ : Env Γ}
             {M : Comp (Γ ∙ X ∙ Y) Z} {cstack : CStack Z}
             -------------------------------------------------------------
             →  ⟨ pm W M ╎ γ ╎ cstack ⟩ →ᶜ ⟨ M ╎ γ · eval₁ W γ · eval₂ W γ ╎ cstack ⟩

  app→ :     {W₁ : Pure Γ (X `⇒ Y)} {W₂ : Pure Γ X} {γ : Env Γ} {cstack : CStack Y}
             ----------------------------------------------------------------
             →  ⟨ app W₁ W₂ ╎ γ ╎ cstack ⟩ →ᶜ eval-clo W₁ W₂ γ cstack

\end{code}
%</CTrans>
\begin{code}


determinismꟲ : {Z₀ : Ty} {S S' : CState {Z₀ = Z₀}} (S→S'₁ S→S'₂ : S →ᶜ S') → (S→S'₁ ≡ S→S'₂)
determinismꟲ eval→ eval→ = refl
determinismꟲ return→ return→ = refl
determinismꟲ push→ push→ = refl
determinismꟲ sub→ sub→ = refl
determinismꟲ var→ var→ = refl
determinismꟲ pmᶜ→ pmᶜ→ = refl
determinismꟲ app→ app→ = refl

open Inception.Prelude.RTC renaming (_~>⟨_⟩_ to _→ᶜ⟨_⟩_)

_→ᶜ*_ : {Z₀ : Ty} → CState {Z₀ = Z₀} → CState {Z₀ = Z₀} → Set
_→ᶜ*_ {Z₀ = Z₀} = _~>*_ (_→ᶜ_ {Z₀ = Z₀})

_⨾ᶜ_ : {Z₀ : Ty} → {F S T : CState {Z₀ = Z₀}} → (F →ᶜ* S) → (S →ᶜ* T) → (F →ᶜ* T)
_⨾ᶜ_ (S ◼) S>>T = S>>T
_⨾ᶜ_ (F →ᶜ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᶜ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ᶜ S₂>>T)


\end{code}
%<*SubVarSN>
\begin{code}
data SN {Z₀ : Ty} (σ : CState {Z₀ = Z₀}) : Set where
  sn : (∀ {σ'} → σ →ᶜ σ' → SN σ') → SN σ
\end{code}
%</SubVarSN>
\begin{code}

Rᵛ : {Z₀ : Ty} → (X : Ty) → Value {Z₀ = Z₀} X → Set
Rᵏ : {Z₀ : Ty} → (X : Ty) → CStack {Z₀ = Z₀} X → Set

Rᵛ `Unit unitᵛ = ⊤
Rᵛ (X `× Y) (pairᵛ W₁ W₂) = Rᵛ X W₁ × Rᵛ Y W₂
Rᵛ {Z₀ = Z₀} (X `⇒ Y) (cloᵛ M γ) = ∀ {W' : Value {Z₀ = Z₀} X} → Rᵛ X W' → ∀ {cstack : CStack {Z₀ = Z₀} Y} → Rᵏ Y cstack → SN ⟨ M ╎ γ · W' ╎ cstack ⟩
Rᵛ `L (jumpᵛ M γ cstack) = SN ⟨ M ╎ γ ╎ cstack ⟩

Rᵏ {Z₀ = Z₀} X cstack = ∀ {W : Value {Z₀ = Z₀} X} → Rᵛ X W → SN ⟨ W ╎ cstack ⟩

Rᴱ : {Z₀ : Ty} → Env {Z₀ = Z₀} Γ → Set
Rᴱ {Γ = Γ} γ = ∀ {X : Ty} → (i : Γ ∋ X) → Rᵛ X (lookup i γ)

Rᴱ-ext : {Z₀ : Ty} {γ : Env {Z₀ = Z₀} Γ} {W : Value {Z₀ = Z₀} X} → Rᴱ γ → Rᵛ X W → Rᴱ (γ · W)
Rᴱ-ext Rγ RW here = RW
Rᴱ-ext Rγ RW (there i) = Rγ i

rv≡sn : {Z₀ : Ty} → (Ẇ : Value {Z₀ = Z₀} `L) → Rᵛ `L Ẇ ≡ SN (jump-to-state Ẇ)
rv≡sn (jumpᵛ _ _ _) = refl

mutual

  fundamentalᵖ  : {Z₀ : Ty} → (W : Pure Γ X) → {γ : Env {Z₀ = Z₀} Γ} → Rᴱ γ → Rᵛ X (eval W γ)
  fundamentalᵖ (var i) Rγ = Rγ i
  fundamentalᵖ (lam M) Rγ RW Rk = fundamentalᶜ M (Rᴱ-ext Rγ RW) Rk
  fundamentalᵖ (pair W₁ W₂) Rγ = (fundamentalᵖ W₁ Rγ) , (fundamentalᵖ W₂ Rγ)
  fundamentalᵖ unit Rγ = tt

  fundamentalᶜ : {Z₀ : Ty} → (M : Comp Γ X) → {γ : Env {Z₀ = Z₀} Γ} → Rᴱ γ → {cstack : CStack {Z₀ = Z₀} X} → Rᵏ X cstack → SN ⟨ M ╎ γ ╎ cstack ⟩
  fundamentalᶜ (return W) Rγ Rk = sn λ { eval→ → Rk (fundamentalᵖ W Rγ)}
  fundamentalᶜ (pm W M) {γ = γ} Rγ Rk =
    let
      IH = fundamentalᵖ W Rγ
      W' = eval W γ
      IH' : Rᵛ _ (pairᵛ (proj₁-val W') (proj₂-val W'))
      IH' = subst (λ x → Rᵛ _ x) (sym (pair-val W')) IH
    in
    sn λ { pmᶜ→ → fundamentalᶜ M (Rᴱ-ext (Rᴱ-ext Rγ (proj₁ IH')) (proj₂ IH')) Rk }
  fundamentalᶜ (push M₁ M₂) {γ = γ} Rγ {cstack = k} Rk =
    let
      Rk' : Rᵏ _ (< M₂ ； γ >∷ k)
      Rk' RW = sn (λ { return→ → fundamentalᶜ M₂ (Rᴱ-ext Rγ RW) Rk })
    in
    sn λ { push→ → fundamentalᶜ M₁ Rγ Rk' }
  fundamentalᶜ (app W₁ W₂) {γ = γ} Rγ {cstack = k} Rk =
    let
      IH = fundamentalᵖ W₁ Rγ
      W₁' = eval W₁ γ
      eq = sym (clo-val W₁')
      IH' = subst (λ x → Rᵛ _ x) eq IH
    in
    sn λ { app→ → IH' (fundamentalᵖ W₂ Rγ) Rk }
  fundamentalᶜ (var W) {γ = γ} Rγ Rk = sn λ { var→ → subst (λ x → x) (rv≡sn (eval W γ)) (fundamentalᵖ W Rγ)}
  fundamentalᶜ (sub M₁ M₂) Rγ Rk = sn λ { sub→ → fundamentalᶜ M₁ (Rᴱ-ext Rγ (fundamentalᶜ M₂ Rγ Rk)) Rk}

Rᴱ-⊘ : {Z₀ : Ty} → Rᴱ {Z₀ = Z₀} ⋄
Rᴱ-⊘ = λ ()

Rᵏ-◻ : {Z₀ : Ty} → Rᵏ {Z₀ = Z₀} Z₀ ◻
Rᵏ-◻ RW = sn λ {σ'} ()

SN-theorem : {Z₀ : Ty} → (M : Comp ε Z₀) → SN {Z₀ = Z₀} ⟨ M ╎ ⋄ ╎ ◻ ⟩
SN-theorem M = fundamentalᶜ M Rᴱ-⊘ Rᵏ-◻

\end{code}
%<*SubVarNormal>
\begin{code}
-- A CState is Normal, if there are no transitions from it.
Normal : {Z₀ : Ty} → CState {Z₀ = Z₀} → Set
Normal cstate₁ = ∀ {cstate₂} → cstate₁ →ᶜ cstate₂ → ⊥
\end{code}
%</SubVarNormal>
\begin{code}

data Progress {Z₀ : Ty} (σ : CState {Z₀ = Z₀}) : Set where
  done : Normal σ → Progress σ
  step : {σ' : CState} → σ →ᶜ σ' → Progress σ

progress : {Z₀ : Ty} (σ : CState {Z₀ = Z₀}) → Progress σ
progress ⟨ W' ╎ ◻ ⟩ = done (λ ())
progress ⟨ W' ╎ < M ； γ >∷ cstack ⟩ = step return→
progress ⟨ return W ╎ γ ╎ cstack ⟩ = step eval→
progress ⟨ pm W M ╎ γ ╎ cstack ⟩ = step pmᶜ→
progress ⟨ push M₁ M₂ ╎ γ ╎ cstack ⟩ = step push→
progress ⟨ app W₁ W₂ ╎ γ ╎ cstack ⟩ = step app→
progress ⟨ var W ╎ γ ╎ cstack ⟩ = step var→
progress ⟨ sub M₁ M₂ ╎ γ ╎ cstack ⟩ = step sub→

\end{code}
%<*SubVarHaltingState>
\begin{code}
-- A Normal CState is a halting state and of the form ⟨ 𝐖 ╎ ◻ ⟩.
halting-state :    (cstate : CState {Z₀ = Z₀}) → Normal cstate
                 → Σ[ 𝐖 ∈ Value Z₀ ] cstate ≡ ⟨ 𝐖 ╎ ◻ ⟩

-- ...
\end{code}
%</SubVarHaltingState>
\begin{code}

halting-state ⟨ W' ╎ ◻ ⟩ normal = W' , refl
halting-state ⟨ W' ╎ < x ； γ >∷ cstack ⟩ normal = ql (normal return→) _
halting-state ⟨ return _ ╎ γ ╎ cstack ⟩ normal = ql (normal eval→) _
halting-state ⟨ pm _ _ ╎ γ ╎ cstack ⟩ normal = ql (normal pmᶜ→) _
halting-state ⟨ push _ _ ╎ γ ╎ cstack ⟩ normal = ql (normal push→) _
halting-state ⟨ app _ _ ╎ γ ╎ cstack ⟩ normal = ql (normal app→) _
halting-state ⟨ var _ ╎ γ ╎ cstack ⟩ normal = ql (normal var→) _
halting-state ⟨ sub _ _ ╎ γ ╎ cstack ⟩ normal = ql (normal sub→) _


exec-acc : {Z₀ : Ty} {σ : CState {Z₀ = Z₀}} → SN σ → Σ[ σ' ∈ CState ] Σ[ W' ∈ Value {Z₀ = Z₀} Z₀ ] Σ[ NF ∈ Normal σ' ] (σ →ᶜ* σ') × (W' ≡ proj₁ (halting-state σ' NF))
exec-acc {σ = σ} (sn f) with progress σ
... | done NF    = σ , proj₁ (halting-state σ NF) , NF , (σ ◼) , refl
... | step S→S' with exec-acc (f S→S')
...   | (σ'' , W' , NF , S'→*S'' , eq) = σ'' , W' , NF , (_ →ᶜ⟨ S→S' ⟩ S'→*S'') , eq

\end{code}
%<*SubVarEval>
\begin{code}
exec :    {Z₀ : Ty} → (M : Comp ε Z₀)
        → Σ[ cstate ∈ CState ]
          Σ[ 𝐖 ∈ Value {Z₀ = Z₀} Z₀ ]
          Σ[ NF ∈ Normal cstate ]
          (⟨ M ╎ ⋄ ╎ ◻ ⟩ →ᶜ* cstate) × (𝐖 ≡ proj₁ (halting-state cstate NF))

-- ...
\end{code}
%</SubVarEval>
\begin{code}

exec M = exec-acc (SN-theorem M)

---------------------------------------------------------------------------------
-- EXAMPLES

ex15 : ε ⊢ᶜ (`Unit)
ex15 = push (push (app (lam {X = `Unit} (sub (var (var here)) (return unit))) unit) (return unit)) (return unit)

_ : exec ex15 ≡ (_ , unitᵛ , _ ,
                  (⟨ push (push (app (lam (sub (var (var here)) (return unit))) unit) (return unit)) (return unit) ╎ ⋄ ╎ ◻ ⟩
    →ᶜ⟨ push→ ⟩   (⟨ push (app (lam (sub (var (var here)) (return unit))) unit) (return unit) ╎ ⋄ ╎ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ push→ ⟩   (⟨ app (lam (sub (var (var here)) (return unit))) unit ╎ ⋄ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ app→ ⟩    (⟨ sub (var (var here)) (return unit) ╎ ⋄ · unitᵛ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ sub→ ⟩    (⟨ var (var here) ╎ ⋄ · unitᵛ · jumpᵛ (return unit) (⋄ · unitᵛ) (< return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻) ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ var→ ⟩    (⟨ return unit ╎ ⋄ · unitᵛ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ eval→ ⟩ (⟨ unitᵛ ╎ < return unit ； ⋄ >∷ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ return→ ⟩ (⟨ return unit ╎ ⋄ · unitᵛ ╎ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ eval→ ⟩ (⟨ unitᵛ ╎ < return unit ； ⋄ >∷ ◻ ⟩
    →ᶜ⟨ return→ ⟩ (⟨ return unit ╎ ⋄ · unitᵛ ╎ ◻ ⟩
    →ᶜ⟨ eval→ ⟩ (⟨ unitᵛ ╎ ◻ ⟩ ◼)))))))))))
    , _)
_ = refl

\end{code}
