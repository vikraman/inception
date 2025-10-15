module Inception.Sub.CompMachine (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Unit
open import Data.Nat

module CMain {R₀ : Ty} (k₀ : ⟦ R₀ ⟧ → R) where

  open import Inception.Sub.ValueMachine R

  open VMain {R₀ = R₀} k₀

  infixr 15 _→ᶜ⟨_⟩_
  infix  15 _→ᶜ*_
  infixr 10 _⨾ᶜ_

  -- Computation Machine
  --------------------------------------------------


  data C̲o̲m̲p : Ctx → Ty → Set
  data C̲o̲m̲p where

      r̲e̲t̲u̲r̲n̲ : V̲a̲l̲ Γ X → C̲o̲m̲p Γ X

      a̲pp    : Γ ⊢ᵛ X `⇒ Y -> V̲a̲l̲ Γ X -> C̲o̲m̲p Γ Y

  wk-c̲o̲m̲p : Wk Γ Δ → C̲o̲m̲p Δ X → C̲o̲m̲p Γ X
  wk-c̲o̲m̲p π (r̲e̲t̲u̲r̲n̲ M) = r̲e̲t̲u̲r̲n̲ (wk-v̲a̲l̲ π M)
  wk-c̲o̲m̲p π (a̲pp M N) = a̲pp (wk-val π M) (wk-v̲a̲l̲ π N)

  data CompState : Set
  data CompState where

        ∘⟨_⊰_╎_⟩ : (W : Γ ⊢ᶜ X) → Env Γ → (cs : CompStack X) → CompState

        ∙⟨_⊰_╎_⟩ : (W : C̲o̲m̲p Γ X) → Env Γ → (cs : CompStack X) → CompState

  data _→ᶜ*_ : CompState → CompState → Set
  data _→ᶜ_ : CompState → CompState → Set

  data CompHaltingState {X : Ty} (cs : CompStack X) : CompState → Set where

      ret : {M : V̲a̲l̲ Γ X} → {γ : Env Γ} → CompHaltingState cs (∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ ╎ cs ⟩)

  ---

  data _→ᶜ_  where

        ∘return  :    {M : Γ ⊢ᵛ X} → {γ : Env Γ'} → {π : Wk Γ' Γ} → {M' : V̲a̲l̲ Γ'' X} → {γ' : Env Γ''} → {cs : CompStack X}
                      → ((∘ ((⇡ wk-val π M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ M' ⊲ γ' ∷ □) {↥ = 🗆})))
                  ----------------------------------------------------------------
                    → ∘⟨ wk-comp π (return M) ⊰ γ ╎ cs ⟩ →ᶜ ∙⟨ r̲e̲t̲u̲r̲n̲ M' ⊰ γ' ╎ cs ⟩

        ∙return  :    {M : V̲a̲l̲ Γ X} → {γ : Env Γ} → {N : (Γ' ∙ X) ⊢ᶜ Y} → {γ' : Env Γ'} → {π : Wk Γ Γ'} → {cs : CompStack Y}
                  ----------------------------------------------------------------
                    → ∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ ╎ N ⊲ γ' ⦂⦂ cs ⟩ →ᶜ ∘⟨ wk-comp (wk-cong π) N ⊰ γ ﹐ M ╎ cs ⟩

        ∘push    :    {M : Γ ⊢ᶜ X} → {N : (Γ ∙ X) ⊢ᶜ Y} → {γ : Env Γ} → {cs : CompStack Y}
                  ----------------------------------------------------------------
                    → ∘⟨ push M N ⊰ γ ╎ cs ⟩ →ᶜ ∘⟨ M ⊰ γ ╎ N ⊲ γ ⦂⦂ cs ⟩

        ∘sub     :    {M : (Γ ∙ `V) ⊢ᶜ X} → {N : Γ ⊢ᶜ X} → {γ : Env Γ} → {cs : CompStack X}
                  ----------------------------------------------------------------
                    → ∘⟨ sub M N ⊰ γ ╎ cs ⟩ →ᶜ ∘⟨ M ⊰ γ ﹐﹝ N ╎ cs ﹞ ╎ cs ⟩

        ∘pm      :    {M : Γ' ⊢ᵛ X `× Y} → {γ : Env Γ} → {W : (Γ' ∙ X ∙ Y) ⊢ᶜ Z} → {cs : CompStack Z}
                    → {LHS : V̲a̲l̲ Γ'' X} → {RHS : V̲a̲l̲ Γ'' Y} → {γ'' : Env Γ''} → (π : Wk Γ Γ')
                    → ((∘ ((⇡ wk-val π M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ'' ∷ □) {↥ = 🗆}))) → (π' : Wk Γ'' Γ)
                  ----------------------------------------------------------------
                    → ∘⟨ pm (wk-val π M) (wk-comp (wk-cong (wk-cong π)) W) ⊰ γ ╎ cs ⟩ →ᶜ ∘⟨ wk-comp (wk-cong (wk-cong π')) (wk-comp (wk-cong (wk-cong π)) W) ⊰ γ' ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ╎ cs ⟩

        ∙app-var     :    {i : Γ ∋ (Z' `⇒ Z)} → {N : V̲a̲l̲ Γ Z'} → {γ : Env Γ} → {cs : CompStack Z}
                       → {W : (Γ' ∙ Z') ⊢ᶜ Z} → {γ' : Env Γ'}
                       → (⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ _﹐_ γ' (l̲a̲m̲ W) ⟩) → (πᵥ : Wk Γ Γ')
                     ----------------------------------------------------------------
                       → ∙⟨ a̲pp (var i) N ⊰ γ ╎ cs ⟩ →ᶜ ∙⟨ a̲pp (wk-val πᵥ (lam W)) N ⊰ γ ╎ cs ⟩

        ∙app-pm     :    {M : Γ ⊢ᵛ (X `× Y)} → {W : (Γ ∙ X ∙ Y) ⊢ᵛ (Z' `⇒ Z)} → {N : V̲a̲l̲ Γ Z'} → {γ : Env Γ} → {cs : CompStack Z}
                       → {LHS : V̲a̲l̲ Γ' X} → {RHS : V̲a̲l̲ Γ' Y} → {γ' : Env Γ'}
                       → ((∘ ((⇡ M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ' ∷ □) {↥ = 🗆}))) → (π : Wk Γ' Γ)
                     ----------------------------------------------------------------
                       → ∙⟨ a̲pp (pm M W) N ⊰ γ ╎ cs ⟩ →ᶜ ∙⟨ a̲pp ((wk-val (wk-cong (wk-cong π)) W)) (wk-v̲a̲l̲ (wk-wk (wk-wk π)) N) ⊰ γ' ﹐ LHS ﹐ (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ╎ cs ⟩

        ∙app-lam     :   {W : (Γ ∙ X) ⊢ᶜ Y} → {N : V̲a̲l̲ Γ X} → {γ : Env Γ} → {cs : CompStack Y}
                     ----------------------------------------------------------------
                       → ∙⟨ a̲pp (lam W) N ⊰ γ ╎ cs ⟩ →ᶜ ∘⟨ W ⊰ γ ﹐ N ╎ cs ⟩

        ∘app         :   {M : Γ ⊢ᵛ X `⇒ Y} → {N : Γ ⊢ᵛ X} → {γ : Env Γ} → {cs : CompStack Y}
                       → {N' : V̲a̲l̲ Γ' X} → {γ' : Env Γ'}
                       → ((∘ ((⇡ N ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ N' ⊲ γ' ∷ □) {↥ = 🗆}))) → (π : Wk Γ' Γ)
                     ----------------------------------------------------------------
                       → ∘⟨ app M N ⊰ γ ╎ cs ⟩ →ᶜ ∙⟨ a̲pp (wk-val π M) N' ⊰ γ' ╎ cs ⟩


        ∘var     :   {a : Γ ⊢ᵛ `V} → {γ : Env Γ} → {i : Γ' ∋ `V} → {γ' : Env Γ'} → {W : Γ'' ⊢ᶜ X} → {γ'' : Env Γ''} → {cs : CompStack `V} → {cs' : CompStack X}
                  → ((∘ ((⇡ wk-val wk-id a ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ v̲a̲r̲ i ⊲ γ' ∷ □) {↥ = 🗆}))) → (π' : Wk Γ' Γ)
                  → (⟨ i ∥ γ' ⟩ →ᴸ* ⟨ h ∥ γ'' ﹐﹝ W ╎ cs' ﹞ ⟩) → (πᵥ : Wk Γ'' Γ')
                  ----------------------------------------------------------------
                    → ∘⟨ var a ⊰ γ ╎ cs ⟩ →ᶜ ∘⟨ W ⊰ γ'' ╎ cs' ⟩

  data _→ᶜ*_ where

    _◼ : (S : CompState) → S →ᶜ* S

    _→ᶜ⟨_⟩_ : (S : CompState) → {S' S'' : CompState} → S →ᶜ S' → S' →ᶜ* S'' → S →ᶜ* S''

  _⨾ᶜ_ : {F S T : CompState} → (F →ᶜ* S) → (S →ᶜ* T) → (F →ᶜ* T)
  _⨾ᶜ_ (S ◼) S>>T = S>>T
  _⨾ᶜ_ (F →ᶜ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᶜ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ᶜ S₂>>T)

  -- data Wrapper : Ctx → Ty → Ty → Set where

  --      empty-wrapper : Wrapper Γ X X

  --      app-wrapper : (N : V̲a̲l̲ Γ X) → Wrapper Γ (X `⇒ Y) Y

  -- wrap : (W : Γ' ⊢ᶜ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Y) → (w : Wrapper Γ' X Y) → CompState
  -- wrap W γ π cs empty-wrapper = ∘⟨ wk-comp π W ⊰ γ ╎ cs ⟩
  -- wrap W γ π cs (app-wrapper N) = {!∙⟨ a̲pp (wk-val ? W) (wk-v̲a̲l̲ ? N) ⊰ γ ╎ cs ⟩!}

  {-
  wk-v̲a̲l̲-trans : (M : V̲a̲l̲ Γ A) → (π₁ : Wk Ψ Δ) → (π₂ : Wk Δ Γ) → wk-v̲a̲l̲ π₁ (wk-v̲a̲l̲ π₂ M) ≡ wk-v̲a̲l̲ (wk-trans π₁ π₂) M
  wk-v̲a̲l̲-trans (l̲a̲m̲ W) π₁ π₂ = cong l̲a̲m̲ (wk-comp-trans W (wk-cong π₁) (wk-cong π₂))
  wk-v̲a̲l̲-trans (pa̲i̲r̲ LHS RHS) π₁ π₂ =
                             pa̲i̲r̲ (wk-v̲a̲l̲ π₁ (wk-v̲a̲l̲ π₂ LHS)) (wk-v̲a̲l̲ π₁ (wk-v̲a̲l̲ π₂ RHS))
                            ≡⟨ cong (λ x → pa̲i̲r̲ (wk-v̲a̲l̲ π₁ (wk-v̲a̲l̲ π₂ LHS)) x) (wk-v̲a̲l̲-trans RHS π₁ π₂) ⟩
                             pa̲i̲r̲ (wk-v̲a̲l̲ π₁ (wk-v̲a̲l̲ π₂ LHS)) (wk-v̲a̲l̲ (wk-trans π₁ π₂) RHS)
                            ≡⟨ cong (λ x → pa̲i̲r̲ x (wk-v̲a̲l̲ (wk-trans π₁ π₂) RHS)) (wk-v̲a̲l̲-trans LHS π₁ π₂) ⟩
                             pa̲i̲r̲ (wk-v̲a̲l̲ (wk-trans π₁ π₂) LHS) (wk-v̲a̲l̲ (wk-trans π₁ π₂) RHS) ∎
  wk-v̲a̲l̲-trans u̲n̲i̲t̲ π₁ π₂ = refl
  wk-v̲a̲l̲-trans (v̲a̲r̲ i) π₁ π₂ = cong v̲a̲r̲ (wk-mem-trans i π₁ π₂)

  wk-trans-id : {π : Wk Δ Γ} → wk-trans π wk-id ≡ π
  wk-trans-id {π = wk-ε} = refl
  wk-trans-id {π = wk-cong π} = cong wk-cong wk-trans-id
  wk-trans-id {π = wk-wk π} = cong wk-wk wk-trans-id

  wk-id-trans : {π : Wk Δ Γ} → wk-trans wk-id π ≡ π
  wk-id-trans {π = wk-ε} = refl
  wk-id-trans {π = wk-cong π} = cong wk-cong wk-id-trans
  wk-id-trans {π = wk-wk π} = cong wk-wk wk-id-trans

  val-count-vars : Γ ⊢ᵛ X → ℕ
  comp-count-vars : Γ ⊢ᶜ X → ℕ

  val-count-vars (var i) = 1
  val-count-vars (lam W) = comp-count-vars W
  val-count-vars (pair LHS RHS) = (val-count-vars LHS) + (val-count-vars RHS)
  val-count-vars (pm M N) = (val-count-vars M) + (val-count-vars N)
  val-count-vars unit = 0

  v̲a̲l̲-count-vars :  V̲a̲l̲ Γ X → ℕ
  v̲a̲l̲-count-vars (l̲a̲m̲ M) = comp-count-vars M
  v̲a̲l̲-count-vars (pa̲i̲r̲ LHS RHS) = (v̲a̲l̲-count-vars LHS) + (v̲a̲l̲-count-vars RHS)
  v̲a̲l̲-count-vars u̲n̲i̲t̲ = 0
  v̲a̲l̲-count-vars (v̲a̲r̲ i) = 1

  comp-count-vars (return M) = val-count-vars M
  comp-count-vars (pm M W) = (val-count-vars M) + (comp-count-vars W)
  comp-count-vars (push W₁ W₂) = (comp-count-vars W₁) + (comp-count-vars W₂)
  comp-count-vars (app M N) = (val-count-vars M) + (val-count-vars N)
  comp-count-vars (var M) = val-count-vars M
  comp-count-vars (sub W₁ W₂) = (comp-count-vars W₁) + (comp-count-vars W₂)

  env-count-vars : Env Γ → ℕ
  cs-count-vars : CompStack X → ℕ

  env-count-vars ∗ = 0
  env-count-vars (γ ﹐ M) = (env-count-vars γ) + (v̲a̲l̲-count-vars M)
  env-count-vars (γ ﹐﹝ W ╎ cs ﹞) = (env-count-vars γ) + (comp-count-vars W) + (cs-count-vars cs)

  cs-count-vars ◻ = 0
  cs-count-vars (W ⊲ γ ⦂⦂ cs) = (comp-count-vars W) + (env-count-vars γ) + (cs-count-vars cs)

  ≤-trans : {a : ℕ} → {b : ℕ} → {c : ℕ} → (a ≤ b) → (b ≤ c) → (a ≤ c)
  ≤-trans {zero} _ _ = z≤n
  ≤-trans (s≤s a≤b) (s≤s b≤c) = s≤s (≤-trans a≤b b≤c)

  n≤sn : {n : ℕ} → n ≤ suc n
  n≤sn {n = zero} = z≤n
  n≤sn {n = suc n} = s≤s n≤sn

  m₂≤n : {m₁ : ℕ} → {m₂ : ℕ} → {n : ℕ} → m₁ + m₂ ≤ n → m₂ ≤ n
  m₂≤n {zero} {m₂} {n} m₁+m₂≤n = m₁+m₂≤n
  m₂≤n {suc m₁} {zero} {suc n} (s≤s m₁+m₂≤n) = z≤n
  m₂≤n {suc m₁} {suc m₂} {suc n} (s≤s m₁+m₂≤n) = ≤-trans (m₂≤n m₁+m₂≤n) n≤sn
  -}

  topCompCtx : CompState → Ctx
  topCompCtx (∘⟨_⊰_╎_⟩ {Γ = Γ} _ _ _) = Γ
  topCompCtx (∙⟨_⊰_╎_⟩ {Γ = Γ} _ _ _) = Γ

  {-
  topCompTy : (Q : CompState) → Ty
  topCompTy (∘⟨_⊰_╎_⟩ {X = X} _ _ _) = X
  topCompTy (∙⟨_⊰_╎_⟩ {X = X} _ _ _) = X

  topCompTerm : (Q : CompState) → (topCompCtx Q) ⊢ᶜ (topCompTy Q)
  topCompTerm ∘⟨ W ⊰ x ╎ cs ⟩ = W
  topCompTerm ∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ x ╎ cs ⟩ = return (toVal M)
  topCompTerm ∙⟨ a̲pp M N ⊰ x ╎ cs ⟩ = app M (toVal N)

  topCompEnv : (Q : CompState) → Env (topCompCtx Q)
  topCompEnv ∘⟨ W ⊰ γ ╎ cs ⟩ = γ
  topCompEnv ∙⟨ W ⊰ γ ╎ cs ⟩ = γ

  topCompCS : (Q : CompState) → CompStack (topCompTy Q)
  topCompCS ∘⟨ W ⊰ γ ╎ cs ⟩ = cs
  topCompCS ∙⟨ W ⊰ γ ╎ cs ⟩ = cs

  state-count-vars : CompState → ℕ
  state-count-vars Q = (comp-count-vars (topCompTerm Q)) + (env-count-vars (topCompEnv Q)) + (cs-count-vars (topCompCS Q))
  -}


  data CompSteps {X : Ty} (cs : CompStack X) : CompState → Set where

      steps : {S T : CompState} → S →ᶜ* T → CompHaltingState cs T → (π : Wk (topCompCtx T) (topCompCtx S)) → CompSteps {X = X} cs S

      -- out-of-gas : {S : CompState} → CompSteps {X = X} cs S

  {-
  mutual

    app-eval : (M : Γ' ⊢ᵛ X `⇒ Y) → (N : V̲a̲l̲ Γ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Y) → (n : ℕ) → CompSteps cs ∙⟨ (a̲pp (wk-val π M) N) ⊰ γ ╎ cs ⟩
    app-eval (var i) N γ π cs zero = {!!}
    app-eval (var i) N γ π cs (suc n) with lookup (wk-mem π i) γ
    ... | steps i>>T (found-lam {W = W} {γ = γ₁}) i≡T π₁ w≡γ with app-eval (lam W) N γ π₁ cs n
    ... | steps W>WT HT π' = steps (∙⟨ a̲pp (wk-val π (var i)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-var i>>T π₁ ⟩ W>WT) HT π'
    app-eval (lam W) N γ π cs n with comp-eval W (γ ﹐ N) (wk-cong π) cs n
    ... | steps W>WT HT π' rewrite (wk-comp-id W) = steps ( ∙⟨ a̲pp (wk-val π (lam W)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-lam ⟩ W>WT) HT (wk-trans π' (wk-wk wk-id))
    app-eval (pm M₁ N₁) N γ π cs n with val-eval-rec M₁ γ π
    ... | steps {T = ∙ (⭭ pa̲i̲r̲ {X = X} {Y = Y} LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ with wk-val-trans N₁ (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
    ...       | eq with app-eval N₁ ((wk-v̲a̲l̲ (wk-wk (wk-wk π')) N)) (γ₁ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS) (wk-cong (wk-cong (wk-trans π' π))) cs n
    ...          | steps N>NT NT π'' rewrite (sym eq) = --rewrite lem {Y = Y} {X = X} N π' π =

        steps
         (∙⟨ (a̲pp (wk-val π (pm M₁ N₁)) N) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-pm M>T π' ⟩ N>NT )
         NT
         (wk-trans π'' (wk-wk (wk-wk π')))


    comp-eval : (W : Γ' ⊢ᶜ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack X) → (n : ℕ) → CompSteps cs ∘⟨ wk-comp π W ⊰ γ ╎ cs ⟩
    comp-eval (return {A = X} M) γ π cs n with val-eval-rec {X = X} M γ π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ = steps (∘⟨ wk-comp π (return M) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘return M>T ⟩ (∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ cs ⟩ ◼)) ret π'

    comp-eval (pm {A = X} {B = Y} M W) γ π cs n with val-eval-rec {X = X `× Y} M γ π
    ...  | steps {T = ∙ ((⭭_ {X = X `× Y} (pa̲i̲r̲ LHS RHS) ⊲ γ' ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ with comp-eval W (γ' ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS) (wk-trans (wk-cong (wk-cong π')) (wk-cong (wk-cong π))) cs n
    ...   | steps W>T HT π₁ with wk-comp-trans W (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
    ...     | eq rewrite (sym eq) = steps (∘⟨ wk-comp π (pm M W) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘pm π M>T π' ⟩ W>T) HT (wk-trans π₁ (wk-wk (wk-wk π')))

    comp-eval (push W V) γ π cs n with comp-eval W γ π ((wk-comp (wk-cong π) V) ⊲ γ ⦂⦂ cs) n
    ... | steps {T = ∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ₁ ╎ .(wk-comp (wk-cong π) V ⊲ γ ⦂⦂ cs) ⟩} W>T ret π' with comp-eval V (γ₁ ﹐ M) (wk-trans (wk-cong π') (wk-cong π)) cs n
    ...    | steps {T = T} V>T ret π'' with wk-comp-trans V (wk-cong π') (wk-cong π)
    ...       | eq rewrite (sym eq) =

            steps
                  (  ∘⟨ push (wk-comp π W) (wk-comp (wk-cong π) V) ⊰ γ ╎ cs ⟩  →ᶜ⟨ ∘push ⟩ W>T ⨾ᶜ
                    ∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ₁ ╎ wk-comp (wk-cong π) V ⊲ γ ⦂⦂ cs ⟩       →ᶜ⟨ ∙return ⟩ V>T )
                  ret
                  (wk-trans π'' (wk-wk π'))

    comp-eval (app (var i) N) γ π cs zero = {!!}
    comp-eval (app (var i) N) γ π cs (suc n)  with val-eval-rec N γ π
    ... | steps {T = ∙ ((⭭_ NT ⊲ γᴺ ∷ □) {↥ = 🗆})} N>NT ∙NT N≡NT πᴺ wk≡ᴺ with app-eval (var i) NT γᴺ (wk-trans πᴺ π) cs n
    ... | steps W>WT HT πᵂ rewrite (sym (wk-mem-trans i πᴺ π))= -- {!!}
            steps

                ((∘⟨ app (wk-val π (var i)) (wk-val π N) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘app N>NT πᴺ ⟩ W>WT ))
                HT
                (wk-trans πᵂ πᴺ) --(wk-trans πᵂ πᴺ)

    comp-eval (app (pm M₁ N₁) N) γ π cs n with val-eval-rec N γ π
    ... | steps {T = ∙ ((⭭_ NT ⊲ γᴺ ∷ □) {↥ = 🗆})} N>NT ∙NT N≡NT πᴺ wk≡ᴺ with app-eval (pm M₁ N₁) NT γᴺ (wk-trans πᴺ π) cs n
    ... | steps W>WT HT πᵂ with wk-val-trans N₁ (wk-cong (wk-cong πᴺ)) (wk-cong (wk-cong π))
    ... | eq rewrite (sym eq) rewrite (sym (wk-val-trans M₁ πᴺ π)) =
            steps

                ((∘⟨ app (wk-val π (pm M₁ N₁)) (wk-val π N) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘app N>NT πᴺ ⟩ W>WT ))
                HT
                (wk-trans πᵂ πᴺ)

    comp-eval (app (lam W) N) γ π cs n with val-eval-rec N γ π
    ... | steps {T = ∙ ((⭭_ NT ⊲ γᴺ ∷ □) {↥ = 🗆})} N>NT ∙NT N≡NT πᴺ wk≡ᴺ with app-eval (lam W) NT γᴺ (wk-trans πᴺ π) cs n
    ... | steps W>WT HT πᵂ rewrite (sym (wk-comp-trans W (wk-cong πᴺ) (wk-cong π))) =

    -- with comp-eval W (γᴺ ﹐ NT) (wk-cong (wk-trans πᴺ π)) cs
    -- ...    | steps W>WT HT πᵂ with wk-comp-trans W (wk-cong πᴺ) (wk-cong π)
    -- ...       | eq rewrite (sym eq) =

            steps

                (∘⟨ app (wk-val π (lam W)) (wk-val π N) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘app N>NT πᴺ ⟩ W>WT ) --∙⟨ a̲pp (lam (wk-comp (wk-cong πᴺ) (wk-comp (wk-cong π) W))) NT ⊰ γᴺ ╎ cs ⟩ →ᶜ⟨ ∙app-lam ⟩ W>WT)
                HT
                (wk-trans πᵂ πᴺ) --(wk-trans πᵂ (wk-wk πᴺ))

    comp-eval (var M) γ π cs n =
              steps
               (∘⟨ var (wk-val π M) ⊰ γ ╎ cs ⟩ →ᶜ⟨ {!∘var ? ? ? ?!} ⟩ {!!})
               {!!}
               {!!}

    comp-eval (sub W V) γ π cs n with comp-eval W (γ ﹐﹝ wk-comp π V ╎ cs ﹞) (wk-cong π) cs n
    ... | steps W>WT HT πᵂ =
                steps
                    (∘⟨ sub (wk-comp (wk-cong π) W) (wk-comp π V) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘sub ⟩ W>WT)
                    HT
                    (wk-trans πᵂ (wk-wk wk-id))

  -}

  -- EXAMPLES
  --------------------------------------------------

  ex1 : ε ⊢ᵛ `Unit
  ex1 = pm (pair unit unit) (var (t h))

  ex2 : ε ⊢ᵛ `Unit `× `Unit
  ex2 = pm (pm (pair (lam {A = `Unit} {B = `Unit} (return (var h))) unit) (pair unit (var (t h)))) (pm (pair unit unit) (pair (var (t h)) (var (t (t (t h))))))

  ---------------------------------------

  -- calling agda2-compute-normalised in the hole below val-eval-recuates example
  -- _ : val-eval ex2 ≡ {!val-eval ex2!}
  -- _ = refl


  --------------------------------------------------------------
