module Inception.Sub.CompMachine (R : Set) where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Unit
open import Data.Nat

open import Inception.Sub.ValueMachine R

module CMain {R₀ : Ty} (k₀ : ⟦ R₀ ⟧ → R) where

  open VMain {R₀ = R₀} k₀

  data CompState : Set where

        ∘⟨_⊰_╎_⟩ : (W : Γ ⊢ᶜ X) → Env Γ → (cs : CompStack Δ X) → {π : Wk Γ Δ} → CompState

        ∙⟨_⊰_╎_⟩ : (W : C̲o̲m̲p Γ X) → Env Γ → (cs : CompStack Δ X) → {π : Wk Γ Δ} → CompState

  data CompHaltingState : CompState → Set where

      ret : {M : V̲a̲l̲ Γ R₀} → {γ : Env Γ} → CompHaltingState ((∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ ╎ ◻ ⟩) {π = wk-wk-ε})


  infixr 15 _→ᶜ⟨_⟩_
  infix  15 _→ᶜ*_
  infixr 10 _⨾ᶜ_

  -- not used currently
  ⟦_⟧ᴷ : (cs : CompStack Δ Y) → ⟦ Y ⟧ → R
  ⟦_⟧ᴷ cs y = ⟦ cs ⟧ᶜˢ (η y) k₀

  ⟦_⟧ᶜꟴ : CompState → K ⟦ R₀ ⟧
  ⟦ ∘⟨ W ⊰ γ ╎ cs ⟩ ⟧ᶜꟴ = ⟦ cs ⟧ᶜˢ (⟦ W ⟧ᶜ ⟦ γ ⟧ᴱ)
  ⟦ ∙⟨ W ⊰ γ ╎ cs ⟩ ⟧ᶜꟴ = ⟦ cs ⟧ᶜˢ (⟦ toComp W ⟧ᶜ ⟦ γ ⟧ᴱ)

  -- Computation Machine
  --------------------------------------------------

  data _→ᶜ*_ : CompState → CompState → Set
  data _→ᶜ_ : CompState → CompState → Set


  ---

  data _→ᶜ_  where

        ∘return  :    {M : Γ ⊢ᵛ X} → {γ : Env Γ'} → {π : Wk Γ' Γ} → {M' : V̲a̲l̲ Γ'' X} → {γ' : Env Γ''} → {cs : CompStack Δ X} → {πₓ : Wk Γ' Δ} → {πₓ' : Wk Γ'' Δ}
                      → ((∘ ((⇡ wk-val π M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ M' ⊲ γ' ∷ □) {↥ = 🗆})))
                  ----------------------------------------------------------------
                    → ((∘⟨ wk-comp π (return M) ⊰ γ ╎ cs ⟩) {π = πₓ} )→ᶜ ((∙⟨ r̲e̲t̲u̲r̲n̲ M' ⊰ γ' ╎ cs ⟩) {π = πₓ'})

        ∙return  :    {M : V̲a̲l̲ Γ X} → {γ : Env Γ} → {N : (Γ' ∙ X) ⊢ᶜ Y} → {γ' : Env Γ'} → {π : Wk Γ Γ'} → {cs : CompStack Δ Y} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ' Δ}
                  ----------------------------------------------------------------
                    → ((∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ ╎ ((N ⊲ γ' ⦂⦂ cs) {π = πₓ'}) ⟩) {π = π}) →ᶜ ((∘⟨ wk-comp (wk-cong π) N ⊰ γ ﹐ M ╎ cs ⟩) {π = wk-wk πₓ})

        ∘push    :    {M : Γ ⊢ᶜ X} → {N : (Γ ∙ X) ⊢ᶜ Y} → {γ : Env Γ} → {cs : CompStack Δ Y} → {πₓ : Wk Γ Δ}
                  ----------------------------------------------------------------
                    → ((∘⟨ push M N ⊰ γ ╎ cs ⟩) {π = πₓ}) →ᶜ ((∘⟨ M ⊰ γ ╎ ((N ⊲ γ ⦂⦂ cs) {π = πₓ}) ⟩) {π = wk-id})

        ∘sub     :    {M : (Γ ∙ `V) ⊢ᶜ X} → {N : Γ ⊢ᶜ X} → {γ : Env Γ} → {cs : CompStack Δ X} → {πₓ : Wk Γ Δ}
                  ----------------------------------------------------------------
                    → ((∘⟨ sub M N ⊰ γ ╎ cs ⟩) {π = πₓ}) →ᶜ ((∘⟨ M ⊰ ((γ ﹐﹝ N ╎ cs ﹞) {π = πₓ}) ╎ cs ⟩) {π = wk-wk πₓ})

        ∘pm      :    {M : Γ' ⊢ᵛ X `× Y} → {γ : Env Γ} → {W : (Γ' ∙ X ∙ Y) ⊢ᶜ Z} → {cs : CompStack Δ Z} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ'' Δ}
                    → {LHS : V̲a̲l̲ Γ'' X} → {RHS : V̲a̲l̲ Γ'' Y} → {γ'' : Env Γ''} → (π : Wk Γ Γ')
                    → ((∘ ((⇡ wk-val π M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ'' ∷ □) {↥ = 🗆}))) → (π' : Wk Γ'' Γ)
                  ----------------------------------------------------------------
                    → ((∘⟨ pm (wk-val π M) (wk-comp (wk-cong (wk-cong π)) W) ⊰ γ ╎ cs ⟩) {π = πₓ}) →ᶜ ((∘⟨ wk-comp (wk-cong (wk-cong π')) (wk-comp (wk-cong (wk-cong π)) W) ⊰ γ' ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS ╎ cs ⟩) {π = wk-wk (wk-wk πₓ')})

        ∙app-var     :    {i : Γ ∋ (Z' `⇒ Z)} → {N : V̲a̲l̲ Γ Z'} → {γ : Env Γ} → {cs : CompStack Δ Z} → {πₓ : Wk Γ Δ}
                       → {W : (Γ' ∙ Z') ⊢ᶜ Z} → {γ' : Env Γ'}
                       → (⟨ i ∥ γ ⟩ →ᴸ* ⟨ h ∥ _﹐_ γ' (l̲a̲m̲ W) ⟩) → (πᵥ : Wk Γ Γ')
                     ----------------------------------------------------------------
                       → ((∙⟨ a̲pp (var i) N ⊰ γ ╎ cs ⟩) {π = πₓ}) →ᶜ ((∙⟨ a̲pp (wk-val πᵥ (lam W)) N ⊰ γ ╎ cs ⟩) {π = πₓ})

        ∙app-pm     :    {M : Γ ⊢ᵛ (X `× Y)} → {W : (Γ ∙ X ∙ Y) ⊢ᵛ (Z' `⇒ Z)} → {N : V̲a̲l̲ Γ Z'} → {γ : Env Γ} → {cs : CompStack Δ Z} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ' Δ}
                       → {LHS : V̲a̲l̲ Γ' X} → {RHS : V̲a̲l̲ Γ' Y} → {γ' : Env Γ'}
                       → ((∘ ((⇡ M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ pa̲i̲r̲ LHS RHS ⊲ γ' ∷ □) {↥ = 🗆}))) → (π : Wk Γ' Γ)
                     ----------------------------------------------------------------
                       → ((∙⟨ a̲pp (pm M W) N ⊰ γ ╎ cs ⟩) {π = πₓ}) →ᶜ ((∙⟨ a̲pp ((wk-val (wk-cong (wk-cong π)) W)) (wk-v̲a̲l̲ (wk-wk (wk-wk π)) N) ⊰ γ' ﹐ LHS ﹐ (wk-v̲a̲l̲ (wk-wk wk-id) RHS) ╎ cs ⟩) {π = wk-wk (wk-wk πₓ')})

        ∙app-lam     :   {W : (Γ ∙ X) ⊢ᶜ Y} → {N : V̲a̲l̲ Γ X} → {γ : Env Γ} → {cs : CompStack Δ Y} → {πₓ : Wk Γ Δ}
                     ----------------------------------------------------------------
                       → ((∙⟨ a̲pp (lam W) N ⊰ γ ╎ cs ⟩) {π = πₓ}) →ᶜ ((∘⟨ W ⊰ γ ﹐ N ╎ cs ⟩) {π = wk-wk πₓ})

        ∘app         :   {M : Γ ⊢ᵛ X `⇒ Y} → {N : Γ ⊢ᵛ X} → {γ : Env Γ} → {cs : CompStack Δ Y} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ' Δ}
                       → {N' : V̲a̲l̲ Γ' X} → {γ' : Env Γ'}
                       → ((∘ ((⇡ N ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ N' ⊲ γ' ∷ □) {↥ = 🗆}))) → (π : Wk Γ' Γ)
                     ----------------------------------------------------------------
                       → ((∘⟨ app M N ⊰ γ ╎ cs ⟩) {π = πₓ}) →ᶜ ((∙⟨ a̲pp (wk-val π M) N' ⊰ γ' ╎ cs ⟩) {π = πₓ'} )


        -- X and X' should always be the same, but I don't think we can easily check for that
        ∘var     :   {M : Γ ⊢ᵛ `V} → {γ : Env Γ} → {i : Γ' ∋ `V} → {γ' : Env Γ'} → {W : Γ'' ⊢ᶜ X'} → {γ'' : Env Γ''} → {cs : CompStack Δ X} → {cs' : CompStack Δ' X'} → {πₓ : Wk Γ Δ} → {πₓ' : Wk Γ' Δ'} → {πₓ'' : Wk Γ'' Δ'}
                  → ((∘ ((⇡ M ⊲ γ ∷ □) {↥ = 🗆})) ↠ᵛ (∙ ((⭭ v̲a̲r̲ i ⊲ γ' ∷ □) {↥ = 🗆}))) → (π' : Wk Γ' Γ)
                  → (⟨ i ∥ γ' ⟩ →ᴸ* ⟨ h ∥ ((γ'' ﹐﹝ W ╎ cs' ﹞) {π = πₓ''}) ⟩) → (πᵥ : Wk Γ' Γ'')
                  ----------------------------------------------------------------
                    → ((∘⟨ var M ⊰ γ ╎ cs ⟩) {π = πₓ}) →ᶜ ((∘⟨ (wk-comp πᵥ W) ⊰ γ' ╎ cs' ⟩) {π = πₓ'})

  data _→ᶜ*_ where

    _◼ : (S : CompState) → S →ᶜ* S

    _→ᶜ⟨_⟩_ : (S : CompState) → {S' S'' : CompState} → S →ᶜ S' → S' →ᶜ* S'' → S →ᶜ* S''

  _⨾ᶜ_ : {F S T : CompState} → (F →ᶜ* S) → (S →ᶜ* T) → (F →ᶜ* T)
  _⨾ᶜ_ (S ◼) S>>T = S>>T
  _⨾ᶜ_ (F →ᶜ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F →ᶜ⟨ F>S₁ ⟩ (S₁>>S₂ ⨾ᶜ S₂>>T)

  topCompCtx : CompState → Ctx
  topCompCtx (∘⟨_⊰_╎_⟩ {Γ = Γ} _ _ _) = Γ
  topCompCtx (∙⟨_⊰_╎_⟩ {Γ = Γ} _ _ _) = Γ

  data CompSteps : CompState → Set where

      steps : {S T : CompState} → S →ᶜ* T → CompHaltingState T → (π : Wk (topCompCtx T) (topCompCtx S)) → CompSteps S

  {-# TERMINATING #-}
  mutual

    app-eval-rec : (M : Γ' ⊢ᵛ X `⇒ Y) → (N : V̲a̲l̲ Γ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ Y) → (πₓ : Wk Γ Δ) → (n : ℕ) → CompSteps ((∙⟨ (a̲pp (wk-val π M) N) ⊰ γ ╎ cs ⟩) {π = πₓ})
    -- app-eval-rec (var i) N γ π cs πₓ zero = {!!} -- terminates because the total number of occurrences of "var" in the term, the environment and the stack decreases
    -- app-eval-rec (var i) N γ π cs πₓ (suc n) with lookup (wk-mem π i) γ
    app-eval-rec (var i) N γ π cs πₓ n with lookup (wk-mem π i) γ
    ... | steps i>>T (found-lam {W = W} {γ = γ₁}) i≡T π₁ w≡γ with app-eval-rec (lam W) N γ π₁ cs πₓ n
    ... | steps W>WT HT π' = steps (∙⟨ a̲pp (wk-val π (var i)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-var i>>T π₁ ⟩ W>WT) HT π'
    app-eval-rec (lam W) N γ π cs πₓ n with comp-eval-rec W (γ ﹐ N) (wk-cong π) cs (wk-wk πₓ) n
    ... | steps W>WT HT π' rewrite (wk-comp-id W) = steps ( ∙⟨ a̲pp (wk-val π (lam W)) N ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-lam ⟩ W>WT) HT (wk-trans π' (wk-wk wk-id))
    app-eval-rec (pm M₁ N₁) N γ π cs πₓ n with val-eval-rec M₁ γ π
    ... | steps {T = ∙ (⭭ pa̲i̲r̲ {X = X} {Y = Y} LHS RHS ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ with wk-val-trans N₁ (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
    ...       | eq with app-eval-rec N₁ ((wk-v̲a̲l̲ (wk-wk (wk-wk π')) N)) (γ₁ ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS) (wk-cong (wk-cong (wk-trans π' π))) cs (wk-wk (wk-wk (wk-trans π' πₓ))) n
    ...          | steps N>NT NT π'' rewrite (sym eq) =

        steps
         (∙⟨ (a̲pp (wk-val π (pm M₁ N₁)) N) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∙app-pm M>T π' ⟩ N>NT )
         NT
         (wk-trans π'' (wk-wk (wk-wk π')))

    comp-eval-rec : (W : Γ' ⊢ᶜ X) → (γ : Env Γ) → (π : Wk Γ Γ') → (cs : CompStack Δ X) → (πₓ : Wk Γ Δ) → (n : ℕ) → CompSteps ((∘⟨ wk-comp π W ⊰ γ ╎ cs ⟩) {π = πₓ})

    comp-eval-rec (return {A = X} M) γ π ◻ πₓ n with val-eval-rec {X = X} M γ π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ = steps (∘⟨ wk-comp π (return M) ⊰ γ ╎ ◻ ⟩ →ᶜ⟨ ∘return M>T ⟩ (∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ ◻ ⟩ ◼)) ret π'
    comp-eval-rec (return {A = X} M) γ π ((M' ⊲ γ' ⦂⦂ cs) {π = π₁}) πₓ n with val-eval-rec {X = X} M γ π
    ... | steps {T = ∙ ((⭭ M₁ ⊲ γ₁ ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ with comp-eval-rec M' (γ₁ ﹐ M₁) (wk-cong (wk-trans π' πₓ)) cs (wk-wk (wk-trans (wk-trans π' πₓ) π₁)) n
    ... | steps {T = T} M'>T ret π'' = steps (∘⟨ wk-comp π (return M) ⊰ γ ╎ (M' ⊲ γ' ⦂⦂ cs) ⟩ →ᶜ⟨ ∘return M>T ⟩ ∙⟨ r̲e̲t̲u̲r̲n̲ M₁ ⊰ γ₁ ╎ M' ⊲ γ' ⦂⦂ cs ⟩ →ᶜ⟨ ∙return {πₓ = wk-trans (wk-trans π' πₓ) π₁} {πₓ' = π₁} ⟩ M'>T) ret (wk-trans π'' (wk-wk π'))

    comp-eval-rec (pm {A = X} {B = Y} M W) γ π cs πₓ n with val-eval-rec {X = X `× Y} M γ π
    ...  | steps {T = ∙ ((⭭_ {X = X `× Y} (pa̲i̲r̲ LHS RHS) ⊲ γ' ∷ □) {↥ = 🗆})} M>T ∙T M≡T π' wk≡ with comp-eval-rec W (γ' ﹐ LHS ﹐ wk-v̲a̲l̲ (wk-wk wk-id) RHS) (wk-trans (wk-cong (wk-cong π')) (wk-cong (wk-cong π))) cs (wk-wk (wk-wk (wk-trans π' πₓ))) n
    ...   | steps W>T HT π₁ with wk-comp-trans W (wk-cong (wk-cong π')) (wk-cong (wk-cong π))
    ...     | eq rewrite (sym eq) = steps (∘⟨ wk-comp π (pm M W) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘pm π M>T π' ⟩ W>T) HT (wk-trans π₁ (wk-wk (wk-wk π')))

    -- comp-eval-rec (push W V) γ π cs πₓ zero = {!!} -- terminates because the total number of occurrences of "push" in the term, the environment and the stack decreases
    -- comp-eval-rec (push W V) γ π cs πₓ (suc n) with comp-eval-rec W γ π ((wk-comp (wk-cong π) V) ⊲ γ ⦂⦂ cs) wk-id n
    comp-eval-rec (push W V) γ π cs πₓ n with comp-eval-rec W γ π ((wk-comp (wk-cong π) V) ⊲ γ ⦂⦂ cs) wk-id n
    ... | steps {T = ∙⟨ r̲e̲t̲u̲r̲n̲ M ⊰ γ₁ ╎ ◻ ⟩} W>T ret π' =

                steps
                  (  ∘⟨ push (wk-comp π W) (wk-comp (wk-cong π) V) ⊰ γ ╎ cs ⟩  →ᶜ⟨ ∘push ⟩ W>T )
                  ret
                  π'

    comp-eval-rec (app M N) γ π cs πₓ n with val-eval-rec N γ π
    ... | steps {T = ∙ ((⭭_ NT ⊲ γᴺ ∷ □) {↥ = 🗆})} N>NT ∙NT N≡NT πᴺ wk≡ᴺ with app-eval-rec M NT γᴺ (wk-trans πᴺ π) cs (wk-trans πᴺ πₓ) n
    ... | steps W>WT HT πᵂ rewrite (sym (wk-val-trans M πᴺ π)) =
            steps

                ((∘⟨ app (wk-val π M) (wk-val π N) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘app N>NT πᴺ ⟩ W>WT ))
                HT
                (wk-trans πᵂ πᴺ)

    -- comp-eval-rec (var {A = X} M) γ π cs πₓ zero = {!!} -- terminates because the total number of occurrences of "var" in the term, the environment and the stack decreases
    -- comp-eval-rec (var {A = X} M) γ π cs πₓ (suc n) with val-eval-rec {X = `V} M γ π
    comp-eval-rec (var {A = X} M) γ π cs πₓ n with val-eval-rec {X = `V} M γ π
    ... | steps {T = ∙ ((⭭ v̲a̲r̲ i) ⊲ γ₁ ∷ □) {↥ = 🗆}} M>T ∙T M≡T π' wk≡ with lookup i γ₁
    ... | steps i>>T (found-comp {X = X} {W = W'} {γ = γ'} {cs = cs'} {π = πᶜ}) i≡T π₂ w≡γ with comp-eval-rec W' γ₁ π₂ cs' (wk-trans π₂ πᶜ) n
    ... | steps {T = T} W>T ret π'' =
                steps
                (∘⟨ var (wk-val π M) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘var M>T π' i>>T π₂ ⟩ W>T)
                ret
                (wk-trans π'' π')

    comp-eval-rec (sub W V) γ π cs πₓ n with comp-eval-rec W (γ ﹐﹝ wk-comp π V ╎ cs ﹞) (wk-cong π) cs (wk-wk πₓ) n
    ... | steps W>WT HT πᵂ =
                steps
                    (∘⟨ sub (wk-comp (wk-cong π) W) (wk-comp π V) ⊰ γ ╎ cs ⟩ →ᶜ⟨ ∘sub ⟩ W>WT)
                    HT
                    (wk-trans πᵂ (wk-wk wk-id))


    comp-eval : (W : ε ⊢ᶜ R₀) → CompSteps ((∘⟨ wk-comp wk-id W ⊰ ∗ ╎ ◻ ⟩) {π = wk-id})
    comp-eval W = comp-eval-rec W ∗ wk-id ◻ wk-id 100000000
