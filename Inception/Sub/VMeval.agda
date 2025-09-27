module Inception.Sub.VMeval (R : Set) where

open import Function.Base using (id)
open Function.Base using (id)

open import Data.List
open import Data.Unit
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≤?_; z≤n; s≤s; _+_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Inception.Sub.ValueMachine R
open import Inception.Sub.VMcong R

{-

-- Using progress and 'gas' we can evaluate expressions (quick-eval).
-- However, we can also prove termination and evaluate expressions using that proof (eval).

open import Inception.Sub.VMprogress R

-- cf PLFA
record Gas : Set where
  constructor gas
  field
    amount : ℕ

data Finished (S : VState T◾) : Set where

  result : {S' : VState T◾} → (haltingVState S') → Finished S

  out-of-gas : Finished S

data Steps : (VState T◾) → Set where

  no-steps : {S : VState T◾} → haltingVState S → Steps S

  steps : {S S' : VState T◾} → S ~>>ᵛᵛ S' → Finished S' → Steps S

bounded-eval : Gas → (S : VState T◾) → Steps S
bounded-eval (gas zero) S  with progress S
... | done HS = no-steps HS
... | step {S' = S'} (S~>S') = steps (S ~>ᵛᵛ⟨ S~>S' ⟩) out-of-gas
bounded-eval (gas (suc amount)) S with progress S
... | done HS = no-steps HS
... | step {S' = S'} (S~>S') with bounded-eval (gas amount) S'
... |   no-steps HS = steps (S ~>ᵛᵛ⟨ S~>S' ⟩) (result HS)
... |   steps S'~>>S'' fin = steps (S ~>ᵛᵛ⟨ S~>S' ⟩ S'~>>S'') fin


calc-steps : (Γ ⊢ᵛ X) → ℕ
calc-steps (var i) = 1
calc-steps (lam x) = 1
calc-steps (pair M M') = 3 + (calc-steps M) + (calc-steps M')
calc-steps (pm M N) = 2 + (calc-steps M) + (calc-steps N)
calc-steps unit = 1

quick-eval : (M : Γ ⊢ᵛ X) → (γ : ⟦ Γ ⟧ˣ) → Steps (∘ M ﹐ γ ■)
quick-eval M γ = bounded-eval (gas (calc-steps M)) (∘ M ﹐ γ ■)
-}


data finiteSteps : VState T◾ → Set where

  steps : {S T : VState T◾} → S ~>>ᵛᵛ T →  haltingVState T → finiteSteps S

getctx : (T : VState X) → {HT : haltingVState T} → Ctx
getctx (∙[var] var {Γ = Γ} i₁ ﹐ γ₁ ■) = Γ
getctx (∙[lam] lam {Γ = Γ} M₁ ﹐ γ₁ ■) = Γ
getctx (∙[unit] unit {Γ = Γ} ﹐ γ₁ ■) = Γ
getctx (∙[pair] pair {Γ = Γ} x₁ y₁ ﹐ γ₁ ■) = Γ

getenv : (T : VState X) → {HT : haltingVState T} → ⟦ getctx T {HT = HT} ⟧ˣ
getenv (∙[var] var i₁ ﹐ γ₁ ■) = γ₁
getenv (∙[lam] lam M₁ ﹐ γ₁ ■) = γ₁
getenv (∙[unit] unit ﹐ γ₁ ■) = γ₁
getenv (∙[pair] pair x₁ y₁ ﹐ γ₁ ■) = γ₁

getterm : (T : VState X) → {HT : haltingVState T} → (getctx T {HT = HT}) ⊢ᵛ X
getterm (∙[var] var i₁ ﹐ γ₁ ■) = var i₁
getterm (∙[lam] lam M₁ ﹐ γ₁ ■) = lam M₁
getterm (∙[unit] unit ﹐ γ₁ ■) = unit
getterm (∙[pair] pair x₁ y₁ ﹐ γ₁ ■) = pair x₁ y₁

gettrans-left : (T' : VState X) → {HT' : haltingVState T'} → (γ : ⟦ Γ ⟧ˣ) → (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → (LHS>>T' : (∘ LHS ﹐ γ ■) ~>>ᵛᵛ T') → ( (T' ::l⟨ (T≡*LHS LHS>>T' refl (pair LHS RHS ﹐ γ ■)) ⟩ (pair LHS RHS ﹐ γ ■)) ~>ᵛᵛ (∘ RHS ﹐ γ ∷r⟨ refl ⟩ pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ ,  ⟦ (getterm T' {HT = HT'}) ⟧ᵛ (getenv T') ) ■) )
gettrans-left (∙[var] var i₁ ﹐ γ₁ ■) γ LHS RHS LHS>>T' = ~∙var∷l■~> γ₁ γ i₁ LHS RHS (T≡*LHS LHS>>T' refl (pair LHS RHS ﹐ γ ■))
gettrans-left (∙[lam] lam M₁ ﹐ γ₁ ■) γ LHS RHS LHS>>T' = ~∙lam∷l■~> γ₁ γ M₁ LHS RHS (T≡*LHS LHS>>T' refl (pair LHS RHS ﹐ γ ■))
gettrans-left (∙[unit] unit ﹐ γ₁ ■) γ LHS RHS LHS>>T' =  ~∙unit∷l■~> γ₁ γ LHS RHS (T≡*LHS LHS>>T' refl (pair LHS RHS ﹐ γ ■))
gettrans-left (∙[pair] pair x₁ y₁ ﹐ γ₁ ■) γ LHS RHS LHS>>T' = ~∙pair∷l■~> γ₁ γ x₁ y₁ LHS RHS (T≡*LHS LHS>>T' refl (pair LHS RHS ﹐ γ ■))

gettrans-right : (T' : VState X) → {HT' : haltingVState T'} → (T'' : VState Y) → {HT'' : haltingVState T''} → (γ : ⟦ Γ ⟧ˣ) → (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → (RHS>>T'' : (∘ RHS ﹐ γ ■) ~>>ᵛᵛ T'') → ( (T'' ::r⟨ T≡*RHS RHS>>T'' refl (pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) ■) ⟩ (pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) ■)) ~>ᵛᵛ (∙[pair] pair (wk-val (wk-wk wk-id) (var h)) (var h)  ﹐ ((γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) , ⟦ getterm T'' {HT = HT''} ⟧ᵛ (getenv T'' {HT = HT''})) ■) )
gettrans-right T' {HT' = HT'} (∙[var] var i₂ ﹐ γ₂ ■) γ LHS RHS RHS>>T'' = ~∙var∷r■~> γ₂ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) i₂ (var h) (wk-val (wk-wk wk-id) RHS) (T≡*RHS RHS>>T'' refl (pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) ■))
gettrans-right T' {HT' = HT'} (∙[lam] lam M₂ ﹐ γ₂ ■) γ LHS RHS RHS>>T'' = ~∙lam∷r■~> γ₂ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) M₂ (var h) (wk-val (wk-wk wk-id) RHS) (T≡*RHS RHS>>T'' refl (pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) ■))
gettrans-right T' {HT' = HT'} (∙[unit] unit ﹐ γ₂ ■) γ LHS RHS RHS>>T'' = ~∙unit∷r■~> γ₂ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) (var h) (wk-val (wk-wk wk-id) RHS) (T≡*RHS RHS>>T'' refl (pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) ■))
gettrans-right T' {HT' = HT'} (∙[pair] pair x₂ y₂ ﹐ γ₂ ■) γ LHS RHS RHS>>T'' = ~∙pair∷r■~> γ₂ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) x₂ y₂ (var h) (wk-val (wk-wk wk-id) RHS) (T≡*RHS RHS>>T'' refl (pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ ,  ⟦ getterm T' {HT = HT'} ⟧ᵛ (getenv T' {HT = HT'})) ■))

get-pair-steps : {T' : VState X} → {T'' : VState Y} → {HT' : haltingVState T'} → {HT'' : haltingVState T''} → (γ : ⟦ Γ ⟧ˣ) → (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → ((∘ LHS ﹐ γ ■) ~>>ᵛᵛ T') → ((∘ RHS ﹐ γ ■) ~>>ᵛᵛ T'') → finiteSteps (∘ pair LHS RHS ﹐ γ ■)
get-pair-steps {T' = T'} {T'' = T''} {HT' = HT'} {HT'' = HT''} γ LHS RHS LHS>>T' RHS>>T'' =
        steps (    (∘ (pair LHS RHS) ﹐ γ ■)                                       ~>ᵛᵛ⟨ ~∘pair~> ⟩
                +[ _ ]+       ⟪ LHS>>T' ⟫::l⟨ refl ⟩ (pair LHS RHS ﹐ γ ■)
                +[ _ ]+       _ ~>ᵛᵛ⟨ gettrans-left T' γ LHS RHS LHS>>T' ⟩
                +[ _ ]+       ⟪ RHS>>T'' ⟫::r⟨ refl ⟩ (pair (var h) (wk-val (wk-wk wk-id) RHS) ﹐ (γ ,  ⟦ LHS' ⟧ᵛ γ₁) ■)
                +[ _ ]+       _ ~>ᵛᵛ⟨ gettrans-right T' T'' γ LHS RHS RHS>>T'' ⟩
              ) ∙pair[ wk-val (wk-wk wk-id) (var h) ⹁ var h ]⹁ ((γ ,  ⟦ LHS' ⟧ᵛ γ₁) , ⟦ RHS' ⟧ᵛ γ₂) ■
        where
         LHS'  = getterm T' {HT = HT'}
         RHS'  = getterm T'' {HT = HT''}
         γ₁  = getenv T' {HT = HT'}
         γ₂  = getenv T'' {HT = HT''}

get-pm-N-env : (T' : VState (X `× Y)) → (HT' : haltingVState T') → (γ : ⟦ Γ ⟧ˣ) → ⟦ Γ ∙ X ∙ Y ⟧ˣ
get-pm-N-env (∙[var] var i ﹐ γ' ■) HT' γ = ((γ , proj₁ (⟦ var i ⟧ᵛ γ')) , proj₂ (⟦ var i ⟧ᵛ γ'))
get-pm-N-env (∙[pair] pair x y ﹐ γ' ■) HT' γ = ((γ , ⟦ x ⟧ᵛ γ') , ⟦ y ⟧ᵛ γ')

get-pm-trans : {T' : VState (X `× Y)} → {T'' : VState Z} → {HT' : haltingVState T'} → {HT'' : haltingVState T''} → (γ : ⟦ Γ ⟧ˣ) → (M : Γ ⊢ᵛ X `× Y) → (N : (Γ ∙ X ∙ Y) ⊢ᵛ Z) → (M>>T' : (∘ M ﹐ γ ■) ~>>ᵛᵛ T') → (T' ::pm⟨ T≡*M M>>T' refl ((pm M N) ﹐ γ ■) ⟩ (pm M N) ﹐ γ ■) ~>>ᵛᵛ (∘ N ﹐ get-pm-N-env T' HT' γ ■)
get-pm-trans {T' = ∙[var] var i ﹐ γ' ■} {T'' = T''} {HT' = HT'} {HT'' = HT''} γ M N M>>T' =  _ ~>ᵛᵛ⟨ ~∙var∷pm■~> γ' γ i M N (T≡*M M>>T' refl ((pm M N) ﹐ γ ■)) ⟩
get-pm-trans {T' = ∙[pair] pair x y ﹐ γ' ■} {T'' = T''} {HT' = HT'} {HT'' = HT''} γ M N M>>T' = _ ~>ᵛᵛ⟨ ~∙pair∷pm■~> γ' γ x y M N (T≡*M M>>T' refl ((pm M N) ﹐ γ ■)) ⟩


get-pm-steps : {T' : VState (X `× Y)} → {T'' : VState Z} → {HT' : haltingVState T'} → {HT'' : haltingVState T''} → (γ : ⟦ Γ ⟧ˣ) → (M : Γ ⊢ᵛ X `× Y) → (N : (Γ ∙ X ∙ Y) ⊢ᵛ Z) → ((∘ M ﹐ γ ■) ~>>ᵛᵛ T') → ((∘ N ﹐ get-pm-N-env T' HT' γ ■) ~>>ᵛᵛ T'') → finiteSteps (∘ pm M N ﹐ γ ■)
get-pm-steps {T' = T'} {T'' = T''} {HT' = HT'} {HT'' = HT''} γ M N M>>T' N>>T'' =

           steps (    (∘ (pm M N) ﹐ γ ■)  ~>ᵛᵛ⟨ ~∘pm~> ⟩
                   +[ MS  ]+       (⟪ M>>T' ⟫::pm⟨ refl ⟩ ((pm M N) ﹐ γ ■))
                   +[ MS' ]+       get-pm-trans {T' = T'} {T'' = T''} {HT' = HT'} {HT'' = HT''} γ M N M>>T'
                   +[ NS  ]+       N>>T''
                 ) HT''

         where
             MS  = ∘ M ﹐ γ ∷pm⟨ refl ⟩ pm M N ﹐ γ ■
             MS' = T' ::pm⟨ T≡*M M>>T' refl ((pm M N) ﹐ γ ■) ⟩ (pm M N) ﹐ γ ■
             NS  = ∘ N ﹐ get-pm-N-env T' HT' γ ■


eval : (M : Γ ⊢ᵛ X) → (γ : ⟦ Γ ⟧ˣ) → finiteSteps (∘ M ﹐ γ ■)
eval (var i) γ = steps ((∘ var i ﹐ γ ■) ~>ᵛᵛ⟨ ~∘var~> ⟩) (∙var i ⹁ γ ■)
eval (lam M) γ = steps ((∘ lam M ﹐ γ ■) ~>ᵛᵛ⟨ ~∘lam~> ⟩) (∙lam M ⹁ γ ■)
eval unit γ = steps ((∘ unit ﹐ γ ■) ~>ᵛᵛ⟨ ~∘unit~> ⟩) ∙unit⹁ γ ■
eval (pair LHS RHS) γ with eval LHS γ | eval RHS γ
... | steps {T = T'} LHS>>T' HT' | steps {T = T''} RHS>>T'' HT'' = get-pair-steps {T' = T'} {T'' = T''} {HT' = HT'} {HT'' = HT''} γ LHS RHS LHS>>T' RHS>>T''
eval (pm M N) γ with eval M γ
... | steps {T = T'} M>>T' HT' with eval N (get-pm-N-env T' HT' γ)
...       |    steps {T = T''} N>>T'' HT'' = get-pm-steps {T' = T'} {T'' = T''} {HT' = HT'} {HT'' = HT''} γ M N M>>T' N>>T''


-------------------------------------

ex1 : ε ⊢ᵛ `Unit
ex1 = pm (pair unit unit) (var (t h))

ex2 : (ε ∙ (`Unit `⇒ `Unit) ∙ `Unit) ⊢ᵛ (`Unit `× (`Unit `⇒ `Unit)) `× `Unit
ex2 = pair (pair (var h) (var (t h))) (var h)

ex3 : ε ⊢ᵛ (`Unit `⇒ `Unit)
ex3 = lam (return unit)

ex4 : (ε ∙ `Unit) ⊢ᵛ `Unit `× `Unit
ex4 = pair (var h) (var h)

---------------------------------------

{-
-- calling agda2-compute-normalised in the hole below evaluates ex2
_ : eval ex2 ((tt , λ _ z → z tt) , tt) ≡ {! eval ex1 tt!}
_ = refl
-}
