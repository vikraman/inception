module Inception.Sub.VMeval (R : Set) where

open import Function.Base using (id)
open import Data.Product using (proj₁; proj₂; _,_; Σ; ∃; Σ-syntax; ∃-syntax)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; sym)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Product as P

open import Data.Unit

variable
  A' B' C' D' X Y Z X' Y' Z' X₁ Y₁ Z₁ X₂ Y₂ Z₂ X◾ Y◾ Z◾ X↓ Y↓ Z↓ T◾ T◾' T◾₁ T◾₂ : Ty
  Γ' Γ'' Γ''' Δ' Γ₁ Γ₂ Γ◾ Γ↓ : Ctx

infix 26 ⇡_
infixr 25 _⹁_∷_

infix 20 ∘_
infix 20 ∙_

infix 15 _→ᵛᵛ_


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
_ : stepVMᵢ  ex2 ((tt , λ _ z → z tt) , tt) ≡ {! stepVMᵢ  ex1 tt!}
_ = refl
-}


--------------
data partialTerm : (Γ : Ctx) → (X : Ty) → Set where

    ⇡_ : (M : Γ ⊢ᵛ X) → partialTerm Γ X

    ⇡ᴹ : (M : Γ ⊢ᵛ X `× Y) → (N : (Γ ∙ X ∙ Y) ⊢ᵛ Z) → partialTerm Γ Z

    ⇡ᴸ : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → partialTerm Γ (X `× Y)

    ⇡ᴿ  : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → partialTerm Γ (X `× Y)

data vStack : (T◾ : Ty) → Set where

    □ : {T◾ : Ty} → vStack T◾

    _⹁_∷_ : partialTerm Γ X → (γ : ⟦ Γ ⟧ˣ) → vStack T◾ → vStack T◾


data vState : (T◾ : Ty) → Set where

     ∘_ : vStack T◾ → vState T◾

     ∙_ : vStack T◾ → vState T◾

data _→ᵛᵛ_ : vState T◾ → vState T◾ → Set where

     ~∘var~>   : {γ : ⟦ Γ ⟧ˣ} → {i : Γ ∋ X} → {tail : vStack T◾} → ∘ ⇡ var i ⹁ γ ∷ tail →ᵛᵛ ∙ ⇡ (var i) ⹁ γ ∷ tail

     ~∘lam~> : {γ : ⟦ Γ ⟧ˣ} → {M : (Γ ∙ X) ⊢ᶜ Y} → {tail : vStack T◾} → ∘ ⇡ lam M ⹁ γ ∷ tail →ᵛᵛ ∙ ⇡ lam M ⹁ γ ∷ tail

     ~∘pair~> : {γ : ⟦ Γ ⟧ˣ} → {LHS : Γ ⊢ᵛ X} → {RHS : Γ ⊢ᵛ Y} → {tail : vStack T◾} → ∘ ⇡ pair LHS RHS ⹁ γ ∷ tail →ᵛᵛ ∘ ⇡ LHS ⹁ γ ∷ ⇡ᴸ LHS RHS ⹁ γ ∷ tail

     ~∘pm~> : {γ : ⟦ Γ ⟧ˣ} → {M : Γ ⊢ᵛ X `× Y} → {N : (Γ ∙ X ∙ Y) ⊢ᵛ Z} → {tail : vStack T◾} → ∘ ⇡ pm M N ⹁ γ ∷ tail →ᵛᵛ ∘ ⇡ᴹ M N ⹁ γ ∷ tail

     ~∘unit~> : {γ : ⟦ Γ ⟧ˣ} → {tail : vStack T◾} → ∘ ⇡ unit ⹁ γ ∷ tail →ᵛᵛ ∙ ⇡ unit ⹁ γ ∷ tail

     ~∙M∷pm~> : {γ : ⟦ Γ ⟧ˣ} → {γ' : ⟦ Γ' ⟧ˣ} → {M₂ : Γ ⊢ᵛ X `× Y} → {M : Γ' ⊢ᵛ X `× Y} → {N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z'} → {tail : vStack T◾}
                 →    ∙ ⇡ M₂ ⹁ γ ∷ ⇡ᴹ M N ⹁ γ' ∷ tail →ᵛᵛ ∘ ⇡ N ⹁ ((γ' , proj₁ (⟦ M₂ ⟧ᵛ γ)) , proj₂ (⟦ M₂ ⟧ᵛ γ)) ∷ tail

     ~∙M∷l~> : {γ : ⟦ Γ ⟧ˣ} → {γ' : ⟦ Γ' ⟧ˣ} → {M : Γ ⊢ᵛ X} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y} → {tail : vStack T◾}
                 →    ∙ ⇡ M ⹁ γ ∷ ⇡ᴸ LHS RHS ⹁ γ' ∷ tail →ᵛᵛ ∘ ⇡ RHS ⹁ γ' ∷ ⇡ᴿ (var h) (wk-val (wk-wk wk-id) RHS) ⹁ (γ' ,  ⟦ M ⟧ᵛ γ) ∷ tail

     ~∙M∷r~> : {γ : ⟦ Γ ⟧ˣ} → {γ' : ⟦ Γ' ⟧ˣ} → {M : Γ ⊢ᵛ Y} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y} → {tail : vStack T◾}
                 →   ∙ ⇡ M ⹁ γ ∷ ⇡ᴿ LHS RHS ⹁ γ' ∷ tail →ᵛᵛ ∙ ⇡ pair (wk-val (wk-wk wk-id) LHS) (var h) ⹁ (γ' , ⟦ M ⟧ᵛ γ) ∷ tail


data _↠ᵛᵛ_ : vState T◾ → vState T◾ → Set where

  _→ᵛᵛ⟨_⟩ : (S : vState T◾) → {S' : vState T◾} → S →ᵛᵛ S' → S ↠ᵛᵛ S'

  _→ᵛᵛ⟨_⟩_ : (S : vState T◾) {S' S'' : vState T◾} → S →ᵛᵛ S' → S' ↠ᵛᵛ S'' → S ↠ᵛᵛ S''


_⦂⦂_ : vStack T◾ → vStack T◾' → vStack T◾'
□ ⦂⦂ lower = lower
(M ⹁ γ ∷ upper) ⦂⦂ lower =  M ⹁ γ ∷ (upper ⦂⦂ lower)


_::_ : vState T◾ → vStack T◾' → vState T◾'
(∘ upper) :: lower = ∘ (upper ⦂⦂ lower)
(∙ upper) :: lower = ∙ (upper ⦂⦂ lower)

⟨_⟩∷_ : {from : vState T◾} → {to : vState T◾} → (F>T : from →ᵛᵛ to) → (tail : vStack T◾') → (from :: tail) →ᵛᵛ (to :: tail)
⟨ ~∘var~> ⟩∷ tail = ~∘var~>
⟨ ~∘lam~> ⟩∷ tail = ~∘lam~>
⟨ ~∘pair~> ⟩∷ tail = ~∘pair~>
⟨ ~∘pm~> ⟩∷ tail = ~∘pm~>
⟨ ~∘unit~> ⟩∷ tail = ~∘unit~>
⟨ ~∙M∷pm~> ⟩∷ tail = ~∙M∷pm~>
⟨ ~∙M∷l~> ⟩∷ tail = ~∙M∷l~>
⟨ ~∙M∷r~> ⟩∷ tail = ~∙M∷r~>

⟪_⟫∷_ : {from : vState T◾} → {to : vState T◾} → (F>T : from ↠ᵛᵛ to) → (tail : vStack T◾') → (from :: tail) ↠ᵛᵛ (to :: tail)
⟪ _ →ᵛᵛ⟨ F>T ⟩ ⟫∷ tail =  _ →ᵛᵛ⟨ ⟨ F>T ⟩∷ tail ⟩
⟪ _ →ᵛᵛ⟨ F>T ⟩ F>>T ⟫∷ tail =   _ →ᵛᵛ⟨ ⟨ F>T ⟩∷ tail ⟩ (⟪ F>>T ⟫∷ tail)

{-
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
-}

{-
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
-}

{-
eval : (M : Γ ⊢ᵛ X) → (γ : ⟦ Γ ⟧ˣ) → finiteSteps (∘ M ﹐ γ ■)
eval (var i) γ = steps ((∘ var i ﹐ γ ■) ~>ᵛᵛ⟨ ~∘var~> ⟩) (∙var i ⹁ γ ■)
eval (lam M) γ = steps ((∘ lam M ﹐ γ ■) ~>ᵛᵛ⟨ ~∘lam~> ⟩) (∙lam M ⹁ γ ■)
eval unit γ = steps ((∘ unit ﹐ γ ■) ~>ᵛᵛ⟨ ~∘unit~> ⟩) ∙unit⹁ γ ■
eval (pair LHS RHS) γ with eval LHS γ | eval RHS γ
... | steps {T = T'} LHS>>T' HT' | steps {T = T''} RHS>>T'' HT'' = get-pair-steps {T' = T'} {T'' = T''} {HT' = HT'} {HT'' = HT''} γ LHS RHS LHS>>T' RHS>>T''
eval (pm M N) γ with eval M γ
... | steps {T = T'} M>>T' HT' with eval N (get-pm-N-env T' HT' γ)
...       |    steps {T = T''} N>>T'' HT'' = get-pm-steps {T' = T'} {T'' = T''} {HT' = HT'} {HT'' = HT''} γ M N M>>T' N>>T''
-}

{-
data finiteSteps : VState T◾ → Set where

  steps : {S T : VState T◾} → S ~>>ᵛᵛ T →  haltingVState T → finiteSteps S
  -}
