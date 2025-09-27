module Inception.Sub.VMeval (R : Set) where

open import Function.Base using (id)
open import Data.Product using (proj₁; proj₂; _,_; Σ; ∃; Σ-syntax; ∃-syntax)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; sym)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax
open import Inception.Sub.CPS R

open import Data.Sum using (_⊎_; inj₁; inj₂)
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

data Bool : Set where
     true : Bool
     false : Bool

variable
     b : Bool

data vStack : Bool → Set where

    □ : vStack false

    _⹁_∷_ : partialTerm Γ X → (γ : ⟦ Γ ⟧ˣ) → vStack b → vStack true


data vState : Set where

     ∘_ : vStack true → vState

     ∙_ : vStack true → vState

data _→ᵛᵛ_ : vState → vState → Set where

     ~∘var~>   : {γ : ⟦ Γ ⟧ˣ} → {i : Γ ∋ X} → {tail : vStack b} → ∘ ⇡ var i ⹁ γ ∷ tail →ᵛᵛ ∙ ⇡ (var i) ⹁ γ ∷ tail

     ~∘lam~> : {γ : ⟦ Γ ⟧ˣ} → {M : (Γ ∙ X) ⊢ᶜ Y} → {tail : vStack b} → ∘ ⇡ lam M ⹁ γ ∷ tail →ᵛᵛ ∙ ⇡ lam M ⹁ γ ∷ tail

     ~∘pair~> : {γ : ⟦ Γ ⟧ˣ} → {LHS : Γ ⊢ᵛ X} → {RHS : Γ ⊢ᵛ Y} → {tail : vStack b} → ∘ ⇡ pair LHS RHS ⹁ γ ∷ tail →ᵛᵛ ∘ ⇡ LHS ⹁ γ ∷ ⇡ᴸ LHS RHS ⹁ γ ∷ tail

     ~∘pm~> : {γ : ⟦ Γ ⟧ˣ} → {M : Γ ⊢ᵛ X `× Y} → {N : (Γ ∙ X ∙ Y) ⊢ᵛ Z} → {tail : vStack b} → ∘ ⇡ pm M N ⹁ γ ∷ tail →ᵛᵛ ∘ ⇡ᴹ M N ⹁ γ ∷ tail

     ~∘unit~> : {γ : ⟦ Γ ⟧ˣ} → {tail : vStack b} → ∘ ⇡ unit ⹁ γ ∷ tail →ᵛᵛ ∙ ⇡ unit ⹁ γ ∷ tail

     ~∙M∷pm~> : {γ : ⟦ Γ ⟧ˣ} → {γ' : ⟦ Γ' ⟧ˣ} → {M₂ : Γ ⊢ᵛ X `× Y} → {M : Γ' ⊢ᵛ X `× Y} → {N : (Γ' ∙ X ∙ Y) ⊢ᵛ Z'} → {tail : vStack b}
                 →    ∙ ⇡ M₂ ⹁ γ ∷ ⇡ᴹ M N ⹁ γ' ∷ tail →ᵛᵛ ∘ ⇡ N ⹁ ((γ' , proj₁ (⟦ M₂ ⟧ᵛ γ)) , proj₂ (⟦ M₂ ⟧ᵛ γ)) ∷ tail

     ~∙M∷l~> : {γ : ⟦ Γ ⟧ˣ} → {γ' : ⟦ Γ' ⟧ˣ} → {M : Γ ⊢ᵛ X} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y} → {tail : vStack b}
                 →    ∙ ⇡ M ⹁ γ ∷ ⇡ᴸ LHS RHS ⹁ γ' ∷ tail →ᵛᵛ ∘ ⇡ RHS ⹁ γ' ∷ ⇡ᴿ (var h) (wk-val (wk-wk wk-id) RHS) ⹁ (γ' ,  ⟦ M ⟧ᵛ γ) ∷ tail

     ~∙M∷r~> : {γ : ⟦ Γ ⟧ˣ} → {γ' : ⟦ Γ' ⟧ˣ} → {M : Γ ⊢ᵛ Y} → {LHS : Γ' ⊢ᵛ X} → {RHS : Γ' ⊢ᵛ Y} → {tail : vStack b}
                 →   ∙ ⇡ M ⹁ γ ∷ ⇡ᴿ LHS RHS ⹁ γ' ∷ tail →ᵛᵛ ∙ ⇡ pair (wk-val (wk-wk wk-id) LHS) (var h) ⹁ (γ' , ⟦ M ⟧ᵛ γ) ∷ tail


data _↠ᵛᵛ_ : vState → vState → Set where

  _→ᵛᵛ⟨_⟩ : (S : vState) → {S' : vState} → S →ᵛᵛ S' → S ↠ᵛᵛ S'

  _→ᵛᵛ⟨_⟩_ : (S : vState) {S' S'' : vState} → S →ᵛᵛ S' → S' ↠ᵛᵛ S'' → S ↠ᵛᵛ S''

-- ~>>ᵛᵛ-trans : {F S T : VState T◾} → (F ~>>ᵛᵛ S) → (S ~>>ᵛᵛ T) → (F ~>>ᵛᵛ T)
-- ~>>ᵛᵛ-trans (F ~>ᵛᵛ⟨ F>S ⟩) S>>T = F ~>ᵛᵛ⟨ F>S ⟩ S>>T
-- ~>>ᵛᵛ-trans (F ~>ᵛᵛ⟨ F>S₁ ⟩ S₁>>S₂) S₂>>T = F ~>ᵛᵛ⟨ F>S₁ ⟩ (~>>ᵛᵛ-trans S₁>>S₂ S₂>>T)
-- 
-- infixr 15 ~>>ᵛᵛ-trans
-- syntax ~>>ᵛᵛ-trans {S = S} F>>S S>>T = F>>S +[ S ]+ S>>T


_⦂⦂_ : vStack true → vStack b → vStack true
(M ⹁ γ ∷ □) ⦂⦂ lower = M ⹁ γ ∷ lower
(M ⹁ γ ∷ M' ⹁ γ' ∷ upper) ⦂⦂ lower =  M ⹁ γ ∷ ((M' ⹁ γ' ∷ upper) ⦂⦂ lower)


_::_ : vState → vStack b → vState
(∘ upper) :: lower = ∘ (upper ⦂⦂ lower)
(∙ upper) :: lower = ∙ (upper ⦂⦂ lower)

⟨_⟩∷_ : {from : vState} → {to : vState} → (F>T : from →ᵛᵛ to) → (tail : vStack b) → (from :: tail) →ᵛᵛ (to :: tail)
⟨ ~∘var~> {tail = □} ⟩∷ tail =  ~∘var~> {tail = tail}
⟨ ~∘var~> {tail = _ ⹁ _ ∷ tail₁} ⟩∷ tail = ~∘var~> {tail = _ ⹁ _ ∷ tail₁ ⦂⦂ tail}
⟨ ~∘lam~>  {tail = □} ⟩∷ tail   =  ~∘lam~> {tail = tail}
⟨ ~∘lam~>  {tail = _ ⹁ _ ∷ tail₁} ⟩∷ tail   = ~∘lam~> {tail = _ ⹁ _ ∷ tail₁ ⦂⦂ tail}
⟨ ~∘pair~> {tail = □} ⟩∷ tail  =  ~∘pair~> {tail = tail}
⟨ ~∘pair~> {tail = _ ⹁ _ ∷ tail₁} ⟩∷ tail  = ~∘pair~> {tail = _ ⹁ _ ∷ tail₁ ⦂⦂ tail}
⟨ ~∘pm~>  {tail = □} ⟩∷ tail    = ~∘pm~> {tail = tail}
⟨ ~∘pm~>  {tail = _ ⹁ _ ∷ tail₁} ⟩∷ tail    = ~∘pm~> {tail = _ ⹁ _ ∷ tail₁ ⦂⦂ tail}
⟨ ~∘unit~> {tail = □} ⟩∷ tail  = ~∘unit~> {tail = tail}
⟨ ~∘unit~> {tail = _ ⹁ _ ∷ tail₁} ⟩∷ tail  = ~∘unit~> {tail = _ ⹁ _ ∷ tail₁ ⦂⦂ tail}
⟨ ~∙M∷pm~> {tail = □} ⟩∷ tail  = ~∙M∷pm~> {tail = tail}
⟨ ~∙M∷pm~> {tail = _ ⹁ _ ∷ tail₁} ⟩∷ tail  = ~∙M∷pm~> {tail = _ ⹁ _ ∷ tail₁ ⦂⦂ tail}
⟨ ~∙M∷l~>  {tail = □} ⟩∷ tail   = ~∙M∷l~> {tail = tail}
⟨ ~∙M∷l~>  {tail = _ ⹁ _ ∷ tail₁} ⟩∷ tail   = ~∙M∷l~> {tail = _ ⹁ _ ∷ tail₁ ⦂⦂ tail}
⟨ ~∙M∷r~>  {tail = □} ⟩∷ tail   = ~∙M∷r~> {tail = tail}
⟨ ~∙M∷r~>  {tail = _ ⹁ _ ∷ tail₁} ⟩∷ tail   = ~∙M∷r~> {tail = _ ⹁ _ ∷ tail₁ ⦂⦂ tail}

⟪_⟫∷_ : {from : vState} → {to : vState} → (F>T : from ↠ᵛᵛ to) → (tail : vStack b) → (from :: tail) ↠ᵛᵛ (to :: tail)
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
⟦ S ⟧↥ = ⟦ M ⟧ᵛ γ
-}

gettype : (S : vStack true) → Ty
gettype ((⇡_ {X = X} M) ⹁ γ ∷ □) = X
gettype (⇡ᴹ {Z = Z} M N ⹁ γ ∷ □) = Z
gettype (⇡ᴸ {X = X} {Y = Y} LHS RHS ⹁ γ ∷ □) = (X `× Y)
gettype (⇡ᴿ {X = X} {Y = Y} LHS RHS ⹁ γ ∷ □) = (X `× Y)
gettype (⇡ M ⹁ γ ∷ x' ⹁ γ' ∷ S) = gettype (x' ⹁ γ' ∷ S)
gettype (⇡ᴹ M N ⹁ γ ∷ x' ⹁ γ' ∷ S) = gettype (x' ⹁ γ' ∷ S)
gettype (⇡ᴸ LHS RHS ⹁ γ ∷ x' ⹁ γ' ∷ S) = gettype (x' ⹁ γ' ∷ S)
gettype (⇡ᴿ LHS RHS ⹁ γ ∷ x' ⹁ γ' ∷ S) = gettype (x' ⹁ γ' ∷ S)

⟦_⟧↥ : (S : vStack true) → ⟦ (gettype S) ⟧
⟦ ⇡ M ⹁ γ ∷ □ ⟧↥ = ⟦ M ⟧ᵛ γ
⟦ ⇡ᴹ M N ⹁ γ ∷ □ ⟧↥ =  ⟦ pm M N ⟧ᵛ γ
⟦ ⇡ᴸ LHS RHS ⹁ γ ∷ □ ⟧↥ =  ⟦ pair LHS RHS ⟧ᵛ γ
⟦ ⇡ᴿ LHS RHS ⹁ γ ∷ □ ⟧↥ =  ⟦ pair LHS RHS ⟧ᵛ γ
⟦ ⇡ M ⹁ γ ∷ M' ⹁ γ' ∷ S ⟧↥ =  ⟦ M' ⹁ γ' ∷ S ⟧↥
⟦ ⇡ᴹ M N ⹁ γ ∷ M' ⹁ γ' ∷ S ⟧↥ = ⟦ M' ⹁ γ' ∷ S ⟧↥
⟦ ⇡ᴸ LHS RHS ⹁ γ ∷ M' ⹁ γ' ∷ S ⟧↥ = ⟦ M' ⹁ γ' ∷ S ⟧↥
⟦ ⇡ᴿ LHS RHS ⹁ γ ∷ M' ⹁ γ' ∷ S ⟧↥ = ⟦ M' ⹁ γ' ∷ S ⟧↥

getstatetype : (S : vState) → Ty
getstatetype (∘ x) = gettype x
getstatetype (∙ x) = gettype x

⟦_⟧◑ : (S : vState) → ⟦ getstatetype S ⟧
⟦ ∘ tail ⟧◑ = ⟦ tail ⟧↥
⟦ ∙ tail ⟧◑ = ⟦ tail ⟧↥

{-
data vHaltingState : vState T◾ → Set where

     ∙var_⹁_■ : (i : Γ ∋ X) → (γ : ⟦ Γ ⟧ˣ) → haltingVState (∙[var] (var i) ﹐ γ ■)

     ∙unit⹁_■ : (γ : ⟦ Γ ⟧ˣ) → haltingVState (∙[unit] unit ﹐ γ ■)

     ∙pair[_⹁_]⹁_■ : (LHS : Γ ⊢ᵛ X) → (RHS : Γ ⊢ᵛ Y) → (γ : ⟦ Γ ⟧ˣ) → haltingVState (∙[pair] pair LHS RHS ﹐ γ ■)

     ∙lam_⹁_■ : (M : (Γ ∙ X) ⊢ᶜ Y) → (γ : ⟦ Γ ⟧ˣ) → haltingVState (∙[lam] lam M ﹐ γ ■)
-}

-- data correctSteps : vState T◾ → Set where
-- 
--   steps : {S T : vState T◾} → S ↠ᵛᵛ T → ⟦ S ⟧ ≡ ⟦ T ⟧ → vHaltingState T → correctSteps S
-- 
-- eval : (M : Γ ⊢ᵛ X) → (γ : ⟦ Γ ⟧ˣ) → correctSteps (∘ M ﹐ γ ■)

-- eval (var i) γ = steps ((∘ var i ﹐ γ ■) ~>ᵛᵛ⟨ ~∘var~> ⟩) (∙var i ⹁ γ ■)
-- eval (lam M) γ = steps ((∘ lam M ﹐ γ ■) ~>ᵛᵛ⟨ ~∘lam~> ⟩) (∙lam M ⹁ γ ■)
-- eval unit γ = steps ((∘ unit ﹐ γ ■) ~>ᵛᵛ⟨ ~∘unit~> ⟩) ∙unit⹁ γ ■
-- eval (pair LHS RHS) γ with eval LHS γ | eval RHS γ
-- ... | steps {T = T'} LHS>>T' HT' | steps {T = T''} RHS>>T'' HT'' = get-pair-steps {T' = T'} {T'' = T''} {HT' = HT'} {HT'' = HT''} γ LHS RHS LHS>>T' RHS>>T''
-- eval (pm M N) γ with eval M γ
-- ... | steps {T = T'} M>>T' HT' with eval N (get-pm-N-env T' HT' γ)
-- ...       |    steps {T = T''} N>>T'' HT'' = get-pm-steps {T' = T'} {T'' = T''} {HT' = HT'} {HT'' = HT''} γ M N M>>T' N>>T''
