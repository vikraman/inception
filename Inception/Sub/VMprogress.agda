module Inception.Sub.VMprogress (R : Set) where

open import Inception.Sub.Syntax
open import Inception.Sub.ValueMachine R


data Progress (S : VState T◾) : Set where

     step : {S' : VState T◾} → S ~>ᵛᵛ S' → Progress S

     done : haltingVState S → Progress S


progress : (S : VState T◾) → Progress S

progress (∘_ {M = var _} _) = step ~∘var~>
progress (∘_ {M = lam _} _) = step ~∘lam~>
progress (∘_ {M = pair _ _} _) = step ~∘pair~>
progress (∘_ {M = pm _ _} _) = step ~∘pm~>
progress (∘_ {M = unit} _) = step ~∘unit~>

---

progress (∙[var] (.(var _) ﹐ _ ■)) = done ∙var■
progress (∙[lam] (.(lam _) ﹐ _ ■)) = done ∙lam■
progress (∙[unit] (.unit ﹐ _ ■)) = done ∙unit■
progress (∙[pair] (.(pair _ _) ﹐ _ ■)) = done ∙pair■

---

progress (∙[var] ((var i) ﹐ γ ∷pm⟨ ≡M ⟩ (pm M N) ﹐ γ' ■)) = step (~∙var∷pm■~> γ γ' i M N ≡M)
progress (∙[var] (var i ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙var∷pm∷pm~> γ γ' i M N ≡M ≡M' tail)
progress (∙[var] (var i ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ∷l⟨ ≡LHS ⟩ tail)) = step (~∙var∷pm∷l~> γ γ' i M N ≡M ≡LHS tail)
progress (∙[var] (var i ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ∷r⟨ ≡RHS ⟩ tail)) = step (~∙var∷pm∷r~> γ γ' i M N ≡M ≡RHS tail)

progress (∙[pair] (pair x y ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ■)) = step (~∙pair∷pm■~> γ γ' x y M N ≡M)
progress (∙[pair] (pair x y ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙pair∷pm∷pm~> γ γ' x y M N ≡M ≡M' tail)
progress (∙[pair] (pair x y ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ∷l⟨ ≡LHS ⟩ tail)) = step (~∙pair∷pm∷l~> γ γ' x y M N ≡M ≡LHS tail)
progress (∙[pair] (pair x y ﹐ γ ∷pm⟨ ≡M ⟩ pm M N ﹐ γ' ∷r⟨ ≡RHS ⟩ tail)) = step (~∙pair∷pm∷r~> γ γ' x y M N ≡M ≡RHS tail)

---

progress (∙[var] (var i ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ■)) = step (~∙var∷l■~> γ γ' i LHS RHS ≡LHS)
progress (∙[var] (var i ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙var∷l∷pm~> γ γ' i LHS RHS ≡LHS ≡M' tail)
progress (∙[var] (var i ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙var∷l∷l~> γ γ' i LHS RHS ≡LHS ≡LHS' tail)
progress (∙[var] (var i ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙var∷l∷r~> γ γ' i LHS RHS ≡LHS ≡RHS' tail)

progress (∙[lam] (lam M ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ■)) = step (~∙lam∷l■~> γ γ' M LHS RHS ≡LHS)
progress (∙[lam] (lam M ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙lam∷l∷pm~> γ γ' M LHS RHS ≡LHS ≡M' tail)
progress (∙[lam] (lam M ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙lam∷l∷l~> γ γ' M LHS RHS ≡LHS ≡LHS' tail)
progress (∙[lam] (lam M ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙lam∷l∷r~> γ γ' M LHS RHS ≡LHS ≡RHS' tail)

progress (∙[unit] (unit ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ■)) = step (~∙unit∷l■~> γ γ' LHS RHS ≡LHS)
progress (∙[unit] (unit ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙unit∷l∷pm~> γ γ' LHS RHS ≡LHS ≡M' tail)
progress (∙[unit] (unit ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙unit∷l∷l~> γ γ' LHS RHS ≡LHS ≡LHS' tail)
progress (∙[unit] (unit ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙unit∷l∷r~> γ γ' LHS RHS ≡LHS ≡RHS' tail)

progress (∙[pair] (pair x y ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ■)) = step (~∙pair∷l■~> γ γ' x y LHS RHS ≡LHS)
progress (∙[pair] (pair x y ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙pair∷l∷pm~> γ γ' x y LHS RHS ≡LHS ≡M' tail)
progress (∙[pair] (pair x y ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙pair∷l∷l~> γ γ' x y LHS RHS ≡LHS ≡LHS' tail)
progress (∙[pair] (pair x y ﹐ γ ∷l⟨ ≡LHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙pair∷l∷r~> γ γ' x y LHS RHS ≡LHS ≡RHS' tail)

---

progress (∙[var] (var i ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ■)) = step (~∙var∷r■~> γ γ' i LHS RHS ≡RHS)
progress (∙[var] (var i ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙var∷r∷pm~> γ γ' i LHS RHS ≡RHS ≡M' tail)
progress (∙[var] (var i ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙var∷r∷l~> γ γ' i LHS RHS ≡RHS ≡LHS' tail)
progress (∙[var] (var i ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙var∷r∷r~> γ γ' i LHS RHS ≡RHS ≡RHS' tail)

progress (∙[lam] (lam M ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ■)) = step (~∙lam∷r■~> γ γ' M LHS RHS ≡RHS)
progress (∙[lam] (lam M ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙lam∷r∷pm~> γ γ' M LHS RHS ≡RHS ≡M' tail)
progress (∙[lam] (lam M ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙lam∷r∷l~> γ γ' M LHS RHS ≡RHS ≡LHS' tail)
progress (∙[lam] (lam M ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙lam∷r∷r~> γ γ' M LHS RHS ≡RHS ≡RHS' tail)

progress (∙[unit] (unit ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ■)) = step (~∙unit∷r■~> γ γ' LHS RHS ≡RHS)
progress (∙[unit] (unit ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙unit∷r∷pm~> γ γ' LHS RHS ≡RHS ≡M' tail)
progress (∙[unit] (unit ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙unit∷r∷l~> γ γ' LHS RHS ≡RHS ≡LHS' tail)
progress (∙[unit] (unit ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙unit∷r∷r~> γ γ' LHS RHS ≡RHS ≡RHS' tail)

progress (∙[pair] (pair x y ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ■)) = step (~∙pair∷r■~> γ γ' x y LHS RHS ≡RHS)
progress (∙[pair] (pair x y ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷pm⟨ ≡M' ⟩ tail)) = step (~∙pair∷r∷pm~> γ γ' x y LHS RHS ≡RHS ≡M' tail)
progress (∙[pair] (pair x y ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷l⟨ ≡LHS' ⟩ tail)) = step (~∙pair∷r∷l~> γ γ' x y LHS RHS ≡RHS ≡LHS' tail)
progress (∙[pair] (pair x y ﹐ γ ∷r⟨ ≡RHS ⟩ pair LHS RHS ﹐ γ' ∷r⟨ ≡RHS' ⟩ tail)) = step (~∙pair∷r∷r~> γ γ' x y LHS RHS ≡RHS ≡RHS' tail)
