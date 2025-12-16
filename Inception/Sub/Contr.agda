module Inception.Sub.Contr where

open import Data.Product using (proj₁; proj₂; _,_; <_,_>; curry; _×_; Σ; ∃; Σ-syntax; ∃-syntax)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning

open import Inception.Sub.Syntax

wk-ctx : (Γ : Ctx) → Wk Γ ε
wk-ctx Cx.ε = wk-ε
wk-ctx (Γ ∙ X) = wk-wk (wk-ctx Γ)

ctx-merge : (Γ : Ctx) → (Δ : Ctx) → Σ[ Ψ ∈ Ctx ] (Wk Ψ Γ × Wk Ψ Δ)
ctx-merge Cx.ε Cx.ε = ε , wk-ε , wk-ε
ctx-merge Cx.ε (Δ ∙ X) = Δ ∙ X , wk-ctx (Δ ∙ X) , wk-id
ctx-merge (Γ ∙ X) Cx.ε = Γ ∙ X , wk-id , wk-ctx (Γ ∙ X)
ctx-merge (Γ ∙ X) (Δ ∙ Y) =
  let
    a1 = ctx-merge Γ Δ
    Ψ₀ = proj₁ a1
    π₁ = proj₁ (proj₂ a1)
    π₂ = proj₂ (proj₂ a1)
  in
  Ψ₀ ∙ X ∙ Y , wk-wk (wk-cong π₁) , wk-cong (wk-wk π₂)

mutual

  contr-val : Val Γ A → Σ[ Δ ∈ Ctx ] Val Δ A
  contr-val (var {A = A} i) = ε ∙ A , var h
  contr-val (lam W) = let W' = proj₂ (contr-comp W) in _ , lam (wk-comp (wk-wk wk-id) W')
  contr-val (pair {A = A} {B = B} M₁ M₂) =
    let
      a1 = contr-val M₁
      a2 = contr-val M₂
      a3 = ctx-merge (proj₁ a1) (proj₁ a2)
      π₁ = proj₁ (proj₂ a3)
      π₂ = proj₂ (proj₂ a3)
      M₁' = wk-val π₁ (proj₂ a1)
      M₂' = wk-val π₂ (proj₂ a2)
    in
      _ , (pair M₁' M₂')
  contr-val (pm {A = A} {B = B} M N) =
    let
      a1 = contr-val M
      a2 = contr-val N
      a3 = ctx-merge (proj₁ a1) (proj₁ a2)
      π₁ = proj₁ (proj₂ a3)
      π₂ = proj₂ (proj₂ a3)
      M' = wk-val π₁ (proj₂ a1)
      N' = wk-val π₂ (proj₂ a2)
    in
      _ , pm M' (wk-val (wk-wk (wk-wk wk-id)) N')
  contr-val unit = ε , unit

  contr-comp : Comp Γ A → Σ[ Δ ∈ Ctx ] Comp Δ A
  contr-comp (return M) = _ , return (proj₂ (contr-val M))
  contr-comp (pm M W) =
    let
      a1 = contr-val M
      a2 = contr-comp W
      a3 = ctx-merge (proj₁ a1) (proj₁ a2)
      π₁ = proj₁ (proj₂ a3)
      π₂ = proj₂ (proj₂ a3)
      M' = wk-val π₁ (proj₂ a1)
      W' = wk-comp π₂ (proj₂ a2)
    in
      _ , pm M' (wk-comp (wk-wk (wk-wk wk-id)) W')
  contr-comp (push W₁ W₂) =
    let
      a1 = contr-comp W₁
      a2 = contr-comp W₂
      a3 = ctx-merge (proj₁ a1) (proj₁ a2)
      π₁ = proj₁ (proj₂ a3)
      π₂ = proj₂ (proj₂ a3)
      W₁' = wk-comp π₁ (proj₂ a1)
      W₂' = wk-comp π₂ (proj₂ a2)
    in
      _ , push W₁' (wk-comp (wk-wk wk-id) W₂')
  contr-comp (app M N) =
    let
      a1 = contr-val M
      a2 = contr-val N
      a3 = ctx-merge (proj₁ a1) (proj₁ a2)
      π₁ = proj₁ (proj₂ a3)
      π₂ = proj₂ (proj₂ a3)
      M' = wk-val π₁ (proj₂ a1)
      N' = wk-val π₂ (proj₂ a2)
    in
      _ , (app M' N')
  contr-comp (var M) = _ , var (proj₂ (contr-val M))
  contr-comp (sub W₁ W₂) =
    let
      a1 = contr-comp W₁
      a2 = contr-comp W₂
      a3 = ctx-merge (proj₁ a1) (proj₁ a2)
      π₁ = proj₁ (proj₂ a3)
      π₂ = proj₂ (proj₂ a3)
      W₁' = wk-comp π₁ (proj₂ a1)
      W₂' = wk-comp π₂ (proj₂ a2)
    in
      _ , sub (wk-comp (wk-wk wk-id) W₁') W₂'

mutual

  contr-val-eq : {Γ' : Ctx} {X : Ty} → (M : Val Γ' X) → (π : Wk Γ Γ') → contr-val M ≡ contr-val (wk-val π M)
  contr-val-eq (var i) π = refl
  contr-val-eq (lam W) π rewrite contr-comp-eq W (wk-cong π) = refl
  contr-val-eq (pair M₁ M₂) π rewrite contr-val-eq M₁ π | contr-val-eq M₂ π = refl
  contr-val-eq (pm M N) π rewrite contr-val-eq M π | contr-val-eq N (wk-cong (wk-cong π)) = refl
  contr-val-eq unit π = refl

  contr-comp-eq : {Γ' : Ctx} {X : Ty} → (W : Comp Γ' X) → (π : Wk Γ Γ') → contr-comp W ≡ contr-comp (wk-comp π W)
  contr-comp-eq (return M) π rewrite contr-val-eq M π = refl
  contr-comp-eq (pm M W) π rewrite contr-val-eq M π | contr-comp-eq W (wk-cong (wk-cong π)) = refl
  contr-comp-eq (push W₁ W₂) π rewrite contr-comp-eq W₁ π | contr-comp-eq W₂ (wk-cong π) = refl
  contr-comp-eq (app M N) π rewrite contr-val-eq M π | contr-val-eq N π = refl
  contr-comp-eq (var M) π rewrite contr-val-eq M π = refl
  contr-comp-eq (sub W₁ W₂) π rewrite contr-comp-eq W₁ (wk-cong π) | contr-comp-eq W₂ π = refl
