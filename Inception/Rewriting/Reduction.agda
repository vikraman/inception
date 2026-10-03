module Inception.Rewriting.Reduction {A : Set} (_~>_ : A → A → Set) where

open import Inception.Rewriting.Closure _~>_ public
open import Inception.Rewriting.Normal _~>_ public
open import Inception.Rewriting.SN _~>_ public
