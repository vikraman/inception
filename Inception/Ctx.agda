module Inception.Ctx (Ty : Set) where

import Inception.Ctx.Sem

open import Inception.Ctx.Base Ty public
open import Inception.Ctx.Sub Ty public
open import Inception.Ctx.Wk Ty public

module Sem = Inception.Ctx.Sem Ty
