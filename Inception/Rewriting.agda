module Inception.Rewriting where

open import Induction.WellFounded public
  using (Acc; acc)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive public
  using (Star; ε; _◅_; _◅◅_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties public
  using (module StarReasoning)
open import Relation.Binary.Construct.Closure.Transitive public
  using (TransClosure; [_])

open import Inception.Rewriting.Acc public
open import Inception.Rewriting.Simulation public

import Inception.Rewriting.Reduction

--------------------------------------------------------------------------
-- reduction relations

module Reduction = Inception.Rewriting.Reduction
