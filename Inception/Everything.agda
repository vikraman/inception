module Inception.Everything where

-- rewriting
import Inception.Rewriting
import Inception.Rewriting.Acc
import Inception.Rewriting.Closure
import Inception.Rewriting.Normal
import Inception.Rewriting.Reduction
import Inception.Rewriting.SN
import Inception.Rewriting.Simulation

-- continuation monad
import Inception.Cont.Base
import Inception.Cont.Repr

-- lambda calculi
import Inception.Lam
import Inception.LamPm

-- substitution calculus
import Inception.Sub.Syntax
import Inception.Sub.Machine
import Inception.Sub.Examples
import Inception.Sub.Semantics

-- inception calculus
import Inception.Inc.Syntax
import Inception.Inc.CPS

-- system L
import Inception.SystemL.Syntax
import Inception.SystemL.CBV
