/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.LinearAlgebra.Trace

/-!
# Standing setting

The ambient space, positivity sets, free boundaries, compact containment and the divergence,
following Abedin–Feldman–Stinson. There is no global setting: statements are local, with explicit
hypotheses on `U` and `Q`.

## Conventions

* All functions are total (`E d → ℝ`); every predicate restricts to its domain explicitly, and
  values outside the domain are never used.

Challenge vocabulary: a Mathlib-only restatement of the library file
`EllipticBernoulli/Basic/Setting.lean`, with the module
system syntax removed and its theorems dropped. The definitions are verbatim and in the
library order, so Comparator can check that they are the library's definitions.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology
open scoped Gradient Laplacian

noncomputable section

namespace EllipticBernoulli

/-- The ambient Euclidean space `ℝᵈ`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- The positivity set `{u > 0}` of `u` inside the domain `U` (the set `{u > 0}` of
Abedin–Feldman–Stinson, with `u` defined on `U` only). -/
def posSet (u : E d → ℝ) (U : Set (E d)) : Set (E d) := {x ∈ U | 0 < u x}

/-- The free boundary `∂{u > 0} ∩ U` (Abedin–Feldman–Stinson, (1.1) and Theorem 1.1). -/
def freeBoundary (u : E d → ℝ) (U : Set (E d)) : Set (E d) := frontier (posSet u U) ∩ U

section CompactlyContained

variable {X : Type*} [TopologicalSpace X]

/-- `A ⊂⊂ B`: the closure of `A` is compact and contained in `B`. -/
def CompactlyContained (A B : Set X) : Prop := IsCompact (closure A) ∧ closure A ⊆ B

end CompactlyContained

/-! ### Differential operators -/

/-- The divergence `∇ · ξ = tr (Dξ)` of a vector field `ξ : ℝᵈ → ℝᵈ` (pointwise, via `fderiv`;
`0` where `ξ` is not differentiable). -/
noncomputable def divergence (ξ : E d → E d) (x : E d) : ℝ :=
  LinearMap.trace ℝ (E d) (fderiv ℝ ξ x).toLinearMap

end EllipticBernoulli
