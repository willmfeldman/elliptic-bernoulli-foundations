/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

import Mathlib.Topology.ContinuousOn
import Mathlib.Data.Real.Basic

/-!
# Touching from above and below

The touching relations used in the viscosity definitions (Abedin–Feldman–Stinson,
Definitions 2.1 and 2.3). Generic over a topological space `X`.

Challenge vocabulary: a Mathlib-only restatement of the library file
`EllipticBernoulli/Basic/Touching.lean`, with the module
system syntax removed and its theorems dropped. The definitions are verbatim and in the
library order, so Comparator can check that they are the library's definitions.

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions in
  the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology

noncomputable section

namespace EllipticBernoulli

variable {X : Type*} [TopologicalSpace X]

/-- `φ` touches `u` from below in `S` at `x`: `x ∈ S`, `φ x = u x`, and `φ ≤ u` on a relative
neighbourhood of `x` in `S` (non-strict, local touching; Abedin–Feldman–Stinson,
Definition 2.1(i)). -/
def TouchesBelow (φ u : X → ℝ) (S : Set X) (x : X) : Prop :=
  x ∈ S ∧ φ x = u x ∧ ∀ᶠ y in 𝓝[S] x, φ y ≤ u y

/-- `φ` touches `u` from above in `S` at `x`: `x ∈ S`, `φ x = u x`, and `u ≤ φ` on a relative
neighbourhood of `x` in `S` (Abedin–Feldman–Stinson, Definitions 2.1(ii) and 2.3). -/
def TouchesAbove (φ u : X → ℝ) (S : Set X) (x : X) : Prop :=
  x ∈ S ∧ φ x = u x ∧ ∀ᶠ y in 𝓝[S] x, u y ≤ φ y

end EllipticBernoulli
