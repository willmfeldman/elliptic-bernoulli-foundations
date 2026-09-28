/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Viscosity
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Headline statements: Lipschitz estimate

Caffarelli–Salsa, Lemma 11.19, for viscosity *super*solutions harmonic in their positivity set,
with a variable coefficient that is only bounded above (the quantitative form) or continuous
(the local form). The theorems proving them live in `EllipticBernoulli/Lipschitz/Estimate.lean`.

## References

* L. A. Caffarelli, S. Salsa, *A Geometric Approach to Free Boundary Problems*, Grad. Stud. Math.
  68, Amer. Math. Soc., 2005.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped NNReal

@[expose] public section

namespace EllipticBernoulli

/-- **Quantitative Lipschitz estimate** (Caffarelli–Salsa, Lemma 11.19). For `1 ≤ d` there is `C`
such that a viscosity supersolution `u` in `U ⊇ B_{2r}(x₀)`, harmonic in `{u > 0}`, with
`Q ≤ Qmax` and `u ≤ M` on `B_{2r}(x₀)`, is `C (Qmax + M / r)`-Lipschitz on `B_r(x₀)`. Proved by
`lipschitzOnWith_of_isViscSuper` (`Lipschitz/Estimate.lean`). -/
def LipschitzEstimateStatement : Prop :=
  ∀ {d : ℕ}, 1 ≤ d → ∃ C : ℝ, ∀ (U : Set (E d)) (Q u : E d → ℝ) (x₀ : E d) (r Qmax M : ℝ),
    IsOpen U → 0 < r → ball x₀ (2 * r) ⊆ U → IsViscSuper U Q u →
    HarmonicOnNhd u (posSet u U) → (∀ y ∈ ball x₀ (2 * r), Q y ≤ Qmax) → 0 ≤ Qmax →
    (∀ y ∈ ball x₀ (2 * r), u y ≤ M) →
    LipschitzOnWith (C * (Qmax + M / r)).toNNReal u (ball x₀ r)

/-- **Local Lipschitz regularity** of viscosity supersolutions harmonic in `{u > 0}`, for
continuous `Q`. Proved by `locallyLipschitzOn_of_isViscSuper` (`Lipschitz/Estimate.lean`). -/
def LocalLipschitzStatement : Prop :=
  ∀ {d : ℕ} {U : Set (E d)} {Q u : E d → ℝ}, IsOpen U → IsViscSuper U Q u →
    HarmonicOnNhd u (posSet u U) → ContinuousOn Q U → LocallyLipschitzOn U u

end EllipticBernoulli
