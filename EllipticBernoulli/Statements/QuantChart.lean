/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Variational
public import EllipticBernoulli.Defs.Regularity
public import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# Headline statements: quantitative charts at flat free boundaries

Let `u` be a continuous, non-negative local minimizer of `J(v; B) = ∫_B |∇v|² + 1_{v>0}` in the unit
ball, `ε`-close in sup norm to a half-plane solution `(x · e)₊`. If `ε` is small (depending on the
dimension only), then near the origin `u` is the positive part of a smooth function `F` whose
derivatives are bounded on the closed positive phase, with constants depending on the dimension
only:

* `QuantFlatChartStatement`: on `B_{1/2}`, `u = max(F, 0)`, `|∇F| = 1` on `{F = 0}`, `ΔF = 0` on
  `{F > 0}`; on `{F ≥ 0} ∩ B_{1/2}`, `∇F · e ≥ 1/2`, `|∇F|, |D²F| ≤ C` and `D²F` is `α`-Hölder with
  constant `C`.
* `QuantFlatChartThreeStatement`: the same chart on `B_{1/4}`, with `|D³F| ≤ C₀` on
  `{F ≥ 0} ∩ B_{1/4}`.

These are the quantitative forms of the smooth chart of `FlatChartStatement`: improvement of
flatness (De Silva (2011)) gives a `C^{1,α}` free boundary with estimates, the partial hodograph
transform (Kinderlehrer–Nirenberg (1977)) gives a quasilinear conormal problem on a half ball of
fixed size, and scaled boundary Schauder estimates for that problem bound the higher derivatives.

## References

* D. Kinderlehrer, L. Nirenberg, *Regularity in free boundary problems*, Ann. Sc. Norm. Sup. Pisa
  Cl. Sci. (4) 4 (1977), no. 2, 373–391.
* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer, 2023.
-/

open Set Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace EllipticBernoulli

/-- **Quantitative `C^{2,α}` chart at a flat free boundary.** For `d ≥ 2` there are `ε₀ > 0`,
`α > 0` and `C > 0` with the following property. Let `u` be continuous and non-negative on `B_1`,
a local minimizer of `J(v; B) = ∫_B |∇v|² + 1_{v>0}` in `B_1`, and let `‖e‖ = 1` and `ε ≤ ε₀` with
`|u(x) - (x · e)₊| ≤ ε` on `B_1`. Then there is `F ∈ C^∞(B_{1/2})` with
* `u = max(F, 0)` on `B_{1/2}`, `|∇F| = 1` on `{F = 0} ∩ B_{1/2}`, `ΔF = 0` on `{F > 0} ∩ B_{1/2}`;
* on `{F ≥ 0} ∩ B_{1/2}`: `∇F · e ≥ 1/2`, `|∇F| ≤ C`, `|D²F| ≤ C`, and
  `|D²F(x) - D²F(y)| ≤ C |x - y|^α` for `x, y` in that set. -/
def QuantFlatChartStatement : Prop :=
  ∀ {d : ℕ}, 2 ≤ d → ∃ ε₀ > 0, ∃ α > 0, ∃ C > 0, ∀ {u : E d → ℝ} {e : E d} {ε : ℝ},
    ContinuousOn u (ball 0 1) → (∀ x ∈ ball (0 : E d) 1, 0 ≤ u x) →
    IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u → ‖e‖ = 1 → ε ≤ ε₀ →
    (∀ x ∈ ball (0 : E d) 1, |u x - max (inner ℝ x e) 0| ≤ ε) →
    ∃ F : E d → ℝ, ContDiffOn ℝ ∞ F (ball 0 (1 / 2)) ∧
      (∀ x ∈ ball (0 : E d) (1 / 2), u x = max (F x) 0) ∧
      (∀ x ∈ ball (0 : E d) (1 / 2), F x = 0 → ‖∇ F x‖ = 1) ∧
      (∀ x ∈ ball (0 : E d) (1 / 2), 0 < F x → Δ F x = 0) ∧
      (∀ x ∈ ball (0 : E d) (1 / 2), 0 ≤ F x →
        1 / 2 ≤ inner ℝ (∇ F x) e ∧ ‖∇ F x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 2 F x‖ ≤ C) ∧
      (∀ x ∈ ball (0 : E d) (1 / 2), ∀ y ∈ ball (0 : E d) (1 / 2), 0 ≤ F x → 0 ≤ F y →
        ‖iteratedFDeriv ℝ 2 F x - iteratedFDeriv ℝ 2 F y‖ ≤ C * ‖x - y‖ ^ α)

/-- **Quantitative third-derivative bound at a flat free boundary.** For `d ≥ 2` there are
`ε₀ > 0` and `C₀ > 0` with the following property. Let `u` be continuous and non-negative on
`B_1`, a local minimizer of `J(v; B) = ∫_B |∇v|² + 1_{v>0}` in `B_1`, and let `‖e‖ = 1` and
`ε ≤ ε₀` with `|u(x) - (x · e)₊| ≤ ε` on `B_1`. Then there is `F ∈ C^∞(B_{1/4})` with
* `u = max(F, 0)` on `B_{1/4}`, `|∇F| = 1` on `{F = 0} ∩ B_{1/4}`, `ΔF = 0` on `{F > 0} ∩ B_{1/4}`;
* on `{F ≥ 0} ∩ B_{1/4}`: `∇F · e ≥ 1/2` and `|D³F| ≤ C₀`. -/
def QuantFlatChartThreeStatement : Prop :=
  ∀ {d : ℕ}, 2 ≤ d → ∃ ε₀ > 0, ∃ C₀ > 0, ∀ {u : E d → ℝ} {e : E d} {ε : ℝ},
    ContinuousOn u (ball 0 1) → (∀ x ∈ ball (0 : E d) 1, 0 ≤ u x) →
    IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u → ‖e‖ = 1 → ε ≤ ε₀ →
    (∀ x ∈ ball (0 : E d) 1, |u x - max (inner ℝ x e) 0| ≤ ε) →
    ∃ F : E d → ℝ, ContDiffOn ℝ ∞ F (ball 0 (1 / 4)) ∧
      (∀ x ∈ ball (0 : E d) (1 / 4), u x = max (F x) 0) ∧
      (∀ x ∈ ball (0 : E d) (1 / 4), F x = 0 → ‖∇ F x‖ = 1) ∧
      (∀ x ∈ ball (0 : E d) (1 / 4), 0 < F x → Δ F x = 0) ∧
      (∀ x ∈ ball (0 : E d) (1 / 4), 0 ≤ F x →
        1 / 2 ≤ inner ℝ (∇ F x) e ∧ ‖iteratedFDeriv ℝ 3 F x‖ ≤ C₀)

end EllipticBernoulli
