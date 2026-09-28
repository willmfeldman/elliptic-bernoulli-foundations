/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Viscosity

/-!
# The linearized (Neumann) problem of De Silva's improvement of flatness

De Silva (2011), (2.2), Definition 2.5, the Remark after it, and Lemma 2.6.

The linearized problem in direction `e` on the half-ball `H⁺ = {⟪x, e⟫ ≥ 0} ∩ B_ρ` is
`Δw = 0` in `{⟪x, e⟫ > 0} ∩ B_ρ`, `∂_e w = 0` on `{⟪x, e⟫ = 0} ∩ B_ρ`.

* `halfBall e ρ`: the closed (relative to `B_ρ`) half-ball `{⟪x, e⟫ ≥ 0} ∩ B_ρ`.
* `IsLinearizedSolution w e ρ`: De Silva's Definition 2.5, with globally `C^∞` test functions in
  place of quadratic polynomials. Touching is relative to `halfBall e ρ`. At boundary points there
  is **no Laplacian alternative**: a test touching from below has `⟪∇φ, e⟫ ≤ 0`, one
  touching from above has `⟪∇φ, e⟫ ≥ 0`. For quadratic polynomials and `C^∞` tests the two notions
  agree (replace `φ` by its 2-jet plus `∓ η |x - x̄|²`); we only ever use the `C^∞` form.

Its regularity (De Silva (2011), Lemma 2.6, and the `C²` bound `linearized_C2_at_origin`) is in
`Flatness/LinearizedRegularity.lean`, which needs the harmonic-function toolkit (`Harmonic/*`).

## References

* D. De Silva, *Free boundary regularity for a problem with right hand side*, Interfaces Free Bound.
  13 (2011), no. 2, 223–238; arXiv:0912.2057.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- The half-ball `{x : ⟪x, e⟫ ≥ 0} ∩ B_ρ(0)` (De Silva's `B_ρ ∩ {x_n ≥ 0}`). -/
def halfBall (e : E d) (ρ : ℝ) : Set (E d) := {x | 0 ≤ ⟪x, e⟫} ∩ ball 0 ρ

/-- **De Silva (2011), Definition 2.5** (viscosity solutions of the linearized problem (2.2)), in
direction `e` on `B_ρ`, with globally `C^∞` test functions touching relative to the half-ball
`halfBall e ρ`:
* `w` is continuous on `halfBall e ρ`;
* if `φ` touches `w` from below at `x` then `Δφ(x) ≤ 0` when `⟪x, e⟫ > 0`, and `⟪∇φ(x), e⟫ ≤ 0`
  when `⟪x, e⟫ = 0`;
* if `φ` touches `w` from above at `x` then `Δφ(x) ≥ 0` when `⟪x, e⟫ > 0`, and `⟪∇φ(x), e⟫ ≥ 0`
  when `⟪x, e⟫ = 0`.

There is no Laplacian alternative at boundary points (De Silva (2011), Definition 2.5(ii)). -/
def IsLinearizedSolution (w : E d → ℝ) (e : E d) (ρ : ℝ) : Prop :=
  ContinuousOn w (halfBall e ρ) ∧
    (∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → ∀ x, TouchesBelow φ w (halfBall e ρ) x →
      (0 < ⟪x, e⟫ → Δ φ x ≤ 0) ∧ (⟪x, e⟫ = 0 → ⟪∇ φ x, e⟫ ≤ 0)) ∧
    ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → ∀ x, TouchesAbove φ w (halfBall e ρ) x →
      (0 < ⟪x, e⟫ → 0 ≤ Δ φ x) ∧ (⟪x, e⟫ = 0 → 0 ≤ ⟪∇ φ x, e⟫)

end EllipticBernoulli

end

public section

namespace EllipticBernoulli

variable {d : ℕ}

theorem mem_halfBall {e x : E d} {ρ : ℝ} : x ∈ halfBall e ρ ↔ 0 ≤ ⟪x, e⟫ ∧ x ∈ ball 0 ρ :=
  Iff.rfl

end EllipticBernoulli
