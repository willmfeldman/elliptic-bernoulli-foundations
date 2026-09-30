/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Flatness.Linearized
import EllipticBernoulli.Common.Calculus
import EllipticBernoulli.Flatness.Barriers
import EllipticBernoulli.Viscosity.Basic
import EllipticBernoulli.Viscosity.Calculus
import EllipticBernoulli.Viscosity.Jet

/-!
# Test-function calculus for the linearized limit

Gradient, Laplacian and jet identities for the test functions `y ↦ ⟪y, e⟫` and
`φ + a ⟪·, e⟫ + κ ⟪·, e⟫²`, and two elementary inner-product bounds for unit directions, used in
the touching tests of `linearized_limit`.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Test-function calculus -/

/-- The gradient of `y ↦ ⟪y, e⟫` is `e`. -/
theorem gradient_inner_const (e x : E d) : ∇ (fun y : E d ↦ ⟪y, e⟫) x = e := by
  have h := hasGradientAt_mul_inner_add_mul (W := fun _ : E d ↦ (0 : ℝ)) (G := 0) (e := e) (x := x)
    (hasGradientAt_const x 0) 1 0 0
  have hf : (fun y : E d ↦ 1 * ⟪y, e⟫ + 0 + 0 * (fun _ : E d ↦ (0 : ℝ)) y) =
      fun y ↦ ⟪y, e⟫ := by funext y; ring
  rw [hf] at h
  rw [h.gradient]
  simp

/-- `Δ (y ↦ ⟪y, e⟫²) = 2 |e|²`. -/
theorem laplacian_inner_sq (e x : E d) : Δ (fun y : E d ↦ ⟪y, e⟫ ^ 2) x = 2 * ‖e‖ ^ 2 := by
  have hg : ContDiff ℝ 2 (fun y : E d ↦ ⟪y, e⟫) := contDiff_id.inner ℝ contDiff_const
  have hlap : Δ (fun y : E d ↦ ⟪y, e⟫) x = 0 := by
    have := laplacian_mul_inner_add e 1 0 x
    simpa using this
  have hf : ContDiffAt ℝ 2 (fun t : ℝ ↦ t ^ 2) ⟪x, e⟫ := (contDiff_id.pow 2).contDiffAt
  have h := laplacian_comp (g := fun y : E d ↦ ⟪y, e⟫) (x := x) hf hg.contDiffAt
  rw [gradient_inner_const, hlap, mul_zero, add_zero] at h
  have hd : deriv (fun t : ℝ ↦ t ^ 2) = fun t ↦ 2 * t := by
    funext t; simp
  have hdd : deriv (fun t : ℝ ↦ 2 * t) = fun _ ↦ 2 := by
    funext t; simp
  rw [h, hd, hdd]

/-- **Jet of the Remark's perturbation** (De Silva (2011), the Remark after Definition 2.5):
`φ̃ = φ + a ⟪·, e⟫ + κ ⟪·, e⟫²` is smooth, and at a point `x` of the plane `⟪x, e⟫ = 0` it has
`Δφ̃(x) = Δφ(x) + 2κ|e|²` and `∇φ̃(x) = ∇φ(x) + a e`. -/
theorem jet_add_inner_sq {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) (e : E d) (a κ : ℝ) {x : E d}
    (hx : ⟪x, e⟫ = 0) :
    ContDiff ℝ ∞ (fun y ↦ φ y + a * ⟪y, e⟫ + κ * ⟪y, e⟫ ^ 2) ∧
      Δ (fun y ↦ φ y + a * ⟪y, e⟫ + κ * ⟪y, e⟫ ^ 2) x = Δ φ x + 2 * κ * ‖e‖ ^ 2 ∧
      ∇ (fun y ↦ φ y + a * ⟪y, e⟫ + κ * ⟪y, e⟫ ^ 2) x = ∇ φ x + a • e := by
  have hi : ContDiff ℝ ∞ (fun y : E d ↦ ⟪y, e⟫) := contDiff_id.inner ℝ contDiff_const
  have hq : ContDiff ℝ ∞ (fun y : E d ↦ κ * ⟪y, e⟫ ^ 2) := contDiff_const.mul (hi.pow 2)
  have hl : ContDiff ℝ ∞ (fun y : E d ↦ a * ⟪y, e⟫) := contDiff_const.mul hi
  refine ⟨(hφ.add hl).add hq, ?_, ?_⟩
  · have h1 : ContDiffAt ℝ 2 (fun y ↦ φ y + a * ⟪y, e⟫) x :=
      (contDiff_two_of_smooth (hφ.add hl)).contDiffAt
    have h2 : ContDiffAt ℝ 2 (fun y : E d ↦ κ * ⟪y, e⟫ ^ 2) x :=
      (contDiff_two_of_smooth hq).contDiffAt
    have h3 := h1.laplacian_add h2
    have h4 := (contDiff_two_of_smooth hφ).contDiffAt.laplacian_add
      (contDiff_two_of_smooth hl).contDiffAt (x := x)
    have h5 : Δ (fun y : E d ↦ a * ⟪y, e⟫) x = 0 := by
      have := laplacian_mul_inner_add e a 0 x
      simpa using this
    have h6 : Δ (fun y : E d ↦ κ * ⟪y, e⟫ ^ 2) x = κ * (2 * ‖e‖ ^ 2) := by
      have := laplacian_smul κ (contDiff_two_of_smooth (hi.pow 2)).contDiffAt (x := x)
      rw [laplacian_inner_sq] at this
      exact this
    change Δ ((fun y ↦ φ y + a * ⟪y, e⟫) + fun y : E d ↦ κ * ⟪y, e⟫ ^ 2) x = _
    rw [h3]
    change Δ (φ + fun y : E d ↦ a * ⟪y, e⟫) x + _ = _
    rw [h4, h5, h6]
    ring
  · have hdφ : HasGradientAt φ (∇ φ x) x :=
      ((hφ.differentiable (by simp)) x).hasGradientAt
    -- `y ↦ κ ⟪y, e⟫²` has zero gradient at `x`
    have hsq : HasFDerivAt (fun y : E d ↦ κ * ⟪y, e⟫ ^ 2) (0 : E d →L[ℝ] ℝ) x := by
      have hin : HasFDerivAt (fun y : E d ↦ ⟪y, e⟫) (fderiv ℝ (fun y : E d ↦ ⟪y, e⟫) x) x :=
        ((hi.differentiable (by simp)) x).hasFDerivAt
      have := (hin.pow 2).const_mul κ
      simpa [hx] using this
    have hW : HasGradientAt (fun y ↦ φ y + κ * ⟪y, e⟫ ^ 2) (∇ φ x) x := by
      rw [hasGradientAt_iff_hasFDerivAt] at hdφ ⊢
      have h2 : HasFDerivAt (fun y ↦ φ y + κ * ⟪y, e⟫ ^ 2) _ x := hdφ.add hsq
      simpa using h2
    have h := hasGradientAt_mul_inner_add_mul (e := e) hW a 0 1
    have hf : (fun y ↦ a * ⟪y, e⟫ + 0 + 1 * (fun y ↦ φ y + κ * ⟪y, e⟫ ^ 2) y) =
        fun y ↦ φ y + a * ⟪y, e⟫ + κ * ⟪y, e⟫ ^ 2 := by funext y; ring
    rw [hf] at h
    rw [h.gradient, one_smul, add_comm]

/-- Algebra of the free-boundary condition from below: `|e + ε v| ≤ 1 + ε²` forces
`⟪v, e⟫ ≤ ε + ε³/2`. -/
theorem inner_le_of_norm_add_smul_le {e v : E d} {ε : ℝ} (he : ‖e‖ = 1) (hε : 0 < ε)
    (h : ‖e + ε • v‖ ≤ 1 + ε ^ 2) : ⟪v, e⟫ ≤ ε + ε ^ 3 / 2 := by
  have hsq : ‖e + ε • v‖ ^ 2 ≤ (1 + ε ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [norm_add_sq_real, inner_smul_right, norm_smul, he, Real.norm_eq_abs, abs_of_pos hε,
    real_inner_comm] at hsq
  have hv : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  have : 2 * ε * ⟪v, e⟫ ≤ 2 * ε * (ε + ε ^ 3 / 2) := by nlinarith
  exact le_of_mul_le_mul_left this (by positivity)

/-- Algebra of the free-boundary condition from above: `1 - ε² ≤ |e + ε v|`, `ε ≤ 1`, forces
`⟪v, e⟫ ≥ -ε (2 + |v|²)/2`. -/
theorem le_inner_of_le_norm_add_smul {e v : E d} {ε : ℝ} (he : ‖e‖ = 1) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (h : 1 - ε ^ 2 ≤ ‖e + ε • v‖) : -(ε * (2 + ‖v‖ ^ 2) / 2) ≤ ⟪v, e⟫ := by
  have h0 : 0 ≤ 1 - ε ^ 2 := by nlinarith
  have hsq : (1 - ε ^ 2) ^ 2 ≤ ‖e + ε • v‖ ^ 2 := pow_le_pow_left₀ h0 h 2
  rw [norm_add_sq_real, inner_smul_right, norm_smul, he, Real.norm_eq_abs, abs_of_pos hε,
    real_inner_comm] at hsq
  have : 2 * ε * (-(ε * (2 + ‖v‖ ^ 2) / 2)) ≤ 2 * ε * ⟪v, e⟫ := by nlinarith
  exact le_of_mul_le_mul_left this (by positivity)

end EllipticBernoulli
