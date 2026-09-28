/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Viscosity.Calculus
public import EllipticBernoulli.Basic.Setting
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# A strictly subharmonic radial barrier

The barrier of the Lipschitz estimate (Caffarelli–Salsa, Lemma 11.19) is the Gaussian
profile
`radialSubBarrier x ρ λ A z = A (exp (-λ |z - x|²) - exp (-λ ρ²))`.
It vanishes on `∂B_ρ(x)`, is `≤ 0` outside `B_ρ(x)`, is globally `C^∞`, and is **strictly**
subharmonic where `2 λ |z - x|² > d`:
`Δ = 2 A λ exp (-λ |z - x|²) (2 λ |z - x|² - d)` and
`|∇| = 2 |A| λ |z - x| exp (-λ |z - x|²)`.

A power barrier `|z - x|^{-γ}` would need smoothing near `x`; the Gaussian is globally smooth, and
it is strictly subharmonic away from a small ball, which is all the proof uses (Caffarelli–Salsa
use the same device).

## References

* L. A. Caffarelli, S. Salsa, *A Geometric Approach to Free Boundary Problems*, Grad. Stud. Math.
  68, Amer. Math. Soc., 2005.
-/

open Set Filter Topology InnerProductSpace
open scoped ContDiff Gradient Laplacian

@[expose] public noncomputable section

namespace EllipticBernoulli

/-! ### Quadratic functions -/

section Quadratic

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem hasFDerivAt_normSq_sub_const (x₀ y : F) :
    HasFDerivAt (fun y ↦ ‖y - x₀‖ ^ 2) ((2 : ℝ) • innerSL ℝ (y - x₀)) y := by
  convert ((hasFDerivAt_id y).sub_const x₀).norm_sq using 1
  ext v
  simp [two_smul]

theorem contDiff_normSq_sub_const (x₀ : F) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun y ↦ ‖y - x₀‖ ^ 2) :=
  (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)

/-- `|∇ ‖y - x₀‖²| = 2 ‖y - x₀‖`. -/
theorem norm_gradient_normSq_sub [CompleteSpace F] (x₀ x : F) :
    ‖∇ (fun y ↦ ‖y - x₀‖ ^ 2) x‖ = 2 * ‖x - x₀‖ := by
  rw [show ‖∇ (fun y ↦ ‖y - x₀‖ ^ 2) x‖ = ‖fderiv ℝ (fun y ↦ ‖y - x₀‖ ^ 2) x‖ by simp [gradient],
    (hasFDerivAt_normSq_sub_const x₀ x).fderiv, norm_smul, innerSL_apply_norm]
  norm_num

/-- `Δ ‖y - x₀‖² = 2 dim F`. -/
theorem laplacian_normSq_sub_const [FiniteDimensional ℝ F] (x₀ x : F) :
    Δ (fun y ↦ ‖y - x₀‖ ^ 2) x = 2 * Module.finrank ℝ F := by
  have hf : fderiv ℝ (fun y ↦ ‖y - x₀‖ ^ 2) = fun y ↦ (2 : ℝ) • innerSL ℝ (y - x₀) :=
    funext fun y ↦ (hasFDerivAt_normSq_sub_const x₀ y).fderiv
  rw [laplacian_eq_sum_fderiv_fderiv, hf]
  have hd : HasFDerivAt (fun y ↦ (2 : ℝ) • innerSL ℝ (y - x₀)) ((2 : ℝ) • innerSL ℝ) x := by
    have := ((innerSL ℝ (E := F)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x₀))
    exact this.const_smul (2 : ℝ)
  rw [hd.fderiv]
  have h1 : ∀ i, ((2 : ℝ) • innerSL ℝ (E := F)) (stdOrthonormalBasis ℝ F i)
      (stdOrthonormalBasis ℝ F i) = 2 := fun i ↦ by
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
      real_inner_self_eq_norm_sq, (stdOrthonormalBasis ℝ F).orthonormal.1 i]
    norm_num
  refine (Finset.sum_congr rfl fun i _ ↦ h1 i).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Quadratic

/-! ### The Gaussian barrier -/

/-- The one-variable profile `t ↦ A (exp (-λ t) - exp (-λ ρ²))`. -/
def radialSubProfile (ρ lam A : ℝ) (t : ℝ) : ℝ :=
  A * (Real.exp (-(lam * t)) - Real.exp (-(lam * ρ ^ 2)))

variable {d : ℕ}

/-- **The strictly subharmonic radial barrier** `A (exp (-λ |z - x|²) - exp (-λ ρ²))`. -/
def radialSubBarrier (x : E d) (ρ lam A : ℝ) (z : E d) : ℝ :=
  radialSubProfile ρ lam A (‖z - x‖ ^ 2)

variable {x : E d} {ρ lam A : ℝ}

theorem radialSubBarrier_apply (z : E d) : radialSubBarrier x ρ lam A z =
    A * (Real.exp (-(lam * ‖z - x‖ ^ 2)) - Real.exp (-(lam * ρ ^ 2))) := rfl

theorem contDiff_radialSubProfile {n : WithTop ℕ∞} : ContDiff ℝ n (radialSubProfile ρ lam A) := by
  unfold radialSubProfile; fun_prop

theorem contDiff_radialSubBarrier {n : WithTop ℕ∞} :
    ContDiff ℝ n (radialSubBarrier x ρ lam A) :=
  contDiff_radialSubProfile.comp (contDiff_normSq_sub_const x)

theorem hasDerivAt_radialSubProfile (t : ℝ) :
    HasDerivAt (radialSubProfile ρ lam A) (-(A * lam * Real.exp (-(lam * t)))) t := by
  have h1 : HasDerivAt (fun t : ℝ ↦ -(lam * t)) (-lam) t := by
    simpa using ((hasDerivAt_id t).const_mul lam).neg
  have h2 := (h1.exp.sub_const (Real.exp (-(lam * ρ ^ 2)))).const_mul A
  convert h2 using 1
  ring

theorem deriv_radialSubProfile :
    deriv (radialSubProfile ρ lam A) = fun t ↦ -(A * lam * Real.exp (-(lam * t))) :=
  funext fun t ↦ (hasDerivAt_radialSubProfile t).deriv

theorem deriv_deriv_radialSubProfile (t : ℝ) :
    deriv (deriv (radialSubProfile ρ lam A)) t = A * lam ^ 2 * Real.exp (-(lam * t)) := by
  rw [deriv_radialSubProfile]
  have h1 : HasDerivAt (fun t : ℝ ↦ -(lam * t)) (-lam) t := by
    simpa using ((hasDerivAt_id t).const_mul lam).neg
  have h2 : HasDerivAt (fun t ↦ -(A * lam * Real.exp (-(lam * t))))
      (-(A * lam * (Real.exp (-(lam * t)) * -lam))) t := (h1.exp.const_mul (A * lam)).neg
  rw [h2.deriv]
  ring

/-- The barrier vanishes on `∂B_ρ(x)`. -/
theorem radialSubBarrier_eq_zero {z : E d} (hz : ‖z - x‖ = ρ) :
    radialSubBarrier x ρ lam A z = 0 := by
  rw [radialSubBarrier_apply, hz, sub_self, mul_zero]

/-- The barrier is `≤ 0` outside `B_ρ(x)`. -/
theorem radialSubBarrier_nonpos (hA : 0 ≤ A) (hlam : 0 ≤ lam) (hρ : 0 ≤ ρ) {z : E d}
    (hz : ρ ≤ ‖z - x‖) : radialSubBarrier x ρ lam A z ≤ 0 := by
  rw [radialSubBarrier_apply]
  refine mul_nonpos_of_nonneg_of_nonpos hA (sub_nonpos.2 (Real.exp_le_exp.2 ?_))
  have : ρ ^ 2 ≤ ‖z - x‖ ^ 2 := pow_le_pow_left₀ hρ hz 2
  nlinarith

/-- **Laplacian of the barrier:** `Δ = 2 A λ exp (-λ |z - x|²) (2 λ |z - x|² - d)`. -/
theorem laplacian_radialSubBarrier (z : E d) :
    Δ (radialSubBarrier x ρ lam A) z =
      2 * A * lam * Real.exp (-(lam * ‖z - x‖ ^ 2)) * (2 * lam * ‖z - x‖ ^ 2 - d) := by
  have h := laplacian_comp (f := radialSubProfile ρ lam A) (g := fun y : E d ↦ ‖y - x‖ ^ 2)
    (x := z) contDiff_radialSubProfile.contDiffAt (contDiff_normSq_sub_const x).contDiffAt
  change Δ (fun y ↦ radialSubProfile ρ lam A (‖y - x‖ ^ 2)) z = _
  rw [h, deriv_deriv_radialSubProfile, deriv_radialSubProfile, norm_gradient_normSq_sub,
    laplacian_normSq_sub_const, finrank_euclideanSpace_fin]
  ring

/-- **Strict subharmonicity** where `d < 2 λ |z - x|²`. -/
theorem laplacian_radialSubBarrier_pos (hA : 0 < A) (hlam : 0 < lam) {z : E d}
    (hz : (d : ℝ) < 2 * lam * ‖z - x‖ ^ 2) : 0 < Δ (radialSubBarrier x ρ lam A) z := by
  rw [laplacian_radialSubBarrier]
  have := Real.exp_pos (-(lam * ‖z - x‖ ^ 2))
  have : 0 < 2 * lam * ‖z - x‖ ^ 2 - d := by linarith
  positivity

/-- **Gradient of the barrier:** `|∇| = 2 |A| λ |z - x| exp (-λ |z - x|²)` for `λ ≥ 0`. -/
theorem norm_gradient_radialSubBarrier (hlam : 0 ≤ lam) (z : E d) :
    ‖∇ (radialSubBarrier x ρ lam A) z‖ =
      2 * |A| * lam * ‖z - x‖ * Real.exp (-(lam * ‖z - x‖ ^ 2)) := by
  have hcomp : HasFDerivAt (fun y ↦ radialSubProfile ρ lam A (‖y - x‖ ^ 2))
      ((-(A * lam * Real.exp (-(lam * ‖z - x‖ ^ 2)))) • ((2 : ℝ) • innerSL ℝ (z - x))) z :=
    (hasDerivAt_radialSubProfile (‖z - x‖ ^ 2)).comp_hasFDerivAt
      (f := fun y : E d ↦ ‖y - x‖ ^ 2) z (hasFDerivAt_normSq_sub_const x z)
  change ‖∇ (fun y ↦ radialSubProfile ρ lam A (‖y - x‖ ^ 2)) z‖ = _
  rw [show ‖∇ (fun y ↦ radialSubProfile ρ lam A (‖y - x‖ ^ 2)) z‖ =
      ‖fderiv ℝ (fun y ↦ radialSubProfile ρ lam A (‖y - x‖ ^ 2)) z‖ by simp [gradient],
    hcomp.fderiv, norm_smul, norm_smul, innerSL_apply_norm, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_neg, abs_mul, abs_mul, abs_of_nonneg hlam, abs_of_pos (Real.exp_pos _)]
  norm_num
  ring

end EllipticBernoulli
