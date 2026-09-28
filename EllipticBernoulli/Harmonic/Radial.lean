/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Harmonic.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Radial barriers

On `E d`, for a centre `z` and an exponent `γ`:

* `radialPow z γ y = ‖y - z‖ ^ (-γ)` (`Real.rpow`). Away from `z` it is `C^∞`
  (`contDiffOn_radialPow`), with
  - `∇ radialPow = -γ ‖y - z‖^{-γ-2} (y - z)` (`gradient_radialPow`),
    `‖∇ radialPow‖ = γ ‖y - z‖^{-γ-1}` for `γ ≥ 0` (`norm_gradient_radialPow`);
  - `Δ radialPow = γ (γ + 2 - d) ‖y - z‖^{-γ-2}` (`laplacian_radialPow`), so it is strictly
    subharmonic for `0 < γ`, `d - 2 < γ` (`laplacian_radialPow_pos`).
* `radialPowSmooth z γ ε = radialProfile γ ε (‖· - z‖²)`: a **globally** `C^∞` function
  (`contDiff_radialPowSmooth`) which equals `radialPow z γ` on `{ε ≤ ‖y - z‖}`
  (`radialPowSmooth_eqOn`) and near every point with `ε < ‖y - z‖`
  (`radialPowSmooth_eventuallyEq`). The profile is
  `radialProfile γ ε t = smoothTransition ((t - ε²/2) / (ε²/2)) * t ^ (-γ/2)`. It is usable as
  a test function in the viscosity definitions, whose test functions are globally `C^∞`.
* `annulusBarrier z ρ₁ ρ₂ γ = (‖· - z‖^{-γ} - ρ₂^{-γ}) / (ρ₁^{-γ} - ρ₂^{-γ})`: equal to `1` on
  `sphere z ρ₁` and `0` on `sphere z ρ₂`, strictly subharmonic for `d - 2 < γ`, with gradient
  norm `γ ρ₂^{-γ-1} / (ρ₁^{-γ} - ρ₂^{-γ})` on `sphere z ρ₂`. `annulusBarrierSmooth` is its
  globally smooth version.

Used for the Lipschitz estimate, exterior-ball non-degeneracy and the barriers of the flat
Harnack inequality.

## Proof

The Laplacian is computed from the radial formula
`Δ ρ(‖·‖²) = 4 ‖x‖² ρ''(‖x‖²) + 2 d ρ'(‖x‖²)` (`ContDiff.laplacian_comp_norm_sq`,
`viscosity_solns`) applied to the smooth profile, and transferred to `radialPow` by locality of
the Laplacian.
-/

open InnerProductSpace Metric Module Set Filter Topology
open scoped ContDiff Laplacian Gradient

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### The smooth profile -/

/-- The smooth radial profile: `smoothTransition ((t - ε²/2) / (ε²/2)) * t ^ (-γ/2)`. It is
`C^∞` on `ℝ` for `ε > 0`, vanishes for `t ≤ ε²/2` and equals `t ^ (-γ/2)` for `t ≥ ε²`. -/
def radialProfile (γ ε : ℝ) (t : ℝ) : ℝ :=
  Real.smoothTransition ((t - ε ^ 2 / 2) / (ε ^ 2 / 2)) * t ^ (-γ / 2)

/-- `‖y - z‖ ^ (-γ)`. -/
def radialPow (z : E d) (γ : ℝ) : E d → ℝ := fun y ↦ ‖y - z‖ ^ (-γ)

/-- A globally smooth version of `radialPow z γ`, equal to it on `{ε ≤ ‖y - z‖}`. -/
def radialPowSmooth (z : E d) (γ ε : ℝ) : E d → ℝ := fun y ↦ radialProfile γ ε (‖y - z‖ ^ 2)

/-- The normalized annulus barrier `(‖y - z‖^{-γ} - ρ₂^{-γ}) / (ρ₁^{-γ} - ρ₂^{-γ})`. -/
def annulusBarrier (z : E d) (ρ₁ ρ₂ γ : ℝ) : E d → ℝ :=
  fun y ↦ (‖y - z‖ ^ (-γ) - ρ₂ ^ (-γ)) / (ρ₁ ^ (-γ) - ρ₂ ^ (-γ))

/-- The globally smooth annulus barrier, equal to `annulusBarrier` on `{ε ≤ ‖y - z‖}`. -/
def annulusBarrierSmooth (z : E d) (ρ₁ ρ₂ γ ε : ℝ) : E d → ℝ :=
  fun y ↦ (radialPowSmooth z γ ε y - ρ₂ ^ (-γ)) / (ρ₁ ^ (-γ) - ρ₂ ^ (-γ))

end EllipticBernoulli

end

public section

namespace EllipticBernoulli

variable {d : ℕ}

theorem radialProfile_eq {γ ε t : ℝ} (hε : 0 < ε) (ht : ε ^ 2 ≤ t) :
    radialProfile γ ε t = t ^ (-γ / 2) := by
  rw [radialProfile, Real.smoothTransition.one_of_one_le, one_mul]
  rw [le_div_iff₀ (by positivity)]
  linarith

theorem contDiff_radialProfile (γ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (radialProfile γ ε) := by
  refine contDiff_iff_contDiffAt.2 fun t ↦ ?_
  rcases lt_or_ge 0 t with ht | ht
  · exact ((Real.smoothTransition.contDiff.comp (by fun_prop)).contDiffAt).mul
      (Real.contDiffAt_rpow_const_of_ne ht.ne')
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    have hε2 : 0 < ε ^ 2 / 2 := by positivity
    filter_upwards [Iio_mem_nhds (show t < ε ^ 2 / 2 by linarith)] with s hs
    rw [radialProfile, Real.smoothTransition.zero_of_nonpos, zero_mul]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [mem_Iio.1 hs]) hε2.le

theorem radialProfile_eventuallyEq {γ ε t : ℝ} (hε : 0 < ε) (ht : ε ^ 2 < t) :
    radialProfile γ ε =ᶠ[𝓝 t] fun s ↦ s ^ (-γ / 2) := by
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact radialProfile_eq hε (le_of_lt hs)

private theorem deriv_rpow_eq (p : ℝ) : deriv (fun s : ℝ ↦ s ^ p) = fun s ↦ p * s ^ (p - 1) :=
  funext fun s ↦ Real.deriv_rpow_const s p

theorem deriv_radialProfile {γ ε t : ℝ} (hε : 0 < ε) (ht : ε ^ 2 < t) :
    deriv (radialProfile γ ε) t = (-γ / 2) * t ^ (-γ / 2 - 1) := by
  rw [(radialProfile_eventuallyEq hε ht).deriv_eq, Real.deriv_rpow_const]

theorem deriv_deriv_radialProfile {γ ε t : ℝ} (hε : 0 < ε) (ht : ε ^ 2 < t) :
    deriv (deriv (radialProfile γ ε)) t =
      (-γ / 2) * ((-γ / 2 - 1) * t ^ (-γ / 2 - 1 - 1)) := by
  have ht0 : t ≠ 0 := by
    have : 0 < ε ^ 2 := by positivity
    exact (this.trans ht).ne'
  rw [(radialProfile_eventuallyEq hε ht).deriv.deriv_eq, deriv_rpow_eq,
    deriv_const_mul _ (Real.differentiableAt_rpow_const_of_ne _ ht0), Real.deriv_rpow_const]

private theorem sq_rpow {s : ℝ} (hs : 0 ≤ s) (q : ℝ) : (s ^ 2) ^ q = s ^ (2 * q) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
  norm_num

theorem radialPowSmooth_eqOn (z : E d) (γ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    EqOn (radialPowSmooth z γ ε) (radialPow z γ) {y | ε ≤ ‖y - z‖} := by
  intro y hy
  simp only [radialPowSmooth, radialPow]
  rw [radialProfile_eq hε (pow_le_pow_left₀ hε.le hy 2), sq_rpow (norm_nonneg _)]
  ring_nf

theorem radialPowSmooth_eventuallyEq {z y : E d} {γ ε : ℝ} (hε : 0 < ε) (hy : ε < ‖y - z‖) :
    radialPowSmooth z γ ε =ᶠ[𝓝 y] radialPow z γ := by
  have ho : IsOpen {w : E d | ε < ‖w - z‖} := isOpen_lt continuous_const (by fun_prop)
  filter_upwards [ho.mem_nhds hy] with w hw
  exact radialPowSmooth_eqOn z γ hε (le_of_lt hw)

theorem contDiff_radialPowSmooth (z : E d) (γ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (radialPowSmooth z γ ε) :=
  (contDiff_radialProfile γ hε).comp ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))

theorem laplacian_radialPowSmooth {z y : E d} {γ ε : ℝ} (hε : 0 < ε) (hy : ε < ‖y - z‖) :
    Δ (radialPowSmooth z γ ε) y = γ * (γ + 2 - d) * ‖y - z‖ ^ (-γ - 2) := by
  have h1 := congrFun (ViscositySolns.Analysis.laplacian_comp_add_right
    (fun w : E d ↦ radialProfile γ ε (‖w‖ ^ 2)) (-z)) y
  simp only [← sub_eq_add_neg] at h1
  have h3 := ContDiff.laplacian_comp_norm_sq (E := E d)
    ((contDiff_radialProfile γ hε).of_le (by norm_cast)) (y - z)
  have hs : 0 < ‖y - z‖ := hε.trans hy
  have ht : ε ^ 2 < ‖y - z‖ ^ 2 := pow_lt_pow_left₀ hy hε.le two_ne_zero
  rw [deriv_radialProfile hε ht, deriv_deriv_radialProfile hε ht, finrank_euclideanSpace_fin,
    sq_rpow hs.le, sq_rpow hs.le] at h3
  change Δ (fun w ↦ radialProfile γ ε (‖w - z‖ ^ 2)) y = _
  rw [h1, h3]
  set s := ‖y - z‖
  have e1 : s ^ (2 * (-γ / 2 - 1)) = s ^ (-γ - 2) := by ring_nf
  have e2 : s ^ (-γ - 2) = s ^ (2 * (-γ / 2 - 1 - 1)) * s ^ 2 := by
    rw [← Real.rpow_natCast s 2, ← Real.rpow_add hs]; ring_nf
  rw [e1, e2]
  ring

theorem hasGradientAt_radialPowSmooth {z y : E d} {γ ε : ℝ} (hε : 0 < ε) (hy : ε < ‖y - z‖) :
    HasGradientAt (radialPowSmooth z γ ε) ((-γ * ‖y - z‖ ^ (-γ - 2)) • (y - z)) y := by
  have hs : 0 < ‖y - z‖ := hε.trans hy
  have ht : ε ^ 2 < ‖y - z‖ ^ 2 := pow_lt_pow_left₀ hy hε.le two_ne_zero
  have hf : HasFDerivAt (fun w : E d ↦ ‖w - z‖ ^ 2)
      (2 • (innerSL ℝ (y - z)).comp (ContinuousLinearMap.id ℝ (E d))) y :=
    ((hasFDerivAt_id y).sub_const z).norm_sq
  have hρ : HasDerivAt (radialProfile γ ε) (deriv (radialProfile γ ε) (‖y - z‖ ^ 2))
      (‖y - z‖ ^ 2) :=
    ((contDiff_radialProfile γ hε).differentiable (by simp) _).hasDerivAt
  have h := hρ.comp_hasFDerivAt y hf
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext w
  rw [deriv_radialProfile hε ht, sq_rpow hs.le]
  simp only [toDual_apply_apply, real_inner_smul_left, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.coe_id', id_eq,
    innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  have e1 : ‖y - z‖ ^ (2 * (-γ / 2 - 1)) = ‖y - z‖ ^ (-γ - 2) := by ring_nf
  rw [e1]
  ring

theorem gradient_radialPowSmooth {z y : E d} {γ ε : ℝ} (hε : 0 < ε) (hy : ε < ‖y - z‖) :
    ∇ (radialPowSmooth z γ ε) y = (-γ * ‖y - z‖ ^ (-γ - 2)) • (y - z) :=
  (hasGradientAt_radialPowSmooth hε hy).gradient

/-! ### `radialPow` -/

private theorem half_lt_norm {z y : E d} (hy : y ≠ z) : ‖y - z‖ / 2 < ‖y - z‖ :=
  half_lt_self (norm_pos_iff.2 (sub_ne_zero.2 hy))

private theorem half_pos_norm {z y : E d} (hy : y ≠ z) : 0 < ‖y - z‖ / 2 :=
  half_pos (norm_pos_iff.2 (sub_ne_zero.2 hy))

/-- `radialPow z γ` is `C^∞` away from `z`. -/
theorem contDiffOn_radialPow (z : E d) (γ : ℝ) :
    ContDiffOn ℝ ∞ (radialPow z γ) {y | y ≠ z} := fun _ hy ↦
  ((contDiff_radialPowSmooth z γ (half_pos_norm hy)).contDiffAt.congr_of_eventuallyEq
    (radialPowSmooth_eventuallyEq (half_pos_norm hy) (half_lt_norm hy)).symm).contDiffWithinAt

theorem hasGradientAt_radialPow {z y : E d} (hy : y ≠ z) (γ : ℝ) :
    HasGradientAt (radialPow z γ) ((-γ * ‖y - z‖ ^ (-γ - 2)) • (y - z)) y :=
  (hasGradientAt_radialPowSmooth (half_pos_norm hy) (half_lt_norm hy)).congr_of_eventuallyEq
    (radialPowSmooth_eventuallyEq (half_pos_norm hy) (half_lt_norm hy)).symm

/-- `∇ ‖· - z‖^{-γ} = -γ ‖y - z‖^{-γ-2} (y - z)`. -/
theorem gradient_radialPow {z y : E d} (hy : y ≠ z) (γ : ℝ) :
    ∇ (radialPow z γ) y = (-γ * ‖y - z‖ ^ (-γ - 2)) • (y - z) :=
  (hasGradientAt_radialPow hy γ).gradient

/-- `‖∇ ‖· - z‖^{-γ}‖ = γ ‖y - z‖^{-γ-1}` for `γ ≥ 0`. -/
theorem norm_gradient_radialPow {z y : E d} (hy : y ≠ z) (γ : ℝ) (hγ : 0 ≤ γ) :
    ‖∇ (radialPow z γ) y‖ = γ * ‖y - z‖ ^ (-γ - 1) := by
  have hs : 0 < ‖y - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  rw [gradient_radialPow hy, norm_smul, Real.norm_eq_abs, abs_mul, abs_neg,
    abs_of_nonneg hγ, abs_of_pos (Real.rpow_pos_of_pos hs _), mul_assoc,
    ← Real.rpow_add_one hs.ne']
  ring_nf

/-- `Δ ‖· - z‖^{-γ} = γ (γ + 2 - d) ‖y - z‖^{-γ-2}` away from `z`. -/
theorem laplacian_radialPow {z y : E d} (hy : y ≠ z) (γ : ℝ) :
    Δ (radialPow z γ) y = γ * (γ + 2 - d) * ‖y - z‖ ^ (-γ - 2) := by
  rw [← (laplacian_congr_nhds
    (radialPowSmooth_eventuallyEq (γ := γ) (half_pos_norm hy) (half_lt_norm hy))).eq_of_nhds]
  exact laplacian_radialPowSmooth (half_pos_norm hy) (half_lt_norm hy)

/-- `‖· - z‖^{-γ}` is strictly subharmonic away from `z` when `0 < γ` and `d - 2 < γ`. -/
theorem laplacian_radialPow_pos {z y : E d} (hy : y ≠ z) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ : (d : ℝ) - 2 < γ) : 0 < Δ (radialPow z γ) y := by
  rw [laplacian_radialPow hy]
  have hs : 0 < ‖y - z‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  have : 0 < γ + 2 - d := by linarith
  positivity

/-! ### Annulus barriers -/

private theorem hasGradientAt_affine {f : E d → ℝ} {g y : E d} (hf : HasGradientAt f g y)
    (c D : ℝ) : HasGradientAt (fun w ↦ (f w - c) / D) (D⁻¹ • g) y := by
  rw [hasGradientAt_iff_hasFDerivAt] at hf ⊢
  have h := (hf.sub_const c).const_mul D⁻¹
  convert h using 1
  · funext w; rw [div_eq_inv_mul]
  · ext w; simp

private theorem laplacian_affine {f : E d → ℝ} {y : E d} (hf : ContDiffAt ℝ 2 f y) (c D : ℝ) :
    Δ (fun w ↦ (f w - c) / D) y = Δ f y / D := by
  have e : (fun w ↦ (f w - c) / D) = D⁻¹ • (f - fun _ ↦ c) := by
    funext w; simp [div_eq_inv_mul]
  have hfc : ContDiffAt ℝ 2 (f - fun _ ↦ c) y := hf.sub contDiffAt_const
  rw [e, laplacian_smul _ hfc, hf.laplacian_sub contDiffAt_const, laplacian_const]
  simp [div_eq_inv_mul]

/-- The normalizing denominator `ρ₁^{-γ} - ρ₂^{-γ}` is positive. -/
theorem annulusBarrier_denom_pos {ρ₁ ρ₂ γ : ℝ} (hρ₁ : 0 < ρ₁) (hρ : ρ₁ < ρ₂) (hγ : 0 < γ) :
    0 < ρ₁ ^ (-γ) - ρ₂ ^ (-γ) :=
  sub_pos.2 (Real.rpow_lt_rpow_of_neg hρ₁ hρ (neg_neg_of_pos hγ))

theorem annulusBarrier_eq_one {z : E d} {ρ₁ ρ₂ γ : ℝ} (hρ₁ : 0 < ρ₁) (hρ : ρ₁ < ρ₂)
    (hγ : 0 < γ) : ∀ y ∈ sphere z ρ₁, annulusBarrier z ρ₁ ρ₂ γ y = 1 := by
  intro y hy
  rw [mem_sphere, dist_eq_norm] at hy
  simp only [annulusBarrier, hy]
  exact div_self (annulusBarrier_denom_pos hρ₁ hρ hγ).ne'

theorem annulusBarrier_eq_zero {z : E d} {ρ₁ ρ₂ γ : ℝ} :
    ∀ y ∈ sphere z ρ₂, annulusBarrier z ρ₁ ρ₂ γ y = 0 := by
  intro y hy
  rw [mem_sphere, dist_eq_norm] at hy
  simp [annulusBarrier, hy]

theorem contDiffOn_annulusBarrier (z : E d) (ρ₁ ρ₂ γ : ℝ) :
    ContDiffOn ℝ ∞ (annulusBarrier z ρ₁ ρ₂ γ) {y | y ≠ z} :=
  ((contDiffOn_radialPow z γ).sub contDiffOn_const).div_const _

/-- `Δ annulusBarrier = Δ radialPow / (ρ₁^{-γ} - ρ₂^{-γ})` away from `z`. -/
theorem laplacian_annulusBarrier {z y : E d} (hy : y ≠ z) (ρ₁ ρ₂ γ : ℝ) :
    Δ (annulusBarrier z ρ₁ ρ₂ γ) y =
      γ * (γ + 2 - d) * ‖y - z‖ ^ (-γ - 2) / (ρ₁ ^ (-γ) - ρ₂ ^ (-γ)) := by
  have hc : ContDiffAt ℝ 2 (radialPow z γ) y :=
    ((contDiffOn_radialPow z γ).contDiffAt ((isOpen_ne).mem_nhds hy)).of_le (by norm_cast)
  rw [← laplacian_radialPow hy]
  exact laplacian_affine hc _ _

/-- The annulus barrier is strictly subharmonic away from `z` when `0 < γ`, `d - 2 < γ`. -/
theorem laplacian_annulusBarrier_pos {z y : E d} (hy : y ≠ z) {ρ₁ ρ₂ γ : ℝ} (hρ₁ : 0 < ρ₁)
    (hρ : ρ₁ < ρ₂) (hγ0 : 0 < γ) (hγ : (d : ℝ) - 2 < γ) :
    0 < Δ (annulusBarrier z ρ₁ ρ₂ γ) y := by
  have hc : ContDiffAt ℝ 2 (radialPow z γ) y :=
    ((contDiffOn_radialPow z γ).contDiffAt ((isOpen_ne).mem_nhds hy)).of_le (by norm_cast)
  change 0 < Δ (fun w ↦ (radialPow z γ w - ρ₂ ^ (-γ)) / (ρ₁ ^ (-γ) - ρ₂ ^ (-γ))) y
  rw [laplacian_affine hc]
  exact div_pos (laplacian_radialPow_pos hy hγ0 hγ) (annulusBarrier_denom_pos hρ₁ hρ hγ0)

theorem gradient_annulusBarrier {z y : E d} (hy : y ≠ z) (ρ₁ ρ₂ γ : ℝ) :
    ∇ (annulusBarrier z ρ₁ ρ₂ γ) y =
      (ρ₁ ^ (-γ) - ρ₂ ^ (-γ))⁻¹ • ((-γ * ‖y - z‖ ^ (-γ - 2)) • (y - z)) :=
  (hasGradientAt_affine (hasGradientAt_radialPow hy γ) _ _).gradient

/-- On the outer sphere, `‖∇ annulusBarrier‖ = γ ρ₂^{-γ-1} / (ρ₁^{-γ} - ρ₂^{-γ})`. -/
theorem norm_gradient_annulusBarrier_of_mem_sphere {z y : E d} {ρ₁ ρ₂ γ : ℝ} (hρ₁ : 0 < ρ₁)
    (hρ : ρ₁ < ρ₂) (hγ : 0 < γ) (hy : y ∈ sphere z ρ₂) :
    ‖∇ (annulusBarrier z ρ₁ ρ₂ γ) y‖ = γ * ρ₂ ^ (-γ - 1) / (ρ₁ ^ (-γ) - ρ₂ ^ (-γ)) := by
  have hρ₂ : 0 < ρ₂ := hρ₁.trans hρ
  have hyz : y ≠ z := ne_of_mem_sphere hy hρ₂.ne'
  have hD := annulusBarrier_denom_pos hρ₁ hρ hγ
  rw [gradient_annulusBarrier hyz, norm_smul, ← gradient_radialPow hyz,
    norm_gradient_radialPow hyz γ hγ.le, Real.norm_eq_abs, abs_inv, abs_of_pos hD]
  rw [mem_sphere, dist_eq_norm] at hy
  rw [hy, inv_mul_eq_div]

/-! ### The globally smooth annulus barrier -/

theorem contDiff_annulusBarrierSmooth (z : E d) (ρ₁ ρ₂ γ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (annulusBarrierSmooth z ρ₁ ρ₂ γ ε) :=
  ((contDiff_radialPowSmooth z γ hε).sub contDiff_const).div_const _

theorem annulusBarrierSmooth_eqOn (z : E d) (ρ₁ ρ₂ γ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    EqOn (annulusBarrierSmooth z ρ₁ ρ₂ γ ε) (annulusBarrier z ρ₁ ρ₂ γ) {y | ε ≤ ‖y - z‖} := by
  intro y hy
  simp only [annulusBarrierSmooth, annulusBarrier, radialPowSmooth_eqOn z γ hε hy, radialPow]

theorem annulusBarrierSmooth_eventuallyEq {z y : E d} {ρ₁ ρ₂ γ ε : ℝ} (hε : 0 < ε)
    (hy : ε < ‖y - z‖) : annulusBarrierSmooth z ρ₁ ρ₂ γ ε =ᶠ[𝓝 y] annulusBarrier z ρ₁ ρ₂ γ := by
  have ho : IsOpen {w : E d | ε < ‖w - z‖} := isOpen_lt continuous_const (by fun_prop)
  filter_upwards [ho.mem_nhds hy] with w hw
  exact annulusBarrierSmooth_eqOn z ρ₁ ρ₂ γ hε (le_of_lt hw)

theorem laplacian_annulusBarrierSmooth {z y : E d} {ρ₁ ρ₂ γ ε : ℝ} (hε : 0 < ε)
    (hy : ε < ‖y - z‖) :
    Δ (annulusBarrierSmooth z ρ₁ ρ₂ γ ε) y =
      γ * (γ + 2 - d) * ‖y - z‖ ^ (-γ - 2) / (ρ₁ ^ (-γ) - ρ₂ ^ (-γ)) := by
  have hyz : y ≠ z := fun h ↦ by simp [h] at hy; linarith
  rw [(laplacian_congr_nhds (annulusBarrierSmooth_eventuallyEq hε hy)).eq_of_nhds,
    laplacian_annulusBarrier hyz]

theorem gradient_annulusBarrierSmooth {z y : E d} {ρ₁ ρ₂ γ ε : ℝ} (hε : 0 < ε)
    (hy : ε < ‖y - z‖) :
    ∇ (annulusBarrierSmooth z ρ₁ ρ₂ γ ε) y =
      (ρ₁ ^ (-γ) - ρ₂ ^ (-γ))⁻¹ • ((-γ * ‖y - z‖ ^ (-γ - 2)) • (y - z)) := by
  have hyz : y ≠ z := fun h ↦ by simp [h] at hy; linarith
  exact ((hasGradientAt_affine (hasGradientAt_radialPow hyz γ) _ _).congr_of_eventuallyEq
    (annulusBarrierSmooth_eventuallyEq hε hy)).gradient

end EllipticBernoulli
