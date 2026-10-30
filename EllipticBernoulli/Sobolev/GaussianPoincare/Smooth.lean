/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sobolev.GaussianPoincare.Weight
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import EllipticBernoulli.Sobolev.Lipschitz
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Gaussian Poincaré inequality for `C¹` functions: the defect identity

Write `γ` for the Gaussian `e^{-|x|²/2} dx / Z` on `ℝᵈ`, `Z = gaussMass d`. For `F : ℝᵈ → ℝ` put

* `gaussVariance F = Z ∫ F² e^{-|x|²/2} - (∫ F e^{-|x|²/2})²`, which is `Z² Var_γ F`;
* `gaussDefect F t = ∫∫ |∇F(x) - ∇F(x cos t + y sin t)|² e^{-(|x|²+|y|²)/2} dx dy`.

`gaussVariance_add_integral_sin_mul_gaussDefect` (the defect identity): for `F` of class `C¹` and
Lipschitz,
`gaussVariance F + ½ ∫₀^{π/2} sin t · gaussDefect F t dt = Z ∫ |∇F|² e^{-|x|²/2}`.

## Proof

Rotation interpolation between `x` and an independent copy `y`: with `Z_t = x cos t + y sin t`
and `W_t = -x sin t + y cos t = ∂ₜ Z_t`,

1. `gaussVariance F = ∫∫ F(x)(F(x) - F(y))` and `F(y) - F(x) = ∫₀^{π/2} DF(Z_t) W_t dt`
   (fundamental theorem of calculus), then Fubini in `(t, x, y)`;
2. for fixed `t` and a unit vector `e`, integrate by parts on `ℝᵈ × ℝᵈ` along the direction
   `v = (e sin t, -e cos t)`: the derivative of the weight along `v` is `⟨W_t, e⟩` times the
   weight, and `Z_t` is constant along `v`, so
   `∫∫ F(x) ∂ₑF(Z_t) ⟨W_t, e⟩ = -sin t ∫∫ ∂ₑF(x) ∂ₑF(Z_t)`; sum over an orthonormal basis;
3. expand `|∇F(x) - ∇F(Z_t)|²` and use rotation invariance (`Z_t ∼ γ`).

Integrating by parts along `v` in the original variables avoids a change of variables by the
rotation `(x, y) ↦ (Z_t, W_t)` of `ℝᵈ × ℝᵈ`, because `Z_t` is constant along `v`.
-/

open Set Filter Topology MeasureTheory Real InnerProductSpace
open scoped Gradient NNReal

namespace EllipticBernoulli

variable {d : ℕ}

@[expose] public noncomputable section

/-- `Z² Var_γ F = Z ∫ F² e^{-|x|²/2} - (∫ F e^{-|x|²/2})²`, with `Z = gaussMass d`. -/
def gaussVariance (F : E d → ℝ) : ℝ :=
  gaussMass d * (∫ x, F x ^ 2 * gaussWeight x) - (∫ x, F x * gaussWeight x) ^ 2

/-- The defect `∫∫ |∇F(x) - ∇F(x cos t + y sin t)|² e^{-(|x|²+|y|²)/2} dx dy` of the Gaussian
Poincaré inequality at angle `t`. -/
def gaussDefect (F : E d → ℝ) (t : ℝ) : ℝ :=
  ∫ p : E d × E d, ‖∇ F p.1 - ∇ F (cos t • p.1 + sin t • p.2)‖ ^ 2 * gaussPairWeight p

end

/-! ### Growth bounds -/

/-- The quadratic growth weight `(1 + |x|²)(1 + |y|²)` on `ℝᵈ × ℝᵈ`. -/
private noncomputable def pairGrowth (p : E d × E d) : ℝ := (1 + ‖p.1‖ ^ 2) * (1 + ‖p.2‖ ^ 2)

private theorem pairGrowth_bounds (p : E d × E d) :
    1 ≤ pairGrowth p ∧ ‖p.1‖ ≤ pairGrowth p ∧ ‖p.2‖ ≤ pairGrowth p ∧
      ‖p.1‖ ^ 2 ≤ pairGrowth p ∧ ‖p.1‖ * ‖p.2‖ ≤ pairGrowth p := by
  have a := norm_nonneg p.1
  have b := norm_nonneg p.2
  have ha : ‖p.1‖ ≤ 1 + ‖p.1‖ ^ 2 := by nlinarith [sq_nonneg (‖p.1‖ - 1)]
  have hb : ‖p.2‖ ≤ 1 + ‖p.2‖ ^ 2 := by nlinarith [sq_nonneg (‖p.2‖ - 1)]
  have h1 : 1 ≤ 1 + ‖p.1‖ ^ 2 := by nlinarith
  have h2 : 1 ≤ 1 + ‖p.2‖ ^ 2 := by nlinarith
  simp only [pairGrowth]
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, ?_⟩
  exact mul_le_mul ha hb b (by positivity)

/-- `F` of linear growth: `|F x| ≤ |F 0| + L |x|`. -/
private theorem abs_le_of_lipschitzWith {F : E d → ℝ} {L : ℝ≥0} (hL : LipschitzWith L F)
    (x : E d) : |F x| ≤ |F 0| + L * ‖x‖ := by
  have := hL.dist_le_mul x 0
  rw [Real.dist_eq, dist_zero_right] at this
  have := abs_sub_abs_le_abs_sub (F x) (F 0)
  linarith

private theorem norm_fderiv_le_of_lipschitzWith {F : E d → ℝ} {L : ℝ≥0}
    (hL : LipschitzWith L F) (x : E d) : ‖fderiv ℝ F x‖ ≤ L :=
  norm_fderiv_le_of_lipschitz ℝ hL

private theorem abs_fderiv_apply_le {F : E d → ℝ} {L : ℝ≥0} (hL : LipschitzWith L F)
    (x v : E d) : |fderiv ℝ F x v| ≤ L * ‖v‖ := by
  rw [← Real.norm_eq_abs]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitzWith hL x) (norm_nonneg _))

/-- `|W_t| ≤ |x| + |y|`. -/
private theorem norm_rot_le (t : ℝ) (x y : E d) : ‖-sin t • x + cos t • y‖ ≤ ‖x‖ + ‖y‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs]
  have := abs_sin_le_one t
  have := abs_cos_le_one t
  have := norm_nonneg x
  have := norm_nonneg y
  nlinarith [abs_nonneg (sin t), abs_nonneg (cos t)]

/-! ### Step 1: the variance as a double integral and the rotation interpolation -/

section Smooth

variable {F : E d → ℝ} {L : ℝ≥0}

private theorem integrable_sq_mul_gaussWeight (hL : LipschitzWith L F) :
    Integrable (fun x ↦ F x ^ 2 * gaussWeight x) := by
  refine integrable_mul_gaussWeight (hL.continuous.pow 2).aestronglyMeasurable
    (C := 2 * (|F 0| ^ 2 + (L : ℝ) ^ 2)) fun x ↦ ?_
  have h := abs_le_of_lipschitzWith hL x
  rw [abs_pow]
  have h0 := abs_nonneg (F x)
  have h2 : |F x| ^ 2 ≤ (|F 0| + L * ‖x‖) ^ 2 := pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (|F 0| - L * ‖x‖), sq_nonneg ‖x‖, abs_nonneg (F 0)]

private theorem integrable_mul_gaussWeight_of_lipschitzWith (hL : LipschitzWith L F) :
    Integrable (fun x ↦ F x * gaussWeight x) := by
  refine integrable_mul_gaussWeight hL.continuous.aestronglyMeasurable
    (C := |F 0| + L) fun x ↦ ?_
  have h := abs_le_of_lipschitzWith hL x
  have hx : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
  have h1 := mul_nonneg (abs_nonneg (F 0)) (sq_nonneg ‖x‖)
  have h2 := mul_le_mul_of_nonneg_left hx (NNReal.coe_nonneg L)
  calc |F x| ≤ |F 0| + L * ‖x‖ := h
    _ ≤ (|F 0| + L) * (1 + ‖x‖ ^ 2) := by nlinarith

/-- `gaussVariance F = ∫∫ F(x) (F(x) - F(y)) e^{-(|x|²+|y|²)/2}`. -/
public theorem gaussVariance_eq_integral (hL : LipschitzWith L F) :
    gaussVariance F = ∫ p : E d × E d, F p.1 * (F p.1 - F p.2) * gaussPairWeight p := by
  have h1 : ∫ p : E d × E d, F p.1 ^ 2 * gaussWeight p.1 * gaussWeight p.2 =
      (∫ x, F x ^ 2 * gaussWeight x) * gaussMass d := by
    rw [Measure.volume_eq_prod, gaussMass]
    exact integral_prod_mul (fun x ↦ F x ^ 2 * gaussWeight x) gaussWeight
  have h2 : ∫ p : E d × E d, F p.1 * gaussWeight p.1 * (F p.2 * gaussWeight p.2) =
      (∫ x, F x * gaussWeight x) * ∫ x, F x * gaussWeight x := by
    rw [Measure.volume_eq_prod]
    exact integral_prod_mul (fun x ↦ F x * gaussWeight x) (fun x ↦ F x * gaussWeight x)
  have hi1 : Integrable fun p : E d × E d ↦ F p.1 ^ 2 * gaussWeight p.1 * gaussWeight p.2 := by
    rw [Measure.volume_eq_prod]
    exact (integrable_sq_mul_gaussWeight hL).mul_prod integrable_gaussWeight
  have hi2 : Integrable fun p : E d × E d ↦
      F p.1 * gaussWeight p.1 * (F p.2 * gaussWeight p.2) := by
    rw [Measure.volume_eq_prod]
    exact (integrable_mul_gaussWeight_of_lipschitzWith hL).mul_prod
      (integrable_mul_gaussWeight_of_lipschitzWith hL)
  have : (fun p : E d × E d ↦ F p.1 * (F p.1 - F p.2) * gaussPairWeight p) =
      fun p ↦ F p.1 ^ 2 * gaussWeight p.1 * gaussWeight p.2 -
        F p.1 * gaussWeight p.1 * (F p.2 * gaussWeight p.2) := by
    funext p; simp only [gaussPairWeight]; ring
  rw [this, integral_sub hi1 hi2, h1, h2, gaussVariance, mul_comm _ (gaussMass d), sq]

/-- Fundamental theorem of calculus along the rotation:
`F(y) - F(x) = ∫₀^{π/2} DF(x cos t + y sin t)(-x sin t + y cos t) dt`. -/
public theorem sub_eq_integral_fderiv_rot (hF : ContDiff ℝ 1 F) (x y : E d) :
    F y - F x = ∫ t in (0 : ℝ)..(π / 2),
      fderiv ℝ F (cos t • x + sin t • y) (-sin t • x + cos t • y) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ ↦ F (cos t • x + sin t • y))
      (fderiv ℝ F (cos t • x + sin t • y) (-sin t • x + cos t • y)) t := fun t ↦ by
    have hz : HasDerivAt (fun t : ℝ ↦ cos t • x + sin t • y) (-sin t • x + cos t • y) t :=
      ((hasDerivAt_cos t).smul_const x).add ((hasDerivAt_sin t).smul_const y)
    exact ((hF.differentiable one_ne_zero _).hasFDerivAt).comp_hasDerivAt t hz
  have hc : Continuous fun t : ℝ ↦
      fderiv ℝ F (cos t • x + sin t • y) (-sin t • x + cos t • y) :=
    ((hF.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply (by fun_prop)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t) (hc.intervalIntegrable _ _)]
  simp

/-! ### Step 2: integration by parts along `(e sin t, -e cos t)` -/

private theorem continuous_fderiv_apply_rot (hF : ContDiff ℝ 1 F) (t : ℝ) (e : E d) :
    Continuous fun p : E d × E d ↦ fderiv ℝ F (cos t • p.1 + sin t • p.2) e :=
  ((hF.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply continuous_const

private theorem continuous_fderiv_apply_fst (hF : ContDiff ℝ 1 F) (e : E d) :
    Continuous fun p : E d × E d ↦ fderiv ℝ F p.1 e :=
  ((hF.continuous_fderiv one_ne_zero).comp continuous_fst).clm_apply continuous_const

private theorem abs_fst_le (hL : LipschitzWith L F) (p : E d × E d) :
    |F p.1| ≤ (|F 0| + L) * pairGrowth p := by
  obtain ⟨h1, h2, -, -, -⟩ := pairGrowth_bounds p
  have h := abs_le_of_lipschitzWith hL p.1
  have hL0 := NNReal.coe_nonneg L
  have ha := abs_nonneg (F 0)
  nlinarith

private theorem abs_fst_mul_rot_le (hL : LipschitzWith L F) (t : ℝ) (p : E d × E d) :
    |F p.1| * ‖-sin t • p.1 + cos t • p.2‖ ≤ (2 * (|F 0| + L)) * pairGrowth p := by
  obtain ⟨-, h2, h3, h4, h5⟩ := pairGrowth_bounds p
  have h := abs_le_of_lipschitzWith hL p.1
  have hW := norm_rot_le t p.1 p.2
  have hL0 := NNReal.coe_nonneg L
  have ha := abs_nonneg (F 0)
  have hx := norm_nonneg p.1
  have hy := norm_nonneg p.2
  calc |F p.1| * ‖-sin t • p.1 + cos t • p.2‖ ≤ (|F 0| + L * ‖p.1‖) * (‖p.1‖ + ‖p.2‖) :=
        mul_le_mul h hW (norm_nonneg _) (by positivity)
    _ = |F 0| * ‖p.1‖ + |F 0| * ‖p.2‖ + L * ‖p.1‖ ^ 2 + L * (‖p.1‖ * ‖p.2‖) := by ring
    _ ≤ |F 0| * pairGrowth p + |F 0| * pairGrowth p + L * pairGrowth p + L * pairGrowth p := by
        gcongr
    _ = (2 * (|F 0| + L)) * pairGrowth p := by ring

private theorem integrable_fderiv_mul_fderiv_rot (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F)
    (t : ℝ) (e : E d) :
    Integrable fun p : E d × E d ↦
      fderiv ℝ F p.1 e * fderiv ℝ F (cos t • p.1 + sin t • p.2) e * gaussPairWeight p := by
  refine integrable_mul_gaussPairWeight ((continuous_fderiv_apply_fst hF e).mul
    (continuous_fderiv_apply_rot hF t e)).aestronglyMeasurable
    (C := (L * ‖e‖) * (L * ‖e‖)) fun p ↦ ?_
  obtain ⟨h1, -, -, -, -⟩ := pairGrowth_bounds p
  rw [abs_mul]
  calc |fderiv ℝ F p.1 e| * |fderiv ℝ F (cos t • p.1 + sin t • p.2) e|
      ≤ (L * ‖e‖) * (L * ‖e‖) :=
        mul_le_mul (abs_fderiv_apply_le hL _ _) (abs_fderiv_apply_le hL _ _) (abs_nonneg _)
          (by positivity)
    _ ≤ (L * ‖e‖) * (L * ‖e‖) * ((1 + ‖p.1‖ ^ 2) * (1 + ‖p.2‖ ^ 2)) :=
        le_mul_of_one_le_right (by positivity) h1

private theorem integrable_fst_mul_fderiv_rot (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F)
    (t : ℝ) (e : E d) :
    Integrable fun p : E d × E d ↦
      F p.1 * fderiv ℝ F (cos t • p.1 + sin t • p.2) e * gaussPairWeight p := by
  refine integrable_mul_gaussPairWeight ((hL.continuous.comp continuous_fst).mul
    (continuous_fderiv_apply_rot hF t e)).aestronglyMeasurable
    (C := (|F 0| + L) * (L * ‖e‖)) fun p ↦ ?_
  rw [abs_mul]
  calc |F p.1| * |fderiv ℝ F (cos t • p.1 + sin t • p.2) e|
      ≤ ((|F 0| + L) * pairGrowth p) * (L * ‖e‖) :=
        mul_le_mul (abs_fst_le hL p) (abs_fderiv_apply_le hL _ _) (abs_nonneg _) (by
          have := (pairGrowth_bounds p).1; positivity)
    _ = (|F 0| + L) * (L * ‖e‖) * ((1 + ‖p.1‖ ^ 2) * (1 + ‖p.2‖ ^ 2)) := by
        rw [pairGrowth]; ring

private theorem integrable_fst_mul_fderiv_rot_mul_inner (hF : ContDiff ℝ 1 F)
    (hL : LipschitzWith L F) (t : ℝ) (e : E d) :
    Integrable fun p : E d × E d ↦ F p.1 * fderiv ℝ F (cos t • p.1 + sin t • p.2) e *
      inner ℝ (-sin t • p.1 + cos t • p.2) e * gaussPairWeight p := by
  refine integrable_mul_gaussPairWeight (((hL.continuous.comp continuous_fst).mul
    (continuous_fderiv_apply_rot hF t e)).mul (by fun_prop)).aestronglyMeasurable
    (C := 2 * (|F 0| + L) * (L * ‖e‖) * ‖e‖) fun p ↦ ?_
  have h1 := abs_fderiv_apply_le hL (cos t • p.1 + sin t • p.2) e
  have h2 : |inner ℝ (-sin t • p.1 + cos t • p.2) e| ≤ ‖-sin t • p.1 + cos t • p.2‖ * ‖e‖ :=
    abs_real_inner_le_norm _ _
  have h3 := abs_fst_mul_rot_le hL t p
  have hP := (pairGrowth_bounds p).1
  rw [abs_mul, abs_mul]
  calc |F p.1| * |fderiv ℝ F (cos t • p.1 + sin t • p.2) e| *
        |inner ℝ (-sin t • p.1 + cos t • p.2) e|
      ≤ |F p.1| * (L * ‖e‖) * (‖-sin t • p.1 + cos t • p.2‖ * ‖e‖) := by gcongr
    _ = (|F p.1| * ‖-sin t • p.1 + cos t • p.2‖) * (L * ‖e‖ * ‖e‖) := by ring
    _ ≤ (2 * (|F 0| + L) * pairGrowth p) * (L * ‖e‖ * ‖e‖) := by gcongr
    _ = 2 * (|F 0| + L) * (L * ‖e‖) * ‖e‖ * ((1 + ‖p.1‖ ^ 2) * (1 + ‖p.2‖ ^ 2)) := by
        rw [pairGrowth]; ring

/-- The line derivative of the product weight along `(e sin t, -e cos t)` is `⟨W_t, e⟩` times
the weight. -/
private theorem hasLineDerivAt_gaussPairWeight (t : ℝ) (e : E d) (p : E d × E d) :
    HasLineDerivAt ℝ gaussPairWeight
      (inner ℝ (-sin t • p.1 + cos t • p.2) e * gaussPairWeight p) p
      (sin t • e, -cos t • e) := by
  have h1 : HasFDerivAt (fun q : E d × E d ↦ gaussWeight q.1)
      ((-gaussWeight p.1 • innerSL ℝ p.1).comp (ContinuousLinearMap.fst ℝ (E d) (E d))) p :=
    (hasFDerivAt_gaussWeight p.1).comp p (hasFDerivAt_fst)
  have h2 : HasFDerivAt (fun q : E d × E d ↦ gaussWeight q.2)
      ((-gaussWeight p.2 • innerSL ℝ p.2).comp (ContinuousLinearMap.snd ℝ (E d) (E d))) p :=
    (hasFDerivAt_gaussWeight p.2).comp p (hasFDerivAt_snd)
  have h := (h1.mul h2).hasLineDerivAt (sin t • e, -cos t • e)
  convert h using 1
  · funext q; rfl
  · simp only [gaussPairWeight, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      innerSL_apply_apply, smul_eq_mul, inner_add_left, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real]
    rw [real_inner_comm e p.1, real_inner_comm e p.2]
    ring_nf

/-- **Gaussian integration by parts along the rotation direction.** -/
private theorem integral_ibp_rot (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) (t : ℝ)
    (e : E d) :
    ∫ p : E d × E d, F p.1 * fderiv ℝ F (cos t • p.1 + sin t • p.2) e *
        inner ℝ (-sin t • p.1 + cos t • p.2) e * gaussPairWeight p =
      -(sin t * ∫ p : E d × E d,
        fderiv ℝ F p.1 e * fderiv ℝ F (cos t • p.1 + sin t • p.2) e * gaussPairWeight p) := by
  set v : E d × E d := (sin t • e, -cos t • e) with hv
  have hf : ∀ p : E d × E d, HasLineDerivAt ℝ
      (fun p : E d × E d ↦ F p.1 * fderiv ℝ F (cos t • p.1 + sin t • p.2) e)
      (sin t * fderiv ℝ F p.1 e * fderiv ℝ F (cos t • p.1 + sin t • p.2) e) p v := fun p ↦ by
    have hline : (fun r : ℝ ↦ F (p + r • v).1 *
          fderiv ℝ F (cos t • (p + r • v).1 + sin t • (p + r • v).2) e) =
        fun r ↦ F (p.1 + r • (sin t • e)) * fderiv ℝ F (cos t • p.1 + sin t • p.2) e := by
      funext r
      simp only [hv, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
      congr 3
      module
    have hl : HasDerivAt (fun r : ℝ ↦ p.1 + r • (sin t • e)) (sin t • e) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (sin t • e)).const_add p.1
    have hc := ((hF.differentiable one_ne_zero p.1).hasFDerivAt.comp_hasDerivAt_of_eq 0 hl
      (by simp)).mul_const (fderiv ℝ F (cos t • p.1 + sin t • p.2) e)
    change HasDerivAt (fun r : ℝ ↦ F (p + r • v).1 *
      fderiv ℝ F (cos t • (p + r • v).1 + sin t • (p + r • v).2) e) _ 0
    rw [hline]
    convert hc using 1
    · rfl
    · rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (E d)).prod volume) (B := ContinuousLinearMap.mul ℝ ℝ)
    (g := gaussPairWeight)
    (g' := fun p ↦ inner ℝ (-sin t • p.1 + cos t • p.2) e * gaussPairWeight p) (v := v)
    (by
      rw [← Measure.volume_eq_prod]
      refine ((integrable_fderiv_mul_fderiv_rot hF hL t e).const_mul (sin t)).congr
        (Eventually.of_forall fun p ↦ ?_)
      simp only [ContinuousLinearMap.mul_apply']
      ring)
    (by
      rw [← Measure.volume_eq_prod]
      refine (integrable_fst_mul_fderiv_rot_mul_inner hF hL t e).congr
        (Eventually.of_forall fun p ↦ ?_)
      simp only [ContinuousLinearMap.mul_apply']
      ring)
    (by
      rw [← Measure.volume_eq_prod]
      refine (integrable_fst_mul_fderiv_rot hF hL t e).congr (Eventually.of_forall fun p ↦ ?_)
      simp only [ContinuousLinearMap.mul_apply'])
    (fun p _ ↦ hf p) (fun p _ ↦ hasLineDerivAt_gaussPairWeight t e p)
  simp only [ContinuousLinearMap.mul_apply'] at hibp
  rw [← Measure.volume_eq_prod] at hibp
  calc ∫ p : E d × E d, F p.1 * fderiv ℝ F (cos t • p.1 + sin t • p.2) e *
        inner ℝ (-sin t • p.1 + cos t • p.2) e * gaussPairWeight p
      = ∫ p : E d × E d, F p.1 * fderiv ℝ F (cos t • p.1 + sin t • p.2) e *
        (inner ℝ (-sin t • p.1 + cos t • p.2) e * gaussPairWeight p) :=
        integral_congr_ae (Eventually.of_forall fun p ↦ by simp only; ring)
    _ = _ := hibp
    _ = _ := by
        rw [← integral_const_mul]
        congr 1
        exact integral_congr_ae (Eventually.of_forall fun p ↦ by simp only; ring)

/-- Summing `integral_ibp_rot` over an orthonormal basis:
`∫∫ F(x) DF(Z_t) W_t = -sin t ∫∫ ⟨∇F(x), ∇F(Z_t)⟩`. -/
private theorem integral_fst_mul_fderiv_rot_eq (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F)
    (t : ℝ) :
    ∫ p : E d × E d, F p.1 *
        fderiv ℝ F (cos t • p.1 + sin t • p.2) (-sin t • p.1 + cos t • p.2) * gaussPairWeight p =
      -(sin t * ∫ p : E d × E d,
        inner ℝ (∇ F p.1) (∇ F (cos t • p.1 + sin t • p.2)) * gaussPairWeight p) := by
  set b := stdOrthonormalBasis ℝ (E d)
  have h1 : ∀ p : E d × E d, F p.1 *
      fderiv ℝ F (cos t • p.1 + sin t • p.2) (-sin t • p.1 + cos t • p.2) * gaussPairWeight p =
      ∑ i, F p.1 * fderiv ℝ F (cos t • p.1 + sin t • p.2) (b i) *
        inner ℝ (-sin t • p.1 + cos t • p.2) (b i) * gaussPairWeight p := fun p ↦ by
    conv_lhs => rw [← b.sum_repr' (-sin t • p.1 + cos t • p.2)]
    rw [map_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ContinuousLinearMap.map_smul, smul_eq_mul, real_inner_comm]
    ring
  have h2 : ∀ p : E d × E d,
      inner ℝ (∇ F p.1) (∇ F (cos t • p.1 + sin t • p.2)) * gaussPairWeight p =
      ∑ i, fderiv ℝ F p.1 (b i) * fderiv ℝ F (cos t • p.1 + sin t • p.2) (b i) *
        gaussPairWeight p := fun p ↦ by
    rw [← b.sum_inner_mul_inner, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inner_gradient_left_eq_fderiv, real_inner_comm, inner_gradient_left_eq_fderiv]
  simp_rw [h1, h2]
  rw [integral_finsetSum _ fun i _ ↦ integrable_fst_mul_fderiv_rot_mul_inner hF hL t (b i),
    integral_finsetSum _ fun i _ ↦ integrable_fderiv_mul_fderiv_rot hF hL t (b i),
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ integral_ibp_rot hF hL t (b i)

/-! ### Step 3: Fubini in `(t, x, y)` and the defect -/

private theorem integrable_rot_prod (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) :
    Integrable (Function.uncurry fun (p : E d × E d) (t : ℝ) ↦ F p.1 *
        fderiv ℝ F (cos t • p.1 + sin t • p.2) (-sin t • p.1 + cos t • p.2) * gaussPairWeight p)
      ((volume : Measure (E d × E d)).prod (volume.restrict (Ioc 0 (π / 2)))) := by
  have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (π / 2))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  have hK : Integrable fun p : E d × E d ↦
      (2 * (|F 0| + L) * L) * ((1 + ‖p.1‖ ^ 2) * (1 + ‖p.2‖ ^ 2)) * gaussPairWeight p :=
    integrable_mul_gaussPairWeight (by fun_prop : Continuous fun p : E d × E d ↦
      (2 * (|F 0| + L) * L) * ((1 + ‖p.1‖ ^ 2) * (1 + ‖p.2‖ ^ 2))).aestronglyMeasurable
      (C := 2 * (|F 0| + L) * L) fun p ↦ (abs_of_nonneg (by positivity)).le
  refine (hK.mul_prod (integrable_const (1 : ℝ))).mono' ?_ (Eventually.of_forall fun z ↦ ?_)
  · refine Continuous.aestronglyMeasurable ?_
    refine ((hL.continuous.comp (continuous_fst.comp continuous_fst)).mul ?_).mul
      (continuous_gaussPairWeight.comp continuous_fst)
    exact ((hF.continuous_fderiv one_ne_zero).comp (by fun_prop)).clm_apply (by fun_prop)
  · obtain ⟨p, t⟩ := z
    simp only [Function.uncurry_apply_pair, mul_one]
    have h1 := abs_fderiv_apply_le hL (cos t • p.1 + sin t • p.2) (-sin t • p.1 + cos t • p.2)
    have h2 := abs_fst_mul_rot_le hL t p
    have hΦ := gaussPairWeight_nonneg p
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hΦ]
    calc |F p.1| * |fderiv ℝ F (cos t • p.1 + sin t • p.2) (-sin t • p.1 + cos t • p.2)| *
          gaussPairWeight p
        ≤ |F p.1| * (L * ‖-sin t • p.1 + cos t • p.2‖) * gaussPairWeight p := by gcongr
      _ = L * (|F p.1| * ‖-sin t • p.1 + cos t • p.2‖) * gaussPairWeight p := by ring
      _ ≤ L * (2 * (|F 0| + L) * pairGrowth p) * gaussPairWeight p := by gcongr
      _ = 2 * (|F 0| + L) * L * pairGrowth p * gaussPairWeight p := by ring

private theorem continuous_gradient_of_contDiff (hF : ContDiff ℝ 1 F) : Continuous (∇ F) :=
  (toDual ℝ (E d)).symm.continuous.comp (hF.continuous_fderiv one_ne_zero)

/-- Expansion of the defect: for `sin t ≠ 0`,
`gaussDefect F t = 2 Z ∫ |∇F|² e^{-|x|²/2} - 2 ∫∫ ⟨∇F(x), ∇F(Z_t)⟩`. -/
private theorem gaussDefect_eq (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) {t : ℝ}
    (ht : sin t ≠ 0) :
    gaussDefect F t = 2 * (gaussMass d * ∫ x, ‖∇ F x‖ ^ 2 * gaussWeight x) -
      2 * ∫ p : E d × E d,
        inner ℝ (∇ F p.1) (∇ F (cos t • p.1 + sin t • p.2)) * gaussPairWeight p := by
  have hg := continuous_gradient_of_contDiff hF
  have hgb : ∀ x, ‖∇ F x‖ ≤ L := fun x ↦ by
    rw [norm_gradient_eq_norm_fderiv]; exact norm_fderiv_le_of_lipschitzWith hL x
  have hb : ∀ x y : E d, |inner ℝ (∇ F x) (∇ F y)| ≤ L * L := fun x y ↦
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hgb x) (hgb y) (norm_nonneg _)
      (NNReal.coe_nonneg L))
  have hsq : ∀ x, |‖∇ F x‖ ^ 2| ≤ L * L := fun x ↦ by
    rw [abs_of_nonneg (sq_nonneg _), sq]
    exact mul_le_mul (hgb x) (hgb x) (norm_nonneg _) (NNReal.coe_nonneg L)
  have hint : ∀ f : E d × E d → ℝ, Continuous f → (∀ p, |f p| ≤ L * L) →
      Integrable fun p ↦ f p * gaussPairWeight p := fun f hf hfb ↦
    integrable_mul_gaussPairWeight hf.aestronglyMeasurable (C := L * L) fun p ↦
      (hfb p).trans (le_mul_of_one_le_right (by positivity) (pairGrowth_bounds p).1)
  have hZ : Continuous fun p : E d × E d ↦ cos t • p.1 + sin t • p.2 := by fun_prop
  have i1 := hint (fun p ↦ ‖∇ F p.1‖ ^ 2) (by fun_prop) fun p ↦ hsq _
  have i2 := hint (fun p ↦ inner ℝ (∇ F p.1) (∇ F (cos t • p.1 + sin t • p.2)))
    ((hg.comp continuous_fst).inner (hg.comp hZ)) fun p ↦ hb _ _
  have i3 := hint (fun p ↦ ‖∇ F (cos t • p.1 + sin t • p.2)‖ ^ 2)
    (((hg.comp hZ).norm).pow 2) fun p ↦ hsq _
  have e1 : ∫ p : E d × E d, ‖∇ F p.1‖ ^ 2 * gaussPairWeight p =
      gaussMass d * ∫ x, ‖∇ F x‖ ^ 2 * gaussWeight x := by
    have : (fun p : E d × E d ↦ ‖∇ F p.1‖ ^ 2 * gaussPairWeight p) =
        fun p ↦ (‖∇ F p.1‖ ^ 2 * gaussWeight p.1) * gaussWeight p.2 := by
      funext p; rw [gaussPairWeight]; ring
    rw [this, Measure.volume_eq_prod]
    exact (integral_prod_mul (fun x ↦ ‖∇ F x‖ ^ 2 * gaussWeight x) gaussWeight).trans
      (by rw [gaussMass, mul_comm])
  have e3 : ∫ p : E d × E d, ‖∇ F (cos t • p.1 + sin t • p.2)‖ ^ 2 * gaussPairWeight p =
      gaussMass d * ∫ x, ‖∇ F x‖ ^ 2 * gaussWeight x :=
    integral_comp_add_smul_gaussPairWeight (cos_sq_add_sin_sq t) ht
      ((measurable_gradient F).norm.pow_const 2) fun x ↦ sq_nonneg _
  have hexp : (fun p : E d × E d ↦
      ‖∇ F p.1 - ∇ F (cos t • p.1 + sin t • p.2)‖ ^ 2 * gaussPairWeight p) =
      fun p ↦ ‖∇ F p.1‖ ^ 2 * gaussPairWeight p -
        2 * (inner ℝ (∇ F p.1) (∇ F (cos t • p.1 + sin t • p.2)) * gaussPairWeight p) +
        ‖∇ F (cos t • p.1 + sin t • p.2)‖ ^ 2 * gaussPairWeight p := by
    funext p; rw [norm_sub_sq_real]; ring
  rw [gaussDefect, hexp, integral_add (by exact i1.sub (i2.const_mul 2)) i3,
    integral_sub i1 (by exact i2.const_mul 2), integral_const_mul, e1, e3]
  ring

/-- The defect is continuous in `t` (for `F` of class `C¹` and Lipschitz). -/
public theorem continuous_gaussDefect (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) :
    Continuous (gaussDefect F) := by
  have hg := continuous_gradient_of_contDiff hF
  have hgb : ∀ x, ‖∇ F x‖ ≤ L := fun x ↦ by
    rw [norm_gradient_eq_norm_fderiv]; exact norm_fderiv_le_of_lipschitzWith hL x
  have hΦ : Integrable fun p : E d × E d ↦ (2 * L) ^ 2 * gaussPairWeight p :=
    integrable_mul_gaussPairWeight (f := fun _ ↦ (2 * (L : ℝ)) ^ 2)
      aestronglyMeasurable_const (C := (2 * L) ^ 2) fun p ↦ by
        rw [abs_of_nonneg (by positivity)]
        exact le_mul_of_one_le_right (by positivity) (pairGrowth_bounds p).1
  refine continuous_of_dominated (fun t ↦ ?_) (fun t ↦ Eventually.of_forall fun p ↦ ?_) hΦ
    (Eventually.of_forall fun p ↦ ?_)
  · exact ((((hg.comp continuous_fst).sub (hg.comp (by fun_prop))).norm.pow 2).mul
      continuous_gaussPairWeight).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (gaussPairWeight_nonneg p))]
    gcongr ?_ * _
    · exact gaussPairWeight_nonneg p
    · refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      refine (norm_sub_le _ _).trans ?_
      linarith [hgb p.1, hgb (cos t • p.1 + sin t • p.2)]
  · exact (((continuous_const.sub (hg.comp (by fun_prop))).norm.pow 2).mul continuous_const)

/-- **The defect identity.** For
`F : ℝᵈ → ℝ` of class `C¹` and Lipschitz,
`gaussVariance F + ½ ∫₀^{π/2} sin t · gaussDefect F t dt = Z ∫ |∇F|² e^{-|x|²/2}`, where
`gaussVariance F = Z² Var_γ F` and `Z = gaussMass d`. Dividing by `Z²`, this is
`∫ |∇F|² dγ - Var_γ F = ½ ∫₀^{π/2} sin t ∫∫ |∇F(x) - ∇F(x cos t + y sin t)|² dγ(x) dγ(y) dt`. -/
public theorem gaussVariance_add_integral_sin_mul_gaussDefect (hF : ContDiff ℝ 1 F)
    (hL : LipschitzWith L F) :
    gaussVariance F + (∫ t in (0 : ℝ)..(π / 2), sin t * gaussDefect F t) / 2 =
      gaussMass d * ∫ x, ‖∇ F x‖ ^ 2 * gaussWeight x := by
  set G := gaussMass d * ∫ x, ‖∇ F x‖ ^ 2 * gaussWeight x
  set g : ℝ → E d × E d → ℝ := fun t p ↦ F p.1 *
    fderiv ℝ F (cos t • p.1 + sin t • p.2) (-sin t • p.1 + cos t • p.2) * gaussPairWeight p
  -- the variance as an iterated integral in `(t, p)`
  have hV : gaussVariance F = -∫ t in (0 : ℝ)..(π / 2), ∫ p, g t p := by
    rw [gaussVariance_eq_integral hL, intervalIntegral.integral_of_le pi_div_two_pos.le,
      ← integral_integral_swap (integrable_rot_prod hF hL), ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun p ↦ ?_)
    simp only
    rw [integral_mul_const, integral_const_mul, ← intervalIntegral.integral_of_le
      pi_div_two_pos.le, ← sub_eq_integral_fderiv_rot hF]
    ring
  -- pointwise in `t`
  have hpt : ∀ t, ∫ p, g t p = -(sin t * G) + sin t * gaussDefect F t / 2 := fun t ↦ by
    rw [integral_fst_mul_fderiv_rot_eq hF hL]
    by_cases ht : sin t = 0
    · simp [ht]
    · rw [gaussDefect_eq hF hL ht]
      ring
  have hc := continuous_gaussDefect hF hL
  rw [hV]
  simp_rw [hpt]
  rw [intervalIntegral.integral_add
      (Continuous.intervalIntegrable (by fun_prop : Continuous fun t ↦ -(sin t * G)) _ _)
      (Continuous.intervalIntegrable (by fun_prop : Continuous fun t ↦
        sin t * gaussDefect F t / 2) _ _),
    intervalIntegral.integral_neg, intervalIntegral.integral_mul_const, integral_sin,
    intervalIntegral.integral_div]
  simp

end Smooth

end EllipticBernoulli
