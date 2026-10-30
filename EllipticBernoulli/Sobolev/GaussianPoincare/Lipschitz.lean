/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sobolev.GaussianPoincare.Smooth
import EllipticBernoulli.Sobolev.Mollify
import EllipticBernoulli.Sobolev.Lipschitz
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# The Gaussian Poincaré inequality for Lipschitz functions

For `F : ℝᵈ → ℝ` Lipschitz, with pointwise gradient `∇F` (`0` where `F` is not differentiable):

* `gaussVariance_le_of_lipschitzWith`: `gaussVariance F ≤ Z ∫ |∇F|² e^{-|x|²/2}`, i.e.
  `Var_γ F ≤ ∫ |∇F|² dγ`;
* `lintegral_sin_mul_defect_le_of_lipschitzWith`:
  `∫₀^{π/2} sin t ∫∫ |∇F(x) - ∇F(x cos t + y sin t)|² e^{-(|x|²+|y|²)/2} dx dy dt
    ≤ 2 (Z ∫ |∇F|² e^{-|x|²/2} - gaussVariance F)`,
  as lower integrals.

## Proof

Mollify, `F_n = F ⋆ ρ_n` with `ρ_n` a normalized bump supported in the ball of radius
`2/(n+1)`. Then `F_n` is smooth and `L`-Lipschitz, `F_n → F` pointwise with
`|F_n - F| ≤ 2L`, and `DF_n(x) v = (⟨∇F, v⟩ ⋆ ρ_n)(x)` (the pointwise gradient of a Lipschitz
function is a weak gradient, `fderiv_convolution_indicator_eq`), so `∇F_n → ∇F` a.e. by the
Lebesgue differentiation theorem (`ae_convolution_tendsto_right_of_locallyIntegrable`).
Dominated convergence passes the variance and the Dirichlet energy to the limit in the defect
identity of `Smooth.lean`. For the defect term, Fatou's lemma suffices (applied in `(x, y)` for
each `t` and then in `t`): `∇F_n(x cos t + y sin t) → ∇F(x cos t + y sin t)` for a.e. `(x, y)`
since `(x, y) ↦ x cos t + y sin t` pulls null sets back to null sets
(`measure_preimage_add_smul_eq_zero`). Only the inequality is passed to the limit, not the
identity itself; the inequality is all that the equality case needs.
-/

open Set Filter Topology MeasureTheory Real InnerProductSpace ContinuousLinearMap
open scoped Gradient NNReal Convolution ENNReal ContDiff

namespace EllipticBernoulli

variable {d : ℕ} {F : E d → ℝ} {L : ℝ≥0}

/-! ### Mollification -/

/-- The bump `ρ_n` with radii `1/(n+1)` and `2/(n+1)`. -/
private noncomputable def molBump (n : ℕ) : ContDiffBump (0 : E d) where
  rIn := ((n : ℝ) + 1)⁻¹
  rOut := 2 * ((n : ℝ) + 1)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := by have : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
                    linarith

/-- The mollification `F_n = F ⋆ ρ_n`. -/
private noncomputable def mollify (F : E d → ℝ) (n : ℕ) : E d → ℝ :=
  F ⋆[lsmul ℝ ℝ, volume] (molBump n).normed volume

private theorem molBump_rOut (n : ℕ) : (molBump (d := d) n).rOut = 2 * ((n : ℝ) + 1)⁻¹ := rfl

private theorem molBump_rOut_le_two (n : ℕ) : (molBump (d := d) n).rOut ≤ 2 := by
  rw [molBump_rOut]
  have : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [n.cast_nonneg (α := ℝ)])
  linarith

private theorem tendsto_molBump_rOut :
    Tendsto (fun n ↦ (molBump (d := d) n).rOut) atTop (𝓝 0) := by
  simp_rw [molBump_rOut]
  simpa [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)

/-- Real convolution is commutative. -/
private theorem convolution_lsmul_comm (f g : E d → ℝ) (x : E d) :
    (f ⋆[lsmul ℝ ℝ, volume] g) x = (g ⋆[lsmul ℝ ℝ, volume] f) x := by
  rw [convolution_def, convolution_eq_swap]
  simp only [lsmul_apply, smul_eq_mul, mul_comm]

private theorem mollify_eq_swap (F : E d → ℝ) (n : ℕ) (x : E d) :
    mollify F n x = ∫ t, F (x - t) * (molBump n).normed volume t := by
  rw [mollify, convolution_eq_swap]
  simp only [lsmul_apply, smul_eq_mul]

private theorem contDiff_mollify (hL : LipschitzWith L F) (n : ℕ) :
    ContDiff ℝ 1 (mollify F n) :=
  (molBump n).hasCompactSupport_normed.contDiff_convolution_right (lsmul ℝ ℝ)
    hL.continuous.locallyIntegrable ((molBump n).contDiff_normed (n := 1))

private theorem integrable_comp_sub_mul_normed (hL : LipschitzWith L F) (n : ℕ) (x : E d) :
    Integrable fun t ↦ F (x - t) * (molBump n).normed volume t :=
  ((hL.continuous.comp (continuous_const.sub continuous_id)).mul
    (molBump n).continuous_normed).integrable_of_hasCompactSupport
    (molBump n).hasCompactSupport_normed.mul_left

private theorem lipschitzWith_mollify (hL : LipschitzWith L F) (n : ℕ) :
    LipschitzWith L (mollify F n) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [Real.dist_eq, mollify_eq_swap, mollify_eq_swap,
    ← integral_sub (integrable_comp_sub_mul_normed hL n x)
      (integrable_comp_sub_mul_normed hL n y)]
  have hρ := (molBump (d := d) n).integral_normed (μ := volume)
  calc |∫ t, (F (x - t) * (molBump n).normed volume t - F (y - t) * (molBump n).normed volume t)|
      ≤ ∫ t, L * dist x y * (molBump n).normed volume t := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le ((molBump n).integrable_normed.const_mul _)
          (Eventually.of_forall fun t ↦ ?_)
        rw [← sub_mul, norm_mul, Real.norm_of_nonneg ((molBump n).nonneg_normed t)]
        refine mul_le_mul_of_nonneg_right ?_ ((molBump n).nonneg_normed t)
        have := hL.dist_le_mul (x - t) (y - t)
        rwa [dist_sub_right, Real.dist_eq, ← Real.norm_eq_abs] at this
    _ = L * dist x y := by rw [integral_const_mul, hρ, mul_one]

private theorem abs_mollify_sub_le (hL : LipschitzWith L F) (n : ℕ) (x : E d) :
    |mollify F n x - F x| ≤ L * (molBump (d := d) n).rOut := by
  rw [← Real.dist_eq, mollify, convolution_lsmul_comm]
  refine (molBump n).dist_normed_convolution_le hL.continuous.aestronglyMeasurable
    fun y hy ↦ ?_
  refine (hL.dist_le_mul y x).trans ?_
  exact mul_le_mul_of_nonneg_left (Metric.mem_ball.1 hy).le (NNReal.coe_nonneg L)

private theorem tendsto_mollify (hL : LipschitzWith L F) (x : E d) :
    Tendsto (fun n ↦ mollify F n x) atTop (𝓝 (F x)) := by
  have h0 : Tendsto (fun n ↦ (L : ℝ) * (molBump (d := d) n).rOut) atTop (𝓝 0) := by
    simpa using (tendsto_molBump_rOut (d := d)).const_mul (L : ℝ)
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_) h0)
  rw [Real.dist_eq]
  exact abs_mollify_sub_le hL n x

/-- `DF_n(x) v = (⟨∇F, v⟩ ⋆ ρ_n)(x)`. -/
private theorem fderiv_mollify_apply (hL : LipschitzWith L F) (n : ℕ) (x v : E d) :
    fderiv ℝ (mollify F n) x v =
      ((fun y ↦ inner ℝ (∇ F y) v) ⋆[lsmul ℝ ℝ, volume] (molBump n).normed volume) x := by
  set ρ := molBump (d := d) n
  set B := Metric.closedBall x (ρ.rOut + 1)
  have hG : HasWeakGradient univ F (∇ F) :=
    (memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ
      hL.locallyLipschitz.locallyLipschitzOn).1
  have hw : ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ B → ∀ v : E d,
      ∫ y, F y * fderiv ℝ φ y v = -∫ y, inner ℝ (∇ F y) v * φ y := by
    intro φ hφ hφc _ v
    have := hG.2.2 φ hφ hφc (subset_univ _) v
    rwa [Measure.restrict_univ] at this
  have hzero : ∀ y : E d, ρ.rOut < ‖y‖ → ρ.normed volume y = 0 := fun y hy ↦ by
    refine image_eq_zero_of_notMem_tsupport ?_
    rw [ρ.tsupport_normed_eq, Metric.mem_closedBall, dist_zero_right]
    exact not_le.2 hy
  have hsub : ∀ y ∈ Metric.ball x 1, Metric.closedBall y ρ.rOut ⊆ B := fun y hy ↦
    Metric.closedBall_subset_closedBall' (by linarith [(Metric.mem_ball.1 hy)])
  have hmain := fderiv_convolution_indicator_eq Metric.isClosed_closedBall.measurableSet
    (hL.continuous.continuousOn.integrableOn_compact (isCompact_closedBall x _)) hw ρ v
    (hsub x (Metric.mem_ball_self one_pos))
  have hev : mollify F n =ᶠ[𝓝 x] (B.indicator F ⋆[lsmul ℝ ℝ, volume] ρ.normed volume) := by
    filter_upwards [Metric.ball_mem_nhds x one_pos] with y hy
    rw [convolution_indicator_eq_integral F _ hzero (hsub y hy), mollify, convolution_def]
    simp only [lsmul_apply, smul_eq_mul]
    rfl
  rw [hev.fderiv_eq, hmain, convolution_indicator_eq_integral _ _ hzero
    (hsub x (Metric.mem_ball_self one_pos)), convolution_def]
  simp only [lsmul_apply, smul_eq_mul]

private theorem norm_gradient_mollify_le (hL : LipschitzWith L F) (n : ℕ) (x : E d) :
    ‖∇ (mollify F n) x‖ ≤ L := by
  rw [norm_gradient_eq_norm_fderiv]
  exact norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_mollify hL n)

/-- `∇F_n → ∇F` almost everywhere. -/
private theorem ae_tendsto_gradient_mollify (hL : LipschitzWith L F) :
    ∀ᵐ x, Tendsto (fun n ↦ ∇ (mollify F n) x) atTop (𝓝 (∇ F x)) := by
  set b := stdOrthonormalBasis ℝ (E d)
  have hcoord : ∀ i, ∀ᵐ x, Tendsto (fun n ↦ fderiv ℝ (mollify F n) x (b i)) atTop
      (𝓝 (inner ℝ (∇ F x) (b i))) := fun i ↦ by
    have hloc : LocallyIntegrable (fun y ↦ inner ℝ (∇ F y) (b i)) volume := fun y ↦
      ⟨Metric.ball y 1, Metric.ball_mem_nhds y one_pos,
        Measure.integrableOn_of_bounded (M := L * ‖b i‖) measure_ball_lt_top.ne
          (Measurable.inner (measurable_gradient F) measurable_const).aestronglyMeasurable
          (Eventually.of_forall fun z ↦ (norm_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_right ((norm_gradient_eq_norm_fderiv F z).trans_le
              (norm_fderiv_le_of_lipschitz ℝ hL)) (norm_nonneg _)))⟩
    filter_upwards [ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (φ := molBump) tendsto_molBump_rOut (K := 2)
      (Eventually.of_forall fun n ↦ le_of_eq rfl) hloc] with x hx
    refine hx.congr fun n ↦ ?_
    rw [fderiv_mollify_apply hL, convolution_lsmul_comm]
  filter_upwards [ae_all_iff.2 hcoord] with x hx
  have hrepr : ∀ G : E d, G = ∑ i, inner ℝ G (b i) • b i := fun G ↦ by
    conv_lhs => rw [← b.sum_repr' G]
    simp_rw [real_inner_comm]
  rw [hrepr (∇ F x)]
  refine (tendsto_finsetSum _ fun i _ ↦ (hx i).smul_const (b i)).congr fun n ↦ ?_
  rw [hrepr (∇ (mollify F n) x)]
  simp_rw [inner_gradient_left_eq_fderiv]

/-! ### Passing to the limit -/

/-- The integrand of the defect, as a lower-integrand on `(0, π/2] × ℝᵈ × ℝᵈ`. -/
private noncomputable def defectIntegrand (G : E d → ℝ) (t : ℝ) (p : E d × E d) : ℝ≥0∞ :=
  ENNReal.ofReal (sin t * ‖∇ G p.1 - ∇ G (cos t • p.1 + sin t • p.2)‖ ^ 2 * gaussPairWeight p)

private theorem measurable_defectIntegrand (G : E d → ℝ) :
    Measurable fun z : ℝ × (E d × E d) ↦ defectIntegrand G z.1 z.2 := by
  refine ENNReal.measurable_ofReal.comp ?_
  refine ((continuous_sin.measurable.comp measurable_fst).mul ?_).mul
    (continuous_gaussPairWeight.measurable.comp measurable_snd)
  refine (((measurable_gradient G).comp (measurable_fst.comp measurable_snd)).sub
    ((measurable_gradient G).comp ?_)).norm.pow_const 2
  exact (by fun_prop : Continuous fun z : ℝ × (E d × E d) ↦
    cos z.1 • z.2.1 + sin z.1 • z.2.2).measurable

private theorem measurable_defectIntegrand_right (G : E d → ℝ) (t : ℝ) :
    Measurable (defectIntegrand G t) := by
  unfold defectIntegrand
  refine ENNReal.measurable_ofReal.comp ((measurable_const.mul ?_).mul
    continuous_gaussPairWeight.measurable)
  exact (((measurable_gradient G).comp measurable_fst).sub ((measurable_gradient G).comp
    (by fun_prop : Continuous fun p : E d × E d ↦
      cos t • p.1 + sin t • p.2).measurable)).norm.pow_const 2

private theorem integrable_defect (hL : LipschitzWith L F) (t : ℝ) :
    Integrable fun p : E d × E d ↦
      ‖∇ F p.1 - ∇ F (cos t • p.1 + sin t • p.2)‖ ^ 2 * gaussPairWeight p := by
  have hgb : ∀ x, ‖∇ F x‖ ≤ L := fun x ↦ by
    rw [norm_gradient_eq_norm_fderiv]; exact norm_fderiv_le_of_lipschitz ℝ hL
  refine integrable_mul_gaussPairWeight ((((measurable_gradient F).comp measurable_fst).sub
    ((measurable_gradient F).comp (by fun_prop : Continuous fun p : E d × E d ↦
      cos t • p.1 + sin t • p.2).measurable)).norm.pow_const 2).aestronglyMeasurable
    (C := (2 * L) ^ 2) fun p ↦ ?_
  rw [abs_of_nonneg (sq_nonneg _)]
  have h1 : 1 ≤ (1 + ‖p.1‖ ^ 2) * (1 + ‖p.2‖ ^ 2) :=
    one_le_mul_of_one_le_of_one_le (by nlinarith [sq_nonneg ‖p.1‖])
      (by nlinarith [sq_nonneg ‖p.2‖])
  refine (pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans ?_) 2).trans
    (le_mul_of_one_le_right (by positivity) h1)
  linarith [hgb p.1, hgb (cos t • p.1 + sin t • p.2)]

/-- The defect identity of `Smooth.lean` as an identity of lower integrals. -/
private theorem lintegral_defectIntegrand_eq (hF : ContDiff ℝ 1 F) (hL : LipschitzWith L F) :
    ∫⁻ t in Ioc 0 (π / 2), ∫⁻ p, defectIntegrand F t p =
      ENNReal.ofReal (2 * (gaussMass d * (∫ x, ‖∇ F x‖ ^ 2 * gaussWeight x) -
        gaussVariance F)) := by
  have hsin : ∀ t ∈ Ioc (0 : ℝ) (π / 2), 0 ≤ sin t := fun t ht ↦
    sin_nonneg_of_nonneg_of_le_pi ht.1.le (ht.2.trans (by linarith [pi_pos]))
  have hin : ∀ t ∈ Ioc (0 : ℝ) (π / 2),
      ∫⁻ p, defectIntegrand F t p = ENNReal.ofReal (sin t * gaussDefect F t) := by
    intro t ht
    rw [gaussDefect, ← integral_const_mul, ofReal_integral_eq_lintegral_ofReal
      ((integrable_defect hL t).const_mul _) (Eventually.of_forall fun p ↦ mul_nonneg (hsin t ht)
        (mul_nonneg (sq_nonneg _) (gaussPairWeight_nonneg p)))]
    refine lintegral_congr fun p ↦ ?_
    rw [defectIntegrand, mul_assoc]
  have hc := continuous_gaussDefect hF hL
  rw [setLIntegral_congr_fun measurableSet_Ioc hin, ← ofReal_integral_eq_lintegral_ofReal
    ((by fun_prop : Continuous fun t ↦ sin t * gaussDefect F t).integrableOn_Ioc)
    ((ae_restrict_mem measurableSet_Ioc).mono
      fun t ht ↦ mul_nonneg (hsin t ht) (integral_nonneg fun p ↦
        mul_nonneg (sq_nonneg _) (gaussPairWeight_nonneg p))),
    ← intervalIntegral.integral_of_le pi_div_two_pos.le]
  have := gaussVariance_add_integral_sin_mul_gaussDefect hF hL
  congr 1
  linarith

private theorem tendsto_gaussVariance_mollify (hL : LipschitzWith L F) :
    Tendsto (fun n ↦ gaussVariance (mollify F n)) atTop (𝓝 (gaussVariance F)) := by
  set A : ℝ := |F 0| + 2 * L
  have hb : ∀ n x, |mollify F n x| ≤ A + L * ‖x‖ := fun n x ↦ by
    have h1 := abs_mollify_sub_le hL n x
    have h2 := mul_le_mul_of_nonneg_left (molBump_rOut_le_two (d := d) n) (NNReal.coe_nonneg L)
    have h3 := hL.dist_le_mul x 0
    rw [Real.dist_eq, dist_zero_right] at h3
    have h4 := abs_sub_abs_le_abs_sub (mollify F n x) (F x)
    have h5 := abs_sub_abs_le_abs_sub (F x) (F 0)
    simp only [A]
    linarith
  have hgrowth : ∀ x : E d, |(A + L * ‖x‖) ^ 2| ≤ 2 * (A ^ 2 + L ^ 2) * (1 + ‖x‖ ^ 2) :=
    fun x ↦ by
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg (A - L * ‖x‖), sq_nonneg (L : ℝ), sq_nonneg A, sq_nonneg ‖x‖,
        mul_nonneg (sq_nonneg (L : ℝ)) (sq_nonneg ‖x‖)]
  have hgrowth1 : ∀ x : E d, |A + L * ‖x‖| ≤ (A + L) * (1 + ‖x‖ ^ 2) := fun x ↦ by
    have hA : 0 ≤ A := by positivity
    have hx : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
    rw [abs_of_nonneg (by positivity)]
    have := mul_le_mul_of_nonneg_left hx (NNReal.coe_nonneg L)
    nlinarith [mul_nonneg hA (sq_nonneg ‖x‖)]
  have hcont : ∀ n, Continuous (mollify F n) := fun n ↦ (lipschitzWith_mollify hL n).continuous
  have h2 : Tendsto (fun n ↦ ∫ x, mollify F n x ^ 2 * gaussWeight x) atTop
      (𝓝 (∫ x, F x ^ 2 * gaussWeight x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ (A + L * ‖x‖) ^ 2 * gaussWeight x)
      (fun n ↦ ((hcont n).pow 2 |>.mul continuous_gaussWeight).aestronglyMeasurable)
      (integrable_mul_gaussWeight (by fun_prop) hgrowth) (fun n ↦ Eventually.of_forall
        fun x ↦ ?_) (Eventually.of_forall fun x ↦
          (((tendsto_mollify hL x).pow 2).mul_const _))
    rw [norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_of_nonneg (gaussWeight_nonneg x)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hb n x) 2)
      (gaussWeight_nonneg x)
  have h1 : Tendsto (fun n ↦ ∫ x, mollify F n x * gaussWeight x) atTop
      (𝓝 (∫ x, F x * gaussWeight x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ (A + L * ‖x‖) * gaussWeight x)
      (fun n ↦ ((hcont n).mul continuous_gaussWeight).aestronglyMeasurable)
      (integrable_mul_gaussWeight (by fun_prop) hgrowth1) (fun n ↦ Eventually.of_forall
        fun x ↦ ?_) (Eventually.of_forall fun x ↦ ((tendsto_mollify hL x).mul_const _))
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (gaussWeight_nonneg x)]
    exact mul_le_mul_of_nonneg_right (hb n x) (gaussWeight_nonneg x)
  exact (h2.const_mul _).sub (h1.pow 2)

private theorem tendsto_energy_mollify (hL : LipschitzWith L F) :
    Tendsto (fun n ↦ ∫ x, ‖∇ (mollify F n) x‖ ^ 2 * gaussWeight x) atTop
      (𝓝 (∫ x, ‖∇ F x‖ ^ 2 * gaussWeight x)) := by
  refine tendsto_integral_of_dominated_convergence (fun x ↦ (L : ℝ) ^ 2 * gaussWeight x)
    (fun n ↦ (((measurable_gradient _).norm.pow_const 2).mul
      continuous_gaussWeight.measurable).aestronglyMeasurable)
    (integrable_gaussWeight.const_mul _) (fun n ↦ Eventually.of_forall fun x ↦ ?_) ?_
  · rw [norm_mul, norm_pow, norm_norm, Real.norm_of_nonneg (gaussWeight_nonneg x)]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_mollify_le hL n x) 2)
      (gaussWeight_nonneg x)
  · filter_upwards [ae_tendsto_gradient_mollify hL] with x hx
    exact ((hx.norm.pow 2).mul_const _)

/-- **Gaussian Poincaré inequality** for Lipschitz `F`: `Var_γ F ≤ ∫ |∇F|² dγ`, in the form
`gaussVariance F ≤ Z ∫ |∇F|² e^{-|x|²/2}` (`Z = gaussMass d`). -/
public theorem gaussVariance_le_of_lipschitzWith (hL : LipschitzWith L F) :
    gaussVariance F ≤ gaussMass d * ∫ x, ‖∇ F x‖ ^ 2 * gaussWeight x := by
  refine le_of_tendsto_of_tendsto' (tendsto_gaussVariance_mollify hL)
    ((tendsto_energy_mollify hL).const_mul _) fun n ↦ ?_
  have h := gaussVariance_add_integral_sin_mul_gaussDefect (contDiff_mollify hL n)
    (lipschitzWith_mollify hL n)
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..(π / 2), sin t * gaussDefect (mollify F n) t :=
    intervalIntegral.integral_nonneg pi_div_two_pos.le fun t ht ↦ mul_nonneg
      (sin_nonneg_of_nonneg_of_le_pi ht.1 (ht.2.trans (by linarith [pi_pos])))
      (integral_nonneg fun p ↦ mul_nonneg (sq_nonneg _) (gaussPairWeight_nonneg p))
  linarith

/-- **The defect bound for Lipschitz functions**: for
`F` Lipschitz,
`∫₀^{π/2} sin t ∫∫ |∇F(x) - ∇F(x cos t + y sin t)|² e^{-(|x|²+|y|²)/2} dx dy dt
  ≤ 2 (Z ∫ |∇F|² e^{-|x|²/2} - gaussVariance F)`
as lower integrals. -/
public theorem lintegral_sin_mul_defect_le_of_lipschitzWith (hL : LipschitzWith L F) :
    ∫⁻ t in Ioc 0 (π / 2), ∫⁻ p : E d × E d,
        ENNReal.ofReal (sin t * ‖∇ F p.1 - ∇ F (cos t • p.1 + sin t • p.2)‖ ^ 2 *
          gaussPairWeight p) ≤
      ENNReal.ofReal (2 * (gaussMass d * (∫ x, ‖∇ F x‖ ^ 2 * gaussWeight x) -
        gaussVariance F)) := by
  -- Fatou in `(x, y)` for each `t`
  have hpt : ∀ t ∈ Ioc (0 : ℝ) (π / 2), ∫⁻ p, defectIntegrand F t p ≤
      liminf (fun n ↦ ∫⁻ p, defectIntegrand (mollify F n) t p) atTop := by
    intro t ht
    have hs : sin t ≠ 0 :=
      (sin_pos_of_pos_of_lt_pi ht.1 (ht.2.trans_lt (by linarith [pi_pos]))).ne'
    have hN := ae_tendsto_gradient_mollify hL (F := F)
    have h1 : ∀ᵐ p : E d × E d, Tendsto (fun n ↦ ∇ (mollify F n) p.1) atTop (𝓝 (∇ F p.1)) := by
      rw [Measure.volume_eq_prod]
      exact Measure.quasiMeasurePreserving_fst.ae hN
    have h2 : ∀ᵐ p : E d × E d, Tendsto (fun n ↦ ∇ (mollify F n) (cos t • p.1 + sin t • p.2))
        atTop (𝓝 (∇ F (cos t • p.1 + sin t • p.2))) := by
      rw [ae_iff] at hN ⊢
      exact measure_preimage_add_smul_eq_zero (cos_sq_add_sin_sq t) hs hN
    calc ∫⁻ p, defectIntegrand F t p
        = ∫⁻ p, liminf (fun n ↦ defectIntegrand (mollify F n) t p) atTop := by
          refine lintegral_congr_ae ?_
          filter_upwards [h1, h2] with p hp1 hp2
          have : Tendsto (fun n ↦ defectIntegrand (mollify F n) t p) atTop
              (𝓝 (defectIntegrand F t p)) := by
            unfold defectIntegrand
            exact (ENNReal.continuous_ofReal.tendsto _).comp
              ((((hp1.sub hp2).norm.pow 2).const_mul _).mul_const _)
          exact this.liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le fun n ↦ measurable_defectIntegrand_right (mollify F n) t
  -- Fatou in `t`
  have hlim : Tendsto (fun n ↦ ∫⁻ t in Ioc 0 (π / 2), ∫⁻ p, defectIntegrand (mollify F n) t p)
      atTop (𝓝 (ENNReal.ofReal (2 * (gaussMass d * (∫ x, ‖∇ F x‖ ^ 2 * gaussWeight x) -
        gaussVariance F)))) := by
    simp_rw [lintegral_defectIntegrand_eq (contDiff_mollify hL _) (lipschitzWith_mollify hL _)]
    refine ENNReal.tendsto_ofReal (((tendsto_energy_mollify hL).const_mul _).sub
      (tendsto_gaussVariance_mollify hL) |>.const_mul 2)
  calc ∫⁻ t in Ioc 0 (π / 2), ∫⁻ p, defectIntegrand F t p
      ≤ ∫⁻ t in Ioc 0 (π / 2), liminf (fun n ↦ ∫⁻ p, defectIntegrand (mollify F n) t p) atTop :=
        setLIntegral_mono' measurableSet_Ioc hpt
    _ ≤ liminf (fun n ↦ ∫⁻ t in Ioc 0 (π / 2), ∫⁻ p, defectIntegrand (mollify F n) t p)
          atTop :=
        lintegral_liminf_le fun n ↦ (measurable_defectIntegrand (mollify F n)).lintegral_prod_right'
    _ = _ := hlim.liminf_eq

end EllipticBernoulli
