/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.Sobolev
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The Gaussian weight

The unnormalized Gaussian weight `gaussWeight x = e^{-|x|²/2}` on `ℝᵈ`, its total mass
`gaussMass d = ∫ e^{-|x|²/2}`, and the product weight `gaussPairWeight (x, y) = e^{-(|x|²+|y|²)/2}`
on `ℝᵈ × ℝᵈ`. The standard Gaussian measure is `γ = gaussWeight x dx / gaussMass d`;
we work with the weight throughout and never normalize.

* `integrable_mul_gaussWeight`, `integrable_mul_gaussPairWeight`: functions of quadratic growth
  are integrable against the weight.
* `lintegral_comp_add_smul_gaussPairWeight`: **rotation invariance.** If `c² + s² = 1` and `s ≠ 0`,
  then `x cos t + y sin t` has law `γ` under `γ ⊗ γ`:
  `∫∫ h(c x + s y) e^{-(|x|²+|y|²)/2} dx dy = gaussMass d · ∫ h(x) e^{-|x|²/2} dx`.
* `measure_preimage_add_smul_eq_zero`: the map `(x, y) ↦ c x + s y` pulls null sets back to null
  sets.

The rotation invariance is proved by two linear changes of variable on `ℝᵈ` and Tonelli, using the
completed square `|x|² + |(u - c x)/s|² = |u|² + |(x - c u)/s|²`; no change of variables on
`ℝᵈ × ℝᵈ` is needed.
-/

open Set Filter Topology MeasureTheory Real Module
open scoped ENNReal

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- The unnormalized Gaussian weight `e^{-|x|²/2}` on `ℝᵈ`. -/
def gaussWeight (x : E d) : ℝ := Real.exp (-(‖x‖ ^ 2 / 2))

/-- The total mass `∫ e^{-|x|²/2} dx` of the Gaussian weight. -/
def gaussMass (d : ℕ) : ℝ := ∫ x : E d, gaussWeight x

/-- The product Gaussian weight `e^{-(|x|²+|y|²)/2}` on `ℝᵈ × ℝᵈ`. -/
def gaussPairWeight (p : E d × E d) : ℝ := gaussWeight p.1 * gaussWeight p.2

theorem gaussWeight_pos (x : E d) : 0 < gaussWeight x := Real.exp_pos _

theorem gaussWeight_nonneg (x : E d) : 0 ≤ gaussWeight x := (gaussWeight_pos x).le

theorem gaussWeight_le_one (x : E d) : gaussWeight x ≤ 1 :=
  Real.exp_le_one_iff.2 (by have := sq_nonneg ‖x‖; linarith)

theorem gaussPairWeight_pos (p : E d × E d) : 0 < gaussPairWeight p :=
  mul_pos (gaussWeight_pos _) (gaussWeight_pos _)

theorem gaussPairWeight_nonneg (p : E d × E d) : 0 ≤ gaussPairWeight p :=
  (gaussPairWeight_pos p).le

theorem continuous_gaussWeight : Continuous (gaussWeight : E d → ℝ) :=
  Real.continuous_exp.comp ((continuous_norm.pow 2).div_const 2).neg

theorem continuous_gaussPairWeight : Continuous (gaussPairWeight : E d × E d → ℝ) :=
  (continuous_gaussWeight.comp continuous_fst).mul (continuous_gaussWeight.comp continuous_snd)

theorem contDiff_gaussWeight {n : WithTop ℕ∞} : ContDiff ℝ n (gaussWeight : E d → ℝ) :=
  Real.contDiff_exp.comp ((contDiff_norm_sq ℝ).div_const 2).neg

/-- The derivative of the Gaussian weight: `Dφ(x) v = -φ(x) ⟨x, v⟩`. -/
theorem hasFDerivAt_gaussWeight (x : E d) :
    HasFDerivAt gaussWeight (-gaussWeight x • innerSL ℝ x) x := by
  have h0 : HasFDerivAt (fun x : E d ↦ ‖x‖ ^ 2) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have h := (h0.mul_const (1 / 2 : ℝ)).neg.exp
  convert h using 1
  · funext y
    simp only [gaussWeight, Pi.neg_apply]
    ring_nf
  · ext v
    simp [gaussWeight, innerSL_apply_apply, two_smul]
    ring_nf

theorem fderiv_gaussWeight_apply (x v : E d) :
    fderiv ℝ gaussWeight x v = -gaussWeight x * inner ℝ x v := by
  rw [(hasFDerivAt_gaussWeight x).fderiv]
  simp [innerSL_apply_apply]

/-- `e^{-|x|²/4}` is integrable on `ℝᵈ`. -/
theorem integrable_exp_neg_norm_sq_div_four :
    Integrable (fun x : E d ↦ Real.exp (-(‖x‖ ^ 2 / 4))) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (show 0 < ((1 / 4 : ℝ) : ℂ).re by simp) 0 (0 : E d)).norm
  refine h.congr (Eventually.of_forall fun x ↦ ?_)
  simp only [Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]
  ring

/-- `(1 + |x|²) e^{-|x|²/2} ≤ 4 e^{-|x|²/4}`. -/
theorem one_add_sq_mul_gaussWeight_le (x : E d) :
    (1 + ‖x‖ ^ 2) * gaussWeight x ≤ 4 * Real.exp (-(‖x‖ ^ 2 / 4)) := by
  have h1 : ‖x‖ ^ 2 / 4 + 1 ≤ Real.exp (‖x‖ ^ 2 / 4) := Real.add_one_le_exp _
  have h2 : gaussWeight x = Real.exp (-(‖x‖ ^ 2 / 4)) * Real.exp (-(‖x‖ ^ 2 / 4)) := by
    rw [gaussWeight, ← Real.exp_add]; ring_nf
  have h3 : Real.exp (‖x‖ ^ 2 / 4) * Real.exp (-(‖x‖ ^ 2 / 4)) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (-(‖x‖ ^ 2 / 4))
  rw [h2]
  nlinarith [mul_le_mul_of_nonneg_right h1 hpos.le]

theorem integrable_one_add_sq_mul_gaussWeight :
    Integrable (fun x : E d ↦ (1 + ‖x‖ ^ 2) * gaussWeight x) := by
  refine (integrable_exp_neg_norm_sq_div_four.const_mul 4).mono'
    ((continuous_const.add (continuous_norm.pow 2)).mul
      continuous_gaussWeight).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (gaussWeight_nonneg x))]
  exact one_add_sq_mul_gaussWeight_le x

/-- A function of quadratic growth is integrable against the Gaussian weight. -/
theorem integrable_mul_gaussWeight {f : E d → ℝ} (hf : AEStronglyMeasurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C * (1 + ‖x‖ ^ 2)) : Integrable (fun x ↦ f x * gaussWeight x) := by
  refine (integrable_one_add_sq_mul_gaussWeight.const_mul C).mono'
    (hf.mul continuous_gaussWeight.aestronglyMeasurable) (Eventually.of_forall fun x ↦ ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (gaussWeight_nonneg x), ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hC x) (gaussWeight_nonneg x)

theorem integrable_gaussWeight : Integrable (gaussWeight : E d → ℝ) := by
  simpa using integrable_mul_gaussWeight (f := fun _ : E d ↦ (1 : ℝ))
    aestronglyMeasurable_const (C := 1) fun x ↦ by simp

theorem gaussMass_pos (d : ℕ) : 0 < gaussMass d := by
  rw [gaussMass, integral_pos_iff_support_of_nonneg gaussWeight_nonneg integrable_gaussWeight]
  have : Function.support (gaussWeight : E d → ℝ) = univ :=
    eq_univ_of_forall fun x ↦ (gaussWeight_pos x).ne'
  rw [this]
  exact NeZero.pos _

/-- A function on `ℝᵈ × ℝᵈ` of growth `(1 + |x|²)(1 + |y|²)` is integrable against the product
weight. -/
theorem integrable_mul_gaussPairWeight {f : E d × E d → ℝ} (hf : AEStronglyMeasurable f) {C : ℝ}
    (hC : ∀ p : E d × E d, |f p| ≤ C * ((1 + ‖p.1‖ ^ 2) * (1 + ‖p.2‖ ^ 2))) :
    Integrable (fun p ↦ f p * gaussPairWeight p) := by
  have hint := (integrable_one_add_sq_mul_gaussWeight (d := d)).mul_prod
    (integrable_one_add_sq_mul_gaussWeight (d := d))
  refine (hint.const_mul C).mono'
    (hf.mul continuous_gaussPairWeight.aestronglyMeasurable) (Eventually.of_forall fun p ↦ ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (gaussPairWeight_nonneg p)]
  calc |f p| * gaussPairWeight p
      ≤ C * ((1 + ‖p.1‖ ^ 2) * (1 + ‖p.2‖ ^ 2)) * gaussPairWeight p :=
        mul_le_mul_of_nonneg_right (hC p) (gaussPairWeight_nonneg p)
    _ = C * ((1 + ‖p.1‖ ^ 2) * gaussWeight p.1 * ((1 + ‖p.2‖ ^ 2) * gaussWeight p.2)) := by
        rw [gaussPairWeight]; ring

/-! ### Rotation invariance -/

/-- Change of variables `x ↦ r x` for lower integrals on `ℝᵈ`. -/
theorem lintegral_comp_smul_of_ne_zero {r : ℝ} (hr : r ≠ 0) (f : E d → ℝ≥0∞) :
    ∫⁻ x, f (r • x) = ENNReal.ofReal |(r ^ d)⁻¹| * ∫⁻ x, f x := by
  calc ∫⁻ x, f (r • x) = ∫⁻ y, f y ∂Measure.map (fun x : E d ↦ r • x) volume :=
        (lintegral_map_equiv f
          (Homeomorph.smul (isUnit_iff_ne_zero.2 hr).unit).toMeasurableEquiv).symm
    _ = _ := by
        rw [Measure.map_addHaar_smul volume hr, lintegral_smul_measure, finrank_euclideanSpace_fin,
          smul_eq_mul]

/-- The completed square behind rotation invariance. -/
theorem gaussWeight_mul_gaussWeight_eq {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (x u : E d) :
    gaussWeight x * gaussWeight (s⁻¹ • (u - c • x)) =
      gaussWeight u * gaussWeight (s⁻¹ • (x - c • u)) := by
  simp only [gaussWeight, ← Real.exp_add]
  congr 1
  have key : ‖x‖ ^ 2 + ‖s⁻¹ • (u - c • x)‖ ^ 2 = ‖u‖ ^ 2 + ‖s⁻¹ • (x - c • u)‖ ^ 2 := by
    simp only [norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, inv_pow, sq_abs]
    rw [@norm_sub_sq_real, @norm_sub_sq_real, norm_smul, norm_smul, inner_smul_right,
      inner_smul_right, real_inner_comm u x]
    simp only [mul_pow, Real.norm_eq_abs, sq_abs]
    field_simp
    linear_combination (‖x‖ ^ 2 - ‖u‖ ^ 2) * hcs
  linarith

/-- The lower integral of `e^{-|(x - a)/s|²/2}` is `|s|ᵈ gaussMass d`. -/
theorem lintegral_gaussWeight_inv_smul_sub {s : ℝ} (hs : s ≠ 0) (a : E d) :
    ∫⁻ x, ENNReal.ofReal (gaussWeight (s⁻¹ • (x - a))) =
      ENNReal.ofReal (|s| ^ d) * ENNReal.ofReal (gaussMass d) := by
  have h1 : ∫⁻ x, ENNReal.ofReal (gaussWeight (s⁻¹ • (x - a))) =
      ∫⁻ x : E d, ENNReal.ofReal (gaussWeight (s⁻¹ • x)) := by
    have := lintegral_add_left_eq_self (μ := (volume : Measure (E d)))
      (fun x : E d ↦ ENNReal.ofReal (gaussWeight (s⁻¹ • x))) (-a)
    simpa [neg_add_eq_sub] using this
  rw [h1, lintegral_comp_smul_of_ne_zero (inv_ne_zero hs)
    (fun x : E d ↦ ENNReal.ofReal (gaussWeight x)), gaussMass,
    ofReal_integral_eq_lintegral_ofReal integrable_gaussWeight
      (Eventually.of_forall gaussWeight_nonneg)]
  congr 2
  rw [inv_pow, inv_inv, abs_pow]

/-- **Rotation invariance of the Gaussian.** If `c² + s² = 1` and `s ≠ 0`, then for every
measurable `h ≥ 0`,
`∫∫ h(c x + s y) e^{-(|x|²+|y|²)/2} dx dy = gaussMass d · ∫ h(x) e^{-|x|²/2} dx`. -/
theorem lintegral_comp_add_smul_gaussPairWeight {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    {h : E d → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ p : E d × E d, h (c • p.1 + s • p.2) * ENNReal.ofReal (gaussPairWeight p) =
      ENNReal.ofReal (gaussMass d) * ∫⁻ x, h x * ENNReal.ofReal (gaussWeight x) := by
  have hφ : Measurable (fun x : E d ↦ ENNReal.ofReal (gaussWeight x)) :=
    ENNReal.measurable_ofReal.comp continuous_gaussWeight.measurable
  have hmeas : Measurable fun p : E d × E d ↦
      h (c • p.1 + s • p.2) * ENNReal.ofReal (gaussPairWeight p) :=
    (hh.comp (by fun_prop)).mul (ENNReal.measurable_ofReal.comp
      continuous_gaussPairWeight.measurable)
  have hsd : ENNReal.ofReal |(s ^ d)⁻¹| * ENNReal.ofReal (|s| ^ d) = 1 := by
    rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_inv, abs_pow, inv_mul_cancel₀
      (pow_ne_zero _ (abs_ne_zero.2 hs)), ENNReal.ofReal_one]
  -- inner integral in `y`, after `y = s⁻¹ (u - c x)`
  have hinner : ∀ x : E d, ∫⁻ y, h (c • x + s • y) * ENNReal.ofReal (gaussWeight y) =
      ENNReal.ofReal |(s ^ d)⁻¹| *
        ∫⁻ u, h u * ENNReal.ofReal (gaussWeight (s⁻¹ • (u - c • x))) := by
    intro x
    have h1 := lintegral_comp_smul_of_ne_zero hs
      (fun z : E d ↦ h (c • x + z) * ENNReal.ofReal (gaussWeight (s⁻¹ • z)))
    simp only [smul_smul, inv_mul_cancel₀ hs, one_smul] at h1
    rw [h1]
    congr 1
    have h2 := lintegral_add_left_eq_self (μ := (volume : Measure (E d)))
      (fun u ↦ h u * ENNReal.ofReal (gaussWeight (s⁻¹ • (u - c • x)))) (c • x)
    simpa using h2
  calc ∫⁻ p : E d × E d, h (c • p.1 + s • p.2) * ENNReal.ofReal (gaussPairWeight p)
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (gaussWeight x) *
          (h (c • x + s • y) * ENNReal.ofReal (gaussWeight y)) := by
        rw [Measure.volume_eq_prod, lintegral_prod _ hmeas.aemeasurable]
        refine lintegral_congr fun x ↦ lintegral_congr fun y ↦ ?_
        simp only [gaussPairWeight, ENNReal.ofReal_mul (gaussWeight_nonneg _)]
        ring
    _ = ∫⁻ x, ENNReal.ofReal |(s ^ d)⁻¹| * ∫⁻ u, h u * (ENNReal.ofReal (gaussWeight x) *
          ENNReal.ofReal (gaussWeight (s⁻¹ • (u - c • x)))) := by
        refine lintegral_congr fun x ↦ ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hinner x, ← mul_assoc,
          mul_comm (ENNReal.ofReal (gaussWeight x)), mul_assoc,
          ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        refine lintegral_congr fun u ↦ ?_
        ring
    _ = ENNReal.ofReal |(s ^ d)⁻¹| * ∫⁻ x, ∫⁻ u, h u * (ENNReal.ofReal (gaussWeight u) *
          ENNReal.ofReal (gaussWeight (s⁻¹ • (x - c • u)))) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        refine lintegral_congr fun x ↦ lintegral_congr fun u ↦ ?_
        rw [← ENNReal.ofReal_mul (gaussWeight_nonneg _),
          ← ENNReal.ofReal_mul (gaussWeight_nonneg _), gaussWeight_mul_gaussWeight_eq hcs hs]
    _ = ENNReal.ofReal |(s ^ d)⁻¹| * ∫⁻ u, h u * ENNReal.ofReal (gaussWeight u) *
          ∫⁻ x, ENNReal.ofReal (gaussWeight (s⁻¹ • (x - c • u))) := by
        congr 1
        rw [lintegral_lintegral_swap ((hh.comp measurable_snd).mul ((hφ.comp measurable_snd).mul
            (hφ.comp (by fun_prop)))).aemeasurable]
        refine lintegral_congr fun u ↦ ?_
        have hm : Measurable fun x : E d ↦ ENNReal.ofReal (gaussWeight (s⁻¹ • (x - c • u))) :=
          hφ.comp (by fun_prop)
        rw [← lintegral_const_mul (h u * ENNReal.ofReal (gaussWeight u)) hm]
        exact lintegral_congr fun x ↦ by ring
    _ = _ := by
        simp_rw [lintegral_gaussWeight_inv_smul_sub hs]
        rw [lintegral_mul_const' _ _
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
          mul_comm (∫⁻ _, _) _, ← mul_assoc, ← mul_assoc, hsd, one_mul]

/-- **Rotation invariance**, Bochner form for nonnegative measurable `f`. -/
theorem integral_comp_add_smul_gaussPairWeight {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    {f : E d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) :
    ∫ p : E d × E d, f (c • p.1 + s • p.2) * gaussPairWeight p =
      gaussMass d * ∫ x, f x * gaussWeight x := by
  have h := lintegral_comp_add_smul_gaussPairWeight hcs hs (ENNReal.measurable_ofReal.comp hf)
  rw [integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun p ↦ mul_nonneg (hf0 _) (gaussPairWeight_nonneg p))
      ((hf.comp (by fun_prop)).mul continuous_gaussPairWeight.measurable).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun x ↦ mul_nonneg (hf0 _) (gaussWeight_nonneg x))
      (hf.mul continuous_gaussWeight.measurable).aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_mul (hf0 _)]
  simp only [Function.comp_apply] at h
  rw [h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (gaussMass_pos d).le]

/-- The map `(x, y) ↦ c x + s y` (`c² + s² = 1`, `s ≠ 0`) pulls Lebesgue-null sets back to
Lebesgue-null sets of `ℝᵈ × ℝᵈ`. -/
theorem measure_preimage_add_smul_eq_zero {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    {N : Set (E d)} (hN : volume N = 0) :
    volume {p : E d × E d | c • p.1 + s • p.2 ∈ N} = 0 := by
  set M := toMeasurable volume N
  have hM : MeasurableSet M := measurableSet_toMeasurable _ _
  have hM0 : volume M = 0 := by rw [measure_toMeasurable]; exact hN
  have hmeas : Measurable fun p : E d × E d ↦ c • p.1 + s • p.2 := by fun_prop
  have h := lintegral_comp_add_smul_gaussPairWeight hcs hs (measurable_one.indicator hM)
  have h0 : ∫⁻ x, M.indicator 1 x * ENNReal.ofReal (gaussWeight x) = 0 := by
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hM0] with x hx
    simp [hx]
  have hm2 : Measurable fun p : E d × E d ↦
      M.indicator 1 (c • p.1 + s • p.2) * ENNReal.ofReal (gaussPairWeight p) :=
    ((measurable_one.indicator hM).comp hmeas).mul
      (ENNReal.measurable_ofReal.comp continuous_gaussPairWeight.measurable)
  rw [h0, mul_zero, lintegral_eq_zero_iff hm2] at h
  refine measure_mono_null (t := {p : E d × E d | c • p.1 + s • p.2 ∈ M})
    (fun p hp ↦ subset_toMeasurable volume N hp) ?_
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [h] with p hp hpM
  have : M.indicator 1 (c • p.1 + s • p.2) * ENNReal.ofReal (gaussPairWeight p) = 0 := hp
  simp only [indicator_of_mem hpM, Pi.one_apply, one_mul, ENNReal.ofReal_eq_zero] at this
  exact (gaussPairWeight_pos p).not_ge this

end EllipticBernoulli
