/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.Sobolev
public import EllipticBernoulli.Sobolev.L2Inner
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Group.Integral

/-!
# `L²` translation estimate for functions with an `L²` weak gradient

If `w ∈ L²(ℝᵈ)` has a weak gradient `Γ ∈ L²(ℝᵈ; ℝᵈ)` on the whole space, then
`‖w(· + h) - w‖₂ ≤ |h| ‖Γ‖₂`.

Proof by duality, without mollifying `w`: for a test function `φ`, the function
`F(t) = ∫ w(y) φ(y - t h) dy` has derivative `F'(t) = ∫ ⟨Γ, h⟩ φ(· - t h)` (differentiation under
the integral sign, then the weak-gradient identity with the test function `φ(· - t h)`), so
`|∫ (w(· + h) - w) φ| = |F(1) - F(0)| ≤ |h| ‖Γ‖₂ ‖φ‖₂`; then approximate `w(· + h) - w` itself in
`L²` by test functions (`exist_eLpNorm_sub_le`).

## Main results

* `hasDerivAt_integral_mul_comp_sub_smul`: differentiation of `t ↦ ∫ w(y) φ(y - t h) dy`.
* `eLpNorm_comp_add_sub_le_of_weakGradient`: the translation estimate.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal ContDiff

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- **Differentiation of a translated pairing.** For `w` locally integrable and `φ ∈ C¹_c`,
`t ↦ ∫ w(y) φ(y - t h) dy` has derivative `∫ w(y) (-Dφ(y - t h) h) dy`. -/
theorem hasDerivAt_integral_mul_comp_sub_smul {w : E d → ℝ} (hw : LocallyIntegrable w)
    {φ : E d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (h : E d) (t₀ : ℝ) :
    HasDerivAt (fun t : ℝ ↦ ∫ y, w y * φ (y - t • h))
      (∫ y, w y * -(fderiv ℝ φ (y - t₀ • h) h)) t₀ := by
  obtain ⟨C, hC⟩ := (hφ.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hφc.fderiv (𝕜 := ℝ))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set S := cthickening (‖h‖ * (|t₀| + 1)) (tsupport φ)
  have hS : IsCompact S := hφc.isCompact.cthickening
  have hmemS : ∀ y (t : ℝ), t ∈ ball t₀ 1 → y - t • h ∈ tsupport φ → y ∈ S := by
    intro y t ht hy
    refine mem_cthickening_of_dist_le y _ _ _ hy ?_
    rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs, mul_comm]
    have h1 := abs_sub_abs_le_abs_sub t t₀
    rw [mem_ball, Real.dist_eq] at ht
    gcongr
    linarith
  have hwS : IntegrableOn w S := hw.integrableOn_isCompact hS
  have hφt : ∀ t : ℝ, Continuous fun y ↦ φ (y - t • h) :=
    fun t ↦ hφ.continuous.comp (continuous_id.sub continuous_const)
  have hφtc : ∀ t : ℝ, HasCompactSupport fun y ↦ φ (y - t • h) :=
    fun t ↦ hφc.comp_homeomorph (Homeomorph.subRight (t • h))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t y ↦ w y * φ (y - t • h)) (F' := fun t y ↦ w y * -(fderiv ℝ φ (y - t • h) h))
    (bound := S.indicator fun y ↦ ‖w y‖ * (C * ‖h‖)) (ball_mem_nhds t₀ one_pos)
    (Eventually.of_forall fun t ↦
      hw.aestronglyMeasurable.mul (hφt t).aestronglyMeasurable) ?_ ?_ ?_ ?_ ?_).2
  · have := hw.integrable_smul_right_of_hasCompactSupport (hφt t₀) (hφtc t₀)
    simpa only [smul_eq_mul] using this
  · refine hw.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable ?_)
    exact (((hφ.continuous_fderiv one_ne_zero).comp (continuous_id.sub continuous_const)).clm_apply
      continuous_const).neg
  · refine Eventually.of_forall fun y t ht ↦ ?_
    by_cases hy : y - t • h ∈ tsupport φ
    · rw [indicator_of_mem (hmemS y t ht hy), norm_mul, norm_neg]
      gcongr
      exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hC _)
    · have h0 : fderiv ℝ φ (y - t • h) = 0 :=
        image_eq_zero_of_notMem_tsupport fun hh ↦ hy (tsupport_fderiv_subset ℝ hh)
      rw [h0]
      simp only [zero_apply, neg_zero, mul_zero, norm_zero]
      exact indicator_nonneg (fun _ _ ↦ by positivity) _
  · rw [integrable_indicator_iff hS.measurableSet]
    exact (hwS.norm.mul_const _)
  · refine Eventually.of_forall fun y t _ ↦ ?_
    have h1 : HasDerivAt (fun s : ℝ ↦ y - s • h) (-h) t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_sub y
    have h2 := ((hφ.differentiable one_ne_zero) (y - t • h)).hasFDerivAt.comp_hasDerivAt t h1
    have h3 := h2.const_mul (w y)
    simpa only [Function.comp_def, ContinuousLinearMap.map_neg] using h3

/-- A function `w` with weak gradient `Γ` on the whole space (tested against `C^∞_c`). -/
def HasWeakGradientUniv (w : E d → ℝ) (Γ : E d → E d) : Prop :=
  ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ v : E d,
    ∫ x, w x * fderiv ℝ φ x v = -∫ x, inner ℝ (Γ x) v * φ x

/-- The pairing bound: `|∫ (w(· + h) - w) φ| ≤ |h| ‖Γ‖₂ ‖φ‖₂` for test functions `φ`. -/
theorem abs_integral_comp_add_sub_mul_le {w : E d → ℝ} {Γ : E d → E d} (hw : MemLp w 2 volume)
    (hΓ : MemLp Γ 2 volume) (hwg : HasWeakGradientUniv w Γ) (h : E d) {φ : E d → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    |∫ x, (w (x + h) - w x) * φ x| ≤
      ‖h‖ * (eLpNorm Γ 2 volume).toReal * (eLpNorm φ 2 volume).toReal := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hφc
  have hwh : MemLp (fun x ↦ w (x + h)) 2 volume :=
    hw.comp_measurePreserving (measurePreserving_add_right volume h)
  have hwl : LocallyIntegrable w volume := hw.locallyIntegrable (by norm_num)
  set F : ℝ → ℝ := fun t ↦ ∫ y, w y * φ (y - t • h) with hF
  -- the pairing is `F 1 - F 0`
  have hpair : ∫ x, (w (x + h) - w x) * φ x = F 1 - F 0 := by
    have i1 : Integrable (fun x ↦ w (x + h) * φ x) volume := hwh.integrable_mul hφ2
    have i2 : Integrable (fun x ↦ w x * φ x) volume := hw.integrable_mul hφ2
    have e1 : ∫ x, w (x + h) * φ x = ∫ y, w y * φ (y - h) := by
      rw [← integral_sub_right_eq_self (fun x ↦ w (x + h) * φ x) h]
      simp only [sub_add_cancel]
    simp only [hF, one_smul, zero_smul, sub_zero, sub_mul]
    rw [integral_sub i1 i2, e1]
  -- the derivative of `F`
  have hderiv : ∀ t : ℝ, HasDerivAt F (∫ y, inner ℝ (Γ y) h * φ (y - t • h)) t := by
    intro t
    have hd := hasDerivAt_integral_mul_comp_sub_smul hwl hφ1 hφc h t
    convert hd using 1
    have hφt : ContDiff ℝ ∞ fun y ↦ φ (y - t • h) :=
      hφ.comp (contDiff_id.sub contDiff_const)
    have hφtc : HasCompactSupport fun y ↦ φ (y - t • h) :=
      hφc.comp_homeomorph (Homeomorph.subRight (t • h))
    have hw' := hwg _ hφt hφtc h
    simp only [fderiv_comp_sub] at hw'
    simp only [mul_neg, integral_neg, hw', neg_neg]
  -- the derivative bound
  have hbound : ∀ t : ℝ, ‖∫ y, inner ℝ (Γ y) h * φ (y - t • h)‖ ≤
      ‖h‖ * (eLpNorm Γ 2 volume).toReal * (eLpNorm φ 2 volume).toReal := by
    intro t
    have hmp := measurePreserving_sub_right (volume : Measure (E d)) (t • h)
    have hφt2 : MemLp (fun y ↦ φ (y - t • h)) 2 volume := hφ2.comp_measurePreserving hmp
    have hΓh : MemLp (fun y ↦ inner ℝ (Γ y) h) 2 volume :=
      hΓ.inner_const h
    have hΓhle : eLpNorm (fun y ↦ inner ℝ (Γ y) h) 2 volume ≤
        ENNReal.ofReal ‖h‖ * eLpNorm Γ 2 volume :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul hΓh.aestronglyMeasurable (Eventually.of_forall fun y ↦ by
        rw [mul_comm]; exact norm_inner_le_norm _ _) 2
    have hφeq : eLpNorm (fun y ↦ φ (y - t • h)) 2 volume = eLpNorm φ 2 volume :=
      eLpNorm_comp_measurePreserving hφ2.aestronglyMeasurable hmp
    rw [Real.norm_eq_abs]
    refine (abs_integral_mul_le_L2 hΓh hφt2).trans ?_
    rw [hφeq]
    gcongr
    calc (eLpNorm (fun y ↦ inner ℝ (Γ y) h) 2 volume).toReal
        ≤ (ENNReal.ofReal ‖h‖ * eLpNorm Γ 2 volume).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΓ.eLpNorm_ne_top)
            hΓhle
      _ = ‖h‖ * (eLpNorm Γ 2 volume).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := F) (a := 0) (b := 1)
    (fun t _ ↦ (hderiv t).hasDerivWithinAt) (fun t _ ↦ hbound t) 1 (by simp)
  rw [hpair, ← Real.norm_eq_abs]
  simpa using hmvt

/-- **`L²` translation estimate.** If `w ∈ L²(ℝᵈ)` has weak gradient `Γ ∈ L²(ℝᵈ)` on the whole
space, then `‖w(· + h) - w‖₂ ≤ |h| ‖Γ‖₂`. -/
theorem eLpNorm_comp_add_sub_le_of_weakGradient {w : E d → ℝ} {Γ : E d → E d}
    (hw : MemLp w 2 volume) (hΓ : MemLp Γ 2 volume) (hwg : HasWeakGradientUniv w Γ) (h : E d) :
    eLpNorm (fun x ↦ w (x + h) - w x) 2 volume ≤
      ENNReal.ofReal ‖h‖ * eLpNorm Γ 2 volume := by
  set g : E d → ℝ := fun x ↦ w (x + h) - w x with hg
  have hg2 : MemLp g 2 volume :=
    (hw.comp_measurePreserving (measurePreserving_add_right volume h)).sub hw
  set a := (eLpNorm g 2 volume).toReal with ha
  set B := ‖h‖ * (eLpNorm Γ 2 volume).toReal with hB
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hB0 : 0 ≤ B := by positivity
  -- `a² = ∫ g g`
  have hsq : ∫ x, g x * g x = a ^ 2 := by
    have := integral_inner_eq_L2 hg2 hg2
    simp only [Real.inner_apply] at this
    rw [this, real_inner_self_eq_norm_sq, Lp.norm_toLp]
  have hkey : ∀ ε > 0, a ^ 2 ≤ B * a + ε * (B + a) := by
    intro ε hε
    obtain ⟨φ, hφc, hφ, hgφ⟩ := hg2.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hε
    have hφ2 : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hφc
    have hgφ2 : MemLp (g - φ) 2 volume := hg2.sub hφ2
    have hgφr : (eLpNorm (g - φ) 2 volume).toReal ≤ ε :=
      ENNReal.toReal_le_of_le_ofReal hε.le hgφ
    have hφle : (eLpNorm φ 2 volume).toReal ≤ a + ε := by
      have : eLpNorm φ 2 volume ≤ eLpNorm g 2 volume + eLpNorm (g - φ) 2 volume := by
        have e : φ = g - (g - φ) := by abel
        conv_lhs => rw [e]
        exact eLpNorm_sub_le (by norm_num)
      have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hg2.eLpNorm_ne_top,
        hgφ2.eLpNorm_ne_top⟩) this
      rw [ENNReal.toReal_add hg2.eLpNorm_ne_top hgφ2.eLpNorm_ne_top] at this
      linarith
    have h1 := abs_integral_comp_add_sub_mul_le hw hΓ hwg h hφ hφc
    have h2 := abs_integral_mul_le_L2 hg2 hgφ2
    have hsplit : ∫ x, g x * g x = (∫ x, g x * φ x) + ∫ x, g x * (g - φ) x := by
      have := integral_add (hg2.integrable_mul hφ2) (hg2.integrable_mul hgφ2)
      simp only [Pi.mul_apply] at this
      rw [← this]
      congr 1; funext x; simp only [Pi.sub_apply]; ring
    have h1' : ∫ x, g x * φ x ≤ B * (a + ε) := by
      refine (le_abs_self _).trans (h1.trans ?_)
      rw [hB]
      gcongr
    have h2' : ∫ x, g x * (g - φ) x ≤ a * ε := by
      refine (le_abs_self _).trans (h2.trans ?_)
      gcongr
    have e : B * (a + ε) + a * ε = B * a + ε * (B + a) := by ring
    linarith
  have hfin : a ≤ B := by
    have hle : a ^ 2 ≤ B * a := by
      refine le_of_forall_pos_le_add fun ε hε ↦ ?_
      have := hkey (ε / (B + a + 1)) (by positivity)
      have hfrac : ε / (B + a + 1) * (B + a) ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    rcases ha0.lt_or_eq with hpos | hzero
    · nlinarith
    · rw [← hzero]; exact hB0
  calc eLpNorm g 2 volume = ENNReal.ofReal a := (ENNReal.ofReal_toReal hg2.eLpNorm_ne_top).symm
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hfin
    _ = ENNReal.ofReal ‖h‖ * eLpNorm Γ 2 volume := by
        rw [hB, ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_toReal hΓ.eLpNorm_ne_top]

end EllipticBernoulli
