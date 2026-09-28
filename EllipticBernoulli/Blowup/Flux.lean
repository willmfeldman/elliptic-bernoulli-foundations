/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Variational
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The flux condition across the free line

Let `(v, χ)` be an inner variational solution in `ℝ²` with constant coefficient `q`, where
`v = a (y·e)₊ + b (y·e)₋` for a unit vector `e`, and `χ = 1` a.e. on `{y·e > 0}` and `χ = c` a.e. on
`{y·e < 0}`. Then the normal components of the constant stress tensors
`T = (|∇v|² + q²χ) I − 2 ∇v ⊗ ∇v` on the two sides agree:
`q² − a² = q² c − b²` (`IsInnerVarSolution.flux_eq`).

## Proof

Test the inner variation identity with `ξ(y) = φ(y) e`, where `φ(y) = ψ(1 − |y|²)` and
`ψ = expNegInvGlue`. With `F = ∂_e φ`, the integrand is `(q² − a²) F` on `{y·e > 0}` and
`(q² c − b²) F` on `{y·e < 0}`, and the line `{y·e = 0}` is null. `φ` is even, so `F` is odd and
`∫_{y·e<0} F = −∫_{y·e>0} F`; and `F ≤ 0` on `{y·e > 0}`, strictly somewhere, so `∫_{y·e>0} F < 0`.
No Fubini or trace on the line is needed.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient RealInnerProductSpace ContDiff

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- A hyperplane `{x · e = 0}`, `e ≠ 0`, is Lebesgue-null. -/
theorem volume_inner_eq_zero {e : E d} (he : e ≠ 0) :
    volume {x : E d | inner ℝ x e = 0} = 0 := by
  have hs : LinearMap.ker ((innerSL ℝ e : E d →L[ℝ] ℝ) : E d →ₗ[ℝ] ℝ) ≠ ⊤ := by
    intro h
    have : e ∈ LinearMap.ker ((innerSL ℝ e : E d →L[ℝ] ℝ) : E d →ₗ[ℝ] ℝ) := h ▸ Submodule.mem_top
    simp [he] at this
  have := Measure.addHaar_submodule volume _ hs
  convert this using 2
  ext x
  simp [real_inner_comm]

/-- If `f` agrees near `y` with the linear function `⟪g, ·⟫`, then `∇f(y) = g`. -/
theorem gradient_eq_of_eventuallyEq_inner {f : E d → ℝ} {y g : E d}
    (h : f =ᶠ[𝓝 y] fun z ↦ ⟪g, z⟫) : ∇ f y = g := by
  have hg : HasGradientAt f g y := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have := (innerSL ℝ g).hasFDerivAt (x := y)
    refine this.congr_of_eventuallyEq ?_ |>.congr_fderiv ?_
    · filter_upwards [h] with z hz
      simp [hz]
    · ext w
      simp
  exact hg.gradient

namespace PlanarFlux

/-- The even bump `φ(y) = ψ(1 − |y|²)`, `ψ = expNegInvGlue`. -/
noncomputable def bump (y : E 2) : ℝ := expNegInvGlue (1 - ‖y‖ ^ 2)

theorem contDiff_bump : ContDiff ℝ ∞ bump :=
  expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

theorem hasCompactSupport_bump : HasCompactSupport bump := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : E 2) 1) fun y hy ↦ ?_
  rw [mem_closedBall_zero_iff, not_le] at hy
  refine expNegInvGlue.zero_of_nonpos ?_
  nlinarith [norm_nonneg y]

theorem fderiv_bump_apply (y w : E 2) :
    fderiv ℝ bump y w = deriv expNegInvGlue (1 - ‖y‖ ^ 2) * (-(2 * ⟪y, w⟫)) := by
  have hg : HasDerivAt expNegInvGlue (deriv expNegInvGlue (1 - ‖y‖ ^ 2)) (1 - ‖y‖ ^ 2) :=
    ((expNegInvGlue.contDiff (n := 1)).differentiable (by norm_num) _).hasDerivAt
  have hn : HasFDerivAt (fun z : E 2 ↦ 1 - ‖z‖ ^ 2) (-(2 • innerSL ℝ y)) y :=
    ((hasStrictFDerivAt_norm_sq y).hasFDerivAt).const_sub 1
  have := hg.comp_hasFDerivAt y hn
  rw [show bump = expNegInvGlue ∘ fun z : E 2 ↦ 1 - ‖z‖ ^ 2 from rfl, this.fderiv]
  simp [smul_eq_mul]

/-- The test field `ξ = φ e`. -/
noncomputable def field (e : E 2) (y : E 2) : E 2 := bump y • e

theorem contDiff_field (e : E 2) : ContDiff ℝ ∞ (field e) :=
  contDiff_bump.smul contDiff_const

theorem hasCompactSupport_field (e : E 2) : HasCompactSupport (field e) :=
  hasCompactSupport_bump.smul_right

theorem fderiv_field_apply (e y w : E 2) :
    fderiv ℝ (field e) y w = fderiv ℝ bump y w • e := by
  have hd : DifferentiableAt ℝ bump y := (contDiff_bump.differentiable (by simp)) y
  rw [show field e = fun y ↦ bump y • e from rfl, fderiv_smul_const hd]
  simp

theorem divergence_field (e y : E 2) : divergence (field e) y = fderiv ℝ bump y e := by
  have hd : DifferentiableAt ℝ bump y := (contDiff_bump.differentiable (by simp)) y
  rw [divergence, show field e = fun y ↦ bump y • e from rfl, fderiv_smul_const hd]
  exact LinearMap.trace_smulRight _ _

/-- `F = ∂_e φ`. -/
noncomputable def flux (e : E 2) (y : E 2) : ℝ := fderiv ℝ bump y e

theorem continuous_flux (e : E 2) : Continuous (flux e) :=
  (contDiff_bump.continuous_fderiv (by simp)).clm_apply continuous_const

theorem integrable_flux (e : E 2) : Integrable (flux e) := by
  refine (continuous_flux e).integrable_of_hasCompactSupport ?_
  refine (hasCompactSupport_bump.fderiv ℝ).mono ?_
  intro y hy h0
  exact hy (by simp [flux, h0])

theorem flux_neg (e y : E 2) : flux e (-y) = -flux e y := by
  simp only [flux, fderiv_bump_apply, norm_neg, inner_neg_left]
  ring

theorem flux_nonpos {e y : E 2} (hy : 0 < ⟪y, e⟫) : flux e y ≤ 0 := by
  rw [flux, fderiv_bump_apply]
  have := expNegInvGlue.monotone.deriv_nonneg (x := 1 - ‖y‖ ^ 2)
  nlinarith

theorem exists_flux_neg {e : E 2} (he : ‖e‖ = 1) : ∃ y, 0 < ⟪y, e⟫ ∧ flux e y < 0 := by
  obtain ⟨s, hs, hds⟩ := exists_deriv_eq_slope expNegInvGlue zero_lt_one
    (expNegInvGlue.contDiff (n := 0)).continuous.continuousOn
    ((expNegInvGlue.contDiff (n := 1)).differentiable (by norm_num)).differentiableOn
  rw [expNegInvGlue.zero, sub_zero, sub_zero, div_one] at hds
  have hpos : 0 < deriv expNegInvGlue s := hds ▸ expNegInvGlue.pos_of_pos one_pos
  have hs1 : 0 < 1 - s := by linarith [hs.2]
  refine ⟨√(1 - s) • e, ?_, ?_⟩
  · rw [real_inner_smul_left, real_inner_self_eq_norm_sq, he]
    simpa using Real.sqrt_pos.2 hs1
  · have hn : ‖√(1 - s) • e‖ ^ 2 = 1 - s := by
      rw [norm_smul, he, mul_one, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        Real.sq_sqrt hs1.le]
    have hi : ⟪√(1 - s) • e, e⟫ = √(1 - s) := by
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, he]; simp
    rw [flux, fderiv_bump_apply, hn, hi, show 1 - (1 - s) = s by ring]
    have := Real.sqrt_pos.2 hs1
    nlinarith

/-- `∫_{y·e>0} ∂_e φ < 0`. -/
theorem integral_flux_pos_neg {e : E 2} (he : ‖e‖ = 1) :
    ∫ y, {y : E 2 | 0 < ⟪y, e⟫}.indicator (flux e) y < 0 := by
  set H := {y : E 2 | 0 < ⟪y, e⟫}
  have hHm : MeasurableSet H :=
    measurableSet_lt measurable_const (continuous_id.inner continuous_const).measurable
  have hint : Integrable (H.indicator fun y ↦ -flux e y) :=
    ((integrable_flux e).neg).indicator hHm
  have hnn : 0 ≤ H.indicator fun y ↦ -flux e y := by
    intro y
    by_cases hy : y ∈ H
    · simp only [indicator_of_mem hy, Pi.zero_apply]
      linarith [flux_nonpos (e := e) hy]
    · simp [indicator_of_notMem hy]
  have hpos : 0 < ∫ y, H.indicator (fun y ↦ -flux e y) y := by
    rw [integral_pos_iff_support_of_nonneg hnn hint]
    obtain ⟨y₁, hy₁, hF⟩ := exists_flux_neg he
    have hU : IsOpen (H ∩ {y | flux e y < 0}) :=
      (isOpen_lt continuous_const (continuous_id.inner continuous_const)).inter
        (isOpen_lt (continuous_flux e) continuous_const)
    refine lt_of_lt_of_le (hU.measure_pos volume ⟨y₁, hy₁, hF⟩) (measure_mono ?_)
    rintro y ⟨hy, hFy⟩
    rw [Function.mem_support, indicator_of_mem hy]
    exact neg_ne_zero.2 hFy.ne
  have : ∫ y, H.indicator (fun y ↦ -flux e y) y = -∫ y, H.indicator (flux e) y := by
    rw [← integral_neg]
    congr 1
    ext y
    by_cases hy : y ∈ H <;> simp [hy]
  linarith

/-- `∫_{y·e<0} ∂_e φ = −∫_{y·e>0} ∂_e φ`, since `φ` is even. -/
theorem integral_flux_neg_side (e : E 2) :
    ∫ y, {y : E 2 | ⟪y, e⟫ < 0}.indicator (flux e) y =
      -∫ y, {y : E 2 | 0 < ⟪y, e⟫}.indicator (flux e) y := by
  have hmp : MeasurePreserving (fun y : E 2 ↦ -y) volume volume :=
    (LinearIsometryEquiv.neg ℝ (E := E 2)).measurePreserving
  rw [← hmp.integral_comp (Homeomorph.neg (E 2)).measurableEmbedding, ← integral_neg]
  congr 1
  ext y
  by_cases hy : 0 < ⟪y, e⟫
  · have hy' : ⟪-y, e⟫ < 0 := by rw [inner_neg_left]; linarith
    simp [indicator_of_mem (show -y ∈ {y : E 2 | ⟪y, e⟫ < 0} from hy'),
      indicator_of_mem (show y ∈ {y : E 2 | 0 < ⟪y, e⟫} from hy), flux_neg]
  · have hy' : ¬ ⟪-y, e⟫ < 0 := by rw [inner_neg_left]; linarith
    simp [indicator_of_notMem (show -y ∉ {y : E 2 | ⟪y, e⟫ < 0} from hy'),
      indicator_of_notMem (show y ∉ {y : E 2 | 0 < ⟪y, e⟫} from hy)]

/-- The inner variation integrand for `ξ = φ e` at a point where `∇v = s e`. -/
theorem innerVarIntegrand_field {q s : ℝ} {v χ : E 2 → ℝ} {e y : E 2} (he : ‖e‖ = 1)
    (hg : ∇ v y = s • e) :
    innerVarIntegrand (fun _ ↦ q) v χ (field e) y = (q ^ 2 * χ y - s ^ 2) * flux e y := by
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  simp only [innerVarIntegrand, hg, divergence_field, fderiv_field_apply, norm_smul, he,
    Real.norm_eq_abs, map_smul, real_inner_smul_left, real_inner_smul_right, hee, flux,
    fderiv_const_apply, ContinuousLinearMap.zero_apply, zero_mul, add_zero, mul_one, sq_abs]
  ring

end PlanarFlux

open PlanarFlux in
/-- **The flux condition.** If `(v, χ)` is an inner variational solution in `ℝ²` with
constant coefficient `q`, `v = a (y·e)₊ + b (y·e)₋` with `‖e‖ = 1`, and `χ = 1` a.e. on
`{y·e > 0}` and `χ = c` a.e. on `{y·e < 0}`, then `q² − a² = q² c − b²`. -/
theorem IsInnerVarSolution.flux_eq {q a b c : ℝ} {v χ : E 2 → ℝ}
    (hv : IsInnerVarSolution univ (fun _ ↦ q) v χ) {e : E 2} (he : ‖e‖ = 1)
    (hvab : ∀ y, v y = a * max ⟪y, e⟫ 0 + b * max (-⟪y, e⟫) 0)
    (hχp : ∀ᵐ y, 0 < ⟪y, e⟫ → χ y = 1) (hχn : ∀ᵐ y, ⟪y, e⟫ < 0 → χ y = c) :
    q ^ 2 - a ^ 2 = q ^ 2 * c - b ^ 2 := by
  set Hp := {y : E 2 | 0 < ⟪y, e⟫}
  set Hn := {y : E 2 | ⟪y, e⟫ < 0}
  have hcont : Continuous fun y : E 2 ↦ ⟪y, e⟫ := continuous_id.inner continuous_const
  have hHp : MeasurableSet Hp := measurableSet_lt measurable_const hcont.measurable
  have hHn : MeasurableSet Hn := measurableSet_lt hcont.measurable measurable_const
  have he0 : e ≠ 0 := by rintro rfl; simp at he
  have hline : ∀ᵐ y : E 2, ⟪y, e⟫ ≠ 0 := by
    rw [ae_iff]
    simpa using volume_inner_eq_zero he0
  obtain ⟨K, hK⟩ := (contDiff_field e).lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_field e) (by simp)
  have hstat := hv.stationary (field e) ⟨K, hK⟩ (hasCompactSupport_field e) (subset_univ _)
  rw [Measure.restrict_univ] at hstat
  have hae : (fun y ↦ innerVarIntegrand (fun _ ↦ q) v χ (field e) y) =ᵐ[volume]
      fun y ↦ (q ^ 2 - a ^ 2) * Hp.indicator (flux e) y +
        (q ^ 2 * c - b ^ 2) * Hn.indicator (flux e) y := by
    filter_upwards [hχp, hχn, hline] with y h1 h2 h3
    rcases lt_or_gt_of_ne h3 with hy | hy
    · have hg : ∇ v y = (-b) • e := by
        refine gradient_eq_of_eventuallyEq_inner ?_
        filter_upwards [(isOpen_lt hcont continuous_const).mem_nhds hy] with z hz
        rw [hvab, max_eq_right (le_of_lt hz), max_eq_left (by linarith [show ⟪z, e⟫ < 0 from hz]),
          real_inner_smul_left, real_inner_comm]
        ring
      rw [innerVarIntegrand_field he hg, h2 hy, indicator_of_mem (show y ∈ Hn from hy),
        indicator_of_notMem (show y ∉ Hp from fun h ↦ by simp [Hp] at h; linarith)]
      ring
    · have hg : ∇ v y = a • e := by
        refine gradient_eq_of_eventuallyEq_inner ?_
        filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds hy] with z hz
        rw [hvab, max_eq_left (le_of_lt hz), max_eq_right (by linarith [show 0 < ⟪z, e⟫ from hz]),
          real_inner_smul_left, real_inner_comm]
        ring
      rw [innerVarIntegrand_field he hg, h1 hy, indicator_of_mem (show y ∈ Hp from hy),
        indicator_of_notMem (show y ∉ Hn from fun h ↦ by simp [Hn] at h; linarith)]
      ring
  rw [integral_congr_ae hae, integral_add, integral_const_mul, integral_const_mul,
    integral_flux_neg_side] at hstat
  · have hI := integral_flux_pos_neg he
    have : ((q ^ 2 - a ^ 2) - (q ^ 2 * c - b ^ 2)) *
        ∫ y, Hp.indicator (flux e) y = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hI.ne
  · exact ((integrable_flux e).indicator hHp).const_mul _
  · exact ((integrable_flux e).indicator hHn).const_mul _

end EllipticBernoulli
