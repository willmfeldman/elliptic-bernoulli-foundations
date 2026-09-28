/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.Sobolev
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Poincaré inequality outside a ball, for `C¹` functions vanishing far out

Let `v ∈ C¹(ℝᵈ)` vanish on `{|y - x| ≥ R'}` and let `0 < r ≤ R'`. Then
`∫_{|y - x| ≥ r} v² ≤ ((R' - r) R' / r)² ∫_{|y - x| ≥ r} |Dv|²`
(`lintegral_sq_compl_ball_le`).

Proof along rays, written with dilations centred at `x` instead of polar coordinates. With
`Λ = R'/r`, for `|y - x| ≥ r` the point `x + Λ (y - x)` lies outside `B_{R'}(x)`, so
`v(y) = -∫_1^Λ Dv(x + μ(y - x))(y - x) dμ` and, by Cauchy–Schwarz,
`v(y)² ≤ (Λ - 1) R'² ∫_1^Λ |Dv(x + μ(y - x))|² dμ` (`sq_le_integral_ray`). Integrate over
`|y - x| ≥ r` and exchange the integrals. For fixed `μ ≥ 1` the change of variables
`z = x + μ(y - x)` has Jacobian `μ^{-d} ≤ 1` and maps `{|y - x| ≥ r}` into itself
(`lintegral_compl_ball_comp_dilate_le`).
-/

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- **Cauchy–Schwarz on an interval.** `(∫_a^b g)² ≤ (b - a) ∫_a^b g²` for continuous `g`. -/
theorem sq_intervalIntegral_le {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hg : Continuous g) :
    (∫ t in a..b, g t) ^ 2 ≤ (b - a) * ∫ t in a..b, g t ^ 2 := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  have hba : 0 < b - a := sub_pos.2 hlt
  set I := ∫ t in a..b, g t with hI
  set J := ∫ t in a..b, g t ^ 2 with hJ
  set m := I / (b - a) with hm
  have hmI : m * (b - a) = I := div_mul_cancel₀ I hba.ne'
  have h0 : 0 ≤ ∫ t in a..b, (g t - m) ^ 2 :=
    intervalIntegral.integral_nonneg hab fun t _ ↦ sq_nonneg _
  have hexp : ∀ t, (g t - m) ^ 2 = (g t ^ 2 - 2 * m * g t) + m ^ 2 := fun t ↦ by ring
  have e : ∫ t in a..b, (g t - m) ^ 2 = J - 2 * m * I + m ^ 2 * (b - a) := by
    simp_rw [hexp]
    rw [intervalIntegral.integral_add
        ((by fun_prop : Continuous fun t ↦ g t ^ 2 - 2 * m * g t).intervalIntegrable a b)
        intervalIntegrable_const, intervalIntegral.integral_sub ((hg.pow 2).intervalIntegrable a b)
        ((by fun_prop : Continuous fun t ↦ 2 * m * g t).intervalIntegrable a b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [e] at h0
  have hm2 : m ^ 2 * (b - a) = m * I := by rw [← hmI]; ring
  have h1 : m * I ≤ J := by linarith
  have h2 : I ^ 2 = (b - a) * (m * I) := by rw [← hmI]; ring
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 hba.le

/-- **One ray.** If `v ∈ C¹` and `v(x + Λ(y - x)) = 0` with `Λ ≥ 1`, then
`v(y)² ≤ (Λ - 1) |y - x|² ∫_1^Λ |Dv(x + μ(y - x))|² dμ`. -/
theorem sq_le_integral_ray {v : E d → ℝ} (hv : ContDiff ℝ 1 v) (x y : E d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (h0 : v (x + Λ • (y - x)) = 0) :
    v y ^ 2 ≤ (Λ - 1) * (‖y - x‖ ^ 2 *
      ∫ μ in (1 : ℝ)..Λ, ‖fderiv ℝ v (x + μ • (y - x))‖ ^ 2) := by
  set γ : ℝ → E d := fun μ ↦ x + μ • (y - x) with hγdef
  have hγ : ∀ μ, HasDerivAt γ (y - x) μ := fun μ ↦ by
    have h1 := (HasDerivAt.smul_const (hasDerivAt_id μ) (y - x)).const_add x
    rw [one_smul] at h1
    exact h1
  have hvd : Differentiable ℝ v := hv.differentiable one_ne_zero
  have hfd : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  have hγc : Continuous γ := continuous_const.add (continuous_id.smul continuous_const)
  set g : ℝ → ℝ := fun μ ↦ fderiv ℝ v (γ μ) (y - x) with hgdef
  have hgc : Continuous g := (hfd.comp hγc).clm_apply continuous_const
  have hderiv : ∀ μ, HasDerivAt (fun μ ↦ v (γ μ)) (g μ) μ := fun μ ↦ by
    exact (hvd (γ μ)).hasFDerivAt.comp_hasDerivAt μ (hγ μ)
  have hftc : ∫ μ in (1 : ℝ)..Λ, g μ = v (γ Λ) - v (γ 1) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun μ _ ↦ hderiv μ) (hgc.intervalIntegrable _ _)
  have hγ1 : γ 1 = y := by simp [hγdef]
  have hγΛ : v (γ Λ) = 0 := h0
  rw [hγ1, hγΛ, zero_sub] at hftc
  have hvy : v y ^ 2 = (∫ μ in (1 : ℝ)..Λ, g μ) ^ 2 := by rw [hftc, neg_sq]
  rw [hvy]
  refine (sq_intervalIntegral_le hΛ hgc).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on hΛ ((hgc.pow 2).intervalIntegrable _ _)
    ((continuous_const.mul ((hfd.comp hγc).norm.pow 2)).intervalIntegrable _ _) fun μ _ ↦ ?_
  have hle : |g μ| ≤ ‖fderiv ℝ v (γ μ)‖ * ‖y - x‖ := by
    rw [← Real.norm_eq_abs]
    exact (fderiv ℝ v (γ μ)).le_opNorm (y - x)
  calc g μ ^ 2 = |g μ| ^ 2 := (sq_abs _).symm
    _ ≤ (‖fderiv ℝ v (γ μ)‖ * ‖y - x‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2
    _ = ‖y - x‖ ^ 2 * ‖fderiv ℝ v (γ μ)‖ ^ 2 := by ring

/-- **Dilations centred at `x`.** For `μ ≥ 1` and measurable `f ≥ 0`,
`∫_{|y - x| ≥ r} f(x + μ(y - x)) dy ≤ ∫_{|z - x| ≥ r} f(z) dz` (Jacobian `μ^{-d} ≤ 1`). -/
theorem lintegral_compl_ball_comp_dilate_le {f : E d → ℝ≥0∞} (hf : Measurable f) (x : E d)
    (r : ℝ) {μ : ℝ} (hμ : 1 ≤ μ) :
    ∫⁻ y in (ball x r)ᶜ, f (x + μ • (y - x)) ≤ ∫⁻ z in (ball x r)ᶜ, f z := by
  have hC : MeasurableSet (ball x r)ᶜ := measurableSet_ball.compl
  set g : E d → ℝ≥0∞ := (ball x r)ᶜ.indicator f with hgdef
  have hg : Measurable g := hf.indicator hC
  have hμ0 : μ ≠ 0 := by positivity
  calc ∫⁻ y in (ball x r)ᶜ, f (x + μ • (y - x))
      = ∫⁻ y, (ball x r)ᶜ.indicator (fun y ↦ f (x + μ • (y - x))) y :=
        (lintegral_indicator hC _).symm
    _ ≤ ∫⁻ y, g (x + μ • (y - x)) := lintegral_mono fun y ↦ by
        by_cases hy : y ∈ (ball x r)ᶜ
        · have hy' : x + μ • (y - x) ∈ (ball x r)ᶜ := by
            simp only [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] at hy ⊢
            rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by linarith)]
            nlinarith [norm_nonneg (y - x)]
          rw [indicator_of_mem hy, hgdef, indicator_of_mem hy']
        · rw [indicator_of_notMem hy]
          exact bot_le
    _ = ∫⁻ z, g (x + μ • z) := lintegral_sub_right_eq_self (fun z ↦ g (x + μ • z)) x
    _ = ENNReal.ofReal |(μ ^ d)⁻¹| * ∫⁻ z, g (x + z) := by
        have hmap := Measure.map_addHaar_smul (volume : Measure (E d)) hμ0
        rw [finrank_euclideanSpace_fin] at hmap
        rw [← smul_eq_mul, ← lintegral_smul_measure, ← hmap,
          lintegral_map (f := fun a ↦ g (x + a)) (hg.comp (measurable_const_add x))
          (measurable_const_smul μ)]
    _ ≤ ∫⁻ z, g (x + z) := by
        refine mul_le_of_le_one_left' (ENNReal.ofReal_le_one.2 ?_)
        rw [abs_of_nonneg (by positivity)]
        exact inv_le_one_of_one_le₀ (one_le_pow₀ hμ)
    _ = ∫⁻ z, g z := lintegral_add_left_eq_self g x
    _ = ∫⁻ z in (ball x r)ᶜ, f z := lintegral_indicator hC f

/-- **Poincaré inequality outside a ball.** If `v ∈ C¹(ℝᵈ)` vanishes on `{|y - x| ≥ R'}` and
`0 < r ≤ R'`, then `∫_{|y - x| ≥ r} v² ≤ ((R' - r) R' / r)² ∫_{|y - x| ≥ r} |Dv|²`. -/
theorem lintegral_sq_compl_ball_le {v : E d → ℝ} (hv : ContDiff ℝ 1 v) {x : E d} {r R' : ℝ}
    (hr : 0 < r) (hrR : r ≤ R') (hv0 : ∀ y, R' ≤ ‖y - x‖ → v y = 0) :
    ∫⁻ y in (ball x r)ᶜ, ENNReal.ofReal (v y ^ 2) ≤
      ENNReal.ofReal (((R' - r) * R' / r) ^ 2) *
        ∫⁻ y in (ball x r)ᶜ, ENNReal.ofReal (‖fderiv ℝ v y‖ ^ 2) := by
  set Λ := R' / r with hΛdef
  have hΛ : 1 ≤ Λ := (one_le_div hr).2 hrR
  have hR' : 0 < R' := hr.trans_le hrR
  have hC : MeasurableSet (ball x r)ᶜ := measurableSet_ball.compl
  set f : E d → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (‖fderiv ℝ v z‖ ^ 2) with hfdef
  have hfd : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  have hfm : Measurable f := (hfd.norm.pow 2).measurable.ennreal_ofReal
  have hpt : ∀ y ∈ (ball x r)ᶜ, ENNReal.ofReal (v y ^ 2) ≤
      ENNReal.ofReal ((Λ - 1) * R' ^ 2) * ∫⁻ μ in Ioc 1 Λ, f (x + μ • (y - x)) := by
    intro y hy
    have hyr : r ≤ ‖y - x‖ := by
      simpa only [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] using hy
    by_cases hyR : R' ≤ ‖y - x‖
    · simp [hv0 y hyR]
    push Not at hyR
    have h0 : v (x + Λ • (y - x)) = 0 := by
      refine hv0 _ ?_
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by linarith)]
      calc R' = Λ * r := by rw [hΛdef]; field_simp
        _ ≤ Λ * ‖y - x‖ := by gcongr
    have h := sq_le_integral_ray hv x y hΛ h0
    have hcont : Continuous fun μ : ℝ ↦ ‖fderiv ℝ v (x + μ • (y - x))‖ ^ 2 :=
      (hfd.comp (continuous_const.add (continuous_id.smul continuous_const))).norm.pow 2
    have hI0 : 0 ≤ ∫ μ in (1 : ℝ)..Λ, ‖fderiv ℝ v (x + μ • (y - x))‖ ^ 2 :=
      intervalIntegral.integral_nonneg hΛ fun _ _ ↦ sq_nonneg _
    have hint : ENNReal.ofReal (∫ μ in (1 : ℝ)..Λ, ‖fderiv ℝ v (x + μ • (y - x))‖ ^ 2) =
        ∫⁻ μ in Ioc 1 Λ, f (x + μ • (y - x)) := by
      rw [intervalIntegral.integral_of_le hΛ, ofReal_integral_eq_lintegral_ofReal
        (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        (Eventually.of_forall fun _ ↦ sq_nonneg _)]
    rw [← hint, ← ENNReal.ofReal_mul (by nlinarith)]
    refine ENNReal.ofReal_le_ofReal (h.trans ?_)
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hI0
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    exact pow_le_pow_left₀ (norm_nonneg _) hyR.le 2
  have hjoint : AEMeasurable (Function.uncurry fun (y : E d) (μ : ℝ) ↦ f (x + μ • (y - x)))
      ((volume.restrict (ball x r)ᶜ).prod (volume.restrict (Ioc 1 Λ))) := by
    refine (hfm.comp ?_).aemeasurable
    exact (continuous_const.add (continuous_snd.smul
      (continuous_fst.sub continuous_const))).measurable
  calc ∫⁻ y in (ball x r)ᶜ, ENNReal.ofReal (v y ^ 2)
      ≤ ∫⁻ y in (ball x r)ᶜ, ENNReal.ofReal ((Λ - 1) * R' ^ 2) *
          ∫⁻ μ in Ioc 1 Λ, f (x + μ • (y - x)) := setLIntegral_mono' hC hpt
    _ = ENNReal.ofReal ((Λ - 1) * R' ^ 2) *
          ∫⁻ y in (ball x r)ᶜ, ∫⁻ μ in Ioc 1 Λ, f (x + μ • (y - x)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((Λ - 1) * R' ^ 2) *
          ∫⁻ μ in Ioc 1 Λ, ∫⁻ y in (ball x r)ᶜ, f (x + μ • (y - x)) := by
        rw [lintegral_lintegral_swap hjoint]
    _ ≤ ENNReal.ofReal ((Λ - 1) * R' ^ 2) *
          ∫⁻ _μ in Ioc 1 Λ, ∫⁻ z in (ball x r)ᶜ, f z := by
        gcongr ?_ * ?_
        exact setLIntegral_mono' measurableSet_Ioc fun μ hμ ↦
          lintegral_compl_ball_comp_dilate_le hfm x r hμ.1.le
    _ = ENNReal.ofReal ((Λ - 1) * R' ^ 2) *
          (ENNReal.ofReal (Λ - 1) * ∫⁻ z in (ball x r)ᶜ, f z) := by
        rw [setLIntegral_const, Real.volume_Ioc, mul_comm (∫⁻ z in (ball x r)ᶜ, f z)]
    _ = ENNReal.ofReal (((R' - r) * R' / r) ^ 2) * ∫⁻ z in (ball x r)ᶜ, f z := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by nlinarith)]
        congr 2
        rw [hΛdef]
        field_simp

end EllipticBernoulli
