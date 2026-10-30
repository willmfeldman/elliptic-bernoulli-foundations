/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sphere.Radial
import EllipticBernoulli.Sphere.Tangential
import EllipticBernoulli.Sobolev.Lipschitz
import EllipticBernoulli.Sphere.Measure
import EllipticBernoulli.TwoPhase.Defs
import EllipticBernoulli.TwoPhase.EnergyIdentity
import Mathlib.Analysis.Calculus.Rademacher

/-!
# The ACF integral: radial identities and the key inequality

Let `w ≥ 0` be Lipschitz on `ℝᵈ` and harmonic on `{w > 0}`, with `w(x₀) = 0`, and let
`k, m, q, a` be its radial quantities about `x₀` (`Sphere/Radial.lean`). This file proves the two
lemmas behind the Alt–Caffarelli–Friedman monotonicity formula:

* `ae_rpow_mul_radialK_eq_setIntegral`: for a.e. `r > 0`, `r^{d-1} k(r) = ∫_{B_r(x₀)} |∇w|²`
  (the divergence theorem for `Δ(w²/2) = |∇w|²` on balls);
* `acfIntegral_eq_rpow_mul_setIntegral_add`: for every `r > 0`,
  `I(w, x₀, r) = r^{2-d} ∫_{B_r(x₀)} |∇w|² + (d - 2)/2 m(r)`;
* `ae_acfIntegral_eq`: for a.e. `r > 0`,
  `I(w, x₀, r) = r k(r) + (d - 2)/2 m(r)`;
* `two_mul_sphExponent_mul_acfIntegral_le`, `ae_two_mul_sphExponent_mul_acfIntegral_le`:
  for a.e. `r > 0`, if `Γ_r = {ω ∈ 𝕊 : w(x₀ + rω) > 0}` is nonempty,
  then `2 α_d(Γ_r) I(r) ≤ r · r q(r) = r I'(r)`;
* `ae_acfIntegral_eq_zero_of_eq_empty`: for a.e. `r > 0`, if `Γ_r = ∅`, then `I(r) = 0`.

Also: `sphRayleigh_nonneg`, `sphEigenvalue_nonneg`, `IsSphAdmissible.sphEigenvalue_le`
(`λ₁(Γ) ≤ R(f)` for admissible `f`), and `ae_ae_differentiableAt_add_smul`.

## Proof of the formula for `I`

One could test the energy identity `∫ |∇w|² η = -∫ w ∇w · ∇η`
(`integral_norm_sq_gradient_mul_eq_neg`) with `η = g(|x - x₀|)`, where `g` equals the fundamental
solution weight `t^{2-d}` on `[ε, r]`, is constant on `[0, ε]` and is a linear ramp of width `δ`
on `[r, r + δ]`, and then let `δ → 0` and `ε → 0`. Here the same identity is used with the ramps
alone (`g = 1` on `[0, s]`, linear on `[s, t]`): this gives `P(s) ≤ (H(t) - H(s))/(t - s) ≤ P(t)`
with `P(s) = ∫_{B_s(x₀)} |∇w|²` and `H(s) = ∫_{B_s(x₀)} w ∂ᵣw`, and since `H' = s^{d-1} k`
a.e., the divergence identity `s^{d-1} k(s) = P(s)` follows. The weight `|x - x₀|^{2-d}` is then
handled in one variable: `G(r) = r^{2-d} P(r) + (d - 2)/2 m(r)` is absolutely continuous on
compact subintervals of `(0, ∞)` with `G' = r q = I'` a.e., and `G, I → 0` as `r → 0⁺`.

The key inequality uses the restriction `f(ω) = w(x₀ + rω)`, which is admissible for `Γ_r`, the
tangential identity `∫_𝕊 |∇f̂|² = r² (q - a)` (`norm_sq_gradient_homogExt0_of_eq`), and the
completed square `∫_𝕊 (r ∂ᵣw - α w)² ≥ 0` with `α = α_d(Γ_r)`. This is the inequality (38) of
Salato (arXiv:2506.13473, v2), §5, Step 2, where it is proved with Young's inequality.

## References

* E. Salato, *A self-contained proof of the Alt–Caffarelli–Friedman monotonicity formula*,
  arXiv:2506.13473 (v2).
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped Gradient NNReal

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### The radial ramp -/

/-- The radial ramp about `x₀`: `1` on `B̄_s(x₀)`, `0` off `B_t(x₀)`, and linear in `|x - x₀|` in
between. -/
private noncomputable def ramp (x₀ : E d) (s t : ℝ) (x : E d) : ℝ :=
  max 0 (min 1 ((t - ‖x - x₀‖) / (t - s)))

private theorem lipschitzWith_ramp (x₀ : E d) {s t : ℝ} (hst : s < t) :
    LipschitzWith (Real.toNNReal (t - s)⁻¹) (ramp x₀ s t) := by
  have hc : 0 < (t - s)⁻¹ := inv_pos.mpr (sub_pos.mpr hst)
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [Real.coe_toNNReal _ hc.le, Real.dist_eq, dist_eq_norm]
  unfold ramp
  calc |max 0 (min 1 ((t - ‖x - x₀‖) / (t - s))) - max 0 (min 1 ((t - ‖y - x₀‖) / (t - s)))|
      ≤ |min 1 ((t - ‖x - x₀‖) / (t - s)) - min 1 ((t - ‖y - x₀‖) / (t - s))| := by
        rw [max_comm 0, max_comm 0]; exact abs_max_sub_max_le_abs _ _ _
    _ ≤ |(t - ‖x - x₀‖) / (t - s) - (t - ‖y - x₀‖) / (t - s)| := by
        rw [min_comm 1, min_comm 1]
        refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
        simp
    _ = (t - s)⁻¹ * |‖y - x₀‖ - ‖x - x₀‖| := by
        rw [← sub_div, div_eq_inv_mul, abs_mul, abs_of_pos hc]; congr 2; ring
    _ ≤ (t - s)⁻¹ * ‖x - y‖ := by
        gcongr
        calc |‖y - x₀‖ - ‖x - x₀‖| ≤ ‖(y - x₀) - (x - x₀)‖ := abs_norm_sub_norm_le _ _
          _ = ‖x - y‖ := by rw [← norm_neg]; congr 1; abel

private theorem ramp_nonneg (x₀ : E d) (s t : ℝ) (x : E d) : 0 ≤ ramp x₀ s t x :=
  le_max_left _ _

private theorem ramp_le_one (x₀ : E d) (s t : ℝ) (x : E d) : ramp x₀ s t x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

private theorem ramp_eq_one {x₀ : E d} {s t : ℝ} (hst : s < t) {x : E d} (hx : ‖x - x₀‖ ≤ s) :
    ramp x₀ s t x = 1 := by
  have h : 1 ≤ (t - ‖x - x₀‖) / (t - s) := by
    rw [le_div_iff₀ (sub_pos.mpr hst)]; linarith
  simp [ramp, min_eq_left h]

private theorem ramp_eq_zero {x₀ : E d} {s t : ℝ} (hst : s < t) {x : E d} (hx : t ≤ ‖x - x₀‖) :
    ramp x₀ s t x = 0 := by
  have h : (t - ‖x - x₀‖) / (t - s) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_pos.mpr hst).le
  simp [ramp, min_eq_right (h.trans zero_le_one), max_eq_left h]

private theorem hasCompactSupport_ramp (x₀ : E d) {s t : ℝ} (hst : s < t) :
    HasCompactSupport (ramp x₀ s t) :=
  HasCompactSupport.intro (isCompact_closedBall x₀ t) fun x hx ↦ by
    rw [mem_closedBall, dist_eq_norm, not_le] at hx
    exact ramp_eq_zero hst hx.le

/-- The derivative of `x ↦ ‖x - x₀‖` at `x ≠ x₀`. -/
private theorem hasFDerivAt_norm_sub {x₀ x : E d} (hx : x ≠ x₀) :
    HasFDerivAt (fun y : E d ↦ ‖y - x₀‖) (innerSL ℝ (‖x - x₀‖⁻¹ • (x - x₀))) x := by
  have hne : ‖x - x₀‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  have h1 := ((hasFDerivAt_id x).sub_const x₀).norm_sq
  have h2 := h1.sqrt (by simp only [id]; positivity)
  simp only [id, Real.sqrt_sq (norm_nonneg _)] at h2
  refine h2.congr_fderiv ?_
  ext v
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, inner_smul_left, ContinuousLinearMap.coe_id', id, RCLike.conj_to_real]
  rw [smul_eq_mul, nsmul_eq_mul]
  field_simp
  ring

/-- The gradient of the ramp: for a.e. `x`, `∇η(x) = -(t - s)⁻¹ (x - x₀)/|x - x₀|` on the annulus
`B_t(x₀) \ B_s(x₀)` and `0` elsewhere. -/
private theorem ae_gradient_ramp (hd : 1 ≤ d) (x₀ : E d) {s t : ℝ} (hs0 : 0 ≤ s) (hst : s < t) :
    ∀ᵐ x, ∇ (ramp x₀ s t) x = (ball x₀ t \ ball x₀ s).indicator
      (fun x ↦ -(t - s)⁻¹ • (‖x - x₀‖⁻¹ • (x - x₀))) x := by
  have := nontrivial_E hd
  have hs := measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere (volume : Measure (E d)) x₀ s)
  have ht := measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere (volume : Measure (E d)) x₀ t)
  filter_upwards [hs, ht] with x hxs hxt
  rw [mem_sphere, dist_eq_norm] at hxs hxt
  rcases lt_or_gt_of_ne hxs with h1 | h1
  · -- inside the inner ball
    have hmem : x ∉ ball x₀ t \ ball x₀ s := fun h ↦ h.2 (by rw [mem_ball, dist_eq_norm]; exact h1)
    rw [indicator_of_notMem hmem]
    have heq : ramp x₀ s t =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ) := by
      filter_upwards [isOpen_ball.mem_nhds (show x ∈ ball x₀ s by
        rw [mem_ball, dist_eq_norm]; exact h1)] with y hy
      rw [mem_ball, dist_eq_norm] at hy
      exact ramp_eq_one hst hy.le
    rw [heq.gradient_eq, gradient_fun_const]
  rcases lt_or_gt_of_ne hxt with h2 | h2
  · -- in the annulus
    have hmem : x ∈ ball x₀ t \ ball x₀ s := by
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_eq_norm]; exact h2
      · rw [mem_ball, dist_eq_norm, not_lt]; exact h1.le
    rw [indicator_of_mem hmem]
    have hx0 : x ≠ x₀ := by
      intro h; rw [h, sub_self, norm_zero] at h1; linarith
    have hopen : IsOpen {y : E d | s < ‖y - x₀‖ ∧ ‖y - x₀‖ < t} :=
      (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
        (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)
    have heq : ramp x₀ s t =ᶠ[𝓝 x] fun y ↦ (t - s)⁻¹ * (t - ‖y - x₀‖) := by
      filter_upwards [hopen.mem_nhds ⟨h1, h2⟩] with y hy
      have hpos : 0 < t - s := sub_pos.mpr hst
      have h0 : 0 ≤ (t - ‖y - x₀‖) / (t - s) := div_nonneg (by linarith [hy.2]) hpos.le
      have h1' : (t - ‖y - x₀‖) / (t - s) ≤ 1 := by
        rw [div_le_one hpos]; linarith [hy.1]
      rw [div_eq_inv_mul] at h0 h1'
      simp only [ramp, div_eq_inv_mul, min_eq_right h1', max_eq_right h0]
    have hder : HasFDerivAt (fun y : E d ↦ (t - s)⁻¹ * (t - ‖y - x₀‖))
        (toDual ℝ (E d) (-(t - s)⁻¹ • (‖x - x₀‖⁻¹ • (x - x₀)))) x := by
      refine (((hasFDerivAt_norm_sub hx0).const_sub t).const_mul (t - s)⁻¹).congr_fderiv ?_
      ext v
      simp only [smul_apply, neg_apply, innerSL_apply_apply,
        toDual_apply_apply, inner_smul_left, RCLike.conj_to_real, smul_eq_mul]
      ring
    exact (hasGradientAt_iff_hasFDerivAt.mpr (hder.congr_of_eventuallyEq heq)).gradient
  · -- outside the outer ball
    have hmem : x ∉ ball x₀ t \ ball x₀ s := fun h ↦ by
      have := h.1; rw [mem_ball, dist_eq_norm] at this; linarith
    rw [indicator_of_notMem hmem]
    have heq : ramp x₀ s t =ᶠ[𝓝 x] fun _ ↦ (0 : ℝ) := by
      have hopen : IsOpen {y : E d | t < ‖y - x₀‖} :=
        isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
      filter_upwards [hopen.mem_nhds h2] with y hy
      exact ramp_eq_zero hst (le_of_lt hy)
    rw [heq.gradient_eq, gradient_fun_const]

/-! ### Divergence identity on balls -/

variable {w : E d → ℝ} {L : ℝ≥0} {x₀ : E d}

/-- On `B_R(x₀)`, `|w ∂ᵣw| ≤ (|w(x₀)| + L R) L`. -/
private theorem abs_mul_radialDeriv_le (hw : LipschitzWith L w) (x₀ : E d) {R : ℝ} {x : E d}
    (hx : x ∈ ball x₀ R) : |w x * radialDeriv w x₀ x| ≤ (|w x₀| + L * R) * L := by
  rw [abs_mul]
  have h1 : |w x| ≤ |w x₀| + L * R := by
    have h := hw.dist_le_mul x x₀
    rw [Real.dist_eq] at h
    have := abs_sub_abs_le_abs_sub (w x) (w x₀)
    have hxR : dist x x₀ ≤ R := (mem_ball.mp hx).le
    nlinarith [L.coe_nonneg]
  exact mul_le_mul h1 (abs_radialDeriv_le hw x₀ x) (abs_nonneg _)
    (by have := abs_nonneg (w x); linarith)

private theorem integrableOn_ball_mul_radialDeriv (hw : LipschitzWith L w) (x₀ : E d) (R : ℝ) :
    IntegrableOn (fun x ↦ w x * radialDeriv w x₀ x) (ball x₀ R) :=
  Measure.integrableOn_of_bounded (M := (|w x₀| + L * R) * L) measure_ball_lt_top.ne
    (hw.continuous.measurable.mul (measurable_radialDeriv w x₀)).aestronglyMeasurable
    ((ae_restrict_mem measurableSet_ball).mono fun x hx ↦ by
      rw [Real.norm_eq_abs]; exact abs_mul_radialDeriv_le hw x₀ hx)

private theorem integrableOn_ball_norm_sq_gradient (hw : LipschitzWith L w) (x₀ : E d) (R : ℝ) :
    IntegrableOn (fun x ↦ ‖∇ w x‖ ^ 2) (ball x₀ R) :=
  Measure.integrableOn_of_bounded (M := (L : ℝ) ^ 2) measure_ball_lt_top.ne
    ((measurable_gradient w).norm.pow_const 2).aestronglyMeasurable
    (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_le_of_lipschitzWith hw x) 2)

/-- The energy identity tested with the ramp:
`∫ |∇w|² η = (t - s)⁻¹ (∫_{B_t(x₀)} w ∂ᵣw - ∫_{B_s(x₀)} w ∂ᵣw)`. -/
private theorem integral_norm_sq_gradient_mul_ramp (hd : 1 ≤ d) (hw : LipschitzWith L w)
    (hw0 : ∀ x, 0 ≤ w x) (hharm : HarmonicOnNhd w {x | 0 < w x}) (x₀ : E d) {s t : ℝ}
    (hs0 : 0 ≤ s) (hst : s < t) :
    ∫ x, ‖∇ w x‖ ^ 2 * ramp x₀ s t x =
      (t - s)⁻¹ * ((∫ x in ball x₀ t, w x * radialDeriv w x₀ x) -
        ∫ x in ball x₀ s, w x * radialDeriv w x₀ x) := by
  rw [integral_norm_sq_gradient_mul_eq_neg hw hw0 hharm (lipschitzWith_ramp x₀ hst)
    (hasCompactSupport_ramp x₀ hst), ← integral_neg]
  have hA : MeasurableSet (ball x₀ t \ ball x₀ s) := measurableSet_ball.diff measurableSet_ball
  calc ∫ x, -(w x * inner ℝ (∇ w x) (∇ (ramp x₀ s t) x))
      = ∫ x, (ball x₀ t \ ball x₀ s).indicator
          (fun x ↦ (t - s)⁻¹ * (w x * radialDeriv w x₀ x)) x := by
        refine integral_congr_ae ?_
        filter_upwards [ae_gradient_ramp hd x₀ hs0 hst] with x hx
        rw [hx]
        by_cases hmem : x ∈ ball x₀ t \ ball x₀ s
        · simp only [indicator_of_mem hmem, inner_smul_right, radialDeriv]
          ring
        · simp [indicator_of_notMem hmem]
    _ = (t - s)⁻¹ * ((∫ x in ball x₀ t, w x * radialDeriv w x₀ x) -
          ∫ x in ball x₀ s, w x * radialDeriv w x₀ x) := by
        rw [integral_indicator hA, integral_const_mul,
          setIntegral_sdiff measurableSet_ball (integrableOn_ball_mul_radialDeriv hw x₀ t)
            (ball_subset_ball hst.le)]

/-- `d/dr ∫_{B_r(x₀)} w ∂ᵣw = r^{d-1} k(r)` for a.e. `r > 0`. -/
private theorem ae_hasDerivAt_setIntegral_ball_mul_radialDeriv (hd : 1 ≤ d)
    (hw : LipschitzWith L w) (x₀ : E d) :
    ∀ᵐ r, 0 < r → HasDerivAt (fun s ↦ ∫ x in ball x₀ s, w x * radialDeriv w x₀ x)
      (r ^ ((d : ℝ) - 1) * radialK w x₀ r) r := by
  have key : ∀ n : ℕ, ∀ᵐ r : ℝ, 0 < r → r < n →
      HasDerivAt (fun s ↦ ∫ x in ball x₀ s, w x * radialDeriv w x₀ x)
        (r ^ ((d : ℝ) - 1) * radialK w x₀ r) r := by
    intro n
    set h : E d → ℝ := (ball x₀ n).indicator fun x ↦ w x * radialDeriv w x₀ x with hh
    have hmeas : Measurable h :=
      (hw.continuous.measurable.mul (measurable_radialDeriv w x₀)).indicator measurableSet_ball
    have hC : ∀ x, |h x| ≤ (|w x₀| + L * n) * L := fun x ↦ by
      by_cases hx : x ∈ ball x₀ n
      · rw [hh, indicator_of_mem hx]; exact abs_mul_radialDeriv_le hw x₀ hx
      · rw [hh, indicator_of_notMem hx, abs_zero]; positivity
    filter_upwards [ae_hasDerivAt_setIntegral_ball_mul_rpow hd hmeas hC x₀ (β := 0)
      (by have : (1 : ℝ) ≤ d := by exact_mod_cast hd
          linarith)] with r hr hr0 hrn
    have h1 := hr hr0
    have heq : (fun s ↦ ∫ x in ball x₀ s, h x * ‖x - x₀‖ ^ (0 : ℝ)) =ᶠ[𝓝 r]
        fun s ↦ ∫ x in ball x₀ s, w x * radialDeriv w x₀ x := by
      filter_upwards [Iio_mem_nhds hrn] with s hs
      refine setIntegral_congr_fun measurableSet_ball fun x hx ↦ ?_
      simp only [hh, Real.rpow_zero, mul_one,
        indicator_of_mem (ball_subset_ball (le_of_lt hs) hx)]
    have hk : ∫ ω : sphere (0 : E d) 1, h (x₀ + r • (ω : E d)) ∂(volume : Measure (E d)).toSphere
        = radialK w x₀ r := by
      refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
      have hmem : x₀ + r • (ω : E d) ∈ ball x₀ n := by
        rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_eq_of_mem_sphere ω,
          mul_one, Real.norm_of_nonneg hr0.le]
        exact hrn
      simp only [hh, indicator_of_mem hmem]
    rw [hk, add_zero] at h1
    exact h1.congr_of_eventuallyEq heq.symm
  rw [← ae_all_iff] at key
  filter_upwards [key] with r hr hr0
  obtain ⟨n, hn⟩ := exists_nat_gt r
  exact hr n hr0 hn

/-- `d/dr ∫_{B_r(x₀)} |∇w|² = r^{d-1} q(r)` for a.e. `r > 0`. -/
private theorem ae_hasDerivAt_setIntegral_ball_norm_sq_gradient (hd : 1 ≤ d)
    (hw : LipschitzWith L w) (x₀ : E d) :
    ∀ᵐ r, 0 < r → HasDerivAt (fun s ↦ ∫ x in ball x₀ s, ‖∇ w x‖ ^ 2)
      (r ^ ((d : ℝ) - 1) * radialQ w x₀ r) r := by
  have hC : ∀ x, |‖∇ w x‖ ^ 2| ≤ (L : ℝ) ^ 2 := fun x ↦ by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_le_of_lipschitzWith hw x) 2
  filter_upwards [ae_hasDerivAt_setIntegral_ball_mul_rpow hd
    ((measurable_gradient w).norm.pow_const 2) hC x₀ (β := 0)
    (by have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        linarith)] with r hr hr0
  have h1 := hr hr0
  simp only [Real.rpow_zero, mul_one, add_zero] at h1
  exact h1

/-- `r ↦ ∫_{B_r(x₀)} |∇w|²` is Lipschitz on `[0, R]`. -/
private theorem exists_lipschitzOnWith_setIntegral_ball_norm_sq_gradient (hd : 1 ≤ d)
    (hw : LipschitzWith L w) (x₀ : E d) (R : ℝ) :
    ∃ K, LipschitzOnWith K (fun s ↦ ∫ x in ball x₀ s, ‖∇ w x‖ ^ 2) (Icc 0 R) := by
  have hC : ∀ x, |‖∇ w x‖ ^ 2| ≤ (L : ℝ) ^ 2 := fun x ↦ by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_le_of_lipschitzWith hw x) 2
  have h := exists_lipschitzOnWith_setIntegral_ball_mul_rpow hd
    ((measurable_gradient w).norm.pow_const 2) hC x₀ (β := 0)
    (by have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        linarith) R
  simpa only [Real.rpow_zero, mul_one] using h

/-- **The divergence identity on balls.** For `w ≥ 0` Lipschitz and harmonic on `{w > 0}`, for
a.e. `r > 0`, `r^{d-1} k(r) = ∫_{B_r(x₀)} |∇w|²`: the flux of `∇(w²/2)` through `∂B_r(x₀)` equals
`∫_{B_r(x₀)} Δ(w²/2)`. It is proved by testing the energy identity with radial ramps of width
`δ → 0`. -/
theorem ae_rpow_mul_radialK_eq_setIntegral (hd : 1 ≤ d) (hw : LipschitzWith L w)
    (hw0 : ∀ x, 0 ≤ w x) (hharm : HarmonicOnNhd w {x | 0 < w x}) (x₀ : E d) :
    ∀ᵐ r, 0 < r → r ^ ((d : ℝ) - 1) * radialK w x₀ r = ∫ x in ball x₀ r, ‖∇ w x‖ ^ 2 := by
  filter_upwards [ae_hasDerivAt_setIntegral_ball_mul_radialDeriv hd hw x₀,
    ae_hasDerivAt_setIntegral_ball_norm_sq_gradient hd hw x₀] with s hH hP hs
  set H : ℝ → ℝ := fun s ↦ ∫ x in ball x₀ s, w x * radialDeriv w x₀ x with hHdef
  set P : ℝ → ℝ := fun s ↦ ∫ x in ball x₀ s, ‖∇ w x‖ ^ 2 with hPdef
  have hH' := hH hs
  have hP' := hP hs
  -- the ramp squeeze `P(s) ≤ slope H s t ≤ P(t)`
  have hint : ∀ t, s < t → Integrable fun x ↦ ‖∇ w x‖ ^ 2 * ramp x₀ s t x := fun t hst ↦
    integrable_of_isCompact_of_bound (isCompact_closedBall x₀ t)
      (((measurable_gradient w).norm.pow_const 2).mul
        (lipschitzWith_ramp x₀ hst).continuous.measurable).aestronglyMeasurable
      (fun x hx ↦ by
        rw [mem_closedBall, dist_eq_norm, not_le] at hx
        rw [ramp_eq_zero hst hx.le, mul_zero])
      (C := (L : ℝ) ^ 2) fun x _ ↦ by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _),
          abs_of_nonneg (ramp_nonneg _ _ _ _)]
        calc ‖∇ w x‖ ^ 2 * ramp x₀ s t x ≤ (L : ℝ) ^ 2 * 1 :=
              mul_le_mul (pow_le_pow_left₀ (norm_nonneg _)
                (norm_gradient_le_of_lipschitzWith hw x) 2) (ramp_le_one _ _ _ _)
                (ramp_nonneg _ _ _ _) (sq_nonneg _)
          _ = (L : ℝ) ^ 2 := mul_one _
  have hslope : ∀ t, s < t → slope H s t = ∫ x, ‖∇ w x‖ ^ 2 * ramp x₀ s t x := fun t hst ↦ by
    rw [integral_norm_sq_gradient_mul_ramp hd hw hw0 hharm x₀ hs.le hst, slope_def_field,
      div_eq_inv_mul]
  have hle1 : ∀ t, s < t → P s ≤ slope H s t := fun t hst ↦ by
    rw [hslope t hst, hPdef]
    dsimp only
    rw [← integral_indicator measurableSet_ball]
    refine integral_mono ((integrable_indicator_iff measurableSet_ball).mpr
      (integrableOn_ball_norm_sq_gradient hw x₀ s)) (hint t hst) fun x ↦ ?_
    by_cases hx : x ∈ ball x₀ s
    · rw [indicator_of_mem hx]
      rw [mem_ball, dist_eq_norm] at hx
      rw [ramp_eq_one hst hx.le, mul_one]
    · rw [indicator_of_notMem hx]
      exact mul_nonneg (sq_nonneg _) (ramp_nonneg _ _ _ _)
  have hle2 : ∀ t, s < t → slope H s t ≤ P t := fun t hst ↦ by
    rw [hslope t hst, hPdef]
    dsimp only
    rw [← integral_indicator measurableSet_ball]
    refine integral_mono (hint t hst) ((integrable_indicator_iff measurableSet_ball).mpr
      (integrableOn_ball_norm_sq_gradient hw x₀ t)) fun x ↦ ?_
    by_cases hx : x ∈ ball x₀ t
    · rw [indicator_of_mem hx]
      exact (mul_le_mul_of_nonneg_left (ramp_le_one _ _ _ _) (sq_nonneg _)).trans_eq (mul_one _)
    · rw [indicator_of_notMem hx]
      rw [mem_ball, dist_eq_norm, not_lt] at hx
      rw [ramp_eq_zero hst hx, mul_zero]
  have hlim : Tendsto (slope H s) (𝓝[>] s) (𝓝 (s ^ ((d : ℝ) - 1) * radialK w x₀ s)) :=
    hH'.tendsto_slope.mono_left (nhdsWithin_mono _ fun t ht ↦ ne_of_gt ht)
  have hPlim : Tendsto P (𝓝[>] s) (𝓝 (P s)) :=
    hP'.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  refine le_antisymm ?_ ?_
  · exact le_of_tendsto_of_tendsto hlim hPlim (eventually_nhdsWithin_of_forall hle2)
  · exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall hle1)

/-! ### The formula for `I` -/

/-- `|∫_{B_r(x₀)} |∇w|²| ≤ L² σ(𝕊) r^{d-1} r`. -/
private theorem abs_setIntegral_ball_norm_sq_gradient_le (hd : 1 ≤ d) (hw : LipschitzWith L w)
    (x₀ : E d) {r : ℝ} (hr : 0 ≤ r) :
    |∫ x in ball x₀ r, ‖∇ w x‖ ^ 2| ≤
      (L : ℝ) ^ 2 * (volume : Measure (E d)).toSphere.real univ * r ^ ((d : ℝ) - 1) * r := by
  have hC : ∀ x, |‖∇ w x‖ ^ 2| ≤ (L : ℝ) ^ 2 := fun x ↦ by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_le_of_lipschitzWith hw x) 2
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h := setIntegral_ball_mul_rpow_eq hd ((measurable_gradient w).norm.pow_const 2) hC x₀
    (β := 0) (by linarith) hr
  simp only [Real.rpow_zero, mul_one, add_zero] at h
  rw [h, ← Real.norm_eq_abs]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := r)
    (C := r ^ ((d : ℝ) - 1) * ((L : ℝ) ^ 2 * (volume : Measure (E d)).toSphere.real univ))
    (f := fun τ ↦ τ ^ ((d : ℝ) - 1) * radialQ w x₀ τ) fun τ hτ ↦ by
      rw [uIoc_of_le hr] at hτ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hτ.1.le _),
        abs_of_nonneg (radialQ_nonneg w x₀ τ)]
      exact mul_le_mul (Real.rpow_le_rpow hτ.1.le hτ.2 (by linarith)) (radialQ_le hw x₀ τ)
        (radialQ_nonneg w x₀ τ) (Real.rpow_nonneg hr _)
  refine hbound.trans_eq ?_
  rw [sub_zero, abs_of_nonneg hr]
  ring

/-- **The ACF integral through the energy of balls.** For `w ≥ 0` Lipschitz and harmonic on
`{w > 0}`, with `w x₀ = 0`, for every `r > 0`,
`I(w, x₀, r) = r^{2-d} ∫_{B_r(x₀)} |∇w|² + (d - 2)/2 m(r)`. Both sides vanish as `r → 0⁺` and,
by the divergence identity `ae_rpow_mul_radialK_eq_setIntegral` and `m' = 2k`, both have
derivative `r q(r)` almost everywhere. -/
theorem acfIntegral_eq_rpow_mul_setIntegral_add (hd : 1 ≤ d) (hw : LipschitzWith L w)
    (hw0 : ∀ x, 0 ≤ w x) (hharm : HarmonicOnNhd w {x | 0 < w x}) (hx₀ : w x₀ = 0) {r : ℝ}
    (hr : 0 < r) :
    acfIntegral w x₀ r =
      r ^ (2 - (d : ℝ)) * (∫ x in ball x₀ r, ‖∇ w x‖ ^ 2) + ((d : ℝ) - 2) / 2 * radialM w x₀ r := by
  set P : ℝ → ℝ := fun s ↦ ∫ x in ball x₀ s, ‖∇ w x‖ ^ 2 with hPdef
  set G : ℝ → ℝ := fun s ↦ s ^ (2 - (d : ℝ)) * P s + ((d : ℝ) - 2) / 2 * radialM w x₀ s
    with hGdef
  set I : ℝ → ℝ := acfIntegral w x₀ with hIdef
  set σ := (volume : Measure (E d)).toSphere.real univ
  -- Step 1: `G - I` is constant on `(0, r]`
  have hstep : ∀ ε, 0 < ε → ε < r → G r - I r = G ε - I ε := by
    intro ε hε hεr
    have huIcc : uIcc ε r = Icc ε r := uIcc_of_le hεr.le
    have hsub : uIcc ε r ⊆ Icc 0 r := by rw [huIcc]; exact Icc_subset_Icc hε.le le_rfl
    obtain ⟨KP, hKP⟩ := exists_lipschitzOnWith_setIntegral_ball_norm_sq_gradient hd hw x₀ r
    have hPac : AbsolutelyContinuousOnInterval P ε r :=
      (hKP.mono hsub).absolutelyContinuousOnInterval
    have hpow : AbsolutelyContinuousOnInterval (fun s : ℝ ↦ s ^ (2 - (d : ℝ))) ε r :=
      ContDiffOn.absolutelyContinuousOnInterval fun s hs ↦
        (Real.contDiffAt_rpow_const_of_ne
          (by rw [huIcc] at hs; exact (hε.trans_le hs.1).ne')).contDiffWithinAt
    have hk : IntervalIntegrable (fun τ ↦ 2 * radialK w x₀ τ) volume ε r := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hεr.le]
      refine IntegrableOn.of_bound measure_Icc_lt_top
        ((stronglyMeasurable_const.mul
          (stronglyMeasurable_radialK hw.continuous.measurable x₀)).aestronglyMeasurable)
        (2 * ((L : ℝ) ^ 2 * r * σ)) ?_
      rw [ae_restrict_iff' measurableSet_Icc]
      refine ae_of_all _ fun τ hτ ↦ ?_
      rw [Real.norm_eq_abs, abs_mul, abs_two]
      gcongr
      calc |radialK w x₀ τ| ≤ (L : ℝ) ^ 2 * τ * σ := abs_radialK_le hw hx₀ (hε.le.trans hτ.1)
        _ ≤ (L : ℝ) ^ 2 * r * σ := by
          gcongr
          exact hτ.2
    have hm : AbsolutelyContinuousOnInterval (radialM w x₀) ε r := by
      refine ((hk.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc).add
        (LipschitzWith.const (radialM w x₀ ε)).lipschitzOnWith.absolutelyContinuousOnInterval
        ).congr fun t ht ↦ ?_
      rw [huIcc] at ht
      have := radialM_sub_eq_integral hd hw x₀ hε.le ht.1
      simp only [Pi.add_apply]
      linarith
    have hG : AbsolutelyContinuousOnInterval G ε r := (hpow.fun_mul hPac).fun_add (hm.const_mul _)
    have hGd : ∀ᵐ τ, τ ∈ uIoo ε r → HasDerivAt G (τ * radialQ w x₀ τ) τ := by
      filter_upwards [ae_rpow_mul_radialK_eq_setIntegral hd hw hw0 hharm x₀,
        ae_hasDerivAt_setIntegral_ball_norm_sq_gradient hd hw x₀,
        ae_hasDerivAt_radialM hd hw hx₀] with τ hK hP hm hτ
      rw [uIoo_of_le hεr.le] at hτ
      have hτ0 : 0 < τ := hε.trans hτ.1
      have h1 := Real.hasDerivAt_rpow_const (p := 2 - (d : ℝ)) (Or.inl hτ0.ne')
      have h2 := (h1.mul (hP hτ0)).add ((hm hτ0).const_mul (((d : ℝ) - 2) / 2))
      refine h2.congr_deriv ?_
      rw [← hK hτ0]
      have e1 : τ ^ (2 - (d : ℝ) - 1) * τ ^ ((d : ℝ) - 1) = 1 := by
        rw [← Real.rpow_add hτ0, show 2 - (d : ℝ) - 1 + ((d : ℝ) - 1) = 0 by ring,
          Real.rpow_zero]
      have e2 : τ ^ (2 - (d : ℝ)) * τ ^ ((d : ℝ) - 1) = τ := by
        rw [← Real.rpow_add hτ0]; norm_num
      linear_combination ((2 - (d : ℝ)) * radialK w x₀ τ) * e1 + radialQ w x₀ τ * e2
    have hGr := hG.integral_eq_sub_of_ae_hasDerivAt hGd
    obtain ⟨KI, hKI⟩ := exists_lipschitzOnWith_acfIntegral hd hw x₀ r
    have hIr := (hKI.mono hsub).integral_eq_sub_of_ae_hasDerivAt
      (f' := fun τ ↦ τ * radialQ w x₀ τ) (by
        filter_upwards [ae_hasDerivAt_acfIntegral hd hw x₀] with τ h hτ
        rw [uIoo_of_le hεr.le] at hτ
        exact h (hε.trans hτ.1))
    linarith
  -- Step 2: `G - I → 0` at `0⁺`
  have hlimP : Tendsto (fun ε ↦ ε ^ (2 - (d : ℝ)) * P ε) (𝓝[>] 0) (𝓝 0) := by
    have hq : Tendsto (fun ε : ℝ ↦ (L : ℝ) ^ 2 * σ * ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun ε : ℝ ↦ (L : ℝ) ^ 2 * σ * ε ^ 2) (𝓝 0) (𝓝 ((L : ℝ) ^ 2 * σ * 0 ^ 2)) :=
        (continuous_const.mul (continuous_pow 2)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hq
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hε.le _)]
    calc ε ^ (2 - (d : ℝ)) * |P ε| ≤
          ε ^ (2 - (d : ℝ)) * ((L : ℝ) ^ 2 * σ * ε ^ ((d : ℝ) - 1) * ε) :=
          mul_le_mul_of_nonneg_left (abs_setIntegral_ball_norm_sq_gradient_le hd hw x₀ hε.le)
            (Real.rpow_nonneg hε.le _)
      _ = (L : ℝ) ^ 2 * σ * (ε ^ (2 - (d : ℝ)) * ε ^ ((d : ℝ) - 1)) * ε := by ring
      _ = (L : ℝ) ^ 2 * σ * ε ^ 2 := by
          rw [← Real.rpow_add hε]; norm_num; ring
  have hlimM : Tendsto (fun ε ↦ ((d : ℝ) - 2) / 2 * radialM w x₀ ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_radialM_nhdsGT_zero hw hx₀).const_mul (((d : ℝ) - 2) / 2)
  have hlimI : Tendsto I (𝓝[>] 0) (𝓝 0) := by
    obtain ⟨K1, hK1⟩ := exists_lipschitzOnWith_acfIntegral hd hw x₀ 1
    have hc := hK1.continuousOn (x := 0) ⟨le_rfl, zero_le_one⟩
    have hI0 : acfIntegral w x₀ 0 = 0 := by simp [acfIntegral, ball_zero]
    have h := (hc.mono_of_mem_nhdsWithin (Icc_mem_nhdsGT zero_lt_one)).tendsto
    rwa [hI0] at h
  have hlim : Tendsto (fun ε ↦ G ε - I ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hlimP.add hlimM).sub hlimI
  have hev : (fun ε ↦ G ε - I ε) =ᶠ[𝓝[>] 0] fun _ ↦ G r - I r := by
    filter_upwards [Ioo_mem_nhdsGT hr] with ε hε
    exact (hstep ε hε.1 hε.2).symm
  have h0 : G r - I r = 0 := tendsto_nhds_unique (tendsto_const_nhds.congr' hev.symm) hlim
  have : I r = G r := by linarith
  exact this

/-- **ACF formula for `I`.** Let `w ≥ 0` be Lipschitz and harmonic on
`{w > 0}`, with `w(x₀) = 0`. For a.e. `r > 0`, `I(w, x₀, r) = r k(r) + (d - 2)/2 m(r)`. -/
theorem ae_acfIntegral_eq (hd : 1 ≤ d) (hw : LipschitzWith L w) (hw0 : ∀ x, 0 ≤ w x)
    (hharm : HarmonicOnNhd w {x | 0 < w x}) (hx₀ : w x₀ = 0) :
    ∀ᵐ r, 0 < r →
      acfIntegral w x₀ r = r * radialK w x₀ r + ((d : ℝ) - 2) / 2 * radialM w x₀ r := by
  filter_upwards [ae_rpow_mul_radialK_eq_setIntegral hd hw hw0 hharm x₀] with r hK hr
  rw [acfIntegral_eq_rpow_mul_setIntegral_add hd hw hw0 hharm hx₀ hr, ← hK hr, ← mul_assoc,
    ← Real.rpow_add hr]
  norm_num

/-! ### Eigenvalue facts -/

theorem sphRayleigh_nonneg (f : sphere (0 : E d) 1 → ℝ) : 0 ≤ sphRayleigh f :=
  div_nonneg (integral_nonneg fun _ ↦ sq_nonneg _) (integral_nonneg fun _ ↦ sq_nonneg _)

theorem sphEigenvalue_nonneg (Γ : Set (sphere (0 : E d) 1)) : 0 ≤ sphEigenvalue Γ :=
  Real.sInf_nonneg (by rintro _ ⟨g, -, rfl⟩; exact sphRayleigh_nonneg g)

/-- `λ₁(Γ) ≤ R(f)` for every `f` admissible for `Γ`. -/
theorem IsSphAdmissible.sphEigenvalue_le {Γ : Set (sphere (0 : E d) 1)}
    {f : sphere (0 : E d) 1 → ℝ} (hf : IsSphAdmissible Γ f) : sphEigenvalue Γ ≤ sphRayleigh f :=
  csInf_le ⟨0, by rintro _ ⟨g, -, rfl⟩; exact sphRayleigh_nonneg g⟩ ⟨f, hf, rfl⟩

/-! ### The key inequality -/

private theorem lipschitzWith_restrict (hw : LipschitzWith L w) (x₀ : E d) {r : ℝ} (hr : 0 ≤ r) :
    LipschitzWith (L * Real.toNNReal r)
      (fun ω : sphere (0 : E d) 1 ↦ w (x₀ + r • (ω : E d))) := by
  refine hw.comp (LipschitzWith.of_dist_le_mul fun ω ω' ↦ ?_)
  rw [Subtype.dist_eq, dist_eq_norm, dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub,
    norm_smul, Real.norm_of_nonneg hr, Real.coe_toNNReal _ hr]

/-- `|w(x₀ + rω)| ≤ L r` when `w(x₀) = 0`. -/
private theorem abs_apply_add_smul_le' (hw : LipschitzWith L w) (hx₀ : w x₀ = 0) {r : ℝ}
    (hr : 0 ≤ r) (ω : sphere (0 : E d) 1) : |w (x₀ + r • (ω : E d))| ≤ L * r := by
  have h := abs_apply_add_smul_le hw x₀ hr ω
  rwa [hx₀, abs_zero, zero_add] at h

/-- **The key inequality** at a fixed radius. Let `w ≥ 0` be
`L`-Lipschitz with `w(x₀) = 0`, and let `r > 0` be a radius at which `w` is differentiable at
`x₀ + rω` for `σ`-a.e. `ω` and `I(r) = r k(r) + (d - 2)/2 m(r)`. If
`Γ_r = {ω ∈ 𝕊 : w(x₀ + rω) > 0}` is nonempty, then `2 α_d(Γ_r) I(r) ≤ r · r q(r)`; by
`ae_hasDerivAt_acfIntegral`, `r q(r) = I'(r)` for a.e. `r`. The proof is the completed square
`∫_𝕊 (r ∂ᵣw - α w)² ≥ 0`, which replaces the Cauchy–Schwarz step `k ≤ a^{1/2} m^{1/2}`. -/
theorem two_mul_sphExponent_mul_acfIntegral_le (hw : LipschitzWith L w) (hw0 : ∀ x, 0 ≤ w x)
    (hx₀ : w x₀ = 0) {r : ℝ} (hr : 0 < r)
    (hdiff : ∀ᵐ ω : sphere (0 : E d) 1 ∂(volume : Measure (E d)).toSphere,
      DifferentiableAt ℝ w (x₀ + r • (ω : E d)))
    (hI : acfIntegral w x₀ r = r * radialK w x₀ r + ((d : ℝ) - 2) / 2 * radialM w x₀ r)
    (hΓ : {ω : sphere (0 : E d) 1 | 0 < w (x₀ + r • (ω : E d))}.Nonempty) :
    2 * sphExponent {ω : sphere (0 : E d) 1 | 0 < w (x₀ + r • (ω : E d))} * acfIntegral w x₀ r ≤
      r * (r * radialQ w x₀ r) := by
  set Γ : Set (sphere (0 : E d) 1) := {ω | 0 < w (x₀ + r • (ω : E d))} with hΓdef
  set f : sphere (0 : E d) 1 → ℝ := fun ω ↦ w (x₀ + r • (ω : E d)) with hfdef
  have hfc : Continuous f := hw.continuous.comp (by fun_prop)
  have hwm : Measurable w := hw.continuous.measurable
  have hrd := measurable_radialDeriv w x₀
  -- integrability of the four sphere integrands
  have hfL : ∀ ω, |f ω| ≤ L * r := abs_apply_add_smul_le' hw hx₀ hr.le
  have hint_m : Integrable (fun ω : sphere (0 : E d) 1 ↦ w (x₀ + r • (ω : E d)) ^ 2)
      (volume : Measure (E d)).toSphere :=
    integrable_toSphere_of_bound (hwm.pow_const 2) x₀ r (B := (L * r) ^ 2) fun ω ↦ by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hfL ω) 2
  have hint_k : Integrable (fun ω : sphere (0 : E d) 1 ↦
      w (x₀ + r • (ω : E d)) * radialDeriv w x₀ (x₀ + r • (ω : E d)))
      (volume : Measure (E d)).toSphere :=
    integrable_toSphere_of_bound (hwm.mul hrd) x₀ r (B := L * r * L) fun ω ↦ by
      rw [Pi.mul_apply, abs_mul]
      exact mul_le_mul (hfL ω) (abs_radialDeriv_le hw _ _) (abs_nonneg _) (by positivity)
  have hint_a : Integrable (fun ω : sphere (0 : E d) 1 ↦ radialDeriv w x₀ (x₀ + r • (ω : E d)) ^ 2)
      (volume : Measure (E d)).toSphere :=
    integrable_toSphere_of_bound (hrd.pow_const 2) x₀ r (B := (L : ℝ) ^ 2) fun ω ↦ by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_radialDeriv_le hw _ _) 2
  have hint_q : Integrable (fun ω : sphere (0 : E d) 1 ↦ ‖∇ w (x₀ + r • (ω : E d))‖ ^ 2)
      (volume : Measure (E d)).toSphere :=
    integrable_toSphere_of_bound ((measurable_gradient w).norm.pow_const 2) x₀ r
      (B := (L : ℝ) ^ 2) fun ω ↦ by
      rw [abs_pow, abs_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_le_of_lipschitzWith hw _) 2
  -- `f` is admissible for `Γ`
  have hmpos : 0 < radialM w x₀ r := by
    rw [radialM, integral_pos_iff_support_of_nonneg (fun ω ↦ sq_nonneg _) hint_m]
    refine lt_of_lt_of_le (toSphere_pos_of_isOpen (isOpen_lt continuous_const hfc) hΓ)
      (measure_mono fun ω hω ↦ ?_)
    rw [Function.mem_support]
    exact pow_ne_zero 2 (ne_of_gt hω)
  have hadm : IsSphAdmissible Γ f :=
    ⟨⟨_, lipschitzWith_restrict hw x₀ hr.le⟩, fun ω hω ↦ le_antisymm (not_lt.mp hω) (hw0 _),
      hmpos⟩
  set lam := sphEigenvalue Γ with hlam
  have hlam0 : 0 ≤ lam := sphEigenvalue_nonneg Γ
  -- the tangential energy: `∫_𝕊 |∇f̂|² = r² (q(r) - a(r))`
  have hD : sphDirichlet f = r ^ 2 * (radialQ w x₀ r - radialA w x₀ r) := by
    unfold sphDirichlet
    rw [integral_congr_ae (g := fun ω : sphere (0 : E d) 1 ↦ r ^ 2 *
        (‖∇ w (x₀ + r • (ω : E d))‖ ^ 2 - radialDeriv w x₀ (x₀ + r • (ω : E d)) ^ 2))]
    · rw [integral_const_mul, integral_sub hint_q hint_a]
      rfl
    · filter_upwards [hdiff] with ω hω
      exact norm_sq_gradient_homogExt0_of_eq x₀ hr (fun _ ↦ rfl) ω hω
  have h1 : lam * radialM w x₀ r ≤ r ^ 2 * (radialQ w x₀ r - radialA w x₀ r) := by
    have h := hadm.sphEigenvalue_le
    have hm' : sphL2Sq f = radialM w x₀ r := rfl
    rw [sphRayleigh, hD, hm'] at h
    exact (le_div_iff₀ hmpos).mp h
  -- the completed square
  set α := charExponent d lam with hα
  have h2 : 0 ≤ r ^ 2 * radialA w x₀ r - 2 * α * r * radialK w x₀ r +
      α ^ 2 * radialM w x₀ r := by
    have hsq : ∫ ω, (r * radialDeriv w x₀ (x₀ + r • (ω : E d)) - α * w (x₀ + r • (ω : E d))) ^ 2
        ∂(volume : Measure (E d)).toSphere =
        r ^ 2 * radialA w x₀ r - 2 * α * r * radialK w x₀ r + α ^ 2 * radialM w x₀ r := by
      rw [integral_congr_ae (g := fun ω : sphere (0 : E d) 1 ↦
          (r ^ 2 * radialDeriv w x₀ (x₀ + r • (ω : E d)) ^ 2 -
            2 * α * r * (w (x₀ + r • (ω : E d)) * radialDeriv w x₀ (x₀ + r • (ω : E d)))) +
            α ^ 2 * w (x₀ + r • (ω : E d)) ^ 2) (ae_of_all _ fun ω ↦ by ring),
        integral_add (f := fun ω : sphere (0 : E d) 1 ↦
            r ^ 2 * radialDeriv w x₀ (x₀ + r • (ω : E d)) ^ 2 -
            2 * α * r * (w (x₀ + r • (ω : E d)) * radialDeriv w x₀ (x₀ + r • (ω : E d))))
          ((hint_a.const_mul _).sub (hint_k.const_mul _)) (hint_m.const_mul _),
        integral_sub (hint_a.const_mul _) (hint_k.const_mul _), integral_const_mul,
        integral_const_mul, integral_const_mul]
      rfl
    rw [← hsq]
    exact integral_nonneg fun _ ↦ sq_nonneg _
  have h3 := charExponent_sq_add (d := d) hlam0
  rw [← hα] at h3
  have h3m : (α ^ 2 + ((d : ℝ) - 2) * α) * radialM w x₀ r = lam * radialM w x₀ r := by rw [h3]
  change 2 * α * acfIntegral w x₀ r ≤ r * (r * radialQ w x₀ r)
  rw [hI]
  nlinarith [h1, h2, h3m]

/-- If `Γ_r` is empty, then `I(r) = 0`, at every radius where `I(r) = r k(r) + (d - 2)/2 m(r)`. -/
theorem acfIntegral_eq_zero_of_eq_empty (hw0 : ∀ x, 0 ≤ w x) {r : ℝ}
    (hI : acfIntegral w x₀ r = r * radialK w x₀ r + ((d : ℝ) - 2) / 2 * radialM w x₀ r)
    (hΓ : {ω : sphere (0 : E d) 1 | 0 < w (x₀ + r • (ω : E d))} = ∅) :
    acfIntegral w x₀ r = 0 := by
  have h0 : ∀ ω : sphere (0 : E d) 1, w (x₀ + r • (ω : E d)) = 0 := fun ω ↦
    le_antisymm (not_lt.mp fun h ↦ eq_empty_iff_forall_notMem.mp hΓ ω h) (hw0 _)
  rw [hI]
  simp [radialK, radialM, h0]

/-- `w` is differentiable at `x₀ + rω` for `σ`-a.e. `ω`, for a.e. `r > 0`
(Rademacher, and the transfer of a.e. statements to spheres, `ae_ae_toSphere_of_ae`). -/
theorem ae_ae_differentiableAt_add_smul (hd : 1 ≤ d) (hw : LipschitzWith L w) (x₀ : E d) :
    ∀ᵐ r : ℝ, 0 < r → ∀ᵐ ω : sphere (0 : E d) 1 ∂(volume : Measure (E d)).toSphere,
      DifferentiableAt ℝ w (x₀ + r • (ω : E d)) := by
  have := nontrivial_E hd
  have h := ae_ae_toSphere_of_ae (μ := (volume : Measure (E d))) hw.ae_differentiableAt x₀
  rw [ae_restrict_iff' measurableSet_Ioi] at h
  exact h

/-- **The key inequality, almost everywhere.** Let `w ≥ 0` be Lipschitz
and harmonic on `{w > 0}`, with `w(x₀) = 0`. For a.e. `r > 0`: if `Γ_r` is nonempty, then
`2 α_d(Γ_r) I(r) ≤ r · r q(r)` (and `I'(r) = r q(r)`, `ae_hasDerivAt_acfIntegral`). -/
theorem ae_two_mul_sphExponent_mul_acfIntegral_le (hd : 1 ≤ d) (hw : LipschitzWith L w)
    (hw0 : ∀ x, 0 ≤ w x) (hharm : HarmonicOnNhd w {x | 0 < w x}) (hx₀ : w x₀ = 0) :
    ∀ᵐ r : ℝ, 0 < r → {ω : sphere (0 : E d) 1 | 0 < w (x₀ + r • (ω : E d))}.Nonempty →
      2 * sphExponent {ω : sphere (0 : E d) 1 | 0 < w (x₀ + r • (ω : E d))} *
        acfIntegral w x₀ r ≤ r * (r * radialQ w x₀ r) := by
  filter_upwards [ae_acfIntegral_eq hd hw hw0 hharm hx₀,
    ae_ae_differentiableAt_add_smul hd hw x₀] with r hI hdiff hr hΓ
  exact two_mul_sphExponent_mul_acfIntegral_le hw hw0 hx₀ hr (hdiff hr) (hI hr) hΓ

/-- For a.e. `r > 0`: if `Γ_r` is empty, then `I(r) = 0`. -/
theorem ae_acfIntegral_eq_zero_of_eq_empty (hd : 1 ≤ d) (hw : LipschitzWith L w)
    (hw0 : ∀ x, 0 ≤ w x) (hharm : HarmonicOnNhd w {x | 0 < w x}) (hx₀ : w x₀ = 0) :
    ∀ᵐ r : ℝ, 0 < r → {ω : sphere (0 : E d) 1 | 0 < w (x₀ + r • (ω : E d))} = ∅ →
      acfIntegral w x₀ r = 0 := by
  filter_upwards [ae_acfIntegral_eq hd hw hw0 hharm hx₀] with r hI hr hΓ
  exact acfIntegral_eq_zero_of_eq_empty hw0 (hI hr) hΓ

end EllipticBernoulli
