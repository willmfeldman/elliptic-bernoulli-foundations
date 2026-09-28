/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Order.Filter.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# A continuous monotone majorant of a monotone modulus

The modulus of the Alt–Caffarelli gradient bound is first obtained as a monotone function
`g(s) = max(ℓ(s) − 1, 0)` with `g(s) → 0` as `s → 0+`, where `ℓ(s)` is a supremum of gradients
over a class of functions. `g` need not be continuous. The statement asks for a modulus that is
continuous and monotone on `[0, 1)`, so we replace `g` by its average

  `avgModulus g r = ∫_1^2 g(r s) ds  (= r⁻¹ ∫_r^{2r} g  for r > 0)`.

## Main results

* `avgModulus`: the average above.
* `exists_continuous_monotone_majorant`: for monotone `g` with `g 0 = 0` and `g(s) → 0` as
  `s → 0+`, `avgModulus g` is continuous and monotone on `[0, ∞)`, tends to `0` at `0+`, and
  dominates `g` on `[0, ∞)`.

## Proof

Monotonicity and the bounds `g r ≤ avgModulus g r ≤ g (2r)` are read off from the `∫_1^2 g(r s)`
form. Continuity at `r > 0` uses the `r⁻¹ ∫_r^{2r}` form and the continuity of the primitive of the
(locally integrable, because monotone) function `g`; continuity at `0` is the squeeze
`0 = g 0 ≤ avgModulus g r ≤ g (2r) → 0`.
-/

open Set Filter Topology MeasureTheory

public section

namespace EllipticBernoulli

/-- The averaged modulus `r ↦ ∫_1^2 g(r s) ds`, equal to `r⁻¹ ∫_r^{2r} g` for `r > 0`. -/
noncomputable def avgModulus (g : ℝ → ℝ) (r : ℝ) : ℝ := ∫ s in (1 : ℝ)..2, g (r * s)

variable {g : ℝ → ℝ}

private theorem intervalIntegrable_comp_mul (hg : Monotone g) {r : ℝ} (hr : 0 ≤ r) (a b : ℝ) :
    IntervalIntegrable (fun s ↦ g (r * s)) volume a b :=
  (hg.comp (monotone_mul_left_of_nonneg hr)).intervalIntegrable

/-- `avgModulus g r = r⁻¹ ∫_r^{2r} g` for `r ≠ 0`. -/
theorem avgModulus_eq_inv_mul (r : ℝ) (hr : r ≠ 0) :
    avgModulus g r = r⁻¹ * ∫ t in r..2 * r, g t := by
  rw [avgModulus, intervalIntegral.integral_comp_mul_left (fun t ↦ g t) hr, smul_eq_mul,
    mul_one, mul_comm r 2]

/-- `g r ≤ avgModulus g r` for `r ≥ 0`. -/
theorem le_avgModulus (hg : Monotone g) {r : ℝ} (hr : 0 ≤ r) : g r ≤ avgModulus g r := by
  have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (1 : ℝ) ≤ 2)
    intervalIntegrable_const (intervalIntegrable_comp_mul hg hr 1 2)
    (fun s hs ↦ hg (le_mul_of_one_le_right hr hs.1) : ∀ s ∈ Icc (1 : ℝ) 2, g r ≤ g (r * s))
  simpa [avgModulus, show (2 : ℝ) - 1 = 1 by norm_num] using h

/-- `avgModulus g r ≤ g (2r)` for `r ≥ 0`. -/
theorem avgModulus_le (hg : Monotone g) {r : ℝ} (hr : 0 ≤ r) : avgModulus g r ≤ g (2 * r) := by
  have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (1 : ℝ) ≤ 2)
    (intervalIntegrable_comp_mul hg hr 1 2) intervalIntegrable_const
    (fun s hs ↦ hg (by nlinarith [hs.2]) : ∀ s ∈ Icc (1 : ℝ) 2, g (r * s) ≤ g (2 * r))
  simpa [avgModulus, show (2 : ℝ) - 1 = 1 by norm_num] using h

/-- `avgModulus g` is monotone on `[0, ∞)`. -/
theorem monotoneOn_avgModulus (hg : Monotone g) : MonotoneOn (avgModulus g) (Ici 0) := by
  intro a ha b hb hab
  exact intervalIntegral.integral_mono_on (by norm_num) (intervalIntegrable_comp_mul hg ha 1 2)
    (intervalIntegrable_comp_mul hg (le_trans ha hab) 1 2)
    fun s hs ↦ hg (mul_le_mul_of_nonneg_right hab (by linarith [hs.1]))

/-- `avgModulus g` is continuous at every `r > 0`. -/
theorem continuousAt_avgModulus (hg : Monotone g) {r : ℝ} (hr : 0 < r) :
    ContinuousAt (avgModulus g) r := by
  set G : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, g t with hG
  have hGc : Continuous G :=
    intervalIntegral.continuous_primitive (fun _ _ ↦ hg.intervalIntegrable) 0
  have heq : (fun x ↦ x⁻¹ * (G (2 * x) - G x)) =ᶠ[𝓝 r] avgModulus g := by
    filter_upwards [lt_mem_nhds hr] with x hx
    rw [avgModulus_eq_inv_mul x hx.ne', hG,
      intervalIntegral.integral_interval_sub_left hg.intervalIntegrable hg.intervalIntegrable]
  refine ContinuousAt.congr ?_ heq
  exact (continuousAt_inv₀ hr.ne').mul
    ((hGc.comp (continuous_const.mul continuous_id)).sub hGc).continuousAt

/-- **Continuous monotone majorant.** If `g` is monotone with `g 0 = 0` and `g(s) → 0` as
`s → 0+`, then `avgModulus g` is continuous and monotone on `[0, ∞)`, vanishes at `0`, tends to
`0` at `0+`, and dominates `g` on `[0, ∞)`. -/
theorem exists_continuous_monotone_majorant (hg : Monotone g) (hg0 : g 0 = 0)
    (hlim : Tendsto g (𝓝[>] 0) (𝓝 0)) :
    ContinuousOn (avgModulus g) (Ici 0) ∧ MonotoneOn (avgModulus g) (Ici 0) ∧
      avgModulus g 0 = 0 ∧ Tendsto (avgModulus g) (𝓝[>] 0) (𝓝 0) ∧
      ∀ r, 0 ≤ r → g r ≤ avgModulus g r := by
  have hw0 : avgModulus g 0 = 0 := by simp [avgModulus, hg0]
  -- continuity within `[0, ∞)` at `0`, by the squeeze `g r ≤ w r ≤ g (2r)`
  have hgc : ContinuousWithinAt g (Ici 0) 0 := by
    rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, hg0]
    exact hlim
  have hg2 : Tendsto (fun r ↦ g (2 * r)) (𝓝[Ici 0] 0) (𝓝 0) := by
    have h2 : Tendsto (fun r : ℝ ↦ 2 * r) (𝓝[Ici 0] 0) (𝓝[Ici 0] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun r hr ↦ ?_⟩
      · have := ((continuous_const_mul (2 : ℝ)).tendsto (0 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := Ici 0))
        simpa using this
      · exact mem_Ici.2 (by have := mem_Ici.1 hr; positivity)
    have h := hgc.tendsto.comp h2
    rwa [hg0] at h
  have hw : ContinuousWithinAt (avgModulus g) (Ici 0) 0 := by
    rw [ContinuousWithinAt, hw0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := g) ?_ hg2 ?_ ?_
    · have := hgc.tendsto; rwa [hg0] at this
    · filter_upwards [self_mem_nhdsWithin] with r hr using le_avgModulus hg hr
    · filter_upwards [self_mem_nhdsWithin] with r hr using avgModulus_le hg hr
  refine ⟨fun r hr ↦ ?_, monotoneOn_avgModulus hg, hw0, ?_,
    fun r hr ↦ le_avgModulus hg hr⟩
  · rcases (mem_Ici.1 hr).lt_or_eq with hr | hr
    · exact (continuousAt_avgModulus hg hr).continuousWithinAt
    · subst hr; exact hw
  · have := (hw.mono Ioi_subset_Ici_self).tendsto
    rwa [hw0] at this

end EllipticBernoulli
