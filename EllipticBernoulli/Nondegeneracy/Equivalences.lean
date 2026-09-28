/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.Nondegeneracy

/-!
# Equivalent forms of non-degeneracy (Abedin–Feldman–Stinson, Lemma B.3)

`nondegenerate_sup_iff_average` (`NondegEquivStatement`): for `u ≥ 0` that is `L`-Lipschitz on
`B_1(x₀)`, the sphere-average form `⨍_{∂B_r(x₀)} u ≥ c r` and the sphere-sup form
`sup_{∂B_r(x₀)} u ≥ c r` (for all `0 < r < 1`) imply each other, with a constant `c'` depending only
on `c`, `d` and `L`. Explicitly, `c' = min (c / 2) (c / 2 · b_d(ε) / d)` with
`ε = c / (2(L + 1))` and `b_d(ε) = toSphereBallBound d ε` (Mathlib's lower bound for the
`volume.toSphere` measure of an `ε`-cap, relative to `|B_1|`).

## Proof

* average ⇒ sup: the average of a function `≤ c r / 2` everywhere is `≤ c r / 2`.
* sup ⇒ average: if `u(x₀ + r e) ≥ c r` with `|e| = 1`, the Lipschitz bound gives
  `u(x₀ + r z) ≥ c r / 2` on the cap `{z : |z - e| < ε}`, whose `toSphere` measure is at least
  `b_d(ε) |B_1|` (`toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball`), while the total
  mass is `d |B_1|` (`toSphere_real_apply_univ`).

Harmonicity in `{u > 0}` and the free boundary hypothesis are not used. The source says the
constants depend on `c`, `d` and `L`, but its hypothesis says only "Lipschitz continuous"; here the
Lipschitz constant `L` is explicit. Only (i)⇔(ii) is treated in general dimension; the form (iii),
a lower bound on the mass of `Δu`, is treated in `d = 2`, at a single radius
(`IsRieszMeasure.mass_lower_bound`, `IsRieszMeasure.circleMean_lower_bound`).

## References

* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
  in the Bernoulli one-phase problem*, arXiv:2609.14981.
-/

open Set Filter Topology MeasureTheory Metric

public section

namespace EllipticBernoulli

variable {d : ℕ}

private theorem mem_ball_of_sphere {x₀ : E d} {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1)
    (z : sphere (0 : E d) 1) : x₀ + r • (z : E d) ∈ ball x₀ 1 := by
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_pos hr.1, norm_eq_of_mem_sphere z, mul_one]
  exact hr.2

/-- The pull-back `z ↦ u (x₀ + r z)` to the unit sphere is integrable when `u` is continuous on
`B_1(x₀)` and `0 < r < 1`. -/
private theorem integrable_sphere_pullback {u : E d → ℝ} {x₀ : E d} {r : ℝ}
    (hu : ContinuousOn u (ball x₀ 1)) (hr : r ∈ Ioo (0 : ℝ) 1) :
    Integrable (fun z : sphere (0 : E d) 1 ↦ u (x₀ + r • (z : E d)))
      (volume : Measure (E d)).toSphere :=
  (hu.comp_continuous (by fun_prop) (mem_ball_of_sphere hr)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- An average bounded pointwise from above by a nonnegative constant is bounded by it. -/
private theorem average_sphere_le {f : sphere (0 : E d) 1 → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ z, f z ≤ M) (hfi : Integrable f (volume : Measure (E d)).toSphere) :
    ⨍ z, f z ∂(volume : Measure (E d)).toSphere ≤ M := by
  set μ := (volume : Measure (E d)).toSphere
  rw [average_eq, smul_eq_mul]
  have h1 : ∫ z, f z ∂μ ≤ μ.real univ * M := by
    calc ∫ z, f z ∂μ ≤ ∫ _z, M ∂μ := integral_mono hfi (integrable_const M) hf
      _ = μ.real univ * M := by rw [integral_const, smul_eq_mul]
  rcases (measureReal_nonneg (μ := μ) (s := univ)).eq_or_lt with h0 | hpos
  · rw [← h0, inv_zero, zero_mul]; exact hM
  · calc (μ.real univ)⁻¹ * ∫ z, f z ∂μ ≤ (μ.real univ)⁻¹ * (μ.real univ * M) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hpos.le)
      _ = M := by field_simp

/-- **Abedin–Feldman–Stinson, Lemma B.3 (i)⇔(ii)** (`NondegEquivStatement`), with
`c' = min (c/2) (c/2 · toSphereBallBound d (c/(2(L+1))) / d)`. Assumes `1 ≤ d`.
Harmonicity in `{u > 0}` and `x₀ ∈ ∂{u > 0}` are not used. -/
theorem nondegenerate_sup_iff_average : NondegEquivStatement := by
  intro d hd L c hc
  set ε : ℝ := c / (2 * ((L : ℝ) + 1)) with hε_def
  have hε : 0 < ε := by positivity
  set b : ℝ := (Measure.toSphereBallBound d ε : ℝ) with hb_def
  have hb : 0 < b := by rw [hb_def]; exact_mod_cast Measure.toSphereBallBound_pos d ε
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨min (c / 2) (c / 2 * b / d), lt_min (by positivity) (by positivity), ?_⟩
  intro u x₀ hu0 hL _ _
  have hcont : ContinuousOn u (ball x₀ 1) := hL.continuousOn
  refine ⟨fun hav r hr ↦ ?_, fun hsup r hr ↦ ?_⟩
  · -- average ⇒ sup
    by_contra hcon
    simp only [not_exists, not_and, not_le] at hcon
    have hle : ∀ z : sphere (0 : E d) 1, u (x₀ + r • (z : E d)) ≤ c / 2 * r := by
      intro z
      have hz : x₀ + r • (z : E d) ∈ sphere x₀ r := by
        rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hr.1, norm_eq_of_mem_sphere z, mul_one]
      exact (hcon _ hz).le.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hr.1.le)
    have h1 := average_sphere_le (mul_nonneg (by positivity) hr.1.le) hle
      (integrable_sphere_pullback hcont hr)
    have h2 := hav r hr
    linarith [mul_pos hc hr.1]
  · -- sup ⇒ average
    obtain ⟨y, hy, hyc⟩ := hsup r hr
    rw [mem_sphere, dist_eq_norm] at hy
    set e : E d := r⁻¹ • (y - x₀) with he_def
    have he : ‖e‖ = 1 := by
      rw [he_def, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr.1, hy,
        inv_mul_cancel₀ hr.1.ne']
    have hye : y = x₀ + r • e := by
      rw [he_def, smul_smul, mul_inv_cancel₀ hr.1.ne', one_smul, add_sub_cancel]
    let e' : sphere (0 : E d) 1 := ⟨e, by rw [mem_sphere_zero_iff_norm]; exact he⟩
    set μ := (volume : Measure (E d)).toSphere
    set f : sphere (0 : E d) 1 → ℝ := fun z ↦ u (x₀ + r • (z : E d))
    have hfi : Integrable f μ := integrable_sphere_pullback hcont hr
    have hf0 : ∀ z, 0 ≤ f z := fun z ↦ hu0 _ (mem_ball_of_sphere hr z)
    -- on the cap, `f ≥ c r / 2`
    have hcap : ∀ z ∈ ball e' ε, c / 2 * r ≤ f z := by
      intro z hz
      rw [mem_ball, Subtype.dist_eq, dist_eq_norm] at hz
      have hyB : y ∈ ball x₀ 1 := by rw [mem_ball, dist_eq_norm, hy]; exact hr.2
      have hLip := hL.dist_le_mul _ (mem_ball_of_sphere hr z) _ hyB
      rw [Real.dist_eq, dist_eq_norm, hye, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
        Real.norm_eq_abs, abs_of_pos hr.1] at hLip
      have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
      have hbound : (L : ℝ) * (r * ‖(z : E d) - e‖) ≤ c / 2 * r := by
        have h1 : (L : ℝ) * ‖(z : E d) - e‖ ≤ c / 2 := by
          calc (L : ℝ) * ‖(z : E d) - e‖ ≤ ((L : ℝ) + 1) * ε :=
                mul_le_mul (by linarith) hz.le (norm_nonneg _) (by positivity)
            _ = c / 2 := by rw [hε_def]; field_simp
        linarith [mul_le_mul_of_nonneg_left h1 hr.1.le]
      have := (abs_le.1 hLip).1
      change c / 2 * r ≤ u (x₀ + r • (z : E d))
      rw [← hye] at this
      linarith
    have hcapμ : b * (volume : Measure (E d)).real (ball 0 1) ≤ μ.real (ball e' ε) := by
      have := Measure.toSphereBallBound_mul_measureReal_unitBall_le_toSphere_ball
        (volume : Measure (E d)) hε e'
      rwa [finrank_euclideanSpace_fin] at this
    have hint : c / 2 * r * μ.real (ball e' ε) ≤ ∫ z, f z ∂μ := by
      calc c / 2 * r * μ.real (ball e' ε) ≤ ∫ z in ball e' ε, f z ∂μ := by
            exact setIntegral_ge_of_const_le_real measurableSet_ball (measure_ne_top _ _) hcap
              hfi.integrableOn
        _ ≤ ∫ z, f z ∂μ := setIntegral_le_integral hfi (Eventually.of_forall hf0)
    have hvol : 0 < (volume : Measure (E d)).real (ball 0 1) := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
    have htot : μ.real univ = d * (volume : Measure (E d)).real (ball 0 1) := by
      rw [Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin]
    change min (c / 2) (c / 2 * b / d) * r ≤ ⨍ z, f z ∂μ
    rw [average_eq, smul_eq_mul, htot]
    set V := (volume : Measure (E d)).real (ball 0 1)
    calc min (c / 2) (c / 2 * b / d) * r ≤ c / 2 * b / d * r :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hr.1.le
      _ = (↑d * V)⁻¹ * (c / 2 * r * (b * V)) := by field_simp
      _ ≤ (↑d * V)⁻¹ * ∫ z, f z ∂μ := by
          refine mul_le_mul_of_nonneg_left (le_trans ?_ hint)
            (inv_nonneg.2 (mul_nonneg hdR.le hvol.le))
          exact mul_le_mul_of_nonneg_left hcapμ (mul_nonneg (by positivity) hr.1.le)

end EllipticBernoulli
