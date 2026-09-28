/-
Copyright (c) 2026 The Tau Ceti contributors, William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, William M. Feldman
-/
module

public import EllipticBernoulli.Harmonic.Basic

/-!
# Mean-value property of harmonic functions

Let `E` be a finite-dimensional real inner product space with an additive Haar measure `μ`.

* `HarmonicOnNhd.integral_toSphere_eq`: the sphere mean-value property,
  `∫_{S} u (x₀ + R θ) dσ(θ) = σ(S) u(x₀)` for `u` harmonic near `closedBall x₀ R`.
* `HarmonicOnNhd.setIntegral_ball_eq`: the mean-value property on balls,
  `∫_{B_R(x₀)} u = |B_R| u(x₀)` for `u` harmonic on a neighbourhood of `closedBall x₀ R`.
* `HarmonicOnNhd.le_div_pow_mul_of_nonneg`: nested balls compare values of a nonnegative
  harmonic function, `u x ≤ (s / r) ^ n * u y` when `r + dist x y ≤ s`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer, Berlin, 2001 (reprint of the 1998 edition), Theorem 2.1.

## Provenance

* Upstream: TauCeti, https://github.com/TauCetiProject/TauCeti, paths
  `TauCeti/Analysis/PDE/Harnack/Basic.lean`,
  `TauCeti/Analysis/InnerProductSpace/Harmonic/MeanValue.lean`,
  commit 90cca67c0c8e91cd30b0d46cb58101f8c5c59236. License: Apache-2.0. Upstream notice:
  `Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.`
* Extent: `HarmonicOnNhd.le_div_pow_mul_of_nonneg` (unchanged up to the namespace);
  `HarmonicOnNhd.setIntegral_ball_eq` (adapted from
  `setIntegral_ball_eq_of_harmonicOnNhd_zero` and `HarmonicOnNhd.setIntegral_ball_eq`).
* Changes: namespace changed to `EllipticBernoulli`; the weak-harmonicity API replaced by
  `ViscositySolns.Analysis.` names; module form. `HarmonicOnNhd.integral_toSphere_eq` is a new
  wrapper.
-/

open InnerProductSpace MeasureTheory Metric Module Set Filter Topology
open scoped ContDiff Laplacian
open ViscositySolns.Analysis (WeaklyHarmonicOn integral_toSphere_eq_of_weaklyHarmonic
  integral_eq_integral_Ioi_integral_toSphere)

public section

namespace EllipticBernoulli

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Measure

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **The sphere mean-value property.** If `u` is harmonic on a neighbourhood of
`closedBall x₀ R` (`R ≥ 0`), then its integral over the sphere of radius `R` about `x₀`
(parametrized by the unit sphere with the surface measure `μ.toSphere`) is `σ(S) u(x₀)`. -/
theorem HarmonicOnNhd.integral_toSphere_eq [Nontrivial E] {u : E → ℝ} {x₀ : E} {R : ℝ}
    (hu : HarmonicOnNhd u (closedBall x₀ R)) (hR : 0 ≤ R) :
    ∫ θ : sphere (0 : E) 1, u (x₀ + R • (θ : E)) ∂μ.toSphere = μ.toSphere.real univ * u x₀ := by
  set U := {x : E | HarmonicAt u x}
  have hU : IsOpen U := isOpen_setOf_harmonicAt u
  have huU : HarmonicOnNhd u U := fun x hx ↦ hx
  simpa [smul_eq_mul] using integral_toSphere_eq_of_weaklyHarmonic hU
    huU.contDiffOn.continuousOn (HarmonicOnNhd.weaklyHarmonicOn (μ := μ) hU huU)
    (fun x hx ↦ hu x hx) hR

/-- The mean-value property on balls, for a weakly harmonic function, centred form. -/
private lemma setIntegral_ball_zero_add_eq [Nontrivial E] {U : Set E} (hU : IsOpen U)
    {u : E → ℝ} (hcont : ContinuousOn u U) (hu : WeaklyHarmonicOn μ u U) {x₀ : E} {R : ℝ}
    (hΩ : closedBall x₀ R ⊆ U) (hR : 0 < R) :
    ∫ y in ball (0 : E) R, u (x₀ + y) ∂μ = μ.real (ball (0 : E) R) * u x₀ := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (Module.finrank_pos (R := ℝ) (M := E)).ne'
  set v : E → ℝ := fun y ↦ u (x₀ + y) with hv
  have hvcont : ContinuousOn v (closedBall (0 : E) R) :=
    (hcont.mono hΩ).comp (continuous_const.add continuous_id).continuousOn fun y hy ↦ by
      rw [mem_closedBall, dist_eq_norm] at hy ⊢
      simpa using hy
  have hint : Integrable ((ball (0 : E) R).indicator v) μ :=
    ((hvcont.integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall).integrable_indicator measurableSet_ball
  rw [← integral_indicator measurableSet_ball, integral_eq_integral_Ioi_integral_toSphere _ hint]
  have hinner : ∀ s ∈ Ioi (0 : ℝ), s ^ (Module.finrank ℝ E - 1) •
      ∫ θ : sphere (0 : E) 1, (ball (0 : E) R).indicator v (s • (θ : E)) ∂μ.toSphere =
        (Iio R).indicator (fun s ↦ s ^ (Module.finrank ℝ E - 1) • (μ.toSphere.real univ • u x₀))
          s := by
    intro s hs
    have hs : 0 < s := hs
    have hmem : ∀ θ : sphere (0 : E) 1, s • (θ : E) ∈ ball (0 : E) R ↔ s < R := fun θ ↦ by
      rw [mem_ball_zero_iff, norm_smul, norm_eq_of_mem_sphere θ, mul_one, Real.norm_of_nonneg hs.le]
    by_cases hsR : s < R
    · rw [indicator_of_mem (mem_Iio.mpr hsR)]
      simp_rw [indicator_of_mem ((hmem _).mpr hsR)]
      rw [hv, integral_toSphere_eq_of_weaklyHarmonic hU hcont hu
        ((closedBall_subset_closedBall hsR.le).trans hΩ) hs.le]
    · rw [indicator_of_notMem (by simpa using hsR)]
      simp_rw [indicator_of_notMem ((not_congr (hmem _)).mpr hsR)]
      simp
  have hball : μ.real (ball (0 : E) R) = R ^ (m + 1) * μ.real (ball (0 : E) 1) := by
    rw [measureReal_def, Measure.addHaar_ball μ _ hR.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), hm, measureReal_def]
  have hsph : μ.toSphere.real univ = ((m : ℝ) + 1) * μ.real (ball (0 : E) 1) := by
    rw [Measure.toSphere_real_apply_univ, hm]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hinner, setIntegral_indicator measurableSet_Iio,
    Ioi_inter_Iio, integral_smul_const, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hR.le, integral_pow, hball, hsph, smul_smul, hm,
    Nat.add_sub_cancel, zero_pow (Nat.succ_ne_zero m), sub_zero, smul_eq_mul]
  field_simp

/-- **The mean-value property on balls.** If `u` is harmonic on a neighbourhood of the closed
ball `closedBall x₀ R`, then `∫_{B_R(x₀)} u = |B_R| u(x₀)`. (For `R ≤ 0` both sides vanish.) -/
theorem HarmonicOnNhd.setIntegral_ball_eq {u : E → ℝ} {x₀ : E} {R : ℝ}
    (hu : HarmonicOnNhd u (closedBall x₀ R)) :
    ∫ x in ball x₀ R, u x ∂μ = μ.real (ball x₀ R) * u x₀ := by
  rcases le_or_gt R 0 with hR | hR
  · simp [ball_eq_empty.mpr hR]
  rcases subsingleton_or_nontrivial E with hE | hE
  · rw [setIntegral_congr_fun measurableSet_ball (g := fun _ ↦ u x₀)
      fun x _ ↦ congrArg u (Subsingleton.elim x x₀), setIntegral_const, smul_eq_mul]
  -- the harmonic points form an open set containing the closed ball
  set U := {x : E | HarmonicAt u x}
  have hU : IsOpen U := isOpen_setOf_harmonicAt u
  have hΩ : closedBall x₀ R ⊆ U := fun x hx ↦ hu x hx
  have huU : HarmonicOnNhd u U := fun x hx ↦ hx
  have h := setIntegral_ball_zero_add_eq hU huU.contDiffOn.continuousOn
    (HarmonicOnNhd.weaklyHarmonicOn (μ := μ) hU huU) hΩ hR
  rw [Measure.addHaar_real_ball_center, ← h, ← integral_indicator measurableSet_ball,
    ← integral_indicator measurableSet_ball, ← integral_add_left_eq_self _ x₀]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  classical
  simp only [indicator_apply, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]

end Measure

variable {u : E → ℝ} {x y : E} {r s : ℝ}

/-- **Nested balls compare the values of a nonnegative harmonic function.** If `u` is harmonic
on a neighbourhood of `closedBall y s` and nonnegative on `ball y s`, and `closedBall x r` lies
inside `closedBall y s` in the sense that `r + dist x y ≤ s`, then
`u x ≤ (s / r) ^ n * u y`, where `n` is the dimension of `E`. -/
theorem HarmonicOnNhd.le_div_pow_mul_of_nonneg
    (hu : HarmonicOnNhd u (closedBall y s)) (hnonneg : ∀ z ∈ ball y s, 0 ≤ u z) (hr : 0 < r)
    (hxy : r + dist x y ≤ s) :
    u x ≤ (s / r) ^ finrank ℝ E * u y := by
  borelize E
  set μ : Measure E := Measure.addHaar
  have hs : 0 < s := hr.trans_le ((le_add_of_nonneg_right dist_nonneg).trans hxy)
  have hint : IntegrableOn u (ball y s) μ :=
    (hu.contDiffOn.continuousOn.integrableOn_compact (isCompact_closedBall y s)).mono_set
      ball_subset_closedBall
  have hle : ∫ z in ball x r, u z ∂μ ≤ ∫ z in ball y s, u z ∂μ :=
    setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_ball).2 (ae_of_all _ hnonneg))
      (ball_subset_ball' hxy).eventuallyLE
  rw [HarmonicOnNhd.setIntegral_ball_eq (hu.mono (closedBall_subset_closedBall' hxy)),
    HarmonicOnNhd.setIntegral_ball_eq hu] at hle
  simp only [measureReal_def, μ.addHaar_ball_of_pos x hr,
    μ.addHaar_ball_of_pos y hs, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _), ENNReal.toReal_ofReal (pow_nonneg hs.le _)] at hle
  have hB : 0 < (μ (ball 0 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  refine le_of_mul_le_mul_left ?_ hB
  nlinarith [hle]

end EllipticBernoulli
