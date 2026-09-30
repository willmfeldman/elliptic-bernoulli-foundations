/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Harmonic.MeanValue
public import EllipticBernoulli.Harmonic.Comparison
public import EllipticBernoulli.Harmonic.ViscosityHarmonic
import ViscositySolns.Applications.Laplace.Weyl.PolarCoord

/-!
# Sphere mean values up to the boundary; the sub-mean-value property

Spheres are parametrized by the unit sphere with the surface measure `μ.toSphere` of an additive
Haar measure `μ`, as in `ViscositySolns.Analysis.integral_toSphere_eq_of_weaklyHarmonic`.

* `integral_toSphere_eq_of_continuousOn_closedBall`: if `h` is continuous on `closedBall x r` and
  harmonic in `ball x r`, then `∫ h (x + r θ) dσ(θ) = σ(S) h(x)`. (The mean value property up to
  the boundary sphere, by continuity in the radius.) In particular the Dirichlet solution of
  `exists_harmonic_ball_boundary` with data `g` satisfies `σ(S) h(x) = ∫ g (x + r θ) dσ(θ)`.
* `IsViscSubharmonicOn.le_integral_toSphere` (sub-mean value):
  `σ(S) w(x) ≤ ∫ w (x + r θ) dσ(θ)` for `w` continuous and viscosity subharmonic on
  `Ω ⊇ closedBall x r`. `IsViscSuperharmonicOn.integral_toSphere_le` is the dual.
* `le_setIntegral_ball_of_le_integral_toSphere`: sphere inequalities for all radii `s < r`
  integrate (polar coordinates) to the ball inequality `μ(B_r) f(x) ≤ ∫_{B_r(x)} f`.
* `IsViscSubharmonicOn.le_setIntegral_ball`: `μ(B_r) w(x) ≤ ∫_{B_r(x)} w`;
  `IsViscSuperharmonicOn.setIntegral_ball_le` is the dual.

## Proof of the sub-mean value property

Let `h` solve the Dirichlet problem on `ball x r` with data `w` (`exists_harmonic_ball_boundary`).
By comparison `w ≤ h` on `closedBall x r`, and `σ(S) h(x) = ∫ h (x + r θ) = ∫ w (x + r θ)`.
-/

open InnerProductSpace MeasureTheory Metric Module Set Filter Topology
open scoped ContDiff Laplacian

public section

namespace EllipticBernoulli

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] [Nontrivial E]

/-- **Sphere mean value up to the boundary.** If `h` is continuous on `closedBall x r` and
harmonic in `ball x r` (`r ≥ 0`), then `∫ h (x + r θ) dσ(θ) = σ(S) h(x)`. -/
theorem integral_toSphere_eq_of_continuousOn_closedBall {h : E → ℝ} {x : E} {r : ℝ}
    (hr : 0 ≤ r) (hc : ContinuousOn h (closedBall x r)) (hh : HarmonicOnNhd h (ball x r)) :
    ∫ θ : sphere (0 : E) 1, h (x + r • (θ : E)) ∂μ.toSphere = μ.toSphere.real univ * h x := by
  set c := μ.toSphere.real univ * h x
  set F : ℝ → ℝ := fun s ↦ ∫ θ : sphere (0 : E) 1, h (x + s • (θ : E)) ∂μ.toSphere with hF
  rcases hr.eq_or_lt with rfl | hr
  · simp [integral_const, smul_eq_mul, c]
  -- `F` is continuous on `[0, r]`
  have hFc : ContinuousOn F (Icc 0 r) := by
    have hc' : ContinuousOn (fun y ↦ h (x + y)) (closedBall (0 : E) r) :=
      hc.comp (continuous_const.add continuous_id).continuousOn fun y hy ↦ by
        rw [mem_closedBall, dist_eq_norm] at hy ⊢
        simpa using hy
    exact ViscositySolns.Analysis.continuousOn_integral_toSphere_smul (μ := μ) hc'
  -- `F = c` on `[0, r)`
  have hFeq : ∀ s ∈ Ico 0 r, F s = c := fun s hs ↦
    HarmonicOnNhd.integral_toSphere_eq (hh.mono (closedBall_subset_ball hs.2)) hs.1
  have hmem : F r ∈ closure (F '' Ico 0 r) :=
    ((hFc r ⟨hr.le, le_rfl⟩).mono Ico_subset_Icc_self).mem_closure_image
      (by rw [closure_Ico hr.ne]; exact ⟨hr.le, le_rfl⟩)
  have hsub : F '' Ico 0 r ⊆ {c} := by
    rintro _ ⟨s, hs, rfl⟩
    exact hFeq s hs
  have := closure_mono hsub hmem
  rwa [closure_singleton, mem_singleton_iff] at this

/-- **From spheres to balls.** If `f` is continuous on `closedBall x r` (`0 < r`) and
`σ(S) f(x) ≤ ∫ f (x + s θ) dσ(θ)` for every `0 < s < r`, then `μ(B_r) f(x) ≤ ∫_{B_r(x)} f`.
(Integration in polar coordinates, as in `HarmonicOnNhd.setIntegral_ball_eq`.) -/
theorem le_setIntegral_ball_of_le_integral_toSphere {f : E → ℝ} {x : E} {r : ℝ} (hr : 0 < r)
    (hf : ContinuousOn f (closedBall x r))
    (hle : ∀ s, 0 < s → s < r →
      μ.toSphere.real univ * f x ≤ ∫ θ : sphere (0 : E) 1, f (x + s • (θ : E)) ∂μ.toSphere) :
    μ.real (ball x r) * f x ≤ ∫ y in ball x r, f y ∂μ := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (Module.finrank_pos (R := ℝ) (M := E)).ne'
  set v : E → ℝ := fun y ↦ f (x + y) with hv
  have hvcont : ContinuousOn v (closedBall (0 : E) r) :=
    hf.comp (continuous_const.add continuous_id).continuousOn fun y hy ↦ by
      rw [mem_closedBall, dist_eq_norm] at hy ⊢
      simpa using hy
  -- translate to the centred ball
  have htrans : ∫ y in ball x r, f y ∂μ = ∫ y in ball (0 : E) r, v y ∂μ := by
    rw [← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball,
      ← integral_add_left_eq_self _ x]
    refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
    classical
    simp only [indicator_apply, mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero, hv]
  have hint : Integrable ((ball (0 : E) r).indicator v) μ :=
    ((hvcont.integrableOn_compact (isCompact_closedBall _ _)).mono_set
      ball_subset_closedBall).integrable_indicator measurableSet_ball
  set F : ℝ → ℝ := fun s ↦ ∫ θ : sphere (0 : E) 1, v (s • (θ : E)) ∂μ.toSphere with hF
  have hFc : ContinuousOn F (Icc 0 r) :=
    ViscositySolns.Analysis.continuousOn_integral_toSphere_smul hvcont
  have hmem : ∀ s, 0 < s → ∀ θ : sphere (0 : E) 1, s • (θ : E) ∈ ball (0 : E) r ↔ s < r :=
    fun s hs θ ↦ by
      rw [mem_ball_zero_iff, norm_smul, norm_eq_of_mem_sphere θ, mul_one,
        Real.norm_of_nonneg hs.le]
  have hG : ∀ s ∈ Ioi (0 : ℝ), s ^ (finrank ℝ E - 1) •
      ∫ θ : sphere (0 : E) 1, (ball (0 : E) r).indicator v (s • (θ : E)) ∂μ.toSphere =
        (Iio r).indicator (fun s ↦ s ^ (finrank ℝ E - 1) * F s) s := by
    intro s hs
    have hs : 0 < s := hs
    by_cases hsr : s < r
    · rw [indicator_of_mem (mem_Iio.2 hsr)]
      simp_rw [indicator_of_mem ((hmem s hs _).2 hsr)]
      rfl
    · rw [indicator_of_notMem (by simpa using hsr)]
      simp_rw [indicator_of_notMem ((not_congr (hmem s hs _)).2 hsr)]
      simp
  rw [htrans, ← integral_indicator measurableSet_ball,
    ViscositySolns.Analysis.integral_eq_integral_Ioi_integral_toSphere _ hint,
    setIntegral_congr_fun measurableSet_Ioi hG, setIntegral_indicator measurableSet_Iio,
    Ioi_inter_Iio]
  -- the left side as an integral over `(0, r)`
  have hball : μ.real (ball (0 : E) r) = r ^ (m + 1) * μ.real (ball (0 : E) 1) := by
    rw [measureReal_def, Measure.addHaar_ball μ _ hr.le, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity), hm, measureReal_def]
  have hsph : μ.toSphere.real univ = ((m : ℝ) + 1) * μ.real (ball (0 : E) 1) := by
    rw [Measure.toSphere_real_apply_univ, hm]
    push_cast
    ring
  have hval : μ.real (ball x r) * f x =
      ∫ s in Ioo 0 r, s ^ (finrank ℝ E - 1) * (μ.toSphere.real univ * f x) ∂volume := by
    rw [integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hr.le, integral_pow, Measure.addHaar_real_ball_center,
      hball, hsph, hm, Nat.add_sub_cancel, zero_pow (Nat.succ_ne_zero m), sub_zero]
    field_simp
  rw [hval]
  refine setIntegral_mono_on ?_ ?_ measurableSet_Ioo fun s hs ↦ ?_
  · exact ((continuous_pow _).mul continuous_const).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  · exact (((continuous_pow _).continuousOn).mul hFc).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  · exact mul_le_mul_of_nonneg_left (hle s hs.1 hs.2) (pow_nonneg hs.1.le _)

end General

variable {d : ℕ} {μ : Measure (E d)} [μ.IsAddHaarMeasure]

/-- **Sub-mean-value property of viscosity subharmonic functions.** If `w` is continuous and
viscosity subharmonic on a set `Ω ⊇ closedBall x r` (`1 ≤ d`, `0 < r`), then
`σ(S) w(x) ≤ ∫ w (x + r θ) dσ(θ)`. -/
theorem IsViscSubharmonicOn.le_integral_toSphere (hd : 1 ≤ d) {Ω : Set (E d)}
    {w : E d → ℝ} (hw : IsViscSubharmonicOn w Ω) (hwc : ContinuousOn w Ω) {x : E d} {r : ℝ}
    (hr : 0 < r) (hB : closedBall x r ⊆ Ω) :
    μ.toSphere.real univ * w x ≤ ∫ θ : sphere (0 : E d) 1, w (x + r • (θ : E d)) ∂μ.toSphere := by
  have := nontrivial_E_of_one_le hd
  obtain ⟨h, hhc, hhh, hhw⟩ := exists_harmonic_ball_boundary hd x r w hr
    (hwc.mono (sphere_subset_closedBall.trans hB))
  have hcl : closure (ball x r) = closedBall x r := closure_ball x hr.ne'
  have hfr : frontier (ball x r) = sphere x r := frontier_ball x hr.ne'
  have hle : ∀ y ∈ closure (ball x r), w y ≤ h y :=
    IsViscSubharmonicOn.le_of_frontier_le hd isOpen_ball isBounded_ball
      (by rw [hcl]; exact hwc.mono hB) (hw.mono isOpen_ball (ball_subset_closedBall.trans hB))
      (by rwa [hcl]) hhh (fun y hy ↦ by rw [hfr] at hy; rw [hhw hy])
  have hmean := integral_toSphere_eq_of_continuousOn_closedBall (μ := μ) hr.le hhc hhh
  have hon : ∀ θ : sphere (0 : E d) 1, x + r • (θ : E d) ∈ sphere x r := fun θ ↦ by
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_eq_of_mem_sphere θ,
      Real.norm_of_nonneg hr.le, mul_one]
  have hint : ∫ θ : sphere (0 : E d) 1, h (x + r • (θ : E d)) ∂μ.toSphere =
      ∫ θ : sphere (0 : E d) 1, w (x + r • (θ : E d)) ∂μ.toSphere :=
    integral_congr_ae (Eventually.of_forall fun θ ↦ hhw (hon θ))
  rw [← hint, hmean]
  exact mul_le_mul_of_nonneg_left (hle x (subset_closure (mem_ball_self hr)))
    measureReal_nonneg

/-- **Super-mean-value property of viscosity superharmonic functions** (dual of
`IsViscSubharmonicOn.le_integral_toSphere`). -/
theorem IsViscSuperharmonicOn.integral_toSphere_le (hd : 1 ≤ d) {Ω : Set (E d)}
    {w : E d → ℝ} (hw : IsViscSuperharmonicOn w Ω) (hwc : ContinuousOn w Ω)
    {x : E d} {r : ℝ} (hr : 0 < r) (hB : closedBall x r ⊆ Ω) :
    ∫ θ : sphere (0 : E d) 1, w (x + r • (θ : E d)) ∂μ.toSphere ≤ μ.toSphere.real univ * w x := by
  have hwc' : ContinuousOn (-w) Ω := hwc.neg
  have := IsViscSubharmonicOn.le_integral_toSphere (μ := μ) hd hw.neg hwc' hr hB
  simp only [Pi.neg_apply, integral_neg, mul_neg] at this
  linarith

/-- **Sub-mean-value property on balls.** If `w` is continuous and viscosity subharmonic on a set
`Ω ⊇ closedBall x r` (`1 ≤ d`, `0 < r`), then `μ(B_r) w(x) ≤ ∫_{B_r(x)} w`. -/
theorem IsViscSubharmonicOn.le_setIntegral_ball (hd : 1 ≤ d) {Ω : Set (E d)} {w : E d → ℝ}
    (hw : IsViscSubharmonicOn w Ω) (hwc : ContinuousOn w Ω) {x : E d} {r : ℝ} (hr : 0 < r)
    (hB : closedBall x r ⊆ Ω) :
    μ.real (ball x r) * w x ≤ ∫ y in ball x r, w y ∂μ := by
  have := nontrivial_E_of_one_le hd
  exact le_setIntegral_ball_of_le_integral_toSphere hr (hwc.mono hB) fun s hs hsr ↦
    IsViscSubharmonicOn.le_integral_toSphere hd hw hwc hs
      ((closedBall_subset_closedBall hsr.le).trans hB)

/-- **Super-mean-value property on balls** (dual of `IsViscSubharmonicOn.le_setIntegral_ball`). -/
theorem IsViscSuperharmonicOn.setIntegral_ball_le (hd : 1 ≤ d) {Ω : Set (E d)} {w : E d → ℝ}
    (hw : IsViscSuperharmonicOn w Ω) (hwc : ContinuousOn w Ω) {x : E d} {r : ℝ} (hr : 0 < r)
    (hB : closedBall x r ⊆ Ω) :
    ∫ y in ball x r, w y ∂μ ≤ μ.real (ball x r) * w x := by
  have hwc' : ContinuousOn (-w) Ω := hwc.neg
  have := IsViscSubharmonicOn.le_setIntegral_ball (μ := μ) hd hw.neg hwc' hr hB
  simp only [Pi.neg_apply, integral_neg, mul_neg] at this
  linarith

end EllipticBernoulli
