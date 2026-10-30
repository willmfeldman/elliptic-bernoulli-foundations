/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.Setting
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
import ViscositySolns.Applications.Laplace.Weyl.PolarCoord

/-!
# Integration in polar coordinates about a point

Mathlib's `Measure.measurePreserving_homeomorphUnitSphereProd` identifies an additive Haar
measure `μ` on `E \ {0}` with the product of the sphere measure `σ = μ.toSphere` and the radial
measure `t ^ (n - 1) dt` on `(0, ∞)`. This file records the resulting polar formula about an
arbitrary centre `x₀`, for nonnegative measurable functions
(Tonelli) and for integrable functions (Fubini), and the transfer of almost-everywhere statements
from `μ` to spheres.

* `lintegral_eq_lintegral_Ioi_lintegral_toSphere`:
  `∫⁻ h dμ = ∫⁻_{t > 0} t^{n-1} ∫⁻_𝕊 h(tω) dσ(ω) dt`.
* `lintegral_add_eq_lintegral_Ioi_lintegral_toSphere`: the same about `x₀`.
* `integral_add_eq_integral_Ioi_integral_toSphere`: the Bochner version about `x₀`, for
  integrable `h`.
* `ae_ae_toSphere_of_ae`: if a property holds `μ`-a.e., then for a.e. `t > 0` it holds at
  `x₀ + tω` for `σ`-a.e. `ω`.
* `ae_toSphere_ae_of_ae`: the same with the order of the quantifiers exchanged.
* `toSphere_preimage_eq_zero_of_cone`: a `μ`-null cone meets the sphere in a `σ`-null set.
* `nontrivial_E`: `E d` is nontrivial for `d ≥ 1`, so the lemmas apply to `E d` with
  `finrank ℝ (E d) = d` (`finrank_euclideanSpace_fin`).

The Bochner version is `ViscositySolns.Analysis.integral_eq_integral_Ioi_integral_toSphere`
translated to the centre `x₀`; this is why the file lives in `Harmonic/` (the only place that may
import `viscosity_solns`).
-/

open MeasureTheory Metric Set Filter Module
open scoped ENNReal NNReal

public section

namespace EllipticBernoulli

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The sphere integrals `t ↦ ∫⁻_𝕊 g(x₀ + tω) dσ(ω)` of a measurable `g` are measurable in `t`. -/
theorem measurable_lintegral_toSphere {g : E → ℝ≥0∞} (hg : Measurable g) (x₀ : E) :
    Measurable fun t : ℝ ↦ ∫⁻ ω : sphere (0 : E) 1, g (x₀ + t • (ω : E)) ∂μ.toSphere :=
  (hg.comp (measurable_const.add
    (measurable_fst.smul (measurable_subtype_coe.comp measurable_snd)))).lintegral_prod_right'

/-- **Polar formula (Tonelli).** For a measurable `h : E → [0, ∞]`,
`∫⁻ h dμ = ∫⁻_{t > 0} t^{n-1} ∫⁻_𝕊 h(tω) dσ(ω) dt`, where `n = dim E` and `σ = μ.toSphere`. -/
theorem lintegral_eq_lintegral_Ioi_lintegral_toSphere [Nontrivial E] {h : E → ℝ≥0∞}
    (hh : Measurable h) :
    ∫⁻ x, h x ∂μ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (finrank ℝ E - 1)) *
      ∫⁻ ω : sphere (0 : E) 1, h (t • (ω : E)) ∂μ.toSphere := by
  set k := finrank ℝ E - 1
  have hmp := μ.measurePreserving_homeomorphUnitSphereProd
  have hemb := (homeomorphUnitSphereProd E).measurableEmbedding
  set g : sphere (0 : E) 1 × Ioi (0 : ℝ) → ℝ≥0∞ := fun p ↦ h ((p.2 : ℝ) • (p.1 : E)) with hg_def
  have hg : g ∘ homeomorphUnitSphereProd E = h ∘ Subtype.val := by
    funext x
    have hx : ‖(x : E)‖ ≠ 0 := norm_ne_zero_iff.mpr x.2
    simp [hg_def, smul_smul, hx]
  have hgm : Measurable g :=
    hh.comp ((measurable_subtype_coe.comp measurable_snd).smul
      (measurable_subtype_coe.comp measurable_fst))
  have hS : MeasurableSet ({0}ᶜ : Set E) := (measurableSet_singleton _).compl
  have hF : Measurable fun t : Ioi (0 : ℝ) ↦
      ∫⁻ ω : sphere (0 : E) 1, h ((t : ℝ) • (ω : E)) ∂μ.toSphere :=
    hgm.lintegral_prod_left'
  calc ∫⁻ x, h x ∂μ = ∫⁻ x in ({0}ᶜ : Set E), h x ∂μ := by rw [restrict_compl_singleton]
    _ = ∫⁻ x : ({0}ᶜ : Set E), h x ∂(μ.comap Subtype.val) :=
        (lintegral_subtype_comap hS h).symm
    _ = ∫⁻ p, g p ∂(μ.toSphere.prod (Measure.volumeIoiPow k)) := by
        rw [← hmp.lintegral_comp_emb hemb g]
        exact lintegral_congr fun x ↦ (congrFun hg x).symm
    _ = ∫⁻ t, ∫⁻ ω, g (ω, t) ∂μ.toSphere ∂(Measure.volumeIoiPow k) :=
        lintegral_prod_symm' g hgm
    _ = ∫⁻ t : Ioi (0 : ℝ), ENNReal.ofReal ((t : ℝ) ^ k) *
          ∫⁻ ω : sphere (0 : E) 1, h ((t : ℝ) • (ω : E)) ∂μ.toSphere
          ∂(Measure.comap Subtype.val volume) := by
        rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul _
          (by fun_prop) hF]
        rfl
    _ = _ := lintegral_subtype_comap measurableSet_Ioi
          (fun t ↦ ENNReal.ofReal (t ^ k) * ∫⁻ ω : sphere (0 : E) 1, h (t • (ω : E)) ∂μ.toSphere)

/-- **Polar formula about `x₀` (Tonelli).** For a measurable `h : E → [0, ∞]` and `x₀ ∈ E`,
`∫⁻ h dμ = ∫⁻_{t > 0} t^{n-1} ∫⁻_𝕊 h(x₀ + tω) dσ(ω) dt`. -/
theorem lintegral_add_eq_lintegral_Ioi_lintegral_toSphere [Nontrivial E] {h : E → ℝ≥0∞}
    (hh : Measurable h) (x₀ : E) :
    ∫⁻ x, h x ∂μ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (finrank ℝ E - 1)) *
      ∫⁻ ω : sphere (0 : E) 1, h (x₀ + t • (ω : E)) ∂μ.toSphere := by
  rw [← lintegral_add_left_eq_self h x₀]
  exact lintegral_eq_lintegral_Ioi_lintegral_toSphere (hh.comp (measurable_const_add x₀))

/-- **Polar formula about `x₀` (Fubini).** For an integrable `h : E → F` and `x₀ ∈ E`,
`∫ h dμ = ∫_{t > 0} t^{n-1} ∫_𝕊 h(x₀ + tω) dσ(ω) dt`. -/
theorem integral_add_eq_integral_Ioi_integral_toSphere [Nontrivial E] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {h : E → F} (hh : Integrable h μ) (x₀ : E) :
    ∫ x, h x ∂μ = ∫ t in Ioi (0 : ℝ), t ^ (finrank ℝ E - 1) •
      ∫ ω : sphere (0 : E) 1, h (x₀ + t • (ω : E)) ∂μ.toSphere := by
  rw [← integral_add_left_eq_self h x₀]
  exact ViscositySolns.Analysis.integral_eq_integral_Ioi_integral_toSphere _
    (hh.comp_add_left x₀)

/-- **A.e. statements transfer to spheres.** If a property holds at `μ`-a.e. point, then for
a.e. `t > 0` it holds at `x₀ + tω` for `σ`-a.e. `ω`. -/
theorem ae_ae_toSphere_of_ae [Nontrivial E] {P : E → Prop} (hP : ∀ᵐ x ∂μ, P x) (x₀ : E) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), ∀ᵐ ω : sphere (0 : E) 1 ∂μ.toSphere,
      P (x₀ + t • (ω : E)) := by
  obtain ⟨N, hPN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  have hint := lintegral_add_eq_lintegral_Ioi_lintegral_toSphere (μ := μ)
    (measurable_one.indicator hNm) x₀
  rw [lintegral_indicator_one hNm, hN0, eq_comm,
    lintegral_eq_zero_iff (f := fun t : ℝ ↦ ENNReal.ofReal (t ^ (finrank ℝ E - 1)) *
      ∫⁻ ω : sphere (0 : E) 1, N.indicator 1 (x₀ + t • (ω : E)) ∂μ.toSphere)
      ((by fun_prop : Measurable fun t : ℝ ↦ ENNReal.ofReal (t ^ (finrank ℝ E - 1))).mul
        (measurable_lintegral_toSphere (measurable_one.indicator hNm) x₀))] at hint
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioi] at hint
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hint] with t ht htpos
  have h := ht htpos
  simp only [Pi.zero_apply, mul_eq_zero, ENNReal.ofReal_eq_zero, not_le.mpr
    (pow_pos (show (0 : ℝ) < t from htpos) _), false_or] at h
  rw [lintegral_eq_zero_iff (f := fun ω : sphere (0 : E) 1 ↦ N.indicator 1 (x₀ + t • (ω : E)))
    ((measurable_one.indicator hNm).comp
      (measurable_const.add (measurable_const.smul measurable_subtype_coe)))] at h
  filter_upwards [h] with ω hω
  by_contra hnot
  have hmem : x₀ + t • (ω : E) ∈ N := hPN hnot
  simp [indicator_of_mem hmem] at hω

/-- **A.e. statements transfer to rays.** If a property holds at `μ`-a.e. point, then for
`σ`-a.e. `ω` it holds at `x₀ + tω` for a.e. `t > 0`. -/
theorem ae_toSphere_ae_of_ae [Nontrivial E] {P : E → Prop} (hP : ∀ᵐ x ∂μ, P x) (x₀ : E) :
    ∀ᵐ ω : sphere (0 : E) 1 ∂μ.toSphere, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      P (x₀ + t • (ω : E)) := by
  obtain ⟨N, hPN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.mp hP)
  have hN : ∀ᵐ x ∂μ, x ∉ N := measure_eq_zero_iff_ae_notMem.mp hN0
  have h := ae_ae_toSphere_of_ae hN x₀
  have hmeas : MeasurableSet {p : ℝ × sphere (0 : E) 1 | x₀ + p.1 • (p.2 : E) ∉ N} :=
    (hNm.preimage (measurable_const.add
      (measurable_fst.smul (measurable_subtype_coe.comp measurable_snd)))).compl
  rw [Measure.ae_ae_comm hmeas] at h
  filter_upwards [h] with ω hω
  filter_upwards [hω] with t ht
  by_contra hnot
  exact ht (hPN hnot)

/-- **Null cones are null on the sphere.** If `A ⊆ E` is `μ`-null and invariant under positive
dilations (`t • x ∈ A` for `x ∈ A`, `t > 0`), then `{ω ∈ 𝕊 | ω ∈ A}` is `σ`-null. -/
theorem toSphere_preimage_eq_zero_of_cone [Nontrivial E] {A : Set E} (hA : μ A = 0)
    (hcone : ∀ t : ℝ, 0 < t → ∀ x ∈ A, t • x ∈ A) :
    μ.toSphere {ω : sphere (0 : E) 1 | (ω : E) ∈ A} = 0 := by
  have hae : ∀ᵐ x ∂μ, x ∉ A := measure_eq_zero_iff_ae_notMem.mp hA
  have h := ae_ae_toSphere_of_ae hae 0
  have : (ae (volume.restrict (Ioi (0 : ℝ)))).NeBot :=
    ae_neBot.mpr (by simp [Measure.restrict_eq_zero])
  obtain ⟨t, ht, htpos⟩ := (h.and (ae_restrict_mem measurableSet_Ioi)).exists
  refine measure_mono_null (fun ω hω ↦ ?_) (ae_iff.mp ht)
  simpa using hcone t htpos _ hω

end General

/-- `E d` is nontrivial for `d ≥ 1`. -/
theorem nontrivial_E {d : ℕ} (hd : 1 ≤ d) : Nontrivial (E d) :=
  Module.nontrivial_of_finrank_pos (by rw [finrank_euclideanSpace_fin]; omega)

end EllipticBernoulli
