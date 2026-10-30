/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.TwoPhase
public import EllipticBernoulli.Harmonic.Polar
public import EllipticBernoulli.Common.FTCLip
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import EllipticBernoulli.Sobolev.Lipschitz

/-!
# Radial calculus about a point

Let `w : E d → ℝ` be `L`-Lipschitz and `x₀ ∈ E d`. Write `∂ᵣw(x) = ∇w(x) · (x - x₀)/|x - x₀|`
(`radialDeriv`) and, for `t ≥ 0`, with `σ = (volume : Measure (E d)).toSphere`,

* `radialK w x₀ t = ∫_𝕊 (w ∂ᵣw)(x₀ + tω) dσ(ω)`,
* `radialM w x₀ t = ∫_𝕊 w(x₀ + tω)² dσ(ω)`,
* `radialQ w x₀ t = ∫_𝕊 |∇w|²(x₀ + tω) dσ(ω)`,
* `radialA w x₀ t = ∫_𝕊 (∂ᵣw)²(x₀ + tω) dσ(ω)`

(abbreviated `k, m, q, a`). This file proves the
bounds `|k(t)| ≤ L² t σ(𝕊)`, `m(t) ≤ L² t² σ(𝕊)`, `q, a ≤ L² σ(𝕊)` (when `w x₀ = 0`), their
measurability in `t`, and the following facts about `m`:

* `radialM_sub_eq_integral`: `m(t) - m(t') = ∫_{t'}^t 2k` for `0 ≤ t' ≤ t`;
* `radialM_zero`, `tendsto_radialM_nhdsGT_zero`: `m(0) = 0` and `m(0⁺) = 0` when `w x₀ = 0`;
* `radialM_eq_integral`, `ae_hasDerivAt_radialM`: `m(t) = ∫_0^t 2k` and `m' = 2k` a.e. on `(0, ∞)`
  when `w x₀ = 0`.

Weighted ball integrals: `setIntegral_ball_mul_rpow_eq` (`∫_{B_r(x₀)} h |x - x₀|^β` in polar form,
`β > -d`), `exists_lipschitzOnWith_setIntegral_ball_mul_rpow` and
`ae_hasDerivAt_setIntegral_ball_mul_rpow` (`β ≥ 1 - d`), and for the ACF integral
`acfIntegral_eq_integral` (`I(r) = ∫_0^r τ q(τ) dτ`), `exists_lipschitzOnWith_acfIntegral` and
`ae_hasDerivAt_acfIntegral` (`I' = r q(r)` a.e.).

No sign condition and no two-phase hypothesis is assumed; the dimension hypothesis is `1 ≤ d`.
-/

open MeasureTheory Metric Set Filter Topology Module
open scoped Gradient NNReal

namespace EllipticBernoulli

variable {d : ℕ}

@[expose] public noncomputable section

/-- The radial derivative about `x₀`: `∂ᵣw(x) = ∇w(x) · (x - x₀)/|x - x₀|` (and `0` at `x₀`). -/
def radialDeriv (w : E d → ℝ) (x₀ x : E d) : ℝ :=
  inner ℝ (∇ w x) (‖x - x₀‖⁻¹ • (x - x₀))

/-- `k(t) = ∫_𝕊 (w ∂ᵣw)(x₀ + tω) dσ(ω)`. -/
def radialK (w : E d → ℝ) (x₀ : E d) (t : ℝ) : ℝ :=
  ∫ ω : sphere (0 : E d) 1, w (x₀ + t • (ω : E d)) * radialDeriv w x₀ (x₀ + t • (ω : E d))
    ∂(volume : Measure (E d)).toSphere

/-- `m(t) = ∫_𝕊 w(x₀ + tω)² dσ(ω)`. -/
def radialM (w : E d → ℝ) (x₀ : E d) (t : ℝ) : ℝ :=
  ∫ ω : sphere (0 : E d) 1, w (x₀ + t • (ω : E d)) ^ 2 ∂(volume : Measure (E d)).toSphere

/-- `q(t) = ∫_𝕊 |∇w|²(x₀ + tω) dσ(ω)`. -/
def radialQ (w : E d → ℝ) (x₀ : E d) (t : ℝ) : ℝ :=
  ∫ ω : sphere (0 : E d) 1, ‖∇ w (x₀ + t • (ω : E d))‖ ^ 2 ∂(volume : Measure (E d)).toSphere

/-- `a(t) = ∫_𝕊 (∂ᵣw)²(x₀ + tω) dσ(ω)`. -/
def radialA (w : E d → ℝ) (x₀ : E d) (t : ℝ) : ℝ :=
  ∫ ω : sphere (0 : E d) 1, radialDeriv w x₀ (x₀ + t • (ω : E d)) ^ 2
    ∂(volume : Measure (E d)).toSphere

end

public section

/-! ### Pointwise facts -/

theorem radialDeriv_add_smul (w : E d → ℝ) (x₀ : E d) {t : ℝ} (ht : 0 < t)
    (ω : sphere (0 : E d) 1) :
    radialDeriv w x₀ (x₀ + t • (ω : E d)) = inner ℝ (∇ w (x₀ + t • (ω : E d))) (ω : E d) := by
  have hω : ‖(ω : E d)‖ = 1 := norm_eq_of_mem_sphere ω
  simp [radialDeriv, norm_smul, hω, abs_of_pos ht, smul_smul, inv_mul_cancel₀ ht.ne']

theorem measurable_radialDeriv (w : E d → ℝ) (x₀ : E d) : Measurable (radialDeriv w x₀) :=
  Measurable.inner (measurable_gradient w)
    (((measurable_id.sub_const x₀).norm).inv.smul (measurable_id.sub_const x₀))

/-- The gradient of an `L`-Lipschitz function has norm at most `L`. -/
theorem norm_gradient_le_of_lipschitzWith {w : E d → ℝ} {L : ℝ≥0} (hw : LipschitzWith L w)
    (x : E d) : ‖∇ w x‖ ≤ L := by
  rw [norm_gradient_eq_norm_fderiv]
  exact norm_fderiv_le_of_lipschitz ℝ hw

theorem abs_radialDeriv_le {w : E d → ℝ} {L : ℝ≥0} (hw : LipschitzWith L w) (x₀ x : E d) :
    |radialDeriv w x₀ x| ≤ L := by
  have hu : ‖‖x - x₀‖⁻¹ • (x - x₀)‖ ≤ 1 := by
    rw [norm_smul, norm_inv, norm_norm]
    rcases eq_or_ne ‖x - x₀‖ 0 with h | h
    · simp [h]
    · rw [inv_mul_cancel₀ h]
  calc |radialDeriv w x₀ x| ≤ ‖∇ w x‖ * ‖‖x - x₀‖⁻¹ • (x - x₀)‖ := abs_real_inner_le_norm _ _
    _ ≤ L * 1 := by
        gcongr
        · exact norm_gradient_le_of_lipschitzWith hw x
    _ = L := mul_one _

theorem abs_apply_add_smul_le {w : E d → ℝ} {L : ℝ≥0} (hw : LipschitzWith L w) (x₀ : E d)
    {t : ℝ} (ht : 0 ≤ t) (ω : sphere (0 : E d) 1) :
    |w (x₀ + t • (ω : E d))| ≤ |w x₀| + L * t := by
  have h := hw.dist_le_mul (x₀ + t • (ω : E d)) x₀
  have hd : dist (x₀ + t • (ω : E d)) x₀ = t := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_eq_of_mem_sphere ω, mul_one,
      Real.norm_of_nonneg ht]
  rw [hd, Real.dist_eq] at h
  have := abs_sub_abs_le_abs_sub (w (x₀ + t • (ω : E d))) (w x₀)
  linarith

/-! ### Measurability and bounds -/

theorem measurable_add_smul_sphere (x₀ : E d) :
    Measurable fun p : ℝ × sphere (0 : E d) 1 ↦ x₀ + p.1 • (p.2 : E d) :=
  measurable_const.add (measurable_fst.smul (measurable_subtype_coe.comp measurable_snd))

/-- Sphere integrals `t ↦ ∫_𝕊 F(x₀ + tω) dσ(ω)` of a measurable `F` are strongly measurable in
`t` (Fubini). -/
theorem stronglyMeasurable_integral_toSphere {F : E d → ℝ} (hF : Measurable F) (x₀ : E d) :
    StronglyMeasurable fun t : ℝ ↦
      ∫ ω : sphere (0 : E d) 1, F (x₀ + t • (ω : E d)) ∂(volume : Measure (E d)).toSphere :=
  (hF.comp (measurable_add_smul_sphere x₀)).stronglyMeasurable.integral_prod_right'

private theorem abs_integral_toSphere_le {F : sphere (0 : E d) 1 → ℝ} {B : ℝ}
    (hF : ∀ ω, |F ω| ≤ B) :
    |∫ ω, F ω ∂(volume : Measure (E d)).toSphere| ≤
      B * (volume : Measure (E d)).toSphere.real univ := by
  have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (E d)).toSphere)
    (f := F) (C := B) (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hF ω)
  rwa [Real.norm_eq_abs] at this

/-- An integrand on the sphere that is measurable on `E d` and bounded is integrable. -/
theorem integrable_toSphere_of_bound {F : E d → ℝ} (hF : Measurable F) (x₀ : E d) (t : ℝ)
    {B : ℝ} (hB : ∀ ω : sphere (0 : E d) 1, |F (x₀ + t • (ω : E d))| ≤ B) :
    Integrable (fun ω : sphere (0 : E d) 1 ↦ F (x₀ + t • (ω : E d)))
      (volume : Measure (E d)).toSphere :=
  Integrable.of_bound
    (hF.comp (show Measurable fun ω : sphere (0 : E d) 1 ↦ x₀ + t • (ω : E d) by
      fun_prop)).aestronglyMeasurable
    B (ae_of_all _ fun ω ↦ by rw [Real.norm_eq_abs]; exact hB ω)

theorem stronglyMeasurable_radialK {w : E d → ℝ} (hw : Measurable w) (x₀ : E d) :
    StronglyMeasurable (radialK w x₀) :=
  stronglyMeasurable_integral_toSphere (hw.mul (measurable_radialDeriv w x₀)) x₀

theorem stronglyMeasurable_radialM {w : E d → ℝ} (hw : Measurable w) (x₀ : E d) :
    StronglyMeasurable (radialM w x₀) :=
  stronglyMeasurable_integral_toSphere (hw.pow_const 2) x₀

theorem stronglyMeasurable_radialQ (w : E d → ℝ) (x₀ : E d) :
    StronglyMeasurable (radialQ w x₀) :=
  stronglyMeasurable_integral_toSphere ((measurable_gradient w).norm.pow_const 2) x₀

theorem stronglyMeasurable_radialA (w : E d → ℝ) (x₀ : E d) :
    StronglyMeasurable (radialA w x₀) :=
  stronglyMeasurable_integral_toSphere ((measurable_radialDeriv w x₀).pow_const 2) x₀

variable {w : E d → ℝ} {L : ℝ≥0} {x₀ : E d}

theorem radialM_nonneg (w : E d → ℝ) (x₀ : E d) (t : ℝ) : 0 ≤ radialM w x₀ t :=
  integral_nonneg fun _ ↦ sq_nonneg _

theorem radialQ_nonneg (w : E d → ℝ) (x₀ : E d) (t : ℝ) : 0 ≤ radialQ w x₀ t :=
  integral_nonneg fun _ ↦ sq_nonneg _

theorem radialA_nonneg (w : E d → ℝ) (x₀ : E d) (t : ℝ) : 0 ≤ radialA w x₀ t :=
  integral_nonneg fun _ ↦ sq_nonneg _

/-- `q(t) ≤ L² σ(𝕊)`. -/
theorem radialQ_le (hw : LipschitzWith L w) (x₀ : E d) (t : ℝ) :
    radialQ w x₀ t ≤ (L : ℝ) ^ 2 * (volume : Measure (E d)).toSphere.real univ := by
  refine le_trans (le_abs_self _) (abs_integral_toSphere_le fun ω ↦ ?_)
  rw [abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_le_of_lipschitzWith hw _) 2

/-- `a(t) ≤ L² σ(𝕊)`. -/
theorem radialA_le (hw : LipschitzWith L w) (x₀ : E d) (t : ℝ) :
    radialA w x₀ t ≤ (L : ℝ) ^ 2 * (volume : Measure (E d)).toSphere.real univ := by
  refine le_trans (le_abs_self _) (abs_integral_toSphere_le fun ω ↦ ?_)
  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_radialDeriv_le hw _ _) 2

/-- `m(t) ≤ L² t² σ(𝕊)` when `w x₀ = 0`. -/
theorem radialM_le (hw : LipschitzWith L w) (hx₀ : w x₀ = 0) {t : ℝ} (ht : 0 ≤ t) :
    radialM w x₀ t ≤ (L : ℝ) ^ 2 * t ^ 2 * (volume : Measure (E d)).toSphere.real univ := by
  refine le_trans (le_abs_self _) (abs_integral_toSphere_le fun ω ↦ ?_)
  have h := abs_apply_add_smul_le hw x₀ ht ω
  rw [hx₀, abs_zero, zero_add] at h
  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs, ← mul_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- `|k(t)| ≤ L² t σ(𝕊)` when `w x₀ = 0`. -/
theorem abs_radialK_le (hw : LipschitzWith L w) (hx₀ : w x₀ = 0) {t : ℝ} (ht : 0 ≤ t) :
    |radialK w x₀ t| ≤ (L : ℝ) ^ 2 * t * (volume : Measure (E d)).toSphere.real univ := by
  refine abs_integral_toSphere_le fun ω ↦ ?_
  have h := abs_apply_add_smul_le hw x₀ ht ω
  rw [hx₀, abs_zero, zero_add] at h
  rw [abs_mul]
  calc |w (x₀ + t • (ω : E d))| * |radialDeriv w x₀ (x₀ + t • (ω : E d))| ≤ (L * t) * L :=
        mul_le_mul h (abs_radialDeriv_le hw _ _) (abs_nonneg _) (by positivity)
    _ = (L : ℝ) ^ 2 * t := by ring

/-! ### Part (a): `m' = 2k` -/

/-- `m(0) = 0` when `w x₀ = 0`. -/
theorem radialM_zero (hx₀ : w x₀ = 0) : radialM w x₀ 0 = 0 := by
  simp [radialM, hx₀]

/-- `m(t) → 0` as `t → 0⁺` when `w x₀ = 0`. -/
theorem tendsto_radialM_nhdsGT_zero (hw : LipschitzWith L w) (hx₀ : w x₀ = 0) :
    Tendsto (radialM w x₀) (𝓝[>] 0) (𝓝 0) := by
  set C := (L : ℝ) ^ 2 * (volume : Measure (E d)).toSphere.real univ
  have hlim : Tendsto (fun t : ℝ ↦ C * t ^ 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ ↦ C * t ^ 2) (𝓝 0) (𝓝 (C * 0 ^ 2)) :=
      (continuous_const.mul (continuous_pow 2)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun t ↦ radialM_nonneg w x₀ t) ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  calc radialM w x₀ t ≤ (L : ℝ) ^ 2 * t ^ 2 * (volume : Measure (E d)).toSphere.real univ :=
        radialM_le hw hx₀ ht.le
    _ = C * t ^ 2 := by ring

/-- Along a ray, `τ ↦ w(x₀ + τω)²` has derivative `2 (w ∂ᵣw)(x₀ + τω)` at every `τ > 0` where `w`
is differentiable at `x₀ + τω`. -/
private theorem hasDerivAt_sq_ray (x₀ : E d) (ω : sphere (0 : E d) 1) {τ : ℝ} (hτ : 0 < τ)
    (hdiff : DifferentiableAt ℝ w (x₀ + τ • (ω : E d))) :
    HasDerivAt (fun s : ℝ ↦ w (x₀ + s • (ω : E d)) * w (x₀ + s • (ω : E d)))
      (2 * (w (x₀ + τ • (ω : E d)) * radialDeriv w x₀ (x₀ + τ • (ω : E d)))) τ := by
  have hray : HasDerivAt (fun s : ℝ ↦ x₀ + s • (ω : E d)) (ω : E d) τ := by
    simpa using ((hasDerivAt_id τ).smul_const (ω : E d)).const_add x₀
  have h1 := hdiff.hasFDerivAt.comp_hasDerivAt τ hray
  refine (h1.mul h1).congr_deriv ?_
  rw [radialDeriv_add_smul w x₀ hτ, inner_gradient_left_eq_fderiv]
  simp only [Function.comp_apply]
  ring

/-- **Radial calculus (a).** For an `L`-Lipschitz `w`, `x₀ ∈ E d` and `0 ≤ t' ≤ t`,
`m(t) - m(t') = ∫_{t'}^t 2 k(τ) dτ`. -/
theorem radialM_sub_eq_integral (hd : 1 ≤ d) (hw : LipschitzWith L w) (x₀ : E d) {t' t : ℝ}
    (ht' : 0 ≤ t') (htt : t' ≤ t) :
    radialM w x₀ t - radialM w x₀ t' = ∫ τ in t'..t, 2 * radialK w x₀ τ := by
  have := nontrivial_E hd
  set σ := (volume : Measure (E d)).toSphere with hσ
  set H : E d → ℝ := fun x ↦ 2 * (w x * radialDeriv w x₀ x) with hH
  have hwm : Measurable w := hw.continuous.measurable
  have hHm : Measurable H := measurable_const.mul (hwm.mul (measurable_radialDeriv w x₀))
  set B : ℝ := |w x₀| + L * t
  have hwB : ∀ τ ∈ Icc 0 t, ∀ ω : sphere (0 : E d) 1, |w (x₀ + τ • (ω : E d))| ≤ B := by
    intro τ hτ ω
    have := abs_apply_add_smul_le hw x₀ hτ.1 ω
    have : (L : ℝ) * τ ≤ L * t := mul_le_mul_of_nonneg_left hτ.2 L.2
    simp only [B]; linarith
  have hHB : ∀ τ ∈ Icc 0 t, ∀ ω : sphere (0 : E d) 1, |H (x₀ + τ • (ω : E d))| ≤ 2 * (B * L) := by
    intro τ hτ ω
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hwB τ hτ ω)
    simp only [hH, abs_mul, abs_two]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (hwB τ hτ ω) (abs_radialDeriv_le hw _ _) (abs_nonneg _) hB0) zero_le_two
  -- the ray-by-ray FTC, for `σ`-a.e. `ω`
  have hray := ae_toSphere_ae_of_ae (μ := (volume : Measure (E d))) hw.ae_differentiableAt x₀
  have hpt : ∀ᵐ ω : sphere (0 : E d) 1 ∂σ,
      w (x₀ + t • (ω : E d)) ^ 2 - w (x₀ + t' • (ω : E d)) ^ 2 =
        ∫ τ in t'..t, H (x₀ + τ • (ω : E d)) := by
    filter_upwards [hray] with ω hω
    rw [ae_restrict_iff' measurableSet_Ioi] at hω
    have hlip : LipschitzWith L fun s : ℝ ↦ w (x₀ + s • (ω : E d)) := by
      refine LipschitzWith.of_dist_le_mul fun s s' ↦ ?_
      have h := hw.dist_le_mul (x₀ + s • (ω : E d)) (x₀ + s' • (ω : E d))
      have hd : dist (x₀ + s • (ω : E d)) (x₀ + s' • (ω : E d)) = dist s s' := by
        rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, norm_eq_of_mem_sphere ω,
          mul_one, Real.dist_eq, Real.norm_eq_abs]
      rwa [hd] at h
    have hac := (hlip.lipschitzOnWith (s := uIcc t' t)).absolutelyContinuousOnInterval
    have h := (hac.mul hac).integral_eq_sub_of_ae_hasDerivAt (f' := fun τ ↦ H (x₀ + τ • (ω : E d)))
      (by
        filter_upwards [hω] with τ hτ hmem
        rw [uIoo_of_le htt] at hmem
        have hτpos : 0 < τ := lt_of_le_of_lt ht' hmem.1
        exact hasDerivAt_sq_ray x₀ ω hτpos (hτ hτpos))
    rw [h]
    simp only [Pi.mul_apply, sq]
  -- integrate over the sphere and exchange the integrals
  have hint : ∀ τ ∈ Icc 0 t,
      Integrable (fun ω : sphere (0 : E d) 1 ↦ w (x₀ + τ • (ω : E d)) ^ 2) σ :=
    fun τ hτ ↦ integrable_toSphere_of_bound (hwm.pow_const 2) x₀ τ (B := B ^ 2) fun ω ↦ by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hwB τ hτ ω) 2
  have : IsFiniteMeasure (volume.restrict (Ioc t' t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hprod : Integrable (Function.uncurry fun (ω : sphere (0 : E d) 1) (τ : ℝ) ↦
      H (x₀ + τ • (ω : E d))) (σ.prod (volume.restrict (Ioc t' t))) := by
    refine Integrable.of_bound ?_ (2 * (B * L)) ?_
    · exact (hHm.comp (measurable_const.add
        (measurable_snd.smul (measurable_subtype_coe.comp measurable_fst)))).aestronglyMeasurable
    · have hmem : ∀ᵐ p ∂(σ.prod (volume.restrict (Ioc t' t))), p.2 ∈ Ioc t' t :=
        Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)
      filter_upwards [hmem] with p hp
      rw [Real.norm_eq_abs]
      exact hHB p.2 ⟨ht'.trans hp.1.le, hp.2⟩ p.1
  calc radialM w x₀ t - radialM w x₀ t'
      = ∫ ω, (w (x₀ + t • (ω : E d)) ^ 2 - w (x₀ + t' • (ω : E d)) ^ 2) ∂σ :=
        (integral_sub (hint t ⟨ht'.trans htt, le_rfl⟩) (hint t' ⟨ht', htt⟩)).symm
    _ = ∫ ω, (∫ τ in t'..t, H (x₀ + τ • (ω : E d))) ∂σ := integral_congr_ae hpt
    _ = ∫ τ in t'..t, ∫ ω, H (x₀ + τ • (ω : E d)) ∂σ := by
        simp_rw [intervalIntegral.integral_of_le htt]
        exact integral_integral_swap hprod
    _ = ∫ τ in t'..t, 2 * radialK w x₀ τ := by
        refine intervalIntegral.integral_congr fun τ _ ↦ ?_
        simp only [hH, radialK]
        exact integral_const_mul 2 _

/-- **Radial calculus (a), from the centre.** If `w x₀ = 0`, then `m(t) = ∫_0^t 2 k(τ) dτ` for
`t ≥ 0`. -/
theorem radialM_eq_integral (hd : 1 ≤ d) (hw : LipschitzWith L w) (hx₀ : w x₀ = 0) {t : ℝ}
    (ht : 0 ≤ t) : radialM w x₀ t = ∫ τ in 0..t, 2 * radialK w x₀ τ := by
  rw [← radialM_sub_eq_integral hd hw x₀ le_rfl ht, radialM_zero hx₀, sub_zero]

/-- `m' = 2k` almost everywhere: if `w x₀ = 0`, then for a.e. `t > 0`, `m` has derivative
`2 k(t)` at `t`. -/
theorem ae_hasDerivAt_radialM (hd : 1 ≤ d) (hw : LipschitzWith L w) (hx₀ : w x₀ = 0) :
    ∀ᵐ t, 0 < t → HasDerivAt (radialM w x₀) (2 * radialK w x₀ t) t := by
  have hint : ∀ n : ℕ,
      IntervalIntegrable (fun τ ↦ 2 * radialK w x₀ τ) volume 0 ((n : ℝ) + 1) := by
    intro n
    have hR : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    have hon : IntegrableOn (fun τ ↦ 2 * radialK w x₀ τ) (Icc 0 ((n : ℝ) + 1)) :=
      IntegrableOn.of_bound measure_Icc_lt_top
        ((stronglyMeasurable_const.mul
          (stronglyMeasurable_radialK hw.continuous.measurable x₀)).aestronglyMeasurable)
        (2 * ((L : ℝ) ^ 2 * ((n : ℝ) + 1) * (volume : Measure (E d)).toSphere.real univ))
        (ae_restrict_of_forall_mem measurableSet_Icc fun τ hτ ↦ by
          rw [Real.norm_eq_abs, abs_mul, abs_two]
          refine mul_le_mul_of_nonneg_left ((abs_radialK_le hw hx₀ hτ.1).trans ?_) zero_le_two
          gcongr
          exact hτ.2)
    rw [← uIcc_of_le hR] at hon
    exact hon.intervalIntegrable
  have hn : ∀ n : ℕ, ∀ᵐ t, t ∈ uIcc 0 ((n : ℝ) + 1) → ∀ c ∈ uIcc 0 ((n : ℝ) + 1),
      HasDerivAt (fun x ↦ ∫ τ in c..x, 2 * radialK w x₀ τ) (2 * radialK w x₀ t) t :=
    fun n ↦ (hint n).ae_hasDerivAt_integral
  filter_upwards [ae_all_iff.2 hn] with t ht htpos
  obtain ⟨n, hnt⟩ := exists_nat_ge t
  have hmem : t ∈ uIcc 0 ((n : ℝ) + 1) := by
    rw [uIcc_of_le (by positivity)]
    exact ⟨htpos.le, by linarith⟩
  refine (ht n hmem 0 left_mem_uIcc).congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds htpos] with s hs
  exact radialM_eq_integral hd hw hx₀ hs.le

/-! ### Part (b): weighted ball integrals -/

/-- `|x - x₀|^β` is integrable on `B_r(x₀)` for `β > -d`. -/
theorem integrableOn_ball_norm_sub_rpow (hd : 1 ≤ d) (x₀ : E d) {β : ℝ} (hβ : -(d : ℝ) < β)
    (r : ℝ) : IntegrableOn (fun x : E d ↦ ‖x - x₀‖ ^ β) (ball x₀ r) := by
  have := nontrivial_E hd
  have h0 : IntegrableOn (fun x : E d ↦ ‖x‖ ^ β) (ball (0 : E d) r) := by
    rw [integrableOn_fun_norm_addHaar (volume : Measure (E d)) (f := fun y : ℝ ↦ y ^ β),
      finrank_euclideanSpace_fin]
    have hint : IntegrableOn (fun y : ℝ ↦ y ^ ((d : ℝ) - 1 + β)) (Ioo 0 r) := by
      rcases le_or_gt r 0 with hr | hr
      · simp [Ioo_eq_empty_of_le hr]
      · have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := r)
          (r := (d : ℝ) - 1 + β) (by linarith)).1
        exact this.mono_set Ioo_subset_Ioc_self
    refine hint.congr_fun (fun y hy ↦ ?_) measurableSet_Ioo
    simp only [smul_eq_mul]
    rw [← Real.rpow_natCast, ← Real.rpow_add hy.1, Nat.cast_sub hd, Nat.cast_one]
  rw [← integrable_indicator_iff measurableSet_ball] at h0 ⊢
  convert h0.comp_sub_right x₀ using 1
  funext x
  simp only [indicator, mem_ball, dist_eq_norm, sub_zero]

/-- **Weighted ball integrals in polar form.** For a bounded
measurable `h`, `β > -d` and `r ≥ 0`,
`∫_{B_r(x₀)} h(x) |x - x₀|^β dx = ∫_0^r τ^{d-1+β} ∫_𝕊 h(x₀ + τω) dσ(ω) dτ`. -/
theorem setIntegral_ball_mul_rpow_eq (hd : 1 ≤ d) {h : E d → ℝ} (hh : Measurable h) {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) (x₀ : E d) {β : ℝ} (hβ : -(d : ℝ) < β) {r : ℝ} (hr : 0 ≤ r) :
    ∫ x in ball x₀ r, h x * ‖x - x₀‖ ^ β =
      ∫ τ in 0..r, τ ^ ((d : ℝ) - 1 + β) *
        ∫ ω : sphere (0 : E d) 1, h (x₀ + τ • (ω : E d)) ∂(volume : Measure (E d)).toSphere := by
  have := nontrivial_E hd
  set G : E d → ℝ := (ball x₀ r).indicator fun x ↦ h x * ‖x - x₀‖ ^ β with hG
  have hGint : Integrable G := by
    rw [hG, integrable_indicator_iff measurableSet_ball]
    exact (integrableOn_ball_norm_sub_rpow hd x₀ hβ r).bdd_mul hh.aestronglyMeasurable
      (c := C) (ae_of_all _ fun x ↦ by rw [Real.norm_eq_abs]; exact hC x)
  have hpt : ∀ t ∈ Ioi (0 : ℝ), t ^ (Module.finrank ℝ (E d) - 1) •
      ∫ ω : sphere (0 : E d) 1, G (x₀ + t • (ω : E d)) ∂(volume : Measure (E d)).toSphere =
      (Iio r).indicator (fun t ↦ t ^ ((d : ℝ) - 1 + β) *
        ∫ ω : sphere (0 : E d) 1, h (x₀ + t • (ω : E d)) ∂(volume : Measure (E d)).toSphere) t := by
    intro t ht
    have ht : 0 < t := ht
    have hnorm : ∀ ω : sphere (0 : E d) 1, ‖x₀ + t • (ω : E d) - x₀‖ = t := fun ω ↦ by
      rw [add_sub_cancel_left, norm_smul, norm_eq_of_mem_sphere ω, mul_one,
        Real.norm_of_nonneg ht.le]
    have hmem : ∀ ω : sphere (0 : E d) 1, x₀ + t • (ω : E d) ∈ ball x₀ r ↔ t < r := fun ω ↦ by
      rw [mem_ball, dist_eq_norm, hnorm]
    have hexp : t ^ (Module.finrank ℝ (E d) - 1) * t ^ β = t ^ ((d : ℝ) - 1 + β) := by
      rw [finrank_euclideanSpace_fin, ← Real.rpow_natCast, ← Real.rpow_add ht, Nat.cast_sub hd,
        Nat.cast_one]
    by_cases htr : t < r
    · rw [indicator_of_mem (mem_Iio.2 htr)]
      simp_rw [hG, indicator_of_mem ((hmem _).2 htr), hnorm]
      rw [integral_mul_const, smul_eq_mul, ← hexp]
      ring
    · rw [indicator_of_notMem (by simpa using htr)]
      simp_rw [hG, indicator_of_notMem (mt (hmem _).1 htr)]
      simp
  rw [← integral_indicator measurableSet_ball, ← hG,
    integral_add_eq_integral_Ioi_integral_toSphere hGint x₀,
    setIntegral_congr_fun measurableSet_Ioi hpt, setIntegral_indicator measurableSet_Iio,
    Ioi_inter_Iio, intervalIntegral.integral_of_le hr, integral_Ioc_eq_integral_Ioo]

/-- The radial profile `τ ↦ τ^{d-1+β} ∫_𝕊 h(x₀ + τω) dσ(ω)` of a weighted ball integral. -/
private theorem stronglyMeasurable_radialProfile {h : E d → ℝ} (hh : Measurable h) (x₀ : E d)
    (e : ℝ) :
    StronglyMeasurable fun τ : ℝ ↦ τ ^ e *
      ∫ ω : sphere (0 : E d) 1, h (x₀ + τ • (ω : E d)) ∂(volume : Measure (E d)).toSphere :=
  ((measurable_id.pow_const e).stronglyMeasurable).mul
    (stronglyMeasurable_integral_toSphere hh x₀)

private theorem abs_radialProfile_le {h : E d → ℝ} {C : ℝ} (hC : ∀ x, |h x| ≤ C) (x₀ : E d)
    {e R τ : ℝ} (he : 0 ≤ e) (hτ : τ ∈ Icc 0 R) :
    |τ ^ e * ∫ ω : sphere (0 : E d) 1, h (x₀ + τ • (ω : E d)) ∂(volume : Measure (E d)).toSphere|
      ≤ R ^ e * (C * (volume : Measure (E d)).toSphere.real univ) := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hτ.1 e)]
  exact mul_le_mul (Real.rpow_le_rpow hτ.1 hτ.2 he) (abs_integral_toSphere_le fun ω ↦ hC _)
    (abs_nonneg _) (Real.rpow_nonneg (hτ.1.trans hτ.2) e)

private theorem intervalIntegrable_radialProfile {h : E d → ℝ} (hh : Measurable h) {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) (x₀ : E d) {e : ℝ} (he : 0 ≤ e) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IntervalIntegrable (fun τ : ℝ ↦ τ ^ e *
      ∫ ω : sphere (0 : E d) 1, h (x₀ + τ • (ω : E d)) ∂(volume : Measure (E d)).toSphere)
      volume a b := by
  set R := max a b
  have hsub : uIcc a b ⊆ Icc 0 R := by
    rw [uIcc]
    exact Icc_subset_Icc (le_min ha hb) le_rfl
  refine ((IntegrableOn.of_bound measure_Icc_lt_top
    (stronglyMeasurable_radialProfile hh x₀ e).aestronglyMeasurable
    (R ^ e * (C * (volume : Measure (E d)).toSphere.real univ))
    (ae_restrict_of_forall_mem measurableSet_Icc fun τ hτ ↦ ?_)).mono_set hsub).intervalIntegrable
  rw [Real.norm_eq_abs]
  exact abs_radialProfile_le hC x₀ he hτ

/-- **Weighted ball integrals are locally Lipschitz in the radius**: for a bounded measurable `h`
and `β ≥ 1 - d`, the map `r ↦ ∫_{B_r(x₀)} h |x - x₀|^β` is Lipschitz on `[0, R]`. -/
theorem exists_lipschitzOnWith_setIntegral_ball_mul_rpow (hd : 1 ≤ d) {h : E d → ℝ}
    (hh : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) (x₀ : E d) {β : ℝ}
    (hβ : 1 - (d : ℝ) ≤ β) (R : ℝ) :
    ∃ K, LipschitzOnWith K (fun r ↦ ∫ x in ball x₀ r, h x * ‖x - x₀‖ ^ β) (Icc 0 R) := by
  have he : 0 ≤ (d : ℝ) - 1 + β := by linarith
  have hβ' : -(d : ℝ) < β := by linarith
  set M := R ^ ((d : ℝ) - 1 + β) * (C * (volume : Measure (E d)).toSphere.real univ)
  refine ⟨Real.toNNReal M, LipschitzOnWith.of_dist_le_mul fun r hr r' hr' ↦ ?_⟩
  rw [setIntegral_ball_mul_rpow_eq hd hh hC x₀ hβ' hr.1,
    setIntegral_ball_mul_rpow_eq hd hh hC x₀ hβ' hr'.1, Real.dist_eq, Real.dist_eq,
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_radialProfile hh hC x₀ he le_rfl hr.1)
      (intervalIntegrable_radialProfile hh hC x₀ he le_rfl hr'.1)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := r') (b := r) (C := M)
    (f := fun τ : ℝ ↦ τ ^ ((d : ℝ) - 1 + β) *
      ∫ ω : sphere (0 : E d) 1, h (x₀ + τ • (ω : E d)) ∂(volume : Measure (E d)).toSphere)
    fun τ hτ ↦ by
      rw [Real.norm_eq_abs]
      have hτ' : τ ∈ Icc 0 R := by
        have := uIoc_subset_uIcc hτ
        rw [uIcc] at this
        exact ⟨le_trans (le_min hr'.1 hr.1) this.1, this.2.trans (max_le hr'.2 hr.2)⟩
      exact abs_radialProfile_le hC x₀ he hτ'
  rw [Real.norm_eq_abs] at hb
  refine hb.trans ?_
  exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal M) (abs_nonneg _)

/-- **Radial derivative of weighted ball integrals**: for a
bounded measurable `h` and `β ≥ 1 - d`, for a.e. `r > 0`,
`d/dr ∫_{B_r(x₀)} h |x - x₀|^β = r^{d-1+β} ∫_𝕊 h(x₀ + rω) dσ(ω)`. -/
theorem ae_hasDerivAt_setIntegral_ball_mul_rpow (hd : 1 ≤ d) {h : E d → ℝ}
    (hh : Measurable h) {C : ℝ} (hC : ∀ x, |h x| ≤ C) (x₀ : E d) {β : ℝ}
    (hβ : 1 - (d : ℝ) ≤ β) :
    ∀ᵐ r, 0 < r → HasDerivAt (fun s ↦ ∫ x in ball x₀ s, h x * ‖x - x₀‖ ^ β)
      (r ^ ((d : ℝ) - 1 + β) *
        ∫ ω : sphere (0 : E d) 1, h (x₀ + r • (ω : E d)) ∂(volume : Measure (E d)).toSphere) r := by
  have he : 0 ≤ (d : ℝ) - 1 + β := by linarith
  have hβ' : -(d : ℝ) < β := by linarith
  set F : ℝ → ℝ := fun τ ↦ τ ^ ((d : ℝ) - 1 + β) *
    ∫ ω : sphere (0 : E d) 1, h (x₀ + τ • (ω : E d)) ∂(volume : Measure (E d)).toSphere
  have hn : ∀ n : ℕ, ∀ᵐ r, r ∈ uIcc 0 ((n : ℝ) + 1) → ∀ c ∈ uIcc 0 ((n : ℝ) + 1),
      HasDerivAt (fun x ↦ ∫ t in c..x, F t) (F r) r := fun n ↦
    (intervalIntegrable_radialProfile hh hC x₀ he le_rfl (by positivity)).ae_hasDerivAt_integral
  filter_upwards [ae_all_iff.2 hn] with r hr hrpos
  obtain ⟨n, hnr⟩ := exists_nat_ge r
  have h0 : (0 : ℝ) ∈ uIcc 0 ((n : ℝ) + 1) := left_mem_uIcc
  have hmem : r ∈ uIcc 0 ((n : ℝ) + 1) := by
    rw [uIcc_of_le (by positivity)]
    exact ⟨hrpos.le, by linarith⟩
  refine (hr n hmem 0 h0).congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hrpos] with s hs
  exact setIntegral_ball_mul_rpow_eq hd hh hC x₀ hβ' hs.le

/-! ### The ACF integral -/

/-- The ACF integral in polar form: `I(w, x₀, r) = ∫_0^r τ q(τ) dτ` for an `L`-Lipschitz `w` and
`r ≥ 0`. -/
theorem acfIntegral_eq_integral (hd : 1 ≤ d) (hw : LipschitzWith L w) (x₀ : E d) {r : ℝ}
    (hr : 0 ≤ r) : acfIntegral w x₀ r = ∫ τ in 0..r, τ * radialQ w x₀ τ := by
  have hC : ∀ x, |‖∇ w x‖ ^ 2| ≤ (L : ℝ) ^ 2 := fun x ↦ by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_le_of_lipschitzWith hw x) 2
  rw [acfIntegral, setIntegral_ball_mul_rpow_eq hd ((measurable_gradient w).norm.pow_const 2) hC
    x₀ (by linarith) hr]
  refine intervalIntegral.integral_congr fun τ _ ↦ ?_
  simp only [radialQ]
  congr 1
  rw [show (d : ℝ) - 1 + (2 - d) = 1 by ring, Real.rpow_one]

/-- The ACF integral is Lipschitz in the radius on every `[0, R]`. -/
theorem exists_lipschitzOnWith_acfIntegral (hd : 1 ≤ d) (hw : LipschitzWith L w) (x₀ : E d)
    (R : ℝ) : ∃ K, LipschitzOnWith K (acfIntegral w x₀) (Icc 0 R) := by
  have hC : ∀ x, |‖∇ w x‖ ^ 2| ≤ (L : ℝ) ^ 2 := fun x ↦ by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_le_of_lipschitzWith hw x) 2
  exact exists_lipschitzOnWith_setIntegral_ball_mul_rpow hd
    ((measurable_gradient w).norm.pow_const 2) hC x₀ (by linarith) R

/-- `d/dr I(w, x₀, r) = r q(r)` for a.e. `r > 0`. -/
theorem ae_hasDerivAt_acfIntegral (hd : 1 ≤ d) (hw : LipschitzWith L w) (x₀ : E d) :
    ∀ᵐ r, 0 < r → HasDerivAt (acfIntegral w x₀) (r * radialQ w x₀ r) r := by
  have hC : ∀ x, |‖∇ w x‖ ^ 2| ≤ (L : ℝ) ^ 2 := fun x ↦ by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_le_of_lipschitzWith hw x) 2
  filter_upwards [ae_hasDerivAt_setIntegral_ball_mul_rpow hd
    ((measurable_gradient w).norm.pow_const 2) hC x₀ (β := 2 - d) (by linarith)] with r hr hrpos
  have h := hr hrpos
  rw [show (d : ℝ) - 1 + (2 - d) = 1 by ring, Real.rpow_one] at h
  exact h

end

end EllipticBernoulli
