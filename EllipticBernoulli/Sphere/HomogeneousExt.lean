/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.TwoPhase.Defs
public import EllipticBernoulli.Harmonic.Polar
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The `0`-homogeneous extension

Facts about `homogExt0 f`, `x ↦ f (x / ‖x‖)`, for a function `f` on the unit sphere.
The tangential gradient of `f` is `∇f̂` restricted to the sphere.

* `homogExt0_smul`: `f̂(t x) = f̂(x)` for `t > 0`.
* `gradient_homogExt0_smul`: `∇f̂(t x) = t⁻¹ ∇f̂(x)` for `t > 0` (at every point; both sides
  vanish where `f̂` is not differentiable), and `norm_gradient_homogExt0_smul`.
* `inner_gradient_homogExt0_self`: `∇f̂(x) ⊥ x`.
* `lipschitzOnWith_homogExt0`: if `f` is `K`-Lipschitz (chordal metric), then `f̂` is
  `4K`-Lipschitz on `{‖x‖ ≥ 1/2}` (the constant is not optimal; any constant serves).
  More generally `lipschitzOnWith_homogExt0_of_pos` (`2K/ρ` on `{‖x‖ ≥ ρ}`),
  `locallyLipschitzOn_homogExt0` (on `E d \ {0}`), and `norm_gradient_homogExt0_le`
  (`‖∇f̂(ω)‖ ≤ 4K` on the sphere).
* `ae_differentiableAt_homogExt0`: for Lipschitz `f`, `f̂` is differentiable at `σ`-a.e. point of
  the sphere (the non-differentiability set is a Lebesgue-null cone).
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped Gradient NNReal

namespace EllipticBernoulli

variable {d : ℕ}

public section

/-- The `0`-homogeneous extension is invariant under positive dilations. -/
theorem homogExt0_smul (f : sphere (0 : E d) 1 → ℝ) {t : ℝ} (ht : 0 < t) (x : E d) :
    homogExt0 f (t • x) = homogExt0 f x := by
  by_cases hx : x = 0
  · simp [hx]
  have htx : t • x ≠ 0 := smul_ne_zero ht.ne' hx
  rw [homogExt0_of_ne_zero f htx, homogExt0_of_ne_zero f hx]
  congr 2
  rw [norm_smul, Real.norm_of_nonneg ht.le, mul_inv, smul_smul]
  congr 1
  field_simp

theorem homogExt0_comp_smul (f : sphere (0 : E d) 1 → ℝ) {t : ℝ} (ht : 0 < t) :
    (fun x ↦ homogExt0 f (t • x)) = homogExt0 f :=
  funext (homogExt0_smul f ht)

/-- `D f̂(x) = t D f̂(t x)` for `t > 0`. -/
theorem fderiv_homogExt0_eq_smul (f : sphere (0 : E d) 1 → ℝ) {t : ℝ} (ht : 0 < t) (x : E d) :
    fderiv ℝ (homogExt0 f) x = t • fderiv ℝ (homogExt0 f) (t • x) := by
  conv_lhs => rw [← homogExt0_comp_smul f ht]
  exact fderiv_comp_smul (f := homogExt0 f) t

/-- **Scaling of the tangential gradient**: `∇f̂(t x) = t⁻¹ ∇f̂(x)` for `t > 0`. -/
theorem gradient_homogExt0_smul (f : sphere (0 : E d) 1 → ℝ) {t : ℝ} (ht : 0 < t) (x : E d) :
    ∇ (homogExt0 f) (t • x) = t⁻¹ • ∇ (homogExt0 f) x := by
  rw [gradient, gradient, fderiv_homogExt0_eq_smul f ht x, map_smul, smul_smul,
    inv_mul_cancel₀ ht.ne', one_smul]

theorem norm_gradient_homogExt0_smul (f : sphere (0 : E d) 1 → ℝ) {t : ℝ} (ht : 0 < t)
    (x : E d) : ‖∇ (homogExt0 f) (t • x)‖ = t⁻¹ * ‖∇ (homogExt0 f) x‖ := by
  rw [gradient_homogExt0_smul f ht, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le)]

/-- Differentiability of `f̂` is invariant under positive dilations. -/
theorem differentiableAt_homogExt0_smul_iff (f : sphere (0 : E d) 1 → ℝ) {t : ℝ} (ht : 0 < t)
    (x : E d) :
    DifferentiableAt ℝ (homogExt0 f) (t • x) ↔ DifferentiableAt ℝ (homogExt0 f) x := by
  constructor
  · intro h
    have := h.comp x ((differentiableAt_id).const_smul t)
    have e : (homogExt0 f ∘ HSMul.hSMul t : E d → ℝ) = homogExt0 f := homogExt0_comp_smul f ht
    rwa [e] at this
  · intro h
    have hx : x = t⁻¹ • (t • x) := by rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    rw [hx] at h
    have := h.comp (t • x) ((differentiableAt_id).const_smul t⁻¹)
    have e : (homogExt0 f ∘ HSMul.hSMul t⁻¹ : E d → ℝ) = homogExt0 f :=
      homogExt0_comp_smul f (inv_pos.2 ht)
    rwa [e] at this

/-- **The tangential gradient is tangential**: `∇f̂(x) ⊥ x`. -/
theorem inner_gradient_homogExt0_self (f : sphere (0 : E d) 1 → ℝ) (x : E d) :
    inner ℝ (∇ (homogExt0 f) x) x = 0 := by
  rw [gradient, toDual_symm_apply]
  by_cases hdiff : DifferentiableAt ℝ (homogExt0 f) x
  · have hray : HasDerivAt (fun s : ℝ ↦ s • x) x 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
    have h1 : HasDerivAt (fun s : ℝ ↦ homogExt0 f (s • x)) (fderiv ℝ (homogExt0 f) x x) 1 := by
      exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (1 : ℝ) hray (one_smul ℝ x).symm
    have h2 : HasDerivAt (fun s : ℝ ↦ homogExt0 f (s • x)) 0 1 := by
      refine (hasDerivAt_const (1 : ℝ) (homogExt0 f x)).congr_of_eventuallyEq ?_
      filter_upwards [lt_mem_nhds one_pos] with s hs
      exact homogExt0_smul f hs x
    exact h1.unique h2
  · rw [fderiv_zero_of_not_differentiableAt hdiff, zero_apply]

private theorem norm_normalize_sub_le {x y : E d} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ 2 * ‖x - y‖ / ‖x‖ := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hsplit : ‖x‖⁻¹ • x - ‖y‖⁻¹ • y = ‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y := by
    rw [smul_sub, sub_smul]; abel
  have h2 : ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ ≤ ‖x - y‖ / ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, inv_sub_inv hxn.ne' hyn.ne', abs_div, abs_mul,
      abs_of_pos hxn, abs_of_pos hyn]
    have := abs_norm_sub_norm_le y x
    rw [norm_sub_rev y x] at this
    calc |‖y‖ - ‖x‖| / (‖x‖ * ‖y‖) * ‖y‖ = |‖y‖ - ‖x‖| / ‖x‖ := by field_simp
      _ ≤ ‖x - y‖ / ‖x‖ := by gcongr
  calc ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ ‖‖x‖⁻¹ • (x - y)‖ + ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ ‖x - y‖ / ‖x‖ + ‖x - y‖ / ‖x‖ := by
        gcongr
        rw [norm_smul, norm_inv, norm_norm, inv_mul_eq_div]
    _ = 2 * ‖x - y‖ / ‖x‖ := by ring

/-- If `f` is `K`-Lipschitz on the sphere (chordal metric), then `f̂` is `4K`-Lipschitz on
`{‖x‖ ≥ 1/2}`. -/
theorem lipschitzOnWith_homogExt0 {f : sphere (0 : E d) 1 → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzOnWith (4 * K) (homogExt0 f) {x | 1 / 2 ≤ ‖x‖} := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  have hx' : (1 : ℝ) / 2 ≤ ‖x‖ := hx
  have hy' : (1 : ℝ) / 2 ≤ ‖y‖ := hy
  have hx0 : x ≠ 0 := norm_pos_iff.1 (by linarith)
  have hy0 : y ≠ 0 := norm_pos_iff.1 (by linarith)
  rw [homogExt0_of_ne_zero f hx0, homogExt0_of_ne_zero f hy0]
  refine (hf.dist_le_mul _ _).trans ?_
  rw [Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
  have h := norm_normalize_sub_le hx0 hy0
  have hxpos : 0 < ‖x‖ := by linarith
  have : 2 * ‖x - y‖ / ‖x‖ ≤ 4 * ‖x - y‖ := by
    rw [div_le_iff₀ hxpos]
    nlinarith [norm_nonneg (x - y)]
  calc (K : ℝ) * ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ K * (4 * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (h.trans this) K.2
    _ = ((4 * K : ℝ≥0) : ℝ) * ‖x - y‖ := by push_cast; ring

/-- If `f` is `K`-Lipschitz on the sphere, then `f̂` is `(2K/ρ)`-Lipschitz on `{‖x‖ ≥ ρ}`, for
every `ρ > 0`. -/
theorem lipschitzOnWith_homogExt0_of_pos {f : sphere (0 : E d) 1 → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {ρ : ℝ} (hρ : 0 < ρ) :
    LipschitzOnWith (Real.toNNReal (2 * K / ρ)) (homogExt0 f) {x | ρ ≤ ‖x‖} := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  have hx' : ρ ≤ ‖x‖ := hx
  have hy' : ρ ≤ ‖y‖ := hy
  have hx0 : x ≠ 0 := norm_pos_iff.1 (by linarith)
  have hy0 : y ≠ 0 := norm_pos_iff.1 (by linarith)
  rw [homogExt0_of_ne_zero f hx0, homogExt0_of_ne_zero f hy0]
  refine (hf.dist_le_mul _ _).trans ?_
  rw [Subtype.dist_eq, dist_eq_norm, dist_eq_norm,
    Real.coe_toNNReal _ (by positivity)]
  have h := norm_normalize_sub_le hx0 hy0
  have : 2 * ‖x - y‖ / ‖x‖ ≤ 2 * ‖x - y‖ / ρ :=
    div_le_div_of_nonneg_left (by positivity) hρ hx'
  calc (K : ℝ) * ‖‖x‖⁻¹ • x - ‖y‖⁻¹ • y‖ ≤ K * (2 * ‖x - y‖ / ρ) :=
        mul_le_mul_of_nonneg_left (h.trans this) K.2
    _ = 2 * K / ρ * ‖x - y‖ := by ring

/-- For Lipschitz `f`, `f̂` is locally Lipschitz on `E d \ {0}`. -/
theorem locallyLipschitzOn_homogExt0 {f : sphere (0 : E d) 1 → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : LocallyLipschitzOn {0}ᶜ (homogExt0 f) := by
  intro x hx
  have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
  refine ⟨_, {y | ‖x‖ / 2 ≤ ‖y‖}, ?_, lipschitzOnWith_homogExt0_of_pos hf (half_pos hx0)⟩
  refine mem_nhdsWithin_of_mem_nhds ?_
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
    (show ‖x‖ / 2 < ‖x‖ by linarith)] with y hy
  exact le_of_lt hy

/-- For Lipschitz `f`, `‖∇f̂(ω)‖ ≤ 4K` on the unit sphere. -/
theorem norm_gradient_homogExt0_le {f : sphere (0 : E d) 1 → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (ω : sphere (0 : E d) 1) :
    ‖∇ (homogExt0 f) (ω : E d)‖ ≤ 4 * K := by
  have hs : {x : E d | 1 / 2 ≤ ‖x‖} ∈ 𝓝 (ω : E d) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
      (show (1 : ℝ) / 2 < ‖(ω : E d)‖ by rw [norm_eq_of_mem_sphere ω]; norm_num)] with y hy
    exact le_of_lt hy
  rw [gradient, LinearIsometryEquiv.norm_map]
  have := norm_fderiv_le_of_lipschitzOn ℝ hs (lipschitzOnWith_homogExt0 hf)
  simpa using this

/-- For Lipschitz `f`, the extension `f̂` is differentiable at `σ`-a.e. point of the sphere: the
set of points of non-differentiability is a Lebesgue-null cone. -/
theorem ae_differentiableAt_homogExt0 (hd : 1 ≤ d) {f : sphere (0 : E d) 1 → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∀ᵐ ω : sphere (0 : E d) 1 ∂(volume : Measure (E d)).toSphere,
      DifferentiableAt ℝ (homogExt0 f) (ω : E d) := by
  have := nontrivial_E hd
  have hU : IsOpen {x : E d | 1 / 2 < ‖x‖} := isOpen_lt continuous_const continuous_norm
  have hlip := (lipschitzOnWith_homogExt0 hf).mono (fun x (hx : 1 / 2 < ‖x‖) ↦ hx.le)
  have hae : ∀ᵐ x ∂(volume : Measure (E d)), 1 / 2 < ‖x‖ →
      DifferentiableAt ℝ (homogExt0 f) x := by
    filter_upwards [hlip.ae_differentiableWithinAt_of_mem] with x hx hxU
    exact (hx hxU).differentiableAt (hU.mem_nhds hxU)
  have h := ae_ae_toSphere_of_ae hae 0
  have h1 : ∀ᵐ t ∂(volume.restrict (Ioi (1 : ℝ))), ∀ᵐ ω : sphere (0 : E d) 1
      ∂(volume : Measure (E d)).toSphere,
      1 / 2 < ‖0 + t • (ω : E d)‖ → DifferentiableAt ℝ (homogExt0 f) (0 + t • (ω : E d)) :=
    ae_restrict_of_ae_restrict_of_subset (Ioi_subset_Ioi zero_le_one) h
  have : (ae (volume.restrict (Ioi (1 : ℝ)))).NeBot :=
    ae_neBot.mpr (by simp [Measure.restrict_eq_zero])
  obtain ⟨t, ht, htpos⟩ := (h1.and (ae_restrict_mem measurableSet_Ioi)).exists
  have htpos : (1 : ℝ) < t := htpos
  filter_upwards [ht] with ω hω
  have hnorm : ‖0 + t • (ω : E d)‖ = t := by
    rw [zero_add, norm_smul, norm_eq_of_mem_sphere ω, mul_one, Real.norm_of_nonneg (by linarith)]
  have := hω (by rw [hnorm]; linarith)
  rwa [zero_add, differentiableAt_homogExt0_smul_iff f (by linarith)] at this

end

end EllipticBernoulli
