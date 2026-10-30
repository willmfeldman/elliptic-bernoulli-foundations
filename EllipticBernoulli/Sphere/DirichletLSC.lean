/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sphere.Measure
public import Mathlib.Topology.ContinuousMap.Compact
import EllipticBernoulli.Sphere.HomogeneousExt
import EllipticBernoulli.Sobolev.L2
import EllipticBernoulli.Sobolev.Closure
import EllipticBernoulli.Sobolev.Uniqueness
import EllipticBernoulli.Sobolev.Lipschitz

/-!
# Lower semicontinuity of the Dirichlet energy on the sphere

A step in the polarization proof of the Pólya–Szegő inequality (`Sphere/PolyaSzego.lean`): if
`g_k → g₀` uniformly on the sphere and all `g_k`
and `g₀` are `L`-Lipschitz, then `∫_𝕊 |∇ĝ₀|² ≤ D` whenever `∫_𝕊 |∇ĝ_k|² ≤ D` for all `k`
(`sphDirichlet_le_of_tendsto`).

The proof transfers to the annulus `A = {1/2 < |x| < 2}`:

* `lintegral_annulus_eq`: for every `g`, `∫_A |∇ĝ|² = K_d ∫_𝕊 |∇ĝ|² dσ` with
  `K_d = ∫_{1/2}^2 t^{d-1} t^{-2} dt ∈ (0, ∞)`, by the polar formula and
  `|∇ĝ(tω)| = t⁻¹ |∇ĝ(ω)|`. (Since the scaling is exact, no weight is needed.)
* The gradients `∇ĝ_k` are bounded on `A`, so a subsequence converges weakly in `L²(A)`
  (`exists_tendstoWeakL2_subseq`) to some `G₀`, and `∫_A |G₀|² ≤ liminf ∫_A |∇ĝ_k|²`
  (`lintegral_weighted_sq_le_liminf`).
* `ĝ_k → ĝ₀` uniformly on `A`, so `G₀` is a weak gradient of `ĝ₀` (`HasWeakGradient.of_tendsto`),
  hence `G₀ = ∇ĝ₀` a.e. on `A` (`HasWeakGradient.ae_eq_of_eqOn`).
-/

open MeasureTheory Metric Set Filter Topology Module
open scoped Gradient NNReal ENNReal

namespace EllipticBernoulli

variable {d : ℕ}

/-- The annulus `{1/2 < |x| < 2}`. -/
private def annulus (d : ℕ) : Set (E d) := {x | 1 / 2 < ‖x‖ ∧ ‖x‖ < 2}

private theorem isOpen_annulus (d : ℕ) : IsOpen (annulus d) :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

private theorem annulus_subset (d : ℕ) : annulus d ⊆ {0}ᶜ := fun x hx h0 ↦ by
  rw [mem_singleton_iff] at h0
  have := hx.1
  rw [h0, norm_zero] at this
  norm_num at this

private theorem volume_annulus_lt_top (d : ℕ) : volume (annulus d) < ⊤ :=
  (measure_mono fun _ hx ↦ mem_ball_zero_iff.2 hx.2).trans_lt measure_ball_lt_top

/-- The radial constant `K_d = ∫_{1/2}^2 t^{d-1} t^{-2} dt`. -/
private noncomputable def annulusConst (d : ℕ) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (1 / 2 : ℝ) 2, ENNReal.ofReal (t ^ (d - 1)) * ENNReal.ofReal (t⁻¹ ^ 2)

private theorem annulusConst_ne_zero (d : ℕ) : annulusConst d ≠ 0 := by
  have hm : Measurable fun t : ℝ ↦ ENNReal.ofReal (t ^ (d - 1)) * ENNReal.ofReal (t⁻¹ ^ 2) :=
    by fun_prop
  refine (ne_of_gt ?_)
  rw [annulusConst, setLIntegral_pos_iff hm]
  refine lt_of_lt_of_le
    (by rw [Real.volume_Ioo]; norm_num : (0 : ℝ≥0∞) < volume (Ioo (1 / 2 : ℝ) 2))
    (measure_mono ?_)
  intro t ht
  refine ⟨?_, ht⟩
  have ht0 : 0 < t := by linarith [ht.1]
  simp only [Function.mem_support, ne_eq, mul_eq_zero, ENNReal.ofReal_eq_zero, not_or, not_le]
  exact ⟨pow_pos ht0 _, pow_pos (inv_pos.2 ht0) _⟩

private theorem annulusConst_ne_top (d : ℕ) : annulusConst d ≠ ⊤ := by
  refine (lt_of_le_of_lt (setLIntegral_mono (g := fun _ ↦ ENNReal.ofReal (2 ^ (d - 1)) *
    ENNReal.ofReal 4) measurable_const fun t ht ↦ ?_) ?_).ne
  · have ht0 : 0 < t := by linarith [ht.1]
    gcongr
    · exact ht.2.le
    · rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
      gcongr
      rw [inv_le_comm₀ ht0 two_pos]
      linarith [ht.1]
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top (by finiteness) (by simp)

/-- For `x` in the annulus, `|∇ĝ(x)| ≤ 8 L`. -/
private theorem norm_gradient_homogExt0_le_of_mem_annulus {g : sphere (0 : E d) 1 → ℝ}
    {L : ℝ≥0} (hg : LipschitzWith L g) {x : E d} (hx : x ∈ annulus d) :
    ‖∇ (homogExt0 g) x‖ ≤ 8 * L := by
  have hx0 : 0 < ‖x‖ := by linarith [hx.1]
  set ω : sphere (0 : E d) 1 := ⟨‖x‖⁻¹ • x, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx0.ne']⟩
  have hxω : x = ‖x‖ • (ω : E d) := by
    simp only [ω, smul_smul, mul_inv_cancel₀ hx0.ne', one_smul]
  rw [hxω, norm_gradient_homogExt0_smul g hx0]
  have h1 : ‖x‖⁻¹ ≤ 2 := by rw [inv_le_comm₀ hx0 two_pos]; linarith [hx.1]
  calc ‖x‖⁻¹ * ‖∇ (homogExt0 g) (ω : E d)‖ ≤ 2 * (4 * L) :=
        mul_le_mul h1 (norm_gradient_homogExt0_le hg ω) (norm_nonneg _) zero_le_two
    _ = 8 * L := by ring

/-- **The energy on the annulus**: `∫_A |∇ĝ|² = K_d ∫_𝕊 |∇ĝ|² dσ`. -/
private theorem lintegral_annulus_eq (hd : 1 ≤ d) (g : sphere (0 : E d) 1 → ℝ) :
    ∫⁻ x in annulus d, ENNReal.ofReal (‖∇ (homogExt0 g) x‖ ^ 2) =
      annulusConst d * ∫⁻ ω, ENNReal.ofReal (‖∇ (homogExt0 g) (ω : E d)‖ ^ 2)
        ∂(volume : Measure (E d)).toSphere := by
  have := nontrivial_E hd
  set F : E d → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (‖∇ (homogExt0 g) x‖ ^ 2)
  have hF : Measurable F := ((measurable_gradient _).norm.pow_const 2).ennreal_ofReal
  set I := ∫⁻ ω, F (ω : E d) ∂(volume : Measure (E d)).toSphere
  have hA : MeasurableSet (annulus d) := (isOpen_annulus d).measurableSet
  rw [← lintegral_indicator hA, lintegral_eq_lintegral_Ioi_lintegral_toSphere
    (hF.indicator hA), finrank_euclideanSpace_fin]
  set k : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (t ^ (d - 1)) * ENNReal.ofReal (t⁻¹ ^ 2)
  have hk : Measurable k := by fun_prop
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (t ^ (d - 1)) *
      ∫⁻ ω : sphere (0 : E d) 1, (annulus d).indicator F (t • (ω : E d))
        ∂(volume : Measure (E d)).toSphere = (Ioo (1 / 2 : ℝ) 2).indicator k t * I := by
    intro t ht
    have ht : 0 < t := ht
    have hnorm : ∀ ω : sphere (0 : E d) 1, ‖t • (ω : E d)‖ = t := fun ω ↦ by
      rw [norm_smul, norm_eq_of_mem_sphere ω, mul_one, Real.norm_of_nonneg ht.le]
    by_cases htA : t ∈ Ioo (1 / 2 : ℝ) 2
    · have hin : ∀ ω : sphere (0 : E d) 1, (annulus d).indicator F (t • (ω : E d)) =
          ENNReal.ofReal (t⁻¹ ^ 2) * F ω := fun ω ↦ by
        rw [indicator_of_mem (show t • (ω : E d) ∈ annulus d by
          change 1 / 2 < ‖t • (ω : E d)‖ ∧ ‖t • (ω : E d)‖ < 2
          rw [hnorm]; exact htA)]
        simp only [F, norm_gradient_homogExt0_smul g ht, mul_pow]
        rw [ENNReal.ofReal_mul (sq_nonneg _), inv_pow]
      simp_rw [hin]
      rw [lintegral_const_mul' _ (fun ω : sphere (0 : E d) 1 ↦ F ω) ENNReal.ofReal_ne_top,
        indicator_of_mem htA]
      simp only [k]
      ring
    · have hout : ∀ ω : sphere (0 : E d) 1, (annulus d).indicator F (t • (ω : E d)) = 0 :=
        fun ω ↦ indicator_of_notMem (fun h ↦ htA (by
          have h' : 1 / 2 < ‖t • (ω : E d)‖ ∧ ‖t • (ω : E d)‖ < 2 := h
          rwa [hnorm] at h')) _
      simp_rw [hout]
      rw [lintegral_zero, mul_zero, indicator_of_notMem htA, zero_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioi hpt, lintegral_mul_const _ (hk.indicator
    measurableSet_Ioo), setLIntegral_indicator measurableSet_Ioo,
    inter_eq_left.2 (show Ioo (1 / 2 : ℝ) 2 ⊆ Ioi 0 from fun t ht ↦ by
      change (0 : ℝ) < t; linarith [ht.1])]
  rfl

private theorem sphDirichlet_eq_toReal (g : sphere (0 : E d) 1 → ℝ) :
    sphDirichlet g = (∫⁻ ω, ENNReal.ofReal (‖∇ (homogExt0 g) (ω : E d)‖ ^ 2)
      ∂(volume : Measure (E d)).toSphere).toReal := by
  rw [sphDirichlet, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ sq_nonneg _)
    (((measurable_gradient _).norm.pow_const 2).comp measurable_subtype_coe).aestronglyMeasurable]

private theorem lintegral_sphere_ne_top {g : sphere (0 : E d) 1 → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) :
    ∫⁻ ω, ENNReal.ofReal (‖∇ (homogExt0 g) (ω : E d)‖ ^ 2)
      ∂(volume : Measure (E d)).toSphere ≠ ⊤ := by
  refine (lt_of_le_of_lt (lintegral_mono (g := fun _ ↦ ENNReal.ofReal ((4 * L : ℝ) ^ 2))
    fun ω ↦ ENNReal.ofReal_le_ofReal ?_) ?_).ne
  · exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_homogExt0_le hg ω) 2
  · rw [lintegral_const]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

public section

/-- **Lower semicontinuity of the Dirichlet energy.** Let `d ≥ 1`. If `g_k → g₀` in `C(𝕊, ℝ)`, all
`g_k` and `g₀` are `L`-Lipschitz, and `∫_𝕊 |∇ĝ_k|² ≤ D` for all `k`, then `∫_𝕊 |∇ĝ₀|² ≤ D`. -/
theorem sphDirichlet_le_of_tendsto (hd : 1 ≤ d) {L : ℝ≥0} {g : ℕ → C(sphere (0 : E d) 1, ℝ)}
    {g₀ : C(sphere (0 : E d) 1, ℝ)} (hgL : ∀ k, LipschitzWith L (g k))
    (hg₀L : LipschitzWith L g₀) (hlim : Tendsto g atTop (𝓝 g₀)) {D : ℝ}
    (hD : ∀ k, sphDirichlet (g k) ≤ D) : sphDirichlet g₀ ≤ D := by
  set A := annulus d
  have hAo := isOpen_annulus d
  have hAm : MeasurableSet A := hAo.measurableSet
  have hAfin : volume A ≠ ⊤ := (volume_annulus_lt_top d).ne
  have : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.2 hAfin
  set v : ℕ → E d → ℝ := fun k ↦ homogExt0 (g k)
  set v₀ : E d → ℝ := homogExt0 g₀
  set G : ℕ → E d → E d := fun k ↦ ∇ (v k)
  have hD0 : 0 ≤ D := (integral_nonneg fun _ ↦ sq_nonneg _).trans (hD 0)
  -- the gradients are bounded in `L²(A)`
  have hGb : ∀ k, ∀ x ∈ A, ‖G k x‖ ≤ 8 * L := fun k x hx ↦
    norm_gradient_homogExt0_le_of_mem_annulus (hgL k) hx
  have hGL2 : ∀ k, MemLp (G k) 2 (volume.restrict A) := fun k ↦
    MemLp.of_bound (measurable_gradient _).aestronglyMeasurable (8 * L)
      (ae_restrict_of_forall_mem hAm (hGb k))
  set B : ℝ≥0∞ := volume.restrict A univ ^ (2 : ℝ≥0∞).toReal⁻¹ * ENNReal.ofReal (8 * L)
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    (measure_ne_top _ _)) ENNReal.ofReal_ne_top
  have hGbd : ∀ k, eLpNorm (G k) 2 (volume.restrict A) ≤ ENNReal.ofReal B.toReal := fun k ↦ by
    rw [ENNReal.ofReal_toReal hB]
    exact eLpNorm_le_of_ae_bound (measurable_gradient _).aestronglyMeasurable
      (ae_restrict_of_forall_mem hAm (hGb k))
  obtain ⟨φ, hφ, G₀, hconv⟩ := exists_tendstoWeakL2_subseq volume A G _ hGL2 hGbd
  -- lower semicontinuity
  have hlsc := lintegral_weighted_sq_le_liminf volume A _ G₀ hconv (fun _ ↦ 1)
    measurable_const (fun _ ↦ zero_le_one) 1 (fun _ ↦ le_rfl)
  simp only [one_mul] at hlsc
  have hbound : ∀ k, ∫⁻ x in A, ENNReal.ofReal (‖G (φ k) x‖ ^ 2) ≤
      annulusConst d * ENNReal.ofReal D := fun k ↦ by
    rw [lintegral_annulus_eq hd]
    gcongr
    rw [← ENNReal.ofReal_toReal (lintegral_sphere_ne_top (hgL (φ k))), ← sphDirichlet_eq_toReal]
    exact ENNReal.ofReal_le_ofReal (hD _)
  have hG₀ : ∫⁻ x in A, ENNReal.ofReal (‖G₀ x‖ ^ 2) ≤ annulusConst d * ENNReal.ofReal D :=
    hlsc.trans (liminf_le_of_frequently_le' (Frequently.of_forall hbound))
  -- identification of the weak limit
  have hloc : ∀ {h : sphere (0 : E d) 1 → ℝ}, LipschitzWith L h →
      LocallyLipschitzOn A (homogExt0 h) := fun hh ↦
    (locallyLipschitzOn_homogExt0 hh).mono (annulus_subset d)
  have hvG : ∀ k, HasWeakGradient A (v (φ k)) (G (φ k)) := fun k ↦
    (memH1Loc_gradient_of_locallyLipschitzOn hAo (hloc (hgL (φ k)))).1
  have hv₀G : HasWeakGradient A v₀ (∇ v₀) :=
    (memH1Loc_gradient_of_locallyLipschitzOn hAo (hloc hg₀L)).1
  have hdist : Tendsto (fun k ↦ dist (g (φ k)) g₀) atTop (𝓝 0) :=
    (tendsto_iff_dist_tendsto_zero.1 hlim).comp hφ.tendsto_atTop
  have hvconv : TendstoLpLoc 2 volume A (fun k ↦ v (φ k)) v₀ atTop := by
    intro K hKA hK
    have hKfin : volume.restrict K univ ≠ ⊤ := by
      rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top.ne
    have hle : ∀ k, eLpNorm (v (φ k) - v₀) 2 (volume.restrict K) ≤
        volume.restrict K univ ^ (2 : ℝ≥0∞).toReal⁻¹ *
          ENNReal.ofReal (dist (g (φ k)) g₀) := fun k ↦ by
      refine eLpNorm_le_of_ae_bound ((((hloc (hgL (φ k))).continuousOn.sub
        (hloc hg₀L).continuousOn).mono hKA).aestronglyMeasurable hK.measurableSet)
        (ae_restrict_of_forall_mem hK.measurableSet fun x hx ↦ ?_)
      have hx0 : x ≠ 0 := annulus_subset d (hKA hx)
      simp only [v, v₀, Pi.sub_apply, homogExt0_of_ne_zero _ hx0, Real.norm_eq_abs]
      rw [← Real.dist_eq]
      exact ContinuousMap.dist_apply_le_dist _
    have htend : Tendsto (fun k ↦ volume.restrict K univ ^ (2 : ℝ≥0∞).toReal⁻¹ *
        ENNReal.ofReal (dist (g (φ k)) g₀)) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal hdist)
        (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hKfin) :
          ENNReal.ofReal 0 ≠ 0 ∨ volume.restrict K univ ^ (2 : ℝ≥0∞).toReal⁻¹ ≠ ⊤)
      rwa [ENNReal.ofReal_zero, mul_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend
      (fun _ ↦ bot_le) hle
  have hv₀m : AEStronglyMeasurable v₀ (volume.restrict A) :=
    (hloc hg₀L).continuousOn.aestronglyMeasurable hAm
  have hW := HasWeakGradient.of_tendsto hAo hvG hv₀m hvconv fun K hKA hK ↦
    hconv.mono_set hK.measurableSet hKA
  have hae := HasWeakGradient.ae_eq_of_eqOn hAo hAo subset_rfl hW hv₀G (fun _ _ ↦ rfl)
  -- conclusion
  have hfinal : annulusConst d * ∫⁻ ω, ENNReal.ofReal (‖∇ v₀ (ω : E d)‖ ^ 2)
      ∂(volume : Measure (E d)).toSphere ≤ annulusConst d * ENNReal.ofReal D := by
    rw [← lintegral_annulus_eq hd]
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) hG₀
    filter_upwards [hae] with x hx
    rw [hx]
  rw [ENNReal.mul_le_mul_iff_right (annulusConst_ne_zero d) (annulusConst_ne_top d)] at hfinal
  rw [sphDirichlet_eq_toReal]
  exact ENNReal.toReal_le_of_le_ofReal hD0 hfinal

end

end EllipticBernoulli
