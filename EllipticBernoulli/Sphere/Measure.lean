/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.TwoPhase.Defs
public import EllipticBernoulli.Harmonic.Polar
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import EllipticBernoulli.Sphere.HomogeneousExt
import EllipticBernoulli.Blowup.Constancy
import EllipticBernoulli.Sobolev.Lipschitz
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The sphere measure

Basic properties of the sphere measure `σ = (volume : Measure (E d)).toSphere` and of the
Rayleigh quotient `sphRayleigh`.

* `sphereMap R`: a linear isometry equivalence `R` of `E d`, restricted to the unit sphere.
* `measurePreserving_sphereMap`: `σ` is invariant under linear isometries.
* `toSphere_pos_of_isOpen`: `σ` is positive on nonempty (relatively) open sets.
* `homogExt0_comp_sphereMap`, `norm_gradient_homogExt0_comp_sphereMap`: the `0`-homogeneous
  extension and its gradient norm commute with `R`.
* `sphDirichlet_comp_sphereMap`, `sphL2Sq_comp_sphereMap`, `sphRayleigh_comp_sphereMap`: the
  Dirichlet energy, the `L²` norm and the Rayleigh quotient are invariant under isometries.
* `IsSphAdmissible.comp_sphereMap` and `sphEigenvalue_preimage_sphereMap`: admissibility and
  `λ₁` are invariant: `λ₁(R⁻¹ Γ) = λ₁(Γ)`.
* `IsSphAdmissible.sphRayleigh_pos`: for `d ≥ 2` and `Γ ≠ 𝕊`, admissible functions have positive
  Rayleigh quotient.

The cone lemma is `toSphere_preimage_eq_zero_of_cone` and
`ae_ae_toSphere_of_ae` in `Harmonic/Polar.lean`.
-/

open MeasureTheory Metric Set Filter
open scoped Gradient ENNReal NNReal Pointwise

namespace EllipticBernoulli

variable {d : ℕ}

@[expose] public section

/-- A linear isometry equivalence `R` of `E d`, restricted to the unit sphere. -/
def sphereMap (R : E d ≃ₗᵢ[ℝ] E d) (ω : sphere (0 : E d) 1) : sphere (0 : E d) 1 :=
  ⟨R ω, by rw [mem_sphere_zero_iff_norm, R.norm_map]; exact norm_eq_of_mem_sphere ω⟩

end

public section

@[simp]
theorem coe_sphereMap (R : E d ≃ₗᵢ[ℝ] E d) (ω : sphere (0 : E d) 1) :
    (sphereMap R ω : E d) = R ω := rfl

theorem sphereMap_symm_sphereMap (R : E d ≃ₗᵢ[ℝ] E d) (ω : sphere (0 : E d) 1) :
    sphereMap R.symm (sphereMap R ω) = ω := by
  ext1; simp

theorem sphereMap_sphereMap_symm (R : E d ≃ₗᵢ[ℝ] E d) (ω : sphere (0 : E d) 1) :
    sphereMap R (sphereMap R.symm ω) = ω := by
  ext1; simp

theorem isometry_sphereMap (R : E d ≃ₗᵢ[ℝ] E d) : Isometry (sphereMap R) :=
  Isometry.of_dist_eq fun ω ω' ↦ by
    rw [Subtype.dist_eq, Subtype.dist_eq, coe_sphereMap, coe_sphereMap, R.dist_map]

theorem continuous_sphereMap (R : E d ≃ₗᵢ[ℝ] E d) : Continuous (sphereMap R) :=
  (isometry_sphereMap R).continuous

/-- `sphereMap R` as a measurable equivalence of the unit sphere. -/
noncomputable def sphereMapMeasurableEquiv (R : E d ≃ₗᵢ[ℝ] E d) :
    sphere (0 : E d) 1 ≃ᵐ sphere (0 : E d) 1 where
  toFun := sphereMap R
  invFun := sphereMap R.symm
  left_inv := sphereMap_symm_sphereMap R
  right_inv := sphereMap_sphereMap_symm R
  measurable_toFun := (continuous_sphereMap R).measurable
  measurable_invFun := (continuous_sphereMap R.symm).measurable

/-- **Isometry invariance of the sphere measure.** Every linear isometry `R` of `E d` preserves
`σ`. -/
theorem measurePreserving_sphereMap (R : E d ≃ₗᵢ[ℝ] E d) :
    MeasurePreserving (sphereMap R) (volume : Measure (E d)).toSphere
      (volume : Measure (E d)).toSphere := by
  have hRm : MeasurePreserving R (volume : Measure (E d)) volume := R.measurePreserving
  have hemb : MeasurableEmbedding R := R.toHomeomorph.measurableEmbedding
  refine ⟨(continuous_sphereMap R).measurable, Measure.ext fun s hs ↦ ?_⟩
  have hs' : MeasurableSet (sphereMap R ⁻¹' s) := (continuous_sphereMap R).measurable hs
  rw [Measure.map_apply (continuous_sphereMap R).measurable hs,
    Measure.toSphere_apply' _ hs', Measure.toSphere_apply' _ hs]
  congr 1
  have hset : Ioo (0 : ℝ) 1 • ((↑) '' (sphereMap R ⁻¹' s) : Set (E d)) =
      R ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    ext x
    simp only [Set.mem_smul, mem_preimage]
    constructor
    · rintro ⟨t, ht, _, ⟨ω, hω, rfl⟩, rfl⟩
      exact ⟨t, ht, _, ⟨sphereMap R ω, hω, rfl⟩, by simp⟩
    · rintro ⟨t, ht, _, ⟨ω, hω, rfl⟩, hx⟩
      refine ⟨t, ht, _, ⟨sphereMap R.symm ω, by simpa [sphereMap_sphereMap_symm] using hω, rfl⟩,
        ?_⟩
      apply R.injective
      simpa using hx
  rw [hset, hRm.measure_preimage_emb hemb]

/-- Integrals over the sphere are invariant under linear isometries. -/
theorem integral_comp_sphereMap (R : E d ≃ₗᵢ[ℝ] E d) (g : sphere (0 : E d) 1 → ℝ) :
    ∫ ω, g (sphereMap R ω) ∂(volume : Measure (E d)).toSphere =
      ∫ ω, g ω ∂(volume : Measure (E d)).toSphere :=
  MeasurePreserving.integral_comp' (f := sphereMapMeasurableEquiv R)
    (measurePreserving_sphereMap R) g

/-- **Positivity on open sets.** A nonempty (relatively) open subset of the unit sphere has
positive `σ`-measure. -/
theorem toSphere_pos_of_isOpen {U : Set (sphere (0 : E d) 1)} (hU : IsOpen U)
    (hne : U.Nonempty) : 0 < (volume : Measure (E d)).toSphere U :=
  hU.measure_pos _ hne

/-! ### The `0`-homogeneous extension and isometries -/

/-- `(f ∘ R)^ = f̂ ∘ R`. -/
theorem homogExt0_comp_sphereMap (R : E d ≃ₗᵢ[ℝ] E d) (f : sphere (0 : E d) 1 → ℝ) :
    homogExt0 (f ∘ sphereMap R) = homogExt0 f ∘ R := by
  funext x
  by_cases hx : x = 0
  · simp [hx]
  have hRx : R x ≠ 0 := by simpa using hx
  simp only [Function.comp_apply, homogExt0_of_ne_zero _ hx, homogExt0_of_ne_zero _ hRx]
  congr 1
  ext1
  simp

/-- `|∇(f ∘ R)^(x)| = |∇f̂(Rx)|`, at every point (both sides vanish where the extensions are not
differentiable). -/
theorem norm_gradient_homogExt0_comp_sphereMap (R : E d ≃ₗᵢ[ℝ] E d)
    (f : sphere (0 : E d) 1 → ℝ) (x : E d) :
    ‖∇ (homogExt0 (f ∘ sphereMap R)) x‖ = ‖∇ (homogExt0 f) (R x)‖ := by
  rw [homogExt0_comp_sphereMap, gradient, gradient, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map]
  have h := (R.toContinuousLinearEquiv).comp_right_fderiv (𝕜 := ℝ) (f := homogExt0 f) (x := x)
  rw [show (homogExt0 f ∘ R) = homogExt0 f ∘ R.toContinuousLinearEquiv from rfl, h]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ R

theorem sphDirichlet_comp_sphereMap (R : E d ≃ₗᵢ[ℝ] E d) (f : sphere (0 : E d) 1 → ℝ) :
    sphDirichlet (f ∘ sphereMap R) = sphDirichlet f := by
  unfold sphDirichlet
  simp_rw [norm_gradient_homogExt0_comp_sphereMap]
  exact integral_comp_sphereMap R fun ω ↦ ‖∇ (homogExt0 f) (ω : E d)‖ ^ 2

theorem sphL2Sq_comp_sphereMap (R : E d ≃ₗᵢ[ℝ] E d) (f : sphere (0 : E d) 1 → ℝ) :
    sphL2Sq (f ∘ sphereMap R) = sphL2Sq f :=
  integral_comp_sphereMap R fun ω ↦ f ω ^ 2

/-- **Isometry invariance of the Rayleigh quotient.** -/
theorem sphRayleigh_comp_sphereMap (R : E d ≃ₗᵢ[ℝ] E d) (f : sphere (0 : E d) 1 → ℝ) :
    sphRayleigh (f ∘ sphereMap R) = sphRayleigh f := by
  rw [sphRayleigh, sphRayleigh, sphDirichlet_comp_sphereMap, sphL2Sq_comp_sphereMap]

/-- If `f` is admissible for `Γ`, then `f ∘ R` is admissible for `R⁻¹ Γ`. -/
theorem IsSphAdmissible.comp_sphereMap {Γ : Set (sphere (0 : E d) 1)}
    {f : sphere (0 : E d) 1 → ℝ} (hf : IsSphAdmissible Γ f) (R : E d ≃ₗᵢ[ℝ] E d) :
    IsSphAdmissible (sphereMap R ⁻¹' Γ) (f ∘ sphereMap R) where
  lipschitz := by
    obtain ⟨K, hK⟩ := hf.lipschitz
    exact ⟨K, by simpa using hK.comp (isometry_sphereMap R).lipschitzWith⟩
  eq_zero ω hω := hf.eq_zero _ hω
  sphL2Sq_pos := by rw [sphL2Sq_comp_sphereMap]; exact hf.sphL2Sq_pos

/-- **Isometry invariance of `λ₁`**: `λ₁(R⁻¹ Γ) = λ₁(Γ)`. -/
theorem sphEigenvalue_preimage_sphereMap (R : E d ≃ₗᵢ[ℝ] E d) (Γ : Set (sphere (0 : E d) 1)) :
    sphEigenvalue (sphereMap R ⁻¹' Γ) = sphEigenvalue Γ := by
  unfold sphEigenvalue
  congr 1
  ext r
  simp only [mem_image, mem_ofPred_eq]
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨f ∘ sphereMap R.symm, ?_, ?_⟩
    · have h := hf.comp_sphereMap R.symm
      have hpre : sphereMap R.symm ⁻¹' (sphereMap R ⁻¹' Γ) = Γ := by
        ext ω; simp [sphereMap_sphereMap_symm]
      rwa [hpre] at h
    · rw [sphRayleigh_comp_sphereMap]
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f ∘ sphereMap R, hf.comp_sphereMap R, sphRayleigh_comp_sphereMap R f⟩

/-! ### Positivity of the Rayleigh quotient -/

/-- If `∇f̂ = 0` at `σ`-a.e. point of the sphere, then `∇f̂ = 0` Lebesgue-a.e. (polar
coordinates and `∇f̂(tω) = t⁻¹ ∇f̂(ω)`). -/
private theorem ae_gradient_homogExt0_eq_zero (hd : 1 ≤ d) {f : sphere (0 : E d) 1 → ℝ}
    (h : ∀ᵐ ω : sphere (0 : E d) 1 ∂(volume : Measure (E d)).toSphere,
      ∇ (homogExt0 f) (ω : E d) = 0) :
    ∀ᵐ x ∂(volume : Measure (E d)), ∇ (homogExt0 f) x = 0 := by
  have := nontrivial_E hd
  have hm : Measurable fun x : E d ↦ ‖∇ (homogExt0 f) x‖ₑ := (measurable_gradient _).enorm
  have hzero : ∫⁻ x, ‖∇ (homogExt0 f) x‖ₑ ∂(volume : Measure (E d)) = 0 := by
    rw [lintegral_add_eq_lintegral_Ioi_lintegral_toSphere hm 0]
    refine (setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_).trans lintegral_zero
    have ht : 0 < t := ht
    have hin : ∫⁻ ω : sphere (0 : E d) 1, ‖∇ (homogExt0 f) (0 + t • (ω : E d))‖ₑ
        ∂(volume : Measure (E d)).toSphere = 0 := by
      refine (lintegral_eq_zero_iff (f := fun ω : sphere (0 : E d) 1 ↦
        ‖∇ (homogExt0 f) (0 + t • (ω : E d))‖ₑ) (hm.comp (show Measurable
          fun ω : sphere (0 : E d) 1 ↦ 0 + t • (ω : E d) by fun_prop))).2 ?_
      filter_upwards [h] with ω hω
      simp [gradient_homogExt0_smul f ht, hω]
    rw [hin, mul_zero]
  have := (lintegral_eq_zero_iff hm).1 hzero
  filter_upwards [this] with x hx
  simpa using hx

/-- **Positivity of the Rayleigh quotient.** Let `d ≥ 2`. If `f` is
admissible for `Γ ⊆ 𝕊` and `Γ ≠ 𝕊`, then `R(f) > 0`. -/
theorem IsSphAdmissible.sphRayleigh_pos (hd : 2 ≤ d) {Γ : Set (sphere (0 : E d) 1)}
    {f : sphere (0 : E d) 1 → ℝ} (hf : IsSphAdmissible Γ f) (hΓ : Γ ≠ univ) :
    0 < sphRayleigh f := by
  obtain ⟨K, hK⟩ := hf.lipschitz
  refine div_pos ?_ hf.sphL2Sq_pos
  have hnn : 0 ≤ sphDirichlet f := integral_nonneg fun _ ↦ sq_nonneg _
  refine lt_of_le_of_ne hnn fun h0 ↦ ?_
  -- `∇f̂ = 0` on the sphere, `σ`-a.e.
  have hint : Integrable (fun ω : sphere (0 : E d) 1 ↦ ‖∇ (homogExt0 f) (ω : E d)‖ ^ 2)
      (volume : Measure (E d)).toSphere :=
    Integrable.of_bound
      (((measurable_gradient _).norm.pow_const 2).comp measurable_subtype_coe).aestronglyMeasurable
      ((4 * K : ℝ) ^ 2) (ae_of_all _ fun ω ↦ by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_homogExt0_le hK ω) 2)
  have hsph := (integral_eq_zero_iff_of_nonneg (fun _ ↦ sq_nonneg _) hint).1 h0.symm
  have hsph' : ∀ᵐ ω : sphere (0 : E d) 1 ∂(volume : Measure (E d)).toSphere,
      ∇ (homogExt0 f) (ω : E d) = 0 := by
    filter_upwards [hsph] with ω hω
    simpa using hω
  have hae := ae_gradient_homogExt0_eq_zero (by omega) hsph'
  -- `f̂` is constant on the connected set `E d \ {0}`
  set U : Set (E d) := {0}ᶜ
  have hU : IsOpen U := isOpen_compl_singleton
  have hUc : IsPreconnected U := by
    refine (isConnected_compl_singleton_of_one_lt_rank ?_ 0).isPreconnected
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast hd
  have hloc := locallyLipschitzOn_homogExt0 hK
  have hW := (memH1Loc_gradient_of_locallyLipschitzOn hU hloc).1
  have hW0 : HasWeakGradient U (homogExt0 f) 0 := by
    refine ⟨hW.1, locallyIntegrableOn_zero, fun φ hφ hφc hφU v ↦ ?_⟩
    rw [hW.2.2 φ hφ hφc hφU v]
    congr 1
    refine integral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hae] with x hx
    simp [hx]
  obtain ⟨c, hc⟩ := exists_ae_eq_const_of_hasWeakGradient_zero hU hUc hW0
  have heq : EqOn (homogExt0 f) (fun _ ↦ c) U :=
    Measure.eqOn_open_of_ae_eq hc hU hloc.continuousOn continuousOn_const
  have hfc : ∀ ω : sphere (0 : E d) 1, f ω = c := fun ω ↦ by
    have hω0 : (ω : E d) ≠ 0 := norm_ne_zero_iff.mp (by rw [norm_eq_of_mem_sphere ω]; norm_num)
    rw [← homogExt0_coe f ω]
    exact heq hω0
  obtain ⟨ω₀, hω₀⟩ := (ne_univ_iff_exists_notMem Γ).1 hΓ
  have hc0 : c = 0 := by rw [← hfc ω₀]; exact hf.eq_zero ω₀ hω₀
  have := hf.sphL2Sq_pos
  simp [sphL2Sq, hfc, hc0] at this

end

end EllipticBernoulli
