/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sphere.Colatitude
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import EllipticBernoulli.Sobolev.Lipschitz
import EllipticBernoulli.Common.Calculus

/-!
# Polarization on the sphere

Fix a unit vector `e`. The reflection in the hyperplane `e^⊥` is
`ρ_e(x) = x - 2 ⟨x, e⟩ e` (`polarReflection e`), and the two-point rearrangement (polarization)
of `f : 𝕊 → ℝ` is

`f^e(ω) = max (f ω) (f (ρ_e ω))` if `⟨ω, e⟩ ≥ 0`, and `min (f ω) (f (ρ_e ω))` if `⟨ω, e⟩ < 0`

(`polarize e f`). On the equator `⟨ω, e⟩ = 0` we have `ρ_e ω = ω`, so `f^e(ω) = f(ω)`; the
equator need not be treated as a separate case. For polarization (two-point rearrangement) in
general, see Brock–Solynin.

This file proves:

* (a) `lipschitzWith_polarize`: `f^e` has the Lipschitz constant of `f`, via the cross-side
  identity `norm_sub_polarReflection_sq`: `|x - ρ y|² = |x - y|² + 4 ⟨x, e⟩ ⟨y, e⟩`;
* (b) `map_polarize`, `lintegral_comp_polarize`: `f^e` and `f` have the same distribution
  under the sphere measure `σ`;
* (c) `sphDirichlet_polarize`: for `d ≥ 2` and Lipschitz `f`, the Dirichlet energy is preserved;
* (d) `abs_polarize_sub_polarize_le`: polarization is `1`-Lipschitz in the sup norm;
* (e) `integral_sq_sub_polarize`: the exact formula
  `∫ (f - h)² = ∫ (f^e - h)² + 2 ∫_{⟨ω,e⟩>0} (f(ρω) - f(ω))⁺ (h(ω) - h(ρω))`, and
  `integral_sq_polarize_sub_le`: if `h` is ordered (`IsPolarOrdered e h`:
  `h(ρω) ≤ h(ω)` whenever `⟨ω, e⟩ ≥ 0`), then `∫ (f^e - h)² ≤ ∫ (f - h)²`.

Every integral is split as `∫ = ∫_{⟨ω,e⟩>0} (G + G ∘ ρ) + ∫_{⟨ω,e⟩=0} G`
(`lintegral_eq_lintegral_pos_add`, `integral_eq_setIntegral_pos_add`), since `ρ` preserves `σ`
and maps `{⟨ω,e⟩<0}` onto `{⟨ω,e⟩>0}`. For (c), the equator is `σ`-null when `d ≥ 2`
(`toSphere_inner_eq_zero`), and at a point where `u`, `v`, `max u v` and `min u v` are all
differentiable, the derivatives of `max u v` and `min u v` are those of `u` and `v` in some order
(`fderiv_max_min`): at a tie `u(x) = v(x)`, the nonnegative function `max u v - u` has a local
minimum at `x`.

## References

* F. Brock, A. Yu. Solynin, *An approach to symmetrization via polarization*, Trans. Amer. Math.
  Soc. 352 (2000).
-/

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped Gradient NNReal Real ENNReal

namespace EllipticBernoulli

variable {d : ℕ}

@[expose] public noncomputable section

/-- The reflection `ρ_e` in the hyperplane `e^⊥`. For a unit vector `e`,
`ρ_e x = x - 2 ⟨x, e⟩ e` (`polarReflection_apply`). -/
def polarReflection (e : E d) : E d ≃ₗᵢ[ℝ] E d :=
  (ℝ ∙ e)ᗮ.reflection

/-- The polarization (two-point rearrangement) of `f : 𝕊 → ℝ` with respect to `e`:
`max (f ω) (f (ρ_e ω))` on the closed half `⟨ω, e⟩ ≥ 0` and `min (f ω) (f (ρ_e ω))` on the open
half `⟨ω, e⟩ < 0`. -/
def polarize (e : E d) (f : sphere (0 : E d) 1 → ℝ) (ω : sphere (0 : E d) 1) : ℝ :=
  if 0 ≤ inner ℝ (ω : E d) e then max (f ω) (f (sphereMap (polarReflection e) ω))
  else min (f ω) (f (sphereMap (polarReflection e) ω))

/-- `h` is ordered with respect to `e`: `h(ρ_e ω) ≤ h(ω)` whenever
`⟨ω, e⟩ ≥ 0`. -/
def IsPolarOrdered (e : E d) (h : sphere (0 : E d) 1 → ℝ) : Prop :=
  ∀ ω : sphere (0 : E d) 1, 0 ≤ inner ℝ (ω : E d) e →
    h (sphereMap (polarReflection e) ω) ≤ h ω

end

public section

/-! ### The reflection -/

theorem polarReflection_apply {e : E d} (he : ‖e‖ = 1) (x : E d) :
    polarReflection e x = x - (2 * inner ℝ x e) • e := by
  rw [polarReflection, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, he]
  simp only [RCLike.ofReal_real_eq_id, id, one_pow, div_one, real_inner_comm e x]
  module

@[simp]
theorem polarReflection_polarReflection (e : E d) (x : E d) :
    polarReflection e (polarReflection e x) = x :=
  Submodule.reflection_reflection _ x

@[simp]
theorem polarReflection_symm (e : E d) : (polarReflection e).symm = polarReflection e :=
  Submodule.reflection_symm

theorem inner_polarReflection {e : E d} (he : ‖e‖ = 1) (x : E d) :
    inner ℝ (polarReflection e x) e = -inner ℝ x e := by
  rw [polarReflection_apply he, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq, he]
  simp only [RCLike.conj_to_real]
  ring

@[simp]
theorem sphereMap_polarReflection_sphereMap_polarReflection (e : E d)
    (ω : sphere (0 : E d) 1) :
    sphereMap (polarReflection e) (sphereMap (polarReflection e) ω) = ω := by
  ext1; simp

/-- **Cross-side identity**: `|x - ρ y|² = |x - y|² + 4 ⟨x, e⟩ ⟨y, e⟩`. -/
theorem norm_sub_polarReflection_sq {e : E d} (he : ‖e‖ = 1) (x y : E d) :
    ‖x - polarReflection e y‖ ^ 2 = ‖x - y‖ ^ 2 + 4 * inner ℝ x e * inner ℝ y e := by
  rw [polarReflection_apply he, show x - (y - (2 * inner ℝ y e) • e) =
    (x - y) + (2 * inner ℝ y e) • e by abel, norm_add_sq_real, inner_smul_right, norm_smul,
    he, inner_sub_left, Real.norm_eq_abs, mul_one, sq_abs]
  ring

/-- If `x` and `y` lie on opposite closed sides of `e^⊥`, then `|x - ρ y| ≤ |x - y|`. -/
theorem norm_sub_polarReflection_le {e : E d} (he : ‖e‖ = 1) {x y : E d}
    (hx : 0 ≤ inner ℝ x e) (hy : inner ℝ y e ≤ 0) :
    ‖x - polarReflection e y‖ ≤ ‖x - y‖ := by
  have h := norm_sub_polarReflection_sq he x y
  have : 4 * inner ℝ x e * inner ℝ y e ≤ 0 := by
    have := mul_nonpos_of_nonneg_of_nonpos hx hy
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by linarith)

/-! ### Elementary properties of `polarize` -/

section Basic

variable {e : E d} {f g h : sphere (0 : E d) 1 → ℝ}

theorem polarize_of_nonneg {ω : sphere (0 : E d) 1} (hω : 0 ≤ inner ℝ (ω : E d) e) :
    polarize e f ω = max (f ω) (f (sphereMap (polarReflection e) ω)) := by
  simp [polarize, hω]

theorem polarize_of_neg {ω : sphere (0 : E d) 1} (hω : inner ℝ (ω : E d) e < 0) :
    polarize e f ω = min (f ω) (f (sphereMap (polarReflection e) ω)) := by
  simp [polarize, not_le.2 hω]

theorem sphereMap_polarReflection_of_inner_eq_zero {ω : sphere (0 : E d) 1}
    (hω : inner ℝ (ω : E d) e = 0) : sphereMap (polarReflection e) ω = ω := by
  ext1
  rw [coe_sphereMap, polarReflection]
  exact Submodule.reflection_mem_subspace_eq_self
    ((Submodule.mem_orthogonal_singleton_iff_inner_right (𝕜 := ℝ)).2
      (by rw [real_inner_comm]; exact hω))

/-- On the equator, polarization does nothing. -/
theorem polarize_of_inner_eq_zero {ω : sphere (0 : E d) 1}
    (hω : inner ℝ (ω : E d) e = 0) : polarize e f ω = f ω := by
  rw [polarize_of_nonneg hω.ge, sphereMap_polarReflection_of_inner_eq_zero hω, max_self]

/-- The value of `f^e` at the reflected point `ρ ω`, for `⟨ω, e⟩ > 0`. -/
theorem polarize_sphereMap_of_pos (he : ‖e‖ = 1) {ω : sphere (0 : E d) 1}
    (hω : 0 < inner ℝ (ω : E d) e) :
    polarize e f (sphereMap (polarReflection e) ω) =
      min (f ω) (f (sphereMap (polarReflection e) ω)) := by
  rw [polarize_of_neg (by rw [coe_sphereMap, inner_polarReflection he]; linarith),
    sphereMap_polarReflection_sphereMap_polarReflection, min_comm]

theorem measurable_sphereMap_polarReflection (e : E d) :
    Measurable (sphereMap (polarReflection e)) :=
  (continuous_sphereMap _).measurable

theorem measurable_polarize (e : E d) (hf : Measurable f) : Measurable (polarize e f) := by
  refine Measurable.ite ?_ (hf.max (hf.comp (measurable_sphereMap_polarReflection e)))
    (hf.min (hf.comp (measurable_sphereMap_polarReflection e)))
  exact measurableSet_le measurable_const
    ((continuous_subtype_val.inner continuous_const).measurable)

/-- `|max a b - min a' b'| ≤ δ` when all four cross differences are at most `δ`. -/
private theorem abs_max_sub_min_le {a b a' b' δ : ℝ} (h₁ : |a - a'| ≤ δ) (h₂ : |b - b'| ≤ δ)
    (h₃ : |a - b'| ≤ δ) (h₄ : |b - a'| ≤ δ) : |max a b - min a' b'| ≤ δ := by
  rw [abs_le] at *
  rcases le_total a b with hab | hab <;> rcases le_total a' b' with hab' | hab' <;>
    simp only [max_eq_left, max_eq_right, min_eq_left, min_eq_right, hab, hab'] <;>
    constructor <;> linarith

/-- The cross-side estimate behind (a): if `⟨ω, e⟩ ≥ 0 > ⟨ω', e⟩`, then
`|f^e(ω) - f^e(ω')| ≤ L |ω - ω'|`. -/
private theorem abs_polarize_sub_le_of_cross (he : ‖e‖ = 1) {L : ℝ≥0}
    (hf : LipschitzWith L f) {ω ω' : sphere (0 : E d) 1} (hω : 0 ≤ inner ℝ (ω : E d) e)
    (hω' : inner ℝ (ω' : E d) e < 0) :
    |polarize e f ω - polarize e f ω'| ≤ L * dist ω ω' := by
  set ρ := sphereMap (polarReflection e)
  rw [polarize_of_nonneg hω, polarize_of_neg hω']
  have hcross : dist ω (ρ ω') ≤ dist ω ω' := by
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    exact norm_sub_polarReflection_le he hω hω'.le
  have hρ : ∀ a b, dist (ρ a) (ρ b) = dist a b := (isometry_sphereMap _).dist_eq
  have hL : ∀ a b, |f a - f b| ≤ L * dist a b := fun a b ↦ by
    rw [← Real.dist_eq]; exact hf.dist_le_mul a b
  have hL0 : (0 : ℝ) ≤ L := L.2
  refine abs_max_sub_min_le (hL _ _) ((hL _ _).trans_eq (by rw [hρ])) ?_ ?_
  · exact (hL _ _).trans (mul_le_mul_of_nonneg_left hcross hL0)
  · refine (hL _ _).trans (mul_le_mul_of_nonneg_left ?_ hL0)
    calc dist (ρ ω) ω' = dist (ρ (ρ ω)) (ρ ω') := (hρ _ _).symm
      _ = dist ω (ρ ω') := by simp only [ρ, sphereMap_polarReflection_sphereMap_polarReflection]
      _ ≤ dist ω ω' := hcross

/-- **(a) Polarization preserves the Lipschitz constant.** -/
theorem lipschitzWith_polarize (he : ‖e‖ = 1) {L : ℝ≥0} (hf : LipschitzWith L f) :
    LipschitzWith L (polarize e f) := by
  set ρ := sphereMap (polarReflection e)
  refine LipschitzWith.of_dist_le_mul fun ω ω' ↦ ?_
  rw [Real.dist_eq]
  have hρ : ∀ a b, dist (ρ a) (ρ b) = dist a b := (isometry_sphereMap _).dist_eq
  have hL : ∀ a b, |f a - f b| ≤ L * dist a b := fun a b ↦ by
    rw [← Real.dist_eq]; exact hf.dist_le_mul a b
  have h₁ := hL ω ω'
  have h₂ : |f (ρ ω) - f (ρ ω')| ≤ L * dist ω ω' := by rw [← hρ]; exact hL _ _
  rcases le_or_gt 0 (inner ℝ (ω : E d) e) with hω | hω <;>
    rcases le_or_gt 0 (inner ℝ (ω' : E d) e) with hω' | hω'
  · rw [polarize_of_nonneg hω, polarize_of_nonneg hω']
    exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le h₁ h₂)
  · exact abs_polarize_sub_le_of_cross he hf hω hω'
  · rw [abs_sub_comm, dist_comm]
    exact abs_polarize_sub_le_of_cross he hf hω' hω
  · rw [polarize_of_neg hω, polarize_of_neg hω']
    exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le h₁ h₂)

/-- **(d) Polarization is `1`-Lipschitz in the sup norm.** -/
theorem abs_polarize_sub_polarize_le (e : E d) {δ : ℝ} (hfg : ∀ ω, |f ω - g ω| ≤ δ)
    (ω : sphere (0 : E d) 1) : |polarize e f ω - polarize e g ω| ≤ δ := by
  by_cases hω : 0 ≤ inner ℝ (ω : E d) e
  · rw [polarize_of_nonneg hω, polarize_of_nonneg hω]
    exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le (hfg _) (hfg _))
  · rw [polarize_of_neg (not_le.1 hω), polarize_of_neg (not_le.1 hω)]
    exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (hfg _) (hfg _))

theorem continuous_polarize (hf : Continuous f) : Continuous (polarize e f) := by
  have hρ := continuous_sphereMap (polarReflection e)
  refine Continuous.if_le ?_ ?_ continuous_const
    (continuous_subtype_val.inner continuous_const) fun ω hω ↦ ?_
  · exact hf.max (hf.comp hρ)
  · exact hf.min (hf.comp hρ)
  · rw [sphereMap_polarReflection_of_inner_eq_zero hω.symm, max_self, min_self]

theorem polarize_nonneg (hf : ∀ ω, 0 ≤ f ω) (ω : sphere (0 : E d) 1) : 0 ≤ polarize e f ω := by
  unfold EllipticBernoulli.polarize
  split_ifs
  · exact le_max_of_le_left (hf ω)
  · exact le_min (hf ω) (hf _)

theorem polarize_le {C : ℝ} (hf : ∀ ω, f ω ≤ C) (ω : sphere (0 : E d) 1) :
    polarize e f ω ≤ C := by
  unfold EllipticBernoulli.polarize
  split_ifs
  · exact max_le (hf ω) (hf _)
  · exact min_le_of_left_le (hf ω)

end Basic

/-! ### Splitting integrals over the two half-spheres -/

section Split

variable {e : E d}

theorem measurableSet_inner_pos (e : E d) :
    MeasurableSet {ω : sphere (0 : E d) 1 | 0 < inner ℝ (ω : E d) e} :=
  measurableSet_lt measurable_const (continuous_subtype_val.inner continuous_const).measurable

theorem measurableSet_inner_neg (e : E d) :
    MeasurableSet {ω : sphere (0 : E d) 1 | inner ℝ (ω : E d) e < 0} :=
  measurableSet_lt (continuous_subtype_val.inner continuous_const).measurable measurable_const

theorem measurableSet_inner_eq_zero (e : E d) :
    MeasurableSet {ω : sphere (0 : E d) 1 | inner ℝ (ω : E d) e = 0} :=
  measurableSet_eq_fun (continuous_subtype_val.inner continuous_const).measurable
    measurable_const

theorem preimage_sphereMap_polarReflection_inner_neg (he : ‖e‖ = 1) :
    sphereMap (polarReflection e) ⁻¹' {ω : sphere (0 : E d) 1 | inner ℝ (ω : E d) e < 0} =
      {ω : sphere (0 : E d) 1 | 0 < inner ℝ (ω : E d) e} := by
  ext ω
  change inner ℝ (polarReflection e ω) e < 0 ↔ 0 < inner ℝ (ω : E d) e
  rw [inner_polarReflection he, neg_lt_zero]

/-- `ρ` as a measurable involution of the sphere. -/
private noncomputable def polarSphereEquiv (e : E d) :
    sphere (0 : E d) 1 ≃ᵐ sphere (0 : E d) 1 where
  toFun := sphereMap (polarReflection e)
  invFun := sphereMap (polarReflection e)
  left_inv := sphereMap_polarReflection_sphereMap_polarReflection e
  right_inv := sphereMap_polarReflection_sphereMap_polarReflection e
  measurable_toFun := measurable_sphereMap_polarReflection e
  measurable_invFun := measurable_sphereMap_polarReflection e

theorem measurableEmbedding_sphereMap_polarReflection (e : E d) :
    MeasurableEmbedding (sphereMap (polarReflection e)) :=
  (polarSphereEquiv e).measurableEmbedding

/-- The sphere is the disjoint union of the open upper half, the equator and the open lower
half. -/
private theorem univ_eq_union (e : E d) :
    (univ : Set (sphere (0 : E d) 1)) = ({ω : sphere (0 : E d) 1 | 0 < inner ℝ (ω : E d) e} ∪
      {ω : sphere (0 : E d) 1 | inner ℝ (ω : E d) e = 0}) ∪
        {ω : sphere (0 : E d) 1 | inner ℝ (ω : E d) e < 0} := by
  ext ω
  simp only [mem_univ, mem_union, mem_ofPred_eq, true_iff]
  rcases lt_trichotomy 0 (inner ℝ (ω : E d) e) with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h.symm)
  · exact Or.inr h

private theorem disjoint_pos_zero (e : E d) :
    Disjoint {ω : sphere (0 : E d) 1 | 0 < inner ℝ (ω : E d) e}
      {ω : sphere (0 : E d) 1 | inner ℝ (ω : E d) e = 0} :=
  Set.disjoint_left.2 fun _ h₁ h₂ ↦ (ne_of_gt h₁) (by exact h₂)

private theorem disjoint_union_neg (e : E d) :
    Disjoint ({ω : sphere (0 : E d) 1 | 0 < inner ℝ (ω : E d) e} ∪
      {ω : sphere (0 : E d) 1 | inner ℝ (ω : E d) e = 0})
        {ω : sphere (0 : E d) 1 | inner ℝ (ω : E d) e < 0} := by
  refine Set.disjoint_left.2 fun ω h₁ h₂ ↦ ?_
  simp only [mem_union, mem_ofPred_eq] at h₁ h₂
  rcases h₁ with h | h <;> linarith

/-- **Splitting a lower integral** over the two half-spheres:
`∫⁻ G = ∫⁻_{⟨ω,e⟩>0} (G(ω) + G(ρω)) + ∫⁻_{⟨ω,e⟩=0} G`. -/
theorem lintegral_eq_lintegral_pos_add (he : ‖e‖ = 1) {G : sphere (0 : E d) 1 → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ ω, G ω ∂(volume : Measure (E d)).toSphere =
      ∫⁻ ω in {ω | 0 < inner ℝ (ω : E d) e},
          (G ω + G (sphereMap (polarReflection e) ω)) ∂(volume : Measure (E d)).toSphere +
        ∫⁻ ω in {ω | inner ℝ (ω : E d) e = 0}, G ω ∂(volume : Measure (E d)).toSphere := by
  set σ := (volume : Measure (E d)).toSphere
  set ρ := sphereMap (polarReflection e)
  have hmp := measurePreserving_sphereMap (polarReflection e)
  have hemb : MeasurableEmbedding ρ := measurableEmbedding_sphereMap_polarReflection e
  have hneg : ∫⁻ ω in {ω | inner ℝ (ω : E d) e < 0}, G ω ∂σ =
      ∫⁻ ω in {ω | 0 < inner ℝ (ω : E d) e}, G (ρ ω) ∂σ := by
    rw [← preimage_sphereMap_polarReflection_inner_neg he]
    exact (hmp.setLIntegral_comp_preimage_emb hemb G _).symm
  rw [← setLIntegral_univ, univ_eq_union e,
    lintegral_union (measurableSet_inner_neg e) (disjoint_union_neg e),
    lintegral_union (measurableSet_inner_eq_zero e) (disjoint_pos_zero e), hneg,
    lintegral_add_left' hG.aemeasurable]
  ring

/-- **Splitting an integral** over the two half-spheres:
`∫ G = ∫_{⟨ω,e⟩>0} (G(ω) + G(ρω)) + ∫_{⟨ω,e⟩=0} G`. -/
theorem integral_eq_setIntegral_pos_add (he : ‖e‖ = 1) {G : sphere (0 : E d) 1 → ℝ}
    (hG : Integrable G (volume : Measure (E d)).toSphere) :
    ∫ ω, G ω ∂(volume : Measure (E d)).toSphere =
      ∫ ω in {ω | 0 < inner ℝ (ω : E d) e},
          (G ω + G (sphereMap (polarReflection e) ω)) ∂(volume : Measure (E d)).toSphere +
        ∫ ω in {ω | inner ℝ (ω : E d) e = 0}, G ω ∂(volume : Measure (E d)).toSphere := by
  set σ := (volume : Measure (E d)).toSphere
  set ρ := sphereMap (polarReflection e)
  have hmp := measurePreserving_sphereMap (polarReflection e)
  have hemb : MeasurableEmbedding ρ :=
    measurableEmbedding_sphereMap_polarReflection e
  have hneg : ∫ ω in {ω | inner ℝ (ω : E d) e < 0}, G ω ∂σ =
      ∫ ω in {ω | 0 < inner ℝ (ω : E d) e}, G (ρ ω) ∂σ := by
    rw [← preimage_sphereMap_polarReflection_inner_neg he]
    exact (hmp.setIntegral_preimage_emb hemb G _).symm
  have hGρ : Integrable (fun ω ↦ G (ρ ω)) σ := hmp.integrable_comp_emb hemb |>.2 hG
  rw [← setIntegral_univ, univ_eq_union e,
    setIntegral_union (disjoint_union_neg e) (measurableSet_inner_neg e) hG.integrableOn
      hG.integrableOn,
    setIntegral_union (disjoint_pos_zero e) (measurableSet_inner_eq_zero e) hG.integrableOn
      hG.integrableOn, hneg, integral_add hG.integrableOn hGρ.integrableOn]
  ring

end Split

/-! ### (b) Equimeasurability -/

section Equimeasurable

variable {e : E d} {f : sphere (0 : E d) 1 → ℝ}

private theorem add_comp_max_min {M : Type*} [AddCommMonoid M] (Ψ : ℝ → M) (a b : ℝ) :
    Ψ (max a b) + Ψ (min a b) = Ψ a + Ψ b := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h, add_comm]
  · rw [max_eq_left h, min_eq_right h]

/-- **(b) Equimeasurability**, integral form: `∫⁻ Ψ ∘ f^e = ∫⁻ Ψ ∘ f` for measurable `Ψ ≥ 0`. -/
theorem lintegral_comp_polarize (he : ‖e‖ = 1) (hf : Measurable f) {Ψ : ℝ → ℝ≥0∞}
    (hΨ : Measurable Ψ) :
    ∫⁻ ω, Ψ (polarize e f ω) ∂(volume : Measure (E d)).toSphere =
      ∫⁻ ω, Ψ (f ω) ∂(volume : Measure (E d)).toSphere := by
  rw [lintegral_eq_lintegral_pos_add (G := fun ω ↦ Ψ (polarize e f ω)) he
      (hΨ.comp (measurable_polarize e hf)),
    lintegral_eq_lintegral_pos_add (G := fun ω ↦ Ψ (f ω)) he (hΨ.comp hf)]
  congr 1
  · refine setLIntegral_congr_fun (measurableSet_inner_pos e) fun ω hω ↦ ?_
    rw [polarize_of_nonneg (le_of_lt hω), polarize_sphereMap_of_pos he hω, add_comp_max_min]
  · refine setLIntegral_congr_fun (measurableSet_inner_eq_zero e) fun ω hω ↦ ?_
    rw [polarize_of_inner_eq_zero hω]

/-- **(b) Equimeasurability**: `f^e` and `f` have the same
distribution under `σ`. -/
theorem map_polarize (he : ‖e‖ = 1) (hf : Measurable f) :
    ((volume : Measure (E d)).toSphere).map (polarize e f) =
      ((volume : Measure (E d)).toSphere).map f := by
  ext s hs
  rw [Measure.map_apply (measurable_polarize e hf) hs, Measure.map_apply hf hs,
    ← lintegral_indicator_one ((measurable_polarize e hf) hs), ← lintegral_indicator_one (hf hs)]
  exact lintegral_comp_polarize he hf (measurable_one.indicator hs)

/-- `σ{f^e > t} = σ{f > t}`. -/
theorem toSphere_lt_polarize (he : ‖e‖ = 1) (hf : Measurable f) (t : ℝ) :
    (volume : Measure (E d)).toSphere {ω | t < polarize e f ω} =
      (volume : Measure (E d)).toSphere {ω | t < f ω} := by
  have h := congrArg (fun μ : Measure ℝ ↦ μ (Ioi t)) (map_polarize he hf)
  rwa [Measure.map_apply (measurable_polarize e hf) measurableSet_Ioi,
    Measure.map_apply hf measurableSet_Ioi] at h

end Equimeasurable

/-! ### (e) The `L²` distance to an ordered function -/

section Distance

variable {e : E d} {f h : sphere (0 : E d) 1 → ℝ}

private theorem integrable_of_bound {G : sphere (0 : E d) 1 → ℝ} (hG : Measurable G) {C : ℝ}
    (hC : ∀ ω, |G ω| ≤ C) : Integrable G (volume : Measure (E d)).toSphere :=
  Integrable.of_bound hG.aestronglyMeasurable C (ae_of_all _ fun ω ↦ by
    rw [Real.norm_eq_abs]; exact hC ω)

/-- The two-point identity behind (e): for `x, y, A, B`,
`(x - A)² + (y - B)² = (max x y - A)² + (min x y - B)² + 2 (y - x)⁺ (A - B)`. -/
private theorem two_point_identity (x y A B : ℝ) :
    (x - A) ^ 2 + (y - B) ^ 2 =
      (max x y - A) ^ 2 + (min x y - B) ^ 2 + 2 * (max (y - x) 0 * (A - B)) := by
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right hxy, min_eq_left hxy, max_eq_left (by linarith)]; ring
  · rw [max_eq_left hxy, min_eq_right hxy, max_eq_right (by linarith)]; ring

private theorem abs_polarize_le {C : ℝ} (hfC : ∀ ω, |f ω| ≤ C) (ω : sphere (0 : E d) 1) :
    |polarize e f ω| ≤ C := by
  have h1 : ∀ ω, f ω ≤ C := fun ω ↦ (abs_le.1 (hfC ω)).2
  have h2 : ∀ ω, -C ≤ f ω := fun ω ↦ (abs_le.1 (hfC ω)).1
  refine abs_le.2 ⟨?_, polarize_le h1 ω⟩
  unfold EllipticBernoulli.polarize
  split_ifs
  · exact le_max_of_le_left (h2 ω)
  · exact le_min (h2 ω) (h2 _)

/-- **(e) The distance formula.** For bounded measurable `f` and `h`,
`∫ (f - h)² = ∫ (f^e - h)² + 2 ∫_{⟨ω,e⟩>0} (f(ρω) - f(ω))⁺ (h(ω) - h(ρω))`. -/
theorem integral_sq_sub_polarize (he : ‖e‖ = 1) (hf : Measurable f) (hh : Measurable h)
    {C : ℝ} (hfC : ∀ ω, |f ω| ≤ C) (hhC : ∀ ω, |h ω| ≤ C) :
    ∫ ω, (f ω - h ω) ^ 2 ∂(volume : Measure (E d)).toSphere =
      ∫ ω, (polarize e f ω - h ω) ^ 2 ∂(volume : Measure (E d)).toSphere +
        2 * ∫ ω in {ω | 0 < inner ℝ (ω : E d) e},
          max (f (sphereMap (polarReflection e) ω) - f ω) 0 *
            (h ω - h (sphereMap (polarReflection e) ω)) ∂(volume : Measure (E d)).toSphere := by
  set σ := (volume : Measure (E d)).toSphere
  set ρ := sphereMap (polarReflection e)
  have hρm := measurable_sphereMap_polarReflection e
  have hfe := measurable_polarize e hf
  have hsq : ∀ {u : sphere (0 : E d) 1 → ℝ}, Measurable u → (∀ ω, |u ω| ≤ C) →
      Integrable (fun ω ↦ (u ω - h ω) ^ 2) σ := fun {u} hu huC ↦
    integrable_of_bound ((hu.sub hh).pow_const 2) (C := (C + C) ^ 2) fun ω ↦ by
      rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
      have : |u ω - h ω| ≤ C + C := (abs_sub _ _).trans (add_le_add (huC ω) (hhC ω))
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
  set D : sphere (0 : E d) 1 → ℝ := fun ω ↦ max (f (ρ ω) - f ω) 0 * (h ω - h (ρ ω))
  have hD : Integrable D σ := by
    refine integrable_of_bound (((hf.comp hρm).sub hf).max measurable_const |>.mul
      (hh.sub (hh.comp hρm))) (C := (C + C) * (C + C)) fun ω ↦ ?_
    rw [abs_mul]
    refine mul_le_mul ?_ ((abs_sub _ _).trans (add_le_add (hhC _) (hhC _))) (abs_nonneg _)
      (by linarith [(abs_nonneg _).trans (hhC ω)])
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_trans (le_abs_self _) ((abs_sub _ _).trans (add_le_add (hfC _) (hfC _))))
      (by linarith [(abs_nonneg _).trans (hfC ω)])
  have hI := hsq hf hfC
  have hJ := hsq hfe (abs_polarize_le hfC)
  have hJρ : Integrable (fun ω ↦ (polarize e f (ρ ω) - h (ρ ω)) ^ 2) σ :=
    (measurePreserving_sphereMap (polarReflection e)).integrable_comp_emb
      (measurableEmbedding_sphereMap_polarReflection e) |>.2 hJ
  rw [integral_eq_setIntegral_pos_add he hI, integral_eq_setIntegral_pos_add he hJ]
  have hpos : ∫ ω in {ω | 0 < inner ℝ (ω : E d) e},
      ((f ω - h ω) ^ 2 + (f (ρ ω) - h (ρ ω)) ^ 2) ∂σ =
      ∫ ω in {ω | 0 < inner ℝ (ω : E d) e},
        ((polarize e f ω - h ω) ^ 2 + (polarize e f (ρ ω) - h (ρ ω)) ^ 2 + 2 * D ω) ∂σ := by
    refine setIntegral_congr_fun (measurableSet_inner_pos e) fun ω hω ↦ ?_
    simp only [D]
    rw [polarize_of_nonneg (le_of_lt hω), polarize_sphereMap_of_pos he hω]
    exact two_point_identity _ _ _ _
  have hzero : ∫ ω in {ω | inner ℝ (ω : E d) e = 0}, (f ω - h ω) ^ 2 ∂σ =
      ∫ ω in {ω | inner ℝ (ω : E d) e = 0}, (polarize e f ω - h ω) ^ 2 ∂σ := by
    refine setIntegral_congr_fun (measurableSet_inner_eq_zero e) fun ω hω ↦ ?_
    rw [polarize_of_inner_eq_zero hω]
  have hsum : IntegrableOn (fun ω ↦ (polarize e f ω - h ω) ^ 2 +
      (polarize e f (ρ ω) - h (ρ ω)) ^ 2) {ω | 0 < inner ℝ (ω : E d) e} σ :=
    (hJ.add hJρ).integrableOn
  rw [hpos, hzero, integral_add hsum (hD.const_mul 2).integrableOn, integral_const_mul]
  ring

/-- **(e) Polarization moves `f` closer to an ordered function**: if `h(ρω) ≤ h(ω)` whenever
`⟨ω, e⟩ ≥ 0`, then `∫ (f^e - h)² ≤ ∫ (f - h)²`. -/
theorem integral_sq_polarize_sub_le (he : ‖e‖ = 1) (hf : Measurable f) (hh : Measurable h)
    {C : ℝ} (hfC : ∀ ω, |f ω| ≤ C) (hhC : ∀ ω, |h ω| ≤ C) (hord : IsPolarOrdered e h) :
    ∫ ω, (polarize e f ω - h ω) ^ 2 ∂(volume : Measure (E d)).toSphere ≤
      ∫ ω, (f ω - h ω) ^ 2 ∂(volume : Measure (E d)).toSphere := by
  rw [integral_sq_sub_polarize he hf hh hfC hhC, le_add_iff_nonneg_right]
  refine mul_nonneg zero_le_two (setIntegral_nonneg (measurableSet_inner_pos e) fun ω hω ↦ ?_)
  exact mul_nonneg (le_max_right _ _) (sub_nonneg.2 (hord ω (le_of_lt hω)))

end Distance

/-! ### (c) The Dirichlet energy -/

section Calculus

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- If `g ≤ k` everywhere, `g x = k x`, and both are differentiable at `x`, then their
derivatives at `x` agree (`k - g ≥ 0` has a local minimum at `x`). -/
theorem fderiv_eq_of_le_of_eq {g k : F → ℝ} {x : F} (hg : DifferentiableAt ℝ g x)
    (hk : DifferentiableAt ℝ k x) (hle : ∀ y, g y ≤ k y) (heq : g x = k x) :
    fderiv ℝ g x = fderiv ℝ k x := by
  have hmin : IsLocalMin (fun y ↦ k y - g y) x :=
    Filter.Eventually.of_forall fun y ↦ by simp only [heq, sub_self, sub_nonneg, hle y]
  have h0 := hmin.hasFDerivAt_eq_zero (hk.hasFDerivAt.sub hg.hasFDerivAt)
  rw [sub_eq_zero] at h0
  exact h0.symm

/-- **Derivatives of `max` and `min`.** At a point where `u`, `v`, `max u v` and `min u v` are
all differentiable, the derivatives of `max u v` and `min u v` are those of `u` and `v`, in some
order. -/
theorem fderiv_max_min {u v : F → ℝ} {x : F} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (hmax : DifferentiableAt ℝ (fun y ↦ max (u y) (v y)) x)
    (hmin : DifferentiableAt ℝ (fun y ↦ min (u y) (v y)) x) :
    (fderiv ℝ (fun y ↦ max (u y) (v y)) x = fderiv ℝ u x ∧
        fderiv ℝ (fun y ↦ min (u y) (v y)) x = fderiv ℝ v x) ∨
      (fderiv ℝ (fun y ↦ max (u y) (v y)) x = fderiv ℝ v x ∧
        fderiv ℝ (fun y ↦ min (u y) (v y)) x = fderiv ℝ u x) := by
  rcases lt_trichotomy (u x) (v x) with h | h | h
  · right
    have hev := hu.continuousAt.eventually_lt hv.continuousAt h
    constructor
    · exact Filter.EventuallyEq.fderiv_eq (hev.mono fun y hy ↦ max_eq_right hy.le)
    · exact Filter.EventuallyEq.fderiv_eq (hev.mono fun y hy ↦ min_eq_left hy.le)
  · left
    constructor
    · exact (fderiv_eq_of_le_of_eq hu hmax (fun y ↦ le_max_left _ _)
        (by simp [h])).symm
    · exact fderiv_eq_of_le_of_eq hmin hv (fun y ↦ min_le_right _ _) (by simp [h])
  · left
    have hev := hv.continuousAt.eventually_lt hu.continuousAt h
    constructor
    · exact Filter.EventuallyEq.fderiv_eq (hev.mono fun y hy ↦ max_eq_left hy.le)
    · exact Filter.EventuallyEq.fderiv_eq (hev.mono fun y hy ↦ min_eq_right hy.le)

theorem norm_sq_fderiv_max_add_min {u v : F → ℝ} {x : F} (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) (hmax : DifferentiableAt ℝ (fun y ↦ max (u y) (v y)) x)
    (hmin : DifferentiableAt ℝ (fun y ↦ min (u y) (v y)) x) :
    ‖fderiv ℝ (fun y ↦ max (u y) (v y)) x‖ ^ 2 + ‖fderiv ℝ (fun y ↦ min (u y) (v y)) x‖ ^ 2 =
      ‖fderiv ℝ u x‖ ^ 2 + ‖fderiv ℝ v x‖ ^ 2 := by
  rcases fderiv_max_min hu hv hmax hmin with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [h₁, h₂]
  · rw [h₁, h₂, add_comm]

end Calculus

section Dirichlet

variable {e : E d} {f : sphere (0 : E d) 1 → ℝ}

/-- For `d ≥ 2`, the equator `{⟨ω, e⟩ = 0}` is `σ`-null. -/
theorem toSphere_inner_eq_zero (hd : 2 ≤ d) (he : ‖e‖ = 1) :
    (volume : Measure (E d)).toSphere {ω : sphere (0 : E d) 1 | inner ℝ (ω : E d) e = 0} = 0 := by
  have h := ae_colatitude_notMem hd he (Z := {π / 2}) (measure_singleton _)
  refine measure_mono_null (fun ω (hω : inner ℝ (ω : E d) e = 0) ↦ ?_)
    (measure_eq_zero_iff_ae_notMem.2 h)
  change colatitude e ω ∈ ({π / 2} : Set ℝ)
  rw [colatitude_eq_arccos he, real_inner_comm, hω, Real.arccos_zero, mem_singleton_iff]

/-- Near a point of the open upper half, `(f^e)^ = max (f̂, (f ∘ ρ)^)` and
`(f^e ∘ ρ)^ = min (f̂, (f ∘ ρ)^)`. -/
private theorem homogExt0_polarize_eventuallyEq (he : ‖e‖ = 1) {ω : sphere (0 : E d) 1}
    (hω : 0 < inner ℝ (ω : E d) e) :
    homogExt0 (polarize e f) =ᶠ[𝓝 (ω : E d)] (fun y ↦ max (homogExt0 f y)
        (homogExt0 (f ∘ sphereMap (polarReflection e)) y)) ∧
      homogExt0 (polarize e f ∘ sphereMap (polarReflection e)) =ᶠ[𝓝 (ω : E d)]
        (fun y ↦ min (homogExt0 f y) (homogExt0 (f ∘ sphereMap (polarReflection e)) y)) := by
  have hopen : IsOpen {y : E d | 0 < inner ℝ y e} :=
    isOpen_lt continuous_const (continuous_id.inner continuous_const)
  have hmem : {y : E d | 0 < inner ℝ y e} ∈ 𝓝 (ω : E d) := hopen.mem_nhds hω
  have key : ∀ y : E d, 0 < inner ℝ y e → ∃ hy : y ≠ 0,
      0 < inner ℝ ((⟨‖y‖⁻¹ • y, by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy)]⟩ : sphere (0 : E d) 1) : E d) e := by
    intro y hy
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    refine ⟨hy0, ?_⟩
    simp only [inner_smul_left, RCLike.conj_to_real]
    exact mul_pos (inv_pos.2 (norm_pos_iff.2 hy0)) hy
  constructor
  · filter_upwards [hmem] with y hy
    obtain ⟨hy0, hpos⟩ := key y hy
    simp only [homogExt0_of_ne_zero _ hy0, Function.comp_apply]
    exact polarize_of_nonneg hpos.le
  · filter_upwards [hmem] with y hy
    obtain ⟨hy0, hpos⟩ := key y hy
    simp only [homogExt0_of_ne_zero _ hy0, Function.comp_apply]
    exact polarize_sphereMap_of_pos he hpos

private theorem integrable_norm_sq_gradient_homogExt0 {g : sphere (0 : E d) 1 → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) :
    Integrable (fun ω : sphere (0 : E d) 1 ↦ ‖∇ (homogExt0 g) (ω : E d)‖ ^ 2)
      (volume : Measure (E d)).toSphere :=
  Integrable.of_bound
    (((measurable_gradient _).norm.pow_const 2).comp measurable_subtype_coe).aestronglyMeasurable
    ((4 * K : ℝ) ^ 2) (ae_of_all _ fun ω ↦ by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_gradient_homogExt0_le hg ω) 2)

/-- **(c) Polarization preserves the Dirichlet energy.** For
`d ≥ 2` and Lipschitz `f`, `∫_𝕊 |∇(f^e)^|² dσ = ∫_𝕊 |∇f̂|² dσ`. -/
theorem sphDirichlet_polarize (hd : 2 ≤ d) (he : ‖e‖ = 1) {L : ℝ≥0} (hf : LipschitzWith L f) :
    sphDirichlet (polarize e f) = sphDirichlet f := by
  set σ := (volume : Measure (E d)).toSphere
  set R := polarReflection e
  set ρ := sphereMap R
  have hd1 : 1 ≤ d := by omega
  have hfe := lipschitzWith_polarize he hf
  have hρL : ∀ {g : sphere (0 : E d) 1 → ℝ}, LipschitzWith L g → LipschitzWith L (g ∘ ρ) :=
    fun hg ↦ by simpa using hg.comp (isometry_sphereMap R).lipschitzWith
  have hD : ∀ g : sphere (0 : E d) 1 → ℝ, ∀ ω : sphere (0 : E d) 1,
      ‖∇ (homogExt0 g) ((ρ ω : sphere (0 : E d) 1) : E d)‖ =
        ‖∇ (homogExt0 (g ∘ ρ)) (ω : E d)‖ := fun g ω ↦
    (norm_gradient_homogExt0_comp_sphereMap R g ω).symm
  have hzero := toSphere_inner_eq_zero hd he
  unfold sphDirichlet
  rw [integral_eq_setIntegral_pos_add he (integrable_norm_sq_gradient_homogExt0 hfe),
    integral_eq_setIntegral_pos_add he (integrable_norm_sq_gradient_homogExt0 hf),
    setIntegral_measure_zero _ hzero, setIntegral_measure_zero _ hzero]
  congr 1
  refine setIntegral_congr_ae (measurableSet_inner_pos e) ?_
  filter_upwards [ae_differentiableAt_homogExt0 hd1 hf,
    ae_differentiableAt_homogExt0 hd1 (hρL hf), ae_differentiableAt_homogExt0 hd1 hfe,
    ae_differentiableAt_homogExt0 hd1 (hρL hfe)] with ω hu hv h₁ h₂ hω
  obtain ⟨heq₁, heq₂⟩ := homogExt0_polarize_eventuallyEq (f := f) he hω
  rw [hD, hD, norm_gradient_eq_norm_fderiv, norm_gradient_eq_norm_fderiv,
    norm_gradient_eq_norm_fderiv, norm_gradient_eq_norm_fderiv, heq₁.fderiv_eq, heq₂.fderiv_eq]
  exact norm_sq_fderiv_max_add_min hu hv (h₁.congr_of_eventuallyEq heq₁.symm)
    (h₂.congr_of_eventuallyEq heq₂.symm)

end Dirichlet

end

end EllipticBernoulli
