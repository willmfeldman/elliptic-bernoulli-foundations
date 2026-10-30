/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.TwoPhase
import EllipticBernoulli.Sphere.Measure
import EllipticBernoulli.Sphere.Radial
import EllipticBernoulli.Sobolev.Lipschitz
import EllipticBernoulli.TwoPhase.Weiss
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.Integral

/-!
# The Weiss functional of a two-plane function

For a unit vector `e` and `a > 0`, `b ≥ 0`, let `v = twoPlane a b e 0`, that is
`v(x) = a (x·e)⁺ - b (x·e)⁻`.

* `volume_setOf_twoPlane_eq_zero`: for `a, b > 0`, the zero set `{v = 0}` is the hyperplane
  `e^⊥`, which is Lebesgue-null.
* `weissW_twoPlane`: `W(v, 0, 1) = |B₁|/2`.

## Proof

Off the null hyperplane `e^⊥`, `|∇v|² = a² 1_{x·e > 0} + b² 1_{x·e < 0}` and
`1_{v > 0} = 1_{x·e > 0}`. The reflection `x ↦ -x` shows that each half-ball has measure
`|B₁|/2`, and that `∫_𝕊 ((ω·e)⁺)² = ∫_𝕊 ((ω·e)⁻)² = ½ ∫_𝕊 (ω·e)²`. Rotating `e` to each vector of
an orthonormal basis (by a reflection, `integral_comp_sphereMap`) and summing gives
`d ∫_𝕊 (ω·e)² = σ(𝕊) = d |B₁|`. Hence
`W = (a² + 1) |B₁|/2 + b² |B₁|/2 - (a² + b²) |B₁|/2 = |B₁|/2`.
For general homogeneous `v`, the energy identity gives `W(v, 0, 1) = |{v > 0} ∩ B₁|`; only the
two-plane case is used, and the direct computation above is shorter.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient NNReal

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-! ### Pointwise facts -/

private theorem twoPlane_of_pos (a b : ℝ) (e : E d) {x : E d} (hx : 0 < inner ℝ x e) :
    twoPlane a b e 0 x = a * inner ℝ x e := by
  simp only [twoPlane, add_zero, max_eq_left hx.le, max_eq_right (neg_nonpos.2 hx.le), mul_zero,
    sub_zero]

private theorem twoPlane_of_neg (a b : ℝ) (e : E d) {x : E d} (hx : inner ℝ x e < 0) :
    twoPlane a b e 0 x = b * inner ℝ x e := by
  simp only [twoPlane, add_zero, max_eq_right hx.le, max_eq_left (neg_nonneg.2 hx.le), mul_zero,
    zero_sub]
  ring

private theorem twoPlane_sq (a b : ℝ) (e : E d) (x : E d) :
    twoPlane a b e 0 x ^ 2 =
      a ^ 2 * max (inner ℝ x e) 0 ^ 2 + b ^ 2 * max (-inner ℝ x e) 0 ^ 2 := by
  rcases le_total (inner ℝ x e) 0 with h | h
  · simp only [twoPlane, add_zero, max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
  · simp only [twoPlane, add_zero, max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring

/-- The hyperplane `e^⊥` is Lebesgue-null for `e ≠ 0`. -/
theorem volume_setOf_inner_eq_zero {e : E d} (he : e ≠ 0) :
    volume {x : E d | inner ℝ x e = 0} = 0 := by
  have hset : {x : E d | inner ℝ x e = 0} =
      (LinearMap.ker (innerSL ℝ e : E d →L[ℝ] ℝ).toLinearMap : Set (E d)) := by
    ext x; simp [real_inner_comm]
  rw [hset]
  refine Measure.addHaar_submodule _ _ fun htop ↦ he ?_
  have hmem : e ∈ LinearMap.ker (innerSL ℝ e : E d →L[ℝ] ℝ).toLinearMap := by
    rw [htop]; exact Submodule.mem_top
  simpa using hmem

/-- For `a, b > 0` and a unit vector `e`, the zero set of `twoPlane a b e 0` is Lebesgue-null. -/
theorem volume_setOf_twoPlane_eq_zero {e : E d} (he : ‖e‖ = 1) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) : volume {x | twoPlane a b e 0 x = 0} = 0 := by
  refine measure_mono_null (fun x hx ↦ ?_) (volume_setOf_inner_eq_zero
    (norm_ne_zero_iff.1 (by rw [he]; exact one_ne_zero)))
  simp only [mem_ofPred_eq] at hx ⊢
  rcases lt_trichotomy (inner ℝ x e) 0 with h | h | h
  · rw [twoPlane_of_neg a b e h] at hx
    exact absurd hx (mul_neg_of_pos_of_neg hb h).ne
  · exact h
  · rw [twoPlane_of_pos a b e h] at hx
    exact absurd hx (mul_pos ha h).ne'

/-! ### Half-balls and half-spheres -/

/-- A half-ball has half the measure of the ball. -/
private theorem measureReal_ball_inter_pos {e : E d} (he : e ≠ 0) :
    volume.real (ball (0 : E d) 1 ∩ {x | 0 < inner ℝ x e}) =
      volume.real (ball (0 : E d) 1) / 2 := by
  set B := ball (0 : E d) 1
  set P := {x : E d | 0 < inner ℝ x e}
  set N := {x : E d | inner ℝ x e < 0}
  have hcont : Continuous fun x : E d ↦ inner ℝ x e := continuous_id.inner continuous_const
  have hPm : MeasurableSet P := measurableSet_lt measurable_const hcont.measurable
  have hNm : MeasurableSet N := measurableSet_lt hcont.measurable measurable_const
  -- the reflection `x ↦ -x` exchanges the two halves
  have hneg : volume (B ∩ N) = volume (B ∩ P) := by
    have hpre : (LinearIsometryEquiv.neg ℝ (E := E d)) ⁻¹' (B ∩ P) = B ∩ N := by
      ext x
      simp [B, P, N, inner_neg_left]
    rw [← hpre, (LinearIsometryEquiv.neg ℝ).measurePreserving.measure_preimage
      (measurableSet_ball.inter hPm).nullMeasurableSet]
  -- the two halves fill the ball up to a null set
  have hZ := volume_setOf_inner_eq_zero he
  have hsplit : volume B = volume (B ∩ P) + volume (B ∩ N) := by
    have h1 : volume B = volume (B \ {x | inner ℝ x e = 0}) :=
      (measure_sdiff_null hZ).symm
    have h2 : B \ {x | inner ℝ x e = 0} = (B ∩ P) ∪ (B ∩ N) := by
      ext x
      simp only [Set.mem_sdiff, mem_ofPred_eq, mem_union, mem_inter_iff, P, N]
      constructor
      · rintro ⟨hx, hx0⟩
        rcases lt_or_gt_of_ne hx0 with h | h
        · exact Or.inr ⟨hx, h⟩
        · exact Or.inl ⟨hx, h⟩
      · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
        · exact ⟨hx, h.ne'⟩
        · exact ⟨hx, h.ne⟩
    rw [h1, h2, measure_union _ (measurableSet_ball.inter hNm)]
    refine disjoint_left.2 fun x hx hx' ↦ ?_
    have h1 : 0 < inner ℝ x e := hx.2
    have h2 : inner ℝ x e < 0 := hx'.2
    linarith
  rw [hneg] at hsplit
  simp only [Measure.real, hsplit]
  rw [ENNReal.toReal_add (measure_ne_top_of_subset inter_subset_left measure_ball_lt_top.ne)
    (measure_ne_top_of_subset inter_subset_left measure_ball_lt_top.ne)]
  ring
  where
  measure_ne_top_of_subset {s t : Set (E d)} (h : s ⊆ t) (ht : volume t ≠ ⊤) :
      volume s ≠ ⊤ := ((measure_mono h).trans_lt ht.lt_top).ne

private theorem integrable_toSphere_of_continuous {g : E d → ℝ} (hg : Continuous g) :
    Integrable (fun ω : sphere (0 : E d) 1 ↦ g ω) (volume : Measure (E d)).toSphere := by
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : E d) 1).exists_bound_of_continuousOn hg.continuousOn
  exact Integrable.of_bound (hg.comp continuous_subtype_val).aestronglyMeasurable C
    (ae_of_all _ fun ω ↦ hC ω ω.2)

/-- `d ∫_𝕊 (ω·e)² dσ = σ(𝕊)` for a unit vector `e`: rotate `e` to each vector of an
orthonormal basis and sum. -/
private theorem natCast_mul_integral_inner_sq {e : E d} (he : ‖e‖ = 1) :
    (d : ℝ) * ∫ ω : sphere (0 : E d) 1, inner ℝ (ω : E d) e ^ 2 ∂(volume : Measure (E d)).toSphere =
      (volume : Measure (E d)).toSphere.real univ := by
  set σ := (volume : Measure (E d)).toSphere
  set b := EuclideanSpace.basisFun (Fin d) ℝ
  have hint : ∀ w : E d,
      Integrable (fun ω : sphere (0 : E d) 1 ↦ inner ℝ (ω : E d) w ^ 2) σ := fun w ↦
    integrable_toSphere_of_continuous (g := fun x ↦ inner ℝ x w ^ 2)
      ((continuous_id.inner continuous_const).pow 2)
  have hrot : ∀ i, ∫ ω, inner ℝ (ω : E d) (b i) ^ 2 ∂σ = ∫ ω, inner ℝ (ω : E d) e ^ 2 ∂σ := by
    intro i
    set R := Submodule.reflection (ℝ ∙ (b i - e))ᗮ
    have hR : R (b i) = e := Submodule.reflection_sub (by rw [b.orthonormal.1 i, he])
    have h := integral_comp_sphereMap R (fun ω ↦ inner ℝ (ω : E d) e ^ 2)
    simp only [coe_sphereMap] at h
    rw [← h]
    refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
    simp only
    rw [← hR, LinearIsometryEquiv.inner_map_map]
  have hsum : ∀ ω : sphere (0 : E d) 1, ∑ i, inner ℝ (ω : E d) (b i) ^ 2 = 1 := by
    intro ω
    have h := b.sum_inner_mul_inner (ω : E d) ω
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere ω, one_pow] at h
    refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) h
    rw [sq, real_inner_comm (b i)]
  calc (d : ℝ) * ∫ ω, inner ℝ (ω : E d) e ^ 2 ∂σ
      = ∑ i : Fin d, ∫ ω, inner ℝ (ω : E d) (b i) ^ 2 ∂σ := by
        simp only [hrot, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ∫ ω, ∑ i, inner ℝ (ω : E d) (b i) ^ 2 ∂σ :=
        (integral_finsetSum _ fun i _ ↦ hint _).symm
    _ = ∫ _ω, (1 : ℝ) ∂σ := integral_congr_ae (ae_of_all _ hsum)
    _ = σ.real univ := by simp

/-- `∫_𝕊 ((ω·e)⁺)² dσ = ∫_𝕊 ((ω·e)⁻)² dσ = σ(𝕊) / (2d)` for a unit vector `e`. -/
private theorem integral_max_inner_sq {e : E d} (he : ‖e‖ = 1) :
    (∫ ω : sphere (0 : E d) 1, max (inner ℝ (ω : E d) e) 0 ^ 2
        ∂(volume : Measure (E d)).toSphere) =
      (volume : Measure (E d)).toSphere.real univ / (2 * d) ∧
    (∫ ω : sphere (0 : E d) 1, max (-inner ℝ (ω : E d) e) 0 ^ 2
        ∂(volume : Measure (E d)).toSphere) =
      (volume : Measure (E d)).toSphere.real univ / (2 * d) := by
  set σ := (volume : Measure (E d)).toSphere
  have hd : (d : ℝ) ≠ 0 := by
    rintro h
    have hd0 : d = 0 := by exact_mod_cast h
    subst hd0
    have : e = 0 := Subsingleton.elim _ _
    rw [this, norm_zero] at he
    exact zero_ne_one he
  have hc : Continuous fun x : E d ↦ inner ℝ x e := continuous_id.inner continuous_const
  have hiP := integrable_toSphere_of_continuous (g := fun x ↦ max (inner ℝ x e) 0 ^ 2)
    ((hc.max continuous_const).pow 2)
  have hiN := integrable_toSphere_of_continuous (g := fun x ↦ max (-inner ℝ x e) 0 ^ 2)
    ((hc.neg.max continuous_const).pow 2)
  -- the reflection `ω ↦ -ω` exchanges the two halves
  have hPN : ∫ ω, max (inner ℝ (ω : E d) e) 0 ^ 2 ∂σ =
      ∫ ω, max (-inner ℝ (ω : E d) e) 0 ^ 2 ∂σ := by
    have h := integral_comp_sphereMap (LinearIsometryEquiv.neg ℝ (E := E d))
      (fun ω ↦ max (inner ℝ (ω : E d) e) 0 ^ 2)
    simp only [coe_sphereMap, LinearIsometryEquiv.coe_neg, inner_neg_left] at h
    exact h.symm
  have hadd : (∫ ω, max (inner ℝ (ω : E d) e) 0 ^ 2 ∂σ) +
      ∫ ω, max (-inner ℝ (ω : E d) e) 0 ^ 2 ∂σ = ∫ ω, inner ℝ (ω : E d) e ^ 2 ∂σ := by
    rw [← integral_add hiP hiN]
    refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
    rcases le_total (inner ℝ (ω : E d) e) 0 with h | h
    · simp only [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
    · simp only [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
  have htot := natCast_mul_integral_inner_sq he
  rw [← hadd, ← hPN] at htot
  rw [← hPN]
  refine ⟨?_, ?_⟩ <;> field_simp <;> linarith

/-- `σ(𝕊) = d |B₁|`. -/
private theorem toSphere_real_univ :
    (volume : Measure (E d)).toSphere.real univ = d * volume.real (ball (0 : E d) 1) := by
  rw [Measure.real, Measure.toSphere_apply_univ, finrank_euclideanSpace_fin, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, Measure.real]

/-! ### The Weiss functional -/

/-- **The Weiss value of a two-plane function.** For a
unit vector `e`, `a > 0` and `b ≥ 0`, `W(twoPlane a b e 0, 0, 1) = |B₁|/2`. -/
theorem weissW_twoPlane {e : E d} (he : ‖e‖ = 1) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    weissW (twoPlane a b e 0) 0 1 = volume.real (ball (0 : E d) 1) / 2 := by
  have he0 : e ≠ 0 := norm_ne_zero_iff.1 (by rw [he]; exact one_ne_zero)
  set v := twoPlane a b e 0 with hvdef
  set B := ball (0 : E d) 1
  set σ := (volume : Measure (E d)).toSphere
  set H := volume.real B / 2
  set P := {x : E d | 0 < inner ℝ x e}
  set N := {x : E d | inner ℝ x e < 0}
  have hc : Continuous fun x : E d ↦ inner ℝ x e := continuous_id.inner continuous_const
  have hPm : MeasurableSet P := measurableSet_lt measurable_const hc.measurable
  have hNm : MeasurableSet N := measurableSet_lt hc.measurable measurable_const
  have hv := twoPlane_lipschitzWith a b e 0
  rw [weissW_eq hv, one_pow, div_one, one_pow, div_one]
  -- the gradient off the hyperplane
  have hgrad : ∀ (c : ℝ) (x : E d), v =ᶠ[𝓝 x] (fun y ↦ c * inner ℝ y e) → ‖∇ v x‖ ^ 2 = c ^ 2 := by
    intro c x hloc
    have hloc' : v =ᶠ[𝓝 x] (c • innerSL ℝ e : E d →L[ℝ] ℝ) := by
      filter_upwards [hloc] with y hy
      rw [hy]; simp [real_inner_comm]
    rw [norm_gradient_eq_norm_fderiv, hloc'.fderiv_eq, ContinuousLinearMap.fderiv, norm_smul,
      innerSL_apply_norm, he, mul_one, Real.norm_eq_abs, sq_abs]
  have hdP : ∀ x ∈ P, weissDensity v x = a ^ 2 + 1 := by
    intro x hx
    have hloc : v =ᶠ[𝓝 x] (fun y ↦ a * inner ℝ y e) := by
      filter_upwards [(isOpen_lt continuous_const hc).mem_nhds hx] with y hy
      exact twoPlane_of_pos a b e hy
    have hvx : 0 < v x := by rw [hvdef, twoPlane_of_pos a b e hx]; exact mul_pos ha hx
    rw [weissDensity, hgrad a x hloc, indicator_of_mem (show x ∈ {y | 0 < v y} from hvx),
      Pi.one_apply]
  have hdN : ∀ x ∈ N, weissDensity v x = b ^ 2 := by
    intro x hx
    have hloc : v =ᶠ[𝓝 x] (fun y ↦ b * inner ℝ y e) := by
      filter_upwards [(isOpen_lt hc continuous_const).mem_nhds hx] with y hy
      exact twoPlane_of_neg a b e hy
    have hvx : ¬ 0 < v x := by
      rw [hvdef, twoPlane_of_neg a b e hx]; exact not_lt.2 (mul_nonpos_of_nonneg_of_nonpos hb hx.le)
    rw [weissDensity, hgrad b x hloc, indicator_of_notMem (show x ∉ {y | 0 < v y} from hvx),
      add_zero]
  -- the energy term
  have hHP : volume.real (B ∩ P) = H := measureReal_ball_inter_pos he0
  have hHN : volume.real (B ∩ N) = H := by
    have h := measureReal_ball_inter_pos (neg_ne_zero.2 he0)
    have hset : {x : E d | 0 < inner ℝ x (-e)} = N := by
      ext x; simp [N, inner_neg_right]
    rwa [hset] at h
  have hB : volume (B) ≠ ⊤ := measure_ball_lt_top.ne
  have hJ : ∫ x in B, weissDensity v x = (a ^ 2 + 1) * H + b ^ 2 * H := by
    have hae : ∀ᵐ x ∂volume.restrict B, weissDensity v x =
        (a ^ 2 + 1) * P.indicator 1 x + b ^ 2 * N.indicator 1 x := by
      refine ae_restrict_of_ae ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_setOf_inner_eq_zero he0)]
        with x hx
      rcases lt_or_gt_of_ne (show inner ℝ x e ≠ 0 from hx) with h | h
      · rw [hdN x h, indicator_of_notMem (show x ∉ P from fun h' ↦ absurd h' (not_lt.2 h.le)),
          indicator_of_mem (show x ∈ N from h)]
        simp
      · rw [hdP x h, indicator_of_mem (show x ∈ P from h),
          indicator_of_notMem (show x ∉ N from fun h' ↦ absurd h' (not_lt.2 h.le))]
        simp
    have hiP : IntegrableOn (P.indicator (1 : E d → ℝ)) B :=
      (integrableOn_const hB).indicator hPm
    have hiN : IntegrableOn (N.indicator (1 : E d → ℝ)) B :=
      (integrableOn_const hB).indicator hNm
    rw [integral_congr_ae hae, integral_add (hiP.const_mul _) (hiN.const_mul _),
      integral_const_mul, integral_const_mul, setIntegral_indicator hPm,
      setIntegral_indicator hNm]
    simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one, hHP, hHN]
  -- the sphere term
  have hM : radialM v 0 1 = (a ^ 2 + b ^ 2) * (σ.real univ / (2 * d)) := by
    obtain ⟨hP, hN⟩ := integral_max_inner_sq he
    have hc' : Continuous fun x : E d ↦ max (inner ℝ x e) 0 ^ 2 := (hc.max continuous_const).pow 2
    have hc'' : Continuous fun x : E d ↦ max (-inner ℝ x e) 0 ^ 2 :=
      (hc.neg.max continuous_const).pow 2
    simp only [radialM, zero_add, one_smul, hvdef, twoPlane_sq]
    rw [integral_add ((integrable_toSphere_of_continuous hc').const_mul _)
      ((integrable_toSphere_of_continuous hc'').const_mul _), integral_const_mul,
      integral_const_mul, hP, hN]
    ring
  rw [hJ, hM, toSphere_real_univ]
  have hd : (d : ℝ) ≠ 0 := by
    rintro h
    have hd0 : d = 0 := by exact_mod_cast h
    subst hd0
    exact he0 (Subsingleton.elim _ _)
  simp only [H]
  field_simp
  ring

end EllipticBernoulli
