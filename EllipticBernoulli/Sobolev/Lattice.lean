/-
Copyright (c) 2026 William M. Feldman, Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman, Alejandro Soto Franco
-/
module

public import EllipticBernoulli.Sobolev.Mollify
public import EllipticBernoulli.Common.Calculus

/-!
# Chain rule and lattice property of weak gradients

Imports only `Basic/*` and Mathlib.

For `HasWeakGradient U u G` (weak gradient carried as data):

* `HasWeakGradient.integral_eq`: the defining identity as a whole-space integral.
* `HasWeakGradient.add`, `.neg`, `.sub`, `.const_smul`, `.sub_const`, `.mul_smooth`
  (product with a smooth function).
* `HasWeakGradient.comp`: chain rule `∇ f(u) = f'(u) ∇u` for `f ∈ C¹` with bounded derivative
  (Gilbarg–Trudinger Lemma 7.5).
* `HasWeakGradient.posPart`: `∇ u₊ = 1_{u > 0} ∇u` (Gilbarg–Trudinger Lemma 7.6).
* `memH1Loc_posPart`: `v₊ ∈ H¹_loc` with weak gradient `1_{v > 0} G`.
* `HasWeakGradient.max`, `.min`, `MemH1Loc.max`, `.min`:
  `∇ max(u, w) = 1_{u<w} ∇w + 1_{u≥w} ∇u`, and dually for `min`.

The chain rule and the positive part are adapted from `EllipticPdes.Embedding.ChainRule`
(EllipticPDE, A. Soto Franco, Apache-2.0, `github.com/alejandro-soto-franco/EllipticPDE`),
rewritten for weak gradients tested against arbitrary directions `v`.

## Provenance

* Upstream: EllipticPDE, https://github.com/alejandro-soto-franco/EllipticPDE
* Path: `lean/EllipticPdes/Embedding/ChainRule.lean`
* Commit: eaf821d31b200bb6ea235f19eecc50cf0f38c294 (2026-09-22)
* License: Apache-2.0. Upstream `NOTICE`: none.
* Upstream notice: `Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.`;
  upstream authors: Alejandro Soto Franco.
* Extent: the chain rule `HasWeakGradient.comp` (from `hasWeakGradOn_comp`) and
  `HasWeakGradient.posPart`.
* Changes: restated for `HasWeakGradient` (weak gradients tested against arbitrary directions `v`)
  and `E d`; ported to Lean/Mathlib v4.30.0; proofs adapted.
-/

open Set Filter Topology MeasureTheory Metric ContinuousLinearMap
open scoped ContDiff Convolution ENNReal NNReal Gradient

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ} {U : Set (E d)}

/-! ### Integrability helpers -/

section Integrability

/-- Domination for `LocallyIntegrableOn` on a measurable set, with measurability only with
respect to the restricted measure. -/
theorem locallyIntegrableOn_of_le {F F' : Type*} [NormedAddCommGroup F]
    [NormedAddCommGroup F'] {s : Set (E d)} (hs : MeasurableSet s) {f : E d → F}
    {g : E d → F'} (hf : LocallyIntegrableOn f s) (hg : AEStronglyMeasurable g (volume.restrict s))
    (h : ∀ x ∈ s, ‖g x‖ ≤ ‖f x‖) : LocallyIntegrableOn g s := by
  intro x hx
  obtain ⟨t, ht, hint⟩ := hf x hx
  obtain ⟨o, ho, hxo, hot⟩ := mem_nhdsWithin.1 ht
  refine ⟨s ∩ o, inter_mem_nhdsWithin s (ho.mem_nhds hxo), ?_⟩
  refine Integrable.mono (hint.mono_set fun y hy ↦ hot ⟨hy.2, hy.1⟩)
    (hg.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)) ?_
  exact (ae_restrict_iff' (hs.inter ho.measurableSet)).2
    (Eventually.of_forall fun y hy ↦ h y hy.1)

theorem locallyIntegrableOn_inner_apply {s : Set (E d)} {G : E d → E d}
    (hG : LocallyIntegrableOn G s) (v : E d) :
    LocallyIntegrableOn (fun x ↦ inner ℝ (G x) v) s := by
  intro x hx
  obtain ⟨t, ht, hi⟩ := hG x hx
  refine ⟨t, ht, ?_⟩
  have := (innerSL ℝ v).integrable_comp hi
  rw [IntegrableOn]
  simpa [innerSL_apply_apply, real_inner_comm] using this

/-- A function locally integrable on `U`, times a continuous function with compact support in
`U`, is integrable on the whole space. -/
theorem integrable_mul_of_locallyIntegrableOn {u : E d → ℝ} (hu : LocallyIntegrableOn u U)
    {h : E d → ℝ} (hc : Continuous h) (hcs : HasCompactSupport h) (hs : tsupport h ⊆ U) :
    Integrable (fun x ↦ u x * h x) := by
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  have hK : IntegrableOn u (tsupport h) := hu.integrableOn_compact_subset hs hcs
  have hprod : IntegrableOn (fun x ↦ u x * h x) (tsupport h) :=
    Integrable.mul_bdd hK hc.aestronglyMeasurable.restrict (Eventually.of_forall hC)
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right u h).trans (subset_tsupport h))).mp hprod

/-- Product of two bounded factors and an integrable one. -/
theorem integrable_bdd_mul_mul_bdd {a b c : E d → ℝ} (ha : AEStronglyMeasurable a volume)
    {A : ℝ} (hA : ∀ x, ‖a x‖ ≤ A) (hb : Integrable b) (hc : AEStronglyMeasurable c volume)
    {C : ℝ} (hC : ∀ x, ‖c x‖ ≤ C) : Integrable (fun x ↦ a x * b x * c x) := by
  refine Integrable.mono' (hb.norm.const_mul (A * C)) ((ha.mul hb.1).mul hc) ?_
  filter_upwards with x
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA x)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC x)
  rw [norm_mul, norm_mul]
  calc ‖a x‖ * ‖b x‖ * ‖c x‖ ≤ A * ‖b x‖ * C := by
        gcongr
        · exact hA x
        · exact hC x
    _ = A * C * ‖b x‖ := by ring

/-- A Lipschitz function of an integrable function, times a continuous compactly supported
factor, is integrable. -/
theorem integrable_comp_mul_of_lipschitz {w : E d → ℝ} (hw : Integrable w) {f : ℝ → ℝ}
    {M : ℝ≥0} (hf : LipschitzWith M f) {h : E d → ℝ} (hc : Continuous h)
    (hcs : HasCompactSupport h) : Integrable (fun x ↦ f (w x) * h x) := by
  have hm : AEStronglyMeasurable (fun x ↦ f (w x) * h x) volume :=
    (hf.continuous.comp_aestronglyMeasurable hw.1).mul hc.aestronglyMeasurable
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  have hint1 : Integrable (fun x ↦ ‖h x‖ * ‖w x‖) :=
    hw.norm.bdd_mul hc.norm.aestronglyMeasurable (Eventually.of_forall fun x ↦ by
      rw [norm_norm]; exact hC x)
  have hint2 : Integrable (fun x ↦ ‖h x‖) := hc.norm.integrable_of_hasCompactSupport hcs.norm
  refine Integrable.mono' ((hint1.const_mul (M : ℝ)).add (hint2.const_mul |f 0|)) hm ?_
  filter_upwards with x
  have h1 : |f (w x) - f 0| ≤ (M : ℝ) * |w x| := by
    have := hf.dist_le_mul (w x) 0
    simpa [Real.dist_eq] using this
  have h2 : |f (w x)| ≤ (M : ℝ) * |w x| + |f 0| := by
    have : |f (w x)| ≤ |f (w x) - f 0| + |f 0| := by
      have := abs_sub_abs_le_abs_sub (f (w x)) (f 0)
      linarith [abs_nonneg (f 0)]
    linarith
  simp only [Pi.add_apply, norm_mul, Real.norm_eq_abs]
  calc |f (w x)| * |h x| ≤ ((M : ℝ) * |w x| + |f 0|) * |h x| := by gcongr
    _ = (M : ℝ) * (|h x| * |w x|) + |f 0| * |h x| := by ring

/-- `a.e.`-strong measurability of `{c < v}.indicator G`. -/
theorem AEStronglyMeasurable.indicator_lt {F : Type*} [NormedAddCommGroup F] {μ : Measure (E d)}
    {v : E d → ℝ} {G : E d → F} (hv : AEStronglyMeasurable v μ)
    (hG : AEStronglyMeasurable G μ) (c : ℝ) :
    AEStronglyMeasurable ({y | c < v y}.indicator G) μ := by
  refine ⟨{y | c < hv.mk v y}.indicator (hG.mk G),
    (hG.stronglyMeasurable_mk).indicator (measurableSet_lt measurable_const
      hv.stronglyMeasurable_mk.measurable), ?_⟩
  filter_upwards [hv.ae_eq_mk, hG.ae_eq_mk] with y hy1 hy2
  simp only [indicator, mem_ofPred_eq, hy1, hy2]

end Integrability

/-! ### The weak-gradient identity -/

section WeakGradient

variable {u w : E d → ℝ} {G H : E d → E d}

theorem fderiv_apply_eq_zero_of_notMem_tsupport {φ : E d → ℝ} {x : E d} (hx : x ∉ tsupport φ)
    (v : E d) : fderiv ℝ φ x v = 0 := by
  have : fderiv ℝ φ x = 0 := Function.notMem_support.1 fun h ↦ hx (support_fderiv_subset ℝ h)
  rw [this, zero_apply]

/-- The weak-gradient identity as a whole-space integral. -/
theorem _root_.EllipticBernoulli.HasWeakGradient.integral_eq
    (hw : HasWeakGradient U u G) {φ : E d → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (v : E d) :
    ∫ x, u x * fderiv ℝ φ x v = -∫ x, inner ℝ (G x) v * φ x := by
  have h := hw.2.2 φ hφ hφc hφU v
  have e1 : ∫ x in U, u x * fderiv ℝ φ x v = ∫ x, u x * fderiv ℝ φ x v :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [fderiv_apply_eq_zero_of_notMem_tsupport (fun h ↦ hx (hφU h)), mul_zero]
  have e2 : ∫ x in U, inner ℝ (G x) v * φ x = ∫ x, inner ℝ (G x) v * φ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hφU h)), mul_zero]
  rw [← e1, ← e2]
  exact h

/-- Build `HasWeakGradient` from the whole-space identity. -/
theorem _root_.EllipticBernoulli.HasWeakGradient.of_integral_eq (hu : LocallyIntegrableOn u U)
    (hG : LocallyIntegrableOn G U)
    (h : ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ v : E d,
      ∫ x, u x * fderiv ℝ φ x v = -∫ x, inner ℝ (G x) v * φ x) :
    HasWeakGradient U u G := by
  refine ⟨hu, hG, fun φ hφ hφc hφU v ↦ ?_⟩
  have e1 : ∫ x in U, u x * fderiv ℝ φ x v = ∫ x, u x * fderiv ℝ φ x v :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [fderiv_apply_eq_zero_of_notMem_tsupport (fun h ↦ hx (hφU h)), mul_zero]
  have e2 : ∫ x in U, inner ℝ (G x) v * φ x = ∫ x, inner ℝ (G x) v * φ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hφU h)), mul_zero]
  rw [e1, e2]
  exact h φ hφ hφc hφU v

theorem integrable_fderiv_apply_mul {u : E d → ℝ} (hu : LocallyIntegrableOn u U) {φ : E d → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (v : E d) :
    Integrable (fun x ↦ u x * fderiv ℝ φ x v) :=
  integrable_mul_of_locallyIntegrableOn hu
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hφc.fderiv_apply (𝕜 := ℝ) v)
    ((tsupport_fderiv_apply_subset ℝ v).trans hφU)

theorem integrable_inner_mul {G : E d → E d} (hG : LocallyIntegrableOn G U) {φ : E d → ℝ}
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (v : E d) :
    Integrable (fun x ↦ inner ℝ (G x) v * φ x) :=
  integrable_mul_of_locallyIntegrableOn (locallyIntegrableOn_inner_apply hG v) hφ hφc hφU

theorem _root_.EllipticBernoulli.HasWeakGradient.add
    (hu : HasWeakGradient U u G) (hw : HasWeakGradient U w H) :
    HasWeakGradient U (fun x ↦ u x + w x) (fun x ↦ G x + H x) := by
  refine HasWeakGradient.of_integral_eq (hu.1.add hw.1) (hu.2.1.add hw.2.1)
    fun φ hφ hφc hφU v ↦ ?_
  have h1 := hu.integral_eq hφ hφc hφU v
  have h2 := hw.integral_eq hφ hφc hφU v
  have i1 := integrable_fderiv_apply_mul hu.1 hφ hφc hφU v
  have i2 := integrable_fderiv_apply_mul hw.1 hφ hφc hφU v
  have j1 := integrable_inner_mul hu.2.1 hφ.continuous hφc hφU v
  have j2 := integrable_inner_mul hw.2.1 hφ.continuous hφc hφU v
  have eL : ∫ x, (u x + w x) * fderiv ℝ φ x v =
      (∫ x, u x * fderiv ℝ φ x v) + ∫ x, w x * fderiv ℝ φ x v := by
    rw [← integral_add i1 i2]; congr 1; funext x; ring
  have eR : ∫ x, inner ℝ (G x + H x) v * φ x =
      (∫ x, inner ℝ (G x) v * φ x) + ∫ x, inner ℝ (H x) v * φ x := by
    rw [← integral_add j1 j2]; congr 1; funext x; rw [inner_add_left]; ring
  rw [eL, eR, h1, h2]; ring

theorem _root_.EllipticBernoulli.HasWeakGradient.const_smul (hu : HasWeakGradient U u G) (c : ℝ) :
    HasWeakGradient U (fun x ↦ c * u x) (fun x ↦ c • G x) := by
  refine HasWeakGradient.of_integral_eq (hu.1.smul c) (hu.2.1.smul c) fun φ hφ hφc hφU v ↦ ?_
  have h1 := hu.integral_eq hφ hφc hφU v
  have eL : ∫ x, c * u x * fderiv ℝ φ x v = c * ∫ x, u x * fderiv ℝ φ x v := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  have eR : ∫ x, inner ℝ (c • G x) v * φ x = c * ∫ x, inner ℝ (G x) v * φ x := by
    rw [← integral_const_mul]; congr 1; funext x; rw [real_inner_smul_left]; ring
  rw [eL, eR, h1]; ring

theorem _root_.EllipticBernoulli.HasWeakGradient.neg (hu : HasWeakGradient U u G) :
    HasWeakGradient U (fun x ↦ -u x) (fun x ↦ -G x) := by
  have := hu.const_smul (-1)
  simpa using this

theorem _root_.EllipticBernoulli.HasWeakGradient.sub
    (hu : HasWeakGradient U u G) (hw : HasWeakGradient U w H) :
    HasWeakGradient U (fun x ↦ u x - w x) (fun x ↦ G x - H x) := by
  have := hu.add hw.neg
  simpa [sub_eq_add_neg] using this

/-- The integral of a directional derivative of a test function vanishes. -/
theorem integral_fderiv_apply_eq_zero {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (v : E d) : ∫ x, fderiv ℝ φ x v = 0 := by
  have h0 : ∀ x : E d, fderiv ℝ (fun _ ↦ (1 : ℝ)) x = 0 := fun x ↦ by simp
  have hI1 : Integrable (fun x ↦ fderiv ℝ φ x v) :=
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hφc.fderiv_apply (𝕜 := ℝ) v)
  have hI2 : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hφc
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ ↦ (1 : ℝ)) (g := φ) (v := v)
    (by simp only [h0, zero_apply, zero_mul]; exact integrable_zero _ _ _)
    (by simpa using hI1) (by simpa using hI2)
    (fun x _ ↦ differentiableAt_const _) (fun x _ ↦ (hφ.differentiable (by simp)) x)
  simpa [h0] using key

/-- A constant has weak gradient `0`. -/
theorem hasWeakGradient_const (c : ℝ) :
    HasWeakGradient U (fun _ ↦ c) (fun _ ↦ 0) := by
  refine HasWeakGradient.of_integral_eq (locallyIntegrableOn_const c)
    (locallyIntegrableOn_const 0) fun φ hφ hφc _ v ↦ ?_
  simp only [inner_zero_left, zero_mul, integral_zero, neg_zero]
  rw [integral_const_mul, integral_fderiv_apply_eq_zero hφ hφc v, mul_zero]

theorem _root_.EllipticBernoulli.HasWeakGradient.sub_const (hu : HasWeakGradient U u G)
    (c : ℝ) :
    HasWeakGradient U (fun x ↦ u x - c) G := by
  have := hu.sub (hasWeakGradient_const c)
  simpa using this

theorem _root_.EllipticBernoulli.HasWeakGradient.const_sub (hu : HasWeakGradient U u G)
    (c : ℝ) :
    HasWeakGradient U (fun x ↦ c - u x) (fun x ↦ -G x) := by
  have := (hasWeakGradient_const c).sub hu
  simpa using this

/-- Weak gradients are determined up to changing the gradient on a null set. -/
theorem _root_.EllipticBernoulli.HasWeakGradient.congr_ae
    (hu : HasWeakGradient U u G) {H : E d → E d}
    (hGH : ∀ᵐ x ∂(volume.restrict U), G x = H x) : HasWeakGradient U u H := by
  refine ⟨hu.1, hu.2.1.congr hGH, fun φ hφ hφc hφU v ↦ ?_⟩
  rw [hu.2.2 φ hφ hφc hφU v]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hGH] with x hx
  rw [hx]

/-- The function may also be changed on a null set. -/
theorem _root_.EllipticBernoulli.HasWeakGradient.congr_fun_ae
    (hu : HasWeakGradient U u G) {w : E d → ℝ}
    (huw : ∀ᵐ x ∂(volume.restrict U), u x = w x) : HasWeakGradient U w G := by
  refine ⟨hu.1.congr huw, hu.2.1, fun φ hφ hφc hφU v ↦ ?_⟩
  rw [← hu.2.2 φ hφ hφc hφU v]
  refine integral_congr_ae ?_
  filter_upwards [huw] with x hx
  rw [hx]

theorem locallyIntegrableOn_continuous_smul {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hU : IsOpen U) {g : E d → F} (hg : LocallyIntegrableOn g U)
    {f : E d → ℝ} (hf : Continuous f) : LocallyIntegrableOn (fun x ↦ f x • g x) U :=
  (locallyIntegrableOn_iff hU.isLocallyClosed).2 fun _ hK hKc ↦
    (hg.integrableOn_compact_subset hK hKc).continuousOn_smul hf.continuousOn hKc

theorem locallyIntegrableOn_smul_continuous {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hU : IsOpen U) {f : E d → ℝ} (hf : LocallyIntegrableOn f U)
    {g : E d → F} (hg : Continuous g) : LocallyIntegrableOn (fun x ↦ f x • g x) U :=
  (locallyIntegrableOn_iff hU.isLocallyClosed).2 fun _ hK hKc ↦
    (hf.integrableOn_compact_subset hK hKc).smul_continuousOn_of_subset hg.continuousOn
      hKc.measurableSet hKc Subset.rfl


/-- **Product with a smooth function.** -/
theorem _root_.EllipticBernoulli.HasWeakGradient.mul_smooth (hU : IsOpen U)
    (hu : HasWeakGradient U u G)
    {η : E d → ℝ} (hη : ContDiff ℝ ∞ η) :
    HasWeakGradient U (fun x ↦ η x * u x) (fun x ↦ η x • G x + u x • ∇ η x) := by
  have hηc : Continuous η := hη.continuous
  have hηd : Differentiable ℝ η := hη.differentiable (by simp)
  have hdη : Continuous (fun x ↦ fderiv ℝ η x) := hη.continuous_fderiv (by simp)
  have hgrad : ∀ x v, inner ℝ (∇ η x) v = fderiv ℝ η x v := fun _ _ ↦
    inner_gradient_left
  have hgradc : Continuous (∇ η) := continuous_gradient (hη.of_le (by simp))
  refine HasWeakGradient.of_integral_eq ?_ ?_ fun φ hφ hφc hφU v ↦ ?_
  · simpa [smul_eq_mul] using locallyIntegrableOn_continuous_smul hU hu.1 hηc
  · exact (locallyIntegrableOn_continuous_smul hU hu.2.1 hηc).add
      (locallyIntegrableOn_smul_continuous hU hu.1 hgradc)
  have hψ : ContDiff ℝ ∞ (fun x ↦ η x * φ x) := hη.mul hφ
  have hψc : HasCompactSupport (fun x ↦ η x * φ x) := hφc.mul_left
  have hψU : tsupport (fun x ↦ η x * φ x) ⊆ U := (tsupport_mul_subset_right).trans hφU
  have h1 := hu.integral_eq hψ hψc hψU v
  have hfd : ∀ x, fderiv ℝ (fun x ↦ η x * φ x) x v =
      η x * fderiv ℝ φ x v + φ x * fderiv ℝ η x v := by
    intro x
    rw [fderiv_fun_mul (hηd x) ((hφ.differentiable (by simp)) x)]
    simp [smul_eq_mul]
  have i1 : Integrable (fun x ↦ u x * fderiv ℝ (fun x ↦ η x * φ x) x v) :=
    integrable_fderiv_apply_mul hu.1 hψ hψc hψU v
  have i2 : Integrable (fun x ↦ u x * (φ x * fderiv ℝ η x v)) :=
    integrable_mul_of_locallyIntegrableOn hu.1
      (hφ.continuous.mul (hdη.clm_apply continuous_const)) hφc.mul_right
      ((tsupport_mul_subset_left).trans hφU)
  have j1 : Integrable (fun x ↦ inner ℝ (G x) v * (η x * φ x)) :=
    integrable_inner_mul hu.2.1 hψ.continuous hψc hψU v
  have eL : ∫ x, η x * u x * fderiv ℝ φ x v =
      (∫ x, u x * fderiv ℝ (fun x ↦ η x * φ x) x v) - ∫ x, u x * (φ x * fderiv ℝ η x v) := by
    rw [← integral_sub i1 i2]; congr 1; funext x; rw [hfd]; ring
  have eR : ∫ x, inner ℝ (η x • G x + u x • ∇ η x) v * φ x =
      (∫ x, inner ℝ (G x) v * (η x * φ x)) + ∫ x, u x * (φ x * fderiv ℝ η x v) := by
    rw [← integral_add j1 i2]; congr 1; funext x
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hgrad]; ring
  rw [eL, eR, h1]; ring

end WeakGradient

/-! ### The chain rule -/

section ChainRule

variable {u : E d → ℝ} {G : E d → E d}

/-- **Chain rule for weak gradients** (Gilbarg–Trudinger Lemma 7.5). For `f ∈ C¹` with bounded
derivative, `f ∘ u` has weak gradient `f'(u) G`. Adapted from EllipticPDE's `hasWeakGradOn_comp`:
mollify `u` inside a compact neighbourhood of the support of the test function, apply the
classical chain rule and integration by parts, and pass to the limit. -/
theorem _root_.EllipticBernoulli.HasWeakGradient.comp (hU : IsOpen U)
    (hw : HasWeakGradient U u G) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ≥0}
    (hM : ∀ t, ‖deriv f t‖₊ ≤ M) :
    HasWeakGradient U (fun x ↦ f (u x)) (fun x ↦ deriv f (u x) • G x) := by
  classical
  set L := (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) with hL
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfl : LipschitzWith M f := lipschitzWith_of_nnnorm_deriv_le hfd hM
  have hf'c : Continuous (deriv f) := hf.continuous_deriv_one
  have hMr : ∀ t, ‖deriv f t‖ ≤ (M : ℝ) := fun t ↦ by
    have := hM t
    rwa [← NNReal.coe_le_coe, coe_nnnorm] at this
  have hum : AEStronglyMeasurable u (volume.restrict U) := hw.1.aestronglyMeasurable
  have hGm : AEStronglyMeasurable G (volume.restrict U) := hw.2.1.aestronglyMeasurable
  have hloc1 : LocallyIntegrableOn (fun x ↦ f (u x)) U := by
    refine locallyIntegrableOn_of_le hU.measurableSet
      ((locallyIntegrableOn_const (|f 0|)).add (hw.1.norm.smul (M : ℝ)))
      (hfl.continuous.comp_aestronglyMeasurable hum) fun x _ ↦ ?_
    have h1 : |f (u x) - f 0| ≤ (M : ℝ) * |u x| := by
      have := hfl.dist_le_mul (u x) 0
      simpa [Real.dist_eq] using this
    have h2 : |f (u x)| ≤ |f 0| + (M : ℝ) * |u x| := by
      have := abs_sub_abs_le_abs_sub (f (u x)) (f 0)
      linarith
    simp only [Pi.add_apply, Real.norm_eq_abs]
    refine h2.trans (le_abs_self _ |>.trans_eq' ?_)
    rfl
  have hloc2 : LocallyIntegrableOn (fun x ↦ deriv f (u x) • G x) U := by
    refine locallyIntegrableOn_of_le hU.measurableSet (hw.2.1.smul (M : ℝ))
      ((hf'c.comp_aestronglyMeasurable hum).smul hGm) fun x _ ↦ ?_
    rw [norm_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs (M : ℝ), NNReal.abs_eq]
    exact mul_le_mul_of_nonneg_right (hMr _) (norm_nonneg _)
  refine HasWeakGradient.of_integral_eq hloc1 hloc2 fun φ hφc hφcs hφΩ v ↦ ?_
  set g : E d → ℝ := fun x ↦ inner ℝ (G x) v with hgdef
  have hgloc : LocallyIntegrableOn g U := locallyIntegrableOn_inner_apply hw.2.1 v
  have hφcont : Continuous φ := hφc.continuous
  set pφ : E d → ℝ := fun x ↦ fderiv ℝ φ x v with hpφdef
  have hpc : Continuous pφ := (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpcs : HasCompactSupport pφ := hφcs.fderiv_apply (𝕜 := ℝ) v
  have hpsupp : tsupport pφ ⊆ tsupport φ := tsupport_fderiv_apply_subset ℝ v
  obtain ⟨Cφ, hCφ⟩ := hφcs.exists_bound_of_continuous hφcont
  obtain ⟨Cp, hCp⟩ := hpcs.exists_bound_of_continuous hpc
  obtain ⟨δ, hδ, hK'⟩ := IsCompact.exists_cthickening_subset_open hφcs hU hφΩ
  set K' := cthickening δ (tsupport φ) with hK'def
  have hK'c : IsCompact K' := IsCompact.cthickening hφcs
  have hK'm : MeasurableSet K' := hK'c.isClosed.measurableSet
  have hKK' : tsupport φ ⊆ K' := self_subset_cthickening _
  have huK : IntegrableOn u K' := hw.1.integrableOn_compact_subset hK' hK'c
  have hgK : IntegrableOn g K' := hgloc.integrableOn_compact_subset hK' hK'c
  have hwgK : ∀ ψ : E d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ K' →
      ∀ v : E d, ∫ x, u x * fderiv ℝ ψ x v = -∫ x, inner ℝ (G x) v * ψ x :=
    fun ψ h1 h2 h3 v ↦ hw.integral_eq h1 h2 (h3.trans hK') v
  set Uf : E d → ℝ := K'.indicator u with hUdef
  set Gf : E d → ℝ := K'.indicator g with hGdef
  have hUint : Integrable Uf := (integrable_indicator_iff hK'm).mpr huK
  have hGint : Integrable Gf := (integrable_indicator_iff hK'm).mpr hgK
  have hUK : ∀ x ∈ K', Uf x = u x := fun x hx ↦ indicator_of_mem hx u
  have hGK : ∀ x ∈ K', Gf x = g x := fun x hx ↦ indicator_of_mem hx g
  have hUcs : HasCompactSupport Uf :=
    hK'c.of_isClosed_subset isClosed_closure
      (closure_minimal support_indicator_subset hK'c.isClosed)
  have hGcs : HasCompactSupport Gf :=
    hK'c.of_isClosed_subset isClosed_closure
      (closure_minimal support_indicator_subset hK'c.isClosed)
  let φb : ℕ → ContDiffBump (0 : E d) := fun n ↦
    { rIn := δ / (n + 1 : ℝ) / 2
      rOut := δ / (n + 1 : ℝ)
      rIn_pos := half_pos (by positivity)
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hrOut : ∀ n : ℕ, (φb n).rOut = δ / (n + 1 : ℝ) := fun _ ↦ rfl
  have hφrOut : Tendsto (fun n ↦ (φb n).rOut) atTop (𝓝 0) := by
    simp only [hrOut]
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
    rw [mul_zero] at this
    refine this.congr fun n ↦ ?_
    ring
  have hrOut_le : ∀ n : ℕ, (φb n).rOut ≤ δ := fun n ↦ by
    rw [hrOut]
    exact div_le_self hδ.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  set vn : ℕ → E d → ℝ := fun n ↦ Uf ⋆[L, volume] (φb n).normed volume with hvdef
  set wn : ℕ → E d → ℝ := fun n ↦ Gf ⋆[L, volume] (φb n).normed volume with hwdef
  have hvsmooth : ∀ n, ContDiff ℝ ∞ (vn n) := fun n ↦
    (φb n).hasCompactSupport_normed.contDiff_convolution_right (L := L)
      hUint.locallyIntegrable (φb n).contDiff_normed
  have hwsmooth : ∀ n, ContDiff ℝ ∞ (wn n) := fun n ↦
    (φb n).hasCompactSupport_normed.contDiff_convolution_right (L := L)
      hGint.locallyIntegrable (φb n).contDiff_normed
  have hvc : ∀ n, Continuous (vn n) := fun n ↦ (hvsmooth n).continuous
  have hwc : ∀ n, Continuous (wn n) := fun n ↦ (hwsmooth n).continuous
  have hvcs : ∀ n, HasCompactSupport (vn n) := fun n ↦
    HasCompactSupport.convolution (L := L) hUcs (φb n).hasCompactSupport_normed
  have hwcs : ∀ n, HasCompactSupport (wn n) := fun n ↦
    HasCompactSupport.convolution (L := L) hGcs (φb n).hasCompactSupport_normed
  have hvint : ∀ n, Integrable (vn n) := fun n ↦
    (hvc n).integrable_of_hasCompactSupport (hvcs n)
  have hwint : ∀ n, Integrable (wn n) := fun n ↦
    (hwc n).integrable_of_hasCompactSupport (hwcs n)
  have hpartial : ∀ n, ∀ x ∈ tsupport φ, fderiv ℝ (vn n) x v = wn n x := by
    intro n x hx
    exact fderiv_convolution_indicator_eq hK'm huK hwgK (φb n) v
      ((closedBall_subset_closedBall (hrOut_le n)).trans (closedBall_subset_cthickening hx δ))
  have hMU : MemLp Uf (ENNReal.ofReal 1) volume := by
    rw [ENNReal.ofReal_one]; exact memLp_one_iff_integrable.mpr hUint
  have hMG : MemLp Gf (ENNReal.ofReal 1) volume := by
    rw [ENNReal.ofReal_one]; exact memLp_one_iff_integrable.mpr hGint
  have hconvU : Tendsto (fun n ↦ eLpNorm (vn n - Uf) 1 volume) atTop (𝓝 0) := by
    have := tendsto_eLpNorm_convolution_sub le_rfl hMU hφrOut
    rwa [ENNReal.ofReal_one] at this
  have hconvG : Tendsto (fun n ↦ eLpNorm (wn n - Gf) 1 volume) atTop (𝓝 0) := by
    have := tendsto_eLpNorm_convolution_sub le_rfl hMG hφrOut
    rwa [ENNReal.ofReal_one] at this
  have htoRealU : Tendsto (fun n ↦ (M : ℝ) * Cp * (eLpNorm (vn n - Uf) 1 volume).toReal)
      atTop (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconvU).const_mul ((M : ℝ) * Cp)
    simpa using this
  have htoRealG : Tendsto (fun n ↦ (M : ℝ) * Cφ * (eLpNorm (wn n - Gf) 1 volume).toReal)
      atTop (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconvG).const_mul ((M : ℝ) * Cφ)
    simpa using this
  have hmeas : TendstoInMeasure volume vn atTop Uf :=
    tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hconvU
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  have hclassical : ∀ n, ∫ x, f (vn n x) * pφ x = -∫ x, deriv f (vn n x) * wn n x * φ x := by
    intro n
    have hv1 : ContDiff ℝ 1 (vn n) := (hvsmooth n).of_le (by simp)
    have hfv : ContDiff ℝ 1 (f ∘ vn n) := hf.comp hv1
    have hfvd : Differentiable ℝ (f ∘ vn n) := hfv.differentiable one_ne_zero
    have hfderiv : ∀ x, fderiv ℝ (f ∘ vn n) x v = deriv f (vn n x) * fderiv ℝ (vn n) x v := by
      intro x
      have h := (hfd (vn n x)).hasDerivAt.comp_hasFDerivAt x
        (hv1.differentiable one_ne_zero x).hasFDerivAt
      rw [h.fderiv, smul_apply, smul_eq_mul]
    have hcont1 : Continuous fun x ↦ fderiv ℝ (f ∘ vn n) x v :=
      (hfv.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := f ∘ vn n) (g := φ) (v := v)
      ((hcont1.mul hφcont).integrable_of_hasCompactSupport hφcs.mul_left)
      ((hfv.continuous.mul hpc).integrable_of_hasCompactSupport hpcs.mul_left)
      ((hfv.continuous.mul hφcont).integrable_of_hasCompactSupport hφcs.mul_left)
      (fun x _ ↦ hfvd x) (fun x _ ↦ (hφc.differentiable (by simp)) x)
    have hL' : (fun x ↦ (f ∘ vn n) x * fderiv ℝ φ x v) = fun x ↦ f (vn n x) * pφ x := rfl
    rw [hL'] at key
    rw [key]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [hfderiv x]
    by_cases hx : x ∈ tsupport φ
    · rw [hpartial n x hx]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero, mul_zero]
  have hintU : Integrable (fun x ↦ f (Uf x) * pφ x) :=
    integrable_comp_mul_of_lipschitz hUint hfl hpc hpcs
  have hlimL : Tendsto (fun n ↦ ∫ x, f (vn n x) * pφ x) atTop (𝓝 (∫ x, f (Uf x) * pφ x)) := by
    rw [← tendsto_sub_nhds_zero_iff]
    refine squeeze_zero_norm (fun n ↦ ?_) htoRealU
    have hint : Integrable (fun x ↦ f (vn n x) * pφ x) :=
      ((hfl.continuous.comp (hvc n)).mul hpc).integrable_of_hasCompactSupport hpcs.mul_left
    rw [← integral_sub hint hintU]
    have hbd : Integrable (fun x ↦ (M : ℝ) * Cp * ‖(vn n - Uf) x‖) :=
      ((hvint n).sub hUint).norm.const_mul _
    refine (norm_integral_le_of_norm_le hbd (Eventually.of_forall fun x ↦ ?_)).trans ?_
    · rw [Pi.sub_apply, ← sub_mul, norm_mul]
      have h1 : ‖f (vn n x) - f (Uf x)‖ ≤ (M : ℝ) * ‖vn n x - Uf x‖ := by
        have := hfl.dist_le_mul (vn n x) (Uf x)
        rwa [dist_eq_norm, dist_eq_norm] at this
      calc ‖f (vn n x) - f (Uf x)‖ * ‖pφ x‖
          ≤ ((M : ℝ) * ‖vn n x - Uf x‖) * Cp := by gcongr; exact hCp x
        _ = (M : ℝ) * Cp * ‖vn n x - Uf x‖ := by ring
    · have hm : AEStronglyMeasurable (vn n - Uf) volume :=
        (hvc n).aestronglyMeasurable.sub hUint.1
      rw [integral_const_mul, integral_norm_eq_lintegral_enorm hm,
        eLpNorm_one_eq_lintegral_enorm hm]
  have hintG : Integrable (fun x ↦ deriv f (Uf x) * Gf x * φ x) :=
    integrable_bdd_mul_mul_bdd (hf'c.comp_aestronglyMeasurable hUint.1) (fun x ↦ hMr _)
      hGint hφcont.aestronglyMeasurable hCφ
  have hlimR : Tendsto (fun i ↦ ∫ x, deriv f (vn (ns i) x) * wn (ns i) x * φ x) atTop
      (𝓝 (∫ x, deriv f (Uf x) * Gf x * φ x)) := by
    have hA : ∀ n, Integrable (fun x ↦ deriv f (vn n x) * (wn n x - Gf x) * φ x) :=
      fun n ↦ integrable_bdd_mul_mul_bdd (hf'c.comp (hvc n)).aestronglyMeasurable
        (fun x ↦ hMr _) ((hwint n).sub hGint) hφcont.aestronglyMeasurable hCφ
    have hB : ∀ n, Integrable (fun x ↦ deriv f (vn n x) * Gf x * φ x) :=
      fun n ↦ integrable_bdd_mul_mul_bdd (hf'c.comp (hvc n)).aestronglyMeasurable
        (fun x ↦ hMr _) hGint hφcont.aestronglyMeasurable hCφ
    have hsplit : ∀ i, ∫ x, deriv f (vn (ns i) x) * wn (ns i) x * φ x
        = (∫ x, deriv f (vn (ns i) x) * (wn (ns i) x - Gf x) * φ x)
          + ∫ x, deriv f (vn (ns i) x) * Gf x * φ x := by
      intro i
      rw [← integral_add (hA _) (hB _)]
      exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp only; ring)
    have hpiece1 : Tendsto (fun i ↦ ∫ x, deriv f (vn (ns i) x) * (wn (ns i) x - Gf x) * φ x)
        atTop (𝓝 0) := by
      refine squeeze_zero_norm
        (a := fun i ↦ (M : ℝ) * Cφ * (eLpNorm (wn (ns i) - Gf) 1 volume).toReal)
        (fun i ↦ ?_) (htoRealG.comp hns.tendsto_atTop)
      have hbd : Integrable (fun x ↦ (M : ℝ) * Cφ * ‖(wn (ns i) - Gf) x‖) :=
        ((hwint _).sub hGint).norm.const_mul _
      refine (norm_integral_le_of_norm_le hbd (Eventually.of_forall fun x ↦ ?_)).trans ?_
      · rw [Pi.sub_apply, norm_mul, norm_mul]
        calc ‖deriv f (vn (ns i) x)‖ * ‖wn (ns i) x - Gf x‖ * ‖φ x‖
            ≤ (M : ℝ) * ‖wn (ns i) x - Gf x‖ * Cφ := by
              gcongr
              · exact hMr _
              · exact hCφ x
          _ = (M : ℝ) * Cφ * ‖wn (ns i) x - Gf x‖ := by ring
      · have hm : AEStronglyMeasurable (wn (ns i) - Gf) volume :=
          (hwc _).aestronglyMeasurable.sub hGint.1
        rw [integral_const_mul, integral_norm_eq_lintegral_enorm hm,
          eLpNorm_one_eq_lintegral_enorm hm]
    have hpiece2 : Tendsto (fun i ↦ ∫ x, deriv f (vn (ns i) x) * Gf x * φ x) atTop
        (𝓝 (∫ x, deriv f (Uf x) * Gf x * φ x)) := by
      refine tendsto_integral_of_dominated_convergence (fun x ↦ (M : ℝ) * Cφ * ‖Gf x‖)
        (fun i ↦ (hB (ns i)).1) (hGint.norm.const_mul _)
        (fun i ↦ Eventually.of_forall fun x ↦ ?_) ?_
      · rw [norm_mul, norm_mul]
        calc ‖deriv f (vn (ns i) x)‖ * ‖Gf x‖ * ‖φ x‖ ≤ (M : ℝ) * ‖Gf x‖ * Cφ := by
              gcongr
              · exact hMr _
              · exact hCφ x
          _ = (M : ℝ) * Cφ * ‖Gf x‖ := by ring
      · filter_upwards [hae] with x hx
        exact (((hf'c.tendsto (Uf x)).comp hx).mul_const (Gf x)).mul_const (φ x)
    have := hpiece1.add hpiece2
    rw [zero_add] at this
    exact this.congr fun i ↦ (hsplit i).symm
  have hlimL' : Tendsto (fun i ↦ ∫ x, f (vn (ns i) x) * pφ x) atTop
      (𝓝 (∫ x, f (Uf x) * pφ x)) := hlimL.comp hns.tendsto_atTop
  have hlimR' : Tendsto (fun i ↦ ∫ x, f (vn (ns i) x) * pφ x) atTop
      (𝓝 (-∫ x, deriv f (Uf x) * Gf x * φ x)) := by
    simp only [hclassical]
    exact hlimR.neg
  have hwhole : ∫ x, f (Uf x) * pφ x = -∫ x, deriv f (Uf x) * Gf x * φ x :=
    tendsto_nhds_unique hlimL' hlimR'
  have e1 : (fun x ↦ f (u x) * fderiv ℝ φ x v) = fun x ↦ f (Uf x) * pφ x := by
    funext x
    by_cases hx : x ∈ K'
    · rw [hUK x hx]
    · rw [show pφ x = 0 from image_eq_zero_of_notMem_tsupport fun hc ↦ hx (hKK' (hpsupp hc)),
        fderiv_apply_eq_zero_of_notMem_tsupport (fun hc ↦ hx (hKK' hc)), mul_zero, mul_zero]
  have e2 : (fun x ↦ inner ℝ (deriv f (u x) • G x) v * φ x) =
      fun x ↦ deriv f (Uf x) * Gf x * φ x := by
    funext x
    rw [real_inner_smul_left]
    by_cases hx : x ∈ K'
    · rw [hUK x hx, hGK x hx]
    · rw [image_eq_zero_of_notMem_tsupport fun hc ↦ hx (hKK' hc), mul_zero, mul_zero]
  rw [e1, e2]
  exact hwhole

end ChainRule

/-! ### The positive part -/

section PosPart

/-- The `C¹` approximation of the positive part, `√((t⁺)² + ε²) - ε`. -/
noncomputable def posPartApprox (ε t : ℝ) : ℝ := Real.sqrt ((max t 0) ^ 2 + ε ^ 2) - ε

theorem hasDerivAt_max_sq (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ (max s 0) ^ 2) (2 * max t 0) t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have h0 : (fun s : ℝ ↦ (max s 0) ^ 2) =ᶠ[𝓝 t] fun _ ↦ (0 : ℝ) :=
      (gt_mem_nhds ht).mono fun s hs ↦ by simp [max_eq_right hs.le]
    rw [max_eq_right ht.le, mul_zero]
    exact (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq h0
  · rw [hasDerivAt_iff_tendsto_slope_zero]
    simp only [zero_add, max_self, zero_pow two_ne_zero, sub_zero, mul_zero, smul_eq_mul]
    have hcont : Tendsto (fun s : ℝ ↦ max s 0) (𝓝[≠] 0) (𝓝 0) := by
      have hc0 : Continuous fun s : ℝ ↦ max s 0 := continuous_id.max continuous_const
      have := hc0.tendsto (0 : ℝ)
      simp only [max_self] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine hcont.congr' (eventually_nhdsWithin_iff.mpr (Eventually.of_forall fun s hs ↦ ?_))
    rcases lt_or_gt_of_ne hs with hs' | hs'
    · simp [max_eq_right hs'.le]
    · simp only [max_eq_left hs'.le]
      field_simp
  · have h0 : (fun s : ℝ ↦ (max s 0) ^ 2) =ᶠ[𝓝 t] fun s ↦ s ^ 2 :=
      (lt_mem_nhds ht).mono fun s hs ↦ by simp [max_eq_left hs.le]
    rw [max_eq_left ht.le]
    have := hasDerivAt_pow 2 t
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at this
    exact this.congr_of_eventuallyEq h0

theorem contDiff_max_sq : ContDiff ℝ 1 fun s : ℝ ↦ (max s 0) ^ 2 := by
  refine contDiff_one_iff_deriv.mpr ⟨fun t ↦ (hasDerivAt_max_sq t).differentiableAt, ?_⟩
  rw [funext fun t ↦ (hasDerivAt_max_sq t).deriv]
  exact continuous_const.mul (continuous_id.max continuous_const)

theorem posPartApprox_arg_pos {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) : 0 < (max t 0) ^ 2 + ε ^ 2 := by
  have := pow_pos (abs_pos.mpr hε) 2
  rw [sq_abs] at this
  nlinarith [sq_nonneg (max t 0)]

theorem hasDerivAt_posPartApprox {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    HasDerivAt (posPartApprox ε)
      (2 * max t 0 / (2 * Real.sqrt ((max t 0) ^ 2 + ε ^ 2))) t :=
  (((hasDerivAt_max_sq t).add_const (ε ^ 2)).sqrt (posPartApprox_arg_pos hε t).ne').sub_const ε

theorem contDiff_posPartApprox {ε : ℝ} (hε : ε ≠ 0) : ContDiff ℝ 1 (posPartApprox ε) :=
  ((contDiff_max_sq.add contDiff_const).sqrt fun t ↦ (posPartApprox_arg_pos hε t).ne').sub
    contDiff_const

theorem deriv_posPartApprox {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    deriv (posPartApprox ε) t = max t 0 / Real.sqrt ((max t 0) ^ 2 + ε ^ 2) := by
  rw [(hasDerivAt_posPartApprox hε t).deriv, mul_div_mul_left _ _ two_ne_zero]

theorem deriv_posPartApprox_mem {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    0 ≤ deriv (posPartApprox ε) t ∧ deriv (posPartApprox ε) t ≤ 1 := by
  rw [deriv_posPartApprox hε]
  have hm : 0 ≤ max t 0 := le_max_right _ _
  have hs : 0 < Real.sqrt ((max t 0) ^ 2 + ε ^ 2) :=
    Real.sqrt_pos.mpr (posPartApprox_arg_pos hε t)
  refine ⟨div_nonneg hm hs.le, (div_le_one hs).mpr ?_⟩
  exact (Real.le_sqrt hm (posPartApprox_arg_pos hε t).le).mpr (by nlinarith [sq_nonneg ε])

theorem nnnorm_deriv_posPartApprox_le {ε : ℝ} (hε : ε ≠ 0) (t : ℝ) :
    ‖deriv (posPartApprox ε) t‖₊ ≤ 1 := by
  obtain ⟨h0, h1⟩ := deriv_posPartApprox_mem hε t
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg h0, NNReal.coe_one]
  exact h1

theorem posPartApprox_mem {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    0 ≤ posPartApprox ε t ∧ posPartApprox ε t ≤ max t 0 := by
  have hm : 0 ≤ max t 0 := le_max_right _ _
  unfold posPartApprox
  constructor
  · rw [sub_nonneg]
    calc ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε).symm
      _ ≤ Real.sqrt ((max t 0) ^ 2 + ε ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (max t 0)])
  · rw [sub_le_iff_le_add]
    exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩

theorem tendsto_posPartApprox (t : ℝ) :
    Tendsto (fun ε ↦ posPartApprox ε t) (𝓝 0) (𝓝 (max t 0)) := by
  have hc : Continuous fun ε : ℝ ↦ posPartApprox ε t := by
    unfold posPartApprox
    fun_prop
  have := hc.tendsto 0
  simp only [posPartApprox, zero_pow two_ne_zero, add_zero, sub_zero,
    Real.sqrt_sq (le_max_right t 0)] at this
  exact this

theorem tendsto_deriv_posPartApprox (t : ℝ) :
    Tendsto (fun n : ℕ ↦ deriv (posPartApprox (1 / (n + 1 : ℝ))) t) atTop
      (𝓝 (if 0 < t then 1 else 0)) := by
  have hεne : ∀ n : ℕ, (1 / (n + 1 : ℝ)) ≠ 0 := fun n ↦ by positivity
  simp only [fun n ↦ deriv_posPartApprox (hεne n) t]
  split_ifs with ht
  · rw [max_eq_left ht.le]
    have hc : Continuous fun ε : ℝ ↦ t / Real.sqrt (t ^ 2 + ε ^ 2) := by
      refine continuous_const.div (continuous_const.add (continuous_id.pow 2)).sqrt fun ε ↦ ?_
      exact (Real.sqrt_pos.mpr (by positivity)).ne'
    have := (hc.tendsto 0).comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simp only [Function.comp_def, zero_pow two_ne_zero, add_zero, Real.sqrt_sq ht.le,
      div_self ht.ne'] at this
    exact this
  · rw [max_eq_right (not_lt.mp ht)]
    simp only [zero_div]
    exact tendsto_const_nhds

variable {u : E d → ℝ} {G : E d → E d}

/-- **Weak gradient of the positive part** (Gilbarg–Trudinger Lemma 7.6):
`∇ u₊ = 1_{u > 0} ∇u`. -/
theorem _root_.EllipticBernoulli.HasWeakGradient.posPart (hU : IsOpen U)
    (hw : HasWeakGradient U u G) :
    HasWeakGradient U (fun x ↦ max (u x) 0) ({x | 0 < u x}.indicator G) := by
  have hum : AEStronglyMeasurable u (volume.restrict U) := hw.1.aestronglyMeasurable
  have hloc1 : LocallyIntegrableOn (fun x ↦ max (u x) 0) U :=
    locallyIntegrableOn_of_le hU.measurableSet hw.1
      ((continuous_id.max continuous_const).comp_aestronglyMeasurable hum) fun x _ ↦ by
        simp only [Real.norm_eq_abs]
        rw [abs_of_nonneg (le_max_right _ _)]
        exact max_le (le_abs_self _) (abs_nonneg _)
  have hloc2 : LocallyIntegrableOn ({x | 0 < u x}.indicator G) U :=
    locallyIntegrableOn_of_le hU.measurableSet hw.2.1
      (AEStronglyMeasurable.indicator_lt hum hw.2.1.aestronglyMeasurable 0) fun x _ ↦
        norm_indicator_le_norm_self _ _
  refine ⟨hloc1, hloc2, fun φ hφc hφcs hφΩ v ↦ ?_⟩
  set g : E d → ℝ := fun x ↦ inner ℝ (G x) v with hgdef
  have hgloc : LocallyIntegrableOn g U := locallyIntegrableOn_inner_apply hw.2.1 v
  have hφcont : Continuous φ := hφc.continuous
  have hpc : Continuous (fun x ↦ fderiv ℝ φ x v) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hpcs : HasCompactSupport (fun x ↦ fderiv ℝ φ x v) := hφcs.fderiv_apply (𝕜 := ℝ) v
  have hps : tsupport (fun x ↦ fderiv ℝ φ x v) ⊆ U :=
    (tsupport_fderiv_apply_subset ℝ v).trans hφΩ
  set ε : ℕ → ℝ := fun n ↦ 1 / (n + 1 : ℝ) with hεdef
  have hεpos : ∀ n, 0 < ε n := fun n ↦ by positivity
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hn : ∀ n, ∫ x in U, posPartApprox (ε n) (u x) * fderiv ℝ φ x v
      = -∫ x in U, deriv (posPartApprox (ε n)) (u x) * g x * φ x := by
    intro n
    have h := (hw.comp hU (contDiff_posPartApprox (hεpos n).ne') (M := 1)
      (nnnorm_deriv_posPartApprox_le (hεpos n).ne')).2.2 φ hφc hφcs hφΩ v
    rw [h]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only [real_inner_smul_left, hgdef]
  have hL : Tendsto (fun n ↦ ∫ x in U, posPartApprox (ε n) (u x) * fderiv ℝ φ x v) atTop
      (𝓝 (∫ x in U, max (u x) 0 * fderiv ℝ φ x v)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖u x * fderiv ℝ φ x v‖)
      (fun n ↦ ((contDiff_posPartApprox (hεpos n).ne').continuous.comp_aestronglyMeasurable
        hum).mul hpc.aestronglyMeasurable)
      (integrable_mul_of_locallyIntegrableOn hw.1 hpc hpcs hps).norm.integrableOn
      (fun n ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
    · obtain ⟨h0, h1⟩ := posPartApprox_mem (hεpos n).le (u x)
      rw [norm_mul, norm_mul, Real.norm_eq_abs (posPartApprox _ _), abs_of_nonneg h0]
      gcongr
      refine h1.trans ?_
      rw [Real.norm_eq_abs]
      exact max_le (le_abs_self _) (abs_nonneg _)
    · exact ((tendsto_posPartApprox (u x)).comp hε0).mul_const _
  have hR : Tendsto (fun n ↦ ∫ x in U, deriv (posPartApprox (ε n)) (u x) * g x * φ x) atTop
      (𝓝 (∫ x in U, (if 0 < u x then 1 else 0) * g x * φ x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x ↦ ‖g x * φ x‖)
      (fun n ↦ (((contDiff_posPartApprox (hεpos n).ne').continuous_deriv_one
        |>.comp_aestronglyMeasurable hum).mul hgloc.aestronglyMeasurable).mul
        hφcont.aestronglyMeasurable)
      (integrable_mul_of_locallyIntegrableOn hgloc hφcont hφcs hφΩ).norm.integrableOn
      (fun n ↦ Eventually.of_forall fun x ↦ ?_) (Eventually.of_forall fun x ↦ ?_)
    · obtain ⟨h0, h1⟩ := deriv_posPartApprox_mem (hεpos n).ne' (u x)
      rw [norm_mul, norm_mul, norm_mul, Real.norm_eq_abs (deriv _ _), abs_of_nonneg h0]
      calc deriv (posPartApprox (ε n)) (u x) * ‖g x‖ * ‖φ x‖
          ≤ 1 * ‖g x‖ * ‖φ x‖ := by gcongr
        _ = ‖g x‖ * ‖φ x‖ := by ring
    · exact ((tendsto_deriv_posPartApprox (u x)).mul_const _).mul_const _
  have hlim := tendsto_nhds_unique hL (by simp only [hn]; exact hR.neg)
  rw [hlim]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  by_cases hx : 0 < u x
  · simp [hx, hgdef]
  · simp [hx]

end PosPart

/-! ### `H¹_loc` closure properties -/

section MemH1Loc

variable {u w : E d → ℝ} {G H : E d → E d}

theorem memLp_continuous_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set (E d)} (hK : IsCompact K) {η : E d → ℝ} (hη : Continuous η) {f : E d → F}
    (hf : MemLp f 2 (volume.restrict K)) : MemLp (fun x ↦ η x • f x) 2 (volume.restrict K) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hη.continuousOn
  refine (hf.const_smul C).of_le (hη.aestronglyMeasurable.smul hf.aestronglyMeasurable) ?_
  refine (ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall fun x hx ↦ ?_)
  rw [norm_smul, Pi.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_right ((hC x hx).trans (le_abs_self C) |>.trans_eq
    (Real.norm_eq_abs C).symm) (norm_nonneg _)

theorem memLp_smul_continuous {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {K : Set (E d)} (hK : IsCompact K) {f : E d → ℝ} (hf : MemLp f 2 (volume.restrict K))
    {g : E d → F} (hg : Continuous g) : MemLp (fun x ↦ f x • g x) 2 (volume.restrict K) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine (hf.const_mul C).of_le (hf.aestronglyMeasurable.smul hg.aestronglyMeasurable) ?_
  refine (ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall fun x hx ↦ ?_)
  rw [norm_smul, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right ((hC x hx).trans (le_abs_self C) |>.trans_eq
    (Real.norm_eq_abs C).symm) (norm_nonneg _)

theorem _root_.EllipticBernoulli.MemH1Loc.add (hu : MemH1Loc U u G) (hw : MemH1Loc U w H) :
    MemH1Loc U (fun x ↦ u x + w x) (fun x ↦ G x + H x) :=
  ⟨hu.1.add hw.1, fun K hK hKc ↦ ⟨(hu.2 K hK hKc).1.add (hw.2 K hK hKc).1,
    (hu.2 K hK hKc).2.add (hw.2 K hK hKc).2⟩⟩

theorem _root_.EllipticBernoulli.MemH1Loc.neg (hu : MemH1Loc U u G) :
    MemH1Loc U (fun x ↦ -u x) (fun x ↦ -G x) :=
  ⟨hu.1.neg, fun K hK hKc ↦ ⟨(hu.2 K hK hKc).1.neg, (hu.2 K hK hKc).2.neg⟩⟩

theorem _root_.EllipticBernoulli.MemH1Loc.sub (hu : MemH1Loc U u G) (hw : MemH1Loc U w H) :
    MemH1Loc U (fun x ↦ u x - w x) (fun x ↦ G x - H x) :=
  ⟨hu.1.sub hw.1, fun K hK hKc ↦ ⟨(hu.2 K hK hKc).1.sub (hw.2 K hK hKc).1,
    (hu.2 K hK hKc).2.sub (hw.2 K hK hKc).2⟩⟩

theorem memH1Loc_const (c : ℝ) : MemH1Loc U (fun _ ↦ c) (fun _ ↦ 0) := by
  refine ⟨hasWeakGradient_const c, fun K _ hKc ↦ ?_⟩
  have : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.2 hKc.measure_lt_top.ne
  exact ⟨memLp_const c, memLp_const 0⟩

theorem _root_.EllipticBernoulli.MemH1Loc.sub_const (hu : MemH1Loc U u G) (c : ℝ) :
    MemH1Loc U (fun x ↦ u x - c) G := by
  have := hu.sub (memH1Loc_const c)
  simpa using this

theorem _root_.EllipticBernoulli.MemH1Loc.const_sub (hu : MemH1Loc U u G) (c : ℝ) :
    MemH1Loc U (fun x ↦ c - u x) (fun x ↦ -G x) := by
  have := (memH1Loc_const c).sub hu
  simpa using this

theorem _root_.EllipticBernoulli.MemH1Loc.mul_smooth (hU : IsOpen U) (hu : MemH1Loc U u G)
    {η : E d → ℝ} (hη : ContDiff ℝ ∞ η) :
    MemH1Loc U (fun x ↦ η x * u x) (fun x ↦ η x • G x + u x • ∇ η x) := by
  refine ⟨hu.1.mul_smooth hU hη, fun K hK hKc ↦ ⟨?_, ?_⟩⟩
  · simpa [smul_eq_mul] using memLp_continuous_smul hKc hη.continuous (hu.2 K hK hKc).1
  · exact (memLp_continuous_smul hKc hη.continuous (hu.2 K hK hKc).2).add
      (memLp_smul_continuous hKc (hu.2 K hK hKc).1 (continuous_gradient (hη.of_le (by simp))))

/-- **`v₊ ∈ H¹_loc`.** If `v ∈ H¹_loc(U)` with weak gradient `G`, then `v₊ = max(v, 0)` is in
`H¹_loc(U)` with weak gradient `1_{v > 0} G` (Gilbarg–Trudinger Lemma 7.6). -/
theorem memH1Loc_posPart {U : Set (E d)} {v : E d → ℝ} {G : E d → E d} (hU : IsOpen U)
    (hv : MemH1Loc U v G) :
    MemH1Loc U (fun y ↦ max (v y) 0) ({y | 0 < v y}.indicator G) := by
  refine ⟨hv.1.posPart hU, fun K hK hKc ↦ ⟨?_, ?_⟩⟩
  · have h := (hv.2 K hK hKc).1
    refine h.of_le ((continuous_id.max continuous_const).comp_aestronglyMeasurable
      h.aestronglyMeasurable)
      (Eventually.of_forall fun x ↦ ?_)
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  · have h := (hv.2 K hK hKc)
    exact h.2.of_le (AEStronglyMeasurable.indicator_lt h.1.aestronglyMeasurable
      h.2.aestronglyMeasurable 0)
      (Eventually.of_forall fun x ↦ norm_indicator_le_norm_self _ _)

/-- `(u - k)₊ ∈ H¹_loc` with weak gradient `1_{u > k} G`. -/
theorem _root_.EllipticBernoulli.MemH1Loc.posPart_sub (hU : IsOpen U) (hu : MemH1Loc U u G)
    (k : ℝ) : MemH1Loc U (fun y ↦ max (u y - k) 0) ({y | k < u y}.indicator G) := by
  have := memH1Loc_posPart hU (hu.sub_const k)
  simpa only [sub_pos] using this

/-- `(k - u)₊ ∈ H¹_loc` with weak gradient `-1_{u < k} G`. -/
theorem _root_.EllipticBernoulli.MemH1Loc.posPart_const_sub (hU : IsOpen U)
    (hu : MemH1Loc U u G) (k : ℝ) :
    MemH1Loc U (fun y ↦ max (k - u y) 0) ({y | u y < k}.indicator fun y ↦ -G y) := by
  have := memH1Loc_posPart hU (hu.const_sub k)
  simpa only [sub_pos] using this

end MemH1Loc

/-! ### `max` and `min`

`max u w = u + (w - u)₊` and `min u w = u - (u - w)₊`, with the gradients read off from the
positive-part rule. -/

section MaxMin

variable {u w : E d → ℝ} {G H : E d → E d}

theorem max_eq_add_posPart_sub (a b : ℝ) : max a b = a + max (b - a) 0 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_left (sub_nonneg.2 h)]; ring
  · rw [max_eq_left h, max_eq_right (sub_nonpos.2 h)]; ring

theorem min_eq_sub_posPart_sub (a b : ℝ) : min a b = a - max (a - b) 0 := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonpos.2 h)]; ring
  · rw [min_eq_right h, max_eq_left (sub_nonneg.2 h)]; ring

private theorem max_fun_eq :
    (fun y ↦ max (u y) (w y)) = fun y ↦ u y + max (w y - u y) 0 :=
  funext fun y ↦ max_eq_add_posPart_sub (u y) (w y)

private theorem max_grad_eq :
    (fun y ↦ if u y < w y then H y else G y) =
      fun y ↦ G y + {y | 0 < w y - u y}.indicator (fun y ↦ H y - G y) y := by
  funext y
  by_cases hy : u y < w y
  · simp [indicator, hy, sub_pos]
  · simp [indicator, hy, sub_pos]

private theorem min_fun_eq :
    (fun y ↦ min (u y) (w y)) = fun y ↦ u y - max (u y - w y) 0 :=
  funext fun y ↦ min_eq_sub_posPart_sub (u y) (w y)

private theorem min_grad_eq :
    (fun y ↦ if w y < u y then H y else G y) =
      fun y ↦ G y - {y | 0 < u y - w y}.indicator (fun y ↦ G y - H y) y := by
  funext y
  by_cases hy : w y < u y
  · simp [indicator, hy, sub_pos]
  · simp [indicator, hy, sub_pos]

/-- **`max` of two functions with weak gradients**: `∇ max(u, w) = ∇w` on `{u < w}` and `∇u`
elsewhere. -/
protected theorem _root_.EllipticBernoulli.HasWeakGradient.max (hU : IsOpen U)
    (hu : HasWeakGradient U u G) (hw : HasWeakGradient U w H) :
    HasWeakGradient U (fun y ↦ max (u y) (w y)) (fun y ↦ if u y < w y then H y else G y) := by
  rw [max_fun_eq, max_grad_eq]
  exact hu.add ((hw.sub hu).posPart hU)

/-- **`min` of two functions with weak gradients**: `∇ min(u, w) = ∇w` on `{w < u}` and `∇u`
elsewhere. -/
protected theorem _root_.EllipticBernoulli.HasWeakGradient.min (hU : IsOpen U)
    (hu : HasWeakGradient U u G) (hw : HasWeakGradient U w H) :
    HasWeakGradient U (fun y ↦ min (u y) (w y)) (fun y ↦ if w y < u y then H y else G y) := by
  rw [min_fun_eq, min_grad_eq]
  exact hu.sub ((hu.sub hw).posPart hU)

/-- **`max` in `H¹_loc`.** -/
protected theorem _root_.EllipticBernoulli.MemH1Loc.max (hU : IsOpen U) (hu : MemH1Loc U u G)
    (hw : MemH1Loc U w H) :
    MemH1Loc U (fun y ↦ max (u y) (w y)) (fun y ↦ if u y < w y then H y else G y) := by
  rw [max_fun_eq, max_grad_eq]
  exact hu.add (memH1Loc_posPart hU (hw.sub hu))

/-- **`min` in `H¹_loc`.** -/
protected theorem _root_.EllipticBernoulli.MemH1Loc.min (hU : IsOpen U) (hu : MemH1Loc U u G)
    (hw : MemH1Loc U w H) :
    MemH1Loc U (fun y ↦ min (u y) (w y)) (fun y ↦ if w y < u y then H y else G y) := by
  rw [min_fun_eq, min_grad_eq]
  exact hu.sub (memH1Loc_posPart hU (hu.sub hw))

end MaxMin

end EllipticBernoulli
