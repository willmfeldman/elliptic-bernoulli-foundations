/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sobolev.Lattice
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Uniqueness of weak gradients and Stampacchia's lemma

* `HasWeakGradient.ae_eq_of_eqOn`: if `f = g` on an open `W ⊆ U`, their weak gradients agree a.e.
  on `W`.
* `HasWeakGradient.ae_eq_of_ae_eq_on`: the same when `f = g` only a.e. on `W`.
* `HasWeakGradient.ae_eq_zero_of_ae_eq_zero_on`: if `f = 0` a.e. on an open `O ⊆ U`, its weak
  gradient vanishes a.e. on `O`.
* `HasWeakGradient.ae_eq_zero_of_eq_zero` (**Stampacchia**; Gilbarg–Trudinger Lemma 7.7): the weak
  gradient vanishes a.e. on the level set `{v = 0}`.
* `HasWeakGradient.exists_modify_zero`: a representative `G'` of the weak gradient with `G' = 0`
  *pointwise* on `{v = 0}`, the hypothesis shape of `SobolevSupport`.
* `HasWeakGradient.ae_eq_zero_of_eq_const`: the same on any level set `{v = c}`.

The proof of Stampacchia's lemma uses no truncation machinery: `v = v₊ - (-v)₊` has weak gradient
`1_{v>0} G + 1_{v<0} G` by the positive-part rule, and uniqueness gives `G = 1_{v ≠ 0} G` a.e.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

theorem locallyIntegrableOn_inner_const {U : Set (E d)} {G : E d → E d}
    (hG : LocallyIntegrableOn G U) (v : E d) :
    LocallyIntegrableOn (fun x ↦ inner ℝ (G x) v) U := by
  intro x hx
  obtain ⟨t, ht, hi⟩ := hG x hx
  refine ⟨t, ht, ?_⟩
  have := (innerSL ℝ v).integrable_comp hi
  rw [IntegrableOn]
  simpa [innerSL_apply_apply, real_inner_comm] using this

/-- A function locally integrable on an open `U`, multiplied by a continuous function with compact
support in `U`, is integrable on `U`. -/
theorem integrableOn_mul_of_tsupport_subset {U : Set (E d)} (hU : IsOpen U) {F φ : E d → ℝ}
    (hF : LocallyIntegrableOn F U) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) : IntegrableOn (fun x ↦ F x * φ x) U := by
  have hK : IsCompact (tsupport φ) := hφc
  have h1 : IntegrableOn F (tsupport φ) := hF.integrableOn_compact_subset hφU hK
  exact (h1.mul_continuousOn hφ.continuousOn hK).of_forall_sdiff_eq_zero hU.measurableSet
    fun x hx ↦ by simp [image_eq_zero_of_notMem_tsupport hx.2]

theorem eq_zero_of_forall_inner_single {z : E d}
    (h : ∀ i : Fin d, inner ℝ z (EuclideanSpace.single i (1 : ℝ)) = 0) : z = 0 := by
  ext i
  simpa [EuclideanSpace.inner_single_right] using h i

/-- **Uniqueness of weak gradients.** If `G₁` is a weak gradient of `f` and `G₂` one of `g` in the
open set `U`, and `f = g` on an open `W ⊆ U`, then `G₁ = G₂` a.e. on `W`. -/
theorem HasWeakGradient.ae_eq_of_eqOn {U W : Set (E d)} (hU : IsOpen U) (hW : IsOpen W)
    (hWU : W ⊆ U) {f g : E d → ℝ} {G₁ G₂ : E d → E d} (hf : HasWeakGradient U f G₁)
    (hg : HasWeakGradient U g G₂) (hfg : EqOn f g W) :
    ∀ᵐ x ∂(volume.restrict W), G₁ x = G₂ x := by
  have key : ∀ v : E d, ∀ᵐ x ∂(volume : Measure (E d)),
      x ∈ W → inner ℝ (G₁ x) v - inner ℝ (G₂ x) v = 0 := by
    intro v
    have hl1 := locallyIntegrableOn_inner_const hf.2.1 v
    have hl2 := locallyIntegrableOn_inner_const hg.2.1 v
    refine hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hl1.sub hl2).mono_set hWU) fun φ hφ hφc hφW ↦ ?_
    have hφU := hφW.trans hWU
    have h1 := hf.2.2 φ hφ hφc hφU v
    have h2 := hg.2.2 φ hφ hφc hφU v
    have hlhs : ∫ x in U, f x * fderiv ℝ φ x v = ∫ x in U, g x * fderiv ℝ φ x v := by
      refine setIntegral_congr_fun hU.measurableSet fun x _ ↦ ?_
      by_cases hxW : x ∈ W
      · simp [hfg hxW]
      · have hx : x ∉ tsupport φ := fun h ↦ hxW (hφW h)
        have : fderiv ℝ φ x = 0 :=
          Function.notMem_support.1 fun h ↦ hx (support_fderiv_subset ℝ h)
        simp [this]
    have hφc' : Continuous φ := hφ.continuous
    have i1 := integrableOn_mul_of_tsupport_subset hU hl1 hφc' hφc hφU
    have i2 := integrableOn_mul_of_tsupport_subset hU hl2 hφc' hφc hφU
    have hzero : ∀ x, x ∉ U → φ x • (inner ℝ (G₁ x) v - inner ℝ (G₂ x) v) = 0 := by
      intro x hx
      simp [image_eq_zero_of_notMem_tsupport fun h ↦ hx (hφU h)]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    have : ∫ x in U, φ x • (inner ℝ (G₁ x) v - inner ℝ (G₂ x) v) =
        (∫ x in U, inner ℝ (G₁ x) v * φ x) - ∫ x in U, inner ℝ (G₂ x) v * φ x := by
      rw [← integral_sub i1 i2]
      congr 1; funext x; simp only [smul_eq_mul]; ring
    rw [this]
    linarith
  have hall : ∀ᵐ x ∂(volume : Measure (E d)), ∀ i : Fin d,
      x ∈ W → inner ℝ (G₁ x) (EuclideanSpace.single i (1 : ℝ)) -
        inner ℝ (G₂ x) (EuclideanSpace.single i (1 : ℝ)) = 0 :=
    ae_all_iff.2 fun i ↦ key _
  rw [ae_restrict_iff' hW.measurableSet]
  filter_upwards [hall] with x hx hxW
  have := eq_zero_of_forall_inner_single (z := G₁ x - G₂ x) fun i ↦ by
    rw [inner_sub_left]; exact hx i hxW
  exact sub_eq_zero.1 this

/-- The weak gradient vanishes a.e. on an open set `O ⊆ U` where the function vanishes a.e. -/
theorem HasWeakGradient.ae_eq_zero_of_ae_eq_zero_on {U O : Set (E d)} {w : E d → ℝ}
    {G : E d → E d} (hw : HasWeakGradient U w G) (hO : IsOpen O) (hOU : O ⊆ U)
    (h0 : ∀ᵐ y ∂(volume.restrict O), w y = 0) : ∀ᵐ y ∂(volume.restrict O), G y = 0 := by
  rw [ae_restrict_iff' hO.measurableSet] at h0 ⊢
  have key : ∀ v : E d, ∀ᵐ y, y ∈ O → inner ℝ (G y) v = 0 := by
    intro v
    refine hO.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (locallyIntegrableOn_inner_const (hw.2.1.mono_set hOU) v) fun φ hφ hφc hφO ↦ ?_
    have h := hw.integral_eq hφ hφc (hφO.trans hOU) v
    have hl : ∫ y, w y * fderiv ℝ φ y v = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [h0] with y hy
      by_cases hyO : y ∈ O
      · simp [hy hyO]
      · simp [fderiv_apply_eq_zero_of_notMem_tsupport (fun h ↦ hyO (hφO h)) v]
    rw [hl] at h
    have h' : ∫ y, inner ℝ (G y) v * φ y = 0 := by linarith
    rw [← h']
    congr 1; funext y; rw [smul_eq_mul, mul_comm]
  have hall : ∀ᵐ y, ∀ i : Fin d, y ∈ O → inner ℝ (G y) (EuclideanSpace.single i (1 : ℝ)) = 0 :=
    ae_all_iff.2 fun i ↦ key _
  filter_upwards [hall] with y hy hyO
  exact eq_zero_of_forall_inner_single fun i ↦ hy i hyO

/-- **Uniqueness of weak gradients, a.e. version.** If `f = g` a.e. on an open `W ⊆ U`, then
their weak gradients on `U` agree a.e. on `W`. -/
theorem HasWeakGradient.ae_eq_of_ae_eq_on {U W : Set (E d)} (hW : IsOpen W) (hWU : W ⊆ U)
    {f g : E d → ℝ} {G₁ G₂ : E d → E d} (hf : HasWeakGradient U f G₁)
    (hg : HasWeakGradient U g G₂) (hfg : ∀ᵐ x ∂(volume.restrict W), f x = g x) :
    ∀ᵐ x ∂(volume.restrict W), G₁ x = G₂ x := by
  have h := (hf.sub hg).ae_eq_zero_of_ae_eq_zero_on hW hWU
    (by filter_upwards [hfg] with x hx; rw [hx, sub_self])
  filter_upwards [h] with x hx using sub_eq_zero.1 hx

/-- The algebraic identity behind Stampacchia's lemma: `v = v₊ - (-v)₊` has weak gradient
`1_{v>0} G + 1_{v<0} G`. -/
theorem HasWeakGradient.posPart_sub_negPart {U : Set (E d)} (hU : IsOpen U) {v : E d → ℝ}
    {G : E d → E d} (hv : HasWeakGradient U v G) :
    HasWeakGradient U v (fun x ↦ {y | 0 < v y}.indicator G x + {y | v y < 0}.indicator G x) := by
  have h1 := hv.posPart hU
  have h2 := hv.neg.posPart hU
  have h3 := h1.sub h2
  have hfun : (fun x ↦ max (v x) 0 - max (-v x) 0) = v := by
    funext x
    rcases le_total (v x) 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
  rw [hfun] at h3
  convert h3 using 2 with x
  by_cases hx : v x < 0
  · have hx' : ¬ 0 < v x := by linarith
    simp [indicator, hx, hx']
  · by_cases hx' : 0 < v x
    · simp [indicator, hx, hx']
    · simp [indicator, hx, hx']

/-- **Stampacchia's lemma** (Gilbarg–Trudinger Lemma 7.7; Evans–Gariepy Thm 4.4 (iv)): a weak
gradient vanishes a.e. on the zero set of the function. -/
theorem HasWeakGradient.ae_eq_zero_of_eq_zero {U : Set (E d)} (hU : IsOpen U) {v : E d → ℝ}
    {G : E d → E d} (hv : HasWeakGradient U v G) :
    ∀ᵐ x ∂(volume.restrict U), v x = 0 → G x = 0 := by
  have h := hv.ae_eq_of_eqOn hU hU subset_rfl (hv.posPart_sub_negPart hU) (fun _ _ ↦ rfl)
  filter_upwards [h] with x hx hx0
  rw [hx]
  simp [indicator, hx0]

/-- **Stampacchia's lemma on level sets**: a weak gradient vanishes a.e. on `{v = c}`. -/
theorem HasWeakGradient.ae_eq_zero_of_eq_const {U : Set (E d)} (hU : IsOpen U) {v : E d → ℝ}
    {G : E d → E d} (hv : HasWeakGradient U v G) (c : ℝ) :
    ∀ᵐ x ∂(volume.restrict U), v x = c → G x = 0 := by
  filter_upwards [(hv.sub_const c).ae_eq_zero_of_eq_zero hU] with x hx hxc
  exact hx (by rw [hxc, sub_self])

/-- A representative of the weak gradient that vanishes *pointwise* on `{v = 0}`. -/
theorem HasWeakGradient.exists_modify_zero {U : Set (E d)} (hU : IsOpen U) {v : E d → ℝ}
    {G : E d → E d} (hv : HasWeakGradient U v G) :
    ∃ G' : E d → E d, (∀ᵐ x ∂(volume.restrict U), G' x = G x) ∧ (∀ x, v x = 0 → G' x = 0) ∧
      HasWeakGradient U v G' := by
  refine ⟨{x | v x ≠ 0}.indicator G, ?_, fun x hx ↦ by simp [hx], ?_⟩
  · filter_upwards [hv.ae_eq_zero_of_eq_zero hU] with x hx
    by_cases hx0 : v x = 0
    · simp [hx0, hx hx0]
    · simp [hx0]
  · refine hv.congr_ae ?_
    filter_upwards [hv.ae_eq_zero_of_eq_zero hU] with x hx
    by_cases hx0 : v x = 0
    · simp [hx0, hx hx0]
    · simp [hx0]

/-- `MemH1Loc` version of `HasWeakGradient.exists_modify_zero`. -/
theorem MemH1Loc.exists_modify_zero {U : Set (E d)} (hU : IsOpen U) {v : E d → ℝ}
    {G : E d → E d} (hv : MemH1Loc U v G) :
    ∃ G' : E d → E d, (∀ᵐ x ∂(volume.restrict U), G' x = G x) ∧ (∀ x, v x = 0 → G' x = 0) ∧
      MemH1Loc U v G' := by
  obtain ⟨G', hG', hz, hw⟩ := hv.1.exists_modify_zero hU
  refine ⟨G', hG', hz, hw, fun K hKU hK ↦ ⟨(hv.2 K hKU hK).1, ?_⟩⟩
  refine (hv.2 K hKU hK).2.ae_eq ?_
  have := ae_restrict_of_ae_restrict_of_subset hKU hG'
  filter_upwards [this] with x hx using hx.symm

end EllipticBernoulli
