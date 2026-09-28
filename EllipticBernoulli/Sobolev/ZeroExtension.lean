/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Sobolev.Compactness
public import EllipticBernoulli.Sobolev.Uniqueness

/-!
# Zero extension of compactly supported weak gradients

* `hasWeakGradient_univ_iff`: `HasWeakGradient univ` is local integrability plus
  `HasWeakGradientUniv`.
* `HasWeakGradientUniv.congr_ae`: whole-space weak gradients are insensitive to null sets.
* `gradient_eq_zero_of_eq_one` : a smooth cut-off `0 ≤ ζ ≤ 1` has zero gradient where `ζ = 1`.
* `HasWeakGradient.univ_of_ae_eq_zero`: if `G` is a weak gradient of `v` on the open
  set `U` and `v = 0` a.e. on `U \ K` for a compact `K ⊆ U`, then the zero extensions satisfy
  `HasWeakGradient univ (U.indicator v) (U.indicator G)`.

Proof of the last item: take a cut-off `ζ = 1` on `K` with compact support in `U`
(`exists_smooth_cutoff`). Then `ζ v` has the whole-space weak gradient `ζ G + v ∇ζ`
(`hasWeakGradientUniv_mul_cutoff`), and `ζ v = U.indicator v`, `ζ G + v ∇ζ = U.indicator G` a.e.,
because `v = 0` and (by `HasWeakGradient.ae_eq_zero_of_ae_eq_zero_on`) `G = 0` a.e. on `U \ K`, and
`∇ζ = 0` on `K` (`ζ` attains its maximum there).
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- `HasWeakGradient univ` is local integrability plus the whole-space identity
`HasWeakGradientUniv`. -/
theorem hasWeakGradient_univ_iff {w : E d → ℝ} {Γ : E d → E d} :
    HasWeakGradient univ w Γ ↔
      LocallyIntegrable w ∧ LocallyIntegrable Γ ∧ HasWeakGradientUniv w Γ := by
  simp only [HasWeakGradient, HasWeakGradientUniv, locallyIntegrableOn_univ, Measure.restrict_univ,
    subset_univ, forall_const]

theorem HasWeakGradientUniv.congr_ae {w w' : E d → ℝ} {Γ Γ' : E d → E d}
    (h : HasWeakGradientUniv w Γ) (hw : w =ᵐ[volume] w') (hΓ : Γ =ᵐ[volume] Γ') :
    HasWeakGradientUniv w' Γ' := by
  intro φ hφ hφc v
  have h1 := h φ hφ hφc v
  have e1 : ∫ x, w' x * fderiv ℝ φ x v = ∫ x, w x * fderiv ℝ φ x v :=
    integral_congr_ae (by filter_upwards [hw] with x hx; rw [hx])
  have e2 : ∫ x, inner ℝ (Γ' x) v * φ x = ∫ x, inner ℝ (Γ x) v * φ x :=
    integral_congr_ae (by filter_upwards [hΓ] with x hx; rw [hx])
  rw [e1, e2, h1]

/-- A differentiable `ζ ≤ 1` has zero gradient at every point where `ζ = 1`. -/
theorem gradient_eq_zero_of_eq_one {ζ : E d → ℝ} (hle : ∀ x, ζ x ≤ 1) {x : E d}
    (hx : ζ x = 1) : ∇ ζ x = 0 := by
  have hmax : IsLocalMax ζ x :=
    Filter.Eventually.of_forall fun y ↦ by simpa [hx] using hle y
  simp [gradient, hmax.fderiv_eq_zero]

/-- The gradient of a `C¹` function vanishes off its topological support. -/
theorem gradient_eq_zero_of_notMem_tsupport {ζ : E d → ℝ} {x : E d} (hx : x ∉ tsupport ζ) :
    ∇ ζ x = 0 := by
  have : fderiv ℝ ζ x = 0 := Function.notMem_support.1 fun h ↦ hx (support_fderiv_subset ℝ h)
  simp [gradient, this]

/-- **Zero extension.** If `G` is a weak gradient of `v` on the open set `U`, `K ⊆ U`
is compact and `v = 0` a.e. on `U \ K`, then `U.indicator G` is a weak gradient of
`U.indicator v` on the whole space. -/
theorem HasWeakGradient.univ_of_ae_eq_zero {U K : Set (E d)} (hU : IsOpen U) {v : E d → ℝ}
    {G : E d → E d} (hv : HasWeakGradient U v G) (hK : IsCompact K) (hKU : K ⊆ U)
    (h0 : ∀ᵐ x ∂(volume.restrict (U \ K)), v x = 0) :
    HasWeakGradient univ (U.indicator v) (U.indicator G) := by
  obtain ⟨ζ, hζ, hζc, hζU, hζ01, hζ1⟩ := exists_smooth_cutoff hK hU hKU
  have hUK : MeasurableSet (U \ K) := hU.measurableSet.diff hK.measurableSet
  have hG0 : ∀ᵐ x ∂(volume.restrict (U \ K)), G x = 0 :=
    hv.ae_eq_zero_of_ae_eq_zero_on (hU.sdiff hK.isClosed) diff_subset h0
  rw [ae_restrict_iff' hUK] at h0 hG0
  have hle : ∀ x, ζ x ≤ 1 := fun x ↦ (hζ01 x).2
  have hζout : ∀ x, x ∉ U → ζ x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hζU h)
  have hζout' : ∀ x, x ∉ U → ∇ ζ x = 0 := fun x hx ↦
    gradient_eq_zero_of_notMem_tsupport fun h ↦ hx (hζU h)
  have huniv := hasWeakGradientUniv_mul_cutoff hv hζ hζc hζU
  have e1 : (fun x ↦ ζ x * v x) =ᵐ[volume] U.indicator v := by
    filter_upwards [h0] with x hx
    by_cases hxK : x ∈ K
    · rw [hζ1 x hxK, one_mul, indicator_of_mem (hKU hxK)]
    · by_cases hxU : x ∈ U
      · rw [hx ⟨hxU, hxK⟩, mul_zero, indicator_of_mem hxU, hx ⟨hxU, hxK⟩]
      · rw [hζout x hxU, zero_mul, indicator_of_notMem hxU]
  have e2 : (fun x ↦ ζ x • G x + v x • ∇ ζ x) =ᵐ[volume] U.indicator G := by
    filter_upwards [h0, hG0] with x hx hGx
    by_cases hxK : x ∈ K
    · rw [hζ1 x hxK, gradient_eq_zero_of_eq_one hle (hζ1 x hxK), one_smul, smul_zero, add_zero,
        indicator_of_mem (hKU hxK)]
    · by_cases hxU : x ∈ U
      · rw [hx ⟨hxU, hxK⟩, hGx ⟨hxU, hxK⟩, smul_zero, zero_smul, add_zero, indicator_of_mem hxU,
          hGx ⟨hxU, hxK⟩]
      · rw [hζout x hxU, hζout' x hxU, zero_smul, smul_zero, add_zero, indicator_of_notMem hxU]
  have hT : IsCompact (tsupport ζ) := hζc
  have hi1 : Integrable (fun x ↦ ζ x * v x) := by
    have := integrable_mul_of_locallyIntegrableOn hv.1 hζ.continuous hζc hζU
    simpa only [mul_comm] using this
  have hi2 : Integrable (fun x ↦ ζ x • G x + v x • ∇ ζ x) := by
    have hGT : IntegrableOn G (tsupport ζ) := hv.2.1.integrableOn_compact_subset hζU hT
    have hvT : IntegrableOn v (tsupport ζ) := hv.1.integrableOn_compact_subset hζU hT
    have hcg : Continuous (∇ ζ) := continuous_gradient (hζ.of_le (by simp))
    refine Integrable.add ?_ ?_
    · refine (integrableOn_iff_integrable_of_support_subset ?_).1
        (hGT.continuousOn_smul hζ.continuous.continuousOn hT)
      intro x hx
      by_contra h
      exact hx (by simp [image_eq_zero_of_notMem_tsupport h])
    · refine (integrableOn_iff_integrable_of_support_subset ?_).1
        (hvT.smul_continuousOn_of_subset hcg.continuousOn hT.measurableSet hT subset_rfl)
      intro x hx
      by_contra h
      exact hx (by simp [gradient_eq_zero_of_notMem_tsupport h])
  refine hasWeakGradient_univ_iff.2 ⟨(hi1.congr e1).locallyIntegrable,
    (hi2.congr e2).locallyIntegrable, huniv.congr_ae e1 e2⟩

end EllipticBernoulli
