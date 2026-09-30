/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.Sobolev
public import EllipticBernoulli.Common.Calculus
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Locally Lipschitz functions are `H¹_loc` with weak gradient `∇u`

For `u` locally Lipschitz on an open set `U ⊆ ℝᵈ`, the pointwise gradient `∇u` (which exists a.e.
by Rademacher's theorem and is `0` at points of non-differentiability) is a weak gradient of `u`
in `U`, and `u, ∇u ∈ L²(K)` for every compact `K ⊆ U`.

This file imports only `Basic/*` and Mathlib.

## Main results

* `integral_fderiv_mul_eq_neg`
* `memH1Loc_gradient_of_locallyLipschitzOn`
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped Gradient ContDiff NNReal ENNReal

@[expose] public noncomputable section

namespace EllipticBernoulli

variable {d : ℕ}

/-- A locally bounded-above function is bounded above on compact sets. -/
theorem exists_bound_of_isCompact {X : Type*} [TopologicalSpace X] {f : X → ℝ} {K : Set X}
    (hK : IsCompact K) (h : ∀ p ∈ K, ∃ B, ∀ᶠ q in 𝓝 p, f q ≤ B) :
    ∃ B, ∀ q ∈ K, f q ≤ B := by
  refine hK.induction_on (p := fun s ↦ ∃ B, ∀ q ∈ s, f q ≤ B) ⟨0, fun _ h ↦ h.elim⟩
    (fun s t hst ⟨B, hB⟩ ↦ ⟨B, fun q hq ↦ hB q (hst hq)⟩)
    (fun s t ⟨B, hB⟩ ⟨B', hB'⟩ ↦ ⟨max B B', fun q hq ↦ hq.elim
      (fun h ↦ (hB q h).trans (le_max_left _ _)) (fun h ↦ (hB' q h).trans (le_max_right _ _))⟩)
    fun p hp ↦ ?_
  obtain ⟨B, hB⟩ := h p hp
  exact ⟨{q | f q ≤ B}, mem_nhdsWithin_of_mem_nhds hB, ⟨B, fun q hq ↦ hq⟩⟩

/-- A locally Lipschitz function on the open set `U` has bounded derivative on compact subsets
of `U`. -/
theorem exists_bound_fderiv_of_locallyLipschitzOn {U : Set (E d)} {f : E d → ℝ} (hU : IsOpen U)
    (hf : LocallyLipschitzOn U f) {V : Set (E d)} (hV : IsCompact V) (hVU : V ⊆ U) :
    ∃ C, ∀ x ∈ V, ‖fderiv ℝ f x‖ ≤ C := by
  refine exists_bound_of_isCompact hV fun x hx ↦ ?_
  obtain ⟨K, t, ht, hK⟩ := hf (hVU hx)
  obtain ⟨o, ho, hot⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 ht
  have hn : o ∩ U ∈ 𝓝 x := inter_mem ho (hU.mem_nhds (hVU hx))
  exact ⟨K, (eventually_mem_nhds_iff.2 hn).mono fun y hy ↦
    norm_fderiv_le_of_lipschitzOn ℝ hy (hK.mono hot)⟩

/-- **Integration by parts** for `f` locally Lipschitz on the open set `U` and `φ ∈ C¹_c(U)`:
`∫_U ∂ᵥf φ = -∫_U f ∂ᵥφ` (McShane extension of `f` from a compact neighbourhood of `spt φ`, then
`LipschitzWith.integral_lineDeriv_mul_eq`). -/
theorem integral_fderiv_mul_eq_neg {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ}
    (hf : LocallyLipschitzOn U f) {φ : E d → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ U) (v : E d) :
    ∫ x in U, fderiv ℝ f x v * φ x = -∫ x in U, f x * fderiv ℝ φ x v := by
  obtain ⟨δ, hδ, hδU⟩ := hφc.isCompact.exists_cthickening_subset_open hU hφU
  set V := cthickening δ (tsupport φ)
  have hVc : IsCompact V := hφc.isCompact.cthickening
  obtain ⟨K, hK⟩ := (hf.mono hδU).exists_lipschitzOnWith_of_compact hVc
  obtain ⟨g, hg, hfg⟩ := hK.extend_real
  have hW : thickening δ (tsupport φ) ⊆ V := thickening_subset_cthickening _ _
  have hfd : ∀ x ∈ tsupport φ, fderiv ℝ f x = fderiv ℝ g x := fun x hx ↦
    Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem
      (isOpen_thickening.mem_nhds (self_subset_thickening hδ _ hx)) (hfg.mono hW))
  obtain ⟨Kφ, hKφ⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc one_ne_zero
  have hvan1 : ∀ x ∉ tsupport φ, fderiv ℝ f x v * φ x = 0 := fun x hx ↦ by
    simp [image_eq_zero_of_notMem_tsupport hx]
  have hvan2 : ∀ x ∉ tsupport φ, f x * fderiv ℝ φ x v = 0 := fun x hx ↦ by
    simp [fderiv_of_notMem_tsupport ℝ hx]
  have e1 : ∫ x in U, fderiv ℝ f x v * φ x = ∫ x, lineDeriv ℝ g x v * φ x := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
      hvan1 x fun h ↦ hx (hφU h)]
    refine integral_congr_ae ?_
    filter_upwards [hg.ae_differentiableAt] with x hx
    by_cases hxs : x ∈ tsupport φ
    · rw [hx.lineDeriv_eq_fderiv, hfd x hxs]
    · simp [image_eq_zero_of_notMem_tsupport hxs]
  have e2 : ∫ x in U, f x * fderiv ℝ φ x v = ∫ x, g x * fderiv ℝ φ x v := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
      hvan2 x fun h ↦ hx (hφU h)]
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    by_cases hxs : x ∈ tsupport φ
    · simp only
      rw [hfg (self_subset_cthickening _ hxs)]
    · simp [fderiv_of_notMem_tsupport ℝ hxs]
  rw [e1, e2, LipschitzWith.integral_lineDeriv_mul_eq hg hKφ hφc v, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  have hd : DifferentiableAt ℝ φ x := hφ.differentiable one_ne_zero x
  simp only [hd.lineDeriv_eq_fderiv, map_neg]
  ring

/-- `⟨∇u(x), v⟩ = Du(x) v` (both sides vanish where `u` is not differentiable). -/
theorem inner_gradient_left_eq_fderiv (u : E d → ℝ) (x v : E d) :
    inner ℝ (∇ u x) v = fderiv ℝ u x v := by
  rw [gradient, toDual_symm_apply]

theorem measurable_gradient (u : E d → ℝ) : Measurable (∇ u) :=
  (toDual ℝ (E d)).symm.continuous.measurable.comp (measurable_fderiv ℝ u)

/-- A function continuous on a compact set `K` is in `L²(K)`. -/
theorem memLp_two_restrict_of_continuousOn {K : Set (E d)} (hK : IsCompact K) {u : E d → ℝ}
    (hu : ContinuousOn u K) : MemLp u 2 (volume.restrict K) := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hu
  exact MemLp.of_bound (hu.aestronglyMeasurable_of_isCompact hK hK.measurableSet) C
    ((ae_restrict_mem hK.measurableSet).mono hC)

/-- For `u` locally Lipschitz on the open set `U` and `K ⊆ U` compact, `∇u ∈ L²(K)`. -/
theorem memLp_two_restrict_gradient {U : Set (E d)} (hU : IsOpen U) {u : E d → ℝ}
    (hu : LocallyLipschitzOn U u) {K : Set (E d)} (hK : IsCompact K) (hKU : K ⊆ U) :
    MemLp (∇ u) 2 (volume.restrict K) := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  obtain ⟨C, hC⟩ := exists_bound_fderiv_of_locallyLipschitzOn hU hu hK hKU
  refine MemLp.of_bound (measurable_gradient u).aestronglyMeasurable C
    ((ae_restrict_mem hK.measurableSet).mono fun x hx ↦ ?_)
  rw [norm_gradient_eq_norm_fderiv]
  exact hC x hx

/-- A locally Lipschitz function `u` on the open set `U ⊆ ℝᵈ` belongs to `H¹_loc(U)`
with weak gradient the pointwise gradient `∇u` (Evans–Gariepy, Thm 4.5). -/
theorem memH1Loc_gradient_of_locallyLipschitzOn {U : Set (E d)} {u : E d → ℝ} (hU : IsOpen U)
    (hu : LocallyLipschitzOn U u) : MemH1Loc U u (∇ u) := by
  have hL2 : ∀ K ⊆ U, IsCompact K →
      MemLp u 2 (volume.restrict K) ∧ MemLp (∇ u) 2 (volume.restrict K) := fun K hKU hK ↦
    ⟨memLp_two_restrict_of_continuousOn hK (hu.continuousOn.mono hKU),
      memLp_two_restrict_gradient hU hu hK hKU⟩
  have hint : ∀ {F : Type _} [NormedAddCommGroup F] {g : E d → F},
      (∀ K ⊆ U, IsCompact K → MemLp g 2 (volume.restrict K)) → LocallyIntegrableOn g U := by
    intro F _ g hg
    refine (locallyIntegrableOn_iff hU.isLocallyClosed).2 fun K hKU hK ↦ ?_
    have : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    exact (hg K hKU hK).integrable one_le_two
  refine ⟨⟨hint fun K hKU hK ↦ (hL2 K hKU hK).1, hint fun K hKU hK ↦ (hL2 K hKU hK).2,
    fun φ hφ hφc hφU v ↦ ?_⟩, hL2⟩
  have h := integral_fderiv_mul_eq_neg hU hu (hφ.of_le (by simp)) hφc hφU v
  simp_rw [inner_gradient_left_eq_fderiv]
  rw [h, neg_neg]

/-- A `C¹` function belongs to `H¹_loc(U)` with weak gradient its gradient (new in this repository;
a corollary of `memH1Loc_gradient_of_locallyLipschitzOn`). -/
theorem memH1Loc_gradient_of_contDiff {U : Set (E d)} {u : E d → ℝ} (hU : IsOpen U)
    (hu : ContDiff ℝ 1 u) : MemH1Loc U u (∇ u) :=
  memH1Loc_gradient_of_locallyLipschitzOn hU hu.locallyLipschitz.locallyLipschitzOn

end EllipticBernoulli
