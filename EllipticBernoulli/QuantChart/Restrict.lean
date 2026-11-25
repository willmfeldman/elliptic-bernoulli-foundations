/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Variational
import EllipticBernoulli.Sobolev.Lattice
import EllipticBernoulli.Sobolev.ZeroExtension
import EllipticBernoulli.Sobolev.Energy

/-!
# Restricting local energy minimizers to open subsets

`IsLocalEnergyMinimizer.mono`: a local minimizer of `J_Q` in an open `U` is a local minimizer in
every open `V ⊆ U`.

A competitor `v` for a ball `B ⋐ V` is turned into a competitor in `U` by
`w = u + 1_V (v - u)`. The function `v - u` vanishes a.e. on `V \ B̄`, so its extension by zero has
the extended weak gradient on the whole space (`HasWeakGradient.univ_of_ae_eq_zero`). On `B`,
`w = v` with the same weak gradient.
-/

open Set Filter Topology MeasureTheory Metric

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- Weak gradients restrict to open subsets. -/
theorem HasWeakGradient.mono_set {U V : Set (E d)} (hVU : V ⊆ U) {f : E d → ℝ} {F : E d → E d}
    (hf : HasWeakGradient U f F) : HasWeakGradient V f F :=
  HasWeakGradient.of_integral_eq (hf.1.mono_set hVU) (hf.2.1.mono_set hVU)
    fun _ hφ hφc hφV v ↦ hf.integral_eq hφ hφc (hφV.trans hVU) v

/-- **Restricting local energy minimizers to open subsets.** -/
theorem IsLocalEnergyMinimizer.mono {U V : Set (E d)} (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U)
    {Q u : E d → ℝ} (hmin : IsLocalEnergyMinimizer U Q u) : IsLocalEnergyMinimizer V Q u := by
  obtain ⟨Gu, hGu, hm⟩ := hmin
  have hGuV : MemH1Loc V u Gu := ⟨hGu.1.mono_set hVU, fun K hKV hK ↦ hGu.2 K (hKV.trans hVU) hK⟩
  refine ⟨Gu, hGuV, fun x r hr hB ↦ ⟨hGuV, fun _ _ ↦ rfl, fun _ _ ↦ mem_univ _,
    fun v Gv hv hvout _ ↦ ?_⟩⟩
  set f : E d → ℝ := fun y ↦ v y - u y with hfdef
  set F : E d → E d := fun y ↦ Gv y - Gu y with hFdef
  have hf : HasWeakGradient V f F := hv.1.sub hGuV.1
  have hsubV : V \ closedBall x r ⊆ V \ ball x r := sdiff_subset_sdiff_right ball_subset_closedBall
  have hf0 : ∀ᵐ y ∂(volume.restrict (V \ closedBall x r)), f y = 0 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsubV hvout] with y hy
    simp [hfdef, hy]
  have hext := hf.univ_of_ae_eq_zero hV (isCompact_closedBall x r) hB hf0
  set w : E d → ℝ := fun y ↦ u y + V.indicator f y with hw
  set Gw : E d → E d := fun y ↦ Gu y + V.indicator F y with hGw
  -- `1_V f = 1_{B̄} f` and `1_V F = 1_{B̄} F` a.e.
  have hcl : MeasurableSet (closedBall x r) := measurableSet_closedBall
  have hae : V.indicator f =ᵐ[volume] (closedBall x r).indicator f := by
    have h1 := (ae_restrict_iff' (hV.measurableSet.diff hcl)).1 hf0
    filter_upwards [h1] with y hy
    by_cases hyB : y ∈ closedBall x r
    · rw [indicator_of_mem (hB hyB), indicator_of_mem hyB]
    · rw [indicator_of_notMem hyB]
      by_cases hyV : y ∈ V
      · rw [indicator_of_mem hyV]; exact hy ⟨hyV, hyB⟩
      · rw [indicator_of_notMem hyV]
  have haeF : V.indicator F =ᵐ[volume] (closedBall x r).indicator F := by
    have hG0 := hf.ae_eq_zero_of_ae_eq_zero_on (O := V \ closedBall x r)
      (hV.sdiff isClosed_closedBall) sdiff_subset hf0
    have h1 := (ae_restrict_iff' (hV.measurableSet.diff hcl)).1 hG0
    filter_upwards [h1] with y hy
    by_cases hyB : y ∈ closedBall x r
    · rw [indicator_of_mem (hB hyB), indicator_of_mem hyB]
    · rw [indicator_of_notMem hyB]
      by_cases hyV : y ∈ V
      · rw [indicator_of_mem hyV]; exact hy ⟨hyV, hyB⟩
      · rw [indicator_of_notMem hyV]
  -- `w ∈ H¹_loc(U)`
  have hfB : MemLp f 2 (volume.restrict (closedBall x r)) :=
    (hv.2 _ hB (isCompact_closedBall x r)).1.sub (hGuV.2 _ hB (isCompact_closedBall x r)).1
  have hFB : MemLp F 2 (volume.restrict (closedBall x r)) :=
    (hv.2 _ hB (isCompact_closedBall x r)).2.sub (hGuV.2 _ hB (isCompact_closedBall x r)).2
  have hwU : MemH1Loc U w Gw := by
    refine ⟨hGu.1.add (hext.mono_set (subset_univ U)), fun K hKU hK ↦ ⟨?_, ?_⟩⟩
    · refine (hGu.2 K hKU hK).1.add ?_
      have : MemLp ((closedBall x r).indicator f) 2 volume :=
        (memLp_indicator_iff_restrict hcl.nullMeasurableSet).2 hfB
      exact (this.restrict K).ae_eq (ae_restrict_of_ae hae.symm)
    · refine (hGu.2 K hKU hK).2.add ?_
      have : MemLp ((closedBall x r).indicator F) 2 volume :=
        (memLp_indicator_iff_restrict hcl.nullMeasurableSet).2 hFB
      exact (this.restrict K).ae_eq (ae_restrict_of_ae haeF.symm)
  -- `w = u` off the ball
  have hwout : ∀ᵐ y ∂(volume.restrict (U \ ball x r)), w y = u y := by
    rw [ae_restrict_iff' (hU.measurableSet.diff measurableSet_ball)]
    have h2 := (ae_restrict_iff' (hV.measurableSet.diff measurableSet_ball)).1 hvout
    filter_upwards [h2] with y hy hyU
    simp only [hw]
    by_cases hyV : y ∈ V
    · rw [indicator_of_mem hyV]; simp [hfdef, hy ⟨hyV, hyU.2⟩]
    · rw [indicator_of_notMem hyV, add_zero]
  have hle := (hm x r hr (hB.trans hVU)).2.2.2 w Gw hwU hwout (ae_of_all _ fun _ ↦ mem_univ _)
  refine hle.trans (le_of_eq (energyJ_congr (fun y hy ↦ ?_)
    (ae_restrict_of_forall_mem measurableSet_ball fun y hy ↦ ?_)))
  · have hyV : y ∈ V := hB (ball_subset_closedBall hy)
    simp [hw, hfdef, indicator_of_mem hyV]
  · have hyV : y ∈ V := hB (ball_subset_closedBall hy)
    simp [hGw, hFdef, indicator_of_mem hyV]

end EllipticBernoulli
