/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Basic.Setting
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Gluing one-sided charts

Let `s ⊆ ℝᵈ` be closed and let `u : ℝᵈ → ℝ`. Suppose every `x ∈ s` has an open neighbourhood `W`
with a smooth `G` on `W` such that `u = max(G, 0)` on `W` and `|∇G| = 1` on `{G = 0} ∩ W`. Then a
smooth partition of unity glues the local `G`s into one `F ∈ C^∞(ℝᵈ)`
(`exists_contDiff_glued_chart`):

* `u = max(F, 0)` on `s`;
* `F = u` near every point of `interior s` where `u > 0`;
* `|∇F| = 1` at points of `interior s` where `F = 0`;
* every point of `interior s` where `F ≥ 0` is in the closure of `{u > 0} ∩ interior s`.

Where `u > 0`, every local `G` equals `u`; where `u = 0`, every local `G` is `≤ 0`. So the convex
combination `F = Σ ρᵢ Gᵢ` equals `u`, resp. is `≤ 0`. At a point of `{F = 0}`, a chart `G` with
`ρ > 0` there vanishes, and `F = G` on the open set `{G > 0}`, which accumulates at the point
because `∇G ≠ 0`. Continuity of the derivatives then gives `∇F = ∇G` there.

`eq_of_eqOn_of_mem_closure` is the continuity step used to transfer pointwise identities and
bounds from `{u > 0}` to its closure.
-/

open Set Filter Topology Metric
open scoped ContDiff Gradient Manifold

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- Two functions continuous at `y` that agree on a set `O` with `y ∈ closure O` agree at `y`. -/
theorem eq_of_eqOn_of_mem_closure {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f g : X → Y} {O : Set X} {y : X} (hy : y ∈ closure O) (hf : ContinuousAt f y)
    (hg : ContinuousAt g y) (hfg : EqOn f g O) : f y = g y := by
  have := mem_closure_iff_nhdsWithin_neBot.1 hy
  exact tendsto_nhds_unique ((hf.tendsto.mono_left nhdsWithin_le_nhds).congr'
    (eventuallyEq_nhdsWithin_of_eqOn hfg)) (hg.tendsto.mono_left nhdsWithin_le_nhds)

/-- A function on an open `W` with `g(y) = 0` and `∇g(y) ≠ 0` takes positive values in every
neighbourhood of `y`. -/
theorem mem_closure_pos_of_gradient_ne_zero {g : E d → ℝ} {W : Set (E d)} (hW : IsOpen W)
    {y : E d} (hyW : y ∈ W) (hgy : g y = 0) (hgrad : ∇ g y ≠ 0)
    {N : Set (E d)} (hN : N ∈ 𝓝 y) : y ∈ closure {z | z ∈ N ∩ W ∧ 0 < g z} := by
  rw [mem_closure_iff_nhds]
  intro t ht
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hmax : IsLocalMax g y := by
    filter_upwards [inter_mem (inter_mem ht hN) (hW.mem_nhds hyW)] with z hz
    rw [hgy]
    by_contra hpos
    push Not at hpos
    have : z ∈ t ∩ {z | z ∈ N ∩ W ∧ 0 < g z} := ⟨hz.1.1, ⟨hz.1.2, hz.2⟩, hpos⟩
    rw [hne] at this
    exact this
  apply hgrad
  rw [gradient, hmax.fderiv_eq_zero, map_zero]

/-- **Gluing one-sided charts.** -/
theorem exists_contDiff_glued_chart {s : Set (E d)} (hs : IsClosed s) {u : E d → ℝ}
    (hloc : ∀ x ∈ s, ∃ W : Set (E d), IsOpen W ∧ x ∈ W ∧ ∃ G : E d → ℝ, ContDiffOn ℝ ∞ G W ∧
      (∀ y ∈ W, u y = max (G y) 0) ∧ (∀ y ∈ W, G y = 0 → ‖∇ G y‖ = 1)) :
    ∃ F : E d → ℝ, ContDiff ℝ ∞ F ∧ (∀ y ∈ s, u y = max (F y) 0) ∧
      (∀ y ∈ interior s, 0 < u y → F =ᶠ[𝓝 y] u) ∧
      (∀ y ∈ interior s, F y = 0 → ‖∇ F y‖ = 1) ∧
      (∀ y ∈ interior s, 0 ≤ F y → y ∈ closure {z | z ∈ interior s ∧ 0 < u z}) := by
  choose W hWo hxW G hG hGu hGn using hloc
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E d) hs
    (fun i : s ↦ W i i.2) (fun i ↦ hWo _ _) fun x hx ↦ mem_iUnion.2 ⟨⟨x, hx⟩, hxW x hx⟩
  set F : E d → ℝ := fun y ↦ ∑ᶠ i : s, ρ i y • G i i.2 y with hF
  -- smoothness
  have hFs : ContDiff ℝ ∞ F := by
    rw [← contMDiff_iff_contDiff]
    refine ρ.contMDiff_finsum_smul fun i x hx ↦ ?_
    have hxW' : x ∈ W i i.2 := hρ i hx
    exact ((hG i i.2).contDiffAt ((hWo i i.2).mem_nhds hxW')).contMDiffAt
  -- where `ρ i y ≠ 0`, `y` is in the chart domain
  have hmemW : ∀ (i : s) (y : E d), ρ i y ≠ 0 → y ∈ W i i.2 := fun i y h ↦
    hρ i (subset_tsupport _ h)
  have hfin : ∀ y, (Function.support fun i : s ↦ ρ i y).Finite := fun y ↦
    ρ.locallyFinite.point_finite y
  -- the sum as a finite sum
  have hFsum : ∀ y, F y = ∑ i ∈ (hfin y).toFinset, ρ i y * G i i.2 y := fun y ↦ by
    rw [hF]
    simp only [smul_eq_mul]
    refine finsum_eq_sum_of_support_subset _ fun i hi ↦ ?_
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    exact left_ne_zero_of_mul hi
  have hsum1 : ∀ y ∈ s, ∑ i ∈ (hfin y).toFinset, ρ i y = 1 := fun y hy ↦ by
    rw [← ρ.sum_eq_one hy]
    exact (finsum_eq_sum_of_support_subset _ (by simp)).symm
  -- `u ≥ 0` on `s`
  have hu0 : ∀ y ∈ s, 0 ≤ u y := fun y hy ↦ by rw [hGu y hy y (hxW y hy)]; exact le_max_right _ _
  -- `F = u` where `u > 0`
  have hFu : ∀ y ∈ s, 0 < u y → F y = u y := by
    intro y hy hpos
    rw [hFsum, ← mul_one (u y), ← hsum1 y hy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases h : ρ i y = 0
    · simp [h]
    · have hu := hGu i i.2 y (hmemW i y h)
      have : G i i.2 y = u y := by
        by_contra hne
        rw [max_def] at hu
        split_ifs at hu with h1
        · linarith
        · exact hne hu.symm
      rw [this, mul_comm]
  -- `F ≤ 0` where `u = 0`; and every active chart vanishes where `F = 0`
  have hGle : ∀ y (i : s), u y = 0 → ρ i y ≠ 0 → G i i.2 y ≤ 0 := fun y i hu h ↦ by
    have := hGu i i.2 y (hmemW i y h)
    rw [hu] at this
    exact (le_max_left _ _).trans this.symm.le
  have hterm : ∀ y (i : s), u y = 0 → ρ i y * G i i.2 y ≤ 0 := fun y i hu ↦ by
    by_cases h : ρ i y = 0
    · simp [h]
    · exact mul_nonpos_of_nonneg_of_nonpos (ρ.nonneg i y) (hGle y i hu h)
  have hFle : ∀ y, u y = 0 → F y ≤ 0 := fun y hu ↦ by
    rw [hFsum]; exact Finset.sum_nonpos fun i _ ↦ hterm y i hu
  have hmax : ∀ y ∈ s, u y = max (F y) 0 := by
    intro y hy
    rcases (hu0 y hy).lt_or_eq with hpos | hzero
    · rw [hFu y hy hpos, max_eq_left hpos.le]
    · rw [← hzero, max_eq_right (hFle y hzero.symm)]
  -- `u` is continuous on `s`
  have hucont : ∀ y ∈ s, ContinuousAt u y := fun y hy ↦ by
    have hc : ContinuousAt (fun z ↦ max (G y hy z) 0) y :=
      (((hG y hy).continuousOn.continuousAt ((hWo y hy).mem_nhds (hxW y hy))).max
        continuousAt_const)
    exact hc.congr (Filter.eventuallyEq_of_mem ((hWo y hy).mem_nhds (hxW y hy))
      fun z hz ↦ (hGu y hy z hz).symm)
  have hloc' : ∀ y ∈ interior s, 0 < u y → F =ᶠ[𝓝 y] u := by
    intro y hy hpos
    have hys := interior_subset hy
    filter_upwards [isOpen_interior.mem_nhds hy, (hucont y hys).eventually (lt_mem_nhds hpos)]
      with z hz hzpos
    exact hFu z (interior_subset hz) hzpos
  -- the zero set
  have hzero : ∀ y ∈ interior s, F y = 0 →
      ‖∇ F y‖ = 1 ∧ y ∈ closure {z | z ∈ interior s ∧ 0 < u z} := by
    intro y hy hFy
    have hys := interior_subset hy
    have huy : u y = 0 := by rw [hmax y hys, hFy, max_self]
    obtain ⟨i₀, hi₀⟩ := ρ.exists_pos_of_mem hys
    have hyW := hmemW i₀ y hi₀.ne'
    set g := G i₀ i₀.2 with hg
    have hgy : g y = 0 := by
      have hall := (Finset.sum_eq_zero_iff_of_nonpos fun i _ ↦ hterm y i huy).1
        ((hFsum y).symm.trans hFy)
      have h0 := hall i₀ (by simp [hi₀.ne'])
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h hi₀.ne'
      · exact h
    have hgn := hGn i₀ i₀.2 y hyW hgy
    have hcl := mem_closure_pos_of_gradient_ne_zero (hWo _ _) hyW hgy
      (by rw [← norm_ne_zero_iff, hgn]; exact one_ne_zero) (isOpen_interior.mem_nhds hy)
    -- on `{g > 0}`, `F = g` near each point
    have hFg : ∀ z ∈ {z | z ∈ interior s ∩ W i₀ i₀.2 ∧ 0 < g z}, F =ᶠ[𝓝 z] g := by
      intro z hz
      have hzu : 0 < u z := by rw [hGu i₀ i₀.2 z hz.1.2]; exact lt_max_of_lt_left hz.2
      have hgcont : ContinuousAt g z :=
        (hG i₀ i₀.2).continuousOn.continuousAt ((hWo _ _).mem_nhds hz.1.2)
      filter_upwards [hloc' z hz.1.1 hzu, (hWo _ _).mem_nhds hz.1.2,
        hgcont.eventually (lt_mem_nhds hz.2)] with w hw1 hw2 hw3
      rw [hw1, hGu i₀ i₀.2 w hw2, max_eq_left hw3.le]
    have hcontF : ContinuousAt (fderiv ℝ F) y :=
      (hFs.continuous_fderiv (by simp)).continuousAt
    have hcontg : ContinuousAt (fderiv ℝ g) y :=
      ((hG i₀ i₀.2).continuousOn_fderiv_of_isOpen (hWo _ _) (by simp)).continuousAt
        ((hWo _ _).mem_nhds hyW)
    have hder : fderiv ℝ F y = fderiv ℝ g y :=
      eq_of_eqOn_of_mem_closure hcl hcontF hcontg fun z hz ↦ (hFg z hz).fderiv_eq
    refine ⟨by rw [gradient, hder, ← gradient, hgn], closure_mono (fun z hz ↦ ?_) hcl⟩
    exact ⟨hz.1.1, by rw [hGu i₀ i₀.2 z hz.1.2]; exact lt_max_of_lt_left hz.2⟩
  refine ⟨F, hFs, hmax, hloc', fun y hy hFy ↦ (hzero y hy hFy).1, fun y hy hFy ↦ ?_⟩
  rcases hFy.lt_or_eq with hpos | h0
  · refine subset_closure ⟨hy, ?_⟩
    rw [hmax y (interior_subset hy)]; exact lt_max_of_lt_left hpos
  · exact (hzero y hy h0.symm).2

end EllipticBernoulli
