/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.QuantChart.LocalChart
public import EllipticBernoulli.QuantChart.Glue
import EllipticBernoulli.Variational.OneSided
import EllipticBernoulli.Viscosity.Basic
import EllipticBernoulli.Viscosity.Harmonic
import EllipticBernoulli.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian

/-!
# A smooth chart on `B_{1/2}` for a flat minimizer

`exists_glued_chart_of_flat`: for `d ≥ 2` there is `ε₁ > 0` such that a continuous, non-negative
local minimizer `u` of `J` in `B_1` with `|u - (x · e)₊| ≤ ε ≤ ε₁` on `B_1` is `max(F, 0)` on
`B_{1/2}` for some `F ∈ C^∞(ℝᵈ)`. Moreover, `F = u` near every point of `{u > 0} ∩ B_{1/2}`,
`|∇F| = 1` on `{F = 0} ∩ B_{1/2}`, `ΔF = 0` on `{F > 0} ∩ B_{1/2}`, and `{F ≥ 0} ∩ B_{1/2}` lies in
the closure of `{u > 0} ∩ B_{1/2}`.

So every derivative bound on `F` over `{F ≥ 0} ∩ B_{1/2}` reduces to the same bound for `u` on
`{u > 0} ∩ B_{1/2}` (`norm_iteratedFDeriv_le_of_glued`).

The local charts are: `u` itself on `{u > 0}` (harmonic, hence smooth), the constant `-1` off
the closure of `{u > 0}`, and the charts of `exists_chart_of_flat` at free-boundary points of
`B̄_{1/2}`.
`exists_contDiff_glued_chart` glues them on `B̄_{1/2}`.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient RealInnerProductSpace Laplacian

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- **A smooth chart on `B_{1/2}` for a flat minimizer.** -/
theorem exists_glued_chart_of_flat (hd : 2 ≤ d) : ∃ ε₁ > 0, ∀ {u : E d → ℝ} {e : E d} {ε : ℝ},
    ContinuousOn u (ball 0 1) → (∀ x ∈ ball (0 : E d) 1, 0 ≤ u x) →
    IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u → ‖e‖ = 1 → ε ≤ ε₁ →
    (∀ x ∈ ball (0 : E d) 1, |u x - max ⟪x, e⟫ 0| ≤ ε) →
    ∃ F : E d → ℝ, ContDiff ℝ ∞ F ∧ (∀ y ∈ ball (0 : E d) (1 / 2), u y = max (F y) 0) ∧
      (∀ y ∈ ball (0 : E d) (1 / 2), 0 < u y → F =ᶠ[𝓝 y] u) ∧
      (∀ y ∈ ball (0 : E d) (1 / 2), F y = 0 → ‖∇ F y‖ = 1) ∧
      (∀ y ∈ ball (0 : E d) (1 / 2), 0 < F y → Δ F y = 0) ∧
      (∀ y ∈ ball (0 : E d) (1 / 2), 0 ≤ F y →
        y ∈ closure {z | z ∈ ball (0 : E d) (1 / 2) ∧ 0 < u z}) := by
  obtain ⟨ε₁, hε₁, H⟩ := exists_chart_of_flat hd
  refine ⟨ε₁, hε₁, fun {u e ε} hc hnn hmin he hεle hflat ↦ ?_⟩
  set U := ball (0 : E d) 1 with hUdef
  have hvisc : IsViscSolution U (fun _ ↦ 1) u :=
    IsLocalEnergyMinimizer.isViscSolution isOpen_ball continuousOn_const
      (fun _ _ ↦ zero_le_one) hc hnn hmin
  have hH : HarmonicOnNhd u (posSet u U) := IsViscSolution.harmonicOnNhd_posSet isOpen_ball hvisc
  have hP : IsOpen (posSet u U) := isOpen_posSet isOpen_ball hc
  have hsU : closedBall (0 : E d) (1 / 2) ⊆ U := closedBall_subset_ball (by norm_num)
  have hloc : ∀ x ∈ closedBall (0 : E d) (1 / 2), ∃ W : Set (E d), IsOpen W ∧ x ∈ W ∧
      ∃ G : E d → ℝ, ContDiffOn ℝ ∞ G W ∧ (∀ y ∈ W, u y = max (G y) 0) ∧
        (∀ y ∈ W, G y = 0 → ‖∇ G y‖ = 1) := by
    intro x hx
    have hxU := hsU hx
    rcases (hnn x hxU).lt_or_eq with hpos | hzero
    · -- the positive phase: `G = u`
      refine ⟨posSet u U, hP, ⟨hxU, hpos⟩, u, HarmonicOnNhd.contDiffOn_top hP hH,
        fun y hy ↦ (max_eq_left hy.2.le).symm, fun y hy h0 ↦ absurd h0 hy.2.ne'⟩
    · by_cases hcl : x ∈ closure (posSet u U)
      · -- a free-boundary point
        have hxFB : x ∈ freeBoundary u U := by
          refine ⟨⟨hcl, fun hint ↦ ?_⟩, hxU⟩
          rw [hP.interior_eq] at hint
          exact (lt_irrefl _ (hzero ▸ hint.2))
        have hx2 : ‖x‖ ≤ 1 / 2 := by simpa using hx
        obtain ⟨ρ, hρ, -, F, hF, hFu, -, hFn, -⟩ := H hc hnn hmin he hεle hflat x hxFB hx2
        exact ⟨ball x ρ, isOpen_ball, mem_ball_self hρ, F, hF, hFu, hFn⟩
      · -- off the closure of the positive phase: `G = -1`
        refine ⟨(closure (posSet u U))ᶜ ∩ U, isClosed_closure.isOpen_compl.inter isOpen_ball,
          ⟨hcl, hxU⟩, (fun _ ↦ (-1 : ℝ)), contDiffOn_const, (fun y hy ↦ ?_),
          (fun y _ h ↦ absurd h (by norm_num))⟩
        have hy0 : u y = 0 := by
          by_contra hne
          exact hy.1 (subset_closure ⟨hy.2, lt_of_le_of_ne (hnn y hy.2) (Ne.symm hne)⟩)
        rw [hy0]; norm_num
  obtain ⟨F, hF, hFu, hFloc, hFn, hFcl⟩ := exists_contDiff_glued_chart isClosed_closedBall hloc
  rw [interior_closedBall _ (by norm_num : (1 / 2 : ℝ) ≠ 0)] at hFloc hFn hFcl
  refine ⟨F, hF, fun y hy ↦ hFu y (ball_subset_closedBall hy), hFloc, hFn,
    fun y hy hpos ↦ ?_, hFcl⟩
  have huy : 0 < u y := by
    rw [hFu y (ball_subset_closedBall hy)]; exact lt_max_of_lt_left hpos
  rw [(laplacian_congr_nhds (hFloc y hy huy)).self_of_nhds]
  exact (hH y ⟨hsU (ball_subset_closedBall hy), huy⟩).2.self_of_nhds

/-- **Bounds on `{F ≥ 0}` from bounds on `{u > 0}`.** In the setting of
`exists_glued_chart_of_flat`: if `‖D^k u‖ ≤ M` on `{u > 0} ∩ B_ρ` for some `ρ ≤ 1/2`, then
`‖D^k F‖ ≤ M` on `{F ≥ 0} ∩ B_ρ`. -/
theorem norm_iteratedFDeriv_le_of_glued {u F : E d → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFloc : ∀ y ∈ ball (0 : E d) (1 / 2), 0 < u y → F =ᶠ[𝓝 y] u)
    (hFcl : ∀ y ∈ ball (0 : E d) (1 / 2), 0 ≤ F y →
      y ∈ closure {z | z ∈ ball (0 : E d) (1 / 2) ∧ 0 < u z})
    {ρ : ℝ} (hρ : ρ ≤ 1 / 2) (k : ℕ) {M : ℝ}
    (hM : ∀ z ∈ ball (0 : E d) ρ, 0 < u z → ‖iteratedFDeriv ℝ k u z‖ ≤ M) :
    ∀ y ∈ ball (0 : E d) ρ, 0 ≤ F y → ‖iteratedFDeriv ℝ k F y‖ ≤ M := by
  intro y hy hFy
  have hy2 : y ∈ ball (0 : E d) (1 / 2) := ball_subset_ball hρ hy
  have hcl : y ∈ closure {z | z ∈ ball (0 : E d) ρ ∧ 0 < u z} := by
    have h := hFcl y hy2 hFy
    rw [mem_closure_iff_nhds] at h ⊢
    intro t ht
    obtain ⟨z, hzt, hz⟩ := h (t ∩ ball 0 ρ) (inter_mem ht (isOpen_ball.mem_nhds hy))
    exact ⟨z, hzt.1, hzt.2, hz.2⟩
  have hcont : Continuous fun z ↦ ‖iteratedFDeriv ℝ k F z‖ :=
    (hF.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  refine ContinuousWithinAt.closure_le (f := fun z ↦ ‖iteratedFDeriv ℝ k F z‖)
    (g := fun _ ↦ M) hcl hcont.continuousWithinAt continuousWithinAt_const ?_
  intro z hz
  have hz2 : z ∈ ball (0 : E d) (1 / 2) := ball_subset_ball hρ hz.1
  rw [(hFloc z hz2 hz.2).iteratedFDeriv ℝ k |>.self_of_nhds]
  exact hM z hz.1 hz.2

end EllipticBernoulli
