/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.QuantChart
import EllipticBernoulli.QuantChart.Chart
import EllipticBernoulli.QuantChart.Core

/-!
# The third-derivative bound at a flat free boundary

`quantFlatChartThree : QuantFlatChartThreeStatement`. The chart `F` is the glued chart of
`exists_glued_chart_of_flat`. On `{F ≥ 0} ∩ B_{1/4}` its derivatives are limits of those of `u`
on `{u > 0} ∩ B_{1/4}`. There `‖D³u‖ ≤ C₀` (`exists_norm_iteratedFDeriv_le_of_flat`) and
`‖∇u - e‖ ≤ C ε ≤ 1/2` (`exists_norm_gradient_sub_le_of_flat_quarter`).
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient RealInnerProductSpace Laplacian

public section

namespace EllipticBernoulli

/-- **The third-derivative bound at a flat free boundary** (`QuantFlatChartThreeStatement`). -/
theorem quantFlatChartThree : QuantFlatChartThreeStatement := by
  intro d hd
  obtain ⟨ε₀, hε₀, C₀, hC₀, H3⟩ := exists_norm_iteratedFDeriv_le_of_flat (d := d) hd
  obtain ⟨εg, hεg, Cg, hCg, HG⟩ := exists_norm_gradient_sub_le_of_flat_quarter (d := d) hd
  obtain ⟨ε₁, hε₁, Hc⟩ := exists_glued_chart_of_flat (d := d) hd
  set εm := min (min ε₀ εg) (min ε₁ (1 / (2 * Cg))) with hεm
  have hεm0 : 0 < εm := lt_min (lt_min hε₀ hεg) (lt_min hε₁ (by positivity))
  refine ⟨εm, hεm0, max C₀ 1, lt_max_of_lt_right one_pos,
    fun {u e ε} hc hnn hmin he hεle hflat ↦ ?_⟩
  set εp := max ε (εm / 2) with hεp
  have hεp0 : 0 < εp := lt_max_of_lt_right (by positivity)
  have hεpm : εp ≤ εm := max_le hεle (by linarith)
  have hflatp : ∀ x ∈ ball (0 : E d) 1, |u x - max ⟪x, e⟫ 0| ≤ εp :=
    fun x hx ↦ (hflat x hx).trans (le_max_left _ _)
  have hε0 : εp ≤ ε₀ := hεpm.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεg' : εp ≤ εg := hεpm.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε1 : εp ≤ ε₁ := hεpm.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεC : Cg * εp ≤ 1 / 2 := by
    have := hεpm.trans ((min_le_right _ _).trans (min_le_right _ _))
    calc Cg * εp ≤ Cg * (1 / (2 * Cg)) := by gcongr
      _ = 1 / 2 := by field_simp
  obtain ⟨F, hF, hFu, hFloc, hFn, hFΔ, hFcl⟩ := Hc hc hnn hmin he hε1 hflatp
  have h42 : ball (0 : E d) (1 / 4) ⊆ ball 0 (1 / 2) := ball_subset_ball (by norm_num)
  refine ⟨F, hF.contDiffOn, fun x hx ↦ hFu x (h42 hx), fun x hx h ↦ hFn x (h42 hx) h,
    fun x hx h ↦ hFΔ x (h42 hx) h, fun x hx hFx ↦ ⟨?_, ?_⟩⟩
  · -- `∇F · e ≥ 1/2`
    have hcl : x ∈ closure {z | z ∈ ball (0 : E d) (1 / 4) ∧ 0 < u z} := by
      have h := hFcl x (h42 hx) hFx
      rw [mem_closure_iff_nhds] at h ⊢
      intro t ht
      obtain ⟨z, hzt, hz⟩ := h (t ∩ ball 0 (1 / 4)) (inter_mem ht (isOpen_ball.mem_nhds hx))
      exact ⟨z, hzt.1, hzt.2, hz.2⟩
    have hcont : Continuous fun z ↦ ⟪∇ F z, e⟫ :=
      ((toDual ℝ (E d)).symm.continuous.comp (hF.continuous_fderiv (by simp))).inner
        continuous_const
    refine ContinuousWithinAt.closure_le (f := fun _ ↦ (1 / 2 : ℝ)) (g := fun z ↦ ⟪∇ F z, e⟫)
      hcl continuousWithinAt_const hcont.continuousWithinAt fun z hz ↦ ?_
    have hzU : z ∈ ball (0 : E d) 1 := ball_subset_ball (by norm_num) hz.1
    have hgu : ∇ F z = ∇ u z := by
      simp only [gradient, (hFloc z (h42 hz.1) hz.2).fderiv_eq]
    have hb := HG hεp0 hεg' hc hnn hmin he hflatp z ⟨⟨hzU, hz.2⟩, hz.1⟩
    change 1 / 2 ≤ ⟪∇ F z, e⟫
    rw [hgu]
    have h1 : ⟪∇ u z, e⟫ = 1 + ⟪∇ u z - e, e⟫ := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq, he]; ring
    have h2 := abs_real_inner_le_norm (∇ u z - e) e
    rw [he, mul_one] at h2
    linarith [neg_abs_le ⟪∇ u z - e, e⟫]
  · -- `‖D³F‖ ≤ C₀`
    refine norm_iteratedFDeriv_le_of_glued hF hFloc hFcl (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) 3
      (fun z hz hu ↦ ?_) x hx hFx
    have hzU : z ∈ ball (0 : E d) 1 := ball_subset_ball (by norm_num) hz
    exact (H3 hεp0 hε0 hc hnn hmin he hflatp z ⟨⟨hzU, hu⟩, hz⟩).2.trans (le_max_left _ _)

end EllipticBernoulli
