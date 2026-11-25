/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Statements.QuantChart
import EllipticBernoulli.QuantChart.Chart
import EllipticBernoulli.QuantChart.Wide
import EllipticBernoulli.QuantChart.Holder

/-!
# The quantitative `C^{2,α}` chart at a flat free boundary

`quantFlatChart : QuantFlatChartStatement`, with `α = 1`. The chart `F` is the glued chart of
`exists_glued_chart_of_flat`. On `{u > 0} ∩ B_{1/2}`, `F = u` near each point, and
`‖∇u - e‖ ≤ C ε`, `‖D²u‖ ≤ C` (`exists_bounds_of_flat_wide`), and `D²u` is `C`-Lipschitz
(`exists_hessian_lipschitz_of_flat`). Every point of `{F ≥ 0} ∩ B_{1/2}` is a limit of such
points, so the bounds pass to `{F ≥ 0}` by continuity of the derivatives of `F`. For the
Lipschitz bound, take limits of pairs, in the closure of the product.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient RealInnerProductSpace Laplacian

public section

namespace EllipticBernoulli

/-- **The quantitative `C^{2,α}` chart at a flat free boundary** (`QuantFlatChartStatement`). -/
theorem quantFlatChart : QuantFlatChartStatement := by
  intro d hd
  obtain ⟨ε₆, hε₆, CW, hCW, HW⟩ := exists_bounds_of_flat_wide (d := d) hd
  obtain ⟨ε₇, hε₇, CH, hCH, HH⟩ := exists_hessian_lipschitz_of_flat (d := d) hd
  obtain ⟨ε₁, hε₁, Hc⟩ := exists_glued_chart_of_flat (d := d) hd
  set εm := min (min ε₆ ε₇) (min ε₁ (1 / (2 * (CW + 1)))) with hεm
  have hεm0 : 0 < εm := lt_min (lt_min hε₆ hε₇) (lt_min hε₁ (by positivity))
  set C := max (max 2 CW) CH + 1 with hC
  have hC0 : 0 < C := by positivity
  refine ⟨εm, hεm0, 1, one_pos, C, hC0, fun {u e ε} hc hnn hmin he hεle hflat ↦ ?_⟩
  set εp := max ε (εm / 2) with hεp
  have hεp0 : 0 < εp := lt_max_of_lt_right (by positivity)
  have hεpm : εp ≤ εm := max_le hεle (by linarith)
  have hflatp : ∀ x ∈ ball (0 : E d) 1, |u x - max ⟪x, e⟫ 0| ≤ εp :=
    fun x hx ↦ (hflat x hx).trans (le_max_left _ _)
  have hε6 : εp ≤ ε₆ := hεpm.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hε7 : εp ≤ ε₇ := hεpm.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hε1 : εp ≤ ε₁ := hεpm.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεC : CW * εp ≤ 1 / 2 := by
    have := hεpm.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at this; nlinarith
  obtain ⟨F, hF, hFu, hFloc, hFn, hFΔ, hFcl⟩ := Hc hc hnn hmin he hε1 hflatp
  have hW := HW hεp0 hε6 hc hnn hmin he hflatp
  have hHL := HH hεp0 hε7 hc hnn hmin he hflatp
  set A : Set (E d) := {z | z ∈ ball (0 : E d) (1 / 2) ∧ 0 < u z} with hA
  have hAP : ∀ z ∈ A, z ∈ posSet u (ball 0 1) ∩ ball 0 (9 / 16) := fun z hz ↦
    ⟨⟨ball_subset_ball (by norm_num) hz.1, hz.2⟩, ball_subset_ball (by norm_num) hz.1⟩
  have hgrad : ∀ z ∈ A, ∇ F z = ∇ u z := fun z hz ↦ by
    simp only [gradient, (hFloc z hz.1 hz.2).fderiv_eq]
  have hD2 : ∀ z ∈ A, iteratedFDeriv ℝ 2 F z = iteratedFDeriv ℝ 2 u z := fun z hz ↦
    ((hFloc z hz.1 hz.2).iteratedFDeriv ℝ 2).self_of_nhds
  have hcontG : Continuous (∇ F) :=
    (toDual ℝ (E d)).symm.continuous.comp (hF.continuous_fderiv (by simp))
  have hcont2 : Continuous (iteratedFDeriv ℝ 2 F) :=
    hF.continuous_iteratedFDeriv (by simp)
  refine ⟨F, hF.contDiffOn, hFu, hFn, hFΔ, fun x hx hFx ↦ ?_, fun x hx y hy hFx hFy ↦ ?_⟩
  · have hcl : x ∈ closure A := hFcl x hx hFx
    refine ⟨?_, ?_, ?_⟩
    · refine ContinuousWithinAt.closure_le (f := fun _ ↦ (1 / 2 : ℝ))
        (g := fun z ↦ ⟪∇ F z, e⟫) hcl continuousWithinAt_const
        (hcontG.inner continuous_const).continuousWithinAt fun z hz ↦ ?_
      change 1 / 2 ≤ ⟪∇ F z, e⟫
      rw [hgrad z hz]
      have hb := (hW z (hAP z hz)).1.trans hεC
      have h1 : ⟪∇ u z, e⟫ = 1 + ⟪∇ u z - e, e⟫ := by
        rw [inner_sub_left, real_inner_self_eq_norm_sq, he]; ring
      have h2 := abs_real_inner_le_norm (∇ u z - e) e
      rw [he, mul_one] at h2
      linarith [neg_abs_le ⟪∇ u z - e, e⟫]
    · refine ContinuousWithinAt.closure_le (f := fun z ↦ ‖∇ F z‖) (g := fun _ ↦ C) hcl
        hcontG.norm.continuousWithinAt continuousWithinAt_const fun z hz ↦ ?_
      change ‖∇ F z‖ ≤ C
      rw [hgrad z hz]
      have hb := (hW z (hAP z hz)).1.trans hεC
      have := norm_le_norm_add_norm_sub' (∇ u z) e
      rw [he] at this
      have : (2 : ℝ) ≤ C := by
        rw [hC]; linarith [le_max_left 2 CW, le_max_left (max 2 CW) CH]
      linarith
    · refine ContinuousWithinAt.closure_le (f := fun z ↦ ‖iteratedFDeriv ℝ 2 F z‖)
        (g := fun _ ↦ C) hcl hcont2.norm.continuousWithinAt continuousWithinAt_const
        fun z hz ↦ ?_
      change ‖iteratedFDeriv ℝ 2 F z‖ ≤ C
      rw [hD2 z hz]
      refine (hW z (hAP z hz)).2.1.trans ?_
      rw [hC]; linarith [le_max_right 2 CW, le_max_left (max 2 CW) CH]
  · -- the Lipschitz bound, through the closure of `A ×ˢ A`
    have hcl : (x, y) ∈ closure (A ×ˢ A) := by
      rw [closure_prod_eq]; exact ⟨hFcl x hx hFx, hFcl y hy hFy⟩
    have hcont : Continuous fun p : E d × E d ↦
        ‖iteratedFDeriv ℝ 2 F p.1 - iteratedFDeriv ℝ 2 F p.2‖ :=
      ((hcont2.comp continuous_fst).sub (hcont2.comp continuous_snd)).norm
    have hcont' : Continuous fun p : E d × E d ↦ C * ‖p.1 - p.2‖ :=
      continuous_const.mul (continuous_fst.sub continuous_snd).norm
    have := ContinuousWithinAt.closure_le (f := fun p : E d × E d ↦
        ‖iteratedFDeriv ℝ 2 F p.1 - iteratedFDeriv ℝ 2 F p.2‖)
      (g := fun p : E d × E d ↦ C * ‖p.1 - p.2‖) hcl hcont.continuousWithinAt
      hcont'.continuousWithinAt fun p hp ↦ by
        change ‖iteratedFDeriv ℝ 2 F p.1 - iteratedFDeriv ℝ 2 F p.2‖ ≤ C * ‖p.1 - p.2‖
        rw [hD2 p.1 hp.1, hD2 p.2 hp.2]
        refine (hHL p.1 ⟨⟨ball_subset_ball (by norm_num) hp.1.1, hp.1.2⟩, hp.1.1⟩ p.2
          ⟨⟨ball_subset_ball (by norm_num) hp.2.1, hp.2.2⟩, hp.2.1⟩).trans ?_
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        rw [hC]; linarith [le_max_right (max 2 CW) CH]
    simpa [Real.rpow_one] using this

end EllipticBernoulli
