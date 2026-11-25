/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Hodograph.Flat
public import EllipticBernoulli.QuantChart.LocalGradient
import EllipticBernoulli.QuantChart.Chart
import EllipticBernoulli.Variational.OneSided
import EllipticBernoulli.Viscosity.Basic
import EllipticBernoulli.Viscosity.Harmonic

/-!
# Hodograph data of fixed size at the free boundary of a flat minimizer

`exists_isFlatChartData_of_flat`: for `d ≥ 2` there are `ε₃, C > 0` such that, if `u` is an
`ε`-flat minimizer in `B_1` (`0 < ε ≤ ε₃`) and `y` is a free-boundary point with `‖y‖ ≤ 3/8`,
there are a unit vector `e'` with `‖e' - e‖ ≤ C ε` and a field `G` with
`IsFlatChartData (B_1) u y e' (1/8) G` and `‖G z - e'‖ ≤ 2 C ε` on `closure {u > 0} ∩ B_{1/8}(y)`.

`G` is the gradient of the glued chart `F` of `exists_glued_chart_of_flat`, and `e' = ∇F(y)`. The
bounds come from `exists_norm_gradient_sub_le_of_flat` and continuity.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped ContDiff Gradient RealInnerProductSpace

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- **Hodograph data of fixed size at the free boundary of a flat minimizer.** -/
theorem exists_isFlatChartData_of_flat (hd : 2 ≤ d) : ∃ ε₃ > 0, ∃ C > 0,
    ∀ {u : E d → ℝ} {e : E d} {ε : ℝ}, 0 < ε → ε ≤ ε₃ →
    ContinuousOn u (ball 0 1) → (∀ x ∈ ball (0 : E d) 1, 0 ≤ u x) →
    IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u → ‖e‖ = 1 →
    (∀ x ∈ ball (0 : E d) 1, |u x - max ⟪x, e⟫ 0| ≤ ε) →
    ∀ y ∈ freeBoundary u (ball 0 1), ‖y‖ ≤ 3 / 8 →
    ∃ (e' : E d) (G : E d → E d), ‖e' - e‖ ≤ C * ε ∧
      IsFlatChartData (ball 0 1) u y e' (1 / 8) G ∧
      ∀ z ∈ closure (posSet u (ball 0 1)) ∩ ball y (1 / 8), ‖G z - e'‖ ≤ 2 * (C * ε) := by
  obtain ⟨ε₁, hε₁, Hg⟩ := exists_glued_chart_of_flat (d := d) hd
  obtain ⟨ε₂, hε₂, C, hC, Hd⟩ := exists_norm_gradient_sub_le_of_flat (d := d) hd
  set c := ndConst d with hcdef
  have hc0 : 0 < c := ndConst_pos hd
  have hc1 : c ≤ 1 := ndConst_le_one hd
  refine ⟨min (min ε₁ ε₂) (min (c / 256) (1 / (64 * C))), lt_min (lt_min hε₁ hε₂)
    (lt_min (by positivity) (by positivity)), C, hC,
    fun {u e ε} hε hεle hc hnn hmin he hflat y hy hy3 ↦ ?_⟩
  have hε1 : ε ≤ ε₁ := hεle.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hε2 : ε ≤ ε₂ := hεle.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεc : ε ≤ c / 256 := hεle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεC : ε ≤ 1 / (64 * C) := hεle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCε : C * ε ≤ 1 / 64 := by
    calc C * ε ≤ C * (1 / (64 * C)) := by gcongr
      _ = 1 / 64 := by field_simp
  set U := ball (0 : E d) 1 with hU
  obtain ⟨F, hF, hFu, hFloc, hFn, -, -⟩ := Hg hc hnn hmin he hε1 hflat
  have hgradD := Hd hε hε2 hc hnn hmin he hflat y hy hy3
  have hy2 : y ∈ ball (0 : E d) (1 / 2) := by rw [mem_ball, dist_zero_right]; linarith
  have hB4 : ball y (1 / 8) ⊆ ball (0 : E d) (1 / 2) := fun z hz ↦ by
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' z y
    linarith
  have hB8 : ball y (1 / 8) ⊆ ball y (1 / 8) := subset_rfl
  have hB84 : ball y (1 / 8) ⊆ ball y (1 / 4) := ball_subset_ball (by norm_num)
  have hB1 : ball y (1 / 8) ⊆ U := hB4.trans (ball_subset_ball (by norm_num))
  have hP : IsOpen (posSet u U) := isOpen_posSet isOpen_ball hc
  have hcontF : Continuous (∇ F) := by
    have := hF.continuous_fderiv (by simp)
    exact (toDual ℝ (E d)).symm.continuous.comp this
  -- `∇F = ∇u` on the positive phase
  have hGeq : ∀ z ∈ posSet u U ∩ ball y (1 / 8), ∇ F z = ∇ u z := fun z hz ↦ by
    simp only [gradient, (hFloc z (hB4 hz.2) hz.1.2).fderiv_eq]
  -- `‖∇F - e‖ ≤ C ε` on the closure of the positive phase near `y`
  have hGe : ∀ z ∈ closure (posSet u U) ∩ ball y (1 / 8), ‖∇ F z - e‖ ≤ C * ε := by
    intro z hz
    have hcl : z ∈ closure (posSet u U ∩ ball y (1 / 8)) :=
      isOpen_ball.inter_closure ⟨hz.2, hz.1⟩ |> fun h ↦ by rwa [inter_comm] at h
    refine ContinuousWithinAt.closure_le (f := fun z ↦ ‖∇ F z - e‖) (g := fun _ ↦ C * ε) hcl
      ((hcontF.sub continuous_const).norm.continuousWithinAt) continuousWithinAt_const ?_
    intro w hw
    change ‖∇ F w - e‖ ≤ C * ε
    rw [hGeq w hw]
    exact hgradD w ⟨hw.1, hB84 hw.2⟩
  have hyU : y ∈ U := hy.2
  have hycl : y ∈ closure (posSet u U) ∩ ball y (1 / 8) := ⟨hy.1.1, mem_ball_self (by norm_num)⟩
  set e' := ∇ F y with he'def
  have he'e : ‖e' - e‖ ≤ C * ε := hGe y hycl
  -- `F = 0` and `|∇F| = 1` at free-boundary points near `y`
  have hFB : ∀ z ∈ freeBoundary u U ∩ ball y (1 / 8), ‖∇ F z‖ = 1 := by
    intro z hz
    have hz2 := hB4 hz.2
    have hP' : z ∉ posSet u U := fun h ↦ hz.1.1.2 (hP.interior_eq.symm ▸ h)
    have huz : u z = 0 := by
      by_contra hne
      exact hP' ⟨hz.1.2, lt_of_le_of_ne (hnn z hz.1.2) (Ne.symm hne)⟩
    have hFle : F z ≤ 0 := by
      have := hFu z hz2; rw [huz] at this
      exact (le_max_left _ _).trans this.symm.le
    have hFge : 0 ≤ F z := by
      have hcl : z ∈ closure (posSet u U ∩ ball (0 : E d) (1 / 2)) :=
        isOpen_ball.inter_closure ⟨hz2, hz.1.1.1⟩ |> fun h ↦ by rwa [inter_comm] at h
      refine ContinuousWithinAt.closure_le (f := fun _ ↦ (0 : ℝ)) (g := F) hcl
        continuousWithinAt_const hF.continuous.continuousWithinAt fun w hw ↦ ?_
      have := hFu w hw.2
      rcases le_total (F w) 0 with h | h
      · rw [max_eq_right h] at this; exact absurd this hw.1.2.ne'
      · exact h
    exact hFn z hz2 (le_antisymm hFle hFge)
  have he'1 : ‖e'‖ = 1 := hFB y ⟨hy, mem_ball_self (by norm_num)⟩
  have hGe' : ∀ z ∈ closure (posSet u U) ∩ ball y (1 / 8), ‖∇ F z - e'‖ ≤ 2 * (C * ε) := by
    intro z hz
    calc ‖∇ F z - e'‖ ≤ ‖∇ F z - e‖ + ‖e - e'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ C * ε + C * ε := by
          gcongr
          · exact hGe z ⟨hz.1, hB8 hz.2⟩
          · rw [norm_sub_rev]; exact he'e
      _ = 2 * (C * ε) := by ring
  -- the flatness facts in direction `e'`
  have hrc : 2 * ε / c < 1 / 2 := by rw [div_lt_iff₀ hc0]; nlinarith
  obtain ⟨-, hye⟩ := abs_inner_le_of_mem_freeBoundary_of_flat hd hε hrc hc hnn hmin he hflat hy
    (by linarith)
  have ha : 2 * ε / c ≤ 1 / 128 := by rw [div_le_iff₀ hc0]; nlinarith
  have hinner : ∀ z ∈ ball y (1 / 8), |⟪z - y, e⟫ - ⟪z - y, e'⟫| ≤ 1 / 8 * (C * ε) := by
    intro z hz
    rw [← inner_sub_right]
    refine (abs_real_inner_le_norm _ _).trans ?_
    have hzy : ‖z - y‖ ≤ 1 / 8 := by
      have := mem_ball.1 hz; rw [dist_eq_norm] at this; exact this.le
    rw [norm_sub_rev] at he'e
    exact mul_le_mul hzy he'e (norm_nonneg _) (by norm_num)
  refine ⟨e', ∇ F, he'e, ⟨by norm_num, he'1, isOpen_ball, hB8.trans hB1, hc, hnn,
    IsViscSolution.harmonicOnNhd_posSet isOpen_ball (IsLocalEnergyMinimizer.isViscSolution
      isOpen_ball continuousOn_const (fun _ _ ↦ zero_le_one) hc hnn hmin), hy, ?_, ?_,
    hcontF.continuousOn, fun z hz ↦ hGeq z ⟨hz.1, hB8 hz.2⟩,
    fun z hz ↦ hFB z ⟨hz.1, hB8 hz.2⟩, ?_, rfl⟩, hGe'⟩
  · -- the zero side
    intro z hz hs
    have hzn : ‖z‖ < 7 / 8 := by
      have h1 := mem_ball.1 hz; rw [dist_eq_norm] at h1
      have := norm_le_norm_add_norm_sub' z y
      linarith
    refine eq_zero_of_flat_of_inner_le hd hε (by linarith) hc hnn hmin he hflat hzn ?_
    have h1 := (abs_le.1 (hinner z hz)).2
    have h2 : ⟪z, e⟫ = ⟪z - y, e⟫ + ⟪y, e⟫ := by rw [inner_sub_left]; ring
    have h3 := (abs_le.1 hye).2
    nlinarith
  · -- the positive side
    intro z hz hs
    have hzU := hB1 (hB8 hz)
    have h1 := (abs_le.1 (hinner z hz)).1
    have h2 : ⟪z, e⟫ = ⟪z - y, e⟫ + ⟪y, e⟫ := by rw [inner_sub_left]; ring
    have h3 := (abs_le.1 hye).1
    have h4 := (abs_le.1 (hflat z hzU)).1
    have h5 := le_max_left ⟪z, e⟫ 0
    have h6 : ε ≤ 2 * ε / c := by rw [le_div_iff₀ hc0]; nlinarith
    nlinarith
  · -- `G · e' ≥ 1/2`
    intro z hz
    have h := hGe' z hz
    have h1 : ⟪∇ F z, e'⟫ = 1 + ⟪∇ F z - e', e'⟫ := by
      rw [inner_sub_left, real_inner_self_eq_norm_sq, he'1]; ring
    have h2 := abs_real_inner_le_norm (∇ F z - e') e'
    rw [he'1, mul_one] at h2
    linarith [neg_abs_le ⟪∇ F z - e', e'⟫]

end EllipticBernoulli
