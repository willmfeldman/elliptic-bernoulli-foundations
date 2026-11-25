/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.QuantChart.NearFB
import EllipticBernoulli.QuantChart.Gradient
import EllipticBernoulli.Lipschitz.LinearGrowth
import EllipticBernoulli.Viscosity.Basic
import EllipticBernoulli.Viscosity.Harmonic
import EllipticBernoulli.Variational.OneSided
import EllipticBernoulli.Flatness.OneStep
import EllipticBernoulli.Flatness.Classical
import EllipticBernoulli.Harmonic.GradientEstimate
import BasicElliptic.Harmonic.Estimates

/-!
# Uniform derivative bounds on the positive phase of a flat minimizer

For an `ε`-flat minimizer `u` in `B_1` with `0 < ε ≤ ε₀(d)`, on `{u > 0} ∩ B_{1/4}`:

* `exists_norm_iteratedFDeriv_le_of_flat`: `‖D²u‖ ≤ C₀` and `‖D³u‖ ≤ C₀`;
* `exists_norm_gradient_sub_le_of_flat_quarter`: `‖∇u - e‖ ≤ C ε`.

A point at distance `< s` from the zero set has a nearest zero, which is a free-boundary point in
`B̄_{3/8}`. There the bounds near the free boundary apply
(`exists_norm_iteratedFDeriv_le_near_freeBoundary`,
`exists_norm_gradient_sub_le_of_flat`). Otherwise `u` is harmonic on `B̄_s`, and the interior
estimates for harmonic functions apply: to `u` itself for `D²`, `D³`, and to `u - x · e` for `∇`.
-/

open Set Filter Topology Metric InnerProductSpace
open scoped Gradient RealInnerProductSpace

public section

namespace EllipticBernoulli

variable {d : ℕ}

/-- A zero within `s` of a positive point gives a free-boundary point within `s`. -/
private theorem exists_freeBoundary_near {u : E d → ℝ} (hc : ContinuousOn u (ball 0 1))
    (hnn : ∀ x ∈ ball (0 : E d) 1, 0 ≤ u x) {z : E d} {s : ℝ}
    (hsub : closedBall z s ⊆ ball (0 : E d) 1) (hz : 0 < u z)
    (hzero : ∃ w ∈ closedBall z s, u w = 0) :
    ∃ x₁ ∈ freeBoundary u (ball 0 1), ‖z - x₁‖ ≤ s := by
  obtain ⟨x₁, hx₁B, hx₁0, hdist, hpos⟩ := exists_nearest_zero hc hnn hsub hz hzero
  have hP : ball z (dist x₁ z) ⊆ posSet u (ball 0 1) := fun w hw ↦
    ⟨hsub (ball_subset_closedBall.trans (closedBall_subset_closedBall
      (by simpa [dist_comm] using hx₁B)) hw), hpos w hw⟩
  refine ⟨x₁, ⟨⟨?_, fun hint ↦ ?_⟩, hsub hx₁B⟩, ?_⟩
  · have : x₁ ∈ closure (ball z (dist x₁ z)) := by
      rw [closure_ball z hdist.ne', mem_closedBall]
    exact closure_mono hP this
  · have := (interior_subset hint : x₁ ∈ posSet u (ball 0 1)).2
    rw [hx₁0] at this; exact lt_irrefl _ this
  · rw [← dist_eq_norm, dist_comm]; exact hx₁B

/-- **Second and third derivatives on the positive phase.** -/
theorem exists_norm_iteratedFDeriv_le_of_flat (hd : 2 ≤ d) : ∃ ε₀ > 0, ∃ C₀ ≥ 0,
    ∀ {u : E d → ℝ} {e : E d} {ε : ℝ}, 0 < ε → ε ≤ ε₀ →
    ContinuousOn u (ball 0 1) → (∀ x ∈ ball (0 : E d) 1, 0 ≤ u x) →
    IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u → ‖e‖ = 1 →
    (∀ x ∈ ball (0 : E d) 1, |u x - max ⟪x, e⟫ 0| ≤ ε) →
    ∀ z ∈ posSet u (ball 0 1) ∩ ball 0 (1 / 4),
      ‖iteratedFDeriv ℝ 2 u z‖ ≤ C₀ ∧ ‖iteratedFDeriv ℝ 3 u z‖ ≤ C₀ := by
  obtain ⟨ε₄, hε₄, C₁, hC₁, HN⟩ := exists_norm_iteratedFDeriv_le_near_freeBoundary (d := d) hd
  obtain ⟨Ch, hCh, Hh⟩ := BasicElliptic.norm_iteratedFDeriv_le_of_harmonic (E d)
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 1 / 4096 := ⟨_, rfl⟩
  refine ⟨min ε₄ (1 / 2), lt_min hε₄ (by norm_num),
    max C₁ (Ch * 2 / s ^ 2 + Ch * 2 / s ^ 3), le_max_of_le_left hC₁,
    fun {u e ε} hε hεle hc hnn hmin he hflat z hz ↦ ?_⟩
  have hε4 : ε ≤ ε₄ := hεle.trans (min_le_left _ _)
  have hε2 : ε ≤ 1 / 2 := hεle.trans (min_le_right _ _)
  have hzn : ‖z‖ < 1 / 4 := by simpa using hz.2
  have hs' : s = 1 / 4096 := hs
  have hsub : closedBall z s ⊆ ball (0 : E d) 1 := fun w hw ↦ by
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' w z
    linarith
  by_cases hzero : ∃ w ∈ closedBall z s, u w = 0
  · obtain ⟨x₁, hx₁, hzx⟩ := exists_freeBoundary_near hc hnn hsub hz.1.2 hzero
    have hx₁3 : ‖x₁‖ ≤ 3 / 8 := by
      have := norm_le_norm_add_norm_sub' x₁ z
      rw [norm_sub_rev] at hzx
      linarith [hs']
    obtain ⟨h2, h3⟩ := HN hε hε4 hc hnn hmin he hflat x₁ hx₁ hx₁3 z
      ⟨hz.1, by rw [mem_ball, dist_eq_norm]; linarith [hs']⟩
    exact ⟨h2.trans (le_max_left _ _), h3.trans (le_max_left _ _)⟩
  · push Not at hzero
    have hP : ∀ w ∈ closedBall z s, w ∈ posSet u (ball 0 1) := fun w hw ↦
      ⟨hsub hw, lt_of_le_of_ne (hnn w (hsub hw)) (Ne.symm (hzero w hw))⟩
    have hH : HarmonicOnNhd u (posSet u (ball 0 1)) :=
      IsViscSolution.harmonicOnNhd_posSet isOpen_ball (IsLocalEnergyMinimizer.isViscSolution
        isOpen_ball continuousOn_const (fun _ _ ↦ zero_le_one) hc hnn hmin)
    have hHs : HarmonicOnNhd u (closedBall z s) := fun w hw ↦ hH w (hP w hw)
    have hbd : ∀ w ∈ closedBall z s, |u w| ≤ 2 := fun w hw ↦ by
      have hwU := hsub hw
      have h1 := (abs_le.1 (hflat w hwU)).2
      have h2 : max ⟪w, e⟫ 0 ≤ 1 := by
        refine max_le ?_ zero_le_one
        have := real_inner_le_norm w e
        rw [he, mul_one] at this
        have : ‖w‖ < 1 := by simpa using hwU
        linarith
      rw [abs_of_nonneg (hnn w hwU)]
      linarith
    have hs0 : (0 : ℝ) < s := by rw [hs]; norm_num
    have b2 := Hh 2 (by norm_num) u z s 2 hs0 hHs hbd
    have b3 := Hh 3 (by norm_num) u z s 2 hs0 hHs hbd
    have p2 : 0 ≤ Ch * 2 / s ^ 2 := by positivity
    have p3 : 0 ≤ Ch * 2 / s ^ 3 := by positivity
    exact ⟨b2.trans ((le_add_of_nonneg_right p3).trans (le_max_right _ _)),
      b3.trans ((le_add_of_nonneg_left p2).trans (le_max_right _ _))⟩

/-- **The gradient on the positive phase.** -/
theorem exists_norm_gradient_sub_le_of_flat_quarter (hd : 2 ≤ d) : ∃ ε₀ > 0, ∃ C > 0,
    ∀ {u : E d → ℝ} {e : E d} {ε : ℝ}, 0 < ε → ε ≤ ε₀ →
    ContinuousOn u (ball 0 1) → (∀ x ∈ ball (0 : E d) 1, 0 ≤ u x) →
    IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u → ‖e‖ = 1 →
    (∀ x ∈ ball (0 : E d) 1, |u x - max ⟪x, e⟫ 0| ≤ ε) →
    ∀ z ∈ posSet u (ball 0 1) ∩ ball 0 (1 / 4), ‖∇ u z - e‖ ≤ C * ε := by
  obtain ⟨ε₂, hε₂, CL, hCL, HL⟩ := exists_norm_gradient_sub_le_of_flat (d := d) hd
  obtain ⟨Cd, hCd0, hCd⟩ := exists_norm_fderiv_le_div_of_harmonic (d := d) (by omega)
  set c := ndConst d with hcdef
  have hc0 : 0 < c := ndConst_pos hd
  have hc1 : c ≤ 1 := ndConst_le_one hd
  refine ⟨min ε₂ (c / 16), lt_min hε₂ (by positivity), CL + 8 * Cd * (1 + 2 / c) + 1,
    by positivity, fun {u e ε} hε hεle hc hnn hmin he hflat z hz ↦ ?_⟩
  have hε2 : ε ≤ ε₂ := hεle.trans (min_le_left _ _)
  have hεc : ε ≤ c / 16 := hεle.trans (min_le_right _ _)
  have hzn : ‖z‖ < 1 / 4 := by simpa using hz.2
  have hsub : closedBall z (1 / 8) ⊆ ball (0 : E d) 1 := fun w hw ↦ by
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' w z
    linarith
  have hCε : 0 ≤ 8 * Cd * (1 + 2 / c) * ε + ε := by positivity
  by_cases hzero : ∃ w ∈ closedBall z (1 / 8), u w = 0
  · obtain ⟨x₁, hx₁, hzx⟩ := exists_freeBoundary_near hc hnn hsub hz.1.2 hzero
    have hx₁3 : ‖x₁‖ ≤ 3 / 8 := by
      have := norm_le_norm_add_norm_sub' x₁ z
      rw [norm_sub_rev] at hzx
      linarith
    have := HL hε hε2 hc hnn hmin he hflat x₁ hx₁ hx₁3 z
      ⟨hz.1, by rw [mem_ball, dist_eq_norm]; linarith⟩
    nlinarith
  · push Not at hzero
    have hP : ∀ w ∈ closedBall z (1 / 8), w ∈ posSet u (ball 0 1) := fun w hw ↦
      ⟨hsub hw, lt_of_le_of_ne (hnn w (hsub hw)) (Ne.symm (hzero w hw))⟩
    have hH : HarmonicOnNhd u (posSet u (ball 0 1)) :=
      IsViscSolution.harmonicOnNhd_posSet isOpen_ball (IsLocalEnergyMinimizer.isViscSolution
        isOpen_ball continuousOn_const (fun _ _ ↦ zero_le_one) hc hnn hmin)
    set h : E d → ℝ := fun x ↦ u x - (⟪x, e⟫ + 0) with hh
    have hhH : HarmonicOnNhd h (closedBall z (1 / 8)) := fun x hx ↦
      (hH x (hP x hx)).sub (harmonicAt_inner_add e 0 x)
    have hεc' : 2 * ε / c ≤ 1 / 8 := by rw [div_le_iff₀ hc0]; nlinarith
    have hbd : ∀ w ∈ closedBall z (1 / 8), |h w| ≤ ε + 2 * ε / c := by
      intro w hw
      have hwP := hP w hw
      have hwn : ‖w‖ < 7 / 8 := by
        rw [mem_closedBall, dist_eq_norm] at hw
        have := norm_le_norm_add_norm_sub' w z
        linarith
      have hwe : -(2 * ε / c) < ⟪w, e⟫ := by
        by_contra hcon
        push Not at hcon
        have := eq_zero_of_flat_of_inner_le hd hε hεc' hc hnn hmin he hflat hwn hcon
        have h2 := hwP.2
        rw [this] at h2; exact lt_irrefl _ h2
      have h1 := abs_le.1 (hflat w hwP.1)
      simp only [hh, add_zero]
      rw [abs_le]
      rcases le_total 0 ⟪w, e⟫ with h0 | h0
      · rw [max_eq_left h0] at h1
        have : 0 ≤ 2 * ε / c := by positivity
        constructor <;> linarith
      · rw [max_eq_right h0] at h1
        have := hwP.2
        constructor <;> linarith
    have hest := hCd h z (1 / 8) (ε + 2 * ε / c) (by norm_num) hhH hbd
    have hvd : DifferentiableAt ℝ u z := (hH z hz.1).1.differentiableAt (by norm_num)
    have hlin : HasFDerivAt (fun x : E d ↦ ⟪x, e⟫ + 0) (toDual ℝ (E d) e) z := by
      have : (fun x : E d ↦ ⟪x, e⟫ + 0) = fun x ↦ toDual ℝ (E d) e x := by
        funext x; rw [toDual_apply_apply, real_inner_comm, add_zero]
      rw [this]; exact (toDual ℝ (E d) e).hasFDerivAt
    have hfd : fderiv ℝ h z = fderiv ℝ u z - toDual ℝ (E d) e :=
      (hvd.hasFDerivAt.sub hlin).fderiv
    rw [norm_gradient_sub_eq, ← hfd]
    have e1 : Cd * (ε + 2 * ε / c) / (1 / 8) = 8 * Cd * (1 + 2 / c) * ε := by ring
    rw [e1] at hest
    nlinarith

end EllipticBernoulli
