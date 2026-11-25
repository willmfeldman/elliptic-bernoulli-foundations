/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.QuantChart.Rescaled
import EllipticBernoulli.Lipschitz.LinearGrowth
import EllipticBernoulli.Viscosity.Basic
import EllipticBernoulli.Viscosity.Harmonic
import EllipticBernoulli.Variational.OneSided
import EllipticBernoulli.Flatness.OneStep
import EllipticBernoulli.Flatness.Classical
import EllipticBernoulli.Harmonic.GradientEstimate
import BasicElliptic.Harmonic.Estimates

/-!
# Uniform bounds on the positive phase in `B_{9/16}`

`exists_bounds_of_flat_wide`: for an `ε`-flat minimizer `u` in `B_1` (`0 < ε ≤ ε₆(d)`), on
`{u > 0} ∩ B_{9/16}` we have `‖∇u - e‖ ≤ C ε`, `‖D²u‖ ≤ C` and `‖D³u‖ ≤ C`.

Near the zero set (distance `< 1/64`) the nearest zero is a free-boundary point `y` with
`‖y‖ ≤ 5/8`, and `exists_bounds_at_freeBoundary` applies. Otherwise `u` is harmonic on
`B̄_{1/64}`, with `|u| ≤ 2` and `|u - x · e| ≤ (1 + 2/c) ε`, and the interior estimates apply.
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

/-- **Uniform bounds on `{u > 0} ∩ B_{9/16}`.** -/
theorem exists_bounds_of_flat_wide (hd : 2 ≤ d) : ∃ ε₆ > 0, ∃ C ≥ 0,
    ∀ {u : E d → ℝ} {e : E d} {ε : ℝ}, 0 < ε → ε ≤ ε₆ →
    ContinuousOn u (ball 0 1) → (∀ x ∈ ball (0 : E d) 1, 0 ≤ u x) →
    IsLocalEnergyMinimizer (ball 0 1) (fun _ ↦ 1) u → ‖e‖ = 1 →
    (∀ x ∈ ball (0 : E d) 1, |u x - max ⟪x, e⟫ 0| ≤ ε) →
    ∀ z ∈ posSet u (ball 0 1) ∩ ball 0 (9 / 16),
      ‖∇ u z - e‖ ≤ C * ε ∧ ‖iteratedFDeriv ℝ 2 u z‖ ≤ C ∧ ‖iteratedFDeriv ℝ 3 u z‖ ≤ C := by
  obtain ⟨ε₅, hε₅, C₅, hC₅, H5⟩ := exists_bounds_at_freeBoundary (d := d) hd
  obtain ⟨Ch, hCh, Hh⟩ := BasicElliptic.norm_iteratedFDeriv_le_of_harmonic (E d)
  obtain ⟨Cd, hCd0, hCd⟩ := exists_norm_fderiv_le_div_of_harmonic (d := d) (by omega)
  set c := ndConst d with hcdef
  have hc0 : 0 < c := ndConst_pos hd
  have hc1 : c ≤ 1 := ndConst_le_one hd
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 1 / 64 := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; norm_num
  set Cw := max C₅ (Cd * (1 + 2 / c) / s + Ch * 2 / s ^ 2 + Ch * 2 / s ^ 3) with hCw
  refine ⟨min ε₅ (min (1 / 2) (c / 16)), lt_min hε₅ (lt_min (by norm_num) (by positivity)), Cw,
    le_max_of_le_left hC₅, fun {u e ε} hε hεle hc hnn hmin he hflat z hz ↦ ?_⟩
  have hε5 : ε ≤ ε₅ := hεle.trans (min_le_left _ _)
  have hε2 : ε ≤ 1 / 2 := hεle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεc : ε ≤ c / 16 := hεle.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hzn : ‖z‖ < 9 / 16 := by simpa using hz.2
  have hsub : closedBall z s ⊆ ball (0 : E d) 1 := fun w hw ↦ by
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' w z
    linarith
  by_cases hzero : ∃ w ∈ closedBall z s, u w = 0
  · obtain ⟨x₁, hx₁, hzx⟩ := exists_freeBoundary_near hc hnn hsub hz.1.2 hzero
    have hx₁5 : ‖x₁‖ ≤ 5 / 8 := by
      have := norm_le_norm_add_norm_sub' x₁ z
      rw [norm_sub_rev] at hzx
      linarith
    obtain ⟨h1, h2, h3⟩ := H5 hε hε5 hc hnn hmin he hflat x₁ hx₁ hx₁5 z
      ⟨hz.1, by rw [mem_ball, dist_eq_norm]; linarith⟩
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hε.le),
      h2.trans (le_max_left _ _), h3.trans (le_max_left _ _)⟩
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
    have b2 := Hh 2 (by norm_num) u z s 2 hs0 hHs hbd
    have b3 := Hh 3 (by norm_num) u z s 2 hs0 hHs hbd
    -- the gradient, from `u - x · e`
    set h : E d → ℝ := fun x ↦ u x - (⟪x, e⟫ + 0) with hh
    have hhH : HarmonicOnNhd h (closedBall z s) := fun x hx ↦
      (hH x (hP x hx)).sub (harmonicAt_inner_add e 0 x)
    have hεc' : 2 * ε / c ≤ 1 / 8 := by rw [div_le_iff₀ hc0]; nlinarith
    have hhb : ∀ w ∈ closedBall z s, |h w| ≤ ε + 2 * ε / c := by
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
    have hest := hCd h z s (ε + 2 * ε / c) hs0 hhH hhb
    have hvd : DifferentiableAt ℝ u z := (hH z hz.1).1.differentiableAt (by norm_num)
    have hlin : HasFDerivAt (fun x : E d ↦ ⟪x, e⟫ + 0) (toDual ℝ (E d) e) z := by
      have : (fun x : E d ↦ ⟪x, e⟫ + 0) = fun x ↦ toDual ℝ (E d) e x := by
        funext x; rw [toDual_apply_apply, real_inner_comm, add_zero]
      rw [this]; exact (toDual ℝ (E d) e).hasFDerivAt
    have hfd : fderiv ℝ h z = fderiv ℝ u z - toDual ℝ (E d) e :=
      (hvd.hasFDerivAt.sub hlin).fderiv
    have p1 : 0 ≤ Cd * (1 + 2 / c) / s := by positivity
    have p2 : 0 ≤ Ch * 2 / s ^ 2 := by positivity
    have p3 : 0 ≤ Ch * 2 / s ^ 3 := by positivity
    have hsum : Cd * (1 + 2 / c) / s + Ch * 2 / s ^ 2 + Ch * 2 / s ^ 3 ≤ Cw := le_max_right _ _
    refine ⟨?_, b2.trans (by linarith), b3.trans (by linarith)⟩
    rw [norm_gradient_sub_eq, ← hfd]
    have e1 : Cd * (ε + 2 * ε / c) / s = Cd * (1 + 2 / c) / s * ε := by ring
    rw [e1] at hest
    exact hest.trans (mul_le_mul_of_nonneg_right (by linarith) hε.le)

end EllipticBernoulli
